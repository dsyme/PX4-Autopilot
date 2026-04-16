/-!
# systemlib::Hysteresis — Formal Verification

🔬 Lean Squad automated formal verification.

This file models and proves correctness properties of `systemlib::Hysteresis` from:

- **C++ source**: `src/lib/hysteresis/hysteresis.h` and `src/lib/hysteresis/hysteresis.cpp`
- **Informal spec**: `formal-verification/specs/hysteresis_informal.md`

## What is Hysteresis?

`Hysteresis` is a **time-delayed boolean state machine** used throughout PX4 to prevent
rapid toggling of safety-critical states (arming/disarming, flight-mode transitions,
sensor debouncing). A committed state change requires a configurable dwell time.

## C++ reference

```cpp
void Hysteresis::update(const hrt_abstime &now_us) {
    if (_requested_state != _state) {
        if (_state && !_requested_state) {        // true → false
            if (now_us >= _last_time_to_change_state + _time_from_true_us)
                _state = false;
        } else if (!_state && _requested_state) { // false → true
            if (now_us >= _last_time_to_change_state + _time_from_false_us)
                _state = true;
        }
    }
}

void Hysteresis::set_state_and_update(const bool new_state, const hrt_abstime &now_us) {
    if (new_state != _state) {
        if (new_state != _requested_state) {
            _requested_state = new_state;
            _last_time_to_change_state = now_us;
        }
    } else {
        _requested_state = _state;
    }
    update(now_us);
}
```

## Model

We model timestamps as `Nat` (microseconds) and booleans as `Bool`.
State is captured in an immutable record `HS` (Hysteresis State); operations
return new records rather than mutating in place.

## What is NOT modelled

- `uint64_t` overflow: `Nat` is unbounded; in C++ `last + delay` can wrap after ~585,000 years
- Thread safety: no synchronisation is modelled
- Non-monotonic clocks: we assume `now` is a valid `Nat`
-/

namespace PX4.Hysteresis

/-! ## State type -/

/-- An abstract snapshot of all mutable fields in `systemlib::Hysteresis`. -/
structure HS where
  state        : Bool
  requested    : Bool
  lastChange   : Nat
  delayTrue    : Nat   -- `_time_from_true_us`  (dwell when leaving `true`)
  delayFalse   : Nat   -- `_time_from_false_us` (dwell when leaving `false`)

/-! ## Core operations -/

/-- Model of `Hysteresis::update`. Pure: takes and returns `HS`. -/
def hysteresisUpdate (h : HS) (now : Nat) : HS :=
  if h.requested == h.state then h
  else if h.state && !h.requested then
    -- pending true → false transition
    if now >= h.lastChange + h.delayTrue
    then { h with state := false }
    else h
  else
    -- pending false → true transition
    if now >= h.lastChange + h.delayFalse
    then { h with state := true }
    else h

/-- Model of `Hysteresis::set_state_and_update`. -/
def setStateAndUpdate (h : HS) (newState : Bool) (now : Nat) : HS :=
  let h' :=
    if newState != h.state then
      if newState != h.requested
      then { h with requested := newState, lastChange := now }
      else h
    else { h with requested := h.state }
  hysteresisUpdate h' now

/-- Model of `set_hysteresis_time_from(from_state, delay_us)`. -/
def setHysteresisTimeFrom (h : HS) (fromState : Bool) (delay : Nat) : HS :=
  if fromState then { h with delayTrue  := delay }
               else { h with delayFalse := delay }

/-- Constructor: `Hysteresis(initial_state)` — both delays start at zero. -/
def mkHysteresis (initial : Bool) : HS :=
  { state := initial, requested := initial,
    lastChange := 0, delayTrue := 0, delayFalse := 0 }

/-! ## Invariant 1 — No spurious transitions (settled state) -/

/-- If `requested = state`, `update` is a no-op: state record is unchanged. -/
theorem update_settled_noop (h : HS) (now : Nat) (heq : h.requested = h.state) :
    hysteresisUpdate h now = h := by
  simp [hysteresisUpdate, heq]

/-- If `requested = state`, `update` leaves `.state` unchanged. -/
theorem update_settled_state (h : HS) (now : Nat) (heq : h.requested = h.state) :
    (hysteresisUpdate h now).state = h.state := by
  simp [hysteresisUpdate, heq]

/-! ## Helper: state stays put when dwell not met -/

/-- true→false: if dwell time not yet elapsed, state remains `true`. -/
theorem update_tf_stays (h : HS) (now : Nat)
    (hst : h.state = true) (hrq : h.requested = false)
    (hlt : now < h.lastChange + h.delayTrue) :
    (hysteresisUpdate h now).state = true := by
  simp [hysteresisUpdate, hst, hrq, Nat.not_le.mpr hlt]

/-- false→true: if dwell time not yet elapsed, state remains `false`. -/
theorem update_ft_stays (h : HS) (now : Nat)
    (hst : h.state = false) (hrq : h.requested = true)
    (hlt : now < h.lastChange + h.delayFalse) :
    (hysteresisUpdate h now).state = false := by
  simp [hysteresisUpdate, hst, hrq, Nat.not_le.mpr hlt]

/-! ## Invariant 2 — Delay lower bound -/

/-- true→false: if `update` committed the transition, the dwell was satisfied. -/
theorem update_tf_delay_lb (h : HS) (now : Nat)
    (hst : h.state = true) (hrq : h.requested = false)
    (hchange : (hysteresisUpdate h now).state = false) :
    now ≥ h.lastChange + h.delayTrue :=
  Classical.byContradiction fun hlt => by
    have hstays := update_tf_stays h now hst hrq (Nat.lt_of_not_le hlt)
    simp [hstays] at hchange

/-- false→true: if `update` committed the transition, the dwell was satisfied. -/
theorem update_ft_delay_lb (h : HS) (now : Nat)
    (hst : h.state = false) (hrq : h.requested = true)
    (hchange : (hysteresisUpdate h now).state = true) :
    now ≥ h.lastChange + h.delayFalse :=
  Classical.byContradiction fun hlt => by
    have hstays := update_ft_stays h now hst hrq (Nat.lt_of_not_le hlt)
    simp [hstays] at hchange

/-! ## Invariant 3 — Commit when dwell satisfied -/

/-- true→false: if dwell satisfied and change is pending, `update` commits. -/
theorem update_tf_commits (h : HS) (now : Nat)
    (hst : h.state = true) (hrq : h.requested = false)
    (hge : now ≥ h.lastChange + h.delayTrue) :
    (hysteresisUpdate h now).state = false := by
  simp [hysteresisUpdate, hst, hrq, hge]

/-- false→true: if dwell satisfied and change is pending, `update` commits. -/
theorem update_ft_commits (h : HS) (now : Nat)
    (hst : h.state = false) (hrq : h.requested = true)
    (hge : now ≥ h.lastChange + h.delayFalse) :
    (hysteresisUpdate h now).state = true := by
  simp [hysteresisUpdate, hst, hrq, hge]

/-! ## Invariant 4 — Zero-delay immediate commitment -/

/-- If delays are zero and a fresh request is made (`newState ≠ requested`),
    `setStateAndUpdate` commits immediately. -/
theorem setStateAndUpdate_zero_delay_fresh (h : HS) (newState : Bool) (now : Nat)
    (hne : newState ≠ h.state) (hnreq : newState ≠ h.requested)
    (hdt : h.delayTrue = 0) (hdf : h.delayFalse = 0) :
    (setStateAndUpdate h newState now).state = newState := by
  rcases Bool.eq_false_or_eq_true newState with hns | hns <;>
  rcases Bool.eq_false_or_eq_true h.state with hst | hst <;>
  rcases Bool.eq_false_or_eq_true h.requested with hrq | hrq <;>
  simp_all [setStateAndUpdate, hysteresisUpdate]

/-! ## Invariant 5 — Request cancellation -/

/-- If `setStateAndUpdate` is called with `newState = h.state`, the pending
    request is cancelled: `requested` returns to `h.state`. -/
theorem setStateAndUpdate_cancel (h : HS) (now : Nat) :
    (setStateAndUpdate h h.state now).requested = h.state := by
  simp only [setStateAndUpdate]
  simp [hysteresisUpdate]

/-- After cancellation the committed state is unchanged. -/
theorem setStateAndUpdate_cancel_state (h : HS) (now : Nat) :
    (setStateAndUpdate h h.state now).state = h.state := by
  simp [setStateAndUpdate, hysteresisUpdate]

/-! ## Constructor invariants -/

/-- Constructor sets `state = requested = initial`. -/
theorem mkHysteresis_state (b : Bool) : (mkHysteresis b).state = b := rfl

/-- Constructor sets `requested = initial`. -/
theorem mkHysteresis_requested (b : Bool) : (mkHysteresis b).requested = b := rfl

/-- Freshly constructed hysteresis has no pending change. -/
theorem mkHysteresis_settled (b : Bool) :
    (mkHysteresis b).requested = (mkHysteresis b).state := rfl

/-- Constructor zero-initialises both dwell times. -/
theorem mkHysteresis_delays (b : Bool) :
    (mkHysteresis b).delayTrue = 0 ∧ (mkHysteresis b).delayFalse = 0 := ⟨rfl, rfl⟩

/-! ## `setHysteresisTimeFrom` -/

/-- Setting delay-from-`true` updates `delayTrue`. -/
theorem setHysteresisTimeFrom_true (h : HS) (d : Nat) :
    (setHysteresisTimeFrom h true d).delayTrue = d := by
  simp [setHysteresisTimeFrom]

/-- Setting delay-from-`false` updates `delayFalse`. -/
theorem setHysteresisTimeFrom_false (h : HS) (d : Nat) :
    (setHysteresisTimeFrom h false d).delayFalse = d := by
  simp [setHysteresisTimeFrom]

/-- Setting delay-from-`true` leaves `delayFalse` unchanged. -/
theorem setHysteresisTimeFrom_true_preserves_false (h : HS) (d : Nat) :
    (setHysteresisTimeFrom h true d).delayFalse = h.delayFalse := by
  simp [setHysteresisTimeFrom]

/-- Setting delay-from-`false` leaves `delayTrue` unchanged. -/
theorem setHysteresisTimeFrom_false_preserves_true (h : HS) (d : Nat) :
    (setHysteresisTimeFrom h false d).delayTrue = h.delayTrue := by
  simp [setHysteresisTimeFrom]

/-- `setHysteresisTimeFrom` does not change the committed `state`. -/
theorem setHysteresisTimeFrom_preserves_state (h : HS) (fromState : Bool) (d : Nat) :
    (setHysteresisTimeFrom h fromState d).state = h.state := by
  rcases Bool.eq_false_or_eq_true fromState with hfs | hfs <;>
  simp [setHysteresisTimeFrom, hfs]

/-! ## Concrete examples (verified by `native_decide`) -/

-- Example 1: zero-delay, immediate true→false transition
example : (setStateAndUpdate (mkHysteresis false) true 100).state = true := by native_decide

-- Example 2: zero-delay, immediate false→true transition
example : (setStateAndUpdate (mkHysteresis true) false 200).state = false := by native_decide

-- Example 3: 500 µs dwell — not yet committed at t=400 (elapsed = 300 < 500)
example :
    let h := { mkHysteresis true with delayTrue := 500 }
    let h1 := setStateAndUpdate h false 100   -- lastChange = 100, state stays true
    let h2 := hysteresisUpdate h1 400          -- 400-100=300 < 500: no commit
    h2.state = true := by native_decide

-- Example 4: 500 µs dwell — committed at t=601 (elapsed = 501 ≥ 500)
example :
    let h := { mkHysteresis true with delayTrue := 500 }
    let h1 := setStateAndUpdate h false 100
    let h2 := hysteresisUpdate h1 601          -- 601-100=501 ≥ 500: commits
    h2.state = false := by native_decide

-- Example 5: request cancellation — pending change cancelled, state stays false
example :
    let h := { mkHysteresis false with delayFalse := 1000 }
    let h1 := setStateAndUpdate h true 0     -- pending true, lastChange=0
    let h2 := setStateAndUpdate h1 false 500 -- cancel (newState=false=state)
    let h3 := hysteresisUpdate h2 2000       -- no pending change
    h3.state = false := by native_decide

-- Example 6: timer restart on direction reversal
example :
    let h := { mkHysteresis false with delayFalse := 1000 }
    let h1 := setStateAndUpdate h true 0     -- pending true, lastChange=0
    let h2 := setStateAndUpdate h1 false 500 -- cancel
    let h3 := setStateAndUpdate h2 true 600  -- restart, lastChange=600
    let h4 := hysteresisUpdate h3 1500        -- 1500-600=900 < 1000: no commit
    let h5 := hysteresisUpdate h3 1601        -- 1601-600=1001 ≥ 1000: commits
    h4.state = false ∧ h5.state = true := by native_decide

end PX4.Hysteresis
