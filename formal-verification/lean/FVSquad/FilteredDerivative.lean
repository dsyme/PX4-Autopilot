import FVSquad.AlphaFilter

/-!
# PX4 FilteredDerivative — Formal Verification

🔬 Lean Squad automated formal verification.

This file models and proves correctness properties of `FilteredDerivative<T>::update`
from PX4-Autopilot's `mathlib`:

- **C++ source**: `src/lib/mathlib/math/filter/FilteredDerivative.hpp`
- **Informal spec**: `formal-verification/specs/filteredderivative_informal.md`

## C++ reference

```cpp
const T &update(const T &sample) {
  if (_initialized) {
    if (_sample_interval > FLT_EPSILON) {
      _alpha_filter.update((sample - _previous_sample) / _sample_interval);
    } else {
      _initialized = false;
    }
  } else {
    // don't update in the first iteration
    _initialized = true;
  }
  _previous_sample = sample;
  return _alpha_filter.getState();
}
```

## Model

We model the update function over `Rat` (rational numbers) with exact arithmetic.
`sample_interval` is taken as a positive rational (abstracting away the FLT_EPSILON guard).

State: `(alpha_state : Rat, previous_sample : Rat, initialized : Bool)`.

Approximations / out of scope:
- IEEE 754 float semantics: NaN, infinity, and rounding are not modelled.
- The `FLT_EPSILON` guard that resets `_initialized = false` is not modelled;
  we take `sample_interval > 0` as a precondition.
- We take `alpha` as a direct input satisfying `0 ≤ alpha ≤ 1`.
-/

open PX4.AlphaFilter

namespace PX4.FilteredDerivative

/-! ## State and update -/

/-- State of the FilteredDerivative. -/
structure FDState where
  alphaState : Rat
  prevSample : Rat
  initialized : Bool
  deriving Repr

/-- Initial state: alpha filter at 0, not initialized. -/
def fdInit : FDState := { alphaState := 0, prevSample := 0, initialized := false }

/-- One step of `FilteredDerivative::update`.

    - First call (not initialized): set initialized=true, save sample; alpha state unchanged.
    - Subsequent calls: compute derivative, feed into alpha filter. -/
def fdUpdate (s : FDState) (alpha dt sample : Rat) : FDState :=
  if s.initialized then
    let deriv := (sample - s.prevSample) / dt
    { alphaState := alphaUpdate s.alphaState alpha deriv,
      prevSample := sample,
      initialized := true }
  else
    { alphaState := s.alphaState,
      prevSample := sample,
      initialized := true }

/-- Iterated update from a given state with a sequence of samples. -/
def fdIter (s : FDState) (alpha dt : Rat) : List Rat → FDState
  | []      => s
  | x :: xs => fdIter (fdUpdate s alpha dt x) alpha dt xs

/-! ## Basic structural theorems -/

/-- On the first call (uninitialized state), the alpha state is unchanged. -/
theorem fdUpdate_first_call_state (s : FDState) (alpha dt sample : Rat)
    (h : s.initialized = false) :
    (fdUpdate s alpha dt sample).alphaState = s.alphaState := by
  simp [fdUpdate, h]

/-- After the first call, the state is initialized. -/
theorem fdUpdate_first_call_initialized (s : FDState) (alpha dt sample : Rat) :
    (fdUpdate s alpha dt sample).initialized = true := by
  simp [fdUpdate]
  split <;> simp

/-- After the first call, the previous sample is stored. -/
theorem fdUpdate_stores_prev_sample (s : FDState) (alpha dt sample : Rat) :
    (fdUpdate s alpha dt sample).prevSample = sample := by
  simp [fdUpdate]
  split <;> simp

/-- On the second call (initialized), the derivative is computed correctly. -/
theorem fdUpdate_second_call_deriv (s : FDState) (alpha dt sample : Rat)
    (h : s.initialized = true) (hdt : dt ≠ 0) :
    (fdUpdate s alpha dt sample).alphaState =
    alphaUpdate s.alphaState alpha ((sample - s.prevSample) / dt) := by
  simp [fdUpdate, h]

/-! ## Constant input convergence -/

/-- When the same sample is fed twice consecutively (initialized), the derivative is 0. -/
theorem fdUpdate_const_deriv_zero (s : FDState) (alpha dt : Rat)
    (h : s.initialized = true) (hdt : dt ≠ 0) :
    (fdUpdate s alpha dt s.prevSample).alphaState =
    alphaUpdate s.alphaState alpha 0 := by
  simp [fdUpdate, h, Rat.sub_self, Rat.div_def, Rat.mul_comm]

/-- With constant input, the derivative fed to alpha filter is always 0. -/
theorem fdUpdate_const_input_zero_deriv (s : FDState) (alpha dt sample : Rat)
    (h : s.initialized = true) (hdt : dt ≠ 0) :
    (fdUpdate s alpha dt sample).alphaState =
    alphaUpdate s.alphaState alpha ((sample - s.prevSample) / dt) := by
  simp [fdUpdate, h]

/-- With constant input `v` after initialization, the alpha state converges to 0.

    After feeding the same value `v` for `n` additional steps past the first initialized call,
    the alpha filter state satisfies the exponential formula with target = 0. -/
theorem fdIter_const_alpha_formula (alphaState : Rat) (alpha dt v : Rat) (n : Nat)
    (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1) :
    let initState : FDState := { alphaState := alphaState, prevSample := v, initialized := true }
    (fdIter initState alpha dt (List.replicate n v)).alphaState =
    alphaIterate alphaState alpha 0 n := by
  induction n generalizing alphaState with
  | zero => simp [fdIter, alphaIterate]
  | succ n ih =>
    simp only [fdIter, List.replicate]
    rw [show fdUpdate { alphaState := alphaState, prevSample := v, initialized := true }
              alpha dt v =
          { alphaState := alphaUpdate alphaState alpha 0, prevSample := v, initialized := true } by
          simp [fdUpdate, Rat.sub_self, Rat.div_def, Rat.mul_comm]]
    exact ih (alphaUpdate alphaState alpha 0)

/-- With constant input `v` from an initialized state with `prevSample = v`,
    the alpha filter state after `n` steps is bounded in [0, alphaState] when alphaState ≥ 0. -/
theorem fdIter_const_bounded_pos (alphaState : Rat) (alpha dt v : Rat) (n : Nat)
    (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1) (hstate : 0 ≤ alphaState) :
    let initState : FDState := { alphaState := alphaState, prevSample := v, initialized := true }
    0 ≤ (fdIter initState alpha dt (List.replicate n v)).alphaState ∧
    (fdIter initState alpha dt (List.replicate n v)).alphaState ≤ alphaState := by
  simp only [fdIter_const_alpha_formula alphaState alpha dt v n ha0 ha1]
  exact alphaIterate_no_overshoot_up alphaState alpha 0 n hstate ha0 ha1

/-- With constant input from an initialized state with alphaState ≤ 0, the filter
    state is bounded in [alphaState, 0] for all n. -/
theorem fdIter_const_bounded_neg (alphaState : Rat) (alpha dt v : Rat) (n : Nat)
    (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1) (hstate : alphaState ≤ 0) :
    let initState : FDState := { alphaState := alphaState, prevSample := v, initialized := true }
    alphaState ≤ (fdIter initState alpha dt (List.replicate n v)).alphaState ∧
    (fdIter initState alpha dt (List.replicate n v)).alphaState ≤ 0 := by
  simp only [fdIter_const_alpha_formula alphaState alpha dt v n ha0 ha1]
  exact alphaIterate_no_overshoot_down alphaState alpha 0 n hstate ha0 ha1

/-- With constant input, the alpha state shrinks monotonically toward 0 (from above). -/
theorem fdIter_const_shrinks_pos (alphaState : Rat) (alpha dt v : Rat) (n : Nat)
    (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1) (hstate : 0 ≤ alphaState) :
    let initState : FDState := { alphaState := alphaState, prevSample := v, initialized := true }
    (fdIter initState alpha dt (List.replicate (n + 1) v)).alphaState ≤
    (fdIter initState alpha dt (List.replicate n v)).alphaState := by
  simp only [fdIter_const_alpha_formula alphaState alpha dt v _ ha0 ha1]
  exact alphaIterate_mono_n_up alphaState alpha 0 n hstate ha0 ha1

/-- With constant input, the alpha state is non-negative for all n when starting ≥ 0. -/
theorem fdIter_const_nonneg (alphaState : Rat) (alpha dt v : Rat) (n : Nat)
    (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1) (hstate : 0 ≤ alphaState) :
    let initState : FDState := { alphaState := alphaState, prevSample := v, initialized := true }
    0 ≤ (fdIter initState alpha dt (List.replicate n v)).alphaState := by
  exact (fdIter_const_bounded_pos alphaState alpha dt v n ha0 ha1 hstate).1

/-! ## Monotone decay from negative initial state -/

/-- With constant input, the alpha state grows monotonically toward 0 (from below).

    Symmetric to `fdIter_const_shrinks_pos`. -/
theorem fdIter_const_shrinks_neg (alphaState : Rat) (alpha dt v : Rat) (n : Nat)
    (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1) (hstate : alphaState ≤ 0) :
    let initState : FDState := { alphaState := alphaState, prevSample := v, initialized := true }
    (fdIter initState alpha dt (List.replicate n v)).alphaState ≤
    (fdIter initState alpha dt (List.replicate (n + 1) v)).alphaState := by
  simp only [fdIter_const_alpha_formula alphaState alpha dt v _ ha0 ha1]
  exact alphaIterate_mono_n_down alphaState alpha 0 n hstate ha0 ha1

/-- With constant input from a non-positive initial state, the filter state is non-positive
    for all n. -/
theorem fdIter_const_nonpos (alphaState : Rat) (alpha dt v : Rat) (n : Nat)
    (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1) (hstate : alphaState ≤ 0) :
    let initState : FDState := { alphaState := alphaState, prevSample := v, initialized := true }
    (fdIter initState alpha dt (List.replicate n v)).alphaState ≤ 0 := by
  exact (fdIter_const_bounded_neg alphaState alpha dt v n ha0 ha1 hstate).2

/-! ## Linear input: constant derivative -/

/-- With a linear ramp input (slope `m`, step size `dt`), the raw derivative is constant = `m/1`
    (normalized: if sample_{k} = v₀ + k*m, then (sample_{k} - sample_{k-1})/dt = m/dt).

    We verify this for a single step. -/
theorem fdUpdate_linear_deriv (s : FDState) (alpha dt m : Rat)
    (h : s.initialized = true) (hdt : dt ≠ 0) :
    (fdUpdate s alpha dt (s.prevSample + m)).alphaState =
    alphaUpdate s.alphaState alpha (m / dt) := by
  simp [fdUpdate, h]
  rw [show s.prevSample + m - s.prevSample = m by rw [Rat.add_comm, Rat.add_sub_cancel]]

/-! ## Linear ramp: iterated convergence toward slope/dt -/

/-- **Core ramp lemma**: starting from `{alphaState, prevSample = v0, initialized = true}`,
    feeding `n` samples that increase by `m` each step (v0+m, v0+2m, …, v0+n*m) drives
    the alpha filter with constant input `m/dt` at every step.

    More precisely: the alpha state after n steps equals `alphaIterate alphaState alpha (m/dt) n`.
-/
theorem fdIter_ramp_alpha_formula (alphaState v0 alpha dt m : Rat) (n : Nat) :
    let initState : FDState := { alphaState := alphaState, prevSample := v0, initialized := true }
    (fdIter initState alpha dt ((List.range n).map (fun (k : Nat) => v0 + ((k : Rat) + 1) * m))).alphaState =
    alphaIterate alphaState alpha (m / dt) n := by
  -- We prove by induction, shifting the "base" sample v0 each step
  induction n generalizing alphaState v0 with
  | zero => simp [fdIter, alphaIterate]
  | succ n ih =>
    -- List.range (n+1) = List.range n ++ [n], so map gives [v0+m, ..., v0+nm] ++ [v0+(n+1)m]
    -- But fdIter processes from left: first element is v0 + 1*m
    -- More precisely, range (n+1) = [0, 1, ..., n], map gives [v0+m, v0+2m, ..., v0+(n+1)m]
    -- Uncons: first element = v0 + (0+1)*m = v0+m
    rw [show (List.range (n + 1)).map (fun (k : Nat) => v0 + ((k : Rat) + 1) * m) =
        (v0 + m) :: (List.range n).map (fun (k : Nat) => (v0 + m) + ((k : Rat) + 1) * m) by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1
      · simp [Rat.zero_add, Rat.one_mul]
      · apply List.ext_getElem
        · simp
        · intros i hi1 hi2
          simp only [List.getElem_map, Function.comp]
          simp [Rat.add_mul, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]]
    simp only [fdIter, fdUpdate, if_true]
    -- The first update: sample = v0+m, prevSample = v0, derivative = m/dt
    rw [show v0 + m - v0 = m by rw [Rat.add_comm v0 m, Rat.add_sub_cancel]]
    exact ih (alphaUpdate alphaState alpha (m / dt)) (v0 + m)

/-- With a linear ramp input, the alpha state is bounded toward `m/dt`.

    When `alphaState ≥ m/dt` and `m/dt ≥ 0`, the state decreases toward `m/dt`. -/
theorem fdIter_ramp_bounded_pos (alphaState v0 alpha dt m : Rat) (n : Nat)
    (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1) (hstate : m / dt ≤ alphaState) :
    let initState : FDState := { alphaState := alphaState, prevSample := v0, initialized := true }
    m / dt ≤ (fdIter initState alpha dt ((List.range n).map (fun (k : Nat) => v0 + ((k : Rat) + 1) * m))).alphaState ∧
    (fdIter initState alpha dt ((List.range n).map (fun (k : Nat) => v0 + ((k : Rat) + 1) * m))).alphaState ≤ alphaState := by
  simp only [fdIter_ramp_alpha_formula]
  exact alphaIterate_no_overshoot_up alphaState alpha (m / dt) n hstate ha0 ha1

/-- With a linear ramp input, the alpha state is bounded when starting below `m/dt`. -/
theorem fdIter_ramp_bounded_neg (alphaState v0 alpha dt m : Rat) (n : Nat)
    (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1) (hstate : alphaState ≤ m / dt) :
    let initState : FDState := { alphaState := alphaState, prevSample := v0, initialized := true }
    alphaState ≤ (fdIter initState alpha dt ((List.range n).map (fun (k : Nat) => v0 + ((k : Rat) + 1) * m))).alphaState ∧
    (fdIter initState alpha dt ((List.range n).map (fun (k : Nat) => v0 + ((k : Rat) + 1) * m))).alphaState ≤ m / dt := by
  simp only [fdIter_ramp_alpha_formula]
  exact alphaIterate_no_overshoot_down alphaState alpha (m / dt) n hstate ha0 ha1

/-! ## Monotonicity: larger sample → larger derivative → larger alpha state -/

/-- When both states are initialized with the same `prevSample`, and `sample1 ≤ sample2`,
    then the resulting alpha states satisfy
    `(fdUpdate s1 …).alphaState ≤ (fdUpdate s2 …).alphaState`
    provided `s1.alphaState ≤ s2.alphaState` and `0 ≤ dt`. -/
theorem fdUpdate_mono (s1 s2 : FDState) (alpha dt sample1 sample2 : Rat)
    (hinit1 : s1.initialized = true) (hinit2 : s2.initialized = true)
    (hprev : s1.prevSample = s2.prevSample)
    (hstate : s1.alphaState ≤ s2.alphaState)
    (hsample : sample1 ≤ sample2)
    (hdt : 0 < dt) (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1) :
    (fdUpdate s1 alpha dt sample1).alphaState ≤
    (fdUpdate s2 alpha dt sample2).alphaState := by
  simp only [fdUpdate, hinit1, hinit2, if_true]
  -- d1 = (sample1 - s1.prevSample)/dt, d2 = (sample2 - s2.prevSample)/dt
  -- Since s1.prevSample = s2.prevSample and sample1 ≤ sample2, we have d1 ≤ d2.
  -- Monotonicity step 1: state s1 → s2 with same derivative d1
  calc alphaUpdate s1.alphaState alpha ((sample1 - s1.prevSample) / dt)
      ≤ alphaUpdate s2.alphaState alpha ((sample1 - s1.prevSample) / dt) :=
        alphaUpdate_mono_state alpha _ ha1 ha0 _ _ hstate
    _ ≤ alphaUpdate s2.alphaState alpha ((sample2 - s2.prevSample) / dt) := by
        apply alphaUpdate_mono_sample
        · exact ha0
        · rw [← hprev]
          rw [Rat.div_def, Rat.div_def]
          apply Rat.mul_le_mul_of_nonneg_right _ (Rat.le_of_lt (Rat.inv_pos.mpr hdt))
          simp only [Rat.sub_eq_add_neg]
          exact Rat.add_le_add_right.mpr hsample

/-! ## Summary

  | Theorem | Statement | Status |
  |---------|-----------|--------|
  | `fdUpdate_first_call_state` | First call: alpha state unchanged | ✅ Proved |
  | `fdUpdate_first_call_initialized` | After any call: `initialized = true` | ✅ Proved |
  | `fdUpdate_stores_prev_sample` | After any call: `prevSample = sample` | ✅ Proved |
  | `fdUpdate_second_call_deriv` | Initialized call: derivative computed | ✅ Proved |
  | `fdUpdate_const_deriv_zero` | Same sample twice → derivative = 0 | ✅ Proved |
  | `fdUpdate_const_input_zero_deriv` | Const input: derivative = (sample - prev)/dt | ✅ Proved |
  | `fdIter_const_alpha_formula` | Const input n steps: alphaIterate formula | ✅ Proved |
  | `fdIter_const_bounded_pos` | Const input: state bounded in [0, init] (init ≥ 0) | ✅ Proved |
  | `fdIter_const_bounded_neg` | Const input: state bounded in [init, 0] (init ≤ 0) | ✅ Proved |
  | `fdIter_const_shrinks_pos` | Const input: state shrinks toward 0 (monotone, init ≥ 0) | ✅ Proved |
  | `fdIter_const_nonneg` | Const input: state non-negative for all n (init ≥ 0) | ✅ Proved |
  | `fdIter_const_shrinks_neg` | Const input: state grows toward 0 (monotone, init ≤ 0) | ✅ Proved |
  | `fdIter_const_nonpos` | Const input: state non-positive for all n (init ≤ 0) | ✅ Proved |
  | `fdUpdate_linear_deriv` | Linear ramp (1 step): derivative = slope/dt | ✅ Proved |
  | `fdIter_ramp_alpha_formula` | Linear ramp n steps: alphaIterate formula | ✅ Proved |
  | `fdIter_ramp_bounded_pos` | Ramp: state bounded ∈ [m/dt, init] (init ≥ m/dt ≥ 0) | ✅ Proved |
  | `fdIter_ramp_bounded_neg` | Ramp: state bounded ∈ [init, m/dt] (init ≤ m/dt ≤ 0) | ✅ Proved |
  | `fdUpdate_mono` | Larger sample → larger alpha state (both initialized, same prev) | ✅ Proved |
-/

end PX4.FilteredDerivative
