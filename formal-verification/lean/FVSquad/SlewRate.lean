/-!
# SlewRate::update — Formal Verification

🔬 Lean Squad automated formal verification.

This file models and proves correctness properties of `SlewRate::update` from
`src/lib/slew_rate/SlewRate.hpp`.

```cpp
Type update(const Type new_value, const float deltatime)
{
    const Type dvalue_desired = new_value - _value;
    const Type dvalue_max = _slew_rate * deltatime;
    const Type dvalue = math::constrain(dvalue_desired, -dvalue_max, dvalue_max);
    _value += dvalue;
    return _value;
}
```

**Model**: We use `Int` to model the arithmetic, abstracting away floating-point
(IEEE 754 NaN/infinity). `slew_rate` and `dt` are combined into a single integer
`max_step` representing the maximum allowed change per update.

**What is NOT modelled**:
- Float/double arithmetic (NaN, infinity, denormals, rounding)
- Negative `dt` (undefined behaviour in C++)
- Negative `slew_rate` (undefined behaviour, slew_rate must be >= 0)
- Mutable state (`_value` field) -- we model pure step functions with explicit arguments
-/

namespace PX4.SlewRate

/-! ## SlewRate step function -/

/-- Model of one SlewRate::update step.
    `current`: the current value (`_value` before the call)
    `target`:  the desired new value
    `max_step`: slew_rate * deltatime (assumed >= 0)
    Returns the new `_value`.
-/
def slewUpdate (current target max_step : Int) : Int :=
  let d := target - current
  current + if d < -max_step then -max_step
            else if d > max_step then max_step
            else d

-- Unfolding lemma helper for by_cases proofs
private theorem if_cases (c : Prop) [Decidable c] (a b : Int) :
    (if c then a else b) = a ∨ (if c then a else b) = b := by
  by_cases h : c <;> simp [h]

/-! ## Theorems -/

/-- The step change is bounded below by -max_step. -/
theorem slewUpdate_change_ge (current target max_step : Int) (h : 0 ≤ max_step) :
    -max_step ≤ slewUpdate current target max_step - current := by
  simp only [slewUpdate]
  by_cases hlo : target - current < -max_step
  · simp [hlo]; omega
  · by_cases hhi : target - current > max_step
    · simp [show ¬(target - current < -max_step) from hlo, hhi]; omega
    · simp [show ¬(target - current < -max_step) from hlo,
            show ¬(target - current > max_step) from hhi]; omega

/-- The step change is bounded above by max_step. -/
theorem slewUpdate_change_le (current target max_step : Int) (h : 0 ≤ max_step) :
    slewUpdate current target max_step - current ≤ max_step := by
  simp only [slewUpdate]
  by_cases hlo : target - current < -max_step
  · simp [hlo]; omega
  · by_cases hhi : target - current > max_step
    · simp [show ¬(target - current < -max_step) from hlo, hhi]; omega
    · simp [show ¬(target - current < -max_step) from hlo,
            show ¬(target - current > max_step) from hhi]; omega

/-- If the target is already within max_step, the update reaches it exactly. -/
theorem slewUpdate_reaches_target (current target max_step : Int)
    (hdist_lo : -max_step ≤ target - current)
    (hdist_hi : target - current ≤ max_step) :
    slewUpdate current target max_step = target := by
  simp only [slewUpdate]
  simp [show ¬(target - current < -max_step) from by omega,
        show ¬(target - current > max_step) from by omega]
  omega

/-- If target > current, the output is non-decreasing (we move toward target). -/
theorem slewUpdate_nondecreasing (current target max_step : Int) (h : 0 ≤ max_step)
    (hgt : current < target) :
    current ≤ slewUpdate current target max_step := by
  simp only [slewUpdate]
  by_cases hlo : target - current < -max_step
  · simp [hlo]; omega
  · by_cases hhi : target - current > max_step
    · simp [show ¬(target - current < -max_step) from hlo, hhi]; omega
    · simp [show ¬(target - current < -max_step) from hlo,
            show ¬(target - current > max_step) from hhi]; omega

/-- If target < current, the output is non-increasing (we move toward target). -/
theorem slewUpdate_nonincreasing (current target max_step : Int) (h : 0 ≤ max_step)
    (hlt : target < current) :
    slewUpdate current target max_step ≤ current := by
  simp only [slewUpdate]
  by_cases hlo : target - current < -max_step
  · simp [hlo]; omega
  · by_cases hhi : target - current > max_step
    · simp [show ¬(target - current < -max_step) from hlo, hhi]; omega
    · simp [show ¬(target - current < -max_step) from hlo,
            show ¬(target - current > max_step) from hhi]; omega

/-- No overshoot: if moving up (current <= target), the output does not exceed the target. -/
theorem slewUpdate_no_overshoot_up (current target max_step : Int) (h : 0 ≤ max_step)
    (hdir : current ≤ target) :
    slewUpdate current target max_step ≤ target := by
  simp only [slewUpdate]
  by_cases hlo : target - current < -max_step
  · simp [hlo]; omega
  · by_cases hhi : target - current > max_step
    · simp [show ¬(target - current < -max_step) from hlo, hhi]; omega
    · simp [show ¬(target - current < -max_step) from hlo,
            show ¬(target - current > max_step) from hhi]; omega

/-- No overshoot: if moving down (target <= current), the output does not go below target. -/
theorem slewUpdate_no_overshoot_down (current target max_step : Int) (h : 0 ≤ max_step)
    (hdir : target ≤ current) :
    target ≤ slewUpdate current target max_step := by
  simp only [slewUpdate]
  by_cases hlo : target - current < -max_step
  · simp [hlo]; omega
  · by_cases hhi : target - current > max_step
    · simp [show ¬(target - current < -max_step) from hlo, hhi]; omega
    · simp [show ¬(target - current < -max_step) from hlo,
            show ¬(target - current > max_step) from hhi]; omega

/-- If current = target, the output is unchanged (steady state). -/
theorem slewUpdate_steady_state (current max_step : Int) (h : 0 ≤ max_step) :
    slewUpdate current current max_step = current := by
  simp only [slewUpdate, Int.sub_self]
  simp [show ¬((0 : Int) > max_step) from by omega]

-- Concrete spot-checks
example : slewUpdate 0 10 3 = 3 := by native_decide
example : slewUpdate 0 10 15 = 10 := by native_decide
example : slewUpdate 5 0 3 = 2 := by native_decide
example : slewUpdate 5 0 10 = 0 := by native_decide
example : slewUpdate 7 7 5 = 7 := by native_decide

/-! ## Multi-step convergence

The following theorems establish that **iterating `slewUpdate` always terminates at
`target`** within a bounded number of steps.  This is the key liveness property of the
rate limiter: it cannot get "stuck" — it always eventually settles.

Key results:
- `slewIterate_converges_up`  : starting below target, N steps with `target - current ≤ max_step * N` suffice.
- `slewIterate_converges_down`: starting above target, N steps with `current - target ≤ max_step * N` suffice.
-/

/-- N-step iterate of `slewUpdate`: applies the update N times. -/
def slewIterate (n : Nat) (current target max_step : Int) : Int :=
  match n with
  | 0     => current
  | n + 1 => slewIterate n (slewUpdate current target max_step) target max_step

@[simp] theorem slewIterate_zero (current target max_step : Int) :
    slewIterate 0 current target max_step = current := rfl

theorem slewIterate_succ (n : Nat) (current target max_step : Int) :
    slewIterate (n + 1) current target max_step =
    slewIterate n (slewUpdate current target max_step) target max_step := rfl

/-- Once at target, all further iterations stay at target. -/
theorem slewIterate_steady (n : Nat) (target max_step : Int) (h : 0 ≤ max_step) :
    slewIterate n target target max_step = target := by
  induction n with
  | zero    => simp
  | succ n ih => rw [slewIterate_succ, slewUpdate_steady_state target max_step h, ih]

/-- When `max_step < target − current`, one step advances by exactly `max_step`. -/
private theorem slewUpdate_far_up (current target max_step : Int)
    (h_step : 0 < max_step) (h_far : max_step < target - current) :
    slewUpdate current target max_step = current + max_step := by
  simp only [slewUpdate]
  have hlo : ¬(target - current < -max_step) := by omega
  have hhi : target - current > max_step     := by omega
  simp [hlo, hhi]

/-- When `max_step < current − target`, one step retreats by exactly `max_step`. -/
private theorem slewUpdate_far_down (current target max_step : Int)
    (_h_step : 0 < max_step) (h_far : max_step < current - target) :
    slewUpdate current target max_step = current - max_step := by
  simp only [slewUpdate]
  have hlo : target - current < -max_step := by omega
  simp [hlo]; omega

/-- **Upward convergence**: starting at or below `target`, N steps suffice when
    `target − current ≤ max_step × N`.

    Each step either reaches `target` directly (if within range) or advances by
    exactly `max_step`, reducing the remaining distance by `max_step`. -/
theorem slewIterate_converges_up (current target max_step : Int)
    (h_step : 0 < max_step)
    (h_dir  : current ≤ target)
    (N : Nat) (h_N : target - current ≤ max_step * N) :
    slewIterate N current target max_step = target := by
  induction N generalizing current with
  | zero    => simp [slewIterate]; omega
  | succ n ih =>
    rw [slewIterate_succ]
    by_cases h : target - current ≤ max_step
    · -- Within range: one step reaches target; then steady state holds.
      have heq : slewUpdate current target max_step = target :=
        slewUpdate_reaches_target current target max_step (by omega) h
      rw [heq]
      exact slewIterate_steady n target max_step (by omega)
    · -- Too far: advance by max_step; apply IH on the shorter gap.
      have h' : max_step < target - current := by omega
      rw [slewUpdate_far_up current target max_step h_step h']
      have h_dist : target - (current + max_step) ≤ max_step * (↑n : Int) :=
        calc target - (current + max_step)
            = (target - current) - max_step  := by omega
          _ ≤ max_step * ↑(n + 1) - max_step := by omega
          _ = max_step * ↑n                  := by simp [Int.mul_add]
      exact ih (current + max_step) (by omega) h_dist

/-- **Downward convergence**: starting at or above `target`, N steps suffice when
    `current − target ≤ max_step × N`. -/
theorem slewIterate_converges_down (current target max_step : Int)
    (h_step : 0 < max_step)
    (h_dir  : target ≤ current)
    (N : Nat) (h_N : current - target ≤ max_step * N) :
    slewIterate N current target max_step = target := by
  induction N generalizing current with
  | zero    => simp [slewIterate]; omega
  | succ n ih =>
    rw [slewIterate_succ]
    by_cases h : current - target ≤ max_step
    · -- Within range: one step reaches target.
      have heq : slewUpdate current target max_step = target :=
        slewUpdate_reaches_target current target max_step (by omega) (by omega)
      rw [heq]
      exact slewIterate_steady n target max_step (by omega)
    · -- Too far: retreat by max_step; apply IH on the shorter gap.
      have h' : max_step < current - target := by omega
      rw [slewUpdate_far_down current target max_step h_step h']
      have h_dist : (current - max_step) - target ≤ max_step * (↑n : Int) :=
        calc (current - max_step) - target
            = (current - target) - max_step  := by omega
          _ ≤ max_step * ↑(n + 1) - max_step := by omega
          _ = max_step * ↑n                  := by simp [Int.mul_add]
      exact ih (current - max_step) (by omega) h_dist

-- Concrete convergence spot-checks
example : slewIterate 4 0 10 3 = 10 := by native_decide  -- 0→3→6→9→10
example : slewIterate 2 10 0 5  = 0  := by native_decide  -- 10→5→0
example : slewIterate 3 10 0 5  = 0  := by native_decide  -- stable past convergence
example : slewIterate 2  7 7 3  = 7  := by native_decide  -- already at target

end PX4.SlewRate


