/-!
# PX4 AlphaFilter — Formal Verification

🔬 Lean Squad automated formal verification.

This file models and proves correctness properties of `AlphaFilter<T>::updateCalculation`
from PX4-Autopilot's `mathlib`:

- **C++ source**: `src/lib/mathlib/math/filter/AlphaFilter.hpp`
- **Informal spec**: `formal-verification/specs/alphafilter_informal.md`

## C++ reference

```cpp
template <typename T>
T AlphaFilter<T>::updateCalculation(const T &sample) {
  return _filter_state + _alpha * (sample - _filter_state);
}
```

This is a first-order IIR low-pass filter (leaky integrator).  Alpha ∈ [0, 1] controls
the blend: `new_state = old_state + alpha * (sample - old_state)`.

## Model

We model the single-step update over `Rat` (rational numbers) with exact arithmetic.

- Takes `state`, `alpha`, `sample` as explicit rational arguments.
- Returns the new state value (does not mutate).
- Alpha must satisfy `0 ≤ alpha ≤ 1`.

## Approximations / out of scope

- **IEEE 754 float semantics**: NaN, infinity, and rounding are not modelled.
- **State mutation**: the C++ class mutates `_filter_state` in place; here we return new values.
- **Quaternion specialisation**: the SO(3) specialisation uses axis-angle interpolation; only
  the scalar/Euclidean case is modelled.
- **`setParameters` / `setCutoffFreq`**: parameter-setting logic is not modelled; we take
  `alpha` as a direct input assumed to satisfy `0 ≤ alpha ≤ 1`.
- **Exponential convergence**: requires real analysis (Mathlib topology); we prove only
  discrete-step no-overshoot and monotonicity properties over `Rat`.
-/

namespace PX4.AlphaFilter

/-! ## Core definition -/

/-- Single-step alpha filter update.
    Models `_filter_state + _alpha * (sample - _filter_state)`. -/
def alphaUpdate (state alpha sample : Rat) : Rat :=
  state + alpha * (sample - state)

-- Sanity checks: spot-check the model against expected outputs
#eval alphaUpdate 0 0 1           -- 0     (alpha=0: state unchanged)
#eval alphaUpdate 0 1 1           -- 1     (alpha=1: state = sample immediately)
#eval alphaUpdate 0 (1/2) 1       -- 1/2
#eval alphaUpdate (1/2) (1/2) 1   -- 3/4
#eval alphaUpdate 1 (1/10) 0      -- 9/10
#eval alphaUpdate (-1) (1/2) 1    -- 0

/-! ## Boundary cases -/

/-- Fixed point: if `sample = state`, the update is the identity. -/
theorem alphaUpdate_fixed (state alpha : Rat) :
    alphaUpdate state alpha state = state := by
  simp [alphaUpdate, Rat.sub_self, Rat.mul_zero, Rat.add_zero]

/-- At `alpha = 0` the state is frozen regardless of sample. -/
theorem alphaUpdate_alpha_zero (state sample : Rat) :
    alphaUpdate state 0 sample = state := by
  simp [alphaUpdate, Rat.zero_mul, Rat.add_zero]

/-- At `alpha = 1` the state immediately equals the sample. -/
theorem alphaUpdate_alpha_one (state sample : Rat) :
    alphaUpdate state 1 sample = sample := by
  simp only [alphaUpdate, Rat.one_mul]
  rw [Rat.add_comm, Rat.sub_add_cancel]

/-! ## No-overshoot: upward case (state ≤ sample) -/

/-- Upper no-overshoot: when `state ≤ sample`, the new state does not exceed `sample`. -/
theorem alphaUpdate_le_sample (state alpha sample : Rat)
    (h_le : state ≤ sample) (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1) :
    alphaUpdate state alpha sample ≤ sample := by
  simp only [alphaUpdate]
  -- key: alpha*(sample - state) ≤ 1*(sample - state) = sample - state
  have hd : 0 ≤ sample - state := (Rat.le_iff_sub_nonneg state sample).mp h_le
  have key : alpha * (sample - state) ≤ 1 * (sample - state) :=
    Rat.mul_le_mul_of_nonneg_right ha1 hd
  rw [Rat.one_mul] at key
  calc state + alpha * (sample - state)
      = alpha * (sample - state) + state := Rat.add_comm _ _
    _ ≤ (sample - state) + state         := (Rat.add_le_add_right (c := state)).mpr key
    _ = sample                            := by rw [Rat.sub_add_cancel]

/-- Lower no-overshoot: when `state ≤ sample`, the new state is at least `state`. -/
theorem alphaUpdate_ge_state (state alpha sample : Rat)
    (h_le : state ≤ sample) (ha0 : 0 ≤ alpha) :
    state ≤ alphaUpdate state alpha sample := by
  simp only [alphaUpdate]
  have hd : 0 ≤ sample - state := (Rat.le_iff_sub_nonneg state sample).mp h_le
  have key : 0 ≤ alpha * (sample - state) := Rat.mul_nonneg ha0 hd
  calc state = 0 + state                          := (Rat.zero_add state).symm
    _ ≤ alpha * (sample - state) + state          := (Rat.add_le_add_right (c := state)).mpr key
    _ = state + alpha * (sample - state)          := Rat.add_comm _ _

/-- No-overshoot (upward): `state ≤ new_state ≤ sample` when `state ≤ sample`. -/
theorem alphaUpdate_no_overshoot_up (state alpha sample : Rat)
    (h_le : state ≤ sample) (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1) :
    state ≤ alphaUpdate state alpha sample ∧ alphaUpdate state alpha sample ≤ sample :=
  ⟨alphaUpdate_ge_state state alpha sample h_le ha0,
   alphaUpdate_le_sample state alpha sample h_le ha0 ha1⟩

/-! ## No-overshoot: downward case (sample ≤ state) -/

/-- Lower no-overshoot (downward): when `sample ≤ state`, the new state is at most `state`.

    Proof: `(1-alpha)*(state - sample) ≥ 0`, so new_state ≤ state.
    TODO: complete this proof — the same algebra as the upward case but negated. -/
theorem alphaUpdate_le_state (state alpha sample : Rat)
    (h_le : sample ≤ state) (ha0 : 0 ≤ alpha) :
    alphaUpdate state alpha sample ≤ state := by
  simp only [alphaUpdate]
  -- state - sample ≥ 0
  have hd : 0 ≤ state - sample := (Rat.le_iff_sub_nonneg sample state).mp h_le
  -- sample - state ≤ 0  (by calc: sample-state ≤ state-state = 0)
  have hdn : sample - state ≤ 0 :=
    calc sample - state ≤ state - state := by
            rw [Rat.sub_eq_add_neg, Rat.sub_eq_add_neg]
            exact (Rat.add_le_add_right (c := -state)).mpr h_le
      _ = 0 := Rat.sub_self
  -- alpha*(sample - state) ≤ 0
  have key : alpha * (sample - state) ≤ 0 := by
    rw [show (0 : Rat) = alpha * 0 from (Rat.mul_zero alpha).symm]
    exact Rat.mul_le_mul_of_nonneg_left hdn ha0
  calc state + alpha * (sample - state)
      = alpha * (sample - state) + state := Rat.add_comm _ _
    _ ≤ 0 + state                        := (Rat.add_le_add_right (c := state)).mpr key
    _ = state                            := Rat.zero_add state

/-- Upper no-overshoot (downward): when `sample ≤ state`, the new state is at least `sample`.

    TODO: complete this proof. -/
theorem alphaUpdate_ge_sample (state alpha sample : Rat)
    (h_le : sample ≤ state) (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1) :
    sample ≤ alphaUpdate state alpha sample := by
  simp only [alphaUpdate]
  -- Need: sample ≤ state + alpha*(sample - state)
  -- ⟺ sample - state ≤ alpha*(sample - state)   [since sample - state ≤ 0 and alpha ≤ 1]
  -- ⟺ 1*(sample - state) ≤ alpha*(sample - state)
  -- which follows since (sample - state) ≤ 0 and alpha ≤ 1 (flip inequality for negatives)
  have hd : 0 ≤ state - sample := (Rat.le_iff_sub_nonneg sample state).mp h_le
  have hdn : sample - state ≤ 0 :=
    calc sample - state ≤ state - state := by
            rw [Rat.sub_eq_add_neg, Rat.sub_eq_add_neg]
            exact (Rat.add_le_add_right (c := -state)).mpr h_le
      _ = 0 := Rat.sub_self
  have key : 1 * (sample - state) ≤ alpha * (sample - state) := by
    sorry -- needs: c ≤ 0 → alpha ≤ 1 → 1*c ≤ alpha*c (mul by nonpositive flips order)
  rw [Rat.one_mul] at key
  calc sample
      = (sample - state) + state   := by rw [Rat.sub_add_cancel]
    _ ≤ alpha * (sample - state) + state := (Rat.add_le_add_right (c := state)).mpr key
    _ = state + alpha * (sample - state)  := Rat.add_comm _ _

/-- No-overshoot (downward): `sample ≤ new_state ≤ state` when `sample ≤ state`. -/
theorem alphaUpdate_no_overshoot_down (state alpha sample : Rat)
    (h_le : sample ≤ state) (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1) :
    sample ≤ alphaUpdate state alpha sample ∧ alphaUpdate state alpha sample ≤ state :=
  ⟨alphaUpdate_ge_sample state alpha sample h_le ha0 ha1,
   alphaUpdate_le_state state alpha sample h_le ha0⟩

/-! ## Monotonicity -/

/-- Update is nondecreasing in `sample`: a larger input produces a larger output. -/
theorem alphaUpdate_mono_sample (state alpha : Rat)
    (ha0 : 0 ≤ alpha) (s1 s2 : Rat) (hs : s1 ≤ s2) :
    alphaUpdate state alpha s1 ≤ alphaUpdate state alpha s2 := by
  simp only [alphaUpdate]
  have hs_diff : s1 - state ≤ s2 - state := by
    rw [Rat.sub_eq_add_neg, Rat.sub_eq_add_neg]
    exact (Rat.add_le_add_right (c := -state)).mpr hs
  have key : alpha * (s1 - state) ≤ alpha * (s2 - state) :=
    Rat.mul_le_mul_of_nonneg_left hs_diff ha0
  rw [show state + alpha * (s1 - state) = alpha * (s1 - state) + state from Rat.add_comm _ _,
      show state + alpha * (s2 - state) = alpha * (s2 - state) + state from Rat.add_comm _ _]
  exact (Rat.add_le_add_right (c := state)).mpr key

/-- Update is nondecreasing in initial state: larger `state` → larger output (alpha ≤ 1). -/
theorem alphaUpdate_mono_state (alpha sample : Rat)
    (ha1 : alpha ≤ 1) (ha0 : 0 ≤ alpha) (s1 s2 : Rat) (hs : s1 ≤ s2) :
    alphaUpdate s1 alpha sample ≤ alphaUpdate s2 alpha sample := by
  simp only [alphaUpdate]
  -- s1 + alpha*(sample - s1) ≤ s2 + alpha*(sample - s2)
  -- ⟺ s1*(1 - alpha) ≤ s2*(1 - alpha)  (cancel alpha*sample, use distributivity)
  -- We show difference is nonneg: (s2 - s1)*(1 - alpha) ≥ 0
  have h1a : 0 ≤ 1 - alpha := (Rat.le_iff_sub_nonneg alpha 1).mp ha1
  have hsd : 0 ≤ s2 - s1 := (Rat.le_iff_sub_nonneg s1 s2).mp hs
  -- Direct: the difference of the two sides equals (s2 - s1) * (1 - alpha) ≥ 0
  -- We use the convex form via a sorry for the algebraic identity
  sorry -- needs ring: s1 + alpha*(sample-s1) ≤ s2 + alpha*(sample-s2)

/-! ## Iterated update -/

/-- Iterated update: `n` steps with constant input `target`. -/
def alphaIterate (state alpha target : Rat) : Nat → Rat
  | 0     => state
  | n + 1 => alphaIterate (alphaUpdate state alpha target) alpha target n

-- Spot checks for iterated update
#eval alphaIterate 0 (1/10) 1 9   -- ≈ 0.613 (should be near 1 - (9/10)^9 ≈ 0.613)
#eval alphaIterate 0 (1/10) 1 90  -- should be near 1 - (9/10)^90 ≈ 0.9999

/-- After `n` steps with constant input `target`:
    `state_n = target + (state₀ - target) * (1 - alpha)^n`.

    This is the standard exponential filter closed-form formula, proved by induction.

    TODO: Lean 4 stdlib `Rat` does not expose `ring` or `norm_num` without Mathlib, so the
    algebraic step in the inductive case requires `sorry`. The formula is correct and
    matches the `#eval` checks above. -/
theorem alphaIterate_formula (state alpha target : Rat) (n : Nat) :
    alphaIterate state alpha target n =
    target + (state - target) * (1 - alpha) ^ n := by
  induction n with
  | zero =>
    simp only [alphaIterate]
    -- Goal: state = target + (state - target) * (1 - alpha) ^ 0
    have h0 : (1 - alpha) ^ (0 : Nat) = 1 := by simp
    rw [h0, Rat.mul_one,
        show target + (state - target) = (state - target) + target from Rat.add_comm _ _]
    exact Rat.sub_add_cancel.symm
  | succ n ih =>
    simp only [alphaIterate, ih]
    sorry -- algebraic step: needs ring over Rat

/-! ## Summary of proved properties

  | Theorem                        | Statement                                                  | Status    |
  |--------------------------------|------------------------------------------------------------|-----------|
  | `alphaUpdate_fixed`            | `update s a s = s` (sample = state → no change)           | ✅ Proved |
  | `alphaUpdate_alpha_zero`       | `update s 0 x = s` (alpha=0: frozen)                      | ✅ Proved |
  | `alphaUpdate_alpha_one`        | `update s 1 x = x` (alpha=1: immediate)                   | ✅ Proved |
  | `alphaUpdate_le_sample`        | `s ≤ x, 0 ≤ a ≤ 1 → update ≤ x`  (upper bound, ↑ case)   | ✅ Proved |
  | `alphaUpdate_ge_state`         | `s ≤ x, 0 ≤ a → s ≤ update`       (lower bound, ↑ case)   | ✅ Proved |
  | `alphaUpdate_no_overshoot_up`  | `s ≤ x → s ≤ update ≤ x`          (no overshoot ↑)        | ✅ Proved |
  | `alphaUpdate_le_state`         | `x ≤ s, 0 ≤ a → update ≤ s`       (upper bound, ↓ case)   | ✅ Proved |
  | `alphaUpdate_ge_sample`        | `x ≤ s, 0 ≤ a ≤ 1 → x ≤ update`  (lower bound, ↓ case)   | 🔄 1 sorry (mul by nonpositive) |
  | `alphaUpdate_no_overshoot_down`| `x ≤ s → x ≤ update ≤ s`          (no overshoot ↓)        | 🔄 sorry (via ge_sample) |
  | `alphaUpdate_mono_sample`      | `s1 ≤ s2 → update(s1) ≤ update(s2)` (monotone in sample)  | ✅ Proved |
  | `alphaUpdate_mono_state`       | `s1 ≤ s2 → update_s1 ≤ update_s2` (monotone in state)     | 🔄 sorry (ring step) |
  | `alphaIterate_formula`         | `state_n = target + (s-target)*(1-a)^n`                    | 🔄 sorry (ring step) |
-/

end PX4.AlphaFilter
