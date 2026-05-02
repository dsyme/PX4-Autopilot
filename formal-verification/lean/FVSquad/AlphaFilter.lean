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
    (h_le : state ≤ sample) (_ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1) :
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
    (h_le : sample ≤ state) (_ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1) :
    sample ≤ alphaUpdate state alpha sample := by
  simp only [alphaUpdate]
  -- Need: sample ≤ state + alpha*(sample - state)
  -- ⟺ sample - state ≤ alpha*(sample - state)   [since sample - state ≤ 0 and alpha ≤ 1]
  -- ⟺ 1*(sample - state) ≤ alpha*(sample - state)
  -- which follows since (sample - state) ≤ 0 and alpha ≤ 1 (flip inequality for negatives)
  have hd : 0 ≤ state - sample := (Rat.le_iff_sub_nonneg sample state).mp h_le
  have hd : 0 ≤ state - sample := (Rat.le_iff_sub_nonneg sample state).mp h_le
  have key1 : alpha * (state - sample) ≤ 1 * (state - sample) :=
    Rat.mul_le_mul_of_nonneg_right ha1 hd
  rw [Rat.one_mul] at key1
  -- key1 : alpha * (state - sample) ≤ state - sample
  -- Apply Rat.neg_le_neg to flip, then rewrite negations
  have key2 : -(state - sample) ≤ -(alpha * (state - sample)) := Rat.neg_le_neg key1
  rw [Rat.neg_sub] at key2
  rw [show -(alpha * (state - sample)) = alpha * (sample - state) from by
      rw [← Rat.mul_neg, Rat.neg_sub]] at key2
  -- key2 : sample - state ≤ alpha * (sample - state)
  calc sample = sample - state + state := by rw [Rat.sub_add_cancel]
    _ ≤ alpha * (sample - state) + state := (Rat.add_le_add_right (c := state)).mpr key2
    _ = state + alpha * (sample - state) := Rat.add_comm _ _

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
    (ha1 : alpha ≤ 1) (_ha0 : 0 ≤ alpha) (s1 s2 : Rat) (hs : s1 ≤ s2) :
    alphaUpdate s1 alpha sample ≤ alphaUpdate s2 alpha sample := by
  simp only [alphaUpdate]
  -- s1 + alpha*(sample - s1) ≤ s2 + alpha*(sample - s2)
  -- ⟺ s1*(1 - alpha) ≤ s2*(1 - alpha)  (cancel alpha*sample, use distributivity)
  -- We show difference is nonneg: (s2 - s1)*(1 - alpha) ≥ 0
  have h1a : 0 ≤ 1 - alpha := (Rat.le_iff_sub_nonneg alpha 1).mp ha1
  -- Expand both sides using sub_eq_add_neg + mul_add + mul_neg
  -- sample - s1 = (sample - s2) + (s2 - s1), so alpha*(sample-s1) = alpha*(sample-s2) + alpha*(s2-s1)
  have split : sample - s1 = (sample - s2) + (s2 - s1) := by
    rw [Rat.sub_eq_add_neg sample s1, Rat.sub_eq_add_neg sample s2,
        Rat.sub_eq_add_neg s2 s1, Rat.add_assoc,
        ← Rat.add_assoc (-s2) s2, Rat.neg_add_cancel, Rat.zero_add]
  have expand : alpha * (sample - s1) = alpha * (sample - s2) + alpha * (s2 - s1) := by
    rw [split, Rat.mul_add]
  rw [expand]
  -- Rearrange: s1 + (alpha*(sample-s2) + alpha*(s2-s1)) = alpha*(sample-s2) + (s1 + alpha*(s2-s1))
  rw [show s1 + (alpha * (sample - s2) + alpha * (s2 - s1)) =
         alpha * (sample - s2) + (s1 + alpha * (s2 - s1)) from by
    rw [← Rat.add_assoc, Rat.add_comm s1, Rat.add_assoc]]
  rw [show s2 + alpha * (sample - s2) = alpha * (sample - s2) + s2 from Rat.add_comm _ _]
  apply (Rat.add_le_add_left (c := alpha * (sample - s2))).mpr
  -- Goal: s1 + alpha * (s2 - s1) ≤ s2
  have hsd : 0 ≤ s2 - s1 := (Rat.le_iff_sub_nonneg s1 s2).mp hs
  have key : alpha * (s2 - s1) ≤ 1 * (s2 - s1) := Rat.mul_le_mul_of_nonneg_right ha1 hsd
  rw [Rat.one_mul] at key
  calc s1 + alpha * (s2 - s1)
      = alpha * (s2 - s1) + s1 := Rat.add_comm _ _
    _ ≤ (s2 - s1) + s1 := (Rat.add_le_add_right (c := s1)).mpr key
    _ = s2 := Rat.sub_add_cancel

/-! ## Iterated update -/

/-- Helper: one alpha update minus the target equals the gap scaled by (1-alpha). -/
private theorem alphaUpdate_sub_target (state alpha target : Rat) :
    alphaUpdate state alpha target - target = (state - target) * (1 - alpha) := by
  simp only [alphaUpdate, Rat.sub_eq_add_neg, Rat.mul_add, Rat.mul_one, Rat.mul_neg,
             Rat.neg_mul, Rat.add_mul, Rat.add_assoc]
  congr 1
  rw [Rat.neg_add, Rat.neg_neg, Rat.mul_comm alpha target, Rat.mul_comm alpha state]
  rw [Rat.add_left_comm (target * alpha) (-(state * alpha)) (-target)]
  rw [Rat.add_comm (target * alpha) (-target)]
  rw [← Rat.add_assoc, Rat.add_comm (-(state * alpha)) (-target), Rat.add_assoc]

/-- Iterated update: `n` steps with constant input `target`. -/
def alphaIterate (state alpha target : Rat) : Nat → Rat
  | 0     => state
  | n + 1 => alphaIterate (alphaUpdate state alpha target) alpha target n

-- Spot checks for iterated update
#eval alphaIterate 0 (1/10) 1 9   -- ≈ 0.613 (should be near 1 - (9/10)^9 ≈ 0.613)
#eval alphaIterate 0 (1/10) 1 90  -- should be near 1 - (9/10)^90 ≈ 0.9999

/-- After `n` steps with constant input `target`:
    `state_n = target + (state₀ - target) * (1 - alpha)^n`.

    This is the standard exponential filter closed-form formula, proved by strong induction
    (generalizing over `state` so the IH applies to the updated state in each step). -/
theorem alphaIterate_formula (state alpha target : Rat) (n : Nat) :
    alphaIterate state alpha target n =
    target + (state - target) * (1 - alpha) ^ n := by
  induction n generalizing state with
  | zero =>
    simp only [alphaIterate]
    have h0 : (1 - alpha) ^ (0 : Nat) = 1 := by simp
    rw [h0, Rat.mul_one, Rat.add_comm, Rat.sub_add_cancel]
  | succ n ih =>
    simp only [alphaIterate]
    rw [ih (alphaUpdate state alpha target)]
    -- alphaUpdate state alpha target - target = (state - target) * (1 - alpha)
    rw [alphaUpdate_sub_target state alpha target]
    -- (state - target) * (1 - alpha) * (1 - alpha)^n = (state - target) * (1 - alpha)^(n+1)
    congr 1
    rw [Rat.pow_succ, Rat.mul_assoc, Rat.mul_comm ((1 - alpha) ^ n) (1 - alpha)]

/-! ## Multi-step no-overshoot and monotone convergence -/

/-- Error formula: the deviation from target after `n` steps equals the initial
    deviation scaled by `(1-alpha)^n`.

    Corollary of `alphaIterate_formula`. -/
theorem alphaIterate_error_formula (state alpha target : Rat) (n : Nat) :
    alphaIterate state alpha target n - target = (state - target) * (1 - alpha) ^ n := by
  induction n generalizing state with
  | zero =>
    simp only [alphaIterate]
    rw [Rat.pow_zero, Rat.mul_one]
  | succ n ih =>
    simp only [alphaIterate]
    rw [ih (alphaUpdate state alpha target), alphaUpdate_sub_target, Rat.mul_assoc]
    congr 1
    rw [Rat.pow_succ, Rat.mul_comm ((1 - alpha) ^ n) (1 - alpha)]

/-- **Multi-step no-overshoot (upward, state starts above target)**:
    if `target ≤ state` and `0 ≤ alpha ≤ 1`,
    then after any number of steps the filter value stays in `[target, state]`.

    The filter moves *downward* toward `target`. Uses
    `alphaUpdate_no_overshoot_down` (applies when `sample ≤ state`). -/
theorem alphaIterate_no_overshoot_up (state alpha target : Rat) (n : Nat)
    (hst : target ≤ state) (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1) :
    target ≤ alphaIterate state alpha target n ∧
    alphaIterate state alpha target n ≤ state := by
  induction n generalizing state with
  | zero =>
    simp only [alphaIterate]
    exact ⟨hst, Rat.le_refl⟩
  | succ n ih =>
    simp only [alphaIterate]
    obtain ⟨h_lo, h_hi⟩ := alphaUpdate_no_overshoot_down state alpha target hst ha0 ha1
    obtain ⟨ih_lo, ih_hi⟩ := ih (alphaUpdate state alpha target) h_lo
    exact ⟨ih_lo, Rat.le_trans ih_hi h_hi⟩

/-- **Multi-step no-overshoot (downward, state starts below target)**:
    if `state ≤ target` and `0 ≤ alpha ≤ 1`,
    then after any number of steps the filter value stays in `[state, target]`.

    The filter moves *upward* toward `target`. Uses
    `alphaUpdate_no_overshoot_up` (applies when `state ≤ sample`). -/
theorem alphaIterate_no_overshoot_down (state alpha target : Rat) (n : Nat)
    (hst : state ≤ target) (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1) :
    state ≤ alphaIterate state alpha target n ∧
    alphaIterate state alpha target n ≤ target := by
  induction n generalizing state with
  | zero =>
    simp only [alphaIterate]
    exact ⟨Rat.le_refl, hst⟩
  | succ n ih =>
    simp only [alphaIterate]
    obtain ⟨h_lo, h_hi⟩ := alphaUpdate_no_overshoot_up state alpha target hst ha0 ha1
    obtain ⟨ih_lo, ih_hi⟩ := ih (alphaUpdate state alpha target) h_hi
    exact ⟨Rat.le_trans h_lo ih_lo, ih_hi⟩

/-- **Monotone convergence (from above)**: if `target ≤ state` and `0 ≤ alpha ≤ 1`,
    each additional iteration brings the filter no farther from `target`.

    Formally: `alphaIterate (n+1) ≤ alphaIterate n` — the sequence is non-increasing. -/
theorem alphaIterate_mono_n_up (state alpha target : Rat) (n : Nat)
    (hst : target ≤ state) (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1) :
    alphaIterate state alpha target (n + 1) ≤ alphaIterate state alpha target n := by
  induction n generalizing state with
  | zero =>
    simp only [alphaIterate]
    exact (alphaUpdate_no_overshoot_down state alpha target hst ha0 ha1).2
  | succ n ih =>
    simp only [alphaIterate]
    have h_lo := (alphaUpdate_no_overshoot_down state alpha target hst ha0 ha1).1
    exact ih (alphaUpdate state alpha target) h_lo

/-- **Monotone convergence (from below)**: if `state ≤ target` and `0 ≤ alpha ≤ 1`,
    each additional iteration brings the filter no farther from `target`.

    Formally: `alphaIterate n ≤ alphaIterate (n+1)` — the sequence is non-decreasing. -/
theorem alphaIterate_mono_n_down (state alpha target : Rat) (n : Nat)
    (hst : state ≤ target) (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1) :
    alphaIterate state alpha target n ≤ alphaIterate state alpha target (n + 1) := by
  induction n generalizing state with
  | zero =>
    simp only [alphaIterate]
    exact (alphaUpdate_no_overshoot_up state alpha target hst ha0 ha1).1
  | succ n ih =>
    simp only [alphaIterate]
    have h_hi := (alphaUpdate_no_overshoot_up state alpha target hst ha0 ha1).2
    exact ih (alphaUpdate state alpha target) h_hi

/-! ## Summary of proved properties

  | Theorem                          | Statement                                                          | Status    |
  |----------------------------------|--------------------------------------------------------------------|-----------|
  | `alphaUpdate_fixed`              | `update s a s = s` (sample = state → no change)                   | ✅ Proved |
  | `alphaUpdate_alpha_zero`         | `update s 0 x = s` (alpha=0: frozen)                              | ✅ Proved |
  | `alphaUpdate_alpha_one`          | `update s 1 x = x` (alpha=1: immediate)                           | ✅ Proved |
  | `alphaUpdate_le_sample`          | `s ≤ x, 0 ≤ a ≤ 1 → update ≤ x`  (upper bound, ↑ case)           | ✅ Proved |
  | `alphaUpdate_ge_state`           | `s ≤ x, 0 ≤ a → s ≤ update`       (lower bound, ↑ case)           | ✅ Proved |
  | `alphaUpdate_no_overshoot_up`    | `s ≤ x → s ≤ update ≤ x`          (no overshoot ↑, 1 step)        | ✅ Proved |
  | `alphaUpdate_le_state`           | `x ≤ s, 0 ≤ a → update ≤ s`       (upper bound, ↓ case)           | ✅ Proved |
  | `alphaUpdate_ge_sample`          | `x ≤ s, 0 ≤ a ≤ 1 → x ≤ update`  (lower bound, ↓ case)           | ✅ Proved |
  | `alphaUpdate_no_overshoot_down`  | `x ≤ s → x ≤ update ≤ s`          (no overshoot ↓, 1 step)        | ✅ Proved |
  | `alphaUpdate_mono_sample`        | `s1 ≤ s2 → update(s1) ≤ update(s2)` (monotone in sample)          | ✅ Proved |
  | `alphaUpdate_mono_state`         | `s1 ≤ s2 → update_s1 ≤ update_s2` (monotone in state)             | ✅ Proved |
  | `alphaIterate_formula`           | `state_n = target + (s-target)*(1-a)^n`                            | ✅ Proved |
  | `alphaIterate_error_formula`     | `state_n - target = (s-target)*(1-a)^n`                            | ✅ Proved |
  | `alphaIterate_no_overshoot_up`   | `target ≤ s, 0 ≤ a ≤ 1 → ∀n, target ≤ state_n ≤ s` (n-step ↑)    | ✅ Proved |
  | `alphaIterate_no_overshoot_down` | `s ≤ target, 0 ≤ a ≤ 1 → ∀n, s ≤ state_n ≤ target` (n-step ↓)    | ✅ Proved |
  | `alphaIterate_mono_n_up`         | `target ≤ s → state_{n+1} ≤ state_n` (monotone toward target ↑)   | ✅ Proved |
  | `alphaIterate_mono_n_down`       | `s ≤ target → state_n ≤ state_{n+1}` (monotone toward target ↓)   | ✅ Proved |
-/

end PX4.AlphaFilter
