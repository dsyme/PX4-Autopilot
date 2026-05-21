/-!
# WelfordMeanVector (2D) — Formal Verification

🔬 *Lean Squad automated formal verification.*

This file models and proves correctness properties of `WelfordMeanVector<Type, 2>`,
the 2-component vector extension of PX4's Welford online mean algorithm.

- **C++ source**: `src/lib/mathlib/math/WelfordMeanVector.hpp`
- **Related file**: `formal-verification/lean/FVSquad/WelfordMean.lean`

## C++ Reference (key logic, N=2 specialisation)

```cpp
bool update(const matrix::Vector<Type, N> &new_value) {
    if (_count == 0) { reset(); _count = 1; _mean = new_value; return false; }
    else { _count++; }
    const matrix::Vector<Type, N> delta{new_value - _mean};
    // Kahan-compensated mean update (abstracted as exact division):
    _mean = _mean + delta / _count;
    // M2 upper triangle (abstracted without Kahan):
    //   M2(i,j) += delta(i) * (new_value(j) - _mean(j))
    return valid();  // valid() iff count > 2
}
```

## Model

We specialise to **N = 2** with **exact rational arithmetic**.
The 2D state carries one shared `count` and two independent Welford mean/M2
accumulators — one per component. Kahan compensator fields and the UINT16_MAX
overflow case are abstracted away.

**Key invariants modelled**:
1. After `n` updates with inputs `x₀, …, xₙ₋₁`, the mean vector satisfies
   `mean.0 * count = Σ x_i.0`  and  `mean.1 * count = Σ x_i.1`.
2. The M2 diagonal entries satisfy `M2_diag.0 ≥ 0` and `M2_diag.1 ≥ 0`.

The M2 off-diagonal entry `M2(0,1) = Σ(x_i.0 - mean.0)(x_i.1 - mean.1)` is
more complex; we state it but prove only the simpler diagonal non-negativity here.

## Properties Proved (11 theorems, 0 sorry)

| # | Theorem | Statement |
|---|---------|-----------|
| 1 | `wv2_update_count` | Count increments by 1 |
| 2 | `wv2_update_mean0_step` | Component-0 mean recurrence |
| 3 | `wv2_update_mean1_step` | Component-1 mean recurrence |
| 4 | `wv2_reset_zero` | Reset gives zero state |
| 5 | `wv2_fold_count` | Count after folding = list length |
| 6 | `wv2_fold_mean0_times_count` | `mean.0 * count = Σ x_i.0` |
| 7 | `wv2_fold_mean1_times_count` | `mean.1 * count = Σ x_i.1` |
| 8 | `wv2_fold_mean0` | mean.0 = sum₀/length for non-empty list |
| 9 | `wv2_fold_mean1` | mean.1 = sum₁/length for non-empty list |
| 10 | `wv2_update_M2_diag0_nonneg` | M2 diagonal(0) stays ≥ 0 |
| 11 | `wv2_update_M2_diag1_nonneg` | M2 diagonal(1) stays ≥ 0 |
-/

namespace PX4.WelfordMeanVector2D

/-! ## State and definitions -/

/-- State of the 2D Welford accumulator.

Models `WelfordMeanVector<Type, 2>` with:
- `count`: shared sample count (both components see the same samples)
- `mean0`, `mean1`: running mean for each component
- `M2_diag0`, `M2_diag1`: diagonal entries of the M2 covariance accumulator
  (the off-diagonal entry M2(0,1) is omitted for simplicity) -/
structure WV2State where
  count     : Nat
  mean0     : Rat
  mean1     : Rat
  M2_diag0  : Rat
  M2_diag1  : Rat
  deriving Repr

/-- Initial (reset) state: all fields zero. -/
def initWV2 : WV2State := { count := 0, mean0 := 0, mean1 := 0, M2_diag0 := 0, M2_diag1 := 0 }

/-- Pure functional update for one new 2D sample `(x0, x1)`.

Models the C++ `update()` for the non-overflow, non-zero-count branch,
ignoring Kahan compensators. -/
def wv2Update (s : WV2State) (x0 x1 : Rat) : WV2State :=
  let n    := s.count + 1
  let nR   := (n : Rat)
  let δ0   := x0 - s.mean0
  let δ1   := x1 - s.mean1
  let m0   := s.mean0 + δ0 / nR
  let m1   := s.mean1 + δ1 / nR
  { count    := n
    mean0    := m0
    mean1    := m1
    M2_diag0 := s.M2_diag0 + δ0 * (x0 - m0)
    M2_diag1 := s.M2_diag1 + δ1 * (x1 - m1) }

/-- Reset to zero state (models C++ `reset()`). -/
def wv2Reset : WV2State := initWV2

/-- Fold a list of 2D samples, starting from an initial state. -/
def wv2FoldFrom (s₀ : WV2State) (xs : List (Rat × Rat)) : WV2State :=
  xs.foldl (fun s p => wv2Update s p.1 p.2) s₀

/-- Fold from the zero initial state. -/
def wv2Fold (xs : List (Rat × Rat)) : WV2State :=
  wv2FoldFrom initWV2 xs

/-! ## Helper lemmas -/

private theorem succ_cast_ne_zero (n : Nat) : (↑(n + 1) : Rat) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)

private theorem succ_cast_pos (n : Nat) : (0 : Rat) < ↑(n + 1) :=
  Nat.cast_pos.mpr (Nat.succ_pos n)

private theorem succ_cast_one_le (n : Nat) : (1 : Rat) ≤ ↑(n + 1) := by
  exact_mod_cast Nat.le_add_left 1 n

private theorem rat_sq_nonneg (δ : Rat) : 0 ≤ δ * δ := by
  by_cases h : 0 ≤ δ
  · exact Rat.mul_nonneg h h
  · have hlt : δ < 0 := Rat.not_le.mp h
    have hneg0 : (0 : Rat) ≤ -δ := by
      have := Rat.neg_le_neg (Rat.le_of_lt hlt)
      simp [Rat.neg_zero] at this; exact this
    rw [← show (-δ) * (-δ) = δ * δ from by rw [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]]
    exact Rat.mul_nonneg hneg0 hneg0

private theorem inv_le_one_of_one_le (nR : Rat) (h1 : 1 ≤ nR) (hpos : 0 < nR) : nR⁻¹ ≤ 1 := by
  have hne : nR ≠ 0 := fun h0 => by simp [h0] at hpos
  have h2 : (1 : Rat) * nR⁻¹ ≤ nR * nR⁻¹ :=
    Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt (Rat.inv_pos.mpr hpos))
  rw [Rat.mul_inv_cancel _ hne, Rat.one_mul] at h2; exact h2

/-! ## Per-update theorems -/

/-- Count increments by 1 on each update. -/
theorem wv2_update_count (s : WV2State) (x0 x1 : Rat) :
    (wv2Update s x0 x1).count = s.count + 1 := rfl

/-- Component-0 mean recurrence:
    `mean0_new * n = mean0_old * (n-1) + x0` where `n = count + 1`. -/
theorem wv2_update_mean0_step (s : WV2State) (x0 x1 : Rat) :
    (wv2Update s x0 x1).mean0 * ↑(s.count + 1) = s.mean0 * ↑s.count + x0 := by
  simp only [wv2Update]
  set n := s.count + 1
  set nR := (n : Rat)
  have hne : nR ≠ 0 := succ_cast_ne_zero s.count
  -- mean0_new = mean0 + (x0 - mean0) / nR
  -- mean0_new * nR = mean0 * nR + (x0 - mean0) = mean0 * (nR - 1) + x0
  have : (s.mean0 + (x0 - s.mean0) / nR) * nR = s.mean0 * ↑s.count + x0 := by
    rw [Rat.add_mul, Rat.div_mul_cancel₀ _ hne]
    have hn : (↑(s.count + 1) : Rat) = ↑s.count + 1 := by push_cast; ring
    rw [hn]; ring
  exact this

/-- Component-1 mean recurrence (symmetric to component-0). -/
theorem wv2_update_mean1_step (s : WV2State) (x0 x1 : Rat) :
    (wv2Update s x0 x1).mean1 * ↑(s.count + 1) = s.mean1 * ↑s.count + x1 := by
  simp only [wv2Update]
  set n := s.count + 1
  set nR := (n : Rat)
  have hne : nR ≠ 0 := succ_cast_ne_zero s.count
  have : (s.mean1 + (x1 - s.mean1) / nR) * nR = s.mean1 * ↑s.count + x1 := by
    rw [Rat.add_mul, Rat.div_mul_cancel₀ _ hne]
    have hn : (↑(s.count + 1) : Rat) = ↑s.count + 1 := by push_cast; ring
    rw [hn]; ring
  exact this

/-- Reset gives the zero state. -/
theorem wv2_reset_zero : wv2Reset = initWV2 := rfl

/-! ## Fold theorems -/

/-- Count after folding a list from an initial state: initial count + list length. -/
theorem wv2_foldFrom_count (s₀ : WV2State) (xs : List (Rat × Rat)) :
    (wv2FoldFrom s₀ xs).count = s₀.count + xs.length := by
  induction xs generalizing s₀ with
  | nil => simp [wv2FoldFrom]
  | cons h t ih =>
    simp only [wv2FoldFrom, List.foldl, List.length_cons]
    rw [ih, wv2_update_count]
    omega

/-- Count after folding a list from zero = list length. -/
theorem wv2_fold_count (xs : List (Rat × Rat)) :
    (wv2Fold xs).count = xs.length := by
  simp [wv2Fold, wv2_foldFrom_count]

/-- Component-0 mean invariant under fold from initial state:
    `mean0 * count = initial_mean0 * initial_count + Σ x_i.0` -/
theorem wv2_foldFrom_mean0_inv (s₀ : WV2State) (xs : List (Rat × Rat)) :
    (wv2FoldFrom s₀ xs).mean0 * ↑(wv2FoldFrom s₀ xs).count =
    s₀.mean0 * ↑s₀.count + (xs.map Prod.fst).sum := by
  induction xs generalizing s₀ with
  | nil => simp [wv2FoldFrom]
  | cons p t ih =>
    simp only [wv2FoldFrom, List.foldl, List.map, List.sum_cons]
    rw [ih]
    have := wv2_update_mean0_step s₀ p.1 p.2
    have hcount := wv2_update_count s₀ p.1 p.2
    rw [hcount] at *
    linarith [this]

/-- Component-1 mean invariant under fold from initial state. -/
theorem wv2_foldFrom_mean1_inv (s₀ : WV2State) (xs : List (Rat × Rat)) :
    (wv2FoldFrom s₀ xs).mean1 * ↑(wv2FoldFrom s₀ xs).count =
    s₀.mean1 * ↑s₀.count + (xs.map Prod.snd).sum := by
  induction xs generalizing s₀ with
  | nil => simp [wv2FoldFrom]
  | cons p t ih =>
    simp only [wv2FoldFrom, List.foldl, List.map, List.sum_cons]
    rw [ih]
    have := wv2_update_mean1_step s₀ p.1 p.2
    have hcount := wv2_update_count s₀ p.1 p.2
    rw [hcount] at *
    linarith [this]

/-- `mean0 * count = Σ x_i.0` (from zero initial state). -/
theorem wv2_fold_mean0_times_count (xs : List (Rat × Rat)) :
    (wv2Fold xs).mean0 * ↑(wv2Fold xs).count = (xs.map Prod.fst).sum := by
  simp [wv2Fold, wv2_foldFrom_mean0_inv]

/-- `mean1 * count = Σ x_i.1` (from zero initial state). -/
theorem wv2_fold_mean1_times_count (xs : List (Rat × Rat)) :
    (wv2Fold xs).mean1 * ↑(wv2Fold xs).count = (xs.map Prod.snd).sum := by
  simp [wv2Fold, wv2_foldFrom_mean1_inv]

/-- For non-empty lists: `mean0 = sum₀ / length`. -/
theorem wv2_fold_mean0 (xs : List (Rat × Rat)) (hne : xs ≠ []) :
    (wv2Fold xs).mean0 = (xs.map Prod.fst).sum / ↑xs.length := by
  have hlen : xs.length ≠ 0 := List.length_ne_zero.mpr hne
  have hlenR : (↑xs.length : Rat) ≠ 0 := Nat.cast_ne_zero.mpr hlen
  have h := wv2_fold_mean0_times_count xs
  rw [wv2_fold_count] at h
  rw [← h, Rat.div_def, Rat.mul_assoc, Rat.mul_inv_cancel _ hlenR, Rat.mul_one]

/-- For non-empty lists: `mean1 = sum₁ / length`. -/
theorem wv2_fold_mean1 (xs : List (Rat × Rat)) (hne : xs ≠ []) :
    (wv2Fold xs).mean1 = (xs.map Prod.snd).sum / ↑xs.length := by
  have hlen : xs.length ≠ 0 := List.length_ne_zero.mpr hne
  have hlenR : (↑xs.length : Rat) ≠ 0 := Nat.cast_ne_zero.mpr hlen
  have h := wv2_fold_mean1_times_count xs
  rw [wv2_fold_count] at h
  rw [← h, Rat.div_def, Rat.mul_assoc, Rat.mul_inv_cancel _ hlenR, Rat.mul_one]

/-! ## M2 diagonal non-negativity -/

/-- M2 diagonal(0) stays ≥ 0 across each update.
    Proof: increment = δ0 * (x0 - mean0_new) = δ0² * (1 - nR⁻¹) ≥ 0. -/
theorem wv2_update_M2_diag0_nonneg (s : WV2State) (x0 x1 : Rat) (h : 0 ≤ s.M2_diag0) :
    0 ≤ (wv2Update s x0 x1).M2_diag0 := by
  simp only [wv2Update]
  apply Rat.add_nonneg h
  have hne  : (↑(s.count + 1) : Rat) ≠ 0 := succ_cast_ne_zero s.count
  have hpos : (0 : Rat) < ↑(s.count + 1) := succ_cast_pos s.count
  have h1nR : (1 : Rat) ≤ ↑(s.count + 1) := succ_cast_one_le s.count
  have hx_sub : x0 - (s.mean0 + (x0 - s.mean0) / ↑(s.count + 1)) =
                (x0 - s.mean0) - (x0 - s.mean0) / ↑(s.count + 1) := by
    simp [Rat.sub_eq_add_neg, Rat.neg_add, Rat.add_assoc]
  rw [hx_sub]
  have hfactor : (x0 - s.mean0) - (x0 - s.mean0) / ↑(s.count + 1) =
                 (x0 - s.mean0) * (1 - (↑(s.count + 1))⁻¹) := by
    rw [Rat.div_def]
    simp [Rat.sub_eq_add_neg, Rat.mul_add, Rat.mul_neg, Rat.mul_one]
  rw [hfactor, ← Rat.mul_assoc]
  apply Rat.mul_nonneg (rat_sq_nonneg _)
  exact (Rat.le_iff_sub_nonneg (↑(s.count + 1))⁻¹ 1).mp
        (inv_le_one_of_one_le _ h1nR hpos)

/-- M2 diagonal(1) stays ≥ 0 across each update (symmetric proof). -/
theorem wv2_update_M2_diag1_nonneg (s : WV2State) (x0 x1 : Rat) (h : 0 ≤ s.M2_diag1) :
    0 ≤ (wv2Update s x0 x1).M2_diag1 := by
  simp only [wv2Update]
  apply Rat.add_nonneg h
  have hne  : (↑(s.count + 1) : Rat) ≠ 0 := succ_cast_ne_zero s.count
  have hpos : (0 : Rat) < ↑(s.count + 1) := succ_cast_pos s.count
  have h1nR : (1 : Rat) ≤ ↑(s.count + 1) := succ_cast_one_le s.count
  have hx_sub : x1 - (s.mean1 + (x1 - s.mean1) / ↑(s.count + 1)) =
                (x1 - s.mean1) - (x1 - s.mean1) / ↑(s.count + 1) := by
    simp [Rat.sub_eq_add_neg, Rat.neg_add, Rat.add_assoc]
  rw [hx_sub]
  have hfactor : (x1 - s.mean1) - (x1 - s.mean1) / ↑(s.count + 1) =
                 (x1 - s.mean1) * (1 - (↑(s.count + 1))⁻¹) := by
    rw [Rat.div_def]
    simp [Rat.sub_eq_add_neg, Rat.mul_add, Rat.mul_neg, Rat.mul_one]
  rw [hfactor, ← Rat.mul_assoc]
  apply Rat.mul_nonneg (rat_sq_nonneg _)
  exact (Rat.le_iff_sub_nonneg (↑(s.count + 1))⁻¹ 1).mp
        (inv_le_one_of_one_le _ h1nR hpos)

/-! ## Concrete examples -/

/-- Single update from zero: mean = x, count = 1. -/
example : (wv2Fold [(3/5 : Rat, 7/2)]).mean0 = 3/5 ∧
          (wv2Fold [(3/5 : Rat, 7/2)]).mean1 = 7/2 ∧
          (wv2Fold [(3/5 : Rat, 7/2)]).count = 1 := by
  native_decide

/-- Two updates: mean is the componentwise average. -/
example : (wv2Fold [(1 : Rat, 2), (3, 4)]).mean0 = 2 ∧
          (wv2Fold [(1 : Rat, 2), (3, 4)]).mean1 = 3 ∧
          (wv2Fold [(1 : Rat, 2), (3, 4)]).count = 2 := by
  native_decide

end PX4.WelfordMeanVector2D
