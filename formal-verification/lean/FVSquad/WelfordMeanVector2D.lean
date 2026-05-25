/-!
# WelfordMeanVector2D — Formal Verification

🔬 *Lean Squad automated formal verification.*

This file models and proves correctness properties of `WelfordMeanVector<T, 2>::update`
from PX4-Autopilot's `mathlib`, specialised to the 2D case (N = 2).

- **C++ source**: `src/lib/mathlib/math/WelfordMeanVector.hpp`
- **Related scalar file**: `formal-verification/lean/FVSquad/WelfordMean.lean`

## C++ Reference (2D case)

```cpp
// update(new_value) with new_value = Vector<Type, 2>
_count++;
const Vector<Type,2> delta = new_value - _mean;
_mean = _mean + delta / _count;          // component-wise
// M2 update (upper triangle, then symmetrised):
M2[0,0] += delta[0] * (new_value[0] - _mean[0])
M2[1,1] += delta[1] * (new_value[1] - _mean[1])
M2[0,1] += delta[0] * (new_value[1] - _mean[1])
M2[1,0]  = M2[0,1]   // symmetry
```

## Model

- Arithmetic over `Rat` (exact rationals).
- The 2D mean is a pair `Rat × Rat`.
- The 2×2 symmetric M2 matrix is represented by three rationals `(m00, m11, m01)`.
- Kahan accumulator fields are omitted (numerical-precision detail only).
- Count-overflow (`UINT16_MAX`) and finiteness guards are omitted.
- The `max(M2(r,r), 0)` diagonal clamp is omitted — we prove the diagonal is ≥ 0 by algebra.

## Proved Properties

| Theorem | Statement | Status |
|---------|-----------|--------|
| `welfordVec2_count` | Count increments by 1 | ✅ Proved |
| `welfordVec2_mean_x_step` | x-mean recurrence: `mean_x * n = old_mean_x * (n-1) + x` | ✅ Proved |
| `welfordVec2_mean_y_step` | y-mean recurrence: `mean_y * n = old_mean_y * (n-1) + y` | ✅ Proved |
| `welfordVec2_m00_nonneg` | M2[0,0] ≥ 0 preserved | ✅ Proved |
| `welfordVec2_m11_nonneg` | M2[1,1] ≥ 0 preserved | ✅ Proved |
| `welfordVec2FoldFrom_count` | Count after fold = init_count + length | ✅ Proved |
| `welfordVec2FoldFrom_mean_x_inv` | mean_x * count = init_mean_x * init_count + Σxᵢ | ✅ Proved |
| `welfordVec2FoldFrom_mean_y_inv` | mean_y * count = init_mean_y * init_count + Σyᵢ | ✅ Proved |
| `welfordVec2Fold_count` | fold count = list length | ✅ Proved |
| `welfordVec2Fold_mean_x` | Non-empty list: mean_x = Σxᵢ / length | ✅ Proved |
| `welfordVec2Fold_mean_y` | Non-empty list: mean_y = Σyᵢ / length | ✅ Proved |
| `welfordVec2FoldFrom_m00_nonneg` | M2[0,0] ≥ 0 preserved across any fold | ✅ Proved |
| `welfordVec2FoldFrom_m11_nonneg` | M2[1,1] ≥ 0 preserved across any fold | ✅ Proved |
| `welfordVec2Fold_m00_nonneg` | M2[0,0] ≥ 0 after full fold from init | ✅ Proved |
| `welfordVec2Fold_m11_nonneg` | M2[1,1] ≥ 0 after full fold from init | ✅ Proved |
-/

namespace PX4.WelfordMeanVector2D

/-! ## State and update -/

/-- State of the 2D Welford accumulator.
    `m00` is M2[0,0] (variance accumulator for x-component),
    `m11` is M2[1,1] (variance accumulator for y-component),
    `m01` is the off-diagonal M2[0,1] = M2[1,0] (covariance accumulator). -/
structure WelfordVec2State where
  count : Nat
  mx    : Rat   -- running mean of x-component
  my    : Rat   -- running mean of y-component
  m00   : Rat   -- M2[0,0]
  m11   : Rat   -- M2[1,1]
  m01   : Rat   -- M2[0,1]
  deriving Repr

/-- Initial state (all-zero, matches C++ default constructor). -/
def initState2 : WelfordVec2State :=
  { count := 0, mx := 0, my := 0, m00 := 0, m11 := 0, m01 := 0 }

/-- Single-step Welford update for a 2D observation `(x, y)`.

    Models the non-Kahan core of `WelfordMeanVector<T,2>::update`, assuming
    `s.count > 0` (the `_count = 0` first-sample branch is handled by starting
    from `initState2` and immediately calling `update`). -/
def welfordVec2Update (s : WelfordVec2State) (x y : Rat) : WelfordVec2State :=
  let n     := s.count + 1
  let nR    : Rat := n
  let δx    := x - s.mx
  let δy    := y - s.my
  let mx'   := s.mx + δx / nR
  let my'   := s.my + δy / nR
  { count := n
  , mx    := mx'
  , my    := my'
  , m00   := s.m00 + δx * (x - mx')
  , m11   := s.m11 + δy * (y - my')
  , m01   := s.m01 + δx * (y - my')
  }

/-- Fold over a list of 2D observations starting from a given initial state. -/
def welfordVec2FoldFrom (s₀ : WelfordVec2State) : List (Rat × Rat) → WelfordVec2State
  | []          => s₀
  | (x, y) :: t => welfordVec2FoldFrom (welfordVec2Update s₀ x y) t

/-- Fold starting from the all-zero initial state. -/
def welfordVec2Fold (pts : List (Rat × Rat)) : WelfordVec2State :=
  welfordVec2FoldFrom initState2 pts

/-! ## Helper lemmas -/

private theorem succ_cast_ne_zero (n : Nat) : (↑(n + 1) : Rat) ≠ 0 := by
  exact_mod_cast Nat.succ_ne_zero n

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

/-! ## Single-step theorems -/

/-- Count increments by one on each update. -/
theorem welfordVec2_count (s : WelfordVec2State) (x y : Rat) :
    (welfordVec2Update s x y).count = s.count + 1 := by
  simp [welfordVec2Update]

/-- x-mean satisfies the Welford recurrence:
    `mean_x_new * (count + 1) = mean_x_old * count + x`. -/
theorem welfordVec2_mean_x_step (s : WelfordVec2State) (x y : Rat) :
    (welfordVec2Update s x y).mx * ↑(s.count + 1) = s.mx * ↑s.count + x := by
  simp only [welfordVec2Update]
  have hn : (↑(s.count + 1) : Rat) ≠ 0 := succ_cast_ne_zero s.count
  have step1 : (s.mx + (x - s.mx) / ↑(s.count + 1)) * ↑(s.count + 1) =
               s.mx * ↑(s.count + 1) + (x - s.mx) := by
    rw [Rat.add_mul]
    congr 1
    rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ hn, Rat.mul_one]
  rw [step1]
  have h_cast : (↑(s.count + 1) : Rat) = ↑s.count + 1 := by push_cast; rfl
  rw [h_cast, Rat.mul_add, Rat.mul_one, Rat.add_assoc]
  congr 1
  rw [Rat.add_comm s.mx _, Rat.sub_add_cancel]

/-- y-mean satisfies the Welford recurrence:
    `mean_y_new * (count + 1) = mean_y_old * count + y`. -/
theorem welfordVec2_mean_y_step (s : WelfordVec2State) (x y : Rat) :
    (welfordVec2Update s x y).my * ↑(s.count + 1) = s.my * ↑s.count + y := by
  simp only [welfordVec2Update]
  have hn : (↑(s.count + 1) : Rat) ≠ 0 := succ_cast_ne_zero s.count
  have step1 : (s.my + (y - s.my) / ↑(s.count + 1)) * ↑(s.count + 1) =
               s.my * ↑(s.count + 1) + (y - s.my) := by
    rw [Rat.add_mul]
    congr 1
    rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ hn, Rat.mul_one]
  rw [step1]
  have h_cast : (↑(s.count + 1) : Rat) = ↑s.count + 1 := by push_cast; rfl
  rw [h_cast, Rat.mul_add, Rat.mul_one, Rat.add_assoc]
  congr 1
  rw [Rat.add_comm s.my _, Rat.sub_add_cancel]

/-- M2[0,0] (variance accumulator for x) is non-negative if it was non-negative before. -/
theorem welfordVec2_m00_nonneg (s : WelfordVec2State) (x y : Rat) (h : 0 ≤ s.m00) :
    0 ≤ (welfordVec2Update s x y).m00 := by
  simp only [welfordVec2Update]
  apply Rat.add_nonneg h
  -- Increment: δx * (x - (mx + δx/n))
  -- Simplify: x - (mx + δx/n) = δx - δx/n = δx * (1 - n⁻¹)
  have hne  : (↑(s.count + 1) : Rat) ≠ 0 := succ_cast_ne_zero s.count
  have hpos : (0 : Rat) < ↑(s.count + 1) := by exact_mod_cast Nat.succ_pos s.count
  have h1nR : (1 : Rat) ≤ ↑(s.count + 1) := by exact_mod_cast Nat.le_add_left 1 s.count
  have hx_sub : x - (s.mx + (x - s.mx) / ↑(s.count + 1)) =
                (x - s.mx) - (x - s.mx) / ↑(s.count + 1) := by
    simp [Rat.sub_eq_add_neg, Rat.neg_add, Rat.add_assoc]
  rw [hx_sub]
  have hfactor : (x - s.mx) - (x - s.mx) / ↑(s.count + 1) =
                 (x - s.mx) * (1 - (↑(s.count + 1))⁻¹) := by
    rw [Rat.div_def]
    simp [Rat.sub_eq_add_neg, Rat.mul_add, Rat.mul_neg, Rat.mul_one]
  rw [hfactor, ← Rat.mul_assoc]
  apply Rat.mul_nonneg (rat_sq_nonneg _)
  exact (Rat.le_iff_sub_nonneg _ _).mp (inv_le_one_of_one_le _ h1nR hpos)

/-- M2[1,1] (variance accumulator for y) is non-negative if it was non-negative before. -/
theorem welfordVec2_m11_nonneg (s : WelfordVec2State) (x y : Rat) (h : 0 ≤ s.m11) :
    0 ≤ (welfordVec2Update s x y).m11 := by
  simp only [welfordVec2Update]
  apply Rat.add_nonneg h
  have hne  : (↑(s.count + 1) : Rat) ≠ 0 := succ_cast_ne_zero s.count
  have hpos : (0 : Rat) < ↑(s.count + 1) := by exact_mod_cast Nat.succ_pos s.count
  have h1nR : (1 : Rat) ≤ ↑(s.count + 1) := by exact_mod_cast Nat.le_add_left 1 s.count
  have hy_sub : y - (s.my + (y - s.my) / ↑(s.count + 1)) =
                (y - s.my) - (y - s.my) / ↑(s.count + 1) := by
    simp [Rat.sub_eq_add_neg, Rat.neg_add, Rat.add_assoc]
  rw [hy_sub]
  have hfactor : (y - s.my) - (y - s.my) / ↑(s.count + 1) =
                 (y - s.my) * (1 - (↑(s.count + 1))⁻¹) := by
    rw [Rat.div_def]
    simp [Rat.sub_eq_add_neg, Rat.mul_add, Rat.mul_neg, Rat.mul_one]
  rw [hfactor, ← Rat.mul_assoc]
  apply Rat.mul_nonneg (rat_sq_nonneg _)
  exact (Rat.le_iff_sub_nonneg _ _).mp (inv_le_one_of_one_le _ h1nR hpos)

/-! ## Fold invariants -/

/-- Count after folding = initial count + list length. -/
theorem welfordVec2FoldFrom_count (s₀ : WelfordVec2State) (pts : List (Rat × Rat)) :
    (welfordVec2FoldFrom s₀ pts).count = s₀.count + pts.length := by
  induction pts generalizing s₀ with
  | nil  => simp [welfordVec2FoldFrom]
  | cons p t ih =>
    simp only [welfordVec2FoldFrom, List.length_cons]
    rw [ih, welfordVec2_count]
    omega

/-- `mean_x * count` invariant: equals `init_mean_x * init_count + Σxᵢ`. -/
theorem welfordVec2FoldFrom_mean_x_inv (s₀ : WelfordVec2State) (pts : List (Rat × Rat)) :
    (welfordVec2FoldFrom s₀ pts).mx * ↑(welfordVec2FoldFrom s₀ pts).count =
    s₀.mx * ↑s₀.count + (pts.map Prod.fst).sum := by
  induction pts generalizing s₀ with
  | nil  => simp [welfordVec2FoldFrom, Rat.add_zero]
  | cons p t ih =>
    obtain ⟨x, y⟩ := p
    simp only [welfordVec2FoldFrom, List.map, List.sum_cons]
    rw [ih (welfordVec2Update s₀ x y)]
    -- Goal: (welfordVec2Update s₀ x y).mx * ↑(welfordVec2Update s₀ x y).count + sum_t
    --     = s₀.mx * ↑s₀.count + (x + sum_t)
    have hstep : (welfordVec2Update s₀ x y).mx * ↑(welfordVec2Update s₀ x y).count =
                 s₀.mx * ↑s₀.count + x := by
      rw [welfordVec2_count, welfordVec2_mean_x_step]
    rw [hstep]
    exact Rat.add_assoc _ _ _

/-- `mean_y * count` invariant: equals `init_mean_y * init_count + Σyᵢ`. -/
theorem welfordVec2FoldFrom_mean_y_inv (s₀ : WelfordVec2State) (pts : List (Rat × Rat)) :
    (welfordVec2FoldFrom s₀ pts).my * ↑(welfordVec2FoldFrom s₀ pts).count =
    s₀.my * ↑s₀.count + (pts.map Prod.snd).sum := by
  induction pts generalizing s₀ with
  | nil  => simp [welfordVec2FoldFrom, Rat.add_zero]
  | cons p t ih =>
    obtain ⟨x, y⟩ := p
    simp only [welfordVec2FoldFrom, List.map, List.sum_cons]
    rw [ih (welfordVec2Update s₀ x y)]
    have hstep : (welfordVec2Update s₀ x y).my * ↑(welfordVec2Update s₀ x y).count =
                 s₀.my * ↑s₀.count + y := by
      rw [welfordVec2_count, welfordVec2_mean_y_step]
    rw [hstep]
    exact Rat.add_assoc _ _ _

/-- Fold count from zero = list length. -/
theorem welfordVec2Fold_count (pts : List (Rat × Rat)) :
    (welfordVec2Fold pts).count = pts.length := by
  simp [welfordVec2Fold, welfordVec2FoldFrom_count, initState2]

/-- For a non-empty list, `mean_x = Σxᵢ / length`. -/
theorem welfordVec2Fold_mean_x (pts : List (Rat × Rat)) (hne : pts ≠ []) :
    (welfordVec2Fold pts).mx =
    (pts.map Prod.fst).sum / ↑pts.length := by
  have hlen : pts.length ≠ 0 := by
    cases pts with
    | nil  => exact absurd rfl hne
    | cons => exact Nat.succ_ne_zero _
  have hlenR : (↑pts.length : Rat) ≠ 0 := by exact_mod_cast hlen
  have h := welfordVec2FoldFrom_mean_x_inv initState2 pts
  simp only [initState2, Rat.zero_mul, Rat.zero_add] at h
  rw [welfordVec2FoldFrom_count] at h
  simp only [Nat.zero_add] at h
  -- h : (welfordVec2FoldFrom initState2 pts).mx * ↑pts.length = sum_x
  -- Goal: (welfordVec2Fold pts).mx = sum_x / ↑length
  simp only [welfordVec2Fold, initState2]
  rw [← h, Rat.div_def, Rat.mul_assoc, Rat.mul_inv_cancel _ hlenR, Rat.mul_one]

/-- For a non-empty list, `mean_y = Σyᵢ / length`. -/
theorem welfordVec2Fold_mean_y (pts : List (Rat × Rat)) (hne : pts ≠ []) :
    (welfordVec2Fold pts).my =
    (pts.map Prod.snd).sum / ↑pts.length := by
  have hlen : pts.length ≠ 0 := by
    cases pts with
    | nil  => exact absurd rfl hne
    | cons => exact Nat.succ_ne_zero _
  have hlenR : (↑pts.length : Rat) ≠ 0 := by exact_mod_cast hlen
  have h := welfordVec2FoldFrom_mean_y_inv initState2 pts
  simp only [initState2, Rat.zero_mul, Rat.zero_add] at h
  rw [welfordVec2FoldFrom_count] at h
  simp only [Nat.zero_add] at h
  simp only [welfordVec2Fold, initState2]
  rw [← h, Rat.div_def, Rat.mul_assoc, Rat.mul_inv_cancel _ hlenR, Rat.mul_one]

/-! ## Fold invariants for M2 non-negativity -/

/-- M2[0,0] is non-negative after folding any list, given it was non-negative initially.

    This lifts `welfordVec2_m00_nonneg` from a single step to an arbitrary number
    of updates via structural induction.  The C++ diagonal clamp `max(M2(0,0), 0)`
    is therefore redundant for the rational model — it can never fire. -/
theorem welfordVec2FoldFrom_m00_nonneg (s₀ : WelfordVec2State)
    (pts : List (Rat × Rat)) (h : 0 ≤ s₀.m00) :
    0 ≤ (welfordVec2FoldFrom s₀ pts).m00 := by
  induction pts generalizing s₀ with
  | nil  => simpa [welfordVec2FoldFrom]
  | cons p t ih =>
    obtain ⟨x, y⟩ := p
    simp only [welfordVec2FoldFrom]
    exact ih (welfordVec2Update s₀ x y) (welfordVec2_m00_nonneg s₀ x y h)

/-- M2[1,1] is non-negative after folding any list, given it was non-negative initially.

    Symmetric to `welfordVec2FoldFrom_m00_nonneg`. -/
theorem welfordVec2FoldFrom_m11_nonneg (s₀ : WelfordVec2State)
    (pts : List (Rat × Rat)) (h : 0 ≤ s₀.m11) :
    0 ≤ (welfordVec2FoldFrom s₀ pts).m11 := by
  induction pts generalizing s₀ with
  | nil  => simpa [welfordVec2FoldFrom]
  | cons p t ih =>
    obtain ⟨x, y⟩ := p
    simp only [welfordVec2FoldFrom]
    exact ih (welfordVec2Update s₀ x y) (welfordVec2_m11_nonneg s₀ x y h)

/-- After folding any list from the zero-initialised state, M2[0,0] ≥ 0.

    Corollary of `welfordVec2FoldFrom_m00_nonneg` with `initState2.m00 = 0`. -/
theorem welfordVec2Fold_m00_nonneg (pts : List (Rat × Rat)) :
    0 ≤ (welfordVec2Fold pts).m00 :=
  welfordVec2FoldFrom_m00_nonneg initState2 pts (le_refl 0)

/-- After folding any list from the zero-initialised state, M2[1,1] ≥ 0.

    Corollary of `welfordVec2FoldFrom_m11_nonneg` with `initState2.m11 = 0`. -/
theorem welfordVec2Fold_m11_nonneg (pts : List (Rat × Rat)) :
    0 ≤ (welfordVec2Fold pts).m11 :=
  welfordVec2FoldFrom_m11_nonneg initState2 pts (le_refl 0)

end PX4.WelfordMeanVector2D
