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
| `welfordVec2_m01_step` | M2[0,1] recurrence: increment = δx * δy * (n-1)/n | ✅ Proved |
| `welfordVec2_m01_single_obs` | After one observation from zero state, m01 = 0 | ✅ Proved |
| `welfordVec2_psd` | 2×2 covariance matrix is PSD: m01² ≤ m00 * m11 preserved | ✅ Proved |
| `welfordVec2FoldFrom_count` | Count after fold = init_count + length | ✅ Proved |
| `welfordVec2FoldFrom_mean_x_inv` | mean_x * count = init_mean_x * init_count + Σxᵢ | ✅ Proved |
| `welfordVec2FoldFrom_mean_y_inv` | mean_y * count = init_mean_y * init_count + Σyᵢ | ✅ Proved |
| `welfordVec2FoldFrom_m00_nonneg` | Fold preserves m00 ≥ 0 | ✅ Proved |
| `welfordVec2FoldFrom_m11_nonneg` | Fold preserves m11 ≥ 0 | ✅ Proved |
| `welfordVec2FoldFrom_psd` | Fold preserves PSD: m01² ≤ m00 * m11 | ✅ Proved |
| `welfordVec2Fold_count` | fold count = list length | ✅ Proved |
| `welfordVec2Fold_mean_x` | Non-empty list: mean_x = Σxᵢ / length | ✅ Proved |
| `welfordVec2Fold_mean_y` | Non-empty list: mean_y = Σyᵢ / length | ✅ Proved |
| `welfordVec2Fold_m00_nonneg` | Starting from zero state, m00 ≥ 0 after fold | ✅ Proved |
| `welfordVec2Fold_m11_nonneg` | Starting from zero state, m11 ≥ 0 after fold | ✅ Proved |
| `welfordVec2Fold_psd` | Starting from zero state, 2×2 matrix PSD after fold | ✅ Proved |
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

/-! ## M2 off-diagonal (covariance) theorems -/

/-- The m01 increment equals δx * δy * (1 - n⁻¹), where n = count + 1 is the new count.

    The off-diagonal M2[0,1] is the Welford covariance accumulator.  Unlike the diagonal
    entries m00/m11, it can be negative (for negatively correlated data).  This theorem
    captures the closed-form increment: `(x - mx_old) * (y - my_old) * (n-1) / n`. -/
theorem welfordVec2_m01_step (s : WelfordVec2State) (x y : Rat) :
    (welfordVec2Update s x y).m01 =
    s.m01 + (x - s.mx) * (y - s.my) * (1 - (↑(s.count + 1))⁻¹) := by
  simp only [welfordVec2Update]
  have hn : (↑(s.count + 1) : Rat) ≠ 0 := succ_cast_ne_zero s.count
  congr 1
  -- Goal: (x - s.mx) * (y - (s.my + (y - s.my) / ↑(s.count+1)))
  --     = (x - s.mx) * (y - s.my) * (1 - (↑(s.count+1))⁻¹)
  have hy : y - (s.my + (y - s.my) / ↑(s.count + 1)) =
            (y - s.my) * (1 - (↑(s.count + 1))⁻¹) := by
    rw [Rat.div_def]
    simp [Rat.sub_eq_add_neg, Rat.neg_add, Rat.add_assoc, Rat.mul_add, Rat.mul_neg, Rat.mul_one]
  rw [hy]
  rw [← Rat.mul_assoc]

/-- After a single observation from the zero state, the covariance accumulator m01 = 0.

    This follows because the count goes 0 → 1, so the factor (1 − n⁻¹) = 0, making the
    off-diagonal increment zero regardless of the input. -/
theorem welfordVec2_m01_single_obs (x y : Rat) :
    (welfordVec2Update initState2 x y).m01 = 0 := by
  rw [welfordVec2_m01_step]
  simp only [initState2]
  push_cast
  rw [show (1:Rat)⁻¹ = 1 from by native_decide]
  simp [Rat.sub_self, Rat.mul_zero, Rat.add_zero]

private theorem m00_increment (s : WelfordVec2State) (x y : Rat) :
    (welfordVec2Update s x y).m00 =
    s.m00 + (x - s.mx) * (x - s.mx) * (1 - (↑(s.count + 1))⁻¹) := by
  simp only [welfordVec2Update]
  congr 1
  have hx : x - (s.mx + (x - s.mx) / ↑(s.count + 1)) =
            (x - s.mx) * (1 - (↑(s.count + 1))⁻¹) := by
    rw [Rat.div_def]
    simp [Rat.sub_eq_add_neg, Rat.neg_add, Rat.add_assoc, Rat.mul_add, Rat.mul_neg, Rat.mul_one]
  rw [hx, ← Rat.mul_assoc]

private theorem m11_increment (s : WelfordVec2State) (x y : Rat) :
    (welfordVec2Update s x y).m11 =
    s.m11 + (y - s.my) * (y - s.my) * (1 - (↑(s.count + 1))⁻¹) := by
  simp only [welfordVec2Update]
  congr 1
  have hy : y - (s.my + (y - s.my) / ↑(s.count + 1)) =
            (y - s.my) * (1 - (↑(s.count + 1))⁻¹) := by
    rw [Rat.div_def]
    simp [Rat.sub_eq_add_neg, Rat.neg_add, Rat.add_assoc, Rat.mul_add, Rat.mul_neg, Rat.mul_one]
  rw [hy, ← Rat.mul_assoc]

/-! ### Private helpers for the PSD theorem -/

/-- Schur complement identity: `b*(b*v²+c*u²-2*a*u*v) = (b*v-a*u)²+(b*c-a²)*u²`.
    Used to show the quadratic form arising in the PSD rank-1 update is non-negative. -/
private theorem psd_identity (a b c u v : Rat) :
    b * (b * (v * v) + c * (u * u) - 2 * a * (u * v)) =
    (b * v - a * u) * (b * v - a * u) + (b * c - a * a) * (u * u) := by
  have lhs_nf : b * (b * (v * v) + c * (u * u) - 2 * a * (u * v)) =
      b * (b * (v * v)) + b * (c * (u * u)) + -(b * (2 * (a * (u * v)))) := by
    rw [Rat.sub_eq_add_neg, Rat.mul_add, Rat.mul_add, Rat.mul_neg, Rat.mul_assoc 2 a (u*v)]
  have sq_nf : (b * v - a * u) * (b * v - a * u) =
      b * (b * (v * v)) + a * (a * (u * u)) + -(b * (2 * (a * (u * v)))) := by
    rw [Rat.sub_eq_add_neg, Rat.add_mul, Rat.mul_add, Rat.mul_add,
        Rat.neg_mul, Rat.mul_neg, Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]
    rw [show b * v * (b * v) = b * (b * (v * v)) from by
      rw [Rat.mul_assoc b v (b*v), show v * (b * v) = b * (v * v) from by
        rw [← Rat.mul_assoc v b v, Rat.mul_comm v b, Rat.mul_assoc b v v]]]
    rw [show b * v * (a * u) = b * (a * (u * v)) from by
      rw [Rat.mul_assoc b v (a*u), show v * (a * u) = a * (u * v) from by
        rw [← Rat.mul_assoc v a u, Rat.mul_comm v a, Rat.mul_assoc a v u, Rat.mul_comm v u]]]
    rw [show a * u * (b * v) = b * (a * (u * v)) from by
      rw [Rat.mul_assoc a u (b*v), show u * (b * v) = b * (u * v) from by
        rw [← Rat.mul_assoc u b v, Rat.mul_comm u b, Rat.mul_assoc b u v, Rat.mul_comm u v],
      ← Rat.mul_assoc a b (u*v), Rat.mul_comm a b, Rat.mul_assoc b a (u*v)]]
    rw [show a * u * (a * u) = a * (a * (u * u)) from by
      rw [Rat.mul_assoc a u (a*u), show u * (a * u) = a * (u * u) from by
        rw [← Rat.mul_assoc u a u, Rat.mul_comm u a, Rat.mul_assoc a u u]]]
    rw [← Rat.add_assoc (b*(b*(v*v)) + -(b*(a*(u*v)))),
        Rat.add_assoc (b*(b*(v*v))),
        show -(b*(a*(u*v))) + -(b*(a*(u*v))) = -(b*(2*(a*(u*v)))) from by
          rw [← Rat.neg_add, ← Rat.mul_add,
              show a*(u*v) + a*(u*v) = 2*(a*(u*v)) from by
                rw [show (2:Rat) = 1+1 from by native_decide, Rat.add_mul, Rat.one_mul]],
        Rat.add_assoc (b*(b*(v*v))),
        show -(b*(2*(a*(u*v)))) + a*(a*(u*u)) = a*(a*(u*u)) + -(b*(2*(a*(u*v)))) from
            Rat.add_comm _ _,
        ← Rat.add_assoc]
  have rest_nf : (b * c - a * a) * (u * u) =
      b * (c * (u * u)) + -(a * (a * (u * u))) := by
    rw [Rat.sub_eq_add_neg, Rat.add_mul, Rat.neg_mul,
        Rat.mul_assoc b c (u*u), Rat.mul_assoc a a (u*u)]
  rw [lhs_nf, sq_nf, rest_nf]
  have hST : a*(a*(u*u)) + -(a*(a*(u*u))) = 0 := Rat.add_neg_cancel _
  rw [Rat.add_assoc (b*(b*(v*v)) + a*(a*(u*u))) (-(b*(2*(a*(u*v))))) _]
  rw [show -(b*(2*(a*(u*v)))) + (b*(c*(u*u)) + -(a*(a*(u*u)))) =
      b*(c*(u*u)) + (-(b*(2*(a*(u*v)))) + -(a*(a*(u*u)))) from Rat.add_left_comm _ _ _]
  rw [← Rat.add_assoc (b*(b*(v*v)) + a*(a*(u*u))) (b*(c*(u*u)))]
  rw [Rat.add_assoc (b*(b*(v*v))) (a*(a*(u*u))) (b*(c*(u*u)))]
  rw [show a*(a*(u*u)) + b*(c*(u*u)) = b*(c*(u*u)) + a*(a*(u*u)) from Rat.add_comm _ _]
  rw [← Rat.add_assoc (b*(b*(v*v))) (b*(c*(u*u))) (a*(a*(u*u)))]
  rw [Rat.add_assoc (b*(b*(v*v)) + b*(c*(u*u))) (a*(a*(u*u))) _]
  rw [show a*(a*(u*u)) + (-(b*(2*(a*(u*v)))) + -(a*(a*(u*u)))) =
      -(b*(2*(a*(u*v)))) + (a*(a*(u*u)) + -(a*(a*(u*u)))) from Rat.add_left_comm _ _ _]
  rw [hST, Rat.add_zero]

/-- Ring identity for rank-1 PSD update:
    `(B+u²t)(C+v²t) - (A+uvt)² = (BC-A²) + t*(Bv²+Cu²-2Auv)`. -/
private theorem psd_ring_id (A B C t u v : Rat) :
    (B + u*u*t) * (C + v*v*t) - (A + u*v*t) * (A + u*v*t) =
    (B*C - A*A) + t * (B*(v*v) + C*(u*u) - 2*(A*(u*v))) := by
  simp only [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.mul_neg, Rat.mul_assoc,
             Rat.add_assoc]
  have h1 : u*(u*(t*C)) = t*(C*(u*u)) := by
    rw [← Rat.mul_assoc u u (t*C), Rat.mul_comm (u*u) (t*C), Rat.mul_assoc t C (u*u)]
  have h2 : B*(v*(v*t)) = t*(B*(v*v)) := by
    rw [← Rat.mul_assoc v v t, Rat.mul_comm (v*v) t, ← Rat.mul_assoc B t (v*v),
        Rat.mul_comm B t, Rat.mul_assoc t B (v*v)]
  have hh3a : u*(v*(t*A)) = t*(A*(u*v)) := by
    rw [show u*(v*(t*A)) = (u*v*t)*A from by
          rw [← Rat.mul_assoc u v (t*A), ← Rat.mul_assoc (u*v) t A],
        Rat.mul_comm (u*v*t) A, ← Rat.mul_assoc A (u*v) t, Rat.mul_comm (A*(u*v)) t]
  have hh3b : A*(u*(v*t)) = t*(A*(u*v)) := by
    rw [← Rat.mul_assoc A u (v*t), ← Rat.mul_assoc (A*u) v t, Rat.mul_assoc A u v,
        Rat.mul_comm (A*(u*v)) t]
  have h3 : -(u*(v*(t*A))) + -(A*(u*(v*t))) = -(t*(2*(A*(u*v)))) := by
    rw [hh3a, hh3b, ← Rat.neg_add, ← Rat.mul_add]
    congr 1; congr 1
    rw [show (2:Rat) = 1+1 from by native_decide, Rat.add_mul, Rat.one_mul]
  have h4 : u*(u*(t*(v*(v*t)))) + -(u*(v*(t*(u*(v*t))))) = 0 := by
    rw [show u*(u*(t*(v*(v*t)))) = (u*u)*(v*v)*(t*t) from by
          rw [← Rat.mul_assoc u u (t*(v*(v*t))),
              show t*(v*(v*t)) = (v*v)*(t*t) from by
                rw [← Rat.mul_assoc v v t, ← Rat.mul_assoc t (v*v) t,
                    Rat.mul_comm (t*(v*v)) t, ← Rat.mul_assoc t t (v*v),
                    Rat.mul_comm (t*t) (v*v)],
              ← Rat.mul_assoc (u*u) (v*v) (t*t)],
        show u*(v*(t*(u*(v*t)))) = (u*u)*(v*v)*(t*t) from by
          rw [show u*(v*(t*(u*(v*t)))) = (u*v)*(u*v)*(t*t) from by
                rw [← Rat.mul_assoc u v (t*(u*(v*t))),
                    show t*(u*(v*t)) = (u*v)*(t*t) from by
                      rw [← Rat.mul_assoc u v t, ← Rat.mul_assoc t (u*v) t,
                          Rat.mul_comm (t*(u*v)) t, ← Rat.mul_assoc t t (u*v),
                          Rat.mul_comm (t*t) (u*v)],
                    ← Rat.mul_assoc (u*v) (u*v) (t*t)],
              show (u*v)*(u*v)*(t*t) = (u*u)*(v*v)*(t*t) from by
                congr 1
                rw [← Rat.mul_assoc (u*v) u v, Rat.mul_assoc u v u, Rat.mul_comm v u,
                    ← Rat.mul_assoc u u v, Rat.mul_assoc (u*u) v v]],
        Rat.add_neg_cancel]
  rw [h1, h2]
  simp only [Rat.neg_add]
  rw [← Rat.add_assoc (-(u*(v*(t*A)))), h3]
  rw [Rat.add_left_comm (u*(u*(t*(v*(v*t))))) (-(A*A))
        (-(t*(2*(A*(u*v)))) + -(u*(v*(t*(u*(v*t))))))]
  rw [Rat.add_left_comm (u*(u*(t*(v*(v*t))))) (-(t*(2*(A*(u*v))))) (-(u*(v*(t*(u*(v*t))))))]
  rw [show u*(u*(t*(v*(v*t)))) + -(u*(v*(t*(u*(v*t))))) = 0 from h4]
  rw [Rat.add_zero]
  rw [Rat.add_left_comm (t*(B*(v*v))) (-(A*A)) (-(t*(2*(A*(u*v)))))]
  rw [Rat.add_left_comm (t*(C*(u*u))) (-(A*A)) _]
  rw [Rat.add_left_comm (t*(C*(u*u))) (t*(B*(v*v))) (-(t*(2*(A*(u*v)))))]

/-- If `0 < B` and `0 ≤ B * form`, then `0 ≤ form`. -/
private theorem nonneg_of_pos_mul_nonneg {B form : Rat} (hB : 0 < B) (hBform : 0 ≤ B * form) :
    0 ≤ form := by
  rcases Classical.em (0 ≤ form) with h | h
  · exact h
  · exfalso
    have hlt : form < 0 := Rat.not_le.mp h
    have : B * form < B * 0 := Rat.mul_lt_mul_of_pos_left hlt hB
    simp at this
    exact absurd hBform (Rat.not_le.mpr this)

/-- The quadratic form `B*v²+C*u²-2*A*u*v ≥ 0` when `A²≤B*C`, `B≥0`, `C≥0`. -/
private theorem quad_form_nonneg (A B C u v : Rat)
    (h00 : 0 ≤ B) (h11 : 0 ≤ C) (hpsd : A * A ≤ B * C) :
    0 ≤ B * (v * v) + C * (u * u) - 2 * (A * (u * v)) := by
  rcases Classical.em (B = 0) with hB0 | hBne
  · -- B = 0 case: A must be 0 (from hpsd), form reduces to C*(u*u) ≥ 0
    subst hB0
    simp at hpsd
    have hAA : A * A = 0 := Rat.le_antisymm hpsd (rat_sq_nonneg A)
    have hA : A = 0 := by
      cases Rat.mul_eq_zero.mp hAA with | inl h => exact h | inr h => exact h
    subst hA
    simp only [Rat.zero_mul, Rat.mul_zero, Rat.zero_add]
    rw [Rat.sub_eq_add_neg, show -(0:Rat) = 0 from by simp, Rat.add_zero]
    exact Rat.mul_nonneg h11 (rat_sq_nonneg u)
  · -- B > 0 case: multiply by B and use psd_identity
    have hBpos : 0 < B := Rat.lt_of_le_of_ne h00 (Ne.symm hBne)
    apply nonneg_of_pos_mul_nonneg hBpos
    rw [show B * (B*(v*v) + C*(u*u) - 2*(A*(u*v))) =
             B * (B*(v*v) + C*(u*u) - 2*A*(u*v)) from by
           congr 1; rw [← Rat.mul_assoc 2 A (u*v)]]
    rw [psd_identity A B C u v]
    apply Rat.add_nonneg
    · exact rat_sq_nonneg _
    · apply Rat.mul_nonneg
      · rw [Rat.sub_eq_add_neg, ← Rat.add_neg_cancel (A*A)]
        exact Rat.add_le_add_right.mpr hpsd
      · exact rat_sq_nonneg _

/-- The 2×2 covariance matrix is positive semi-definite (PSD) after each update step:
    m01² ≤ m00 * m11, provided it was PSD before.

    This is the key structural property of the Welford algorithm: the running M2 matrix
    always represents a valid sample covariance matrix.  The proof exploits the
    rank-1 update structure: M2_{n+1} = M2_n + t·(δ⊗δ) where t = (n-1)/n ≥ 0 and
    δ = (δx, δy) = (x − mx_old, y − my_old).

    The increment matrix t·(δ⊗δ) is itself PSD (it is an outer product), and the
    sum of two PSD matrices is PSD. -/
theorem welfordVec2_psd (s : WelfordVec2State) (x y : Rat)
    (h00 : 0 ≤ s.m00) (h11 : 0 ≤ s.m11) (hpsd : s.m01 * s.m01 ≤ s.m00 * s.m11) :
    let s' := welfordVec2Update s x y
    s'.m01 * s'.m01 ≤ s'.m00 * s'.m11 := by
  simp only []
  rw [welfordVec2_m01_step, m00_increment, m11_increment]
  -- Let A = s.m01, B = s.m00, C = s.m11, u = x-s.mx, v = y-s.my, t = 1-(count+1)⁻¹
  -- Goal: (A + u*v*t)*(A + u*v*t) ≤ (B + u*u*t)*(C + v*v*t)
  rw [Rat.le_iff_sub_nonneg]
  rw [psd_ring_id s.m01 s.m00 s.m11 (1 - (↑(s.count + 1))⁻¹) (x - s.mx) (y - s.my)]
  apply Rat.add_nonneg
  · -- 0 ≤ B*C - A*A (from hpsd)
    rw [Rat.sub_eq_add_neg, ← Rat.add_neg_cancel (s.m01 * s.m01)]
    exact Rat.add_le_add_right.mpr hpsd
  · -- 0 ≤ t * quadratic_form (t ≥ 0 and form ≥ 0)
    apply Rat.mul_nonneg
    · -- 0 ≤ 1 - (count+1)⁻¹
      have hpos : (0 : Rat) < ↑(s.count + 1) := by exact_mod_cast Nat.succ_pos s.count
      have h1nR : (1 : Rat) ≤ ↑(s.count + 1) := by exact_mod_cast Nat.le_add_left 1 s.count
      rw [Rat.sub_eq_add_neg, ← Rat.add_neg_cancel (↑(s.count + 1))⁻¹]
      exact Rat.add_le_add_right.mpr (inv_le_one_of_one_le _ h1nR hpos)
    · -- 0 ≤ B*v² + C*u² - 2*A*u*v (quadratic form)
      exact quad_form_nonneg s.m01 s.m00 s.m11 (x - s.mx) (y - s.my) h00 h11 hpsd

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

/-- Fold preserves m00 ≥ 0 (diagonal variance accumulator for x). -/
theorem welfordVec2FoldFrom_m00_nonneg (s₀ : WelfordVec2State) (pts : List (Rat × Rat))
    (h : 0 ≤ s₀.m00) : 0 ≤ (welfordVec2FoldFrom s₀ pts).m00 := by
  induction pts generalizing s₀ with
  | nil  => simpa [welfordVec2FoldFrom]
  | cons p t ih =>
    simp only [welfordVec2FoldFrom]
    exact ih _ (welfordVec2_m00_nonneg s₀ p.1 p.2 h)

/-- Fold preserves m11 ≥ 0 (diagonal variance accumulator for y). -/
theorem welfordVec2FoldFrom_m11_nonneg (s₀ : WelfordVec2State) (pts : List (Rat × Rat))
    (h : 0 ≤ s₀.m11) : 0 ≤ (welfordVec2FoldFrom s₀ pts).m11 := by
  induction pts generalizing s₀ with
  | nil  => simpa [welfordVec2FoldFrom]
  | cons p t ih =>
    simp only [welfordVec2FoldFrom]
    exact ih _ (welfordVec2_m11_nonneg s₀ p.1 p.2 h)

/-- Fold preserves the PSD property of the 2×2 covariance matrix: m01² ≤ m00 * m11. -/
theorem welfordVec2FoldFrom_psd (s₀ : WelfordVec2State) (pts : List (Rat × Rat))
    (h00 : 0 ≤ s₀.m00) (h11 : 0 ≤ s₀.m11) (hpsd : s₀.m01 * s₀.m01 ≤ s₀.m00 * s₀.m11) :
    let s' := welfordVec2FoldFrom s₀ pts
    s'.m01 * s'.m01 ≤ s'.m00 * s'.m11 := by
  induction pts generalizing s₀ with
  | nil  => simpa [welfordVec2FoldFrom]
  | cons p t ih =>
    simp only [welfordVec2FoldFrom]
    apply ih
    · exact welfordVec2_m00_nonneg s₀ p.1 p.2 h00
    · exact welfordVec2_m11_nonneg s₀ p.1 p.2 h11
    · exact welfordVec2_psd s₀ p.1 p.2 h00 h11 hpsd

/-- Starting from zero state, m00 ≥ 0 after folding any list. -/
theorem welfordVec2Fold_m00_nonneg (pts : List (Rat × Rat)) :
    0 ≤ (welfordVec2Fold pts).m00 :=
  welfordVec2FoldFrom_m00_nonneg initState2 pts (by simp [initState2])

/-- Starting from zero state, m11 ≥ 0 after folding any list. -/
theorem welfordVec2Fold_m11_nonneg (pts : List (Rat × Rat)) :
    0 ≤ (welfordVec2Fold pts).m11 :=
  welfordVec2FoldFrom_m11_nonneg initState2 pts (by simp [initState2])

/-- Starting from zero state, the 2×2 covariance matrix is PSD after folding any list:
    m01² ≤ m00 * m11. This guarantees the accumulated M2 matrix is always a valid
    positive semi-definite matrix. -/
theorem welfordVec2Fold_psd (pts : List (Rat × Rat)) :
    let s := welfordVec2Fold pts
    s.m01 * s.m01 ≤ s.m00 * s.m11 :=
  welfordVec2FoldFrom_psd initState2 pts
    (by simp [initState2])
    (by simp [initState2])
    (by simp [initState2])

end PX4.WelfordMeanVector2D
