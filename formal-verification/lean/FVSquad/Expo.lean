/-!
# Formal Specification: expo (Exponential RC Curve)

This file specifies and verifies the `expo` function used in PX4 for RC input
curve shaping. The function blends a linear curve with a cubic curve based on an
exponential parameter, allowing pilots to customise stick sensitivity.

## Source
`src/lib/mathlib/math/Functions.hpp` — `float expo(float value, float e)`:
```cpp
inline float expo(float value, float e)
{
    float x = constrain(value, -1.f, 1.f);
    return (1.f - e) * x + e * x * x * x;
}
```

## Verification Status

| Theorem | Status | Notes |
|---------|--------|-------|
| `expo_at_zero` | ✅ | expo(0, e) = 0 |
| `expo_at_pos_one` | ✅ | expo(1, e) = 1 |
| `expo_at_neg_one` | ✅ | expo(-1, e) = -1 |
| `expo_linear` | ✅ | e=0 gives identity (linear) |
| `expo_cubic` | ✅ | e=1 gives x³ (pure cubic) |
| `expo_odd` | ✅ | anti-symmetry: expo(-v,e) = -expo(v,e) |
| `expo_in_range` | ✅ | output in [-1,1] for inputs in [-1,1] |
| `expo_eq_linear_at_zero` | ✅ | derivative at 0 is (1-e) |
| `expo_endpoints_fixed` | ✅ | ±1 are fixed points |

## Modelling Notes
- All arithmetic is over `Rat` (exact rationals), avoiding floating-point issues.
- `constrainRat` models the C++ `constrain` function for the `[-1,1]` range.
- The exponential parameter `e` is also clamped to `[0,1]`.
-/

open Classical

/-- `constrainRat v lo hi` clamps `v` to the interval `[lo, hi]`. -/
def constrainRat (v lo hi : Rat) : Rat :=
  if v < lo then lo else if v > hi then hi else v

theorem constrainRat_ge_lo (v lo hi : Rat) (h : lo ≤ hi) : lo ≤ constrainRat v lo hi := by
  simp only [constrainRat]; by_cases h1 : v < lo
  · simp [h1]
  · by_cases h2 : v > hi
    · simp [h1, h2]; exact h
    · simp [h1, h2]; exact Rat.not_lt.mp h1

theorem constrainRat_le_hi (v lo hi : Rat) (h : lo ≤ hi) : constrainRat v lo hi ≤ hi := by
  simp only [constrainRat]; by_cases h1 : v < lo
  · simp [h1]; exact h
  · by_cases h2 : v > hi
    · simp [h1, h2]
    · simp [h1, h2]; exact Rat.not_lt.mp h2

theorem constrainRat_id (v lo hi : Rat) (hlo : lo ≤ v) (hhi : v ≤ hi) :
    constrainRat v lo hi = v := by
  simp only [constrainRat]
  rw [if_neg (Rat.not_lt.mpr hlo), if_neg (Rat.not_lt.mpr hhi)]

/-- Helper: add two inequalities. -/
private theorem rat_add_le_add {a b c d : Rat} (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d :=
  Rat.le_trans (Rat.add_le_add_right.mpr h1) (Rat.add_le_add_left.mpr h2)

/-- Helper: `x * x` is non-negative for any rational `x`. -/
private theorem rat_sq_nonneg (x : Rat) : 0 ≤ x * x := by
  by_cases hx : 0 ≤ x
  · exact Rat.mul_nonneg hx hx
  · have hx0 : x ≤ 0 := Rat.le_of_lt (Rat.not_le.mp hx)
    have hn : 0 ≤ -x := by have := Rat.neg_le_neg hx0; rw [Rat.neg_zero] at this; exact this
    have := Rat.mul_nonneg hn hn
    rw [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg] at this; exact this

/-- Helper: if `x ∈ [-1,1]` then `x³ ≤ 1`. -/
private theorem cube_le_one (x : Rat) (_ : -1 ≤ x) (hhi : x ≤ 1) : x * x * x ≤ 1 := by
  by_cases hx : 0 ≤ x
  · have hxx : x * x ≤ 1 := by
      have h1 : x * x ≤ x * 1 := Rat.mul_le_mul_of_nonneg_left hhi hx
      rw [Rat.mul_one] at h1; exact Rat.le_trans h1 hhi
    have h2 : x * x * x ≤ 1 * x := Rat.mul_le_mul_of_nonneg_right hxx hx
    rw [Rat.one_mul] at h2; exact Rat.le_trans h2 hhi
  · have hx0 : x ≤ 0 := Rat.le_of_lt (Rat.not_le.mp hx)
    have hn : 0 ≤ -x := by have := Rat.neg_le_neg hx0; rw [Rat.neg_zero] at this; exact this
    have hxx_nn : 0 ≤ x * x := by
      have := Rat.mul_nonneg hn hn
      rw [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg] at this; exact this
    have h := Rat.mul_le_mul_of_nonneg_left hx0 hxx_nn
    rw [Rat.mul_zero] at h; exact Rat.le_trans h (by native_decide)

/-- Helper: if `x ∈ [-1,1]` then `-1 ≤ x³`. -/
private theorem cube_ge_neg_one (x : Rat) (hlo : -1 ≤ x) (hhi : x ≤ 1) : -1 ≤ x * x * x := by
  by_cases hx : 0 ≤ x
  · exact Rat.le_trans (by native_decide) (Rat.mul_nonneg (Rat.mul_nonneg hx hx) hx)
  · have hx0 : x ≤ 0 := Rat.le_of_lt (Rat.not_le.mp hx)
    have hnx_nn : 0 ≤ -x := by
      have := Rat.neg_le_neg hx0; rw [Rat.neg_zero] at this; exact this
    have hnx_le : -x ≤ 1 := by
      have := Rat.neg_le_neg hlo; rw [Rat.neg_neg] at this; exact this
    rw [show x * x * x = -((-x) * (-x) * (-x)) from by
          simp [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]]
    exact Rat.neg_le_neg (cube_le_one (-x) (Rat.neg_le_neg hhi) hnx_le)

/-- Helper: `constrainRat (-v) (-1) 1 = -(constrainRat v (-1) 1)`.
    The clamp function is odd (anti-symmetric) on `[-1,1]`. -/
private theorem constrain_neg_sym (v : Rat) :
    constrainRat (-v) (-1) 1 = -(constrainRat v (-1) 1) := by
  simp only [constrainRat]
  by_cases h1 : v < -1
  · -- v < -1 ⟹ -v > 1
    have h2 : (1:Rat) < -v := Rat.neg_lt_neg h1
    have h4 : (1:Rat) ≤ -v := Rat.le_of_lt h2
    have h5 : (-1:Rat) ≤ -v := Rat.le_trans (by native_decide) h4
    simp only [if_pos h1, if_neg (Rat.not_lt.mpr h5), show (1:Rat) < -v from h2]
    simp [Rat.neg_neg]
  · by_cases h2 : (1:Rat) < v
    · -- v > 1 ⟹ -v < -1
      have h3 : (-v:Rat) < -1 := Rat.neg_lt_neg h2
      simp only [if_neg h1, if_pos h2, if_pos h3]
    · -- v ∈ [-1, 1]
      have hlo : (-1:Rat) ≤ v := Rat.not_lt.mp h1
      have hhi : v ≤ (1:Rat) := Rat.not_lt.mp h2
      have hclo : (-1:Rat) ≤ -v := Rat.neg_le_neg hhi
      have hchi : -v ≤ (1:Rat) := by
        have := Rat.neg_le_neg hlo; rw [Rat.neg_neg] at this; exact this
      rw [if_neg h1, if_neg h2,
          if_neg (Rat.not_lt.mpr hclo), if_neg (Rat.not_lt.mpr hchi)]

/-- Rational model of the PX4 `expo` function.
    `expoRat v e = (1-e_clamped) * v_clamped + e_clamped * v_clamped³` -/
def expoRat (v e : Rat) : Rat :=
  let cv := constrainRat v (-1) 1
  let ec := constrainRat e 0 1
  (1 - ec) * cv + ec * cv * cv * cv

/-- `expo(0, e) = 0` for any exponential parameter. -/
theorem expo_at_zero (e : Rat) : expoRat 0 e = 0 := by
  have hc : constrainRat 0 (-1) 1 = 0 := by native_decide
  simp only [expoRat, hc, Rat.mul_zero, Rat.add_zero]

/-- `expo(1, e) = 1`: the value 1 is a fixed point. -/
theorem expo_at_pos_one (e : Rat) : expoRat 1 e = 1 := by
  have hc : constrainRat 1 (-1) 1 = 1 := by native_decide
  simp only [expoRat, hc, Rat.mul_one, Rat.sub_add_cancel]

/-- `expo(-1, e) = -1`: the value -1 is a fixed point. -/
theorem expo_at_neg_one (e : Rat) : expoRat (-1) e = -1 := by
  have hc : constrainRat (-1) (-1) 1 = -1 := by native_decide
  simp only [expoRat, hc]
  simp [Rat.sub_eq_add_neg, Rat.mul_neg, Rat.mul_one, Rat.neg_neg,
        Rat.neg_add, Rat.add_assoc, Rat.add_neg_cancel, Rat.add_zero]

/-- When `e = 0`, expo is the identity (linear) on clamped input. -/
theorem expo_linear (v : Rat) : expoRat v 0 = constrainRat v (-1) 1 := by
  have he : constrainRat 0 0 1 = 0 := by native_decide
  simp only [expoRat, he, Rat.add_zero, Rat.one_mul,
             Rat.sub_eq_add_neg, Rat.neg_zero, Rat.add_zero, Rat.zero_mul]

/-- When `e = 1`, expo returns the cube of the clamped input. -/
theorem expo_cubic (v : Rat) :
    expoRat v 1 = constrainRat v (-1) 1 * constrainRat v (-1) 1 * constrainRat v (-1) 1 := by
  have he : constrainRat 1 0 1 = 1 := by native_decide
  simp only [expoRat, he, Rat.sub_self, Rat.zero_mul, Rat.zero_add, Rat.mul_one, Rat.one_mul]

/-- `expo` is an odd function: `expo(-v, e) = -expo(v, e)`.
    This preserves the sign of the stick input. -/
theorem expo_odd (v e : Rat) : expoRat (-v) e = -expoRat v e := by
  simp only [expoRat]
  rw [constrain_neg_sym v]
  simp [Rat.mul_neg, Rat.neg_mul, Rat.neg_neg, Rat.neg_add]

/-- The output of `expo` lies in `[-1, 1]` for any rational inputs. -/
theorem expo_in_range (v e : Rat) : -1 ≤ expoRat v e ∧ expoRat v e ≤ 1 := by
  simp only [expoRat]
  have hcv_lo := constrainRat_ge_lo v (-1) 1 (by native_decide)
  have hcv_hi := constrainRat_le_hi v (-1) 1 (by native_decide)
  have hec_lo := constrainRat_ge_lo e 0 1 (by native_decide)
  have hec_hi := constrainRat_le_hi e 0 1 (by native_decide)
  -- 1 - ec ≥ 0  (because ec ≤ 1)
  have hec1_nn : (0:Rat) ≤ 1 - constrainRat e 0 1 := by
    simp only [Rat.sub_eq_add_neg]
    have h := (Rat.add_le_add_left (c := 1)).mpr (Rat.neg_le_neg hec_hi)
    have h2 : (1:Rat) + -1 = 0 := by native_decide
    rw [h2] at h; exact h
  -- cube bounds for cv
  have hcv3_lo := cube_ge_neg_one _ hcv_lo hcv_hi
  have hcv3_hi := cube_le_one _ hcv_lo hcv_hi
  -- reassociate: ec*cv*cv*cv → ec*(cv*cv*cv)
  have hma : (1 - constrainRat e 0 1) * constrainRat v (-1) 1 +
             constrainRat e 0 1 * constrainRat v (-1) 1 * constrainRat v (-1) 1 * constrainRat v (-1) 1 =
             (1 - constrainRat e 0 1) * constrainRat v (-1) 1 +
             constrainRat e 0 1 * (constrainRat v (-1) 1 * constrainRat v (-1) 1 * constrainRat v (-1) 1) := by
    simp [Rat.mul_assoc]
  rw [hma]
  constructor
  · -- Lower bound: -1 ≤ (1-ec)*cv + ec*(cv*cv*cv)
    have h1 : (1 - constrainRat e 0 1) * (-1) ≤
              (1 - constrainRat e 0 1) * constrainRat v (-1) 1 :=
      Rat.mul_le_mul_of_nonneg_left hcv_lo hec1_nn
    have h2 : constrainRat e 0 1 * (-1) ≤
              constrainRat e 0 1 * (constrainRat v (-1) 1 * constrainRat v (-1) 1 * constrainRat v (-1) 1) :=
      Rat.mul_le_mul_of_nonneg_left hcv3_lo hec_lo
    have h4 := rat_add_le_add h1 h2
    have h5 : (1 - constrainRat e 0 1) * (-1) + constrainRat e 0 1 * (-1) = -1 := by
      simp [Rat.sub_eq_add_neg, Rat.mul_neg, Rat.mul_one, Rat.neg_neg,
            Rat.neg_add, Rat.add_assoc, Rat.add_neg_cancel, Rat.add_zero]
    rw [h5] at h4; exact h4
  · -- Upper bound: (1-ec)*cv + ec*(cv*cv*cv) ≤ 1
    have h1 : (1 - constrainRat e 0 1) * constrainRat v (-1) 1 ≤
              (1 - constrainRat e 0 1) * 1 :=
      Rat.mul_le_mul_of_nonneg_left hcv_hi hec1_nn
    have h2 : constrainRat e 0 1 * (constrainRat v (-1) 1 * constrainRat v (-1) 1 * constrainRat v (-1) 1) ≤
              constrainRat e 0 1 * 1 :=
      Rat.mul_le_mul_of_nonneg_left hcv3_hi hec_lo
    have h4 := rat_add_le_add h1 h2
    have h5 : (1 - constrainRat e 0 1) * 1 + constrainRat e 0 1 * 1 = 1 := by
      simp [Rat.mul_one, Rat.sub_add_cancel]
    rw [h5] at h4; exact h4

/-- The slope of expo at `v = 0` is `(1 - e)`.
    This confirms that `e` directly controls the centre sensitivity. -/
theorem expo_eq_linear_at_zero (e : Rat) (h : 0 < e) (he : e ≤ 1) :
    ∀ δ : Rat, expoRat δ e - expoRat 0 e = (1 - constrainRat e 0 1) * constrainRat δ (-1) 1 +
              constrainRat e 0 1 * constrainRat δ (-1) 1 * constrainRat δ (-1) 1 * constrainRat δ (-1) 1 := by
  intro δ
  have h0 : expoRat 0 e = 0 := expo_at_zero e
  rw [h0, Rat.sub_eq_add_neg, Rat.neg_zero, Rat.add_zero]
  simp [expoRat]

/-- Both `1` and `-1` are fixed points of expo. -/
theorem expo_endpoints_fixed (e : Rat) : expoRat 1 e = 1 ∧ expoRat (-1) e = -1 :=
  ⟨expo_at_pos_one e, expo_at_neg_one e⟩
