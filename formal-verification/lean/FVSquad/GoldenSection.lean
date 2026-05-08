/-!
# PX4 GoldenSection Search — Formal Verification

🔬 Lean Squad automated formal verification.

This file models and proves invariant properties of `math::goldensection` from
PX4-Autopilot's `mathlib`:

- **C++ source**: `src/lib/mathlib/math/SearchMin.hpp:56–81`
- **Informal spec**: `formal-verification/specs/goldensection_informal.md`

## C++ reference

```cpp
static constexpr double GOLDEN_RATIO = 1.6180339887; // (sqrt(5)+1)/2

template<typename _Tp>
inline const _Tp goldensection(const _Tp &arg1, const _Tp &arg2, _Tp(*fun)(_Tp), const _Tp &tol)
{
    _Tp a = arg1;
    _Tp b = arg2;
    _Tp c = b - (b - a) / GOLDEN_RATIO;
    _Tp d = a + (b - a) / GOLDEN_RATIO;

    while (abs_t(c - d) > tol) {
        if (fun(c) < fun(d)) { b = d; }
        else                 { a = c; }
        c = b - (b - a) / GOLDEN_RATIO;
        d = a + (b - a) / GOLDEN_RATIO;
    }
    return ((b + a) / (_Tp)2);
}
```

## Model

We model the abstract search bracket over `Rat` (exact rational arithmetic).
The golden ratio `φ` is abstracted to a parameter `r : Rat` representing `1/φ`
(the contraction ratio). The actual value `1/φ ≈ 0.618` satisfies `0 < r < 1`
and `r > 1/2`.

The higher-order `fun` argument and floating-point rounding of `GOLDEN_RATIO`
are **not modelled**: we prove structural/geometric invariants that hold for any
ratio `r` satisfying the stated constraints.

## Approximations / out of scope

- **IEEE 754 float semantics**: rounding of `1.6180339887` is not modelled.
- **Termination**: requires real-number topology; not proved here.
- **Optimality for unimodal f**: depends on `fun`'s structure; not modelled.
- **The function argument**: invariants hold regardless of `fun`'s comparison.
-/

namespace PX4.GoldenSection

/-! ## Helpers -/

/-- If `a + c ≤ b`, then `a ≤ b - c`. -/
private theorem le_sub_of_add_le {x y z : Rat} (h : x + z ≤ y) : x ≤ y - z := by
  have key := (Rat.add_le_add_right (c := -z)).mpr h
  rw [Rat.add_assoc, Rat.add_neg_cancel, Rat.add_zero, ← Rat.sub_eq_add_neg] at key
  exact key

/-- `a + (b - a) = b`. -/
private theorem add_sub_comm (a b : Rat) : a + (b - a) = b := by
  rw [Rat.add_comm, Rat.sub_add_cancel]

/-- Distributivity of multiplication over subtraction: `a * (b - c) = a*b - a*c`. -/
private theorem rat_mul_sub (a b c : Rat) : a * (b - c) = a * b - a * c := by
  rw [Rat.sub_eq_add_neg, Rat.mul_add, Rat.mul_neg, ← Rat.sub_eq_add_neg]

/-- `r + r = 2 * r`. -/
private theorem rat_two_mul (r : Rat) : r + r = 2 * r := by
  rw [← Rat.one_mul r, ← Rat.add_mul, show (1:Rat) + 1 = 2 from by native_decide, Rat.one_mul]

/-! ## Interior-point computation -/

/-- Left interior point: `c = b - (b - a) * r`. With r = 1/φ ≈ 0.618, this sits
    in the left-of-centre part of `[a, b]`. -/
def gsC (a b r : Rat) : Rat := b - (b - a) * r

/-- Right interior point: `d = a + (b - a) * r`. With r = 1/φ ≈ 0.618, this sits
    in the right-of-centre part of `[a, b]`. -/
def gsD (a b r : Rat) : Rat := a + (b - a) * r

/-- Bracket width. -/
def gsWidth (a b : Rat) : Rat := b - a

-- Sanity checks with r ≈ 0.618 on [0, 10]
#eval gsC 0 10 (618/1000)  -- 3.82
#eval gsD 0 10 (618/1000)  -- 6.18

/-! ## Lower-bound: `a ≤ c` -/

/-- The left interior point `c` is at or above the left bracket endpoint `a`,
    provided `r ≤ 1` (interior, not outside the bracket). -/
theorem gsC_ge_a (a b r : Rat) (hab : a ≤ b) (hr1 : r ≤ 1) :
    a ≤ gsC a b r := by
  simp only [gsC]
  -- want: a ≤ b - (b-a)*r  (equiv: a + (b-a)*r ≤ b)
  apply le_sub_of_add_le
  have hd : 0 ≤ b - a := (Rat.le_iff_sub_nonneg a b).mp hab
  have key : (b - a) * r ≤ (b - a) * 1 := Rat.mul_le_mul_of_nonneg_left hr1 hd
  rw [Rat.mul_one] at key
  calc a + (b - a) * r ≤ a + (b - a) := (Rat.add_le_add_left).mpr key
    _ = b := add_sub_comm a b

/-! ## Upper-bound: `d ≤ b` -/

/-- The right interior point `d` is at or below the right bracket endpoint `b`,
    provided `r ≤ 1`. -/
theorem gsD_le_b (a b r : Rat) (hab : a ≤ b) (hr1 : r ≤ 1) :
    gsD a b r ≤ b := by
  simp only [gsD]
  have hd : 0 ≤ b - a := (Rat.le_iff_sub_nonneg a b).mp hab
  have key : (b - a) * r ≤ (b - a) * 1 := Rat.mul_le_mul_of_nonneg_left hr1 hd
  rw [Rat.mul_one] at key
  calc a + (b - a) * r ≤ a + (b - a) := (Rat.add_le_add_left).mpr key
    _ = b := add_sub_comm a b

/-! ## Lower-bound: `a ≤ d` -/

/-- The right interior point `d` is above the left bracket endpoint `a`,
    provided `r ≥ 0`. -/
theorem gsD_ge_a (a b r : Rat) (hab : a ≤ b) (hr0 : 0 ≤ r) :
    a ≤ gsD a b r := by
  simp only [gsD]
  -- want: a ≤ a + (b-a)*r  (equiv: 0 ≤ (b-a)*r)
  have h : 0 ≤ (b - a) * r := Rat.mul_nonneg ((Rat.le_iff_sub_nonneg a b).mp hab) hr0
  calc a = a + 0                 := (Rat.add_zero a).symm
    _ ≤ a + (b - a) * r          := (Rat.add_le_add_left).mpr h

/-! ## Interior: `c ≤ d`

    When r ≥ 1/2, the left interior point c does not exceed the right interior
    point d. This is the key property that ensures the two probe points are
    distinct and ordered. The golden ratio satisfies r ≈ 0.618 > 1/2.

    The proof reduces to the identity
      `d - c = (b - a) * (2*r - 1)`
    which is non-negative when `r ≥ 1/2` and `b ≥ a`. -/

-- Helper: `w*r + w*r - w = w*(2*r - 1)`.
private theorem gs_interior_key (w r : Rat) : w * r + w * r - w = w * (2 * r - 1) := by
  symm
  rw [rat_mul_sub, Rat.mul_one, ← rat_two_mul, Rat.mul_add]

-- Helper: normalise `a + (b-a)*r - (b - (b-a)*r)` to `(b-a)*r + (b-a)*r - (b-a)`.
private theorem gs_interior_expand (a b r : Rat) :
    a + (b - a) * r - (b - (b - a) * r) = (b - a) * r + (b - a) * r - (b - a) := by
  simp only [Rat.sub_eq_add_neg, Rat.add_mul, Rat.neg_mul, Rat.neg_neg, Rat.neg_add]
  simp [Rat.add_comm, Rat.add_assoc, Rat.add_left_comm]

theorem gsC_le_gsD (a b r : Rat) (hab : a ≤ b) (hr_half : 1/2 ≤ r) :
    gsC a b r ≤ gsD a b r := by
  simp only [gsC, gsD]
  -- b - (b-a)*r ≤ a + (b-a)*r
  -- ↔ 0 ≤ a + (b-a)*r - (b - (b-a)*r) = (b-a)*(2*r-1) ≥ 0
  have hd : 0 ≤ b - a := (Rat.le_iff_sub_nonneg a b).mp hab
  rw [Rat.le_iff_sub_nonneg, gs_interior_expand, gs_interior_key]
  apply Rat.mul_nonneg hd
  -- 0 ≤ 2*r - 1 from r ≥ 1/2
  have h2 : (1:Rat)/2 * 2 ≤ r * 2 := Rat.mul_le_mul_of_nonneg_right hr_half (by native_decide)
  rw [show (1:Rat)/2 * 2 = 1 from by native_decide, Rat.mul_comm] at h2
  exact (Rat.le_iff_sub_nonneg 1 (2 * r)).mp h2

/-! ## Width after the `b ← d` step -/

/-- After the `b = d` branch, the bracket width shrinks by factor `r`. -/
theorem gs_width_b_step (a b r : Rat) :
    gsWidth a (gsD a b r) = gsWidth a b * r := by
  simp only [gsWidth, gsD]
  -- a + (b-a)*r - a = (b-a)*r
  rw [Rat.add_comm a _, Rat.add_sub_cancel]

/-! ## Width after the `a ← c` step -/

/-- After the `a = c` branch, the bracket width also shrinks by factor `r`. -/
theorem gs_width_a_step (a b r : Rat) :
    gsWidth (gsC a b r) b = gsWidth a b * r := by
  simp only [gsWidth, gsC]
  -- b - (b - (b-a)*r) = (b-a)*r
  -- Step: b - X where X = b - (b-a)*r; use b - (b - Y) = Y pattern
  rw [Rat.sub_eq_add_neg (a := b), Rat.neg_sub, Rat.add_comm, Rat.sub_add_cancel]

/-! ## Equal contraction on both branches -/

/-- Both update branches produce the same contracted width — this is the key
    optimality property of the golden-section method. -/
theorem gs_width_steps_equal (a b r : Rat) :
    gsWidth a (gsD a b r) = gsWidth (gsC a b r) b := by
  rw [gs_width_b_step, gs_width_a_step]

/-! ## Non-negativity of contracted width -/

/-- After the `b = d` step the new width is non-negative (bracket is valid). -/
theorem gs_width_nonneg_after_b_step (a b r : Rat) (hab : a ≤ b) (hr0 : 0 ≤ r) :
    0 ≤ gsWidth a (gsD a b r) := by
  rw [gs_width_b_step]
  exact Rat.mul_nonneg ((Rat.le_iff_sub_nonneg a b).mp hab) hr0

/-! ## Width strictly contracts when `r < 1` -/

/-- When `r < 1` and the bracket is non-trivial (`a < b`), each step strictly
    reduces the bracket width. This is the key convergence mechanism. -/
theorem gs_width_contracts (a b r : Rat) (hab : a < b) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    gsWidth a (gsD a b r) < gsWidth a b := by
  rw [gs_width_b_step]
  have hw : 0 < gsWidth a b := (Rat.lt_iff_sub_pos a b).mp hab
  calc gsWidth a b * r < gsWidth a b * 1 :=
        Rat.mul_lt_mul_of_pos_left hr1 hw
    _ = gsWidth a b := Rat.mul_one _

/-! ## Bracket containment after each step -/

/-- After `b = d`: the new right endpoint `d` is still within `[a, b]`. -/
theorem gsD_in_range (a b r : Rat) (hab : a ≤ b) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    a ≤ gsD a b r ∧ gsD a b r ≤ b :=
  ⟨gsD_ge_a a b r hab hr0, gsD_le_b a b r hab hr1⟩

/-- After `a = c`: the new left endpoint `c` is still within `[a, b]`. -/
theorem gsC_in_range (a b r : Rat) (hab : a ≤ b) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    a ≤ gsC a b r ∧ gsC a b r ≤ b := by
  constructor
  · exact gsC_ge_a a b r hab hr1
  · simp only [gsC]
    -- want: b - (b-a)*r ≤ b  ↔  0 ≤ b - (b-(b-a)*r) = (b-a)*r
    rw [Rat.le_iff_sub_nonneg]
    rw [show b - (b - (b - a) * r) = (b - a) * r by
          rw [Rat.sub_eq_add_neg (a := b), Rat.neg_sub, Rat.add_comm, Rat.sub_add_cancel]]
    exact Rat.mul_nonneg ((Rat.le_iff_sub_nonneg a b).mp hab) hr0

/-! ## Full ordering invariant: `a ≤ c ≤ d ≤ b` -/
theorem gs_ordering (a b r : Rat) (hab : a ≤ b) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hr_half : 1/2 ≤ r) :
    a ≤ gsC a b r ∧ gsC a b r ≤ gsD a b r ∧ gsD a b r ≤ b :=
  ⟨gsC_ge_a a b r hab hr1,
   gsC_le_gsD a b r hab hr_half,
   gsD_le_b a b r hab hr1⟩

/-! ## Midpoint containment -/

/-- The returned midpoint `(a + b) / 2` is always in `[a, b]`.

    This is guaranteed by the width bound: since `|b - a| ≤ tol` at termination,
    the midpoint is within `tol/2` of any contained point.

    Proof: `(a+b)/2 = (a+b) * (1/2)`. Since `a*(1/2) ≤ b*(1/2)` and
    `x = x*(1/2) + x*(1/2)` for any `x`, both bounds follow from monotonicity
    of `(· * (1/2))`. -/
theorem gs_midpoint_in_range (a b : Rat) (hab : a ≤ b) :
    a ≤ (a + b) / 2 ∧ (a + b) / 2 ≤ b := by
  have h2inv : (2:Rat)⁻¹ = 1/2 := by native_decide
  have hmul : a * (1/2) ≤ b * (1/2) :=
    Rat.mul_le_mul_of_nonneg_right hab (by native_decide)
  have hxx : ∀ x : Rat, x = x * (1/2) + x * (1/2) := fun x => by
    rw [← Rat.mul_add, show (1:Rat)/2 + 1/2 = 1 from by native_decide, Rat.mul_one]
  rw [Rat.div_def, h2inv, Rat.add_mul]
  constructor
  · calc a = a * (1/2) + a * (1/2) := hxx a
         _ ≤ a * (1/2) + b * (1/2) := Rat.add_le_add_left.mpr hmul
  · calc a * (1/2) + b * (1/2) ≤ b * (1/2) + b * (1/2) := Rat.add_le_add_right.mpr hmul
         _ = b := (hxx b).symm

/-! ## Concrete verification (golden ratio r = 618/1000 ≈ 1/φ) -/

-- Ordering invariants on [0, 10] with r = 618/1000
example : (0 : Rat) ≤ gsC 0 10 (618/1000) := by native_decide
example : gsD 0 10 (618/1000) ≤ (10 : Rat) := by native_decide
example : (0 : Rat) ≤ gsD 0 10 (618/1000) := by native_decide
example : gsC 0 10 (618/1000) ≤ gsD 0 10 (618/1000) := by native_decide

-- Width after b=d step: 10 * (618/1000) = 6.18
example : gsWidth 0 (gsD 0 10 (618/1000)) = 10 * (618/1000) := by native_decide
-- Width after a=c step (same!)
example : gsWidth (gsC 0 10 (618/1000)) 10 = 10 * (618/1000) := by native_decide

end PX4.GoldenSection
