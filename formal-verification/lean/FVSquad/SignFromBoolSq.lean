/-!
# SignFromBool and Sq — Formal Verification

🔬 Lean Squad automated formal verification.

Models and proves correctness of two small utility functions from PX4 mathlib:

- `math::signFromBool` (src/lib/mathlib/math/Functions.hpp:63)
- `math::sq`           (src/lib/mathlib/math/Functions.hpp:69)

**Informal specs**: `formal-verification/specs/sign_from_bool_informal.md`
                    `formal-verification/specs/sq_informal.md`

No Mathlib dependency — Lean 4 standard library only.

## Correspondence

`signFromBool` is modelled **exactly**: `Bool → Int`, `true ↦ 1`, `false ↦ -1`.
No approximation needed; the input domain is finite ({true, false}).

`sq` is modelled for `Rat` (rationals) and `Int` (unbounded integers).
Integer overflow for fixed-width C++ types (e.g. `int16_t`) is **not modelled** —
the Lean model uses unbounded arithmetic. Float NaN/∞ is out of scope.
-/

namespace PX4.SignFromBoolSq

/-! ## `signFromBool`: Bool → {-1, +1}

C++ source (src/lib/mathlib/math/Functions.hpp:63):
```cpp
inline int signFromBool(bool positive)
{
    return positive ? 1 : -1;
}
```
The Lean model is an exact transcription of the C++ semantics.
-/

/-- Lean model of `math::signFromBool`. -/
def signFromBool (positive : Bool) : Int :=
  if positive then 1 else -1

/-- signFromBool(true) = 1 -/
theorem signFromBool_true : signFromBool true = 1 := by decide

/-- signFromBool(false) = -1 -/
theorem signFromBool_false : signFromBool false = -1 := by decide

/-- The result is never zero for any boolean input. -/
theorem signFromBool_ne_zero (b : Bool) : signFromBool b ≠ 0 := by
  rcases Bool.eq_false_or_eq_true b with hb | hb <;> simp [signFromBool, hb]

/-- The absolute value (natAbs) is always 1. -/
theorem signFromBool_natAbs (b : Bool) : (signFromBool b).natAbs = 1 := by
  rcases Bool.eq_false_or_eq_true b with hb | hb <;> simp [signFromBool, hb]

/-- signFromBool(b)² = 1: the result is a unit. -/
theorem signFromBool_sq (b : Bool) : signFromBool b * signFromBool b = 1 := by
  rcases Bool.eq_false_or_eq_true b with hb | hb <;> simp [signFromBool, hb]

/-- Negating the boolean negates the sign: signFromBool(!b) = -signFromBool(b). -/
theorem signFromBool_not (b : Bool) : signFromBool (!b) = -signFromBool b := by
  rcases Bool.eq_false_or_eq_true b with hb | hb <;> simp [signFromBool, hb]

/-- The range is exactly {-1, 1}: no other value is possible. -/
theorem signFromBool_range (b : Bool) : signFromBool b = 1 ∨ signFromBool b = -1 := by
  rcases Bool.eq_false_or_eq_true b with hb | hb <;> simp [signFromBool, hb]

example : signFromBool true  = 1  := by decide
example : signFromBool false = -1 := by decide

/-! ## `sq`: squaring function

C++ source (src/lib/mathlib/math/Functions.hpp:69):
```cpp
template<typename T>
T sq(T val)
{
    return val * val;
}
```

We model `sq` for `Rat` (exact rationals) and `Int` (unbounded integers).
Fixed-width integer overflow (e.g. `int16_t`) and float NaN/∞ are out of scope.
-/

/-- Lean model of `math::sq` for rational numbers. -/
def sqRat (x : Rat) : Rat := x * x

/-- Lean model of `math::sq` for integers (unbounded — no overflow). -/
def sqInt (x : Int) : Int := x * x

/-- sq(0 : Rat) = 0 -/
theorem sqRat_zero : sqRat 0 = 0 := by native_decide

/-- sq(1 : Rat) = 1 -/
theorem sqRat_one : sqRat 1 = 1 := by native_decide

/-- sq(-1 : Rat) = 1 -/
theorem sqRat_neg_one : sqRat (-1) = 1 := by native_decide

/-- sq is always non-negative for Rat. -/
theorem sqRat_nonneg (x : Rat) : 0 ≤ sqRat x := by
  simp only [sqRat]
  by_cases hx : 0 ≤ x
  · exact Rat.mul_nonneg hx hx
  · have hx0 : x ≤ 0 := Rat.le_of_lt (Rat.not_le.mp hx)
    have hn : 0 ≤ -x := by
      have := Rat.neg_le_neg hx0
      rwa [Rat.neg_zero] at this
    have := Rat.mul_nonneg hn hn
    rwa [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg] at this

/-- sq is an even function: sq(-x) = sq(x) for Rat. -/
theorem sqRat_even (x : Rat) : sqRat (-x) = sqRat x := by
  simp only [sqRat, Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]

/-- sq(x) = 0 if and only if x = 0 for Rat.
    (Non-zero rationals always have a positive square.) -/
theorem sqRat_eq_zero_iff (x : Rat) : sqRat x = 0 ↔ x = 0 := by
  simp only [sqRat, Rat.mul_eq_zero]
  constructor
  · intro h
    exact h.elim id id
  · intro h
    left; exact h

/-- sq(x * y) = sq(x) * sq(y): multiplicativity for Rat. -/
theorem sqRat_mul (x y : Rat) : sqRat (x * y) = sqRat x * sqRat y := by
  simp only [sqRat]
  calc x * y * (x * y)
      = x * (y * (x * y)) := Rat.mul_assoc x y (x * y)
    _ = x * (y * x * y)   := by rw [← Rat.mul_assoc y x y]
    _ = x * (x * y * y)   := by rw [Rat.mul_comm y x]
    _ = x * (x * (y * y)) := by rw [Rat.mul_assoc x y y]
    _ = x * x * (y * y)   := (Rat.mul_assoc x x (y * y)).symm

/-- sq(0 : Int) = 0 -/
theorem sqInt_zero : sqInt 0 = 0 := by decide

/-- sq is always non-negative for Int. -/
theorem sqInt_nonneg (x : Int) : 0 ≤ sqInt x := by
  simp only [sqInt]
  by_cases hx : 0 ≤ x
  · exact Int.mul_nonneg hx hx
  · have hx0 : x ≤ 0 := Int.le_of_lt (Int.not_le.mp hx)
    have hn : 0 ≤ -x := Int.neg_nonneg.mpr hx0
    have := Int.mul_nonneg hn hn
    rwa [Int.neg_mul_neg] at this

/-- sq is an even function for Int: sq(-x) = sq(x). -/
theorem sqInt_even (x : Int) : sqInt (-x) = sqInt x := by
  simp only [sqInt, Int.neg_mul_neg]

/-- Concrete examples for sq (Rat). -/
example : sqRat (3/2 : Rat) = 9/4  := by native_decide
example : sqRat (0   : Rat) = 0    := by native_decide
example : sqRat (-5  : Rat) = 25   := by native_decide

end PX4.SignFromBoolSq
