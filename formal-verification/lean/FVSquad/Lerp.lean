/-!
# PX4 `lerp` Function — Formal Verification

🔬 Lean Squad automated formal verification.

This file models and proves correctness properties of `math::lerp` from
PX4-Autopilot's `mathlib`:

- **C++ source**: `src/lib/mathlib/math/Functions.hpp` (approx. line 127)
- **Informal spec**: `formal-verification/specs/lerp_informal.md`

## C++ Reference

```cpp
/**
 * Linear interpolation between two values.
 * s=0 returns a
 * s=1 returns b
 * Any value for s is valid.
 */
template<typename T>
const T lerp(const T &a, const T &b, const T &s)
{
    return (static_cast<T>(1) - s) * a + s * b;
}
```

`lerp` is used throughout PX4 for flight-task setpoint blending, RC stick
processing, and gain scheduling.

## Model

We model the function over `Rat` (rational numbers) for exact arithmetic.
The C++ template uses `float`/`double`; the Lean model is a faithful rational
abstraction capturing all algebraic properties.

```
lerpRat a b s := (1 - s) * a + s * b
```

## Approximations / Out of Scope

- **IEEE 754 float semantics**: NaN, infinity, and rounding errors are not
  modelled.  `lerp(a, b, 0.0f)` may not exactly equal `a` in hardware when
  `b = NaN` or `b = ±∞`.
- **Integer overflow**: the generic template works for integer `T` but truncation
  of `(1 - s) * a` is not modelled.
- **Out-of-range s**: extrapolation (s < 0 or s > 1) is valid per C++ comment
  but range theorems only apply for s ∈ [0, 1].

## Theorems Summary

| Theorem | Description | Proof status |
|---------|-------------|-------------|
| `lerp_zero` | `lerp(a, b, 0) = a` | ✅ Proved |
| `lerp_one` | `lerp(a, b, 1) = b` | ✅ Proved |
| `lerp_const` | `lerp(a, a, s) = a` | ✅ Proved |
| `lerp_alt_form` | `lerp(a,b,s) = a + s*(b-a)` | ✅ Proved |
| `lerp_lower` | `s ∈ [0,1] ∧ a ≤ b → a ≤ lerp(a,b,s)` | ✅ Proved |
| `lerp_upper` | `s ∈ [0,1] ∧ a ≤ b → lerp(a,b,s) ≤ b` | ✅ Proved |
| `lerp_in_range` | Range containment (combines lower + upper) | ✅ Proved |
| `lerp_comm` | `lerp(a,b,s) = lerp(b,a,1-s)` | ✅ Proved |
| `lerp_mono_s` | Monotone in s when a ≤ b | ✅ Proved |
| `lerp_half` | `lerp(a,b,½) = (a+b)/2` | ✅ Proved |

-/

namespace PX4.Lerp

/-- Pure functional model of `math::lerp` over `Rat`.

    Exact match of the C++ formula `(1 - s) * a + s * b`. -/
def lerpRat (a b s : Rat) : Rat := (1 - s) * a + s * b

/-! ## Concrete examples (sanity checks) -/

#eval lerpRat 0 10 0       -- 0    (s=0: pure a)
#eval lerpRat 0 10 1       -- 10   (s=1: pure b)
#eval lerpRat 0 10 (1/2)   -- 5    (midpoint)
#eval lerpRat 0 10 (1/4)   -- 5/2  (quarter)
#eval lerpRat (-5) 5 (1/2) -- 0    (midpoint of symmetric range)
#eval lerpRat 3 3 (7/5)    -- 3    (const, any s)

/-! ## Boundary theorems -/

/-- At blend parameter 0, result is exactly `a`. -/
theorem lerp_zero (a b : Rat) : lerpRat a b 0 = a := by
  unfold lerpRat
  rw [Rat.sub_eq_add_neg (1 : Rat) 0, Rat.neg_zero, Rat.add_zero,
      Rat.one_mul, Rat.zero_mul, Rat.add_zero]

/-- At blend parameter 1, result is exactly `b`. -/
theorem lerp_one (a b : Rat) : lerpRat a b 1 = b := by
  unfold lerpRat
  rw [Rat.sub_self, Rat.zero_mul, Rat.zero_add, Rat.one_mul]

/-- When both endpoints are the same, result is always that value regardless of `s`. -/
theorem lerp_const (a s : Rat) : lerpRat a a s = a := by
  unfold lerpRat
  rw [← Rat.add_mul, Rat.sub_add_cancel, Rat.one_mul]

/-! ## Alternative form -/

/-- Alternative form: `lerp(a, b, s) = a + s * (b - a)`.

    Useful for reasoning about the "offset from a" interpretation:
    `lerp` moves from `a` by fraction `s` of the gap `(b - a)`. -/
theorem lerp_alt_form (a b s : Rat) : lerpRat a b s = a + s * (b - a) := by
  simp only [lerpRat, Rat.sub_eq_add_neg, Rat.add_mul, Rat.mul_add, Rat.neg_mul, Rat.mul_neg,
             Rat.one_mul, Rat.add_comm, Rat.add_left_comm]

/-! ## Convexity / range theorems -/

/-- When `a ≤ b` and `s ∈ [0, 1]`, the result is at least `a` (lower bound). -/
theorem lerp_lower (a b s : Rat) (hs0 : 0 ≤ s) (_hs1 : s ≤ 1) (hab : a ≤ b) :
    a ≤ lerpRat a b s := by
  show a ≤ (1 - s) * a + s * b
  calc a = (1 - s) * a + s * a := by rw [← Rat.add_mul, Rat.sub_add_cancel, Rat.one_mul]
       _ ≤ (1 - s) * a + s * b :=
             Rat.add_le_add_left.mpr (Rat.mul_le_mul_of_nonneg_left hab hs0)

/-- When `a ≤ b` and `s ∈ [0, 1]`, the result is at most `b` (upper bound). -/
theorem lerp_upper (a b s : Rat) (_hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hab : a ≤ b) :
    lerpRat a b s ≤ b := by
  show (1 - s) * a + s * b ≤ b
  have h1s : 0 ≤ (1 : Rat) - s := (Rat.le_iff_sub_nonneg s 1).mp hs1
  calc (1 - s) * a + s * b
      ≤ (1 - s) * b + s * b :=
             Rat.add_le_add_right.mpr (Rat.mul_le_mul_of_nonneg_left hab h1s)
    _ = b := by rw [← Rat.add_mul, Rat.sub_add_cancel, Rat.one_mul]

/-- Combined range theorem: when `a ≤ b` and `s ∈ [0, 1]`, output is in `[a, b]`.

    This is the key safety property: `lerp` cannot overshoot its endpoints
    when the blend parameter is in the unit interval. -/
theorem lerp_in_range (a b s : Rat) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hab : a ≤ b) :
    a ≤ lerpRat a b s ∧ lerpRat a b s ≤ b :=
  ⟨lerp_lower a b s hs0 hs1 hab, lerp_upper a b s hs0 hs1 hab⟩

/-! ## Symmetry -/

/-- `lerp(a, b, s) = lerp(b, a, 1 - s)`: swapping endpoints requires swapping the
    blend parameter about ½ as well. -/
theorem lerp_comm (a b s : Rat) : lerpRat a b s = lerpRat b a (1 - s) := by
  unfold lerpRat
  have h1 : (1 : Rat) - (1 - s) = s := by
    rw [Rat.sub_eq_add_neg, Rat.neg_sub, Rat.add_comm, Rat.sub_add_cancel]
  rw [h1]
  exact Rat.add_comm _ _

/-! ## Monotonicity -/

/-- `lerp(a, b, -)` is monotone non-decreasing in the blend parameter when `a ≤ b`.

    Moving `s` from `s₁` toward `s₂` (s₁ ≤ s₂) shifts the result from `a` toward
    `b`.  This property is critical for setpoint ramp / rate-limiting uses in PX4. -/
theorem lerp_mono_s (a b s1 s2 : Rat) (hab : a ≤ b) (hs : s1 ≤ s2) :
    lerpRat a b s1 ≤ lerpRat a b s2 := by
  rw [lerp_alt_form a b s1, lerp_alt_form a b s2]
  apply Rat.add_le_add_left.mpr
  exact Rat.mul_le_mul_of_nonneg_right hs ((Rat.le_iff_sub_nonneg a b).mp hab)

/-! ## Midpoint -/

/-- At blend parameter ½, result is the arithmetic mean `(a + b) / 2`. -/
theorem lerp_half (a b : Rat) : lerpRat a b (1 / 2) = (a + b) / 2 := by
  unfold lerpRat
  have h1 : (1 : Rat) - 1 / 2 = 1 / 2 := by native_decide
  rw [h1, ← Rat.mul_add, Rat.mul_comm]
  simp only [Rat.div_def, Rat.one_mul]

end PX4.Lerp
