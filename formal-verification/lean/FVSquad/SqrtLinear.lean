/-!
# math::sqrt_linear — Formal Verification

🔬 *Lean Squad automated formal verification.*

- **C++ source**: `src/lib/mathlib/math/Functions.hpp`
- **Informal spec**: `formal-verification/specs/sqrt_linear_informal.md`

## C++ reference

```cpp
template<typename T>
const T sqrt_linear(const T& value)
{
    if (value < static_cast<T>(0)) {
        return static_cast<T>(0);
    } else if (value < static_cast<T>(1)) {
        return sqrtf(value);
    } else {
        return value;
    }
}
```

## Three-branch piecewise structure

| Branch | Condition | Return |
|--------|-----------|--------|
| Negative | `value < 0` | `0` |
| Sqrt | `0 ≤ value < 1` | `sqrtf(value)` |
| Identity | `value ≥ 1` | `value` |

## Model

We model the function over `Rat` (rational numbers):

- **Negative branch** (`x < 0`): exact — returns `0`.
- **Identity branch** (`x ≥ 1`): exact — returns `x`.
- **Sqrt branch** (`0 ≤ x < 1`): abstracted via axiom `sqrtBranch`.
  `Real.sqrt` is not available in Lean 4 stdlib; theorems about this branch use `sorry`.

All theorems that concern only the negative or identity branch are proved without `sorry`.

## Approximations / Out of Scope

- **IEEE 754 float semantics**: NaN, infinity, and rounding are not modelled.
- **Sqrt branch**: `sqrtf` is axiomatised; any theorem requiring `sqrtf` properties
  (non-negativity, sub-1 bound, `sqrtf(0) = 0`) uses `sorry` until Mathlib is available.
- **Template parameter**: modelled as `Rat`; C++ `float` has additional rounding not
  captured here.
-/

namespace PX4.SqrtLinear

/-! ## Abstract sqrt model -/

/-- Abstract model for `sqrtf(x)` on `[0, 1)`.
    `Real.sqrt` is not available in Lean 4 stdlib; this is an opaque axiom.
    All theorems that depend on sqrt properties are sorry-guarded. -/
noncomputable axiom sqrtBranch : Rat → Rat

/-! ## Implementation model -/

/-- Lean model of `math::sqrt_linear<Rat>`.

    Matches the three-branch C++ implementation:
    - `x < 0`:   returns `0`
    - `0 ≤ x < 1`: returns `sqrtBranch x`  (models `sqrtf(x)`)
    - `x ≥ 1`:   returns `x` -/
noncomputable def sqrtLinear (x : Rat) : Rat :=
  if x < 0 then 0
  else if x < 1 then sqrtBranch x
  else x

/-! ## Sanity checks (as expressions: sqrtLinear is noncomputable due to sqrtBranch) -/

-- Identity branch: sqrtLinear x = x for x ≥ 1
-- e.g. sqrtLinear 1 = 1, sqrtLinear 2 = 2, sqrtLinear (5/2) = 5/2
-- Negative branch: sqrtLinear x = 0 for x < 0
-- e.g. sqrtLinear (-1) = 0, sqrtLinear (-3/2) = 0
-- Sqrt branch: sqrtLinear x = sqrtBranch x for 0 ≤ x < 1
-- e.g. sqrtLinear (1/4) = sqrtBranch (1/4)  [= 0.5 in the C++ float implementation]

/-! ## Negative branch: maps to zero -/

/-- For all `x < 0`, `sqrt_linear(x) = 0`.
    This is the first branch of the C++ implementation. -/
theorem sqrtLinear_neg (x : Rat) (h : x < 0) : sqrtLinear x = 0 := by
  simp [sqrtLinear, h]

/-- `sqrt_linear(-1) = 0`: concrete example. -/
theorem sqrtLinear_neg1 : sqrtLinear (-1) = 0 :=
  sqrtLinear_neg (-1) (by decide)

/-- `sqrt_linear(-3/2) = 0`: concrete example with rational input. -/
theorem sqrtLinear_neg_three_halves : sqrtLinear (-3/2) = 0 :=
  sqrtLinear_neg (-3/2) (by native_decide)

/-- For `x < 0`, the output is nonneg (trivially: output is 0). -/
theorem sqrtLinear_neg_nonneg (x : Rat) (h : x < 0) : 0 ≤ sqrtLinear x := by
  rw [sqrtLinear_neg x h]
  exact (by decide : (0 : Rat) ≤ 0)

/-! ## Identity branch: fixed points for x ≥ 1 -/

/-- For all `x ≥ 1`, `sqrt_linear(x) = x`.
    This is the third branch of the C++ implementation. -/
theorem sqrtLinear_ge_one (x : Rat) (h : 1 ≤ x) : sqrtLinear x = x := by
  simp only [sqrtLinear]
  have h0 : ¬ x < 0 := Rat.not_lt.mpr (Rat.le_trans (by decide) h)
  have h1 : ¬ x < 1 := Rat.not_lt.mpr h
  simp [h0, h1]

/-- `sqrt_linear(1) = 1`: the identity branch starts exactly at 1.
    This is a key boundary: both sqrt(1)=1 and identity(1)=1. -/
theorem sqrtLinear_one : sqrtLinear 1 = 1 :=
  sqrtLinear_ge_one 1 (by decide)

/-- `sqrt_linear(2) = 2`: concrete example in identity branch. -/
theorem sqrtLinear_two : sqrtLinear 2 = 2 :=
  sqrtLinear_ge_one 2 (by decide)

/-- `sqrt_linear(5/2) = 5/2`: rational input in identity branch. -/
theorem sqrtLinear_five_halves : sqrtLinear (5/2) = 5/2 :=
  sqrtLinear_ge_one (5/2) (by native_decide)

/-- For `x ≥ 1`, `sqrt_linear(x) ≥ 0`.
    Follows from the identity: result is `x`, and `x ≥ 1 > 0`. -/
theorem sqrtLinear_ge_one_nonneg (x : Rat) (h : 1 ≤ x) : 0 ≤ sqrtLinear x := by
  rw [sqrtLinear_ge_one x h]
  exact Rat.le_trans (by decide) h

/-- For `x ≥ 1`, `sqrt_linear(x) ≥ 1`.
    The identity branch preserves the `≥ 1` property. -/
theorem sqrtLinear_ge_one_ge_one (x : Rat) (h : 1 ≤ x) : 1 ≤ sqrtLinear x := by
  rw [sqrtLinear_ge_one x h]
  exact h

/-- Identity branch is monotone: `1 ≤ x ≤ y → sqrt_linear(x) ≤ sqrt_linear(y)`.
    Both sides equal their arguments; monotonicity follows directly. -/
theorem sqrtLinear_mono_ge_one (x y : Rat) (hx : 1 ≤ x) (hxy : x ≤ y) :
    sqrtLinear x ≤ sqrtLinear y := by
  rw [sqrtLinear_ge_one x hx, sqrtLinear_ge_one y (Rat.le_trans hx hxy)]
  exact hxy

/-- `sqrt_linear` is idempotent on `[1, ∞)`:
    applying it twice is the same as applying it once. -/
theorem sqrtLinear_idempotent_ge_one (x : Rat) (h : 1 ≤ x) :
    sqrtLinear (sqrtLinear x) = sqrtLinear x := by
  rw [sqrtLinear_ge_one x h, sqrtLinear_ge_one x h]

/-! ## Sqrt branch (sorry-guarded: requires Mathlib Real.sqrt) -/

/-- `sqrt_linear(0) = 0`: `sqrtf(0.0) = 0.0` by IEEE 754.

    Requires `sqrtBranch 0 = 0`.
    In Lean 4 with Mathlib: follows from `Real.sqrt_zero`. -/
theorem sqrtLinear_zero : sqrtLinear 0 = 0 := by
  simp only [sqrtLinear, if_neg (by decide : ¬(0 : Rat) < 0),
             if_pos (by decide : (0 : Rat) < 1)]
  sorry -- sqrtBranch 0 = 0; needs Real.sqrt_zero from Mathlib

/-- For `0 ≤ x < 1`, `sqrt_linear(x) ≥ 0`.

    Requires `0 ≤ sqrtBranch x` (i.e., `Real.sqrt x ≥ 0`).
    In Lean 4 with Mathlib: follows from `Real.sqrt_nonneg`. -/
theorem sqrtLinear_sqrt_nonneg (x : Rat) (h0 : 0 ≤ x) (h1 : x < 1) :
    0 ≤ sqrtLinear x := by
  simp only [sqrtLinear, if_neg (Rat.not_lt.mpr h0), if_pos h1]
  sorry -- 0 ≤ sqrtBranch x; needs Real.sqrt_nonneg from Mathlib

/-- For `0 < x < 1`, `sqrt_linear(x) < 1`.

    Requires `sqrtBranch x < 1` (i.e., `Real.sqrt x < 1` for `x ∈ (0,1)`).
    In Lean 4 with Mathlib: follows from `Real.sqrt_lt_one`. -/
theorem sqrtLinear_sqrt_lt_one (x : Rat) (h0 : 0 < x) (h1 : x < 1) :
    sqrtLinear x < 1 := by
  simp only [sqrtLinear, if_neg (Rat.not_lt.mpr (Rat.le_of_lt h0)), if_pos h1]
  sorry -- sqrtBranch x < 1; needs Real.sqrt_lt_one from Mathlib

end PX4.SqrtLinear
