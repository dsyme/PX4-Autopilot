/-!
# math::signNoZero — Formal Specification and Proofs

🔬 *Lean Squad automated formal verification.*

- **C++ source**: `src/lib/mathlib/math/Functions.hpp`
- **Informal spec**: `formal-verification/specs/signNoZero_informal.md`

## C++ Reference

```cpp
template<typename T>
int signNoZero(T val) {
    return (T(0) <= val) - (val < T(0));
}
```

`signNoZero` returns the sign of a value as `+1` or `-1`, treating zero as
positive.  Unlike the standard mathematical sign function (which returns 0 for
zero input), this variant guarantees the result is always ±1.  It is used as a
multiplier in control and normalisation contexts where 0 would be incorrect.

## Modelling Choices

- We model the function over `Int` (arbitrary-precision integers), which faithfully
  captures all signed integer instantiations including `int32_t`.
- Overflow is not an issue for `signNoZero` because the result is always -1 or 1.
- Floating-point instantiations are out of scope; `Int` suffices for the key properties.

## Verification Status

| Theorem | Status | Notes |
|---------|--------|-------|
| `signNoZero_nonneg` | ✅ proved | `0 ≤ v → signNoZero v = 1` |
| `signNoZero_neg` | ✅ proved | `v < 0 → signNoZero v = -1` |
| `signNoZero_zero` | ✅ proved | `signNoZero 0 = 1` |
| `signNoZero_range` | ✅ proved | `signNoZero v = 1 ∨ signNoZero v = -1` |
| `signNoZero_ne_zero` | ✅ proved | `signNoZero v ≠ 0` |
| `signNoZero_sq` | ✅ proved | `signNoZero v * signNoZero v = 1` |
| `signNoZero_natAbs` | ✅ proved | `(signNoZero v).natAbs = 1` |
| `signNoZero_neg_val` | ✅ proved | `v < 0 → signNoZero (-v) = 1` |
| `signNoZero_pos_val_neg` | ✅ proved | `0 < v → signNoZero (-v) = -1` |
| `signNoZero_mul_neg` | ✅ proved | `v ≠ 0 → signNoZero v * signNoZero (-v) = -1` |
-/

namespace PX4.SignNoZero

/-! ## Implementation model -/

/-- Lean model of `math::signNoZero<int>`.
    Returns 1 for `val ≥ 0`, -1 for `val < 0`.
    Matches the C++ formula `(0 <= val) - (val < 0)` exactly on `Int`. -/
def signNoZero (v : Int) : Int :=
  if 0 ≤ v then 1 else -1

/-! ## Correctness theorems -/

/-- For non-negative input, result is 1. -/
theorem signNoZero_nonneg (v : Int) (h : 0 ≤ v) : signNoZero v = 1 := by
  simp [signNoZero, h]

/-- For negative input, result is -1. -/
theorem signNoZero_neg (v : Int) (h : v < 0) : signNoZero v = -1 := by
  simp [signNoZero]
  omega

/-- At zero, result is 1 (zero treated as non-negative). -/
theorem signNoZero_zero : signNoZero 0 = 1 := by
  simp [signNoZero]

/-- Result is always in {-1, 1}. -/
theorem signNoZero_range (v : Int) : signNoZero v = 1 ∨ signNoZero v = -1 := by
  simp only [signNoZero]
  by_cases h : 0 ≤ v
  · left; simp [h]
  · right; simp [h]

/-- Result is never zero. -/
theorem signNoZero_ne_zero (v : Int) : signNoZero v ≠ 0 := by
  rcases signNoZero_range v with h | h <;> simp [h]

/-- Squaring the result always gives 1 (idempotence under multiplication). -/
theorem signNoZero_sq (v : Int) : signNoZero v * signNoZero v = 1 := by
  simp only [signNoZero]
  by_cases h : 0 ≤ v <;> simp [h]

/-- The natural absolute value of the result is always 1. -/
theorem signNoZero_natAbs (v : Int) : (signNoZero v).natAbs = 1 := by
  rcases signNoZero_range v with h | h <;> simp [h]

/-! ## Negation properties -/

/-- Negating a negative value gives a positive: `signNoZero(-v) = 1` when `v < 0`. -/
theorem signNoZero_neg_val (v : Int) (h : v < 0) : signNoZero (-v) = 1 := by
  apply signNoZero_nonneg
  omega

/-- Negating a positive value gives a negative: `signNoZero(-v) = -1` when `0 < v`. -/
theorem signNoZero_pos_val_neg (v : Int) (h : 0 < v) : signNoZero (-v) = -1 := by
  apply signNoZero_neg
  omega

/-- For any non-zero value, `signNoZero(v) * signNoZero(-v) = -1`.
    This captures the anti-symmetry: negating the input flips the sign. -/
theorem signNoZero_mul_neg (v : Int) (hv : v ≠ 0) :
    signNoZero v * signNoZero (-v) = -1 := by
  by_cases h : 0 ≤ v
  · -- v ≥ 0 and v ≠ 0 → -v < 0
    rw [signNoZero_nonneg v h, signNoZero_pos_val_neg v (by omega)]
    simp
  · -- v < 0 → -v ≥ 0
    have hlt : v < 0 := Int.not_le.mp h
    rw [signNoZero_neg v hlt, signNoZero_neg_val v hlt]
    simp

end PX4.SignNoZero
