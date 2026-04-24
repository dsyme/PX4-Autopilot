# Informal Specification: `math::sqrt_linear`

🔬 *Lean Squad automated formal verification.*

- **C++ source**: `src/lib/mathlib/math/Functions.hpp`
- **Lean file**: `formal-verification/lean/FVSquad/SqrtLinear.lean`

---

## Purpose

`sqrt_linear` is a piecewise scalar utility used in PX4's mathlib. It smoothly connects
a zero-output region (for negative inputs), a square-root curve (for inputs in [0, 1)),
and a linear identity (for inputs ≥ 1). This shape provides a "soft" nonlinear mapping
often used in sensor scaling and stick-response curves.

## C++ Signature

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

## Preconditions

- `value` is a finite floating-point or rational number.
- No special requirements; the function is total and well-defined for all inputs.

## Postconditions

The function has three branches:

| Condition | Return value | Notes |
|-----------|-------------|-------|
| `value < 0` | `0` | Zero-clamp for negative inputs |
| `0 ≤ value < 1` | `sqrtf(value)` | Square-root curve |
| `value ≥ 1` | `value` | Identity / linear |

## Key Invariants

1. **Non-negativity**: `sqrt_linear(x) ≥ 0` for all `x`.
2. **Monotonicity on [1, ∞)**: `sqrt_linear` is the identity on `[1, ∞)`, hence monotone.
3. **Fixed point at 1**: `sqrt_linear(1) = 1` (boundary between sqrt and identity branches).
4. **Fixed point at 0**: `sqrt_linear(0) = 0` (since `sqrtf(0) = 0`).
5. **Negative inputs collapse**: for `x ≤ 0`, `sqrt_linear(x) = 0`.
6. **Idempotence on [1, ∞)**: `sqrt_linear(sqrt_linear(x)) = sqrt_linear(x)` for `x ≥ 1`.
7. **Continuity at 1**: both sqrt and identity branches give `1` at `x = 1`.

## Edge Cases

- `value = 0`: falls in the `[0, 1)` branch; `sqrtf(0.0) = 0.0` by IEEE 754.
- `value = 1`: falls in the `x ≥ 1` branch; returns `1`.
- Very large negatives: always returns `0`.
- Very large positives: returns `value` (identity, no saturation).
- NaN: C++ comparison `NaN < 0` and `NaN < 1` both evaluate to `false`, so `NaN` input
  returns `NaN` (identity branch). This is not modelled in our Lean spec.

## Examples

| Input | Output | Branch |
|-------|--------|--------|
| -3/2 | 0 | negative |
| -1 | 0 | negative |
| 0 | 0 | sqrt (sqrtf(0) = 0) |
| 1/4 | 1/2 | sqrt (sqrtf(0.25) = 0.5) |
| 1 | 1 | identity |
| 2 | 2 | identity |
| 5/2 | 5/2 | identity |

## Formal Spec Summary (Lean propositions)

The Lean 4 file `SqrtLinear.lean` formalises the following key properties:

**Proved (no sorry):**
- `sqrtLinear_neg`: for `x < 0`, `sqrtLinear x = 0`
- `sqrtLinear_ge_one`: for `1 ≤ x`, `sqrtLinear x = x`
- `sqrtLinear_one`: `sqrtLinear 1 = 1`
- `sqrtLinear_neg_nonneg`: for `x < 0`, `0 ≤ sqrtLinear x`
- `sqrtLinear_ge_one_nonneg`: for `1 ≤ x`, `0 ≤ sqrtLinear x`
- `sqrtLinear_ge_one_ge_one`: for `1 ≤ x`, `1 ≤ sqrtLinear x`
- `sqrtLinear_mono_ge_one`: monotonicity on `[1, ∞)`
- `sqrtLinear_idempotent_ge_one`: `sqrt_linear(sqrt_linear(x)) = sqrt_linear(x)` for `x ≥ 1`

**Requires Mathlib (sorry-guarded):**
- `sqrtLinear_zero`: `sqrtLinear 0 = 0` (needs `Real.sqrt 0 = 0`)
- `sqrtLinear_sqrt_nonneg`: for `0 ≤ x < 1`, `0 ≤ sqrtLinear x` (needs `Real.sqrt ≥ 0`)
- `sqrtLinear_sqrt_lt_one`: for `0 < x < 1`, `sqrtLinear x < 1` (needs sqrt sub-1 bound)
- `sqrtLinear_sqrt_le`: for `0 ≤ x < 1`, `sqrtLinear x ≤ 1` (needs sqrt ≤ 1 for x ≤ 1)

## Open Questions

1. **NaN behaviour**: The C++ function inherits NaN propagation from IEEE 754 comparisons.
   The model does not address NaN; this is out of scope for a Rat-based model.
2. **Float rounding**: The model uses exact `Rat` arithmetic; `sqrtf` has ±0.5 ULP error.
3. **Continuity at x=0**: Both branches give 0 at x=0, but continuity of the sqrt branch
   at 0 is a real-analysis fact; it cannot be stated using `Rat` arithmetic.
