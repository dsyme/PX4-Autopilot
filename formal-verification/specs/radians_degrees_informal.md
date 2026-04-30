# Informal Specification: `math::radians` / `math::degrees`

🔬 *Lean Squad automated formal verification.*

**Source file**: `src/lib/mathlib/math/Limits.hpp` (lines 97–106)

## C++ Reference

```cpp
template<typename T>
constexpr T radians(T degrees)
{
    return degrees * (static_cast<T>(MATH_PI) / static_cast<T>(180));
}

template<typename T>
constexpr T degrees(T radians)
{
    return radians * (static_cast<T>(180) / static_cast<T>(MATH_PI));
}
```

where `MATH_PI ≈ 3.14159265358979323846` (a `double` constant defined in `<math.h>`).

## Purpose

`radians` converts an angle expressed in degrees to an equivalent angle in radians
by multiplying by the factor `π/180`.

`degrees` converts an angle expressed in radians to an equivalent angle in degrees
by multiplying by the factor `180/π`.

They are used extensively throughout PX4's attitude, navigation, and control modules
wherever angle units must be converted — e.g. user-facing parameters (in degrees) are
converted to internal representation (in radians) before being fed to the EKF, control
loops, and trigonometric functions.

## Preconditions

- `x` (the input) is a finite, non-NaN value of the template type `T`.
- For the **round-trip** property, `T` must support exact arithmetic; over `float`
  or `double`, floating-point rounding makes `degrees(radians(x))` only approximately
  equal to `x`.
- The abstract parameter `π` must be **non-zero** (trivially satisfied for any
  representation of π).

## Postconditions

1. **Fixed point at zero**: `radians(0) = 0` and `degrees(0) = 0`.
2. **Linearity (additivity)**: `radians(a + b) = radians(a) + radians(b)`.
3. **Linearity (scaling)**: `radians(k * x) = k * radians(x)`.
4. **Monotone**: `a ≤ b → radians(a) ≤ radians(b)` (holds because `π/180 > 0`).
5. **Sign preservation**: `sign(radians(x)) = sign(x)` (since `π/180 > 0`).
6. **Round-trip (in exact arithmetic)**:
   - `degrees(radians(x)) = x` for all `x`.
   - `radians(degrees(x)) = x` for all `x`.
7. **Specific values**:
   - `radians(180) = π`
   - `radians(360) = 2π`
   - `radians(90) = π/2`
   - `radians(-180) = -π`
   - `degrees(π) = 180`
   - `degrees(π/2) = 90`
   - `degrees(2π) = 360`

## Invariants

- Both functions are **linear maps** over any ordered field: they scale all inputs by
  a positive constant.
- Because the scaling factor is positive, both functions are **strictly monotone** and
  hence **injective**.
- The two functions are **mutual inverses** in exact arithmetic.
- Neither function clamps, wraps, or otherwise bounds the output — the output range
  is `(-∞, +∞)`, and inputs outside `[0°, 360°]` / `[0, 2π]` are handled correctly
  by simple scaling.

## Edge Cases

| Input | `radians` result | `degrees` result |
|-------|-----------------|-----------------|
| `0` | `0` | `0` |
| `180` | `π` | (n/a) |
| `-180` | `-π` | (n/a) |
| `360` | `2π` | (n/a) |
| `π` | (n/a) | `180` |
| `-π` | (n/a) | `-180` |
| `2π` | (n/a) | `360` |
| very large `x` | scales proportionally | scales proportionally |
| NaN | NaN (fp propagation) | NaN (fp propagation) |

## Inferred Intent

These functions are the standard unit-conversion utilities for angle arithmetic.  The
`constexpr` qualifier means they are evaluated at compile time when called with literal
arguments, which is important for constant-folded sensor calibration offsets and
pre-computed control-law coefficients.

The design choice to use a plain multiplicative scaling (rather than a modular
arithmetic approach like `wrap_pi`) implies that:
- The functions are intentionally **not** restricted to canonical angle ranges.
- Callers are responsible for range normalisation if needed.
- Both functions are pure and have no side effects.

## Lean Modelling Approach

Because the exact value of `π` is irrational, we model it as an **abstract parameter**
`pi : ℚ` with the single axiom `pi_pos : pi > 0`.  Under this abstraction:

- `radians (x : ℚ) : ℚ := x * (pi / 180)`
- `degrees (x : ℚ) : ℚ := x * (180 / pi)`

The round-trip property `degrees (radians x) = x` reduces to the algebraic identity
`(x * (pi / 180)) * (180 / pi) = x`, which holds by `field_simp` (using `pi ≠ 0`
from `pi_pos`).  Linearity, monotonicity, and sign properties follow from `pi_pos`
alone with `linarith` / `ring`.

Floating-point rounding is **not** modelled; the Lean spec captures the mathematical
(exact-arithmetic) semantics only.

## Open Questions

- **Floating-point exactness**: over `float`, `radians(180.0f)` is not exactly `M_PI`
  — it differs by a few ULPs.  The round-trip `degrees(radians(x))` accumulates two
  rounding errors.  Should the Lean spec state approximate versions of these properties
  using `|result - expected| ≤ ε`?  For now the spec targets exact rational arithmetic.
- **`MATH_PI` vs `M_PI`**: PX4 uses its own `MATH_PI` constant (defined in
  `src/lib/mathlib/mathlib.h`).  The value is identical to the system `M_PI` on most
  platforms, but this is platform-dependent.
- **Integer `T`**: with `T = int`, the C++ expression `MATH_PI / 180` rounds to `0`
  at compile time, making both functions return `0` for all inputs — a silent bug for
  integer callers.  The Lean model over `ℚ` does not exhibit this behaviour; this
  discrepancy should be flagged for integer callers.

## Examples

```
radians(0)    = 0
radians(180)  = π   ≈ 3.14159265
radians(90)   = π/2 ≈ 1.57079633
radians(360)  = 2π  ≈ 6.28318530
radians(-180) = -π  ≈ -3.14159265

degrees(0)    = 0
degrees(π)    = 180
degrees(π/2)  = 90
degrees(2π)   = 360
degrees(-π)   = -180

degrees(radians(45))  = 45   (round-trip)
radians(degrees(1.0)) = 1.0  (round-trip)
```
