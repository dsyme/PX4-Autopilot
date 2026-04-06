# Informal Specification: `math::lerp`

🔬 *Lean Squad automated formal verification.*

**Source file**: `src/lib/mathlib/math/Functions.hpp` (approx. line 127)

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

## Purpose

`lerp` computes a weighted blend between two values `a` and `b` using a blend
parameter `s`.  It is the standard linear interpolation formula:

```
lerp(a, b, s) = (1 - s) * a + s * b
```

When `s = 0`, the result is `a`; when `s = 1`, the result is `b`.  For `s ∈ [0, 1]`,
the result lies in the convex hull `[min(a,b), max(a,b)]`.

## Preconditions

- `a`, `b`, `s` are finite, non-NaN floating-point (or integer/rational) values.
- No specific constraint on `s` — the C++ code notes "any value for s is valid".
- For the **convexity** and **range** properties, `s ∈ [0, 1]` is required.
- For the **ordered range** property, `a ≤ b` is required.

## Postconditions

1. **Boundary at 0**: `lerp(a, b, 0) = a`
2. **Boundary at 1**: `lerp(a, b, 1) = b`
3. **Constant blend**: `lerp(a, a, s) = a` for all `s`
4. **Lower bound** (when `a ≤ b`, `s ∈ [0, 1]`): `a ≤ lerp(a, b, s)`
5. **Upper bound** (when `a ≤ b`, `s ∈ [0, 1]`): `lerp(a, b, s) ≤ b`
6. **Symmetry**: `lerp(a, b, s) = lerp(b, a, 1 - s)`
7. **Monotone in s** (when `a ≤ b`): `s₁ ≤ s₂ → lerp(a,b,s₁) ≤ lerp(a,b,s₂)`
8. **Alternative form**: `lerp(a, b, s) = a + s * (b - a)`

## Invariants

- The function is a linear function of each argument separately.
- For `s ∈ [0, 1]` and `a ≤ b`: output is in `[a, b]` — no overshoot.
- Monotone non-decreasing in `s` when `a ≤ b`.

## Edge Cases

| Input | Expected | Reason |
|-------|----------|--------|
| `s = 0` | `a` | Pure `a` |
| `s = 1` | `b` | Pure `b` |
| `s = 1/2` | `(a + b) / 2` | Midpoint |
| `a = b` | `a` for any `s` | Constant |
| `s < 0` | extrapolates below `a` (when `a ≤ b`) | Out-of-range `s` |
| `s > 1` | extrapolates above `b` (when `a ≤ b`) | Out-of-range `s` |

## Inferred Intent

The function is used throughout PX4 for:

- **Flight task setpoint blending**: smooth transitions between hover/forward-flight
  attitude targets.
- **RC stick processing**: expo curves that blend raw and cubed inputs.
- **Gain scheduling**: interpolation between control gains across flight envelopes.

The comment "Any value for s is valid" indicates the implementation deliberately
allows extrapolation (s outside [0,1]) for these use cases.  The convexity
invariant only applies when s ∈ [0, 1].

## Open Questions

- **Float rounding**: in IEEE 754, `lerp(a, b, 0.0f)` may not exactly equal `a`
  (e.g. if `b` is ±∞ or NaN).  The Lean model over `Rat` avoids this issue but
  cannot represent the real C++ floating-point behaviour.
- **Integer types**: the generic template is not specialised for integer `T`; integer
  division is not used here, but callers using integer `T` should be aware that
  `(1 - s) * a` truncates.

## Examples

```
lerp(0, 10, 0.0) = 0
lerp(0, 10, 1.0) = 10
lerp(0, 10, 0.5) = 5.0
lerp(0, 10, 0.25) = 2.5
lerp(-5, 5, 0.5) = 0.0
lerp(a, b, s) = lerp(b, a, 1 - s)   (symmetry)
```
