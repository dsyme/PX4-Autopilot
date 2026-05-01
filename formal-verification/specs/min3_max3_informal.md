# Informal Specification: `math::min` and `math::max` (3-argument)

🔬 *Lean Squad automated formal verification.*

**Source**: `src/lib/mathlib/math/Limits.hpp`, lines 60–75
**Target ID**: 44

## Purpose

PX4's `math` namespace defines 3-argument overloads of `min` and `max`:

```cpp
template<typename _Tp>
constexpr _Tp min(_Tp a, _Tp b, _Tp c)
{
    return min(min(a, b), c);  // left-associative
}

template<typename _Tp>
constexpr _Tp max(_Tp a, _Tp b, _Tp c)
{
    return max(max(a, b), c);  // left-associative
}
```

These are utility functions used throughout PX4 for clamping, selecting
extremes, and ordering three values. They reduce to the 2-argument forms
applied left-associatively.

## Preconditions

- The type must support a total order (`<` comparison).
- No special preconditions on the values: all inputs are valid.

## Postconditions

### `min3(a, b, c)`

- **Lower bound**: the result is ≤ all three inputs (`result ≤ a`, `result ≤ b`, `result ≤ c`).
- **Greatest lower bound**: for any `x` with `x ≤ a`, `x ≤ b`, `x ≤ c`, we have `x ≤ result`.
- **Selection**: the result equals one of the three inputs (it is `a`, `b`, or `c`).
- **Idempotence**: `min3(a, a, a) = a`.

### `max3(a, b, c)`

- **Upper bound**: the result is ≥ all three inputs (`a ≤ result`, `b ≤ result`, `c ≤ result`).
- **Least upper bound**: for any `x` with `a ≤ x`, `b ≤ x`, `c ≤ x`, we have `result ≤ x`.
- **Selection**: the result equals one of the three inputs.
- **Idempotence**: `max3(a, a, a) = a`.

## Invariants

- **Symmetry**: `min3` and `max3` are symmetric in all three arguments
  (order of arguments does not affect the result).
  - The C++ implementation is left-associative: `min(min(a,b),c)`. By the
    associativity and commutativity of `min`, this is equivalent to any
    other permutation.
- **Duality**: `max3(a, b, c) = -min3(-a, -b, -c)` (and vice versa).
- **Relationship to 2-arg**: `min3(a,b,c) = min(a, min(b,c))` (by associativity).

## Edge Cases

- **All equal**: `min3(k, k, k) = max3(k, k, k) = k`.
- **Two equal**: e.g., `min3(a, a, b)` = `min(a, b)`.
- **Negative values**: no special handling; the order is total.
- **Min = Max**: if `a ≤ b` and `a ≤ c`, then `min3(a,b,c) = a`.

## Examples

| Input (a, b, c) | `min3` | `max3` |
|---|---|---|
| (1, 2, 3) | 1 | 3 |
| (3, 1, 2) | 1 | 3 |
| (2, 3, 1) | 1 | 3 |
| (-5, 0, 5) | -5 | 5 |
| (7, 7, 7) | 7 | 7 |
| (-3, -3, -1) | -3 | -1 |

## Open Questions

None — the semantics are completely determined by the C++ code and the
standard total order on the underlying type.

## Approach for Lean Spec

- Model over `Int` (unbounded integers): exact semantics for all integer types.
- Use `Int.min_le_left`, `Int.min_le_right`, `Int.le_min`, etc. from Lean 4 stdlib.
- All properties provable by composing 2-argument lemmas and `by omega`.
- Prove duality via a helper `neg_min` / `neg_max` lemma.
