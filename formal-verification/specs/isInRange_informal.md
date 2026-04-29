# Informal Specification: `math::isInRange`

🔬 *Lean Squad — automated formal verification.*

**Source**: `src/lib/mathlib/math/Limits.hpp`, line 91

## C++ Source

```cpp
template<typename _Tp>
constexpr bool isInRange(_Tp val, _Tp min_val, _Tp max_val)
{
    return (min_val <= val) && (val <= max_val);
}
```

## Purpose

`isInRange` tests whether a value `val` lies within the **closed interval**
`[min_val, max_val]`, i.e. satisfies `min_val ≤ val ≤ max_val`.

It is a generic predicate used throughout PX4 for range-checking sensor readings,
control outputs, parameter bounds, and safety limits.

## Preconditions

- `_Tp` must be a type with a total linear order and `<=` operator (integer, float, double, etc.).
- No specific numeric range is required; the check is purely relational.
- **Float semantics**: when `_Tp = float`, NaN comparisons return `false` by IEEE 754,
  so `isInRange(NaN, min, max)` returns `false` regardless of the bounds.

## Postconditions

| Condition | Result |
|-----------|--------|
| `min_val ≤ val` and `val ≤ max_val` | `true` |
| `val < min_val` | `false` |
| `max_val < val` | `false` |
| `min_val > max_val` (empty interval) | `false` |

## Invariants

- **Reflexive**: `isInRange(v, v, v)` is always `true` (every value is in its own
  singleton interval).
- **Monotone in bounds**: if `isInRange(v, lo, hi)` is `true` and `lo' ≤ lo` and
  `hi ≤ hi'`, then `isInRange(v, lo', hi')` is also `true`.
- **Shift invariant**: `isInRange(v + d, lo + d, hi + d) = isInRange(v, lo, hi)` for
  all offsets `d`.
- **Symmetric range**: `isInRange(v, -r, r)` iff `|v| ≤ r`.

## Edge Cases

- **Empty interval** (`max_val < min_val`): returns `false` for all `val`, since no
  `val` can simultaneously satisfy `min_val ≤ val ≤ max_val`.
- **Singleton interval** (`min_val == max_val == c`): returns `true` iff `val == c`.
- **Exact boundary**: returns `true` at both `min_val` and `max_val` (closed interval).
- **NaN input (float)**: comparisons with NaN produce `false`, so `isInRange(NaN, ...)
  = false`.

## Examples

```
isInRange(5,   0,  10) = true     -- interior point
isInRange(0,   0,  10) = true     -- at lower bound
isInRange(10,  0,  10) = true     -- at upper bound
isInRange(-1,  0,  10) = false    -- below lower bound
isInRange(11,  0,  10) = false    -- above upper bound
isInRange(5,   5,   5) = true     -- singleton interval
isInRange(4,   5,   5) = false    -- outside singleton
isInRange(5,  10,   0) = false    -- empty interval (max < min)
```

## Inferred Intent

The function is a thin, readable wrapper around two comparison operators. Its
primary purpose is to make range-checking intent explicit and avoid
accidentally writing open intervals or misremembering operator direction.

Because it is `constexpr`, it can be used in compile-time assertions and
template-parameter bounds as well as at runtime.

## Open Questions

1. **NaN behaviour for float**: callers may assume `isInRange` returns `false` for NaN
   inputs. Is this documented as a contract or merely an IEEE 754 side effect?
2. **`min_val > max_val`**: is the empty-interval case considered a programmer error,
   or is returning `false` the specified behaviour?
