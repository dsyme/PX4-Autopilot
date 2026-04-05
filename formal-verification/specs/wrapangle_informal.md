# Informal Specification: `wrap_pi` / `wrap` Angle Wrapping

🔬 *Lean Squad automated formal verification.*

**C++ source**: `src/lib/matrix/matrix/helper_functions.hpp`
**Used in**: flight tasks, EKF, fixed-wing wheel controller, orbit following, attitude estimation.

---

## Purpose

`wrap_pi(x)` maps an angle `x` (in radians) to the equivalent angle in the half-open
interval `[-π, π)`. `wrap_2pi(x)` does the same for `[0, 2π)`. The generic `wrap(x, low, high)`
performs the same reduction for any interval `[low, high)` with `low < high`.

These are used wherever angle arithmetic can drift outside the "canonical" range — e.g.,
after heading integration, delta-heading computation, or yaw setpoint accumulation.

There are two implementations:
- **Floating-point** (`wrap_floating`): uses `std::floor` for continuous types.
- **Integer** (`wrap<Integer>`): uses integer division and `%` for discrete types.

---

## Preconditions

- **`wrap_floating(x, low, high)`**: `low < high`, and `x` is a finite (non-NaN, non-∞)
  floating-point value. If `x` is NaN or ±∞, `std::floor((x-low)/range)` is undefined
  (NaN), and the result is unspecified.
- **`wrap<Integer>(x, low, high)`**: `low < high` and `range = high - low > 0`. No
  integer overflow (undefined behaviour if `range` overflows the integer type).
- **`wrap_pi(x)`**: `x` is finite (not NaN or ±∞).

---

## Postconditions

### Range containment (core contract)
- `low ≤ wrap(x, low, high) < high` for all valid inputs.
- For `wrap_pi`: `-π ≤ wrap_pi(x) < π`.
- For `wrap_2pi`: `0 ≤ wrap_2pi(x) < 2π`.

### Identity in range
- If `low ≤ x < high`, then `wrap(x, low, high) = x` (no modification needed).

### Idempotence
- `wrap(wrap(x, low, high), low, high) = wrap(x, low, high)`.
- Corollary: `wrap_pi(wrap_pi(x)) = wrap_pi(x)`.

### Periodicity
- `wrap(x + k*(high - low), low, high) = wrap(x, low, high)` for any integer `k`.
- Corollary: `wrap_pi(x + 2πk) = wrap_pi(x)` for any integer `k`.

### Congruence
- `wrap(x, low, high) ≡ x  (mod high - low)`.
- That is, `∃ k : ℤ, wrap(x, low, high) = x + k * (high - low)`.
- Corollary for angle arithmetic: if `a ≡ b (mod 2π)`, then `wrap_pi(a) = wrap_pi(b)`.

---

## Invariants

- The result is always in the half-open interval `[low, high)`. The upper endpoint is
  **exclusive**: `wrap_pi(π) = -π`, not `π`.
- The result differs from the input by an exact multiple of the period `(high - low)`.
  This is essential for correctness in contexts that compute *angular differences*:
  `wrap_pi(a) - wrap_pi(b)` may differ from `a - b` by a multiple of `2π`, but
  `wrap_pi(a - b)` gives the "shortest arc" distance.

---

## Edge Cases

| Input | Expected output | Notes |
|-------|----------------|-------|
| `x` already in `[-π, π)` | `x` | Identity |
| `x = π` | `-π` | Upper bound exclusive |
| `x = -π` | `-π` | Lower bound inclusive |
| `x = 0` | `0` | Zero preserved |
| `x = 2π` | `0` | Exact period reduction |
| `x = -2π` | `0` | Negative period reduction |
| `x = 1.5π` | `-0.5π` | Positive overflow |
| `x = -1.5π` | `0.5π` | Negative overflow |
| `x = NaN` | Undefined | C++ UB; `std::floor(NaN) = NaN` |
| `x = ±∞` | Undefined | C++ UB; `std::floor(±∞) = ±∞` |
| `low ≥ high` | Undefined | Division by zero or empty range |

---

## Examples

```
wrap_pi( 0.5π)  =  0.5π    (already in range)
wrap_pi(-0.5π)  = -0.5π    (already in range)
wrap_pi( 1.5π)  = -0.5π    (subtract 2π)
wrap_pi(-1.5π)  =  0.5π    (add 2π)
wrap_pi( π   )  = -π        (upper bound exclusive: π is NOT in [-π, π))
wrap_pi(-π   )  = -π        (lower bound inclusive: -π is in range)
wrap_pi( 3π  )  = -π        (subtract 2π twice? No: 3π - 2π = π → not in range;
                              3π - 4π = -π → in range)
wrap_pi( 4π  )  =  0        (subtract 2·2π)
```

Integer example (`wrap<int>(x, -3, 3)`, period 6):
```
wrap(-7, -3, 3) = -1     (-7 + 6 = -1, in [-3,3))
wrap(-4, -3, 3) = 2      (-4 + 6 = 2, in [-3,3))
wrap( 0, -3, 3) = 0      (already in range)
wrap( 3, -3, 3) = -3     (3 is the exclusive upper bound; 3 - 6 = -3)
```

---

## Inferred Intent

The function exists to keep angle representations in a canonical form, preventing
unbounded accumulation of angle values and ensuring that angular comparisons and
differences produce meaningful results. The half-open convention `[low, high)` (not
`[-π, π]`) ensures uniqueness: every real number has exactly one equivalent in the range.

The choice of `[-π, π)` (not `(-π, π]`) is conventional in aerospace and robotics.
The consequence is that `π` and `-π` represent the same heading, but `π` is normalised
to `-π`. Callers that compare `|wrap_pi(x)| < threshold` for some threshold near `π`
should be aware that the threshold check is symmetric and the comparison is well-formed.

---

## Open Questions

1. **NaN behaviour**: Should `wrap_pi` explicitly check for NaN and return 0 or NaN?
   The current C++ silently propagates undefined behaviour. Callers in the EKF and flight
   tasks do not guard against NaN inputs.

2. **unwrap_pi correctness**: The `unwrap_pi` function uses `wrap` to compute delta
   headings. Its correctness property — `unwrap_pi(last, new) - last ≡ new (mod 2π)` —
   follows from `wrapInt_congruent` applied to `new - last`. Should this also be formally
   verified?

3. **`wrap_pi` vs `wrap_2pi` coherence**: `wrap_2pi(x) = wrap_pi(x - π) + π` (or similar).
   Formalising this relationship would allow proofs about `wrap_2pi` to reuse `wrap_pi`
   lemmas.
