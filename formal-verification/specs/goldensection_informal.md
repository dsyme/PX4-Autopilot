# Informal Specification: `math::goldensection`

🔬 Lean Squad automated formal verification.

**Source**: `src/lib/mathlib/math/SearchMin.hpp:56–81`

---

## Purpose

`goldensection` implements the **golden-section search** algorithm, which finds the
x-value of the minimum of a unimodal function `f` over the interval `[arg1, arg2]`
to within tolerance `tol`. It returns the midpoint `(a + b) / 2` of the final
bracket `[a, b]`.

The algorithm exploits the golden ratio φ ≈ 1.618 to shrink the bracket optimally:
on each iteration exactly one function evaluation is needed (the other interior point
was already evaluated) and the bracket shrinks by a factor of `1/φ ≈ 0.618` per step.

---

## Algorithm

```
c = b − (b − a) / φ
d = a + (b − a) / φ
while |c − d| > tol:
    if f(c) < f(d):  b = d
    else:            a = c
    c = b − (b − a) / φ
    d = a + (b − a) / φ
return (a + b) / 2
```

---

## Preconditions

1. `arg1 < arg2` — the initial bracket is non-trivial.
2. `f` is unimodal on `[arg1, arg2]` (has exactly one minimum; not formally verified).
3. `tol > 0` — the tolerance is positive (ensures termination).
4. The numeric type `_Tp` supports arithmetic with sufficient precision.

---

## Postconditions

1. **Containment**: the returned value `(a + b) / 2` is always in `[arg1, arg2]`.
2. **Bracket size**: the final bracket `[a, b]` satisfies `|b − a| ≤ tol`.
3. **Bracket containment**: at all times `arg1 ≤ a ≤ b ≤ arg2`.

---

## Key Invariants (loop invariant)

Let `r = 1/φ ≈ 0.618` and `r' = 1 − r = 1/φ² ≈ 0.382`. Let `w = b − a`.

1. **Ordering**: `a ≤ c ≤ d ≤ b`
2. **Interior positions**:
   - `c = b − w·r = a + w·r'`
   - `d = a + w·r = b − w·r'`
3. **Strict interior** (when `a < b`): `a < c < d < b` (since `r > 1/2`)
4. **Width contraction**: after each step the width shrinks to `w·r`

---

## Interior Point Computations

For the bracket `[a, b]` with width `w = b − a`:
- `c = b − w/φ = b − w·r`
- `d = a + w/φ = a + w·r`

Since `r = 1/φ ≈ 0.618 > 1/2`, we have `d − c = w·(2r − 1) > 0`, so `c < d`.

After the `b = d` update:
- new width = `d − a = w·r`
- new c = `d − (d−a)/φ = d − w·r²` (recomputed from scratch)

After the `a = c` update:
- new width = `b − c = w·r`
- new d = `c + (b−c)/φ = c + w·r²` (recomputed from scratch)

---

## Convergence

The width after `n` iterations is `w₀ · rⁿ`. Since `0 < r < 1`, the width converges
to 0 exponentially. The number of iterations to achieve tolerance `tol` from initial
width `w₀` is `⌈log(tol/w₀) / log(r)⌉`.

For `w₀ = 1` and `tol = 1e-5`, this is about 26 iterations.

---

## Returned Value

`(a + b) / 2` — the midpoint of the final bracket. Since the bracket shrinks to width
≤ tol, the returned value is within `tol/2` of the true minimum (assuming unimodality).

---

## Edge Cases

- **`arg1 = arg2`**: the initial bracket is empty; the loop body never executes (since
  `c = d = arg1 = arg2`, so `|c − d| = 0 ≤ tol`). Returns `arg1`. *Note*: the
  precondition requires `arg1 < arg2`, so this is a degenerate input.
- **`tol = 0`**: the algorithm may not terminate (floating-point equality of `c` and `d`
  may never be reached). The precondition requires `tol > 0`.
- **Negative interval** (`arg1 > arg2`): behaviour is undefined; the precondition
  excludes this.

---

## Inferred Intent

The algorithm is intended as a fast, derivative-free minimization subroutine for
PX4 flight controllers. Likely use cases include finding optimal tilt angles,
gains, or other scalar parameters that minimise a cost function.

The use of the golden ratio is deliberate: it is the optimal constant for bracket-
search algorithms (no smaller constant guarantees termination for all unimodal f).

---

## Open Questions

1. Does PX4 ever call this with `arg1 > arg2` (reversed interval)? If so, what is
   the expected behaviour?
2. The function returns `(a + b) / 2` — could it return either `a`, `b`, or the
   midpoint? Is there a preference?
3. The `GOLDEN_RATIO` constant `1.6180339887` is a truncated approximation.
   Could this cause the ordering invariant `c < d` to be violated for very small
   intervals? (Answer: only if `(b−a) < eps` where eps is the float representation
   error of the golden ratio, so negligible in practice.)

---

## Examples

For `f(x) = (x − 3)²`, `arg1 = 0`, `arg2 = 6`, `tol = 1e-4`:
- Initial: `a=0, b=6, c≈3.708, d≈2.292` (note: C++ uses `GOLDEN_RATIO` so
  `c = 6 − 6/1.618 ≈ 2.292`, `d = 0 + 6/1.618 ≈ 3.708`).
- `f(c) < f(d)` iff `c` is closer to 3 than `d`; the algorithm converges to `≈3.0`.

For the ordering invariant: `a=0, b=6, r=1/1.618`:
- `c = 6 − 6·r ≈ 2.292`, `d = 0 + 6·r ≈ 3.708`
- `0 ≤ 2.292 ≤ 3.708 ≤ 6` ✓
