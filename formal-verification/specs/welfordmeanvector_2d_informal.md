# Informal Specification: `WelfordMeanVector<T, 2>::update`

🔬 *Lean Squad automated formal verification.*

## Source

`src/lib/mathlib/math/WelfordMeanVector.hpp`

Used by `VehicleIMU` and `GyroCalibration` with N=3 (3D), but we specify the N=2
(2D) case for tractability.

```cpp
template <typename Type, size_t N>
bool WelfordMeanVector<Type, N>::update(const matrix::Vector<Type, N> &new_value)
{
    if (_count == 0) {
        reset();
        _count = 1;
        _mean = new_value;
        return false;
    } else if (_count == UINT16_MAX) {
        _M2 = _M2 / _count;
        _M2_accum.zero();
        _count = 1;
    } else {
        _count++;
    }

    // Kahan-compensated mean update (vectorised)
    const Vector delta{new_value - _mean};
    const Vector y = (delta / _count) - _mean_accum;
    const Vector t = _mean + y;
    _mean_accum = (t - _mean) - y;
    _mean = t;

    if (!_mean.isAllFinite()) {
        reset();
        return false;
    }

    // upper-triangle covariance update (Welford)
    for r in 0..N:
        for c in r..N:
            m2_change(r,c) = delta(r) * (new_value(c) - _mean(c))
    _M2 += m2_change + m2_change^T - diag(m2_change)  // symmetrise
    ...
    return (_count > 2);
}
```

## Purpose

`WelfordMeanVector<T,N>` computes, in a single streaming pass, the running
vector mean and the running sum-of-outer-product matrix (M2) used to derive the
sample covariance. After seeing `n` samples `x₁, …, xₙ` the object satisfies:

```
_count = n
_mean  ≈ (x₁ + … + xₙ) / n         (exact over ℚ; approximate over float)
_M2[i,j] ≈ Σₖ (xₖᵢ - mean_i)(xₖⱼ - mean_j)   (sample covariance numerator)
```

The key mathematical invariant is that `_mean * _count = sum of all observed vectors`.

## State

| Field | Type (float32, N=2) | Meaning |
|-------|---------------------|---------|
| `_count` | `uint16_t` | Number of samples seen |
| `_mean` | `Vector<T,2>` | Running componentwise mean |
| `_mean_accum` | `Vector<T,2>` | Kahan compensator for mean (ignored in model) |
| `_M2` | `SquareMatrix<T,2>` | Running sum-of-squared-deviations matrix |
| `_M2_accum` | `SquareMatrix<T,2>` | Kahan compensator for M2 (ignored in model) |

## Preconditions

- `new_value` components are finite (not NaN, not ±∞)
- `_count < UINT16_MAX` (overflow handling ignored in model)
- `_count == 0` or the object has been updated consistently

## Postconditions

After `update(x)` on state `(n, mean)`:
- `count_new = n + 1` (assuming n < UINT16_MAX and n ≥ 1)
- `mean_new * (n+1) = mean * n + x` for each component
- The M2 matrix is updated by the outer-product correction

## Key Properties (componentwise, per each index i=0,1)

1. **Mean invariant**: `mean_i * count = Σₖ xₖᵢ` (sum of all observed component values)
2. **Initialization**: after the first sample, `mean = x₁` and `count = 1`
3. **Zero reset**: if `_count == 0` before update, result is same as first-sample case
4. **Monotone count**: `count` strictly increases on each update (until overflow)
5. **Convergence**: the running mean converges to the arithmetic mean of all samples

## Modelling Choices

- We model arithmetic over `Rat` (exact rationals), ignoring IEEE-754 rounding.
- We ignore the Kahan compensator fields `_mean_accum` and `_M2_accum`.
- We ignore the `UINT16_MAX` overflow branch.
- We ignore `_M2` (covariance tracking) — only mean is modelled.
- We model N=2 (2D) and prove componentwise properties.

## Examples

- `update([3, 7])` on empty state → `mean = [3, 7]`, `count = 1`
- `update([1, 5])` then `update([3, 7])` → `mean = [2, 6]`, `count = 2`
- 3 updates with `[0,0]`, `[2,4]`, `[1,2]` → `mean = [1, 2]`, `count = 3`

## Open Questions

1. How much does the Kahan compensator matter in practice?
   (Affects floating-point accuracy, not mathematical invariants)
2. Is the covariance update symmetric? The code builds upper triangle then symmetrises.
3. The `isAllFinite()` reset on bad input could lose accumulated data — is that intended?
