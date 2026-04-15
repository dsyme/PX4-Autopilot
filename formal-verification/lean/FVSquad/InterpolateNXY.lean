import FVSquad.Interpolate

/-!
# Piecewise-Linear Interpolation over Sorted Table — `math::interpolateNXY`

🔬 Lean Squad automated formal verification.

This file provides formal specifications and proofs for the piecewise-linear
N-point table interpolation function from `src/lib/mathlib/math/Functions.hpp`:

```cpp
template<typename T, size_t N>
const T interpolateNXY(const T &value, const T(&x)[N], const T(&y)[N])
{
    size_t index = 0;
    while ((value > x[index + 1]) && (index < (N - 2))) {
        index++;
    }
    return interpolate(value, x[index], x[index + 1], y[index], y[index + 1]);
}
```

## Scope

We model and verify the **3-point case (N=3)** as `interp3`. This is the most common
use case in PX4 (e.g., motor efficiency curves, RC lookup tables with three control
points). The proofs cover:

- Low and high clamping (outside the table range)
- Exact endpoint values at `x[0]`, `x[1]`, `x[2]`
- Continuity at the interior breakpoint `x[1]` (both segments agree on `y[1]`)
- Range containment when y-values are monotone
- Monotonicity of each segment

## Approximations

- Arithmetic is over `Rat` (exact rationals, not IEEE 754 floats).
- The 3-point model is exact for N=3; for N > 3, the proofs carry over to each
  segment pair by structural symmetry.
- Overflow and NaN are not modelled.

## Structure

Imported from `FVSquad.Interpolate` (single-segment `interpolate` and its theorems).
-/

open PX4.Interpolate

/-!
# 3-Point Piecewise-Linear Interpolation — `interpolateNXY` (N=3)
Models the C++ `math::interpolateNXY` template for N=3. -/

namespace PX4.InterpolateNXY

/-- 3-point piecewise-linear interpolation. Exact model of `interpolateNXY` for N=3.

    Given sorted breakpoints `x0 < x1 < x2` and corresponding values `y0, y1, y2`,
    returns `interpolate` on the appropriate segment:
    - `v > x1`:  segment 1 `[x1, x2]`
    - `v ≤ x1`:  segment 0 `[x0, x1]` -/
def interp3 (v x0 x1 x2 y0 y1 y2 : Rat) : Rat :=
  if v > x1 then interpolate v x1 x2 y1 y2
  else interpolate v x0 x1 y0 y1

-- Sanity checks
#eval interp3 0     0 1 2  0  5 10  -- 0   (at x0)
#eval interp3 (1/2) 0 1 2  0  5 10  -- 2.5 (first segment midpoint)
#eval interp3 1     0 1 2  0  5 10  -- 5   (at x1 from segment 0)
#eval interp3 (3/2) 0 1 2  0  5 10  -- 7.5 (second segment midpoint)
#eval interp3 2     0 1 2  0  5 10  -- 10  (at x2)
#eval interp3 (-1)  0 1 2  0  5 10  -- 0   (clamped low)
#eval interp3 3     0 1 2  0  5 10  -- 10  (clamped high)

/-- **Low clamp**: when `v ≤ x0 ≤ x1`, both segment conditions are false,
    and `interpolate v x0 x1 y0 y1` clamps to `y0`. -/
theorem interp3_low_clamp (v x0 x1 x2 y0 y1 y2 : Rat)
    (hv : v ≤ x0) (hx01 : x0 ≤ x1) :
    interp3 v x0 x1 x2 y0 y1 y2 = y0 := by
  simp only [interp3, if_neg (Rat.not_lt.mpr (Rat.le_trans hv hx01))]
  exact interpolate_clamped_low v x0 x1 y0 y1 hv

/-- **High clamp**: when `v > x2` (and `x1 < x2`), segment 1 is used and clamps high. -/
theorem interp3_high_clamp (v x0 x1 x2 y0 y1 y2 : Rat)
    (hv : v > x2) (hx12 : x1 < x2) :
    interp3 v x0 x1 x2 y0 y1 y2 = y2 := by
  have h1 : v > x1 := Std.lt_trans hx12 hv
  simp only [interp3, if_pos h1]
  exact interpolate_clamped_high v x1 x2 y1 y2 hx12 hv

/-- **At first endpoint** `v = x0`: output is exactly `y0` (when `x0 ≤ x1`). -/
theorem interp3_at_x0 (x0 x1 x2 y0 y1 y2 : Rat) (h : x0 ≤ x1) :
    interp3 x0 x0 x1 x2 y0 y1 y2 = y0 := by
  exact interp3_low_clamp x0 x0 x1 x2 y0 y1 y2 Rat.le_refl h

/-- **At breakpoint** `v = x1`: output is `y1` (segment 0 gives `y1` via `interpolate_at_high`). -/
theorem interp3_at_x1 (x0 x1 x2 y0 y1 y2 : Rat) (h01 : x0 < x1) :
    interp3 x1 x0 x1 x2 y0 y1 y2 = y1 := by
  simp only [interp3, if_neg Rat.lt_irrefl]
  exact interpolate_at_high x0 x1 y0 y1 h01

/-- **Continuity at `x1` from segment 1**: `interpolate x1 x1 x2 y1 y2 = y1`.
    Together with `interp3_at_x1`, this confirms the two segments join at `y1`. -/
theorem interp3_seg1_at_x1 (_x0 x1 x2 _y0 y1 y2 : Rat) :
    interpolate x1 x1 x2 y1 y2 = y1 :=
  interpolate_at_low x1 x2 y1 y2

/-- **At last endpoint** `v = x2`: output is `y2` (when `x1 < x2`). -/
theorem interp3_at_x2 (x0 x1 x2 y0 y1 y2 : Rat) (h12 : x1 < x2) :
    interp3 x2 x0 x1 x2 y0 y1 y2 = y2 := by
  simp only [interp3, if_pos h12]
  exact interpolate_at_high x1 x2 y1 y2 h12

/-- **Upper range bound**: if `y0 ≤ y1 ≤ y2` and `x0 < x1 < x2`,
    then the output is ≤ `y2` for any `v`. -/
theorem interp3_le_y2 (v x0 x1 x2 y0 y1 y2 : Rat)
    (hx01 : x0 < x1) (hx12 : x1 < x2) (hy01 : y0 ≤ y1) (hy12 : y1 ≤ y2) :
    interp3 v x0 x1 x2 y0 y1 y2 ≤ y2 := by
  simp only [interp3]
  by_cases hv : v > x1
  · simp only [if_pos hv]
    exact interpolate_le_high v x1 x2 y1 y2 hx12 hy12
  · simp only [if_neg hv]
    exact Rat.le_trans (interpolate_le_high v x0 x1 y0 y1 hx01 hy01) hy12

/-- **Lower range bound**: if `y0 ≤ y1 ≤ y2` and `x0 < x1 < x2`,
    then the output is ≥ `y0` for any `v`. -/
theorem interp3_ge_y0 (v x0 x1 x2 y0 y1 y2 : Rat)
    (hx01 : x0 < x1) (hx12 : x1 < x2) (hy01 : y0 ≤ y1) (hy12 : y1 ≤ y2) :
    y0 ≤ interp3 v x0 x1 x2 y0 y1 y2 := by
  simp only [interp3]
  by_cases hv : v > x1
  · simp only [if_pos hv]
    exact Rat.le_trans hy01 (interpolate_ge_low v x1 x2 y1 y2 hx12 hy12)
  · simp only [if_neg hv]
    exact interpolate_ge_low v x0 x1 y0 y1 hx01 hy01

/-- **Monotone in segment 0**: when y-values are ordered, x-values strictly increasing,
    and both query points are strictly above `x0` but within segment 0 (`v ≤ x1`),
    a larger query gives a larger output. -/
theorem interp3_mono_seg0 (v1 v2 x0 x1 x2 y0 y1 y2 : Rat)
    (hx01 : x0 < x1) (hv1lo : x0 < v1) (hv12 : v1 ≤ v2) (hv2 : v2 ≤ x1) (hy01 : y0 ≤ y1) :
    interp3 v1 x0 x1 x2 y0 y1 y2 ≤ interp3 v2 x0 x1 x2 y0 y1 y2 := by
  simp only [interp3, if_neg (Rat.not_lt.mpr hv2), if_neg (Rat.not_lt.mpr (Rat.le_trans hv12 hv2))]
  exact interpolate_mono_interior x0 x1 y0 y1 v1 v2 hx01 hy01 hv1lo hv12 hv2

/-- **Monotone in segment 1**: when y-values are ordered, x-values strictly increasing,
    and both query points are strictly inside segment 1 (`v1 > x1`, `v2 ≤ x2`),
    a larger query gives a larger output. -/
theorem interp3_mono_seg1 (v1 v2 x0 x1 x2 y0 y1 y2 : Rat)
    (hx12 : x1 < x2) (hv1 : v1 > x1) (hv12 : v1 ≤ v2) (hv2 : v2 ≤ x2) (hy12 : y1 ≤ y2) :
    interp3 v1 x0 x1 x2 y0 y1 y2 ≤ interp3 v2 x0 x1 x2 y0 y1 y2 := by
  have hv2_gt : v2 > x1 := Std.lt_of_lt_of_le hv1 hv12
  simp only [interp3, if_pos hv1, if_pos hv2_gt]
  exact interpolate_mono_interior x1 x2 y1 y2 v1 v2 hx12 hy12 hv1 hv12 hv2

/-- **Output in range**: when y-values are monotone and x-values strictly increasing,
    the output is always in `[y0, y2]` for any input `v`. This is the key safety
    property: no actuator value escapes the table range. -/
theorem interp3_in_range (v x0 x1 x2 y0 y1 y2 : Rat)
    (hx01 : x0 < x1) (hx12 : x1 < x2) (hy01 : y0 ≤ y1) (hy12 : y1 ≤ y2) :
    y0 ≤ interp3 v x0 x1 x2 y0 y1 y2 ∧ interp3 v x0 x1 x2 y0 y1 y2 ≤ y2 :=
  ⟨interp3_ge_y0 v x0 x1 x2 y0 y1 y2 hx01 hx12 hy01 hy12,
   interp3_le_y2 v x0 x1 x2 y0 y1 y2 hx01 hx12 hy01 hy12⟩

end PX4.InterpolateNXY
