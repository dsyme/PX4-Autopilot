# Informal Specification: `get_lower_bound_angle`

🔬 *Lean Squad automated formal verification.*

**C++ source**: `src/lib/collision_prevention/ObstacleMath.cpp` (line 60)  
**Related target**: `GetBinAtAngle` (bins the corresponding angle → bin direction)

---

## Purpose

`get_lower_bound_angle` returns the **lower angular boundary** (in degrees, range `[0°, 360°)`) of the angular sector corresponding to bin `bin`. The collision-prevention system divides the full 360° circle into `n = 360 / bin_width` equal bins. Each bin `b` covers the angular range `[lower_b, lower_b + bin_width)`. An optional `angle_offset` rotates the entire bin grid.

---

## C++ Implementation

```cpp
float get_lower_bound_angle(int bin, float bin_width, float angle_offset)
{
    bin = wrap_bin(bin, 360 / bin_width);
    return wrap_360(bin * bin_width + angle_offset - bin_width / 2.f);
}
```

Step by step:

1. **Wrap the bin index** into `[0, n)` via `wrap_bin(bin, n)` where `n = 360 / bin_width`. This handles out-of-range inputs gracefully.
2. **Compute the bin centre angle** as `bin * bin_width + angle_offset`.  
   - `bin * bin_width` is the nominal centre of the un-shifted bin.  
   - `angle_offset` shifts the entire grid (e.g. a sensor mounted at a yaw offset).
3. **Subtract half a bin width** to obtain the *left edge* (lower bound) of the bin: centre − `bin_width / 2`.
4. **Wrap to `[0°, 360°)`** via `wrap_360`.

---

## Preconditions

- `bin_width > 0`
- `360 / bin_width` is a positive integer (i.e. `bin_width` divides 360; typical values: 2, 3, 5, 6, 10, 15, 20, …)
- `angle_offset` is any real number (commonly in `(−180°, 180°]`)
- `bin` is any integer (will be wrapped)

---

## Postconditions

1. **Range**: `0 ≤ result < 360`
2. **Semantics**: `result = wrap_360(wbin * bin_width + angle_offset − bin_width / 2)` where `wbin = wrap_bin(bin, n)`.
3. **Periodicity**: `get_lower_bound_angle(bin + n, bw, off) = get_lower_bound_angle(bin, bw, off)` — shifting bin by one full circle is transparent.
4. **Consecutive bins differ by `bin_width`**: the lower bound of bin `b+1` equals the lower bound of bin `b` plus `bin_width` (modulo 360), for all `b` not at the wrap boundary.

---

## Invariants

- The lower bound of bin `b` is exactly `bin_width` less than the lower bound of bin `b+1` (modulo 360).
- The lower bound of bin 0 with zero offset is `wrap_360(−bin_width/2) = 360 − bin_width/2`.  
  For `bin_width = 10`, that is `355°`.
- **Centre relation**: `lower_bound(b) + bin_width / 2 ≡ b * bin_width + angle_offset (mod 360)`.  
  The lower bound is always half a bin width *before* the nominal bin centre.

---

## Edge Cases

- **`bin = -1`** with `bin_width = 7.5`, `angle_offset = -4.3`:  
  `n = 48`, `wrap_bin(-1, 48) = 47`, centre = `47*7.5 + (−4.3) = 352.5 − 4.3 = 348.2`, lower = `wrap_360(348.2 − 3.75) = wrap_360(344.45) = 344.45°`.  
  This matches the unit test `EXPECT_FLOAT_EQ(lower_bound, 344.45)`.
- **`bin = 0`**, `bin_width = 10`, `angle_offset = 0`:  
  Lower bound = `wrap_360(0 − 5) = 355°`.
- **`angle_offset` causes wrap**: If the un-wrapped lower bound is negative or ≥ 360, `wrap_360` normalises it.

---

## Examples (integer-domain model)

When `angle_offset = 0` and angles are expressed in **half-bin units** (1 unit = `bin_width / 2`), the full circle spans `2n` units and:

| `n` | bin `b` | lower bound (half-bin units) | degrees (× `bin_width/2`) |
|-----|---------|------------------------------|---------------------------|
|  4  |    0    | `2n − 1 = 7`                 | 315°                       |
|  4  |    1    | 1                            |  45°                       |
|  4  |    2    | 3                            | 135°                       |
|  4  |    3    | 5                            | 225°                       |

Each consecutive bin increases the lower bound by 2 half-bin units (= 1 full bin width).

---

## Inferred Intent

The function is used by the **collision prevention system** to test whether a measured obstacle angle falls within bin `b`'s sector, i.e.:

```
lower_bound_angle(b, bw, off) ≤ angle < lower_bound_angle(b, bw, off) + bw
```

The `−bin_width/2` shift makes the bins *centred* on their nominal angles rather than left-aligned. This is the natural convention when the bin index is computed by rounding (as in `get_bin_at_angle` which uses `round()`).

---

## Open Questions

1. **Non-dividing `bin_width`**: when `360 / bin_width` is not an integer, is there a defined behaviour? In practice PX4 uses values that divide 360.
2. **Interaction with `angle_offset`**: is `angle_offset` always in the range `[−bin_width/2, bin_width/2)`? The code applies no such restriction.
3. **Floating-point rounding**: the test expects `FLOAT_EQ(lower_bound, 344.45)` — this is a round number; is there a deliberate design to keep lower bounds at representable floats?

---

## Formal Model Choice

We use an **integer model with half-bin units**:
- `n`: number of bins
- `b`: bin index (any integer)
- `a`: angle offset in half-bin units (any integer)
- `getLowerBoundI n b a = (2 * (b % n) + a - 1) % (2*n)`

This captures the exact structure: the full circle is `2n` half-bin units; the lower bound of bin `b` is one half-unit *before* its centre `2 * (b % n) + a`.
