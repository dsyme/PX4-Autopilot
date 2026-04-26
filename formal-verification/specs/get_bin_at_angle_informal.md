# Informal Specification: `get_bin_at_angle` / `get_offset_bin_index`

🔬 *Lean Squad automated formal verification.*

**C++ source**: `src/lib/collision_prevention/ObstacleMath.cpp`
**Formal spec**: `formal-verification/lean/FVSquad/GetBinAtAngle.lean`

---

## Purpose

The PX4 collision-prevention module divides the 360° horizontal plane into `n` equal
angular bins (e.g., 36 bins × 10°/bin). Sensors and obstacles are associated with bins.

- **`get_bin_at_angle(bin_width, angle)`**: given an angle in degrees, return the index
  of the bin that angle falls into. Bin `0` is the 0° direction, bins are numbered
  clockwise. The result is always in `[0, n)` where `n = 360 / bin_width`.

- **`get_offset_bin_index(bin, bin_width, angle_offset)`**: given a bin index and an
  angular offset, return the "relative" bin index after rotating the reference frame by
  `angle_offset`. Used to convert between world-frame and body-frame bin indices.

---

## Preconditions

- `bin_width > 0` and `360 / bin_width` is a positive integer `n`.
- For `get_bin_at_angle`: `angle` is a finite floating-point value.
- For `get_offset_bin_index`: `bin ∈ ℤ` (the function wraps it internally).

---

## Postconditions

1. **Range**: `get_bin_at_angle` returns a value in `[0, n)`.
2. **Range**: `get_offset_bin_index` returns a value in `[0, n)`.
3. **Zero angle → bin 0**: `get_bin_at_angle(bw, 0) = 0`.
4. **Periodicity (360°)**: `get_bin_at_angle(bw, a + 360) = get_bin_at_angle(bw, a)`.
5. **Zero offset = identity**: `get_offset_bin_index(b, bw, 0) = b mod n`.
6. **Offset = subtraction**: `get_offset_bin_index(b, bw, offset) =`
   `get_bin_at_angle(bw, b * bw - offset)` — rotating by offset is equivalent
   to subtracting the offset bin from the bin index.
7. **Self-offset = 0**: `get_offset_bin_index(b, bw, b * bw) = 0` for bin `b`.
8. **Round-trip**: `get_bin_at_angle(bw, get_lower_bound_angle(b, bw, 0) + bw/2) = b mod n`.

---

## Invariants

- The bin circle has exactly `n` distinct positions; all operations are modulo `n`.
- `get_offset_bin_index` implements a **rotation** on the bin circle: it is a bijection
  `[0, n) → [0, n)` for fixed offset, and the inverse rotation is `+offset`.
- Rotation is commutative with `get_bin_at_angle`: rotating then looking up a bin
  is the same as looking up the rotated angle.

---

## Edge Cases

- **Negative angle**: `get_bin_at_angle(10, -10) = 35` (wraps to 350°, bin 35 for n=36).
- **Angle = 360**: same as 0° (wrap_360 maps it to bin 0).
- **Large angles**: any integer multiple of 360° maps to the same result.
- **Negative bin**: `get_offset_bin_index(-5, 10, 0) = 31` (wrap_bin handles this).
- **bin_width does not divide 360**: floating-point rounding may cause `n` to deviate
  from the intended value; the model assumes exact divisibility.

---

## Examples

| Function | Input | Output | Notes |
|----------|-------|--------|-------|
| `get_bin_at_angle(10, 0)` | bw=10, a=0 | 0 | North |
| `get_bin_at_angle(10, 90)` | bw=10, a=90 | 9 | East (9 * 10 = 90) |
| `get_bin_at_angle(10, 360)` | bw=10, a=360 | 0 | Full circle |
| `get_bin_at_angle(10, -10)` | bw=10, a=-10 | 35 | Wraps: 350° = bin 35 |
| `get_offset_bin_index(10, 10, 50)` | b=10, bw=10, offset=50 | 5 | 10-5=5 |
| `get_offset_bin_index(3, 10, 50)` | b=3, bw=10, offset=50 | 34 | 3-5=-2→34 |

---

## Inferred Intent

The two functions form a **reference-frame transformation** pair:
- `get_bin_at_angle` converts from angle space to bin index space.
- `get_offset_bin_index` shifts bin indices by an angular offset, enabling sensors
  mounted at different orientations to report in a common reference frame.

The integer arithmetic model captures the essential algebraic structure: both functions
are modular operations on `ℤ/nℤ` (the cyclic group of `n` elements).

---

## Open Questions

1. When `angle` is not an integer multiple of `bin_width`, `round()` introduces ±0.5 bin
   ambiguity at bin boundaries. Which bin "owns" an angle exactly at `(k + 0.5) * bw`?
2. Does the convention match real sensor data? Lidar sensors report distance at the
   *center* of each angular sector; is the `- bin_width / 2` in `get_lower_bound_angle`
   consistent with this?
3. Are there callers that depend on `get_offset_bin_index` being the *exact* inverse of
   `get_bin_at_angle(bw, angle_offset)` (i.e., round-trip guarantees with float rounding)?
