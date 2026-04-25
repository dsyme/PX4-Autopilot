# Informal Specification: Collision Prevention Composition

🔬 *Lean Squad automated formal verification.*

- **C++ source**: `src/lib/collision_prevention/ObstacleMath.cpp`
- **Related Lean files**:
  - `formal-verification/lean/FVSquad/GetBinAtAngle.lean`
  - `formal-verification/lean/FVSquad/GetLowerBoundAngle.lean`
  - `formal-verification/lean/FVSquad/CollisionPrevComposition.lean`

---

## Purpose

The collision prevention module (`CollisionPrevention.cpp`) detects obstacles by dividing
the 360° horizontal plane into `n` equal angular **bins** and maintaining distance
measurements per bin. Three functions from `ObstacleMath` govern the geometry:

| C++ function | Role |
|---|---|
| `get_bin_at_angle(bw, angle)` | Map an angle to a bin index `[0, n)` |
| `get_offset_bin_index(bin, bw, offset)` | Rotate reference frame: `bin → (bin - offset_bin) mod n` |
| `get_lower_bound_angle(bin, bw, offset)` | Lower boundary of bin's sector in `[0°, 360°)` |

This spec describes the **composition properties** that must hold for the three functions
to form a geometrically consistent system.

---

## Preconditions

- `n = 360 / bin_width` is a positive integer (e.g. `n = 72` for `bin_width = 5°`).
- Angles are measured in degrees, clockwise from North (bin 0).
- `angle_offset` specifies the angular reference-frame rotation.
- For the integer model: angles are integer multiples of `bin_width`; no float rounding.

---

## Postconditions and Invariants

### 1. Bin-index cast transparency

`get_bin_at_angle` returns a `Nat` in `[0, n)`. When this result is used as the `bin`
argument to `get_lower_bound_angle` (after integer cast), the output should equal the
lower bound computed from the original angle directly.

**Property**: `lower_bound(bin_at_angle(k), offset) = lower_bound(k, offset)`

This means: *extracting a bin index and then computing its lower bound is equivalent
to computing the lower bound directly from the original angle.* The bin-index extraction
is lossless for the purpose of lower-bound computation (within the same bin).

### 2. Rotated-frame lower bound

When sensors are mounted at an angular offset, obstacle data arrives in a rotated reference
frame. The `get_offset_bin_index` transforms bin indices between frames. The lower bound
of the transformed bin must correspond to the correct angle in the original frame.

**Property**: `lower_bound(offset_bin(bin, k), offset) = lower_bound(bin - k, offset)`

This ensures: *rotating a bin index by `k` and computing its lower bound gives the same
result as computing the lower bound at angle `bin - k`.* Sensor fusion across multiple
frame rotations is geometrically consistent.

### 3. Rotation group structure

Frame rotations should compose additively — applying two rotations in sequence is
equivalent to applying their sum as a single rotation.

**Property**: `offset_bin(offset_bin(bin, k1), k2) = offset_bin(bin, k1 + k2)`

**Corollary (inverse)**: `offset_bin(offset_bin(bin, k), -k) = bin_at_angle(bin)` — 
rotating forward and back recovers the original bin.

**Corollary (full circle)**: `offset_bin(offset_bin(bin, n), 0) = bin_at_angle(bin)` —
rotating by a full circle is a no-op.

### 4. Composed-rotation lower bound

Combining the rotation composition and lower bound theorems:

**Property**: `lower_bound(offset_bin(offset_bin(bin, k1), k2), offset) = lower_bound(bin - (k1 + k2), offset)`

This proves that after any sequence of frame rotations, the lower bound correctly
identifies the expected angular sector boundary.

---

## Edge Cases

- **`k = 0`** (no rotation): `offset_bin(bin, 0) = bin_at_angle(bin)` — identity rotation.
- **`k = n`** (full circle): `offset_bin(bin, n) = offset_bin(bin, 0)` — wraps back.
- **Negative offsets**: handled by `Int.emod` (Euclidean remainder, always nonneg).
- **Large angles**: periodicity ensures `lower_bound(bin + n, offset) = lower_bound(bin, offset)`.

---

## Examples

With `n = 4` (90°/bin), `bin_width = 90°`, half-bin unit = 45°:

| Operation | Value | Meaning |
|---|---|---|
| `bin_at_angle(4, 0)` = 0 | cast → 0 | Lower bound of angle 0 = lower bound of bin 0 |
| `offset_bin(7, n=4, k=1)` = 2 | rotate bin 7 by 1 | `(7-1)%4 = 2` |
| `offset_bin(offset_bin(3, k=1), k=2)` = `offset_bin(3, k=3)` | Composition | `(3-3)%4 = 0` |
| `offset_bin(offset_bin(3, k=2), k=-2)` = `bin_at_angle(3)` | Inverse | `3 mod 4 = 3` |

---

## Open Questions

1. **Float rounding**: the C++ implementation uses `float`. For non-integer multiples of
   `bin_width`, the integer model is only approximate. When does float rounding cause
   the bin assignment to differ from the integer model? (See also `GetBinAtAngle` informal spec.)
2. **Negative offsets at boundaries**: does `get_lower_bound_angle` with a negative
   `angle_offset` always produce the expected sector boundary? The integer model handles
   this via `Int.emod` (Euclidean), but the C++ `wrap_360` may behave differently for
   edge values.
3. **Composition with `get_lower_bound_angle`**: is there a direct C++ test for the
   composition invariant `lower_bound(offset_bin(b, k), off) = lower_bound(b-k, off)`?
   If so, it should be added to `ObstacleMathTest.cpp`.
