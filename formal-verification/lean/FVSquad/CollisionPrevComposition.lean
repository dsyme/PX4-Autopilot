import FVSquad.GetBinAtAngle
import FVSquad.GetLowerBoundAngle

/-!
# Collision Prevention — Cross-Module Composition Theorems

🔬 *Lean Squad automated formal verification.*

- **C++ source**: `src/lib/collision_prevention/ObstacleMath.cpp`
- **Depends on**:
  - `GetBinAtAngle.lean` (`getBinI`, `getOffsetBinI`)
  - `GetLowerBoundAngle.lean` (`getLowerBoundI`)

## Purpose

This file proves **composition theorems** that connect the three core collision-prevention
integer models:

| Model | Lean function | C++ function |
|-------|--------------|--------------|
| Bin at angle | `getBinI n k` | `get_bin_at_angle` |
| Offset bin | `getOffsetBinI n b k` | `get_offset_bin_index` |
| Lower bound angle | `getLowerBoundI n b a` | `get_lower_bound_angle` |

The theorems verify that these functions form a **geometrically consistent system**:
- The lower bound of the bin containing angle `k` equals the lower bound of angle `k` directly.
- The lower bound of a rotated bin equals the lower bound computed from the rotation-adjusted angle.
- Two consecutive rotations compose additively (rotation forms a group action on bins).

## Key results

- **`getBinI_cast`** (helper): `↑(getBinI n k) = k % n` — bridge between Nat result and Int arithmetic.
- **`lowerBound_at_getBin`**: `getLowerBoundI n (↑(getBinI n k)) a = getLowerBoundI n k a`
  — the lower bound of the bin containing angle `k` can be computed directly from `k`.
- **`lowerBound_of_offsetBin`**: `getLowerBoundI n (↑(getOffsetBinI n b k)) a = getLowerBoundI n (b - k) a`
  — after a frame rotation of `k` bins, the lower bound equals the unrotated geometry shifted by `k`.
- **`offsetBin_compose`**: `getOffsetBinI n (↑(getOffsetBinI n b k1)) k2 = getOffsetBinI n b (k1 + k2)`
  — two successive frame rotations compose additively.
- **`lowerBound_of_composed_offset`**: combines the above to show that lower bounds commute with
  composed rotations.

## Approximations

All theorems are proved in the integer model (exact for angles that are integer multiples of
`bin_width`). Float rounding in the C++ implementation is not modelled here.
-/

open PX4.BinAngle   -- getBinI, getOffsetBinI, ...
open PX4.LowerBound -- getLowerBoundI, ...

namespace PX4.CollisionPrev

/-! ## Helper: casting `getBinI` result back to `Int` -/

/-- **Cast lemma**: the `Nat`-typed bin index, when cast back to `Int`, equals `k % n`.

    `getBinI n k = (k % n).toNat`, so `↑(getBinI n k) = ↑((k % n).toNat) = k % n`
    (using `Int.toNat_of_nonneg`, valid since Euclidean remainder is nonneg for positive `n`). -/
theorem getBinI_cast (n : Nat) (k : Int) (hn : 0 < n) :
    (↑(getBinI n k) : Int) = k % ↑n := by
  unfold getBinI
  exact Int.toNat_of_nonneg (Int.emod_nonneg k (by omega))

/-- **Cast lemma for `getOffsetBinI`**: `↑(getOffsetBinI n b k) = (b - k) % n`.

    Combines `getOffsetBinI_eq_getBinI_sub` with `getBinI_cast`. -/
theorem getOffsetBinI_cast (n : Nat) (b k : Int) (hn : 0 < n) :
    (↑(getOffsetBinI n b k) : Int) = (b - k) % ↑n := by
  rw [getOffsetBinI_eq_getBinI_sub _ _ _ hn, getBinI_cast _ _ hn]

/-! ## Lower bound of a bin specified by `getBinI` -/

/-- **Lower bound at bin-at-angle** (key composition theorem):
    The lower bound of the *bin containing angle `k`* equals the lower bound computed
    directly from angle `k`.

    In collision prevention: after computing the bin index for angle `k` via `get_bin_at_angle`,
    calling `get_lower_bound_angle` on that bin index gives the same result as computing
    the lower bound directly at angle `k`. The bin-index extraction is transparent. -/
theorem lowerBound_at_getBin (n : Nat) (k a : Int) (hn : 0 < n) :
    getLowerBoundI n (↑(getBinI n k)) a = getLowerBoundI n k a := by
  unfold getLowerBoundI
  rw [getBinI_cast n k hn]
  -- goal: (2 * ((k % ↑n) % ↑n) + a - 1) % (2*↑n)).toNat = (2 * (k % ↑n) + a - 1) % (2*↑n)).toNat
  -- (k % n) % n = k % n since k % n is already in [0, n)
  have h : (k % ↑n) % ↑n = k % ↑n :=
    Int.emod_eq_of_lt
      (Int.emod_nonneg k (by omega))
      (Int.emod_lt_of_pos k (by omega))
  rw [h]

/-- **Lower bound of offset bin** (rotated-frame lower bound):
    The lower bound of the bin *after rotating the reference frame by `k` bins* equals
    the lower bound of the unrotated angle `b - k`.

    This is the key correctness property for sensor fusion: if sensor data from a rotated
    frame gives bin `b`, then `get_lower_bound_angle` on the offset-transformed bin
    agrees with the lower bound at angle `b - k` in the original frame. -/
theorem lowerBound_of_offsetBin (n : Nat) (b k a : Int) (hn : 0 < n) :
    getLowerBoundI n (↑(getOffsetBinI n b k)) a = getLowerBoundI n (b - k) a := by
  rw [getOffsetBinI_cast n b k hn, ← getBinI_cast n (b - k) hn]
  exact lowerBound_at_getBin n (b - k) a hn

/-! ## Rotation group structure -/

/-- **Rotation composition** (group action):
    Two successive rotations by `k1` and then `k2` compose to a single rotation by `k1 + k2`.

    Formally: applying `get_offset_bin_index` twice with offsets `k1` and `k2` is the same
    as applying it once with offset `k1 + k2`. This confirms the frame rotations form a
    (discrete) rotation group action on the `n`-bin circle. -/
theorem offsetBin_compose (n : Nat) (b k1 k2 : Int) (hn : 0 < n) :
    getOffsetBinI n (↑(getOffsetBinI n b k1)) k2 = getOffsetBinI n b (k1 + k2) := by
  -- Unfold both sides to getBinI
  rw [getOffsetBinI_eq_getBinI_sub _ _ k2 hn,
      getOffsetBinI_cast n b k1 hn,
      getOffsetBinI_eq_getBinI_sub _ _ _ hn]
  -- goal: getBinI n ((b - k1) % n - k2) = getBinI n (b - (k1 + k2))
  unfold getBinI
  congr 1
  -- goal: ((b - k1) % n - k2) % n = (b - (k1 + k2)) % n
  rw [Int.sub_emod ((b - k1) % ↑n) k2 ↑n,
      Int.emod_eq_of_lt
        (Int.emod_nonneg (b - k1) (by omega))
        (Int.emod_lt_of_pos (b - k1) (by omega)),
      ← Int.sub_emod (b - k1) k2 ↑n]
  congr 1; omega

/-- **Rotation identity** (special case of composition):
    Applying a rotation and then its inverse returns to the original bin.

    `getOffsetBinI n (↑(getOffsetBinI n b k)) (-k) = getBinI n b`

    This is `offsetBin_compose` with `k2 = -k`, combined with `getOffsetBinI n b 0 = getBinI n b`. -/
theorem offsetBin_inv_cancel (n : Nat) (b k : Int) (hn : 0 < n) :
    getOffsetBinI n (↑(getOffsetBinI n b k)) (-k) = getBinI n b := by
  rw [offsetBin_compose n b k (-k) hn]
  have hzero : k + -k = 0 := by omega
  rw [hzero]
  exact getOffsetBinI_zero_offset n b hn

/-- **Rotation zero** (special case of composition):
    Applying `getOffsetBinI` with `k = n` (a full circle) is a no-op.
    Follows from `offsetBin_compose` and periodicity of `getOffsetBinI`. -/
theorem offsetBin_full_circle (n : Nat) (b : Int) (hn : 0 < n) :
    getOffsetBinI n (↑(getOffsetBinI n b ↑n)) 0 = getBinI n b := by
  rw [offsetBin_compose n b ↑n 0 hn]
  have hzero : (↑n : Int) + 0 = 0 + ↑n := by omega
  rw [hzero, getOffsetBinI_periodic_offset n b 0 hn]
  exact getOffsetBinI_zero_offset n b hn

/-- **Lower bound commutes with rotation composition**:
    The lower bound of the doubly-rotated bin (by `k1` then `k2`) equals the lower bound
    computed directly at angle `b - k1 - k2`.

    This is the main system-level correctness property: after two consecutive frame rotations,
    the lower bound still correctly identifies the angular sector boundary. -/
theorem lowerBound_of_composed_offset (n : Nat) (b k1 k2 a : Int) (hn : 0 < n) :
    getLowerBoundI n (↑(getOffsetBinI n (↑(getOffsetBinI n b k1)) k2)) a =
    getLowerBoundI n (b - (k1 + k2)) a := by
  rw [offsetBin_compose n b k1 k2 hn]
  exact lowerBound_of_offsetBin n b (k1 + k2) a hn

/-! ## Sanity-check examples -/

-- With n = 4 bins (90°/bin), 36 half-bin units per full circle:
-- Rotation by 1 bin, then by 2 bins = rotation by 3 bins
example : getOffsetBinI 4 (↑(getOffsetBinI 4 (0:Int) 1)) 2 = getOffsetBinI 4 (0:Int) 3 := by
  native_decide

-- Rotation by 2 and then by -2 = identity
example : getOffsetBinI 4 (↑(getOffsetBinI 4 (3:Int) 2)) (-2) = getBinI 4 (3:Int) := by
  native_decide

-- Lower bound of bin containing angle 10 (n=4) = lower bound of angle 10
example : getLowerBoundI 4 (↑(getBinI 4 10)) 0 = getLowerBoundI 4 10 0 := by
  native_decide

-- Lower bound after rotation: offset_bin(7, n=4, k=2) = 1; lower bound of bin 1 = bin 1's lb
example : getLowerBoundI 4 (↑(getOffsetBinI 4 (7:Int) 2)) 0 = getLowerBoundI 4 (7 - 2) 0 := by
  native_decide

end PX4.CollisionPrev
