/-!
# `get_bin_at_angle` / `get_offset_bin_index` — Formal Verification

🔬 *Lean Squad automated formal verification.*

- **C++ source**: `src/lib/collision_prevention/ObstacleMath.cpp`
- **Informal spec**: `formal-verification/specs/get_bin_at_angle_informal.md`

## C++ reference

```cpp
// Returns bin index at a given angle from the 0th bin
// bin_width: width of a bin in degrees; angle: clockwise angle in degrees
int get_bin_at_angle(float bin_width, float angle) {
    int bin_at_angle = (int)round(matrix::wrap(angle, 0.f, 360.f) / bin_width);
    return wrap_bin(bin_at_angle, 360 / bin_width);
}

// Returns bin index after rotating by an angle offset
int get_offset_bin_index(int bin, float bin_width, float angle_offset) {
    int offset = get_bin_at_angle(bin_width, angle_offset);
    return wrap_bin(bin - offset, 360 / bin_width);
}
```

## Model

We provide **integer** models that capture the exact behaviour when angles are
integer multiples of `bin_width` (no floating-point rounding arises):

- **`getBinI n k`** — bin index of angle `k` (measured in integer bin units)
  in a `n`-bin circle. Collapses to `k mod n` since `wrap_360` + `round` + `wrap_bin`
  compose to exact integer modular reduction for integer-aligned angles.

- **`getOffsetBinI n b k_offset`** — offset bin index of bin `b` after rotating
  the reference frame by `k_offset` bin units. Implements a **rotation** on the
  bin circle: equivalent to `(b - k_offset) mod n`.

## Key result

`getOffsetBinI_eq_getBinI_sub` (theorem 9): the offset function is a pure subtraction
modulo `n`. Combined with `getBinI_range`, this guarantees:
- Result is always in `[0, n)` (no out-of-bounds bin index)
- Rotation is invertible: `getOffsetBinI n (b + k) n k = getBinI n b`
- Composition: two rotations add

## Approximations / out of scope

- **Float rounding**: the C++ `round()` and `matrix::wrap` involve floating-point
  arithmetic. The model is exact only for angles that are exact integer multiples
  of `bin_width`. For general float angles, the model gives the *intended* bin
  (what a caller with exact arithmetic would compute).
- **Float `bin_width`**: the precondition `n_bins * bin_width = 360` need not hold
  exactly in floating point. The integer `n` in the model is `360 / bin_width` rounded.
- **`get_lower_bound_angle`**: involves `bin_width / 2` (half-integer boundaries in
  degree units). Modelled separately in `GetLowerBoundAngle.lean`.
-/

namespace PX4.BinAngle

/-! ## Integer bin models -/

/-- **Integer model** of `get_bin_at_angle` for exact integer-angle-multiple inputs.

    Returns the bin index `k mod n` in `[0, n)` for angle `k` (measured in bin units).

    **Rationale**: For angle `a = k * bin_width` with `n = 360 / bin_width`:
    - `wrap_360(a) = (k mod n) * bin_width`  (since `360 = n * bin_width`)
    - `round(wrap_360(a) / bin_width) = k mod n`  (exact integer for integer `k`)
    - `wrap_bin(k mod n, n) = k mod n`  (already in range)

    So the full pipeline collapses to `k mod n`, implemented via `Int.emod`
    (Euclidean remainder, always `≥ 0` for positive divisor). -/
def getBinI (n : Nat) (k : Int) : Nat := (k % n).toNat

/-- **Integer model** of `get_offset_bin_index`.

    Returns the bin index of bin `b` rotated by `k_offset` bin units: `(b - k_offset) mod n`.

    This models looking at bin `b` from a reference frame that has been rotated by
    `k_offset` bins clockwise — equivalent to subtracting the offset from the bin angle. -/
def getOffsetBinI (n : Nat) (b k_offset : Int) : Nat :=
  getBinI n (b - getBinI n k_offset)

/-! ## Properties of `getBinI` -/

/-- `getBinI` always returns a value in `[0, n)`.
    Formally: the bin circle has exactly `n` distinct positions. -/
theorem getBinI_range (n : Nat) (k : Int) (hn : 0 < n) : getBinI n k < n := by
  unfold getBinI
  have h1 : 0 ≤ k % n := Int.emod_nonneg k (by omega)
  have h2 : k % n < n := Int.emod_lt_of_pos k (by omega)
  omega

/-- Angle `0` maps to bin `0`. -/
theorem getBinI_zero (n : Nat) : getBinI n 0 = 0 := by
  unfold getBinI; simp [Int.zero_emod]

/-- If the angle `k` is already in `[0, n)`, `getBinI` returns `k.toNat` unchanged. -/
theorem getBinI_in_range (n : Nat) (k : Int) (h1 : 0 ≤ k) (h2 : k < n) :
    getBinI n k = k.toNat := by
  unfold getBinI
  rw [Int.emod_eq_of_lt h1 (by exact_mod_cast h2)]

/-- Shifting the angle by one full circle (`n` bins) does not change the bin.
    Models `get_bin_at_angle(bw, angle + 360) = get_bin_at_angle(bw, angle)`. -/
theorem getBinI_periodic (n : Nat) (k : Int) : getBinI n (k + n) = getBinI n k := by
  unfold getBinI; congr 1; exact Int.add_emod_right k n

/-- Shifting by any integer multiple of `n` bins is transparent. -/
theorem getBinI_periodic_k (n : Nat) (k j : Int) : getBinI n (k + j * n) = getBinI n k := by
  unfold getBinI; congr 1; exact Int.add_mul_emod_self_right k j n

/-- `getBinI` is idempotent: the bin of a bin index is the bin index itself. -/
theorem getBinI_idempotent (n : Nat) (k : Int) (hn : 0 < n) :
    getBinI n (getBinI n k) = getBinI n k := by
  unfold getBinI
  have h1 : 0 ≤ k % n := Int.emod_nonneg k (by omega)
  have h2 : k % n < n := Int.emod_lt_of_pos k (by omega)
  rw [Int.toNat_of_nonneg h1]
  congr 1
  exact Int.emod_eq_of_lt h1 h2

/-! ## Properties of `getOffsetBinI` -/

/-- `getOffsetBinI` always returns a value in `[0, n)`. -/
theorem getOffsetBinI_range (n : Nat) (b k : Int) (hn : 0 < n) :
    getOffsetBinI n b k < n := getBinI_range n _ hn

/-- Zero offset is identity: `getOffsetBinI n b 0 = getBinI n b`. -/
theorem getOffsetBinI_zero_offset (n : Nat) (b : Int) (_hn : 0 < n) :
    getOffsetBinI n b 0 = getBinI n b := by
  unfold getOffsetBinI
  rw [getBinI_zero n]
  simp

/-- **KEY THEOREM**: `getOffsetBinI` is equivalent to modular subtraction.
    The offset bin index of `b` with offset `k` equals `getBinI n (b - k)`.
    This shows `getOffsetBinI` implements a **rotation** by `k` bins on the circle. -/
theorem getOffsetBinI_eq_getBinI_sub (n : Nat) (b k : Int) (hn : 0 < n) :
    getOffsetBinI n b k = getBinI n (b - k) := by
  unfold getOffsetBinI getBinI
  have h1 : 0 ≤ k % n := Int.emod_nonneg k (by omega)
  rw [Int.toNat_of_nonneg h1]
  congr 1
  rw [Int.sub_emod b (k % n) n, Int.sub_emod b k n]
  congr 2
  exact Int.emod_eq_of_lt h1 (Int.emod_lt_of_pos k (by omega))

/-- Rotating the reference frame by one full circle (n bins) is transparent. -/
theorem getOffsetBinI_periodic_offset (n : Nat) (b k : Int) (hn : 0 < n) :
    getOffsetBinI n b (k + n) = getOffsetBinI n b k := by
  rw [getOffsetBinI_eq_getBinI_sub _ _ _ hn, getOffsetBinI_eq_getBinI_sub _ _ _ hn]
  unfold getBinI; congr 1
  rw [show b - (k + n) = b - k + (-1) * n from by omega]
  exact Int.add_mul_emod_self_right (b - k) (-1) n

/-- Shifting the bin by a full circle (n bins) does not change the offset result. -/
theorem getOffsetBinI_periodic_bin (n : Nat) (b k : Int) (hn : 0 < n) :
    getOffsetBinI n (b + n) k = getOffsetBinI n b k := by
  rw [getOffsetBinI_eq_getBinI_sub _ _ _ hn, getOffsetBinI_eq_getBinI_sub _ _ _ hn]
  unfold getBinI; congr 1
  rw [show b + n - k = b - k + 1 * n from by omega]
  exact Int.add_mul_emod_self_right (b - k) 1 n

/-- `getOffsetBinI n k k = 0`: when the bin equals the offset angle, the
    result is bin 0 (the forward direction of the rotated frame). -/
theorem getOffsetBinI_self (n : Nat) (k : Int) (hn : 0 < n) :
    getOffsetBinI n k k = 0 := by
  rw [getOffsetBinI_eq_getBinI_sub _ _ _ hn, Int.sub_self]
  exact getBinI_zero n

/-- **Round-trip**: converting back from offset bin to angle bin recovers the original.
    `getBinI n (getOffsetBinI n b k + k) = getBinI n b` (mod `n`). -/
theorem getOffsetBinI_inverse (n : Nat) (b k : Int) (hn : 0 < n) :
    getBinI n ((getOffsetBinI n b k : Int) + k) = getBinI n b := by
  rw [getOffsetBinI_eq_getBinI_sub _ _ _ hn]
  unfold getBinI
  have h1 : 0 ≤ (b - k) % n := Int.emod_nonneg (b - k) (by omega)
  rw [Int.toNat_of_nonneg h1]
  congr 1
  rw [Int.add_emod ((b - k) % n) k n]
  rw [Int.emod_eq_of_lt h1 (Int.emod_lt_of_pos (b - k) (by omega))]
  rw [← Int.add_emod (b - k) k n]
  simp [Int.sub_add_cancel]

/-! ## Sanity-check examples -/

-- 36 bins × 10°/bin = 360°; bin 0 = North (0°)
#eval getBinI 36 0    -- 0  (0° = bin 0)
#eval getBinI 36 10   -- 10 (10 bin-units)
#eval getBinI 36 35   -- 35 (last bin before wrapping)
#eval getBinI 36 36   -- 0  (360° = bin 0 again, wraps)
#eval getBinI 36 (-1) -- 35 (−1 bin = bin 35, wraps)

-- Offset bin: 10° sensor rotated by 5 bin-units → bin 5
#eval getOffsetBinI 36 10 5   -- 5
-- Offset bin: 3° with 5 bin-unit offset → bin 34 (3 − 5 = −2 → 34)
#eval getOffsetBinI 36 3 5    -- 34
-- Zero offset is identity
#eval getOffsetBinI 36 7 0    -- 7

end PX4.BinAngle
