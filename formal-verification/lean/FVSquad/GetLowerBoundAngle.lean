/-!
# `get_lower_bound_angle` — Formal Verification

🔬 *Lean Squad automated formal verification.*

- **C++ source**: `src/lib/collision_prevention/ObstacleMath.cpp`
- **Informal spec**: `formal-verification/specs/get_lower_bound_angle_informal.md`

## C++ reference

```cpp
float get_lower_bound_angle(int bin, float bin_width, float angle_offset) {
    bin = wrap_bin(bin, 360 / bin_width);
    return wrap_360(bin * bin_width + angle_offset - bin_width / 2.f);
}
```

The function returns the **lower angular boundary** of bin `bin`'s sector (degrees,
wrapped into `[0°, 360°)`). With `n = 360 / bin_width` bins:
- Each bin `b` covers the angular sector `[lower_b, lower_b + bin_width)`.
- The centre of bin `b` is at `b * bin_width + angle_offset` (mod 360°).
- The lower bound is one half-width *before* the centre.

## Integer model

We use **half-bin units** to avoid non-integer arithmetic:
- The full 360° circle = `2n` half-bin units.
- Bin `b` has centre at `2*(b mod n) + a` half-bin units (where `a` = offset in half-bin units).
- Bin `b` has lower bound at `2*(b mod n) + a - 1` half-bin units.

```
getLowerBoundI n b a = (2 * (b % n) + a - 1) % (2 * n)
```

This captures the full semantics when `angle_offset` is a multiple of `bin_width / 2`.

## Approximations / out of scope

- **IEEE 754 float semantics**: NaN, infinity, and rounding are not modelled.
- **Non-integer `bin_width / 2`**: the integer model works exactly when `angle_offset`
  is an integer multiple of `bin_width / 2`.  The C++ computation with irrational
  offsets or non-dividing widths introduces rounding not captured here.
- **`360 / bin_width` must be integer**: the model assumes `n` is a positive integer
  such that `n * bin_width = 360`. In practice PX4 uses values like 2, 5, 10, 45
  that always divide 360.
-/

namespace PX4.LowerBound

/-! ## Helper lemmas -/

/-- `((x + 2) % (2n)).toNat = (x.toNat + 2) % (2n)` for `x ≥ 0`. -/
private theorem toNat_mod_add2 (x : Int) (n : Nat) (hx : 0 ≤ x) (hn : 0 < n) :
    ((x + 2) % (2 * ↑n)).toNat = (x.toNat + 2) % (2 * n) := by
  rw [Int.toNat_emod (by omega) (by omega : (0:Int) ≤ 2 * ↑n)]
  rw [Int.toNat_add hx (by omega)]
  simp [Int.toNat_mul]

/-- `(x % m + 1) % m = (x + 1) % m` for `m > 1`. -/
private theorem emod_succ (x m : Int) (hm : 1 < m) : (x % m + 1) % m = (x + 1) % m := by
  rw [Int.add_emod x 1 m]
  rw [Int.emod_eq_of_lt (by omega : (0 : Int) ≤ 1) (by omega : (1 : Int) < m)]

/-- `(-1) % m = m - 1` for `m > 1`. -/
private theorem emod_neg_one (m : Int) (hm : 1 < m) : (-1 : Int) % m = m - 1 := by
  have step : (-1 : Int) = (m - 1) + (-1) * m := by omega
  rw [step, Int.add_mul_emod_self_right]
  exact Int.emod_eq_of_lt (by omega) (by omega)

/-- Key congruence: `(2 * (b % n) + a - 1) % (2n) = (2 * b + a - 1) % (2n)`.
    Reduces the modular bin index to the raw integer value. -/
private theorem modeq_two (n : Nat) (b a : Int) :
    (2 * (b % ↑n) + a - 1) % (2 * ↑n) = (2 * b + a - 1) % (2 * ↑n) := by
  have hk : b % ↑n + ↑n * (b / ↑n) = b := Int.emod_add_mul_ediv b ↑n
  have hmul : (b / ↑n) * (2 * ↑n) = 2 * (↑n * (b / ↑n)) := by
    rw [Int.mul_left_comm _ 2 ↑n, Int.mul_comm _ ↑n]
  have hmul_neg : (-(b / ↑n)) * (2 * ↑n) = -(2 * (↑n * (b / ↑n))) := by
    rw [Int.neg_mul, hmul]
  have step : 2 * (b % ↑n) + a - 1 = 2 * b + a - 1 + (-(b / ↑n)) * (2 * ↑n) := by
    rw [hmul_neg]; omega
  rw [step, Int.add_mul_emod_self_right]

/-- Int version of the consecutive property:
    `(2*((b+1)%n)+a-1) % (2n) = ((2*(b%n)+a-1)%(2n) + 2) % (2n)`. -/
private theorem consecutive_Int (n : Nat) (b a : Int) :
    (2 * ((b + 1) % ↑n) + a - 1) % (2 * ↑n) =
    ((2 * (b % ↑n) + a - 1) % (2 * ↑n) + 2) % (2 * ↑n) := by
  have lhs : (2 * ((b + 1) % ↑n) + a - 1) % (2 * ↑n) = (2 * b + a + 1) % (2 * ↑n) := by
    rw [modeq_two n (b + 1) a]; congr 1; omega
  have rhs : ((2 * (b % ↑n) + a - 1) % (2 * ↑n) + 2) % (2 * ↑n) = (2 * b + a + 1) % (2 * ↑n) := by
    rw [show (2 * (b % ↑n) + a - 1) % (2 * ↑n) = (2 * b + a - 1) % (2 * ↑n) from
          modeq_two n b a]
    rw [Int.add_emod _ 2, Int.emod_emod_of_dvd _ (Int.dvd_refl _), ← Int.add_emod]
    congr 1; omega
  rw [lhs, rhs]

/-! ## Core definition -/

/-- **Integer lower-bound model**.

    Returns the lower angular boundary of bin `b` in a `n`-bin circle,
    in **half-bin units** (1 unit = `bin_width / 2`).

    - Full circle = `2n` half-bin units.
    - `b` is first wrapped to `[0, n)` via `b % n`.
    - The centre of bin `b` is at `2*(b % n) + a` half-bin units (where `a` is the
      angle offset in half-bin units).
    - The lower bound is one unit *before* the centre: `2*(b % n) + a − 1`.
    - Result is taken mod `2n` to stay in `[0, 2n)`. -/
def getLowerBoundI (n : Nat) (b a : Int) : Nat :=
  ((2 * (b % n) + a - 1) % (2 * n)).toNat

/-! ## Properties -/

/-- The lower bound is always in `[0, 2n)`.
    In degrees: result ∈ `[0°, 360°)` since each unit is `bin_width / 2`. -/
theorem getLowerBoundI_range (n : Nat) (b a : Int) (hn : 0 < n) :
    getLowerBoundI n b a < 2 * n := by
  unfold getLowerBoundI
  have hnn : (0 : Int) ≤ (2 * (b % ↑n) + a - 1) % (2 * ↑n) :=
    Int.emod_nonneg _ (by omega)
  have hlt : (2 * (b % ↑n) + a - 1) % (2 * ↑n) < 2 * ↑n :=
    Int.emod_lt_of_pos _ (by omega)
  omega

/-- **Periodicity over bins**: shifting `b` by a full circle (`n` bins) leaves the
    lower bound unchanged.
    Models: `get_lower_bound_angle(bin + n, bw, off) = get_lower_bound_angle(bin, bw, off)`. -/
theorem getLowerBoundI_periodic_bin (n : Nat) (b a : Int) :
    getLowerBoundI n (b + n) a = getLowerBoundI n b a := by
  unfold getLowerBoundI
  congr 1
  rw [modeq_two n (b + n) a, modeq_two n b a]
  have step : 2 * (b + ↑n) + a - 1 = 2 * b + a - 1 + 1 * (2 * ↑n) := by omega
  rw [step, Int.add_mul_emod_self_right]

/-- **Periodicity over offset**: shifting the angle offset by a full circle
    (`2n` half-bin units = 360°) leaves the lower bound unchanged. -/
theorem getLowerBoundI_periodic_offset (n : Nat) (b a : Int) :
    getLowerBoundI n b (a + 2 * n) = getLowerBoundI n b a := by
  unfold getLowerBoundI
  congr 1
  have step : 2 * (b % ↑n) + (a + 2 * ↑n) - 1 = 2 * (b % ↑n) + a - 1 + 1 * (2 * ↑n) := by
    omega
  rw [step, Int.add_mul_emod_self_right]

/-- **Zero offset, bin 0**: the lower bound of bin 0 with offset 0 is `2n − 1`
    (the last half-bin unit, i.e. `360° − bin_width/2`).

    Bin 0's centre is at 0° and its left edge is at −bin_width/2 = 360° − bin_width/2. -/
theorem getLowerBoundI_zero_zero (n : Nat) (hn : 1 < n) :
    getLowerBoundI n 0 0 = 2 * n - 1 := by
  unfold getLowerBoundI
  rw [show (0 : Int) % ↑n = 0 from Int.zero_emod ↑n]
  rw [show 2 * (0 : Int) + 0 - 1 = -1 from by omega]
  rw [emod_neg_one (2 * ↑n) (by omega)]
  omega

/-- **Consecutive bins**: the lower bound of bin `b+1` equals `(getLowerBoundI n b a + 2) % (2n)`.
    Consecutive lower bounds differ by exactly one bin width (2 half-bin units). -/
theorem getLowerBoundI_consecutive (n : Nat) (b a : Int) (hn : 0 < n) :
    getLowerBoundI n (b + 1) a = (getLowerBoundI n b a + 2) % (2 * n) := by
  unfold getLowerBoundI
  have hnn := Int.emod_nonneg (2 * (b % ↑n) + a - 1) (by omega : (2 * ↑n : Int) ≠ 0)
  have hint := consecutive_Int n b a
  -- hint : (2*((b+1)%n)+a-1)%(2n) = ((2*(b%n)+a-1)%(2n) + 2) % (2n)
  rw [hint]
  exact toNat_mod_add2 _ n hnn hn

/-- **Centre relation**: the bin centre is one unit above the lower bound.
    `getLowerBoundI n b a + 1` is congruent to the bin centre `2*(b % n) + a` modulo `2n`. -/
theorem getLowerBoundI_centre_relation (n : Nat) (b a : Int) (hn : 1 < n) :
    (getLowerBoundI n b a + 1) % (2 * n) = (2 * (b % n) + a) % (2 * n) := by
  unfold getLowerBoundI
  have hnn := Int.emod_nonneg (2 * (b % ↑n) + a - 1) (by omega : (2 * ↑n : Int) ≠ 0)
  rw [Int.toNat_of_nonneg hnn]
  push_cast
  rw [emod_succ _ _ (by omega)]
  congr 1; omega

/-- **Offset shift**: adding `2` to the angle offset advances the lower bound by `2` (mod `2n`). -/
theorem getLowerBoundI_offset_shift (n : Nat) (b a : Int) (hn : 0 < n) :
    getLowerBoundI n b (a + 2) = (getLowerBoundI n b a + 2) % (2 * n) := by
  unfold getLowerBoundI
  have hnn := Int.emod_nonneg (2 * (b % ↑n) + a - 1) (by omega : (2 * ↑n : Int) ≠ 0)
  have hint : (2 * (b % ↑n) + (a + 2) - 1) % (2 * ↑n) =
      ((2 * (b % ↑n) + a - 1) % (2 * ↑n) + 2) % (2 * ↑n) := by
    rw [Int.add_emod _ 2, Int.emod_emod_of_dvd _ (Int.dvd_refl _), ← Int.add_emod]
    congr 1; omega
  rw [hint]
  exact toNat_mod_add2 _ n hnn hn

/-- **Bin-0 lower bound with offset `a = 2`**:
    When `a = 2` and bin = 0, the lower bound is `1` (one half-bin unit past 0). -/
theorem getLowerBoundI_zero_offset2 (n : Nat) (hn : 1 < n) :
    getLowerBoundI n 0 2 = 1 := by
  unfold getLowerBoundI
  rw [show (0 : Int) % ↑n = 0 from Int.zero_emod ↑n]
  rw [show 2 * (0 : Int) + 2 - 1 = 1 from by omega]
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  simp

/-! ## Sanity-check examples

With n = 4 (90°/bin, so `bin_width = 90`, half-bin unit = 45°):
- Bin 0, offset 0: lower bound = 2*4-1 = 7 units = 315°
- Bin 1, offset 0: lower bound = 2*1-1 = 1 unit = 45°
- Bin 2, offset 0: lower bound = 2*2-1 = 3 units = 135°
- Bin 3, offset 0: lower bound = 2*3-1 = 5 units = 225°
-/

#eval getLowerBoundI 4 0 0  -- 7  (315°)
#eval getLowerBoundI 4 1 0  -- 1  (45°)
#eval getLowerBoundI 4 2 0  -- 3  (135°)
#eval getLowerBoundI 4 3 0  -- 5  (225°)

-- Periodicity: bin 0 and bin 4 give the same result
#eval getLowerBoundI 4 4 0  -- 7  (same as bin 0)
#eval getLowerBoundI 4 (-1) 0  -- 5  (same as bin 3)

-- With offset a = 2 (offset by bin_width / 2):
#eval getLowerBoundI 4 0 2  -- 1  (45°)
#eval getLowerBoundI 4 1 2  -- 3  (135°)

-- 36-bin model (10°/bin, half-bin = 5°, circle = 72 units):
-- Bin 0, offset 0: lower bound = 71 units = 355°
-- Bin 1, offset 0: lower bound = 1 unit = 5°
#eval getLowerBoundI 36 0 0   -- 71 (355°)
#eval getLowerBoundI 36 1 0   -- 1  (5°)
#eval getLowerBoundI 36 35 0  -- 69 (345°)
#eval getLowerBoundI 36 36 0  -- 71 (same as bin 0, wraps)

end PX4.LowerBound
