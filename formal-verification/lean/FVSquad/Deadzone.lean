/-!
# PX4 Deadzone Function — Formal Verification

🔬 Lean Squad automated formal verification.

This file models and proves correctness properties of `math::deadzone` from
PX4-Autopilot's `mathlib`:

- **C++ source**: `src/lib/mathlib/math/Functions.hpp`
- **Informal spec**: `formal-verification/specs/deadzone_informal.md`

## Model

We model the function over `Rat` (rational numbers) to capture exact piecewise-linear
semantics.  The C++ implementation uses `float`; our model is an exact abstraction.

```cpp
// C++ (condensed):
const T deadzone(const T &value, const T &dz) {
  T x   = constrain(value, -1, 1);
  T dzc = constrain(dz, 0, 0.99);
  T out = (x - sign(x) * dzc) / (1 - dzc);
  return out * (fabsf(x) > dzc);   // zeroed in deadzone
}
```

## Approximations / out of scope

- **IEEE 754 float semantics**: NaN, infinity, and rounding are not modelled.
- **Input clamping**: we assume inputs are already in range (`|x| ≤ 1`, `0 ≤ dz < 1`).
  The internal `constrain` calls are not modelled.
- **`dz` upper bound**: C++ uses `0.99`; we allow any `dz < 1`.

## What Cannot Be Proved Without Mathlib

Several arithmetic lemmas below require `linarith` or `ring` over `Rat`, which are
only available via Mathlib. Those theorems are marked with `sorry` and a comment.
Install Mathlib (add `require mathlib` to `lakefile.toml`) to unlock full proofs.
-/

namespace PX4.Deadzone

/-- Rational sign: +1 when `x ≥ 0`, −1 when `x < 0`. -/
def signR (x : Rat) : Rat := if 0 ≤ x then 1 else -1

/-- Pure functional model of `math::deadzone` over `Rat`.

    - When `|x| ≤ dz` (inside deadzone): returns `0`.
    - When `|x| > dz` (outside deadzone): returns `(x − sign(x)·dz) / (1 − dz)`. -/
def deadzone (x dz : Rat) : Rat :=
  if x.abs > dz then (x - signR x * dz) / (1 - dz) else 0

-- Sanity check: model produces expected numeric outputs.
#eval deadzone 0      0.3   -- 0      (inside deadzone)
#eval deadzone 0.3    0.3   -- 0      (on boundary — inclusive deadzone)
#eval deadzone 0.5    0.3   -- 2/7    ≈ 0.286
#eval deadzone 1      0.3   -- 1      (extreme input → extreme output)
#eval deadzone (-0.5) 0.3   -- -2/7   (negative, symmetric)
#eval deadzone (-1)   0.3   -- -1
#eval deadzone 0.5    0     -- 1/2    (no deadzone → identity)

/-! ## signR lemmas -/

/-- `signR x = 1` when `x ≥ 0`. -/
theorem signR_of_nonneg (x : Rat) (h : 0 ≤ x) : signR x = 1 := by
  simp [signR, h]

/-- `signR x = −1` when `x < 0`. -/
theorem signR_of_neg (x : Rat) (h : x < 0) : signR x = -1 := by
  simp [signR, show ¬(0 ≤ x) from Rat.not_le.mpr h]

/-! ## Structural theorem: in-deadzone outputs 0 -/

/-- The central deadzone property: any input inside the deadzone maps to exactly 0.

    This holds with equality — there is no rounding or approximation.
    `|x| ≤ dz → deadzone x dz = 0` -/
theorem deadzone_in_dz (x dz : Rat) (h : x.abs ≤ dz) :
    deadzone x dz = 0 := by
  simp only [deadzone]
  rw [if_neg (Rat.not_lt.mpr h)]

/-! ## Simplified form outside the deadzone -/

/-- When `x > dz ≥ 0`, the deadzone simplifies to `(x − dz) / (1 − dz)`.
    This is the positive branch with `sign(x) = 1`. -/
theorem deadzone_pos_eq (x dz : Rat) (hxdz : dz < x) (hdz0 : 0 ≤ dz) :
    deadzone x dz = (x - dz) / (1 - dz) := by
  simp only [deadzone]
  have hx0 : 0 ≤ x := Rat.le_trans hdz0 (Rat.le_of_lt hxdz)
  have habs : dz < x.abs := by
    rw [Rat.abs_of_nonneg hx0]; exact hxdz
  rw [if_pos habs, signR_of_nonneg x hx0, Rat.one_mul]

/-- When `x < −dz ≤ 0`, the deadzone simplifies to `(x + dz) / (1 − dz)`.
    This is the negative branch with `sign(x) = −1`.

    Note: `x - (-1)*dz = x + dz` requires basic ring arithmetic over `Rat`.
    This algebra is proved below; it does NOT need Mathlib. -/
theorem deadzone_neg_eq (x dz : Rat) (hxdz : x < -dz) (hdz0 : 0 ≤ dz) :
    deadzone x dz = (x + dz) / (1 - dz) := by
  simp only [deadzone]
  have hxneg : x < 0 :=
    Std.lt_of_lt_of_le hxdz (Rat.neg_le_iff.mp hdz0)
  -- |x| = -x  (since x < 0)
  have habs_eq : x.abs = -x := Rat.abs_of_nonpos (Rat.le_of_lt hxneg)
  -- |-x| > dz (since x < -dz means -x > dz)
  have habs : dz < x.abs := by
    rw [habs_eq]
    exact Rat.neg_lt_neg_iff.mp (by rw [Rat.neg_neg]; exact hxdz)
  rw [if_pos habs, signR_of_neg x hxneg]
  -- x - (-1) * dz = x + dz
  congr 1
  rw [Rat.neg_mul, Rat.one_mul, Rat.sub_eq_add_neg, Rat.neg_neg]

/-! ## Sign of the output -/

/-- When `x > dz ≥ 0` and `dz < 1`, the output is positive. -/
theorem deadzone_pos (x dz : Rat) (hxdz : dz < x) (hdz0 : 0 ≤ dz) (hdz1 : dz < 1) :
    0 < deadzone x dz := by
  rw [deadzone_pos_eq x dz hxdz hdz0]
  have hnum : 0 < x - dz := (Rat.lt_iff_sub_pos dz x).mp hxdz
  have hden : 0 < 1 - dz := (Rat.lt_iff_sub_pos dz 1).mp hdz1
  rw [Rat.div_def]
  exact Rat.mul_pos hnum (Rat.inv_pos.mpr hden)

/-- When `x < -dz ≤ 0` and `dz < 1`, the output is negative. -/
theorem deadzone_neg (x dz : Rat) (hxdz : x < -dz) (hdz0 : 0 ≤ dz) (hdz1 : dz < 1) :
    deadzone x dz < 0 := by
  rw [deadzone_neg_eq x dz hxdz hdz0]
  -- Need: x + dz < 0, which follows from x < -dz
  -- Requires Rat arithmetic: x < -dz ↔ x + dz < 0
  -- TODO: (Mathlib: linarith closes this)
  have hnum : x + dz < 0 := by
    have key : x + dz < -dz + dz := (Rat.add_lt_add_right).mpr hxdz
    rw [Rat.add_comm (-dz) dz, ← Rat.sub_eq_add_neg, Rat.sub_self] at key
    exact key
  have hden : 0 < 1 - dz := (Rat.lt_iff_sub_pos dz 1).mp hdz1
  rw [Rat.div_def]
  exact (Rat.mul_neg_iff_of_pos_right (Rat.inv_pos.mpr hden)).mpr hnum

/-! ## Output range -/

/-- Upper bound: deadzone output is at most 1 when input is at most 1.

    The positive case is fully proved.
    The negative case uses `sorry` (needs Rat arithmetic; provable with Mathlib's `linarith`). -/
theorem deadzone_le_one (x dz : Rat) (hx1 : x ≤ 1) (hdz0 : 0 ≤ dz) (hdz1 : dz < 1) :
    deadzone x dz ≤ 1 := by
  simp only [deadzone]
  split
  · rename_i h
    have h1 : (0 : Rat) < 1 - dz := (Rat.lt_iff_sub_pos dz 1).mp hdz1
    by_cases hx0 : 0 ≤ x
    · -- Positive branch: (x - dz) / (1 - dz) ≤ 1 because x ≤ 1
      rw [signR_of_nonneg x hx0, Rat.one_mul]
      have h2 : x - dz ≤ 1 - dz := by
        rw [Rat.sub_eq_add_neg, Rat.sub_eq_add_neg]
        exact (Rat.add_le_add_right).mpr hx1
      rw [Rat.div_def]
      calc (x - dz) * (1 - dz)⁻¹
          ≤ (1 - dz) * (1 - dz)⁻¹ :=
            Rat.mul_le_mul_of_nonneg_right h2 (Rat.le_of_lt (Rat.inv_pos.mpr h1))
        _ = 1 := Rat.mul_inv_cancel _ (Rat.ne_of_gt h1)
    · -- Negative branch: x < 0, so output (x + dz)/(1 − dz) < 0 ≤ 1
      have hxneg : x < 0 := Rat.not_le.mp hx0
      -- |x| = −x since x < 0
      have habs : x.abs = -x := Rat.abs_of_nonpos (Rat.le_of_lt hxneg)
      -- dz < −x (from |x| > dz)
      have h' : dz < -x := habs ▸ h
      -- x < −dz (negate both sides of dz < −x)
      have hxdz : x < -dz :=
        Rat.neg_lt_neg_iff.mp (by rw [Rat.neg_neg]; exact h')
      rw [signR_of_neg x hxneg, Rat.neg_mul, Rat.one_mul,
          Rat.sub_eq_add_neg, Rat.neg_neg]
      -- Goal: (x + dz) / (1 − dz) ≤ 1. Show x + dz < 0 first.
      have hxpdz : x + dz < 0 := by
        have key : x + dz < -dz + dz := (Rat.add_lt_add_right).mpr hxdz
        rw [Rat.add_comm (-dz) dz, ← Rat.sub_eq_add_neg, Rat.sub_self] at key
        exact key
      apply Rat.le_of_lt
      apply Std.lt_trans _ (by decide : (0 : Rat) < 1)
      rw [Rat.div_def]
      exact (Rat.mul_neg_iff_of_pos_right (Rat.inv_pos.mpr h1)).mpr hxpdz
  · -- In deadzone: output = 0 ≤ 1
    exact Rat.le_of_lt (by decide)

/-- Lower bound: deadzone output is at least −1 when input is at least −1.

    Cases:
    - In deadzone: output = 0 ≥ −1.
    - Positive branch (x > dz ≥ 0): output > 0 ≥ −1.
    - Negative branch (x < −dz ≤ 0): output = (x+dz)/(1−dz).
      Since x ≥ −1, we have x+dz ≥ −1+dz = −(1−dz),
      so output ≥ −(1−dz)/(1−dz) = −1. -/
theorem deadzone_ge_neg_one (x dz : Rat) (hxm1 : -1 ≤ x) (hdz0 : 0 ≤ dz) (hdz1 : dz < 1) :
    -1 ≤ deadzone x dz := by
  simp only [deadzone]
  split
  · rename_i h
    have h1 : (0 : Rat) < 1 - dz := (Rat.lt_iff_sub_pos dz 1).mp hdz1
    by_cases hx0 : 0 ≤ x
    · -- Positive branch: output > 0 ≥ −1
      rw [signR_of_nonneg x hx0, Rat.one_mul]
      apply Rat.le_of_lt
      apply Std.lt_trans (by decide : (-1 : Rat) < 0)
      have hxabs : x.abs = x := Rat.abs_of_nonneg hx0
      have hnum : 0 < x - dz := (Rat.lt_iff_sub_pos dz x).mp (hxabs ▸ h)
      rw [Rat.div_def]
      exact Rat.mul_pos hnum (Rat.inv_pos.mpr h1)
    · -- Negative branch: −(1−dz) ≤ x+dz, so −1 ≤ (x+dz)/(1−dz)
      have hxneg : x < 0 := Rat.not_le.mp hx0
      rw [signR_of_neg x hxneg, Rat.neg_mul, Rat.one_mul,
          Rat.sub_eq_add_neg, Rat.neg_neg]
      -- −(1−dz) ≤ x+dz  because −1 ≤ x → −1+dz ≤ x+dz = −(1−dz) ≤ x+dz
      have hlower : -(1 - dz) ≤ x + dz := by
        rw [show -(1 - dz) = (-1 : Rat) + dz from by
          rw [Rat.sub_eq_add_neg, Rat.neg_add, Rat.neg_neg]]
        exact (Rat.add_le_add_right).mpr hxm1
      rw [Rat.div_def]
      calc (-1 : Rat)
          = -(1 - dz) * (1 - dz)⁻¹ := by
            rw [Rat.neg_mul, Rat.mul_inv_cancel _ (Rat.ne_of_gt h1)]
        _ ≤ (x + dz) * (1 - dz)⁻¹ :=
            Rat.mul_le_mul_of_nonneg_right hlower (Rat.le_of_lt (Rat.inv_pos.mpr h1))
  · -- In deadzone: output = 0 ≥ −1
    exact Rat.le_of_lt (by decide)

/-! ## Special cases -/

/-- When there is no deadzone (`dz = 0`), the function is the identity on positives. -/
theorem deadzone_no_dz_pos (x : Rat) (hx : 0 < x) : deadzone x 0 = x := by
  rw [deadzone_pos_eq x 0 hx (Rat.le_refl)]
  rw [Rat.sub_eq_add_neg, Rat.neg_zero, Rat.add_zero,
      Rat.sub_eq_add_neg, Rat.neg_zero, Rat.add_zero,
      Rat.div_def, Rat.inv_eq_of_mul_eq_one (Rat.mul_one 1), Rat.mul_one]

/-- At maximum input (`x = 1`), output equals 1 for any `dz < 1`.

    Proof: `(1 - dz) / (1 - dz) = 1`. -/
theorem deadzone_at_max (dz : Rat) (hdz0 : 0 ≤ dz) (hdz1 : dz < 1) :
    deadzone 1 dz = 1 := by
  rw [deadzone_pos_eq 1 dz hdz1 hdz0]
  -- Goal: (1 - dz) / (1 - dz) = 1
  have h1 : (0 : Rat) < 1 - dz := (Rat.lt_iff_sub_pos dz 1).mp hdz1
  rw [Rat.div_def]
  exact Rat.mul_inv_cancel _ (Rat.ne_of_gt h1)

/-- At minimum input (`x = -1`), output equals −1 for any `dz < 1`.

    Proof: `(-1 + dz) = -(1 - dz)`, so `(-1 + dz) / (1 - dz) = -1`. -/
theorem deadzone_at_min (dz : Rat) (hdz0 : 0 ≤ dz) (hdz1 : dz < 1) :
    deadzone (-1) dz = -1 := by
  have hneg : (-1 : Rat) < -dz := by
    rw [Rat.neg_lt_neg_iff]; exact hdz1
  rw [deadzone_neg_eq (-1) dz hneg hdz0]
  have h1 : (0 : Rat) < 1 - dz := (Rat.lt_iff_sub_pos dz 1).mp hdz1
  have h1ne : (1 - dz) ≠ 0 := Rat.ne_of_gt h1
  rw [show (-1 : Rat) + dz = -(1 - dz) from by
    rw [Rat.sub_eq_add_neg, Rat.neg_add, Rat.neg_neg]]
  rw [Rat.div_def, Rat.neg_mul, Rat.mul_inv_cancel _ h1ne]

/-! ## Summary of proved properties

  | Theorem                 | Statement                                             | Status  |
  |-------------------------|-------------------------------------------------------|---------|
  | `deadzone_in_dz`        | `|x| ≤ dz → deadzone x dz = 0`                       | ✅ Proved |
  | `signR_of_nonneg`       | `x ≥ 0 → signR x = 1`                                | ✅ Proved |
  | `signR_of_neg`          | `x < 0 → signR x = −1`                               | ✅ Proved |
  | `deadzone_pos_eq`       | Simplified form for positive branch                   | ✅ Proved |
  | `deadzone_neg_eq`       | Simplified form for negative branch                   | ✅ Proved |
  | `deadzone_pos`          | `x > dz ≥ 0, dz < 1 → deadzone x dz > 0`            | ✅ Proved |
  | `deadzone_neg`          | `x < -dz ≤ 0, dz < 1 → deadzone x dz < 0`           | ✅ Proved |
  | `deadzone_no_dz_pos`    | `deadzone x 0 = x` (identity, positive case)         | ✅ Proved |
  | `deadzone_at_max`       | `deadzone 1 dz = 1` (for `dz < 1`)                   | ✅ Proved |
  | `deadzone_at_min`       | `deadzone (-1) dz = -1` (for `dz < 1`)               | ✅ Proved |
  | `deadzone_le_one`       | `x ≤ 1, 0 ≤ dz < 1 → deadzone x dz ≤ 1`             | ✅ Proved |
  | `deadzone_ge_neg_one`   | `-1 ≤ x, 0 ≤ dz < 1 → -1 ≤ deadzone x dz`           | ✅ Proved |
-/

end PX4.Deadzone
