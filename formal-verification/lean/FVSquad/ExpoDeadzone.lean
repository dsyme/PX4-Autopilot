import FVSquad.Expo
import FVSquad.Deadzone

/-!
# Formal Specification: expo_deadzone (Composed RC Curve)

🔬 Lean Squad automated formal verification.

This file models and proves correctness properties of `math::expo_deadzone` from
PX4-Autopilot's `mathlib`. The function **composes** deadzone (dead-band suppression)
with expo (cubic RC curve shaping):

  `expo_deadzone(v, e, dz) = expo(deadzone(v, dz), e)`

First the deadzone zeroes small stick inputs; then expo shapes the remaining range.

## Source
`src/lib/mathlib/math/Functions.hpp`:
```cpp
template<typename T>
const T expo_deadzone(const T &value, const T &e, const T &dz)
{
    return expo(deadzone(value, dz), e);
}
```

## Verification Status

| Theorem | Status | Notes |
|---------|--------|-------|
| `expoDeadzone_in_range` | ✅ | output always in [-1, 1] (unconditional) |
| `expoDeadzone_zero` | ✅ | in-deadzone input → output 0 |
| `expoDeadzone_e0` | ✅ | e=0 collapses to constrainRat(deadzone, -1, 1) |
| `expoDeadzone_e0_eq_deadzone` | ✅ | e=0 collapses to deadzone when input in range |
| `expoDeadzone_at_one` | ✅ | v=1 maps to 1 |
| `expoDeadzone_at_neg_one` | ✅ | v=-1 maps to -1 |
| `expoDeadzone_odd` | ✅ | anti-symmetry: expo_deadzone(-v,e,dz) = -expo_deadzone(v,e,dz) |
| `expoDeadzone_cubic` | ✅ | e=1 gives cubic of deadzone output |

## Modelling Notes

- All arithmetic is over `Rat` (exact rationals); float rounding is not modelled.
- `expoRat` and `constrainRat` are imported from `FVSquad.Expo`.
- `deadzone` and `signR` are imported from `FVSquad.Deadzone`.
- The C++ implementation internally calls `constrain` on each argument; our model
  delegates clamping to the sub-function models.
- IEEE 754 special values (NaN, ∞) and floating-point rounding are out of scope.
-/

open PX4.Deadzone

namespace PX4.ExpoDeadzone

/-! ## Model definition -/

/-- Rational model of `expo_deadzone`: apply deadzone then expo.

    `expoDeadzone v e dz = expoRat (deadzone v dz) e`

    - `v`:  input value (stick position, modelled over ℚ)
    - `e`:  expo curvature parameter `[0, 1]` (0 = linear, 1 = cubic)
    - `dz`: deadzone ratio `[0, 1)` (0 = none, 0.5 = half of range)
-/
def expoDeadzone (v e dz : Rat) : Rat :=
  expoRat (deadzone v dz) e

/-! ## Sanity checks -/

#eval expoDeadzone 0      (1/2) (3/10)  -- 0   : in deadzone
#eval expoDeadzone (3/10) (1/2) (3/10)  -- 0   : on deadzone boundary
#eval expoDeadzone 1      (1/2) (3/10)  -- 1   : maximum input
#eval expoDeadzone (-1)   (1/2) (3/10)  -- -1  : minimum input
#eval expoDeadzone (7/10) (1/2) (3/10)  -- positive output, shaped by expo
#eval expoDeadzone (1/2)  0     (3/10)  -- deadzone only (e=0)

/-! ## Helper: deadzone is an odd function -/

/-- Helper: `signR` negates when `v ≠ 0`. -/
private theorem signR_neg_of_ne_zero (v : Rat) (hv : v ≠ 0) : signR (-v) = -signR v := by
  by_cases hv0 : 0 ≤ v
  · have hv_pos : 0 < v := Rat.lt_of_le_of_ne hv0 (Ne.symm hv)
    rw [signR_of_nonneg v hv0]
    have hnv : -v < 0 := by
      have := Rat.neg_lt_neg_iff.mpr hv_pos; rwa [Rat.neg_zero] at this
    rw [signR_of_neg (-v) hnv]
  · have hv_neg : v < 0 := Rat.not_le.mp hv0
    rw [signR_of_neg v hv_neg]
    have hnv0 : 0 ≤ -v := by
      have := Rat.neg_le_neg (Rat.le_of_lt hv_neg); rwa [Rat.neg_zero] at this
    rw [signR_of_nonneg (-v) hnv0]
    rw [Rat.neg_neg]

/-- Helper: `deadzone` is an odd function when `dz ≥ 0`. -/
private theorem deadzone_neg_odd (v dz : Rat) (hdz : 0 ≤ dz) :
    deadzone (-v) dz = -deadzone v dz := by
  simp only [deadzone, Rat.abs_neg]
  by_cases h : v.abs > dz
  · rw [if_pos h, if_pos h]
    have hv_ne : v ≠ 0 := by
      intro hv0
      rw [hv0, Rat.abs_zero] at h
      exact absurd hdz (Rat.not_le.mpr h)
    rw [signR_neg_of_ne_zero v hv_ne]
    rw [Rat.div_def, Rat.div_def, Rat.neg_mul]
    have key : (-v - -(signR v * dz)) = -(v - signR v * dz) := by
      simp only [Rat.sub_eq_add_neg, Rat.neg_add, Rat.neg_neg]
    rw [key, ← Rat.neg_mul]
  · rw [if_neg h, if_neg h, Rat.neg_zero]

/-! ## Theorems -/

/-- **Range containment** (unconditional): the output is always in [-1, 1].

    This follows directly from `expo_in_range`: `expoRat` internally clamps its
    input to [-1, 1], so regardless of what `deadzone` returns, the output is bounded. -/
theorem expoDeadzone_in_range (v e dz : Rat) :
    -1 ≤ expoDeadzone v e dz ∧ expoDeadzone v e dz ≤ 1 :=
  expo_in_range (deadzone v dz) e

/-- **In-deadzone → zero**: if the absolute value of the input is within the deadzone,
    the output is exactly 0.  Composition of `deadzone_in_dz` and `expo_at_zero`. -/
theorem expoDeadzone_zero (v e dz : Rat) (h : v.abs ≤ dz) :
    expoDeadzone v e dz = 0 := by
  simp [expoDeadzone, deadzone_in_dz v dz h, expo_at_zero]

/-- **e = 0 collapses to constrained deadzone**: when the expo parameter is zero
    the function reduces to `constrainRat(deadzone(v, dz), -1, 1)`.
    (For inputs with |v| ≤ 1 and valid dz, this equals `deadzone v dz` exactly.) -/
theorem expoDeadzone_e0 (v dz : Rat) :
    expoDeadzone v 0 dz = constrainRat (deadzone v dz) (-1) 1 := by
  simp [expoDeadzone, expo_linear]

/-- **e = 0 equals deadzone** when input is in range and `dz` is valid.
    For `v ∈ [-1, 1]` and `dz ∈ [0, 1)`, `deadzone v dz ∈ [-1, 1]`, so the
    clamp in `expo_linear` is a no-op. -/
theorem expoDeadzone_e0_eq_deadzone (v dz : Rat)
    (hv1 : v ≤ 1) (hvm1 : -1 ≤ v)
    (hdz0 : 0 ≤ dz) (hdz1 : dz < 1) :
    expoDeadzone v 0 dz = deadzone v dz := by
  rw [expoDeadzone_e0]
  apply constrainRat_id
  · exact deadzone_ge_neg_one v dz hvm1 hdz0 hdz1
  · exact deadzone_le_one v dz hv1 hdz0 hdz1

/-- **Endpoint v = 1**: for any valid `dz`, input 1 maps to output 1.
    `deadzone 1 dz = 1` when `dz < 1`, and `expo 1 e = 1` for any `e`. -/
theorem expoDeadzone_at_one (e dz : Rat) (hdz0 : 0 ≤ dz) (hdz1 : dz < 1) :
    expoDeadzone 1 e dz = 1 := by
  simp [expoDeadzone, deadzone_at_max dz hdz0 hdz1, expo_at_pos_one]

/-- **Endpoint v = -1**: for any valid `dz`, input -1 maps to output -1.
    `deadzone (-1) dz = -1` when `dz < 1`, and `expo (-1) e = -1` for any `e`. -/
theorem expoDeadzone_at_neg_one (e dz : Rat) (hdz0 : 0 ≤ dz) (hdz1 : dz < 1) :
    expoDeadzone (-1) e dz = -1 := by
  have h := PX4.Deadzone.deadzone_at_min dz hdz0 hdz1
  simp [expoDeadzone, h, expo_at_neg_one]

/-- **Odd symmetry**: `expo_deadzone` is an odd function when `dz ≥ 0`.
    Both `deadzone` (odd for `dz ≥ 0`) and `expoRat` (unconditionally odd) preserve
    the anti-symmetry of the composition. -/
theorem expoDeadzone_odd (v e dz : Rat) (hdz : 0 ≤ dz) :
    expoDeadzone (-v) e dz = -expoDeadzone v e dz := by
  unfold expoDeadzone
  rw [deadzone_neg_odd v dz hdz]
  exact expo_odd (deadzone v dz) e

/-- **Cubic composition** (e = 1): `expo_deadzone` with full expo gives the cubic
    of the deadzone output.

    `expo_deadzone v 1 dz = constrainRat(deadzone v dz, -1, 1)³`

    where `a³ = a * a * a`.  This follows from `expo_cubic`. -/
theorem expoDeadzone_cubic (v dz : Rat) :
    let cx := constrainRat (PX4.Deadzone.deadzone v dz) (-1) 1
    expoDeadzone v 1 dz = cx * cx * cx := by
  simp only [expoDeadzone, expo_cubic]

/-! ## Summary

  | Theorem                     | Preconditions          | Statement                               |
  |-----------------------------|------------------------|-----------------------------------------|
  | `expoDeadzone_in_range`     | none                   | output ∈ [-1, 1]                        |
  | `expoDeadzone_zero`         | `|v| ≤ dz`             | output = 0                              |
  | `expoDeadzone_e0`           | none                   | output = constrainRat(dz_out, -1, 1)    |
  | `expoDeadzone_e0_eq_deadzone` | `|v|≤1, 0≤dz<1`    | output = deadzone v dz                  |
  | `expoDeadzone_at_one`       | `0 ≤ dz < 1`           | expoDeadzone 1 e dz = 1                 |
  | `expoDeadzone_at_neg_one`   | `0 ≤ dz < 1`           | expoDeadzone (-1) e dz = -1             |
  | `expoDeadzone_odd`          | `0 ≤ dz`               | expoDeadzone (-v) e dz = -expoDeadzone v e dz |
  | `expoDeadzone_cubic`        | none                   | e=1 → cubic of clamped deadzone output  |

-/

end PX4.ExpoDeadzone
