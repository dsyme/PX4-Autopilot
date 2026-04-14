import FVSquad.Expo
import FVSquad.Deadzone

/-!
# Expo+Deadzone Composition — Formal Verification

🔬 Lean Squad automated formal verification.

This file specifies and proves correctness properties of the combined
`expo(deadzone(v, dz), e)` pipeline used in PX4 RC input processing.

## Source

- `expo`:     `src/lib/mathlib/math/Functions.hpp` — `float expo(float value, float e)`
- `deadzone`: `src/lib/mathlib/math/Functions.hpp` — `const T deadzone(const T &value, const T &dz)`

In PX4, RC stick input is first passed through a deadzone (to ignore stick drift
near centre), then through an exponential curve (to adjust sensitivity):
```cpp
float expo_deadzone(float value, float e, float dz) {
    return expo(deadzone(value, dz), e);
}
```

## Verification Status

| Theorem | Status | Notes |
|---------|--------|-------|
| `expodz_in_dz`      | ✅ | Inside deadzone → exactly 0 |
| `expodz_in_range`   | ✅ | Output always ∈ [-1, 1] |
| `expodz_zero`       | ✅ | Zero input → zero output |
| `expodz_at_one`     | ✅ | Full deflection → 1 |
| `expodz_at_neg_one` | ✅ | Full negative deflection → -1 |
| `expodz_e0`         | ✅ | e=0: reduces to pure deadzone (linear) |
| `expodz_cubic`      | ✅ | e=1: deadzone output cubed |
| `expodz_no_dz`      | ✅ | dz=0: reduces to pure expo |
| `expodz_odd`        | ✅ | Odd symmetry: `expodz(-v, e, dz) = -expodz(v, e, dz)` |

## Modelling Notes

- All arithmetic is over `Rat` (exact rationals).
- `expoRat` and `constrainRat` are imported from `FVSquad.Expo` (root namespace).
- `PX4.Deadzone.deadzone` is imported from `FVSquad.Deadzone`.
- The deadzone parameter `dz` satisfies `0 ≤ dz < 1` in valid C++ usage.
  Where theorems need this, it is stated as a hypothesis.
- Theorems about range containment and zero/fixed-point behaviour hold unconditionally
  (they rely only on `expo_in_range` which clamps outputs to [-1,1]).
-/

open PX4.Deadzone

namespace PX4.ExpoDeadzone

/-- Combined expo-deadzone function: apply deadzone then expo curve.

    Models the RC input pipeline: `expo(deadzone(v, dz), e)`. -/
def expodz (v e dz : Rat) : Rat :=
  expoRat (deadzone v dz) e

/-!
## Theorems about zero behaviour
-/

/-- **Zero inside deadzone**: any input within the deadzone maps to exactly 0.

    For `|v| ≤ dz`, `deadzone v dz = 0`, so `expo(0, e) = 0`. -/
theorem expodz_in_dz (v e dz : Rat) (h : v.abs ≤ dz) :
    expodz v e dz = 0 := by
  simp only [expodz, deadzone_in_dz v dz h, expo_at_zero]

/-- **Zero at centre**: zero input gives zero output for any `dz ≥ 0`. -/
theorem expodz_zero (e dz : Rat) (h : 0 ≤ dz) :
    expodz 0 e dz = 0 := by
  apply expodz_in_dz
  rw [Rat.abs_of_nonneg (by native_decide : (0:Rat) ≤ 0)]
  exact h

/-!
## Range containment
-/

/-- **Range containment**: output always lies in `[-1, 1]` for any inputs.

    This holds unconditionally because `expoRat` always clamps its output. -/
theorem expodz_in_range (v e dz : Rat) :
    -1 ≤ expodz v e dz ∧ expodz v e dz ≤ 1 :=
  expo_in_range (deadzone v dz) e

/-!
## Fixed points at ±1
-/

/-- **Full positive deflection**: input 1 maps to output 1 for `dz ∈ [0, 1)`.

    Since `deadzone 1 dz = 1` and `expo(1, e) = 1`. -/
theorem expodz_at_one (e dz : Rat) (hdz0 : 0 ≤ dz) (hdz1 : dz < 1) :
    expodz 1 e dz = 1 := by
  simp only [expodz, deadzone_at_max dz hdz0 hdz1, expo_at_pos_one]

/-- **Full negative deflection**: input -1 maps to output -1 for `dz ∈ [0, 1)`.

    Since `deadzone (-1) dz = -1` and `expo(-1, e) = -1`. -/
theorem expodz_at_neg_one (e dz : Rat) (hdz0 : 0 ≤ dz) (hdz1 : dz < 1) :
    expodz (-1) e dz = -1 := by
  simp only [expodz, deadzone_at_min dz hdz0 hdz1, expo_at_neg_one]

/-!
## Boundary exponential parameters
-/

/-- **Linear expo** (`e = 0`): expo degenerates to identity, so `expodz v 0 dz = deadzone v dz`.

    This is the "no curve shaping" case: input passes straight through the deadzone
    with no further reshaping. Requires `v ∈ [-1, 1]` and `dz ∈ [0, 1)` so that
    the deadzone output is already in range (no clipping by `constrainRat`). -/
theorem expodz_e0 (v dz : Rat) (hv1 : -1 ≤ v) (hv2 : v ≤ 1)
    (hdz0 : 0 ≤ dz) (hdz1 : dz < 1) :
    expodz v 0 dz = deadzone v dz := by
  simp only [expodz, expo_linear]
  apply constrainRat_id
  · exact deadzone_ge_neg_one v dz hv1 hdz0 hdz1
  · exact deadzone_le_one v dz hv2 hdz0 hdz1

/-- **Cubic expo** (`e = 1`): expo raises to the third power, so
    `expodz v 1 dz = (deadzone v dz)³`.

    The pure cubic curve gives maximum sensitivity boost near ±1.
    Requires `v ∈ [-1, 1]` and `dz ∈ [0, 1)` as for `expodz_e0`. -/
theorem expodz_cubic (v dz : Rat) (hv1 : -1 ≤ v) (hv2 : v ≤ 1)
    (hdz0 : 0 ≤ dz) (hdz1 : dz < 1) :
    expodz v 1 dz = deadzone v dz * deadzone v dz * deadzone v dz := by
  simp only [expodz]
  rw [expo_cubic]
  have hdz_lo := deadzone_ge_neg_one v dz hv1 hdz0 hdz1
  have hdz_hi := deadzone_le_one v dz hv2 hdz0 hdz1
  have hcid : constrainRat (deadzone v dz) (-1) 1 = deadzone v dz :=
    constrainRat_id _ _ _ hdz_lo hdz_hi
  rw [hcid]

/-!
## No-deadzone degeneration
-/

/-- **No deadzone** (`dz = 0`): when the deadzone width is 0, `expodz` reduces to
    pure `expoRat`.

    This proves that adding a zero-width deadzone is a no-op: `deadzone v 0 = v`
    for all `v`, so `expodz v e 0 = expoRat v e`. -/
theorem expodz_no_dz (v e : Rat) : expodz v e 0 = expoRat v e := by
  simp only [expodz]
  -- It suffices to show: deadzone v 0 = v
  congr 1
  by_cases h1 : 0 < v
  · -- v > 0: use existing lemma
    exact deadzone_no_dz_pos v h1
  · by_cases h2 : v = 0
    · -- v = 0: in-deadzone branch (0.abs = 0 ≤ 0)
      subst h2
      exact deadzone_in_dz 0 0 (by native_decide)
    · -- v < 0: use negative branch with dz = 0
      have hv0 : v < 0 := Rat.lt_of_le_of_ne (Rat.not_lt.mp h1) h2
      rw [deadzone_neg_eq v 0 (by rw [Rat.neg_zero]; exact hv0) (by native_decide : (0:Rat) ≤ 0)]
      -- Goal: (v + 0) / (1 - 0) = v
      rw [Rat.add_zero, Rat.sub_eq_add_neg, Rat.neg_zero, Rat.add_zero,
          Rat.div_def, Rat.inv_eq_of_mul_eq_one (Rat.mul_one 1), Rat.mul_one]

/-!
## Odd symmetry
-/

/-- **Odd symmetry**: the expo-deadzone pipeline is an odd function for `dz ≥ 0`.

    `expodz (-v) e dz = -(expodz v e dz)` — negating the stick input negates the output.
    This follows from:
    1. `deadzone_odd`: `deadzone (-v) dz = -(deadzone v dz)`
    2. `expo_odd`: `expoRat (-w) e = -(expoRat w e)`
    Together: `expodz (-v) e dz = expoRat(deadzone(-v) dz) e`
                                  `= expoRat(-(deadzone v dz)) e`
                                  `= -(expoRat(deadzone v dz) e)`
                                  `= -(expodz v e dz)`. -/
theorem expodz_odd (v e dz : Rat) (hdz : 0 ≤ dz) :
    expodz (-v) e dz = -(expodz v e dz) := by
  simp only [expodz]
  rw [deadzone_odd v dz hdz, expo_odd (deadzone v dz) e]

end PX4.ExpoDeadzone
