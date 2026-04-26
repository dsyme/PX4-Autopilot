/-!
# PX4 Atmosphere Library — Formal Verification

🔬 Lean Squad automated formal verification.

This file models and proves correctness properties of the PX4 atmosphere library:

- **C++ source**: `src/lib/atmosphere/atmosphere.h`, `src/lib/atmosphere/atmosphere.cpp`
- **Informal spec**: `formal-verification/specs/atmosphere_informal.md`

## C++ reference

```cpp
// From atmosphere.cpp:
float getDensityFromPressureAndTemp(const float pressure_pa, const float temperature_celsius) {
    return (pressure_pa / (kAirGasConstant * (temperature_celsius - kAbsoluteNullCelsius)));
}
float getStandardTemperatureAtAltitude(float altitude_m) {
    return 15.0f + kTempGradient * altitude_m;
}
```

Constants: `kAirGasConstant = 287.1f`, `kAbsoluteNullCelsius = -273.15f`,
`kTempGradient = -6.5e-3f`.

## Model

We model the two tractable functions over `Rat` (exact rational arithmetic):

1. `densityRat P T_celsius` — ideal gas law: ρ = P / (R · (T_celsius + 273.15))
2. `tempAtAltRat h` — ISA lapse: T = 15 + (-13/2000) · h

Functions `getPressureFromAltitude` and `getAltitudeFromPressure` use `powf` (a
transcendental), which requires `Real.rpow` from Mathlib and are **deferred**.

## Approximations / Out of Scope

- **IEEE 754 float semantics**: NaN, infinity, and rounding are not modelled.
- **Input validation**: The C++ performs no bounds checking; the Lean model requires
  preconditions (`P > 0`, `T_celsius > -273.15`) for the positivity theorems.
- **`powf`-based functions**: `getPressureFromAltitude` and `getAltitudeFromPressure`
  involve exponential arithmetic and are not modelled here.
- **kAirGasConstant precision**: modelled as `2871/10` (rational approximation of 287.1f).
  The exact float literal 287.1f is `24092672 / 2^17` ≈ 287.0999755859375.
  For proportionality and monotonicity theorems the exact constant value is irrelevant.
-/

namespace PX4.Atmosphere

/-! ## Constants -/

/-- Air gas constant R ≈ 287.1 J/(kg·K), modelled as exact rational 2871/10. -/
private def kR : Rat := 2871 / 10

/-- Absolute null in Celsius: kAbsoluteNullCelsius = -273.15 °C, as -27315/100. -/
private def kAbsNull : Rat := -27315 / 100

/-- ISA temperature gradient: kTempGradient = -6.5e-3 K/m = -13/2000. -/
private def kTempGrad : Rat := -13 / 2000

/-- Reference temperature at sea level: 15°C = 288.15 K. -/
private def kTempRefKelvin : Rat := 28815 / 100

/-- Reference sea-level pressure: 101325 Pa. -/
private def kPressRef : Rat := 101325

/-- kR is strictly positive. -/
private theorem kR_pos : (0 : Rat) < kR := by native_decide

/-- kTempGrad is strictly negative. -/
private theorem kTempGrad_neg : kTempGrad < (0 : Rat) := by native_decide

/-! ## Function models -/

/-- Absolute temperature (Kelvin) from Celsius.
    T_K = temperature_celsius - kAbsoluteNullCelsius = temperature_celsius + 273.15 -/
def tempKelvin (T_celsius : Rat) : Rat :=
  T_celsius - kAbsNull

/-- Density from pressure and temperature (ideal gas law).
    ρ = P / (R · T_K)  where  T_K = T_celsius + 273.15 -/
def densityRat (P T_celsius : Rat) : Rat :=
  P / (kR * tempKelvin T_celsius)

/-- Standard ISA temperature at altitude (first tropospheric layer).
    T_celsius = 15 + kTempGradient · h  =  15 + (-13/2000) · h -/
def tempAtAltRat (h : Rat) : Rat :=
  15 + kTempGrad * h

-- Sanity checks: model reproduces expected numeric outputs
#eval densityRat 101325 15                   -- ≈ 1.225 (ISA SL)
#eval densityRat 101325 0                    -- ≈ 1.292
#eval densityRat 22632  (-113/2)             -- ≈ 0.364 (≈ 11 km ISA)
#eval tempAtAltRat 0                         -- 15
#eval tempAtAltRat 1000                      -- 17/2 = 8.5
#eval tempAtAltRat 5000                      -- -35/2 = -17.5
#eval tempAtAltRat 11000                     -- -113/2 = -56.5

/-! ## Positivity and well-definedness -/

/-- tempKelvin is positive iff T_celsius > kAbsNull (-273.15). -/
theorem tempKelvin_pos_iff (T_celsius : Rat) :
    0 < tempKelvin T_celsius ↔ kAbsNull < T_celsius :=
  (Rat.lt_iff_sub_pos kAbsNull T_celsius).symm

/-- When T_celsius > -273.15, tempKelvin is strictly positive. -/
theorem tempKelvin_pos (T_celsius : Rat) (h : kAbsNull < T_celsius) :
    0 < tempKelvin T_celsius :=
  (Rat.lt_iff_sub_pos kAbsNull T_celsius).mp h

/-- The divisor kR · tempKelvin is positive when the temperature is above absolute zero. -/
theorem kR_mul_tempKelvin_pos (T_celsius : Rat) (h : kAbsNull < T_celsius) :
    0 < kR * tempKelvin T_celsius :=
  Rat.mul_pos kR_pos (tempKelvin_pos T_celsius h)

/-- **Positivity**: density is strictly positive when pressure > 0 and
    temperature is above absolute zero. -/
theorem densityRat_pos (P T_celsius : Rat)
    (hP : 0 < P) (hT : kAbsNull < T_celsius) :
    0 < densityRat P T_celsius := by
  simp only [densityRat, Rat.div_def]
  exact Rat.mul_pos hP (Rat.inv_pos.mpr (kR_mul_tempKelvin_pos T_celsius hT))

/-! ## Gas law identity -/

/-- **Ideal gas law**: ρ · R · T_K = P.
    The density times the gas constant times the absolute temperature equals pressure. -/
theorem densityRat_gas_law (P T_celsius : Rat)
    (hT : kAbsNull < T_celsius) :
    densityRat P T_celsius * (kR * tempKelvin T_celsius) = P := by
  simp only [densityRat, Rat.div_def]
  have hne : kR * tempKelvin T_celsius ≠ 0 :=
    Rat.ne_of_gt (kR_mul_tempKelvin_pos T_celsius hT)
  rw [Rat.mul_assoc, Rat.inv_mul_cancel _ hne, Rat.mul_one]

/-! ## Monotonicity -/

/-- **Monotone in pressure**: for fixed temperature, higher pressure → higher density. -/
theorem densityRat_mono_pressure (P1 P2 T_celsius : Rat)
    (hP : P1 < P2) (hT : kAbsNull < T_celsius) :
    densityRat P1 T_celsius < densityRat P2 T_celsius := by
  simp only [densityRat, Rat.div_def]
  exact Rat.mul_lt_mul_of_pos_right hP
    (Rat.inv_pos.mpr (kR_mul_tempKelvin_pos T_celsius hT))

/-- **Anti-monotone in temperature**: for fixed pressure, higher temperature → lower density.
    When T_celsius increases, T_K = T_celsius + 273.15 increases, so density decreases.
    Proof: reduce to showing (kR * T_K2)⁻¹ < (kR * T_K1)⁻¹ when T_K1 < T_K2.
    This requires `Rat.inv_lt_inv_of_lt` which is not in stdlib v4.29.
    Left as `sorry` pending Mathlib availability. -/
-- Helper: for positive rationals, strict order is reversed by multiplicative inverse.
-- `Rat.inv_lt_inv_of_lt` is not in stdlib v4.29, so we prove it from first principles
-- using `Rat.mul_lt_mul_right`: `B⁻¹ < A⁻¹` iff `B⁻¹ * (A*B) < A⁻¹ * (A*B)` (mult by A*B > 0),
-- which simplifies to `A < B`.
private theorem rat_inv_lt_inv_of_lt {A B : Rat} (hA : 0 < A) (hB : 0 < B) (h : A < B) :
    B⁻¹ < A⁻¹ := by
  have hAne := Rat.ne_of_gt hA
  have hBne := Rat.ne_of_gt hB
  have hAB := Rat.mul_pos hA hB
  rw [show B⁻¹ < A⁻¹ ↔ B⁻¹ * (A * B) < A⁻¹ * (A * B) from (Rat.mul_lt_mul_right hAB).symm]
  have lhs : B⁻¹ * (A * B) = A := by
    rw [Rat.mul_comm A B, ← Rat.mul_assoc, Rat.inv_mul_cancel _ hBne, Rat.one_mul]
  have rhs : A⁻¹ * (A * B) = B := by
    rw [← Rat.mul_assoc, Rat.inv_mul_cancel _ hAne, Rat.one_mul]
  rw [lhs, rhs]; exact h

theorem densityRat_anti_mono_temp (P T1 T2 : Rat)
    (hP : 0 < P) (hT1 : kAbsNull < T1) (hT2 : kAbsNull < T2) (hTlt : T1 < T2) :
    densityRat P T2 < densityRat P T1 := by
  simp only [densityRat, Rat.div_def]
  apply Rat.mul_lt_mul_of_pos_left _ hP
  -- goal: (kR * tempKelvin T2)⁻¹ < (kR * tempKelvin T1)⁻¹
  -- Strategy: apply rat_inv_lt_inv_of_lt; then reduce to tempKelvin T1 < tempKelvin T2.
  apply rat_inv_lt_inv_of_lt (kR_mul_tempKelvin_pos T1 hT1) (kR_mul_tempKelvin_pos T2 hT2)
  apply Rat.mul_lt_mul_of_pos_left _ kR_pos
  -- goal: tempKelvin T1 < tempKelvin T2
  -- tempKelvin T = T - kAbsNull; use Rat.add_lt_add_right on T1 + (-kAbsNull) < T2 + (-kAbsNull)
  unfold tempKelvin
  rw [Rat.sub_eq_add_neg, Rat.sub_eq_add_neg]
  exact (Rat.add_lt_add_right).mpr hTlt

/-! ## Proportionality -/

/-- **Proportionality in pressure**: scaling pressure by k scales density by k. -/
theorem densityRat_proportional (k P T_celsius : Rat) :
    densityRat (k * P) T_celsius = k * densityRat P T_celsius := by
  simp only [densityRat, Rat.div_def, Rat.mul_assoc]

/-! ## Temperature at altitude -/

/-- At sea level (altitude 0), the ISA temperature is 15 °C. -/
theorem tempAtAlt_sea_level : tempAtAltRat 0 = 15 := by native_decide

/-- At 11 km (tropopause base), the ISA temperature is -56.5 °C = -113/2. -/
theorem tempAtAlt_tropopause : tempAtAltRat 11000 = -113 / 2 := by native_decide

/-- At 1 km, the ISA temperature is 8.5 °C = 17/2. -/
theorem tempAtAlt_1km : tempAtAltRat 1000 = 17 / 2 := by native_decide

/-- At 5 km, the ISA temperature is -17.5 °C = -35/2. -/
theorem tempAtAlt_5km : tempAtAltRat 5000 = -35 / 2 := by native_decide

/-- **Linearity / lapse rate**: temperature drop per metre equals kTempGrad.
    Equivalent to: tempAtAltRat(h2) - tempAtAltRat(h1) = kTempGrad · (h2 - h1).
    Proof: manual Rat algebra using `Rat.mul_add`, `Rat.mul_neg`, `Rat.neg_add`,
    `Rat.add_assoc`, `Rat.add_comm`, `Rat.add_neg_cancel`. -/
theorem tempAtAlt_lapse_rate (h1 h2 : Rat) :
    tempAtAltRat h2 - tempAtAltRat h1 = kTempGrad * (h2 - h1) := by
  simp only [tempAtAltRat]
  -- Simplify LHS: (15 + kTempGrad*h2) - (15 + kTempGrad*h1) = kTempGrad*h2 - kTempGrad*h1
  have lhs_simp : 15 + kTempGrad * h2 - (15 + kTempGrad * h1) =
      kTempGrad * h2 - kTempGrad * h1 := by
    rw [Rat.sub_eq_add_neg, Rat.neg_add]
    rw [← Rat.add_assoc (15 + kTempGrad * h2) (-15)]
    rw [Rat.add_assoc 15 (kTempGrad * h2) (-15)]
    rw [Rat.add_comm (kTempGrad * h2) (-15 : Rat)]
    rw [← Rat.add_assoc 15 (-15 : Rat) (kTempGrad * h2)]
    rw [Rat.add_neg_cancel, Rat.zero_add]
    rw [← Rat.sub_eq_add_neg]
  -- Simplify RHS: kTempGrad * (h2 - h1) = kTempGrad*h2 - kTempGrad*h1
  rw [lhs_simp, Rat.sub_eq_add_neg h2 h1, Rat.mul_add, Rat.mul_neg, ← Rat.sub_eq_add_neg]

/-- **Strict monotone decreasing**: temperature strictly decreases with altitude.
    Proof: unfold `tempAtAltRat` (= 15 + kTempGrad * h), use `Rat.add_lt_add_left` to
    reduce to `kTempGrad * h2 < kTempGrad * h1`.  Then rewrite `kTempGrad = -(13/2000)`
    and apply `Rat.neg_lt_neg` + `Rat.mul_lt_mul_of_pos_left`. -/
theorem tempAtAlt_strict_anti (h1 h2 : Rat) (hlt : h1 < h2) :
    tempAtAltRat h2 < tempAtAltRat h1 := by
  simp only [tempAtAltRat, kTempGrad]
  rw [Rat.add_lt_add_left]
  -- goal: (-13 / 2000 : Rat) * h2 < (-13 / 2000 : Rat) * h1
  -- Rewrite negative coefficient as negation of a positive one
  have h_neg : (-13 : Rat) / 2000 = -(13 / 2000) := by native_decide
  rw [h_neg, Rat.neg_mul, Rat.neg_mul]
  exact Rat.neg_lt_neg (Rat.mul_lt_mul_of_pos_left hlt (by native_decide : (0 : Rat) < 13 / 2000))

/-- Temperature at altitude is an affine function: f(h) = 15 + g*h. -/
theorem tempAtAlt_affine (h : Rat) :
    tempAtAltRat h = 15 + kTempGrad * h := rfl

/-! ## Concrete density examples (verifiable with native_decide) -/

-- ISA sea-level density: P=101325 Pa, T=15°C → ρ ≈ 1.225 kg/m³
-- #eval gives: 6755000/5515191 ≈ 1.2250
#eval densityRat 101325 15  -- 6755000/5515191

-- Check: result matches the expected reduced fraction
example : densityRat 101325 15 = 6755000 / 5515191 := by native_decide

-- Check it's between 1.224 and 1.226 (standard atmosphere ISA)
example : (1224 : Rat) / 1000 < densityRat 101325 15 ∧
          densityRat 101325 15 < 1226 / 1000 := by native_decide

-- Check positivity for sea-level conditions (via concrete proof)
example : 0 < densityRat 101325 15 := by native_decide

-- Temperature decreases from 0 to 11000 m
example : tempAtAltRat 11000 < tempAtAltRat 0 := by native_decide

end PX4.Atmosphere
