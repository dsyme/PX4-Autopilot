# Informal Specification: `atmosphere` functions

🔬 *Lean Squad automated formal verification.*

**Target**: `atmosphere::getDensityFromPressureAndTemp`,
`atmosphere::getStandardTemperatureAtAltitude`,
`atmosphere::getPressureFromAltitude`, `atmosphere::getAltitudeFromPressure`

**C++ source**: `src/lib/atmosphere/atmosphere.h` and `src/lib/atmosphere/atmosphere.cpp`

**Informal spec written**: 2026-04-20

---

## Purpose

The `atmosphere` library models the **International Standard Atmosphere (ISA)**,
specifically the first layer (troposphere, 0–11 km AMSL). It is used throughout PX4 for:

- Air-density estimation (motor efficiency, sensor calibration)
- Barometric altitude calculation (from pressure readings)
- EKF2 barometric fusion
- Fixed-wing airspeed and lift computation

Four functions are provided:

1. `getDensityFromPressureAndTemp(pressure_pa, temperature_celsius)` — ideal gas law
2. `getStandardTemperatureAtAltitude(altitude_m)` — ISA temperature lapse rate
3. `getPressureFromAltitude(altitude_m)` — barometric formula (pressure from altitude)
4. `getAltitudeFromPressure(pressure_pa, pressure_sealevel_pa)` — hypsometric equation

The most tractable for formal verification are (1) and (2), which involve only rational
arithmetic. Functions (3) and (4) require `powf` (exponential/power law) and are better
verified using monotonicity and bounds arguments rather than exact computation.

---

## Constants

From `atmosphere.h`:

```
kAirGasConstant      = 287.1  J/(kg·K)
kAbsoluteNullCelsius = -273.15 °C
kTempRefKelvin       = 15.0 - (-273.15) = 288.15 K   (ISA sea-level temperature)
kTempGradient        = -6.5e-3 K/m                   (ISA lapse rate)
kPressRefSeaLevelPa  = 101325 Pa
CONSTANTS_ONE_G      = 9.80665 m/s²
```

---

## Function 1: `getDensityFromPressureAndTemp`

### Formula

```
ρ = P / (R · T_K)
```

where:
- `P` = `pressure_pa`  (Pa)
- `R` = `kAirGasConstant` = 287.1 J/(kg·K)
- `T_K` = `temperature_celsius - kAbsoluteNullCelsius` = `temperature_celsius + 273.15` (K)

### Preconditions

- `pressure_pa > 0`  (physical: pressure is always positive)
- `temperature_celsius > kAbsoluteNullCelsius` (i.e., `> -273.15`)  so that `T_K > 0`
  — this ensures the divisor is nonzero and positive.
- The function is well-defined for all positive `P` and positive `T_K`.
- **Note**: The C++ source has NO bounds checking. Callers are expected to supply valid
  inputs. Passing `temperature_celsius ≤ -273.15` or `pressure_pa ≤ 0` produces a
  zero-denominator or negative density — physically meaningless results that the code
  does not guard against.

### Postconditions

- **Positivity**: if `pressure_pa > 0` and `temperature_celsius > -273.15`, then the
  result (density) is strictly positive.
- **Ideal gas law identity**: `ρ · R · (temperature_celsius + 273.15) = pressure_pa`
  (up to floating-point rounding).
- **Monotonicity in pressure**: for fixed temperature, density is increasing in pressure.
- **Monotonicity in temperature**: for fixed pressure, density is decreasing in
  temperature (higher temperature → lower density, consistent with hot air rising).
- **Sea-level standard**: at `pressure_pa = 101325` and `temperature_celsius = 15.0`,
  the result should be approximately `1.225 kg/m³`
  (= 101325 / (287.1 × 288.15) ≈ 1.2250 kg/m³).

### Invariants / mathematical properties

- **Proportionality**: `getDensityFromPressureAndTemp(k·P, T) = k · getDensityFromPressureAndTemp(P, T)` for `k > 0`.
- **Inverse proportionality in temperature**: doubling the absolute temperature halves density (at fixed pressure).

### Edge cases

- `pressure_pa = 0`: denominator is valid (R·T > 0) but numerator is 0 → result is 0. Physically: vacuum → zero density. Mathematically well-defined.
- `temperature_celsius = -273.15`: `T_K = 0` → division by zero. **Undefined / implementation defect**: the C++ performs a division-by-zero (undefined behaviour for floats → `±∞` or NaN in practice). This is an input domain error the caller must avoid.
- `temperature_celsius < -273.15`: `T_K < 0` → negative density. Physically impossible; caller must avoid.
- Very large `pressure_pa`: no overflow for typical float range; ISA validity ends at ~11 km altitude.

### Lean 4 formalisation notes

- Model using `Rat` arithmetic (exact) or `Float` (floating-point).
- Rational model: `densityRat (P T_K : Rat) := P / (kR * T_K)` where `kR = 2871/10` (approximating 287.1).
- Key properties to prove: `densityRat_pos`, `densityRat_gas_law`, `densityRat_mono_pressure`, `densityRat_anti_mono_temp`.
- Ideal gas law: `densityRat P T_K * kR * T_K = P` (when `T_K ≠ 0`) — follows directly from rational field axioms.
- Standard value: `densityRat 101325 28815/100 ≈ 1.225` — provable by `native_decide` on a rational approximation.

---

## Function 2: `getStandardTemperatureAtAltitude`

### Formula

```
T_celsius = 15.0 + kTempGradient · altitude_m
          = 15.0 + (-0.0065) · altitude_m
```

Equivalently: `T_K = 288.15 - 0.0065 · altitude_m`

### Preconditions

- `altitude_m ∈ [0, 11000]` for the ISA first-layer model to be valid.
- The function is defined for all real `altitude_m` (no bounds check in C++), but the
  ISA model breaks down above 11 km.

### Postconditions

- **At sea level**: `getStandardTemperatureAtAltitude(0) = 15.0 °C`.
- **At 11 km**: `getStandardTemperatureAtAltitude(11000) = 15 + (-0.0065 × 11000) = -56.5 °C`.
- **Linearity**: the function is a linear (affine) function of altitude.
- **Monotonicity**: temperature is strictly decreasing with altitude (lapse rate < 0).
- **Continuity**: temperature changes continuously with altitude (no discontinuities in first layer).

### Invariants / mathematical properties

- **Lapse rate**: `getStandardTemperatureAtAltitude(h2) - getStandardTemperatureAtAltitude(h1) = -0.0065 · (h2 - h1)`.
- **Affine**: the function is `f(h) = 15 + g·h` for `g = -0.0065`.

### Edge cases

- `altitude_m = 0`: returns 15 °C (ISA sea-level temperature) — straightforward.
- Negative altitude (e.g. Dead Sea, −420 m): `15 + 0.0065 × 420 = 17.73 °C`. Physically
  plausible but outside the strict ISA model validity. The C++ returns this value.
- `altitude_m > 11000`: temperature continues decreasing linearly, which is incorrect
  above the tropopause (real ISA is isothermal 11–20 km at −56.5 °C). **Open question
  for maintainers**: is it acceptable to use this extrapolation above 11 km?

### Lean 4 formalisation notes

- Model: `tempAtAltRat (h : Rat) : Rat := 15 + (-13/2000) * h`
  (using `kTempGradient = -6.5/1000 = -13/2000` exactly in rationals).
- Key properties: `tempAtAlt_sea_level` (`tempAtAltRat 0 = 15`), `tempAtAlt_linear`,
  `tempAtAlt_mono` (strictly decreasing), `tempAtAlt_tropopause`
  (`tempAtAltRat 11000 = -565/10`).
- All properties provable by `norm_num` / `ring` / `omega` on rational arithmetic.

---

## Functions 3 & 4: `getPressureFromAltitude` and `getAltitudeFromPressure`

These functions use the **barometric / hypsometric formula** and require `powf` (a
transcendental function). They are noted here for completeness but are **deferred** for
formal verification until Mathlib's `Real.rpow` is available in the build environment.

### `getPressureFromAltitude`

```
P(h) = P₀ · (T(h) / T₀)^(g / (-a·R))
```

where `a = kTempGradient`, `g = CONSTANTS_ONE_G`, `R = kAirGasConstant`.

**Key properties** (informal):
- **Monotonicity**: `P(h)` is strictly decreasing with altitude (pressure falls with height).
- **Sea-level identity**: `P(0) = kPressRefSeaLevelPa = 101325 Pa`.
- **Positive**: `P(h) > 0` for all altitudes in the valid range.
- **Inverse of `getAltitudeFromPressure`** (with `pressure_sealevel_pa = kPressRefSeaLevelPa`): `getAltitudeFromPressure(getPressureFromAltitude(h), kPressRefSeaLevelPa) ≈ h`.

### `getAltitudeFromPressure`

```
h(P) = (T₀ · (P/P₁)^(-a·R/g) - T₀) / a
```

**Key properties** (informal):
- **Inverse of pressure formula**: `getPressureFromAltitude(getAltitudeFromPressure(P, P₁)) ≈ P`.
- **Monotonicity**: altitude is strictly decreasing in pressure (lower pressure → higher altitude).
- **Reference sea level**: `getAltitudeFromPressure(kPressRefSeaLevelPa, kPressRefSeaLevelPa) = 0`.

---

## Inferred Intent

The atmosphere library provides simple, low-overhead ISA model calculations for use in
flight controllers. The design intent is:

1. Fast, branchless arithmetic for flight-critical paths.
2. Validity for the troposphere (0–11 km); the code comment says "first layer of US Standard Atmosphere 1976".
3. No defensive bounds checking — callers are responsible for providing physically sensible inputs.

The ideal gas law formula is exact modulo floating-point rounding. The barometric formula
uses `powf` (exponential) so it is inherently approximate in floating-point.

---

## Open Questions for Maintainers

1. **Temperature below absolute zero**: Should the code add a guard against
   `temperature_celsius ≤ -273.15`? Currently returns ±∞ or NaN.
2. **Altitude validity**: Should `getStandardTemperatureAtAltitude` clamp above 11 km?
   The current implementation returns a linearly extrapolated value that does not match
   the real ISA isothermal stratosphere layer.
3. **Precision of kTempGradient and kAirGasConstant**: The constants use float literals
   (`-6.5f/1000.f`, `287.1f`). Would double precision improve accuracy for EKF2 fusion?

---

## Example Values (for specification testing)

| `pressure_pa` | `temperature_celsius` | Expected density (kg/m³) |
|--------------|----------------------|--------------------------|
| 101325 | 15.0 | ≈ 1.2250 (ISA SL) |
| 101325 | 0.0 | ≈ 1.2924 |
| 89875 | 5.0 | ≈ 1.1117 (≈ 1000 m ISA) |
| 54048 | -21.5 | ≈ 0.7364 (≈ 5000 m ISA) |
| 22632 | -56.5 | ≈ 0.3639 (≈ 11000 m ISA) |

| `altitude_m` | Expected temperature (°C) |
|-------------|--------------------------|
| 0 | 15.0 |
| 1000 | 8.5 |
| 5000 | −17.5 |
| 11000 | −56.5 |
