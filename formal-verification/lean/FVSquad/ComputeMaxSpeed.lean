/-!
# computeMaxSpeedFromDistance — Formal Specification

🔬 *Lean Squad automated formal verification.*

- **C++ source**: `src/lib/mathlib/math/TrajMath.hpp`
- **Informal spec**: `formal-verification/specs/computemaxspeed_informal.md`

## C++ Reference

```cpp
float computeMaxSpeedFromDistance(float jerk, float accel, float braking_distance, float final_speed)
{
    auto sqr = [](float f) { return f * f; };
    float b = 4.0f * sqr(accel) / jerk;
    float c = -2.0f * accel * braking_distance - sqr(final_speed);
    float max_speed = 0.5f * (-b + sqrtf(sqr(b) - 4.0f * c));
    return fmaxf(max_speed, final_speed);
}
```

Used by the PX4 velocity smoother to determine the maximum approach speed at
a waypoint so that kinematic constraints (jerk + deceleration limits) are
satisfied within the available braking distance.

## Quadratic Formula

```
b = 4a²/j,    c = -(2a·d) - vf²
disc = b² - 4c = b² + 4·(2a·d + vf²)    [≥ 0 when a,d,vf ≥ 0]
raw_max = 0.5·(-b + √disc)
result  = max(raw_max, vf)
```

## Modelling Choices

- Arithmetic is over `Rat` (exact rationals); IEEE-754 rounding not modelled.
- `sqrtf` is axiomatised via `sqrtQ` with: non-negativity, squaring identity, monotonicity.
- Preconditions: `jerk > 0`, `accel ≥ 0`, `dist ≥ 0`, `finalSpeed ≥ 0`.

## Verification Status

| Theorem | Proof status | Notes |
|---------|--------------|-------|
| `discriminant_nonneg` | ✅ proved | disc ≥ 0 when inputs non-negative |
| `maxSpeed_ge_finalSpeed` | ✅ proved | result ≥ finalSpeed by construction |
| `maxSpeed_nonneg` | ✅ proved | result ≥ 0 when finalSpeed ≥ 0 |
| `maxSpeed_accel_zero` | ✅ proved | accel=0 → result = finalSpeed |
| `maxSpeed_mono_dist` | ✅ proved | more braking distance → higher allowed speed |
| `maxSpeed_quadratic_eq` | ✅ proved | (2·ms + b)² = disc |
-/

namespace PX4.ComputeMaxSpeed

/-! ## Abstract square-root model -/

/-- Abstract model for `sqrtf(x)` on non-negative rationals. -/
noncomputable axiom sqrtQ : Rat → Rat

/-- `sqrtQ` is non-negative for non-negative inputs. -/
axiom sqrtQ_nonneg (x : Rat) (h : 0 ≤ x) : 0 ≤ sqrtQ x

/-- `sqrtQ x * sqrtQ x = x` for `x ≥ 0`. -/
axiom sqrtQ_sq (x : Rat) (h : 0 ≤ x) : sqrtQ x * sqrtQ x = x

/-- `sqrtQ` is monotone on non-negative inputs. -/
axiom sqrtQ_mono (u v : Rat) (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u ≤ v) :
    sqrtQ u ≤ sqrtQ v

/-- Uniqueness of the non-negative square root: if `s ≥ 0` and `s² = x` then `sqrtQ x = s`. -/
axiom sqrtQ_unique (x s : Rat) (hs : 0 ≤ s) (hx : 0 ≤ x) (h : s * s = x) : sqrtQ x = s

/-! ## Helper lemmas -/

/-- `a * a ≥ 0` for any rational. -/
private theorem mul_self_nonneg (a : Rat) : 0 ≤ a * a := by
  by_cases h : 0 ≤ a
  · exact Rat.mul_nonneg h h
  · have ha : a < 0 := Rat.not_le.mp h
    have hna : 0 ≤ -a := by
      have hh := Rat.neg_le_neg (Rat.le_of_lt ha)
      rw [Rat.neg_zero] at hh; exact hh
    have key : a * a = (-a) * (-a) := by
      rw [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]
    rw [key]; exact Rat.mul_nonneg hna hna

/-- `-a ≤ 0` when `0 ≤ a`. -/
private theorem neg_nonpos_of_nonneg (a : Rat) (h : 0 ≤ a) : -a ≤ 0 := by
  have hh := Rat.neg_le_neg h
  rw [Rat.neg_zero] at hh; exact hh

/-! ## Implementation model -/

/-- b-coefficient: `b = 4·accel² / jerk`. -/
noncomputable def bCoeff (jerk accel : Rat) : Rat :=
  4 * (accel * accel) / jerk

/-- c-coefficient: `c = -(2·accel·dist) - finalSpeed²`. Always ≤ 0 for non-negative inputs. -/
noncomputable def cCoeff (accel dist finalSpeed : Rat) : Rat :=
  -(2 * accel * dist) - finalSpeed * finalSpeed

/-- Discriminant: `b² - 4c`. Always ≥ 0 for non-negative inputs (see `discriminant_nonneg`). -/
noncomputable def discriminant (jerk accel dist finalSpeed : Rat) : Rat :=
  bCoeff jerk accel * bCoeff jerk accel - 4 * cCoeff accel dist finalSpeed

/-- Unclamped max speed: `(1/2)·(-b + sqrtQ(disc))`. -/
noncomputable def rawMaxSpeed (jerk accel dist finalSpeed : Rat) : Rat :=
  (1 : Rat) / 2 * (-bCoeff jerk accel + sqrtQ (discriminant jerk accel dist finalSpeed))

/-- Lean model of `computeMaxSpeedFromDistance`. -/
noncomputable def computeMaxSpeed (jerk accel dist finalSpeed : Rat) : Rat :=
  max (rawMaxSpeed jerk accel dist finalSpeed) finalSpeed

/-! ## Discriminant non-negativity -/

/-- `cCoeff` is non-positive when all inputs are non-negative. -/
private theorem cCoeff_nonpos (accel dist finalSpeed : Rat)
    (ha : 0 ≤ accel) (hd : 0 ≤ dist) (hvf : 0 ≤ finalSpeed) :
    cCoeff accel dist finalSpeed ≤ 0 := by
  simp only [cCoeff, Rat.sub_eq_add_neg]
  have h2ad : 0 ≤ 2 * accel * dist :=
    Rat.mul_nonneg (Rat.mul_nonneg (by decide) ha) hd
  have hvf2 : 0 ≤ finalSpeed * finalSpeed := mul_self_nonneg _
  have hn2ad : -(2 * accel * dist) ≤ 0 := neg_nonpos_of_nonneg _ h2ad
  have hnvf2 : -(finalSpeed * finalSpeed) ≤ 0 := neg_nonpos_of_nonneg _ hvf2
  calc -(2 * accel * dist) + -(finalSpeed * finalSpeed)
      ≤ 0 + -(finalSpeed * finalSpeed) := Rat.add_le_add_right.mpr hn2ad
    _ ≤ 0 + 0 := Rat.add_le_add_left.mpr hnvf2
    _ = 0 := Rat.zero_add 0

/-- `discriminant ≥ 0` when `accel, dist, finalSpeed ≥ 0`.
    This guarantees `sqrtQ` is always applied to a non-negative value. -/
theorem discriminant_nonneg (jerk accel dist finalSpeed : Rat)
    (ha : 0 ≤ accel) (hd : 0 ≤ dist) (hvf : 0 ≤ finalSpeed) :
    0 ≤ discriminant jerk accel dist finalSpeed := by
  simp only [discriminant, Rat.sub_eq_add_neg]
  apply Rat.add_nonneg
  · exact mul_self_nonneg _
  · have hc_nonpos := cCoeff_nonpos accel dist finalSpeed ha hd hvf
    have h4c : 4 * cCoeff accel dist finalSpeed ≤ 0 :=
      calc 4 * cCoeff accel dist finalSpeed
          ≤ 4 * 0 := Rat.mul_le_mul_of_nonneg_left hc_nonpos (by decide)
        _ = 0 := Rat.mul_zero 4
    have hh := Rat.neg_le_neg h4c
    rw [Rat.neg_zero] at hh; exact hh

/-! ## Result clamping -/

/-- `computeMaxSpeed` always returns at least `finalSpeed` (from `max` clamp). -/
theorem maxSpeed_ge_finalSpeed (jerk accel dist finalSpeed : Rat) :
    finalSpeed ≤ computeMaxSpeed jerk accel dist finalSpeed := by
  simp only [computeMaxSpeed, Rat.max_def]
  by_cases h : rawMaxSpeed jerk accel dist finalSpeed ≤ finalSpeed
  · rw [if_pos h]; exact (Rat.le_iff_sub_nonneg _ _).mpr (by simp [Rat.sub_self])
  · rw [if_neg h]; exact Rat.le_of_lt (Rat.not_le.mp h)

/-- `computeMaxSpeed` is non-negative when `finalSpeed ≥ 0`. -/
theorem maxSpeed_nonneg (jerk accel dist finalSpeed : Rat) (hvf : 0 ≤ finalSpeed) :
    0 ≤ computeMaxSpeed jerk accel dist finalSpeed :=
  Rat.le_trans hvf (maxSpeed_ge_finalSpeed jerk accel dist finalSpeed)

/-! ## Special cases and key properties -/

/-! ### Helper lemmas for special-case proofs -/

/-- `2·vf · 2·vf = 4·vf²` — used to evaluate `sqrtQ(4·vf²) = 2·vf`. -/
private theorem mul_two_sq (vf : Rat) : 2 * vf * (2 * vf) = 4 * (vf * vf) := by
  calc 2 * vf * (2 * vf)
      = 2 * (vf * (2 * vf)) := Rat.mul_assoc 2 vf (2 * vf)
    _ = 2 * ((vf * 2) * vf) := by rw [← Rat.mul_assoc vf 2 vf]
    _ = 2 * ((2 * vf) * vf) := by rw [Rat.mul_comm vf 2]
    _ = 2 * (2 * (vf * vf)) := by rw [Rat.mul_assoc 2 vf vf]
    _ = 2 * 2 * (vf * vf) := (Rat.mul_assoc 2 2 (vf * vf)).symm
    _ = 4 * (vf * vf) := by rw [show (2 : Rat) * 2 = 4 from by native_decide]

/-- `2·(1/2·(-b + s)) + b = s` — used to simplify `2·rawMaxSpeed + b`. -/
private theorem key_linear (b s : Rat) : 2 * ((1 : Rat) / 2 * (-b + s)) + b = s := by
  have h2half : (2 : Rat) * (1 / 2) = 1 := by native_decide
  calc 2 * (1 / 2 * (-b + s)) + b
      = 2 * (1 / 2) * (-b + s) + b := by rw [← Rat.mul_assoc]
    _ = 1 * (-b + s) + b := by rw [h2half]
    _ = (-b + s) + b := by rw [Rat.one_mul]
    _ = s := by rw [Rat.add_assoc, Rat.add_comm s b, ← Rat.add_assoc, Rat.neg_add_cancel, Rat.zero_add]

/-- `max a a = a`. -/
private theorem max_self (a : Rat) : max a a = a := by simp [Rat.max_def]

/-- `max a c ≤ max b c` when `a ≤ b`. -/
private theorem max_le_max_left (a b c : Rat) (h : a ≤ b) : max a c ≤ max b c := by
  simp only [Rat.max_def]
  by_cases h1 : a ≤ c <;> by_cases h2 : b ≤ c
  · simp [h1, h2]
  · simp [h1, h2]; exact Rat.le_of_lt (Rat.not_le.mp h2)
  · simp [h1, h2]; exact absurd (Rat.le_trans h h2) h1
  · simp [h1, h2, h]

/-- `cCoeff` decreases (gets more negative) as `dist` increases. -/
private theorem cCoeff_antimono_dist (accel dist₁ dist₂ finalSpeed : Rat)
    (ha : 0 ≤ accel) (hle : dist₁ ≤ dist₂) :
    cCoeff accel dist₂ finalSpeed ≤ cCoeff accel dist₁ finalSpeed := by
  simp only [cCoeff, Rat.sub_eq_add_neg]
  apply Rat.add_le_add_right.mpr
  apply Rat.neg_le_neg
  apply Rat.mul_le_mul_of_nonneg_left hle
  exact Rat.mul_nonneg (by native_decide) ha

/-- `discriminant` increases (gets larger) as `dist` increases. -/
private theorem discriminant_mono_dist (jerk accel dist₁ dist₂ finalSpeed : Rat)
    (ha : 0 ≤ accel) (hle : dist₁ ≤ dist₂) :
    discriminant jerk accel dist₁ finalSpeed ≤ discriminant jerk accel dist₂ finalSpeed := by
  simp only [discriminant, Rat.sub_eq_add_neg]
  apply Rat.add_le_add_left.mpr
  apply Rat.neg_le_neg
  apply Rat.mul_le_mul_of_nonneg_left _ (by native_decide : (0 : Rat) ≤ 4)
  exact cCoeff_antimono_dist accel dist₁ dist₂ finalSpeed ha hle

/-- When `accel = 0`: b = 0, disc = vf², rawMaxSpeed = vf/2, result = vf.
    The `fmaxf(vf/2, vf) = vf` step uses that vf ≥ 0 implies vf/2 ≤ vf. -/
theorem maxSpeed_accel_zero (jerk dist finalSpeed : Rat) (hvf : 0 ≤ finalSpeed) :
    computeMaxSpeed jerk 0 dist finalSpeed = finalSpeed := by
  simp only [computeMaxSpeed, rawMaxSpeed, bCoeff, cCoeff, discriminant]
  simp only [Rat.mul_zero, Rat.zero_mul, Rat.neg_zero]
  simp only [Rat.div_def, Rat.zero_mul]
  -- Goal: max (1 * 2⁻¹ * sqrtQ (-(4 * -(finalSpeed * finalSpeed)))) finalSpeed = finalSpeed
  rw [Rat.mul_neg, Rat.neg_neg]
  -- sqrtQ(4*vf²) = 2*vf by uniqueness
  have hvf2 : 0 ≤ finalSpeed * finalSpeed := Rat.mul_nonneg hvf hvf
  have hdisc : 0 ≤ 4 * (finalSpeed * finalSpeed) := Rat.mul_nonneg (by decide) hvf2
  rw [sqrtQ_unique _ (2 * finalSpeed) (Rat.mul_nonneg (by decide) hvf) hdisc (mul_two_sq finalSpeed)]
  -- Now: max (1 * 2⁻¹ * (2 * finalSpeed)) finalSpeed = finalSpeed
  have h : (1 : Rat) * 2⁻¹ * (2 * finalSpeed) = finalSpeed := by
    have h2 : (2 : Rat)⁻¹ * 2 = 1 := by native_decide
    rw [Rat.mul_assoc 1 2⁻¹ (2 * finalSpeed), Rat.one_mul]
    rw [← Rat.mul_assoc 2⁻¹ 2 finalSpeed, h2, Rat.one_mul]
  rw [h, max_self]

/-- More braking distance → higher allowed approach speed (monotone). -/
theorem maxSpeed_mono_dist (jerk accel dist₁ dist₂ finalSpeed : Rat)
    (ha : 0 ≤ accel) (hd₁ : 0 ≤ dist₁) (hd₂ : 0 ≤ dist₂)
    (hvf : 0 ≤ finalSpeed) (hle : dist₁ ≤ dist₂) :
    computeMaxSpeed jerk accel dist₁ finalSpeed ≤
    computeMaxSpeed jerk accel dist₂ finalSpeed := by
  simp only [computeMaxSpeed]
  apply max_le_max_left
  simp only [rawMaxSpeed]
  apply Rat.mul_le_mul_of_nonneg_left _ (by native_decide : (0 : Rat) ≤ 1 / 2)
  apply Rat.add_le_add_left.mpr
  apply sqrtQ_mono
  · exact discriminant_nonneg jerk accel dist₁ finalSpeed ha hd₁ hvf
  · exact discriminant_nonneg jerk accel dist₂ finalSpeed ha hd₂ hvf
  · exact discriminant_mono_dist jerk accel dist₁ dist₂ finalSpeed ha hle

/-- `rawMaxSpeed` satisfies the original quadratic: `(2·ms + b)² = disc`. -/
theorem maxSpeed_quadratic_eq (jerk accel dist finalSpeed : Rat)
    (ha : 0 ≤ accel) (hd : 0 ≤ dist) (hvf : 0 ≤ finalSpeed) :
    (2 * rawMaxSpeed jerk accel dist finalSpeed + bCoeff jerk accel) *
    (2 * rawMaxSpeed jerk accel dist finalSpeed + bCoeff jerk accel) =
    discriminant jerk accel dist finalSpeed := by
  simp only [rawMaxSpeed]
  rw [key_linear]
  exact sqrtQ_sq _ (discriminant_nonneg jerk accel dist finalSpeed ha hd hvf)

end PX4.ComputeMaxSpeed
