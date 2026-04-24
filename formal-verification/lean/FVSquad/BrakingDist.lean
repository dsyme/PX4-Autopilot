/-!
# computeBrakingDistanceFromVelocity — Formal Verification

🔬 *Lean Squad automated formal verification.*

- **C++ source**: `src/lib/mathlib/math/TrajMath.hpp`, line 107
- **Informal spec**: `formal-verification/specs/braking_dist_informal.md`

## C++ Reference

```cpp
inline float computeBrakingDistanceFromVelocity(const float velocity, const float jerk,
        const float accel, const float accel_delay_max)
{
    return velocity * (velocity / (2.0f * accel) + accel_delay_max / jerk);
}
```

Used in `navigator_main.cpp` to predict the multirotor braking distance for
geofence breach avoidance and waypoint lookahead.

## Formula

```
dist(v, a, j, d) = v · (v / (2a) + d/j)
                 = v² / (2a)  +  v · d/j
```

- v = initial velocity (≥ 0 in all known call sites)
- a = maximum deceleration (> 0)
- j = maximum jerk (> 0)
- d = `accel_delay_max` — acceleration defining the delay phase (≥ 0)

## Modelling Choices

- All arithmetic is over `Rat` (exact rationals), avoiding IEEE-754 rounding.
- The C++ function has no range checks; we state preconditions explicitly.
- The model covers only `computeBrakingDistanceFromVelocity`.

## Verification Status

| Theorem | Status | Notes |
|---------|--------|-------|
| `brakingDist_zero_v` | ✅ | v=0 → dist=0 |
| `brakingDist_nonneg` | ✅ | v≥0, a>0, j>0, d≥0 → dist≥0 |
| `brakingDist_pos` | ✅ | v>0, a>0, j>0, d≥0 → dist>0 |
| `brakingDist_mono_v` | ✅ | monotone in v for fixed params |
| `brakingDist_mono_d` | ✅ | monotone in delay d |
| `brakingDist_no_delay` | ✅ | d=0 → dist = v²/(2a) |
| `brakingDist_no_delay_nonneg` | ✅ | d=0, v≥0, a>0 → dist≥0 |
| `brakingDist_alt_form` | ✅ | dist = v·v/(2a) + v·d/j |
| `brakingDist_double_v_no_delay` | ✅ | dist(2v,a,j,0) = 4·dist(v,a,j,0) |
| Concrete examples (7) | ✅ | Checked by `native_decide` |
-/

namespace PX4.BrakingDistance

/-! ## Implementation model -/

/-- Rational model of `computeBrakingDistanceFromVelocity`.

    Exact transcription of the C++ formula:
    `velocity * (velocity / (2.0f * accel) + accel_delay_max / jerk)` -/
def brakingDist (v a j d : Rat) : Rat :=
  v * (v / (2 * a) + d / j)

/-! ## Concrete examples (sanity checks) -/

-- v=10, a=2, j=4, d=1 : 10 * (10/4 + 1/4) = 10 * 11/4 = 110/4 = 55/2
example : brakingDist 10 2 4 1 = 55 / 2 := by native_decide

-- v=0: zero braking distance
example : brakingDist 0 2 4 1 = 0 := by native_decide

-- d=0 (no delay): classic kinematic formula v²/(2a) = 100/4 = 25
example : brakingDist 10 2 4 0 = 25 := by native_decide

-- v=5, d=0: 25/4
example : brakingDist 5 2 4 0 = 25 / 4 := by native_decide

-- Higher velocity needs more distance (v=10 vs v=5, same params)
example : brakingDist 5 2 4 1 < brakingDist 10 2 4 1 := by native_decide

-- Higher delay (d) needs more distance
example : brakingDist 10 2 4 0 < brakingDist 10 2 4 1 := by native_decide

-- Quadratic growth: doubling speed (d=0) quadruples the distance
example : brakingDist 10 2 4 0 = 4 * brakingDist 5 2 4 0 := by native_decide

/-! ## Helper lemmas -/

private theorem two_pos : (0 : Rat) < 2 := by decide

private theorem inv_nonneg_of_pos {x : Rat} (hx : 0 < x) : 0 ≤ x⁻¹ :=
  Rat.le_of_lt (Rat.inv_pos.mpr hx)

private theorem div_nonneg_rat {a b : Rat} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / b := by
  rw [Rat.div_def]
  exact Rat.mul_nonneg ha (inv_nonneg_of_pos hb)

private theorem div_pos_rat {a b : Rat} (ha : 0 < a) (hb : 0 < b) : 0 < a / b := by
  rw [Rat.div_def]
  exact Rat.mul_pos ha (Rat.inv_pos.mpr hb)

private theorem le_add_nonneg_right {a b : Rat} (hb : 0 ≤ b) : a ≤ a + b :=
  calc a = a + 0 := (Rat.add_zero a).symm
    _ ≤ a + b := Rat.add_le_add_left.mpr hb

/-! ## Main theorems -/

/-- **Zero velocity** gives zero braking distance. -/
theorem brakingDist_zero_v (a j d : Rat) : brakingDist 0 a j d = 0 := by
  simp [brakingDist]

/-- **Non-negativity**: for physically valid inputs, braking distance is ≥ 0.

    This is the key safety property: the function never returns a negative value
    when called with the expected non-negative velocity. -/
theorem brakingDist_nonneg (v a j d : Rat)
    (hv : 0 ≤ v) (ha : 0 < a) (hj : 0 < j) (hd : 0 ≤ d) :
    0 ≤ brakingDist v a j d := by
  simp only [brakingDist]
  apply Rat.mul_nonneg hv
  apply Rat.add_nonneg
  · exact div_nonneg_rat hv (Rat.mul_pos two_pos ha)
  · exact div_nonneg_rat hd hj

/-- **Strict positivity**: positive velocity gives positive braking distance. -/
theorem brakingDist_pos (v a j d : Rat)
    (hv : 0 < v) (ha : 0 < a) (hj : 0 < j) (hd : 0 ≤ d) :
    0 < brakingDist v a j d := by
  simp only [brakingDist]
  apply Rat.mul_pos hv
  have ha2 : 0 < 2 * a := Rat.mul_pos two_pos ha
  have h1 : 0 < v / (2 * a) := div_pos_rat hv ha2
  have h2 : 0 ≤ d / j := div_nonneg_rat hd hj
  exact Std.lt_of_lt_of_le h1 (le_add_nonneg_right h2)

/-- **Monotone in velocity**: more initial speed requires a longer braking distance.

    For fixed (positive) parameters, `dist` increases as `v` increases. -/
theorem brakingDist_mono_v (v₁ v₂ a j d : Rat)
    (hv1 : 0 ≤ v₁) (hv12 : v₁ ≤ v₂)
    (ha : 0 < a) (hj : 0 < j) (hd : 0 ≤ d) :
    brakingDist v₁ a j d ≤ brakingDist v₂ a j d := by
  simp only [brakingDist]
  have ha2 : 0 < 2 * a := Rat.mul_pos two_pos ha
  have hinv_nonneg : 0 ≤ (2 * a)⁻¹ := inv_nonneg_of_pos ha2
  have hv2 : 0 ≤ v₂ := Rat.le_trans hv1 hv12
  -- f(v) := v/(2a) + d/j is monotone in v (right addend d/j fixed, left varies)
  have hf12 : v₁ / (2 * a) + d / j ≤ v₂ / (2 * a) + d / j := by
    apply Rat.add_le_add_right.mpr
    rw [Rat.div_def, Rat.div_def]
    exact Rat.mul_le_mul_of_nonneg_right hv12 hinv_nonneg
  -- f(v₂) ≥ 0
  have hf2_nn : 0 ≤ v₂ / (2 * a) + d / j :=
    Rat.add_nonneg (div_nonneg_rat hv2 ha2) (div_nonneg_rat hd hj)
  -- v₁ · f(v₁) ≤ v₁ · f(v₂) ≤ v₂ · f(v₂)
  calc v₁ * (v₁ / (2 * a) + d / j)
      ≤ v₁ * (v₂ / (2 * a) + d / j) := Rat.mul_le_mul_of_nonneg_left hf12 hv1
    _ ≤ v₂ * (v₂ / (2 * a) + d / j) := Rat.mul_le_mul_of_nonneg_right hv12 hf2_nn

/-- **Monotone in delay**: more `accel_delay_max` → more braking distance needed. -/
theorem brakingDist_mono_d (v a j d₁ d₂ : Rat)
    (hv : 0 ≤ v) (hj : 0 < j) (hd12 : d₁ ≤ d₂) :
    brakingDist v a j d₁ ≤ brakingDist v a j d₂ := by
  simp only [brakingDist]
  apply Rat.mul_le_mul_of_nonneg_left _ hv
  -- v/(2a) + d₁/j ≤ v/(2a) + d₂/j: left addend fixed, right varies
  apply Rat.add_le_add_left.mpr
  rw [Rat.div_def, Rat.div_def]
  exact Rat.mul_le_mul_of_nonneg_right hd12 (inv_nonneg_of_pos hj)

/-- **No-delay formula**: when `accel_delay_max = 0`, reduces to the classic kinematics
    formula `v² / (2a)`. -/
theorem brakingDist_no_delay (v a j : Rat) :
    brakingDist v a j 0 = v * v / (2 * a) := by
  simp only [brakingDist, Rat.div_def, Rat.zero_mul, Rat.add_zero]
  -- Goal: v * (v * (2 * a)⁻¹) = v * v * (2 * a)⁻¹
  exact (Rat.mul_assoc v v (2 * a)⁻¹).symm

/-- **No-delay non-negativity**: `v²/(2a) ≥ 0` for `v ≥ 0`, `a > 0`. -/
theorem brakingDist_no_delay_nonneg (v a j : Rat)
    (hv : 0 ≤ v) (ha : 0 < a) :
    0 ≤ brakingDist v a j 0 := by
  rw [brakingDist_no_delay v a j]
  exact div_nonneg_rat (Rat.mul_nonneg hv hv) (Rat.mul_pos two_pos ha)

/-- **Alternative form**: `dist = v · v / (2a) + v · d / j` (distributive expansion). -/
theorem brakingDist_alt_form (v a j d : Rat) :
    brakingDist v a j d = v * v / (2 * a) + v * d / j := by
  unfold brakingDist
  rw [Rat.mul_add]
  -- Goal: v * (v / (2*a)) + v * (d / j) = v*v/(2*a) + v*d/j
  congr 1
  · -- v * (v / (2*a)) = v * v / (2*a)
    simp only [Rat.div_def]
    exact (Rat.mul_assoc v v (2 * a)⁻¹).symm
  · -- v * (d / j) = v * d / j
    simp only [Rat.div_def]
    exact (Rat.mul_assoc v d j⁻¹).symm

/-- **Quadratic scaling** (no-delay case): doubling velocity quadruples braking distance.

    Reflects the v² term: dist(2v) = (2v)²/(2a) = 4·v²/(2a) = 4·dist(v). -/
theorem brakingDist_double_v_no_delay (v a j : Rat) :
    brakingDist (2 * v) a j 0 = 4 * brakingDist v a j 0 := by
  rw [brakingDist_no_delay, brakingDist_no_delay]
  -- Goal: 2*v*(2*v) / (2*a) = 4 * (v*v / (2*a))
  -- Step 1: show 2*v*(2*v) = 4*(v*v)
  have key : (2 : Rat) * v * (2 * v) = 4 * (v * v) := by
    calc (2 : Rat) * v * (2 * v)
        = 2 * (v * (2 * v))   := Rat.mul_assoc 2 v (2 * v)
      _ = 2 * ((2 * v) * v)   := by rw [Rat.mul_comm v (2 * v)]
      _ = 2 * (2 * (v * v))   := by rw [Rat.mul_assoc]
      _ = 2 * 2 * (v * v)     := (Rat.mul_assoc 2 2 (v * v)).symm
      _ = 4 * (v * v)         := by rw [show (2 : Rat) * 2 = 4 from by native_decide]
  rw [key]
  -- Goal: 4*(v*v) / (2*a) = 4 * (v*v / (2*a))
  rw [Rat.div_def, Rat.div_def]
  exact Rat.mul_assoc 4 (v * v) (2 * a)⁻¹

end PX4.BrakingDistance
