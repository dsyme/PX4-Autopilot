/-!
# PX4 `interpolate` Function — Formal Verification

🔬 Lean Squad automated formal verification.

This file models and proves correctness properties of `math::interpolate` from
PX4-Autopilot's `mathlib`:

- **C++ source**: `src/lib/mathlib/math/Functions.hpp` (approx. line 152)
- **Informal spec**: `formal-verification/specs/interpolate_informal.md`

## Model

We model the function over `Rat` (rational numbers) for exact piecewise-linear semantics.
The C++ template uses `float`/`double`; the Lean model is a faithful rational abstraction.

```cpp
// C++ (condensed):
template<typename T>
const T interpolate(const T &value, const T &x_low, const T &x_high,
                    const T &y_low, const T &y_high) {
    if (value <= x_low) {
        return y_low;
    } else if (value > x_high) {
        return y_high;
    } else {
        T a = (y_high - y_low) / (x_high - x_low);
        T b = y_low - (a * x_low);
        return (a * value) + b;
    }
}
```

## Approximations / Out of Scope

- **IEEE 754 float semantics**: NaN, infinity, and rounding are not modelled.
- **Precondition required**: `x_low < x_high` must hold for theorems about interior
  behaviour; the C++ invokes division-by-zero otherwise.
- **Template generality**: Only the rational abstraction is modelled; overflow for
  fixed-width integer types is out of scope.
-/

namespace PX4.Interpolate

/-- Pure functional model of `math::interpolate` over `Rat`.

    - When `value ≤ x_low`: returns `y_low` (clamped low).
    - When `value > x_high`: returns `y_high` (clamped high).
    - Otherwise (`x_low < value ≤ x_high`): linear interpolation. -/
def interpolate (value x_low x_high y_low y_high : Rat) : Rat :=
  if value ≤ x_low then y_low
  else if value > x_high then y_high
  else
    let a := (y_high - y_low) / (x_high - x_low)
    let b := y_low - a * x_low
    a * value + b

-- Sanity checks: model produces expected numeric outputs.
#eval interpolate 0       0 1  0  10  -- 0.0  (at low endpoint, clamped)
#eval interpolate (1/2)   0 1  0  10  -- 5.0  (midpoint)
#eval interpolate 1       0 1  0  10  -- 10.0 (at high endpoint)
#eval interpolate (-1)    0 1  0  10  -- 0.0  (clamped low)
#eval interpolate 2       0 1  0  10  -- 10.0 (clamped high)
#eval interpolate (1/4)   0 1  0  10  -- 2.5
#eval interpolate (1/2)   0 1  5   5  -- 5.0  (constant y)
#eval interpolate (1/2)   0 1  10  0  -- 5.0  (reversed y, midpoint = 5)

/-! ## Boundary saturation lemmas -/

/-- Below or at the low endpoint: output is clamped to `y_low`. -/
theorem interpolate_clamped_low (value x_low x_high y_low y_high : Rat)
    (h : value ≤ x_low) :
    interpolate value x_low x_high y_low y_high = y_low := by
  simp [interpolate, h]

/-- Above the high endpoint: output is clamped to `y_high`.

    Requires `x_low < x_high` to ensure the first branch is not also triggered. -/
theorem interpolate_clamped_high (value x_low x_high y_low y_high : Rat)
    (hlh : x_low < x_high) (h : value > x_high) :
    interpolate value x_low x_high y_low y_high = y_high := by
  simp only [interpolate]
  rw [if_neg (Rat.not_le.mpr (Std.lt_of_lt_of_le hlh (Rat.le_of_lt h))), if_pos h]

/-- At the low endpoint (`value = x_low`), output is exactly `y_low`.

    The `≤` branch is triggered since `x_low ≤ x_low`. -/
theorem interpolate_at_low (x_low x_high y_low y_high : Rat) :
    interpolate x_low x_low x_high y_low y_high = y_low := by
  simp [interpolate]

/-- At the high endpoint (`value = x_high`), output is exactly `y_high`,
    provided `x_low < x_high`.

    The C++ does NOT catch `value = x_high` via the `> x_high` branch; it falls
    through to the linear formula.  This theorem proves the formula evaluates to
    `y_high` algebraically. -/
theorem interpolate_at_high (x_low x_high y_low y_high : Rat)
    (hlh : x_low < x_high) :
    interpolate x_high x_low x_high y_low y_high = y_high := by
  simp only [interpolate]
  rw [if_neg (Rat.not_le.mpr hlh), if_neg Rat.lt_irrefl]
  have hne : x_high - x_low ≠ 0 :=
    Rat.ne_of_gt ((Rat.lt_iff_sub_pos x_low x_high).mp hlh)
  have ha_mul : (y_high - y_low) / (x_high - x_low) * (x_high - x_low) = y_high - y_low := by
    rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ hne, Rat.mul_one]
  have h1 : (y_high - y_low) / (x_high - x_low) * x_high +
            (y_low - (y_high - y_low) / (x_high - x_low) * x_low)
            = (y_high - y_low) / (x_high - x_low) * (x_high - x_low) + y_low := by
    simp only [Rat.sub_eq_add_neg, Rat.mul_add, Rat.mul_neg, Rat.add_comm, Rat.add_left_comm]
  rw [h1, ha_mul]
  exact Rat.sub_add_cancel

/-! ## Constant output -/

/-- When both y endpoints are equal, the output is always that constant. -/
theorem interpolate_const (value x_low x_high c : Rat) :
    interpolate value x_low x_high c c = c := by
  simp only [interpolate]
  split
  · rfl
  · rename_i h1; split
    · rfl
    · -- Linear formula: numerator is 0, so a = 0, result = 0*value + c = c
      simp [Rat.sub_self, Rat.div_def, Rat.zero_mul,
            Rat.sub_eq_add_neg, Rat.neg_zero, Rat.add_zero, Rat.zero_add]

/-! ## Slope non-negativity -/

/-- The interpolation slope `a = (y_high - y_low) / (x_high - x_low)` is non-negative
    when `y_low ≤ y_high` and `x_low < x_high`. -/
theorem interpolate_slope_nonneg (x_low x_high y_low y_high : Rat)
    (hlh : x_low < x_high) (hylh : y_low ≤ y_high) :
    0 ≤ (y_high - y_low) / (x_high - x_low) := by
  have hden_pos : 0 < x_high - x_low := (Rat.lt_iff_sub_pos x_low x_high).mp hlh
  have hnum_nn : 0 ≤ y_high - y_low := (Rat.le_iff_sub_nonneg y_low y_high).mp hylh
  rw [Rat.div_def]
  exact Rat.mul_nonneg hnum_nn (Rat.le_of_lt (Rat.inv_pos.mpr hden_pos))

/-! ## Monotonicity in the interior -/

/-- The interpolated output is non-decreasing when y endpoints are ordered the same way
    as x endpoints (`y_low ≤ y_high`), for pairs of inputs in the interior
    `x_low < v1 ≤ v2 ≤ x_high`. -/
theorem interpolate_mono_interior (x_low x_high y_low y_high v1 v2 : Rat)
    (hlh : x_low < x_high) (hylh : y_low ≤ y_high)
    (hv1lo : x_low < v1) (hv1v2 : v1 ≤ v2) (hv2hi : v2 ≤ x_high) :
    interpolate v1 x_low x_high y_low y_high ≤
    interpolate v2 x_low x_high y_low y_high := by
  simp only [interpolate]
  have hv1_not_low : ¬(v1 ≤ x_low) := Rat.not_le.mpr hv1lo
  have hv1_not_high : ¬(v1 > x_high) :=
    Rat.not_lt.mpr (Rat.le_trans hv1v2 hv2hi)
  have hv2_not_low : ¬(v2 ≤ x_low) :=
    Rat.not_le.mpr (Std.lt_of_lt_of_le hv1lo hv1v2)
  have hv2_not_high : ¬(v2 > x_high) := Rat.not_lt.mpr hv2hi
  rw [if_neg hv1_not_low, if_neg hv1_not_high,
      if_neg hv2_not_low, if_neg hv2_not_high]
  -- Both use the linear formula. Goal: a*v1 + b ≤ a*v2 + b.
  have ha_nn := interpolate_slope_nonneg x_low x_high y_low y_high hlh hylh
  have hmono : (y_high - y_low) / (x_high - x_low) * v1 ≤
               (y_high - y_low) / (x_high - x_low) * v2 :=
    Rat.mul_le_mul_of_nonneg_left hv1v2 ha_nn
  exact Rat.add_le_add_right.mpr hmono

/-! ## Output range -/

/-- Upper bound: when `y_low ≤ y_high` and `x_low < x_high`, the output is at most
    `y_high` for all inputs. -/
theorem interpolate_le_high (value x_low x_high y_low y_high : Rat)
    (hlh : x_low < x_high) (hylh : y_low ≤ y_high) :
    interpolate value x_low x_high y_low y_high ≤ y_high := by
  simp only [interpolate]
  split
  · exact hylh
  · split
    · exact Rat.le_refl
    · rename_i hval_not_lo hval_not_hi
      have hval_hi : value ≤ x_high := Rat.not_lt.mp hval_not_hi
      have hne : x_high - x_low ≠ 0 :=
        Rat.ne_of_gt ((Rat.lt_iff_sub_pos x_low x_high).mp hlh)
      have ha_nn := interpolate_slope_nonneg x_low x_high y_low y_high hlh hylh
      have ha_mul : (y_high - y_low) / (x_high - x_low) * (x_high - x_low) = y_high - y_low := by
        rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ hne, Rat.mul_one]
      have hrw : (y_high - y_low) / (x_high - x_low) * value +
                 (y_low - (y_high - y_low) / (x_high - x_low) * x_low)
                 = (y_high - y_low) / (x_high - x_low) * (value - x_low) + y_low := by
        simp only [Rat.sub_eq_add_neg, Rat.mul_add, Rat.mul_neg, Rat.add_comm, Rat.add_left_comm]
      rw [hrw]
      have hval_sub : value - x_low ≤ x_high - x_low := by
        simp only [Rat.sub_eq_add_neg]; exact Rat.add_le_add_right.mpr hval_hi
      have hstep : (y_high - y_low) / (x_high - x_low) * (value - x_low) ≤ y_high - y_low := by
        have h := Rat.mul_le_mul_of_nonneg_left hval_sub ha_nn
        rw [ha_mul] at h; exact h
      exact Rat.le_sub_iff.mp hstep

/-- Lower bound: when `y_low ≤ y_high` and `x_low < x_high`, the output is at least
    `y_low` for all inputs. -/
theorem interpolate_ge_low (value x_low x_high y_low y_high : Rat)
    (hlh : x_low < x_high) (hylh : y_low ≤ y_high) :
    y_low ≤ interpolate value x_low x_high y_low y_high := by
  simp only [interpolate]
  split
  · exact Rat.le_refl
  · split
    · exact hylh
    · rename_i hval_not_lo hval_not_hi
      have hval_lo : x_low < value := Rat.not_le.mp hval_not_lo
      have ha_nn := interpolate_slope_nonneg x_low x_high y_low y_high hlh hylh
      have hrw : (y_high - y_low) / (x_high - x_low) * value +
                 (y_low - (y_high - y_low) / (x_high - x_low) * x_low)
                 = (y_high - y_low) / (x_high - x_low) * (value - x_low) + y_low := by
        simp only [Rat.sub_eq_add_neg, Rat.mul_add, Rat.mul_neg, Rat.add_comm, Rat.add_left_comm]
      rw [hrw]
      have hstep : 0 ≤ (y_high - y_low) / (x_high - x_low) * (value - x_low) :=
        Rat.mul_nonneg ha_nn
          (Rat.le_of_lt ((Rat.lt_iff_sub_pos x_low value).mp hval_lo))
      have : 0 + y_low ≤ (y_high - y_low) / (x_high - x_low) * (value - x_low) + y_low :=
        Rat.add_le_add_right.mpr hstep
      simp only [Rat.zero_add] at this
      exact this

/-! ## Special case: identity slope -/

/-- When the x interval and y interval have the same length, the slope is 1. -/
theorem interpolate_identity_slope (x_low x_high : Rat) (hlh : x_low < x_high) :
    (x_high - x_low) / (x_high - x_low) = 1 := by
  have hne : x_high - x_low ≠ 0 :=
    Rat.ne_of_gt ((Rat.lt_iff_sub_pos x_low x_high).mp hlh)
  rw [Rat.div_def, Rat.mul_inv_cancel _ hne]

/-! ## Summary of proved properties

  | Theorem                       | Statement                                           | Status   |
  |-------------------------------|-----------------------------------------------------|----------|
  | `interpolate_clamped_low`     | `value ≤ x_low → result = y_low`                   | ✅ Proved |
  | `interpolate_clamped_high`    | `x_low < x_high → value > x_high → result = y_high`| ✅ Proved |
  | `interpolate_at_low`          | `interpolate x_low ... = y_low`                    | ✅ Proved |
  | `interpolate_at_high`         | `x_low < x_high → interpolate x_high ... = y_high` | ✅ Proved |
  | `interpolate_const`           | `y_low = y_high = c → result = c`                  | ✅ Proved |
  | `interpolate_slope_nonneg`    | slope ≥ 0 when `y_low ≤ y_high, x_low < x_high`   | ✅ Proved |
  | `interpolate_mono_interior`   | monotone non-decreasing in interior                 | ✅ Proved |
  | `interpolate_le_high`         | `y_low ≤ y_high → result ≤ y_high`                 | ✅ Proved |
  | `interpolate_ge_low`          | `y_low ≤ y_high → y_low ≤ result`                  | ✅ Proved |
  | `interpolate_identity_slope`  | (x_high-x_low)/(x_high-x_low) = 1                  | ✅ Proved |
-/

end PX4.Interpolate
