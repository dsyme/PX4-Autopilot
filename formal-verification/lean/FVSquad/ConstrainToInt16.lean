/-!
# `constrainFloatToInt16` — Formal Verification

🔬 *Lean Squad automated formal verification.*

This file models and proves correctness properties of `constrainFloatToInt16`
from PX4-Autopilot's `mathlib`:

- **C++ source**: `src/lib/mathlib/math/Limits.hpp`
- **Informal spec**: `formal-verification/specs/constrainFloatToInt16_informal.md`

## C++ Source

```cpp
constexpr int16_t constrainFloatToInt16(float value)
{
    return (int16_t)math::constrain(value, (float)INT16_MIN, (float)INT16_MAX);
}
```

where `math::constrain`:

```cpp
template<typename _Tp>
constexpr _Tp constrain(_Tp val, _Tp min_val, _Tp max_val)
{
    return (val < min_val) ? min_val : ((val > max_val) ? max_val : val);
}
```

## Model

We model `constrainFloatToInt16` over `Int` (unbounded integers), abstracting
away floating-point rounding errors.  The integer model captures the exact
clamping semantics:

```
constrainToInt16 v =
    if v < INT16_MIN then INT16_MIN
    else if v > INT16_MAX then INT16_MAX
    else v
```

This is equivalent to `math::constrain(v, INT16_MIN, INT16_MAX)`.

## Named constants

We use `abbrev` so that `omega` can see through the definitions and reason
about the concrete values directly.

## Approximations / Out of Scope

- **Float-to-integer rounding**: the C++ function receives a `float`; this model
  assumes the input is already an integer (or has been rounded to the nearest
  integer by the caller).  For integer inputs there is no rounding.
- **Float infinities / NaN**: not modelled.  `math::constrain` with float bounds
  will clamp NaN inputs to INT16_MIN; this model only handles finite inputs.
- **Overflow**: `Int` is unbounded; intermediate C++ integer overflow is not
  modelled.
-/

namespace PX4.ConstrainToInt16

/-- Lower bound of the int16_t range. -/
abbrev INT16_MIN : Int := -32768
/-- Upper bound of the int16_t range. -/
abbrev INT16_MAX : Int := 32767

/-- Pure integer model of `constrainFloatToInt16`.
    Clamps `v` to the closed interval `[INT16_MIN, INT16_MAX]`. -/
def constrainToInt16 (v : Int) : Int :=
  if v < INT16_MIN then INT16_MIN
  else if v > INT16_MAX then INT16_MAX
  else v

-- Sanity checks
#eval constrainToInt16 0          -- 0
#eval constrainToInt16 32767      -- 32767
#eval constrainToInt16 32768      -- 32767 (clamped)
#eval constrainToInt16 (-32768)   -- -32768
#eval constrainToInt16 (-32769)   -- -32768 (clamped)
#eval constrainToInt16 100        -- 100

-- ============================================================
-- § 1  Range safety: result always lies in [INT16_MIN, INT16_MAX]
-- ============================================================

/-- The result is always at least `INT16_MIN`. -/
theorem constrainToInt16_ge_min (v : Int) :
    INT16_MIN ≤ constrainToInt16 v := by
  simp only [constrainToInt16, INT16_MIN, INT16_MAX]
  by_cases h1 : v < -32768
  · simp [h1]
  · by_cases h2 : v > 32767
    · simp [show ¬v < -32768 from h1, h2]
    · simp [show ¬v < -32768 from h1, show ¬v > 32767 from h2]; omega

/-- The result is always at most `INT16_MAX`. -/
theorem constrainToInt16_le_max (v : Int) :
    constrainToInt16 v ≤ INT16_MAX := by
  simp only [constrainToInt16, INT16_MIN, INT16_MAX]
  by_cases h1 : v < -32768
  · simp [h1]
  · by_cases h2 : v > 32767
    · simp [show ¬v < -32768 from h1, h2]
    · simp [show ¬v < -32768 from h1, show ¬v > 32767 from h2]; omega

/-- The result is always in `[INT16_MIN, INT16_MAX]`. -/
theorem constrainToInt16_in_range (v : Int) :
    INT16_MIN ≤ constrainToInt16 v ∧ constrainToInt16 v ≤ INT16_MAX :=
  ⟨constrainToInt16_ge_min v, constrainToInt16_le_max v⟩

-- ============================================================
-- § 2  Identity: already-in-range values are unchanged
-- ============================================================

/-- If `v` is already in `[INT16_MIN, INT16_MAX]`, the result is `v`. -/
theorem constrainToInt16_id {v : Int}
    (hlo : INT16_MIN ≤ v) (hhi : v ≤ INT16_MAX) :
    constrainToInt16 v = v := by
  simp only [constrainToInt16, INT16_MIN, INT16_MAX] at *
  have h1 : ¬v < -32768 := by omega
  have h2 : ¬v > 32767 := by omega
  simp [h1, h2]

-- ============================================================
-- § 3  Clamping: out-of-range values map to the nearer bound
-- ============================================================

/-- If `v < INT16_MIN`, the result is `INT16_MIN`. -/
theorem constrainToInt16_clamp_low {v : Int} (h : v < INT16_MIN) :
    constrainToInt16 v = INT16_MIN := by
  simp only [constrainToInt16, INT16_MIN, INT16_MAX] at *
  simp [h]

/-- If `v > INT16_MAX`, the result is `INT16_MAX`. -/
theorem constrainToInt16_clamp_high {v : Int} (h : v > INT16_MAX) :
    constrainToInt16 v = INT16_MAX := by
  simp only [constrainToInt16, INT16_MIN, INT16_MAX] at *
  have h1 : ¬v < -32768 := by omega
  simp [h1, h]

-- ============================================================
-- § 4  Idempotence: applying constrainToInt16 twice is the same as once
-- ============================================================

/-- `constrainToInt16` is idempotent. -/
theorem constrainToInt16_idempotent (v : Int) :
    constrainToInt16 (constrainToInt16 v) = constrainToInt16 v := by
  apply constrainToInt16_id
  · exact constrainToInt16_ge_min v
  · exact constrainToInt16_le_max v

-- ============================================================
-- § 5  Monotonicity
-- ============================================================

/-- `constrainToInt16` is monotone: `a ≤ b → result a ≤ result b`. -/
theorem constrainToInt16_mono {a b : Int} (h : a ≤ b) :
    constrainToInt16 a ≤ constrainToInt16 b := by
  simp only [constrainToInt16, INT16_MIN, INT16_MAX]
  by_cases ha1 : a < -32768
  · by_cases hb1 : b < -32768
    · simp [ha1, hb1]
    · by_cases hb2 : b > 32767
      · simp [ha1, show ¬b < -32768 from hb1, hb2]
      · simp [ha1, show ¬b < -32768 from hb1, show ¬b > 32767 from hb2]; omega
  · by_cases ha2 : a > 32767
    · have hb2 : b > 32767 := by omega
      simp [show ¬a < -32768 from ha1, ha2, show ¬b < -32768 from (by omega), hb2]
    · by_cases hb1 : b < -32768
      · omega
      · by_cases hb2 : b > 32767
        · simp [show ¬a < -32768 from ha1, show ¬a > 32767 from ha2,
                show ¬b < -32768 from hb1, hb2]; omega
        · simp [show ¬a < -32768 from ha1, show ¬a > 32767 from ha2,
                show ¬b < -32768 from hb1, show ¬b > 32767 from hb2]; omega

-- ============================================================
-- § 6  Characterisation: iff conditions for each case
-- ============================================================

/-- The result equals `INT16_MIN` iff `v ≤ INT16_MIN`. -/
theorem constrainToInt16_eq_min_iff (v : Int) :
    constrainToInt16 v = INT16_MIN ↔ v ≤ INT16_MIN := by
  simp only [constrainToInt16, INT16_MIN, INT16_MAX]
  constructor
  · intro h
    by_cases h1 : v < -32768
    · simp [h1] at h; omega
    · by_cases h2 : v > 32767
      · simp [show ¬v < -32768 from h1, h2] at h
      · simp [show ¬v < -32768 from h1, show ¬v > 32767 from h2] at h; omega
  · intro h
    have h1 : v < -32768 ∨ v = -32768 := by omega
    cases h1 with
    | inl h1 => simp [h1]
    | inr h1 => simp [h1]

/-- The result equals `INT16_MAX` iff `v ≥ INT16_MAX`. -/
theorem constrainToInt16_eq_max_iff (v : Int) :
    constrainToInt16 v = INT16_MAX ↔ INT16_MAX ≤ v := by
  simp only [constrainToInt16, INT16_MIN, INT16_MAX]
  constructor
  · intro h
    by_cases h1 : v < -32768
    · simp [h1] at h        -- h becomes -32768 = 32767, contradiction
    · by_cases h2 : v > 32767
      · simp [show ¬v < -32768 from h1, h2] at h; omega  -- h : 32767=32767, goal: 32767≤v
      · simp [show ¬v < -32768 from h1, show ¬v > 32767 from h2] at h; omega
  · intro h
    have h2 : v > 32767 ∨ v = 32767 := by omega
    cases h2 with
    | inl h2 =>
      have h1 : ¬v < -32768 := by omega
      simp [h1, h2]
    | inr h2 =>
      have h1 : ¬v < -32768 := by omega
      simp [h2]

end PX4.ConstrainToInt16
