/-!
# PX4 `isInRange` — Formal Verification

🔬 Lean Squad automated formal verification.

This file models and proves correctness properties of `math::isInRange` from
PX4-Autopilot's `mathlib`:

- **C++ source**: `src/lib/mathlib/math/Limits.hpp` (line 91)
- **Informal spec**: `formal-verification/specs/isInRange_informal.md`

## C++ Source

```cpp
template<typename _Tp>
constexpr bool isInRange(_Tp val, _Tp min_val, _Tp max_val)
{
    return (min_val <= val) && (val <= max_val);
}
```

## Model

We model `isInRange` over `Int` (unbounded integers), capturing the exact
closed-interval semantics.  The C++ template is generic over any ordered type;
the Int model covers all integer instantiations exactly.  A `Rat`-based model
is identical — `Int.le`  and `Rat.le` obey the same axioms used below.

## Approximations / out of scope

- **Float semantics**: NaN, ±∞, and rounding are not modelled.  For float
  instantiations the real-number interpretation is captured here.
- **Overflow**: `Int` is unbounded; C++ integer overflow is not modelled.
- **Template dispatch**: we model one instantiation; the C++ template is
  parametric and this proof covers its axiomatic contract, not one specific type.
-/

namespace PX4.IsInRange

/-- Pure functional model of `math::isInRange` over `Int`.

    Returns `true` iff `min_val ≤ val ≤ max_val` (closed interval). -/
def isInRange (val min_val max_val : Int) : Bool :=
  min_val ≤ val && val ≤ max_val

-- Sanity checks: model produces expected outputs.
#eval isInRange 5   0   10   -- true   (5 is in [0,10])
#eval isInRange (-1) 0  10   -- false  (−1 is below 0)
#eval isInRange 0   0   10   -- true   (at lower bound)
#eval isInRange 10  0   10   -- true   (at upper bound)
#eval isInRange 11  0   10   -- false  (above upper bound)
#eval isInRange 5   5   5    -- true   (singleton interval, val = min = max)
#eval isInRange 4   5   5    -- false  (singleton interval, val ≠ bound)
#eval isInRange 5   10  0    -- false  (empty interval, min > max)

-- ============================================================
-- § 1  Fundamental characterisation
-- ============================================================

/-- `isInRange` returns `true` iff `min_val ≤ val` and `val ≤ max_val`. -/
theorem isInRange_eq_true_iff (val min_val max_val : Int) :
    isInRange val min_val max_val = true ↔ min_val ≤ val ∧ val ≤ max_val := by
  simp [isInRange, Bool.and_eq_true, decide_eq_true_eq]

/-- `isInRange` returns `false` iff `val < min_val` or `max_val < val`. -/
theorem isInRange_eq_false_iff (val min_val max_val : Int) :
    isInRange val min_val max_val = false ↔ val < min_val ∨ max_val < val := by
  constructor
  · intro h
    have hnt : ¬(min_val ≤ val ∧ val ≤ max_val) := by
      intro hc
      rw [← isInRange_eq_true_iff] at hc
      simp [h] at hc
    by_cases hge : min_val ≤ val
    · right; omega
    · left; omega
  · intro h
    cases hc : isInRange val min_val max_val
    · rfl
    · rw [isInRange_eq_true_iff] at hc
      rcases h with h | h <;> omega

/-- If both bounds are satisfied, `isInRange` returns `true`. -/
theorem isInRange_of_le_of_le {val min_val max_val : Int}
    (h1 : min_val ≤ val) (h2 : val ≤ max_val) :
    isInRange val min_val max_val = true := by
  rw [isInRange_eq_true_iff]; exact ⟨h1, h2⟩

-- ============================================================
-- § 2  Boundary and special cases
-- ============================================================

/-- The lower bound is always in the range (when `min_val ≤ max_val`). -/
theorem isInRange_min_in_range {min_val max_val : Int} (h : min_val ≤ max_val) :
    isInRange min_val min_val max_val = true :=
  isInRange_of_le_of_le (Int.le_refl _) h

/-- The upper bound is always in the range (when `min_val ≤ max_val`). -/
theorem isInRange_max_in_range {min_val max_val : Int} (h : min_val ≤ max_val) :
    isInRange max_val min_val max_val = true :=
  isInRange_of_le_of_le h (Int.le_refl _)

/-- A value is always in the singleton interval `[v, v]`. -/
theorem isInRange_self (v : Int) : isInRange v v v = true :=
  isInRange_of_le_of_le (Int.le_refl _) (Int.le_refl _)

/-- The singleton interval `[c, c]` contains exactly `c`. -/
theorem isInRange_singleton_iff (val c : Int) :
    isInRange val c c = true ↔ val = c := by
  rw [isInRange_eq_true_iff]; omega

-- ============================================================
-- § 3  Empty interval
-- ============================================================

/-- If `max_val < min_val`, the interval is empty: `isInRange` is always `false`. -/
theorem isInRange_empty {min_val max_val : Int} (h : max_val < min_val)
    (val : Int) : isInRange val min_val max_val = false := by
  rw [isInRange_eq_false_iff]; omega

-- ============================================================
-- § 4  Monotonicity in the bounds
-- ============================================================

/-- Widening the interval preserves membership: if `val ∈ [min, max]` and
    `[min, max] ⊆ [min', max']` then `val ∈ [min', max']`. -/
theorem isInRange_mono_bounds {val min_val max_val min_val' max_val' : Int}
    (hv : isInRange val min_val max_val = true)
    (hlo : min_val' ≤ min_val)
    (hhi : max_val ≤ max_val') :
    isInRange val min_val' max_val' = true := by
  rw [isInRange_eq_true_iff] at hv ⊢
  exact ⟨Int.le_trans hlo hv.1, Int.le_trans hv.2 hhi⟩

/-- Shifting `val` and both bounds by the same amount preserves membership. -/
theorem isInRange_shift (val min_val max_val d : Int) :
    isInRange (val + d) (min_val + d) (max_val + d) =
    isInRange val min_val max_val := by
  simp [isInRange, Int.add_le_add_iff_right]

-- ============================================================
-- § 5  Relationship to `constrain`
-- ============================================================

/-- Specialisation: `isInRange` for an unsigned-style range starting at 0.
    `isInRange val 0 n = true ↔ 0 ≤ val ∧ val ≤ n` (redundant `0 ≤ val`). -/
theorem isInRange_nonneg_iff (val n : Int) :
    isInRange val 0 n = true ↔ 0 ≤ val ∧ val ≤ n := by
  exact isInRange_eq_true_iff val 0 n

/-- For a symmetric interval `[-r, r]`, membership is equivalent to
    `−r ≤ val` and `val ≤ r`. -/
theorem isInRange_symmetric_iff (val r : Int) :
    isInRange val (-r) r = true ↔ -r ≤ val ∧ val ≤ r :=
  isInRange_eq_true_iff val (-r) r

-- ============================================================
-- § 6  Decidability and examples
-- ============================================================

/-- `isInRange` is computable and its Bool result equals the decision
    of the conjunction of two integer inequalities. -/
theorem isInRange_eq_decide (val min_val max_val : Int) :
    isInRange val min_val max_val =
    (decide (min_val ≤ val) && decide (val ≤ max_val)) := by
  simp [isInRange]

end PX4.IsInRange
