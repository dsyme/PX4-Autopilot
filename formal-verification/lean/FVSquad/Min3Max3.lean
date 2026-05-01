/-!
# PX4 `math::min3` / `math::max3` — Formal Verification

🔬 Lean Squad automated formal verification.

This file models and proves correctness properties of the 3-argument overloads
of `math::min` and `math::max` from PX4-Autopilot's `mathlib`:

- **C++ source**: `src/lib/mathlib/math/Limits.hpp`, lines 60–75
- **Informal spec**: `formal-verification/specs/min3_max3_informal.md`

## C++ Source

```cpp
template<typename _Tp>
constexpr _Tp min(_Tp a, _Tp b, _Tp c)
{
    return min(min(a, b), c);   // left-associative
}

template<typename _Tp>
constexpr _Tp max(_Tp a, _Tp b, _Tp c)
{
    return max(max(a, b), c);   // left-associative
}
```

## Model

We model `min3` and `max3` over `Int` (unbounded integers).  The C++ template
is generic over any ordered type; the `Int` model covers all integer
instantiations exactly.  Floating-point instances are captured at the
real-number level (no NaN/±∞ modelled).

## Approximations / out of scope

- **Float semantics**: NaN, ±∞, and rounding are not modelled.
- **Overflow**: `Int` is unbounded; C++ integer overflow is not modelled.
- **Template dispatch**: one instantiation modelled; the C++ template is
  parametric and this proof covers its axiomatic contract.
-/

namespace PX4.Min3Max3

-- ============================================================
-- § 0  Definitions
-- ============================================================

/-- 3-argument minimum: `min3 a b c = min (min a b) c`.
    Left-associative, matching the C++ implementation. -/
def min3 (a b c : Int) : Int := min (min a b) c

/-- 3-argument maximum: `max3 a b c = max (max a b) c`.
    Left-associative, matching the C++ implementation. -/
def max3 (a b c : Int) : Int := max (max a b) c

-- Sanity checks.
#eval min3 1 2 3   -- 1
#eval min3 3 1 2   -- 1
#eval min3 2 3 1   -- 1
#eval max3 1 2 3   -- 3
#eval max3 3 1 2   -- 3
#eval max3 7 7 7   -- 7
#eval min3 (-5) 0 5  -- -5
#eval max3 (-5) 0 5  -- 5

-- ============================================================
-- § 1  Private helpers — negation swaps min/max
-- ============================================================

private theorem neg_min_aux (a b : Int) : -(min a b) = max (-a) (-b) := by
  by_cases h : a ≤ b
  · rw [Int.min_eq_left h, Int.max_eq_left (Int.neg_le_neg h)]
  · rw [Int.min_eq_right (by omega), Int.max_eq_right (Int.neg_le_neg (by omega))]

private theorem neg_max_aux (a b : Int) : -(max a b) = min (-a) (-b) := by
  by_cases h : a ≤ b
  · rw [Int.max_eq_right h, Int.min_eq_right (Int.neg_le_neg h)]
  · rw [Int.max_eq_left (by omega), Int.min_eq_left (Int.neg_le_neg (by omega))]

-- ============================================================
-- § 2  `min3` — lower bound properties
-- ============================================================

/-- `min3 a b c` is a lower bound: it does not exceed `a`. -/
theorem min3_le_left (a b c : Int) : min3 a b c ≤ a :=
  Int.le_trans (Int.min_le_left _ _) (Int.min_le_left _ _)

/-- `min3 a b c` is a lower bound: it does not exceed `b`. -/
theorem min3_le_mid (a b c : Int) : min3 a b c ≤ b :=
  Int.le_trans (Int.min_le_left _ _) (Int.min_le_right _ _)

/-- `min3 a b c` is a lower bound: it does not exceed `c`. -/
theorem min3_le_right (a b c : Int) : min3 a b c ≤ c :=
  Int.min_le_right _ _

/-- `min3 a b c` is the *greatest* lower bound of `{a, b, c}`:
    any `x ≤ a`, `x ≤ b`, `x ≤ c` implies `x ≤ min3 a b c`. -/
theorem le_min3 {a b c x : Int} (ha : x ≤ a) (hb : x ≤ b) (hc : x ≤ c) :
    x ≤ min3 a b c := by
  unfold min3
  exact Int.le_min.mpr ⟨Int.le_min.mpr ⟨ha, hb⟩, hc⟩

-- ============================================================
-- § 3  `min3` — structural / algebraic properties
-- ============================================================

/-- Idempotence: `min3 a a a = a`. -/
theorem min3_idempotent (a : Int) : min3 a a a = a := by
  unfold min3; simp [Int.min_self]

/-- `min3` is left-commutative in its first two arguments. -/
theorem min3_left_comm (a b c : Int) : min3 a b c = min3 b a c := by
  unfold min3; rw [Int.min_comm a b]

/-- `min3` is right-commutative in its last two arguments. -/
theorem min3_right_comm (a b c : Int) : min3 a b c = min3 a c b := by
  unfold min3
  rw [Int.min_assoc, Int.min_comm b c, ← Int.min_assoc]

/-- `min3` is invariant under cyclic permutation. -/
theorem min3_rotate (a b c : Int) : min3 a b c = min3 b c a := by
  simp [min3_left_comm, min3_right_comm]

/-- `min3` is fully symmetric (any permutation gives the same result). -/
theorem min3_comm_all (a b c : Int) : min3 a b c = min3 c b a := by
  simp [min3_left_comm, min3_right_comm]

/-- Alternative associativity: `min3 a b c = min a (min b c)`. -/
theorem min3_eq_alt (a b c : Int) : min3 a b c = min a (min b c) :=
  Int.min_assoc a b c

-- ============================================================
-- § 4  `min3` — characterisation theorems
-- ============================================================

/-- If `a` is at most both `b` and `c`, then `min3 a b c = a`. -/
theorem min3_eq_of_le (a b c : Int) (h1 : a ≤ b) (h2 : a ≤ c) : min3 a b c = a := by
  unfold min3
  rw [Int.min_eq_left h1, Int.min_eq_left h2]

/-- If `b` is at most both `a` and `c`, then `min3 a b c = b`. -/
theorem min3_eq_mid_of_le (a b c : Int) (h1 : b ≤ a) (h2 : b ≤ c) : min3 a b c = b := by
  unfold min3
  rw [Int.min_eq_right h1, Int.min_eq_left h2]

/-- If `c` is at most both `a` and `b`, then `min3 a b c = c`. -/
theorem min3_eq_right_of_le (a b c : Int) (h1 : c ≤ a) (h2 : c ≤ b) : min3 a b c = c := by
  unfold min3
  rw [show min (min a b) c = c from by
    apply Int.min_eq_right
    exact Int.le_min.mpr ⟨h1, h2⟩]

-- ============================================================
-- § 5  `max3` — upper bound properties
-- ============================================================

/-- `max3 a b c` is an upper bound: it is at least `a`. -/
theorem le_max3_left (a b c : Int) : a ≤ max3 a b c :=
  Int.le_trans (Int.le_max_left _ _) (Int.le_max_left _ _)

/-- `max3 a b c` is an upper bound: it is at least `b`. -/
theorem le_max3_mid (a b c : Int) : b ≤ max3 a b c :=
  Int.le_trans (Int.le_max_right _ _) (Int.le_max_left _ _)

/-- `max3 a b c` is an upper bound: it is at least `c`. -/
theorem le_max3_right (a b c : Int) : c ≤ max3 a b c :=
  Int.le_max_right _ _

/-- `max3 a b c` is the *least* upper bound of `{a, b, c}`:
    any `a ≤ x`, `b ≤ x`, `c ≤ x` implies `max3 a b c ≤ x`. -/
theorem max3_le {a b c x : Int} (ha : a ≤ x) (hb : b ≤ x) (hc : c ≤ x) :
    max3 a b c ≤ x := by
  unfold max3
  exact Int.max_le.mpr ⟨Int.max_le.mpr ⟨ha, hb⟩, hc⟩

-- ============================================================
-- § 6  `max3` — structural / algebraic properties
-- ============================================================

/-- Idempotence: `max3 a a a = a`. -/
theorem max3_idempotent (a : Int) : max3 a a a = a := by
  unfold max3; simp [Int.max_self]

/-- `max3` is left-commutative in its first two arguments. -/
theorem max3_left_comm (a b c : Int) : max3 a b c = max3 b a c := by
  unfold max3; rw [Int.max_comm a b]

/-- `max3` is right-commutative in its last two arguments. -/
theorem max3_right_comm (a b c : Int) : max3 a b c = max3 a c b := by
  unfold max3
  rw [Int.max_assoc, Int.max_comm b c, ← Int.max_assoc]

/-- `max3` is invariant under cyclic permutation. -/
theorem max3_rotate (a b c : Int) : max3 a b c = max3 b c a := by
  simp [max3_left_comm, max3_right_comm]

/-- Alternative associativity: `max3 a b c = max a (max b c)`. -/
theorem max3_eq_alt (a b c : Int) : max3 a b c = max a (max b c) :=
  Int.max_assoc a b c

-- ============================================================
-- § 7  `max3` — characterisation theorems
-- ============================================================

/-- If `a` is at least both `b` and `c`, then `max3 a b c = a`. -/
theorem max3_eq_of_ge (a b c : Int) (h1 : b ≤ a) (h2 : c ≤ a) : max3 a b c = a := by
  unfold max3
  rw [Int.max_eq_left h1, Int.max_eq_left h2]

/-- If `b` is at least both `a` and `c`, then `max3 a b c = b`. -/
theorem max3_eq_mid_of_ge (a b c : Int) (h1 : a ≤ b) (h2 : c ≤ b) : max3 a b c = b := by
  unfold max3
  rw [Int.max_eq_right h1, Int.max_eq_left h2]

/-- If `c` is at least both `a` and `b`, then `max3 a b c = c`. -/
theorem max3_eq_right_of_ge (a b c : Int) (h1 : a ≤ c) (h2 : b ≤ c) : max3 a b c = c := by
  unfold max3
  apply Int.max_eq_right
  exact Int.max_le.mpr ⟨h1, h2⟩

-- ============================================================
-- § 8  Duality between `min3` and `max3`
-- ============================================================

/-- Duality: `max3 a b c = -(min3 (-a) (-b) (-c))`.

    Negation maps maxima to minima: the maximum of three values equals the
    negation of the minimum of their negations.  This is the standard
    De Morgan-style duality for lattice operations. -/
theorem max3_neg_min3 (a b c : Int) : max3 a b c = -(min3 (-a) (-b) (-c)) := by
  unfold max3 min3
  rw [show -(min (min (-a) (-b)) (-c)) = max (-(min (-a) (-b))) (- -c) from
        neg_min_aux _ _]
  rw [show -(min (-a) (-b)) = max (- -a) (- -b) from neg_min_aux _ _]
  simp [Int.neg_neg]

/-- Duality: `min3 a b c = -(max3 (-a) (-b) (-c))`. -/
theorem min3_neg_max3 (a b c : Int) : min3 a b c = -(max3 (-a) (-b) (-c)) := by
  unfold max3 min3
  rw [show -(max (max (-a) (-b)) (-c)) = min (-(max (-a) (-b))) (- -c) from
        neg_max_aux _ _]
  rw [show -(max (-a) (-b)) = min (- -a) (- -b) from neg_max_aux _ _]
  simp [Int.neg_neg]

-- ============================================================
-- § 9  Interaction between min3 and max3
-- ============================================================

/-- `min3` result is bounded above by `max3` result. -/
theorem min3_le_max3 (a b c : Int) : min3 a b c ≤ max3 a b c :=
  Int.le_trans (min3_le_left a b c) (le_max3_left a b c)

/-- `min3` and `max3` agree on identical inputs. -/
theorem min3_eq_max3_of_eq (a : Int) : min3 a a a = max3 a a a := by
  rw [min3_idempotent, max3_idempotent]

end PX4.Min3Max3
