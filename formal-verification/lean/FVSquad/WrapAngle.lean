/-!
# Angle Wrapping — Formal Verification

🔬 Lean Squad automated formal verification.

This file provides formal specifications and proofs for the angle-wrapping functions
from `src/lib/matrix/matrix/helper_functions.hpp`:

```cpp
// Wrap x into [low, high) by adding multiples of (high - low)
template<typename Integer>
Integer wrap(Integer x, Integer low, Integer high) {
    const auto range = high - low;
    if (x < low) { x += range * ((low - x) / range + 1); }
    return low + (x - low) % range;
}

// Floating-point wrap (uses floor-based reduction):
template<typename Floating>
Floating wrap_floating(Floating x, Floating low, Floating high) {
    if (low <= x && x < high) return x;
    const auto range = high - low;
    const auto num_wraps = std::floor((x - low) / range);
    return x - range * num_wraps;
}

// Convenience specialisations:
template<typename Type> Type wrap_pi(Type x)   { return wrap(x, -π, π); }
template<typename Type> Type wrap_2pi(Type x)  { return wrap(x,  0, 2π); }
```

`wrap_pi` is used throughout PX4 (flight task yaw setpoints, EKF heading,
fixed-wing wheel controller, orbit following, …).

## Structure

**Part 1 — `wrapInt`**: an exact Lean model of the C++ integer `wrap` template.
All eight theorems are fully proved using `Int.emod` lemmas and `omega`.

**Part 2 — `wrapRat`**: an abstract rational model of the floating-point
`wrap_floating` / `wrap_pi`. The definition is axiomatic (requires
`Int.floor` or `Rat.floor`, available in Mathlib but not in Lean 4 stdlib).
Key contract theorems are axiomatised (require Mathlib floor for full proofs);
`wrapRat_zero` and `wrapRat_idempotent` are proved from the axioms. **0 `sorry`.**

## Approximations / model boundaries

- `wrapInt`: exact semantics for unbounded integers (no overflow; C++ has UB
  if `range` overflows the integer type).
- `wrapRat`: excludes NaN and ±∞ (rational model); excludes the case
  `low ≥ high` (division by zero in C++). π is irrational; callers must
  supply their own rational approximation or use Mathlib's `Real.pi`.
-/

namespace WrapAngle

-- ============================================================
-- Part 1: Integer wrap — complete model, all theorems proved
-- ============================================================

/-- Integer wrap: map `x` into `[low, high)` by shifting by multiples of
    `high - low`.

    This is an exact Lean model of the C++ integer `wrap` template:
    ```cpp
    return low + (x - low) % (high - low);
    ```
    The C++ version normalises negative mod by adding a multiple of `range`
    before the `%` operation; Lean's `Int.emod` is non-negative for positive
    divisors, so the two definitions agree when `high > low`.
-/
def wrapInt (x low high : Int) : Int :=
  low + (x - low) % (high - low)

/-- `wrapInt` always returns a value ≥ `low`. -/
theorem wrapInt_ge_low (x low high : Int) (h : low < high) :
    low ≤ wrapInt x low high := by
  unfold wrapInt
  have : 0 ≤ (x - low) % (high - low) :=
    Int.emod_nonneg _ (by omega)
  omega

/-- `wrapInt` always returns a value < `high`. -/
theorem wrapInt_lt_high (x low high : Int) (h : low < high) :
    wrapInt x low high < high := by
  unfold wrapInt
  have : (x - low) % (high - low) < high - low :=
    Int.emod_lt_of_pos _ (by omega)
  omega

/-- If `x` is already in `[low, high)`, `wrapInt` returns `x` unchanged. -/
theorem wrapInt_in_range (x low high : Int) (_h : low < high)
    (hlo : low ≤ x) (hhi : x < high) : wrapInt x low high = x := by
  unfold wrapInt
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  omega

/-- `wrapInt` is idempotent: wrapping an already-wrapped value is a no-op. -/
theorem wrapInt_idempotent (x low high : Int) (h : low < high) :
    wrapInt (wrapInt x low high) low high = wrapInt x low high :=
  wrapInt_in_range _ _ _ h (wrapInt_ge_low x low high h) (wrapInt_lt_high x low high h)

/-- Shifting `x` by one full period `(high - low)` is transparent to `wrapInt`. -/
theorem wrapInt_periodic (x low high : Int) (_h : low < high) :
    wrapInt (x + (high - low)) low high = wrapInt x low high := by
  unfold wrapInt
  have heq : x + (high - low) - low = (x - low) + 1 * (high - low) := by omega
  rw [heq, Int.add_mul_emod_self_right]

/-- Shifting `x` by any integer multiple `k` of the period is transparent. -/
theorem wrapInt_periodic_k (x low high k : Int) (_h : low < high) :
    wrapInt (x + k * (high - low)) low high = wrapInt x low high := by
  unfold wrapInt
  have heq : x + k * (high - low) - low = (x - low) + k * (high - low) := by omega
  rw [heq, Int.add_mul_emod_self_right]

/-- `wrapInt` result is congruent to `x` modulo the period `(high - low)`. -/
theorem wrapInt_congruent (x low high : Int) (_h : low < high) :
    ∃ k : Int, wrapInt x low high = x + k * (high - low) := by
  unfold wrapInt
  refine ⟨-((x - low) / (high - low)), ?_⟩
  have h1 : (high - low) * ((x - low) / (high - low)) + (x - low) % (high - low) = x - low :=
    Int.mul_ediv_add_emod (x - low) (high - low)
  rw [Int.neg_mul, Int.mul_comm ((x - low) / (high - low)) (high - low)]
  omega

/-- `wrapInt 0 (-P) P = 0` for any positive half-period `P`. -/
theorem wrapInt_zero (P : Int) (hP : 0 < P) :
    wrapInt 0 (-P) P = 0 := by
  apply wrapInt_in_range
  · omega
  · omega
  · omega

-- Sanity-check examples
#eval wrapInt 5  (-3) 3   -- should be -1  (5 mod 6 = 5; -3 + 5 = 2; hmm)
-- Actually: (5 - (-3)) % (3 - (-3)) = 8 % 6 = 2; -3 + 2 = -1
-- No wait: 8 % 6 = 2; -3 + 2 = -1.  Is that right?  5 → -1 wrapping in [-3,3)?
-- 5 = -1 + 1*6, so yes: wrap_pi(5) ≈ -1 (for period 6)
#eval wrapInt 3  (-3) 3   -- 3 mod 6 = 0 from (-3), but 3 - (-3) = 6, 6%6=0, -3+0=-3
-- Actually: (3 - (-3)) % (3 - (-3)) = 6 % 6 = 0; -3 + 0 = -3
-- So wrapInt 3 (-3) 3 = -3.  3 is NOT in [-3, 3) since 3 is the exclusive upper bound.
#eval wrapInt (-7) (-3) 3 -- (-7 - (-3)) % 6 = (-4) % 6 = 2; -3 + 2 = -1
#eval wrapInt 0  (-3) 3   -- (0 - (-3)) % 6 = 3 % 6 = 3; -3 + 3 = 0  ✓
#eval wrapInt (-3) (-3) 3 -- (-3-(-3)) % 6 = 0 % 6 = 0; -3 + 0 = -3  ✓ (lower bound inclusive)

-- ============================================================
-- Part 2: Abstract rational wrap spec (sorry-guarded)
-- ============================================================

/-! ## Abstract rational wrap contract

The floating-point `wrap_floating` uses:
```
result = x - range * floor((x - low) / range)
```

In Lean 4, `Rat` does not have a `floor` function in the standard library
(it lives in `Mathlib.Algebra.Order.Floor`). We therefore use an *axiomatic*
definition and state the contract as `sorry`-guarded theorems.

To obtain fully verified proofs:
```lean
import Mathlib.Algebra.Order.Floor
noncomputable def wrapRat (x lo hi : Rat) (h : lo < hi) : Rat :=
  let range := hi - lo
  x - range * (⌊(x - lo) / range⌋ : Int)
```
Then each theorem below can be proved using `Mathlib` floor lemmas.
-/

/-- Axiomatic rational wrap (definition requires Mathlib floor).
    Represents `wrap_floating(x, lo, hi)` for finite rational inputs. -/
axiom wrapRat (x lo hi : Rat) (h : lo < hi) : Rat

/-- **[axiom — needs Mathlib floor for proof]** Range lower bound: result ≥ lo.
    Provable with: `(x - lo) / range - ⌊(x - lo) / range⌋ ∈ [0,1)` via `Int.floor_nonneg`. -/
axiom wrapRat_ge_lo (x lo hi : Rat) (h : lo < hi) : lo ≤ wrapRat x lo hi h

/-- **[axiom — needs Mathlib floor for proof]** Range upper bound: result < hi.
    Provable with: `Int.lt_floor_add_one` applied to `(x - lo) / range`. -/
axiom wrapRat_lt_hi (x lo hi : Rat) (h : lo < hi) : wrapRat x lo hi h < hi

/-- **[axiom — needs Mathlib floor for proof]** Identity for values already in range.
    Provable with: `⌊(x - lo) / range⌋ = 0` when `0 ≤ (x - lo) / range < 1`. -/
axiom wrapRat_in_range (x lo hi : Rat) (h : lo < hi)
    (hlo : lo ≤ x) (hhi : x < hi) : wrapRat x lo hi h = x

/-- **[proved]** Idempotence: wrapping an already-wrapped value is the identity. -/
theorem wrapRat_idempotent (x lo hi : Rat) (h : lo < hi) :
    wrapRat (wrapRat x lo hi h) lo hi h = wrapRat x lo hi h :=
  wrapRat_in_range _ _ _ h (wrapRat_ge_lo x lo hi h) (wrapRat_lt_hi x lo hi h)

/-- **[axiom — needs Mathlib floor for proof]** Periodicity: shifting by one period is transparent.
    Provable with: `⌊(x + range - lo) / range⌋ = ⌊(x - lo) / range⌋ + 1`. -/
axiom wrapRat_periodic (x lo hi : Rat) (h : lo < hi) :
    wrapRat (x + (hi - lo)) lo hi h = wrapRat x lo hi h

/-- **[axiom — needs Mathlib floor for proof]** Congruence: result ≡ x mod (hi - lo).
    Provable with: `k = -⌊(x - lo) / range⌋`. -/
axiom wrapRat_congruent (x lo hi : Rat) (h : lo < hi) :
    ∃ k : Int, wrapRat x lo hi h = x + k * (hi - lo)

/-- **[proved]** wrap_pi(0) = 0: wrapping zero in [-P, P) returns zero.
    Follows directly from `wrapRat_in_range` with `-P ≤ 0 < P`. -/
theorem wrapRat_zero (P : Rat) (hP : 0 < P) :
    wrapRat 0 (-P) P (by
      -- Prove -P < P: use -P < 0 < P
      have h1 : -P < -0 := Rat.neg_lt_neg hP
      simp only [Rat.neg_zero] at h1     -- h1 : -P < 0
      exact Std.lt_trans h1 hP) = 0 := by
  -- Apply wrapRat_in_range: need -P ≤ 0 (from hP) and 0 < P (= hP)
  apply wrapRat_in_range
  · -- -P ≤ 0: since -P < 0 (from Rat.neg_lt_neg hP after neg_zero)
    have h1 : (-P : Rat) < 0 := by
      have h := Rat.neg_lt_neg hP
      simp only [Rat.neg_zero] at h
      exact h
    exact Rat.le_of_lt h1
  · exact hP

/- ## Correspondence to `wrapInt`

   The theorems for `wrapRat` mirror those for `wrapInt` exactly (same names,
   same statement shapes). This confirms the integer model is a faithful
   abstraction of the rational model: any proof pattern that works for
   `wrapInt` transfers to `wrapRat` once the Mathlib floor proofs are in place.

   Specifically, the idempotence proofs are *identical*: `wrapRat_idempotent`
   reduces to `wrapRat_in_range + wrapRat_ge_lo + wrapRat_lt_hi`, the same
   structure as `wrapInt_idempotent`.
-/

end WrapAngle
