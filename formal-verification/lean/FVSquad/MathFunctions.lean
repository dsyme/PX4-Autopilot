/-!
# PX4 Math Functions — Formal Verification

🔬 Lean Squad automated formal verification.

This file models and proves correctness properties of key pure mathematical
functions from PX4-Autopilot's `mathlib`:

- `math::constrain`    (src/lib/mathlib/math/Limits.hpp)
- `math::signNoZero`   (src/lib/mathlib/math/Functions.hpp)
- `math::countSetBits` / Hamming weight (src/lib/mathlib/math/Functions.hpp)

We use integer/natural number models. Floating-point behaviour (NaN, infinity)
is explicitly out of scope — documented in the CORRESPONDENCE.md section.

No Mathlib dependency — only the Lean 4 standard library.
-/

namespace PX4.Math

/-! ## Section 1: `constrain` — clamping a value to [lo, hi]

C++ source: `src/lib/mathlib/math/Limits.hpp`
```cpp
template<typename _Tp>
constexpr _Tp constrain(_Tp val, _Tp min_val, _Tp max_val)
{
    return (val < min_val) ? min_val : ((val > max_val) ? max_val : val);
}
```
Approximation: we use `Int` instead of `float`.
NaN and infinity are not modelled.
-/

def constrain (val lo hi : Int) : Int :=
  if val < lo then lo
  else if val > hi then hi
  else val

/-- `constrain` always returns a value ≥ lo, given lo ≤ hi. -/
theorem constrain_ge_lo (val lo hi : Int) (h : lo ≤ hi) :
    lo ≤ constrain val lo hi := by
  simp only [constrain]
  split
  · exact Int.le_refl lo
  · split
    · exact h
    · omega

/-- `constrain` always returns a value ≤ hi, given lo ≤ hi. -/
theorem constrain_le_hi (val lo hi : Int) (h : lo ≤ hi) :
    constrain val lo hi ≤ hi := by
  simp only [constrain]
  split
  · exact h
  · split
    · exact Int.le_refl hi
    · omega

/-- `constrain` output is always within [lo, hi], given lo ≤ hi. -/
theorem constrain_in_range (val lo hi : Int) (h : lo ≤ hi) :
    lo ≤ constrain val lo hi ∧ constrain val lo hi ≤ hi :=
  ⟨constrain_ge_lo val lo hi h, constrain_le_hi val lo hi h⟩

/-- If val is already in [lo, hi], `constrain` is the identity. -/
theorem constrain_of_mem (val lo hi : Int) (hlo : lo ≤ val) (hhi : val ≤ hi) :
    constrain val lo hi = val := by
  simp only [constrain]
  split <;> omega

/-- `constrain` clamps to lo when val < lo. -/
theorem constrain_of_lt_lo (val lo hi : Int) (h : val < lo) :
    constrain val lo hi = lo := by
  simp only [constrain]
  split <;> omega

/-- `constrain` clamps to hi when val > hi (and val ≥ lo). -/
theorem constrain_of_gt_hi (val lo hi : Int) (hlo : ¬ val < lo) (hhi : val > hi) :
    constrain val lo hi = hi := by
  simp only [constrain]
  split <;> omega

/-- Idempotence: applying `constrain` twice equals applying it once. -/
theorem constrain_idempotent (val lo hi : Int) (h : lo ≤ hi) :
    constrain (constrain val lo hi) lo hi = constrain val lo hi := by
  apply constrain_of_mem
  · exact constrain_ge_lo val lo hi h
  · exact constrain_le_hi val lo hi h

/-- Monotonicity: `constrain` preserves ≤ ordering (requires valid bounds). -/
theorem constrain_mono (val1 val2 lo hi : Int) (hbounds : lo ≤ hi) (h : val1 ≤ val2) :
    constrain val1 lo hi ≤ constrain val2 lo hi := by
  simp only [constrain]
  by_cases h1 : val1 < lo <;> by_cases h2 : val2 < lo <;>
  by_cases h3 : val1 > hi <;> by_cases h4 : val2 > hi <;>
  simp [h1, h2, h3, h4] <;> omega

-- Concrete spot-checks
example : constrain 5 0 10 = 5 := by native_decide
example : constrain (-3) 0 10 = 0 := by native_decide
example : constrain 15 0 10 = 10 := by native_decide
example : constrain 0 0 0 = 0 := by native_decide
example : constrain 100 50 50 = 50 := by native_decide

/-! ## Section 2: `signNoZero` — sign with no zero return

C++ source: `src/lib/mathlib/math/Functions.hpp`
```cpp
template<typename T>
int signNoZero(T val) {
    return (T(0) <= val) - (val < T(0));
}
```
Returns +1 for non-negative, -1 for negative. Never returns 0.
-/

def signNoZero (val : Int) : Int :=
  if 0 ≤ val then 1 else -1

/-- `signNoZero` returns 1 for non-negative inputs. -/
theorem signNoZero_nonneg (val : Int) (h : 0 ≤ val) :
    signNoZero val = 1 := by
  simp [signNoZero, h]

/-- `signNoZero` returns -1 for negative inputs. -/
theorem signNoZero_neg (val : Int) (h : val < 0) :
    signNoZero val = -1 := by
  unfold signNoZero
  by_cases hnn : 0 ≤ val <;> simp [hnn] <;> omega

/-- `signNoZero` never returns 0. -/
theorem signNoZero_ne_zero (val : Int) :
    signNoZero val ≠ 0 := by
  unfold signNoZero
  by_cases h : 0 ≤ val <;> simp [h]

/-- `signNoZero` output is in {-1, 1}. -/
theorem signNoZero_values (val : Int) :
    signNoZero val = 1 ∨ signNoZero val = -1 := by
  unfold signNoZero
  by_cases h : 0 ≤ val <;> simp [h]

/-- `signNoZero(0) = 1` (zero is treated as non-negative). -/
theorem signNoZero_zero : signNoZero 0 = 1 := by decide

/-- `signNoZero` squared always equals 1. -/
theorem signNoZero_sq (val : Int) :
    signNoZero val * signNoZero val = 1 := by
  unfold signNoZero
  by_cases h : 0 ≤ val <;> simp [h]

-- Concrete spot-checks
example : signNoZero (5 : Int) = 1 := by native_decide
example : signNoZero (-3 : Int) = -1 := by native_decide
example : signNoZero (0 : Int) = 1 := by native_decide

/-! ## Section 3: `countSetBits` — Hamming weight

C++ source: `src/lib/mathlib/math/Functions.hpp`
```cpp
template<typename T>
int countSetBits(T n) {
    int count = 0;
    while (n) { count += n & 1; n >>= 1; }
    return count;
}
```
We define a structurally-recursive version on `Nat` for ease of reasoning.
The C++ loop is semantically equivalent on non-negative inputs.
-/

def countSetBits : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) % 2 + countSetBits ((n + 1) / 2)

/-- Helper: unfold countSetBits for positive inputs. -/
theorem countSetBits_unfold (n : Nat) (h : 0 < n) :
    countSetBits n = n % 2 + countSetBits (n / 2) := by
  cases n with
  | zero => omega
  | succ m => simp [countSetBits]

/-- Concrete spot-checks via native_decide. -/
example : countSetBits 0 = 0 := by native_decide
example : countSetBits 1 = 1 := by native_decide
example : countSetBits 2 = 1 := by native_decide
example : countSetBits 3 = 2 := by native_decide
example : countSetBits 4 = 1 := by native_decide
example : countSetBits 7 = 3 := by native_decide
example : countSetBits 8 = 1 := by native_decide
example : countSetBits 255 = 8 := by native_decide
example : countSetBits 0xFF00 = 8 := by native_decide

/-- `countSetBits` of a power of 2 is always 1. -/
theorem countSetBits_pow2 (k : Nat) : countSetBits (2 ^ k) = 1 := by
  induction k with
  | zero => native_decide
  | succ n ih =>
    have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
    rw [countSetBits_unfold _ (Nat.two_pow_pos _)]
    rw [Nat.pow_succ]
    have hmod : 2 ^ n * 2 % 2 = 0 := by omega
    have hdiv : 2 ^ n * 2 / 2 = 2 ^ n := by omega
    rw [hmod, hdiv, ih]

/-- `countSetBits 0 = 0`: zero has no bits set. -/
theorem countSetBits_zero : countSetBits 0 = 0 := by native_decide

/-- `countSetBits 1 = 1`: exactly one bit set in 1. -/
theorem countSetBits_one : countSetBits 1 = 1 := by native_decide

/-- Doubling a positive integer does not change its bit count.
    Shifting left by one adds a zero LSB. -/
theorem countSetBits_double (n : Nat) (hn : 0 < n) :
    countSetBits (2 * n) = countSetBits n := by
  rw [countSetBits_unfold (2 * n) (by omega)]
  have hmod : 2 * n % 2 = 0 := by omega
  have hdiv : 2 * n / 2 = n := by omega
  simp [hmod, hdiv]

/-- An odd number has one more bit set than its half.
    The LSB 1 contributes exactly 1 to the count. -/
theorem countSetBits_succ_odd (n : Nat) :
    countSetBits (2 * n + 1) = 1 + countSetBits n := by
  rw [countSetBits_unfold (2 * n + 1) (by omega)]
  have hmod : (2 * n + 1) % 2 = 1 := by omega
  have hdiv : (2 * n + 1) / 2 = n := by omega
  rw [hmod, hdiv]

/-- Any positive natural number has at least one bit set.
    Safety property: `countSetBits n > 0` iff `n > 0`. -/
theorem countSetBits_pos (n : Nat) (h : 0 < n) : 0 < countSetBits n := by
  rw [countSetBits_unfold n h]
  by_cases hmod : n % 2 = 0
  · simp only [hmod, Nat.zero_add]
    exact countSetBits_pos (n / 2) (by omega)
  · omega
termination_by n

/-- Zero bit count iff zero: `countSetBits n = 0 ↔ n = 0`. -/
theorem countSetBits_eq_zero_iff_zero (n : Nat) : countSetBits n = 0 ↔ n = 0 := by
  constructor
  · intro h
    by_cases hn : n = 0
    · exact hn
    · exfalso
      have hpos : 0 < n := Nat.pos_of_ne_zero hn
      have hcpos : 0 < countSetBits n := countSetBits_pos n hpos
      omega
  · intro h; subst h; exact countSetBits_zero

/-- The `signNoZero` product with the input is always non-negative.
    `signNoZero(x) * x = |x|`: multiplying by the sign yields magnitude. -/
theorem signNoZero_mul_self_nonneg (val : Int) : signNoZero val * val ≥ 0 := by
  simp only [signNoZero]
  by_cases h : 0 ≤ val
  · rw [if_pos h]; omega
  · rw [if_neg h]; omega

/-- `signNoZero` negates when the input is strictly positive:
    `signNoZero(-x) = -1` when `x > 0`. -/
theorem signNoZero_neg_of_pos (val : Int) (h : 0 < val) : signNoZero (-val) = -1 := by
  simp only [signNoZero]
  have hneg : ¬ (0 : Int) ≤ -val := by omega
  rw [if_neg hneg]

/-- `signNoZero` is 1 when the input is strictly positive.
    Companion to `signNoZero_nonneg` with strict hypothesis. -/
theorem signNoZero_pos (val : Int) (h : 0 < val) : signNoZero val = 1 :=
  signNoZero_nonneg val (Int.le_of_lt h)

/-- `signNoZero 1 = 1`: concrete instance. -/
theorem signNoZero_one : signNoZero 1 = 1 := by decide

/-- `signNoZero (-1) = -1`: concrete instance. -/
theorem signNoZero_neg_one : signNoZero (-1) = -1 := by decide

end PX4.Math
