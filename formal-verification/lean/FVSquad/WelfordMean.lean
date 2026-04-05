/-!
# WelfordMean — Formal Verification

🔬 Lean Squad automated formal verification.

This file models and proves correctness properties of `WelfordMean<T>::update`
from PX4-Autopilot's `mathlib`:

- **C++ source**: `src/lib/mathlib/math/WelfordMean.hpp`
- **Informal spec**: `formal-verification/specs/welfordmean_informal.md`

## C++ reference

```cpp
template<typename Type>
bool WelfordMean<Type>::update(const Type new_value)
{
    if (_count == 0) { reset(); }
    _count++;
    const Type delta_1 = new_value - _mean;
    _mean += delta_1 / _count;
    const Type delta_2 = new_value - _mean;
    _M2 += delta_1 * delta_2;
    return (_count > 2);
}
```

This is Welford's online algorithm for computing the running mean and variance
of a stream of values without storing all samples.

## Model

We model the pure recurrence over `Rat` (rational numbers) with exact arithmetic.

- **Ignores** Kahan compensator fields (`_mean_accum`, `_M2_accum`): these only
  improve numerical precision for floats; they do not affect the mathematical invariants.
- **Ignores** the `UINT16_MAX` count overflow case: we prove the non-overflow behaviour.
- **Ignores** the `PX4_ISFINITE` guard: we assume all inputs are finite (required precondition).
- **Models** the core Welford recurrence exactly over exact rational arithmetic.

## Proved properties

| Theorem | Statement | Status |
|---------|-----------|--------|
| `welfordUpdate_count` | Count increments by 1 on each update | ✅ Proved |
| `welfordUpdate_mean_step` | Mean recurrence: `mean * n = old_mean * (n-1) + x` | ✅ Proved |
| `welfordFoldFrom_count` | Count after folding = initial count + list length | ✅ Proved |
| `welfordFoldFrom_mean_inv` | `mean * count = initial_mean * initial_count + sum(xs)` | ✅ Proved |
| `welfordFold_count` | `(welfordFold xs).count = xs.length` | ✅ Proved |
| `welfordFold_mean_times_count` | `(welfordFold xs).mean * length = sum(xs)` | ✅ Proved |
| `welfordFold_mean` | For non-empty lists: `mean = sum(xs) / length(xs)` | ✅ Proved |
| `welfordUpdate_M2_nonneg` | `M2 ≥ 0` is preserved by each update | 🔄 Sorry — see below |

**`welfordUpdate_M2_nonneg` is left with `sorry`**: the proof requires showing
`(x - s.mean) * (x - new_mean) ≥ 0` which is equivalent to
`delta_old² * (n-1)/n ≥ 0` for `n ≥ 1`. This reduces to showing `(↑(n-1) : Rat) / n ≥ 0`
which requires `Rat.inv_nonneg` — but `Rat.inv` is `@[irreducible]` in the Lean 4 stdlib,
blocking this proof without Mathlib. The mathematical argument is clear; the sorry is
a tooling limitation only.
-/

namespace PX4.WelfordMean

/-! ## State and definitions -/

/-- State of the Welford accumulator after zero or more updates.

Models the three fields of `WelfordMean<T>` that carry the running statistics:
`_count`, `_mean`, and `_M2`. Kahan compensator fields are omitted (numerical
stability detail irrelevant to the abstract correctness proof). -/
structure WelfordState where
  count : Nat
  mean  : Rat
  M2    : Rat
  deriving Repr

/-- Initial state: all fields zero (matches the C++ default constructor). -/
def initState : WelfordState := { count := 0, mean := 0, M2 := 0 }

/-- Single-step Welford update.

    Models one call to `WelfordMean::update(new_value)` for a non-zero count.

    C++ recurrence (simplified, count already incremented):
    ```
    delta_1 = new_value - _mean_old
    _mean  += delta_1 / _count           -- _count after increment
    _M2    += delta_1 * (new_value - _mean_new)
    ```

    **Note**: We use `↑(s.count + 1) : Rat` for the denominator to keep the
    Nat-to-Rat cast explicit; this is important for the proof of `welfordUpdate_mean_step`. -/
def welfordUpdate (s : WelfordState) (x : Rat) : WelfordState :=
  let nR  : Rat := ↑(s.count + 1)
  let δ         := x - s.mean
  let newMean   := s.mean + δ / nR
  { count := s.count + 1,
    mean  := newMean,
    M2    := s.M2 + δ * (x - newMean) }

/-- Fold a list of samples through the Welford update, starting from a given state. -/
def welfordFoldFrom (s₀ : WelfordState) : List Rat → WelfordState
  | []      => s₀
  | x :: xs => welfordFoldFrom (welfordUpdate s₀ x) xs

/-- Fold a list of samples through Welford update, starting from the initial state. -/
def welfordFold (xs : List Rat) : WelfordState := welfordFoldFrom initState xs

-- Sanity checks: verify the model computes correct values.
#eval welfordFold [1, 2, 3]
-- Expected: { count := 3, mean := 2, M2 := 2 }
-- sample variance = M2 / (count - 1) = 2/2 = 1 ✓

#eval (welfordFold [1, 2, 3]).mean  -- 2
#eval (welfordFold [4, 8, 15, 16, 23, 42]).mean -- should be 18

/-! ## Auxiliary: non-zero cast -/

/-- `(n+1 : Rat) ≠ 0` for any natural number `n`.  This follows directly from
    Lean 4's `CharZero` instance for `Rat` and `Nat.succ_ne_zero`. -/
private theorem succ_cast_ne_zero (n : Nat) : (↑(n + 1) : Rat) ≠ 0 :=
  by exact_mod_cast Nat.succ_ne_zero n

/-! ## Theorem 1: Count tracking -/

/-- Each call to `welfordUpdate` increments the count by exactly 1. -/
theorem welfordUpdate_count (s : WelfordState) (x : Rat) :
    (welfordUpdate s x).count = s.count + 1 := by
  simp [welfordUpdate]

/-! ## Theorem 2: Mean recurrence (key algebraic step) -/

/-- **Core invariant step**: after one update, `new_mean × new_count = old_mean × old_count + x`.

    This is the heart of the mean-correctness proof.  Algebraic sketch:
    ```
    new_mean × (count+1)
      = (mean + (x-mean)/(count+1)) × (count+1)     -- [def of new_mean]
      = mean×(count+1) + (x-mean)                   -- [add_mul, div_mul_cancel]
      = mean×count + mean + x - mean                 -- [mul_add, mul_one]
      = mean×count + x                               -- ✓
    ```
-/
theorem welfordUpdate_mean_step (s : WelfordState) (x : Rat) :
    (welfordUpdate s x).mean * ↑(welfordUpdate s x).count = s.mean * ↑s.count + x := by
  simp only [welfordUpdate]
  have hn : (↑(s.count + 1) : Rat) ≠ 0 := succ_cast_ne_zero s.count
  -- Step 1: (mean + δ/n) × n  = mean × n + δ   where δ = x - mean
  have step1 : (s.mean + (x - s.mean) / ↑(s.count + 1)) * ↑(s.count + 1) =
               s.mean * ↑(s.count + 1) + (x - s.mean) := by
    rw [Rat.add_mul]
    congr 1
    rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ hn, Rat.mul_one]
  rw [step1]
  -- Step 2: mean × (count+1) = mean × count + mean
  have h_cast : (↑(s.count + 1) : Rat) = ↑s.count + 1 := by push_cast; rfl
  rw [h_cast, Rat.mul_add, Rat.mul_one, Rat.add_assoc]
  -- Step 3: mean + (x - mean) = x
  congr 1
  rw [Rat.add_comm s.mean _, Rat.sub_add_cancel]

/-! ## Theorem 3: Count after folding -/

/-- After processing `xs` elements starting from state `s₀`,
    the count is `s₀.count + xs.length`. -/
theorem welfordFoldFrom_count (s₀ : WelfordState) (xs : List Rat) :
    (welfordFoldFrom s₀ xs).count = s₀.count + xs.length := by
  induction xs generalizing s₀ with
  | nil => simp [welfordFoldFrom]
  | cons x xs ih =>
    simp only [welfordFoldFrom, List.length_cons]
    rw [ih (welfordUpdate s₀ x), welfordUpdate_count]
    omega

/-! ## Theorem 4: Mean invariant (inductive) -/

/-- **General mean invariant**: after processing `xs` starting from `s₀`,
    `new_mean × new_count = s₀.mean × s₀.count + sum(xs)`.

    Proof: by induction on `xs`, using `welfordUpdate_mean_step` at each step.
    The inductive step reduces to showing associativity of addition. -/
theorem welfordFoldFrom_mean_inv (s₀ : WelfordState) (xs : List Rat) :
    (welfordFoldFrom s₀ xs).mean * ↑(welfordFoldFrom s₀ xs).count =
    s₀.mean * ↑s₀.count + xs.sum := by
  induction xs generalizing s₀ with
  | nil => simp [welfordFoldFrom, List.sum_nil, Rat.add_zero]
  | cons x xs ih =>
    simp only [welfordFoldFrom, List.sum_cons]
    rw [ih (welfordUpdate s₀ x), welfordUpdate_mean_step]
    -- Goal: (old_mean * old_count + x) + xs.sum = old_mean * old_count + (x + xs.sum)
    exact Rat.add_assoc _ _ _

/-! ## Main fold theorems -/

/-- The count after `welfordFold xs` equals the length of `xs`. -/
theorem welfordFold_count (xs : List Rat) :
    (welfordFold xs).count = xs.length := by
  unfold welfordFold
  rw [welfordFoldFrom_count]
  simp [initState]

/-- **Main mean correctness theorem**: `mean × count = sum(xs)`.

    The mean computed by Welford's algorithm equals the arithmetic mean of
    all inputs: dividing both sides by `count` (= `length`) gives `mean = sum/length`.
    We state the multiplication form to avoid division and the nonzero precondition. -/
theorem welfordFold_mean_times_count (xs : List Rat) :
    (welfordFold xs).mean * ↑(welfordFold xs).count = xs.sum := by
  unfold welfordFold
  rw [welfordFoldFrom_mean_inv]
  simp [initState, Rat.zero_add]

/-- **Corollary**: for a non-empty list, `mean = sum / length`. -/
theorem welfordFold_mean (xs : List Rat) (hne : xs ≠ []) :
    (welfordFold xs).mean = xs.sum / xs.length := by
  have hlen : xs.length ≠ 0 := by
    cases xs with
    | nil  => exact absurd rfl hne
    | cons => exact Nat.succ_ne_zero _
  have hlenR : (↑xs.length : Rat) ≠ 0 := by exact_mod_cast hlen
  have h := welfordFold_mean_times_count xs
  rw [welfordFold_count] at h
  -- h : mean * ↑length = sum
  -- Want: mean = sum / length, i.e., mean = sum * length⁻¹
  rw [← h, Rat.div_def, Rat.mul_assoc, Rat.mul_inv_cancel _ hlenR, Rat.mul_one]

/-! ## M2 non-negativity -/

/-- `M2 ≥ 0` is preserved by each update.

    **Mathematical argument**: the increment is `δ₁ × δ₂` where:
    - `δ₁ = x - mean_old`
    - `δ₂ = x - mean_new = δ₁ × (count / (count+1))`
    so `δ₁ × δ₂ = δ₁² × count / (count+1) ≥ 0`.

    **Why `sorry`**: proving `δ₁ * δ₂ ≥ 0` requires showing `(↑count : Rat) / (count+1) ≥ 0`.
    This reduces to `Rat.inv_nonneg` (for non-negative denominator), but `Rat.inv` is
    `@[irreducible]` in Lean 4 stdlib, which blocks the proof without Mathlib.
    The mathematical argument is correct; this is a tooling limitation only.
    Fix: add `import Mathlib.Algebra.Order.Field.Basic` for `div_nonneg`. -/
theorem welfordUpdate_M2_nonneg (s : WelfordState) (x : Rat) (h : 0 ≤ s.M2) :
    0 ≤ (welfordUpdate s x).M2 := by
  simp only [welfordUpdate]
  -- δ₁ * δ₂ = (x - s.mean) * (x - (s.mean + (x - s.mean) / ↑(s.count + 1)))
  -- = (x - s.mean)² * ↑s.count / ↑(s.count + 1) ≥ 0
  sorry

end PX4.WelfordMean
