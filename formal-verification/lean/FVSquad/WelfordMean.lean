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

**`welfordUpdate_M2_nonneg` is now fully proved** via algebraic factoring: the increment
`δ * (x - mean_new) = δ² * (1 - nR⁻¹)` where `nR = count + 1`. This is ≥ 0 because
`δ² ≥ 0` always, and `1 - nR⁻¹ ≥ 0` since `nR ≥ 1` implies `nR⁻¹ ≤ 1`.
The key insight: `Rat.inv_pos` is available in Lean 4 stdlib (unlike `Rat.inv_nonneg`),
which allows proving `nR⁻¹ ≤ 1` by multiplying both sides by `nR > 0`.
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

/-- Helper: `δ * δ ≥ 0` for any rational `δ`.
    Proved by case split: if `δ ≥ 0` use `mul_nonneg`; if `δ < 0` use `(-δ)*(-δ) = δ*δ`. -/
private theorem rat_sq_nonneg (δ : Rat) : 0 ≤ δ * δ := by
  by_cases h : 0 ≤ δ
  · exact Rat.mul_nonneg h h
  · have hlt : δ < 0 := Rat.not_le.mp h
    have hneg0 : (0 : Rat) ≤ -δ := by
      have := Rat.neg_le_neg (Rat.le_of_lt hlt)
      simp [Rat.neg_zero] at this; exact this
    rw [← show (-δ) * (-δ) = δ * δ from by rw [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]]
    exact Rat.mul_nonneg hneg0 hneg0

/-- Helper: `nR⁻¹ ≤ 1` when `1 ≤ nR` and `0 < nR`.
    Proved via: `1 * nR⁻¹ ≤ nR * nR⁻¹ = 1`. -/
private theorem inv_le_one_of_one_le (nR : Rat) (h1 : 1 ≤ nR) (hpos : 0 < nR) : nR⁻¹ ≤ 1 := by
  have hne : nR ≠ 0 := fun h0 => by simp [h0] at hpos
  have h2 : (1 : Rat) * nR⁻¹ ≤ nR * nR⁻¹ :=
    Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt (Rat.inv_pos.mpr hpos))
  rw [Rat.mul_inv_cancel _ hne, Rat.one_mul] at h2; exact h2

/-- `M2 ≥ 0` is preserved by each update.

    **Proof**: The increment is `δ * (x - mean_new)` where `δ = x - mean_old`.
    We show `x - mean_new = δ * (1 - nR⁻¹)` (simple algebra), so the increment
    equals `δ² * (1 - nR⁻¹) ≥ 0` since:
    - `δ² ≥ 0` (square is non-negative)
    - `1 - nR⁻¹ ≥ 0` because `nR = count + 1 ≥ 1` implies `nR⁻¹ ≤ 1` -/
theorem welfordUpdate_M2_nonneg (s : WelfordState) (x : Rat) (h : 0 ≤ s.M2) :
    0 ≤ (welfordUpdate s x).M2 := by
  simp only [welfordUpdate]
  apply Rat.add_nonneg h
  -- Goal: 0 ≤ (x - s.mean) * (x - (s.mean + (x - s.mean) / ↑(s.count + 1)))
  have hne  : (↑(s.count + 1) : Rat) ≠ 0 := succ_cast_ne_zero s.count
  have hpos : (0 : Rat) < ↑(s.count + 1)  := by exact_mod_cast Nat.succ_pos s.count
  have h1nR : (1 : Rat) ≤ ↑(s.count + 1)  := by exact_mod_cast Nat.le_add_left 1 s.count
  -- Simplify: x - (mean + δ/nR) = δ - δ/nR
  have hx_sub : x - (s.mean + (x - s.mean) / ↑(s.count + 1)) =
                (x - s.mean) - (x - s.mean) / ↑(s.count + 1) := by
    simp [Rat.sub_eq_add_neg, Rat.neg_add, Rat.add_assoc]
  rw [hx_sub]
  -- Factor: δ - δ/nR = δ * (1 - nR⁻¹)
  have hfactor : (x - s.mean) - (x - s.mean) / ↑(s.count + 1) =
                 (x - s.mean) * (1 - (↑(s.count + 1))⁻¹) := by
    rw [Rat.div_def]
    simp [Rat.sub_eq_add_neg, Rat.mul_add, Rat.mul_neg, Rat.mul_one]
  rw [hfactor, ← Rat.mul_assoc]
  apply Rat.mul_nonneg (rat_sq_nonneg _)
  -- 0 ≤ 1 - nR⁻¹ since nR⁻¹ ≤ 1
  exact (Rat.le_iff_sub_nonneg (↑(s.count + 1))⁻¹ 1).mp
        (inv_le_one_of_one_le _ h1nR hpos)

end PX4.WelfordMean
