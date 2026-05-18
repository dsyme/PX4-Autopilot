import Init.Data.Rat.Basic

/-!
# PX4 `BlockLimit` — Formal Verification

🔬 *Lean Squad automated formal verification.*

This file models and proves correctness properties of PX4's asymmetric
clamp/saturation block `BlockLimit`:

- **C++ source**: `src/lib/controllib/BlockLimit.cpp` (lines 47–59) and
  `src/lib/controllib/BlockLimit.hpp`

## C++ Source

```cpp
float BlockLimit::update(float input)
{
    if (input > getMax()) {
        input = _max.get();
    } else if (input < getMin()) {
        input = getMin();
    }
    return input;
}
```

## Model

Over `Rat` (exact rational arithmetic), the pure functional model of `update` is:

```
limit(input, lo, hi) =
  if input > hi  then  hi
  if input < lo  then  lo
  otherwise            input
```

**Abstracted away**: The `_min`/`_max` parameter objects, the `Block` hierarchy,
and floating-point rounding. The Lean model captures the pure numeric behaviour.
Most theorems require `lo ≤ hi` (a valid clamp range), which always holds in practice.

## Properties Proved (10 theorems, 0 sorry)

1. `limit_above`       — input above hi → output = hi
2. `limit_below`       — input below lo → output = lo (requires lo ≤ hi)
3. `limit_in_range`    — input in [lo, hi] → output = input (pass-through)
4. `limit_upper`       — output ≤ hi (requires lo ≤ hi)
5. `limit_lower`       — lo ≤ output (requires lo ≤ hi)
6. `limit_range`       — lo ≤ output ≤ hi (combined, requires lo ≤ hi)
7. `limit_idempotent`  — applying twice = applying once (requires lo ≤ hi)
8. `limit_lo_fixed`    — limit lo lo hi = lo when lo ≤ hi
9. `limit_hi_fixed`    — limit hi lo hi = hi when lo ≤ hi
10. `limit_mono`       — monotone in input (requires lo ≤ hi)
-/

namespace PX4.BlockLimit

def limit (input lo hi : Rat) : Rat :=
  if input > hi then hi
  else if input < lo then lo
  else input

theorem limit_above (input lo hi : Rat) (h : input > hi) :
    limit input lo hi = hi := by
  unfold limit; rw [if_pos h]

theorem limit_below (input lo hi : Rat) (hlohi : lo ≤ hi) (h : input < lo) :
    limit input lo hi = lo := by
  unfold limit
  rw [if_neg (Rat.not_lt.mpr (Rat.le_trans (Rat.le_of_lt h) hlohi)), if_pos h]

theorem limit_in_range (input lo hi : Rat) (h1 : lo ≤ input) (h2 : input ≤ hi) :
    limit input lo hi = input := by
  unfold limit
  rw [if_neg (Rat.not_lt.mpr h2), if_neg (Rat.not_lt.mpr h1)]

theorem limit_upper (input lo hi : Rat) (hlohi : lo ≤ hi) : limit input lo hi ≤ hi := by
  unfold limit
  by_cases h1 : input > hi
  · rw [if_pos h1]; exact Rat.le_refl
  · by_cases h2 : input < lo
    · rw [if_neg h1, if_pos h2]; exact hlohi
    · rw [if_neg h1, if_neg h2]; exact Rat.not_lt.mp h1

theorem limit_lower (input lo hi : Rat) (hlohi : lo ≤ hi) : lo ≤ limit input lo hi := by
  unfold limit
  by_cases h1 : input > hi
  · rw [if_pos h1]; exact hlohi
  · by_cases h2 : input < lo
    · rw [if_neg h1, if_pos h2]; exact Rat.le_refl
    · rw [if_neg h1, if_neg h2]; exact Rat.not_lt.mp h2

theorem limit_range (input lo hi : Rat) (hlohi : lo ≤ hi) :
    lo ≤ limit input lo hi ∧ limit input lo hi ≤ hi :=
  ⟨limit_lower input lo hi hlohi, limit_upper input lo hi hlohi⟩

theorem limit_idempotent (input lo hi : Rat) (hlohi : lo ≤ hi) :
    limit (limit input lo hi) lo hi = limit input lo hi :=
  limit_in_range _ _ _ (limit_lower input lo hi hlohi) (limit_upper input lo hi hlohi)

theorem limit_lo_fixed (lo hi : Rat) (hlohi : lo ≤ hi) :
    limit lo lo hi = lo :=
  limit_in_range lo lo hi Rat.le_refl hlohi

theorem limit_hi_fixed (lo hi : Rat) (hlohi : lo ≤ hi) :
    limit hi lo hi = hi :=
  limit_in_range hi lo hi hlohi Rat.le_refl

/-- `limit` is monotone in its input.

    Saturation is a non-decreasing operation: larger inputs produce outputs
    that are at least as large. -/
theorem limit_mono (a b lo hi : Rat) (hlohi : lo ≤ hi) (h : a ≤ b) :
    limit a lo hi ≤ limit b lo hi := by
  unfold limit
  by_cases ha1 : a > hi
  · rw [if_pos ha1]
    by_cases hb1 : b > hi
    · rw [if_pos hb1]; exact Rat.le_refl
    · exact absurd (Std.lt_of_lt_of_le ha1 h) hb1
  · by_cases ha2 : a < lo
    · rw [if_neg ha1, if_pos ha2]
      by_cases hb1 : b > hi
      · rw [if_pos hb1]; exact hlohi
      · by_cases hb2 : b < lo
        · rw [if_neg hb1, if_pos hb2]; exact Rat.le_refl
        · rw [if_neg hb1, if_neg hb2]; exact Rat.not_lt.mp hb2
    · rw [if_neg ha1, if_neg ha2]
      by_cases hb1 : b > hi
      · rw [if_pos hb1]; exact Rat.not_lt.mp ha1
      · by_cases hb2 : b < lo
        · exact absurd (Std.lt_of_lt_of_le hb2 (Rat.not_lt.mp ha2)) (Rat.not_lt.mpr h)
        · rw [if_neg hb1, if_neg hb2]; exact h

end PX4.BlockLimit
