/-!
# ObstacleMath::wrap_bin — Formal Verification

🔬 *Lean Squad automated formal verification.*

- **C++ source**: `src/lib/collision_prevention/ObstacleMath.cpp` (line ~140)
- **Informal spec**: `formal-verification/specs/wrap_bin_informal.md`

## C++ reference

```cpp
// ObstacleMath.cpp
int wrap_bin(int bin, int bin_count)
{
    return (bin + bin_count) % bin_count;
}
```

## Model

We provide two models:

1. **`wrapBin`** — uses Lean 4's Euclidean `%` on `Int` (non-negative for positive
   divisor). This captures the *intended* semantics: result always in `[0, bin_count)`.
   All correctness theorems use this model.

2. **`wrapBinCpp`** — uses `Int.tmod` (C++ truncation-toward-zero semantics).
   For `bin ≤ -bin_count - 1`, `bin + bin_count < 0`, so `Int.tmod` returns a
   negative value — the latent bug in the C++ implementation.

**Key insight**: Lean's `%` on `Int` is Euclidean (always `≥ 0` for positive divisor),
so `wrapBin` is provably correct for *all* integer inputs. The C++ implementation has a
latent bug because `%` in C++ uses truncation semantics.

## Bug Finding

`wrapBinCpp_bug_general` proves that for any `bin_count > 1`,
`wrapBinCpp (-bin_count - 1) bin_count = -1`, confirming the documented latent bug.

`wrapBinOffset_valid` proves that all current callers (`get_offset_bin_index`, passing
`bin - offset` with `0 ≤ bin, offset < bin_count`) are **safe** in practice —
the inputs never reach the buggy region.

## Approximations / Out of Scope

- **Float-based callers** (`get_bin_at_angle`, `get_lower_bound_angle`): involve
  `float` arithmetic and `roundf`, which are not modelled here.
- **`wrap_360`**: uses a floating-point wrap; not modelled.
- The model covers only `wrap_bin` itself.
-/

namespace PX4.ObstacleMath

/-! ## Implementation models -/

/-- **Lean model** of `wrap_bin`: uses Euclidean `%` (always `≥ 0` for positive divisor).
    This captures the intended semantics. All correctness theorems use this model. -/
def wrapBin (bin bin_count : Int) : Int :=
  (bin + bin_count) % bin_count

/-- **C++ model** of `wrap_bin`: uses `Int.tmod` (truncation-toward-zero, matching C++).
    For negative sums `bin + bin_count < 0`, this returns a negative result — the bug. -/
def wrapBinCpp (bin bin_count : Int) : Int :=
  Int.tmod (bin + bin_count) bin_count

/-! ## Sanity checks (eval) -/

-- All test cases from ObstacleMathTest.cpp
#eval wrapBin 0   72    -- 0   (in range: identity)
#eval wrapBin 71  72    -- 71  (in range: identity)
#eval wrapBin 72  72    -- 0   (at count: wrap to 0)
#eval wrapBin 73  72    -- 1   (one above: wrap to 1)
#eval wrapBin (-1) 72   -- 71  (one below: wrap to last)
#eval wrapBin (-72) 72  -- 0   (exactly -n: still ok)
#eval wrapBin (-73) 72  -- 71  (Lean: correct; C++ would give -1)

-- C++ model shows the bug
#eval wrapBinCpp (-1)  72  -- 71  (same sign as argument: correct here)
#eval wrapBinCpp (-73) 72  -- -1  ← BUG: C++ truncation gives negative result!

/-! ## Concrete examples (native_decide) -/

/-- Test case 1: bin 0 is identity. -/
theorem wrapBin_example_zero : wrapBin 0 72 = 0 := by native_decide

/-- Test case 2: bin 71 is identity. -/
theorem wrapBin_example_71 : wrapBin 71 72 = 71 := by native_decide

/-- Test case 3: bin 72 wraps to 0. -/
theorem wrapBin_example_72 : wrapBin 72 72 = 0 := by native_decide

/-- Test case 4: bin 73 wraps to 1. -/
theorem wrapBin_example_73 : wrapBin 73 72 = 1 := by native_decide

/-- Test case 5: bin -1 wraps to 71 (correct Euclidean semantics). -/
theorem wrapBin_example_neg1 : wrapBin (-1) 72 = 71 := by native_decide

/-- Test case 6: bin -72 wraps to 0 (correct). -/
theorem wrapBin_example_neg72 : wrapBin (-72) 72 = 0 := by native_decide

/-- Test case 7: bin -73 wraps to 71 (Lean Euclidean: correct).
    The C++ version would give -1 (the latent bug). -/
theorem wrapBin_example_neg73 : wrapBin (-73) 72 = 71 := by native_decide

/-- Bug demo: C++ model gives -1 for bin = -73. -/
theorem wrapBinCpp_bug_example : wrapBinCpp (-73) 72 = -1 := by native_decide

/-! ## Universal range theorem -/

/-- **Range**: `wrapBin` always returns a value in `[0, bin_count)` for any `bin`
    and any positive `bin_count`. This holds for ALL integer inputs — no preconditions
    on `bin` are needed. This is the key advantage of Lean's Euclidean `%`. -/
theorem wrapBin_range (bin bin_count : Int) (hpos : 0 < bin_count) :
    0 ≤ wrapBin bin bin_count ∧ wrapBin bin bin_count < bin_count :=
  ⟨Int.emod_nonneg _ (Int.ne_of_gt hpos), Int.emod_lt_of_pos _ hpos⟩

/-- **Range lower bound** (standalone). -/
theorem wrapBin_nonneg (bin bin_count : Int) (hpos : 0 < bin_count) :
    0 ≤ wrapBin bin bin_count :=
  Int.emod_nonneg _ (Int.ne_of_gt hpos)

/-- **Range upper bound** (standalone). -/
theorem wrapBin_lt_count (bin bin_count : Int) (hpos : 0 < bin_count) :
    wrapBin bin bin_count < bin_count :=
  Int.emod_lt_of_pos _ hpos

/-! ## Identity and wrap-around theorems -/

/-- **Identity**: for in-range bins, `wrapBin` is the identity. -/
theorem wrapBin_identity (bin bin_count : Int)
    (hnn : 0 ≤ bin) (hlt : bin < bin_count) :
    wrapBin bin bin_count = bin := by
  simp only [wrapBin, Int.add_emod_right, Int.emod_eq_of_lt hnn hlt]

/-- **Wrap at bin_count**: `wrapBin bin_count bin_count = 0`. -/
theorem wrapBin_at_count (bin_count : Int) (_ : 0 < bin_count) :
    wrapBin bin_count bin_count = 0 := by
  simp only [wrapBin, Int.add_emod_right, Int.emod_self]

/-- **One below zero**: `wrapBin (-1) n = n - 1` when `n > 1`. -/
theorem wrapBin_neg1 (bin_count : Int) (h : 1 < bin_count) :
    wrapBin (-1) bin_count = bin_count - 1 := by
  simp only [wrapBin, show (-1 : Int) + bin_count = bin_count - 1 from by omega]
  exact Int.emod_eq_of_lt (by omega) (by omega)

/-- **Exactly -bin_count**: `wrapBin (-bin_count) bin_count = 0`. -/
theorem wrapBin_neg_count (bin_count : Int) (_ : 0 < bin_count) :
    wrapBin (-bin_count) bin_count = 0 := by
  simp only [wrapBin, show (-bin_count) + bin_count = (0 : Int) from by omega, Int.zero_emod]

/-- **One above**: `wrapBin (bin_count + k) bin_count = k` when `0 ≤ k < bin_count`. -/
theorem wrapBin_one_above (k bin_count : Int)
    (hk : 0 ≤ k) (hklt : k < bin_count) :
    wrapBin (bin_count + k) bin_count = k := by
  simp only [wrapBin, show bin_count + k + bin_count = k + bin_count * 2 from by omega,
             Int.add_mul_emod_self_left, Int.emod_eq_of_lt hk hklt]

/-! ## C++ model and bug theorems -/

/-- **Key lemma**: `Int.tmod (-1) n = -1` for `n > 1`.
    This follows from the definition: `tmod (negSucc 0) (ofNat (k+2)) = -(1 % (k+2)) = -1`. -/
private theorem tmod_neg1_gt1 (n : Int) (hn : 1 < n) : Int.tmod (-1) n = -1 := by
  match n with
  | Int.ofNat (k + 2) =>
    show (match (Int.negSucc 0 : Int), (Int.ofNat (k + 2) : Int) with
           | Int.ofNat m, Int.ofNat n => Int.ofNat (m % n)
           | Int.ofNat m, Int.negSucc n => Int.ofNat (m % n.succ)
           | Int.negSucc m, Int.ofNat n => -Int.ofNat (m.succ % n)
           | Int.negSucc m, Int.negSucc n => -Int.ofNat (m.succ % n.succ)) = -1
    simp only
    rw [Nat.mod_eq_of_lt (by omega)]
    rfl

/-- **C++ latent bug**: `wrapBinCpp (-bin_count - 1) bin_count = -1` for `bin_count > 1`.

    When `bin = -bin_count - 1`, `bin + bin_count = -1 < 0`, and C++ truncation mod
    returns `-1` — a negative array index that causes undefined behaviour. -/
theorem wrapBinCpp_bug_general (n : Int) (hn : 1 < n) :
    wrapBinCpp (-n - 1) n = -1 := by
  simp only [wrapBinCpp, show -n - 1 + n = (-1 : Int) from by omega]
  exact tmod_neg1_gt1 n hn

/-- **Models agree on the valid domain**: when `bin + bin_count ≥ 0`,
    `wrapBin` and `wrapBinCpp` give the same result (non-negative argument → both agree). -/
theorem wrapBin_eq_wrapBinCpp_valid (bin bin_count : Int)
    (hsum : 0 ≤ bin + bin_count) :
    wrapBin bin bin_count = wrapBinCpp bin bin_count := by
  simp only [wrapBin, wrapBinCpp, Int.tmod_eq_emod_of_nonneg hsum]

/-! ## Caller safety theorem -/

/-- **`get_offset_bin_index` caller safety**: passing `bin - offset` where
    `bin ∈ [0, bin_count)` and `offset ∈ [0, bin_count)` always gives `sum ≥ 1 > 0`,
    so `wrapBin` and `wrapBinCpp` agree and the result is in `[0, bin_count)`.
    Current callers are **never** affected by the latent bug. -/
theorem wrapBinOffset_valid (bin offset bin_count : Int)
    (hpos  : 0 < bin_count)
    (hbin_lb : 0 ≤ bin)  (_hbin_ub : bin < bin_count)
    (_hoff_lb : 0 ≤ offset) (hoff_ub : offset < bin_count) :
    0 ≤ wrapBin (bin - offset) bin_count ∧
    wrapBin (bin - offset) bin_count < bin_count ∧
    wrapBin (bin - offset) bin_count = wrapBinCpp (bin - offset) bin_count := by
  refine ⟨wrapBin_nonneg _ _ hpos, wrapBin_lt_count _ _ hpos, ?_⟩
  apply wrapBin_eq_wrapBinCpp_valid
  omega

end PX4.ObstacleMath
