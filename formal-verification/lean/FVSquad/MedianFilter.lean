/-!
# MedianFilter — Formal Verification

🔬 Lean Squad automated formal verification.

This file models and proves correctness properties of `math::MedianFilter<T, WINDOW>`
from PX4-Autopilot's mathlib:

- **C++ source**: `src/lib/mathlib/math/filter/MedianFilter.hpp`
- **Informal spec**: `formal-verification/specs/medianfilter_informal.md`

## Model

We model the filter over `Int` (exact arithmetic, no NaN/infinity).
The C++ template operates over `float`, `double`, or integer types; our Lean model
is an integer abstraction.

The key operation is `median()`:

```cpp
T median() {
    T sorted[WINDOW];
    memcpy(sorted, _buffer, sizeof(_buffer));
    qsort(&sorted, WINDOW, sizeof(T), cmp);
    return sorted[WINDOW / 2];
}
```

We model `median` as: sort a copy of the window list, return the element at index
`length / 2`.

## Proved properties

| Theorem | Statement | Status |
|---------|-----------|--------|
| `mfMedian_mem` | Median is a member of the input window | ✅ Proved |
| `mfMedian_const` | Constant window returns that value | ✅ Proved |
| `mfMedian_ge_sorted_first` | Result ≥ smallest sorted element (window ≥ 3) | ✅ Proved |
| `mfMedian_le_sorted_last` | Result ≤ largest sorted element (window ≥ 3) | ✅ Proved |
| `mfInsert_lt` | Head stays in bounds after insert | ✅ Proved |
| `mfInsert_head_wraps` | Head wraps to 0 after last slot | ✅ Proved |
| 6× concrete `native_decide` examples | Window-3 and window-5 concrete values | ✅ Proved |

## Approximations / Out of Scope

- **NaN / infinity**: the C++ `cmp` comparator has special handling for non-finite
  floats (sorted to the top). This is not modelled — our model uses total integer order.
- **Zero-initialisation bias**: the C++ buffer is zero-initialised; early calls to
  `median()` before `WINDOW` inserts return a mix of zeros and real samples.
  Modelled abstractly as a pure `List Int` without the initialisation phase.
- **`uint8_t` overflow**: `_head` is `uint8_t` in C++, capping at 255 elements.
  We use `Nat` with explicit `% window` guards.
- **`qsort` vs `mergeSort`**: functionally equivalent for total orders; we use
  `List.mergeSort intLE` where `intLE` is a total, transitive Bool comparator.
-/

namespace PX4.MedianFilter

-- ============================================================
-- Part 0: Bool comparator for Int (required by List.mergeSort API)
-- ============================================================

/-- Bool comparator: `a ≤ b` -/
private def intLE (a b : Int) : Bool := if a ≤ b then true else false

private theorem intLE_total (a b : Int) : (intLE a b || intLE b a) = true := by
  simp only [intLE]; rcases Int.le_total a b with h | h <;> simp [h]

private theorem intLE_trans (a b c : Int) (h1 : intLE a b = true) (h2 : intLE b c = true) :
    intLE a c = true := by
  simp only [intLE] at *
  by_cases hab : a ≤ b
  · by_cases hbc : b ≤ c
    · simp [Int.le_trans hab hbc]
    · simp [hbc] at h2
  · simp [hab] at h1

private theorem intLE_iff (a b : Int) : intLE a b = true ↔ a ≤ b := by
  simp only [intLE]; by_cases h : a ≤ b <;> simp [h]

/-- Key lemma: `sorted[i] ≤ sorted[j]` for `i ≤ j`, where `sorted = l.mergeSort intLE`.

    Proved using `List.pairwise_mergeSort` (stdlib) plus `List.pairwise_iff_getElem`. -/
private theorem sorted_getElem_le (l : List Int) (i j : Nat)
    (hi : i < l.length) (hj : j < l.length) (hij : i ≤ j) :
    (l.mergeSort intLE)[i]'(by rwa [List.length_mergeSort]) ≤
    (l.mergeSort intLE)[j]'(by rwa [List.length_mergeSort]) := by
  rcases Nat.lt_or_eq_of_le hij with h | h
  · rw [← intLE_iff]
    exact List.pairwise_iff_getElem.mp (List.pairwise_mergeSort intLE_trans intLE_total l)
      i j (by rwa [List.length_mergeSort]) (by rwa [List.length_mergeSort]) h
  · subst h; exact Int.le_refl _

-- ============================================================
-- Part 1: Abstract median function
-- ============================================================

/-- Abstract median over an integer list: sort and return the middle element.

    Models `MedianFilter<T, WINDOW>::median()` — sort a copy of the window buffer,
    return `sorted[WINDOW / 2]`.

    **Precondition**: `l` is non-empty (guaranteed by `static_assert(WINDOW >= 3)`). -/
def mfMedian (l : List Int) (h : 0 < l.length) : Int :=
  (l.mergeSort intLE)[l.length / 2]'(by rw [List.length_mergeSort]; omega)

-- ============================================================
-- Concrete examples (native_decide)
-- ============================================================

-- Window = 3: basic ordering
-- [1, 5, 2] → sorted [1, 2, 5] → index 1 = 2
example : mfMedian [1, 5, 2] (by decide) = 2 := by native_decide

-- Window = 3: spike rejection — outlier 10 is discarded
-- [10, 2, 3] → sorted [2, 3, 10] → index 1 = 3
example : mfMedian [10, 2, 3] (by decide) = 3 := by native_decide

-- Window = 3: negative values
-- [-1, -5, -2] → sorted [-5, -2, -1] → index 1 = -2
example : mfMedian [-1, -5, -2] (by decide) = -2 := by native_decide

-- Window = 3: constant window
example : mfMedian [4, 4, 4] (by decide) = 4 := by native_decide

-- Window = 5: mixed values
-- [3, 1, 4, 1, 5] → sorted [1, 1, 3, 4, 5] → index 2 = 3
example : mfMedian [3, 1, 4, 1, 5] (by decide) = 3 := by native_decide

-- Window = 5: constant window
example : mfMedian [7, 7, 7, 7, 7] (by decide) = 7 := by native_decide

-- ============================================================
-- Theorem: median is a member of the input list
-- ============================================================

/-- **`mfMedian_mem`**: The median of any window is one of the window's elements.

    This follows from `List.mem_mergeSort` (mergeSort preserves membership) and
    `List.getElem_mem` (every element at a valid index is a member). -/
theorem mfMedian_mem (l : List Int) (h : 0 < l.length) : mfMedian l h ∈ l := by
  simp only [mfMedian]
  rw [← List.mem_mergeSort]
  exact List.getElem_mem _

-- ============================================================
-- Theorem: constant window returns the constant value
-- ============================================================

/-- **`mfMedian_const`**: The median of a constant window `[x, x, …, x]` is `x`.

    Proof: every element of `(replicate n x).mergeSort intLE` equals `x`
    (by `List.mem_replicate`); therefore the element at index `n / 2` equals `x`. -/
theorem mfMedian_const (x : Int) (n : Nat) (hn : 0 < n) :
    mfMedian (List.replicate n x) (by simp [List.length_replicate, hn]) = x := by
  simp only [mfMedian, List.length_replicate]
  have hbound : n / 2 < ((List.replicate n x).mergeSort intLE).length := by
    rw [List.length_mergeSort, List.length_replicate]; omega
  have hmem : ((List.replicate n x).mergeSort intLE)[n / 2]'hbound ∈
      (List.replicate n x).mergeSort intLE := List.getElem_mem _
  rw [List.mem_mergeSort] at hmem
  exact (List.mem_replicate.mp hmem).2

-- ============================================================
-- Theorems: range containment (median ∈ [min, max])
-- ============================================================

/-- **`mfMedian_ge_sorted_first`**: For windows of length ≥ 3, the median is ≥ the
    minimum element (the first element of the sorted copy).

    Key: index 0 ≤ length / 2 for any length, so `sorted_getElem_le` applies. -/
theorem mfMedian_ge_sorted_first (l : List Int) (h : 3 ≤ l.length) :
    (l.mergeSort intLE)[0]'(by rw [List.length_mergeSort]; omega) ≤ mfMedian l (by omega) :=
  sorted_getElem_le l 0 (l.length / 2) (by omega) (by omega) (by omega)

/-- **`mfMedian_le_sorted_last`**: For windows of length ≥ 3, the median is ≤ the
    maximum element (the last element of the sorted copy).

    Key: length / 2 ≤ length - 1 for length ≥ 3 (odd window), so `sorted_getElem_le` applies. -/
theorem mfMedian_le_sorted_last (l : List Int) (h : 3 ≤ l.length) :
    mfMedian l (by omega) ≤
    (l.mergeSort intLE)[l.length - 1]'(by rw [List.length_mergeSort]; omega) :=
  sorted_getElem_le l (l.length / 2) (l.length - 1) (by omega) (by omega) (by omega)

-- ============================================================
-- Part 2: Circular buffer head invariant
-- ============================================================

/-- Model of `MedianFilter::insert`: advance the circular head by 1 modulo window.

    C++ implementation: `_head = (_head + 1) % WINDOW`. -/
def mfInsert (head window : Nat) (_h : head < window) : Nat := (head + 1) % window

/-- **`mfInsert_lt`**: Head stays strictly within `[0, window)` after every insert.

    Ensures the C++ head index is always a valid buffer index. -/
theorem mfInsert_lt (head window : Nat) (hw : 0 < window) (hh : head < window) :
    mfInsert head window hh < window :=
  Nat.mod_lt _ hw

/-- **`mfInsert_head_wraps`**: Inserting from the last slot wraps the head to 0.

    This is the ring-wrap condition: after writing slot `window - 1`, the next write
    targets slot 0. -/
theorem mfInsert_head_wraps (window : Nat) (hw : 0 < window) :
    mfInsert (window - 1) window (by omega) = 0 := by
  simp only [mfInsert]
  have : window - 1 + 1 = window := Nat.sub_add_cancel hw
  rw [this, Nat.mod_self]

end PX4.MedianFilter
