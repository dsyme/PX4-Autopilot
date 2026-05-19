/-!
# PX4 `BlockStats` — Formal Verification

🔬 *Lean Squad automated formal verification.*

This file models and proves correctness properties of PX4's running statistics
accumulator `BlockStats<Type, M>`, specialised to scalar integer arithmetic.

- **C++ source**: `src/lib/controllib/BlockStats.hpp`
- **Informal spec**: `formal-verification/specs/blockstats_informal.md`

## C++ Source (key methods)

```cpp
template<class Type, size_t M>
class BlockStats {
  void update(const matrix::Vector<Type, M> &u) {
    _sum += u;
    _sumSq += u.emult(u);
    _count += 1;
  }
  void reset() { _sum.setZero(); _sumSq.setZero(); _count = 0; }
  size_t getCount() { return _count; }
  Vector<Type,M> getMean()  { return _sum / _count; }
  Vector<Type,M> getVar()   { return (_sumSq - _sum.emult(_sum) / _count) / _count; }
};
```

## Model

Specialise to **scalar (`M = 1`) integer arithmetic**. The state is a triple
`(sum, sumSq, count)` updated by a pure function.

**Abstracted away**: the `Block` parent class hierarchy, floating-point rounding,
vector-dimension generality, and the potential division-by-zero in `getMean`/`getVar`
when `count = 0`.

## Properties Proved (10 theorems, 0 sorry)

1. `bsUpdate_count`       — count increases by 1 per update
2. `bsUpdate_sum`         — sum increases by `u`
3. `bsUpdate_sumSq`       — sumSq increases by `u²`
4. `bsReset_zero`         — reset gives the zero state
5. `bsUpdate_sumSq_nonneg`— sumSq remains ≥ 0 if it started ≥ 0
6. `bsFold_count`         — count after folding a list = initial count + list length
7. `bsFold_sum`           — sum after folding = initial sum + List.sum of inputs
8. `bsFold_sumSq_nonneg`  — sumSq ≥ 0 after folding any list (starting from ≥ 0)
9. `bsUpdate_mono_count`  — count strictly increases each update
10. `bsMean_single`       — mean (as Rat) after one update equals the update value
-/

namespace PX4.BlockStats

/-- Scalar accumulator state: running sum, sum-of-squares, count. -/
structure BSState where
  sum   : Int
  sumSq : Int
  count : Nat

/-- Pure functional update: accumulate one new sample `u`. -/
def bsUpdate (s : BSState) (u : Int) : BSState :=
  { sum   := s.sum + u
    sumSq := s.sumSq + u * u
    count := s.count + 1 }

/-- Reset: return to the zero state. -/
def bsReset : BSState := { sum := 0, sumSq := 0, count := 0 }

/-- Fold a list of samples, starting from a given state. -/
def bsFold (s : BSState) (us : List Int) : BSState :=
  us.foldl bsUpdate s

/-- Mean as a rational number (only meaningful when count > 0). -/
def bsMean (s : BSState) : Rat := (s.sum : Rat) / (s.count : Rat)

-- ────────────────────────────────────────────────────────────────────────────
-- Single-step theorems
-- ────────────────────────────────────────────────────────────────────────────

/-- Each call to `update` increments the count by exactly 1. -/
theorem bsUpdate_count (s : BSState) (u : Int) :
    (bsUpdate s u).count = s.count + 1 := by
  simp [bsUpdate]

/-- Each call to `update` adds `u` to the running sum. -/
theorem bsUpdate_sum (s : BSState) (u : Int) :
    (bsUpdate s u).sum = s.sum + u := by
  simp [bsUpdate]

/-- Each call to `update` adds `u²` to the sum-of-squares. -/
theorem bsUpdate_sumSq (s : BSState) (u : Int) :
    (bsUpdate s u).sumSq = s.sumSq + u * u := by
  simp [bsUpdate]

/-- If `sumSq ≥ 0` before an update, it remains `≥ 0` after (since `u² ≥ 0`). -/
theorem bsUpdate_sumSq_nonneg (s : BSState) (u : Int) (h : 0 ≤ s.sumSq) :
    0 ≤ (bsUpdate s u).sumSq := by
  simp only [bsUpdate]
  have huu : (0 : Int) ≤ u * u := by
    by_cases h : 0 ≤ u
    · exact Int.mul_nonneg h h
    · simp at h
      have hn : 0 ≤ -u := Int.neg_nonneg.mpr (Int.le_of_lt h)
      have key := Int.mul_nonneg hn hn
      rw [Int.neg_mul_neg] at key
      exact key
  exact Int.add_nonneg h huu

/-- Count strictly increases with each update. -/
theorem bsUpdate_mono_count (s : BSState) (u : Int) :
    s.count < (bsUpdate s u).count := by
  simp [bsUpdate]

-- ────────────────────────────────────────────────────────────────────────────
-- Reset theorem
-- ────────────────────────────────────────────────────────────────────────────

/-- After `reset`, all accumulators are zero. -/
theorem bsReset_zero : bsReset = { sum := 0, sumSq := 0, count := 0 } :=
  rfl

-- ────────────────────────────────────────────────────────────────────────────
-- Fold (iterated update) theorems
-- ────────────────────────────────────────────────────────────────────────────

/-- Count after folding a list equals initial count plus list length. -/
theorem bsFold_count (s : BSState) (us : List Int) :
    (bsFold s us).count = s.count + us.length := by
  induction us generalizing s with
  | nil => simp [bsFold]
  | cons u rest ih =>
    simp only [bsFold, List.foldl, List.length_cons]
    rw [show List.foldl bsUpdate (bsUpdate s u) rest =
            bsFold (bsUpdate s u) rest from rfl]
    rw [ih (bsUpdate s u)]
    simp [bsUpdate]; omega

/-- Sum after folding equals initial sum plus the sum of the list. -/
theorem bsFold_sum (s : BSState) (us : List Int) :
    (bsFold s us).sum = s.sum + us.foldl (· + ·) 0 := by
  induction us generalizing s with
  | nil => simp [bsFold]
  | cons u rest ih =>
    simp only [bsFold, List.foldl]
    rw [show List.foldl bsUpdate (bsUpdate s u) rest =
            bsFold (bsUpdate s u) rest from rfl]
    rw [ih (bsUpdate s u)]
    simp [bsUpdate]
    have key : ∀ (acc : Int) (xs : List Int),
        xs.foldl (· + ·) acc = acc + xs.foldl (· + ·) 0 := by
      intro acc xs
      induction xs generalizing acc with
      | nil => simp
      | cons x rest' ih' =>
        simp only [List.foldl]
        have h1 := ih' (acc + x)
        have h2 := ih' (0 + x)
        omega
    have hk := key u rest; omega

/-- `sumSq ≥ 0` is an inductive invariant: if it holds before folding, it holds after. -/
theorem bsFold_sumSq_nonneg (s : BSState) (us : List Int) (h : 0 ≤ s.sumSq) :
    0 ≤ (bsFold s us).sumSq := by
  induction us generalizing s with
  | nil => simp [bsFold, h]
  | cons u rest ih =>
    simp only [bsFold, List.foldl]
    rw [show List.foldl bsUpdate (bsUpdate s u) rest =
            bsFold (bsUpdate s u) rest from rfl]
    apply ih
    exact bsUpdate_sumSq_nonneg s u h

-- ────────────────────────────────────────────────────────────────────────────
-- Mean theorem
-- ────────────────────────────────────────────────────────────────────────────

/-- After a single update starting from the zero state, the mean equals the input. -/
theorem bsMean_single (u : Int) :
    bsMean (bsUpdate bsReset u) = (u : Rat) := by
  have hs : bsUpdate bsReset u = { sum := u, sumSq := u * u, count := 1 } := by
    simp [bsUpdate, bsReset]
  simp only [bsMean, hs]
  rw [Rat.div_def]
  have hinv : (↑(1 : Nat) : Rat)⁻¹ = 1 := by rw [Rat.inv_def]; rfl
  rw [hinv, Rat.mul_one]

end PX4.BlockStats
