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

## Properties Proved (15 theorems, 0 sorry)

1. `bsUpdate_count`       — count increases by 1 per update
2. `bsUpdate_sum`         — sum increases by `u`
3. `bsUpdate_sumSq`       — sumSq increases by `u * u`
4. `bsReset_zero`         — reset gives the zero state
5. `bsUpdate_sumSq_nonneg`— sumSq remains ≥ 0 if it started ≥ 0
6. `bsFold_count`         — count after folding a list = initial count + list length
7. `bsFold_sum`           — sum after folding = initial sum + List.sum of inputs
8. `bsFold_sumSq_nonneg`  — sumSq ≥ 0 after folding any list (starting from ≥ 0)
9. `bsUpdate_mono_count`  — count strictly increases each update
10. `bsMean_single`       — mean (as Rat) after one update equals the update value
11. `cs_ring_identity`    — ring identity (A): n·(n·u·u−2·sv·u+ss) = (n·u−sv)²+(n·ss−sv·sv)
12. `cs_goal_identity`    — step decomposition identity (B) for the inductive case
13. `bsUpdate_cauchy_schwarz_step` — Cauchy–Schwarz invariant is preserved by one update
14. `bsFold_cauchy_schwarz` — count * sumSq ≥ sum * sum for any list (Cauchy–Schwarz)
15. `bsFold_var_nonneg`   — variance numerator count*sumSq − sum*sum ≥ 0
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

-- ────────────────────────────────────────────────────────────────────────────
-- Cauchy–Schwarz invariant: count * sumSq ≥ sum * sum
-- ────────────────────────────────────────────────────────────────────────────

/-!
## Cauchy–Schwarz / Variance Non-Negativity

The **Cauchy–Schwarz inequality** for the sequence (x₁, …, xₙ) and the
all-ones vector states:

    n · Σxᵢ² ≥ (Σxᵢ)²

In `BlockStats` terms: `count * sumSq ≥ sum * sum`.

This establishes that the running variance estimator
`(sumSq / count) - (sum / count)²` is always non-negative — a fundamental
sanity property for any statistical accumulator.

**Proof strategy**: The invariant is maintained one update at a time.
For the inductive step we need:

    (n + 1)(ss + u²) ≥ (sv + u)²

Given `n · ss ≥ sv · sv` and `ss ≥ 0`.  Two algebraic identities are used:

  (A)  n · (n·u·u − 2·sv·u + ss) = (n·u − sv)·(n·u − sv) + (n·ss − sv·sv)

  (B)  (n + 1)·(ss + u·u) − (sv + u)·(sv + u)
         = (n·ss − sv·sv) + (n·u·u − 2·sv·u + ss)

Both are proved by explicit rewrite chains and `omega` (no `ring` tactic,
which is a Mathlib-only tactic unavailable in this stdlib-only project).

The RHS of (A) is a sum of two non-negative terms, so the LHS is non-negative.
When n ≥ 1, dividing by n gives `n·u² − 2·sv·u + ss ≥ 0`, and (B) closes
the goal.  When n = 0, `sv = 0` is forced by the CS invariant and `ss ≥ 0`
suffices directly.
-/

/-- Helper: `x * x ≥ 0` for any integer `x`. -/
private theorem int_mul_self_nonneg (x : Int) : 0 ≤ x * x := by
  by_cases h : 0 ≤ x
  · exact Int.mul_nonneg h h
  · have hlt : x < 0 := Int.not_le.mp h
    have hn : 0 ≤ -x := Int.neg_nonneg.mpr (Int.le_of_lt hlt)
    have key := Int.mul_nonneg hn hn
    rwa [Int.neg_mul_neg] at key

/-- Key ring identity (A): `n·(n·u·u − 2·sv·u + ss) = (n·u − sv)² + (n·ss − sv²)`.

    Proved without the `ring` tactic using explicit associativity/commutativity
    rewrites followed by `omega` on a linear residual. -/
private theorem cs_ring_identity (n u sv ss : Int) :
    n * (n * u * u - 2 * sv * u + ss) =
    (n * u - sv) * (n * u - sv) + (n * ss - sv * sv) := by
  simp only [Int.sub_mul, Int.mul_sub, Int.mul_add]
  have h1 : n * u * sv = n * sv * u := Int.mul_right_comm n u sv
  have h2 : sv * (n * u) = n * sv * u := by
    rw [show sv * (n * u) = sv * n * u from by rw [Int.mul_assoc]]
    rw [show sv * n = n * sv from Int.mul_comm sv n]
  have h3 : n * u * (n * u) = n * n * (u * u) := by
    rw [show n * u * (n * u) = n * (u * (n * u)) from by rw [Int.mul_assoc]]
    rw [show u * (n * u) = u * n * u from by rw [Int.mul_assoc]]
    rw [show u * n = n * u from Int.mul_comm u n]
    rw [show n * u * u = n * (u * u) from by rw [Int.mul_assoc]]
    rw [Int.mul_assoc n n (u * u)]
  have h4 : n * (n * u * u) = n * n * (u * u) := by
    rw [show n * u * u = n * (u * u) from by rw [Int.mul_assoc]]
    rw [Int.mul_assoc n n (u * u)]
  have h5 : n * (2 * sv * u) = 2 * (n * sv * u) := by
    rw [show 2 * sv * u = 2 * (sv * u) from by rw [Int.mul_assoc]]
    rw [show n * (2 * (sv * u)) = 2 * (n * (sv * u)) from by
          rw [← Int.mul_assoc 2 n (sv * u), Int.mul_comm 2 n, Int.mul_assoc n 2 (sv * u)]]
    rw [show n * (sv * u) = n * sv * u from by rw [← Int.mul_assoc]]
  omega

/-- Key identity (B): step decomposition for the Cauchy–Schwarz inductive case. -/
private theorem cs_goal_identity (n u sv ss : Int) :
    (n + 1) * (ss + u * u) - (sv + u) * (sv + u) =
    (n * ss - sv * sv) + (n * u * u - 2 * sv * u + ss) := by
  have h1 : u * sv = sv * u := Int.mul_comm u sv
  have h2 : 2 * sv * u = sv * u + sv * u := by
    have heq1 : 2 * sv * u = 2 * (sv * u) := by rw [Int.mul_assoc]
    have heq2 : 2 * (sv * u) = sv * u + sv * u := Int.two_mul (sv * u)
    omega
  have h3 : n * u * u = n * (u * u) := by rw [Int.mul_assoc]
  simp only [Int.add_mul, Int.mul_add]
  rw [h1, h2, h3]; omega

/-- The Cauchy–Schwarz invariant `count * sumSq ≥ sum * sum` together with
    `sumSq ≥ 0` is preserved by a single `bsUpdate`. -/
private theorem bsUpdate_cauchy_schwarz_step (s : BSState) (u : Int)
    (h : (s.count : Int) * s.sumSq ≥ s.sum * s.sum)
    (hss : 0 ≤ s.sumSq) :
    ((bsUpdate s u).count : Int) * (bsUpdate s u).sumSq ≥ (bsUpdate s u).sum * (bsUpdate s u).sum ∧
    0 ≤ (bsUpdate s u).sumSq := by
  simp only [bsUpdate]
  constructor
  · have hcast : ((s.count + 1 : Nat) : Int) = (s.count : Int) + 1 := by omega
    rw [hcast]
    by_cases hn0 : (s.count : Int) = 0
    · -- n = 0: h forces s.sum = 0 (since 0 ≥ s.sum * s.sum ≥ 0)
      have hsv0 : s.sum = 0 := by
        have heq : s.sum * s.sum = 0 :=
          Int.le_antisymm (by rw [hn0] at h; simpa using h) (int_mul_self_nonneg s.sum)
        by_cases h0 : 0 ≤ s.sum
        · by_cases h1 : s.sum = 0
          · exact h1
          · have hpos : 0 < s.sum := by omega
            exact absurd heq (Int.ne_of_gt (Int.mul_pos hpos hpos))
        · have hlt : s.sum < 0 := Int.not_le.mp h0
          have hmp : 0 < -s.sum := Int.neg_pos.mpr hlt
          have key : 0 < (-s.sum) * (-s.sum) := Int.mul_pos hmp hmp
          rw [Int.neg_mul_neg] at key
          exact absurd heq (Int.ne_of_gt key)
      rw [hn0, hsv0]; simp; omega
    · -- n ≥ 1: use identity (A) to show the auxiliary expression is non-negative,
      --         divide by n, then use identity (B) to close the goal.
      have hpos : (0 : Int) < s.count := by
        have := Int.natCast_nonneg s.count; omega
      -- By identity (A), n * (n*u*u - 2*sv*u + ss) = (n*u - sv)^2 + (n*ss - sv^2) ≥ 0
      have hmul_nonneg : 0 ≤ (s.count : Int) *
          ((s.count : Int) * u * u - 2 * s.sum * u + s.sumSq) := by
        rw [cs_ring_identity (s.count : Int) u s.sum s.sumSq]
        exact Int.add_nonneg (int_mul_self_nonneg _) (Int.sub_nonneg.mpr h)
      -- Divide by n (positive): n*u*u - 2*sv*u + ss ≥ 0
      have hmid : 0 ≤ (s.count : Int) * u * u - 2 * s.sum * u + s.sumSq :=
        Int.le_of_mul_le_mul_left (by rwa [Int.mul_zero]) hpos
      -- By identity (B), the step difference decomposes into two non-negative parts
      have hres : 0 ≤ ((s.count : Int) + 1) * (s.sumSq + u * u) -
          (s.sum + u) * (s.sum + u) := by
        rw [cs_goal_identity (s.count : Int) u s.sum s.sumSq]
        exact Int.add_nonneg (Int.sub_nonneg.mpr h) hmid
      exact Int.sub_nonneg.mp hres
  · exact Int.add_nonneg hss (int_mul_self_nonneg u)

/-- **Cauchy–Schwarz**: for any list of integer samples accumulated from the
    zero state, `count * sumSq ≥ sum * sum`.

    Equivalently, the running variance estimator is always non-negative.
    This is the discrete Cauchy–Schwarz inequality `(Σxᵢ)² ≤ n · Σxᵢ²`. -/
theorem bsFold_cauchy_schwarz (us : List Int) :
    let s := bsFold bsReset us
    (s.count : Int) * s.sumSq ≥ s.sum * s.sum := by
  suffices ∀ s0 : BSState,
      (s0.count : Int) * s0.sumSq ≥ s0.sum * s0.sum → 0 ≤ s0.sumSq →
      (bsFold s0 us).count * (bsFold s0 us).sumSq ≥ (bsFold s0 us).sum * (bsFold s0 us).sum from
    this bsReset (by simp [bsReset]) (by simp [bsReset])
  intro s0 hs0 hss0
  induction us generalizing s0 with
  | nil => simpa [bsFold]
  | cons u rest ih =>
    simp only [bsFold, List.foldl]
    have step := bsUpdate_cauchy_schwarz_step s0 u hs0 hss0
    exact ih _ step.1 step.2

/-- The variance numerator `count * sumSq − sum * sum` is always non-negative.

    This is a direct corollary of `bsFold_cauchy_schwarz` and is the key
    invariant ensuring that `BlockStats::getVar()` never returns a negative
    value (modulo integer-division truncation). -/
theorem bsFold_var_nonneg (us : List Int) :
    let s := bsFold bsReset us
    0 ≤ (s.count : Int) * s.sumSq - s.sum * s.sum :=
  Int.sub_nonneg.mpr (bsFold_cauchy_schwarz us)

end PX4.BlockStats
