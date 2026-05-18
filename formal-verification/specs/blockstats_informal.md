# Informal Specification: `BlockStats<Type, M>`

🔬 *Lean Squad automated formal verification.*

**Source**: `src/lib/controllib/BlockStats.hpp`
**C++ template**: `control::BlockStats<Type, M>`

---

## Purpose

`BlockStats` is a running statistics accumulator for vectors of dimension `M`.
It accumulates three quantities:
- `_sum`: the element-wise sum of all update vectors
- `_sumSq`: the element-wise sum of squared elements
- `_count`: the number of updates

It provides derived accessors `getMean()`, `getVar()`, and `getStdDev()`.

The core correctness invariant is:

> After `n` calls to `update(u_1), ..., update(u_n)`:
> - `_sum[i] = u_1[i] + ... + u_n[i]` for each component `i`
> - `_sumSq[i] = u_1[i]^2 + ... + u_n[i]^2` for each component `i`
> - `_count = n`
> - `getMean()[i] = _sum[i] / n` (when `n > 0`)

---

## Preconditions

- `_count > 0` must hold before calling `getMean()`, `getVar()`, or `getStdDev()` (division by zero otherwise).
- No bounds on `Type` are enforced; overflow is possible for large `n` or large inputs.

---

## Postconditions

### `update(u)`

- `_sum' = _sum + u` (element-wise)
- `_sumSq' = _sumSq + u ⊙ u` (element-wise, where `⊙` is Hadamard/component-wise product)
- `_count' = _count + 1`

### `reset()`

- `_sum = 0` (zero vector)
- `_sumSq = 0` (zero vector)
- `_count = 0`

### `getMean()` (requires `_count > 0`)

- Returns `_sum / _count` (element-wise scalar division)
- After `n` updates: `getMean()[i] = (u_1[i] + ... + u_n[i]) / n`

### `getVar()` (requires `_count > 0`)

- Returns `(_sumSq - _sum ⊙ _sum / _count) / _count`
- This is the biased sample variance (population variance, dividing by `n` not `n-1`).
- After `n` updates: `getVar()[i] = (Σ u_k[i]^2) / n − ((Σ u_k[i]) / n)^2`

---

## Key Invariants

1. **Sum accumulation** (by induction on number of updates):
   After `n` updates with vectors `u_1, ..., u_n`:
   `_sum[i] = Σ_{k=1}^{n} u_k[i]` for all `i`.

2. **SumSq accumulation**:
   `_sumSq[i] = Σ_{k=1}^{n} (u_k[i])^2` for all `i`.

3. **Count accuracy**:
   `_count = n` where `n` is the number of `update` calls since last `reset`.

4. **Mean formula** (when `_count > 0`):
   `getMean()[i] = _sum[i] / _count`.

5. **Variance non-negativity**:
   For real-valued `Type`: `getVar()[i] ≥ 0` always (by Cauchy-Schwarz / variance ≥ 0).

6. **Reset postcondition**:
   After `reset()`, all three accumulators are zero.

---

## Edge Cases

- **Zero updates** (`_count = 0`): `getMean()`, `getVar()`, `getStdDev()` all divide by zero. The C++ code does not guard against this; callers must check `getCount() > 0`.
- **Single update** (`n = 1`): `getMean() = u_1`; `getVar() = 0` (variance of one sample is zero).
- **Constant input** (`u_1 = u_2 = ... = u_n = c`): `getMean() = c`, `getVar() = 0`.
- **Integer overflow**: for large `n` or large inputs, `_sum` and `_sumSq` can overflow.

---

## Examples

### 1D case (`M = 1`), 3 updates

```
reset()       → _sum=0, _sumSq=0, _count=0
update([2])   → _sum=2, _sumSq=4, _count=1
update([4])   → _sum=6, _sumSq=20, _count=2
update([6])   → _sum=12, _sumSq=56, _count=3
getMean()  = 12/3 = 4
getVar()   = (56 - 144/3) / 3 = (56 - 48) / 3 = 8/3
```

### Reset then single update

```
update([5])
reset()
→ _sum=0, _sumSq=0, _count=0
```

---

## Inferred Intent

- `BlockStats` is designed as a lightweight accumulator for real-time monitoring of filter/controller signals.
- The mean and variance are used to detect anomalies (drift, oscillation) in flight control loops.
- The template parameter `M` allows scalar (M=1) and vector (M>1) signals.
- The simplicity of the implementation (no Welford online algorithm) means numerical precision degrades for large `n` — this is acceptable for the short-duration flight windows in which it's used.

---

## Open Questions

1. Should `getMean()` / `getVar()` return a sentinel (NaN, 0) when `_count = 0` instead of dividing by zero?
2. Is `getVar()` intended as biased (population) or unbiased (sample) variance? The formula uses `/ _count` twice, giving biased variance. No comment clarifies this.
3. For the Lean model: should we model a 1D (`M = 1`) version for tractability, or a 2D generic version?

---

## Lean Modelling Plan

For tractability, the Lean model will specialise to **scalar (`M = 1`) integer arithmetic**:

```lean
structure BlockStats where
  sum : Int
  sumSq : Int
  count : Nat

def bsUpdate (s : BlockStats) (u : Int) : BlockStats :=
  { sum := s.sum + u, sumSq := s.sumSq + u * u, count := s.count + 1 }

def bsReset : BlockStats := { sum := 0, sumSq := 0, count := 0 }
```

Key theorems (all `omega`/`ring`-provable):
- `bsUpdate_count`: `(bsUpdate s u).count = s.count + 1`
- `bsUpdate_sum`: `(bsUpdate s u).sum = s.sum + u`
- `bsUpdate_sumSq`: `(bsUpdate s u).sumSq = s.sumSq + u * u`
- `bsFold_count`: count after `n` updates = initial count + `n`
- `bsFold_sum`: sum after `n` updates = initial sum + Σ inputs
- `bsReset_zero`: all fields are zero after reset
- `bsUpdate_mono_count`: count strictly increases each update
- `bsUpdate_sumSq_nonneg`: if `s.sumSq ≥ 0` initially then `(bsUpdate s u).sumSq ≥ 0`
