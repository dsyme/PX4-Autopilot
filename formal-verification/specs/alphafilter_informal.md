# Informal Specification: AlphaFilter::update

**Target**: `AlphaFilter<T>::updateCalculation` / `AlphaFilter<T>::update`
**Source file**: `src/lib/mathlib/math/filter/AlphaFilter.hpp`
**Phase**: 2 (informal spec)

---

## Purpose

`AlphaFilter` is a first-order IIR (infinite impulse response) digital low-pass filter, also
known as a leaky integrator or forgetting-factor average.  Each call to `update(sample)` blends
the new sample into the stored state with weight `alpha`:

```
new_state = state + alpha * (sample - state)
           = (1 - alpha) * state + alpha * sample
```

`alpha ∈ [0, 1]` controls the trade-off between responsiveness and smoothing:
- `alpha = 0` → state never changes (infinite time-constant, zero bandwidth)
- `alpha = 1` → state immediately equals sample (no filtering at all)
- `alpha = dt / (dt + tau)` where `dt` is the sample interval and `tau` is the time constant

---

## Preconditions

- `alpha ∈ [0, 1]`  (enforced by `setParameters`; values outside this range produce
  undefined/degenerate behaviour)
- `sample` is finite (NaN or infinity are not modelled)
- `state` (filter state) is initialised; defaults to `T{}` (i.e., zero for scalar types)

---

## Postconditions (after one call to `update(sample)`)

1. **Blending**: `new_state = old_state + alpha * (sample - old_state)`
   Equivalently: `new_state = (1 - alpha) * old_state + alpha * sample`

2. **Weighted average**: `new_state` is a convex combination of `old_state` and `sample` when
   `0 ≤ alpha ≤ 1`:
   - `min(old_state, sample) ≤ new_state ≤ max(old_state, sample)`

3. **No overshoot (nondecreasing case)**: If `old_state ≤ sample` and `0 ≤ alpha ≤ 1`, then
   `old_state ≤ new_state ≤ sample`.

4. **No overshoot (nonincreasing case)**: If `sample ≤ old_state` and `0 ≤ alpha ≤ 1`, then
   `sample ≤ new_state ≤ old_state`.

5. **Fixed point**: If `sample = old_state`, then `new_state = old_state`.

6. **Strictly closer** (when `0 < alpha < 1`): `|new_state - sample| < |old_state - sample|`
   whenever `old_state ≠ sample`.  The state strictly approaches the input on each step.

7. **Identity at alpha = 1**: If `alpha = 1`, then `new_state = sample`.

8. **Identity at alpha = 0**: If `alpha = 0`, then `new_state = old_state`.

---

## Invariants

- If `state` has always been updated from inputs in `[lo, hi]` and the initial state is also in
  `[lo, hi]`, then `state ∈ [lo, hi]` always.  (Closure under convex combinations.)

---

## Multi-step / convergence behaviour

After `n` steps with constant input `c`, starting from state `s0`:

```
state_n = c + (s0 - c) * (1 - alpha)^n
```

This follows by induction on `n`.  Key consequences:
- `state_n → c` as `n → ∞` for any `0 < alpha ≤ 1`  (exponential convergence)
- The error at step `n` is `(1 - alpha)^n * (s0 - c)`; the filter reaches 63% of the step
  response after `1/alpha` steps, and 95% after `3/alpha` steps.
- After exactly `n = ceil(log(ε) / log(1 - alpha))` steps, the error is below `ε`

> **Note**: exact convergence-speed proofs require real-valued analysis (Mathlib
> `Real.tendsto_pow_atTop_nhds_zero`); we restrict the Lean model to discrete, rational arithmetic.

---

## Edge Cases

| Condition | Behaviour |
|-----------|-----------|
| `alpha = 0` | State is frozen; never changes regardless of input |
| `alpha = 1` | State immediately equals input; no memory |
| `sample = state` | State is unchanged (fixed point) |
| `alpha > 1` | Undefined / oscillatory behaviour — not modelled |
| `alpha < 0` | Undefined — not modelled |
| `sample = NaN` / `±Inf` | C++ float result undefined; not modelled in Lean |

---

## Concrete Examples (for testing / `#eval`)

| `state` | `alpha` | `sample` | `new_state` |
|---------|---------|----------|-------------|
| 0       | 0       | 1        | 0           |
| 0       | 1       | 1        | 1           |
| 0       | 1/2     | 1        | 1/2         |
| 1/2     | 1/2     | 1        | 3/4         |
| 1       | 1/10    | 0        | 9/10        |
| -1      | 1/2     | 1        | 0           |

---

## Inferred Intent

The filter is intended to smooth noisy scalar (or vector) signals over time, providing a
low-pass frequency response.  The `alpha` parameter is the main user-facing design knob;
typically set indirectly via `setParameters(dt, tau)` which computes `alpha = dt / (dt + tau)`.

The key safety property for autopilot use is **no overshoot**: the filter output never exceeds
the range `[old_state, sample]` (or `[sample, old_state]`), which is essential to avoid
injecting spurious transients into attitude or rate controllers.

---

## Open Questions

1. **Alpha clamping**: `setParameters` only sets `alpha` if the denominator exceeds `FLT_EPSILON`.
   If `dt + tau ≤ FLT_EPSILON`, `alpha` is not updated.  Is this the correct behaviour for
   very small time constants?  Could a stale `alpha` from a previous call cause unexpected
   filter behaviour?

2. **Vector case**: The quaternion specialisation uses a different update formula (axis-angle
   interpolation on SO(3)).  The Lean model covers only the scalar/Euclidean case.

3. **Thread safety**: `update()` reads and writes `_filter_state`.  If called from two threads
   simultaneously (e.g., fast sampling + parameter update), there is a data race.  Not modelled.

---

🔬 *Generated by Lean Squad automated formal verification.*
