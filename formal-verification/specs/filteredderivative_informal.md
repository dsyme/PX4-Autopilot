# Informal Specification: `FilteredDerivative<T>::update`

🔬 *Lean Squad automated formal verification.*

- **C++ source**: `src/lib/mathlib/math/filter/FilteredDerivative.hpp`
- **Author**: Silvan Fuhrer (Auterion)
- **Lean file**: `formal-verification/lean/FVSquad/FilteredDerivative.lean`

---

## Purpose

`FilteredDerivative<T>` estimates the derivative of a sampled signal by computing
finite differences between consecutive samples and then smoothing the result through
a first-order IIR alpha filter (see `AlphaFilter`).

It is used in PX4 whenever a smooth derivative estimate is needed from a noisy
signal — for example, altitude rate estimation from barometric pressure readings.

---

## State

The class maintains three internal state fields:

| Field | Type | Description |
|---|---|---|
| `_alpha_filter` | `AlphaFilter<T>` | Running smoothed estimate of the derivative |
| `_previous_sample` | `T` | The most recently stored sample |
| `_initialized` | `bool` | Whether the first sample has been consumed |

Additionally, the class requires an external parameter `_sample_interval` (positive
real, same units as the samples' time axis) which must be set before use via
`setParameters`.

---

## Preconditions

1. `setParameters(sample_interval, time_constant)` must be called before `update`,
   with `sample_interval > 0` and `time_constant > 0`.
2. `sample_interval > FLT_EPSILON` (enforced internally; the model uses `dt > 0`).
3. The `alpha` coefficient inside `_alpha_filter` must satisfy `0 ≤ alpha ≤ 1`.

---

## Postconditions for `update(sample)`

### First call (not yet initialized)

- `_initialized` is set to `true`.
- `_previous_sample` is set to `sample`.
- The alpha filter state is **not updated** — it remains at its prior value (0
  after construction, or the reset value after `reset`).
- The returned reference is `_alpha_filter.getState()` — i.e., the *unchanged*
  alpha-filter state.

**Design intent**: The first call "primes" the filter by recording the first sample
without producing a meaningful derivative estimate, because no previous sample
exists. Callers should discard or ignore the output of the first call.

### Subsequent calls (initialized)

- The raw derivative `deriv = (sample - _previous_sample) / sample_interval` is
  computed.
- This derivative is fed into the alpha filter: `_alpha_filter.update(deriv)`.
- `_previous_sample` is updated to `sample`.
- The returned reference is the updated alpha-filter state.

**Key property**: if `sample == _previous_sample` (no change between calls), then
`deriv = 0` and the alpha filter is updated with zero — so the output decays
exponentially toward zero over subsequent constant-input calls.

---

## Invariants

1. **`initialized` is monotone**: once set to `true`, it is never reset to `false`
   (except by an explicit call to `reset()`). In the model, we do *not* model the
   `_initialized = false` reset triggered by `sample_interval ≤ FLT_EPSILON` (this
   path is guarded against by the precondition `dt > 0`).

2. **`prevSample` is always the last input**: after every call, `_previous_sample`
   holds the value of `sample` from that call.

3. **Output is always the alpha filter state**: `getState()` always returns the
   same value as `update()`.

---

## Edge Cases

| Scenario | Behaviour |
|---|---|
| First call ever | alpha state unchanged; `initialized` becomes `true`; `prevSample = sample` |
| Same sample repeated | derivative = 0; alpha state decays toward 0 over time |
| Constant-slope ramp (samples increase by `m` each step) | derivative = `m / dt` every step; alpha state converges to `m/dt` |
| `reset(v)` called | alpha state set to `v`, `initialized = false`; next call behaves as first call |
| Very large sample jump | derivative can be arbitrarily large; alpha filter is bounded only by its inputs |

---

## Examples

**Example 1: First call**
- State before: `{alphaState=0, prevSample=0, initialized=false}`
- `update(5.0)` with `dt=0.01, alpha=0.5`
- State after: `{alphaState=0, prevSample=5.0, initialized=true}`
- Output: `0`

**Example 2: Second call — step input**
- State before: `{alphaState=0, prevSample=5.0, initialized=true}`
- `update(5.1)` with `dt=0.01, alpha=0.5`
- Raw derivative: `(5.1 - 5.0) / 0.01 = 10.0`
- Alpha update: `(1-0.5)*0 + 0.5*10 = 5.0`
- State after: `{alphaState=5.0, prevSample=5.1, initialized=true}`
- Output: `5.0`

**Example 3: Constant input after initialization**
- State before: `{alphaState=5.0, prevSample=5.1, initialized=true}`
- `update(5.1)` with `dt=0.01, alpha=0.5`
- Raw derivative: `(5.1 - 5.1) / 0.01 = 0`
- Alpha update: `(1-0.5)*5.0 + 0.5*0 = 2.5`
- State after: `{alphaState=2.5, prevSample=5.1, initialized=true}`
- Output: `2.5` (decaying toward 0)

---

## Key Properties to Verify Formally

1. **First-call identity**: `fdUpdate_first_call_state` — alpha state unchanged on first call.
2. **Always stores sample**: `fdUpdate_stores_prev_sample` — `prevSample = sample` after any call.
3. **Derivative formula**: `fdUpdate_second_call_deriv` — on initialized call, alpha update uses `(sample - prev)/dt`.
4. **Constant-input convergence formula**: `fdIter_const_alpha_formula` — with constant input, the alpha state after `n` steps equals `alphaIterate alphaState alpha 0 n` (exponential decay toward 0).
5. **No overshoot (positive start)**: `fdIter_const_bounded_pos` — alpha state stays in `[0, alphaState]` with constant input.
6. **Monotone decay**: `fdIter_const_shrinks_pos` — with constant input, successive alpha states are non-increasing (from positive start).
7. **Linear ramp derivative**: `fdUpdate_linear_deriv` — if sample increases by `m` each step, the derivative fed to the alpha filter is `m/dt`.

---

## Approximations / Out of Scope

- **Float arithmetic**: the model uses exact `Rat` arithmetic. NaN, ±∞, and
  IEEE 754 rounding are not modelled.
- **`FLT_EPSILON` guard**: the C++ code resets `_initialized = false` if
  `_sample_interval ≤ FLT_EPSILON`. This path is not modelled; the formal
  model takes `dt > 0` as a hard precondition.
- **`reset()` method**: not modelled — considered out of initial scope.
- **Alpha parameter derivation**: in C++, `alpha` is computed from `sample_interval`
  and `time_constant` inside `AlphaFilter::setParameters`. The model treats `alpha`
  as a direct input.

---

## Open Questions

1. **Reset semantics**: the `reset(sample)` method sets `_alpha_filter` to `sample`
   and `_initialized = false`. Should the formal model include this path? Currently it
   does not. The interaction between `reset()` and subsequent `update()` calls would
   be worth specifying if the filter is used in modes that reset frequently.

2. **Overflow**: for very large sample jumps, the derivative `(sample - prev) / dt`
   can be large. No clamping is applied to the derivative input. Is this by design?
   The alpha filter will eventually decay any large derivative state, but the transient
   could be significant.

3. **`sample_interval ≤ FLT_EPSILON` reset path**: the C++ code resets `_initialized`
   when `sample_interval` is too small. This guards against division by near-zero.
   The formal model abstracts this away; it might be worth adding a separate theorem
   showing that with `dt = 0`, the behavior degrades gracefully.
