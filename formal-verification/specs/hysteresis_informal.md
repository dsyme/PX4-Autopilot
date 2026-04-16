# Informal Specification: `systemlib::Hysteresis`

**Source**: `src/lib/hysteresis/hysteresis.h` and `src/lib/hysteresis/hysteresis.cpp`

---

## Purpose

`Hysteresis` is a **time-delayed boolean state machine** used throughout PX4 to prevent
rapid toggling of safety-critical states. It wraps a boolean value and ensures that
transitions from `false→true` and `true→false` are only committed after a configurable
dwell time has elapsed.

Typical uses include:
- Arming/disarming delay (must hold arm command for N milliseconds)
- Flight mode transition settling delay
- Sensor validity debouncing

---

## State

A `Hysteresis` object has four pieces of internal state:

| Field | Type | Description |
|-------|------|-------------|
| `_state` | `bool` | The **committed** current state (externally visible via `get_state()`) |
| `_requested_state` | `bool` | The **pending** state (set by the most recent call to `set_state_and_update`) |
| `_time_from_true_us` | `uint64_t` (µs) | Dwell time required before a `true→false` transition commits |
| `_time_from_false_us` | `uint64_t` (µs) | Dwell time required before a `false→true` transition commits |
| `_last_time_to_change_state` | `uint64_t` (µs) | Timestamp (µs) when the most recent request to change state was first made |

---

## Operations

### `Hysteresis(bool initial_state)` — Constructor

**Preconditions**: none  
**Postconditions**:
- `_state = _requested_state = initial_state`
- `_time_from_true_us = _time_from_false_us = 0`
- `_last_time_to_change_state = 0`

When both delays are zero, every `update` call immediately commits any pending request.

---

### `set_hysteresis_time_from(bool from_state, hrt_abstime delay_us)`

Sets the dwell time for transitions **away from** `from_state`.

**Preconditions**: `delay_us ≥ 0`  
**Postconditions**:
- If `from_state == true`: `_time_from_true_us = delay_us`
- If `from_state == false`: `_time_from_false_us = delay_us`
- `_state`, `_requested_state`, and `_last_time_to_change_state` are unchanged

**Examples**:
- `set_hysteresis_time_from(true, 500000)` → must hold `false` request for 500 ms before leaving `true`
- `set_hysteresis_time_from(false, 200000)` → must hold `true` request for 200 ms before leaving `false`

---

### `set_state_and_update(bool new_state, hrt_abstime now_us)`

Requests a state change and immediately evaluates whether the committed state should be updated.

**Preconditions**: `now_us` is a monotonically non-decreasing timestamp in microseconds

**Behaviour**:

1. If `new_state == _state` (request agrees with committed state):
   - Set `_requested_state = _state` (cancel any pending request)
   - Equivalent to "settling" — the request is withdrawn.
2. If `new_state != _state` and `new_state != _requested_state` (new direction of request):
   - Set `_requested_state = new_state`
   - Set `_last_time_to_change_state = now_us` (reset the timer)
3. If `new_state != _state` and `new_state == _requested_state` (same direction, timer already running):
   - Leave `_requested_state` and `_last_time_to_change_state` unchanged
4. In all cases, call `update(now_us)` — which may commit the state if the dwell time has elapsed.

**Postconditions** (overall, after `update` runs):
- If `new_state == old_state`: `_state` is unchanged
- If the dwell timer has expired: `_state = _requested_state`
- If the dwell timer has not expired: `_state` is unchanged from its value before the call

---

### `update(hrt_abstime now_us)`

Checks whether a pending state transition should be committed.

**Preconditions**: `now_us` is a monotonically non-decreasing timestamp in microseconds

**Behaviour** (pure evaluation, no timer reset):

1. If `_requested_state == _state`: do nothing (no pending change).
2. If `_state == true` and `_requested_state == false` (pending `true→false`):
   - If `now_us >= _last_time_to_change_state + _time_from_true_us`: set `_state = false`
3. If `_state == false` and `_requested_state == true` (pending `false→true`):
   - If `now_us >= _last_time_to_change_state + _time_from_false_us`: set `_state = true`

**Postconditions**:
- `_state` may change to match `_requested_state` iff the dwell time is satisfied
- `_requested_state` is never modified by `update`
- `_last_time_to_change_state` is never modified by `update`

---

## Key Invariants

### Invariant 1 — Settled state
> When `_requested_state == _state`, calling `update` is a no-op on `_state`.

### Invariant 2 — Delay lower bound
> `_state` can only change from `s` to `¬s` if at least `delay(s)` microseconds have elapsed since the first request to leave `s`. Formally, if `_state` changes in `update(now_us)`, then `now_us ≥ _last_time_to_change_state + delay(_state)`.

### Invariant 3 — No spurious transitions
> `_state` never changes unless `_requested_state ≠ _state`. A call to `update` with `_requested_state = _state` is always a no-op.

### Invariant 4 — Zero-delay immediate commitment
> When the relevant dwell time is 0, every call to `set_state_and_update(new_state, t)` with `new_state ≠ _state` will immediately commit: `_state = new_state` after the call.

### Invariant 5 — Monotone timer satisfaction
> If the dwell condition was not satisfied at time `t`, it may become satisfied at any time `t' ≥ t`. Once satisfied, calling `update(t'')` for any `t'' ≥ t` will commit the transition.

### Invariant 6 — Request cancellation
> If `set_state_and_update(s, t)` is called when `_state == s`, the pending request is cancelled: `_requested_state = s`. A subsequent `update` will see no pending change.

---

## Edge Cases

| Scenario | Expected behaviour |
|----------|--------------------|
| Zero dwell time (both from true and from false = 0) | State commits immediately on each `set_state_and_update` or `update` call |
| Timer overflow: `_last_time_to_change_state + delay` wraps | **Open question** — `hrt_abstime` is `uint64_t`; the condition `now >= last + delay` uses unsigned arithmetic, which is well-defined but wraps after ~585,000 years. In practice not a concern, but should be noted. |
| `now_us < _last_time_to_change_state` (non-monotonic clock) | The condition `now_us >= last + delay` may evaluate false, causing the transition to stall indefinitely. Not guarded against by the implementation. |
| Rapid alternation: call `set_state_and_update(true, t)` then `set_state_and_update(false, t)` | Second call sets `_requested_state = false` (same as `_state`), effectively cancelling the first request with no timer start. |
| `set_state_and_update` called multiple times with same `new_state ≠ _state` | After the first call, `_last_time_to_change_state` is set; subsequent calls with the same direction do not reset the timer. |

---

## Concrete Examples

### Example 1 — Immediate transition (zero dwell)
```
init(false), delays = (0, 0)
set_state_and_update(true, t=100)  → _state = true  (timer = 0 → immediate)
set_state_and_update(false, t=200) → _state = false
```

### Example 2 — Delayed true→false transition (500 µs dwell from true)
```
init(true), time_from_true = 500
set_state_and_update(false, t=100) → _last = 100, _requested = false, _state = true (not yet)
update(t=500)                       → _state = true  (500 - 100 = 400 < 500)
update(t=601)                       → _state = false (601 - 100 = 501 ≥ 500)
```

### Example 3 — Request cancellation
```
init(false), time_from_false = 1000
set_state_and_update(true, t=0)    → _requested = true, _last = 0, _state = false
set_state_and_update(false, t=500) → _requested = false (cancelled, same as _state)
update(t=2000)                     → _state = false (no pending change)
```

### Example 4 — Timer restart on direction change
```
init(false), time_from_false = 1000
set_state_and_update(true, t=0)    → _requested = true, _last = 0
set_state_and_update(false, t=500) → cancels (_requested = false)
set_state_and_update(true, t=600)  → _requested = true, _last = 600 (timer RESTARTED)
update(t=1500)                     → _state = false (1500 - 600 = 900 < 1000)
update(t=1601)                     → _state = true  (1601 - 600 = 1001 ≥ 1000)
```

---

## Inferred Intent

The hysteresis is designed to prevent "bouncing" — rapid oscillation between states in
response to noisy or unstable inputs. By requiring a sustained request for a minimum
duration before committing, it filters out glitches and provides stability guarantees
for downstream consumers (e.g., the arming state machine, flight mode manager).

The asymmetric delays (separate `_time_from_true_us` and `_time_from_false_us`) allow
different settling times for arming vs disarming, or for mode-enter vs mode-exit
transitions. This is a common pattern in embedded control systems.

---

## Open Questions

1. **Non-monotonic time**: Should the implementation guard against `now_us < _last_time_to_change_state`? A backwards clock would stall the hysteresis indefinitely.
2. **Initial delay race**: If `_last_time_to_change_state = 0` (never set) and the delay is also `0`, the condition `now >= 0 + 0 = 0` is always true, which means `update` will commit instantly. Is this intentional?
3. **Thread safety**: Are `set_state_and_update` and `update` expected to be called from a single thread, or is locking required? The implementation has no synchronization.

---

## Lean Modelling Approach

**Model**: Abstract the timestamp as a `Nat` (natural number, representing microseconds).
Represent state as a record:
```
structure HysteresisState where
  state : Bool
  requested : Bool
  lastChange : Nat
  delayFromTrue : Nat
  delayFromFalse : Nat
```

Key theorems to prove:
- `update_noop`: if `state = requested`, `update` returns unchanged state
- `update_delay_lb`: if `update` changes state, `now ≥ lastChange + delay(state)`
- `update_commits`: if `now ≥ lastChange + delay(requested)` and `state ≠ requested`, `update` changes state
- `set_state_cancel`: if `new = state`, `set_state_and_update new t` produces `requested = state`
- `set_state_zero_delay_commits`: if delay = 0 and `new ≠ state`, `set_state_and_update new t` commits immediately

All properties are decidable over `Bool` and `Nat`, so `decide` and `omega` should close most goals.

🔬 *Generated by Lean Squad automated formal verification.*
