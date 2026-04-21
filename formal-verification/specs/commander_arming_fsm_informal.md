# Commander Arming FSM — Informal Specification

🔬 *Lean Squad automated formal verification.*

## Source

- **C++ source**: `src/modules/commander/Commander.cpp` lines 584–730
- **Header**: `src/modules/commander/Commander.hpp` lines 86–137

---

## Purpose

The Commander arming FSM controls the binary DISARMED ↔ ARMED transition of the
PX4 flight controller. Arming enables motor outputs; disarming cuts them.

The two central operations are:

- `arm(reason, run_preflight_checks)` → `transition_result_t`
- `disarm(reason, forced)` → `transition_result_t`

Both return one of three outcomes:

| Result              | Meaning                                      |
|---------------------|----------------------------------------------|
| `TRANSITION_CHANGED`     | Transition succeeded; arming state changed  |
| `TRANSITION_NOT_CHANGED` | Already in the target state; no-op          |
| `TRANSITION_DENIED`      | Preconditions not met; transition rejected  |

---

## State

The relevant arming state is `vehicle_status_s::arming_state`:

```
enum { ARMING_STATE_DISARMED, ARMING_STATE_ARMED }
```

Initial state (from `Commander::Commander()`): **DISARMED**.

---

## Preconditions and Postconditions

### `arm(reason, run_preflight_checks)`

**Preconditions for TRANSITION_NOT_CHANGED:**
- `isArmed()` is true (already armed)

**Preconditions for TRANSITION_DENIED:**
- Calibration in progress (`calibration_enabled || rc_calibration_in_progress || in_esc_calibration_mode`)
- *OR* (when `run_preflight_checks` is true):
  - Manual control mode AND manual signal present AND throttle NOT in safe position
  - *OR* RC arm command while not in manual mode
  - *OR* health-and-arming checks fail (`!canArm(nav_state)`)

**Postcondition for TRANSITION_CHANGED:**
- `arming_state = ARMING_STATE_ARMED`
- Old state was DISARMED
- `armed_time` set to current time

**Key invariant**: if `arm()` returns `TRANSITION_CHANGED`, the new state is `ARMED`.  
If it returns `TRANSITION_DENIED` or `TRANSITION_NOT_CHANGED`, the state is **unchanged**.

---

### `disarm(reason, forced)`

**Preconditions for TRANSITION_NOT_CHANGED:**
- `!isArmed()` (already disarmed)

**Preconditions for TRANSITION_DENIED (only when `forced = false`):**
- Not landed (landed = `vehicle_land_detected.landed || maybe_landed || is_ground_vehicle`)
- AND NOT (MC manual thrust mode AND commanded by RC AND `COM_DISARM_MAN` enabled)

**Postcondition for TRANSITION_CHANGED:**
- `arming_state = ARMING_STATE_DISARMED`
- Old state was ARMED
- `armed_time` reset to 0

**Key invariant**: if `disarm()` returns `TRANSITION_CHANGED`, the new state is `DISARMED`.

---

## Invariants

1. **Binary state**: `arming_state ∈ {DISARMED, ARMED}` always holds.
2. **Idempotence of arm**: calling `arm()` on an already-armed vehicle always returns
   `TRANSITION_NOT_CHANGED` and leaves state unchanged.
3. **Idempotence of disarm**: calling `disarm()` on an already-disarmed vehicle always
   returns `TRANSITION_NOT_CHANGED` and leaves state unchanged.
4. **No state change on DENIED/NOT_CHANGED**: arming state is only modified when the
   result is `TRANSITION_CHANGED`.
5. **Result → state correspondence**:
   - `arm()` returns `CHANGED` ⟹ new state is ARMED and old state was DISARMED
   - `disarm()` returns `CHANGED` ⟹ new state is DISARMED and old state was ARMED
6. **Forced disarm always succeeds**: `disarm(reason, forced=true)` on an armed vehicle
   always returns `TRANSITION_CHANGED`.

---

## Edge Cases

- **arm() when already armed**: returns `NOT_CHANGED` immediately; no side effects.
- **disarm() when already disarmed**: returns `NOT_CHANGED` immediately; no side effects.
- **Forced disarm skips landing check**: `forced=true` bypasses the "not landed" guard.
- **Grace period re-arm**: when re-arming via RC switch within 5 s of last disarm,
  preflight checks are skipped (a partial safety relaxation). This is modelled by
  abstracting `run_preflight_checks` as a boolean input.

---

## Modelling Approach

The pure functional Lean model:
- Abstracts `arming_state` as `ArmState : DISARMED | ARMED`.
- Abstracts `transition_result_t` as `ArmResult : DENIED | NOT_CHANGED | CHANGED`.
- Captures all guard conditions in a record `ArmConditions` with boolean fields:
  - `calibrating`: any calibration mode active
  - `can_arm`: health-and-arming checks pass
  - `throttle_safe`: throttle position safe for arming
  - `manual_control`: manual control mode active
  - `manual_signal_ok`: RC signal present in manual mode
  - `rc_commanded`: arm request came from stick/switch/button
  - `landed`: vehicle is landed or on ground
  - `mc_manual_thrust`: rotary-wing in manual non-climb-rate mode
  - `rc_disarm_ok`: `COM_DISARM_MAN` enabled
- Side effects (logging, sound, parameter saves, home position) are omitted.
- Time (armed_time, last_disarmed_timestamp) is omitted from the pure state model.

---

## Examples

| Current state | Call | Conditions | Result | New state |
|---|---|---|---|---|
| DISARMED | arm(_, true) | no calibration, canArm, throttle safe | CHANGED | ARMED |
| ARMED | arm(_, _) | any | NOT_CHANGED | ARMED |
| DISARMED | arm(_, _) | calibrating | DENIED | DISARMED |
| ARMED | disarm(_, false) | landed | CHANGED | DISARMED |
| ARMED | disarm(_, true) | not landed | CHANGED | DISARMED |
| DISARMED | disarm(_, _) | any | NOT_CHANGED | DISARMED |
| ARMED | disarm(_, false) | not landed, not MC manual | DENIED | ARMED |

---

## Open Questions

1. Is the "grace period" for re-arm (5 s after disarm skip preflight) a security concern?
   Maintainer input welcome.
2. Should `canArm` checking be modelled before or after throttle-safe checking in the
   spec? (In code, throttle is checked first.)
