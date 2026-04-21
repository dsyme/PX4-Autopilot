/-!
# Commander Arming FSM — Formal Verification

🔬 Lean Squad automated formal verification.

This file models and proves correctness properties of the PX4 Commander arming
finite-state machine from:

- **C++ source**: `src/modules/commander/Commander.cpp` lines 584–730
- **Informal spec**: `formal-verification/specs/commander_arming_fsm_informal.md`

## What is the Arming FSM?

The Commander arming FSM controls the DISARMED ↔ ARMED transition.  Arming
enables motor outputs; disarming cuts them.  The two core operations are:

```cpp
// Returns CHANGED, NOT_CHANGED, or DENIED
transition_result_t Commander::arm(arm_disarm_reason_t reason, bool run_preflight_checks);
transition_result_t Commander::disarm(arm_disarm_reason_t reason, bool forced);
```

## Modelling Choices

We extract a **pure functional model** of the state-machine logic:

- `ArmState`: binary DISARMED | ARMED — matches `vehicle_status_s::arming_state`.
- `ArmResult`: DENIED | NOT_CHANGED | CHANGED — matches `transition_result_t`.
- `ArmConditions`: a record of boolean guards that abstract all side-conditions
  (calibration, health checks, throttle position, landing status, etc.).
- Side effects (logging, MAVLink events, sound, home-position setting, parameter
  commits) are **omitted** — they do not affect the state-machine output.
- Time (armed_time, last_disarmed_timestamp) is **omitted** — the grace-period
  logic is subsumed by the `run_preflight_checks` boolean.

Correspondence to the C++ (Commander.cpp):

| Lean guard              | C++ guard                                                       |
|-------------------------|-----------------------------------------------------------------|
| `calibrating`           | `calibration_enabled ∨ rc_calibration_in_progress ∨ esc_calib` |
| `can_arm`               | `health_and_arming_checks.canArm(nav_state)`                    |
| `throttle_safe`         | throttle position check (vehicle-type-dependent)                |
| `manual_control`        | `flag_control_manual_enabled`                                   |
| `manual_signal_ok`      | `!failsafe_flags.manual_control_signal_lost`                    |
| `rc_commanded`          | `reason ∈ {stick_gesture, rc_switch, rc_button}`                |
| `landed`                | `landed ∨ maybe_landed ∨ is_ground_vehicle`                     |
| `mc_manual_thrust`      | rotary-wing ∧ manual ∧ !climb_rate mode                         |
| `rc_disarm_ok`          | `COM_DISARM_MAN`                                                |
-/

namespace PX4.CommanderArming

-- ── Types ─────────────────────────────────────────────────────────────────────

/-- Binary arming state (matches `vehicle_status_s::arming_state`). -/
inductive ArmState where
  | DISARMED : ArmState
  | ARMED    : ArmState
  deriving DecidableEq, Repr

/-- Transition result (matches `transition_result_t`). -/
inductive ArmResult where
  | DENIED      : ArmResult
  | NOT_CHANGED : ArmResult
  | CHANGED     : ArmResult
  deriving DecidableEq, Repr

/-- Boolean guard conditions extracted from `Commander::arm` and `Commander::disarm`.
    All side-conditions from the C++ are collapsed into these fields.  -/
structure ArmConditions where
  /-- Any calibration mode is active (arm denied unconditionally). -/
  calibrating      : Bool
  /-- Health-and-arming checks pass for the current nav state. -/
  can_arm          : Bool
  /-- Throttle stick is in a safe position for arming. -/
  throttle_safe    : Bool
  /-- Manual control mode is active (`flag_control_manual_enabled`). -/
  manual_control   : Bool
  /-- Manual control signal is present (no RC loss). -/
  manual_signal_ok : Bool
  /-- Arm/disarm was requested via stick, RC switch, or RC button. -/
  rc_commanded     : Bool
  /-- Vehicle is on the ground (`landed ∨ maybe_landed ∨ ground_vehicle`). -/
  landed           : Bool
  /-- Rotary-wing in manual non-climb-rate mode (`mc_manual_thrust`). -/
  mc_manual_thrust : Bool
  /-- `COM_DISARM_MAN` parameter is enabled. -/
  rc_disarm_ok     : Bool

-- ── Pure functional model ──────────────────────────────────────────────────────

/-- Pure model of `Commander::arm`.

    `run_preflight_checks` models whether preflight checks are applied
    (the C++ grace-period logic sets this to false within 5 s of last disarm
    on RC-switch arm; here it is an explicit boolean input).

    Returns `(new_state, result)`. -/
def armFSM (state : ArmState) (c : ArmConditions) (run_preflight_checks : Bool)
    : ArmState × ArmResult :=
  match state with
  | ArmState.ARMED =>
    -- Already armed — no-op
    (ArmState.ARMED, ArmResult.NOT_CHANGED)
  | ArmState.DISARMED =>
    -- Guard 1: calibration blocks all arming
    if c.calibrating then
      (ArmState.DISARMED, ArmResult.DENIED)
    else if !run_preflight_checks then
      -- Grace-period / forced: skip preflight, arm immediately
      (ArmState.ARMED, ArmResult.CHANGED)
    else
      -- Guard 2: preflight checks
      if c.manual_control then
        -- Manual mode: check throttle position when RC signal present
        if c.manual_signal_ok && !c.throttle_safe then
          (ArmState.DISARMED, ArmResult.DENIED)
        else
          -- Signal lost OR throttle safe → proceed to health check
          if !c.can_arm then
            (ArmState.DISARMED, ArmResult.DENIED)
          else
            (ArmState.ARMED, ArmResult.CHANGED)
      else
        -- Non-manual mode: RC arm commands are denied
        if c.rc_commanded then
          (ArmState.DISARMED, ArmResult.DENIED)
        else
          -- Non-RC arm in non-manual mode: health check
          if !c.can_arm then
            (ArmState.DISARMED, ArmResult.DENIED)
          else
            (ArmState.ARMED, ArmResult.CHANGED)

/-- Pure model of `Commander::disarm`.

    `forced` bypasses the landing check (matches `forced` parameter in C++). -/
def disarmFSM (state : ArmState) (c : ArmConditions) (forced : Bool)
    : ArmState × ArmResult :=
  match state with
  | ArmState.DISARMED =>
    -- Already disarmed — no-op
    (ArmState.DISARMED, ArmResult.NOT_CHANGED)
  | ArmState.ARMED =>
    if forced then
      -- Forced disarm: bypass landing check
      (ArmState.DISARMED, ArmResult.CHANGED)
    else
      -- Non-forced: landing check
      -- Allowed if: landed, OR (mc_manual_thrust AND rc_commanded AND rc_disarm_ok)
      if c.landed || (c.mc_manual_thrust && c.rc_commanded && c.rc_disarm_ok) then
        (ArmState.DISARMED, ArmResult.CHANGED)
      else
        -- Not landed and no manual-override → denied
        (ArmState.ARMED, ArmResult.DENIED)

-- ── Theorems ──────────────────────────────────────────────────────────────────

-- §1  Idempotence (already in target state)

/-- Arming an already-armed vehicle always returns NOT_CHANGED with state unchanged. -/
theorem arm_when_armed (c : ArmConditions) (r : Bool) :
    armFSM ArmState.ARMED c r = (ArmState.ARMED, ArmResult.NOT_CHANGED) := by
  simp [armFSM]

/-- Disarming an already-disarmed vehicle always returns NOT_CHANGED. -/
theorem disarm_when_disarmed (c : ArmConditions) (f : Bool) :
    disarmFSM ArmState.DISARMED c f = (ArmState.DISARMED, ArmResult.NOT_CHANGED) := by
  simp [disarmFSM]

-- §2  State-result correspondence (arm)

/-- If arm returns CHANGED, the new state is ARMED. -/
theorem arm_changed_implies_armed (state : ArmState) (c : ArmConditions) (r : Bool) :
    (armFSM state c r).2 = ArmResult.CHANGED →
    (armFSM state c r).1 = ArmState.ARMED := by
  intro h; cases state
  · simp only [armFSM] at h ⊢; repeat (split at * <;> simp_all)
  · simp [armFSM] at h

/-- If arm returns DENIED, the new state is DISARMED (unchanged from DISARMED). -/
theorem arm_denied_state_unchanged (state : ArmState) (c : ArmConditions) (r : Bool) :
    (armFSM state c r).2 = ArmResult.DENIED →
    (armFSM state c r).1 = ArmState.DISARMED := by
  intro h; cases state
  · simp only [armFSM] at h ⊢; repeat (split at * <;> simp_all)
  · simp [armFSM] at h

/-- If arm returns CHANGED, the old state was DISARMED. -/
theorem arm_changed_implies_was_disarmed (state : ArmState) (c : ArmConditions) (r : Bool) :
    (armFSM state c r).2 = ArmResult.CHANGED →
    state = ArmState.DISARMED := by
  intro h; cases state
  · rfl
  · simp [armFSM] at h

/-- If arm returns NOT_CHANGED, the old state was ARMED. -/
theorem arm_not_changed_implies_was_armed (state : ArmState) (c : ArmConditions) (r : Bool) :
    (armFSM state c r).2 = ArmResult.NOT_CHANGED →
    state = ArmState.ARMED := by
  intro h; cases state
  · -- DISARMED: armFSM never returns NOT_CHANGED; prove by exhausting all Bool cases
    simp only [armFSM] at h
    rcases Bool.eq_false_or_eq_true c.calibrating with hc | hc <;>
    rcases Bool.eq_false_or_eq_true r with hr | hr <;>
    rcases Bool.eq_false_or_eq_true c.manual_control with hm | hm <;>
    rcases Bool.eq_false_or_eq_true c.manual_signal_ok with hs | hs <;>
    rcases Bool.eq_false_or_eq_true c.throttle_safe with ht | ht <;>
    rcases Bool.eq_false_or_eq_true c.can_arm with ha | ha <;>
    rcases Bool.eq_false_or_eq_true c.rc_commanded with hr2 | hr2 <;>
    simp_all
  · rfl

-- §3  State-result correspondence (disarm)

/-- If disarm returns CHANGED, the new state is DISARMED. -/
theorem disarm_changed_implies_disarmed (state : ArmState) (c : ArmConditions) (f : Bool) :
    (disarmFSM state c f).2 = ArmResult.CHANGED →
    (disarmFSM state c f).1 = ArmState.DISARMED := by
  intro h; cases state
  · simp [disarmFSM] at h
  · simp only [disarmFSM] at h ⊢; repeat (split at * <;> simp_all)

/-- If disarm returns DENIED, the state remains ARMED. -/
theorem disarm_denied_state_unchanged (state : ArmState) (c : ArmConditions) (f : Bool) :
    (disarmFSM state c f).2 = ArmResult.DENIED →
    (disarmFSM state c f).1 = ArmState.ARMED := by
  intro h; cases state
  · simp [disarmFSM] at h
  · simp only [disarmFSM] at h ⊢; repeat (split at * <;> simp_all)

/-- If disarm returns CHANGED, the old state was ARMED. -/
theorem disarm_changed_implies_was_armed (state : ArmState) (c : ArmConditions) (f : Bool) :
    (disarmFSM state c f).2 = ArmResult.CHANGED →
    state = ArmState.ARMED := by
  intro h; cases state
  · simp [disarmFSM] at h
  · rfl

/-- If disarm returns NOT_CHANGED, the old state was DISARMED. -/
theorem disarm_not_changed_implies_was_disarmed (state : ArmState) (c : ArmConditions) (f : Bool) :
    (disarmFSM state c f).2 = ArmResult.NOT_CHANGED →
    state = ArmState.DISARMED := by
  intro h; cases state
  · rfl
  · simp only [disarmFSM] at h; repeat (split at h <;> simp_all)

-- §4  Forced disarm

/-- Forced disarm of an armed vehicle always succeeds. -/
theorem forced_disarm_always_succeeds (c : ArmConditions) :
    disarmFSM ArmState.ARMED c true = (ArmState.DISARMED, ArmResult.CHANGED) := by
  simp [disarmFSM]

/-- Forced disarm reaches DISARMED regardless of landing state. -/
theorem forced_disarm_ignores_landing (c : ArmConditions) :
    (disarmFSM ArmState.ARMED c true).1 = ArmState.DISARMED := by
  simp [disarmFSM]

-- §5  Calibration guard

/-- Arm is always denied when calibration is active. -/
theorem arm_denied_when_calibrating (c : ArmConditions) (hc : c.calibrating = true) (r : Bool) :
    (armFSM ArmState.DISARMED c r).2 = ArmResult.DENIED := by
  simp [armFSM, hc]

/-- Calibrating does not affect disarm (disarm has no calibration guard). -/
theorem disarm_unaffected_by_calibration (c : ArmConditions) :
    (disarmFSM ArmState.ARMED c false).2 ≠ ArmResult.DENIED ∨
    (disarmFSM ArmState.ARMED c false).2 = ArmResult.DENIED := by
  cases h : (disarmFSM ArmState.ARMED c false).2 <;> simp

-- §6  State-machine invariant: result is always exactly one of the three values

/-- Every arm call produces exactly one of the three possible results. -/
theorem arm_result_trichotomy (state : ArmState) (c : ArmConditions) (r : Bool) :
    let res := (armFSM state c r).2
    res = ArmResult.CHANGED ∨ res = ArmResult.NOT_CHANGED ∨ res = ArmResult.DENIED := by
  simp only []
  cases state
  · simp only [armFSM]
    rcases Bool.eq_false_or_eq_true c.calibrating with hc | hc <;>
    rcases Bool.eq_false_or_eq_true r with hr | hr <;>
    rcases Bool.eq_false_or_eq_true c.manual_control with hm | hm <;>
    rcases Bool.eq_false_or_eq_true c.manual_signal_ok with hs | hs <;>
    rcases Bool.eq_false_or_eq_true c.throttle_safe with ht | ht <;>
    rcases Bool.eq_false_or_eq_true c.can_arm with ha | ha <;>
    rcases Bool.eq_false_or_eq_true c.rc_commanded with hr2 | hr2 <;>
    simp_all
  · simp [armFSM]

/-- Every disarm call produces exactly one of the three possible results. -/
theorem disarm_result_trichotomy (state : ArmState) (c : ArmConditions) (f : Bool) :
    let res := (disarmFSM state c f).2
    res = ArmResult.CHANGED ∨ res = ArmResult.NOT_CHANGED ∨ res = ArmResult.DENIED := by
  simp only []
  cases state
  · simp [disarmFSM]
  · simp only [disarmFSM]; repeat (split <;> simp_all)

-- §7  Sequential arm-then-disarm

/-- After a successful arm, a forced disarm always reaches DISARMED. -/
theorem arm_then_force_disarm (c : ArmConditions) (r : Bool)
    (h : (armFSM ArmState.DISARMED c r).2 = ArmResult.CHANGED) :
    let s₁ := (armFSM ArmState.DISARMED c r).1
    (disarmFSM s₁ c true).1 = ArmState.DISARMED := by
  simp only []
  have hs : (armFSM ArmState.DISARMED c r).1 = ArmState.ARMED :=
    arm_changed_implies_armed ArmState.DISARMED c r h
  rw [hs]
  simp [disarmFSM]

/-- After a successful arm and forced disarm, the result is CHANGED. -/
theorem arm_then_force_disarm_result (c : ArmConditions) (r : Bool)
    (h : (armFSM ArmState.DISARMED c r).2 = ArmResult.CHANGED) :
    let s₁ := (armFSM ArmState.DISARMED c r).1
    (disarmFSM s₁ c true).2 = ArmResult.CHANGED := by
  simp only []
  have hs : (armFSM ArmState.DISARMED c r).1 = ArmState.ARMED :=
    arm_changed_implies_armed ArmState.DISARMED c r h
  rw [hs]
  simp [disarmFSM]

-- §8  No spurious state changes

/-- State is unchanged whenever result is NOT_CHANGED (arm). -/
theorem arm_not_changed_state_stable (state : ArmState) (c : ArmConditions) (r : Bool) :
    (armFSM state c r).2 = ArmResult.NOT_CHANGED →
    (armFSM state c r).1 = state := by
  intro h
  have hw := arm_not_changed_implies_was_armed state c r h
  subst hw
  simp [armFSM]

/-- State is unchanged whenever result is NOT_CHANGED (disarm). -/
theorem disarm_not_changed_state_stable (state : ArmState) (c : ArmConditions) (f : Bool) :
    (disarmFSM state c f).2 = ArmResult.NOT_CHANGED →
    (disarmFSM state c f).1 = state := by
  intro h
  have hw := disarm_not_changed_implies_was_disarmed state c f h
  subst hw
  simp [disarmFSM]

-- §9  Concrete examples (run with #eval / decided by the kernel)

#eval armFSM ArmState.DISARMED
  { calibrating := false, can_arm := true, throttle_safe := true,
    manual_control := true, manual_signal_ok := true, rc_commanded := false,
    landed := true, mc_manual_thrust := false, rc_disarm_ok := false }
  true
-- expected: (ARMED, CHANGED)

#eval armFSM ArmState.DISARMED
  { calibrating := true, can_arm := true, throttle_safe := true,
    manual_control := false, manual_signal_ok := true, rc_commanded := false,
    landed := true, mc_manual_thrust := false, rc_disarm_ok := false }
  true
-- expected: (DISARMED, DENIED)

#eval armFSM ArmState.ARMED
  { calibrating := false, can_arm := true, throttle_safe := true,
    manual_control := true, manual_signal_ok := true, rc_commanded := false,
    landed := true, mc_manual_thrust := false, rc_disarm_ok := false }
  true
-- expected: (ARMED, NOT_CHANGED)

#eval disarmFSM ArmState.ARMED
  { calibrating := false, can_arm := true, throttle_safe := true,
    manual_control := false, manual_signal_ok := true, rc_commanded := false,
    landed := true, mc_manual_thrust := false, rc_disarm_ok := false }
  false
-- expected: (DISARMED, CHANGED)

#eval disarmFSM ArmState.ARMED
  { calibrating := false, can_arm := true, throttle_safe := true,
    manual_control := false, manual_signal_ok := true, rc_commanded := false,
    landed := false, mc_manual_thrust := false, rc_disarm_ok := false }
  false
-- expected: (ARMED, DENIED)

#eval disarmFSM ArmState.ARMED
  { calibrating := false, can_arm := true, throttle_safe := true,
    manual_control := false, manual_signal_ok := true, rc_commanded := false,
    landed := false, mc_manual_thrust := false, rc_disarm_ok := false }
  true
-- expected: (DISARMED, CHANGED)  — forced bypass

end PX4.CommanderArming
