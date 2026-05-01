# Informal Specification: `VelocitySmoothing::computeT2` (simple) and `computeT3`

🔬 Lean Squad automated formal verification.

- **C++ source**: `src/lib/motion_planning/VelocitySmoothing.cpp`, lines 143–162
- **Target IDs**: #41 (`computeT3`), #43 (`computeT2` simple overload)

---

## Context

`VelocitySmoothing` implements a jerk-limited velocity trajectory planner. A
trajectory is divided into three phases, each of duration T1, T2, T3:

- **Phase 1 (T1)**: constant positive jerk `+j_max` — acceleration ramps up
- **Phase 2 (T2)**: zero jerk — cruising at constant acceleration
- **Phase 3 (T3)**: constant negative jerk `−j_max` — acceleration ramps back to zero

The durations must be non-negative. Two helper functions compute T2 and T3.

---

## `computeT3(T1, a0, j_max)`

### C++ Source

```cpp
float VelocitySmoothing::computeT3(float T1, float a0, float j_max) const
{
    float T3 = a0 / j_max + T1;
    return math::max(T3, 0.f);
}
```

### Purpose

Computes the duration of phase 3 (deceleration phase). T3 is determined by
how long it takes to bring the acceleration from its current value `a0` back
to zero at jerk rate `j_max`, plus the time T1 already accumulated in phase 1.
The result is clamped to zero from below (negative durations are not physical).

### Preconditions

- `j_max > 0` (positive jerk limit; the divisor must be non-zero)
- `T1 ≥ 0` (phase 1 duration is non-negative in practice)
- `a0` can be any real (current acceleration, possibly negative)

### Postconditions

- **Result ≥ 0**: `computeT3(T1, a0, j_max) ≥ 0`
- **Value when sum non-negative**: if `a0/j_max + T1 ≥ 0` then result = `a0/j_max + T1`
- **Value when sum negative**: if `a0/j_max + T1 < 0` then result = 0

### Key Properties

1. **Non-negativity**: the result is always ≥ 0 (clamping guarantee).
2. **Monotone in T1**: increasing T1 cannot decrease T3.
3. **Monotone in a0 (when j_max > 0)**: a higher initial acceleration requires
   a longer deceleration phase.
4. **Scale identity (when j_max > 0)**:
   `j_max * computeT3(T1, a0, j_max) = max(a0 + j_max * T1, 0)`
   — multiplying out the division gives a clean integer-style identity.
5. **Zero input**: `computeT3(0, 0, j_max) = 0` for any `j_max ≠ 0`.
6. **Lower bound by T1 (when a0 ≥ 0, j_max > 0)**: `T1 ≤ computeT3(T1, a0, j_max)`.

### Edge Cases

- `a0/j_max + T1 = 0`: result is 0 (boundary of clamping).
- `a0 < 0`: deceleration may already be negative, T3 can be 0.
- `j_max = 0`: physically undefined; the Lean model uses Rat division (returns 0 when jMax = 0), avoiding undefined behaviour.

### Inferred Intent

The function represents: given we entered phase 1 with initial acceleration `a0`
and applied jerk `j_max` for duration T1, how long does phase 3 need to be to
cancel the resulting acceleration? The formula `a0/j_max + T1` is the total time
to zero out the acceleration ignoring phase 2 (which is at constant acceleration).
The clamp ensures non-negative output even if the trajectory is over-actuated.

---

## `computeT2(T123, T1, T3)` — simple overload

### C++ Source

```cpp
float VelocitySmoothing::computeT2(float T123, float T1, float T3) const
{
    float T2 = T123 - T1 - T3;
    return math::max(T2, 0.f);
}
```

### Purpose

Computes the duration of the coasting phase (phase 2) given that the total
trajectory duration has been fixed at `T123`. T2 is whatever time remains after
allocating T1 and T3, clamped to zero from below.

### Preconditions

- `T1 ≥ 0`, `T3 ≥ 0`, `T123 ≥ 0` in typical use
- No division; all inputs are plain durations

### Postconditions

- **Result ≥ 0**: `computeT2(T123, T1, T3) ≥ 0`
- **Value when fits**: if `T1 + T3 ≤ T123` then result = `T123 − T1 − T3`
- **Value when exceeds**: if `T123 < T1 + T3` then result = 0

### Key Properties

1. **Non-negativity**: the result is always ≥ 0.
2. **Partition identity**: `computeT2(T123, T1, T3) + T1 + T3 = max(T123, T1 + T3)`.
   The total time consumed equals the larger of `T123` and `T1 + T3`.
3. **Exact-fit**: `computeT2(T1 + T3, T1, T3) = 0` — if T123 equals T1 + T3, no
   coasting phase is needed.
4. **Monotone in T123**: increasing the total duration cannot decrease T2.
5. **Anti-monotone in T1**: a longer phase 1 leaves less room for phase 2.
6. **Anti-monotone in T3**: a longer phase 3 leaves less room for phase 2.
7. **Commutativity in T1/T3**: `computeT2(T123, T1, T3) = computeT2(T123, T3, T1)`.
8. **Upper bound**: `computeT2(T123, T1, T3) ≤ T123`.

### Edge Cases

- `T1 + T3 = T123`: result is exactly 0.
- `T1 + T3 > T123`: the available time is insufficient; T2 is clamped to 0.
  The planner handles this by adjusting T123 in an outer loop.
- All-zero inputs: `computeT2(0, 0, 0) = 0`.

### Open Questions

- In what circumstances does the planner call this overload vs the longer
  `computeT2(T1, T3, a0, v3, j_max)` overload? The simple overload is used
  when T123 is already computed externally (fixed-time mode).

---

## Examples

### `computeT3`

| T1   | a0  | j_max | Expected T3 | Notes                      |
|------|-----|-------|-------------|----------------------------|
| 1.0  | 2.0 | 4.0   | 1.5         | 2/4 + 1 = 1.5              |
| 0.0  | 0.0 | 5.0   | 0.0         | 0/5 + 0 = 0                |
| 0.5  | -4.0| 2.0   | 0.0         | −4/2 + 0.5 = −1.5 → clamp 0|
| 0.5  | 2.0 | 1.0   | 2.5         | 2/1 + 0.5 = 2.5            |

### `computeT2`

| T123 | T1  | T3  | Expected T2 | Notes                        |
|------|-----|-----|-------------|------------------------------|
| 5.0  | 1.0 | 1.5 | 2.5         | 5 − 1 − 1.5 = 2.5           |
| 3.0  | 2.0 | 2.0 | 0.0         | 3 < 4 → clamp 0             |
| 4.0  | 2.0 | 2.0 | 0.0         | 4 = 4 → exactly 0           |
| 0.0  | 0.0 | 0.0 | 0.0         | 0 − 0 − 0 = 0               |
