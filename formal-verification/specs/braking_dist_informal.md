# Informal Specification: computeBrakingDistanceFromVelocity

🔬 *Lean Squad automated formal verification.*

## Source

`src/lib/mathlib/math/TrajMath.hpp`, line 107:

```cpp
/* Compute the braking distance given a maximum acceleration, maximum jerk and a maximum delay acceleration.
 * We assume a constant acceleration profile with a delay of accel_delay_max/jerk
 * (time to reach the desired acceleration from opposite max acceleration)
 * Equation to solve: vel_final^2 = vel_initial^2 - 2*accel*(x - vel_initial*2*accel/jerk)
 *
 * @param velocity initial velocity
 * @param jerk maximum jerk
 * @param accel maximum target acceleration during the braking maneuver
 * @param accel_delay_max the acceleration defining the delay described above
 *
 * @return braking distance
 */
inline float computeBrakingDistanceFromVelocity(const float velocity, const float jerk, const float accel,
        const float accel_delay_max)
{
    return velocity * (velocity / (2.0f * accel) + accel_delay_max / jerk);
}
```

## Purpose

Computes the horizontal braking distance required to stop a multirotor vehicle
starting from a given velocity, using a jerk-limited acceleration profile with a
delay phase. Used in geofence breach avoidance and waypoint arrival calculations.

## Callers and Intended Usage

- `navigator_main.cpp` line 1628: called with `velocity_hor_abs = sqrt(vx² + vy²)`, which
  is always ≥ 0. Parameters `_param_mpc_jerk_auto > 0`, `_param_mpc_acc_hor > 0`,
  `accel_delay_max = 0.6 * jerk > 0`.
- The result is used as a forward distance to compute a safe waypoint, so it must be
  non-negative to avoid sending the vehicle backwards.

## Parameters

| Parameter | Symbol | Physical meaning | Expected range |
|-----------|--------|------------------|---------------|
| `velocity` | v | Initial speed (m/s) | ≥ 0 |
| `jerk` | j | Maximum jerk (m/s³) | > 0 |
| `accel` | a | Maximum target acceleration (m/s²) | > 0 |
| `accel_delay_max` | d | Acceleration defining delay phase (m/s²) | ≥ 0 |

## Formula

The formula derives from the kinematic equation:

```
v_f² = v_i² - 2 · a · (Δx - v_i · delay_time)
```

where `delay_time = d / j` and `v_f = 0` (stopping condition). Solving for Δx:

```
dist = v² / (2a) + v · d/j
     = v · (v/(2a) + d/j)
```

This is the C++ formula.

## Preconditions

- `velocity ≥ 0` (the caller always passes `velocity_hor_abs`, a Euclidean norm)
- `jerk > 0` (parameter constraint; division by zero otherwise)
- `accel > 0` (parameter constraint; division by zero otherwise)
- `accel_delay_max ≥ 0` (physically: acceleration ≥ 0)

## Postconditions

- `dist ≥ 0`: braking distance is non-negative for valid inputs
- `dist = 0` when `velocity = 0`: no movement → no braking distance
- `dist > 0` when `velocity > 0`, `accel > 0`, `jerk > 0`, `accel_delay_max ≥ 0`

## Key Properties

1. **Non-negativity**: `v ≥ 0, a > 0, j > 0, d ≥ 0 → dist ≥ 0`
2. **Zero velocity → zero distance**: `dist(0, a, j, d) = 0`
3. **Strict positivity**: `v > 0, a > 0, j > 0, d ≥ 0 → dist > 0`
4. **Monotone in velocity**: `v₁ ≤ v₂ (both ≥ 0) → dist(v₁) ≤ dist(v₂)` for fixed a, j, d
5. **No-delay formula**: `d = 0 → dist = v²/(2a)` (classic kinematics under constant decel)
6. **Quadratic term dominates**: for fixed a, j, d, the v² term grows faster than the v term

## Invariants / Algebraic Properties

- Equivalent form: `dist = v²/(2a) + v·d/j` (expand multiplication)
- Scaling: `dist(k·v) = k²·v²/(2a) + k·v·d/j ≠ k·dist(v)` (super-linear in v)
- `dist(2v, a, j, 0) = 4 · dist(v, a, j, 0)`: quadratic scaling when d=0

## Edge Cases

- `velocity = 0`: returns 0 (correct — no braking needed)
- `velocity < 0`: returns a negative value (no check in C++; callers ensure v ≥ 0)
- `accel = 0`: **undefined** — division by zero in C++ (UB); callers must ensure a > 0
- `jerk = 0`: **undefined** — division by zero in C++ (UB); callers must ensure j > 0
- Large velocities: quadratic term dominates, no overflow check in C++ for `float`

## Open Questions

1. Should the function clamp `velocity` to ≥ 0? Currently relies on caller contract.
2. Is there a parameter validation guard anywhere for `accel > 0` and `jerk > 0`?
   (Not visible from the call sites — parameter system presumably enforces this.)
3. The delay model assumes the vehicle starts at maximum negative acceleration.
   Is this a conservative or optimistic estimate of braking distance?
