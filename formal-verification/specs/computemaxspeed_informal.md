# Informal Specification: `math::trajectory::computeMaxSpeedFromDistance`

🔬 *Lean Squad automated formal verification.*

**Source**: `src/lib/mathlib/math/TrajMath.hpp` (lines ~48–64)
**Namespace**: `math::trajectory`

---

## Purpose

`computeMaxSpeedFromDistance` computes the **maximum initial speed** at which a vehicle
can begin a braking manoeuvre and still arrive at a target point with speed `final_speed`
within a given `braking_distance`.

The model assumes a **constant deceleration** profile with a **jerk-limited ramp delay**:
the vehicle cannot instantly apply maximum deceleration; it must ramp from its current
acceleration to the maximum deceleration over a delay of `2 * accel / jerk` seconds.

The underlying kinematic equation is:

```
v_f² = v₀² − 2·a·(d − v₀·2·a/j)
```

where:
- `v₀` = initial (maximum) speed (the unknown to solve for)
- `v_f` = `final_speed`
- `a` = `accel` (maximum deceleration magnitude)
- `j` = `jerk` (maximum jerk)
- `d` = `braking_distance`

Solving for `v₀` using the quadratic formula:

```
v₀² + v₀·(4a²/j) − 2·a·d − v_f² = 0

b = 4a²/j
c = −2a·d − v_f²

v₀ = 0.5 · (−b + √(b² − 4c))
   = 0.5 · (−4a²/j + √((4a²/j)² + 4·(2·a·d + v_f²)))
```

The discriminant `b² − 4c = b² + 4·(2·a·d + v_f²)` is always ≥ 0 when `a, d ≥ 0`.

The result is clamped to `max(v₀, final_speed)` so the function never returns a speed
lower than `final_speed` even when the conservative delay model over-estimates the
required braking room.

---

## C++ Implementation

```cpp
float computeMaxSpeedFromDistance(float jerk, float accel, float braking_distance, float final_speed)
{
    auto sqr = [](float f) { return f * f; };
    float b = 4.0f * sqr(accel) / jerk;
    float c = -2.0f * accel * braking_distance - sqr(final_speed);
    float max_speed = 0.5f * (-b + sqrtf(sqr(b) - 4.0f * c));
    return fmaxf(max_speed, final_speed);
}
```

---

## Parameters

| Parameter | Type | Meaning |
|-----------|------|---------|
| `jerk` | `float > 0` | Maximum jerk (rate of change of acceleration), m/s³ |
| `accel` | `float ≥ 0` | Maximum deceleration magnitude, m/s² |
| `braking_distance` | `float ≥ 0` | Distance available for braking, m |
| `final_speed` | `float ≥ 0` | Required speed at end of braking, m/s |

---

## Preconditions

1. `jerk > 0` — division by zero otherwise; physically, zero jerk means no ramp delay exists
2. `accel ≥ 0` — deceleration magnitude is non-negative
3. `braking_distance ≥ 0` — distance is non-negative
4. `final_speed ≥ 0` — final speed is non-negative (physical constraint)

Under these preconditions, the discriminant `b² − 4c ≥ 0`, so `sqrt` is well-defined.

---

## Postconditions

1. **Return value ≥ final_speed**: `result ≥ final_speed` always (enforced by `fmaxf`)
2. **Non-negativity**: `result ≥ 0` (follows from result ≥ final_speed ≥ 0)
3. **Monotone in braking_distance**: larger `braking_distance` allows higher initial speed.
   More room to brake → higher max speed. Formally: `d1 ≤ d2 → result(d1) ≤ result(d2)`.
4. **Monotone in final_speed**: larger `final_speed` → larger result. Formally:
   `vf1 ≤ vf2 → result(vf1) ≤ result(vf2)`.
5. **Zero braking distance**: when `braking_distance = 0`, the formula gives
   `max_speed = 0.5 * (-b + sqrt(b² + 4*vf²))`, which may be less than `final_speed`
   depending on parameters; the `fmaxf` clamp ensures `result = final_speed`.
6. **Zero accel**: when `accel = 0`, `b = 0` and `c = -vf²`, so
   `max_speed = 0.5 * sqrt(4*vf²) = vf`, and `result = final_speed`.
7. **Quadratic relationship**: `result` grows roughly as `√(braking_distance)` for large
   `braking_distance` and fixed other parameters.

---

## Invariants

- **Kinematic consistency** (informal): the result is the largest initial speed `v₀ ≥ final_speed`
  such that the vehicle, using at most `accel` deceleration with at most `jerk` ramp,
  can reach `final_speed` within `braking_distance`.
- **Lower bound**: `result ≥ final_speed` always.
- **Discriminant non-negativity**: `b² - 4c = (4a²/j)² + 4·(2·a·d + vf²) ≥ 0` when `a, d ≥ 0`.

---

## Edge Cases

| Scenario | Behaviour |
|----------|-----------|
| `accel = 0` | `b = 0`, `c = -vf²`, `max_speed = vf`; result = `final_speed` |
| `braking_distance = 0` | No room; formula may yield `max_speed < final_speed`; clamped to `final_speed` |
| `final_speed = 0` | Stop completely; result is purely a function of `accel`, `jerk`, `distance` |
| `jerk → ∞` | `b → 0`; delay disappears; result → `sqrt(2·accel·distance + vf²)` (ideal braking) |
| Large `braking_distance` | `max_speed ≈ sqrt(2·accel·d)` for large `d` |

---

## Examples

### Example 1: typical parameters
```
jerk = 8, accel = 4, braking_distance = 10, final_speed = 0
b = 4 * 16 / 8 = 8
c = -2 * 4 * 10 - 0 = -80
discriminant = 64 - 4*(-80) = 64 + 320 = 384
max_speed = 0.5 * (-8 + sqrt(384)) ≈ 0.5 * (-8 + 19.6) ≈ 5.8 m/s
result = max(5.8, 0) = 5.8
```

### Example 2: zero acceleration
```
jerk = 8, accel = 0, braking_distance = 10, final_speed = 5
b = 0, c = -25
max_speed = 0.5 * sqrt(100) = 5
result = max(5, 5) = 5 (= final_speed, as expected)
```

### Example 3: large final_speed dominates
```
jerk = 8, accel = 4, braking_distance = 1, final_speed = 20
max_speed formula likely gives < 20 (small distance, large desired end speed)
result = max(max_speed, 20) = 20 (clamped to final_speed)
```

---

## Inferred Intent

The function is used by the PX4 velocity smoother to determine whether a waypoint
can be approached at a given speed without violating kinematic constraints. The
`fmaxf(max_speed, final_speed)` guard prevents the function from "helpfully" suggesting
a speed lower than the target, which could cause unnecessary deceleration.

The 2·accel/jerk delay model is an approximation; it assumes the vehicle transitions
directly from maximum forward acceleration to maximum braking. In practice this is
conservative (actual braking capability is often higher).

---

## Open Questions

1. Is `jerk > 0` enforced by the caller, or could jerk = 0 happen? (Division by zero risk.)
2. Should `accel = 0` be treated as a degenerate case requiring a guard?
3. The comment says "delay of 2*accel/jerk" but the code uses `b = 4*accel²/jerk` which
   comes from the full kinematic derivation, not directly from the delay. The mapping from
   delay to `b` should be verified carefully.

---

## Lean Modelling Plan

Specialise to **rational arithmetic** to avoid floating-point. The key properties to
prove are algebraic:

```lean
-- Input parameters (all rational, with positivity assumptions)
def maxSpeedFromDist (j a d vf : Rat) : Rat :=
  let b := 4 * a^2 / j
  let c := -2 * a * d - vf^2
  -- discriminant = b^2 - 4*c = b^2 + 4*(2*a*d + vf^2) ≥ 0
  -- For Rat we'd need sqrt; instead prove properties algebraically
  -- or use the squared equation: max_speed^2 + b*max_speed + c = 0
  ...
```

**Challenge**: the square root makes exact rational modelling non-trivial.
Possible approaches:
1. **Algebraic identity proofs**: prove that the returned `max_speed` satisfies the
   quadratic equation (substituting back). Prove non-negativity and monotonicity
   as abstract properties of the formula.
2. **Abstract model with sqrt**: use `Real.sqrt` from Mathlib.
3. **Focus on structural properties**: `result ≥ final_speed`, monotone in `d`,
   monotone in `vf`, and the `accel = 0` special case — these don't require sqrt.

**Priority properties** (provable without sqrt in most cases):
- `computeMaxSpeed_ge_final_speed`: `result ≥ final_speed` (from the `max` construction)
- `computeMaxSpeed_accel_zero`: when `accel = 0`, `result = final_speed`
- `discriminant_nonneg`: `b^2 - 4*c ≥ 0` when `a, d, vf ≥ 0`
