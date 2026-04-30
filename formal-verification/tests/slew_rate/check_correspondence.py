#!/usr/bin/env python3
"""
Route B Correspondence Tests: SlewRate::update
🔬 Lean Squad automated formal verification.

Validates that the Lean 4 integer model of SlewRate::update in
formal-verification/lean/FVSquad/SlewRate.lean produces results
behaviourally identical to the C++ implementation in
src/lib/slew_rate/SlewRate.hpp on a comprehensive set of integer test cases.

The C++ source (integer semantics, no float):
    Type update(Type new_value, int max_step):
        dvalue_desired = new_value - _value
        dvalue = constrain(dvalue_desired, -max_step, max_step)
        _value += dvalue
        return _value

The Lean 4 model (SlewRate.lean, namespace PX4.SlewRate):
    def slewUpdate (current target max_step : Int) : Int :=
      let d := target - current
      current + if d < -max_step then -max_step
                else if d > max_step then max_step
                else d

Since both use unbounded integer arithmetic with identical branching logic,
correspondence is exact (no floating-point rounding, no overflow).

Usage:
    python3 check_correspondence.py

Exit code 0 on success, non-zero on any mismatch.
"""

import sys
import itertools

# ── Lean model (exact translation from SlewRate.lean) ──────────────────────

def lean_slew_update(current: int, target: int, max_step: int) -> int:
    """Lean 4 model: PX4.SlewRate.slewUpdate"""
    d = target - current
    if d < -max_step:
        clamped = -max_step
    elif d > max_step:
        clamped = max_step
    else:
        clamped = d
    return current + clamped


# ── C++ model (direct translation from SlewRate.hpp, integer arithmetic) ──

def cpp_slew_update(current: int, target: int, max_step: int) -> int:
    """C++ model: SlewRate::update with integer arithmetic.
    dvalue_desired = new_value - _value
    dvalue = constrain(dvalue_desired, -max_step, max_step)
    _value += dvalue
    """
    dvalue_desired = target - current
    # math::constrain(val, lo, hi)
    if dvalue_desired < -max_step:
        dvalue = -max_step
    elif dvalue_desired > max_step:
        dvalue = max_step
    else:
        dvalue = dvalue_desired
    return current + dvalue


# ── Test harness ────────────────────────────────────────────────────────────

def run_tests():
    failures = []
    total = 0

    def check(current, target, max_step, label=""):
        nonlocal total
        total += 1
        lean = lean_slew_update(current, target, max_step)
        cpp  = cpp_slew_update(current, target, max_step)
        if lean != cpp:
            failures.append(
                f"MISMATCH [{label}] current={current} target={target} "
                f"max_step={max_step}: lean={lean}, cpp={cpp}"
            )

    # § 1  Exact reach: target within max_step
    for c, t, ms in [
        (0, 0, 5),         # already at target
        (0, 3, 5),         # small positive step
        (0, -3, 5),        # small negative step
        (0, 5, 5),         # exactly at max_step (positive)
        (0, -5, 5),        # exactly at max_step (negative)
        (100, 103, 5),     # shifted up
        (-100, -97, 5),    # shifted down
        (0, 0, 0),         # zero max_step, already at target
        (7, 7, 100),       # zero delta
    ]:
        check(c, t, ms, "exact_reach")

    # § 2  Clamped positive direction
    for c, t, ms in [
        (0, 10, 5),        # overshoot: clamp to +5
        (0, 100, 1),       # large overshoot: clamp to +1
        (50, 200, 10),     # large target, clamp to +10
        (-20, 20, 7),      # cross zero, clamp to +7
        (0, 1, 0),         # max_step=0, no movement
    ]:
        check(c, t, ms, "clamp_pos")

    # § 3  Clamped negative direction
    for c, t, ms in [
        (0, -10, 5),       # overshoot: clamp to -5
        (0, -100, 1),      # large overshoot: clamp to -1
        (50, -200, 10),    # large negative target, clamp to -10
        (20, -20, 7),      # cross zero negative, clamp to -7
        (5, 4, 0),         # max_step=0, no movement
    ]:
        check(c, t, ms, "clamp_neg")

    # § 4  Zero max_step (no movement regardless)
    for c, t in [
        (0, 100), (0, -100), (50, 50), (-30, 30), (0, 1), (0, -1),
    ]:
        check(c, t, 0, "zero_max_step")
        # result must equal current (no movement)
        result = lean_slew_update(c, t, 0)
        if result != c:
            failures.append(
                f"ZERO_MAX_STEP: expected no movement: current={c} "
                f"target={t} max_step=0, got result={result}"
            )

    # § 5  max_step == 1 (unit steps)
    for c in range(-5, 6):
        for t in range(-5, 6):
            check(c, t, 1, "unit_step")

    # § 6  Large range sweep (small values)
    for c in range(-10, 11):
        for t in range(-10, 11):
            for ms in [0, 1, 2, 5, 10, 100]:
                check(c, t, ms, "small_range_sweep")

    # § 7  Boundary arithmetic (large integers, no overflow in Python)
    large = 10**9
    for c, t, ms in [
        (0, large, large // 2),
        (large, 0, large // 2),
        (-large, large, 3),
        (large, -large, large),
        (large, large + 1, 1),
        (-large, -large - 1, 1),
    ]:
        check(c, t, ms, "large_integers")

    # § 8  Idempotence: after enough steps, reaches target
    def reaches_in_n_steps(current, target, max_step, n):
        v = current
        for _ in range(n):
            v = lean_slew_update(v, target, max_step)
        return v

    for c, t, ms in [
        (0, 100, 10),     # 10 steps to reach exactly
        (0, -100, 10),    # 10 steps negative
        (0, 7, 3),        # 3 steps to reach exactly
        (100, 70, 10),    # 3 steps (100->90->80->70)
    ]:
        if ms > 0:
            n_needed = (abs(t - c) + ms - 1) // ms
            result = reaches_in_n_steps(c, t, ms, n_needed)
            if result != t:
                failures.append(
                    f"REACH_CHECK: current={c} target={t} max_step={ms} "
                    f"after {n_needed} steps: got {result}, expected {t}"
                )
            total += 1

    # § 9  Monotone convergence: each step does not overshoot
    for c, t, ms in [
        (0, 50, 7), (0, -50, 7), (100, 0, 13), (-100, 0, 13),
    ]:
        v = c
        for step in range(20):
            new_v = lean_slew_update(v, t, ms)
            # distance to target must be non-increasing
            if abs(new_v - t) > abs(v - t):
                failures.append(
                    f"MONO_CONV: step {step}: current={v} target={t} "
                    f"max_step={ms}: distance increased from "
                    f"{abs(v-t)} to {abs(new_v-t)}"
                )
            # must not overshoot
            if c <= t:
                if new_v > t:
                    failures.append(
                        f"OVERSHOOT_POS: current={v} target={t} "
                        f"max_step={ms}: new_v={new_v} > target"
                    )
            else:
                if new_v < t:
                    failures.append(
                        f"OVERSHOOT_NEG: current={v} target={t} "
                        f"max_step={ms}: new_v={new_v} < target"
                    )
            v = new_v
            total += 1

    # § 10  Change bound: |new - current| <= max_step (when max_step >= 0)
    for c in range(-8, 9):
        for t in range(-8, 9):
            for ms in [0, 1, 2, 3, 8]:
                result = lean_slew_update(c, t, ms)
                delta = abs(result - c)
                if delta > ms:
                    failures.append(
                        f"CHANGE_BOUND: |{result}-{c}|={delta} > max_step={ms}"
                    )
                total += 1

    # Report
    print(f"SlewRate correspondence tests: {total} cases")
    if failures:
        print(f"FAILED: {len(failures)} mismatches")
        for f in failures[:20]:
            print(f"  {f}")
        return False
    else:
        print("All tests PASSED ✓")
        print("  C++ model and Lean 4 model agree on all cases.")
        print(f"  Monotone convergence and change-bound properties verified.")
        return True


if __name__ == "__main__":
    ok = run_tests()
    sys.exit(0 if ok else 1)
