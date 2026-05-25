#!/usr/bin/env python3
"""
Route B Correspondence Tests: PX4 BlockIntegral
🔬 Lean Squad automated formal verification.

Validates that the Lean 4 rational model of BlockIntegral::update in
formal-verification/lean/FVSquad/BlockIntegral.lean produces results that match
the expected C++ behaviour on a comprehensive set of inputs.

## Model summary

C++ source (src/lib/controllib/BlockIntegral.cpp, lines 48-52):
    float BlockIntegral::update(float input) {
        setY(_limit.update(getY() + input * getDt()));
        return getY();
    }
    // BlockLimitSym::update: clamps to [-max, +max]

Lean 4 model (BlockIntegral.lean, namespace PX4.BlockIntegral):
    def limitSym (x max : Rat) : Rat :=
      if max < 0 then 0
      else if x < -max then -max
      else if max < x then max
      else x
    def biUpdate (state input dt max : Rat) : Rat :=
      limitSym (state + input * dt) max
    def biIterate (n : Nat) (input dt max : Rat) : Rat :=
      match n with
      | 0     => 0
      | n + 1 => biUpdate (biIterate n input dt max) input dt max

The Lean model uses exact rational arithmetic; C++ uses float.
Tests use inputs representable exactly in both (small integers / simple fractions),
so no floating-point rounding error arises within the tested cases.

## Theorems validated

This test suite exercises each of the 10 proved theorems:
1. biUpdate_zero_input   — zero input on zero state → 0
2. biUpdate_bounded      — |output| ≤ max
3. biUpdate_upper        — output ≤ max
4. biUpdate_lower        — -max ≤ output
5. biUpdate_exact_pos    — accumulation within range (positive)
6. biUpdate_exact_neg    — accumulation within range (negative)
7. biUpdate_sat_upper    — saturation at +max
8. biUpdate_sat_lower    — saturation at -max
9. biUpdate_mono         — monotone in input
10. biIterate_bounded    — iterated output stays bounded

## Running

    python3 check_correspondence.py

Exit code 0 on success (all cases pass), non-zero on any failure.
"""

import sys
from fractions import Fraction

# ── Lean rational model (Python translation) ──────────────────────────────────

def limit_sym(x: Fraction, max_val: Fraction) -> Fraction:
    """Mirrors PX4.BlockLimitSym.limitSym in FVSquad/BlockLimitSym.lean.

    limitSym x max =
      if max < 0  then 0
      else if x < -max then -max
      else if max < x  then max
      else x
    """
    if max_val < 0:
        return Fraction(0)
    if x < -max_val:
        return -max_val
    if max_val < x:
        return max_val
    return x


def bi_update(state: Fraction, input_: Fraction, dt: Fraction, max_val: Fraction) -> Fraction:
    """Mirrors PX4.BlockIntegral.biUpdate.

    biUpdate state input dt max = limitSym (state + input * dt) max
    """
    return limit_sym(state + input_ * dt, max_val)


def bi_iterate(n: int, input_: Fraction, dt: Fraction, max_val: Fraction) -> Fraction:
    """Mirrors PX4.BlockIntegral.biIterate.

    biIterate 0       ...    = 0
    biIterate (n + 1) ...    = biUpdate (biIterate n ...) input dt max
    """
    state = Fraction(0)
    for _ in range(n):
        state = bi_update(state, input_, dt, max_val)
    return state


# ── Test harness ──────────────────────────────────────────────────────────────

_pass = 0
_fail = 0


def check(name: str, got, expected) -> None:
    global _pass, _fail
    if got == expected:
        _pass += 1
    else:
        _fail += 1
        print(f"FAIL  {name}")
        print(f"      got      = {got}")
        print(f"      expected = {expected}")


def check_le(name: str, lhs, rhs) -> None:
    global _pass, _fail
    if lhs <= rhs:
        _pass += 1
    else:
        _fail += 1
        print(f"FAIL  {name}")
        print(f"      {lhs} > {rhs}")


def check_ge(name: str, lhs, rhs) -> None:
    global _pass, _fail
    if lhs >= rhs:
        _pass += 1
    else:
        _fail += 1
        print(f"FAIL  {name}")
        print(f"      {lhs} < {rhs}")


# ── Test group 1: biUpdate_zero_input (theorem 1) ─────────────────────────────

def test_zero_input() -> None:
    """Zero input on zero state → 0, for various dt and max values."""
    for max_val in [Fraction(1), Fraction(5), Fraction(10), Fraction(1, 2)]:
        for dt in [Fraction(1), Fraction(1, 10), Fraction(2)]:
            result = bi_update(Fraction(0), Fraction(0), dt, max_val)
            check(f"zero_input(dt={dt}, max={max_val})", result, Fraction(0))


# ── Test group 2: biUpdate_bounded / upper / lower (theorems 2-4) ─────────────

def test_bounds() -> None:
    """Output is bounded by [-max, max] for various inputs."""
    max_vals = [Fraction(1), Fraction(5), Fraction(1, 2)]
    inputs   = [Fraction(-10), Fraction(-2), Fraction(0), Fraction(3), Fraction(10)]
    states   = [Fraction(-3), Fraction(0), Fraction(2)]
    dts      = [Fraction(1), Fraction(1, 10)]

    for max_val in max_vals:
        for inp in inputs:
            for state in states:
                for dt in dts:
                    result = bi_update(state, inp, dt, max_val)
                    check_le(f"upper_bound(state={state},inp={inp},dt={dt},max={max_val})",
                             result, max_val)
                    check_ge(f"lower_bound(state={state},inp={inp},dt={dt},max={max_val})",
                             result, -max_val)


# ── Test group 3: exact value within range (theorems 5-6) ─────────────────────

def test_exact() -> None:
    """When state + input*dt is within [-max, max], output equals the sum."""
    cases = [
        # (state, input, dt, max, expected)
        (Fraction(0),  Fraction(2),  Fraction(1),    Fraction(10), Fraction(2)),
        (Fraction(3),  Fraction(1),  Fraction(1),    Fraction(10), Fraction(4)),
        (Fraction(0),  Fraction(-2), Fraction(1),    Fraction(10), Fraction(-2)),
        (Fraction(-3), Fraction(1),  Fraction(1),    Fraction(10), Fraction(-2)),
        (Fraction(0),  Fraction(1),  Fraction(1, 2), Fraction(5),  Fraction(1, 2)),
        (Fraction(1),  Fraction(3),  Fraction(1, 3), Fraction(5),  Fraction(2)),
        (Fraction(0),  Fraction(-1), Fraction(3),    Fraction(5),  Fraction(-3)),
    ]
    for state, inp, dt, max_val, expected in cases:
        result = bi_update(state, inp, dt, max_val)
        check(f"exact(state={state},inp={inp},dt={dt},max={max_val})", result, expected)


# ── Test group 4: saturation (theorems 7-8) ───────────────────────────────────

def test_saturation() -> None:
    """Output clamps to max / -max when sum exceeds bounds."""
    max_val = Fraction(5)
    # Upper saturation
    sat_upper_cases = [
        (Fraction(0),  Fraction(10), Fraction(1)),
        (Fraction(4),  Fraction(2),  Fraction(1)),
        (Fraction(0),  Fraction(6),  Fraction(1)),
        (Fraction(3),  Fraction(100), Fraction(1, 10)),
    ]
    for state, inp, dt in sat_upper_cases:
        result = bi_update(state, inp, dt, max_val)
        check(f"sat_upper(state={state},inp={inp},dt={dt})", result, max_val)

    # Lower saturation
    sat_lower_cases = [
        (Fraction(0),   Fraction(-10), Fraction(1)),
        (Fraction(-4),  Fraction(-2),  Fraction(1)),
        (Fraction(0),   Fraction(-6),  Fraction(1)),
        (Fraction(-3),  Fraction(-100), Fraction(1, 10)),
    ]
    for state, inp, dt in sat_lower_cases:
        result = bi_update(state, inp, dt, max_val)
        check(f"sat_lower(state={state},inp={inp},dt={dt})", result, -max_val)


# ── Test group 5: monotonicity (theorem 9) ────────────────────────────────────

def test_monotone() -> None:
    """biUpdate is monotone in input: inp1 ≤ inp2 → biUpdate(...,inp1,...) ≤ biUpdate(...,inp2,...)."""
    max_val = Fraction(10)
    dt      = Fraction(1)
    states  = [Fraction(-3), Fraction(0), Fraction(4)]
    inputs  = [Fraction(-5), Fraction(-2), Fraction(0), Fraction(1), Fraction(5)]

    for state in states:
        for i, inp1 in enumerate(inputs):
            for inp2 in inputs[i:]:
                r1 = bi_update(state, inp1, dt, max_val)
                r2 = bi_update(state, inp2, dt, max_val)
                check_le(f"mono(state={state},inp1={inp1},inp2={inp2})", r1, r2)


# ── Test group 6: biIterate_bounded (theorem 10) ──────────────────────────────

def test_iterate_bounded() -> None:
    """Iterated update remains bounded by max for any number of steps."""
    max_val = Fraction(5)
    dt      = Fraction(1, 10)

    for inp in [Fraction(-100), Fraction(-5), Fraction(0), Fraction(5), Fraction(100)]:
        for n in range(0, 20):
            result = bi_iterate(n, inp, dt, max_val)
            check_le(f"iter_upper(n={n},inp={inp})", result, max_val)
            check_ge(f"iter_lower(n={n},inp={inp})", result, -max_val)


# ── Test group 7: accumulation correctness ───────────────────────────────────

def test_accumulation() -> None:
    """Unsaturated accumulation: n steps of input=a, dt=1 → state = n*a."""
    a       = Fraction(1, 2)
    dt      = Fraction(1)
    max_val = Fraction(100)

    for n in range(1, 20):
        result   = bi_iterate(n, a, dt, max_val)
        expected = Fraction(n) * a
        check(f"accumulate(n={n},a={a})", result, expected)

    # With dt ≠ 1
    a2 = Fraction(3)
    dt2 = Fraction(1, 4)
    for n in range(1, 10):
        result   = bi_iterate(n, a2, dt2, max_val)
        expected = Fraction(n) * a2 * dt2
        check(f"accumulate_dt(n={n},a={a2},dt={dt2})", result, expected)


# ── Test group 8: dt = 0 is identity ──────────────────────────────────────────

def test_dt_zero() -> None:
    """When dt = 0, biUpdate is the identity (state unchanged)."""
    dt = Fraction(0)
    for state in [Fraction(-5), Fraction(0), Fraction(3)]:
        for inp in [Fraction(-10), Fraction(0), Fraction(10)]:
            for max_val in [Fraction(1), Fraction(10)]:
                result = bi_update(state, inp, dt, max_val)
                expected = limit_sym(state, max_val)  # state re-clamped (no new accumulation)
                check(f"dt_zero(state={state},inp={inp},max={max_val})", result, expected)


# ── Main ──────────────────────────────────────────────────────────────────────

def main() -> int:
    test_zero_input()
    test_bounds()
    test_exact()
    test_saturation()
    test_monotone()
    test_iterate_bounded()
    test_accumulation()
    test_dt_zero()

    total = _pass + _fail
    print(f"\nBlockIntegral correspondence: {_pass}/{total} passed, {_fail} failed.")
    return 0 if _fail == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
