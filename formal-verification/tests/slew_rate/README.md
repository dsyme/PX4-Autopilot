# SlewRate Correspondence Tests

🔬 *Lean Squad automated formal verification.*

This directory contains Route B correspondence tests for `SlewRate::update`,
verifying that the Lean 4 integer model in
`formal-verification/lean/FVSquad/SlewRate.lean` produces results behaviourally
identical to the C++ implementation in `src/lib/slew_rate/SlewRate.hpp`.

## What Is Tested

The function under test is `SlewRate::update`, modelled as a pure step function:

| C++ implementation | Lean 4 model |
|---|---|
| `SlewRate::update(new_value, deltatime)` | `slewUpdate current target max_step` |

The Lean 4 model (from `SlewRate.lean`, namespace `PX4.SlewRate`):

```lean
def slewUpdate (current target max_step : Int) : Int :=
  let d := target - current
  current + if d < -max_step then -max_step
            else if d > max_step then max_step
            else d
```

The C++ semantics (integer arithmetic, no float):

```cpp
dvalue_desired = new_value - _value
dvalue = constrain(dvalue_desired, -max_step, max_step)
_value += dvalue
```

## Test Sections

| Section | Description | Cases |
|---|---|---|
| § 1 Exact reach | Target within `max_step` — reaches exactly | 9 |
| § 2 Clamped positive | Overshoot positive direction: clamped to `+max_step` | 5 |
| § 3 Clamped negative | Overshoot negative direction: clamped to `−max_step` | 5 |
| § 4 Zero `max_step` | No movement when `max_step=0` | 12 |
| § 5 Unit steps | All `(current, target)` in `[−5,5]² with `max_step=1` | 121 |
| § 6 Small range sweep | All `(c, t, ms)` in `[−10,10]²×{0,1,2,5,10,100}` | 2646 |
| § 7 Large integers | Boundary arithmetic with large values (10⁹ scale) | 6 |
| § 8 Idempotence | Sufficient steps always reach target exactly | 4 |
| § 9 Monotone convergence | Each step does not overshoot; distance decreases | ~320 |
| § 10 Change bound | `\|new−current\| ≤ max_step` for all inputs | ~1200 |

**Total: 4 327 test cases.**

## Properties Verified Beyond Lean Proofs

The tests additionally exercise **sequential multi-step** properties that go
beyond the single-step theorems in `SlewRate.lean`:

- **Exact convergence in k steps**: given `max_step > 0` and
  `dist = |target − current|`, after `⌈dist / max_step⌉` steps the state
  equals `target` exactly.
- **Monotone convergence**: each step strictly reduces or maintains distance to
  target; no overshoot occurs.
- **Change bound**: the magnitude of each step is at most `max_step`.

These properties hold for all integer inputs because Lean's `Int` arithmetic
is exactly Python's arbitrary-precision integer arithmetic — no overflow,
no rounding.

## How to Run

```bash
cd formal-verification/tests/slew_rate
python3 check_correspondence.py
```

Requires Python 3.6+; no external packages needed.

Exit code `0` on success, non-zero if any test fails.

## Last Known Result

```
SlewRate correspondence tests: 4327 cases
All tests PASSED ✓
  C++ model and Lean 4 model agree on all cases.
  Monotone convergence and change-bound properties verified.
```

Run on 2026-04-29, commit `05771636d3`.

## Correspondence Level

**Exact** for integer arithmetic. The Lean `Int` model uses unbounded
integers with identical branching logic, so the correspondence is
mathematically exact. The integer instantiation of `SlewRate::update` with
`max_step` derived from `slew_rate * deltatime` (the floating-point product)
is not tested here — that rounding falls outside the integer model's scope.

For the full correspondence analysis, see `formal-verification/CORRESPONDENCE.md`.
