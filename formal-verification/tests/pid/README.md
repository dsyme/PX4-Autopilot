# PID Controller — Route B Correspondence Tests

🔬 *Lean Squad automated formal verification.*

## Purpose

Validates that the Lean 4 integer model in
`formal-verification/lean/FVSquad/PID.lean` produces results behaviourally
identical to the C++ implementation in `src/lib/pid/PID.cpp` on a
comprehensive set of integer test cases.

## Running the tests

```bash
python3 check_correspondence.py
```

Exit code 0 on success, non-zero on any mismatch. No external dependencies.

## Test outcome (run 100)

```
Total test cases: 7964
✅ All 7964 cases passed — Lean model matches C++ reference exactly
```

## What is tested

| Test group | Cases | What it verifies |
|------------|-------|-----------------|
| `clamp` | 310 | Symmetric clamp [-limit, limit] — exact bit-for-bit agreement |
| `deriv_first_call` | 80 | First-call returns 0 (NaN guard) — all (fb, dt) pairs |
| `deriv_subsequent` | 2646 | Subsequent derivative: `(fb-prev)/dt`, integer division |
| `updateIntegral` | 1764 | Anti-windup clamp: all gain/error/dt/limit combinations |
| `pidOutput` | 2304 | Full one-step output for grid of (sp, fb, dt, gains, limits, state) |
| `multiStep_output` | 430 | 5 multi-step sequences × 10 steps × output |
| `multiStep_integral` | 430 | 5 multi-step sequences × 10 steps × integral |

## What the correspondence covers

The Lean model abstracts three aspects of the C++ implementation:
- **Float rounding**: the Lean model uses exact `Int` arithmetic; C++ uses `float`. Tests use integer-valued inputs so rounding is absent.
- **FLT_EPSILON threshold**: the Lean model uses strict `dt > 0`; C++ uses `dt > FLT_EPSILON`. With integer `dt`, these are equivalent for `dt ≥ 1`.
- **`update_integral` flag**: always `true` in the model; multi-step tests verify this path.

## What is NOT covered

- Floating-point rounding for non-integer inputs
- NaN/infinity propagation
- The `isfinite` guard on `integral_new` in C++ (rare edge case)

## Files

- `check_correspondence.py` — self-contained test script (pure Python, no deps)
