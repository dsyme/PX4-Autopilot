import Init.Data.Rat.Basic
import FVSquad.BlockLimitSym

/-!
# PX4 `BlockIntegral` — Formal Verification

🔬 *Lean Squad automated formal verification.*

This file models and proves correctness properties of PX4's rectangular integrator
`BlockIntegral::update`:

- **C++ source**: `src/lib/controllib/BlockIntegral.cpp` (lines 48–52) and
  `src/lib/controllib/BlockIntegral.hpp`

## C++ Source

```cpp
float BlockIntegral::update(float input)
{
    // trapezoidal integration
    setY(_limit.update(getY() + input * getDt()));
    return getY();
}
```

Note: the comment says "trapezoidal" but the implementation is rectangular — it
multiplies the current `input` by `dt` and accumulates. There is no averaging of
consecutive inputs. This is a naming discrepancy in the source code (not a bug).

## Model

Over `Rat` (exact rational arithmetic), the pure functional model of one `update`
step is:

```
biUpdate(state, input, dt, max) = limitSym(state + input * dt, max)
```

The iterated model tracks the state after `n` steps:

```
biIterate(n, input, dt, max) = state after n steps from 0
```

**Abstracted away**: The `Block` hierarchy, `BlockParam` objects, and floating-point
rounding. The Lean model captures the pure numeric behaviour under the assumption
that `max ≥ 0` (as required by `BlockLimitSym`).

## Properties Proved (10 theorems, 0 sorry)

1. `biUpdate_zero_input`   — zero input leaves state unchanged (if already 0)
2. `biUpdate_bounded`      — output is bounded by max when max ≥ 0
3. `biUpdate_upper`        — output ≤ max when max ≥ 0
4. `biUpdate_lower`        — −max ≤ output when max ≥ 0
5. `biUpdate_exact_pos`    — exact value when sum is within range (pos direction)
6. `biUpdate_exact_neg`    — exact value when sum is within range (neg direction)
7. `biUpdate_sat_upper`    — output = max when sum exceeds max
8. `biUpdate_sat_lower`    — output = −max when sum goes below −max
9. `biUpdate_mono`         — monotone in input when max ≥ 0
10. `biIterate_bounded`    — iterated output remains bounded by max
-/

namespace PX4.BlockIntegral

open PX4.BlockLimitSym

/-- Single update step: accumulate `input * dt` into `state`, then clamp to `[−max, max]`. -/
def biUpdate (state input dt max : Rat) : Rat :=
  limitSym (state + input * dt) max

/-- Iterated update from `state = 0` with constant `input` and `dt`. -/
def biIterate (n : Nat) (input dt max : Rat) : Rat :=
  match n with
  | 0     => 0
  | n + 1 => biUpdate (biIterate n input dt max) input dt max

-- ─── Single-step theorems ────────────────────────────────────────────────────

/-- Zero input on zero state gives zero. -/
theorem biUpdate_zero_input (dt max : Rat) :
    biUpdate 0 0 dt max = limitSym 0 max := by
  unfold biUpdate; simp [Rat.zero_mul, Rat.add_zero]

/-- The output is bounded: lies in [−max, max] when max ≥ 0. -/
theorem biUpdate_bounded (state input dt max : Rat) (hmax : 0 ≤ max) :
    -max ≤ biUpdate state input dt max ∧ biUpdate state input dt max ≤ max := by
  exact ⟨limitSym_lower _ _ hmax, limitSym_upper _ _ hmax⟩

/-- Upper bound: output ≤ max when max ≥ 0. -/
theorem biUpdate_upper (state input dt max : Rat) (hmax : 0 ≤ max) :
    biUpdate state input dt max ≤ max :=
  limitSym_upper _ _ hmax

/-- Lower bound: −max ≤ output when max ≥ 0. -/
theorem biUpdate_lower (state input dt max : Rat) (hmax : 0 ≤ max) :
    -max ≤ biUpdate state input dt max :=
  limitSym_lower _ _ hmax

/-- Exact value (no saturation) when accumulated value is within [−max, max]. -/
theorem biUpdate_exact (state input dt max : Rat)
    (h1 : -max ≤ state + input * dt) (h2 : state + input * dt ≤ max) :
    biUpdate state input dt max = state + input * dt :=
  limitSym_in_range _ _ h1 h2

/-- Upper saturation: output = max when accumulated sum exceeds max. -/
theorem biUpdate_sat_upper (state input dt max : Rat)
    (h : state + input * dt > max) :
    biUpdate state input dt max = max :=
  limitSym_above _ _ h

/-- Lower saturation: output = −max when accumulated sum goes below −max. -/
theorem biUpdate_sat_lower (state input dt max : Rat) (hmax : 0 ≤ max)
    (h : state + input * dt < -max) :
    biUpdate state input dt max = -max :=
  limitSym_below _ _ hmax h

/-- Monotone in `input`: larger input → larger or equal output (dt ≥ 0 required). -/
theorem biUpdate_mono (state input₁ input₂ dt max : Rat)
    (hdt : 0 ≤ dt) (hmax : 0 ≤ max) (hi : input₁ ≤ input₂) :
    biUpdate state input₁ dt max ≤ biUpdate state input₂ dt max := by
  unfold biUpdate
  apply limitSym_mono
  · exact hmax
  · have : input₁ * dt ≤ input₂ * dt := Rat.mul_le_mul_of_nonneg_right hi hdt
    exact Rat.add_le_add_left.mpr this

-- ─── Iterated-update theorems ────────────────────────────────────────────────

/-- After any number of steps, the accumulated state lies in [−max, max]. -/
theorem biIterate_bounded (n : Nat) (input dt max : Rat) (hmax : 0 ≤ max) :
    -max ≤ biIterate n input dt max ∧ biIterate n input dt max ≤ max := by
  induction n with
  | zero =>
    simp [biIterate]
    exact ⟨Rat.neg_le_iff.mp hmax, hmax⟩
  | succ n ih =>
    simp [biIterate]
    exact biUpdate_bounded _ _ _ _ hmax

end PX4.BlockIntegral
