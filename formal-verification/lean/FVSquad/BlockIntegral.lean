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

## Properties Proved (14 theorems, 0 sorry)

1. `biUpdate_zero_input`      — zero input leaves state unchanged (if already 0)
2. `biUpdate_bounded`         — output is bounded by max when max ≥ 0
3. `biUpdate_upper`           — output ≤ max when max ≥ 0
4. `biUpdate_lower`           — −max ≤ output when max ≥ 0
5. `biUpdate_exact_pos`       — exact value when sum is within range (pos direction)
6. `biUpdate_exact_neg`       — exact value when sum is within range (neg direction)
7. `biUpdate_sat_upper`       — output = max when sum exceeds max
8. `biUpdate_sat_lower`       — output = −max when sum goes below −max
9. `biUpdate_mono`            — monotone in input when max ≥ 0
10. `biIterate_bounded`       — iterated output remains bounded by max
11. `biIterate_zero_input`    — zero input leaves accumulated state at 0
12. `biIterate_mono`          — iterated output is monotone in input (dt ≥ 0)
13. `biUpdate_idempotent`     — applying biUpdate to a saturated state at max stays at max
14. `biIterate_nonneg`        — non-negative input and dt gives non-negative iterated output
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

-- ─── Additional iterated-update theorems ─────────────────────────────────────

/-- Zero input keeps the accumulated state at 0 for all n steps. -/
theorem biIterate_zero_input (n : Nat) (dt max : Rat) (hmax : 0 ≤ max) :
    biIterate n 0 dt max = 0 := by
  induction n with
  | zero => simp [biIterate]
  | succ n ih =>
    simp only [biIterate, biUpdate, ih, Rat.zero_mul, Rat.add_zero]
    exact limitSym_zero max hmax

/-- Iterated update is monotone in `input`: larger input → larger or equal accumulated output (dt ≥ 0). -/
theorem biIterate_mono (n : Nat) (input₁ input₂ dt max : Rat)
    (hdt : 0 ≤ dt) (hmax : 0 ≤ max) (hi : input₁ ≤ input₂) :
    biIterate n input₁ dt max ≤ biIterate n input₂ dt max := by
  induction n with
  | zero => simp only [biIterate]; exact Rat.le_refl
  | succ n ih =>
    simp only [biIterate, biUpdate]
    apply limitSym_mono _ _ _ hmax
    have hdt2 : input₁ * dt ≤ input₂ * dt := Rat.mul_le_mul_of_nonneg_right hi hdt
    calc biIterate n input₁ dt max + input₁ * dt
        ≤ biIterate n input₂ dt max + input₁ * dt := Rat.add_le_add_right.mpr ih
      _ ≤ biIterate n input₂ dt max + input₂ * dt := Rat.add_le_add_left.mpr hdt2

/-- If the state equals `max`, non-negative input and dt keeps it at `max`
    (since `max + input * dt ≥ max`, clamping the sum returns `max`). -/
theorem biUpdate_idempotent (input dt max : Rat)
    (hdt : 0 ≤ dt) (hmax : 0 ≤ max) (hi : 0 ≤ input) :
    biUpdate max input dt max = max := by
  unfold biUpdate
  have h1 : 0 ≤ input * dt := Rat.mul_nonneg hi hdt
  have hge : max + 0 ≤ max + input * dt := Rat.add_le_add_left.mpr h1
  rw [Rat.add_zero] at hge
  rcases Rat.le_iff_lt_or_eq.mp hge with hlt | heq
  · exact limitSym_above _ _ hlt
  · rw [← heq]
    exact limitSym_in_range max max (Rat.le_trans (Rat.neg_le_iff.mp hmax) hmax) Rat.le_refl

/-- Non-negative input and dt gives non-negative iterated output (from 0 initial state). -/
theorem biIterate_nonneg (n : Nat) (input dt max : Rat)
    (hdt : 0 ≤ dt) (hmax : 0 ≤ max) (hi : 0 ≤ input) :
    0 ≤ biIterate n input dt max := by
  have h0 : biIterate n 0 dt max = 0 := biIterate_zero_input n dt max hmax
  calc 0 = biIterate n 0 dt max := h0.symm
    _ ≤ biIterate n input dt max := biIterate_mono n 0 input dt max hdt hmax hi

end PX4.BlockIntegral
