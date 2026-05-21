import FVSquad.BlockLimitSym

/-!
# PX4 `BlockIntegral` — Formal Verification

🔬 *Lean Squad automated formal verification.*

This file models and proves correctness properties of the rectangular integrator
`BlockIntegral`:

- **C++ source**: `src/lib/controllib/BlockIntegral.cpp` (line 48) and
  `src/lib/controllib/BlockIntegral.hpp`
- **Informal spec**: implied by class docstring; similar to `BlockIntegralTrap` but rectangular

## C++ Reference

```cpp
class BlockIntegral : public SuperBlock {
    float _y{0};          // accumulated integral
    BlockLimitSym _limit; // saturation guard
};

float BlockIntegral::update(float input) {
    // trapezoidal integration  <-- comment is misleading; formula is rectangular
    setY(_limit.update(getY() + input * getDt()));
    return getY();
}
```

The integrator accumulates `input * dt` at each timestep and saturates the
running sum to `[-limit, +limit]`.

## Model

We model all arithmetic over `Rat` (exact rationals):

- `y`    : accumulated integral (output state)
- `lim`  : non-negative saturation bound
- `dt`   : timestep (positive)
- `input`: input signal

The update rule is: `y_new = limitSym(y + input * dt, lim)`

where `limitSym x l = max(-l, min(l, x))`.

## Modelling Choices

- **Rectangular integration**: the update adds `input * dt` (not the trapezoidal
  average), matching the C++ formula exactly.
- **No previous-input tracking**: unlike `BlockIntegralTrap`, this integrator
  has no `_u` field — state is just `_y`.
- **`limitSym`** is reused from `BlockLimitSym.lean` in the same namespace.
- **Ignores** floating-point rounding, overflow, and NaN.

## Correspondence

| Lean | C++ | Correspondence |
|------|-----|----------------|
| `iState.y` | `BlockIntegral::_y` | exact |
| `iParams.limit` | `BlockLimitSym::getMax()` | exact |
| `iParams.dt` | `Block::getDt()` | exact |
| `iUpdate` | `BlockIntegral::update` | exact (rectangular) |
| `iConstrain` | `BlockLimitSym::update` | `limitSym` = exact |

## Verification Status

| Theorem | Status | Notes |
|---------|--------|-------|
| `iUpdate_y_bounded` | ✅ | output in `[-lim, lim]` |
| `iUpdate_y_ge_neg_lim` | ✅ | lower bound |
| `iUpdate_y_le_lim` | ✅ | upper bound |
| `iUpdate_y_exact` | ✅ | unclamped case: `y + input*dt` |
| `iUpdate_zero_input` | ✅ | zero input → y unchanged |
| `iUpdate_zero_state_zero_input` | ✅ | `y=0, input=0 → y=0` |
| `iFold_y_bounded` | ✅ | multi-step: y stays in range |
| `iUpdate_mono_input` | ✅ | larger input → larger y |
| `iUpdate_saturated_pos` | ✅ | raw accum > lim → clamped to lim |
| `iUpdate_saturated_neg` | ✅ | raw accum < -lim → clamped to -lim |
-/

namespace PX4.BlockIntegral

open PX4.BlockLimitSym (limitSym limitSym_above limitSym_below limitSym_range limitSym_upper limitSym_lower
                         limitSym_in_range limitSym_mono limitSym_zero limitSym_idempotent)

/-! ## Parameters and state -/

/-- Parameters of the rectangular integrator. -/
structure IParams where
  limit : Rat  -- saturation bound (must be ≥ 0)
  dt    : Rat  -- timestep (must be > 0)

/-- State of the rectangular integrator. -/
structure IState where
  y : Rat  -- accumulated integral

/-! ## Implementation model -/

/-- One-step rectangular update: `y_new = limitSym(y + input * dt, lim)`. -/
def iUpdate (p : IParams) (s : IState) (input : Rat) : IState :=
  { y := limitSym (s.y + input * p.dt) p.limit }

/-- Multi-step fold over a list of inputs. -/
def iFold (p : IParams) (s₀ : IState) : List Rat → IState
  | []      => s₀
  | x :: xs => iFold p (iUpdate p s₀ x) xs

/-! ## Concrete examples -/

-- Single step, no saturation: 0 + 1 * 0.1 = 0.1
example : (iUpdate ⟨1, 1/10⟩ ⟨0⟩ 1).y = 1/10 := by native_decide

-- Single step, positive saturation: 0 + 100 * 0.1 = 10 → clamped to 5
example : (iUpdate ⟨5, 1/10⟩ ⟨0⟩ 100).y = 5 := by native_decide

-- Single step, negative saturation: 0 + (-100) * 0.1 = -10 → clamped to -5
example : (iUpdate ⟨5, 1/10⟩ ⟨0⟩ (-100)).y = -5 := by native_decide

-- Two steps: accumulate
example : (iFold ⟨10, 1⟩ ⟨0⟩ [3, 2]).y = 5 := by native_decide

-- Two steps: accumulate then clamp
example : (iFold ⟨4, 1⟩ ⟨0⟩ [3, 3]).y = 4 := by native_decide

/-! ## Helper lemmas -/

private theorem limitSym_nonneg_y (s : IState) (input : Rat) (p : IParams)
    (hlim : 0 ≤ p.limit) :
    -p.limit ≤ limitSym (s.y + input * p.dt) p.limit ∧
     limitSym (s.y + input * p.dt) p.limit ≤ p.limit :=
  limitSym_range _ _ hlim

/-! ## Boundedness theorems -/

/-- The output is always in `[-lim, lim]` after one step. -/
theorem iUpdate_y_bounded (p : IParams) (s : IState) (input : Rat) (hlim : 0 ≤ p.limit) :
    -p.limit ≤ (iUpdate p s input).y ∧ (iUpdate p s input).y ≤ p.limit := by
  simp only [iUpdate]
  exact limitSym_range _ _ hlim

/-- Lower bound: output ≥ -lim. -/
theorem iUpdate_y_ge_neg_lim (p : IParams) (s : IState) (input : Rat) (hlim : 0 ≤ p.limit) :
    -p.limit ≤ (iUpdate p s input).y :=
  (iUpdate_y_bounded p s input hlim).1

/-- Upper bound: output ≤ lim. -/
theorem iUpdate_y_le_lim (p : IParams) (s : IState) (input : Rat) (hlim : 0 ≤ p.limit) :
    (iUpdate p s input).y ≤ p.limit :=
  (iUpdate_y_bounded p s input hlim).2

/-- When unsaturated: output equals `y + input * dt` exactly. -/
theorem iUpdate_y_exact (p : IParams) (s : IState) (input : Rat)
    (hlo : -p.limit ≤ s.y + input * p.dt) (hhi : s.y + input * p.dt ≤ p.limit) :
    (iUpdate p s input).y = s.y + input * p.dt := by
  simp only [iUpdate]
  exact limitSym_in_range _ _ hlo hhi

/-- Zero input leaves the output unchanged. -/
theorem iUpdate_zero_input (p : IParams) (s : IState) (hlim : 0 ≤ p.limit)
    (hs : -p.limit ≤ s.y ∧ s.y ≤ p.limit) :
    (iUpdate p s 0).y = s.y := by
  simp only [iUpdate, Rat.zero_mul, Rat.add_zero]
  exact limitSym_in_range _ _ hs.1 hs.2

/-- Zero state with zero input stays zero. -/
theorem iUpdate_zero_state_zero_input (p : IParams) (hlim : 0 ≤ p.limit) :
    (iUpdate p ⟨0⟩ 0).y = 0 := by
  simp only [iUpdate, Rat.zero_mul, Rat.add_zero]
  exact limitSym_zero _ hlim

/-! ## Multi-step boundedness -/

/-- After any number of steps, `y` remains in `[-lim, lim]`. -/
theorem iFold_y_bounded (p : IParams) (s₀ : IState) (inputs : List Rat) (hlim : 0 ≤ p.limit)
    (hs₀ : -p.limit ≤ s₀.y ∧ s₀.y ≤ p.limit) :
    -p.limit ≤ (iFold p s₀ inputs).y ∧ (iFold p s₀ inputs).y ≤ p.limit := by
  induction inputs generalizing s₀ with
  | nil => exact hs₀
  | cons x xs ih =>
    apply ih
    exact iUpdate_y_bounded p s₀ x hlim

/-! ## Monotonicity -/

/-- Larger input → larger (or equal) output after one step. -/
theorem iUpdate_mono_input (p : IParams) (s : IState) (i1 i2 : Rat)
    (hdt : 0 ≤ p.dt) (hi : i1 ≤ i2) (hlim : 0 ≤ p.limit) :
    (iUpdate p s i1).y ≤ (iUpdate p s i2).y := by
  simp only [iUpdate]
  apply limitSym_mono _ _ _ hlim
  apply Rat.add_le_add_left.mpr
  exact Rat.mul_le_mul_of_nonneg_right hi hdt

/-! ## Saturation theorems -/

/-- If the raw accumulation exceeds `lim`, output is clamped to `lim`. -/
theorem iUpdate_saturated_pos (p : IParams) (s : IState) (input : Rat)
    (hlim : 0 ≤ p.limit) (hsat : s.y + input * p.dt > p.limit) :
    (iUpdate p s input).y = p.limit := by
  simp only [iUpdate]
  have h_neg_lim : -p.limit ≤ 0 := by
    have := Rat.neg_le_neg hlim; rw [Rat.neg_zero] at this; exact this
  have h_neg_le_v : -p.limit ≤ s.y + input * p.dt :=
    Rat.le_trans h_neg_lim (Rat.le_trans hlim (Rat.le_of_lt hsat))
  simp [limitSym, Rat.not_lt.mpr h_neg_le_v, hsat]

/-- If the raw accumulation is below `-lim`, output is clamped to `-lim`. -/
theorem iUpdate_saturated_neg (p : IParams) (s : IState) (input : Rat)
    (hlim : 0 ≤ p.limit) (hsat : s.y + input * p.dt < -p.limit) :
    (iUpdate p s input).y = -p.limit := by
  simp only [iUpdate]
  have h_neg_lim_le_zero : -p.limit ≤ 0 := by
    have h := Rat.neg_le_neg hlim; rw [Rat.neg_zero] at h; exact h
  have h_not_above : ¬ (s.y + input * p.dt > p.limit) :=
    Rat.not_lt.mpr (Rat.le_trans (Rat.le_of_lt hsat) (Rat.le_trans h_neg_lim_le_zero hlim))
  simp [limitSym, h_not_above, hsat]

end PX4.BlockIntegral
