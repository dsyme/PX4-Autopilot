/-!
# PX4 `VelocitySmoothing::computeT2` / `computeT3` — Formal Verification

🔬 Lean Squad automated formal verification.

This file models and proves correctness properties of two helpers in PX4's
jerk-limited velocity trajectory planner:

- **C++ source**: `src/lib/motion_planning/VelocitySmoothing.cpp`, lines 143–162
- **Informal spec**: `formal-verification/specs/velocity_smoothing_informal.md`

## C++ Source

```cpp
float VelocitySmoothing::computeT3(float T1, float a0, float j_max) const
{
    float T3 = a0 / j_max + T1;
    return math::max(T3, 0.f);
}

float VelocitySmoothing::computeT2(float T123, float T1, float T3) const
{
    float T2 = T123 - T1 - T3;
    return math::max(T2, 0.f);
}
```

## Model

We model over `Int` (unbounded integers) to obtain fully automated proofs via
`omega`.  The C++ functions operate on `float`; integer inputs capture the
algebraic structure exactly when the domain is restricted to integers.

**`computeT2`** (`T123 T1 T3 : Int`): models `max(T123 − T1 − T3, 0)` exactly.

**`computeT3Scaled`** (`T1 a0 jMax : Int`): models `max(a0 + jMax * T1, 0)`.
This represents `jMax * computeT3(T1, a0/jMax)` when `jMax > 0`, i.e., the
formula with the division cleared.  All key algebraic properties
(non-negativity, monotonicity, value characterisation) transfer intact.

## Approximations / out of scope

- **Float NaN / ±∞ / rounding**: not modelled; `Int` arithmetic is exact.
- **IEEE 754 semantics**: `math::max` is modelled as mathematical `max`.
- **Division by jMax**: cleared by multiplication in `computeT3Scaled`; the
  `jMax > 0` hypothesis is carried explicitly wherever it matters.
- **The full trajectory planner**: only the two simple helpers are modelled;
  `updateDurations` and `updateTraj` are out of scope.
-/

namespace PX4.VelocitySmoothing

-- ============================================================
-- § 0  Definitions
-- ============================================================

/-- Integer model of `VelocitySmoothing::computeT2(T123, T1, T3)`.

    Returns the phase-2 (coasting) duration: `T123 − T1 − T3` clamped to
    `[0, ∞)`.  Matches the C++ formula exactly for integer arguments. -/
def computeT2 (T123 T1 T3 : Int) : Int := max (T123 - T1 - T3) 0

/-- Scaled integer model of `VelocitySmoothing::computeT3(T1, a0, jMax)`.

    Returns `max(a0 + jMax * T1, 0)`, which equals `jMax * computeT3` when
    `jMax > 0`.  Division is cleared to keep proofs in `omega`'s fragment. -/
def computeT3Scaled (T1 a0 jMax : Int) : Int := max (a0 + jMax * T1) 0

-- Sanity checks.
#eval computeT2 5   1   2   -- 2
#eval computeT2 3   2   2   -- 0   (T1+T3 = 4 > T123 → clamped)
#eval computeT2 4   2   2   -- 0   (exact fit)
#eval computeT2 0   0   0   -- 0

#eval computeT3Scaled 1   2   4   -- 6   (= 4 * computeT3 = 4 * 1.5)
#eval computeT3Scaled 0   0   5   -- 0
#eval computeT3Scaled 1 (-4)  2   -- 0   (a0 + jMax*T1 = -4 + 2 = -2 → 0)

-- ============================================================
-- § 1  `computeT2` — non-negativity and value
-- ============================================================

/-- `computeT2` always returns a non-negative duration. -/
theorem computeT2_nonneg (T123 T1 T3 : Int) : 0 ≤ computeT2 T123 T1 T3 := by
  unfold computeT2
  by_cases h : T123 - T1 - T3 ≤ 0
  · rw [Int.max_eq_right h]; exact Int.le_refl 0
  · rw [Int.max_eq_left (by omega)]; omega

/-- When `T1 + T3 ≤ T123`, the clamp is inactive: result equals `T123 − T1 − T3`. -/
theorem computeT2_eq_diff (T123 T1 T3 : Int) (h : T1 + T3 ≤ T123) :
    computeT2 T123 T1 T3 = T123 - T1 - T3 := by
  unfold computeT2
  rw [Int.max_eq_left]; omega

/-- When `T123 < T1 + T3`, the coasting phase is zero. -/
theorem computeT2_eq_zero (T123 T1 T3 : Int) (h : T123 < T1 + T3) :
    computeT2 T123 T1 T3 = 0 := by
  unfold computeT2
  rw [Int.max_eq_right]; omega

/-- Exact fit: when `T123 = T1 + T3`, no coasting is needed. -/
theorem computeT2_zero_exact (T1 T3 : Int) : computeT2 (T1 + T3) T1 T3 = 0 := by
  unfold computeT2
  rw [Int.max_eq_right]; omega

-- ============================================================
-- § 2  `computeT2` — partition identity
-- ============================================================

/-- **Partition identity**: `computeT2 T123 T1 T3 + T1 + T3 = max T123 (T1 + T3)`.

    If T123 is large enough (T2 > 0), total time is T123.
    If T123 is too small (T2 = 0), total time is T1 + T3. -/
theorem computeT2_partition (T123 T1 T3 : Int) :
    computeT2 T123 T1 T3 + T1 + T3 = max T123 (T1 + T3) := by
  unfold computeT2
  by_cases h1 : T123 - T1 - T3 ≤ 0
  · rw [Int.max_eq_right h1]
    have h2 : T123 ≤ T1 + T3 := by omega
    rw [Int.max_eq_right h2]; omega
  · rw [Int.max_eq_left (by omega)]
    have h2 : ¬ T123 ≤ T1 + T3 := by omega
    rw [Int.max_eq_left (by omega)]; omega

-- ============================================================
-- § 3  `computeT2` — monotonicity and anti-monotonicity
-- ============================================================

/-- `computeT2` is monotone in `T123`:
    a longer total duration allows a longer (or equal) coasting phase. -/
theorem computeT2_mono_T123 (T123 T123' T1 T3 : Int) (h : T123 ≤ T123') :
    computeT2 T123 T1 T3 ≤ computeT2 T123' T1 T3 := by
  unfold computeT2
  by_cases h1 : T123 - T1 - T3 ≤ 0
  · rw [Int.max_eq_right h1]; exact Int.le_max_right _ _
  · rw [Int.max_eq_left (by omega)]
    by_cases h2 : T123' - T1 - T3 ≤ 0
    · exfalso; omega
    · rw [Int.max_eq_left (by omega)]; omega

/-- `computeT2` is anti-monotone in `T1`:
    a longer phase 1 leaves less room for the coasting phase. -/
theorem computeT2_anti_T1 (T123 T1 T1' T3 : Int) (h : T1 ≤ T1') :
    computeT2 T123 T1' T3 ≤ computeT2 T123 T1 T3 := by
  unfold computeT2
  by_cases h1 : T123 - T1' - T3 ≤ 0
  · rw [Int.max_eq_right h1]; exact Int.le_max_right _ _
  · rw [Int.max_eq_left (by omega)]
    by_cases h2 : T123 - T1 - T3 ≤ 0
    · exfalso; omega
    · rw [Int.max_eq_left (by omega)]; omega

/-- `computeT2` is anti-monotone in `T3`:
    a longer phase 3 leaves less room for the coasting phase. -/
theorem computeT2_anti_T3 (T123 T1 T3 T3' : Int) (h : T3 ≤ T3') :
    computeT2 T123 T1 T3' ≤ computeT2 T123 T1 T3 := by
  unfold computeT2
  by_cases h1 : T123 - T1 - T3' ≤ 0
  · rw [Int.max_eq_right h1]; exact Int.le_max_right _ _
  · rw [Int.max_eq_left (by omega)]
    by_cases h2 : T123 - T1 - T3 ≤ 0
    · exfalso; omega
    · rw [Int.max_eq_left (by omega)]; omega

-- ============================================================
-- § 4  `computeT2` — commutativity, upper bound, special values
-- ============================================================

/-- `computeT2` is symmetric in `T1` and `T3`:
    the order of phase 1 and phase 3 does not matter for the coasting duration. -/
theorem computeT2_comm (T123 T1 T3 : Int) :
    computeT2 T123 T1 T3 = computeT2 T123 T3 T1 := by
  unfold computeT2; congr 1; omega

/-- `computeT2` does not exceed `T123` when `T123`, `T1`, `T3` are all non-negative. -/
theorem computeT2_le_T123 (T123 T1 T3 : Int) (h0 : 0 ≤ T123) (h1 : 0 ≤ T1) (h3 : 0 ≤ T3) :
    computeT2 T123 T1 T3 ≤ T123 := by
  unfold computeT2
  by_cases hc : T123 - T1 - T3 ≤ 0
  · rw [Int.max_eq_right hc]; exact h0
  · rw [Int.max_eq_left (by omega)]; omega

/-- All-zero inputs give zero output. -/
theorem computeT2_all_zero : computeT2 0 0 0 = 0 := by
  unfold computeT2; simp

-- ============================================================
-- § 5  `computeT3Scaled` — non-negativity and value
-- ============================================================

/-- `computeT3Scaled` always returns a non-negative value. -/
theorem computeT3Scaled_nonneg (T1 a0 jMax : Int) : 0 ≤ computeT3Scaled T1 a0 jMax := by
  unfold computeT3Scaled
  by_cases h : a0 + jMax * T1 ≤ 0
  · rw [Int.max_eq_right h]; exact Int.le_refl 0
  · rw [Int.max_eq_left (by omega)]; omega

/-- When `a0 + jMax * T1 ≥ 0`, the clamp is inactive. -/
theorem computeT3Scaled_eq_sum (T1 a0 jMax : Int) (h : 0 ≤ a0 + jMax * T1) :
    computeT3Scaled T1 a0 jMax = a0 + jMax * T1 := by
  unfold computeT3Scaled
  rw [Int.max_eq_left]; omega

/-- When `a0 + jMax * T1 < 0`, the result is zero. -/
theorem computeT3Scaled_eq_zero (T1 a0 jMax : Int) (h : a0 + jMax * T1 < 0) :
    computeT3Scaled T1 a0 jMax = 0 := by
  unfold computeT3Scaled
  rw [Int.max_eq_right]; omega

/-- Zero inputs give zero output. -/
theorem computeT3Scaled_zero (jMax : Int) : computeT3Scaled 0 0 jMax = 0 := by
  unfold computeT3Scaled; simp

-- ============================================================
-- § 6  `computeT3Scaled` — monotonicity
-- ============================================================

/-- `computeT3Scaled` is monotone in `T1` when `jMax > 0`:
    a longer phase 1 gives a longer (or equal) scaled phase 3. -/
theorem computeT3Scaled_mono_T1 (T1 T1' a0 jMax : Int) (hjMax : 0 < jMax) (h : T1 ≤ T1') :
    computeT3Scaled T1 a0 jMax ≤ computeT3Scaled T1' a0 jMax := by
  unfold computeT3Scaled
  have hmul : jMax * T1 ≤ jMax * T1' :=
    Int.mul_le_mul_of_nonneg_left h (Int.le_of_lt hjMax)
  by_cases h1 : a0 + jMax * T1 ≤ 0
  · rw [Int.max_eq_right h1]; exact Int.le_max_right _ _
  · rw [Int.max_eq_left (by omega)]
    by_cases h2 : a0 + jMax * T1' ≤ 0
    · exfalso; omega
    · rw [Int.max_eq_left (by omega)]; omega

/-- `computeT3Scaled` is monotone in `a0`:
    larger initial acceleration gives a larger (or equal) scaled phase 3. -/
theorem computeT3Scaled_mono_a0 (T1 a0 a0' jMax : Int) (h : a0 ≤ a0') :
    computeT3Scaled T1 a0 jMax ≤ computeT3Scaled T1 a0' jMax := by
  unfold computeT3Scaled
  by_cases h1 : a0 + jMax * T1 ≤ 0
  · rw [Int.max_eq_right h1]; exact Int.le_max_right _ _
  · rw [Int.max_eq_left (by omega)]
    by_cases h2 : a0' + jMax * T1 ≤ 0
    · exfalso; omega
    · rw [Int.max_eq_left (by omega)]; omega

-- ============================================================
-- § 7  `computeT3Scaled` — monotonicity in jMax
-- ============================================================

/-- `computeT3Scaled` is monotone in `jMax` when `T1 ≥ 0`:
    higher jerk limit → larger scaled phase 3 duration (more room to decelerate). -/
theorem computeT3Scaled_mono_jMax (T1 a0 jMax jMax' : Int)
    (hT1 : 0 ≤ T1) (h : jMax ≤ jMax') :
    computeT3Scaled T1 a0 jMax ≤ computeT3Scaled T1 a0 jMax' := by
  unfold computeT3Scaled
  have hmul : jMax * T1 ≤ jMax' * T1 := Int.mul_le_mul_of_nonneg_right h hT1
  by_cases h1 : a0 + jMax * T1 ≤ 0
  · rw [Int.max_eq_right h1]; exact Int.le_max_right _ _
  · rw [Int.max_eq_left (by omega)]
    by_cases h2 : a0 + jMax' * T1 ≤ 0
    · exfalso; omega
    · rw [Int.max_eq_left (by omega)]; omega

/-- When `T1 = 0`, `computeT3Scaled` does not depend on `jMax`. -/
theorem computeT3Scaled_T1_zero (a0 jMax : Int) :
    computeT3Scaled 0 a0 jMax = max a0 0 := by
  unfold computeT3Scaled; simp

-- ============================================================
-- § 8  Strict monotonicity of `computeT2`
-- ============================================================

/-- `computeT2` is *strictly* monotone in `T123` when the clamp is inactive:
    if `T1 + T3 ≤ T123 < T123'`, then `computeT2 T123 T1 T3 < computeT2 T123' T1 T3`. -/
theorem computeT2_strict_mono_T123 (T123 T123' T1 T3 : Int)
    (hfit : T1 + T3 ≤ T123) (hlt : T123 < T123') :
    computeT2 T123 T1 T3 < computeT2 T123' T1 T3 := by
  rw [computeT2_eq_diff T123 T1 T3 hfit]
  by_cases h2 : T1 + T3 ≤ T123'
  · rw [computeT2_eq_diff T123' T1 T3 h2]; omega
  · exfalso; omega

/-- `computeT2` is constant in `T123` when the clamp is active:
    if `T123 < T1 + T3` and `T123' < T1 + T3`, both outputs are 0. -/
theorem computeT2_const_when_clamped (T123 T123' T1 T3 : Int)
    (h1 : T123 < T1 + T3) (h2 : T123' < T1 + T3) :
    computeT2 T123 T1 T3 = computeT2 T123' T1 T3 := by
  rw [computeT2_eq_zero T123 T1 T3 h1, computeT2_eq_zero T123' T1 T3 h2]

-- ============================================================
-- § 9  Cross-function: `computeT2` composed with `computeT3Scaled`
-- ============================================================

/-- The combined total `T1 + computeT2 + computeT3Scaled` is always non-negative
    when `T1 ≥ 0`. -/
theorem total_T_nonneg (T123 T1 a0 jMax : Int) (hT1 : 0 ≤ T1) :
    0 ≤ T1 + computeT2 T123 T1 (computeT3Scaled T1 a0 jMax) +
        computeT3Scaled T1 a0 jMax := by
  have h2 : 0 ≤ computeT2 T123 T1 (computeT3Scaled T1 a0 jMax) :=
    computeT2_nonneg T123 T1 (computeT3Scaled T1 a0 jMax)
  have h3 : 0 ≤ computeT3Scaled T1 a0 jMax := computeT3Scaled_nonneg T1 a0 jMax
  omega

/-- When T123 is large enough to accommodate T1 and computeT3Scaled, the total schedule
    equals T123: `T1 + computeT2 T123 T1 T3Scaled + T3Scaled = T123`. -/
theorem total_T_eq_T123 (T123 T1 a0 jMax : Int)
    (hfit : T1 + computeT3Scaled T1 a0 jMax ≤ T123) :
    T1 + computeT2 T123 T1 (computeT3Scaled T1 a0 jMax) +
        computeT3Scaled T1 a0 jMax = T123 := by
  rw [computeT2_eq_diff T123 T1 (computeT3Scaled T1 a0 jMax) hfit]; omega

/-- The partition identity for the full schedule using `computeT3Scaled`:
    `T1 + T2 + T3Scaled = max T123 (T1 + T3Scaled)`. -/
theorem total_T_partition (T123 T1 a0 jMax : Int) :
    T1 + computeT2 T123 T1 (computeT3Scaled T1 a0 jMax) +
        computeT3Scaled T1 a0 jMax =
    max T123 (T1 + computeT3Scaled T1 a0 jMax) := by
  have h := computeT2_partition T123 T1 (computeT3Scaled T1 a0 jMax)
  omega

/-- When `jMax > 0` and T1 increases, the T3 phase grows (by `computeT3Scaled_mono_T1`)
    and the T1 phase grows, so the coasting T2 phase shrinks in both directions. -/
theorem T2_decreases_as_T3_grows (T123 T1 T1' a0 jMax : Int)
    (hjMax : 0 < jMax) (hle : T1 ≤ T1') :
    computeT2 T123 T1' (computeT3Scaled T1' a0 jMax) ≤
    computeT2 T123 T1  (computeT3Scaled T1  a0 jMax) := by
  have hT3mono : computeT3Scaled T1 a0 jMax ≤ computeT3Scaled T1' a0 jMax :=
    computeT3Scaled_mono_T1 T1 T1' a0 jMax hjMax hle
  -- Step 1: increasing T1 (with fixed T3 = T3') shrinks T2.
  have step1 : computeT2 T123 T1' (computeT3Scaled T1' a0 jMax) ≤
               computeT2 T123 T1  (computeT3Scaled T1' a0 jMax) :=
    computeT2_anti_T1 T123 T1 T1' (computeT3Scaled T1' a0 jMax) hle
  -- Step 2: increasing T3 (from T1's T3 to T1's T3) shrinks T2.
  have step2 : computeT2 T123 T1 (computeT3Scaled T1' a0 jMax) ≤
               computeT2 T123 T1  (computeT3Scaled T1 a0 jMax) :=
    computeT2_anti_T3 T123 T1 (computeT3Scaled T1 a0 jMax) (computeT3Scaled T1' a0 jMax) hT3mono
  exact Int.le_trans step1 step2

-- ============================================================
-- § 10  Additional corollaries: T2 decreasing as a0 or jMax grows
-- ============================================================

/-- Larger initial acceleration (fixed T1, fixed jMax) → longer T3Scaled → shorter T2.

    `a0` increasing raises the scaled phase-3 duration (`computeT3Scaled_mono_a0`),
    which in turn squeezes the coasting phase (`computeT2_anti_T3`). -/
theorem T2_decreases_as_a0_grows (T123 T1 a0 a0' jMax : Int) (hle : a0 ≤ a0') :
    computeT2 T123 T1 (computeT3Scaled T1 a0' jMax) ≤
    computeT2 T123 T1 (computeT3Scaled T1 a0  jMax) :=
  computeT2_anti_T3 T123 T1 (computeT3Scaled T1 a0 jMax) (computeT3Scaled T1 a0' jMax)
    (computeT3Scaled_mono_a0 T1 a0 a0' jMax hle)

/-- Higher jerk limit (with `T1 ≥ 0`) → longer T3Scaled → shorter T2.

    When `jMax` increases and `T1 ≥ 0`, the scaled phase-3 duration grows
    (`computeT3Scaled_mono_jMax`), which squeezes the coasting phase (`computeT2_anti_T3`). -/
theorem T2_decreases_as_jMax_grows (T123 T1 a0 jMax jMax' : Int)
    (hT1 : 0 ≤ T1) (hle : jMax ≤ jMax') :
    computeT2 T123 T1 (computeT3Scaled T1 a0 jMax') ≤
    computeT2 T123 T1 (computeT3Scaled T1 a0 jMax) :=
  computeT2_anti_T3 T123 T1 (computeT3Scaled T1 a0 jMax) (computeT3Scaled T1 a0 jMax')
    (computeT3Scaled_mono_jMax T1 a0 jMax jMax' hT1 hle)

-- ============================================================
-- § 11  Total schedule duration is monotone in T1
-- ============================================================

/-- **Total schedule monotonicity**: when T1 grows (with `jMax > 0`), the total
    schedule duration `max T123 (T1 + T3Scaled)` is non-decreasing.

    By `total_T_partition`, the total schedule is `max T123 (T1 + computeT3Scaled T1 a0 jMax)`.
    Since `T1 + computeT3Scaled` is monotone in `T1` when `jMax > 0`, the max is too. -/
theorem total_T_mono_T1 (T123 T1 T1' a0 jMax : Int)
    (hjMax : 0 < jMax) (hle : T1 ≤ T1') :
    max T123 (T1  + computeT3Scaled T1  a0 jMax) ≤
    max T123 (T1' + computeT3Scaled T1' a0 jMax) := by
  have hT3 : computeT3Scaled T1 a0 jMax ≤ computeT3Scaled T1' a0 jMax :=
    computeT3Scaled_mono_T1 T1 T1' a0 jMax hjMax hle
  have hA : T1 + computeT3Scaled T1 a0 jMax ≤ T1' + computeT3Scaled T1' a0 jMax := by omega
  by_cases h : T123 ≤ T1 + computeT3Scaled T1 a0 jMax
  · rw [Int.max_eq_right h]
    exact Int.le_trans hA (Int.le_max_right _ _)
  · rw [Int.max_eq_left (by omega)]
    exact Int.le_max_left _ _

-- ============================================================
-- § 12  Total schedule lower bounds and further monotonicity
-- ============================================================

/-- The total schedule `T1 + T2 + T3Scaled` is always ≥ `T123`.

    Proof: by `total_T_partition`, total = `max T123 (T1 + T3Scaled) ≥ T123`. -/
theorem total_T_ge_T123 (T123 T1 a0 jMax : Int) :
    T123 ≤ T1 + computeT2 T123 T1 (computeT3Scaled T1 a0 jMax) +
           computeT3Scaled T1 a0 jMax := by
  rw [total_T_partition]
  exact Int.le_max_left _ _

/-- The total schedule is always ≥ `T1 + T3Scaled`.

    Proof: by `total_T_partition`, total = `max T123 (T1 + T3Scaled) ≥ T1 + T3Scaled`. -/
theorem total_T_ge_T1_T3 (T123 T1 a0 jMax : Int) :
    T1 + computeT3Scaled T1 a0 jMax ≤
    T1 + computeT2 T123 T1 (computeT3Scaled T1 a0 jMax) +
         computeT3Scaled T1 a0 jMax := by
  rw [total_T_partition]
  exact Int.le_max_right _ _

/-- **Iff characterisation**: `computeT2 = 0` exactly when `T123 ≤ T1 + T3`.

    The clamp fires (returning 0) iff the requested total duration is too short to
    accommodate phases 1 and 3.  This is the canonical boundary condition for the
    coast-phase check in the trajectory planner. -/
theorem computeT2_zero_iff (T123 T1 T3 : Int) :
    computeT2 T123 T1 T3 = 0 ↔ T123 ≤ T1 + T3 := by
  unfold computeT2
  constructor
  · intro h
    by_cases hc : T123 - T1 - T3 ≤ 0
    · omega
    · rw [Int.max_eq_left (by omega)] at h; omega
  · intro h
    rw [Int.max_eq_right (by omega)]

/-- **Total schedule is monotone in `a0`**: larger initial acceleration → longer T3Scaled
    → total schedule `max T123 (T1 + T3Scaled)` is non-decreasing.

    Combines `computeT3Scaled_mono_a0` and the max-monotone argument. -/
theorem total_T_mono_a0 (T123 T1 a0 a0' jMax : Int) (hle : a0 ≤ a0') :
    max T123 (T1 + computeT3Scaled T1 a0 jMax) ≤
    max T123 (T1 + computeT3Scaled T1 a0' jMax) := by
  have hT3 : computeT3Scaled T1 a0 jMax ≤ computeT3Scaled T1 a0' jMax :=
    computeT3Scaled_mono_a0 T1 a0 a0' jMax hle
  have hA : T1 + computeT3Scaled T1 a0 jMax ≤ T1 + computeT3Scaled T1 a0' jMax := by omega
  by_cases h : T123 ≤ T1 + computeT3Scaled T1 a0 jMax
  · rw [Int.max_eq_right h]
    exact Int.le_trans hA (Int.le_max_right _ _)
  · rw [Int.max_eq_left (by omega)]
    exact Int.le_max_left _ _

/-- **Total schedule is monotone in `jMax`** (when `T1 ≥ 0`): higher jerk limit →
    longer T3Scaled → total schedule `max T123 (T1 + T3Scaled)` is non-decreasing.

    Combines `computeT3Scaled_mono_jMax` and the max-monotone argument. -/
theorem total_T_mono_jMax (T123 T1 a0 jMax jMax' : Int)
    (hT1 : 0 ≤ T1) (hle : jMax ≤ jMax') :
    max T123 (T1 + computeT3Scaled T1 a0 jMax) ≤
    max T123 (T1 + computeT3Scaled T1 a0 jMax') := by
  have hT3 : computeT3Scaled T1 a0 jMax ≤ computeT3Scaled T1 a0 jMax' :=
    computeT3Scaled_mono_jMax T1 a0 jMax jMax' hT1 hle
  have hA : T1 + computeT3Scaled T1 a0 jMax ≤ T1 + computeT3Scaled T1 a0 jMax' := by omega
  by_cases h : T123 ≤ T1 + computeT3Scaled T1 a0 jMax
  · rw [Int.max_eq_right h]
    exact Int.le_trans hA (Int.le_max_right _ _)
  · rw [Int.max_eq_left (by omega)]
    exact Int.le_max_left _ _

end PX4.VelocitySmoothing
