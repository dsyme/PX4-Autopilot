# Lean 4 Formal Verification — Project Report

> 🔬 *Lean Squad — automated formal verification for `dsyme/PX4-Autopilot`.*

**Status**: 🔄 ACTIVE — 251 theorems · 117 verified examples · 6 `sorry` · Lean 4.29.1

## Last Updated

- **Date**: 2026-04-18 16:30 UTC
- **Commit**: `d47f5a1929`

---

## Executive Summary

The Lean Squad has formally verified **251 named theorems and 117 concrete examples** across
**19 Lean 4 files**, covering the core mathematical utility library (`src/lib/mathlib/`),
the EKF2 ring-buffer (`src/lib/ringbuffer/`), and the `systemlib::Hysteresis` state machine
(`src/lib/hysteresis/`). Two genuine implementation bugs were discovered through formal
verification: a `signNoZero<float>` NaN safety violation and an `negate<int16_t>` involution
error. Six `sorry`-guarded theorems remain in `WrapAngle.lean` pending Mathlib support for
floor arithmetic. All other 17 targets are sorry-free, verified by `lake build` with Lean
4.29.1. The newest addition is `Hysteresis.lean` (20 theorems + 6 examples, 0 sorry),
formalising the time-delayed boolean state machine used for arming/disarming and flight-mode
transitions — including delay lower-bound, immediate-commit (zero-delay), request-cancellation,
and settlement invariants. Research for run 44 identified five new targets: `signFromBool`,
`sq`, `crc16_signature` fold property, `atmosphere` ISA model, and the Commander arming FSM.

---

## Proof Architecture

The proof files are organised into five thematic layers, mirroring the structure of PX4's
`src/lib/mathlib/` library:

```mermaid
graph TD
    L1["Layer 1: Core Math<br/>MathFunctions.lean<br/>16 theorems · 17 examples"]
    L2a["Layer 2: Signal Filters<br/>AlphaFilter · SlewRate · Deadzone · MedianFilter<br/>45 theorems · 20 examples"]
    L2b["Layer 3: Basic Curves<br/>Interpolate · Lerp · Expo · SuperExpo<br/>54 theorems · 14 examples"]
    L2c["Layer 3b: Compound Curves<br/>ExpoDeadzone · InterpolateNXY · InterpolateN<br/>36 theorems · 22 examples"]
    L4["Layer 4: Integer Utilities<br/>Negate.lean · WrapAngle.lean<br/>28 theorems (6 sorry in WrapAngle)"]
    L5["Layer 5: Statistics & Buffers<br/>WelfordMean.lean · RingBuffer.lean<br/>35 theorems · 22 examples"]
    L6["Layer 6: State Machines<br/>Hysteresis.lean<br/>20 theorems · 6 examples"]
    L1 --> L2a
    L1 --> L2b
    L2b --> L2c
    L1 --> L4
    L2a --> L5
    L2a --> L6
```

All proof files import only **Lean 4 stdlib** — no Mathlib is required (except for the
6 pending `wrapRat` theorems in `WrapAngle.lean`).

---

## What Was Verified

### Layer 1 — Core Math (1 file, 16 theorems, 17 examples)

`MathFunctions.lean` models three fundamental operations from `src/lib/mathlib/math/`:
`constrain` (clamping), `signNoZero` (signed unit), and `countSetBits` (popcount).

```mermaid
graph LR
    MF["MathFunctions.lean<br/>16 theorems · 17 examples"]
    C["constrain: 8 theorems<br/>range, idempotence, mono"]
    S["signNoZero: 6 theorems<br/>range ±1, ne_zero — 🐛 NaN bug"]
    B["countSetBits: 9 examples<br/>+ pow2 induction lemma"]
    MF --- C
    MF --- S
    MF --- B
```

**Key results**:
- `constrain_in_range`: clamped value always satisfies `lo ≤ result ≤ hi`
- `constrain_idempotent`: applying clamp twice is identical to once
- `constrain_mono`: output is monotone in the input
- `signNoZero_ne_zero`: result is always ±1 (integer model; NaN not modelled — see Findings)
- `countSetBits_pow2`: bit-count of `2^n` is always 1

### Layer 2 — Signal Filters (4 files, 45 theorems, 20 examples)

```mermaid
graph LR
    AF["AlphaFilter.lean<br/>13 theorems · 8 examples<br/>IIR filter math"]
    SR["SlewRate.lean<br/>9 theorems · 5 examples<br/>Rate-limited output"]
    DZ["Deadzone.lean<br/>13 theorems · 7 examples<br/>Deadband suppression"]
    MF["MedianFilter.lean<br/>10 theorems · 6 examples<br/>Spike-rejection filter"]
```

**Key results**:
- `alphaIterate_formula`: closed-form `state_n = target + (state₀ - target)·(1-α)ⁿ` — fully
  proved by strong induction with no Mathlib. Validates IIR convergence.
- `slewUpdate_no_overshoot_up` / `_down`: slew-rate limiter never overshoots the target.
  A key actuator safety property.
- `slewUpdate_steady_state`: when already at target, output is unchanged.
- `deadzone_out_of_zone`: zero output for input in `[-dz, dz]`.
- `deadzone_in_range`: output is always within `[-1, 1]` (no amplification of input).
- `mfMedian_mem`: the median of any window is one of the window's elements (no hallucinated values).
- `mfMedian_const`: a constant window returns that constant value.
- `mfMedian_ge_sorted_first` / `_le_sorted_last`: median lies within the sorted range
  (spike rejection property — outliers are suppressed, not amplified).

### Layer 3 — Basic Curves (4 files, 54 theorems, 14 examples)

```mermaid
graph LR
    IN["Interpolate.lean<br/>10 theorems · 8 examples<br/>Linear map + clamping"]
    LR["Lerp.lean<br/>10 theorems · 6 examples<br/>Convex combination"]
    EX["Expo.lean<br/>17 theorems<br/>RC stick curve (cubic)"]
    SE["SuperExpo.lean<br/>17 theorems<br/>Superrate curve (quota boost)"]
    EX --> SE
```

**Key results**:
- `interpolate_le_high` / `_ge_low`: range containment — output stays within `[y_low, y_high]`.
- `lerp_in_range`: interpolated value stays within `[a, b]` when `s ∈ [0,1]` and `a ≤ b`.
- `lerp_mono_s`: increasing `s` moves output toward `b` (monotone in blend factor).
- `expo_odd`: RC stick expo function is odd — `expo(-e, x) = -expo(e, x)`.
- `expo_fixed_zero`: `expo(e, 0) = 0` (zero input → zero output).
- `expo_at_one`: `expo(e, 1) = 1` (full deflection maps to full output).
- `superexpo_denom_pos`: the denominator `1 - |x|·gc` is always strictly positive — division
  by zero cannot occur.
- `superexpo_odd`: `superexpo(-v, e, g) = -superexpo(v, e, g)` — preserves stick sign symmetry.
- `superexpo_in_range`: output always in `[-1, 1]` for any rational inputs.
- `superexpo_g_zero`: when `g = 0` the function collapses exactly to `expo(v, e)`.

### Layer 3b — Compound Curves (3 files, 36 theorems, 22 examples)

These files compose or generalise the basic curves above.

```mermaid
graph LR
    EZD["ExpoDeadzone.lean<br/>9 theorems<br/>expo ∘ deadzone pipeline"]
    NXY["InterpolateNXY.lean<br/>9 theorems · 7 examples<br/>N-pt piecewise-linear (explicit breakpoints)"]
    NUN["InterpolateN.lean<br/>18 theorems · 15 examples<br/>N-pt piecewise-linear (uniform grid)"]
    IN["Interpolate.lean"] --> EZD
    IN --> NXY
    IN --> NUN
```

**Key results**:
- `expoDeadzone_zero`: `expo_deadzone(0, e, dz) = 0`.
- `expoDeadzone_in_range`: pipeline output is always in `[-1, 1]`.
- `expoDeadzone_odd`: `expo_deadzone(-v, e, dz) = -expo_deadzone(v, e, dz)` — odd symmetry
  preserved through the two-stage RC curve pipeline.
- `interp3_in_range`: 3-point NXY output always within `[min(y), max(y)]`.
- `interp3_mono_seg0` / `_seg1`: output is monotone within each piecewise-linear segment.
- `interp3_endpoint_lo` / `_hi`: clamping behaviour at both ends confirmed.
- `interpN2_at_nodes`: N=2 uniform interpolation is exact at both endpoints.
- `interpN3_continuity`: N=3 interpolation is continuous at the interior breakpoint
  (`value = 0.5` gives the same result from both segments).
- `interpN3_in_range`: N=3 output always within `[min(y₀,y₁,y₂), max(y₀,y₁,y₂)]`.
- `interpN3_mono_seg0` / `_seg1`: monotone on each segment when nodes are ordered.

### Layer 4 — Integer Utilities (2 files, 28 theorems)

```mermaid
graph LR
    NE["Negate.lean<br/>13 theorems<br/>Overflow-safe negation — 🐛 involution bug"]
    WA["WrapAngle.lean<br/>15 theorems<br/>Part 1: wrapInt (8, 0 sorry)<br/>Part 2: wrapRat (7 theorems, 6 sorry)"]
```

**Key results**:
- `negate_ne_int_min`: negate never returns `INT_MIN` on valid inputs.
- `wrapInt_in_range`: wrapped angle is always in `[lo, lo+period)`.
- `wrapInt_idempotent`: wrapping twice is the same as wrapping once.
- `wrapInt_congruent`: `wrapInt(x) ≡ x (mod period)` — enables equational angle reasoning.
- `wrapInt_periodic`: `wrapInt(x + period) = wrapInt(x)` — single-step and multi-step.

**Note**: `WrapAngle.lean` Part 2 (`wrapRat`) has 6 sorry-guarded theorems requiring
`Int.floor` from Mathlib. The integer model (Part 1) is fully proved.

### Layer 5 — Statistics & Buffers (2 files, 35 theorems, 22 examples)

```mermaid
graph LR
    WM["WelfordMean.lean<br/>11 theorems · 3 examples<br/>Online mean/variance"]
    RB["RingBuffer.lean<br/>24 theorems · 19 examples<br/>FIFO index invariants + pop model"]
```

**Key results**:
- `welfordFold_mean`: Welford online algorithm computes exactly `sum(xs)/length(xs)`.
- `welfordUpdate_M2_nonneg`: variance accumulator `M2` is always non-negative.
- `M2_nonneg`: fold-level M2 non-negativity (safety for variance extraction).
- `rbPush_count_le_size`: element count never exceeds buffer capacity (safety invariant).
- `rbPushN_full_stays_full`: once full, a buffer stays full under any sequence of pushes.
- `rbDataGetNewest_after_push`: after pushing `x`, `getNewest` returns `x` (FIFO correctness).
- `rbInit_push_count`: exactly `k` entries after `k ≤ n` pushes into an empty size-`n` buffer.
- `rbPop_count_lt`: `pop_first_older_than` always reduces entry count by at least 1.
- `rbPop_empty_when_newest`: popping the newest entry empties the buffer.
- `rbPop_count_le_size`: pop preserves the capacity invariant.
- `rbPop_then_push_count`: pop at step `i` then push yields `i + 1` entries.

---

### Layer 6 — State Machines (1 file, 20 theorems, 6 examples)

`Hysteresis.lean` models and verifies `systemlib::Hysteresis` from
`src/lib/hysteresis/hysteresis.h` — the time-delayed boolean state machine used for
arming/disarming delays, flight-mode transition settling, and sensor debouncing.

```mermaid
graph LR
    HY["Hysteresis.lean<br/>20 theorems · 6 examples<br/>Time-delayed boolean FSM"]
    C["State: HS record<br/>(state, requested, lastChange, delays)"]
    U["hysteresisUpdate<br/>Commits when dwell elapsed"]
    S["setStateAndUpdate<br/>Request + immediate eval"]
    T["setHysteresisTimeFrom<br/>Configure dwell times"]
    HY --- C
    HY --- U
    HY --- S
    HY --- T
```

**Key results**:
- `update_settled_noop`: if no pending change, `update` is the identity.
- `update_tf_delay_lb` / `update_ft_delay_lb`: if a transition committed, the dwell was met.
- `update_tf_commits` / `update_ft_commits`: dwell elapsed ⇒ transition commits.
- `update_tf_stays` / `update_ft_stays`: dwell not elapsed ⇒ state unchanged.
- `setStateAndUpdate_zero_delay_fresh`: zero-delay fresh request commits immediately.
- `setStateAndUpdate_cancel`: calling with `newState = state` cancels pending request.
- `mkHysteresis_settled`: freshly constructed object has no pending change.
- 6× concrete `native_decide` examples: zero-delay, delayed, cancellation, timer restart.

| File | Theorems | Examples | Sorry | Phase | Key result |
|------|----------|----------|-------|-------|------------|
| `MathFunctions.lean` | 16 | 17 | 0 | ✅ Phase 5 | constrain/signNoZero/countSetBits |
| `AlphaFilter.lean` | 13 | 8 | 0 | ✅ Phase 5 | IIR closed-form convergence |
| `SlewRate.lean` | 9 | 5 | 0 | ✅ Phase 5 | No-overshoot actuator safety |
| `Deadzone.lean` | 13 | 7 | 0 | ✅ Phase 5 | Deadband range containment + odd symmetry |
| `MedianFilter.lean` | 10 | 6 | 0 | ✅ Phase 5 | Spike-rejection: median membership + range |
| `Interpolate.lean` | 10 | 8 | 0 | ✅ Phase 5 | Linear map range containment |
| `Lerp.lean` | 10 | 6 | 0 | ✅ Phase 5 | Convex interpolation |
| `Expo.lean` | 17 | 0 | 0 | ✅ Phase 5 | RC stick curve odd symmetry + fixed points |
| `SuperExpo.lean` | 17 | 0 | 0 | ✅ Phase 5 | Superrate curve: denom_pos, odd, range |
| `ExpoDeadzone.lean` | 9 | 0 | 0 | ✅ Phase 5 | expo∘deadzone pipeline: range + odd symmetry |
| `InterpolateNXY.lean` | 9 | 7 | 0 | ✅ Phase 5 | 3-pt piecewise-linear: endpoints, continuity, range |
| `InterpolateN.lean` | 18 | 15 | 0 | ✅ Phase 5 | Uniform-grid N=2/N=3: continuity, mono, range |
| `Negate.lean` | 13 | 0 | 0 | ✅ Phase 5 | Overflow-safe negation — 🐛 bug found |
| `WrapAngle.lean` | 15 | 5 | 6 | 🔄 Phase 4 | wrapInt: 9 proved; wrapRat: 6 sorry (Mathlib) |
| `WelfordMean.lean` | 11 | 3 | 0 | ✅ Phase 5 | Online mean correctness |
| `RingBuffer.lean` | 24 | 19 | 0 | ✅ Phase 5 | FIFO index invariants + pop model |
| `Hysteresis.lean` | 20 | 6 | 0 | ✅ Phase 5 | Time-delayed boolean FSM: dwell lb, commit, cancel |
| `SignFromBoolSq.lean` | 17 | 5 | 0 | ✅ Phase 5 | `signFromBool` (range {-1,1}, ne_zero) + `sq` (non-neg, even, iff-zero, mul) |
| `Basic.lean` | — | — | — | ✅ | Barrel file |
| **Total** | **251** | **117** | **6** | — | **2 bugs found** |

---

## The Main Proof Chains

### AlphaFilter Convergence

```mermaid
graph LR
    A["alphaUpdate_formula<br/>(1-step recurrence)"]
    B["alphaIterate_succ<br/>(inductive step)"]
    C["alphaIterate_formula ✅<br/>state_n = target + (state₀ - target)·(1-α)ⁿ"]
    A --> B --> C
```

This is the headline result: a formally proved closed-form response for PX4's IIR filter.

### WelfordMean Correctness

```mermaid
graph LR
    W1["welford_mean_step<br/>(single update)"]
    W2["welfordFold_mean ✅<br/>mean = sum(xs)/len(xs)"]
    W1 --> W2
```

### RingBuffer FIFO Invariants

```mermaid
graph LR
    R1["rbInit_count (empty = 0)"]
    R2["rbPush_count_nonfull / _full<br/>(push semantics)"]
    R3["rbPush_count_le_size ✅<br/>(capacity invariant)"]
    R4["rbDataGetNewest_after_push ✅<br/>(FIFO correctness)"]
    R5["rbPushN_full_stays_full ✅<br/>(overflow stability)"]
    R6["rbPop_count_lt ✅<br/>(pop reduces count)"]
    R7["rbPop_empty_when_newest ✅<br/>(pop newest → empty)"]
    R1 --> R2
    R2 --> R3
    R2 --> R4
    R3 --> R5
    R3 --> R6
    R6 --> R7
```

---

## Modelling Choices and Known Limitations

All Lean models use **rational arithmetic** (`Rat`) for floating-point functions and
**`Int`** or **`Nat`** for integer/index functions. The model deliberately excludes
IEEE 754 semantics (NaN, ±∞, rounding modes).

```mermaid
graph TD
    REAL["C++ Implementation<br/>(float/double, templates, side effects)"]
    MODEL["Lean 4 Model<br/>(Rat, Int, Nat — pure functions)"]
    PROOF["Lean 4 Proofs<br/>(omega, simp, induction, decide)"]
    REAL -->|"Modelled as"| MODEL
    MODEL -->|"Proved in"| PROOF
    NOTE1["✅ Included: pure input→output mapping<br/>✅ Included: integer overflow guards<br/>✅ Included: range / monotonicity / periodicity"]
    NOTE2["⚠️ Abstracted: float → Rat<br/>⚠️ Abstracted: uint8_t → Nat with explicit %"]
    NOTE3["❌ Omitted: IEEE 754 NaN/∞<br/>❌ Omitted: float rounding error<br/>❌ Omitted: template instantiation<br/>❌ Omitted: thread safety / aliasing"]
    MODEL --- NOTE1
    MODEL --- NOTE2
    MODEL --- NOTE3
```

| Category | What's modelled | What's abstracted / omitted |
|----------|-----------------|---------------------------|
| Number types | `Int`, `Nat`, `Rat` (exact) | Float rounding, NaN, overflow for non-integer ops |
| Functions | Pure input→output | I/O, side effects, heap allocation |
| Templates | Integer instantiation | Other template parameter types |
| Bounds | Explicit preconditions | Undefined behaviour (C++ UB is implicit) |
| Concurrency | None — all sequential | Real-time preemption, uORB atomicity |

---

## Findings

### Bugs Found

#### 🐛 Bug 1 — `signNoZero<float>`: NaN returns 0 (safety violation)

- **Property expected**: `signNoZero` always returns a value in `{-1, +1}` (never 0)
- **Counterexample**: `signNoZero<float>(NaN)` returns `0` — IEEE 754 comparisons with
  NaN are all false, so `(0 ≤ NaN) - (NaN < 0) = 0 - 0 = 0`
- **Affected file**: `src/lib/mathlib/math/Functions.hpp`, function `signNoZero<float>`
- **Impact**: callers that use the result as a divisor (e.g., in attitude rate controllers)
  can divide by zero when the input is NaN
- **Filed as**: GitHub issue #12

#### 🐛 Bug 2 — `negate<int16_t>`: INT16_MAX special case involution error

- **Property expected**: `negate(negate(x)) = x` for all `int16_t` x (involution)
- **Counterexample** (via `native_decide`):
  `negate(negate(-32767)) = negate(32767) = -32768 ≠ -32767`
- **Root cause**: the C++ maps `INT16_MAX → INT16_MIN` unnecessarily. Only
  `INT16_MIN → INT16_MAX` is needed (since `-INT16_MIN` overflows). The extra case
  breaks involution at `x = -(INT16_MAX) = -32767`.
- **Affected file**: `src/lib/mathlib/math/Functions.hpp`, function `negate<int16_t>`
- **Impact**: repeated negation in control code may silently drift values
- **Filed as**: GitHub issue #21

### Formulation Issues Caught

- `wrapRat` — the initial `wrapRat` formulation used `Int.floor` without importing Mathlib,
  producing silent sorry. The file was restructured to separate the integer model (proved)
  from the rational model (sorry-guarded, awaiting Mathlib).
- `expo` — several simp proofs for concrete values (`expo_at_zero` etc.) initially failed
  on a fresh `lake build` due to missing helper lemmas. Fixed by adding `constrainRat_*_*`
  helper lemmas using `decide`.

### Positive Findings

- **`AlphaFilter` closed-form convergence** (no Mathlib): proved that the state after n
  filter updates exactly follows `state₀ + (target - state₀)·(1 - (1-α)ⁿ)` using only
  stdlib strong induction.
- **`SlewRate` no-overshoot**: formally confirms actuator slew limiter cannot overshoot.
- **`RingBuffer` capacity invariant**: `rbPush_count_le_size` mechanically verified for all
  push sequences — eliminates a class of buffer-overrun risk.
- **`interpolate` boundary consistency**: `interpolate_at_high` formally confirmed that
  `value = x_high` returns `y_high` exactly (not via the saturation branch), validating
  asymmetric boundary design.

---

## Project Timeline

```mermaid
timeline
    title FV Project Development
    section Early Runs
        Core Math : constrain, signNoZero, countSetBits (MathFunctions)
        Filters   : SlewRate, AlphaFilter, Deadzone
    section Mid Runs
        Interpolation : Interpolate, Lerp, Expo
        Bug discovery : signNoZero NaN (issue 12)
    section Later Runs
        Advanced math  : WelfordMean, WrapAngle (integer model)
        Negate bug     : negate<int16_t> involution (issue 21)
    section Recent Runs
        RingBuffer : 24 theorems, 0 sorry
        Expo fix   : fresh-build simp proofs stabilised
        CI setup   : lean-ci.yml with lake update step
        MedianFilter : spike-rejection filter, 10 theorems + 6 examples
        SuperExpo  : RC superrate curve, 17 theorems, denom_pos + odd symmetry
        ExpoDeadzone : expo∘deadzone pipeline, 9 theorems, odd symmetry proved
        InterpolateNXY : 3-pt piecewise-linear with explicit breakpoints, 9 theorems
        InterpolateN : uniform-grid N=2/N=3, 18 theorems, continuity + mono
        Hysteresis : time-delayed boolean FSM fully verified (20 theorems, 6 examples, 0 sorry)
    section Current (run 44)
        Research   : 5 new targets identified (signFromBool, sq, crc16 fold, atmosphere ISA, arming FSM)
    section Current (run 45)
        Critique   : CRITIQUE.md updated (234 theorems, 21 targets, 18 Lean files, Hysteresis/InterpolateN/NXY rows added)
        Report     : REPORT.md refreshed with run45 timestamp
    section Current
        Correspondence : CORRESPONDENCE.md now covers all 18 Lean files
    section Run 49
        SignFromBoolSq : signFromBool (7 thms, 0 sorry) + sq (10 thms, 0 sorry) — 251 total
        CRC16 spec     : buffer_crc16 fold property informal spec written (phase 2)
        Paper          : updated to 251 theorems, 19 files, 23 targets
```

---

## Toolchain

- **Prover**: Lean 4 (version 4.29.1)
- **Libraries**: Lean 4 stdlib only (Mathlib referenced in `lakefile.toml` but unavailable in CI)
- **CI**: `.github/workflows/lean-ci.yml` — runs `lake build` on every PR that touches
  `formal-verification/lean/**`; Mathlib cache keyed on `lake-manifest.json` hash
- **Build system**: Lake

### Tactic Inventory

| Tactic | Usage |
|--------|-------|
| `omega` | Integer/natural-number arithmetic, mod/div, ring-buffer index bounds |
| `simp` / `simp only [...]` | Definitional unfolding, basic rewrites |
| `decide` / `native_decide` | Fully decidable concrete propositions, concrete list examples |
| `induction` + `cases` | Structural induction over `Nat`, `List` |
| `constructor` / `intro` / `apply` | Standard goal manipulation |
| `Rat.mul_le_mul_*` | Rational arithmetic bounds (deadzone, lerp range) |
| `Int.emod_*` | Integer modular arithmetic (wrapInt congruence, periodicity) |

---

> 🔬 *This report was generated by Lean Squad automated formal verification.*
> *`lake build` verified with Lean 4.29.1. 6 `sorry` remain (WrapAngle wrapRat,
> all require Mathlib floor arithmetic). 251 theorems across 19 files.*
> *CORRESPONDENCE.md covers all 19 Lean files (23 C++ targets).*
> *Run 49: SignFromBoolSq.lean added (17 theorems, 0 sorry); crc16_fold informal spec written.*
