# Informal Specification: `ObstacleMath::wrap_bin`

🔬 *Lean Squad automated formal verification.*

- **C++ source**: `src/lib/collision_prevention/ObstacleMath.hpp` /
  `src/lib/collision_prevention/ObstacleMath.cpp`
- **Lean spec**: `formal-verification/lean/FVSquad/WrapBin.lean`

---

## Purpose

`wrap_bin(bin, bin_count)` wraps an integer bin index into the canonical range
`[0, bin_count)`. It is used in the collision-prevention subsystem to normalise
bin indices that may lie slightly outside `[0, bin_count)` (one above or one below)
back into a valid range before they are used as array indices.

**C++ implementation**:

```cpp
int wrap_bin(int bin, int bin_count)
{
    return (bin + bin_count) % bin_count;
}
```

---

## Preconditions

- `bin_count > 0` (must be a positive number of bins).
- Callers in `ObstacleMath` pass inputs that satisfy `-(bin_count - 1) ≤ bin ≤ bin_count`.
  This ensures the sum `bin + bin_count` is always positive, so C++ truncation semantics
  coincide with mathematical modulo.

---

## Postconditions (Intended)

The result should be the unique integer `r` such that:
1. `0 ≤ r < bin_count`
2. `r ≡ bin (mod bin_count)`

That is, `wrap_bin` should return the mathematical (Euclidean) modulo of `bin` by
`bin_count`.

---

## Invariants

- **Range invariant** (over the valid caller domain): when `-(bin_count-1) ≤ bin ≤ bin_count`,
  the result lies in `[0, bin_count)`.
- **Identity for in-range inputs**: when `0 ≤ bin < bin_count`, `wrap_bin bin bin_count = bin`.
- **Wrap for bin = -1**: `wrap_bin (-1) n = n - 1` (one-below wraps to the last bin).
- **Wrap for bin = bin_count**: `wrap_bin n n = 0` (one-above wraps to the first bin).

---

## Edge Cases

### In-range: `0 ≤ bin < bin_count`

`(bin + bin_count) % bin_count = bin % bin_count = bin` since `n ≤ bin + bin_count < 2n`.

### One below zero: `bin = -1`

`(-1 + bin_count) % bin_count = (bin_count - 1) % bin_count = bin_count - 1`. Correct.

### At bin_count: `bin = bin_count`

`(bin_count + bin_count) % bin_count = 2*bin_count % bin_count = 0`. Correct.

### **BUG — Two or more below zero: `bin ≤ -bin_count`**

For `bin = -bin_count`: `(-bin_count + bin_count) % bin_count = 0 % bin_count = 0`. Still correct.

For `bin = -bin_count - 1`: `(-bin_count - 1 + bin_count) % bin_count = (-1) % bin_count`.

In **C++**, `%` uses truncation-toward-zero semantics, so `(-1) % n = -1` for any `n > 0`.
This gives `-1`, which is **outside** `[0, bin_count)` and would be used as a negative
array index — undefined behaviour (UB) and likely a crash or memory corruption.

In **Lean 4**, `%` on `Int` also uses truncation-toward-zero (matching C++), so the same
latent bug is observable in the Lean model.

---

## Examples

| `bin` | `bin_count` | `(bin + n) % n` (C++/Lean) | Expected | Correct? |
|-------|-------------|----------------------------|----------|----------|
| 0 | 72 | 0 | 0 | ✓ |
| 71 | 72 | 71 | 71 | ✓ |
| 72 | 72 | 0 | 0 | ✓ |
| 73 | 72 | 1 | 1 | ✓ |
| -1 | 72 | 71 | 71 | ✓ |
| -72 | 72 | 0 | 0 | ✓ |
| **-73** | **72** | **-1** | 71 | **✗ BUG** |

---

## Inferred Intent

The function is intended to normalise bin indices that may be slightly out of range
(typically by at most one step in either direction, or one full wrap above). The design
only handles the typical usage pattern; it does not handle deeply negative inputs.

All actual callers in `ObstacleMath` guarantee the precondition
`-(bin_count - 1) ≤ bin ≤ bin_count`, so the bug is **latent** (does not trigger in
current callers). However the API contract expressed in the doc-comment says
"wraps a bin index to the range `[0, bin_count)`" with no restriction on `bin`, which
overstates what the implementation guarantees.

---

## Open Questions

1. Should `wrap_bin` be defensive (handle all integer inputs)? The correct general
   implementation is `((bin % n) + n) % n` (two mod operations, always non-negative
   when `n > 0`). Should the implementation be fixed?
2. Are there any callers that could pass `bin ≤ -bin_count`? Static analysis would
   confirm whether the latent bug can actually trigger.

---

## Relation to Lean Spec

The Lean file `WrapBin.lean` provides:
- A direct model of the C++ implementation using Lean's truncation-mod `Int.mod` (which
  matches C++ `%` semantics for integers).
- Proofs that the model is correct within the valid caller precondition domain.
- A proof-by-counterexample that the model violates the range property for `bin ≤ -bin_count`.
- The `wrapBinOffset_valid` theorem showing current callers are safe.
