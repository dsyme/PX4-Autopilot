# Informal Specification: `math::deadzone`

**Source**: `src/lib/mathlib/math/Functions.hpp`

🔬 *Lean Squad automated formal verification.*

---

## Purpose

`deadzone(value, dz)` implements a **piecewise-linear deadzone function** used in
RC input processing to create a "null zone" around the centre of a joystick/stick
input. Inputs near zero (within the deadzone) are mapped to exactly zero, preventing
small stick deflections from producing any output. Outside the deadzone the function
rescales the remaining range linearly so the output still spans the full `[-1, 1]`
interval.

```
 1              ------
              /
           --
         /
-1 ------
       -1  -dz  +dz  1
```

---

## Signature

```cpp
template<typename T>
const T deadzone(const T &value, const T &dz)
```

| Parameter | Domain       | Description                                                 |
|-----------|--------------|-------------------------------------------------------------|
| `value`   | `[-1, 1]`    | Normalised input (typically stick position)                 |
| `dz`      | `[0, 0.99]`  | Deadzone ratio — fraction of the full span that maps to 0   |

**Return type**: same as `T` (typically `float`)

---

## C++ Implementation

```cpp
T x   = constrain(value, (T)-1, (T)1);
T dzc = constrain(dz, (T)0, (T)0.99);
T out = (x - matrix::sign(x) * dzc) / (1 - dzc);
return out * (fabsf(x) > dzc);
```

Key details:
- `value` is clamped to `[-1, 1]` and `dz` to `[0, 0.99]` before use.
- `matrix::sign(x)` returns `+1` if `x ≥ 0`, `-1` if `x < 0` (or uses the C++ sign
  function which returns `0` for `x = 0`, but here the final `* (fabsf(x) > dzc)`
  handles the zero case).
- The Boolean `(fabsf(x) > dzc)` converts to `0` or `1`, zeroing the output in the
  deadzone.

---

## Preconditions

- `value` should be in `[-1, 1]` (enforced by internal `constrain`).
- `dz` should be in `[0, 0.99]` (enforced by internal `constrain`).
- `dz < 1` is required to avoid division by zero.

---

## Postconditions

1. **In-deadzone**: If `|value| ≤ dz` then `deadzone(value, dz) = 0`.
2. **Sign preservation**: If `value > dz` then `deadzone(value, dz) > 0`.
   If `value < -dz` then `deadzone(value, dz) < 0`.
3. **Output range**: If `|value| ≤ 1` and `0 ≤ dz < 1` then `|deadzone(value, dz)| ≤ 1`.
4. **Continuity at boundary**: `lim_{x → dz⁺} deadzone(x, dz) = 0` — the function
   is continuous; there is no jump at the edge of the deadzone.
5. **Extreme inputs map to extreme outputs**: `deadzone(1, dz) = 1` and
   `deadzone(-1, dz) = -1` for any `dz ∈ [0, 1)`.
6. **No deadzone is identity**: `deadzone(x, 0) = x` for `x ∈ [-1, 1]`.

---

## Invariants

- The function is **odd**: `deadzone(-x, dz) = -deadzone(x, dz)`.
- The function is **monotonically non-decreasing** in `value` (for fixed `dz`).
- The output is **piecewise linear** with a flat section at 0.

---

## Edge Cases

| Scenario                        | Expected behaviour                                    |
|--------------------------------|-------------------------------------------------------|
| `value = 0`, any `dz ≥ 0`     | Output is 0 (always in deadzone)                      |
| `dz = 0`                       | No deadzone; output = input (identity on `[-1, 1]`)   |
| `|value| = dz` (boundary)      | Output is 0 (inclusive deadzone)                      |
| `value = 1`, `dz < 1`          | Output is exactly 1                                   |
| `value = -1`, `dz < 1`         | Output is exactly -1                                  |
| `dz → 0.99`, `value = 1`       | Output approaches 1 (continuous at `dz = 0.99`)       |
| `value > 1` (OOB input)        | Clamped to 1 before processing                         |

---

## Concrete Examples

| `value` | `dz`  | `output`                       |
|---------|-------|-------------------------------|
| 0.0     | 0.3   | 0.0                           |
| 0.3     | 0.3   | 0.0 (at boundary)             |
| 0.5     | 0.3   | (0.5 − 0.3)/(1 − 0.3) ≈ 0.286 |
| 1.0     | 0.3   | (1 − 0.3)/(1 − 0.3) = 1.0     |
| −0.5    | 0.3   | (−0.5 + 0.3)/(1 − 0.3) ≈ −0.286 |
| −1.0    | 0.3   | (−1 + 0.3)/(1 − 0.3) = −1.0   |
| 0.5     | 0.0   | 0.5 (identity, no deadzone)   |

---

## Inferred Intent

The function exists to process pilot stick inputs before they are passed to the
control system. The deadzone removes noise and mechanical centre-offset from the
stick, and the rescaling ensures that full deflection still produces a full-range
output command. Without the rescaling, a 30% deadzone would reduce the effective
travel to 70% of full scale.

---

## Open Questions

1. **NaN/infinity**: The C++ version uses `float`/`double`. Are there safety checks
   upstream to ensure `value` and `dz` are finite? (NaN inputs would produce NaN
   output with no error.)
2. **`dz = 1` boundary**: The implementation clamps `dz` to `0.99`, but is `dz = 1`
   ever passed in practice? What would happen if it were (division by zero)?
3. **`sign` at zero**: When `x = 0`, `matrix::sign(0)` returns `0` in some
   implementations. In the deadzone code this does not matter because `0 ≤ dz` so
   the Boolean `(fabsf(0) > dzc)` is false and the whole expression is multiplied by 0.
   Correct? Worth a comment in the source.
