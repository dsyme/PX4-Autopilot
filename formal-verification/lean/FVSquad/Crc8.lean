/-!
# CRC-8 CRSF Fold Property — Formal Verification

🔬 *Lean Squad automated formal verification.*

Models and proves properties of the CRC-8 checksum computation in:
  `src/drivers/rc/crsf_rc/Crc8.cpp` (`Crc8Calc` / `Crc8Init`)

This is the CRC-8/DVB-S2 variant (polynomial 0xD5, MSB-first), used to verify
integrity of CRSF (Crossfire RC) protocol packets in the PX4 RC driver.

**Key result**: the computation is equivalent to `List.foldl crc8Step 0 bytes`,
which immediately gives the **fold/split** (incremental computation) theorem:

```
crc8 (a ++ b) = crc8Continue (crc8 a) b
```

This proves that chunked/streaming CRC-8 computation is correct: computing the
CRC over a buffer arriving in pieces gives the same result as computing it
all at once.

No Mathlib dependency — only the Lean 4 standard library.
-/

namespace PX4.Crc8

/-! ## C++ Source Reference

```cpp
// src/drivers/rc/crsf_rc/Crc8.cpp

// Table initialisation (poly = 0xD5, MSB-first):
void Crc8Init(const uint8_t poly)
{
    for (int idx = 0; idx < 256; ++idx) {
        uint8_t crc = idx;
        for (int shift = 0; shift < 8; ++shift) {
            crc = (crc << 1) ^ ((crc & 0x80) ? poly : 0);
        }
        crc8_lut[idx] = crc & 0xff;
    }
}

// CRC computation:
uint8_t Crc8Calc(const uint8_t *data, uint8_t size)
{
    uint8_t crc = 0;
    while (size--) {
        crc = crc8_lut[crc ^ *data++];
    }
    return crc;
}
```

**Correspondence**: We use Lean's `UInt8` type, which carries the same modular
arithmetic as C `uint8_t` (mod 2⁸), so the model is **exact** for all inputs.

Specifically:
- `UInt8.xor` / `^^^` matches C bitwise XOR
- `UInt8.shiftLeft` matches C `<<` for `uint8_t` (mod 256)
- `UInt8.and` / `&&&` matches C `&`
- `!=` on `UInt8` matches C `!= 0` comparison

**Abstractions / omissions**:
- The global LUT (`crc8_lut`) and initialisation function `Crc8Init` are replaced
  by an inline pure function `crc8LutEntry` that computes the same value.
- The C++ pointer (`data`) and `size` counter are replaced by a `List UInt8`.
- The `while (size--)` loop becomes `List.foldl`.
- No side effects, no pointer aliasing, no memory safety issues.
- The `size` parameter is `uint8_t` in C++ (max 255 bytes); the Lean model accepts
  any `List UInt8`, so it is more general.
-/

/-! ## Model: polynomial step, LUT entry, per-byte step, buffer CRC -/

/-- One iteration of the CRC-8 polynomial shift loop for polynomial 0xD5.

    Mirrors the inner body of `Crc8Init`:
    ```
    crc = (crc << 1) ^ ((crc & 0x80) ? 0xD5 : 0)
    ```
-/
def crc8PolyStep (crc : UInt8) : UInt8 :=
  (crc <<< 1) ^^^ (if crc &&& 0x80 != 0 then 0xD5 else 0)

/-- LUT entry for index `idx`: apply `crc8PolyStep` 8 times to `idx`.

    Directly models `crc8_lut[idx]` after `Crc8Init(0xD5)` — the LUT is
    the table of these values for all `idx` in [0, 255]. -/
def crc8LutEntry (idx : UInt8) : UInt8 :=
  (List.range 8).foldl (fun crc _ => crc8PolyStep crc) idx

/-- Per-byte CRC-8 update function.

    Mirrors the C++ loop body exactly:
    ```
    crc = crc8_lut[crc ^ *data++]
    ```
    The LUT lookup is replaced by `crc8LutEntry`, which computes the same value. -/
def crc8Step (crc : UInt8) (b : UInt8) : UInt8 :=
  crc8LutEntry (crc ^^^ b)

/-- Buffer CRC-8 as a left fold over a byte list.

    This directly models `Crc8Calc(data, size)`:
    the initial CRC is 0 and each byte is processed with `crc8Step`. -/
def crc8 (bs : List UInt8) : UInt8 :=
  bs.foldl crc8Step 0

/-- CRC continuation: like `crc8` but starting from a given partial CRC
    rather than 0.  Used in the fold/split property. -/
def crc8Continue (init : UInt8) (bs : List UInt8) : UInt8 :=
  bs.foldl crc8Step init

/-! ## Theorems -/

/-- The CRC of an empty buffer is 0 (the initial state). -/
theorem crc8_nil : crc8 [] = 0 := by
  simp [crc8]

/-- The CRC of a single byte equals `crc8Step 0 b`. -/
theorem crc8_singleton (b : UInt8) : crc8 [b] = crc8Step 0 b := by
  simp [crc8]

/-- The CRC of two bytes equals applying the step function twice from 0. -/
theorem crc8_two (a b : UInt8) :
    crc8 [a, b] = crc8Step (crc8Step 0 a) b := by
  simp [crc8]

/-- The CRC of `b :: bs` equals `crc8Continue (crc8Step 0 b) bs`. -/
theorem crc8_cons (b : UInt8) (bs : List UInt8) :
    crc8 (b :: bs) = crc8Continue (crc8Step 0 b) bs := by
  simp [crc8, crc8Continue]

/-- **Fold/split theorem**: the CRC of a concatenated buffer equals continuing
    the computation from the partial CRC of the first part.

    This is the algebraic property that enables incremental / streaming CRC
    computation: a CRSF packet arriving in chunks can be checksummed on the fly,
    and the result equals checksumming the complete packet at once. -/
theorem crc8_append (a b : List UInt8) :
    crc8 (a ++ b) = crc8Continue (crc8 a) b := by
  simp [crc8, crc8Continue, List.foldl_append]

/-- Corollary: the CRC of a concatenation matches chaining `crc8Continue`. -/
theorem crc8_append_eq (a b : List UInt8) :
    crc8 (a ++ b) = b.foldl crc8Step (crc8 a) := by
  simp [crc8]

/-- Three-part split: CRC over `a ++ b ++ c` equals chaining three parts. -/
theorem crc8_append3 (a b c : List UInt8) :
    crc8 (a ++ b ++ c) =
      crc8Continue (crc8Continue (crc8 a) b) c := by
  simp [crc8, crc8Continue]

/-- `crc8Continue` with init `0` is the same as `crc8`. -/
theorem crc8Continue_zero (bs : List UInt8) :
    crc8Continue 0 bs = crc8 bs := by
  simp [crc8, crc8Continue]

/-! ## Concrete examples (verified by computation with `native_decide`) -/

/-- Empty buffer: CRC = 0. -/
example : crc8 [] = 0 := by native_decide

/-- Single zero byte: CRC = 0
    (XOR with 0 gives LUT entry 0, which polynomial-steps 0 → 0). -/
example : crc8 [0x00] = 0 := by native_decide

/-- Single byte 0xFF: CRC = 0xF9 (verified by `native_decide`). -/
example : crc8 [0xFF] = 0xF9 := by native_decide

/-- Single byte 0x01: CRC = LUT entry for 0x01 XOR 0 = LUT[1]. -/
example : crc8 [0x01] = crc8Step 0 0x01 := by native_decide

/-- Append property holds for a concrete 3-byte buffer. -/
example : crc8 ([0x01, 0x02] ++ [0x03]) =
    crc8Continue (crc8 [0x01, 0x02]) [0x03] := by
  simp [crc8, crc8Continue]

/-- CRC of a known 4-byte buffer matches step-by-step computation. -/
example : crc8 [0xAB, 0xCD, 0xEF, 0x01] =
    crc8Step (crc8Step (crc8Step (crc8Step 0 0xAB) 0xCD) 0xEF) 0x01 := by
  native_decide

/-- The fold/split property at concrete values. -/
example : crc8 ([0xDE, 0xAD] ++ [0xBE, 0xEF]) =
    crc8 [0xDE, 0xAD, 0xBE, 0xEF] := by
  simp [crc8]

/-- LUT entry for index 0 is 0 (the identity for the zero-initialised state). -/
example : crc8LutEntry 0 = 0 := by native_decide

end PX4.Crc8
