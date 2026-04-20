/-!
# CRC-16 Fold Property — Formal Verification

🔬 *Lean Squad automated formal verification.*

Models and proves properties of the CRC-16 checksum computation in:
  `src/drivers/gnss/septentrio/util.cpp` (`septentrio::buffer_crc16`)

This is the CCITT variant of CRC-16 (polynomial 0x1021, MSB-first), used to
verify integrity of SBF (Septentrio Binary Format) GNSS receiver packets.

**Key result**: the computation is equivalent to `List.foldl crc16Step 0 bytes`,
which immediately gives the **fold/split** (incremental computation) theorem:

```
crc16 (a ++ b) = List.foldl crc16Step (crc16 a) b
```

This property proves that streaming/chunked CRC computation is correct:
computing CRC over a buffer arriving in pieces gives the same result as
computing it all at once.

No Mathlib dependency — only the Lean 4 standard library.
-/

namespace PX4.Crc16

/-! ## C++ Source Reference

```cpp
// src/drivers/gnss/septentrio/util.cpp
uint16_t buffer_crc16(const uint8_t *data_p, uint32_t length)
{
    uint8_t  x;
    uint16_t crc = 0;
    while (length--) {
        x   = crc >> 8 ^ *data_p++;
        x  ^= x >> 4;
        crc = (uint16_t)((crc << 8) ^ (x << 12) ^ (x << 5) ^ x);
    }
    return crc;
}
```

**Correspondence**: We use Lean's `UInt8` and `UInt16` types.  These carry the
same modular arithmetic as C `uint8_t`/`uint16_t` (mod 2⁸ and mod 2¹⁶
respectively), so the model is **exact** for all inputs.

Specifically:
- `UInt8.xor` / `UInt16.xor` match C bitwise XOR
- `UInt16.shiftRight` matches C unsigned right shift (no sign extension)
- `UInt16.shiftLeft` matches C left shift (mod 2¹⁶)
- `.toUInt8` truncates low 8 bits (matches `uint8_t` assignment from `uint16_t >> 8` which is ≤ 0xFF)
- `.toUInt16` zero-extends (matches C integer promotion of `uint8_t`)

**Abstractions / omissions**:
- The C++ pointer (`data_p`) and `length` counter are replaced by a `List UInt8`.
- The `while (length--)` loop becomes `List.foldl`.
- No side effects, no pointer aliasing, no memory safety issues.
-/

/-! ## Model: per-byte step and buffer CRC -/

/-- Per-byte CRC-16 update function.

    Mirrors the C++ loop body exactly:
    ```
    x   = (crc >> 8) ^ b
    x  ^= x >> 4
    crc = (crc << 8) ^ (x << 12) ^ (x << 5) ^ x
    ```
-/
def crc16Step (crc : UInt16) (b : UInt8) : UInt16 :=
  let x  : UInt8  := (crc >>> 8).toUInt8 ^^^ b
  let x' : UInt8  := x ^^^ (x >>> 4)
  (crc <<< 8) ^^^ (x'.toUInt16 <<< 12) ^^^ (x'.toUInt16 <<< 5) ^^^ x'.toUInt16

/-- Buffer CRC-16 as a left fold over a byte list.

    This directly models `buffer_crc16(data_p, length)`:
    the initial CRC is 0 and each byte is processed with `crc16Step`. -/
def crc16 (bs : List UInt8) : UInt16 :=
  bs.foldl crc16Step 0

/-- CRC continuation: like `crc16` but starting from a given partial CRC
    rather than 0.  This is the "continue" operation used in the fold/split
    property. -/
def crc16Continue (init : UInt16) (bs : List UInt8) : UInt16 :=
  bs.foldl crc16Step init

/-! ## Theorems -/

/-- The CRC of an empty buffer is 0 (the initial state). -/
theorem crc16_nil : crc16 [] = 0 := by
  simp [crc16]

/-- The CRC of a single byte equals `crc16Step 0 b`. -/
theorem crc16_singleton (b : UInt8) : crc16 [b] = crc16Step 0 b := by
  simp [crc16]

/-- The CRC of two bytes equals applying the step function twice from 0. -/
theorem crc16_two (a b : UInt8) :
    crc16 [a, b] = crc16Step (crc16Step 0 a) b := by
  simp [crc16]

/-- The CRC of `b :: bs` equals `crc16Continue (crc16Step 0 b) bs`. -/
theorem crc16_cons (b : UInt8) (bs : List UInt8) :
    crc16 (b :: bs) = crc16Continue (crc16Step 0 b) bs := by
  simp [crc16, crc16Continue]

/-- **Fold/split theorem**: the CRC of a concatenated buffer equals continuing
    the computation from the partial CRC of the first part.

    This is the algebraic property that enables incremental / streaming CRC
    computation: a packet arriving in chunks can be checksummed on the fly,
    and the result equals checksumming the complete packet at once. -/
theorem crc16_append (a b : List UInt8) :
    crc16 (a ++ b) = crc16Continue (crc16 a) b := by
  simp [crc16, crc16Continue, List.foldl_append]

/-- Corollary: the CRC of a concatenation matches chaining `crc16Continue`. -/
theorem crc16_append_eq (a b : List UInt8) :
    crc16 (a ++ b) = b.foldl crc16Step (crc16 a) := by
  simp [crc16]

/-- Three-part split: CRC over `a ++ b ++ c` equals chaining three parts. -/
theorem crc16_append3 (a b c : List UInt8) :
    crc16 (a ++ b ++ c) =
      crc16Continue (crc16Continue (crc16 a) b) c := by
  simp [crc16, crc16Continue]

/-- `crc16Continue` with init `0` is the same as `crc16`. -/
theorem crc16Continue_zero (bs : List UInt8) :
    crc16Continue 0 bs = crc16 bs := by
  simp [crc16, crc16Continue]

/-! ## Concrete examples (verified by computation with `native_decide`) -/

/-- Empty buffer: CRC = 0. -/
example : crc16 [] = 0 := by native_decide

/-- Single byte 0xFF yields CRC = 0x1EF0 (CCITT-verified value). -/
example : crc16 [0xFF] = 0x1EF0 := by native_decide

/-- Single zero byte yields CRC = 0. -/
example : crc16 [0x00] = 0 := by native_decide

/-- Append property holds for a concrete 3-byte buffer. -/
example : crc16 ([0x01, 0x02] ++ [0x03]) =
    crc16Continue (crc16 [0x01, 0x02]) [0x03] := by
  simp [crc16, crc16Continue]

/-- CRC of a known 4-byte buffer matches its step-by-step computation. -/
example : crc16 [0xAB, 0xCD, 0xEF, 0x01] =
    crc16Step (crc16Step (crc16Step (crc16Step 0 0xAB) 0xCD) 0xEF) 0x01 := by
  native_decide

/-- The fold/split property at concrete values (streaming check). -/
example : crc16 ([0xDE, 0xAD] ++ [0xBE, 0xEF]) =
    crc16 [0xDE, 0xAD, 0xBE, 0xEF] := by
  simp [crc16]

end PX4.Crc16
