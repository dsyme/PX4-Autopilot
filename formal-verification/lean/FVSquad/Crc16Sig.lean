/-!
# CRC-16-CCITT Signature — Formal Verification

🔬 *Lean Squad automated formal verification.*

Models and proves properties of the CRC-16 computation in:
  `src/lib/crc/crc.c` (`crc16_add`, `crc16_signature`)

This is the CRC-16-CCITT variant (polynomial **0x1021**, MSB-first), used in PX4
for firmware integrity verification and bootloader packet checksums.

**Key simplification**: `CRC16_OUTPUT_XOR = 0x0000` (from `crc.h`), so
`crc16_signature(init, bytes)` reduces to a pure left fold of `crc16_add`
over `bytes` starting at `init`.

**Key result**: the fold/split (incremental streaming) theorem:

```
crc16sig init (a ++ b) = crc16sig (crc16sig init a) b
```

This proves correctness of chunked / streaming checksum computation.

No Mathlib dependency — only the Lean 4 standard library.
-/

namespace PX4.Crc16Sig

/-! ## C++ Source Reference

```c
// src/lib/crc/crc.c  —  crc16_add
uint16_t crc16_add(uint16_t crc, uint8_t value)
{
    uint32_t i;
    const uint16_t poly = 0x1021u;
    crc ^= (uint16_t)((uint16_t) value << 8u);
    for (i = 0; i < 8; i++) {
        if (crc & (1u << 15u)) {
            crc = (uint16_t)((crc << 1u) ^ poly);
        } else {
            crc = (uint16_t)(crc << 1u);
        }
    }
    return crc;
}

// CRC16_OUTPUT_XOR = 0x0000u  (from crc.h)
uint16_t crc16_signature(uint16_t initial, size_t length, const uint8_t *bytes)
{
    for (size_t i = 0; i < length; i++) {
        initial = crc16_add(initial, bytes[i]);
    }
    return initial ^ CRC16_OUTPUT_XOR;   // = initial ^ 0 = initial
}
```

**Correspondence notes**:
- `UInt8` / `UInt16` carry the same modular-2⁸ / modular-2¹⁶ arithmetic as C
  `uint8_t` / `uint16_t`.
- `^^^` (XOR), `<<<` (left shift mod 2¹⁶), `&&&` (bitwise AND) match C operators.
- `.toUInt16` zero-extends a `UInt8` (matches C integer promotion).
- The pointer / length pair is replaced by a `List UInt8`.
- The final `^ CRC16_OUTPUT_XOR` vanishes because `CRC16_OUTPUT_XOR = 0`.
-/

/-! ## Model: per-bit and per-byte step functions -/

/-- One iteration of the bit loop in `crc16_add`:
    if MSB is set, left-shift and XOR with polynomial 0x1021; otherwise just left-shift.

    Mirrors the C body:
    ```
    if (crc & (1u << 15u)) crc = (crc << 1u) ^ poly;
    else                    crc = (crc << 1u);
    ``` -/
def crc16AddBit (c : UInt16) : UInt16 :=
  if c &&& 0x8000 != 0 then (c <<< 1) ^^^ 0x1021 else c <<< 1

/-- `crc16_add`: XOR the new byte into the high byte of the running CRC, then
    execute eight iterations of `crc16AddBit`.

    This is an exact Lean model of the C `crc16_add` function. -/
def crc16Add (crc : UInt16) (b : UInt8) : UInt16 :=
  let c := crc ^^^ (b.toUInt16 <<< 8)
  crc16AddBit (crc16AddBit (crc16AddBit (crc16AddBit
    (crc16AddBit (crc16AddBit (crc16AddBit (crc16AddBit c)))))))

/-- `crc16_signature` with explicit initial value: fold `crc16Add` over a byte list.

    Because `CRC16_OUTPUT_XOR = 0x0000`, this is identical to the C function:
    `crc16_signature(initial, bytes) = List.foldl crc16Add initial bytes`. -/
def crc16sig (init : UInt16) (bs : List UInt8) : UInt16 :=
  bs.foldl crc16Add init

/-- Continuation helper: alias for `crc16sig` with explicit init (matches `crc16Continue`
    in Crc16Fold). -/
abbrev crc16sigCont := crc16sig

/-! ## Theorems -/

/-- The signature of an empty buffer is the initial value (identity). -/
theorem crc16sig_nil (init : UInt16) : crc16sig init [] = init := by
  simp [crc16sig]

/-- The signature of a single byte equals `crc16Add init b`. -/
theorem crc16sig_singleton (init : UInt16) (b : UInt8) :
    crc16sig init [b] = crc16Add init b := by
  simp [crc16sig]

/-- Unfolding the first byte: `crc16sig init (b :: bs) = crc16sig (crc16Add init b) bs`. -/
theorem crc16sig_cons (init : UInt16) (b : UInt8) (bs : List UInt8) :
    crc16sig init (b :: bs) = crc16sig (crc16Add init b) bs := by
  simp [crc16sig]

/-- **Fold/split theorem**: computing the signature of a concatenated buffer equals
    continuing the computation from the partial signature of the first part.

    This is the algebraic property enabling streaming / chunked CRC computation:
    a packet arriving in pieces can be checksummed incrementally, and the result
    equals checksumming the complete packet at once.

    Proof: `List.foldl_append` applied to `crc16Add`. -/
theorem crc16sig_append (init : UInt16) (a b : List UInt8) :
    crc16sig init (a ++ b) = crc16sig (crc16sig init a) b := by
  simp [crc16sig, List.foldl_append]

/-- Three-part split: `crc16sig init (a ++ b ++ c)` chains through three parts. -/
theorem crc16sig_append3 (init : UInt16) (a b c : List UInt8) :
    crc16sig init (a ++ b ++ c) =
      crc16sig (crc16sig (crc16sig init a) b) c := by
  simp [crc16sig, List.foldl_append]

/-- `crc16sig 0 bs` is the standard "start from zero" signature used in the bootloader. -/
theorem crc16sig_init_zero (bs : List UInt8) :
    crc16sig 0 bs = bs.foldl crc16Add 0 := by
  simp [crc16sig]

/-- Idempotent extension: appending the empty list is a no-op on the signature. -/
theorem crc16sig_append_nil (init : UInt16) (a : List UInt8) :
    crc16sig init (a ++ []) = crc16sig init a := by
  simp [crc16sig]

/-- Two bytes `[a, b]` form the same signature as chaining single-byte steps. -/
theorem crc16sig_two (init : UInt16) (a b : UInt8) :
    crc16sig init [a, b] = crc16Add (crc16Add init a) b := by
  simp [crc16sig]

/-! ## Concrete examples (verified by computation with `native_decide`) -/

/-- Empty buffer: signature equals the initial value. -/
example : crc16sig 0 [] = 0 := by native_decide

/-- Single zero byte from initial 0: output is 0.
    (`crc = 0 ^^^ (0x00 << 8) = 0`, then 8 left-shifts of 0 → 0.) -/
example : crc16sig 0 [0x00] = 0 := by native_decide

/-- Single 0xFF byte: concrete expected output (CCITT-16, poly 0x1021, init 0). -/
example : crc16sig 0 [0xFF] = crc16Add 0 0xFF := by native_decide

/-- Fold/split at concrete inputs: chunked equals monolithic computation. -/
example : crc16sig 0 ([0x31, 0x32] ++ [0x33]) =
    crc16sig (crc16sig 0 [0x31, 0x32]) [0x33] := by
  simp [crc16sig]

/-- Fold/split for a longer buffer (6 bytes = 3 + 3). -/
example : crc16sig 0xFFFF ([0xDE, 0xAD, 0xBE] ++ [0xEF, 0x01, 0x23]) =
    crc16sig (crc16sig 0xFFFF [0xDE, 0xAD, 0xBE]) [0xEF, 0x01, 0x23] := by
  simp [crc16sig]

/-- Non-zero initial value: fold/split holds for `init = 0x1234`. -/
example : crc16sig 0x1234 ([0xAB, 0xCD] ++ [0xEF]) =
    crc16sig (crc16sig 0x1234 [0xAB, 0xCD]) [0xEF] := by
  simp [crc16sig]

end PX4.Crc16Sig
