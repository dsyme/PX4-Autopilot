/-!
# `crc64_add_word` — Formal Verification

🔬 *Lean Squad automated formal verification.*

This file models and proves correctness properties of `crc64_add_word` from
PX4-Autopilot:

- **C source**: `src/lib/crc/crc.c`
- **Informal spec**: `formal-verification/specs/crc64_informal.md`

## C Source

```c
uint64_t crc64_add_word(uint64_t crc, uint32_t value)
{
    uint32_t i, j;
    uint8_t byte;
    const uint64_t poly = 0x42F0E1EBA9EA3693ull;

    for (j = 0; j < 4; j++) {
        byte = ((uint8_t *) &value)[j];    // little-endian: j=0 is LSB
        crc ^= (uint64_t) byte << 56u;     // byte into MSB

        for (i = 0; i < 8; i++) {
            if (crc & (1ull << 63u)) {
                crc = (uint64_t)(crc << 1u) ^ poly;
            } else {
                crc = (uint64_t)(crc << 1u);
            }
        }
    }
    return crc;
}
```

## Model

The algorithm is CRC-64-WE (ECMA-182), MSBIT-first, polynomial
`0x42F0E1EBA9EA3693`.  We model it in three layers:

1. **`crc64Step`**: one bit-iteration of the LFSR.
2. **`crc64AddByte`**: process one byte (8 `crc64Step` applications after
   XOR-ing the byte into the MSB).
3. **`crc64AddWord`**: process one `UInt32` as four bytes in little-endian
   order.

We then define `crc64Words` (fold over a list of `UInt32` words) and prove
the key **streaming / fold-split theorem**: computing CRC-64 over a
concatenation equals composing the CRC over each part.

## Key Property

`crc64Words_append`: The CRC of `xs ++ ys` starting from `init` equals
the CRC of `ys` starting from the CRC of `xs` (starting from `init`).

This is the fundamental property that justifies chunked CRC computation:
a long message can be processed in pieces and the partial CRCs composed
correctly.

## Approximations / Out of Scope

- **Endianness**: the byte extraction `((uint8_t *)&value)[j]` is
  little-endian.  The model uses explicit byte extraction via shifts.
- **UInt64 / UInt32 overflow**: modelled faithfully using Lean's `UInt64`
  / `UInt32` fixed-width arithmetic (wrapping at 2⁶⁴ / 2³²).
- **Platform ABI**: the C code uses `uint64_t` / `uint32_t`; we use Lean's
  `UInt64` / `UInt32` which have the same sizes.
-/

namespace PX4.Crc64

/-! ## CRC-64-WE polynomial and step function -/

/-- CRC-64-WE (ECMA-182) generator polynomial: `0x42F0E1EBA9EA3693`. -/
def CRC64_POLY : UInt64 := 0x42F0E1EBA9EA3693

/-- One LFSR step (MSBIT-first): shift left by 1, XOR polynomial if MSB was set. -/
def crc64Step (crc : UInt64) : UInt64 :=
  if (crc &&& 0x8000000000000000) != 0 then (crc <<< 1) ^^^ CRC64_POLY
  else crc <<< 1

/-! ## Byte-level processing -/

/-- Process one byte: XOR into MSB of CRC, then run 8 LFSR steps. -/
def crc64AddByte (crc : UInt64) (b : UInt8) : UInt64 :=
  let crc1 := crc ^^^ (b.toUInt64 <<< 56)
  (List.range 8).foldl (fun c _ => crc64Step c) crc1

/-! ## Word-level processing (uint32, little-endian byte order) -/

/-- Extract the j-th byte of a `UInt32` in little-endian order (j = 0..3). -/
def getByteLE (w : UInt32) (j : Nat) : UInt8 :=
  ((w >>> (j * 8).toUInt32) &&& 0xFF).toUInt8

/-- Process one `UInt32` word as 4 bytes in little-endian order.
    Models `crc64_add_word(crc, value)` from `crc.c`. -/
def crc64AddWord (crc : UInt64) (value : UInt32) : UInt64 :=
  (List.range 4).foldl (fun c j => crc64AddByte c (getByteLE value j)) crc

-- Sanity checks using known CRC-64-WE check value.
-- CRC-64-WE("123456789") = 0x62EC59E3F1A4F00A
-- Process ASCII "1234" (0x34333231 little-endian) then "5678" then "9"
-- Here we just verify the step function produces a non-trivial value.
#eval crc64AddWord 0 0       -- 0 (all-zero input is absorbed)
#eval crc64AddWord 0 0x31323334  -- non-trivial value

/-! ## Streaming CRC over a list of words -/

/-- CRC-64 over a list of `UInt32` words, starting from `init`. -/
def crc64Words (init : UInt64) (ws : List UInt32) : UInt64 :=
  ws.foldl crc64AddWord init

-- Sanity checks
#eval crc64Words 0 []         -- 0 (empty)
#eval crc64Words 0 [0]        -- same as crc64AddWord 0 0
#eval crc64Words 0 [1, 2]     -- two-word CRC

/-! ## Key theorem: fold-split (streaming correctness) -/

/-- **Fold-split / streaming theorem**: CRC over a concatenation equals
    composing the CRC over each part.

    `crc64Words init (xs ++ ys) = crc64Words (crc64Words init xs) ys`

    This is the fundamental property justifying chunked CRC computation:
    a large message may be processed in any partition into consecutive chunks,
    and the results composed correctly. -/
theorem crc64Words_append (init : UInt64) (xs ys : List UInt32) :
    crc64Words init (xs ++ ys) = crc64Words (crc64Words init xs) ys := by
  simp [crc64Words, List.foldl_append]

/-! ## Corollaries -/

/-- Empty list is identity: `crc64Words init [] = init`. -/
theorem crc64Words_nil (init : UInt64) :
    crc64Words init [] = init := rfl

/-- Single-word list: `crc64Words init [w] = crc64AddWord init w`. -/
theorem crc64Words_singleton (init : UInt64) (w : UInt32) :
    crc64Words init [w] = crc64AddWord init w := rfl

/-- Two-element list: CRC of `[a, b]` = CRC of `b` applied to CRC of `a`.
    Proved via `crc64Words_append` to avoid kernel evaluation of `crc64AddWord`. -/
theorem crc64Words_two (init : UInt64) (a b : UInt32) :
    crc64Words init [a, b] = crc64AddWord (crc64AddWord init a) b := by
  rw [show [a, b] = [a] ++ [b] from rfl, crc64Words_append,
      crc64Words_singleton, crc64Words_singleton]

/-- Prepend one word: `crc64Words init (w :: ws) = crc64Words (crc64AddWord init w) ws`.
    Proved via `crc64Words_append` to avoid kernel evaluation of `crc64AddWord`. -/
theorem crc64Words_cons (init : UInt64) (w : UInt32) (ws : List UInt32) :
    crc64Words init (w :: ws) = crc64Words (crc64AddWord init w) ws := by
  rw [show w :: ws = [w] ++ ws from rfl, crc64Words_append, crc64Words_singleton]

/-- CRC of `xs ++ [w]` appends one word to the running total. -/
theorem crc64Words_append_single (init : UInt64) (xs : List UInt32) (w : UInt32) :
    crc64Words init (xs ++ [w]) = crc64AddWord (crc64Words init xs) w := by
  rw [crc64Words_append, crc64Words_singleton]

/-- Three-chunk split: CRC of `xs ++ ys ++ zs` can be computed in three passes. -/
theorem crc64Words_three_chunks (init : UInt64) (xs ys zs : List UInt32) :
    crc64Words init (xs ++ ys ++ zs) =
    crc64Words (crc64Words (crc64Words init xs) ys) zs := by
  rw [crc64Words_append, crc64Words_append]

-- Concrete streaming example: use #eval to confirm both sides equal
-- (cannot use `example` as UInt64 kernel evaluation times out for 4-word inputs).
#eval crc64Words 0 [1, 2, 3, 4]
#eval crc64Words (crc64Words 0 [1, 2]) [3, 4]
-- Both produce the same value, demonstrating the fold/split property concretely.

end PX4.Crc64
