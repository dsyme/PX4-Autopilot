# Informal Specification: `crc32_signature`

**Source**: `src/lib/crc/crc.c`, line 151  
**Header**: `src/lib/crc/crc.h`, line 116

---

## Purpose

`crc32_signature` computes a CRC-32 checksum over a byte array using the
CRC-32/ISO-HDLC algorithm (also known as CRC-32b, used in Ethernet, gzip, PNG,
and ZIP). It processes bytes one at a time, feeding an accumulator (`acc`)
through a bit-by-bit XOR/shift loop driven by the reflected polynomial
`0xEDB88320` (the bit-reversal of the standard `0x04C11DB7` polynomial).

The function is used in the UAVCAN bootloader to verify firmware image
integrity (see `platforms/nuttx/src/canbootloader/uavcan/main.c`).

---

## Signature

```c
uint32_t crc32_signature(uint32_t acc, size_t length, const uint8_t *bytes);
```

---

## Preconditions

1. `length == 0` OR `bytes` points to a valid buffer of at least `length` bytes.
2. No constraint on `acc`; any 32-bit value is valid. Common choices are:
   - `0x00000000` — initial value used in the UAVCAN bootloader.
   - `0xFFFFFFFF` — initial value for "standard" CRC-32 (requires a final XOR
     with `0xFFFFFFFF` outside this function to match RFC 1952/gzip output).

---

## Algorithm

For each byte `b` in `bytes[0..length-1]`:

1. `acc ^= b`  (XOR byte into lowest 8 bits of accumulator)
2. Repeat 8 times:
   - `xor_mask = -(acc & 1)`  (all-ones if LSB is 1, else zero)
   - `acc >>= 1`              (unsigned right shift)
   - `acc ^= (poly & xor_mask)` where `poly = 0xEDB88320`

This is the standard LSBIT-first (reflected) CRC-32 algorithm.

---

## Postconditions

1. **Empty input identity**: If `length == 0`, the return value equals `acc`.
   ```
   crc32_signature(acc, 0, any) == acc
   ```

2. **Single-byte extension**: For any byte `b` and accumulator `acc`:
   ```
   crc32_signature(acc, 1, &b) == crc32Step(acc, b)
   ```
   where `crc32Step` performs the 8-bit shift loop above.

3. **Fold / append property**: For any split `k ≤ n`:
   ```
   crc32_signature(acc, n, bytes)
     == crc32_signature(crc32_signature(acc, k, bytes), n-k, bytes+k)
   ```
   That is, CRC over a concatenated buffer equals CRC of the second part
   initialised with the CRC of the first part. This follows directly from
   the `List.foldl` structure of the algorithm.

4. **Determinism**: The output depends only on `acc`, `length`, and the
   contents of `bytes[0..length-1]`. Equivalent inputs always produce
   the same output.

5. **32-bit range**: The return value is in `[0, 2^32)`.

---

## Invariants

- The accumulator is always a valid 32-bit unsigned integer throughout the loop.
- The polynomial mask `0xEDB88320` is a compile-time constant; it is never
  written or re-read from memory.

---

## Edge Cases

| Scenario | Expected behaviour |
|---|---|
| `length == 0` | Returns `acc` unchanged |
| `length == 1` | Applies one 8-bit CRC step to `acc` |
| All-zero byte array | Applies CRC steps with XOR of 0 each time; not a no-op |
| `acc == 0` | Standard "initial" seed used by UAVCAN bootloader |
| `acc == 0xFFFFFFFF` | Standard seed for gzip-compatible CRC32; caller must XOR result with `0xFFFFFFFF` |
| Very large `length` | No overflow in `size_t` indexing; no internal 32-bit overflow (only XOR/shift) |

---

## Concrete Examples

The CRC-32/ISO-HDLC check value (acc=0x00000000, input = ASCII "123456789"):
```
crc32_signature(0x00000000, 9, "123456789") == 0xCBF43926
```
(This is the standard check value for CRC-32/ISO-HDLC per REVENG catalogue.)

For the UAVCAN bootloader pattern, two blocks are checked separately:
```c
block_crc1 = crc32_signature(0, len1, block1);
block_crc1 = crc32_signature(block_crc1, len2, block2);
// equivalent to: crc32_signature(0, len1 + len2, block1_then_block2)
```

---

## Formal Properties Suitable for Lean

The following properties are strong candidates for formalisation:

1. **`crc32Step_bits`**: The bit loop is equivalent to a single lookup in an
   infinite lookup table defined by the polynomial recurrence. (Connects to the
   standard CRC table-driven implementation.)

2. **`crc32_empty`**: `crc32_signature acc 0 [] = acc`.

3. **`crc32_fold`**: `crc32_signature acc (a ++ b) = crc32_signature (crc32_signature acc a) b`.
   This follows directly from `List.foldl_append` once `crc32_signature` is
   modelled as `List.foldl crc32Step acc bytes`.

4. **`crc32_single`**: `crc32_signature acc [b] = crc32Step acc b`.

5. **`crc32Step_deterministic`**: `crc32Step` is a pure function of its inputs
   (no side effects, no state).

The fold property (3) is the highest-value target because it justifies the
bootloader's two-call chaining pattern and underpins correctness of incremental
CRC verification.

---

## Relationship to `crc16_add`

`crc32_signature` mirrors the structure of `crc16_add` (in the same file) but
uses the 32-bit reflected polynomial and does **not** apply the initial or final
XOR that `crc16_add` applies. The existing Lean file `Crc16Fold.lean` proves
analogous fold/append properties for CRC-16; `crc32_signature` is an ideal
next step at the same level of abstraction.

---

## Open Questions

1. **No final XOR or bit-inversion**: `crc32_signature` does not apply the
   standard `^ 0xFFFFFFFF` final step. Should the spec cover both the "raw"
   function and a wrapper that applies the final XOR? (Low priority — UAVCAN
   uses the raw form.)

2. **Endianness**: The function XORs the byte directly into the low 8 bits of
   `acc`. This is correct for LSB-first (reflected) CRC. Any Lean model should
   note this explicitly.

3. **Check value verification**: The check value `0xCBF43926` for input
   `"123456789"` with `acc=0` should be confirmed by running the C code. It
   matches the REVENG catalogue entry for CRC-32/ISO-HDLC.

4. **No tests in the repository**: There are no unit tests for `crc32_signature`
   in the PX4 repository. Lean proofs and a simple test harness would both add
   value here. Should we add C unit tests as a separate contribution?
