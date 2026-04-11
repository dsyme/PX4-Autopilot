# Informal Specification: TimestampedRingBuffer

🔬 *Lean Squad automated formal verification.*

**Source**: `src/lib/ringbuffer/TimestampedRingBuffer.hpp`
**Target**: `TimestampedRingBuffer<data_type>`

---

## Purpose

`TimestampedRingBuffer<T>` is a fixed-capacity circular buffer for timestamped sensor
samples. Its primary contract is FIFO ordering with bounded memory: once full, pushing a
new sample silently overwrites the oldest sample. Samples carry a `time_us` field
(microseconds since epoch); `time_us == 0` acts as a sentinel meaning "slot is empty".

The buffer is used throughout the EKF2 and sensor fusion stack to hold windows of recent
sensor measurements for time-alignment. For example, `ekf2/Ekf2.cpp` uses it to buffer
IMU data and optical flow samples so that observations can be aligned to a common time
base.

---

## Data Model

Abstractly, the buffer is:

- A fixed-capacity array of `T` of length `n` (`n = _size`)
- A **head** pointer (index of the most recently inserted slot)
- A **tail** pointer (index of the oldest valid slot)
- A **first-write** flag indicating the buffer has never been written to

The physical layout is a ring: indices `0, 1, ..., n-1` wrap modulo `n`.

---

## Preconditions

### Construction / `allocate`
- `size > 0`: a zero-size buffer is invalid. `allocate(0)` returns `false`.
- Memory must be available for `new data_type[size]`.

### `push`
- `valid() == true`: buffer was successfully allocated and not de-allocated.

### `get_newest` / `get_oldest`
- `valid() == true`
- At least one sample has been pushed (i.e., `!_first_write` or there is a write in progress).
  Calling on a freshly-reset buffer is technically safe (returns `_buffer[0]`) but
  yields a zero-initialised / garbage element.

### `pop_first_older_than`
- `valid() == true`
- `sample` is a non-null pointer to a `T` object.

---

## Postconditions

### `push(s)`

Let `n = _size`. After `push(s)`:

1. **New head**: `_head' = _head + 1 (mod n)` when at least one prior write has occurred;
   `_head' = _head = 0` on the very first write (the `_first_write` flag avoids
   advancing the head before the first write).
2. **Sample stored**: `_buffer[_head'] = s`.
3. **Tail advance on overwrite**: if `_head' == _tail` after the head advance (buffer was
   full), then `_tail' = (_tail + 1) % n`. This evicts the oldest sample.
4. **FIFO property**: the sequence accessible from tail to head (in circular order) is
   a suffix of all ever-pushed samples; the oldest accessible sample is at most `n` pushes
   behind the newest.

### `get_newest()`
- Returns `_buffer[_head]`, which is the most recently pushed sample.

### `get_oldest()`
- Returns `_buffer[_tail]`, which is the oldest retained sample.

### `pop_first_older_than(ts, sample)`

Returns `true` iff there exists an index `i` (scanning newest-to-oldest) such that:

  `_buffer[i].time_us ≤ ts < _buffer[i].time_us + 1e5`

When such an entry is found:
- `*sample = _buffer[i]`
- `_buffer[i].time_us = 0` (invalidated)
- Tail advances to `(i + 1) % n` (all older entries are discarded)
- `true` is returned

When no such entry is found: `*sample` is unchanged; buffer state is unchanged; `false`
is returned.

**Note on the 1e5 window**: the time match window is hard-coded as 100 ms (100,000 µs).
This means a call at time `ts` will accept a sample whose timestamp falls anywhere in
`[ts - 99999, ts]` µs (approximately). This is the EKF2 sample-association tolerance.

### `reset()`
- All slots are zero-initialised.
- `_head = 0`, `_tail = 0`, `_first_write = true`.
- Postcondition: `entries() == 0`.

### `entries()`
- Returns the count of slots whose `time_us != 0`.
- **Note**: this is NOT the count of ever-pushed samples. It counts occupied slots after
  zeroing by `pop_first_older_than`. A freshly-pushed buffer of size `n` with no pops
  will have `entries() = n` (since `time_us` is set to non-zero by the push).

---

## Invariants

1. **Index bounds**: `_head < _size` and `_tail < _size` always hold (modular
   arithmetic maintains this after any sequence of pushes).

2. **Capacity bound**: the number of distinct valid slots (those reachable by scanning
   from `_tail` to `_head` in circular order) is always ≤ `_size`.

3. **Valid before use**: `_buffer != nullptr` and `_size > 0` (guaranteed by
   `allocate` returning `true`).

4. **Overwrite semantics**: the buffer never blocks; a push always succeeds, at the cost
   of silently discarding the oldest entry when full.

5. **Zeroed sentinel**: `time_us == 0` means "empty or invalidated slot". Callers must
   ensure `time_us != 0` for valid samples (this is not enforced by the buffer itself).

---

## Edge Cases

1. **Single-element buffer** (`n = 1`): every push overwrites the sole slot; `_head = _tail = 0`
   always; `get_newest() == get_oldest()`.

2. **First push** (`_first_write = true`): the head does *not* advance; the sample is
   written to slot 0. `_first_write` is cleared. Subsequent pushes advance the head normally.

3. **Pop on empty buffer**: `pop_first_older_than` returns `false` immediately if no
   matching timestamp is found. It does not block or assert.

4. **Pop of the newest element** (`index == _head`): the tail is set to `_head` and
   `_first_write = true`, effectively resetting the buffer to empty.

5. **`entries()` vs capacity**: `entries()` counts non-zero `time_us` fields, not the
   logical occupancy. If a caller pushes a sample with `time_us = 0`, `entries()` will
   under-count. This is a caller contract, not a buffer invariant.

6. **Zero-size `allocate(0)`**: returns `false`; `_buffer` is deleted; `valid()` becomes
   `false`. No further operations should be performed.

---

## Examples

### Push / Overwrite

```
Buffer size = 3. Push samples A(t=1), B(t=2), C(t=3), D(t=4).

After A: buffer=[A,_,_], head=0, tail=0
After B: buffer=[A,B,_], head=1, tail=0
After C: buffer=[A,B,C], head=2, tail=0  (full)
After D: buffer=[D,B,C], head=0, tail=1  (overwrote A; tail advances to 1)
         => get_newest() = D, get_oldest() = B
```

### Pop First Older Than

```
Buffer = [D(t=4), B(t=2), C(t=3)], head=0, tail=1
pop_first_older_than(ts=3):
  Scan from head=0: D(t=4): 4 > 3+100000? No. 3 >= 4? No — skip.
  Next: C(t=3): 3 <= 3 < 3+100000 => MATCH.
    *sample = C; buffer[2].time_us = 0; tail = (2+1)%3 = 0
  Returns true.
```

---

## Inferred Intent

1. **Nearest-but-not-newer lookup**: `pop_first_older_than` is designed for
   time-domain association: given a reference time `ts`, find the freshest sample that
   could have been measured *at or before* `ts`. The 100 ms window prevents stale
   associations while tolerating moderate clock misalignment.

2. **Latency bound**: because the tail advances on pop (discarding all older samples),
   repeated calls to `pop_first_older_than` with non-decreasing timestamps always make
   forward progress and never return duplicate samples.

3. **Not thread-safe**: there are no locks or atomics. Callers must serialize access.

4. **`uint8_t` size/index arithmetic**: `_head`, `_tail`, and `_size` are `uint8_t`,
   so the buffer can hold at most 255 elements. This is a deliberate embedded footprint
   constraint.

---

## Open Questions for Maintainers

1. **`time_us == 0` sentinel contract**: is it guaranteed that all valid pushed samples
   have `time_us != 0`? If a sensor failure leads to `time_us = 0`, the slot will appear
   "empty" to `entries()` and to `pop_first_older_than`. Should there be an explicit
   assert or check in `push`?

2. **Behaviour of `push` on `!valid()`**: the code does not guard against `push` when
   `_buffer == nullptr`. This would be a null-dereference. Should there be a validity
   check at the top of `push`?

3. **Intent of `get_length()`**: it returns `_size` (total capacity), not the number of
   populated entries. Is this naming intentional? `entries()` returns the latter.

4. **100 ms window hard-coding**: the `(uint64_t)1e5` window in `pop_first_older_than`
   is hard-coded. Is this a configuration parameter that should be exposed, or is it an
   architectural constant for EKF2?

5. **`uint8_t` capacity limit**: the 255-element cap is embedded in `uint8_t`
   field types. Is this ever a limitation for high-rate sensors (e.g., 2 kHz IMU would
   fill 255 samples in ~128 ms)?

---

## FV Approach Notes

- **Primary target**: formal model should focus on the index-arithmetic invariants
  and the FIFO property. These are purely integer/modular-arithmetic properties, well
  suited to `omega` proofs.
- **Key theorems to target**:
  - `push_advances_head_mod_n`: `new_head = (old_head + 1) % n` (after first write)
  - `entries_le_size`: at most `n` entries are ever reachable from tail to head
  - `get_newest_is_last_pushed`: after `push(s)`, `get_newest() = s`
  - `get_oldest_is_fifo`: oldest accessible sample is the one pushed earliest among
    currently retained samples
  - `pop_clears_older`: after a successful pop, `tail ≥ matched_index + 1 (mod n)`
- **Abstraction**: model the buffer as a `Fin n → T` array with `Nat` head/tail indices.
  Eliminate the `_first_write` flag by treating it as `head = tail ∧ not yet written`.
- **`pop_first_older_than` is complex**: the timestamp-matching search and concurrent
  tail advance interact. Model the pop as a pure function on the abstract state, then
  prove the invariants are maintained.
- **`uint8_t` arithmetic**: to avoid overflow in proofs, model indices as `Nat` with
  explicit `% n` reductions. The `omega` tactic handles these naturally.
