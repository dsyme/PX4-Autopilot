/-!
# RingBuffer -- Formal Verification

🔬 Lean Squad automated formal verification.

This file models and proves correctness properties of `TimestampedRingBuffer<T>`
from PX4-Autopilot's EKF2 sensor-fusion library:

- **C++ source**: `src/lib/ringbuffer/TimestampedRingBuffer.hpp`
- **Informal spec**: `formal-verification/specs/ringbuffer_informal.md`

## Model

We represent the ring-buffer **index state** as a record with machine-checked
invariants. The data array is abstracted away in Part 1; Part 2 adds a simple
typed data model.

**Key design choice**: the C++ `_first_write` flag is eliminated by initialising
`head = size - 1`, so the first `rbPush` advances to slot
`(size - 1 + 1) % size = 0`, matching C++ first-write semantics exactly.

**Abstracted away**:
- The data array type `T` (Part 2 covers a generic `alpha`)
- `pop_first_older_than` timestamp search (complex loop; deferred)
- `uint8_t` overflow (we use `Nat` with explicit `% size`)
- Thread-safety / null-pointer guards

## Proved properties

| Theorem | Statement | Status |
|---------|-----------|--------|
| `rbInit_count` | Fresh buffer has 0 entries | Proved |
| `rbInit_head_lt` | head < size for initial state | Proved |
| `rbPush_head` | head' = (head + 1) % size | Proved |
| `rbPush_head_lt` | head' < size always | Proved |
| `rbPush_tail_lt` | tail' < size always | Proved |
| `rbPush_count_le_size` | count never exceeds capacity | Proved |
| `rbPush_count_nonfull` | Non-full: count' = count + 1 | Proved |
| `rbPush_count_full` | Full: count' = size | Proved |
| `rbPush_tail_nonfull` | Non-full: tail unchanged | Proved |
| `rbPush_tail_full` | Full: tail' = (tail + 1) % size | Proved |
| `rbPushN_size` | Size invariant over any push sequence | Proved |
| `rbPushN_count_le_size` | Count bounded by size after any pushes | Proved |
| `rbPushN_head_lt` | head < size after any pushes | Proved |
| `rbInit_push_count` | k <= n pushes into empty n-buffer => count = k | Proved |
| `rbInit_full_push_count` | n pushes into empty n-buffer => count = n | Proved |
| `rbPush_full_stays_full` | Full buffer stays full after one more push | Proved |
| `rbPushN_full_stays_full` | Full buffer stays full after any pushes | Proved |
| `rbDataGetNewest_after_push` | After push x: getNewest = x | Proved |
-/

namespace PX4.RingBuffer

/-! ## Part 1: Index-level model (no data) -/

/-- Abstract ring-buffer state carrying only index/count information.
    Invariants `hhead`, `htail`, `hcnt` are machine-checked fields. -/
structure RBState where
  size  : Nat
  hsize : 0 < size
  head  : Nat
  tail  : Nat
  count : Nat
  hhead : head < size
  htail : tail < size
  hcnt  : count <= size

/-- Empty buffer of capacity `n`. Head initialised to `n - 1` so that the first
    push advances to slot 0 -- this eliminates the C++ `_first_write` flag. -/
def rbInit (n : Nat) (h : 0 < n) : RBState where
  size  := n
  hsize := h
  head  := n - 1
  tail  := 0
  count := 0
  hhead := by omega
  htail := by omega
  hcnt  := by omega

/-- Push one entry: advance head mod size; if full, evict oldest by advancing tail. -/
def rbPush (s : RBState) : RBState where
  size  := s.size
  hsize := s.hsize
  head  := (s.head + 1) % s.size
  tail  := if s.count = s.size then (s.tail + 1) % s.size else s.tail
  count := if s.count = s.size then s.size else s.count + 1
  hhead := Nat.mod_lt _ s.hsize
  htail := by
    by_cases hc : s.count = s.size
    · simp [hc]; exact Nat.mod_lt _ s.hsize
    · simp [hc]; exact s.htail
  hcnt  := by
    have := s.hcnt
    by_cases hc : s.count = s.size
    · simp [hc]
    · simp [hc]; omega

/-- Push `k` entries (ignoring data). -/
def rbPushN (s : RBState) : Nat -> RBState
  | 0     => s
  | k + 1 => rbPush (rbPushN s k)

/-! ## Field access lemmas (all `rfl`) -/

@[simp] theorem rbInit_size  (n : Nat) (h : 0 < n) : (rbInit n h).size  = n     := rfl
@[simp] theorem rbInit_head  (n : Nat) (h : 0 < n) : (rbInit n h).head  = n - 1 := rfl
@[simp] theorem rbInit_tail  (n : Nat) (h : 0 < n) : (rbInit n h).tail  = 0     := rfl
@[simp] theorem rbInit_count (n : Nat) (h : 0 < n) : (rbInit n h).count = 0     := rfl

@[simp] theorem rbPush_size (s : RBState) : (rbPush s).size = s.size := rfl
@[simp] theorem rbPush_head (s : RBState) : (rbPush s).head = (s.head + 1) % s.size := rfl
@[simp] theorem rbPush_count_eq (s : RBState) :
    (rbPush s).count = if s.count = s.size then s.size else s.count + 1 := rfl
@[simp] theorem rbPush_tail_eq (s : RBState) :
    (rbPush s).tail = if s.count = s.size then (s.tail + 1) % s.size else s.tail := rfl

@[simp] theorem rbPushN_zero (s : RBState) : rbPushN s 0 = s := rfl
@[simp] theorem rbPushN_succ (s : RBState) (k : Nat) :
    rbPushN s (k + 1) = rbPush (rbPushN s k) := rfl

/-! ## Invariant theorems -/

theorem rbInit_head_lt (n : Nat) (h : 0 < n) : (rbInit n h).head < n := by simp; omega

theorem rbPush_head_lt (s : RBState) : (rbPush s).head < s.size :=
  Nat.mod_lt _ s.hsize

theorem rbPush_tail_lt (s : RBState) : (rbPush s).tail < s.size :=
  (rbPush s).htail

theorem rbPush_count_le_size (s : RBState) : (rbPush s).count <= s.size := by
  simp only [rbPush_count_eq]
  have hcnt := s.hcnt
  by_cases hc : s.count = s.size
  · simp [hc]
  · simp [hc]; omega

/-! ## Push count/tail theorems -/

theorem rbPush_count_nonfull (s : RBState) (h : s.count < s.size) :
    (rbPush s).count = s.count + 1 := by
  simp only [rbPush_count_eq]
  have : ¬ s.count = s.size := by omega
  simp [this]

theorem rbPush_count_full (s : RBState) (h : s.count = s.size) :
    (rbPush s).count = s.size := by
  simp only [rbPush_count_eq]
  simp [h]

theorem rbPush_tail_nonfull (s : RBState) (h : s.count < s.size) :
    (rbPush s).tail = s.tail := by
  simp only [rbPush_tail_eq]
  have : ¬ s.count = s.size := by omega
  simp [this]

theorem rbPush_tail_full (s : RBState) (h : s.count = s.size) :
    (rbPush s).tail = (s.tail + 1) % s.size := by
  simp only [rbPush_tail_eq]
  simp [h]

/-! ## Multi-push invariant theorems -/

theorem rbPushN_size (s : RBState) (k : Nat) : (rbPushN s k).size = s.size := by
  induction k with
  | zero      => rfl
  | succ k ih => simp only [rbPushN_succ, rbPush_size, ih]

theorem rbPushN_count_le_size (s : RBState) (k : Nat) : (rbPushN s k).count <= s.size := by
  induction k with
  | zero      => exact s.hcnt
  | succ k ih =>
    simp only [rbPushN_succ]
    have hsize : (rbPushN s k).size = s.size := rbPushN_size s k
    calc (rbPush (rbPushN s k)).count
        <= (rbPushN s k).size := rbPush_count_le_size _
      _ = s.size             := hsize

theorem rbPushN_head_lt (s : RBState) (k : Nat) : (rbPushN s k).head < s.size := by
  induction k with
  | zero      => exact s.hhead
  | succ k ih =>
    simp only [rbPushN_succ]
    have hsize : (rbPushN s k).size = s.size := rbPushN_size s k
    calc (rbPush (rbPushN s k)).head
        < (rbPushN s k).size := rbPush_head_lt _
      _ = s.size             := hsize

/-- Pushing k <= n items into a fresh n-capacity buffer yields exactly k entries. -/
theorem rbInit_push_count (n : Nat) (h : 0 < n) (k : Nat) (hk : k <= n) :
    (rbPushN (rbInit n h) k).count = k := by
  induction k with
  | zero      => simp
  | succ k ih =>
    have ih'   : (rbPushN (rbInit n h) k).count = k := ih (by omega)
    have hsize : (rbPushN (rbInit n h) k).size  = n := rbPushN_size _ _
    have hlt   : (rbPushN (rbInit n h) k).count < (rbPushN (rbInit n h) k).size := by
      rw [ih', hsize]; omega
    simp only [rbPushN_succ]
    rw [rbPush_count_nonfull _ hlt, ih']

/-- Filling a buffer (exactly n pushes) gives count = n. -/
theorem rbInit_full_push_count (n : Nat) (h : 0 < n) :
    (rbPushN (rbInit n h) n).count = n :=
  rbInit_push_count n h n (Nat.le_refl n)

/-- A full buffer stays full after one more push. -/
theorem rbPush_full_stays_full (s : RBState) (h : s.count = s.size) :
    (rbPush s).count = s.size :=
  rbPush_count_full s h

/-- A full buffer stays full after any number of pushes. -/
theorem rbPushN_full_stays_full (s : RBState) (h : s.count = s.size) (k : Nat) :
    (rbPushN s k).count = s.size := by
  induction k with
  | zero      => exact h
  | succ k ih =>
    simp only [rbPushN_succ]
    have hsize : (rbPushN s k).size  = s.size := rbPushN_size s k
    have hfull : (rbPushN s k).count = (rbPushN s k).size := by rw [ih, hsize]
    rw [rbPush_count_full _ hfull, hsize]

/-! ## Part 2: Data model -- get_newest correctness -/

/-- Ring buffer with typed data payload. -/
structure RBData (alpha : Type) where
  idx : RBState
  buf : Fin idx.size -> alpha

variable {alpha : Type}

/-- Push entry `x`: advance head, write `x` at new head, evict oldest if full. -/
def rbDataPush (s : RBData alpha) (x : alpha) : RBData alpha :=
  { idx := rbPush s.idx
    buf := fun i =>
      if i.val = (rbPush s.idx).head
      then x
      else s.buf { val := i.val, isLt := i.isLt } }

/-- Return the most-recently-pushed entry (slot at head). -/
def rbDataGetNewest (s : RBData alpha) : alpha :=
  s.buf { val := s.idx.head, isLt := s.idx.hhead }

/-- After pushing `x`, `getNewest` returns `x`. -/
theorem rbDataGetNewest_after_push (s : RBData alpha) (x : alpha) :
    rbDataGetNewest (rbDataPush s x) = x := by
  unfold rbDataGetNewest rbDataPush
  simp

/-! ## Part 3: Concrete examples (native_decide) -/

-- Reference state: size-3 buffer
private def ex3 : RBState := rbInit 3 (by omega)

-- Count after 0..3 pushes into empty size-3 buffer
example : (rbPushN ex3 0).count = 0 := by native_decide
example : (rbPushN ex3 1).count = 1 := by native_decide
example : (rbPushN ex3 2).count = 2 := by native_decide
example : (rbPushN ex3 3).count = 3 := by native_decide

-- Head positions
example : (rbPushN ex3 1).head = 0 := by native_decide  -- first push: slot 0
example : (rbPushN ex3 2).head = 1 := by native_decide
example : (rbPushN ex3 3).head = 2 := by native_decide

-- After filling (n=3 pushes) and one overwrite push:
example : (rbPushN ex3 4).count = 3 := by native_decide  -- still full
example : (rbPushN ex3 4).head  = 0 := by native_decide  -- wrapped to slot 0
example : (rbPushN ex3 4).tail  = 1 := by native_decide  -- oldest evicted

-- After two overwrite pushes (5 total into size-3):
example : (rbPushN ex3 5).head  = 1 := by native_decide
example : (rbPushN ex3 5).tail  = 2 := by native_decide
example : (rbPushN ex3 5).count = 3 := by native_decide

end PX4.RingBuffer
