/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import VerifiedLibraries.RustStd.Spec.Top

/-!
# Global Allocator Interface for Rust `std` I/O

Defines the out-of-memory-explicit allocator record `RustStdAlloc oom`, the contracts
`rustStdAllocSpec`, `rustStdDeallocSpec`, and `rustStdReallocSpec` for `__rust_alloc`,
`__rust_dealloc`, and `__rust_realloc`, and the native and hook entry bundles
`RustStdAllocEntries` and `RustStdAllocHooks`.

`RustStdAlloc oom` is indexed by an explicit policy `oom : State → State → Prop`: an allocating
call that terminates with `sf.status = .OutOfMemory` establishes `⌜oom s0 sf⌝` (unlike
`Arm64.Rust.GlobalAlloc`, whose `onOom = ⌜True⌝` discards filesystem, trace, and signal-disposition
facts, or `ProofLib.MallocngIface`, which models C `malloc` without Rust alignment). Setting
`oom := OomPreserved` and `CanAlloc := True` models an unbudgeted CLI allocator; setting
`oom := fun _ _ => False` and `CanAlloc` to a budget check models a budgeted allocator where
`AllocSeqFits` bounds an amortized-growth sequence. A normal null return is permitted only when
`NullAllowed size align` (`2 ^ 62 < size + align`) holds.

Because musl's allocator and the `std` I/O routines share the thread-local `errno` slot, `pool`
must not own `StdErrnoCell`: every contract takes `StdErrnoCell s.tpidrEl0` in the precondition
and returns `StdErrnoCell s0.tpidrEl0` with an unspecified value on normal return. Instances live
outside `Spec/` and must use genuine spatial predicates for `pool` and `live` with `pool_transport`
derived solely from `PoolPreserved`.
-/

@[expose] public section

namespace VerifiedLibraries.RustStd

open Arm64

/-! ## State Predicates -/

/-- The state fields an allocator pool may depend on: `brkStart`, `brk` and `tpidrEl0`. The
    system calls of the `std` I/O routines (`openat`, `read`, `write`, `close`, `fstat`) touch only
    registers, memory, the file system and the trace, so they keep it. -/
abbrev PoolPreserved (s s' : State) : Prop :=
  s'.brkStart = s.brkStart ∧ s'.brk = s.brk ∧ s'.tpidrEl0 = s.tpidrEl0

/-- Process state an allocator call leaves unchanged on a normal return: file system, trace,
    signal dispositions, thread pointer, heap start, oracle and symbol table. `brk` may move;
    memory changes only inside the allocator's footprint (the separation-logic frame). -/
abbrev AllocCallPreserved (s0 sf : State) : Prop :=
  sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ sf.sigActions = s0.sigActions ∧
    sf.tpidrEl0 = s0.tpidrEl0 ∧ sf.brkStart = s0.brkStart ∧ sf.oracle = s0.oracle ∧
    sf.symtab = s0.symtab

/-- Process state left unchanged when a call runs out of memory (`sf.status = .OutOfMemory`):
    file system, trace and signal dispositions. The CLI allocator's out-of-memory policy. -/
abbrev OomPreserved (s0 sf : State) : Prop :=
  sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ sf.sigActions = s0.sigActions

/-- musl's `errno` cell for thread pointer `tp`: `&__pthread_self()->errno_val`
    (`tp - 0xa4`, `struct pthread` of musl 1.2.5 on aarch64). -/
def stdErrnoAddr (tp : BitVec 64) : BitVec 64 := tp - 0xa4#64

/-- musl's `errno` cell at thread pointer `tp`, contents unspecified. The allocator and the
    `std` I/O routines share it: musl's allocator writes `ENOMEM` there (on a null return, and on
    a successful `realloc` whose `mremap` fails before it falls back to copying; `free`'s
    `munmap` / `madvise` can also set it), and the I/O routines read it after a failing system
    call. So the allocator contracts below take it as an explicit frame: owned in the pre, given
    back with an unspecified value in every normal return. It is the first conjunct of
    `StdErrCells` (`Spec/IoCommon.lean`), so a caller that owns `StdErrCells` splits it off around
    an allocator call. -/
abbrev StdErrnoCell (tp : BitVec 64) : SepProp :=
  ∃∗ e : BitVec 32, stdErrnoAddr tp ↦₃₂ e

/-! ## Layouts and Null Returns -/

/-- A valid non-zero-size Rust `core::alloc::Layout` (`Layout::from_size_align`: `0 < size`,
    `align` a power of two, `size + align ≤ 2 ^ 63`) whose alignment is at most `2 ^ 31`, the
    largest alignment musl `mallocng`'s `aligned_alloc` serves. -/
def RustLayoutOk (size align : Nat) : Prop :=
  0 < size ∧ (∃ k, align = 2 ^ k) ∧ size + align ≤ 2 ^ 63 ∧ align ≤ 2 ^ 31

/-- The only requests for which an allocator may return null on a normal return:
    `size + align > 2 ^ 62` (musl `mallocng` returns null only when
    `size + max align 16 - 16 > 2 ^ 63 - 4098`). Running out of memory is not a null return; it is
    the `.OutOfMemory` outcome. -/
def NullAllowed (size align : Nat) : Prop :=
  2 ^ 62 < size + align

/-! ## Allocator Record -/

/-- A Rust global allocator with out-of-memory policy `oom` (the fact an allocating call gives
    when it ends with `sf.status = .OutOfMemory`).
    - `pool lb lk s`: private state at `s` with `lb` budget units and `lk` blocks live.
    - `live p n al`: the live block of `n` bytes at `p` with alignment `al` (without its contents).
    - `cost n al`: the budget units one live block of layout `(n, al)` uses.
    - `CanAlloc lb lk n al`: one more request of layout `(n, al)` fits the budget at `(lb, lk)`. -/
structure RustStdAlloc (oom : State → State → Prop) where
  pool : Nat → Nat → State → SepProp
  live : BitVec 64 → Nat → Nat → SepProp
  cost : Nat → Nat → Nat
  CanAlloc : Nat → Nat → Nat → Nat → Prop
  /-- A live block is non-null, aligned, fits within `Arm64.USER_VA_LIMIT`, and has a valid layout. -/
  block_valid : ∀ p n al, live p n al ⊢
    ⌜p ≠ 0#64 ∧ p.toNat % al = 0 ∧ p.toNat + n ≤ Arm64.USER_VA_LIMIT ∧ RustLayoutOk n al⌝ ∗ live p n al
  /-- `pool` reads only the fields of `PoolPreserved`. -/
  pool_transport : ∀ lb lk s s', PoolPreserved s s' → pool lb lk s' = pool lb lk s

/-! ## Contracts

Registers follow the Rust ABI: `__rust_alloc(size = x0, align = x1)`,
`__rust_dealloc(ptr = x0, size = x1, align = x2)`, and
`__rust_realloc(ptr = x0, old = x1, align = x2, new = x3)`, returning in `x0`. The callee may use
`hookStack` bytes of stack below `sp` (`hookFrame`). Each contract reads `A.pool` at entry (`s0`)
and exit (`sf`) and frames `StdErrnoCell` at `tpidrEl0` with an unspecified exit value. -/

variable {oom : State → State → Prop}

/-- `__rust_alloc(size, align)`. Ghost: `(size, align, lb, lk)`.
    - Normal return: `AllocCallPreserved`, and either a fresh live `align`-aligned block of `size`
      uninitialized bytes with the pool at `(lb + cost size align, lk + 1)`, or null with
      `NullAllowed size align` and the pool unchanged.
    - Out of memory: `oom s0 sf`. -/
def rustStdAllocSpec (A : RustStdAlloc oom) : Spec (Nat × Nat × Nat × Nat) where
  pre := fun (size, align, lb, lk) s =>
    ⌜(s.readReg64 .x0).toNat = size ∧ (s.readReg64 .x1).toNat = align ∧
      RustLayoutOk size align ∧ A.CanAlloc lb lk size align⌝ ∗
      A.pool lb lk s ∗ StdErrnoCell s.tpidrEl0 ∗ Rust.hookFrame s.sp
  post := fun (size, align, lb, lk) s0 sf =>
    ⌜AllocCallPreserved s0 sf⌝ ∗ StdErrnoCell s0.tpidrEl0 ∗ Rust.hookFrame s0.sp ∗
      (if sf.readReg64 .x0 = 0 then ⌜NullAllowed size align⌝ ∗ A.pool lb lk sf
       else ⌜(sf.readReg64 .x0).toNat % align = 0⌝ ∗
         A.pool (lb + A.cost size align) (lk + 1) sf ∗
         A.live (sf.readReg64 .x0) size align ∗ memRegion (sf.readReg64 .x0) size)
  onOom := fun _ s0 sf => ⌜oom s0 sf⌝

/-- `__rust_dealloc(ptr, size, align)` of a live block. Ghost: `(ptr, size, align, lb, lk)`.
    Never runs out of memory (`onOom` is the default `⌜False⌝`). The pool goes to
    `(lb - cost size align, lk - 1)`. -/
def rustStdDeallocSpec (A : RustStdAlloc oom) : Spec (BitVec 64 × Nat × Nat × Nat × Nat) where
  pre := fun (p, size, align, lb, lk) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = size ∧ (s.readReg64 .x2).toNat = align⌝ ∗
      A.pool lb lk s ∗ A.live p size align ∗ memRegion p size ∗ StdErrnoCell s.tpidrEl0 ∗
      Rust.hookFrame s.sp
  post := fun (_, size, align, lb, lk) s0 sf =>
    ⌜AllocCallPreserved s0 sf⌝ ∗ A.pool (lb - A.cost size align) (lk - 1) sf ∗
      StdErrnoCell s0.tpidrEl0 ∗ Rust.hookFrame s0.sp

/-- `__rust_realloc(ptr, old, align, new)` of a live block whose first `bs.length ≤ min old new`
    bytes are `bs`. Ghost: `(ptr, old, align, new, bs, lb, lk)`. `CanAlloc lb lk new align` is
    checked with the old block still live (a moving `realloc` holds both blocks at its peak).
    - Normal return: a live block of `new` bytes starting with `bs` (the old block is consumed;
      pool at `(lb + cost new align - cost old align, lk)`), or null with `NullAllowed new align`,
      the old block unchanged and the pool unchanged.
    - Out of memory: `oom s0 sf` (the old block is not returned to the caller). -/
def rustStdReallocSpec (A : RustStdAlloc oom) :
    Spec (BitVec 64 × Nat × Nat × Nat × List (BitVec 8) × Nat × Nat) where
  pre := fun (p, old, align, new, bs, lb, lk) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = old ∧ (s.readReg64 .x2).toNat = align ∧
      (s.readReg64 .x3).toNat = new ∧ RustLayoutOk new align ∧ bs.length ≤ old ∧
      bs.length ≤ new ∧ A.CanAlloc lb lk new align⌝ ∗
      A.pool lb lk s ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
      memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗ StdErrnoCell s.tpidrEl0 ∗
      Rust.hookFrame s.sp
  post := fun (p, old, align, new, bs, lb, lk) s0 sf =>
    ⌜AllocCallPreserved s0 sf⌝ ∗ StdErrnoCell s0.tpidrEl0 ∗ Rust.hookFrame s0.sp ∗
      (if sf.readReg64 .x0 = 0 then
        ⌜NullAllowed new align⌝ ∗ A.pool lb lk sf ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
          memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length)
       else
        ⌜(sf.readReg64 .x0).toNat % align = 0⌝ ∗
          A.pool (lb + A.cost new align - A.cost old align) lk sf ∗
          A.live (sf.readReg64 .x0) new align ∗ (sf.readReg64 .x0 ↦ₛ bs) ∗
          memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 bs.length) (new - bs.length))
  onOom := fun _ s0 sf => ⌜oom s0 sf⌝

/-! ## Amortized Buffer Growth -/

/-- The successive capacities `caps` of one `align`-aligned buffer, grown by `alloc` (the first
    capacity, from no buffer) and then `realloc`s, all fit the budget starting from `(lb, lk)`:
    each request satisfies `CanAlloc` at the pool state the previous calls left. Every request
    is counted, including ones that could return null (`NullAllowed`). -/
def AllocSeqFits {oom : State → State → Prop} (A : RustStdAlloc oom) (align : Nat) :
    Nat → Nat → List Nat → Prop
  | _, _, [] => True
  | lb, lk, c :: cs => A.CanAlloc lb lk c align ∧ go (lb + A.cost c align) (lk + 1) c cs
where
  /-- After the first allocation: `prev` is the current capacity. -/
  go (lb lk prev : Nat) : List Nat → Prop
    | [] => True
    | c :: cs => A.CanAlloc lb lk c align ∧
        go (lb + A.cost c align - A.cost prev align) lk c cs

/-! ## Entry Bundles -/

/-- Entry addresses of the Rust allocator functions in a program. -/
structure RustStdAllocAddrs where
  alloc : BitVec 64
  dealloc : BitVec 64
  realloc : BitVec 64

/-- Native mode: the allocator is code in `P`, entered at `addrs`, wherever it is placed. -/
structure RustStdAllocEntries (A : RustStdAlloc oom) (P : Program) (addrs : RustStdAllocAddrs) :
    Prop where
  alloc : subroutine_ok P addrs.alloc (rustStdAllocSpec A)
  dealloc : subroutine_ok P addrs.dealloc (rustStdDeallocSpec A)
  realloc : subroutine_ok P addrs.realloc (rustStdReallocSpec A)

/-- Hook mode: the extern hooks `hooks` implement `A`. -/
structure RustStdAllocHooks (A : RustStdAlloc oom) (hooks : String → Option (State → State)) :
    Prop where
  alloc : HookSat hooks "__rustc::__rust_alloc" (rustStdAllocSpec A)
  dealloc : HookSat hooks "__rustc::__rust_dealloc" (rustStdDeallocSpec A)
  realloc : HookSat hooks "__rustc::__rust_realloc" (rustStdReallocSpec A)

end VerifiedLibraries.RustStd
