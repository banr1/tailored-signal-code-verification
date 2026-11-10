/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.RustHeap.Alloc

/-!
# State-Indexed Rust Allocator Interface

State-indexed, OOM-aware contract (`RustCliAlloc`) between caller proofs invoking the Rust global
allocator (`__rust_alloc`, `__rust_dealloc`, `__rust_realloc`) and the linked `musl` `mallocng`
implementation:
* **State-indexed pool:** `pool s` depends only on `brkStart`, `brk`, and `tpidrEl0`
  (`PoolPreserved`), so it transports across register writes, memory stores, branches, and
  non-`brk` syscalls or hooks.
* **Out-of-memory outcome:** `alloc` and `realloc` may terminate in `.OutOfMemory` preserving
  `OomPreserved`; `dealloc` never runs out of memory.
* **Null returns:** normal returns yield null only when `NullAllowed size align`
  (`2 ^ 62 < size + align`), never as an out-of-memory report.
* **Alignment bound:** `RustLayoutOk` caps alignment at `2 ^ 31` (`MaxAlignedAllocAlign`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Heap

open Arm64 ProofLib
open CryptoVerification.RustHeap (RustAlloc LayoutOk allocHookStack)

/-! ## State Predicates -/

/-- The state fields an allocator pool may depend on: `brkStart`, `brk` and `tpidrEl0`. Caller
code that does not call the allocator leaves all three unchanged (unlike
`Arm64.Rust.VmPreserved`, the page permissions are not included: the allocator's own pages are
owned inside `pool`, so stores and caller `mmap`s do not disturb it). -/
abbrev PoolPreserved (s s' : State) : Prop :=
  s'.brkStart = s.brkStart ∧ s'.brk = s.brk ∧ s'.tpidrEl0 = s.tpidrEl0

theorem PoolPreserved.refl (s : State) : PoolPreserved s s := ⟨rfl, rfl, rfl⟩

theorem PoolPreserved.trans {s₁ s₂ s₃ : State}
    (h12 : PoolPreserved s₁ s₂) (h23 : PoolPreserved s₂ s₃) : PoolPreserved s₁ s₃ :=
  ⟨h23.1.trans h12.1, h23.2.1.trans h12.2.1, h23.2.2.trans h12.2.2⟩

/-- Process state an allocator call leaves unchanged when it returns normally: file system,
trace, signal dispositions, thread pointer, heap start, oracle and symbol table (musl
`mallocng`'s `MallocngProcPreserved`). `brk` may move; memory changes only inside the
allocator's footprint (the separation-logic frame). -/
def AllocCallPreserved (s0 sf : State) : Prop :=
  sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ sf.sigActions = s0.sigActions ∧
    sf.tpidrEl0 = s0.tpidrEl0 ∧ sf.brkStart = s0.brkStart ∧ sf.oracle = s0.oracle ∧
    sf.symtab = s0.symtab

/-- Process state an allocator call leaves unchanged when it runs out of memory
(`sf.status = .OutOfMemory`): file system, trace and signal dispositions. -/
def OomPreserved (s0 sf : State) : Prop :=
  sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ sf.sigActions = s0.sigActions

/-! ## Layouts -/

/-- A valid non-zero-size Rust `core::alloc::Layout` (`LayoutOk`: `0 < size`, `align` a power of
two, `size + align ≤ 2 ^ 63`) whose alignment is at most `2 ^ 31`. Larger alignments are valid
Rust layouts but musl `mallocng` cannot serve them; libsignal never asks for them. -/
def RustLayoutOk (size align : Nat) : Prop :=
  LayoutOk size align ∧ align ≤ 2 ^ 31

/-- The only requests for which an allocator may return null on a normal return:
`size + align > 2 ^ 62` (musl `mallocng` returns null only when
`size + max align 16 - 16 > 2 ^ 63 - 4098`). Running out of memory is not a null return; it is
the `.OutOfMemory` outcome. -/
def NullAllowed (size align : Nat) : Prop :=
  2 ^ 62 < size + align

/-! ## Allocator Structure -/

/-- A Rust global allocator with state-indexed private state.
* `pool s`: the allocator's private state (metadata, free lists, its pages) in machine state `s`;
* `live p n al`: ownership of the live block of `n` bytes at `p` allocated with alignment `al`
  (without its contents, which are separate `memRegion` / `↦ₛ` resources). -/
structure RustCliAlloc where
  pool : State → SepProp
  live : BitVec 64 → Nat → Nat → SepProp
  /-- A live block is non-null, aligned, fits below `2 ^ 64`, and has a layout the allocator
  accepts (so `dealloc` / `realloc` of a live block need no further layout check). -/
  block_valid : ∀ p n al, live p n al ⊢
    ⌜p ≠ 0#64 ∧ p.toNat % al = 0 ∧ p.toNat + n < 2 ^ 64 ∧ RustLayoutOk n al⌝ ∗ live p n al
  /-- `pool` reads only the fields of `PoolPreserved`. -/
  pool_transport : ∀ s s' : State, PoolPreserved s s' → pool s' = pool s

namespace RustCliAlloc

variable (A : RustCliAlloc)

/-- `A` at machine state `s`, as a `RustAlloc` with a constant pool. -/
def atState (s : State) : RustAlloc := { pool := A.pool s, live := A.live }

/-- `A`'s live-block tokens as a `RustAlloc`, for predicates that read only `live` (`vecU8`,
`boxAt`, ...). Its `pool` is `emp`: never pass `repAlloc` to `rustAllocSpec` or any other
contract that reads `pool`; use `atState` or the `rustCli*Spec` contracts below. -/
def repAlloc : RustAlloc := { pool := emp, live := A.live }

@[simp] theorem atState_pool (s : State) : (A.atState s).pool = A.pool s := rfl
@[simp] theorem atState_live (s : State) : (A.atState s).live = A.live := rfl
@[simp] theorem repAlloc_live : A.repAlloc.live = A.live := rfl

variable {A}

theorem pool_of_preserved {s0 sf : State} (h : PoolPreserved s0 sf) : A.pool sf = A.pool s0 :=
  A.pool_transport s0 sf h

@[simp] theorem pool_setMem (s : State) (m : Memory) : A.pool (s.setMem m) = A.pool s :=
  A.pool_transport _ _ ⟨rfl, rfl, rfl⟩
@[simp] theorem pool_setPC (s : State) (pc : BitVec 64) : A.pool (s.setPC pc) = A.pool s :=
  A.pool_transport _ _ ⟨rfl, rfl, rfl⟩
@[simp] theorem pool_advancePC (s : State) : A.pool s.advancePC = A.pool s :=
  A.pool_transport _ _ ⟨rfl, rfl, rfl⟩
@[simp] theorem pool_setPState (s : State) (ps : PState) : A.pool (s.setPState ps) = A.pool s :=
  A.pool_transport _ _ ⟨rfl, rfl, rfl⟩
@[simp] theorem pool_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    A.pool (s.writeReg64 r v) = A.pool s :=
  A.pool_transport _ _ ⟨rfl, rfl, rfl⟩
@[simp] theorem pool_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    A.pool (s.writeReg32 r v) = A.pool s :=
  A.pool_transport _ _ ⟨rfl, rfl, rfl⟩
@[simp] theorem pool_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    A.pool (s.writeReg w r v) = A.pool s :=
  A.pool_transport _ _ ⟨rfl, rfl, rfl⟩
@[simp] theorem pool_writeVReg128 (s : State) (i : BitVec 5) (v : BitVec 128) :
    A.pool (s.writeVReg128 i v) = A.pool s :=
  A.pool_transport _ _ ⟨rfl, rfl, rfl⟩
@[simp] theorem pool_writeVReg64 (s : State) (i : BitVec 5) (v : BitVec 64) :
    A.pool (s.writeVReg64 i v) = A.pool s :=
  A.pool_transport _ _ ⟨rfl, rfl, rfl⟩
@[simp] theorem pool_writeVReg32 (s : State) (i : BitVec 5) (v : BitVec 32) :
    A.pool (s.writeVReg32 i v) = A.pool s :=
  A.pool_transport _ _ ⟨rfl, rfl, rfl⟩

end RustCliAlloc

/-! ## Allocator Call Contracts

Register and ghost conventions follow `rustAllocSpec`, `rustDeallocSpec`, and `rustReallocSpec`,
reading the pool at entry (`A.pool s0`) and exit (`A.pool sf`). -/

/-- `__rust_alloc(size = x0, align = x1)` (`zeroed = false`) and
`__rust_alloc_zeroed(size, align)` (`zeroed = true`). Ghost: `(size, align)`.
* Normal return: `AllocCallPreserved`, the pool at `sf`, and either a fresh live `align`-aligned
  block of `size` bytes (uninitialized, or zero bytes if `zeroed`), or null with
  `NullAllowed size align`.
* Out of memory: allowed on every call (`OomPreserved`). -/
def rustCliAllocSpec (A : RustCliAlloc) (zeroed : Bool) : Spec (Nat × Nat) where
  pre := fun (size, align) s =>
    ⌜(s.readReg64 .x0).toNat = size ∧ (s.readReg64 .x1).toNat = align ∧
      RustLayoutOk size align⌝ ∗
      A.pool s ∗ stackAt s.sp allocHookStack
  post := fun (size, align) s0 sf =>
    ⌜AllocCallPreserved s0 sf⌝ ∗ A.pool sf ∗ stackAt s0.sp allocHookStack ∗
      (if sf.readReg64 .x0 = 0 then ⌜NullAllowed size align⌝
       else ⌜(sf.readReg64 .x0).toNat % align = 0⌝ ∗ A.live (sf.readReg64 .x0) size align ∗
         (if zeroed then (sf.readReg64 .x0 ↦ₛ List.replicate size 0#8)
          else memRegion (sf.readReg64 .x0) size))
  onOom := fun _ s0 sf => ⌜OomPreserved s0 sf⌝

/-- `__rust_dealloc(ptr = x0, size = x1, align = x2)` of a live block. Ghost: `(ptr, size, align)`.
Never runs out of memory (`onOom` is the default `False`). -/
def rustCliDeallocSpec (A : RustCliAlloc) : Spec (BitVec 64 × Nat × Nat) where
  pre := fun (p, size, align) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = size ∧ (s.readReg64 .x2).toNat = align⌝ ∗
      A.pool s ∗ A.live p size align ∗ memRegion p size ∗ stackAt s.sp allocHookStack
  post := fun _ s0 sf =>
    ⌜AllocCallPreserved s0 sf⌝ ∗ A.pool sf ∗ stackAt s0.sp allocHookStack

/-- `__rust_realloc(ptr = x0, old = x1, align = x2, new = x3)` of a live block whose first
`bs.length ≤ min old new` bytes are `bs`. Ghost: `(ptr, old, align, new, bs)`.
* Normal return: a live block of `new` bytes starting with `bs` (the old block is consumed), or
  null with `NullAllowed new align` and the old block unchanged.
* Out of memory: allowed on every call (`OomPreserved`). -/
def rustCliReallocSpec (A : RustCliAlloc) :
    Spec (BitVec 64 × Nat × Nat × Nat × List (BitVec 8)) where
  pre := fun (p, old, align, new, bs) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = old ∧ (s.readReg64 .x2).toNat = align ∧
      (s.readReg64 .x3).toNat = new ∧ RustLayoutOk new align ∧ bs.length ≤ old ∧
      bs.length ≤ new⌝ ∗
      A.pool s ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
      memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗ stackAt s.sp allocHookStack
  post := fun (p, old, align, new, bs) s0 sf =>
    ⌜AllocCallPreserved s0 sf⌝ ∗ A.pool sf ∗ stackAt s0.sp allocHookStack ∗
      (if sf.readReg64 .x0 = 0 then
        ⌜NullAllowed new align⌝ ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
          memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length)
       else
        ⌜(sf.readReg64 .x0).toNat % align = 0⌝ ∗ A.live (sf.readReg64 .x0) new align ∗
          (sf.readReg64 .x0 ↦ₛ bs) ∗
          memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 bs.length) (new - bs.length))
  onOom := fun _ s0 sf => ⌜OomPreserved s0 sf⌝

/-! ## Hook and Subroutine Bundles -/

/-- Hook-mode bundle asserting that extern `hooks` implement `A`. -/
structure RustCliAllocHooks (A : RustCliAlloc) (hooks : String → Option (State → State)) :
    Prop where
  alloc : HookSat hooks "__rustc::__rust_alloc" (rustCliAllocSpec A false)
  dealloc : HookSat hooks "__rustc::__rust_dealloc" (rustCliDeallocSpec A)
  realloc : HookSat hooks "__rustc::__rust_realloc" (rustCliReallocSpec A)

/-- Entry addresses of the Rust allocator functions in a program. -/
structure RustAllocAddrs where
  alloc : BitVec 64
  dealloc : BitVec 64
  realloc : BitVec 64

/-- Native subroutine bundle asserting that `P` implements `A` at `addrs`. -/
structure RustCliAllocEntries (A : RustCliAlloc) (P : Program) (addrs : RustAllocAddrs) :
    Prop where
  alloc : subroutine_ok P addrs.alloc (rustCliAllocSpec A false)
  dealloc : subroutine_ok P addrs.dealloc (rustCliDeallocSpec A)
  realloc : subroutine_ok P addrs.realloc (rustCliReallocSpec A)

/-! ## Inhabitation Check

Non-`emp` consistency witness for `RustCliAlloc`; the `musl` `mallocng` instance is constructed in
`LibsignalBinary.Heap.MallocngInst`. -/

private def witnessAlloc : RustCliAlloc where
  pool := fun s => ⌜s.brk = s.brkStart ∧ s.tpidrEl0 ≠ 0#64⌝
  live := fun p n al =>
    ⌜p ≠ 0#64 ∧ p.toNat % al = 0 ∧ p.toNat + n < 2 ^ 64 ∧ RustLayoutOk n al⌝ ∗ emp
  block_valid := by
    intro p n al
    refine Entails.pure_left fun h => ?_
    exact Entails.pure_right h (Entails.pure_right h (Entails.refl _))
  pool_transport := by
    rintro s s' ⟨hbs, hb, ht⟩
    simp only [hbs, hb, ht]

example : ∃ A : RustCliAlloc, A.pool = witnessAlloc.pool := ⟨witnessAlloc, rfl⟩

end LibsignalBinary.Heap
