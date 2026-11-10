/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.Stack

/-!
# Rust Global Allocator Hook Contracts (`RustAlloc`)

**Checked by Lean.** Abstract separation-logic allocator interface `RustAlloc` (`pool` and per-block
ownership tokens `live p n al`) and Hoare contracts (`rustAllocSpec`, `rustDeallocSpec`,
`rustReallocSpec`, `AllocHooks`) for `__rustc::__rust_alloc`, `__rustc::__rust_dealloc`, and
`__rustc::__rust_realloc` in hook-allocator specifications. Placed CLI ELF statements execute the
linked `mallocng` allocator directly without `__rust_*` hooks (`s.status = .OutOfMemory`, DEV-CLI15;
DEV-CLI12 retired).
-/

@[expose] public section

namespace CryptoVerification.RustHeap

open Arm64 ProofLib

/-- An abstract Rust global allocator: `pool` is its private state; `live p n al` owns the live
allocation of `n` bytes at `p` made with alignment `al` (without its contents). -/
structure RustAlloc where
  pool : SepProp
  live : BitVec 64 → Nat → Nat → SepProp

/-- Stack bytes below `sp` that an allocator hook may use. -/
abbrev allocHookStack : Nat := 4096

/-- A valid non-zero-size `core::alloc::Layout` (`Layout::from_size_align`,
`library/core/src/alloc/layout.rs`): the alignment is a power of two and the size rounded up to it
is at most `isize::MAX`. -/
def LayoutOk (size align : Nat) : Prop :=
  0 < size ∧ (∃ k, align = 2 ^ k) ∧ size + align ≤ 2 ^ 63

/-- The trace event a failing allocation hook appends (tag `"rust_alloc_failed"`, empty payload). -/
def allocFailedEvent : TraceEvent := .userDefined "rust_alloc_failed" []

/-- The allocator reported a failure in the part of `sf`'s trace after `s0`'s. -/
def allocFailedIn (s0 sf : State) : Prop :=
  allocFailedEvent ∈ sf.trace.drop s0.trace.length

/-- `__rust_alloc(size = x0, align = x1)`. Ghost: `(size, align)`. Success: a fresh aligned block
(`live` token and uninitialized bytes), trace unchanged. Failure: `x0 = 0`, one `allocFailedEvent`
appended. -/
def rustAllocSpec (A : RustAlloc) : Spec (Nat × Nat) where
  pre := fun (size, align) s =>
    ⌜(s.readReg64 .x0).toNat = size ∧ (s.readReg64 .x1).toNat = align ∧ LayoutOk size align⌝ ∗
      A.pool ∗ stackAt s.sp allocHookStack
  post := fun (size, align) s0 sf =>
    A.pool ∗ stackAt s0.sp allocHookStack ∗
      (if sf.readReg64 .x0 = 0 then ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝
       else ⌜(sf.readReg64 .x0).toNat % align = 0 ∧ sf.trace = s0.trace⌝ ∗
         A.live (sf.readReg64 .x0) size align ∗ memRegion (sf.readReg64 .x0) size)

/-- `__rust_dealloc(ptr = x0, size = x1, align = x2)` of a live block. Ghost: `(ptr, size, align)`. -/
def rustDeallocSpec (A : RustAlloc) : Spec (BitVec 64 × Nat × Nat) where
  pre := fun (p, size, align) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = size ∧ (s.readReg64 .x2).toNat = align⌝ ∗
      A.pool ∗ A.live p size align ∗ memRegion p size ∗ stackAt s.sp allocHookStack
  post := fun _ s0 sf => ⌜sf.trace = s0.trace⌝ ∗ A.pool ∗ stackAt s0.sp allocHookStack

/-- `__rust_realloc(ptr = x0, old = x1, align = x2, new = x3)` of a live block whose first
`bs.length ≤ min old new` bytes are `bs`. Success: a live block of `new` bytes starting with `bs`
(the old block is consumed). Failure: `x0 = 0`, `allocFailedEvent` appended, old block unchanged.
Ghost: `(ptr, old, align, new, bs)`. -/
def rustReallocSpec (A : RustAlloc) : Spec (BitVec 64 × Nat × Nat × Nat × List (BitVec 8)) where
  pre := fun (p, old, align, new, bs) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = old ∧ (s.readReg64 .x2).toNat = align ∧
      (s.readReg64 .x3).toNat = new ∧ LayoutOk new align ∧ bs.length ≤ old ∧ bs.length ≤ new⌝ ∗
      A.pool ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
      memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗ stackAt s.sp allocHookStack
  post := fun (p, old, align, new, bs) s0 sf =>
    A.pool ∗ stackAt s0.sp allocHookStack ∗
      (if sf.readReg64 .x0 = 0 then
        ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
          A.live p old align ∗ (p ↦ₛ bs) ∗
          memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length)
       else
        ⌜(sf.readReg64 .x0).toNat % align = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live (sf.readReg64 .x0) new align ∗ (sf.readReg64 .x0 ↦ₛ bs) ∗
          memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 bs.length) (new - bs.length))

/-- The extern hooks `hooks` implement the allocator `A`. -/
structure AllocHooks (A : RustAlloc) (hooks : String → Option (State → State)) : Prop where
  alloc : HookSat hooks "__rustc::__rust_alloc" (rustAllocSpec A)
  dealloc : HookSat hooks "__rustc::__rust_dealloc" (rustDeallocSpec A)
  realloc : HookSat hooks "__rustc::__rust_realloc" (rustReallocSpec A)

/-- `[p, p + n)` is unmapped in `m`: every byte has a permission that is not `mapped`. No frame can
own such a byte (`Heap.Matches` needs a mapped, accessible cell), so an allocator may hand it out
whatever the caller's frame is. -/
def Unmapped (m : Memory) (p : BitVec 64) (n : Nat) : Prop :=
  ∀ a, InRegion p n a → (m.perm a).mapped = false

end CryptoVerification.RustHeap
