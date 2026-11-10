/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.GlobalAlloc
public import ProofLib.Abi.Rust.Heap
public import ProofLib.Invariant
public import ProofLib.SepLogic.WP

/-!
# Global Allocator Bridges and Transport Lemmas

Bridges `Arm64.Rust.GlobalAlloc` to `ProofLib.RustHeap`, providing block-validity projections,
`Vec` / `Box` representation conversions, `@[simp]` `VmPreserved` heap-transport rules, and
non-null postcondition specializations under `BudgetOk`.
-/

@[expose] public section

namespace ProofLib.GlobalAlloc

open Arm64 Arm64.Rust ProofLib

/-! ## Smart Constructor and Block Validity -/

theorem noWrap_of_block_valid
    {Block : BitVec 64 → Nat → Nat → SepProp}
    (hvalid : ∀ (p : BitVec 64) (size align : Nat),
      Block p size align ⊢
        ⌜p ≠ 0#64 ∧ p.toNat % align = 0 ∧ p.toNat + size ≤ 2 ^ 64⌝ ∗ Block p size align)
    (p : BitVec 64) (size align : Nat) :
    Block p size align ⊢ ⌜p.toNat + size ≤ 2 ^ 64⌝ ∗ Block p size align := by
  refine Entails.trans (hvalid p size align) ?_
  apply Entails.pure_left
  rintro ⟨_, _, hnw⟩
  exact Entails.pure_right hnw (Entails.refl _)

/-- Smart constructor for `Arm64.Rust.GlobalAlloc` deriving `noWrap` from `block_valid`. -/
def ofBlockValid {P : Program} {addrs : GlobalAllocAddrs}
    (Heap : Nat → Nat → State → SepProp)
    (Block : BitVec 64 → Nat → Nat → SepProp)
    (stackBytes maxGuaranteedAlign maxLiveBytes maxLiveBlocks : Nat)
    (block_valid :
      ∀ (p : BitVec 64) (size align : Nat),
        Block p size align ⊢
          ⌜p ≠ 0#64 ∧ p.toNat % align = 0 ∧ p.toNat + size ≤ 2 ^ 64⌝ ∗ Block p size align)
    (heap_transport :
      ∀ (liveBytes liveBlocks : Nat) (s s' : State),
        VmPreserved s s' →
        Heap liveBytes liveBlocks s' = Heap liveBytes liveBlocks s)
    (alloc_ok :
      subroutine_ok P addrs.alloc
        (globalAllocSpec Heap Block stackBytes maxGuaranteedAlign maxLiveBytes maxLiveBlocks))
    (alloc_zeroed_ok :
      subroutine_ok P addrs.alloc_zeroed
        (globalAllocZeroedSpec Heap Block stackBytes maxGuaranteedAlign maxLiveBytes maxLiveBlocks))
    (dealloc_ok :
      subroutine_ok P addrs.dealloc
        (globalDeallocSpec Heap Block stackBytes))
    (realloc_ok :
      subroutine_ok P addrs.realloc
        (globalReallocSpec Heap Block stackBytes maxGuaranteedAlign maxLiveBytes maxLiveBlocks)) :
    GlobalAlloc P addrs where
  Heap := Heap
  Block := Block
  stackBytes := stackBytes
  maxGuaranteedAlign := maxGuaranteedAlign
  maxLiveBytes := maxLiveBytes
  maxLiveBlocks := maxLiveBlocks
  noWrap := noWrap_of_block_valid block_valid
  block_valid := block_valid
  heap_transport := heap_transport
  alloc_ok := alloc_ok
  alloc_zeroed_ok := alloc_zeroed_ok
  dealloc_ok := dealloc_ok
  realloc_ok := realloc_ok

end ProofLib.GlobalAlloc

namespace Arm64.Rust.GlobalAlloc

open Arm64 ProofLib

variable {P : Program} {addrs : GlobalAllocAddrs}

theorem block_nonnull (A : GlobalAlloc P addrs) (p : BitVec 64) (size align : Nat) :
    A.Block p size align ⊢ ⌜p ≠ 0#64⌝ ∗ A.Block p size align := by
  refine Entails.trans (A.block_valid p size align) ?_
  apply Entails.pure_left
  rintro ⟨hne, _, _⟩
  exact Entails.pure_right hne (Entails.refl _)

theorem block_aligned (A : GlobalAlloc P addrs) (p : BitVec 64) (size align : Nat) :
    A.Block p size align ⊢ ⌜p.toNat % align = 0⌝ ∗ A.Block p size align := by
  refine Entails.trans (A.block_valid p size align) ?_
  apply Entails.pure_left
  rintro ⟨_, hal, _⟩
  exact Entails.pure_right hal (Entails.refl _)

theorem block_noWrap (A : GlobalAlloc P addrs) (p : BitVec 64) (size align : Nat) :
    A.Block p size align ⊢ ⌜p.toNat + size ≤ 2 ^ 64⌝ ∗ A.Block p size align :=
  A.noWrap p size align

/-! ## `RustAlloc`, `Vec`, and `Box` Bridges -/

/-- Lift `A : GlobalAlloc P addrs` into `ProofLib.RustHeap.RustAlloc` with pool `pool` (default
    `emp` for representation predicates `vecBuf`, `vecAt`, and `boxAt`). -/
def toRustAlloc (A : GlobalAlloc P addrs) (pool : SepProp := emp) :
    ProofLib.RustHeap.RustAlloc where
  pool := pool
  live := A.Block
  noWrap := A.noWrap

@[simp]
theorem toRustAlloc_pool (A : GlobalAlloc P addrs) (pool : SepProp) :
    (A.toRustAlloc pool).pool = pool := rfl

@[simp]
theorem toRustAlloc_live (A : GlobalAlloc P addrs) (pool : SepProp) :
    (A.toRustAlloc pool).live = A.Block := rfl

@[simp]
theorem atAlign_toRustAlloc (A : GlobalAlloc P addrs) (align : Nat) (pool : SepProp) :
    (A.toRustAlloc pool).atAlign align = A.atAlign align pool := rfl

@[simp]
theorem atAlign_live (A : GlobalAlloc P addrs) (align : Nat) (pool : SepProp) :
    (A.atAlign align pool).live = A.live align := rfl

/-- Typed `Vec<T>` buffer over `A` with element stride `stride` and alignment `align`. -/
abbrev typedVecBuf {α : Type} (A : GlobalAlloc P addrs) (stride align : Nat)
    (elem : α → BitVec 64 → SepProp) (cap ptr : BitVec 64) (xs : List α) : SepProp :=
  ProofLib.RustHeap.vecBuf (A.toRustAlloc) stride align elem cap ptr xs

/-- Typed `Vec<T>` at `v` over `A` with element stride `stride` and alignment `align`. -/
abbrev typedVecAt {α : Type} (A : GlobalAlloc P addrs) (stride align : Nat)
    (elem : α → BitVec 64 → SepProp) (v cap ptr : BitVec 64) (xs : List α) : SepProp :=
  ProofLib.RustHeap.vecAt (A.toRustAlloc) stride align elem v cap ptr xs

/-- Typed `Box<[T]>` at `ptr` over `A` with element stride `stride` and alignment `align`. -/
abbrev typedBoxAt {α : Type} (A : GlobalAlloc P addrs) (stride align : Nat)
    (elem : α → BitVec 64 → SepProp) (ptr : BitVec 64) (xs : List α) : SepProp :=
  ProofLib.RustHeap.boxAt (A.toRustAlloc) stride align elem ptr xs

theorem vecBuf_eq_rustHeap_vecU8Buf (A : GlobalAlloc P addrs) (pool : SepProp)
    (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    A.vecBuf cap ptr bs = ProofLib.RustHeap.vecU8Buf (A.toRustAlloc pool) cap ptr bs := rfl

theorem vecAt_eq_rustHeap_vecU8At (A : GlobalAlloc P addrs) (pool : SepProp)
    (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    A.vecAt v cap ptr bs = ProofLib.RustHeap.vecU8At (A.toRustAlloc pool) v cap ptr bs := rfl

theorem vecAt_eq_typedVecAt (A : GlobalAlloc P addrs)
    (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    A.vecAt v cap ptr bs = A.typedVecAt 1 1 (fun b addr => addr ↦₈ b) v cap ptr bs := by
  rw [vecAt_eq_rustHeap_vecU8At A emp]
  exact ProofLib.RustHeap.vecU8At_eq_vecAt (A.toRustAlloc emp) v cap ptr bs

/-- Collapse `A.vecBuf cap ptr bs` into the block and raw byte region expected by `A.dealloc_ok`. -/
theorem vecBuf_entails_dealloc (A : GlobalAlloc P addrs)
    (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    A.vecBuf cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ SmallLen cap.toNat ∧ ptr ≠ 0⌝ ∗
        (if cap = 0 then emp else A.Block ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) :=
  ProofLib.RustHeap.vecU8Buf_entails_dealloc (A.toRustAlloc emp) cap ptr bs

/-- Expose the header of `A.vecAt v cap ptr bs` and collapse its buffer for `A.dealloc_ok`. -/
theorem vecAt_entails_dealloc (A : GlobalAlloc P addrs)
    (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    A.vecAt v cap ptr bs ⊢
      Arm64.Rust.vecHeader v cap ptr (BitVec.ofNat 64 bs.length) ∗
        (⌜bs.length ≤ cap.toNat ∧ SmallLen cap.toNat ∧ ptr ≠ 0⌝ ∗
          (if cap = 0 then emp else A.Block ptr cap.toNat 1 ∗ memRegion ptr cap.toNat)) := by
  rw [vecAt_eq_rustHeap_vecU8At A emp]
  exact ProofLib.RustHeap.vecU8At_entails_dealloc (A.toRustAlloc emp) v cap ptr bs

/-- Collapse `A.boxAt ptr bs` into the block and raw byte region expected by `A.dealloc_ok`. -/
theorem boxAt_entails_dealloc (A : GlobalAlloc P addrs)
    (ptr : BitVec 64) (bs : List (BitVec 8)) :
    A.boxAt ptr bs ⊢
      ⌜ptr ≠ 0⌝ ∗ (if bs = [] then emp else A.Block ptr bs.length 1 ∗ memRegion ptr bs.length) := by
  unfold GlobalAlloc.boxAt Arm64.Rust.boxAt
  apply Entails.pure_left
  intro hptr
  apply Entails.pure_right hptr
  by_cases hbs : bs = []
  · simp only [hbs, ↓reduceIte]
    exact Entails.refl _
  · simp only [hbs, ↓reduceIte]
    exact sepConj_mono_right (pointsToBytes_entails_memRegion ptr bs)

end Arm64.Rust.GlobalAlloc

namespace Arm64.Rust

open Arm64 ProofLib

/-! ## Caller-Step `VmPreserved` and Heap Transport -/

@[simp]
theorem VmPreserved.refl (s : State) : VmPreserved s s :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem VmPreserved.symm {s₁ s₂ : State} (h : VmPreserved s₁ s₂) : VmPreserved s₂ s₁ :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩

theorem VmPreserved.trans {s₁ s₂ s₃ : State}
    (h₁₂ : VmPreserved s₁ s₂) (h₂₃ : VmPreserved s₂ s₃) : VmPreserved s₁ s₃ :=
  ⟨h₂₃.1.trans h₁₂.1, h₂₃.2.1.trans h₁₂.2.1, h₂₃.2.2.1.trans h₁₂.2.2.1, h₂₃.2.2.2.trans h₁₂.2.2.2⟩

@[simp]
theorem VmPreserved.writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    VmPreserved s (s.writeReg64 r v) :=
  ⟨rfl, rfl, rfl, rfl⟩

@[simp]
theorem VmPreserved.writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    VmPreserved s (s.writeReg32 r v) :=
  ⟨rfl, rfl, rfl, rfl⟩

@[simp]
theorem VmPreserved.writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    VmPreserved s (s.writeReg w r v) :=
  ⟨rfl, rfl, rfl, rfl⟩

@[simp]
theorem VmPreserved.writeVReg128 (s : State) (idx : BitVec 5) (v : BitVec 128) :
    VmPreserved s (s.writeVReg128 idx v) :=
  ⟨rfl, rfl, rfl, rfl⟩

@[simp]
theorem VmPreserved.writeVReg64 (s : State) (idx : BitVec 5) (v : BitVec 64) :
    VmPreserved s (s.writeVReg64 idx v) :=
  ⟨rfl, rfl, rfl, rfl⟩

@[simp]
theorem VmPreserved.writeVReg32 (s : State) (idx : BitVec 5) (v : BitVec 32) :
    VmPreserved s (s.writeVReg32 idx v) :=
  ⟨rfl, rfl, rfl, rfl⟩

@[simp]
theorem VmPreserved.advancePC (s : State) : VmPreserved s s.advancePC :=
  ⟨rfl, rfl, rfl, rfl⟩

@[simp]
theorem VmPreserved.setPC (s : State) (pc : BitVec 64) : VmPreserved s (s.setPC pc) :=
  ⟨rfl, rfl, rfl, rfl⟩

@[simp]
theorem VmPreserved.setPState (s : State) (ps : PState) : VmPreserved s (s.setPState ps) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem VmPreserved.setMem_of_perm_eq (s : State) (m' : Memory) (h : m'.perm = s.mem.perm) :
    VmPreserved s (s.setMem m') :=
  ⟨rfl, rfl, rfl, h⟩

@[simp]
theorem VmPreserved.setMem_write8 (s : State) (a : BitVec 64) (v : BitVec 8) :
    VmPreserved s (s.setMem (s.mem.write8 a v)) :=
  ⟨rfl, rfl, rfl, Memory.perm_write8 s.mem a v⟩

@[simp]
theorem VmPreserved.setMem_write16 (s : State) (a : BitVec 64) (v : BitVec 16) :
    VmPreserved s (s.setMem (s.mem.write16 a v)) :=
  ⟨rfl, rfl, rfl, Memory.perm_write16 s.mem a v⟩

@[simp]
theorem VmPreserved.setMem_write32 (s : State) (a : BitVec 64) (v : BitVec 32) :
    VmPreserved s (s.setMem (s.mem.write32 a v)) :=
  ⟨rfl, rfl, rfl, Memory.perm_write32 s.mem a v⟩

@[simp]
theorem VmPreserved.setMem_write64 (s : State) (a : BitVec 64) (v : BitVec 64) :
    VmPreserved s (s.setMem (s.mem.write64 a v)) :=
  ⟨rfl, rfl, rfl, Memory.perm_write64 s.mem a v⟩

@[simp]
theorem VmPreserved.setMem_write128 (s : State) (a : BitVec 64) (v : BitVec 128) :
    VmPreserved s (s.setMem (s.mem.write128 a v)) :=
  ⟨rfl, rfl, rfl, Memory.perm_write128 s.mem a v⟩

@[simp]
theorem VmPreserved.setMem_writeSized (s : State) (sz : MemWidth) (a v : BitVec 64) :
    VmPreserved s (s.setMem (s.mem.writeSized sz a v)) :=
  ⟨rfl, rfl, rfl, Memory.perm_writeSized s.mem sz a v⟩

@[simp]
theorem VmPreserved.setMem_writeSimdSized (s : State) (sz : SimdMemSize) (a : BitVec 64) (v : BitVec 128) :
    VmPreserved s (s.setMem (s.mem.writeSimdSized sz a v)) :=
  ⟨rfl, rfl, rfl, Memory.perm_writeSimdSized s.mem sz a v⟩

@[simp]
theorem VmPreserved.setMem_writeBytes (s : State) (a : BitVec 64) (bs : List (BitVec 8)) :
    VmPreserved s (s.setMem (s.mem.writeBytes a bs)) :=
  ⟨rfl, rfl, rfl, Memory.perm_writeBytes s.mem a bs⟩

theorem GlobalAlloc.heap_transport_entails {P : Program} {addrs : GlobalAllocAddrs}
    (A : GlobalAlloc P addrs) {liveBytes liveBlocks : Nat} {s s' : State}
    (h : VmPreserved s s') :
    A.Heap liveBytes liveBlocks s ⊢ A.Heap liveBytes liveBlocks s' := by
  rw [A.heap_transport liveBytes liveBlocks s s' h]
  exact Entails.refl _

/-! ## `LayoutOk` and `BudgetOk` Specializations -/

theorem IsPow2Align.pos {align : BitVec 64} (h : IsPow2Align align) : 0 < align.toNat := by
  rcases h with ⟨hne, _⟩
  exact Nat.pos_of_ne_zero (fun h0 => hne (BitVec.eq_of_toNat_eq h0))

theorem LayoutOk.size_pos {size align : BitVec 64} (h : LayoutOk size align) : 0 < size.toNat := by
  rcases h with ⟨hne, _, _⟩
  exact Nat.pos_of_ne_zero (fun h0 => hne (BitVec.eq_of_toNat_eq h0))

theorem LayoutOk.align_pos {size align : BitVec 64} (h : LayoutOk size align) : 0 < align.toNat :=
  h.2.1.pos

theorem LayoutOk.size_small {size align : BitVec 64} (h : LayoutOk size align) :
    SmallLen size.toNat := by
  have hal : 0 < align.toNat := h.align_pos
  have hle : size.toNat + align.toNat ≤ 2 ^ 63 := h.2.2
  unfold SmallLen
  omega

/-- Eliminates the null branch in `globalAllocSpec`'s postcondition when `BudgetOk` holds. -/
theorem globalAlloc_nonnull_of_budgetOk
    (Heap : Nat → Nat → State → SepProp)
    (Block : BitVec 64 → Nat → Nat → SepProp)
    (maxGuaranteedAlign maxLiveBytes maxLiveBlocks liveBytes liveBlocks : Nat)
    (size align ret : BitVec 64) (sf : State)
    (hbud : BudgetOk maxGuaranteedAlign maxLiveBytes maxLiveBlocks
      liveBytes liveBlocks size.toNat align.toNat) :
    (if ret = 0#64 then
       ⌜¬ BudgetOk maxGuaranteedAlign maxLiveBytes maxLiveBlocks
           liveBytes liveBlocks size.toNat align.toNat⌝ ∗
       Heap liveBytes liveBlocks sf
     else
       ⌜ret.toNat % align.toNat = 0 ∧ ret.toNat + size.toNat < 2 ^ 64⌝ ∗
       Heap (liveBytes + size.toNat) (liveBlocks + 1) sf ∗
       Block ret size.toNat align.toNat ∗
       memRegion ret size.toNat) ⊢
    ⌜ret ≠ 0#64 ∧ ret.toNat % align.toNat = 0 ∧ ret.toNat + size.toNat < 2 ^ 64⌝ ∗
      Heap (liveBytes + size.toNat) (liveBlocks + 1) sf ∗
      Block ret size.toNat align.toNat ∗
      memRegion ret size.toNat := by
  by_cases hret : ret = 0#64
  · simp only [hret, ↓reduceIte]
    apply Entails.pure_left
    intro hnot
    exact False.elim (hnot hbud)
  · simp only [hret, ↓reduceIte]
    apply Entails.pure_left
    rintro ⟨hal, hnw⟩
    exact Entails.pure_right ⟨hret, hal, hnw⟩ (Entails.refl _)

/-- Eliminates the null branch in `globalAllocZeroedSpec`'s postcondition when `BudgetOk` holds. -/
theorem globalAllocZeroed_nonnull_of_budgetOk
    (Heap : Nat → Nat → State → SepProp)
    (Block : BitVec 64 → Nat → Nat → SepProp)
    (maxGuaranteedAlign maxLiveBytes maxLiveBlocks liveBytes liveBlocks : Nat)
    (size align ret : BitVec 64) (sf : State)
    (hbud : BudgetOk maxGuaranteedAlign maxLiveBytes maxLiveBlocks
      liveBytes liveBlocks size.toNat align.toNat) :
    (if ret = 0#64 then
       ⌜¬ BudgetOk maxGuaranteedAlign maxLiveBytes maxLiveBlocks
           liveBytes liveBlocks size.toNat align.toNat⌝ ∗
       Heap liveBytes liveBlocks sf
     else
       ⌜ret.toNat % align.toNat = 0 ∧ ret.toNat + size.toNat < 2 ^ 64⌝ ∗
       Heap (liveBytes + size.toNat) (liveBlocks + 1) sf ∗
       Block ret size.toNat align.toNat ∗
       (ret ↦ₛ List.replicate size.toNat 0#8)) ⊢
    ⌜ret ≠ 0#64 ∧ ret.toNat % align.toNat = 0 ∧ ret.toNat + size.toNat < 2 ^ 64⌝ ∗
      Heap (liveBytes + size.toNat) (liveBlocks + 1) sf ∗
      Block ret size.toNat align.toNat ∗
      (ret ↦ₛ List.replicate size.toNat 0#8) := by
  by_cases hret : ret = 0#64
  · simp only [hret, ↓reduceIte]
    apply Entails.pure_left
    intro hnot
    exact False.elim (hnot hbud)
  · simp only [hret, ↓reduceIte]
    apply Entails.pure_left
    rintro ⟨hal, hnw⟩
    exact Entails.pure_right ⟨hret, hal, hnw⟩ (Entails.refl _)

/-- Eliminates the null branch in `globalReallocSpec`'s postcondition when `BudgetOk` holds. -/
theorem globalRealloc_nonnull_of_budgetOk
    (Heap : Nat → Nat → State → SepProp)
    (Block : BitVec 64 → Nat → Nat → SepProp)
    (maxGuaranteedAlign maxLiveBytes maxLiveBlocks liveBytes liveBlocks : Nat)
    (p oldSize align newSize ret : BitVec 64) (bs : List (BitVec 8)) (sf : State)
    (hbud : BudgetOk maxGuaranteedAlign maxLiveBytes maxLiveBlocks
      liveBytes liveBlocks newSize.toNat align.toNat) :
    (if ret = 0#64 then
       ⌜¬ BudgetOk maxGuaranteedAlign maxLiveBytes maxLiveBlocks
           liveBytes liveBlocks newSize.toNat align.toNat⌝ ∗
       Heap liveBytes liveBlocks sf ∗
       Block p oldSize.toNat align.toNat ∗
       (p ↦ₛ bs) ∗
       memRegion (p + BitVec.ofNat 64 bs.length) (oldSize.toNat - bs.length)
     else
       ⌜ret.toNat % align.toNat = 0 ∧ ret.toNat + newSize.toNat < 2 ^ 64⌝ ∗
       Heap (liveBytes - oldSize.toNat + newSize.toNat) liveBlocks sf ∗
       Block ret newSize.toNat align.toNat ∗
       (ret ↦ₛ bs) ∗
       memRegion (ret + BitVec.ofNat 64 bs.length) (newSize.toNat - bs.length)) ⊢
    ⌜ret ≠ 0#64 ∧ ret.toNat % align.toNat = 0 ∧ ret.toNat + newSize.toNat < 2 ^ 64⌝ ∗
      Heap (liveBytes - oldSize.toNat + newSize.toNat) liveBlocks sf ∗
      Block ret newSize.toNat align.toNat ∗
      (ret ↦ₛ bs) ∗
      memRegion (ret + BitVec.ofNat 64 bs.length) (newSize.toNat - bs.length) := by
  by_cases hret : ret = 0#64
  · simp only [hret, ↓reduceIte]
    apply Entails.pure_left
    intro hnot
    exact False.elim (hnot hbud)
  · simp only [hret, ↓reduceIte]
    apply Entails.pure_left
    rintro ⟨hal, hnw⟩
    exact Entails.pure_right ⟨hret, hal, hnw⟩ (Entails.refl _)

end Arm64.Rust
