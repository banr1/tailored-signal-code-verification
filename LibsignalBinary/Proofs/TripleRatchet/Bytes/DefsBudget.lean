/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.TripleRatchet.Bytes.Defs

/-!
# Budget-Threaded `bytes::Bytes` Function Specifications

Defines `VmPreserved`-strengthened contracts for 0-allocation `bytes::Bytes` operations
(`bytesFromVecSpec`, `bytesFromVecPlacedSpec`, `bytesStaticClonePlacedSpec`, `bytesStaticDropSpec`)
and `RustCliAllocBudget M` contracts with deterministic `bytesDropEvents` envelopes (`onOom = ⌜False⌝`)
for `promotable_even_drop`, `promotable_odd_drop`, and unified vtable `drop` dispatch.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Bytes.DefsBudget

open Arm64 ProofLib SepProp
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8At)
open CryptoVerification.LibsignalTripleRatchet (
  BytesFromVecGhost BytesDropGhost
  bytesFromVecStack promotableEvenDropStack promotableOddDropStack bytesVtableDropStack
  promotableEvenDropStackX promotableOddDropStackX bytesVtableDropStackX
  bytesPtr bytesData bytesBoxU8Buf bytesHeader bytesAt
  staticVtablePlacedAddr bytesPlacedAt
)
open LibsignalBinary.Heap (
  VmPreserved AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget
  FreeOnlyEvs rustDeallocEvents
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)

noncomputable section

/-! ## 1. Deterministic Drop Events for `bytes::Bytes` -/

/-- Deterministic `AllocEvent` list emitted when dropping a `bytes::Bytes` with buffer `bs`:
    `[]` when `bs.length = 0` (`STATIC_VTABLE` → `static_drop`), else
    `rustDeallocEvents bs.length 1` (`promotable_{even,odd}_drop` → `__rust_dealloc(ptr, len, 1)`). -/
def bytesDropEvents (bs : List (BitVec 8)) : List AllocEvent :=
  if bs.length = 0 then [] else rustDeallocEvents bs.length 1

def BytesDropEnv (bs : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  evs = bytesDropEvents bs

theorem freeOnlyEvs_bytesDropEvents (bs : List (BitVec 8)) :
    FreeOnlyEvs (bytesDropEvents bs) := by
  unfold bytesDropEvents
  by_cases h : bs.length = 0
  · simp only [h, ↓reduceIte]
    exact FreeOnlyEvs.nil
  · simp only [h, ↓reduceIte, rustDeallocEvents]
    exact FreeOnlyEvs.singleton 1 bs.length

theorem liveBytes_stepEvents_bytesDropEvents_le (M : AllocCostModel) (bs : List (BitVec 8))
    (st : M.σ) :
    M.liveBytes (M.stepEvents (bytesDropEvents bs) st) ≤ M.liveBytes st := by
  unfold bytesDropEvents
  by_cases h : bs.length = 0
  · simp only [h, ↓reduceIte, AllocCostModel.stepEvents_nil]
    exact Nat.le_refl _
  · simp only [h, ↓reduceIte, rustDeallocEvents, AllocCostModel.stepEvents_cons,
      AllocCostModel.stepEvents_nil]
    exact M.liveBytes_free_le 1 bs.length st

/-! ## 2. Pure (`0`-Allocation, `VmPreserved`) `Bytes` Specifications -/

/-- VM-preserving specification of `<Bytes as From<Vec<u8>>>::from` at base `b`. -/
def bytesFromVecSpec (A : RustAlloc) (b : BitVec 64) : Spec BytesFromVecGhost where
  pre := fun (v, out, cap, ptr, bs) s =>
    ⌜s.readReg64 .x0 = v ∧ s.readReg64 .x8 = out ∧ cap.toNat = bs.length⌝ ∗
    vecU8At A v cap ptr bs ∗
    memRegion out 32 ∗
    stackAt s.sp bytesFromVecStack
  post := fun (v, out, cap, ptr, bs) s0 sf =>
    ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
    vecHeader v cap ptr (BitVec.ofNat 64 bs.length) ∗
    bytesAt A b out ptr bs ∗
    stackAt s0.sp bytesFromVecStack

/-- VM-preserving specification of `bytes::bytes::static_drop` (`ret`, `0` allocations). -/
def bytesStaticDropSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ s0 sf => ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf⌝

/-- Relocatable VM-preserving specification of `<Bytes as From<Vec<u8>>>::from` (Block `250`). -/
def bytesFromVecPlacedSpec [LibsignalPlacement] (A : RustAlloc) : Spec BytesFromVecGhost where
  pre := fun (v, out, cap, ptr, bs) s =>
    ⌜s.readReg64 .x0 = v ∧ s.readReg64 .x8 = out ∧ cap.toNat = bs.length⌝ ∗
    vecU8At A v cap ptr bs ∗
    memRegion out 32 ∗
    stackAt s.sp bytesFromVecStack
  post := fun (v, out, cap, ptr, bs) s0 sf =>
    ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
    vecHeader v cap ptr (BitVec.ofNat 64 bs.length) ∗
    bytesPlacedAt A out ptr bs ∗
    stackAt s0.sp bytesFromVecStack

/-- Relocatable VM-preserving specification of `bytes::bytes::static_clone` (Block `226`). -/
def bytesStaticClonePlacedSpec [LibsignalPlacement] :
    Spec (BitVec 64 × BitVec 64 × BitVec 64) where
  pre := fun (out, ptr, len) s =>
    ⌜s.readReg64 .x8 = out ∧ s.readReg64 .x1 = ptr ∧ s.readReg64 .x2 = len⌝ ∗
    memRegion out 32
  post := fun (out, ptr, len) s0 sf =>
    ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
    bytesHeader out staticVtablePlacedAddr ptr len 0#64

/-! ## 3. Budget-Threaded Drop Specifications (`allocHookStack + 48`) -/

/-- Budget-threaded specification of `bytes::bytes::promotable_even_drop` (Block `237`). -/
def promotableEvenDropSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BytesDropGhost × M.σ) where
  pre := fun ((ptr, bs, off), st) s =>
    ⌜0 < bs.length ∧
      off ≤ bs.length ∧
      (ptr &&& 1#64) = 0#64 ∧
      s.readReg64 .x0 = (ptr ||| 1#64) ∧
      s.readReg64 .x1 = ptr + BitVec.ofNat 64 off ∧
      s.readReg64 .x2 = BitVec.ofNat 64 (bs.length - off) ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
    bytesBoxU8Buf A.repAlloc ptr bs ∗
    A.pool lim st s ∗
    stackAt s.sp promotableEvenDropStack
  post := fun ((_, bs, _), st) s0 sf =>
    let st' := M.stepEvents (rustDeallocEvents bs.length 1) st
    ⌜sf.trace = s0.trace ∧ M.liveBytes st' ≤ M.liveBytes st⌝ ∗
    A.pool lim st' sf ∗
    stackAt s0.sp promotableEvenDropStack

/-- Budget-threaded specification of `bytes::bytes::promotable_odd_drop` (Block `236`). -/
def promotableOddDropSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BytesDropGhost × M.σ) where
  pre := fun ((ptr, bs, off), st) s =>
    ⌜0 < bs.length ∧
      off ≤ bs.length ∧
      (ptr &&& 1#64) ≠ 0#64 ∧
      s.readReg64 .x0 = ptr ∧
      s.readReg64 .x1 = ptr + BitVec.ofNat 64 off ∧
      s.readReg64 .x2 = BitVec.ofNat 64 (bs.length - off) ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
    bytesBoxU8Buf A.repAlloc ptr bs ∗
    A.pool lim st s ∗
    stackAt s.sp promotableOddDropStack
  post := fun ((_, bs, _), st) s0 sf =>
    let st' := M.stepEvents (rustDeallocEvents bs.length 1) st
    ⌜sf.trace = s0.trace ∧ M.liveBytes st' ≤ M.liveBytes st⌝ ∗
    A.pool lim st' sf ∗
    stackAt s0.sp promotableOddDropStack

/-- Budget-threaded unified vtable `drop` specification at `bytesVtableDropStack`. -/
def bytesVtableDropSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ptr : BitVec 64) (bs : List (BitVec 8)) (off : Nat) :
    Spec M.σ where
  pre := fun st s =>
    ⌜off ≤ bs.length ∧
      s.readReg64 .x0 = bytesData ptr bs.length ∧
      s.readReg64 .x1 = bytesPtr ptr bs.length + BitVec.ofNat 64 off ∧
      s.readReg64 .x2 = BitVec.ofNat 64 (bs.length - off) ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
    bytesBoxU8Buf A.repAlloc ptr bs ∗
    A.pool lim st s ∗
    stackAt s.sp bytesVtableDropStack
  post := fun st s0 sf =>
    let st' := M.stepEvents (bytesDropEvents bs) st
    ⌜sf.trace = s0.trace ∧ M.liveBytes st' ≤ M.liveBytes st⌝ ∗
    A.pool lim st' sf ∗
    stackAt s0.sp bytesVtableDropStack

/-! ## 4. Budget-Threaded Drop Specifications at `extHookStack + 48` (`*SpecX`) -/

/-- Budget-threaded `promotableEvenDropSpec` at `promotableEvenDropStackX` (`= extHookStack + 48`). -/
def promotableEvenDropSpecX [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BytesDropGhost × M.σ) where
  pre := fun ((ptr, bs, off), st) s =>
    ⌜0 < bs.length ∧
      off ≤ bs.length ∧
      (ptr &&& 1#64) = 0#64 ∧
      s.readReg64 .x0 = (ptr ||| 1#64) ∧
      s.readReg64 .x1 = ptr + BitVec.ofNat 64 off ∧
      s.readReg64 .x2 = BitVec.ofNat 64 (bs.length - off) ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
    bytesBoxU8Buf A.repAlloc ptr bs ∗
    A.pool lim st s ∗
    stackAt s.sp promotableEvenDropStackX
  post := fun ((_, bs, _), st) s0 sf =>
    let st' := M.stepEvents (rustDeallocEvents bs.length 1) st
    ⌜sf.trace = s0.trace ∧ M.liveBytes st' ≤ M.liveBytes st⌝ ∗
    A.pool lim st' sf ∗
    stackAt s0.sp promotableEvenDropStackX

/-- Budget-threaded `promotableOddDropSpec` at `promotableOddDropStackX` (`= extHookStack + 48`). -/
def promotableOddDropSpecX [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BytesDropGhost × M.σ) where
  pre := fun ((ptr, bs, off), st) s =>
    ⌜0 < bs.length ∧
      off ≤ bs.length ∧
      (ptr &&& 1#64) ≠ 0#64 ∧
      s.readReg64 .x0 = ptr ∧
      s.readReg64 .x1 = ptr + BitVec.ofNat 64 off ∧
      s.readReg64 .x2 = BitVec.ofNat 64 (bs.length - off) ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
    bytesBoxU8Buf A.repAlloc ptr bs ∗
    A.pool lim st s ∗
    stackAt s.sp promotableOddDropStackX
  post := fun ((_, bs, _), st) s0 sf =>
    let st' := M.stepEvents (rustDeallocEvents bs.length 1) st
    ⌜sf.trace = s0.trace ∧ M.liveBytes st' ≤ M.liveBytes st⌝ ∗
    A.pool lim st' sf ∗
    stackAt s0.sp promotableOddDropStackX

/-- Budget-threaded `bytesVtableDropSpec` at `bytesVtableDropStackX` (`= extHookStack + 48`). -/
def bytesVtableDropSpecX [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ptr : BitVec 64) (bs : List (BitVec 8)) (off : Nat) :
    Spec M.σ where
  pre := fun st s =>
    ⌜off ≤ bs.length ∧
      s.readReg64 .x0 = bytesData ptr bs.length ∧
      s.readReg64 .x1 = bytesPtr ptr bs.length + BitVec.ofNat 64 off ∧
      s.readReg64 .x2 = BitVec.ofNat 64 (bs.length - off) ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
    bytesBoxU8Buf A.repAlloc ptr bs ∗
    A.pool lim st s ∗
    stackAt s.sp bytesVtableDropStackX
  post := fun st s0 sf =>
    let st' := M.stepEvents (bytesDropEvents bs) st
    ⌜sf.trace = s0.trace ∧ M.liveBytes st' ≤ M.liveBytes st⌝ ∗
    A.pool lim st' sf ∗
    stackAt s0.sp bytesVtableDropStackX

end

end LibsignalBinary.Proofs.TripleRatchet.Bytes.DefsBudget
