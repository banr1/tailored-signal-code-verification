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
public import LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersX
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerializeLenExtBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SessionLenExtBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Helpers
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.HooksX

/-!
# Budget-Threaded `SessionRecord::serialize` Callee Sub-Specs at `serializeSubStackX`

Lifts the budget-threaded `[LibsignalPlacement]` contracts of all `SessionRecord::serialize`
callees (`vecVecClone`, `sessionLen`, `sessionClone`, `encode_varint`, `encode_raw`, drop glue,
`__rust_alloc`, `shim`, and `memcpy`) to operate over `stackAt sp serializeSubStackX` in Block `52`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersXBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks LibsignalCodeLoaded IsLsBlockProg
  lsmpl withLsCodeLoaded withLsCl extract_withLsCodeLoaded
  lsρ lsRustAllocSym lsRustNoAllocShimSym lsMemcpySym
  blkPl_6 blkPl_10
)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8At)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalPublicApiRepr (sessionStateReprAt)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost sessionStateAt)
open CryptoVerification.LibsignalTripleRatchet (
  extHookStack sessionMemcpySpec ls_subroutine_ok_cl_of_callee
)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  encodeVarintStackX EncodeVarintGhost
)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (
  DropSessionStructureGhost
)
open CryptoVerification.E2E.Record.Placed (
  blkPl_14 blkPl_80 blkPl_86 blkPl_117
)
open CryptoVerification.E2E.Record.Serialization (
  vecVecCloneStack sessionLenStack encSessionMem
  VecVecCloneGhost SessionCloneGhost SessionLenGhost EncodeRawGhost
)
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux (
  subroutine_ok_withLsCodeLoaded_frame_weaken
  subroutine_ok_withLsCl_of_withLsCodeLoaded
)
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX (
  serializeSubStackX stackAt_serializeSub_splitX
  subroutine_ok_withLsCodeLoaded_of_withLsCl
)
open LibsignalBinary.Heap (
  VmPreserved AllocCallPreserved AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget
  RustLayoutOk NullAllowed FitsEnv FreeOnlyEvs rustAllocEvents
  not_nullAllowed_of_fitsAllocEvents
)
open LibsignalBinary.Heap.IfaceLemmas (satisfies_drop_mid_entails)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  rustCliAllocBudgetSpecWithStack rustCliAllocNoOomSpecWithStack
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (session2ShimBudgetSpecX)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget (
  vecVecCloneEmptySpec sessionLenSpec SessionCloneEnv EncodeRawEnv
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget (
  EncodeVarintEnv encodeVarintSpecX
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DefsBudget (
  subroutine_ok_withLsCl_map_oom'
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerializeLenExtBudget (
  vecVecCloneEmpty_placed_ok_cl
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SessionLenExtBudget (
  sessionLen_placed_ok_cl
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (
  sessionCloneStackX encodeRawStackX dropSessionStructureLocal1StackX
  sessionCloneSpecX encodeRawSpecX dropSessionStructureLocal1SpecX
  SerContractsXPlaced
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget (
  EncodeVarintPlacedOkX SessionClonePlacedOkX EncodeRawPlacedOkX
  DropSessionStructureLocal1PlacedOkX
)

/-! ## Lifted callee specifications at `serializeSubStackX` -/

def vecVecCloneSubSpecX : Spec VecVecCloneGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.dst ∧ s.readReg64 .x1 = x.src ∧ s.readReg64 .x2 = 0#64⌝ ∗
      memRegion x.dst 24 ∗ stackAt s.sp serializeSubStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
      vecHeader x.dst 0#64 8#64 0#64 ∗ stackAt s0.sp serializeSubStackX

def sessionLenSubSpecX (A : RustAlloc) : Spec SessionLenGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ (encSessionMem x.G x.s).length < 2 ^ 32⌝ ∗
      sessionStateReprAt A x.ss x.G x.s ∗ stackAt s.sp serializeSubStackX
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (encSessionMem x.G x.s).length ∧
      sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
      sessionStateReprAt A x.ss x.G x.s ∗ stackAt s0.sp serializeSubStackX

def sessionCloneSubSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (SessionCloneGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.dst ∧ s.readReg64 .x1 = x.src ∧
      FitsEnv M lim st (SessionCloneEnv x.G x.s)⌝ ∗
      sessionStateReprAt A.repAlloc x.src x.G x.s ∗ memRegion x.dst 344 ∗
      A.pool lim st s ∗ stackAt s.sp serializeSubStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ SessionCloneEnv x.G x.s evs⌝ ∗
      sessionStateReprAt A.repAlloc x.src x.G x.s ∗
      (∃∗ G' : SessionGhost, ⌜encSessionMem G' x.s = encSessionMem x.G x.s⌝ ∗
        sessionStateReprAt A.repAlloc x.dst G' x.s) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp serializeSubStackX

def encodeVarintSubSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (EncodeVarintGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.val ∧ s.readReg64 .x1 = x.v ∧ x.bs.length + 10 < 2 ^ 62 ∧
      FitsEnv M lim st (EncodeVarintEnv x)⌝ ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗ stackAt s.sp serializeSubStackX
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeVarint x.val).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodeVarint x.val)) ∗
      (∃∗ evs : List AllocEvent, ⌜EncodeVarintEnv x evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp serializeSubStackX

def encodeRawSubSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (EncodeRawGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.ss ∧ s.readReg64 .x1 = x.v ∧
      x.bs.length + (encSessionMem x.G x.s).length < 2 ^ 32 ∧
      FitsEnv M lim st (EncodeRawEnv x)⌝ ∗
      sessionStateReprAt A.repAlloc x.ss x.G x.s ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗
      stackAt s.sp serializeSubStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ EncodeRawEnv x evs⌝ ∗
      sessionStateReprAt A.repAlloc x.ss x.G x.s ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encSessionMem x.G x.s)) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp serializeSubStackX

def dropLocal1SubSpecXBase (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DropSessionStructureGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.ss⌝ ∗
      sessionStateAt A.repAlloc x.ss x.G x.st ∗ A.pool lim st s ∗ stackAt s.sp serializeSubStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ FreeOnlyEvs evs⌝ ∗
      memRegion x.ss 344 ∗ A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp serializeSubStackX

def dropLocal1SubSpecX [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DropSessionStructureGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.ss ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      sessionStateAt A.repAlloc x.ss x.G x.st ∗ A.pool lim st s ∗ stackAt s.sp serializeSubStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ FreeOnlyEvs evs⌝ ∗
      memRegion x.ss 344 ∗ A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp serializeSubStackX

abbrev rustAllocSubSpecX [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (Nat × Nat × M.σ) :=
  rustCliAllocBudgetSpecWithStack M A lim false serializeSubStackX

abbrev rustAllocNoOomSubSpecX [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (Nat × Nat × M.σ) :=
  rustCliAllocNoOomSpecWithStack M A lim false serializeSubStackX

def shimSubSpecX : Spec Unit where
  pre := fun _ s => stackAt s.sp serializeSubStackX
  post := fun _ s0 sf => ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗ stackAt s0.sp serializeSubStackX

def memcpySubSpecX : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s =>
    ⌜s.readReg64 .x0 = dst ∧ s.readReg64 .x1 = src ∧ (s.readReg64 .x2).toNat = bs.length⌝ ∗
      memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt s.sp serializeSubStackX
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
      (dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt s0.sp serializeSubStackX

/-! ## Relocatable `[LibsignalPlacement]` lifted callee proofs -/

section Placed

theorem vecVecClone_placed_sub_okX [LibsignalPlacement]
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H] :
    subroutine_ok callerProg (blkPl_117).base (withLsCodeLoaded lsmpl vecVecCloneSubSpecX) := by
  refine subroutine_ok_withLsCodeLoaded_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStackX)
      (serializeSubStackX - vecVecCloneStack))
    (subroutine_ok_withLsCodeLoaded_of_withLsCl
      (vecVecCloneEmpty_placed_ok_cl (callerProg := callerProg)))
    (fun x s0 => ?_)
    (fun x s0 sf => ?_)
    (fun _ _ _ => Entails.pure_left False.elim)
    (fun _ _ _ _ => rfl)
  · simp only [vecVecCloneSubSpecX, vecVecCloneEmptySpec,
      stackAt_serializeSub_splitX s0.sp vecVecCloneStack (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)
  · simp only [vecVecCloneSubSpecX, vecVecCloneEmptySpec,
      stackAt_serializeSub_splitX s0.sp vecVecCloneStack (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)

theorem vecVecClone_placed_sub_clX [LibsignalPlacement]
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H] :
    subroutine_ok callerProg (blkPl_117).base (withLsCl lsmpl vecVecCloneSubSpecX) :=
  subroutine_ok_withLsCl_of_withLsCodeLoaded vecVecClone_placed_sub_okX

theorem sessionLen_placed_sub_okX [LibsignalPlacement] (A : RustAlloc)
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H] :
    subroutine_ok callerProg (blkPl_86).base (withLsCodeLoaded lsmpl (sessionLenSubSpecX A)) := by
  refine subroutine_ok_withLsCodeLoaded_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStackX)
      (serializeSubStackX - sessionLenStack))
    (subroutine_ok_withLsCodeLoaded_of_withLsCl
      (sessionLen_placed_ok_cl A (callerProg := callerProg)))
    (fun x s0 => ?_)
    (fun x s0 sf => ?_)
    (fun _ _ _ => Entails.pure_left False.elim)
    (fun _ _ _ _ => rfl)
  · simp only [sessionLenSubSpecX, sessionLenSpec,
      stackAt_serializeSub_splitX s0.sp sessionLenStack (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)
  · simp only [sessionLenSubSpecX, sessionLenSpec,
      stackAt_serializeSub_splitX s0.sp sessionLenStack (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)

theorem sessionLen_placed_sub_clX [LibsignalPlacement] (A : RustAlloc)
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H] :
    subroutine_ok callerProg (blkPl_86).base (withLsCl lsmpl (sessionLenSubSpecX A)) :=
  subroutine_ok_withLsCl_of_withLsCodeLoaded (sessionLen_placed_sub_okX A)

theorem sessionClone_placed_sub_okX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hClone : SessionClonePlacedOkX M A lim H) :
    subroutine_ok callerProg (blkPl_80).base
      (withLsCodeLoaded lsmpl (sessionCloneSubSpecX M A lim)) := by
  refine subroutine_ok_withLsCodeLoaded_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStackX)
      (serializeSubStackX - sessionCloneStackX))
    (subroutine_ok_withLsCodeLoaded_of_withLsCl
      (ls_subroutine_ok_cl_of_callee (callerProg := callerProg) hClone))
    (fun ⟨x, st⟩ s0 => ?_)
    (fun ⟨x, st⟩ s0 sf => ?_)
    (fun _ _ _ => Entails.pure_left False.elim)
    (fun _ _ _ _ => rfl)
  · simp only [sessionCloneSubSpecX, sessionCloneSpecX,
      stackAt_serializeSub_splitX s0.sp sessionCloneStackX (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)
  · dsimp only [sessionCloneSubSpecX, sessionCloneSpecX]
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_mono fun evs => ?_
    rw [stackAt_serializeSub_splitX s0.sp sessionCloneStackX (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)

theorem sessionClone_placed_sub_clX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hClone : SessionClonePlacedOkX M A lim H) :
    subroutine_ok callerProg (blkPl_80).base
      (withLsCl lsmpl (sessionCloneSubSpecX M A lim)) :=
  subroutine_ok_withLsCl_of_withLsCodeLoaded (sessionClone_placed_sub_okX hClone)

theorem encodeVarint_placed_sub_okX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hEV : EncodeVarintPlacedOkX M A lim H) :
    subroutine_ok callerProg (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintSubSpecX M A lim)) := by
  refine subroutine_ok_withLsCodeLoaded_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStackX)
      (serializeSubStackX - encodeVarintStackX))
    (subroutine_ok_withLsCodeLoaded_of_withLsCl
      (ls_subroutine_ok_cl_of_callee (callerProg := callerProg) hEV))
    (fun ⟨x, st⟩ s0 => ?_)
    (fun ⟨x, st⟩ s0 sf => ?_)
    (fun _ _ _ => Entails.pure_left False.elim)
    (fun _ _ _ _ => rfl)
  · simp only [encodeVarintSubSpecX, encodeVarintSpecX,
      stackAt_serializeSub_splitX s0.sp encodeVarintStackX (by decide)]
    refine Entails.trans (sepConj_mono_left (Entails.pure_mono
      (ψ := s0.readReg64 .x0 = x.val ∧ s0.readReg64 .x1 = x.v ∧
        (x.bs.length + 10 ≤ x.cap.toNat ∨ x.bs.length + 10 < 2 ^ 62) ∧
        FitsEnv M lim st (EncodeVarintEnv x))
      fun ⟨h0, h1, h2, h3⟩ => ⟨h0, h1, Or.inr h2, h3⟩)) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  · simp only [encodeVarintSubSpecX, encodeVarintSpecX,
      stackAt_serializeSub_splitX s0.sp encodeVarintStackX (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)

theorem encodeVarint_placed_sub_clX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hEV : EncodeVarintPlacedOkX M A lim H) :
    subroutine_ok callerProg (blkPl_10).base
      (withLsCl lsmpl (encodeVarintSubSpecX M A lim)) :=
  subroutine_ok_withLsCl_of_withLsCodeLoaded (encodeVarint_placed_sub_okX hEV)

theorem encodeRaw_placed_sub_okX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hRaw : EncodeRawPlacedOkX M A lim H) :
    subroutine_ok callerProg (blkPl_14).base
      (withLsCodeLoaded lsmpl (encodeRawSubSpecX M A lim)) := by
  refine subroutine_ok_withLsCodeLoaded_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStackX)
      (serializeSubStackX - encodeRawStackX))
    (subroutine_ok_withLsCodeLoaded_of_withLsCl
      (ls_subroutine_ok_cl_of_callee (callerProg := callerProg) hRaw))
    (fun ⟨x, st⟩ s0 => ?_)
    (fun ⟨x, st⟩ s0 sf => ?_)
    (fun _ _ _ => Entails.pure_left False.elim)
    (fun _ _ _ _ => rfl)
  · simp only [encodeRawSubSpecX, encodeRawSpecX,
      stackAt_serializeSub_splitX s0.sp encodeRawStackX (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)
  · dsimp only [encodeRawSubSpecX, encodeRawSpecX]
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_mono fun evs => ?_
    rw [stackAt_serializeSub_splitX s0.sp encodeRawStackX (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)

theorem encodeRaw_placed_sub_clX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hRaw : EncodeRawPlacedOkX M A lim H) :
    subroutine_ok callerProg (blkPl_14).base
      (withLsCl lsmpl (encodeRawSubSpecX M A lim)) :=
  subroutine_ok_withLsCl_of_withLsCodeLoaded (encodeRaw_placed_sub_okX hRaw)

theorem dropLocal1_placed_sub_okX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hDrop : DropSessionStructureLocal1PlacedOkX M A lim H) :
    subroutine_ok callerProg (blkPl_6).base
      (withLsCodeLoaded lsmpl (dropLocal1SubSpecX M A lim)) := by
  refine subroutine_ok_withLsCodeLoaded_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStackX)
      (serializeSubStackX - dropSessionStructureLocal1StackX))
    (subroutine_ok_withLsCodeLoaded_of_withLsCl
      (ls_subroutine_ok_cl_of_callee (callerProg := callerProg) hDrop))
    (fun ⟨x, st⟩ s0 => ?_)
    (fun ⟨x, st⟩ s0 sf => ?_)
    (fun _ _ _ => Entails.pure_left False.elim)
    (fun _ _ _ _ => rfl)
  · simp only [dropLocal1SubSpecX, dropSessionStructureLocal1SpecX,
      stackAt_serializeSub_splitX s0.sp dropSessionStructureLocal1StackX (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)
  · simp only [dropLocal1SubSpecX, dropSessionStructureLocal1SpecX, sepExists_sepConj_left,
      stackAt_serializeSub_splitX s0.sp dropSessionStructureLocal1StackX (by decide)]
    refine Entails.sepExists_mono fun evs => ?_
    exact Entails.of_eq (by sep_ac_rfl)

theorem dropLocal1_placed_sub_clX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hDrop : DropSessionStructureLocal1PlacedOkX M A lim H) :
    subroutine_ok callerProg (blkPl_6).base
      (withLsCl lsmpl (dropLocal1SubSpecX M A lim)) :=
  subroutine_ok_withLsCl_of_withLsCodeLoaded (dropLocal1_placed_sub_okX hDrop)

theorem alloc_placed_sub_clX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok callerProg (lsρ lsRustAllocSym)
      (withLsCl lsmpl (rustAllocSubSpecX M A lim)) := by
  refine subroutine_ok_withLsCl_map_oom' (hC.alloc.alloc (callerProg := callerProg))
    fun ⟨size, align, st⟩ R s0 hpre =>
      ⟨(size, align, st),
        memRegion (s0.sp - BitVec.ofNat 64 serializeSubStackX)
          (serializeSubStackX - extHookStack) ∗ R,
        ?_, fun sf hpost => ?_, fun _ hoom => satisfies_drop_mid_entails (Entails.refl _) hoom⟩
  · dsimp only [rustAllocSubSpecX, rustCliAllocBudgetSpecWithStack] at hpre ⊢
    rw [stackAt_serializeSub_splitX s0.sp extHookStack (by decide)] at hpre
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  · dsimp only [rustAllocSubSpecX, rustCliAllocBudgetSpecWithStack] at hpost ⊢
    rw [stackAt_serializeSub_splitX s0.sp extHookStack (by decide)]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost

theorem alloc_placed_sub_okX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok callerProg (lsρ lsRustAllocSym)
      (withLsCodeLoaded lsmpl (rustAllocSubSpecX M A lim)) :=
  subroutine_ok_withLsCodeLoaded_of_withLsCl (alloc_placed_sub_clX hC)

theorem allocNoOom_placed_sub_okX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok callerProg (lsρ lsRustAllocSym)
      (withLsCodeLoaded lsmpl (rustAllocNoOomSubSpecX M A lim)) := by
  have h0 := alloc_placed_sub_okX (callerProg := callerProg) hC
  refine subroutine_ok_outcome_intro fun ⟨size, align, st⟩ R s0 hpc hrun hpre hsp => ?_
  have ⟨hcl, hpre0⟩ := extract_withLsCodeLoaded hpre
  dsimp only [rustAllocNoOomSubSpecX, rustCliAllocNoOomSpecWithStack] at hpre0
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hx0, hx1, hlay, hfits, hlr⟩, hrest⟩
  have hpre_b : s0.mem ⊨
      (withLsCodeLoaded lsmpl (rustAllocSubSpecX M A lim)).pre (size, align, st) s0 ∗ R := by
    dsimp only [withLsCodeLoaded, rustAllocSubSpecX, rustCliAllocBudgetSpecWithStack]
    refine Satisfies.mono (Entails.of_eq (by sep_ac_rfl))
      (P := ⌜LibsignalCodeLoaded lsmpl s0.mem⌝ ∗
        (⌜(s0.readReg64 .x0).toNat = size ∧ (s0.readReg64 .x1).toNat = align ∧
          RustLayoutOk size align ∧ LsRetAddr624 (s0.readReg64 .lr)⌝ ∗ ((A.pool lim st s0 ∗ stackAt s0.sp serializeSubStackX) ∗ R))) ?_
    rw [satisfies_pure_sepConj, satisfies_pure_sepConj]
    exact ⟨hcl, ⟨hx0, hx1, hlay, hlr⟩, hrest⟩
  refine h0.mono_outcome (size, align, st) R s0 hpc hrun hpre_b hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, rustAllocSubSpecX, rustCliAllocBudgetSpecWithStack,
      rustAllocNoOomSubSpecX, rustCliAllocNoOomSpecWithStack] at hpost ⊢
    by_cases hnull : sf.readReg64 .x0 = 0
    · simp only [hnull, ↓reduceIte] at hpost
      have hpost' : sf.mem ⊨ ⌜NullAllowed size align⌝ ∗
          (⌜AllocCallPreserved s0 sf⌝ ∗ A.pool lim st sf ∗
            stackAt s0.sp serializeSubStackX ∗ R) :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
      rw [satisfies_pure_sepConj] at hpost'
      exact False.elim (not_nullAllowed_of_fitsAllocEvents hlay hfits hpost'.1)
    · simp only [hnull, Bool.false_eq_true, ↓reduceIte] at hpost ⊢
      have hpost' : sf.mem ⊨ ⌜AllocCallPreserved s0 sf⌝ ∗
          (⌜(sf.readReg64 .x0).toNat % align = 0⌝ ∗
            (A.pool lim (M.stepEvents (rustAllocEvents size align) st) sf ∗
              stackAt s0.sp serializeSubStackX ∗ A.live (sf.readReg64 .x0) size align ∗
              memRegion (sf.readReg64 .x0) size ∗ R)) :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost'
      refine Satisfies.mono (Entails.of_eq (by sep_ac_rfl))
        (P := ⌜AllocCallPreserved s0 sf ∧ sf.readReg64 .x0 ≠ 0#64 ∧
          (sf.readReg64 .x0).toNat % align = 0⌝ ∗
          (A.pool lim (M.stepEvents (rustAllocEvents size align) st) sf ∗
            stackAt s0.sp serializeSubStackX ∗ A.live (sf.readReg64 .x0) size align ∗
            memRegion (sf.readReg64 .x0) size ∗ R)) ?_
      rw [satisfies_pure_sepConj]
      exact ⟨⟨hpost'.1, hnull, hpost'.2.1⟩, hpost'.2.2⟩
  · exact Or.inr (Or.inl ⟨hp, hpan⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
  · dsimp only [withLsCodeLoaded, rustAllocSubSpecX, rustCliAllocBudgetSpecWithStack] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim (hoom.1.1 hfits)

theorem allocNoOom_placed_sub_clX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok callerProg (lsρ lsRustAllocSym)
      (withLsCl lsmpl (rustAllocNoOomSubSpecX M A lim)) :=
  subroutine_ok_withLsCl_of_withLsCodeLoaded (allocNoOom_placed_sub_okX hC)

theorem shim_placed_sub_okX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok callerProg (lsρ lsRustNoAllocShimSym)
      (withLsCodeLoaded lsmpl shimSubSpecX) := by
  refine subroutine_ok_withLsCodeLoaded_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStackX)
      (serializeSubStackX - extHookStack))
    (subroutine_ok_withLsCodeLoaded_of_withLsCl (hC.alloc.shim (callerProg := callerProg)))
    (fun _ s0 => ?_)
    (fun _ s0 sf => ?_)
    (fun _ _ _ => Entails.pure_left False.elim)
    (fun _ _ _ _ => rfl)
  · simp only [shimSubSpecX, session2ShimBudgetSpecX,
      stackAt_serializeSub_splitX s0.sp extHookStack (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)
  · simp only [shimSubSpecX, session2ShimBudgetSpecX,
      stackAt_serializeSub_splitX s0.sp extHookStack (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)

theorem shim_placed_sub_clX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok callerProg (lsρ lsRustNoAllocShimSym)
      (withLsCl lsmpl shimSubSpecX) :=
  subroutine_ok_withLsCl_of_withLsCodeLoaded (shim_placed_sub_okX hC)

theorem memcpy_placed_sub_okX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok callerProg (lsρ lsMemcpySym)
      (withLsCodeLoaded lsmpl memcpySubSpecX) := by
  refine subroutine_ok_withLsCodeLoaded_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStackX)
      (serializeSubStackX - extHookStack))
    (subroutine_ok_withLsCodeLoaded_of_withLsCl (hC.memcpy (callerProg := callerProg)))
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf => ?_)
    (fun _ _ _ => Entails.pure_left False.elim)
    (fun _ _ _ _ => rfl)
  · simp only [memcpySubSpecX, sessionMemcpyBudgetSpec, sessionMemcpySpec, libcMemcpySpec,
      stackAt_serializeSub_splitX s0.sp extHookStack (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)
  · dsimp only [memcpySubSpecX, sessionMemcpyBudgetSpec, sessionMemcpySpec]
    rw [stackAt_serializeSub_splitX s0.sp extHookStack (by decide), sepConj_assoc]
    apply Entails.pure_left; intro hvm
    rw [sepConj_assoc]
    apply Entails.pure_left; rintro ⟨hx0, htr⟩
    exact Entails.pure_right ⟨hx0, htr, hvm⟩ (Entails.of_eq (by sep_ac_rfl))

theorem memcpy_placed_sub_clX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok callerProg (lsρ lsMemcpySym)
      (withLsCl lsmpl memcpySubSpecX) :=
  subroutine_ok_withLsCl_of_withLsCodeLoaded (memcpy_placed_sub_okX hC)

end Placed

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersXBudget
