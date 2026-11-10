/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveNoneBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchivePromote
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DropSsLocal1ExtBudget
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `SessionRecord::promote_state` Proofs

`RustCliAllocBudget`-threaded relocatable `[LibsignalPlacement]` proofs of
`SessionRecord::promote_state` on `lsProg_47 H` (Block `47`), proving
`PromoteStateOverGenPlacedOk` (arbitrary `prevCap`) and `PromoteStateOverPlacedOkX`
(`prevCap = 0#64`) alongside `VmPreserved`-preserving `memcpy` at `promoteStackX`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchivePromoteBudget

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoGames.LibsignalSessionApi (Session)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks LibsignalCodeLoaded IsLsBlockProg
  lsmpl withLsCodeLoaded withLsCl sepWP_seq_lscl
  lsρ lsMemcpySym lsProg_47 blkPl_47 blkLib_eq_47 lsProg_51
)
open CryptoVerification.RustHeap (RustAlloc vecAt)
open CryptoVerification.LibsignalPublicApiRepr (sessionStateReprAt)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost)
open CryptoVerification.LibsignalTripleRatchet (
  extHookStack sessionMemcpySpec ls_subroutine_ok_cl_of_callee
)
open CryptoVerification.E2E.Record.Serialization (encSessionMem)
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux (
  subroutine_ok_withLsCodeLoaded_frame_weaken
  subroutine_ok_withLsCl_of_withLsCodeLoaded
)
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX (
  subroutine_ok_withLsCodeLoaded_of_withLsCl
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (
  HdrP Prev1 prevVecAt
  clearPendingGhost clearPending archiveStackX promoteStackX
  ArchiveOverGhost ArchiveOverGenGhost PromoteOverGhost PromoteOverGenGhost
  stackAt_promote_splitX stackAt_promote_mergeX pointsTo64_memRegion_336_entails_344X
)
open Proofs.libsignal.Hooks2 (stackAt_sub_split_ser)
open LibsignalBinary.Heap (
  VmPreserved AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (
  growOneVecU8BudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyBudgetSpec)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (SerContractsXPlaced)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget (
  DropSessionStructureLocal1PlacedOkX
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DropSsLocal1ExtBudget (
  drop_session_structure_local1_placed_ok_ext
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveDefsBudget (
  ArchiveCoreEnv ArchiveOverEnvX ArchiveOverGenEnv PromoteOverEnvX PromoteOverGenEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveAuxBudget (
  PromoteStateOverGenPlacedOk PromoteStateOverPlacedOkX
  archiveOverGenSpec_pre_eq archiveOverGenSpec_post_eq
  archiveOverSpecX_pre_eq archiveOverSpecX_post_eq
  promoteOverGenSpec_pre_eq promoteOverGenSpec_post_eq
  promoteOverSpecX_pre_eq promoteOverSpecX_post_eq
  EncodeRawPreallocPlacedOkX
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveNoneBudget (
  archive_over_gen_placed_cl_of_contracts archive_over_placed_cl_of_contracts
)

/-! ## 1. `VmPreserved`-Preserving `memcpy` at `promoteStackX` -/

/-- `VmPreserved`-augmented `memcpyPromSpecX` with the full `promote_state` stack budget
(`promoteStackX`), used for the tail call `b memcpy` in `SessionRecord::promote_state`. -/
def memcpyPromBudgetSpecX : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s =>
    ⌜s.readReg64 .x0 = dst ∧ s.readReg64 .x1 = src ∧ (s.readReg64 .x2).toNat = bs.length⌝ ∗
      memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt s.sp promoteStackX
  post := fun (dst, src, bs) s0 sf =>
    ⌜VmPreserved s0 sf⌝ ∗
      ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗
      (dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt s0.sp promoteStackX

/-- Relocatable `memcpy` budget contract lifted to `promoteStackX` (`withLsCodeLoaded`) on any
block caller. -/
theorem memcpy_prom_placed_okX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok callerProg (lsρ lsMemcpySym)
      (withLsCodeLoaded lsmpl memcpyPromBudgetSpecX) := by
  refine subroutine_ok_withLsCodeLoaded_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 promoteStackX)
      (promoteStackX - extHookStack))
    (subroutine_ok_withLsCodeLoaded_of_withLsCl (hC.memcpy (callerProg := callerProg)))
    (fun ⟨_dst, _src, _bs⟩ s0 => ?_)
    (fun ⟨_dst, _src, _bs⟩ s0 _sf => ?_)
    (fun _ _ _ => Entails.pure_left False.elim)
    (fun _ _ _ _ => rfl)
  · simp only [memcpyPromBudgetSpecX, sessionMemcpyBudgetSpec, sessionMemcpySpec, libcMemcpySpec,
      stackAt_sub_split_ser s0.sp extHookStack promoteStackX (by decide) (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)
  · simp only [memcpyPromBudgetSpecX, sessionMemcpyBudgetSpec, sessionMemcpySpec,
      stackAt_sub_split_ser s0.sp extHookStack promoteStackX (by decide) (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)

/-- Caller-block-polymorphic `withLsCl` form of `memcpy_prom_placed_okX`. -/
theorem memcpy_prom_placed_clX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok callerProg (lsρ lsMemcpySym)
      (withLsCl lsmpl memcpyPromBudgetSpecX) :=
  subroutine_ok_withLsCl_of_withLsCodeLoaded (memcpy_prom_placed_okX hC)

/-! ## 2. Local Unfoldings & Stepping Helpers -/

private def promGenPrevOut (A : RustAlloc) (recPtr : BitVec 64)
    (G : SessionGhost) (sess : Session (List (BitVec 8))) : SepProp :=
  ∃∗ prevCap' : BitVec 64, ∃∗ prevPtr' : BitVec 64,
    ⌜prevCap' ≠ 0#64⌝ ∗
    prevVecAt A recPtr prevCap' prevPtr'
      [encSessionMem (clearPendingGhost G) (clearPending sess)]

private def promZeroPrevOut (A : RustAlloc) (recPtr : BitVec 64)
    (G : SessionGhost) (sess : Session (List (BitVec 8))) : SepProp :=
  ∃∗ q : BitVec 64,
    HdrP recPtr 4#64 q 1#64 ∗
      Prev1 A q (encSessionMem (clearPendingGhost G) (clearPending sess))

private theorem archiveOverGenSpec_pre_fun_eq (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    (ArchiveDefsBudget.archiveOverGenSpec M A lim).pre =
      fun (x, st) s =>
        ⌜FitsEnv M lim st (ArchiveOverGenEnv x) ∧ s.readReg64 .x0 = x.recPtr ∧
          (encSessionMem (clearPendingGhost x.G) (clearPending x.sess)).length < 2 ^ 32⌝ ∗
          vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) x.recPtr x.prevCap x.prevPtr [] ∗
          sessionStateReprAt A.repAlloc (x.recPtr + 0x18#64) x.G x.sess ∗
          A.pool lim st s ∗ stackAt s.sp archiveStackX := by
  funext ⟨x, st⟩ s
  rw [archiveOverGenSpec_pre_eq, ← sepConj_assoc, pure_sepConj_pure]

private theorem archiveOverGenSpec_post_fun_eq (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    (ArchiveDefsBudget.archiveOverGenSpec M A lim).post =
      fun (x, st) s0 sf =>
        ∃∗ evs : List AllocEvent,
          ⌜ArchiveOverGenEnv x evs ∧ sf.trace = s0.trace⌝ ∗
          promGenPrevOut A.repAlloc x.recPtr x.G x.sess ∗
          ((x.recPtr + 0x18#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (x.recPtr + 0x20#64) 336 ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp archiveStackX := by
  funext ⟨x, st⟩ s0 sf
  rw [archiveOverGenSpec_post_eq]
  dsimp only [promGenPrevOut]
  simp only [← sepConj_assoc, pure_sepConj_pure]

private theorem promoteOverGenSpec_pre_fun_eq (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    (ArchiveDefsBudget.promoteOverGenSpec M A lim).pre =
      fun (x, st) s =>
        ⌜FitsEnv M lim st (PromoteOverGenEnv x) ∧
          s.readReg64 .x0 = x.recPtr ∧ s.readReg64 .x1 = x.src ∧ x.newBs.length = 344 ∧
          (encSessionMem (clearPendingGhost x.G) (clearPending x.sess)).length < 2 ^ 32⌝ ∗
          vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) x.recPtr x.prevCap x.prevPtr [] ∗
          sessionStateReprAt A.repAlloc (x.recPtr + 0x18#64) x.G x.sess ∗
          A.pool lim st s ∗ (x.src ↦ₛ x.newBs) ∗ stackAt s.sp promoteStackX := by
  funext ⟨x, st⟩ s
  rw [promoteOverGenSpec_pre_eq, ← sepConj_assoc, pure_sepConj_pure]

private theorem promoteOverGenSpec_post_fun_eq (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    (ArchiveDefsBudget.promoteOverGenSpec M A lim).post =
      fun (x, st) s0 sf =>
        ∃∗ evs : List AllocEvent,
          ⌜PromoteOverGenEnv x evs⌝ ∗
          ⌜sf.trace = s0.trace⌝ ∗
          promGenPrevOut A.repAlloc x.recPtr x.G x.sess ∗
          ((x.recPtr + 0x18#64) ↦ₛ x.newBs) ∗ (x.src ↦ₛ x.newBs) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp promoteStackX := by
  funext ⟨x, st⟩ s0 sf
  rw [promoteOverGenSpec_post_eq]
  dsimp only [promGenPrevOut]

private theorem archiveOverSpecX_pre_fun_eq (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    (ArchiveDefsBudget.archiveOverSpecX M A lim).pre =
      fun (x, st) s =>
        ⌜FitsEnv M lim st (ArchiveOverEnvX x) ∧ s.readReg64 .x0 = x.recPtr ∧
          x.prevPtr ≠ 0#64 ∧
          (encSessionMem (clearPendingGhost x.G) (clearPending x.sess)).length < 2 ^ 32⌝ ∗
          HdrP x.recPtr 0#64 x.prevPtr 0#64 ∗
          sessionStateReprAt A.repAlloc (x.recPtr + 0x18#64) x.G x.sess ∗
          A.pool lim st s ∗ stackAt s.sp archiveStackX := by
  funext ⟨x, st⟩ s
  rw [archiveOverSpecX_pre_eq, ← sepConj_assoc, pure_sepConj_pure]

private theorem archiveOverSpecX_post_fun_eq (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    (ArchiveDefsBudget.archiveOverSpecX M A lim).post =
      fun (x, st) s0 sf =>
        ∃∗ evs : List AllocEvent,
          ⌜ArchiveOverEnvX x evs ∧ sf.trace = s0.trace⌝ ∗
          promZeroPrevOut A.repAlloc x.recPtr x.G x.sess ∗
          ((x.recPtr + 0x18#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (x.recPtr + 0x20#64) 336 ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp archiveStackX := by
  funext ⟨x, st⟩ s0 sf
  rw [archiveOverSpecX_post_eq]
  dsimp only [promZeroPrevOut]
  simp only [← sepConj_assoc, pure_sepConj_pure]

private theorem promoteOverSpecX_pre_fun_eq (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    (ArchiveDefsBudget.promoteOverSpecX M A lim).pre =
      fun (x, st) s =>
        ⌜FitsEnv M lim st (PromoteOverEnvX x) ∧
          s.readReg64 .x0 = x.recPtr ∧ s.readReg64 .x1 = x.src ∧ x.newBs.length = 344 ∧
          x.prevPtr ≠ 0#64 ∧
          (encSessionMem (clearPendingGhost x.G) (clearPending x.sess)).length < 2 ^ 32⌝ ∗
          HdrP x.recPtr 0#64 x.prevPtr 0#64 ∗
          sessionStateReprAt A.repAlloc (x.recPtr + 0x18#64) x.G x.sess ∗
          A.pool lim st s ∗ (x.src ↦ₛ x.newBs) ∗ stackAt s.sp promoteStackX := by
  funext ⟨x, st⟩ s
  rw [promoteOverSpecX_pre_eq, ← sepConj_assoc, pure_sepConj_pure]

private theorem promoteOverSpecX_post_fun_eq (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    (ArchiveDefsBudget.promoteOverSpecX M A lim).post =
      fun (x, st) s0 sf =>
        ∃∗ evs : List AllocEvent,
          ⌜PromoteOverEnvX x evs⌝ ∗
          ⌜sf.trace = s0.trace⌝ ∗
          promZeroPrevOut A.repAlloc x.recPtr x.G x.sess ∗
          ((x.recPtr + 0x18#64) ↦ₛ x.newBs) ∗ (x.src ↦ₛ x.newBs) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp promoteStackX := by
  funext ⟨x, st⟩ s0 sf
  rw [promoteOverSpecX_post_eq]
  dsimp only [promZeroPrevOut]

private theorem bv_sub_add_lit_local (x a b : BitVec 64) : x - a + b = x - (a - b) := by
  bv_omega

@[local simp, local wp_norm, local arm64_norm]
private theorem sp_sub_32_align_local (sp : BitVec 64) :
    ((sp - 32#64) &&& 15#64) = (sp &&& 15#64) := by bv_robdd

@[local simp, local wp_norm, local arm64_norm]
private theorem sp_sub_32_add_32_local (sp : BitVec 64) :
    sp - 32#64 + 32#64 = sp := by bv_omega

private theorem sepWP_expose_sp {prog : Program} {target : BitVec 64} {s : State}
    {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ sp', s.sp = sp' → SepWP prog target s P post oom) :
    SepWP prog target s P post oom :=
  h s.sp rfl

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit_local BitVec.toNat_zero

/-! ## 3. Relocatable `[LibsignalPlacement]` `promote_state` Proofs (Block `47`) -/

section Placed

attribute [local irreducible]
  encSessionMem sessionStateReprAt FitsEnv promGenPrevOut promZeroPrevOut

local macro "wp_done_call " hcl:ident : tactic =>
  `(tactic| (
    apply SepWP.done
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm]; assumption)
    intro $hcl:ident
    simp only [wp_norm, arm64_norm] at $hcl:ident))

/-- Relocatable `archive_over_gen_placed_ok_of_contracts` lifted onto `lsProg_47 H` at
`lsmpl.base 51` from explicit leaf contracts. -/
theorem archive_prom_gen_placed_ok_of_leaves [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (hGrow : subroutine_ok (lsProg_51 H) (lsmpl.base 621)
      (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc H)
    (hDrop : DropSessionStructureLocal1PlacedOkX M A lim H) :
    subroutine_ok (lsProg_47 H) (lsmpl.base 51)
      (withLsCodeLoaded lsmpl (ArchiveDefsBudget.archiveOverGenSpec M A lim)) :=
  subroutine_ok_withLsCodeLoaded_of_withLsCl
    (archive_over_gen_placed_cl_of_contracts (callerProg := lsProg_47 H) hC hGrow hRaw hDrop)

/-- Relocatable `archive_over_gen_placed_ok_of_contracts` lifted onto `lsProg_47 H` at
`lsmpl.base 51`, discharging `DropSessionStructureLocal1PlacedOkX` from `hC.alloc`. -/
theorem archive_prom_gen_placed_ok_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (hGrow : subroutine_ok (lsProg_51 H) (lsmpl.base 621)
      (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc H) :
    subroutine_ok (lsProg_47 H) (lsmpl.base 51)
      (withLsCodeLoaded lsmpl (ArchiveDefsBudget.archiveOverGenSpec M A lim)) :=
  archive_prom_gen_placed_ok_of_leaves hC hGrow hRaw
    (drop_session_structure_local1_placed_ok_ext hC.alloc)

/-- Relocatable `archive_over_placed_ok_of_contracts` lifted onto `lsProg_47 H` at
`lsmpl.base 51` from explicit leaf contracts. -/
theorem archive_prom_placed_ok_of_leaves [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (hGrow : subroutine_ok (lsProg_51 H) (lsmpl.base 621)
      (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc H)
    (hDrop : DropSessionStructureLocal1PlacedOkX M A lim H) :
    subroutine_ok (lsProg_47 H) (lsmpl.base 51)
      (withLsCodeLoaded lsmpl (ArchiveDefsBudget.archiveOverSpecX M A lim)) :=
  subroutine_ok_withLsCodeLoaded_of_withLsCl
    (archive_over_placed_cl_of_contracts (callerProg := lsProg_47 H) hC hGrow hRaw hDrop)

/-- Relocatable `archive_over_placed_ok_of_contracts` lifted onto `lsProg_47 H` at
`lsmpl.base 51`, discharging `DropSessionStructureLocal1PlacedOkX` from `hC.alloc`. -/
theorem archive_prom_placed_ok_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (hGrow : subroutine_ok (lsProg_51 H) (lsmpl.base 621)
      (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc H) :
    subroutine_ok (lsProg_47 H) (lsmpl.base 51)
      (withLsCodeLoaded lsmpl (ArchiveDefsBudget.archiveOverSpecX M A lim)) :=
  archive_prom_placed_ok_of_leaves hC hGrow hRaw
    (drop_session_structure_local1_placed_ok_ext hC.alloc)

set_option maxHeartbeats 800000 in
/-- Relocatable `PromoteStateOverGenPlacedOk` (Block `47`) from `SerContractsXPlaced`, a
Block `51`→`621` `grow_one` budget contract, `EncodeRawPreallocPlacedOkX`, and
`DropSessionStructureLocal1PlacedOkX`. -/
theorem promote_state_over_gen_placed_ok_of_leaves [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (hGrow : subroutine_ok (lsProg_51 H) (lsmpl.base 621)
      (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc H)
    (hDrop : DropSessionStructureLocal1PlacedOkX M A lim H) :
    PromoteStateOverGenPlacedOk M A lim H := by
  have harch :=
    archive_over_gen_placed_cl_of_contracts (callerProg := lsProg_47 H) hC hGrow hRaw hDrop
  have hmemcpy := memcpy_prom_placed_clX (callerProg := lsProg_47 H) hC
  clear hGrow hDrop
  change subroutine_ok (lsProg_47 H) (lsmpl.base 51)
    (withLsCl lsmpl (ArchiveDefsBudget.archiveOverGenSpec M A lim)) at harch
  change subroutine_ok (lsProg_47 H) (lsρ lsMemcpySym)
    (withLsCl lsmpl memcpyPromBudgetSpecX) at hmemcpy
  dsimp only [withLsCl, memcpyPromBudgetSpecX] at harch hmemcpy
  rw [archiveOverGenSpec_pre_fun_eq M A lim, archiveOverGenSpec_post_fun_eq M A lim] at harch
  unfold PromoteStateOverGenPlacedOk withLsCodeLoaded
  rw [promoteOverGenSpec_pre_fun_eq M A lim, promoteOverGenSpec_post_fun_eq M A lim]
  wp_init x s0
  obtain ⟨⟨recPtr, src, prevCap, prevPtr, G, sess, newBs⟩, st⟩ := x
  dsimp only [PromoteOverGenEnv] at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hFit : FitsEnv M lim st (ArchiveCoreEnv prevCap G sess) := by assumption
  have hlen : newBs.length = 344 := by assumption
  have hlen_enc : (encSessionMem (clearPendingGhost G) (clearPending sess)).length < 2 ^ 32 := by
    assumption
  apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 51)
  conv => arg 4; rw [stackAt_promote_splitX s0.sp]
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro v0
  apply SepWP.exists_left; intro v1
  apply SepWP.exists_left; intro v2
  apply SepWP.exists_left; intro v3
  wp_steps_sync_pool (lsmpl.base 51)
  wp_done_call hcl1
  have hFit_arch : FitsEnv M lim st (ArchiveOverGenEnv ⟨recPtr, prevCap, prevPtr, G, sess⟩) := hFit
  wp_call harch (⟨recPtr, prevCap, prevPtr, G, sess⟩, st)
  apply sepWP_seq_lscl (pl := lsmpl) (mid := lsρ lsMemcpySym); · assumption
  conv => arg 4; simp only [wp_norm, arm64_norm]
  wp_steps_sync_pool (lsρ lsMemcpySym)
  refine SepWP.fold
    (pointsTo64_memRegion_336_entails_344X recPtr _)
    (by sep_focus) ?_ -- framing-bypass: equality-frame combinator requires P = P1 * F
  refine SepWP.fold
    (stackAt_promote_mergeX s0.sp _ _ _ _)
    (by sep_focus) ?_ -- framing-bypass: equality-frame combinator requires P = P1 * F
  wp_done_call hcl2
  rw [← hlen]
  apply sepWP_expose_sp; intro sp_cur hsp_cur
  have hsp_eq : s0.sp = sp_cur := by
    rw [← hsp_cur]
    simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm] at hsp_sf ⊢
  conv => arg 4; pattern (stackAt s0.sp promoteStackX); rw [hsp_eq, ← hsp_cur]
  wp_call hmemcpy (recPtr + 24#64, src, newBs)
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_done

/-- Relocatable `PromoteStateOverGenPlacedOk` (Block `47`) from `SerContractsXPlaced`, a
Block `51`→`621` `grow_one` budget contract, and `EncodeRawPreallocPlacedOkX`
(discharging `DropSessionStructureLocal1PlacedOkX` automatically from `hC.alloc`). -/
theorem promote_state_over_gen_placed_ok_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (hGrow : subroutine_ok (lsProg_51 H) (lsmpl.base 621)
      (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc H) :
    PromoteStateOverGenPlacedOk M A lim H :=
  promote_state_over_gen_placed_ok_of_leaves hC hGrow hRaw
    (drop_session_structure_local1_placed_ok_ext hC.alloc)

/-- Caller-block-polymorphic `withLsCl` form of `promote_state_over_gen_placed_ok_of_leaves`. -/
theorem promote_state_over_gen_placed_cl_of_leaves [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H)
    (hGrow : subroutine_ok (lsProg_51 H) (lsmpl.base 621)
      (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc H)
    (hDrop : DropSessionStructureLocal1PlacedOkX M A lim H) :
    subroutine_ok callerProg (lsmpl.base 47)
      (withLsCl lsmpl (ArchiveDefsBudget.promoteOverGenSpec M A lim)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg)
    (promote_state_over_gen_placed_ok_of_leaves hC hGrow hRaw hDrop)

/-- Caller-block-polymorphic `withLsCl` form of `promote_state_over_gen_placed_ok_of_contracts`. -/
theorem promote_state_over_gen_placed_cl_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H)
    (hGrow : subroutine_ok (lsProg_51 H) (lsmpl.base 621)
      (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc H) :
    subroutine_ok callerProg (lsmpl.base 47)
      (withLsCl lsmpl (ArchiveDefsBudget.promoteOverGenSpec M A lim)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg)
    (promote_state_over_gen_placed_ok_of_contracts hC hGrow hRaw)

set_option maxHeartbeats 800000 in
/-- Relocatable `PromoteStateOverPlacedOkX` (Block `47`, `prevCap = 0#64` specialization) from
`SerContractsXPlaced`, a Block `51`→`621` `grow_one` budget contract,
`EncodeRawPreallocPlacedOkX`, and `DropSessionStructureLocal1PlacedOkX`. -/
theorem promote_state_over_placed_ok_of_leaves [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (hGrow : subroutine_ok (lsProg_51 H) (lsmpl.base 621)
      (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc H)
    (hDrop : DropSessionStructureLocal1PlacedOkX M A lim H) :
    PromoteStateOverPlacedOkX M A lim H := by
  have harch :=
    archive_over_placed_cl_of_contracts (callerProg := lsProg_47 H) hC hGrow hRaw hDrop
  have hmemcpy := memcpy_prom_placed_clX (callerProg := lsProg_47 H) hC
  clear hGrow hDrop
  change subroutine_ok (lsProg_47 H) (lsmpl.base 51)
    (withLsCl lsmpl (ArchiveDefsBudget.archiveOverSpecX M A lim)) at harch
  change subroutine_ok (lsProg_47 H) (lsρ lsMemcpySym)
    (withLsCl lsmpl memcpyPromBudgetSpecX) at hmemcpy
  dsimp only [withLsCl, memcpyPromBudgetSpecX] at harch hmemcpy
  rw [archiveOverSpecX_pre_fun_eq M A lim, archiveOverSpecX_post_fun_eq M A lim] at harch
  unfold PromoteStateOverPlacedOkX withLsCodeLoaded
  rw [promoteOverSpecX_pre_fun_eq M A lim, promoteOverSpecX_post_fun_eq M A lim]
  wp_init x s0
  obtain ⟨⟨recPtr, src, prevPtr, G, sess, newBs⟩, st⟩ := x
  dsimp only [PromoteOverEnvX] at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hFit : FitsEnv M lim st (ArchiveCoreEnv 0#64 G sess) := by assumption
  have hlen : newBs.length = 344 := by assumption
  have hprev_ne : prevPtr ≠ 0#64 := by assumption
  have hlen_enc : (encSessionMem (clearPendingGhost G) (clearPending sess)).length < 2 ^ 32 := by
    assumption
  apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 51)
  conv => arg 4; rw [stackAt_promote_splitX s0.sp]
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro v0
  apply SepWP.exists_left; intro v1
  apply SepWP.exists_left; intro v2
  apply SepWP.exists_left; intro v3
  wp_steps_sync_pool (lsmpl.base 51)
  wp_done_call hcl1
  have hFit_arch : FitsEnv M lim st (ArchiveOverEnvX ⟨recPtr, prevPtr, G, sess⟩) := hFit
  wp_call harch (⟨recPtr, prevPtr, G, sess⟩, st)
  apply sepWP_seq_lscl (pl := lsmpl) (mid := lsρ lsMemcpySym); · assumption
  conv => arg 4; simp only [wp_norm, arm64_norm]
  wp_steps_sync_pool (lsρ lsMemcpySym)
  refine SepWP.fold
    (pointsTo64_memRegion_336_entails_344X recPtr _)
    (by sep_focus) ?_ -- framing-bypass: equality-frame combinator requires P = P1 * F
  refine SepWP.fold
    (stackAt_promote_mergeX s0.sp _ _ _ _)
    (by sep_focus) ?_ -- framing-bypass: equality-frame combinator requires P = P1 * F
  wp_done_call hcl2
  rw [← hlen]
  apply sepWP_expose_sp; intro sp_cur hsp_cur
  have hsp_eq : s0.sp = sp_cur := by
    rw [← hsp_cur]
    simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm] at hsp_sf ⊢
  conv => arg 4; pattern (stackAt s0.sp promoteStackX); rw [hsp_eq, ← hsp_cur]
  wp_call hmemcpy (recPtr + 24#64, src, newBs)
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_done

/-- Relocatable `PromoteStateOverPlacedOkX` (Block `47`) from `SerContractsXPlaced`, a
Block `51`→`621` `grow_one` budget contract, and `EncodeRawPreallocPlacedOkX`
(discharging `DropSessionStructureLocal1PlacedOkX` automatically from `hC.alloc`). -/
theorem promote_state_over_placed_ok_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (hGrow : subroutine_ok (lsProg_51 H) (lsmpl.base 621)
      (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc H) :
    PromoteStateOverPlacedOkX M A lim H :=
  promote_state_over_placed_ok_of_leaves hC hGrow hRaw
    (drop_session_structure_local1_placed_ok_ext hC.alloc)

/-- Caller-block-polymorphic `withLsCl` form of `promote_state_over_placed_ok_of_leaves`. -/
theorem promote_state_over_placed_cl_of_leaves [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H)
    (hGrow : subroutine_ok (lsProg_51 H) (lsmpl.base 621)
      (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc H)
    (hDrop : DropSessionStructureLocal1PlacedOkX M A lim H) :
    subroutine_ok callerProg (lsmpl.base 47)
      (withLsCl lsmpl (ArchiveDefsBudget.promoteOverSpecX M A lim)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg)
    (promote_state_over_placed_ok_of_leaves hC hGrow hRaw hDrop)

/-- Caller-block-polymorphic `withLsCl` form of `promote_state_over_placed_ok_of_contracts`. -/
theorem promote_state_over_placed_cl_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H)
    (hGrow : subroutine_ok (lsProg_51 H) (lsmpl.base 621)
      (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc H) :
    subroutine_ok callerProg (lsmpl.base 47)
      (withLsCl lsmpl (ArchiveDefsBudget.promoteOverSpecX M A lim)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg)
    (promote_state_over_placed_ok_of_contracts hC hGrow hRaw)

end Placed

end LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchivePromoteBudget
