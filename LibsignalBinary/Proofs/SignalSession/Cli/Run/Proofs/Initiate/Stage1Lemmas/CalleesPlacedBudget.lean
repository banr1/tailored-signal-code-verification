/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.CalleesBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.CalleesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.ModelAndLayoutPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerializeBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.Common.StringClonePlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.SegB_ErrPlaced

/-!
# Budget-Threaded Relocatable Stage 1 Direct `BL` Wrappers and Error Epilogue

Provides `RustCliAllocBudget M` and `VmPreserved` Stage 1 direct `BL` callee wrappers at residual
stack `stk - cliInitiateFrame` and the shared error epilogue `stage1_epilogue_err_placed_ok`
(`0x0350 → ret`) on `initProgPlaced mmpl gh W`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.CalleesPlacedBudget

noncomputable section

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
  (LibsignalHooks LibsignalPlacement lsProg_205 lsRustNoAllocShimSym ls_hook_ok_ultra_of_mem lsmpl
   lsρ)
open CryptoVerification.CliHandshake.InitiatePlaced (blkPl_521 lsProg_521)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives modelPrims)
open CryptoVerification.E2E.Pqxdh.Shared (pqxdhHookStack)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (extract_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_plain withLsCodeRoLoaded)
open CryptoVerification.LibsignalSessionRepr (VecGhost vecGhostAt)
open CryptoVerification.LibsignalSpqrV1 (Params)
open CryptoVerification.LibsignalTripleRatchet
  (PublicKeySerializeCall boxU8Buf extHookStack memcpyName noAllocShimSpec
   publicKeySerializeStackX sessionMemcpyRegionSpec withStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr (protocolAddressAt)
open CryptoVerification.RustHeap (allocFailedIn vecU8)
open CryptoVerification.SignalSession
  (CliHooks cliExternsPlaced lsRustDeallocSymCli lsStringCloneSym)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.MainHops (storesAt)
open CryptoVerification.SignalSession.Cli.RunCompose
  (InitGhost RunSem cliBundleAt initResAt slotOut slotTrace)
open CryptoVerification.SignalSession.Cli.RunProofs (cliInitiateFrame cliInitiateNeed)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
  (InInitiatePlaced initLocalsSize initProgPlaced initSaved satisfies_withLsCodeRoLoaded_pre
   stk_ge_frame stk_sub_ge_base transfer_withLsCodeRoLoaded)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas
  (initArgsAtPlaced_entails_memRegion initSaved_entails_memRegion memcpyScratchSpec
   pointsTo64_low_byte_entails stackAt_entry_split stackAt_sub_split_local stage1Err stage1VecBuf
   stage1VecBuf_to_vecU8 stage2LocalsPlaced_entails_memRegion vecU8_unpack_words verifySigAtStkSpec
   words_to_plain11_initResAt words_to_untrusted_initResAt)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas
  (calleeSavedPreserved_of_regs initSaved_eq_fsp memRegion_48_eq_words6
   sepWPp_of_sepWP_exit slotTrace_of_eq spAligned_mask_add_4096 spAligned_mask_add_7312
   spAligned_mask_of_frame)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas.CliStage2Norm
  (extractLsb_append_hi extractLsb_append_lo extractLsb_pack32_0 extractLsb_pack32_0_16
   extractLsb_pack32_8 extractLsb_pack32_16 extractLsb_pack32_16_16 extractLsb_pack32_24
   fs_setMem_pre fs_setPC_pre fs_setPState_pre fs_writeReg32_pre fs_writeReg64_pre fs_writeReg_pre
   fs_writeVReg128_pre readReg32_setMem_setPC_pre readReg32_setPC_pre readReg32_writeVReg128_pre
   readReg64_setMem_setPC_pre readReg64_setPC_pre readReg64_writeVReg128_pre
   readReg_setMem_setPC_pre readReg_setPC_pre readReg_writeVReg128_pre readVReg128_setMem_pre
   readVReg128_setMem_setPC_pre readVReg128_setPC_pre readVReg128_setPState_pre
   readVReg128_writeReg32_pre readVReg128_writeReg64_pre readVReg128_writeReg_pre
   sp_setMem_setPC_pre sp_setPC_pre sp_writeVReg128_pre trace_writeReg32_pre trace_writeReg_pre
   trace_writeVReg128_pre)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget VmPreserved
   rustAllocEvents rustCliDeallocBudgetExternSpecWithStack)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge
  (StringCloneEnv fitsEvents_stringClone_of_fitsEnv stringCloneBudgetSpec stringCloneEvents
   stringCloneEvents_eq_of_env)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
  (InitExitPostPlaced initSlotSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget
  (InitLocalCalleesPlaced kemPubSerializeInnerSpec verifySignatureInnerSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.CalleesBudget
  (pubKeySerializeAtStkSpec stringCloneAtStkSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (fitsEnv_publicKeySerialize_iff noAllocShimBudgetSpec publicKeySerializeEvents
   publicKeySerializeSpecWithStack publicKeySerializeSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerializeBudget
  (public_key_serialize_placed_ok_x)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)
open Arm64.Obj (MultiPlacement)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

export CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas
  (initArgsAtPlaced_entails_memRegion pointsTo64_low_byte_entails stage1Err stage1VecBuf
   stage1VecBuf_to_vecU8)
export CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas
  (stage2LocalsPlaced_entails_memRegion vecU8_unpack_words words_to_plain11_initResAt
   words_to_untrusted_initResAt)
export LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.CalleesBudget
  (pubKeySerializeAtStkSpec stringCloneAtStkSpec)

/-! ## Direct `BL` callee wrappers at residual stack `stk - cliInitiateFrame` -/

theorem fitsEnv_stringClone_iff {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {g : VecGhost} :
    FitsEnv M lim st (StringCloneEnv g) ↔ FitsEvents M lim st (stringCloneEvents g) :=
  ⟨fitsEvents_stringClone_of_fitsEnv M lim st g,
   fun h _evs he => stringCloneEvents_eq_of_env he ▸ h⟩

private theorem hookSat_noAllocShimBudget_of_withVmPreserved {H : LibsignalHooks}
    (h : HookSat H lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec)) :
    HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec := by
  rcases h with ⟨fn, hfn, hok⟩
  refine ⟨fn, hfn, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hok x R s0 hrun hpre hsp with ⟨hkf, hsym, hout⟩
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withVmPreserved, noAllocShimSpec, noAllocShimBudgetSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hpost.2.1, hpost.1⟩, hpost.2.2⟩
  · exact Or.inr hrest

/-- Lifts `subroutine_ok` for `withLsCodeRoLoaded lsmpl (spec sub)` from `sub` to `full` stack on `initProgPlaced`. -/
theorem lift_stack_lscro [LibsignalPlacement] {α : Type} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {e : BitVec 64} {spec : Nat → Spec α} {sub full : Nat}
    (hsub : subroutine_ok (initProgPlaced mmpl gh W) e (withLsCodeRoLoaded lsmpl (spec sub)))
    (_hle : sub ≤ full) (_hhi : full ≤ 2 ^ 64)
    (hpreEq : ∀ x s, (spec full).pre x s =
      memRegion (s.sp - BitVec.ofNat 64 full) (full - sub) ∗ (spec sub).pre x s)
    (hpostEq : ∀ x s0 sf, (spec full).post x s0 sf =
      memRegion (s0.sp - BitVec.ofNat 64 full) (full - sub) ∗ (spec sub).post x s0 sf)
    (hpanEq : ∀ x s0 sf, (spec sub).onPanic x s0 sf ⊢
      ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap)
    (hpanFull : ∀ x s0 sf,
      ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ⊢ (spec full).onPanic x s0 sf)
    (hexit : ∀ x c s0 sf, (spec sub).onExit x c s0 sf = ⌜False⌝)
    (hoom : ∀ x s0 sf, (spec sub).onOom x s0 sf = ⌜False⌝) :
    subroutine_ok (initProgPlaced mmpl gh W) e (withLsCodeRoLoaded lsmpl (spec full)) := by
  apply subroutine_ok.of_codeLoaded
  intro gx R s0 hpc hrun hpre hsp _
  obtain ⟨hinv, hpre⟩ := extract_withLsCodeRoLoaded hpre
  rw [hpreEq gx s0] at hpre
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 full) (full - sub)
  have hpre0 : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl (spec sub)).pre gx s0 ∗ (stkRem ∗ R) := by
    refine satisfies_withLsCodeRoLoaded_pre hinv ?_
    dsimp only [stkRem]
    convert hpre using 1; sep_ac_rfl
  refine subroutine_ok.mono_outcome hsub gx (stkRem ∗ R) s0 hpc hrun hpre0 hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨c, _, hq⟩ | ⟨_, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    change sf.mem ⊨ (spec full).post gx s0 sf ∗ R
    change sf.mem ⊨ (spec sub).post gx s0 sf ∗ (stkRem ∗ R) at hq
    rw [hpostEq gx s0 sf]
    dsimp only [stkRem] at hq
    convert hq using 1; sep_ac_rfl
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    change sf.mem ⊨ (spec sub).onPanic gx s0 sf ∗ (stkRem ∗ R) at hq
    change sf.mem ⊨ (spec full).onPanic gx s0 sf ∗ R
    have h1 : (spec sub).onPanic gx s0 sf ∗ stkRem ⊢ (spec full).onPanic gx s0 sf := by
      refine Entails.trans (sepConj_mono_left (hpanEq gx s0 sf)) ?_
      rw [sepConj_assoc]
      exact Entails.trans (sepConj_mono_right (entails_anyHeap _)) (hpanFull gx s0 sf)
    rw [← sepConj_assoc] at hq
    exact Satisfies.mono (sepConj_mono_left h1) hq
  · change sf.mem ⊨ (spec sub).onExit gx c s0 sf ∗ (stkRem ∗ R) at hq
    rw [hexit] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · change sf.mem ⊨ (spec sub).onOom gx s0 sf ∗ (stkRem ∗ R) at hq
    rw [hoom] at hq
    exact (not_satisfies_false_sepConj hq).elim

/-- Budget-threaded `__rust_dealloc` wrapper at residual stack `stk - cliInitiateFrame`. -/
theorem init_dealloc_placed_ok_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {B : RunBudgets} {stk : Nat}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsρ lsRustDeallocSymCli)
      (withLsCodeRoLoaded lsmpl
        (rustCliDeallocBudgetExternSpecWithStack M A lim (stk - cliInitiateFrame))) := by
  have hbase : subroutine_ok (initProgPlaced mmpl gh W) (lsρ lsRustDeallocSymCli)
      (withLsCodeRoLoaded lsmpl
        (rustCliDeallocBudgetExternSpecWithStack M A lim extHookStack)) :=
    transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W) hh.alloc.dealloc
  have hle : extHookStack ≤ stk - cliInitiateFrame := by
    have h1 := stk_sub_ge_base hstk
    have hext : extHookStack ≤ 65536 := by decide
    omega
  have hhi : stk - cliInitiateFrame ≤ 2 ^ 64 := by omega
  apply subroutine_ok.of_codeLoaded
  intro gx R s0 hpc hrun hpre hsp _
  obtain ⟨hinv, hpre⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [rustCliDeallocBudgetExternSpecWithStack] at hpre
  rw [stackAt_sub_split_local s0.sp hle hhi] at hpre
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 (stk - cliInitiateFrame))
    ((stk - cliInitiateFrame) - extHookStack)
  have hpre0 : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl
        (rustCliDeallocBudgetExternSpecWithStack M A lim extHookStack)).pre gx s0 ∗
        (stkRem ∗ R) := by
    refine satisfies_withLsCodeRoLoaded_pre hinv ?_
    dsimp only [rustCliDeallocBudgetExternSpecWithStack, stkRem]
    convert hpre using 1; sep_ac_rfl
  refine subroutine_ok.mono_outcome hbase gx (stkRem ∗ R) s0 hpc hrun hpre0 hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    change sf.mem ⊨
      (rustCliDeallocBudgetExternSpecWithStack M A lim (stk - cliInitiateFrame)).post gx s0 sf ∗ R
    dsimp only [withLsCodeRoLoaded, rustCliDeallocBudgetExternSpecWithStack] at hq ⊢
    rw [stackAt_sub_split_local s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; sep_ac_rfl
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

/-- Budget-threaded `<String as Clone>::clone` wrapper at residual stack `stk - cliInitiateFrame`. -/
theorem init_stringClone_placed_ok_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {B : RunBudgets} {stk : Nat}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 623)
      (withLsCodeRoLoaded lsmpl
        (stringCloneAtStkSpec M A lim (stk - cliInitiateFrame))) := by
  have hbase : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 623)
      (withLsCodeRoLoaded lsmpl (stringCloneBudgetSpec M A lim)) :=
    CryptoVerification.LibsignalPublicApi.StoreKit.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
      (LibsignalBinary.Proofs.Common.StringClonePlacedBudget.stringCloneBudget_placed_vm_codeLoaded_ok
        (callerProg := initProgPlaced mmpl gh W) (i := 521)
        hh.shimVm hh.rawAlloc hh.allocMemcpyVm (by decide))
  have hle : extHookStack ≤ stk - cliInitiateFrame := by
    have h1 := stk_sub_ge_base hstk
    have hext : extHookStack ≤ 65536 := by decide
    omega
  have hhi : stk - cliInitiateFrame ≤ 2 ^ 64 := by omega
  apply subroutine_ok.of_codeLoaded
  rintro ⟨⟨p, ret, g⟩, st⟩ R s0 hpc hrun hpre hsp _
  obtain ⟨hinv, hpre⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [stringCloneAtStkSpec] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hFit, hlr⟩, hmem⟩
  have hFitEnv : FitsEnv M lim st (StringCloneEnv g) := fitsEnv_stringClone_iff.mpr hFit
  rw [stackAt_sub_split_local s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 (stk - cliInitiateFrame))
    ((stk - cliInitiateFrame) - extHookStack)
  have hpre0 : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl (stringCloneBudgetSpec M A lim)).pre (p, ret, g, st) s0 ∗
        (stkRem ∗ R) := by
    refine satisfies_withLsCodeRoLoaded_pre hinv ?_
    dsimp only [stringCloneBudgetSpec, stkRem]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hFitEnv, hlr⟩, ?_⟩
    convert hmem using 1; sep_ac_rfl
  refine subroutine_ok.mono_outcome hbase (p, ret, g, st) (stkRem ∗ R) s0 hpc hrun hpre0 hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    change sf.mem ⊨
      (stringCloneAtStkSpec M A lim (stk - cliInitiateFrame)).post ((p, ret, g), st) s0 sf ∗ R
    dsimp only [withLsCodeRoLoaded, stringCloneBudgetSpec, stringCloneAtStkSpec] at hq ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hq
    rcases hq with ⟨evs, hq⟩
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨⟨htr, hevs⟩, hq⟩
    have heq := stringCloneEvents_eq_of_env hevs
    subst heq
    rw [stackAt_sub_split_local s0.sp hle hhi]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    dsimp only [stkRem] at hq
    convert hq using 1; sep_ac_rfl
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

/-- Budget-threaded `<PublicKey>::serialize` (block `205`) wrapper at residual stack `stk - cliInitiateFrame`. -/
theorem init_pubKeySerialize_placed_ok_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {B : RunBudgets} {stk : Nat}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 205)
      (withLsCodeRoLoaded lsmpl
        (pubKeySerializeAtStkSpec M A lim (stk - cliInitiateFrame))) := by
  have h205 : subroutine_ok (lsProg_205 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 205) (publicKeySerializeSpecX M A lim) :=
    public_key_serialize_placed_ok_x
      (hookSat_noAllocShimBudget_of_withVmPreserved hh.shim) hh.rawAlloc
  have hbase : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 205)
      (withLsCodeRoLoaded lsmpl (publicKeySerializeSpecX M A lim)) :=
    transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W)
      (subroutine_ok_withLsCodeRoLoaded_of_plain h205)
  have hle : publicKeySerializeStackX ≤ stk - cliInitiateFrame := by
    have h1 := stk_sub_ge_base hstk
    have hp : publicKeySerializeStackX ≤ 65536 := by decide
    omega
  have hhi : stk - cliInitiateFrame ≤ 2 ^ 64 := by omega
  apply subroutine_ok.of_codeLoaded
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp _
  obtain ⟨hinv, hpre⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [pubKeySerializeAtStkSpec] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hFit⟩, hmem⟩
  have hFitEnv : FitsEnv M lim st _ := fitsEnv_publicKeySerialize_iff.mpr hFit
  rw [stackAt_sub_split_local s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 (stk - cliInitiateFrame))
    ((stk - cliInitiateFrame) - publicKeySerializeStackX)
  have hpre0 : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl (publicKeySerializeSpecX M A lim)).pre (x, st) s0 ∗
        (stkRem ∗ R) := by
    refine satisfies_withLsCodeRoLoaded_pre hinv ?_
    dsimp only [publicKeySerializeSpecX, publicKeySerializeSpecWithStack, stkRem]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hFitEnv⟩, ?_⟩
    dsimp only [publicKeySerializeStackX] at hmem
    convert hmem using 1; sep_ac_rfl
  refine subroutine_ok.mono_outcome hbase (x, st) (stkRem ∗ R) s0 hpc hrun hpre0 hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    change sf.mem ⊨
      (pubKeySerializeAtStkSpec M A lim (stk - cliInitiateFrame)).post (x, st) s0 sf ∗ R
    dsimp only [withLsCodeRoLoaded, publicKeySerializeSpecX, publicKeySerializeSpecWithStack,
      pubKeySerializeAtStkSpec, publicKeySerializeEvents] at hq ⊢
    rw [stackAt_sub_split_local s0.sp hle hhi]
    dsimp only [stkRem, publicKeySerializeStackX] at hq ⊢
    convert hq using 1; sep_ac_rfl
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

/-- `VmPreserved`-strengthened `<PublicKey>::verify_signature` (block `203`) wrapper at residual stack `stk - cliInitiateFrame`. -/
theorem init_verifySig_vm_placed_ok_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {stk : Nat}
    (hLocal : InitLocalCalleesPlaced A lim InitStateEnv mmpl gh W stk)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 203)
      (withLsCodeRoLoaded lsmpl
        (withVmPreserved
          (verifySigAtStkSpec (modelPrims X ⟨W.C, W.Q⟩) (stk - cliInitiateFrame)))) := by
  have hbase := hLocal.verifySignature X
  have hle : pqxdhHookStack + 1280 ≤ stk - cliInitiateFrame := by
    have h1 := stk_sub_ge_base hstk
    have hp : pqxdhHookStack + 1280 ≤ 516880 := by decide
    omega
  have hhi : stk - cliInitiateFrame ≤ 2 ^ 64 := by omega
  have hspecEq :
      verifySignatureInnerSpec (modelPrims X ⟨W.C, W.Q⟩) =
        withVmPreserved
          (verifySigAtStkSpec (modelPrims X ⟨W.C, W.Q⟩) (pqxdhHookStack + 1280)) := rfl
  rw [hspecEq] at hbase
  apply subroutine_ok.of_codeLoaded
  intro gx R s0 hpc hrun hpre hsp _
  obtain ⟨hinv, hpre⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [withVmPreserved, verifySigAtStkSpec] at hpre
  rw [stackAt_sub_split_local s0.sp hle hhi] at hpre
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 (stk - cliInitiateFrame))
    ((stk - cliInitiateFrame) - (pqxdhHookStack + 1280))
  have hpre0 : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl
        (withVmPreserved
          (verifySigAtStkSpec (modelPrims X ⟨W.C, W.Q⟩)
            (pqxdhHookStack + 1280)))).pre gx s0 ∗ (stkRem ∗ R) := by
    refine satisfies_withLsCodeRoLoaded_pre hinv ?_
    dsimp only [withVmPreserved, verifySigAtStkSpec, stkRem]
    convert hpre using 1; sep_ac_rfl
  refine subroutine_ok.mono_outcome hbase gx (stkRem ∗ R) s0 hpc hrun hpre0 hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    change sf.mem ⊨
      (withVmPreserved
        (verifySigAtStkSpec (modelPrims X ⟨W.C, W.Q⟩) (stk - cliInitiateFrame))).post gx s0 sf ∗ R
    dsimp only [withLsCodeRoLoaded, withVmPreserved, verifySigAtStkSpec] at hq ⊢
    rw [stackAt_sub_split_local s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; sep_ac_rfl
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

theorem init_verifySig_placed_ok_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {stk : Nat}
    (hLocal : InitLocalCalleesPlaced A lim InitStateEnv mmpl gh W stk)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 203)
      (withLsCodeRoLoaded lsmpl
        (verifySigAtStkSpec (modelPrims X ⟨W.C, W.Q⟩) (stk - cliInitiateFrame))) := by
  refine subroutine_ok_mono (init_verifySig_vm_placed_ok_at (X := X) (B := B) hLocal hstk hstk64)
    (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [withLsCodeRoLoaded, withVmPreserved] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq
  exact hq.2

/-- Budget-threaded `<kem::Key<Public>>::serialize [local#1]` (block `523`) wrapper at residual stack `stk - cliInitiateFrame`. -/
theorem init_kemPubSerialize_placed_ok_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {stk : Nat}
    (hLocal : InitLocalCalleesPlaced A lim InitStateEnv mmpl gh W stk) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 523)
      (withLsCodeRoLoaded lsmpl
        (kemPubSerializeInnerSpec A lim (stk - cliInitiateFrame))) :=
  hLocal.kemPubSerialize

/-- `VmPreserved`-strengthened `memcpy` scratch wrapper at residual stack `stk - cliInitiateFrame`. -/
theorem init_memcpyScratch_vm_placed_ok_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {B : RunBudgets} {n stk : Nat}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hn : n ≤ 2 ^ 64 := by decide) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsρ memcpyName)
      (withLsCodeRoLoaded lsmpl
        (withVmPreserved (memcpyScratchSpec n (stk - cliInitiateFrame)))) := by
  have hmc : subroutine_ok (initProgPlaced mmpl gh W) (lsρ memcpyName)
      (withLsCodeRoLoaded lsmpl
        (withStack sessionMemcpyRegionBudgetSpec extHookStack)) :=
    transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W)
      (hh.alloc.session_memcpy_region extHookStack (by decide) (by decide))
  have hle : extHookStack ≤ stk - cliInitiateFrame := by
    have h1 := stk_sub_ge_base hstk
    have hext : extHookStack ≤ 65536 := by decide
    omega
  have hhi : stk - cliInitiateFrame ≤ 2 ^ 64 := by omega
  apply subroutine_ok.of_codeLoaded
  rintro ⟨dst, src⟩ R s0 hpc hrun hpre hsp _
  obtain ⟨hinv, hpre⟩ := extract_withLsCodeRoLoaded hpre
  simp only [withVmPreserved, memcpyScratchSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2⟩, hmem⟩
  rw [ProofLib.memRegion_eq_exists_bytes src n hn] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem
  rcases hmem with ⟨bs, hmem⟩
  rw [show memRegion dst n ∗ ((⌜bs.length = n⌝ ∗ (src ↦ₛ bs)) ∗
        stackAt s0.sp (stk - cliInitiateFrame) ∗ R) =
      ⌜bs.length = n⌝ ∗
        (memRegion dst n ∗ (src ↦ₛ bs) ∗ stackAt s0.sp (stk - cliInitiateFrame) ∗ R) by sep_ac_rfl,
      satisfies_pure_sepConj] at hmem
  rcases hmem with ⟨hlen, hmem⟩
  subst hlen
  rw [stackAt_sub_split_local s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 (stk - cliInitiateFrame))
    ((stk - cliInitiateFrame) - extHookStack)
  have hpre0 : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl
        (withStack sessionMemcpyRegionBudgetSpec extHookStack)).pre
        (dst, src, bs) s0 ∗ (stkRem ∗ R) := by
    refine satisfies_withLsCodeRoLoaded_pre hinv ?_
    simp only [withStack, sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    dsimp only [stkRem]
    convert hmem using 1; sep_ac_rfl
  refine subroutine_ok.mono_outcome hmc (dst, src, bs) (stkRem ∗ R) s0 hpc hrun hpre0 hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    change sf.mem ⊨
      (withVmPreserved (memcpyScratchSpec bs.length (stk - cliInitiateFrame))).post (dst, src) s0 sf ∗ R
    simp only [withStack, sessionMemcpyRegionBudgetSpec,
      sessionMemcpyRegionSpec, withVmPreserved, memcpyScratchSpec, sepConj_assoc,
      satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨hvm, ⟨_hx0f, htr⟩, hq⟩
    refine ⟨hvm, htr, ?_⟩
    have h1 := pointsToBytes_entails_memRegion dst bs
    have h2 := pointsToBytes_entails_memRegion src bs
    rw [stackAt_sub_split_local s0.sp hle hhi]
    dsimp only [stkRem] at hq
    refine Satisfies.mono ?_ hq
    refine Entails.trans (sepConj_mono h1 (sepConj_mono h2 (Entails.refl _))) ?_
    sep_frame
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

theorem init_memcpyScratch_placed_ok_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {B : RunBudgets} {n stk : Nat}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hn : n ≤ 2 ^ 64 := by decide) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsρ memcpyName)
      (withLsCodeRoLoaded lsmpl
        (memcpyScratchSpec n (stk - cliInitiateFrame))) := by
  refine subroutine_ok_mono
    (init_memcpyScratch_vm_placed_ok_at (B := B) (n := n) hh hstk hstk64 hn)
    (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [withLsCodeRoLoaded, withVmPreserved] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq
  exact hq.2

/-! ## Shared error epilogue (`0x0350 → ret`) -/

private theorem sepWP_of_vm {prog : Program} {mid : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP prog mid s P (fun sm Pm => VmPreserved s sm ∧ (VmPreserved s sm → post sm Pm))) :
    SepWP prog mid s P post oom :=
  SepWP.mono h (fun _ _ _ _ ⟨hvmp, hpost⟩ => hpost hvmp)

private theorem sepWP_done_tpidr {prog : Program} {target_pc : BitVec 64} {s0 s : State}
    {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = target_pc) (hrun : s.status = .Running)
    (htp : s.tpidrEl0 = s0.tpidrEl0) (hpost : Q s P) :
    SepWP prog target_pc s P (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ Q sm Pm) :=
  SepWP.done hpc hrun ⟨htp, hpost⟩

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre sp_writeVReg128_pre
  fs_setPC_pre fs_setMem_pre fs_setPState_pre
  fs_writeReg64_pre fs_writeReg32_pre fs_writeReg_pre
  fs_writeVReg128_pre
  trace_writeVReg128_pre trace_writeReg32_pre
  trace_writeReg_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg64_writeVReg128_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg32_writeVReg128_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
  readReg_writeVReg128_pre
  readVReg128_setPC_pre readVReg128_setMem_setPC_pre
  readVReg128_setMem_pre readVReg128_setPState_pre
  readVReg128_writeReg64_pre readVReg128_writeReg32_pre
  readVReg128_writeReg_pre
  extractLsb_append_lo extractLsb_append_hi
  extractLsb_pack32_0 extractLsb_pack32_8
  extractLsb_pack32_16 extractLsb_pack32_24
  extractLsb_pack32_0_16 extractLsb_pack32_16_16

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 200000 in
/-- Budget-threaded Stage 1 error epilogue (`0x0350 → ret`), writing the `SpeOwned` error words to `x.ret`, restoring callee-saved registers and `SP`, and transporting `A.pool` via `VmPreserved`. -/
theorem stage1_epilogue_err_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 : M.σ} {evs : List AllocEvent}
    {stk : Nat} {s0 s : State}
    {H_err H_extra : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hEnv : InitEnv x evs)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hctrl : InInitiatePlaced s0 s 0x0350)
    (htr : s.trace = s0.trace)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hans : S.initiate x.F x.peer.val x.me.val x.bundle x.coins = some none)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (hres :
      (x.ret ↦₆₄ s.readReg64 (.gpr 26#5)) ∗
        ((x.ret + 8#64) ↦₆₄ s.readReg64 (.gpr 27#5)) ∗
        ((x.ret + 16#64) ↦₆₄ s.readReg64 (.gpr 25#5)) ∗
        ((x.ret + 24#64) ↦₆₄ s.readReg64 (.gpr 28#5)) ∗
        ((x.ret + 32#64) ↦₆₄ s.readReg64 (.gpr 24#5)) ∗
        ((x.ret + 40#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗ H_err ⊢
        initResAt A.repAlloc x.ret stage1Err) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      (storesAt A.repAlloc x.stores StoresGhost.opened ∗
        protocolAddressAt A.repAlloc x.peer x.peerA ∗
        protocolAddressAt A.repAlloc x.me x.meA ∗
        cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        (s0.sp ↦₃₂ 0#32) ∗ lsLogOff ∗
        A.pool lim (M.stepEvents evs st0) s ∗
        memRegion x.ret 48 ∗
        initSaved s0 ∗
        memRegion fsp initLocalsSize ∗
        stackAt fsp (stk - cliInitiateFrame) ∗
        H_err ∗ H_extra)
      Q Qp oom := by
  intro fsp
  have hpc : s.pc = (blkPl_521).base + 848#64 := hctrl.pc
  have hrun : s.status = .Running := hctrl.run
  have hsp_mask : ((s.sp &&& 15#64) == 0#64) = true :=
    spAligned_mask_of_frame hctrl.sp hctrl.spAligned
  have hsp_mask4096 : (((s.sp + 4096#64) &&& 15#64) == 0#64) = true :=
    spAligned_mask_add_4096 hsp_mask
  have hsp_mask7312 : (((s.sp + 7312#64) &&& 15#64) == 0#64) = true :=
    spAligned_mask_add_7312 hsp_mask
  have hx19 : s.readReg64 (.gpr 19#5) = x.ret := hctrl.x19.trans hx8
  apply sepWPp_of_sepWP_exit
  dsimp only [fsp]
  rw [memRegion_48_eq_words6 x.ret, initSaved_eq_fsp hctrl.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro u5
  apply SepWP.exists_left; intro u4
  apply SepWP.exists_left; intro u3
  apply SepWP.exists_left; intro u2
  apply SepWP.exists_left; intro u1
  apply SepWP.exists_left; intro u0
  dsimp only [initProgPlaced, lsProg_521]
  apply sepWP_of_vm
  by_vm_steps (
    wp_steps
    have hsp_raw : s.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame := hctrl.sp
    have hsp : s.sp = s0.sp - 7408#64 := hctrl.sp
    apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hvm
    apply hpost
    refine ⟨?_, ?_, ?_⟩
    · simp only [arm64_norm, hsp]
    · apply calleeSavedPreserved_of_regs
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [calleeSavedVRegs, arm64_norm]
        exact hctrl.vregs
    · dsimp only [initSlotSpecPlaced]
      refine Entails.sepExists_right evs ?_
      refine Entails.sepExists_right StoresGhost.opened ?_
      refine Entails.sepExists_right stage1Err ?_
      refine Entails.pure_right ⟨hEnv, slotTrace_of_eq
        (by simp only [arm64_norm, htr])
        (by simp only [arm64_norm]; exact hctrl.files0), by
          simp [slotOut, hans, stage1Err]⟩ ?_
      have hstkMerge :
          initSaved s0 ∗
            memRegion (s0.sp - BitVec.ofNat 64 cliInitiateFrame) initLocalsSize ∗
            stackAt (s0.sp - BitVec.ofNat 64 cliInitiateFrame) (stk - cliInitiateFrame) ⊢
            stackAt s0.sp stk := by
        rw [stackAt_entry_split s0 (stk_ge_frame hstk) hstk64]
        refine Entails.trans (sepConj_mono_left (initSaved_entails_memRegion s0)) ?_
        sep_frame
      have hHeap : H_extra ⊢ anyHeap := entails_anyHeap H_extra
      have foc : ∀ {Full Sub Target F Goal : SepProp},
          (Full ⊢ Sub ∗ F) → (Sub ⊢ Target) → (Target ∗ F ⊢ Goal) → (Full ⊢ Goal) :=
        fun hfoc h hrest => Entails.trans hfoc (Entails.trans (sepConj_mono_left h) hrest)
      refine foc (by sep_frame) (Entails.of_eq (initSaved_eq_fsp hsp_raw).symm) ?_
      refine foc (by sep_frame) hres ?_
      refine foc (by sep_frame) hstkMerge ?_
      refine foc (by sep_frame) hHeap ?_
      rw [A.pool_of_vmPreserved hvm]
      sep_frame)

end

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.CalleesPlacedBudget
