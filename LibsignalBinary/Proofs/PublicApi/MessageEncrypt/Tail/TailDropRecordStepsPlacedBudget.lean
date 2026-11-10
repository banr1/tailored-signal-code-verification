/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PlacedDefsBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.CommonPlacedBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.ProtocolErrCommonPlacedBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailDropRecordStepsPlaced
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailFreePrevSessionsPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailDropRecordSteps
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailFreePrevSessions
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# Budget-Threaded Relocatable `T1` Drop-Record Steppers and `+0x55c` / `+0x54c` Bridges

Budget-threaded basic-block steppers (`+0x46c..+0x564`) across the `pqr_state` buffer deallocation
and `drop_glue<SessionStructure> [local#2]` (`FreeOnlyEvs`), together with `SegExitPlaced` bridges at
`+0x55c` and `+0x54c` on Block `198` (`lsProg_198 Hk`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailDropRecordStepsPlacedBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved
   rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget (SpqrSendBudgetEnv)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
  (dropSessionStructureLocal2Spec)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PlacedDefsBudget
  (EncEnvPlaced SegExitPlaced)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.CommonPlacedBudget
  (EncTailVPlaced encCommonPlaced_vmPreserved encTail_mem_retag_eq)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.ProtocolErrCommonPlacedBudget
  (seamBudget_step_freeOnly)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailFreePrevSessionsPlacedBudget
  (tailFreePrevSessions_placed_ok_of_dealloc)
open CryptoGames.LibsignalSession (Crypto SessionState)
open CryptoGames.LibsignalSessionApi (ApiError SessionRecord StoreAnswers)
open CryptoVerification
  (LibsignalHooks LibsignalPlacement lsRustDeallocSym ls_hook_ok_of_mem lsmpl lsρ)
open CryptoVerification.RustHeap (allocHookStack vecAt)
open CryptoVerification.LibsignalSessionRepr (leBytes)
open CryptoVerification.LibsignalTripleRatchetRepr
  (SessionGhost UuidParser noneCap protocolAddressAt sessionStateAt tapeAfter)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
  (dropSessionStructureLocal2Stack lsLogOff)
open CryptoVerification.LibsignalPublicApiRepr
  (AddrVal KyberRel PendingRel RecordGhost sessionRecordAt sessionStateReprAt)
open CryptoVerification.LibsignalPublicApi.Placed (lsProg_198)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (IdentityStoreSpec LibsignalCodeRoLoaded SessionStoreSpec withLsRoCl)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
  (WithStoresEncGhost cmScratch curScratch encCommonPlaced encEntryPlaced encSavedRegs encSpillsAtV
   encStoreExtraPlaced encSubStack nowAt)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon
  (SpeStaged TailModel pollWith tailRegs)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailFreePrevSessions
  (stackAt_encSubStack_alloc)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps
  (cap_add_one_beq_zero_eq_false cap_add_one_ne_zero cur_none_weaken flag_memRegion_weaken
   scratch_has_50 sessionStateAfterLocalIk sessionStateAt_unfold_cap stackAt_encSubStack_dropSs)

set_option maxRecDepth 200000

private theorem bv_sub_add_lit_local (x a b : BitVec 64) : x - a + b = x - (a - b) := by
  bv_omega

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit_local BitVec.toNat_zero

private theorem protocolAddressAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) :
    protocolAddressAt (A.atState lim st s) = protocolAddressAt A.repAlloc := rfl

private theorem sepWP_of_step_pre_and_call {α : Type} {prog : Program}
    {mid ret_pc : BitVec 64} {spec : Spec α}
    {s : State} {P_pre P_rest F_call : SepProp}
    {post_pre : State → SepProp → Prop}
    {post : State → SepProp → Prop}
    (hwp_pre : SepWP prog mid s P_pre post_pre)
    (hcall : subroutine_ok prog mid spec)
    (hstep_call : ∀ (s_pre : State) (P_mid R : SepProp),
      Steps prog s s_pre →
      s_pre.pc = mid → s_pre.status = .Running →
      (s_pre.mem ⊨ P_mid ∗ (P_rest ∗ R)) →
      post_pre s_pre P_mid →
      ∃ xc : α,
        s_pre.spAligned = true ∧
        s_pre.readReg64 Reg.lr = ret_pc ∧
        (s_pre.mem ⊨ (spec.pre xc s_pre ∗ F_call) ∗ R) ∧
        (∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit xc code s_pre sf ∗ R') → False) ∧
        (∀ sf R', sf.status = .Panicked → (sf.mem ⊨ (spec.onPanic xc s_pre sf ∗ F_call) ∗ R') → False) ∧
        (∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom xc s_pre sf ∗ R') → False) ∧
        (∀ sf : State, Steps prog s_pre sf → sf.pc = ret_pc → sf.status = .Running →
          sf.sp = s_pre.sp → CalleeSavedPreserved s_pre sf →
          (sf.mem ⊨ (spec.post xc s_pre sf ∗ F_call) ∗ R) →
          ∃ P_f : SepProp, (sf.mem ⊨ P_f ∗ R) ∧ post sf P_f)) :
    SepWP prog ret_pc s (P_pre ∗ P_rest) post := by
  unfold SepWP
  intro R hm hL
  rw [sepConj_assoc] at hm
  obtain ⟨s_pre, hsteps_pre, ⟨hpc_pre, hrun_pre, P_mid, hm_pre, hpost_pre⟩ | ⟨_, hoom0⟩⟩ :=
    hwp_pre.elim hm hL
  rotate_left
  · exact (not_satisfies_false_sepConj hoom0).elim
  obtain ⟨xc, hsp_al, hlr, hm_call, hexit, hpanic, hoom, hdone⟩ :=
    hstep_call s_pre P_mid R hsteps_pre hpc_pre hrun_pre hm_pre hpost_pre
  have hwpp : SepWPp prog ret_pc s_pre (spec.pre xc s_pre ∗ F_call)
      (fun sm Pm => sm.sp = s_pre.sp ∧ CalleeSavedPreserved s_pre sm ∧ Pm = spec.post xc s_pre sm ∗ F_call)
      (fun sf Pf => Pf = spec.onPanic xc s_pre sf ∗ F_call) :=
    SepWPp.call (x := xc) (F := F_call) hcall hpc_pre hrun_pre hsp_al hlr
      (fun _ h => by rwa [sepConj_assoc] at h) hexit (fun _ _ => rfl)
      (fun _ hpcm hrunm hspm hcsm => SepWPp.done hpcm hrunm ⟨hspm, hcsm, rfl⟩)
      (fun sf R' hst hmem => False.elim (hoom sf (F_call ∗ R') hst hmem))
  obtain ⟨sf, hsteps_call, ⟨hpcm, hrunm, _, hpost, hspm, hcsm, rfl⟩ | ⟨hpan, _, hpost, rfl⟩ | ⟨_, hoom_f⟩⟩ :=
    hwpp R hm_call (hsteps_pre.codeLoaded hL)
  · exact ⟨sf, hsteps_pre.trans hsteps_call,
      Or.inl ⟨hpcm, hrunm, hdone sf hsteps_call hpcm hrunm hspm hcsm hpost⟩⟩
  · exact False.elim (hpanic sf R hpan hpost)
  · exact (not_satisfies_false_sepConj hoom_f).elim

/-! ## Drop-Record Basic-Block Steppers (`+0x46c..+0x564`) -/

theorem dropRecordDropSs_placed_step_pre [LibsignalPlacement]
    {Hk : LibsignalHooks}
    {s : State} {sp : BitVec 64}
    (hpc : s.pc = encEntryPlaced + 0x55c#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp) :
    SepWP (lsProg_198 Hk) (lsmpl.base 139) s
      ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))
      (fun sf P_f =>
        VmPreserved s sf ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = sp + 0x128#64 ∧
        sf.readReg64 .x30 = encEntryPlaced + 0x564#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))) := by
  subst hsp
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp_al
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_198, ite_true]
  by_vm_steps (
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    exact ⟨by simp only [wp_norm, arm64_norm], rfl, hsp_al, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

theorem dropRecordDropSs_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Hk : LibsignalHooks}
    {s : State} {sp : BitVec 64} {G : SessionGhost} {st : SessionState (List (BitVec 8))}
    {st_m : M.σ}
    (hdrop : subroutine_ok (lsProg_198 Hk) (lsmpl.base 139)
      (withLsRoCl lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hpc : s.pc = encEntryPlaced + 0x55c#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWP (lsProg_198 Hk) (encEntryPlaced + 0x564#64) s
      (((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗ sessionStateAt A.repAlloc (sp + 0x128#64) G st ∗
        A.pool lim st_m s ∗ stackAt sp dropSessionStructureLocal2Stack)
      (fun sf P_f =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          LibsignalCodeRoLoaded lsmpl sf.mem ∧
          sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
          sf.readReg64 .x19 = s.readReg64 .x19 ∧
          sf.readReg64 .x21 = s.readReg64 .x21 ∧
          sf.readReg64 .x23 = s.readReg64 .x23 ∧
          sf.readReg64 .x25 = s.readReg64 .x25 ∧
          sf.readReg64 .x26 = s.readReg64 .x26 ∧
          sf.readReg64 .x27 = s.readReg64 .x27 ∧
          sf.readReg64 .x28 = s.readReg64 .x28 ∧
          sf.readReg64 .x29 = s.readReg64 .x29 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s ∧
          P_f = (((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x128#64) 0x158 ∗
            A.pool lim (M.stepEvents evs st_m) sf ∗ stackAt sp dropSessionStructureLocal2Stack)) := by
  have hwp_pre := dropRecordDropSs_placed_step_pre (Hk := Hk) hpc hrun hsp_al hsp
  refine sepWP_of_step_pre_and_call
    (F_call := (sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) hwp_pre hdrop ?_
  intro s_pre P_mid R hsteps_pre _hpc_pre _hrun_pre hm_pre
    ⟨hvm_pre, hsp_pre, hsp_pre_al, htr_pre, hx0_pre, hlr_pre,
      hx19_pre, hx21_pre, hx23_pre, hx25_pre, hx26_pre, hx27_pre, hx28_pre, hx29_pre, hvregs_pre, hP_mid⟩
  subst hP_mid
  have hcrl_pre : LibsignalCodeRoLoaded lsmpl s_pre.mem :=
    hcrl.of_keepsFrozen hsteps_pre.keepsFrozen
  rw [← A.pool_transport lim st_m s s_pre hvm_pre] at hm_pre
  refine ⟨(⟨sp + 0x128#64, G, st⟩, st_m), hsp_pre_al, hlr_pre, ?_,
    (fun _ _ _ _ h => not_satisfies_false_sepConj h),
    (fun _ _ _ h => not_satisfies_false_sepConj (by
      dsimp only [withLsRoCl, dropSessionStructureLocal2Spec] at h
      rwa [sepConj_assoc] at h)),
    (fun _ _ _ h => not_satisfies_false_sepConj h),
    ?_⟩
  · have hlr_ls : LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (s_pre.readReg64 .lr) := by
      rw [show s_pre.readReg64 .lr = _ from hlr_pre]
      simp (config := { decide := true }) only [arm64_norm, wp_norm]
    have heq_pre :
        (((withLsRoCl lsmpl (dropSessionStructureLocal2Spec M A lim)).pre
            (⟨sp + 0x128#64, G, st⟩, st_m) s_pre ∗
          ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))) ∗ R) =
        (⌜s_pre.readReg64 .x0 = sp + 0x128#64 ∧
            LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (s_pre.readReg64 .lr)⌝ ∗
          (⌜LibsignalCodeRoLoaded lsmpl s_pre.mem⌝ ∗
            (((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗
              ((sessionStateAt A.repAlloc (sp + 0x128#64) G st ∗
                A.pool lim st_m s_pre ∗ stackAt sp dropSessionStructureLocal2Stack) ∗ R)))) := by
      dsimp only [withLsRoCl, dropSessionStructureLocal2Spec]
      rw [hsp_pre]
      sep_ac_rfl
    rw [heq_pre, satisfies_pure_sepConj, satisfies_pure_sepConj]
    exact ⟨⟨hx0_pre, hlr_ls⟩, hcrl_pre, hm_pre⟩
  · intro sf _hsteps_call _hpcm _hrunm hspm hcsm hpost
    have hsp_sf : sf.sp = sp := hspm.trans hsp_pre
    have hsp_al_sf : sf.spAligned = true := by
      unfold State.spAligned at hsp_pre_al ⊢
      rw [hspm]
      exact hsp_pre_al
    obtain ⟨hx19_c, _, hx21_c, _, hx23_c, _, hx25_c, hx26_c, hx27_c, hx28_c, hx29_c, hvregs_c⟩ := hcsm
    dsimp only [withLsRoCl, dropSessionStructureLocal2Spec] at hpost
    rw [hsp_pre, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨hcrl_sf, hpost⟩ := hpost
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    obtain ⟨evs, hpost⟩ := hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨⟨htr_call, hfree⟩, hpost⟩ := hpost
    have heq_post :
        ((memRegion (sp + 0x128#64) 344 ∗
          A.pool lim (M.stepEvents evs st_m) sf ∗ stackAt sp dropSessionStructureLocal2Stack) ∗
          (((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗ R)) =
        ((((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x128#64) 0x158 ∗
          A.pool lim (M.stepEvents evs st_m) sf ∗ stackAt sp dropSessionStructureLocal2Stack) ∗ R) := by
      change ((memRegion (sp + 0x128#64) 0x158 ∗
        A.pool lim (M.stepEvents evs st_m) sf ∗ stackAt sp dropSessionStructureLocal2Stack) ∗
        (((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗ R)) = _
      sep_ac_rfl
    rw [heq_post] at hpost
    exact ⟨_, hpost, evs, hfree, hcrl_sf, hsp_sf, hsp_al_sf, htr_call.trans htr_pre,
      hx19_c.trans hx19_pre, hx21_c.trans hx21_pre, hx23_c.trans hx23_pre,
      hx25_c.trans hx25_pre, hx26_c.trans hx26_pre, hx27_c.trans hx27_pre,
      hx28_c.trans hx28_pre, hx29_c.trans hx29_pre, hvregs_c.trans hvregs_pre, rfl⟩

theorem dropRecordCur_none_placed_sepWP [LibsignalPlacement]
    {Hk : LibsignalHooks}
    {s : State} {sp : BitVec 64} {b469 : BitVec 8}
    (hpc : s.pc = encEntryPlaced + 0x54c#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp) :
    SepWP (lsProg_198 Hk) (encEntryPlaced + 0x564#64) s
      (((sp + 0x128#64) ↦₆₄ noneCap) ∗ ((sp + 0x469#64) ↦₈ b469))
      (fun sf P_f =>
        VmPreserved s sf ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧ sf.symtab = s.symtab ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (((sp + 0x128#64) ↦₆₄ noneCap) ∗ ((sp + 0x469#64) ↦₈ 0#8))) := by
  subst hsp
  unfold encEntryPlaced at hpc ⊢
  unfold noneCap
  dsimp only [lsProg_198, ite_true]
  by_vm_steps (
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun)
    exact ⟨by simp only [wp_norm, arm64_norm], rfl, hsp_al, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, by sep_ac_rfl⟩)

theorem dropRecordCur_some_placed_sepWP [LibsignalPlacement]
    {Hk : LibsignalHooks}
    {s : State} {sp cap : BitVec 64} {b469 : BitVec 8}
    (hcap_lt : cap.toNat < 2 ^ 63)
    (hpc : s.pc = encEntryPlaced + 0x54c#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp) :
    SepWP (lsProg_198 Hk) (encEntryPlaced + 0x55c#64) s
      (((sp + 0x128#64) ↦₆₄ cap) ∗ ((sp + 0x469#64) ↦₈ b469))
      (fun sf P_f =>
        VmPreserved s sf ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧ sf.symtab = s.symtab ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (((sp + 0x128#64) ↦₆₄ cap) ∗ ((sp + 0x469#64) ↦₈ 0#8))) := by
  subst hsp
  have hcmn := cap_add_one_beq_zero_eq_false hcap_lt
  have hcmn_ne := cap_add_one_ne_zero hcap_lt
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_198, ite_true]
  by_vm_steps (
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun)
    exact ⟨by simp only [wp_norm, arm64_norm], rfl, hsp_al, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, by sep_ac_rfl⟩)

theorem dropRecordAfterDealloc_none_placed_sepWP [LibsignalPlacement]
    {Hk : LibsignalHooks}
    {s : State} {sp : BitVec 64} {b469 : BitVec 8}
    (hpc : s.pc = encEntryPlaced + 0x488#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp) :
    SepWP (lsProg_198 Hk) (encEntryPlaced + 0x564#64) s
      (((sp + 0x128#64) ↦₆₄ noneCap) ∗ ((sp + 0x469#64) ↦₈ b469))
      (fun sf P_f =>
        VmPreserved s sf ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧ sf.symtab = s.symtab ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (((sp + 0x128#64) ↦₆₄ noneCap) ∗ ((sp + 0x469#64) ↦₈ 0#8))) := by
  subst hsp
  unfold encEntryPlaced at hpc ⊢
  unfold noneCap
  dsimp only [lsProg_198, ite_true]
  by_vm_steps (
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun)
    exact ⟨by simp only [wp_norm, arm64_norm], rfl, hsp_al, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, by sep_ac_rfl⟩)

theorem dropRecordAfterDealloc_some_placed_sepWP [LibsignalPlacement]
    {Hk : LibsignalHooks}
    {s : State} {sp cap : BitVec 64} {b469 : BitVec 8}
    (hcap_lt : cap.toNat < 2 ^ 63)
    (hpc : s.pc = encEntryPlaced + 0x488#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp) :
    SepWP (lsProg_198 Hk) (encEntryPlaced + 0x55c#64) s
      (((sp + 0x128#64) ↦₆₄ cap) ∗ ((sp + 0x469#64) ↦₈ b469))
      (fun sf P_f =>
        VmPreserved s sf ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧ sf.symtab = s.symtab ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (((sp + 0x128#64) ↦₆₄ cap) ∗ ((sp + 0x469#64) ↦₈ 0#8))) := by
  subst hsp
  have hcmn := cap_add_one_beq_zero_eq_false hcap_lt
  have hcmn_ne := cap_add_one_ne_zero hcap_lt
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_198, ite_true]
  by_vm_steps (
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun)
    exact ⟨by simp only [wp_norm, arm64_norm], rfl, hsp_al, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, by sep_ac_rfl⟩)

theorem dropRecord_otr_none_placed_sepWP [LibsignalPlacement]
    {Hk : LibsignalHooks}
    {s : State} {sp : BitVec 64}
    (hpc : s.pc = encEntryPlaced + 0x46c#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp) :
    SepWP (lsProg_198 Hk) (encEntryPlaced + 0x54c#64) s
      ((sp + 0x469#64) ↦₈ 0#8)
      (fun sf P_f =>
        VmPreserved s sf ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧ sf.symtab = s.symtab ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = ((sp + 0x469#64) ↦₈ 0#8)) := by
  subst hsp
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_198, ite_true]
  by_vm_steps (
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun)
    exact ⟨by simp only [wp_norm, arm64_norm], rfl, hsp_al, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

theorem dropRecord_otr_zero_placed_sepWP [LibsignalPlacement]
    {Hk : LibsignalHooks}
    {s : State} {sp : BitVec 64}
    (hpc : s.pc = encEntryPlaced + 0x46c#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp) :
    SepWP (lsProg_198 Hk) (encEntryPlaced + 0x54c#64) s
      (((sp + 0x288#64) ↦₆₄ 0#64) ∗ ((sp + 0x469#64) ↦₈ 1#8))
      (fun sf P_f =>
        VmPreserved s sf ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧ sf.symtab = s.symtab ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (((sp + 0x288#64) ↦₆₄ 0#64) ∗ ((sp + 0x469#64) ↦₈ 1#8))) := by
  subst hsp
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_198, ite_true]
  by_vm_steps (
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun)
    exact ⟨by simp only [wp_norm, arm64_norm], rfl, hsp_al, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, by sep_ac_rfl⟩)

set_option maxHeartbeats 800000 in
theorem dropRecord_otr_nz_placed_step_pre [LibsignalPlacement]
    {Hk : LibsignalHooks}
    {s : State} {sp pqCap pqPtr : BitVec 64}
    (hpq_nz : pqCap ≠ 0#64)
    (hpc : s.pc = encEntryPlaced + 0x46c#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp) :
    SepWP (lsProg_198 Hk) (lsρ lsRustDeallocSym) s
      (((sp + 0x288#64) ↦₆₄ pqCap) ∗ ((sp + 0x290#64) ↦₆₄ pqPtr) ∗ ((sp + 0x469#64) ↦₈ 1#8))
      (fun sf P_f =>
        VmPreserved s sf ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = pqPtr ∧
        (sf.readReg64 .x1).toNat = pqCap.toNat ∧
        (sf.readReg64 .x2).toNat = 1 ∧
        sf.readReg64 .x30 = encEntryPlaced + 0x488#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (((sp + 0x288#64) ↦₆₄ pqCap) ∗ ((sp + 0x290#64) ↦₆₄ pqPtr) ∗
          ((sp + 0x469#64) ↦₈ 1#8))) := by
  subst hsp
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp_al
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_198, ite_true]
  by_vm_steps (
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    exact ⟨by simp only [wp_norm, arm64_norm], rfl, hsp_al, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by sep_ac_rfl⟩)

theorem dropRecord_otr_nz_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Hk : LibsignalHooks}
    {s : State} {sp pqCap pqPtr : BitVec 64} {st_m : M.σ}
    (hdealloc_sat : HookSat Hk lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hpq_nz : pqCap ≠ 0#64)
    (hpc : s.pc = encEntryPlaced + 0x46c#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp) :
    SepWP (lsProg_198 Hk) (encEntryPlaced + 0x488#64) s
      (((sp + 0x288#64) ↦₆₄ pqCap) ∗ ((sp + 0x290#64) ↦₆₄ pqPtr) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
        A.pool lim st_m s ∗ A.live pqPtr pqCap.toNat 1 ∗ memRegion pqPtr pqCap.toNat ∗
        stackAt sp allocHookStack)
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (((sp + 0x288#64) ↦₆₄ pqCap) ∗ ((sp + 0x290#64) ↦₆₄ pqPtr) ∗
          ((sp + 0x469#64) ↦₈ 1#8) ∗
          A.pool lim (M.stepEvents (rustDeallocEvents pqCap.toNat 1) st_m) sf ∗
          stackAt sp allocHookStack)) := by
  let P_pre := ((sp + 0x288#64) ↦₆₄ pqCap) ∗ ((sp + 0x290#64) ↦₆₄ pqPtr) ∗ ((sp + 0x469#64) ↦₈ 1#8)
  let P_rest := A.pool lim st_m s ∗ A.live pqPtr pqCap.toNat 1 ∗
    memRegion pqPtr pqCap.toNat ∗ stackAt sp allocHookStack
  have hpre_split :
      (((sp + 0x288#64) ↦₆₄ pqCap) ∗ ((sp + 0x290#64) ↦₆₄ pqPtr) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
        A.pool lim st_m s ∗ A.live pqPtr pqCap.toNat 1 ∗ memRegion pqPtr pqCap.toNat ∗
        stackAt sp allocHookStack) = (P_pre ∗ P_rest) := by
    dsimp only [P_pre, P_rest]
    sep_ac_rfl
  rw [hpre_split]
  have hwp_pre := dropRecord_otr_nz_placed_step_pre (Hk := Hk) (pqPtr := pqPtr) hpq_nz hpc hrun hsp_al hsp
  have hdealloc : subroutine_ok (lsProg_198 Hk) (lsρ lsRustDeallocSym)
      (rustCliDeallocBudgetSpec M A lim) := by
    unfold lsProg_198
    exact ls_hook_ok_of_mem hdealloc_sat
  refine sepWP_of_step_pre_and_call (F_call := P_pre) hwp_pre hdealloc ?_
  intro s_pre P_mid R _hsteps_pre _hpc_pre _hrun_pre hm_pre
    ⟨hvm_pre, hsp_pre, hsp_pre_al, htr_pre, hx0_pre, hx1_pre, hx2_pre, hlr_pre,
      hx19_pre, hx21_pre, hx23_pre, hx25_pre, hx26_pre, hx27_pre, hx28_pre, hx29_pre, hvregs_pre, hP_mid⟩
  subst hP_mid
  dsimp only [P_rest] at hm_pre
  rw [← A.pool_transport lim st_m s s_pre hvm_pre] at hm_pre
  refine ⟨(pqPtr, pqCap.toNat, 1, st_m), hsp_pre_al, hlr_pre, ?_,
    (fun _ _ _ _ h => not_satisfies_false_sepConj h),
    (fun _ _ _ h => not_satisfies_false_sepConj (by
      dsimp only [rustCliDeallocBudgetSpec] at h
      rwa [sepConj_assoc] at h)),
    (fun _ _ _ h => not_satisfies_false_sepConj h),
    ?_⟩
  · have hlr_ls : LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (s_pre.readReg64 .lr) := by
      rw [show s_pre.readReg64 .lr = _ from hlr_pre]
      simp (config := { decide := true }) only [arm64_norm, wp_norm]
    have heq_pre :
        (((rustCliDeallocBudgetSpec M A lim).pre (pqPtr, pqCap.toNat, 1, st_m) s_pre ∗ P_pre) ∗ R) =
        (⌜s_pre.readReg64 .x0 = pqPtr ∧
            (s_pre.readReg64 .x1).toNat = pqCap.toNat ∧
            (s_pre.readReg64 .x2).toNat = 1 ∧
            LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (s_pre.readReg64 .lr)⌝ ∗
          (P_pre ∗ ((A.pool lim st_m s_pre ∗ A.live pqPtr pqCap.toNat 1 ∗
            memRegion pqPtr pqCap.toNat ∗ stackAt sp allocHookStack) ∗ R))) := by
      dsimp only [rustCliDeallocBudgetSpec, P_pre]
      rw [hsp_pre]
      sep_ac_rfl
    rw [heq_pre, satisfies_pure_sepConj]
    exact ⟨⟨hx0_pre, hx1_pre, hx2_pre, hlr_ls⟩, hm_pre⟩
  · intro sf _hsteps_call _hpcm _hrunm hspm hcsm hpost
    have hsp_sf : sf.sp = sp := hspm.trans hsp_pre
    have hsp_al_sf : sf.spAligned = true := by
      unfold State.spAligned at hsp_pre_al ⊢
      rw [hspm]
      exact hsp_pre_al
    obtain ⟨hx19_c, _, hx21_c, _, hx23_c, _, hx25_c, hx26_c, hx27_c, hx28_c, hx29_c, hvregs_c⟩ := hcsm
    dsimp only [rustCliDeallocBudgetSpec] at hpost
    rw [hsp_pre, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨⟨hacp, _⟩, hpost⟩ := hpost
    have htr_call : sf.trace = s_pre.trace := hacp.2.1
    have heq_post :
        ((A.pool lim (M.stepEvents (rustDeallocEvents pqCap.toNat 1) st_m) sf ∗
          stackAt sp allocHookStack) ∗ (P_pre ∗ R)) =
        ((((sp + 0x288#64) ↦₆₄ pqCap) ∗ ((sp + 0x290#64) ↦₆₄ pqPtr) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
          A.pool lim (M.stepEvents (rustDeallocEvents pqCap.toNat 1) st_m) sf ∗
          stackAt sp allocHookStack) ∗ R) := by
      dsimp only [P_pre]
      sep_ac_rfl
    rw [heq_post] at hpost
    exact ⟨_, hpost, hsp_sf, hsp_al_sf, htr_call.trans htr_pre,
      hx19_c.trans hx19_pre, hx21_c.trans hx21_pre, hx23_c.trans hx23_pre,
      hx25_c.trans hx25_pre, hx26_c.trans hx26_pre, hx27_c.trans hx27_pre,
      hx28_c.trans hx28_pre, hx29_c.trans hx29_pre, hvregs_c.trans hvregs_pre, rfl⟩

/-! ## `+0x55c` and `+0x54c` `SegExitPlaced` Bridges -/

theorem tailDropRecordAt55c_placed_ok_of_dropSs_dealloc [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64} {parse : UuidParser}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {ist0 : ikit.IdState}
    (hdropSs : subroutine_ok (lsProg_198 Hk) (lsmpl.base 139)
      (withLsRoCl lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hdealloc : HookSat Hk lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (x : WithStoresEncGhost) (st_init st : M.σ) (R0 : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp) (scratch : BitVec 64 → SepProp)
    (hscr : scratch = curScratch ∨ scratch = cmScratch)
    (prevCap prevPtr : BitVec 64) (G : SessionGhost) (sess_st : SessionState (List (BitVec 8)))
    (hm : TailModel kit st0 ikit ist0 C S parse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A.repAlloc x.ret e [w0, w1, w2, w3, w4, w5] H)
    (hs : EncTailVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv
      x st_init st answers (encEntryPlaced + 0x55c#64) (tailRegs w0 w1 w2)
      (fun sp => scratch sp ∗
        vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
        sessionStateAt A.repAlloc (sp + 0x128#64) G sess_st ∗
        memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H)
      R0 s0 s) :
    SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord Hk
      x st_init R0 s0 s (fun _ => False) := by
  let R := encStoreExtraPlaced kit (kit.storeFinal st0 answers (x.model C S parse answers).2)
    ikit (ikit.idFinal ist0 answers (x.model C S parse answers).2) x s0 ∗ R0
  rcases hs with ⟨hbud, hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hcrl, hvregs⟩,
    ⟨hx26, hx28, hx27, hx21, hx23⟩, hstack_le, hmem⟩
  have hmem := Eq.mp (congrArg (s.mem ⊨ ·)
    (encTail_mem_retag_eq kit st0 ikit ist0 C ctl parse S x answers _ R0 s0)) hmem
  let sp := s0.sp - 0xbe0#64
  rcases scratch_has_50 hscr sp with ⟨S50, hscr_eq, hscr_weaken⟩
  change s.mem ⊨
    (scratch sp ∗
      vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
      sessionStateAt A.repAlloc (sp + 0x128#64) G sess_st ∗
      memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R at hmem
  rw [hscr_eq] at hmem
  let F := S50 ∗ vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
    memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
    protocolAddressAt A.repAlloc x.loc x.locA ∗
    nowAt s0.sp x.now ∗ tapeAfter ctl x.cur x.rest (x.draws S answers) ∗ lsLogOff ∗
    memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - dropSessionStructureLocal2Stack) ∗
    encSavedRegs s0.sp s0
  have hmem_re : s.mem ⊨
      (((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗ sessionStateAt A.repAlloc (sp + 0x128#64) G sess_st ∗
        A.pool lim st s ∗ stackAt sp dropSessionStructureLocal2Stack) ∗ (F ∗ R) := by
    have heq :
        (((S50 ∗ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))) ∗
          vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          sessionStateAt A.repAlloc (sp + 0x128#64) G sess_st ∗
          memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R) =
        ((((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗ sessionStateAt A.repAlloc (sp + 0x128#64) G sess_st ∗
          A.pool lim st s ∗ stackAt sp dropSessionStructureLocal2Stack) ∗ (F ∗ R)) := by
      unfold encCommonPlaced
      rw [protocolAddressAt_atState]
      change (((S50 ∗ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))) ∗
        vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
        sessionStateAt A.repAlloc (sp + 0x128#64) G sess_st ∗
        memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
       encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
       ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
        protocolAddressAt A.repAlloc x.loc x.locA ∗
        nowAt s0.sp x.now ∗ tapeAfter ctl x.cur x.rest (x.draws S answers) ∗ lsLogOff ∗
        stackAt sp encSubStack ∗ encSavedRegs s0.sp s0 ∗ A.pool lim st s) ∗ R) = _
      rw [stackAt_encSubStack_dropSs sp]
      dsimp only [F]
      sep_ac_rfl
    rwa [← heq]
  have hwp := dropRecordDropSs_placed_sepWP (sp := sp) (G := G) (st := sess_st) (st_m := st)
    hdropSs hpc hrun hsp_al hsp hcrl
  refine SegExitPlaced.of_sepWP (R0 := R0) hmem_re hwp ?_
  intro s1 P_f _ _hsteps1 hpc1 hrun1 hmf1
    ⟨evs, hfree, hcrl1, hsp1, hsp1_al, htr1, hx19_1, hx21_1, hx23_1, _, hx26_1, hx27_1, hx28_1, hx29_1, hvregs1, hPf⟩
  subst hPf
  have hbud1 := seamBudget_step_freeOnly hbud hfree
  set st1 := M.stepEvents evs st
  have hm1 : TailModel kit st0 ikit ist0 C S parse encRecord x answers (.error e) s0 s1 :=
    ⟨hm.1, htr1.trans hm.2⟩
  refine tailFreePrevSessions_placed_ok_of_dealloc hdealloc x st_init st1 R0 s0 s1 answers e
    w0 w1 w2 w3 w4 w5 H prevCap prevPtr hm1 hst ⟨hbud1, ?_⟩
  refine ⟨hpc1, ⟨hrun1, hsp1, hsp0_al, hsp1_al, hx29_1.trans hx29, hx19_1.trans hx19,
    hcrl1, hvregs1.trans hvregs⟩,
    ⟨hx26_1.trans hx26, hx28_1.trans hx28, hx27_1.trans hx27, hx21_1.trans hx21, hx23_1.trans hx23⟩,
    hstack_le, ?_⟩
  refine Eq.mpr (congrArg (s1.mem ⊨ ·)
    (encTail_mem_retag_eq kit st0 ikit ist0 C ctl parse S x answers _ R0 s0)) ?_
  have hmf2 : s1.mem ⊨
      (S50 ∗ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))) ∗
      (vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
       memRegion (sp + 0x128#64) 0x158 ∗
       memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
       encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
       encCommonPlaced (A.atState lim st1 s1) ctl x (x.draws S answers) s0 ∗ R) := by
    have heq :
        ((((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x128#64) 0x158 ∗
          A.pool lim st1 s1 ∗ stackAt sp dropSessionStructureLocal2Stack) ∗ (F ∗ R)) =
        ((S50 ∗ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))) ∗
         (vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          memRegion (sp + 0x128#64) 0x158 ∗
          memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          encCommonPlaced (A.atState lim st1 s1) ctl x (x.draws S answers) s0 ∗ R)) := by
      unfold encCommonPlaced
      rw [protocolAddressAt_atState]
      change _ = ((S50 ∗ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))) ∗
        (vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
         memRegion (sp + 0x128#64) 0x158 ∗
         memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
          protocolAddressAt A.repAlloc x.loc x.locA ∗
          nowAt s0.sp x.now ∗ tapeAfter ctl x.cur x.rest (x.draws S answers) ∗ lsLogOff ∗
          stackAt sp encSubStack ∗ encSavedRegs s0.sp s0 ∗ A.pool lim st1 s1) ∗ R))
      rw [stackAt_encSubStack_dropSs sp]
      dsimp only [F]
      sep_ac_rfl
    rwa [heq] at hmf1
  have hmf3 := Satisfies.mono (sepConj_mono_left hscr_weaken) hmf2
  have heq2 :
      (memRegion sp 0x58 ∗
       (vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
        memRegion (sp + 0x128#64) 0x158 ∗
        memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
        encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
        encCommonPlaced (A.atState lim st1 s1) ctl x (x.draws S answers) s0 ∗ R)) =
      ((memRegion sp 0x58 ∗
        vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
        memRegion (sp + 0x128#64) 0x158 ∗
        memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
       encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
       encCommonPlaced (A.atState lim st1 s1) ctl x (x.draws S answers) s0 ∗ R) := by sep_ac_rfl
  rwa [← heq2]

theorem tailDropRecordAt55c_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {C : Crypto} {ctl : BitVec 64} {parse : UuidParser}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {ist0 : ikit.IdState}
    (env : EncEnvPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl parse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st : M.σ) (R0 : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp) (scratch : BitVec 64 → SepProp)
    (hscr : scratch = curScratch ∨ scratch = cmScratch)
    (prevCap prevPtr : BitVec 64) (G : SessionGhost) (sess_st : SessionState (List (BitVec 8)))
    (hm : TailModel kit st0 ikit ist0 C S parse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A.repAlloc x.ret e [w0, w1, w2, w3, w4, w5] H)
    (hs : EncTailVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv
      x st_init st answers (encEntryPlaced + 0x55c#64) (tailRegs w0 w1 w2)
      (fun sp => scratch sp ∗
        vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
        sessionStateAt A.repAlloc (sp + 0x128#64) G sess_st ∗
        memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H)
      R0 s0 s) :
    SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord Hk
      x st_init R0 s0 s (fun _ => False) :=
  tailDropRecordAt55c_placed_ok_of_dropSs_dealloc env.callees.dropSs env.hooks.dealloc
    x st_init st R0 s0 s answers e w0 w1 w2 w3 w4 w5 H scratch hscr prevCap prevPtr G sess_st hm hst hs

theorem tailDropRecordCur_placed_ok_of_dropSs_dealloc [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64} {parse : UuidParser}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {ist0 : ikit.IdState}
    (hdropSs : subroutine_ok (lsProg_198 Hk) (lsmpl.base 139)
      (withLsRoCl lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hdealloc : HookSat Hk lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (x : WithStoresEncGhost) (st_init st : M.σ) (R0 : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp) (scratch : BitVec 64 → SepProp)
    (hscr : scratch = curScratch ∨ scratch = cmScratch) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8))) (b469 : BitVec 8)
    (hm : TailModel kit st0 ikit ist0 C S parse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A.repAlloc x.ret e [w0, w1, w2, w3, w4, w5] H)
    (hs : EncTailVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv
      x st_init st answers (encEntryPlaced + 0x54c#64) (tailRegs w0 w1 w2)
      (fun sp => scratch sp ∗ sessionRecordAt A.repAlloc (sp + 0x110#64) g rec ∗
        memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
        pollWith sp 0x9d0 [w3, w4, w5] ∗ H)
      R0 s0 s) :
    SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord Hk
      x st_init R0 s0 s (fun _ => False) := by
  let R := encStoreExtraPlaced kit (kit.storeFinal st0 answers (x.model C S parse answers).2)
    ikit (ikit.idFinal ist0 answers (x.model C S parse answers).2) x s0 ∗ R0
  rcases hs with ⟨hbud, hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hcrl, hvregs⟩,
    ⟨hx26, hx28, hx27, hx21, hx23⟩, hstack_le, hmem⟩
  have hmem := Eq.mp (congrArg (s.mem ⊨ ·)
    (encTail_mem_retag_eq kit st0 ikit ist0 C ctl parse S x answers _ R0 s0)) hmem
  let sp := s0.sp - 0xbe0#64
  change s.mem ⊨
    (scratch sp ∗ sessionRecordAt A.repAlloc (sp + 0x110#64) g rec ∗
      memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
      pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R at hmem
  unfold sessionRecordAt at hmem
  have h128 : sp + 0x110#64 + 0x18#64 = sp + 0x128#64 := by bv_omega
  have h130 : sp + 0x110#64 + 0x20#64 = sp + 0x130#64 := by bv_omega
  rcases g with ⟨prevCap, prevPtr, _ | G⟩ <;> rcases hcur : rec.currentSession with _ | sess
  · rw [hcur, h128, h130] at hmem
    rcases scratch_has_50 hscr sp with ⟨S50, hscr_eq, hscr_weaken⟩
    have hscr_mem : scratch sp ⊢ memRegion sp 0x58 := hscr_eq ▸ hscr_weaken
    let F := scratch sp ∗ vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
      memRegion (sp + 0x130#64) 336 ∗ memRegion (sp + 0x280#64) 0x1e9 ∗
      pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
      encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
      encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0
    have hmem_re : s.mem ⊨ (((sp + 0x128#64) ↦₆₄ noneCap) ∗ ((sp + 0x469#64) ↦₈ b469)) ∗ (F ∗ R) := by
      have heq :
          ((scratch sp ∗
            (vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
              (((sp + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x130#64) 336)) ∗
            memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
            pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R) =
          ((((sp + 0x128#64) ↦₆₄ noneCap) ∗ ((sp + 0x469#64) ↦₈ b469)) ∗ (F ∗ R)) := by
        dsimp only [F]; sep_ac_rfl
      rwa [← heq]
    have hwp := dropRecordCur_none_placed_sepWP (Hk := Hk) (b469 := b469) hpc hrun hsp_al hsp
    refine SegExitPlaced.of_sepWP (R0 := R0) hmem_re hwp ?_
    intro s1 P_f _ hsteps1 hpc1 hrun1 hmf1
      ⟨hvm1, hsp1, hsp1_al, htr1, _hsym1, hx19_1, hx21_1, hx23_1, _, hx26_1, hx27_1, hx28_1, hx29_1, hvregs1, hPf⟩
    subst hPf
    have hm1 : TailModel kit st0 ikit ist0 C S parse encRecord x answers (.error e) s0 s1 :=
      ⟨hm.1, htr1.trans hm.2⟩
    refine tailFreePrevSessions_placed_ok_of_dealloc hdealloc x st_init st R0 s0 s1 answers e
      w0 w1 w2 w3 w4 w5 H prevCap prevPtr hm1 hst ⟨hbud, ?_⟩
    refine ⟨hpc1, ⟨hrun1, hsp1, hsp0_al, hsp1_al, hx29_1.trans hx29, hx19_1.trans hx19,
      hcrl.of_keepsFrozen hsteps1.keepsFrozen, hvregs1.trans hvregs⟩,
      ⟨hx26_1.trans hx26, hx28_1.trans hx28, hx27_1.trans hx27, hx21_1.trans hx21, hx23_1.trans hx23⟩,
      hstack_le, ?_⟩
    refine Eq.mpr (congrArg (s1.mem ⊨ ·)
      (encTail_mem_retag_eq kit st0 ikit ist0 C ctl parse S x answers _ R0 s0)) ?_
    have hmf2 : s1.mem ⊨
        (scratch sp ∗
          (((sp + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x130#64) 336) ∗
          (memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ 0#8))) ∗
        (vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          encCommonPlaced (A.atState lim st s1) ctl x (x.draws S answers) s0 ∗ R) := by
      have heq :
          ((((sp + 0x128#64) ↦₆₄ noneCap) ∗ ((sp + 0x469#64) ↦₈ 0#8)) ∗ (F ∗ R)) =
          ((scratch sp ∗
            (((sp + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x130#64) 336) ∗
            (memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ 0#8))) ∗
           (vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
             pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             encCommonPlaced (A.atState lim st s1) ctl x (x.draws S answers) s0 ∗ R)) := by
        dsimp only [F]
        rw [encCommonPlaced_vmPreserved A lim st ctl x (x.draws S answers) s0 s s1 hvm1]
        sep_ac_rfl
      rwa [← heq]
    have hmf3 := Satisfies.mono
      (sepConj_mono_left (sepConj_mono hscr_mem
        (sepConj_mono (cur_none_weaken sp) (flag_memRegion_weaken sp 0#8)))) hmf2
    have heq2 :
        ((memRegion sp 0x58 ∗ memRegion (sp + 0x128#64) 0x158 ∗ memRegion (sp + 0x280#64) 0x1ea) ∗
         (vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
           pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           encCommonPlaced (A.atState lim st s1) ctl x (x.draws S answers) s0 ∗ R)) =
        ((memRegion sp 0x58 ∗
          vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          memRegion (sp + 0x128#64) 0x158 ∗
          memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         encCommonPlaced (A.atState lim st s1) ctl x (x.draws S answers) s0 ∗ R) := by sep_ac_rfl
    rwa [← heq2]
  · rw [hcur] at hmem
    have hfalse : s.mem ⊨ ⌜False⌝ ∗
        (scratch sp ∗ vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
          pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R) := by
      have heq :
          ((scratch sp ∗
            (vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗ ⌜False⌝) ∗
            memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
            pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R) =
          (⌜False⌝ ∗
           (scratch sp ∗ vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
             memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
             pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R)) := by sep_ac_rfl
      rwa [← heq]
    rw [satisfies_pure_sepConj] at hfalse
    exact hfalse.1.elim
  · rw [hcur] at hmem
    have hfalse : s.mem ⊨ ⌜False⌝ ∗
        (scratch sp ∗ vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
          pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R) := by
      have heq :
          ((scratch sp ∗
            (vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗ ⌜False⌝) ∗
            memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
            pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R) =
          (⌜False⌝ ∗
           (scratch sp ∗ vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
             memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
             pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R)) := by sep_ac_rfl
      rwa [← heq]
    rw [satisfies_pure_sepConj] at hfalse
    exact hfalse.1.elim
  · rw [hcur] at hmem
    dsimp only at hmem
    unfold sessionStateReprAt at hmem
    rw [h128, sessionStateAt_unfold_cap A.repAlloc (sp + 0x128#64) G sess.state] at hmem
    let P_sess_pure : Prop :=
      PendingRel G.pending sess.pendingPreKey ∧ KyberRel G.kyber sess.pendingKyberPreKey ∧
        G.alice.bytes = sess.aliceBaseKey ∧
        G.regIds.take 4 = leBytes 4 sess.remoteRegistrationId.toNat ∧
        (G.regIds.drop 4).take 4 = leBytes 4 sess.localRegistrationId.toNat
    let P_ik_pure : Prop :=
      G.localIk.bytes.length ≤ G.localIk.cap.toNat ∧ G.localIk.cap.toNat < 2 ^ 63 ∧ G.localIk.ptr ≠ 0
    let F := scratch sp ∗ vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
      sessionStateAfterLocalIk A.repAlloc (sp + 0x128#64) G sess.state ∗
      memRegion (sp + 0x280#64) 0x1e9 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
      encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
      encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0
    have hmem_re : s.mem ⊨ ⌜P_sess_pure⌝ ∗ (⌜P_ik_pure⌝ ∗
        ((((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗ ((sp + 0x469#64) ↦₈ b469)) ∗ (F ∗ R))) := by
      have heq :
          ((scratch sp ∗
            (vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
              (⌜P_sess_pure⌝ ∗
                (⌜P_ik_pure⌝ ∗
                  (((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗
                    sessionStateAfterLocalIk A.repAlloc (sp + 0x128#64) G sess.state)))) ∗
            memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
            pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R) =
          (⌜P_sess_pure⌝ ∗ (⌜P_ik_pure⌝ ∗
            ((((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗ ((sp + 0x469#64) ↦₈ b469)) ∗ (F ∗ R)))) := by
        dsimp only [P_sess_pure, P_ik_pure, F]; sep_ac_rfl
      rwa [← heq]
    rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hmem_re
    rcases hmem_re with ⟨_, h_ik, hmem2⟩
    have hcap_lt : G.localIk.cap.toNat < 2 ^ 63 := h_ik.2.1
    have hwp := dropRecordCur_some_placed_sepWP (Hk := Hk) (b469 := b469) hcap_lt hpc hrun hsp_al hsp
    refine SegExitPlaced.of_sepWP (R0 := R0) hmem2 hwp ?_
    intro s1 P_f _ hsteps1 hpc1 hrun1 hmf1
      ⟨hvm1, hsp1, hsp1_al, htr1, _hsym1, hx19_1, hx21_1, hx23_1, _, hx26_1, hx27_1, hx28_1, hx29_1, hvregs1, hPf⟩
    subst hPf
    have hm1 : TailModel kit st0 ikit ist0 C S parse encRecord x answers (.error e) s0 s1 :=
      ⟨hm.1, htr1.trans hm.2⟩
    refine tailDropRecordAt55c_placed_ok_of_dropSs_dealloc hdropSs hdealloc x st_init st R0 s0 s1
      answers e w0 w1 w2 w3 w4 w5 H scratch hscr prevCap prevPtr G sess.state hm1 hst ⟨hbud, ?_⟩
    refine ⟨hpc1, ⟨hrun1, hsp1, hsp0_al, hsp1_al, hx29_1.trans hx29, hx19_1.trans hx19,
      hcrl.of_keepsFrozen hsteps1.keepsFrozen, hvregs1.trans hvregs⟩,
      ⟨hx26_1.trans hx26, hx28_1.trans hx28, hx27_1.trans hx27, hx21_1.trans hx21, hx23_1.trans hx23⟩,
      hstack_le, ?_⟩
    refine Eq.mpr (congrArg (s1.mem ⊨ ·)
      (encTail_mem_retag_eq kit st0 ikit ist0 C ctl parse S x answers _ R0 s0)) ?_
    have hmf1' : s1.mem ⊨ ⌜P_ik_pure⌝ ∗
        ((((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗ ((sp + 0x469#64) ↦₈ 0#8)) ∗ (F ∗ R)) := by
      rw [satisfies_pure_sepConj]
      exact ⟨h_ik, hmf1⟩
    have hmf2 : s1.mem ⊨
        (memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ 0#8)) ∗
        (scratch sp ∗ vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          sessionStateAt A.repAlloc (sp + 0x128#64) G sess.state ∗
          pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          encCommonPlaced (A.atState lim st s1) ctl x (x.draws S answers) s0 ∗ R) := by
      have heq :
          (⌜P_ik_pure⌝ ∗
            ((((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗ ((sp + 0x469#64) ↦₈ 0#8)) ∗ (F ∗ R))) =
          ((memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ 0#8)) ∗
           (scratch sp ∗ vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
             sessionStateAt A.repAlloc (sp + 0x128#64) G sess.state ∗
             pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             encCommonPlaced (A.atState lim st s1) ctl x (x.draws S answers) s0 ∗ R)) := by
        dsimp only [F, P_ik_pure]
        rw [encCommonPlaced_vmPreserved A lim st ctl x (x.draws S answers) s0 s s1 hvm1,
            sessionStateAt_unfold_cap A.repAlloc (sp + 0x128#64) G sess.state]
        sep_ac_rfl
      rwa [← heq]
    have hmf3 := Satisfies.mono (sepConj_mono_left (flag_memRegion_weaken sp 0#8)) hmf2
    have heq2 :
        (memRegion (sp + 0x280#64) 0x1ea ∗
         (scratch sp ∗ vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
           sessionStateAt A.repAlloc (sp + 0x128#64) G sess.state ∗
           pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           encCommonPlaced (A.atState lim st s1) ctl x (x.draws S answers) s0 ∗ R)) =
        ((scratch sp ∗
          vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          sessionStateAt A.repAlloc (sp + 0x128#64) G sess.state ∗
          memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         encCommonPlaced (A.atState lim st s1) ctl x (x.draws S answers) s0 ∗ R) := by sep_ac_rfl
    rwa [← heq2]

theorem tailDropRecordCur_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {C : Crypto} {ctl : BitVec 64} {parse : UuidParser}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {ist0 : ikit.IdState}
    (env : EncEnvPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl parse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st : M.σ) (R0 : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp) (scratch : BitVec 64 → SepProp)
    (hscr : scratch = curScratch ∨ scratch = cmScratch) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8))) (b469 : BitVec 8)
    (hm : TailModel kit st0 ikit ist0 C S parse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A.repAlloc x.ret e [w0, w1, w2, w3, w4, w5] H)
    (hs : EncTailVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv
      x st_init st answers (encEntryPlaced + 0x54c#64) (tailRegs w0 w1 w2)
      (fun sp => scratch sp ∗ sessionRecordAt A.repAlloc (sp + 0x110#64) g rec ∗
        memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
        pollWith sp 0x9d0 [w3, w4, w5] ∗ H)
      R0 s0 s) :
    SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord Hk
      x st_init R0 s0 s (fun _ => False) :=
  tailDropRecordCur_placed_ok_of_dropSs_dealloc env.callees.dropSs env.hooks.dealloc
    x st_init st R0 s0 s answers e w0 w1 w2 w3 w4 w5 H scratch hscr g rec b469 hm hst hs

end LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailDropRecordStepsPlacedBudget
