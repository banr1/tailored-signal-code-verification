/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegSaveAuxBudget
public meta import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegSaveAuxBudget -- shake: keep
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.ExtDefsPlacedBudgetFd
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegBatch1PlacedBudget
import LibsignalBinary.Proofs.PublicApi.StoreKit.RecordMove
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# File-Descriptor-Threaded Relocatable `SegLoad` and `SegRegionSome`

Proves `FdsGe3Closed`-threaded `segLoadVX_placed_ok_fd` (`+0x0 → +0x8c`) and
`segRegionSomeV_placed_ok_fd` (`+0x1a8 → +0x1f50`) on `lsProg_463 H`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegBatch1PlacedBudgetFd

open Arm64 ProofLib ProofLib.ProgramReflection
open scoped LibsignalBinary.Proofs.Placed.BudgetVmSteps
open scoped LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegSaveAuxBudget
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.CliRatchet.DecPlaced (lsProg_463)
open CryptoVerification.RustHeap (vecBuf)
open CryptoGames.LibsignalSession (Crypto)
open CryptoGames.LibsignalSessionApi (SessionRecord StoreAnswers)
open CryptoVerification.LibsignalTripleRatchetRepr
  (protocolAddressAt signalMessageAt uuidTryParse)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel region_ok)
open CryptoVerification.LibsignalPublicApi (DecryptGhost)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsAt LibsignalCodeRoLoaded NoFsEv SessionStoreSpec extract_withLsCodeRoLoaded
   loadPollPlacedOutAtS subroutine_ok_withStepsPost withEnvPre withEnvPre_pre_intro
   withLsRoCl withStepsPost)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreSpec)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
  (ScopePq decLoadVtableAtV decSaveVtableAtV decStoreVtableAtV decTrustVtableAtV
   decVtablesAtV prevBufAt recGhostOf wsArgCellsV wsCalleeStackV wsMsgCells wsStack
   wsStackV wsStack_le_V)
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt
  (decStoreExtraPlaced loadPolledPCPlaced wsCalleeStack_split_extra_placed wsEntryPCPlaced
   wsEnvPlaced wsFixedVPlaced wsMetaPlaced wsRegionFrameVPlaced)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegLoad
  (fold_2c8 fold_2e0 fold_sp0 fold_words8 memRegion_0xe80_split stackAt_wsStackV_split
   stack_wsCalleeV_poll_back stack_wsCalleeV_shim stack_wsCalleeV_shim_to_poll wsSavedRegs_fold)
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegLoad
  (messageDecrypt_call_panic_then_wp_lscro messageDecrypt_call_panic_then_wpp_lscro
   messageDecrypt_of_sepWP_lscro)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegRegionSome
  (model_panic_of_region_panic recvPanics_of_region_recvPanics)
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegRegionSome
  (post_meta_extract_placed)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget SeqEnv VmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (vmPreserved_setPC vmPreserved_writeReg64)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
  (SessionStoreBudgetEnv kitLoadShimSpec retagSessionStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
  (IdentityStoreBudgetEnv retagIdentityStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
  (kitLoadPollPlacedSpecS kitLoadPollPlacedSpecSE)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
  (RecordDecryptEnv SeamBudget TryDecryptEnvArgs)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
  (LoadPollStepEnv WithStoresDecEnv fromPostSomeEnv_nonempty)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegSaveAuxBudget (sepWP_cut_here)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed withFdsGe3Closed)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsPlacedBudget
  (sessionGhostValid_of_recordPlacedPre)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsPlacedBudgetFd
  (LoadPolledStateVPlacedFd PostSomeStateVPlacedFd RegionSomeStateVPlacedFd)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsVXPlacedBudget
  (DecSegVXPlaced withStoresDecPlacedSpecVX)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsVXPlacedBudgetFd
  (withStoresDecPlacedSpecVXFd withStoresDecPlacedSpecVXFd_pre_elim)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.ExtDefsPlacedBudget
  (decSegVXPlaced_of_sepWPp false_onPanic_entails)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.ExtDefsPlacedBudgetFd
  (DecFsCtxExtPlacedFd DecHypsExtPlacedFd)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## `segLoadVX_placed_ok_fd` (`+0x0 → +0x8c`) -/

private theorem rep_protocolAddressAt_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (P : SepProp) :
    protocolAddressAt { pool := P, live := A.live } = protocolAddressAt A.repAlloc := rfl

private theorem rep_signalMessageAt_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (P : SepProp) :
    signalMessageAt { pool := P, live := A.live } = signalMessageAt A.repAlloc := rfl

private theorem rep_loadPollOut_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (P : SepProp) :
    loadPollPlacedOutAtS Scope { pool := P, live := A.live } =
      loadPollPlacedOutAtS Scope A.repAlloc := rfl

private theorem rep_decVtables_eq {M : AllocCostModel} (A : RustCliAllocBudget M) (P : SepProp)
    (kit : SessionStoreSpec A.repAlloc 0#64) (ikit : IdentityStoreSpec A.repAlloc 0#64) :
    decVtablesAtV (retagSessionStore (A' := { pool := P, live := A.live }) kit)
      (retagIdentityStore (A' := { pool := P, live := A.live }) ikit) =
    decVtablesAtV kit ikit := rfl

private theorem rep_decStoreExtra_eq [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (P : SepProp)
    (kit : SessionStoreSpec A.repAlloc 0#64) (ikit : IdentityStoreSpec A.repAlloc 0#64) :
    decStoreExtraPlaced (retagSessionStore (A' := { pool := P, live := A.live }) kit)
      (retagIdentityStore (A' := { pool := P, live := A.live }) ikit) =
    decStoreExtraPlaced kit ikit := rfl

set_option maxHeartbeats 1600000 in
theorem segLoadVX_placed_ok_fd [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    (hH : DecHypsExtPlacedFd C A lim uuidTryParse S encRecord H kit kitEnv ikit ikitEnv st0 Scope)
    (x : DecryptGhost) (st_init : M.σ) (R : SepProp) (s0 : State)
    (hfs : DecFsCtxExtPlacedFd kit ikit H s0 s0)
    (hpc : s0.pc = wsEntryPCPlaced)
    (hrun : s0.status = .Running)
    (hal : s0.spAligned = true)
    (hpre : s0.mem ⊨ (withStoresDecPlacedSpecVXFd
      C A lim ctl uuidTryParse S tdEnv encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope Extra).pre
      (x, st_init) s0 ∗ R) :
    DecSegVXPlaced C A lim ctl uuidTryParse S tdEnv encRecord H kit kitEnv ikit ikitEnv
      st0 ist0 Scope Extra x st_init R s0 s0
      (fun s' => ∃ ans, LoadPolledStateVPlacedFd C A lim ctl uuidTryParse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans R s0 s') := by
  obtain ⟨hFds0, hpre⟩ := withStoresDecPlacedSpecVXFd_pre_elim hpre
  have hfds0_kit : kit.fdsOk s0.fs := (hH.ss_fdsOk s0.fs).mpr hFds0
  dsimp only [withStoresDecPlacedSpecVX,
    LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsPlacedBudget.withStoresDecPlacedSpecV] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hfits_init, hpre⟩
  have hsb0 : SeamBudget M lim
      (WithStoresDecEnv kit kitEnv st0 ikit ikitEnv ist0 C S uuidTryParse tdEnv Scope x)
      st_init st_init
      (WithStoresDecEnv kit kitEnv st0 ikit ikitEnv ist0 C S uuidTryParse tdEnv Scope x) :=
    SeamBudget.init hfits_init
  have hfits_load : FitsEnv M lim st_init (LoadPollStepEnv kit kitEnv st0 x.rem.val) :=
    hfits_init.seq_left
  have hfits_sh : FitsEnv M lim st_init (BoxAllocEnv kit.loadBoxSize) :=
    hfits_load.seq_left
  obtain ⟨hcrl0, hpre⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecPlacedSpecV] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx4, hx6, hx8, hsp_le, haddr_ss, _haddr_id⟩, hmem⟩
  change wsStackV kit ikit ≤ s0.sp.toNat at hsp_le
  rw [show wsStackV (retagSessionStore (A' := A.atState lim st_init s0) kit)
      (retagIdentityStore (A' := A.atState lim st_init s0) ikit) = wsStackV kit ikit from rfl] at hmem
  simp only [← sepConj_assoc] at hmem
  simp only [wp_norm, arm64_norm] at hx0 hx1 hx2 hx4 hx6 hx8
  unfold wsEntryPCPlaced at hpc
  have hshim := subroutine_ok_withStepsPost
    (hH.loadFds.loadShim (callerProg := lsProg_463 H) (callerBlk := 463) (by decide))
  have hpoll := hH.loadFds.loadPoll (callerProg := lsProg_463 H) (callerBlk := 463) (by decide)
  rw [BitVec.zero_add] at hshim hpoll
  have hfsAt : FsAt kit.envOk (kit.Quiet ∧ ikit.Quiet) (lsProg_463 H) s0 :=
    (hfs.fsAt (evs := []) (List.append_nil _).symm (fun _ => NoFsEv.nil)).mono
      (fun _ h => h.1) id
  have hsp_lt := s0.sp.isLt
  have hn_v : wsCalleeStackV kit ikit ≤ 2 ^ 64 := by
    have : wsStackV kit ikit = wsCalleeStackV kit ikit + 0xee0 := rfl
    omega
  have hsp_base : wsStack ≤ s0.sp.toNat := Nat.le_trans (wsStack_le_V kit ikit) hsp_le
  apply decSegVXPlaced_of_sepWPp (st_init := st_init) (target := loadPolledPCPlaced) hmem
  unfold loadPolledPCPlaced
  dsimp only [lsProg_463] at hshim hpoll hfsAt ⊢
  apply messageDecrypt_of_sepWP_lscro hcrl0 (mid := kit.loadShimOff)
  rw [stackAt_wsStackV_split kit ikit s0.sp hsp_le,
    memRegion_0xe80_split (s0.sp - 0xee0#64),
    stack_wsCalleeV_shim kit ikit (s0.sp - 0xee0#64) hn_v]
  cells_unfold
  unfold decVtablesAtV decLoadVtableAtV decStoreVtableAtV decTrustVtableAtV decSaveVtableAtV
  dsimp only [RustCliAllocBudget.atState]
  wp_simp_pre [cells_succ, cells_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat' (apply SepWP.exists_elim; intro _)
  apply sepWP_cut_here
  by_vm_open (
    wp_steps 8
    refine SepWP.done rfl (by wp_norm_lhs) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
    intro hvm0
    refine SepWP.transport_budgetPool hvm0 (hnext := ?_); clear hvm0
    wp_step
    refine SepWP.transport_budgetPool
      ((vmPreserved_setPC _ _ _).mpr ((vmPreserved_writeReg64 _ _ _ _).mpr (VmPreserved.refl _)))
      (hnext := ?_)
    by_vm_open (
    wp_steps
    refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
    intro hvm1 hF1
    refine SepWPp.transport_budgetPool hvm1 (hnext := ?_); clear hvm1
    apply (messageDecrypt_call_panic_then_wpp_lscro hshim
      (x := (⟨s0.readReg64 (Reg.gpr 3#5), x.remA⟩, st_init)) hF1)
    · wp_norm_lhs
    · wp_norm_lhs
    · simp only [State.spAligned, wp_norm, arm64_norm]; exact hal
    · wp_norm_lhs
    · intro _R' _hmR'
      dsimp only [withStepsPost, Arm64.ReachesOutcome.withStepsPost, withLsRoCl, kitLoadShimSpec]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      refine ⟨hF1, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨by wp_norm_lhs, by simp only [wp_norm, arm64_norm, hx1], hfits_sh,
        by simpa only [wp_norm, arm64_norm] using hfds0_kit⟩, ?_⟩
      simp only [sepConj_assoc, wp_norm, arm64_norm, hx1] at _hmR' ⊢
      arm64_sep_close
    · intro _; exact false_onPanic_entails
    · intro _ _; rfl
    intro sf hpc_sf hrun_sf hsp_sf hcs_sf hF2
    dsimp only [withStepsPost, Arm64.ReachesOutcome.withStepsPost, withLsRoCl, kitLoadShimSpec]
    simp only [wp_norm, arm64_norm] at hpc_sf hsp_sf
    apply messageDecrypt_of_sepWP_lscro hF2 (mid := kit.loadPollOff)
    wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro (evs_sh : List AllocEvent)
    wp_simp_pre [sepConj_assoc]
    apply SepWP.pure_elim
    rintro ⟨hsteps_sh, _hcrl_sf, hx1_sf, hbox_ne, hbox_mod, htr_sf, hevs_sh, hfds_sf⟩
    have hfits_pl : FitsEnv M lim (M.stepEvents evs_sh st_init) (kitEnv.loadPollEnv st0 x.rem.val) :=
      hfits_load.seq_right hevs_sh
    have hFds_sf : FdsGe3Closed sf.fs := (hH.ss_fdsOk sf.fs).mp hfds_sf
    have henv : kit.envOk sf.fs.files :=
      (hfsAt.of_call hsteps_sh (by simp only [arm64_norm]) htr_sf).envOk_here
    clear hsteps_sh hfsAt
    simp only [wp_norm, arm64_norm] at hx1_sf
    apply SepWP.fold (Entails.of_eq (stack_wsCalleeV_shim_to_poll kit ikit (s0.sp - 0xee0#64) hn_v)) (by sep_focus)
    by_vm_open (
      wp_steps
      refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
      intro hvm2 hF3
      refine SepWPp.transport_budgetPool hvm2 (hnext := ?_); clear hvm2
      apply (messageDecrypt_call_panic_then_wp_lscro hpoll
        (x := (⟨sf.readReg64 (Reg.gpr 0#5), (s0.sp - 0xee0#64) + 0x5f0#64, x.remA, x.rem⟩,
          s0.readReg64 (Reg.gpr 3#5), st0, M.stepEvents evs_sh st_init)) hF3)
      · wp_norm_lhs
      · wp_norm_lhs
      · simp only [State.spAligned, wp_norm, arm64_norm, hsp_sf]; exact hal
      · wp_norm_lhs
      · intro _R' _hmR'
        dsimp only [withLsRoCl]
        rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
        refine ⟨hF3, ?_⟩
        refine withEnvPre_pre_intro ⟨by simp only [arm64_norm]; exact henv,
          by simpa only [wp_norm, arm64_norm] using hfds_sf⟩ ?_
        dsimp only [kitLoadPollPlacedSpecS]
        rw [sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨⟨by wp_norm_lhs,
          by simp (config := { decide := true }) only [wp_norm, arm64_norm, bv_sub_add_lit, Nat.reduceSub],
          haddr_ss, hfits_pl⟩, ?_⟩
        simp (config := { decide := true }) only [sepConj_assoc, wp_norm, arm64_norm, hsp_sf,
          bv_sub_add_lit, Nat.reduceSub, BitVec.add_assoc, BitVec.zero_add,
          rep_protocolAddressAt_eq, rep_signalMessageAt_eq] at _hmR' ⊢
        arm64_sep_close
      · intro _; exact false_onPanic_entails
      · intro _ _; rfl
      intro sf1 hpc_sf1 hrun_sf1 hsp_sf1 hcs_sf1
      dsimp only [withLsRoCl, withEnvPre, kitLoadPollPlacedSpecSE, kitLoadPollPlacedSpecS]
      simp only [wp_norm, arm64_norm, hsp_sf] at hpc_sf1 hsp_sf1
      wp_simp_pre [wp_norm, arm64_norm, hsp_sf, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWP.exists_elim; intro w
      apply SepWP.exists_elim; intro (evs_pl : List AllocEvent)
      wp_simp_pre [sepConj_assoc]
      apply SepWP.pure_elim; rintro ⟨_hcrl_sf1, hloadRel, htr_sf1, hevs_pl, hfds_sf1⟩
      apply SepWP.fold (wsSavedRegs_fold s0.sp s0) (by sep_focus)
      apply SepWP.fold (fold_sp0 (s0.sp - 0xee0#64) 0#64) (by sep_focus)
      apply SepWP.fold (fold_words8 (s0.sp - 0xee0#64 + 0xa0#64)
        x.msgA x.remA x.locA (s0.readReg64 (Reg.gpr 3#5))
        kit.ss_vt (s0.readReg64 (Reg.gpr 5#5))
        ikit.id_vt (s0.sp - 113#64)) (by sep_focus)
      apply SepWP.fold (fold_2c8 (s0.sp - 0xee0#64) 0#8) (by sep_focus)
      apply SepWP.fold (fold_2e0 (s0.sp - 0xee0#64) _ _ 0#64) (by sep_focus)
      apply SepWP.fold (Entails.of_eq (stack_wsCalleeV_poll_back kit ikit (s0.sp - 0xee0#64) hn_v)) (by sep_focus)
      have hsplit_extra := wsCalleeStack_split_extra_placed kit ikit st0 ist0 s0 hsp_le
      dsimp only [Reg.x3, Reg.x5] at hsplit_extra
      apply SepWP.fold hsplit_extra (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF4 hmf
      have hstep_load : LoadPollStepEnv kit kitEnv st0 x.rem.val (evs_sh ++ evs_pl) :=
        SeqEnv.append hevs_sh hevs_pl
      have hsb1 := hsb0.step (fun _ _ h1 h2 => SeqEnv.append h1 h2) hstep_load
      have hst1_eq : M.stepEvents evs_pl (M.stepEvents evs_sh st_init) =
          M.stepEvents (evs_sh ++ evs_pl) st_init :=
        (M.stepEvents_append evs_sh evs_pl st_init).symm
      refine ⟨⟨w, .ok false, .ok .newOrUnchanged, .ok ()⟩, ?_, (hH.ss_fdsOk sf1.fs).mp hfds_sf1⟩
      refine ⟨M.stepEvents (evs_sh ++ evs_pl) st_init, hsb1, ?_⟩
      refine ⟨?_, ?_, hsp_base, ?_, hloadRel, ?_, ?_⟩
      · wp_norm_lhs
      · simp only [CalleeSavedPreserved, wp_norm, arm64_norm] at hcs_sf hcs_sf1
        refine ⟨by wp_norm_lhs,
                by simp only [wp_norm, arm64_norm, hsp_sf1],
                hal,
                by simp only [State.spAligned, wp_norm, arm64_norm, hsp_sf1]; exact hal,
                by simp only [wp_norm, arm64_norm, hcs_sf1, hcs_sf],
                by simp only [wp_norm, arm64_norm, hcs_sf1, hcs_sf],
                hF4,
                by simp only [wp_norm, arm64_norm, hcs_sf1, hcs_sf]⟩
      · simp only [CalleeSavedPreserved, wp_norm, arm64_norm] at hcs_sf1
        simpa only [Reg.x19, wp_norm, arm64_norm, hsp_sf] using hcs_sf1.1
      · simp only [wp_norm, arm64_norm] at htr_sf1 ⊢
        rw [htr_sf1, htr_sf]
      · rw [← hst1_eq]
        dsimp only [CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.LoadPolledStateVPlaced,
          wsFixedVPlaced, wsArgCellsV, decVtablesAtV,
          decLoadVtableAtV, decStoreVtableAtV, decTrustVtableAtV, decSaveVtableAtV,
          wsEnvPlaced, wsMsgCells, RustCliAllocBudget.atState, Reg.x3, Reg.x5] at hmf ⊢
        simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub, BitVec.add_assoc,
          BitVec.zero_add, rep_protocolAddressAt_eq, rep_signalMessageAt_eq, rep_loadPollOut_eq,
          rep_decVtables_eq, rep_decStoreExtra_eq] at hmf ⊢
        arm64_sep_close
    )
    )
  )

/-! ## `segRegionSomeV_placed_ok_fd` (`+0x1a8 → +0x1f50`) -/

private theorem rep_wsRegionFrameV_eq [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (P₁ P₂ : SepProp)
    (kit : SessionStoreSpec A.repAlloc 0#64) (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (x : DecryptGhost) (s0 : State) (prevCap prevPtr : BitVec 64) :
    wsRegionFrameVPlaced
      (retagSessionStore (A' := { pool := P₁, live := A.live }) kit)
      (retagIdentityStore (A' := { pool := P₁, live := A.live }) ikit) x s0 prevCap prevPtr =
    wsRegionFrameVPlaced
      (retagSessionStore (A' := { pool := P₂, live := A.live }) kit)
      (retagIdentityStore (A' := { pool := P₂, live := A.live }) ikit) x s0 prevCap prevPtr := by
  dsimp only [wsRegionFrameVPlaced, prevBufAt, vecBuf]
  split <;> rfl

theorem segRegionSomeV_placed_ok_fd [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (Q : List (BitVec 8) → Prop)
    (hreg : region_ok (lsProg_463 H)
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.recEntryPlaced
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.recExitPlaced
      ((withFdsGe3Closed
        (LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.recordDecryptPlacedSpec
          C A lim ctl uuidTryParse S tdEnv)).withVRegs.restrictPre
            (fun p => Q p.1.st.pqRatchetState)))
    (hQ : ScopePq kit st0 Scope Q)
    (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (R : SepProp) (s0 s : State)
    (hRSFd : RegionSomeStateVPlacedFd C A lim ctl uuidTryParse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans R s0 s) :
    DecSegVXPlaced C A lim ctl uuidTryParse S tdEnv encRecord H kit kitEnv ikit ikitEnv
      st0 ist0 Scope (fun x answers => x.recvPanics S answers) x st_init R s0 s
      (fun s' => PostSomeStateVPlacedFd C A lim ctl uuidTryParse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans R s0 s') := by
  intro hL
  rcases hRSFd with ⟨hRS, hFds_s⟩
  obtain ⟨st, hsb_all, hpc, ⟨hrun, hsp, hal0, hal, hx29, _hx27, hcrl, hvregs⟩,
    rec, ses, G, prevCap, prevPtr, hload, hscope, hcur, hw0, htrace, hmem⟩ := hRS
  let x_rg := recGhostOf x prevPtr G ses.state
  let R_rg : SepProp :=
    (wsRegionFrameVPlaced
      (retagSessionStore (A' := A.atState lim st s) kit)
      (retagIdentityStore (A' := A.atState lim st s) ikit) x s0 prevCap prevPtr ∗
    decStoreExtraPlaced
      (retagSessionStore (A' := A.atState lim st s) kit)
      (retagIdentityStore (A' := A.atState lim st s) ikit) st0 ist0 s0 ∗ R)
  have hgv := sessionGhostValid_of_recordPlacedPre hw0 (by simpa only [sepConj_assoc] using hmem)
  have hsb := hsb_all rec ses G hload hscope hcur hgv
  have hfits : FitsEnv M lim st (RecordDecryptEnv tdEnv x_rg) :=
    hsb.fitsSeg (fun _ _ h1 h2 => SeqEnv.append h1 h2) fromPostSomeEnv_nonempty
  have hmem_rg :
      s.mem ⊨
        (withFdsGe3Closed
          (LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.recordDecryptPlacedSpec
            C A lim ctl uuidTryParse S tdEnv)).withVRegs.pre (x_rg, st) s ∗ R_rg := by
    dsimp only [x_rg, R_rg, Spec.withVRegs, withFdsGe3Closed,
      LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.recordDecryptPlacedSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hFds_s, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hfits, by simpa only [sepConj_assoc] using hmem⟩
  have hmemQ :
      s.mem ⊨
        ((withFdsGe3Closed
          (LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.recordDecryptPlacedSpec
            C A lim ctl uuidTryParse S tdEnv)).withVRegs.restrictPre
              (fun p => Q p.1.st.pqRatchetState)).pre (x_rg, st) s ∗ R_rg :=
    Spec.satisfies_restrictPre.mpr ⟨hQ x.rem.val rec ses hscope hcur, hmem_rg⟩
  obtain ⟨sf, hsteps, hout⟩ := hreg (x_rg, st) R_rg s hpc hrun hmemQ hL
  try dsimp only [Spec.restrictPre] at hout
  rcases hout with ⟨hpc_sf, hrun_sf, hmf⟩ | ⟨hpan_sf, hmf⟩
  · refine ⟨sf, hsteps, Or.inl ?_⟩
    dsimp only [Spec.withVRegs, withFdsGe3Closed,
      LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.recordDecryptPlacedSpec] at hmf
    rw [sepConj_assoc, satisfies_pure_sepConj] at hmf
    obtain ⟨hvregs_sf, hmf⟩ := hmf
    rw [sepConj_assoc, satisfies_pure_sepConj] at hmf
    obtain ⟨hFds_sf, hmf⟩ := hmf
    rw [sepExists_sepConj_left, satisfies_sepExists] at hmf
    obtain ⟨evs, hmf⟩ := hmf
    rw [sepConj_assoc, satisfies_pure_sepConj] at hmf
    obtain ⟨hevs, hmf⟩ := hmf
    obtain ⟨hsp_sf, hx29_sf, hx27_sf⟩ := post_meta_extract_placed hmf
    have hcrl_sf : LibsignalCodeRoLoaded lsmpl sf.mem := hcrl.of_keepsFrozen hsteps.keepsFrozen
    have hal_sf : sf.spAligned = true := by
      rw [State.spAligned, hsp_sf]
      exact hal
    have hmeta_sf : wsMetaPlaced x s0 sf :=
      ⟨hrun_sf, hsp_sf.trans hsp, hal0, hal_sf, hx29_sf.trans hx29,
        hx27_sf, hcrl_sf, hvregs_sf.trans hvregs⟩
    have hsb' := hsb.step (fun _ _ h1 h2 => SeqEnv.append h1 h2) hevs
    refine ⟨⟨M.stepEvents evs st, ?_, hpc_sf, hmeta_sf, s, rec, ses, G, prevCap, prevPtr,
      hsp, htrace, hload, hscope, hcur, hw0, ?_⟩, hFds_sf⟩
    · intro rec₁ hload₁
      cases Option.some.inj (Except.ok.inj (hload.symm.trans hload₁))
      exact hsb'
    · dsimp only [x_rg, R_rg, RustCliAllocBudget.atState] at hmf ⊢
      rw [rep_wsRegionFrameV_eq A (A.pool lim st s) (A.pool lim (M.stepEvents evs st) sf),
        rep_decStoreExtra_eq A (A.pool lim st s),
        ← rep_decStoreExtra_eq A (A.pool lim (M.stepEvents evs st) sf)] at hmf
      simpa only [sepConj_assoc] using hmf
  · refine ⟨sf, hsteps, Or.inr (Or.inr (Or.inl ⟨hpan_sf, ?_⟩))⟩
    dsimp only [Spec.withVRegs, withFdsGe3Closed,
      LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.recordDecryptPlacedSpec,
      withStoresDecPlacedSpecVX, R_rg] at hmf ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hmf
    rcases hmf with ⟨⟨hdisj, hpref⟩, hmf⟩
    have hload_pref : s0.trace ++ kit.loadEvs encRecord x.rem.val ans.loadSession <+: sf.trace := by
      rwa [← htrace]
    have hs0_pref : s0.trace <+: sf.trace :=
      (List.prefix_append s0.trace (kit.loadEvs encRecord x.rem.val ans.loadSession)).trans hload_pref
    have hpan_pure :
        s0.trace <+: sf.trace ∧
          (∃ answers : StoreAnswers (List (BitVec 8)) Unit,
            kit.loadRel st0 x.rem.val answers.loadSession ∧
            s0.trace ++ kit.loadEvs encRecord x.rem.val answers.loadSession <+: sf.trace ∧
            ((x.model C S uuidTryParse answers).1 = .error .panic ∨ x.recvPanics S answers)) := by
      refine ⟨hs0_pref, ?_⟩
      rcases hdisj with hmod_pan | hrecv_pan
      · exact ⟨ans, hload ▸ hscope.2, hload_pref, Or.inl
          (model_panic_of_region_panic C S x ans rec ses G prevPtr hload hcur hmod_pan)⟩
      · exact ⟨ans, hload ▸ hscope.2, hload_pref, Or.inr
          (recvPanics_of_region_recvPanics S x ans rec ses G prevPtr hload hcur hrecv_pan)⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hpan_pure, ?_⟩
    have h_any :
        anyHeap ∗
          (wsRegionFrameVPlaced
            (retagSessionStore (A' := A.atState lim st s) kit)
            (retagIdentityStore (A' := A.atState lim st s) ikit) x s0 prevCap prevPtr ∗
          decStoreExtraPlaced
            (retagSessionStore (A' := A.atState lim st s) kit)
            (retagIdentityStore (A' := A.atState lim st s) ikit) st0 ist0 s0) ⊢ anyHeap :=
      entails_anyHeap _
    rw [← sepConj_assoc, ← sepConj_assoc] at hmf
    rw [sepConj_assoc anyHeap] at hmf
    exact Satisfies.mono (sepConj_mono_left h_any) hmf

end LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegBatch1PlacedBudgetFd
