/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegLoad
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.SessionOnlyKitEPlaced
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegLoad

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.CliRatchet.DecPlaced CryptoVerification.CliRatchet.Placed CryptoVerification.Cli.CoinsTape
open Arm64
open ProofLib
open ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalSession
open CryptoGames
open CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt hiding lsStringCloneSym lsExpectFailedSym wsEntryPCPlaced loadPolledPCPlaced keyReadyPCPlaced saveCallPCPlaced untrustedPCPlaced trustedPCPlaced storeCallPCPlaced errJoinPCPlaced resultFinalPCPlaced decStoreExtraPlaced wsStack_split_extra_placed wsStack_join_extra_placed wsCalleeStack_join_extra_placed wsCalleeStack_split_extra_placed wsMetaPlaced wsFixedVPlaced wsEnvPlaced satisfies_decVtablesAtV_placed LoadPolledStateVPlaced wsRegionFrameVPlaced RegionSomeStateVPlaced regionNonePrePlaced RegionNoneStateVPlaced PostSomeStateVPlaced PostNoneStateVPlaced KeyReadyStateVPlaced TrustedStateVPlaced StoreCallStateVPlaced ErrJoinStateVPlaced ResultFinalStateVPlaced withStoresDecPlacedSpecV withStoresDecPlacedSpecV_pre_addrOk DecSegVPlaced PublicApiDecHooksPlaced DecHypsVPlaced DecFsCtxPlaced RemoteIdentityKeyPlacedOk DropSessionStructureLocal2PlacedOk SegLoadSpecVPlaced SegDispatchSpecVPlaced SegRegionSomeSpecVPlaced SegRegionNoneSpecVPlaced SegPostSomeSpecVPlaced SegPostNoneSpecVPlaced SegTrustSpecVPlaced SegUntrustedSpecVPlaced SegSaveSpecVPlaced SegStoreSpecVPlaced SegErrTeardownSpecVPlaced SegWriteSpecVPlaced
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegLoad hiding messageDecrypt_of_sepWP_lscro messageDecrypt_call_panic_then_wp_lscro messageDecrypt_call_panic_then_wpp_lscro loadShim_onPanic_entailsVPlaced decSegVPlaced_of_sepWPp segLoadVPlaced_ok

set_option maxRecDepth 200000
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero


theorem messageDecrypt_of_sepWP_lscro [LibsignalPlacement] {prog : Program} {ret mid : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (h : SepWP prog mid s P
      (fun sm Pm => StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  StoreKit.sepWPp_seq_lscro hF h

theorem messageDecrypt_call_panic_then_wp_lscro [LibsignalPlacement] {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {P F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hF : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P ∗ R') → (s.mem ⊨ spec.pre x s ∗ (F ∗ R')))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWP prog target_pc sf (spec.post x s sf ∗ F)
        (fun sf' P_f => StoreKit.LibsignalCodeRoLoaded lsmpl sf'.mem → post sf' P_f))
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h) :
    SepWPp prog target_pc s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) := by
  intro R' hm hL
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R') hpc hrun (hpre R' hm) hsp_align hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_hoom_st, _hoom_post⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hFm := hF.of_keepsFrozen hsteps.keepsFrozen
    obtain ⟨sf, hsteps', ⟨hpc', hrun', P_f, hmf, hq⟩ | ⟨_, _hoom⟩⟩ :=
      (hnext sm hpcm hrunm hspm hcsm).elim hpost (hsteps.codeLoaded hL)
    · exact ⟨sf, hsteps.trans hsteps', Or.inl ⟨hpc', hrun', P_f, hmf, hq (hFm.of_keepsFrozen hsteps'.keepsFrozen)⟩⟩
    · exact (not_satisfies_false_sepConj _hoom).elim
  · rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, _, hpost,
      fun hm' => Satisfies.mono (sepConj_mono_left (hpan sm)) hm'⟩)⟩
  · rw [hexit_eq] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · exact (hoom sm (F ∗ R') _hoom_st _hoom_post).elim

theorem messageDecrypt_call_panic_then_wpp_lscro [LibsignalPlacement] {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {P F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hF : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P ∗ R') → (s.mem ⊨ spec.pre x s ∗ (F ∗ R')))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog target_pc sf (spec.post x s sf ∗ F) post
        (fun sf' P_f => (sf'.mem ⊨ P_f ∗ R) → (sf'.mem ⊨ Qpan sf' ∗ R)))
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h) :
    SepWPp prog target_pc s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) := by
  intro R' hm hL
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R') hpc hrun (hpre R' hm) hsp_align hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_hoom_st, _hoom_post⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hFm := hF.of_keepsFrozen hsteps.keepsFrozen
    obtain ⟨sf, hsteps', hout'⟩ :=
      (hnext sm hpcm hrunm hspm hcsm hFm) R' hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, _, hpost,
      fun hm' => Satisfies.mono (sepConj_mono_left (hpan sm)) hm'⟩)⟩
  · rw [hexit_eq] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · exact (hoom sm (F ∗ R') _hoom_st _hoom_post).elim

theorem loadShim_onPanic_entailsVPlaced [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {s0 s sf : State} {F : SepProp}
    (htr : s.trace = s0.trace) :
    (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      (withStoresDecPlacedSpecV C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope).onPanic x s0 sf := by
  dsimp only [withStoresDecPlacedSpecV, StoreKit.withLsCodeRoLoaded]
  rw [sepConj_assoc]
  refine Entails.pure_left fun ⟨halloc, hpref⟩ => ?_
  unfold allocFailedIn at halloc ⊢
  rw [htr] at halloc hpref
  exact Entails.pure_right ⟨hpref, Or.inl halloc⟩ (entails_anyHeap _)

theorem decSegVPlaced_of_sepWPp [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s : State} {target : BitVec 64} {P : SepProp}
    {Out : State → Prop}
    (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWPp (lsProg_463 H) target s P
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → Out sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (withStoresDecPlacedSpecV C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope).onPanic x s0 sf ∗ R))) :
    DecSegVPlaced C A ctl uuidTryParse S encRecord H kit ikit st0 ist0 Scope x R s0 s Out := by
  intro hL
  obtain ⟨sf, hsteps, hout⟩ := hwp R hm hL
  rcases hout with ⟨_, _, P_f, hmf, hOut⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, _hoom⟩
  · exact ⟨sf, hsteps, Or.inl (hOut hmf)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inl ⟨hpan, hqp hmf⟩))⟩
  · dsimp only at _hoom
    exact (not_satisfies_false_sepConj _hoom).elim

set_option maxHeartbeats 1600000 in
theorem segLoadVPlaced_ok [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} :
    SegLoadSpecVPlaced C A ctl uuidTryParse S encRecord H kit ikit st0 ist0 Scope := by
  intro hH x R s0 hfs hpc hrun hal hpre
  obtain ⟨hcrl0, hpre⟩ := StoreKit.extract_withLsCodeRoLoaded hpre
  dsimp only [withStoresDecPlacedSpecV] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx4, hx6, hx8, hsp_le, haddr_ss, _haddr_id⟩, hmem⟩
  simp only [← sepConj_assoc] at hmem
  simp only [wp_norm, arm64_norm] at hx0 hx1 hx2 hx4 hx6 hx8
  unfold wsEntryPCPlaced at hpc
  have hshim := subroutine_ok_withStepsPost
    (hH.kit.loadShim (callerProg := lsProg_463 H) (callerBlk := 463) (by decide))
  have hpoll := hH.kit.loadPoll (callerProg := lsProg_463 H) (callerBlk := 463) (by decide)
  rw [BitVec.zero_add] at hshim hpoll
  have hfsAt : FsAt kit.envOk (kit.Quiet ∧ ikit.Quiet) (lsProg_463 H) s0 :=
    (hfs.fsAt (evs := []) (List.append_nil _).symm (fun _ => NoFsEv.nil)).mono (fun _ h => h.1) id
  have hsp_lt := s0.sp.isLt
  have hn_v : wsCalleeStackV kit ikit ≤ 2 ^ 64 := by
    have : wsStackV kit ikit = wsCalleeStackV kit ikit + 0xee0 := rfl
    omega
  have hsp_base : wsStack ≤ s0.sp.toNat := Nat.le_trans (wsStack_le_V kit ikit) hsp_le
  apply decSegVPlaced_of_sepWPp (target := loadPolledPCPlaced) hmem
  unfold loadPolledPCPlaced
  dsimp only [lsProg_463] at hshim hpoll hfsAt ⊢
  apply messageDecrypt_of_sepWP_lscro hcrl0 (mid := kit.loadShimOff)
  rw [stackAt_wsStackV_split kit ikit s0.sp hsp_le, memRegion_0xe80_split (s0.sp - 0xee0#64),
    stack_wsCalleeV_shim kit ikit (s0.sp - 0xee0#64) hn_v]
  cells_unfold
  unfold decVtablesAtV decLoadVtableAtV decStoreVtableAtV decTrustVtableAtV decSaveVtableAtV
  wp_simp_pre [cells_succ, cells_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat' (apply SepWP.exists_elim; intro _)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hF1
  apply (messageDecrypt_call_panic_then_wpp_lscro hshim (x := ⟨s0.readReg64 (Reg.gpr 3#5), x.remA⟩) hF1)
  · wp_norm_lhs
  · wp_norm_lhs
  · simp only [State.spAligned, wp_norm, arm64_norm]; exact hal
  · wp_norm_lhs
  · intro _R' _hmR'
    dsimp only [withStepsPost, Arm64.ReachesOutcome.withStepsPost, StoreKit.withLsRoCl, kitLoadShimSpec]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hF1, ?_⟩
    simp only [sepConj_assoc, wp_norm, arm64_norm, hx1] at _hmR' ⊢
    arm64_sep_close
  · intro _; exact loadShim_onPanic_entailsVPlaced (by wp_norm_lhs)
  · intro _ _; rfl
  intro sf hpc_sf hrun_sf hsp_sf hcs_sf hF2
  dsimp only [withStepsPost, Arm64.ReachesOutcome.withStepsPost, StoreKit.withLsRoCl, kitLoadShimSpec]
  simp only [wp_norm, arm64_norm] at hpc_sf hsp_sf
  apply messageDecrypt_of_sepWP_lscro hF2 (mid := kit.loadPollOff)
  wp_simp_pre [sepConj_assoc]
  apply SepWP.pure_elim; rintro ⟨hsteps_sh, _hcrl_sf, hx1_sf, hbox_ne, hbox_mod, htr_sf⟩
  have henv : kit.envOk sf.fs.files :=
    (hfsAt.of_call hsteps_sh (by simp only [arm64_norm]) htr_sf).envOk_here
  clear hsteps_sh hfsAt
  simp only [wp_norm, arm64_norm] at hx1_sf
  apply SepWP.fold (Entails.of_eq (stack_wsCalleeV_shim_to_poll kit ikit (s0.sp - 0xee0#64) hn_v)) (by sep_focus)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hF3
  apply (messageDecrypt_call_panic_then_wp_lscro hpoll
    (x := (⟨sf.readReg64 (Reg.gpr 0#5), (s0.sp - 0xee0#64) + 0x5f0#64, x.remA, x.rem⟩,
      s0.readReg64 (Reg.gpr 3#5), st0)) hF3)
  · wp_norm_lhs
  · wp_norm_lhs
  · simp only [State.spAligned, wp_norm, arm64_norm, hsp_sf]; exact hal
  · wp_norm_lhs
  · intro _R' _hmR'
    dsimp only [StoreKit.withLsRoCl]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hF3, ?_⟩
    refine withEnvPre_pre_intro (by simp only [arm64_norm]; exact henv) ?_
    dsimp only [StoreKit.kitLoadPollPlacedSpecS]
    simp only [sepConj_assoc, wp_norm, arm64_norm, hsp_sf, haddr_ss, and_true] at _hmR' ⊢
    arm64_sep_close
  · intro _; exact loadShim_onPanic_entailsVPlaced (by simp only [wp_norm, arm64_norm]; exact htr_sf)
  · intro _ _; rfl
  intro sf1 hpc_sf1 hrun_sf1 hsp_sf1 hcs_sf1
  dsimp only [StoreKit.withLsRoCl, StoreKit.kitLoadPollPlacedSpecSE, StoreKit.kitLoadPollPlacedSpecS]
  simp only [wp_norm, arm64_norm, hsp_sf] at hpc_sf1 hsp_sf1
  wp_simp_pre [wp_norm, arm64_norm, hsp_sf, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w
  apply SepWP.pure_elim; rintro ⟨_hcrl_sf1, hloadRel, htr_sf1⟩
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
  refine ⟨⟨w, .ok false, .ok .newOrUnchanged, .ok ()⟩, ?_⟩
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
  · dsimp only [LoadPolledStateVPlaced, wsFixedVPlaced, wsArgCellsV, decVtablesAtV,
      decLoadVtableAtV, decStoreVtableAtV, decTrustVtableAtV, decSaveVtableAtV,
      wsEnvPlaced, wsMsgCells, Reg.x3, Reg.x5] at hmf ⊢
    simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub, BitVec.add_assoc] at hmf ⊢
    arm64_sep_close


end CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegLoad
