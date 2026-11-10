/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalUnack
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg1
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFrom
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadCommon
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadDispatchSome
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadDispatchSomeTrap
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadDispatchTrap
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadShimPollTrap
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSave
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSaveTrap
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalFetch
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommon
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegLoadDispatch
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegLoadDispatchSome
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegSignalFrame
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Defs
import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain
import ProofLib.RegChain

@[expose] public section

set_option autoImplicit false

/-!
# CLI `MessageEncrypt` `WithStoresVT` (Part 3): Segments `SegSave`, `SegLoad`, `SegExitVT`, and `SegSignal` Unpack (`_trap`)
-/

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalSpqrV1 (TokenInit)
open CryptoVerification.Cli.LibsignalPublicApi (encryptWithStoresName)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

section SegSave
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSave
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust
  (SegExit.of_false_trap SegExit.of_sepWP_trap encEntry_eq_fnAddr_trap)
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSave
  (save_to_d94_trap step_d94_err_trap step_d94_ok_trap)
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails (tailStoreHookErr_ok_trap)
open CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails

theorem h45_segSave_okVT_trap {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (hEnv : EncEnvT_trap kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
    (otr' : OutgoingTripleRatchet (List (BitVec 8))) (pqCap' pqPtr' : BitVec 64) (R0 : SepProp)
    (s0 s : State)
    (haddr : ikit.addrOk x.rem.val)
    (hfs : EncFsCtx_trap kit ikit C abs s0 s)
    (hsave : SaveStateV kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord x r sess otr taken k m otr' pqCap' pqPtr' R0 s0 s) :
    SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s
      (fun s' => ∃ c, ApplyStateV kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord x r sess otr taken k m otr' pqCap' pqPtr' c R0 s0 s') := by
  let env := h45_envF hEnv
  let R : SepProp := kit.storeAt x.ssA st0 ∗ R0
  obtain ⟨⟨h15, htrustRel⟩, hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hfl, hsym, hvregs⟩,
    htr, ⟨hx20, hx22, hx25, hx26, hx28⟩, hpt, hrest, hloc, hnow, hstk, hm⟩ := hsave
  set sp := s0.sp - 0xbe0#64
  set draws := S.draws otr.pqrState x.rest
  set ist1 := ikit.trustUpdate ist0 x.rem.val k .sending (.ok true)
  set F := Pf.SegSave.savePassive kit.ss_vt ikit.id_vt A img.base x sess taken otr' pqCap' pqPtr' m draws s0
  have hpref0 : s0.trace <+: s.trace := ⟨_, htr.symm⟩
  have hm_pre : s.mem ⊨
      (trustBaseActive ikit.id_vt A img s.sp x k ∗ encStoreExtra kit st0 ikit ist1 x s0) ∗
      ((memRegion (s.sp + 0x470#64) 16 ∗
        memRegion (s.sp + 0x580#64) 48 ∗
        memRegion (s.sp + 0x990#64) 24) ∗ F ∗ R0) := by
    have hm1 : s.mem ⊨
        (cmSlots A s.sp sess taken otr' pqCap' pqPtr' k m ∗ cmScratch s.sp ∗
          encSpillsAtV kit.ss_vt ikit.id_vt s.sp x ∗ memRegion (s.sp + 0x46a#64) 0x716 ∗
          memRegion x.ret 248 ∗
          encCommon A ctl img x draws s0) ∗
        (encStoreExtra kit st0 ikit ist1 x s0 ∗ R0) := by
      rw [hsp]
      exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm
    rw [Pf.SegSave.save_seam_mem_split kit.ss_vt ikit.id_vt A ctl img x sess taken otr' pqCap' pqPtr' k m draws s0 s.sp hsp] at hm1
    dsimp only [F]
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm1
  have hm_join := Satisfies.mono (sepConj_mono_left
    (trustBaseActive_join_extra kit st0 ikit ist1 x k s0 s.sp hsp)) hm_pre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm_join
  obtain ⟨hbound, hm_join⟩ := hm_join
  have hm_split : s.mem ⊨ (saveVtablesAt ikit ∗
      trustActive img ikit ist1 s.sp (encSubStackV kit ikit) x k ∗
      memRegion (s.sp + 0x470#64) 16 ∗
      memRegion (s.sp + 0x580#64) 48 ∗
      memRegion (s.sp + 0x990#64) 24) ∗ (F ∗ R) := by
    have hm' := saveVtablesAt_intro env.idVtables hfl hm_join
    dsimp only [R]
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm'
  have hx22' : s.readReg64 .x22 = s.sp + 0x8b8#64 := by rw [hsp]; exact hx22
  have hx25' : s.readReg64 .x25 = s.sp + 0x580#64 := by rw [hsp]; exact hx25
  have hpc_bd4 : s.pc = (trTrapProgAt img.base C abs).fnAddr encryptWithStoresName + 0xbd4#64 := by
    rw [hpc, savePC, encEntry_eq_fnAddr_trap env]
  rw [← h45_segExit_kitF_trap]
  refine save_to_d94_trap (R0 := R0) env haddr
    (fun s' hst' htr' =>
      ((hfs.of_steps hst').envOk_at (htr'.trans htr) fun hq => by
        obtain ⟨⟨hl, -⟩, ht, -⟩ := hq
        simp only [NoFsEv.append_iff, hl, ht, and_self]).2)
    hbound hpc_bd4 hrun hsp_al hx22' hx25' hpref0 hfl hsym hm_split ?_
  intro sm ans w0 w1 w2 w3 w4 w5 H hsteps_d94 hpcm hrunm hspm hspm_al hsaveRel htrm
    hx19m hx20m hx25m hx26m hx28m hx29m hvregsm hx27m hx21m hx23m hans hmm_act
  let R' : SepProp := encStoreExtra kit st0 ikit (ikit.saveUpdate ist1 x.rem.val k ans) x s0 ∗ R0
  have hmm : sm.mem ⊨ (trustBaseActive ikit.id_vt A img s.sp x k ∗
      memRegion (s.sp + 0x470#64) 16 ∗
      memRegion (s.sp + 0x580#64) 48 ∗
      (((s.sp + 0x990#64) ↦₆₄ w3) ∗
        ((s.sp + 0x998#64) ↦₆₄ w4) ∗
        ((s.sp + 0x9a0#64) ↦₆₄ w5)) ∗ H) ∗ (F ∗ R') := by
    have hmm1 : sm.mem ⊨
        (trustActive img ikit (ikit.saveUpdate ist1 x.rem.val k ans) s.sp (encSubStackV kit ikit) x k ∗
          kit.storeAt x.ssA st0) ∗
        ((memRegion (s.sp + 0x470#64) 16 ∗
          memRegion (s.sp + 0x580#64) 48 ∗
          (((s.sp + 0x990#64) ↦₆₄ w3) ∗
            ((s.sp + 0x998#64) ↦₆₄ w4) ∗
            ((s.sp + 0x9a0#64) ↦₆₄ w5)) ∗ H) ∗ F ∗ R0) := by
      dsimp only [R] at hmm_act
      exact Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hmm_act
    have hmm2 := Satisfies.mono (sepConj_mono_left
      (trustActive_split_extra kit st0 ikit (ikit.saveUpdate ist1 x.rem.val k ans) x k s0 s.sp hsp hbound)) hmm1
    dsimp only [R']
    exact Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hmm2
  have ⟨hflm, hsymm⟩ := callInv_steps hfl hsym hsteps_d94
  have hspm' : sm.sp = sp := hspm.trans hsp
  have htrm' : sm.trace = s0.trace ++
      (kit.loadEvs encRecord x.rem.val (.ok (some r)) ++
        (ikit.trustEvs x.rem.val k .sending (.ok true) ++
          ikit.saveEvs x.rem.val k ans)) := by
    rw [htrm, htr, List.append_assoc, List.append_assoc]
  rcases ans with ⟨⟨⟩⟩ | c
  · obtain ⟨rfl, hw1, rfl, rfl, hw4, hH⟩ := hans
    have hmm_emp : sm.mem ⊨ emp ∗
        (((trustBaseActive ikit.id_vt A img s.sp x k ∗
          memRegion (s.sp + 0x470#64) 16 ∗
          memRegion (s.sp + 0x580#64) 48 ∗
          (((s.sp + 0x990#64) ↦₆₄ 1#64) ∗
            ((s.sp + 0x998#64) ↦₆₄ w4) ∗
            ((s.sp + 0x9a0#64) ↦₆₄ w5)) ∗
          H) ∗ F) ∗ R') := by
      rw [emp_sepConj]
      exact Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hmm
    refine SegExit.of_sepWP_trap hmm_emp (step_d94_err_trap hpcm hrunm hx27m) ?_
    rintro s_err _ _ hsteps_err hpc_err hrun_err hm_err
      ⟨rfl, hsp_err, htr_err, hx19_err, hx21_err, hx23_err, hx26_err, hx27_err, hx28_err, hx29_err, hvregs_err⟩
    rw [emp_sepConj] at hm_err
    have ⟨hfl_err, hsym_err⟩ := callInv_steps hflm hsymm hsteps_err
    have hm_ro' : s_err.mem ⊨
        ((trustBaseActive ikit.id_vt A img s.sp x k ∗
          memRegion (s.sp + 0x470#64) 16 ∗
          memRegion (s.sp + 0x580#64) 48 ∗
          (((s.sp + 0x990#64) ↦₆₄ 1#64) ∗
            ((s.sp + 0x998#64) ↦₆₄ w4) ∗
            ((s.sp + 0x9a0#64) ↦₆₄ w5)) ∗
          H) ∗ F) ∗ R' :=
      Eq.mp (congrArg (s_err.mem ⊨ ·) (by ac_rfl)) hm_err
    have htail_ent :=
      Pf.SegSave.save_seam_mem_to_tail
        kit.ss_vt ikit.id_vt A ctl img x sess taken otr' pqCap' pqPtr' k m draws s0 s.sp hsp
        (((s.sp + 0x990#64) ↦₆₄ 1#64) ∗
          ((s.sp + 0x998#64) ↦₆₄ w4) ∗
          ((s.sp + 0x9a0#64) ↦₆₄ w5))
        (pollWith s.sp 0x990 [1#64, w4, w5])
        H
        (savePoll_merge_990 s.sp 1#64 w4 w5)
    have hm_tail := Satisfies.mono (sepConj_mono_left htail_ent) hm_ro'
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hm_tail
    obtain ⟨g, hm_tail⟩ := hm_tail
    have htm : Tails.TailModel (h45_kitF kit) st0 ikit ist0 C S uuidTryParse encRecord x
        (answersOfSaveErr r) (.error (.store ())) s0 s_err := by
      rw [h45_tailModel_kitF]
      exact StepsThroughEncrypt.tailModel_save_err (encRecord := encRecord) (s0 := s0) (s := s_err)
        h15 htrustRel hsaveRel (htr_err.trans htrm')
    have hdraws : x.draws S (answersOfSaveErr r) = draws :=
      StepsThroughEncrypt.draws_eq h15 (answersOfSaveErr r) rfl
    refine SegExit.of_false_trap
      (tailStoreHookErr_ok_trap env x R0 s0 s_err (answersOfSaveErr r) (.store ())
        0x800000000000001A#64 w1 10#64 1#64 w4 w5
        H cmScratch (Or.inr rfl)
        g (takenRecord sess taken) (some (pqCap', pqPtr', otr')) m 0xe28 0x990 (Or.inr (Or.inl rfl))
        htm (by subst hH hw1 hw4; exact speStaged_storeErr A img.base x.ret w5) ?_)
    refine ⟨by rw [hpc_err, encEntry_eq_fnAddr_trap env],
      ⟨hrun_err, hsp_err.trans hspm', hsp0_al,
      spAligned_of_sp_eq hspm_al hsp_err,
      by rw [hx29_err, hx29m, hx29], by rw [hx19_err, hx19m, hx19], hfl_err, hsym_err,
      by rw [hvregs_err, hvregsm, hvregs]⟩,
      ⟨by rw [hx26_err, hx26m, hx26], by rw [hx28_err, hx28m, hx28],
       by rw [hx27_err, hx27m], by rw [hx21_err, hx21m], by rw [hx23_err, hx23m]⟩,
      hstk, ?_⟩
    rw [hdraws, (StepsThroughEncrypt.model_save_err h15)]
    rw [hsp] at hm_tail
    dsimp only [sp, draws, ist1, SessionStoreSpec.storeFinal,
      StoreKit.Identity.IdentityStoreSpec.idFinal, answersOfSaveErr, R'] at hm_tail ⊢
    exact Eq.mp (congrArg (s_err.mem ⊨ ·) (by ac_rfl)) hm_tail
  · obtain ⟨rfl, _, rfl⟩ := hans
    have hmm_emp : sm.mem ⊨ emp ∗
        (((trustBaseActive ikit.id_vt A img s.sp x k ∗
          memRegion (s.sp + 0x470#64) 16 ∗
          memRegion (s.sp + 0x580#64) 48 ∗
          (((s.sp + 0x990#64) ↦₆₄ w3) ∗
            ((s.sp + 0x998#64) ↦₆₄ w4) ∗
            ((s.sp + 0x9a0#64) ↦₆₄ w5))) ∗ F) ∗ R') := by
      simp only [sepConj_emp, emp_sepConj] at hmm ⊢
      exact Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hmm
    refine SegExit.of_sepWP_trap hmm_emp (step_d94_ok_trap hpcm hrunm hx27m) ?_
    rintro s_ok _ _ hsteps_ok hpc_ok hrun_ok hm_ok
      ⟨rfl, hsp_ok, htr_ok, hx19_ok, hx20_ok, hx25_ok, hx26_ok, hx28_ok, hx29_ok, hvregs_ok⟩
    rw [emp_sepConj] at hm_ok
    have ⟨hfl_ok, hsym_ok⟩ := callInv_steps hflm hsymm hsteps_ok
    have hm_ok_990 : s_ok.mem ⊨
        (((s.sp + 0x990#64) ↦₆₄ w3) ∗
          ((s.sp + 0x990#64 + 8#64) ↦₆₄ w4) ∗
          ((s.sp + 0x990#64 + 16#64) ↦₆₄ w5)) ∗
        ((trustBaseActive ikit.id_vt A img s.sp x k ∗
          memRegion (s.sp + 0x470#64) 16 ∗
          memRegion (s.sp + 0x580#64) 48) ∗ F ∗ R') := by
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact Eq.mp (congrArg (s_ok.mem ⊨ ·) (by ac_rfl)) hm_ok
    have hm_ok_fold := Satisfies.mono (sepConj_mono_left
      (words3_entails_memRegion24 (s.sp + 0x990#64) w3 w4 w5)) hm_ok_990
    have hm_ok_seam : s_ok.mem ⊨
        ((trustBaseActive ikit.id_vt A img s.sp x k ∗
          memRegion (s.sp + 0x470#64) 16 ∗
          memRegion (s.sp + 0x580#64) 48 ∗
          memRegion (s.sp + 0x990#64) 24) ∗
          Pf.SegSave.savePassive kit.ss_vt ikit.id_vt A img.base x sess taken otr' pqCap' pqPtr' m draws s0) ∗ R' := by
      dsimp only [F] at hm_ok_fold
      exact Eq.mp (congrArg (s_ok.mem ⊨ ·) (by ac_rfl)) hm_ok_fold
    rw [← Pf.SegSave.save_seam_mem_split kit.ss_vt ikit.id_vt A ctl img x sess taken otr' pqCap' pqPtr' k m draws s0 s.sp hsp] at hm_ok_seam
    rw [hsp] at hm_ok_seam
    intro _
    refine ⟨s_ok, Steps.refl s_ok, Or.inl ⟨c, ⟨h15, htrustRel, hsaveRel⟩,
      by rw [hpc_ok, applyPC, encEntry_eq_fnAddr_trap env],
      ⟨hrun_ok, hsp_ok.trans hspm', hsp0_al, spAligned_of_sp_eq hspm_al hsp_ok,
        by rw [hx29_ok, hx29m, hx29], by rw [hx19_ok, hx19m, hx19], hfl_ok, hsym_ok,
        by rw [hvregs_ok, hvregsm, hvregs]⟩,
      by rw [htr_ok, htrm']; simp only [List.append_assoc],
      ⟨by rw [hx20_ok, hx20m, hx20],
       by rw [hx25_ok, hx25m, hx25], by rw [hx26_ok, hx26m, hx26],
       by rw [hx28_ok, hx28m, hx28]⟩,
      hpt, hrest, hloc, hnow, hstk, ?_⟩⟩
    dsimp only [sp, draws, ist1, R'] at hm_ok_seam ⊢
    exact Eq.mp (congrArg (s_ok.mem ⊨ ·) (by ac_rfl)) hm_ok_seam

end SegSave

section SegLoad
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit.Pf.RecordMove
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails
open CryptoVerification.LibsignalSession

private theorem h45_encSubStackV_kitL {img : Obj.Image} {A : RustAlloc}
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base) :
    encSubStackV (h45_kitL kit) ikit = encSubStackV kit ikit := rfl

private theorem h45_loadVtablesAt_kitL {img : Obj.Image} {A : RustAlloc}
    (kit : SessionStoreSpec A img.base) :
    loadVtablesAt (h45_kitL kit) = loadVtablesAt kit := rfl

private theorem h45_segExit_mono_trap {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {C : Crypto} {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {x : WithStoresEncGhost} {R : SepProp} {s0 s : State} {p q : State → Prop}
    (h : SegExit_trap kit st0 ikit ist0 C ctl parse S encRecord abs x R s0 s p)
    (hpq : ∀ sf, p sf → q sf) :
    SegExit_trap kit st0 ikit ist0 C ctl parse S encRecord abs x R s0 s q := by
  intro hL
  obtain ⟨sf, hst, hp | hout⟩ := h hL
  · exact ⟨sf, hst, Or.inl (hpq sf hp)⟩
  · exact ⟨sf, hst, Or.inr hout⟩

private theorem h45_curStateV_of_false {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {img : Obj.Image} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {R : SepProp} {s0 s' : State}
    (h : ∃ r g sess, CurStateV (h45_kitF kit) st0 ikit ist0 (fun _ => False) ctl encRecord x r g sess R s0 s') :
    ∃ r g sess, CurStateV kit st0 ikit ist0 Scope ctl encRecord x r g sess R s0 s' := by
  rcases h with ⟨r, _, _, _, ⟨hfalse, _⟩, _⟩
  exact False.elim hfalse

private theorem h45_curStateV_of_scopeNone {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {img : Obj.Image} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {R : SepProp} {s0 s' : State}
    (h : ∃ r g sess, CurStateV (h45_kitF kit) st0 ikit ist0 (h45_ScopeNone Scope) ctl encRecord x r g sess R s0 s') :
    ∃ r g sess, CurStateV kit st0 ikit ist0 Scope ctl encRecord x r g sess R s0 s' := by
  rcases h with ⟨r, g, sess, hcur, ⟨⟨hscope, _⟩, hl⟩, hrest⟩
  exact ⟨r, g, sess, hcur, ⟨hscope, hl⟩, hrest⟩

private theorem h45_loadOutRes_some_scopeNone {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (A : RustAlloc) (b w0 w1 w2 w3 w4 w5 w6 : BitVec 64) (tail : List (BitVec 8))
    {r : SessionRecord (List (BitVec 8))} (hcur : r.currentSession = none) :
    LoadOutRes Scope A b (.ok (some r)) w0 w1 w2 w3 w4 w5 w6 tail ⊢
      LoadOutRes (h45_ScopeNone Scope) A b (.ok (some r)) w0 w1 w2 w3 w4 w5 w6 tail := by
  rw [loadOutRes_some_eq, loadOutRes_some_eq]
  apply Entails.sepExists_elim
  intro g
  refine Entails.trans ?_ (Entails.sepExists_intro g)
  refine Entails.pure_left fun ⟨hscope, hrest⟩ => ?_
  exact Entails.pure_right ⟨⟨hscope, hcur⟩, hrest⟩ (Entails.refl _)

private theorem h45_segLoad_to_dispatch_trap {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (hEnv : EncEnvT_trap kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (R : SepProp) (s0 : State)
    (hfs : EncFsCtx_trap kit ikit C abs s0 s0)
    (hpc0 : s0.pc = encEntry img) (hrun0 : s0.status = .Running) (hal0 : s0.spAligned = true)
    (hm0 : s0.mem ⊨ (withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).pre x s0 ∗ R)
    (hcont : ∀ (s : State) (sp : BitVec 64)
      (ans : Except Unit (Option (SessionRecord (List (BitVec 8)))))
      (w0 w1 w2 w3 w4 w5 w6 v50 : BitVec 64) (tail : List (BitVec 8)),
      sp = s0.sp - 0xbe0#64 →
      s.pc = (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x160#64 →
      encMidMeta img x s0 s →
      x.ptext.length < 2 ^ 32 ∧ x.rest.length < 2 ^ 63 ∧ x.locA ≠ 0#64 ∧
        x.now.tvNsec.toNat < 10 ^ 9 ∧ withStoresEncStackV kit ikit ≤ s0.sp.toNat →
      w0 ≠ 0xFFFFFFFFFFFFFFFD#64 → tail.length = 312 →
      kit.loadRel st0 x.rem.val ans →
      s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val ans →
      s.readReg64 .x24 = w0 → s.readReg64 .x27 = w1 →
      s.readReg64 .x21 = w2 → s.readReg64 .x23 = w3 →
      s.readReg64 .x25 = sp + 0x580#64 →
      s.readReg64 .x26 = sp + 0x9d0#64 →
      s.readReg64 .x28 = sp + 0x4a0#64 →
      s.pstate = addsPState64 w0 2#64 →
      (s.mem ⊨ (memRegion (sp + 0x46a#64) 0x116 ∗
        memRegion (sp + 0x580#64) 368 ∗
        ((sp + 0x6f8#64) ↦ₛ tail) ∗
        ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗
        ((sp + 0x840#64) ↦₆₄ w6) ∗
        LoadOutRes Scope A img.base ans w0 w1 w2 w3 w4 w5 w6 tail ∗
        protocolAddressAt A x.rem x.remA ∗
        A.pool ∗ stackAt sp encSubStack ∗ loadVtablesAt kit ∗
        Pf.SegLoad.dispatchFrame kit st0 ikit ist0 ctl x s0 v50) ∗ R) →
      SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s
        (fun s' => ∃ r g sess,
          CurStateV kit st0 ikit ist0 Scope ctl encRecord x r g sess R s0 s')) :
    SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s0
      (fun s' => ∃ r g sess,
        CurStateV kit st0 ikit ist0 Scope ctl encRecord x r g sess R s0 s') := by
  let envL := h45_envL hEnv
  dsimp only [withStoresEncSpecV, Spec.inImage] at hm0
  rw [Pf.SegLoad.tapeAt_eq_pure_sep_tapeAfter_zero] at hm0
  have hpull0 :
      (⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
        (⌜s0.readReg64 .x0 = x.ptA ∧ (s0.readReg64 .x1).toNat = x.ptext.length ∧
          x.ptext.length < 2 ^ 32 ∧ s0.readReg64 .x2 = x.remA ∧ s0.readReg64 .x3 = x.locA ∧
          x.locA ≠ 0#64 ∧
          s0.readReg64 .x4 = x.ssA ∧ s0.readReg64 .x5 = kit.ss_vt ∧
          s0.readReg64 .x6 = x.idA ∧ s0.readReg64 .x7 = ikit.id_vt ∧
          x.now.tvNsec.toNat < 10 ^ 9 ∧ s0.readReg64 .x8 = x.ret ∧
          withStoresEncStackV kit ikit ≤ s0.sp.toNat ∧
          kit.addrOk x.rem.val ∧ ikit.addrOk x.rem.val⌝ ∗
        kit.storeAt x.ssA st0 ∗ ikit.identityAt x.idA ist0 ∗
        nowAt s0.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗ memRegion x.ret 248 ∗
        (⌜x.rest.length < 2 ^ 63⌝ ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest 0) ∗
        logOff img ∗ stackAt s0.sp (withStoresEncStackV kit ikit) ∗ A.pool)) ∗ R =
      ⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
      (⌜s0.readReg64 .x0 = x.ptA ∧ (s0.readReg64 .x1).toNat = x.ptext.length ∧
        x.ptext.length < 2 ^ 32 ∧ s0.readReg64 .x2 = x.remA ∧ s0.readReg64 .x3 = x.locA ∧
        x.locA ≠ 0#64 ∧
        s0.readReg64 .x4 = x.ssA ∧ s0.readReg64 .x5 = kit.ss_vt ∧
        s0.readReg64 .x6 = x.idA ∧ s0.readReg64 .x7 = ikit.id_vt ∧
        x.now.tvNsec.toNat < 10 ^ 9 ∧ s0.readReg64 .x8 = x.ret ∧
        withStoresEncStackV kit ikit ≤ s0.sp.toNat ∧
        kit.addrOk x.rem.val ∧ ikit.addrOk x.rem.val⌝ ∗
      (⌜x.rest.length < 2 ^ 63⌝ ∗
      ((nowAt s0.sp x.now ∗ stackAt s0.sp (withStoresEncStackV kit ikit) ∗
        (protocolAddressAt A x.rem x.remA ∗ kit.storeAt x.ssA st0 ∗ A.pool ∗
          ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.loc x.locA ∗ memRegion x.ret 248 ∗
            CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest 0 ∗ logOff img ∗ ikit.identityAt x.idA ist0))) ∗ R))) := by ac_rfl
  rw [hpull0] at hm0
  obtain ⟨hF0, hm0⟩ := (satisfies_pure_sepConj _ _ _).mp hm0
  obtain ⟨⟨hx0, hx1_nat, hpt_lt, hx2, hx3, hloc_ne, hx4, hx5, hx6, hx7, hnsec, hx8, hsp_le, haddr_ss, _haddr_id⟩, hm0⟩ :=
    (satisfies_pure_sepConj _ _ _).mp hm0
  obtain ⟨hrest_lt, hm0⟩ := (satisfies_pure_sepConj _ _ _).mp hm0
  have hsub := encSubStackV_le_two_pow_64 kit ikit hsp_le
  have hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.ptext.length := by
    rw [← hx1_nat, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hm_vt := loadVtablesAt_intro hEnv.vtables hF0.1 hm0
  have hpull_vt :
      loadVtablesAt kit ∗
        ((nowAt s0.sp x.now ∗ stackAt s0.sp (withStoresEncStackV kit ikit) ∗
          (protocolAddressAt A x.rem x.remA ∗ kit.storeAt x.ssA st0 ∗ A.pool ∗
            ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.loc x.locA ∗ memRegion x.ret 248 ∗
              CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest 0 ∗ logOff img ∗ ikit.identityAt x.idA ist0))) ∗ R) =
      (nowAt s0.sp x.now ∗ stackAt s0.sp (withStoresEncStackV kit ikit) ∗ loadVtablesAt kit ∗
        (protocolAddressAt A x.rem x.remA ∗ kit.storeAt x.ssA st0 ∗ A.pool ∗
          ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.loc x.locA ∗ memRegion x.ret 248 ∗
            CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest 0 ∗ logOff img ∗ ikit.identityAt x.idA ist0))) ∗ R := by ac_rfl
  rw [hpull_vt] at hm_vt
  rw [Pf.SegLoad.encEntry_eq_fnAddr_trap envL] at hpc0
  have hfsAt : FsAt kit.envOk (kit.Quiet ∧ ikit.Quiet) (trTrapProgAt img.base C abs) s0 :=
    (hfs.fsAt (evs := []) (List.append_nil _).symm (fun _ => NoFsEv.nil)).mono (fun _ h => h.1) id
  refine Pf.SegLoad.segExit_of_sepWPp_trap
    (target := (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x160#64) hm_vt ?_
  have he0 := Pf.SegLoad.segLoad_shim_wp_trap envL x s0
    (protocolAddressAt A x.rem x.remA ∗ kit.storeAt x.ssA st0 ∗ A.pool ∗
      ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.loc x.locA ∗ memRegion x.ret 248 ∗
        CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest 0 ∗ logOff img ∗ ikit.identityAt x.idA ist0))
    hsp_le rfl hpc0 hrun0 hal0 hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8
  refine messageEncrypt_of_sepWP_frozen ⟨hF0.1, hF0.2⟩ (SepWP.mono he0 ?_)
  intro sm P_m hpcm hrunm hpostm hFm
  rcases hpostm with ⟨v50, v470, v478, waker0, waker1, v830, v838, v840,
    hspm, halm, hfsm, htrm, hx0m, hx1m, hx19m, hx29m, hvregsm, hx30m, rfl⟩
  refine messageEncrypt_call_panic_then_sepWPp_frozen
    (subroutine_ok_withStepsPost_inImage hEnv.kitOk.loadShim)
    (x := ⟨x.ssA, x.remA⟩)
    (F := Pf.SegLoad.shimFrame kit ikit ist0 ctl x s0 v50 ∗
      memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - kit.loadShimStack) ∗
      memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 6 ∗
      ((s0.sp - 0xbe0#64 + 0x470#64) ↦₆₄ v470) ∗ ((s0.sp - 0xbe0#64 + 0x478#64) ↦₆₄ v478) ∗
      ((s0.sp - 0xbe0#64 + 0x480#64) ↦₆₄ waker0) ∗ ((s0.sp - 0xbe0#64 + 0x488#64) ↦₆₄ waker1) ∗
      ((s0.sp - 0xbe0#64 + 0x490#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 0xbe0#64 + 0x498#64) 0xe8 ∗
      memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
      memRegion (s0.sp - 0xbe0#64 + 0x6f8#64) 312 ∗
      ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ v830) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ v838) ∗
      ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ v840) ∗
      protocolAddressAt A x.rem x.remA ∗
      kit.storeAt x.ssA st0 ∗
      loadVtablesAt kit)
    hFm hpcm hrunm halm hx30m ?_ ?_ (fun _ _ => rfl) ?_
  · intro R' hm'
    refine inImage_pre_intro hFm.1 hFm.2 ?_
    dsimp only [kitLoadShimSpec, Pf.SegLoad.shimFrame] at hm' ⊢
    refine Satisfies.mono ?_ hm'
    rw [h45_encSubStackV_kitL kit ikit, h45_loadVtablesAt_kitL kit]
    have hpre_eq :
        (nowAt s0.sp x.now ∗
          encSavedRegs s0.sp s0 ∗
          stackAt sm.sp kit.loadShimStack ∗
          memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - kit.loadShimStack) ∗
          memRegion (s0.sp - 0xbe0#64) 0x50 ∗
          ((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ v50) ∗
          encSpillsInit kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
          ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x358 ∗
          ((s0.sp - 0xbe0#64 + 0x468#64) ↦₈ 0#8) ∗ ((s0.sp - 0xbe0#64 + 0x469#64) ↦₈ 0#8) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 6 ∗
          ((s0.sp - 0xbe0#64 + 0x470#64) ↦₆₄ v470) ∗ ((s0.sp - 0xbe0#64 + 0x478#64) ↦₆₄ v478) ∗
          ((s0.sp - 0xbe0#64 + 0x480#64) ↦₆₄ waker0) ∗ ((s0.sp - 0xbe0#64 + 0x488#64) ↦₆₄ waker1) ∗
          ((s0.sp - 0xbe0#64 + 0x490#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 0xbe0#64 + 0x498#64) 0xe8 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x6f8#64) 312 ∗
          ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ v830) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ v838) ∗
          ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ v840) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
          loadVtablesAt kit ∗
          (protocolAddressAt A x.rem x.remA ∗ kit.storeAt x.ssA st0 ∗ A.pool ∗
            ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.loc x.locA ∗ memRegion x.ret 248 ∗
              CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest 0 ∗ logOff img ∗ ikit.identityAt x.idA ist0))) ∗ R' =
        (A.pool ∗ stackAt sm.sp kit.loadShimStack) ∗
        (((nowAt s0.sp x.now ∗
          encSavedRegs s0.sp s0 ∗
          memRegion (s0.sp - 0xbe0#64) 0x50 ∗
          ((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ v50) ∗
          encSpillsInit kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
          ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x358 ∗
          ((s0.sp - 0xbe0#64 + 0x468#64) ↦₈ 0#8) ∗ ((s0.sp - 0xbe0#64 + 0x469#64) ↦₈ 0#8) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
          (x.ptA ↦ₛ x.ptext) ∗
          protocolAddressAt A x.loc x.locA ∗
          memRegion x.ret 248 ∗
          CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest 0 ∗
          logOff img ∗
          ikit.identityAt x.idA ist0) ∗
          memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - kit.loadShimStack) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 6 ∗
          ((s0.sp - 0xbe0#64 + 0x470#64) ↦₆₄ v470) ∗ ((s0.sp - 0xbe0#64 + 0x478#64) ↦₆₄ v478) ∗
          ((s0.sp - 0xbe0#64 + 0x480#64) ↦₆₄ waker0) ∗ ((s0.sp - 0xbe0#64 + 0x488#64) ↦₆₄ waker1) ∗
          ((s0.sp - 0xbe0#64 + 0x490#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 0xbe0#64 + 0x498#64) 0xe8 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x6f8#64) 312 ∗
          ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ v830) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ v838) ∗
          ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ v840) ∗
          protocolAddressAt A x.rem x.remA ∗
          kit.storeAt x.ssA st0 ∗
          loadVtablesAt kit) ∗ R') := by ac_rfl
    rw [hpre_eq]
    apply sepConj_mono_left
    exact Entails.pure_right (And.intro hx0m hx1m) (Entails.refl _)
  · intro sf
    dsimp only [kitLoadShimSpec]
    exact Pf.SegLoad.alloc_onPanic_entails (by rw [htrm])
  · intro sf1 hpc1 hrun1 hsp1 hcs1 hF1
    rcases hcs1 with ⟨hcs19, _, _, _, _, _, _, _, _, _, hcs29, hcsv1⟩
    dsimp only [Spec.inImage, withStepsPost, kitLoadShimSpec]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hsteps1 => ?_
    refine SepWPp.pure_elim fun ⟨hx1_1, hbox_ne, _hbox_align, htr1⟩ => ?_
    have henv1 : kit.envOk sf1.fs.files :=
      (hfsAt.of_call hsteps1 (congrArg FsState.files hfsm) htr1).envOk_here
    set box := sf1.readReg64 .x0
    have hsp1' : sf1.sp = s0.sp - 0xbe0#64 := by rw [hsp1, hspm]
    have hal1 : sf1.spAligned = true := by rw [State.spAligned, hsp1, ← State.spAligned]; exact halm
    have hpre_poll := Pf.SegLoad.segLoad_pre_poll_wp_trap envL
      (s := sf1) (sp := s0.sp - 0xbe0#64) (box := box)
      (v470 := v470) (v478 := v478)
      (F := A.live box kit.loadBoxSize 8 ∗ kit.loadBoxAt box x.ssA x.remA 0#8 ∗
        A.pool ∗
        Pf.SegLoad.shimFrame kit ikit ist0 ctl x s0 v50 ∗
        memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 6 ∗
        ((s0.sp - 0xbe0#64 + 0x480#64) ↦₆₄ waker0) ∗ ((s0.sp - 0xbe0#64 + 0x488#64) ↦₆₄ waker1) ∗
        ((s0.sp - 0xbe0#64 + 0x490#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 0xbe0#64 + 0x498#64) 0xe8 ∗
        memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
        memRegion (s0.sp - 0xbe0#64 + 0x6f8#64) 312 ∗
        ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ v830) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ v838) ∗
        ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ v840) ∗
        protocolAddressAt A x.rem x.remA ∗
        kit.storeAt x.ssA st0)
      hsub hpc1 hrun1 hsp1' hal1 rfl hx1_1 hbox_ne
    have hpre_poll_eq :
        A.live box kit.loadBoxSize 8 ∗ kit.loadBoxAt box x.ssA x.remA 0#8 ∗
          A.pool ∗ stackAt sm.sp kit.loadShimStack ∗
          Pf.SegLoad.shimFrame kit ikit ist0 ctl x s0 v50 ∗
          memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - kit.loadShimStack) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 6 ∗
          ((s0.sp - 0xbe0#64 + 0x470#64) ↦₆₄ v470) ∗ ((s0.sp - 0xbe0#64 + 0x478#64) ↦₆₄ v478) ∗
          ((s0.sp - 0xbe0#64 + 0x480#64) ↦₆₄ waker0) ∗ ((s0.sp - 0xbe0#64 + 0x488#64) ↦₆₄ waker1) ∗
          ((s0.sp - 0xbe0#64 + 0x490#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 0xbe0#64 + 0x498#64) 0xe8 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x6f8#64) 312 ∗
          ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ v830) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ v838) ∗
          ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ v840) ∗
          protocolAddressAt A x.rem x.remA ∗
          kit.storeAt x.ssA st0 ∗
          loadVtablesAt kit =
        ((s0.sp - 0xbe0#64 + 0x470#64) ↦₆₄ v470) ∗ ((s0.sp - 0xbe0#64 + 0x478#64) ↦₆₄ v478) ∗
          stackAt sf1.sp kit.loadShimStack ∗
          memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV (h45_kitL kit) ikit)) (encSubStackV (h45_kitL kit) ikit - kit.loadShimStack) ∗
          loadVtablesAt (h45_kitL kit) ∗
          (A.live box kit.loadBoxSize 8 ∗ kit.loadBoxAt box x.ssA x.remA 0#8 ∗
            A.pool ∗
            Pf.SegLoad.shimFrame kit ikit ist0 ctl x s0 v50 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 6 ∗
            ((s0.sp - 0xbe0#64 + 0x480#64) ↦₆₄ waker0) ∗ ((s0.sp - 0xbe0#64 + 0x488#64) ↦₆₄ waker1) ∗
            ((s0.sp - 0xbe0#64 + 0x490#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 0xbe0#64 + 0x498#64) 0xe8 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x6f8#64) 312 ∗
            ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ v830) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ v838) ∗
            ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ v840) ∗
            protocolAddressAt A x.rem x.remA ∗
            kit.storeAt x.ssA st0) := by
      rw [hsp1, h45_encSubStackV_kitL kit ikit, h45_loadVtablesAt_kitL kit]
      ac_rfl
    rw [hpre_poll_eq]
    refine messageEncrypt_of_sepWP_frozen hF1 (SepWP.mono hpre_poll ?_)
    intro sm2 P_m2 hpcm2 hrunm2 hpostm2 hFm2
    rcases hpostm2 with ⟨hspm2, halm2, hfsm2, htrm2, hx0m2, hx8m2, hx20m2, hx19m2, hx29m2, hvregsm2, hx30m2, rfl⟩
    refine messageEncrypt_call_panic_then_wp_frozen hEnv.kitOk.loadPoll
      (x := (⟨box, s0.sp - 0xbe0#64 + 0x580#64, x.remA, x.rem⟩, x.ssA, st0))
      (F := ((s0.sp - 0xbe0#64 + 0x470#64) ↦₆₄ box) ∗
        ((s0.sp - 0xbe0#64 + 0x478#64) ↦₆₄ (img.base + kit.loadFutVtOff)) ∗
        memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - kit.loadPollStack) ∗
        loadVtablesAt kit ∗
        A.live box kit.loadBoxSize 8 ∗
        Pf.SegLoad.shimFrame kit ikit ist0 ctl x s0 v50 ∗
        memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 6 ∗
        ((s0.sp - 0xbe0#64 + 0x480#64) ↦₆₄ waker0) ∗ ((s0.sp - 0xbe0#64 + 0x488#64) ↦₆₄ waker1) ∗
        ((s0.sp - 0xbe0#64 + 0x490#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 0xbe0#64 + 0x498#64) 0xe8 ∗
        memRegion (s0.sp - 0xbe0#64 + 0x6f8#64) 312 ∗
        ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ v830) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ v838) ∗
        ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ v840))
      hFm2 hpcm2 hrunm2 halm2 hx30m2 ?_ ?_ (fun _ _ => rfl) ?_
    · intro R' hm'
      refine withEnvPre_pre_intro (hfsm2 ▸ henv1) ?_
      dsimp only [kitLoadPollSpecS] at hm' ⊢
      refine Satisfies.mono ?_ hm'
      rw [hspm2, h45_encSubStackV_kitL kit ikit, h45_loadVtablesAt_kitL kit]
      have hperm_p :
          (((s0.sp - 0xbe0#64 + 0x470#64) ↦₆₄ box) ∗
            ((s0.sp - 0xbe0#64 + 0x478#64) ↦₆₄ (img.base + kit.loadFutVtOff)) ∗
            memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - kit.loadPollStack) ∗
            stackAt (s0.sp - 0xbe0#64) kit.loadPollStack ∗
            loadVtablesAt kit ∗
            (A.live box kit.loadBoxSize 8 ∗ kit.loadBoxAt box x.ssA x.remA 0#8 ∗
              A.pool ∗
              Pf.SegLoad.shimFrame kit ikit ist0 ctl x s0 v50 ∗
              memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 6 ∗
              ((s0.sp - 0xbe0#64 + 0x480#64) ↦₆₄ waker0) ∗ ((s0.sp - 0xbe0#64 + 0x488#64) ↦₆₄ waker1) ∗
              ((s0.sp - 0xbe0#64 + 0x490#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 0xbe0#64 + 0x498#64) 0xe8 ∗
              memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
              memRegion (s0.sp - 0xbe0#64 + 0x6f8#64) 312 ∗
              ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ v830) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ v838) ∗
              ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ v840) ∗
              protocolAddressAt A x.rem x.remA ∗
              kit.storeAt x.ssA st0)) ∗ R' =
          (kit.loadBoxAt box x.ssA x.remA 0#8 ∗ kit.storeAt x.ssA st0 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
            protocolAddressAt A x.rem x.remA ∗ A.pool ∗
            stackAt (s0.sp - 0xbe0#64) kit.loadPollStack) ∗
          ((((s0.sp - 0xbe0#64 + 0x470#64) ↦₆₄ box) ∗
            ((s0.sp - 0xbe0#64 + 0x478#64) ↦₆₄ (img.base + kit.loadFutVtOff)) ∗
            memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - kit.loadPollStack) ∗
            loadVtablesAt kit ∗
            A.live box kit.loadBoxSize 8 ∗
            Pf.SegLoad.shimFrame kit ikit ist0 ctl x s0 v50 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 6 ∗
            ((s0.sp - 0xbe0#64 + 0x480#64) ↦₆₄ waker0) ∗ ((s0.sp - 0xbe0#64 + 0x488#64) ↦₆₄ waker1) ∗
            ((s0.sp - 0xbe0#64 + 0x490#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 0xbe0#64 + 0x498#64) 0xe8 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x6f8#64) 312 ∗
            ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ v830) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ v838) ∗
            ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ v840)) ∗ R') := by ac_rfl
      rw [hperm_p]
      apply sepConj_mono_left
      exact Entails.pure_right ⟨hFm2.1, hFm2.2, hx0m2, hx8m2, haddr_ss⟩ (Entails.refl _)
    · intro sf
      dsimp only [kitLoadPollSpecSE, withEnvPre, kitLoadPollSpecS]
      exact Pf.SegLoad.alloc_onPanic_entails (by rw [htrm2, htr1, htrm])
    · intro sf2 hpc2 hrun2 hsp2 hcs2
      rcases hcs2 with ⟨hcs2_19, hcs2_20, _, _, _, _, _, _, _, _, hcs2_29, hcs2_v⟩
      dsimp only [kitLoadPollSpecSE, withEnvPre, kitLoadPollSpecS]
      wp_simp_pre [sepExists_sepConj_left, sepConj_assoc]
      apply SepWP.exists_elim; intro ans
      apply SepWP.pure_elim; rintro ⟨hl, htr2⟩
      have hsp2' : sf2.sp = s0.sp - 0xbe0#64 := by rw [hsp2, hspm2]
      have hal2 : sf2.spAligned = true := by rw [State.spAligned, hsp2, ← State.spAligned]; exact halm2
      have hx20_2 : sf2.readReg64 .x20 = s0.sp - 0xbe0#64 + 0x580#64 := by rw [hcs2_20, hx20m2]
      have he1 := Pf.SegLoad.segLoad_poll_wp_trap envL
        (s := sf2) (sp := s0.sp - 0xbe0#64) (box := box) (self := x.ssA) (remA := x.remA)
        (waker0 := waker0) (waker1 := waker1) (v830 := v830) (v838 := v838) (v840 := v840)
        (ans := ans)
        (F := protocolAddressAt A x.rem x.remA ∗ kit.storeAt x.ssA st0 ∗ Pf.SegLoad.shimFrame kit ikit ist0 ctl x s0 v50)
        hsub hpc2 hrun2 hsp2' hal2 hx20_2
      refine sepWP_conseq_pc_run (by rw [hspm2, h45_encSubStackV_kitL kit ikit, h45_loadVtablesAt_kitL kit]; ac_rfl) he1 ?_
      intro sf P_f hpcf hrunf hpostf hFf hm_f
      rcases hpostf with ⟨w0, w1, w2, w3, w4, w5, w6, tail,
        hw0_ne, htail, hspf, half, htrf, hx19f, hx29f, hvregsf,
        hx24f, hx27f, hx21f, hx23f, hx25f, hx26f, hx28f, hpsf, rfl⟩
      have hm_f' : sf.mem ⊨ (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
          ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
          ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
          ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
          LoadOutRes Scope A img.base ans w0 w1 w2 w3 w4 w5 w6 tail ∗
          protocolAddressAt A x.rem x.remA ∗
          A.pool ∗ stackAt (s0.sp - 0xbe0#64) encSubStack ∗ loadVtablesAt kit ∗
          Pf.SegLoad.dispatchFrame kit st0 ikit ist0 ctl x s0 v50) ∗ R := by
        refine Satisfies.mono ?_ hm_f
        refine sepConj_mono_left ?_
        rw [h45_encSubStackV_kitL kit ikit, h45_loadVtablesAt_kitL kit]
        have hsp_split := encSubStack_split_extra kit st0 ikit ist0 x s0 hsp_le
        dsimp only [Pf.SegLoad.shimFrame, Pf.SegLoad.dispatchFrame]
        have hperm :
            memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
              memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
              ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
              ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
              ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
              LoadOutRes Scope A img.base ans w0 w1 w2 w3 w4 w5 w6 tail ∗
              A.pool ∗ stackAt (s0.sp - 0xbe0#64) (encSubStackV kit ikit) ∗ loadVtablesAt kit ∗
              (protocolAddressAt A x.rem x.remA ∗
                kit.storeAt x.ssA st0 ∗
                (nowAt s0.sp x.now ∗
                  encSavedRegs s0.sp s0 ∗
                  memRegion (s0.sp - 0xbe0#64) 0x50 ∗
                  ((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ v50) ∗
                  encSpillsInit kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
                  ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
                  memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x358 ∗
                  ((s0.sp - 0xbe0#64 + 0x468#64) ↦₈ 0#8) ∗ ((s0.sp - 0xbe0#64 + 0x469#64) ↦₈ 0#8) ∗
                  memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗
                  memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
                  (x.ptA ↦ₛ x.ptext) ∗
                  protocolAddressAt A x.loc x.locA ∗
                  memRegion x.ret 248 ∗
                  CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest 0 ∗
                  logOff img ∗
                  ikit.identityAt x.idA ist0)) =
            (kit.storeAt x.ssA st0 ∗ ikit.identityAt x.idA ist0 ∗
              stackAt (s0.sp - 0xbe0#64) (encSubStackV kit ikit)) ∗
            (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
              memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
              ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
              ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
              ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
              LoadOutRes Scope A img.base ans w0 w1 w2 w3 w4 w5 w6 tail ∗
              protocolAddressAt A x.rem x.remA ∗
              A.pool ∗ loadVtablesAt kit ∗
              nowAt s0.sp x.now ∗
              encSavedRegs s0.sp s0 ∗
              memRegion (s0.sp - 0xbe0#64) 0x50 ∗
              ((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ v50) ∗
              encSpillsInit kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
              ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
              memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x358 ∗
              ((s0.sp - 0xbe0#64 + 0x468#64) ↦₈ 0#8) ∗ ((s0.sp - 0xbe0#64 + 0x469#64) ↦₈ 0#8) ∗
              memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗
              memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
              (x.ptA ↦ₛ x.ptext) ∗
              protocolAddressAt A x.loc x.locA ∗
              memRegion x.ret 248 ∗
              CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest 0 ∗
              logOff img) := by ac_rfl
        rw [hperm]
        refine Entails.trans (sepConj_mono_left hsp_split) ?_
        exact Entails.of_eq (by ac_rfl)
      refine hcont sf (s0.sp - 0xbe0#64) ans w0 w1 w2 w3 w4 w5 w6 v50 tail rfl
        hpcf ⟨hrunf, hspf, hal0, half, ?_, ?_, hFf.1, hFf.2, ?_⟩
        ⟨hpt_lt, hrest_lt, hloc_ne, hnsec, hsp_le⟩
        hw0_ne htail hl ?_ hx24f hx27f hx21f hx23f hx25f hx26f hx28f hpsf hm_f'
      · rw [hx29f, hcs2_29, hx29m2, hcs29, hx29m]
      · rw [hx19f, hcs2_19, hx19m2, hcs19, hx19m]
      · rw [hvregsf, hcs2_v, hvregsm2, hcsv1, hvregsm]
      · rw [htrf, htr2, htrm2, htr1, htrm]

theorem h45_segLoad_okVT_trap {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (hEnv : EncEnvT_trap kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (R : SepProp) (s0 : State)
    (hfs : EncFsCtx_trap kit ikit C abs s0 s0)
    (hpc0 : s0.pc = encEntry img) (hrun0 : s0.status = .Running) (hal0 : s0.spAligned = true)
    (hm0 : s0.mem ⊨ (withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).pre x s0 ∗ R) :
    SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s0
      (fun s' => ∃ r g sess,
        CurStateV kit st0 ikit ist0 Scope ctl encRecord x r g sess R s0 s') := by
  let envF := h45_envF hEnv
  let envL := h45_envL hEnv
  let envN := h45_envNone hEnv
  refine h45_segLoad_to_dispatch_trap hEnv x R s0 hfs hpc0 hrun0 hal0 hm0 ?_
  intro s sp ans w0 w1 w2 w3 w4 w5 w6 v50 tail hsp_eq hpc hmeta hbnds _hw0_ne3 htail
    hl htr hx24 hx27 hx21 hx23 hx25 hx26 hx28 hps hm
  rcases ans with ⟨⟩ | (_ | r)
  · rw [← h45_segExit_kitF_trap]
    exact h45_segExit_mono_trap (Pf.SegLoad.segLoad_dispatch_err_trap envF x R s0 s sp w0 w1 w2 w3 w4 w5 w6 v50 tail
      hsp_eq hpc hmeta hbnds.2.2.2.2 htail hl htr hx27 hx21 hx23 hx25 hx26 hx28 hps hm)
      (fun _ => h45_curStateV_of_false)
  · rw [← h45_segExit_kitF_trap]
    exact h45_segExit_mono_trap (Pf.SegLoad.segLoad_dispatch_none_trap envF x R s0 s sp w0 w1 w2 w3 w4 w5 w6 v50 tail
      hsp_eq hpc hmeta hbnds.2.2.2.2 htail hl htr hx24 hx26 hx28 hps hm)
      (fun _ => h45_curStateV_of_false)
  · cases hcur : r.currentSession with
    | none =>
      have hmN : s.mem ⊨ (memRegion (sp + 0x46a#64) 0x116 ∗
          memRegion (sp + 0x580#64) 368 ∗
          ((sp + 0x6f8#64) ↦ₛ tail) ∗
          ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗
          ((sp + 0x840#64) ↦₆₄ w6) ∗
          LoadOutRes (h45_ScopeNone Scope) A img.base (.ok (some r)) w0 w1 w2 w3 w4 w5 w6 tail ∗
          protocolAddressAt A x.rem x.remA ∗
          A.pool ∗ stackAt sp encSubStack ∗ loadVtablesAt kit ∗
          Pf.SegLoad.dispatchFrame kit st0 ikit ist0 ctl x s0 v50) ∗ R := by
        refine Satisfies.mono ?_ hm
        exact sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_left (h45_loadOutRes_some_scopeNone A img.base w0 w1 w2 w3 w4 w5 w6 tail hcur))))))))
      rw [← h45_segExit_kitF_trap]
      exact h45_segExit_mono_trap (Pf.SegLoad.segLoad_dispatch_some_trap envN x R s0 s r sp w0 w1 w2 w3 w4 w5 w6 v50 tail
        hsp_eq hpc hmeta hbnds htail hl htr hx24 hx27 hx21 hx23 hx25 hx26 hx28 hps hmN)
        (fun _ => h45_curStateV_of_scopeNone)
    | some sess =>
      subst hsp_eq
      rcases hmeta with ⟨hrun, hsp, hal0, hal, hx29, hx19, hF, hsym, hvregs⟩
      rcases hbnds with ⟨hpt_lt, hrest_lt, hloc_ne, hnsec, hsp_le⟩
      have hm_drop : s.mem ⊨
          LoadOutRes Scope A img.base (.ok (some r)) w0 w1 w2 w3 w4 w5 w6 tail ∗
          ((memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
            ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
            ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
            ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
            protocolAddressAt A x.rem x.remA ∗
            A.pool ∗ stackAt (s0.sp - 0xbe0#64) encSubStack ∗
            Pf.SegLoad.dispatchFrame kit st0 ikit ist0 ctl x s0 v50) ∗ R) := by
        refine Satisfies.drop_left (P := loadVtablesAt kit) ?_
        refine Satisfies.mono ?_ hm
        exact Entails.of_eq (by ac_rfl)
      clear hm
      rw [loadOutRes_some_eq] at hm_drop
      obtain ⟨g, hm_drop1⟩ := satisfies_sepExists_left hm_drop
      clear hm_drop
      rw [sepConj_assoc] at hm_drop1
      obtain ⟨⟨hscope, hcap_lt, hw0_eq, hw1_eq, hw2_eq, hw3_eq_init, htail_inl⟩, hm_drop2⟩ :=
        satisfies_pure_left hm_drop1
      clear hm_drop1
      subst hw0_eq hw1_eq hw2_eq hw3_eq_init
      obtain ⟨hw0_ne1, hw0_ne2, _⟩ := ne_neg_tags_of_lt_two_pow_63 hcap_lt
      have hm_cur : s.mem ⊨
          ⌜recordCurCap g ≠ 0xFFFFFFFFFFFFFFFF#64⌝ ∗
          ((((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ v50) ∗
            ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
            memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x358 ∗
            ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
            ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
            ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
            (recordHeap A g r ∗
              memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
              memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
              protocolAddressAt A x.rem x.remA ∗
              A.pool ∗ stackAt (s0.sp - 0xbe0#64) encSubStack ∗
              memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
              Pf.SegLoad.dispatchFrameNoRec kit st0 ikit ist0 ctl x s0)) ∗ R) := by
        refine Satisfies.mono ?_ hm_drop2
        refine Entails.trans (sepConj_mono_left (curSession_some_of_recordTailInline htail_inl hcur)) ?_
        rw [Pf.SegLoad.dispatchFrame_eq_rec_sep kit st0 ikit ist0 ctl x s0 v50]
        exact Entails.of_eq (by ac_rfl)
      clear hm_drop2
      obtain ⟨hw3_ne, hm_cur'⟩ := satisfies_pure_left hm_cur
      clear hm_cur
      refine Pf.SegLoad.segExit_of_sepWP_frozen_trap ⟨hF, hsym⟩ hm_cur'
        (Pf.SegLoad.segLoad_dispatch_some_cur_wp_trap envL hpc hrun hsp hal hw0_ne1 hw0_ne2 hw3_ne htail
          hx24 hx27 hx21 hx23 hx25 hx26 hx28 hps) ?_
      intro sf P_f hpcf hrunf hpostf hFf hm_f
      rcases hpostf with ⟨hspf, half, htrf, hx19f, hx29f, hvregsf, hx20f, hx21f, hx25f, hx26f, hx28f, rfl⟩
      refine Pf.SegLoad.segExit_done_trap ⟨r, g, sess, hcur, ⟨hscope, hl⟩, ?_⟩
      refine ⟨?_, ⟨hrunf, hspf, hal0, half, by rw [hx29f, hx29], by rw [hx19f, hx19], hFf.1, hFf.2, by rw [hvregsf, hvregs]⟩,
        by rw [htrf, htr],
        ⟨hx20f, hx21f, hx25f, hx26f, hx28f⟩,
        hpt_lt, hrest_lt, hloc_ne, hnsec, enc_sp_bound_of_kit kit ikit hsp_le, ?_⟩
      · rw [curPC, Pf.SegLoad.encEntry_eq_fnAddr_trap envL, hpcf]
      · dsimp only [EncSeam, curScratch]
        refine Satisfies.mono ?_ hm_f
        have hrec := sessionRecordAt_of_words56_sep_tail A (s0.sp - 0xbe0#64 + 0x110#64) g r htail_inl
        have h38 : (s0.sp - 0xbe0#64 + 0x110#64) + 0x38#64 = s0.sp - 0xbe0#64 + 0x148#64 := by bv_arith
        rw [h38] at hrec
        have h46a := memRegion_0x46a_0x716_fold (s0.sp - 0xbe0#64) w4 w5 w6 tail htail
        have hspills := encSpillsAt_fold kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x
        have hperm_cur :
            (recordWords56At (s0.sp - 0xbe0#64 + 0x110#64) g.prevCap g.prevPtr 0#64 (recordCurCap g) w4 w5 w6 ∗
              ((s0.sp - 0xbe0#64 + 0x148#64) ↦ₛ tail) ∗
              memRegion (s0.sp - 0xbe0#64 + 0x280#64) 0x1e8 ∗
              ((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ (s0.sp - 0xbe0#64 + 0x128#64)) ∗
              ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
              ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
              ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
              ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
              (recordHeap A g r ∗
                memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
                memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
                protocolAddressAt A x.rem x.remA ∗
                A.pool ∗ stackAt (s0.sp - 0xbe0#64) encSubStack ∗
                memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
                Pf.SegLoad.dispatchFrameNoRec kit st0 ikit ist0 ctl x s0)) ∗ R =
            (recordWords56At (s0.sp - 0xbe0#64 + 0x110#64) g.prevCap g.prevPtr 0#64 (recordCurCap g) w4 w5 w6 ∗
              ((s0.sp - 0xbe0#64 + 0x148#64) ↦ₛ tail) ∗ recordHeap A g r) ∗
            (encSpillsInit kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗ ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA)) ∗
            (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
              memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
              memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗
              ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
              ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
              ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
              memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338) ∗
            (memRegion (s0.sp - 0xbe0#64 + 0x280#64) 0x1e8 ∗
              ((s0.sp - 0xbe0#64 + 0x468#64) ↦₈ 0#8) ∗ ((s0.sp - 0xbe0#64 + 0x469#64) ↦₈ 0#8) ∗
              memRegion (s0.sp - 0xbe0#64) 0x50 ∗
              ((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ (s0.sp - 0xbe0#64 + 0x128#64)) ∗
              memRegion x.ret 248 ∗
              encCommon A ctl img x 0 s0 ∗ (encStoreExtra kit st0 ikit ist0 x s0 ∗ R)) := by
          dsimp only [Pf.SegLoad.dispatchFrameNoRec, encCommon]
          ac_rfl
        rw [hperm_cur]
        refine Entails.trans (sepConj_mono hrec (sepConj_mono hspills (sepConj_mono_left h46a))) ?_
        exact Entails.of_eq (by ac_rfl)

end SegLoad

section SegSignalUnack
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails
open CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.LibsignalSession

set_option linter.unusedVariables false in
def h45_segSignalUnackRestFrame {ss_vt id_vt : BitVec 64} (A : RustAlloc) (ctl : BitVec 64)
    (_img : Obj.Image)
    (x : WithStoresEncGhost) (g : RecordGhost) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (pqCap pqPtr : BitVec 64) (k : IdentityKey) (sp : BitVec 64) (s0 : State) : SepProp :=
  vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) g.prevCap g.prevPtr [] ∗
  ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
  otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
  ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8 ∗
  curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
  memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x5d8#64) 0x5a8 ∗
  memRegion x.ret 248 ∗
  (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
  nowAt s0.sp x.now ∗ CryptoVerification.SignalSession.Coins.coinsAfter _img.base x.cur x.rest 0 ∗
  memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - unackItemsStack) ∗
  encSavedRegs s0.sp s0 ∗ A.pool

theorem h45_segSignal_keyState_mem_unpack {ss_vt id_vt : BitVec 64} (A : RustAlloc) (ctl : BitVec 64)
    (img : Obj.Image)
    (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (pqCap pqPtr : BitVec 64) (k : IdentityKey) (sp : BitVec 64) (R : SepProp) (s0 : State)
    {m : Memory} (hsp0 : s0.sp - 0xbe0#64 = sp)
    (hm : m ⊨ (takenSlots A sp sess taken ∗ otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8) ∗
      curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗
      encCommon A ctl img x 0 s0 ∗ R) :
    ∃ g G,
      m ⊨ ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        ((sessionStateReprAt A (sp + 0x128#64) G { sess with state := taken } ∗
          memRegion (sp + 0x580#64) 88 ∗
          logOff img ∗
          stackAt sp unackItemsStack ∗
          h45_segSignalUnackRestFrame (ss_vt := ss_vt) (id_vt := id_vt) A ctl img x g otr pqCap pqPtr k sp s0) ∗
        R) := by
  unfold takenSlots encCommon at hm
  rw [hsp0] at hm
  simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc] at hm
  obtain ⟨g, hm⟩ := hm
  have hm_rec := Satisfies.mono (sepConj_mono_left (segSignal_rec_unpack A sp g sess taken)) hm
  simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc] at hm_rec
  obtain ⟨G, hm_rec⟩ := hm_rec
  have h46a : memRegion (sp + 0x46a#64) 0x716 =
      memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x580#64) 88 ∗
      memRegion (sp + 0x5d8#64) 0x5a8 := by
    rw [show sp + 0x46a#64 = sp + BitVec.ofNat 64 0x46a from rfl,
        mr_cut_add sp 0x46a 0x116 0x600 (by decide),
        mr_cut_add sp (0x46a + 0x116) 88 0x5a8 (by decide)]
  rw [h46a, stackAt_sub sp encSubStack unackItemsStack] at hm_rec
  refine ⟨g, G, ?_⟩
  unfold h45_segSignalUnackRestFrame
  exact Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm_rec

theorem h45_segSignal_unack_pre_frame {ss_vt id_vt : BitVec 64} (A : RustAlloc) (ctl : BitVec 64)
    (img : Obj.Image)
    (x : WithStoresEncGhost) (g : RecordGhost) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (sp : BitVec 64) (R Pm : SepProp) (s0 s1 : State)
    (hsp1 : s1.sp = sp)
    (hx0 : s1.readReg64 .x0 = sp + 0x128#64)
    (hx8 : s1.readReg64 .x8 = sp + 0x580#64)
    (hPm : Pm ⊢ (sp + 0x280#64) ↦₆₄ (sp + 0x128#64))
    (hm : s1.mem ⊨ Pm ∗
      ((sessionStateReprAt A (sp + 0x128#64) G { sess with state := taken } ∗
        memRegion (sp + 0x580#64) 88 ∗
        logOff img ∗
        stackAt sp unackItemsStack ∗
        h45_segSignalUnackRestFrame (ss_vt := ss_vt) (id_vt := id_vt) A ctl img x g otr pqCap pqPtr k sp s0) ∗
      R)) :
    s1.mem ⊨ (unackItemsSpec A img).pre ⟨sp + 0x128#64, G, { sess with state := taken }, sp + 0x580#64⟩ s1 ∗
      ((((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        h45_segSignalUnackRestFrame (ss_vt := ss_vt) (id_vt := id_vt) A ctl img x g otr pqCap pqPtr k sp s0) ∗
      R) := by
  have hm' := Satisfies.mono (sepConj_mono_left hPm) hm
  unfold unackItemsSpec
  dsimp only
  rw [hsp1]
  have hpure : (⌜s1.readReg64 .x0 = sp + 0x128#64 ∧ s1.readReg64 .x8 = sp + 0x580#64⌝ : SepProp) ∗
      (((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        ((sessionStateReprAt A (sp + 0x128#64) G { sess with state := taken } ∗
          memRegion (sp + 0x580#64) 88 ∗
          logOff img ∗
          stackAt sp unackItemsStack ∗
          h45_segSignalUnackRestFrame (ss_vt := ss_vt) (id_vt := id_vt) A ctl img x g otr pqCap pqPtr k sp s0) ∗
        R)) =
      (((⌜s1.readReg64 .x0 = sp + 0x128#64 ∧ s1.readReg64 .x8 = sp + 0x580#64⌝ ∗
        sessionStateReprAt A (sp + 0x128#64) G { sess with state := taken } ∗
        memRegion (sp + 0x580#64) 88 ∗
        logOff img ∗
        stackAt sp unackItemsStack) ∗
        ((((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
          h45_segSignalUnackRestFrame (ss_vt := ss_vt) (id_vt := id_vt) A ctl img x g otr pqCap pqPtr k sp s0) ∗
        R))) := by
    ac_rfl
  rw [← hpure, satisfies_pure_sepConj]
  exact ⟨⟨hx0, hx8⟩, hm'⟩

theorem h45_segSignal_unack_panic_absurd (A : RustAlloc) (img : Obj.Image)
    (G : SessionGhost) (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (sp : BitVec 64) (F R : SepProp) (s1 sf : State)
    (hpk : sess.pendingPreKey = none)
    (hpost : sf.mem ⊨ ((unackItemsSpec A img).onPanic
      ⟨sp + 0x128#64, G, { sess with state := taken }, sp + 0x580#64⟩ s1 sf ∗ F) ∗ R) :
    False := by
  unfold unackItemsSpec at hpost
  dsimp only at hpost
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost
  rcases hpost.1.1 with ⟨items, hsome, _⟩
  rw [hpk] at hsome
  cases hsome

theorem h45_segSignal_unack_post_pack {ss_vt id_vt : BitVec 64} (A : RustAlloc) (ctl : BitVec 64)
    (img : Obj.Image)
    (x : WithStoresEncGhost) (g : RecordGhost) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (sp : BitVec 64) (R : SepProp) (s0 s1 s2 : State)
    (hsp0 : s0.sp - 0xbe0#64 = sp)
    (hsp1 : s1.sp = sp)
    (hpk : sess.pendingPreKey = none)
    (hpost : s2.mem ⊨ ((unackItemsSpec A img).post
      ⟨sp + 0x128#64, G, { sess with state := taken }, sp + 0x580#64⟩ s1 s2 ∗
      (((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        h45_segSignalUnackRestFrame (ss_vt := ss_vt) (id_vt := id_vt) A ctl img x g otr pqCap pqPtr k sp s0)) ∗
      R) :
    s2.trace = s1.trace ∧
    (s2.mem ⊨
      (takenSlots A sp sess taken ∗ otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8) ∗
      curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      (memRegion (sp + 0x46a#64) 0x116 ∗ ((sp + 0x580#64) ↦₃₂ 2#32) ∗
        memRegion (sp + 0x584#64) 84 ∗ memRegion (sp + 0x5d8#64) 0x5a8) ∗
      memRegion x.ret 248 ∗ encCommon A ctl img x 0 s0 ∗ R) := by
  have hout : unackOutAt (sp + 0x580#64) G.kyber
      ({ sess with state := taken }).pendingKyberPreKey
      ({ sess with state := taken }).pendingPreKey =
      ((sp + 0x580#64) ↦₃₂ 2#32) ∗ memRegion (sp + 0x584#64) 84 := by
    change unackOutAt (sp + 0x580#64) G.kyber sess.pendingKyberPreKey sess.pendingPreKey = _
    rw [hpk]
    unfold unackOutAt
    have h584 : (sp + 0x580#64) + 4#64 = sp + 0x584#64 := by bv_omega
    rw [h584]
  unfold unackItemsSpec at hpost
  dsimp only [Spec.post] at hpost
  rw [hsp1, hout] at hpost
  simp only [sepConj_assoc] at hpost
  rw [satisfies_pure_sepConj] at hpost
  rcases hpost with ⟨htr, hmem⟩
  refine ⟨htr, ?_⟩
  unfold h45_segSignalUnackRestFrame at hmem
  have hrec :
      vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) g.prevCap g.prevPtr [] ∗
        sessionStateReprAt A (sp + 0x128#64) G { sess with state := taken } ⊢
      ∃∗ g' : RecordGhost, sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess taken) :=
    Entails.trans (segSignal_rec_pack A sp g.prevCap g.prevPtr G sess taken)
      (Entails.sepExists_right ⟨g.prevCap, g.prevPtr, some G⟩ (Entails.refl _))
  have hmem_rearr : s2.mem ⊨
      (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) g.prevCap g.prevPtr [] ∗
        sessionStateReprAt A (sp + 0x128#64) G { sess with state := taken }) ∗
      (memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - unackItemsStack) ∗
        stackAt sp unackItemsStack) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8 ∗
      curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x116 ∗ ((sp + 0x580#64) ↦₃₂ 2#32) ∗
      memRegion (sp + 0x584#64) 84 ∗ memRegion (sp + 0x5d8#64) 0x5a8 ∗
      memRegion x.ret 248 ∗
      (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
      nowAt s0.sp x.now ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest 0 ∗ logOff img ∗
      encSavedRegs s0.sp s0 ∗ A.pool ∗ R :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by ac_rfl)) hmem
  rw [← stackAt_sub sp encSubStack unackItemsStack] at hmem_rearr
  have hmem_fold := Satisfies.mono (sepConj_mono_left hrec) hmem_rearr
  unfold takenSlots encCommon
  rw [hsp0]
  exact Eq.mp (congrArg (s2.mem ⊨ ·) (by ac_rfl)) hmem_fold

theorem h45_segSignal_to_ack_trap {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (hEnv : EncEnvT_trap kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (R0 : SepProp) (s0 s : State) (hpk : sess.pendingPreKey = none)
    (hs : KeyStateV kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr k R0 s0 s) :
    SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s
      (fun s' => Pf.SegSignal.SegSignalAckStateV kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr
        k R0 s0 s') := by
  let R := encStoreExtra kit st0 ikit ist0 x s0 ∗ R0
  rcases hs with ⟨hcur, hsc, hfrom, hrem, hs_pc,
    ⟨hrun, hsp, hal0, hal, hx29, hx19, hfl, hsym, hvregs⟩,
    htr, ⟨hx0, hx8, hx20, _hx22, hx23, hx25, hx26, hx27, hx28⟩,
    hpt, hrest, hloc, hnow, hstk, hm⟩
  set sp := s0.sp - 0xbe0#64
  have hsp0 : s0.sp - 0xbe0#64 = sp := rfl
  have hentry : encEntry img = (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName :=
    entryOf_eq_tripleRatchetProgAt_trap (C := C) (abs := abs) hEnv.loads CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName
  have hs_pc' : s.pc = (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x344#64 := by
    simpa only [keyPC, hentry] using hs_pc
  obtain ⟨g, G, hm_unp⟩ :=
    h45_segSignal_keyState_mem_unpack A ctl img x sess otr taken pqCap pqPtr k sp R s0 hsp0 hm
  refine Pf.SegFrom.SegExit.of_sepWP_trap hm_unp (Pf.SegSignal.segSignal_step_bl_trap hs_pc' hrun hsp hal) ?_
  intro s1 Pm1 hL0 hsteps01 hs1_pc hs1_run hm1
    ⟨hs1_sp, hs1_tr, hs1_x0, hs1_x8, hs1_x19, hs1_x20, hs1_x23, hs1_x25, hs1_x26, hs1_x27,
      hs1_x28, hs1_x29, hs1_vregs, hs1_lr, hPm1⟩
  have ⟨hfl1, hsym1⟩ := SegFrom.callInv_steps hfl hsym hsteps01 hL0
  have hs1_al : s1.spAligned = true := SegFrom.spAligned_of_sp_eq hal (hs1_sp.trans hsp.symm)
  have hs1_pc' : s1.pc = img.base + bv% (ls_off% "<libsignal_protocol::state::session::SessionState>::unacknowledged_pre_key_message_items") := by
    rw [hs1_pc, Pf.SegSignal.unack_addr_eq_trap]
  have hm1_pre := h45_segSignal_unack_pre_frame A ctl img x g G sess otr taken pqCap pqPtr k sp R Pm1 s0 s1
    hs1_sp (hs1_x0.trans hx0) (hs1_x8.trans hx8) hPm1 hm1
  refine Pf.SegFrom.SegExit.call_trap hEnv.callees.unack
    ⟨sp + 0x128#64, G, { sess with state := taken }, sp + 0x580#64⟩
    hs1_pc' hs1_run hs1_al hs1_lr hm1_pre
    (fun _ code _ _ hex => by
      rw [show (unackItemsSpec A img).onExit
        ⟨sp + 0x128#64, G, { sess with state := taken }, sp + 0x580#64⟩ code s1 _ = ⌜False⌝ from rfl,
          satisfies_pure_sepConj] at hex
      exact hex.1)
    (fun sf _ _ hpost =>
      (h45_segSignal_unack_panic_absurd A img G sess taken sp _ R s1 sf hpk hpost).elim)
    ?_
  intro s2 hL1 hsteps12 hs2_pc hs2_run hs2_sp hcs12 hpost2
  have ⟨hfl2, hsym2⟩ := SegFrom.callInv_steps hfl1 hsym1 hsteps12 hL1
  have hs2_al : s2.spAligned = true := SegFrom.spAligned_of_sp_eq hs1_al hs2_sp
  have ⟨hs2_tr, hm2⟩ := h45_segSignal_unack_post_pack A ctl img x g G sess otr taken pqCap pqPtr k sp R
    s0 s1 s2 hsp0 hs1_sp hpk hpost2
  refine Pf.SegFrom.SegExit.next_trap ⟨hcur, hsc, hfrom, hrem, hpk, ?_,
    ⟨hs2_run, by reg_chain, hal0, hs2_al, by reg_chain, by reg_chain, hfl2, hsym2,
      (hcs12.2.2.2.2.2.2.2.2.2.2.2).trans (hs1_vregs.trans hvregs)⟩, by reg_chain,
    by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain,
    hpt, hrest, hloc, hnow, hstk, hm2⟩
  rw [hs2_pc, hentry]

end SegSignalUnack

end CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
