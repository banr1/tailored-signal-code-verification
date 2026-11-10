/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefs
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Statements
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244
import LibsignalBinary.Proofs.TripleRatchet.Statements

/-!
# `OTR::encrypt::<HookRng>` over SPQR V1 (`OtrEncryptV1RunStmt`)

Generalizes `otrEncrypt_body_ok_ext` to thread a state-and-tape restriction `Q` and spatial frame
`F` (`TokenInit img`) across `spqr::send`, deriving `OtrEncryptV1RunStmt` from `SpqrSendV1Stmt`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalSpqrV1.M4

set_option autoImplicit false

open Arm64 ProofLib CryptoGames CryptoGames.CBC CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet.Encrypt

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem h43a_except_ok_eq_error {α ε : Type _} (x : α) (e : ε) :
    ((Except.ok x : Except ε α) = Except.error e) = False := by simp

private theorem h43a_except_ok_ne_error_eq_true {α ε : Type _} (x : α) (e : ε) :
    ((Except.ok x : Except ε α) ≠ Except.error e) = True := by simp

attribute [local arm64_norm] h43a_except_ok_eq_error h43a_except_ok_ne_error_eq_true

private theorem h43a_subroutine_ok_of_sepWPp {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} {Qpre : α → State → SepProp} {F : SepProp}
    (h : ∀ (x : α) (R : SepProp) (s0 : State), s0.pc = entry → s0.status = .Running →
      (s0.mem ⊨ (Qpre x s0 ∗ F ∗ spec.pre x s0) ∗ R) → s0.spAligned = true →
      ∃ P Fr : SepProp, (s0.mem ⊨ P ∗ Fr) ∧
        SepWPp prog (s0.readReg64 Reg.lr) s0 P
          (fun sf P_f => ((sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ spec.post x s0 sf ∗ (F ∗ R))) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
          (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ spec.onPanic x s0 sf ∗ R))) :
    subroutine_ok prog entry
      { spec with
        pre := fun x s => Qpre x s ∗ F ∗ spec.pre x s
        post := fun x s0 sf => F ∗ spec.post x s0 sf } := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp
  obtain ⟨P, Fr, hm, hwp⟩ := h x R s0 hpc hrun hpre hsp
  refine ⟨P, Fr, hm, ?_⟩
  have hcomm : ∀ sf, (F ∗ spec.post x s0 sf) ∗ R = spec.post x s0 sf ∗ (F ∗ R) := fun sf => by ac_rfl
  simp only [hcomm]
  exact hwp

private theorem h43a_absorb_frame {prog : Program} {ret : BitVec 64} {s : State}
    {F P R : SepProp} {Ψ φ_pan : State → Prop} {sp0 : BitVec 64} {s0 : State}
    (h : SepWPp prog ret s P
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ (F ∗ R)) → Ψ sf) ∧
        sf.sp = sp0 ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ (F ∗ R)) → (φ_pan sf ∧ sf.mem ⊨ anyHeap ∗ (F ∗ R)))) :
    SepWPp prog ret s (F ∗ P)
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → Ψ sf) ∧
        sf.sp = sp0 ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (φ_pan sf ∧ sf.mem ⊨ anyHeap ∗ R)) := by
  intro R' hm hL
  have hm' : s.mem ⊨ P ∗ (F ∗ R') := by
    have heq : (F ∗ P) ∗ R' = P ∗ (F ∗ R') := by ac_rfl
    exact heq ▸ hm
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hq, hsp, hcs⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, hfalse⟩⟩ :=
    h (F ∗ R') hm' hL
  · refine ⟨sf, hsteps, Or.inl ⟨hpc, hrun, F ∗ P_f, ?_, ⟨?_, hsp, hcs⟩⟩⟩
    · have heq : P_f ∗ (F ∗ R') = (F ∗ P_f) ∗ R' := by ac_rfl
      exact heq ▸ hmf
    · intro hmR
      have heq : (F ∗ P_f) ∗ R = P_f ∗ (F ∗ R) := by ac_rfl
      exact hq (heq ▸ hmR)
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, F ∗ P_f, ?_, ?_⟩)⟩
    · have heq : P_f ∗ (F ∗ R') = (F ∗ P_f) ∗ R' := by ac_rfl
      exact heq ▸ hmf
    · intro hmR
      have heq : (F ∗ P_f) ∗ R = P_f ∗ (F ∗ R) := by ac_rfl
      obtain ⟨hφ, hany⟩ := hqp (heq ▸ hmR)
      refine ⟨hφ, ?_⟩
      rw [← sepConj_assoc] at hany
      exact Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hany
  · exact (not_satisfies_false_sepConj hfalse).elim

set_option maxHeartbeats 600000 in
set_option maxRecDepth 4096 in
set_option linter.unusedSimpArgs false in
/-- `otrEncrypt_body_ok_ext` generalized with a pure restriction `Q` on state and tape and a spatial frame `F` threaded through `spqr::send`. -/
theorem otrEncrypt_body_ok_ext_frame (Q : List (BitVec 8) → List (BitVec 8) → Prop) (F : SepProp)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (ext : String → Option (State → State)) (img : Obj.Image)
    (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hSend : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName)
      { spqrSendSpec A ctl S img with
        pre := fun x s => ⌜Q x.st.bytes x.rest⌝ ∗ F ∗ (spqrSendSpec A ctl S img).pre x s
        post := fun x s0 sf => F ∗ (spqrSendSpec A ctl S img).post x s0 sf })
    (hMK : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr messageKeysName) (messageKeysSpec C.F A img))
    (hGK : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr generateKeysName)
      ((generateKeysSpec C.F A).inImage img))
    (hNew : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signalMessageNewName)
      ((signalMessageNewSpec C.F A uuidTryParse).inImage img))
    (hNCK : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr nextChainKeyName) (nextChainKeySpec C.F img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr otrEncryptName)
      { otrEncryptSpec C A ctl uuidTryParse S img with
        pre := fun x s =>
          ⌜Q x.ot.pqrState x.rest⌝ ∗ F ∗ (otrEncryptSpec C A ctl uuidTryParse S img).pre x s
        post := fun x s0 sf => F ∗ (otrEncryptSpec C A ctl uuidTryParse S img).post x s0 sf } := by
  apply h43a_subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp_align
  unfold State.spAligned at hsp_align
  dsimp only [otrEncryptSpec, Spec.inImage, Spec.allowPanicWhen,
    Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Option.isSome] at hpre ⊢
  rw [sepConj_pure_left_comm F, sepConj_pure_left_comm F] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hQ, ⟨himg_f, hsym⟩,
    ⟨hx0_0, hx1_0, hx2_0, hx3_0, hpt_lt_32, hx4_0, hloc_ne, hx5_0⟩, hpre⟩
  have hinv0 : CallInv img s0 := ⟨himg_f, hsym⟩
  refine ⟨F ∗ otrAt A x.o x.pqCap x.pqPtr x.ot ∗
      x.ptA ↦ₛ x.ptext ∗
        optAddrAt A x.locA x.loc ∗
          protocolAddressAt A x.rem x.remA ∗
            memRegion x.ret 120 ∗ tapeAt ctl x.cur x.rest ∗ logOff img ∗ stackAt s0.sp rootStack ∗ A.pool,
    R, ?_, ?_⟩
  · wp_focus_close arm64_sep_close
  have hfn := (ls_lemma% fnOff "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>")
  have hb : img.base &&& 0xfff#64 = 0#64 := ProofLib.ObjectLoad.base_aligned_of_loads himg
  rw [spqrSend_addr_eq_ext] at hSend
  rw [messageKeys_addr_eq_ext] at hMK
  rw [generateKeys_addr_eq_ext] at hGK
  rw [signalMessageNew_addr_eq_ext] at hNew
  rw [nextChainKey_addr_eq_ext] at hNCK
  have hAes := aesEnc_ok_at_encrypt_ext C A ctl S ext img.base hC
  have hFmt := formatInner_ok_at_encrypt_ext C A ctl S ext img.base hC
  have hDealloc := dealloc_ok_at_encrypt_ext A ext img.base hC.toAllocContracts
  dsimp only [spqrSendSpec, messageKeysSpec, generateKeysSpec, signalMessageNewSpec,
    nextChainKeySpec, aesEncSpec, formatInnerSpec, rustDeallocSpec,
    Spec.inImage, Spec.allowPanicWhen,
    AesCall.pre, VecArg.at, SignalMessageNewGhost.inputsAt, Option.isSome] at hSend hMK hGK hNew hNCK hAes hFmt hDealloc
  simp only [sepConj_pure_left_comm F, pure_sepConj_pure_assoc] at hSend
  simp only [pure_sepConj_pure_assoc] at hMK hGK hNew hNCK hAes
  have hadrp : AdrpFact ((tripleRatchetProgAtExt img.base ext).fnAddr otrEncryptName) img.base := by
    refine ⟨adrp_0x453ee_eq img.base _ hb ?_⟩
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>")]
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>")) 864
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr otrEncryptName = entry
  examples_hide_fetches
  have ⟨hsp640, hsp640_beq⟩ := spAligned_sub_640 hsp_align
  apply SepWPp.of_sepWP_callInv hinv0 (mid := entry + bv% (2 ^ 64 + (ls_off% "spqr::send::<libsignal_session::HookRng>") - (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>")))
  wp_simp_pre only [otrAt, stackAt_encrypt_prologue s0.sp,
    stackAt_sub (s0.sp - 640#64) (rootStack - 640) spqrSendStack,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro s8
  apply SepWP.exists_elim; intro s16
  apply SepWP.exists_elim; intro s24
  apply SepWP.exists_elim; intro s32
  apply SepWP.exists_elim; intro s40
  apply SepWP.exists_elim; intro s48
  apply SepWP.exists_elim; intro s56
  apply SepWP.exists_elim; intro s64
  apply SepWP.exists_elim; intro s72
  apply SepWP.exists_elim; intro s80
  apply SepWP.exists_elim; intro s88
  apply SepWP.exists_elim; intro s96
  apply SepWP.exists_elim; intro w560
  wp_steps
  apply SepWP.done
    (by simp (config := { decide := true }) only [arm64_norm])
    (by simp (config := { decide := true }) only [arm64_norm, hrun])
  intro hinv1
  refine SepWPp.call_frame_inv
    (x := ⟨s0.sp - 408#64, ⟨x.o, x.pqCap, x.pqPtr, x.ot.pqrState⟩, x.cur, x.rest⟩)
    hSend hinv1
    (by simp (config := { decide := true }) only [arm64_norm])
    (by simp (config := { decide := true }) only [arm64_norm, hrun])
    (by simp (config := { decide := true }) only [State.spAligned, arm64_norm, hsp_align, hsp640_beq])
    rfl rfl
    ⟨hQ, ⟨hinv1.1, hinv1.2⟩,
      by simp (config := { decide := true }) only [arm64_norm, hx1_0],
      by simp (config := { decide := true }) only [arm64_norm, hx1_0]⟩
    (by simp (config := { decide := true }) only [State.sp_writeReg64, State.sp_setPC, State.sp_setPState, State.sp_setMem, ite_true, ite_false]; sep_focus)
    (fun _ _ _ _ => allowPanic_not_exited)
    (fun sf _ hm => onPanic_of_send (x := x) (by simp (config := { decide := true }) only [arm64_norm]) hm)
    fun s1 hpc1 hrun1 hsp1 hcs1 hinv2 => ?_
  simp only [CalleeSavedPreserved] at hcs1
  simp (config := { decide := true }) only [arm64_norm, hx0_0, hx1_0, hx2_0, hx3_0, hx4_0, hx5_0] at hpc1 hsp1 hcs1
  obtain ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, h29_1⟩ := hcs1
  simp (config := { decide := true }) only [arm64_norm]
  refine SepWPp.pure_elim fun ⟨hdraws, htr1, hnp1⟩ => ?_
  have hnp1 : S.sendPanics x.ot.pqrState x.rest = false := by simpa using hnp1
  apply h43a_absorb_frame
  refine SepWPp.fold
    (Entails.of_eq (stackAt_sub (s0.sp - 640#64) (rootStack - 640) spqrSendStack).symm)
    (by sep_focus) ?_
  cases hsend : S.send x.ot.pqrState x.rest with
  | none =>
    simp (disch := decide) only [spqrSendResultAt, bv_sub_add_lit, Nat.reduceSub, sepConj_assoc]
    apply SepWPp.of_sepWP_callInv hinv2 (mid := entry + bv% (ls_off% "alloc::fmt::format::format_inner" - ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>"))
    refine SepWP.fold (Entails.of_eq (err_branch_stack_split s0.sp)) (by sep_focus) ?_
    wp_simp_pre only [stackAt_sub (s0.sp - 640#64) (rootStack - 640) extHookStack,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro b1
    apply SepWP.exists_elim; intro b0
    apply SepWP.exists_elim; intro c2
    apply SepWP.exists_elim; intro c1
    apply SepWP.exists_elim; intro c0
    apply SepWP.exists_elim; intro a2
    apply SepWP.exists_elim; intro a1
    apply SepWP.exists_elim; intro a0
    wp_steps
    apply SepWP.done
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm, hrun1])
    intro hinv3
    refine SepWPp.call_frame_inv
      (x := s0.sp - 544#64)
      hFmt hinv3
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm, hrun1])
      (by simp (config := { decide := true }) only [State.spAligned, arm64_norm, hsp1, hsp_align, hsp640_beq])
      rfl rfl
      (by simp (config := { decide := true }) only [arm64_norm, hsp1])
      (by simp (config := { decide := true }) only [State.sp_writeReg64, State.sp_writeVReg128, State.sp_setPC, State.sp_setPState, State.sp_setMem, ite_true, ite_false, hsp1]; sep_focus)
      (fun _ _ _ _ => allowPanic_not_exited)
      (fun sf _ hm => onPanic_of_alloc (x := x) (by simp (config := { decide := true }) only [arm64_norm, htr1]) hm)
      fun s2 hpc2 hrun2 hsp2 hcs2 hinv4 => ?_
    simp only [CalleeSavedPreserved] at hcs2
    simp (config := { decide := true }) only [arm64_norm, hsp1, h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, h29_1] at hpc2 hsp2 hcs2
    obtain ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, h29_2, hvregs2⟩ := hcs2
    simp (config := { decide := true }) only [arm64_norm, hsp1, htr1]
    refine SepWPp.exists_elim_top fun fBs => ?_
    refine SepWPp.pure_elim fun htr2 => ?_
    refine SepWPp.fold
      (Entails.of_eq (stackAt_sub (s0.sp - 640#64) (rootStack - 640) extHookStack).symm)
      (by sep_focus) ?_
    apply rodata_encrypt_sepWPp himg hinv4.1.roData
    apply SepWPp.of_sepWP_ret
    refine SepWP.fold (vecU8_544_unpack A s0.sp fBs) (by sep_focus) ?_
    wp_simp_pre only [ret120_split_err x.ret,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro r6
    apply SepWP.exists_elim; intro r5
    apply SepWP.exists_elim; intro r4
    apply SepWP.exists_elim; intro r3
    apply SepWP.exists_elim; intro r2
    apply SepWP.exists_elim; intro r1
    apply SepWP.exists_elim; intro r0
    apply SepWP.exists_elim; intro fCap
    apply SepWP.exists_elim; intro fPtr
    wp_steps
    refine SepWP.fold (err_branch_stack_join s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
    refine SepWP.fold (stackAt_encrypt_epilogue s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
    refine SepWP.fold (otrAt_exists_pack A x.o x.pqCap x.pqPtr x.ot) (by sep_focus) ?_
    refine SepWP.fold (errResultAt_invalidState_pack A x.ret fCap fPtr fBs img.base entry hadrp.eq) (by sep_focus) ?_
    rw [model_of_send_none x C S hnp1 hsend]
    dsimp only
    apply EncryptCoreFacts.sepWP_done_encrypt
    · simp (config := { decide := true }) only [arm64_norm]
    · simp (config := { decide := true }) only [arm64_norm, hrun2]
    · exact ⟨by decide, by simp (config := { decide := true }) only [arm64_norm, htr2]⟩
    · sep_focus
    · simp (config := { decide := true }) only [arm64_norm, hsp2, BitVec.sub_add_cancel]
    · simp only [CalleeSavedPreserved]; simp (config := { decide := true }) only [arm64_norm, hvregs2]
  | some val =>
    obtain ⟨newPqrState, pqrKey, pqrMsg⟩ := val
    refine SepWPp.fold (sendResultAt_some_unpack A s0.sp newPqrState pqrKey pqrMsg) (by sep_focus) ?_
    refine SepWPp.exists_elim fun newPqrCap => SepWPp.exists_elim fun newPqrPtr =>
      SepWPp.exists_elim fun pqrMsgCap => SepWPp.exists_elim fun pqrMsgPtr =>
      SepWPp.exists_elim fun k0 => SepWPp.exists_elim fun k1 =>
      SepWPp.exists_elim fun k2 => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hpqrMsgLen, hnewPqrCap⟩ => ?_
    have ⟨hnewPqrCap_beq, hnewPqrCap_eq⟩ := add_one_beq_zero_false_of_lt_2_63 hnewPqrCap
    apply SepWPp.of_sepWP_callInv hinv2 (mid := entry + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::message_keys") - (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>")))
    refine SepWP.fold (Entails.of_eq (some_branch_pre_mk_split s0.sp)) (by sep_focus) ?_
    wp_simp_pre only [stackAt_sub (s0.sp - 640#64) (rootStack - 640) messageKeysStack,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro u128
    apply SepWP.exists_elim; intro u136
    apply SepWP.exists_elim; intro u144
    apply SepWP.exists_elim; intro w568
    apply SepWP.exists_elim; intro w576
    apply SepWP.exists_elim; intro w584
    apply SepWP.exists_elim; intro w592
    apply SepWP.exists_elim; intro w600
    apply SepWP.exists_elim; intro w608
    apply SepWP.exists_elim; intro w616
    apply SepWP.exists_elim; intro w624
    apply SepWP.exists_elim; intro w632
    apply SepWP.exists_elim; intro w640
    wp_steps
    refine SepWP.fold (some_branch_pre_mk_fold A s0.sp _ _ _ _ _ _ k0 k1 k2 pqrKey) (by sep_focus) ?_
    apply SepWP.done
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm, hrun1])
    intro hinv3
    refine SepWPp.call_frame_inv
      (x := (x.o + 152#64, x.ot.senderChainKey, s0.sp - 408#64))
      hMK hinv3
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm, hrun1])
      (by simp (config := { decide := true }) only [State.spAligned, arm64_norm, hsp1, hsp_align, hsp640_beq])
      rfl rfl
      ⟨⟨hinv3.1, hinv3.2⟩,
        by simp (config := { decide := true }) only [arm64_norm, hsp1, h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, h29_1],
        by simp (config := { decide := true }) only [arm64_norm, hsp1, h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, h29_1]⟩
      (by simp (config := { decide := true }) only [State.sp_writeReg64, State.sp_writeVReg128, State.sp_setPC, State.sp_setPState, State.sp_setMem, ite_true, ite_false, hsp1]; sep_focus)
      (fun _ _ _ _ => allowPanic_not_exited)
      (fun sf _ hm => onPanic_of_alloc (x := x) (by simp (config := { decide := true }) only [arm64_norm, htr1]) hm)
      fun s2 hpc2 hrun2 hsp2 hcs2 hinv4 => ?_
    simp only [CalleeSavedPreserved] at hcs2
    simp (config := { decide := true }) only [arm64_norm, hsp1, h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, h29_1] at hpc2 hsp2 hcs2
    obtain ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, h29_2⟩ := hcs2
    simp (config := { decide := true }) only [arm64_norm, hsp1, htr1]
    refine SepWPp.pure_elim fun htr2 => ?_
    refine SepWPp.fold
      (Entails.of_eq (stackAt_sub (s0.sp - 640#64) (rootStack - 640) messageKeysStack).symm)
      (by sep_focus) ?_
    apply SepWPp.of_sepWP_callInv hinv4 (mid := entry + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys") - (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>")))
    wp_simp_pre only [stackAt_sub (s0.sp - 640#64) (rootStack - 640) generateKeysStack,
      sepConj_assoc]
    wp_steps
    apply SepWP.done
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm, hrun2])
    intro hinv5
    have hseed_len : (x.ot.senderChainKey.messageKeys C.F).seed.length = 32 :=
      messageKeys_seed_length C.F x.ot.senderChainKey
    refine SepWPp.call_frame_inv
      (x := ⟨s0.sp - 408#64, x.ot.senderChainKey.messageKeys C.F, s0.sp - 144#64, pqrKey, s0.sp - 552#64⟩)
      hGK hinv5
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm, hrun2])
      (by simp (config := { decide := true }) only [State.spAligned, arm64_norm, hsp2, hsp_align, hsp640_beq])
      rfl rfl
      ⟨⟨hinv5.1, hinv5.2⟩,
        by simp (config := { decide := true }) only [arm64_norm, hsp2, h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, h29_2],
        by simp (config := { decide := true }) only [arm64_norm, hsp2, h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, h29_2],
        by simp (config := { decide := true }) only [arm64_norm, hsp2, h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, h29_2], hseed_len⟩
      (by simp (config := { decide := true }) only [State.sp_writeReg64, State.sp_setPC, State.sp_setPState, State.sp_setMem, ite_true, ite_false, hsp2]; sep_focus)
      (fun _ _ _ _ => allowPanic_not_exited)
      (fun sf _ hm => by
        simp only [sepConj_assoc, satisfies_pure_sepConj] at hm
        exact hm.1.elim)
      fun s3 hpc3 hrun3 hsp3 hcs3 hinv6 => ?_
    simp only [CalleeSavedPreserved] at hcs3
    simp (config := { decide := true }) only [arm64_norm, hsp2, h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, h29_2] at hpc3 hsp3 hcs3
    obtain ⟨h19_3, h20_3, h21_3, h22_3, h23_3, h24_3, h25_3, h26_3, h27_3, h28_3, h29_3⟩ := hcs3
    simp (config := { decide := true }) only [arm64_norm, hsp2, htr2]
    refine SepWPp.pure_elim fun htr3 => ?_
    refine SepWPp.fold
      (Entails.of_eq (stackAt_sub (s0.sp - 640#64) (rootStack - 640) generateKeysStack).symm)
      (by sep_focus) ?_
    set mk := (x.ot.senderChainKey.messageKeys C.F).generateKeys C.F pqrKey
    apply SepWPp.of_sepWP_callInv hinv6 (mid := entry + bv% (ls_off% "signal_crypto::aes_cbc::aes_256_cbc_encrypt" - ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>"))
    wp_simp_pre only [messageKeysAt, bv_sub_add_lit, Nat.reduceSub,
      stackAt_sub (s0.sp - 640#64) (rootStack - 640) extHookStack, sepConj_assoc]
    wp_steps
    apply SepWP.done
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm, hrun3])
    intro hinv7
    have hpt_lt_40 : x.ptext.length < 2 ^ 40 := by omega
    refine SepWPp.call_frame_inv
      (x := ⟨x.ptA, x.ptext, s0.sp - 552#64, keyToBytes32 mk.cipherKey,
        s0.sp - 488#64, CBC.blockToBytesLE mk.iv, s0.sp - 464#64⟩)
      hAes hinv7
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm, hrun3])
      (by simp (config := { decide := true }) only [State.spAligned, arm64_norm, hsp3, hsp_align, hsp640_beq])
      rfl rfl
      ⟨by simp (config := { decide := true }) only [arm64_norm, hsp3, h19_3, h20_3, h21_3, h22_3, h23_3, h24_3, h25_3, h26_3, h27_3, h28_3, h29_3],
        by simp (config := { decide := true }) only [arm64_norm, hsp3, h19_3, h20_3, h21_3, h22_3, h23_3, h24_3, h25_3, h26_3, h27_3, h28_3, h29_3, hx3_0],
        by simp (config := { decide := true }) only [arm64_norm, hsp3],
        by simp (config := { decide := true }) only [arm64_norm, hsp3],
        by simp (config := { decide := true }) only [arm64_norm, hsp3],
        by simp (config := { decide := true }) only [arm64_norm, hsp3],
        by simp (config := { decide := true }) only [arm64_norm, hsp3],
        length_keyToBytes32 mk.cipherKey, blockToBytesLE_length mk.iv, hpt_lt_40⟩
      (by simp (config := { decide := true }) only [State.sp_writeReg64, State.sp_setPC, State.sp_setPState, State.sp_setMem, ite_true, ite_false, hsp3]; sep_focus)
      (fun _ _ _ _ => allowPanic_not_exited)
      (fun sf _ hm => onPanic_of_alloc (x := x) (by simp (config := { decide := true }) only [arm64_norm, htr3]) hm)
      fun s4 hpc4 hrun4 hsp4 hcs4 hinv8 => ?_
    simp only [CalleeSavedPreserved] at hcs4
    simp (config := { decide := true }) only [arm64_norm, hsp3, h19_3, h20_3, h21_3, h22_3, h23_3, h24_3, h25_3, h26_3, h27_3, h28_3, h29_3] at hpc4 hsp4 hcs4
    obtain ⟨h19_4, h20_4, h21_4, h22_4, h23_4, h24_4, h25_4, h26_4, h27_4, h28_4, h29_4⟩ := hcs4
    simp (config := { decide := true }) only [AesCall.frame, bytesToKey32_keyToBytes32,
      bytesToBlock_blockToBytesLE, arm64_norm, hsp3, htr3]
    refine SepWPp.pure_elim fun htr4 => ?_
    refine SepWPp.fold
      (Entails.of_eq (stackAt_sub (s0.sp - 640#64) (rootStack - 640) extHookStack).symm)
      (by sep_focus) ?_
    set ctext := aesCbcEncrypt C.E mk.cipherKey mk.iv x.ptext
    refine SepWPp.fold (vecU8_464_unpack A s0.sp ctext) (by sep_focus) ?_
    refine SepWPp.exists_elim fun ctCap => SepWPp.exists_elim fun ctPtr => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hctLenLeCap, hctCapLt, hctPtrNe⟩ => ?_
    have ⟨hctCap_beq, hctCap_eq⟩ := add_one_beq_zero_false_of_lt_2_63 hctCapLt
    refine SepWPp.fold (vecU8Buf_expose_slice A pqrMsgCap pqrMsgPtr pqrMsg) (by sep_focus) ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hpqrMsgLenLeCap, hpqrMsgCapLt, hpqrMsgPtrNe⟩ => ?_
    refine SepWPp.fold
      (bytes32_unpack (x.o + 24#64) (bs := x.ot.senderRatchetKey.publicKey.bytes.toList)
        (List.Vector.toList_length _))
      (by sep_focus) ?_
    refine SepWPp.exists_elim fun srk0 => SepWPp.exists_elim fun srk1 =>
      SepWPp.exists_elim fun srk2 => SepWPp.exists_elim fun srk3 => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hsrk => ?_
    apply SepWPp.of_sepWP_callInv hinv8 (mid := entry + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::protocol::SignalMessage>::new") - (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>")))
    refine SepWP.fold (Entails.of_eq (pre_new_stack_split s0.sp)) (by sep_focus) ?_
    wp_simp_pre only [chainKeyBytes_split (x.o + 152#64) x.ot.senderChainKey,
      BitVec.add_assoc, BitVec.reduceAdd,
      stackAt_sub (s0.sp - 640#64) (rootStack - 640) signalMessageNewStack,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro d3
    apply SepWP.exists_elim; intro d2
    apply SepWP.exists_elim; intro d1
    apply SepWP.exists_elim; intro d0
    wp_steps
    refine SepWP.fold
      (srk_copy_pack x.o s0.sp x.ot.senderRatchetKey.publicKey.bytes.toList srk0 srk1 srk2 srk3 hsrk)
      (by sep_focus) ?_
    apply SepWP.done
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm, hrun4])
    intro hinv9
    have hct_le : ctext.length ≤ 2 ^ 32 :=
      aesCbcEncrypt_length_le_u32 C.E mk.cipherKey mk.iv x.ptext (by omega)
    let x_new : SignalMessageNewGhost :=
      { messageVersion := x.ot.sessionVersion
        macKeyA := s0.sp - 520#64
        macKey := mk.macKey
        locA := x.locA
        loc := x.loc
        remA := x.remA
        rem := x.rem
        senderRatchetKeyA := s0.sp - 288#64
        senderRatchetKey := x.ot.senderRatchetKey.publicKey
        counter := x.ot.senderChainKey.index
        previousCounter := x.ot.previousCounter
        ciphertextA := ctPtr
        ciphertext := ctext
        senderIkA := x.o + 88#64
        senderIk := x.ot.localIdentityKey
        receiverIkA := x.o + 120#64
        receiverIk := x.ot.remoteIdentityKey
        pqRatchetA := pqrMsgPtr
        pqRatchet := pqrMsg
        ret := s0.sp - 408#64 }
    refine SepWPp.call_frame_inv
      (x := x_new)
      hNew hinv9
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm, hrun4])
      (by simp (config := { decide := true }) only [State.spAligned, arm64_norm, hsp4, hsp_align, hsp640_beq])
      rfl rfl
      ⟨⟨hinv9.1, hinv9.2⟩,
        by simp (config := { decide := true }) only [x_new, arm64_norm, hsp4, h19_4, h20_4, h21_4, h22_4, h23_4, h24_4, h25_4, h26_4, h27_4, h28_4, h29_4],
        by simp (config := { decide := true }) only [x_new, arm64_norm, hsp4, h19_4, h20_4, h21_4, h22_4, h23_4, h24_4, h25_4, h26_4, h27_4, h28_4, h29_4],
        by simp (config := { decide := true }) only [x_new, arm64_norm, hsp4, h19_4, h20_4, h21_4, h22_4, h23_4, h24_4, h25_4, h26_4, h27_4, h28_4, h29_4],
        by simp (config := { decide := true }) only [x_new, Option.isSome, arm64_norm, hsp4, h19_4, h20_4, h21_4, h22_4, h23_4, h24_4, h25_4, h26_4, h27_4, h28_4, h29_4],
        hloc_ne,
        by simp (config := { decide := true }) only [x_new, arm64_norm, hsp4, h19_4, h20_4, h21_4, h22_4, h23_4, h24_4, h25_4, h26_4, h27_4, h28_4, h29_4],
        by simp (config := { decide := true }) only [x_new, arm64_norm, hsp4, h19_4, h20_4, h21_4, h22_4, h23_4, h24_4, h25_4, h26_4, h27_4, h28_4, h29_4],
        by simp (config := { decide := true }) only [x_new, arm64_norm, hsp4, h19_4, h20_4, h21_4, h22_4, h23_4, h24_4, h25_4, h26_4, h27_4, h28_4, h29_4],
        by simp (config := { decide := true }) only [x_new, arm64_norm, hsp4, h19_4, h20_4, h21_4, h22_4, h23_4, h24_4, h25_4, h26_4, h27_4, h28_4, h29_4],
        by simp (config := { decide := true }) only [x_new, arm64_norm, hsp4, h19_4, h20_4, h21_4, h22_4, h23_4, h24_4, h25_4, h26_4, h27_4, h28_4, h29_4],
        hct_le, hpqrMsgLen⟩
      (by simp (config := { decide := true }) only [x_new, State.sp_writeReg64, State.sp_writeVReg128, State.sp_setPC, State.sp_setPState, State.sp_setMem, ite_true, ite_false, hsp4, bv_sub_add_lit, Nat.reduceSub]; sep_focus)
      (fun _ _ _ _ => allowPanic_not_exited)
      (fun sf _ hm => onPanic_of_alloc (x := x) (by simp (config := { decide := true }) only [arm64_norm, htr4]) hm)
      fun s5 hpc5 hrun5 hsp5 hcs5 hinv10 => ?_
    simp only [CalleeSavedPreserved] at hcs5
    simp (config := { decide := true }) only [arm64_norm, hsp4, h19_4, h20_4, h21_4, h22_4, h23_4, h24_4, h25_4, h26_4, h27_4, h28_4, h29_4] at hpc5 hsp5 hcs5
    obtain ⟨h19_5, h20_5, h21_5, h22_5, h23_5, h24_5, h25_5, h26_5, h27_5, h28_5, h29_5⟩ := hcs5
    simp (config := { decide := true }) only [x_new, arm64_norm, hsp4, htr4]
    refine SepWPp.exists_elim_top fun msgG => ?_
    refine SepWPp.pure_elim fun htr5 => ?_
    refine SepWPp.fold
      (Entails.of_eq (stackAt_sub (s0.sp - 640#64) (rootStack - 640) signalMessageNewStack).symm)
      (by sep_focus) ?_
    set msg := SignalMessageNewGhost.model C.F uuidTryParse x_new
    refine SepWPp.fold (signalMessageAt_unpack A msgG (s0.sp - 408#64) msg) (by sep_focus) ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hmsgPqCap => ?_
    have ⟨hmsgPqCap_beq, hmsgPqCap_eq⟩ := add_one_beq_zero_false_of_lt_2_63 hmsgPqCap
    refine SepWPp.exists_elim fun m7 => SepWPp.exists_elim fun m8 =>
      SepWPp.exists_elim fun m9 => SepWPp.exists_elim fun m10 =>
      SepWPp.exists_elim fun m11 => SepWPp.exists_elim fun m12 =>
      SepWPp.exists_elim fun m14 => ?_
    apply SepWPp.of_sepWP_callInv hinv10 (mid := entry + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::next_chain_key") - (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>")))
    refine SepWP.fold (Entails.of_eq (pre_nck_stack_split s0.sp)) (by sep_focus) ?_
    wp_simp_pre only [signalMessageWordsAt, bv_sub_add_lit, Nat.reduceSub,
      stackAt_sub (s0.sp - 640#64) (rootStack - 640) nextChainKeyStack,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro t13
    apply SepWP.exists_elim; intro t12
    apply SepWP.exists_elim; intro t11
    apply SepWP.exists_elim; intro t10
    apply SepWP.exists_elim; intro t9
    apply SepWP.exists_elim; intro t8
    apply SepWP.exists_elim; intro t7
    apply SepWP.exists_elim; intro t6
    apply SepWP.exists_elim; intro t5
    apply SepWP.exists_elim; intro t4
    apply SepWP.exists_elim; intro t3
    apply SepWP.exists_elim; intro t2
    apply SepWP.exists_elim; intro t1
    apply SepWP.exists_elim; intro t0
    apply SepWP.exists_elim; intro e2
    apply SepWP.exists_elim; intro e1
    apply SepWP.exists_elim; intro e0
    wp_steps
    refine SepWP.fold
      (pre_nck_fold s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
      (by sep_focus) ?_
    refine SepWP.fold
      (Entails.of_eq (chainKeyBytes_split (x.o + 152#64) x.ot.senderChainKey).symm)
      (by sep_focus) ?_
    apply SepWP.done
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm, hrun5])
    intro hinv11
    refine SepWPp.call_frame_inv
      (x := (x.o + 152#64, x.ot.senderChainKey, s0.sp - 408#64))
      hNCK hinv11
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm, hrun5])
      (by simp (config := { decide := true }) only [State.spAligned, arm64_norm, hsp5, hsp_align, hsp640_beq])
      rfl rfl
      ⟨⟨hinv11.1, hinv11.2⟩,
        by simp (config := { decide := true }) only [arm64_norm, hsp5, h19_5, h20_5, h21_5, h22_5, h23_5, h24_5, h25_5, h26_5, h27_5, h28_5, h29_5],
        by simp (config := { decide := true }) only [arm64_norm, hsp5, h19_5, h20_5, h21_5, h22_5, h23_5, h24_5, h25_5, h26_5, h27_5, h28_5, h29_5]⟩
      (by simp (config := { decide := true }) only [State.sp_writeReg64, State.sp_writeVReg128, State.sp_setPC, State.sp_setPState, State.sp_setMem, ite_true, ite_false, hsp5]; sep_focus)
      (fun _ _ _ _ => allowPanic_not_exited)
      (fun sf _ hm => onPanic_of_nck hsend (by simp (config := { decide := true }) only [arm64_norm, htr5]) hm)
      fun s6 hpc6 hrun6 hsp6 hcs6 hinv12 => ?_
    simp only [CalleeSavedPreserved] at hcs6
    simp (config := { decide := true }) only [arm64_norm, hsp5, h19_5, h20_5, h21_5, h22_5, h23_5, h24_5, h25_5, h26_5, h27_5, h28_5, h29_5] at hpc6 hsp6 hcs6
    obtain ⟨h19_6, h20_6, h21_6, h22_6, h23_6, h24_6, h25_6, h26_6, h27_6, h28_6, h29_6⟩ := hcs6
    simp (config := { decide := true }) only [arm64_norm, hsp5, htr5]
    refine SepWPp.pure_elim fun ⟨hnck_not_panic, htr6⟩ => ?_
    refine SepWPp.fold
      (Entails.of_eq (stackAt_sub (s0.sp - 640#64) (rootStack - 640) nextChainKeyStack).symm)
      (by sep_focus) ?_
    cases hnck : ChainKey.nextChainKey C.F x.ot.senderChainKey with
    | error e => dsimp only; exact SepWPp.false_elim
    | ok ck' =>
      dsimp only
      refine SepWPp.fold (chainKeyBytes_unpack (s0.sp - 408#64) ck') (by sep_focus) ?_
      refine SepWPp.exists_elim fun ck0 => SepWPp.exists_elim fun ck1 =>
        SepWPp.exists_elim fun ck2 => SepWPp.exists_elim fun ck3 => ?_
      simp (disch := decide) only [bv_sub_add_lit, Nat.reduceSub, sepConj_assoc]
      refine SepWPp.pure_elim fun hck => ?_
      refine SepWPp.fold (chainKeyBytes_unpack (x.o + 152#64) x.ot.senderChainKey) (by sep_focus) ?_
      refine SepWPp.exists_elim fun ock0 => SepWPp.exists_elim fun ock1 =>
        SepWPp.exists_elim fun ock2 => SepWPp.exists_elim fun ock3 => ?_
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      refine SepWPp.pure_elim fun _ => ?_
      refine SepWPp.fold (vecU8At_unpack_dealloc A x.o x.pqCap x.pqPtr x.ot.pqrState) (by sep_focus) ?_
      refine SepWPp.fold
        (pre_dealloc1_stack_fold s0.sp _ _ _ _ _ _ mk
          x.ot.senderRatchetKey.publicKey.bytes.toList (List.Vector.toList_length _))
        (by sep_focus) ?_
      simp only [sepConj_assoc]
      refine SepWPp.join_focus
        (fun s7 => s7.pc = entry + bv% (392) ∧ s7.status = .Running ∧ s7.sp = s0.sp - 640#64 ∧
          CalleeSavedPreserved s6 s7 ∧ CallInv img s7 ∧ s7.trace = s0.trace)
        (stackAt (s0.sp - 640#64) (rootStack - 640) ∗
          memRegion (s0.sp - 552#64) 144 ∗
          ((s0.sp - 408#64) ↦₆₄ ck0) ∗ ((s0.sp - 400#64) ↦₆₄ ck1) ∗
          ((s0.sp - 392#64) ↦₆₄ ck2) ∗ ((s0.sp - 384#64) ↦₆₄ ck3) ∗
          ((s0.sp - 376#64) ↦₃₂ ck'.index) ∗ memRegion (s0.sp - 372#64) 116 ∗
          (x.o ↦₆₄ x.pqCap) ∗ ((x.o + 8#64) ↦₆₄ x.pqPtr) ∗
          ((x.o + 152#64) ↦₆₄ ock0) ∗ ((x.o + 160#64) ↦₆₄ ock1) ∗
          ((x.o + 168#64) ↦₆₄ ock2) ∗ ((x.o + 176#64) ↦₆₄ ock3) ∗
          ((x.o + 184#64) ↦₃₂ x.ot.senderChainKey.index) ∗
          (if x.pqCap = 0 then emp else A.live x.pqPtr x.pqCap.toNat 1 ∗ memRegion x.pqPtr x.pqCap.toNat) ∗
          A.pool)
        (stackAt (s0.sp - 640#64) (rootStack - 640) ∗
          memRegion (s0.sp - 552#64) 296 ∗
          (x.o ↦₆₄ x.pqCap) ∗ ((x.o + 8#64) ↦₆₄ x.pqPtr) ∗
          ((x.o + 152#64) ↦ₛ chainKeyBytes ck') ∗
          A.pool)
        (by sep_focus)
        (fun R1 hjoin1 => by
          by_cases hpqCap : x.pqCap = 0
          · have hpqCap_beq : (x.pqCap == 0#64) = true := by simp [hpqCap]
            have hite : (if x.pqCap = 0 then emp else A.live x.pqPtr x.pqCap.toNat 1 ∗ memRegion x.pqPtr x.pqCap.toNat) = emp := by simp only [hpqCap, ↓reduceIte]
            rw [hite]
            simp only [emp_sepConj, sepConj_assoc]
            apply SepWPp.of_sepWP_callInv hinv12 (mid := entry + bv% (392))
            wp_steps
            refine SepWP.fold (post_dealloc1_copy_fold x.o s0.sp ck' ck0 ck1 ck2 ck3 hck) (by sep_focus) ?_
            apply SepWP.done
              (by simp (config := { decide := true }) only [arm64_norm])
              (by simp (config := { decide := true }) only [arm64_norm, hrun6])
            intro hinv13
            refine SepWPp.fold (Entails.refl _) (by sep_focus)
              (hjoin1 _ ⟨by simp (config := { decide := true }) only [arm64_norm],
                by simp (config := { decide := true }) only [arm64_norm, hrun6],
                by simp (config := { decide := true }) only [arm64_norm, hsp6],
                ?_, hinv13,
                by simp (config := { decide := true }) only [arm64_norm, htr6]⟩)
            simp only [CalleeSavedPreserved]
            simp (config := { decide := true }) only [arm64_norm]
          · have hpqCap_beq : (x.pqCap == 0#64) = false := Encrypt.beq_false_of_ne hpqCap
            have hite : (if x.pqCap = 0 then emp else A.live x.pqPtr x.pqCap.toNat 1 ∗ memRegion x.pqPtr x.pqCap.toNat) =
                (A.live x.pqPtr x.pqCap.toNat 1 ∗ memRegion x.pqPtr x.pqCap.toNat) := by simp only [hpqCap, ↓reduceIte]
            rw [hite]
            simp only [sepConj_assoc]
            apply SepWPp.of_sepWP_callInv hinv12 (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>"))
            wp_simp_pre only [stackAt_sub (s0.sp - 640#64) (rootStack - 640) allocHookStack, sepConj_assoc]
            wp_steps
            refine SepWP.fold (post_dealloc1_copy_fold x.o s0.sp ck' ck0 ck1 ck2 ck3 hck) (by sep_focus) ?_
            apply SepWP.done
              (by simp (config := { decide := true }) only [arm64_norm])
              (by simp (config := { decide := true }) only [arm64_norm, hrun6])
            intro hinv13
            refine SepWPp.call_frame_inv
              (x := (x.pqPtr, (x.pqCap.toNat, 1)))
              hDealloc hinv13
              (by simp (config := { decide := true }) only [arm64_norm])
              (by simp (config := { decide := true }) only [arm64_norm, hrun6])
              (by simp (config := { decide := true }) only [State.spAligned, arm64_norm, hsp_align, hsp6, hsp640_beq])
              rfl rfl
              ⟨by simp (config := { decide := true }) only [arm64_norm],
                by simp (config := { decide := true }) only [arm64_norm, BitVec.ofNat_toNat, BitVec.setWidth_eq],
                by simp (config := { decide := true }) only [arm64_norm]⟩
              (by simp (config := { decide := true }) only [State.sp_writeReg64, State.sp_writeVReg128, State.sp_setPC, State.sp_setPState, State.sp_setMem, ite_true, ite_false, hsp6]; sep_focus)
              (fun _ _ _ _ => allowPanic_not_exited)
              (fun sf _ hm => by
                simp only [sepConj_assoc, satisfies_pure_sepConj] at hm
                exact hm.1.elim)
              fun s7 hpc7 hrun7 hsp7 hcs7 hinv14 => ?_
            simp (config := { decide := true }) only [arm64_norm, hsp6, htr6] at hpc7 hsp7 ⊢
            refine SepWPp.pure_elim fun htr7 => ?_
            refine SepWPp.fold
              (Entails.of_eq (stackAt_sub (s0.sp - 640#64) (rootStack - 640) allocHookStack).symm)
              (by sep_focus) ?_
            refine SepWPp.fold (Entails.refl _) (by sep_focus) (hjoin1 s7 ⟨hpc7, hrun7, hsp7, ?_, hinv14, htr7⟩)
            simp only [CalleeSavedPreserved] at hcs7 ⊢
            simp (config := { decide := true }) only [arm64_norm, h19_6, h20_6, h21_6, h22_6, h23_6, h24_6, h25_6, h26_6, h27_6, h28_6, h29_6] at hcs7 ⊢
            exact hcs7)
        fun s7 ⟨hpc7, hrun7, hsp7, hcs7, hinv13, htr7⟩ => ?_
      simp only [CalleeSavedPreserved] at hcs7
      simp (config := { decide := true }) only [arm64_norm, h19_6, h20_6, h21_6, h22_6, h23_6, h24_6, h25_6, h26_6, h27_6, h28_6, h29_6] at hcs7
      obtain ⟨h19_7, h20_7, h21_7, h22_7, h23_7, h24_7, h25_7, h26_7, h27_7, h28_7, h29_7⟩ := hcs7
      have hsp7_align : s7.spAligned = true := by simp [State.spAligned, hsp7, hsp640]
      refine SepWPp.fold (vecU8Spare_dealloc A ctCap ctPtr ctext) (by sep_focus) ?_
      simp only [sepConj_assoc]
      refine SepWPp.pure_elim fun _ => ?_
      refine SepWPp.fold (vecU8Spare_dealloc A pqrMsgCap pqrMsgPtr pqrMsg) (by sep_focus) ?_
      simp only [sepConj_assoc]
      refine SepWPp.pure_elim fun _ => ?_
      apply SepWPp.of_sepWP_callInv hinv13 (mid := entry + bv% (456))
      refine SepWP.fold (Entails.of_eq (ret120_split_ok x.ret)) (by sep_focus) ?_
      wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWP.exists_elim; intro r14
      apply SepWP.exists_elim; intro r13
      apply SepWP.exists_elim; intro r12
      apply SepWP.exists_elim; intro r11
      apply SepWP.exists_elim; intro r10
      apply SepWP.exists_elim; intro r9
      apply SepWP.exists_elim; intro r8
      apply SepWP.exists_elim; intro r7
      apply SepWP.exists_elim; intro r6
      apply SepWP.exists_elim; intro r5
      apply SepWP.exists_elim; intro r4
      apply SepWP.exists_elim; intro r3
      apply SepWP.exists_elim; intro r2
      apply SepWP.exists_elim; intro r1
      apply SepWP.exists_elim; intro r0
      wp_steps
      refine SepWP.fold (msgResultAt_ok_pack A msgG x.ret msg m7 m8 m9 m10 m11 m12 m14) (by sep_focus) ?_
      refine SepWP.fold (otrAt_updated_pack A x.o newPqrCap newPqrPtr x.ot ck' newPqrState) (by sep_focus) ?_
      refine SepWP.fold (post_copy_stack_fold s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
      apply SepWP.done
        (by simp (config := { decide := true }) only [arm64_norm])
        (by simp (config := { decide := true }) only [arm64_norm, hrun7])
      intro hinv14
      refine SepWPp.join_focus
        (fun s8 => s8.pc = entry + bv% (480) ∧ s8.status = .Running ∧ s8.sp = s0.sp - 640#64 ∧
          s8.readReg64 (Reg.gpr 1#5) = pqrMsgCap ∧
          CalleeSavedPreserved s7 s8 ∧ CallInv img s8 ∧ s8.trace = s0.trace)
        (stackAt (s0.sp - 640#64) (rootStack - 640) ∗
          ((s0.sp - 576#64) ↦₆₄ newPqrCap) ∗ ((s0.sp - 568#64) ↦₆₄ pqrMsgCap) ∗
          (if ctCap = 0 then emp else A.live ctPtr ctCap.toNat 1 ∗ memRegion ctPtr ctCap.toNat) ∗
          A.pool)
        (stackAt (s0.sp - 640#64) (rootStack - 640) ∗
          memRegion (s0.sp - 576#64) 16 ∗
          A.pool)
        (by sep_focus)
        (fun R2 hjoin2 => by
          by_cases hctCap : ctCap = 0
          · have hctCap_beq : (ctCap == 0#64) = true := by simp [hctCap]
            have hite : (if ctCap = 0 then emp else A.live ctPtr ctCap.toNat 1 ∗ memRegion ctPtr ctCap.toNat) = emp := by simp only [hctCap, ↓reduceIte]
            rw [hite]
            simp only [emp_sepConj, sepConj_assoc]
            apply SepWPp.of_sepWP_callInv hinv14 (mid := entry + bv% (480))
            wp_steps
            refine SepWP.fold (pair_576_entails_memRegion s0.sp _ _) (by sep_focus) ?_
            apply SepWP.done
              (by simp (config := { decide := true }) only [arm64_norm])
              (by simp (config := { decide := true }) only [arm64_norm, hrun7])
            intro hinv15
            refine SepWPp.fold (Entails.refl _) (by sep_focus)
              (hjoin2 _ ⟨by simp (config := { decide := true }) only [arm64_norm],
                by simp (config := { decide := true }) only [arm64_norm, hrun7],
                by simp (config := { decide := true }) only [arm64_norm, hsp7],
                by simp (config := { decide := true }) only [arm64_norm],
                ?_, hinv15,
                by simp (config := { decide := true }) only [arm64_norm, htr7]⟩)
            simp only [CalleeSavedPreserved]
            simp (config := { decide := true }) only [arm64_norm]
          · have hctCap_beq : (ctCap == 0#64) = false := Encrypt.beq_false_of_ne hctCap
            have hite : (if ctCap = 0 then emp else A.live ctPtr ctCap.toNat 1 ∗ memRegion ctPtr ctCap.toNat) =
                (A.live ctPtr ctCap.toNat 1 ∗ memRegion ctPtr ctCap.toNat) := by simp only [hctCap, ↓reduceIte]
            rw [hite]
            simp only [sepConj_assoc]
            apply SepWPp.of_sepWP_callInv hinv14 (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>"))
            wp_simp_pre only [stackAt_sub (s0.sp - 640#64) (rootStack - 640) allocHookStack, sepConj_assoc]
            wp_steps
            apply SepWP.done
              (by simp (config := { decide := true }) only [arm64_norm])
              (by simp (config := { decide := true }) only [arm64_norm, hrun7])
            intro hinv15
            refine SepWPp.call_frame_inv
              (x := (ctPtr, (ctCap.toNat, 1)))
              hDealloc hinv15
              (by simp (config := { decide := true }) only [arm64_norm])
              (by simp (config := { decide := true }) only [arm64_norm, hrun7])
              (by simp (config := { decide := true }) only [State.spAligned, arm64_norm, hsp7_align, hsp_align, hsp7, hsp640_beq])
              rfl rfl
              ⟨by simp (config := { decide := true }) only [arm64_norm, h26_7],
                by simp (config := { decide := true }) only [arm64_norm, h25_7, BitVec.ofNat_toNat, BitVec.setWidth_eq],
                by simp (config := { decide := true }) only [arm64_norm]⟩
              (by simp (config := { decide := true }) only [State.sp_writeReg64, State.sp_writeVReg128, State.sp_setPC, State.sp_setPState, State.sp_setMem, ite_true, ite_false, hsp7]; sep_focus)
              (fun _ _ _ _ => allowPanic_not_exited)
              (fun sf _ hm => by
                simp only [sepConj_assoc, satisfies_pure_sepConj] at hm
                exact hm.1.elim)
              fun s8a hpc8a hrun8a hsp8a hcs8a hinv16 => ?_
            simp only [CalleeSavedPreserved] at hcs8a
            simp (config := { decide := true }) only [arm64_norm, hsp7, h19_7, h20_7, h21_7, h22_7, h23_7, h24_7, h25_7, h26_7, h27_7, h28_7, h29_7] at hpc8a hsp8a hcs8a
            obtain ⟨h19_8a, h20_8a, h21_8a, h22_8a, h23_8a, h24_8a, h25_8a, h26_8a, h27_8a, h28_8a, h29_8a⟩ := hcs8a
            simp (config := { decide := true }) only [arm64_norm, hsp7, htr7]
            refine SepWPp.pure_elim fun htr8a => ?_
            refine SepWPp.fold
              (Entails.of_eq (stackAt_sub (s0.sp - 640#64) (rootStack - 640) allocHookStack).symm)
              (by sep_focus) ?_
            have hsp8a_align : s8a.spAligned = true := by simp [State.spAligned, hsp8a, hsp640]
            apply SepWPp.of_sepWP_callInv hinv16 (mid := entry + bv% (480))
            wp_steps
            refine SepWP.fold (pair_576_entails_memRegion s0.sp _ _) (by sep_focus) ?_
            apply SepWP.done
              (by simp (config := { decide := true }) only [arm64_norm])
              (by simp (config := { decide := true }) only [arm64_norm, hrun8a])
            intro hinv17
            refine SepWPp.fold (Entails.refl _) (by sep_focus)
              (hjoin2 _ ⟨by simp (config := { decide := true }) only [arm64_norm],
                by simp (config := { decide := true }) only [arm64_norm, hrun8a],
                by simp (config := { decide := true }) only [arm64_norm, hsp8a],
                by simp (config := { decide := true }) only [arm64_norm],
                ?_, hinv17,
                by simp (config := { decide := true }) only [arm64_norm, htr8a]⟩)
            simp only [CalleeSavedPreserved]
            simp (config := { decide := true }) only [arm64_norm, h19_8a, h20_8a, h21_8a, h22_8a, h23_8a, h24_8a, h25_8a, h26_8a, h27_8a, h28_8a, h29_8a,
              h19_7, h20_7, h21_7, h22_7, h23_7, h24_7, h25_7, h26_7, h27_7, h28_7, h29_7])
        fun s8 ⟨hpc8, hrun8, hsp8, hx1_8, hcs8, hinv15, htr8⟩ => ?_
      simp only [CalleeSavedPreserved] at hcs8
      simp (config := { decide := true }) only [arm64_norm, h19_7, h20_7, h21_7, h22_7, h23_7, h24_7, h25_7, h26_7, h27_7, h28_7, h29_7] at hcs8
      obtain ⟨h19_8, h20_8, h21_8, h22_8, h23_8, h24_8, h25_8, h26_8, h27_8, h28_8, h29_8⟩ := hcs8
      have hsp8_align : s8.spAligned = true := by simp [State.spAligned, hsp8, hsp640]
      refine SepWPp.join_focus
        (fun s9 => s9.pc = entry + bv% (832) ∧ s9.status = .Running ∧ s9.sp = s0.sp - 640#64 ∧
          CalleeSavedPreserved s8 s9 ∧ CallInv img s9 ∧ s9.trace = s0.trace)
        (stackAt (s0.sp - 640#64) (rootStack - 640) ∗
          (if pqrMsgCap = 0 then emp else A.live pqrMsgPtr pqrMsgCap.toNat 1 ∗ memRegion pqrMsgPtr pqrMsgCap.toNat) ∗
          A.pool)
        (stackAt (s0.sp - 640#64) (rootStack - 640) ∗
          A.pool)
        (by sep_focus)
        (fun R3 hjoin3 => by
          by_cases hpqrMsgCap : pqrMsgCap = 0
          · have hpqrMsgCap_beq : (pqrMsgCap == 0#64) = true := by simp [hpqrMsgCap]
            have hite : (if pqrMsgCap = 0 then emp else A.live pqrMsgPtr pqrMsgCap.toNat 1 ∗ memRegion pqrMsgPtr pqrMsgCap.toNat) = emp := by simp only [hpqrMsgCap, ↓reduceIte]
            rw [hite]
            simp only [emp_sepConj, sepConj_assoc]
            apply SepWPp.of_sepWP_callInv hinv15 (mid := entry + bv% (832))
            wp_steps
            apply SepWP.done
              (by simp (config := { decide := true }) only [arm64_norm])
              (by simp (config := { decide := true }) only [arm64_norm, hrun8])
            intro hinv16
            refine SepWPp.fold (Entails.refl _) (by sep_focus)
              (hjoin3 _ ⟨by simp (config := { decide := true }) only [arm64_norm],
                by simp (config := { decide := true }) only [arm64_norm, hrun8],
                by simp (config := { decide := true }) only [arm64_norm, hsp8],
                ?_, hinv16,
                by simp (config := { decide := true }) only [arm64_norm, htr8]⟩)
            simp only [CalleeSavedPreserved]
            simp (config := { decide := true }) only [arm64_norm]
          · have hpqrMsgCap_beq : (pqrMsgCap == 0#64) = false := Encrypt.beq_false_of_ne hpqrMsgCap
            have hite : (if pqrMsgCap = 0 then emp else A.live pqrMsgPtr pqrMsgCap.toNat 1 ∗ memRegion pqrMsgPtr pqrMsgCap.toNat) =
                (A.live pqrMsgPtr pqrMsgCap.toNat 1 ∗ memRegion pqrMsgPtr pqrMsgCap.toNat) := by simp only [hpqrMsgCap, ↓reduceIte]
            rw [hite]
            simp only [sepConj_assoc]
            apply SepWPp.of_sepWP_callInv hinv15 (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>"))
            wp_simp_pre only [stackAt_sub (s0.sp - 640#64) (rootStack - 640) allocHookStack, sepConj_assoc]
            wp_steps
            apply SepWP.done
              (by simp (config := { decide := true }) only [arm64_norm])
              (by simp (config := { decide := true }) only [arm64_norm, hrun8])
            intro hinv16
            refine SepWPp.call_frame_inv
              (x := (pqrMsgPtr, (pqrMsgCap.toNat, 1)))
              hDealloc hinv16
              (by simp (config := { decide := true }) only [arm64_norm])
              (by simp (config := { decide := true }) only [arm64_norm, hrun8])
              (by simp (config := { decide := true }) only [State.spAligned, arm64_norm, hsp8_align, hsp_align, hsp8, hsp640_beq])
              rfl rfl
              ⟨by simp (config := { decide := true }) only [arm64_norm, h21_8],
                by simp (config := { decide := true }) only [arm64_norm, hx1_8, BitVec.ofNat_toNat, BitVec.setWidth_eq],
                by simp (config := { decide := true }) only [arm64_norm]⟩
              (by simp (config := { decide := true }) only [State.sp_writeReg64, State.sp_setPC, State.sp_setPState, State.sp_setMem, ite_true, ite_false, hsp8]; sep_focus)
              (fun _ _ _ _ => allowPanic_not_exited)
              (fun sf _ hm => by
                simp only [sepConj_assoc, satisfies_pure_sepConj] at hm
                exact hm.1.elim)
              fun s9 hpc9 hrun9 hsp9 hcs9 hinv17 => ?_
            simp (config := { decide := true }) only [arm64_norm, hsp8, htr8] at hpc9 hsp9 ⊢
            refine SepWPp.pure_elim fun htr9 => ?_
            refine SepWPp.fold
              (Entails.of_eq (stackAt_sub (s0.sp - 640#64) (rootStack - 640) allocHookStack).symm)
              (by sep_focus) ?_
            refine SepWPp.fold (Entails.refl _) (by sep_focus)
              (hjoin3 s9 ⟨hpc9, hrun9, hsp9, ?_, hinv17, htr9⟩)
            simp only [CalleeSavedPreserved] at hcs9 ⊢
            simp (config := { decide := true }) only [arm64_norm, h19_8, h20_8, h21_8, h22_8, h23_8, h24_8, h25_8, h26_8, h27_8, h28_8, h29_8] at hcs9 ⊢
            exact hcs9)
        fun s9 ⟨hpc9, hrun9, hsp9, hcs9, _, htr9⟩ => ?_
      simp only [CalleeSavedPreserved] at hcs9
      simp (config := { decide := true }) only [arm64_norm, h19_8, h20_8, h21_8, h22_8, h23_8, h24_8, h25_8, h26_8, h27_8, h28_8, h29_8] at hcs9
      obtain ⟨h19_9, h20_9, h21_9, h22_9, h23_9, h24_9, h25_9, h26_9, h27_9, h28_9, h29_9, hvregs9⟩ := hcs9
      have hsp9_align : s9.spAligned = true := by simp [State.spAligned, hsp9, hsp640]
      apply SepWPp.of_sepWP_ret
      wp_steps
      refine SepWP.fold (ok_branch_epilogue_stack s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
      rw [EncryptCoreFacts.model_of_send_some_ok_eq x C S newPqrState pqrKey pqrMsg ck' hnp1 hsend hnck (msg := msg) rfl]
      dsimp only
      apply EncryptCoreFacts.sepWP_done_encrypt
      · simp (config := { decide := true }) only [arm64_norm]
      · simp (config := { decide := true }) only [arm64_norm, hrun9]
      · exact ⟨by simp only [h43a_except_ok_ne_error_eq_true], by simp (config := { decide := true }) only [arm64_norm, htr9]⟩
      · sep_focus
      · simp (config := { decide := true }) only [arm64_norm, hsp9, BitVec.sub_add_cancel]
      · simp only [CalleeSavedPreserved]; simp (config := { decide := true }) only [arm64_norm, hvregs9]

/-- Instantiation of `otrEncrypt_body_ok_ext_frame` on `tripleRatchetProgAt`. -/
theorem otrEncrypt_body_ok_frame (Q : List (BitVec 8) → List (BitVec 8) → Prop) (F : SepProp)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (abs : String → Option (State → State)) (img : Obj.Image)
    (hHooks : TripleRatchetHooks C A S abs)
    (himg : Obj.Loads libsignalSessionImage img)
    (hSend : subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr spqrSendName)
      { spqrSendSpec A ctl S img with
        pre := fun x s => ⌜Q x.st.bytes x.rest⌝ ∗ F ∗ (spqrSendSpec A ctl S img).pre x s
        post := fun x s0 sf => F ∗ (spqrSendSpec A ctl S img).post x s0 sf })
    (hMK : MessageKeysOk img C A ctl abs)
    (hGK : GenerateKeysOk img C A ctl abs)
    (hNew : SignalMessageNewOk img C A ctl uuidTryParse abs)
    (hNCK : NextChainKeyOk img C ctl abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr otrEncryptName)
      { otrEncryptSpec C A ctl uuidTryParse S img with
        pre := fun x s =>
          ⌜Q x.ot.pqrState x.rest⌝ ∗ F ∗ (otrEncryptSpec C A ctl uuidTryParse S img).pre x s
        post := fun x s0 sf => F ∗ (otrEncryptSpec C A ctl uuidTryParse S img).post x s0 sf } :=
  otrEncrypt_body_ok_ext_frame Q F C A ctl S (tripleRatchetExterns C ctl abs) img
    (Stage2Contracts.of_tripleRatchetProgAt img.base C A ctl S abs hHooks) himg hSend hMK hGK hNew hNCK

/-- `OTR::encrypt` meets `otrEncryptSpecT` for any `S` whose `spqr::send` meets `spqrSendSpecT`. -/
theorem otrEncryptT_run_of_send (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) (img : Obj.Image)
    (hHooks : TripleRatchetHooks C A S abs)
    (himg : Obj.Loads libsignalSessionImage img)
    (hSend : subroutine_ok (tripleRatchetProg img C ctl abs) (entryOf img spqrSendName)
      (spqrSendSpecT A ctl S img))
    (hMK : MessageKeysOk img C A ctl abs)
    (hGK : GenerateKeysOk img C A ctl abs)
    (hNew : SignalMessageNewOk img C A ctl uuidTryParse abs)
    (hNCK : NextChainKeyOk img C ctl abs) :
    subroutine_ok (tripleRatchetProg img C ctl abs) (entryOf img otrEncryptName)
      (otrEncryptSpecT C A ctl uuidTryParse S img) := by
  apply root_of_tripleRatchetProgAt himg
  rw [tripleRatchetProg_eq_tripleRatchetProgAt himg,
    entryOf_eq_tripleRatchetProgAt (C := C) (ctl := ctl) (abs := abs) himg spqrSendName] at hSend
  exact otrEncrypt_body_ok_frame (fun pq rest => pq.length < 2 ^ 32 ∧ 64 ≤ rest.length)
    (TokenInit img) C A ctl S abs img hHooks himg hSend hMK hGK hNew hNCK

/-- Derives `OtrEncryptV1RunStmt` from `SpqrSendV1Stmt`. -/
theorem otrEncryptV1_run_of_sendV1 (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (K : MlKem)
    (abs : String → Option (State → State)) (img : Obj.Image)
    (hSendV1 : SpqrSendV1Stmt C A ctl K abs img) :
    OtrEncryptV1RunStmt C A ctl K abs img := by
  intro hHooks hSpqr himg
  obtain ⟨hMK, hGK, hNew, hNCK⟩ :=
    CryptoVerification.LibsignalTripleRatchet.Statements.encryptCallees C A ctl (spqrV1 C.F K) abs img hHooks himg
  exact otrEncryptT_run_of_send C A ctl (spqrV1 C.F K) abs img hHooks himg
    (hSendV1 hHooks hSpqr himg) hMK hGK hNew hNCK

end CryptoVerification.LibsignalSpqrV1.M4
