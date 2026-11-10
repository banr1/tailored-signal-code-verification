/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Acknowledged3
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Acknowledged1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1AcknowledgedExt1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.Dispatch
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` — `.ct1Acknowledged` Arm (`AllocContractsX`, Part 2)

**Checked by Lean.** Lifts `call_ct1AcknowledgedRecvEkChunk`, `ct1Ack_ek_4448_ret`, and the
top-level `.ct1Acknowledged` arm (`tag = 11#64`) to `AllocContractsX img A ext` and
`DeallocOkExt img.base A ext` at `statesRecvStackXExt` (`40176` B).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.NextChunk
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff

local elab "sep_ac_rfl_ct1Ack2_ext" : tactic => do
  let g ← _root_.Lean.Elab.Tactic.getMainGoal
  g.withContext do
    let ty := (← _root_.Lean.instantiateMVars (← g.getType)).consumeMData
    let some (_, lhs, rhs) := ty.eq?
      | _root_.Lean.throwError "sep_ac_rfl_ct1Ack2_ext: expected equality"
    if lhs == rhs then
      g.assign (← _root_.Lean.Meta.mkEqRefl lhs)
      _root_.Lean.Elab.Tactic.replaceMainGoal []
    else if let some (tbl, tA, tB) := ProofLib.SepSolver.synReifyPermTbl? lhs rhs then
      g.assign (← ProofLib.SepSolver.eqACOfTbl lhs rhs tbl tA tB)
      _root_.Lean.Elab.Tactic.replaceMainGoal []
    else
      _root_.Lean.Elab.Tactic.evalTactic (← `(tactic| sep_frame))

private theorem ct1Ack_stackAt_calleeExt_split (sp : BitVec 64) :
    stackAt sp statesRecvCalleeStackXExt =
      memRegion (sp - BitVec.ofNat 64 statesRecvCalleeStackXExt)
        (statesRecvCalleeStackXExt - ct1AcknowledgedRecvEkChunkStack) ∗
      stackAt sp ct1AcknowledgedRecvEkChunkStack := by
  have h := ProofLib.stackAt_split_bottom sp ct1AcknowledgedRecvEkChunkStack
    (statesRecvCalleeStackXExt - ct1AcknowledgedRecvEkChunkStack) (by decide)
  rwa [Nat.add_sub_of_le (by decide : ct1AcknowledgedRecvEkChunkStack ≤ statesRecvCalleeStackXExt)] at h

theorem call_ct1AcknowledgedRecvEkChunk_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    {entry ret_pc : BitVec 64}
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hcall : subroutine_ok (tripleRatchetProgAtExt img.base ext) entry
      (({ pre := fun x s =>
            (ct1AcknowledgedRecvEkChunkSpec A F K img.base).pre x s ∗
              memRegion (s.sp - BitVec.ofNat 64 statesRecvCalleeStackXExt)
                (statesRecvCalleeStackXExt - ct1AcknowledgedRecvEkChunkStack)
          post := fun x s0 sf =>
            (ct1AcknowledgedRecvEkChunkSpec A F K img.base).post x s0 sf ∗
              memRegion (s0.sp - BitVec.ofNat 64 statesRecvCalleeStackXExt)
                (statesRecvCalleeStackXExt - ct1AcknowledgedRecvEkChunkStack)
          onPanic := (ct1AcknowledgedRecvEkChunkSpec A F K img.base).onPanic : Spec _ }).inImage img))
    (outA stA chunkA : BitVec 64)
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk)
    (res : Except Error (Chunked.SendCt.Ct1AcknowledgedRecvChunk spqrPolyApi (spqrAuthApi F)))
    (hstrict : PolyDecoderStrictSorted st.receiving_ek)
    (hrecv : st.recv_ek_chunk K st.uc.epoch chunk = StatesResult.ofError res)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post Q_panic : State → SepProp → Prop}
    (hinv_img : ImgCallInv img s)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 Reg.x0 = outA) (hx1 : s.readReg64 Reg.x1 = stA)
    (hx2 : s.readReg64 Reg.x2 = st.uc.epoch) (hx3 : s.readReg64 Reg.x3 = chunkA)
    (hsplit : P = (memRegion outA 528 ∗
      chunkedCt1AcknowledgedAt A stA st ∗ chunkAt chunkA chunk ∗
      unchunkedSendCt2RoAt img.base ∗ tokenInitAt img.base ∗ reduceTableAt img.base ∗
      A.pool ∗ stackAt sp_call statesRecvCalleeStackXExt) ∗ Frame)
    (hpanic : ∀ sf P_f,
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) →
      Q_panic sf P_f)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → TraceCalleeSaved sf s0 →
      ImgCallInv img sf →
      SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 Reg.lr) sf
        ((ct1AcknowledgedRecvEkChunkResAt A outA res ∗
          memRegion stA 528 ∗ chunkAt chunkA chunk ∗
          unchunkedSendCt2RoAt img.base ∗ tokenInitAt img.base ∗ reduceTableAt img.base ∗
          A.pool ∗ stackAt sp_call statesRecvCalleeStackXExt) ∗ Frame) post) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 Reg.lr) s P post Q_panic := by
  refine SepWPp.call_imgInv hcall hinv_img
    (x := ⟨outA, stA, chunkA, st, chunk, res⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ => hpanic sf _ fun hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hinv_sf => ?_)
  · intro R' hm
    refine satisfies_inImage_pre hinv_img ?_
    rw [hsplit] at hm
    dsimp only [ct1AcknowledgedRecvEkChunkSpec]
    rw [hsp]
    rw [ct1Ack_stackAt_calleeExt_split sp_call] at hm
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hb, hx0, hx1, hx2, hx3, hstrict, hrecv⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl_ct1Ack2_ext)) hm⟩
  · dsimp only [Spec.inImage, ct1AcknowledgedRecvEkChunkSpec] at hmem
    refine allowPanic_frame (fun ⟨haf, htr_sub⟩ => ?_) hmem
    unfold allocFailedIn at haf ⊢
    rw [htrace.1] at haf htr_sub
    exact ⟨haf, htr_sub⟩
  · dsimp only [Spec.inImage, ct1AcknowledgedRecvEkChunkSpec]
    simp only [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    apply SepWPp.of_sepWP_ret
    refine SepWP.weaken_pre ?_
      (hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf
        ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩ hinv_sf)
    rw [ct1Ack_stackAt_calleeExt_split sp_call]
    exact Entails.of_eq (by sep_ac_rfl_ct1Ack2_ext)

theorem ct1Ack_ek_4448_ret_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hAx : AllocContractsX img A ext)
    (hcall : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ct1AcknowledgedRecvEkChunkName)
      (({ pre := fun x s =>
            (ct1AcknowledgedRecvEkChunkSpec A F K img.base).pre x s ∗
              memRegion (s.sp - BitVec.ofNat 64 statesRecvCalleeStackXExt)
                (statesRecvCalleeStackXExt - ct1AcknowledgedRecvEkChunkStack)
          post := fun x s0 sf =>
            (ct1AcknowledgedRecvEkChunkSpec A F K img.base).post x s0 sf ∗
              memRegion (s0.sp - BitVec.ofNat 64 statesRecvCalleeStackXExt)
                (statesRecvCalleeStackXExt - ct1AcknowledgedRecvEkChunkStack)
          onPanic := (ct1AcknowledgedRecvEkChunkSpec A F K img.base).onPanic : Spec _ }).inImage img))
    (s0 s4 : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk)
    (w : Words66) (sp : SendEkSpills) (P_msg_rest R : SepProp)
    (hinv4 : ImgCallInv img s4)
    (hlen : st.receiving_ek.pts.length = 16)
    (hinv : statesRecvPreInv (F := F) (.ct1Acknowledged st))
    (hrecv_eq : ∀ res, st.recv_ek_chunk K st.uc.epoch chunk = StatesResult.ofError res →
      States.recv K (.ct1Acknowledged st) msg = ct1AckRecvChunkToStatesResult res)
    (hmsg_recomp : chunkAt (msgA + 10#64) chunk ∗ P_msg_rest ⊢ messageAt spqrPolyApi msgA msg)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc4 : s4.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 4448#64)
    (hrun4 : s4.status = .Running)
    (hsp4 : s4.sp = s0.sp - 4240#64)
    (hx2_4 : s4.readReg64 .x2 = st.uc.epoch)
    (hx19_4 : s4.readReg64 .x19 = outA)
    (hx20_4 : s4.readReg64 .x20 = selfA)
    (hx24_4 : s4.readReg64 .x24 = msgA)
    (htr4 : TraceCalleeSaved s4 s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 Reg.lr) s4
      (memRegion (s0.sp - 40176#64) 16384 ∗
       chunkAt (msgA + 10#64) chunk ∗ P_msg_rest ∗
       (selfA ↦₆₄ 11#64) ∗ words66At (selfA + 8#64) w ∗
       relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst st) (wordsBytes (words66List w)) ∗
       memRegion (selfA + 536#64) 392 ∗
       words66At ((s0.sp - 4240#64) + 976#64) w ∗ memRegion ((s0.sp - 4240#64) + 1504#64) 352 ∗
       statesRecvRoAt img.base ∗ memRegion outA v1RecvSize ∗ A.pool ∗
       stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
       sendEkSpillsAt (s0.sp - 4240#64) sp ∗ memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
       memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗ sendEkUnusedAt (s0.sp - 4240#64) ∗
       statesRecvSavedCells s0)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (statesRecvVariantSpecExt A F K img.base (.ct1Acknowledged st) msg).post
            (outA, selfA, msgA) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (statesRecvVariantSpecExt A F K img.base (.ct1Acknowledged st) msg).onPanic
            (outA, selfA, msgA) s0 sf ∗ R)) := by
  set fsp := s0.sp - 4240#64
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  obtain ⟨res, hrecv, herr⟩ :=
    ct1Acknowledged_recv_ek_chunk_cases_of_preInv K st chunk hlen hinv
  have hres_eq : States.recv K (.ct1Acknowledged st) msg = ct1AckRecvChunkToStatesResult res :=
    hrecv_eq res hrecv
  refine ct1Ack_sepWPp_seq_clean_inImage hinv4
    (ct1Ack_step_4448_call s4 fsp selfA msgA st.uc.epoch _ hpc4 hrun4 hsp4 hx2_4 hx20_4 hx24_4) ?_
  intro s5 hpc5 hrun5 hinv5 ⟨hsp5, hx0_5, hx1_5, hx2_5, hx3_5, hx19_5, hx20_5, _, _, hx30_5, htr5⟩
  have hx19_5' : s5.readReg64 .x19 = outA := hx19_5.trans hx19_4
  have htr5' : TraceCalleeSaved s5 s0 := htr5.trans htr4
  have hpre_call :
      memRegion (s0.sp - 40176#64) 16384 ∗
      chunkAt (msgA + 10#64) chunk ∗ P_msg_rest ∗
      (selfA ↦₆₄ 11#64) ∗ words66At (selfA + 8#64) w ∗
      relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst st) (wordsBytes (words66List w)) ∗
      memRegion (selfA + 536#64) 392 ∗
      words66At (fsp + 976#64) w ∗ memRegion (fsp + 1504#64) 352 ∗
      statesRecvRoAt img.base ∗ memRegion outA v1RecvSize ∗ A.pool ∗
      stackAt fsp statesRecvCalleeStackX ∗
      sendEkSpillsAt fsp sp ∗ memRegion (fsp + 576#64) 376 ∗
      memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗
      statesRecvSavedCells s0 ⊢
      (memRegion (fsp + 1856#64) 528 ∗
       chunkedCt1AcknowledgedAt A (selfA + 8#64) st ∗ chunkAt (msgA + 10#64) chunk ∗
       unchunkedSendCt2RoAt img.base ∗ tokenInitAt img.base ∗ reduceTableAt img.base ∗
       A.pool ∗ stackAt fsp statesRecvCalleeStackXExt) ∗
      (P_msg_rest ∗ statesRecvJumpTableAt img.base ∗
       memRegion outA v1RecvSize ∗
       (selfA ↦₆₄ 11#64) ∗ memRegion (selfA + 536#64) 392 ∗
       sendEkSpillsAt fsp sp ∗ memRegion (fsp + 576#64) 376 ∗
       memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 2384#64) 352 ∗
       sendEkUnusedAt fsp ∗ statesRecvSavedCells s0) := by
    have hrecomp := recompose66_ct1Acknowledged A (selfA + 8#64) w st
    have h976 := words66At_976_352_entails_memRegion_880 fsp w
    dsimp only [statesRecvRoAt, fsp]
    rw [stackAt_statesRecvCalleeExt_eq_X s0.sp,
        memRegion_880_split_528_352 (s0.sp - 4240#64)]
    refine Entails.trans (Entails.of_eq (show _ =
      ((words66At (selfA + 8#64) w ∗
        relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst st) (wordsBytes (words66List w))) ∗
       (words66At ((s0.sp - 4240#64) + 976#64) w ∗ memRegion ((s0.sp - 4240#64) + 1504#64) 352)) ∗
      (memRegion (s0.sp - 40176#64) 16384 ∗
       memRegion ((s0.sp - 4240#64) + 1856#64) 528 ∗ chunkAt (msgA + 10#64) chunk ∗
       unchunkedSendCt2RoAt img.base ∗ tokenInitAt img.base ∗ reduceTableAt img.base ∗
       A.pool ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
       P_msg_rest ∗ statesRecvJumpTableAt img.base ∗
       memRegion outA v1RecvSize ∗
       (selfA ↦₆₄ 11#64) ∗ memRegion (selfA + 536#64) 392 ∗
       sendEkSpillsAt (s0.sp - 4240#64) sp ∗ memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
       memRegion ((s0.sp - 4240#64) + 2384#64) 352 ∗
       sendEkUnusedAt (s0.sp - 4240#64) ∗ statesRecvSavedCells s0) by sep_ac_rfl_ct1Ack2_ext)) ?_
    exact Entails.trans (sepConj_mono_left (sepConj_mono hrecomp h976)) (Entails.of_eq (by sep_ac_rfl_ct1Ack2_ext))
  refine SepWPp.weaken_pre hpre_call ?_
  refine call_ct1AcknowledgedRecvEkChunk_ext (R := R) hb hcall
    (fsp + 1856#64) (selfA + 8#64) (msgA + 10#64) st chunk res
    hinv.1 hrecv hinv5 hpc5 hrun5 hsp5 hfsp_align hx30_5 htr5' hx0_5 hx1_5 hx2_5 hx3_5 rfl
    (fun sf Pf h hmem => by
      have h1 := h hmem
      dsimp only [statesRecvVariantSpecExt, statesRecvOnPanic]
      rw [sepConj_assoc, satisfies_pure_sepConj] at h1 ⊢
      exact ⟨⟨Or.inr h1.1.1, h1.1.2⟩, h1.2⟩) ?_
  intro s6 hpc6 hrun6 hsp6 hcs6 htr6 hinv6
  have hx19_6 : s6.readReg64 .x19 = outA := hcs6.1.trans hx19_5'
  have hx20_6 : s6.readReg64 .x20 = fsp + 1856#64 := hcs6.2.1.trans hx20_5
  have hself := selfA_11_528_392_entails_memRegion selfA
  cases res with
  | error err =>
    have he : err = .erroneousDataReceived := herr err rfl
    subst he
    have hret := ct1Ack_err_4468_ret (A := A) (F := F) s0 s6 outA selfA .erroneousDataReceived sp
      (memRegion (s0.sp - 40176#64) 16384 ∗
       messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base ∗ A.pool)
      hsp0_align hpc6 hrun6 hsp6 hx19_6 htr6
    refine SepWP.weaken_pre ?_ (SepWP.mono hret ?_)
    · refine Entails.trans (Entails.of_eq (show _ =
        ((selfA ↦₆₄ 11#64) ∗ memRegion (selfA + 8#64) 528 ∗ memRegion (selfA + 536#64) 392) ∗
        (chunkAt (msgA + 10#64) chunk ∗ P_msg_rest) ∗
        ((statesRecvJumpTableAt img.base ∗ unchunkedSendCt2RoAt img.base ∗
          tokenInitAt img.base ∗ reduceTableAt img.base) ∗
         A.pool ∗ memRegion outA v1RecvSize ∗
         ct1AcknowledgedRecvEkChunkResAt A (F := F) (fsp + 1856#64) (.error .erroneousDataReceived) ∗
         stackAt fsp statesRecvCalleeStackXExt ∗
         sendEkSpillsAt fsp sp ∗ memRegion (fsp + 576#64) 376 ∗
         memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 2384#64) 352 ∗
         sendEkUnusedAt fsp ∗ statesRecvSavedCells s0) by sep_ac_rfl_ct1Ack2_ext)) ?_
      exact Entails.trans (sepConj_mono hself (sepConj_mono_left hmsg_recomp))
        (Entails.of_eq (by
          dsimp only [statesRecvRoAt, fsp]
          rw [stackAt_statesRecvCalleeExt_eq_X s0.sp]
          sep_ac_rfl_ct1Ack2_ext))
    · intro sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩
      refine ⟨fun hmem_f => ?_, hsp_sf, hcs_sf⟩
      dsimp only [statesRecvVariantSpecExt]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨htr_sf, Satisfies.mono (Entails.trans (sepConj_mono_left hPf) ?_) hmem_f⟩
      rw [hres_eq, stackAt_statesRecvStackXExt_eq_X s0.sp]
      dsimp only [ct1AckRecvChunkToStatesResult]
      exact Entails.of_eq (by sep_ac_rfl_ct1Ack2_ext)
  | ok chunkRes =>
    cases chunkRes with
    | stillReceiving outSt =>
      have hret := ct1Ack_still_4468_ret_ext (A := A) hAx s0 s6 outA selfA outSt sp
        (memRegion (s0.sp - 40176#64) 16384 ∗
         messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base ∗ A.pool)
        hinv6 hsp0_align hpc6 hrun6 hsp6 hx19_6 hx20_6 htr6
      refine SepWP.weaken_pre ?_ (SepWP.mono hret ?_)
      · refine Entails.trans (Entails.of_eq (show _ =
          ((selfA ↦₆₄ 11#64) ∗ memRegion (selfA + 8#64) 528 ∗ memRegion (selfA + 536#64) 392) ∗
          (chunkAt (msgA + 10#64) chunk ∗ P_msg_rest) ∗
          ((statesRecvJumpTableAt img.base ∗ unchunkedSendCt2RoAt img.base ∗
            tokenInitAt img.base ∗ reduceTableAt img.base) ∗
           A.pool ∗ memRegion outA v1RecvSize ∗
           ct1AcknowledgedRecvEkChunkResAt A (F := F) (fsp + 1856#64) (.ok (.stillReceiving outSt)) ∗
           stackAt fsp statesRecvCalleeStackXExt ∗
           sendEkSpillsAt fsp sp ∗ memRegion (fsp + 576#64) 376 ∗
           memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 2384#64) 352 ∗
           sendEkUnusedAt fsp ∗ statesRecvSavedCells s0) by sep_ac_rfl_ct1Ack2_ext)) ?_
        exact Entails.trans (sepConj_mono hself (sepConj_mono_left hmsg_recomp))
          (Entails.of_eq (by
            dsimp only [statesRecvRoAt, fsp]
            rw [stackAt_statesRecvCalleeExt_eq_X s0.sp]
            sep_ac_rfl_ct1Ack2_ext))
      · intro sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩
        refine ⟨fun hmem_f => ?_, hsp_sf, hcs_sf⟩
        dsimp only [statesRecvVariantSpecExt]
        rw [sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨htr_sf, Satisfies.mono (Entails.trans (sepConj_mono_left hPf) ?_) hmem_f⟩
        rw [hres_eq, stackAt_statesRecvStackXExt_eq_X s0.sp]
        dsimp only [ct1AckRecvChunkToStatesResult]
        exact Entails.of_eq (by sep_ac_rfl_ct1Ack2_ext)
    | done outSt =>
      have hret := ct1Ack_done_4468_ret_ext (A := A) hb hAx s0 s6 outA selfA outSt sp
        (memRegion (s0.sp - 40176#64) 16384 ∗
         messageAt spqrPolyApi msgA msg ∗ statesRecvJumpTableAt img.base ∗
         tokenInitAt img.base ∗ reduceTableAt img.base ∗ A.pool)
        hinv6 hsp0_align hpc6 hrun6 hsp6 hx19_6 hx20_6 htr6
      refine SepWP.weaken_pre ?_ (SepWP.mono hret ?_)
      · refine Entails.trans (Entails.of_eq (show _ =
          ((selfA ↦₆₄ 11#64) ∗ memRegion (selfA + 8#64) 528 ∗ memRegion (selfA + 536#64) 392) ∗
          (chunkAt (msgA + 10#64) chunk ∗ P_msg_rest) ∗
          ((statesRecvJumpTableAt img.base ∗ tokenInitAt img.base ∗ reduceTableAt img.base ∗ A.pool) ∗
           unchunkedSendCt2RoAt img.base ∗
           memRegion outA v1RecvSize ∗
           ct1AcknowledgedRecvEkChunkResAt A (F := F) (fsp + 1856#64) (.ok (.done outSt)) ∗
           stackAt fsp statesRecvCalleeStackXExt ∗
           sendEkSpillsAt fsp sp ∗ memRegion (fsp + 576#64) 376 ∗
           memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 2384#64) 352 ∗
           sendEkUnusedAt fsp ∗ statesRecvSavedCells s0) by sep_ac_rfl_ct1Ack2_ext)) ?_
        exact Entails.trans (sepConj_mono hself (sepConj_mono_left hmsg_recomp))
          (Entails.of_eq (by
            dsimp only [fsp]
            rw [stackAt_statesRecvCalleeExt_eq_X s0.sp]
            sep_ac_rfl_ct1Ack2_ext))
      · intro sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩
        refine ⟨fun hmem_f => ?_, hsp_sf, hcs_sf⟩
        dsimp only [statesRecvVariantSpecExt, statesRecvRoAt]
        rw [sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨htr_sf, Satisfies.mono (Entails.trans (sepConj_mono_left hPf) ?_) hmem_f⟩
        rw [hres_eq, stackAt_statesRecvStackXExt_eq_X s0.sp]
        dsimp only [ct1AckRecvChunkToStatesResult]
        exact Entails.of_eq (by sep_ac_rfl_ct1Ack2_ext)

/-- Per-variant `.inImage img` specification proof for `States.ct1Acknowledged st` (`tag = 11#64`)
    at `statesRecvStackXExt` (`40176` B) under `AllocContractsX img A ext` and
    `DeallocOkExt img.base A ext`. -/
theorem states_recv_ct1Acknowledged_ok_x_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext)
    (hdealloc : DeallocOkExt img.base A ext)
    (hcall : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ct1AcknowledgedRecvEkChunkName)
      (({ pre := fun x s =>
            (ct1AcknowledgedRecvEkChunkSpec A F K img.base).pre x s ∗
              memRegion (s.sp - BitVec.ofNat 64 statesRecvCalleeStackXExt)
                (statesRecvCalleeStackXExt - ct1AcknowledgedRecvEkChunkStack)
          post := fun x s0 sf =>
            (ct1AcknowledgedRecvEkChunkSpec A F K img.base).post x s0 sf ∗
              memRegion (s0.sp - BitVec.ofNat 64 statesRecvCalleeStackXExt)
                (statesRecvCalleeStackXExt - ct1AcknowledgedRecvEkChunkStack)
          onPanic := (ct1AcknowledgedRecvEkChunkSpec A F K img.base).onPanic : Spec _ }).inImage img))
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName)
      ((statesRecvVariantSpecExt A F K img.base (.ct1Acknowledged st) msg).inImage img) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨outA, selfA, msgA⟩ R s0 hpc0 hrun0 hpre hsp0_align
  simp only [Spec.inImage, statesRecvVariantSpecExt, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF0, hsym0⟩, ⟨hb, hx0, hx1, hx2, hinv⟩, hmem⟩
  have hinv0 : ImgCallInv img s0 := ⟨hF0, hsym0⟩
  refine ⟨stackAt s0.sp statesRecvStackX ∗
      (memRegion (s0.sp - 40176#64) 16384 ∗
       memRegion outA v1RecvSize ∗
       chunkedStatesAt A selfA (.ct1Acknowledged st) ∗
       messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base ∗ A.pool),
    R, Satisfies.mono (Entails.of_eq (by rw [stackAt_statesRecvStackXExt_eq_X s0.sp]; sep_ac_rfl_ct1Ack2_ext)) hmem, ?_⟩
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  set fsp := s0.sp - 4240#64
  have hpro := states_recv_prologue (b := img.base) (ext := ext) s0
    (memRegion (s0.sp - 40176#64) 16384 ∗
     memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ct1Acknowledged st) ∗
     messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base ∗ A.pool) hsp0_align hpc0 hrun0
  refine ct1Ack_sepWPp_seq_clean_inImage hinv0 hpro ?_
  intro s1 hpc1 hrun1 hinv1 ⟨hsp1, hx0_1, hx1_1, hx2_1, _, hx29_1, htr1⟩
  rw [hx0] at hx0_1; rw [hx1] at hx1_1; rw [hx2] at hx2_1
  dsimp only [chunkedStatesAt]
  have hdisp := states_recv_dispatch_ct1Acknowledged hb s1 fsp selfA
    (memRegion (s0.sp - 40176#64) 16384 ∗
     chunkedCt1AcknowledgedAt A (selfA + 8#64) st ∗ memRegion (selfA + 536#64) 392 ∗
     memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ A.pool ∗
     stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 4144 ∗
     statesRecvSavedCells s0)
    hpc1 hrun1 hsp1 hx1_1
  refine ct1Ack_sepWPp_seq_clean_inImage hinv1
    (SepWP.weaken_pre (Entails.of_eq (by dsimp only [fsp]; sep_ac_rfl_ct1Ack2_ext)) hdisp) ?_
  intro s2 hpc2 hrun2 hinv2 ⟨hsp2, hx0_2, hx1_2, hx2_2, _, _, _, hx19_2, _, hx24_2, _, hx29_2, htr2⟩
  rw [hx0_1] at hx19_2; rw [hx2_1] at hx24_2
  have htr20 : TraceCalleeSaved s2 s0 := htr2.trans htr1
  have hpre_split :
      (selfA ↦₆₄ 11#64) ∗ statesRecvRoAt img.base ∗
      (memRegion (s0.sp - 40176#64) 16384 ∗
       chunkedCt1AcknowledgedAt A (selfA + 8#64) st ∗ memRegion (selfA + 536#64) 392 ∗
       memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ A.pool ∗
       stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 4144 ∗ statesRecvSavedCells s0) ⊢
      (∃∗ w : Words66, ∃∗ sp : SendEkSpills,
        ⌜st.receiving_ek.pts.length = 16 ∧ (w.b0.w0.toNat < 2 ^ 63 ∧ w.b1.w5 = st.uc.epoch)⌝ ∗
        (memRegion (fsp + 976#64) 528 ∗ words66At (selfA + 8#64) w ∗
         stackAt fsp statesRecvCalleeStackX ∗
         (memRegion (s0.sp - 40176#64) 16384 ∗
          (msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ ct1AckPayloadTag msg.payload) ∗
          ct1AckPayloadTailAt msgA msg.payload ∗
          (selfA ↦₆₄ 11#64) ∗
          relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst st) (wordsBytes (words66List w)) ∗
          memRegion (selfA + 536#64) 392 ∗
          statesRecvRoAt img.base ∗ memRegion outA v1RecvSize ∗ A.pool ∗
          sendEkSpillsAt fsp sp ∗
          memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 1504#64) 352 ∗
          memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0))) := by
    rw [messageAt_eq_epoch_ct1AckTag_tail msgA msg]
    have hex66 : chunkedCt1AcknowledgedAt A (selfA + 8#64) st ⊢
        ∃∗ w : Words66,
          ⌜st.receiving_ek.pts.length = 16 ∧ (w.b0.w0.toNat < 2 ^ 63 ∧ w.b1.w5 = st.uc.epoch)⌝ ∗
          words66At (selfA + 8#64) w ∗
          relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst st) (wordsBytes (words66List w)) := by
      refine Entails.trans (chunkedCt1AcknowledgedAt_entails_pts_length_16 A (selfA + 8#64) st) ?_
      apply Entails.pure_left; intro hlen
      refine Entails.trans (chunkedCt1AcknowledgedAt_extract66 A (selfA + 8#64) st) ?_
      apply Entails.sepExists_elim; intro w
      apply Entails.pure_left; intro hw
      exact Entails.sepExists_right w (Entails.pure_right ⟨hlen, hw⟩ (Entails.refl _))
    have hstk : memRegion fsp 4144 ⊢
        ∃∗ sp : SendEkSpills,
          sendEkSpillsAt fsp sp ∗ memRegion (fsp + 576#64) 376 ∗
          memRegion (fsp + 976#64) 528 ∗ memRegion (fsp + 1504#64) 352 ∗
          memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp := by
      refine Entails.trans (memRegion_4144_entails_sendEkFrame fsp) ?_
      apply Entails.sepExists_elim; intro sp
      rw [memRegion_976_880_split_528_352 fsp]
      exact Entails.sepExists_right sp (Entails.of_eq (by sep_ac_rfl_ct1Ack2_ext))
    refine Entails.trans (Entails.of_eq (show _ =
      chunkedCt1AcknowledgedAt A (selfA + 8#64) st ∗ memRegion fsp 4144 ∗
      (memRegion (s0.sp - 40176#64) 16384 ∗
       (selfA ↦₆₄ 11#64) ∗ statesRecvRoAt img.base ∗ memRegion (selfA + 536#64) 392 ∗
       memRegion outA v1RecvSize ∗
       ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ ct1AckPayloadTag msg.payload) ∗
        ct1AckPayloadTailAt msgA msg.payload) ∗
       A.pool ∗ stackAt fsp statesRecvCalleeStackX ∗ statesRecvSavedCells s0) by sep_ac_rfl_ct1Ack2_ext)) ?_
    refine Entails.trans (sepConj_mono hex66 (sepConj_mono_left hstk)) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro sp
    apply Entails.sepExists_elim; intro w
    exact Entails.sepExists_right w (Entails.sepExists_right sp (Entails.of_eq (by sep_ac_rfl_ct1Ack2_ext)))
  refine SepWPp.weaken_pre hpre_split ?_
  apply ct1Ack_sepWPp_intro_ex hrun2; intro w
  apply ct1Ack_sepWPp_intro_ex hrun2; intro sp
  apply SepWPp.pure_left; rintro ⟨hlen, _, hep⟩
  refine ct1Ack_sepWPp_seq_clean_inImage hinv2 (ct1Ack_step_588_608_ext hAx s2 fsp outA selfA msgA w
    (memRegion (s0.sp - 40176#64) 16384 ∗
     (msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ ct1AckPayloadTag msg.payload) ∗
     ct1AckPayloadTailAt msgA msg.payload ∗
     (selfA ↦₆₄ 11#64) ∗
     relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst st) (wordsBytes (words66List w)) ∗
     memRegion (selfA + 536#64) 392 ∗
     statesRecvRoAt img.base ∗ memRegion outA v1RecvSize ∗ A.pool ∗
     sendEkSpillsAt fsp sp ∗
     memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 1504#64) 352 ∗
     memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
    hinv2 hfsp_align hpc2 hrun2 hsp2 hx1_2 hx19_2 hx24_2) ?_
  intro s2b hpc2b hrun2b hinv2b ⟨hsp2b, hx19_2b, hx20_2b, hx24_2b, _, htr2b⟩
  have htr2b0 : TraceCalleeSaved s2b s0 := htr2b.trans htr20
  refine ct1Ack_sepWPp_seq_clean_inImage hinv2b (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl_ct1Ack2_ext))
    (ct1Ack_step_608_632_words66 s2b fsp outA selfA msgA msg.epoch w
      (memRegion (s0.sp - 40176#64) 16384 ∗
       words66At (selfA + 8#64) w ∗ ((msgA + 8#64) ↦₈ ct1AckPayloadTag msg.payload) ∗
       ct1AckPayloadTailAt msgA msg.payload ∗
       (selfA ↦₆₄ 11#64) ∗
       relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst st) (wordsBytes (words66List w)) ∗
       memRegion (selfA + 536#64) 392 ∗
       statesRecvRoAt img.base ∗ memRegion outA v1RecvSize ∗ A.pool ∗
       stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp ∗
       memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 1504#64) 352 ∗
       memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
      hfsp_align hpc2b hrun2b hsp2b hx19_2b hx20_2b hx24_2b)) ?_
  intro s3 hpc3 hrun3 hinv3 ⟨hsp3, hx2_3, hx9_3, hx19_3, hx20_3, hx24_3, _, hx8_3, hz_3, htr3⟩
  have htr30 : TraceCalleeSaved s3 s0 := htr3.trans htr2b0
  rw [hep] at hx9_3 hx8_3 hz_3
  by_cases hgt : msg.epoch > st.uc.epoch
  · refine ct1Ack_sepWPp_seq_clean_inImage hinv3
      (ct1Ack_step_632_644_gt s3 fsp outA selfA msgA msg.epoch st.uc.epoch _
        hgt hpc3 hrun3 hsp3 hx2_3 hx9_3 hx19_3 hx20_3 hx24_3 hx8_3 hz_3) ?_
    intro s4 hpc4 hrun4 _hinv4 ⟨hsp4, hx2_4, _, hx19_4, _, _, _, htr4⟩
    have hrecv := states_recv_ct1Acknowledged_gt K st msg hgt
    have hexit := ct1Ack_gt_644_ret hdealloc s0 s4 outA selfA msg.epoch st
      (memRegion (s0.sp - 40176#64) 16384 ∗
       messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base)
      hsp0_align hpc4 hrun4 hsp4 hx2_4 hx19_4 (htr4.trans htr30)
    refine sepWPp_of_statesRecv_exit_ext s0 s4 outA selfA msgA (.ct1Acknowledged st) msg _ R ?_
    refine SepWP.weaken_pre ?_ (SepWP.mono hexit ?_)
    · rw [messageAt_eq_epoch_ct1AckTag_tail msgA msg]
      have hself_mem := selfA_ct1Acknowledged_entails_memRegion selfA w
      have hrecomp := recompose66_ct1Acknowledged A (fsp + 976#64) w st
      have hstk := sendEkFrame_entails_976_2288 fsp sp
      refine Entails.trans (Entails.of_eq (show _ =
        ((selfA ↦₆₄ 11#64) ∗ words66At (selfA + 8#64) w ∗ memRegion (selfA + 536#64) 392) ∗
        (words66At (fsp + 976#64) w ∗
         relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst st) (wordsBytes (words66List w))) ∗
        (sendEkSpillsAt fsp sp ∗ memRegion (fsp + 576#64) 376 ∗
         memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp) ∗
        (memRegion (s0.sp - 40176#64) 16384 ∗
         ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ ct1AckPayloadTag msg.payload) ∗
          ct1AckPayloadTailAt msgA msg.payload) ∗
         statesRecvRoAt img.base ∗ memRegion outA v1RecvSize ∗
         memRegion (fsp + 1504#64) 352 ∗ A.pool ∗
         stackAt fsp statesRecvCalleeStackX ∗ statesRecvSavedCells s0) by sep_ac_rfl_ct1Ack2_ext)) ?_
      exact Entails.trans
        (sepConj_mono hself_mem (sepConj_mono hrecomp (sepConj_mono_left hstk)))
        (Entails.of_eq (by dsimp only [fsp]; sep_ac_rfl_ct1Ack2_ext))
    · intro sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩
      refine ⟨Entails.trans hPf ?_, hsp_sf, hcs_sf, htr_sf⟩
      rw [hrecv, stackAt_statesRecvStackXExt_eq_X s0.sp]; exact Entails.of_eq (by sep_ac_rfl_ct1Ack2_ext)
  · by_cases hlt : msg.epoch < st.uc.epoch
    · refine ct1Ack_sepWPp_seq_clean_inImage hinv3
        (ct1Ack_step_632_4516_lt s3 fsp outA selfA msgA msg.epoch st.uc.epoch _
          hlt hpc3 hrun3 hsp3 hx2_3 hx9_3 hx19_3 hx20_3 hx24_3 hx8_3 hz_3) ?_
      intro s4 hpc4 hrun4 hinv4 ⟨hsp4, _, hx9_4, hx19_4, hx20_4, _, _, htr4⟩
      have hrecv := states_recv_ct1Acknowledged_lt K st msg hlt
      rw [← hep] at hx9_4
      have hexit := ct1Ack_noop_4516_ret_ext (A := A) (F := F) hAx s0 s4 outA selfA st w sp
        (memRegion (s0.sp - 40176#64) 16384 ∗
         messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base ∗ A.pool)
        hinv4 hsp0_align hpc4 hrun4 hsp4 hx9_4 hx19_4 hx20_4 (htr4.trans htr30)
      refine sepWPp_of_statesRecv_exit_ext s0 s4 outA selfA msgA (.ct1Acknowledged st) msg _ R ?_
      refine SepWP.weaken_pre
        (Entails.of_eq (by rw [messageAt_eq_epoch_ct1AckTag_tail msgA msg]; dsimp only [fsp]; sep_ac_rfl_ct1Ack2_ext))
        (SepWP.mono hexit ?_)
      intro sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩
      refine ⟨Entails.trans hPf ?_, hsp_sf, hcs_sf, htr_sf⟩
      rw [hrecv, stackAt_statesRecvStackXExt_eq_X s0.sp]; exact Entails.of_eq (by sep_ac_rfl_ct1Ack2_ext)
    · have heq : msg.epoch = st.uc.epoch :=
        BitVec.le_antisymm (BitVec.not_lt.mp hgt) (BitVec.not_lt.mp hlt)
      refine ct1Ack_sepWPp_seq_clean_inImage hinv3
        (ct1Ack_step_632_4432_eq s3 fsp outA selfA msgA msg.epoch st.uc.epoch _
          heq hpc3 hrun3 hsp3 hx2_3 hx9_3 hx19_3 hx20_3 hx24_3 hx8_3 hz_3) ?_
      intro s4 hpc4 hrun4 hinv4 ⟨hsp4, hx2_4, hx9_4, hx19_4, hx20_4, hx24_4, _, htr4⟩
      have htr40 : TraceCalleeSaved s4 s0 := htr4.trans htr30
      rw [heq] at hx2_4
      cases hpay : msg.payload with
      | ek chunk =>
        have hcond : (BitVec.truncate 32 (BitVec.zeroExtend 64 (ct1AckPayloadTag msg.payload) &&& 25769803782#64) != 2#32) = false := by
          rw [hpay]; exact messagePayloadTag_and6_bne_2_of_ek chunk
        refine ct1Ack_sepWPp_seq_clean_inImage hinv4
          (SepWP.weaken_pre (Entails.of_eq (by rw [hpay]; sep_ac_rfl_ct1Ack2_ext))
            (ct1Ack_step_4432_4448_ek s4 fsp outA selfA msgA st.uc.epoch msg.payload
              (memRegion (s0.sp - 40176#64) 16384 ∗
               words66At (fsp + 976#64) w ∗ (msgA ↦₆₄ msg.epoch) ∗
               words66At (selfA + 8#64) w ∗ ct1AckPayloadTailAt msgA msg.payload ∗
               (selfA ↦₆₄ 11#64) ∗
               relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst st) (wordsBytes (words66List w)) ∗
               memRegion (selfA + 536#64) 392 ∗
               statesRecvRoAt img.base ∗ memRegion outA v1RecvSize ∗ A.pool ∗
               stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp ∗
               memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 1504#64) 352 ∗
               memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
              hcond hpc4 hrun4 hsp4 hx2_4 hx9_4 hx19_4 hx20_4 hx24_4)) ?_
        intro s5 hpc5 hrun5 hinv5 ⟨hsp5, hx2_5, _, hx19_5, hx20_5, hx24_5, _, htr5⟩
        have hmsg_recomp :
            chunkAt (msgA + 10#64) chunk ∗
            ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ ct1AckPayloadTag msg.payload) ∗
             memRegion (msgA + 0x09#64) 1 ∗ memRegion (msgA + 0x2c#64) 4) ⊢
            messageAt spqrPolyApi msgA msg := by
          rw [messageAt_eq_epoch_ct1AckTag_tail msgA msg, hpay]
          dsimp only [ct1AckPayloadTailAt]
          exact Entails.of_eq (by sep_ac_rfl_ct1Ack2_ext)
        refine SepWPp.weaken_pre
          (Entails.of_eq (by rw [hpay]; dsimp only [ct1AckPayloadTailAt, fsp]; sep_ac_rfl_ct1Ack2_ext))
          (ct1Ack_ek_4448_ret_ext hb hAx hcall s0 s5 outA selfA msgA st msg chunk w sp
            ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ ct1AckPayloadTag (.ek chunk)) ∗
             memRegion (msgA + 0x09#64) 1 ∗ memRegion (msgA + 0x2c#64) 4)
            R hinv5 hlen hinv
            (fun res hrecv => states_recv_ct1Acknowledged_eq_ek_res K st msg chunk res heq hpay hrecv)
            (by rw [← hpay]; exact hmsg_recomp)
            hsp0_align hpc5 hrun5 hsp5 hx2_5 hx19_5 hx20_5 hx24_5 (htr5.trans htr40))
      | ekCt1Ack chunk =>
        have hcond : (BitVec.truncate 32 (BitVec.zeroExtend 64 (ct1AckPayloadTag msg.payload) &&& 25769803782#64) != 2#32) = false := by
          rw [hpay]; exact messagePayloadTag_and6_bne_2_of_ekCt1Ack chunk
        refine ct1Ack_sepWPp_seq_clean_inImage hinv4
          (SepWP.weaken_pre (Entails.of_eq (by rw [hpay]; sep_ac_rfl_ct1Ack2_ext))
            (ct1Ack_step_4432_4448_ek s4 fsp outA selfA msgA st.uc.epoch msg.payload
              (memRegion (s0.sp - 40176#64) 16384 ∗
               words66At (fsp + 976#64) w ∗ (msgA ↦₆₄ msg.epoch) ∗
               words66At (selfA + 8#64) w ∗ ct1AckPayloadTailAt msgA msg.payload ∗
               (selfA ↦₆₄ 11#64) ∗
               relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst st) (wordsBytes (words66List w)) ∗
               memRegion (selfA + 536#64) 392 ∗
               statesRecvRoAt img.base ∗ memRegion outA v1RecvSize ∗ A.pool ∗
               stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp ∗
               memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 1504#64) 352 ∗
               memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
              hcond hpc4 hrun4 hsp4 hx2_4 hx9_4 hx19_4 hx20_4 hx24_4)) ?_
        intro s5 hpc5 hrun5 hinv5 ⟨hsp5, hx2_5, _, hx19_5, hx20_5, hx24_5, _, htr5⟩
        have hmsg_recomp :
            chunkAt (msgA + 10#64) chunk ∗
            ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ ct1AckPayloadTag msg.payload) ∗
             memRegion (msgA + 0x09#64) 1 ∗ memRegion (msgA + 0x2c#64) 4) ⊢
            messageAt spqrPolyApi msgA msg := by
          rw [messageAt_eq_epoch_ct1AckTag_tail msgA msg, hpay]
          dsimp only [ct1AckPayloadTailAt]
          exact Entails.of_eq (by sep_ac_rfl_ct1Ack2_ext)
        refine SepWPp.weaken_pre
          (Entails.of_eq (by rw [hpay]; dsimp only [ct1AckPayloadTailAt, fsp]; sep_ac_rfl_ct1Ack2_ext))
          (ct1Ack_ek_4448_ret_ext hb hAx hcall s0 s5 outA selfA msgA st msg chunk w sp
            ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ ct1AckPayloadTag (.ekCt1Ack chunk)) ∗
             memRegion (msgA + 0x09#64) 1 ∗ memRegion (msgA + 0x2c#64) 4)
            R hinv5 hlen hinv
            (fun res hrecv => states_recv_ct1Acknowledged_eq_ekCt1Ack_res K st msg chunk res heq hpay hrecv)
            (by rw [← hpay]; exact hmsg_recomp)
            hsp0_align hpc5 hrun5 hsp5 hx2_5 hx19_5 hx20_5 hx24_5 (htr5.trans htr40))
      | _ =>
        have hek : ∀ c, msg.payload ≠ .ek c := by intro c h; rw [hpay] at h; cases h
        have hekAck : ∀ c, msg.payload ≠ .ekCt1Ack c := by intro c h; rw [hpay] at h; cases h
        have hrecv := states_recv_ct1Acknowledged_eq_other K st msg heq hek hekAck
        refine ct1Ack_sepWPp_seq_clean_inImage hinv4
          (SepWP.weaken_pre (Entails.of_eq (by rw [hpay]; sep_ac_rfl_ct1Ack2_ext))
            (ct1Ack_step_4432_4516_not_ek s4 fsp outA selfA msgA st.uc.epoch msg.payload
              (memRegion (s0.sp - 40176#64) 16384 ∗
               words66At (fsp + 976#64) w ∗ (msgA ↦₆₄ msg.epoch) ∗
               words66At (selfA + 8#64) w ∗ ct1AckPayloadTailAt msgA msg.payload ∗
               (selfA ↦₆₄ 11#64) ∗
               relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst st) (wordsBytes (words66List w)) ∗
               memRegion (selfA + 536#64) 392 ∗
               statesRecvRoAt img.base ∗ memRegion outA v1RecvSize ∗ A.pool ∗
               stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp ∗
               memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 1504#64) 352 ∗
               memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
              hek hekAck hpc4 hrun4 hsp4 hx9_4 hx19_4 hx20_4 hx24_4)) ?_
        intro s5 hpc5 hrun5 hinv5 ⟨hsp5, hx9_5, hx19_5, hx20_5, _, _, htr5⟩
        rw [← hep] at hx9_5
        have hexit := ct1Ack_noop_4516_ret_ext (A := A) (F := F) hAx s0 s5 outA selfA st w sp
          (memRegion (s0.sp - 40176#64) 16384 ∗
           messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base ∗ A.pool)
          hinv5 hsp0_align hpc5 hrun5 hsp5 hx9_5 hx19_5 hx20_5 (htr5.trans htr40)
        refine sepWPp_of_statesRecv_exit_ext s0 s5 outA selfA msgA (.ct1Acknowledged st) msg _ R ?_
        refine SepWP.weaken_pre
          (Entails.of_eq (by rw [messageAt_eq_epoch_ct1AckTag_tail msgA msg]; dsimp only [fsp]; sep_ac_rfl_ct1Ack2_ext))
          (SepWP.mono hexit ?_)
        intro sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩
        refine ⟨Entails.trans hPf ?_, hsp_sf, hcs_sf, htr_sf⟩
        rw [hrecv, stackAt_statesRecvStackXExt_eq_X s0.sp]; exact Entails.of_eq (by sep_ac_rfl_ct1Ack2_ext)

end CryptoVerification.SpqrV1.States.Recv
