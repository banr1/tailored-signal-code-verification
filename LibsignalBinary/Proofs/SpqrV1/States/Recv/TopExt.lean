/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchExt
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1AcknowledgedExt2
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received2
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledExtPart10
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledExtPart7
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledExtPart8
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart6
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkReceivedCt1SampledExt
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkSentCt1ReceivedExt
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSentExt2
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmKeysSampledExt2
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceived2
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceivedExt1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceivedExt2
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSimple3
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSimpleExt1
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv`: Contract-Backed Top-Level Assembly (`40,176`-Byte Stack)

Assembles all 13 `States` variants under `StatesRecvContractsAx` / `StatesRecvContractsExt`
to prove `states_recv_ok_x_ext_ax_full` and `states_recv_ok_x_ext_ax` (`statesRecvStackXExt = 40176` B).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
open CryptoVerification.SpqrV1.Top.MessageSerialize

local elab "sep_ac_rfl_top_ext" : tactic => do
  let g ← _root_.Lean.Elab.Tactic.getMainGoal
  g.withContext do
    let ty := (← _root_.Lean.instantiateMVars (← g.getType)).consumeMData
    let some (_, lhs, rhs) := ty.eq?
      | _root_.Lean.throwError "sep_ac_rfl_top_ext: expected equality"
    if lhs == rhs then
      g.assign (← _root_.Lean.Meta.mkEqRefl lhs)
      _root_.Lean.Elab.Tactic.replaceMainGoal []
    else if let some (tbl, tA, tB) := ProofLib.SepSolver.synReifyPermTbl? lhs rhs then
      g.assign (← ProofLib.SepSolver.eqACOfTbl lhs rhs tbl tA tB)
      _root_.Lean.Elab.Tactic.replaceMainGoal []
    else
      _root_.Lean.Elab.Tactic.evalTactic (← `(tactic| sep_frame))

private theorem stackAt_statesRecvCalleeExt_eq_nhr_ax (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackXExt =
      memRegion (fsp - BitVec.ofNat 64 statesRecvCalleeStackXExt)
        (statesRecvCalleeStackXExt - noHeaderReceivedRecvHdrChunkStackX) ∗
      stackAt fsp noHeaderReceivedRecvHdrChunkStackX := by
  change memRegion (fsp - 35936#64) 35936 =
    memRegion (fsp - 35936#64) 17232 ∗ memRegion (fsp - 18704#64) 18704
  exact ProofLib.memRegion_split' (b := fsp - 35936#64) (n := 17232) (k := 18704)
    (b' := fsp - 18704#64) rfl (by bv_omega) (by decide)

private theorem call_noHeaderReceivedRecvHdrChunk_ax_grown
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hcall : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr noHeaderReceivedRecvHdrChunkName)
      ((growToCalleeExt noHeaderReceivedRecvHdrChunkStackX
        (noHeaderReceivedRecvHdrChunkSpec F A img.base)).inImage img))
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk)
    (Frame R : SepProp)
    (hinv_img : ImgCallInv img s)
    (heq : msg.epoch = st.uc.epoch)
    (hp : msg.payload = .hdr chunk)
    (hinv : PolyDecoderStrictSorted st.receiving_hdr)
    (hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr noHeaderReceivedRecvHdrChunkName)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hx0 : s.readReg64 .x0 = (s0.sp - 4240#64) + 1856#64)
    (hx1 : s.readReg64 .x1 = (s0.sp - 4240#64) + 976#64)
    (hx2 : s.readReg64 .x2 = st.uc.epoch)
    (hx3 : s.readReg64 .x3 = msgA + 10#64)
    (hx19 : s.readReg64 .x19 = outA)
    (hlr : s.readReg64 Reg.lr = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 8616#64)
    (htr : TraceCalleeSaved s s0)
    (hnext : ∀ sf : State,
      sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 8616#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 4240#64 →
      sf.readReg64 .x19 = outA →
      TraceCalleeSaved sf s0 →
      ImgCallInv img sf →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 Reg.lr) sf
        ((noHeaderReceivedRecvChunkResultAt A ((s0.sp - 4240#64) + 1856#64) (st.recv_hdr_chunk st.uc.epoch chunk) ∗
          memRegion ((s0.sp - 4240#64) + 976#64) chunkedNoHeaderReceivedSize ∗
          chunkAt (msgA + 10#64) chunk ∗
          tokenInitAt img.base ∗ reduceTableAt img.base ∗ A.pool ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt) ∗ Frame)
        (fun sf P_f =>
          (sf.mem ⊨ P_f ∗ R →
            sf.mem ⊨ (statesRecvVariantSpecExt A F K img.base (.noHeaderReceived st) msg).post
              (outA, selfA, msgA) s0 sf ∗ R) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ (statesRecvVariantSpecExt A F K img.base (.noHeaderReceived st) msg).onPanic
              (outA, selfA, msgA) s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 Reg.lr) s
      ((memRegion ((s0.sp - 4240#64) + 1856#64) chunkedHeaderReceivedSize ∗
        chunkedNoHeaderReceivedAt A ((s0.sp - 4240#64) + 976#64) st ∗
        chunkAt (msgA + 10#64) chunk ∗
        tokenInitAt img.base ∗ reduceTableAt img.base ∗ A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt) ∗ Frame)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (statesRecvVariantSpecExt A F K img.base (.noHeaderReceived st) msg).post
            (outA, selfA, msgA) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (statesRecvVariantSpecExt A F K img.base (.noHeaderReceived st) msg).onPanic
            (outA, selfA, msgA) s0 sf ∗ R)) := by
  refine SepWPp.call_imgInv hcall hinv_img
    (x := ⟨(s0.sp - 4240#64) + 1856#64, (s0.sp - 4240#64) + 976#64, st, st.uc.epoch, msgA + 10#64, chunk⟩)
    (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hfsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hinv_sf => ?_)
  · intro R' hm
    dsimp only [Spec.inImage, growToCalleeExt, noHeaderReceivedRecvHdrChunkSpec]
    rw [hsp]
    rw [stackAt_statesRecvCalleeExt_eq_nhr_ax (s0.sp - 4240#64)] at hm
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    refine ⟨⟨hinv_img.1, hinv_img.2⟩, ⟨hb, hx0, hx1, hx2, hx3, hinv⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl_top_ext)) hm
  · dsimp only [Spec.inImage, growToCalleeExt, noHeaderReceivedRecvHdrChunkSpec,
      statesRecvVariantSpecExt, statesRecvOnPanic] at hmem ⊢
    refine allowPanic_frame (fun ⟨hpan_or, htr_sub⟩ => ?_) hmem
    unfold allocFailedIn at hpan_or ⊢
    rw [htr.1] at hpan_or htr_sub
    rcases hpan_or with hpan | haf
    · exact ⟨Or.inl (states_recv_noHeaderReceived_isPanic_hdr K st msg chunk heq hp hpan), htr_sub⟩
    · exact ⟨Or.inr haf, htr_sub⟩
  · dsimp only [Spec.inImage, growToCalleeExt, noHeaderReceivedRecvHdrChunkSpec]
    rw [hsp, sepConj_assoc, sepConj_assoc]
    refine SepWPp.pure_left fun htr_sf => ?_
    refine SepWPp.weaken_pre (Entails.of_eq ?_)
      (hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) (hcs_sf.1.trans hx19)
        ⟨htr_sf.trans htr.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htr.2⟩ hinv_sf)
    rw [stackAt_statesRecvCalleeExt_eq_nhr_ax (s0.sp - 4240#64)]
    sep_ac_rfl_top_ext

private theorem nhr_hdr_8568_ret_ax_grown
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hA : AllocContractsX img A ext)
    (hcall : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr noHeaderReceivedRecvHdrChunkName)
      ((growToCalleeExt noHeaderReceivedRecvHdrChunkStackX
        (noHeaderReceivedRecvHdrChunkSpec F A img.base)).inImage img))
    (s0 s1 : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk)
    (w : Words57) (sp1 : SendEkSpills) (R : SepProp)
    (hinv1 : ImgCallInv img s1)
    (heq : msg.epoch = st.uc.epoch) (hp : msg.payload = .hdr chunk)
    (hinv : PolyDecoderStrictSorted st.receiving_hdr)
    (hsp0_align : s0.spAligned = true)
    (hpc : s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 8568#64)
    (hrun : s1.status = .Running) (hsp : s1.sp = s0.sp - 4240#64)
    (hx19 : s1.readReg64 .x19 = outA) (hx20 : s1.readReg64 .x20 = st.uc.epoch)
    (hx21 : s1.readReg64 .x21 = selfA) (hx24 : s1.readReg64 .x24 = msgA)
    (htr : TraceCalleeSaved s1 s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 Reg.lr) s1
      ((selfA ↦₆₄ 7#64) ∗ words57At (selfA + 8#64) w ∗
        relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst st) (wordsBytes (words57List w)) ∗
        memRegion (selfA + 464#64) 464 ∗
        words57At ((s0.sp - 4240#64) + 2752#64) w ∗ nhrUnusedRestAt (s0.sp - 4240#64) ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗ memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        (msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA (.hdr chunk) ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
        (statesRecvRoAt img.base ∗ memRegion outA v1RecvSize ∗ A.pool ∗
         sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗
         memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ statesRecvSavedCells s0))
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (statesRecvVariantSpecExt A F K img.base (.noHeaderReceived st) msg).post
            (outA, selfA, msgA) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (statesRecvVariantSpecExt A F K img.base (.noHeaderReceived st) msg).onPanic
            (outA, selfA, msgA) s0 sf ∗ R)) := by
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  set fsp := s0.sp - 4240#64
  have hpre0 :
      (selfA ↦₆₄ 7#64) ∗ words57At (selfA + 8#64) w ∗
        relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst st) (wordsBytes (words57List w)) ∗
        memRegion (selfA + 464#64) 464 ∗
        words57At (fsp + 2752#64) w ∗ nhrUnusedRestAt fsp ∗
        memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1856#64) 880 ∗
        (msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA (.hdr chunk) ∗
        stackAt fsp statesRecvCalleeStackXExt ∗
        (statesRecvRoAt img.base ∗ memRegion outA v1RecvSize ∗ A.pool ∗
         sendEkSpillsAt fsp sp1 ∗
         memRegion (fsp + 576#64) 376 ∗ statesRecvSavedCells s0) =
      (selfA ↦₆₄ 7#64) ∗ words57At (selfA + 8#64) w ∗
        relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst st) (wordsBytes (words57List w)) ∗
        memRegion (selfA + 464#64) 464 ∗
        words57At (fsp + 2752#64) w ∗ nhrUnusedRestAt fsp ∗
        memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1856#64) 880 ∗
        (msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA (.hdr chunk) ∗
        stackAt fsp statesRecvCalleeStackX ∗
        (memRegion (s0.sp - 40176#64) 16384 ∗
         statesRecvRoAt img.base ∗ memRegion outA v1RecvSize ∗ A.pool ∗
         sendEkSpillsAt fsp sp1 ∗
         memRegion (fsp + 576#64) 376 ∗ statesRecvSavedCells s0) := by
    dsimp only [fsp]
    rw [stackAt_statesRecvCalleeExt_eq_X s0.sp]
    sep_ac_rfl_top_ext
  refine SepWPp.weaken_pre (Entails.of_eq hpre0) ?_
  refine sepWPp_seq_clean_inImage_ax hinv1
    (nhr_step_8568_to_call_entry_ext hA s0 s1 outA selfA msgA st msg chunk w
      (memRegion (s0.sp - 40176#64) 16384 ∗
       statesRecvRoAt img.base ∗ memRegion outA v1RecvSize ∗ A.pool ∗
       sendEkSpillsAt fsp sp1 ∗ memRegion (fsp + 576#64) 376 ∗ statesRecvSavedCells s0)
      hinv1 hfsp_align hpc hrun hsp hx19 hx20 hx21 hx24 htr) ?_
  intro s2 hpc2 hrun2 hinv2 ⟨hsp2, h0_2, h1_2, h2_2, h3_2, h19_2, h30_2, htr2⟩
  refine SepWPp.weaken_pre (Entails.of_eq (show _ =
    (memRegion (fsp + 1856#64) chunkedHeaderReceivedSize ∗
     chunkedNoHeaderReceivedAt A (fsp + 976#64) st ∗
     chunkAt (msgA + 10#64) chunk ∗
     tokenInitAt img.base ∗ reduceTableAt img.base ∗ A.pool ∗
     stackAt fsp statesRecvCalleeStackXExt) ∗
    (statesRecvJumpTableAt img.base ∗ unchunkedSendCt2RoAt img.base ∗
     memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
     (msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 1#8) ∗
     memRegion (msgA + 9#64) 1 ∗ memRegion (msgA + 44#64) 4 ∗
     sendEkSpillsAt fsp sp1 ∗ memRegion (fsp + 576#64) 376 ∗
     memRegion (fsp + 1432#64) 424 ∗ memRegion (fsp + 2336#64) 400 ∗
     sendEkUnusedAt fsp ∗ statesRecvSavedCells s0) by
      dsimp only [statesRecvRoAt, fsp]
      rw [stackAt_statesRecvCalleeExt_eq_X s0.sp]
      sep_ac_rfl_top_ext)) ?_
  refine call_noHeaderReceivedRecvHdrChunk_ax_grown hb hcall s0 s2 outA selfA msgA st msg chunk _ R
    hinv2 heq hp hinv hfsp_align hpc2 hrun2 hsp2 h0_2 h1_2 h2_2 h3_2 h19_2 h30_2 htr2 ?_
  intro s3 hpc3 hrun3 hsp3 h19_3 htr3 hinv3
  refine SepWPp.weaken_pre (Entails.of_eq (show _ =
    noHeaderReceivedRecvChunkResultAt A (fsp + 1856#64) (st.recv_hdr_chunk st.uc.epoch chunk) ∗
    (memRegion (s0.sp - 40176#64) 16384 ∗
     messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base ∗ A.pool) ∗
    memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
    stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp1 ∗
    memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗
    memRegion (fsp + 2336#64) 400 ∗ sendEkUnusedAt fsp ∗
    statesRecvSavedCells s0 by
      dsimp only [statesRecvRoAt, chunkedNoHeaderReceivedSize, fsp]
      rw [stackAt_statesRecvCalleeExt_eq_X s0.sp,
          memRegion_880_split_456_424_nhr (s0.sp - 4240#64),
          ← messageAt_hdr_recompose msgA msg chunk hp]
      sep_ac_rfl_top_ext)) ?_
  cases hres : st.recv_hdr_chunk st.uc.epoch chunk with
  | error e =>
    cases e with
    | panic _ =>
      dsimp only [noHeaderReceivedRecvChunkResultAt]
      exact SepWPp.pure_left (fun h => False.elim h)
    | err err =>
      have hrecv : (States.noHeaderReceived st).recv K msg = .error (.err err) := by
        rw [states_recv_noHeaderReceived_eq_hdr K st msg chunk heq hp, hres]
      have hexit := nhr_err_8616_ret (A := A) (F := F) s0 s3 outA selfA err sp1
        (memRegion (s0.sp - 40176#64) 16384 ∗
         messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base ∗ A.pool)
        hsp0_align hpc3 hrun3 hsp3 h19_3 htr3
      refine sepWPp_of_statesRecv_exit_ext s0 s3 outA selfA msgA (.noHeaderReceived st) msg _ R ?_
      refine SepWP.weaken_pre (Entails.of_eq (by dsimp only [fsp]; sep_ac_rfl_top_ext)) (SepWP.mono hexit ?_)
      intro sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩
      refine ⟨Entails.trans hPf ?_, hsp_sf, hcs_sf, htr_sf⟩
      rw [hrecv, stackAt_statesRecvStackXExt_eq_X s0.sp]
      exact Entails.of_eq (by sep_ac_rfl_top_ext)
  | ok step =>
    cases step with
    | stillReceiving outSt =>
      have hrecv : (States.noHeaderReceived st).recv K msg =
          .ok { key := none, state := .noHeaderReceived outSt } := by
        rw [states_recv_noHeaderReceived_eq_hdr K st msg chunk heq hp, hres]
      refine SepWPp.weaken_pre (sepConj_mono_left (nhr_still_1856_split (A := A) (F := F) fsp outSt)) ?_
      simp only [sepExists_sepConj_left]
      apply sepWPp_intro_ex_nhr hrun3; intro w_out
      apply sepWPp_intro_ex_nhr hrun3; intro w58
      apply sepWPp_intro_ex_nhr hrun3; intro w59
      have hexit := nhr_still_8616_ret_ext (A := A) (F := F) hA s0 s3 outA selfA w58 w59 outSt w_out sp1
        (memRegion (s0.sp - 40176#64) 16384 ∗
         messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base ∗ A.pool)
        hinv3 hsp0_align hpc3 hrun3 hsp3 h19_3 htr3
      refine sepWPp_of_statesRecv_exit_ext s0 s3 outA selfA msgA (.noHeaderReceived st) msg _ R ?_
      refine SepWP.weaken_pre (Entails.of_eq (by dsimp only [fsp]; sep_ac_rfl_top_ext)) (SepWP.mono hexit ?_)
      intro sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩
      refine ⟨Entails.trans hPf ?_, hsp_sf, hcs_sf, htr_sf⟩
      rw [hrecv, stackAt_statesRecvStackXExt_eq_X s0.sp]
      exact Entails.of_eq (by sep_ac_rfl_top_ext)
    | done outSt =>
      have hrecv : (States.noHeaderReceived st).recv K msg =
          .ok { key := none, state := .headerReceived outSt } := by
        rw [states_recv_noHeaderReceived_eq_hdr K st msg chunk heq hp, hres]
      refine SepWPp.weaken_pre (sepConj_mono_left (nhr_done_1856_split (A := A) (F := F) fsp outSt)) ?_
      simp only [sepExists_sepConj_left]
      apply sepWPp_intro_ex_nhr hrun3; intro w_out
      rw [sepConj_assoc]
      apply SepWPp.pure_left; intro ⟨hw0_ne_err, hw0_ne_none⟩
      have hexit := nhr_done_8616_ret_ext (A := A) (F := F) hb hA s0 s3 outA selfA outSt w_out sp1
        (memRegion (s0.sp - 40176#64) 16384 ∗
         messageAt spqrPolyApi msgA msg ∗ statesRecvJumpTableAt img.base ∗
         ((img.base + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel) ∗
         tokenInitAt img.base ∗ reduceTableAt img.base ∗ A.pool)
        hinv3 hsp0_align hw0_ne_err hw0_ne_none hpc3 hrun3 hsp3 h19_3 htr3
      refine sepWPp_of_statesRecv_exit_ext s0 s3 outA selfA msgA (.noHeaderReceived st) msg _ R ?_
      refine SepWP.weaken_pre
        (Entails.of_eq (by dsimp only [statesRecvRoAt, unchunkedSendCt2RoAt, BitVec.ofNat_eq_ofNat, fsp]; sep_ac_rfl_top_ext))
        (SepWP.mono hexit ?_)
      intro sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩
      refine ⟨Entails.trans hPf ?_, hsp_sf, hcs_sf, htr_sf⟩
      rw [hrecv, stackAt_statesRecvStackXExt_eq_X s0.sp]
      exact Entails.of_eq (by dsimp only [statesRecvRoAt, unchunkedSendCt2RoAt, BitVec.ofNat_eq_ofNat]; sep_ac_rfl_top_ext)

private theorem states_recv_noHeaderReceived_ok_x_ax_grown
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext)
    (hdealloc : DeallocOkExt img.base A ext)
    (hcall : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr noHeaderReceivedRecvHdrChunkName)
      ((growToCalleeExt noHeaderReceivedRecvHdrChunkStackX
        (noHeaderReceivedRecvHdrChunkSpec F A img.base)).inImage img))
    (st : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName)
      ((statesRecvVariantSpecExt A F K img.base (.noHeaderReceived st) msg).inImage img) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨outA, selfA, msgA⟩ R s0 hpc0 hrun0 hpre hsp0_align
  simp only [Spec.inImage, statesRecvVariantSpecExt, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF0, hsym0⟩, ⟨hb, hx0, hx1, hx2, hinv⟩, hmem⟩
  have hinv0 : ImgCallInv img s0 := ⟨hF0, hsym0⟩
  refine ⟨stackAt s0.sp statesRecvStackXExt ∗ (memRegion outA v1RecvSize ∗
      chunkedStatesAt A selfA (.noHeaderReceived st) ∗
      messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base ∗ A.pool),
    R, Satisfies.mono (Entails.of_eq (by sep_ac_rfl_top_ext)) hmem, ?_⟩
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  have hpro := states_recv_prologue_ext (b := img.base) (ext := ext) s0
    (memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.noHeaderReceived st) ∗
     messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base ∗ A.pool) hsp0_align hpc0 hrun0
  refine sepWPp_seq_clean_inImage_ax hinv0 hpro ?_
  intro s1 hpc1 hrun1 hinv1 ⟨hsp1, hx0_1, hx1_1, hx2_1, _, _, htr1⟩
  rw [hx0] at hx0_1; rw [hx1] at hx1_1; rw [hx2] at hx2_1
  dsimp only [chunkedStatesAt]
  have hdisp := states_recv_dispatch_noHeaderReceived hb s1 (s0.sp - 4240#64) selfA
    (chunkedNoHeaderReceivedAt A (selfA + 8#64) st ∗ memRegion (selfA + 464#64) 464 ∗
     memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ A.pool ∗
     stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗ memRegion (s0.sp - 4240#64) 4144 ∗
     statesRecvSavedCells s0)
    hpc1 hrun1 hsp1 hx1_1
  refine sepWPp_seq_clean_inImage_ax hinv1
    (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl_top_ext)) hdisp) ?_
  intro s2 hpc2 hrun2 hinv2 ⟨hsp2, _, hx1_2, _, _, _, _, hx19_2, _, hx24_2, _, _, htr2⟩
  rw [hx0_1] at hx19_2; rw [hx2_1] at hx24_2
  have htr20 : TraceCalleeSaved s2 s0 := htr2.trans htr1
  set fsp := s0.sp - 4240#64
  have hpre_split :
      (selfA ↦₆₄ 7#64) ∗ statesRecvRoAt img.base ∗
      (chunkedNoHeaderReceivedAt A (selfA + 8#64) st ∗ memRegion (selfA + 464#64) 464 ∗
       memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ A.pool ∗
       stackAt fsp statesRecvCalleeStackXExt ∗ memRegion fsp 4144 ∗ statesRecvSavedCells s0) ⊢
      (∃∗ w : Words57, ∃∗ sp : SendEkSpills,
        ⌜w.b0.w6 = st.uc.epoch⌝ ∗
        (memRegion (fsp + 2752#64) 456 ∗ words57At (selfA + 8#64) w ∗
         (msgA ↦₆₄ msg.epoch) ∗ sendEkSpillsAt fsp sp ∗ stackAt fsp statesRecvCalleeStackX ∗
         (memRegion (s0.sp - 40176#64) 16384 ∗
          (selfA ↦₆₄ 7#64) ∗
          relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst st) (wordsBytes (words57List w)) ∗
          memRegion (selfA + 464#64) 464 ∗ messagePayloadAt spqrPolyApi msgA msg.payload ∗
          statesRecvRoAt img.base ∗ memRegion outA v1RecvSize ∗ A.pool ∗
          memRegion (fsp + 576#64) 376 ∗
          memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1856#64) 880 ∗
          nhrUnusedRestAt fsp ∗ statesRecvSavedCells s0))) := by
    unfold messageAt
    have hex57 := chunkedNoHeaderReceivedAt_extract57 A (selfA + 8#64) st
    have hstk : memRegion fsp 4144 ⊢
        ∃∗ sp : SendEkSpills,
          sendEkSpillsAt fsp sp ∗ memRegion (fsp + 576#64) 376 ∗
          memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1856#64) 880 ∗
          memRegion (fsp + 2752#64) 456 ∗ nhrUnusedRestAt fsp := by
      refine Entails.trans (memRegion_4144_entails_sendEkFrame fsp) ?_
      apply Entails.sepExists_elim; intro sp
      refine Entails.sepExists_right sp ?_
      refine Entails.trans (Entails.of_eq (show _ =
        sendEkUnusedAt fsp ∗ (sendEkSpillsAt fsp sp ∗ memRegion (fsp + 576#64) 376 ∗
        memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1856#64) 880) by sep_ac_rfl_top_ext)) ?_
      exact Entails.trans (sepConj_mono_left (sendEkUnusedAt_split_nhr fsp))
        (Entails.of_eq (by sep_ac_rfl_top_ext))
    refine Entails.trans (Entails.of_eq (show _ =
      chunkedNoHeaderReceivedAt A (selfA + 8#64) st ∗ memRegion fsp 4144 ∗
      (memRegion (s0.sp - 40176#64) 16384 ∗
       (selfA ↦₆₄ 7#64) ∗ statesRecvRoAt img.base ∗ memRegion (selfA + 464#64) 464 ∗
       memRegion outA v1RecvSize ∗ ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
       A.pool ∗ stackAt fsp statesRecvCalleeStackX ∗ statesRecvSavedCells s0) by
        dsimp only [fsp]; rw [stackAt_statesRecvCalleeExt_eq_X s0.sp]; sep_ac_rfl_top_ext)) ?_
    refine Entails.trans (sepConj_mono hex57 (sepConj_mono_left hstk)) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro sp
    apply Entails.sepExists_elim; intro w
    exact Entails.sepExists_right w (Entails.sepExists_right sp (Entails.of_eq (by sep_ac_rfl_top_ext)))
  refine SepWPp.weaken_pre hpre_split ?_
  apply sepWPp_intro_ex_nhr hrun2; intro w
  apply sepWPp_intro_ex_nhr hrun2; intro sp
  apply SepWPp.pure_left; intro hw6
  set sp1 := { sp with w62 := w.b0.w6 }
  refine sepWPp_seq_clean_inImage_ax hinv2 (nhr_step_2132_2180_spills_ext hAx s2 fsp outA selfA msgA msg.epoch w sp
    (memRegion (s0.sp - 40176#64) 16384 ∗
     (selfA ↦₆₄ 7#64) ∗
     relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst st) (wordsBytes (words57List w)) ∗
     memRegion (selfA + 464#64) 464 ∗ messagePayloadAt spqrPolyApi msgA msg.payload ∗
     statesRecvRoAt img.base ∗ memRegion outA v1RecvSize ∗ A.pool ∗
     memRegion (fsp + 576#64) 376 ∗
     memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1856#64) 880 ∗
     nhrUnusedRestAt fsp ∗ statesRecvSavedCells s0)
    hinv2 hfsp_align hpc2 hrun2 hsp2 hx1_2 hx19_2 hx24_2) ?_
  intro s3 hpc3 hrun3 hinv3 ⟨hsp3, h3_19, h3_20, h3_21, h3_24, _, h3_8, h3_z, htr3⟩
  have htr30 : TraceCalleeSaved s3 s0 := htr3.trans htr20
  rw [hw6] at h3_8 h3_z
  by_cases hgt : msg.epoch > st.uc.epoch
  · have hcmp : ekCmpW8 (subsPState64 msg.epoch st.uc.epoch) = 1#32 := ekCmpW8_of_gt hgt
    rw [hcmp] at h3_8 h3_z
    have hz_f : s3.pstate.z = false := h3_z
    have hrecv := states_recv_noHeaderReceived_gt K st msg hgt
    have hexit := nhr_gt_2180_ret (A := A) (F := F) hdealloc s0 s3 outA selfA msg.epoch st sp1
      (memRegion (s0.sp - 40176#64) 16384 ∗ messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base)
      hsp0_align hpc3 hrun3 hsp3 hz_f h3_8 h3_19 h3_20 htr30
    refine sepWPp_of_statesRecv_exit_ext s0 s3 outA selfA msgA (.noHeaderReceived st) msg _ R ?_
    refine SepWP.weaken_pre ?_ (SepWP.mono hexit ?_)
    · have hrec := recompose57 (F_pred := fun dst => chunkedNoHeaderReceivedAt A dst st) (fsp + 2752#64) w
      have hself := selfA_noHeaderReceived_entails_memRegion selfA w
      unfold messageAt
      refine Entails.trans (Entails.of_eq (show _ =
        (words57At (fsp + 2752#64) w ∗
         relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst st) (wordsBytes (words57List w))) ∗
        ((selfA ↦₆₄ 7#64) ∗ words57At (selfA + 8#64) w ∗ memRegion (selfA + 464#64) 464) ∗
        (memRegion (s0.sp - 40176#64) 16384 ∗
         ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
         statesRecvRoAt img.base ∗ memRegion outA v1RecvSize ∗ A.pool ∗
         stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp1 ∗
         memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗
         memRegion (fsp + 1856#64) 880 ∗ nhrUnusedRestAt fsp ∗ statesRecvSavedCells s0) by sep_ac_rfl_top_ext)) ?_
      exact Entails.trans (sepConj_mono hrec (sepConj_mono_left hself))
        (Entails.of_eq (by dsimp only [fsp]; sep_ac_rfl_top_ext))
    · intro sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩
      refine ⟨Entails.trans hPf ?_, hsp_sf, hcs_sf, htr_sf⟩
      rw [hrecv, stackAt_statesRecvStackXExt_eq_X s0.sp]
      exact Entails.of_eq (by sep_ac_rfl_top_ext)
  · by_cases hlt : msg.epoch < st.uc.epoch
    · have hcmp : ekCmpW8 (subsPState64 msg.epoch st.uc.epoch) = 255#32 := ekCmpW8_of_lt hlt
      rw [hcmp] at h3_8 h3_z
      have hz_f : s3.pstate.z = false := h3_z
      have hrecv := states_recv_noHeaderReceived_lt K st msg hlt
      refine sepWPp_seq_clean_inImage_ax hinv3 (nhr_step_2180_lt_8664 s3 fsp _ hpc3 hrun3 hsp3 hz_f h3_8) ?_
      intro s4 hpc4 hrun4 hinv4 ⟨hsp4, h4_19, _, _, _, _, htr4⟩
      have hexit := nhr_noop_8664_ret_ext (A := A) (F := F) hAx s0 s4 outA selfA st w sp1
        (memRegion (s0.sp - 40176#64) 16384 ∗
         messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base ∗ A.pool)
        hinv4 hsp0_align rfl hpc4 hrun4 hsp4 (h4_19.trans h3_19) (htr4.trans htr30)
      refine sepWPp_of_statesRecv_exit_ext s0 s4 outA selfA msgA (.noHeaderReceived st) msg _ R ?_
      refine SepWP.weaken_pre ?_ (SepWP.mono hexit ?_)
      · have hself := selfA_noHeaderReceived_entails_memRegion selfA w
        unfold messageAt
        refine Entails.trans (Entails.of_eq (show _ =
          ((selfA ↦₆₄ 7#64) ∗ words57At (selfA + 8#64) w ∗ memRegion (selfA + 464#64) 464) ∗
          (memRegion (s0.sp - 40176#64) 16384 ∗
           ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
           statesRecvRoAt img.base ∗ A.pool ∗ memRegion outA v1RecvSize ∗
           words57At (fsp + 2752#64) w ∗
           relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst st) (wordsBytes (words57List w)) ∗
           stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp1 ∗
           memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗
           memRegion (fsp + 1856#64) 880 ∗ nhrUnusedRestAt fsp ∗ statesRecvSavedCells s0) by sep_ac_rfl_top_ext)) ?_
        exact Entails.trans (sepConj_mono_left hself) (Entails.of_eq (by dsimp only [fsp]; sep_ac_rfl_top_ext))
      · intro sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩
        refine ⟨Entails.trans hPf ?_, hsp_sf, hcs_sf, htr_sf⟩
        rw [hrecv, stackAt_statesRecvStackXExt_eq_X s0.sp]
        exact Entails.of_eq (by sep_ac_rfl_top_ext)
    · have heq : msg.epoch = st.uc.epoch :=
        BitVec.le_antisymm (BitVec.not_lt.mp hgt) (BitVec.not_lt.mp hlt)
      have hcmp : ekCmpW8 (subsPState64 msg.epoch st.uc.epoch) = 0#32 := ekCmpW8_of_eq heq
      rw [hcmp] at h3_z
      have hz_t : s3.pstate.z = true := h3_z
      refine sepWPp_seq_clean_inImage_ax hinv3 (nhr_step_2180_eq_8568 s3 fsp _ hpc3 hrun3 hsp3 hz_t) ?_
      intro s4 hpc4 hrun4 hinv4 ⟨hsp4, h4_19, h4_20, h4_21, h4_24, _, htr4⟩
      have htr40 : TraceCalleeSaved s4 s0 := htr4.trans htr30
      by_cases hhdr : ∃ chunk, msg.payload = .hdr chunk
      · rcases hhdr with ⟨chunk, hp⟩
        have h20_eq : s4.readReg64 .x20 = st.uc.epoch := by
          rw [h4_20, h3_20, heq]
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (nhr_hdr_8568_ret_ax_grown hb hAx hcall s0 s4 outA selfA msgA st msg chunk w sp1 R
            hinv4 heq hp hinv hsp0_align hpc4 hrun4 hsp4
            (h4_19.trans h3_19) h20_eq (h4_21.trans h3_21) (h4_24.trans h3_24) htr40)
        rw [hp]; dsimp only [fsp]; rw [stackAt_statesRecvCalleeExt_eq_X s0.sp]; sep_ac_rfl_top_ext
      · have hno : ∀ c, msg.payload ≠ .hdr c := fun c hc => hhdr ⟨c, hc⟩
        have hrecv := states_recv_noHeaderReceived_eq_non_hdr K st msg heq hno
        have hstep_no := nhr_step_8568_non_hdr_8664 s4 fsp msgA msg.payload
          (memRegion (s0.sp - 40176#64) 16384 ∗
           words57At (fsp + 2752#64) w ∗ words57At (selfA + 8#64) w ∗
           (msgA ↦₆₄ msg.epoch) ∗ sendEkSpillsAt fsp sp1 ∗
           (selfA ↦₆₄ 7#64) ∗
           relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst st) (wordsBytes (words57List w)) ∗
           memRegion (selfA + 464#64) 464 ∗
           statesRecvRoAt img.base ∗ memRegion outA v1RecvSize ∗ A.pool ∗
           stackAt fsp statesRecvCalleeStackX ∗ memRegion (fsp + 576#64) 376 ∗
           memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1856#64) 880 ∗
           nhrUnusedRestAt fsp ∗ statesRecvSavedCells s0)
          hno hpc4 hrun4 hsp4 (h4_24.trans h3_24)
        refine sepWPp_seq_clean_inImage_ax hinv4
          (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl_top_ext)) hstep_no) ?_
        intro s5 hpc5 hrun5 hinv5 ⟨hsp5, h5_19, _, _, _, _, htr5⟩
        have hexit := nhr_noop_8664_ret_ext (A := A) (F := F) hAx s0 s5 outA selfA st w sp1
          (memRegion (s0.sp - 40176#64) 16384 ∗
           messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base ∗ A.pool)
          hinv5 hsp0_align rfl hpc5 hrun5 hsp5 (h5_19.trans (h4_19.trans h3_19)) (htr5.trans htr40)
        refine sepWPp_of_statesRecv_exit_ext s0 s5 outA selfA msgA (.noHeaderReceived st) msg _ R ?_
        refine SepWP.weaken_pre ?_ (SepWP.mono hexit ?_)
        · have hself := selfA_noHeaderReceived_entails_memRegion selfA w
          unfold messageAt
          refine Entails.trans (Entails.of_eq (show _ =
            ((selfA ↦₆₄ 7#64) ∗ words57At (selfA + 8#64) w ∗ memRegion (selfA + 464#64) 464) ∗
            (memRegion (s0.sp - 40176#64) 16384 ∗
             ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
             statesRecvRoAt img.base ∗ A.pool ∗ memRegion outA v1RecvSize ∗
             words57At (fsp + 2752#64) w ∗
             relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst st) (wordsBytes (words57List w)) ∗
             stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp1 ∗
             memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗
             memRegion (fsp + 1856#64) 880 ∗ nhrUnusedRestAt fsp ∗ statesRecvSavedCells s0) by sep_ac_rfl_top_ext)) ?_
          exact Entails.trans (sepConj_mono_left hself) (Entails.of_eq (by dsimp only [fsp]; sep_ac_rfl_top_ext))
        · intro sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩
          refine ⟨Entails.trans hPf ?_, hsp_sf, hcs_sf, htr_sf⟩
          rw [hrecv, stackAt_statesRecvStackXExt_eq_X s0.sp]
          exact Entails.of_eq (by sep_ac_rfl_top_ext)

theorem states_recv_ok_x_of_variants_ext_ax
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hvar : ∀ (self : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi),
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName)
        ((statesRecvVariantSpecExt A F K img.base self msg).inImage img)) :
    StatesRecvOkXExt img A F K ext := by
  dsimp only [StatesRecvOkXExt]
  refine subroutine_ok_outcome_intro fun ⟨outA, selfA, msgA, self, msg⟩ R s0 hpc hrun hpre halign =>
    (hvar self msg).mono_outcome (outA, selfA, msgA) R s0 hpc hrun hpre halign fun _ hout => hout

private theorem ct1SampledExt678Deps_mk
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)} :
    Ct1SampledExt678Deps img A F K ext where
  send_ct2_and_encode :=
    _root_.CryptoVerification.SpqrV1.States.Recv.ct1Sampled_send_ct2_and_encode_ext
  recv_ek_common_prefix :=
    _root_.LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledExtPart7.ct1Sampled_recv_ek_common_prefix_ext
  path_none_no_ack :=
    _root_.LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledExtPart7.ct1Sampled_path_none_no_ack_extStack
  path_none_ack :=
    _root_.LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledExtPart8.ct1Sampled_path_none_ack_extStack
  path_some_err :=
    _root_.LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledExtPart8.ct1Sampled_path_some_err_ext

/-- Per-variant `.inImage img` correctness of `<spqr::v1::chunked::states::States>::recv`
    at `statesRecvStackXExt` (`40176` B) across all 11 `States` constructors under
    `AllocContractsX img A ext`, `DeallocOkExt img.base A ext`, and `StatesRecvContractsAx`. -/
theorem states_recv_variant_x_ext_ax_full
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext)
    (hdealloc : DeallocOkExt img.base A ext)
    (hC : StatesRecvContractsAx img A F K ext)
    (self : States spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName)
      ((statesRecvVariantSpecExt A F K img.base self msg).inImage img) := by
  cases self with
  | keysUnsampled st =>
    exact states_recv_keysUnsampled_ok_x_ext img A F K ext hAx st msg
  | keysSampled st =>
    exact states_recv_keysSampled_ok_x_ext hAx hdealloc hC.keysSampledRecvCt1Chunk_ok st msg
  | headerSent st =>
    exact states_recv_headerSent_ok_x_ext hAx hdealloc hC.headerSentRecvCt1Chunk_ok st msg
  | ct1Received st =>
    exact states_recv_ct1Received_ok_x_ext hAx hdealloc hC.ct1ReceivedRecvCt2Chunk_ok st msg
  | ekSentCt1Received st =>
    exact states_recv_ekSentCt1Received_ok_x_ax hAx hdealloc hC.ekSentCt1ReceivedRecvCt2Chunk_ok st msg
  | noHeaderReceived st =>
    exact states_recv_noHeaderReceived_ok_x_ax_grown hAx hdealloc hC.noHeaderReceivedRecvHdrChunk_ok st msg
  | headerReceived st =>
    exact states_recv_headerReceived_ok_x_ext hAx hdealloc st msg
  | ct1Sampled st =>
    exact states_recv_ct1Sampled_ok_x_ax hAx hdealloc hC ct1SampledExt678Deps_mk st msg
  | ekReceivedCt1Sampled st =>
    exact states_recv_ekReceivedCt1Sampled_ok_x_ext hAx hdealloc hC.ekReceivedCt1SampledRecvCt1Ack_ok st msg
  | ct1Acknowledged st =>
    exact states_recv_ct1Acknowledged_ok_x_ext hAx hdealloc hC.ct1AcknowledgedRecvEkChunk_ok st msg
  | ct2Sampled st =>
    exact states_recv_ct2Sampled_ok_x_ext hAx hdealloc st msg

/-- `<spqr::v1::chunked::states::States>::recv` satisfies `statesRecvSpecXExt A F K img`
    (`40176` B stack, `.inImage img`) on `tripleRatchetProgAtExt img.base ext` under
    `AllocContractsX`, `DeallocOkExt`, and `StatesRecvContractsAx`. -/
theorem states_recv_ok_x_ext_ax_full
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext)
    (hdealloc : DeallocOkExt img.base A ext)
    (hC : StatesRecvContractsAx img A F K ext) :
    StatesRecvOkXExt img A F K ext :=
  states_recv_ok_x_of_variants_ext_ax (states_recv_variant_x_ext_ax_full hAx hdealloc hC)

theorem states_recv_variant_x_ext_ax
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext)
    (hdealloc : DeallocOkExt img.base A ext)
    (hC : StatesRecvContractsExt img A F K ext)
    (self : States spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName)
      ((statesRecvVariantSpecExt A F K img.base self msg).inImage img) :=
  states_recv_variant_x_ext_ax_full hAx hdealloc hC.toAx self msg

/-- `<spqr::v1::chunked::states::States>::recv` satisfies `statesRecvSpecXExt A F K img`
    (`40176` B stack, `.inImage img`) on `tripleRatchetProgAtExt img.base ext` under
    `AllocContractsX`, `DeallocOkExt`, and `StatesRecvContractsExt`. -/
theorem states_recv_ok_x_ext_ax
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext)
    (hdealloc : DeallocOkExt img.base A ext)
    (hC : StatesRecvContractsExt img A F K ext) :
    StatesRecvOkXExt img A F K ext :=
  states_recv_ok_x_ext_ax_full hAx hdealloc hC.toAx

end CryptoVerification.SpqrV1.States.Recv
