/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchExt
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Defs
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart2
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledExtPart1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledExtPart3
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledExtPart9
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart10
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart3
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart7
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart8
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart9
import LibsignalBinary.Proofs.SpqrV1.States.Recv.Dispatch
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` — `.ct1Sampled` Arm (`AllocContractsX`, Part 10)

**Checked by Lean.** Top-level `AllocContractsX` + `.inImage img` composition
(`states_recv_ct1Sampled_ok_x_ext` and `states_recv_ct1Sampled_ok_x_ax`) for the `.ct1Sampled` arm
(`0x55a4c`, `entry + 1528`) at `statesRecvStackXExt` (`40176` B).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 400000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (ShaState hmacWith toBEBytes)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Poly.DecodedMessage
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.States

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit BitVec.toNat_zero
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_48 sp_sub_4240_add_4096 sp_sub_144_add_48
  sp_sub_4240_add_4144

/-- Segment contracts for Paths 4a, 4b, and 5a of the `.ct1Sampled` arm under `AllocContractsX`. -/
structure Ct1SampledExt678Deps (img : Obj.Image) (A : RustAlloc) (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State)) : Prop where
  send_ct2_and_encode :
    ∀ {P_pan : Prop}
      (hb : img.base &&& 0xfff#64 = 0#64)
      (hsendCt2 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name)
        ((growToCalleeExt unchunkedSendCt2Stack
          (unchunkedCt1SentEkReceivedSendCt2Spec A F K img.base)).inImage img))
      (hsendCt2Enc : subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr sendCt2EncoderName)
        ((growToCalleeExt sendCt2EncoderStack (sendCt2EncoderSpec A)).inImage img))
      (s0 s_in : State) (fsp : BitVec 64)
      (uc_ek : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F))
      (outUc : Unchunked.SendCt.Ct2Sent (spqrAuthApi F)) (ct2 : Bytes) (mac : Mac)
      (outEnc : PolyEncoder)
      (hsc : uc_ek.send_ct2 K = .ok (outUc, ct2, mac))
      (henc : Chunked.SendCt.send_ct2_encoder spqrPolyApi ct2 mac = .ok outEnc)
      (Frame R : SepProp) {post : State → SepProp → Prop}
      (hinv : ImgCallInv img s_in)
      (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
      (hpc : s_in.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 11624#64)
      (hrun : s_in.status = .Running) (hsp : s_in.sp = fsp) (htr : TraceCalleeSaved s_in s0)
      (hx21 : s_in.readReg64 .x21 = fsp + 3856#64) (hx29 : s_in.readReg64 .x29 = fsp + 4144#64),
      (∀ (sf : State) (g_uc : AuthWords) (ct2Cap ct2Ptr macCap macPtr : BitVec 64),
        sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 11696#64 →
        sf.status = .Running → sf.sp = fsp → ImgCallInv img sf →
        sf.readReg64 .x19 = s_in.readReg64 .x19 → sf.readReg64 .x20 = macCap →
        sf.readReg64 .x21 = fsp + 3856#64 → sf.readReg64 .x24 = s_in.readReg64 .x24 →
        sf.readReg64 .x25 = ct2Cap → sf.readReg64 .x26 = ct2Ptr →
        sf.readReg64 .x27 = macPtr → sf.readReg64 .x28 = s_in.readReg64 .x28 →
        sf.readReg64 .x29 = fsp + 4144#64 → TraceCalleeSaved sf s0 →
        SepWP (tripleRatchetProgAtExt img.base ext)
          ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 11696#64) sf
          ((polyEncoderAt A (fsp + 1856#64) outEnc ∗
            wordsAt (fsp + 2256#64) (ct2SentWordsList g_uc outUc.epoch) ∗
            relocatedHeap (fun dst => unchunkedCt2SentAt A dst outUc)
              (wordsBytes (ct2SentWordsList g_uc outUc.epoch)) ∗
            vecCapPtrDealloc A ct2Cap ct2Ptr ∗ vecCapPtrDealloc A macCap macPtr ∗
            memRegion (fsp + 3856#64) 128 ∗ memRegion (fsp + 3992#64) 104 ∗
            unchunkedSendCt2RoAt img.base ∗ A.pool ∗ stackAt fsp statesRecvCalleeStackXExt) ∗ Frame)
          (fun sm Pm =>
            SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 Reg.lr) sm Pm post
              (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
                (sf.mem ⊨ (⌜(P_pan ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)))) →
      SepWP (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 36780#64) s_in
        ((memRegion (fsp + 1856#64) 400 ∗ memRegion (fsp + 2256#64) 56 ∗
          unchunkedCt1SentEkReceivedAt A (fsp + 3856#64) uc_ek ∗
          memRegion (fsp + 3992#64) 104 ∗ unchunkedSendCt2RoAt img.base ∗
          A.pool ∗ stackAt fsp statesRecvCalleeStackXExt) ∗ Frame)
        (fun sm Pm =>
          SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 Reg.lr) sm Pm post
            (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
              (sf.mem ⊨ (⌜(P_pan ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)))
  recv_ek_common_prefix :
    ∀ {P_pan : Prop}
      (hAx : AllocContractsX img A ext) (hadd_call : AddChunkOkX img A ext)
      (hdec_call : subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr polyDecoderDecodedMessageName)
        ((growToCalleeExt polyDecoderDecodedMessageStack
          (polyDecoderDecodedMessageSpec A img.base)).inImage img))
      (hb : img.base &&& 0xfff#64 = 0#64)
      (s0 s_in : State) (fsp selfA outA msgA ack_val : BitVec 64)
      (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F)) (chunk : Chunk)
      (hlen : st.receiving_ek.pts.length = 16) (hsort : PolyDecoderStrictSorted st.receiving_ek)
      (Rest R : SepProp) {post : State → SepProp → Prop}
      (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (hfsp : fsp = s0.sp - 4240#64)
      (hpc : s_in.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 11404#64)
      (hrun : s_in.status = .Running) (hsp : s_in.sp = fsp) (hx1 : s_in.readReg64 .x1 = selfA)
      (hx19 : s_in.readReg64 .x19 = outA) (hx20 : s_in.readReg64 .x20 = st.uc.epoch)
      (hx21 : s_in.readReg64 .x21 = fsp + 3856#64) (hx22 : s_in.readReg64 .x22 = ack_val)
      (hx23 : s_in.readReg64 .x23 = polyEncoderTagVal st.sending_ct1)
      (hx24 : s_in.readReg64 .x24 = msgA) (hx28 : s_in.readReg64 .x28 = fsp + 3272#64)
      (hx29 : s_in.readReg64 .x29 = fsp + 4144#64)
      (htr : TraceCalleeSaved s_in s0) (hinv : ImgCallInv img s_in),
      (∀ (sf : State) (c_uc : Words16) (sc : CopyScratchStack) (k : EpilogueStoreStack),
        sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 11496#64 →
        sf.status = .Running → sf.sp = fsp → sf.readReg64 .x19 = outA →
        sf.readReg64 .x20 = st.uc.epoch → sf.readReg64 .x21 = fsp + 3856#64 →
        sf.readReg64 .x22 = ack_val → sf.readReg64 .x23 = polyEncoderTagVal st.sending_ct1 →
        sf.readReg64 .x24 = msgA → sf.readReg64 .x28 = fsp + 3272#64 →
        sf.readReg64 .x29 = fsp + 4144#64 → TraceCalleeSaved sf s0 → ImgCallInv img sf →
        SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 Reg.lr) sf
          (optVecU8At A (fsp + 3832#64) (decodedMessageTotal (addChunkTotal st.receiving_ek chunk)) ∗
            polyDecoderAt A (fsp + 2752#64) (addChunkTotal st.receiving_ek chunk) ∗
            chunkAt (msgA + 10#64) chunk ∗ statesRecvRoAt img.base ∗ A.pool ∗
            stackAt fsp statesRecvCalleeStackXExt ∗
            (polyEncoderAt A selfA st.sending_ct1 ∗ wordsAt (selfA + 400#64) c_uc.toList ∗
              wordsAt (fsp + 3696#64) c_uc.toList ∗
              relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
              memRegion (selfA + 528#64) 400 ∗ copyScratchStackAt fsp sc ∗
              epilogueStoreStackPart1At fsp k ∗ ((fsp + 232#64) ↦₆₄ selfA) ∗
              ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
              wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
              memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
              memRegion (fsp + 976#64) 1776 ∗ memRegion (fsp + 3152#64) 544 ∗
              memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3856#64) 288 ∗ Rest))
          post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ (⌜(P_pan ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 Reg.lr) s_in
        (polyEncoderAt A selfA st.sending_ct1 ∗ unchunkedCt1SentAt A (selfA + 400#64) st.uc ∗
          polyDecoderAt A (selfA + 528#64) st.receiving_ek ∗ chunkAt (msgA + 10#64) chunk ∗
          statesRecvRoAt img.base ∗ A.pool ∗ stackAt fsp statesRecvCalleeStackXExt ∗
          memRegion fsp 4144 ∗ Rest)
        post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (⌜(P_pan ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))
  path_none_no_ack :
    ∀ (hAx : AllocContractsX img A ext) (s0 s_in : State) (fsp selfA outA : BitVec 64)
      (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
      (dec' : PolyDecoder) (c_uc : Words16) (sc : CopyScratchStack) (k : EpilogueStoreStack)
      (Rest : SepProp)
      (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
      (hfsp : fsp = s0.sp - 4240#64)
      (hpc : s_in.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 11496#64)
      (hrun : s_in.status = .Running) (hsp : s_in.sp = fsp) (hx19 : s_in.readReg64 .x19 = outA)
      (hx22 : s_in.readReg64 .x22 = 0#64) (hx23 : s_in.readReg64 .x23 = polyEncoderTagVal st.sending_ct1)
      (hx29 : s_in.readReg64 .x29 = fsp + 4144#64)
      (htr : TraceCalleeSaved s_in s0) (hinv : ImgCallInv img s_in),
      SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s_in
        (optVecU8At A (fsp + 3832#64) none ∗ polyDecoderAt A (fsp + 2752#64) dec' ∗
          polyEncoderAt A selfA st.sending_ct1 ∗ wordsAt (selfA + 400#64) c_uc.toList ∗
          wordsAt (fsp + 3696#64) c_uc.toList ∗
          relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
          memRegion (selfA + 528#64) 400 ∗ copyScratchStackAt fsp sc ∗ epilogueStoreStackPart1At fsp k ∗
          ((fsp + 232#64) ↦₆₄ selfA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
          wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
          memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗ memRegion (fsp + 976#64) 1776 ∗
          memRegion (fsp + 3152#64) 544 ∗ memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3856#64) 288 ∗
          memRegion outA v1RecvSize ∗ stackAt fsp statesRecvCalleeStackXExt ∗
          statesRecvSavedCells s0 ∗ Rest)
        (fun sf Pf =>
          (Pf ⊢ resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct1Sampled { st with receiving_ek := dec' } }) ∗
            memRegion selfA chunkedStatesSize ∗ stackAt s0.sp statesRecvStackXExt ∗ Rest) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
  path_none_ack :
    ∀ (hb : img.base &&& 0xfff#64 = 0#64) (hAx : AllocContractsX img A ext)
      (hdealloc : DeallocOkExt img.base A ext) (s0 s_in : State) (fsp selfA outA : BitVec 64)
      (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
      (dec' : PolyDecoder) (c_uc : Words16) (sc : CopyScratchStack) (k : EpilogueStoreStack)
      (Rest : SepProp)
      (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
      (hfsp : fsp = s0.sp - 4240#64)
      (hpc : s_in.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 11496#64)
      (hrun : s_in.status = .Running) (hsp : s_in.sp = fsp) (hx19 : s_in.readReg64 .x19 = outA)
      (hx22 : s_in.readReg64 .x22 = 1#64) (hx28 : s_in.readReg64 .x28 = fsp + 3272#64)
      (htr : TraceCalleeSaved s_in s0) (hinv : ImgCallInv img s_in),
      SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s_in
        (optVecU8At A (fsp + 3832#64) none ∗ polyDecoderAt A (fsp + 2752#64) dec' ∗
          polyEncoderAt A selfA st.sending_ct1 ∗ wordsAt (selfA + 400#64) c_uc.toList ∗
          wordsAt (fsp + 3696#64) c_uc.toList ∗
          relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
          memRegion (selfA + 528#64) 400 ∗ copyScratchStackAt fsp sc ∗ epilogueStoreStackPart1At fsp k ∗
          ((fsp + 232#64) ↦₆₄ selfA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
          wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
          memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗ memRegion (fsp + 976#64) 1776 ∗
          memRegion (fsp + 3152#64) 544 ∗ memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3856#64) 288 ∗
          memRegion outA v1RecvSize ∗ statesRecvRoAt img.base ∗ A.pool ∗
          stackAt fsp statesRecvCalleeStackXExt ∗ statesRecvSavedCells s0 ∗ Rest)
        (fun sf Pf =>
          (Pf ⊢ resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct1Acknowledged { uc := st.uc, receiving_ek := dec' } }) ∗
            memRegion selfA chunkedStatesSize ∗ statesRecvRoAt img.base ∗ A.pool ∗
            stackAt s0.sp statesRecvStackXExt ∗ Rest) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
  path_some_err :
    ∀ (hdealloc : DeallocOkExt img.base A ext)
      (hrecv_ek : subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr unchunkedCt1SentRecvEkName)
        ((growToCalleeExt unchunkedRecvEkStack
          (unchunkedCt1SentRecvEkSpec A F K)).inImage img))
      (s0 s_in : State) (fsp selfA outA : BitVec 64)
      (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
      (dec' : PolyDecoder) (c_uc : Words16) (decoded : Bytes) (err : Error)
      (sc : CopyScratchStack) (k : EpilogueStoreStack) (Rest : SepProp)
      (hres : st.uc.recv_ek K st.uc.epoch decoded = .error (.err err))
      (herr_val : err = .erroneousDataReceived)
      (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
      (hfsp : fsp = s0.sp - 4240#64)
      (hpc : s_in.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 11496#64)
      (hrun : s_in.status = .Running) (hsp : s_in.sp = fsp) (hx19 : s_in.readReg64 .x19 = outA)
      (hx20 : s_in.readReg64 .x20 = st.uc.epoch)
      (htr : TraceCalleeSaved s_in s0) (hinv : ImgCallInv img s_in),
      SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s_in
        (optVecU8At A (fsp + 3832#64) (some decoded) ∗ polyDecoderAt A (fsp + 2752#64) dec' ∗
          polyEncoderAt A selfA st.sending_ct1 ∗ wordsAt (selfA + 400#64) c_uc.toList ∗
          wordsAt (fsp + 3696#64) c_uc.toList ∗
          relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
          memRegion (selfA + 528#64) 400 ∗ copyScratchStackAt fsp sc ∗ epilogueStoreStackPart1At fsp k ∗
          ((fsp + 232#64) ↦₆₄ selfA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
          wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
          memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗ memRegion (fsp + 976#64) 1776 ∗
          memRegion (fsp + 3152#64) 544 ∗ memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3856#64) 288 ∗
          memRegion outA v1RecvSize ∗ A.pool ∗ stackAt fsp statesRecvCalleeStackXExt ∗
          statesRecvSavedCells s0 ∗ Rest)
        (fun sf Pf =>
          (Pf ⊢ resultV1RecvAt A (F := F) outA (.error (.err err)) ∗
            memRegion selfA chunkedStatesSize ∗ A.pool ∗ stackAt s0.sp statesRecvStackXExt ∗ Rest) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)

set_option maxHeartbeats 800000 in
private theorem ct1Sampled_some_ok_ack_pre1_ext {A : RustAlloc} {F : ShaCompress}
    (b fsp selfA outA msgA : BitVec 64) (s0 : State)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (dec' : PolyDecoder)
    (uc_ek : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F))
    (c_uc : Words16) (sc : CopyScratchStack) (k : EpilogueStoreStack) :
    unchunkedCt1SentRecvEkResAt A (fsp + 1856#64) (.ok uc_ek) ∗
      memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1984#64) 768 ∗
      memRegion (fsp + 3696#64) 128 ∗ memRegion (fsp + 3832#64) 24 ∗
      A.pool ∗ stackAt fsp statesRecvCalleeStackXExt ∗
      (polyDecoderAt A (fsp + 2752#64) dec' ∗ polyEncoderAt A selfA st.sending_ct1 ∗
        wordsAt (selfA + 400#64) c_uc.toList ∗ memRegion (selfA + 528#64) 400 ∗
        copyScratchStackAt fsp sc ∗ epilogueStoreStackPart1At fsp k ∗
        ((fsp + 232#64) ↦₆₄ selfA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 3152#64) 544 ∗ memRegion (fsp + 3824#64) 8 ∗
        memRegion (fsp + 3856#64) 288 ∗ memRegion outA v1RecvSize ∗ statesRecvRoAt b ∗
        statesRecvSavedCells s0 ∗ messageAt spqrPolyApi msgA msg) ⊢
    ∃∗ c_ek : Words16,
      ⌜c_ek.w0.toNat < 2 ^ 63⌝ ∗
      wordsAt (fsp + 1856#64) c_ek.toList ∗ memRegion (fsp + 3856#64) 128 ∗
      copyScratchStackAt fsp sc ∗
      (relocatedHeap (fun a => unchunkedCt1SentEkReceivedAt A a uc_ek) (wordsBytes c_ek.toList) ∗
        polyDecoderAt A (fsp + 2752#64) dec' ∗ polyEncoderAt A selfA st.sending_ct1 ∗
        wordsAt (selfA + 400#64) c_uc.toList ∗ memRegion (selfA + 528#64) 400 ∗
        epilogueStoreStackPart1At fsp k ∗ ((fsp + 232#64) ↦₆₄ selfA) ∗
        ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1984#64) 768 ∗
        memRegion (fsp + 3152#64) 544 ∗ memRegion (fsp + 3696#64) 128 ∗
        memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3832#64) 24 ∗
        memRegion (fsp + 3984#64) 160 ∗ memRegion outA v1RecvSize ∗ statesRecvRoAt b ∗
        A.pool ∗ stackAt fsp statesRecvCalleeStackXExt ∗ statesRecvSavedCells s0 ∗
        messageAt spqrPolyApi msgA msg) := by
  dsimp only [unchunkedCt1SentRecvEkResAt]
  rw [ProofLib.memRegion_split' (b := fsp + 3856#64) (n := 128) (k := 160) (b' := fsp + 3984#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans (sepConj_mono_left
    (unchunkedCt1SentEkReceivedAt_extract_words16 A (fsp + 1856#64) uc_ek)) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro c_ek
  exact Entails.sepExists_right c_ek (Entails.of_eq (by ac_rfl))

set_option maxHeartbeats 800000 in
private theorem ct1Sampled_some_ok_ack_pre3_ext {A : RustAlloc} {F : ShaCompress}
    (b fsp selfA outA msgA : BitVec 64) (s0 : State)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (dec' : PolyDecoder)
    (uc_ek : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F))
    (c_uc c_ek : Words16) (sc : CopyScratchStack) (k : EpilogueStoreStack) :
    wordsAt (fsp + 1856#64) c_ek.toList ∗ wordsAt (fsp + 3856#64) c_ek.toList ∗
      copyScratchStackAt fsp { sc with wb0 := c_ek.w1 } ∗
      (relocatedHeap (fun a => unchunkedCt1SentEkReceivedAt A a uc_ek) (wordsBytes c_ek.toList) ∗
        polyDecoderAt A (fsp + 2752#64) dec' ∗ polyEncoderAt A selfA st.sending_ct1 ∗
        wordsAt (selfA + 400#64) c_uc.toList ∗ memRegion (selfA + 528#64) 400 ∗
        epilogueStoreStackPart1At fsp k ∗ ((fsp + 232#64) ↦₆₄ selfA) ∗
        ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1984#64) 768 ∗
        memRegion (fsp + 3152#64) 544 ∗ memRegion (fsp + 3696#64) 128 ∗
        memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3832#64) 24 ∗
        memRegion (fsp + 3984#64) 160 ∗ memRegion outA v1RecvSize ∗ statesRecvRoAt b ∗
        A.pool ∗ stackAt fsp statesRecvCalleeStackXExt ∗ statesRecvSavedCells s0 ∗
        messageAt spqrPolyApi msgA msg) ⊢
    (memRegion (fsp + 1856#64) 400 ∗ memRegion (fsp + 2256#64) 56 ∗
      unchunkedCt1SentEkReceivedAt A (fsp + 3856#64) uc_ek ∗
      memRegion (fsp + 3992#64) 104 ∗ unchunkedSendCt2RoAt b ∗
      A.pool ∗ stackAt fsp statesRecvCalleeStackXExt) ∗
    (polyDecoderAt A (fsp + 2752#64) dec' ∗ polyEncoderAt A selfA st.sending_ct1 ∗
      wordsAt (selfA + 400#64) c_uc.toList ∗ memRegion (selfA + 528#64) 400 ∗
      copyScratchStackAt fsp { sc with wb0 := c_ek.w1 } ∗ epilogueStoreStackPart1At fsp k ∗
      ((fsp + 232#64) ↦₆₄ selfA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
      wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
      memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
      memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 2312#64) 440 ∗
      memRegion (fsp + 3152#64) 544 ∗ memRegion (fsp + 3696#64) 128 ∗
      memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3832#64) 24 ∗
      memRegion (fsp + 3984#64) 8 ∗ memRegion (fsp + 4096#64) 48 ∗
      memRegion outA v1RecvSize ∗
      (statesRecvJumpTableAt b ∗ tokenInitAt b ∗ reduceTableAt b) ∗
      statesRecvSavedCells s0 ∗ messageAt spqrPolyApi msgA msg) := by
  refine Entails.trans (sepConj_mono_left (words16_entails_memRegion_128 (fsp + 1856#64) c_ek)) ?_
  have hek := Relocatable.reconstruct_128 (fun a => unchunkedCt1SentEkReceivedAt A a uc_ek) (fsp + 3856#64) c_ek
  have h1856_join :
      memRegion (fsp + 1856#64) 128 ∗ memRegion (fsp + 1984#64) 768 =
      memRegion (fsp + 1856#64) 400 ∗ memRegion (fsp + 2256#64) 56 ∗ memRegion (fsp + 2312#64) 440 := by
    rw [← ProofLib.memRegion_split' (b := fsp + 1856#64) (n := 128) (k := 768) (b' := fsp + 1984#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 1856#64) (n := 400) (k := 496) (b' := fsp + 2256#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 2256#64) (n := 56) (k := 440) (b' := fsp + 2312#64) rfl (by bv_omega) (by decide)]
  rw [ProofLib.memRegion_split' (b := fsp + 3984#64) (n := 8) (k := 152) (b' := fsp + 3992#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3992#64) (n := 104) (k := 48) (b' := fsp + 4096#64) rfl (by bv_omega) (by decide),
      statesRecvRoAt_eq_unchunkedSendCt2 b]
  refine Entails.trans (Entails.of_eq (show _ =
    (memRegion (fsp + 1856#64) 128 ∗ memRegion (fsp + 1984#64) 768) ∗
    (wordsAt (fsp + 3856#64) c_ek.toList ∗
      relocatedHeap (fun a => unchunkedCt1SentEkReceivedAt A a uc_ek) (wordsBytes c_ek.toList)) ∗
    (memRegion (fsp + 3992#64) 104 ∗ unchunkedSendCt2RoAt b ∗
      A.pool ∗ stackAt fsp statesRecvCalleeStackXExt) ∗
    (polyDecoderAt A (fsp + 2752#64) dec' ∗ polyEncoderAt A selfA st.sending_ct1 ∗
      wordsAt (selfA + 400#64) c_uc.toList ∗ memRegion (selfA + 528#64) 400 ∗
      copyScratchStackAt fsp { sc with wb0 := c_ek.w1 } ∗ epilogueStoreStackPart1At fsp k ∗
      ((fsp + 232#64) ↦₆₄ selfA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
      wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
      memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
      memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 3152#64) 544 ∗
      memRegion (fsp + 3696#64) 128 ∗ memRegion (fsp + 3824#64) 8 ∗
      memRegion (fsp + 3832#64) 24 ∗ memRegion (fsp + 3984#64) 8 ∗
      memRegion (fsp + 4096#64) 48 ∗ memRegion outA v1RecvSize ∗
      (statesRecvJumpTableAt b ∗ tokenInitAt b ∗ reduceTableAt b) ∗
      statesRecvSavedCells s0 ∗ messageAt spqrPolyApi msgA msg) by ac_rfl)) ?_
  rw [h1856_join]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left hek)) ?_
  exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 1200000 in
/-- Path 5c from `+11496 -> s0.x30` (`outMsg = some decoded`, `recv_ek = .ok uc_ek`, `ack = true`)
    under `AllocContractsX` + `.inImage img` at `statesRecvCalleeStackXExt` (`35936` B). -/
theorem ct1Sampled_path_some_ok_ack_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hA : AllocContractsX img A ext)
    (hdealloc : DeallocOkExt img.base A ext)
    (hrecv_ek : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr unchunkedCt1SentRecvEkName)
      ((growToCalleeExt unchunkedRecvEkStack
        (unchunkedCt1SentRecvEkSpec A F K)).inImage img))
    (hsendCt2 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name)
      ((growToCalleeExt unchunkedSendCt2Stack
        (unchunkedCt1SentEkReceivedSendCt2Spec A F K img.base)).inImage img))
    (hsendCt2Enc : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr sendCt2EncoderName)
      ((growToCalleeExt sendCt2EncoderStack (sendCt2EncoderSpec A)).inImage img))
    (h678 : Ct1SampledExt678Deps img A F K ext)
    (s0 s_in : State) (fsp selfA outA msgA : BitVec 64)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk) (decoded : Bytes)
    (uc_ek : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F))
    (outUc : Unchunked.SendCt.Ct2Sent (spqrAuthApi F)) (ct2 : Bytes) (mac : Mac)
    (outEnc : PolyEncoder) (c_uc : Words16) (sc : CopyScratchStack) (k : EpilogueStoreStack)
    (R : SepProp)
    (heq : msg.epoch = st.uc.epoch) (hpay : msg.payload = .ekCt1Ack chunk)
    (hlen : st.receiving_ek.pts.length = 16) (hsort : PolyDecoderStrictSorted st.receiving_ek)
    (hdec : decodedMessageTotal (addChunkTotal st.receiving_ek chunk) = some decoded)
    (hrek : st.uc.recv_ek K st.uc.epoch decoded = .ok uc_ek)
    (hsc : uc_ek.send_ct2 K = .ok (outUc, ct2, mac))
    (henc : Chunked.SendCt.send_ct2_encoder spqrPolyApi ct2 mac = .ok outEnc)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp : fsp = s0.sp - 4240#64)
    (hpc : s_in.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 11496#64)
    (hrun : s_in.status = .Running) (hsp : s_in.sp = fsp)
    (hx19 : s_in.readReg64 .x19 = outA) (hx20 : s_in.readReg64 .x20 = st.uc.epoch)
    (hx21 : s_in.readReg64 .x21 = fsp + 3856#64) (hx22 : s_in.readReg64 .x22 = 1#64)
    (hx23 : s_in.readReg64 .x23 = polyEncoderTagVal st.sending_ct1)
    (hx28 : s_in.readReg64 .x28 = fsp + 3272#64) (hx29 : s_in.readReg64 .x29 = fsp + 4144#64)
    (htr : TraceCalleeSaved s_in s0) (hinv : ImgCallInv img s_in) :
    let dec' := addChunkTotal st.receiving_ek chunk
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s_in
      (optVecU8At A (fsp + 3832#64) (some decoded) ∗ polyDecoderAt A (fsp + 2752#64) dec' ∗
        polyEncoderAt A selfA st.sending_ct1 ∗ wordsAt (selfA + 400#64) c_uc.toList ∗
        wordsAt (fsp + 3696#64) c_uc.toList ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
        memRegion (selfA + 528#64) 400 ∗ copyScratchStackAt fsp sc ∗ epilogueStoreStackPart1At fsp k ∗
        ((fsp + 232#64) ↦₆₄ selfA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 976#64) 1776 ∗ memRegion (fsp + 3152#64) 544 ∗
        memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3856#64) 288 ∗
        memRegion outA v1RecvSize ∗ statesRecvRoAt img.base ∗ A.pool ∗
        stackAt fsp statesRecvCalleeStackXExt ∗ statesRecvSavedCells s0 ∗
        messageAt spqrPolyApi msgA msg)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ ((statesRecvVariantSpecExt A F K img.base (.ct1Sampled st) msg).post ⟨outA, selfA, msgA⟩ s0 sf) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨ ((statesRecvVariantSpecExt A F K img.base (.ct1Sampled st) msg).onPanic ⟨outA, selfA, msgA⟩ s0 sf) ∗ R) := by
  intro dec'
  refine SepWPp.of_sepWP (mid := (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 36780#64) ?_
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (seq_clean_inImage_ax hinv
      (ct1Sampled_some_to_11528_ax hrecv_ek s_in fsp st.uc c_uc decoded (.ok uc_ek)
        (polyDecoderAt A (fsp + 2752#64) dec' ∗ polyEncoderAt A selfA st.sending_ct1 ∗
          wordsAt (selfA + 400#64) c_uc.toList ∗ memRegion (selfA + 528#64) 400 ∗
          copyScratchStackAt fsp sc ∗ epilogueStoreStackPart1At fsp k ∗
          ((fsp + 232#64) ↦₆₄ selfA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
          wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
          memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
          memRegion (fsp + 3152#64) 544 ∗ memRegion (fsp + 3824#64) 8 ∗
          memRegion (fsp + 3856#64) 288 ∗ memRegion outA v1RecvSize ∗ statesRecvRoAt img.base ∗
          statesRecvSavedCells s0 ∗ messageAt spqrPolyApi msgA msg)
        (by simpa [StatesResult.ofError] using hrek) hfsp_align hpc hrun hsp hx20 hinv) ?_)
  intro s1 hpc1 hrun1 hinv1 ⟨hsp1, hx19_1, _, hx21_1, hx22_1, hx23_1, _, hx28_1, hx29_1, htr1⟩
  refine SepWP.weaken_pre
    (ct1Sampled_some_ok_ack_pre1_ext (A := A) img.base fsp selfA outA msgA s0 st msg dec' uc_ek c_uc sc k) ?_
  apply ProofLib.SepWP.exists_left; intro c_ek
  wp_focus_pure; intro hw0_ek
  refine seq_clean_inImage_ax hinv1
    (ct1Sampled_recv_ek_ok_copy_sc s1 fsp sc c_ek _ hw0_ek hfsp_align hpc1 hrun1 hsp1) ?_
  intro s2 hpc2 hrun2 hinv2 ⟨hsp2, hx8_2, hx9_2, hx10_2, hx19_2, _, hx21_2, hx22_2, hx23_2, _, _, hx28_2, hx29_2, htr2⟩
  refine seq_clean_inImage_ax hinv2
    (ct1Sampled_ok_branch_ack s2 _ hpc2 hrun2 (hx22_2.trans (hx22_1.trans hx22))) ?_
  intro s3 hpc3 hrun3 hinv3 ⟨hsp3, _, _, _, hx19_3, _, hx21_3, hx23_3, _, _, hx28_3, hx29_3, htr3⟩
  refine SepWP.weaken_pre
    (ct1Sampled_some_ok_ack_pre3_ext img.base fsp selfA outA msgA s0 st msg dec' uc_ek c_uc c_ek sc k) ?_
  refine h678.send_ct2_and_encode
    (P_pan := (((States.ct1Sampled st).recv K msg).isPanic = true))
    hb hsendCt2 hsendCt2Enc s0 s3 fsp uc_ek outUc ct2 mac outEnc hsc henc _ R hinv3
    hfsp_align hpc3 hrun3 (hsp3.trans hsp2)
    (htr3.trans (htr2.trans (htr1.trans htr)))
    (hx21_3.trans (hx21_2.trans (hx21_1.trans hx21)))
    (hx29_3.trans (hx29_2.trans (hx29_1.trans hx29))) ?_
  intro s4 g_uc ct2Cap ct2Ptr macCap macPtr hpc4 hrun4 hsp4 hinv4 hx19_4 hx20_4 hx21_4 _ hx25_4 hx26_4 hx27_4 hx28_4 hx29_4 htr4
  apply SepWP.done hpc4 hrun4
  refine sepWPp_of_statesRecv_exit_ext s0 s4 outA selfA msgA (.ct1Sampled st) msg _ R ?_
  rw [states_recv_ct1Sampled_eq_some_ok_ack K st msg chunk decoded uc_ek outUc ct2 mac outEnc
    heq hpay hlen hsort hdec hrek hsc henc]
  refine SepWP.mono
    (ct1Sampled_some_ok_ack_from_11696_ext hb hA hdealloc s0 s4 fsp selfA outA st dec' c_uc
      outUc outEnc g_uc ct2Cap ct2Ptr macCap macPtr { sc with wb0 := c_ek.w1 } k
      (messageAt spqrPolyApi msgA msg) hfsp_align hsp0_align hfsp hpc4 hrun4 hsp4
      (hx19_4.trans (hx19_3.trans (hx19_2.trans (hx19_1.trans hx19))))
      hx20_4 hx25_4 hx26_4 hx27_4
      (hx28_4.trans (hx28_3.trans (hx28_2.trans (hx28_1.trans hx28))))
      hx29_4 htr4 hinv4) ?_
  intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
  exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩

set_option maxHeartbeats 2000000 in
/-- Complete `.ct1Sampled` arm from `+1528 -> s0.x30` (`0x55a4c -> s0.x30`) for `msg.payload = .ek chunk`
    under `AllocContractsX` + `.inImage img`. -/
theorem ct1Sampled_arm_eq_ek_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hb : img.base &&& 0xfff#64 = 0#64) (hA : AllocContractsX img A ext)
    (hdealloc : DeallocOkExt img.base A ext) (hadd_call : AddChunkOkX img A ext)
    (hdec_call : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr polyDecoderDecodedMessageName)
      ((growToCalleeExt polyDecoderDecodedMessageStack
        (polyDecoderDecodedMessageSpec A img.base)).inImage img))
    (hrecv_ek : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr unchunkedCt1SentRecvEkName)
      ((growToCalleeExt unchunkedRecvEkStack
        (unchunkedCt1SentRecvEkSpec A F K)).inImage img))
    (h678 : Ct1SampledExt678Deps img A F K ext)
    (s0 s2 : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk) (R : SepProp)
    (hsort : PolyDecoderStrictSorted st.receiving_ek)
    (heq : msg.epoch = st.uc.epoch) (hpay : msg.payload = .ek chunk)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc2 : s2.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 1528#64)
    (hrun2 : s2.status = .Running) (hsp2 : s2.sp = s0.sp - 4240#64)
    (hx1 : s2.readReg64 .x1 = selfA) (hx12 : s2.readReg64 .x12 = polyEncoderTagVal st.sending_ct1)
    (hx19 : s2.readReg64 .x19 = outA) (hx21 : s2.readReg64 .x21 = (s0.sp - 4240#64) + 3856#64)
    (hx24 : s2.readReg64 .x24 = msgA) (hx28 : s2.readReg64 .x28 = (s0.sp - 4240#64) + 3272#64)
    (hx29 : s2.readReg64 .x29 = s0.sp - 96#64)
    (htr2 : TraceCalleeSaved s2 s0) (hinv2 : ImgCallInv img s2) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s2
      (memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ct1Sampled st) ∗
        messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base ∗ A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ ((statesRecvVariantSpecExt A F K img.base (.ct1Sampled st) msg).post ⟨outA, selfA, msgA⟩ s0 sf) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨ ((statesRecvVariantSpecExt A F K img.base (.ct1Sampled st) msg).onPanic ⟨outA, selfA, msgA⟩ s0 sf) ∗ R) := by
  let b := img.base
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  have hpre :
      memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ct1Sampled st) ∗
        messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 ⊢
      ⌜st.receiving_ek.pts.length = 16⌝ ∗
      (((selfA + 520#64) ↦₆₄ st.uc.epoch) ∗ (msgA ↦₆₄ st.uc.epoch) ∗
        (((msgA + 8#64) ↦₈ 2#8) ∗
          (authenticatorAt A (selfA + 400#64) st.uc.auth ∗ vecU8 A (selfA + 448#64) st.uc.hdr ∗
            vecU8 A (selfA + 472#64) st.uc.es ∗ vecU8 A (selfA + 496#64) st.uc.ct1) ∗
          polyEncoderAt A selfA st.sending_ct1 ∗ polyDecoderAt A (selfA + 528#64) st.receiving_ek ∗
          memRegion (msgA + 9#64) 1 ∗ chunkAt (msgA + 10#64) chunk ∗ memRegion (msgA + 44#64) 4 ∗
          memRegion outA v1RecvSize ∗ statesRecvRoAt b ∗ A.pool ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
          memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)) := by
    dsimp only [chunkedStatesAt, chunkedCt1SampledAt]
    rw [unchunkedCt1SentAt_epoch_expose A selfA st.uc, messageAt_ek_eq msgA msg chunk hpay, heq]
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right (polyDecoderAt_dup_pts_len A (selfA + 528#64) st.receiving_ek))))) ?_
    exact Entails.of_eq (by ac_rfl)
  refine SepWPp.weaken_pre hpre ?_
  refine SepWPp.of_sepWP_frozen (mid := (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 11404#64)
    hinv2.1 hinv2.2 ?_
  wp_focus_pure; intro hlen
  refine SepWP.seq
    (ct1Sampled_epoch_cmp_eq s2 selfA msgA st.uc.epoch _ hpc2 hrun2 hx1 hx24) ?_
  intro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, _, hx1_3, _, _, hx12_3, hx19_3, hx20_3, hx21_3, hx24_3, hx28_3, hx29_3, htr3⟩
  have hP3' : P3 ⊢
      ((msgA + 8#64) ↦₈ 2#8) ∗
      (polyEncoderAt A selfA st.sending_ct1 ∗ unchunkedCt1SentAt A (selfA + 400#64) st.uc ∗
        polyDecoderAt A (selfA + 528#64) st.receiving_ek ∗ chunkAt (msgA + 10#64) chunk ∗
        statesRecvRoAt b ∗ A.pool ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        (memRegion outA v1RecvSize ∗ statesRecvSavedCells s0 ∗
          (msgA ↦₆₄ st.uc.epoch) ∗ memRegion (msgA + 9#64) 1 ∗ memRegion (msgA + 44#64) 4)) := by
    refine Entails.trans hP3 ?_
    rw [unchunkedCt1SentAt_epoch_expose A selfA st.uc]
    exact Entails.of_eq (by ac_rfl)
  refine SepWP.weaken_pre hP3' ?_
  refine SepWP.seq
    (ct1Sampled_msg_kind_check_ek s3 msgA _ hpc3 hrun3 hx24_3) ?_
  intro s4 P4 hpc4 hrun4 ⟨hP4, hsp4, hx1_4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx28_4, hx29_4, htr4⟩
  have hP4' : P4 ⊢
      polyEncoderAt A selfA st.sending_ct1 ∗ unchunkedCt1SentAt A (selfA + 400#64) st.uc ∗
        polyDecoderAt A (selfA + 528#64) st.receiving_ek ∗ chunkAt (msgA + 10#64) chunk ∗
        statesRecvRoAt b ∗ A.pool ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        (memRegion outA v1RecvSize ∗ statesRecvSavedCells s0 ∗
          ((msgA + 8#64) ↦₈ 2#8) ∗ (msgA ↦₆₄ st.uc.epoch) ∗
          memRegion (msgA + 9#64) 1 ∗ memRegion (msgA + 44#64) 4) :=
    Entails.trans hP4 (Entails.of_eq (by ac_rfl))
  refine SepWP.weaken_pre hP4' ?_
  apply SepWP.done hpc4 hrun4
  intro hF4 hsym4
  have hx29_fsp : s4.readReg64 .x29 = (s0.sp - 4240#64) + 4144#64 := by
    rw [hx29_4, hx29_3, hx29, sp_sub_4240_add_4144]
  refine h678.recv_ek_common_prefix
    (P_pan := (((States.ct1Sampled st).recv K msg).isPanic = true))
    hA hadd_call hdec_call hb s0 s4 (s0.sp - 4240#64) selfA outA msgA 0#64 st chunk hlen hsort _ R
    hfsp_align rfl hpc4 hrun4 (hsp4.trans (hsp3.trans hsp2)) (hx1_4.trans hx1_3)
    (hx19_4.trans (hx19_3.trans hx19)) (hx20_4.trans hx20_3) (hx21_4.trans (hx21_3.trans hx21))
    hx22_4 (hx23_4.trans (hx12_3.trans hx12)) hx24_4 (hx28_4.trans (hx28_3.trans hx28))
    hx29_fsp (htr4.trans (htr3.trans htr2)) ⟨hF4, hsym4⟩ ?_
  intro s5 c_uc sc k hpc5 hrun5 hsp5 hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 _ hx28_5 hx29_5 htr5 hinv5
  have hmsg_join :
      chunkAt (msgA + 10#64) chunk ∗ ((msgA + 8#64) ↦₈ 2#8) ∗ (msgA ↦₆₄ st.uc.epoch) ∗
        memRegion (msgA + 9#64) 1 ∗ memRegion (msgA + 44#64) 4 =
      messageAt spqrPolyApi msgA msg := by
    rw [messageAt_ek_eq msgA msg chunk hpay, heq]; ac_rfl
  cases hdec_opt : decodedMessageTotal (addChunkTotal st.receiving_ek chunk) with
  | none =>
    refine sepWPp_of_statesRecv_exit_ext s0 s5 outA selfA msgA (.ct1Sampled st) msg _ R ?_
    rw [states_recv_ct1Sampled_eq_none_no_ack K st msg chunk heq hpay hlen hsort hdec_opt]
    refine SepWP.weaken_pre (by rw [← hmsg_join]; exact Entails.of_eq (by ac_rfl))
      (SepWP.mono
        (h678.path_none_no_ack hA s0 s5 (s0.sp - 4240#64) selfA outA st
          (addChunkTotal st.receiving_ek chunk) c_uc sc k
          (statesRecvRoAt b ∗ A.pool ∗ messageAt spqrPolyApi msgA msg)
          hfsp_align hsp0_align rfl hpc5 hrun5 hsp5 hx19_5 hx22_5 hx23_5 hx29_5 htr5 hinv5) ?_)
    intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
    exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩
  | some decoded =>
    have hrek_eq := ct1Sent_recv_ek_eq_ofError K st.uc decoded
    dsimp only at hrek_eq
    split_ifs at hrek_eq with hpk
    · let uc_ek : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F) :=
        { epoch := st.uc.epoch, auth := st.uc.auth, es := st.uc.es, ek := decoded, ct1 := st.uc.ct1 }
      have hrek : st.uc.recv_ek K st.uc.epoch decoded = .ok uc_ek := hrek_eq
      refine sepWPp_of_statesRecv_exit_ext s0 s5 outA selfA msgA (.ct1Sampled st) msg _ R ?_
      rw [states_recv_ct1Sampled_eq_some_ok_no_ack K st msg chunk decoded uc_ek
        heq hpay hlen hsort hdec_opt hrek]
      refine SepWP.weaken_pre (by rw [← hmsg_join]; exact Entails.of_eq (by ac_rfl))
        (SepWP.mono
          (ct1Sampled_path_some_ok_no_ack_ext hb hA hdealloc hrecv_ek s0 s5 (s0.sp - 4240#64)
            selfA outA st (addChunkTotal st.receiving_ek chunk) c_uc decoded uc_ek sc k
            (messageAt spqrPolyApi msgA msg) hrek hfsp_align hsp0_align rfl
            hpc5 hrun5 hsp5 hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx28_5 hx29_5 htr5 hinv5) ?_)
      intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
      exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩
    · have hrek : st.uc.recv_ek K st.uc.epoch decoded = .error (.err .erroneousDataReceived) := hrek_eq
      refine sepWPp_of_statesRecv_exit_ext s0 s5 outA selfA msgA (.ct1Sampled st) msg _ R ?_
      rw [states_recv_ct1Sampled_eq_some_err K st msg chunk decoded .erroneousDataReceived
        heq (Or.inl hpay) hlen hsort hdec_opt hrek]
      refine SepWP.weaken_pre (by rw [← hmsg_join]; exact Entails.of_eq (by ac_rfl))
        (SepWP.mono
          (h678.path_some_err hdealloc hrecv_ek s0 s5 (s0.sp - 4240#64) selfA outA st
            (addChunkTotal st.receiving_ek chunk) c_uc decoded .erroneousDataReceived sc k
            (statesRecvRoAt b ∗ messageAt spqrPolyApi msgA msg)
            hrek rfl hfsp_align hsp0_align rfl hpc5 hrun5 hsp5 hx19_5 hx20_5 htr5 hinv5) ?_)
      intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
      exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩

set_option maxHeartbeats 2000000 in
/-- Complete `.ct1Sampled` arm from `+1528 -> s0.x30` (`0x55a4c -> s0.x30`) for `msg.payload = .ekCt1Ack chunk`
    under `AllocContractsX` + `.inImage img`. -/
theorem ct1Sampled_arm_eq_ekCt1Ack_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hb : img.base &&& 0xfff#64 = 0#64) (hA : AllocContractsX img A ext)
    (hdealloc : DeallocOkExt img.base A ext) (hadd_call : AddChunkOkX img A ext)
    (hdec_call : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr polyDecoderDecodedMessageName)
      ((growToCalleeExt polyDecoderDecodedMessageStack
        (polyDecoderDecodedMessageSpec A img.base)).inImage img))
    (hrecv_ek : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr unchunkedCt1SentRecvEkName)
      ((growToCalleeExt unchunkedRecvEkStack
        (unchunkedCt1SentRecvEkSpec A F K)).inImage img))
    (hsendCt2 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name)
      ((growToCalleeExt unchunkedSendCt2Stack
        (unchunkedCt1SentEkReceivedSendCt2Spec A F K img.base)).inImage img))
    (hsendCt2Enc : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr sendCt2EncoderName)
      ((growToCalleeExt sendCt2EncoderStack (sendCt2EncoderSpec A)).inImage img))
    (h678 : Ct1SampledExt678Deps img A F K ext)
    (s0 s2 : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk) (R : SepProp)
    (hsort : PolyDecoderStrictSorted st.receiving_ek)
    (h_sendCt2 : ∀ decoded (uc_ek : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F)),
      decodedMessageTotal (addChunkTotal st.receiving_ek chunk) = some decoded →
      st.uc.recv_ek K st.uc.epoch decoded = .ok uc_ek →
      ∃ outUc ct2 mac outEnc,
        uc_ek.send_ct2 K = .ok (outUc, ct2, mac) ∧
        Chunked.SendCt.send_ct2_encoder spqrPolyApi ct2 mac = .ok outEnc)
    (heq : msg.epoch = st.uc.epoch) (hpay : msg.payload = .ekCt1Ack chunk)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc2 : s2.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 1528#64)
    (hrun2 : s2.status = .Running) (hsp2 : s2.sp = s0.sp - 4240#64)
    (hx1 : s2.readReg64 .x1 = selfA) (hx12 : s2.readReg64 .x12 = polyEncoderTagVal st.sending_ct1)
    (hx19 : s2.readReg64 .x19 = outA) (hx21 : s2.readReg64 .x21 = (s0.sp - 4240#64) + 3856#64)
    (hx24 : s2.readReg64 .x24 = msgA) (hx28 : s2.readReg64 .x28 = (s0.sp - 4240#64) + 3272#64)
    (hx29 : s2.readReg64 .x29 = s0.sp - 96#64)
    (htr2 : TraceCalleeSaved s2 s0) (hinv2 : ImgCallInv img s2) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s2
      (memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ct1Sampled st) ∗
        messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base ∗ A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ ((statesRecvVariantSpecExt A F K img.base (.ct1Sampled st) msg).post ⟨outA, selfA, msgA⟩ s0 sf) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨ ((statesRecvVariantSpecExt A F K img.base (.ct1Sampled st) msg).onPanic ⟨outA, selfA, msgA⟩ s0 sf) ∗ R) := by
  let b := img.base
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  have hpre :
      memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ct1Sampled st) ∗
        messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 ⊢
      ⌜st.receiving_ek.pts.length = 16⌝ ∗
      (((selfA + 520#64) ↦₆₄ st.uc.epoch) ∗ (msgA ↦₆₄ st.uc.epoch) ∗
        (((msgA + 8#64) ↦₈ 3#8) ∗
          (authenticatorAt A (selfA + 400#64) st.uc.auth ∗ vecU8 A (selfA + 448#64) st.uc.hdr ∗
            vecU8 A (selfA + 472#64) st.uc.es ∗ vecU8 A (selfA + 496#64) st.uc.ct1) ∗
          polyEncoderAt A selfA st.sending_ct1 ∗ polyDecoderAt A (selfA + 528#64) st.receiving_ek ∗
          memRegion (msgA + 9#64) 1 ∗ chunkAt (msgA + 10#64) chunk ∗ memRegion (msgA + 44#64) 4 ∗
          memRegion outA v1RecvSize ∗ statesRecvRoAt b ∗ A.pool ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
          memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)) := by
    dsimp only [chunkedStatesAt, chunkedCt1SampledAt]
    rw [unchunkedCt1SentAt_epoch_expose A selfA st.uc, messageAt_ekCt1Ack_eq msgA msg chunk hpay, heq]
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right (polyDecoderAt_dup_pts_len A (selfA + 528#64) st.receiving_ek))))) ?_
    exact Entails.of_eq (by ac_rfl)
  refine SepWPp.weaken_pre hpre ?_
  refine SepWPp.of_sepWP_frozen (mid := (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 11404#64)
    hinv2.1 hinv2.2 ?_
  wp_focus_pure; intro hlen
  refine SepWP.seq
    (ct1Sampled_epoch_cmp_eq s2 selfA msgA st.uc.epoch _ hpc2 hrun2 hx1 hx24) ?_
  intro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, _, hx1_3, _, _, hx12_3, hx19_3, hx20_3, hx21_3, hx24_3, hx28_3, hx29_3, htr3⟩
  have hP3' : P3 ⊢
      ((msgA + 8#64) ↦₈ 3#8) ∗
      (polyEncoderAt A selfA st.sending_ct1 ∗ unchunkedCt1SentAt A (selfA + 400#64) st.uc ∗
        polyDecoderAt A (selfA + 528#64) st.receiving_ek ∗ chunkAt (msgA + 10#64) chunk ∗
        statesRecvRoAt b ∗ A.pool ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        (memRegion outA v1RecvSize ∗ statesRecvSavedCells s0 ∗
          (msgA ↦₆₄ st.uc.epoch) ∗ memRegion (msgA + 9#64) 1 ∗ memRegion (msgA + 44#64) 4)) := by
    refine Entails.trans hP3 ?_
    rw [unchunkedCt1SentAt_epoch_expose A selfA st.uc]
    exact Entails.of_eq (by ac_rfl)
  refine SepWP.weaken_pre hP3' ?_
  refine SepWP.seq
    (ct1Sampled_msg_kind_check_ekCt1Ack s3 msgA _ hpc3 hrun3 hx24_3) ?_
  intro s4 P4 hpc4 hrun4 ⟨hP4, hsp4, hx1_4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx28_4, hx29_4, htr4⟩
  have hP4' : P4 ⊢
      polyEncoderAt A selfA st.sending_ct1 ∗ unchunkedCt1SentAt A (selfA + 400#64) st.uc ∗
        polyDecoderAt A (selfA + 528#64) st.receiving_ek ∗ chunkAt (msgA + 10#64) chunk ∗
        statesRecvRoAt b ∗ A.pool ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        (memRegion outA v1RecvSize ∗ statesRecvSavedCells s0 ∗
          ((msgA + 8#64) ↦₈ 3#8) ∗ (msgA ↦₆₄ st.uc.epoch) ∗
          memRegion (msgA + 9#64) 1 ∗ memRegion (msgA + 44#64) 4) :=
    Entails.trans hP4 (Entails.of_eq (by ac_rfl))
  refine SepWP.weaken_pre hP4' ?_
  apply SepWP.done hpc4 hrun4
  intro hF4 hsym4
  have hx29_fsp : s4.readReg64 .x29 = (s0.sp - 4240#64) + 4144#64 := by
    rw [hx29_4, hx29_3, hx29, sp_sub_4240_add_4144]
  refine h678.recv_ek_common_prefix
    (P_pan := (((States.ct1Sampled st).recv K msg).isPanic = true))
    hA hadd_call hdec_call hb s0 s4 (s0.sp - 4240#64) selfA outA msgA 1#64 st chunk hlen hsort _ R
    hfsp_align rfl hpc4 hrun4 (hsp4.trans (hsp3.trans hsp2)) (hx1_4.trans hx1_3)
    (hx19_4.trans (hx19_3.trans hx19)) (hx20_4.trans hx20_3) (hx21_4.trans (hx21_3.trans hx21))
    hx22_4 (hx23_4.trans (hx12_3.trans hx12)) hx24_4 (hx28_4.trans (hx28_3.trans hx28))
    hx29_fsp (htr4.trans (htr3.trans htr2)) ⟨hF4, hsym4⟩ ?_
  intro s5 c_uc sc k hpc5 hrun5 hsp5 hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 _ hx28_5 hx29_5 htr5 hinv5
  have hmsg_join :
      chunkAt (msgA + 10#64) chunk ∗ ((msgA + 8#64) ↦₈ 3#8) ∗ (msgA ↦₆₄ st.uc.epoch) ∗
        memRegion (msgA + 9#64) 1 ∗ memRegion (msgA + 44#64) 4 =
      messageAt spqrPolyApi msgA msg := by
    rw [messageAt_ekCt1Ack_eq msgA msg chunk hpay, heq]; ac_rfl
  cases hdec_opt : decodedMessageTotal (addChunkTotal st.receiving_ek chunk) with
  | none =>
    refine sepWPp_of_statesRecv_exit_ext s0 s5 outA selfA msgA (.ct1Sampled st) msg _ R ?_
    rw [states_recv_ct1Sampled_eq_none_ack K st msg chunk heq hpay hlen hsort hdec_opt]
    refine SepWP.weaken_pre (by rw [← hmsg_join]; exact Entails.of_eq (by ac_rfl))
      (SepWP.mono
        (h678.path_none_ack hb hA hdealloc s0 s5 (s0.sp - 4240#64) selfA outA st
          (addChunkTotal st.receiving_ek chunk) c_uc sc k
          (messageAt spqrPolyApi msgA msg)
          hfsp_align hsp0_align rfl hpc5 hrun5 hsp5 hx19_5 hx22_5 hx28_5 htr5 hinv5) ?_)
    intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
    exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩
  | some decoded =>
    have hrek_eq := ct1Sent_recv_ek_eq_ofError K st.uc decoded
    dsimp only at hrek_eq
    split_ifs at hrek_eq with hpk
    · let uc_ek : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F) :=
        { epoch := st.uc.epoch, auth := st.uc.auth, es := st.uc.es, ek := decoded, ct1 := st.uc.ct1 }
      have hrek : st.uc.recv_ek K st.uc.epoch decoded = .ok uc_ek := hrek_eq
      obtain ⟨outUc, ct2, mac, outEnc, hsc, henc⟩ := h_sendCt2 decoded uc_ek hdec_opt hrek
      refine SepWPp.weaken_pre (by rw [← hmsg_join]; exact Entails.of_eq (by ac_rfl))
        (ct1Sampled_path_some_ok_ack_ext hb hA hdealloc hrecv_ek hsendCt2 hsendCt2Enc h678
          s0 s5 (s0.sp - 4240#64) selfA outA msgA st msg chunk decoded uc_ek outUc ct2 mac outEnc
          c_uc sc k R heq hpay hlen hsort hdec_opt hrek hsc henc hfsp_align hsp0_align rfl
          hpc5 hrun5 hsp5 hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx28_5 hx29_5 htr5 hinv5)
    · have hrek : st.uc.recv_ek K st.uc.epoch decoded = .error (.err .erroneousDataReceived) := hrek_eq
      refine sepWPp_of_statesRecv_exit_ext s0 s5 outA selfA msgA (.ct1Sampled st) msg _ R ?_
      rw [states_recv_ct1Sampled_eq_some_err K st msg chunk decoded .erroneousDataReceived
        heq (Or.inr hpay) hlen hsort hdec_opt hrek]
      refine SepWP.weaken_pre (by rw [← hmsg_join]; exact Entails.of_eq (by ac_rfl))
        (SepWP.mono
          (h678.path_some_err hdealloc hrecv_ek s0 s5 (s0.sp - 4240#64) selfA outA st
            (addChunkTotal st.receiving_ek chunk) c_uc decoded .erroneousDataReceived sc k
            (statesRecvRoAt b ∗ messageAt spqrPolyApi msgA msg)
            hrek rfl hfsp_align hsp0_align rfl hpc5 hrun5 hsp5 hx19_5 hx20_5 htr5 hinv5) ?_)
      intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
      exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩

set_option maxHeartbeats 2000000 in
/-- Complete `.ct1Sampled` arm from `+1528 -> s0.x30` (`0x55a4c -> s0.x30`) for all `msg`
    under `AllocContractsX` + `.inImage img`. -/
theorem states_recv_arm_ct1Sampled_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hb : img.base &&& 0xfff#64 = 0#64) (hA : AllocContractsX img A ext)
    (hdealloc : DeallocOkExt img.base A ext) (hadd_call : AddChunkOkX img A ext)
    (hdec_call : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr polyDecoderDecodedMessageName)
      ((growToCalleeExt polyDecoderDecodedMessageStack
        (polyDecoderDecodedMessageSpec A img.base)).inImage img))
    (hrecv_ek : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr unchunkedCt1SentRecvEkName)
      ((growToCalleeExt unchunkedRecvEkStack
        (unchunkedCt1SentRecvEkSpec A F K)).inImage img))
    (hsendCt2 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name)
      ((growToCalleeExt unchunkedSendCt2Stack
        (unchunkedCt1SentEkReceivedSendCt2Spec A F K img.base)).inImage img))
    (hsendCt2Enc : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr sendCt2EncoderName)
      ((growToCalleeExt sendCt2EncoderStack (sendCt2EncoderSpec A)).inImage img))
    (h678 : Ct1SampledExt678Deps img A F K ext)
    (s0 s2 : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (R : SepProp)
    (hsort : PolyDecoderStrictSorted st.receiving_ek)
    (h_sendCt2 : ∀ chunk decoded (uc_ek : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F)),
      msg.epoch = st.uc.epoch → msg.payload = .ekCt1Ack chunk →
      decodedMessageTotal (addChunkTotal st.receiving_ek chunk) = some decoded →
      st.uc.recv_ek K st.uc.epoch decoded = .ok uc_ek →
      ∃ outUc ct2 mac outEnc,
        uc_ek.send_ct2 K = .ok (outUc, ct2, mac) ∧
        Chunked.SendCt.send_ct2_encoder spqrPolyApi ct2 mac = .ok outEnc)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc2 : s2.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 1528#64)
    (hrun2 : s2.status = .Running) (hsp2 : s2.sp = s0.sp - 4240#64)
    (hx1 : s2.readReg64 .x1 = selfA) (hx12 : s2.readReg64 .x12 = polyEncoderTagVal st.sending_ct1)
    (hx19 : s2.readReg64 .x19 = outA) (hx21 : s2.readReg64 .x21 = (s0.sp - 4240#64) + 3856#64)
    (hx24 : s2.readReg64 .x24 = msgA) (hx28 : s2.readReg64 .x28 = (s0.sp - 4240#64) + 3272#64)
    (hx29 : s2.readReg64 .x29 = s0.sp - 96#64)
    (htr2 : TraceCalleeSaved s2 s0) (hinv2 : ImgCallInv img s2) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s2
      (memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ct1Sampled st) ∗
        messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base ∗ A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ ((statesRecvVariantSpecExt A F K img.base (.ct1Sampled st) msg).post ⟨outA, selfA, msgA⟩ s0 sf) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨ ((statesRecvVariantSpecExt A F K img.base (.ct1Sampled st) msg).onPanic ⟨outA, selfA, msgA⟩ s0 sf) ∗ R) := by
  let b := img.base
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  by_cases hgt : msg.epoch.toNat > st.uc.epoch.toNat
  · refine sepWPp_of_statesRecv_exit_ext s0 s2 outA selfA msgA (.ct1Sampled st) msg _ R ?_
    rw [states_recv_ct1Sampled_eq_gt K st msg hgt]
    have hpre :
        memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ct1Sampled st) ∗
          messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
          memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 ⊢
        ((selfA + 520#64) ↦₆₄ st.uc.epoch) ∗ (msgA ↦₆₄ msg.epoch) ∗
        (memRegion outA v1RecvSize ∗ polyEncoderAt A selfA st.sending_ct1 ∗
          (authenticatorAt A (selfA + 400#64) st.uc.auth ∗ vecU8 A (selfA + 448#64) st.uc.hdr ∗
            vecU8 A (selfA + 472#64) st.uc.es ∗ vecU8 A (selfA + 496#64) st.uc.ct1) ∗
          polyDecoderAt A (selfA + 528#64) st.receiving_ek ∗
          messagePayloadAt spqrPolyApi msgA msg.payload ∗ statesRecvRoAt b ∗ A.pool ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
          memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0) := by
      dsimp only [chunkedStatesAt, chunkedCt1SampledAt, messageAt]
      rw [unchunkedCt1SentAt_epoch_expose A selfA st.uc]; exact Entails.of_eq (by ac_rfl)
    refine SepWP.weaken_pre hpre ?_
    refine SepWP.seq
      (ct1Sampled_epoch_cmp_gt s2 selfA msgA st.uc.epoch msg.epoch _ hgt hpc2 hrun2 hx1 hx24) ?_
    intro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, hx1_3, hx19_3, hx20_3, _, _, _, _, htr3⟩
    have hP3' : P3 ⊢
        memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ct1Sampled st) ∗ A.pool ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗ memRegion (s0.sp - 4240#64) 4144 ∗
          statesRecvSavedCells s0 ∗ (messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b) := by
      refine Entails.trans hP3 ?_
      dsimp only [chunkedStatesAt, chunkedCt1SampledAt, messageAt]
      rw [unchunkedCt1SentAt_epoch_expose A selfA st.uc]; exact Entails.of_eq (by ac_rfl)
    refine SepWP.weaken_pre hP3' ?_
    refine SepWP.mono
      (ct1Sampled_drop_epochOutOfRange_ext hdealloc s0 s3 outA selfA msg.epoch st
        (messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b)
        hsp0_align hpc3 hrun3 (hsp3.trans hsp2) hx1_3 (hx19_3.trans hx19) hx20_3 (htr3.trans htr2)) ?_
    intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
    exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩
  · by_cases hlt : msg.epoch.toNat < st.uc.epoch.toNat
    · refine sepWPp_of_statesRecv_exit_ext s0 s2 outA selfA msgA (.ct1Sampled st) msg _ R ?_
      rw [states_recv_ct1Sampled_eq_lt K st msg hlt]
      have hpre :
          memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ct1Sampled st) ∗
            messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool ∗
            stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
            memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 ⊢
          ((selfA + 520#64) ↦₆₄ st.uc.epoch) ∗ (msgA ↦₆₄ msg.epoch) ∗
          (memRegion outA v1RecvSize ∗ polyEncoderAt A selfA st.sending_ct1 ∗
            (authenticatorAt A (selfA + 400#64) st.uc.auth ∗ vecU8 A (selfA + 448#64) st.uc.hdr ∗
              vecU8 A (selfA + 472#64) st.uc.es ∗ vecU8 A (selfA + 496#64) st.uc.ct1) ∗
            polyDecoderAt A (selfA + 528#64) st.receiving_ek ∗
            messagePayloadAt spqrPolyApi msgA msg.payload ∗ statesRecvRoAt b ∗ A.pool ∗
            stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
            memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0) := by
        dsimp only [chunkedStatesAt, chunkedCt1SampledAt, messageAt]
        rw [unchunkedCt1SentAt_epoch_expose A selfA st.uc]; exact Entails.of_eq (by ac_rfl)
      refine SepWP.weaken_pre hpre ?_
      refine seq_clean_inImage_ax hinv2
        (ct1Sampled_epoch_cmp_lt s2 selfA msgA st.uc.epoch msg.epoch _ hlt hpc2 hrun2 hx1 hx24) ?_
      intro s3 hpc3 hrun3 hinv3 ⟨hsp3, _, hx1_3, _, _, hx12_3, hx19_3, _, _, _, _, hx29_3, htr3⟩
      refine SepWP.weaken_pre
        (by
          rw [← chunkedCt1SampledAt_eq_tag_body A selfA st]
          dsimp only [chunkedCt1SampledAt, messageAt]
          rw [unchunkedCt1SentAt_epoch_expose A selfA st.uc]
          exact Entails.of_eq (by ac_rfl))
        (SepWP.mono
          (ct1Sampled_path_lt_extStack hA s0 s3 (s0.sp - 4240#64) selfA outA st
            (messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool)
            hfsp_align hsp0_align rfl hpc3 hrun3 (hsp3.trans hsp2)
            hx1_3 (hx12_3.trans hx12) (hx19_3.trans hx19) (hx29_3.trans hx29)
            (htr3.trans htr2) hinv3) ?_)
      intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
      exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩
    · have heq : msg.epoch = st.uc.epoch := by apply BitVec.eq_of_toNat_eq; omega
      cases hpay : msg.payload with
      | ek chunk =>
        exact ct1Sampled_arm_eq_ek_ext hb hA hdealloc hadd_call hdec_call hrecv_ek h678
          s0 s2 outA selfA msgA st msg chunk R hsort heq hpay
          hsp0_align hpc2 hrun2 hsp2 hx1 hx12 hx19 hx21 hx24 hx28 hx29 htr2 hinv2
      | ekCt1Ack chunk =>
        exact ct1Sampled_arm_eq_ekCt1Ack_ext hb hA hdealloc hadd_call hdec_call hrecv_ek hsendCt2 hsendCt2Enc h678
          s0 s2 outA selfA msgA st msg chunk R hsort
          (fun decoded uc_ek hdec hrek => h_sendCt2 chunk decoded uc_ek heq hpay hdec hrek)
          heq hpay hsp0_align hpc2 hrun2 hsp2 hx1 hx12 hx19 hx21 hx24 hx28 hx29 htr2 hinv2
      | none | hdr _ | ct1Ack _ | ct1 _ | ct2 _ =>
        have hnot_ek : ∀ c, msg.payload ≠ .ek c := by intro c hc; rw [hpay] at hc; cases hc
        have hnot_ack : ∀ c, msg.payload ≠ .ekCt1Ack c := by intro c hc; rw [hpay] at hc; cases hc
        obtain ⟨msg_tag, Rest_msg, hne2, hne3, hmsg_pay⟩ :=
          messagePayloadAt_other_expose msgA msg.payload hnot_ek hnot_ack
        refine sepWPp_of_statesRecv_exit_ext s0 s2 outA selfA msgA (.ct1Sampled st) msg _ R ?_
        rw [states_recv_ct1Sampled_eq_other K st msg heq hnot_ek hnot_ack]
        have hpre :
            memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ct1Sampled st) ∗
              messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool ∗
              stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
              memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 ⊢
            ((selfA + 520#64) ↦₆₄ st.uc.epoch) ∗ (msgA ↦₆₄ st.uc.epoch) ∗
            (((msgA + 8#64) ↦₈ msg_tag) ∗ Rest_msg ∗ memRegion outA v1RecvSize ∗
              polyEncoderAt A selfA st.sending_ct1 ∗
              (authenticatorAt A (selfA + 400#64) st.uc.auth ∗ vecU8 A (selfA + 448#64) st.uc.hdr ∗
                vecU8 A (selfA + 472#64) st.uc.es ∗ vecU8 A (selfA + 496#64) st.uc.ct1) ∗
              polyDecoderAt A (selfA + 528#64) st.receiving_ek ∗ statesRecvRoAt b ∗ A.pool ∗
              stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
              memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0) := by
          dsimp only [chunkedStatesAt, chunkedCt1SampledAt, messageAt]
          rw [unchunkedCt1SentAt_epoch_expose A selfA st.uc, hmsg_pay, heq]
          exact Entails.of_eq (by ac_rfl)
        refine SepWP.weaken_pre hpre ?_
        refine seq_clean_inImage_ax hinv2
          (ct1Sampled_epoch_cmp_eq s2 selfA msgA st.uc.epoch _ hpc2 hrun2 hx1 hx24) ?_
        intro s3 hpc3 hrun3 hinv3 ⟨hsp3, _, hx1_3, _, _, hx12_3, hx19_3, _, _, hx24_3, _, hx29_3, htr3⟩
        refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
          (seq_clean_inImage_ax hinv3
            (ct1Sampled_msg_kind_check_other s3 msgA msg_tag
              (((selfA + 520#64) ↦₆₄ st.uc.epoch) ∗ (msgA ↦₆₄ st.uc.epoch) ∗ Rest_msg ∗
                memRegion outA v1RecvSize ∗ polyEncoderAt A selfA st.sending_ct1 ∗
                (authenticatorAt A (selfA + 400#64) st.uc.auth ∗ vecU8 A (selfA + 448#64) st.uc.hdr ∗
                  vecU8 A (selfA + 472#64) st.uc.es ∗ vecU8 A (selfA + 496#64) st.uc.ct1) ∗
                polyDecoderAt A (selfA + 528#64) st.receiving_ek ∗ statesRecvRoAt b ∗ A.pool ∗
                stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
                memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)
              hne2 hne3 hpc3 hrun3 hx24_3) ?_)
        intro s4 hpc4 hrun4 hinv4 ⟨hsp4, hx1_4, hx12_4, hx19_4, hx29_4, htr4⟩
        refine SepWP.weaken_pre
          (by
            rw [← chunkedCt1SampledAt_eq_tag_body A selfA st]
            dsimp only [chunkedCt1SampledAt, messageAt]
            rw [unchunkedCt1SentAt_epoch_expose A selfA st.uc, hmsg_pay, heq]
            exact Entails.of_eq (by ac_rfl))
          (SepWP.mono
            (ct1Sampled_path_other_from_12144_extStack hA s0 s4 (s0.sp - 4240#64) selfA outA st
              (messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool)
              hfsp_align hsp0_align rfl hpc4 hrun4 (hsp4.trans (hsp3.trans hsp2))
              (hx1_4.trans hx1_3) (hx12_4.trans (hx12_3.trans hx12))
              (hx19_4.trans (hx19_3.trans hx19)) (hx29_4.trans (hx29_3.trans hx29))
              (htr4.trans (htr3.trans htr2)) hinv4) ?_)
        intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
        exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩

/-- Per-variant `.inImage img` specification proof for `States.ct1Sampled st` (`tag = 0#64 ∨ tag = 1#64`)
    at `statesRecvStackXExt` (`40176` B) under `AllocContractsX` + `DeallocOkExt`. -/
theorem states_recv_ct1Sampled_ok_x_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) (hdealloc : DeallocOkExt img.base A ext)
    (hadd_call : AddChunkOkX img A ext)
    (hdec_call : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr polyDecoderDecodedMessageName)
      ((growToCalleeExt polyDecoderDecodedMessageStack
        (polyDecoderDecodedMessageSpec A img.base)).inImage img))
    (hrecv_ek : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr unchunkedCt1SentRecvEkName)
      ((growToCalleeExt unchunkedRecvEkStack
        (unchunkedCt1SentRecvEkSpec A F K)).inImage img))
    (hsendCt2 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name)
      ((growToCalleeExt unchunkedSendCt2Stack
        (unchunkedCt1SentEkReceivedSendCt2Spec A F K img.base)).inImage img))
    (hsendCt2Enc : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr sendCt2EncoderName)
      ((growToCalleeExt sendCt2EncoderStack (sendCt2EncoderSpec A)).inImage img))
    (h678 : Ct1SampledExt678Deps img A F K ext)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName)
      ((statesRecvVariantSpecExt A F K img.base (.ct1Sampled st) msg).inImage img) := by
  let b := img.base
  apply subroutine_ok_of_sepWPp
  intro ⟨outA, selfA, msgA⟩ R s0 hpc0 hrun0 hpre hsp0_align
  simp only [Spec.inImage, statesRecvVariantSpecExt, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF0, hsym0⟩, ⟨hb, hx0, hx1, hx2, hsort, hes, hct1, hmac⟩, hmem⟩
  have hinv0 : ImgCallInv img s0 := ⟨hF0, hsym0⟩
  refine ⟨stackAt s0.sp statesRecvStackXExt ∗ (memRegion outA v1RecvSize ∗
      chunkedStatesAt A selfA (.ct1Sampled st) ∗
      messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool),
    R, Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem, ?_⟩
  have hpro := ct1Sampled_prologue_ext (b := b) (ext := ext) s0
    (memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ct1Sampled st) ∗
     messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool) hsp0_align hpc0 hrun0
  refine sepWPp_seq_clean_inImage_ax hinv0 hpro ?_
  intro s1 hpc1 hrun1 hinv1 ⟨hsp1, hx0_1, hx1_1, hx2_1, _, hx29_1, htr1⟩
  rw [hx0] at hx0_1; rw [hx1] at hx1_1; rw [hx2] at hx2_1
  have hP1' :
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗ memRegion (s0.sp - 4240#64) 4144 ∗
      statesRecvSavedCells s0 ∗
      (memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ct1Sampled st) ∗
       messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool) ⊢
      (selfA ↦₆₄ polyEncoderTagVal st.sending_ct1) ∗ statesRecvRoAt b ∗
      (chunkedCt1SampledBodyAt A (selfA + 8#64) st ∗
        memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗ memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0) := by
    dsimp only [chunkedStatesAt]
    rw [chunkedCt1SampledAt_eq_tag_body A selfA st]; exact Entails.of_eq (by ac_rfl)
  refine SepWPp.weaken_pre hP1' ?_
  have hdisp := ct1Sampled_dispatch (b := b) (ext := ext) hb s1 (s0.sp - 4240#64) selfA
    (polyEncoderTagVal st.sending_ct1)
    (chunkedCt1SampledBodyAt A (selfA + 8#64) st ∗
      memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ A.pool ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗ memRegion (s0.sp - 4240#64) 4144 ∗
      statesRecvSavedCells s0)
    (polyEncoderTagVal_zero_or_one st.sending_ct1) hpc1 hrun1 hsp1 hx1_1
  refine sepWPp_seq_clean_inImage_ax hinv1 hdisp ?_
  intro s2 hpc2 hrun2 hinv2 ⟨hsp2, _, hx1_2, _, _, _, hx12_2, hx19_2, hx21_2, hx24_2, hx28_2, hx29_2, htr2⟩
  rw [hx0_1] at hx19_2; rw [hx2_1] at hx24_2; rw [hx29_1] at hx29_2
  have hP2' :
      (selfA ↦₆₄ polyEncoderTagVal st.sending_ct1) ∗ statesRecvRoAt b ∗
      (chunkedCt1SampledBodyAt A (selfA + 8#64) st ∗
        memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗ memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0) ⊢
      memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ct1Sampled st) ∗
      messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
      memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 := by
    dsimp only [chunkedStatesAt]
    rw [chunkedCt1SampledAt_eq_tag_body A selfA st]; exact Entails.of_eq (by ac_rfl)
  refine SepWPp.weaken_pre hP2' ?_
  exact states_recv_arm_ct1Sampled_ext hb hA hdealloc hadd_call hdec_call hrecv_ek hsendCt2 hsendCt2Enc h678
    s0 s2 outA selfA msgA st msg R hsort
    (fun _ decoded uc_ek _ _ _ hrek =>
      ct1Sampled_send_ct2_ok_of_recv_ek_ok K st decoded uc_ek hes hct1 hmac hrek)
    hsp0_align hpc2 hrun2 hsp2
    hx1_2 hx12_2 hx19_2 hx21_2 hx24_2 hx28_2 hx29_2 (htr2.trans htr1) hinv2

theorem states_recv_ct1Sampled_ok_x_ax
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) (hdealloc : DeallocOkExt img.base A ext)
    (hC : StatesRecvContractsAx img A F K ext)
    (h678 : Ct1SampledExt678Deps img A F K ext)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName)
      ((statesRecvVariantSpecExt A F K img.base (.ct1Sampled st) msg).inImage img) :=
  states_recv_ct1Sampled_ok_x_ext hA hdealloc hC.polyAddChunk_ok hC.polyDecodedMessage_ok
    hC.unchunkedCt1SentRecvEk_ok hC.unchunkedCt1SentEkReceivedSendCt2_ok hC.sendCt2Encoder_ok
    h678 st msg

end CryptoVerification.SpqrV1.States.Recv
