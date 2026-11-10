/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Defs
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart2
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart3
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart6
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart7
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart8
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart9
import LibsignalBinary.Proofs.SpqrV1.States.Recv.Dispatch
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` — `.ct1Sampled` Arm, Part 10 (Top-Level Arm)

**Checked by Lean.** Composes all paths of the `.ct1Sampled` arm (`0x55a4c`, `entry + 1528`) into
`states_recv_ct1Sampled_ok_ext`.
-/

@[expose] public section

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

set_option maxRecDepth 400000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit BitVec.toNat_zero
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_48 sp_sub_4240_add_4096 sp_sub_144_add_48
  sp_sub_4240_add_4144

theorem states_recv_ct1Sampled_eq_gt {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (hgt : msg.epoch.toNat > st.uc.epoch.toNat) :
    (States.ct1Sampled st).recv K msg = .error (.err (.epochOutOfRange msg.epoch)) := by
  have hlt : st.uc.epoch < msg.epoch := BitVec.lt_def.mpr hgt
  simp only [States.recv, Chunked.SendCt.Ct1Sampled.epoch, Unchunked.SendCt.Ct1Sent.epoch,
    gt_iff_lt, hlt, ↓reduceIte]

theorem states_recv_ct1Sampled_eq_lt {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (hlt : msg.epoch.toNat < st.uc.epoch.toNat) :
    (States.ct1Sampled st).recv K msg = .ok { key := none, state := .ct1Sampled st } := by
  have hlt' : msg.epoch < st.uc.epoch := BitVec.lt_def.mpr hlt
  have hnot_gt : ¬ (st.uc.epoch < msg.epoch) := by
    rw [BitVec.lt_def]; omega
  simp only [States.recv, Chunked.SendCt.Ct1Sampled.epoch, Unchunked.SendCt.Ct1Sent.epoch,
    gt_iff_lt, hnot_gt, hlt', Bool.false_eq_true, ↓reduceIte]

theorem messagePayloadAt_other_expose (msgA : BitVec 64) (p : MessagePayload spqrPolyApi)
    (hnot_ek : ∀ c, p ≠ .ek c) (hnot_ack : ∀ c, p ≠ .ekCt1Ack c) :
    ∃ (tag : BitVec 8) (Rest_msg : SepProp),
      (BitVec.zeroExtend 32 tag == 2#32) = false ∧
      (BitVec.zeroExtend 32 tag != 3#32) = true ∧
      messagePayloadAt spqrPolyApi msgA p = (((msgA + 8#64) ↦₈ tag) ∗ Rest_msg) := by
  cases p with
  | none =>
    exact ⟨0#8, memRegion (msgA + 9#64) 39, rfl, rfl, rfl⟩
  | hdr c =>
    exact ⟨1#8, memRegion (msgA + 9#64) 1 ∗ chunkAt (msgA + 10#64) c ∗ memRegion (msgA + 44#64) 4,
      rfl, rfl, rfl⟩
  | ek c => exact False.elim (hnot_ek c rfl)
  | ekCt1Ack c => exact False.elim (hnot_ack c rfl)
  | ct1Ack b =>
    exact ⟨4#8, ((msgA + 9#64) ↦₈ (if b then 1#8 else 0#8)) ∗ memRegion (msgA + 10#64) 38,
      rfl, rfl, rfl⟩
  | ct1 c =>
    exact ⟨5#8, memRegion (msgA + 9#64) 1 ∗ chunkAt (msgA + 10#64) c ∗ memRegion (msgA + 44#64) 4,
      rfl, rfl, rfl⟩
  | ct2 c =>
    exact ⟨6#8, memRegion (msgA + 9#64) 1 ∗ chunkAt (msgA + 10#64) c ∗ memRegion (msgA + 44#64) 4,
      rfl, rfl, rfl⟩

theorem messageAt_ek_eq (msgA : BitVec 64) (msg : Message spqrPolyApi) (chunk : Chunk)
    (hpay : msg.payload = .ek chunk) :
    messageAt spqrPolyApi msgA msg =
      (msgA ↦₆₄ msg.epoch) ∗
      ((msgA + 8#64) ↦₈ 2#8) ∗
      memRegion (msgA + 9#64) 1 ∗
      chunkAt (msgA + 10#64) chunk ∗
      memRegion (msgA + 44#64) 4 := by
  dsimp only [messageAt, messagePayloadAt]
  rw [hpay]

theorem messageAt_ekCt1Ack_eq (msgA : BitVec 64) (msg : Message spqrPolyApi) (chunk : Chunk)
    (hpay : msg.payload = .ekCt1Ack chunk) :
    messageAt spqrPolyApi msgA msg =
      (msgA ↦₆₄ msg.epoch) ∗
      ((msgA + 8#64) ↦₈ 3#8) ∗
      memRegion (msgA + 9#64) 1 ∗
      chunkAt (msgA + 10#64) chunk ∗
      memRegion (msgA + 44#64) 4 := by
  dsimp only [messageAt, messagePayloadAt]
  rw [hpay]

set_option maxHeartbeats 800000 in
theorem ct1Sampled_some_ok_ack_pre0 {A : RustAlloc} {F : ShaCompress}
    (b fsp selfA outA msgA : BitVec 64) (s0 : State)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (dec' : PolyDecoder) (decoded : Bytes)
    (c_uc : Words16) (sc : CopyScratchStack) (k : EpilogueStoreStack) :
    optVecU8At A (fsp + 3832#64) (some decoded) ∗ polyDecoderAt A (fsp + 2752#64) dec' ∗
      polyEncoderAt A selfA st.sending_ct1 ∗ wordsAt (selfA + 400#64) c_uc.toList ∗
      wordsAt (fsp + 3696#64) c_uc.toList ∗
      relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
      memRegion (selfA + 528#64) 400 ∗ copyScratchStackAt fsp sc ∗ epilogueStoreStackPart1At fsp k ∗
      ((fsp + 232#64) ↦₆₄ selfA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
      wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
      memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
      memRegion (fsp + 976#64) 1776 ∗ memRegion (fsp + 3152#64) 544 ∗
      memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3856#64) 288 ∗
      memRegion outA v1RecvSize ∗ statesRecvRoAt b ∗ A.pool ∗
      stackAt fsp statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗
      messageAt spqrPolyApi msgA msg ⊢
    optVecU8At A (fsp + 3832#64) (some decoded) ∗ wordsAt (fsp + 3696#64) c_uc.toList ∗
      relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
      memRegion (fsp + 976#64) 1776 ∗ A.pool ∗ stackAt fsp statesRecvCalleeStackX ∗
      (polyDecoderAt A (fsp + 2752#64) dec' ∗ polyEncoderAt A selfA st.sending_ct1 ∗
        wordsAt (selfA + 400#64) c_uc.toList ∗ memRegion (selfA + 528#64) 400 ∗
        copyScratchStackAt fsp sc ∗ epilogueStoreStackPart1At fsp k ∗
        ((fsp + 232#64) ↦₆₄ selfA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 3152#64) 544 ∗ memRegion (fsp + 3824#64) 8 ∗
        memRegion (fsp + 3856#64) 288 ∗ memRegion outA v1RecvSize ∗ statesRecvRoAt b ∗
        statesRecvSavedCells s0 ∗ messageAt spqrPolyApi msgA msg) :=
  Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 800000 in
theorem ct1Sampled_some_ok_ack_pre1 {A : RustAlloc} {F : ShaCompress}
    (b fsp selfA outA msgA : BitVec 64) (s0 : State)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (dec' : PolyDecoder)
    (uc_ek : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F))
    (c_uc : Words16) (sc : CopyScratchStack) (k : EpilogueStoreStack) :
    unchunkedCt1SentRecvEkResAt A (fsp + 1856#64) (.ok uc_ek) ∗
      memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1984#64) 768 ∗
      memRegion (fsp + 3696#64) 128 ∗ memRegion (fsp + 3832#64) 24 ∗
      A.pool ∗ stackAt fsp statesRecvCalleeStackX ∗
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
        A.pool ∗ stackAt fsp statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗
        messageAt spqrPolyApi msgA msg) := by
  dsimp only [unchunkedCt1SentRecvEkResAt]
  rw [ProofLib.memRegion_split' (b := fsp + 3856#64) (n := 128) (k := 160) (b' := fsp + 3984#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans (sepConj_mono_left
    (unchunkedCt1SentEkReceivedAt_extract_words16 A (fsp + 1856#64) uc_ek)) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro c_ek
  exact Entails.sepExists_right c_ek (Entails.of_eq (by ac_rfl))

set_option maxHeartbeats 800000 in
theorem ct1Sampled_some_ok_ack_pre3 {A : RustAlloc} {F : ShaCompress}
    (b fsp selfA outA msgA : BitVec 64) (s0 : State)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (dec' : PolyDecoder)
    (uc_ek : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F))
    (c_uc c_ek : Words16) (sc : CopyScratchStack) (k : EpilogueStoreStack) :
    wordsAt (fsp + 1856#64) c_ek.toList ∗
      wordsAt (fsp + 3856#64) c_ek.toList ∗
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
        A.pool ∗ stackAt fsp statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗
        messageAt spqrPolyApi msgA msg) ⊢
    (memRegion (fsp + 1856#64) 400 ∗ memRegion (fsp + 2256#64) 56 ∗
      unchunkedCt1SentEkReceivedAt A (fsp + 3856#64) uc_ek ∗
      memRegion (fsp + 3992#64) 104 ∗ unchunkedSendCt2RoAt b ∗
      A.pool ∗ stackAt fsp statesRecvCalleeStackX) ∗
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
      A.pool ∗ stackAt fsp statesRecvCalleeStackX) ∗
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

set_option maxHeartbeats 800000 in
/-- Path 5c from `+11496 -> s0.x30` (`outMsg = some decoded`, `recv_ek = .ok uc_ek`, `ack = true`):
    calls `<Ct1Sent>::recv_ek`, `<Ct1SentEkReceived>::send_ct2`, `send_ct2_encoder`, deallocates
    `ct2`/`mac`/`sending_ct1`/`dec'`, and returns `Ok { key := none, state := .ct2Sampled { uc := outUc, sending_ct2 := outEnc } }`. -/
theorem ct1Sampled_path_some_ok_ack
    {b : BitVec 64} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64)
    (hdealloc : DeallocOkExt b A ext)
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (hrecv_ek : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentRecvEkName)
      (unchunkedCt1SentRecvEkSpec A F K))
    (hsendCt2 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name)
      (unchunkedCt1SentEkReceivedSendCt2Spec A F K b))
    (hsendCt2Enc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr sendCt2EncoderName)
      (sendCt2EncoderSpec A))
    (s0 s_in : State) (fsp selfA outA msgA : BitVec 64)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk) (decoded : Bytes)
    (uc_ek : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F))
    (outUc : Unchunked.SendCt.Ct2Sent (spqrAuthApi F)) (ct2 : Bytes) (mac : Mac)
    (outEnc : PolyEncoder)
    (c_uc : Words16) (sc : CopyScratchStack) (k : EpilogueStoreStack)
    (R : SepProp)
    (heq : msg.epoch = st.uc.epoch)
    (hpay : msg.payload = .ekCt1Ack chunk)
    (hlen : st.receiving_ek.pts.length = 16)
    (hsort : PolyDecoderStrictSorted st.receiving_ek)
    (hdec : decodedMessageTotal (addChunkTotal st.receiving_ek chunk) = some decoded)
    (hrek : st.uc.recv_ek K st.uc.epoch decoded = .ok uc_ek)
    (hsc : uc_ek.send_ct2 K = .ok (outUc, ct2, mac))
    (henc : Chunked.SendCt.send_ct2_encoder spqrPolyApi ct2 mac = .ok outEnc)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp : fsp = s0.sp - 4240#64)
    (hpc : s_in.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 11496#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx19 : s_in.readReg64 .x19 = outA)
    (hx20 : s_in.readReg64 .x20 = st.uc.epoch)
    (hx21 : s_in.readReg64 .x21 = fsp + 3856#64)
    (hx22 : s_in.readReg64 .x22 = 1#64)
    (hx23 : s_in.readReg64 .x23 = polyEncoderTagVal st.sending_ct1)
    (hx28 : s_in.readReg64 .x28 = fsp + 3272#64)
    (hx29 : s_in.readReg64 .x29 = fsp + 4144#64)
    (htr : TraceCalleeSaved s_in s0) :
    let dec' := addChunkTotal st.receiving_ek chunk
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s_in
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
        memRegion outA v1RecvSize ∗ statesRecvRoAt b ∗ A.pool ∗
        stackAt fsp statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗
        messageAt spqrPolyApi msgA msg)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ ((statesRecvVariantSpec A F K b (.ct1Sampled st) msg).post ⟨outA, selfA, msgA⟩ s0 sf) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨ ((statesRecvVariantSpec A F K b (.ct1Sampled st) msg).onPanic ⟨outA, selfA, msgA⟩ s0 sf) ∗ R) := by
  intro dec'
  refine SepWPp.of_sepWP (mid := (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 36780#64) ?_
  refine SepWP.weaken_pre (ct1Sampled_some_ok_ack_pre0 b fsp selfA outA msgA s0 st msg dec' decoded c_uc sc k) ?_
  refine SepWP.seq
    (ct1Sampled_some_to_11528 hrecv_ek s_in fsp st.uc c_uc decoded (.ok uc_ek) _
      (by simpa [StatesResult.ofError] using hrek) hfsp_align hpc hrun hsp hx20) ?_
  intro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, hx19_1, _, hx21_1, hx22_1, hx23_1, _, hx28_1, hx29_1, htr1⟩
  refine SepWP.weaken_pre (Entails.trans hP1
    (ct1Sampled_some_ok_ack_pre1 b fsp selfA outA msgA s0 st msg dec' uc_ek c_uc sc k)) ?_
  apply ProofLib.SepWP.exists_left; intro c_ek
  wp_focus_pure; intro hw0_ek
  refine SepWP.seq
    (ct1Sampled_recv_ek_ok_copy_sc s1 fsp sc c_ek _ hw0_ek hfsp_align hpc1 hrun1 hsp1) ?_
  intro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, hx8_2, hx9_2, hx10_2, hx19_2, _, hx21_2, hx22_2, hx23_2, _, _, hx28_2, hx29_2, htr2⟩
  refine SepWP.weaken_pre hP2 ?_
  refine SepWP.seq
    (ct1Sampled_ok_branch_ack s2 _ hpc2 hrun2 (hx22_2.trans (hx22_1.trans hx22))) ?_
  intro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, _, _, _, hx19_3, _, hx21_3, hx23_3, _, _, hx28_3, hx29_3, htr3⟩
  refine SepWP.weaken_pre (Entails.trans hP3
    (ct1Sampled_some_ok_ack_pre3 b fsp selfA outA msgA s0 st msg dec' uc_ek c_uc c_ek sc k)) ?_
  refine ct1Sampled_send_ct2_and_encode
    (P_pan := (((States.ct1Sampled st).recv K msg).isPanic = true))
    hb hsendCt2 hsendCt2Enc s0 s3 fsp uc_ek outUc ct2 mac outEnc hsc henc _ R
    hfsp_align hpc3 hrun3 (hsp3.trans hsp2)
    (htr3.trans (htr2.trans (htr1.trans htr)))
    (hx21_3.trans (hx21_2.trans (hx21_1.trans hx21)))
    (hx29_3.trans (hx29_2.trans (hx29_1.trans hx29))) ?_
  intro s4 g_uc ct2Cap ct2Ptr macCap macPtr hpc4 hrun4 hsp4 hx19_4 hx20_4 hx21_4 _ hx25_4 hx26_4 hx27_4 hx28_4 hx29_4 htr4
  apply SepWP.done hpc4 hrun4
  refine sepWPp_of_statesRecv_exit s0 s4 outA selfA msgA (.ct1Sampled st) msg _ R ?_
  rw [states_recv_ct1Sampled_eq_some_ok_ack K st msg chunk decoded uc_ek outUc ct2 mac outEnc
    heq hpay hlen hsort hdec hrek hsc henc]
  refine SepWP.mono
    (ct1Sampled_some_ok_ack_from_11696 hb hdealloc hmemcpy s0 s4 fsp selfA outA st dec' c_uc
      outUc outEnc g_uc ct2Cap ct2Ptr macCap macPtr { sc with wb0 := c_ek.w1 } k
      (messageAt spqrPolyApi msgA msg) hfsp_align hsp0_align hfsp hpc4 hrun4 hsp4
      (hx19_4.trans (hx19_3.trans (hx19_2.trans (hx19_1.trans hx19))))
      hx20_4 hx25_4 hx26_4 hx27_4
      (hx28_4.trans (hx28_3.trans (hx28_2.trans (hx28_1.trans hx28))))
      hx29_4 htr4) ?_
  intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
  exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩

set_option maxHeartbeats 2000000 in
/-- Complete `.ct1Sampled` arm from `+1528 -> s0.x30` (`0x55a4c -> s0.x30`) for `msg.payload = .ek chunk`. -/
theorem ct1Sampled_arm_eq_ek
    {b : BitVec 64} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) (hA : AllocContracts b A ext) (hdealloc : DeallocOkExt b A ext)
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (hdec_call : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr polyDecoderDecodedMessageName)
      (polyDecoderDecodedMessageSpec A b))
    (hrecv_ek : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentRecvEkName)
      (unchunkedCt1SentRecvEkSpec A F K))
    (s0 s2 : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk) (R : SepProp)
    (hsort : PolyDecoderStrictSorted st.receiving_ek)
    (heq : msg.epoch = st.uc.epoch) (hpay : msg.payload = .ek chunk)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc2 : s2.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 1528#64)
    (hrun2 : s2.status = .Running) (hsp2 : s2.sp = s0.sp - 4240#64)
    (hx1 : s2.readReg64 .x1 = selfA)
    (hx12 : s2.readReg64 .x12 = polyEncoderTagVal st.sending_ct1)
    (hx19 : s2.readReg64 .x19 = outA)
    (hx21 : s2.readReg64 .x21 = (s0.sp - 4240#64) + 3856#64)
    (hx24 : s2.readReg64 .x24 = msgA)
    (hx28 : s2.readReg64 .x28 = (s0.sp - 4240#64) + 3272#64)
    (hx29 : s2.readReg64 .x29 = s0.sp - 96#64)
    (htr2 : TraceCalleeSaved s2 s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s2
      (memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ct1Sampled st) ∗
        messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ ((statesRecvVariantSpec A F K b (.ct1Sampled st) msg).post ⟨outA, selfA, msgA⟩ s0 sf) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨ ((statesRecvVariantSpec A F K b (.ct1Sampled st) msg).onPanic ⟨outA, selfA, msgA⟩ s0 sf) ∗ R) := by
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  have hpre :
      memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ct1Sampled st) ∗
        messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 ⊢
      ⌜st.receiving_ek.pts.length = 16⌝ ∗
      (((selfA + 520#64) ↦₆₄ st.uc.epoch) ∗ (msgA ↦₆₄ st.uc.epoch) ∗
        (((msgA + 8#64) ↦₈ 2#8) ∗
          (authenticatorAt A (selfA + 400#64) st.uc.auth ∗ vecU8 A (selfA + 448#64) st.uc.hdr ∗
            vecU8 A (selfA + 472#64) st.uc.es ∗ vecU8 A (selfA + 496#64) st.uc.ct1) ∗
          polyEncoderAt A selfA st.sending_ct1 ∗ polyDecoderAt A (selfA + 528#64) st.receiving_ek ∗
          memRegion (msgA + 9#64) 1 ∗ chunkAt (msgA + 10#64) chunk ∗ memRegion (msgA + 44#64) 4 ∗
          memRegion outA v1RecvSize ∗ statesRecvRoAt b ∗ A.pool ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)) := by
    dsimp only [chunkedStatesAt, chunkedCt1SampledAt]
    rw [unchunkedCt1SentAt_epoch_expose A selfA st.uc, messageAt_ek_eq msgA msg chunk hpay, heq]
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right (polyDecoderAt_dup_pts_len A (selfA + 528#64) st.receiving_ek))))) ?_
    exact Entails.of_eq (by ac_rfl)
  refine SepWPp.weaken_pre hpre ?_
  apply SepWPp.of_sepWP (mid := (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 11404#64)
  wp_focus_pure; intro hlen
  refine SepWP.seq
    (ct1Sampled_epoch_cmp_eq s2 selfA msgA st.uc.epoch _ hpc2 hrun2 hx1 hx24) ?_
  intro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, _, hx1_3, _, _, hx12_3, hx19_3, hx20_3, hx21_3, hx24_3, hx28_3, hx29_3, htr3⟩
  have hP3' : P3 ⊢
      ((msgA + 8#64) ↦₈ 2#8) ∗
      (polyEncoderAt A selfA st.sending_ct1 ∗ unchunkedCt1SentAt A (selfA + 400#64) st.uc ∗
        polyDecoderAt A (selfA + 528#64) st.receiving_ek ∗ chunkAt (msgA + 10#64) chunk ∗
        statesRecvRoAt b ∗ A.pool ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
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
        statesRecvRoAt b ∗ A.pool ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        (memRegion outA v1RecvSize ∗ statesRecvSavedCells s0 ∗
          ((msgA + 8#64) ↦₈ 2#8) ∗ (msgA ↦₆₄ st.uc.epoch) ∗
          memRegion (msgA + 9#64) 1 ∗ memRegion (msgA + 44#64) 4) :=
    Entails.trans hP4 (Entails.of_eq (by ac_rfl))
  refine SepWP.weaken_pre hP4' ?_
  apply SepWP.done hpc4 hrun4
  have hx29_fsp : s4.readReg64 .x29 = (s0.sp - 4240#64) + 4144#64 := by
    rw [hx29_4, hx29_3, hx29, sp_sub_4240_add_4144]
  refine ct1Sampled_recv_ek_common_prefix
    (P_pan := (((States.ct1Sampled st).recv K msg).isPanic = true))
    hA hmemcpy hdec_call hb s0 s4 (s0.sp - 4240#64) selfA outA msgA 0#64 st chunk hlen hsort _ R
    hfsp_align hpc4 hrun4 (hsp4.trans (hsp3.trans hsp2)) (hx1_4.trans hx1_3)
    (hx19_4.trans (hx19_3.trans hx19)) (hx20_4.trans hx20_3) (hx21_4.trans (hx21_3.trans hx21))
    hx22_4 (hx23_4.trans (hx12_3.trans hx12)) hx24_4 (hx28_4.trans (hx28_3.trans hx28))
    hx29_fsp (htr4.trans (htr3.trans htr2)) ?_
  intro s5 c_uc sc k hpc5 hrun5 hsp5 hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 _ hx28_5 hx29_5 htr5
  have hmsg_join :
      chunkAt (msgA + 10#64) chunk ∗ ((msgA + 8#64) ↦₈ 2#8) ∗ (msgA ↦₆₄ st.uc.epoch) ∗
        memRegion (msgA + 9#64) 1 ∗ memRegion (msgA + 44#64) 4 =
      messageAt spqrPolyApi msgA msg := by
    rw [messageAt_ek_eq msgA msg chunk hpay, heq]; ac_rfl
  cases hdec_opt : decodedMessageTotal (addChunkTotal st.receiving_ek chunk) with
  | none =>
    refine SepWPp.weaken_pre (Entails.of_eq (show _ =
      optVecU8At A ((s0.sp - 4240#64) + 3832#64) none ∗
        polyDecoderAt A ((s0.sp - 4240#64) + 2752#64) (addChunkTotal st.receiving_ek chunk) ∗
        polyEncoderAt A selfA st.sending_ct1 ∗ wordsAt (selfA + 400#64) c_uc.toList ∗
        wordsAt ((s0.sp - 4240#64) + 3696#64) c_uc.toList ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
        memRegion (selfA + 528#64) 400 ∗ copyScratchStackAt (s0.sp - 4240#64) sc ∗
        epilogueStoreStackPart1At (s0.sp - 4240#64) k ∗ (((s0.sp - 4240#64) + 232#64) ↦₆₄ selfA) ∗
        (((s0.sp - 4240#64) + 512#64) ↦₆₄ k.w200) ∗ (((s0.sp - 4240#64) + 520#64) ↦₆₄ k.w208) ∗
        wordsAt ((s0.sp - 4240#64) + 528#64) k.tail.toList ∗ memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 568#64) 8 ∗ memRegion ((s0.sp - 4240#64) + 952#64) 8 ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 1776 ∗ memRegion ((s0.sp - 4240#64) + 3152#64) 544 ∗
        memRegion ((s0.sp - 4240#64) + 3824#64) 8 ∗ memRegion ((s0.sp - 4240#64) + 3856#64) 288 ∗
        memRegion outA v1RecvSize ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        statesRecvSavedCells s0 ∗
        (statesRecvRoAt b ∗ A.pool ∗
          (chunkAt (msgA + 10#64) chunk ∗ ((msgA + 8#64) ↦₈ 2#8) ∗ (msgA ↦₆₄ st.uc.epoch) ∗
            memRegion (msgA + 9#64) 1 ∗ memRegion (msgA + 44#64) 4)) by ac_rfl)) ?_
    rw [hmsg_join]
    refine sepWPp_of_statesRecv_exit s0 s5 outA selfA msgA (.ct1Sampled st) msg _ R ?_
    rw [states_recv_ct1Sampled_eq_none_no_ack K st msg chunk heq hpay hlen hsort hdec_opt]
    refine SepWP.mono
      (ct1Sampled_path_none_no_ack hmemcpy s0 s5 (s0.sp - 4240#64) selfA outA st
        (addChunkTotal st.receiving_ek chunk) c_uc sc k
        (statesRecvRoAt b ∗ A.pool ∗ messageAt spqrPolyApi msgA msg)
        hfsp_align hsp0_align rfl hpc5 hrun5 hsp5 hx19_5 hx22_5 hx23_5 hx29_5 htr5) ?_
    intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
    exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩
  | some decoded =>
    have hrek_eq := ct1Sent_recv_ek_eq_ofError K st.uc decoded
    dsimp only at hrek_eq
    split_ifs at hrek_eq with hpk
    · let uc_ek : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F) :=
        { epoch := st.uc.epoch, auth := st.uc.auth, es := st.uc.es, ek := decoded, ct1 := st.uc.ct1 }
      have hrek : st.uc.recv_ek K st.uc.epoch decoded = .ok uc_ek := hrek_eq
      refine SepWPp.weaken_pre (Entails.of_eq (show _ =
        optVecU8At A ((s0.sp - 4240#64) + 3832#64) (some decoded) ∗
          polyDecoderAt A ((s0.sp - 4240#64) + 2752#64) (addChunkTotal st.receiving_ek chunk) ∗
          polyEncoderAt A selfA st.sending_ct1 ∗ wordsAt (selfA + 400#64) c_uc.toList ∗
          wordsAt ((s0.sp - 4240#64) + 3696#64) c_uc.toList ∗
          relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
          memRegion (selfA + 528#64) 400 ∗ copyScratchStackAt (s0.sp - 4240#64) sc ∗
          epilogueStoreStackPart1At (s0.sp - 4240#64) k ∗ (((s0.sp - 4240#64) + 232#64) ↦₆₄ selfA) ∗
          (((s0.sp - 4240#64) + 512#64) ↦₆₄ k.w200) ∗ (((s0.sp - 4240#64) + 520#64) ↦₆₄ k.w208) ∗
          wordsAt ((s0.sp - 4240#64) + 528#64) k.tail.toList ∗ memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
          memRegion ((s0.sp - 4240#64) + 568#64) 8 ∗ memRegion ((s0.sp - 4240#64) + 952#64) 8 ∗
          memRegion ((s0.sp - 4240#64) + 976#64) 1776 ∗ memRegion ((s0.sp - 4240#64) + 3152#64) 544 ∗
          memRegion ((s0.sp - 4240#64) + 3824#64) 8 ∗ memRegion ((s0.sp - 4240#64) + 3856#64) 288 ∗
          memRegion outA v1RecvSize ∗ statesRecvRoAt b ∗ A.pool ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗
          (chunkAt (msgA + 10#64) chunk ∗ ((msgA + 8#64) ↦₈ 2#8) ∗ (msgA ↦₆₄ st.uc.epoch) ∗
            memRegion (msgA + 9#64) 1 ∗ memRegion (msgA + 44#64) 4) by ac_rfl)) ?_
      rw [hmsg_join]
      refine sepWPp_of_statesRecv_exit s0 s5 outA selfA msgA (.ct1Sampled st) msg _ R ?_
      rw [states_recv_ct1Sampled_eq_some_ok_no_ack K st msg chunk decoded uc_ek
        heq hpay hlen hsort hdec_opt hrek]
      refine SepWP.mono
        (ct1Sampled_path_some_ok_no_ack hb hdealloc hmemcpy hrecv_ek s0 s5 (s0.sp - 4240#64)
          selfA outA st (addChunkTotal st.receiving_ek chunk) c_uc decoded uc_ek sc k
          (messageAt spqrPolyApi msgA msg) hrek hfsp_align hsp0_align rfl
          hpc5 hrun5 hsp5 hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx28_5 hx29_5 htr5) ?_
      intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
      exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩
    · have hrek : st.uc.recv_ek K st.uc.epoch decoded = .error (.err .erroneousDataReceived) := hrek_eq
      refine SepWPp.weaken_pre (Entails.of_eq (show _ =
        optVecU8At A ((s0.sp - 4240#64) + 3832#64) (some decoded) ∗
          polyDecoderAt A ((s0.sp - 4240#64) + 2752#64) (addChunkTotal st.receiving_ek chunk) ∗
          polyEncoderAt A selfA st.sending_ct1 ∗ wordsAt (selfA + 400#64) c_uc.toList ∗
          wordsAt ((s0.sp - 4240#64) + 3696#64) c_uc.toList ∗
          relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
          memRegion (selfA + 528#64) 400 ∗ copyScratchStackAt (s0.sp - 4240#64) sc ∗
          epilogueStoreStackPart1At (s0.sp - 4240#64) k ∗ (((s0.sp - 4240#64) + 232#64) ↦₆₄ selfA) ∗
          (((s0.sp - 4240#64) + 512#64) ↦₆₄ k.w200) ∗ (((s0.sp - 4240#64) + 520#64) ↦₆₄ k.w208) ∗
          wordsAt ((s0.sp - 4240#64) + 528#64) k.tail.toList ∗ memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
          memRegion ((s0.sp - 4240#64) + 568#64) 8 ∗ memRegion ((s0.sp - 4240#64) + 952#64) 8 ∗
          memRegion ((s0.sp - 4240#64) + 976#64) 1776 ∗ memRegion ((s0.sp - 4240#64) + 3152#64) 544 ∗
          memRegion ((s0.sp - 4240#64) + 3824#64) 8 ∗ memRegion ((s0.sp - 4240#64) + 3856#64) 288 ∗
          memRegion outA v1RecvSize ∗ A.pool ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗
          (statesRecvRoAt b ∗
            (chunkAt (msgA + 10#64) chunk ∗ ((msgA + 8#64) ↦₈ 2#8) ∗ (msgA ↦₆₄ st.uc.epoch) ∗
              memRegion (msgA + 9#64) 1 ∗ memRegion (msgA + 44#64) 4)) by ac_rfl)) ?_
      rw [hmsg_join]
      refine sepWPp_of_statesRecv_exit s0 s5 outA selfA msgA (.ct1Sampled st) msg _ R ?_
      rw [states_recv_ct1Sampled_eq_some_err K st msg chunk decoded .erroneousDataReceived
        heq (Or.inl hpay) hlen hsort hdec_opt hrek]
      refine SepWP.mono
        (ct1Sampled_path_some_err hdealloc hrecv_ek s0 s5 (s0.sp - 4240#64) selfA outA st
          (addChunkTotal st.receiving_ek chunk) c_uc decoded .erroneousDataReceived sc k
          (statesRecvRoAt b ∗ messageAt spqrPolyApi msgA msg)
          hrek rfl hfsp_align hsp0_align rfl hpc5 hrun5 hsp5 hx19_5 hx20_5 htr5) ?_
      intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
      exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩

set_option maxHeartbeats 2000000 in
/-- Complete `.ct1Sampled` arm from `+1528 -> s0.x30` (`0x55a4c -> s0.x30`) for `msg.payload = .ekCt1Ack chunk`. -/
theorem ct1Sampled_arm_eq_ekCt1Ack
    {b : BitVec 64} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) (hA : AllocContracts b A ext) (hdealloc : DeallocOkExt b A ext)
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (hdec_call : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr polyDecoderDecodedMessageName)
      (polyDecoderDecodedMessageSpec A b))
    (hrecv_ek : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentRecvEkName)
      (unchunkedCt1SentRecvEkSpec A F K))
    (hsendCt2 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name)
      (unchunkedCt1SentEkReceivedSendCt2Spec A F K b))
    (hsendCt2Enc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr sendCt2EncoderName) (sendCt2EncoderSpec A))
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
    (hpc2 : s2.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 1528#64)
    (hrun2 : s2.status = .Running) (hsp2 : s2.sp = s0.sp - 4240#64)
    (hx1 : s2.readReg64 .x1 = selfA) (hx12 : s2.readReg64 .x12 = polyEncoderTagVal st.sending_ct1)
    (hx19 : s2.readReg64 .x19 = outA) (hx21 : s2.readReg64 .x21 = (s0.sp - 4240#64) + 3856#64)
    (hx24 : s2.readReg64 .x24 = msgA) (hx28 : s2.readReg64 .x28 = (s0.sp - 4240#64) + 3272#64)
    (hx29 : s2.readReg64 .x29 = s0.sp - 96#64) (htr2 : TraceCalleeSaved s2 s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s2
      (memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ct1Sampled st) ∗
        messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ ((statesRecvVariantSpec A F K b (.ct1Sampled st) msg).post ⟨outA, selfA, msgA⟩ s0 sf) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨ ((statesRecvVariantSpec A F K b (.ct1Sampled st) msg).onPanic ⟨outA, selfA, msgA⟩ s0 sf) ∗ R) := by
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  have hpre :
      memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ct1Sampled st) ∗
        messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 ⊢
      ⌜st.receiving_ek.pts.length = 16⌝ ∗
      (((selfA + 520#64) ↦₆₄ st.uc.epoch) ∗ (msgA ↦₆₄ st.uc.epoch) ∗
        (((msgA + 8#64) ↦₈ 3#8) ∗
          (authenticatorAt A (selfA + 400#64) st.uc.auth ∗ vecU8 A (selfA + 448#64) st.uc.hdr ∗
            vecU8 A (selfA + 472#64) st.uc.es ∗ vecU8 A (selfA + 496#64) st.uc.ct1) ∗
          polyEncoderAt A selfA st.sending_ct1 ∗ polyDecoderAt A (selfA + 528#64) st.receiving_ek ∗
          memRegion (msgA + 9#64) 1 ∗ chunkAt (msgA + 10#64) chunk ∗ memRegion (msgA + 44#64) 4 ∗
          memRegion outA v1RecvSize ∗ statesRecvRoAt b ∗ A.pool ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)) := by
    dsimp only [chunkedStatesAt, chunkedCt1SampledAt]
    rw [unchunkedCt1SentAt_epoch_expose A selfA st.uc, messageAt_ekCt1Ack_eq msgA msg chunk hpay, heq]
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right (polyDecoderAt_dup_pts_len A (selfA + 528#64) st.receiving_ek))))) ?_
    exact Entails.of_eq (by ac_rfl)
  refine SepWPp.weaken_pre hpre ?_
  apply SepWPp.of_sepWP (mid := (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 11404#64)
  wp_focus_pure; intro hlen
  refine SepWP.seq
    (ct1Sampled_epoch_cmp_eq s2 selfA msgA st.uc.epoch _ hpc2 hrun2 hx1 hx24) ?_
  intro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, _, hx1_3, _, _, hx12_3, hx19_3, hx20_3, hx21_3, hx24_3, hx28_3, hx29_3, htr3⟩
  have hP3' : P3 ⊢
      ((msgA + 8#64) ↦₈ 3#8) ∗
      (polyEncoderAt A selfA st.sending_ct1 ∗ unchunkedCt1SentAt A (selfA + 400#64) st.uc ∗
        polyDecoderAt A (selfA + 528#64) st.receiving_ek ∗ chunkAt (msgA + 10#64) chunk ∗
        statesRecvRoAt b ∗ A.pool ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
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
        statesRecvRoAt b ∗ A.pool ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        (memRegion outA v1RecvSize ∗ statesRecvSavedCells s0 ∗
          ((msgA + 8#64) ↦₈ 3#8) ∗ (msgA ↦₆₄ st.uc.epoch) ∗
          memRegion (msgA + 9#64) 1 ∗ memRegion (msgA + 44#64) 4) :=
    Entails.trans hP4 (Entails.of_eq (by ac_rfl))
  refine SepWP.weaken_pre hP4' ?_
  apply SepWP.done hpc4 hrun4
  have hx29_fsp : s4.readReg64 .x29 = (s0.sp - 4240#64) + 4144#64 := by
    rw [hx29_4, hx29_3, hx29, sp_sub_4240_add_4144]
  refine ct1Sampled_recv_ek_common_prefix
    (P_pan := (((States.ct1Sampled st).recv K msg).isPanic = true))
    hA hmemcpy hdec_call hb s0 s4 (s0.sp - 4240#64) selfA outA msgA 1#64 st chunk hlen hsort _ R
    hfsp_align hpc4 hrun4 (hsp4.trans (hsp3.trans hsp2)) (hx1_4.trans hx1_3)
    (hx19_4.trans (hx19_3.trans hx19)) (hx20_4.trans hx20_3) (hx21_4.trans (hx21_3.trans hx21))
    hx22_4 (hx23_4.trans (hx12_3.trans hx12)) hx24_4 (hx28_4.trans (hx28_3.trans hx28))
    hx29_fsp (htr4.trans (htr3.trans htr2)) ?_
  intro s5 c_uc sc k hpc5 hrun5 hsp5 hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 _ hx28_5 hx29_5 htr5
  have hmsg_join :
      chunkAt (msgA + 10#64) chunk ∗ ((msgA + 8#64) ↦₈ 3#8) ∗ (msgA ↦₆₄ st.uc.epoch) ∗
        memRegion (msgA + 9#64) 1 ∗ memRegion (msgA + 44#64) 4 =
      messageAt spqrPolyApi msgA msg := by
    rw [messageAt_ekCt1Ack_eq msgA msg chunk hpay, heq]; ac_rfl
  cases hdec_opt : decodedMessageTotal (addChunkTotal st.receiving_ek chunk) with
  | none =>
    refine SepWPp.weaken_pre (Entails.of_eq (show _ =
      optVecU8At A ((s0.sp - 4240#64) + 3832#64) none ∗
        polyDecoderAt A ((s0.sp - 4240#64) + 2752#64) (addChunkTotal st.receiving_ek chunk) ∗
        polyEncoderAt A selfA st.sending_ct1 ∗ wordsAt (selfA + 400#64) c_uc.toList ∗
        wordsAt ((s0.sp - 4240#64) + 3696#64) c_uc.toList ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
        memRegion (selfA + 528#64) 400 ∗ copyScratchStackAt (s0.sp - 4240#64) sc ∗
        epilogueStoreStackPart1At (s0.sp - 4240#64) k ∗ (((s0.sp - 4240#64) + 232#64) ↦₆₄ selfA) ∗
        (((s0.sp - 4240#64) + 512#64) ↦₆₄ k.w200) ∗ (((s0.sp - 4240#64) + 520#64) ↦₆₄ k.w208) ∗
        wordsAt ((s0.sp - 4240#64) + 528#64) k.tail.toList ∗ memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 568#64) 8 ∗ memRegion ((s0.sp - 4240#64) + 952#64) 8 ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 1776 ∗ memRegion ((s0.sp - 4240#64) + 3152#64) 544 ∗
        memRegion ((s0.sp - 4240#64) + 3824#64) 8 ∗ memRegion ((s0.sp - 4240#64) + 3856#64) 288 ∗
        memRegion outA v1RecvSize ∗ statesRecvRoAt b ∗ A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗
        (chunkAt (msgA + 10#64) chunk ∗ ((msgA + 8#64) ↦₈ 3#8) ∗ (msgA ↦₆₄ st.uc.epoch) ∗
          memRegion (msgA + 9#64) 1 ∗ memRegion (msgA + 44#64) 4) by ac_rfl)) ?_
    rw [hmsg_join]
    refine sepWPp_of_statesRecv_exit s0 s5 outA selfA msgA (.ct1Sampled st) msg _ R ?_
    rw [states_recv_ct1Sampled_eq_none_ack K st msg chunk heq hpay hlen hsort hdec_opt]
    refine SepWP.mono
      (ct1Sampled_path_none_ack hb hdealloc hmemcpy s0 s5 (s0.sp - 4240#64) selfA outA st
        (addChunkTotal st.receiving_ek chunk) c_uc sc k
        (messageAt spqrPolyApi msgA msg)
        hfsp_align hsp0_align rfl hpc5 hrun5 hsp5 hx19_5 hx22_5 hx28_5 htr5) ?_
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
      refine SepWPp.weaken_pre (Entails.of_eq (show _ =
        optVecU8At A ((s0.sp - 4240#64) + 3832#64) (some decoded) ∗
          polyDecoderAt A ((s0.sp - 4240#64) + 2752#64) (addChunkTotal st.receiving_ek chunk) ∗
          polyEncoderAt A selfA st.sending_ct1 ∗ wordsAt (selfA + 400#64) c_uc.toList ∗
          wordsAt ((s0.sp - 4240#64) + 3696#64) c_uc.toList ∗
          relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
          memRegion (selfA + 528#64) 400 ∗ copyScratchStackAt (s0.sp - 4240#64) sc ∗
          epilogueStoreStackPart1At (s0.sp - 4240#64) k ∗ (((s0.sp - 4240#64) + 232#64) ↦₆₄ selfA) ∗
          (((s0.sp - 4240#64) + 512#64) ↦₆₄ k.w200) ∗ (((s0.sp - 4240#64) + 520#64) ↦₆₄ k.w208) ∗
          wordsAt ((s0.sp - 4240#64) + 528#64) k.tail.toList ∗ memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
          memRegion ((s0.sp - 4240#64) + 568#64) 8 ∗ memRegion ((s0.sp - 4240#64) + 952#64) 8 ∗
          memRegion ((s0.sp - 4240#64) + 976#64) 1776 ∗ memRegion ((s0.sp - 4240#64) + 3152#64) 544 ∗
          memRegion ((s0.sp - 4240#64) + 3824#64) 8 ∗ memRegion ((s0.sp - 4240#64) + 3856#64) 288 ∗
          memRegion outA v1RecvSize ∗ statesRecvRoAt b ∗ A.pool ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗
          (chunkAt (msgA + 10#64) chunk ∗ ((msgA + 8#64) ↦₈ 3#8) ∗ (msgA ↦₆₄ st.uc.epoch) ∗
            memRegion (msgA + 9#64) 1 ∗ memRegion (msgA + 44#64) 4) by ac_rfl)) ?_
      rw [hmsg_join]
      exact ct1Sampled_path_some_ok_ack hb hdealloc hmemcpy hrecv_ek hsendCt2 hsendCt2Enc
        s0 s5 (s0.sp - 4240#64) selfA outA msgA st msg chunk decoded uc_ek outUc ct2 mac outEnc
        c_uc sc k R heq hpay hlen hsort hdec_opt hrek hsc henc hfsp_align hsp0_align rfl
        hpc5 hrun5 hsp5 hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx28_5 hx29_5 htr5
    · have hrek : st.uc.recv_ek K st.uc.epoch decoded = .error (.err .erroneousDataReceived) := hrek_eq
      refine SepWPp.weaken_pre (Entails.of_eq (show _ =
        optVecU8At A ((s0.sp - 4240#64) + 3832#64) (some decoded) ∗
          polyDecoderAt A ((s0.sp - 4240#64) + 2752#64) (addChunkTotal st.receiving_ek chunk) ∗
          polyEncoderAt A selfA st.sending_ct1 ∗ wordsAt (selfA + 400#64) c_uc.toList ∗
          wordsAt ((s0.sp - 4240#64) + 3696#64) c_uc.toList ∗
          relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
          memRegion (selfA + 528#64) 400 ∗ copyScratchStackAt (s0.sp - 4240#64) sc ∗
          epilogueStoreStackPart1At (s0.sp - 4240#64) k ∗ (((s0.sp - 4240#64) + 232#64) ↦₆₄ selfA) ∗
          (((s0.sp - 4240#64) + 512#64) ↦₆₄ k.w200) ∗ (((s0.sp - 4240#64) + 520#64) ↦₆₄ k.w208) ∗
          wordsAt ((s0.sp - 4240#64) + 528#64) k.tail.toList ∗ memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
          memRegion ((s0.sp - 4240#64) + 568#64) 8 ∗ memRegion ((s0.sp - 4240#64) + 952#64) 8 ∗
          memRegion ((s0.sp - 4240#64) + 976#64) 1776 ∗ memRegion ((s0.sp - 4240#64) + 3152#64) 544 ∗
          memRegion ((s0.sp - 4240#64) + 3824#64) 8 ∗ memRegion ((s0.sp - 4240#64) + 3856#64) 288 ∗
          memRegion outA v1RecvSize ∗ A.pool ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗
          (statesRecvRoAt b ∗
            (chunkAt (msgA + 10#64) chunk ∗ ((msgA + 8#64) ↦₈ 3#8) ∗ (msgA ↦₆₄ st.uc.epoch) ∗
              memRegion (msgA + 9#64) 1 ∗ memRegion (msgA + 44#64) 4)) by ac_rfl)) ?_
      rw [hmsg_join]
      refine sepWPp_of_statesRecv_exit s0 s5 outA selfA msgA (.ct1Sampled st) msg _ R ?_
      rw [states_recv_ct1Sampled_eq_some_err K st msg chunk decoded .erroneousDataReceived
        heq (Or.inr hpay) hlen hsort hdec_opt hrek]
      refine SepWP.mono
        (ct1Sampled_path_some_err hdealloc hrecv_ek s0 s5 (s0.sp - 4240#64) selfA outA st
          (addChunkTotal st.receiving_ek chunk) c_uc decoded .erroneousDataReceived sc k
          (statesRecvRoAt b ∗ messageAt spqrPolyApi msgA msg)
          hrek rfl hfsp_align hsp0_align rfl hpc5 hrun5 hsp5 hx19_5 hx20_5 htr5) ?_
      intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
      exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩

set_option maxHeartbeats 2000000 in
/-- Complete `.ct1Sampled` arm from `+1528 -> s0.x30` (`0x55a4c -> s0.x30`) for all `msg`. -/
theorem states_recv_arm_ct1Sampled
    {b : BitVec 64} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) (hA : AllocContracts b A ext) (hdealloc : DeallocOkExt b A ext)
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (hdec_call : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr polyDecoderDecodedMessageName)
      (polyDecoderDecodedMessageSpec A b))
    (hrecv_ek : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentRecvEkName)
      (unchunkedCt1SentRecvEkSpec A F K))
    (hsendCt2 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name)
      (unchunkedCt1SentEkReceivedSendCt2Spec A F K b))
    (hsendCt2Enc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr sendCt2EncoderName) (sendCt2EncoderSpec A))
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
    (hpc2 : s2.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 1528#64)
    (hrun2 : s2.status = .Running) (hsp2 : s2.sp = s0.sp - 4240#64)
    (hx1 : s2.readReg64 .x1 = selfA) (hx12 : s2.readReg64 .x12 = polyEncoderTagVal st.sending_ct1)
    (hx19 : s2.readReg64 .x19 = outA) (hx21 : s2.readReg64 .x21 = (s0.sp - 4240#64) + 3856#64)
    (hx24 : s2.readReg64 .x24 = msgA) (hx28 : s2.readReg64 .x28 = (s0.sp - 4240#64) + 3272#64)
    (hx29 : s2.readReg64 .x29 = s0.sp - 96#64) (htr2 : TraceCalleeSaved s2 s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s2
      (memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ct1Sampled st) ∗
        messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ ((statesRecvVariantSpec A F K b (.ct1Sampled st) msg).post ⟨outA, selfA, msgA⟩ s0 sf) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨ ((statesRecvVariantSpec A F K b (.ct1Sampled st) msg).onPanic ⟨outA, selfA, msgA⟩ s0 sf) ∗ R) := by
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  by_cases hgt : msg.epoch.toNat > st.uc.epoch.toNat
  · refine sepWPp_of_statesRecv_exit s0 s2 outA selfA msgA (.ct1Sampled st) msg _ R ?_
    rw [states_recv_ct1Sampled_eq_gt K st msg hgt]
    have hpre :
        memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ct1Sampled st) ∗
          messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 ⊢
        ((selfA + 520#64) ↦₆₄ st.uc.epoch) ∗ (msgA ↦₆₄ msg.epoch) ∗
        (memRegion outA v1RecvSize ∗ polyEncoderAt A selfA st.sending_ct1 ∗
          (authenticatorAt A (selfA + 400#64) st.uc.auth ∗ vecU8 A (selfA + 448#64) st.uc.hdr ∗
            vecU8 A (selfA + 472#64) st.uc.es ∗ vecU8 A (selfA + 496#64) st.uc.ct1) ∗
          polyDecoderAt A (selfA + 528#64) st.receiving_ek ∗
          messagePayloadAt spqrPolyApi msgA msg.payload ∗ statesRecvRoAt b ∗ A.pool ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0) := by
      dsimp only [chunkedStatesAt, chunkedCt1SampledAt, messageAt]
      rw [unchunkedCt1SentAt_epoch_expose A selfA st.uc]; exact Entails.of_eq (by ac_rfl)
    refine SepWP.weaken_pre hpre ?_
    refine SepWP.seq
      (ct1Sampled_epoch_cmp_gt s2 selfA msgA st.uc.epoch msg.epoch _ hgt hpc2 hrun2 hx1 hx24) ?_
    intro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, hx1_3, hx19_3, hx20_3, _, _, _, _, htr3⟩
    have hP3' : P3 ⊢
        memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ct1Sampled st) ∗ A.pool ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
          statesRecvSavedCells s0 ∗ (messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b) := by
      refine Entails.trans hP3 ?_
      dsimp only [chunkedStatesAt, chunkedCt1SampledAt, messageAt]
      rw [unchunkedCt1SentAt_epoch_expose A selfA st.uc]; exact Entails.of_eq (by ac_rfl)
    refine SepWP.weaken_pre hP3' ?_
    refine SepWP.mono
      (ct1Sampled_drop_epochOutOfRange hdealloc s0 s3 outA selfA msg.epoch st
        (messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b)
        hsp0_align hpc3 hrun3 (hsp3.trans hsp2) hx1_3 (hx19_3.trans hx19) hx20_3 (htr3.trans htr2)) ?_
    intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
    exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩
  · by_cases hlt : msg.epoch.toNat < st.uc.epoch.toNat
    · refine sepWPp_of_statesRecv_exit s0 s2 outA selfA msgA (.ct1Sampled st) msg _ R ?_
      rw [states_recv_ct1Sampled_eq_lt K st msg hlt]
      have hpre :
          memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ct1Sampled st) ∗
            messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool ∗
            stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
            memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 ⊢
          ((selfA + 520#64) ↦₆₄ st.uc.epoch) ∗ (msgA ↦₆₄ msg.epoch) ∗
          (memRegion outA v1RecvSize ∗ polyEncoderAt A selfA st.sending_ct1 ∗
            (authenticatorAt A (selfA + 400#64) st.uc.auth ∗ vecU8 A (selfA + 448#64) st.uc.hdr ∗
              vecU8 A (selfA + 472#64) st.uc.es ∗ vecU8 A (selfA + 496#64) st.uc.ct1) ∗
            polyDecoderAt A (selfA + 528#64) st.receiving_ek ∗
            messagePayloadAt spqrPolyApi msgA msg.payload ∗ statesRecvRoAt b ∗ A.pool ∗
            stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
            memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0) := by
        dsimp only [chunkedStatesAt, chunkedCt1SampledAt, messageAt]
        rw [unchunkedCt1SentAt_epoch_expose A selfA st.uc]; exact Entails.of_eq (by ac_rfl)
      refine SepWP.weaken_pre hpre ?_
      refine SepWP.seq
        (ct1Sampled_epoch_cmp_lt s2 selfA msgA st.uc.epoch msg.epoch _ hlt hpc2 hrun2 hx1 hx24) ?_
      intro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, _, hx1_3, _, _, hx12_3, hx19_3, _, _, _, _, hx29_3, htr3⟩
      have hP3' : P3 ⊢
          ((selfA ↦₆₄ polyEncoderTagVal st.sending_ct1) ∗ chunkedCt1SampledBodyAt A (selfA + 8#64) st) ∗
          memRegion outA v1RecvSize ∗ memRegion (s0.sp - 4240#64) 4144 ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗
          (messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool) := by
        refine Entails.trans hP3 ?_
        rw [← chunkedCt1SampledAt_eq_tag_body A selfA st]
        dsimp only [chunkedCt1SampledAt, messageAt]
        rw [unchunkedCt1SentAt_epoch_expose A selfA st.uc]; exact Entails.of_eq (by ac_rfl)
      refine SepWP.weaken_pre hP3' ?_
      refine SepWP.mono
        (ct1Sampled_path_lt hmemcpy s0 s3 (s0.sp - 4240#64) selfA outA st
          (messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool)
          hfsp_align hsp0_align rfl hpc3 hrun3 (hsp3.trans hsp2)
          hx1_3 (hx12_3.trans hx12) (hx19_3.trans hx19) (hx29_3.trans hx29) (htr3.trans htr2)) ?_
      intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
      exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩
    · have heq : msg.epoch = st.uc.epoch := by apply BitVec.eq_of_toNat_eq; omega
      cases hpay : msg.payload with
      | ek chunk =>
        exact ct1Sampled_arm_eq_ek hb hA hdealloc hmemcpy hdec_call hrecv_ek
          s0 s2 outA selfA msgA st msg chunk R hsort heq hpay
          hsp0_align hpc2 hrun2 hsp2 hx1 hx12 hx19 hx21 hx24 hx28 hx29 htr2
      | ekCt1Ack chunk =>
        exact ct1Sampled_arm_eq_ekCt1Ack hb hA hdealloc hmemcpy hdec_call hrecv_ek hsendCt2 hsendCt2Enc
          s0 s2 outA selfA msgA st msg chunk R hsort
          (fun decoded uc_ek hdec hrek => h_sendCt2 chunk decoded uc_ek heq hpay hdec hrek)
          heq hpay hsp0_align hpc2 hrun2 hsp2 hx1 hx12 hx19 hx21 hx24 hx28 hx29 htr2
      | none | hdr _ | ct1Ack _ | ct1 _ | ct2 _ =>
        have hnot_ek : ∀ c, msg.payload ≠ .ek c := by intro c hc; rw [hpay] at hc; cases hc
        have hnot_ack : ∀ c, msg.payload ≠ .ekCt1Ack c := by intro c hc; rw [hpay] at hc; cases hc
        obtain ⟨msg_tag, Rest_msg, hne2, hne3, hmsg_pay⟩ :=
          messagePayloadAt_other_expose msgA msg.payload hnot_ek hnot_ack
        refine sepWPp_of_statesRecv_exit s0 s2 outA selfA msgA (.ct1Sampled st) msg _ R ?_
        rw [states_recv_ct1Sampled_eq_other K st msg heq hnot_ek hnot_ack]
        have hpre :
            memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ct1Sampled st) ∗
              messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool ∗
              stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
              memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 ⊢
            ((selfA + 520#64) ↦₆₄ st.uc.epoch) ∗ (msgA ↦₆₄ st.uc.epoch) ∗
            (((msgA + 8#64) ↦₈ msg_tag) ∗ Rest_msg ∗ memRegion outA v1RecvSize ∗
              polyEncoderAt A selfA st.sending_ct1 ∗
              (authenticatorAt A (selfA + 400#64) st.uc.auth ∗ vecU8 A (selfA + 448#64) st.uc.hdr ∗
                vecU8 A (selfA + 472#64) st.uc.es ∗ vecU8 A (selfA + 496#64) st.uc.ct1) ∗
              polyDecoderAt A (selfA + 528#64) st.receiving_ek ∗ statesRecvRoAt b ∗ A.pool ∗
              stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
              memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0) := by
          dsimp only [chunkedStatesAt, chunkedCt1SampledAt, messageAt]
          rw [unchunkedCt1SentAt_epoch_expose A selfA st.uc, hmsg_pay, heq]
          exact Entails.of_eq (by ac_rfl)
        refine SepWP.weaken_pre hpre ?_
        refine SepWP.seq
          (ct1Sampled_epoch_cmp_eq s2 selfA msgA st.uc.epoch _ hpc2 hrun2 hx1 hx24) ?_
        intro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, _, hx1_3, _, _, hx12_3, hx19_3, _, _, hx24_3, _, hx29_3, htr3⟩
        have hP3' : P3 ⊢
            ((msgA + 8#64) ↦₈ msg_tag) ∗
            ((selfA + 520#64) ↦₆₄ st.uc.epoch) ∗ (msgA ↦₆₄ st.uc.epoch) ∗ Rest_msg ∗
            memRegion outA v1RecvSize ∗ polyEncoderAt A selfA st.sending_ct1 ∗
            (authenticatorAt A (selfA + 400#64) st.uc.auth ∗ vecU8 A (selfA + 448#64) st.uc.hdr ∗
              vecU8 A (selfA + 472#64) st.uc.es ∗ vecU8 A (selfA + 496#64) st.uc.ct1) ∗
            polyDecoderAt A (selfA + 528#64) st.receiving_ek ∗ statesRecvRoAt b ∗ A.pool ∗
            stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
            memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 :=
          Entails.trans hP3 (Entails.of_eq (by ac_rfl))
        refine SepWP.weaken_pre hP3' ?_
        refine SepWP.seq
          (ct1Sampled_msg_kind_check_other s3 msgA msg_tag _ hne2 hne3 hpc3 hrun3 hx24_3) ?_
        intro s4 P4 hpc4 hrun4 ⟨hP4, hsp4, hx1_4, hx12_4, hx19_4, hx29_4, htr4⟩
        have hP4' : P4 ⊢
            ((selfA ↦₆₄ polyEncoderTagVal st.sending_ct1) ∗ chunkedCt1SampledBodyAt A (selfA + 8#64) st) ∗
            memRegion outA v1RecvSize ∗ memRegion (s0.sp - 4240#64) 4144 ∗
            stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗
            (messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool) := by
          refine Entails.trans hP4 ?_
          rw [← chunkedCt1SampledAt_eq_tag_body A selfA st]
          dsimp only [chunkedCt1SampledAt, messageAt]
          rw [unchunkedCt1SentAt_epoch_expose A selfA st.uc, hmsg_pay, heq]
          exact Entails.of_eq (by ac_rfl)
        refine SepWP.weaken_pre hP4' ?_
        refine SepWP.mono
          (ct1Sampled_path_other_from_12144 hmemcpy s0 s4 (s0.sp - 4240#64) selfA outA st
            (messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool)
            hfsp_align hsp0_align rfl hpc4 hrun4 (hsp4.trans (hsp3.trans hsp2))
            (hx1_4.trans hx1_3) (hx12_4.trans (hx12_3.trans hx12))
            (hx19_4.trans (hx19_3.trans hx19)) (hx29_4.trans (hx29_3.trans hx29))
            (htr4.trans (htr3.trans htr2))) ?_
        intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
        exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩

theorem ct1Sampled_send_ct2_ok_of_recv_ek_ok {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (decoded : Bytes) (uc_ek : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F))
    (hes : st.uc.es.length = 2080) (hct1 : st.uc.ct1.length = 960)
    (hmac : st.uc.auth.macKey.length < 2 ^ 32)
    (hrek : st.uc.recv_ek K st.uc.epoch decoded = .ok uc_ek) :
    ∃ outUc ct2 mac outEnc,
      uc_ek.send_ct2 K = .ok (outUc, ct2, mac) ∧
      Chunked.SendCt.send_ct2_encoder spqrPolyApi ct2 mac = .ok outEnc := by
  unfold Unchunked.SendCt.Ct1Sent.recv_ek ek_matches_header MlKem.validPkBytes at hrek
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at hrek
  split_ifs at hrek with hval
  have huc : uc_ek = { epoch := st.uc.epoch, auth := st.uc.auth, es := st.uc.es, ek := decoded, ct1 := st.uc.ct1 } :=
    (Except.ok.inj hrek).symm
  simp only [Bool.and_eq_true, beq_iff_eq] at hval
  subst huc
  exact send_ct2_and_encoder_eq_ok_of_lengths K _ hes hval.1.2 hct1 hmac

/-- Per-variant specification proof for `States.ct1Sampled st` (`tag = 0#64 ∨ tag = 1#64`). -/
theorem states_recv_ct1Sampled_ok_ext
    (A : RustAlloc) (F : ShaCompress) (K : MlKem) (b : BitVec 64)
    (ext : String → Option (State → State))
    (hA : AllocContracts b A ext) (hdealloc : DeallocOkExt b A ext)
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (hdec_call : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr polyDecoderDecodedMessageName)
      (polyDecoderDecodedMessageSpec A b))
    (hrecv_ek : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentRecvEkName)
      (unchunkedCt1SentRecvEkSpec A F K))
    (hsendCt2 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name)
      (unchunkedCt1SentEkReceivedSendCt2Spec A F K b))
    (hsendCt2Enc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr sendCt2EncoderName)
      (sendCt2EncoderSpec A))
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName)
      (statesRecvVariantSpec A F K b (.ct1Sampled st) msg) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨outA, selfA, msgA⟩ R s0 hpc0 hrun0 hpre hsp0_align
  simp only [statesRecvVariantSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hb, hx0, hx1, hx2, hsort, hes, hct1, hmac⟩, hmem⟩
  refine ⟨stackAt s0.sp statesRecvStackX ∗ (memRegion outA v1RecvSize ∗
      chunkedStatesAt A selfA (.ct1Sampled st) ∗
      messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool),
    R, Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem, ?_⟩
  have hpro := ct1Sampled_prologue (b := b) (ext := ext) s0
    (memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ct1Sampled st) ∗
     messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool) hsp0_align hpc0 hrun0
  refine sepWPp_seq_clean hpro ?_
  intro s1 hpc1 hrun1 ⟨hsp1, hx0_1, hx1_1, hx2_1, _, hx29_1, htr1⟩
  rw [hx0] at hx0_1; rw [hx1] at hx1_1; rw [hx2] at hx2_1
  have hP1' :
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
      statesRecvSavedCells s0 ∗
      (memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ct1Sampled st) ∗
       messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool) ⊢
      (selfA ↦₆₄ polyEncoderTagVal st.sending_ct1) ∗ statesRecvRoAt b ∗
      (chunkedCt1SampledBodyAt A (selfA + 8#64) st ∗
        memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0) := by
    dsimp only [chunkedStatesAt]
    rw [chunkedCt1SampledAt_eq_tag_body A selfA st]; exact Entails.of_eq (by ac_rfl)
  refine SepWPp.weaken_pre hP1' ?_
  have hdisp := ct1Sampled_dispatch (b := b) (ext := ext) hb s1 (s0.sp - 4240#64) selfA
    (polyEncoderTagVal st.sending_ct1)
    (chunkedCt1SampledBodyAt A (selfA + 8#64) st ∗
      memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ A.pool ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
      statesRecvSavedCells s0)
    (polyEncoderTagVal_zero_or_one st.sending_ct1) hpc1 hrun1 hsp1 hx1_1
  refine sepWPp_seq_clean hdisp ?_
  intro s2 hpc2 hrun2 ⟨hsp2, _, hx1_2, _, _, _, hx12_2, hx19_2, hx21_2, hx24_2, hx28_2, hx29_2, htr2⟩
  rw [hx0_1] at hx19_2; rw [hx2_1] at hx24_2; rw [hx29_1] at hx29_2
  have hP2' :
      (selfA ↦₆₄ polyEncoderTagVal st.sending_ct1) ∗ statesRecvRoAt b ∗
      (chunkedCt1SampledBodyAt A (selfA + 8#64) st ∗
        memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0) ⊢
      memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ct1Sampled st) ∗
      messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 := by
    dsimp only [chunkedStatesAt]
    rw [chunkedCt1SampledAt_eq_tag_body A selfA st]; exact Entails.of_eq (by ac_rfl)
  refine SepWPp.weaken_pre hP2' ?_
  exact states_recv_arm_ct1Sampled hb hA hdealloc hmemcpy hdec_call hrecv_ek hsendCt2 hsendCt2Enc
    s0 s2 outA selfA msgA st msg R hsort
    (fun _ decoded uc_ek _ _ _ hrek =>
      ct1Sampled_send_ct2_ok_of_recv_ek_ok K st decoded uc_ek hes hct1 hmac hrek)
    hsp0_align hpc2 hrun2 hsp2
    hx1_2 hx12_2 hx19_2 hx21_2 hx24_2 hx28_2 hx29_2 (htr2.trans htr1)

end CryptoVerification.SpqrV1.States.Recv
