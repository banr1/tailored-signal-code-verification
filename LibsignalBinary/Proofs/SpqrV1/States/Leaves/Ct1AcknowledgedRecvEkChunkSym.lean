/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2Defs
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpoch
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.Common
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::send_ct::Ct1Acknowledged>::recv_ek_chunk` (`0x5e9c8`): Symbolic Helpers

**Checked by Lean.**

Instruction decode tree, pure inversion lemmas, framed call rules, stack/word layout helpers,
shared epilogue (`ct1_ack_recv_ek_epilogue_244`), error branch (`ct1_ack_recv_ek_err_branch`),
and `decoded? = none` branch (`ct1_ack_recv_ek_none_branch`) for `<Ct1Acknowledged>::recv_ek_chunk`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.Leaves

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16 CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncodeBytes CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop CryptoVerification.SpqrV1.Alloc CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [-arm64_norm] Expand.sp_sub_496_eq_esp Expand.sp_add_neg496_eq_esp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local arm64_norm] bv_sub_add_lit bv_sub_sub BitVec.sub_add_cancel BitVec.toNat_zero

/-! ## 1. Instruction Decode Tree (`0x5e9c8..0x5ec2c`) -/

gen_decodes libsignalSessionCode_tree spqrCt1AcknowledgedRecvEkChunkBin [ 0x595d0 → 0x59834 ]

/-! ## 2. Pure Unfolding & Inversion Lemmas -/

attribute [local irreducible] addChunkTotal

theorem ct1_acknowledged_recv_ek_chunk_elim {F : ShaCompress} {K : MlKem}
    {st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F)} {chunk : Chunk}
    {res : Except Error (Chunked.SendCt.Ct1AcknowledgedRecvChunk spqrPolyApi (spqrAuthApi F))}
    (h16 : st.receiving_ek.pts.length = 16)
    (h : st.recv_ek_chunk K st.uc.epoch chunk = StatesResult.ofError res) :
    let receivingEk := addChunkTotal st.receiving_ek chunk
    ∃ decoded? : Option Bytes,
      spqrPolyApi.decoded_message receivingEk = .ok decoded? ∧
      match decoded? with
      | none => res = .ok (.stillReceiving { uc := st.uc, receiving_ek := receivingEk })
      | some decoded =>
        ∃ ucRes : Except Error (Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F)),
          st.uc.recv_ek K st.uc.epoch decoded = StatesResult.ofError ucRes ∧
          match ucRes with
          | .error e => res = .error e
          | .ok uc1 =>
            ∃ outUc ct2 mac sendingCt2,
              uc1.send_ct2 K = .ok (outUc, ct2, mac) ∧
              Chunked.SendCt.send_ct2_encoder spqrPolyApi ct2 mac = .ok sendingCt2 ∧
              res = .ok (.done { uc := outUc, sending_ct2 := sendingCt2 }) := by
  unfold Chunked.SendCt.Ct1Acknowledged.recv_ek_chunk at h
  have hadd_eq : spqrPolyApi.add_chunk st.receiving_ek chunk =
      .ok (addChunkTotal st.receiving_ek chunk) := by
    dsimp only [spqrPolyApi]; rw [addChunk_eq_ok st.receiving_ek chunk h16]; rfl
  rw [hadd_eq] at h; dsimp only [StatesResult.ofPanic, Bind.bind, Except.bind] at h
  cases hdm : spqrPolyApi.decoded_message (addChunkTotal st.receiving_ek chunk) with
  | error p =>
    rw [hdm] at h; dsimp only [StatesResult.ofPanic, Bind.bind, Except.bind] at h
    cases res <;> nomatch h
  | ok decoded? =>
    refine ⟨decoded?, hdm, ?_⟩
    rw [hdm] at h; dsimp only [StatesResult.ofPanic, Bind.bind, Except.bind] at h
    cases decoded? with
    | none =>
      dsimp only at h
      cases res with
      | ok v =>
        dsimp only [StatesResult.ofError] at h; exact congrArg Except.ok (Except.ok.inj h).symm
      | error e => dsimp only [StatesResult.ofError] at h; nomatch h
    | some decoded =>
      dsimp only at h
      cases huc : st.uc.recv_ek K st.uc.epoch decoded with
      | error se =>
        rw [huc] at h; dsimp only [Bind.bind, Except.bind] at h
        cases res with
        | ok v => dsimp only [StatesResult.ofError] at h; nomatch h
        | error e =>
          dsimp only [StatesResult.ofError] at h
          have hse : se = .err e := Except.error.inj h; subst hse; exact ⟨.error e, huc, rfl⟩
      | ok uc1 =>
        rw [huc] at h; dsimp only [Bind.bind, Except.bind] at h; refine ⟨.ok uc1, huc, ?_⟩
        cases hsc : uc1.send_ct2 K with
        | error p =>
          rw [hsc] at h; dsimp only [StatesResult.ofPanic, Bind.bind, Except.bind] at h
          cases res <;> nomatch h
        | ok val =>
          rcases val with ⟨outUc, ct2, mac⟩
          rw [hsc] at h; dsimp only [StatesResult.ofPanic, Bind.bind, Except.bind] at h
          cases henc : Chunked.SendCt.send_ct2_encoder spqrPolyApi ct2 mac with
          | error p =>
            rw [henc] at h; dsimp only [StatesResult.ofPanic, Bind.bind, Except.bind] at h
            cases res <;> nomatch h
          | ok sendingCt2 =>
            rw [henc] at h; dsimp only [StatesResult.ofPanic, Bind.bind, Except.bind] at h
            cases res with
            | error e => nomatch h
            | ok v =>
              dsimp only [StatesResult.ofError] at h
              exact ⟨outUc, ct2, mac, sendingCt2, hsc, henc,
                congrArg Except.ok (Except.ok.inj h).symm⟩

def pack64_8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : BitVec 64 :=
  b7 ++ (b6 ++ (b5 ++ (b4 ++ (b3 ++ (b2 ++ (b1 ++ b0))))))

theorem unpack64_pack64_8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    unpack64 (pack64_8 b0 b1 b2 b3 b4 b5 b6 b7) = [b0, b1, b2, b3, b4, b5, b6, b7] := by
  unfold unpack64 pack64_8; simp only [List.cons.injEq, and_true]
  refine ⟨by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel,
    by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel⟩

theorem exists_word_of_length_add_8 {bs : List (BitVec 8)} {k : Nat} (h : bs.length = k + 8) :
    ∃ w : BitVec 64, ∃ rest : List (BitVec 8), rest.length = k ∧ bs = unpack64 w ++ rest := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, rest⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try (simp only [List.length_cons, List.length_nil] at h; omega)
  refine ⟨pack64_8 b0 b1 b2 b3 b4 b5 b6 b7, rest, by simp only [List.length_cons] at h; omega, ?_⟩
  rw [unpack64_pack64_8]; rfl

theorem exists_words8_of_length_64 {bs : List (BitVec 8)} (h : bs.length = 64) :
    ∃ d0 d1 d2 d3 d4 d5 d6 d7 : BitVec 64, bs = wordsBytes [d0, d1, d2, d3, d4, d5, d6, d7] := by
  obtain ⟨d0, r1, h1, rfl⟩ := exists_word_of_length_add_8 (k := 56) h
  obtain ⟨d1, r2, h2, rfl⟩ := exists_word_of_length_add_8 (k := 48) h1
  obtain ⟨d2, r3, h3, rfl⟩ := exists_word_of_length_add_8 (k := 40) h2
  obtain ⟨d3, r4, h4, rfl⟩ := exists_word_of_length_add_8 (k := 32) h3
  obtain ⟨d4, r5, h5, rfl⟩ := exists_word_of_length_add_8 (k := 24) h4
  obtain ⟨d5, r6, h6, rfl⟩ := exists_word_of_length_add_8 (k := 16) h5
  obtain ⟨d6, r7, h7, rfl⟩ := exists_word_of_length_add_8 (k := 8) h6
  obtain ⟨d7, r8, h8, rfl⟩ := exists_word_of_length_add_8 (k := 0) h7
  have hr8 : r8 = [] := List.eq_nil_of_length_eq_zero h8; subst hr8
  exact ⟨d0, d1, d2, d3, d4, d5, d6, d7, rfl⟩

theorem polyDecoderAt_extract_336_64 (A : RustAlloc) (a : BitVec 64) (dec : PolyDecoder) :
    polyDecoderAt A a dec ⊢
      ∃∗ bs1 : List (BitVec 8),
      ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64, ∃∗ d3 : BitVec 64,
      ∃∗ d4 : BitVec 64, ∃∗ d5 : BitVec 64, ∃∗ d6 : BitVec 64, ∃∗ d7 : BitVec 64,
        ⌜bs1.length = 336⌝ ∗ (a ↦ₛ bs1) ∗
        wordsAt (a + 336#64) [d0, d1, d2, d3, d4, d5, d6, d7] ∗
        relocatedHeap (fun dst => polyDecoderAt A dst dec)
          (bs1 ++ wordsBytes [d0, d1, d2, d3, d4, d5, d6, d7]) := by
  refine Entails.trans (Relocatable.of_polyDecoderAt A dec a) ?_
  apply Entails.sepExists_elim; intro bs; apply Entails.pure_left; intro hlen
  have h1 : (bs.take 336).length = 336 := by simp [hlen]
  have h2 : (bs.drop 336).length = 64 := by simp [hlen]
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, hd⟩ := exists_words8_of_length_64 h2
  have hbs : bs = bs.take 336 ++ wordsBytes [d0, d1, d2, d3, d4, d5, d6, d7] := by
    rw [← hd, List.take_append_drop]
  refine Entails.sepExists_right (bs.take 336) (Entails.sepExists_right d0 (Entails.sepExists_right d1
    (Entails.sepExists_right d2 (Entails.sepExists_right d3 (Entails.sepExists_right d4
      (Entails.sepExists_right d5 (Entails.sepExists_right d6 (Entails.sepExists_right d7 ?_))))))))
  refine Entails.pure_right h1 ?_; conv_lhs => rw [hbs]
  rw [pointsToBytes_append a (bs.take 336) (wordsBytes [d0, d1, d2, d3, d4, d5, d6, d7]), h1,
      ← wordsAt_eq_pointsToBytes]
  exact Entails.of_eq (by ac_rfl)

/-! ## 3. Framed Call Rules (`call_addChunk_mid`, `call_decodedMessage`, `call_unchunkedRecvEk`) -/

/-- Framed call rule for `addChunkSpec A` (`0x6c420`) continuing to `next_pc`. -/
theorem call_addChunk_mid {A : RustAlloc} {prog : Program} {entry ret_pc next_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (addChunkSpec A))
    (decA chunkA : BitVec 64) (dec : PolyDecoder) (chunk : Chunk)
    (hsorted : PolyDecoderStrictSorted dec)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = decA) (hx1 : s.readReg64 Reg.x1 = chunkA)
    (hsplit : P = (polyDecoderAt A decA dec ∗ chunkAt chunkA chunk ∗
      A.pool ∗ stackAt sp_call addChunkStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      PolyDecoderStrictSorted (addChunkTotal dec chunk) →
      SepWP prog next_pc sf
        ((polyDecoderAt A decA (addChunkTotal dec chunk) ∗ chunkAt chunkA chunk ∗
          A.pool ∗ stackAt sp_call addChunkStack) ∗ Frame)
        (fun sm Pm =>
          SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
            (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
              (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)))) :
    SepWP prog entry s P
      (fun sm Pm =>
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R))) := by
  apply SepWP.done hpc hrun
  refine SepWPp.call hcall (x := ⟨decA, chunkA, dec, chunk⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ hmem => ?_) (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm; rw [hsplit] at hm; dsimp only [addChunkSpec]; rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hsorted⟩, hm⟩
  · rw [← sepConj_assoc]
    refine allowPanic_frame (fun ⟨haf, htr_sub⟩ => ?_) hmem
    unfold allocFailedIn at haf ⊢; rw [htrace] at haf htr_sub; exact ⟨haf, htr_sub⟩
  · dsimp only [addChunkSpec]; rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun ⟨htr, hsorted'⟩ => ?_
    apply SepWPp.of_sepWP (mid := next_pc)
    have hassoc :
        (polyDecoderAt A decA (addChunkTotal dec chunk) ∗ chunkAt chunkA chunk ∗
          A.pool ∗ stackAt sp_call addChunkStack) ∗ Frame =
        (polyDecoderAt A decA (addChunkTotal dec chunk) ∗
          (chunkAt chunkA chunk ∗ (A.pool ∗ stackAt sp_call addChunkStack))) ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) hsorted'

/-- Framed call rule for `polyDecoderDecodedMessageSpec A b` (`0x6bb80`). -/
theorem ct1AckEk_call_decodedMessage {A : RustAlloc} {b : BitVec 64} {prog : Program}
    {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (polyDecoderDecodedMessageSpec A b))
    (hb : b &&& 0xfff#64 = 0#64)
    (outA decA : BitVec 64) (dec : PolyDecoder) (outMsg : Option Bytes)
    (hsorted : PolyDecoderStrictSorted dec) (hdm : spqrPolyApi.decoded_message dec = .ok outMsg)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx8 : s.readReg64 Reg.x8 = outA) (hx0 : s.readReg64 Reg.x0 = decA)
    (hsplit : P = (memRegion outA 24 ∗ polyDecoderAt A decA dec ∗
      tokenInitAt b ∗ reduceTableAt b ∗ A.pool ∗ stackAt sp_call polyDecoderDecodedMessageStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWPp prog (s0.readReg64 Reg.lr) sf
        ((optVecU8At A outA outMsg ∗ polyDecoderAt A decA dec ∗
          tokenInitAt b ∗ reduceTableAt b ∗ A.pool ∗ stackAt sp_call polyDecoderDecodedMessageStack) ∗ Frame)
        post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R))) :
    SepWP prog entry s P
      (fun sm Pm =>
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R))) := by
  apply SepWP.done hpc hrun
  refine SepWPp.call hcall (x := ⟨outA, decA, dec, outMsg⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ hmem => ?_) (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm; rw [hsplit] at hm; dsimp only [polyDecoderDecodedMessageSpec]; rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hb, hx8, hx0, hsorted, hdm⟩, hm⟩
  · rw [← sepConj_assoc]
    refine allowPanic_frame (fun ⟨haf, htr_sub⟩ => ?_) hmem
    unfold allocFailedIn at haf ⊢; rw [htrace] at haf htr_sub; exact ⟨haf, htr_sub⟩
  · dsimp only [polyDecoderDecodedMessageSpec]; rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    have hassoc :
        (optVecU8At A outA outMsg ∗ polyDecoderAt A decA dec ∗
          tokenInitAt b ∗ reduceTableAt b ∗ A.pool ∗ stackAt sp_call polyDecoderDecodedMessageStack) ∗ Frame =
        (optVecU8At A outA outMsg ∗
          (polyDecoderAt A decA dec ∗
            (tokenInitAt b ∗ (reduceTableAt b ∗
              (A.pool ∗ stackAt sp_call polyDecoderDecodedMessageStack))))) ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace)

/-- Framed call rule for `unchunkedCt1SentRecvEkSpec A F K` (`0x5dac0`). -/
theorem call_unchunkedRecvEk {A : RustAlloc} {F : ShaCompress} {K : MlKem} {prog : Program}
    {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (unchunkedCt1SentRecvEkSpec A F K))
    (outA stA ekA : BitVec 64)
    (st : Unchunked.SendCt.Ct1Sent (spqrAuthApi F)) (ek : Bytes)
    (ucRes : Except Error (Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F)))
    (hrecv : st.recv_ek K st.epoch ek = StatesResult.ofError ucRes)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = outA) (hx1 : s.readReg64 Reg.x1 = stA)
    (hx2 : s.readReg64 Reg.x2 = st.epoch) (hx3 : s.readReg64 Reg.x3 = ekA)
    (hsplit : P = (memRegion outA 128 ∗ unchunkedCt1SentAt A stA st ∗
      vecU8 A ekA ek ∗ A.pool ∗ stackAt sp_call unchunkedRecvEkStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog target_pc sf
        ((unchunkedCt1SentRecvEkResAt A outA ucRes ∗ memRegion stA 128 ∗
          memRegion ekA 24 ∗ A.pool ∗ stackAt sp_call unchunkedRecvEkStack) ∗ Frame)
        post) :
    SepWP prog target_pc s P post := by
  rw [hsplit]
  refine SepWP.call_subroutine_frame hcall (x := ⟨outA, stA, ekA, st, ek, ucRes⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm; dsimp only [unchunkedCt1SentRecvEkSpec]; rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hx2, hx3, hrecv⟩, hm⟩
  · dsimp only [unchunkedCt1SentRecvEkSpec]; rw [hsp, sepConj_assoc]
    refine SepWP.pure_elim fun htr => ?_
    have hassoc :
        (unchunkedCt1SentRecvEkResAt A outA ucRes ∗ memRegion stA 128 ∗
          memRegion ekA 24 ∗ A.pool ∗ stackAt sp_call unchunkedRecvEkStack) ∗ Frame =
        (unchunkedCt1SentRecvEkResAt A outA ucRes ∗
          (memRegion stA 128 ∗
            (memRegion ekA 24 ∗ (A.pool ∗ stackAt sp_call unchunkedRecvEkStack)))) ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace)

/-- Framed `memcpy` call rule for raw byte slices `(src ↦ₛ bs)`, producing `(dst ↦ₛ bs) ∗ (src ↦ₛ bs)`. -/
theorem call_memcpy_bytes_cs {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry sessionMemcpyRegionSpec)
    (dst src : BitVec 64) (bs : List (BitVec 8)) {n : Nat} (hlen : bs.length = n)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = dst) (hx1 : s.readReg64 Reg.x1 = src)
    (hx2 : (s.readReg64 Reg.x2).toNat = n)
    (hsplit : P = (memRegion dst n ∗ (src ↦ₛ bs)) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog target_pc sf (((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  rw [hsplit]
  refine SepWP.call_subroutine_frame hcall (x := (dst, src, bs)) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm; dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [hlen, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩; simpa only [sepConj_assoc] using hm
  · dsimp only [sessionMemcpyRegionSpec]; rw [sepConj_assoc]
    refine SepWP.pure_elim fun ⟨_, htr⟩ => ?_
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace)

/-! ## 4. Stack Layout & Saved Register Helpers -/

/-- Saved callee-saved registers at `[s0.sp - 64#64 .. s0.sp)` in `<Ct1Acknowledged>::recv_ek_chunk`. -/
def ct1AckSavedRegs (s0 : State) : SepProp :=
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)

theorem ct1AckSavedRegs_entails_memRegion_64 (s0 : State) :
    ct1AckSavedRegs s0 ⊢ memRegion (s0.sp - 64#64) 64 := by
  unfold ct1AckSavedRegs
  have heq :
      (((s0.sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) =
      wordsAt (s0.sp - 64#64)
        [s0.readReg64 .fp, s0.readReg64 .lr, s0.readReg64 .x28, s0.readReg64 .x23,
         s0.readReg64 .x22, s0.readReg64 .x21, s0.readReg64 .x20, s0.readReg64 .x19] := by
    simp only [wordsAt_8, arm64_norm]
  rw [heq]; exact wordsAt_entails_memRegion _ (s0.sp - 64#64) 64 rfl

theorem stackAt_1760_entry_split (sp : BitVec 64) :
    stackAt sp ct1AcknowledgedRecvEkChunkStack =
      stackAt (sp - 1760#64) sendCt2EncoderStack ∗
      memRegion (sp - 1760#64) 128 ∗ memRegion (sp - 1632#64) 8 ∗
      memRegion (sp - 1624#64) 400 ∗ memRegion (sp - 1224#64) 24 ∗
      memRegion (sp - 1200#64) 1136 ∗ memRegion (sp - 64#64) 64 := by
  change memRegion (sp - 19216#64) 19216 =
    memRegion (sp - 1760#64 - 17456#64) 17456 ∗ _
  have hsub : sp - 1760#64 - 17456#64 = sp - 19216#64 := by bv_omega
  rw [hsub,
      ProofLib.memRegion_split' (b := sp - 19216#64) (n := 17456) (k := 1760) (b' := sp - 1760#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 1760#64) (n := 128) (k := 1632) (b' := sp - 1632#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 1632#64) (n := 8) (k := 1624) (b' := sp - 1624#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 1624#64) (n := 400) (k := 1224) (b' := sp - 1224#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 1224#64) (n := 24) (k := 1200) (b' := sp - 1200#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 1200#64) (n := 1136) (k := 64) (b' := sp - 64#64) rfl (by bv_omega) (by decide)]

theorem stackAt_1760_exit_rejoin (s0 : State) :
    stackAt (s0.sp - 1760#64) sendCt2EncoderStack ∗
      memRegion (s0.sp - 1760#64) 136 ∗ memRegion (s0.sp - 1624#64) 400 ∗
      memRegion (s0.sp - 1224#64) 1160 ∗ ct1AckSavedRegs s0 ⊢
    stackAt s0.sp ct1AcknowledgedRecvEkChunkStack := by
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (ct1AckSavedRegs_entails_memRegion_64 s0))))) ?_
  change memRegion (s0.sp - 1760#64 - 17456#64) 17456 ∗
    (memRegion (s0.sp - 1760#64) 136 ∗
      (memRegion (s0.sp - 1624#64) 400 ∗
        (memRegion (s0.sp - 1224#64) 1160 ∗ memRegion (s0.sp - 64#64) 64))) ⊢
    memRegion (s0.sp - 19216#64) 19216
  have hsub : s0.sp - 1760#64 - 17456#64 = s0.sp - 19216#64 := by bv_omega
  rw [hsub,
      ← ProofLib.memRegion_split' (b := s0.sp - 1224#64) (n := 1160) (k := 64) (b' := s0.sp - 64#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := s0.sp - 1624#64) (n := 400) (k := 1224) (b' := s0.sp - 1224#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := s0.sp - 1760#64) (n := 136) (k := 1624) (b' := s0.sp - 1624#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := s0.sp - 19216#64) (n := 17456) (k := 1760) (b' := s0.sp - 1760#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem stackAt_sendCt2Encoder_eq_addChunk (fsp : BitVec 64) :
    stackAt fsp sendCt2EncoderStack =
      memRegion (fsp - 17456#64) 13152 ∗ stackAt fsp addChunkStack := by
  change memRegion (fsp - 17456#64) 17456 = memRegion (fsp - 17456#64) 13152 ∗ memRegion (fsp - 4304#64) 4304
  exact ProofLib.memRegion_split' (b := fsp - 17456#64) (n := 13152) (k := 4304) (b' := fsp - 4304#64) rfl (by bv_omega) (by decide)

theorem stackAt_sendCt2Encoder_eq_decodedMessage (fsp : BitVec 64) :
    stackAt fsp sendCt2EncoderStack = memRegion (fsp - 17456#64) 400 ∗ stackAt fsp polyDecoderDecodedMessageStack := by
  change memRegion (fsp - 17456#64) 17456 = memRegion (fsp - 17456#64) 400 ∗ memRegion (fsp - 17056#64) 17056
  exact ProofLib.memRegion_split' (b := fsp - 17456#64) (n := 400) (k := 17056) (b' := fsp - 17056#64) rfl (by bv_omega) (by decide)

theorem stackAt_sendCt2Encoder_eq_unchunkedRecvEk (fsp : BitVec 64) :
    stackAt fsp sendCt2EncoderStack = memRegion (fsp - 17456#64) 864 ∗ stackAt fsp unchunkedRecvEkStack := by
  change memRegion (fsp - 17456#64) 17456 = memRegion (fsp - 17456#64) 864 ∗ memRegion (fsp - 16592#64) 16592
  exact ProofLib.memRegion_split' (b := fsp - 17456#64) (n := 864) (k := 16592) (b' := fsp - 16592#64) rfl (by bv_omega) (by decide)

theorem stackAt_sendCt2Encoder_eq_unchunkedSendCt2 (fsp : BitVec 64) :
    stackAt fsp sendCt2EncoderStack = memRegion (fsp - 17456#64) 736 ∗ stackAt fsp unchunkedSendCt2Stack := by
  change memRegion (fsp - 17456#64) 17456 = memRegion (fsp - 17456#64) 736 ∗ memRegion (fsp - 16720#64) 16720
  exact ProofLib.memRegion_split' (b := fsp - 17456#64) (n := 736) (k := 16720) (b' := fsp - 16720#64) rfl (by bv_omega) (by decide)

theorem stackAt_sendCt2Encoder_eq_allocHook (fsp : BitVec 64) :
    stackAt fsp sendCt2EncoderStack = memRegion (fsp - 17456#64) 13360 ∗ stackAt fsp allocHookStack := by
  change memRegion (fsp - 17456#64) 17456 = memRegion (fsp - 17456#64) 13360 ∗ memRegion (fsp - 4096#64) 4096
  exact ProofLib.memRegion_split' (b := fsp - 17456#64) (n := 13360) (k := 4096) (b' := fsp - 4096#64) rfl (by bv_omega) (by decide)

theorem stackAt_sendCt2Encoder_eq_dropSortedSetPt16 (fsp : BitVec 64) :
    stackAt fsp sendCt2EncoderStack = memRegion (fsp - 17456#64) 13328 ∗ stackAt fsp dropGluePoly16Stack := by
  change memRegion (fsp - 17456#64) 17456 = memRegion (fsp - 17456#64) 13328 ∗ memRegion (fsp - 4128#64) 4128
  exact ProofLib.memRegion_split' (b := fsp - 17456#64) (n := 13328) (k := 4128) (b' := fsp - 4128#64) rfl (by bv_omega) (by decide)

/-- Framed call rule for `dropGlueSortedSetPt16Spec A` (`0x4bd18`). -/
theorem call_dropGlueSortedSetPt16 {A : RustAlloc} {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (dropGlueSortedSetPt16Spec A))
    (arrA : BitVec 64) (vecs : List (List Pt))
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = arrA) (hlen : vecs.length = NUM_POLYS)
    (hsplit : P = (vecPtListOf A arrA vecs ∗ A.pool ∗ stackAt sp_call dropGluePoly16Stack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog target_pc sf
        ((memRegion arrA polyArrayBytes ∗ A.pool ∗ stackAt sp_call dropGluePoly16Stack) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  rw [hsplit]
  refine SepWP.call_subroutine_frame hcall (x := ⟨arrA, vecs⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm; dsimp only [dropGlueSortedSetPt16Spec]; rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hlen⟩, hm⟩
  · dsimp only [dropGlueSortedSetPt16Spec]; rw [hsp, sepConj_assoc]
    refine SepWP.pure_elim fun htr => ?_
    have hassoc :
        (memRegion arrA polyArrayBytes ∗ A.pool ∗ stackAt sp_call dropGluePoly16Stack) ∗ Frame =
        (memRegion arrA polyArrayBytes ∗ (A.pool ∗ stackAt sp_call dropGluePoly16Stack)) ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace)

theorem fold_ct1AckSavedRegs (s0 : State) :
    (((s0.sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
     ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
     ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
     ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ⊢
    ct1AckSavedRegs s0 := Entails.refl _

/-- Shared epilogue at `+0x248..+0x260` (starting right after `bl 0x4bd18` jumps to the callee):
    calls `drop_glue::<[SortedSet<Pt>; 16]>` (`0x4bd18`) on `receivingEk` at `s0.sp - 1624#64`,
    restores callee-saved registers from `ct1AckSavedRegs s0`, and returns. -/
theorem ct1_ack_recv_ek_epilogue_244 {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hsortedSet16_raw : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr ct1AcknowledgedRecvEkChunkName + 18446744073709474640#64)
      (dropGlueSortedSetPt16Spec A))
    (outA stA chunkA : BitVec 64)
    (chunk : Chunk) (receivingEk : PolyDecoder)
    (res : Except Error (Chunked.SendCt.Ct1AcknowledgedRecvChunk spqrPolyApi (spqrAuthApi F)))
    (s0 s : State) (R : SepProp)
    (hsp0_align : s0.spAligned = true)
    (hpc : s.pc = (leavesProgAtExt b ext).fnAddr ct1AcknowledgedRecvEkChunkName + 18446744073709474640#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1760#64)
    (hlr : s.readReg64 Reg.lr = (leavesProgAtExt b ext).fnAddr ct1AcknowledgedRecvEkChunkName + 588#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = s0.sp - 1624#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5))
    (hx25 : s.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5))
    (hx26 : s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5))
    (hx27 : s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (leavesProgAtExt b ext) (s0.readReg64 Reg.lr) s
      (ct1AcknowledgedRecvEkChunkResAt A outA res ∗
        memRegion stA 528 ∗ chunkAt chunkA chunk ∗
        unchunkedSendCt2RoAt b ∗ tokenInitAt b ∗ reduceTableAt b ∗
        polyDecoderAt A (s0.sp - 1624#64) receivingEk ∗
        memRegion (s0.sp - 1760#64) 136 ∗ memRegion (s0.sp - 1224#64) 1160 ∗
        ct1AckSavedRegs s0 ∗ A.pool ∗ stackAt (s0.sp - 1760#64) sendCt2EncoderStack)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (⌜sf.trace = s0.trace⌝ ∗
            ct1AcknowledgedRecvEkChunkResAt A outA res ∗ memRegion stA 528 ∗
            chunkAt chunkA chunk ∗ unchunkedSendCt2RoAt b ∗
            tokenInitAt b ∗ reduceTableAt b ∗
            A.pool ∗ stackAt s0.sp ct1AcknowledgedRecvEkChunkStack) ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  have hfsp_align : ((s0.sp - 1760#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 1760#64 hsp0_align (by decide)
  code_fetches libsignalSessionCode spqrCt1AcknowledgedRecvEkChunkBin b
    (Rust.withPanics ext) ct1AcknowledgedRecvEkChunk_fnOff 366032 612
  dsimp only [leavesProgAtExt, ct1AcknowledgedRecvEkChunkName, BitVec.ofNat_eq_ofNat] at hsortedSet16_raw hpc hlr ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::send_ct::Ct1Acknowledged>::recv_ek_chunk" = entry
  examples_hide_fetches
  refine SepWP.fold (polyDecoderAt_entails_vecs_tail A (s0.sp - 1624#64) receivingEk)
    (by sep_focus) ?_
  wp_pull_exists; rename_i vecs
  wp_focus_pure; intro hvecs_len
  refine SepWP.fold (Entails.of_eq (stackAt_sendCt2Encoder_eq_dropSortedSetPt16 (s0.sp - 1760#64)))
    (by sep_focus) ?_
  refine call_dropGlueSortedSetPt16 hsortedSet16_raw (s0.sp - 1624#64) vecs
    (ret_pc := entry + 588#64) (sp_call := s0.sp - 1760#64) (s0 := s0)
    (by simp only [arm64_norm, hpc]) (by simpa only [arm64_norm] using hrun)
    (by simp only [State.sp, arm64_norm, hsp]) hfsp_align
    (by simp only [Reg.lr, arm64_norm, hlr]) (by simp only [arm64_norm, htr])
    (by simp only [Reg.x0, arm64_norm, hx0]) hvecs_len (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 htr1 => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [arm64_norm, hx24, hx25, hx26, hx27, hvregs] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
  refine SepWP.fold (polyDecoder_post_join (s0.sp - 1624#64)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (stackAt_sendCt2Encoder_eq_dropSortedSetPt16 (s0.sp - 1760#64)).symm)
    (by sep_focus) ?_
  wp_conv_pre => unfold ct1AckSavedRegs
  wp_steps
  refine SepWP.fold (fold_ct1AckSavedRegs s0) (by sep_focus) ?_
  refine SepWP.fold (stackAt_1760_exit_rejoin s0) (by sep_focus) ?_
  wp_done

/-! ## 5. Branch 1: `uc.recv_ek = .error e` (`+0x098..+0x0b4`, `+0x22c..+0x244`, then `+0x248`) -/

theorem ct1AckEk_sepWP_congr_pre {prog : Program} {target_pc : BitVec 64} {s : State}
    {P1 P2 : SepProp} {post1 post2 : State → SepProp → Prop}
    (h : SepWP prog target_pc s P2 post2) (heqP : P1 = P2) (heqPost : post1 = post2) :
    SepWP prog target_pc s P1 post1 := heqP ▸ heqPost ▸ h

theorem cells_2_unfold (a : BitVec 64) :
    memRegion a 16 ⊢ ∃∗ v0, ∃∗ v1, (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) := by
  rw [ProofLib.memRegion_cells a 2 (by decide), ProofLib.cells_succ]
  simp only [cells_succ_off, ProofLib.cells_zero, sepConj_emp, sepExists_sepConj_right]
  exact Entails.refl _

theorem cells_3_unfold (a : BitVec 64) :
    memRegion a 24 ⊢
      ∃∗ v0, ∃∗ v1, ∃∗ v2, (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) := by
  rw [ProofLib.memRegion_cells a 3 (by decide), ProofLib.cells_succ]
  simp only [cells_succ_off, ProofLib.cells_zero, sepConj_emp, sepExists_sepConj_right,
    show (8#64 + 8#64 : BitVec 64) = 16#64 from rfl]
  exact Entails.refl _

theorem byte_12_and_7_to_word64 (a : BitVec 64) :
    (a ↦₈ 12#8) ∗ memRegion (a + 1#64) 7 ⊢
      ∃∗ w : BitVec 64,
        ⌜∀ dst : BitVec 64, (dst ↦₆₄ w) ⊢ (dst ↦₈ 12#8) ∗ memRegion (dst + 1#64) 7⌝ ∗ (a ↦₆₄ w) := by
  rw [memRegion_eq_exists_bytes (a + 1#64) 7 (by decide), sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro bs; rw [sepConj_left_comm (a ↦₈ 12#8)]
  apply Entails.pure_left; intro hlen
  obtain ⟨w, rest, hrest0, heq⟩ := exists_word_of_length_add_8 (k := 0) (by simp [hlen] : (12#8 :: bs).length = 0 + 8)
  have hnil : rest = [] := List.eq_nil_of_length_eq_zero hrest0
  subst hnil; rw [List.append_nil] at heq
  refine Entails.sepExists_right w (Entails.pure_right (fun dst => ?_) ?_)
  · rw [pointsTo64_eq_pointsToBytes, ← heq, pointsToBytes_cons, ← hlen]
    exact sepConj_mono_right (pointsToBytes_entails_memRegion (dst + 1#64) bs)
  · rw [pointsTo64_eq_pointsToBytes, ← heq, pointsToBytes_cons]; exact Entails.refl _

theorem unchunkedRecvEk_err_expose (A : RustAlloc) {F : ShaCompress}
    (sp : BitVec 64) (e : Error) :
    unchunkedCt1SentRecvEkResAt A (sp - 592#64) (Except.error e : Except Error (Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F))) ⊢
      ∃∗ w1 : BitVec 64,
        ⌜∀ dst : BitVec 64, (dst ↦₆₄ w1) ⊢ (dst ↦₈ 12#8) ∗ memRegion (dst + 1#64) 7⌝ ∗
        ((sp - 592#64) ↦₆₄ noneCap) ∗ ((sp - 584#64) ↦₆₄ w1) ∗
        memRegion (sp - 576#64) 16 ∗ memRegion (sp - 560#64) 96 := by
  dsimp only [unchunkedCt1SentRecvEkResAt]
  have h8 : (sp - 592#64) + 8#64 = sp - 584#64 := by bv_omega
  have h9 : (sp - 592#64) + 9#64 = (sp - 584#64) + 1#64 := by bv_omega
  rw [h8, h9,
      ProofLib.memRegion_split' (b := (sp - 584#64) + 1#64) (n := 7) (k := 112) (b' := sp - 576#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 576#64) (n := 16) (k := 96) (b' := sp - 560#64) rfl (by bv_omega) (by decide)]
  have hassoc :
      ((sp - 592#64) ↦₆₄ noneCap) ∗ ((sp - 584#64) ↦₈ 12#8) ∗
        (memRegion ((sp - 584#64) + 1#64) 7 ∗ (memRegion (sp - 576#64) 16 ∗ memRegion (sp - 560#64) 96)) =
      (((sp - 584#64) ↦₈ 12#8) ∗ memRegion ((sp - 584#64) + 1#64) 7) ∗
        (((sp - 592#64) ↦₆₄ noneCap) ∗ memRegion (sp - 576#64) 16 ∗ memRegion (sp - 560#64) 96) := by ac_rfl
  rw [hassoc]
  refine Entails.trans (sepConj_mono_left (byte_12_and_7_to_word64 (sp - 584#64))) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro w1
  refine Entails.sepExists_right w1 ?_
  rw [sepConj_assoc]; apply Entails.pure_left; intro hw1
  exact Entails.pure_right hw1 (Entails.of_eq (by ac_rfl))

theorem ct1Ack_err_outA_recompose (A : RustAlloc) {F : ShaCompress}
    (outA : BitVec 64) (e : Error) (w2 w3 : BitVec 64) :
    (outA ↦₆₄ 0xfffffffffffffffe#64) ∗ ((outA + 8#64) ↦₈ 12#8) ∗
      memRegion ((outA + 8#64) + 1#64) 7 ∗
      ((outA + 16#64) ↦₆₄ w2) ∗ ((outA + 24#64) ↦₆₄ w3) ∗ memRegion (outA + 32#64) 496 ⊢
    ct1AcknowledgedRecvEkChunkResAt A (F := F) outA (.error e) := by
  dsimp only [ct1AcknowledgedRecvEkChunkResAt]
  have hw23 : ((outA + 16#64) ↦₆₄ w2) ∗ ((outA + 24#64) ↦₆₄ w3) ⊢ memRegion (outA + 16#64) 16 := by
    have heq : (((outA + 16#64) ↦₆₄ w2) ∗ ((outA + 24#64) ↦₆₄ w3)) = wordsAt (outA + 16#64) [w2, w3] := by
      simp only [wordsAt, wordsAt_cons_off, wordsAt_nil, sepConj_emp, BitVec.add_assoc, arm64_norm]
    rw [heq]; exact wordsAt_entails_memRegion [w2, w3] (outA + 16#64) 16 rfl
  have hassoc :
      (outA ↦₆₄ 0xfffffffffffffffe#64) ∗ ((outA + 8#64) ↦₈ 12#8) ∗
        memRegion ((outA + 8#64) + 1#64) 7 ∗
        ((outA + 16#64) ↦₆₄ w2) ∗ ((outA + 24#64) ↦₆₄ w3) ∗ memRegion (outA + 32#64) 496 =
      (outA ↦₆₄ 0xfffffffffffffffe#64) ∗ ((outA + 8#64) ↦₈ 12#8) ∗
        memRegion ((outA + 8#64) + 1#64) 7 ∗
        (((outA + 16#64) ↦₆₄ w2) ∗ ((outA + 24#64) ↦₆₄ w3)) ∗ memRegion (outA + 32#64) 496 := by ac_rfl
  rw [hassoc]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hw23)))) ?_
  have h9 : (outA + 8#64) + 1#64 = outA + 9#64 := by bv_omega
  rw [h9,
      ← ProofLib.memRegion_split' (b := outA + 16#64) (n := 16) (k := 496) (b' := outA + 32#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := outA + 9#64) (n := 7) (k := 512) (b' := outA + 16#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem ct1Ack_err_stack_1160_rejoin (sp : BitVec 64) (u0 u1 u2 v0 v1 v2 v3 : BitVec 64) :
    memRegion (sp - 1224#64) 24 ∗
      (((sp - 1200#64) ↦₆₄ u0) ∗ ((sp - 1192#64) ↦₆₄ u1) ∗ ((sp - 1184#64) ↦₆₄ u2)) ∗
      memRegion (sp - 1176#64) 584 ∗
      (((sp - 592#64) ↦₆₄ v0) ∗ ((sp - 584#64) ↦₆₄ v1) ∗ ((sp - 576#64) ↦₆₄ v2) ∗ ((sp - 568#64) ↦₆₄ v3)) ∗
      memRegion (sp - 560#64) 96 ∗ memRegion (sp - 464#64) 400 ⊢
    memRegion (sp - 1224#64) 1160 := by
  have h3 : (((sp - 1200#64) ↦₆₄ u0) ∗ ((sp - 1192#64) ↦₆₄ u1) ∗ ((sp - 1184#64) ↦₆₄ u2)) ⊢
      memRegion (sp - 1200#64) 24 := by
    have heq : (((sp - 1200#64) ↦₆₄ u0) ∗ ((sp - 1192#64) ↦₆₄ u1) ∗ ((sp - 1184#64) ↦₆₄ u2)) =
        wordsAt (sp - 1200#64) [u0, u1, u2] := by
      simp only [wordsAt, wordsAt_cons_off, wordsAt_nil, sepConj_emp,
        show (8#64 + 8#64 : BitVec 64) = 16#64 from rfl, arm64_norm]
    rw [heq]; exact wordsAt_entails_memRegion _ (sp - 1200#64) 24 rfl
  have h4 : (((sp - 592#64) ↦₆₄ v0) ∗ ((sp - 584#64) ↦₆₄ v1) ∗ ((sp - 576#64) ↦₆₄ v2) ∗ ((sp - 568#64) ↦₆₄ v3)) ⊢
      memRegion (sp - 592#64) 32 := by
    have heq : (((sp - 592#64) ↦₆₄ v0) ∗ ((sp - 584#64) ↦₆₄ v1) ∗ ((sp - 576#64) ↦₆₄ v2) ∗ ((sp - 568#64) ↦₆₄ v3)) =
        wordsAt (sp - 592#64) [v0, v1, v2, v3] := by
      simp only [wordsAt, wordsAt_cons_off, wordsAt_nil, sepConj_emp,
        show (8#64 + 8#64 : BitVec 64) = 16#64 from rfl,
        show (16#64 + 8#64 : BitVec 64) = 24#64 from rfl, arm64_norm]
    rw [heq]; exact wordsAt_entails_memRegion _ (sp - 592#64) 32 rfl
  refine Entails.trans (sepConj_mono_right (sepConj_mono h3 (sepConj_mono_right (sepConj_mono_left h4)))) ?_
  rw [← ProofLib.memRegion_split' (b := sp - 560#64) (n := 96) (k := 400) (b' := sp - 464#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 592#64) (n := 32) (k := 496) (b' := sp - 560#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 1176#64) (n := 584) (k := 528) (b' := sp - 592#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 1200#64) (n := 24) (k := 1112) (b' := sp - 1176#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 1224#64) (n := 24) (k := 1136) (b' := sp - 1200#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

set_option maxHeartbeats 600000 in
theorem ct1_ack_recv_ek_err_branch {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hsortedSet16_raw : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr ct1AcknowledgedRecvEkChunkName + 18446744073709474640#64)
      (dropGlueSortedSetPt16Spec A))
    (outA stA chunkA : BitVec 64)
    (chunk : Chunk) (receivingEk : PolyDecoder) (e : Error)
    (res : Except Error (Chunked.SendCt.Ct1AcknowledgedRecvChunk spqrPolyApi (spqrAuthApi F)))
    (hres : res = .error e) (s0 s : State) (R : SepProp) (hsp0_align : s0.spAligned = true)
    (hpc : s.pc = (leavesProgAtExt b ext).fnAddr ct1AcknowledgedRecvEkChunkName + 152#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1760#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = outA)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5))
    (hx25 : s.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5))
    (hx26 : s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5))
    (hx27 : s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (leavesProgAtExt b ext) (s0.readReg64 Reg.lr) s
      (memRegion outA 528 ∗ memRegion stA 528 ∗ chunkAt chunkA chunk ∗
        unchunkedSendCt2RoAt b ∗ tokenInitAt b ∗ reduceTableAt b ∗
        polyDecoderAt A (s0.sp - 1624#64) receivingEk ∗
        memRegion (s0.sp - 1760#64) 136 ∗ memRegion (s0.sp - 1224#64) 632 ∗
        unchunkedCt1SentRecvEkResAt A (F := F) (s0.sp - 592#64) (.error e) ∗
        memRegion (s0.sp - 464#64) 400 ∗ ct1AckSavedRegs s0 ∗
        A.pool ∗ stackAt (s0.sp - 1760#64) sendCt2EncoderStack)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (⌜sf.trace = s0.trace⌝ ∗
            ct1AcknowledgedRecvEkChunkResAt A outA res ∗ memRegion stA 528 ∗
            chunkAt chunkA chunk ∗ unchunkedSendCt2RoAt b ∗
            tokenInitAt b ∗ reduceTableAt b ∗
            A.pool ∗ stackAt s0.sp ct1AcknowledgedRecvEkChunkStack) ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  subst hres
  have hepilogue := ct1_ack_recv_ek_epilogue_244 (F := F) hsortedSet16_raw
    outA stA chunkA chunk receivingEk (.error e) s0
  code_fetches libsignalSessionCode spqrCt1AcknowledgedRecvEkChunkBin b
    (Rust.withPanics ext) ct1AcknowledgedRecvEkChunk_fnOff 366032 612
  dsimp only [leavesProgAtExt, ct1AcknowledgedRecvEkChunkName, BitVec.ofNat_eq_ofNat] at hepilogue hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::send_ct::Ct1Acknowledged>::recv_ek_chunk" = entry
  examples_hide_fetches
  wp_conv_pre =>
    rw [ProofLib.memRegion_split' (b := outA) (n := 32) (k := 496) (b' := outA + 32#64) rfl rfl (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 1224#64) (n := 24) (k := 608) (b' := s0.sp - 1200#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 1200#64) (n := 24) (k := 584) (b' := s0.sp - 1176#64) rfl (by bv_omega) (by decide)]
  refine SepWP.fold (unchunkedRecvEk_err_expose A (F := F) s0.sp e) (by sep_focus) ?_
  wp_pull_exists; rename_i w1; wp_focus_pure; intro hw1
  refine SepWP.fold (cells_4_unfold outA) (by sep_focus) ?_
  refine SepWP.fold (cells_3_unfold (s0.sp - 1200#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_2_unfold (s0.sp - 576#64)) (by sep_focus) ?_
  wp_pull_exists
  wp_conv_pre => simp only [BitVec.add_assoc, arm64_norm]
  wp_steps
  refine SepWP.fold (hw1 (outA + 8#64)) (by sep_focus) ?_
  refine SepWP.fold (ct1Ack_err_outA_recompose A (F := F) outA e _ _) (by sep_focus) ?_
  refine SepWP.fold (ct1Ack_err_stack_1160_rejoin s0.sp _ _ _ _ _ _ _) (by sep_focus) ?_
  apply ct1AckEk_sepWP_congr_pre
  · refine hepilogue _ R hsp0_align ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [arm64_norm]
    · simpa only [arm64_norm] using hrun
    · simp only [State.sp, arm64_norm, hsp]
    · simp only [Reg.lr, arm64_norm]
    · simp only [arm64_norm, htr]
    · simp only [Reg.x0, arm64_norm, hsp]
    · simp only [arm64_norm, hx24]
    · simp only [arm64_norm, hx25]
    · simp only [arm64_norm, hx26]
    · simp only [arm64_norm, hx27]
    · simp only [arm64_norm, hvregs]
  · ac_rfl
  · funext sf P_f; simp only [sepConj_assoc]

/-! ## 6. Word Unfolding Helpers & Branch 2: `decoded? = none` (`+0x078..+0x080`, `+0x188..+0x228`) -/

theorem recompose_wordsAt_relocatedHeap (F : BitVec 64 → SepProp) (ws : List (BitVec 64)) (dst : BitVec 64) :
    wordsAt dst ws ∗ relocatedHeap F (wordsBytes ws) ⊢ F dst := by
  rw [wordsAt_eq_pointsToBytes]; exact relocatedHeap_recompose F (wordsBytes ws) dst

theorem vecU8_extract_nonNone (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A a bs ⊢
      ∃∗ v : VecWords,
        ⌜(v.w0 + 1#64 == 0#64) = false⌝ ∗
        wordsAt a (vecWordsList v) ∗
        relocatedHeap (fun dst => vecU8 A dst bs) (wordsBytes (vecWordsList v)) := by
  unfold vecU8 vecU8At vecHeader
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  let v : VecWords := ⟨cap, ptr, BitVec.ofNat 64 bs.length⟩
  refine Entails.sepExists_right v ?_
  rw [sepConj_left_comm (a ↦₆₄ cap ∗ (a + 8#64) ↦₆₄ ptr ∗ (a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)]
  apply Entails.pure_left; rintro ⟨hle, hcap_lt, hptr_ne⟩
  have hne : (v.w0 + 1#64 == 0#64) = false := by
    change (cap + 1#64 == 0#64) = false; apply beq_false_of_ne; bv_omega
  refine Entails.pure_right hne ?_
  have hhdr : ∀ dst : BitVec 64,
      ((dst ↦₆₄ cap) ∗ ((dst + 8#64) ↦₆₄ ptr) ∗ ((dst + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) =
      wordsAt dst (vecWordsList v) := by
    intro dst; simp only [vecWordsList, wordsAt, sepConj_emp]
    have h16 : (dst + 8#64) + 8#64 = dst + 16#64 := by bv_omega
    rw [h16]
  rw [hhdr a]
  refine sepConj_mono_right (relocatedHeap_intro _ fun dst => ?_)
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  rw [sepConj_left_comm (dst ↦₆₄ cap ∗ (dst + 8#64) ↦₆₄ ptr ∗ (dst + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)]
  refine Entails.pure_right ⟨hle, hcap_lt, hptr_ne⟩ ?_
  rw [hhdr dst, wordsAt_eq_pointsToBytes]; exact Entails.refl _

theorem unchunkedCt1SentEkReceivedAt_extract_nonNone (A : RustAlloc) {F : ShaCompress}
    (a : BitVec 64) (st : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F)) :
    unchunkedCt1SentEkReceivedAt A a st ⊢
      ∃∗ g : FiveVecWords,
        ⌜(g.v1.w0 + 1#64 == 0#64) = false⌝ ∗
        wordsAt a (fiveVecWordsList g st.epoch) ∗
        relocatedHeap (fun dst => unchunkedCt1SentEkReceivedAt A dst st)
          (wordsBytes (fiveVecWordsList g st.epoch)) := by
  let r0 := st.auth.rootKey
  let m0 := st.auth.macKey
  let st4 : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F) := ⟨st.epoch, ⟨m0, st.es⟩, st.ek, st.ct1⟩
  have heq : ∀ dst : BitVec 64,
      vecU8 A dst r0 ∗ unchunkedEkSentCt1ReceivedAt A (dst + 24#64) st4 =
        unchunkedCt1SentEkReceivedAt A dst st := by
    intro dst
    change vecU8 A dst r0 ∗ ((vecU8 A (dst + 24#64) m0 ∗ vecU8 A ((dst + 24#64) + 24#64) st.es) ∗
        vecU8 A ((dst + 24#64) + 48#64) st.ek ∗ vecU8 A ((dst + 24#64) + 72#64) st.ct1 ∗
        (((dst + 24#64) + 96#64) ↦₆₄ st.epoch)) =
      (vecU8 A dst r0 ∗ vecU8 A (dst + 24#64) m0) ∗ vecU8 A (dst + 48#64) st.es ∗
        vecU8 A (dst + 72#64) st.ek ∗ vecU8 A (dst + 96#64) st.ct1 ∗
        ((dst + 120#64) ↦₆₄ st.epoch)
    rw [BitVec.add_assoc dst 24#64 24#64, BitVec.add_assoc dst 24#64 48#64,
        BitVec.add_assoc dst 24#64 72#64, BitVec.add_assoc dst 24#64 96#64]; ac_rfl
  rw [← heq a]
  refine Entails.trans (sepConj_mono (vecU8_extract_nonNone A a r0)
    (unchunkedEkSentCt1ReceivedAt_extract A (a + 24#64) st4)) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro v1
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro rest
  refine Entails.sepExists_right ⟨v1, rest⟩ ?_
  rw [sepConj_assoc]; apply Entails.pure_left; intro hne
  exact Entails.pure_right hne (wordsExtract_sepConj rfl heq)

theorem wordsAt_fiveVec (a : BitVec 64) (g : FiveVecWords) (ep : BitVec 64) :
    wordsAt a (fiveVecWordsList g ep) =
      (a ↦₆₄ g.v1.w0) ∗ ((a + 8#64) ↦₆₄ g.v1.w1) ∗
      ((a + 16#64) ↦₆₄ g.v1.w2) ∗ ((a + 24#64) ↦₆₄ g.rest.v1.w0) ∗
      ((a + 32#64) ↦₆₄ g.rest.v1.w1) ∗ ((a + 40#64) ↦₆₄ g.rest.v1.w2) ∗
      ((a + 48#64) ↦₆₄ g.rest.rest.v1.w0) ∗ ((a + 56#64) ↦₆₄ g.rest.rest.v1.w1) ∗
      ((a + 64#64) ↦₆₄ g.rest.rest.v1.w2) ∗ ((a + 72#64) ↦₆₄ g.rest.rest.auth.v1.w0) ∗
      ((a + 80#64) ↦₆₄ g.rest.rest.auth.v1.w1) ∗ ((a + 88#64) ↦₆₄ g.rest.rest.auth.v1.w2) ∗
      ((a + 96#64) ↦₆₄ g.rest.rest.auth.v2.w0) ∗ ((a + 104#64) ↦₆₄ g.rest.rest.auth.v2.w1) ∗
      ((a + 112#64) ↦₆₄ g.rest.rest.auth.v2.w2) ∗ ((a + 120#64) ↦₆₄ ep) := by
  dsimp only [fiveVecWordsList, ekSentCt1ReceivedWordsList, ekSentWordsList,
    ct2SentWordsList, authWordsList, vecWordsList, List.append]
  simp only [wordsAt_16, arm64_norm]

def fiveVecTail15 (g : FiveVecWords) (ep : BitVec 64) : List (BitVec 64) :=
  [g.v1.w1, g.v1.w2] ++ ekSentCt1ReceivedWordsList g.rest ep

@[simp]
theorem length_fiveVecTail15 (g : FiveVecWords) (ep : BitVec 64) :
    (fiveVecTail15 g ep).length = 15 := rfl

theorem fiveVecWordsList_cons (g : FiveVecWords) (ep : BitVec 64) :
    fiveVecWordsList g ep = g.v1.w0 :: fiveVecTail15 g ep := rfl

theorem wordsAt_15 (a : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : BitVec 64) :
    wordsAt a [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] =
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
      ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗
      ((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9) ∗ ((a + 80#64) ↦₆₄ w10) ∗ ((a + 88#64) ↦₆₄ w11) ∗
      ((a + 96#64) ↦₆₄ w12) ∗ ((a + 104#64) ↦₆₄ w13) ∗ ((a + 112#64) ↦₆₄ w14) := by
  conv_lhs => rw [wordsAt]
  simp only [wordsAt_cons_off, wordsAt_nil, sepConj_emp,
    show (8#64 + 8#64 : BitVec 64) = 16#64 from rfl, show (16#64 + 8#64 : BitVec 64) = 24#64 from rfl,
    show (24#64 + 8#64 : BitVec 64) = 32#64 from rfl, show (32#64 + 8#64 : BitVec 64) = 40#64 from rfl,
    show (40#64 + 8#64 : BitVec 64) = 48#64 from rfl, show (48#64 + 8#64 : BitVec 64) = 56#64 from rfl,
    show (56#64 + 8#64 : BitVec 64) = 64#64 from rfl, show (64#64 + 8#64 : BitVec 64) = 72#64 from rfl,
    show (72#64 + 8#64 : BitVec 64) = 80#64 from rfl, show (80#64 + 8#64 : BitVec 64) = 88#64 from rfl,
    show (88#64 + 8#64 : BitVec 64) = 96#64 from rfl, show (96#64 + 8#64 : BitVec 64) = 104#64 from rfl,
    show (104#64 + 8#64 : BitVec 64) = 112#64 from rfl]

theorem wordsAt_fiveVecTail15 (a : BitVec 64) (g : FiveVecWords) (ep : BitVec 64) :
    wordsAt a (fiveVecTail15 g ep) =
      (a ↦₆₄ g.v1.w1) ∗ ((a + 8#64) ↦₆₄ g.v1.w2) ∗
      ((a + 16#64) ↦₆₄ g.rest.v1.w0) ∗ ((a + 24#64) ↦₆₄ g.rest.v1.w1) ∗
      ((a + 32#64) ↦₆₄ g.rest.v1.w2) ∗ ((a + 40#64) ↦₆₄ g.rest.rest.v1.w0) ∗
      ((a + 48#64) ↦₆₄ g.rest.rest.v1.w1) ∗ ((a + 56#64) ↦₆₄ g.rest.rest.v1.w2) ∗
      ((a + 64#64) ↦₆₄ g.rest.rest.auth.v1.w0) ∗ ((a + 72#64) ↦₆₄ g.rest.rest.auth.v1.w1) ∗
      ((a + 80#64) ↦₆₄ g.rest.rest.auth.v1.w2) ∗ ((a + 88#64) ↦₆₄ g.rest.rest.auth.v2.w0) ∗
      ((a + 96#64) ↦₆₄ g.rest.rest.auth.v2.w1) ∗ ((a + 104#64) ↦₆₄ g.rest.rest.auth.v2.w2) ∗
      ((a + 112#64) ↦₆₄ ep) := by
  dsimp only [fiveVecTail15, ekSentCt1ReceivedWordsList, ekSentWordsList,
    ct2SentWordsList, authWordsList, vecWordsList, List.append]
  simp only [wordsAt_15, arm64_norm]

theorem cells_15_unfold (a : BitVec 64) :
    memRegion a 120 ⊢
      ∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3, ∃∗ v4, ∃∗ v5, ∃∗ v6, ∃∗ v7,
      ∃∗ v8, ∃∗ v9, ∃∗ v10, ∃∗ v11, ∃∗ v12, ∃∗ v13, ∃∗ v14,
        (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) ∗
        ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5) ∗ ((a + 48#64) ↦₆₄ v6) ∗ ((a + 56#64) ↦₆₄ v7) ∗
        ((a + 64#64) ↦₆₄ v8) ∗ ((a + 72#64) ↦₆₄ v9) ∗ ((a + 80#64) ↦₆₄ v10) ∗ ((a + 88#64) ↦₆₄ v11) ∗
        ((a + 96#64) ↦₆₄ v12) ∗ ((a + 104#64) ↦₆₄ v13) ∗ ((a + 112#64) ↦₆₄ v14) := by
  rw [ProofLib.memRegion_cells a 15 (by decide), ProofLib.cells_succ]
  simp only [cells_succ_off, ProofLib.cells_zero, sepConj_emp, sepExists_sepConj_right,
    show (8#64 + 8#64 : BitVec 64) = 16#64 from rfl, show (16#64 + 8#64 : BitVec 64) = 24#64 from rfl,
    show (24#64 + 8#64 : BitVec 64) = 32#64 from rfl, show (32#64 + 8#64 : BitVec 64) = 40#64 from rfl,
    show (40#64 + 8#64 : BitVec 64) = 48#64 from rfl, show (48#64 + 8#64 : BitVec 64) = 56#64 from rfl,
    show (56#64 + 8#64 : BitVec 64) = 64#64 from rfl, show (64#64 + 8#64 : BitVec 64) = 72#64 from rfl,
    show (72#64 + 8#64 : BitVec 64) = 80#64 from rfl, show (80#64 + 8#64 : BitVec 64) = 88#64 from rfl,
    show (88#64 + 8#64 : BitVec 64) = 96#64 from rfl, show (96#64 + 8#64 : BitVec 64) = 104#64 from rfl,
    show (104#64 + 8#64 : BitVec 64) = 112#64 from rfl]
  exact Entails.refl _

theorem ct1Ack_none_outA_recompose (A : RustAlloc) {F : ShaCompress}
    (outA : BitVec 64) (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (receivingEk : PolyDecoder) (g : FiveVecWords)
    (bs1 : List (BitVec 8)) (hbs1 : bs1.length = 336)
    (d0 d1 d2 d3 d4 d5 d6 d7 : BitVec 64)
    (res : Except Error (Chunked.SendCt.Ct1AcknowledgedRecvChunk spqrPolyApi (spqrAuthApi F)))
    (hres : res = .ok (.stillReceiving { uc := uc, receiving_ek := receivingEk })) :
    (outA ↦₆₄ g.v1.w0) ∗
      ((outA + 8#64) ↦ₛ (wordsBytes (fiveVecTail15 g uc.epoch) ++ bs1)) ∗
      wordsAt (outA + 464#64) [d0, d1, d2, d3, d4, d5, d6, d7] ∗
      relocatedHeap (fun dst => unchunkedCt1SentAt A dst uc)
        (wordsBytes (fiveVecWordsList g uc.epoch)) ∗
      relocatedHeap (fun dst => polyDecoderAt A dst receivingEk)
        (bs1 ++ wordsBytes [d0, d1, d2, d3, d4, d5, d6, d7]) ⊢
    ct1AcknowledgedRecvEkChunkResAt A outA res := by
  subst hres
  dsimp only [ct1AcknowledgedRecvEkChunkResAt, chunkedCt1AcknowledgedAt]
  have hlen15 : (wordsBytes (fiveVecTail15 g uc.epoch)).length = 120 := by
    rw [length_wordsBytes, length_fiveVecTail15]
  have h128 : (outA + 8#64) + BitVec.ofNat 64 (wordsBytes (fiveVecTail15 g uc.epoch)).length =
      outA + 128#64 := by rw [hlen15]; bv_omega
  rw [pointsToBytes_append (outA + 8#64) (wordsBytes (fiveVecTail15 g uc.epoch)) bs1, h128]
  have huc :
      (outA ↦₆₄ g.v1.w0) ∗ ((outA + 8#64) ↦ₛ wordsBytes (fiveVecTail15 g uc.epoch)) ∗
        relocatedHeap (fun dst => unchunkedCt1SentAt A dst uc)
          (wordsBytes (fiveVecWordsList g uc.epoch)) ⊢
      unchunkedCt1SentAt A outA uc := by
    rw [← sepConj_assoc (outA ↦₆₄ g.v1.w0), ← wordsAt_eq_pointsToBytes, fiveVecWordsList_cons]
    exact recompose_wordsAt_relocatedHeap _ (g.v1.w0 :: fiveVecTail15 g uc.epoch) outA
  have h464 : (outA + 128#64) + BitVec.ofNat 64 bs1.length = outA + 464#64 := by
    rw [hbs1]; bv_omega
  have hdec :
      ((outA + 128#64) ↦ₛ bs1) ∗
        wordsAt (outA + 464#64) [d0, d1, d2, d3, d4, d5, d6, d7] ∗
        relocatedHeap (fun dst => polyDecoderAt A dst receivingEk)
          (bs1 ++ wordsBytes [d0, d1, d2, d3, d4, d5, d6, d7]) ⊢
      polyDecoderAt A (outA + 128#64) receivingEk := by
    rw [← sepConj_assoc ((outA + 128#64) ↦ₛ bs1), wordsAt_eq_pointsToBytes, ← h464,
        ← pointsToBytes_append (outA + 128#64) bs1 (wordsBytes [d0, d1, d2, d3, d4, d5, d6, d7])]
    exact relocatedHeap_recompose _ _ (outA + 128#64)
  refine Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono huc hdec)

theorem dec_slice_400_combine (a : BitVec 64) (bs1 : List (BitVec 8)) (hbs1 : bs1.length = 336)
    (d0 d1 d2 d3 d4 d5 d6 d7 : BitVec 64) :
    (a ↦ₛ bs1) ∗ wordsAt (a + 336#64) [d0, d1, d2, d3, d4, d5, d6, d7] =
      (a ↦ₛ (bs1 ++ wordsBytes [d0, d1, d2, d3, d4, d5, d6, d7])) := by
  have h336 : a + BitVec.ofNat 64 bs1.length = a + 336#64 := by rw [hbs1]
  rw [wordsAt_eq_pointsToBytes, ← h336,
      ← pointsToBytes_append a bs1 (wordsBytes [d0, d1, d2, d3, d4, d5, d6, d7])]

theorem dec_slice_400_split_dst (sp : BitVec 64) (bs1 : List (BitVec 8)) (hbs1 : bs1.length = 336)
    (d0 d1 d2 d3 d4 d5 d6 d7 : BitVec 64) :
    ((sp - 472#64) ↦ₛ (bs1 ++ wordsBytes [d0, d1, d2, d3, d4, d5, d6, d7])) ⊢
      ((sp - 472#64) ↦ₛ bs1) ∗ memRegion (sp - 136#64) 64 := by
  rw [← dec_slice_400_combine (sp - 472#64) bs1 hbs1 d0 d1 d2 d3 d4 d5 d6 d7]
  have h136 : (sp - 472#64) + 336#64 = sp - 136#64 := by bv_omega
  rw [h136]; exact sepConj_mono_right (wordsAt_entails_memRegion _ (sp - 136#64) 64 rfl)

theorem dec_slice_400_split_src (sp : BitVec 64) (bs1 : List (BitVec 8)) (hbs1 : bs1.length = 336)
    (d0 d1 d2 d3 d4 d5 d6 d7 : BitVec 64) :
    ((sp - 1624#64) ↦ₛ (bs1 ++ wordsBytes [d0, d1, d2, d3, d4, d5, d6, d7])) ⊢
      memRegion (sp - 1624#64) 336 ∗
        wordsAt (sp - 1288#64) [d0, d1, d2, d3, d4, d5, d6, d7] := by
  rw [← dec_slice_400_combine (sp - 1624#64) bs1 hbs1 d0 d1 d2 d3 d4 d5 d6 d7]
  have h1288 : (sp - 1624#64) + 336#64 = sp - 1288#64 := by bv_omega
  rw [h1288, ← hbs1]; exact sepConj_mono_left (pointsToBytes_entails_memRegion (sp - 1624#64) bs1)

theorem tail15_and_bs1_combine {F : ShaCompress} (sp : BitVec 64)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F)) (g : FiveVecWords) (bs1 : List (BitVec 8)) :
    wordsAt (sp - 592#64) (fiveVecTail15 g uc.epoch) ∗ ((sp - 472#64) ↦ₛ bs1) ⊢
      ((sp - 592#64) ↦ₛ (wordsBytes (fiveVecTail15 g uc.epoch) ++ bs1)) := by
  rw [wordsAt_eq_pointsToBytes]
  have hlen : (wordsBytes (fiveVecTail15 g uc.epoch)).length = 120 := by
    rw [length_wordsBytes, length_fiveVecTail15]
  have h472 : (sp - 592#64) + BitVec.ofNat 64 (wordsBytes (fiveVecTail15 g uc.epoch)).length =
      sp - 472#64 := by rw [hlen]; bv_omega
  rw [← h472, ← pointsToBytes_append (sp - 592#64) (wordsBytes (fiveVecTail15 g uc.epoch)) bs1]
  exact Entails.refl _

theorem ct1Ack_none_stack_rejoin (s0 : State) (d0 d1 d2 d3 d4 d5 d6 d7 : BitVec 64) :
    stackAt (s0.sp - 1760#64) sendCt2EncoderStack ∗
      memRegion (s0.sp - 1760#64) 136 ∗ memRegion (s0.sp - 1624#64) 336 ∗
      wordsAt (s0.sp - 1288#64) [d0, d1, d2, d3, d4, d5, d6, d7] ∗
      memRegion (s0.sp - 1224#64) 24 ∗ memRegion (s0.sp - 1200#64) 152 ∗
      memRegion (s0.sp - 1048#64) 456 ∗ memRegion (s0.sp - 592#64) 456 ∗
      memRegion (s0.sp - 136#64) 64 ∗ memRegion (s0.sp - 72#64) 8 ∗
      ct1AckSavedRegs s0 ⊢
    stackAt s0.sp ct1AcknowledgedRecvEkChunkStack := by
  have hd : wordsAt (s0.sp - 1288#64) [d0, d1, d2, d3, d4, d5, d6, d7] ⊢
      memRegion (s0.sp - 1288#64) 64 :=
    wordsAt_entails_memRegion _ (s0.sp - 1288#64) 64 rfl
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hd)))) ?_
  have h1160 :
      memRegion (s0.sp - 1224#64) 24 ∗
        (memRegion (s0.sp - 1200#64) 152 ∗
          (memRegion (s0.sp - 1048#64) 456 ∗
            (memRegion (s0.sp - 592#64) 456 ∗
              (memRegion (s0.sp - 136#64) 64 ∗ memRegion (s0.sp - 72#64) 8)))) =
      memRegion (s0.sp - 1224#64) 1160 := by
    rw [← ProofLib.memRegion_split' (b := s0.sp - 136#64) (n := 64) (k := 8) (b' := s0.sp - 72#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := s0.sp - 592#64) (n := 456) (k := 72) (b' := s0.sp - 136#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := s0.sp - 1048#64) (n := 456) (k := 528) (b' := s0.sp - 592#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := s0.sp - 1200#64) (n := 152) (k := 984) (b' := s0.sp - 1048#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := s0.sp - 1224#64) (n := 24) (k := 1136) (b' := s0.sp - 1200#64) rfl (by bv_omega) (by decide)]
  have h400 :
      memRegion (s0.sp - 1624#64) 336 ∗ memRegion (s0.sp - 1288#64) 64 =
      memRegion (s0.sp - 1624#64) 400 :=
    (ProofLib.memRegion_split' (b := s0.sp - 1624#64) (n := 336) (k := 64) (b' := s0.sp - 1288#64) rfl (by bv_omega) (by decide)).symm
  have hassoc :
      stackAt (s0.sp - 1760#64) sendCt2EncoderStack ∗
        memRegion (s0.sp - 1760#64) 136 ∗ memRegion (s0.sp - 1624#64) 336 ∗
        memRegion (s0.sp - 1288#64) 64 ∗ memRegion (s0.sp - 1224#64) 24 ∗
        memRegion (s0.sp - 1200#64) 152 ∗ memRegion (s0.sp - 1048#64) 456 ∗
        memRegion (s0.sp - 592#64) 456 ∗ memRegion (s0.sp - 136#64) 64 ∗
        memRegion (s0.sp - 72#64) 8 ∗ ct1AckSavedRegs s0 =
      stackAt (s0.sp - 1760#64) sendCt2EncoderStack ∗
        memRegion (s0.sp - 1760#64) 136 ∗
        (memRegion (s0.sp - 1624#64) 336 ∗ memRegion (s0.sp - 1288#64) 64) ∗
        (memRegion (s0.sp - 1224#64) 24 ∗
          (memRegion (s0.sp - 1200#64) 152 ∗
            (memRegion (s0.sp - 1048#64) 456 ∗
              (memRegion (s0.sp - 592#64) 456 ∗
                (memRegion (s0.sp - 136#64) 64 ∗ memRegion (s0.sp - 72#64) 8))))) ∗
        ct1AckSavedRegs s0 := by ac_rfl
  rw [hassoc, h400, h1160]
  exact stackAt_1760_exit_rejoin s0

theorem wordsAt_sp1760_fiveVec (sp : BitVec 64) (g : FiveVecWords) (ep : BitVec 64) :
    wordsAt (sp - 1760#64) (fiveVecWordsList g ep) =
      ((sp - 1760#64) ↦₆₄ g.v1.w0) ∗ ((sp - 1752#64) ↦₆₄ g.v1.w1) ∗
      ((sp - 1744#64) ↦₆₄ g.v1.w2) ∗ ((sp - 1736#64) ↦₆₄ g.rest.v1.w0) ∗
      ((sp - 1728#64) ↦₆₄ g.rest.v1.w1) ∗ ((sp - 1720#64) ↦₆₄ g.rest.v1.w2) ∗
      ((sp - 1712#64) ↦₆₄ g.rest.rest.v1.w0) ∗ ((sp - 1704#64) ↦₆₄ g.rest.rest.v1.w1) ∗
      ((sp - 1696#64) ↦₆₄ g.rest.rest.v1.w2) ∗ ((sp - 1688#64) ↦₆₄ g.rest.rest.auth.v1.w0) ∗
      ((sp - 1680#64) ↦₆₄ g.rest.rest.auth.v1.w1) ∗ ((sp - 1672#64) ↦₆₄ g.rest.rest.auth.v1.w2) ∗
      ((sp - 1664#64) ↦₆₄ g.rest.rest.auth.v2.w0) ∗ ((sp - 1656#64) ↦₆₄ g.rest.rest.auth.v2.w1) ∗
      ((sp - 1648#64) ↦₆₄ g.rest.rest.auth.v2.w2) ∗ ((sp - 1640#64) ↦₆₄ ep) := by
  rw [wordsAt_fiveVec]; simp only [arm64_norm]

theorem wordsAt_sp592_fiveVecTail15 (sp : BitVec 64) (g : FiveVecWords) (ep : BitVec 64) :
    wordsAt (sp - 592#64) (fiveVecTail15 g ep) =
      ((sp - 592#64) ↦₆₄ g.v1.w1) ∗ ((sp - 584#64) ↦₆₄ g.v1.w2) ∗
      ((sp - 576#64) ↦₆₄ g.rest.v1.w0) ∗ ((sp - 568#64) ↦₆₄ g.rest.v1.w1) ∗
      ((sp - 560#64) ↦₆₄ g.rest.v1.w2) ∗ ((sp - 552#64) ↦₆₄ g.rest.rest.v1.w0) ∗
      ((sp - 544#64) ↦₆₄ g.rest.rest.v1.w1) ∗ ((sp - 536#64) ↦₆₄ g.rest.rest.v1.w2) ∗
      ((sp - 528#64) ↦₆₄ g.rest.rest.auth.v1.w0) ∗ ((sp - 520#64) ↦₆₄ g.rest.rest.auth.v1.w1) ∗
      ((sp - 512#64) ↦₆₄ g.rest.rest.auth.v1.w2) ∗ ((sp - 504#64) ↦₆₄ g.rest.rest.auth.v2.w0) ∗
      ((sp - 496#64) ↦₆₄ g.rest.rest.auth.v2.w1) ∗ ((sp - 488#64) ↦₆₄ g.rest.rest.auth.v2.w2) ∗
      ((sp - 480#64) ↦₆₄ ep) := by
  rw [wordsAt_fiveVecTail15]; simp only [arm64_norm]

set_option maxHeartbeats 1200000 in
theorem ct1_ack_recv_ek_none_branch {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hmemcpy_raw : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr ct1AcknowledgedRecvEkChunkName + (bv% (ls_rel% "<spqr::v1::chunked::send_ct::Ct1Acknowledged>::recv_ek_chunk" "memcpy")))
      sessionMemcpyRegionSpec)
    (outA stA chunkA : BitVec 64)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (chunk : Chunk) (receivingEk : PolyDecoder) (g_uc : FiveVecWords)
    (res : Except Error (Chunked.SendCt.Ct1AcknowledgedRecvChunk spqrPolyApi (spqrAuthApi F)))
    (hres : res = .ok (.stillReceiving { uc := uc, receiving_ek := receivingEk }))
    (s0 s : State) (R : SepProp)
    (hsp0_align : s0.spAligned = true)
    (hpc : s.pc = (leavesProgAtExt b ext).fnAddr ct1AcknowledgedRecvEkChunkName + 120#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1760#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = outA) (hx20 : s.readReg64 (Reg.gpr 20#5) = stA)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = s0.sp - 1624#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5))
    (hx25 : s.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5))
    (hx26 : s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5))
    (hx27 : s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (leavesProgAtExt b ext) (s0.readReg64 Reg.lr) s
      (memRegion outA 528 ∗
        wordsAt stA (fiveVecWordsList g_uc uc.epoch) ∗ memRegion (stA + 128#64) 400 ∗
        relocatedHeap (fun dst => unchunkedCt1SentAt A dst uc)
          (wordsBytes (fiveVecWordsList g_uc uc.epoch)) ∗
        chunkAt chunkA chunk ∗ unchunkedSendCt2RoAt b ∗ tokenInitAt b ∗ reduceTableAt b ∗
        wordsAt (s0.sp - 1760#64) (fiveVecWordsList g_uc uc.epoch) ∗
        memRegion (s0.sp - 1632#64) 8 ∗ polyDecoderAt A (s0.sp - 1624#64) receivingEk ∗
        optVecU8At A (s0.sp - 1224#64) none ∗ memRegion (s0.sp - 1200#64) 1136 ∗
        ct1AckSavedRegs s0 ∗ A.pool ∗ stackAt (s0.sp - 1760#64) sendCt2EncoderStack)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (⌜sf.trace = s0.trace⌝ ∗
            ct1AcknowledgedRecvEkChunkResAt A outA res ∗ memRegion stA 528 ∗
            chunkAt chunkA chunk ∗ unchunkedSendCt2RoAt b ∗
            tokenInitAt b ∗ reduceTableAt b ∗
            A.pool ∗ stackAt s0.sp ct1AcknowledgedRecvEkChunkStack) ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  have hfsp_align : ((s0.sp - 1760#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 1760#64 hsp0_align (by decide)
  code_fetches libsignalSessionCode spqrCt1AcknowledgedRecvEkChunkBin b
    (Rust.withPanics ext) ct1AcknowledgedRecvEkChunk_fnOff 366032 612
  dsimp only [leavesProgAtExt, ct1AcknowledgedRecvEkChunkName, BitVec.ofNat_eq_ofNat] at hmemcpy_raw hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::send_ct::Ct1Acknowledged>::recv_ek_chunk" = entry
  examples_hide_fetches
  wp_conv_pre =>
    dsimp only [optVecU8At]
    rw [ProofLib.memRegion_split' (b := s0.sp - 1200#64) (n := 152) (k := 984) (b' := s0.sp - 1048#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 1048#64) (n := 456) (k := 528) (b' := s0.sp - 592#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 592#64) (n := 120) (k := 408) (b' := s0.sp - 472#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 472#64) (n := 400) (k := 8) (b' := s0.sp - 72#64) rfl (by bv_omega) (by decide)]
  wp_steps
  have h1224_fold :
      ((s0.sp - 1224#64) ↦₆₄ noneCap) ∗ memRegion ((s0.sp - 1224#64) + 8#64) 16 ⊢
      memRegion (s0.sp - 1224#64) 24 := by
    refine Entails.trans (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (s0.sp - 1224#64) noneCap)) ?_
    rw [← ProofLib.memRegion_split' (b := s0.sp - 1224#64) (n := 8) (k := 16) (b' := (s0.sp - 1224#64) + 8#64) rfl rfl (by decide)]
    exact Entails.refl _
  refine SepWP.fold h1224_fold (by sep_focus) ?_
  refine SepWP.fold (polyDecoderAt_extract_336_64 A (s0.sp - 1624#64) receivingEk) (by sep_focus) ?_
  wp_pull_exists; rename_i bs1 d0 d1 d2 d3 d4 d5 d6 d7
  wp_focus_pure; intro hbs1
  refine SepWP.fold (Entails.of_eq (dec_slice_400_combine (s0.sp - 1624#64) bs1 hbs1 d0 d1 d2 d3 d4 d5 d6 d7))
    (by sep_focus) ?_
  have hlen400 : (bs1 ++ wordsBytes [d0, d1, d2, d3, d4, d5, d6, d7]).length = 400 := by simp [hbs1]
  refine call_memcpy_bytes_cs hmemcpy_raw (s0.sp - 472#64) (s0.sp - 1624#64)
    (bs1 ++ wordsBytes [d0, d1, d2, d3, d4, d5, d6, d7]) hlen400
    (ret_pc := entry + 412#64) (sp_call := s0.sp - 1760#64) (s0 := s0)
    (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun)
    (by simp only [State.sp, arm64_norm, hsp]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr])
    (by simp only [Reg.x0, arm64_norm, hsp]) (by simp only [Reg.x1, arm64_norm, hsp])
    (by simp only [Reg.x2, arm64_norm]) (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 htr1 => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [arm64_norm, hx19, hx20, hx23, hx24, hx25, hx26, hx27, hvregs] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
  refine SepWP.fold (dec_slice_400_split_dst s0.sp bs1 hbs1 d0 d1 d2 d3 d4 d5 d6 d7) (by sep_focus) ?_
  refine SepWP.fold (dec_slice_400_split_src s0.sp bs1 hbs1 d0 d1 d2 d3 d4 d5 d6 d7) (by sep_focus) ?_
  refine SepWP.fold (cells_15_unfold (s0.sp - 592#64)) (by sep_focus) ?_
  wp_pull_exists
  wp_conv_pre =>
    rw [wordsAt_fiveVec stA g_uc uc.epoch, wordsAt_sp1760_fiveVec s0.sp g_uc uc.epoch]
    simp only [BitVec.add_assoc, arm64_norm]
  wp_steps
  refine SepWP.fold (Entails.of_eq (wordsAt_fiveVec stA g_uc uc.epoch).symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (wordsAt_sp1760_fiveVec s0.sp g_uc uc.epoch).symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (wordsAt_sp592_fiveVecTail15 s0.sp g_uc uc.epoch).symm) (by sep_focus) ?_
  have hstA_528 :
      wordsAt stA (fiveVecWordsList g_uc uc.epoch) ∗ memRegion (stA + 128#64) 400 ⊢
      memRegion stA 528 := by
    refine Entails.trans (sepConj_mono_left (wordsAt_entails_memRegion _ stA 128 rfl)) ?_
    rw [← ProofLib.memRegion_split' (b := stA) (n := 128) (k := 400) (b' := stA + 128#64) rfl rfl (by decide)]
    exact Entails.refl _
  have hsp1760_136 :
      wordsAt (s0.sp - 1760#64) (fiveVecWordsList g_uc uc.epoch) ∗ memRegion (s0.sp - 1632#64) 8 ⊢
      memRegion (s0.sp - 1760#64) 136 := by
    refine Entails.trans (sepConj_mono_left (wordsAt_entails_memRegion _ (s0.sp - 1760#64) 128 rfl)) ?_
    rw [← ProofLib.memRegion_split' (b := s0.sp - 1760#64) (n := 128) (k := 8) (b' := s0.sp - 1632#64) rfl (by bv_omega) (by decide)]
    exact Entails.refl _
  refine SepWP.fold hstA_528 (by sep_focus) ?_
  refine SepWP.fold hsp1760_136 (by sep_focus) ?_
  refine SepWP.fold (tail15_and_bs1_combine s0.sp uc g_uc bs1) (by sep_focus) ?_
  have hlen456 : (wordsBytes (fiveVecTail15 g_uc uc.epoch) ++ bs1).length = 456 := by
    rw [List.length_append, length_wordsBytes, length_fiveVecTail15, hbs1]
  refine call_memcpy_bytes_cs hmemcpy_raw (s0.sp - 1048#64) (s0.sp - 592#64)
    (wordsBytes (fiveVecTail15 g_uc uc.epoch) ++ bs1) hlen456
    (ret_pc := entry + 496#64) (sp_call := s0.sp - 1760#64) (s0 := s0)
    (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun1)
    (by simp only [State.sp, arm64_norm, hsp1]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr1])
    (by simp only [Reg.x0, arm64_norm, hsp1]) (by simp only [Reg.x1, arm64_norm, hsp1])
    (by simp only [Reg.x2, arm64_norm]) (by sep_focus)
    (fun sf2 hpc2 hrun2 hsp2 hcs2 htr2 => ?_)
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
  simp only [arm64_norm, hx19_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hvregs_1] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
  have h592_mem :
      ((s0.sp - 592#64) ↦ₛ (wordsBytes (fiveVecTail15 g_uc uc.epoch) ++ bs1)) ⊢
      memRegion (s0.sp - 592#64) 456 := by
    rw [← hlen456]; exact pointsToBytes_entails_memRegion (s0.sp - 592#64) _
  refine SepWP.fold h592_mem (by sep_focus) ?_
  wp_conv_pre =>
    rw [ProofLib.memRegion_split' (b := outA) (n := 8) (k := 520) (b' := outA + 8#64) rfl rfl (by decide),
        ProofLib.memRegion_split' (b := outA + 8#64) (n := 456) (k := 64) (b' := outA + 464#64) rfl (by bv_omega) (by decide)]
  refine SepWP.fold (cells_1_unfold outA) (by sep_focus) ?_
  wp_pull_exists
  wp_steps
  refine call_memcpy_bytes_cs hmemcpy_raw (outA + 8#64) (s0.sp - 1048#64)
    (wordsBytes (fiveVecTail15 g_uc uc.epoch) ++ bs1) hlen456
    (ret_pc := entry + 516#64) (sp_call := s0.sp - 1760#64) (s0 := s0)
    (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun2)
    (by simp only [State.sp, arm64_norm, hsp2]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr2])
    (by simp only [Reg.x0, arm64_norm]) (by simp only [Reg.x1, arm64_norm, hsp2])
    (by simp only [Reg.x2, arm64_norm]) (by sep_focus)
    (fun sf3 hpc3 hrun3 hsp3 hcs3 htr3 => ?_)
  rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hfp_3, hvregs_3⟩
  simp only [arm64_norm, hx19_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hvregs_2] at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hfp_3 hvregs_3
  have h1048_mem :
      ((s0.sp - 1048#64) ↦ₛ (wordsBytes (fiveVecTail15 g_uc uc.epoch) ++ bs1)) ⊢
      memRegion (s0.sp - 1048#64) 456 := by
    rw [← hlen456]; exact pointsToBytes_entails_memRegion (s0.sp - 1048#64) _
  refine SepWP.fold h1048_mem (by sep_focus) ?_
  refine SepWP.fold (cells_8_unfold (outA + 464#64)) (by sep_focus) ?_
  wp_pull_exists
  have hd_1288 :
      wordsAt (s0.sp - 1288#64) [d0, d1, d2, d3, d4, d5, d6, d7] =
      (((s0.sp - 1288#64) ↦₆₄ d0) ∗ ((s0.sp - 1280#64) ↦₆₄ d1) ∗
       ((s0.sp - 1272#64) ↦₆₄ d2) ∗ ((s0.sp - 1264#64) ↦₆₄ d3) ∗
       ((s0.sp - 1256#64) ↦₆₄ d4) ∗ ((s0.sp - 1248#64) ↦₆₄ d5) ∗
       ((s0.sp - 1240#64) ↦₆₄ d6) ∗ ((s0.sp - 1232#64) ↦₆₄ d7)) := by
    simp only [wordsAt_8, arm64_norm]
  have hd_out464 :
      wordsAt (outA + 464#64) [d0, d1, d2, d3, d4, d5, d6, d7] =
      (((outA + 464#64) ↦₆₄ d0) ∗ ((outA + 472#64) ↦₆₄ d1) ∗
       ((outA + 480#64) ↦₆₄ d2) ∗ ((outA + 488#64) ↦₆₄ d3) ∗
       ((outA + 496#64) ↦₆₄ d4) ∗ ((outA + 504#64) ↦₆₄ d5) ∗
       ((outA + 512#64) ↦₆₄ d6) ∗ ((outA + 520#64) ↦₆₄ d7)) := by
    simp only [wordsAt_8, BitVec.add_assoc, arm64_norm]
  wp_conv_pre =>
    unfold ct1AckSavedRegs
    rw [hd_1288]
    simp only [BitVec.add_assoc, arm64_norm]
  wp_steps
  refine SepWP.fold (Entails.of_eq hd_1288.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hd_out464.symm) (by sep_focus) ?_
  refine SepWP.fold (ct1Ack_none_outA_recompose A outA uc receivingEk g_uc bs1 hbs1
    d0 d1 d2 d3 d4 d5 d6 d7 res hres) (by sep_focus) ?_
  refine SepWP.fold (fold_ct1AckSavedRegs s0) (by sep_focus) ?_
  refine SepWP.fold (ct1Ack_none_stack_rejoin s0 d0 d1 d2 d3 d4 d5 d6 d7) (by sep_focus) ?_
  wp_done

end CryptoVerification.SpqrV1.States.Leaves
