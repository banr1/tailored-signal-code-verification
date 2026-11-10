/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2Defs
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import ProofLib.SepLogic.WPp

/-!
# Shared Pure & Framed Call Helpers for `recv_ct1_ack` and `recv_ct2_chunk`

**Checked by Lean.**

Pure unfolding lemmas, `vecU8Tail` slice/deallocation entailments, `emptyPolyDecoder`, and framed
subroutine call rules (`call_addChunk`, `call_sendCt2`, `call_sendCt2Encoder`) shared by
`<EkReceivedCt1Sampled>::recv_ct1_ack` and `<Ct1Received>::recv_ct2_chunk`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.Leaves

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit bv_sub_sub BitVec.sub_add_cancel BitVec.toNat_zero

/-! ## Pure Unfolding & `Vec<u8>` Slice/Dealloc Helpers -/

theorem recv_ct1_ack_ok_elim {F : ShaCompress} {K : MlKem}
    {st : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)}
    {outSt : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F)}
    (h : st.recv_ct1_ack K st.uc.epoch = .ok outSt) :
    ∃ ct2 mac,
      st.uc.send_ct2 K = .ok (outSt.uc, ct2, mac) ∧
      Chunked.SendCt.send_ct2_encoder spqrPolyApi ct2 mac = .ok outSt.sending_ct2 := by
  unfold Chunked.SendCt.EkReceivedCt1Sampled.recv_ct1_ack at h
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind] at h
  cases hsc : st.uc.send_ct2 K with
  | error e => simp [hsc] at h
  | ok val =>
    rcases val with ⟨uc', ct2, mac⟩
    simp only [hsc] at h
    cases henc : Chunked.SendCt.send_ct2_encoder spqrPolyApi ct2 mac with
    | error e => simp [henc] at h
    | ok enc' =>
      simp only [henc, Except.ok.injEq] at h
      subst h
      exact ⟨ct2, mac, rfl, henc⟩

/-- Remaining heap tail of a `Vec<u8>` when `(ptr ↦ₛ bs)` is borrowed out. -/
def vecU8Tail (A : RustAlloc) (cap ptr : BitVec 64) (bs : Bytes) : SepProp :=
  if (cap == 0#64) = true then emp
  else A.live ptr cap.toNat 1 ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)

/-- Unpack `vecU8 A a bs` into its header words `(cap, ptr, len)`, live slice `(ptr ↦ₛ bs)`,
    and `vecU8Tail A cap ptr bs`. -/
theorem vecU8_entails_slice_and_tail (A : RustAlloc) (a : BitVec 64) (bs : Bytes) :
    vecU8 A a bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗
        vecU8Tail A cap ptr bs := by
  unfold vecU8 vecU8At vecHeader vecU8Tail
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  rw [sepConj_left_comm (a ↦₆₄ cap ∗ (a + 8#64) ↦₆₄ ptr ∗ (a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)]
  apply Entails.pure_left; rintro ⟨hle, hcap_lt, hptr_ne⟩
  refine Entails.pure_right ⟨hle, hcap_lt, hptr_ne⟩ ?_
  by_cases hc : cap = 0#64
  · subst hc
    have hbs0 : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hle)
    subst hbs0
    simp only [beq_self_eq_true, ↓reduceIte, pointsToBytes_nil, emp_sepConj, sepConj_emp]
    exact Entails.of_eq (by ac_rfl)
  · have hcb : (cap == 0#64) = false := beq_false_of_ne hc
    have hc0 : cap ≠ 0 := hc
    simp only [hc0, hcb, Bool.false_eq_true, ↓reduceIte]
    exact Entails.of_eq (by ac_rfl)

/-- Recombine `(ptr ↦ₛ bs)` and `vecU8Tail A cap ptr bs` into `vecCapPtrDealloc A cap ptr`. -/
theorem slice_and_tail_entails_vecCapPtrDealloc (A : RustAlloc) (cap ptr : BitVec 64) (bs : Bytes)
    (hle : bs.length ≤ cap.toNat) (hcap_lt : cap.toNat < 2 ^ 63) :
    (ptr ↦ₛ bs) ∗ vecU8Tail A cap ptr bs ⊢ vecCapPtrDealloc A cap ptr := by
  unfold vecU8Tail vecCapPtrDealloc
  by_cases hc : (cap == 0#64) = true
  · simp only [hc, ↓reduceIte, sepConj_emp]
    have hcap0 : cap = 0#64 := eq_of_beq hc
    subst hcap0
    have hbs0 : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hle)
    subst hbs0
    rw [pointsToBytes_nil]
    exact Entails.refl _
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    refine Entails.trans (Entails.of_eq (show _ =
      A.live ptr cap.toNat 1 ∗ ((ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) by ac_rfl)) ?_
    refine sepConj_mono_right ?_
    have hsplit : memRegion ptr cap.toNat =
        memRegion ptr bs.length ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) := by
      conv_lhs => rw [show cap.toNat = bs.length + (cap.toNat - bs.length) by omega]
      exact ProofLib.memRegion_split ptr bs.length (cap.toNat - bs.length) (by omega)
    rw [hsplit]
    exact sepConj_mono_left (pointsToBytes_entails_memRegion ptr bs)

/-- Fresh `PolyDecoder` with `ptsNeeded` (`lenBytes / 2`) and 16 empty `SortedSetPt`s. -/
def emptyPolyDecoder (ptsNeeded : Nat) : PolyDecoder :=
  { ptsNeeded := ptsNeeded
    pts := List.replicate 16 SortedSetPt.new
    isComplete := false }

@[simp] theorem expectDecoderNew_160 (site : String) :
    expectDecoderNew spqrPolyApi site 160 = .ok (emptyPolyDecoder 80) := rfl

@[simp] theorem expectDecoderNew_960 (site : String) :
    expectDecoderNew spqrPolyApi site 960 = .ok (emptyPolyDecoder 480) := rfl

theorem ct1_received_recv_ct2_chunk_ok_elim {F : ShaCompress}
    {st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F)}
    {ct2_chunk : Chunk}
    {outSt : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F)}
    (h : st.recv_ct2_chunk st.uc.epoch ct2_chunk = .ok outSt) :
    outSt = { uc := st.uc,
              receiving_ct2 := addChunkTotal (emptyPolyDecoder 80) ct2_chunk } := by
  unfold Chunked.SendEk.Ct1Received.recv_ct2_chunk at h
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
  change (do
    let receivingCt2 ← expectDecoderNew spqrPolyApi "v1/chunked/send_ek.rs:174" 160
    let receivingCt2 ← spqrPolyApi.add_chunk receivingCt2 ct2_chunk
    Except.ok { uc := st.uc, receiving_ct2 := receivingCt2 }) = Except.ok outSt at h
  rw [expectDecoderNew_160] at h
  dsimp only [Bind.bind, Except.bind, spqrPolyApi, liftM, monadLift, MonadLift.monadLift,
    liftSpqrPanic] at h
  rw [addChunk_eq_ok (emptyPolyDecoder 80) ct2_chunk rfl] at h
  simp only [Except.mapError] at h
  exact (Except.ok.inj h).symm

theorem emptyPolyDecoder_strictSorted (ptsNeeded : Nat) :
    PolyDecoderStrictSorted (emptyPolyDecoder ptsNeeded) := by
  intro ss hss
  simp only [emptyPolyDecoder, List.mem_replicate] at hss
  rcases hss with ⟨_, rfl⟩
  exact List.Pairwise.nil

theorem three_words_entails_sortedSetPtOf_empty (A : RustAlloc) (b : BitVec 64) :
    (b ↦₆₄ 0#64) ∗ ((b + 8#64) ↦₆₄ 2#64) ∗ ((b + 16#64) ↦₆₄ 0#64) ⊢
      sortedSetPtOf A b SortedSetPt.new := by
  unfold sortedSetPtOf SortedSetPt.new vecOf vecAt vecHeader vecBuf
  refine Entails.sepExists_right 0#64 (Entails.sepExists_right 2#64 ?_)
  dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat]
  rw [ite_eq_left_iff.mpr (fun h => False.elim (h rfl)), sepConj_emp]
  have hpure : ([] : List Pt).length ≤ (0#64 : BitVec 64).toNat ∧
      (0#64 : BitVec 64).toNat * ptStride < 2 ^ 63 ∧ (2#64 : BitVec 64) ≠ 0 :=
    ⟨by decide, by decide, by decide⟩
  refine Entails.trans (Entails.pure_right hpure (Entails.refl _)) ?_
  exact Entails.of_eq (by ac_rfl)

theorem wordsAt_empty_slot_cons (A : RustAlloc) (a : BitVec 64) (ws : List (BitVec 64))
    (rest : List SortedSetPt)
    (hrest : wordsAt (a + 24#64) ws ⊢ sortedSetPtListOf A (a + 24#64) rest) :
    wordsAt a (0#64 :: 2#64 :: 0#64 :: ws) ⊢
      sortedSetPtListOf A a (SortedSetPt.new :: rest) := by
  show (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 2#64) ∗ (((a + 8#64) + 8#64) ↦₆₄ 0#64) ∗
    wordsAt (((a + 8#64) + 8#64) + 8#64) ws ⊢
    sortedSetPtOf A a SortedSetPt.new ∗ sortedSetPtListOf A (a + 24#64) rest
  have h16 : (a + 8#64) + 8#64 = a + 16#64 := by bv_omega
  have h24 : ((a + 8#64) + 8#64) + 8#64 = a + 24#64 := by bv_omega
  rw [h24, h16]
  refine Entails.trans (Entails.of_eq (show _ =
    ((a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 2#64) ∗ ((a + 16#64) ↦₆₄ 0#64)) ∗
      wordsAt (a + 24#64) ws by ac_rfl)) ?_
  exact sepConj_mono (three_words_entails_sortedSetPtOf_empty A a) hrest

theorem byte_1_unfold (a : BitVec 64) :
    memRegion a 1 ⊢ ∃∗ b0 : BitVec 8, a ↦₈ b0 := by
  rw [memRegion_eq_exists_bytes a 1 (by decide)]
  apply Entails.sepExists_elim; intro bs
  apply Entails.pure_left; intro hlen
  rcases bs with _ | ⟨b0, _ | _⟩
  · simp at hlen
  · refine Entails.sepExists_right b0 ?_
    simp [pointsToBytes_cons, pointsToBytes_nil]
    exact Entails.refl _
  · simp at hlen

theorem emptyPolyDecoder_recompose (A : RustAlloc) (decA : BitVec 64) (ptsNeeded : Nat)
    (hptsNeeded : ptsNeeded < 2 ^ 64) :
    wordsAt decA
      [0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64,
       0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64] ∗
    wordsAt (decA + 128#64)
      [2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64,
       0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64] ∗
    wordsAt (decA + 256#64)
      [0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64,
       2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64] ∗
    ((decA + 384#64) ↦₆₄ BitVec.ofNat 64 ptsNeeded) ∗
    ((decA + 392#64) ↦₈ 0#8) ∗
    memRegion (decA + 393#64) 7 ⊢
    polyDecoderAt A decA (emptyPolyDecoder ptsNeeded) := by
  unfold polyDecoderAt emptyPolyDecoder
  dsimp only [polyDecoderPtsNeededOff, polyDecoderIsCompleteOff, polyDecoderPadOff,
    polyDecoderPadSize, boolByte]
  have hpure : (List.replicate 16 SortedSetPt.new).length = NUM_POLYS ∧ ptsNeeded < 2 ^ 64 :=
    ⟨rfl, hptsNeeded⟩
  refine Entails.pure_right hpure ?_
  have happ1 := (wordsAt_append
    [0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64,
     0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64]
    [2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64,
     0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64] decA).symm
  have happ2 := (wordsAt_append
    ([0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64,
      0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64] ++
     [2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64,
      0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64])
    [0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64,
     2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64] decA).symm
  dsimp only [List.length_cons, List.length_nil, List.cons_append, List.nil_append] at happ1 happ2
  rw [← sepConj_assoc, ← sepConj_assoc, happ1, happ2]
  refine sepConj_mono_left ?_
  dsimp only [List.replicate]
  iterate 16 refine wordsAt_empty_slot_cons A _ _ _ ?_
  exact Entails.refl emp

/-- Framed call rule for `addChunkSpec A` (`0x66f44`), bridging from `SepWP` before the call
to `SepWPp` (propagating `allocFailedIn s0 sf`) and back to `SepWP` after the call. -/
theorem call_addChunk {A : RustAlloc} {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (addChunkSpec A))
    (decA chunkA : BitVec 64) (dec : PolyDecoder) (chunk : Chunk)
    (hsorted : PolyDecoderStrictSorted dec)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = decA)
    (hx1 : s.readReg64 Reg.x1 = chunkA)
    (hsplit : P = (polyDecoderAt A decA dec ∗ chunkAt chunkA chunk ∗
      A.pool ∗ stackAt sp_call addChunkStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      PolyDecoderStrictSorted (addChunkTotal dec chunk) →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((polyDecoderAt A decA (addChunkTotal dec chunk) ∗ chunkAt chunkA chunk ∗
          A.pool ∗ stackAt sp_call addChunkStack) ∗ Frame) post) :
    SepWP prog entry s P
      (fun sm Pm =>
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R))) := by
  apply SepWP.done hpc hrun
  refine SepWPp.call hcall (x := ⟨decA, chunkA, dec, chunk⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [addChunkSpec]
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hsorted⟩, hm⟩
  · rw [← sepConj_assoc]
    refine allowPanic_frame (fun ⟨haf, htr_sub⟩ => ?_) hmem
    unfold allocFailedIn at haf ⊢
    rw [htrace] at haf htr_sub
    exact ⟨haf, htr_sub⟩
  · dsimp only [addChunkSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun ⟨htr, hsorted'⟩ => ?_
    apply SepWPp.of_sepWP_ret
    have hassoc :
        (polyDecoderAt A decA (addChunkTotal dec chunk) ∗ chunkAt chunkA chunk ∗
          A.pool ∗ stackAt sp_call addChunkStack) ∗ Frame =
        (polyDecoderAt A decA (addChunkTotal dec chunk) ∗
          (chunkAt chunkA chunk ∗ (A.pool ∗ stackAt sp_call addChunkStack))) ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) hsorted'

/-- Framed call rule for `unchunkedCt1SentEkReceivedSendCt2Spec A F K b` (`0x5e400`). -/
theorem call_sendCt2 {A : RustAlloc} {F : ShaCompress} {K : MlKem} {b : BitVec 64}
    {prog : Program} {entry ret_pc next_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (unchunkedCt1SentEkReceivedSendCt2Spec A F K b))
    (hb : b &&& 0xfff#64 = 0#64)
    (outA stA : BitVec 64)
    (st : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F))
    (outUc : Unchunked.SendCt.Ct2Sent (spqrAuthApi F)) (ct2 : Bytes) (mac : Mac)
    (hsc : st.send_ct2 K = .ok (outUc, ct2, mac))
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = outA)
    (hx1 : s.readReg64 Reg.x1 = stA)
    (hsplit : P = (memRegion outA 104 ∗ unchunkedCt1SentEkReceivedAt A stA st ∗
      unchunkedSendCt2RoAt b ∗ A.pool ∗ stackAt sp_call unchunkedSendCt2Stack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog next_pc sf
        ((unchunkedCt2SentAt A outA outUc ∗ vecU8 A (outA + 56#64) ct2 ∗
          vecU8 A (outA + 80#64) mac ∗ memRegion stA 128 ∗
          unchunkedSendCt2RoAt b ∗ A.pool ∗ stackAt sp_call unchunkedSendCt2Stack) ∗ Frame)
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
  refine SepWPp.call hcall (x := ⟨outA, stA, st, outUc, ct2, mac⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [unchunkedCt1SentEkReceivedSendCt2Spec]
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hb, hx0, hx1, hsc⟩, hm⟩
  · rw [← sepConj_assoc]
    refine allowPanic_frame (fun ⟨haf, htr_sub⟩ => ?_) hmem
    unfold allocFailedIn at haf ⊢
    rw [htrace] at haf htr_sub
    exact ⟨haf, htr_sub⟩
  · dsimp only [unchunkedCt1SentEkReceivedSendCt2Spec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    apply SepWPp.of_sepWP (mid := next_pc)
    have hassoc :
        (unchunkedCt2SentAt A outA outUc ∗ vecU8 A (outA + 56#64) ct2 ∗
          vecU8 A (outA + 80#64) mac ∗ memRegion stA 128 ∗
          unchunkedSendCt2RoAt b ∗ A.pool ∗ stackAt sp_call unchunkedSendCt2Stack) ∗ Frame =
        (unchunkedCt2SentAt A outA outUc ∗
          (vecU8 A (outA + 56#64) ct2 ∗
            (vecU8 A (outA + 80#64) mac ∗
              (memRegion stA 128 ∗
                (unchunkedSendCt2RoAt b ∗
                  (A.pool ∗ stackAt sp_call unchunkedSendCt2Stack)))))) ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace)

/-- Framed call rule for `sendCt2EncoderSpec A` (`0x63b28`). -/
theorem call_sendCt2Encoder {A : RustAlloc} {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (sendCt2EncoderSpec A))
    (outA ct2Ptr macPtr : BitVec 64) (ct2 mac : Bytes) (enc : PolyEncoder)
    (hct2_ptr : ct2Ptr ≠ 0#64) (hmac_ptr : macPtr ≠ 0#64)
    (henc : Chunked.SendCt.send_ct2_encoder spqrPolyApi ct2 mac = .ok enc)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = outA)
    (hx1 : s.readReg64 Reg.x1 = ct2Ptr)
    (hx2 : s.readReg64 Reg.x2 = BitVec.ofNat 64 ct2.length)
    (hx3 : s.readReg64 Reg.x3 = macPtr)
    (hx4 : s.readReg64 Reg.x4 = BitVec.ofNat 64 mac.length)
    (hsplit : P = (memRegion outA 400 ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
      A.pool ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((polyEncoderAt A outA enc ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
          A.pool ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame) post) :
    SepWP prog entry s P
      (fun sm Pm =>
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R))) := by
  apply SepWP.done hpc hrun
  refine SepWPp.call hcall (x := ⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [sendCt2EncoderSpec]
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hct2_ptr, hmac_ptr, henc⟩, hm⟩
  · rw [← sepConj_assoc]
    refine allowPanic_frame (fun ⟨haf, htr_sub⟩ => ?_) hmem
    unfold allocFailedIn at haf ⊢
    rw [htrace] at haf htr_sub
    exact ⟨haf, htr_sub⟩
  · dsimp only [sendCt2EncoderSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    apply SepWPp.of_sepWP_ret
    have hassoc :
        (polyEncoderAt A outA enc ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
          A.pool ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame =
        (polyEncoderAt A outA enc ∗
          ((ct2Ptr ↦ₛ ct2) ∗ ((macPtr ↦ₛ mac) ∗ (A.pool ∗ stackAt sp_call sendCt2EncoderStack)))) ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace)

theorem wordsAt_8 (a : BitVec 64) (w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64) :
    wordsAt a [w0, w1, w2, w3, w4, w5, w6, w7] =
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
      ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) := by
  conv_lhs => rw [wordsAt]
  simp only [wordsAt_cons_off, wordsAt_nil, sepConj_emp,
    show (8#64 + 8#64 : BitVec 64) = 16#64 from rfl, show (16#64 + 8#64 : BitVec 64) = 24#64 from rfl,
    show (24#64 + 8#64 : BitVec 64) = 32#64 from rfl, show (32#64 + 8#64 : BitVec 64) = 40#64 from rfl,
    show (40#64 + 8#64 : BitVec 64) = 48#64 from rfl, show (48#64 + 8#64 : BitVec 64) = 56#64 from rfl]

theorem cells_8_unfold (a : BitVec 64) :
    memRegion a 64 ⊢
      ∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3, ∃∗ v4, ∃∗ v5, ∃∗ v6, ∃∗ v7,
        (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) ∗
        ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5) ∗ ((a + 48#64) ↦₆₄ v6) ∗ ((a + 56#64) ↦₆₄ v7) := by
  rw [ProofLib.memRegion_cells a 8 (by decide), ProofLib.cells_succ]
  simp only [cells_succ_off, ProofLib.cells_zero, sepConj_emp, sepExists_sepConj_right,
    show (8#64 + 8#64 : BitVec 64) = 16#64 from rfl, show (16#64 + 8#64 : BitVec 64) = 24#64 from rfl,
    show (24#64 + 8#64 : BitVec 64) = 32#64 from rfl, show (32#64 + 8#64 : BitVec 64) = 40#64 from rfl,
    show (40#64 + 8#64 : BitVec 64) = 48#64 from rfl, show (48#64 + 8#64 : BitVec 64) = 56#64 from rfl]
  exact Entails.refl _

end CryptoVerification.SpqrV1.States.Leaves
