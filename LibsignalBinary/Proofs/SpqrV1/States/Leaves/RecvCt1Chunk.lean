/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2Defs
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpoch
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.KeysSampledRecvCt1Chunk
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandCommon
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.AsmConstants -- shake: keep

/-!
# `<spqr::v1::chunked::send_ek::HeaderSent>::recv_ct1_chunk` (`0x5d8fc`)

**Checked by Lean.**

Verifies `header_sent_recv_ct1_chunk_ok_ext` (`0x5d8fc`, 113 instructions) against
`headerSentRecvCt1ChunkSpec A F b`.
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
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [-arm64_norm] headerSentRecvCt1Chunk_fnOff libsignalSessionCode_fnOff_0x58504
attribute [local arm64_norm] bv_sub_add_lit bv_sub_sub BitVec.sub_add_cancel BitVec.toNat_zero

/-! ## 1. Instruction Decode Tree (`0x5d8fc..0x5dac0`) -/

gen_decodes libsignalSessionCode_tree spqrHeaderSentRecvCt1ChunkBin [
  0x58504 → 0x586c8
]

/-! ## 2. Pure Unfolding & Extraction Lemmas -/

theorem spqrPolyApi_add_chunk_eq (dec : PolyDecoder) (chunk : Chunk) (hpts : dec.pts.length = 16) :
    spqrPolyApi.add_chunk dec chunk = .ok (addChunkTotal dec chunk) := by
  dsimp only [spqrPolyApi]
  rw [addChunk_eq_ok dec chunk hpts]
  rfl

theorem header_sent_recv_ct1_chunk_ok_elim {F : ShaCompress}
    {st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F)}
    {chunk : Chunk}
    {outRes : Chunked.SendEk.HeaderSentRecvChunk spqrPolyApi (spqrAuthApi F)}
    (hpts : st.receiving_ct1.pts.length = 16)
    (h : st.recv_ct1_chunk st.uc.epoch chunk = .ok outRes) :
    ∃ outMsg : Option Bytes,
      spqrPolyApi.decoded_message (addChunkTotal st.receiving_ct1 chunk) = .ok outMsg ∧
      ((outMsg = none ∧
        outRes = .stillReceiving { uc := st.uc,
                                   sending_ek := st.sending_ek,
                                   receiving_ct1 := addChunkTotal st.receiving_ct1 chunk }) ∨
       (∃ ct1 : Bytes,
         outMsg = some ct1 ∧
         outRes = .done { uc := { epoch := st.uc.epoch, auth := st.uc.auth, dk := st.uc.dk, ct1 := ct1 },
                          sending_ek := st.sending_ek })) := by
  unfold Chunked.SendEk.HeaderSent.recv_ct1_chunk at h
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
  dsimp only [Bind.bind, Except.bind, liftM, monadLift, MonadLift.monadLift, liftSpqrPanic] at h
  rw [spqrPolyApi_add_chunk_eq st.receiving_ct1 chunk hpts] at h
  dsimp only [Except.mapError] at h
  cases hdm : spqrPolyApi.decoded_message (addChunkTotal st.receiving_ct1 chunk) with
  | error e =>
    rw [hdm] at h
    contradiction
  | ok outMsg =>
    rw [hdm] at h
    dsimp only [Except.mapError] at h
    refine ⟨outMsg, rfl, ?_⟩
    cases outMsg with
    | none =>
      injection h with h
      exact Or.inl ⟨rfl, h.symm⟩
    | some ct1 =>
      unfold Unchunked.SendEk.EkSent.recv_ct1 at h
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
      exact Or.inr ⟨ct1, rfl, h.symm⟩

attribute [local irreducible] addChunkTotal

theorem vecU8_extract_with_cap_lt (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A a bs ⊢
      ∃∗ v : VecWords,
        ⌜v.w0.toNat < 2 ^ 63⌝ ∗
        wordsAt a (vecWordsList v) ∗
        relocatedHeap (fun dst => vecU8 A dst bs) (wordsBytes (vecWordsList v)) := by
  unfold vecU8 vecU8At vecHeader
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  rw [sepConj_left_comm ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length))]
  apply Entails.pure_left; rintro ⟨hle, hcap_lt, hptr_ne⟩
  let v : VecWords := ⟨cap, ptr, BitVec.ofNat 64 bs.length⟩
  refine Entails.sepExists_right v (Entails.pure_right hcap_lt ?_)
  have hhdr : ∀ dst : BitVec 64,
      ((dst ↦₆₄ cap) ∗ ((dst + 8#64) ↦₆₄ ptr) ∗ ((dst + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) =
      wordsAt dst (vecWordsList v) := by
    intro dst
    simp only [vecWordsList, wordsAt, sepConj_emp]
    have h16 : (dst + 8#64) + 8#64 = dst + 16#64 := by bv_omega
    rw [h16]
  rw [hhdr a]
  refine sepConj_mono_right (relocatedHeap_intro _ fun dst => ?_)
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  rw [hhdr dst, wordsAt_eq_pointsToBytes]
  refine sepConj_mono_right (Entails.pure_right ⟨hle, hcap_lt, hptr_ne⟩ (Entails.refl _))

theorem wordsAt_12 (a : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 : BitVec 64) :
    wordsAt a [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11] =
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
      ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗
      ((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9) ∗ ((a + 80#64) ↦₆₄ w10) ∗ ((a + 88#64) ↦₆₄ w11) := by
  conv_lhs => rw [wordsAt]
  simp only [wordsAt_cons_off, wordsAt_nil, sepConj_emp,
    show (8#64 + 8#64 : BitVec 64) = 16#64 from rfl, show (16#64 + 8#64 : BitVec 64) = 24#64 from rfl,
    show (24#64 + 8#64 : BitVec 64) = 32#64 from rfl, show (32#64 + 8#64 : BitVec 64) = 40#64 from rfl,
    show (40#64 + 8#64 : BitVec 64) = 48#64 from rfl, show (48#64 + 8#64 : BitVec 64) = 56#64 from rfl,
    show (56#64 + 8#64 : BitVec 64) = 64#64 from rfl, show (64#64 + 8#64 : BitVec 64) = 72#64 from rfl,
    show (72#64 + 8#64 : BitVec 64) = 80#64 from rfl, show (80#64 + 8#64 : BitVec 64) = 88#64 from rfl]

theorem cells_12_unfold (a : BitVec 64) :
    memRegion a 96 ⊢
      ∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3, ∃∗ v4, ∃∗ v5, ∃∗ v6, ∃∗ v7, ∃∗ v8, ∃∗ v9, ∃∗ v10, ∃∗ v11,
        wordsAt a [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11] := by
  rw [ProofLib.memRegion_cells a 12 (by decide), ProofLib.cells_succ]
  simp only [wordsAt_12, cells_succ_off, ProofLib.cells_zero, sepConj_emp, sepExists_sepConj_right,
    show (8#64 + 8#64 : BitVec 64) = 16#64 from rfl, show (16#64 + 8#64 : BitVec 64) = 24#64 from rfl,
    show (24#64 + 8#64 : BitVec 64) = 32#64 from rfl, show (32#64 + 8#64 : BitVec 64) = 40#64 from rfl,
    show (40#64 + 8#64 : BitVec 64) = 48#64 from rfl, show (48#64 + 8#64 : BitVec 64) = 56#64 from rfl,
    show (56#64 + 8#64 : BitVec 64) = 64#64 from rfl, show (64#64 + 8#64 : BitVec 64) = 72#64 from rfl,
    show (72#64 + 8#64 : BitVec 64) = 80#64 from rfl, show (80#64 + 8#64 : BitVec 64) = 88#64 from rfl]
  exact Entails.refl _

theorem Relocatable.of_wordsAt (ws : List (BitVec 64)) (n : Nat) (hn : 8 * ws.length = n) :
    Relocatable n (fun a => wordsAt a ws) := by
  intro src; dsimp only
  refine Entails.sepExists_right (wordsBytes ws) ?_
  have hlen : (wordsBytes ws).length = n := by rw [length_wordsBytes, hn]
  refine Entails.pure_right hlen ?_
  rw [wordsAt_eq_pointsToBytes]
  conv_lhs => rw [← sepConj_emp (src ↦ₛ wordsBytes ws)]
  refine sepConj_mono_right (relocatedHeap_intro emp fun dst => ?_)
  rw [sepConj_emp, wordsAt_eq_pointsToBytes]
  exact Entails.refl _

theorem Relocatable.of_polyEncoder_and_words12 (A : RustAlloc) (enc : PolyEncoder)
    (ws : List (BitVec 64)) (hws : 8 * ws.length = 96) :
    Relocatable 496 (fun a => polyEncoderAt A a enc ∗ wordsAt (a + 400#64) ws) :=
  Relocatable.sepConj (off := 400#64) (m := 496) rfl rfl
    (Relocatable.of_polyEncoderAt A enc) (Relocatable.of_wordsAt ws 96 hws)

/-! ## 3. Framed Call Helpers for `decoded_message` (`0x6bb80`) and `drop_glue::<[SortedSet<Pt>; 16]>` (`0x4bd18`) -/

/-- Framed call rule for `polyDecoderDecodedMessageSpec A b` (`0x6bb80`). -/
theorem call_decodedMessage {A : RustAlloc} {b : BitVec 64} {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (polyDecoderDecodedMessageSpec A b))
    (hb : b &&& 0xfff#64 = 0#64)
    (outA decA : BitVec 64) (dec : PolyDecoder) (outMsg : Option Bytes)
    (hsorted : PolyDecoderStrictSorted dec)
    (hdm : spqrPolyApi.decoded_message dec = .ok outMsg)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hx8 : s.readReg64 Reg.x8 = outA)
    (hx0 : s.readReg64 Reg.x0 = decA)
    (hsplit : P = (memRegion outA 24 ∗ polyDecoderAt A decA dec ∗
      tokenInitAt b ∗ reduceTableAt b ∗ A.pool ∗ stackAt sp_call polyDecoderDecodedMessageStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((optVecU8At A outA outMsg ∗ polyDecoderAt A decA dec ∗
          tokenInitAt b ∗ reduceTableAt b ∗ A.pool ∗ stackAt sp_call polyDecoderDecodedMessageStack) ∗ Frame) post) :
    SepWP prog entry s P
      (fun sm Pm =>
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R))) := by
  apply SepWP.done hpc hrun
  refine SepWPp.call hcall (x := ⟨outA, decA, dec, outMsg⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [polyDecoderDecodedMessageSpec]
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hb, hx8, hx0, hsorted, hdm⟩, hm⟩
  · rw [← sepConj_assoc]
    refine allowPanic_frame (fun ⟨haf, htr_sub⟩ => ?_) hmem
    unfold allocFailedIn at haf ⊢
    rw [htrace] at haf htr_sub
    exact ⟨haf, htr_sub⟩
  · dsimp only [polyDecoderDecodedMessageSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    apply SepWPp.of_sepWP_ret
    have hassoc :
        (optVecU8At A outA outMsg ∗ polyDecoderAt A decA dec ∗
          tokenInitAt b ∗ reduceTableAt b ∗ A.pool ∗ stackAt sp_call polyDecoderDecodedMessageStack) ∗ Frame =
        (optVecU8At A outA outMsg ∗ (polyDecoderAt A decA dec ∗
          (tokenInitAt b ∗ (reduceTableAt b ∗ (A.pool ∗ stackAt sp_call polyDecoderDecodedMessageStack))))) ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace)

/-- Framed call rule for `dropGlueSortedSetPt16Spec A` (`0x4bd18`). -/
theorem call_dropGlueSortedSetPt16_cs {A : RustAlloc} {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (dropGlueSortedSetPt16Spec A))
    (arrA : BitVec 64) (vecs : List (List Pt))
    (hvecs_len : vecs.length = NUM_POLYS)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = arrA)
    (hsplit : P = (vecPtListOf A arrA vecs ∗ A.pool ∗ stackAt sp_call dropGluePoly16Stack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog target_pc sf
        ((memRegion arrA polyArrayBytes ∗ A.pool ∗ stackAt sp_call dropGluePoly16Stack) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  refine SepWP.call_subroutine_frame hcall (x := ⟨arrA, vecs⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    rw [hsplit] at hm
    dsimp only [dropGlueSortedSetPt16Spec]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hvecs_len⟩, by simpa only [sepConj_assoc] using hm⟩
  · dsimp only [dropGlueSortedSetPt16Spec]
    rw [hsp, sepConj_assoc]
    refine SepWP.pure_elim fun htr => ?_
    have hassoc :
        (memRegion arrA polyArrayBytes ∗ A.pool ∗ stackAt sp_call dropGluePoly16Stack) ∗ Frame =
        (memRegion arrA polyArrayBytes ∗ (A.pool ∗ stackAt sp_call dropGluePoly16Stack)) ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace)

/-! ## 4. Stack Layout & Address Normalization for `HeaderSent::recv_ct1_chunk` (`1568`B Frame) -/

@[local arm64_norm, local wp_norm] private theorem sp_sub_64_align (sp : BitVec 64) :
    ((sp - 64#64) &&& 15#64 == 0#64) = (sp &&& 15#64 == 0#64) := by
  have h : (sp - 64#64) &&& 15#64 = sp &&& 15#64 := by bv_bits
  rw [h]
@[local arm64_norm, local wp_norm] private theorem sp_sub_64_sub_1504 (sp : BitVec 64) : (sp - 64#64) - 1504#64 = sp - 1568#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_1504 (sp : BitVec 64) : (sp - 1568#64) + 1504#64 = sp - 64#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_64_add_8 (sp : BitVec 64) : (sp - 64#64) + 8#64 = sp - 56#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_64_add_16 (sp : BitVec 64) : (sp - 64#64) + 16#64 = sp - 48#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_64_add_24 (sp : BitVec 64) : (sp - 64#64) + 24#64 = sp - 40#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_64_add_32 (sp : BitVec 64) : (sp - 64#64) + 32#64 = sp - 32#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_64_add_40 (sp : BitVec 64) : (sp - 64#64) + 40#64 = sp - 24#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_64_add_48 (sp : BitVec 64) : (sp - 64#64) + 48#64 = sp - 16#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_64_add_56 (sp : BitVec 64) : (sp - 64#64) + 56#64 = sp - 8#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_64_add_64 (sp : BitVec 64) : (sp - 64#64) + 64#64 = sp := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_48_add_8 (sp : BitVec 64) : (sp - 48#64) + 8#64 = sp - 40#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_32_add_8 (sp : BitVec 64) : (sp - 32#64) + 8#64 = sp - 24#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_16_add_8 (sp : BitVec 64) : (sp - 16#64) + 8#64 = sp - 8#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_8 (sp : BitVec 64) : (sp - 1568#64) + 8#64 = sp - 1560#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_16 (sp : BitVec 64) : (sp - 1568#64) + 16#64 = sp - 1552#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_24 (sp : BitVec 64) : (sp - 1568#64) + 24#64 = sp - 1544#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_32 (sp : BitVec 64) : (sp - 1568#64) + 32#64 = sp - 1536#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_40 (sp : BitVec 64) : (sp - 1568#64) + 40#64 = sp - 1528#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_48 (sp : BitVec 64) : (sp - 1568#64) + 48#64 = sp - 1520#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_56 (sp : BitVec 64) : (sp - 1568#64) + 56#64 = sp - 1512#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_64 (sp : BitVec 64) : (sp - 1568#64) + 64#64 = sp - 1504#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_72 (sp : BitVec 64) : (sp - 1568#64) + 72#64 = sp - 1496#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_80 (sp : BitVec 64) : (sp - 1568#64) + 80#64 = sp - 1488#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_88 (sp : BitVec 64) : (sp - 1568#64) + 88#64 = sp - 1480#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_104 (sp : BitVec 64) : (sp - 1568#64) + 104#64 = sp - 1464#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_249 (sp : BitVec 64) : (sp - 1568#64) + 249#64 = sp - 1319#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_504 (sp : BitVec 64) : (sp - 1568#64) + 504#64 = sp - 1064#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_520 (sp : BitVec 64) : (sp - 1568#64) + 520#64 = sp - 1048#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_528 (sp : BitVec 64) : (sp - 1568#64) + 528#64 = sp - 1040#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_592 (sp : BitVec 64) : (sp - 1568#64) + 592#64 = sp - 976#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_616 (sp : BitVec 64) : (sp - 1568#64) + 616#64 = sp - 952#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_624 (sp : BitVec 64) : (sp - 1568#64) + 624#64 = sp - 944#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1552_add_8 (sp : BitVec 64) : (sp - 1552#64) + 8#64 = sp - 1544#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1552_add_16 (sp : BitVec 64) : (sp - 1552#64) + 16#64 = sp - 1536#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1552_add_24 (sp : BitVec 64) : (sp - 1552#64) + 24#64 = sp - 1528#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1520_add_8 (sp : BitVec 64) : (sp - 1520#64) + 8#64 = sp - 1512#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1520_add_16 (sp : BitVec 64) : (sp - 1520#64) + 16#64 = sp - 1504#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1520_add_24 (sp : BitVec 64) : (sp - 1520#64) + 24#64 = sp - 1496#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1488_add_8 (sp : BitVec 64) : (sp - 1488#64) + 8#64 = sp - 1480#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1319_add_255 (sp : BitVec 64) : (sp - 1319#64) + 255#64 = sp - 1064#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1064_add_8 (sp : BitVec 64) : (sp - 1064#64) + 8#64 = sp - 1056#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_944_add_480 (sp : BitVec 64) : (sp - 944#64) + 480#64 = sp - 464#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_944_add_400 (sp : BitVec 64) : (sp - 944#64) + 400#64 = sp - 544#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_8 (sp : BitVec 64) : (sp - 1040#64) + 8#64 = sp - 1032#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_16 (sp : BitVec 64) : (sp - 1040#64) + 16#64 = sp - 1024#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_24 (sp : BitVec 64) : (sp - 1040#64) + 24#64 = sp - 1016#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_32 (sp : BitVec 64) : (sp - 1040#64) + 32#64 = sp - 1008#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_40 (sp : BitVec 64) : (sp - 1040#64) + 40#64 = sp - 1000#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_48 (sp : BitVec 64) : (sp - 1040#64) + 48#64 = sp - 992#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_56 (sp : BitVec 64) : (sp - 1040#64) + 56#64 = sp - 984#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_64 (sp : BitVec 64) : (sp - 1040#64) + 64#64 = sp - 976#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_72 (sp : BitVec 64) : (sp - 1040#64) + 72#64 = sp - 968#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_80 (sp : BitVec 64) : (sp - 1040#64) + 80#64 = sp - 960#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_88 (sp : BitVec 64) : (sp - 1040#64) + 88#64 = sp - 952#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_496 (sp : BitVec 64) : (sp - 1040#64) + 496#64 = sp - 544#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_504 (sp : BitVec 64) : (sp - 1040#64) + 504#64 = sp - 536#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_512 (sp : BitVec 64) : (sp - 1040#64) + 512#64 = sp - 528#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_520 (sp : BitVec 64) : (sp - 1040#64) + 520#64 = sp - 520#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_528 (sp : BitVec 64) : (sp - 1040#64) + 528#64 = sp - 512#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_536 (sp : BitVec 64) : (sp - 1040#64) + 536#64 = sp - 504#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_544 (sp : BitVec 64) : (sp - 1040#64) + 544#64 = sp - 496#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_552 (sp : BitVec 64) : (sp - 1040#64) + 552#64 = sp - 488#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_560 (sp : BitVec 64) : (sp - 1040#64) + 560#64 = sp - 480#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_568 (sp : BitVec 64) : (sp - 1040#64) + 568#64 = sp - 472#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_576 (sp : BitVec 64) : (sp - 1040#64) + 576#64 = sp - 464#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_584 (sp : BitVec 64) : (sp - 1040#64) + 584#64 = sp - 456#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1024_add_8 (sp : BitVec 64) : (sp - 1024#64) + 8#64 = sp - 1016#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1024_add_16 (sp : BitVec 64) : (sp - 1024#64) + 16#64 = sp - 1008#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1024_add_24 (sp : BitVec 64) : (sp - 1024#64) + 24#64 = sp - 1000#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1008_add_8 (sp : BitVec 64) : (sp - 1008#64) + 8#64 = sp - 1000#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1008_add_16 (sp : BitVec 64) : (sp - 1008#64) + 16#64 = sp - 992#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1008_add_24 (sp : BitVec 64) : (sp - 1008#64) + 24#64 = sp - 984#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_992_add_8 (sp : BitVec 64) : (sp - 992#64) + 8#64 = sp - 984#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_976_add_8 (sp : BitVec 64) : (sp - 976#64) + 8#64 = sp - 968#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_976_add_16 (sp : BitVec 64) : (sp - 976#64) + 16#64 = sp - 960#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_976_add_24 (sp : BitVec 64) : (sp - 976#64) + 24#64 = sp - 952#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_968_add_8 (sp : BitVec 64) : (sp - 968#64) + 8#64 = sp - 960#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_960_add_8 (sp : BitVec 64) : (sp - 960#64) + 8#64 = sp - 952#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_544_add_8 (sp : BitVec 64) : (sp - 544#64) + 8#64 = sp - 536#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_544_add_16 (sp : BitVec 64) : (sp - 544#64) + 16#64 = sp - 528#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_544_add_24 (sp : BitVec 64) : (sp - 544#64) + 24#64 = sp - 520#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_528_add_8 (sp : BitVec 64) : (sp - 528#64) + 8#64 = sp - 520#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_512_add_8' (sp : BitVec 64) : (sp - 512#64) + 8#64 = sp - 504#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_512_add_16' (sp : BitVec 64) : (sp - 512#64) + 16#64 = sp - 496#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_512_add_24' (sp : BitVec 64) : (sp - 512#64) + 24#64 = sp - 488#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_496_add_8' (sp : BitVec 64) : (sp - 496#64) + 8#64 = sp - 488#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_480_add_8 (sp : BitVec 64) : (sp - 480#64) + 8#64 = sp - 472#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_480_add_16 (sp : BitVec 64) : (sp - 480#64) + 16#64 = sp - 464#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_480_add_24 (sp : BitVec 64) : (sp - 480#64) + 24#64 = sp - 456#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_464_add_8 (sp : BitVec 64) : (sp - 464#64) + 8#64 = sp - 456#64 := by bv_omega

private theorem wordsAt_10_sp_1552 (sp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 : BitVec 64) :
    wordsAt (sp - 1552#64) [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9] =
    (((sp - 1552#64) ↦₆₄ v0) ∗ ((sp - 1544#64) ↦₆₄ v1) ∗ ((sp - 1536#64) ↦₆₄ v2) ∗
     ((sp - 1528#64) ↦₆₄ v3) ∗ ((sp - 1520#64) ↦₆₄ v4) ∗ ((sp - 1512#64) ↦₆₄ v5) ∗
     ((sp - 1504#64) ↦₆₄ v6) ∗ ((sp - 1496#64) ↦₆₄ v7) ∗ ((sp - 1488#64) ↦₆₄ v8) ∗
     ((sp - 1480#64) ↦₆₄ v9)) := by simp only [wordsAt_10, arm64_norm]

private theorem wordsAt_10_sp_544 (sp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 : BitVec 64) :
    wordsAt (sp - 544#64) [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9] =
    (((sp - 544#64) ↦₆₄ v0) ∗ ((sp - 536#64) ↦₆₄ v1) ∗ ((sp - 528#64) ↦₆₄ v2) ∗
     ((sp - 520#64) ↦₆₄ v3) ∗ ((sp - 512#64) ↦₆₄ v4) ∗ ((sp - 504#64) ↦₆₄ v5) ∗
     ((sp - 496#64) ↦₆₄ v6) ∗ ((sp - 488#64) ↦₆₄ v7) ∗ ((sp - 480#64) ↦₆₄ v8) ∗
     ((sp - 472#64) ↦₆₄ v9)) := by simp only [wordsAt_10, arm64_norm]

private theorem wordsAt_12_sp_1040 (sp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : BitVec 64) :
    wordsAt (sp - 1040#64) [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11] =
    (((sp - 1040#64) ↦₆₄ v0) ∗ ((sp - 1032#64) ↦₆₄ v1) ∗ ((sp - 1024#64) ↦₆₄ v2) ∗
     ((sp - 1016#64) ↦₆₄ v3) ∗ ((sp - 1008#64) ↦₆₄ v4) ∗ ((sp - 1000#64) ↦₆₄ v5) ∗
     ((sp - 992#64) ↦₆₄ v6) ∗ ((sp - 984#64) ↦₆₄ v7) ∗ ((sp - 976#64) ↦₆₄ v8) ∗
     ((sp - 968#64) ↦₆₄ v9) ∗ ((sp - 960#64) ↦₆₄ v10) ∗ ((sp - 952#64) ↦₆₄ v11)) := by simp only [wordsAt_12, arm64_norm]

private theorem wordsAt_12_sp_544 (sp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : BitVec 64) :
    wordsAt (sp - 544#64) [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11] =
    (((sp - 544#64) ↦₆₄ v0) ∗ ((sp - 536#64) ↦₆₄ v1) ∗ ((sp - 528#64) ↦₆₄ v2) ∗
     ((sp - 520#64) ↦₆₄ v3) ∗ ((sp - 512#64) ↦₆₄ v4) ∗ ((sp - 504#64) ↦₆₄ v5) ∗
     ((sp - 496#64) ↦₆₄ v6) ∗ ((sp - 488#64) ↦₆₄ v7) ∗ ((sp - 480#64) ↦₆₄ v8) ∗
     ((sp - 472#64) ↦₆₄ v9) ∗ ((sp - 464#64) ↦₆₄ v10) ∗ ((sp - 456#64) ↦₆₄ v11)) := by simp only [wordsAt_12, arm64_norm]

def recvCt1SavedCells (s0 : State) : SepProp :=
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)

theorem recvCt1SavedCells_entails_memRegion_64 (s0 : State) :
    recvCt1SavedCells s0 ⊢ memRegion (s0.sp - 64#64) 64 := by
  unfold recvCt1SavedCells
  have heq :
      (((s0.sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) =
      wordsAt (s0.sp - 64#64)
        [s0.readReg64 .fp, s0.readReg64 .lr, s0.readReg64 .x28, s0.readReg64 .x23,
         s0.readReg64 .x22, s0.readReg64 .x21, s0.readReg64 .x20, s0.readReg64 .x19] := by
    simp only [wordsAt_8, arm64_norm]
  rw [heq]
  exact wordsAt_entails_memRegion _ (s0.sp - 64#64) 64 rfl

theorem stackAt_1568_split (sp : BitVec 64) :
    stackAt sp headerSentRecvCt1ChunkStack =
      stackAt (sp - 1568#64) polyDecoderDecodedMessageStack ∗
      memRegion (sp - 1568#64) 8 ∗
      memRegion (sp - 1560#64) 8 ∗
      memRegion (sp - 1552#64) 80 ∗
      memRegion (sp - 1472#64) 8 ∗
      memRegion (sp - 1464#64) 400 ∗
      memRegion (sp - 1064#64) 24 ∗
      memRegion (sp - 1040#64) 96 ∗
      memRegion (sp - 944#64) 400 ∗
      memRegion (sp - 544#64) 480 ∗
      memRegion (sp - 64#64) 64 := by
  change memRegion (sp - 18624#64) 18624 =
    memRegion (sp - 1568#64 - 17056#64) 17056 ∗ _
  have hsub : sp - 1568#64 - 17056#64 = sp - 18624#64 := by bv_omega
  rw [hsub,
      ProofLib.memRegion_split' (b := sp - 18624#64) (n := 17056) (k := 1568) (b' := sp - 1568#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 1568#64) (n := 8) (k := 1560) (b' := sp - 1560#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 1560#64) (n := 8) (k := 1552) (b' := sp - 1552#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 1552#64) (n := 80) (k := 1472) (b' := sp - 1472#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 1472#64) (n := 8) (k := 1464) (b' := sp - 1464#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 1464#64) (n := 400) (k := 1064) (b' := sp - 1064#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 1064#64) (n := 24) (k := 1040) (b' := sp - 1040#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 1040#64) (n := 96) (k := 944) (b' := sp - 944#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 944#64) (n := 400) (k := 544) (b' := sp - 544#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 544#64) (n := 480) (k := 64) (b' := sp - 64#64) rfl (by bv_omega) (by decide)]

theorem stackAt_decodedMessage_to_addChunk (fsp : BitVec 64) :
    stackAt fsp polyDecoderDecodedMessageStack =
      memRegion (fsp - 17056#64) 12752 ∗ stackAt fsp addChunkStack := by
  change memRegion (fsp - 17056#64) 17056 =
    memRegion (fsp - 17056#64) 12752 ∗ memRegion (fsp - 4304#64) 4304
  exact ProofLib.memRegion_split' (b := fsp - 17056#64) (n := 12752) (k := 4304)
    (b' := fsp - 4304#64) rfl (by bv_omega) (by decide)

theorem stackAt_decodedMessage_from_addChunk (fsp : BitVec 64) :
    memRegion (fsp - 17056#64) 12752 ∗ stackAt fsp addChunkStack ⊢
      stackAt fsp polyDecoderDecodedMessageStack :=
  Entails.of_eq (stackAt_decodedMessage_to_addChunk fsp).symm

theorem stackAt_decodedMessage_to_dropPoly16 (fsp : BitVec 64) :
    stackAt fsp polyDecoderDecodedMessageStack =
      memRegion (fsp - 17056#64) 12928 ∗ stackAt fsp dropGluePoly16Stack := by
  change memRegion (fsp - 17056#64) 17056 =
    memRegion (fsp - 17056#64) 12928 ∗ memRegion (fsp - 4128#64) 4128
  exact ProofLib.memRegion_split' (b := fsp - 17056#64) (n := 12928) (k := 4128)
    (b' := fsp - 4128#64) rfl (by bv_omega) (by decide)

theorem stackAt_decodedMessage_from_dropPoly16 (fsp : BitVec 64) :
    memRegion (fsp - 17056#64) 12928 ∗ stackAt fsp dropGluePoly16Stack ⊢
      stackAt fsp polyDecoderDecodedMessageStack :=
  Entails.of_eq (stackAt_decodedMessage_to_dropPoly16 fsp).symm

theorem stackAt_1568_rejoin (s0 : State) (w0 w8 : BitVec 64)
    (ws10 : List (BitVec 64)) (hws10 : 8 * ws10.length = 80) :
    stackAt (s0.sp - 1568#64) polyDecoderDecodedMessageStack ∗
      ((s0.sp - 1568#64) ↦₆₄ w0) ∗
      ((s0.sp - 1560#64) ↦₆₄ w8) ∗
      wordsAt (s0.sp - 1552#64) ws10 ∗
      memRegion (s0.sp - 1472#64) 8 ∗
      memRegion (s0.sp - 1464#64) 400 ∗
      memRegion (s0.sp - 1064#64) 24 ∗
      memRegion (s0.sp - 1040#64) 96 ∗
      memRegion (s0.sp - 944#64) 880 ∗
      recvCt1SavedCells s0 ⊢
    stackAt s0.sp headerSentRecvCt1ChunkStack := by
  have hw0 := ProofLib.pointsTo64_entails_memRegion (s0.sp - 1568#64) w0
  have hw8 := ProofLib.pointsTo64_entails_memRegion (s0.sp - 1560#64) w8
  have h10 := wordsAt_entails_memRegion ws10 (s0.sp - 1552#64) 80 hws10
  have hsaved := recvCt1SavedCells_entails_memRegion_64 s0
  refine Entails.trans (sepConj_mono_right (sepConj_mono hw0 (sepConj_mono hw8 (sepConj_mono h10
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right hsaved))))))))) ?_
  rw [stackAt_1568_split s0.sp,
      ProofLib.memRegion_split' (b := s0.sp - 944#64) (n := 400) (k := 480)
        (b' := s0.sp - 544#64) rfl (by bv_omega) (by decide)]
  exact Entails.of_eq (by ac_rfl)

theorem unchunkedEkSentAt_400_eq (A : RustAlloc) {F : ShaCompress}
    (stA : BitVec 64) (st : Unchunked.SendEk.EkSent (spqrAuthApi F)) :
    unchunkedEkSentAt A (stA + 400#64) st =
      authenticatorAt A (stA + 400#64) st.auth ∗
      vecU8 A (stA + 448#64) st.dk ∗
      ((stA + 472#64) ↦₆₄ st.epoch) := by
  unfold unchunkedEkSentAt
  simp only [BitVec.add_assoc, arm64_norm]

theorem stA_880_rejoin (stA : BitVec 64) (g : AuthWords) (gdk : VecWords) (ep : BitVec 64) :
    memRegion stA 400 ∗
      wordsAt (stA + 400#64) (authWordsList g) ∗
      wordsAt (stA + 448#64) (vecWordsList gdk) ∗
      ((stA + 472#64) ↦₆₄ ep) ∗
      memRegion (stA + 480#64) 400 ⊢
    memRegion stA 880 := by
  have h1 : wordsAt (stA + 400#64) (authWordsList g) ⊢ memRegion (stA + 400#64) 48 :=
    wordsAt_entails_memRegion (authWordsList g) (stA + 400#64) 48 rfl
  have h2 : wordsAt (stA + 448#64) (vecWordsList gdk) ⊢ memRegion (stA + 448#64) 24 :=
    wordsAt_entails_memRegion (vecWordsList gdk) (stA + 448#64) 24 rfl
  have h3 : ((stA + 472#64) ↦₆₄ ep) ⊢ memRegion (stA + 472#64) 8 :=
    ProofLib.pointsTo64_entails_memRegion (stA + 472#64) ep
  refine Entails.trans (sepConj_mono_right (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono_left h3)))) ?_
  rw [← ProofLib.memRegion_split' (b := stA + 472#64) (n := 8) (k := 400) (b' := stA + 480#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := stA + 448#64) (n := 24) (k := 408) (b' := stA + 472#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := stA + 400#64) (n := 48) (k := 432) (b' := stA + 448#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := stA) (n := 400) (k := 480) (b' := stA + 400#64) rfl rfl (by decide)]
  exact Entails.refl _

theorem cap_add_one_beq_zero_false {cap : BitVec 64} (hlt : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  have hne : cap ≠ BitVec.allOnes 64 := by
    intro heq
    subst heq
    revert hlt
    decide
  exact ep_add_one_beq_zero_false hne

theorem sp_944_headerSent_recompose (A : RustAlloc) {F : ShaCompress}
    (sp : BitVec 64)
    (st outSt : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (dec1 : PolyDecoder)
    (hout : outSt = { uc := st.uc, sending_ek := st.sending_ek, receiving_ct1 := dec1 })
    (g : AuthWords) (gdk : VecWords) :
    polyEncoderAt A (sp - 944#64) st.sending_ek ∗
      wordsAt (sp - 544#64) (authWordsList g ++ vecWordsList gdk ++ [st.uc.epoch]) ∗
      relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g)) ∗
      relocatedHeap (fun dst => vecU8 A dst st.uc.dk) (wordsBytes (vecWordsList gdk)) ∗
      polyDecoderAt A (sp - 464#64) dec1 ⊢
    chunkedHeaderSentAt A (sp - 944#64) outSt := by
  subst hout
  have hsplit1 :
      wordsAt (sp - 544#64) (authWordsList g ++ vecWordsList gdk ++ [st.uc.epoch]) =
        wordsAt (sp - 544#64) (authWordsList g) ∗
        wordsAt (sp - 496#64) (vecWordsList gdk) ∗
        ((sp - 472#64) ↦₆₄ st.uc.epoch) := by
    dsimp only [authWordsList, vecWordsList, List.append]
    simp only [wordsAt_10, wordsAt_6, wordsAt, wordsAt_cons_off, wordsAt_nil, sepConj_emp,
      BitVec.add_assoc, arm64_norm]
  have hauth :
      wordsAt (sp - 544#64) (authWordsList g) ∗
        relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g)) ⊢
      authenticatorAt A (sp - 544#64) st.uc.auth := by
    rw [wordsAt_eq_pointsToBytes]; exact relocatedHeap_recompose _ _ (sp - 544#64)
  have hdk :
      wordsAt (sp - 496#64) (vecWordsList gdk) ∗
        relocatedHeap (fun dst => vecU8 A dst st.uc.dk) (wordsBytes (vecWordsList gdk)) ⊢
      vecU8 A (sp - 496#64) st.uc.dk := by
    rw [wordsAt_eq_pointsToBytes]; exact relocatedHeap_recompose _ _ (sp - 496#64)
  unfold chunkedHeaderSentAt unchunkedEkSentAt
  have h1 : (sp - 944#64) + 400#64 = sp - 544#64 := by bv_omega
  have h2 : (sp - 944#64) + 480#64 = sp - 464#64 := by bv_omega
  have h3 : (sp - 544#64) + 48#64 = sp - 496#64 := by bv_omega
  have h4 : (sp - 544#64) + 72#64 = sp - 472#64 := by bv_omega
  rw [h1, h2, h3, h4, hsplit1]
  have hreord :
      polyEncoderAt A (sp - 944#64) st.sending_ek ∗
      (wordsAt (sp - 544#64) (authWordsList g) ∗
       wordsAt (sp - 496#64) (vecWordsList gdk) ∗
       ((sp - 472#64) ↦₆₄ st.uc.epoch)) ∗
      relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g)) ∗
      relocatedHeap (fun dst => vecU8 A dst st.uc.dk) (wordsBytes (vecWordsList gdk)) ∗
      polyDecoderAt A (sp - 464#64) dec1 =
      polyEncoderAt A (sp - 944#64) st.sending_ek ∗
      ((wordsAt (sp - 544#64) (authWordsList g) ∗
        relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g))) ∗
       (wordsAt (sp - 496#64) (vecWordsList gdk) ∗
        relocatedHeap (fun dst => vecU8 A dst st.uc.dk) (wordsBytes (vecWordsList gdk))) ∗
       ((sp - 472#64) ↦₆₄ st.uc.epoch)) ∗
      polyDecoderAt A (sp - 464#64) dec1 := by ac_rfl
  rw [hreord]
  exact sepConj_mono_right (sepConj_mono_left (sepConj_mono hauth (sepConj_mono_left hdk)))

theorem outA_done_recompose (A : RustAlloc) {F : ShaCompress}
    (outA : BitVec 64)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (ct1 : Bytes)
    (outRes : Chunked.SendEk.HeaderSentRecvChunk spqrPolyApi (spqrAuthApi F))
    (hout : outRes = .done { uc := { epoch := st.uc.epoch, auth := st.uc.auth, dk := st.uc.dk, ct1 := ct1 },
                             sending_ek := st.sending_ek })
    (g : AuthWords) (gdk gct1 : VecWords) :
    (outA ↦₆₄ 2#64) ∗
      polyEncoderAt A (outA + 8#64) st.sending_ek ∗
      wordsAt ((outA + 8#64) + 400#64) (authWordsList g ++ vecWordsList gdk ++ vecWordsList gct1) ∗
      relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g)) ∗
      relocatedHeap (fun dst => vecU8 A dst st.uc.dk) (wordsBytes (vecWordsList gdk)) ∗
      relocatedHeap (fun dst => vecU8 A dst ct1) (wordsBytes (vecWordsList gct1)) ∗
      ((outA + 504#64) ↦₆₄ st.uc.epoch) ∗
      memRegion (outA + 512#64) 368 ⊢
    headerSentRecvChunkAt A outA outRes := by
  subst hout
  have hsplit1 :
      wordsAt (outA + 408#64) (authWordsList g ++ vecWordsList gdk ++ vecWordsList gct1) =
        wordsAt (outA + 408#64) (authWordsList g) ∗
        wordsAt (outA + 456#64) (vecWordsList gdk) ∗
        wordsAt (outA + 480#64) (vecWordsList gct1) := by
    dsimp only [authWordsList, vecWordsList, List.append]
    simp only [wordsAt_12, wordsAt_6, wordsAt, wordsAt_cons_off, wordsAt_nil, sepConj_emp,
      BitVec.add_assoc, arm64_norm]
  have hauth :
      wordsAt (outA + 408#64) (authWordsList g) ∗
        relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g)) ⊢
      authenticatorAt A (outA + 408#64) st.uc.auth := by
    rw [wordsAt_eq_pointsToBytes]; exact relocatedHeap_recompose _ _ (outA + 408#64)
  have hdk :
      wordsAt (outA + 456#64) (vecWordsList gdk) ∗
        relocatedHeap (fun dst => vecU8 A dst st.uc.dk) (wordsBytes (vecWordsList gdk)) ⊢
      vecU8 A (outA + 456#64) st.uc.dk := by
    rw [wordsAt_eq_pointsToBytes]; exact relocatedHeap_recompose _ _ (outA + 456#64)
  have hct1 :
      wordsAt (outA + 480#64) (vecWordsList gct1) ∗
        relocatedHeap (fun dst => vecU8 A dst ct1) (wordsBytes (vecWordsList gct1)) ⊢
      vecU8 A (outA + 480#64) ct1 := by
    rw [wordsAt_eq_pointsToBytes]; exact relocatedHeap_recompose _ _ (outA + 480#64)
  dsimp only [headerSentRecvChunkAt]
  unfold chunkedCt1ReceivedAt unchunkedEkSentCt1ReceivedAt
  have h408 : (outA + 8#64) + 400#64 = outA + 408#64 := by bv_omega
  have h456 : (outA + 408#64) + 48#64 = outA + 456#64 := by bv_omega
  have h480 : (outA + 408#64) + 72#64 = outA + 480#64 := by bv_omega
  have h504 : (outA + 408#64) + 96#64 = outA + 504#64 := by bv_omega
  rw [h408, h456, h480, h504, hsplit1]
  have hreord :
      (outA ↦₆₄ 2#64) ∗
      polyEncoderAt A (outA + 8#64) st.sending_ek ∗
      (wordsAt (outA + 408#64) (authWordsList g) ∗
       wordsAt (outA + 456#64) (vecWordsList gdk) ∗
       wordsAt (outA + 480#64) (vecWordsList gct1)) ∗
      relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g)) ∗
      relocatedHeap (fun dst => vecU8 A dst st.uc.dk) (wordsBytes (vecWordsList gdk)) ∗
      relocatedHeap (fun dst => vecU8 A dst ct1) (wordsBytes (vecWordsList gct1)) ∗
      ((outA + 504#64) ↦₆₄ st.uc.epoch) ∗
      memRegion (outA + 512#64) 368 =
      (outA ↦₆₄ 2#64) ∗
      (polyEncoderAt A (outA + 8#64) st.sending_ek ∗
       ((wordsAt (outA + 408#64) (authWordsList g) ∗
         relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g))) ∗
        (wordsAt (outA + 456#64) (vecWordsList gdk) ∗
         relocatedHeap (fun dst => vecU8 A dst st.uc.dk) (wordsBytes (vecWordsList gdk))) ∗
        (wordsAt (outA + 480#64) (vecWordsList gct1) ∗
         relocatedHeap (fun dst => vecU8 A dst ct1) (wordsBytes (vecWordsList gct1))) ∗
        ((outA + 504#64) ↦₆₄ st.uc.epoch))) ∗
      memRegion (outA + 512#64) 368 := by ac_rfl
  rw [hreord]
  exact sepConj_mono_right (sepConj_mono_left (sepConj_mono_right
    (sepConj_mono hauth (sepConj_mono hdk (sepConj_mono_left hct1)))))

/-! ## 5. Branch 1 (`outMsg = none`, `entry + 128#64` = `0x5d97c` → `0x5da20` → `0x5da80`) -/

set_option maxHeartbeats 800000 in
theorem header_sent_recv_ct1_chunk_none {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr headerSentRecvCt1ChunkName + (bv% (ls_rel% "<spqr::v1::chunked::send_ek::HeaderSent>::recv_ct1_chunk" "memcpy"))) sessionMemcpyRegionSpec)
    (outA stA chunkA : BitVec 64)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk) (dec1 : PolyDecoder)
    (outRes : Chunked.SendEk.HeaderSentRecvChunk spqrPolyApi (spqrAuthApi F))
    (hout : outRes = .stillReceiving { uc := st.uc, sending_ek := st.sending_ek, receiving_ct1 := dec1 })
    (g : AuthWords) (gdk : VecWords)
    {s0 s : State} {P R : SepProp}
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp_align : ((s0.sp - 1568#64) &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (leavesProgAtExt b ext).fnAddr headerSentRecvCt1ChunkName + 128#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1568#64)
    (hx19 : s.readReg64 .x19 = outA) (hx20 : s.readReg64 .x20 = stA)
    (_hx21 : s.readReg64 .x21 = st.uc.epoch) (_hx22 : s.readReg64 .x22 = chunkA)
    (hx23 : s.readReg64 .x23 = s0.sp - 1040#64) (hx24 : s.readReg64 .x24 = s0.readReg64 .x24)
    (hx25 : s.readReg64 .x25 = s0.readReg64 .x25) (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27) (_hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hfp : s.readReg64 .fp = s0.sp - 64#64) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) (htrace : s.trace = s0.trace)
    (hP : P = (
      optVecU8At A (s0.sp - 1064#64) none ∗ polyDecoderAt A (s0.sp - 1464#64) dec1 ∗
      tokenInitAt b ∗ reduceTableAt b ∗ A.pool ∗
      stackAt (s0.sp - 1568#64) polyDecoderDecodedMessageStack ∗
      memRegion outA 880 ∗ polyEncoderAt A stA st.sending_ek ∗
      wordsAt (stA + 400#64) (authWordsList g) ∗
      relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g)) ∗
      wordsAt (stA + 448#64) (vecWordsList gdk) ∗
      relocatedHeap (fun dst => vecU8 A dst st.uc.dk) (wordsBytes (vecWordsList gdk)) ∗
      ((stA + 472#64) ↦₆₄ st.uc.epoch) ∗ memRegion (stA + 480#64) 400 ∗ chunkAt chunkA chunk ∗
      ((s0.sp - 1568#64) ↦₆₄ 0#64) ∗ ((s0.sp - 1560#64) ↦₆₄ st.uc.epoch) ∗
      wordsAt (s0.sp - 1552#64) (authWordsList g ++ vecWordsList gdk ++ [st.uc.epoch]) ∗
      memRegion (s0.sp - 1472#64) 8 ∗ memRegion (s0.sp - 1040#64) 96 ∗
      memRegion (s0.sp - 944#64) 400 ∗ memRegion (s0.sp - 544#64) 480 ∗ recvCt1SavedCells s0)) :
    SepWP (leavesProgAtExt b ext) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ ⌜sf.trace = s0.trace⌝ ∗
            headerSentRecvChunkAt A outA outRes ∗ memRegion stA chunkedHeaderSentSize ∗
            chunkAt chunkA chunk ∗ tokenInitAt b ∗ reduceTableAt b ∗
            A.pool ∗ stackAt s0.sp headerSentRecvCt1ChunkStack ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  rw [hP]
  have hfn : libsignalSessionCode.fnOff headerSentRecvCt1ChunkName = 0x58504 :=
    headerSentRecvCt1Chunk_fnOff
  code_fetches libsignalSessionCode spqrHeaderSentRecvCt1ChunkBin b
    (Rust.withPanics ext) hfn 0x58504 452
  dsimp only [leavesProgAtExt, tripleRatchetProgAtExt, headerSentRecvCt1ChunkName,
    chunkedHeaderSentSize, optVecU8At, noneCap, AsmConstants.optionVecNoneWord,
    BitVec.ofNat_eq_ofNat] at *
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::send_ek::HeaderSent>::recv_ct1_chunk" = entry
  examples_hide_fetches
  wp_conv_pre =>
    rw [ProofLib.memRegion_split' (b := s0.sp - 544#64) (n := 80) (k := 400)
        (b' := s0.sp - 464#64) rfl (by bv_omega) (by decide)]
    simp only [sepConj_assoc]
  wp_steps
  refine call_memcpy_relocate_cs hmemcpy (s0 := s0)
    (Relocatable.of_polyDecoderAt A dec1) (s0.sp - 464#64) (s0.sp - 1464#64)
    (ret_pc := entry + 312#64) (sp_call := s0.sp - 1568#64)
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm, hsp]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htrace])
    (by simp only [Reg.x0, arm64_norm, hsp]) (by simp only [Reg.x1, arm64_norm, hsp])
    (by simp only [Reg.x2, arm64_norm]) (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 htr1 => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [arm64_norm, hx19, hx20, hx23, hx24, hx25, hx26, hx27, hfp, hvregs]
    at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
  have hst_auth :
      wordsAt (stA + 400#64) (authWordsList g) =
      (((stA + 400#64) ↦₆₄ g.v1.w0) ∗ ((stA + 408#64) ↦₆₄ g.v1.w1) ∗
       ((stA + 416#64) ↦₆₄ g.v1.w2) ∗ ((stA + 424#64) ↦₆₄ g.v2.w0) ∗
       ((stA + 432#64) ↦₆₄ g.v2.w1) ∗ ((stA + 440#64) ↦₆₄ g.v2.w2)) := by
    dsimp only [authWordsList]; simp only [wordsAt_6, BitVec.add_assoc, arm64_norm]
  have hst_dk :
      wordsAt (stA + 448#64) (vecWordsList gdk) =
      (((stA + 448#64) ↦₆₄ gdk.w0) ∗ ((stA + 456#64) ↦₆₄ gdk.w1) ∗
       ((stA + 464#64) ↦₆₄ gdk.w2)) := by
    dsimp only [vecWordsList]
    simp only [wordsAt, wordsAt_cons_off, wordsAt_nil, sepConj_emp, BitVec.add_assoc, arm64_norm]
  have hsp_544_words :
      wordsAt (s0.sp - 544#64) (authWordsList g ++ vecWordsList gdk ++ [st.uc.epoch]) =
      (((s0.sp - 544#64) ↦₆₄ g.v1.w0) ∗ ((s0.sp - 536#64) ↦₆₄ g.v1.w1) ∗
       ((s0.sp - 528#64) ↦₆₄ g.v1.w2) ∗ ((s0.sp - 520#64) ↦₆₄ g.v2.w0) ∗
       ((s0.sp - 512#64) ↦₆₄ g.v2.w1) ∗ ((s0.sp - 504#64) ↦₆₄ g.v2.w2) ∗
       ((s0.sp - 496#64) ↦₆₄ gdk.w0) ∗ ((s0.sp - 488#64) ↦₆₄ gdk.w1) ∗
       ((s0.sp - 480#64) ↦₆₄ gdk.w2) ∗ ((s0.sp - 472#64) ↦₆₄ st.uc.epoch)) := by
    dsimp only [authWordsList, vecWordsList, List.append]
    simp only [wordsAt_10, arm64_norm]
  refine SepWP.fold (cells_10_unfold (s0.sp - 544#64)) (by sep_focus) ?_
  wp_pull_exists
  wp_conv_pre => rw [hst_auth, hst_dk, wordsAt_10_sp_544]; simp only [sepConj_assoc]
  wp_steps
  refine SepWP.fold (Entails.of_eq hst_auth.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hst_dk.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hsp_544_words.symm) (by sep_focus) ?_
  refine call_memcpy_relocate_cs hmemcpy (s0 := s0)
    (Relocatable.of_polyEncoderAt A st.sending_ek) (s0.sp - 944#64) stA
    (ret_pc := entry + 352#64) (sp_call := s0.sp - 1568#64)
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm, hsp1]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [trace_writeVReg128, arm64_norm, htr1])
    (by simp only [Reg.x0, arm64_norm, hsp1]) (by simp only [Reg.x1, arm64_norm, hx20_1])
    (by simp only [Reg.x2, arm64_norm]) (by sep_focus)
    (fun sf2 hpc2 hrun2 hsp2 hcs2 htr2 => ?_)
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
  simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1]
    at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
  let outSt : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F) :=
    { uc := st.uc, sending_ek := st.sending_ek, receiving_ct1 := dec1 }
  refine SepWP.fold (stA_880_rejoin stA g gdk st.uc.epoch) (by sep_focus) ?_
  refine SepWP.fold (sp_944_headerSent_recompose A s0.sp st outSt dec1 rfl g gdk) (by sep_focus) ?_
  wp_steps
  refine call_memcpy_relocate_cs hmemcpy (s0 := s0)
    (Relocatable.of_chunkedHeaderSentAt A outSt) outA (s0.sp - 944#64)
    (ret_pc := entry + 368#64) (sp_call := s0.sp - 1568#64)
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm, hsp2]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr2])
    (by simp only [Reg.x0, arm64_norm, hx19_2]) (by simp only [Reg.x1, arm64_norm, hsp2])
    (by simp only [Reg.x2, arm64_norm]) (by sep_focus)
    (fun sf3 hpc3 hrun3 hsp3 hcs3 htr3 => ?_)
  rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hfp_3, hvregs_3⟩
  simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2]
    at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hfp_3 hvregs_3
  have hnone_24 :
      ((s0.sp - 1064#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (s0.sp - 1056#64) 16 ⊢
      memRegion (s0.sp - 1064#64) 24 := by
    rw [ProofLib.memRegion_split' (b := s0.sp - 1064#64) (n := 8) (k := 16)
        (b' := s0.sp - 1056#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _)
  refine SepWP.fold hnone_24 (by sep_focus) ?_
  wp_conv_pre => unfold recvCt1SavedCells
  wp_steps
  refine SepWP.fold (stackAt_1568_rejoin s0 0#64 st.uc.epoch
    (authWordsList g ++ vecWordsList gdk ++ [st.uc.epoch]) rfl)
    (by dsimp only [recvCt1SavedCells]; sep_focus) ?_
  subst hout
  dsimp only [headerSentRecvChunkAt]
  wp_done

/-! ## 6. Branch 2 (`outMsg = some ct1`, `entry + 128#64` = `0x5d97c` → `0x5da1c`) -/

set_option maxHeartbeats 800000 in
theorem header_sent_recv_ct1_chunk_some {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr headerSentRecvCt1ChunkName + (bv% (ls_rel% "<spqr::v1::chunked::send_ek::HeaderSent>::recv_ct1_chunk" "memcpy"))) sessionMemcpyRegionSpec)
    (hpt16 : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr headerSentRecvCt1ChunkName + 18446744073709478940#64)
      (dropGlueSortedSetPt16Spec A))
    (outA stA chunkA : BitVec 64)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk) (dec1 : PolyDecoder) (ct1 : Bytes)
    (outRes : Chunked.SendEk.HeaderSentRecvChunk spqrPolyApi (spqrAuthApi F))
    (hout : outRes = .done { uc := { epoch := st.uc.epoch, auth := st.uc.auth, dk := st.uc.dk, ct1 := ct1 },
                             sending_ek := st.sending_ek })
    (g : AuthWords) (gdk : VecWords)
    {s0 s : State} {P R : SepProp}
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp_align : ((s0.sp - 1568#64) &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (leavesProgAtExt b ext).fnAddr headerSentRecvCt1ChunkName + 128#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1568#64)
    (hx19 : s.readReg64 .x19 = outA) (hx20 : s.readReg64 .x20 = stA)
    (hx21 : s.readReg64 .x21 = st.uc.epoch) (_hx22 : s.readReg64 .x22 = chunkA)
    (hx23 : s.readReg64 .x23 = s0.sp - 1040#64) (hx24 : s.readReg64 .x24 = s0.readReg64 .x24)
    (hx25 : s.readReg64 .x25 = s0.readReg64 .x25) (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27) (_hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hfp : s.readReg64 .fp = s0.sp - 64#64) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) (htrace : s.trace = s0.trace)
    (hP : P = (
      optVecU8At A (s0.sp - 1064#64) (some ct1) ∗ polyDecoderAt A (s0.sp - 1464#64) dec1 ∗
      tokenInitAt b ∗ reduceTableAt b ∗ A.pool ∗
      stackAt (s0.sp - 1568#64) polyDecoderDecodedMessageStack ∗
      memRegion outA 880 ∗ polyEncoderAt A stA st.sending_ek ∗
      wordsAt (stA + 400#64) (authWordsList g) ∗
      relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g)) ∗
      wordsAt (stA + 448#64) (vecWordsList gdk) ∗
      relocatedHeap (fun dst => vecU8 A dst st.uc.dk) (wordsBytes (vecWordsList gdk)) ∗
      ((stA + 472#64) ↦₆₄ st.uc.epoch) ∗ memRegion (stA + 480#64) 400 ∗ chunkAt chunkA chunk ∗
      ((s0.sp - 1568#64) ↦₆₄ 0#64) ∗ ((s0.sp - 1560#64) ↦₆₄ st.uc.epoch) ∗
      wordsAt (s0.sp - 1552#64) (authWordsList g ++ vecWordsList gdk ++ [st.uc.epoch]) ∗
      memRegion (s0.sp - 1472#64) 8 ∗ memRegion (s0.sp - 1040#64) 96 ∗
      memRegion (s0.sp - 944#64) 400 ∗ memRegion (s0.sp - 544#64) 480 ∗ recvCt1SavedCells s0)) :
    SepWP (leavesProgAtExt b ext) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ ⌜sf.trace = s0.trace⌝ ∗
            headerSentRecvChunkAt A outA outRes ∗ memRegion stA chunkedHeaderSentSize ∗
            chunkAt chunkA chunk ∗ tokenInitAt b ∗ reduceTableAt b ∗
            A.pool ∗ stackAt s0.sp headerSentRecvCt1ChunkStack ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  rw [hP]
  have hfn : libsignalSessionCode.fnOff headerSentRecvCt1ChunkName = 0x58504 :=
    headerSentRecvCt1Chunk_fnOff
  code_fetches libsignalSessionCode spqrHeaderSentRecvCt1ChunkBin b
    (Rust.withPanics ext) hfn 0x58504 452
  dsimp only [leavesProgAtExt, tripleRatchetProgAtExt, headerSentRecvCt1ChunkName,
    chunkedHeaderSentSize, optVecU8At, BitVec.ofNat_eq_ofNat] at *
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::send_ek::HeaderSent>::recv_ct1_chunk" = entry
  examples_hide_fetches
  refine SepWP.fold (vecU8_extract_with_cap_lt A (s0.sp - 1064#64) ct1) (by sep_focus) ?_
  wp_pull_exists; rename_i gct1
  wp_focus_pure; intro hcap_lt
  have hadds_z := cap_add_one_beq_zero_false hcap_lt
  have hct1_words :
      wordsAt (s0.sp - 1064#64) (vecWordsList gct1) =
      (((s0.sp - 1064#64) ↦₆₄ gct1.w0) ∗ ((s0.sp - 1056#64) ↦₆₄ gct1.w1) ∗
       ((s0.sp - 1048#64) ↦₆₄ gct1.w2)) := by
    dsimp only [vecWordsList]
    simp only [wordsAt, wordsAt_cons_off, wordsAt_nil, sepConj_emp, arm64_norm]
  have hsp_1552_words :
      wordsAt (s0.sp - 1552#64) (authWordsList g ++ vecWordsList gdk ++ [st.uc.epoch]) =
      (((s0.sp - 1552#64) ↦₆₄ g.v1.w0) ∗ ((s0.sp - 1544#64) ↦₆₄ g.v1.w1) ∗
       ((s0.sp - 1536#64) ↦₆₄ g.v1.w2) ∗ ((s0.sp - 1528#64) ↦₆₄ g.v2.w0) ∗
       ((s0.sp - 1520#64) ↦₆₄ g.v2.w1) ∗ ((s0.sp - 1512#64) ↦₆₄ g.v2.w2) ∗
       ((s0.sp - 1504#64) ↦₆₄ gdk.w0) ∗ ((s0.sp - 1496#64) ↦₆₄ gdk.w1) ∗
       ((s0.sp - 1488#64) ↦₆₄ gdk.w2) ∗ ((s0.sp - 1480#64) ↦₆₄ st.uc.epoch)) := by
    dsimp only [authWordsList, vecWordsList, List.append]
    simp only [wordsAt_10, arm64_norm]
  have hst_auth :
      wordsAt (stA + 400#64) (authWordsList g) =
      (((stA + 400#64) ↦₆₄ g.v1.w0) ∗ ((stA + 408#64) ↦₆₄ g.v1.w1) ∗
       ((stA + 416#64) ↦₆₄ g.v1.w2) ∗ ((stA + 424#64) ↦₆₄ g.v2.w0) ∗
       ((stA + 432#64) ↦₆₄ g.v2.w1) ∗ ((stA + 440#64) ↦₆₄ g.v2.w2)) := by
    dsimp only [authWordsList]; simp only [wordsAt_6, BitVec.add_assoc, arm64_norm]
  have hst_dk :
      wordsAt (stA + 448#64) (vecWordsList gdk) =
      (((stA + 448#64) ↦₆₄ gdk.w0) ∗ ((stA + 456#64) ↦₆₄ gdk.w1) ∗
       ((stA + 464#64) ↦₆₄ gdk.w2)) := by
    dsimp only [vecWordsList]
    simp only [wordsAt, wordsAt_cons_off, wordsAt_nil, sepConj_emp, BitVec.add_assoc, arm64_norm]
  have hsp_544_words12 :
      wordsAt ((s0.sp - 944#64) + 400#64) (authWordsList g ++ vecWordsList gdk ++ vecWordsList gct1) =
      (((s0.sp - 544#64) ↦₆₄ g.v1.w0) ∗ ((s0.sp - 536#64) ↦₆₄ g.v1.w1) ∗
       ((s0.sp - 528#64) ↦₆₄ g.v1.w2) ∗ ((s0.sp - 520#64) ↦₆₄ g.v2.w0) ∗
       ((s0.sp - 512#64) ↦₆₄ g.v2.w1) ∗ ((s0.sp - 504#64) ↦₆₄ g.v2.w2) ∗
       ((s0.sp - 496#64) ↦₆₄ gdk.w0) ∗ ((s0.sp - 488#64) ↦₆₄ gdk.w1) ∗
       ((s0.sp - 480#64) ↦₆₄ gdk.w2) ∗ ((s0.sp - 472#64) ↦₆₄ gct1.w0) ∗
       ((s0.sp - 464#64) ↦₆₄ gct1.w1) ∗ ((s0.sp - 456#64) ↦₆₄ gct1.w2)) := by
    dsimp only [authWordsList, vecWordsList, List.append]
    simp only [wordsAt_12, arm64_norm]
  have hsp_1040_words12 :
      wordsAt (s0.sp - 1040#64) (authWordsList g ++ vecWordsList gdk ++ vecWordsList gct1) =
      (((s0.sp - 1040#64) ↦₆₄ g.v1.w0) ∗ ((s0.sp - 1032#64) ↦₆₄ g.v1.w1) ∗
       ((s0.sp - 1024#64) ↦₆₄ g.v1.w2) ∗ ((s0.sp - 1016#64) ↦₆₄ g.v2.w0) ∗
       ((s0.sp - 1008#64) ↦₆₄ g.v2.w1) ∗ ((s0.sp - 1000#64) ↦₆₄ g.v2.w2) ∗
       ((s0.sp - 992#64) ↦₆₄ gdk.w0) ∗ ((s0.sp - 984#64) ↦₆₄ gdk.w1) ∗
       ((s0.sp - 976#64) ↦₆₄ gdk.w2) ∗ ((s0.sp - 968#64) ↦₆₄ gct1.w0) ∗
       ((s0.sp - 960#64) ↦₆₄ gct1.w1) ∗ ((s0.sp - 952#64) ↦₆₄ gct1.w2)) := by
    dsimp only [authWordsList, vecWordsList, List.append]
    simp only [wordsAt_12, arm64_norm]
  wp_conv_pre =>
    rw [hct1_words, hsp_1552_words, hst_auth, hst_dk,
        ProofLib.memRegion_split' (b := outA) (n := 8) (k := 872) (b' := outA + 8#64) rfl rfl (by decide),
        ProofLib.memRegion_split' (b := outA + 8#64) (n := 496) (k := 376) (b' := outA + 504#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := outA + 504#64) (n := 8) (k := 368) (b' := outA + 512#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 944#64) (n := 8) (k := 392)
          (b' := s0.sp - 936#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 544#64) (n := 96) (k := 384)
          (b' := s0.sp - 448#64) rfl (by bv_omega) (by decide)]
    simp only [sepConj_assoc]
  refine SepWP.fold (cells_1_unfold outA) (by sep_focus) ?_
  refine SepWP.fold (cells_1_unfold (outA + 504#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_1_unfold (s0.sp - 944#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_12_unfold (s0.sp - 1040#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_12_unfold (s0.sp - 544#64)) (by sep_focus) ?_
  wp_pull_exists
  wp_conv_pre => rw [wordsAt_12_sp_1040, wordsAt_12_sp_544]; simp only [sepConj_assoc]
  wp_steps
  refine SepWP.fold (Entails.of_eq hsp_1552_words.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hst_auth.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hst_dk.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hct1_words.symm) (by sep_focus) ?_
  refine SepWP.fold (wordsAt_entails_memRegion (vecWordsList gct1) (s0.sp - 1064#64) 24 rfl) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hsp_1040_words12.symm) (by sep_focus) ?_
  refine SepWP.fold (wordsAt_entails_memRegion (authWordsList g ++ vecWordsList gdk ++ vecWordsList gct1) (s0.sp - 1040#64) 96 rfl) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hsp_544_words12.symm) (by sep_focus) ?_
  refine SepWP.fold (cell_0_rejoin_400 s0.sp 944#64 936#64 st.uc.epoch (by bv_omega)) (by sep_focus) ?_
  refine call_memcpy_relocate_cs hmemcpy (s0 := s0)
    (Relocatable.of_polyEncoderAt A st.sending_ek) (s0.sp - 944#64) stA
    (ret_pc := entry + 232#64) (sp_call := s0.sp - 1568#64)
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm, hsp]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [trace_writeVReg128, arm64_norm, htrace])
    (by simp only [Reg.x0, arm64_norm, hsp]) (by simp only [Reg.x1, arm64_norm, hx20])
    (by simp only [Reg.x2, arm64_norm]) (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 htr1 => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [arm64_norm, hx19, hx20, hx21, hx23, hx24, hx25, hx26, hx27, hfp, hvregs]
    at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
  refine SepWP.fold (stA_880_rejoin stA g gdk st.uc.epoch) (by sep_focus) ?_
  wp_steps
  refine call_memcpy_relocate_cs hmemcpy (s0 := s0)
    (Relocatable.of_polyEncoder_and_words12 A st.sending_ek
      (authWordsList g ++ vecWordsList gdk ++ vecWordsList gct1) rfl)
    (outA + 8#64) (s0.sp - 944#64)
    (ret_pc := entry + 248#64) (sp_call := s0.sp - 1568#64)
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm, hsp1]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr1])
    (by simp only [Reg.x0, arm64_norm, hx19_1]) (by simp only [Reg.x1, arm64_norm, hsp1])
    (by simp only [Reg.x2, arm64_norm]) (by sep_focus)
    (fun sf2 hpc2 hrun2 hsp2 hcs2 htr2 => ?_)
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
  simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1]
    at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
  have hrejoin_880 :
      memRegion (s0.sp - 944#64) 496 ∗ memRegion (s0.sp - 448#64) 384 ⊢
      memRegion (s0.sp - 944#64) 880 := by
    rw [← ProofLib.memRegion_split' (b := s0.sp - 944#64) (n := 496) (k := 384)
        (b' := s0.sp - 448#64) rfl (by bv_omega) (by decide)]
    exact Entails.refl _
  refine SepWP.fold hrejoin_880 (by sep_focus) ?_
  refine SepWP.fold (polyDecoderAt_entails_vecs_tail A (s0.sp - 1464#64) dec1) (by sep_focus) ?_
  wp_pull_exists; rename_i vecs
  wp_focus_pure; intro hvecs_len
  wp_conv_pre => rw [stackAt_decodedMessage_to_dropPoly16 (s0.sp - 1568#64)]
  wp_steps
  refine SepWP.fold (outA_done_recompose A outA st ct1 outRes hout g gdk gct1) (by sep_focus) ?_
  refine call_dropGlueSortedSetPt16_cs hpt16 (s0.sp - 1464#64) vecs hvecs_len (s0 := s0)
    (ret_pc := entry + 268#64) (sp_call := s0.sp - 1568#64)
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm, hsp2]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr2])
    (by simp only [Reg.x0, arm64_norm, hsp2]) (by sep_focus)
    (fun sf3 hpc3 hrun3 hsp3 hcs3 htr3 => ?_)
  rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hfp_3, hvregs_3⟩
  simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2]
    at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hfp_3 hvregs_3
  refine SepWP.fold (polyDecoder_post_join (s0.sp - 1464#64)) (by sep_focus) ?_
  refine SepWP.fold (stackAt_decodedMessage_from_dropPoly16 (s0.sp - 1568#64)) (by sep_focus) ?_
  wp_conv_pre => unfold recvCt1SavedCells
  wp_steps
  refine SepWP.fold (stackAt_1568_rejoin s0 0#64 st.uc.epoch
    (authWordsList g ++ vecWordsList gdk ++ [st.uc.epoch]) rfl)
    (by dsimp only [recvCt1SavedCells]; sep_focus) ?_
  wp_done

/-! ## 7. Main Theorem: `<HeaderSent>::recv_ct1_chunk` (`0x5d8fc`, 113 insns) -/

attribute [local irreducible] Chunked.SendEk.HeaderSent.recv_ct1_chunk

set_option maxHeartbeats 800000 in
theorem header_sent_recv_ct1_chunk_ok_ext {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt b A ext)
    (hmemcpy : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (haddChunk : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr addChunkName) (addChunkSpec A))
    (hdecoded : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr polyDecoderDecodedMessageName)
      (polyDecoderDecodedMessageSpec A b)) :
    subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr headerSentRecvCt1ChunkName)
      (headerSentRecvCt1ChunkSpec A F b) := by
  have hfn : libsignalSessionCode.fnOff headerSentRecvCt1ChunkName = 0x58504 :=
    headerSentRecvCt1Chunk_fnOff
  have hmemcpy_raw : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr headerSentRecvCt1ChunkName + (bv% (ls_rel% "<spqr::v1::chunked::send_ek::HeaderSent>::recv_ct1_chunk" "memcpy")))
      sessionMemcpyRegionSpec := sub_ok_of_addr_eq
    (fnAddr_fwd_eq (d := (num% (ls_rel% "<spqr::v1::chunked::send_ek::HeaderSent>::recv_ct1_chunk" "memcpy"))) (b := b) (X := Rust.withPanics ext)
      hfn (ls_stub% "memcpy") (by decide)).symm hmemcpy
  have hadd_raw : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr headerSentRecvCt1ChunkName + 60196#64)
      (addChunkSpec A) := sub_ok_of_addr_eq
    (fnAddr_fwd_eq (d := 60196) (b := b) (X := Rust.withPanics ext)
      hfn libsignalSessionCode_fnOff_0x67028 (by decide)).symm haddChunk
  have hdec_raw : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr headerSentRecvCt1ChunkName + 57988#64)
      (polyDecoderDecodedMessageSpec A b) := sub_ok_of_addr_eq
    (fnAddr_fwd_eq (d := 57988) (b := b) (X := Rust.withPanics ext)
      hfn libsignalSessionCode_fnOff_0x66788 (by decide)).symm hdecoded
  have hpt16_raw : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr headerSentRecvCt1ChunkName + 18446744073709478940#64)
      (dropGlueSortedSetPt16Spec A) := by
    have hrel : (leavesProgAtExt b ext).fnAddr headerSentRecvCt1ChunkName =
        (leavesProgAtExt b ext).fnAddr dropSortedSetPt16Name + BitVec.ofNat 64 72676 :=
      Program.fnAddr_rel (k := 72676) (b := b) (X := Rust.withPanics ext)
        libsignalSessionCode_fnOff_0x46920 hfn (by decide)
    refine sub_ok_of_addr_eq ?_ (drop_glue_sorted_set_pt16_ok_ext hdealloc)
    rw [hrel, BitVec.add_assoc]; simp
  code_fetches libsignalSessionCode spqrHeaderSentRecvCt1ChunkBin b
    (Rust.withPanics ext) hfn 0x58504 452
  clear hfn
  unfold headerSentRecvCt1ChunkSpec
  wpp_init x s0
  conv => arg 6; ext sf P_f; rw [sepConj_assoc]
  rcases x with ⟨outA, stA, chunkA, st, chunk, outRes⟩
  have h_none := header_sent_recv_ct1_chunk_none (A := A) (F := F) hmemcpy_raw
  have h_some := header_sent_recv_ct1_chunk_some (A := A) (F := F) hmemcpy_raw hpt16_raw
  dsimp only [leavesProgAtExt, tripleRatchetProgAtExt, headerSentRecvCt1ChunkName,
    chunkedHeaderSentSize, BitVec.ofNat_eq_ofNat] at *
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::send_ek::HeaderSent>::recv_ct1_chunk" = entry
  examples_hide_fetches
  subst ‹s0.readReg64 (Reg.gpr 0#5) = outA›
    ‹s0.readReg64 (Reg.gpr 1#5) = stA› ‹s0.readReg64 (Reg.gpr 3#5) = chunkA›
  have hb : b &&& 4095#64 = 0#64 := by assumption
  have hx2 : s0.readReg64 (Reg.gpr 2#5) = st.uc.epoch := by assumption
  have hsorted : PolyDecoderStrictSorted st.receiving_ct1 := by assumption
  have hrecv : st.recv_ct1_chunk st.uc.epoch chunk = .ok outRes := by assumption
  have hsp0_align : (s0.sp &&& 15#64 == 0#64) = true := by assumption
  have hfsp_align : ((s0.sp - 1568#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 1568#64 hsp0_align (by decide)
  apply SepWPp.of_sepWP (mid := entry + 60196#64)
  wp_conv_pre =>
    rw [stackAt_1568_split s0.sp,
        stackAt_decodedMessage_to_addChunk (s0.sp - 1568#64)]
    unfold chunkedHeaderSentAt
  refine SepWP.fold (polyDecoderAt_dup_pts_len A (s0.readReg64 (Reg.gpr 1#5) + 480#64) st.receiving_ct1)
    (by sep_focus) ?_
  wp_focus_pure; intro hpts
  obtain ⟨outMsg, hdm, hcases⟩ := header_sent_recv_ct1_chunk_ok_elim hpts hrecv
  wp_conv_pre => rw [unchunkedEkSentAt_400_eq]
  refine SepWP.fold (authenticatorAt_extract A (s0.readReg64 (Reg.gpr 1#5) + 400#64) st.uc.auth)
    (by sep_focus) ?_
  wp_pull_exists; rename_i g
  refine SepWP.fold (vecU8_extract A (s0.readReg64 (Reg.gpr 1#5) + 448#64) st.uc.dk)
    (by sep_focus) ?_
  wp_pull_exists; rename_i gdk
  have hst_auth :
      wordsAt (s0.readReg64 (Reg.gpr 1#5) + 400#64) (authWordsList g) =
      (((s0.readReg64 (Reg.gpr 1#5) + 400#64) ↦₆₄ g.v1.w0) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 408#64) ↦₆₄ g.v1.w1) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 416#64) ↦₆₄ g.v1.w2) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 424#64) ↦₆₄ g.v2.w0) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 432#64) ↦₆₄ g.v2.w1) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 440#64) ↦₆₄ g.v2.w2)) := by
    dsimp only [authWordsList]; simp only [wordsAt_6, BitVec.add_assoc, arm64_norm]
  have hst_dk :
      wordsAt (s0.readReg64 (Reg.gpr 1#5) + 448#64) (vecWordsList gdk) =
      (((s0.readReg64 (Reg.gpr 1#5) + 448#64) ↦₆₄ gdk.w0) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 456#64) ↦₆₄ gdk.w1) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 464#64) ↦₆₄ gdk.w2)) := by
    dsimp only [vecWordsList]
    simp only [wordsAt, wordsAt_cons_off, wordsAt_nil, sepConj_emp, BitVec.add_assoc, arm64_norm]
  have hsp_1552_words :
      wordsAt (s0.sp - 1552#64) (authWordsList g ++ vecWordsList gdk ++ [st.uc.epoch]) =
      (((s0.sp - 1552#64) ↦₆₄ g.v1.w0) ∗ ((s0.sp - 1544#64) ↦₆₄ g.v1.w1) ∗
       ((s0.sp - 1536#64) ↦₆₄ g.v1.w2) ∗ ((s0.sp - 1528#64) ↦₆₄ g.v2.w0) ∗
       ((s0.sp - 1520#64) ↦₆₄ g.v2.w1) ∗ ((s0.sp - 1512#64) ↦₆₄ g.v2.w2) ∗
       ((s0.sp - 1504#64) ↦₆₄ gdk.w0) ∗ ((s0.sp - 1496#64) ↦₆₄ gdk.w1) ∗
       ((s0.sp - 1488#64) ↦₆₄ gdk.w2) ∗ ((s0.sp - 1480#64) ↦₆₄ st.uc.epoch)) := by
    dsimp only [authWordsList, vecWordsList, List.append]; simp only [wordsAt_10, arm64_norm]
  refine SepWP.fold (cells_1_unfold (s0.sp - 1568#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_1_unfold (s0.sp - 1560#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_10_unfold (s0.sp - 1552#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_8_unfold (s0.sp - 64#64)) (by sep_focus) ?_
  wp_pull_exists
  wp_conv_pre => rw [hst_auth, hst_dk, wordsAt_10_sp_1552, sp_sub_64_add_8, sp_sub_64_add_16,
    sp_sub_64_add_24, sp_sub_64_add_32, sp_sub_64_add_40, sp_sub_64_add_48, sp_sub_64_add_56]
  wp_steps
  refine SepWP.fold (Entails.of_eq hst_auth.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hst_dk.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hsp_1552_words.symm) (by sep_focus) ?_
  have hfold_saved :
      (((s0.sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ⊢
      recvCt1SavedCells s0 := Entails.refl _
  refine SepWP.fold hfold_saved (by dsimp only [Reg.fp, Reg.lr, Reg.x28, Reg.x23, Reg.x22, Reg.x21, Reg.x20, Reg.x19]; sep_focus) ?_
  refine call_memcpy_relocate_cs hmemcpy_raw (s0 := s0)
    (Relocatable.of_polyDecoderAt A st.receiving_ct1)
    (s0.sp - 1464#64) (s0.readReg64 (Reg.gpr 1#5) + 480#64)
    (ret_pc := entry + 104#64) (sp_call := s0.sp - 1568#64)
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [trace_writeVReg128, arm64_norm])
    (by simp only [Reg.x0, arm64_norm]) (by simp only [Reg.x1, arm64_norm])
    (by simp only [Reg.x2, arm64_norm]) (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 htr1 => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [arm64_norm, hx2]
    at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
  wp_steps
  refine call_addChunk_next hadd_raw (s0.sp - 1464#64) (s0.readReg64 (Reg.gpr 3#5)) st.receiving_ct1 chunk hsorted
    (s0 := s0) (ret_pc := entry + 116#64) (next_pc := entry + 57988#64) (sp_call := s0.sp - 1568#64)
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm, hsp1]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) htr1
    (by simp only [Reg.x0, arm64_norm, hsp1]) (by simp only [Reg.x1, arm64_norm, hx22_1])
    (by sep_focus)
    (fun sf2 hpc2 hrun2 hsp2 hcs2 htr2 hsorted1 => ?_)
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
  simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1]
    at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
  refine SepWP.fold (stackAt_decodedMessage_from_addChunk (s0.sp - 1568#64)) (by sep_focus) ?_
  wp_steps
  refine call_decodedMessage hdec_raw hb (s0.sp - 1064#64) (s0.sp - 1464#64)
    (addChunkTotal st.receiving_ct1 chunk) outMsg hsorted1 hdm
    (s0 := s0) (ret_pc := entry + 128#64) (sp_call := s0.sp - 1568#64)
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm, hsp2]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) htr2
    (by simp only [Reg.x8, arm64_norm, hsp2]) (by simp only [Reg.x0, arm64_norm, hsp2])
    (by sep_focus)
    (fun sf3 hpc3 hrun3 hsp3 hcs3 htr3 => ?_)
  rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hfp_3, hvregs_3⟩
  simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2]
    at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hfp_3 hvregs_3
  rcases hcases with ⟨rfl, hout⟩ | ⟨ct1, rfl, hout⟩
  · refine h_none (s0.readReg64 (Reg.gpr 0#5)) (s0.readReg64 (Reg.gpr 1#5)) (s0.readReg64 (Reg.gpr 3#5))
      st chunk (addChunkTotal st.receiving_ct1 chunk) outRes hout g gdk
      hsp0_align hfsp_align hpc3 hrun3 hsp3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3
      hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hfp_3 hvregs_3 htr3 ?_
    ac_rfl
  · refine h_some (s0.readReg64 (Reg.gpr 0#5)) (s0.readReg64 (Reg.gpr 1#5)) (s0.readReg64 (Reg.gpr 3#5))
      st chunk (addChunkTotal st.receiving_ct1 chunk) ct1 outRes hout g gdk
      hsp0_align hfsp_align hpc3 hrun3 hsp3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3
      hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hfp_3 hvregs_3 htr3 ?_
    ac_rfl

end CryptoVerification.SpqrV1.States.Leaves
