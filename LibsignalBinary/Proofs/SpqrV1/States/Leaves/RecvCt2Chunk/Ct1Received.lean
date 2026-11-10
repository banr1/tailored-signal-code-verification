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
import LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoder
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.Common
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::send_ek::Ct1Received>::recv_ct2_chunk` (`0x58e18`)

Verifies `<Ct1Received>::recv_ct2_chunk` (`0x58e18`, 67 instructions) against
`ct1ReceivedRecvCt2ChunkSpec A F`.
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

gen_decodes libsignalSessionCode_tree spqrRecvCt2ChunkBin [
  0x58efc → 0x59004
]

/-! ## Proof of `<Ct1Received>::recv_ct2_chunk` (`0x58e18`, 67 insns) -/

theorem wordsAt_13' (a : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 : BitVec 64) :
    wordsAt a [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12] =
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
      ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗
      ((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9) ∗ ((a + 80#64) ↦₆₄ w10) ∗ ((a + 88#64) ↦₆₄ w11) ∗
      ((a + 96#64) ↦₆₄ w12) := by
  conv_lhs => rw [wordsAt]
  simp only [wordsAt_cons_off, wordsAt_nil, sepConj_emp,
    show (8#64 + 8#64 : BitVec 64) = 16#64 from rfl, show (16#64 + 8#64 : BitVec 64) = 24#64 from rfl,
    show (24#64 + 8#64 : BitVec 64) = 32#64 from rfl, show (32#64 + 8#64 : BitVec 64) = 40#64 from rfl,
    show (40#64 + 8#64 : BitVec 64) = 48#64 from rfl, show (48#64 + 8#64 : BitVec 64) = 56#64 from rfl,
    show (56#64 + 8#64 : BitVec 64) = 64#64 from rfl, show (64#64 + 8#64 : BitVec 64) = 72#64 from rfl,
    show (72#64 + 8#64 : BitVec 64) = 80#64 from rfl, show (80#64 + 8#64 : BitVec 64) = 88#64 from rfl,
    show (88#64 + 8#64 : BitVec 64) = 96#64 from rfl]

theorem cells_13_unfold' (a : BitVec 64) :
    memRegion a 104 ⊢
      ∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3, ∃∗ v4, ∃∗ v5, ∃∗ v6, ∃∗ v7,
      ∃∗ v8, ∃∗ v9, ∃∗ v10, ∃∗ v11, ∃∗ v12,
        wordsAt a [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12] := by
  rw [ProofLib.memRegion_cells a 13 (by decide), ProofLib.cells_succ]
  simp only [wordsAt_13', cells_succ_off, ProofLib.cells_zero, sepConj_emp, sepExists_sepConj_right,
    show (8#64 + 8#64 : BitVec 64) = 16#64 from rfl, show (16#64 + 8#64 : BitVec 64) = 24#64 from rfl,
    show (24#64 + 8#64 : BitVec 64) = 32#64 from rfl, show (32#64 + 8#64 : BitVec 64) = 40#64 from rfl,
    show (40#64 + 8#64 : BitVec 64) = 48#64 from rfl, show (48#64 + 8#64 : BitVec 64) = 56#64 from rfl,
    show (56#64 + 8#64 : BitVec 64) = 64#64 from rfl, show (64#64 + 8#64 : BitVec 64) = 72#64 from rfl,
    show (72#64 + 8#64 : BitVec 64) = 80#64 from rfl, show (80#64 + 8#64 : BitVec 64) = 88#64 from rfl,
    show (88#64 + 8#64 : BitVec 64) = 96#64 from rfl]
  exact Entails.refl _

theorem stackAt_448_split (sp : BitVec 64) :
    stackAt sp ct1ReceivedRecvCt2ChunkStack =
      memRegion (sp - 16976#64) 12224 ∗ stackAt (sp - 448#64) addChunkStack ∗
      memRegion (sp - 448#64) 128 ∗ memRegion (sp - 320#64) 128 ∗ memRegion (sp - 192#64) 128 ∗
      memRegion (sp - 64#64) 8 ∗ memRegion (sp - 56#64) 1 ∗ memRegion (sp - 55#64) 7 ∗
      memRegion (sp - 48#64) 48 := by
  change memRegion (sp - 16976#64) 16976 =
    memRegion (sp - 16976#64) 12224 ∗ memRegion (sp - 448#64 - 4304#64) 4304 ∗ _
  have hsub : sp - 448#64 - 4304#64 = sp - 4752#64 := by bv_omega
  rw [hsub,
      ProofLib.memRegion_split' (b := sp - 16976#64) (n := 12224) (k := 4752) (b' := sp - 4752#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 4752#64) (n := 4304) (k := 448) (b' := sp - 448#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 448#64) (n := 128) (k := 320) (b' := sp - 320#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 320#64) (n := 128) (k := 192) (b' := sp - 192#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 192#64) (n := 128) (k := 64) (b' := sp - 64#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 64#64) (n := 8) (k := 56) (b' := sp - 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 56#64) (n := 1) (k := 55) (b' := sp - 55#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 55#64) (n := 7) (k := 48) (b' := sp - 48#64) rfl (by bv_omega) (by decide)]

theorem stackAt_448_to_dropPoly16 (sp w0 w1 w2 w3 w4 w5 : BitVec 64) :
    memRegion (sp - 16976#64) 12224 ∗ stackAt (sp - 448#64) addChunkStack ∗ memRegion (sp - 448#64) 400 ∗
      (((sp - 48#64) ↦₆₄ w0) ∗ ((sp - 40#64) ↦₆₄ w1) ∗ ((sp - 32#64) ↦₆₄ w2) ∗
       ((sp - 24#64) ↦₆₄ w3) ∗ ((sp - 16#64) ↦₆₄ w4) ∗ ((sp - 8#64) ↦₆₄ w5)) ⊢
    memRegion (sp - 16976#64) 12848 ∗ stackAt sp dropGluePoly16Stack := by
  have h6 :
      (((sp - 48#64) ↦₆₄ w0) ∗ ((sp - 40#64) ↦₆₄ w1) ∗ ((sp - 32#64) ↦₆₄ w2) ∗
       ((sp - 24#64) ↦₆₄ w3) ∗ ((sp - 16#64) ↦₆₄ w4) ∗ ((sp - 8#64) ↦₆₄ w5)) ⊢
      memRegion (sp - 48#64) 48 := by
    have heq :
        (((sp - 48#64) ↦₆₄ w0) ∗ ((sp - 40#64) ↦₆₄ w1) ∗ ((sp - 32#64) ↦₆₄ w2) ∗
         ((sp - 24#64) ↦₆₄ w3) ∗ ((sp - 16#64) ↦₆₄ w4) ∗ ((sp - 8#64) ↦₆₄ w5)) =
        wordsAt (sp - 48#64) [w0, w1, w2, w3, w4, w5] := by simp only [wordsAt_6, arm64_norm]
    rw [heq]; exact wordsAt_entails_memRegion [w0, w1, w2, w3, w4, w5] (sp - 48#64) 48 rfl
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right h6))) ?_
  change memRegion (sp - 16976#64) 12224 ∗
      (memRegion (sp - 448#64 - 4304#64) 4304 ∗ (memRegion (sp - 448#64) 400 ∗ memRegion (sp - 48#64) 48)) ⊢
    memRegion (sp - 16976#64) 12848 ∗ memRegion (sp - 4128#64) 4128
  have hsub : sp - 448#64 - 4304#64 = sp - 4752#64 := by bv_omega
  rw [hsub,
      ← ProofLib.memRegion_split' (b := sp - 448#64) (n := 400) (k := 48) (b' := sp - 48#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 4752#64) (n := 4304) (k := 448) (b' := sp - 448#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 16976#64) (n := 12224) (k := 4752) (b' := sp - 4752#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 16976#64) (n := 12848) (k := 4128) (b' := sp - 4128#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem stackAt_448_from_dropPoly16 (sp : BitVec 64) :
    memRegion (sp - 16976#64) 12848 ∗ stackAt sp dropGluePoly16Stack ⊢
    stackAt sp ct1ReceivedRecvCt2ChunkStack := by
  change memRegion (sp - 16976#64) 12848 ∗ memRegion (sp - 4128#64) 4128 ⊢ memRegion (sp - 16976#64) 16976
  rw [← ProofLib.memRegion_split' (b := sp - 16976#64) (n := 12848) (k := 4128) (b' := sp - 4128#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem uc_104_copy_recompose {A : RustAlloc} {F : ShaCompress}
    (outA stA : BitVec 64) (st : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F))
    (g : FourVecWords) :
    wordsAt outA (ekSentCt1ReceivedWordsList g st.epoch) ∗
      wordsAt (stA + 400#64) (ekSentCt1ReceivedWordsList g st.epoch) ∗
      relocatedHeap (fun dst => unchunkedEkSentCt1ReceivedAt A dst st)
        (wordsBytes (ekSentCt1ReceivedWordsList g st.epoch)) ⊢
    unchunkedEkSentCt1ReceivedAt A outA st ∗ memRegion (stA + 400#64) 104 := by
  have h1 : wordsAt outA (ekSentCt1ReceivedWordsList g st.epoch) ∗
      relocatedHeap (fun dst => unchunkedEkSentCt1ReceivedAt A dst st)
        (wordsBytes (ekSentCt1ReceivedWordsList g st.epoch)) ⊢
      unchunkedEkSentCt1ReceivedAt A outA st := by
    rw [wordsAt_eq_pointsToBytes]; exact relocatedHeap_recompose _ _ outA
  have h2 : wordsAt (stA + 400#64) (ekSentCt1ReceivedWordsList g st.epoch) ⊢
      memRegion (stA + 400#64) 104 :=
    wordsAt_entails_memRegion (ekSentCt1ReceivedWordsList g st.epoch) (stA + 400#64) 104 rfl
  refine Entails.trans (Entails.of_eq (show _ =
    (wordsAt outA (ekSentCt1ReceivedWordsList g st.epoch) ∗
      relocatedHeap (fun dst => unchunkedEkSentCt1ReceivedAt A dst st)
        (wordsBytes (ekSentCt1ReceivedWordsList g st.epoch))) ∗
    wordsAt (stA + 400#64) (ekSentCt1ReceivedWordsList g st.epoch) by ac_rfl)) ?_
  exact sepConj_mono h1 h2

theorem chunkedEkSentCt1ReceivedAt_recompose (A : RustAlloc) {F : ShaCompress}
    (outA : BitVec 64) (uc : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F))
    (dec : PolyDecoder) (outSt : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (hout : outSt = { uc := uc, receiving_ct2 := dec }) :
    unchunkedEkSentCt1ReceivedAt A outA uc ∗ polyDecoderAt A (outA + 104#64) dec ⊢
    chunkedEkSentCt1ReceivedAt A outA outSt := by
  subst hout; exact Entails.refl _

set_option maxHeartbeats 1200000 in
theorem ct1_received_recv_ct2_chunk_ok_ext {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt b A ext)
    (hmemcpy : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (haddChunk : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr addChunkName) (addChunkSpec A)) :
    subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr ct1ReceivedRecvCt2ChunkName)
      (ct1ReceivedRecvCt2ChunkSpec A F) := by
  simp only [ct1ReceivedRecvCt2ChunkSpec]
  have hadd_raw : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr ct1ReceivedRecvCt2ChunkName + 57644#64)
      (addChunkSpec A) := sub_ok_of_addr_eq
    (fnAddr_fwd_eq (d := 57644) (b := b) (X := Rust.withPanics ext)
      ct1ReceivedRecvCt2Chunk_fnOff libsignalSessionCode_fnOff_0x67028 (by decide)).symm haddChunk
  have hmemcpy_raw : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr ct1ReceivedRecvCt2ChunkName +
        (bv% (ls_rel% "<spqr::v1::chunked::send_ek::Ct1Received>::recv_ct2_chunk" "memcpy")))
      sessionMemcpyRegionSpec := sub_ok_of_addr_eq
    (fnAddr_fwd_eq (d := (num% (ls_rel% "<spqr::v1::chunked::send_ek::Ct1Received>::recv_ct2_chunk" "memcpy"))) (b := b) (X := Rust.withPanics ext)
      ct1ReceivedRecvCt2Chunk_fnOff libsignalSessionCode_fnOff_memcpy (by decide)).symm hmemcpy
  have hpoly16_raw : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr ct1ReceivedRecvCt2ChunkName + 18446744073709476808#64)
      (dropGluePoly16Spec A) := by
    have hrel : (leavesProgAtExt b ext).fnAddr ct1ReceivedRecvCt2ChunkName =
        (leavesProgAtExt b ext).fnAddr dropPoly16Name + BitVec.ofNat 64 74808 :=
      Program.fnAddr_rel (k := 74808) (b := b) (X := Rust.withPanics ext)
        libsignalSessionCode_fnOff_0x46ac4 ct1ReceivedRecvCt2Chunk_fnOff (by decide)
    refine sub_ok_of_addr_eq ?_ (drop_glue_poly16_ok_ext hdealloc)
    dsimp only [dropProgAtExt, leavesProgAtExt] at hrel ⊢
    rw [hrel, BitVec.add_assoc]; simp
  code_fetches libsignalSessionCode spqrRecvCt2ChunkBin b
    (Rust.withPanics ext) ct1ReceivedRecvCt2Chunk_fnOff
    (num% (ls_off% "<spqr::v1::chunked::send_ek::Ct1Received>::recv_ct2_chunk")) 268
  dsimp only [leavesProgAtExt, ct1ReceivedRecvCt2ChunkName,
    chunkedEkSentCt1ReceivedSize, chunkedCt1ReceivedSize,
    BitVec.ofNat_eq_ofNat] at hadd_raw hmemcpy_raw hpoly16_raw ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::send_ek::Ct1Received>::recv_ct2_chunk" = entry
  examples_hide_fetches
  wpp_init x s0
  rcases x with ⟨outA, stA, chunkA, st, chunk, outSt⟩
  dsimp only at *
  subst ‹s0.readReg64 (Reg.gpr 0#5) = outA›
    ‹s0.readReg64 (Reg.gpr 1#5) = stA› ‹s0.readReg64 (Reg.gpr 3#5) = chunkA›
  have hout_eq := ct1_received_recv_ct2_chunk_ok_elim (by assumption)
  have hfsp_align : ((s0.sp - 448#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 448#64 (by assumption) (by decide)
  apply SepWPp.of_sepWP (mid := entry + 57644#64)
  wp_conv_pre =>
    rw [ProofLib.memRegion_split' (b := s0.readReg64 (Reg.gpr 0#5)) (n := 104) (k := 400)
        (b' := s0.readReg64 (Reg.gpr 0#5) + 104#64) rfl rfl (by decide),
        stackAt_448_split s0.sp]
    unfold chunkedCt1ReceivedAt
  refine SepWP.fold (cells_16_unfold (s0.sp - 448#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_16_unfold (s0.sp - 320#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_16_unfold (s0.sp - 192#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_1_unfold (s0.sp - 64#64)) (by sep_focus) ?_
  refine SepWP.fold (byte_1_unfold (s0.sp - 56#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_6_unfold (s0.sp - 48#64)) (by sep_focus) ?_
  wp_pull_exists
  refine SepWP.fold (unchunkedEkSentCt1ReceivedAt_extract A
    (s0.readReg64 (Reg.gpr 1#5) + 400#64) st.uc) (by sep_focus) ?_
  wp_pull_exists; rename_i g
  have hst_words :
      wordsAt (s0.readReg64 (Reg.gpr 1#5) + 400#64) (ekSentCt1ReceivedWordsList g st.uc.epoch) =
      (((s0.readReg64 (Reg.gpr 1#5) + 400#64) ↦₆₄ g.v1.w0) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 408#64) ↦₆₄ g.v1.w1) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 416#64) ↦₆₄ g.v1.w2) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 424#64) ↦₆₄ g.rest.v1.w0) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 432#64) ↦₆₄ g.rest.v1.w1) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 440#64) ↦₆₄ g.rest.v1.w2) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 448#64) ↦₆₄ g.rest.auth.v1.w0) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 456#64) ↦₆₄ g.rest.auth.v1.w1) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 464#64) ↦₆₄ g.rest.auth.v1.w2) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 472#64) ↦₆₄ g.rest.auth.v2.w0) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 480#64) ↦₆₄ g.rest.auth.v2.w1) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 488#64) ↦₆₄ g.rest.auth.v2.w2) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 496#64) ↦₆₄ st.uc.epoch)) := by
    dsimp only [ekSentCt1ReceivedWordsList, ekSentWordsList,
      ct2SentWordsList, authWordsList, vecWordsList, List.append]
    simp only [wordsAt_13', BitVec.add_assoc, arm64_norm]
  have hout_words :
      wordsAt (s0.readReg64 (Reg.gpr 0#5)) (ekSentCt1ReceivedWordsList g st.uc.epoch) =
      (((s0.readReg64 (Reg.gpr 0#5)) ↦₆₄ g.v1.w0) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ g.v1.w1) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ g.v1.w2) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 24#64) ↦₆₄ g.rest.v1.w0) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 32#64) ↦₆₄ g.rest.v1.w1) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 40#64) ↦₆₄ g.rest.v1.w2) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 48#64) ↦₆₄ g.rest.auth.v1.w0) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 56#64) ↦₆₄ g.rest.auth.v1.w1) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 64#64) ↦₆₄ g.rest.auth.v1.w2) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 72#64) ↦₆₄ g.rest.auth.v2.w0) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 80#64) ↦₆₄ g.rest.auth.v2.w1) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 88#64) ↦₆₄ g.rest.auth.v2.w2) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 96#64) ↦₆₄ st.uc.epoch)) := by
    dsimp only [ekSentCt1ReceivedWordsList, ekSentWordsList,
      ct2SentWordsList, authWordsList, vecWordsList, List.append]
    simp only [wordsAt_13', arm64_norm]
  wp_conv_pre => rw [hst_words]; simp only [wordsAt_16, arm64_norm]
  wp_steps
  have hdec0_1 :
      (((s0.sp - 448#64) ↦₆₄ 0#64) ∗ ((s0.sp - 440#64) ↦₆₄ 2#64) ∗
       ((s0.sp - 432#64) ↦₆₄ 0#64) ∗ ((s0.sp - 424#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 416#64) ↦₆₄ 2#64) ∗ ((s0.sp - 408#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 400#64) ↦₆₄ 0#64) ∗ ((s0.sp - 392#64) ↦₆₄ 2#64) ∗
       ((s0.sp - 384#64) ↦₆₄ 0#64) ∗ ((s0.sp - 376#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 368#64) ↦₆₄ 2#64) ∗ ((s0.sp - 360#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 352#64) ↦₆₄ 0#64) ∗ ((s0.sp - 344#64) ↦₆₄ 2#64) ∗
       ((s0.sp - 336#64) ↦₆₄ 0#64) ∗ ((s0.sp - 328#64) ↦₆₄ 0#64)) =
      wordsAt (s0.sp - 448#64)
        [0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64,
         0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64] := by simp only [wordsAt_16, arm64_norm]
  have hdec0_2 :
      (((s0.sp - 320#64) ↦₆₄ 2#64) ∗ ((s0.sp - 312#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 304#64) ↦₆₄ 0#64) ∗ ((s0.sp - 296#64) ↦₆₄ 2#64) ∗
       ((s0.sp - 288#64) ↦₆₄ 0#64) ∗ ((s0.sp - 280#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 272#64) ↦₆₄ 2#64) ∗ ((s0.sp - 264#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 256#64) ↦₆₄ 0#64) ∗ ((s0.sp - 248#64) ↦₆₄ 2#64) ∗
       ((s0.sp - 240#64) ↦₆₄ 0#64) ∗ ((s0.sp - 232#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 224#64) ↦₆₄ 2#64) ∗ ((s0.sp - 216#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 208#64) ↦₆₄ 0#64) ∗ ((s0.sp - 200#64) ↦₆₄ 2#64)) =
      wordsAt ((s0.sp - 448#64) + 128#64)
        [2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64,
         0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64] := by simp only [wordsAt_16, arm64_norm]
  have hdec0_3 :
      (((s0.sp - 192#64) ↦₆₄ 0#64) ∗ ((s0.sp - 184#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 176#64) ↦₆₄ 2#64) ∗ ((s0.sp - 168#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 160#64) ↦₆₄ 0#64) ∗ ((s0.sp - 152#64) ↦₆₄ 2#64) ∗
       ((s0.sp - 144#64) ↦₆₄ 0#64) ∗ ((s0.sp - 136#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 128#64) ↦₆₄ 2#64) ∗ ((s0.sp - 120#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 112#64) ↦₆₄ 0#64) ∗ ((s0.sp - 104#64) ↦₆₄ 2#64) ∗
       ((s0.sp - 96#64) ↦₆₄ 0#64) ∗ ((s0.sp - 88#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 80#64) ↦₆₄ 2#64) ∗ ((s0.sp - 72#64) ↦₆₄ 0#64)) =
      wordsAt ((s0.sp - 448#64) + 256#64)
        [0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64,
         2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64] := by simp only [wordsAt_16, arm64_norm]
  refine SepWP.fold (Entails.of_eq hdec0_1) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hdec0_2) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hdec0_3) (by sep_focus) ?_
  have hdec_recomp :
      wordsAt (s0.sp - 448#64)
        [0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64,
         0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64] ∗
      wordsAt ((s0.sp - 448#64) + 128#64)
        [2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64,
         0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64] ∗
      wordsAt ((s0.sp - 448#64) + 256#64)
        [0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64,
         2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64] ∗
      ((s0.sp - 64#64) ↦₆₄ 80#64) ∗ ((s0.sp - 56#64) ↦₈ 0#8) ∗ memRegion (s0.sp - 55#64) 7 ⊢
      polyDecoderAt A (s0.sp - 448#64) (emptyPolyDecoder 80) := by
    simpa only [arm64_norm] using emptyPolyDecoder_recompose A (s0.sp - 448#64) 80 (by decide)
  refine SepWP.fold hdec_recomp (by sep_focus) ?_
  refine call_addChunk hadd_raw
    (s0.sp - 448#64) (s0.readReg64 (Reg.gpr 3#5)) (emptyPolyDecoder 80) chunk
    (emptyPolyDecoder_strictSorted 80) (ret_pc := entry + 168#64) (sp_call := s0.sp - 448#64)
    (by simp only [arm64_norm]) (by simpa only [arm64_norm] using ‹s0.status = .Running›)
    (by simp only [State.sp, arm64_norm]) hfsp_align (by simp only [Reg.lr, arm64_norm])
    (by simp only [arm64_norm]) (by simp only [Reg.x0, arm64_norm])
    (by simp only [Reg.x1, arm64_norm]) (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 htr1 _ => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [arm64_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
  refine SepWP.fold (cells_13_unfold' (s0.readReg64 (Reg.gpr 0#5))) (by sep_focus) ?_
  wp_pull_exists
  wp_conv_pre => simp only [wordsAt_13', arm64_norm]
  wp_steps
  refine SepWP.fold (Entails.of_eq hst_words.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hout_words.symm) (by sep_focus) ?_
  refine SepWP.fold (uc_104_copy_recompose
    (s0.readReg64 (Reg.gpr 0#5)) (s0.readReg64 (Reg.gpr 1#5)) st.uc g) (by sep_focus) ?_
  refine call_memcpy_relocate hmemcpy_raw (s0 := s0)
    (Relocatable.of_polyDecoderAt A (addChunkTotal (emptyPolyDecoder 80) chunk))
    (s0.readReg64 (Reg.gpr 0#5) + 104#64) (s0.sp - 448#64)
    (ret_pc := entry + 216#64) (sp_call := s0.sp - 448#64)
    (v19 := s0.readReg64 (Reg.gpr 1#5)) (v20 := s0.readReg64 (Reg.gpr 0#5))
    (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun1)
    (by simp only [State.sp, arm64_norm, hsp1]) hfsp_align (by simp only [Reg.lr, arm64_norm])
    (by simp only [arm64_norm, htr1])
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hvregs_1])
    (by simp only [Reg.x0, arm64_norm, hx20_1]) (by simp only [Reg.x1, arm64_norm, hsp1])
    (by simp only [Reg.x2, arm64_norm]) (by sep_focus)
    (fun sf2 hpc2 hrun2 hsp2 hregs2 htr2 => ?_)
  rcases hregs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hvregs_2⟩
  refine SepWP.fold (chunkedEkSentCt1ReceivedAt_recompose A
    (s0.readReg64 (Reg.gpr 0#5)) st.uc (addChunkTotal (emptyPolyDecoder 80) chunk) outSt hout_eq)
    (by sep_focus) ?_
  refine SepWP.fold (polyEncoderAt_entails_tag_vecs_tail A
    (s0.readReg64 (Reg.gpr 1#5)) st.sending_ek) (by sep_focus) ?_
  wp_pull_exists; rename_i tag vecs
  wp_focus_pure; intro hvecs_len
  wp_steps
  refine SepWP.fold (stackAt_448_to_dropPoly16 s0.sp _ _ _ _ _ _) (by sep_focus) ?_
  wp_call hpoly16_raw ⟨s0.readReg64 (Reg.gpr 1#5) + 8#64, vecs⟩
  refine SepWP.fold (chunked_400_join (s0.readReg64 (Reg.gpr 1#5)) tag 104 504 rfl (by decide))
    (by sep_focus) ?_
  refine SepWP.fold (stackAt_448_from_dropPoly16 s0.sp) (by sep_focus) ?_
  wp_done

end CryptoVerification.SpqrV1.States.Leaves
