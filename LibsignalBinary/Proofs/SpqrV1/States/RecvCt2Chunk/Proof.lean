/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Common
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.ProofX
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Proof
import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part1c
import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part2
import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part2b
import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part2c
import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part3
import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part3c
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp

/-!
# `<EkSentCt1Received>::recv_ct2_chunk`: Top-Level Verification

**Checked by Lean.** Composes all segments (`Part1`..`Part3c`) of `<EkSentCt1Received>::recv_ct2_chunk`
(`0x5ec2c .. 0x5f434`, `514` instructions) to prove `recv_ct2_chunk_ok_x` and `recv_ct2_chunk_ok_ext`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.RecvCt2Chunk

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
open CryptoVerification.SpqrV1.GF.IsNonZero
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.States
open CryptoVerification
open CryptoVerification.LibsignalSpqrV1.PolyDecoder
open CryptoVerification.LibsignalTripleRatchet.Keys
open CryptoVerification.SpqrV1.ChainProofs
open UpdateFacts NextKeyInternalFacts AgreeStateSimp SplitBytes NewFacts

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  spqrHkdfWith Authenticator.update Chunked.SendEk.EkSentCt1Received.recv_ct2_chunk

/-! ## Bridging `DecodedMessageOkExt` to `PolyDecodedMessageOkX` -/

theorem optVecU8Of_eq_optKeyBytesAt (A : RustAlloc) (a : BitVec 64) (opt : Option Bytes) :
    optVecU8Of A a opt = optKeyBytesAt A a opt := by
  cases opt <;> rfl

theorem polyDecodedMessage_ok_of_decodedMessage {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : DecodedMessageOkExt b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr polyDecodedMessageName)
      (polyDecodedMessageSpec A b) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  have hpre_pts : s0.mem ⊨
      (⌜b &&& 0xfff#64 = 0#64 ∧
          s0.readReg64 .x8 = x.outA ∧
          s0.readReg64 .x0 = x.decA ∧
          PolyDecoderStrictSorted x.dec⌝ ∗
        memRegion x.outA vecHeaderBytes ∗
        (⌜x.dec.pts.length = 16⌝ ∗ polyDecoderAt A x.decA x.dec) ∗
        tokenInitAt b ∗
        reduceTableAt b ∗
        A.pool ∗
        stackAt s0.sp polyDecodedMessageStackX) ∗ R := by
    refine Satisfies.mono ?_ hpre
    dsimp only [polyDecodedMessageSpec]
    exact sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (polyDecoderAt_pts_length A x.decA x.dec))))
  have hpts_sort : x.dec.pts.length = 16 ∧ PolyDecoderStrictSorted x.dec := by
    have h1 : s0.mem ⊨
        ⌜x.dec.pts.length = 16⌝ ∗
        ⌜b &&& 0xfff#64 = 0#64 ∧
          s0.readReg64 .x8 = x.outA ∧
          s0.readReg64 .x0 = x.decA ∧
          PolyDecoderStrictSorted x.dec⌝ ∗
        (memRegion x.outA vecHeaderBytes ∗
          polyDecoderAt A x.decA x.dec ∗
          tokenInitAt b ∗
          reduceTableAt b ∗
          A.pool ∗
          stackAt s0.sp polyDecodedMessageStackX ∗ R) := by
      refine Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre_pts
    rw [satisfies_pure_sepConj] at h1
    rcases h1 with ⟨hlen, h2⟩
    rw [satisfies_pure_sepConj] at h2
    exact ⟨hlen, h2.1.2.2.2⟩
  have hdec_eq := decodedMessage_eq_ok x.dec hpts_sort.1 hpts_sort.2
  let x' : DecodedMessageGhost := { out := x.outA, decA := x.decA, dec := x.dec }
  have hpre' : s0.mem ⊨ (decodedMessageSpec A b).pre x' s0 ∗ R := hpre
  refine (subroutine_ok.mono_outcome h x' R s0 hpc hrun hpre' hsp) fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    dsimp only [decodedMessageSpec] at hpost
    dsimp only [polyDecodedMessageSpec]
    refine Satisfies.mono ?_ hpost
    refine sepConj_mono_left ?_
    rw [optVecU8Of_eq_optKeyBytesAt]
    refine Entails.pure_left fun htr => ?_
    refine Entails.trans (Entails.of_eq (show
        optKeyBytesAt A x.outA (decodedMessageTotal x.dec) ∗
          polyDecoderAt A x.decA x.dec ∗
          tokenInitAt b ∗ reduceTableAt b ∗ A.pool ∗ stackAt s0.sp decodedMessageStack =
        optKeyBytesAt A x.outA (decodedMessageTotal x.dec) ∗
          (polyDecoderAt A x.decA x.dec ∗
            tokenInitAt b ∗ reduceTableAt b ∗ A.pool ∗ stackAt s0.sp polyDecodedMessageStackX) by
        ac_rfl)) ?_
    refine sepConj_mono_left ?_
    exact Entails.sepExists_right (decodedMessageTotal x.dec)
      (Entails.pure_right ⟨hdec_eq, htr⟩ (Entails.refl _))
  · right; left; exact ⟨hpan, hpost⟩
  · right; right; left; exact ⟨code, hex, hpost⟩
  · right; right; right; exact ⟨hoom, hpost⟩

theorem polyDecodedMessageOkX_of_decodedMessage {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : DecodedMessageOkExt img.base A ext) :
    PolyDecodedMessageOkX img A ext := by
  have h1 := polyDecodedMessage_ok_of_decodedMessage h
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  have hpre' : s0.mem ⊨ (polyDecodedMessageSpec A img.base).pre x s0 ∗ R := by
    dsimp only [Spec.inImage] at hpre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    exact hpre.2
  exact (h1.mono_outcome x R s0 hpc hrun hpre' hsp) fun _ hout => hout

theorem polyDecodedMessageOkX_of_alloc {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext) :
    PolyDecodedMessageOkX img A ext :=
  polyDecodedMessageOkX_of_decodedMessage (polyDecoderDecodedMessage_ok hA)

/-! ## `.rodata` Slice for `0x83798` (`List.replicate 32 0#8`) -/

theorem rodata_zero32_recvCt2 {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964")) ↦ᵣ List.replicate 32 0#8) ∗ P := by
  have hhb := loads_rodata_holdsBytes himg hF
    (off := num% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964")) (n := 32) (bs := List.replicate 32 0#8)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel)
    (by rfl_kernel) (by decide) (by rfl_kernel)
  have ⟨h1, h2⟩ := holdsBytes_ro hhb
  exact Satisfies.rodata_intro h1 h2 (by decide) hP

/-! ## Top-Level Composition: `recv_ct2_chunk_ok_x` -/

theorem lt_128_of_compare_prefix_drop_bne {ct2Full tag : List (BitVec 8)}
    (hcmp : (compare_prefix (ct2Full.drop 128) tag != 0#8) = true) :
    128 < ct2Full.length := by
  by_contra hle
  have hdrop : ct2Full.drop 128 = [] := List.drop_eq_nil_of_le (by omega)
  rw [hdrop, compare_prefix] at hcmp
  change (isNonZero 0#8 != 0#8) = true at hcmp
  revert hcmp; decide

set_option maxHeartbeats 1600000 in
theorem recv_ct2_chunk_ok_x {img : Obj.Image} {K : MlKem} {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContractsX img A ext)
    (hdealloc_ext : DeallocOkExt img.base A ext)
    (hallocZeroed : AllocZeroedWithStackOkX img A ext)
    (hadd_ok : AddChunkOkX img A ext)
    (hdec_ok : PolyDecodedMessageOkX img A ext)
    (hdecaps : HookSat ext mlkemDecapsName (mlkemDecapsSpec K))
    (hconcat2 : SliceConcat2OkX img A ext)
    (hconcat3 : SliceConcat3OkX img A ext)
    (hhkdf : HkdfToSliceSpqrOkX img (spqrHkdfWith F) ext)
    (hupdate : AuthUpdateOkX img F A ext)
    (hres7 : DoReserve7OkX img A ext)
    (hhmac : HookSat ext libcruxHmacName (libcruxHmacSpec F A)) :
    RecvCt2ChunkOkX img K F A ext := by
  unfold RecvCt2ChunkOkX
  apply subroutine_ok_inImage_rodata3_keep
    (rodata_sckaKeyInfoPrefix himg)
    (rodata_zero32_recvCt2 himg)
    (rodata_ctLabel himg)
  dsimp only [recvCt2ChunkSpec]
  wpp_init x s0
  have hpc' : s0.pc = (tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName := by
    rw [tripleRatchetProgAtExt, Program.fnAddr_rebase, recvCt2Chunk_fnOff]; exact hpc
  have hinv : ImgCallInv img s0 := ⟨h_2, h_1⟩
  refine SepWPp.rw_pre ?_
    (recv_ct2_chunk_part1_wpp hA hadd_ok hdec_ok hdecaps x s0 R h_8
      hpc' hrun hsp_align h_3 hinv h_4 h_5 h_6 h_7
      (fun st2 receivingCt2 ct2Full cap_ct2 ptr_ct2 ptr_mac ptr_ct2_128 c3 _c7
        g_auth cap_dk ptr_dk cap_ct1 ptr_ct1
        hepoch hadd _hsort hdec hge128 hlt_max hct1_len htake128_len hdk_len
        hcap_ct1 hle_ct1 hmax_ct1 hptr_ct1
        hpc2 hrun2 hsp2 htr2 hvregs2 hinv2
        hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx29_2 => ?_))
  · dsimp only [recvCt2ChunkRoAt]; ac_rfl
  let ss_raw := (K.decaps ⟨x.self.uc.dk, hdk_len⟩ ⟨x.self.uc.ct1, hct1_len⟩ ⟨ct2Full.take 128, htake128_len⟩).toList
  have hss_raw_len : ss_raw.length = 32 :=
    (K.decaps ⟨x.self.uc.dk, hdk_len⟩ ⟨x.self.uc.ct1, hct1_len⟩ ⟨ct2Full.take 128, htake128_len⟩).2
  have hge_not_lt : ¬ ct2Full.length < 128 := by omega
  refine SepWPp.rw_pre ?_
    (recv_ct2_chunk_ss_hkdf_update_wpp hA hallocZeroed hconcat2 hhkdf hupdate
      x ss_raw ct2Full ptr_ct2 ptr_dk ptr_ct2_128 cap_ct2 c3 g_auth s0 st2
      (memRegion x.outA chunkedEkSentCt1ReceivedSize ∗
        memRegion x.selfA chunkedEkSentCt1ReceivedSize ∗
        ct2DeallocAt A cap_ct2 ptr_ct2 ∗
        ct2DeallocAt A cap_dk ptr_dk ∗
        (ptr_ct2_128 ↦ₛ ct2Full.take 128) ∗
        A.live ptr_ct2_128 128 1 ∗
        vecBufAt A (BitVec.ofNat 64 (ct2Full.length - 128)) ptr_mac (ct2Full.drop 128) ∗
        vecU8At A (s0.sp - 1280#64) cap_ct1 ptr_ct1 x.self.uc.ct1 ∗
        memRegion (s0.sp - 2000#64) 144 ∗
        memRegion (s0.sp - 1344#64) 16 ∗
        unusedFrameAt (s0.sp - 2496#64) ∗
        ((s0.sp - 2496#64) ↦₆₄ 0#64) ∗
        ((s0.sp - 2488#64) ↦₆₄ ptr_dk) ∗
        ((s0.sp - 2480#64) ↦₆₄ BitVec.ofNat 64 ct2Full.length) ∗
        ((s0.sp - 2464#64) ↦₆₄ cap_ct2) ∗
        ((s0.sp - 2456#64) ↦₆₄ cap_dk) ∗
        ((s0.sp - 2448#64) ↦₆₄ ptr_mac) ∗
        ((s0.sp - 2440#64) ↦₆₄ ptr_ct1) ∗
        ((s0.sp - 2432#64) ↦₆₄ x.epoch) ∗
        polyDecoderAt A (s0.sp - 2424#64) receivingCt2 ∗
        memRegion (s0.sp - 2024#64) 24 ∗
        memRegion (s0.sp - 1856#64) 504 ∗
        chunkAt x.chunkA x.chunk ∗
        tokenInitAt img.base ∗
        reduceTableAt img.base ∗
        savedRegsAt s0)
      R hss_raw_len htake128_len h h_3
      hpc2 hrun2 hsp2 hsp_align htr2 hvregs2 hinv2
      hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx29_2
      (fun st3 cap_info ptr_info ptr_ss_raw ptr_ss g_auth'
        _hptr_ss_raw_ne _hptr_ss_ne
        hpc3 hrun3 hsp3 htr3 hvregs3 hinv3
        hx19_3 _hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 _hx26_3 hx27_3 hx28_3 hx29_3 => ?_))
  · dsimp only [ss_raw]; ac_rfl
  refine SepWPp.fold
    (vecU8At_expose_sp_1280 A s0.sp cap_ct1 ptr_ct1 x.self.uc.ct1 (by omega))
    (by sep_focus) ?_
  refine SepWPp.pure_left_focus _ (by sep_focus) fun _ => ?_
  refine SepWPp.rw_pre (by rw [hct1_len]) ?_
  refine SepWPp.rw_pre ?_
    (recv_ct2_chunk_reserve_ct1_wpp hres7 x cap_ct1 ptr_ct1 s0 st3
      (recvCt2ChunkRoAt img ∗
        authenticatorPinAt A g_auth' (s0.sp - 1328#64)
          (x.self.uc.auth.update F x.epoch
            (spqrHkdfWith F (List.replicate 32 0#8) ss_raw
              (sckaKeyInfoPrefix ++ toBEBytes 8 x.epoch) 32)) ∗
        (ptr_ss_raw ↦ₛ ss_raw) ∗
        A.live ptr_ss_raw 32 1 ∗
        (ptr_ss ↦ₛ
          spqrHkdfWith F (List.replicate 32 0#8) ss_raw
            (sckaKeyInfoPrefix ++ toBEBytes 8 x.epoch) 32) ∗
        A.live ptr_ss 32 1 ∗
        ct2DeallocAt A cap_info ptr_info ∗
        ((s0.sp - 152#64) ↦₆₄ cap_info) ∗
        ((s0.sp - 144#64) ↦₆₄ ptr_info) ∗
        ((s0.sp - 136#64) ↦₆₄ 41#64) ∗
        memRegion (s0.sp - 128#64) 8 ∗
        memRegion (s0.sp - 288#64) 128 ∗
        memRegion (s0.sp - 1248#64) 960 ∗
        ((s0.sp - 2472#64) ↦₆₄ ptr_info) ∗
        memRegion x.outA chunkedEkSentCt1ReceivedSize ∗
        memRegion x.selfA chunkedEkSentCt1ReceivedSize ∗
        ct2DeallocAt A cap_ct2 ptr_ct2 ∗
        ct2DeallocAt A cap_dk ptr_dk ∗
        (ptr_ct2_128 ↦ₛ ct2Full.take 128) ∗
        A.live ptr_ct2_128 128 1 ∗
        vecBufAt A (BitVec.ofNat 64 (ct2Full.length - 128)) ptr_mac (ct2Full.drop 128) ∗
        memRegion (s0.sp - 2000#64) 144 ∗
        memRegion (s0.sp - 1344#64) 16 ∗
        unusedFrameAt (s0.sp - 2496#64) ∗
        ((s0.sp - 2496#64) ↦₆₄ 0#64) ∗
        ((s0.sp - 2488#64) ↦₆₄ ptr_dk) ∗
        ((s0.sp - 2480#64) ↦₆₄ BitVec.ofNat 64 ct2Full.length) ∗
        ((s0.sp - 2464#64) ↦₆₄ cap_ct2) ∗
        ((s0.sp - 2456#64) ↦₆₄ cap_dk) ∗
        ((s0.sp - 2448#64) ↦₆₄ ptr_mac) ∗
        ((s0.sp - 2432#64) ↦₆₄ x.epoch) ∗
        polyDecoderAt A (s0.sp - 2424#64) receivingCt2 ∗
        memRegion (s0.sp - 2024#64) 24 ∗
        memRegion (s0.sp - 1856#64) 504 ∗
        chunkAt x.chunkA x.chunk ∗
        tokenInitAt img.base ∗
        reduceTableAt img.base ∗
        savedRegsAt s0)
      R hct1_len hcap_ct1 hle_ct1 hmax_ct1 hptr_ct1
      hpc3 hrun3 hsp3 hsp_align htr3 hvregs3 hinv3
      (fun st4 cap_ct1' ptr_ct1'
        hcap_ct1'_ne hge1088 hmax_ct1' hptr_ct1'_ne
        hpc4 hrun4 hsp4 htr4 hvregs4 hinv4
        hx8_4 hx19_4 _hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 _hx26_4 hx27_4 hx28_4 hx29_4 => ?_))
  · ac_rfl
  let ss := spqrHkdfWith F (List.replicate 32 0#8) ss_raw (sckaKeyInfoPrefix ++ toBEBytes 8 x.epoch) 32
  let auth' := x.self.uc.auth.update F x.epoch ss
  have hss_len : ss.length = 32 := length_spqrHkdfWith F _ _ _ 32
  have hmk_len : auth'.macKey.length = 32 := auth_update_macKey_length_32 F x.self.uc.auth x.epoch ss
  have hrk_len : auth'.rootKey.length = 32 := auth_update_rootKey_length_32 F x.self.uc.auth x.epoch ss
  refine SepWPp.rw_pre ?_
    (recv_ct2_chunk_append_hmac_wpp hA hconcat3 hhmac x ct2Full auth' g_auth'
      cap_ct1' ptr_ct1' ptr_ct2_128 0#64 s0 st4
      (((img.base + bv% (ls_xref% 0x59a38 0x59a3c)) ↦ᵣ sckaKeyInfoPrefix) ∗
        ((img.base + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964")) ↦ᵣ List.replicate 32 0#8) ∗
        (ptr_ss_raw ↦ₛ ss_raw) ∗
        A.live ptr_ss_raw 32 1 ∗
        (ptr_ss ↦ₛ ss) ∗
        A.live ptr_ss 32 1 ∗
        ct2DeallocAt A cap_info ptr_info ∗
        ((s0.sp - 152#64) ↦₆₄ cap_info) ∗
        ((s0.sp - 144#64) ↦₆₄ ptr_info) ∗
        ((s0.sp - 136#64) ↦₆₄ 41#64) ∗
        memRegion (s0.sp - 128#64) 8 ∗
        ((s0.sp - 2472#64) ↦₆₄ ptr_info) ∗
        memRegion x.outA chunkedEkSentCt1ReceivedSize ∗
        memRegion x.selfA chunkedEkSentCt1ReceivedSize ∗
        ct2DeallocAt A cap_ct2 ptr_ct2 ∗
        ct2DeallocAt A cap_dk ptr_dk ∗
        A.live ptr_ct2_128 128 1 ∗
        vecBufAt A (BitVec.ofNat 64 (ct2Full.length - 128)) ptr_mac (ct2Full.drop 128) ∗
        memRegion (s0.sp - 1344#64) 16 ∗
        unusedFrameAt (s0.sp - 2496#64) ∗
        ((s0.sp - 2488#64) ↦₆₄ ptr_dk) ∗
        ((s0.sp - 2480#64) ↦₆₄ BitVec.ofNat 64 ct2Full.length) ∗
        ((s0.sp - 2464#64) ↦₆₄ cap_ct2) ∗
        ((s0.sp - 2456#64) ↦₆₄ cap_dk) ∗
        ((s0.sp - 2448#64) ↦₆₄ ptr_mac) ∗
        ((s0.sp - 2432#64) ↦₆₄ x.epoch) ∗
        polyDecoderAt A (s0.sp - 2424#64) receivingCt2 ∗
        memRegion (s0.sp - 2024#64) 24 ∗
        memRegion (s0.sp - 1856#64) 504 ∗
        chunkAt x.chunkA x.chunk ∗
        tokenInitAt img.base ∗
        reduceTableAt img.base ∗
        memRegion (s0.sp - 19552#64) 672 ∗
        savedRegsAt s0)
      R hct1_len htake128_len hmk_len hcap_ct1'_ne hge1088 hmax_ct1' hptr_ct1'_ne h_3
      hpc4 hrun4 hsp4 hsp_align htr4 hvregs4 hinv4
      hx8_4 (by rw [hx25_4, hx25_3]) (by rw [hx28_4, hx28_3]) (by rw [hx29_4, hx29_3])
      (fun st5 hmk_cap_ne hmk_le hmk_max hmk_ptr_ne
        hpc5 hrun5 hsp5 htr5 hvregs5 hinv5
        hx19_5 hx21_5 hx22_5 hx23_5 hx24_5 hx25_5 _hx26_5 hx27_5 hx29_5 => ?_))
  · dsimp only [recvCt2ChunkRoAt, auth', ss]; ac_rfl
  refine SepWPp.rw_pre ?_
    (recv_ct2_chunk_mac_compare_wpp hA x receivingCt2 ct2Full auth' ptr_mac s0 st5
      (((s0.sp - 1280#64) ↦₆₄ cap_ct1') ∗
        ((s0.sp - 1272#64) ↦₆₄ ptr_ct1') ∗
        ((s0.sp - 1264#64) ↦₆₄ 960#64) ∗
        ct2DeallocAt A cap_ct1' ptr_ct1' ∗
        ((s0.sp - 2440#64) ↦₆₄ ptr_ct1') ∗
        (ptr_ct2_128 ↦ₛ ct2Full.take 128) ∗
        vecU8At A (s0.sp - 1328#64) g_auth'.rootKey.cap g_auth'.rootKey.ptr auth'.rootKey ∗
        ((s0.sp - 1304#64) ↦₆₄ g_auth'.macKey.cap) ∗
        ((s0.sp - 1296#64) ↦₆₄ g_auth'.macKey.ptr) ∗
        ((s0.sp - 1288#64) ↦₆₄ 32#64) ∗
        (g_auth'.macKey.ptr ↦ₛ auth'.macKey) ∗
        memRegion (g_auth'.macKey.ptr + 32#64) (g_auth'.macKey.cap.toNat - 32) ∗
        A.live g_auth'.macKey.ptr g_auth'.macKey.cap.toNat 1 ∗
        ((s0.sp - 2496#64) ↦₆₄ g_auth'.macKey.ptr) ∗
        memRegion (s0.sp - 288#64) 128 ∗
        memRegion (s0.sp - 2000#64) 144 ∗
        ((img.base + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel) ∗
        ((img.base + bv% (ls_xref% 0x59a38 0x59a3c)) ↦ᵣ sckaKeyInfoPrefix) ∗
        ((img.base + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964")) ↦ᵣ List.replicate 32 0#8) ∗
        (ptr_ss_raw ↦ₛ ss_raw) ∗
        A.live ptr_ss_raw 32 1 ∗
        (ptr_ss ↦ₛ ss) ∗
        A.live ptr_ss 32 1 ∗
        ct2DeallocAt A cap_info ptr_info ∗
        ((s0.sp - 152#64) ↦₆₄ cap_info) ∗
        ((s0.sp - 144#64) ↦₆₄ ptr_info) ∗
        ((s0.sp - 136#64) ↦₆₄ 41#64) ∗
        memRegion (s0.sp - 128#64) 8 ∗
        ((s0.sp - 2472#64) ↦₆₄ ptr_info) ∗
        memRegion x.outA chunkedEkSentCt1ReceivedSize ∗
        memRegion x.selfA chunkedEkSentCt1ReceivedSize ∗
        ct2DeallocAt A cap_ct2 ptr_ct2 ∗
        ct2DeallocAt A cap_dk ptr_dk ∗
        A.live ptr_ct2_128 128 1 ∗
        memRegion (s0.sp - 1344#64) 16 ∗
        unusedFrameAt (s0.sp - 2496#64) ∗
        ((s0.sp - 2488#64) ↦₆₄ ptr_dk) ∗
        ((s0.sp - 2464#64) ↦₆₄ cap_ct2) ∗
        ((s0.sp - 2456#64) ↦₆₄ cap_dk) ∗
        ((s0.sp - 2432#64) ↦₆₄ x.epoch) ∗
        polyDecoderAt A (s0.sp - 2424#64) receivingCt2 ∗
        memRegion (s0.sp - 2024#64) 24 ∗
        memRegion (s0.sp - 1856#64) 504 ∗
        chunkAt x.chunkA x.chunk ∗
        tokenInitAt img.base ∗
        reduceTableAt img.base ∗
        memRegion (s0.sp - 19552#64) 672 ∗
        savedRegsAt s0)
      R hepoch hadd hdec hge_not_lt hlt_max hct1_len hdk_len
      hpc5 hrun5 hsp5 hsp_align htr5 hvregs5 hinv5
      (by rw [hx23_5, hx23_4, hx23_3])
      (fun st_err hm_le32 hcmp_err
        hpc_err hrun_err hsp_err htr_err hvregs_err hinv_err
        hx19_err hx20_err hx21_err _hx22_err hx23_err hx24_err hx25_err hx27_err hx29_err => ?_)
      (fun st_ok hm_le32 hcmp_ok
        hpc_ok hrun_ok hsp_ok htr_ok hvregs_ok hinv_ok
        hx19_ok hx20_ok hx21_ok hx22_ok hx23_ok hx24_ok hx25_ok hx27_ok hx29_ok => ?_))
  · ac_rfl
  · -- `Err(Error::MacVerifyFailed)` at `0x5eff4` (`+968`)
    have hcmp_err' :
        (let hct2 : (ct2Full.take 128).length = 128 := by rw [List.length_take]; omega
         let ss_raw0 := (K.decaps ⟨x.self.uc.dk, hdk_len⟩ ⟨x.self.uc.ct1, hct1_len⟩ ⟨ct2Full.take 128, hct2⟩).toList
         let info0 := sckaKeyInfoPrefix ++ toBEBytes 8 x.self.uc.epoch
         let ss0 := spqrHkdfWith F (List.replicate 32 0#8) ss_raw0 info0 32
         let auth0 := x.self.uc.auth.update F x.self.uc.epoch ss0
         let ct1Full0 := x.self.uc.ct1 ++ ct2Full.take 128
         let tag0 := hmacWith F auth0.macKey (Authenticator.ctLabel ++ toBEBytes 8 x.self.uc.epoch ++ ct1Full0)
         compare_prefix (ct2Full.drop 128) tag0 != 0#8) = true := by
      dsimp only
      rw [← macCtUnchecked_eq_hmacWith]
      simpa only [auth', ss, ss_raw, hepoch] using hcmp_err
    have hres_err : x.self.recv_ct2_chunk K x.epoch x.chunk = .error (.err .macVerifyFailed) :=
      recv_ct2_chunk_eq_err_macVerifyFailed x.self x.epoch x.chunk receivingCt2 ct2Full
        hepoch hadd hdec hge_not_lt hct1_len hdk_len hm_le32 hcmp_err'
    have hgt128 : 128 < ct2Full.length :=
      lt_128_of_compare_prefix_drop_bne hcmp_err
    refine SepWPp.rw_pre ?_
      (recv_ct2_chunk_err_wpp hA hdealloc_ext x receivingCt2 ct2Full ss_raw ss auth' g_auth'
        cap_ct2 ptr_ct2 cap_dk ptr_dk cap_ct1' ptr_ct1'
        cap_info ptr_info ptr_ss_raw ptr_ss ptr_mac ptr_ct2_128
        s0 st_err R
        hres_err hgt128 hlt_max hss_raw_len hss_len htake128_len hrk_len hmk_len
        hmk_cap_ne hmk_le hmk_max hmk_ptr_ne
        hpc_err hrun_err hsp_err hsp_align htr_err hvregs_err hinv_err
        (by rw [hx19_err, hx19_5, hx19_4, hx19_3])
        hx20_err
        (by rw [hx21_err, hx21_5, hx21_4, hx21_3])
        hx23_err
        (by rw [hx24_err, hx24_5, hx24_4, hx24_3])
        (by rw [hx25_err, hx25_5])
        (by rw [hx27_err, hx27_5, hx27_4, hx27_3])
        (by rw [hx29_err, hx29_5]))
    · dsimp only [recvCt2ChunkRoAt]; ac_rfl
  · -- `Ok(Done(NoHeaderReceived, EpochSecret))` at `0x5f148` (`+1308`)
    have hcmp_ok' :
        (let hct2 : (ct2Full.take 128).length = 128 := by rw [List.length_take]; omega
         let ss_raw0 := (K.decaps ⟨x.self.uc.dk, hdk_len⟩ ⟨x.self.uc.ct1, hct1_len⟩ ⟨ct2Full.take 128, hct2⟩).toList
         let info0 := sckaKeyInfoPrefix ++ toBEBytes 8 x.self.uc.epoch
         let ss0 := spqrHkdfWith F (List.replicate 32 0#8) ss_raw0 info0 32
         let auth0 := x.self.uc.auth.update F x.self.uc.epoch ss0
         let ct1Full0 := x.self.uc.ct1 ++ ct2Full.take 128
         let tag0 := hmacWith F auth0.macKey (Authenticator.ctLabel ++ toBEBytes 8 x.self.uc.epoch ++ ct1Full0)
         compare_prefix (ct2Full.drop 128) tag0 != 0#8) = false := by
      dsimp only
      rw [← macCtUnchecked_eq_hmacWith]
      simpa only [auth', ss, ss_raw, hepoch] using hcmp_ok
    have hss_eq :
        (let hct2 : (ct2Full.take 128).length = 128 := by rw [List.length_take]; omega
         let ss_raw0 := (K.decaps ⟨x.self.uc.dk, hdk_len⟩ ⟨x.self.uc.ct1, hct1_len⟩ ⟨ct2Full.take 128, hct2⟩).toList
         let info0 := sckaKeyInfoPrefix ++ toBEBytes 8 x.self.uc.epoch
         ss = spqrHkdfWith F (List.replicate 32 0#8) ss_raw0 info0 32) := by
      dsimp only [ss, ss_raw]
      rw [hepoch]
    have hauth'_eq : auth' = x.self.uc.auth.update F x.self.uc.epoch ss := by
      dsimp only [auth']
      rw [hepoch]
    refine SepWPp.rw_pre ?_
      (recv_ct2_chunk_ok_done_dealloc_wpp hA hdealloc_ext x receivingCt2 ct2Full
        cap_ct2 ptr_ct2 ptr_ct2_128 ptr_mac cap_dk ptr_dk cap_ct1' ptr_ct1'
        ptr_ss_raw cap_info ptr_info ptr_ss ss_raw ss auth' g_auth' s0 st_ok R
        hepoch hadd hdec hge128 hlt_max hct1_len hdk_len hm_le32 hcmp_ok'
        hss_eq hauth'_eq hss_len hss_raw_len htake128_len hrk_len hmk_len
        hmk_cap_ne hmk_le hmk_max hmk_ptr_ne
        hpc_ok hrun_ok hsp_ok hsp_align htr_ok hvregs_ok hinv_ok
        (by rw [hx19_ok, hx19_5, hx19_4, hx19_3])
        hx20_ok
        (by rw [hx21_ok, hx21_5, hx21_4, hx21_3])
        (by rw [hx22_ok, hx22_5, hx22_4, hx22_3])
        hx23_ok
        (by rw [hx24_ok, hx24_5, hx24_4, hx24_3])
        (by rw [hx25_ok, hx25_5])
        (by rw [hx27_ok, hx27_5, hx27_4, hx27_3])
        (by rw [hx29_ok, hx29_5]))
    · dsimp only [recvCt2ChunkRoAt]; ac_rfl

/-- Unconditional corollary of `recv_ct2_chunk_ok_x` discharging `AddChunkOkX`,
`PolyDecodedMessageOkX`, and `DeallocOkExt` via `add_chunk_ok_x`, `polyDecoderDecodedMessage_ok`,
and `hA_raw.dealloc`. -/
theorem recv_ct2_chunk_ok_x_of_decodedMessage {img : Obj.Image} {K : MlKem} {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA_raw : AllocContracts img.base A ext)
    (hA : AllocContractsX img A ext)
    (hallocZeroed : AllocZeroedWithStackOkX img A ext)
    (hdecaps : HookSat ext mlkemDecapsName (mlkemDecapsSpec K))
    (hconcat2 : SliceConcat2OkX img A ext)
    (hconcat3 : SliceConcat3OkX img A ext)
    (hhkdf : HkdfToSliceSpqrOkX img (spqrHkdfWith F) ext)
    (hupdate : AuthUpdateOkX img F A ext)
    (hres7 : DoReserve7OkX img A ext)
    (hhmac : HookSat ext libcruxHmacName (libcruxHmacSpec F A)) :
    RecvCt2ChunkOkX img K F A ext :=
  recv_ct2_chunk_ok_x himg hA hA_raw.dealloc hallocZeroed (add_chunk_ok_x hA_raw)
    (polyDecodedMessageOkX_of_alloc hA_raw)
    hdecaps hconcat2 hconcat3 hhkdf hupdate hres7 hhmac

/-! ## Contract-Backed Composition: `recv_ct2_chunk_ok_ext` -/

set_option maxHeartbeats 1600000 in
theorem recv_ct2_chunk_ok_ext {img : Obj.Image} {K : MlKem} {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContractsX img A ext)
    (hdealloc_ext : DeallocOkExt img.base A ext)
    (hallocZeroed : AllocZeroedWithStackOkX img A ext)
    (hadd_ok : AddChunkOkX img A ext)
    (hdec_ok : PolyDecodedMessageOkX img A ext)
    (hdecaps : HookSat ext mlkemDecapsName (mlkemDecapsSpec K))
    (hconcat2 : SliceConcat2OkX img A ext)
    (hconcat3 : SliceConcat3OkX img A ext)
    (hhkdf : HkdfToSliceSpqrOkExt img (spqrHkdfWith F) ext)
    (hupdate : AuthUpdateOkExt img F A ext)
    (hres7 : DoReserve7OkX img A ext)
    (hhmac : HookSat ext libcruxHmacName (libcruxHmacSpec F A)) :
    RecvCt2ChunkOkExt img K F A ext := by
  unfold RecvCt2ChunkOkExt
  apply subroutine_ok_inImage_rodata3_keep
    (rodata_sckaKeyInfoPrefix himg)
    (rodata_zero32_recvCt2 himg)
    (rodata_ctLabel himg)
  dsimp only [recvCt2ChunkSpecExt]
  wpp_init x s0
  have hpc' : s0.pc = (tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName := by
    rw [tripleRatchetProgAtExt, Program.fnAddr_rebase, recvCt2Chunk_fnOff]; exact hpc
  have hinv : ImgCallInv img s0 := ⟨h_2, h_1⟩
  refine SepWPp.rw_pre ?_
    (recv_ct2_chunk_part1_wpp_ext hA hadd_ok hdec_ok hdecaps x s0 R h_8
      hpc' hrun hsp_align h_3 hinv h_4 h_5 h_6 h_7
      (fun st2 receivingCt2 ct2Full cap_ct2 ptr_ct2 ptr_mac ptr_ct2_128 c3 _c7
        g_auth cap_dk ptr_dk cap_ct1 ptr_ct1
        hepoch hadd _hsort hdec hge128 hlt_max hct1_len htake128_len hdk_len
        hcap_ct1 hle_ct1 hmax_ct1 hptr_ct1
        hpc2 hrun2 hsp2 htr2 hvregs2 hinv2
        hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx29_2 => ?_))
  · dsimp only [recvCt2ChunkRoAt]; ac_rfl
  let ss_raw := (K.decaps ⟨x.self.uc.dk, hdk_len⟩ ⟨x.self.uc.ct1, hct1_len⟩ ⟨ct2Full.take 128, htake128_len⟩).toList
  have hss_raw_len : ss_raw.length = 32 :=
    (K.decaps ⟨x.self.uc.dk, hdk_len⟩ ⟨x.self.uc.ct1, hct1_len⟩ ⟨ct2Full.take 128, htake128_len⟩).2
  have hge_not_lt : ¬ ct2Full.length < 128 := by omega
  refine SepWPp.rw_pre ?_
    (recv_ct2_chunk_ss_hkdf_update_wpp_ext hA hallocZeroed hconcat2 hhkdf hupdate
      x ss_raw ct2Full ptr_ct2 ptr_dk ptr_ct2_128 cap_ct2 c3 g_auth s0 st2
      (memRegion x.outA chunkedEkSentCt1ReceivedSize ∗
        memRegion x.selfA chunkedEkSentCt1ReceivedSize ∗
        ct2DeallocAt A cap_ct2 ptr_ct2 ∗
        ct2DeallocAt A cap_dk ptr_dk ∗
        (ptr_ct2_128 ↦ₛ ct2Full.take 128) ∗
        A.live ptr_ct2_128 128 1 ∗
        vecBufAt A (BitVec.ofNat 64 (ct2Full.length - 128)) ptr_mac (ct2Full.drop 128) ∗
        vecU8At A (s0.sp - 1280#64) cap_ct1 ptr_ct1 x.self.uc.ct1 ∗
        memRegion (s0.sp - 2000#64) 144 ∗
        memRegion (s0.sp - 1344#64) 16 ∗
        unusedFrameAt (s0.sp - 2496#64) ∗
        ((s0.sp - 2496#64) ↦₆₄ 0#64) ∗
        ((s0.sp - 2488#64) ↦₆₄ ptr_dk) ∗
        ((s0.sp - 2480#64) ↦₆₄ BitVec.ofNat 64 ct2Full.length) ∗
        ((s0.sp - 2464#64) ↦₆₄ cap_ct2) ∗
        ((s0.sp - 2456#64) ↦₆₄ cap_dk) ∗
        ((s0.sp - 2448#64) ↦₆₄ ptr_mac) ∗
        ((s0.sp - 2440#64) ↦₆₄ ptr_ct1) ∗
        ((s0.sp - 2432#64) ↦₆₄ x.epoch) ∗
        polyDecoderAt A (s0.sp - 2424#64) receivingCt2 ∗
        memRegion (s0.sp - 2024#64) 24 ∗
        memRegion (s0.sp - 1856#64) 504 ∗
        chunkAt x.chunkA x.chunk ∗
        tokenInitAt img.base ∗
        reduceTableAt img.base ∗
        savedRegsAt s0)
      R hss_raw_len htake128_len h h_3
      hpc2 hrun2 hsp2 hsp_align htr2 hvregs2 hinv2
      hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx29_2
      (fun st3 cap_info ptr_info ptr_ss_raw ptr_ss g_auth'
        _hptr_ss_raw_ne _hptr_ss_ne
        hpc3 hrun3 hsp3 htr3 hvregs3 hinv3
        hx19_3 _hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 _hx26_3 hx27_3 hx28_3 hx29_3 => ?_))
  · dsimp only [ss_raw]; ac_rfl
  refine SepWPp.rw_pre (show _ =
    (recvCt2ChunkRoAt img ∗
      authenticatorPinAt A g_auth' (s0.sp - 1328#64)
        (x.self.uc.auth.update F x.epoch
          (spqrHkdfWith F (List.replicate 32 0#8) ss_raw
            (sckaKeyInfoPrefix ++ toBEBytes 8 x.epoch) 32)) ∗
      (ptr_ss_raw ↦ₛ ss_raw) ∗
      A.live ptr_ss_raw 32 1 ∗
      (ptr_ss ↦ₛ
        spqrHkdfWith F (List.replicate 32 0#8) ss_raw
          (sckaKeyInfoPrefix ++ toBEBytes 8 x.epoch) 32) ∗
      A.live ptr_ss 32 1 ∗
      ct2DeallocAt A cap_info ptr_info ∗
      ((s0.sp - 152#64) ↦₆₄ cap_info) ∗
      ((s0.sp - 144#64) ↦₆₄ ptr_info) ∗
      ((s0.sp - 136#64) ↦₆₄ 41#64) ∗
      memRegion (s0.sp - 128#64) 8 ∗
      memRegion (s0.sp - 288#64) 128 ∗
      memRegion (s0.sp - 1248#64) 960 ∗
      ((s0.sp - 2472#64) ↦₆₄ ptr_info) ∗
      A.pool ∗
      memRegion (s0.sp - 19552#64) 672 ∗
      stackAt (s0.sp - 2496#64) extHookStack ∗
      (memRegion x.outA chunkedEkSentCt1ReceivedSize ∗
        memRegion x.selfA chunkedEkSentCt1ReceivedSize ∗
        ct2DeallocAt A cap_ct2 ptr_ct2 ∗
        ct2DeallocAt A cap_dk ptr_dk ∗
        (ptr_ct2_128 ↦ₛ ct2Full.take 128) ∗
        A.live ptr_ct2_128 128 1 ∗
        vecBufAt A (BitVec.ofNat 64 (ct2Full.length - 128)) ptr_mac (ct2Full.drop 128) ∗
        vecU8At A (s0.sp - 1280#64) cap_ct1 ptr_ct1 x.self.uc.ct1 ∗
        memRegion (s0.sp - 2000#64) 144 ∗
        memRegion (s0.sp - 1344#64) 16 ∗
        unusedFrameAt (s0.sp - 2496#64) ∗
        ((s0.sp - 2496#64) ↦₆₄ 0#64) ∗
        ((s0.sp - 2488#64) ↦₆₄ ptr_dk) ∗
        ((s0.sp - 2480#64) ↦₆₄ BitVec.ofNat 64 ct2Full.length) ∗
        ((s0.sp - 2464#64) ↦₆₄ cap_ct2) ∗
        ((s0.sp - 2456#64) ↦₆₄ cap_dk) ∗
        ((s0.sp - 2448#64) ↦₆₄ ptr_mac) ∗
        ((s0.sp - 2440#64) ↦₆₄ ptr_ct1) ∗
        ((s0.sp - 2432#64) ↦₆₄ x.epoch) ∗
        polyDecoderAt A (s0.sp - 2424#64) receivingCt2 ∗
        memRegion (s0.sp - 2024#64) 24 ∗
        memRegion (s0.sp - 1856#64) 504 ∗
        chunkAt x.chunkA x.chunk ∗
        tokenInitAt img.base ∗
        reduceTableAt img.base ∗
        savedRegsAt s0)) ∗ memRegion (s0.sp - 20272#64) 720 by ac_rfl) ?_
  apply sepWPp_frame_recvCt2_ext
  let R' := memRegion (s0.sp - 20272#64) 720 ∗ R
  change SepWPp _ _ _ _
    (recvCt2ChunkPostQ img K F A x s0 R')
    (recvCt2ChunkPostQp K F A img.base x s0 R')
  refine SepWPp.fold
    (vecU8At_expose_sp_1280 A s0.sp cap_ct1 ptr_ct1 x.self.uc.ct1 (by omega))
    (by sep_focus) ?_
  refine SepWPp.pure_left_focus _ (by sep_focus) fun _ => ?_
  refine SepWPp.rw_pre (by rw [hct1_len]) ?_
  refine SepWPp.rw_pre ?_
    (recv_ct2_chunk_reserve_ct1_wpp hres7 x cap_ct1 ptr_ct1 s0 st3
      (recvCt2ChunkRoAt img ∗
        authenticatorPinAt A g_auth' (s0.sp - 1328#64)
          (x.self.uc.auth.update F x.epoch
            (spqrHkdfWith F (List.replicate 32 0#8) ss_raw
              (sckaKeyInfoPrefix ++ toBEBytes 8 x.epoch) 32)) ∗
        (ptr_ss_raw ↦ₛ ss_raw) ∗
        A.live ptr_ss_raw 32 1 ∗
        (ptr_ss ↦ₛ
          spqrHkdfWith F (List.replicate 32 0#8) ss_raw
            (sckaKeyInfoPrefix ++ toBEBytes 8 x.epoch) 32) ∗
        A.live ptr_ss 32 1 ∗
        ct2DeallocAt A cap_info ptr_info ∗
        ((s0.sp - 152#64) ↦₆₄ cap_info) ∗
        ((s0.sp - 144#64) ↦₆₄ ptr_info) ∗
        ((s0.sp - 136#64) ↦₆₄ 41#64) ∗
        memRegion (s0.sp - 128#64) 8 ∗
        memRegion (s0.sp - 288#64) 128 ∗
        memRegion (s0.sp - 1248#64) 960 ∗
        ((s0.sp - 2472#64) ↦₆₄ ptr_info) ∗
        memRegion x.outA chunkedEkSentCt1ReceivedSize ∗
        memRegion x.selfA chunkedEkSentCt1ReceivedSize ∗
        ct2DeallocAt A cap_ct2 ptr_ct2 ∗
        ct2DeallocAt A cap_dk ptr_dk ∗
        (ptr_ct2_128 ↦ₛ ct2Full.take 128) ∗
        A.live ptr_ct2_128 128 1 ∗
        vecBufAt A (BitVec.ofNat 64 (ct2Full.length - 128)) ptr_mac (ct2Full.drop 128) ∗
        memRegion (s0.sp - 2000#64) 144 ∗
        memRegion (s0.sp - 1344#64) 16 ∗
        unusedFrameAt (s0.sp - 2496#64) ∗
        ((s0.sp - 2496#64) ↦₆₄ 0#64) ∗
        ((s0.sp - 2488#64) ↦₆₄ ptr_dk) ∗
        ((s0.sp - 2480#64) ↦₆₄ BitVec.ofNat 64 ct2Full.length) ∗
        ((s0.sp - 2464#64) ↦₆₄ cap_ct2) ∗
        ((s0.sp - 2456#64) ↦₆₄ cap_dk) ∗
        ((s0.sp - 2448#64) ↦₆₄ ptr_mac) ∗
        ((s0.sp - 2432#64) ↦₆₄ x.epoch) ∗
        polyDecoderAt A (s0.sp - 2424#64) receivingCt2 ∗
        memRegion (s0.sp - 2024#64) 24 ∗
        memRegion (s0.sp - 1856#64) 504 ∗
        chunkAt x.chunkA x.chunk ∗
        tokenInitAt img.base ∗
        reduceTableAt img.base ∗
        savedRegsAt s0)
      R' hct1_len hcap_ct1 hle_ct1 hmax_ct1 hptr_ct1
      hpc3 hrun3 hsp3 hsp_align htr3 hvregs3 hinv3
      (fun st4 cap_ct1' ptr_ct1'
        hcap_ct1'_ne hge1088 hmax_ct1' hptr_ct1'_ne
        hpc4 hrun4 hsp4 htr4 hvregs4 hinv4
        hx8_4 hx19_4 _hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 _hx26_4 hx27_4 hx28_4 hx29_4 => ?_))
  · ac_rfl
  let ss := spqrHkdfWith F (List.replicate 32 0#8) ss_raw (sckaKeyInfoPrefix ++ toBEBytes 8 x.epoch) 32
  let auth' := x.self.uc.auth.update F x.epoch ss
  have hss_len : ss.length = 32 := length_spqrHkdfWith F _ _ _ 32
  have hmk_len : auth'.macKey.length = 32 := auth_update_macKey_length_32 F x.self.uc.auth x.epoch ss
  have hrk_len : auth'.rootKey.length = 32 := auth_update_rootKey_length_32 F x.self.uc.auth x.epoch ss
  refine SepWPp.rw_pre ?_
    (recv_ct2_chunk_append_hmac_wpp hA hconcat3 hhmac x ct2Full auth' g_auth'
      cap_ct1' ptr_ct1' ptr_ct2_128 0#64 s0 st4
      (((img.base + bv% (ls_xref% 0x59a38 0x59a3c)) ↦ᵣ sckaKeyInfoPrefix) ∗
        ((img.base + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964")) ↦ᵣ List.replicate 32 0#8) ∗
        (ptr_ss_raw ↦ₛ ss_raw) ∗
        A.live ptr_ss_raw 32 1 ∗
        (ptr_ss ↦ₛ ss) ∗
        A.live ptr_ss 32 1 ∗
        ct2DeallocAt A cap_info ptr_info ∗
        ((s0.sp - 152#64) ↦₆₄ cap_info) ∗
        ((s0.sp - 144#64) ↦₆₄ ptr_info) ∗
        ((s0.sp - 136#64) ↦₆₄ 41#64) ∗
        memRegion (s0.sp - 128#64) 8 ∗
        ((s0.sp - 2472#64) ↦₆₄ ptr_info) ∗
        memRegion x.outA chunkedEkSentCt1ReceivedSize ∗
        memRegion x.selfA chunkedEkSentCt1ReceivedSize ∗
        ct2DeallocAt A cap_ct2 ptr_ct2 ∗
        ct2DeallocAt A cap_dk ptr_dk ∗
        A.live ptr_ct2_128 128 1 ∗
        vecBufAt A (BitVec.ofNat 64 (ct2Full.length - 128)) ptr_mac (ct2Full.drop 128) ∗
        memRegion (s0.sp - 1344#64) 16 ∗
        unusedFrameAt (s0.sp - 2496#64) ∗
        ((s0.sp - 2488#64) ↦₆₄ ptr_dk) ∗
        ((s0.sp - 2480#64) ↦₆₄ BitVec.ofNat 64 ct2Full.length) ∗
        ((s0.sp - 2464#64) ↦₆₄ cap_ct2) ∗
        ((s0.sp - 2456#64) ↦₆₄ cap_dk) ∗
        ((s0.sp - 2448#64) ↦₆₄ ptr_mac) ∗
        ((s0.sp - 2432#64) ↦₆₄ x.epoch) ∗
        polyDecoderAt A (s0.sp - 2424#64) receivingCt2 ∗
        memRegion (s0.sp - 2024#64) 24 ∗
        memRegion (s0.sp - 1856#64) 504 ∗
        chunkAt x.chunkA x.chunk ∗
        tokenInitAt img.base ∗
        reduceTableAt img.base ∗
        memRegion (s0.sp - 19552#64) 672 ∗
        savedRegsAt s0)
      R' hct1_len htake128_len hmk_len hcap_ct1'_ne hge1088 hmax_ct1' hptr_ct1'_ne h_3
      hpc4 hrun4 hsp4 hsp_align htr4 hvregs4 hinv4
      hx8_4 (by rw [hx25_4, hx25_3]) (by rw [hx28_4, hx28_3]) (by rw [hx29_4, hx29_3])
      (fun st5 hmk_cap_ne hmk_le hmk_max hmk_ptr_ne
        hpc5 hrun5 hsp5 htr5 hvregs5 hinv5
        hx19_5 hx21_5 hx22_5 hx23_5 hx24_5 hx25_5 _hx26_5 hx27_5 hx29_5 => ?_))
  · dsimp only [recvCt2ChunkRoAt, auth', ss]; ac_rfl
  refine SepWPp.rw_pre ?_
    (recv_ct2_chunk_mac_compare_wpp hA x receivingCt2 ct2Full auth' ptr_mac s0 st5
      (((s0.sp - 1280#64) ↦₆₄ cap_ct1') ∗
        ((s0.sp - 1272#64) ↦₆₄ ptr_ct1') ∗
        ((s0.sp - 1264#64) ↦₆₄ 960#64) ∗
        ct2DeallocAt A cap_ct1' ptr_ct1' ∗
        ((s0.sp - 2440#64) ↦₆₄ ptr_ct1') ∗
        (ptr_ct2_128 ↦ₛ ct2Full.take 128) ∗
        vecU8At A (s0.sp - 1328#64) g_auth'.rootKey.cap g_auth'.rootKey.ptr auth'.rootKey ∗
        ((s0.sp - 1304#64) ↦₆₄ g_auth'.macKey.cap) ∗
        ((s0.sp - 1296#64) ↦₆₄ g_auth'.macKey.ptr) ∗
        ((s0.sp - 1288#64) ↦₆₄ 32#64) ∗
        (g_auth'.macKey.ptr ↦ₛ auth'.macKey) ∗
        memRegion (g_auth'.macKey.ptr + 32#64) (g_auth'.macKey.cap.toNat - 32) ∗
        A.live g_auth'.macKey.ptr g_auth'.macKey.cap.toNat 1 ∗
        ((s0.sp - 2496#64) ↦₆₄ g_auth'.macKey.ptr) ∗
        memRegion (s0.sp - 288#64) 128 ∗
        memRegion (s0.sp - 2000#64) 144 ∗
        ((img.base + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel) ∗
        ((img.base + bv% (ls_xref% 0x59a38 0x59a3c)) ↦ᵣ sckaKeyInfoPrefix) ∗
        ((img.base + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964")) ↦ᵣ List.replicate 32 0#8) ∗
        (ptr_ss_raw ↦ₛ ss_raw) ∗
        A.live ptr_ss_raw 32 1 ∗
        (ptr_ss ↦ₛ ss) ∗
        A.live ptr_ss 32 1 ∗
        ct2DeallocAt A cap_info ptr_info ∗
        ((s0.sp - 152#64) ↦₆₄ cap_info) ∗
        ((s0.sp - 144#64) ↦₆₄ ptr_info) ∗
        ((s0.sp - 136#64) ↦₆₄ 41#64) ∗
        memRegion (s0.sp - 128#64) 8 ∗
        ((s0.sp - 2472#64) ↦₆₄ ptr_info) ∗
        memRegion x.outA chunkedEkSentCt1ReceivedSize ∗
        memRegion x.selfA chunkedEkSentCt1ReceivedSize ∗
        ct2DeallocAt A cap_ct2 ptr_ct2 ∗
        ct2DeallocAt A cap_dk ptr_dk ∗
        A.live ptr_ct2_128 128 1 ∗
        memRegion (s0.sp - 1344#64) 16 ∗
        unusedFrameAt (s0.sp - 2496#64) ∗
        ((s0.sp - 2488#64) ↦₆₄ ptr_dk) ∗
        ((s0.sp - 2464#64) ↦₆₄ cap_ct2) ∗
        ((s0.sp - 2456#64) ↦₆₄ cap_dk) ∗
        ((s0.sp - 2432#64) ↦₆₄ x.epoch) ∗
        polyDecoderAt A (s0.sp - 2424#64) receivingCt2 ∗
        memRegion (s0.sp - 2024#64) 24 ∗
        memRegion (s0.sp - 1856#64) 504 ∗
        chunkAt x.chunkA x.chunk ∗
        tokenInitAt img.base ∗
        reduceTableAt img.base ∗
        memRegion (s0.sp - 19552#64) 672 ∗
        savedRegsAt s0)
      R' hepoch hadd hdec hge_not_lt hlt_max hct1_len hdk_len
      hpc5 hrun5 hsp5 hsp_align htr5 hvregs5 hinv5
      (by rw [hx23_5, hx23_4, hx23_3])
      (fun st_err hm_le32 hcmp_err
        hpc_err hrun_err hsp_err htr_err hvregs_err hinv_err
        hx19_err hx20_err hx21_err _hx22_err hx23_err hx24_err hx25_err hx27_err hx29_err => ?_)
      (fun st_ok hm_le32 hcmp_ok
        hpc_ok hrun_ok hsp_ok htr_ok hvregs_ok hinv_ok
        hx19_ok hx20_ok hx21_ok hx22_ok hx23_ok hx24_ok hx25_ok hx27_ok hx29_ok => ?_))
  · ac_rfl
  · -- `Err(Error::MacVerifyFailed)` at `0x5eff4` (`+968`)
    have hcmp_err' :
        (let hct2 : (ct2Full.take 128).length = 128 := by rw [List.length_take]; omega
         let ss_raw0 := (K.decaps ⟨x.self.uc.dk, hdk_len⟩ ⟨x.self.uc.ct1, hct1_len⟩ ⟨ct2Full.take 128, hct2⟩).toList
         let info0 := sckaKeyInfoPrefix ++ toBEBytes 8 x.self.uc.epoch
         let ss0 := spqrHkdfWith F (List.replicate 32 0#8) ss_raw0 info0 32
         let auth0 := x.self.uc.auth.update F x.self.uc.epoch ss0
         let ct1Full0 := x.self.uc.ct1 ++ ct2Full.take 128
         let tag0 := hmacWith F auth0.macKey (Authenticator.ctLabel ++ toBEBytes 8 x.self.uc.epoch ++ ct1Full0)
         compare_prefix (ct2Full.drop 128) tag0 != 0#8) = true := by
      dsimp only
      rw [← macCtUnchecked_eq_hmacWith]
      simpa only [auth', ss, ss_raw, hepoch] using hcmp_err
    have hres_err : x.self.recv_ct2_chunk K x.epoch x.chunk = .error (.err .macVerifyFailed) :=
      recv_ct2_chunk_eq_err_macVerifyFailed x.self x.epoch x.chunk receivingCt2 ct2Full
        hepoch hadd hdec hge_not_lt hct1_len hdk_len hm_le32 hcmp_err'
    have hgt128 : 128 < ct2Full.length :=
      lt_128_of_compare_prefix_drop_bne hcmp_err
    refine SepWPp.rw_pre ?_
      (recv_ct2_chunk_err_wpp hA hdealloc_ext x receivingCt2 ct2Full ss_raw ss auth' g_auth'
        cap_ct2 ptr_ct2 cap_dk ptr_dk cap_ct1' ptr_ct1'
        cap_info ptr_info ptr_ss_raw ptr_ss ptr_mac ptr_ct2_128
        s0 st_err R'
        hres_err hgt128 hlt_max hss_raw_len hss_len htake128_len hrk_len hmk_len
        hmk_cap_ne hmk_le hmk_max hmk_ptr_ne
        hpc_err hrun_err hsp_err hsp_align htr_err hvregs_err hinv_err
        (by rw [hx19_err, hx19_5, hx19_4, hx19_3])
        hx20_err
        (by rw [hx21_err, hx21_5, hx21_4, hx21_3])
        hx23_err
        (by rw [hx24_err, hx24_5, hx24_4, hx24_3])
        (by rw [hx25_err, hx25_5])
        (by rw [hx27_err, hx27_5, hx27_4, hx27_3])
        (by rw [hx29_err, hx29_5]))
    · dsimp only [recvCt2ChunkRoAt]; ac_rfl
  · -- `Ok(Done(NoHeaderReceived, EpochSecret))` at `0x5f148` (`+1308`)
    have hcmp_ok' :
        (let hct2 : (ct2Full.take 128).length = 128 := by rw [List.length_take]; omega
         let ss_raw0 := (K.decaps ⟨x.self.uc.dk, hdk_len⟩ ⟨x.self.uc.ct1, hct1_len⟩ ⟨ct2Full.take 128, hct2⟩).toList
         let info0 := sckaKeyInfoPrefix ++ toBEBytes 8 x.self.uc.epoch
         let ss0 := spqrHkdfWith F (List.replicate 32 0#8) ss_raw0 info0 32
         let auth0 := x.self.uc.auth.update F x.self.uc.epoch ss0
         let ct1Full0 := x.self.uc.ct1 ++ ct2Full.take 128
         let tag0 := hmacWith F auth0.macKey (Authenticator.ctLabel ++ toBEBytes 8 x.self.uc.epoch ++ ct1Full0)
         compare_prefix (ct2Full.drop 128) tag0 != 0#8) = false := by
      dsimp only
      rw [← macCtUnchecked_eq_hmacWith]
      simpa only [auth', ss, ss_raw, hepoch] using hcmp_ok
    have hss_eq :
        (let hct2 : (ct2Full.take 128).length = 128 := by rw [List.length_take]; omega
         let ss_raw0 := (K.decaps ⟨x.self.uc.dk, hdk_len⟩ ⟨x.self.uc.ct1, hct1_len⟩ ⟨ct2Full.take 128, hct2⟩).toList
         let info0 := sckaKeyInfoPrefix ++ toBEBytes 8 x.self.uc.epoch
         ss = spqrHkdfWith F (List.replicate 32 0#8) ss_raw0 info0 32) := by
      dsimp only [ss, ss_raw]
      rw [hepoch]
    have hauth'_eq : auth' = x.self.uc.auth.update F x.self.uc.epoch ss := by
      dsimp only [auth']
      rw [hepoch]
    refine SepWPp.rw_pre ?_
      (recv_ct2_chunk_ok_done_dealloc_wpp hA hdealloc_ext x receivingCt2 ct2Full
        cap_ct2 ptr_ct2 ptr_ct2_128 ptr_mac cap_dk ptr_dk cap_ct1' ptr_ct1'
        ptr_ss_raw cap_info ptr_info ptr_ss ss_raw ss auth' g_auth' s0 st_ok R'
        hepoch hadd hdec hge128 hlt_max hct1_len hdk_len hm_le32 hcmp_ok'
        hss_eq hauth'_eq hss_len hss_raw_len htake128_len hrk_len hmk_len
        hmk_cap_ne hmk_le hmk_max hmk_ptr_ne
        hpc_ok hrun_ok hsp_ok hsp_align htr_ok hvregs_ok hinv_ok
        (by rw [hx19_ok, hx19_5, hx19_4, hx19_3])
        hx20_ok
        (by rw [hx21_ok, hx21_5, hx21_4, hx21_3])
        (by rw [hx22_ok, hx22_5, hx22_4, hx22_3])
        hx23_ok
        (by rw [hx24_ok, hx24_5, hx24_4, hx24_3])
        (by rw [hx25_ok, hx25_5])
        (by rw [hx27_ok, hx27_5, hx27_4, hx27_3])
        (by rw [hx29_ok, hx29_5]))
    · dsimp only [recvCt2ChunkRoAt]; ac_rfl

/-- Contract-backed corollary of `recv_ct2_chunk_ok_ext` discharging `AddChunkOkX`,
`PolyDecodedMessageOkX`, and `DeallocOkExt` via `add_chunk_ok_x`, `polyDecoderDecodedMessage_ok`,
and `hA_raw.dealloc`. -/
theorem recv_ct2_chunk_ok_ext_of_decodedMessage {img : Obj.Image} {K : MlKem} {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA_raw : AllocContracts img.base A ext)
    (hA : AllocContractsX img A ext)
    (hallocZeroed : AllocZeroedWithStackOkX img A ext)
    (hdecaps : HookSat ext mlkemDecapsName (mlkemDecapsSpec K))
    (hconcat2 : SliceConcat2OkX img A ext)
    (hconcat3 : SliceConcat3OkX img A ext)
    (hhkdf : HkdfToSliceSpqrOkExt img (spqrHkdfWith F) ext)
    (hupdate : AuthUpdateOkExt img F A ext)
    (hres7 : DoReserve7OkX img A ext)
    (hhmac : HookSat ext libcruxHmacName (libcruxHmacSpec F A)) :
    RecvCt2ChunkOkExt img K F A ext :=
  recv_ct2_chunk_ok_ext himg hA hA_raw.dealloc hallocZeroed (add_chunk_ok_x hA_raw)
    (polyDecodedMessageOkX_of_alloc hA_raw)
    hdecaps hconcat2 hconcat3 hhkdf hupdate hres7 hhmac

end CryptoVerification.SpqrV1.States.RecvCt2Chunk
