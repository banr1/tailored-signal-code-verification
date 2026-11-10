/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlaced
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part1cPlaced
import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part2Placed
import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part2bPlaced
import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part2cPlaced
import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part3Placed
import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part3cPlaced
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp

/-!
# `<EkSentCt1Received>::recv_ct2_chunk` (Block `350`): Top-Level Relocatable Verification

Composes all relocatable `[LibsignalPlacement]` segments of `<EkSentCt1Received>::recv_ct2_chunk`
(Block `350`, `514` instructions) to prove `RecvCt2ChunkPlacedOkExt` and `RecvCt2ChunkPlacedOkX`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

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
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.GF.IsNonZero
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.Drop
open CryptoVerification
open CryptoVerification.LibsignalSpqrV1.PolyDecoder
open CryptoVerification.LibsignalTripleRatchet.Keys
open CryptoVerification.SpqrV1.ChainProofs
open UpdateFacts NextKeyInternalFacts AgreeStateSimp SplitBytes NewFacts

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  spqrHkdfWith Authenticator.update Chunked.SendEk.EkSentCt1Received.recv_ct2_chunk

private theorem lt_128_of_compare_prefix_drop_bne_placed {ct2Full tag : List (BitVec 8)}
    (hcmp : (compare_prefix (ct2Full.drop 128) tag != 0#8) = true) :
    128 < ct2Full.length := by
  by_contra hle
  have hdrop : ct2Full.drop 128 = [] := List.drop_eq_nil_of_le (by omega)
  rw [hdrop, compare_prefix] at hcmp
  change (isNonZero 0#8 != 0#8) = true at hcmp
  revert hcmp; decide

/-! ## Top-Level Composition: `recv_ct2_chunk_placed_ok_x` -/

set_option maxHeartbeats 1600000 in
/-- Top-level relocatable `[LibsignalPlacement]` proof of `<EkSentCt1Received>::recv_ct2_chunk`
    (Block `350`) parameterized by `RecvCt2PlacedAlloc` and explicit callee contracts for
    Block `419` (`add_chunk`), Block `418` (`decoded_message`), and Block `379` (`hkdf_to_slice`). -/
theorem recv_ct2_chunk_placed_ok_of_contracts [LibsignalPlacement] {K : MlKem} {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : RecvCt2PlacedAlloc A ext)
    (hadd_ok : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (blkPl_419).base (withLsCodeLoaded lsmpl (addChunkSpecX A)))
    (hdec_ok : PolyDecodedMessagePlacedOkX A ext)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym (mlkemDecapsSpec K))
    (hhkdf : subroutine_ok ((blkPC_379).rebase (blkPl_379).base (Rust.withPanics ext))
      (blkPl_379).base (withLsCodeRoLoaded lsmpl (hkdfToSliceSpqrSpec (spqrHkdfWith F))))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym' (libcruxHmacSpec F A)) :
    RecvCt2ChunkPlacedOkX K F A ext := by
  unfold RecvCt2ChunkPlacedOkX
  refine subroutine_ok_withLsCodeRoLoaded_rodata3_keep
    (s1 := sckaKeyInfoPrefixSym) (b1 := sckaKeyInfoPrefix)
    (s2 := zeros32Sym) (b2 := List.replicate 32 0#8)
    (s3 := ctLabelSym) (b3 := Authenticator.ctLabel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  dsimp only [recvCt2ChunkPlacedSpec]
  wpp_init x s0
  have hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true := ‹(s0.sp &&& 15#64 == 0#64) = true›
  have hinv : LibsignalCodeRoLoaded lsmpl s0.mem := ‹LibsignalCodeRoLoaded lsmpl s0.mem›
  have hsort_self : PolyDecoderStrictSorted x.self.receiving_ct2 :=
    ‹PolyDecoderStrictSorted x.self.receiving_ct2›
  have hroot_lt : x.self.uc.auth.rootKey.length + 32 < 2 ^ 63 :=
    ‹x.self.uc.auth.rootKey.length + 32 < 2 ^ 63›
  have hx0 : s0.readReg64 .x0 = x.outA := by simp only [wp_norm, arm64_norm, *]
  have hx1 : s0.readReg64 .x1 = x.selfA := by simp only [wp_norm, arm64_norm, *]
  have hx2 : s0.readReg64 .x2 = x.epoch := by simp only [wp_norm, arm64_norm, *]
  have hx3 : s0.readReg64 .x3 = x.chunkA := by simp only [wp_norm, arm64_norm, *]
  refine SepWPp.rw_pre ?_
    (recv_ct2_chunk_part1_placed_wpp hA hadd_ok hdec_ok hdecaps x s0 R hsort_self
      hpc hrun hsp_s0 hinv hx0 hx1 hx2 hx3
      (fun st2 receivingCt2 ct2Full cap_ct2 ptr_ct2 ptr_mac ptr_ct2_128 c3 _c7
        g_auth cap_dk ptr_dk cap_ct1 ptr_ct1
        hepoch hadd _hsort hdec hge128 hlt_max hct1_len htake128_len hdk_len
        hcap_ct1 hle_ct1 hmax_ct1 hptr_ct1
        hpc2 hrun2 hsp2 htr2 hvregs2 hinv2
        hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx29_2 => ?_))
  · dsimp only [recvCt2RoPlacedAt, lsρ]; ac_rfl
  let ss_raw := (K.decaps ⟨x.self.uc.dk, hdk_len⟩ ⟨x.self.uc.ct1, hct1_len⟩ ⟨ct2Full.take 128, htake128_len⟩).toList
  have hss_raw_len : ss_raw.length = 32 :=
    (K.decaps ⟨x.self.uc.dk, hdk_len⟩ ⟨x.self.uc.ct1, hct1_len⟩ ⟨ct2Full.take 128, htake128_len⟩).2
  have hge_not_lt : ¬ ct2Full.length < 128 := by omega
  refine SepWPp.rw_pre ?_
    (recv_ct2_chunk_ss_hkdf_update_placed_wpp hA hhkdf
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
        tokenInitPlacedAt ∗
        reduceTablePlacedAt ∗
        savedRegsAt s0)
      R hss_raw_len htake128_len hroot_lt
      hpc2 hrun2 hsp2 hsp_s0 htr2 hvregs2 hinv2
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
    (recv_ct2_chunk_reserve_ct1_placed_wpp hA x cap_ct1 ptr_ct1 s0 st3
      (recvCt2RoPlacedAt ∗
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
        tokenInitPlacedAt ∗
        reduceTablePlacedAt ∗
        savedRegsAt s0)
      R hct1_len hcap_ct1 hle_ct1 hmax_ct1 hptr_ct1
      hpc3 hrun3 hsp3 hsp_s0 htr3 hvregs3 hinv3
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
    (recv_ct2_chunk_append_hmac_placed_wpp hA hhmac x ct2Full auth' g_auth'
      cap_ct1' ptr_ct1' ptr_ct2_128 0#64 s0 st4
      (((lsρ sckaKeyInfoPrefixSym) ↦ᵣ sckaKeyInfoPrefix) ∗
        ((lsρ zeros32Sym) ↦ᵣ List.replicate 32 0#8) ∗
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
        tokenInitPlacedAt ∗
        reduceTablePlacedAt ∗
        memRegion (s0.sp - 19552#64) 672 ∗
        savedRegsAt s0)
      R hct1_len htake128_len hmk_len hcap_ct1'_ne hge1088 hmax_ct1' hptr_ct1'_ne
      hpc4 hrun4 hsp4 hsp_s0 htr4 hvregs4 hinv4
      hx8_4 (by rw [hx25_4, hx25_3]) (by rw [hx28_4, hx28_3]) (by rw [hx29_4, hx29_3])
      (fun st5 hmk_cap_ne hmk_le hmk_max hmk_ptr_ne
        hpc5 hrun5 hsp5 htr5 hvregs5 hinv5
        hx19_5 hx21_5 hx22_5 hx23_5 hx24_5 hx25_5 _hx26_5 hx27_5 hx29_5 => ?_))
  · dsimp only [recvCt2RoPlacedAt, auth', ss]; ac_rfl
  refine SepWPp.rw_pre ?_
    (recv_ct2_chunk_mac_compare_placed_wpp hA x receivingCt2 ct2Full auth' ptr_mac s0 st5
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
        ((lsρ ctLabelSym) ↦ᵣ Authenticator.ctLabel) ∗
        ((lsρ sckaKeyInfoPrefixSym) ↦ᵣ sckaKeyInfoPrefix) ∗
        ((lsρ zeros32Sym) ↦ᵣ List.replicate 32 0#8) ∗
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
        tokenInitPlacedAt ∗
        reduceTablePlacedAt ∗
        memRegion (s0.sp - 19552#64) 672 ∗
        savedRegsAt s0)
      R hepoch hadd hdec hge_not_lt hlt_max hct1_len hdk_len
      hpc5 hrun5 hsp5 hsp_s0 htr5 hvregs5 hinv5
      (by rw [hx23_5, hx23_4, hx23_3])
      (fun st_err hm_le32 hcmp_err
        hpc_err hrun_err hsp_err htr_err hvregs_err hinv_err
        hx19_err hx20_err hx21_err _hx22_err hx23_err hx24_err hx25_err hx27_err hx29_err => ?_)
      (fun st_ok hm_le32 hcmp_ok
        hpc_ok hrun_ok hsp_ok htr_ok hvregs_ok hinv_ok
        hx19_ok hx20_ok hx21_ok hx22_ok hx23_ok hx24_ok hx25_ok hx27_ok hx29_ok => ?_))
  · ac_rfl
  · -- `Err(Error::MacVerifyFailed)` at `+968`
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
      lt_128_of_compare_prefix_drop_bne_placed hcmp_err
    refine SepWPp.rw_pre ?_
      (recv_ct2_chunk_err_placed_wpp hA x receivingCt2 ct2Full ss_raw ss auth' g_auth'
        cap_ct2 ptr_ct2 cap_dk ptr_dk cap_ct1' ptr_ct1'
        cap_info ptr_info ptr_ss_raw ptr_ss ptr_mac ptr_ct2_128
        s0 st_err R
        hres_err hgt128 hlt_max hss_raw_len hss_len htake128_len hrk_len hmk_len
        hmk_cap_ne hmk_le hmk_max hmk_ptr_ne
        hpc_err hrun_err hsp_err hsp_s0 htr_err hvregs_err hinv_err
        (by rw [hx19_err, hx19_5, hx19_4, hx19_3])
        hx20_err
        (by rw [hx21_err, hx21_5, hx21_4, hx21_3])
        hx23_err
        (by rw [hx24_err, hx24_5, hx24_4, hx24_3])
        (by rw [hx25_err, hx25_5])
        (by rw [hx27_err, hx27_5, hx27_4, hx27_3])
        (by rw [hx29_err, hx29_5]))
    · dsimp only [recvCt2RoPlacedAt]; ac_rfl
  · -- `Ok(Done(NoHeaderReceived, EpochSecret))` at `+1308`
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
      (recv_ct2_chunk_ok_done_dealloc_placed_wpp hA x receivingCt2 ct2Full
        cap_ct2 ptr_ct2 ptr_ct2_128 ptr_mac cap_dk ptr_dk cap_ct1' ptr_ct1'
        ptr_ss_raw cap_info ptr_info ptr_ss ss_raw ss auth' g_auth' s0 st_ok R
        hepoch hadd hdec hge128 hlt_max hct1_len hdk_len hm_le32 hcmp_ok'
        hss_eq hauth'_eq hss_len hss_raw_len htake128_len hrk_len hmk_len
        hmk_cap_ne hmk_le hmk_max hmk_ptr_ne
        hpc_ok hrun_ok hsp_ok hsp_s0 htr_ok hvregs_ok hinv_ok
        (by rw [hx19_ok, hx19_5, hx19_4, hx19_3])
        hx20_ok
        (by rw [hx21_ok, hx21_5, hx21_4, hx21_3])
        (by rw [hx22_ok, hx22_5, hx22_4, hx22_3])
        hx23_ok
        (by rw [hx24_ok, hx24_5, hx24_4, hx24_3])
        (by rw [hx25_ok, hx25_5])
        (by rw [hx27_ok, hx27_5, hx27_4, hx27_3])
        (by rw [hx29_ok, hx29_5]))
    · dsimp only [recvCt2RoPlacedAt]; ac_rfl

/-- Top-level relocatable `[LibsignalPlacement]` contract for `<EkSentCt1Received>::recv_ct2_chunk`
    (Block `350`), discharging `hkdf_to_slice` via `[HkdfPlacedHooks F (Rust.withPanics ext)]`. -/
theorem recv_ct2_chunk_placed_ok_x [LibsignalPlacement] {K : MlKem} {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    [HkdfPlacedHooks F (Rust.withPanics ext)]
    (hA : RecvCt2PlacedAlloc A ext)
    (hadd_ok : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (blkPl_419).base (withLsCodeLoaded lsmpl (addChunkSpecX A)))
    (hdec_ok : PolyDecodedMessagePlacedOkX A ext)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym (mlkemDecapsSpec K))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym' (libcruxHmacSpec F A)) :
    RecvCt2ChunkPlacedOkX K F A ext :=
  recv_ct2_chunk_placed_ok_of_contracts hA hadd_ok hdec_ok hdecaps
    (hkdfToSlice_placed_ok_of_hooks F) hhmac

/-- Top-level relocatable `[LibsignalPlacement]` contract for `<EkSentCt1Received>::recv_ct2_chunk`
    (Block `350`) taking individual external hook and panic hypotheses directly. -/
theorem recv_ct2_chunk_placed_ok_x_of_hooks [LibsignalPlacement] {K : MlKem} {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    [HkdfPlacedHooks F (Rust.withPanics ext)]
    (hadd_ok : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (blkPl_419).base (withLsCodeLoaded lsmpl (addChunkSpecX A)))
    (hdec_ok : PolyDecodedMessagePlacedOkX A ext)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hallocZeroed : HookSat (Rust.withPanics ext) spqrRustAllocZeroedSym (rustAllocZeroedSpec A))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym' (rustDeallocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym framelessMemcpySpec)
    (hRO : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionROSpec)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym (mlkemDecapsSpec K))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym' (libcruxHmacSpec F A))
    (h_handle_error : Rust.withPanics ext spqrHandleErrorSym = some Rust.panicked)
    (h_assert_failed_u64 : Rust.withPanics ext spqrAssertFailedU64Sym = some Rust.panicked)
    (h_slice_index_fail : Rust.withPanics ext spqrSliceIndexFailSym = some Rust.panicked)
    (h_unwrap_failed : Rust.withPanics ext spqrUnwrapFailedSym = some Rust.panicked)
    (h_panic_bounds_check : Rust.withPanics ext spqrPanicBoundsCheckSym = some Rust.panicked)
    (h_panic_add_overflow : Rust.withPanics ext spqrPanicConstAddOverflowSym = some Rust.panicked) :
    RecvCt2ChunkPlacedOkX K F A ext :=
  recv_ct2_chunk_placed_ok_x
    { shim := hshim
      alloc := halloc
      allocZeroed := hallocZeroed
      dealloc := hdealloc
      realloc := hrealloc
      memcpy := hmemcpy
      memcpyRO := hRO
      handleError := h_handle_error
      assertFailedU64 := h_assert_failed_u64
      sliceIndexFail := h_slice_index_fail
      unwrapFailed := h_unwrap_failed
      panicBoundsCheck := h_panic_bounds_check
      panicConstAddOverflow := h_panic_add_overflow }
    hadd_ok hdec_ok hdecaps hhmac

end CryptoVerification.SpqrV1.States.RecvCt2Chunk
