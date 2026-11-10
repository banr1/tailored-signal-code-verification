/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlaced
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.LeavesCodeSymA
import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part1Placed
import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part1bPlaced
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp

/-!
# `<EkSentCt1Received>::recv_ct2_chunk` (Block `350`): Relocatable Entry through Decapsulation

Composes prologue epoch check, `PolyDecoder::add_chunk` (Block `419`), `decoded_message` (Block `418`),
the `None` return path, and `Some(ct2Full)` allocation + decapsulation (`+0 .. +480`).
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
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  HkdfToSliceProof.sp_sub_688_eq_hsp
  HkdfToSliceProof.sp_add_neg688_eq_hsp
  HkdfToSliceProof.sp_sub_96_eq_hsp_592
  HkdfToSliceProof.sp_add_neg96_eq_hsp_592

set_option maxHeartbeats 1600000 in
theorem recv_ct2_chunk_part1_placed_wpp [LibsignalPlacement] {K : MlKem} {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : RecvCt2PlacedAlloc A ext)
    (hadd_ok : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (blkPl_419).base (withLsCodeLoaded lsmpl (addChunkSpecX A)))
    (hdec_ok : PolyDecodedMessagePlacedOkX A ext)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym (mlkemDecapsSpec K))
    (x : RecvCt2ChunkGhost F)
    (s0 : State) (R : SepProp)
    (hsort_self : PolyDecoderStrictSorted x.self.receiving_ct2)
    (hpc : s0.pc = (blkPl_350).base)
    (hrun : s0.status = .Running)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (hinv : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = x.outA)
    (hx1 : s0.readReg64 .x1 = x.selfA)
    (hx2 : s0.readReg64 .x2 = x.epoch)
    (hx3 : s0.readReg64 .x3 = x.chunkA)
    (hcont : ∀ (st2 : State) (receivingCt2 : PolyDecoder) (ct2Full : Bytes)
        (cap_ct2 ptr_ct2 ptr_mac ptr_ct2_128 : BitVec 64)
        (c3 _c7 : BitVec 64)
        (g_auth : AuthenticatorGhost) (cap_dk ptr_dk cap_ct1 ptr_ct1 : BitVec 64)
        (_hepoch : x.epoch = x.self.uc.epoch)
        (_hadd : PolyDecoder.addChunk x.self.receiving_ct2 x.chunk = .ok receivingCt2)
        (_hsort : PolyDecoderStrictSorted receivingCt2)
        (_hdec : receivingCt2.decodedMessage = .ok (some ct2Full))
        (_hge128 : 128 ≤ ct2Full.length)
        (_hlt_max : ct2Full.length < 2 ^ 63)
        (hct1_len : x.self.uc.ct1.length = 960)
        (htake128_len : (ct2Full.take 128).length = 128)
        (hdk_len : x.self.uc.dk.length = 2400),
      cap_ct1 ≠ 0#64 →
      960 ≤ cap_ct1.toNat →
      cap_ct1.toNat < 2 ^ 63 →
      ptr_ct1 ≠ 0#64 →
      st2.pc = (blkPl_350).base + 480#64 →
      st2.status = .Running →
      st2.sp = s0.sp - 2496#64 →
      st2.trace = s0.trace →
      calleeSavedVRegs st2 = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl st2.mem →
      st2.readReg64 .x19 = x.outA →
      st2.readReg64 .x20 = s0.sp - 288#64 →
      st2.readReg64 .x21 = ptr_ct2 →
      st2.readReg64 .x22 = x.epoch →
      st2.readReg64 .x23 = BitVec.ofNat 64 (ct2Full.length - 128) →
      st2.readReg64 .x24 = ptr_dk →
      st2.readReg64 .x25 = ptr_ct2_128 →
      st2.readReg64 .x26 = BitVec.ofNat 64 ct2Full.length →
      st2.readReg64 .x27 = cap_ct2 →
      st2.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp (lsProg_350 (Rust.withPanics ext)) (s0.readReg64 .x30) st2
        (recvCt2RoPlacedAt ∗
          memRegion x.outA chunkedEkSentCt1ReceivedSize ∗
          memRegion x.selfA chunkedEkSentCt1ReceivedSize ∗
          ct2DeallocAt A cap_ct2 ptr_ct2 ∗
          ct2DeallocAt A cap_dk ptr_dk ∗
          (ptr_ct2_128 ↦ₛ ct2Full.take 128) ∗
          A.live ptr_ct2_128 128 1 ∗
          vecBufAt A (BitVec.ofNat 64 (ct2Full.length - 128)) ptr_mac (ct2Full.drop 128) ∗
          authenticatorPinAt A g_auth (s0.sp - 1328#64) x.self.uc.auth ∗
          vecU8At A (s0.sp - 1280#64) cap_ct1 ptr_ct1 x.self.uc.ct1 ∗
          ((s0.sp - 152#64) ↦ₛ (K.decaps ⟨x.self.uc.dk, hdk_len⟩ ⟨x.self.uc.ct1, hct1_len⟩ ⟨ct2Full.take 128, htake128_len⟩).toList) ∗
          ((s0.sp - 288#64) ↦ₛ ct2Full.take 128) ∗
          memRegion (s0.sp - 1248#64) 960 ∗
          memRegion (s0.sp - 2000#64) 144 ∗
          memRegion (s0.sp - 1344#64) 16 ∗
          unusedFrameAt (s0.sp - 2496#64) ∗
          ((s0.sp - 2496#64) ↦₆₄ 0#64) ∗
          ((s0.sp - 2488#64) ↦₆₄ ptr_dk) ∗
          ((s0.sp - 2480#64) ↦₆₄ BitVec.ofNat 64 ct2Full.length) ∗
          ((s0.sp - 2472#64) ↦₆₄ c3) ∗
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
          A.pool ∗
          memRegion (s0.sp - 19552#64) 672 ∗
          stackAt (s0.sp - 2496#64) extHookStack ∗
          savedRegsAt s0)
        (recvCt2PlacedPostQ K F A x s0 R)
        (recvCt2PlacedPostQp K F A x s0 R)) :
    SepWPp (lsProg_350 (Rust.withPanics ext)) (s0.readReg64 .x30) s0
      (recvCt2RoPlacedAt ∗
        memRegion x.outA chunkedEkSentCt1ReceivedSize ∗
        ekSentCt1ReceivedAt A x.selfA x.self ∗
        chunkAt x.chunkA x.chunk ∗
        tokenInitPlacedAt ∗
        reduceTablePlacedAt ∗
        A.pool ∗
        stackAt s0.sp recvCt2ChunkStackX)
      (recvCt2PlacedPostQ K F A x s0 R)
      (recvCt2PlacedPostQp K F A x s0 R) := by
  have hmc_raw := hA.memcpy_region_at_block
    (prog := lsProg_350 (Rust.withPanics ext)) polyDecodedMessageStackX
  have h_mc_dec := (polyDecoderSplit A x.self.receiving_ct2).memcpy_withStack_lscro_ok
    (pl := lsmpl) (by decide) polyDecodedMessageStackX hmc_raw
  have h_add := addChunk_placed_lscro hadd_ok
  have h_dec := polyDecodedMessage_placed_lscro hdec_ok
  have h_pan_epoch := hA.panic_assert_failed_u64
  have h_pan_slice := hA.panic_slice_index_fail
  have h_none := @recv_ct2_chunk_none_placed_wpp _ K F A ext hA x
  have h_alloc_mac := @recv_ct2_chunk_alloc_mac_ct2_placed_wpp _ K F A ext hA x
  have h_to_decaps := @recv_ct2_chunk_to_decaps_placed_wpp _ K F A ext hA hdecaps x
  simp only [wp_norm, arm64_norm] at hx0 hx1 hx2 hx3
  clear hmc_raw hadd_ok hdec_ok hA hdecaps
  simp only [lsProg_350] at h_mc_dec h_add h_dec h_pan_epoch h_pan_slice h_none h_alloc_mac h_to_decaps hcont ⊢
  unfold ekSentCt1ReceivedAt
  refine SepWPp.rw_pre (by rw [stackAt_recvCt2Chunk_split s0.sp]) ?_
  unfold activeFrameRegionsAt
  refine SepWPp.rw_pre (by rw [cells12_sp_96_expand s0.sp, cells9_sp_2496_expand s0.sp]) ?_
  sep_elim_exists
  rename_i c0 c1 c2 c3 c4 c5 c6 c7 c8
  refine SepWPp.fold (ekSentCt1ReceivedUcAt_expose_entails A x.selfA x.self.uc) (by sep_focus) ?_
  sep_elim_exists
  rename_i g_auth0 cap_dk0 ptr_dk0 cap_ct10 ptr_ct10
  by_cases hepoch : x.epoch = x.self.uc.epoch
  · have hepoch_bne : (x.epoch != x.self.uc.epoch) = false := by
      simp [hepoch]
    refine SepWPp.of_sepWP_lscro (mid := lsρ spqrMemcpySym) hinv ?_
    wp_steps
    refine SepWP.fold
      (ekSentCt1ReceivedUcAt_fold_entails A x.selfA x.self.uc g_auth0 cap_dk0 ptr_dk0 cap_ct10 ptr_ct10)
      (by sep_focus) ?_
    refine SepWP.fold (savedRegsAt_of_cells12 s0) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv1
    wpp_call_lscro_recvCt2 h_mc_dec
      (s0.sp - 2424#64, x.selfA + 104#64) hinv1
    refine SepWPp.pure_left_focus _ (by sep_focus) fun hpost_mc => ?_
    rcases hpost_mc with ⟨htr1, _⟩
    refine SepWPp.fold
      (polyDecoderAt_pts_length A (s0.sp - 2424#64) x.self.receiving_ct2)
      (by sep_focus) ?_
    refine SepWPp.pure_left_focus _ (by sep_focus) fun hpts_len => ?_
    have hadd_eq : PolyDecoder.addChunk x.self.receiving_ct2 x.chunk =
        .ok (addChunkTotal x.self.receiving_ct2 x.chunk) :=
      addChunk_eq_ok x.self.receiving_ct2 x.chunk hpts_len
    refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 419) hF_sf ?_
    wp_steps
    have hstack_add :
        stackAt (s0.sp - 2496#64) polyDecodedMessageStackX =
          memRegion ((s0.sp - 2496#64) - 17056#64) 576 ∗ stackAt sf.sp addChunkStackX := by
      rw [hsp_sf, stackAt_polyDecodedMessage_eq_addChunk (s0.sp - 2496#64)]
    refine SepWP.fold (Entails.of_eq hstack_add) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv2
    wpp_call_lscro_recvCt2 h_add
      ⟨s0.sp - 2424#64, x.chunkA, x.self.receiving_ct2, x.chunk⟩ hinv2
    refine SepWPp.pure_left_focus _ (by sep_focus) fun hpost_add => ?_
    rcases hpost_add with ⟨htr2, hsort_add⟩
    have hstack_add_back :
        memRegion ((s0.sp - 2496#64) - 17056#64) 576 ∗ stackAt sf.sp addChunkStackX ⊢
          stackAt sf_1.sp polyDecodedMessageStackX := by
      rw [hsp_sf_1, hsp_sf, ← stackAt_polyDecodedMessage_eq_addChunk (s0.sp - 2496#64)]
      exact Entails.refl _
    refine SepWPp.fold hstack_add_back (by sep_focus) ?_
    refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 418) hF_sf_1 ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv3
    wpp_call_lscro_recvCt2 h_dec
      ⟨s0.sp - 2024#64, s0.sp - 2424#64,
       addChunkTotal x.self.receiving_ct2 x.chunk⟩ hinv3
    apply SepWPp.exists_elim
    intro optMsg
    refine SepWPp.pure_left_focus _ (by sep_focus) fun hpost_dec => ?_
    rcases hpost_dec with ⟨hdec_eq, htr3⟩
    have hsp_sf2 : sf_2.sp = s0.sp - 2496#64 := by rw [hsp_sf_2, hsp_sf_1, hsp_sf]
    have htr_sf2 : sf_2.trace = s0.trace := by rw [htr3, htr2, htr1]
    have hstack_sf1 :
        stackAt sf_1.sp polyDecodedMessageStackX ⊢
          stackAt (s0.sp - 2496#64) polyDecodedMessageStackX := by
      rw [hsp_sf_1, hsp_sf]
      exact Entails.refl _
    refine SepWPp.fold hstack_sf1 (by sep_focus) ?_
    change SepWPp ((blkPC_350).rebase (blkPl_350).base (Rust.withPanics ext))
      (s0.readReg64 .x30) sf_2 _
      (recvCt2PlacedPostQ K F A x s0 R)
      (recvCt2PlacedPostQp K F A x s0 R)
    cases optMsg with
    | none =>
      refine SepWPp.rw_pre (by rw [optKeyBytesAt_none_sp_2024 A s0.sp]) ?_
      refine SepWPp.of_sepWP_lscro (mid := (blkPl_350).base + 152#64) hF_sf_2 ?_
      wp_steps
      refine SepWP.fold (cells9_sp_2496_fold s0.sp _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold
        (fold_none_addrs_sp A s0.sp (addChunkTotal x.self.receiving_ct2 x.chunk))
        (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv_none
      refine SepWPp.rw_pre (by unfold recvCt2RoPlacedAt; ac_rfl)
        (h_none (addChunkTotal x.self.receiving_ct2 x.chunk)
          s0 _ R hepoch hadd_eq hsort_add hdec_eq
          (by wp_norm_goal) (by wp_norm_goal)
          (by simp only [wp_norm, arm64_norm, hsp_sf2])
          hsp_s0
          (by simp only [wp_norm, arm64_norm, htr_sf2])
          (by simp only [wp_norm, arm64_norm, *])
          hinv_none
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *]))
    | some ct2Full =>
      refine SepWPp.fold (optKeyBytesAt_some_sp_2024 A s0.sp ct2Full) (by sep_focus) ?_
      sep_elim_exists
      rename_i cap_ct2 ptr_ct2
      refine SepWPp.pure_left_focus _ (by sep_focus) ?_
      rintro ⟨hle_cap, hmax_cap, hptr_ct2⟩
      have hlt_max : ct2Full.length < 2 ^ 63 := by omega
      have hcap_cmn : (cap_ct2 + 1#64 == 0#64) = false := cap_add_one_beq_zero_false hmax_cap
      by_cases hge128 : 128 ≤ ct2Full.length
      · have hult128 : (BitVec.ofNat 64 ct2Full.length).ult 128#64 = false :=
          ofNat_ult_128_of_ge hge128 hlt_max
        have hsub128 : BitVec.ofNat 64 ct2Full.length - 128#64 = BitVec.ofNat 64 (ct2Full.length - 128) :=
          ofNat_sub_128_eq hge128 hlt_max
        have hmsb128 : (BitVec.ofNat 64 (ct2Full.length - 128)).getLsbD 63 = false :=
          ofNat_getLsbD_63_false (by omega)
        have hmsb128' : (BitVec.ofNat 64 (ct2Full.length - 128))[63] = false :=
          ofNat_getElem_63_false (by omega)
        have hpl128 : ConditionHolds .PL (subsPState64 (BitVec.ofNat 64 ct2Full.length) 128#64) = true := by
          simp only [ConditionHolds, subsPState64, wp_norm, arm64_norm, addWithCarry64_sub_128_n, hsub128, hmsb128, hmsb128']
        refine SepWPp.fold (vecU8HeapAt_split_128 A cap_ct2 ptr_ct2 ct2Full hge128) (by sep_focus) ?_
        refine SepWPp.pure_left_focus _ (by sep_focus) ?_
        rintro ⟨_, _, _, hcap_ct2⟩
        refine SepWPp.of_sepWP_lscro (mid := (blkPl_350).base + 224#64) hF_sf_2 ?_
        wp_steps
        refine SepWP.fold (Entails.of_eq (stackAt_polyDecodedMessage_eq_extHook (s0.sp - 2496#64))) (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hinv_some
        refine SepWPp.frame_call
          (((s0.sp - 2448#64) ↦₆₄ c6) ∗
            ((s0.sp - 2016#64) ↦₆₄ ptr_ct2) ∗
            ((ptr_ct2 + 128#64) ↦ₛ ct2Full.drop 128) ∗
            A.pool ∗
            stackAt (s0.sp - 2496#64) extHookStack)
          (by sep_focus)
          (by repeat rw [sepConj_assoc])
          (h_alloc_mac ct2Full cap_ct2 ptr_ct2 c6 s0 _ _ R hge128 hlt_max
            (by wp_norm_goal) (by wp_norm_goal)
            (by simp only [wp_norm, arm64_norm, hsp_sf2])
            hsp_s0
            (by simp only [wp_norm, arm64_norm, htr_sf2])
            (by simp only [wp_norm, arm64_norm, *])
            hinv_some
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, hsub128, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (fun st' ptr_mac ptr_ct2_128 _hptr128 hpc' hrun' hsp' htr' hvregs' hinv'
              hx0' hx19' hx20' hx21' hx22' hx23' hx26' hx27' hx29' => ?_))
        refine SepWPp.fold
          (memRegion_24_of_sp_2024 s0.sp cap_ct2 ptr_ct2 (BitVec.ofNat 64 ct2Full.length))
          (by sep_focus) ?_
        refine SepWPp.frame_call
          (ekSentCt1ReceivedUcAt A x.selfA x.self.uc ∗
            memRegion (x.selfA + 104#64) 400 ∗
            (ptr_ct2 ↦ₛ ct2Full.take 128) ∗
            ((ptr_ct2 + 128#64) ↦ₛ ct2Full.drop 128) ∗
            memRegion (ptr_ct2 + BitVec.ofNat 64 ct2Full.length) (cap_ct2.toNat - ct2Full.length) ∗
            A.live ptr_ct2 cap_ct2.toNat 1 ∗
            memRegion ptr_ct2_128 128 ∗
            A.live ptr_ct2_128 128 1 ∗
            vecBufAt A (BitVec.ofNat 64 (ct2Full.length - 128)) ptr_mac (ct2Full.drop 128) ∗
            ((s0.sp - 2496#64) ↦₆₄ 0#64) ∗
            ((s0.sp - 2488#64) ↦₆₄ c1) ∗
            ((s0.sp - 2480#64) ↦₆₄ c2) ∗
            ((s0.sp - 2472#64) ↦₆₄ c3) ∗
            ((s0.sp - 2464#64) ↦₆₄ c4) ∗
            ((s0.sp - 2456#64) ↦₆₄ c5) ∗
            ((s0.sp - 2448#64) ↦₆₄ ptr_mac) ∗
            ((s0.sp - 2440#64) ↦₆₄ c7) ∗
            ((s0.sp - 2432#64) ↦₆₄ x.self.uc.epoch) ∗
            someBranchFrameAt (s0.sp - 2496#64) ∗
            A.pool ∗
            stackAt (s0.sp - 2496#64) extHookStack)
          (by sep_focus)
          (by repeat rw [sepConj_assoc])
          (h_to_decaps (addChunkTotal x.self.receiving_ct2 x.chunk)
            ct2Full cap_ct2 ptr_ct2 ptr_mac ptr_ct2_128 0#64 c1 c2 c3 c4 c5 c7 x.self.uc.epoch s0 st' R _
            hepoch hadd_eq hdec_eq hge128 hlt_max hle_cap hmax_cap hptr_ct2 hcap_ct2
            hpc' hrun' hsp' hsp_s0 htr' hvregs' hinv'
            hx0' hx19' hx20' hx21' hx22' hx23' hx26' hx27' hx29'
            (fun st2 g_auth cap_dk ptr_dk cap_ct1 ptr_ct1 hct1_len htake128_len hdk_len
              hcap_ct1 hle_ct1 hmax_ct1 hptr_ct1
              hpc2 hrun2 hsp2 htr2 hvregs2 hinv2
              hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx29_2 => ?_))
        refine SepWPp.rw_pre (by unfold recvCt2RoPlacedAt; rw [← hepoch]; ac_rfl)
          (hcont st2 (addChunkTotal x.self.receiving_ct2 x.chunk) ct2Full
            cap_ct2 ptr_ct2 ptr_mac ptr_ct2_128 c3 c7 g_auth cap_dk ptr_dk cap_ct1 ptr_ct1
            hepoch hadd_eq hsort_add hdec_eq hge128 hlt_max hct1_len htake128_len hdk_len
            hcap_ct1 hle_ct1 hmax_ct1 hptr_ct1
            hpc2 hrun2 hsp2 htr2 hvregs2 hinv2
            hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx29_2)
      · have hlt128 : ct2Full.length < 128 := by omega
        have hult128 : (BitVec.ofNat 64 ct2Full.length).ult 128#64 = true :=
          ofNat_ult_128_of_lt hlt128
        have hpan_lt := recv_ct2_chunk_isPanic_of_lt_128 (K := K) x.self x.epoch x.chunk
          (addChunkTotal x.self.receiving_ct2 x.chunk) ct2Full hepoch hadd_eq hdec_eq hlt128
        apply SepWPp.of_sepWP (mid := lsρ spqrSliceIndexFailSym)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *]) fun hm => ?_
        exact allowPanic_isPanic_recvCt2 hpan_lt
          (by simp only [wp_norm, arm64_norm, htr_sf2, List.prefix_refl]) hm
  · have hepoch_bne : (x.epoch != x.self.uc.epoch) = true := bne_iff_ne.mpr hepoch
    have hpan_ep := recv_ct2_chunk_isPanic_of_epoch_ne (K := K) x.self x.epoch x.chunk hepoch
    apply SepWPp.of_sepWP (mid := lsρ spqrAssertFailedU64Sym)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) fun hm => ?_
    exact allowPanic_isPanic_recvCt2 hpan_ep
      (by simp only [wp_norm, arm64_norm, List.prefix_refl]) hm

end CryptoVerification.SpqrV1.States.RecvCt2Chunk
