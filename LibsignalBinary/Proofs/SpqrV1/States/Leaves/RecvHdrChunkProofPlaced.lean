/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart1Placed
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart2
public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedSegs
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart2Placed
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart3Placed
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart4Placed
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart5
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart5Placed
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkProof
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp

/-!
# `<NoHeaderReceived>::recv_hdr_chunk` (Block `369`) — Relocatable Epilogues & Top-Level Proof

Relocatable `[LibsignalPlacement]` proofs for the `MacVerifyFailed` epilogue entry
(offsets `800 .. 920`), the `Ok(.done ...)` epilogue (offsets `1060 .. 1196`), and the
top-level Block `369` contract `noHeaderReceived_recv_hdr_chunk_placed_okX`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk

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
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.SpqrV1.Unchunked (spqrLibcruxHmacSym)
open CryptoVerification
open CryptoVerification.LibsignalSpqrV1.PolyDecoder
open CryptoVerification.LibsignalTripleRatchet.Keys
open CryptoVerification.SpqrV1.ChainProofs
open UpdateFacts NextKeyInternalFacts AgreeStateSimp SplitBytes NewFacts

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  out_9_add_8 out_32_add_8 out_48_add_8 out_64_add_8
  zeroExtend32_truncate8_loByte bv391_toNat
attribute [-arm64_norm]
  HkdfToSliceProof.sp_sub_688_eq_hsp
  HkdfToSliceProof.sp_add_neg688_eq_hsp
  HkdfToSliceProof.sp_sub_96_eq_hsp_592
  HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 1. `MacVerifyFailed` Epilogue Entry (offsets `800 .. 920`) -/

set_option maxHeartbeats 1600000 in
theorem recv_hdr_chunk_err_epilogue_placed_wpp [LibsignalPlacement] {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : RecvHdrChunkContractsPlaced A ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F)
    (receivingHdr : PolyDecoder)
    (hdrFull : Bytes)
    (cap_hdrFull ptr_hdrFull ptr_mac ptr_hdr : BitVec 64)
    (v0 v3 v6 v8 v9 v10 v200 : BitVec 64)
    (g_auth0 : AuthenticatorGhost)
    (s0 st : State) (R : SepProp)
    (hres : x.self.recv_hdr_chunk x.epoch x.chunk = .error (.err .macVerifyFailed))
    (hge64 : 64 ≤ hdrFull.length)
    (hmax_hdr : hdrFull.length < 2 ^ 63)
    (_hptr_hdr : ptr_hdr ≠ 0#64)
    (hpc : st.pc = (blkPl_369).base + 800#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 1648#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx19 : st.readReg64 .x19 = x.outA)
    (hx20 : st.readReg64 .x20 = cap_hdrFull)
    (hx22 : st.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64))
    (hx23 : st.readReg64 .x23 = ptr_mac)
    (hx25 : st.readReg64 .x25 = ptr_hdr) :
    SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (vecBufAt A (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
        recvHdrChunkPlacedRoAt ∗
        memRegion x.outA chunkedHeaderReceivedSize ∗
        memRegion x.selfA chunkedNoHeaderReceivedSize ∗
        chunkAt x.chunkA x.chunk ∗
        tokenInitPlacedAt ∗
        reduceTablePlacedAt ∗
        ct2DeallocAt A cap_hdrFull ptr_hdrFull ∗
        (ptr_hdr ↦ₛ hdrFull.take 64) ∗
        A.live ptr_hdr 64 1 ∗
        authenticatorHeapAt A g_auth0 x.self.uc.auth ∗
        ((s0.sp - 1648#64) ↦₆₄ v0) ∗
        ((s0.sp - 1640#64) ↦₆₄ g_auth0.macKey.ptr) ∗
        ((s0.sp - 1632#64) ↦₆₄ ptr_hdrFull) ∗
        ((s0.sp - 1624#64) ↦₆₄ v3) ∗
        ((s0.sp - 1616#64) ↦₆₄ g_auth0.rootKey.cap) ∗
        ((s0.sp - 1608#64) ↦₆₄ g_auth0.rootKey.ptr) ∗
        ((s0.sp - 1600#64) ↦₆₄ v6) ∗
        ((s0.sp - 1592#64) ↦₆₄ g_auth0.macKey.cap) ∗
        ((s0.sp - 1584#64) ↦₆₄ v8) ∗
        ((s0.sp - 1576#64) ↦₆₄ v9) ∗
        ((s0.sp - 1568#64) ↦₆₄ v10) ∗
        polyDecoderAt A (s0.sp - 1560#64) receivingHdr ∗
        memRegion (s0.sp - 1160#64) 24 ∗
        polyDecoderNew1152RawAt A (s0.sp - 1136#64) ∗
        memRegion (s0.sp - 736#64) 80 ∗
        memRegion (s0.sp - 656#64) 456 ∗
        ((s0.sp - 200#64) ↦₆₄ v200) ∗
        memRegion (s0.sp - 192#64) 24 ∗
        memRegion (s0.sp - 168#64) 48 ∗
        memRegion (s0.sp - 120#64) 8 ∗
        memRegion (s0.sp - 112#64) 16 ∗
        savedRegsAt s0 ∗
        memRegion (s0.sp - 18704#64) 672 ∗
        A.pool ∗
        stackAt (s0.sp - 1648#64) extHookStack)
      (recvHdrChunkPlacedPostQ F A x s0 R)
      (recvHdrChunkPlacedPostQp F A x s0 R) := by
  refine SepWPp.fold (ptr_hdr_take64_entails_memRegion ptr_hdr hdrFull hge64) (by sep_focus) ?_
  have h_dealloc := dealloc_placed_ok_at_recvHdr hC
  have h_err844 := @recv_hdr_chunk_err_844_placed_wpp _ F A ext hC x hdrFull cap_hdrFull ptr_hdrFull ptr_mac g_auth0 s0
  have h_err864 := @recv_hdr_chunk_err_864_placed_wpp _ F A ext hC x receivingHdr hdrFull
    cap_hdrFull ptr_hdrFull ptr_mac v0 g_auth0.macKey.ptr ptr_hdrFull v3
    g_auth0.rootKey.cap g_auth0.rootKey.ptr v6 g_auth0.macKey.cap v8 v9 v10 v200 s0
  have hpos64 : 0 < 64 := by decide
  have halign1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hmax64 : 64 + 1 ≤ 2 ^ 63 := by decide
  have hsp_norm : st.readReg64 .sp = s0.sp - 1648#64 := hsp
  by_cases hcap : g_auth0.rootKey.cap = 0#64
  · refine SepWPp.fold
      (authenticatorHeapAt_rootKey_eq0 A g_auth0 x.self.uc.auth hcap)
      (by sep_focus) ?_
    simp only [wp_norm, arm64_norm] at hsp_norm hx19 hx20 hx22 hx23 hx25
    clear hC
    refine of_sepWP_lscro (mid := lsρ spqrRustDeallocSym) hinv ?_
    wp_steps
    have hstack_st : stackAt (s0.sp - 1648#64) extHookStack = stackAt st.sp extHookStack := by
      rw [hsp]
    refine SepWP.fold (Entails.of_eq hstack_st) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv1
    wpp_call_lscro_recvHdr h_dealloc (ptr_hdr, 64, 1) hinv1
    refine SepWPp.pure_left_focus (sf.trace = st.trace) (by sep_focus) fun htr1 => ?_
    have hstack_sf : stackAt st.sp extHookStack = stackAt (s0.sp - 1648#64) extHookStack := by
      rw [hsp]
    refine SepWPp.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
    refine of_sepWP_lscro (mid := (blkPl_369).base + 844#64) hF_sf ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv2
    refine SepWPp.rw_pre (by ac_rfl)
      (h_err844 _
        (vecBufAt A (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
          memRegion x.outA chunkedHeaderReceivedSize ∗
          memRegion x.selfA chunkedNoHeaderReceivedSize ∗
          chunkAt x.chunkA x.chunk ∗
          tokenInitPlacedAt ∗
          reduceTablePlacedAt ∗
          ct2DeallocAt A cap_hdrFull ptr_hdrFull ∗
          ((s0.sp - 1648#64) ↦₆₄ v0) ∗
          ((s0.sp - 1632#64) ↦₆₄ ptr_hdrFull) ∗
          ((s0.sp - 1624#64) ↦₆₄ v3) ∗
          ((s0.sp - 1616#64) ↦₆₄ g_auth0.rootKey.cap) ∗
          ((s0.sp - 1608#64) ↦₆₄ g_auth0.rootKey.ptr) ∗
          ((s0.sp - 1600#64) ↦₆₄ v6) ∗
          ((s0.sp - 1584#64) ↦₆₄ v8) ∗
          ((s0.sp - 1576#64) ↦₆₄ v9) ∗
          ((s0.sp - 1568#64) ↦₆₄ v10) ∗
          polyDecoderAt A (s0.sp - 1560#64) receivingHdr ∗
          memRegion (s0.sp - 1160#64) 24 ∗
          polyDecoderNew1152RawAt A (s0.sp - 1136#64) ∗
          memRegion (s0.sp - 736#64) 80 ∗
          memRegion (s0.sp - 656#64) 456 ∗
          ((s0.sp - 200#64) ↦₆₄ v200) ∗
          memRegion (s0.sp - 192#64) 24 ∗
          memRegion (s0.sp - 168#64) 48 ∗
          memRegion (s0.sp - 120#64) 8 ∗
          memRegion (s0.sp - 112#64) 16 ∗
          savedRegsAt s0 ∗
          memRegion (s0.sp - 18704#64) 672)
        R
        (by wp_norm_goal) (by wp_norm_goal)
        (by simp only [wp_norm, arm64_norm, *])
        hsp_s0
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        hinv2
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (fun st2 hpc2 hrun2 hsp2 htr2 hvregs2 hinv3 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx26_2 =>
          SepWPp.rw_pre (by ac_rfl)
            (h_err864 st2 R hres hge64 hmax_hdr
              hpc2 hrun2 hsp2 hsp_s0 htr2 hvregs2 hinv3
              hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx26_2)))
  · have hcap_beq : (g_auth0.rootKey.cap == 0#64) = false := beq_false_of_ne hcap
    have hcap_pos : 0 < g_auth0.rootKey.cap.toNat :=
      Nat.pos_of_ne_zero (fun h0 => hcap (BitVec.eq_of_toNat_eq h0))
    refine SepWPp.fold
      (authenticatorHeapAt_rootKey_ne0 A g_auth0 x.self.uc.auth hcap)
      (by sep_focus) ?_
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨hmax, hptr_ne⟩
    have hmax1 : g_auth0.rootKey.cap.toNat + 1 ≤ 2 ^ 63 := by omega
    simp only [wp_norm, arm64_norm] at hsp_norm hx19 hx20 hx22 hx23 hx25
    clear hC
    refine of_sepWP_lscro (mid := lsρ spqrRustDeallocSym) hinv ?_
    wp_steps
    have hstack_st : stackAt (s0.sp - 1648#64) extHookStack = stackAt st.sp extHookStack := by
      rw [hsp]
    refine SepWP.fold (Entails.of_eq hstack_st) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv1
    wpp_call_lscro_recvHdr h_dealloc (ptr_hdr, 64, 1) hinv1
    refine SepWPp.pure_left_focus (sf.trace = st.trace) (by sep_focus) fun htr1 => ?_
    have hstack_sf : stackAt st.sp extHookStack = stackAt (s0.sp - 1648#64) extHookStack := by
      rw [hsp]
    refine SepWPp.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
    refine of_sepWP_lscro (mid := lsρ spqrRustDeallocSym) hF_sf ?_
    wp_steps
    have hstack_sf' : stackAt (s0.sp - 1648#64) extHookStack = stackAt sf.sp extHookStack := by
      rw [hsp_sf, hsp]
    refine SepWP.fold (Entails.of_eq hstack_sf') (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv2
    wpp_call_lscro_recvHdr h_dealloc (g_auth0.rootKey.ptr, g_auth0.rootKey.cap.toNat, 1) hinv2
    refine SepWPp.pure_left_focus (sf_1.trace = sf.trace) (by sep_focus) fun htr2 => ?_
    have hstack_sf1 : stackAt sf.sp extHookStack = stackAt (s0.sp - 1648#64) extHookStack := by
      rw [hsp_sf, hsp]
    refine SepWPp.fold (Entails.of_eq hstack_sf1) (by sep_focus) ?_
    refine SepWPp.rw_pre (by ac_rfl)
      (h_err844 sf_1
        (vecBufAt A (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
          memRegion x.outA chunkedHeaderReceivedSize ∗
          memRegion x.selfA chunkedNoHeaderReceivedSize ∗
          chunkAt x.chunkA x.chunk ∗
          tokenInitPlacedAt ∗
          reduceTablePlacedAt ∗
          ct2DeallocAt A cap_hdrFull ptr_hdrFull ∗
          ((s0.sp - 1648#64) ↦₆₄ v0) ∗
          ((s0.sp - 1632#64) ↦₆₄ ptr_hdrFull) ∗
          ((s0.sp - 1624#64) ↦₆₄ v3) ∗
          ((s0.sp - 1616#64) ↦₆₄ g_auth0.rootKey.cap) ∗
          ((s0.sp - 1608#64) ↦₆₄ g_auth0.rootKey.ptr) ∗
          ((s0.sp - 1600#64) ↦₆₄ v6) ∗
          ((s0.sp - 1584#64) ↦₆₄ v8) ∗
          ((s0.sp - 1576#64) ↦₆₄ v9) ∗
          ((s0.sp - 1568#64) ↦₆₄ v10) ∗
          polyDecoderAt A (s0.sp - 1560#64) receivingHdr ∗
          memRegion (s0.sp - 1160#64) 24 ∗
          polyDecoderNew1152RawAt A (s0.sp - 1136#64) ∗
          memRegion (s0.sp - 736#64) 80 ∗
          memRegion (s0.sp - 656#64) 456 ∗
          ((s0.sp - 200#64) ↦₆₄ v200) ∗
          memRegion (s0.sp - 192#64) 24 ∗
          memRegion (s0.sp - 168#64) 48 ∗
          memRegion (s0.sp - 120#64) 8 ∗
          memRegion (s0.sp - 112#64) 16 ∗
          savedRegsAt s0 ∗
          memRegion (s0.sp - 18704#64) 672)
        R
        (by wp_norm_goal) (by wp_norm_goal)
        (by simp only [wp_norm, arm64_norm, *])
        hsp_s0
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        hF_sf_1
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (fun st2 hpc2 hrun2 hsp2 htr3 hvregs2 hinv3 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx26_2 =>
          SepWPp.rw_pre (by ac_rfl)
            (h_err864 st2 R hres hge64 hmax_hdr
              hpc2 hrun2 hsp2 hsp_s0 htr3 hvregs2 hinv3
              hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx26_2)))

/-! ## 2. `Ok(.done ...)` Epilogue (offsets `1060 .. 1196`) -/

set_option maxHeartbeats 1600000 in
theorem recv_hdr_chunk_ok_epilogue_placed_wpp [LibsignalPlacement] {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : RecvHdrChunkContractsPlaced A ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F)
    (g_auth0 : AuthenticatorGhost) (receivingHdr : PolyDecoder) (hdrFull : Bytes)
    (cap_hdrFull ptr_hdrFull ptr_hdr ptr_mac v0 v1 v3 v10 v200 : BitVec 64)
    (s0 st : State) (R : SepProp)
    (hres : x.self.recv_hdr_chunk x.epoch x.chunk =
      .ok (.done { uc := { auth := x.self.uc.auth, hdr := hdrFull.take 64, epoch := x.epoch }
                   receiving_ek := polyDecoderNew1152 }))
    (hptr_hdr : ptr_hdr ≠ 0#64) (hge64 : 64 ≤ hdrFull.length) (hmax_hdr : hdrFull.length < 2 ^ 63)
    (hpc : st.pc = (blkPl_369).base + 1060#64)
    (hrun : st.status = .Running) (hsp : st.sp = s0.sp - 1648#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true) (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx19 : st.readReg64 .x19 = x.outA) (hx20 : st.readReg64 .x20 = cap_hdrFull)
    (hx22 : st.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64))
    (hx23 : st.readReg64 .x23 = ptr_mac) (hx24 : st.readReg64 .x24 = x.epoch)
    (hx25 : st.readReg64 .x25 = ptr_hdr) :
    SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (authenticatorHeapAt A g_auth0 x.self.uc.auth ∗ (ptr_hdr ↦ₛ hdrFull.take 64) ∗
        A.live ptr_hdr 64 1 ∗
        vecBufAt A (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
        recvHdrChunkPlacedRoAt ∗ memRegion x.outA chunkedHeaderReceivedSize ∗
        memRegion x.selfA chunkedNoHeaderReceivedSize ∗ chunkAt x.chunkA x.chunk ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool ∗
        ct2DeallocAt A cap_hdrFull ptr_hdrFull ∗
        ((s0.sp - 1648#64) ↦₆₄ v0) ∗ ((s0.sp - 1640#64) ↦₆₄ v1) ∗
        ((s0.sp - 1632#64) ↦₆₄ ptr_hdrFull) ∗ ((s0.sp - 1624#64) ↦₆₄ v3) ∗
        ((s0.sp - 1616#64) ↦₆₄ g_auth0.rootKey.cap) ∗ ((s0.sp - 1608#64) ↦₆₄ g_auth0.rootKey.ptr) ∗
        ((s0.sp - 1600#64) ↦₆₄ BitVec.ofNat 64 x.self.uc.auth.rootKey.length) ∗
        ((s0.sp - 1592#64) ↦₆₄ g_auth0.macKey.cap) ∗ ((s0.sp - 1584#64) ↦₆₄ g_auth0.macKey.ptr) ∗
        ((s0.sp - 1576#64) ↦₆₄ BitVec.ofNat 64 x.self.uc.auth.macKey.length) ∗
        ((s0.sp - 1568#64) ↦₆₄ v10) ∗ polyDecoderAt A (s0.sp - 1560#64) receivingHdr ∗
        memRegion (s0.sp - 1160#64) 24 ∗ polyDecoderNew1152RawAt A (s0.sp - 1136#64) ∗
        memRegion (s0.sp - 736#64) 80 ∗ memRegion (s0.sp - 656#64) 456 ∗
        ((s0.sp - 200#64) ↦₆₄ v200) ∗ memRegion (s0.sp - 192#64) 24 ∗
        memRegion (s0.sp - 168#64) 48 ∗ memRegion (s0.sp - 120#64) 8 ∗
        memRegion (s0.sp - 112#64) 16 ∗ savedRegsAt s0 ∗
        memRegion (s0.sp - 18704#64) 672 ∗ stackAt (s0.sp - 1648#64) extHookStack)
      (recvHdrChunkPlacedPostQ F A x s0 R)
      (recvHdrChunkPlacedPostQp F A x s0 R) := by
  have horr := sp_sub_1616_orr_9 s0.sp hsp_s0
  have h_memcpy := memcpy_withStack_lscro_ok (polyDecoderNew1152Tail391Split A)
    (by decide) extHookStack (memcpy_withStack_placed_at_recvHdr hC extHookStack)
  have h_tail940 := @recv_hdr_chunk_tail_940_placed_wpp _ F A ext hC
    x receivingHdr cap_hdrFull ptr_hdrFull s0
  have h_tail924 := @recv_hdr_chunk_tail_924_placed_wpp _ F A ext hC
    x receivingHdr hdrFull cap_hdrFull ptr_hdrFull ptr_mac s0
  refine SepWPp.fold (authenticatorHeapAt_rootKey_cap_max A g_auth0 x.self.uc.auth) (by sep_focus) ?_
  refine SepWPp.pure_left_focus _ (by sep_focus) fun hmax_rk => ?_
  have hmax1 : g_auth0.rootKey.cap.toNat + 1 ≤ 2 ^ 63 := by omega
  have hcap_cmn : (g_auth0.rootKey.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_false hmax_rk
  refine SepWPp.fold (memRegion_out_480_split x.outA) (by sep_focus) ?_
  refine SepWPp.fold (memRegion_736_80_split s0.sp) (by sep_focus) ?_
  dsimp only [cells]
  sep_elim_exists
  rename_i ub88 u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 sc0 sc8 sc16 sc24 sc32
  simp only [bv_sub_add_lit, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWPp.fold (Entails.of_eq (poly_1136_split_head9_tail391 A s0.sp)) (by sep_focus) ?_
  refine SepWPp.fold (Entails.of_eq (sp_1608_words5_shift1 s0.sp
    g_auth0.rootKey.ptr (BitVec.ofNat 64 x.self.uc.auth.rootKey.length)
    g_auth0.macKey.cap g_auth0.macKey.ptr (BitVec.ofNat 64 x.self.uc.auth.macKey.length)))
    (by sep_focus) ?_
  refine SepWPp.fold (Entails.of_eq (out_8_words3_shift1 x.outA u8 u16 u24)) (by sep_focus) ?_
  have hsp_norm : st.readReg64 .sp = s0.sp - 1648#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm hx19 hx20 hx22 hx23 hx24 hx25
  clear hC
  refine of_sepWP_lscro (mid := lsρ spqrMemcpySym) hinv ?_
  wp_step; wp_step; wp_step; wp_step
  refine SepWP.fold (Entails.of_eq (sp_1591_words2_unshift1 s0.sp
    g_auth0.macKey.cap g_auth0.macKey.ptr (BitVec.ofNat 64 x.self.uc.auth.macKey.length)))
    (by sep_focus) ?_
  wp_step; wp_step; wp_step; wp_step; wp_step
  refine SepWP.fold (Entails.of_eq (sp_680_words2_shift7 s0.sp
    (overlapWord1 g_auth0.macKey.ptr (BitVec.ofNat 64 x.self.uc.auth.macKey.length)) sc32))
    (by sep_focus) ?_
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step
  refine SepWP.fold (Entails.of_eq (sp_1608_words3_unshift1 s0.sp
    g_auth0.rootKey.ptr (BitVec.ofNat 64 x.self.uc.auth.rootKey.length) g_auth0.macKey.cap))
    (by sep_focus) ?_
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  refine SepWP.fold (Entails.of_eq (out_8_words3_unmerge x.outA
    g_auth0.rootKey.ptr (BitVec.ofNat 64 x.self.uc.auth.rootKey.length) g_auth0.macKey.cap u24))
    (by sep_focus) ?_
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  refine SepWP.fold (collapse_scratch_736 s0.sp
    (overlapWord1 g_auth0.rootKey.ptr (BitVec.ofNat 64 x.self.uc.auth.rootKey.length))
    (overlapWord1 (BitVec.ofNat 64 x.self.uc.auth.rootKey.length) g_auth0.macKey.cap)
    (overlapWord1 g_auth0.macKey.cap g_auth0.macKey.ptr)
    (overlapWord1 g_auth0.macKey.ptr (BitVec.ofNat 64 x.self.uc.auth.macKey.length))
    (BitVec.ofNat 64 x.self.uc.auth.macKey.length)
    (Poly.EncoderFromPb.hiByte sc32)) (by sep_focus) ?_
  have hstack_st : stackAt (s0.sp - 1648#64) extHookStack = stackAt st.sp extHookStack := by rw [hsp]
  refine SepWP.fold (Entails.of_eq hstack_st) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  wpp_call_lscro_recvHdr h_memcpy (x.outA + 89#64, s0.sp - 1127#64) hinv1
  refine SepWPp.pure_left_focus (sf.trace = st.trace ∧ sf.readReg64 (Reg.gpr 0#5) = x.outA + 89#64)
    (by sep_focus) fun ⟨htr1, _⟩ => ?_
  have hstack_sf : stackAt st.sp extHookStack = stackAt (s0.sp - 1648#64) extHookStack := by rw [hsp]
  refine SepWPp.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
  refine SepWPp.fold (fold_out_ok_done A x g_auth0 hdrFull ptr_hdr hptr_hdr hge64 hres) (by sep_focus) ?_
  refine SepWPp.fold (collapse_poly_1136_head9_tail391 s0.sp) (by sep_focus) ?_
  refine SepWPp.fold
    (cells11_entails_memRegion_88 s0.sp v0 v1 ptr_hdrFull v3
      g_auth0.rootKey.cap g_auth0.rootKey.ptr (BitVec.ofNat 64 x.self.uc.auth.rootKey.length)
      g_auth0.macKey.cap g_auth0.macKey.ptr (BitVec.ofNat 64 x.self.uc.auth.macKey.length) v10)
    (by sep_focus) ?_
  refine SepWPp.fold (collapse_tail_1160_1064 s0.sp v200) (by sep_focus) ?_
  have hx22_sf : sf.readReg64 (Reg.gpr 22#5) = st.readReg64 (Reg.gpr 22#5) := ‹_›
  by_cases heq64 : hdrFull.length = 64
  · have hsub0 : hdrFull.length - 64 = 0 := by omega
    have hx22_sf0 : sf.readReg64 (Reg.gpr 22#5) = 0#64 := by
      rw [hx22_sf, hx22, hsub0]
    refine of_sepWP_lscro (mid := (blkPl_369).base + 940#64) hF_sf ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv2
    refine SepWPp.fold (vecBufAt_drop64_eq64_emp A ptr_mac hdrFull heq64) (by sep_focus) ?_
    refine SepWPp.rw_pre (by simp only [emp_sepConj, sepConj_emp]; ac_rfl)
      (h_tail940 _ R (by wp_norm_goal) (by wp_norm_goal)
        (by simp only [wp_norm, arm64_norm, *]) hsp_s0
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) hinv2
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]))
  · have hge65 : 65 ≤ hdrFull.length := by omega
    have hx22_ne : BitVec.ofNat 64 (hdrFull.length - 64) ≠ 0#64 := by
      intro h0
      have h1 := congrArg BitVec.toNat h0
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
      change hdrFull.length - 64 = 0 at h1; omega
    have hx22_beq : (BitVec.ofNat 64 (hdrFull.length - 64) == 0#64) = false :=
      beq_false_of_ne hx22_ne
    have hx22_sf_ne : (sf.readReg64 (Reg.gpr 22#5) == 0#64) = false := by
      rw [hx22_sf, hx22]
      exact hx22_beq
    refine of_sepWP_lscro (mid := (blkPl_369).base + 924#64) hF_sf ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv2
    refine SepWPp.rw_pre (by ac_rfl)
      (h_tail924 _ R hge65 hmax_hdr (by wp_norm_goal) (by wp_norm_goal)
        (by simp only [wp_norm, arm64_norm, *]) hsp_s0
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) hinv2
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]))

/-! ## 3. Top-Level Relocatable Contract (`NoHeaderReceivedRecvHdrChunkPlacedOkX`) -/

private theorem subroutine_ok_withLsCodeRoLoaded_rodata1_keep {α : Type}
    {prog : Program} {entry : BitVec 64} {pl : Arm64.Obj.MultiPlacement}
    {s1 : String} {b1 : List (BitVec 8)} {spec : Spec α}
    (h1 : lsroCheck s1 b1 = true)
    (h : subroutine_ok prog entry
      { spec with
        pre := fun x s => ⌜LibsignalCodeRoLoaded pl s.mem⌝ ∗
          (pl.ρ s1 ↦ᵣ b1) ∗ spec.pre x s
        post := fun x s0 sf =>
          (pl.ρ s1 ↦ᵣ b1) ∗ spec.post x s0 sf }) :
    subroutine_ok prog entry (withLsCodeRoLoaded pl spec) := by
  refine subroutine_ok_withLsCodeRoLoaded_of_withRoSlice h1 ?_
  refine subroutine_ok_mono h ?_ (fun _ _ _ _ hq => hq)
  intro x R s0 hp
  obtain ⟨hfr, hp⟩ := extract_withLsCodeRoLoaded hp
  dsimp only [withRoSlice] at hp ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hfr, hp⟩

set_option maxHeartbeats 800000 in
theorem noHeaderReceived_recv_hdr_chunk_placed_okX_of_contracts [LibsignalPlacement]
    {F : ShaCompress} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : RecvHdrChunkContractsPlaced A ext)
    (hadd_ok : subroutine_ok (lsProg_369 (Rust.withPanics ext))
      (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpecX A)))
    (hdec_ok : PolyDecodedMessagePlacedOkX A ext)
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym (libcruxHmacSpec F A)) :
    NoHeaderReceivedRecvHdrChunkPlacedOkX F A ext := by
  unfold NoHeaderReceivedRecvHdrChunkPlacedOkX
  refine subroutine_ok_withLsCodeRoLoaded_rodata1_keep
    (s1 := hdrLabelSym) (b1 := Authenticator.hdrLabel) (by decide +kernel) ?_
  dsimp only [noHeaderReceivedRecvHdrChunkPlacedSpec, lsProg_369]
  wpp_init x s0
  have hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true := ‹(s0.sp &&& 15#64 == 0#64) = true›
  have hinv0 : LibsignalCodeRoLoaded lsmpl s0.mem := ‹LibsignalCodeRoLoaded lsmpl s0.mem›
  have hsort0 : PolyDecoderStrictSorted x.self.receiving_hdr :=
    ‹PolyDecoderStrictSorted x.self.receiving_hdr›
  have hx0_0 : s0.readReg64 .x0 = x.outA := by simp only [wp_norm, arm64_norm, *]
  have hx1_0 : s0.readReg64 .x1 = x.selfA := by simp only [wp_norm, arm64_norm, *]
  have hx2_0 : s0.readReg64 .x2 = x.epoch := by simp only [wp_norm, arm64_norm, *]
  have hx3_0 : s0.readReg64 .x3 = x.chunkA := by simp only [wp_norm, arm64_norm, *]
  change SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) s0
    (recvHdrChunkPlacedRoAt ∗
      memRegion x.outA chunkedHeaderReceivedSize ∗
      chunkedNoHeaderReceivedAt A x.selfA x.self ∗
      chunkAt x.chunkA x.chunk ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool ∗
      stackAt s0.sp noHeaderReceivedRecvHdrChunkStackX)
    (recvHdrChunkPlacedPostQ F A x s0 R)
    (recvHdrChunkPlacedPostQp F A x s0 R)
  refine recv_hdr_chunk_part1_placed_wpp hC hadd_ok hdec_ok x s0 R
    hsort0 hpc hrun hsp_s0 hinv0 hx0_0 hx1_0 hx2_0 hx3_0
    (fun st2 receivingHdr hdrFull cap_hdrFull ptr_hdrFull ptr_mac ptr_hdr c1 c2 g_auth0
      hepoch hadd _hsort hdec hge64 hlt_max hptr_hdr
      hpc2 hrun2 hsp2 htr2 hvregs2 hinv2
      hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx29_2 => ?_)
  refine SepWPp.frame_call
    (recvHdrChunkPlacedRoAt ∗
      (ptr_hdr ↦ₛ hdrFull.take 64) ∗
      authenticatorHeapAt A g_auth0 x.self.uc.auth ∗
      ((s0.sp - 1640#64) ↦₆₄ c1) ∗
      ((s0.sp - 1632#64) ↦₆₄ c2) ∗
      ((s0.sp - 1584#64) ↦₆₄ g_auth0.macKey.ptr) ∗
      ((s0.sp - 1576#64) ↦₆₄ BitVec.ofNat 64 x.self.uc.auth.macKey.length) ∗
      memRegion (s0.sp - 192#64) 24 ∗
      memRegion (s0.sp - 168#64) 48 ∗
      memRegion (s0.sp - 120#64) 8 ∗
      A.pool ∗
      stackAt (s0.sp - 1648#64) extHookStack)
    (by sep_focus) (by repeat rw [sepConj_assoc])
    (recv_hdr_chunk_hmac_placed_wpp hC hhmac x receivingHdr hdrFull
      cap_hdrFull ptr_hdrFull ptr_mac ptr_hdr c1 c2 g_auth0 s0 st2 _ R
      hepoch hadd hdec hge64
      hpc2 hrun2 hsp2 hsp_s0 htr2 hvregs2 hinv2
      hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx29_2
      (fun st3 hmk_lt32 hpc3 hrun3 hsp3 htr3 hvregs3 hinv3
        hx19_3 hx20_3 hx21_3 hx22_3 _hx23_3 hx24_3 hx25_3 hx26_3 _hx27_3 hx29_3 => ?_))
  refine SepWPp.frame_call
    (vecU8 A (s0.sp - 168#64)
        (x.self.uc.auth.macHdrUnchecked F x.epoch (hdrFull.take 64)) ∗
      memRegion (s0.sp - 144#64) 24 ∗
      vecBufAt A (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
      A.pool ∗
      stackAt (s0.sp - 1648#64) extHookStack)
    (by sep_focus) (by repeat rw [sepConj_assoc])
    (recv_hdr_chunk_mac_compare_placed_wpp hC x receivingHdr hdrFull ptr_mac s0 st3 _ R
      hepoch hadd hdec hge64 hlt_max hmk_lt32
      hpc3 hrun3 hsp3 hsp_s0 htr3 hvregs3 hinv3
      hx21_3 hx22_3 hx26_3 hx29_3
      (fun st4 hle32 hcmp hpc4 hrun4 hsp4 htr4 hvregs4 hinv4
        hx19_4 hx20_4 _ hx22_4 hx23_4 _ hx25_4 _ _ => ?_)
      (fun st4 hle32 hcmp_f hpc4 hrun4 hsp4 htr4 hvregs4 hinv4
        hx19_4 hx20_4 _ hx22_4 hx23_4 hx24_4 hx25_4 _ _ => ?_))
  · have hres_err := recv_hdr_chunk_eq_macVerifyFailed x.self x.epoch x.chunk
      receivingHdr hdrFull hepoch hadd hdec hge64 hmk_lt32 hle32 hcmp
    refine SepWPp.rw_pre (by ac_rfl)
      (recv_hdr_chunk_err_epilogue_placed_wpp hC x receivingHdr hdrFull
        cap_hdrFull ptr_hdrFull ptr_mac ptr_hdr
        0#64 x.epoch (BitVec.ofNat 64 x.self.uc.auth.rootKey.length)
        g_auth0.macKey.ptr (BitVec.ofNat 64 x.self.uc.auth.macKey.length)
        x.self.uc.epoch x.epoch g_auth0 s0 st4 R
        hres_err hge64 hlt_max hptr_hdr
        hpc4 hrun4 hsp4 hsp_s0 htr4 hvregs4 hinv4
        (hx19_4.trans hx19_3) (hx20_4.trans hx20_3) hx22_4 hx23_4 (hx25_4.trans hx25_3))
  · have hres_ok := recv_hdr_chunk_eq_ok_done x.self x.epoch x.chunk
      receivingHdr hdrFull hepoch hadd hdec hge64 hmk_lt32 hle32 hcmp_f
    refine SepWPp.rw_pre (by ac_rfl)
      (recv_hdr_chunk_ok_epilogue_placed_wpp hC x g_auth0 receivingHdr hdrFull
        cap_hdrFull ptr_hdrFull ptr_hdr ptr_mac
        0#64 g_auth0.macKey.ptr x.epoch x.self.uc.epoch x.epoch s0 st4 R
        hres_ok hptr_hdr hge64 hlt_max
        hpc4 hrun4 hsp4 hsp_s0 htr4 hvregs4 hinv4
        (hx19_4.trans hx19_3) (hx20_4.trans hx20_3) hx22_4 hx23_4
        (hx24_4.trans hx24_3) (hx25_4.trans hx25_3))

/-- Relocatable `[LibsignalPlacement]` contract for `<NoHeaderReceived>::recv_hdr_chunk` (Block `369`)
    taking `add_chunk` already transferred onto `lsProg_369 (Rust.withPanics ext)`. -/
theorem noHeaderReceived_recv_hdr_chunk_placed_okX_of_prog [LibsignalPlacement]
    {F : ShaCompress} {A : RustAlloc} {ext : String → Option (State → State)}
    (hadd : subroutine_ok (lsProg_369 (Rust.withPanics ext))
      (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpecX A)))
    (hdec : PolyDecodedMessagePlacedOkX A ext)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym framelessMemcpySpec)
    (hRO : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionROSpec)
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym (libcruxHmacSpec F A))
    (h_handle_error : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (h_assert_failed : (Rust.withPanics ext) assertFailedRecvHdrSym = some Rust.panicked)
    (h_slice_index_fail : (Rust.withPanics ext) sliceIndexFailRecvHdrSym = some Rust.panicked)
    (h_panic_bounds_check : (Rust.withPanics ext) panicBoundsCheckRecvHdrSym = some Rust.panicked) :
    NoHeaderReceivedRecvHdrChunkPlacedOkX F A ext :=
  noHeaderReceived_recv_hdr_chunk_placed_okX_of_contracts
    { shim := hshim
      alloc := halloc
      dealloc := hdealloc
      memcpy := hmemcpy
      memcpyRO := hRO
      handle_error := h_handle_error
      assert_failed := h_assert_failed
      slice_index_fail := h_slice_index_fail
      panic_bounds_check := h_panic_bounds_check }
    hadd hdec hhmac

/-- Top-level relocatable `[LibsignalPlacement]` contract for
    `<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk` (Block `369`). -/
theorem noHeaderReceived_recv_hdr_chunk_placed_okX [LibsignalPlacement]
    {F : ShaCompress} {A : RustAlloc} {ext : String → Option (State → State)}
    (hadd : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (blkPl_419).base (withLsCodeLoaded lsmpl (addChunkSpecX A)))
    (hdec : PolyDecodedMessagePlacedOkX A ext)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym framelessMemcpySpec)
    (hRO : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionROSpec)
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym (libcruxHmacSpec F A))
    (h_handle_error : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (h_assert_failed : (Rust.withPanics ext) assertFailedRecvHdrSym = some Rust.panicked)
    (h_slice_index_fail : (Rust.withPanics ext) sliceIndexFailRecvHdrSym = some Rust.panicked)
    (h_panic_bounds_check : (Rust.withPanics ext) panicBoundsCheckRecvHdrSym = some Rust.panicked) :
    NoHeaderReceivedRecvHdrChunkPlacedOkX F A ext :=
  noHeaderReceived_recv_hdr_chunk_placed_okX_of_prog
    (ls_subroutine_ok_of_block (callerProg := lsProg_369 (Rust.withPanics ext))
      (i := 369) (j := 419) hadd)
    hdec hshim halloc hdealloc hmemcpy hRO hhmac
    h_handle_error h_assert_failed h_slice_index_fail h_panic_bounds_check

end CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
