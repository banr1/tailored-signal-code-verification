/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart1Placed
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart2
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart5
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp

/-!
# `<NoHeaderReceived>::recv_hdr_chunk` (Block `369`) — Relocatable Part 5

Relocatable `[LibsignalPlacement]` proofs on `lsProg_369 (Rust.withPanics ext)` for the shared
epilogue tail (offsets `920 .. 996`) and the `MacVerifyFailed` epilogue body (offsets `844 .. 920`).
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
open CryptoVerification
open CryptoVerification.LibsignalSpqrV1.PolyDecoder
open CryptoVerification.LibsignalTripleRatchet.Keys
open CryptoVerification.SpqrV1.ChainProofs
open UpdateFacts NextKeyInternalFacts AgreeStateSimp SplitBytes NewFacts

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm] out_9_add_8
attribute [-arm64_norm]
  HkdfToSliceProof.sp_sub_688_eq_hsp
  HkdfToSliceProof.sp_add_neg688_eq_hsp
  HkdfToSliceProof.sp_sub_96_eq_hsp_592
  HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 1. Shared Epilogue Tail (offsets `920 .. 996`) -/

set_option maxHeartbeats 1200000 in
theorem recv_hdr_chunk_tail_940_placed_wpp [LibsignalPlacement] {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : RecvHdrChunkContractsPlaced A ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F)
    (receivingHdr : PolyDecoder)
    (cap_hdrFull ptr_hdrFull : BitVec 64)
    (s0 st : State) (R : SepProp)
    (hpc : st.pc = (blkPl_369).base + 940#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 1648#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx20 : st.readReg64 .x20 = cap_hdrFull)
    (hx21 : st.readReg64 .x21 = ptr_hdrFull) :
    SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (recvHdrChunkPlacedRoAt ∗
        noHeaderReceivedRecvChunkResultAt A x.outA
          (x.self.recv_hdr_chunk x.epoch x.chunk) ∗
        memRegion x.selfA chunkedNoHeaderReceivedSize ∗
        chunkAt x.chunkA x.chunk ∗
        tokenInitPlacedAt ∗
        reduceTablePlacedAt ∗
        ct2DeallocAt A cap_hdrFull ptr_hdrFull ∗
        memRegion (s0.sp - 1648#64) 88 ∗
        polyDecoderAt A (s0.sp - 1560#64) receivingHdr ∗
        memRegion (s0.sp - 1160#64) 1064 ∗
        savedRegsAt s0 ∗
        memRegion (s0.sp - 18704#64) 672 ∗
        A.pool ∗
        stackAt (s0.sp - 1648#64) extHookStack)
      (recvHdrChunkPlacedPostQ F A x s0 R)
      (recvHdrChunkPlacedPostQp F A x s0 R) := by
  refine SepWPp.fold (ct2DeallocAt_expose A cap_hdrFull ptr_hdrFull) (by sep_focus) ?_
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hcap_hdrFull_ne, hmax_hdrFull, hptr_hdrFull_ne⟩
  have hpos_hdrFull : 0 < cap_hdrFull.toNat := by
    have : cap_hdrFull.toNat ≠ 0 := fun h0 => hcap_hdrFull_ne (BitVec.eq_of_toNat_eq h0)
    omega
  have halign1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hmax_hdrFull' : cap_hdrFull.toNat + 1 ≤ 2 ^ 63 := by omega
  have hcap_hdrFull_beq : (cap_hdrFull == 0#64) = false := beq_false_of_ne hcap_hdrFull_ne
  have h_dealloc := dealloc_placed_ok_at_recvHdr hC
  have h_drop16 := dropSortedSet16_placed_ok_at_recvHdr hC
  have hsp_norm : st.readReg64 .sp = s0.sp - 1648#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm hx20 hx21
  clear hC
  refine of_sepWP_lscro (mid := lsρ spqrRustDeallocSym) hinv ?_
  wp_steps
  have hstack_st : stackAt (s0.sp - 1648#64) extHookStack = stackAt st.sp extHookStack := by
    rw [hsp]
  refine SepWP.fold (Entails.of_eq hstack_st) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  wpp_call_lscro_recvHdr h_dealloc (ptr_hdrFull, cap_hdrFull.toNat, 1) hinv1
  refine SepWPp.pure_left_focus (sf.trace = st.trace) (by sep_focus) fun htr1 => ?_
  have hstack_sf : stackAt st.sp extHookStack = stackAt (s0.sp - 1648#64) extHookStack := by
    rw [hsp]
  refine SepWPp.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
  refine SepWPp.fold
    (polyDecoderAt_entails_sortedSet16_tail A (s0.sp - 1560#64) receivingHdr)
    (by sep_focus) ?_
  refine SepWPp.pure_left_focus _ (by sep_focus) fun hlen_pts => ?_
  have hstack_drop :
      memRegion (s0.sp - 18704#64) 672 ∗ stackAt (s0.sp - 1648#64) extHookStack ⊢
        memRegion (s0.sp - 18704#64) 12928 ∗ stackAt sf.sp dropStack32 := by
    rw [hsp_sf, hsp, stackAt_extHook_eq_dropStack32_hdr s0.sp]
    exact Entails.refl _
  refine SepWPp.fold hstack_drop (by sep_focus) ?_
  refine of_sepWP_lscro (mid := lsmpl.base 264) hF_sf ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv2
  wpp_call_lscro_recvHdr h_drop16
    (⟨s0.sp - 1560#64, receivingHdr.pts.map SortedSetPt.vec⟩ : DropGlueSortedSetPt16Ghost) hinv2
  refine SepWPp.pure_left_focus (sf_1.trace = sf.trace) (by sep_focus) fun htr2 => ?_
  refine SepWPp.fold (memRegion_400_sp_1560 s0.sp) (by sep_focus) ?_
  have hstack_sf1 : stackAt sf.sp dropStack32 = stackAt (s0.sp - 1648#64) dropStack32 := by
    rw [hsp_sf, hsp]
  refine SepWPp.fold (Entails.of_eq hstack_sf1) (by sep_focus) ?_
  refine SepWPp.fold (stackAt_dropStack32_to_polyDecodedMessage_hdr s0.sp) (by sep_focus) ?_
  have hsp_sf1_norm : sf_1.readReg64 .sp = s0.sp - 1648#64 := hsp_sf_1.trans (hsp_sf.trans hsp)
  simp only [wp_norm, arm64_norm] at hsp_sf1_norm
  unfold savedRegsAt
  apply SepWPp.of_sepWP_ret
  wp_steps
  refine SepWP.fold (Entails.of_eq (show
    ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
      ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
      ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
      ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
      ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
      ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
      ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
      ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) =
    savedRegsAt s0 from rfl)) (by sep_focus) ?_
  refine SepWP.fold (rejoin_stack_hdr_epilogue s0) (by sep_focus) ?_
  unfold recvHdrChunkPlacedPostQ
  dsimp only [noHeaderReceivedRecvHdrChunkPlacedSpec]
  wp_done

set_option maxHeartbeats 1200000 in
theorem recv_hdr_chunk_tail_924_placed_wpp [LibsignalPlacement] {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : RecvHdrChunkContractsPlaced A ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F)
    (receivingHdr : PolyDecoder)
    (hdrFull : Bytes)
    (cap_hdrFull ptr_hdrFull ptr_mac : BitVec 64)
    (s0 st : State) (R : SepProp)
    (hge65 : 65 ≤ hdrFull.length)
    (hmax_hdr : hdrFull.length < 2 ^ 63)
    (hpc : st.pc = (blkPl_369).base + 924#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 1648#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx20 : st.readReg64 .x20 = cap_hdrFull)
    (hx21 : st.readReg64 .x21 = ptr_hdrFull)
    (hx22 : st.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64))
    (hx23 : st.readReg64 .x23 = ptr_mac) :
    SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (vecBufAt A (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
        recvHdrChunkPlacedRoAt ∗
        noHeaderReceivedRecvChunkResultAt A x.outA
          (x.self.recv_hdr_chunk x.epoch x.chunk) ∗
        memRegion x.selfA chunkedNoHeaderReceivedSize ∗
        chunkAt x.chunkA x.chunk ∗
        tokenInitPlacedAt ∗
        reduceTablePlacedAt ∗
        ct2DeallocAt A cap_hdrFull ptr_hdrFull ∗
        memRegion (s0.sp - 1648#64) 88 ∗
        polyDecoderAt A (s0.sp - 1560#64) receivingHdr ∗
        memRegion (s0.sp - 1160#64) 1064 ∗
        savedRegsAt s0 ∗
        memRegion (s0.sp - 18704#64) 672 ∗
        A.pool ∗
        stackAt (s0.sp - 1648#64) extHookStack)
      (recvHdrChunkPlacedPostQ F A x s0 R)
      (recvHdrChunkPlacedPostQp F A x s0 R) := by
  refine SepWPp.fold (vecBufAt_drop64_ne64_dealloc A ptr_mac hdrFull hge65 hmax_hdr) (by sep_focus) ?_
  have h_dealloc := dealloc_placed_ok_at_recvHdr hC
  have h_tail940 := @recv_hdr_chunk_tail_940_placed_wpp _ F A ext hC x receivingHdr cap_hdrFull ptr_hdrFull s0
  have hsub_pos : 0 < hdrFull.length - 64 := by omega
  have halign1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hsub_max : (hdrFull.length - 64) + 1 ≤ 2 ^ 63 := by omega
  have hsub_toNat : (BitVec.ofNat 64 (hdrFull.length - 64)).toNat = hdrFull.length - 64 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsp_norm : st.readReg64 .sp = s0.sp - 1648#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm hx20 hx21 hx22 hx23
  clear hC
  refine of_sepWP_lscro (mid := lsρ spqrRustDeallocSym) hinv ?_
  wp_steps
  have hstack_st : stackAt (s0.sp - 1648#64) extHookStack = stackAt st.sp extHookStack := by
    rw [hsp]
  refine SepWP.fold (Entails.of_eq hstack_st) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  wpp_call_lscro_recvHdr h_dealloc (ptr_mac, hdrFull.length - 64, 1) hinv1
  refine SepWPp.pure_left_focus (sf.trace = st.trace) (by sep_focus) fun htr1 => ?_
  have hstack_sf : stackAt st.sp extHookStack = stackAt (s0.sp - 1648#64) extHookStack := by
    rw [hsp]
  refine SepWPp.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
  refine SepWPp.rw_pre (by ac_rfl)
    (h_tail940 sf R
      (by wp_norm_goal) (by wp_norm_goal)
      (by simp only [wp_norm, arm64_norm, *])
      hsp_s0
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      hF_sf
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]))

theorem recv_hdr_chunk_tail_920_placed_wpp [LibsignalPlacement] {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : RecvHdrChunkContractsPlaced A ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F)
    (receivingHdr : PolyDecoder)
    (hdrFull : Bytes)
    (cap_hdrFull ptr_hdrFull ptr_mac : BitVec 64)
    (s0 st : State) (R : SepProp)
    (hge64 : 64 ≤ hdrFull.length)
    (hmax_hdr : hdrFull.length < 2 ^ 63)
    (hpc : st.pc = (blkPl_369).base + 920#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 1648#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx20 : st.readReg64 .x20 = cap_hdrFull)
    (hx21 : st.readReg64 .x21 = ptr_hdrFull)
    (hx22 : st.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64))
    (hx23 : st.readReg64 .x23 = ptr_mac) :
    SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (vecBufAt A (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
        recvHdrChunkPlacedRoAt ∗
        noHeaderReceivedRecvChunkResultAt A x.outA
          (x.self.recv_hdr_chunk x.epoch x.chunk) ∗
        memRegion x.selfA chunkedNoHeaderReceivedSize ∗
        chunkAt x.chunkA x.chunk ∗
        tokenInitPlacedAt ∗
        reduceTablePlacedAt ∗
        ct2DeallocAt A cap_hdrFull ptr_hdrFull ∗
        memRegion (s0.sp - 1648#64) 88 ∗
        polyDecoderAt A (s0.sp - 1560#64) receivingHdr ∗
        memRegion (s0.sp - 1160#64) 1064 ∗
        savedRegsAt s0 ∗
        memRegion (s0.sp - 18704#64) 672 ∗
        A.pool ∗
        stackAt (s0.sp - 1648#64) extHookStack)
      (recvHdrChunkPlacedPostQ F A x s0 R)
      (recvHdrChunkPlacedPostQp F A x s0 R) := by
  have h_tail940 := @recv_hdr_chunk_tail_940_placed_wpp _ F A ext hC x receivingHdr cap_hdrFull ptr_hdrFull s0
  have h_tail924 := @recv_hdr_chunk_tail_924_placed_wpp _ F A ext hC x receivingHdr hdrFull cap_hdrFull ptr_hdrFull ptr_mac s0
  by_cases heq64 : hdrFull.length = 64
  · have hsub0 : hdrFull.length - 64 = 0 := by omega
    have hx22_0 : st.readReg64 .x22 = 0#64 := by rw [hx22, hsub0]
    simp only [wp_norm, arm64_norm] at hx20 hx21 hx22_0
    refine SepWPp.fold (vecBufAt_drop64_eq64_emp A ptr_mac hdrFull heq64) (by sep_focus) ?_
    clear hC h_tail924
    refine of_sepWP_lscro (mid := (blkPl_369).base + 940#64) hinv ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv1
    refine SepWPp.rw_pre (by simp only [emp_sepConj, sepConj_emp])
      (h_tail940 _ R
        (by wp_norm_goal) (by wp_norm_goal)
        (by simp only [wp_norm, arm64_norm, *])
        hsp_s0
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        hinv1
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]))
  · have hge65 : 65 ≤ hdrFull.length := by omega
    have hx22_ne : BitVec.ofNat 64 (hdrFull.length - 64) ≠ 0#64 := by
      intro h0
      have h1 := congrArg BitVec.toNat h0
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
      change hdrFull.length - 64 = 0 at h1
      omega
    have hx22_beq : (BitVec.ofNat 64 (hdrFull.length - 64) == 0#64) = false :=
      beq_false_of_ne hx22_ne
    simp only [wp_norm, arm64_norm] at hx20 hx21 hx22 hx23
    clear hC h_tail940
    refine of_sepWP_lscro (mid := (blkPl_369).base + 924#64) hinv ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv1
    refine SepWPp.rw_pre (by ac_rfl)
      (h_tail924 _ R hge65 hmax_hdr
        (by wp_norm_goal) (by wp_norm_goal)
        (by simp only [wp_norm, arm64_norm, *])
        hsp_s0
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        hinv1
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]))

/-! ## 2. `MacVerifyFailed` Epilogue Body (offsets `844 .. 920`) -/

theorem recv_hdr_chunk_err_844_placed_wpp [LibsignalPlacement] {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : RecvHdrChunkContractsPlaced A ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F)
    (hdrFull : Bytes)
    (cap_hdrFull ptr_hdrFull ptr_mac : BitVec 64)
    (g_auth0 : AuthenticatorGhost)
    (s0 st : State) (F_frame R : SepProp)
    (hpc : st.pc = (blkPl_369).base + 844#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 1648#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx19 : st.readReg64 .x19 = x.outA)
    (hx20 : st.readReg64 .x20 = cap_hdrFull)
    (hx21 : st.readReg64 .x21 = ptr_hdrFull)
    (hx22 : st.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64))
    (hx23 : st.readReg64 .x23 = ptr_mac)
    (hx26 : st.readReg64 .x26 = s0.sp - 736#64)
    (hcont : ∀ (st2 : State),
      st2.pc = (blkPl_369).base + 864#64 →
      st2.status = .Running →
      st2.sp = s0.sp - 1648#64 →
      st2.trace = s0.trace →
      calleeSavedVRegs st2 = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl st2.mem →
      st2.readReg64 .x19 = x.outA →
      st2.readReg64 .x20 = cap_hdrFull →
      st2.readReg64 .x21 = ptr_hdrFull →
      st2.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64) →
      st2.readReg64 .x23 = ptr_mac →
      st2.readReg64 .x26 = s0.sp - 736#64 →
      SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st2
        (recvHdrChunkPlacedRoAt ∗
          ((s0.sp - 1640#64) ↦₆₄ g_auth0.macKey.ptr) ∗
          ((s0.sp - 1592#64) ↦₆₄ g_auth0.macKey.cap) ∗
          A.pool ∗
          stackAt (s0.sp - 1648#64) extHookStack ∗
          F_frame)
        (recvHdrChunkPlacedPostQ F A x s0 R)
        (recvHdrChunkPlacedPostQp F A x s0 R)) :
    SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (vecU8HeapAt A g_auth0.macKey.cap g_auth0.macKey.ptr x.self.uc.auth.macKey ∗
        recvHdrChunkPlacedRoAt ∗
        ((s0.sp - 1640#64) ↦₆₄ g_auth0.macKey.ptr) ∗
        ((s0.sp - 1592#64) ↦₆₄ g_auth0.macKey.cap) ∗
        A.pool ∗
        stackAt (s0.sp - 1648#64) extHookStack ∗
        F_frame)
      (recvHdrChunkPlacedPostQ F A x s0 R)
      (recvHdrChunkPlacedPostQp F A x s0 R) := by
  have h_dealloc := dealloc_placed_ok_at_recvHdr hC
  have hsp_norm : st.readReg64 .sp = s0.sp - 1648#64 := hsp
  by_cases hcap : g_auth0.macKey.cap = 0#64
  · refine SepWPp.fold
      (vecU8HeapAt_eq0_emp A g_auth0.macKey.cap g_auth0.macKey.ptr x.self.uc.auth.macKey hcap)
      (by sep_focus) ?_
    simp only [wp_norm, arm64_norm] at hsp_norm hx19 hx20 hx21 hx22 hx23 hx26
    clear hC h_dealloc
    refine of_sepWP_lscro (mid := (blkPl_369).base + 864#64) hinv ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv1
    refine SepWPp.rw_pre (by simp only [emp_sepConj, sepConj_emp])
      (hcont _
        (by wp_norm_goal) (by wp_norm_goal)
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        hinv1
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]))
  · have hcap_beq : (g_auth0.macKey.cap == 0#64) = false := beq_false_of_ne hcap
    have hcap_pos : 0 < g_auth0.macKey.cap.toNat :=
      Nat.pos_of_ne_zero (fun h0 => hcap (BitVec.eq_of_toNat_eq h0))
    have halign1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    refine SepWPp.fold
      (vecU8HeapAt_ne0_dealloc A g_auth0.macKey.cap g_auth0.macKey.ptr x.self.uc.auth.macKey hcap)
      (by sep_focus) ?_
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨hmax, hptr_ne⟩
    have hmax1 : g_auth0.macKey.cap.toNat + 1 ≤ 2 ^ 63 := by omega
    simp only [wp_norm, arm64_norm] at hsp_norm hx19 hx20 hx21 hx22 hx23 hx26
    clear hC
    refine of_sepWP_lscro (mid := lsρ spqrRustDeallocSym) hinv ?_
    wp_steps
    have hstack_st : stackAt (s0.sp - 1648#64) extHookStack = stackAt st.sp extHookStack := by
      rw [hsp]
    refine SepWP.fold (Entails.of_eq hstack_st) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv1
    wpp_call_lscro_recvHdr h_dealloc (g_auth0.macKey.ptr, g_auth0.macKey.cap.toNat, 1) hinv1
    refine SepWPp.pure_left_focus (sf.trace = st.trace) (by sep_focus) fun htr1 => ?_
    have hstack_sf : stackAt st.sp extHookStack = stackAt (s0.sp - 1648#64) extHookStack := by
      rw [hsp]
    refine SepWPp.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
    refine SepWPp.rw_pre (by ac_rfl)
      (hcont sf
        (by wp_norm_goal) (by wp_norm_goal)
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        hF_sf
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]))

set_option maxHeartbeats 1200000 in
theorem recv_hdr_chunk_err_864_placed_wpp [LibsignalPlacement] {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : RecvHdrChunkContractsPlaced A ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F)
    (receivingHdr : PolyDecoder)
    (hdrFull : Bytes)
    (cap_hdrFull ptr_hdrFull ptr_mac : BitVec 64)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v200 : BitVec 64)
    (s0 st : State) (R : SepProp)
    (hres : x.self.recv_hdr_chunk x.epoch x.chunk = .error (.err .macVerifyFailed))
    (hge64 : 64 ≤ hdrFull.length)
    (hmax_hdr : hdrFull.length < 2 ^ 63)
    (hpc : st.pc = (blkPl_369).base + 864#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 1648#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx19 : st.readReg64 .x19 = x.outA)
    (hx20 : st.readReg64 .x20 = cap_hdrFull)
    (hx21 : st.readReg64 .x21 = ptr_hdrFull)
    (hx22 : st.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64))
    (hx23 : st.readReg64 .x23 = ptr_mac)
    (hx26 : st.readReg64 .x26 = s0.sp - 736#64) :
    SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (vecBufAt A (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
        recvHdrChunkPlacedRoAt ∗
        memRegion x.outA chunkedHeaderReceivedSize ∗
        memRegion x.selfA chunkedNoHeaderReceivedSize ∗
        chunkAt x.chunkA x.chunk ∗
        tokenInitPlacedAt ∗
        reduceTablePlacedAt ∗
        ct2DeallocAt A cap_hdrFull ptr_hdrFull ∗
        ((s0.sp - 1648#64) ↦₆₄ v0) ∗
        ((s0.sp - 1640#64) ↦₆₄ v1) ∗
        ((s0.sp - 1632#64) ↦₆₄ v2) ∗
        ((s0.sp - 1624#64) ↦₆₄ v3) ∗
        ((s0.sp - 1616#64) ↦₆₄ v4) ∗
        ((s0.sp - 1608#64) ↦₆₄ v5) ∗
        ((s0.sp - 1600#64) ↦₆₄ v6) ∗
        ((s0.sp - 1592#64) ↦₆₄ v7) ∗
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
  have h_drop := dropSortedSet16_placed_ok_at_recvHdr hC
  have h_tail920 := @recv_hdr_chunk_tail_920_placed_wpp _ F A ext hC x receivingHdr hdrFull cap_hdrFull ptr_hdrFull ptr_mac s0
  refine SepWPp.fold (cells11_entails_memRegion_88 s0.sp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10) (by sep_focus) ?_
  refine SepWPp.fold (polyDecoderNew1152RawAt_entails_polyDecoderAt A (s0.sp - 1136#64)) (by sep_focus) ?_
  refine SepWPp.fold (polyDecoderAt_entails_sortedSet16_tail A (s0.sp - 1136#64) polyDecoderNew1152) (by sep_focus) ?_
  refine SepWPp.pure_left_focus _ (by sep_focus) fun hlen16 => ?_
  refine SepWPp.fold (sp_736_80_expose s0.sp) (by sep_focus) ?_
  refine SepWPp.fold (out_480_err_expose x.outA) (by sep_focus) ?_
  sep_elim_exists
  rename_i w736 w728 w720 w704 w696 w688 u0 ub8 u9 u17 u25
  have hsp_norm : st.readReg64 .sp = s0.sp - 1648#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm hx19 hx20 hx21 hx22 hx23 hx26
  clear hC
  refine of_sepWP_lscro (mid := lsmpl.base 264) hinv ?_
  wp_step; wp_step
  refine SepWP.fold (sp_696_realign s0.sp w696 w688) (by sep_focus) ?_
  wp_step; wp_step; wp_step; wp_step; wp_step
  refine SepWP.fold (sp_728_realign s0.sp w696 w720) (by sep_focus) ?_
  wp_step; wp_step
  refine SepWP.fold (sp_728_721_realign s0.sp w696 (FromPb.overlapWord7 w696 w688)) (by sep_focus) ?_
  wp_step; wp_step; wp_step
  refine SepWP.fold (out_17_25_realign x.outA (FromPb.overlapLow7 w696 (FromPb.overlapWord7 w696 w688)) u25) (by sep_focus) ?_
  wp_step; wp_step
  refine SepWP.fold
    (sp_736_80_collapse s0.sp w704
      (FromPb.overlapLow7 w696 (FromPb.overlapWord7 w696 w688))
      (FromPb.overlapWord7 w696 w688)
      w704 w696 (FromPb.overlapWord7 w696 w688))
    (by sep_focus) ?_
  refine SepWP.fold
    (out_480_err_collapse A x.outA w704
      (FromPb.overlapLow7 w696 (FromPb.overlapWord7 w696 w688))
      (FromPb.overlapWord7 w696 w688)
      (x.self.recv_hdr_chunk x.epoch x.chunk) hres)
    (by sep_focus) ?_
  have hstack_drop :
      memRegion (s0.sp - 18704#64) 672 ∗ stackAt (s0.sp - 1648#64) extHookStack ⊢
        memRegion (s0.sp - 18704#64) 12928 ∗ stackAt st.sp dropStack32 := by
    rw [hsp, stackAt_extHook_eq_dropStack32_hdr s0.sp]
    exact Entails.refl _
  refine SepWP.fold hstack_drop (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  wpp_call_lscro_recvHdr h_drop
    (⟨s0.sp - 1136#64, polyDecoderNew1152.pts.map SortedSetPt.vec⟩ : DropGlueSortedSetPt16Ghost) hinv1
  refine SepWPp.pure_left_focus (sf.trace = st.trace) (by sep_focus) fun htr1 => ?_
  have hstack_back :
      memRegion (s0.sp - 18704#64) 12928 ∗ stackAt st.sp dropStack32 =
        memRegion (s0.sp - 18704#64) 672 ∗ stackAt (s0.sp - 1648#64) extHookStack := by
    rw [hsp, ← stackAt_extHook_eq_dropStack32_hdr s0.sp]
  refine SepWPp.fold (Entails.of_eq hstack_back) (by sep_focus) ?_
  refine SepWPp.fold (rejoin_sp_1160_1064 s0.sp v200) (by sep_focus) ?_
  refine SepWPp.rw_pre (by ac_rfl)
    (h_tail920 sf R hge64 hmax_hdr
      (by wp_norm_goal) (by wp_norm_goal)
      (by simp only [wp_norm, arm64_norm, *])
      hsp_s0
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      hF_sf
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]))

end CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
