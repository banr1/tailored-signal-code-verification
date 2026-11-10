/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart1PlacedBudget
meta import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart1PlacedBudget -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart2
public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedSegs
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart2PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart3PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart4PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart5
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart5PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkProof
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp

/-!
# `<NoHeaderReceived>::recv_hdr_chunk` (Block `369`) — Budget-Threaded Top-Level Proof

Budget-threaded `[LibsignalPlacement]` proofs for the `MacVerifyFailed` epilogue entry
(offsets `800 .. 920`), the `Ok(.done ...)` epilogue (offsets `1060 .. 1196`), and the
top-level Block `369` contracts `noHeaderReceived_recv_hdr_chunk_placed_okX{,_ofPrePostEnv,_ofEnv}`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkProofPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalPlacement blkPC_369 blkPC_419 blkPl_369 blkPl_419 lsProg_369
   ls_subroutine_ok_of_block lsmpl lsρ withLsCodeLoaded)
open CryptoVerification.RustHeap (vecU8)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded extHookStack subroutine_ok_withLsCodeRoLoaded_rodata'
   withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Keys (SepWPp.rw_pre)
open CryptoVerification.LibsignalSpqrV1
  (Authenticator Bytes PolyDecoder spqrAuthApi spqrPolyApi)
open CryptoVerification.SpqrV1.Alloc
  (spqrHandleErrorSym spqrMemcpySym spqrRustAllocSym spqrRustNoAllocShimSym)
open CryptoVerification.SpqrV1.Auth (AuthenticatorGhost vecBufAt)
open CryptoVerification.SpqrV1.Auth.NewFacts (authenticatorHeapAt)
open CryptoVerification.SpqrV1.Drop (chunkedNoHeaderReceivedAt)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly (chunkAt polyDecoderAt)
open CryptoVerification.SpqrV1.Poly.AddChunk (PolyDecoderStrictSorted addChunkTotal)
open CryptoVerification.SpqrV1.Poly.DecodedMessage (decodedMessageTotal)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (hiByte)
open CryptoVerification.SpqrV1.States.Leaves (of_sepWP_lscro)
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
  (NoHeaderReceivedRecvHdrChunkGhost authenticatorHeapAt_rootKey_cap_max
   authenticatorHeapAt_rootKey_eq0 authenticatorHeapAt_rootKey_ne0 bv391_toNat
   cells11_entails_memRegion_88 chunkedHeaderReceivedSize chunkedNoHeaderReceivedSize
   collapse_poly_1136_head9_tail391 collapse_scratch_736 collapse_tail_1160_1064
   fold_out_ok_done hdrLabelSym memRegion_736_80_split memRegion_out_480_split
   noHeaderReceivedRecvHdrChunkStackX out_32_add_8 out_48_add_8 out_64_add_8
   out_8_words3_shift1 out_8_words3_unmerge out_9_add_8 overlapWord1 polyDecoderNew1152
   polyDecoderNew1152RawAt polyDecoderNew1152Tail391Split poly_1136_split_head9_tail391
   ptr_hdr_take64_entails_memRegion recv_hdr_chunk_eq_macVerifyFailed
   recv_hdr_chunk_eq_ok_done sp_1591_words2_unshift1 sp_1608_words3_unshift1
   sp_1608_words5_shift1 sp_680_words2_shift7 sp_sub_1616_orr_9
   vecBufAt_drop64_eq64_emp zeroExtend32_truncate8_loByte)
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
  (SepWPp.frame_call cap_add_one_beq_zero_false ct2DeallocAt savedRegsAt vecU8HeapAt)
open CryptoVerification.SpqrV1.Unchunked (spqrLibcruxHmacSym)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
   RustCliAllocBudget RustLayoutOk rustCliAllocBudgetSpec rustCliDeallocBudgetSpec
   rustDeallocEvents)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Heap.SpecBudget (libcruxHmacBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudget
  (framelessMemcpyAcpSpec sessionMemcpyRegionROSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget (AddChunkSlotsEnv addChunkSpecX)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget (DecodedMessageEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkDefsPlacedBudget
  (NoHeaderReceivedRecvHdrChunkEnv NoHeaderReceivedRecvHdrChunkPlacedOkX
   NoHeaderReceivedRecvHdrChunkPlacedOkXOfEnv
   noHeaderReceivedRecvHdrChunkPlacedSpecOfPrePostEnv
   recvHdrChunkAllocMacHdrEvents recvHdrChunkHmacEvents)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart1PlacedBudget
  (RecvHdrChunkContractsPlaced assertFailedRecvHdrSym dealloc_placed_ok_at_recvHdr
   memcpy_withStack_lscro_ok memcpy_withStack_placed_at_recvHdr panicBoundsCheckRecvHdrSym
   recvHdrChunkPlacedPostQ recvHdrChunkPlacedPostQOfEnv recvHdrChunkPlacedPostQOfPrePostEnv
   recvHdrChunkPlacedPostQp recvHdrChunkPlacedRoAt sliceIndexFailRecvHdrSym
   spqrRustDeallocSym)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart2PlacedBudget
  (recv_hdr_chunk_part1_placed_wpp_ofPrePostEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart3PlacedBudget
  (recv_hdr_chunk_hmac_placed_wpp_ofPrePostEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart4PlacedBudget
  (recv_hdr_chunk_mac_compare_placed_wpp_ofPrePostEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart5PlacedBudget
  (recv_hdr_chunk_err_844_placed_wpp_ofPrePostEnv
   recv_hdr_chunk_err_864_placed_wpp_ofPrePostEnv
   recv_hdr_chunk_tail_924_placed_wpp_ofPrePostEnv
   recv_hdr_chunk_tail_940_placed_wpp_ofPrePostEnv)
open LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsPlacedBudget
  (PolyDecodedMessagePlacedOkX)

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  addChunkTotal decodedMessageTotal DecodedMessageEnv
  CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.NoHeaderReceived.recv_hdr_chunk
attribute [local arm64_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  out_9_add_8 out_32_add_8 out_48_add_8 out_64_add_8
  zeroExtend32_truncate8_loByte bv391_toNat
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

private theorem authenticatorHeapAt_rootKey_ne0_budget {M : AllocCostModel}
    (A : RustCliAllocBudget M) (g : AuthenticatorGhost) (auth : Authenticator)
    (hne : g.rootKey.cap ≠ 0#64) :
    authenticatorHeapAt A.repAlloc g auth ⊢
      ⌜g.rootKey.cap.toNat < 2 ^ 63 ∧ g.rootKey.ptr ≠ 0#64⌝ ∗
        memRegion g.rootKey.ptr g.rootKey.cap.toNat ∗
        A.live g.rootKey.ptr g.rootKey.cap.toNat 1 ∗
        vecU8HeapAt A.repAlloc g.macKey.cap g.macKey.ptr auth.macKey :=
  authenticatorHeapAt_rootKey_ne0 A.repAlloc g auth hne

private theorem prep_ext_stack {prog : Program} {mid : BitVec 64} {s : State}
    {P R : SepProp} {post : State → SepProp → Prop} (sp0 : BitVec 64)
    (hf : P = stackAt (sp0 - 1648#64) extHookStack ∗ R)
    (hsp_eq : s.sp = sp0 - 1648#64)
    (hnext : SepWP prog mid s (stackAt s.sp extHookStack ∗ R) post) :
    SepWP prog mid s P post := by
  rw [hf, ← hsp_eq]
  exact hnext

private theorem unprep_ext_stack {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    {sp1 : BitVec 64} (sp0 : BitVec 64) {R : SepProp}
    (hf : P = stackAt sp1 extHookStack ∗ R)
    (hsp_eq : sp1 = sp0 - 1648#64)
    (hnext : SepWPp prog ret s (stackAt (sp0 - 1648#64) extHookStack ∗ R) Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.rw_pre (by rw [hf, hsp_eq]) hnext

/-! ## 1. `MacVerifyFailed` Epilogue Entry (offsets `800 .. 920`) -/

set_option maxHeartbeats 1600000 in
theorem recv_hdr_chunk_err_epilogue_placed_wpp_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {PreEnv PostEnv : NoHeaderReceivedRecvHdrChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hC : RecvHdrChunkContractsPlaced M A lim ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F)
    (receivingHdr : PolyDecoder)
    (hdrFull : Bytes)
    (cap_hdrFull ptr_hdrFull ptr_mac ptr_hdr : BitVec 64)
    (v0 v3 v6 v8 v9 v10 v200 : BitVec 64)
    (g_auth0 : AuthenticatorGhost)
    (st0 st_cur : M.σ) (evs_pre : List AllocEvent)
    (s0 st : State) (R : SepProp)
    (hst_cur : st_cur = M.stepEvents evs_pre st0)
    (hpost_free :
      ∀ evs_free : List AllocEvent, FreeOnlyEvs evs_free → PostEnv x (evs_pre ++ evs_free))
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
      (vecBufAt A.repAlloc (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
        recvHdrChunkPlacedRoAt ∗
        memRegion x.outA chunkedHeaderReceivedSize ∗
        memRegion x.selfA chunkedNoHeaderReceivedSize ∗
        chunkAt x.chunkA x.chunk ∗
        tokenInitPlacedAt ∗
        reduceTablePlacedAt ∗
        ct2DeallocAt A.repAlloc cap_hdrFull ptr_hdrFull ∗
        (ptr_hdr ↦ₛ hdrFull.take 64) ∗
        A.live ptr_hdr 64 1 ∗
        authenticatorHeapAt A.repAlloc g_auth0 x.self.uc.auth ∗
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
        polyDecoderAt A.repAlloc (s0.sp - 1560#64) receivingHdr ∗
        memRegion (s0.sp - 1160#64) 24 ∗
        polyDecoderNew1152RawAt A.repAlloc (s0.sp - 1136#64) ∗
        memRegion (s0.sp - 736#64) 80 ∗
        memRegion (s0.sp - 656#64) 456 ∗
        ((s0.sp - 200#64) ↦₆₄ v200) ∗
        memRegion (s0.sp - 192#64) 24 ∗
        memRegion (s0.sp - 168#64) 48 ∗
        memRegion (s0.sp - 120#64) 8 ∗
        memRegion (s0.sp - 112#64) 16 ∗
        savedRegsAt s0 ∗
        memRegion (s0.sp - 18704#64) 672 ∗
        A.pool lim st_cur st ∗
        stackAt (s0.sp - 1648#64) extHookStack)
      (recvHdrChunkPlacedPostQOfPrePostEnv M A lim F PreEnv PostEnv x st0 s0 R)
      (recvHdrChunkPlacedPostQp F x s0 R) := by
  refine SepWPp.fold (ptr_hdr_take64_entails_memRegion ptr_hdr hdrFull hge64) (by sep_focus) ?_
  have h_dealloc := dealloc_placed_ok_at_recvHdr hC
  have h_err844 :=
    @recv_hdr_chunk_err_844_placed_wpp_ofPrePostEnv _ M A lim F PreEnv PostEnv ext
      hC x hdrFull cap_hdrFull ptr_hdrFull ptr_mac g_auth0 st0
  have h_err864 :=
    @recv_hdr_chunk_err_864_placed_wpp_ofPrePostEnv _ M A lim F PreEnv PostEnv ext
      hC x receivingHdr hdrFull cap_hdrFull ptr_hdrFull ptr_mac
      v0 g_auth0.macKey.ptr ptr_hdrFull v3 g_auth0.rootKey.cap g_auth0.rootKey.ptr
      v6 g_auth0.macKey.cap v8 v9 v10 v200 st0
  have hrlay64 : RustLayoutOk 64 1 := ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩
  have hsp_norm : st.readReg64 .sp = s0.sp - 1648#64 := hsp
  by_cases hcap : g_auth0.rootKey.cap = 0#64
  · refine SepWPp.fold
      (authenticatorHeapAt_rootKey_eq0 A.repAlloc g_auth0 x.self.uc.auth hcap)
      (by sep_focus) ?_
    simp only [wp_norm, arm64_norm] at hsp_norm hx19 hx20 hx22 hx23 hx25
    clear hC
    refine of_sepWP_lscro (mid := lsρ spqrRustDeallocSym) hinv ?_
    wp_steps_sync_pool (lsρ spqrRustDeallocSym)
    try simp only [State.setMem_setMem]
    refine prep_ext_stack s0.sp (by sep_focus) (by simp only [wp_norm, arm64_norm, *]) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv1
    wpp_call_lscro_recvHdr_budget h_dealloc (ptr_hdr, 64, 1, st_cur) hinv1
    refine CryptoVerification.SpqrV1.Auth.SepWPp.pure_left_focus _ (by sep_focus) fun htr1 => ?_
    refine unprep_ext_stack s0.sp (by sep_focus) (by simp only [wp_norm, arm64_norm, *]) ?_
    refine of_sepWP_lscro (mid := (blkPl_369).base + 844#64) hF_sf ?_
    wp_steps_sync_pool ((blkPl_369).base + 844#64)
    try simp only [State.setMem_setMem]
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv2
    refine SepWPp.rw_pre (by sep_ac_rfl)
      (h_err844 (M.stepEvents (rustDeallocEvents 64 1) st_cur) s0 _
        (vecBufAt A.repAlloc (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
          memRegion x.outA chunkedHeaderReceivedSize ∗
          memRegion x.selfA chunkedNoHeaderReceivedSize ∗
          chunkAt x.chunkA x.chunk ∗
          tokenInitPlacedAt ∗
          reduceTablePlacedAt ∗
          ct2DeallocAt A.repAlloc cap_hdrFull ptr_hdrFull ∗
          ((s0.sp - 1648#64) ↦₆₄ v0) ∗
          ((s0.sp - 1632#64) ↦₆₄ ptr_hdrFull) ∗
          ((s0.sp - 1624#64) ↦₆₄ v3) ∗
          ((s0.sp - 1616#64) ↦₆₄ g_auth0.rootKey.cap) ∗
          ((s0.sp - 1608#64) ↦₆₄ g_auth0.rootKey.ptr) ∗
          ((s0.sp - 1600#64) ↦₆₄ v6) ∗
          ((s0.sp - 1584#64) ↦₆₄ v8) ∗
          ((s0.sp - 1576#64) ↦₆₄ v9) ∗
          ((s0.sp - 1568#64) ↦₆₄ v10) ∗
          polyDecoderAt A.repAlloc (s0.sp - 1560#64) receivingHdr ∗
          memRegion (s0.sp - 1160#64) 24 ∗
          polyDecoderNew1152RawAt A.repAlloc (s0.sp - 1136#64) ∗
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
        (fun st2 evs_mk hfree_mk hpc2 hrun2 hsp2 htr2 hvregs2 hinv3
          hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx26_2 => ?_))
    have hst2 :
        M.stepEvents evs_mk (M.stepEvents (rustDeallocEvents 64 1) st_cur) =
          M.stepEvents (evs_pre ++ (rustDeallocEvents 64 1 ++ evs_mk)) st0 := by
      rw [hst_cur, ← M.stepEvents_append, ← M.stepEvents_append]
    have hpost2 :
        ∀ evs_free : List AllocEvent, FreeOnlyEvs evs_free →
          PostEnv x ((evs_pre ++ (rustDeallocEvents 64 1 ++ evs_mk)) ++ evs_free) := by
      intro evs_free hf
      rw [List.append_assoc]
      exact hpost_free _
        (FreeOnlyEvs.append (FreeOnlyEvs.append (FreeOnlyEvs.singleton 1 64) hfree_mk) hf)
    exact SepWPp.rw_pre (by sep_ac_rfl)
      (h_err864
        (M.stepEvents evs_mk (M.stepEvents (rustDeallocEvents 64 1) st_cur))
        (evs_pre ++ (rustDeallocEvents 64 1 ++ evs_mk))
        s0 st2 R hst2 hpost2 hres hge64 hmax_hdr
        hpc2 hrun2 hsp2 hsp_s0 htr2 hvregs2 hinv3
        hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx26_2)
  · have hcap_beq : (g_auth0.rootKey.cap == 0#64) = false := beq_false_of_ne hcap
    have hcap_pos : 0 < g_auth0.rootKey.cap.toNat :=
      Nat.pos_of_ne_zero (fun h0 => hcap (BitVec.eq_of_toNat_eq h0))
    refine SepWPp.fold
      (authenticatorHeapAt_rootKey_ne0_budget A g_auth0 x.self.uc.auth hcap)
      (by sep_focus) ?_
    refine CryptoVerification.SpqrV1.Auth.SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨hmax, hptr_ne⟩
    have hrlay_rk : RustLayoutOk g_auth0.rootKey.cap.toNat 1 :=
      ⟨⟨hcap_pos, ⟨0, rfl⟩, by omega⟩, by decide⟩
    simp only [wp_norm, arm64_norm] at hsp_norm hx19 hx20 hx22 hx23 hx25
    clear hC
    refine of_sepWP_lscro (mid := lsρ spqrRustDeallocSym) hinv ?_
    wp_steps_sync_pool (lsρ spqrRustDeallocSym)
    try simp only [State.setMem_setMem]
    refine prep_ext_stack s0.sp (by sep_focus) (by simp only [wp_norm, arm64_norm, *]) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv1
    wpp_call_lscro_recvHdr_budget h_dealloc (ptr_hdr, 64, 1, st_cur) hinv1
    refine CryptoVerification.SpqrV1.Auth.SepWPp.pure_left_focus _ (by sep_focus) fun htr1 => ?_
    refine unprep_ext_stack s0.sp (by sep_focus) (by simp only [wp_norm, arm64_norm, *]) ?_
    refine of_sepWP_lscro (mid := lsρ spqrRustDeallocSym) hF_sf ?_
    wp_steps_sync_pool (lsρ spqrRustDeallocSym)
    try simp only [State.setMem_setMem]
    refine prep_ext_stack s0.sp (by sep_focus) (by simp only [wp_norm, arm64_norm, *]) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv2
    wpp_call_lscro_recvHdr_budget h_dealloc
      (g_auth0.rootKey.ptr, g_auth0.rootKey.cap.toNat, 1,
       M.stepEvents (rustDeallocEvents 64 1) st_cur) hinv2
    refine CryptoVerification.SpqrV1.Auth.SepWPp.pure_left_focus _ (by sep_focus) fun htr2 => ?_
    refine unprep_ext_stack s0.sp (by sep_focus) (by simp only [wp_norm, arm64_norm, *]) ?_
    let st_rk :=
      M.stepEvents (rustDeallocEvents g_auth0.rootKey.cap.toNat 1)
        (M.stepEvents (rustDeallocEvents 64 1) st_cur)
    refine SepWPp.rw_pre (by sep_ac_rfl)
      (h_err844 st_rk s0 sf_1
        (vecBufAt A.repAlloc (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
          memRegion x.outA chunkedHeaderReceivedSize ∗
          memRegion x.selfA chunkedNoHeaderReceivedSize ∗
          chunkAt x.chunkA x.chunk ∗
          tokenInitPlacedAt ∗
          reduceTablePlacedAt ∗
          ct2DeallocAt A.repAlloc cap_hdrFull ptr_hdrFull ∗
          ((s0.sp - 1648#64) ↦₆₄ v0) ∗
          ((s0.sp - 1632#64) ↦₆₄ ptr_hdrFull) ∗
          ((s0.sp - 1624#64) ↦₆₄ v3) ∗
          ((s0.sp - 1616#64) ↦₆₄ g_auth0.rootKey.cap) ∗
          ((s0.sp - 1608#64) ↦₆₄ g_auth0.rootKey.ptr) ∗
          ((s0.sp - 1600#64) ↦₆₄ v6) ∗
          ((s0.sp - 1584#64) ↦₆₄ v8) ∗
          ((s0.sp - 1576#64) ↦₆₄ v9) ∗
          ((s0.sp - 1568#64) ↦₆₄ v10) ∗
          polyDecoderAt A.repAlloc (s0.sp - 1560#64) receivingHdr ∗
          memRegion (s0.sp - 1160#64) 24 ∗
          polyDecoderNew1152RawAt A.repAlloc (s0.sp - 1136#64) ∗
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
        (fun st2 evs_mk hfree_mk hpc2 hrun2 hsp2 htr3 hvregs2 hinv3
          hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx26_2 => ?_))
    let evs_hdr_rk_mk :=
      rustDeallocEvents 64 1 ++ rustDeallocEvents g_auth0.rootKey.cap.toNat 1 ++ evs_mk
    have hst2 :
        M.stepEvents evs_mk st_rk = M.stepEvents (evs_pre ++ evs_hdr_rk_mk) st0 := by
      dsimp only [st_rk, evs_hdr_rk_mk]
      rw [hst_cur, ← M.stepEvents_append, ← M.stepEvents_append, ← M.stepEvents_append]
      exact congrArg (fun l => M.stepEvents l st0) (by simp only [List.append_assoc])
    have hpost2 :
        ∀ evs_free : List AllocEvent, FreeOnlyEvs evs_free →
          PostEnv x ((evs_pre ++ evs_hdr_rk_mk) ++ evs_free) := by
      intro evs_free hf
      dsimp only [evs_hdr_rk_mk]
      rw [List.append_assoc]
      exact hpost_free _
        (FreeOnlyEvs.append
          (FreeOnlyEvs.append
            (FreeOnlyEvs.append (FreeOnlyEvs.singleton 1 64)
              (FreeOnlyEvs.singleton 1 g_auth0.rootKey.cap.toNat))
            hfree_mk)
          hf)
    exact SepWPp.rw_pre (by sep_ac_rfl)
      (h_err864
        (M.stepEvents evs_mk st_rk)
        (evs_pre ++ evs_hdr_rk_mk)
        s0 st2 R hst2 hpost2 hres hge64 hmax_hdr
        hpc2 hrun2 hsp2 hsp_s0 htr3 hvregs2 hinv3
        hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx26_2)

theorem recv_hdr_chunk_err_epilogue_placed_wpp_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {Env : NoHeaderReceivedRecvHdrChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hC : RecvHdrChunkContractsPlaced M A lim ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F) (receivingHdr : PolyDecoder) (hdrFull : Bytes)
    (cap_hdrFull ptr_hdrFull ptr_mac ptr_hdr : BitVec 64)
    (v0 v3 v6 v8 v9 v10 v200 : BitVec 64)
    (g_auth0 : AuthenticatorGhost)
    (st0 st_cur : M.σ) (evs_pre : List AllocEvent)
    (s0 st : State) (R : SepProp)
    (hst_cur : st_cur = M.stepEvents evs_pre st0)
    (hpost_free :
      ∀ evs_free : List AllocEvent, FreeOnlyEvs evs_free → Env x (evs_pre ++ evs_free))
    (hres : x.self.recv_hdr_chunk x.epoch x.chunk = .error (.err .macVerifyFailed))
    (hge64 : 64 ≤ hdrFull.length) (hmax_hdr : hdrFull.length < 2 ^ 63)
    (hptr_hdr : ptr_hdr ≠ 0#64)
    (hpc : st.pc = (blkPl_369).base + 800#64) (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 1648#64) (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace) (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx19 : st.readReg64 .x19 = x.outA) (hx20 : st.readReg64 .x20 = cap_hdrFull)
    (hx22 : st.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64))
    (hx23 : st.readReg64 .x23 = ptr_mac) (hx25 : st.readReg64 .x25 = ptr_hdr) :
    SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (vecBufAt A.repAlloc (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
        recvHdrChunkPlacedRoAt ∗ memRegion x.outA chunkedHeaderReceivedSize ∗
        memRegion x.selfA chunkedNoHeaderReceivedSize ∗ chunkAt x.chunkA x.chunk ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ ct2DeallocAt A.repAlloc cap_hdrFull ptr_hdrFull ∗
        (ptr_hdr ↦ₛ hdrFull.take 64) ∗ A.live ptr_hdr 64 1 ∗
        authenticatorHeapAt A.repAlloc g_auth0 x.self.uc.auth ∗
        ((s0.sp - 1648#64) ↦₆₄ v0) ∗ ((s0.sp - 1640#64) ↦₆₄ g_auth0.macKey.ptr) ∗
        ((s0.sp - 1632#64) ↦₆₄ ptr_hdrFull) ∗ ((s0.sp - 1624#64) ↦₆₄ v3) ∗
        ((s0.sp - 1616#64) ↦₆₄ g_auth0.rootKey.cap) ∗ ((s0.sp - 1608#64) ↦₆₄ g_auth0.rootKey.ptr) ∗
        ((s0.sp - 1600#64) ↦₆₄ v6) ∗ ((s0.sp - 1592#64) ↦₆₄ g_auth0.macKey.cap) ∗
        ((s0.sp - 1584#64) ↦₆₄ v8) ∗ ((s0.sp - 1576#64) ↦₆₄ v9) ∗
        ((s0.sp - 1568#64) ↦₆₄ v10) ∗ polyDecoderAt A.repAlloc (s0.sp - 1560#64) receivingHdr ∗
        memRegion (s0.sp - 1160#64) 24 ∗ polyDecoderNew1152RawAt A.repAlloc (s0.sp - 1136#64) ∗
        memRegion (s0.sp - 736#64) 80 ∗ memRegion (s0.sp - 656#64) 456 ∗
        ((s0.sp - 200#64) ↦₆₄ v200) ∗ memRegion (s0.sp - 192#64) 24 ∗
        memRegion (s0.sp - 168#64) 48 ∗ memRegion (s0.sp - 120#64) 8 ∗
        memRegion (s0.sp - 112#64) 16 ∗ savedRegsAt s0 ∗
        memRegion (s0.sp - 18704#64) 672 ∗ A.pool lim st_cur st ∗
        stackAt (s0.sp - 1648#64) extHookStack)
      (recvHdrChunkPlacedPostQOfEnv M A lim F Env x st0 s0 R)
      (recvHdrChunkPlacedPostQp F x s0 R) :=
  recv_hdr_chunk_err_epilogue_placed_wpp_ofPrePostEnv hC x receivingHdr hdrFull cap_hdrFull
    ptr_hdrFull ptr_mac ptr_hdr v0 v3 v6 v8 v9 v10 v200 g_auth0 st0 st_cur evs_pre s0 st R
    hst_cur hpost_free hres hge64 hmax_hdr hptr_hdr hpc hrun hsp hsp_s0 htr hvregs hinv
    hx19 hx20 hx22 hx23 hx25

theorem recv_hdr_chunk_err_epilogue_placed_wpp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hC : RecvHdrChunkContractsPlaced M A lim ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F) (receivingHdr : PolyDecoder) (hdrFull : Bytes)
    (cap_hdrFull ptr_hdrFull ptr_mac ptr_hdr : BitVec 64)
    (v0 v3 v6 v8 v9 v10 v200 : BitVec 64)
    (g_auth0 : AuthenticatorGhost)
    (st0 st_cur : M.σ) (evs_pre : List AllocEvent)
    (s0 st : State) (R : SepProp)
    (hst_cur : st_cur = M.stepEvents evs_pre st0)
    (hpost_free :
      ∀ evs_free : List AllocEvent, FreeOnlyEvs evs_free →
        NoHeaderReceivedRecvHdrChunkEnv x (evs_pre ++ evs_free))
    (hres : x.self.recv_hdr_chunk x.epoch x.chunk = .error (.err .macVerifyFailed))
    (hge64 : 64 ≤ hdrFull.length) (hmax_hdr : hdrFull.length < 2 ^ 63)
    (hptr_hdr : ptr_hdr ≠ 0#64)
    (hpc : st.pc = (blkPl_369).base + 800#64) (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 1648#64) (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace) (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx19 : st.readReg64 .x19 = x.outA) (hx20 : st.readReg64 .x20 = cap_hdrFull)
    (hx22 : st.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64))
    (hx23 : st.readReg64 .x23 = ptr_mac) (hx25 : st.readReg64 .x25 = ptr_hdr) :
    SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (vecBufAt A.repAlloc (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
        recvHdrChunkPlacedRoAt ∗ memRegion x.outA chunkedHeaderReceivedSize ∗
        memRegion x.selfA chunkedNoHeaderReceivedSize ∗ chunkAt x.chunkA x.chunk ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ ct2DeallocAt A.repAlloc cap_hdrFull ptr_hdrFull ∗
        (ptr_hdr ↦ₛ hdrFull.take 64) ∗ A.live ptr_hdr 64 1 ∗
        authenticatorHeapAt A.repAlloc g_auth0 x.self.uc.auth ∗
        ((s0.sp - 1648#64) ↦₆₄ v0) ∗ ((s0.sp - 1640#64) ↦₆₄ g_auth0.macKey.ptr) ∗
        ((s0.sp - 1632#64) ↦₆₄ ptr_hdrFull) ∗ ((s0.sp - 1624#64) ↦₆₄ v3) ∗
        ((s0.sp - 1616#64) ↦₆₄ g_auth0.rootKey.cap) ∗ ((s0.sp - 1608#64) ↦₆₄ g_auth0.rootKey.ptr) ∗
        ((s0.sp - 1600#64) ↦₆₄ v6) ∗ ((s0.sp - 1592#64) ↦₆₄ g_auth0.macKey.cap) ∗
        ((s0.sp - 1584#64) ↦₆₄ v8) ∗ ((s0.sp - 1576#64) ↦₆₄ v9) ∗
        ((s0.sp - 1568#64) ↦₆₄ v10) ∗ polyDecoderAt A.repAlloc (s0.sp - 1560#64) receivingHdr ∗
        memRegion (s0.sp - 1160#64) 24 ∗ polyDecoderNew1152RawAt A.repAlloc (s0.sp - 1136#64) ∗
        memRegion (s0.sp - 736#64) 80 ∗ memRegion (s0.sp - 656#64) 456 ∗
        ((s0.sp - 200#64) ↦₆₄ v200) ∗ memRegion (s0.sp - 192#64) 24 ∗
        memRegion (s0.sp - 168#64) 48 ∗ memRegion (s0.sp - 120#64) 8 ∗
        memRegion (s0.sp - 112#64) 16 ∗ savedRegsAt s0 ∗
        memRegion (s0.sp - 18704#64) 672 ∗ A.pool lim st_cur st ∗
        stackAt (s0.sp - 1648#64) extHookStack)
      (recvHdrChunkPlacedPostQ M A lim F x st0 s0 R)
      (recvHdrChunkPlacedPostQp F x s0 R) :=
  recv_hdr_chunk_err_epilogue_placed_wpp_ofEnv hC x receivingHdr hdrFull cap_hdrFull
    ptr_hdrFull ptr_mac ptr_hdr v0 v3 v6 v8 v9 v10 v200 g_auth0 st0 st_cur evs_pre s0 st R
    hst_cur hpost_free hres hge64 hmax_hdr hptr_hdr hpc hrun hsp hsp_s0 htr hvregs hinv
    hx19 hx20 hx22 hx23 hx25

/-! ## 2. `Ok(.done ...)` Epilogue (offsets `1060 .. 1196`) -/

set_option maxHeartbeats 1600000 in
theorem recv_hdr_chunk_ok_epilogue_placed_wpp_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {PreEnv PostEnv : NoHeaderReceivedRecvHdrChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hC : RecvHdrChunkContractsPlaced M A lim ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F)
    (g_auth0 : AuthenticatorGhost) (receivingHdr : PolyDecoder) (hdrFull : Bytes)
    (cap_hdrFull ptr_hdrFull ptr_hdr ptr_mac v0 v1 v3 v10 v200 : BitVec 64)
    (st0 st_cur : M.σ) (evs_pre : List AllocEvent)
    (s0 st : State) (R : SepProp)
    (hst_cur : st_cur = M.stepEvents evs_pre st0)
    (hpost_free :
      ∀ evs_free : List AllocEvent, FreeOnlyEvs evs_free → PostEnv x (evs_pre ++ evs_free))
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
      (authenticatorHeapAt A.repAlloc g_auth0 x.self.uc.auth ∗ (ptr_hdr ↦ₛ hdrFull.take 64) ∗
        A.live ptr_hdr 64 1 ∗
        vecBufAt A.repAlloc (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
        recvHdrChunkPlacedRoAt ∗ memRegion x.outA chunkedHeaderReceivedSize ∗
        memRegion x.selfA chunkedNoHeaderReceivedSize ∗ chunkAt x.chunkA x.chunk ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool lim st_cur st ∗
        ct2DeallocAt A.repAlloc cap_hdrFull ptr_hdrFull ∗
        ((s0.sp - 1648#64) ↦₆₄ v0) ∗ ((s0.sp - 1640#64) ↦₆₄ v1) ∗
        ((s0.sp - 1632#64) ↦₆₄ ptr_hdrFull) ∗ ((s0.sp - 1624#64) ↦₆₄ v3) ∗
        ((s0.sp - 1616#64) ↦₆₄ g_auth0.rootKey.cap) ∗ ((s0.sp - 1608#64) ↦₆₄ g_auth0.rootKey.ptr) ∗
        ((s0.sp - 1600#64) ↦₆₄ BitVec.ofNat 64 x.self.uc.auth.rootKey.length) ∗
        ((s0.sp - 1592#64) ↦₆₄ g_auth0.macKey.cap) ∗ ((s0.sp - 1584#64) ↦₆₄ g_auth0.macKey.ptr) ∗
        ((s0.sp - 1576#64) ↦₆₄ BitVec.ofNat 64 x.self.uc.auth.macKey.length) ∗
        ((s0.sp - 1568#64) ↦₆₄ v10) ∗ polyDecoderAt A.repAlloc (s0.sp - 1560#64) receivingHdr ∗
        memRegion (s0.sp - 1160#64) 24 ∗ polyDecoderNew1152RawAt A.repAlloc (s0.sp - 1136#64) ∗
        memRegion (s0.sp - 736#64) 80 ∗ memRegion (s0.sp - 656#64) 456 ∗
        ((s0.sp - 200#64) ↦₆₄ v200) ∗ memRegion (s0.sp - 192#64) 24 ∗
        memRegion (s0.sp - 168#64) 48 ∗ memRegion (s0.sp - 120#64) 8 ∗
        memRegion (s0.sp - 112#64) 16 ∗ savedRegsAt s0 ∗
        memRegion (s0.sp - 18704#64) 672 ∗ stackAt (s0.sp - 1648#64) extHookStack)
      (recvHdrChunkPlacedPostQOfPrePostEnv M A lim F PreEnv PostEnv x st0 s0 R)
      (recvHdrChunkPlacedPostQp F x s0 R) := by
  have horr := sp_sub_1616_orr_9 s0.sp hsp_s0
  have h_memcpy := memcpy_withStack_lscro_ok (polyDecoderNew1152Tail391Split A.repAlloc)
    (by decide) extHookStack (memcpy_withStack_placed_at_recvHdr hC extHookStack)
  have h_tail940 :=
    @recv_hdr_chunk_tail_940_placed_wpp_ofPrePostEnv _ M A lim F PreEnv PostEnv ext
      hC x receivingHdr cap_hdrFull ptr_hdrFull st0
  have h_tail924 :=
    @recv_hdr_chunk_tail_924_placed_wpp_ofPrePostEnv _ M A lim F PreEnv PostEnv ext
      hC x receivingHdr hdrFull cap_hdrFull ptr_hdrFull ptr_mac st0
  refine SepWPp.fold
    (authenticatorHeapAt_rootKey_cap_max A.repAlloc g_auth0 x.self.uc.auth)
    (by sep_focus) ?_
  refine CryptoVerification.SpqrV1.Auth.SepWPp.pure_left_focus _ (by sep_focus) fun hmax_rk => ?_
  have hcap_cmn : (g_auth0.rootKey.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_false hmax_rk
  refine SepWPp.fold (memRegion_out_480_split x.outA) (by sep_focus) ?_
  refine SepWPp.fold (memRegion_736_80_split s0.sp) (by sep_focus) ?_
  dsimp only [cells]
  sep_elim_exists
  rename_i ub88 u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 sc0 sc8 sc16 sc24 sc32
  simp only [bv_sub_add_lit, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWPp.fold (Entails.of_eq (poly_1136_split_head9_tail391 A.repAlloc s0.sp)) (by sep_focus) ?_
  refine SepWPp.fold (Entails.of_eq (sp_1608_words5_shift1 s0.sp
    g_auth0.rootKey.ptr (BitVec.ofNat 64 x.self.uc.auth.rootKey.length)
    g_auth0.macKey.cap g_auth0.macKey.ptr (BitVec.ofNat 64 x.self.uc.auth.macKey.length)))
    (by sep_focus) ?_
  refine SepWPp.fold (Entails.of_eq (out_8_words3_shift1 x.outA u8 u16 u24)) (by sep_focus) ?_
  have hsp_norm : st.readReg64 .sp = s0.sp - 1648#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm hx19 hx20 hx22 hx23 hx24 hx25
  clear hC
  refine of_sepWP_lscro (mid := lsρ spqrMemcpySym) hinv ?_
  apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
    (Q := (blkPC_369).rebase (blkPl_369).base
      (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException (Rust.withPanics ext)))
    CryptoVerification.blkLib_eq_369 (mid := lsρ spqrMemcpySym)
  intro _m_strip
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
    (hiByte sc32)) (by sep_focus) ?_
  refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]))
    (hnext := ?_)
  try simp only [State.setMem_setMem]
  refine prep_ext_stack s0.sp (by sep_focus) (by simp only [wp_norm, arm64_norm, *]) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  wpp_call_lscro_recvHdr_budget h_memcpy (x.outA + 89#64, s0.sp - 1127#64) hinv1
  refine CryptoVerification.SpqrV1.Auth.SepWPp.pure_left_focus _ (by sep_focus) fun hp_mc => ?_
  rcases hp_mc with ⟨hvm1, htr1, _⟩
  refine SepWPp.rw_pre (by rw [← A.pool_of_vmPreserved hvm1]) ?_
  refine unprep_ext_stack s0.sp (by sep_focus) (by simp only [wp_norm, arm64_norm, *]) ?_
  have hlive_hdr : A.live ptr_hdr 64 1 = A.repAlloc.live ptr_hdr 64 1 := rfl
  refine SepWPp.rw_pre (by rw [hlive_hdr]) ?_
  refine SepWPp.fold
    (fold_out_ok_done A.repAlloc x g_auth0 hdrFull ptr_hdr hptr_hdr hge64 hres)
    (by sep_focus) ?_
  refine SepWPp.fold (collapse_poly_1136_head9_tail391 s0.sp) (by sep_focus) ?_
  refine SepWPp.fold
    (cells11_entails_memRegion_88 s0.sp v0 v1 ptr_hdrFull v3
      g_auth0.rootKey.cap g_auth0.rootKey.ptr (BitVec.ofNat 64 x.self.uc.auth.rootKey.length)
      g_auth0.macKey.cap g_auth0.macKey.ptr (BitVec.ofNat 64 x.self.uc.auth.macKey.length) v10)
    (by sep_focus) ?_
  refine SepWPp.fold (collapse_tail_1160_1064 s0.sp v200) (by sep_focus) ?_
  have hx22_sf : sf.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 (hdrFull.length - 64) := by
    simp only [wp_norm, arm64_norm, *]
  by_cases heq64 : hdrFull.length = 64
  · have hsub0 : hdrFull.length - 64 = 0 := by omega
    have hx22_sf0 : sf.readReg64 (Reg.gpr 22#5) = 0#64 := by
      rw [hx22_sf, hsub0]
    refine SepWPp.fold (vecBufAt_drop64_eq64_emp A.repAlloc ptr_mac hdrFull heq64) (by sep_focus) ?_
    refine of_sepWP_lscro (mid := (blkPl_369).base + 940#64) hF_sf ?_
    wp_steps_sync_pool ((blkPl_369).base + 940#64)
    try simp only [State.setMem_setMem]
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv2
    refine SepWPp.rw_pre (by sep_ac_rfl)
      (h_tail940 st_cur evs_pre s0 _ R hst_cur hpost_free
        (by wp_norm_goal) (by wp_norm_goal)
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
      rw [hx22_sf]
      exact hx22_beq
    refine of_sepWP_lscro (mid := (blkPl_369).base + 924#64) hF_sf ?_
    wp_steps_sync_pool ((blkPl_369).base + 924#64)
    try simp only [State.setMem_setMem]
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv2
    refine SepWPp.rw_pre (by sep_ac_rfl)
      (h_tail924 st_cur evs_pre s0 _ R hst_cur hpost_free hge65 hmax_hdr
        (by wp_norm_goal) (by wp_norm_goal)
        (by simp only [wp_norm, arm64_norm, *]) hsp_s0
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) hinv2
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]))

theorem recv_hdr_chunk_ok_epilogue_placed_wpp_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {Env : NoHeaderReceivedRecvHdrChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hC : RecvHdrChunkContractsPlaced M A lim ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F)
    (g_auth0 : AuthenticatorGhost) (receivingHdr : PolyDecoder) (hdrFull : Bytes)
    (cap_hdrFull ptr_hdrFull ptr_hdr ptr_mac v0 v1 v3 v10 v200 : BitVec 64)
    (st0 st_cur : M.σ) (evs_pre : List AllocEvent)
    (s0 st : State) (R : SepProp)
    (hst_cur : st_cur = M.stepEvents evs_pre st0)
    (hpost_free :
      ∀ evs_free : List AllocEvent, FreeOnlyEvs evs_free → Env x (evs_pre ++ evs_free))
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
      (authenticatorHeapAt A.repAlloc g_auth0 x.self.uc.auth ∗ (ptr_hdr ↦ₛ hdrFull.take 64) ∗
        A.live ptr_hdr 64 1 ∗
        vecBufAt A.repAlloc (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
        recvHdrChunkPlacedRoAt ∗ memRegion x.outA chunkedHeaderReceivedSize ∗
        memRegion x.selfA chunkedNoHeaderReceivedSize ∗ chunkAt x.chunkA x.chunk ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool lim st_cur st ∗
        ct2DeallocAt A.repAlloc cap_hdrFull ptr_hdrFull ∗
        ((s0.sp - 1648#64) ↦₆₄ v0) ∗ ((s0.sp - 1640#64) ↦₆₄ v1) ∗
        ((s0.sp - 1632#64) ↦₆₄ ptr_hdrFull) ∗ ((s0.sp - 1624#64) ↦₆₄ v3) ∗
        ((s0.sp - 1616#64) ↦₆₄ g_auth0.rootKey.cap) ∗ ((s0.sp - 1608#64) ↦₆₄ g_auth0.rootKey.ptr) ∗
        ((s0.sp - 1600#64) ↦₆₄ BitVec.ofNat 64 x.self.uc.auth.rootKey.length) ∗
        ((s0.sp - 1592#64) ↦₆₄ g_auth0.macKey.cap) ∗ ((s0.sp - 1584#64) ↦₆₄ g_auth0.macKey.ptr) ∗
        ((s0.sp - 1576#64) ↦₆₄ BitVec.ofNat 64 x.self.uc.auth.macKey.length) ∗
        ((s0.sp - 1568#64) ↦₆₄ v10) ∗ polyDecoderAt A.repAlloc (s0.sp - 1560#64) receivingHdr ∗
        memRegion (s0.sp - 1160#64) 24 ∗ polyDecoderNew1152RawAt A.repAlloc (s0.sp - 1136#64) ∗
        memRegion (s0.sp - 736#64) 80 ∗ memRegion (s0.sp - 656#64) 456 ∗
        ((s0.sp - 200#64) ↦₆₄ v200) ∗ memRegion (s0.sp - 192#64) 24 ∗
        memRegion (s0.sp - 168#64) 48 ∗ memRegion (s0.sp - 120#64) 8 ∗
        memRegion (s0.sp - 112#64) 16 ∗ savedRegsAt s0 ∗
        memRegion (s0.sp - 18704#64) 672 ∗ stackAt (s0.sp - 1648#64) extHookStack)
      (recvHdrChunkPlacedPostQOfEnv M A lim F Env x st0 s0 R)
      (recvHdrChunkPlacedPostQp F x s0 R) :=
  recv_hdr_chunk_ok_epilogue_placed_wpp_ofPrePostEnv hC x g_auth0 receivingHdr hdrFull
    cap_hdrFull ptr_hdrFull ptr_hdr ptr_mac v0 v1 v3 v10 v200 st0 st_cur evs_pre s0 st R
    hst_cur hpost_free hres hptr_hdr hge64 hmax_hdr hpc hrun hsp hsp_s0 htr hvregs hinv
    hx19 hx20 hx22 hx23 hx24 hx25

theorem recv_hdr_chunk_ok_epilogue_placed_wpp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hC : RecvHdrChunkContractsPlaced M A lim ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F)
    (g_auth0 : AuthenticatorGhost) (receivingHdr : PolyDecoder) (hdrFull : Bytes)
    (cap_hdrFull ptr_hdrFull ptr_hdr ptr_mac v0 v1 v3 v10 v200 : BitVec 64)
    (st0 st_cur : M.σ) (evs_pre : List AllocEvent)
    (s0 st : State) (R : SepProp)
    (hst_cur : st_cur = M.stepEvents evs_pre st0)
    (hpost_free :
      ∀ evs_free : List AllocEvent, FreeOnlyEvs evs_free →
        NoHeaderReceivedRecvHdrChunkEnv x (evs_pre ++ evs_free))
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
      (authenticatorHeapAt A.repAlloc g_auth0 x.self.uc.auth ∗ (ptr_hdr ↦ₛ hdrFull.take 64) ∗
        A.live ptr_hdr 64 1 ∗
        vecBufAt A.repAlloc (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
        recvHdrChunkPlacedRoAt ∗ memRegion x.outA chunkedHeaderReceivedSize ∗
        memRegion x.selfA chunkedNoHeaderReceivedSize ∗ chunkAt x.chunkA x.chunk ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool lim st_cur st ∗
        ct2DeallocAt A.repAlloc cap_hdrFull ptr_hdrFull ∗
        ((s0.sp - 1648#64) ↦₆₄ v0) ∗ ((s0.sp - 1640#64) ↦₆₄ v1) ∗
        ((s0.sp - 1632#64) ↦₆₄ ptr_hdrFull) ∗ ((s0.sp - 1624#64) ↦₆₄ v3) ∗
        ((s0.sp - 1616#64) ↦₆₄ g_auth0.rootKey.cap) ∗ ((s0.sp - 1608#64) ↦₆₄ g_auth0.rootKey.ptr) ∗
        ((s0.sp - 1600#64) ↦₆₄ BitVec.ofNat 64 x.self.uc.auth.rootKey.length) ∗
        ((s0.sp - 1592#64) ↦₆₄ g_auth0.macKey.cap) ∗ ((s0.sp - 1584#64) ↦₆₄ g_auth0.macKey.ptr) ∗
        ((s0.sp - 1576#64) ↦₆₄ BitVec.ofNat 64 x.self.uc.auth.macKey.length) ∗
        ((s0.sp - 1568#64) ↦₆₄ v10) ∗ polyDecoderAt A.repAlloc (s0.sp - 1560#64) receivingHdr ∗
        memRegion (s0.sp - 1160#64) 24 ∗ polyDecoderNew1152RawAt A.repAlloc (s0.sp - 1136#64) ∗
        memRegion (s0.sp - 736#64) 80 ∗ memRegion (s0.sp - 656#64) 456 ∗
        ((s0.sp - 200#64) ↦₆₄ v200) ∗ memRegion (s0.sp - 192#64) 24 ∗
        memRegion (s0.sp - 168#64) 48 ∗ memRegion (s0.sp - 120#64) 8 ∗
        memRegion (s0.sp - 112#64) 16 ∗ savedRegsAt s0 ∗
        memRegion (s0.sp - 18704#64) 672 ∗ stackAt (s0.sp - 1648#64) extHookStack)
      (recvHdrChunkPlacedPostQ M A lim F x st0 s0 R)
      (recvHdrChunkPlacedPostQp F x s0 R) :=
  recv_hdr_chunk_ok_epilogue_placed_wpp_ofEnv hC x g_auth0 receivingHdr hdrFull
    cap_hdrFull ptr_hdrFull ptr_hdr ptr_mac v0 v1 v3 v10 v200 st0 st_cur evs_pre s0 st R
    hst_cur hpost_free hres hptr_hdr hge64 hmax_hdr hpc hrun hsp hsp_s0 htr hvregs hinv
    hx19 hx20 hx22 hx23 hx24 hx25

/-! ## 3. Top-Level Relocatable Contracts (`NoHeaderReceivedRecvHdrChunkPlacedOkX*`) -/

/-- Two-envelope (`PreEnv` / `PostEnv`) relocatable contract for `<NoHeaderReceived>::recv_hdr_chunk`
    (Block `369`) wrapped with `withLsCodeRoLoaded lsmpl`. -/
def NoHeaderReceivedRecvHdrChunkPlacedOkXOfPrePostEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress)
    (PreEnv PostEnv : NoHeaderReceivedRecvHdrChunkGhost F → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_369 (Rust.withPanics ext))
    (blkPl_369).base
    (withLsCodeRoLoaded lsmpl
      (noHeaderReceivedRecvHdrChunkPlacedSpecOfPrePostEnv M A lim F PreEnv PostEnv))

set_option maxHeartbeats 800000 in
theorem noHeaderReceived_recv_hdr_chunk_placed_okX_of_contracts_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {PreEnv PostEnv : NoHeaderReceivedRecvHdrChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hPre : ∀ (x : NoHeaderReceivedRecvHdrChunkGhost F) (st : M.σ),
      FitsEnv M lim st (PreEnv x) → FitsEnv M lim st (NoHeaderReceivedRecvHdrChunkEnv x))
    (hPost : ∀ (x : NoHeaderReceivedRecvHdrChunkGhost F) (evs : List AllocEvent),
      NoHeaderReceivedRecvHdrChunkEnv x evs → PostEnv x evs)
    (hC : RecvHdrChunkContractsPlaced M A lim ext)
    (hadd_ok : subroutine_ok (lsProg_369 (Rust.withPanics ext))
      (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (hdec_ok : PolyDecodedMessagePlacedOkX M A lim ext)
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym (libcruxHmacBudgetSpec F M A lim)) :
    NoHeaderReceivedRecvHdrChunkPlacedOkXOfPrePostEnv M A lim F PreEnv PostEnv ext := by
  unfold NoHeaderReceivedRecvHdrChunkPlacedOkXOfPrePostEnv
  refine subroutine_ok_withLsCodeRoLoaded_rodata'
    (roSym := hdrLabelSym) (roBytes := Authenticator.hdrLabel) (by decide +kernel) ?_
  dsimp only [noHeaderReceivedRecvHdrChunkPlacedSpecOfPrePostEnv, lsProg_369]
  wpp_init p s0
  rcases p with ⟨x, st0⟩
  dsimp only at *
  have hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true := by assumption
  have hinv0 : LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have hsort0 : PolyDecoderStrictSorted x.self.receiving_hdr := by assumption
  have hfits0 : FitsEnv M lim st0 (PreEnv x) := by assumption
  have hx0_0 : s0.readReg64 .x0 = x.outA := by simp only [wp_norm, arm64_norm, *]
  have hx1_0 : s0.readReg64 .x1 = x.selfA := by simp only [wp_norm, arm64_norm, *]
  have hx2_0 : s0.readReg64 .x2 = x.epoch := by simp only [wp_norm, arm64_norm, *]
  have hx3_0 : s0.readReg64 .x3 = x.chunkA := by simp only [wp_norm, arm64_norm, *]
  change SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) s0
    (recvHdrChunkPlacedRoAt ∗
      memRegion x.outA chunkedHeaderReceivedSize ∗
      chunkedNoHeaderReceivedAt A.repAlloc x.selfA x.self ∗
      chunkAt x.chunkA x.chunk ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool lim st0 s0 ∗
      stackAt s0.sp noHeaderReceivedRecvHdrChunkStackX)
    (recvHdrChunkPlacedPostQOfPrePostEnv M A lim F PreEnv PostEnv x st0 s0 R)
    (recvHdrChunkPlacedPostQp F x s0 R)
  refine recv_hdr_chunk_part1_placed_wpp_ofPrePostEnv hC hadd_ok hdec_ok x st0 s0 R
    (hPre x st0) (hPost x) hfits0 hsort0 hpc hrun hsp_s0 hinv0 hx0_0 hx1_0 hx2_0 hx3_0
    (fun st2 receivingHdr hdrFull cap_hdrFull ptr_hdrFull ptr_mac ptr_hdr c1 c2 g_auth0
      eAdd eDec hepoch hadd _hsort hdec hge64 hlt_max hptr_hdr _heAdd _heDec hfits_hmac hpost_free
      hpc2 hrun2 hsp2 htr2 hvregs2 hinv2
      hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx29_2 => ?_)
  let st_cur1 := M.stepEvents (eAdd ++ eDec ++ recvHdrChunkAllocMacHdrEvents hdrFull.length) st0
  refine SepWPp.frame_call
    (recvHdrChunkPlacedRoAt ∗
      (ptr_hdr ↦ₛ hdrFull.take 64) ∗
      authenticatorHeapAt A.repAlloc g_auth0 x.self.uc.auth ∗
      ((s0.sp - 1640#64) ↦₆₄ c1) ∗
      ((s0.sp - 1632#64) ↦₆₄ c2) ∗
      ((s0.sp - 1584#64) ↦₆₄ g_auth0.macKey.ptr) ∗
      ((s0.sp - 1576#64) ↦₆₄ BitVec.ofNat 64 x.self.uc.auth.macKey.length) ∗
      memRegion (s0.sp - 192#64) 24 ∗
      memRegion (s0.sp - 168#64) 48 ∗
      memRegion (s0.sp - 120#64) 8 ∗
      A.pool lim st_cur1 st2 ∗
      stackAt (s0.sp - 1648#64) extHookStack)
    (by sep_focus) (by repeat rw [sepConj_assoc])
    (recv_hdr_chunk_hmac_placed_wpp_ofPrePostEnv hC hhmac x receivingHdr hdrFull
      cap_hdrFull ptr_hdrFull ptr_mac ptr_hdr c1 c2 g_auth0 st0 st_cur1 s0 st2 _ R
      hepoch hadd hdec hge64 hfits_hmac
      hpc2 hrun2 hsp2 hsp_s0 htr2 hvregs2 hinv2
      hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx29_2
      (fun st3 evs_md hfree_md hmk_lt32 hpc3 hrun3 hsp3 htr3 hvregs3 hinv3
        hx19_3 hx20_3 hx21_3 hx22_3 _hx23_3 hx24_3 hx25_3 hx26_3 _hx27_3 hx29_3 => ?_))
  let st_cur2 := M.stepEvents (recvHdrChunkHmacEvents ++ evs_md) st_cur1
  refine SepWPp.frame_call
    (vecU8 A.repAlloc (s0.sp - 168#64)
        (x.self.uc.auth.macHdrUnchecked F x.epoch (hdrFull.take 64)) ∗
      memRegion (s0.sp - 144#64) 24 ∗
      vecBufAt A.repAlloc (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
      A.pool lim st_cur2 st3 ∗
      stackAt (s0.sp - 1648#64) extHookStack)
    (by sep_focus) (by repeat rw [sepConj_assoc])
    (recv_hdr_chunk_mac_compare_placed_wpp_ofPrePostEnv hC x receivingHdr hdrFull ptr_mac
      st0 st_cur2 s0 st3 _ R hepoch hadd hdec hge64 hlt_max hmk_lt32
      hpc3 hrun3 hsp3 hsp_s0 htr3 hvregs3 hinv3
      hx21_3 hx22_3 hx26_3 hx29_3
      (fun st4 evs_tag hfree_tag hle32 hcmp hpc4 hrun4 hsp4 htr4 hvregs4 hinv4
        hx19_4 hx20_4 _ hx22_4 hx23_4 _ hx25_4 _ _ => ?_)
      (fun st4 evs_tag hfree_tag hle32 hcmp_f hpc4 hrun4 hsp4 htr4 hvregs4 hinv4
        hx19_4 hx20_4 _ hx22_4 hx23_4 hx24_4 hx25_4 _ _ => ?_))
  · let evs_pre :=
      (eAdd ++ eDec ++ recvHdrChunkAllocMacHdrEvents hdrFull.length ++ recvHdrChunkHmacEvents) ++
        (evs_md ++ evs_tag)
    have hst_cur3 : M.stepEvents evs_tag st_cur2 = M.stepEvents evs_pre st0 := by
      dsimp only [st_cur2, st_cur1, evs_pre]
      rw [← M.stepEvents_append, ← M.stepEvents_append]
      exact congrArg (fun l => M.stepEvents l st0) (by simp only [List.append_assoc])
    have hpost_cur3 :
        ∀ evs_free : List AllocEvent, FreeOnlyEvs evs_free → PostEnv x (evs_pre ++ evs_free) := by
      intro evs_free hf
      dsimp only [evs_pre]
      rw [List.append_assoc]
      exact hpost_free _ (FreeOnlyEvs.append (FreeOnlyEvs.append hfree_md hfree_tag) hf)
    have hres_err := recv_hdr_chunk_eq_macVerifyFailed x.self x.epoch x.chunk
      receivingHdr hdrFull hepoch hadd hdec hge64 hmk_lt32 hle32 hcmp
    exact SepWPp.rw_pre (by sep_ac_rfl)
      (recv_hdr_chunk_err_epilogue_placed_wpp_ofPrePostEnv hC x receivingHdr hdrFull
        cap_hdrFull ptr_hdrFull ptr_mac ptr_hdr
        0#64 x.epoch (BitVec.ofNat 64 x.self.uc.auth.rootKey.length)
        g_auth0.macKey.ptr (BitVec.ofNat 64 x.self.uc.auth.macKey.length)
        x.self.uc.epoch x.epoch g_auth0
        st0 (M.stepEvents evs_tag st_cur2) evs_pre s0 st4 R
        hst_cur3 hpost_cur3 hres_err hge64 hlt_max hptr_hdr
        hpc4 hrun4 hsp4 hsp_s0 htr4 hvregs4 hinv4
        (hx19_4.trans hx19_3) (hx20_4.trans hx20_3) hx22_4 hx23_4 (hx25_4.trans hx25_3))
  · let evs_pre :=
      (eAdd ++ eDec ++ recvHdrChunkAllocMacHdrEvents hdrFull.length ++ recvHdrChunkHmacEvents) ++
        (evs_md ++ evs_tag)
    have hst_cur3 : M.stepEvents evs_tag st_cur2 = M.stepEvents evs_pre st0 := by
      dsimp only [st_cur2, st_cur1, evs_pre]
      rw [← M.stepEvents_append, ← M.stepEvents_append]
      exact congrArg (fun l => M.stepEvents l st0) (by simp only [List.append_assoc])
    have hpost_cur3 :
        ∀ evs_free : List AllocEvent, FreeOnlyEvs evs_free → PostEnv x (evs_pre ++ evs_free) := by
      intro evs_free hf
      dsimp only [evs_pre]
      rw [List.append_assoc]
      exact hpost_free _ (FreeOnlyEvs.append (FreeOnlyEvs.append hfree_md hfree_tag) hf)
    have hres_ok := recv_hdr_chunk_eq_ok_done x.self x.epoch x.chunk
      receivingHdr hdrFull hepoch hadd hdec hge64 hmk_lt32 hle32 hcmp_f
    exact SepWPp.rw_pre (by sep_ac_rfl)
      (recv_hdr_chunk_ok_epilogue_placed_wpp_ofPrePostEnv hC x g_auth0 receivingHdr hdrFull
        cap_hdrFull ptr_hdrFull ptr_hdr ptr_mac
        0#64 g_auth0.macKey.ptr x.epoch x.self.uc.epoch x.epoch
        st0 (M.stepEvents evs_tag st_cur2) evs_pre s0 st4 R
        hst_cur3 hpost_cur3 hres_ok hptr_hdr hge64 hlt_max
        hpc4 hrun4 hsp4 hsp_s0 htr4 hvregs4 hinv4
        (hx19_4.trans hx19_3) (hx20_4.trans hx20_3) hx22_4 hx23_4
        (hx24_4.trans hx24_3) (hx25_4.trans hx25_3))

theorem noHeaderReceived_recv_hdr_chunk_placed_okX_of_contracts_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {Env : NoHeaderReceivedRecvHdrChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hPre : ∀ (x : NoHeaderReceivedRecvHdrChunkGhost F) (st : M.σ),
      FitsEnv M lim st (Env x) → FitsEnv M lim st (NoHeaderReceivedRecvHdrChunkEnv x))
    (hPost : ∀ (x : NoHeaderReceivedRecvHdrChunkGhost F) (evs : List AllocEvent),
      NoHeaderReceivedRecvHdrChunkEnv x evs → Env x evs)
    (hC : RecvHdrChunkContractsPlaced M A lim ext)
    (hadd_ok : subroutine_ok (lsProg_369 (Rust.withPanics ext))
      (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (hdec_ok : PolyDecodedMessagePlacedOkX M A lim ext)
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym (libcruxHmacBudgetSpec F M A lim)) :
    NoHeaderReceivedRecvHdrChunkPlacedOkXOfEnv M A lim F Env ext :=
  noHeaderReceived_recv_hdr_chunk_placed_okX_of_contracts_ofPrePostEnv
    hPre hPost hC hadd_ok hdec_ok hhmac

theorem noHeaderReceived_recv_hdr_chunk_placed_okX_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hC : RecvHdrChunkContractsPlaced M A lim ext)
    (hadd_ok : subroutine_ok (lsProg_369 (Rust.withPanics ext))
      (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (hdec_ok : PolyDecodedMessagePlacedOkX M A lim ext)
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym (libcruxHmacBudgetSpec F M A lim)) :
    NoHeaderReceivedRecvHdrChunkPlacedOkX M A lim F ext :=
  noHeaderReceived_recv_hdr_chunk_placed_okX_of_contracts_ofEnv
    (fun _ _ h => h) (fun _ _ h => h) hC hadd_ok hdec_ok hhmac

/-- Two-envelope (`PreEnv` / `PostEnv`) relocatable `[LibsignalPlacement]` contract for
    `<NoHeaderReceived>::recv_hdr_chunk` (Block `369`) taking `add_chunk` already transferred onto
    `lsProg_369 (Rust.withPanics ext)`. -/
theorem noHeaderReceived_recv_hdr_chunk_placed_okX_of_prog_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {PreEnv PostEnv : NoHeaderReceivedRecvHdrChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hPre : ∀ (x : NoHeaderReceivedRecvHdrChunkGhost F) (st : M.σ),
      FitsEnv M lim st (PreEnv x) → FitsEnv M lim st (NoHeaderReceivedRecvHdrChunkEnv x))
    (hPost : ∀ (x : NoHeaderReceivedRecvHdrChunkGhost F) (evs : List AllocEvent),
      NoHeaderReceivedRecvHdrChunkEnv x evs → PostEnv x evs)
    (hadd : subroutine_ok (lsProg_369 (Rust.withPanics ext))
      (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (hdec : PolyDecodedMessagePlacedOkX M A lim ext)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym framelessMemcpyAcpSpec)
    (hRO : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionROSpec)
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym (libcruxHmacBudgetSpec F M A lim))
    (h_handle_error : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (h_assert_failed : (Rust.withPanics ext) assertFailedRecvHdrSym = some Rust.panicked)
    (h_slice_index_fail : (Rust.withPanics ext) sliceIndexFailRecvHdrSym = some Rust.panicked)
    (h_panic_bounds_check : (Rust.withPanics ext) panicBoundsCheckRecvHdrSym = some Rust.panicked) :
    NoHeaderReceivedRecvHdrChunkPlacedOkXOfPrePostEnv M A lim F PreEnv PostEnv ext :=
  noHeaderReceived_recv_hdr_chunk_placed_okX_of_contracts_ofPrePostEnv hPre hPost
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

theorem noHeaderReceived_recv_hdr_chunk_placed_okX_of_prog_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {Env : NoHeaderReceivedRecvHdrChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hPre : ∀ (x : NoHeaderReceivedRecvHdrChunkGhost F) (st : M.σ),
      FitsEnv M lim st (Env x) → FitsEnv M lim st (NoHeaderReceivedRecvHdrChunkEnv x))
    (hPost : ∀ (x : NoHeaderReceivedRecvHdrChunkGhost F) (evs : List AllocEvent),
      NoHeaderReceivedRecvHdrChunkEnv x evs → Env x evs)
    (hadd : subroutine_ok (lsProg_369 (Rust.withPanics ext))
      (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (hdec : PolyDecodedMessagePlacedOkX M A lim ext)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym framelessMemcpyAcpSpec)
    (hRO : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionROSpec)
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym (libcruxHmacBudgetSpec F M A lim))
    (h_handle_error : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (h_assert_failed : (Rust.withPanics ext) assertFailedRecvHdrSym = some Rust.panicked)
    (h_slice_index_fail : (Rust.withPanics ext) sliceIndexFailRecvHdrSym = some Rust.panicked)
    (h_panic_bounds_check : (Rust.withPanics ext) panicBoundsCheckRecvHdrSym = some Rust.panicked) :
    NoHeaderReceivedRecvHdrChunkPlacedOkXOfEnv M A lim F Env ext :=
  noHeaderReceived_recv_hdr_chunk_placed_okX_of_prog_ofPrePostEnv hPre hPost
    hadd hdec hshim halloc hdealloc hmemcpy hRO hhmac
    h_handle_error h_assert_failed h_slice_index_fail h_panic_bounds_check

/-- Relocatable `[LibsignalPlacement]` budget contract for `<NoHeaderReceived>::recv_hdr_chunk`
    (Block `369`) taking `add_chunk` already transferred onto `lsProg_369 (Rust.withPanics ext)`. -/
theorem noHeaderReceived_recv_hdr_chunk_placed_okX_of_prog [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hadd : subroutine_ok (lsProg_369 (Rust.withPanics ext))
      (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (hdec : PolyDecodedMessagePlacedOkX M A lim ext)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym framelessMemcpyAcpSpec)
    (hRO : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionROSpec)
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym (libcruxHmacBudgetSpec F M A lim))
    (h_handle_error : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (h_assert_failed : (Rust.withPanics ext) assertFailedRecvHdrSym = some Rust.panicked)
    (h_slice_index_fail : (Rust.withPanics ext) sliceIndexFailRecvHdrSym = some Rust.panicked)
    (h_panic_bounds_check : (Rust.withPanics ext) panicBoundsCheckRecvHdrSym = some Rust.panicked) :
    NoHeaderReceivedRecvHdrChunkPlacedOkX M A lim F ext :=
  noHeaderReceived_recv_hdr_chunk_placed_okX_of_prog_ofEnv
    (fun _ _ h => h) (fun _ _ h => h)
    hadd hdec hshim halloc hdealloc hmemcpy hRO hhmac
    h_handle_error h_assert_failed h_slice_index_fail h_panic_bounds_check

theorem noHeaderReceived_recv_hdr_chunk_placed_okX_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {PreEnv PostEnv : NoHeaderReceivedRecvHdrChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hPre : ∀ (x : NoHeaderReceivedRecvHdrChunkGhost F) (st : M.σ),
      FitsEnv M lim st (PreEnv x) → FitsEnv M lim st (NoHeaderReceivedRecvHdrChunkEnv x))
    (hPost : ∀ (x : NoHeaderReceivedRecvHdrChunkGhost F) (evs : List AllocEvent),
      NoHeaderReceivedRecvHdrChunkEnv x evs → PostEnv x evs)
    (hadd : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (blkPl_419).base (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (hdec : PolyDecodedMessagePlacedOkX M A lim ext)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym framelessMemcpyAcpSpec)
    (hRO : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionROSpec)
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym (libcruxHmacBudgetSpec F M A lim))
    (h_handle_error : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (h_assert_failed : (Rust.withPanics ext) assertFailedRecvHdrSym = some Rust.panicked)
    (h_slice_index_fail : (Rust.withPanics ext) sliceIndexFailRecvHdrSym = some Rust.panicked)
    (h_panic_bounds_check : (Rust.withPanics ext) panicBoundsCheckRecvHdrSym = some Rust.panicked) :
    NoHeaderReceivedRecvHdrChunkPlacedOkXOfPrePostEnv M A lim F PreEnv PostEnv ext :=
  noHeaderReceived_recv_hdr_chunk_placed_okX_of_prog_ofPrePostEnv hPre hPost
    (ls_subroutine_ok_of_block (callerProg := lsProg_369 (Rust.withPanics ext))
      (i := 369) (j := 419) hadd)
    hdec hshim halloc hdealloc hmemcpy hRO hhmac
    h_handle_error h_assert_failed h_slice_index_fail h_panic_bounds_check

theorem noHeaderReceived_recv_hdr_chunk_placed_okX_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {Env : NoHeaderReceivedRecvHdrChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hPre : ∀ (x : NoHeaderReceivedRecvHdrChunkGhost F) (st : M.σ),
      FitsEnv M lim st (Env x) → FitsEnv M lim st (NoHeaderReceivedRecvHdrChunkEnv x))
    (hPost : ∀ (x : NoHeaderReceivedRecvHdrChunkGhost F) (evs : List AllocEvent),
      NoHeaderReceivedRecvHdrChunkEnv x evs → Env x evs)
    (hadd : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (blkPl_419).base (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (hdec : PolyDecodedMessagePlacedOkX M A lim ext)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym framelessMemcpyAcpSpec)
    (hRO : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionROSpec)
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym (libcruxHmacBudgetSpec F M A lim))
    (h_handle_error : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (h_assert_failed : (Rust.withPanics ext) assertFailedRecvHdrSym = some Rust.panicked)
    (h_slice_index_fail : (Rust.withPanics ext) sliceIndexFailRecvHdrSym = some Rust.panicked)
    (h_panic_bounds_check : (Rust.withPanics ext) panicBoundsCheckRecvHdrSym = some Rust.panicked) :
    NoHeaderReceivedRecvHdrChunkPlacedOkXOfEnv M A lim F Env ext :=
  noHeaderReceived_recv_hdr_chunk_placed_okX_ofPrePostEnv hPre hPost
    hadd hdec hshim halloc hdealloc hmemcpy hRO hhmac
    h_handle_error h_assert_failed h_slice_index_fail h_panic_bounds_check

/-- Top-level relocatable `[LibsignalPlacement]` budget contract for
    `<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk` (Block `369`). -/
theorem noHeaderReceived_recv_hdr_chunk_placed_okX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hadd : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (blkPl_419).base (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (hdec : PolyDecodedMessagePlacedOkX M A lim ext)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym framelessMemcpyAcpSpec)
    (hRO : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionROSpec)
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym (libcruxHmacBudgetSpec F M A lim))
    (h_handle_error : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (h_assert_failed : (Rust.withPanics ext) assertFailedRecvHdrSym = some Rust.panicked)
    (h_slice_index_fail : (Rust.withPanics ext) sliceIndexFailRecvHdrSym = some Rust.panicked)
    (h_panic_bounds_check : (Rust.withPanics ext) panicBoundsCheckRecvHdrSym = some Rust.panicked) :
    NoHeaderReceivedRecvHdrChunkPlacedOkX M A lim F ext :=
  noHeaderReceived_recv_hdr_chunk_placed_okX_ofEnv
    (fun _ _ h => h) (fun _ _ h => h)
    hadd hdec hshim halloc hdealloc hmemcpy hRO hhmac
    h_handle_error h_assert_failed h_slice_index_fail h_panic_bounds_check

end LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkProofPlacedBudget
