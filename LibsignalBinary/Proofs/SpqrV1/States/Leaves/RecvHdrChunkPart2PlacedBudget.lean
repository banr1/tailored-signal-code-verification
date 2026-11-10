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
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlaced
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp

/-!
# `<NoHeaderReceived>::recv_hdr_chunk` (Block `369`) — Budget-Threaded Part 2

Budget-threaded `[LibsignalPlacement]` proofs on `lsProg_369 (Rust.withPanics ext)` for
`polyDecoderNew1152` initialization (`recv_hdr_chunk_init_dec_placed_wpp`, offsets `320 .. 564`)
and the combined entry prefix (`recv_hdr_chunk_part1_placed_wpp`, offsets `0 .. 564`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart2PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalPlacement blkPC_369 blkPl_369 lsProg_369 lsmpl lsρ withLsCodeLoaded)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded extHookStack keys_ls_subroutine_ok_of_block_cro withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Keys
  (SepWPp.rw_pre)
open CryptoVerification.LibsignalSpqrV1
  (Bytes PolyDecoder optKeyBytesAt spqrAuthApi spqrPolyApi)
open CryptoVerification.SpqrV1.Alloc
  (spqrMemcpySym)
open CryptoVerification.SpqrV1.Auth
  (AuthenticatorGhost toBEBytes_8_length vecBufAt)
open CryptoVerification.SpqrV1.Auth.NewFacts
  (authenticatorHeapAt)
open CryptoVerification.SpqrV1.ChainProofs
  (bytesAt_false bytesAt_true)
open CryptoVerification.SpqrV1.Drop
  (chunkedNoHeaderReceivedAt)
open CryptoVerification.SpqrV1.GF.Mul2U16
  (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
  (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly
  (chunkAt polyDecoderAt)
open CryptoVerification.SpqrV1.Poly.AddChunk
  (PolyDecoderStrictSorted addChunkStackX addChunkTotal addChunk_eq_ok)
open CryptoVerification.SpqrV1.Poly.DecodedMessage
  (decodedMessageTotal decodedMessage_eq_ok)
open CryptoVerification.SpqrV1.States.Leaves
  (of_sepWP_lscro subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded)
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
  (NoHeaderReceivedRecvHdrChunkGhost addWithCarry64_sub_64_n
   cells11_sp_1648_expand cells11_sp_1648_fold cells12_sp_96_expand_hdr
   chunkedHeaderReceivedSize chunkedNoHeaderReceivedSize
   ct2DeallocAt_of_cells64_drop exists_unpack64_of_length_64_hdr
   fold_none_addrs_sp_hdr hdrActiveFrameRegionsAt hdrSomeBranchFrameAt
   hdrSomeBranchFrameAt_expose memRegion_128_sp_1008 memRegion_128_sp_1136
   memRegion_128_sp_880 memRegion_24_of_sp_1160 memRegion_64_cells_hdr
   noHeaderReceivedCells_entails_memRegion_456 noHeaderReceivedRecvHdrChunkStackX
   noHeaderReceivedUcAt_expose_entails noHeaderReceivedUcAt_fold_entails
   ofNat_sub_64_eq ofNat_ult_64_of_ge ofNat_ult_64_of_lt
   optKeyBytesAt_none_sp_1160 optKeyBytesAt_some_sp_1160
   polyDecoderNew1152RawAt polyDecoderNew1152Raw_of_slots
   recv_hdr_chunk_isPanic_of_epoch_ne recv_hdr_chunk_isPanic_of_lt_64
   savedRegsAt_of_cells12_hdr sortedSetPtOf_new_sp stackAt_recvHdrChunk_split
   vecU8HeapAt_split_64)
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
  (SepWPp.frame_call cap_add_one_beq_zero_false ct2DeallocAt
   ofNat_getElem_63_false ofNat_getLsbD_63_false polyDecodedMessageStackX
   polyDecoderAt_pts_length savedRegsAt stackAt_polyDecodedMessage_eq_addChunk
   stackAt_polyDecodedMessage_eq_extHook)
open CryptoVerification.SpqrV1.States.RecvCt2Chunk.SplitBytes
  (polyDecoderSplit)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
   RustCliAllocBudget SeqEnv fitsEvents_append)
open LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget
  (AddChunkEnv AddChunkSlotsEnv addChunkSpecX)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget
  (DecodedMessageEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkDefsPlacedBudget
  (NoHeaderReceivedRecvHdrChunkEnv RecvHdrChunkTailEnv
   recvHdrChunkAllocMacHdrEvents recvHdrChunkHmacEvents)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart1PlacedBudget
  (RecvHdrChunkContractsPlaced allowPanic_isPanic_recvHdr_budget
   assertFailedRecvHdrSym memcpy_withStack_lscro_ok
   memcpy_withStack_placed_at_recvHdr panic_at_assert_failed_u64_placed_recvHdr
   panic_at_slice_index_fail_placed_recvHdr recvHdrChunkPlacedPostQ
   recvHdrChunkPlacedPostQOfEnv recvHdrChunkPlacedPostQOfPrePostEnv
   recvHdrChunkPlacedPostQp recvHdrChunkPlacedRoAt
   recv_hdr_chunk_alloc_mac_hdr_placed_wpp_ofPrePostEnv
   recv_hdr_chunk_none_placed_wpp_ofPrePostEnv sliceIndexFailRecvHdrSym)
open LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsPlacedBudget
  (PolyDecodedMessageEnv PolyDecodedMessagePlacedOkX polyDecodedMessagePlacedSpec)

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  addChunkTotal decodedMessageTotal DecodedMessageEnv
  CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.NoHeaderReceived.recv_hdr_chunk
attribute [local arm64_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  bytesAt_true bytesAt_false toBEBytes_8_length
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

private theorem frame_call_at {prog : Program} {ret : BitVec 64} {s : State}
    {P F_frame P' : SepProp} {Q Qp : State → SepProp → Prop}
    (T : State → SepProp)
    (hf : P = T s ∗ F_frame)
    (heq : T s ∗ F_frame = P')
    (h : SepWPp prog ret s P' Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.frame_call (T s) hf heq h

/-! ## 1. `polyDecoderNew1152` Initialization & `hdr` Copy (offsets `320 .. 564`) -/

set_option maxHeartbeats 1600000 in
theorem recv_hdr_chunk_init_dec_placed_wpp_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress}
    {PreEnv PostEnv : NoHeaderReceivedRecvHdrChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (x : NoHeaderReceivedRecvHdrChunkGhost F) (hdrFull : Bytes)
    (cap_hdrFull ptr_hdrFull ptr_mac ptr_hdr : BitVec 64)
    (st0 st_cur : M.σ)
    (s0 st : State) (F_frame R : SepProp)
    (hepoch : x.epoch = x.self.uc.epoch)
    (hge64 : 64 ≤ hdrFull.length)
    (hle_cap : hdrFull.length ≤ cap_hdrFull.toNat)
    (hmax_cap : cap_hdrFull.toNat < 2 ^ 63)
    (hptr_hdrFull : ptr_hdrFull ≠ 0#64)
    (hcap_hdrFull : cap_hdrFull ≠ 0#64)
    (hpc : st.pc = (blkPl_369).base + 320#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 1648#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx0 : st.readReg64 .x0 = ptr_hdr)
    (hx19 : st.readReg64 .x19 = x.outA)
    (hx20 : st.readReg64 .x20 = cap_hdrFull)
    (hx21 : st.readReg64 .x21 = ptr_hdrFull)
    (hx22 : st.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64))
    (hx23 : st.readReg64 .x23 = ptr_mac)
    (hx24 : st.readReg64 .x24 = x.epoch)
    (hx26 : st.readReg64 .x26 = BitVec.ofNat 64 hdrFull.length)
    (hx29 : st.readReg64 .x29 = s0.sp - 96#64)
    (hcont : ∀ (st2 : State),
      st2.pc = (blkPl_369).base + 564#64 →
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
      st2.readReg64 .x24 = x.epoch →
      st2.readReg64 .x25 = ptr_hdr →
      st2.readReg64 .x26 = BitVec.ofNat 64 hdrFull.length →
      st2.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st2
        (ct2DeallocAt A.repAlloc cap_hdrFull ptr_hdrFull ∗
          (ptr_hdr ↦ₛ hdrFull.take 64) ∗
          A.live ptr_hdr 64 1 ∗
          ((s0.sp - 1568#64) ↦₆₄ x.self.uc.epoch) ∗
          polyDecoderNew1152RawAt A.repAlloc (s0.sp - 1136#64) ∗
          memRegion (s0.sp - 736#64) 80 ∗
          ((s0.sp - 200#64) ↦₆₄ x.epoch) ∗
          memRegion (s0.sp - 192#64) 24 ∗
          memRegion (s0.sp - 168#64) 48 ∗
          memRegion (s0.sp - 120#64) 8 ∗
          memRegion (s0.sp - 112#64) 16 ∗
          A.pool lim st_cur st2 ∗
          F_frame)
        (recvHdrChunkPlacedPostQOfPrePostEnv M A lim F PreEnv PostEnv x st0 s0 R)
        (recvHdrChunkPlacedPostQp F x s0 R)) :
    SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st
      ((ptr_hdrFull ↦ₛ hdrFull.take 64) ∗
        ((ptr_hdrFull + 64#64) ↦ₛ hdrFull.drop 64) ∗
        memRegion (ptr_hdrFull + BitVec.ofNat 64 hdrFull.length) (cap_hdrFull.toNat - hdrFull.length) ∗
        A.live ptr_hdrFull cap_hdrFull.toNat 1 ∗
        memRegion ptr_hdr 64 ∗
        A.live ptr_hdr 64 1 ∗
        ((s0.sp - 1568#64) ↦₆₄ x.self.uc.epoch) ∗
        hdrSomeBranchFrameAt (s0.sp - 1648#64) ∗
        A.pool lim st_cur st ∗
        F_frame)
      (recvHdrChunkPlacedPostQOfPrePostEnv M A lim F PreEnv PostEnv x st0 s0 R)
      (recvHdrChunkPlacedPostQp F x s0 R) := by
  have hsp_norm : st.readReg64 .sp = s0.sp - 1648#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm hx0 hx19 hx20 hx21 hx22 hx23 hx24 hx26 hx29
  have htake64_len : (hdrFull.take 64).length = 64 := by rw [List.length_take]; omega
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, ha_hdr⟩ :=
    exists_unpack64_of_length_64_hdr htake64_len
  have hepoch_bne : (x.epoch != x.self.uc.epoch) = false := by simp [hepoch]
  refine SepWPp.fold (hdrSomeBranchFrameAt_expose s0.sp)
    (by sep_focus) ?_
  refine of_sepWP_lscro (mid := (blkPl_369).base + 564#64) hinv ?_
  wp_conv_pre =>
    rw [ha_hdr ptr_hdrFull, memRegion_64_cells_hdr ptr_hdr,
        memRegion_128_sp_1136 s0.sp,
        memRegion_128_sp_1008 s0.sp,
        memRegion_128_sp_880 s0.sp]
  wp_pull_exists
  wp_steps_sync_pool ((blkPl_369).base + 564#64)
  simp only [State.setMem_setMem]
  have h_ct2 :=
    ct2DeallocAt_of_cells64_drop A.repAlloc cap_hdrFull ptr_hdrFull hdrFull
      w0 w1 w2 w3 w4 w5 w6 w7 hge64 hle_cap hmax_cap hptr_hdrFull hcap_hdrFull
  rw [A.repAlloc_live] at h_ct2
  refine SepWP.fold h_ct2 (by sep_focus) ?_
  have hfold_hdr :
      (ptr_hdr ↦₆₄ w0) ∗ ((ptr_hdr + 8#64) ↦₆₄ w1) ∗
        ((ptr_hdr + 16#64) ↦₆₄ w2) ∗ ((ptr_hdr + 24#64) ↦₆₄ w3) ∗
        ((ptr_hdr + 32#64) ↦₆₄ w4) ∗ ((ptr_hdr + 40#64) ↦₆₄ w5) ∗
        ((ptr_hdr + 48#64) ↦₆₄ w6) ∗ ((ptr_hdr + 56#64) ↦₆₄ w7) ⊢
      (ptr_hdr ↦ₛ hdrFull.take 64) :=
    Entails.of_eq (ha_hdr ptr_hdr).symm
  refine SepWP.fold hfold_hdr (by sep_focus) ?_
  refine SepWP.fold (sortedSetPtOf_new_sp A.repAlloc s0.sp 1112#64 1104#64 1096#64 (by bv_kernel) (by bv_kernel)) (by sep_focus) ?_
  refine SepWP.fold (sortedSetPtOf_new_sp A.repAlloc s0.sp 1088#64 1080#64 1072#64 (by bv_kernel) (by bv_kernel)) (by sep_focus) ?_
  refine SepWP.fold (sortedSetPtOf_new_sp A.repAlloc s0.sp 1064#64 1056#64 1048#64 (by bv_kernel) (by bv_kernel)) (by sep_focus) ?_
  refine SepWP.fold (sortedSetPtOf_new_sp A.repAlloc s0.sp 1040#64 1032#64 1024#64 (by bv_kernel) (by bv_kernel)) (by sep_focus) ?_
  refine SepWP.fold (sortedSetPtOf_new_sp A.repAlloc s0.sp 1016#64 1008#64 1000#64 (by bv_kernel) (by bv_kernel)) (by sep_focus) ?_
  refine SepWP.fold (sortedSetPtOf_new_sp A.repAlloc s0.sp 992#64 984#64 976#64 (by bv_kernel) (by bv_kernel)) (by sep_focus) ?_
  refine SepWP.fold (sortedSetPtOf_new_sp A.repAlloc s0.sp 968#64 960#64 952#64 (by bv_kernel) (by bv_kernel)) (by sep_focus) ?_
  refine SepWP.fold (sortedSetPtOf_new_sp A.repAlloc s0.sp 944#64 936#64 928#64 (by bv_kernel) (by bv_kernel)) (by sep_focus) ?_
  refine SepWP.fold (sortedSetPtOf_new_sp A.repAlloc s0.sp 920#64 912#64 904#64 (by bv_kernel) (by bv_kernel)) (by sep_focus) ?_
  refine SepWP.fold (sortedSetPtOf_new_sp A.repAlloc s0.sp 896#64 888#64 880#64 (by bv_kernel) (by bv_kernel)) (by sep_focus) ?_
  refine SepWP.fold (sortedSetPtOf_new_sp A.repAlloc s0.sp 872#64 864#64 856#64 (by bv_kernel) (by bv_kernel)) (by sep_focus) ?_
  refine SepWP.fold (sortedSetPtOf_new_sp A.repAlloc s0.sp 848#64 840#64 832#64 (by bv_kernel) (by bv_kernel)) (by sep_focus) ?_
  refine SepWP.fold (sortedSetPtOf_new_sp A.repAlloc s0.sp 824#64 816#64 808#64 (by bv_kernel) (by bv_kernel)) (by sep_focus) ?_
  refine SepWP.fold (sortedSetPtOf_new_sp A.repAlloc s0.sp 800#64 792#64 784#64 (by bv_kernel) (by bv_kernel)) (by sep_focus) ?_
  refine SepWP.fold (sortedSetPtOf_new_sp A.repAlloc s0.sp 776#64 768#64 760#64 (by bv_kernel) (by bv_kernel)) (by sep_focus) ?_
  refine SepWP.fold (polyDecoderNew1152Raw_of_slots A.repAlloc s0.sp) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv_end
  refine SepWPp.rw_pre (by rw [← hepoch]; sep_ac_rfl)
    (hcont _
      (by wp_norm_goal) (by wp_norm_goal)
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      hinv_end
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]))

theorem recv_hdr_chunk_init_dec_placed_wpp_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress}
    {Env : NoHeaderReceivedRecvHdrChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (x : NoHeaderReceivedRecvHdrChunkGhost F) (hdrFull : Bytes)
    (cap_hdrFull ptr_hdrFull ptr_mac ptr_hdr : BitVec 64)
    (st0 st_cur : M.σ)
    (s0 st : State) (F_frame R : SepProp)
    (hepoch : x.epoch = x.self.uc.epoch)
    (hge64 : 64 ≤ hdrFull.length)
    (hle_cap : hdrFull.length ≤ cap_hdrFull.toNat)
    (hmax_cap : cap_hdrFull.toNat < 2 ^ 63)
    (hptr_hdrFull : ptr_hdrFull ≠ 0#64)
    (hcap_hdrFull : cap_hdrFull ≠ 0#64)
    (hpc : st.pc = (blkPl_369).base + 320#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 1648#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx0 : st.readReg64 .x0 = ptr_hdr)
    (hx19 : st.readReg64 .x19 = x.outA)
    (hx20 : st.readReg64 .x20 = cap_hdrFull)
    (hx21 : st.readReg64 .x21 = ptr_hdrFull)
    (hx22 : st.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64))
    (hx23 : st.readReg64 .x23 = ptr_mac)
    (hx24 : st.readReg64 .x24 = x.epoch)
    (hx26 : st.readReg64 .x26 = BitVec.ofNat 64 hdrFull.length)
    (hx29 : st.readReg64 .x29 = s0.sp - 96#64)
    (hcont : ∀ (st2 : State),
      st2.pc = (blkPl_369).base + 564#64 →
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
      st2.readReg64 .x24 = x.epoch →
      st2.readReg64 .x25 = ptr_hdr →
      st2.readReg64 .x26 = BitVec.ofNat 64 hdrFull.length →
      st2.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st2
        (ct2DeallocAt A.repAlloc cap_hdrFull ptr_hdrFull ∗
          (ptr_hdr ↦ₛ hdrFull.take 64) ∗
          A.live ptr_hdr 64 1 ∗
          ((s0.sp - 1568#64) ↦₆₄ x.self.uc.epoch) ∗
          polyDecoderNew1152RawAt A.repAlloc (s0.sp - 1136#64) ∗
          memRegion (s0.sp - 736#64) 80 ∗
          ((s0.sp - 200#64) ↦₆₄ x.epoch) ∗
          memRegion (s0.sp - 192#64) 24 ∗
          memRegion (s0.sp - 168#64) 48 ∗
          memRegion (s0.sp - 120#64) 8 ∗
          memRegion (s0.sp - 112#64) 16 ∗
          A.pool lim st_cur st2 ∗
          F_frame)
        (recvHdrChunkPlacedPostQOfEnv M A lim F Env x st0 s0 R)
        (recvHdrChunkPlacedPostQp F x s0 R)) :
    SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st
      ((ptr_hdrFull ↦ₛ hdrFull.take 64) ∗
        ((ptr_hdrFull + 64#64) ↦ₛ hdrFull.drop 64) ∗
        memRegion (ptr_hdrFull + BitVec.ofNat 64 hdrFull.length) (cap_hdrFull.toNat - hdrFull.length) ∗
        A.live ptr_hdrFull cap_hdrFull.toNat 1 ∗
        memRegion ptr_hdr 64 ∗
        A.live ptr_hdr 64 1 ∗
        ((s0.sp - 1568#64) ↦₆₄ x.self.uc.epoch) ∗
        hdrSomeBranchFrameAt (s0.sp - 1648#64) ∗
        A.pool lim st_cur st ∗
        F_frame)
      (recvHdrChunkPlacedPostQOfEnv M A lim F Env x st0 s0 R)
      (recvHdrChunkPlacedPostQp F x s0 R) :=
  recv_hdr_chunk_init_dec_placed_wpp_ofPrePostEnv x hdrFull cap_hdrFull ptr_hdrFull ptr_mac ptr_hdr
    st0 st_cur s0 st F_frame R hepoch hge64 hle_cap hmax_cap hptr_hdrFull hcap_hdrFull
    hpc hrun hsp hsp_s0 htr hvregs hinv hx0 hx19 hx20 hx21 hx22 hx23 hx24 hx26 hx29 hcont

theorem recv_hdr_chunk_init_dec_placed_wpp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress}
    {ext : String → Option (State → State)}
    (x : NoHeaderReceivedRecvHdrChunkGhost F) (hdrFull : Bytes)
    (cap_hdrFull ptr_hdrFull ptr_mac ptr_hdr : BitVec 64)
    (st0 st_cur : M.σ)
    (s0 st : State) (F_frame R : SepProp)
    (hepoch : x.epoch = x.self.uc.epoch)
    (hge64 : 64 ≤ hdrFull.length)
    (hle_cap : hdrFull.length ≤ cap_hdrFull.toNat)
    (hmax_cap : cap_hdrFull.toNat < 2 ^ 63)
    (hptr_hdrFull : ptr_hdrFull ≠ 0#64)
    (hcap_hdrFull : cap_hdrFull ≠ 0#64)
    (hpc : st.pc = (blkPl_369).base + 320#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 1648#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx0 : st.readReg64 .x0 = ptr_hdr)
    (hx19 : st.readReg64 .x19 = x.outA)
    (hx20 : st.readReg64 .x20 = cap_hdrFull)
    (hx21 : st.readReg64 .x21 = ptr_hdrFull)
    (hx22 : st.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64))
    (hx23 : st.readReg64 .x23 = ptr_mac)
    (hx24 : st.readReg64 .x24 = x.epoch)
    (hx26 : st.readReg64 .x26 = BitVec.ofNat 64 hdrFull.length)
    (hx29 : st.readReg64 .x29 = s0.sp - 96#64)
    (hcont : ∀ (st2 : State),
      st2.pc = (blkPl_369).base + 564#64 →
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
      st2.readReg64 .x24 = x.epoch →
      st2.readReg64 .x25 = ptr_hdr →
      st2.readReg64 .x26 = BitVec.ofNat 64 hdrFull.length →
      st2.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st2
        (ct2DeallocAt A.repAlloc cap_hdrFull ptr_hdrFull ∗
          (ptr_hdr ↦ₛ hdrFull.take 64) ∗
          A.live ptr_hdr 64 1 ∗
          ((s0.sp - 1568#64) ↦₆₄ x.self.uc.epoch) ∗
          polyDecoderNew1152RawAt A.repAlloc (s0.sp - 1136#64) ∗
          memRegion (s0.sp - 736#64) 80 ∗
          ((s0.sp - 200#64) ↦₆₄ x.epoch) ∗
          memRegion (s0.sp - 192#64) 24 ∗
          memRegion (s0.sp - 168#64) 48 ∗
          memRegion (s0.sp - 120#64) 8 ∗
          memRegion (s0.sp - 112#64) 16 ∗
          A.pool lim st_cur st2 ∗
          F_frame)
        (recvHdrChunkPlacedPostQ M A lim F x st0 s0 R)
        (recvHdrChunkPlacedPostQp F x s0 R)) :
    SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st
      ((ptr_hdrFull ↦ₛ hdrFull.take 64) ∗
        ((ptr_hdrFull + 64#64) ↦ₛ hdrFull.drop 64) ∗
        memRegion (ptr_hdrFull + BitVec.ofNat 64 hdrFull.length) (cap_hdrFull.toNat - hdrFull.length) ∗
        A.live ptr_hdrFull cap_hdrFull.toNat 1 ∗
        memRegion ptr_hdr 64 ∗
        A.live ptr_hdr 64 1 ∗
        ((s0.sp - 1568#64) ↦₆₄ x.self.uc.epoch) ∗
        hdrSomeBranchFrameAt (s0.sp - 1648#64) ∗
        A.pool lim st_cur st ∗
        F_frame)
      (recvHdrChunkPlacedPostQ M A lim F x st0 s0 R)
      (recvHdrChunkPlacedPostQp F x s0 R) :=
  recv_hdr_chunk_init_dec_placed_wpp_ofEnv x hdrFull cap_hdrFull ptr_hdrFull ptr_mac ptr_hdr
    st0 st_cur s0 st F_frame R hepoch hge64 hle_cap hmax_cap hptr_hdrFull hcap_hdrFull
    hpc hrun hsp hsp_s0 htr hvregs hinv hx0 hx19 hx20 hx21 hx22 hx23 hx24 hx26 hx29 hcont

/-! ## 2. Combined Part 1 (offsets `0 .. 564`) -/

set_option maxHeartbeats 2000000 in
theorem recv_hdr_chunk_part1_placed_wpp_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress}
    {PreEnv PostEnv : NoHeaderReceivedRecvHdrChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hC : RecvHdrChunkContractsPlaced M A lim ext)
    (hadd_ok : subroutine_ok (lsProg_369 (Rust.withPanics ext))
      (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (hdec_ok : PolyDecodedMessagePlacedOkX M A lim ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F)
    (st0 : M.σ) (s0 : State) (R : SepProp)
    (hPre : FitsEnv M lim st0 (PreEnv x) → FitsEnv M lim st0 (NoHeaderReceivedRecvHdrChunkEnv x))
    (hPost : ∀ evs, NoHeaderReceivedRecvHdrChunkEnv x evs → PostEnv x evs)
    (hfits_pre : FitsEnv M lim st0 (PreEnv x))
    (hsort_self : PolyDecoderStrictSorted x.self.receiving_hdr)
    (hpc : s0.pc = (blkPl_369).base)
    (hrun : s0.status = .Running)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (hinv : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = x.outA)
    (hx1 : s0.readReg64 .x1 = x.selfA)
    (hx2 : s0.readReg64 .x2 = x.epoch)
    (hx3 : s0.readReg64 .x3 = x.chunkA)
    (hcont : ∀ (st2 : State) (receivingHdr : PolyDecoder) (hdrFull : Bytes)
        (cap_hdrFull ptr_hdrFull ptr_mac ptr_hdr : BitVec 64)
        (c1 c2 : BitVec 64) (g_auth0 : AuthenticatorGhost)
        (eAdd eDec : List AllocEvent)
        (_hepoch : x.epoch = x.self.uc.epoch)
        (_hadd : PolyDecoder.addChunk x.self.receiving_hdr x.chunk = .ok receivingHdr)
        (_hsort : PolyDecoderStrictSorted receivingHdr)
        (_hdec : receivingHdr.decodedMessage = .ok (some hdrFull))
        (_hge64 : 64 ≤ hdrFull.length)
        (_hlt_max : hdrFull.length < 2 ^ 63)
        (_hptr_hdr : ptr_hdr ≠ 0#64)
        (_heAdd : AddChunkSlotsEnv x.self.receiving_hdr.pts eAdd)
        (_heDec : DecodedMessageEnv receivingHdr eDec)
        (_hfits_hmac :
          FitsEvents M lim
            (M.stepEvents (eAdd ++ eDec ++ recvHdrChunkAllocMacHdrEvents hdrFull.length) st0)
            recvHdrChunkHmacEvents)
        (_hpost_free :
          ∀ evs_free, FreeOnlyEvs evs_free →
            PostEnv x
              ((eAdd ++ eDec ++ recvHdrChunkAllocMacHdrEvents hdrFull.length ++
                  recvHdrChunkHmacEvents) ++ evs_free)),
      st2.pc = (blkPl_369).base + 564#64 →
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
      st2.readReg64 .x24 = x.epoch →
      st2.readReg64 .x25 = ptr_hdr →
      st2.readReg64 .x26 = BitVec.ofNat 64 hdrFull.length →
      st2.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st2
        (recvHdrChunkPlacedRoAt ∗
          memRegion x.outA chunkedHeaderReceivedSize ∗
          memRegion x.selfA chunkedNoHeaderReceivedSize ∗
          ct2DeallocAt A.repAlloc cap_hdrFull ptr_hdrFull ∗
          (ptr_hdr ↦ₛ hdrFull.take 64) ∗
          A.live ptr_hdr 64 1 ∗
          vecBufAt A.repAlloc (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
          authenticatorHeapAt A.repAlloc g_auth0 x.self.uc.auth ∗
          ((s0.sp - 1648#64) ↦₆₄ 0#64) ∗
          ((s0.sp - 1640#64) ↦₆₄ c1) ∗
          ((s0.sp - 1632#64) ↦₆₄ c2) ∗
          ((s0.sp - 1624#64) ↦₆₄ x.epoch) ∗
          ((s0.sp - 1616#64) ↦₆₄ g_auth0.rootKey.cap) ∗
          ((s0.sp - 1608#64) ↦₆₄ g_auth0.rootKey.ptr) ∗
          ((s0.sp - 1600#64) ↦₆₄ BitVec.ofNat 64 x.self.uc.auth.rootKey.length) ∗
          ((s0.sp - 1592#64) ↦₆₄ g_auth0.macKey.cap) ∗
          ((s0.sp - 1584#64) ↦₆₄ g_auth0.macKey.ptr) ∗
          ((s0.sp - 1576#64) ↦₆₄ BitVec.ofNat 64 x.self.uc.auth.macKey.length) ∗
          ((s0.sp - 1568#64) ↦₆₄ x.self.uc.epoch) ∗
          polyDecoderAt A.repAlloc (s0.sp - 1560#64) receivingHdr ∗
          memRegion (s0.sp - 1160#64) 24 ∗
          polyDecoderNew1152RawAt A.repAlloc (s0.sp - 1136#64) ∗
          memRegion (s0.sp - 736#64) 80 ∗
          memRegion (s0.sp - 656#64) 456 ∗
          ((s0.sp - 200#64) ↦₆₄ x.epoch) ∗
          memRegion (s0.sp - 192#64) 24 ∗
          memRegion (s0.sp - 168#64) 48 ∗
          memRegion (s0.sp - 120#64) 8 ∗
          memRegion (s0.sp - 112#64) 16 ∗
          chunkAt x.chunkA x.chunk ∗
          tokenInitPlacedAt ∗
          reduceTablePlacedAt ∗
          A.pool lim
            (M.stepEvents (eAdd ++ eDec ++ recvHdrChunkAllocMacHdrEvents hdrFull.length) st0)
            st2 ∗
          memRegion (s0.sp - 18704#64) 672 ∗
          stackAt (s0.sp - 1648#64) extHookStack ∗
          savedRegsAt s0)
        (recvHdrChunkPlacedPostQOfPrePostEnv M A lim F PreEnv PostEnv x st0 s0 R)
        (recvHdrChunkPlacedPostQp F x s0 R)) :
    SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) s0
      (recvHdrChunkPlacedRoAt ∗
        memRegion x.outA chunkedHeaderReceivedSize ∗
        chunkedNoHeaderReceivedAt A.repAlloc x.selfA x.self ∗
        chunkAt x.chunkA x.chunk ∗
        tokenInitPlacedAt ∗
        reduceTablePlacedAt ∗
        A.pool lim st0 s0 ∗
        stackAt s0.sp noHeaderReceivedRecvHdrChunkStackX)
      (recvHdrChunkPlacedPostQOfPrePostEnv M A lim F PreEnv PostEnv x st0 s0 R)
      (recvHdrChunkPlacedPostQp F x s0 R) := by
  have hfits0 : FitsEnv M lim st0 (NoHeaderReceivedRecvHdrChunkEnv x) := hPre hfits_pre
  have hmc_raw := memcpy_withStack_placed_at_recvHdr hC polyDecodedMessageStackX
  have h_mc_dec := memcpy_withStack_lscro_ok (polyDecoderSplit A.repAlloc x.self.receiving_hdr)
    (by decide) polyDecodedMessageStackX hmc_raw
  have h_add : subroutine_ok ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext))
      (lsmpl.base 419) (withLsCodeRoLoaded lsmpl (addChunkSpecX M A lim)) :=
    subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hadd_ok
  have h_dec : subroutine_ok (lsProg_369 (Rust.withPanics ext))
      (lsmpl.base 418) (withLsCodeRoLoaded lsmpl (polyDecodedMessagePlacedSpec M A lim)) :=
    keys_ls_subroutine_ok_of_block_cro (i := 369) (j := 418) hdec_ok
  have h_pan_epoch := panic_at_assert_failed_u64_placed_recvHdr hC
  have h_pan_slice := panic_at_slice_index_fail_placed_recvHdr hC
  have h_none := @recv_hdr_chunk_none_placed_wpp_ofPrePostEnv _ M A lim F PreEnv PostEnv ext hC x
  have h_alloc_mac :=
    @recv_hdr_chunk_alloc_mac_hdr_placed_wpp_ofPrePostEnv _ M A lim F PreEnv PostEnv ext hC x
  have h_init_dec :=
    @recv_hdr_chunk_init_dec_placed_wpp_ofPrePostEnv _ M A lim F PreEnv PostEnv ext x
  simp only [wp_norm, arm64_norm] at hx0 hx1 hx2 hx3
  clear hmc_raw hadd_ok hdec_ok hC hPre hfits_pre
  unfold chunkedNoHeaderReceivedAt
  refine SepWPp.rw_pre (by rw [stackAt_recvHdrChunk_split s0.sp]) ?_
  unfold hdrActiveFrameRegionsAt
  refine SepWPp.rw_pre (by rw [cells12_sp_96_expand_hdr s0.sp, cells11_sp_1648_expand s0.sp]) ?_
  sep_elim_exists
  rename_i c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10
  refine SepWPp.fold
    (noHeaderReceivedUcAt_expose_entails A.repAlloc x.selfA x.self.uc) (by sep_focus) ?_
  sep_elim_exists
  rename_i g_auth0
  by_cases hepoch : x.epoch = x.self.uc.epoch
  · have hepoch_bne : (x.epoch != x.self.uc.epoch) = false := by simp [hepoch]
    have hfits_seq :
        FitsEnv M lim st0
          (SeqEnv (AddChunkSlotsEnv x.self.receiving_hdr.pts)
            (SeqEnv (DecodedMessageEnv (addChunkTotal x.self.receiving_hdr x.chunk))
              (RecvHdrChunkTailEnv
                (decodedMessageTotal (addChunkTotal x.self.receiving_hdr x.chunk))))) := by
      intro evs hevs
      apply hfits0
      unfold NoHeaderReceivedRecvHdrChunkEnv
      simp only [hepoch_bne, Bool.false_eq_true, ↓reduceIte]
      exact hevs
    have hfits_add :
        FitsEnv M lim st0
          (AddChunkEnv ⟨s0.sp - 1560#64, x.chunkA, x.self.receiving_hdr, x.chunk⟩) := by
      change FitsEnv M lim st0 (AddChunkSlotsEnv x.self.receiving_hdr.pts)
      exact fun evs hevs => hfits_seq evs (Or.inl hevs)
    refine of_sepWP_lscro (mid := lsρ spqrMemcpySym) hinv ?_
    wp_steps_sync_pool (lsρ spqrMemcpySym)
    simp only [State.setMem_setMem]
    refine SepWP.fold (savedRegsAt_of_cells12_hdr s0) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv1
    wpp_call_lscro_recvHdr_budget h_mc_dec
      (s0.sp - 1560#64, x.selfA + 56#64) hinv1
    refine CryptoVerification.SpqrV1.Auth.SepWPp.pure_left_focus _ (by sep_focus) fun hpost_mc => ?_
    rcases hpost_mc with ⟨hvm1, htr1, _⟩
    refine SepWPp.rw_pre (by rw [← A.pool_of_vmPreserved hvm1]) ?_
    refine SepWPp.fold
      (polyDecoderAt_pts_length A.repAlloc (s0.sp - 1560#64) x.self.receiving_hdr)
      (by sep_focus) ?_
    refine CryptoVerification.SpqrV1.Auth.SepWPp.pure_left_focus _ (by sep_focus) fun hpts_len => ?_
    have hadd_eq : PolyDecoder.addChunk x.self.receiving_hdr x.chunk =
        .ok (addChunkTotal x.self.receiving_hdr x.chunk) :=
      addChunk_eq_ok x.self.receiving_hdr x.chunk hpts_len
    refine of_sepWP_lscro (mid := lsmpl.base 419) hF_sf ?_
    wp_steps_sync_pool (lsmpl.base 419)
    simp only [State.setMem_setMem]
    have hstack_add :
        stackAt (s0.sp - 1648#64) polyDecodedMessageStackX =
          memRegion ((s0.sp - 1648#64) - 17056#64) 576 ∗ stackAt sf.sp addChunkStackX := by
      rw [hsp_sf, stackAt_polyDecodedMessage_eq_addChunk (s0.sp - 1648#64)]
    refine SepWP.fold (Entails.of_eq hstack_add) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv2
    wpp_call_lscro_recvHdr_budget h_add
      (⟨s0.sp - 1560#64, x.chunkA, x.self.receiving_hdr, x.chunk⟩, st0) hinv2
    apply SepWPp.exists_elim
    intro eAdd
    refine CryptoVerification.SpqrV1.Auth.SepWPp.pure_left_focus _ (by sep_focus) fun hpost_add => ?_
    rcases hpost_add with ⟨htr2, _, heAdd, hsort_add⟩
    have hfits_dec_seq :
        FitsEnv M lim (M.stepEvents eAdd st0)
          (SeqEnv (DecodedMessageEnv (addChunkTotal x.self.receiving_hdr x.chunk))
            (RecvHdrChunkTailEnv
              (decodedMessageTotal (addChunkTotal x.self.receiving_hdr x.chunk)))) :=
      fun evs2 h2 =>
        ((fitsEvents_append M lim eAdd evs2 st0).mp
          (hfits_seq (eAdd ++ evs2) (Or.inr ⟨eAdd, evs2, rfl, heAdd, h2⟩))).2
    have hfits_dec :
        FitsEnv M lim (M.stepEvents eAdd st0)
          (PolyDecodedMessageEnv
            ⟨s0.sp - 1160#64, s0.sp - 1560#64, addChunkTotal x.self.receiving_hdr x.chunk⟩) := by
      change FitsEnv M lim (M.stepEvents eAdd st0)
        (DecodedMessageEnv (addChunkTotal x.self.receiving_hdr x.chunk))
      exact fun evs hevs => hfits_dec_seq evs (Or.inl hevs)
    have hstack_add_back :
        memRegion ((s0.sp - 1648#64) - 17056#64) 576 ∗ stackAt sf.sp addChunkStackX ⊢
          stackAt sf_1.sp polyDecodedMessageStackX := by
      rw [hsp_sf_1, hsp_sf, ← stackAt_polyDecodedMessage_eq_addChunk (s0.sp - 1648#64)]
      exact Entails.refl _
    refine SepWPp.fold hstack_add_back (by sep_focus) ?_
    refine SepWPp.fold
      (polyDecoderAt_pts_length A.repAlloc (s0.sp - 1560#64)
        (addChunkTotal x.self.receiving_hdr x.chunk))
      (by sep_focus) ?_
    refine CryptoVerification.SpqrV1.Auth.SepWPp.pure_left_focus _ (by sep_focus)
      fun hpts_len_add => ?_
    have hdec_total :
        (addChunkTotal x.self.receiving_hdr x.chunk).decodedMessage =
          .ok (decodedMessageTotal (addChunkTotal x.self.receiving_hdr x.chunk)) :=
      decodedMessage_eq_ok _ hpts_len_add hsort_add
    refine of_sepWP_lscro (mid := lsmpl.base 418) hF_sf_1 ?_
    wp_steps_sync_pool (lsmpl.base 418)
    simp only [State.setMem_setMem]
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv3
    wpp_call_lscro_recvHdr_budget h_dec
      (⟨s0.sp - 1160#64, s0.sp - 1560#64,
        addChunkTotal x.self.receiving_hdr x.chunk⟩, M.stepEvents eAdd st0) hinv3
    dsimp only [LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsBudget.polyDecodedMessagePlacedSpecOfEnv]
    refine SepWPp.rw_pre
      (by simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
            wp_norm, arm64_norm]; rfl) ?_
    apply SepWPp.exists_elim
    intro eDec
    apply SepWPp.exists_elim
    intro optMsg
    refine CryptoVerification.SpqrV1.Auth.SepWPp.pure_left_focus _ (by sep_focus) fun hpost_dec => ?_
    rcases hpost_dec with ⟨hdec_eq, htr3, heDec⟩
    change DecodedMessageEnv (addChunkTotal x.self.receiving_hdr x.chunk) eDec at heDec
    have hopt_eq :
        decodedMessageTotal (addChunkTotal x.self.receiving_hdr x.chunk) = optMsg :=
      Except.ok.inj (hdec_total.symm.trans hdec_eq)
    have hfits_tail_raw :
        FitsEnv M lim (M.stepEvents eDec (M.stepEvents eAdd st0))
          (RecvHdrChunkTailEnv
            (decodedMessageTotal (addChunkTotal x.self.receiving_hdr x.chunk))) :=
      fun evs3 h3 =>
        ((fitsEvents_append M lim eDec evs3 (M.stepEvents eAdd st0)).mp
          (hfits_dec_seq (eDec ++ evs3) (Or.inr ⟨eDec, evs3, rfl, heDec, h3⟩))).2
    have hfits_tail :
        FitsEnv M lim (M.stepEvents eDec (M.stepEvents eAdd st0))
          (RecvHdrChunkTailEnv optMsg) :=
      hopt_eq ▸ hfits_tail_raw
    have hsp_sf2 : sf_2.sp = s0.sp - 1648#64 := by rw [hsp_sf_2, hsp_sf_1, hsp_sf]
    have htr_sf2 : sf_2.trace = s0.trace := by
      have htr2' : sf_1.trace = s0.trace := htr2.trans (htr1.trans (by wp_norm_goal))
      exact htr3.trans (by simp only [wp_norm, arm64_norm, htr2'])
    have hvregs_sf2 : calleeSavedVRegs sf_2 = calleeSavedVRegs s0 := by
      rw [hcs_sf_2, hcs_sf_1, hcs_sf]
    have hstack_sf1 :
        stackAt sf_1.sp polyDecodedMessageStackX ⊢
          stackAt (s0.sp - 1648#64) polyDecodedMessageStackX := by
      rw [hsp_sf_1, hsp_sf]
      exact Entails.refl _
    refine SepWPp.fold hstack_sf1 (by sep_focus) ?_
    change SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) sf_2 _
      (recvHdrChunkPlacedPostQOfPrePostEnv M A lim F PreEnv PostEnv x st0 s0 R)
      (recvHdrChunkPlacedPostQp F x s0 R)
    cases optMsg with
    | none =>
      have htail_none :
          RecvHdrChunkTailEnv
            (decodedMessageTotal (addChunkTotal x.self.receiving_hdr x.chunk)) [] :=
        hopt_eq.symm ▸ (rfl : RecvHdrChunkTailEnv none [])
      have henv_none : NoHeaderReceivedRecvHdrChunkEnv x (eAdd ++ eDec) := by
        have happ_nil : eAdd ++ eDec = eAdd ++ (eDec ++ []) := by simp only [List.append_nil]
        rw [happ_nil]
        unfold NoHeaderReceivedRecvHdrChunkEnv
        simp only [hepoch_bne, Bool.false_eq_true, ↓reduceIte]
        exact Or.inr ⟨eAdd, eDec ++ [], rfl, heAdd, Or.inr ⟨eDec, [], rfl, heDec, htail_none⟩⟩
      have hpost_none : PostEnv x (eAdd ++ eDec) := hPost (eAdd ++ eDec) henv_none
      have hst_cur_none :
          M.stepEvents eDec (M.stepEvents eAdd st0) = M.stepEvents (eAdd ++ eDec) st0 :=
        (M.stepEvents_append eAdd eDec st0).symm
      refine SepWPp.rw_pre (by rw [optKeyBytesAt_none_sp_1160 A.repAlloc s0.sp]) ?_
      refine of_sepWP_lscro (mid := (blkPl_369).base + 180#64) hF_sf_2 ?_
      wp_steps_sync_pool ((blkPl_369).base + 180#64)
      simp only [State.setMem_setMem]
      refine SepWP.fold (noHeaderReceivedUcAt_fold_entails A.repAlloc x.selfA x.self.uc g_auth0)
        (by sep_focus) ?_
      refine SepWP.fold (cells11_sp_1648_fold s0.sp _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold
        (fold_none_addrs_sp_hdr A.repAlloc s0.sp (addChunkTotal x.self.receiving_hdr x.chunk))
        (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv_none
      refine SepWPp.rw_pre (by unfold recvHdrChunkPlacedRoAt; sep_ac_rfl)
        (h_none (addChunkTotal x.self.receiving_hdr x.chunk)
          st0 (M.stepEvents eDec (M.stepEvents eAdd st0)) (eAdd ++ eDec)
          s0 _ R hst_cur_none hpost_none hepoch hadd_eq hsort_add hdec_eq
          (by wp_norm_goal) (by wp_norm_goal)
          (by simp only [wp_norm, arm64_norm, hsp_sf2])
          hsp_s0
          (by simp only [wp_norm, arm64_norm, htr_sf2])
          (by simp only [wp_norm, arm64_norm, hvregs_sf2])
          hinv_none
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *]))
    | some hdrFull =>
      refine SepWPp.fold
        (optKeyBytesAt_some_sp_1160 A.repAlloc s0.sp hdrFull) (by sep_focus) ?_
      sep_elim_exists
      rename_i cap_hdrFull ptr_hdrFull
      refine CryptoVerification.SpqrV1.Auth.SepWPp.pure_left_focus _ (by sep_focus) ?_
      rintro ⟨hle_cap, hmax_cap, hptr_hdrFull⟩
      have hlt_max : hdrFull.length < 2 ^ 63 := by omega
      have hcap_cmn : (cap_hdrFull + 1#64 == 0#64) = false := cap_add_one_beq_zero_false hmax_cap
      by_cases hge64 : 64 ≤ hdrFull.length
      · have hult64 : (BitVec.ofNat 64 hdrFull.length).ult 64#64 = false :=
          ofNat_ult_64_of_ge hge64 hlt_max
        have hsub64 : BitVec.ofNat 64 hdrFull.length - 64#64 = BitVec.ofNat 64 (hdrFull.length - 64) :=
          ofNat_sub_64_eq hge64 hlt_max
        have hmsb64 : (BitVec.ofNat 64 (hdrFull.length - 64)).getLsbD 63 = false :=
          ofNat_getLsbD_63_false (by omega)
        have hmsb64' : (BitVec.ofNat 64 (hdrFull.length - 64))[63] = false :=
          ofNat_getElem_63_false (by omega)
        have hpl64 : ConditionHolds .PL (subsPState64 (BitVec.ofNat 64 hdrFull.length) 64#64) = true := by
          simp only [ConditionHolds, subsPState64, wp_norm, arm64_norm, addWithCarry64_sub_64_n,
            hsub64, hmsb64, hmsb64']
        have hstep_ed :
            M.stepEvents eDec (M.stepEvents eAdd st0) = M.stepEvents (eAdd ++ eDec) st0 :=
          (M.stepEvents_append eAdd eDec st0).symm
        have hfits_alloc_hmac :
            FitsEvents M lim (M.stepEvents (eAdd ++ eDec) st0)
              (recvHdrChunkAllocMacHdrEvents hdrFull.length ++ recvHdrChunkHmacEvents) := by
          rw [← hstep_ed]
          have hnot_lt64 : ¬ hdrFull.length < 64 := by omega
          apply hfits_tail
          dsimp only [RecvHdrChunkTailEnv]
          simp only [hnot_lt64, ↓reduceIte]
          exact Or.inl rfl
        rcases (fitsEvents_append M lim
            (recvHdrChunkAllocMacHdrEvents hdrFull.length)
            recvHdrChunkHmacEvents
            (M.stepEvents (eAdd ++ eDec) st0)).mp hfits_alloc_hmac with
          ⟨hfits_alloc_mac, hfits_hmac_raw⟩
        have hstep_alloc :
            M.stepEvents (recvHdrChunkAllocMacHdrEvents hdrFull.length)
                (M.stepEvents (eAdd ++ eDec) st0) =
              M.stepEvents (eAdd ++ eDec ++ recvHdrChunkAllocMacHdrEvents hdrFull.length) st0 :=
          (M.stepEvents_append (eAdd ++ eDec)
            (recvHdrChunkAllocMacHdrEvents hdrFull.length) st0).symm
        have hfits_hmac :
            FitsEvents M lim
              (M.stepEvents (eAdd ++ eDec ++ recvHdrChunkAllocMacHdrEvents hdrFull.length) st0)
              recvHdrChunkHmacEvents := by
          rwa [← hstep_alloc]
        have hpost_free :
            ∀ evs_free, FreeOnlyEvs evs_free →
              PostEnv x
                ((eAdd ++ eDec ++ recvHdrChunkAllocMacHdrEvents hdrFull.length ++
                    recvHdrChunkHmacEvents) ++ evs_free) := by
          intro evs_free hfree
          apply hPost
          have htail_some :
              RecvHdrChunkTailEnv (some hdrFull)
                ((recvHdrChunkAllocMacHdrEvents hdrFull.length ++ recvHdrChunkHmacEvents) ++
                  evs_free) := by
            have hnot_lt64 : ¬ hdrFull.length < 64 := by omega
            dsimp only [RecvHdrChunkTailEnv]
            simp only [hnot_lt64, ↓reduceIte]
            exact Or.inr ⟨recvHdrChunkAllocMacHdrEvents hdrFull.length ++ recvHdrChunkHmacEvents,
              evs_free, rfl, rfl, hfree⟩
          have htail_free :
              RecvHdrChunkTailEnv (decodedMessageTotal (addChunkTotal x.self.receiving_hdr x.chunk))
                ((recvHdrChunkAllocMacHdrEvents hdrFull.length ++ recvHdrChunkHmacEvents) ++
                  evs_free) :=
            hopt_eq.symm ▸ htail_some
          have henv_raw :
              NoHeaderReceivedRecvHdrChunkEnv x
                (eAdd ++ (eDec ++
                  ((recvHdrChunkAllocMacHdrEvents hdrFull.length ++ recvHdrChunkHmacEvents) ++
                    evs_free))) := by
            unfold NoHeaderReceivedRecvHdrChunkEnv
            simp only [hepoch_bne, Bool.false_eq_true, ↓reduceIte]
            exact Or.inr ⟨eAdd, _, rfl, heAdd, Or.inr ⟨eDec, _, rfl, heDec, htail_free⟩⟩
          simpa only [List.append_assoc] using henv_raw
        refine SepWPp.rw_pre (by rw [hstep_ed]) ?_
        have h_vsplit := vecU8HeapAt_split_64 A.repAlloc cap_hdrFull ptr_hdrFull hdrFull hge64
        rw [A.repAlloc_live] at h_vsplit
        refine SepWPp.fold h_vsplit (by sep_focus) ?_
        refine CryptoVerification.SpqrV1.Auth.SepWPp.pure_left_focus _ (by sep_focus) ?_
        rintro ⟨_, _, _, hcap_hdrFull⟩
        refine SepWPp.fold
          (noHeaderReceivedCells_entails_memRegion_456 x.selfA _ _ _ _ _ _ _)
          (by sep_focus) ?_
        refine of_sepWP_lscro (mid := (blkPl_369).base + 252#64) hF_sf_2 ?_
        wp_steps_sync_pool ((blkPl_369).base + 252#64)
        simp only [State.setMem_setMem]
        refine SepWP.fold (Entails.of_eq (stackAt_polyDecodedMessage_eq_extHook (s0.sp - 1648#64)))
          (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hinv_some
        refine frame_call_at
          (fun s_252 =>
            ((s0.sp - 1152#64) ↦₆₄ ptr_hdrFull) ∗
              ((ptr_hdrFull + 64#64) ↦ₛ hdrFull.drop 64) ∗
              A.pool lim (M.stepEvents (eAdd ++ eDec) st0) s_252 ∗
              stackAt (s0.sp - 1648#64) extHookStack)
          (by sep_focus)
          (by repeat rw [sepConj_assoc])
          (h_alloc_mac hdrFull cap_hdrFull ptr_hdrFull
            st0 (M.stepEvents (eAdd ++ eDec) st0) s0 _ _ R
            hge64 hlt_max hfits_alloc_mac
            (by wp_norm_goal) (by wp_norm_goal)
            (by simp only [wp_norm, arm64_norm, hsp_sf2])
            hsp_s0
            (by simp only [wp_norm, arm64_norm, htr_sf2])
            (by simp only [wp_norm, arm64_norm, hvregs_sf2])
            hinv_some
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, hsub64, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (fun st' ptr_mac ptr_hdr hptr_hdr hpc' hrun' hsp' htr' hvregs' hinv'
              hx0' hx19' hx20' hx21' hx22' hx23' hx24' hx26' hx29' => ?_))
        refine SepWPp.rw_pre (by rw [hstep_alloc]) ?_
        refine SepWPp.fold
          (memRegion_24_of_sp_1160 s0.sp cap_hdrFull ptr_hdrFull (BitVec.ofNat 64 hdrFull.length))
          (by sep_focus) ?_
        refine SepWPp.frame_call
          ((ptr_hdrFull ↦ₛ hdrFull.take 64) ∗
            ((ptr_hdrFull + 64#64) ↦ₛ hdrFull.drop 64) ∗
            memRegion (ptr_hdrFull + BitVec.ofNat 64 hdrFull.length) (cap_hdrFull.toNat - hdrFull.length) ∗
            A.live ptr_hdrFull cap_hdrFull.toNat 1 ∗
            memRegion ptr_hdr 64 ∗
            A.live ptr_hdr 64 1 ∗
            ((s0.sp - 1568#64) ↦₆₄ x.self.uc.epoch) ∗
            hdrSomeBranchFrameAt (s0.sp - 1648#64) ∗
            A.pool lim
              (M.stepEvents (eAdd ++ eDec ++ recvHdrChunkAllocMacHdrEvents hdrFull.length) st0)
              st')
          (by sep_focus)
          (by repeat rw [sepConj_assoc])
          (h_init_dec hdrFull cap_hdrFull ptr_hdrFull ptr_mac ptr_hdr
            st0 (M.stepEvents (eAdd ++ eDec ++ recvHdrChunkAllocMacHdrEvents hdrFull.length) st0)
            s0 st' _ R
            hepoch hge64 hle_cap hmax_cap hptr_hdrFull hcap_hdrFull
            hpc' hrun' hsp' hsp_s0 htr' hvregs' hinv'
            hx0' hx19' hx20' hx21' hx22' hx23' hx24' hx26' hx29'
            (fun st2 hpc2 hrun2 hsp2 htr2 hvregs2 hinv2
              hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx29_2 => ?_))
        refine SepWPp.rw_pre (by rw [← hepoch]; sep_ac_rfl)
          (hcont st2 (addChunkTotal x.self.receiving_hdr x.chunk) hdrFull
            cap_hdrFull ptr_hdrFull ptr_mac ptr_hdr c1 c2 g_auth0 eAdd eDec
            hepoch hadd_eq hsort_add hdec_eq hge64 hlt_max hptr_hdr
            heAdd heDec hfits_hmac hpost_free
            hpc2 hrun2 hsp2 htr2 hvregs2 hinv2
            hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx29_2)
      · have hlt64 : hdrFull.length < 64 := by omega
        have hult64 : (BitVec.ofNat 64 hdrFull.length).ult 64#64 = true :=
          ofNat_ult_64_of_lt hlt64
        have hpan_lt := recv_hdr_chunk_isPanic_of_lt_64 x.self x.epoch x.chunk
          (addChunkTotal x.self.receiving_hdr x.chunk) hdrFull hepoch hadd_eq hdec_eq hlt64
        apply SepWPp.of_sepWP (mid := lsρ sliceIndexFailRecvHdrSym)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
        exact allowPanic_isPanic_recvHdr_budget hpan_lt
          (by simp only [wp_norm, arm64_norm, htr_sf2, List.prefix_refl]) hm
  · have hepoch_bne : (x.epoch != x.self.uc.epoch) = true := bne_iff_ne.mpr hepoch
    have hpan_ep := recv_hdr_chunk_isPanic_of_epoch_ne x.self x.epoch x.chunk hepoch
    apply SepWPp.of_sepWP (mid := lsρ assertFailedRecvHdrSym)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
    exact allowPanic_isPanic_recvHdr_budget hpan_ep
      (by simp only [wp_norm, arm64_norm, List.prefix_refl]) hm

theorem recv_hdr_chunk_part1_placed_wpp_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress}
    {Env : NoHeaderReceivedRecvHdrChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hC : RecvHdrChunkContractsPlaced M A lim ext)
    (hadd_ok : subroutine_ok (lsProg_369 (Rust.withPanics ext))
      (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (hdec_ok : PolyDecodedMessagePlacedOkX M A lim ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F)
    (st0 : M.σ) (s0 : State) (R : SepProp)
    (hPre : FitsEnv M lim st0 (Env x) → FitsEnv M lim st0 (NoHeaderReceivedRecvHdrChunkEnv x))
    (hPost : ∀ evs, NoHeaderReceivedRecvHdrChunkEnv x evs → Env x evs)
    (hfits_pre : FitsEnv M lim st0 (Env x))
    (hsort_self : PolyDecoderStrictSorted x.self.receiving_hdr)
    (hpc : s0.pc = (blkPl_369).base)
    (hrun : s0.status = .Running)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (hinv : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = x.outA)
    (hx1 : s0.readReg64 .x1 = x.selfA)
    (hx2 : s0.readReg64 .x2 = x.epoch)
    (hx3 : s0.readReg64 .x3 = x.chunkA)
    (hcont : ∀ (st2 : State) (receivingHdr : PolyDecoder) (hdrFull : Bytes)
        (cap_hdrFull ptr_hdrFull ptr_mac ptr_hdr : BitVec 64)
        (c1 c2 : BitVec 64) (g_auth0 : AuthenticatorGhost)
        (eAdd eDec : List AllocEvent)
        (_hepoch : x.epoch = x.self.uc.epoch)
        (_hadd : PolyDecoder.addChunk x.self.receiving_hdr x.chunk = .ok receivingHdr)
        (_hsort : PolyDecoderStrictSorted receivingHdr)
        (_hdec : receivingHdr.decodedMessage = .ok (some hdrFull))
        (_hge64 : 64 ≤ hdrFull.length)
        (_hlt_max : hdrFull.length < 2 ^ 63)
        (_hptr_hdr : ptr_hdr ≠ 0#64)
        (_heAdd : AddChunkSlotsEnv x.self.receiving_hdr.pts eAdd)
        (_heDec : DecodedMessageEnv receivingHdr eDec)
        (_hfits_hmac :
          FitsEvents M lim
            (M.stepEvents (eAdd ++ eDec ++ recvHdrChunkAllocMacHdrEvents hdrFull.length) st0)
            recvHdrChunkHmacEvents)
        (_hpost_free :
          ∀ evs_free, FreeOnlyEvs evs_free →
            Env x
              ((eAdd ++ eDec ++ recvHdrChunkAllocMacHdrEvents hdrFull.length ++
                  recvHdrChunkHmacEvents) ++ evs_free)),
      st2.pc = (blkPl_369).base + 564#64 →
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
      st2.readReg64 .x24 = x.epoch →
      st2.readReg64 .x25 = ptr_hdr →
      st2.readReg64 .x26 = BitVec.ofNat 64 hdrFull.length →
      st2.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st2
        (recvHdrChunkPlacedRoAt ∗
          memRegion x.outA chunkedHeaderReceivedSize ∗
          memRegion x.selfA chunkedNoHeaderReceivedSize ∗
          ct2DeallocAt A.repAlloc cap_hdrFull ptr_hdrFull ∗
          (ptr_hdr ↦ₛ hdrFull.take 64) ∗
          A.live ptr_hdr 64 1 ∗
          vecBufAt A.repAlloc (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
          authenticatorHeapAt A.repAlloc g_auth0 x.self.uc.auth ∗
          ((s0.sp - 1648#64) ↦₆₄ 0#64) ∗
          ((s0.sp - 1640#64) ↦₆₄ c1) ∗
          ((s0.sp - 1632#64) ↦₆₄ c2) ∗
          ((s0.sp - 1624#64) ↦₆₄ x.epoch) ∗
          ((s0.sp - 1616#64) ↦₆₄ g_auth0.rootKey.cap) ∗
          ((s0.sp - 1608#64) ↦₆₄ g_auth0.rootKey.ptr) ∗
          ((s0.sp - 1600#64) ↦₆₄ BitVec.ofNat 64 x.self.uc.auth.rootKey.length) ∗
          ((s0.sp - 1592#64) ↦₆₄ g_auth0.macKey.cap) ∗
          ((s0.sp - 1584#64) ↦₆₄ g_auth0.macKey.ptr) ∗
          ((s0.sp - 1576#64) ↦₆₄ BitVec.ofNat 64 x.self.uc.auth.macKey.length) ∗
          ((s0.sp - 1568#64) ↦₆₄ x.self.uc.epoch) ∗
          polyDecoderAt A.repAlloc (s0.sp - 1560#64) receivingHdr ∗
          memRegion (s0.sp - 1160#64) 24 ∗
          polyDecoderNew1152RawAt A.repAlloc (s0.sp - 1136#64) ∗
          memRegion (s0.sp - 736#64) 80 ∗
          memRegion (s0.sp - 656#64) 456 ∗
          ((s0.sp - 200#64) ↦₆₄ x.epoch) ∗
          memRegion (s0.sp - 192#64) 24 ∗
          memRegion (s0.sp - 168#64) 48 ∗
          memRegion (s0.sp - 120#64) 8 ∗
          memRegion (s0.sp - 112#64) 16 ∗
          chunkAt x.chunkA x.chunk ∗
          tokenInitPlacedAt ∗
          reduceTablePlacedAt ∗
          A.pool lim
            (M.stepEvents (eAdd ++ eDec ++ recvHdrChunkAllocMacHdrEvents hdrFull.length) st0)
            st2 ∗
          memRegion (s0.sp - 18704#64) 672 ∗
          stackAt (s0.sp - 1648#64) extHookStack ∗
          savedRegsAt s0)
        (recvHdrChunkPlacedPostQOfEnv M A lim F Env x st0 s0 R)
        (recvHdrChunkPlacedPostQp F x s0 R)) :
    SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) s0
      (recvHdrChunkPlacedRoAt ∗
        memRegion x.outA chunkedHeaderReceivedSize ∗
        chunkedNoHeaderReceivedAt A.repAlloc x.selfA x.self ∗
        chunkAt x.chunkA x.chunk ∗
        tokenInitPlacedAt ∗
        reduceTablePlacedAt ∗
        A.pool lim st0 s0 ∗
        stackAt s0.sp noHeaderReceivedRecvHdrChunkStackX)
      (recvHdrChunkPlacedPostQOfEnv M A lim F Env x st0 s0 R)
      (recvHdrChunkPlacedPostQp F x s0 R) :=
  recv_hdr_chunk_part1_placed_wpp_ofPrePostEnv hC hadd_ok hdec_ok x st0 s0 R
    hPre hPost hfits_pre hsort_self hpc hrun hsp_s0 hinv hx0 hx1 hx2 hx3 hcont

theorem recv_hdr_chunk_part1_placed_wpp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hC : RecvHdrChunkContractsPlaced M A lim ext)
    (hadd_ok : subroutine_ok (lsProg_369 (Rust.withPanics ext))
      (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (hdec_ok : PolyDecodedMessagePlacedOkX M A lim ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F)
    (st0 : M.σ) (s0 : State) (R : SepProp)
    (hfits_pre : FitsEnv M lim st0 (NoHeaderReceivedRecvHdrChunkEnv x))
    (hsort_self : PolyDecoderStrictSorted x.self.receiving_hdr)
    (hpc : s0.pc = (blkPl_369).base)
    (hrun : s0.status = .Running)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (hinv : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = x.outA)
    (hx1 : s0.readReg64 .x1 = x.selfA)
    (hx2 : s0.readReg64 .x2 = x.epoch)
    (hx3 : s0.readReg64 .x3 = x.chunkA)
    (hcont : ∀ (st2 : State) (receivingHdr : PolyDecoder) (hdrFull : Bytes)
        (cap_hdrFull ptr_hdrFull ptr_mac ptr_hdr : BitVec 64)
        (c1 c2 : BitVec 64) (g_auth0 : AuthenticatorGhost)
        (eAdd eDec : List AllocEvent)
        (_hepoch : x.epoch = x.self.uc.epoch)
        (_hadd : PolyDecoder.addChunk x.self.receiving_hdr x.chunk = .ok receivingHdr)
        (_hsort : PolyDecoderStrictSorted receivingHdr)
        (_hdec : receivingHdr.decodedMessage = .ok (some hdrFull))
        (_hge64 : 64 ≤ hdrFull.length)
        (_hlt_max : hdrFull.length < 2 ^ 63)
        (_hptr_hdr : ptr_hdr ≠ 0#64)
        (_heAdd : AddChunkSlotsEnv x.self.receiving_hdr.pts eAdd)
        (_heDec : DecodedMessageEnv receivingHdr eDec)
        (_hfits_hmac :
          FitsEvents M lim
            (M.stepEvents (eAdd ++ eDec ++ recvHdrChunkAllocMacHdrEvents hdrFull.length) st0)
            recvHdrChunkHmacEvents)
        (_hpost_free :
          ∀ evs_free, FreeOnlyEvs evs_free →
            NoHeaderReceivedRecvHdrChunkEnv x
              ((eAdd ++ eDec ++ recvHdrChunkAllocMacHdrEvents hdrFull.length ++
                  recvHdrChunkHmacEvents) ++ evs_free)),
      st2.pc = (blkPl_369).base + 564#64 →
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
      st2.readReg64 .x24 = x.epoch →
      st2.readReg64 .x25 = ptr_hdr →
      st2.readReg64 .x26 = BitVec.ofNat 64 hdrFull.length →
      st2.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st2
        (recvHdrChunkPlacedRoAt ∗
          memRegion x.outA chunkedHeaderReceivedSize ∗
          memRegion x.selfA chunkedNoHeaderReceivedSize ∗
          ct2DeallocAt A.repAlloc cap_hdrFull ptr_hdrFull ∗
          (ptr_hdr ↦ₛ hdrFull.take 64) ∗
          A.live ptr_hdr 64 1 ∗
          vecBufAt A.repAlloc (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
          authenticatorHeapAt A.repAlloc g_auth0 x.self.uc.auth ∗
          ((s0.sp - 1648#64) ↦₆₄ 0#64) ∗
          ((s0.sp - 1640#64) ↦₆₄ c1) ∗
          ((s0.sp - 1632#64) ↦₆₄ c2) ∗
          ((s0.sp - 1624#64) ↦₆₄ x.epoch) ∗
          ((s0.sp - 1616#64) ↦₆₄ g_auth0.rootKey.cap) ∗
          ((s0.sp - 1608#64) ↦₆₄ g_auth0.rootKey.ptr) ∗
          ((s0.sp - 1600#64) ↦₆₄ BitVec.ofNat 64 x.self.uc.auth.rootKey.length) ∗
          ((s0.sp - 1592#64) ↦₆₄ g_auth0.macKey.cap) ∗
          ((s0.sp - 1584#64) ↦₆₄ g_auth0.macKey.ptr) ∗
          ((s0.sp - 1576#64) ↦₆₄ BitVec.ofNat 64 x.self.uc.auth.macKey.length) ∗
          ((s0.sp - 1568#64) ↦₆₄ x.self.uc.epoch) ∗
          polyDecoderAt A.repAlloc (s0.sp - 1560#64) receivingHdr ∗
          memRegion (s0.sp - 1160#64) 24 ∗
          polyDecoderNew1152RawAt A.repAlloc (s0.sp - 1136#64) ∗
          memRegion (s0.sp - 736#64) 80 ∗
          memRegion (s0.sp - 656#64) 456 ∗
          ((s0.sp - 200#64) ↦₆₄ x.epoch) ∗
          memRegion (s0.sp - 192#64) 24 ∗
          memRegion (s0.sp - 168#64) 48 ∗
          memRegion (s0.sp - 120#64) 8 ∗
          memRegion (s0.sp - 112#64) 16 ∗
          chunkAt x.chunkA x.chunk ∗
          tokenInitPlacedAt ∗
          reduceTablePlacedAt ∗
          A.pool lim
            (M.stepEvents (eAdd ++ eDec ++ recvHdrChunkAllocMacHdrEvents hdrFull.length) st0)
            st2 ∗
          memRegion (s0.sp - 18704#64) 672 ∗
          stackAt (s0.sp - 1648#64) extHookStack ∗
          savedRegsAt s0)
        (recvHdrChunkPlacedPostQ M A lim F x st0 s0 R)
        (recvHdrChunkPlacedPostQp F x s0 R)) :
    SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) s0
      (recvHdrChunkPlacedRoAt ∗
        memRegion x.outA chunkedHeaderReceivedSize ∗
        chunkedNoHeaderReceivedAt A.repAlloc x.selfA x.self ∗
        chunkAt x.chunkA x.chunk ∗
        tokenInitPlacedAt ∗
        reduceTablePlacedAt ∗
        A.pool lim st0 s0 ∗
        stackAt s0.sp noHeaderReceivedRecvHdrChunkStackX)
      (recvHdrChunkPlacedPostQ M A lim F x st0 s0 R)
      (recvHdrChunkPlacedPostQp F x s0 R) :=
  recv_hdr_chunk_part1_placed_wpp_ofEnv hC hadd_ok hdec_ok x st0 s0 R
    id (fun _ h => h) hfits_pre hsort_self hpc hrun hsp_s0 hinv hx0 hx1 hx2 hx3 hcont

end LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart2PlacedBudget
