/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Drop.SortedSetPtBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart1PlacedBudget
meta import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart1PlacedBudget -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart5
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlaced
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp

/-!
# `<NoHeaderReceived>::recv_hdr_chunk` (Block `369`) — Budget-Threaded Part 5

Budget-threaded `[LibsignalPlacement]` proofs on `lsProg_369 (Rust.withPanics ext)` for the shared
epilogue tail (offsets `920 .. 996`) and the `MacVerifyFailed` epilogue body (offsets `844 .. 920`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart5PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalPlacement blkPC_369 blkPl_369 lsmpl lsρ)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded extHookStack)
open CryptoVerification.LibsignalTripleRatchet.Keys
  (SepWPp.rw_pre)
open CryptoVerification.LibsignalSpqrV1
  (Bytes PolyDecoder SortedSetPt spqrAuthApi spqrPolyApi)
open CryptoVerification.SpqrV1.Auth
  (AuthenticatorGhost vecBufAt)
open CryptoVerification.SpqrV1.Drop
  (DropGlueSortedSetPt16Ghost dropGluePoly16Stack)
open CryptoVerification.SpqrV1.GF.Mul2U16
  (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
  (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly
  (chunkAt polyArrayBytes polyDecoderAt)
open CryptoVerification.SpqrV1.Poly.AddChunk
  (addChunkTotal)
open CryptoVerification.SpqrV1.Poly.DecodedMessage
  (decodedMessageTotal)
open CryptoVerification.SpqrV1.States.FromPb
  (overlapLow7 overlapWord7)
open CryptoVerification.SpqrV1.States.Leaves
  (of_sepWP_lscro)
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
  (NoHeaderReceivedRecvHdrChunkGhost cells11_entails_memRegion_88 chunkedHeaderReceivedSize
   chunkedNoHeaderReceivedSize ct2DeallocAt_expose memRegion_400_sp_1560
   noHeaderReceivedRecvChunkResultAt noHeaderReceivedRecvHdrChunkStackX out_17_25_realign
   out_480_err_collapse out_480_err_expose out_9_add_8 polyDecoderAt_entails_sortedSet16_tail
   polyDecoderNew1152 polyDecoderNew1152RawAt polyDecoderNew1152RawAt_entails_polyDecoderAt
   rejoin_sp_1160_1064 rejoin_stack_hdr_epilogue sp_696_realign sp_728_721_realign sp_728_realign
   sp_736_80_collapse sp_736_80_expose stackAt_dropStack32_to_polyDecodedMessage_hdr
   stackAt_extHook_eq_dropStack32_hdr vecBufAt_drop64_eq64_emp vecBufAt_drop64_ne64_dealloc
   vecU8HeapAt_eq0_emp vecU8HeapAt_ne0_dealloc)
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
  (ct2DeallocAt polyDecodedMessageStackX savedRegsAt vecU8HeapAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
   RustLayoutOk rustDeallocEvents)
open LibsignalBinary.Proofs.SpqrV1.Drop.SortedSetPtBudget
  (dropGlueSortedSetPt16Spec)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget
  (DecodedMessageEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkDefsPlacedBudget
  (NoHeaderReceivedRecvHdrChunkEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart1PlacedBudget
  (RecvHdrChunkContractsPlaced dealloc_placed_ok_at_recvHdr dropSortedSet16_placed_ok_at_recvHdr
   recvHdrChunkPlacedPostQ recvHdrChunkPlacedPostQOfEnv recvHdrChunkPlacedPostQOfPrePostEnv
   recvHdrChunkPlacedPostQOfPrePostEnv_intro recvHdrChunkPlacedPostQp recvHdrChunkPlacedRoAt
   spqrRustDeallocSym)

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  addChunkTotal decodedMessageTotal DecodedMessageEnv
  CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.NoHeaderReceived.recv_hdr_chunk
attribute [local arm64_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm] out_9_add_8
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

private theorem ct2DeallocAt_expose_budget {M : AllocCostModel} (A : RustCliAllocBudget M)
    (cap ptr : BitVec 64) :
    ct2DeallocAt A.repAlloc cap ptr ⊢
      ⌜cap ≠ 0#64 ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        memRegion ptr cap.toNat ∗ A.live ptr cap.toNat 1 :=
  ct2DeallocAt_expose A.repAlloc cap ptr

private theorem vecBufAt_drop64_ne64_dealloc_budget {M : AllocCostModel} (A : RustCliAllocBudget M)
    (ptr_mac : BitVec 64) (hdrFull : Bytes)
    (hge65 : 65 ≤ hdrFull.length) (hmax : hdrFull.length < 2 ^ 63) :
    vecBufAt A.repAlloc (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ⊢
      memRegion ptr_mac (hdrFull.length - 64) ∗ A.live ptr_mac (hdrFull.length - 64) 1 :=
  vecBufAt_drop64_ne64_dealloc A.repAlloc ptr_mac hdrFull hge65 hmax

private theorem vecU8HeapAt_ne0_dealloc_budget {M : AllocCostModel} (A : RustCliAllocBudget M)
    (cap ptr : BitVec 64) (bs : List (BitVec 8)) (hne : cap ≠ 0#64) :
    vecU8HeapAt A.repAlloc cap ptr bs ⊢
      ⌜cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        memRegion ptr cap.toNat ∗ A.live ptr cap.toNat 1 :=
  vecU8HeapAt_ne0_dealloc A.repAlloc cap ptr bs hne

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

private theorem prep_dropGlue_stack {prog : Program} {mid : BitVec 64} {s : State}
    {P R : SepProp} {post : State → SepProp → Prop} (sp0 : BitVec 64)
    (hf : P = (memRegion (sp0 - 18704#64) 672 ∗ stackAt (sp0 - 1648#64) extHookStack) ∗ R)
    (hsp_eq : s.sp = sp0 - 1648#64)
    (hnext : SepWP prog mid s
      ((memRegion (sp0 - 18704#64) 12928 ∗ stackAt s.sp dropGluePoly16Stack) ∗ R) post) :
    SepWP prog mid s P post := by
  rw [hf, stackAt_extHook_eq_dropStack32_hdr sp0, ← hsp_eq]
  exact hnext

private theorem unprep_dropGlue_stack {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    {sp1 : BitVec 64} (sp0 : BitVec 64) {R : SepProp}
    (hf : P = (memRegion (sp0 - 18704#64) 12928 ∗ stackAt sp1 dropGluePoly16Stack) ∗ R)
    (hsp_eq : sp1 = sp0 - 1648#64)
    (hnext : SepWPp prog ret s
      ((memRegion (sp0 - 18704#64) 672 ∗ stackAt (sp0 - 1648#64) extHookStack) ∗ R) Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.rw_pre (by rw [hf, hsp_eq, ← stackAt_extHook_eq_dropStack32_hdr sp0]) hnext

private theorem finish_dropGlue_stack {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    {sp1 : BitVec 64} (sp0 : BitVec 64) {R : SepProp}
    (hf : P = (memRegion (sp0 - 18704#64) 12928 ∗ stackAt sp1 dropGluePoly16Stack) ∗ R)
    (hsp_eq : sp1 = sp0 - 1648#64)
    (hnext : SepWPp prog ret s
      (stackAt (sp0 - 1648#64) polyDecodedMessageStackX ∗ R) Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.fold (stackAt_dropStack32_to_polyDecodedMessage_hdr sp0) (by rw [hf, hsp_eq]) hnext

/-! ## 1. Shared Epilogue Tail (offsets `920 .. 996`) -/

set_option maxHeartbeats 1600000 in
theorem recv_hdr_chunk_tail_940_placed_wpp_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {PreEnv PostEnv : NoHeaderReceivedRecvHdrChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)} (hC : RecvHdrChunkContractsPlaced M A lim ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F) (receivingHdr : PolyDecoder)
    (cap_hdrFull ptr_hdrFull : BitVec 64) (st0 st_cur : M.σ) (evs_pre : List AllocEvent)
    (s0 st : State) (R : SepProp) (hst_cur : st_cur = M.stepEvents evs_pre st0)
    (hpost_free : ∀ evs_free : List AllocEvent, FreeOnlyEvs evs_free → PostEnv x (evs_pre ++ evs_free))
    (hpc : st.pc = (blkPl_369).base + 940#64) (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 1648#64) (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace) (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx20 : st.readReg64 .x20 = cap_hdrFull) (hx21 : st.readReg64 .x21 = ptr_hdrFull) :
    SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (recvHdrChunkPlacedRoAt ∗
        noHeaderReceivedRecvChunkResultAt A.repAlloc x.outA
          (x.self.recv_hdr_chunk x.epoch x.chunk) ∗
        memRegion x.selfA chunkedNoHeaderReceivedSize ∗ chunkAt x.chunkA x.chunk ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        ct2DeallocAt A.repAlloc cap_hdrFull ptr_hdrFull ∗ memRegion (s0.sp - 1648#64) 88 ∗
        polyDecoderAt A.repAlloc (s0.sp - 1560#64) receivingHdr ∗
        memRegion (s0.sp - 1160#64) 1064 ∗ savedRegsAt s0 ∗ memRegion (s0.sp - 18704#64) 672 ∗
        A.pool lim st_cur st ∗ stackAt (s0.sp - 1648#64) extHookStack)
      (recvHdrChunkPlacedPostQOfPrePostEnv M A lim F PreEnv PostEnv x st0 s0 R)
      (recvHdrChunkPlacedPostQp F x s0 R) := by
  refine SepWPp.fold (ct2DeallocAt_expose_budget A cap_hdrFull ptr_hdrFull) (by sep_focus) ?_
  refine CryptoVerification.SpqrV1.Auth.SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hcap_hdrFull_ne, hmax_hdrFull, hptr_hdrFull_ne⟩
  have hpos_hdrFull : 0 < cap_hdrFull.toNat := by
    have : cap_hdrFull.toNat ≠ 0 := fun h0 => hcap_hdrFull_ne (BitVec.eq_of_toNat_eq h0)
    omega
  have hrlay_hdrFull : RustLayoutOk cap_hdrFull.toNat 1 :=
    ⟨⟨hpos_hdrFull, ⟨0, rfl⟩, by omega⟩, by decide⟩
  have hcap_hdrFull_beq : (cap_hdrFull == 0#64) = false := beq_false_of_ne hcap_hdrFull_ne
  have h_dealloc := dealloc_placed_ok_at_recvHdr hC
  have h_drop16 := dropSortedSet16_placed_ok_at_recvHdr hC
  have hsp_norm : st.readReg64 .sp = s0.sp - 1648#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm hx20 hx21
  clear hC
  refine of_sepWP_lscro (mid := lsρ spqrRustDeallocSym) hinv ?_
  wp_steps_sync_pool (lsρ spqrRustDeallocSym)
  simp only [State.setMem_setMem]
  refine prep_ext_stack s0.sp (by sep_focus) (by simp only [wp_norm, arm64_norm, *]) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  wpp_call_lscro_recvHdr_budget h_dealloc (ptr_hdrFull, cap_hdrFull.toNat, 1, st_cur) hinv1
  refine CryptoVerification.SpqrV1.Auth.SepWPp.pure_left_focus _ (by sep_focus) fun htr1 => ?_
  refine unprep_ext_stack s0.sp (by sep_focus) (by simp only [wp_norm, arm64_norm, *]) ?_
  refine SepWPp.fold
    (polyDecoderAt_entails_sortedSet16_tail A.repAlloc (s0.sp - 1560#64) receivingHdr)
    (by sep_focus) ?_
  refine CryptoVerification.SpqrV1.Auth.SepWPp.pure_left_focus _ (by sep_focus) fun hlen_pts => ?_
  refine of_sepWP_lscro (mid := lsmpl.base 264) hF_sf ?_
  wp_steps_sync_pool (lsmpl.base 264)
  simp only [State.setMem_setMem]
  refine prep_dropGlue_stack s0.sp (by sep_focus) (by simp only [wp_norm, arm64_norm, *]) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv2
  wpp_call_lscro_recvHdr_budget h_drop16
    ((⟨s0.sp - 1560#64, receivingHdr.pts.map SortedSetPt.vec⟩ : DropGlueSortedSetPt16Ghost),
     M.stepEvents (rustDeallocEvents cap_hdrFull.toNat 1) st_cur) hinv2
  try dsimp only [dropGlueSortedSetPt16Spec]
  refine SepWPp.rw_pre (by
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      polyArrayBytes, bv_sub_add_lit]; rfl) ?_
  apply SepWPp.exists_elim; intro evs_drop
  refine CryptoVerification.SpqrV1.Auth.SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨htr2, _, hfree_drop⟩
  refine SepWPp.fold (memRegion_400_sp_1560 s0.sp) (by sep_focus) ?_
  refine finish_dropGlue_stack s0.sp (by sep_focus) (by simp only [wp_norm, arm64_norm, *]) ?_
  have hsp_sf1_norm : sf_1.readReg64 .sp = s0.sp - 1648#64 := hsp_sf_1.trans (hsp_sf.trans hsp)
  simp only [wp_norm, arm64_norm] at hsp_sf1_norm
  unfold savedRegsAt
  apply SepWPp.of_sepWP_ret
  wp_steps_sync_pool (s0.readReg64 .x30)
  simp only [State.setMem_setMem]
  refine SepWP.fold (Entails.of_eq (show
    ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
      ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) =
    savedRegsAt s0 from rfl)) (by sep_focus) ?_
  refine SepWP.fold (rejoin_stack_hdr_epilogue s0) (by sep_focus) ?_
  let st_end :=
    M.stepEvents evs_drop (M.stepEvents (rustDeallocEvents cap_hdrFull.toNat 1) st_cur)
  have hst_end :
      st_end =
        M.stepEvents (evs_pre ++ (rustDeallocEvents cap_hdrFull.toNat 1 ++ evs_drop)) st0 := by
    dsimp only [st_end]
    rw [hst_cur, ← M.stepEvents_append, ← M.stepEvents_append]
  have hfree_tail : FreeOnlyEvs (rustDeallocEvents cap_hdrFull.toNat 1 ++ evs_drop) :=
    FreeOnlyEvs.append (FreeOnlyEvs.singleton 1 cap_hdrFull.toNat) hfree_drop
  refine SepWP.mono
    (post := fun sf_ret P_ret =>
      ((sf_ret.mem ⊨ P_ret ∗ R) →
        (sf_ret.mem ⊨
          (⌜sf_ret.trace = s0.trace⌝ ∗
            (recvHdrChunkPlacedRoAt ∗
              noHeaderReceivedRecvChunkResultAt A.repAlloc x.outA
                (x.self.recv_hdr_chunk x.epoch x.chunk) ∗
              memRegion x.selfA chunkedNoHeaderReceivedSize ∗ chunkAt x.chunkA x.chunk ∗
              tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool lim st_end sf_ret ∗
              stackAt s0.sp noHeaderReceivedRecvHdrChunkStackX)) ∗ R)) ∧
        sf_ret.sp = s0.sp ∧ CalleeSavedPreserved s0 sf_ret)
    ?_ ?_
  · dsimp only [st_end]
    wp_done
  · rintro sf_ret P_ret _ _ ⟨hmem_ret, hsp_ret, hcs_ret⟩
    refine ⟨fun hm => ?_, hsp_ret, hcs_ret⟩
    have hm1 := hmem_ret hm
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm1
    rcases hm1 with ⟨htr_ret, hm2⟩
    rw [hst_end] at hm2
    exact (recvHdrChunkPlacedPostQOfPrePostEnv_intro (P_f := P_ret)
      (evs_pre ++ (rustDeallocEvents cap_hdrFull.toNat 1 ++ evs_drop))
      (hpost_free _ hfree_tail) htr_ret hsp_ret hcs_ret (fun _ => hm2)).1 hm

theorem recv_hdr_chunk_tail_940_placed_wpp_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {Env : NoHeaderReceivedRecvHdrChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)} (hC : RecvHdrChunkContractsPlaced M A lim ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F) (receivingHdr : PolyDecoder)
    (cap_hdrFull ptr_hdrFull : BitVec 64) (st0 st_cur : M.σ) (evs_pre : List AllocEvent)
    (s0 st : State) (R : SepProp) (hst_cur : st_cur = M.stepEvents evs_pre st0)
    (hpost_free : ∀ evs_free : List AllocEvent, FreeOnlyEvs evs_free → Env x (evs_pre ++ evs_free))
    (hpc : st.pc = (blkPl_369).base + 940#64) (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 1648#64) (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace) (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx20 : st.readReg64 .x20 = cap_hdrFull) (hx21 : st.readReg64 .x21 = ptr_hdrFull) :
    SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (recvHdrChunkPlacedRoAt ∗
        noHeaderReceivedRecvChunkResultAt A.repAlloc x.outA
          (x.self.recv_hdr_chunk x.epoch x.chunk) ∗
        memRegion x.selfA chunkedNoHeaderReceivedSize ∗ chunkAt x.chunkA x.chunk ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        ct2DeallocAt A.repAlloc cap_hdrFull ptr_hdrFull ∗ memRegion (s0.sp - 1648#64) 88 ∗
        polyDecoderAt A.repAlloc (s0.sp - 1560#64) receivingHdr ∗
        memRegion (s0.sp - 1160#64) 1064 ∗ savedRegsAt s0 ∗ memRegion (s0.sp - 18704#64) 672 ∗
        A.pool lim st_cur st ∗ stackAt (s0.sp - 1648#64) extHookStack)
      (recvHdrChunkPlacedPostQOfEnv M A lim F Env x st0 s0 R)
      (recvHdrChunkPlacedPostQp F x s0 R) :=
  recv_hdr_chunk_tail_940_placed_wpp_ofPrePostEnv hC x receivingHdr cap_hdrFull ptr_hdrFull
    st0 st_cur evs_pre s0 st R hst_cur hpost_free hpc hrun hsp hsp_s0 htr hvregs hinv hx20 hx21

theorem recv_hdr_chunk_tail_940_placed_wpp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)} (hC : RecvHdrChunkContractsPlaced M A lim ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F) (receivingHdr : PolyDecoder)
    (cap_hdrFull ptr_hdrFull : BitVec 64) (st0 st_cur : M.σ) (evs_pre : List AllocEvent)
    (s0 st : State) (R : SepProp) (hst_cur : st_cur = M.stepEvents evs_pre st0)
    (hpost_free :
      ∀ evs_free : List AllocEvent, FreeOnlyEvs evs_free →
        NoHeaderReceivedRecvHdrChunkEnv x (evs_pre ++ evs_free))
    (hpc : st.pc = (blkPl_369).base + 940#64) (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 1648#64) (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace) (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx20 : st.readReg64 .x20 = cap_hdrFull) (hx21 : st.readReg64 .x21 = ptr_hdrFull) :
    SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (recvHdrChunkPlacedRoAt ∗
        noHeaderReceivedRecvChunkResultAt A.repAlloc x.outA
          (x.self.recv_hdr_chunk x.epoch x.chunk) ∗
        memRegion x.selfA chunkedNoHeaderReceivedSize ∗ chunkAt x.chunkA x.chunk ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        ct2DeallocAt A.repAlloc cap_hdrFull ptr_hdrFull ∗ memRegion (s0.sp - 1648#64) 88 ∗
        polyDecoderAt A.repAlloc (s0.sp - 1560#64) receivingHdr ∗
        memRegion (s0.sp - 1160#64) 1064 ∗ savedRegsAt s0 ∗ memRegion (s0.sp - 18704#64) 672 ∗
        A.pool lim st_cur st ∗ stackAt (s0.sp - 1648#64) extHookStack)
      (recvHdrChunkPlacedPostQ M A lim F x st0 s0 R)
      (recvHdrChunkPlacedPostQp F x s0 R) :=
  recv_hdr_chunk_tail_940_placed_wpp_ofEnv hC x receivingHdr cap_hdrFull ptr_hdrFull
    st0 st_cur evs_pre s0 st R hst_cur hpost_free hpc hrun hsp hsp_s0 htr hvregs hinv hx20 hx21

set_option maxHeartbeats 1200000 in
theorem recv_hdr_chunk_tail_924_placed_wpp_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {PreEnv PostEnv : NoHeaderReceivedRecvHdrChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)} (hC : RecvHdrChunkContractsPlaced M A lim ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F) (receivingHdr : PolyDecoder) (hdrFull : Bytes)
    (cap_hdrFull ptr_hdrFull ptr_mac : BitVec 64)
    (st0 st_cur : M.σ) (evs_pre : List AllocEvent) (s0 st : State) (R : SepProp)
    (hst_cur : st_cur = M.stepEvents evs_pre st0)
    (hpost_free : ∀ evs_free : List AllocEvent, FreeOnlyEvs evs_free → PostEnv x (evs_pre ++ evs_free))
    (hge65 : 65 ≤ hdrFull.length) (hmax_hdr : hdrFull.length < 2 ^ 63)
    (hpc : st.pc = (blkPl_369).base + 924#64) (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 1648#64) (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace) (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx20 : st.readReg64 .x20 = cap_hdrFull) (hx21 : st.readReg64 .x21 = ptr_hdrFull)
    (hx22 : st.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64))
    (hx23 : st.readReg64 .x23 = ptr_mac) :
    SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (vecBufAt A.repAlloc (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
        recvHdrChunkPlacedRoAt ∗
        noHeaderReceivedRecvChunkResultAt A.repAlloc x.outA
          (x.self.recv_hdr_chunk x.epoch x.chunk) ∗
        memRegion x.selfA chunkedNoHeaderReceivedSize ∗ chunkAt x.chunkA x.chunk ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        ct2DeallocAt A.repAlloc cap_hdrFull ptr_hdrFull ∗ memRegion (s0.sp - 1648#64) 88 ∗
        polyDecoderAt A.repAlloc (s0.sp - 1560#64) receivingHdr ∗
        memRegion (s0.sp - 1160#64) 1064 ∗ savedRegsAt s0 ∗ memRegion (s0.sp - 18704#64) 672 ∗
        A.pool lim st_cur st ∗ stackAt (s0.sp - 1648#64) extHookStack)
      (recvHdrChunkPlacedPostQOfPrePostEnv M A lim F PreEnv PostEnv x st0 s0 R)
      (recvHdrChunkPlacedPostQp F x s0 R) := by
  refine SepWPp.fold
    (vecBufAt_drop64_ne64_dealloc_budget A ptr_mac hdrFull hge65 hmax_hdr)
    (by sep_focus) ?_
  have h_dealloc := dealloc_placed_ok_at_recvHdr hC
  have h_tail940 :=
    @recv_hdr_chunk_tail_940_placed_wpp_ofPrePostEnv _ M A lim F PreEnv PostEnv ext
      hC x receivingHdr cap_hdrFull ptr_hdrFull st0
  have hsub_pos : 0 < hdrFull.length - 64 := by omega
  have hrlay_mac : RustLayoutOk (hdrFull.length - 64) 1 :=
    ⟨⟨hsub_pos, ⟨0, rfl⟩, by omega⟩, by decide⟩
  have hsub_toNat : (BitVec.ofNat 64 (hdrFull.length - 64)).toNat = hdrFull.length - 64 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsp_norm : st.readReg64 .sp = s0.sp - 1648#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm hx20 hx21 hx22 hx23
  clear hC
  refine of_sepWP_lscro (mid := lsρ spqrRustDeallocSym) hinv ?_
  wp_steps_sync_pool (lsρ spqrRustDeallocSym)
  simp only [State.setMem_setMem]
  refine prep_ext_stack s0.sp (by sep_focus) (by simp only [wp_norm, arm64_norm, *]) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  wpp_call_lscro_recvHdr_budget h_dealloc (ptr_mac, hdrFull.length - 64, 1, st_cur) hinv1
  refine CryptoVerification.SpqrV1.Auth.SepWPp.pure_left_focus _ (by sep_focus) fun htr1 => ?_
  refine unprep_ext_stack s0.sp (by sep_focus) (by simp only [wp_norm, arm64_norm, *]) ?_
  have hst_mac :
      M.stepEvents (rustDeallocEvents (hdrFull.length - 64) 1) st_cur =
        M.stepEvents (evs_pre ++ rustDeallocEvents (hdrFull.length - 64) 1) st0 := by
    rw [hst_cur, ← M.stepEvents_append]
  have hpost_mac :
      ∀ evs_free : List AllocEvent, FreeOnlyEvs evs_free →
        PostEnv x ((evs_pre ++ rustDeallocEvents (hdrFull.length - 64) 1) ++ evs_free) := by
    intro evs_free hf
    rw [List.append_assoc]
    exact hpost_free _ (FreeOnlyEvs.append (FreeOnlyEvs.singleton 1 (hdrFull.length - 64)) hf)
  refine SepWPp.rw_pre (by sep_ac_rfl)
    (h_tail940
      (M.stepEvents (rustDeallocEvents (hdrFull.length - 64) 1) st_cur)
      (evs_pre ++ rustDeallocEvents (hdrFull.length - 64) 1)
      s0 sf R hst_mac hpost_mac
      (by wp_norm_goal) (by wp_norm_goal)
      (by simp only [wp_norm, arm64_norm, *])
      hsp_s0
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      hF_sf
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]))

theorem recv_hdr_chunk_tail_924_placed_wpp_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {Env : NoHeaderReceivedRecvHdrChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)} (hC : RecvHdrChunkContractsPlaced M A lim ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F) (receivingHdr : PolyDecoder) (hdrFull : Bytes)
    (cap_hdrFull ptr_hdrFull ptr_mac : BitVec 64)
    (st0 st_cur : M.σ) (evs_pre : List AllocEvent) (s0 st : State) (R : SepProp)
    (hst_cur : st_cur = M.stepEvents evs_pre st0)
    (hpost_free : ∀ evs_free : List AllocEvent, FreeOnlyEvs evs_free → Env x (evs_pre ++ evs_free))
    (hge65 : 65 ≤ hdrFull.length) (hmax_hdr : hdrFull.length < 2 ^ 63)
    (hpc : st.pc = (blkPl_369).base + 924#64) (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 1648#64) (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace) (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx20 : st.readReg64 .x20 = cap_hdrFull) (hx21 : st.readReg64 .x21 = ptr_hdrFull)
    (hx22 : st.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64))
    (hx23 : st.readReg64 .x23 = ptr_mac) :
    SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (vecBufAt A.repAlloc (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
        recvHdrChunkPlacedRoAt ∗
        noHeaderReceivedRecvChunkResultAt A.repAlloc x.outA
          (x.self.recv_hdr_chunk x.epoch x.chunk) ∗
        memRegion x.selfA chunkedNoHeaderReceivedSize ∗ chunkAt x.chunkA x.chunk ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        ct2DeallocAt A.repAlloc cap_hdrFull ptr_hdrFull ∗ memRegion (s0.sp - 1648#64) 88 ∗
        polyDecoderAt A.repAlloc (s0.sp - 1560#64) receivingHdr ∗
        memRegion (s0.sp - 1160#64) 1064 ∗ savedRegsAt s0 ∗ memRegion (s0.sp - 18704#64) 672 ∗
        A.pool lim st_cur st ∗ stackAt (s0.sp - 1648#64) extHookStack)
      (recvHdrChunkPlacedPostQOfEnv M A lim F Env x st0 s0 R)
      (recvHdrChunkPlacedPostQp F x s0 R) :=
  recv_hdr_chunk_tail_924_placed_wpp_ofPrePostEnv hC x receivingHdr hdrFull cap_hdrFull ptr_hdrFull
    ptr_mac st0 st_cur evs_pre s0 st R hst_cur hpost_free hge65 hmax_hdr hpc hrun hsp hsp_s0 htr
    hvregs hinv hx20 hx21 hx22 hx23

theorem recv_hdr_chunk_tail_924_placed_wpp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)} (hC : RecvHdrChunkContractsPlaced M A lim ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F) (receivingHdr : PolyDecoder) (hdrFull : Bytes)
    (cap_hdrFull ptr_hdrFull ptr_mac : BitVec 64)
    (st0 st_cur : M.σ) (evs_pre : List AllocEvent) (s0 st : State) (R : SepProp)
    (hst_cur : st_cur = M.stepEvents evs_pre st0)
    (hpost_free :
      ∀ evs_free : List AllocEvent, FreeOnlyEvs evs_free →
        NoHeaderReceivedRecvHdrChunkEnv x (evs_pre ++ evs_free))
    (hge65 : 65 ≤ hdrFull.length) (hmax_hdr : hdrFull.length < 2 ^ 63)
    (hpc : st.pc = (blkPl_369).base + 924#64) (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 1648#64) (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace) (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx20 : st.readReg64 .x20 = cap_hdrFull) (hx21 : st.readReg64 .x21 = ptr_hdrFull)
    (hx22 : st.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64))
    (hx23 : st.readReg64 .x23 = ptr_mac) :
    SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (vecBufAt A.repAlloc (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
        recvHdrChunkPlacedRoAt ∗
        noHeaderReceivedRecvChunkResultAt A.repAlloc x.outA
          (x.self.recv_hdr_chunk x.epoch x.chunk) ∗
        memRegion x.selfA chunkedNoHeaderReceivedSize ∗ chunkAt x.chunkA x.chunk ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        ct2DeallocAt A.repAlloc cap_hdrFull ptr_hdrFull ∗ memRegion (s0.sp - 1648#64) 88 ∗
        polyDecoderAt A.repAlloc (s0.sp - 1560#64) receivingHdr ∗
        memRegion (s0.sp - 1160#64) 1064 ∗ savedRegsAt s0 ∗ memRegion (s0.sp - 18704#64) 672 ∗
        A.pool lim st_cur st ∗ stackAt (s0.sp - 1648#64) extHookStack)
      (recvHdrChunkPlacedPostQ M A lim F x st0 s0 R)
      (recvHdrChunkPlacedPostQp F x s0 R) :=
  recv_hdr_chunk_tail_924_placed_wpp_ofEnv hC x receivingHdr hdrFull cap_hdrFull ptr_hdrFull
    ptr_mac st0 st_cur evs_pre s0 st R hst_cur hpost_free hge65 hmax_hdr hpc hrun hsp hsp_s0 htr
    hvregs hinv hx20 hx21 hx22 hx23

theorem recv_hdr_chunk_tail_920_placed_wpp_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {PreEnv PostEnv : NoHeaderReceivedRecvHdrChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)} (hC : RecvHdrChunkContractsPlaced M A lim ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F) (receivingHdr : PolyDecoder) (hdrFull : Bytes)
    (cap_hdrFull ptr_hdrFull ptr_mac : BitVec 64)
    (st0 st_cur : M.σ) (evs_pre : List AllocEvent) (s0 st : State) (R : SepProp)
    (hst_cur : st_cur = M.stepEvents evs_pre st0)
    (hpost_free : ∀ evs_free : List AllocEvent, FreeOnlyEvs evs_free → PostEnv x (evs_pre ++ evs_free))
    (hge64 : 64 ≤ hdrFull.length) (hmax_hdr : hdrFull.length < 2 ^ 63)
    (hpc : st.pc = (blkPl_369).base + 920#64) (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 1648#64) (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace) (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx20 : st.readReg64 .x20 = cap_hdrFull) (hx21 : st.readReg64 .x21 = ptr_hdrFull)
    (hx22 : st.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64))
    (hx23 : st.readReg64 .x23 = ptr_mac) :
    SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (vecBufAt A.repAlloc (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
        recvHdrChunkPlacedRoAt ∗
        noHeaderReceivedRecvChunkResultAt A.repAlloc x.outA
          (x.self.recv_hdr_chunk x.epoch x.chunk) ∗
        memRegion x.selfA chunkedNoHeaderReceivedSize ∗ chunkAt x.chunkA x.chunk ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        ct2DeallocAt A.repAlloc cap_hdrFull ptr_hdrFull ∗ memRegion (s0.sp - 1648#64) 88 ∗
        polyDecoderAt A.repAlloc (s0.sp - 1560#64) receivingHdr ∗
        memRegion (s0.sp - 1160#64) 1064 ∗ savedRegsAt s0 ∗ memRegion (s0.sp - 18704#64) 672 ∗
        A.pool lim st_cur st ∗ stackAt (s0.sp - 1648#64) extHookStack)
      (recvHdrChunkPlacedPostQOfPrePostEnv M A lim F PreEnv PostEnv x st0 s0 R)
      (recvHdrChunkPlacedPostQp F x s0 R) := by
  have h_tail940 :=
    @recv_hdr_chunk_tail_940_placed_wpp_ofPrePostEnv _ M A lim F PreEnv PostEnv ext
      hC x receivingHdr cap_hdrFull ptr_hdrFull st0
  have h_tail924 :=
    @recv_hdr_chunk_tail_924_placed_wpp_ofPrePostEnv _ M A lim F PreEnv PostEnv ext
      hC x receivingHdr hdrFull cap_hdrFull ptr_hdrFull ptr_mac st0
  by_cases heq64 : hdrFull.length = 64
  · have hsub0 : hdrFull.length - 64 = 0 := by omega
    have hx22_0 : st.readReg64 .x22 = 0#64 := by rw [hx22, hsub0]
    simp only [wp_norm, arm64_norm] at hx20 hx21 hx22_0
    refine SepWPp.fold (vecBufAt_drop64_eq64_emp A.repAlloc ptr_mac hdrFull heq64) (by sep_focus) ?_
    clear hC h_tail924
    refine of_sepWP_lscro (mid := (blkPl_369).base + 940#64) hinv ?_
    wp_steps_sync_pool ((blkPl_369).base + 940#64)
    simp only [State.setMem_setMem]
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv1
    refine SepWPp.rw_pre (by sep_ac_rfl)
      (h_tail940 st_cur evs_pre s0 _ R hst_cur hpost_free
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
    wp_steps_sync_pool ((blkPl_369).base + 924#64)
    simp only [State.setMem_setMem]
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv1
    refine SepWPp.rw_pre (by sep_ac_rfl)
      (h_tail924 st_cur evs_pre s0 _ R hst_cur hpost_free hge65 hmax_hdr
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

theorem recv_hdr_chunk_tail_920_placed_wpp_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {Env : NoHeaderReceivedRecvHdrChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)} (hC : RecvHdrChunkContractsPlaced M A lim ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F) (receivingHdr : PolyDecoder) (hdrFull : Bytes)
    (cap_hdrFull ptr_hdrFull ptr_mac : BitVec 64)
    (st0 st_cur : M.σ) (evs_pre : List AllocEvent) (s0 st : State) (R : SepProp)
    (hst_cur : st_cur = M.stepEvents evs_pre st0)
    (hpost_free : ∀ evs_free : List AllocEvent, FreeOnlyEvs evs_free → Env x (evs_pre ++ evs_free))
    (hge64 : 64 ≤ hdrFull.length) (hmax_hdr : hdrFull.length < 2 ^ 63)
    (hpc : st.pc = (blkPl_369).base + 920#64) (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 1648#64) (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace) (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx20 : st.readReg64 .x20 = cap_hdrFull) (hx21 : st.readReg64 .x21 = ptr_hdrFull)
    (hx22 : st.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64))
    (hx23 : st.readReg64 .x23 = ptr_mac) :
    SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (vecBufAt A.repAlloc (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
        recvHdrChunkPlacedRoAt ∗
        noHeaderReceivedRecvChunkResultAt A.repAlloc x.outA
          (x.self.recv_hdr_chunk x.epoch x.chunk) ∗
        memRegion x.selfA chunkedNoHeaderReceivedSize ∗ chunkAt x.chunkA x.chunk ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        ct2DeallocAt A.repAlloc cap_hdrFull ptr_hdrFull ∗ memRegion (s0.sp - 1648#64) 88 ∗
        polyDecoderAt A.repAlloc (s0.sp - 1560#64) receivingHdr ∗
        memRegion (s0.sp - 1160#64) 1064 ∗ savedRegsAt s0 ∗ memRegion (s0.sp - 18704#64) 672 ∗
        A.pool lim st_cur st ∗ stackAt (s0.sp - 1648#64) extHookStack)
      (recvHdrChunkPlacedPostQOfEnv M A lim F Env x st0 s0 R)
      (recvHdrChunkPlacedPostQp F x s0 R) :=
  recv_hdr_chunk_tail_920_placed_wpp_ofPrePostEnv hC x receivingHdr hdrFull cap_hdrFull ptr_hdrFull
    ptr_mac st0 st_cur evs_pre s0 st R hst_cur hpost_free hge64 hmax_hdr hpc hrun hsp hsp_s0 htr
    hvregs hinv hx20 hx21 hx22 hx23

theorem recv_hdr_chunk_tail_920_placed_wpp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)} (hC : RecvHdrChunkContractsPlaced M A lim ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F) (receivingHdr : PolyDecoder) (hdrFull : Bytes)
    (cap_hdrFull ptr_hdrFull ptr_mac : BitVec 64)
    (st0 st_cur : M.σ) (evs_pre : List AllocEvent) (s0 st : State) (R : SepProp)
    (hst_cur : st_cur = M.stepEvents evs_pre st0)
    (hpost_free :
      ∀ evs_free : List AllocEvent, FreeOnlyEvs evs_free →
        NoHeaderReceivedRecvHdrChunkEnv x (evs_pre ++ evs_free))
    (hge64 : 64 ≤ hdrFull.length) (hmax_hdr : hdrFull.length < 2 ^ 63)
    (hpc : st.pc = (blkPl_369).base + 920#64) (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 1648#64) (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace) (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx20 : st.readReg64 .x20 = cap_hdrFull) (hx21 : st.readReg64 .x21 = ptr_hdrFull)
    (hx22 : st.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64))
    (hx23 : st.readReg64 .x23 = ptr_mac) :
    SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (vecBufAt A.repAlloc (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
        recvHdrChunkPlacedRoAt ∗
        noHeaderReceivedRecvChunkResultAt A.repAlloc x.outA
          (x.self.recv_hdr_chunk x.epoch x.chunk) ∗
        memRegion x.selfA chunkedNoHeaderReceivedSize ∗ chunkAt x.chunkA x.chunk ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        ct2DeallocAt A.repAlloc cap_hdrFull ptr_hdrFull ∗ memRegion (s0.sp - 1648#64) 88 ∗
        polyDecoderAt A.repAlloc (s0.sp - 1560#64) receivingHdr ∗
        memRegion (s0.sp - 1160#64) 1064 ∗ savedRegsAt s0 ∗ memRegion (s0.sp - 18704#64) 672 ∗
        A.pool lim st_cur st ∗ stackAt (s0.sp - 1648#64) extHookStack)
      (recvHdrChunkPlacedPostQ M A lim F x st0 s0 R)
      (recvHdrChunkPlacedPostQp F x s0 R) :=
  recv_hdr_chunk_tail_920_placed_wpp_ofEnv hC x receivingHdr hdrFull cap_hdrFull ptr_hdrFull
    ptr_mac st0 st_cur evs_pre s0 st R hst_cur hpost_free hge64 hmax_hdr hpc hrun hsp hsp_s0 htr
    hvregs hinv hx20 hx21 hx22 hx23

/-! ## 2. `MacVerifyFailed` Epilogue Body (offsets `844 .. 920`) -/

theorem recv_hdr_chunk_err_844_placed_wpp_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {PreEnv PostEnv : NoHeaderReceivedRecvHdrChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)} (hC : RecvHdrChunkContractsPlaced M A lim ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F) (hdrFull : Bytes)
    (cap_hdrFull ptr_hdrFull ptr_mac : BitVec 64) (g_auth0 : AuthenticatorGhost)
    (st0 st_cur : M.σ) (s0 st : State) (F_frame R : SepProp)
    (hpc : st.pc = (blkPl_369).base + 844#64) (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 1648#64) (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace) (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem) (hx19 : st.readReg64 .x19 = x.outA)
    (hx20 : st.readReg64 .x20 = cap_hdrFull) (hx21 : st.readReg64 .x21 = ptr_hdrFull)
    (hx22 : st.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64))
    (hx23 : st.readReg64 .x23 = ptr_mac) (hx26 : st.readReg64 .x26 = s0.sp - 736#64)
    (hcont : ∀ (st2 : State) (evs_mk : List AllocEvent),
      FreeOnlyEvs evs_mk → st2.pc = (blkPl_369).base + 864#64 → st2.status = .Running →
      st2.sp = s0.sp - 1648#64 → st2.trace = s0.trace →
      calleeSavedVRegs st2 = calleeSavedVRegs s0 → LibsignalCodeRoLoaded lsmpl st2.mem →
      st2.readReg64 .x19 = x.outA → st2.readReg64 .x20 = cap_hdrFull →
      st2.readReg64 .x21 = ptr_hdrFull →
      st2.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64) →
      st2.readReg64 .x23 = ptr_mac → st2.readReg64 .x26 = s0.sp - 736#64 →
      SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st2
        (recvHdrChunkPlacedRoAt ∗ ((s0.sp - 1640#64) ↦₆₄ g_auth0.macKey.ptr) ∗
          ((s0.sp - 1592#64) ↦₆₄ g_auth0.macKey.cap) ∗
          A.pool lim (M.stepEvents evs_mk st_cur) st2 ∗
          stackAt (s0.sp - 1648#64) extHookStack ∗ F_frame)
        (recvHdrChunkPlacedPostQOfPrePostEnv M A lim F PreEnv PostEnv x st0 s0 R)
        (recvHdrChunkPlacedPostQp F x s0 R)) :
    SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (vecU8HeapAt A.repAlloc g_auth0.macKey.cap g_auth0.macKey.ptr x.self.uc.auth.macKey ∗
        recvHdrChunkPlacedRoAt ∗ ((s0.sp - 1640#64) ↦₆₄ g_auth0.macKey.ptr) ∗
        ((s0.sp - 1592#64) ↦₆₄ g_auth0.macKey.cap) ∗ A.pool lim st_cur st ∗
        stackAt (s0.sp - 1648#64) extHookStack ∗ F_frame)
      (recvHdrChunkPlacedPostQOfPrePostEnv M A lim F PreEnv PostEnv x st0 s0 R)
      (recvHdrChunkPlacedPostQp F x s0 R) := by
  have h_dealloc := dealloc_placed_ok_at_recvHdr hC
  have hsp_norm : st.readReg64 .sp = s0.sp - 1648#64 := hsp
  by_cases hcap : g_auth0.macKey.cap = 0#64
  · refine SepWPp.fold
      (vecU8HeapAt_eq0_emp A.repAlloc g_auth0.macKey.cap g_auth0.macKey.ptr x.self.uc.auth.macKey hcap)
      (by sep_focus) ?_
    simp only [wp_norm, arm64_norm] at hsp_norm hx19 hx20 hx21 hx22 hx23 hx26
    clear hC h_dealloc
    refine of_sepWP_lscro (mid := (blkPl_369).base + 864#64) hinv ?_
    wp_steps_sync_pool ((blkPl_369).base + 864#64)
    simp only [State.setMem_setMem]
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv1
    refine SepWPp.rw_pre (by sep_ac_rfl)
      (hcont _ [] FreeOnlyEvs.nil
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
    refine SepWPp.fold
      (vecU8HeapAt_ne0_dealloc_budget A g_auth0.macKey.cap g_auth0.macKey.ptr x.self.uc.auth.macKey hcap)
      (by sep_focus) ?_
    refine CryptoVerification.SpqrV1.Auth.SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨hmax, hptr_ne⟩
    have hrlay_mk : RustLayoutOk g_auth0.macKey.cap.toNat 1 :=
      ⟨⟨hcap_pos, ⟨0, rfl⟩, by omega⟩, by decide⟩
    simp only [wp_norm, arm64_norm] at hsp_norm hx19 hx20 hx21 hx22 hx23 hx26
    clear hC
    refine of_sepWP_lscro (mid := lsρ spqrRustDeallocSym) hinv ?_
    wp_steps_sync_pool (lsρ spqrRustDeallocSym)
    simp only [State.setMem_setMem]
    refine prep_ext_stack s0.sp (by sep_focus) (by simp only [wp_norm, arm64_norm, *]) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv1
    wpp_call_lscro_recvHdr_budget h_dealloc
      (g_auth0.macKey.ptr, g_auth0.macKey.cap.toNat, 1, st_cur) hinv1
    refine CryptoVerification.SpqrV1.Auth.SepWPp.pure_left_focus _ (by sep_focus) fun htr1 => ?_
    refine unprep_ext_stack s0.sp (by sep_focus) (by simp only [wp_norm, arm64_norm, *]) ?_
    refine SepWPp.rw_pre (by sep_ac_rfl)
      (hcont sf (rustDeallocEvents g_auth0.macKey.cap.toNat 1)
        (FreeOnlyEvs.singleton 1 g_auth0.macKey.cap.toNat)
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

theorem recv_hdr_chunk_err_844_placed_wpp_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {Env : NoHeaderReceivedRecvHdrChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)} (hC : RecvHdrChunkContractsPlaced M A lim ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F) (hdrFull : Bytes)
    (cap_hdrFull ptr_hdrFull ptr_mac : BitVec 64) (g_auth0 : AuthenticatorGhost)
    (st0 st_cur : M.σ) (s0 st : State) (F_frame R : SepProp)
    (hpc : st.pc = (blkPl_369).base + 844#64) (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 1648#64) (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace) (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem) (hx19 : st.readReg64 .x19 = x.outA)
    (hx20 : st.readReg64 .x20 = cap_hdrFull) (hx21 : st.readReg64 .x21 = ptr_hdrFull)
    (hx22 : st.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64))
    (hx23 : st.readReg64 .x23 = ptr_mac) (hx26 : st.readReg64 .x26 = s0.sp - 736#64)
    (hcont : ∀ (st2 : State) (evs_mk : List AllocEvent),
      FreeOnlyEvs evs_mk → st2.pc = (blkPl_369).base + 864#64 → st2.status = .Running →
      st2.sp = s0.sp - 1648#64 → st2.trace = s0.trace →
      calleeSavedVRegs st2 = calleeSavedVRegs s0 → LibsignalCodeRoLoaded lsmpl st2.mem →
      st2.readReg64 .x19 = x.outA → st2.readReg64 .x20 = cap_hdrFull →
      st2.readReg64 .x21 = ptr_hdrFull →
      st2.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64) →
      st2.readReg64 .x23 = ptr_mac → st2.readReg64 .x26 = s0.sp - 736#64 →
      SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st2
        (recvHdrChunkPlacedRoAt ∗ ((s0.sp - 1640#64) ↦₆₄ g_auth0.macKey.ptr) ∗
          ((s0.sp - 1592#64) ↦₆₄ g_auth0.macKey.cap) ∗
          A.pool lim (M.stepEvents evs_mk st_cur) st2 ∗
          stackAt (s0.sp - 1648#64) extHookStack ∗ F_frame)
        (recvHdrChunkPlacedPostQOfEnv M A lim F Env x st0 s0 R)
        (recvHdrChunkPlacedPostQp F x s0 R)) :
    SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (vecU8HeapAt A.repAlloc g_auth0.macKey.cap g_auth0.macKey.ptr x.self.uc.auth.macKey ∗
        recvHdrChunkPlacedRoAt ∗ ((s0.sp - 1640#64) ↦₆₄ g_auth0.macKey.ptr) ∗
        ((s0.sp - 1592#64) ↦₆₄ g_auth0.macKey.cap) ∗ A.pool lim st_cur st ∗
        stackAt (s0.sp - 1648#64) extHookStack ∗ F_frame)
      (recvHdrChunkPlacedPostQOfEnv M A lim F Env x st0 s0 R)
      (recvHdrChunkPlacedPostQp F x s0 R) :=
  recv_hdr_chunk_err_844_placed_wpp_ofPrePostEnv hC x hdrFull cap_hdrFull ptr_hdrFull ptr_mac
    g_auth0 st0 st_cur s0 st F_frame R hpc hrun hsp hsp_s0 htr hvregs hinv hx19 hx20 hx21 hx22
    hx23 hx26 hcont

theorem recv_hdr_chunk_err_844_placed_wpp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)} (hC : RecvHdrChunkContractsPlaced M A lim ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F) (hdrFull : Bytes)
    (cap_hdrFull ptr_hdrFull ptr_mac : BitVec 64) (g_auth0 : AuthenticatorGhost)
    (st0 st_cur : M.σ) (s0 st : State) (F_frame R : SepProp)
    (hpc : st.pc = (blkPl_369).base + 844#64) (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 1648#64) (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace) (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem) (hx19 : st.readReg64 .x19 = x.outA)
    (hx20 : st.readReg64 .x20 = cap_hdrFull) (hx21 : st.readReg64 .x21 = ptr_hdrFull)
    (hx22 : st.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64))
    (hx23 : st.readReg64 .x23 = ptr_mac) (hx26 : st.readReg64 .x26 = s0.sp - 736#64)
    (hcont : ∀ (st2 : State) (evs_mk : List AllocEvent),
      FreeOnlyEvs evs_mk → st2.pc = (blkPl_369).base + 864#64 → st2.status = .Running →
      st2.sp = s0.sp - 1648#64 → st2.trace = s0.trace →
      calleeSavedVRegs st2 = calleeSavedVRegs s0 → LibsignalCodeRoLoaded lsmpl st2.mem →
      st2.readReg64 .x19 = x.outA → st2.readReg64 .x20 = cap_hdrFull →
      st2.readReg64 .x21 = ptr_hdrFull →
      st2.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64) →
      st2.readReg64 .x23 = ptr_mac → st2.readReg64 .x26 = s0.sp - 736#64 →
      SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st2
        (recvHdrChunkPlacedRoAt ∗ ((s0.sp - 1640#64) ↦₆₄ g_auth0.macKey.ptr) ∗
          ((s0.sp - 1592#64) ↦₆₄ g_auth0.macKey.cap) ∗
          A.pool lim (M.stepEvents evs_mk st_cur) st2 ∗
          stackAt (s0.sp - 1648#64) extHookStack ∗ F_frame)
        (recvHdrChunkPlacedPostQ M A lim F x st0 s0 R)
        (recvHdrChunkPlacedPostQp F x s0 R)) :
    SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (vecU8HeapAt A.repAlloc g_auth0.macKey.cap g_auth0.macKey.ptr x.self.uc.auth.macKey ∗
        recvHdrChunkPlacedRoAt ∗ ((s0.sp - 1640#64) ↦₆₄ g_auth0.macKey.ptr) ∗
        ((s0.sp - 1592#64) ↦₆₄ g_auth0.macKey.cap) ∗ A.pool lim st_cur st ∗
        stackAt (s0.sp - 1648#64) extHookStack ∗ F_frame)
      (recvHdrChunkPlacedPostQ M A lim F x st0 s0 R)
      (recvHdrChunkPlacedPostQp F x s0 R) :=
  recv_hdr_chunk_err_844_placed_wpp_ofEnv hC x hdrFull cap_hdrFull ptr_hdrFull ptr_mac
    g_auth0 st0 st_cur s0 st F_frame R hpc hrun hsp hsp_s0 htr hvregs hinv hx19 hx20 hx21 hx22
    hx23 hx26 hcont

set_option maxHeartbeats 1600000 in
theorem recv_hdr_chunk_err_864_placed_wpp_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {PreEnv PostEnv : NoHeaderReceivedRecvHdrChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)} (hC : RecvHdrChunkContractsPlaced M A lim ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F) (receivingHdr : PolyDecoder) (hdrFull : Bytes)
    (cap_hdrFull ptr_hdrFull ptr_mac : BitVec 64)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v200 : BitVec 64)
    (st0 st_cur : M.σ) (evs_pre : List AllocEvent) (s0 st : State) (R : SepProp)
    (hst_cur : st_cur = M.stepEvents evs_pre st0)
    (hpost_free : ∀ evs_free : List AllocEvent, FreeOnlyEvs evs_free → PostEnv x (evs_pre ++ evs_free))
    (hres : x.self.recv_hdr_chunk x.epoch x.chunk = .error (.err .macVerifyFailed))
    (hge64 : 64 ≤ hdrFull.length) (hmax_hdr : hdrFull.length < 2 ^ 63)
    (hpc : st.pc = (blkPl_369).base + 864#64) (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 1648#64) (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace) (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem) (hx19 : st.readReg64 .x19 = x.outA)
    (hx20 : st.readReg64 .x20 = cap_hdrFull) (hx21 : st.readReg64 .x21 = ptr_hdrFull)
    (hx22 : st.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64))
    (hx23 : st.readReg64 .x23 = ptr_mac) (hx26 : st.readReg64 .x26 = s0.sp - 736#64) :
    SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (vecBufAt A.repAlloc (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
        recvHdrChunkPlacedRoAt ∗ memRegion x.outA chunkedHeaderReceivedSize ∗
        memRegion x.selfA chunkedNoHeaderReceivedSize ∗ chunkAt x.chunkA x.chunk ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        ct2DeallocAt A.repAlloc cap_hdrFull ptr_hdrFull ∗
        ((s0.sp - 1648#64) ↦₆₄ v0) ∗ ((s0.sp - 1640#64) ↦₆₄ v1) ∗
        ((s0.sp - 1632#64) ↦₆₄ v2) ∗ ((s0.sp - 1624#64) ↦₆₄ v3) ∗
        ((s0.sp - 1616#64) ↦₆₄ v4) ∗ ((s0.sp - 1608#64) ↦₆₄ v5) ∗
        ((s0.sp - 1600#64) ↦₆₄ v6) ∗ ((s0.sp - 1592#64) ↦₆₄ v7) ∗
        ((s0.sp - 1584#64) ↦₆₄ v8) ∗ ((s0.sp - 1576#64) ↦₆₄ v9) ∗
        ((s0.sp - 1568#64) ↦₆₄ v10) ∗
        polyDecoderAt A.repAlloc (s0.sp - 1560#64) receivingHdr ∗
        memRegion (s0.sp - 1160#64) 24 ∗ polyDecoderNew1152RawAt A.repAlloc (s0.sp - 1136#64) ∗
        memRegion (s0.sp - 736#64) 80 ∗ memRegion (s0.sp - 656#64) 456 ∗
        ((s0.sp - 200#64) ↦₆₄ v200) ∗ memRegion (s0.sp - 192#64) 24 ∗
        memRegion (s0.sp - 168#64) 48 ∗ memRegion (s0.sp - 120#64) 8 ∗
        memRegion (s0.sp - 112#64) 16 ∗ savedRegsAt s0 ∗ memRegion (s0.sp - 18704#64) 672 ∗
        A.pool lim st_cur st ∗ stackAt (s0.sp - 1648#64) extHookStack)
      (recvHdrChunkPlacedPostQOfPrePostEnv M A lim F PreEnv PostEnv x st0 s0 R)
      (recvHdrChunkPlacedPostQp F x s0 R) := by
  have h_drop := dropSortedSet16_placed_ok_at_recvHdr hC
  have h_tail920 :=
    @recv_hdr_chunk_tail_920_placed_wpp_ofPrePostEnv _ M A lim F PreEnv PostEnv ext
      hC x receivingHdr hdrFull cap_hdrFull ptr_hdrFull ptr_mac st0
  refine SepWPp.fold
    (cells11_entails_memRegion_88 s0.sp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10)
    (by sep_focus) ?_
  refine SepWPp.fold
    (polyDecoderNew1152RawAt_entails_polyDecoderAt A.repAlloc (s0.sp - 1136#64))
    (by sep_focus) ?_
  refine SepWPp.fold
    (polyDecoderAt_entails_sortedSet16_tail A.repAlloc (s0.sp - 1136#64) polyDecoderNew1152)
    (by sep_focus) ?_
  refine CryptoVerification.SpqrV1.Auth.SepWPp.pure_left_focus _ (by sep_focus) fun hlen16 => ?_
  refine SepWPp.fold (sp_736_80_expose s0.sp) (by sep_focus) ?_
  refine SepWPp.fold (out_480_err_expose x.outA) (by sep_focus) ?_
  sep_elim_exists
  rename_i w736 w728 w720 w704 w696 w688 u0 ub8 u9 u17 u25
  have hsp_norm : st.readReg64 .sp = s0.sp - 1648#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm hx19 hx20 hx21 hx22 hx23 hx26
  clear hC
  refine of_sepWP_lscro (mid := lsmpl.base 264) hinv ?_
  apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
    (Q := (blkPC_369).rebase (blkPl_369).base
      (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException (Rust.withPanics ext)))
    CryptoVerification.blkLib_eq_369 (mid := lsmpl.base 264)
  intro _m_strip
  wp_step; wp_step
  refine SepWP.fold (sp_696_realign s0.sp w696 w688) (by sep_focus) ?_
  wp_step; wp_step; wp_step; wp_step; wp_step
  refine SepWP.fold (sp_728_realign s0.sp w696 w720) (by sep_focus) ?_
  wp_step; wp_step
  refine SepWP.fold
    (sp_728_721_realign s0.sp w696 (overlapWord7 w696 w688))
    (by sep_focus) ?_
  wp_step; wp_step; wp_step
  refine SepWP.fold
    (out_17_25_realign x.outA (overlapLow7 w696 (overlapWord7 w696 w688)) u25)
    (by sep_focus) ?_
  wp_step; wp_step
  refine SepWP.fold
    (sp_736_80_collapse s0.sp w704
      (overlapLow7 w696 (overlapWord7 w696 w688))
      (overlapWord7 w696 w688)
      w704 w696 (overlapWord7 w696 w688))
    (by sep_focus) ?_
  refine SepWP.fold
    (out_480_err_collapse A.repAlloc x.outA w704
      (overlapLow7 w696 (overlapWord7 w696 w688))
      (overlapWord7 w696 w688)
      (x.self.recv_hdr_chunk x.epoch x.chunk) hres)
    (by sep_focus) ?_
  refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  refine prep_dropGlue_stack s0.sp (by sep_focus) (by simp only [wp_norm, arm64_norm, *]) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  wpp_call_lscro_recvHdr_budget h_drop
    ((⟨s0.sp - 1136#64, polyDecoderNew1152.pts.map SortedSetPt.vec⟩ : DropGlueSortedSetPt16Ghost),
     st_cur) hinv1
  try dsimp only [dropGlueSortedSetPt16Spec]
  refine SepWPp.rw_pre (by
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      polyArrayBytes, bv_sub_add_lit]; rfl) ?_
  apply SepWPp.exists_elim; intro evs_drop1152
  refine CryptoVerification.SpqrV1.Auth.SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨htr1, _, hfree_drop1152⟩
  refine unprep_dropGlue_stack s0.sp (by sep_focus) (by simp only [wp_norm, arm64_norm, *]) ?_
  refine SepWPp.fold (rejoin_sp_1160_1064 s0.sp v200) (by sep_focus) ?_
  have hst_drop1152 :
      M.stepEvents evs_drop1152 st_cur = M.stepEvents (evs_pre ++ evs_drop1152) st0 := by
    rw [hst_cur, ← M.stepEvents_append]
  have hpost_drop1152 :
      ∀ evs_free : List AllocEvent, FreeOnlyEvs evs_free →
        PostEnv x ((evs_pre ++ evs_drop1152) ++ evs_free) := by
    intro evs_free hf
    rw [List.append_assoc]
    exact hpost_free _ (FreeOnlyEvs.append hfree_drop1152 hf)
  refine SepWPp.rw_pre (by sep_ac_rfl)
    (h_tail920 (M.stepEvents evs_drop1152 st_cur) (evs_pre ++ evs_drop1152) s0 sf R
      hst_drop1152 hpost_drop1152 hge64 hmax_hdr
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

theorem recv_hdr_chunk_err_864_placed_wpp_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {Env : NoHeaderReceivedRecvHdrChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)} (hC : RecvHdrChunkContractsPlaced M A lim ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F) (receivingHdr : PolyDecoder) (hdrFull : Bytes)
    (cap_hdrFull ptr_hdrFull ptr_mac : BitVec 64)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v200 : BitVec 64)
    (st0 st_cur : M.σ) (evs_pre : List AllocEvent) (s0 st : State) (R : SepProp)
    (hst_cur : st_cur = M.stepEvents evs_pre st0)
    (hpost_free : ∀ evs_free : List AllocEvent, FreeOnlyEvs evs_free → Env x (evs_pre ++ evs_free))
    (hres : x.self.recv_hdr_chunk x.epoch x.chunk = .error (.err .macVerifyFailed))
    (hge64 : 64 ≤ hdrFull.length) (hmax_hdr : hdrFull.length < 2 ^ 63)
    (hpc : st.pc = (blkPl_369).base + 864#64) (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 1648#64) (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace) (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem) (hx19 : st.readReg64 .x19 = x.outA)
    (hx20 : st.readReg64 .x20 = cap_hdrFull) (hx21 : st.readReg64 .x21 = ptr_hdrFull)
    (hx22 : st.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64))
    (hx23 : st.readReg64 .x23 = ptr_mac) (hx26 : st.readReg64 .x26 = s0.sp - 736#64) :
    SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (vecBufAt A.repAlloc (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
        recvHdrChunkPlacedRoAt ∗ memRegion x.outA chunkedHeaderReceivedSize ∗
        memRegion x.selfA chunkedNoHeaderReceivedSize ∗ chunkAt x.chunkA x.chunk ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        ct2DeallocAt A.repAlloc cap_hdrFull ptr_hdrFull ∗
        ((s0.sp - 1648#64) ↦₆₄ v0) ∗ ((s0.sp - 1640#64) ↦₆₄ v1) ∗
        ((s0.sp - 1632#64) ↦₆₄ v2) ∗ ((s0.sp - 1624#64) ↦₆₄ v3) ∗
        ((s0.sp - 1616#64) ↦₆₄ v4) ∗ ((s0.sp - 1608#64) ↦₆₄ v5) ∗
        ((s0.sp - 1600#64) ↦₆₄ v6) ∗ ((s0.sp - 1592#64) ↦₆₄ v7) ∗
        ((s0.sp - 1584#64) ↦₆₄ v8) ∗ ((s0.sp - 1576#64) ↦₆₄ v9) ∗
        ((s0.sp - 1568#64) ↦₆₄ v10) ∗
        polyDecoderAt A.repAlloc (s0.sp - 1560#64) receivingHdr ∗
        memRegion (s0.sp - 1160#64) 24 ∗ polyDecoderNew1152RawAt A.repAlloc (s0.sp - 1136#64) ∗
        memRegion (s0.sp - 736#64) 80 ∗ memRegion (s0.sp - 656#64) 456 ∗
        ((s0.sp - 200#64) ↦₆₄ v200) ∗ memRegion (s0.sp - 192#64) 24 ∗
        memRegion (s0.sp - 168#64) 48 ∗ memRegion (s0.sp - 120#64) 8 ∗
        memRegion (s0.sp - 112#64) 16 ∗ savedRegsAt s0 ∗ memRegion (s0.sp - 18704#64) 672 ∗
        A.pool lim st_cur st ∗ stackAt (s0.sp - 1648#64) extHookStack)
      (recvHdrChunkPlacedPostQOfEnv M A lim F Env x st0 s0 R)
      (recvHdrChunkPlacedPostQp F x s0 R) :=
  recv_hdr_chunk_err_864_placed_wpp_ofPrePostEnv hC x receivingHdr hdrFull cap_hdrFull ptr_hdrFull
    ptr_mac v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v200 st0 st_cur evs_pre s0 st R hst_cur hpost_free
    hres hge64 hmax_hdr hpc hrun hsp hsp_s0 htr hvregs hinv hx19 hx20 hx21 hx22 hx23 hx26

theorem recv_hdr_chunk_err_864_placed_wpp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)} (hC : RecvHdrChunkContractsPlaced M A lim ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F) (receivingHdr : PolyDecoder) (hdrFull : Bytes)
    (cap_hdrFull ptr_hdrFull ptr_mac : BitVec 64)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v200 : BitVec 64)
    (st0 st_cur : M.σ) (evs_pre : List AllocEvent) (s0 st : State) (R : SepProp)
    (hst_cur : st_cur = M.stepEvents evs_pre st0)
    (hpost_free :
      ∀ evs_free : List AllocEvent, FreeOnlyEvs evs_free →
        NoHeaderReceivedRecvHdrChunkEnv x (evs_pre ++ evs_free))
    (hres : x.self.recv_hdr_chunk x.epoch x.chunk = .error (.err .macVerifyFailed))
    (hge64 : 64 ≤ hdrFull.length) (hmax_hdr : hdrFull.length < 2 ^ 63)
    (hpc : st.pc = (blkPl_369).base + 864#64) (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 1648#64) (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace) (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem) (hx19 : st.readReg64 .x19 = x.outA)
    (hx20 : st.readReg64 .x20 = cap_hdrFull) (hx21 : st.readReg64 .x21 = ptr_hdrFull)
    (hx22 : st.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64))
    (hx23 : st.readReg64 .x23 = ptr_mac) (hx26 : st.readReg64 .x26 = s0.sp - 736#64) :
    SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (vecBufAt A.repAlloc (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
        recvHdrChunkPlacedRoAt ∗ memRegion x.outA chunkedHeaderReceivedSize ∗
        memRegion x.selfA chunkedNoHeaderReceivedSize ∗ chunkAt x.chunkA x.chunk ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        ct2DeallocAt A.repAlloc cap_hdrFull ptr_hdrFull ∗
        ((s0.sp - 1648#64) ↦₆₄ v0) ∗ ((s0.sp - 1640#64) ↦₆₄ v1) ∗
        ((s0.sp - 1632#64) ↦₆₄ v2) ∗ ((s0.sp - 1624#64) ↦₆₄ v3) ∗
        ((s0.sp - 1616#64) ↦₆₄ v4) ∗ ((s0.sp - 1608#64) ↦₆₄ v5) ∗
        ((s0.sp - 1600#64) ↦₆₄ v6) ∗ ((s0.sp - 1592#64) ↦₆₄ v7) ∗
        ((s0.sp - 1584#64) ↦₆₄ v8) ∗ ((s0.sp - 1576#64) ↦₆₄ v9) ∗
        ((s0.sp - 1568#64) ↦₆₄ v10) ∗
        polyDecoderAt A.repAlloc (s0.sp - 1560#64) receivingHdr ∗
        memRegion (s0.sp - 1160#64) 24 ∗ polyDecoderNew1152RawAt A.repAlloc (s0.sp - 1136#64) ∗
        memRegion (s0.sp - 736#64) 80 ∗ memRegion (s0.sp - 656#64) 456 ∗
        ((s0.sp - 200#64) ↦₆₄ v200) ∗ memRegion (s0.sp - 192#64) 24 ∗
        memRegion (s0.sp - 168#64) 48 ∗ memRegion (s0.sp - 120#64) 8 ∗
        memRegion (s0.sp - 112#64) 16 ∗ savedRegsAt s0 ∗ memRegion (s0.sp - 18704#64) 672 ∗
        A.pool lim st_cur st ∗ stackAt (s0.sp - 1648#64) extHookStack)
      (recvHdrChunkPlacedPostQ M A lim F x st0 s0 R)
      (recvHdrChunkPlacedPostQp F x s0 R) :=
  recv_hdr_chunk_err_864_placed_wpp_ofEnv hC x receivingHdr hdrFull cap_hdrFull ptr_hdrFull
    ptr_mac v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v200 st0 st_cur evs_pre s0 st R hst_cur hpost_free
    hres hge64 hmax_hdr hpc hrun hsp hsp_s0 htr hvregs hinv hx19 hx20 hx21 hx22 hx23 hx26

end LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart5PlacedBudget
