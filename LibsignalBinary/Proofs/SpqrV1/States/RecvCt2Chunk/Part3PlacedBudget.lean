/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import Lean -- shake: keep
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
meta import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlacedBudget -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.SpqrV1.Drop.SortedSetPtBudget
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp

/-!
# `<EkSentCt1Received>::recv_ct2_chunk` (Block `350`): Budget Epilogue & `Err(MacVerifyFailed)`

Relocatable `[LibsignalPlacement]` `RustCliAllocBudget` proof of the shared `Some`-branch epilogue
(`+1188 .. +1244`), `Err(MacVerifyFailed)` write-out, and 9-buffer deallocation chain (`+968 .. +1140`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part3PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement blkLib_eq_350 blkPC_350 blkPl_350 lsProg_350 lsmpl lsρ)
open CryptoVerification.LibsignalSpqrV1 (
  Authenticator Bytes MlKem NUM_POLYS PolyDecoder spqrAuthApi spqrHkdfWith spqrPolyApi
)
open CryptoVerification.LibsignalTripleRatchet (LibsignalCodeRoLoaded extHookStack)
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.SpqrV1.Auth (AuthenticatorGhost vecBufAt)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt_false bytesAt_true)
open CryptoVerification.SpqrV1.Drop (
  DropGlueSortedSetPt16Ghost chunkedEkSentCt1ReceivedSize dropGluePoly16Stack
  polyDecoderAt_entails_vecs_tail polyDecoder_post_join
)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly (chunkAt polyDecoderAt)
open CryptoVerification.SpqrV1.States.RecvCt2Chunk (
  Ct2DeallocProp RecvCt2ChunkGhost b7 bytes_rem_entails_ct2DeallocAt cells9_sp_2496_fold
  ct2DeallocAt ct2DeallocAt_expose ekSentCt1ReceivedRecvChunkResultAt left_and_low7_to_mid_at_7
  low7At memRegion_144_x20_split memRegion_24_split_23_1 memRegion_outA_err_split mid7At
  mid_at_7_to_left recvCt2ChunkStackX recvCt2RoPlacedAt rejoin_activeFrameRegionsAt_epilogue
  rejoin_memRegion_24_left rejoin_memRegion_24_mid rejoin_memRegion_24_sp_1280
  rejoin_memRegion_32_sp_152 rejoin_memRegion_48_sp_1328 rejoin_outA_err rejoin_someBranchFrameAt
  rejoin_stack_polyDecodedMessage_from_extHook rejoin_stack_recvCt2Chunk savedRegsAt setByte7
  someBranchFrameAt spqrRustDeallocSym' stackAt_extHook_eq_dropGluePoly16 unshiftWord8
  unusedFrameAt vecBufAt_entails_memRegion_live vecU8At_expose_sp_1328
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
  RustLayoutOk rustCliDeallocBudgetExternSpecWithStack rustDeallocEvents
)
open LibsignalBinary.Proofs.SpqrV1.Drop.SortedSetPtBudget (dropGlueSortedSetPt16Spec)
open LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlacedBudget (
  RecvCt2PlacedAlloc freeOnlyEvs_rustDealloc1 recvCt2ChunkPlacedSpecOfPrePostEnv
  recvCt2PlacedPostQOfPrePostEnv recvCt2PlacedPostQp sepWPp_of_sepWP_lscro
)

private theorem rustLayoutOk_one {n : Nat} (hpos : 0 < n) (hmax : n < 2 ^ 63) :
    RustLayoutOk n 1 :=
  ⟨⟨hpos, ⟨0, rfl⟩, by omega⟩, by decide⟩

private theorem sepWPp_rw_pre {prog : Program} {ret : BitVec 64} {s : State} {P P' : SepProp}
    {Q Qp : State → SepProp → Prop} (hP : P = P') (h : SepWPp prog ret s P' Q Qp) :
    SepWPp prog ret s P Q Qp :=
  hP ▸ h

private theorem sepWPp_rw_pre' {prog : Program} {ret : BitVec 64} {s : State} {P P' : SepProp}
    {Q Qp : State → SepProp → Prop} (h : SepWPp prog ret s P' Q Qp) (hP : P = P') :
    SepWPp prog ret s P Q Qp :=
  hP ▸ h

private theorem sepWPp_pure_left_focus {prog : Program} {pc : BitVec 64} {s : State}
    {P P' : SepProp} {post post_err : State → SepProp → Prop} (φ : Prop)
    (hf : P = ⌜φ⌝ ∗ P')
    (h : φ → SepWPp prog pc s P' post post_err) :
    SepWPp prog pc s P post post_err := by
  intro R hm hL
  rw [hf, sepConj_assoc, satisfies_pure_sepConj] at hm
  exact (h hm.1) R hm.2 hL

private theorem close_epilogue_post [LibsignalPlacement] {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    {x : RecvCt2ChunkGhost F} {st0 : M.σ} {s0 sf : State} {P_f R : SepProp}
    (evs_all : List AllocEvent)
    (htr : sf.trace = s0.trace)
    (hpost : PostEnv x evs_all)
    (hsp : sf.sp = s0.sp)
    (hcs : CalleeSavedPreserved s0 sf)
    (hP : P_f =
      recvCt2RoPlacedAt ∗
        ekSentCt1ReceivedRecvChunkResultAt A.repAlloc x.outA
          (x.self.recv_ct2_chunk K x.epoch x.chunk) ∗
        memRegion x.selfA chunkedEkSentCt1ReceivedSize ∗
        chunkAt x.chunkA x.chunk ∗
        tokenInitPlacedAt ∗
        reduceTablePlacedAt ∗
        A.pool lim (M.stepEvents evs_all st0) sf ∗
        stackAt s0.sp recvCt2ChunkStackX) :
    recvCt2PlacedPostQOfPrePostEnv K F M A lim PreEnv PostEnv x st0 s0 R sf P_f := by
  refine ⟨fun hm => ?_, hsp, hcs⟩
  subst hP
  dsimp only [recvCt2PlacedPostQOfPrePostEnv, recvCt2ChunkPlacedSpecOfPrePostEnv,
    LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsPlacedBudget.recvCt2ChunkPlacedSpecOfPrePostEnv,
    LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsBudget.recvCt2ChunkPlacedSpecOfPrePostEnv]
  simp only [sepExists_sepConj_right, sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨evs_all, ?_⟩
  have hm' : sf.mem ⊨
      ⌜sf.trace = s0.trace ∧ PostEnv x evs_all⌝ ∗
        (recvCt2RoPlacedAt ∗
          ekSentCt1ReceivedRecvChunkResultAt A.repAlloc x.outA
            (x.self.recv_ct2_chunk K x.epoch x.chunk) ∗
          memRegion x.selfA chunkedEkSentCt1ReceivedSize ∗
          chunkAt x.chunkA x.chunk ∗
          tokenInitPlacedAt ∗
          reduceTablePlacedAt ∗
          A.pool lim (M.stepEvents evs_all st0) sf ∗
          stackAt s0.sp recvCt2ChunkStackX ∗ R) :=
    (satisfies_pure_sepConj _ _ _).mpr
      ⟨⟨htr, hpost⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm⟩
  exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm'

local macro "sep_elim_exists" : tactic =>
  `(tactic| (
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    repeat' (first | (apply SepWPp.exists_elim; intro _) | (apply SepWP.exists_elim; intro _))))

local macro "wp_steps_sync_pool_350 " ext:term:max mid:term:max : tactic =>
  `(tactic| (
    apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
      (Q := (blkPC_350).rebase (blkPl_350).base
        (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException (Rust.withPanics $ext)))
      blkLib_eq_350 (mid := $mid)
    intro _m_strip
    wp_steps
    refine SepWP.done (by wp_norm_goal) (by wp_norm_goal) fun _m_real _hnsp => ?_
    refine ProofLib.SepWP.transport_budgetPool (_hnsp.toVmPreserved (by wp_norm_goal)) (hnext := ?_)
    simp only [State.setMem_setMem]))

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  spqrHkdfWith
  CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.EkSentCt1Received.recv_ct2_chunk
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  bytesAt_true bytesAt_false

local elab "erase_hkdf_sp_norm" : command =>
  Lean.Elab.Command.liftCoreM do
    for nm in [
      ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp,
      ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp,
      ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592,
      ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
    ] do
      try Lean.Attribute.erase nm `arm64_norm catch _ => pure ()

erase_hkdf_sp_norm

/-! ## Shared `Some`-Branch Epilogue (`+1188 .. +1244`) -/

set_option maxHeartbeats 1200000 in
theorem recv_ct2_chunk_epilogue_placed_wpp [LibsignalPlacement] {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (x : RecvCt2ChunkGhost F)
    (st0 σ : M.σ)
    (receivingCt2 : PolyDecoder) (cap_ct2 ptr_ct2 : BitVec 64)
    (s0 st : State) (R : SepProp)
    (hpost_env : ∀ evs_ep : List AllocEvent, FreeOnlyEvs evs_ep →
      ∃ evs_all : List AllocEvent, PostEnv x evs_all ∧
        M.stepEvents evs_ep σ = M.stepEvents evs_all st0)
    (hpc : st.pc = (blkPl_350).base + 1188#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 2496#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx21 : st.readReg64 .x21 = ptr_ct2)
    (hx24 : st.readReg64 .x24 = cap_ct2) :
    SepWPp (lsProg_350 (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (ct2DeallocAt A.repAlloc cap_ct2 ptr_ct2 ∗
        polyDecoderAt A.repAlloc (s0.sp - 2424#64) receivingCt2 ∗
        cells (s0.sp - 2496#64) 9 ∗
        memRegion (s0.sp - 2024#64) 24 ∗
        memRegion (s0.sp - 1856#64) 504 ∗
        someBranchFrameAt (s0.sp - 2496#64) ∗
        memRegion (s0.sp - 19552#64) 672 ∗
        savedRegsAt s0 ∗
        recvCt2RoPlacedAt ∗
        ekSentCt1ReceivedRecvChunkResultAt A.repAlloc x.outA
          (x.self.recv_ct2_chunk K x.epoch x.chunk) ∗
        memRegion x.selfA chunkedEkSentCt1ReceivedSize ∗
        chunkAt x.chunkA x.chunk ∗
        tokenInitPlacedAt ∗
        reduceTablePlacedAt ∗
        A.pool lim σ st ∗
        stackAt (s0.sp - 2496#64) extHookStack)
      (recvCt2PlacedPostQOfPrePostEnv K F M A lim PreEnv PostEnv x st0 s0 R)
      (recvCt2PlacedPostQp K x s0 R) := by
  have h_dealloc := hA.dealloc_lscro
  dsimp only [LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
    rustCliDeallocBudgetExternSpecWithStack] at h_dealloc
  have h_drop := hA.dropSortedSetPt16_lscro
  dsimp only [dropGlueSortedSetPt16Spec] at h_drop
  dsimp only [ct2DeallocAt]
  refine sepWPp_pure_left_focus (cap_ct2 ≠ 0#64 ∧ cap_ct2.toNat < 2 ^ 63 ∧ ptr_ct2 ≠ 0#64)
    (by sep_focus) fun ⟨hcap_ct2_ne, hmax_ct2, hptr_ct2_ne⟩ => ?_
  have hcap_ct2_pos : 0 < cap_ct2.toNat := by
    apply Nat.pos_of_ne_zero
    intro h0
    exact hcap_ct2_ne (BitVec.eq_of_toNat_eq (by rw [h0]; rfl))
  have hrlay_ct2 : RustLayoutOk cap_ct2.toNat 1 := rustLayoutOk_one hcap_ct2_pos hmax_ct2
  have hsp_norm : st.readReg64 .sp = s0.sp - 2496#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm hvregs
  clear hA
  simp only [lsProg_350] at h_dealloc h_drop ⊢
  refine sepWPp_of_sepWP_lscro (mid := lsρ spqrRustDeallocSym') hinv ?_
  wp_steps_sync_pool_350 ext (lsρ spqrRustDeallocSym')
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  wpp_call_lscro_recvCt2_budget h_dealloc (ptr_ct2, cap_ct2.toNat, 1, σ) hinv1
  conv => arg 4; simp only [State.sp, hsp_sf, hsp, hsp_norm, wp_norm, arm64_norm]
  refine sepWPp_pure_left_focus (sf.trace = _) (by sep_focus) fun htr1 => ?_
  have hsp_sf_norm : sf.readReg64 .sp = s0.sp - 2496#64 := by
    simp only [State.sp, wp_norm, arm64_norm, *]
  simp only [wp_norm, arm64_norm] at hsp_sf_norm
  have hstack_sf :
      stackAt (s0.sp - 2496#64) extHookStack ⊢
        memRegion (s0.sp - 18880#64) 12256 ∗ stackAt (s0.sp - 2496#64) dropGluePoly16Stack := by
    rw [← stackAt_extHook_eq_dropGluePoly16 s0.sp]
    exact Entails.refl _
  refine SepWPp.fold hstack_sf (by sep_focus) ?_
  refine SepWPp.fold
    (polyDecoderAt_entails_vecs_tail A.repAlloc (s0.sp - 2424#64) receivingCt2)
    (by sep_focus) ?_
  sep_elim_exists
  rename_i vecs
  refine sepWPp_pure_left_focus (vecs.length = NUM_POLYS) (by sep_focus) fun hvecs_len => ?_
  refine sepWPp_of_sepWP_lscro (mid := lsmpl.base 264) hF_sf ?_
  wp_steps_sync_pool_350 ext (lsmpl.base 264)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv2
  wpp_call_lscro_recvCt2_budget h_drop
    ((⟨s0.sp - 2424#64, vecs⟩ : DropGlueSortedSetPt16Ghost),
      M.stepEvents (rustDeallocEvents cap_ct2.toNat 1) σ)
    hinv2
  conv => arg 4; simp only [State.sp, hsp_sf_1, hsp_sf, hsp, hsp_norm, hsp_sf_norm, wp_norm, arm64_norm]
  refine sepWPp_rw_pre (emp_sepConj _).symm ?_
  sep_elim_exists
  rename_i evs_drop
  refine sepWPp_rw_pre (emp_sepConj _) ?_
  refine sepWPp_pure_left_focus (sf_1.trace = _ ∧ AllocCallPreserved _ sf_1 ∧ _)
    (by sep_focus) ?_
  rintro ⟨htr2, _, hfree_drop⟩
  obtain ⟨evs_all, hpost_all, hstep_all⟩ :=
    hpost_env (rustDeallocEvents cap_ct2.toNat 1 ++ evs_drop)
      ((freeOnlyEvs_rustDealloc1 cap_ct2.toNat).append hfree_drop)
  have hstep_ep :
      M.stepEvents evs_drop (M.stepEvents (rustDeallocEvents cap_ct2.toNat 1) σ) =
        M.stepEvents evs_all st0 :=
    (M.stepEvents_append (rustDeallocEvents cap_ct2.toNat 1) evs_drop σ).symm.trans hstep_all
  rw [hstep_ep]
  have hstack_back :
      memRegion (s0.sp - 18880#64) 12256 ∗ stackAt (s0.sp - 2496#64) dropGluePoly16Stack ⊢
        stackAt (s0.sp - 2496#64) extHookStack := by
    rw [← stackAt_extHook_eq_dropGluePoly16 s0.sp]
    exact Entails.refl _
  refine SepWPp.fold hstack_back (by sep_focus) ?_
  refine SepWPp.fold (polyDecoder_post_join (s0.sp - 2424#64)) (by sep_focus) ?_
  change SepWPp ((blkPC_350).rebase (blkPl_350).base (Rust.withPanics ext))
    (s0.readReg64 .x30) sf_1 (memRegion (s0.sp - 2424#64) 400 ∗ _) _ _
  refine SepWPp.fold (rejoin_activeFrameRegionsAt_epilogue s0.sp) (by sep_focus) ?_
  refine SepWPp.fold (rejoin_stack_polyDecodedMessage_from_extHook s0.sp) (by sep_focus) ?_
  have hsp_sf1_norm : sf_1.readReg64 .sp = s0.sp - 2496#64 := by
    simp only [State.sp, wp_norm, arm64_norm, *]
  simp only [wp_norm, arm64_norm] at hsp_sf1_norm
  apply SepWPp.of_sepWP_ret
  unfold savedRegsAt
  wp_steps_sync_pool_350 ext (s0.readReg64 .x30)
  have hfold_saved :
      ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
      ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ⊢
      savedRegsAt s0 := Entails.refl _
  refine SepWP.fold hfold_saved (by sep_focus) ?_
  refine SepWP.fold (rejoin_stack_recvCt2Chunk s0) (by sep_focus) ?_
  refine SepWP.done (by wp_norm_goal) (by wp_norm_goal) ?_
  refine close_epilogue_post evs_all
    (by simp only [wp_norm, arm64_norm, *])
    hpost_all
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [CalleeSavedPreserved, wp_norm, arm64_norm, *])
    (by sep_ac_rfl)

/-! ## Write Out `Err(MacVerifyFailed)` (`+1140 .. +1188`) -/

set_option maxHeartbeats 1200000 in
theorem recv_ct2_chunk_err_write_out_placed_wpp [LibsignalPlacement] {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (x : RecvCt2ChunkGhost F)
    (st0 σ : M.σ)
    (receivingCt2 : PolyDecoder) (cap_ct2 ptr_ct2 : BitVec 64)
    (s0 st : State) (R : SepProp)
    (hpost_env : ∀ evs_ep : List AllocEvent, FreeOnlyEvs evs_ep →
      ∃ evs_all : List AllocEvent, PostEnv x evs_all ∧
        M.stepEvents evs_ep σ = M.stepEvents evs_all st0)
    (hres : x.self.recv_ct2_chunk K x.epoch x.chunk = .error (.err .macVerifyFailed))
    (hpc : st.pc = (blkPl_350).base + 1140#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 2496#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx19 : st.readReg64 .x19 = x.outA)
    (hx20 : st.readReg64 .x20 = s0.sp - 2000#64)
    (hx21 : st.readReg64 .x21 = ptr_ct2)
    (hx24 : st.readReg64 .x24 = cap_ct2) :
    SepWPp (lsProg_350 (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (ct2DeallocAt A.repAlloc cap_ct2 ptr_ct2 ∗
        memRegion x.outA chunkedEkSentCt1ReceivedSize ∗
        memRegion (s0.sp - 2000#64) 144 ∗
        memRegion (s0.sp - 1344#64) 16 ∗
        memRegion (s0.sp - 1328#64) 48 ∗
        memRegion (s0.sp - 1280#64) 24 ∗
        memRegion (s0.sp - 1248#64) 960 ∗
        memRegion (s0.sp - 288#64) 128 ∗
        memRegion (s0.sp - 152#64) 32 ∗
        unusedFrameAt (s0.sp - 2496#64) ∗
        memRegion (s0.sp - 1856#64) 504 ∗
        polyDecoderAt A.repAlloc (s0.sp - 2424#64) receivingCt2 ∗
        cells (s0.sp - 2496#64) 9 ∗
        memRegion (s0.sp - 2024#64) 24 ∗
        memRegion (s0.sp - 19552#64) 672 ∗
        savedRegsAt s0 ∗
        recvCt2RoPlacedAt ∗
        memRegion x.selfA chunkedEkSentCt1ReceivedSize ∗
        chunkAt x.chunkA x.chunk ∗
        tokenInitPlacedAt ∗
        reduceTablePlacedAt ∗
        A.pool lim σ st ∗
        stackAt (s0.sp - 2496#64) extHookStack)
      (recvCt2PlacedPostQOfPrePostEnv K F M A lim PreEnv PostEnv x st0 s0 R)
      (recvCt2PlacedPostQp K x s0 R) := by
  have hep :=
    @recv_ct2_chunk_epilogue_placed_wpp _ K F M A lim PreEnv PostEnv ext hA x st0 σ
      receivingCt2 cap_ct2 ptr_ct2 s0
  dsimp only [ct2DeallocAt]
  refine sepWPp_pure_left_focus (cap_ct2 ≠ 0#64 ∧ cap_ct2.toNat < 2 ^ 63 ∧ ptr_ct2 ≠ 0#64)
    (by sep_focus) fun ⟨hcap_ct2_ne, hmax_ct2, hptr_ct2_ne⟩ => ?_
  have hcap_ct2_beq : (cap_ct2 == 0#64) = false := beq_false_of_ne hcap_ct2_ne
  have hfold_ct2 :
      memRegion ptr_ct2 cap_ct2.toNat ∗ A.repAlloc.live ptr_ct2 cap_ct2.toNat 1 ⊢
        ct2DeallocAt A.repAlloc cap_ct2 ptr_ct2 := by
    dsimp only [ct2DeallocAt]
    exact Entails.pure_right ⟨hcap_ct2_ne, hmax_ct2, hptr_ct2_ne⟩ (Entails.refl _)
  refine SepWPp.fold hfold_ct2 (by sep_focus) ?_
  refine SepWPp.fold (memRegion_outA_err_split x.outA) (by sep_focus) ?_
  sep_elim_exists
  rename_i o0 ob8 o9 o17 o25
  refine sepWPp_rw_pre (by rw [memRegion_144_x20_split s0.sp]) ?_
  refine SepWPp.fold (memRegion_24_split_23_1 (s0.sp - 2000#64)) (by sep_focus) ?_
  sep_elim_exists
  rename_i u0 u1 u2
  refine SepWPp.fold (memRegion_24_split_23_1 (s0.sp - 1968#64)) (by sep_focus) ?_
  sep_elim_exists
  rename_i v0 v1 v2
  have ha0 : (s0.sp - 2000#64) + 8#64 = s0.sp - 1992#64 := by bv_omega
  have ha1 : (s0.sp - 2000#64) + 16#64 = s0.sp - 1984#64 := by bv_omega
  have ha2 : (s0.sp - 2000#64) + 23#64 = s0.sp - 1977#64 := by bv_omega
  have hb0 : (s0.sp - 1968#64) + 8#64 = s0.sp - 1960#64 := by bv_omega
  have hb1 : (s0.sp - 1968#64) + 16#64 = s0.sp - 1952#64 := by bv_omega
  have hb2 : (s0.sp - 1968#64) + 23#64 = s0.sp - 1945#64 := by bv_omega
  refine sepWPp_rw_pre (by simp only [ha0, ha1, ha2, hb0, hb1, hb2]; try rfl) ?_
  have hsp_norm : st.readReg64 .sp = s0.sp - 2496#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm hx19 hx20 hx21 hx24
  clear hA
  simp only [lsProg_350] at hep ⊢
  refine sepWPp_of_sepWP_lscro (mid := (blkPl_350).base + 1188#64) hinv ?_
  apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
    (Q := (blkPC_350).rebase (blkPl_350).base
      (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException (Rust.withPanics ext)))
    blkLib_eq_350 (mid := (blkPl_350).base + 1188#64)
  intro _m_strip
  wp_step; wp_step
  have hshift_b :=
    left_and_low7_to_mid_at_7 (s0.sp - 1960#64) (s0.sp - 1953#64) (s0.sp - 1952#64)
      v1 v2 (by bv_omega) (by bv_omega)
  refine SepWP.fold (Entails.of_eq hshift_b) (by sep_focus) ?_
  wp_step; wp_step; wp_step; wp_step
  have hshift_a1 :=
    left_and_low7_to_mid_at_7 (s0.sp - 1992#64) (s0.sp - 1985#64) (s0.sp - 1984#64)
      v1 u2 (by bv_omega) (by bv_omega)
  refine SepWP.fold (Entails.of_eq hshift_a1) (by sep_focus) ?_
  wp_step
  have hshift_a2 :=
    mid_at_7_to_left (s0.sp - 1992#64) (s0.sp - 1985#64) (s0.sp - 1984#64)
      v1 (unshiftWord8 v1 v2) (by bv_omega) (by bv_omega)
  refine SepWP.fold (Entails.of_eq hshift_a2) (by sep_focus) ?_
  wp_step; wp_step; wp_step
  have hshift_out :=
    left_and_low7_to_mid_at_7 (x.outA + 17#64) (x.outA + 24#64) (x.outA + 25#64)
      (setByte7 v1 (unshiftWord8 v1 v2)) o25 (by bv_omega) (by bv_omega)
  refine SepWP.fold (Entails.of_eq hshift_out) (by sep_focus) ?_
  wp_step; wp_step
  have hrejoin_out := rejoin_outA_err A.repAlloc (F := F) x.outA
    v0 (setByte7 v1 (unshiftWord8 v1 v2)) (unshiftWord8 v1 v2)
  rw [← hres] at hrejoin_out
  refine SepWP.fold hrejoin_out (by sep_focus) ?_
  have hrejoin_a :
      ((s0.sp - 2000#64) ↦₆₄ v0) ∗ ((s0.sp - 1992#64) ↦₆₄ setByte7 v1 (unshiftWord8 v1 v2)) ∗
      mid7At (s0.sp - 1984#64) (unshiftWord8 v1 v2) ∗ ((s0.sp - 1977#64) ↦₈ b7 u2) ⊢
      memRegion (s0.sp - 2000#64) 24 := by
    have h := rejoin_memRegion_24_left (s0.sp - 2000#64) v0
      (setByte7 v1 (unshiftWord8 v1 v2)) (unshiftWord8 v1 v2) (b7 u2)
    rwa [ha0, ha1, ha2] at h
  have hrejoin_b :
      ((s0.sp - 1968#64) ↦₆₄ v0) ∗ low7At (s0.sp - 1960#64) v1 ∗
      ((s0.sp - 1953#64) ↦₆₄ unshiftWord8 v1 v2) ∗ ((s0.sp - 1945#64) ↦₈ b7 v2) ⊢
      memRegion (s0.sp - 1968#64) 24 := by
    have h := rejoin_memRegion_24_mid (s0.sp - 1968#64) v0 v1 (unshiftWord8 v1 v2) (b7 v2)
    have h15 : (s0.sp - 1968#64) + 15#64 = s0.sp - 1953#64 := by bv_omega
    rwa [hb0, h15, hb2] at h
  refine SepWP.fold hrejoin_a (by sep_focus) ?_
  refine SepWP.fold hrejoin_b (by sep_focus) ?_
  have hrejoin_144 :
      memRegion (s0.sp - 2000#64) 24 ∗ memRegion (s0.sp - 1976#64) 8 ∗
      memRegion (s0.sp - 1968#64) 24 ∗ memRegion (s0.sp - 1944#64) 88 ⊢
      memRegion (s0.sp - 2000#64) 144 :=
    Entails.of_eq (memRegion_144_x20_split s0.sp).symm
  refine SepWP.fold hrejoin_144 (by sep_focus) ?_
  refine SepWP.fold (rejoin_someBranchFrameAt s0.sp) (by sep_focus) ?_
  refine SepWP.done (by wp_norm_goal) (by wp_norm_goal) fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool (_hnsp.toVmPreserved (by wp_norm_goal)) (hnext := ?_)
  simp only [State.setMem_setMem]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  refine sepWPp_rw_pre'
    (hep _ R hpost_env
      (by wp_norm_goal) (by wp_norm_goal)
      (by simp only [wp_norm, arm64_norm, *]) hsp_s0
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      hinv1
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]))
    (by sep_ac_rfl)

/-! ## `Err(MacVerifyFailed)` Deallocation Chain (`+968 .. +1140`) -/

set_option maxHeartbeats 1600000 in
theorem recv_ct2_chunk_err_placed_wpp [LibsignalPlacement] {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (x : RecvCt2ChunkGhost F)
    (st0 σ : M.σ)
    (receivingCt2 : PolyDecoder) (ct2Full ss_raw ss : Bytes)
    (auth' : Authenticator) (g_auth' : AuthenticatorGhost)
    (cap_ct2 ptr_ct2 cap_dk ptr_dk cap_ct1' ptr_ct1'
      cap_info ptr_info ptr_ss_raw ptr_ss ptr_mac ptr_ct2_128 : BitVec 64)
    (s0 st : State) (R : SepProp)
    (hpost_env : ∀ evs_err : List AllocEvent, FreeOnlyEvs evs_err →
      ∃ evs_all : List AllocEvent, PostEnv x evs_all ∧
        M.stepEvents evs_err σ = M.stepEvents evs_all st0)
    (hres : x.self.recv_ct2_chunk K x.epoch x.chunk = .error (.err .macVerifyFailed))
    (hgt128 : 128 < ct2Full.length)
    (hmax_ct2 : ct2Full.length < 2 ^ 63)
    (hss_raw_len : ss_raw.length = 32)
    (hss_len : ss.length = 32)
    (htake128_len : (ct2Full.take 128).length = 128)
    (hrk_len : auth'.rootKey.length = 32)
    (hmk_len : auth'.macKey.length = 32)
    (hmk_cap_ne : g_auth'.macKey.cap ≠ 0#64)
    (hmk_le : 32 ≤ g_auth'.macKey.cap.toNat)
    (hmk_max : g_auth'.macKey.cap.toNat < 2 ^ 63)
    (hmk_ptr_ne : g_auth'.macKey.ptr ≠ 0#64)
    (hpc : st.pc = (blkPl_350).base + 968#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 2496#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx19 : st.readReg64 .x19 = x.outA)
    (hx20 : st.readReg64 .x20 = s0.sp - 2000#64)
    (hx21 : st.readReg64 .x21 = ptr_ct2)
    (hx23 : st.readReg64 .x23 = BitVec.ofNat 64 (ct2Full.length - 128))
    (hx24 : st.readReg64 .x24 = ptr_ss_raw)
    (hx25 : st.readReg64 .x25 = ptr_ct2_128)
    (hx27 : st.readReg64 .x27 = ptr_ss)
    (hx29 : st.readReg64 .x29 = s0.sp - 96#64) :
    SepWPp (lsProg_350 (Rust.withPanics ext)) (s0.readReg64 .x30) st
      ((ptr_ss ↦ₛ ss) ∗ A.live ptr_ss 32 1 ∗
        ct2DeallocAt A.repAlloc cap_info ptr_info ∗
        ((s0.sp - 152#64) ↦₆₄ cap_info) ∗ ((s0.sp - 144#64) ↦₆₄ ptr_info) ∗
        ((s0.sp - 136#64) ↦₆₄ 41#64) ∗ memRegion (s0.sp - 128#64) 8 ∗
        (ptr_ss_raw ↦ₛ ss_raw) ∗ A.live ptr_ss_raw 32 1 ∗
        ((s0.sp - 1280#64) ↦₆₄ cap_ct1') ∗ ((s0.sp - 1272#64) ↦₆₄ ptr_ct1') ∗
        ((s0.sp - 1264#64) ↦₆₄ 960#64) ∗ ct2DeallocAt A.repAlloc cap_ct1' ptr_ct1' ∗
        ct2DeallocAt A.repAlloc cap_dk ptr_dk ∗
        vecU8At A.repAlloc (s0.sp - 1328#64) g_auth'.rootKey.cap g_auth'.rootKey.ptr auth'.rootKey ∗
        ((s0.sp - 1304#64) ↦₆₄ g_auth'.macKey.cap) ∗ ((s0.sp - 1296#64) ↦₆₄ g_auth'.macKey.ptr) ∗
        ((s0.sp - 1288#64) ↦₆₄ 32#64) ∗ (g_auth'.macKey.ptr ↦ₛ auth'.macKey) ∗
        memRegion (g_auth'.macKey.ptr + 32#64) (g_auth'.macKey.cap.toNat - 32) ∗
        A.live g_auth'.macKey.ptr g_auth'.macKey.cap.toNat 1 ∗
        vecBufAt A.repAlloc (BitVec.ofNat 64 (ct2Full.length - 128)) ptr_mac (ct2Full.drop 128) ∗
        (ptr_ct2_128 ↦ₛ ct2Full.take 128) ∗ A.live ptr_ct2_128 128 1 ∗
        ((s0.sp - 2496#64) ↦₆₄ g_auth'.macKey.ptr) ∗ ((s0.sp - 2488#64) ↦₆₄ ptr_dk) ∗
        ((s0.sp - 2480#64) ↦₆₄ BitVec.ofNat 64 ct2Full.length) ∗
        ((s0.sp - 2472#64) ↦₆₄ ptr_info) ∗ ((s0.sp - 2464#64) ↦₆₄ cap_ct2) ∗
        ((s0.sp - 2456#64) ↦₆₄ cap_dk) ∗ ((s0.sp - 2448#64) ↦₆₄ ptr_mac) ∗
        ((s0.sp - 2440#64) ↦₆₄ ptr_ct1') ∗ ((s0.sp - 2432#64) ↦₆₄ x.epoch) ∗
        ct2DeallocAt A.repAlloc cap_ct2 ptr_ct2 ∗
        memRegion x.outA chunkedEkSentCt1ReceivedSize ∗
        memRegion (s0.sp - 2000#64) 144 ∗ memRegion (s0.sp - 1344#64) 16 ∗
        memRegion (s0.sp - 1248#64) 960 ∗ memRegion (s0.sp - 288#64) 128 ∗
        unusedFrameAt (s0.sp - 2496#64) ∗ memRegion (s0.sp - 1856#64) 504 ∗
        polyDecoderAt A.repAlloc (s0.sp - 2424#64) receivingCt2 ∗
        memRegion (s0.sp - 2024#64) 24 ∗
        memRegion (s0.sp - 19552#64) 672 ∗ savedRegsAt s0 ∗ recvCt2RoPlacedAt ∗
        memRegion x.selfA chunkedEkSentCt1ReceivedSize ∗ chunkAt x.chunkA x.chunk ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool lim σ st ∗
        stackAt (s0.sp - 2496#64) extHookStack)
      (recvCt2PlacedPostQOfPrePostEnv K F M A lim PreEnv PostEnv x st0 s0 R)
      (recvCt2PlacedPostQp K x s0 R) := by
  have h_dealloc := hA.dealloc_lscro
  dsimp only [LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
    rustCliDeallocBudgetExternSpecWithStack] at h_dealloc
  have hss_mr : (ptr_ss ↦ₛ ss) ⊢ memRegion ptr_ss 32 := by
    rw [← hss_len]; exact pointsToBytes_entails_memRegion ptr_ss ss
  have hss_raw_mr : (ptr_ss_raw ↦ₛ ss_raw) ⊢ memRegion ptr_ss_raw 32 := by
    rw [← hss_raw_len]; exact pointsToBytes_entails_memRegion ptr_ss_raw ss_raw
  have hct2_128_mr : (ptr_ct2_128 ↦ₛ ct2Full.take 128) ⊢ memRegion ptr_ct2_128 128 := by
    have h := pointsToBytes_entails_memRegion ptr_ct2_128 (ct2Full.take 128)
    rwa [htake128_len] at h
  have hmk_dealloc :
      (g_auth'.macKey.ptr ↦ₛ auth'.macKey) ∗
        memRegion (g_auth'.macKey.ptr + 32#64) (g_auth'.macKey.cap.toNat - 32) ∗
        A.live g_auth'.macKey.ptr g_auth'.macKey.cap.toNat 1 ⊢
      ct2DeallocAt A.repAlloc g_auth'.macKey.cap g_auth'.macKey.ptr := by
    have h := bytes_rem_entails_ct2DeallocAt A.repAlloc g_auth'.macKey.cap g_auth'.macKey.ptr
      auth'.macKey (by omega) hmk_max hmk_ptr_ne hmk_cap_ne
    rwa [hmk_len] at h
  have hmac_mr_live :
      vecBufAt A.repAlloc (BitVec.ofNat 64 (ct2Full.length - 128)) ptr_mac (ct2Full.drop 128) ⊢
        memRegion ptr_mac (BitVec.ofNat 64 (ct2Full.length - 128)).toNat ∗
          A.live ptr_mac (BitVec.ofNat 64 (ct2Full.length - 128)).toNat 1 := by
    have hlen : (ct2Full.drop 128).length = ct2Full.length - 128 := List.length_drop
    rw [← hlen]
    exact vecBufAt_entails_memRegion_live A.repAlloc ptr_mac (ct2Full.drop 128)
      (by omega) (by omega)
  have hmac_toNat : (BitVec.ofNat 64 (ct2Full.length - 128)).toNat = ct2Full.length - 128 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hmac_pos : 0 < (BitVec.ofNat 64 (ct2Full.length - 128)).toNat := by omega
  have hmac_max : (BitVec.ofNat 64 (ct2Full.length - 128)).toNat < 2 ^ 63 := by omega
  have hmac_beq : (BitVec.ofNat 64 (ct2Full.length - 128) == 0#64) = false := by
    apply beq_false_of_ne
    intro h0
    have h1 := congrArg BitVec.toNat h0
    change (BitVec.ofNat 64 (ct2Full.length - 128)).toNat = 0 at h1
    omega
  refine SepWPp.fold hss_mr (by sep_focus) ?_
  refine SepWPp.fold hss_raw_mr (by sep_focus) ?_
  refine SepWPp.fold hct2_128_mr (by sep_focus) ?_
  refine SepWPp.fold hmk_dealloc (by sep_focus) ?_
  refine SepWPp.fold hmac_mr_live (by sep_focus) ?_
  refine SepWPp.fold
    (vecU8At_expose_sp_1328 A.repAlloc s0.sp g_auth'.rootKey.cap g_auth'.rootKey.ptr
      auth'.rootKey (by omega))
    (by sep_focus) ?_
  refine sepWPp_pure_left_focus
    (auth'.rootKey.length ≤ g_auth'.rootKey.cap.toNat ∧ g_auth'.rootKey.cap.toNat < 2 ^ 63 ∧
      g_auth'.rootKey.ptr ≠ 0#64 ∧ g_auth'.rootKey.cap ≠ 0#64)
    (by sep_focus) fun _ => ?_
  refine SepWPp.fold (ct2DeallocAt_expose A.repAlloc cap_info ptr_info) (by sep_focus) ?_
  refine sepWPp_pure_left_focus (Ct2DeallocProp cap_info ptr_info) (by sep_focus)
    fun ⟨hinfo_beq, hinfo_pos, hinfo_max, hinfo_ptr⟩ => ?_
  refine SepWPp.fold (ct2DeallocAt_expose A.repAlloc cap_ct1' ptr_ct1') (by sep_focus) ?_
  refine sepWPp_pure_left_focus (Ct2DeallocProp cap_ct1' ptr_ct1') (by sep_focus)
    fun ⟨hct1_beq, hct1_pos, hct1_max, hct1_ptr⟩ => ?_
  refine SepWPp.fold (ct2DeallocAt_expose A.repAlloc cap_dk ptr_dk) (by sep_focus) ?_
  refine sepWPp_pure_left_focus (Ct2DeallocProp cap_dk ptr_dk) (by sep_focus)
    fun ⟨hdk_beq, hdk_pos, hdk_max, hdk_ptr⟩ => ?_
  refine SepWPp.fold
    (ct2DeallocAt_expose A.repAlloc g_auth'.rootKey.cap g_auth'.rootKey.ptr)
    (by sep_focus) ?_
  refine sepWPp_pure_left_focus (Ct2DeallocProp g_auth'.rootKey.cap g_auth'.rootKey.ptr)
    (by sep_focus) fun ⟨hrk_beq, hrk_pos, hrk_max, hrk_ptr⟩ => ?_
  refine SepWPp.fold
    (ct2DeallocAt_expose A.repAlloc g_auth'.macKey.cap g_auth'.macKey.ptr)
    (by sep_focus) ?_
  refine sepWPp_pure_left_focus (Ct2DeallocProp g_auth'.macKey.cap g_auth'.macKey.ptr)
    (by sep_focus) fun ⟨hmk_beq, hmk_pos, hmk_max, hmk_ptr⟩ => ?_
  have hrlay_32 : RustLayoutOk 32 1 := rustLayoutOk_one (by decide) (by decide)
  have hrlay_128 : RustLayoutOk 128 1 := rustLayoutOk_one (by decide) (by decide)
  have hrlay_info : RustLayoutOk cap_info.toNat 1 := rustLayoutOk_one hinfo_pos hinfo_max
  have hrlay_ct1 : RustLayoutOk cap_ct1'.toNat 1 := rustLayoutOk_one hct1_pos hct1_max
  have hrlay_dk : RustLayoutOk cap_dk.toNat 1 := rustLayoutOk_one hdk_pos hdk_max
  have hrlay_rk : RustLayoutOk g_auth'.rootKey.cap.toNat 1 := rustLayoutOk_one hrk_pos hrk_max
  have hrlay_mk : RustLayoutOk g_auth'.macKey.cap.toNat 1 := rustLayoutOk_one hmk_pos hmk_max
  have hrlay_mac : RustLayoutOk (BitVec.ofNat 64 (ct2Full.length - 128)).toNat 1 :=
    rustLayoutOk_one hmac_pos hmac_max
  have hrlay_mac' : RustLayoutOk (ct2Full.length - 128) 1 :=
    rustLayoutOk_one (by omega) (by omega)
  have hpow2_1 : ∃ k : Nat, 1 = 2 ^ k := ⟨0, rfl⟩
  let σ₁ : M.σ := M.stepEvents (rustDeallocEvents 32 1) σ
  let σ₂ : M.σ := M.stepEvents (rustDeallocEvents cap_info.toNat 1) σ₁
  let σ₃ : M.σ := M.stepEvents (rustDeallocEvents 32 1) σ₂
  let σ₄ : M.σ := M.stepEvents (rustDeallocEvents cap_ct1'.toNat 1) σ₃
  let σ₅ : M.σ := M.stepEvents (rustDeallocEvents cap_dk.toNat 1) σ₄
  let σ₆ : M.σ := M.stepEvents (rustDeallocEvents g_auth'.rootKey.cap.toNat 1) σ₅
  let σ₇ : M.σ := M.stepEvents (rustDeallocEvents g_auth'.macKey.cap.toNat 1) σ₆
  let σ₈ : M.σ := M.stepEvents (rustDeallocEvents (BitVec.ofNat 64 (ct2Full.length - 128)).toNat 1) σ₇
  let evs_9 : List AllocEvent :=
    rustDeallocEvents 32 1 ++
      rustDeallocEvents cap_info.toNat 1 ++
      rustDeallocEvents 32 1 ++
      rustDeallocEvents cap_ct1'.toNat 1 ++
      rustDeallocEvents cap_dk.toNat 1 ++
      rustDeallocEvents g_auth'.rootKey.cap.toNat 1 ++
      rustDeallocEvents g_auth'.macKey.cap.toNat 1 ++
      rustDeallocEvents (BitVec.ofNat 64 (ct2Full.length - 128)).toNat 1 ++
      rustDeallocEvents 128 1
  have hfree_9 : FreeOnlyEvs evs_9 :=
    ((((((((freeOnlyEvs_rustDealloc1 32).append
      (freeOnlyEvs_rustDealloc1 cap_info.toNat)).append
      (freeOnlyEvs_rustDealloc1 32)).append
      (freeOnlyEvs_rustDealloc1 cap_ct1'.toNat)).append
      (freeOnlyEvs_rustDealloc1 cap_dk.toNat)).append
      (freeOnlyEvs_rustDealloc1 g_auth'.rootKey.cap.toNat)).append
      (freeOnlyEvs_rustDealloc1 g_auth'.macKey.cap.toNat)).append
      (freeOnlyEvs_rustDealloc1 (BitVec.ofNat 64 (ct2Full.length - 128)).toNat)).append
      (freeOnlyEvs_rustDealloc1 128)
  have hstep_9 :
      M.stepEvents (rustDeallocEvents 128 1)
        (M.stepEvents (rustDeallocEvents (BitVec.ofNat 64 (ct2Full.length - 128)).toNat 1)
          (M.stepEvents (rustDeallocEvents g_auth'.macKey.cap.toNat 1)
            (M.stepEvents (rustDeallocEvents g_auth'.rootKey.cap.toNat 1)
              (M.stepEvents (rustDeallocEvents cap_dk.toNat 1)
                (M.stepEvents (rustDeallocEvents cap_ct1'.toNat 1)
                  (M.stepEvents (rustDeallocEvents 32 1)
                    (M.stepEvents (rustDeallocEvents cap_info.toNat 1)
                      (M.stepEvents (rustDeallocEvents 32 1) σ)))))))) =
        M.stepEvents evs_9 σ := by
    dsimp only [evs_9]
    simp only [M.stepEvents_append]
  have hpost_env' :
      ∀ evs_ep : List AllocEvent, FreeOnlyEvs evs_ep →
        ∃ evs_all : List AllocEvent, PostEnv x evs_all ∧
          M.stepEvents evs_ep (M.stepEvents evs_9 σ) = M.stepEvents evs_all st0 := by
    intro evs_ep hfree_ep
    obtain ⟨evs_all, hpost_all, hstep_all⟩ :=
      hpost_env (evs_9 ++ evs_ep) (hfree_9.append hfree_ep)
    exact ⟨evs_all, hpost_all, (M.stepEvents_append evs_9 evs_ep σ).symm.trans hstep_all⟩
  have h_write :=
    @recv_ct2_chunk_err_write_out_placed_wpp _ K F M A lim PreEnv PostEnv ext hA x
      st0 (M.stepEvents evs_9 σ) receivingCt2 cap_ct2 ptr_ct2 s0
  have hsp_norm : st.readReg64 .sp = s0.sp - 2496#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm hx19 hx20 hx21 hx23 hx24 hx25 hx27 hx29
  clear hA
  simp only [lsProg_350] at h_dealloc h_write ⊢
  refine sepWPp_of_sepWP_lscro (mid := lsρ spqrRustDeallocSym') hinv ?_
  wp_steps_sync_pool_350 ext (lsρ spqrRustDeallocSym')
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  wpp_call_lscro_recvCt2_budget h_dealloc (ptr_ss, 32, 1, σ) hinv1
  have hsp_1 : sf.readReg64 .sp = s0.sp - 2496#64 := by
    simp only [State.sp, wp_norm, arm64_norm, *]
  simp only [wp_norm, arm64_norm] at hsp_1
  conv => arg 4; simp only [State.sp, hsp_sf, hsp, hsp_norm, hsp_1, wp_norm, arm64_norm]
  refine sepWPp_pure_left_focus (sf.trace = _) (by sep_focus) fun htr1 => ?_
  refine sepWPp_of_sepWP_lscro (mid := lsρ spqrRustDeallocSym') hF_sf ?_
  wp_steps_sync_pool_350 ext (lsρ spqrRustDeallocSym')
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv2
  wpp_call_lscro_recvCt2_budget h_dealloc (ptr_info, cap_info.toNat, 1, σ₁) hinv2
  have hsp_2 : sf_1.readReg64 .sp = s0.sp - 2496#64 := by
    simp only [State.sp, wp_norm, arm64_norm, *]
  simp only [wp_norm, arm64_norm] at hsp_2
  conv => arg 4; simp only [State.sp, hsp_sf_1, hsp_1, wp_norm, arm64_norm]
  refine sepWPp_pure_left_focus (sf_1.trace = _) (by sep_focus) fun htr2 => ?_
  refine sepWPp_of_sepWP_lscro (mid := lsρ spqrRustDeallocSym') hF_sf_1 ?_
  wp_steps_sync_pool_350 ext (lsρ spqrRustDeallocSym')
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv3
  wpp_call_lscro_recvCt2_budget h_dealloc (ptr_ss_raw, 32, 1, σ₂) hinv3
  have hsp_3 : sf_2.readReg64 .sp = s0.sp - 2496#64 := by
    simp only [State.sp, wp_norm, arm64_norm, *]
  simp only [wp_norm, arm64_norm] at hsp_3
  conv => arg 4; simp only [State.sp, hsp_sf_2, hsp_2, wp_norm, arm64_norm]
  refine sepWPp_pure_left_focus (sf_2.trace = _) (by sep_focus) fun htr3 => ?_
  refine sepWPp_of_sepWP_lscro (mid := lsρ spqrRustDeallocSym') hF_sf_2 ?_
  wp_steps_sync_pool_350 ext (lsρ spqrRustDeallocSym')
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv4
  wpp_call_lscro_recvCt2_budget h_dealloc (ptr_ct1', cap_ct1'.toNat, 1, σ₃) hinv4
  have hsp_4 : sf_3.readReg64 .sp = s0.sp - 2496#64 := by
    simp only [State.sp, wp_norm, arm64_norm, *]
  simp only [wp_norm, arm64_norm] at hsp_4
  conv => arg 4; simp only [State.sp, hsp_sf_3, hsp_3, wp_norm, arm64_norm]
  refine sepWPp_pure_left_focus (sf_3.trace = _) (by sep_focus) fun htr4 => ?_
  refine sepWPp_of_sepWP_lscro (mid := lsρ spqrRustDeallocSym') hF_sf_3 ?_
  wp_steps_sync_pool_350 ext (lsρ spqrRustDeallocSym')
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv5
  wpp_call_lscro_recvCt2_budget h_dealloc (ptr_dk, cap_dk.toNat, 1, σ₄) hinv5
  have hsp_5 : sf_4.readReg64 .sp = s0.sp - 2496#64 := by
    simp only [State.sp, wp_norm, arm64_norm, *]
  simp only [wp_norm, arm64_norm] at hsp_5
  conv => arg 4; simp only [State.sp, hsp_sf_4, hsp_4, wp_norm, arm64_norm]
  refine sepWPp_pure_left_focus (sf_4.trace = _) (by sep_focus) fun htr5 => ?_
  refine sepWPp_of_sepWP_lscro (mid := lsρ spqrRustDeallocSym') hF_sf_4 ?_
  wp_steps_sync_pool_350 ext (lsρ spqrRustDeallocSym')
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv6
  wpp_call_lscro_recvCt2_budget h_dealloc
    (g_auth'.rootKey.ptr, g_auth'.rootKey.cap.toNat, 1, σ₅) hinv6
  have hsp_6 : sf_5.readReg64 .sp = s0.sp - 2496#64 := by
    simp only [State.sp, wp_norm, arm64_norm, *]
  simp only [wp_norm, arm64_norm] at hsp_6
  conv => arg 4; simp only [State.sp, hsp_sf_5, hsp_5, wp_norm, arm64_norm]
  refine sepWPp_pure_left_focus (sf_5.trace = _) (by sep_focus) fun htr6 => ?_
  refine sepWPp_of_sepWP_lscro (mid := lsρ spqrRustDeallocSym') hF_sf_5 ?_
  wp_steps_sync_pool_350 ext (lsρ spqrRustDeallocSym')
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv7
  wpp_call_lscro_recvCt2_budget h_dealloc
    (g_auth'.macKey.ptr, g_auth'.macKey.cap.toNat, 1, σ₆) hinv7
  have hsp_7 : sf_6.readReg64 .sp = s0.sp - 2496#64 := by
    simp only [State.sp, wp_norm, arm64_norm, *]
  simp only [wp_norm, arm64_norm] at hsp_7
  conv => arg 4; simp only [State.sp, hsp_sf_6, hsp_6, wp_norm, arm64_norm]
  refine sepWPp_pure_left_focus (sf_6.trace = _) (by sep_focus) fun htr7 => ?_
  refine sepWPp_of_sepWP_lscro (mid := lsρ spqrRustDeallocSym') hF_sf_6 ?_
  wp_steps_sync_pool_350 ext (lsρ spqrRustDeallocSym')
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv8
  wpp_call_lscro_recvCt2_budget h_dealloc
    (ptr_mac, (BitVec.ofNat 64 (ct2Full.length - 128)).toNat, 1, σ₇) hinv8
  have hsp_8 : sf_7.readReg64 .sp = s0.sp - 2496#64 := by
    simp only [State.sp, wp_norm, arm64_norm, *]
  simp only [wp_norm, arm64_norm] at hsp_8
  conv => arg 4; simp only [State.sp, hsp_sf_7, hsp_7, wp_norm, arm64_norm]
  refine sepWPp_pure_left_focus (sf_7.trace = _) (by sep_focus) fun htr8 => ?_
  refine sepWPp_of_sepWP_lscro (mid := lsρ spqrRustDeallocSym') hF_sf_7 ?_
  wp_steps_sync_pool_350 ext (lsρ spqrRustDeallocSym')
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv9
  wpp_call_lscro_recvCt2_budget h_dealloc (ptr_ct2_128, 128, 1, σ₈) hinv9
  have hsp_9 : sf_8.readReg64 .sp = s0.sp - 2496#64 := by
    simp only [State.sp, wp_norm, arm64_norm, *]
  simp only [wp_norm, arm64_norm] at hsp_9
  conv => arg 4; simp only [State.sp, hsp_sf_8, hsp_8, wp_norm, arm64_norm]
  refine sepWPp_pure_left_focus (sf_8.trace = _) (by sep_focus) fun htr9 => ?_
  dsimp only [σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁]
  rw [hstep_9]
  refine SepWPp.fold (rejoin_memRegion_32_sp_152 s0.sp cap_info ptr_info 41#64) (by sep_focus) ?_
  refine SepWPp.fold (rejoin_memRegion_24_sp_1280 s0.sp cap_ct1' ptr_ct1' 960#64) (by sep_focus) ?_
  refine SepWPp.fold
    (rejoin_memRegion_48_sp_1328 s0.sp g_auth'.rootKey.cap g_auth'.rootKey.ptr
      (BitVec.ofNat 64 auth'.rootKey.length) g_auth'.macKey.cap g_auth'.macKey.ptr 32#64)
    (by sep_focus) ?_
  refine SepWPp.fold
    (cells9_sp_2496_fold s0.sp g_auth'.macKey.ptr ptr_dk (BitVec.ofNat 64 ct2Full.length)
      ptr_info cap_ct2 cap_dk ptr_mac ptr_ct1' x.epoch)
    (by sep_focus) ?_
  refine sepWPp_rw_pre'
    (h_write sf_8 R hpost_env' hres
      (by wp_norm_goal) (by wp_norm_goal)
      (by simp only [wp_norm, arm64_norm, *]) hsp_s0
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      hF_sf_8
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]))
    (by dsimp only [recvCt2RoPlacedAt]; sep_ac_rfl)

end LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part3PlacedBudget
