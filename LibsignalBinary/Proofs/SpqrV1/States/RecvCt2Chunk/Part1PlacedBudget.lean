/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlacedBudget
meta import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlacedBudget -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp

/-!
# `<EkSentCt1Received>::recv_ct2_chunk` (Block `350`): Budget `None` Return Path

Relocatable `[LibsignalPlacement]` `RustCliAllocBudget` proof of the `None` (`StillReceiving`)
branch (`+112 .. +200`, zero allocations after `decoded_message`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part1PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement blkPC_350 blkPl_350 lsProg_350 lsmpl lsρ)
open CryptoVerification.LibsignalSpqrV1 (MlKem PolyDecoder optKeyBytesAt spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalTripleRatchet (LibsignalCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Keys (SepWPp.rw_pre)
open CryptoVerification.SpqrV1.Alloc (spqrMemcpySym)
open CryptoVerification.SpqrV1.Drop (chunkedEkSentCt1ReceivedSize)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof (
  sp_add_neg688_eq_hsp sp_add_neg96_eq_hsp_592 sp_sub_688_eq_hsp sp_sub_96_eq_hsp_592
)
open CryptoVerification.SpqrV1.Poly (chunkAt polyDecoderAt)
open CryptoVerification.SpqrV1.Poly.AddChunk (PolyDecoderStrictSorted)
open CryptoVerification.SpqrV1.States.RecvCt2Chunk (
  RecvCt2ChunkGhost activeFrameRegionsAt ekSentCt1ReceivedAt_fsp_280_entails
  ekSentCt1ReceivedCells_entails_memRegion_504 ekSentCt1ReceivedRecvChunkAt
  ekSentCt1ReceivedRecvChunkResultAt ekSentCt1ReceivedUcAt
  ekSentCt1ReceivedUcAt_expose_entails memRegion_504_at_fsp_280_split
  optKeyBytesAt_none_entails_memRegion_24 polyDecodedMessageStackX
  recvCt2ChunkStackX recvCt2RoPlacedAt recv_ct2_chunk_eq_stillReceiving
  rejoin_stack_recvCt2Chunk savedRegsAt someBranchFrameAt
)
open CryptoVerification.SpqrV1.States.RecvCt2Chunk.SplitBytes (
  ekSentCt1ReceivedSplit polyDecoderSplit
)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlacedBudget (
  RecvCt2ChunkEnv RecvCt2PlacedAlloc recvCt2PlacedPostQ recvCt2PlacedPostQOfEnv
  recvCt2PlacedPostQOfPrePostEnv recvCt2PlacedPostQp sepWPp_of_sepWP_lscro
  splitBytes_memcpyVmOuter_withStack_lscro_ok
)

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
run_cmd Lean.Elab.Command.liftCoreM do
  for nm in [
    ``sp_sub_688_eq_hsp,
    ``sp_add_neg688_eq_hsp,
    ``sp_sub_96_eq_hsp_592,
    ``sp_add_neg96_eq_hsp_592] do
    Lean.Attribute.erase nm `arm64_norm

theorem recvCt2PlacedPostQOfPrePostEnv_intro [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    {x : RecvCt2ChunkGhost F} {st0 : M.σ} {s0 sf : State} {P_f R : SepProp}
    (evs : List AllocEvent)
    (hpost_env : PostEnv x evs)
    (htr : sf.trace = s0.trace)
    (hsp : sf.sp = s0.sp)
    (hcs : CalleeSavedPreserved s0 sf)
    (hmem : (sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨
        (recvCt2RoPlacedAt ∗
          ekSentCt1ReceivedRecvChunkResultAt A.repAlloc x.outA
            (x.self.recv_ct2_chunk K x.epoch x.chunk) ∗
          memRegion x.selfA chunkedEkSentCt1ReceivedSize ∗
          chunkAt x.chunkA x.chunk ∗
          tokenInitPlacedAt ∗
          reduceTablePlacedAt ∗
          A.pool lim (M.stepEvents evs st0) sf ∗
          stackAt s0.sp recvCt2ChunkStackX) ∗ R)) :
    recvCt2PlacedPostQOfPrePostEnv K F M A lim PreEnv PostEnv x st0 s0 R sf P_f := by
  refine ⟨fun hm => ?_, hsp, hcs⟩
  have hm1 := hmem hm
  dsimp only [recvCt2PlacedPostQOfPrePostEnv,
    DefsPlacedBudget.recvCt2ChunkPlacedSpecOfPrePostEnv,
    DefsBudget.recvCt2ChunkPlacedSpecOfPrePostEnv]
  simp only [sepExists_sepConj_right, sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨evs, ?_⟩
  have hpure : sf.trace = s0.trace ∧ PostEnv x evs := ⟨htr, hpost_env⟩
  have harr :
      (recvCt2RoPlacedAt ∗
        (⌜sf.trace = s0.trace ∧ PostEnv x evs⌝ ∗
          ekSentCt1ReceivedRecvChunkResultAt A.repAlloc x.outA
            (x.self.recv_ct2_chunk K x.epoch x.chunk) ∗
          memRegion x.selfA chunkedEkSentCt1ReceivedSize ∗
          chunkAt x.chunkA x.chunk ∗
          tokenInitPlacedAt ∗
          reduceTablePlacedAt ∗
          A.pool lim (M.stepEvents evs st0) sf ∗
          stackAt s0.sp recvCt2ChunkStackX)) ∗ R =
      ⌜sf.trace = s0.trace ∧ PostEnv x evs⌝ ∗
        ((recvCt2RoPlacedAt ∗
          ekSentCt1ReceivedRecvChunkResultAt A.repAlloc x.outA
            (x.self.recv_ct2_chunk K x.epoch x.chunk) ∗
          memRegion x.selfA chunkedEkSentCt1ReceivedSize ∗
          chunkAt x.chunkA x.chunk ∗
          tokenInitPlacedAt ∗
          reduceTablePlacedAt ∗
          A.pool lim (M.stepEvents evs st0) sf ∗
          stackAt s0.sp recvCt2ChunkStackX) ∗ R) := by
    sep_ac_rfl
  rw [harr, satisfies_pure_sepConj]
  exact ⟨hpure, hm1⟩

set_option maxHeartbeats 800000 in
theorem recv_ct2_chunk_none_placed_wpp_ofPrePostEnv [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (x : RecvCt2ChunkGhost F) (receivingCt2 : PolyDecoder)
    (st0 st_cur : M.σ) (evs_so_far : List AllocEvent)
    (s0 st : State) (R : SepProp)
    (hst_cur : st_cur = M.stepEvents evs_so_far st0)
    (hpost_env : PostEnv x evs_so_far)
    (hepoch : x.epoch = x.self.uc.epoch)
    (hadd : PolyDecoder.addChunk x.self.receiving_ct2 x.chunk = .ok receivingCt2)
    (_hsort : PolyDecoderStrictSorted receivingCt2)
    (hdec : receivingCt2.decodedMessage = .ok none)
    (hpc : st.pc = (blkPl_350).base + 152#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 2496#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx19 : st.readReg64 .x19 = x.outA)
    (hx20 : st.readReg64 .x20 = x.selfA) :
    SepWPp (lsProg_350 (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (recvCt2RoPlacedAt ∗
        memRegion x.outA chunkedEkSentCt1ReceivedSize ∗
        ekSentCt1ReceivedUcAt A.repAlloc x.selfA x.self.uc ∗
        memRegion (x.selfA + 104#64) 400 ∗
        cells (s0.sp - 2496#64) 9 ∗
        polyDecoderAt A.repAlloc ((s0.sp - 2496#64) + 0x48#64) receivingCt2 ∗
        optKeyBytesAt A.repAlloc ((s0.sp - 2496#64) + 0x1d8#64) none ∗
        memRegion ((s0.sp - 2496#64) + 0x280#64) 504 ∗
        someBranchFrameAt (s0.sp - 2496#64) ∗
        chunkAt x.chunkA x.chunk ∗
        tokenInitPlacedAt ∗
        reduceTablePlacedAt ∗
        A.pool lim st_cur st ∗
        stackAt (s0.sp - 2496#64) polyDecodedMessageStackX ∗
        savedRegsAt s0)
      (recvCt2PlacedPostQOfPrePostEnv K F M A lim PreEnv PostEnv x st0 s0 R)
      (recvCt2PlacedPostQp K x s0 R) := by
  have hmc_raw := hA.memcpy_region_at_block
    (prog := lsProg_350 (Rust.withPanics ext)) polyDecodedMessageStackX
  have h_mc_dec := splitBytes_memcpyVmOuter_withStack_lscro_ok
    (pl := lsmpl) (polyDecoderSplit A.repAlloc receivingCt2)
    (by decide) polyDecodedMessageStackX hmc_raw
  have h_mc_st := splitBytes_memcpyVmOuter_withStack_lscro_ok
    (pl := lsmpl)
    (ekSentCt1ReceivedSplit A.repAlloc { uc := x.self.uc, receiving_ct2 := receivingCt2 })
    (by decide) polyDecodedMessageStackX hmc_raw
  clear hA hmc_raw
  simp only [lsProg_350] at h_mc_dec h_mc_st ⊢
  refine SepWPp.rw_pre (by rw [memRegion_504_at_fsp_280_split (s0.sp - 2496#64)]) ?_
  sep_elim_exists
  refine sepWPp_of_sepWP_lscro (mid := lsρ spqrMemcpySym) hinv ?_
  wp_steps_sync_pool (lsρ spqrMemcpySym)
  simp only [State.setMem_setMem]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  wpp_call_lscro_recvCt2_budget h_mc_dec
    ((s0.sp - 2496#64) + 0x2e8#64, (s0.sp - 2496#64) + 0x48#64) hinv1
  refine CryptoVerification.SpqrV1.Auth.SepWPp.pure_left_focus _ (by sep_focus) fun hpost1 => ?_
  rcases hpost1 with ⟨hvm1, htr1, _⟩
  refine SepWPp.rw_pre (by rw [← A.pool_transport lim st_cur _ _ hvm1]) ?_
  refine sepWPp_of_sepWP_lscro (mid := lsρ spqrMemcpySym) hF_sf ?_
  refine SepWP.fold (ekSentCt1ReceivedUcAt_expose_entails A.repAlloc x.selfA x.self.uc)
    (by sep_focus) ?_
  sep_elim_exists
  wp_steps_sync_pool (lsρ spqrMemcpySym)
  simp only [State.setMem_setMem]
  refine SepWP.fold
    (ekSentCt1ReceivedAt_fsp_280_entails A.repAlloc s0.sp x.self.uc receivingCt2 _ _ _ _ _)
    (by sep_focus) ?_
  refine SepWP.fold
    (ekSentCt1ReceivedCells_entails_memRegion_504 x.selfA _ _ _ _ _ _ _ _ _ _ _ _ _)
    (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv2
  wpp_call_lscro_recvCt2_budget h_mc_st (x.outA, s0.sp - 1856#64) hinv2
  refine CryptoVerification.SpqrV1.Auth.SepWPp.pure_left_focus _ (by sep_focus) fun hpost2 => ?_
  rcases hpost2 with ⟨hvm2, htr2, _⟩
  refine SepWPp.rw_pre (by rw [← A.pool_transport lim st_cur _ _ hvm2]) ?_
  apply SepWPp.of_sepWP_ret
  refine SepWP.fold
    (optKeyBytesAt_none_entails_memRegion_24 A.repAlloc (s0.sp - 2024#64))
    (by sep_focus) ?_
  unfold savedRegsAt
  wp_steps_sync_pool (s0.readReg64 .x30)
  simp only [State.setMem_setMem]
  have hfold_saved :
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
      ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ⊢ savedRegsAt s0 := Entails.refl _
  refine SepWP.fold hfold_saved (by sep_focus) ?_
  have hfold_active :
      cells (s0.sp - 2496#64) 9 ∗
        memRegion (s0.sp - 2424#64) 400 ∗
        memRegion (s0.sp - 2024#64) 24 ∗
        memRegion (s0.sp - 1856#64) 504 ∗
        someBranchFrameAt (s0.sp - 2496#64) ⊢
      activeFrameRegionsAt (s0.sp - 2496#64) := by
    unfold activeFrameRegionsAt
    have ha1 : (s0.sp - 2496#64) + 0x48#64 = s0.sp - 2424#64 := by bv_omega
    have ha2 : (s0.sp - 2496#64) + 0x1d8#64 = s0.sp - 2024#64 := by bv_omega
    have ha3 : (s0.sp - 2496#64) + 0x280#64 = s0.sp - 1856#64 := by bv_omega
    rw [ha1, ha2, ha3]
    exact Entails.refl _
  refine SepWP.fold hfold_active (by sep_focus) ?_
  have hstack_eq : stackAt sf.sp polyDecodedMessageStackX ⊢
      stackAt (s0.sp - 2496#64) polyDecodedMessageStackX := by
    rw [hsp_sf, hsp]; exact Entails.refl _
  refine SepWP.fold hstack_eq (by sep_focus) ?_
  refine SepWP.fold (rejoin_stack_recvCt2Chunk s0) (by sep_focus) ?_
  have hres := recv_ct2_chunk_eq_stillReceiving (K := K) x.self x.epoch x.chunk receivingCt2
    hepoch hadd hdec
  refine SepWP.mono
    (post := fun sf_ret P_ret =>
      ((sf_ret.mem ⊨ P_ret ∗ R) →
        (sf_ret.mem ⊨
          (⌜sf_ret.trace = s0.trace⌝ ∗
            (recvCt2RoPlacedAt ∗
              ekSentCt1ReceivedRecvChunkResultAt A.repAlloc x.outA
                (x.self.recv_ct2_chunk K x.epoch x.chunk) ∗
              memRegion x.selfA chunkedEkSentCt1ReceivedSize ∗
              chunkAt x.chunkA x.chunk ∗
              tokenInitPlacedAt ∗
              reduceTablePlacedAt ∗
              A.pool lim st_cur sf_ret ∗
              stackAt s0.sp recvCt2ChunkStackX)) ∗ R)) ∧
        sf_ret.sp = s0.sp ∧ CalleeSavedPreserved s0 sf_ret)
    ?_ ?_
  · rw [hres]
    dsimp only [ekSentCt1ReceivedRecvChunkResultAt, ekSentCt1ReceivedRecvChunkAt]
    wp_done
  · rintro sf_ret P_ret _ _ ⟨hmem_ret, hsp_ret, hcs_ret⟩
    refine ⟨fun hm => ?_, hsp_ret, hcs_ret⟩
    have hm1 := hmem_ret hm
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm1
    rcases hm1 with ⟨htr_ret, hm2⟩
    rw [hst_cur] at hm2
    exact (recvCt2PlacedPostQOfPrePostEnv_intro (P_f := P_ret)
      evs_so_far hpost_env htr_ret hsp_ret hcs_ret (fun _ => hm2)).1 hm

theorem recv_ct2_chunk_none_placed_wpp_ofEnv [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (x : RecvCt2ChunkGhost F) (receivingCt2 : PolyDecoder)
    (st0 st_cur : M.σ) (evs_so_far : List AllocEvent)
    (s0 st : State) (R : SepProp)
    (hst_cur : st_cur = M.stepEvents evs_so_far st0)
    (hpost_env : Env x evs_so_far)
    (hepoch : x.epoch = x.self.uc.epoch)
    (hadd : PolyDecoder.addChunk x.self.receiving_ct2 x.chunk = .ok receivingCt2)
    (hsort : PolyDecoderStrictSorted receivingCt2)
    (hdec : receivingCt2.decodedMessage = .ok none)
    (hpc : st.pc = (blkPl_350).base + 152#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 2496#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx19 : st.readReg64 .x19 = x.outA)
    (hx20 : st.readReg64 .x20 = x.selfA) :
    SepWPp (lsProg_350 (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (recvCt2RoPlacedAt ∗
        memRegion x.outA chunkedEkSentCt1ReceivedSize ∗
        ekSentCt1ReceivedUcAt A.repAlloc x.selfA x.self.uc ∗
        memRegion (x.selfA + 104#64) 400 ∗
        cells (s0.sp - 2496#64) 9 ∗
        polyDecoderAt A.repAlloc ((s0.sp - 2496#64) + 0x48#64) receivingCt2 ∗
        optKeyBytesAt A.repAlloc ((s0.sp - 2496#64) + 0x1d8#64) none ∗
        memRegion ((s0.sp - 2496#64) + 0x280#64) 504 ∗
        someBranchFrameAt (s0.sp - 2496#64) ∗
        chunkAt x.chunkA x.chunk ∗
        tokenInitPlacedAt ∗
        reduceTablePlacedAt ∗
        A.pool lim st_cur st ∗
        stackAt (s0.sp - 2496#64) polyDecodedMessageStackX ∗
        savedRegsAt s0)
      (recvCt2PlacedPostQOfEnv K F M A lim Env x st0 s0 R)
      (recvCt2PlacedPostQp K x s0 R) :=
  recv_ct2_chunk_none_placed_wpp_ofPrePostEnv hA x receivingCt2 st0 st_cur evs_so_far s0 st R
    hst_cur hpost_env hepoch hadd hsort hdec hpc hrun hsp hsp_s0 htr hvregs hinv hx19 hx20

theorem recv_ct2_chunk_none_placed_wpp [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (x : RecvCt2ChunkGhost F) (receivingCt2 : PolyDecoder)
    (st0 st_cur : M.σ) (evs_so_far : List AllocEvent)
    (s0 st : State) (R : SepProp)
    (hst_cur : st_cur = M.stepEvents evs_so_far st0)
    (hpost_env : RecvCt2ChunkEnv x evs_so_far)
    (hepoch : x.epoch = x.self.uc.epoch)
    (hadd : PolyDecoder.addChunk x.self.receiving_ct2 x.chunk = .ok receivingCt2)
    (hsort : PolyDecoderStrictSorted receivingCt2)
    (hdec : receivingCt2.decodedMessage = .ok none)
    (hpc : st.pc = (blkPl_350).base + 152#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 2496#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx19 : st.readReg64 .x19 = x.outA)
    (hx20 : st.readReg64 .x20 = x.selfA) :
    SepWPp (lsProg_350 (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (recvCt2RoPlacedAt ∗
        memRegion x.outA chunkedEkSentCt1ReceivedSize ∗
        ekSentCt1ReceivedUcAt A.repAlloc x.selfA x.self.uc ∗
        memRegion (x.selfA + 104#64) 400 ∗
        cells (s0.sp - 2496#64) 9 ∗
        polyDecoderAt A.repAlloc ((s0.sp - 2496#64) + 0x48#64) receivingCt2 ∗
        optKeyBytesAt A.repAlloc ((s0.sp - 2496#64) + 0x1d8#64) none ∗
        memRegion ((s0.sp - 2496#64) + 0x280#64) 504 ∗
        someBranchFrameAt (s0.sp - 2496#64) ∗
        chunkAt x.chunkA x.chunk ∗
        tokenInitPlacedAt ∗
        reduceTablePlacedAt ∗
        A.pool lim st_cur st ∗
        stackAt (s0.sp - 2496#64) polyDecodedMessageStackX ∗
        savedRegsAt s0)
      (recvCt2PlacedPostQ K F M A lim x st0 s0 R)
      (recvCt2PlacedPostQp K x s0 R) :=
  recv_ct2_chunk_none_placed_wpp_ofEnv hA x receivingCt2 st0 st_cur evs_so_far s0 st R
    hst_cur hpost_env hepoch hadd hsort hdec hpc hrun hsp hsp_s0 htr hvregs hinv hx19 hx20

end LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part1PlacedBudget
