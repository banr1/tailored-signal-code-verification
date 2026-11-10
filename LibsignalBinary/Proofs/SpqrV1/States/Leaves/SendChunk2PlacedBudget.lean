/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.TopPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk2
import ProofLib.Hoare.LibcHooks
import ProofLib.SepLogic.WPp

/-!
# Chunked Braid Send-Chunk Leaf Transitions 2 (Budget-Threaded Relocatable)

Budget-threaded `[LibsignalPlacement]` contracts for `<Ct1Received>::send_ek_chunk` (Block `345`)
and `<Ct1Sampled>::send_ct1_chunk` (Block `335`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk2PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalPlacement blkLib_eq_335 blkLib_eq_345 blkPC_335 blkPC_345 blkPl_335 blkPl_345
   lsProg_335 lsProg_345 lsmpl lsρ)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded sessionMemcpyRegionSpec sessionMemcpySpec withLsCodeRoLoaded)
open CryptoVerification.SpqrV1.Alloc (spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Drop (chunkedCt1ReceivedAt chunkedCt1SampledAt)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly (chunkAt chunkSize)
open CryptoVerification.SpqrV1.Poly.ComputeAt
  (readReg32_setMem_pre readReg64_setMem_pre readReg_setMem_pre sp_setMem_pre)
open CryptoVerification.SpqrV1.Poly.NextChunk (polyNextChunkStack)
open CryptoVerification.SpqrV1.States.Leaves
  (Ct1ReceivedSendEkChunkGhost Ct1SampledSendCt1ChunkGhost Relocatable authWordsList bv_sub_sub
   cell_0_rejoin_400 cells_13_unfold cells_16_unfold cells_1_unfold cells_4_unfold cells_6_unfold
   chunkedCt1ReceivedAt_recompose_sp chunkedCt1SampledAt_recompose_sp ct1Received_send_ek_chunk_ok
   ct1Sampled_send_ct1_chunk_ok ct2SentWordsList ekSentCt1ReceivedWordsList ekSentWordsList
   fiveVecWordsList ls_subroutine_ok_to_blockProgram stackAt_1376_rejoin stackAt_1376_split
   stackAt_944_rejoin stackAt_944_split subroutine_ok_withLsCodeRoLoaded_of_left uc_copy_recompose
   uc_dec_copy_recompose unchunkedCt1SentAt_extract unchunkedEkSentCt1ReceivedAt_extract
   vecWordsList wordsAt wordsAt_13 wordsAt_16)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsPlacedBudget (polyNextChunkPlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlacedBudget (AllocContractsPlaced)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.TopPlacedBudget (poly_next_chunk_caller_ok_x)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget
  (Ct1ReceivedSendEkChunkEnv Ct1ReceivedSendEkChunkPlacedOkX
   Ct1ReceivedSendEkChunkPlacedOkXOfEnv Ct1SampledSendCt1ChunkEnv
   Ct1SampledSendCt1ChunkPlacedOkX Ct1SampledSendCt1ChunkPlacedOkXOfEnv PolyEncoderNextChunkEnv
   call_memcpy_relocate_pool call_polyNextChunk_placed ct1ReceivedSendEkChunkPlacedSpecOfEnv
   ct1SampledSendCt1ChunkPlacedSpecOfEnv sepWP_seq_lscro)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyBudgetSpec)

/-! ## Re-Exports & Shared Pool-Sync / Postcondition Helpers -/

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget
  (Ct1ReceivedSendEkChunkEnv ct1ReceivedSendEkChunkEnv_nonempty
   ct1ReceivedSendEkChunkPlacedSpecOfEnv ct1ReceivedSendEkChunkPlacedSpec)

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget
  (Ct1ReceivedSendEkChunkPlacedOkXOfEnv Ct1ReceivedSendEkChunkPlacedOkX)

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget
  (Ct1SampledSendCt1ChunkEnv ct1SampledSendCt1ChunkEnv_nonempty
   ct1SampledSendCt1ChunkPlacedSpecOfEnv ct1SampledSendCt1ChunkPlacedSpec)

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget
  (Ct1SampledSendCt1ChunkPlacedOkXOfEnv Ct1SampledSendCt1ChunkPlacedOkX)

private theorem pc_setMem_pre (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by
  cases s; rfl
private theorem status_setMem_pre (s : State) (m : Memory) : (s.setMem m).status = s.status := by
  cases s; rfl
private theorem trace_setMem_pre (s : State) (m : Memory) : (s.setMem m).trace = s.trace := by
  cases s; rfl
private theorem calleeSavedVRegs_setMem_pre (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by
  cases s; rfl

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit bv_sub_sub BitVec.sub_add_cancel BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre pc_setMem_pre status_setMem_pre trace_setMem_pre
  calleeSavedVRegs_setMem_pre readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre

private theorem hookSat_memcpyRegion_of_sessionMemcpyBudget0'
    {H : String → Option (State → State)}
    (hsat : HookSat H "memcpy" (sessionMemcpyBudgetSpec 0)) :
    HookSat H "memcpy" (withVmPreserved sessionMemcpyRegionSpec) := by
  refine ProofLib.HookSat.mono hsat fun ⟨dst, src, bs⟩ R s0 hpre =>
    ⟨(dst, src, bs), R, ?_, fun sf hpost => ?_⟩
  · dsimp only [sessionMemcpyBudgetSpec, sessionMemcpySpec, libcMemcpySpec,
      withVmPreserved, sessionMemcpyRegionSpec, memcpyRegionSpec, stackAt] at hpre ⊢
    rw [ProofLib.memRegion_zero]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  · dsimp only [sessionMemcpyBudgetSpec, sessionMemcpySpec,
      withVmPreserved, sessionMemcpyRegionSpec, stackAt] at hpost ⊢
    rw [ProofLib.memRegion_zero] at hpost
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost

/-! ## 1. Block `345`: `<Ct1Received>::send_ek_chunk` (`41` insns) -/

/-- Envelope-parametric `[LibsignalPlacement]` contract for `<Ct1Received>::send_ek_chunk`
    (Block `345`), given `HookSat` on `memcpy` and `subroutine_ok` for `PolyEncoder::next_chunk`
    (Block `416`). -/
theorem ct1_received_send_ek_chunk_placed_cl_ext_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {Env : Ct1ReceivedSendEkChunkGhost F → List AllocEvent → Prop}
    (hsub : ∀ x evs, Ct1ReceivedSendEkChunkEnv x evs → Env x evs)
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" (withVmPreserved sessionMemcpyRegionSpec))
    (hnext : subroutine_ok (lsProg_345 (Rust.withPanics ext))
      (lsmpl.base 416) (withLsCodeRoLoaded lsmpl (polyNextChunkPlacedSpec M A lim))) :
    Ct1ReceivedSendEkChunkPlacedOkXOfEnv M A lim F ext Env := by
  unfold Ct1ReceivedSendEkChunkPlacedOkXOfEnv
  apply ls_subroutine_ok_to_blockProgram (calleeProg := lsProg_345 (Rust.withPanics ext))
  change subroutine_ok (lsProg_345 (Rust.withPanics ext)) (blkPl_345).base _
  apply subroutine_ok_withLsCodeRoLoaded_of_left
  have hmemcpy_ok : subroutine_ok (lsProg_345 (Rust.withPanics ext))
      (lsρ "memcpy") (withVmPreserved sessionMemcpyRegionSpec) :=
    spqr_hook_ok_of_mem hmemcpy
  simp only [ct1ReceivedSendEkChunkPlacedSpecOfEnv, lsProg_345,
    BitVec.ofNat_eq_ofNat] at hmemcpy_ok hnext ⊢
  wp_init x_st s0
  rcases x_st with ⟨⟨outA, stA, st, outSt, chunk⟩, st0⟩
  dsimp only at *
  have hcro0 : LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  subst ‹s0.readReg64 (Reg.gpr 8#5) = outA›
    ‹s0.readReg64 (Reg.gpr 0#5) = stA›
  have hfit0 : FitsEnv M lim st0
      (Env ⟨s0.readReg64 (Reg.gpr 8#5), s0.readReg64 (Reg.gpr 0#5), st, outSt, chunk⟩) := by
    assumption
  have hfit_nc : FitsEnv M lim st0 (PolyEncoderNextChunkEnv st.sending_ek) :=
    fun evs hevs => hfit0 evs (hsub ⟨s0.readReg64 (Reg.gpr 8#5), s0.readReg64 (Reg.gpr 0#5), st, outSt, chunk⟩ evs hevs)
  obtain ⟨hnc_ok, hout_eq⟩ := ct1Received_send_ek_chunk_ok (by assumption)
  have hfsp_align : ((s0.sp - 944#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 944#64 (by assumption) (by decide)
  apply sepWP_seq_lscro hcro0 (mid := lsmpl.base 416)
  wp_conv_pre =>
    rw [ProofLib.memRegion_split' (b := s0.readReg64 (Reg.gpr 8#5)) (n := 504) (k := chunkSize)
        (b' := s0.readReg64 (Reg.gpr 8#5) + 504#64) rfl rfl (by decide),
        stackAt_944_split s0.sp]
    unfold chunkedCt1ReceivedAt
  refine SepWP.fold (cells_13_unfold (s0.sp - 136#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_4_unfold (s0.sp - 32#64)) (by sep_focus) ?_
  wp_pull_exists
  refine SepWP.fold (unchunkedEkSentCt1ReceivedAt_extract A.repAlloc
    (s0.readReg64 (Reg.gpr 0#5) + 400#64) st.uc) (by sep_focus) ?_
  wp_pull_exists
  rename_i g
  have hst_words :
      wordsAt (s0.readReg64 (Reg.gpr 0#5) + 400#64) (ekSentCt1ReceivedWordsList g st.uc.epoch) =
      (((s0.readReg64 (Reg.gpr 0#5) + 400#64) ↦₆₄ g.v1.w0) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 408#64) ↦₆₄ g.v1.w1) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 416#64) ↦₆₄ g.v1.w2) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 424#64) ↦₆₄ g.rest.v1.w0) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 432#64) ↦₆₄ g.rest.v1.w1) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 440#64) ↦₆₄ g.rest.v1.w2) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 448#64) ↦₆₄ g.rest.auth.v1.w0) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 456#64) ↦₆₄ g.rest.auth.v1.w1) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 464#64) ↦₆₄ g.rest.auth.v1.w2) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 472#64) ↦₆₄ g.rest.auth.v2.w0) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 480#64) ↦₆₄ g.rest.auth.v2.w1) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 488#64) ↦₆₄ g.rest.auth.v2.w2) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 496#64) ↦₆₄ st.uc.epoch)) := by
    dsimp only [ekSentCt1ReceivedWordsList, ekSentWordsList, ct2SentWordsList, authWordsList,
      vecWordsList, List.append]
    simp only [wordsAt_13, BitVec.add_assoc, arm64_norm]
  have hsp_words :
      wordsAt (s0.sp - 136#64) (ekSentCt1ReceivedWordsList g st.uc.epoch) =
      (((s0.sp - 136#64) ↦₆₄ g.v1.w0) ∗
       ((s0.sp - 128#64) ↦₆₄ g.v1.w1) ∗
       ((s0.sp - 120#64) ↦₆₄ g.v1.w2) ∗
       ((s0.sp - 112#64) ↦₆₄ g.rest.v1.w0) ∗
       ((s0.sp - 104#64) ↦₆₄ g.rest.v1.w1) ∗
       ((s0.sp - 96#64) ↦₆₄ g.rest.v1.w2) ∗
       ((s0.sp - 88#64) ↦₆₄ g.rest.auth.v1.w0) ∗
       ((s0.sp - 80#64) ↦₆₄ g.rest.auth.v1.w1) ∗
       ((s0.sp - 72#64) ↦₆₄ g.rest.auth.v1.w2) ∗
       ((s0.sp - 64#64) ↦₆₄ g.rest.auth.v2.w0) ∗
       ((s0.sp - 56#64) ↦₆₄ g.rest.auth.v2.w1) ∗
       ((s0.sp - 48#64) ↦₆₄ g.rest.auth.v2.w2) ∗
       ((s0.sp - 40#64) ↦₆₄ st.uc.epoch)) := by
    dsimp only [ekSentCt1ReceivedWordsList, ekSentWordsList, ct2SentWordsList, authWordsList,
      vecWordsList, List.append]
    simp only [wordsAt_13, arm64_norm]
  wp_conv_pre =>
    rw [hst_words]
    simp only [wordsAt_13, arm64_norm]
  wp_steps_sync_pool (lsρ "memcpy")
  refine call_memcpy_relocate_pool (st := st0) hmemcpy_ok (s0 := s0)
    (Relocatable.of_polyEncoderAt A.repAlloc st.sending_ek)
    (s0.sp - 936#64) (s0.readReg64 (Reg.gpr 0#5))
    (ret_pc := (blkPl_345).base + 104#64) (sp_call := s0.sp - 944#64)
    (v19 := s0.readReg64 (Reg.gpr 8#5)) (v20 := s0.readReg64 (Reg.gpr 20#5))
    (by simp only [arm64_norm])
    (by simpa only [arm64_norm] using ‹s0.status = .Running›)
    (by simp only [State.sp, arm64_norm])
    hfsp_align
    (by simp only [Reg.lr, arm64_norm])
    (by simp only [arm64_norm])
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [arm64_norm])
    (by simp only [Reg.x0, arm64_norm])
    (by simp only [Reg.x1, arm64_norm])
    (by simp only [Reg.x2, arm64_norm])
    (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 hregs1 htr1 _hvm1 => ?_)
  rcases hregs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hvregs_1⟩
  refine SepWP.fold (Entails.of_eq hst_words.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hsp_words.symm) (by sep_focus) ?_
  refine SepWP.fold (uc_copy_recompose (k := 104) (by decide)
    (s0.readReg64 (Reg.gpr 0#5)) (s0.sp - 136#64)
    (ekSentCt1ReceivedWordsList g st.uc.epoch) rfl) (by sep_focus) ?_
  wp_steps_sync_pool (lsmpl.base 416)
  refine call_polyNextChunk_placed hnext
    (s0.readReg64 (Reg.gpr 8#5) + 504#64) (s0.sp - 936#64)
    st.sending_ek outSt.sending_ek chunk st0
    (ret_pc := (blkPl_345).base + 116#64) (sp_call := s0.sp - 944#64)
    (v19 := s0.readReg64 (Reg.gpr 8#5)) (v20 := s0.readReg64 (Reg.gpr 20#5))
    (by simp only [arm64_norm])
    (by simpa only [arm64_norm] using hrun1)
    (by simp only [State.sp, arm64_norm, hsp1])
    hfsp_align
    (by simp only [Reg.lr, arm64_norm])
    (by simp only [arm64_norm, htr1])
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hvregs_1])
    (by simp only [Reg.x8, arm64_norm, hx19_1])
    (by simp only [Reg.x0, arm64_norm, hsp1])
    hnc_ok
    hfit_nc
    (by sep_focus)
    (fun sf2 evs hpc2 hrun2 hsp2 hregs2 htr2 hevs => ?_)
  rcases hregs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hvregs_2⟩
  wp_steps_sync_pool (lsρ "memcpy")
  refine call_memcpy_relocate_pool (st := M.stepEvents evs st0) hmemcpy_ok (s0 := s0)
    (Relocatable.of_polyEncoderAt A.repAlloc outSt.sending_ek)
    (s0.sp - 536#64) (s0.sp - 936#64)
    (ret_pc := (blkPl_345).base + 132#64) (sp_call := s0.sp - 944#64)
    (v19 := s0.readReg64 (Reg.gpr 8#5)) (v20 := s0.readReg64 (Reg.gpr 20#5))
    (by simp only [arm64_norm])
    (by simpa only [arm64_norm] using hrun2)
    (by simp only [State.sp, arm64_norm, hsp2])
    hfsp_align
    (by simp only [Reg.lr, arm64_norm])
    (by simp only [arm64_norm, htr2])
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hvregs_2])
    (by simp only [Reg.x0, arm64_norm, hsp2])
    (by simp only [Reg.x1, arm64_norm, hsp2])
    (by simp only [Reg.x2, arm64_norm])
    (by sep_focus)
    (fun sf3 hpc3 hrun3 hsp3 hregs3 htr3 _hvm3 => ?_)
  rcases hregs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hvregs_3⟩
  refine SepWP.fold (chunkedCt1ReceivedAt_recompose_sp A.repAlloc s0.sp st outSt hout_eq)
    (by sep_focus) ?_
  wp_steps_sync_pool (lsρ "memcpy")
  refine call_memcpy_relocate_pool (st := M.stepEvents evs st0) hmemcpy_ok (s0 := s0)
    (Relocatable.of_chunkedCt1ReceivedAt A.repAlloc outSt)
    (s0.readReg64 (Reg.gpr 8#5)) (s0.sp - 536#64)
    (ret_pc := (blkPl_345).base + 148#64) (sp_call := s0.sp - 944#64)
    (v19 := s0.readReg64 (Reg.gpr 8#5)) (v20 := s0.readReg64 (Reg.gpr 20#5))
    (by simp only [arm64_norm])
    (by simpa only [arm64_norm] using hrun3)
    (by simp only [State.sp, arm64_norm, hsp3])
    hfsp_align
    (by simp only [Reg.lr, arm64_norm])
    (by simp only [arm64_norm, htr3])
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [arm64_norm, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hvregs_3])
    (by simp only [Reg.x0, arm64_norm, hx19_3])
    (by simp only [Reg.x1, arm64_norm, hsp3])
    (by simp only [Reg.x2, arm64_norm])
    (by sep_focus)
    (fun sf4 hpc4 hrun4 hsp4 hregs4 htr4 _hvm4 => ?_)
  rcases hregs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hvregs_4⟩
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  refine SepWP.fold (stackAt_944_rejoin s0.sp _ _ _ _) (by sep_focus) ?_
  refine SepWP.done
    (by simp only [Reg.lr, arm64_norm])
    (by simpa only [arm64_norm] using hrun4)
    ⟨?_, by simp only [State.sp, arm64_norm, hsp4],
     by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26,
          Reg.x27, Reg.x28, Reg.fp, arm64_norm,
          hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hvregs_4]⟩
  intro hm
  try rw [sepExists_sepConj_left]
  rw [satisfies_sepExists]
  refine ⟨evs, ?_⟩
  try simp only [Nat.reduceAdd, sepConj_assoc] at hm ⊢
  rw [satisfies_pure_sepConj]
  refine ⟨⟨by simp only [arm64_norm, htr4],
    hsub ⟨s0.readReg64 (Reg.gpr 8#5), s0.readReg64 (Reg.gpr 0#5), st, outSt, chunk⟩ evs hevs⟩, ?_⟩
  exact Satisfies.of_eq hm (by sep_ac_rfl)

theorem ct1_received_send_ek_chunk_placed_cl_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" (withVmPreserved sessionMemcpyRegionSpec))
    (hnext : subroutine_ok (lsProg_345 (Rust.withPanics ext))
      (lsmpl.base 416) (withLsCodeRoLoaded lsmpl (polyNextChunkPlacedSpec M A lim))) :
    Ct1ReceivedSendEkChunkPlacedOkX M A lim F ext :=
  ct1_received_send_ek_chunk_placed_cl_ext_ofEnv (fun _ _ h => h) hmemcpy hnext

/-- Closed envelope-parametric `[LibsignalPlacement]` contract for `<Ct1Received>::send_ek_chunk`
    (Block `345`) discharging `PolyEncoder::next_chunk` (Block `416`) via
    `poly_next_chunk_caller_ok_x`. -/
theorem ct1_received_send_ek_chunk_placed_ok_x_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {Env : Ct1ReceivedSendEkChunkGhost F → List AllocEvent → Prop}
    (hsub : ∀ x evs, Ct1ReceivedSendEkChunkEnv x evs → Env x evs)
    (hA : AllocContractsPlaced M A lim ext) :
    Ct1ReceivedSendEkChunkPlacedOkXOfEnv M A lim F ext Env :=
  ct1_received_send_ek_chunk_placed_cl_ext_ofEnv hsub
    (hookSat_memcpyRegion_of_sessionMemcpyBudget0' (hA.session_memcpy 0))
    (poly_next_chunk_caller_ok_x (callerProg := lsProg_345 (Rust.withPanics ext))
      (i := 345) M A lim ext hA)

/-- Closed canonical `[LibsignalPlacement]` contract for `<Ct1Received>::send_ek_chunk`
    (Block `345`). -/
theorem ct1_received_send_ek_chunk_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) :
    Ct1ReceivedSendEkChunkPlacedOkX M A lim F ext :=
  ct1_received_send_ek_chunk_placed_ok_x_ofEnv (fun _ _ h => h) hA

/-! ## 2. Block `335`: `<Ct1Sampled>::send_ct1_chunk` (`41` insns) -/

/-- Envelope-parametric `[LibsignalPlacement]` contract for `<Ct1Sampled>::send_ct1_chunk`
    (Block `335`), given `HookSat` on `memcpy` and `subroutine_ok` for `PolyEncoder::next_chunk`
    (Block `416`). -/
theorem ct1_sampled_send_ct1_chunk_placed_cl_ext_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {Env : Ct1SampledSendCt1ChunkGhost F → List AllocEvent → Prop}
    (hsub : ∀ x evs, Ct1SampledSendCt1ChunkEnv x evs → Env x evs)
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" (withVmPreserved sessionMemcpyRegionSpec))
    (hnext : subroutine_ok (lsProg_335 (Rust.withPanics ext))
      (lsmpl.base 416) (withLsCodeRoLoaded lsmpl (polyNextChunkPlacedSpec M A lim))) :
    Ct1SampledSendCt1ChunkPlacedOkXOfEnv M A lim F ext Env := by
  unfold Ct1SampledSendCt1ChunkPlacedOkXOfEnv
  apply ls_subroutine_ok_to_blockProgram (calleeProg := lsProg_335 (Rust.withPanics ext))
  change subroutine_ok (lsProg_335 (Rust.withPanics ext)) (blkPl_335).base _
  apply subroutine_ok_withLsCodeRoLoaded_of_left
  have hmemcpy_ok : subroutine_ok (lsProg_335 (Rust.withPanics ext))
      (lsρ "memcpy") (withVmPreserved sessionMemcpyRegionSpec) :=
    spqr_hook_ok_of_mem hmemcpy
  simp only [ct1SampledSendCt1ChunkPlacedSpecOfEnv, lsProg_335,
    BitVec.ofNat_eq_ofNat] at hmemcpy_ok hnext ⊢
  wp_init x_st s0
  rcases x_st with ⟨⟨outA, stA, st, outSt, chunk⟩, st0⟩
  dsimp only at *
  have hcro0 : LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  subst ‹s0.readReg64 (Reg.gpr 8#5) = outA›
    ‹s0.readReg64 (Reg.gpr 0#5) = stA›
  have hfit0 : FitsEnv M lim st0
      (Env ⟨s0.readReg64 (Reg.gpr 8#5), s0.readReg64 (Reg.gpr 0#5), st, outSt, chunk⟩) := by
    assumption
  have hfit_nc : FitsEnv M lim st0 (PolyEncoderNextChunkEnv st.sending_ct1) :=
    fun evs hevs => hfit0 evs (hsub ⟨s0.readReg64 (Reg.gpr 8#5), s0.readReg64 (Reg.gpr 0#5), st, outSt, chunk⟩ evs hevs)
  obtain ⟨hnc_ok, hout_eq⟩ := ct1Sampled_send_ct1_chunk_ok (by assumption)
  have hfsp_align : ((s0.sp - 1376#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 1376#64 (by assumption) (by decide)
  apply sepWP_seq_lscro hcro0 (mid := lsmpl.base 416)
  wp_conv_pre =>
    rw [ProofLib.memRegion_split' (b := s0.readReg64 (Reg.gpr 8#5)) (n := 928) (k := chunkSize)
        (b' := s0.readReg64 (Reg.gpr 8#5) + 928#64) rfl rfl (by decide),
        stackAt_1376_split s0.sp]
    unfold chunkedCt1SampledAt
  refine SepWP.fold (cells_1_unfold (s0.sp - 1376#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_16_unfold (s0.sp - 576#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_6_unfold (s0.sp - 48#64)) (by sep_focus) ?_
  wp_pull_exists
  refine SepWP.fold (unchunkedCt1SentAt_extract A.repAlloc
    (s0.readReg64 (Reg.gpr 0#5) + 400#64) st.uc) (by sep_focus) ?_
  wp_pull_exists
  rename_i g
  have hst_words :
      wordsAt (s0.readReg64 (Reg.gpr 0#5) + 400#64) (fiveVecWordsList g st.uc.epoch) =
      (((s0.readReg64 (Reg.gpr 0#5) + 400#64) ↦₆₄ g.v1.w0) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 408#64) ↦₆₄ g.v1.w1) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 416#64) ↦₆₄ g.v1.w2) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 424#64) ↦₆₄ g.rest.v1.w0) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 432#64) ↦₆₄ g.rest.v1.w1) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 440#64) ↦₆₄ g.rest.v1.w2) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 448#64) ↦₆₄ g.rest.rest.v1.w0) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 456#64) ↦₆₄ g.rest.rest.v1.w1) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 464#64) ↦₆₄ g.rest.rest.v1.w2) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 472#64) ↦₆₄ g.rest.rest.auth.v1.w0) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 480#64) ↦₆₄ g.rest.rest.auth.v1.w1) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 488#64) ↦₆₄ g.rest.rest.auth.v1.w2) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 496#64) ↦₆₄ g.rest.rest.auth.v2.w0) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 504#64) ↦₆₄ g.rest.rest.auth.v2.w1) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 512#64) ↦₆₄ g.rest.rest.auth.v2.w2) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 520#64) ↦₆₄ st.uc.epoch)) := by
    dsimp only [fiveVecWordsList, ekSentCt1ReceivedWordsList, ekSentWordsList, ct2SentWordsList,
      authWordsList, vecWordsList, List.append]
    simp only [wordsAt_16, BitVec.add_assoc, arm64_norm]
  have hsp_words :
      wordsAt (s0.sp - 576#64) (fiveVecWordsList g st.uc.epoch) =
      (((s0.sp - 576#64) ↦₆₄ g.v1.w0) ∗
       ((s0.sp - 568#64) ↦₆₄ g.v1.w1) ∗
       ((s0.sp - 560#64) ↦₆₄ g.v1.w2) ∗
       ((s0.sp - 552#64) ↦₆₄ g.rest.v1.w0) ∗
       ((s0.sp - 544#64) ↦₆₄ g.rest.v1.w1) ∗
       ((s0.sp - 536#64) ↦₆₄ g.rest.v1.w2) ∗
       ((s0.sp - 528#64) ↦₆₄ g.rest.rest.v1.w0) ∗
       ((s0.sp - 520#64) ↦₆₄ g.rest.rest.v1.w1) ∗
       ((s0.sp - 512#64) ↦₆₄ g.rest.rest.v1.w2) ∗
       ((s0.sp - 504#64) ↦₆₄ g.rest.rest.auth.v1.w0) ∗
       ((s0.sp - 496#64) ↦₆₄ g.rest.rest.auth.v1.w1) ∗
       ((s0.sp - 488#64) ↦₆₄ g.rest.rest.auth.v1.w2) ∗
       ((s0.sp - 480#64) ↦₆₄ g.rest.rest.auth.v2.w0) ∗
       ((s0.sp - 472#64) ↦₆₄ g.rest.rest.auth.v2.w1) ∗
       ((s0.sp - 464#64) ↦₆₄ g.rest.rest.auth.v2.w2) ∗
       ((s0.sp - 456#64) ↦₆₄ st.uc.epoch)) := by
    dsimp only [fiveVecWordsList, ekSentCt1ReceivedWordsList, ekSentWordsList, ct2SentWordsList,
      authWordsList, vecWordsList, List.append]
    simp only [wordsAt_16, arm64_norm]
  wp_conv_pre =>
    rw [hst_words]
    simp only [wordsAt_16, arm64_norm]
  wp_steps_sync_pool (lsρ "memcpy")
  refine SepWP.fold (cell_0_rejoin_400 s0.sp 1376#64 1368#64 0#64 (by bv_omega)) (by sep_focus) ?_
  refine call_memcpy_relocate_pool (st := st0) hmemcpy_ok (s0 := s0)
    (Relocatable.of_polyEncoderAt A.repAlloc st.sending_ct1)
    (s0.sp - 1376#64) (s0.readReg64 (Reg.gpr 0#5))
    (ret_pc := (blkPl_335).base + 80#64) (sp_call := s0.sp - 1376#64)
    (v19 := s0.readReg64 (Reg.gpr 0#5)) (v20 := s0.readReg64 (Reg.gpr 8#5))
    (by simp only [arm64_norm])
    (by simpa only [arm64_norm] using ‹s0.status = .Running›)
    (by simp only [State.sp, arm64_norm])
    hfsp_align
    (by simp only [Reg.lr, arm64_norm])
    (by simp only [arm64_norm])
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [arm64_norm])
    (by simp only [Reg.x0, arm64_norm])
    (by simp only [Reg.x1, arm64_norm])
    (by simp only [Reg.x2, arm64_norm])
    (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 hregs1 htr1 _hvm1 => ?_)
  rcases hregs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hvregs_1⟩
  wp_steps_sync_pool (lsρ "memcpy")
  refine call_memcpy_relocate_pool (st := st0) hmemcpy_ok (s0 := s0)
    (Relocatable.of_polyDecoderAt A.repAlloc st.receiving_ek)
    (s0.sp - 448#64) (s0.readReg64 (Reg.gpr 0#5) + 528#64)
    (ret_pc := (blkPl_335).base + 100#64) (sp_call := s0.sp - 1376#64)
    (v19 := s0.readReg64 (Reg.gpr 0#5)) (v20 := s0.readReg64 (Reg.gpr 8#5))
    (by simp only [arm64_norm])
    (by simpa only [arm64_norm] using hrun1)
    (by simp only [State.sp, arm64_norm, hsp1])
    hfsp_align
    (by simp only [Reg.lr, arm64_norm])
    (by simp only [arm64_norm, htr1])
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hvregs_1])
    (by simp only [Reg.x0, arm64_norm, hsp1])
    (by simp only [Reg.x1, arm64_norm, hx19_1])
    (by simp only [Reg.x2, arm64_norm])
    (by sep_focus)
    (fun sf2 hpc2 hrun2 hsp2 hregs2 htr2 _hvm2 => ?_)
  rcases hregs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hvregs_2⟩
  refine SepWP.fold (Entails.of_eq hst_words.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hsp_words.symm) (by sep_focus) ?_
  refine SepWP.fold (uc_dec_copy_recompose (k := 128) (by decide) (by decide)
    (s0.readReg64 (Reg.gpr 0#5)) (s0.sp - 576#64) (by bv_omega)
    (fiveVecWordsList g st.uc.epoch) rfl) (by sep_focus) ?_
  wp_steps_sync_pool (lsmpl.base 416)
  refine call_polyNextChunk_placed hnext
    (s0.readReg64 (Reg.gpr 8#5) + 928#64) (s0.sp - 1376#64)
    st.sending_ct1 outSt.sending_ct1 chunk st0
    (ret_pc := (blkPl_335).base + 112#64) (sp_call := s0.sp - 1376#64)
    (v19 := s0.readReg64 (Reg.gpr 0#5)) (v20 := s0.readReg64 (Reg.gpr 8#5))
    (by simp only [arm64_norm])
    (by simpa only [arm64_norm] using hrun2)
    (by simp only [State.sp, arm64_norm, hsp2])
    hfsp_align
    (by simp only [Reg.lr, arm64_norm])
    (by simp only [arm64_norm, htr2])
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hvregs_2])
    (by simp only [Reg.x8, arm64_norm, hx20_2])
    (by simp only [Reg.x0, arm64_norm, hsp2])
    hnc_ok
    hfit_nc
    (by sep_focus)
    (fun sf3 evs hpc3 hrun3 hsp3 hregs3 htr3 hevs => ?_)
  rcases hregs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hvregs_3⟩
  wp_steps_sync_pool (lsρ "memcpy")
  refine call_memcpy_relocate_pool (st := M.stepEvents evs st0) hmemcpy_ok (s0 := s0)
    (Relocatable.of_polyEncoderAt A.repAlloc outSt.sending_ct1)
    (s0.sp - 976#64) (s0.sp - 1376#64)
    (ret_pc := (blkPl_335).base + 128#64) (sp_call := s0.sp - 1376#64)
    (v19 := s0.readReg64 (Reg.gpr 0#5)) (v20 := s0.readReg64 (Reg.gpr 8#5))
    (by simp only [arm64_norm])
    (by simpa only [arm64_norm] using hrun3)
    (by simp only [State.sp, arm64_norm, hsp3])
    hfsp_align
    (by simp only [Reg.lr, arm64_norm])
    (by simp only [arm64_norm, htr3])
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [arm64_norm, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hvregs_3])
    (by simp only [Reg.x0, arm64_norm, hsp3])
    (by simp only [Reg.x1, arm64_norm, hsp3])
    (by simp only [Reg.x2, arm64_norm])
    (by sep_focus)
    (fun sf4 hpc4 hrun4 hsp4 hregs4 htr4 _hvm4 => ?_)
  rcases hregs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hvregs_4⟩
  refine SepWP.fold (chunkedCt1SampledAt_recompose_sp A.repAlloc s0.sp st outSt hout_eq)
    (by sep_focus) ?_
  wp_steps_sync_pool (lsρ "memcpy")
  refine call_memcpy_relocate_pool (st := M.stepEvents evs st0) hmemcpy_ok (s0 := s0)
    (Relocatable.of_chunkedCt1SampledAt A.repAlloc outSt)
    (s0.readReg64 (Reg.gpr 8#5)) (s0.sp - 976#64)
    (ret_pc := (blkPl_335).base + 144#64) (sp_call := s0.sp - 1376#64)
    (v19 := s0.readReg64 (Reg.gpr 0#5)) (v20 := s0.readReg64 (Reg.gpr 8#5))
    (by simp only [arm64_norm])
    (by simpa only [arm64_norm] using hrun4)
    (by simp only [State.sp, arm64_norm, hsp4])
    hfsp_align
    (by simp only [Reg.lr, arm64_norm])
    (by simp only [arm64_norm, htr4])
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [arm64_norm, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hvregs_4])
    (by simp only [Reg.x0, arm64_norm, hx20_4])
    (by simp only [Reg.x1, arm64_norm, hsp4])
    (by simp only [Reg.x2, arm64_norm])
    (by sep_focus)
    (fun sf5 hpc5 hrun5 hsp5 hregs5 htr5 _hvm5 => ?_)
  rcases hregs5 with ⟨hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hvregs_5⟩
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  refine SepWP.fold (stackAt_1376_rejoin s0.sp _ _ _ _ _ _) (by sep_focus) ?_
  refine SepWP.done
    (by simp only [Reg.lr, arm64_norm])
    (by simpa only [arm64_norm] using hrun5)
    ⟨?_, by simp only [State.sp, arm64_norm, hsp5],
     by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26,
          Reg.x27, Reg.x28, Reg.fp, arm64_norm,
          hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hvregs_5]⟩
  intro hm
  try rw [sepExists_sepConj_left]
  rw [satisfies_sepExists]
  refine ⟨evs, ?_⟩
  try simp only [Nat.reduceAdd, sepConj_assoc] at hm ⊢
  rw [satisfies_pure_sepConj]
  refine ⟨⟨by simp only [arm64_norm, htr5],
    hsub ⟨s0.readReg64 (Reg.gpr 8#5), s0.readReg64 (Reg.gpr 0#5), st, outSt, chunk⟩ evs hevs⟩, ?_⟩
  exact Satisfies.of_eq hm (by sep_ac_rfl)

theorem ct1_sampled_send_ct1_chunk_placed_cl_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" (withVmPreserved sessionMemcpyRegionSpec))
    (hnext : subroutine_ok (lsProg_335 (Rust.withPanics ext))
      (lsmpl.base 416) (withLsCodeRoLoaded lsmpl (polyNextChunkPlacedSpec M A lim))) :
    Ct1SampledSendCt1ChunkPlacedOkX M A lim F ext :=
  ct1_sampled_send_ct1_chunk_placed_cl_ext_ofEnv (fun _ _ h => h) hmemcpy hnext

/-- Closed envelope-parametric `[LibsignalPlacement]` contract for `<Ct1Sampled>::send_ct1_chunk`
    (Block `335`) discharging `PolyEncoder::next_chunk` (Block `416`) via
    `poly_next_chunk_caller_ok_x`. -/
theorem ct1_sampled_send_ct1_chunk_placed_ok_x_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {Env : Ct1SampledSendCt1ChunkGhost F → List AllocEvent → Prop}
    (hsub : ∀ x evs, Ct1SampledSendCt1ChunkEnv x evs → Env x evs)
    (hA : AllocContractsPlaced M A lim ext) :
    Ct1SampledSendCt1ChunkPlacedOkXOfEnv M A lim F ext Env :=
  ct1_sampled_send_ct1_chunk_placed_cl_ext_ofEnv hsub
    (hookSat_memcpyRegion_of_sessionMemcpyBudget0' (hA.session_memcpy 0))
    (poly_next_chunk_caller_ok_x (callerProg := lsProg_335 (Rust.withPanics ext))
      (i := 335) M A lim ext hA)

/-- Closed canonical `[LibsignalPlacement]` contract for `<Ct1Sampled>::send_ct1_chunk`
    (Block `335`). -/
theorem ct1_sampled_send_ct1_chunk_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) :
    Ct1SampledSendCt1ChunkPlacedOkX M A lim F ext :=
  ct1_sampled_send_ct1_chunk_placed_ok_x_ofEnv (fun _ _ h => h) hA

end LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk2PlacedBudget
