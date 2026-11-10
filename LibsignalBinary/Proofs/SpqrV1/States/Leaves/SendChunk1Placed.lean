/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.TopPlaced
import ProofLib.SepLogic.WPp

/-!
# Chunked Braid Send-Chunk Leaf Transitions 1 (Relocatable)

Relocatable `[LibsignalPlacement]` contracts for `<EkReceivedCt1Sampled>::send_ct1_chunk`
(Block `344`), `<Ct2Sampled>::send_ct2_chunk` (Block `354`), and `<HeaderSent>::send_ek_chunk`
(Block `336`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.States.Leaves

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.NextChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Alloc

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit bv_sub_sub BitVec.sub_add_cancel BitVec.toNat_zero

private theorem hookSat_memcpyRegion_of_sessionMemcpy0
    {H : String → Option (State → State)}
    (hsat : HookSat H "memcpy" (sessionMemcpySpec 0)) :
    HookSat H "memcpy" sessionMemcpyRegionSpec := by
  refine ProofLib.HookSat.mono hsat fun ⟨dst, src, bs⟩ R s0 hpre =>
    ⟨(dst, src, bs), R, ?_, fun sf hpost => ?_⟩
  · dsimp only [sessionMemcpySpec, libcMemcpySpec, sessionMemcpyRegionSpec, memcpyRegionSpec, stackAt] at hpre ⊢
    simpa only [ProofLib.memRegion_zero, sepConj_emp, emp_sepConj, sepConj_assoc] using hpre
  · dsimp only [sessionMemcpySpec, sessionMemcpyRegionSpec, stackAt] at hpost ⊢
    simpa only [ProofLib.memRegion_zero, sepConj_emp, emp_sepConj, sepConj_assoc] using hpost

/-! ## 1. Block `344`: `<EkReceivedCt1Sampled>::send_ct1_chunk` (32 insns) -/

theorem ek_received_ct1_sampled_send_ct1_chunk_placed_cl_ext [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionSpec)
    (hnext : subroutine_ok (lsProg_344 (Rust.withPanics ext))
      (lsmpl.base 416) (withLsCodeRoLoaded lsmpl (polyNextChunkPlacedSpec A))) :
    EkReceivedCt1SampledSendCt1ChunkPlacedOkX A F ext := by
  unfold EkReceivedCt1SampledSendCt1ChunkPlacedOkX
  apply ls_subroutine_ok_to_blockProgram (calleeProg := lsProg_344 (Rust.withPanics ext))
  change subroutine_ok (lsProg_344 (Rust.withPanics ext)) (blkPl_344).base _
  apply subroutine_ok_withLsCodeRoLoaded_of_left
  have hmemcpy_ok : subroutine_ok (lsProg_344 (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionSpec :=
    spqr_hook_ok_of_mem hmemcpy
  simp only [ekReceivedCt1SampledSendCt1ChunkPlacedSpec, lsProg_344,
    BitVec.ofNat_eq_ofNat] at hmemcpy_ok hnext ⊢
  wpp_init x s0
  rcases x with ⟨outA, stA, st, outSt, chunk⟩
  dsimp only at *
  have hcro0 : LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  subst ‹s0.readReg64 (Reg.gpr 8#5) = outA›
    ‹s0.readReg64 (Reg.gpr 0#5) = stA›
  obtain ⟨hnc_ok, hout_eq⟩ := ekReceivedCt1Sampled_send_ct1_chunk_ok (by assumption)
  have hfsp_align : ((s0.sp - 960#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 960#64 (by assumption) (by decide)
  apply of_sepWP_lscro hcro0 (mid := lsmpl.base 416)
  wp_conv_pre =>
    rw [ProofLib.memRegion_split' (b := s0.readReg64 (Reg.gpr 8#5)) (n := 528) (k := chunkSize)
        (b' := s0.readReg64 (Reg.gpr 8#5) + 528#64) rfl rfl (by decide),
        stackAt_960_split s0.sp]
    unfold chunkedEkReceivedCt1SampledAt
  refine SepWP.fold (cells_16_unfold (s0.sp - 160#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_4_unfold (s0.sp - 32#64)) (by sep_focus) ?_
  wp_pull_exists
  refine SepWP.fold (unchunkedCt1SentEkReceivedAt_extract A
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
    dsimp only [fiveVecWordsList, ekSentCt1ReceivedWordsList, ekSentWordsList,
      ct2SentWordsList, authWordsList, vecWordsList, List.append]
    simp only [wordsAt_16, BitVec.add_assoc, arm64_norm]
  have hsp_words :
      wordsAt (s0.sp - 160#64) (fiveVecWordsList g st.uc.epoch) =
      (((s0.sp - 160#64) ↦₆₄ g.v1.w0) ∗
       ((s0.sp - 152#64) ↦₆₄ g.v1.w1) ∗
       ((s0.sp - 144#64) ↦₆₄ g.v1.w2) ∗
       ((s0.sp - 136#64) ↦₆₄ g.rest.v1.w0) ∗
       ((s0.sp - 128#64) ↦₆₄ g.rest.v1.w1) ∗
       ((s0.sp - 120#64) ↦₆₄ g.rest.v1.w2) ∗
       ((s0.sp - 112#64) ↦₆₄ g.rest.rest.v1.w0) ∗
       ((s0.sp - 104#64) ↦₆₄ g.rest.rest.v1.w1) ∗
       ((s0.sp - 96#64) ↦₆₄ g.rest.rest.v1.w2) ∗
       ((s0.sp - 88#64) ↦₆₄ g.rest.rest.auth.v1.w0) ∗
       ((s0.sp - 80#64) ↦₆₄ g.rest.rest.auth.v1.w1) ∗
       ((s0.sp - 72#64) ↦₆₄ g.rest.rest.auth.v1.w2) ∗
       ((s0.sp - 64#64) ↦₆₄ g.rest.rest.auth.v2.w0) ∗
       ((s0.sp - 56#64) ↦₆₄ g.rest.rest.auth.v2.w1) ∗
       ((s0.sp - 48#64) ↦₆₄ g.rest.rest.auth.v2.w2) ∗
       ((s0.sp - 40#64) ↦₆₄ st.uc.epoch)) := by
    dsimp only [fiveVecWordsList, ekSentCt1ReceivedWordsList, ekSentWordsList,
      ct2SentWordsList, authWordsList, vecWordsList, List.append]
    simp only [wordsAt_16, arm64_norm]
  wp_conv_pre =>
    rw [hst_words]
    simp only [wordsAt_16, arm64_norm]
  wp_steps
  refine call_memcpy_relocate hmemcpy_ok (s0 := s0) (Relocatable.of_polyEncoderAt A st.sending_ct1)
    (s0.sp - 960#64) (s0.readReg64 (Reg.gpr 0#5))
    (ret_pc := (blkPl_344).base + 68#64) (sp_call := s0.sp - 960#64)
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
    (fun sf1 hpc1 hrun1 hsp1 hregs1 htr1 => ?_)
  rcases hregs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hvregs_1⟩
  refine SepWP.fold (Entails.of_eq hst_words.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hsp_words.symm) (by sep_focus) ?_
  refine SepWP.fold (uc_copy_recompose (k := 128) (by decide)
    (s0.readReg64 (Reg.gpr 0#5)) (s0.sp - 160#64)
    (fiveVecWordsList g st.uc.epoch) rfl) (by sep_focus) ?_
  wp_steps
  refine call_polyNextChunk_placed hnext
    (s0.readReg64 (Reg.gpr 8#5) + 528#64) (s0.sp - 960#64)
    st.sending_ct1 outSt.sending_ct1 chunk
    (ret_pc := (blkPl_344).base + 80#64) (sp_call := s0.sp - 960#64)
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
    (by sep_focus)
    (fun sf2 hpc2 hrun2 hsp2 hregs2 htr2 => ?_)
  rcases hregs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hvregs_2⟩
  wp_steps
  refine call_memcpy_relocate hmemcpy_ok (s0 := s0) (Relocatable.of_polyEncoderAt A outSt.sending_ct1)
    (s0.sp - 560#64) (s0.sp - 960#64)
    (ret_pc := (blkPl_344).base + 96#64) (sp_call := s0.sp - 960#64)
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
    (fun sf3 hpc3 hrun3 hsp3 hregs3 htr3 => ?_)
  rcases hregs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hvregs_3⟩
  refine SepWP.fold (chunkedEkReceivedCt1SampledAt_recompose_sp A s0.sp st outSt hout_eq)
    (by sep_focus) ?_
  wp_steps
  refine call_memcpy_relocate hmemcpy_ok (s0 := s0) (Relocatable.of_chunkedEkReceivedCt1SampledAt A outSt)
    (s0.readReg64 (Reg.gpr 8#5)) (s0.sp - 560#64)
    (ret_pc := (blkPl_344).base + 112#64) (sp_call := s0.sp - 960#64)
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
    (fun sf4 hpc4 hrun4 hsp4 hregs4 htr4 => ?_)
  rcases hregs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hvregs_4⟩
  wp_steps
  refine SepWP.fold (stackAt_960_rejoin s0.sp _ _ _ _) (by sep_focus) ?_
  wp_done

/-- Closed `[LibsignalPlacement]` contract for `<EkReceivedCt1Sampled>::send_ct1_chunk` (Block `344`)
    discharging `<PolyEncoder as Encoder>::next_chunk` (Block `416`) via `poly_next_chunk_placed_ok`. -/
theorem ek_received_ct1_sampled_send_ct1_chunk_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced A ext) :
    EkReceivedCt1SampledSendCt1ChunkPlacedOkX A F ext :=
  ek_received_ct1_sampled_send_ct1_chunk_placed_cl_ext
    (hookSat_memcpyRegion_of_sessionMemcpy0 (hA.session_memcpy 0))
    (keys_ls_subroutine_ok_of_block_cro (i := 344) (j := 416)
      (poly_next_chunk_placed_ok A ext hA))

/-! ## 2. Block `354`: `<Ct2Sampled>::send_ct2_chunk` (34 insns) -/

theorem ct2_sampled_send_ct2_chunk_placed_cl_ext [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionSpec)
    (hnext : subroutine_ok (lsProg_354 (Rust.withPanics ext))
      (lsmpl.base 416) (withLsCodeRoLoaded lsmpl (polyNextChunkPlacedSpec A))) :
    Ct2SampledSendCt2ChunkPlacedOkX A F ext := by
  unfold Ct2SampledSendCt2ChunkPlacedOkX
  apply ls_subroutine_ok_to_blockProgram (calleeProg := lsProg_354 (Rust.withPanics ext))
  change subroutine_ok (lsProg_354 (Rust.withPanics ext)) (blkPl_354).base _
  apply subroutine_ok_withLsCodeRoLoaded_of_left
  have hmemcpy_ok : subroutine_ok (lsProg_354 (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionSpec :=
    spqr_hook_ok_of_mem hmemcpy
  simp only [ct2SampledSendCt2ChunkPlacedSpec, lsProg_354,
    BitVec.ofNat_eq_ofNat] at hmemcpy_ok hnext ⊢
  wpp_init x s0
  rcases x with ⟨outA, stA, st, outSt, chunk⟩
  dsimp only at *
  have hcro0 : LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  subst ‹s0.readReg64 (Reg.gpr 8#5) = outA›
    ‹s0.readReg64 (Reg.gpr 0#5) = stA›
  obtain ⟨hnc_ok, hout_eq⟩ := ct2Sampled_send_ct2_chunk_ok (by assumption)
  have hfsp_align : ((s0.sp - 896#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 896#64 (by assumption) (by decide)
  apply of_sepWP_lscro hcro0 (mid := lsmpl.base 416)
  wp_conv_pre =>
    rw [ProofLib.memRegion_split' (b := s0.readReg64 (Reg.gpr 8#5)) (n := 456) (k := chunkSize)
        (b' := s0.readReg64 (Reg.gpr 8#5) + 456#64) rfl rfl (by decide),
        stackAt_896_split s0.sp]
    unfold chunkedCt2SampledAt
  refine SepWP.fold (cells_7_unfold (s0.sp - 88#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_4_unfold (s0.sp - 32#64)) (by sep_focus) ?_
  wp_pull_exists
  refine SepWP.fold (unchunkedCt2SentAt_extract A
    (s0.readReg64 (Reg.gpr 0#5) + 400#64) st.uc) (by sep_focus) ?_
  wp_pull_exists
  rename_i g
  have hst_words :
      wordsAt (s0.readReg64 (Reg.gpr 0#5) + 400#64) (ct2SentWordsList g st.uc.epoch) =
      (((s0.readReg64 (Reg.gpr 0#5) + 400#64) ↦₆₄ g.v1.w0) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 408#64) ↦₆₄ g.v1.w1) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 416#64) ↦₆₄ g.v1.w2) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 424#64) ↦₆₄ g.v2.w0) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 432#64) ↦₆₄ g.v2.w1) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 440#64) ↦₆₄ g.v2.w2) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 448#64) ↦₆₄ st.uc.epoch)) := by
    dsimp only [ct2SentWordsList, authWordsList, vecWordsList, List.append]
    simp only [wordsAt_7, BitVec.add_assoc, arm64_norm]
  have hsp_words :
      wordsAt (s0.sp - 88#64) (ct2SentWordsList g st.uc.epoch) =
      (((s0.sp - 88#64) ↦₆₄ g.v1.w0) ∗
       ((s0.sp - 80#64) ↦₆₄ g.v1.w1) ∗
       ((s0.sp - 72#64) ↦₆₄ g.v1.w2) ∗
       ((s0.sp - 64#64) ↦₆₄ g.v2.w0) ∗
       ((s0.sp - 56#64) ↦₆₄ g.v2.w1) ∗
       ((s0.sp - 48#64) ↦₆₄ g.v2.w2) ∗
       ((s0.sp - 40#64) ↦₆₄ st.uc.epoch)) := by
    dsimp only [ct2SentWordsList, authWordsList, vecWordsList, List.append]
    simp only [wordsAt_7, arm64_norm]
  wp_conv_pre =>
    rw [hst_words]
    simp only [wordsAt_7, arm64_norm]
  wp_steps
  refine call_memcpy_relocate hmemcpy_ok (s0 := s0) (Relocatable.of_polyEncoderAt A st.sending_ct2)
    (s0.sp - 888#64) (s0.readReg64 (Reg.gpr 0#5))
    (ret_pc := (blkPl_354).base + 76#64) (sp_call := s0.sp - 896#64)
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
    (fun sf1 hpc1 hrun1 hsp1 hregs1 htr1 => ?_)
  rcases hregs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hvregs_1⟩
  refine SepWP.fold (Entails.of_eq hst_words.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hsp_words.symm) (by sep_focus) ?_
  refine SepWP.fold (uc_copy_recompose (k := 56) (by decide)
    (s0.readReg64 (Reg.gpr 0#5)) (s0.sp - 88#64)
    (ct2SentWordsList g st.uc.epoch) rfl) (by sep_focus) ?_
  wp_steps
  refine call_polyNextChunk_placed hnext
    (s0.readReg64 (Reg.gpr 8#5) + 456#64) (s0.sp - 888#64)
    st.sending_ct2 outSt.sending_ct2 chunk
    (ret_pc := (blkPl_354).base + 88#64) (sp_call := s0.sp - 896#64)
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
    (by sep_focus)
    (fun sf2 hpc2 hrun2 hsp2 hregs2 htr2 => ?_)
  rcases hregs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hvregs_2⟩
  wp_steps
  refine call_memcpy_relocate hmemcpy_ok (s0 := s0) (Relocatable.of_polyEncoderAt A outSt.sending_ct2)
    (s0.sp - 488#64) (s0.sp - 888#64)
    (ret_pc := (blkPl_354).base + 104#64) (sp_call := s0.sp - 896#64)
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
    (fun sf3 hpc3 hrun3 hsp3 hregs3 htr3 => ?_)
  rcases hregs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hvregs_3⟩
  refine SepWP.fold (chunkedCt2SampledAt_recompose_sp A s0.sp st outSt hout_eq)
    (by sep_focus) ?_
  wp_steps
  refine call_memcpy_relocate hmemcpy_ok (s0 := s0) (Relocatable.of_chunkedCt2SampledAt A outSt)
    (s0.readReg64 (Reg.gpr 8#5)) (s0.sp - 488#64)
    (ret_pc := (blkPl_354).base + 120#64) (sp_call := s0.sp - 896#64)
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
    (fun sf4 hpc4 hrun4 hsp4 hregs4 htr4 => ?_)
  rcases hregs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hvregs_4⟩
  wp_steps
  refine SepWP.fold (stackAt_896_rejoin s0.sp _ _ _ _) (by sep_focus) ?_
  wp_done

/-- Closed `[LibsignalPlacement]` contract for `<Ct2Sampled>::send_ct2_chunk` (Block `354`)
    discharging `<PolyEncoder as Encoder>::next_chunk` (Block `416`) via `poly_next_chunk_placed_ok`. -/
theorem ct2_sampled_send_ct2_chunk_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced A ext) :
    Ct2SampledSendCt2ChunkPlacedOkX A F ext :=
  ct2_sampled_send_ct2_chunk_placed_cl_ext
    (hookSat_memcpyRegion_of_sessionMemcpy0 (hA.session_memcpy 0))
    (keys_ls_subroutine_ok_of_block_cro (i := 354) (j := 416)
      (poly_next_chunk_placed_ok A ext hA))

/-! ## 3. Block `336`: `<HeaderSent>::send_ek_chunk` (39 insns) -/

theorem header_sent_send_ek_chunk_placed_cl_ext [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionSpec)
    (hnext : subroutine_ok (lsProg_336 (Rust.withPanics ext))
      (lsmpl.base 416) (withLsCodeRoLoaded lsmpl (polyNextChunkPlacedSpec A))) :
    HeaderSentSendEkChunkPlacedOkX A F ext := by
  unfold HeaderSentSendEkChunkPlacedOkX
  apply ls_subroutine_ok_to_blockProgram (calleeProg := lsProg_336 (Rust.withPanics ext))
  change subroutine_ok (lsProg_336 (Rust.withPanics ext)) (blkPl_336).base _
  apply subroutine_ok_withLsCodeRoLoaded_of_left
  have hmemcpy_ok : subroutine_ok (lsProg_336 (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionSpec :=
    spqr_hook_ok_of_mem hmemcpy
  simp only [headerSentSendEkChunkPlacedSpec, lsProg_336,
    BitVec.ofNat_eq_ofNat] at hmemcpy_ok hnext ⊢
  wpp_init x s0
  rcases x with ⟨outA, stA, st, outSt, chunk⟩
  dsimp only at *
  have hcro0 : LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  subst ‹s0.readReg64 (Reg.gpr 8#5) = outA›
    ‹s0.readReg64 (Reg.gpr 0#5) = stA›
  obtain ⟨hnc_ok, hout_eq⟩ := headerSent_send_ek_chunk_ok (by assumption)
  have hfsp_align : ((s0.sp - 1328#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 1328#64 (by assumption) (by decide)
  apply of_sepWP_lscro hcro0 (mid := lsmpl.base 416)
  wp_conv_pre =>
    rw [ProofLib.memRegion_split' (b := s0.readReg64 (Reg.gpr 8#5)) (n := 880) (k := chunkSize)
        (b' := s0.readReg64 (Reg.gpr 8#5) + 880#64) rfl rfl (by decide),
        stackAt_1328_split s0.sp]
    unfold chunkedHeaderSentAt
  refine SepWP.fold (cells_1_unfold (s0.sp - 1328#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_10_unfold (s0.sp - 528#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_6_unfold (s0.sp - 48#64)) (by sep_focus) ?_
  wp_pull_exists
  refine SepWP.fold (unchunkedEkSentAt_extract A
    (s0.readReg64 (Reg.gpr 0#5) + 400#64) st.uc) (by sep_focus) ?_
  wp_pull_exists
  rename_i g
  have hst_words :
      wordsAt (s0.readReg64 (Reg.gpr 0#5) + 400#64) (ekSentWordsList g st.uc.epoch) =
      (((s0.readReg64 (Reg.gpr 0#5) + 400#64) ↦₆₄ g.v1.w0) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 408#64) ↦₆₄ g.v1.w1) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 416#64) ↦₆₄ g.v1.w2) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 424#64) ↦₆₄ g.auth.v1.w0) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 432#64) ↦₆₄ g.auth.v1.w1) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 440#64) ↦₆₄ g.auth.v1.w2) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 448#64) ↦₆₄ g.auth.v2.w0) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 456#64) ↦₆₄ g.auth.v2.w1) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 464#64) ↦₆₄ g.auth.v2.w2) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 472#64) ↦₆₄ st.uc.epoch)) := by
    dsimp only [ekSentWordsList, ct2SentWordsList, authWordsList, vecWordsList, List.append]
    simp only [wordsAt_10, BitVec.add_assoc, arm64_norm]
  have hsp_words :
      wordsAt (s0.sp - 528#64) (ekSentWordsList g st.uc.epoch) =
      (((s0.sp - 528#64) ↦₆₄ g.v1.w0) ∗
       ((s0.sp - 520#64) ↦₆₄ g.v1.w1) ∗
       ((s0.sp - 512#64) ↦₆₄ g.v1.w2) ∗
       ((s0.sp - 504#64) ↦₆₄ g.auth.v1.w0) ∗
       ((s0.sp - 496#64) ↦₆₄ g.auth.v1.w1) ∗
       ((s0.sp - 488#64) ↦₆₄ g.auth.v1.w2) ∗
       ((s0.sp - 480#64) ↦₆₄ g.auth.v2.w0) ∗
       ((s0.sp - 472#64) ↦₆₄ g.auth.v2.w1) ∗
       ((s0.sp - 464#64) ↦₆₄ g.auth.v2.w2) ∗
       ((s0.sp - 456#64) ↦₆₄ st.uc.epoch)) := by
    dsimp only [ekSentWordsList, ct2SentWordsList, authWordsList, vecWordsList, List.append]
    simp only [wordsAt_10, arm64_norm]
  wp_conv_pre =>
    rw [hst_words]
    simp only [wordsAt_10, arm64_norm]
  wp_steps
  refine SepWP.fold (cell_0_rejoin_400 s0.sp 1328#64 1320#64 0#64 (by bv_omega)) (by sep_focus) ?_
  refine call_memcpy_relocate hmemcpy_ok (s0 := s0) (Relocatable.of_polyEncoderAt A st.sending_ek)
    (s0.sp - 1328#64) (s0.readReg64 (Reg.gpr 0#5))
    (ret_pc := (blkPl_336).base + 72#64) (sp_call := s0.sp - 1328#64)
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
    (fun sf1 hpc1 hrun1 hsp1 hregs1 htr1 => ?_)
  rcases hregs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hvregs_1⟩
  wp_steps
  refine call_memcpy_relocate hmemcpy_ok (s0 := s0) (Relocatable.of_polyDecoderAt A st.receiving_ct1)
    (s0.sp - 448#64) (s0.readReg64 (Reg.gpr 0#5) + 480#64)
    (ret_pc := (blkPl_336).base + 92#64) (sp_call := s0.sp - 1328#64)
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
    (fun sf2 hpc2 hrun2 hsp2 hregs2 htr2 => ?_)
  rcases hregs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hvregs_2⟩
  refine SepWP.fold (Entails.of_eq hst_words.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hsp_words.symm) (by sep_focus) ?_
  refine SepWP.fold (uc_dec_copy_recompose (k := 80) (by decide) (by decide)
    (s0.readReg64 (Reg.gpr 0#5)) (s0.sp - 528#64) (by bv_omega)
    (ekSentWordsList g st.uc.epoch) rfl) (by sep_focus) ?_
  wp_steps
  refine call_polyNextChunk_placed hnext
    (s0.readReg64 (Reg.gpr 8#5) + 880#64) (s0.sp - 1328#64)
    st.sending_ek outSt.sending_ek chunk
    (ret_pc := (blkPl_336).base + 104#64) (sp_call := s0.sp - 1328#64)
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
    (by sep_focus)
    (fun sf3 hpc3 hrun3 hsp3 hregs3 htr3 => ?_)
  rcases hregs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hvregs_3⟩
  wp_steps
  refine call_memcpy_relocate hmemcpy_ok (s0 := s0) (Relocatable.of_polyEncoderAt A outSt.sending_ek)
    (s0.sp - 928#64) (s0.sp - 1328#64)
    (ret_pc := (blkPl_336).base + 120#64) (sp_call := s0.sp - 1328#64)
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
    (fun sf4 hpc4 hrun4 hsp4 hregs4 htr4 => ?_)
  rcases hregs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hvregs_4⟩
  refine SepWP.fold (chunkedHeaderSentAt_recompose_sp A s0.sp st outSt hout_eq)
    (by sep_focus) ?_
  wp_steps
  refine call_memcpy_relocate hmemcpy_ok (s0 := s0) (Relocatable.of_chunkedHeaderSentAt A outSt)
    (s0.readReg64 (Reg.gpr 8#5)) (s0.sp - 928#64)
    (ret_pc := (blkPl_336).base + 136#64) (sp_call := s0.sp - 1328#64)
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
    (fun sf5 hpc5 hrun5 hsp5 hregs5 htr5 => ?_)
  rcases hregs5 with ⟨hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hvregs_5⟩
  wp_steps
  refine SepWP.fold (stackAt_1328_rejoin s0.sp _ _ _ _ _ _) (by sep_focus) ?_
  wp_done

/-- Closed `[LibsignalPlacement]` contract for `<HeaderSent>::send_ek_chunk` (Block `336`)
    discharging `<PolyEncoder as Encoder>::next_chunk` (Block `416`) via `poly_next_chunk_placed_ok`. -/
theorem header_sent_send_ek_chunk_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced A ext) :
    HeaderSentSendEkChunkPlacedOkX A F ext :=
  header_sent_send_ek_chunk_placed_cl_ext
    (hookSat_memcpyRegion_of_sessionMemcpy0 (hA.session_memcpy 0))
    (keys_ls_subroutine_ok_of_block_cro (i := 336) (j := 416)
      (poly_next_chunk_placed_ok A ext hA))

end CryptoVerification.SpqrV1.States.Leaves
