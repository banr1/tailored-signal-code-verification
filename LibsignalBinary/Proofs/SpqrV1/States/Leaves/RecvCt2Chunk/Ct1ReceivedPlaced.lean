/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoder
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.Common
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.CommonPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.Ct1Received
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpochPlaced
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::send_ek::Ct1Received>::recv_ct2_chunk` (Block `346`)

Relocatable `[LibsignalPlacement]` verification of `<Ct1Received>::recv_ct2_chunk` (Block `346`,
67 instructions), proving `ct1_received_recv_ct2_chunk_placed_cl_ext`
(`Ct1ReceivedRecvCt2ChunkPlacedOkX`).
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
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Alloc

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit bv_sub_sub BitVec.sub_add_cancel BitVec.toNat_zero

set_option maxHeartbeats 1200000 in
/-- Relocatable `<Ct1Received>::recv_ct2_chunk` (Block `346`, 67 insns) with an explicit
    `withLsCodeLoaded` hypothesis for `drop_glue::<[Poly; 16]>` (Block `265`). -/
theorem ct1_received_recv_ct2_chunk_placed_cl_ext_of_drop [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionSpec)
    (hadd : subroutine_ok (lsProg_346 (Rust.withPanics ext))
      (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpec A)))
    (hdrop : subroutine_ok (lsProg_346 (Rust.withPanics ext))
      (lsmpl.base 265) (withLsCodeLoaded lsmpl (dropGluePoly16Spec A))) :
    Ct1ReceivedRecvCt2ChunkPlacedOkX A F ext := by
  unfold Ct1ReceivedRecvCt2ChunkPlacedOkX
  apply subroutine_ok_withLsCodeLoaded_of_left
  have hmemcpy_ok : subroutine_ok (lsProg_346 (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionSpec :=
    spqr_hook_ok_of_mem hmemcpy
  simp only [ct1ReceivedRecvCt2ChunkSpec, lsProg_346,
    chunkedEkSentCt1ReceivedSize, chunkedCt1ReceivedSize,
    BitVec.ofNat_eq_ofNat] at hmemcpy_ok hadd hdrop ⊢
  wpp_init x s0
  rcases x with ⟨outA, stA, chunkA, st, chunk, outSt⟩
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  subst ‹s0.readReg64 (Reg.gpr 0#5) = outA›
    ‹s0.readReg64 (Reg.gpr 1#5) = stA› ‹s0.readReg64 (Reg.gpr 3#5) = chunkA›
  have hout_eq := ct1_received_recv_ct2_chunk_ok_elim (by assumption)
  have hfsp_align : ((s0.sp - 448#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 448#64 (by assumption) (by decide)
  apply of_sepWP_lscl hcl0 (mid := lsmpl.base 419)
  wp_conv_pre =>
    rw [ProofLib.memRegion_split' (b := s0.readReg64 (Reg.gpr 0#5)) (n := 104) (k := 400)
        (b' := s0.readReg64 (Reg.gpr 0#5) + 104#64) rfl rfl (by decide),
        stackAt_448_split s0.sp]
    unfold chunkedCt1ReceivedAt
  refine SepWP.fold (cells_16_unfold (s0.sp - 448#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_16_unfold (s0.sp - 320#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_16_unfold (s0.sp - 192#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_1_unfold (s0.sp - 64#64)) (by sep_focus) ?_
  refine SepWP.fold (byte_1_unfold (s0.sp - 56#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_6_unfold (s0.sp - 48#64)) (by sep_focus) ?_
  wp_pull_exists
  refine SepWP.fold (unchunkedEkSentCt1ReceivedAt_extract A
    (s0.readReg64 (Reg.gpr 1#5) + 400#64) st.uc) (by sep_focus) ?_
  wp_pull_exists; rename_i g
  have hst_words :
      wordsAt (s0.readReg64 (Reg.gpr 1#5) + 400#64) (ekSentCt1ReceivedWordsList g st.uc.epoch) =
      (((s0.readReg64 (Reg.gpr 1#5) + 400#64) ↦₆₄ g.v1.w0) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 408#64) ↦₆₄ g.v1.w1) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 416#64) ↦₆₄ g.v1.w2) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 424#64) ↦₆₄ g.rest.v1.w0) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 432#64) ↦₆₄ g.rest.v1.w1) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 440#64) ↦₆₄ g.rest.v1.w2) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 448#64) ↦₆₄ g.rest.auth.v1.w0) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 456#64) ↦₆₄ g.rest.auth.v1.w1) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 464#64) ↦₆₄ g.rest.auth.v1.w2) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 472#64) ↦₆₄ g.rest.auth.v2.w0) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 480#64) ↦₆₄ g.rest.auth.v2.w1) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 488#64) ↦₆₄ g.rest.auth.v2.w2) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 496#64) ↦₆₄ st.uc.epoch)) := by
    dsimp only [ekSentCt1ReceivedWordsList, ekSentWordsList,
      ct2SentWordsList, authWordsList, vecWordsList, List.append]
    simp only [wordsAt_13', BitVec.add_assoc, arm64_norm]
  have hout_words :
      wordsAt (s0.readReg64 (Reg.gpr 0#5)) (ekSentCt1ReceivedWordsList g st.uc.epoch) =
      (((s0.readReg64 (Reg.gpr 0#5)) ↦₆₄ g.v1.w0) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ g.v1.w1) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ g.v1.w2) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 24#64) ↦₆₄ g.rest.v1.w0) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 32#64) ↦₆₄ g.rest.v1.w1) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 40#64) ↦₆₄ g.rest.v1.w2) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 48#64) ↦₆₄ g.rest.auth.v1.w0) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 56#64) ↦₆₄ g.rest.auth.v1.w1) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 64#64) ↦₆₄ g.rest.auth.v1.w2) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 72#64) ↦₆₄ g.rest.auth.v2.w0) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 80#64) ↦₆₄ g.rest.auth.v2.w1) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 88#64) ↦₆₄ g.rest.auth.v2.w2) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 96#64) ↦₆₄ st.uc.epoch)) := by
    dsimp only [ekSentCt1ReceivedWordsList, ekSentWordsList,
      ct2SentWordsList, authWordsList, vecWordsList, List.append]
    simp only [wordsAt_13', arm64_norm]
  wp_conv_pre => rw [hst_words]; simp only [wordsAt_16, arm64_norm]
  wp_steps
  have hdec0_1 :
      (((s0.sp - 448#64) ↦₆₄ 0#64) ∗ ((s0.sp - 440#64) ↦₆₄ 2#64) ∗
       ((s0.sp - 432#64) ↦₆₄ 0#64) ∗ ((s0.sp - 424#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 416#64) ↦₆₄ 2#64) ∗ ((s0.sp - 408#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 400#64) ↦₆₄ 0#64) ∗ ((s0.sp - 392#64) ↦₆₄ 2#64) ∗
       ((s0.sp - 384#64) ↦₆₄ 0#64) ∗ ((s0.sp - 376#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 368#64) ↦₆₄ 2#64) ∗ ((s0.sp - 360#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 352#64) ↦₆₄ 0#64) ∗ ((s0.sp - 344#64) ↦₆₄ 2#64) ∗
       ((s0.sp - 336#64) ↦₆₄ 0#64) ∗ ((s0.sp - 328#64) ↦₆₄ 0#64)) =
      wordsAt (s0.sp - 448#64)
        [0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64,
         0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64] := by simp only [wordsAt_16, arm64_norm]
  have hdec0_2 :
      (((s0.sp - 320#64) ↦₆₄ 2#64) ∗ ((s0.sp - 312#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 304#64) ↦₆₄ 0#64) ∗ ((s0.sp - 296#64) ↦₆₄ 2#64) ∗
       ((s0.sp - 288#64) ↦₆₄ 0#64) ∗ ((s0.sp - 280#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 272#64) ↦₆₄ 2#64) ∗ ((s0.sp - 264#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 256#64) ↦₆₄ 0#64) ∗ ((s0.sp - 248#64) ↦₆₄ 2#64) ∗
       ((s0.sp - 240#64) ↦₆₄ 0#64) ∗ ((s0.sp - 232#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 224#64) ↦₆₄ 2#64) ∗ ((s0.sp - 216#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 208#64) ↦₆₄ 0#64) ∗ ((s0.sp - 200#64) ↦₆₄ 2#64)) =
      wordsAt ((s0.sp - 448#64) + 128#64)
        [2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64,
         0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64] := by simp only [wordsAt_16, arm64_norm]
  have hdec0_3 :
      (((s0.sp - 192#64) ↦₆₄ 0#64) ∗ ((s0.sp - 184#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 176#64) ↦₆₄ 2#64) ∗ ((s0.sp - 168#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 160#64) ↦₆₄ 0#64) ∗ ((s0.sp - 152#64) ↦₆₄ 2#64) ∗
       ((s0.sp - 144#64) ↦₆₄ 0#64) ∗ ((s0.sp - 136#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 128#64) ↦₆₄ 2#64) ∗ ((s0.sp - 120#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 112#64) ↦₆₄ 0#64) ∗ ((s0.sp - 104#64) ↦₆₄ 2#64) ∗
       ((s0.sp - 96#64) ↦₆₄ 0#64) ∗ ((s0.sp - 88#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 80#64) ↦₆₄ 2#64) ∗ ((s0.sp - 72#64) ↦₆₄ 0#64)) =
      wordsAt ((s0.sp - 448#64) + 256#64)
        [0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64,
         2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64] := by simp only [wordsAt_16, arm64_norm]
  refine SepWP.fold (Entails.of_eq hdec0_1) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hdec0_2) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hdec0_3) (by sep_focus) ?_
  have hdec_recomp :
      wordsAt (s0.sp - 448#64)
        [0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64,
         0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64] ∗
      wordsAt ((s0.sp - 448#64) + 128#64)
        [2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64,
         0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64] ∗
      wordsAt ((s0.sp - 448#64) + 256#64)
        [0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64,
         2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64] ∗
      ((s0.sp - 64#64) ↦₆₄ 80#64) ∗ ((s0.sp - 56#64) ↦₈ 0#8) ∗ memRegion (s0.sp - 55#64) 7 ⊢
      polyDecoderAt A (s0.sp - 448#64) (emptyPolyDecoder 80) := by
    simpa only [arm64_norm] using emptyPolyDecoder_recompose A (s0.sp - 448#64) 80 (by decide)
  refine SepWP.fold hdec_recomp (by sep_focus) ?_
  refine call_addChunk_cl hadd
    (s0.sp - 448#64) (s0.readReg64 (Reg.gpr 3#5)) (emptyPolyDecoder 80) chunk
    (emptyPolyDecoder_strictSorted 80) (ret_pc := (blkPl_346).base + 168#64) (sp_call := s0.sp - 448#64)
    (by simp only [arm64_norm]) (by simpa only [arm64_norm] using ‹s0.status = .Running›)
    (by simp only [State.sp, arm64_norm]) hfsp_align (by simp only [Reg.lr, arm64_norm])
    (by simp only [arm64_norm]) (by simp only [Reg.x0, arm64_norm])
    (by simp only [Reg.x1, arm64_norm]) (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 htr1 _ hcl1 => ?_)
  apply SepWPp.of_sepWP_ret
  apply sepWP_seq_lscl hcl1 (mid := lsmpl.base 265)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [arm64_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
  refine SepWP.fold (cells_13_unfold' (s0.readReg64 (Reg.gpr 0#5))) (by sep_focus) ?_
  wp_pull_exists
  wp_conv_pre => simp only [wordsAt_13', arm64_norm]
  wp_steps
  refine SepWP.fold (Entails.of_eq hst_words.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hout_words.symm) (by sep_focus) ?_
  refine SepWP.fold (uc_104_copy_recompose
    (s0.readReg64 (Reg.gpr 0#5)) (s0.readReg64 (Reg.gpr 1#5)) st.uc g) (by sep_focus) ?_
  refine call_memcpy_relocate hmemcpy_ok (s0 := s0)
    (Relocatable.of_polyDecoderAt A (addChunkTotal (emptyPolyDecoder 80) chunk))
    (s0.readReg64 (Reg.gpr 0#5) + 104#64) (s0.sp - 448#64)
    (ret_pc := (blkPl_346).base + 216#64) (sp_call := s0.sp - 448#64)
    (v19 := s0.readReg64 (Reg.gpr 1#5)) (v20 := s0.readReg64 (Reg.gpr 0#5))
    (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun1)
    (by simp only [State.sp, arm64_norm, hsp1]) hfsp_align (by simp only [Reg.lr, arm64_norm])
    (by simp only [arm64_norm, htr1])
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hvregs_1])
    (by simp only [Reg.x0, arm64_norm, hx20_1]) (by simp only [Reg.x1, arm64_norm, hsp1])
    (by simp only [Reg.x2, arm64_norm]) (by sep_focus)
    (fun sf2 hpc2 hrun2 hsp2 hregs2 htr2 => ?_)
  rcases hregs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hvregs_2⟩
  refine SepWP.fold (chunkedEkSentCt1ReceivedAt_recompose A
    (s0.readReg64 (Reg.gpr 0#5)) st.uc (addChunkTotal (emptyPolyDecoder 80) chunk) outSt hout_eq)
    (by sep_focus) ?_
  refine SepWP.fold (polyEncoderAt_entails_tag_vecs_tail A
    (s0.readReg64 (Reg.gpr 1#5)) st.sending_ek) (by sep_focus) ?_
  wp_pull_exists; rename_i tag vecs
  wp_focus_pure; intro hvecs_len
  wp_steps
  refine SepWP.fold (stackAt_448_to_dropPoly16 s0.sp _ _ _ _ _ _) (by sep_focus) ?_
  refine call_dropGluePoly16_cl hdrop (s0.readReg64 (Reg.gpr 1#5) + 8#64) vecs
    (ret_pc := s0.readReg64 Reg.lr) (sp_call := s0.sp)
    (by simp only [arm64_norm])
    (by simpa only [arm64_norm] using hrun2)
    (by simp only [State.sp, arm64_norm, hsp2])
    (by simpa only [State.spAligned] using ‹s0.spAligned = true›)
    (by simp only [Reg.lr, arm64_norm])
    (by simp only [arm64_norm, htr2])
    (by simp only [Reg.x0, arm64_norm, hx19_2])
    hvecs_len
    (by sep_focus)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf htrace_sf => ?_)
  refine SepWP.fold (chunked_400_join (s0.readReg64 (Reg.gpr 1#5)) tag 104 504 rfl (by decide))
    (by sep_focus) ?_
  refine SepWP.fold (stackAt_448_from_dropPoly16 s0.sp) (by sep_focus) ?_
  wp_done

/-- Relocatable `<Ct1Received>::recv_ct2_chunk` (Block `346`, 67 insns) discharging
    `drop_glue::<[Poly; 16]>` (Block `265`) directly from `hdealloc`. -/
theorem ct1_received_recv_ct2_chunk_placed_cl_ext [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionSpec)
    (hadd : subroutine_ok (lsProg_346 (Rust.withPanics ext))
      (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpec A))) :
    Ct1ReceivedRecvCt2ChunkPlacedOkX A F ext :=
  ct1_received_recv_ct2_chunk_placed_cl_ext_of_drop hmemcpy hadd
    (ls_subroutine_ok_of_block (i := 346) (j := 265)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (drop_glue_poly16_placed_ok (spqr_hook_ok_of_mem hdealloc))))

end CryptoVerification.SpqrV1.States.Leaves
