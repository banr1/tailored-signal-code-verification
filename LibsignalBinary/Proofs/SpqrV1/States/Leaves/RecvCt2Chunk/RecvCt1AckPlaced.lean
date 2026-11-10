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
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.RecvCt1Ack
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpochPlaced
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::send_ct::EkReceivedCt1Sampled>::recv_ct1_ack` (Block `343`)

Relocatable `[LibsignalPlacement]` verification of `<EkReceivedCt1Sampled>::recv_ct1_ack`
(Block `343`, 53 instructions), proving `ek_received_ct1_sampled_recv_ct1_ack_placed_cl_ext`
(`EkReceivedCt1SampledRecvCt1AckPlacedOkX`).
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
open CryptoVerification.SpqrV1.Unchunked (unchunkedSendCt2PlacedRoAt unchunkedCt1SentEkReceivedSendCt2PlacedSpec)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit bv_sub_sub BitVec.sub_add_cancel BitVec.toNat_zero

set_option maxHeartbeats 800000 in
/-- Relocatable `<EkReceivedCt1Sampled>::recv_ct1_ack` (Block `343`, 53 insns) with an explicit
    `withLsCodeLoaded` hypothesis for `drop_glue::<[Poly; 16]>` (Block `265`). -/
theorem ek_received_ct1_sampled_recv_ct1_ack_placed_cl_ext_of_drop [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (hsend : subroutine_ok (lsProg_343 (Rust.withPanics ext))
      (lsmpl.base 347)
      (withLsCodeLoaded lsmpl (unchunkedCt1SentEkReceivedSendCt2PlacedSpec A F K)))
    (henc : subroutine_ok (lsProg_343 (Rust.withPanics ext))
      (lsmpl.base 382)
      (withLsCodeLoaded lsmpl (sendCt2EncoderSpec A)))
    (hdrop : subroutine_ok (lsProg_343 (Rust.withPanics ext))
      (lsmpl.base 265)
      (withLsCodeLoaded lsmpl (dropGluePoly16Spec A))) :
    EkReceivedCt1SampledRecvCt1AckPlacedOkX A F K ext := by
  unfold EkReceivedCt1SampledRecvCt1AckPlacedOkX
  apply subroutine_ok_withLsCodeLoaded_of_left
  have hdealloc_raw : subroutine_ok (lsProg_343 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A) :=
    spqr_hook_ok_of_mem hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  simp only [ekReceivedCt1SampledRecvCt1AckPlacedSpec, lsProg_343,
    chunkedCt2SampledSize, chunkedEkReceivedCt1SampledSize,
    BitVec.ofNat_eq_ofNat] at hdealloc_raw hsend henc hdrop ⊢
  wpp_init x s0
  rcases x with ⟨outA, stA, st, outSt⟩
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  subst ‹s0.readReg64 (Reg.gpr 0#5) = outA› ‹s0.readReg64 (Reg.gpr 1#5) = stA›
  obtain ⟨ct2, mac, hsc_ok, henc_ok⟩ := recv_ct1_ack_ok_elim (by assumption)
  have hfsp_align : ((s0.sp - 176#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 176#64 (by assumption) (by decide)
  apply of_sepWP_lscl hcl0 (mid := lsmpl.base 347)
  wp_conv_pre =>
    rw [ProofLib.memRegion_split' (b := s0.readReg64 (Reg.gpr 0#5)) (n := 400) (k := 56)
        (b' := s0.readReg64 (Reg.gpr 0#5) + 400#64) rfl rfl (by decide),
        stackAt_176_split s0.sp]
    unfold chunkedEkReceivedCt1SampledAt
    rw [unchunkedCt1SentEkReceivedAt_400_eq A (s0.readReg64 (Reg.gpr 1#5)) st.uc]
  refine SepWP.fold (cells_1_unfold (s0.sp - 176#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_8_unfold (s0.sp - 64#64)) (by sep_focus) ?_
  wp_pull_exists
  wp_conv_pre => simp only [arm64_norm]
  wp_steps
  refine SepWP.fold (Entails.of_eq (unchunkedCt1SentEkReceivedAt_400_eq A
    (s0.readReg64 (Reg.gpr 1#5)) st.uc).symm) (by sep_focus) ?_
  refine call_sendCt2_cl hsend
    (s0.sp - 168#64) (s0.readReg64 (Reg.gpr 1#5) + 400#64) st.uc outSt.uc ct2 mac hsc_ok
    (ret_pc := (blkPl_343).base + 60#64) (next_pc := lsmpl.base 382) (sp_call := s0.sp - 176#64)
    (by simp only [arm64_norm]) (by simpa only [arm64_norm] using ‹s0.status = .Running›)
    (by simp only [State.sp, arm64_norm]) hfsp_align (by simp only [Reg.lr, arm64_norm])
    (by simp only [arm64_norm]) (by simp only [Reg.x0, arm64_norm])
    (by simp only [Reg.x1, arm64_norm]) (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 htr1 => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [arm64_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
  have h56_eq : (s0.sp - 168#64) + 56#64 = s0.sp - 112#64 := by bv_omega
  have h80_eq : (s0.sp - 168#64) + 80#64 = s0.sp - 88#64 := by bv_omega
  wp_conv_pre => rw [h56_eq, h80_eq]
  refine SepWP.fold (stackAt_176_to_sendCt2Encoder s0.sp) (by sep_focus) ?_
  refine SepWP.fold (unchunkedCt2SentAt_extract A (s0.sp - 168#64) outSt.uc) (by sep_focus) ?_
  wp_pull_exists; rename_i g_uc
  refine SepWP.fold (vecU8_entails_slice_and_tail A (s0.sp - 112#64) ct2) (by sep_focus) ?_
  wp_pull_exists; rename_i ct2Cap ct2Ptr
  wp_focus_pure; rintro ⟨hct2_le, hct2_lt, hct2_ne⟩
  refine SepWP.fold (vecU8_entails_slice_and_tail A (s0.sp - 88#64) mac) (by sep_focus) ?_
  wp_pull_exists; rename_i macCap macPtr
  wp_focus_pure; rintro ⟨hmac_le, hmac_lt, hmac_ne⟩
  refine SepWP.fold (cells_7_unfold (s0.readReg64 (Reg.gpr 0#5) + 400#64)) (by sep_focus) ?_
  wp_pull_exists
  have hsp_uc_words :
      wordsAt (s0.sp - 168#64) (ct2SentWordsList g_uc outSt.uc.epoch) =
      (((s0.sp - 168#64) ↦₆₄ g_uc.v1.w0) ∗ ((s0.sp - 160#64) ↦₆₄ g_uc.v1.w1) ∗
       ((s0.sp - 152#64) ↦₆₄ g_uc.v1.w2) ∗ ((s0.sp - 144#64) ↦₆₄ g_uc.v2.w0) ∗
       ((s0.sp - 136#64) ↦₆₄ g_uc.v2.w1) ∗ ((s0.sp - 128#64) ↦₆₄ g_uc.v2.w2) ∗
       ((s0.sp - 120#64) ↦₆₄ outSt.uc.epoch)) := by
    dsimp only [ct2SentWordsList, authWordsList, List.append]
    simp only [wordsAt_7, arm64_norm]
  have hout_uc_words :
      wordsAt (s0.readReg64 (Reg.gpr 0#5) + 400#64) (ct2SentWordsList g_uc outSt.uc.epoch) =
      (((s0.readReg64 (Reg.gpr 0#5) + 400#64) ↦₆₄ g_uc.v1.w0) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 408#64) ↦₆₄ g_uc.v1.w1) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 416#64) ↦₆₄ g_uc.v1.w2) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 424#64) ↦₆₄ g_uc.v2.w0) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 432#64) ↦₆₄ g_uc.v2.w1) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 440#64) ↦₆₄ g_uc.v2.w2) ∗
       ((s0.readReg64 (Reg.gpr 0#5) + 448#64) ↦₆₄ outSt.uc.epoch)) := by
    dsimp only [ct2SentWordsList, authWordsList, List.append]
    simp only [wordsAt_7, BitVec.add_assoc, arm64_norm]
  wp_conv_pre => rw [hsp_uc_words]; simp only [wordsAt_7, BitVec.add_assoc, arm64_norm]
  wp_steps
  refine SepWP.fold (Entails.of_eq hsp_uc_words.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hout_uc_words.symm) (by sep_focus) ?_
  refine SepWP.fold (uc_56_and_headers_recompose
    (s0.readReg64 (Reg.gpr 0#5)) s0.sp outSt.uc g_uc _ _ _ _ _ _ _) (by sep_focus) ?_
  refine call_sendCt2Encoder_cl henc
    (s0.readReg64 (Reg.gpr 0#5)) ct2Ptr macPtr ct2 mac outSt.sending_ct2
    hct2_ne hmac_ne henc_ok (ret_pc := (blkPl_343).base + 116#64) (sp_call := s0.sp - 176#64)
    (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun1)
    (by simp only [State.sp, arm64_norm, hsp1]) hfsp_align (by simp only [Reg.lr, arm64_norm])
    (by simp only [arm64_norm, htr1]) (by simp only [Reg.x0, arm64_norm, hx22_1])
    (by simp only [Reg.x1, arm64_norm]) (by simp only [Reg.x2, arm64_norm])
    (by simp only [Reg.x3, arm64_norm]) (by simp only [Reg.x4, arm64_norm]) (by sep_focus)
    (fun sf2 hpc2 hrun2 hsp2 hcs2 htr2 hcl2 => ?_)
  apply SepWPp.of_sepWP_ret
  apply sepWP_seq_lscl hcl2 (mid := lsmpl.base 265)
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
  simp only [arm64_norm, hx19_1, hx22_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
  refine SepWP.fold (slice_and_tail_entails_vecCapPtrDealloc A ct2Cap ct2Ptr ct2 hct2_le hct2_lt)
    (by sep_focus) ?_
  refine SepWP.fold (slice_and_tail_entails_vecCapPtrDealloc A macCap macPtr mac hmac_le hmac_lt)
    (by sep_focus) ?_
  refine SepWP.fold (stackAt_176_to_allocHook s0.sp) (by sep_focus) ?_
  have hout_join :
      polyEncoderAt A (s0.readReg64 (Reg.gpr 0#5)) outSt.sending_ct2 ∗
        unchunkedCt2SentAt A (s0.readReg64 (Reg.gpr 0#5) + 400#64) outSt.uc ⊢
      chunkedCt2SampledAt A (s0.readReg64 (Reg.gpr 0#5)) outSt := Entails.refl _
  refine SepWP.fold hout_join (by sep_focus) ?_
  refine Drop.seq_clean (mid := (blkPl_343).base + 136#64)
    (P_mid := (chunkedCt2SampledAt A (s0.readReg64 (Reg.gpr 0#5)) outSt ∗
      polyEncoderAt A (s0.readReg64 (Reg.gpr 1#5)) st.sending_ct1 ∗
      memRegion (s0.readReg64 (Reg.gpr 1#5) + 400#64) 128 ∗
      vecCapPtrDealloc A ct2Cap ct2Ptr ∗
      unchunkedSendCt2PlacedRoAt ∗
      memRegion (s0.sp - 17632#64) 13360 ∗ memRegion (s0.sp - 176#64) 112 ∗
      (((s0.sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ∗
      A.pool ∗ stackAt (s0.sp - 176#64) allocHookStack)
    (Q := fun sm => RecvCt1AckSaved s0 sm (s0.sp - 176#64) (s0.readReg64 (Reg.gpr 1#5)) ct2Cap ct2Ptr)
    ?_ ?_
  · dsimp only [vecCapPtrDealloc]
    by_cases hmac : (macCap == 0#64) = true <;>
      simp only [hmac, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps
      refine Drop.align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x24, Reg.x23, Reg.x22, Reg.x21, Reg.x20, Reg.x19]; ac_rfl) ?_
      refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun2) ?_
      exact ⟨Entails.refl _, by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp2, htr2, hvregs_2]⟩
    · wp_steps; wp_apply
      refine Drop.align_pre (by rw [hsp2]; dsimp only [Reg.fp, Reg.lr, Reg.x24, Reg.x23, Reg.x22, Reg.x21, Reg.x20, Reg.x19]; ac_rfl) ?_
      wp_done
  · intro s3 hpc3 hrun3 ⟨hx19_3, hx20_3, hx21_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp3, htr3, hvregs_3⟩
    refine Drop.seq_clean (mid := (blkPl_343).base + 156#64)
      (P_mid := (chunkedCt2SampledAt A (s0.readReg64 (Reg.gpr 0#5)) outSt ∗
        polyEncoderAt A (s0.readReg64 (Reg.gpr 1#5)) st.sending_ct1 ∗
        memRegion (s0.readReg64 (Reg.gpr 1#5) + 400#64) 128 ∗
        unchunkedSendCt2PlacedRoAt ∗
        memRegion (s0.sp - 17632#64) 13360 ∗ memRegion (s0.sp - 176#64) 112 ∗
        (((s0.sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ∗
        A.pool ∗ stackAt (s0.sp - 176#64) allocHookStack)
      (Q := fun sm => RecvCt1AckSaved s0 sm (s0.sp - 176#64) (s0.readReg64 (Reg.gpr 1#5)) ct2Cap ct2Ptr)
      ?_ ?_
    · dsimp only [vecCapPtrDealloc]
      by_cases hct2 : (ct2Cap == 0#64) = true <;>
        simp only [hct2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps
        refine Drop.align_pre (by ac_rfl) ?_
        refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun3) ?_
        exact ⟨Entails.refl _, by
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            simp only [arm64_norm, hx19_3, hx20_3, hx21_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp3, htr3, hvregs_3]⟩
      · wp_steps; wp_apply
        refine Drop.align_pre (by rw [hsp3]; ac_rfl) ?_
        wp_done
    · intro s4 hpc4 hrun4 ⟨hx19_4, hx20_4, hx21_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp4, htr4, hvregs_4⟩
      refine SepWP.fold (polyEncoderAt_entails_tag_vecs_tail A
        (s0.readReg64 (Reg.gpr 1#5)) st.sending_ct1) (by sep_focus) ?_
      wp_pull_exists; rename_i tag vecs
      wp_focus_pure; intro hvecs_len
      wp_steps
      refine SepWP.fold (stackAt_176_to_dropPoly16 s0.sp _ _ _ _ _ _ _ _) (by sep_focus) ?_
      refine call_dropGluePoly16_cl hdrop (s0.readReg64 (Reg.gpr 1#5) + 8#64) vecs
        (ret_pc := s0.readReg64 Reg.lr) (sp_call := s0.sp)
        (by simp only [arm64_norm])
        (by simpa only [arm64_norm] using hrun4)
        (by simp only [State.sp, arm64_norm, hsp4])
        (by simpa only [State.spAligned] using ‹s0.spAligned = true›)
        (by simp only [Reg.lr, arm64_norm])
        (by simp only [arm64_norm, htr4])
        (by simp only [Reg.x0, arm64_norm, hx19_4])
        hvecs_len
        (by sep_focus)
        (fun sf hpc_sf hrun_sf hsp_sf hcs_sf htrace_sf => ?_)
      refine SepWP.fold (chunked_400_join (s0.readReg64 (Reg.gpr 1#5)) tag 128 528 rfl (by decide))
        (by sep_focus) ?_
      refine SepWP.fold (stackAt_176_from_dropPoly16 s0.sp) (by sep_focus) ?_
      wp_done

/-- Relocatable `<EkReceivedCt1Sampled>::recv_ct1_ack` (Block `343`, 53 insns) discharging
    `drop_glue::<[Poly; 16]>` (Block `265`) directly from `hdealloc`. -/
theorem ek_received_ct1_sampled_recv_ct1_ack_placed_cl_ext [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (hsend : subroutine_ok (lsProg_343 (Rust.withPanics ext))
      (lsmpl.base 347)
      (withLsCodeLoaded lsmpl (unchunkedCt1SentEkReceivedSendCt2PlacedSpec A F K)))
    (henc : subroutine_ok (lsProg_343 (Rust.withPanics ext))
      (lsmpl.base 382)
      (withLsCodeLoaded lsmpl (sendCt2EncoderSpec A))) :
    EkReceivedCt1SampledRecvCt1AckPlacedOkX A F K ext :=
  ek_received_ct1_sampled_recv_ct1_ack_placed_cl_ext_of_drop hdealloc hsend henc
    (ls_subroutine_ok_of_block (i := 343) (j := 265)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (drop_glue_poly16_placed_ok (spqr_hook_ok_of_mem hdealloc))))

end CryptoVerification.SpqrV1.States.Leaves
