/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.States1aPlaced
public import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.PolyDecoderPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.PolyEncoderPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.UnchunkedPlaced
import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Relocatable Chunked `States` Drop Glue (Block `443`, Part 2/2 and Top-Level)

Proves the remaining five variant contracts (`ct2Sampled`, `headerSent`, `ct1Received`,
`keysSampled`, `ekReceivedCt1Sampled`), the combined 11-variant `Block 443` contracts, and the
`LibsignalRoLoaded`-discharged jump-table-free contracts on `lsProg_443 H` under
`[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Drop

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.CodeLayout
open CryptoVerification.Cli.SpqrV1.Drop.TopPlaced

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Per-Variant `[LibsignalPlacement]` Proofs (Part 2/2: 5 Variants) -/

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_ct2Sampled_placed_ok
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {H : String → Option (State → State)}
    (hdealloc : subroutine_ok (lsProg_443 H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (henc : subroutine_ok (CryptoVerification.Cli.SpqrV1.Drop.Placed.lsProg_441 H)
      (CryptoVerification.Cli.SpqrV1.Drop.Placed.blkPl_441).base (dropGluePolyEncoderSpec A))
    (st : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 H) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedVariantSpec A (.ct2Sampled st))) := by
  have henc_cl : subroutine_ok (lsProg_443 H) (lsmpl.base 441)
      (withLsCl lsmpl (dropGluePolyEncoderSpec A)) :=
    ls_subroutine_ok_cl_of_plain (callerProg := lsProg_443 H) henc
  simp only [withLsCodeLoaded, CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedVariantSpec]
  have hdealloc_raw := hdealloc; simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [withLsCl, dropGluePolyEncoderSpec, chunkedStatesAt, chunkedCt2SampledAt,
    CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedAt,
    chunkedStatesLocal1JumpTableBytes, chunkedStatesSize, polyEncoderSize, dropGluePoly16Stack,
    spqrPolyApi] at hdealloc_raw henc_cl ⊢
  wp_init a s0
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  refine SepWP.focus_weaken (unchunkedCt2Sent408_entails_dealloc A a st.uc) (by sep_focus) ?_
  wp_pull_exists; rename_i g
  dsimp only [twoVec408HeadersAt, vecCapPtrDealloc]
  nth_rw 1 [stackAt_dropStackPoly64_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x20 v_x19
  have hsplit32 := stackAt_dropStack32_split_sub32 s0.sp
  refine SepWP.focus_weaken (Entails.of_eq hsplit32) (by sep_focus) ?_
  refine CryptoVerification.Cli.SpqrV1.Drop.seq_clean_lscl ‹_› (mid := (blkPl_443).base + 580#64)
    (P_mid := ((a ↦₆₄ 12#64) ∗
      polyEncoderAt A (a + 8#64) st.sending_ct2 ∗
      ((a + 408#64) ↦₆₄ g.v1.cap) ∗ ((a + 416#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 424#64) 8 ∗
      ((a + 432#64) ↦₆₄ g.v2.cap) ∗ ((a + 440#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 448#64) 16 ∗
      (if (g.v2.cap == 0#64) = true then emp
       else A.live g.v2.ptr g.v2.cap.toNat 1 ∗ memRegion g.v2.ptr g.v2.cap.toNat) ∗
      memRegion (a + 464#64) 464) ∗
      CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded ∗
      A.pool ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
    (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · wp_steps
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
    · wp_steps; wp_apply
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 hcl1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine CryptoVerification.Cli.SpqrV1.Drop.seq_clean_lscl hcl1 (mid := (blkPl_443).base + 696#64)
      (P_mid := ((a ↦₆₄ 12#64) ∗
        polyEncoderAt A (a + 8#64) st.sending_ct2 ∗
        memRegion (a + 408#64) 56 ∗
        memRegion (a + 464#64) 464) ∗
        CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded ∗
        A.pool ∗ stackAt (s0.sp - 32#64) dropStack32 ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
      (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
      ?_ ?_
    · have hhdr56 := twoVec408HeadersAt_entails_memRegion_56 a g
      dsimp only [twoVec408HeadersAt] at hhdr56
      by_cases hc2 : (g.v2.cap == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
      · wp_steps
        refine SepWP.focus_weaken hhdr56 (by sep_focus) ?_
        refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
        refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
      · wp_steps; wp_apply
        refine SepWP.focus_weaken hhdr56 (by sep_focus) ?_
        have hsp_eq : stackAt s1.sp allocHookStack = stackAt (s0.sp - 32#64) allocHookStack := by rw [hsp_1]
        refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
        refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
        refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
    · intro s2 hpc2 hrun2 _hcl2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      dsimp only [CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]
      wp_steps_lscl (lsmpl.base 441)
      refine SepWP.focus_weaken
        (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x19) v_x19)
        (by sep_focus) ?_
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
      wp_call henc_cl ⟨a + 8#64, st.sending_ct2⟩
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp).symm) (by sep_focus) ?_
      have hjoin456 : memRegion (a + 8#64) 400 ∗ memRegion (a + 408#64) 56 ⊢
          memRegion (a + 8#64) 456 := by
        have h408 : (a + 8#64) + 400#64 = a + 408#64 := BitVec.add_assoc a 8#64 400#64
        rw [← h408, show (456 : Nat) = 400 + 56 from rfl,
            ProofLib.memRegion_split (a + 8#64) 400 56 (by decide)]
        exact Entails.refl _
      refine SepWP.focus_weaken hjoin456 (by sep_focus) ?_
      have hjoin928 := tag_and_two_regions_entails_928 a 12#64 456 464 464#64
        (BitVec.add_assoc a 8#64 456#64).symm rfl
      refine SepWP.focus_weaken hjoin928 (by sep_focus) ?_
      wp_done

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_headerSent_placed_ok
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {H : String → Option (State → State)}
    (hdealloc : subroutine_ok (lsProg_443 H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (henc : subroutine_ok (CryptoVerification.Cli.SpqrV1.Drop.Placed.lsProg_441 H)
      (CryptoVerification.Cli.SpqrV1.Drop.Placed.blkPl_441).base (dropGluePolyEncoderSpec A))
    (hdec : subroutine_ok (CryptoVerification.Cli.SpqrV1.Drop.Placed.lsProg_440 H)
      (CryptoVerification.Cli.SpqrV1.Drop.Placed.blkPl_440).base (dropGlueSortedSetPt16Spec A))
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 H) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedVariantSpec A (.headerSent st))) := by
  have henc_cl : subroutine_ok (lsProg_443 H) (lsmpl.base 441)
      (withLsCl lsmpl (dropGluePolyEncoderSpec A)) :=
    ls_subroutine_ok_cl_of_plain (callerProg := lsProg_443 H) henc
  have hdec_cl : subroutine_ok (lsProg_443 H) (lsmpl.base 440)
      (withLsCl lsmpl (dropGlueSortedSetPt16Spec A)) :=
    ls_subroutine_ok_cl_of_plain (callerProg := lsProg_443 H) hdec
  simp only [withLsCodeLoaded, CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedVariantSpec]
  have hdealloc_raw := hdealloc; simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [withLsCl, dropGluePolyEncoderSpec, dropGlueSortedSetPt16Spec, chunkedStatesAt,
    chunkedHeaderSentAt, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedAt,
    chunkedStatesLocal1JumpTableBytes, chunkedStatesSize, polyEncoderSize, polyArrayBytes,
    dropGluePoly16Stack, spqrPolyApi] at hdealloc_raw henc_cl hdec_cl ⊢
  wp_init a s0
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  refine SepWP.focus_weaken (unchunkedEkSent408_entails_dealloc A a st.uc) (by sep_focus) ?_
  wp_pull_exists; rename_i g
  have hdec488 : polyDecoderAt A (a + 488#64) st.receiving_ct1 ⊢
      ∃∗ vecs : List (List Pt),
        ⌜vecs.length = NUM_POLYS⌝ ∗
        vecPtListOf A (a + 488#64) vecs ∗
        memRegion (a + 872#64) 16 := by
    refine Entails.trans (polyDecoderAt_entails_vecs_tail A (a + 488#64) st.receiving_ct1) ?_
    apply Entails.sepExists_elim; intro vecs
    refine Entails.sepExists_right vecs ?_
    rw [BitVec.add_assoc a 488#64 384#64]
    exact Entails.refl _
  refine SepWP.focus_weaken hdec488 (by sep_focus) ?_
  wp_pull_exists; rename_i vecs; wp_focus_pure; intro hvecs_len
  dsimp only [threeVec408HeadersAt, vecCapPtrDealloc]
  nth_rw 1 [stackAt_dropStackPoly64_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x20 v_x19
  have hsplit32 := stackAt_dropStack32_split_sub32 s0.sp
  refine SepWP.focus_weaken (Entails.of_eq hsplit32) (by sep_focus) ?_
  refine CryptoVerification.Cli.SpqrV1.Drop.seq_clean_lscl ‹_› (mid := (blkPl_443).base + 332#64)
    (P_mid := ((a ↦₆₄ 4#64) ∗
      polyEncoderAt A (a + 8#64) st.sending_ek ∗
      ((a + 408#64) ↦₆₄ g.v1.cap) ∗ ((a + 416#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 424#64) 8 ∗
      ((a + 432#64) ↦₆₄ g.v2.cap) ∗ ((a + 440#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 448#64) 8 ∗
      ((a + 456#64) ↦₆₄ g.v3.cap) ∗ ((a + 464#64) ↦₆₄ g.v3.ptr) ∗ memRegion (a + 472#64) 16 ∗
      (if (g.v2.cap == 0#64) = true then emp
       else A.live g.v2.ptr g.v2.cap.toNat 1 ∗ memRegion g.v2.ptr g.v2.cap.toNat) ∗
      (if (g.v3.cap == 0#64) = true then emp
       else A.live g.v3.ptr g.v3.cap.toNat 1 ∗ memRegion g.v3.ptr g.v3.cap.toNat) ∗
      vecPtListOf A (a + 488#64) vecs ∗ memRegion (a + 872#64) 16 ∗
      memRegion (a + 888#64) 40) ∗
      CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded ∗
      A.pool ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
    (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · wp_steps
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
    · wp_steps; wp_apply
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 hcl1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine CryptoVerification.Cli.SpqrV1.Drop.seq_clean_lscl hcl1 (mid := (blkPl_443).base + 352#64)
      (P_mid := ((a ↦₆₄ 4#64) ∗
        polyEncoderAt A (a + 8#64) st.sending_ek ∗
        ((a + 408#64) ↦₆₄ g.v1.cap) ∗ ((a + 416#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 424#64) 8 ∗
        ((a + 432#64) ↦₆₄ g.v2.cap) ∗ ((a + 440#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 448#64) 8 ∗
        ((a + 456#64) ↦₆₄ g.v3.cap) ∗ ((a + 464#64) ↦₆₄ g.v3.ptr) ∗ memRegion (a + 472#64) 16 ∗
        (if (g.v3.cap == 0#64) = true then emp
         else A.live g.v3.ptr g.v3.cap.toNat 1 ∗ memRegion g.v3.ptr g.v3.cap.toNat) ∗
        vecPtListOf A (a + 488#64) vecs ∗ memRegion (a + 872#64) 16 ∗
        memRegion (a + 888#64) 40) ∗
        CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded ∗
        A.pool ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
      (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
      ?_ ?_
    · by_cases hc2 : (g.v2.cap == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
      · wp_steps
        refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
      · wp_steps; wp_apply
        refine align_pre (by rw [hsp_1]; simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
    · intro s2 hpc2 hrun2 hcl2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      refine CryptoVerification.Cli.SpqrV1.Drop.seq_clean_lscl hcl2 (mid := (blkPl_443).base + 372#64)
        (P_mid := ((a ↦₆₄ 4#64) ∗
          polyEncoderAt A (a + 8#64) st.sending_ek ∗
          memRegion (a + 408#64) 80 ∗
          vecPtListOf A (a + 488#64) vecs ∗ memRegion (a + 872#64) 16 ∗
          memRegion (a + 888#64) 40) ∗
          CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded ∗
          A.pool ∗ stackAt (s0.sp - 32#64) dropStack32 ∗
          (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
        (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
        ?_ ?_
      · have hhdr80 := threeVec408HeadersAt_entails_memRegion_80 a g
        dsimp only [threeVec408HeadersAt] at hhdr80
        by_cases hc3 : (g.v3.cap == 0#64) = true <;>
          simp only [hc3, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
        · wp_steps
          refine SepWP.focus_weaken hhdr80 (by sep_focus) ?_
          refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
          refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
        · wp_steps; wp_apply
          refine SepWP.focus_weaken hhdr80 (by sep_focus) ?_
          have hsp_eq : stackAt s2.sp allocHookStack = stackAt (s0.sp - 32#64) allocHookStack := by rw [hsp_2]
          refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
          refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
          refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
      · intro s3 hpc3 hrun3 _hcl3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
        dsimp only [CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]
        wp_steps_lscl (lsmpl.base 441)
        wp_call henc_cl ⟨a + 8#64, st.sending_ek⟩
        wp_steps_lscl (lsmpl.base 440)
        have hsp_eq : stackAt s3.sp dropStack32 = stackAt (s0.sp - 32#64) dropStack32 := by
          rw [hsp_3]
        refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
        refine SepWP.focus_weaken
          (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x19) v_x19)
          (by sep_focus) ?_
        refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
        wp_call hdec_cl ⟨a + 488#64, vecs⟩
        refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp).symm) (by sep_focus) ?_
        refine SepWP.focus_weaken (polyDecoder488_post_join a) (by sep_focus) ?_
        have hjoin480 : memRegion (a + 8#64) 400 ∗ memRegion (a + 408#64) 80 ⊢
            memRegion (a + 8#64) 480 := by
          have h408 : (a + 8#64) + 400#64 = a + 408#64 := BitVec.add_assoc a 8#64 400#64
          rw [← h408, show (480 : Nat) = 400 + 80 from rfl,
              ProofLib.memRegion_split (a + 8#64) 400 80 (by decide)]
          exact Entails.refl _
        refine SepWP.focus_weaken hjoin480 (by sep_focus) ?_
        have hjoin880 : memRegion (a + 8#64) 480 ∗ memRegion (a + 488#64) polyDecoderSize ⊢
            memRegion (a + 8#64) 880 := by
          have h488 : (a + 8#64) + 480#64 = a + 488#64 := BitVec.add_assoc a 8#64 480#64
          rw [← h488, show (880 : Nat) = 480 + polyDecoderSize from rfl,
              ProofLib.memRegion_split (a + 8#64) 480 polyDecoderSize (by decide)]
          exact Entails.refl _
        refine SepWP.focus_weaken hjoin880 (by sep_focus) ?_
        have hjoin928 := tag_and_two_regions_entails_928 a 4#64 880 40 888#64
          (BitVec.add_assoc a 8#64 880#64).symm rfl
        refine SepWP.focus_weaken hjoin928 (by sep_focus) ?_
        wp_done

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_ct1Received_placed_ok
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {H : String → Option (State → State)}
    (hdealloc : subroutine_ok (lsProg_443 H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (henc : subroutine_ok (CryptoVerification.Cli.SpqrV1.Drop.Placed.lsProg_441 H)
      (CryptoVerification.Cli.SpqrV1.Drop.Placed.blkPl_441).base (dropGluePolyEncoderSpec A))
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 H) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedVariantSpec A (.ct1Received st))) := by
  have henc_cl : subroutine_ok (lsProg_443 H) (lsmpl.base 441)
      (withLsCl lsmpl (dropGluePolyEncoderSpec A)) :=
    ls_subroutine_ok_cl_of_plain (callerProg := lsProg_443 H) henc
  simp only [withLsCodeLoaded, CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedVariantSpec]
  have hdealloc_raw := hdealloc; simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [withLsCl, dropGluePolyEncoderSpec, chunkedStatesAt, chunkedCt1ReceivedAt,
    CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedAt,
    chunkedStatesLocal1JumpTableBytes, chunkedStatesSize, polyEncoderSize, dropGluePoly16Stack,
    spqrPolyApi] at hdealloc_raw henc_cl ⊢
  wp_init a s0
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  refine SepWP.focus_weaken (unchunkedEkSentCt1Received408_entails_dealloc A a st.uc) (by sep_focus) ?_
  wp_pull_exists; rename_i g
  dsimp only [fourVec408HeadersAt, vecCapPtrDealloc]
  nth_rw 1 [stackAt_dropStackPoly64_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x20 v_x19
  have hsplit32 := stackAt_dropStack32_split_sub32 s0.sp
  refine SepWP.focus_weaken (Entails.of_eq hsplit32) (by sep_focus) ?_
  refine CryptoVerification.Cli.SpqrV1.Drop.seq_clean_lscl ‹_› (mid := (blkPl_443).base + 88#64)
    (P_mid := ((a ↦₆₄ 5#64) ∗
      polyEncoderAt A (a + 8#64) st.sending_ek ∗
      ((a + 408#64) ↦₆₄ g.v1.cap) ∗ ((a + 416#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 424#64) 8 ∗
      ((a + 432#64) ↦₆₄ g.v2.cap) ∗ ((a + 440#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 448#64) 8 ∗
      ((a + 456#64) ↦₆₄ g.v3.cap) ∗ ((a + 464#64) ↦₆₄ g.v3.ptr) ∗ memRegion (a + 472#64) 8 ∗
      ((a + 480#64) ↦₆₄ g.v4.cap) ∗ ((a + 488#64) ↦₆₄ g.v4.ptr) ∗ memRegion (a + 496#64) 16 ∗
      (if (g.v2.cap == 0#64) = true then emp
       else A.live g.v2.ptr g.v2.cap.toNat 1 ∗ memRegion g.v2.ptr g.v2.cap.toNat) ∗
      (if (g.v3.cap == 0#64) = true then emp
       else A.live g.v3.ptr g.v3.cap.toNat 1 ∗ memRegion g.v3.ptr g.v3.cap.toNat) ∗
      (if (g.v4.cap == 0#64) = true then emp
       else A.live g.v4.ptr g.v4.cap.toNat 1 ∗ memRegion g.v4.ptr g.v4.cap.toNat) ∗
      memRegion (a + 512#64) 416) ∗
      CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded ∗
      A.pool ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
    (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · wp_steps
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
    · wp_steps; wp_apply
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 hcl1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine CryptoVerification.Cli.SpqrV1.Drop.seq_clean_lscl hcl1 (mid := (blkPl_443).base + 108#64)
      (P_mid := ((a ↦₆₄ 5#64) ∗
        polyEncoderAt A (a + 8#64) st.sending_ek ∗
        ((a + 408#64) ↦₆₄ g.v1.cap) ∗ ((a + 416#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 424#64) 8 ∗
        ((a + 432#64) ↦₆₄ g.v2.cap) ∗ ((a + 440#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 448#64) 8 ∗
        ((a + 456#64) ↦₆₄ g.v3.cap) ∗ ((a + 464#64) ↦₆₄ g.v3.ptr) ∗ memRegion (a + 472#64) 8 ∗
        ((a + 480#64) ↦₆₄ g.v4.cap) ∗ ((a + 488#64) ↦₆₄ g.v4.ptr) ∗ memRegion (a + 496#64) 16 ∗
        (if (g.v3.cap == 0#64) = true then emp
         else A.live g.v3.ptr g.v3.cap.toNat 1 ∗ memRegion g.v3.ptr g.v3.cap.toNat) ∗
        (if (g.v4.cap == 0#64) = true then emp
         else A.live g.v4.ptr g.v4.cap.toNat 1 ∗ memRegion g.v4.ptr g.v4.cap.toNat) ∗
        memRegion (a + 512#64) 416) ∗
        CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded ∗
        A.pool ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
      (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
      ?_ ?_
    · by_cases hc2 : (g.v2.cap == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
      · wp_steps
        refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
      · wp_steps; wp_apply
        refine align_pre (by rw [hsp_1]; simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
    · intro s2 hpc2 hrun2 hcl2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      refine CryptoVerification.Cli.SpqrV1.Drop.seq_clean_lscl hcl2 (mid := (blkPl_443).base + 128#64)
        (P_mid := ((a ↦₆₄ 5#64) ∗
          polyEncoderAt A (a + 8#64) st.sending_ek ∗
          ((a + 408#64) ↦₆₄ g.v1.cap) ∗ ((a + 416#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 424#64) 8 ∗
          ((a + 432#64) ↦₆₄ g.v2.cap) ∗ ((a + 440#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 448#64) 8 ∗
          ((a + 456#64) ↦₆₄ g.v3.cap) ∗ ((a + 464#64) ↦₆₄ g.v3.ptr) ∗ memRegion (a + 472#64) 8 ∗
          ((a + 480#64) ↦₆₄ g.v4.cap) ∗ ((a + 488#64) ↦₆₄ g.v4.ptr) ∗ memRegion (a + 496#64) 16 ∗
          (if (g.v4.cap == 0#64) = true then emp
           else A.live g.v4.ptr g.v4.cap.toNat 1 ∗ memRegion g.v4.ptr g.v4.cap.toNat) ∗
          memRegion (a + 512#64) 416) ∗
          CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded ∗
          A.pool ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
          (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
        (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
        ?_ ?_
      · by_cases hc3 : (g.v3.cap == 0#64) = true <;>
          simp only [hc3, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
        · wp_steps
          refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
        · wp_steps; wp_apply
          refine align_pre (by rw [hsp_2]; simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
      · intro s3 hpc3 hrun3 hcl3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
        refine CryptoVerification.Cli.SpqrV1.Drop.seq_clean_lscl hcl3 (mid := (blkPl_443).base + 696#64)
          (P_mid := ((a ↦₆₄ 5#64) ∗
            polyEncoderAt A (a + 8#64) st.sending_ek ∗
            memRegion (a + 408#64) 104 ∗
            memRegion (a + 512#64) 416) ∗
            CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded ∗
            A.pool ∗ stackAt (s0.sp - 32#64) dropStack32 ∗
            (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
          (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
          ?_ ?_
        · have hhdr104 := fourVec408HeadersAt_entails_memRegion_104 a g
          dsimp only [fourVec408HeadersAt] at hhdr104
          by_cases hc4 : (g.v4.cap == 0#64) = true <;>
            simp only [hc4, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
          · wp_steps
            refine SepWP.focus_weaken hhdr104 (by sep_focus) ?_
            refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
            refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
          · wp_steps; wp_apply
            refine SepWP.focus_weaken hhdr104 (by sep_focus) ?_
            have hsp_eq : stackAt s3.sp allocHookStack = stackAt (s0.sp - 32#64) allocHookStack := by rw [hsp_3]
            refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
            refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
            refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
        · intro s4 hpc4 hrun4 _hcl4 ⟨⟨hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hx19_4⟩
          dsimp only [CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]
          wp_steps_lscl (lsmpl.base 441)
          refine SepWP.focus_weaken
            (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
              (s0.readReg64 .x19) v_x19)
            (by sep_focus) ?_
          refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
          wp_call henc_cl ⟨a + 8#64, st.sending_ek⟩
          refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp).symm) (by sep_focus) ?_
          have hjoin504 : memRegion (a + 8#64) 400 ∗ memRegion (a + 408#64) 104 ⊢
              memRegion (a + 8#64) 504 := by
            have h408 : (a + 8#64) + 400#64 = a + 408#64 := BitVec.add_assoc a 8#64 400#64
            rw [← h408, show (504 : Nat) = 400 + 104 from rfl,
                ProofLib.memRegion_split (a + 8#64) 400 104 (by decide)]
            exact Entails.refl _
          refine SepWP.focus_weaken hjoin504 (by sep_focus) ?_
          have hjoin928 := tag_and_two_regions_entails_928 a 5#64 504 416 512#64
            (BitVec.add_assoc a 8#64 504#64).symm rfl
          refine SepWP.focus_weaken hjoin928 (by sep_focus) ?_
          wp_done

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_keysSampled_placed_ok
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {H : String → Option (State → State)}
    (hdealloc : subroutine_ok (lsProg_443 H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (henc : subroutine_ok (CryptoVerification.Cli.SpqrV1.Drop.Placed.lsProg_441 H)
      (CryptoVerification.Cli.SpqrV1.Drop.Placed.blkPl_441).base (dropGluePolyEncoderSpec A))
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 H) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedVariantSpec A (.keysSampled st))) := by
  have henc_cl : subroutine_ok (lsProg_443 H) (lsmpl.base 441)
      (withLsCl lsmpl (dropGluePolyEncoderSpec A)) :=
    ls_subroutine_ok_cl_of_plain (callerProg := lsProg_443 H) henc
  simp only [withLsCodeLoaded, CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedVariantSpec]
  have hdealloc_raw := hdealloc; simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [withLsCl, dropGluePolyEncoderSpec, chunkedStatesAt, chunkedKeysSampledAt,
    CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedAt,
    chunkedStatesLocal1JumpTableBytes, chunkedStatesSize, polyEncoderSize, dropGluePoly16Stack,
    spqrPolyApi] at hdealloc_raw henc_cl ⊢
  wp_init a s0
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  have hdealloc408 : unchunkedHeaderSentAt A (a + 408#64) st.uc ⊢
      ∃∗ g : FourVecGhost,
        fourVec408HeadersAt a g ∗
        vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
        vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
        vecCapPtrDealloc A g.v3.cap g.v3.ptr ∗
        vecCapPtrDealloc A g.v4.cap g.v4.ptr :=
    unchunkedEkSentCt1Received408_entails_dealloc A a (unchunkedHeaderSentToEkSentCt1Received st.uc)
  refine SepWP.focus_weaken hdealloc408 (by sep_focus) ?_
  wp_pull_exists; rename_i g
  dsimp only [fourVec408HeadersAt, vecCapPtrDealloc]
  nth_rw 1 [stackAt_dropStackPoly64_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x20 v_x19
  have hsplit32 := stackAt_dropStack32_split_sub32 s0.sp
  refine SepWP.focus_weaken (Entails.of_eq hsplit32) (by sep_focus) ?_
  refine CryptoVerification.Cli.SpqrV1.Drop.seq_clean_lscl ‹_› (mid := (blkPl_443).base + 88#64)
    (P_mid := ((a ↦₆₄ 3#64) ∗
      polyEncoderAt A (a + 8#64) st.sending_hdr ∗
      ((a + 408#64) ↦₆₄ g.v1.cap) ∗ ((a + 416#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 424#64) 8 ∗
      ((a + 432#64) ↦₆₄ g.v2.cap) ∗ ((a + 440#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 448#64) 8 ∗
      ((a + 456#64) ↦₆₄ g.v3.cap) ∗ ((a + 464#64) ↦₆₄ g.v3.ptr) ∗ memRegion (a + 472#64) 8 ∗
      ((a + 480#64) ↦₆₄ g.v4.cap) ∗ ((a + 488#64) ↦₆₄ g.v4.ptr) ∗ memRegion (a + 496#64) 16 ∗
      (if (g.v2.cap == 0#64) = true then emp
       else A.live g.v2.ptr g.v2.cap.toNat 1 ∗ memRegion g.v2.ptr g.v2.cap.toNat) ∗
      (if (g.v3.cap == 0#64) = true then emp
       else A.live g.v3.ptr g.v3.cap.toNat 1 ∗ memRegion g.v3.ptr g.v3.cap.toNat) ∗
      (if (g.v4.cap == 0#64) = true then emp
       else A.live g.v4.ptr g.v4.cap.toNat 1 ∗ memRegion g.v4.ptr g.v4.cap.toNat) ∗
      memRegion (a + 512#64) 416) ∗
      CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded ∗
      A.pool ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
    (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · wp_steps
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
    · wp_steps; wp_apply
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 hcl1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine CryptoVerification.Cli.SpqrV1.Drop.seq_clean_lscl hcl1 (mid := (blkPl_443).base + 108#64)
      (P_mid := ((a ↦₆₄ 3#64) ∗
        polyEncoderAt A (a + 8#64) st.sending_hdr ∗
        ((a + 408#64) ↦₆₄ g.v1.cap) ∗ ((a + 416#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 424#64) 8 ∗
        ((a + 432#64) ↦₆₄ g.v2.cap) ∗ ((a + 440#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 448#64) 8 ∗
        ((a + 456#64) ↦₆₄ g.v3.cap) ∗ ((a + 464#64) ↦₆₄ g.v3.ptr) ∗ memRegion (a + 472#64) 8 ∗
        ((a + 480#64) ↦₆₄ g.v4.cap) ∗ ((a + 488#64) ↦₆₄ g.v4.ptr) ∗ memRegion (a + 496#64) 16 ∗
        (if (g.v3.cap == 0#64) = true then emp
         else A.live g.v3.ptr g.v3.cap.toNat 1 ∗ memRegion g.v3.ptr g.v3.cap.toNat) ∗
        (if (g.v4.cap == 0#64) = true then emp
         else A.live g.v4.ptr g.v4.cap.toNat 1 ∗ memRegion g.v4.ptr g.v4.cap.toNat) ∗
        memRegion (a + 512#64) 416) ∗
        CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded ∗
        A.pool ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
      (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
      ?_ ?_
    · by_cases hc2 : (g.v2.cap == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
      · wp_steps
        refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
      · wp_steps; wp_apply
        refine align_pre (by rw [hsp_1]; simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
    · intro s2 hpc2 hrun2 hcl2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      refine CryptoVerification.Cli.SpqrV1.Drop.seq_clean_lscl hcl2 (mid := (blkPl_443).base + 128#64)
        (P_mid := ((a ↦₆₄ 3#64) ∗
          polyEncoderAt A (a + 8#64) st.sending_hdr ∗
          ((a + 408#64) ↦₆₄ g.v1.cap) ∗ ((a + 416#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 424#64) 8 ∗
          ((a + 432#64) ↦₆₄ g.v2.cap) ∗ ((a + 440#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 448#64) 8 ∗
          ((a + 456#64) ↦₆₄ g.v3.cap) ∗ ((a + 464#64) ↦₆₄ g.v3.ptr) ∗ memRegion (a + 472#64) 8 ∗
          ((a + 480#64) ↦₆₄ g.v4.cap) ∗ ((a + 488#64) ↦₆₄ g.v4.ptr) ∗ memRegion (a + 496#64) 16 ∗
          (if (g.v4.cap == 0#64) = true then emp
           else A.live g.v4.ptr g.v4.cap.toNat 1 ∗ memRegion g.v4.ptr g.v4.cap.toNat) ∗
          memRegion (a + 512#64) 416) ∗
          CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded ∗
          A.pool ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
          (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
        (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
        ?_ ?_
      · by_cases hc3 : (g.v3.cap == 0#64) = true <;>
          simp only [hc3, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
        · wp_steps
          refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
        · wp_steps; wp_apply
          refine align_pre (by rw [hsp_2]; simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
      · intro s3 hpc3 hrun3 hcl3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
        refine CryptoVerification.Cli.SpqrV1.Drop.seq_clean_lscl hcl3 (mid := (blkPl_443).base + 696#64)
          (P_mid := ((a ↦₆₄ 3#64) ∗
            polyEncoderAt A (a + 8#64) st.sending_hdr ∗
            memRegion (a + 408#64) 104 ∗
            memRegion (a + 512#64) 416) ∗
            CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded ∗
            A.pool ∗ stackAt (s0.sp - 32#64) dropStack32 ∗
            (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
          (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
          ?_ ?_
        · have hhdr104 := fourVec408HeadersAt_entails_memRegion_104 a g
          dsimp only [fourVec408HeadersAt] at hhdr104
          by_cases hc4 : (g.v4.cap == 0#64) = true <;>
            simp only [hc4, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
          · wp_steps
            refine SepWP.focus_weaken hhdr104 (by sep_focus) ?_
            refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
            refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
          · wp_steps; wp_apply
            refine SepWP.focus_weaken hhdr104 (by sep_focus) ?_
            have hsp_eq : stackAt s3.sp allocHookStack = stackAt (s0.sp - 32#64) allocHookStack := by rw [hsp_3]
            refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
            refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
            refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
        · intro s4 hpc4 hrun4 _hcl4 ⟨⟨hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hx19_4⟩
          dsimp only [CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]
          wp_steps_lscl (lsmpl.base 441)
          refine SepWP.focus_weaken
            (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
              (s0.readReg64 .x19) v_x19)
            (by sep_focus) ?_
          refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
          wp_call henc_cl ⟨a + 8#64, st.sending_hdr⟩
          refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp).symm) (by sep_focus) ?_
          have hjoin504 : memRegion (a + 8#64) 400 ∗ memRegion (a + 408#64) 104 ⊢
              memRegion (a + 8#64) 504 := by
            have h408 : (a + 8#64) + 400#64 = a + 408#64 := BitVec.add_assoc a 8#64 400#64
            rw [← h408, show (504 : Nat) = 400 + 104 from rfl,
                ProofLib.memRegion_split (a + 8#64) 400 104 (by decide)]
            exact Entails.refl _
          refine SepWP.focus_weaken hjoin504 (by sep_focus) ?_
          have hjoin928 := tag_and_two_regions_entails_928 a 3#64 504 416 512#64
            (BitVec.add_assoc a 8#64 504#64).symm rfl
          refine SepWP.focus_weaken hjoin928 (by sep_focus) ?_
          wp_done

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_ekReceivedCt1Sampled_placed_ok
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {H : String → Option (State → State)}
    (hdealloc : subroutine_ok (lsProg_443 H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (henc : subroutine_ok (CryptoVerification.Cli.SpqrV1.Drop.Placed.lsProg_441 H)
      (CryptoVerification.Cli.SpqrV1.Drop.Placed.blkPl_441).base (dropGluePolyEncoderSpec A))
    (st : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 H) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedVariantSpec A (.ekReceivedCt1Sampled st))) := by
  have henc_cl : subroutine_ok (lsProg_443 H) (lsmpl.base 441)
      (withLsCl lsmpl (dropGluePolyEncoderSpec A)) :=
    ls_subroutine_ok_cl_of_plain (callerProg := lsProg_443 H) henc
  simp only [withLsCodeLoaded, CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedVariantSpec]
  have hdealloc_raw := hdealloc; simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [withLsCl, dropGluePolyEncoderSpec, chunkedStatesAt, chunkedEkReceivedCt1SampledAt,
    CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedAt,
    chunkedStatesLocal1JumpTableBytes, chunkedStatesSize, polyEncoderSize, dropGluePoly16Stack,
    spqrPolyApi] at hdealloc_raw henc_cl ⊢
  wp_init a s0
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  have hdealloc408 : unchunkedCt1SentEkReceivedAt A (a + 408#64) st.uc ⊢
      ∃∗ g : FiveVecGhost,
        fiveVec408HeadersAt a g ∗
        vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
        vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
        vecCapPtrDealloc A g.v3.cap g.v3.ptr ∗
        vecCapPtrDealloc A g.v4.cap g.v4.ptr ∗
        vecCapPtrDealloc A g.v5.cap g.v5.ptr :=
    unchunkedCt1Sent408_entails_dealloc A a
      { epoch := st.uc.epoch, hdr := st.uc.es, es := st.uc.ek, ct1 := st.uc.ct1, auth := st.uc.auth }
  refine SepWP.focus_weaken hdealloc408 (by sep_focus) ?_
  wp_pull_exists; rename_i g
  dsimp only [fiveVec408HeadersAt, vecCapPtrDealloc]
  nth_rw 1 [stackAt_dropStackPoly64_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x20 v_x19
  have hsplit32 := stackAt_dropStack32_split_sub32 s0.sp
  refine SepWP.focus_weaken (Entails.of_eq hsplit32) (by sep_focus) ?_
  refine CryptoVerification.Cli.SpqrV1.Drop.seq_clean_lscl ‹_› (mid := (blkPl_443).base + 616#64)
    (P_mid := ((a ↦₆₄ 10#64) ∗
      polyEncoderAt A (a + 8#64) st.sending_ct1 ∗
      ((a + 408#64) ↦₆₄ g.v1.cap) ∗ ((a + 416#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 424#64) 8 ∗
      ((a + 432#64) ↦₆₄ g.v2.cap) ∗ ((a + 440#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 448#64) 8 ∗
      ((a + 456#64) ↦₆₄ g.v3.cap) ∗ ((a + 464#64) ↦₆₄ g.v3.ptr) ∗ memRegion (a + 472#64) 8 ∗
      ((a + 480#64) ↦₆₄ g.v4.cap) ∗ ((a + 488#64) ↦₆₄ g.v4.ptr) ∗ memRegion (a + 496#64) 8 ∗
      ((a + 504#64) ↦₆₄ g.v5.cap) ∗ ((a + 512#64) ↦₆₄ g.v5.ptr) ∗ memRegion (a + 520#64) 16 ∗
      (if (g.v2.cap == 0#64) = true then emp
       else A.live g.v2.ptr g.v2.cap.toNat 1 ∗ memRegion g.v2.ptr g.v2.cap.toNat) ∗
      (if (g.v3.cap == 0#64) = true then emp
       else A.live g.v3.ptr g.v3.cap.toNat 1 ∗ memRegion g.v3.ptr g.v3.cap.toNat) ∗
      (if (g.v4.cap == 0#64) = true then emp
       else A.live g.v4.ptr g.v4.cap.toNat 1 ∗ memRegion g.v4.ptr g.v4.cap.toNat) ∗
      (if (g.v5.cap == 0#64) = true then emp
       else A.live g.v5.ptr g.v5.cap.toNat 1 ∗ memRegion g.v5.ptr g.v5.cap.toNat) ∗
      memRegion (a + 536#64) 392) ∗
      CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded ∗
      A.pool ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
    (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · wp_steps
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
    · wp_steps; wp_apply
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 hcl1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine CryptoVerification.Cli.SpqrV1.Drop.seq_clean_lscl hcl1 (mid := (blkPl_443).base + 636#64)
      (P_mid := ((a ↦₆₄ 10#64) ∗
        polyEncoderAt A (a + 8#64) st.sending_ct1 ∗
        ((a + 408#64) ↦₆₄ g.v1.cap) ∗ ((a + 416#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 424#64) 8 ∗
        ((a + 432#64) ↦₆₄ g.v2.cap) ∗ ((a + 440#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 448#64) 8 ∗
        ((a + 456#64) ↦₆₄ g.v3.cap) ∗ ((a + 464#64) ↦₆₄ g.v3.ptr) ∗ memRegion (a + 472#64) 8 ∗
        ((a + 480#64) ↦₆₄ g.v4.cap) ∗ ((a + 488#64) ↦₆₄ g.v4.ptr) ∗ memRegion (a + 496#64) 8 ∗
        ((a + 504#64) ↦₆₄ g.v5.cap) ∗ ((a + 512#64) ↦₆₄ g.v5.ptr) ∗ memRegion (a + 520#64) 16 ∗
        (if (g.v3.cap == 0#64) = true then emp
         else A.live g.v3.ptr g.v3.cap.toNat 1 ∗ memRegion g.v3.ptr g.v3.cap.toNat) ∗
        (if (g.v4.cap == 0#64) = true then emp
         else A.live g.v4.ptr g.v4.cap.toNat 1 ∗ memRegion g.v4.ptr g.v4.cap.toNat) ∗
        (if (g.v5.cap == 0#64) = true then emp
         else A.live g.v5.ptr g.v5.cap.toNat 1 ∗ memRegion g.v5.ptr g.v5.cap.toNat) ∗
        memRegion (a + 536#64) 392) ∗
        CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded ∗
        A.pool ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
      (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
      ?_ ?_
    · by_cases hc2 : (g.v2.cap == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
      · wp_steps
        refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
      · wp_steps; wp_apply
        refine align_pre (by rw [hsp_1]; simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
    · intro s2 hpc2 hrun2 hcl2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      refine CryptoVerification.Cli.SpqrV1.Drop.seq_clean_lscl hcl2 (mid := (blkPl_443).base + 656#64)
        (P_mid := ((a ↦₆₄ 10#64) ∗
          polyEncoderAt A (a + 8#64) st.sending_ct1 ∗
          ((a + 408#64) ↦₆₄ g.v1.cap) ∗ ((a + 416#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 424#64) 8 ∗
          ((a + 432#64) ↦₆₄ g.v2.cap) ∗ ((a + 440#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 448#64) 8 ∗
          ((a + 456#64) ↦₆₄ g.v3.cap) ∗ ((a + 464#64) ↦₆₄ g.v3.ptr) ∗ memRegion (a + 472#64) 8 ∗
          ((a + 480#64) ↦₆₄ g.v4.cap) ∗ ((a + 488#64) ↦₆₄ g.v4.ptr) ∗ memRegion (a + 496#64) 8 ∗
          ((a + 504#64) ↦₆₄ g.v5.cap) ∗ ((a + 512#64) ↦₆₄ g.v5.ptr) ∗ memRegion (a + 520#64) 16 ∗
          (if (g.v4.cap == 0#64) = true then emp
           else A.live g.v4.ptr g.v4.cap.toNat 1 ∗ memRegion g.v4.ptr g.v4.cap.toNat) ∗
          (if (g.v5.cap == 0#64) = true then emp
           else A.live g.v5.ptr g.v5.cap.toNat 1 ∗ memRegion g.v5.ptr g.v5.cap.toNat) ∗
          memRegion (a + 536#64) 392) ∗
          CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded ∗
          A.pool ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
          (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
        (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
        ?_ ?_
      · by_cases hc3 : (g.v3.cap == 0#64) = true <;>
          simp only [hc3, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
        · wp_steps
          refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
        · wp_steps; wp_apply
          refine align_pre (by rw [hsp_2]; simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
      · intro s3 hpc3 hrun3 hcl3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
        refine CryptoVerification.Cli.SpqrV1.Drop.seq_clean_lscl hcl3 (mid := (blkPl_443).base + 676#64)
          (P_mid := ((a ↦₆₄ 10#64) ∗
            polyEncoderAt A (a + 8#64) st.sending_ct1 ∗
            ((a + 408#64) ↦₆₄ g.v1.cap) ∗ ((a + 416#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 424#64) 8 ∗
            ((a + 432#64) ↦₆₄ g.v2.cap) ∗ ((a + 440#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 448#64) 8 ∗
            ((a + 456#64) ↦₆₄ g.v3.cap) ∗ ((a + 464#64) ↦₆₄ g.v3.ptr) ∗ memRegion (a + 472#64) 8 ∗
            ((a + 480#64) ↦₆₄ g.v4.cap) ∗ ((a + 488#64) ↦₆₄ g.v4.ptr) ∗ memRegion (a + 496#64) 8 ∗
            ((a + 504#64) ↦₆₄ g.v5.cap) ∗ ((a + 512#64) ↦₆₄ g.v5.ptr) ∗ memRegion (a + 520#64) 16 ∗
            (if (g.v5.cap == 0#64) = true then emp
             else A.live g.v5.ptr g.v5.cap.toNat 1 ∗ memRegion g.v5.ptr g.v5.cap.toNat) ∗
            memRegion (a + 536#64) 392) ∗
            CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded ∗
            A.pool ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
            (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
          (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
          ?_ ?_
        · by_cases hc4 : (g.v4.cap == 0#64) = true <;>
            simp only [hc4, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
          · wp_steps
            refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
          · wp_steps; wp_apply
            refine align_pre (by rw [hsp_3]; simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
        · intro s4 hpc4 hrun4 hcl4 ⟨⟨hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hx19_4⟩
          refine CryptoVerification.Cli.SpqrV1.Drop.seq_clean_lscl hcl4 (mid := (blkPl_443).base + 696#64)
            (P_mid := ((a ↦₆₄ 10#64) ∗
              polyEncoderAt A (a + 8#64) st.sending_ct1 ∗
              memRegion (a + 408#64) 128 ∗
              memRegion (a + 536#64) 392) ∗
              CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded ∗
              A.pool ∗ stackAt (s0.sp - 32#64) dropStack32 ∗
              (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
               ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
            (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
            ?_ ?_
          · have hhdr128 := fiveVec408HeadersAt_entails_memRegion_128 a g
            dsimp only [fiveVec408HeadersAt] at hhdr128
            by_cases hc5 : (g.v5.cap == 0#64) = true <;>
              simp only [hc5, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
            · wp_steps
              refine SepWP.focus_weaken hhdr128 (by sep_focus) ?_
              refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
              refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
            · wp_steps; wp_apply
              refine SepWP.focus_weaken hhdr128 (by sep_focus) ?_
              have hsp_eq : stackAt s4.sp allocHookStack = stackAt (s0.sp - 32#64) allocHookStack := by rw [hsp_4]
              refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
              refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
              refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
          · intro s5 hpc5 hrun5 _hcl5 ⟨⟨hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hsp_5, htrace_5, hvregs_5⟩, hx19_5⟩
            dsimp only [CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedExpanded]
            wp_steps_lscl (lsmpl.base 441)
            refine SepWP.focus_weaken
              (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
                (s0.readReg64 .x19) v_x19)
              (by sep_focus) ?_
            refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
            wp_call henc_cl ⟨a + 8#64, st.sending_ct1⟩
            refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp).symm) (by sep_focus) ?_
            have hjoin528 : memRegion (a + 8#64) 400 ∗ memRegion (a + 408#64) 128 ⊢
                memRegion (a + 8#64) 528 := by
              have h408 : (a + 8#64) + 400#64 = a + 408#64 := BitVec.add_assoc a 8#64 400#64
              rw [← h408, show (528 : Nat) = 400 + 128 from rfl,
                  ProofLib.memRegion_split (a + 8#64) 400 128 (by decide)]
              exact Entails.refl _
            refine SepWP.focus_weaken hjoin528 (by sep_focus) ?_
            have hjoin928 := tag_and_two_regions_entails_928 a 10#64 528 392 536#64
              (BitVec.add_assoc a 8#64 528#64).symm rfl
            refine SepWP.focus_weaken hjoin928 (by sep_focus) ?_
            wp_done

/-! ## 2. `HookSat` & `withPanics` Per-Variant Wrappers (Part 2/2) -/

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_ct2Sampled_placed
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {H : String → Option (State → State)}
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (st : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 H) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedVariantSpec A (.ct2Sampled st))) :=
  CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_ct2Sampled_placed_ok
    (SpqrV1.Alloc.spqr_hook_ok_of_mem hdealloc)
    (CryptoVerification.Cli.SpqrV1.Drop.drop_poly_encoder_local1_placed hdealloc) st

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_ct2Sampled_placed_x
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (st : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 (Rust.withPanics ext)) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedVariantSpec A (.ct2Sampled st))) :=
  CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_ct2Sampled_placed
    (CryptoVerification.Cli.SpqrV1.Drop.hookSat_dealloc_withPanics hdealloc) st

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_headerSent_placed
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {H : String → Option (State → State)}
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 H) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedVariantSpec A (.headerSent st))) :=
  CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_headerSent_placed_ok
    (SpqrV1.Alloc.spqr_hook_ok_of_mem hdealloc)
    (CryptoVerification.Cli.SpqrV1.Drop.drop_poly_encoder_local1_placed hdealloc)
    (CryptoVerification.Cli.SpqrV1.Drop.drop_poly_decoder_placed hdealloc) st

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_headerSent_placed_x
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 (Rust.withPanics ext)) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedVariantSpec A (.headerSent st))) :=
  CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_headerSent_placed
    (CryptoVerification.Cli.SpqrV1.Drop.hookSat_dealloc_withPanics hdealloc) st

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_ct1Received_placed
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {H : String → Option (State → State)}
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 H) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedVariantSpec A (.ct1Received st))) :=
  CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_ct1Received_placed_ok
    (SpqrV1.Alloc.spqr_hook_ok_of_mem hdealloc)
    (CryptoVerification.Cli.SpqrV1.Drop.drop_poly_encoder_local1_placed hdealloc) st

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_ct1Received_placed_x
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 (Rust.withPanics ext)) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedVariantSpec A (.ct1Received st))) :=
  CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_ct1Received_placed
    (CryptoVerification.Cli.SpqrV1.Drop.hookSat_dealloc_withPanics hdealloc) st

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_keysSampled_placed
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {H : String → Option (State → State)}
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 H) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedVariantSpec A (.keysSampled st))) :=
  CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_keysSampled_placed_ok
    (SpqrV1.Alloc.spqr_hook_ok_of_mem hdealloc)
    (CryptoVerification.Cli.SpqrV1.Drop.drop_poly_encoder_local1_placed hdealloc) st

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_keysSampled_placed_x
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 (Rust.withPanics ext)) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedVariantSpec A (.keysSampled st))) :=
  CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_keysSampled_placed
    (CryptoVerification.Cli.SpqrV1.Drop.hookSat_dealloc_withPanics hdealloc) st

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_ekReceivedCt1Sampled_placed
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {H : String → Option (State → State)}
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (st : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 H) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedVariantSpec A (.ekReceivedCt1Sampled st))) :=
  CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_ekReceivedCt1Sampled_placed_ok
    (SpqrV1.Alloc.spqr_hook_ok_of_mem hdealloc)
    (CryptoVerification.Cli.SpqrV1.Drop.drop_poly_encoder_local1_placed hdealloc) st

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_ekReceivedCt1Sampled_placed_x
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (st : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_443 (Rust.withPanics ext)) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedVariantSpec A (.ekReceivedCt1Sampled st))) :=
  CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_ekReceivedCt1Sampled_placed
    (CryptoVerification.Cli.SpqrV1.Drop.hookSat_dealloc_withPanics hdealloc) st

/-! ## 3. Combined Top-Level `Block 443` Contracts -/

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_placed_ok
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {H : String → Option (State → State)}
    (hdealloc : subroutine_ok (lsProg_443 H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hdec : subroutine_ok (CryptoVerification.Cli.SpqrV1.Drop.Placed.lsProg_440 H)
      (CryptoVerification.Cli.SpqrV1.Drop.Placed.blkPl_440).base (dropGlueSortedSetPt16Spec A))
    (henc : subroutine_ok (CryptoVerification.Cli.SpqrV1.Drop.Placed.lsProg_441 H)
      (CryptoVerification.Cli.SpqrV1.Drop.Placed.blkPl_441).base (dropGluePolyEncoderSpec A))
    (hct1_sent : subroutine_ok (CryptoVerification.Cli.SpqrV1.Drop.Placed.lsProg_444 H)
      (CryptoVerification.Cli.SpqrV1.Drop.Placed.blkPl_444).base (dropUnchunkedCt1SentSpec A F)) :
    subroutine_ok (lsProg_443 H) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedSpec A F)) := by
  refine subroutine_ok_outcome_intro fun ⟨a, st⟩ R s0 hpc hrun hpre hsp => ?_
  cases st with
  | keysUnsampled s =>
    exact (CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_keysUnsampled_placed_ok
      hdealloc s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
  | keysSampled s =>
    exact (CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_keysSampled_placed_ok
      hdealloc henc s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
  | headerSent s =>
    exact (CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_headerSent_placed_ok
      hdealloc henc hdec s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
  | ct1Received s =>
    exact (CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_ct1Received_placed_ok
      hdealloc henc s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
  | ekSentCt1Received s =>
    exact (CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_ekSentCt1Received_placed_ok
      hdealloc hdec s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
  | noHeaderReceived s =>
    exact (CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_noHeaderReceived_placed_ok
      hdealloc hdec s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
  | headerReceived s =>
    exact (CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_headerReceived_placed_ok
      hdealloc hdec s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
  | ct1Sampled s =>
    exact (CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_ct1Sampled_placed_ok
      hct1_sent henc hdec s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
  | ekReceivedCt1Sampled s =>
    exact (CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_ekReceivedCt1Sampled_placed_ok
      hdealloc henc s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
  | ct1Acknowledged s =>
    exact (CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_ct1Acknowledged_placed_ok
      hct1_sent hdec s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
  | ct2Sampled s =>
    exact (CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_ct2Sampled_placed_ok
      hdealloc henc s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_placed
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {H : String → Option (State → State)}
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A)) :
    subroutine_ok (lsProg_443 H) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedSpec A F)) :=
  CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_placed_ok
    (SpqrV1.Alloc.spqr_hook_ok_of_mem hdealloc)
    (CryptoVerification.Cli.SpqrV1.Drop.drop_poly_decoder_placed hdealloc)
    (CryptoVerification.Cli.SpqrV1.Drop.drop_poly_encoder_local1_placed hdealloc)
    (CryptoVerification.Cli.SpqrV1.Drop.drop_unchunked_ct1_sent_local1_placed hdealloc)

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_placed_x
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A)) :
    subroutine_ok (lsProg_443 (Rust.withPanics ext)) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedSpec A F)) :=
  CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_placed
    (CryptoVerification.Cli.SpqrV1.Drop.hookSat_dealloc_withPanics hdealloc)

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_placed_lscl
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    [IsLsBlockProg callerProg i H]
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 443)
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedSpec A F)) :=
  ls_subroutine_ok_of_block (callerProg := callerProg)
    (CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_placed hdealloc) hi

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_placed_cl
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    [IsLsBlockProg callerProg i H]
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 443)
      (withLsCl lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedSpec A F)) :=
  ls_subroutine_ok_cl_of_block (callerProg := callerProg)
    (CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_placed hdealloc) hi

/-! ## 4. `LibsignalRoLoaded` Jump-Table-Discharged Contracts (`ro_*` / `*_ro_*`) -/

abbrev _root_.CryptoVerification.Cli.SpqrV1.Drop.withLsRoLoaded
    {α : Type} (pl : MultiPlacement) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s0 => spec.pre x s0 ∗ ⌜LibsignalRoLoaded pl s0.mem⌝ }

/-- Jump-table-free specification for `States` drop glue (`Block 443`). -/
def _root_.CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1CleanPlacedSpec
    (A : RustAlloc) (F : ShaCompress) : Spec (DropChunkedStatesGhost F) where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗
      chunkedStatesAt A x.a x.st ∗
      A.pool ∗ stackAt s.sp dropStackPoly64
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.a chunkedStatesSize ∗
      A.pool ∗ stackAt s0.sp dropStackPoly64

/-- Jump-table-discharged `[LibsignalPlacement]` specification for `States` drop glue (`Block 443`),
    requiring only `LibsignalRoLoaded lsmpl s0.mem` instead of an explicit `.rodata` jump-table atom. -/
abbrev _root_.CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1RoPlacedSpec
    [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress) : Spec (DropChunkedStatesGhost F) :=
  CryptoVerification.Cli.SpqrV1.Drop.withLsRoLoaded lsmpl
    (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1CleanPlacedSpec A F)

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.subroutine_ok_drop_states_ro_of_placed
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedSpec A F))) :
    subroutine_ok prog entry
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1RoPlacedSpec A F)) := by
  refine subroutine_ok_mono h (fun x R s0 hp => ?_) (fun x R s0 sf hq => ?_)
  · obtain ⟨hcl, hp1⟩ := extract_withLsCodeLoaded hp
    dsimp only [CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1RoPlacedSpec,
      CryptoVerification.Cli.SpqrV1.Drop.withLsRoLoaded] at hp1
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hp1
    obtain ⟨hro, hp2⟩ := hp1
    have hp3 := CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTable_lsro_cli_intro hro hp2
    dsimp only [withLsCodeLoaded,
      CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedSpec,
      CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1CleanPlacedSpec,
      CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedAt] at hp3 ⊢
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl, Satisfies.mono (Entails.of_eq (by ac_rfl)) hp3⟩
  · dsimp only [withLsCodeLoaded,
      CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1PlacedSpec,
      CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1RoPlacedSpec,
      CryptoVerification.Cli.SpqrV1.Drop.withLsRoLoaded,
      CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1CleanPlacedSpec] at hq ⊢
    have hperm : sf.mem ⊨
        CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedAt ∗
        (((⌜sf.trace = s0.trace⌝ ∗
          memRegion x.a chunkedStatesSize ∗
          A.pool ∗ stackAt s0.sp dropStackPoly64)) ∗ R) :=
      Satisfies.mono (Entails.of_eq (by ac_rfl)) hq
    exact Satisfies.of_sep_right hperm

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.ro_drop_chunked_states_local1_placed_ok
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {H : String → Option (State → State)}
    (hdealloc : subroutine_ok (lsProg_443 H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hdec : subroutine_ok (CryptoVerification.Cli.SpqrV1.Drop.Placed.lsProg_440 H)
      (CryptoVerification.Cli.SpqrV1.Drop.Placed.blkPl_440).base (dropGlueSortedSetPt16Spec A))
    (henc : subroutine_ok (CryptoVerification.Cli.SpqrV1.Drop.Placed.lsProg_441 H)
      (CryptoVerification.Cli.SpqrV1.Drop.Placed.blkPl_441).base (dropGluePolyEncoderSpec A))
    (hct1_sent : subroutine_ok (CryptoVerification.Cli.SpqrV1.Drop.Placed.lsProg_444 H)
      (CryptoVerification.Cli.SpqrV1.Drop.Placed.blkPl_444).base (dropUnchunkedCt1SentSpec A F)) :
    subroutine_ok (lsProg_443 H) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1RoPlacedSpec A F)) :=
  CryptoVerification.Cli.SpqrV1.Drop.subroutine_ok_drop_states_ro_of_placed
    (CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_placed_ok
      hdealloc hdec henc hct1_sent)

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.ro_drop_chunked_states_local1_placed
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {H : String → Option (State → State)}
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A)) :
    subroutine_ok (lsProg_443 H) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1RoPlacedSpec A F)) :=
  CryptoVerification.Cli.SpqrV1.Drop.subroutine_ok_drop_states_ro_of_placed
    (CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_placed hdealloc)

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.ro_drop_chunked_states_local1_placed_x
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A)) :
    subroutine_ok (lsProg_443 (Rust.withPanics ext)) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1RoPlacedSpec A F)) :=
  CryptoVerification.Cli.SpqrV1.Drop.ro_drop_chunked_states_local1_placed
    (CryptoVerification.Cli.SpqrV1.Drop.hookSat_dealloc_withPanics hdealloc)

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.ro_drop_chunked_states_local1_placed_lscl
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    [IsLsBlockProg callerProg i H]
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 443)
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1RoPlacedSpec A F)) :=
  ls_subroutine_ok_of_block (callerProg := callerProg)
    (CryptoVerification.Cli.SpqrV1.Drop.ro_drop_chunked_states_local1_placed hdealloc) hi

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.ro_drop_chunked_states_local1_placed_cl
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    [IsLsBlockProg callerProg i H]
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 443)
      (withLsCl lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1RoPlacedSpec A F)) :=
  ls_subroutine_ok_cl_of_block (callerProg := callerProg)
    (CryptoVerification.Cli.SpqrV1.Drop.ro_drop_chunked_states_local1_placed hdealloc) hi

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_ro_placed_ok
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {H : String → Option (State → State)}
    (hdealloc : subroutine_ok (lsProg_443 H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hdec : subroutine_ok (CryptoVerification.Cli.SpqrV1.Drop.Placed.lsProg_440 H)
      (CryptoVerification.Cli.SpqrV1.Drop.Placed.blkPl_440).base (dropGlueSortedSetPt16Spec A))
    (henc : subroutine_ok (CryptoVerification.Cli.SpqrV1.Drop.Placed.lsProg_441 H)
      (CryptoVerification.Cli.SpqrV1.Drop.Placed.blkPl_441).base (dropGluePolyEncoderSpec A))
    (hct1_sent : subroutine_ok (CryptoVerification.Cli.SpqrV1.Drop.Placed.lsProg_444 H)
      (CryptoVerification.Cli.SpqrV1.Drop.Placed.blkPl_444).base (dropUnchunkedCt1SentSpec A F)) :
    subroutine_ok (lsProg_443 H) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1RoPlacedSpec A F)) :=
  CryptoVerification.Cli.SpqrV1.Drop.ro_drop_chunked_states_local1_placed_ok
    hdealloc hdec henc hct1_sent

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_ro_placed
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {H : String → Option (State → State)}
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A)) :
    subroutine_ok (lsProg_443 H) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1RoPlacedSpec A F)) :=
  CryptoVerification.Cli.SpqrV1.Drop.ro_drop_chunked_states_local1_placed hdealloc

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_ro_placed_x
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A)) :
    subroutine_ok (lsProg_443 (Rust.withPanics ext)) (blkPl_443).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1RoPlacedSpec A F)) :=
  CryptoVerification.Cli.SpqrV1.Drop.ro_drop_chunked_states_local1_placed_x hdealloc

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_ro_placed_lscl
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    [IsLsBlockProg callerProg i H]
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 443)
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1RoPlacedSpec A F)) :=
  CryptoVerification.Cli.SpqrV1.Drop.ro_drop_chunked_states_local1_placed_lscl hdealloc hi

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_chunked_states_local1_ro_placed_cl
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    [IsLsBlockProg callerProg i H]
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 443)
      (withLsCl lsmpl
        (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1RoPlacedSpec A F)) :=
  CryptoVerification.Cli.SpqrV1.Drop.ro_drop_chunked_states_local1_placed_cl hdealloc hi

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.ro_outer_drop_chunked_states_local1_placed_lscl
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    [IsLsBlockProg callerProg i H]
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 443)
      (CryptoVerification.Cli.SpqrV1.Drop.withLsRoLoaded lsmpl
        (withLsCodeLoaded lsmpl
          (CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1CleanPlacedSpec A F))) := by
  refine subroutine_ok_mono
    (CryptoVerification.Cli.SpqrV1.Drop.ro_drop_chunked_states_local1_placed_lscl hdealloc hi)
    (fun _ _ _ hp => Satisfies.mono (Entails.of_eq (by
      dsimp only [withLsCodeLoaded, CryptoVerification.Cli.SpqrV1.Drop.dropChunkedStatesLocal1RoPlacedSpec,
        CryptoVerification.Cli.SpqrV1.Drop.withLsRoLoaded]
      ac_rfl)) hp)
    (fun _ _ _ _ hq => hq)

end CryptoVerification.SpqrV1.Drop
