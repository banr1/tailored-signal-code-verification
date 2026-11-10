/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Drop.States1a
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Drop.PolyDecoder
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Drop Glue for `spqr::v1::chunked::states::States [local#1]` (`0x35a6c`, Part 2)

**Checked by Lean.**

Proves the remaining five variant theorems (`ct2Sampled`, `headerSent`, `ct1Received`,
`keysSampled`, `ekReceivedCt1Sampled`), the fixed-image contract
`drop_chunked_states_local1_ok_ext` (`0x35a6c`, 181 instructions), and the relocatable
`[LibsignalPlacement]` contract `drop_chunked_states_local1_placed_ok` (Block `140`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Drop

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Layout.L28

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Per-Variant Proofs for `0x35a6c` (Remaining Five Variants) -/

set_option hygiene false

local macro "states1_ct2Sampled_steps " entry:term:max jtExp:term:max : tactic => `(tactic| (
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  refine SepWP.focus_weaken (unchunkedCt2Sent408_entails_dealloc A a st.uc) (by sep_focus) ?_
  wp_pull_exists; rename_i g
  dsimp only [twoVec408HeadersAt, vecCapPtrDealloc]
  nth_rw 1 [stackAt_dropStackPoly64_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x20 v_x19
  have hsplit32 := stackAt_dropStack32_split_sub32 s0.sp
  refine SepWP.focus_weaken (Entails.of_eq hsplit32) (by sep_focus) ?_
  refine seq_clean (mid := $entry + 580#64)
    (P_mid := ((a ↦₆₄ 12#64) ∗
      polyEncoderAt A (a + 8#64) st.sending_ct2 ∗
      ((a + 408#64) ↦₆₄ g.v1.cap) ∗ ((a + 416#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 424#64) 8 ∗
      ((a + 432#64) ↦₆₄ g.v2.cap) ∗ ((a + 440#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 448#64) 16 ∗
      (if (g.v2.cap == 0#64) = true then emp
       else A.live g.v2.ptr g.v2.cap.toNat 1 ∗ memRegion g.v2.ptr g.v2.cap.toNat) ∗
      memRegion (a + 464#64) 464) ∗
      $jtExp ∗
      A.pool ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
    (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · wp_steps
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
    · wp_steps; wp_apply
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine seq_clean (mid := $entry + 696#64)
      (P_mid := ((a ↦₆₄ 12#64) ∗
        polyEncoderAt A (a + 8#64) st.sending_ct2 ∗
        memRegion (a + 408#64) 56 ∗
        memRegion (a + 464#64) 464) ∗
        $jtExp ∗
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
        refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
      · wp_steps; wp_apply
        refine SepWP.focus_weaken hhdr56 (by sep_focus) ?_
        have hsp_eq : stackAt s1.sp allocHookStack = stackAt (s0.sp - 32#64) allocHookStack := by rw [hsp_1]
        refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
        refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
        refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      dsimp only [chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]
      wp_steps
      refine SepWP.focus_weaken
        (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x19) v_x19)
        (by sep_focus) ?_
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
      wp_call henc_raw ⟨a + 8#64, st.sending_ct2⟩
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
      wp_done))

/-- Variant `ct2Sampled` (`tag = 12#64`, `b.hi` -> `+560` -> dealloc 2 Vecs -> `+696` tail-call `0x357b4`). -/
theorem drop_chunked_states_local1_ct2Sampled {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (st : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name)
      (dropChunkedStatesLocal1VariantSpec A b (.ct2Sampled st)) := by
  simp only [dropChunkedStatesLocal1VariantSpec]
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]" "__rustc::__rust_dealloc"))
      (b := b) (X := Rust.withPanics ext)
      dropChunkedStatesLocal1_fnOff (ls_stub% "__rustc::__rust_dealloc") (by decide))
    hdealloc
  have henc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name +
        bv% (2 ^ 64 - (ls_rel% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#1]" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]")))
      (dropGluePolyEncoderSpec A) := by
    have hrel : (dropProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name =
        (dropProgAtExt b ext).fnAddr dropPolyEncoderLocal1Name +
          BitVec.ofNat 64 (num% (ls_rel% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#1]" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]")) :=
      Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#1]" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]"))
        (b := b) (X := Rust.withPanics ext)
        (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#1]") dropChunkedStatesLocal1_fnOff (by decide)
    refine sub_ok_of_addr_eq ?_ (drop_glue_poly_encoder_local1_ok_ext hdealloc)
    rw [hrel, BitVec.add_assoc]; simp
  simp only [rustDeallocSpec] at hdealloc_raw
  code_fetches_sym libsignalSessionCode spqrDropTopBin b
    (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]" 724
  dsimp only [dropProgAtExt, dropChunkedStatesLocal1Name, dropGluePolyEncoderSpec,
    chunkedStatesAt, chunkedCt2SampledAt, chunkedStatesLocal1JumpTableAt,
    chunkedStatesLocal1JumpTableBytes, chunkedStatesSize, polyEncoderSize, dropGluePoly16Stack,
    spqrPolyApi, BitVec.ofNat_eq_ofNat] at hdealloc_raw henc_raw ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]" = entry
  examples_hide_fetches; wp_init a s0
  states1_ct2Sampled_steps entry (chunkedStatesLocal1JumpTableExpanded b)

local macro "states1_headerSent_steps " entry:term:max jtExp:term:max : tactic => `(tactic| (
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
  refine seq_clean (mid := $entry + 332#64)
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
      $jtExp ∗
      A.pool ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
    (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · wp_steps
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
    · wp_steps; wp_apply
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine seq_clean (mid := $entry + 352#64)
      (P_mid := ((a ↦₆₄ 4#64) ∗
        polyEncoderAt A (a + 8#64) st.sending_ek ∗
        ((a + 408#64) ↦₆₄ g.v1.cap) ∗ ((a + 416#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 424#64) 8 ∗
        ((a + 432#64) ↦₆₄ g.v2.cap) ∗ ((a + 440#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 448#64) 8 ∗
        ((a + 456#64) ↦₆₄ g.v3.cap) ∗ ((a + 464#64) ↦₆₄ g.v3.ptr) ∗ memRegion (a + 472#64) 16 ∗
        (if (g.v3.cap == 0#64) = true then emp
         else A.live g.v3.ptr g.v3.cap.toNat 1 ∗ memRegion g.v3.ptr g.v3.cap.toNat) ∗
        vecPtListOf A (a + 488#64) vecs ∗ memRegion (a + 872#64) 16 ∗
        memRegion (a + 888#64) 40) ∗
        $jtExp ∗
        A.pool ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
      (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
      ?_ ?_
    · by_cases hc2 : (g.v2.cap == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
      · wp_steps
        refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
      · wp_steps; wp_apply
        refine align_pre (by rw [hsp_1]; simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      refine seq_clean (mid := $entry + 372#64)
        (P_mid := ((a ↦₆₄ 4#64) ∗
          polyEncoderAt A (a + 8#64) st.sending_ek ∗
          memRegion (a + 408#64) 80 ∗
          vecPtListOf A (a + 488#64) vecs ∗ memRegion (a + 872#64) 16 ∗
          memRegion (a + 888#64) 40) ∗
          $jtExp ∗
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
          refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
        · wp_steps; wp_apply
          refine SepWP.focus_weaken hhdr80 (by sep_focus) ?_
          have hsp_eq : stackAt s2.sp allocHookStack = stackAt (s0.sp - 32#64) allocHookStack := by rw [hsp_2]
          refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
          refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
          refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
      · intro s3 hpc3 hrun3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
        dsimp only [chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]
        wp_steps
        wp_call henc_raw ⟨a + 8#64, st.sending_ek⟩
        wp_steps
        have hsp_eq : stackAt s3.sp dropStack32 = stackAt (s0.sp - 32#64) dropStack32 := by
          rw [hsp_3]
        refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
        refine SepWP.focus_weaken
          (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x19) v_x19)
          (by sep_focus) ?_
        refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
        wp_call hdec_raw ⟨a + 488#64, vecs⟩
        refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp).symm) (by sep_focus) ?_
        have hjoin488 : memRegion (a + 488#64) 384 ∗ memRegion (a + 872#64) 16 ⊢
            memRegion (a + 488#64) polyDecoderSize := by
          have h872 : a + 872#64 = (a + 488#64) + 384#64 := (BitVec.add_assoc a 488#64 384#64).symm
          rw [h872]
          exact polyDecoder_post_join (a + 488#64)
        refine SepWP.focus_weaken hjoin488 (by sep_focus) ?_
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
        wp_done))

/-- Variant `headerSent` (`tag = 4#64`, jump index `2` -> `+312`). -/
theorem drop_chunked_states_local1_headerSent {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name)
      (dropChunkedStatesLocal1VariantSpec A b (.headerSent st)) := by
  simp only [dropChunkedStatesLocal1VariantSpec]
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]" "__rustc::__rust_dealloc"))
      (b := b) (X := Rust.withPanics ext)
      dropChunkedStatesLocal1_fnOff (ls_stub% "__rustc::__rust_dealloc") (by decide))
    hdealloc
  have henc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name +
        bv% (2 ^ 64 - (ls_rel% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#1]" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]")))
      (dropGluePolyEncoderSpec A) := by
    have hrel : (dropProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name =
        (dropProgAtExt b ext).fnAddr dropPolyEncoderLocal1Name +
          BitVec.ofNat 64 (num% (ls_rel% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#1]" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]")) :=
      Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#1]" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]"))
        (b := b) (X := Rust.withPanics ext)
        (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#1]") dropChunkedStatesLocal1_fnOff (by decide)
    refine sub_ok_of_addr_eq ?_ (drop_glue_poly_encoder_local1_ok_ext hdealloc)
    rw [hrel, BitVec.add_assoc]; simp
  have hdec_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name +
        bv% (2 ^ 64 - (ls_rel% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyDecoder> [local#1]" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]")))
      (dropGlueSortedSetPt16Spec A) := by
    have hrel : (dropProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name =
        (dropProgAtExt b ext).fnAddr dropPolyDecoderName +
          BitVec.ofNat 64 (num% (ls_rel% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyDecoder> [local#1]" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]")) :=
      Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyDecoder> [local#1]" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]"))
        (b := b) (X := Rust.withPanics ext)
        (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyDecoder> [local#1]") dropChunkedStatesLocal1_fnOff (by decide)
    refine sub_ok_of_addr_eq ?_ (drop_glue_poly_decoder_ok_ext hdealloc)
    rw [hrel, BitVec.add_assoc]; simp
  have hadrp : ∀ (hb : b &&& 0xfff#64 = 0#64),
      (((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr dropChunkedStatesLocal1Name + 44#64) &&&
        0xfffffffffffff000#64) = b + bv% (page% ((ls_off% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]") + 44)) := fnAddr_adrp_35a98
  simp only [rustDeallocSpec] at hdealloc_raw
  code_fetches_sym libsignalSessionCode spqrDropTopBin b
    (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]" 724
  dsimp only [dropProgAtExt, dropChunkedStatesLocal1Name, dropGluePolyEncoderSpec,
    dropGlueSortedSetPt16Spec, chunkedStatesAt, chunkedHeaderSentAt,
    chunkedStatesLocal1JumpTableAt, chunkedStatesLocal1JumpTableBytes,
    chunkedStatesSize, polyEncoderSize, polyArrayBytes, dropGluePoly16Stack,
    spqrPolyApi, BitVec.ofNat_eq_ofNat] at hdealloc_raw henc_raw hdec_raw hadrp ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]" = entry
  examples_hide_fetches; wp_init a s0; have hadrp' := hadrp h
  states1_headerSent_steps entry (chunkedStatesLocal1JumpTableExpanded b)

local macro "states1_ct1Received_steps " entry:term:max jtExp:term:max : tactic => `(tactic| (
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  refine SepWP.focus_weaken (unchunkedEkSentCt1Received408_entails_dealloc A a st.uc) (by sep_focus) ?_
  wp_pull_exists; rename_i g
  dsimp only [fourVec408HeadersAt, vecCapPtrDealloc]
  nth_rw 1 [stackAt_dropStackPoly64_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x20 v_x19
  have hsplit32 := stackAt_dropStack32_split_sub32 s0.sp
  refine SepWP.focus_weaken (Entails.of_eq hsplit32) (by sep_focus) ?_
  refine seq_clean (mid := $entry + 88#64)
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
      $jtExp ∗
      A.pool ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
    (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · wp_steps
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
    · wp_steps; wp_apply
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine seq_clean (mid := $entry + 108#64)
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
        $jtExp ∗
        A.pool ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
      (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
      ?_ ?_
    · by_cases hc2 : (g.v2.cap == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
      · wp_steps
        refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
      · wp_steps; wp_apply
        refine align_pre (by rw [hsp_1]; simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      refine seq_clean (mid := $entry + 128#64)
        (P_mid := ((a ↦₆₄ 5#64) ∗
          polyEncoderAt A (a + 8#64) st.sending_ek ∗
          ((a + 408#64) ↦₆₄ g.v1.cap) ∗ ((a + 416#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 424#64) 8 ∗
          ((a + 432#64) ↦₆₄ g.v2.cap) ∗ ((a + 440#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 448#64) 8 ∗
          ((a + 456#64) ↦₆₄ g.v3.cap) ∗ ((a + 464#64) ↦₆₄ g.v3.ptr) ∗ memRegion (a + 472#64) 8 ∗
          ((a + 480#64) ↦₆₄ g.v4.cap) ∗ ((a + 488#64) ↦₆₄ g.v4.ptr) ∗ memRegion (a + 496#64) 16 ∗
          (if (g.v4.cap == 0#64) = true then emp
           else A.live g.v4.ptr g.v4.cap.toNat 1 ∗ memRegion g.v4.ptr g.v4.cap.toNat) ∗
          memRegion (a + 512#64) 416) ∗
          $jtExp ∗
          A.pool ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
          (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
        (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
        ?_ ?_
      · by_cases hc3 : (g.v3.cap == 0#64) = true <;>
          simp only [hc3, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
        · wp_steps
          refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
        · wp_steps; wp_apply
          refine align_pre (by rw [hsp_2]; simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
      · intro s3 hpc3 hrun3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
        refine seq_clean (mid := $entry + 696#64)
          (P_mid := ((a ↦₆₄ 5#64) ∗
            polyEncoderAt A (a + 8#64) st.sending_ek ∗
            memRegion (a + 408#64) 104 ∗
            memRegion (a + 512#64) 416) ∗
            $jtExp ∗
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
            refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
          · wp_steps; wp_apply
            refine SepWP.focus_weaken hhdr104 (by sep_focus) ?_
            have hsp_eq : stackAt s3.sp allocHookStack = stackAt (s0.sp - 32#64) allocHookStack := by rw [hsp_3]
            refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
            refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
            refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
        · intro s4 hpc4 hrun4 ⟨⟨hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hx19_4⟩
          dsimp only [chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]
          wp_steps
          refine SepWP.focus_weaken
            (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
              (s0.readReg64 .x19) v_x19)
            (by sep_focus) ?_
          refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
          wp_call henc_raw ⟨a + 8#64, st.sending_ek⟩
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
          wp_done))

/-- Variant `ct1Received` (`tag = 5#64`, jump index `3` -> `+68` -> dealloc 4 Vecs -> `+696` tail-call `0x357b4`). -/
theorem drop_chunked_states_local1_ct1Received {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name)
      (dropChunkedStatesLocal1VariantSpec A b (.ct1Received st)) := by
  simp only [dropChunkedStatesLocal1VariantSpec]
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]" "__rustc::__rust_dealloc"))
      (b := b) (X := Rust.withPanics ext)
      dropChunkedStatesLocal1_fnOff (ls_stub% "__rustc::__rust_dealloc") (by decide))
    hdealloc
  have henc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name +
        bv% (2 ^ 64 - (ls_rel% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#1]" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]")))
      (dropGluePolyEncoderSpec A) := by
    have hrel : (dropProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name =
        (dropProgAtExt b ext).fnAddr dropPolyEncoderLocal1Name +
          BitVec.ofNat 64 (num% (ls_rel% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#1]" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]")) :=
      Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#1]" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]"))
        (b := b) (X := Rust.withPanics ext)
        (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#1]") dropChunkedStatesLocal1_fnOff (by decide)
    refine sub_ok_of_addr_eq ?_ (drop_glue_poly_encoder_local1_ok_ext hdealloc)
    rw [hrel, BitVec.add_assoc]; simp
  have hadrp : ∀ (hb : b &&& 0xfff#64 = 0#64),
      (((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr dropChunkedStatesLocal1Name + 44#64) &&&
        0xfffffffffffff000#64) = b + bv% (page% ((ls_off% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]") + 44)) := fnAddr_adrp_35a98
  simp only [rustDeallocSpec] at hdealloc_raw
  code_fetches_sym libsignalSessionCode spqrDropTopBin b
    (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]" 724
  dsimp only [dropProgAtExt, dropChunkedStatesLocal1Name, dropGluePolyEncoderSpec,
    chunkedStatesAt, chunkedCt1ReceivedAt, chunkedStatesLocal1JumpTableAt,
    chunkedStatesLocal1JumpTableBytes, chunkedStatesSize, polyEncoderSize, dropGluePoly16Stack,
    spqrPolyApi, BitVec.ofNat_eq_ofNat] at hdealloc_raw henc_raw hadrp ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]" = entry
  examples_hide_fetches; wp_init a s0; have hadrp' := hadrp h
  states1_ct1Received_steps entry (chunkedStatesLocal1JumpTableExpanded b)

local macro "states1_keysSampled_steps " entry:term:max jtExp:term:max : tactic => `(tactic| (
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
  refine seq_clean (mid := $entry + 88#64)
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
      $jtExp ∗
      A.pool ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
    (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · wp_steps
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
    · wp_steps; wp_apply
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine seq_clean (mid := $entry + 108#64)
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
        $jtExp ∗
        A.pool ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
      (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
      ?_ ?_
    · by_cases hc2 : (g.v2.cap == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
      · wp_steps
        refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
      · wp_steps; wp_apply
        refine align_pre (by rw [hsp_1]; simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      refine seq_clean (mid := $entry + 128#64)
        (P_mid := ((a ↦₆₄ 3#64) ∗
          polyEncoderAt A (a + 8#64) st.sending_hdr ∗
          ((a + 408#64) ↦₆₄ g.v1.cap) ∗ ((a + 416#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 424#64) 8 ∗
          ((a + 432#64) ↦₆₄ g.v2.cap) ∗ ((a + 440#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 448#64) 8 ∗
          ((a + 456#64) ↦₆₄ g.v3.cap) ∗ ((a + 464#64) ↦₆₄ g.v3.ptr) ∗ memRegion (a + 472#64) 8 ∗
          ((a + 480#64) ↦₆₄ g.v4.cap) ∗ ((a + 488#64) ↦₆₄ g.v4.ptr) ∗ memRegion (a + 496#64) 16 ∗
          (if (g.v4.cap == 0#64) = true then emp
           else A.live g.v4.ptr g.v4.cap.toNat 1 ∗ memRegion g.v4.ptr g.v4.cap.toNat) ∗
          memRegion (a + 512#64) 416) ∗
          $jtExp ∗
          A.pool ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
          (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
        (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
        ?_ ?_
      · by_cases hc3 : (g.v3.cap == 0#64) = true <;>
          simp only [hc3, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
        · wp_steps
          refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
        · wp_steps; wp_apply
          refine align_pre (by rw [hsp_2]; simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
      · intro s3 hpc3 hrun3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
        refine seq_clean (mid := $entry + 696#64)
          (P_mid := ((a ↦₆₄ 3#64) ∗
            polyEncoderAt A (a + 8#64) st.sending_hdr ∗
            memRegion (a + 408#64) 104 ∗
            memRegion (a + 512#64) 416) ∗
            $jtExp ∗
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
            refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
          · wp_steps; wp_apply
            refine SepWP.focus_weaken hhdr104 (by sep_focus) ?_
            have hsp_eq : stackAt s3.sp allocHookStack = stackAt (s0.sp - 32#64) allocHookStack := by rw [hsp_3]
            refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
            refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
            refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
        · intro s4 hpc4 hrun4 ⟨⟨hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hx19_4⟩
          dsimp only [chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]
          wp_steps
          refine SepWP.focus_weaken
            (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
              (s0.readReg64 .x19) v_x19)
            (by sep_focus) ?_
          refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
          wp_call henc_raw ⟨a + 8#64, st.sending_hdr⟩
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
          wp_done))

/-- Variant `keysSampled` (`tag = 3#64`, jump index `1` -> `+68` -> dealloc 4 Vecs -> `+696` tail-call `0x357b4`). -/
theorem drop_chunked_states_local1_keysSampled {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name)
      (dropChunkedStatesLocal1VariantSpec A b (.keysSampled st)) := by
  simp only [dropChunkedStatesLocal1VariantSpec]
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]" "__rustc::__rust_dealloc"))
      (b := b) (X := Rust.withPanics ext)
      dropChunkedStatesLocal1_fnOff (ls_stub% "__rustc::__rust_dealloc") (by decide))
    hdealloc
  have henc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name +
        bv% (2 ^ 64 - (ls_rel% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#1]" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]")))
      (dropGluePolyEncoderSpec A) := by
    have hrel : (dropProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name =
        (dropProgAtExt b ext).fnAddr dropPolyEncoderLocal1Name +
          BitVec.ofNat 64 (num% (ls_rel% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#1]" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]")) :=
      Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#1]" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]"))
        (b := b) (X := Rust.withPanics ext)
        (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#1]") dropChunkedStatesLocal1_fnOff (by decide)
    refine sub_ok_of_addr_eq ?_ (drop_glue_poly_encoder_local1_ok_ext hdealloc)
    rw [hrel, BitVec.add_assoc]; simp
  have hadrp : ∀ (hb : b &&& 0xfff#64 = 0#64),
      (((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr dropChunkedStatesLocal1Name + 44#64) &&&
        0xfffffffffffff000#64) = b + bv% (page% ((ls_off% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]") + 44)) := fnAddr_adrp_35a98
  simp only [rustDeallocSpec] at hdealloc_raw
  code_fetches_sym libsignalSessionCode spqrDropTopBin b
    (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]" 724
  dsimp only [dropProgAtExt, dropChunkedStatesLocal1Name, dropGluePolyEncoderSpec,
    chunkedStatesAt, chunkedKeysSampledAt, chunkedStatesLocal1JumpTableAt,
    chunkedStatesLocal1JumpTableBytes, chunkedStatesSize, polyEncoderSize, dropGluePoly16Stack,
    spqrPolyApi, BitVec.ofNat_eq_ofNat] at hdealloc_raw henc_raw hadrp ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]" = entry
  examples_hide_fetches; wp_init a s0; have hadrp' := hadrp h
  states1_keysSampled_steps entry (chunkedStatesLocal1JumpTableExpanded b)

local macro "states1_ekReceivedCt1Sampled_steps " entry:term:max jtExp:term:max : tactic => `(tactic| (
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
  refine seq_clean (mid := $entry + 616#64)
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
      $jtExp ∗
      A.pool ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
    (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · wp_steps
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
    · wp_steps; wp_apply
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine seq_clean (mid := $entry + 636#64)
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
        $jtExp ∗
        A.pool ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
      (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
      ?_ ?_
    · by_cases hc2 : (g.v2.cap == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
      · wp_steps
        refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
      · wp_steps; wp_apply
        refine align_pre (by rw [hsp_1]; simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      refine seq_clean (mid := $entry + 656#64)
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
          $jtExp ∗
          A.pool ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
          (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
        (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
        ?_ ?_
      · by_cases hc3 : (g.v3.cap == 0#64) = true <;>
          simp only [hc3, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
        · wp_steps
          refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
        · wp_steps; wp_apply
          refine align_pre (by rw [hsp_2]; simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
      · intro s3 hpc3 hrun3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
        refine seq_clean (mid := $entry + 676#64)
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
            $jtExp ∗
            A.pool ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
            (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19)))
          (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
          ?_ ?_
        · by_cases hc4 : (g.v4.cap == 0#64) = true <;>
            simp only [hc4, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
          · wp_steps
            refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
          · wp_steps; wp_apply
            refine align_pre (by rw [hsp_3]; simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
        · intro s4 hpc4 hrun4 ⟨⟨hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hx19_4⟩
          refine seq_clean (mid := $entry + 696#64)
            (P_mid := ((a ↦₆₄ 10#64) ∗
              polyEncoderAt A (a + 8#64) st.sending_ct1 ∗
              memRegion (a + 408#64) 128 ∗
              memRegion (a + 536#64) 392) ∗
              $jtExp ∗
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
              refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
            · wp_steps; wp_apply
              refine SepWP.focus_weaken hhdr128 (by sep_focus) ?_
              have hsp_eq : stackAt s4.sp allocHookStack = stackAt (s0.sp - 32#64) allocHookStack := by rw [hsp_4]
              refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
              refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
              refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]; try ac_rfl) ?_; wp_done
          · intro s5 hpc5 hrun5 ⟨⟨hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hsp_5, htrace_5, hvregs_5⟩, hx19_5⟩
            dsimp only [chunkedStatesLocal1JumpTableExpanded, chunkedStatesLocal1JumpTablePlacedExpanded]
            wp_steps
            refine SepWP.focus_weaken
              (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
                (s0.readReg64 .x19) v_x19)
              (by sep_focus) ?_
            refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
            wp_call henc_raw ⟨a + 8#64, st.sending_ct1⟩
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
            wp_done))

/-- Variant `ekReceivedCt1Sampled` (`tag = 10#64`, jump index `8` -> `+596` -> dealloc 5 Vecs -> `+696` tail-call `0x357b4`). -/
theorem drop_chunked_states_local1_ekReceivedCt1Sampled {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (st : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name)
      (dropChunkedStatesLocal1VariantSpec A b (.ekReceivedCt1Sampled st)) := by
  simp only [dropChunkedStatesLocal1VariantSpec]
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]" "__rustc::__rust_dealloc"))
      (b := b) (X := Rust.withPanics ext)
      dropChunkedStatesLocal1_fnOff (ls_stub% "__rustc::__rust_dealloc") (by decide))
    hdealloc
  have henc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name +
        bv% (2 ^ 64 - (ls_rel% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#1]" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]")))
      (dropGluePolyEncoderSpec A) := by
    have hrel : (dropProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name =
        (dropProgAtExt b ext).fnAddr dropPolyEncoderLocal1Name +
          BitVec.ofNat 64 (num% (ls_rel% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#1]" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]")) :=
      Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#1]" "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]"))
        (b := b) (X := Rust.withPanics ext)
        (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#1]") dropChunkedStatesLocal1_fnOff (by decide)
    refine sub_ok_of_addr_eq ?_ (drop_glue_poly_encoder_local1_ok_ext hdealloc)
    rw [hrel, BitVec.add_assoc]; simp
  have hadrp : ∀ (hb : b &&& 0xfff#64 = 0#64),
      (((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr dropChunkedStatesLocal1Name + 44#64) &&&
        0xfffffffffffff000#64) = b + bv% (page% ((ls_off% "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]") + 44)) := fnAddr_adrp_35a98
  simp only [rustDeallocSpec] at hdealloc_raw
  code_fetches_sym libsignalSessionCode spqrDropTopBin b
    (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]" 724
  dsimp only [dropProgAtExt, dropChunkedStatesLocal1Name, dropGluePolyEncoderSpec,
    chunkedStatesAt, chunkedEkReceivedCt1SampledAt, chunkedStatesLocal1JumpTableAt,
    chunkedStatesLocal1JumpTableBytes, chunkedStatesSize, polyEncoderSize, dropGluePoly16Stack,
    spqrPolyApi, BitVec.ofNat_eq_ofNat] at hdealloc_raw henc_raw hadrp ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]" = entry
  examples_hide_fetches; wp_init a s0; have hadrp' := hadrp h
  states1_ekReceivedCt1Sampled_steps entry (chunkedStatesLocal1JumpTableExpanded b)

/-! ## Top-Level Proof of `0x35a6c` (`drop_chunked_states_local1_ok_ext`) -/

theorem drop_chunked_states_local1_ok_ext {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropChunkedStatesLocal1Name)
      (dropChunkedStatesLocal1Spec A F b) := by
  refine subroutine_ok_outcome_intro fun ⟨a, st⟩ R s0 hpc hrun hpre hsp => ?_
  cases st with
  | keysUnsampled s =>
    exact (drop_chunked_states_local1_keysUnsampled hdealloc s).mono_outcome
      a R s0 hpc hrun hpre hsp fun _ hout => hout
  | keysSampled s =>
    exact (drop_chunked_states_local1_keysSampled hdealloc s).mono_outcome
      a R s0 hpc hrun hpre hsp fun _ hout => hout
  | headerSent s =>
    exact (drop_chunked_states_local1_headerSent hdealloc s).mono_outcome
      a R s0 hpc hrun hpre hsp fun _ hout => hout
  | ct1Received s =>
    exact (drop_chunked_states_local1_ct1Received hdealloc s).mono_outcome
      a R s0 hpc hrun hpre hsp fun _ hout => hout
  | ekSentCt1Received s =>
    exact (drop_chunked_states_local1_ekSentCt1Received hdealloc s).mono_outcome
      a R s0 hpc hrun hpre hsp fun _ hout => hout
  | noHeaderReceived s =>
    exact (drop_chunked_states_local1_noHeaderReceived hdealloc s).mono_outcome
      a R s0 hpc hrun hpre hsp fun _ hout => hout
  | headerReceived s =>
    exact (drop_chunked_states_local1_headerReceived hdealloc s).mono_outcome
      a R s0 hpc hrun hpre hsp fun _ hout => hout
  | ct1Sampled s =>
    exact (drop_chunked_states_local1_ct1Sampled hdealloc s).mono_outcome
      a R s0 hpc hrun hpre hsp fun _ hout => hout
  | ekReceivedCt1Sampled s =>
    exact (drop_chunked_states_local1_ekReceivedCt1Sampled hdealloc s).mono_outcome
      a R s0 hpc hrun hpre hsp fun _ hout => hout
  | ct1Acknowledged s =>
    exact (drop_chunked_states_local1_ct1Acknowledged hdealloc s).mono_outcome
      a R s0 hpc hrun hpre hsp fun _ hout => hout
  | ct2Sampled s =>
    exact (drop_chunked_states_local1_ct2Sampled hdealloc s).mono_outcome
      a R s0 hpc hrun hpre hsp fun _ hout => hout

/-! ## Relocatable `[LibsignalPlacement]` Proof of Block `140` -/

section PlacedStates1
variable [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {H : String → Option (State → State)}

theorem drop_chunked_states_local1_ct2Sampled_placed
    (hdealloc : subroutine_ok ((blkPC_140).rebase (blkPl_140).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (henc_raw : subroutine_ok ((blkPC_140).rebase (blkPl_140).base H) (lsmpl.base 138) (dropGluePolyEncoderSpec A))
    (st : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_140).rebase (blkPl_140).base H) (blkPl_140).base
      (dropChunkedStatesLocal1PlacedVariantSpec A (.ct2Sampled st)) := by
  simp only [dropChunkedStatesLocal1PlacedVariantSpec]
  have hdealloc_raw := hdealloc; simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [dropGluePolyEncoderSpec, chunkedStatesAt, chunkedCt2SampledAt,
    chunkedStatesLocal1JumpTablePlacedAt, chunkedStatesLocal1JumpTableBytes,
    chunkedStatesSize, polyEncoderSize, dropGluePoly16Stack, spqrPolyApi] at hdealloc_raw henc_raw ⊢
  wp_init a s0; states1_ct2Sampled_steps (blkPl_140).base chunkedStatesLocal1JumpTablePlacedExpanded

theorem drop_chunked_states_local1_headerSent_placed
    (hdealloc : subroutine_ok ((blkPC_140).rebase (blkPl_140).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (henc_raw : subroutine_ok ((blkPC_140).rebase (blkPl_140).base H) (lsmpl.base 138) (dropGluePolyEncoderSpec A))
    (hdec_raw : subroutine_ok ((blkPC_140).rebase (blkPl_140).base H) (lsmpl.base 137) (dropGlueSortedSetPt16Spec A))
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_140).rebase (blkPl_140).base H) (blkPl_140).base
      (dropChunkedStatesLocal1PlacedVariantSpec A (.headerSent st)) := by
  simp only [dropChunkedStatesLocal1PlacedVariantSpec]
  have hdealloc_raw := hdealloc; simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [dropGluePolyEncoderSpec, dropGlueSortedSetPt16Spec, chunkedStatesAt, chunkedHeaderSentAt,
    chunkedStatesLocal1JumpTablePlacedAt, chunkedStatesLocal1JumpTableBytes,
    chunkedStatesSize, polyEncoderSize, polyArrayBytes, dropGluePoly16Stack, spqrPolyApi] at hdealloc_raw henc_raw hdec_raw ⊢
  wp_init a s0; states1_headerSent_steps (blkPl_140).base chunkedStatesLocal1JumpTablePlacedExpanded

theorem drop_chunked_states_local1_ct1Received_placed
    (hdealloc : subroutine_ok ((blkPC_140).rebase (blkPl_140).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (henc_raw : subroutine_ok ((blkPC_140).rebase (blkPl_140).base H) (lsmpl.base 138) (dropGluePolyEncoderSpec A))
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_140).rebase (blkPl_140).base H) (blkPl_140).base
      (dropChunkedStatesLocal1PlacedVariantSpec A (.ct1Received st)) := by
  simp only [dropChunkedStatesLocal1PlacedVariantSpec]
  have hdealloc_raw := hdealloc; simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [dropGluePolyEncoderSpec, chunkedStatesAt, chunkedCt1ReceivedAt,
    chunkedStatesLocal1JumpTablePlacedAt, chunkedStatesLocal1JumpTableBytes,
    chunkedStatesSize, polyEncoderSize, dropGluePoly16Stack, spqrPolyApi] at hdealloc_raw henc_raw ⊢
  wp_init a s0; states1_ct1Received_steps (blkPl_140).base chunkedStatesLocal1JumpTablePlacedExpanded

theorem drop_chunked_states_local1_keysSampled_placed
    (hdealloc : subroutine_ok ((blkPC_140).rebase (blkPl_140).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (henc_raw : subroutine_ok ((blkPC_140).rebase (blkPl_140).base H) (lsmpl.base 138) (dropGluePolyEncoderSpec A))
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_140).rebase (blkPl_140).base H) (blkPl_140).base
      (dropChunkedStatesLocal1PlacedVariantSpec A (.keysSampled st)) := by
  simp only [dropChunkedStatesLocal1PlacedVariantSpec]
  have hdealloc_raw := hdealloc; simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [dropGluePolyEncoderSpec, chunkedStatesAt, chunkedKeysSampledAt,
    chunkedStatesLocal1JumpTablePlacedAt, chunkedStatesLocal1JumpTableBytes,
    chunkedStatesSize, polyEncoderSize, dropGluePoly16Stack, spqrPolyApi] at hdealloc_raw henc_raw ⊢
  wp_init a s0; states1_keysSampled_steps (blkPl_140).base chunkedStatesLocal1JumpTablePlacedExpanded

theorem drop_chunked_states_local1_ekReceivedCt1Sampled_placed
    (hdealloc : subroutine_ok ((blkPC_140).rebase (blkPl_140).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (henc_raw : subroutine_ok ((blkPC_140).rebase (blkPl_140).base H) (lsmpl.base 138) (dropGluePolyEncoderSpec A))
    (st : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_140).rebase (blkPl_140).base H) (blkPl_140).base
      (dropChunkedStatesLocal1PlacedVariantSpec A (.ekReceivedCt1Sampled st)) := by
  simp only [dropChunkedStatesLocal1PlacedVariantSpec]
  have hdealloc_raw := hdealloc; simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [dropGluePolyEncoderSpec, chunkedStatesAt, chunkedEkReceivedCt1SampledAt,
    chunkedStatesLocal1JumpTablePlacedAt, chunkedStatesLocal1JumpTableBytes,
    chunkedStatesSize, polyEncoderSize, dropGluePoly16Stack, spqrPolyApi] at hdealloc_raw henc_raw ⊢
  wp_init a s0; states1_ekReceivedCt1Sampled_steps (blkPl_140).base chunkedStatesLocal1JumpTablePlacedExpanded

theorem drop_chunked_states_local1_placed_ok
    (hdealloc : subroutine_ok ((blkPC_140).rebase (blkPl_140).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hdec : subroutine_ok ((blkPC_140).rebase (blkPl_140).base H) (lsmpl.base 137) (dropGlueSortedSetPt16Spec A))
    (henc : subroutine_ok ((blkPC_140).rebase (blkPl_140).base H) (lsmpl.base 138) (dropGluePolyEncoderSpec A))
    (hct1_sent : subroutine_ok ((blkPC_140).rebase (blkPl_140).base H) (lsmpl.base 141) (dropUnchunkedCt1SentSpec A F)) :
    subroutine_ok ((blkPC_140).rebase (blkPl_140).base H) (blkPl_140).base
      (dropChunkedStatesLocal1PlacedSpec A F) := by
  refine subroutine_ok_outcome_intro fun ⟨a, st⟩ R s0 hpc hrun hpre hsp => ?_
  cases st with
  | keysUnsampled s =>
    exact (drop_chunked_states_local1_keysUnsampled_placed hdealloc s).mono_outcome
      a R s0 hpc hrun hpre hsp fun _ hout => hout
  | keysSampled s =>
    exact (drop_chunked_states_local1_keysSampled_placed hdealloc henc s).mono_outcome
      a R s0 hpc hrun hpre hsp fun _ hout => hout
  | headerSent s =>
    exact (drop_chunked_states_local1_headerSent_placed hdealloc henc hdec s).mono_outcome
      a R s0 hpc hrun hpre hsp fun _ hout => hout
  | ct1Received s =>
    exact (drop_chunked_states_local1_ct1Received_placed hdealloc henc s).mono_outcome
      a R s0 hpc hrun hpre hsp fun _ hout => hout
  | ekSentCt1Received s =>
    exact (drop_chunked_states_local1_ekSentCt1Received_placed hdealloc hdec s).mono_outcome
      a R s0 hpc hrun hpre hsp fun _ hout => hout
  | noHeaderReceived s =>
    exact (drop_chunked_states_local1_noHeaderReceived_placed hdealloc hdec s).mono_outcome
      a R s0 hpc hrun hpre hsp fun _ hout => hout
  | headerReceived s =>
    exact (drop_chunked_states_local1_headerReceived_placed hdealloc hdec s).mono_outcome
      a R s0 hpc hrun hpre hsp fun _ hout => hout
  | ct1Sampled s =>
    exact (drop_chunked_states_local1_ct1Sampled_placed hct1_sent henc hdec s).mono_outcome
      a R s0 hpc hrun hpre hsp fun _ hout => hout
  | ekReceivedCt1Sampled s =>
    exact (drop_chunked_states_local1_ekReceivedCt1Sampled_placed hdealloc henc s).mono_outcome
      a R s0 hpc hrun hpre hsp fun _ hout => hout
  | ct1Acknowledged s =>
    exact (drop_chunked_states_local1_ct1Acknowledged_placed hct1_sent hdec s).mono_outcome
      a R s0 hpc hrun hpre hsp fun _ hout => hout
  | ct2Sampled s =>
    exact (drop_chunked_states_local1_ct2Sampled_placed hdealloc henc s).mono_outcome
      a R s0 hpc hrun hpre hsp fun _ hout => hout

end PlacedStates1

end CryptoVerification.SpqrV1.Drop
