/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Drop.SortedSetPt
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Drop Glue for `spqr::encoding::polynomial::PolyDecoder`

**Checked by Lean.**

Proves fixed-image (`drop_glue_poly_decoder_ok_ext`) and relocatable `[LibsignalPlacement]`
(`drop_glue_poly_decoder_placed_ok`, Block `137`) contracts for
`core::ptr::drop_glue::<spqr::encoding::polynomial::PolyDecoder> [local#1]` (105 instructions).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Layout.L12

open Lean Elab Tactic ProofLib CryptoVerification.SpqrV1.Drop in
/-- Add instruction-fetch hypotheses for `drop_glue::<PolyDecoder>` (`105 * 4 = 420` B). -/
elab "drop_poly_decoder_fetches " b:term:max H:term:max : tactic => do
  let eOff ← ProofLib.CodeLookup.lookup ``CryptoVerification.libsignalSessionCode .fnOff
    "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyDecoder> [local#1]"
  let hfn := mkCIdent eOff.decl
  let offLit := Syntax.mkNumLit (toString eOff.val)
  evalTactic (← `(tactic|
    code_fetches CryptoVerification.libsignalSessionCode spqrDropChainEpochBin $b $H $hfn $offLit 420))

end CryptoVerification.SpqrV1.Layout.L12

namespace CryptoVerification.SpqrV1.Drop

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Getters.DropGlueFacts
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Layout.L12

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option hygiene false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

local macro "poly_decoder_first8_steps " entry:term : tactic => `(tactic| (
  refine DropGlueFacts.seq_clean (mid := $entry + 40#64) (P_mid :=
    vecPtListOf A (arrA + 24#64) (c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest) ∗
      (memRegion arrA 24 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
    (Q := fun sm => Saved32Preserved s0 sm fsp arrA) ?_ ?_
  · refine SepWP.dealloc_pt_list_cons0_step arrA c0 _ _ ?_
    intro cap ptr
    dsimp only [vecPtDealloc, Saved32Preserved]
    by_cases hcap : (cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp]
    · wp_steps; wp_done
    · wp_steps; wp_apply; refine DropGlueFacts.align_pre (by rw [hsp]; ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hsp_1, htrace_1, hvregs_1⟩
    refine DropGlueFacts.seq_clean (mid := $entry + 64#64) (P_mid :=
      vecPtListOf A (arrA + 48#64) (c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest) ∗
        (memRegion arrA 48 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
      (Q := fun sm => Saved32Preserved s0 sm fsp arrA) ?_ ?_
    · refine SepWP.dealloc_pt_list_cons_step arrA 24#64 32#64 40#64 48#64 24 48 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c1 _ _ ?_
      intro cap ptr
      dsimp only [vecPtDealloc, Saved32Preserved]
      by_cases hcap : (cap == 0#64) = true <;>
        simp only [hcap, ↓reduceIte, sepConj_emp]
      · wp_steps; wp_done
      · wp_steps; wp_apply; refine DropGlueFacts.align_pre (by rw [hsp_1]; ac_rfl) ?_; wp_done
    · intro s2 hpc2 hrun2 ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hsp_2, htrace_2, hvregs_2⟩
      refine DropGlueFacts.seq_clean (mid := $entry + 88#64) (P_mid :=
        vecPtListOf A (arrA + 72#64) (c3 :: c4 :: c5 :: c6 :: c7 :: rest) ∗
          (memRegion arrA 72 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
        (Q := fun sm => Saved32Preserved s0 sm fsp arrA) ?_ ?_
      · refine SepWP.dealloc_pt_list_cons_step arrA 48#64 56#64 64#64 72#64 48 72 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c2 _ _ ?_
        intro cap ptr
        dsimp only [vecPtDealloc, Saved32Preserved]
        by_cases hcap : (cap == 0#64) = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp]
        · wp_steps; wp_done
        · wp_steps; wp_apply; refine DropGlueFacts.align_pre (by rw [hsp_2]; ac_rfl) ?_; wp_done
      · intro s3 hpc3 hrun3 ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3, hsp_3, htrace_3, hvregs_3⟩
        refine DropGlueFacts.seq_clean (mid := $entry + 112#64) (P_mid :=
          vecPtListOf A (arrA + 96#64) (c4 :: c5 :: c6 :: c7 :: rest) ∗
            (memRegion arrA 96 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
          (Q := fun sm => Saved32Preserved s0 sm fsp arrA) ?_ ?_
        · refine SepWP.dealloc_pt_list_cons_step arrA 72#64 80#64 88#64 96#64 72 96 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c3 _ _ ?_
          intro cap ptr
          dsimp only [vecPtDealloc, Saved32Preserved]
          by_cases hcap : (cap == 0#64) = true <;>
            simp only [hcap, ↓reduceIte, sepConj_emp]
          · wp_steps; wp_done
          · wp_steps; wp_apply; refine DropGlueFacts.align_pre (by rw [hsp_3]; ac_rfl) ?_; wp_done
        · intro s4 hpc4 hrun4 ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4, hsp_4, htrace_4, hvregs_4⟩
          refine DropGlueFacts.seq_clean (mid := $entry + 136#64) (P_mid :=
            vecPtListOf A (arrA + 120#64) (c5 :: c6 :: c7 :: rest) ∗
              (memRegion arrA 120 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
            (Q := fun sm => Saved32Preserved s0 sm fsp arrA) ?_ ?_
          · refine SepWP.dealloc_pt_list_cons_step arrA 96#64 104#64 112#64 120#64 96 120 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c4 _ _ ?_
            intro cap ptr
            dsimp only [vecPtDealloc, Saved32Preserved]
            by_cases hcap : (cap == 0#64) = true <;>
              simp only [hcap, ↓reduceIte, sepConj_emp]
            · wp_steps; wp_done
            · wp_steps; wp_apply; refine DropGlueFacts.align_pre (by rw [hsp_4]; ac_rfl) ?_; wp_done
          · intro s5 hpc5 hrun5 ⟨hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hx29_5, hsp_5, htrace_5, hvregs_5⟩
            refine DropGlueFacts.seq_clean (mid := $entry + 160#64) (P_mid :=
              vecPtListOf A (arrA + 144#64) (c6 :: c7 :: rest) ∗
                (memRegion arrA 144 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
              (Q := fun sm => Saved32Preserved s0 sm fsp arrA) ?_ ?_
            · refine SepWP.dealloc_pt_list_cons_step arrA 120#64 128#64 136#64 144#64 120 144 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c5 _ _ ?_
              intro cap ptr
              dsimp only [vecPtDealloc, Saved32Preserved]
              by_cases hcap : (cap == 0#64) = true <;>
                simp only [hcap, ↓reduceIte, sepConj_emp]
              · wp_steps; wp_done
              · wp_steps; wp_apply; refine DropGlueFacts.align_pre (by rw [hsp_5]; ac_rfl) ?_; wp_done
            · intro s6 hpc6 hrun6 ⟨hx19_6, hx20_6, hx21_6, hx22_6, hx23_6, hx24_6, hx25_6, hx26_6, hx27_6, hx28_6, hx29_6, hsp_6, htrace_6, hvregs_6⟩
              refine DropGlueFacts.seq_clean (mid := $entry + 184#64) (P_mid :=
                vecPtListOf A (arrA + 168#64) (c7 :: rest) ∗
                  (memRegion arrA 168 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
                (Q := fun sm => Saved32Preserved s0 sm fsp arrA) ?_ ?_
              · refine SepWP.dealloc_pt_list_cons_step arrA 144#64 152#64 160#64 168#64 144 168 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c6 _ _ ?_
                intro cap ptr
                dsimp only [vecPtDealloc, Saved32Preserved]
                by_cases hcap : (cap == 0#64) = true <;>
                  simp only [hcap, ↓reduceIte, sepConj_emp]
                · wp_steps; wp_done
                · wp_steps; wp_apply; refine DropGlueFacts.align_pre (by rw [hsp_6]; ac_rfl) ?_; wp_done
              · intro s7 hpc7 hrun7 ⟨hx19_7, hx20_7, hx21_7, hx22_7, hx23_7, hx24_7, hx25_7, hx26_7, hx27_7, hx28_7, hx29_7, hsp_7, htrace_7, hvregs_7⟩
                refine SepWP.dealloc_pt_list_cons_step arrA 168#64 176#64 184#64 192#64 168 192 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c7 _ _ ?_
                intro cap ptr
                dsimp only [vecPtDealloc, Saved32Preserved]
                by_cases hcap : (cap == 0#64) = true <;>
                  simp only [hcap, ↓reduceIte, sepConj_emp]
                · wp_steps; wp_done
                · wp_steps; wp_apply; refine DropGlueFacts.align_pre (by rw [hsp_7]; ac_rfl) ?_; wp_done
))

local macro "poly_decoder_mid7_steps " entry:term : tactic => `(tactic| (
  rcases hpres with ⟨hx19_8, hx20_8, hx21_8, hx22_8, hx23_8, hx24_8, hx25_8, hx26_8, hx27_8, hx28_8, hx29_8, hsp_8, htrace_8, hvregs_8⟩
  refine DropGlueFacts.seq_clean (mid := $entry + 232#64) (P_mid :=
    vecPtListOf A (arrA + 216#64) (c9 :: c10 :: c11 :: c12 :: c13 :: c14 :: rest) ∗
      (memRegion arrA 216 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
    (Q := fun sm => Saved32Preserved s0 sm fsp arrA) ?_ ?_
  · refine SepWP.dealloc_pt_list_cons_step arrA 192#64 200#64 208#64 216#64 192 216 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c8 _ _ ?_
    intro cap ptr
    dsimp only [vecPtDealloc, Saved32Preserved]
    by_cases hcap : (cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp]
    · wp_steps; wp_done
    · wp_steps; wp_apply; refine DropGlueFacts.align_pre (by rw [hsp_8]; ac_rfl) ?_; wp_done
  · intro s9 hpc9 hrun9 ⟨hx19_9, hx20_9, hx21_9, hx22_9, hx23_9, hx24_9, hx25_9, hx26_9, hx27_9, hx28_9, hx29_9, hsp_9, htrace_9, hvregs_9⟩
    refine DropGlueFacts.seq_clean (mid := $entry + 256#64) (P_mid :=
      vecPtListOf A (arrA + 240#64) (c10 :: c11 :: c12 :: c13 :: c14 :: rest) ∗
        (memRegion arrA 240 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
      (Q := fun sm => Saved32Preserved s0 sm fsp arrA) ?_ ?_
    · refine SepWP.dealloc_pt_list_cons_step arrA 216#64 224#64 232#64 240#64 216 240 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c9 _ _ ?_
      intro cap ptr
      dsimp only [vecPtDealloc, Saved32Preserved]
      by_cases hcap : (cap == 0#64) = true <;>
        simp only [hcap, ↓reduceIte, sepConj_emp]
      · wp_steps; wp_done
      · wp_steps; wp_apply; refine DropGlueFacts.align_pre (by rw [hsp_9]; ac_rfl) ?_; wp_done
    · intro s10 hpc10 hrun10 ⟨hx19_10, hx20_10, hx21_10, hx22_10, hx23_10, hx24_10, hx25_10, hx26_10, hx27_10, hx28_10, hx29_10, hsp_10, htrace_10, hvregs_10⟩
      refine DropGlueFacts.seq_clean (mid := $entry + 280#64) (P_mid :=
        vecPtListOf A (arrA + 264#64) (c11 :: c12 :: c13 :: c14 :: rest) ∗
          (memRegion arrA 264 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
        (Q := fun sm => Saved32Preserved s0 sm fsp arrA) ?_ ?_
      · refine SepWP.dealloc_pt_list_cons_step arrA 240#64 248#64 256#64 264#64 240 264 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c10 _ _ ?_
        intro cap ptr
        dsimp only [vecPtDealloc, Saved32Preserved]
        by_cases hcap : (cap == 0#64) = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp]
        · wp_steps; wp_done
        · wp_steps; wp_apply; refine DropGlueFacts.align_pre (by rw [hsp_10]; ac_rfl) ?_; wp_done
      · intro s11 hpc11 hrun11 ⟨hx19_11, hx20_11, hx21_11, hx22_11, hx23_11, hx24_11, hx25_11, hx26_11, hx27_11, hx28_11, hx29_11, hsp_11, htrace_11, hvregs_11⟩
        refine DropGlueFacts.seq_clean (mid := $entry + 304#64) (P_mid :=
          vecPtListOf A (arrA + 288#64) (c12 :: c13 :: c14 :: rest) ∗
            (memRegion arrA 288 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
          (Q := fun sm => Saved32Preserved s0 sm fsp arrA) ?_ ?_
        · refine SepWP.dealloc_pt_list_cons_step arrA 264#64 272#64 280#64 288#64 264 288 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c11 _ _ ?_
          intro cap ptr
          dsimp only [vecPtDealloc, Saved32Preserved]
          by_cases hcap : (cap == 0#64) = true <;>
            simp only [hcap, ↓reduceIte, sepConj_emp]
          · wp_steps; wp_done
          · wp_steps; wp_apply; refine DropGlueFacts.align_pre (by rw [hsp_11]; ac_rfl) ?_; wp_done
        · intro s12 hpc12 hrun12 ⟨hx19_12, hx20_12, hx21_12, hx22_12, hx23_12, hx24_12, hx25_12, hx26_12, hx27_12, hx28_12, hx29_12, hsp_12, htrace_12, hvregs_12⟩
          refine DropGlueFacts.seq_clean (mid := $entry + 328#64) (P_mid :=
            vecPtListOf A (arrA + 312#64) (c13 :: c14 :: rest) ∗
              (memRegion arrA 312 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
            (Q := fun sm => Saved32Preserved s0 sm fsp arrA) ?_ ?_
          · refine SepWP.dealloc_pt_list_cons_step arrA 288#64 296#64 304#64 312#64 288 312 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c12 _ _ ?_
            intro cap ptr
            dsimp only [vecPtDealloc, Saved32Preserved]
            by_cases hcap : (cap == 0#64) = true <;>
              simp only [hcap, ↓reduceIte, sepConj_emp]
            · wp_steps; wp_done
            · wp_steps; wp_apply; refine DropGlueFacts.align_pre (by rw [hsp_12]; ac_rfl) ?_; wp_done
          · intro s13 hpc13 hrun13 ⟨hx19_13, hx20_13, hx21_13, hx22_13, hx23_13, hx24_13, hx25_13, hx26_13, hx27_13, hx28_13, hx29_13, hsp_13, htrace_13, hvregs_13⟩
            refine DropGlueFacts.seq_clean (mid := $entry + 352#64) (P_mid :=
              vecPtListOf A (arrA + 336#64) (c14 :: rest) ∗
                (memRegion arrA 336 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
              (Q := fun sm => Saved32Preserved s0 sm fsp arrA) ?_ ?_
            · refine SepWP.dealloc_pt_list_cons_step arrA 312#64 320#64 328#64 336#64 312 336 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c13 _ _ ?_
              intro cap ptr
              dsimp only [vecPtDealloc, Saved32Preserved]
              by_cases hcap : (cap == 0#64) = true <;>
                simp only [hcap, ↓reduceIte, sepConj_emp]
              · wp_steps; wp_done
              · wp_steps; wp_apply; refine DropGlueFacts.align_pre (by rw [hsp_13]; ac_rfl) ?_; wp_done
            · intro s14 hpc14 hrun14 ⟨hx19_14, hx20_14, hx21_14, hx22_14, hx23_14, hx24_14, hx25_14, hx26_14, hx27_14, hx28_14, hx29_14, hsp_14, htrace_14, hvregs_14⟩
              refine SepWP.dealloc_pt_list_cons_step arrA 336#64 344#64 352#64 360#64 336 360 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c14 _ _ ?_
              intro cap ptr
              dsimp only [vecPtDealloc, Saved32Preserved]
              by_cases hcap : (cap == 0#64) = true <;>
                simp only [hcap, ↓reduceIte, sepConj_emp]
              · wp_steps; wp_done
              · wp_steps; wp_apply; refine DropGlueFacts.align_pre (by rw [hsp_14]; ac_rfl) ?_; wp_done
))

local macro "poly_decoder_main_steps " entry:term : tactic => `(tactic| (
  wp_init x s0
  obtain ⟨arrA, vecs⟩ := x
  dsimp only [NUM_POLYS] at *
  subst ‹s0.readReg64 (Reg.gpr 0#5) = arrA›
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, rfl⟩ :=
    list_length_16_elim (by assumption)
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropGluePoly16_split s0.sp]
  cells_unfold
  wp_pull_exists
  rename_i w0 w1 w2 w3
  refine DropGlueFacts.seq_clean (mid := $entry + 12#64)
    (P_mid :=
      vecPtListOf A (s0.readReg64 (Reg.gpr 0#5))
        [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15] ∗
      (A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3))))
    (Q := fun sm =>
      sm.readReg64 .x0 = s0.readReg64 (Reg.gpr 0#5) ∧
      sm.readReg64 .x20 = s0.readReg64 .x20 ∧
      sm.readReg64 .x21 = s0.readReg64 .x21 ∧
      sm.readReg64 .x22 = s0.readReg64 .x22 ∧
      sm.readReg64 .x23 = s0.readReg64 .x23 ∧
      sm.readReg64 .x24 = s0.readReg64 .x24 ∧
      sm.readReg64 .x25 = s0.readReg64 .x25 ∧
      sm.readReg64 .x26 = s0.readReg64 .x26 ∧
      sm.readReg64 .x27 = s0.readReg64 .x27 ∧
      sm.readReg64 .x28 = s0.readReg64 .x28 ∧
      sm.readReg64 .x29 = s0.sp - 32#64 ∧
      sm.sp = s0.sp - 32#64 ∧
      sm.trace = s0.trace ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0)
    ?_ ?_
  · wp_steps
    refine DropGlueFacts.align_pre (by dsimp only [Reg.x19, Reg.lr, Reg.fp]) ?_
    wp_done
  · intro s1 hpc1 hrun1 ⟨hx0_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hsp_1, htrace_1, hvregs_1⟩
    refine DropGlueFacts.seq_clean (mid := $entry + 208#64)
      (P_mid :=
        vecPtListOf A (s0.readReg64 (Reg.gpr 0#5) + 192#64)
          [c8, c9, c10, c11, c12, c13, c14, c15] ∗
        (memRegion (s0.readReg64 (Reg.gpr 0#5)) 192 ∗
          (A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
            (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3)))))
      (Q := fun sm => Saved32Preserved s0 sm (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)))
      (hfirst8 s0 (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)) hfsp_align
        c0 c1 c2 c3 c4 c5 c6 c7 [c8, c9, c10, c11, c12, c13, c14, c15] s1 _
        hpc1 hrun1 hx0_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hsp_1 htrace_1 hvregs_1)
      ?_
    intro s2 hpc2 hrun2 hpres2
    refine DropGlueFacts.seq_clean (mid := $entry + 376#64)
      (P_mid :=
        vecPtListOf A (s0.readReg64 (Reg.gpr 0#5) + 360#64) [c15] ∗
        (memRegion (s0.readReg64 (Reg.gpr 0#5)) 360 ∗
          (A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
            (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3)))))
      (Q := fun sm => Saved32Preserved s0 sm (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)))
      (hmid7 s0 (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)) hfsp_align
        c8 c9 c10 c11 c12 c13 c14 [c15] s2 _ hpc2 hrun2 hpres2)
      ?_
    intro s3 hpc3 hrun3 ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3, hsp_3, htrace_3, hvregs_3⟩
    have hsingleton : vecPtListOf A (s0.readReg64 (Reg.gpr 0#5) + 360#64) [c15] =
        vecPtOf A (s0.readReg64 (Reg.gpr 0#5) + 360#64) c15 :=
      arrayAt_singleton (fun pts addr => vecPtOf A addr pts) 24 (s0.readReg64 (Reg.gpr 0#5) + 360#64) c15
    rw [hsingleton]
    refine SepWP.weaken_pre
      (vecPtOf_step_entails A (s0.readReg64 (Reg.gpr 0#5)) 360#64 368#64 376#64 (by bv_omega) (by bv_omega) c15 _) ?_
    apply SepWP.exists_left; intro cap
    apply SepWP.exists_left; intro ptr
    dsimp only [vecPtDealloc]
    by_cases hcap : (cap == 0#64) = true <;>
      simp only [hcap, Bool.false_eq_true, ↓reduceIte, sepConj_emp]
    · wp_steps
      refine SepWP.weaken_pre
        (Entails.trans (Entails.of_eq (by ac_rfl))
          (cap0_poly16_post (s0.readReg64 (Reg.gpr 0#5)) cap ptr A.pool s0.sp
            (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) w3)) ?_
      wp_done
    · wp_steps
      refine SepWP.weaken_pre
        (Entails.trans (Entails.of_eq (by ac_rfl))
          (tail_dealloc_poly16_pre_weaken (s0.readReg64 (Reg.gpr 0#5)) cap ptr
            (A.live ptr (cap <<< 2#64).toNat 2 ∗ memRegion ptr (cap <<< 2#64).toNat)
            (memRegion (s0.readReg64 (Reg.gpr 0#5)) 360) A.pool s0.sp
            (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) w3)) ?_
      wp_apply
      refine SepWP.weaken_pre
        (tail_dealloc_poly16_post (s0.readReg64 (Reg.gpr 0#5)) A.pool s0.sp) ?_
      wp_done
))

private theorem drop_glue_poly_decoder_first8 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropPolyDecoderName +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyDecoder> [local#1]" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A))
    (s0 : State) (fsp arrA : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (c0 c1 c2 c3 c4 c5 c6 c7 : List Pt) (rest : List (List Pt))
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (dropProgAtExt b ext).fnAddr dropPolyDecoderName + 12#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = arrA)
    (hx20 : s.readReg64 .x20 = s0.readReg64 .x20)
    (hx21 : s.readReg64 .x21 = s0.readReg64 .x21)
    (hx22 : s.readReg64 .x22 = s0.readReg64 .x22)
    (hx23 : s.readReg64 .x23 = s0.readReg64 .x23)
    (hx24 : s.readReg64 .x24 = s0.readReg64 .x24)
    (hx25 : s.readReg64 .x25 = s0.readReg64 .x25)
    (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hx29 : s.readReg64 .x29 = fsp)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropPolyDecoderName + 208#64)
      s
      (vecPtListOf A arrA (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest) ∗
        (A.pool ∗ stackAt fsp allocHookStack ∗ Frame))
      (fun sm Pm =>
        (Pm ⊢ vecPtListOf A (arrA + 192#64) rest ∗
          (memRegion arrA 192 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame))) ∧
        Saved32Preserved s0 sm fsp arrA) := by
  simp only [rustDeallocSpec] at hdealloc
  dsimp only [dropProgAtExt, dropPolyDecoderName, BitVec.ofNat_eq_ofNat] at *
  drop_poly_decoder_fetches b (Rust.withPanics ext)
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyDecoder> [local#1]" = entry
  examples_hide_fetches
  poly_decoder_first8_steps entry

private theorem drop_glue_poly_decoder_mid7 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropPolyDecoderName +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyDecoder> [local#1]" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A))
    (s0 : State) (fsp arrA : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (c8 c9 c10 c11 c12 c13 c14 : List Pt) (rest : List (List Pt))
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (dropProgAtExt b ext).fnAddr dropPolyDecoderName + 208#64)
    (hrun : s.status = .Running)
    (hpres : Saved32Preserved s0 s fsp arrA) :
    SepWP (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropPolyDecoderName + 376#64)
      s
      (vecPtListOf A (arrA + 192#64) (c8 :: c9 :: c10 :: c11 :: c12 :: c13 :: c14 :: rest) ∗
        (memRegion arrA 192 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
      (fun sm Pm =>
        (Pm ⊢ vecPtListOf A (arrA + 360#64) rest ∗
          (memRegion arrA 360 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame))) ∧
        Saved32Preserved s0 sm fsp arrA) := by
  simp only [rustDeallocSpec] at hdealloc
  dsimp only [dropProgAtExt, dropPolyDecoderName, BitVec.ofNat_eq_ofNat] at *
  drop_poly_decoder_fetches b (Rust.withPanics ext)
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyDecoder> [local#1]" = entry
  examples_hide_fetches
  poly_decoder_mid7_steps entry

/-- `core::ptr::drop_glue::<spqr::encoding::polynomial::PolyDecoder> [local#1]` (105 instructions)
    satisfies `dropGlueSortedSetPt16Spec A`. -/
theorem drop_glue_poly_decoder_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc_base : DeallocOkExt b A ext) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropPolyDecoderName)
      (dropGlueSortedSetPt16Spec A) := by
  simp only [dropGlueSortedSetPt16Spec]
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropPolyDecoderName +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyDecoder> [local#1]" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel
      (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyDecoder> [local#1]" "__rustc::__rust_dealloc"))
      (b := b) (X := Rust.withPanics ext)
      dropPolyDecoder_fnOff dealloc_fnOff_drop (by decide))
    hdealloc_base
  have hdealloc := hdealloc_raw
  simp only [rustDeallocSpec] at hdealloc
  have hfirst8 := drop_glue_poly_decoder_first8 (b := b) (ext := ext) hdealloc_raw
  have hmid7 := drop_glue_poly_decoder_mid7 (b := b) (ext := ext) hdealloc_raw
  drop_poly_decoder_fetches b (Rust.withPanics ext)
  dsimp only [dropProgAtExt, dropPolyDecoderName, BitVec.ofNat_eq_ofNat] at hdealloc hfirst8 hmid7 ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyDecoder> [local#1]" = entry
  examples_hide_fetches
  poly_decoder_main_steps entry

/-! ## Relocatable `[LibsignalPlacement]` Proof (Block `137`) -/

private theorem drop_glue_poly_decoder_placed_first8 [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_137).rebase (blkPl_137).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (fsp arrA : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (c0 c1 c2 c3 c4 c5 c6 c7 : List Pt) (rest : List (List Pt))
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_137).base + 12#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = arrA)
    (hx20 : s.readReg64 .x20 = s0.readReg64 .x20)
    (hx21 : s.readReg64 .x21 = s0.readReg64 .x21)
    (hx22 : s.readReg64 .x22 = s0.readReg64 .x22)
    (hx23 : s.readReg64 .x23 = s0.readReg64 .x23)
    (hx24 : s.readReg64 .x24 = s0.readReg64 .x24)
    (hx25 : s.readReg64 .x25 = s0.readReg64 .x25)
    (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hx29 : s.readReg64 .x29 = fsp)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_137).rebase (blkPl_137).base H)
      ((blkPl_137).base + 208#64)
      s
      (vecPtListOf A arrA (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest) ∗
        (A.pool ∗ stackAt fsp allocHookStack ∗ Frame))
      (fun sm Pm =>
        (Pm ⊢ vecPtListOf A (arrA + 192#64) rest ∗
          (memRegion arrA 192 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame))) ∧
        Saved32Preserved s0 sm fsp arrA) := by
  simp only [rustDeallocSpec] at hdealloc
  poly_decoder_first8_steps (blkPl_137).base

private theorem drop_glue_poly_decoder_placed_mid7 [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_137).rebase (blkPl_137).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (fsp arrA : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (c8 c9 c10 c11 c12 c13 c14 : List Pt) (rest : List (List Pt))
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_137).base + 208#64)
    (hrun : s.status = .Running)
    (hpres : Saved32Preserved s0 s fsp arrA) :
    SepWP ((blkPC_137).rebase (blkPl_137).base H)
      ((blkPl_137).base + 376#64)
      s
      (vecPtListOf A (arrA + 192#64) (c8 :: c9 :: c10 :: c11 :: c12 :: c13 :: c14 :: rest) ∗
        (memRegion arrA 192 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
      (fun sm Pm =>
        (Pm ⊢ vecPtListOf A (arrA + 360#64) rest ∗
          (memRegion arrA 360 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame))) ∧
        Saved32Preserved s0 sm fsp arrA) := by
  simp only [rustDeallocSpec] at hdealloc
  poly_decoder_mid7_steps (blkPl_137).base

/-- Relocatable `core::ptr::drop_glue::<spqr::encoding::polynomial::PolyDecoder> [local#1]`
    (Block `137`) satisfies `dropGlueSortedSetPt16Spec A` under `[LibsignalPlacement]`. -/
theorem drop_glue_poly_decoder_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc_raw : subroutine_ok ((blkPC_137).rebase (blkPl_137).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_137).rebase (blkPl_137).base H)
      (blkPl_137).base
      (dropGlueSortedSetPt16Spec A) := by
  simp only [dropGlueSortedSetPt16Spec]
  have hdealloc := hdealloc_raw
  simp only [rustDeallocSpec] at hdealloc
  have hfirst8 := drop_glue_poly_decoder_placed_first8 hdealloc_raw
  have hmid7 := drop_glue_poly_decoder_placed_mid7 hdealloc_raw
  poly_decoder_main_steps (blkPl_137).base

end CryptoVerification.SpqrV1.Drop
