/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbOuter
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbOuter
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDecodes
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::encoding::polynomial::PolyDecoder>::from_pb`: Outer Loop Induction and Error Exits

Proves outer-loop induction (`+204 → +876 / +740`), shared epilogue tails (`+1244`, `+828`, `+820`,
`+1236`), the `Vec<u8>` drop loop (`+776 → +820`), and error exits A (`+712`) and B (`+740`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Poly.DecoderPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Getters.DropGlueFacts
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem align_pre_wpp {prog : Program} {t : BitVec 64} {s : State} {P1 P2 : SepProp}
    {Q R : State → SepProp → Prop} (hwp : SepWPp prog t s P2 Q R) (h : P1 = P2) :
    SepWPp prog t s P1 Q R := h ▸ hwp

theorem align_pre_wp {prog : Program} {t : BitVec 64} {s : State} {P1 P2 : SepProp}
    {post : State → SepProp → Prop} (hwp : SepWP prog t s P2 post) (h : P1 = P2) :
    SepWP prog t s P1 post := h ▸ hwp

theorem replace_sub_entails {A B P Q : SepProp} (h : A ⊢ B) (C : SepProp)
    (hP : P = A ∗ C) (hQ : B ∗ C = Q) : P ⊢ Q := by
  rw [hP, ← hQ]; exact sepConj_mono_left h

/-! ## Outer Loop Induction (`+204 -> +876` or `+740`) -/

/-- Outer loop induction (`+204 -> +876` if all remaining elements have `length % 4 = 0`,
    or `+204 -> +740` at the first element with `length % 4 ≠ 0`). -/
theorem fromPb_outer_loop_wpp {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    {Q : State → SepProp → Prop} {R : SepProp}
    (s0 : State) (fsp ptsPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rem : List (List (BitVec 8))) (hrem_ne : rem ≠ [])
      (i : Nat) (htot : i + rem.length = 16) (v416 v424 v432 : BitVec 64)
      (s : State) (Frame : SepProp),
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 204#64 →
      s.status = .Running → s.sp = fsp → s.readReg64 .x19 = 24#64 → s.readReg64 .x21 = ptsPtr →
      s.readReg64 .x24 = 16#64 → s.readReg64 .x25 = BitVec.ofNat 64 i → s.readReg64 .x29 = fsp + 448#64 →
      s.trace = s0.trace → calleeSavedVRegs s = calleeSavedVRegs s0 →
      (∀ (sm : State) (w416 w424 w432 : BitVec 64),
        (∀ bs ∈ rem, bs.length % 4 = 0) →
        sm.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 876#64 →
        sm.status = .Running → sm.sp = fsp → sm.readReg64 .x21 = ptsPtr →
        sm.readReg64 .x24 = 16#64 → sm.readReg64 .x29 = fsp + 448#64 → sm.trace = s0.trace →
        calleeSavedVRegs sm = calleeSavedVRegs s0 →
        SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) sm
          (((fsp + 24#64) ↦₆₄ ptsPtr) ∗ ((fsp + 416#64) ↦₆₄ w416) ∗
            ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
            sortedSetPtListOf A (fsp + 32#64 + BitVec.ofNat 64 (24 * i))
              (rem.map fun bs => pushChunks4Total bs { vec := [] }) ∗
            arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * i)) rem ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
          Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ fromPbOnPanic s0 sf ∗ R))) →
      (∀ (sm : State) (sets_err : List SortedSetPt) (w416 w424 w432 : BitVec 64),
        (∃ bs ∈ rem, bs.length % 4 ≠ 0) → sets_err.length = rem.length →
        sm.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 740#64 →
        sm.status = .Running → sm.sp = fsp → sm.readReg64 .x21 = ptsPtr →
        sm.readReg64 .x24 = 16#64 → sm.readReg64 .x29 = fsp + 448#64 → sm.trace = s0.trace →
        calleeSavedVRegs sm = calleeSavedVRegs s0 →
        SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) sm
          (((fsp + 24#64) ↦₆₄ ptsPtr) ∗ ((fsp + 416#64) ↦₆₄ w416) ∗
            ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
            sortedSetPtListOf A (fsp + 32#64 + BitVec.ofNat 64 (24 * i)) sets_err ∗
            arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * i)) rem ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
          Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ fromPbOnPanic s0 sf ∗ R))) →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s
        (((fsp + 24#64) ↦₆₄ ptsPtr) ∗ ((fsp + 416#64) ↦₆₄ v416) ∗
          ((fsp + 424#64) ↦₆₄ v424) ∗ ((fsp + 432#64) ↦₆₄ v432) ∗
          emptySlotsAt (fsp + 32#64 + BitVec.ofNat 64 (24 * i)) rem.length ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * i)) rem ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ fromPbOnPanic s0 sf ∗ R))
  | [], hrem_ne, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => nomatch hrem_ne rfl
  | [pts], _, i, htot, v416, v424, v432,
      s, Frame, hpc, hrun, hsp, hx19, hx21, hx24, hx25, hx29, htr, hvregs, hok, herr => by
    have hi1 : i + 1 = 16 := by simp at htot; omega
    by_cases hmod4 : pts.length % 4 = 0
    · conv => arg 4; simp only [List.length_singleton, arrayAt_cons, arrayAt_nil, sepConj_emp]
      refine align_pre_wpp
        (fromPb_outer_alloc_and_push_wpp hA s0 fsp ptsPtr hfsp_align i 0 (by omega) pts hmod4
          v416 v424 v432 s Frame hpc hrun hsp hx19 hx21 hx24 hx25 hx29 htr hvregs ?_)
        (by ac_rfl)
      intro sm w416 w424 w432 hpcm hrunm hspm hx19m hx21m hx24m hx25m hx29m htrm hvregsm
      simp only [hi1, ↓reduceIte] at hpcm
      have hall : ∀ bs ∈ [pts], bs.length % 4 = 0 := by
        intro bs hbs; simp only [List.mem_singleton] at hbs; subst hbs; exact hmod4
      refine SepWPp.weaken_pre ?_
        (hok sm w416 w424 w432 hall hpcm hrunm hspm hx21m hx24m hx29m htrm hvregsm)
      dsimp only [sortedSetPtListOf, List.map]
      simp only [emptySlotsAt_zero, arrayAt_cons, arrayAt_nil, sepConj_emp]
      exact Entails.of_eq (by ac_rfl)
    · have hempty := emptySlotsAt_entails_sortedSetPtListOf A 1
        (fsp + 32#64 + BitVec.ofNat 64 (24 * i))
      conv => arg 4; simp only [List.length_singleton, arrayAt_cons, arrayAt_nil, sepConj_emp]
      refine SepWPp.weaken_pre (replace_sub_entails hempty
        (vecU8 A (ptsPtr + BitVec.ofNat 64 (24 * i)) pts ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
          ((fsp + 416#64) ↦₆₄ v416) ∗ ((fsp + 424#64) ↦₆₄ v424) ∗ ((fsp + 432#64) ↦₆₄ v432) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) (by ac_rfl) (by ac_rfl))
        (fromPb_outer_invalid_mod4_wpp s0 fsp ptsPtr i pts hmod4 s
          (((fsp + 24#64) ↦₆₄ ptsPtr) ∗
            ((fsp + 416#64) ↦₆₄ v416) ∗ ((fsp + 424#64) ↦₆₄ v424) ∗ ((fsp + 432#64) ↦₆₄ v432) ∗
            sortedSetPtListOf A (fsp + 32#64 + BitVec.ofNat 64 (24 * i)) (List.replicate 1 { vec := [] }) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
          hpc hrun hsp hx19 hx21 hx24 hx25 hx29 htr hvregs ?_)
      intro sm hpcm hrunm hspm hx21m hx24m hx29m htrm hvregsm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (herr sm (List.replicate 1 { vec := [] }) v416 v424 v432
          ⟨pts, List.mem_singleton.mpr rfl, hmod4⟩ rfl hpcm hrunm hspm hx21m hx24m hx29m htrm hvregsm)
      simp only [arrayAt_cons, arrayAt_nil, sepConj_emp]; ac_rfl
  | pts :: pts2 :: rem', _, i, htot, v416, v424, v432,
      s, Frame, hpc, hrun, hsp, hx19, hx21, hx24, hx25, hx29, htr, hvregs, hok, herr => by
    have hi1_ne : i + 1 ≠ 16 := by simp at htot; omega
    have hoff_out : (fsp + 32#64 + BitVec.ofNat 64 (24 * i)) + 24#64 =
        fsp + 32#64 + BitVec.ofNat 64 (24 * (i + 1)) := off_24_succ (fsp + 32#64) i
    have hoff_in : (ptsPtr + BitVec.ofNat 64 (24 * i)) + 24#64 =
        ptsPtr + BitVec.ofNat 64 (24 * (i + 1)) := off_24_succ ptsPtr i
    by_cases hmod4 : pts.length % 4 = 0
    · conv => arg 4; rw [arrayAt_cons, hoff_in]
      refine align_pre_wpp
        (fromPb_outer_alloc_and_push_wpp hA s0 fsp ptsPtr hfsp_align i (pts2 :: rem').length
          (by simp at htot ⊢; omega) pts hmod4 v416 v424 v432 s
          (arrayAt (fun bs addr => vecU8 A addr bs) 24
            (ptsPtr + BitVec.ofNat 64 (24 * (i + 1))) (pts2 :: rem') ∗ Frame)
          hpc hrun hsp hx19 hx21 hx24 hx25 hx29 htr hvregs ?_)
        (by ac_rfl)
      intro sm w416 w424 w432 hpcm hrunm hspm hx19m hx21m hx24m hx25m hx29m htrm hvregsm
      simp only [hi1_ne, ↓reduceIte] at hpcm
      refine align_pre_wpp
        (fromPb_outer_loop_wpp hA s0 fsp ptsPtr hfsp_align
          (pts2 :: rem') (List.cons_ne_nil pts2 rem') (i + 1) (by simp at htot ⊢; omega)
          w416 w424 w432 sm
          (sortedSetPtOf A (fsp + 32#64 + BitVec.ofNat 64 (24 * i))
            (pushChunks4Total pts { vec := [] }) ∗
            vecU8 A (ptsPtr + BitVec.ofNat 64 (24 * i)) pts ∗ Frame)
          hpcm hrunm hspm hx19m hx21m hx24m hx25m hx29m htrm hvregsm ?_ ?_)
        (by ac_rfl)
      · intro s_end u416 u424 u432 hall_rem hpc_end hrun_end hsp_end hx21_end hx24_end hx29_end htr_end hvregs_end
        have hall : ∀ bs ∈ (pts :: pts2 :: rem'), bs.length % 4 = 0 := by
          intro bs hbs; exact (List.mem_cons.mp hbs).elim (fun h => h ▸ hmod4) (hall_rem bs)
        refine SepWPp.weaken_pre ?_
          (hok s_end u416 u424 u432 hall hpc_end hrun_end hsp_end hx21_end hx24_end hx29_end htr_end hvregs_end)
        rw [show sortedSetPtListOf A (fsp + 32#64 + BitVec.ofNat 64 (24 * i))
              ((pts :: pts2 :: rem').map fun bs => pushChunks4Total bs { vec := [] }) =
            sortedSetPtOf A (fsp + 32#64 + BitVec.ofNat 64 (24 * i)) (pushChunks4Total pts { vec := [] }) ∗
              sortedSetPtListOf A (fsp + 32#64 + BitVec.ofNat 64 (24 * i) + 24#64)
                ((pts2 :: rem').map fun bs => pushChunks4Total bs { vec := [] }) from rfl, hoff_out,
          show arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * i)) (pts :: pts2 :: rem') =
            vecU8 A (ptsPtr + BitVec.ofNat 64 (24 * i)) pts ∗
              arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * i) + 24#64) (pts2 :: rem') from rfl, hoff_in]
        exact Entails.of_eq (by ac_rfl)
      · intro s_err sets_rem u416 u424 u432 hex_rem hlen_rem hpc_err hrun_err hsp_err hx21_err hx24_err hx29_err htr_err hvregs_err
        rcases hex_rem with ⟨bs_bad, hbs_bad, hbad⟩
        have hex : ∃ bs ∈ (pts :: pts2 :: rem'), bs.length % 4 ≠ 0 := ⟨bs_bad, List.mem_cons_of_mem pts hbs_bad, hbad⟩
        refine SepWPp.weaken_pre ?_
          (herr s_err (pushChunks4Total pts { vec := [] } :: sets_rem) u416 u424 u432
            hex (by simp [hlen_rem]) hpc_err hrun_err hsp_err hx21_err hx24_err hx29_err htr_err hvregs_err)
        rw [show sortedSetPtListOf A (fsp + 32#64 + BitVec.ofNat 64 (24 * i))
              (pushChunks4Total pts { vec := [] } :: sets_rem) =
            sortedSetPtOf A (fsp + 32#64 + BitVec.ofNat 64 (24 * i)) (pushChunks4Total pts { vec := [] }) ∗
              sortedSetPtListOf A (fsp + 32#64 + BitVec.ofNat 64 (24 * i) + 24#64) sets_rem from rfl, hoff_out,
          show arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * i)) (pts :: pts2 :: rem') =
            vecU8 A (ptsPtr + BitVec.ofNat 64 (24 * i)) pts ∗
              arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * i) + 24#64) (pts2 :: rem') from rfl, hoff_in]
        exact Entails.of_eq (by ac_rfl)
    · have hempty := emptySlotsAt_entails_sortedSetPtListOf A (pts :: pts2 :: rem').length (fsp + 32#64 + BitVec.ofNat 64 (24 * i))
      conv => arg 4; rw [arrayAt_cons, hoff_in]
      refine SepWPp.weaken_pre (replace_sub_entails hempty
        (vecU8 A (ptsPtr + BitVec.ofNat 64 (24 * i)) pts ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
          ((fsp + 416#64) ↦₆₄ v416) ∗ ((fsp + 424#64) ↦₆₄ v424) ∗ ((fsp + 432#64) ↦₆₄ v432) ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * (i + 1))) (pts2 :: rem') ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) (by ac_rfl) (by ac_rfl))
        (fromPb_outer_invalid_mod4_wpp s0 fsp ptsPtr i pts hmod4 s
          (((fsp + 24#64) ↦₆₄ ptsPtr) ∗ ((fsp + 416#64) ↦₆₄ v416) ∗ ((fsp + 424#64) ↦₆₄ v424) ∗ ((fsp + 432#64) ↦₆₄ v432) ∗
            sortedSetPtListOf A (fsp + 32#64 + BitVec.ofNat 64 (24 * i)) (List.replicate (pts :: pts2 :: rem').length { vec := [] }) ∗
            arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * (i + 1))) (pts2 :: rem') ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
          hpc hrun hsp hx19 hx21 hx24 hx25 hx29 htr hvregs ?_)
      intro sm hpcm hrunm hspm hx21m hx24m hx29m htrm hvregsm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (herr sm (List.replicate (pts :: pts2 :: rem').length { vec := [] }) v416 v424 v432
          ⟨pts, List.mem_cons_self, hmod4⟩ (by simp) hpcm hrunm hspm hx21m hx24m hx29m htrm hvregsm)
      simp only [arrayAt_cons, hoff_in]; ac_rfl

/-! ## Stack Frame, `savedRegsAt`, and `vecVecU8At` Deallocation Helpers -/

/-- Core stack budget of `from_pb` (`544 + dropGluePoly16Stack = 4672` bytes). -/
abbrev fromPbCoreStack : Nat := 544 + dropGluePoly16Stack

/-- Saved callee-saved registers at `[fsp + 448 .. fsp + 544)` (`= [s0.sp - 96 .. s0.sp)`). -/
def savedRegsAt (fsp : BitVec 64) (s0 : State) : SepProp :=
  ((fsp + 448#64) ↦₆₄ s0.readReg64 .x29) ∗
  ((fsp + 456#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((fsp + 464#64) ↦₆₄ s0.readReg64 .x28) ∗
  ((fsp + 472#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((fsp + 480#64) ↦₆₄ s0.readReg64 .x26) ∗
  ((fsp + 488#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((fsp + 496#64) ↦₆₄ s0.readReg64 .x24) ∗
  ((fsp + 504#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((fsp + 512#64) ↦₆₄ s0.readReg64 .x22) ∗
  ((fsp + 520#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((fsp + 528#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((fsp + 536#64) ↦₆₄ s0.readReg64 .x19)

@[local arm64_norm, local wp_norm] theorem fsp_448_add_8 (fsp : BitVec 64) : (fsp + 448#64) + 8#64 = fsp + 456#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem fsp_448_add_16 (fsp : BitVec 64) : (fsp + 448#64) + 16#64 = fsp + 464#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem fsp_448_add_24 (fsp : BitVec 64) : (fsp + 448#64) + 24#64 = fsp + 472#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem fsp_448_add_32 (fsp : BitVec 64) : (fsp + 448#64) + 32#64 = fsp + 480#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem fsp_448_add_40 (fsp : BitVec 64) : (fsp + 448#64) + 40#64 = fsp + 488#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem fsp_448_add_48 (fsp : BitVec 64) : (fsp + 448#64) + 48#64 = fsp + 496#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem fsp_448_add_56 (fsp : BitVec 64) : (fsp + 448#64) + 56#64 = fsp + 504#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem fsp_448_add_64 (fsp : BitVec 64) : (fsp + 448#64) + 64#64 = fsp + 512#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem fsp_448_add_72 (fsp : BitVec 64) : (fsp + 448#64) + 72#64 = fsp + 520#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem fsp_448_add_80 (fsp : BitVec 64) : (fsp + 448#64) + 80#64 = fsp + 528#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem fsp_448_add_88 (fsp : BitVec 64) : (fsp + 448#64) + 88#64 = fsp + 536#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem fsp_448_add_96 (fsp : BitVec 64) : (fsp + 448#64) + 96#64 = fsp + 544#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem fsp_456_add_8 (fsp : BitVec 64) : (fsp + 456#64) + 8#64 = fsp + 464#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem fsp_464_add_8 (fsp : BitVec 64) : (fsp + 464#64) + 8#64 = fsp + 472#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem fsp_472_add_8 (fsp : BitVec 64) : (fsp + 472#64) + 8#64 = fsp + 480#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem fsp_480_add_8 (fsp : BitVec 64) : (fsp + 480#64) + 8#64 = fsp + 488#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem fsp_488_add_8 (fsp : BitVec 64) : (fsp + 488#64) + 8#64 = fsp + 496#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem fsp_496_add_8 (fsp : BitVec 64) : (fsp + 496#64) + 8#64 = fsp + 504#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem fsp_504_add_8 (fsp : BitVec 64) : (fsp + 504#64) + 8#64 = fsp + 512#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem fsp_512_add_8 (fsp : BitVec 64) : (fsp + 512#64) + 8#64 = fsp + 520#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem fsp_520_add_8 (fsp : BitVec 64) : (fsp + 520#64) + 8#64 = fsp + 528#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem fsp_528_add_8 (fsp : BitVec 64) : (fsp + 528#64) + 8#64 = fsp + 536#64 := by bv_omega

theorem savedRegsAt_entails_memRegion_96 (fsp : BitVec 64) (s0 : State) :
    savedRegsAt fsp s0 ⊢ memRegion (fsp + 448#64) 96 := by
  rw [show (96 : Nat) = 8 * 12 by rfl, ProofLib.memRegion_cells (fsp + 448#64) 12 (by decide)]
  simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
    fsp_448_add_8, fsp_456_add_8, fsp_464_add_8, fsp_472_add_8, fsp_480_add_8,
    fsp_488_add_8, fsp_496_add_8, fsp_504_add_8, fsp_512_add_8, fsp_520_add_8,
    fsp_528_add_8, ← sepExists_sepConj_left]
  unfold savedRegsAt
  exact sepConj_mono (Entails.sepExists_right _ (Entails.refl _)) (sepConj_mono (Entails.sepExists_right _ (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right _ (Entails.refl _)) (sepConj_mono (Entails.sepExists_right _ (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right _ (Entails.refl _)) (sepConj_mono (Entails.sepExists_right _ (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right _ (Entails.refl _)) (sepConj_mono (Entails.sepExists_right _ (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right _ (Entails.refl _)) (sepConj_mono (Entails.sepExists_right _ (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right _ (Entails.refl _)) (Entails.sepExists_right _ (Entails.refl _))))))))))))

theorem stackAt_fromPbCoreStack_split (sp : BitVec 64) :
    stackAt sp fromPbCoreStack =
      stackAt (sp - 544#64) dropGluePoly16Stack ∗
        memRegion (sp - 544#64) 448 ∗
        memRegion ((sp - 544#64) + 448#64) 96 := by
  have h1 : fromPbCoreStack = dropGluePoly16Stack + 544 := by decide
  rw [h1]
  simp only [stackAt]
  rw [ProofLib.memRegion_split _ dropGluePoly16Stack 544 (by decide)]
  have e1 : sp - BitVec.ofNat 64 (dropGluePoly16Stack + 544) =
      sp - 544#64 - BitVec.ofNat 64 dropGluePoly16Stack := by
    dsimp only [dropGluePoly16Stack, dropStack32, allocHookStack]
    bv_omega
  have e2 : sp - BitVec.ofNat 64 (dropGluePoly16Stack + 544) + BitVec.ofNat 64 dropGluePoly16Stack =
      sp - 544#64 := by
    dsimp only [dropGluePoly16Stack, dropStack32, allocHookStack]
    bv_omega
  rw [e2, e1, show (544 : Nat) = 448 + 96 by rfl,
      ProofLib.memRegion_split (sp - 544#64) 448 96 (by decide)]

theorem savedRegsAt_restore_fromPbCoreStack (sp fsp : BitVec 64) (hfsp : fsp = sp - 544#64) (s0 : State) :
    savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗ stackAt fsp dropGluePoly16Stack ⊢
      stackAt sp fromPbCoreStack := by
  rw [hfsp, stackAt_fromPbCoreStack_split sp]
  refine Entails.trans (sepConj_mono_left (savedRegsAt_entails_memRegion_96 (sp - 544#64) s0)) ?_
  exact Entails.of_eq (by ac_rfl)

theorem stackAt_fromPbCoreStack_split_bottom_allocHook (sp : BitVec 64) :
    stackAt sp fromPbCoreStack =
      memRegion (sp - 4672#64) 576 ∗ stackAt sp allocHookStack := by
  have h : fromPbCoreStack = allocHookStack + 576 := by decide
  rw [h]
  exact stackAt_split_bottom sp allocHookStack 576 (by decide)

theorem fromPb_stackAt_dropGluePoly16_split_bottom (sp : BitVec 64) :
    stackAt sp dropGluePoly16Stack =
      memRegion (sp - 4128#64) 32 ∗ stackAt sp allocHookStack :=
  stackAt_split_bottom sp allocHookStack 32 (by decide)

/-- Conditional deallocation resource for the outer `Vec<Vec<u8>>` buffer (`sz = 24`, `align = 8`). -/
def vecVecU8BufDealloc (A : RustAlloc) (cap ptr : BitVec 64) : SepProp :=
  if (cap == 0#64) = true then emp
  else A.live ptr (cap.toNat * 24) 8 ∗ memRegion ptr (cap.toNat * 24)

theorem vecVecU8At_expose (A : RustAlloc) (pbA : BitVec 64) (bss : List (List (BitVec 8))) :
    vecVecU8At A pbA bss ⊢
      ∃∗ cap_pts : BitVec 64, ∃∗ ptsPtr : BitVec 64,
        ⌜bss.length ≤ cap_pts.toNat ∧ cap_pts.toNat * 24 < 2 ^ 63 ∧
          bss.length * 24 < 2 ^ 63 ∧ ptsPtr ≠ 0⌝ ∗
        (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
        ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 bss.length) ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr bss ∗
        (if cap_pts = 0 then emp
          else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (bss.length * 24)) ((cap_pts.toNat - bss.length) * 24)) := by
  unfold vecVecU8At vecOf
  apply Entails.sepExists_elim; intro cap_pts
  apply Entails.sepExists_elim; intro ptsPtr
  refine Entails.sepExists_right cap_pts (Entails.sepExists_right ptsPtr ?_)
  refine Entails.trans (DropGlueFacts.vecAt_expose_loop A 24 8 (fun bs addr => vecU8 A addr bs) pbA cap_pts ptsPtr bss) ?_
  apply Entails.pure_left; rintro ⟨hle, hcap_lt, hlen_lt, hptr⟩
  refine Entails.pure_right ⟨hle, hcap_lt, hlen_lt, hptr⟩ ?_
  exact Entails.of_eq (by ac_rfl)

theorem pbA_rejoin_40 (pbA cap_pts ptsPtr len_pts : BitVec 64) :
    (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ len_pts) ∗
      memRegion (pbA + 24#64) 16 ⊢
    memRegion pbA 40 := by
  have h1 := DropGlueFacts.header_cells_entails_memRegion_24 pbA cap_pts ptsPtr
  have h2 : ((pbA + 16#64) ↦₆₄ len_pts) ⊢ memRegion (pbA + 16#64) 8 :=
    ProofLib.pointsTo64_entails_memRegion (pbA + 16#64) len_pts
  rw [show (40 : Nat) = 24 + 16 by rfl, ProofLib.memRegion_split pbA 24 16 (by decide)]
  refine Entails.trans (Q :=
    ((pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ memRegion (pbA + 16#64) 8) ∗
      memRegion (pbA + 24#64) 16) ?_ (sepConj_mono_left h1)
  exact replace_sub_entails h2
    ((pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ memRegion (pbA + 24#64) 16)
    (by ac_rfl) (by ac_rfl)

theorem pbA_tail_entails_memRegion_16 (pbA : BitVec 64) (ptsNeeded polys : BitVec 32) (isComplete : BitVec 8) :
    ((pbA + 24#64) ↦₃₂ ptsNeeded) ∗ ((pbA + 28#64) ↦₃₂ polys) ∗
      ((pbA + 32#64) ↦₈ isComplete) ∗ memRegion (pbA + 33#64) 7 ⊢
    memRegion (pbA + 24#64) 16 := by
  have h28 : (pbA + 24#64) + 4#64 = pbA + 28#64 := by bv_omega
  have h32 : (pbA + 28#64) + 4#64 = pbA + 32#64 := by bv_omega
  have h33 : (pbA + 32#64) + 1#64 = pbA + 33#64 := by bv_omega
  rw [show (16 : Nat) = 4 + (4 + (1 + 7)) by rfl,
      ProofLib.memRegion_split (pbA + 24#64) 4 12 (by decide), h28,
      ProofLib.memRegion_split (pbA + 28#64) 4 8 (by decide), h32,
      ProofLib.memRegion_split (pbA + 32#64) 1 7 (by decide), h33]
  exact sepConj_mono (ProofLib.pointsTo32_entails_memRegion (pbA + 24#64) ptsNeeded)
    (sepConj_mono (ProofLib.pointsTo32_entails_memRegion (pbA + 28#64) polys)
      (sepConj_mono_left (ProofLib.pointsTo8_entails_memRegion (pbA + 32#64) isComplete)))

theorem memRegion_400_split_err (out : BitVec 64) :
    memRegion out 400 =
      (∃∗ d0 : BitVec 64, out ↦₆₄ d0) ∗
      (∃∗ b8 : BitVec 8, (out + 8#64) ↦₈ b8) ∗
      memRegion (out + 9#64) 391 := by
  have h9 : (out + 8#64) + 1#64 = out + 9#64 := by bv_omega
  rw [show (400 : Nat) = 8 + (1 + 391) by rfl,
      ProofLib.memRegion_split out 8 392 (by decide),
      ProofLib.memRegion_split (out + 8#64) 1 391 (by decide), h9,
      ProofLib.memRegion_eight, ProofLib.memRegion_one]

/-! ## Shared Epilogue Tails (`+1244 -> s0.lr`, `+828 -> s0.lr`, `+820 -> s0.lr`, `+1236 -> s0.lr`) -/

@[local arm64_norm, local wp_norm]
theorem cap_add_lsl1_lsl3_toNat {cap : BitVec 64} (h : cap.toNat * 24 < 2 ^ 63) :
    ((cap + (cap <<< 1#64)) <<< 3#64).toNat = cap.toNat * 24 := by
  have h1 : cap <<< 1#64 = cap + cap := by bv_bits
  have h2 (x : BitVec 64) : x <<< 3#64 = (x + x) + (x + x) + ((x + x) + (x + x)) := by bv_bits
  rw [h2, h1]
  bv_omega

@[local arm64_norm, local wp_norm]
theorem cap_add_lsl1_ubfm_toNat {cap : BitVec 64} (h : cap.toNat * 24 < 2 ^ 63) :
    (BitVec.setWidth 64 (BitVec.extractLsb' 0 61 (cap + (cap <<< 1#64))) <<< 3#64).toNat =
      cap.toNat * 24 := by
  have hex : BitVec.setWidth 64 (BitVec.extractLsb' 0 61 (cap + (cap <<< 1#64))) <<< 3#64 =
      (cap + (cap <<< 1#64)) <<< 3#64 := by bv_bits
  rw [hex]
  exact cap_add_lsl1_lsl3_toNat h

/-- Return epilogue at `+1244 -> s0.lr` (when `cap_pts = 0`):
    restores `sp := s0.sp` and `x19..x30` from `savedRegsAt fsp s0` and returns to `s0.lr`. -/
theorem fromPb_tail_ret_1244_sepWP {b : BitVec 64}
    {ext : String → Option (State → State)}
    (s0 : State) (fsp : BitVec 64)
    (hfsp : HiddenEq fsp (s0.sp - 544#64))
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 1244#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) (htrace : s.trace = s0.trace) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗ stackAt fsp dropGluePoly16Stack ∗ Frame)
      (fun sf P' =>
        (P' ⊢ stackAt s0.sp fromPbCoreStack ∗ Frame) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  from_pb_fetches_range b (Rust.withPanics ext) 1244 32
  dsimp only [tripleRatchetProgAtExt, fromPbDecName, savedRegsAt,
    Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
    Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30,
    BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
  examples_hide_fetches
  have hsp448_al : ((fsp + 448#64) &&& 15#64 == 0#64) = true := by revert hfsp_align; bv_bits
  have hsp_ret : fsp + 544#64 = s0.sp := by rw [hfsp.eq]; bv_omega
  wp_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨?_, by simp [wp_norm, arm64_norm, hsp, hsp_ret], ?_, by simp [wp_norm, arm64_norm, htrace]⟩
  · refine Entails.trans ?_ (sepConj_mono_left (savedRegsAt_restore_fromPbCoreStack s0.sp fsp hfsp.eq s0))
    unfold savedRegsAt
    dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
      Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
    exact Entails.of_eq (by ac_rfl)
  · unfold CalleeSavedPreserved; simp [wp_norm, arm64_norm, *]

/-- Tail-call dealloc epilogue at `+828 -> s0.lr` (when `cap_pts ≠ 0`):
    computes `24 * cap_pts`, restores `sp := s0.sp` and `x19..x30`, and tail-calls `b __rust_dealloc` at `+872`. -/
theorem fromPb_tail_dealloc_828_sepWP {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hdealloc_ok : DeallocOkExt b A ext)
    (s0 : State) (fsp ptsPtr cap_pts : BitVec 64) (hfsp : HiddenEq fsp (s0.sp - 544#64))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hcap_bound : cap_pts.toNat * 24 < 2 ^ 63) (s : State) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 828#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx8 : s.readReg64 .x8 = cap_pts) (hx21 : s.readReg64 .x21 = ptsPtr)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) (htrace : s.trace = s0.trace) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.live ptsPtr (cap_pts.toNat * 24) 8 ∗ memRegion ptsPtr (cap_pts.toNat * 24) ∗
        savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗ A.pool ∗ stackAt fsp dropGluePoly16Stack ∗ Frame)
      (fun sf P' =>
        (P' ⊢ A.pool ∗ stackAt s0.sp fromPbCoreStack ∗ Frame) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hdealloc := sub_ok_at_of_fnAddr hdealloc_ok fromPbDecName
    (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<spqr::encoding::polynomial::PolyDecoder>::from_pb"))
    (by rw [decoderFromPb_fnOff]; simp only [arm64_norm])
  simp only [rustDeallocSpec] at hdealloc
  have hpre_dealloc :
      A.live ptsPtr (cap_pts.toNat * 24) 8 ∗ memRegion ptsPtr (cap_pts.toNat * 24) ∗
        savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗ A.pool ∗ stackAt fsp dropGluePoly16Stack ∗ Frame ⊢
      A.live ptsPtr (cap_pts.toNat * 24) 8 ∗ memRegion ptsPtr (cap_pts.toNat * 24) ∗
        A.pool ∗ stackAt s0.sp allocHookStack ∗ (memRegion (s0.sp - 4672#64) 576 ∗ Frame) := by
    have hrest := savedRegsAt_restore_fromPbCoreStack s0.sp fsp hfsp.eq s0
    rw [stackAt_fromPbCoreStack_split_bottom_allocHook s0.sp] at hrest
    exact replace_sub_entails hrest
      (A.live ptsPtr (cap_pts.toNat * 24) 8 ∗ memRegion ptsPtr (cap_pts.toNat * 24) ∗ A.pool ∗ Frame)
      (by ac_rfl) (by ac_rfl)
  have hpost_dealloc :
      A.pool ∗ stackAt s0.sp allocHookStack ∗ (memRegion (s0.sp - 4672#64) 576 ∗ Frame) ⊢
      A.pool ∗ stackAt s0.sp fromPbCoreStack ∗ Frame := by
    rw [stackAt_fromPbCoreStack_split_bottom_allocHook s0.sp]; exact Entails.of_eq (by ac_rfl)
  from_pb_fetches_range b (Rust.withPanics ext) 828 48
  dsimp only [tripleRatchetProgAtExt, fromPbDecName, savedRegsAt,
    Reg.x8, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
    Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30,
    BitVec.ofNat_eq_ofNat] at hdealloc hpre_dealloc hpc hx8 hx21 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
  examples_hide_fetches
  have hsp448_al : ((fsp + 448#64) &&& 15#64 == 0#64) = true := by revert hfsp_align; bv_bits
  have hsp_ret : fsp + 544#64 = s0.sp := by rw [hfsp.eq]; bv_omega
  have hmul24 := cap_add_lsl1_ubfm_toNat hcap_bound
  have hmul24' := cap_add_lsl1_lsl3_toNat hcap_bound
  wp_steps 12
  refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (by ac_rfl)) hpre_dealloc) ?_
  wp_apply; refine SepWP.weaken_pre hpost_dealloc ?_; wp_done

/-- Shared tail at `+820 -> s0.lr` (`x20 = pbA`, `x21 = ptsPtr`):
    loads `cap_pts ← [pbA]` and either returns via `+1244` (if `cap_pts = 0`)
    or tail-calls `__rust_dealloc` via `+828` (if `cap_pts ≠ 0`). -/
theorem fromPb_tail_820_sepWP {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (s0 : State) (fsp pbA ptsPtr cap_pts : BitVec 64) (hfsp : HiddenEq fsp (s0.sp - 544#64))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hcap_bound : cap_pts.toNat * 24 < 2 ^ 63) (s : State) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 820#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx20 : s.readReg64 .x20 = pbA) (hx21 : s.readReg64 .x21 = ptsPtr)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) (htrace : s.trace = s0.trace) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      ((pbA ↦₆₄ cap_pts) ∗ vecVecU8BufDealloc A cap_pts ptsPtr ∗
        savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗ A.pool ∗ stackAt fsp dropGluePoly16Stack ∗ Frame)
      (fun sf P' =>
        (P' ⊢ (pbA ↦₆₄ cap_pts) ∗ A.pool ∗ stackAt s0.sp fromPbCoreStack ∗ Frame) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  unfold vecVecU8BufDealloc
  by_cases hcap0 : (cap_pts == 0#64) = true
  · simp only [hcap0, ↓reduceIte, emp_sepConj]
    refine DropGlueFacts.seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 1244#64)
      (P_mid := savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗ stackAt fsp dropGluePoly16Stack ∗
        ((pbA ↦₆₄ cap_pts) ∗ A.pool ∗ Frame))
      (Q := fun sm => sm.sp = fsp ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
    · from_pb_fetches_range b (Rust.withPanics ext) 820 8
      dsimp only [tripleRatchetProgAtExt, fromPbDecName, Reg.x20, BitVec.ofNat_eq_ofNat] at hpc hx20 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
      examples_hide_fetches; wp_steps; wp_done
    · intro sm hpcm hrunm ⟨hspm, hvregsm, htrm⟩
      refine SepWP.strengthen_entails_const (Entails.of_eq (by ac_rfl))
        (fromPb_tail_ret_1244_sepWP s0 fsp hfsp hfsp_align sm _ hpcm hrunm hspm hvregsm htrm)
  · have hcap_beq : (cap_pts == 0#64) = false := Bool.eq_false_iff.mpr hcap0
    simp only [hcap_beq, Bool.false_eq_true, ↓reduceIte]
    refine DropGlueFacts.seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 828#64)
      (P_mid := A.live ptsPtr (cap_pts.toNat * 24) 8 ∗ memRegion ptsPtr (cap_pts.toNat * 24) ∗
        savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗
        A.pool ∗ stackAt fsp dropGluePoly16Stack ∗ ((pbA ↦₆₄ cap_pts) ∗ Frame))
      (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x8 = cap_pts ∧ sm.readReg64 .x21 = ptsPtr ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
    · from_pb_fetches_range b (Rust.withPanics ext) 820 8
      dsimp only [tripleRatchetProgAtExt, fromPbDecName, Reg.x8, Reg.x20, Reg.x21, BitVec.ofNat_eq_ofNat] at hpc hx20 hx21 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
      examples_hide_fetches; wp_steps; wp_done
    · intro sm hpcm hrunm ⟨hspm, hx8m, hx21m, hvregsm, htrm⟩
      refine SepWP.strengthen_entails_const (Entails.of_eq (by ac_rfl))
        (fromPb_tail_dealloc_828_sepWP hdealloc s0 fsp ptsPtr cap_pts hfsp hsp0_align hfsp_align hcap_bound
          sm _ hpcm hrunm hspm hx8m hx21m hvregsm htrm)

/-- Shared tail at `+1236 -> s0.lr` (`x19 = pbA`, `x21 = ptsPtr`, used by the success path),
    generalised over `DeallocOkExt`. -/
theorem fromPb_tail_1236_sepWP_dealloc {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (s0 : State) (fsp pbA ptsPtr cap_pts : BitVec 64) (hfsp : HiddenEq fsp (s0.sp - 544#64))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hcap_bound : cap_pts.toNat * 24 < 2 ^ 63) (s : State) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 1236#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = pbA) (hx21 : s.readReg64 .x21 = ptsPtr)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) (htrace : s.trace = s0.trace) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      ((pbA ↦₆₄ cap_pts) ∗ vecVecU8BufDealloc A cap_pts ptsPtr ∗
        savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗ A.pool ∗ stackAt fsp dropGluePoly16Stack ∗ Frame)
      (fun sf P' =>
        (P' ⊢ (pbA ↦₆₄ cap_pts) ∗ A.pool ∗ stackAt s0.sp fromPbCoreStack ∗ Frame) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  unfold vecVecU8BufDealloc
  by_cases hcap0 : (cap_pts == 0#64) = true
  · simp only [hcap0, ↓reduceIte, emp_sepConj]
    refine DropGlueFacts.seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 1244#64)
      (P_mid := savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗ stackAt fsp dropGluePoly16Stack ∗
        ((pbA ↦₆₄ cap_pts) ∗ A.pool ∗ Frame))
      (Q := fun sm => sm.sp = fsp ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
    · from_pb_fetches_range b (Rust.withPanics ext) 1236 8
      dsimp only [tripleRatchetProgAtExt, fromPbDecName, Reg.x19, BitVec.ofNat_eq_ofNat] at hpc hx19 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
      examples_hide_fetches; wp_steps; wp_done
    · intro sm hpcm hrunm ⟨hspm, hvregsm, htrm⟩
      refine SepWP.strengthen_entails_const (Entails.of_eq (by ac_rfl))
        (fromPb_tail_ret_1244_sepWP s0 fsp hfsp hfsp_align sm _ hpcm hrunm hspm hvregsm htrm)
  · have hcap_beq : (cap_pts == 0#64) = false := Bool.eq_false_iff.mpr hcap0
    simp only [hcap_beq, Bool.false_eq_true, ↓reduceIte]
    refine DropGlueFacts.seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 828#64)
      (P_mid := A.live ptsPtr (cap_pts.toNat * 24) 8 ∗ memRegion ptsPtr (cap_pts.toNat * 24) ∗
        savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗
        A.pool ∗ stackAt fsp dropGluePoly16Stack ∗ ((pbA ↦₆₄ cap_pts) ∗ Frame))
      (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x8 = cap_pts ∧ sm.readReg64 .x21 = ptsPtr ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
    · from_pb_fetches_range b (Rust.withPanics ext) 1236 8
      dsimp only [tripleRatchetProgAtExt, fromPbDecName, Reg.x8, Reg.x19, Reg.x21, BitVec.ofNat_eq_ofNat] at hpc hx19 hx21 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
      examples_hide_fetches; wp_steps; wp_done
    · intro sm hpcm hrunm ⟨hspm, hx8m, hx21m, hvregsm, htrm⟩
      refine SepWP.strengthen_entails_const (Entails.of_eq (by ac_rfl))
        (fromPb_tail_dealloc_828_sepWP hdealloc s0 fsp ptsPtr cap_pts hfsp hsp0_align hfsp_align hcap_bound
          sm _ hpcm hrunm hspm hx8m hx21m hvregsm htrm)

theorem fromPb_tail_1236_sepWP {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    (s0 : State) (fsp pbA ptsPtr cap_pts : BitVec 64) (hfsp : HiddenEq fsp (s0.sp - 544#64))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hcap_bound : cap_pts.toNat * 24 < 2 ^ 63) (s : State) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 1236#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = pbA) (hx21 : s.readReg64 .x21 = ptsPtr)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) (htrace : s.trace = s0.trace) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      ((pbA ↦₆₄ cap_pts) ∗ vecVecU8BufDealloc A cap_pts ptsPtr ∗
        savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗ A.pool ∗ stackAt fsp dropGluePoly16Stack ∗ Frame)
      (fun sf P' =>
        (P' ⊢ (pbA ↦₆₄ cap_pts) ∗ A.pool ∗ stackAt s0.sp fromPbCoreStack ∗ Frame) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  fromPb_tail_1236_sepWP_dealloc hA.dealloc s0 fsp pbA ptsPtr cap_pts hfsp hsp0_align hfsp_align
    hcap_bound s Frame hpc hrun hsp hx19 hx21 hvregs htrace

/-! ## `Vec<u8>` Drop Loop (`+776 / +796 -> +820`) -/

@[local arm64_norm, local wp_norm]
theorem cur_add8_sub8 (cur : BitVec 64) :
    (cur + 8#64) + 18446744073709551608#64 = cur := by bv_omega

@[local arm64_norm, local wp_norm]
theorem cur_add8_add24 (cur : BitVec 64) :
    (cur + 8#64) + 24#64 = (cur + 24#64) + 8#64 := by bv_omega

theorem ofNat_succ_sub_one_eq (n : Nat) :
    BitVec.ofNat 64 (n + 1) - 1#64 = BitVec.ofNat 64 n := by
  rw [BitVec.ofNat_add, BitVec.add_sub_cancel]

/-- One iteration of the `Vec<u8>` drop loop (`+796 -> +784`):
    deallocates the `Vec<u8>` at `cur` (`x19 = cur + 8#64`) and leaves `memRegion cur 24`. -/
theorem fromPb_drop_vec_u8_one_sepWP {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hdealloc_ok : DeallocOkExt b A ext)
    (s0 : State) (fsp pbA ptsPtr cur cnt : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (bs : List (BitVec 8))
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 796#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = cur + 8#64) (hx20 : s.readReg64 .x20 = pbA)
    (hx21 : s.readReg64 .x21 = ptsPtr) (hx24 : s.readReg64 .x24 = cnt)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) (htrace : s.trace = s0.trace) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 784#64) s
      (vecU8 A cur bs ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x19 = cur + 8#64 ∧ sm.readReg64 .x20 = pbA ∧
        sm.readReg64 .x21 = ptsPtr ∧ sm.readReg64 .x24 = cnt ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) := by
  have hdealloc := sub_ok_at_of_fnAddr hdealloc_ok fromPbDecName
    (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<spqr::encoding::polynomial::PolyDecoder>::from_pb"))
    (by rw [decoderFromPb_fnOff]; simp only [arm64_norm])
  simp only [rustDeallocSpec] at hdealloc
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A cur bs)) ?_
  apply SepWP.exists_sepConj_left; intro cap
  apply SepWP.exists_sepConj_left; intro ptr
  have hpost24 :
      ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ ptr) ∗ memRegion (cur + 16#64) 8) ∗
        (A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ⊢
      memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame := by
    refine Entails.trans (sepConj_mono_left (DropGlueFacts.header_cells_entails_memRegion_24 cur cap ptr)) ?_
    exact Entails.of_eq (by ac_rfl)
  dsimp only [vecCapPtrDealloc]
  from_pb_fetches_range b (Rust.withPanics ext) 796 24
  dsimp only [tripleRatchetProgAtExt, fromPbDecName,
    Reg.x19, Reg.x20, Reg.x21, Reg.x24, BitVec.ofNat_eq_ofNat] at hdealloc hpc hx19 hx20 hx21 hx24 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
  examples_hide_fetches
  by_cases hcap : (cap == 0#64) = true
  · simp only [hcap, ↓reduceIte, sepConj_emp]
    refine SepWP.strengthen_entails_const hpost24 ?_; wp_steps; wp_done
  · have hcap_f : (cap == 0#64) = false := Bool.eq_false_iff.mpr hcap
    simp only [hcap_f, Bool.false_eq_true, ↓reduceIte]
    refine SepWP.strengthen_entails_const hpost24 ?_
    wp_steps 5; wp_apply; wp_steps
    refine DropGlueFacts.align_pre (by rw [hsp]; ac_rfl) ?_; wp_done

/-- Loop at `+796 -> +820`: deallocates a non-empty `arrayAt (vecU8 A) 24 cur rem` into `memRegion cur (rem.length * 24)`. -/
theorem fromPb_drop_vec_u8_loop_sepWP {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (s0 : State) (fsp pbA ptsPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rem : List (List (BitVec 8))) (hrem_ne : rem ≠ [])
      (hlen_bound : rem.length * 24 < 2 ^ 63) (cur : BitVec 64) (s : State) (Frame : SepProp),
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 796#64 →
      s.status = .Running → s.sp = fsp →
      s.readReg64 .x19 = cur + 8#64 → s.readReg64 .x20 = pbA →
      s.readReg64 .x21 = ptsPtr → s.readReg64 .x24 = BitVec.ofNat 64 rem.length →
      calleeSavedVRegs s = calleeSavedVRegs s0 → s.trace = s0.trace →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 820#64) s
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 cur rem ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rem.length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          sm.sp = fsp ∧ sm.readReg64 .x20 = pbA ∧ sm.readReg64 .x21 = ptsPtr ∧
          calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace)
  | [], hrem_ne, _, _, _, _, _, _, _, _, _, _, _, _, _ => nomatch hrem_ne rfl
  | [bs], _, _, cur, s, Frame, hpc, hrun, hsp, hx19, hx20, hx21, hx24, hvregs, htr => by
    conv => arg 4; simp only [arrayAt_cons, arrayAt_nil, sepConj_emp]
    dsimp only [List.length_singleton, BitVec.ofNat_eq_ofNat] at hx24 ⊢
    refine DropGlueFacts.seq_clean
      (fromPb_drop_vec_u8_one_sepWP hdealloc s0 fsp pbA ptsPtr cur 1#64 hfsp_align bs s Frame
        hpc hrun hsp hx19 hx20 hx21 hx24 hvregs htr) ?_
    intro s1 hpc1 hrun1 ⟨hsp1, hx19_1, hx20_1, hx21_1, hx24_1, hvregs1, htr1⟩
    from_pb_fetches_range b (Rust.withPanics ext) 784 12
    dsimp only [tripleRatchetProgAtExt, fromPbDecName,
      Reg.x19, Reg.x20, Reg.x21, Reg.x24, BitVec.ofNat_eq_ofNat] at hpc1 hx19_1 hx20_1 hx21_1 hx24_1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
    examples_hide_fetches; wp_steps; wp_done
  | bs :: bs2 :: rest, _, hlen_bound, cur, s, Frame, hpc, hrun, hsp, hx19, hx20, hx21, hx24, hvregs, htr => by
    have hrem'_ne : (bs2 :: rest) ≠ [] := List.cons_ne_nil bs2 rest
    have hrem'_pos : 0 < (bs2 :: rest).length := by simp
    have hrem'_bound : (bs2 :: rest).length * 24 < 2 ^ 63 := by
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at hlen_bound ⊢; omega
    have hcnt_sub : BitVec.ofNat 64 (bs :: bs2 :: rest).length - 1#64 = BitVec.ofNat 64 (bs2 :: rest).length := by
      dsimp only [List.length_cons]; exact ofNat_succ_sub_one_eq (bs2 :: rest).length
    have hcnt_ne0 : (BitVec.ofNat 64 (bs :: bs2 :: rest).length == 1#64) = false := by
      rw [beq_eq_false_iff_ne]; intro heq
      have h1 : (BitVec.ofNat 64 (bs :: bs2 :: rest).length).toNat = 1 := congrArg BitVec.toNat heq
      have hlt64 : (bs :: bs2 :: rest).length < 2 ^ 64 := by
        simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at hlen_bound ⊢; omega
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64] at h1; simp only [List.length_cons] at h1; omega
    conv => arg 4; rw [arrayAt_cons]
    refine align_pre_wp
      (DropGlueFacts.seq_clean
        (fromPb_drop_vec_u8_one_sepWP hdealloc s0 fsp pbA ptsPtr cur (BitVec.ofNat 64 (bs :: bs2 :: rest).length)
          hfsp_align bs s (arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) (bs2 :: rest) ∗ Frame)
          hpc hrun hsp hx19 hx20 hx21 hx24 hvregs htr) ?_)
      (by ac_rfl)
    intro s1 hpc1 hrun1 ⟨hsp1, hx19_1, hx20_1, hx21_1, hx24_1, hvregs1, htr1⟩
    refine DropGlueFacts.seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 796#64)
      (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) (bs2 :: rest) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ (memRegion cur 24 ∗ Frame))
      (Q := fun s2 =>
        s2.sp = fsp ∧ s2.readReg64 .x19 = (cur + 24#64) + 8#64 ∧
        s2.readReg64 .x20 = pbA ∧ s2.readReg64 .x21 = ptsPtr ∧
        s2.readReg64 .x24 = BitVec.ofNat 64 (bs2 :: rest).length ∧
        calleeSavedVRegs s2 = calleeSavedVRegs s0 ∧ s2.trace = s0.trace) ?_ ?_
    · from_pb_fetches_range b (Rust.withPanics ext) 784 12
      dsimp only [tripleRatchetProgAtExt, fromPbDecName,
        Reg.x19, Reg.x20, Reg.x21, Reg.x24, BitVec.ofNat_eq_ofNat] at hpc1 hx19_1 hx20_1 hx21_1 hx24_1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
      examples_hide_fetches; wp_steps
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
      refine ⟨Entails.of_eq (by ac_rfl), ?_⟩
      simp [wp_norm, arm64_norm, hcnt_sub, *]
    · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx20_2, hx21_2, hx24_2, hvregs2, htr2⟩
      have hpost_join :
          memRegion (cur + 24#64) ((bs2 :: rest).length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗
            (memRegion cur 24 ∗ Frame) ⊢
          memRegion cur ((bs :: bs2 :: rest).length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame := by
        have hlen_split : (bs :: bs2 :: rest).length * 24 = 24 + (bs2 :: rest).length * 24 := by
          simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega
        rw [hlen_split, ProofLib.memRegion_split cur 24 ((bs2 :: rest).length * 24) (by omega)]
        exact Entails.of_eq (by ac_rfl)
      exact SepWP.strengthen_entails_const hpost_join
        (fromPb_drop_vec_u8_loop_sepWP hdealloc s0 fsp pbA ptsPtr hfsp_align (bs2 :: rest) hrem'_ne hrem'_bound
          (cur + 24#64) s2 (memRegion cur 24 ∗ Frame)
          hpc2 hrun2 hsp2 hx19_2 hx20_2 hx21_2 hx24_2 hvregs2 htr2)

/-- Entry to the `Vec<u8>` drop loop at `+776 -> +820` (`add x19, x21, #8; b +796`). -/
theorem fromPb_drop_vec_u8_776_sepWP {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (s0 : State) (fsp pbA ptsPtr : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (rem : List (List (BitVec 8))) (hrem_ne : rem ≠ []) (hlen_bound : rem.length * 24 < 2 ^ 63)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 776#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx20 : s.readReg64 .x20 = pbA) (hx21 : s.readReg64 .x21 = ptsPtr)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 rem.length)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) (htrace : s.trace = s0.trace) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 820#64) s
      (arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr rem ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion ptsPtr (rem.length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x20 = pbA ∧ sm.readReg64 .x21 = ptsPtr ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) := by
  refine DropGlueFacts.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 796#64)
    (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr rem ∗
      A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm =>
      sm.sp = fsp ∧ sm.readReg64 .x19 = ptsPtr + 8#64 ∧
      sm.readReg64 .x20 = pbA ∧ sm.readReg64 .x21 = ptsPtr ∧
      sm.readReg64 .x24 = BitVec.ofNat 64 rem.length ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
  · from_pb_fetches_range b (Rust.withPanics ext) 776 8
    dsimp only [tripleRatchetProgAtExt, fromPbDecName,
      Reg.x19, Reg.x20, Reg.x21, Reg.x24, BitVec.ofNat_eq_ofNat] at hpc hx20 hx21 hx24 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
    examples_hide_fetches; wp_steps; wp_done
  · intro sm hpcm hrunm ⟨hspm, hx19m, hx20m, hx21m, hx24m, hvregsm, htrm⟩
    exact fromPb_drop_vec_u8_loop_sepWP hdealloc s0 fsp pbA ptsPtr hfsp_align rem hrem_ne hlen_bound
      ptsPtr sm Frame hpcm hrunm hspm hx19m hx20m hx21m hx24m hvregsm htrm

/-! ## Error Exit A (`+712 -> s0.lr`, when `pb.pts.length ≠ 16`) -/

/-- Error Exit A (`+712 -> s0.lr`, reached when `pb.pts.length ≠ 16`), generalised over `DeallocOkExt`. -/
theorem fromPb_error_exit_712_sepWP_dealloc {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (s0 : State) (fsp out pbA cap_pts ptsPtr : BitVec 64) (hfsp : HiddenEq fsp (s0.sp - 544#64))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (bss : List (List (BitVec 8))) (hle : bss.length ≤ cap_pts.toNat)
    (hcap_bound : cap_pts.toNat * 24 < 2 ^ 63) (hlen_bound : bss.length * 24 < 2 ^ 63)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 712#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out) (hx20 : s.readReg64 .x20 = pbA)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 bss.length)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) (htrace : s.trace = s0.trace) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion out 400 ∗
        (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
        ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 bss.length) ∗ memRegion (pbA + 24#64) 16 ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr bss ∗
        (if cap_pts = 0 then emp
          else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (bss.length * 24)) ((cap_pts.toNat - bss.length) * 24)) ∗
        savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗ A.pool ∗ stackAt fsp dropGluePoly16Stack ∗ Frame)
      (fun sf P' =>
        (P' ⊢ resultPolyDecoderFromPbAt A out (.error .serializationInvalid) ∗
          memRegion pbA 40 ∗ A.pool ∗ stackAt s0.sp fromPbCoreStack ∗ Frame) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  conv => arg 4; rw [memRegion_400_split_err out]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro d0
  apply ProofLib.SepWP.exists_left; intro b8
  have hrejoin_pb := pbA_rejoin_40 pbA cap_pts ptsPtr (BitVec.ofNat 64 bss.length)
  have hrejoin_buf := DropGlueFacts.memRegion_rejoin_vecBuf A 24 8 cap_pts ptsPtr bss.length hle hcap_bound
  by_cases hbss0 : bss.length = 0
  · have hbss_nil : bss = [] := List.eq_nil_of_length_eq_zero hbss0
    subst hbss_nil
    refine DropGlueFacts.seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 820#64)
      (P_mid := (pbA ↦₆₄ cap_pts) ∗ vecVecU8BufDealloc A cap_pts ptsPtr ∗
        savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗ A.pool ∗ stackAt fsp dropGluePoly16Stack ∗
        (resultPolyDecoderFromPbAt A out (.error .serializationInvalid) ∗
          ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 0#64) ∗
          memRegion (pbA + 24#64) 16 ∗ Frame))
      (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x20 = pbA ∧ sm.readReg64 .x21 = ptsPtr ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
    · from_pb_fetches_range b (Rust.withPanics ext) 712 28
      dsimp only [tripleRatchetProgAtExt, fromPbDecName,
        Reg.x0, Reg.x20, Reg.x21, Reg.x24, List.length_nil, BitVec.ofNat_eq_ofNat] at hpc hx0 hx20 hx24 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
      examples_hide_fetches; wp_steps
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
      refine ⟨?_, by simp [wp_norm, arm64_norm, *]⟩
      unfold resultPolyDecoderFromPbAt vecVecU8BufDealloc noneCap
      dsimp only [resultPolyDecoderErrByteOff, resultPolyDecoderErrTailSize, polynomialErrorByte,
        List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat]
      simp only [arrayAt_nil, BitVec.add_zero, emp_sepConj, beq_iff_eq]
      exact Entails.of_eq (by ac_rfl)
    · intro sm hpcm hrunm ⟨hspm, hx20m, hx21m, hvregsm, htrm⟩
      have hpost_final :
          (pbA ↦₆₄ cap_pts) ∗ A.pool ∗ stackAt s0.sp fromPbCoreStack ∗
            (resultPolyDecoderFromPbAt A out (.error .serializationInvalid) ∗
              ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 0#64) ∗
              memRegion (pbA + 24#64) 16 ∗ Frame) ⊢
          resultPolyDecoderFromPbAt A out (.error .serializationInvalid) ∗
            memRegion pbA 40 ∗ A.pool ∗ stackAt s0.sp fromPbCoreStack ∗ Frame :=
        replace_sub_entails hrejoin_pb
          (resultPolyDecoderFromPbAt A out (.error .serializationInvalid) ∗
            A.pool ∗ stackAt s0.sp fromPbCoreStack ∗ Frame) (by ac_rfl) (by ac_rfl)
      exact SepWP.strengthen_entails_const hpost_final
        (fromPb_tail_820_sepWP hdealloc s0 fsp pbA ptsPtr cap_pts hfsp hsp0_align hfsp_align hcap_bound
          sm _ hpcm hrunm hspm hx20m hx21m hvregsm htrm)
  · have hbss_ne : bss ≠ [] := by intro h; simp [h] at hbss0
    have hbeq0 : (BitVec.ofNat 64 bss.length == 0#64) = false :=
      ofNat_beq_zero_false (by omega) (by omega)
    rw [fromPb_stackAt_dropGluePoly16_split_bottom fsp]
    refine DropGlueFacts.seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 776#64)
      (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr bss ∗
        A.pool ∗ stackAt fsp allocHookStack ∗
        (resultPolyDecoderFromPbAt A out (.error .serializationInvalid) ∗
          (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
          ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 bss.length) ∗ memRegion (pbA + 24#64) 16 ∗
          (if cap_pts = 0 then emp
            else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
              memRegion (ptsPtr + BitVec.ofNat 64 (bss.length * 24)) ((cap_pts.toNat - bss.length) * 24)) ∗
          savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗ memRegion (fsp - 4128#64) 32 ∗ Frame))
      (Q := fun sm =>
        sm.sp = fsp ∧ sm.readReg64 .x20 = pbA ∧ sm.readReg64 .x21 = ptsPtr ∧
        sm.readReg64 .x24 = BitVec.ofNat 64 bss.length ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
    · from_pb_fetches_range b (Rust.withPanics ext) 712 24
      dsimp only [tripleRatchetProgAtExt, fromPbDecName,
        Reg.x0, Reg.x20, Reg.x21, Reg.x24, BitVec.ofNat_eq_ofNat] at hpc hx0 hx20 hx24 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
      examples_hide_fetches; wp_steps
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
      refine ⟨?_, by simp [wp_norm, arm64_norm, *]⟩
      unfold resultPolyDecoderFromPbAt noneCap
      dsimp only [resultPolyDecoderErrByteOff, resultPolyDecoderErrTailSize, polynomialErrorByte, BitVec.ofNat_eq_ofNat]
      exact Entails.of_eq (by ac_rfl)
    · intro s1 hpc1 hrun1 ⟨hsp1, hx20_1, hx21_1, hx24_1, hvregs1, htr1⟩
      refine DropGlueFacts.seq_clean
        (fromPb_drop_vec_u8_776_sepWP hdealloc s0 fsp pbA ptsPtr hfsp_align bss hbss_ne hlen_bound
          s1 _ hpc1 hrun1 hsp1 hx20_1 hx21_1 hx24_1 hvregs1 htr1) ?_
      intro s2 hpc2 hrun2 ⟨hsp2, hx20_2, hx21_2, hvregs2, htr2⟩
      have hpre_820 :
          memRegion ptsPtr (bss.length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗
            (resultPolyDecoderFromPbAt A out (.error .serializationInvalid) ∗
              (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
              ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 bss.length) ∗ memRegion (pbA + 24#64) 16 ∗
              (if cap_pts = 0 then emp
                else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
                  memRegion (ptsPtr + BitVec.ofNat 64 (bss.length * 24)) ((cap_pts.toNat - bss.length) * 24)) ∗
              savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗ memRegion (fsp - 4128#64) 32 ∗ Frame) ⊢
          (pbA ↦₆₄ cap_pts) ∗ vecVecU8BufDealloc A cap_pts ptsPtr ∗
            savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗ A.pool ∗ stackAt fsp dropGluePoly16Stack ∗
            (resultPolyDecoderFromPbAt A out (.error .serializationInvalid) ∗
              ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 bss.length) ∗
              memRegion (pbA + 24#64) 16 ∗ Frame) := by
        rw [fromPb_stackAt_dropGluePoly16_split_bottom fsp]; unfold vecVecU8BufDealloc
        exact replace_sub_entails hrejoin_buf
          ((pbA ↦₆₄ cap_pts) ∗ savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗
            A.pool ∗ memRegion (fsp - 4128#64) 32 ∗ stackAt fsp allocHookStack ∗
            resultPolyDecoderFromPbAt A out (.error .serializationInvalid) ∗
            ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 bss.length) ∗
            memRegion (pbA + 24#64) 16 ∗ Frame) (by ac_rfl) (by ac_rfl)
      have hpost_final :
          (pbA ↦₆₄ cap_pts) ∗ A.pool ∗ stackAt s0.sp fromPbCoreStack ∗
            (resultPolyDecoderFromPbAt A out (.error .serializationInvalid) ∗
              ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 bss.length) ∗
              memRegion (pbA + 24#64) 16 ∗ Frame) ⊢
          resultPolyDecoderFromPbAt A out (.error .serializationInvalid) ∗
            memRegion pbA 40 ∗ A.pool ∗ stackAt s0.sp fromPbCoreStack ∗ Frame :=
        replace_sub_entails hrejoin_pb
          (resultPolyDecoderFromPbAt A out (.error .serializationInvalid) ∗
            A.pool ∗ stackAt s0.sp fromPbCoreStack ∗ Frame) (by ac_rfl) (by ac_rfl)
      exact SepWP.weaken_pre hpre_820
        (SepWP.strengthen_entails_const hpost_final
          (fromPb_tail_820_sepWP hdealloc s0 fsp pbA ptsPtr cap_pts hfsp hsp0_align hfsp_align hcap_bound
            s2 _ hpc2 hrun2 hsp2 hx20_2 hx21_2 hvregs2 htr2))

theorem fromPb_error_exit_712_sepWP {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    (s0 : State) (fsp out pbA cap_pts ptsPtr : BitVec 64) (hfsp : HiddenEq fsp (s0.sp - 544#64))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (bss : List (List (BitVec 8))) (hle : bss.length ≤ cap_pts.toNat)
    (hcap_bound : cap_pts.toNat * 24 < 2 ^ 63) (hlen_bound : bss.length * 24 < 2 ^ 63)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 712#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out) (hx20 : s.readReg64 .x20 = pbA)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 bss.length)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) (htrace : s.trace = s0.trace) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion out 400 ∗
        (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
        ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 bss.length) ∗ memRegion (pbA + 24#64) 16 ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr bss ∗
        (if cap_pts = 0 then emp
          else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (bss.length * 24)) ((cap_pts.toNat - bss.length) * 24)) ∗
        savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗ A.pool ∗ stackAt fsp dropGluePoly16Stack ∗ Frame)
      (fun sf P' =>
        (P' ⊢ resultPolyDecoderFromPbAt A out (.error .serializationInvalid) ∗
          memRegion pbA 40 ∗ A.pool ∗ stackAt s0.sp fromPbCoreStack ∗ Frame) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  fromPb_error_exit_712_sepWP_dealloc hA.dealloc s0 fsp out pbA cap_pts ptsPtr hfsp hsp0_align
    hfsp_align bss hle hcap_bound hlen_bound s Frame hpc hrun hsp hx0 hx20 hx24 hvregs htrace

/-! ## Error Exit B (`+740 -> s0.lr`, when `pb.pts.length = 16` and some `pts.length % 4 ≠ 0`) -/

theorem drop_glue_sorted_set_pt16_ok_at_fromPb {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr fromPbDecName +
        BitVec.ofNat 64 (num% (2 ^ 64 -
          (ls_off% "<spqr::encoding::polynomial::PolyDecoder>::from_pb" -
           ls_off% "core::ptr::drop_glue::<[sorted_vec::SortedSet<spqr::encoding::polynomial::Pt>; 16]>"))))
      (dropGlueSortedSetPt16Spec A) := by
  have h := Drop.drop_glue_sorted_set_pt16_ok_ext hdealloc
  unfold dropProgAtExt at h
  have haddr : (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName +
      BitVec.ofNat 64 (num% (2 ^ 64 -
        (ls_off% "<spqr::encoding::polynomial::PolyDecoder>::from_pb" -
         ls_off% "core::ptr::drop_glue::<[sorted_vec::SortedSet<spqr::encoding::polynomial::Pt>; 16]>"))) =
      (tripleRatchetProgAtExt b ext).fnAddr dropSortedSetPt16Name := by
    simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase,
      decoderFromPb_fnOff, dropSortedSetPt16_fnOff, BitVec.ofNat_eq_ofNat]
    bv_omega
  rw [haddr]; exact h

theorem fsp_rejoin_448 (fsp out pbA ptsPtr w416 w424 w432 : BitVec 64) :
    memRegion fsp 8 ∗
      ((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
      memRegion (fsp + 32#64) 384 ∗
      ((fsp + 416#64) ↦₆₄ w416) ∗ ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
      memRegion (fsp + 440#64) 8 ⊢
    memRegion fsp 448 := by
  have h1 := ProofLib.pointsTo64_entails_memRegion (fsp + 8#64) out
  have h2 := ProofLib.pointsTo64_entails_memRegion (fsp + 16#64) pbA
  have h3 := ProofLib.pointsTo64_entails_memRegion (fsp + 24#64) ptsPtr
  have h4 := ProofLib.pointsTo64_entails_memRegion (fsp + 416#64) w416
  have h5 := ProofLib.pointsTo64_entails_memRegion (fsp + 424#64) w424
  have h6 := ProofLib.pointsTo64_entails_memRegion (fsp + 432#64) w432
  have ha16 : (fsp + 8#64) + 8#64 = fsp + 16#64 := by bv_omega
  have ha24 : (fsp + 16#64) + 8#64 = fsp + 24#64 := by bv_omega
  have ha32 : (fsp + 24#64) + 8#64 = fsp + 32#64 := by bv_omega
  have ha416 : (fsp + 32#64) + 384#64 = fsp + 416#64 := by bv_omega
  have ha424 : (fsp + 416#64) + 8#64 = fsp + 424#64 := by bv_omega
  have ha432 : (fsp + 424#64) + 8#64 = fsp + 432#64 := by bv_omega
  have ha440 : (fsp + 432#64) + 8#64 = fsp + 440#64 := by bv_omega
  rw [show (448 : Nat) = 8 + (8 + (8 + (8 + (384 + (8 + (8 + (8 + 8))))))) by rfl,
      ProofLib.memRegion_split fsp 8 440 (by decide),
      ProofLib.memRegion_split (fsp + 8#64) 8 432 (by decide), ha16,
      ProofLib.memRegion_split (fsp + 16#64) 8 424 (by decide), ha24,
      ProofLib.memRegion_split (fsp + 24#64) 8 416 (by decide), ha32,
      ProofLib.memRegion_split (fsp + 32#64) 384 32 (by decide), ha416,
      ProofLib.memRegion_split (fsp + 416#64) 8 24 (by decide), ha424,
      ProofLib.memRegion_split (fsp + 424#64) 8 16 (by decide), ha432,
      ProofLib.memRegion_split (fsp + 432#64) 8 8 (by decide), ha440]
  exact sepConj_mono_right (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3
    (sepConj_mono_right (sepConj_mono h4 (sepConj_mono h5 (sepConj_mono_left h6)))))))

/-- Error Exit B (`+740 -> s0.lr`, reached when `pb.pts.length = 16` and some `pts.length % 4 ≠ 0`),
    generalised over `DeallocOkExt`. -/
theorem fromPb_error_exit_740_sepWP_dealloc {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (s0 : State) (fsp out pbA cap_pts ptsPtr w416 w424 w432 : BitVec 64)
    (hfsp : HiddenEq fsp (s0.sp - 544#64))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (sets_err : List SortedSetPt) (hsets_len : sets_err.length = 16)
    (bss : List (List (BitVec 8))) (hbss_len : bss.length = 16)
    (hle : bss.length ≤ cap_pts.toNat) (hcap_bound : cap_pts.toNat * 24 < 2 ^ 63)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 740#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx21 : s.readReg64 .x21 = ptsPtr)
    (hx24 : s.readReg64 .x24 = 16#64) (hx29 : s.readReg64 .x29 = fsp + 448#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) (htrace : s.trace = s0.trace) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion out 400 ∗ memRegion fsp 8 ∗
        ((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
        sortedSetPtListOf A (fsp + 32#64) sets_err ∗
        ((fsp + 416#64) ↦₆₄ w416) ∗ ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
        memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
        (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
        memRegion (pbA + 24#64) 16 ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr bss ∗
        (if cap_pts = 0 then emp
          else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (bss.length * 24)) ((cap_pts.toNat - bss.length) * 24)) ∗
        memRegion (fsp - 4128#64) 32 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sf P' =>
        (P' ⊢ resultPolyDecoderFromPbAt A out (.error .serializationInvalid) ∗
          memRegion pbA 40 ∗ A.pool ∗ stackAt s0.sp fromPbCoreStack ∗ Frame) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hdrop := drop_glue_sorted_set_pt16_ok_at_fromPb hdealloc
  simp only [dropGlueSortedSetPt16Spec] at hdrop
  rw [sortedSetPtListOf_eq_vecPtListOf]
  conv => arg 4; rw [memRegion_400_split_err out]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro b8
  apply ProofLib.SepWP.exists_left; intro d0
  have hvecs_len : (sets_err.map SortedSetPt.vec).length = NUM_POLYS := by
    simp [hsets_len, NUM_POLYS, CHUNK_SIZE]
  refine align_pre_wp
    (DropGlueFacts.seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 776#64)
      (P := (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₈ b8) ∗ memRegion (out + 9#64) 391 ∗ memRegion fsp 8 ∗
        ((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
        vecPtListOf A (fsp + 32#64) (sets_err.map SortedSetPt.vec) ∗
        ((fsp + 416#64) ↦₆₄ w416) ∗ ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
        memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
        (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
        memRegion (pbA + 24#64) 16 ∗ arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr bss ∗
        (if cap_pts = 0 then emp
          else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (bss.length * 24)) ((cap_pts.toNat - bss.length) * 24)) ∗
        A.pool ∗ stackAt fsp dropGluePoly16Stack ∗ Frame)
      (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr bss ∗
        A.pool ∗ stackAt fsp allocHookStack ∗
        (resultPolyDecoderFromPbAt A out (.error .serializationInvalid) ∗
          memRegion fsp 448 ∗ savedRegsAt fsp s0 ∗
          (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
          memRegion (pbA + 24#64) 16 ∗
          (if cap_pts = 0 then emp
            else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
              memRegion (ptsPtr + BitVec.ofNat 64 (bss.length * 24)) ((cap_pts.toNat - bss.length) * 24)) ∗
          memRegion (fsp - 4128#64) 32 ∗ Frame))
      (Q := fun sm =>
        sm.sp = fsp ∧ sm.readReg64 .x20 = pbA ∧ sm.readReg64 .x21 = ptsPtr ∧
        sm.readReg64 .x24 = BitVec.ofNat 64 bss.length ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_)
    (by rw [fromPb_stackAt_dropGluePoly16_split_bottom fsp]; ac_rfl)
  · from_pb_fetches_range b (Rust.withPanics ext) 740 36
    dsimp only [tripleRatchetProgAtExt, fromPbDecName,
      Reg.x0, Reg.x20, Reg.x21, Reg.x24, Reg.x29, BitVec.ofNat_eq_ofNat] at hdrop hpc hx21 hx24 hx29 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
    examples_hide_fetches; wp_steps 7
    wp_call hdrop (⟨fsp + 32#64, sets_err.map SortedSetPt.vec⟩ : DropGlueSortedSetPt16Ghost)
    wp_steps
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_sf])
    have hsp_sf' : sf.sp = fsp := hsp_sf.trans (by simp [wp_norm, arm64_norm, hsp])
    refine ⟨?_, ?_⟩
    · rw [← hsp_sf, hsp_sf', fromPb_stackAt_dropGluePoly16_split_bottom fsp]
      unfold resultPolyDecoderFromPbAt noneCap
      dsimp only [resultPolyDecoderErrByteOff, resultPolyDecoderErrTailSize, polynomialErrorByte,
        polyArrayBytes, BitVec.ofNat_eq_ofNat]
      have hfsp448 := fsp_rejoin_448 fsp out pbA ptsPtr w416 w424 w432
      exact replace_sub_entails hfsp448
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr bss ∗
          A.pool ∗ stackAt fsp allocHookStack ∗
          (((out ↦₆₄ 18446744073709551615#64) ∗ ((out + 8#64) ↦₈ 2#8) ∗ memRegion (out + 9#64) 391) ∗
            savedRegsAt fsp s0 ∗
            (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
            memRegion (pbA + 24#64) 16 ∗
            (if cap_pts = 0 then emp
              else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
                memRegion (ptsPtr + BitVec.ofNat 64 (bss.length * 24)) ((cap_pts.toNat - bss.length) * 24)) ∗
            memRegion (fsp - 4128#64) 32 ∗ Frame)) (by ac_rfl) (by ac_rfl)
    · rw [hbss_len]; simp [wp_norm, arm64_norm, *]
  · intro s1 hpc1 hrun1 ⟨hsp1, hx20_1, hx21_1, hx24_1, hvregs1, htr1⟩
    have hbss_ne : bss ≠ [] := by intro h; simp [h] at hbss_len
    have hlen_bound : bss.length * 24 < 2 ^ 63 := by rw [hbss_len]; decide
    have hrejoin_pb := pbA_rejoin_40 pbA cap_pts ptsPtr 16#64
    have hrejoin_buf := DropGlueFacts.memRegion_rejoin_vecBuf A 24 8 cap_pts ptsPtr bss.length hle hcap_bound
    refine DropGlueFacts.seq_clean
      (fromPb_drop_vec_u8_776_sepWP hdealloc s0 fsp pbA ptsPtr hfsp_align bss hbss_ne hlen_bound
        s1 _ hpc1 hrun1 hsp1 hx20_1 hx21_1 hx24_1 hvregs1 htr1) ?_
    intro s2 hpc2 hrun2 ⟨hsp2, hx20_2, hx21_2, hvregs2, htr2⟩
    have hpre_820 :
        memRegion ptsPtr (bss.length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗
          (resultPolyDecoderFromPbAt A out (.error .serializationInvalid) ∗
            memRegion fsp 448 ∗ savedRegsAt fsp s0 ∗
            (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
            memRegion (pbA + 24#64) 16 ∗
            (if cap_pts = 0 then emp
              else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
                memRegion (ptsPtr + BitVec.ofNat 64 (bss.length * 24)) ((cap_pts.toNat - bss.length) * 24)) ∗
            memRegion (fsp - 4128#64) 32 ∗ Frame) ⊢
        (pbA ↦₆₄ cap_pts) ∗ vecVecU8BufDealloc A cap_pts ptsPtr ∗
          savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗ A.pool ∗ stackAt fsp dropGluePoly16Stack ∗
          (resultPolyDecoderFromPbAt A out (.error .serializationInvalid) ∗
            ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
            memRegion (pbA + 24#64) 16 ∗ Frame) := by
      rw [fromPb_stackAt_dropGluePoly16_split_bottom fsp]; unfold vecVecU8BufDealloc
      exact replace_sub_entails hrejoin_buf
        ((pbA ↦₆₄ cap_pts) ∗ savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗
          A.pool ∗ memRegion (fsp - 4128#64) 32 ∗ stackAt fsp allocHookStack ∗
          resultPolyDecoderFromPbAt A out (.error .serializationInvalid) ∗
          ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
          memRegion (pbA + 24#64) 16 ∗ Frame) (by ac_rfl) (by ac_rfl)
    have hpost_final :
        (pbA ↦₆₄ cap_pts) ∗ A.pool ∗ stackAt s0.sp fromPbCoreStack ∗
          (resultPolyDecoderFromPbAt A out (.error .serializationInvalid) ∗
            ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
            memRegion (pbA + 24#64) 16 ∗ Frame) ⊢
        resultPolyDecoderFromPbAt A out (.error .serializationInvalid) ∗
          memRegion pbA 40 ∗ A.pool ∗ stackAt s0.sp fromPbCoreStack ∗ Frame :=
      replace_sub_entails hrejoin_pb
        (resultPolyDecoderFromPbAt A out (.error .serializationInvalid) ∗
          A.pool ∗ stackAt s0.sp fromPbCoreStack ∗ Frame) (by ac_rfl) (by ac_rfl)
    exact SepWP.weaken_pre hpre_820
      (SepWP.strengthen_entails_const hpost_final
        (fromPb_tail_820_sepWP hdealloc s0 fsp pbA ptsPtr cap_pts hfsp hsp0_align hfsp_align hcap_bound
          s2 _ hpc2 hrun2 hsp2 hx20_2 hx21_2 hvregs2 htr2))

theorem fromPb_error_exit_740_sepWP {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    (s0 : State) (fsp out pbA cap_pts ptsPtr w416 w424 w432 : BitVec 64)
    (hfsp : HiddenEq fsp (s0.sp - 544#64))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (sets_err : List SortedSetPt) (hsets_len : sets_err.length = 16)
    (bss : List (List (BitVec 8))) (hbss_len : bss.length = 16)
    (hle : bss.length ≤ cap_pts.toNat) (hcap_bound : cap_pts.toNat * 24 < 2 ^ 63)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 740#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx21 : s.readReg64 .x21 = ptsPtr)
    (hx24 : s.readReg64 .x24 = 16#64) (hx29 : s.readReg64 .x29 = fsp + 448#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) (htrace : s.trace = s0.trace) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion out 400 ∗ memRegion fsp 8 ∗
        ((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
        sortedSetPtListOf A (fsp + 32#64) sets_err ∗
        ((fsp + 416#64) ↦₆₄ w416) ∗ ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
        memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
        (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
        memRegion (pbA + 24#64) 16 ∗ arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr bss ∗
        (if cap_pts = 0 then emp
          else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (bss.length * 24)) ((cap_pts.toNat - bss.length) * 24)) ∗
        memRegion (fsp - 4128#64) 32 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sf P' =>
        (P' ⊢ resultPolyDecoderFromPbAt A out (.error .serializationInvalid) ∗
          memRegion pbA 40 ∗ A.pool ∗ stackAt s0.sp fromPbCoreStack ∗ Frame) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  fromPb_error_exit_740_sepWP_dealloc hA.dealloc s0 fsp out pbA cap_pts ptsPtr w416 w424 w432 hfsp
    hsp0_align hfsp_align sets_err hsets_len bss hbss_len hle hcap_bound s Frame hpc hrun hsp hx21
    hx24 hx29 hvregs htrace

end CryptoVerification.SpqrV1.Poly.DecoderPb
