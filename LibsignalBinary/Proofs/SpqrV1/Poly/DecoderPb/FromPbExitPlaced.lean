/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbExit
import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbOuterPlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::encoding::polynomial::PolyDecoder>::from_pb`: Relocatable Outer Loop Induction and Error Exits

Relocatable `[LibsignalPlacement]` proofs of outer-loop induction, epilogue tails, the `Vec<u8>`
drop loop, and error exits A (`+712`) and B (`+740`) on Block `376`.
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
open CryptoVerification.SpqrV1.Alloc
  (spqrRustAllocSym spqrRustReallocSym spqrRustNoAllocShimSym
   spqrHandleErrorSym spqrMemcpySym spqrMemmoveSym)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  fsp_448_add_8 fsp_448_add_16 fsp_448_add_24 fsp_448_add_32 fsp_448_add_40 fsp_448_add_48
  fsp_448_add_56 fsp_448_add_64 fsp_448_add_72 fsp_448_add_80 fsp_448_add_88 fsp_448_add_96
  fsp_456_add_8 fsp_464_add_8 fsp_472_add_8 fsp_480_add_8 fsp_488_add_8 fsp_496_add_8
  fsp_504_add_8 fsp_512_add_8 fsp_520_add_8 fsp_528_add_8
  cap_add_lsl1_lsl3_toNat cap_add_lsl1_ubfm_toNat cur_add8_sub8 cur_add8_add24

/-! ## Placed Outer Loop Induction (`+204 -> +876` or `+740`) -/

theorem fromPb_outer_loop_placed_wpp [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveSpec 0))
    {Q : State → SepProp → Prop} {R : SepProp}
    (s0 : State) (fsp ptsPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rem : List (List (BitVec 8))) (hrem_ne : rem ≠ [])
      (i : Nat) (htot : i + rem.length = 16)
      (v416 v424 v432 : BitVec 64)
      (s : State) (Frame : SepProp),
      s.pc = (blkPl_376).base + 204#64 →
      s.status = .Running →
      s.sp = fsp →
      s.readReg64 .x19 = 24#64 →
      s.readReg64 .x21 = ptsPtr →
      s.readReg64 .x24 = 16#64 →
      s.readReg64 .x25 = BitVec.ofNat 64 i →
      s.readReg64 .x29 = fsp + 448#64 →
      s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      (∀ (sm : State) (w416 w424 w432 : BitVec 64),
        (∀ bs ∈ rem, bs.length % 4 = 0) →
        sm.pc = (blkPl_376).base + 876#64 →
        sm.status = .Running → sm.sp = fsp → sm.readReg64 .x21 = ptsPtr →
        sm.readReg64 .x24 = 16#64 → sm.readReg64 .x29 = fsp + 448#64 → sm.trace = s0.trace →
        calleeSavedVRegs sm = calleeSavedVRegs s0 →
        SepWPp ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) sm
          (((fsp + 24#64) ↦₆₄ ptsPtr) ∗ ((fsp + 416#64) ↦₆₄ w416) ∗
            ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
            sortedSetPtListOf A (fsp + 32#64 + BitVec.ofNat 64 (24 * i))
              (rem.map fun bs => pushChunks4Total bs { vec := [] }) ∗
            arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * i)) rem ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
          Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ fromPbOnPanic s0 sf ∗ R))) →
      (∀ (sm : State) (sets_err : List SortedSetPt) (w416 w424 w432 : BitVec 64),
        (∃ bs ∈ rem, bs.length % 4 ≠ 0) → sets_err.length = rem.length →
        sm.pc = (blkPl_376).base + 740#64 →
        sm.status = .Running → sm.sp = fsp → sm.readReg64 .x21 = ptsPtr →
        sm.readReg64 .x24 = 16#64 → sm.readReg64 .x29 = fsp + 448#64 → sm.trace = s0.trace →
        calleeSavedVRegs sm = calleeSavedVRegs s0 →
        SepWPp ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) sm
          (((fsp + 24#64) ↦₆₄ ptsPtr) ∗ ((fsp + 416#64) ↦₆₄ w416) ∗
            ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
            sortedSetPtListOf A (fsp + 32#64 + BitVec.ofNat 64 (24 * i)) sets_err ∗
            arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * i)) rem ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
          Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ fromPbOnPanic s0 sf ∗ R))) →
      SepWPp ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
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
        (fromPb_outer_alloc_and_push_placed_wpp h_panic hshim_sat halloc_sat hmemmove_sat
          s0 fsp ptsPtr hfsp_align i 0 (by omega) pts hmod4
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
        (fromPb_outer_invalid_mod4_placed_wpp s0 fsp ptsPtr i pts hmod4 s
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
        (fromPb_outer_alloc_and_push_placed_wpp h_panic hshim_sat halloc_sat hmemmove_sat
          s0 fsp ptsPtr hfsp_align i (pts2 :: rem').length
          (by simp at htot ⊢; omega) pts hmod4 v416 v424 v432 s
          (arrayAt (fun bs addr => vecU8 A addr bs) 24
            (ptsPtr + BitVec.ofNat 64 (24 * (i + 1))) (pts2 :: rem') ∗ Frame)
          hpc hrun hsp hx19 hx21 hx24 hx25 hx29 htr hvregs ?_)
        (by ac_rfl)
      intro sm w416 w424 w432 hpcm hrunm hspm hx19m hx21m hx24m hx25m hx29m htrm hvregsm
      simp only [hi1_ne, ↓reduceIte] at hpcm
      refine align_pre_wpp
        (fromPb_outer_loop_placed_wpp h_panic hshim_sat halloc_sat hmemmove_sat s0 fsp ptsPtr hfsp_align
          (pts2 :: rem') (List.cons_ne_nil pts2 rem') (i + 1) (by simp at htot ⊢; omega)
          w416 w424 w432 sm
          (sortedSetPtOf A (fsp + 32#64 + BitVec.ofNat 64 (24 * i))
            (pushChunks4Total pts { vec := [] }) ∗
            vecU8 A (ptsPtr + BitVec.ofNat 64 (24 * i)) pts ∗ Frame)
          hpcm hrunm hspm hx19m hx21m hx24m hx25m hx29m htrm hvregsm ?_ ?_)
        (by ac_rfl)
      · intro s_end u416 u424 u432 hall_rem hpc_end hrun_end hsp_end hx21_end hx24_end hx29_end htr_end hvregs_end
        have hall : ∀ bs ∈ (pts :: pts2 :: rem'), bs.length % 4 = 0 := by
          intro bs hbs; rcases List.mem_cons.mp hbs with rfl | hbs'
          · exact hmod4
          · exact hall_rem bs hbs'
        refine SepWPp.weaken_pre ?_
          (hok s_end u416 u424 u432 hall hpc_end hrun_end hsp_end hx21_end hx24_end hx29_end htr_end hvregs_end)
        rw [show sortedSetPtListOf A (fsp + 32#64 + BitVec.ofNat 64 (24 * i))
              ((pts :: pts2 :: rem').map fun bs => pushChunks4Total bs { vec := [] }) =
            sortedSetPtOf A (fsp + 32#64 + BitVec.ofNat 64 (24 * i)) (pushChunks4Total pts { vec := [] }) ∗
              sortedSetPtListOf A (fsp + 32#64 + BitVec.ofNat 64 (24 * i) + 24#64)
                ((pts2 :: rem').map fun bs => pushChunks4Total bs { vec := [] }) from rfl,
          hoff_out,
          show arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * i)) (pts :: pts2 :: rem') =
            vecU8 A (ptsPtr + BitVec.ofNat 64 (24 * i)) pts ∗
              arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * i) + 24#64) (pts2 :: rem') from rfl,
          hoff_in]
        exact Entails.of_eq (by ac_rfl)
      · intro s_err sets_rem u416 u424 u432 hex_rem hlen_rem hpc_err hrun_err hsp_err hx21_err hx24_err hx29_err htr_err hvregs_err
        rcases hex_rem with ⟨bs_bad, hbs_bad, hbad⟩
        have hex : ∃ bs ∈ (pts :: pts2 :: rem'), bs.length % 4 ≠ 0 :=
          ⟨bs_bad, List.mem_cons_of_mem pts hbs_bad, hbad⟩
        refine SepWPp.weaken_pre ?_
          (herr s_err (pushChunks4Total pts { vec := [] } :: sets_rem) u416 u424 u432
            hex (by simp [hlen_rem]) hpc_err hrun_err hsp_err hx21_err hx24_err hx29_err htr_err hvregs_err)
        rw [show sortedSetPtListOf A (fsp + 32#64 + BitVec.ofNat 64 (24 * i))
              (pushChunks4Total pts { vec := [] } :: sets_rem) =
            sortedSetPtOf A (fsp + 32#64 + BitVec.ofNat 64 (24 * i)) (pushChunks4Total pts { vec := [] }) ∗
              sortedSetPtListOf A (fsp + 32#64 + BitVec.ofNat 64 (24 * i) + 24#64) sets_rem from rfl,
          hoff_out,
          show arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * i)) (pts :: pts2 :: rem') =
            vecU8 A (ptsPtr + BitVec.ofNat 64 (24 * i)) pts ∗
              arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * i) + 24#64) (pts2 :: rem') from rfl,
          hoff_in]
        exact Entails.of_eq (by ac_rfl)
    · have hempty := emptySlotsAt_entails_sortedSetPtListOf A (pts :: pts2 :: rem').length
        (fsp + 32#64 + BitVec.ofNat 64 (24 * i))
      conv => arg 4; rw [arrayAt_cons, hoff_in]
      refine SepWPp.weaken_pre (replace_sub_entails hempty
        (vecU8 A (ptsPtr + BitVec.ofNat 64 (24 * i)) pts ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
          ((fsp + 416#64) ↦₆₄ v416) ∗ ((fsp + 424#64) ↦₆₄ v424) ∗ ((fsp + 432#64) ↦₆₄ v432) ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24
            (ptsPtr + BitVec.ofNat 64 (24 * (i + 1))) (pts2 :: rem') ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) (by ac_rfl) (by ac_rfl))
        (fromPb_outer_invalid_mod4_placed_wpp s0 fsp ptsPtr i pts hmod4 s
          (((fsp + 24#64) ↦₆₄ ptsPtr) ∗
            ((fsp + 416#64) ↦₆₄ v416) ∗ ((fsp + 424#64) ↦₆₄ v424) ∗ ((fsp + 432#64) ↦₆₄ v432) ∗
            sortedSetPtListOf A (fsp + 32#64 + BitVec.ofNat 64 (24 * i))
              (List.replicate (pts :: pts2 :: rem').length { vec := [] }) ∗
            arrayAt (fun bs addr => vecU8 A addr bs) 24
              (ptsPtr + BitVec.ofNat 64 (24 * (i + 1))) (pts2 :: rem') ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
          hpc hrun hsp hx19 hx21 hx24 hx25 hx29 htr hvregs ?_)
      intro sm hpcm hrunm hspm hx21m hx24m hx29m htrm hvregsm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (herr sm (List.replicate (pts :: pts2 :: rem').length { vec := [] }) v416 v424 v432
          ⟨pts, List.mem_cons_self, hmod4⟩ (by simp) hpcm hrunm hspm hx21m hx24m hx29m htrm hvregsm)
      simp only [arrayAt_cons, hoff_in]; ac_rfl

/-! ## Placed Shared Epilogue Tails (`+1244 -> s0.lr`, `+828 -> s0.lr`, `+820 -> s0.lr`, `+1236 -> s0.lr`) -/

theorem fromPb_tail_ret_1244_placed_sepWP [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 : State) (fsp : BitVec 64)
    (hfsp : HiddenEq fsp (s0.sp - 544#64))
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_376).base + 1244#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) (htrace : s.trace = s0.trace) :
    SepWP ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗ stackAt fsp dropGluePoly16Stack ∗ Frame)
      (fun sf P' =>
        (P' ⊢ stackAt s0.sp fromPbCoreStack ∗ Frame) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  dsimp only [savedRegsAt,
    Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
    Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30,
    BitVec.ofNat_eq_ofNat] at hpc ⊢
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

theorem fromPb_tail_dealloc_828_placed_sepWP [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A))
    (s0 : State) (fsp ptsPtr cap_pts : BitVec 64)
    (hfsp : HiddenEq fsp (s0.sp - 544#64))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hcap_bound : cap_pts.toNat * 24 < 2 ^ 63)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_376).base + 828#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx8 : s.readReg64 .x8 = cap_pts) (hx21 : s.readReg64 .x21 = ptsPtr)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (htrace : s.trace = s0.trace) :
    SepWP ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.live ptsPtr (cap_pts.toNat * 24) 8 ∗ memRegion ptsPtr (cap_pts.toNat * 24) ∗
        savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗
        A.pool ∗ stackAt fsp dropGluePoly16Stack ∗ Frame)
      (fun sf P' =>
        (P' ⊢ A.pool ∗ stackAt s0.sp fromPbCoreStack ∗ Frame) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  simp only [rustDeallocSpec, spqrRustDeallocSym] at hdealloc
  have hpre_dealloc :
      A.live ptsPtr (cap_pts.toNat * 24) 8 ∗ memRegion ptsPtr (cap_pts.toNat * 24) ∗
        savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗
        A.pool ∗ stackAt fsp dropGluePoly16Stack ∗ Frame ⊢
      A.live ptsPtr (cap_pts.toNat * 24) 8 ∗ memRegion ptsPtr (cap_pts.toNat * 24) ∗
        A.pool ∗ stackAt s0.sp allocHookStack ∗
        (memRegion (s0.sp - 4672#64) 576 ∗ Frame) := by
    have hrest := savedRegsAt_restore_fromPbCoreStack s0.sp fsp hfsp.eq s0
    rw [stackAt_fromPbCoreStack_split_bottom_allocHook s0.sp] at hrest
    exact replace_sub_entails hrest
      (A.live ptsPtr (cap_pts.toNat * 24) 8 ∗ memRegion ptsPtr (cap_pts.toNat * 24) ∗ A.pool ∗ Frame)
      (by ac_rfl) (by ac_rfl)
  have hpost_dealloc :
      A.pool ∗ stackAt s0.sp allocHookStack ∗ (memRegion (s0.sp - 4672#64) 576 ∗ Frame) ⊢
      A.pool ∗ stackAt s0.sp fromPbCoreStack ∗ Frame := by
    rw [stackAt_fromPbCoreStack_split_bottom_allocHook s0.sp]
    exact Entails.of_eq (by ac_rfl)
  dsimp only [savedRegsAt,
    Reg.x8, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
    Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30,
    BitVec.ofNat_eq_ofNat] at hdealloc hpre_dealloc hpc hx8 hx21 ⊢
  have hsp448_al : ((fsp + 448#64) &&& 15#64 == 0#64) = true := by revert hfsp_align; bv_bits
  have hsp_ret : fsp + 544#64 = s0.sp := by rw [hfsp.eq]; bv_omega
  have hmul24 := cap_add_lsl1_ubfm_toNat hcap_bound
  have hmul24' := cap_add_lsl1_lsl3_toNat hcap_bound
  wp_steps 12
  refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (by ac_rfl)) hpre_dealloc) ?_
  wp_apply
  refine SepWP.weaken_pre hpost_dealloc ?_
  wp_done

theorem fromPb_tail_820_placed_sepWP [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A))
    (s0 : State) (fsp pbA ptsPtr cap_pts : BitVec 64)
    (hfsp : HiddenEq fsp (s0.sp - 544#64))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hcap_bound : cap_pts.toNat * 24 < 2 ^ 63)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_376).base + 820#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx20 : s.readReg64 .x20 = pbA) (hx21 : s.readReg64 .x21 = ptsPtr)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (htrace : s.trace = s0.trace) :
    SepWP ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      ((pbA ↦₆₄ cap_pts) ∗ vecVecU8BufDealloc A cap_pts ptsPtr ∗
        savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗
        A.pool ∗ stackAt fsp dropGluePoly16Stack ∗ Frame)
      (fun sf P' =>
        (P' ⊢ (pbA ↦₆₄ cap_pts) ∗ A.pool ∗ stackAt s0.sp fromPbCoreStack ∗ Frame) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  unfold vecVecU8BufDealloc
  by_cases hcap0 : (cap_pts == 0#64) = true
  · simp only [hcap0, ↓reduceIte, emp_sepConj]
    refine DropGlueFacts.seq_clean
      (mid := (blkPl_376).base + 1244#64)
      (P_mid := savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗ stackAt fsp dropGluePoly16Stack ∗
        ((pbA ↦₆₄ cap_pts) ∗ A.pool ∗ Frame))
      (Q := fun sm => sm.sp = fsp ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
    · dsimp only [Reg.x20, BitVec.ofNat_eq_ofNat] at hpc hx20 ⊢
      wp_steps; wp_done
    · intro sm hpcm hrunm ⟨hspm, hvregsm, htrm⟩
      refine SepWP.strengthen_entails_const (Entails.of_eq (by ac_rfl))
        (fromPb_tail_ret_1244_placed_sepWP s0 fsp hfsp hfsp_align sm _ hpcm hrunm hspm hvregsm htrm)
  · have hcap_beq : (cap_pts == 0#64) = false := Bool.eq_false_iff.mpr hcap0
    simp only [hcap_beq, Bool.false_eq_true, ↓reduceIte]
    refine DropGlueFacts.seq_clean
      (mid := (blkPl_376).base + 828#64)
      (P_mid := A.live ptsPtr (cap_pts.toNat * 24) 8 ∗ memRegion ptsPtr (cap_pts.toNat * 24) ∗
        savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗
        A.pool ∗ stackAt fsp dropGluePoly16Stack ∗ ((pbA ↦₆₄ cap_pts) ∗ Frame))
      (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x8 = cap_pts ∧ sm.readReg64 .x21 = ptsPtr ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
    · dsimp only [Reg.x8, Reg.x20, Reg.x21, BitVec.ofNat_eq_ofNat] at hpc hx20 hx21 ⊢
      wp_steps; wp_done
    · intro sm hpcm hrunm ⟨hspm, hx8m, hx21m, hvregsm, htrm⟩
      refine SepWP.strengthen_entails_const (Entails.of_eq (by ac_rfl))
        (fromPb_tail_dealloc_828_placed_sepWP hdealloc s0 fsp ptsPtr cap_pts hfsp hsp0_align hfsp_align hcap_bound
          sm _ hpcm hrunm hspm hx8m hx21m hvregsm htrm)

theorem fromPb_tail_1236_placed_sepWP [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A))
    (s0 : State) (fsp pbA ptsPtr cap_pts : BitVec 64)
    (hfsp : HiddenEq fsp (s0.sp - 544#64))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hcap_bound : cap_pts.toNat * 24 < 2 ^ 63)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_376).base + 1236#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = pbA) (hx21 : s.readReg64 .x21 = ptsPtr)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (htrace : s.trace = s0.trace) :
    SepWP ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      ((pbA ↦₆₄ cap_pts) ∗ vecVecU8BufDealloc A cap_pts ptsPtr ∗
        savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗
        A.pool ∗ stackAt fsp dropGluePoly16Stack ∗ Frame)
      (fun sf P' =>
        (P' ⊢ (pbA ↦₆₄ cap_pts) ∗ A.pool ∗ stackAt s0.sp fromPbCoreStack ∗ Frame) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  unfold vecVecU8BufDealloc
  by_cases hcap0 : (cap_pts == 0#64) = true
  · simp only [hcap0, ↓reduceIte, emp_sepConj]
    refine DropGlueFacts.seq_clean
      (mid := (blkPl_376).base + 1244#64)
      (P_mid := savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗ stackAt fsp dropGluePoly16Stack ∗
        ((pbA ↦₆₄ cap_pts) ∗ A.pool ∗ Frame))
      (Q := fun sm => sm.sp = fsp ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
    · dsimp only [Reg.x19, BitVec.ofNat_eq_ofNat] at hpc hx19 ⊢
      wp_steps; wp_done
    · intro sm hpcm hrunm ⟨hspm, hvregsm, htrm⟩
      refine SepWP.strengthen_entails_const (Entails.of_eq (by ac_rfl))
        (fromPb_tail_ret_1244_placed_sepWP s0 fsp hfsp hfsp_align sm _ hpcm hrunm hspm hvregsm htrm)
  · have hcap_beq : (cap_pts == 0#64) = false := Bool.eq_false_iff.mpr hcap0
    simp only [hcap_beq, Bool.false_eq_true, ↓reduceIte]
    refine DropGlueFacts.seq_clean
      (mid := (blkPl_376).base + 828#64)
      (P_mid := A.live ptsPtr (cap_pts.toNat * 24) 8 ∗ memRegion ptsPtr (cap_pts.toNat * 24) ∗
        savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗
        A.pool ∗ stackAt fsp dropGluePoly16Stack ∗ ((pbA ↦₆₄ cap_pts) ∗ Frame))
      (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x8 = cap_pts ∧ sm.readReg64 .x21 = ptsPtr ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
    · dsimp only [Reg.x8, Reg.x19, Reg.x21, BitVec.ofNat_eq_ofNat] at hpc hx19 hx21 ⊢
      wp_steps; wp_done
    · intro sm hpcm hrunm ⟨hspm, hx8m, hx21m, hvregsm, htrm⟩
      refine SepWP.strengthen_entails_const (Entails.of_eq (by ac_rfl))
        (fromPb_tail_dealloc_828_placed_sepWP hdealloc s0 fsp ptsPtr cap_pts hfsp hsp0_align hfsp_align hcap_bound
          sm _ hpcm hrunm hspm hx8m hx21m hvregsm htrm)

/-! ## Placed `Vec<u8>` Drop Loop (`+776 / +796 -> +820`) -/

theorem fromPb_drop_vec_u8_one_placed_sepWP [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A))
    (s0 : State) (fsp pbA ptsPtr cur cnt : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (bs : List (BitVec 8))
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_376).base + 796#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = cur + 8#64) (hx20 : s.readReg64 .x20 = pbA)
    (hx21 : s.readReg64 .x21 = ptsPtr) (hx24 : s.readReg64 .x24 = cnt)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (htrace : s.trace = s0.trace) :
    SepWP ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      ((blkPl_376).base + 784#64) s
      (vecU8 A cur bs ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x19 = cur + 8#64 ∧ sm.readReg64 .x20 = pbA ∧
        sm.readReg64 .x21 = ptsPtr ∧ sm.readReg64 .x24 = cnt ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) := by
  simp only [rustDeallocSpec, spqrRustDeallocSym] at hdealloc
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A cur bs)) ?_
  apply SepWP.exists_sepConj_left; intro cap
  apply SepWP.exists_sepConj_left; intro ptr
  have hpost24 :
      ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ ptr) ∗ memRegion (cur + 16#64) 8) ∗
        (A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ⊢
      memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame := by
    refine Entails.trans (sepConj_mono_left (DropGlueFacts.header_cells_entails_memRegion_24 cur cap ptr)) ?_
    exact Entails.of_eq (by ac_rfl)
  dsimp only [vecCapPtrDealloc,
    Reg.x19, Reg.x20, Reg.x21, Reg.x24, BitVec.ofNat_eq_ofNat] at hdealloc hpc hx19 hx20 hx21 hx24 ⊢
  by_cases hcap : (cap == 0#64) = true
  · simp only [hcap, ↓reduceIte, sepConj_emp]
    refine SepWP.strengthen_entails_const hpost24 ?_; wp_steps; wp_done
  · have hcap_f : (cap == 0#64) = false := Bool.eq_false_iff.mpr hcap
    simp only [hcap_f, Bool.false_eq_true, ↓reduceIte]
    refine SepWP.strengthen_entails_const hpost24 ?_
    wp_steps 5; wp_apply; wp_steps
    refine DropGlueFacts.align_pre (by rw [hsp]; ac_rfl) ?_; wp_done

theorem fromPb_drop_vec_u8_loop_placed_sepWP [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A))
    (s0 : State) (fsp pbA ptsPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rem : List (List (BitVec 8))) (hrem_ne : rem ≠ [])
      (hlen_bound : rem.length * 24 < 2 ^ 63)
      (cur : BitVec 64) (s : State) (Frame : SepProp),
      s.pc = (blkPl_376).base + 796#64 →
      s.status = .Running → s.sp = fsp →
      s.readReg64 .x19 = cur + 8#64 → s.readReg64 .x20 = pbA →
      s.readReg64 .x21 = ptsPtr → s.readReg64 .x24 = BitVec.ofNat 64 rem.length →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      s.trace = s0.trace →
      SepWP ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
        ((blkPl_376).base + 820#64) s
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
      (fromPb_drop_vec_u8_one_placed_sepWP hdealloc s0 fsp pbA ptsPtr cur 1#64 hfsp_align bs s Frame
        hpc hrun hsp hx19 hx20 hx21 hx24 hvregs htr) ?_
    intro s1 hpc1 hrun1 ⟨hsp1, hx19_1, hx20_1, hx21_1, hx24_1, hvregs1, htr1⟩
    dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x24, BitVec.ofNat_eq_ofNat] at hpc1 hx19_1 hx20_1 hx21_1 hx24_1 ⊢
    wp_steps; wp_done
  | bs :: bs2 :: rest, _, hlen_bound, cur, s, Frame, hpc, hrun, hsp, hx19, hx20, hx21, hx24, hvregs, htr => by
    have hrem'_ne : (bs2 :: rest) ≠ [] := List.cons_ne_nil bs2 rest
    have hrem'_pos : 0 < (bs2 :: rest).length := by simp
    have hrem'_bound : (bs2 :: rest).length * 24 < 2 ^ 63 := by
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at hlen_bound ⊢; omega
    have hcnt_sub : BitVec.ofNat 64 (bs :: bs2 :: rest).length - 1#64 = BitVec.ofNat 64 (bs2 :: rest).length := by
      dsimp only [List.length_cons]
      exact ofNat_succ_sub_one_eq (bs2 :: rest).length
    have hcnt_ne0 : (BitVec.ofNat 64 (bs :: bs2 :: rest).length == 1#64) = false := by
      rw [beq_eq_false_iff_ne]
      intro heq
      have h1 : (BitVec.ofNat 64 (bs :: bs2 :: rest).length).toNat = 1 :=
        congrArg BitVec.toNat heq
      have hlt64 : (bs :: bs2 :: rest).length < 2 ^ 64 := by
        simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at hlen_bound ⊢; omega
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64] at h1
      simp only [List.length_cons] at h1
      omega
    conv => arg 4; rw [arrayAt_cons]
    refine align_pre_wp
      (DropGlueFacts.seq_clean
        (fromPb_drop_vec_u8_one_placed_sepWP hdealloc s0 fsp pbA ptsPtr cur (BitVec.ofNat 64 (bs :: bs2 :: rest).length)
          hfsp_align bs s (arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) (bs2 :: rest) ∗ Frame)
          hpc hrun hsp hx19 hx20 hx21 hx24 hvregs htr) ?_)
      (by ac_rfl)
    intro s1 hpc1 hrun1 ⟨hsp1, hx19_1, hx20_1, hx21_1, hx24_1, hvregs1, htr1⟩
    refine DropGlueFacts.seq_clean
      (mid := (blkPl_376).base + 796#64)
      (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) (bs2 :: rest) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ (memRegion cur 24 ∗ Frame))
      (Q := fun s2 =>
        s2.sp = fsp ∧ s2.readReg64 .x19 = (cur + 24#64) + 8#64 ∧
        s2.readReg64 .x20 = pbA ∧ s2.readReg64 .x21 = ptsPtr ∧
        s2.readReg64 .x24 = BitVec.ofNat 64 (bs2 :: rest).length ∧
        calleeSavedVRegs s2 = calleeSavedVRegs s0 ∧ s2.trace = s0.trace) ?_ ?_
    · dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x24, BitVec.ofNat_eq_ofNat] at hpc1 hx19_1 hx20_1 hx21_1 hx24_1 ⊢
      wp_steps
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
        (fromPb_drop_vec_u8_loop_placed_sepWP hdealloc s0 fsp pbA ptsPtr hfsp_align (bs2 :: rest) hrem'_ne hrem'_bound
          (cur + 24#64) s2 (memRegion cur 24 ∗ Frame)
          hpc2 hrun2 hsp2 hx19_2 hx20_2 hx21_2 hx24_2 hvregs2 htr2)

theorem fromPb_drop_vec_u8_776_placed_sepWP [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A))
    (s0 : State) (fsp pbA ptsPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (rem : List (List (BitVec 8))) (hrem_ne : rem ≠ [])
    (hlen_bound : rem.length * 24 < 2 ^ 63)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_376).base + 776#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx20 : s.readReg64 .x20 = pbA) (hx21 : s.readReg64 .x21 = ptsPtr)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 rem.length)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (htrace : s.trace = s0.trace) :
    SepWP ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      ((blkPl_376).base + 820#64) s
      (arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr rem ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion ptsPtr (rem.length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x20 = pbA ∧ sm.readReg64 .x21 = ptsPtr ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) := by
  refine DropGlueFacts.seq_clean
    (mid := (blkPl_376).base + 796#64)
    (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr rem ∗
      A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm =>
      sm.sp = fsp ∧ sm.readReg64 .x19 = ptsPtr + 8#64 ∧
      sm.readReg64 .x20 = pbA ∧ sm.readReg64 .x21 = ptsPtr ∧
      sm.readReg64 .x24 = BitVec.ofNat 64 rem.length ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
  · dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x24, BitVec.ofNat_eq_ofNat] at hpc hx20 hx21 hx24 ⊢
    wp_steps; wp_done
  · intro sm hpcm hrunm ⟨hspm, hx19m, hx20m, hx21m, hx24m, hvregsm, htrm⟩
    exact fromPb_drop_vec_u8_loop_placed_sepWP hdealloc s0 fsp pbA ptsPtr hfsp_align rem hrem_ne hlen_bound
      ptsPtr sm Frame hpcm hrunm hspm hx19m hx20m hx21m hx24m hvregsm htrm

/-! ## Placed Error Exit A (`+712 -> s0.lr`, when `pb.pts.length ≠ 16`) -/

theorem fromPb_error_exit_712_placed_sepWP [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A))
    (s0 : State) (fsp out pbA cap_pts ptsPtr : BitVec 64)
    (hfsp : HiddenEq fsp (s0.sp - 544#64))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (bss : List (List (BitVec 8)))
    (hle : bss.length ≤ cap_pts.toNat)
    (hcap_bound : cap_pts.toNat * 24 < 2 ^ 63)
    (hlen_bound : bss.length * 24 < 2 ^ 63)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_376).base + 712#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out) (hx20 : s.readReg64 .x20 = pbA)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 bss.length)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (htrace : s.trace = s0.trace) :
    SepWP ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion out 400 ∗
        (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
        ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 bss.length) ∗
        memRegion (pbA + 24#64) 16 ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr bss ∗
        (if cap_pts = 0 then emp
          else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (bss.length * 24)) ((cap_pts.toNat - bss.length) * 24)) ∗
        savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗
        A.pool ∗ stackAt fsp dropGluePoly16Stack ∗ Frame)
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
      (mid := (blkPl_376).base + 820#64)
      (P_mid := (pbA ↦₆₄ cap_pts) ∗ vecVecU8BufDealloc A cap_pts ptsPtr ∗
        savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗
        A.pool ∗ stackAt fsp dropGluePoly16Stack ∗
        (resultPolyDecoderFromPbAt A out (.error .serializationInvalid) ∗
          ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 0#64) ∗
          memRegion (pbA + 24#64) 16 ∗ Frame))
      (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x20 = pbA ∧ sm.readReg64 .x21 = ptsPtr ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
    · dsimp only [Reg.x0, Reg.x20, Reg.x21, Reg.x24, List.length_nil, BitVec.ofNat_eq_ofNat] at hpc hx0 hx20 hx24 ⊢
      wp_steps
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
        (fromPb_tail_820_placed_sepWP hdealloc s0 fsp pbA ptsPtr cap_pts hfsp hsp0_align hfsp_align hcap_bound
          sm _ hpcm hrunm hspm hx20m hx21m hvregsm htrm)
  · have hbss_ne : bss ≠ [] := by intro h; simp [h] at hbss0
    have hbeq0 : (BitVec.ofNat 64 bss.length == 0#64) = false :=
      ofNat_beq_zero_false (by omega) (by omega)
    rw [fromPb_stackAt_dropGluePoly16_split_bottom fsp]
    refine DropGlueFacts.seq_clean
      (mid := (blkPl_376).base + 776#64)
      (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr bss ∗
        A.pool ∗ stackAt fsp allocHookStack ∗
        (resultPolyDecoderFromPbAt A out (.error .serializationInvalid) ∗
          (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
          ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 bss.length) ∗
          memRegion (pbA + 24#64) 16 ∗
          (if cap_pts = 0 then emp
            else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
              memRegion (ptsPtr + BitVec.ofNat 64 (bss.length * 24)) ((cap_pts.toNat - bss.length) * 24)) ∗
          savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗
          memRegion (fsp - 4128#64) 32 ∗ Frame))
      (Q := fun sm =>
        sm.sp = fsp ∧ sm.readReg64 .x20 = pbA ∧ sm.readReg64 .x21 = ptsPtr ∧
        sm.readReg64 .x24 = BitVec.ofNat 64 bss.length ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
    · dsimp only [Reg.x0, Reg.x20, Reg.x21, Reg.x24, BitVec.ofNat_eq_ofNat] at hpc hx0 hx20 hx24 ⊢
      wp_steps
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
      refine ⟨?_, by simp [wp_norm, arm64_norm, *]⟩
      unfold resultPolyDecoderFromPbAt noneCap
      dsimp only [resultPolyDecoderErrByteOff, resultPolyDecoderErrTailSize, polynomialErrorByte, BitVec.ofNat_eq_ofNat]
      exact Entails.of_eq (by ac_rfl)
    · intro s1 hpc1 hrun1 ⟨hsp1, hx20_1, hx21_1, hx24_1, hvregs1, htr1⟩
      refine DropGlueFacts.seq_clean
        (fromPb_drop_vec_u8_776_placed_sepWP hdealloc s0 fsp pbA ptsPtr hfsp_align bss hbss_ne hlen_bound
          s1 _ hpc1 hrun1 hsp1 hx20_1 hx21_1 hx24_1 hvregs1 htr1) ?_
      intro s2 hpc2 hrun2 ⟨hsp2, hx20_2, hx21_2, hvregs2, htr2⟩
      have hpre_820 :
          memRegion ptsPtr (bss.length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗
            (resultPolyDecoderFromPbAt A out (.error .serializationInvalid) ∗
              (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
              ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 bss.length) ∗
              memRegion (pbA + 24#64) 16 ∗
              (if cap_pts = 0 then emp
                else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
                  memRegion (ptsPtr + BitVec.ofNat 64 (bss.length * 24)) ((cap_pts.toNat - bss.length) * 24)) ∗
              savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗
              memRegion (fsp - 4128#64) 32 ∗ Frame) ⊢
          (pbA ↦₆₄ cap_pts) ∗ vecVecU8BufDealloc A cap_pts ptsPtr ∗
            savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗
            A.pool ∗ stackAt fsp dropGluePoly16Stack ∗
            (resultPolyDecoderFromPbAt A out (.error .serializationInvalid) ∗
              ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
              ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 bss.length) ∗
              memRegion (pbA + 24#64) 16 ∗ Frame) := by
        rw [fromPb_stackAt_dropGluePoly16_split_bottom fsp]
        unfold vecVecU8BufDealloc
        exact replace_sub_entails hrejoin_buf
          ((pbA ↦₆₄ cap_pts) ∗ savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗
            A.pool ∗ memRegion (fsp - 4128#64) 32 ∗ stackAt fsp allocHookStack ∗
            resultPolyDecoderFromPbAt A out (.error .serializationInvalid) ∗
            ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
            ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 bss.length) ∗
            memRegion (pbA + 24#64) 16 ∗ Frame) (by ac_rfl) (by ac_rfl)
      have hpost_final :
          (pbA ↦₆₄ cap_pts) ∗ A.pool ∗ stackAt s0.sp fromPbCoreStack ∗
            (resultPolyDecoderFromPbAt A out (.error .serializationInvalid) ∗
              ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
              ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 bss.length) ∗
              memRegion (pbA + 24#64) 16 ∗ Frame) ⊢
          resultPolyDecoderFromPbAt A out (.error .serializationInvalid) ∗
            memRegion pbA 40 ∗ A.pool ∗ stackAt s0.sp fromPbCoreStack ∗ Frame :=
        replace_sub_entails hrejoin_pb
          (resultPolyDecoderFromPbAt A out (.error .serializationInvalid) ∗
            A.pool ∗ stackAt s0.sp fromPbCoreStack ∗ Frame) (by ac_rfl) (by ac_rfl)
      exact SepWP.weaken_pre hpre_820
        (SepWP.strengthen_entails_const hpost_final
          (fromPb_tail_820_placed_sepWP hdealloc s0 fsp pbA ptsPtr cap_pts hfsp hsp0_align hfsp_align hcap_bound
            s2 _ hpc2 hrun2 hsp2 hx20_2 hx21_2 hvregs2 htr2))

/-! ## Placed Error Exit B (`+740 -> s0.lr`, when `pb.pts.length = 16` and some `pts.length % 4 ≠ 0`) -/

theorem fromPb_error_exit_740_placed_sepWP [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A))
    (hdrop : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsmpl.base 264) (dropGlueSortedSetPt16Spec A))
    (s0 : State) (fsp out pbA cap_pts ptsPtr w416 w424 w432 : BitVec 64)
    (hfsp : HiddenEq fsp (s0.sp - 544#64))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (sets_err : List SortedSetPt) (hsets_len : sets_err.length = 16)
    (bss : List (List (BitVec 8))) (hbss_len : bss.length = 16)
    (hle : bss.length ≤ cap_pts.toNat)
    (hcap_bound : cap_pts.toNat * 24 < 2 ^ 63)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_376).base + 740#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx21 : s.readReg64 .x21 = ptsPtr)
    (hx24 : s.readReg64 .x24 = 16#64) (hx29 : s.readReg64 .x29 = fsp + 448#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (htrace : s.trace = s0.trace) :
    SepWP ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
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
        memRegion (fsp - 4128#64) 32 ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sf P' =>
        (P' ⊢ resultPolyDecoderFromPbAt A out (.error .serializationInvalid) ∗
          memRegion pbA 40 ∗ A.pool ∗ stackAt s0.sp fromPbCoreStack ∗ Frame) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  simp only [dropGlueSortedSetPt16Spec] at hdrop
  rw [sortedSetPtListOf_eq_vecPtListOf]
  conv => arg 4; rw [memRegion_400_split_err out]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro b8
  apply ProofLib.SepWP.exists_left; intro d0
  have hvecs_len : (sets_err.map SortedSetPt.vec).length = NUM_POLYS := by
    simp [hsets_len, NUM_POLYS, CHUNK_SIZE]
  refine align_pre_wp
    (DropGlueFacts.seq_clean
      (mid := (blkPl_376).base + 776#64)
      (P := (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₈ b8) ∗ memRegion (out + 9#64) 391 ∗
        memRegion fsp 8 ∗
        ((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
        vecPtListOf A (fsp + 32#64) (sets_err.map SortedSetPt.vec) ∗
        ((fsp + 416#64) ↦₆₄ w416) ∗ ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
        memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
        (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
        memRegion (pbA + 24#64) 16 ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr bss ∗
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
  · dsimp only [Reg.x0, Reg.x20, Reg.x21, Reg.x24, Reg.x29, BitVec.ofNat_eq_ofNat] at hdrop hpc hx21 hx24 hx29 ⊢
    wp_steps 7
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
      (fromPb_drop_vec_u8_776_placed_sepWP hdealloc s0 fsp pbA ptsPtr hfsp_align bss hbss_ne hlen_bound
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
          savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗
          A.pool ∗ stackAt fsp dropGluePoly16Stack ∗
          (resultPolyDecoderFromPbAt A out (.error .serializationInvalid) ∗
            ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
            memRegion (pbA + 24#64) 16 ∗ Frame) := by
      rw [fromPb_stackAt_dropGluePoly16_split_bottom fsp]
      unfold vecVecU8BufDealloc
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
        (fromPb_tail_820_placed_sepWP hdealloc s0 fsp pbA ptsPtr cap_pts hfsp hsp0_align hfsp_align hcap_bound
          s2 _ hpc2 hrun2 hsp2 hx20_2 hx21_2 hvregs2 htr2))

end CryptoVerification.SpqrV1.Poly.DecoderPb
