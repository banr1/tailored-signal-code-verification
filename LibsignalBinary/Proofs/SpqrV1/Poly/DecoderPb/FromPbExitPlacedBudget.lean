/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.Drop.SortedSetPtBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbExitPlaced
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbOuterPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbExit
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Outer Loop Induction and Error Exits for `<PolyDecoder>::from_pb`

Threads `RustCliAllocBudget M`, `FreeOnlyEvs`, and `AllocCallPreserved` through outer-loop
induction, epilogue tails, the `Vec<u8>` drop loop, and error exits A and B on Block `376`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbExitPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (LibsignalPlacement blkPC_376 blkPl_376 lsmpl lsρ)
open CryptoVerification.RustHeap (RustAlloc allocHookStack arrayAt arrayAt_cons arrayAt_nil vecU8)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalSpqrV1 (CHUNK_SIZE NUM_POLYS SortedSetPt)
open CryptoVerification.LibsignalTripleRatchet.Getters.DropGlueFacts (
  header_cells_entails_memRegion_24 memRegion_rejoin_vecBuf
)
open CryptoVerification.SpqrV1.Alloc (spqrMemmoveSym spqrRustAllocSym spqrRustNoAllocShimSym)
open CryptoVerification.SpqrV1.Drop (
  DropGlueSortedSetPt16Ghost dropGluePoly16Stack sortedSetPtListOf_eq_vecPtListOf
  vecCapPtrDealloc vecPtListOf vecU8_entails_capPtr_dealloc
)
open CryptoVerification.SpqrV1.Poly (
  polyArrayBytes polynomialErrorByte resultPolyDecoderErrByteOff resultPolyDecoderErrTailSize
  resultPolyDecoderFromPbAt sortedSetPtListOf sortedSetPtOf
)
open CryptoVerification.SpqrV1.Poly.DecoderPb (
  HiddenEq SepWPp.seq_clean align_pre_wp align_pre_wpp cap_add_lsl1_lsl3_toNat
  cap_add_lsl1_ubfm_toNat cur_add8_add24 cur_add8_sub8 emptySlotsAt
  emptySlotsAt_entails_sortedSetPtListOf emptySlotsAt_zero fromPbCoreStack
  fromPb_stackAt_dropGluePoly16_split_bottom fsp_448_add_8 fsp_448_add_16
  fsp_448_add_24 fsp_448_add_32 fsp_448_add_40 fsp_448_add_48 fsp_448_add_56 fsp_448_add_64
  fsp_448_add_72 fsp_448_add_80 fsp_448_add_88 fsp_448_add_96 fsp_456_add_8 fsp_464_add_8
  fsp_472_add_8 fsp_480_add_8 fsp_488_add_8 fsp_496_add_8 fsp_504_add_8 fsp_512_add_8
  fsp_520_add_8 fsp_528_add_8 fsp_rejoin_448 memRegion_400_split_err off_24_succ
  ofNat_beq_zero_false ofNat_succ_sub_one_eq pbA_rejoin_40 pushChunks4Total replace_sub_entails
  savedRegsAt savedRegsAt_restore_fromPbCoreStack spqrRustDeallocSym
  stackAt_fromPbCoreStack_split_bottom_allocHook vecVecU8BufDealloc
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEvents FreeOnlyEvs
  RustCliAllocBudget VmPreserved fitsEvents_append rustCliAllocBudgetSpec
  rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SpqrV1.Drop.SortedSetPtBudget (dropGlueSortedSetPt16Spec)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDefsBudget (
  fromPbDecLoopAllocEvents fromPbDecSlotEvents
)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbInnerPlacedBudget (sessionMemmoveVmAcpSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbOuterPlacedBudget (
  fromPb_outer_alloc_and_push_placed_wpp_of_hookSat fromPb_outer_invalid_mod4_placed_wpp
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  fsp_448_add_8 fsp_448_add_16 fsp_448_add_24 fsp_448_add_32 fsp_448_add_40 fsp_448_add_48
  fsp_448_add_56 fsp_448_add_64 fsp_448_add_72 fsp_448_add_80 fsp_448_add_88 fsp_448_add_96
  fsp_456_add_8 fsp_464_add_8 fsp_472_add_8 fsp_480_add_8 fsp_488_add_8 fsp_496_add_8
  fsp_504_add_8 fsp_512_add_8 fsp_520_add_8 fsp_528_add_8
  cap_add_lsl1_lsl3_toNat cap_add_lsl1_ubfm_toNat cur_add8_sub8 cur_add8_add24

private def deallocFreeOnlySpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × Nat × Nat × M.σ) where
  pre := (rustCliDeallocBudgetSpec M A lim).pre
  post := fun (_, size, align, st) s0 sf =>
    ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf⌝ ∗
      A.pool lim (M.stepEvents (rustDeallocEvents size align) st) sf ∗ stackAt s0.sp allocHookStack

private theorem subroutine_ok_deallocFreeOnly [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok prog entry (deallocFreeOnlySpec M A lim) := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [rustCliDeallocBudgetSpec, deallocFreeOnlySpec] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  exact ⟨⟨hq.1.1.2.1, hq.1.1⟩, hq.2⟩

private theorem seq_vm_clean {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)}
    {mid target : BitVec 64} {s : State}
    {Pre P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP (P.rebase b Hk) mid s Pre (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      SepWP (P.rebase b Hk) target sm P_mid post) :
    SepWP (P.rebase b Hk) target s Pre post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨hvm, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hvm hQ)

private theorem sepWP_exists_sepConj_left {α : Type} {prog : Program} {tgt : BitVec 64}
    {s : State} {P : α → SepProp} {Q : SepProp} {post : State → SepProp → Prop}
    (h : ∀ x, SepWP prog tgt s (P x ∗ Q) post) :
    SepWP prog tgt s ((∃∗ x, P x) ∗ Q) post := by
  rw [sepExists_sepConj_left]; exact ProofLib.SepWP.exists_left h

private theorem sync_pool_vm (s1 : State) {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ} {prog : Program} {target : BitVec 64}
    {s2 : State} {P F : SepProp} {post : State → SepProp → Prop}
    (hnext : VmPreserved s1 s2 → SepWP prog target s2 (A.pool lim st s2 ∗ F) post)
    (hf : P = A.pool lim st s1 ∗ F := by sep_focus)
    (hvm : VmPreserved s1 s2 := by simp [VmPreserved, Heap.PoolPreserved, wp_norm, arm64_norm]) :
    SepWP prog target s2 P post := by
  rw [hf, ← A.pool_of_vmPreserved hvm]; exact hnext hvm

private theorem seq_clean_evs {prog : Program} {mid target : BitVec 64}
    {s : State} {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm))
    (h2 : ∀ (evs : List AllocEvent) (sm : State),
      FreeOnlyEvs evs → sm.pc = mid → sm.status = .Running → Q sm →
      SepWP prog target sm (P_evs evs sm) post) :
    SepWP prog target s P post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨evs, hevs, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 evs sm hevs hpc hrun hQ)

theorem fromPbDecLoopAllocEvents_cons_ok {pts : List (BitVec 8)} (hmod4 : pts.length % 4 = 0)
    (tail : List (List (BitVec 8))) :
    fromPbDecLoopAllocEvents (pts :: tail) =
      fromPbDecSlotEvents pts ++ fromPbDecLoopAllocEvents tail := by
  unfold fromPbDecLoopAllocEvents
  have hb : (pts.length % 4 == 0) = true := beq_iff_eq.mpr hmod4
  simp [List.takeWhile_cons, hb, List.flatMap_cons]

theorem fromPbDecLoopAllocEvents_cons_err {pts : List (BitVec 8)} (hmod4 : pts.length % 4 ≠ 0)
    (tail : List (List (BitVec 8))) :
    fromPbDecLoopAllocEvents (pts :: tail) = [] := by
  unfold fromPbDecLoopAllocEvents
  have hb : (pts.length % 4 == 0) = false := beq_eq_false_iff_ne.mpr hmod4
  simp [List.takeWhile_cons, hb]

/-! ## Placed Outer Loop Induction (`+204 -> +876` or `+740`) -/

theorem fromPb_outer_loop_placed_wpp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveVmAcpSpec 0))
    {Q Qp : State → SepProp → Prop}
    (s0 : State) (fsp ptsPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rem : List (List (BitVec 8))) (hrem_ne : rem ≠ [])
      (i : Nat) (htot : i + rem.length = 16)
      (st : M.σ) (hfit : FitsEvents M lim st (fromPbDecLoopAllocEvents rem))
      (v416 v424 v432 : BitVec 64)
      (s : State) (Frame : SepProp),
      s.pc = (blkPl_376).base + 204#64 → s.status = .Running → s.sp = fsp →
      s.readReg64 .x19 = 24#64 → s.readReg64 .x21 = ptsPtr → s.readReg64 .x24 = 16#64 →
      s.readReg64 .x25 = BitVec.ofNat 64 i → s.readReg64 .x29 = fsp + 448#64 →
      s.trace = s0.trace → calleeSavedVRegs s = calleeSavedVRegs s0 →
      (∀ (sm : State) (w416 w424 w432 : BitVec 64),
        (∀ bs ∈ rem, bs.length % 4 = 0) →
        sm.pc = (blkPl_376).base + 876#64 → sm.status = .Running → AllocCallPreserved s sm →
        sm.sp = fsp → sm.readReg64 .x21 = ptsPtr → sm.readReg64 .x24 = 16#64 →
        sm.readReg64 .x29 = fsp + 448#64 → sm.trace = s0.trace →
        calleeSavedVRegs sm = calleeSavedVRegs s0 →
        SepWPp ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) sm
          (((fsp + 24#64) ↦₆₄ ptsPtr) ∗ ((fsp + 416#64) ↦₆₄ w416) ∗
            ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
            sortedSetPtListOf A.repAlloc (fsp + 32#64 + BitVec.ofNat 64 (24 * i))
              (rem.map fun bs => pushChunks4Total bs { vec := [] }) ∗
            arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * i)) rem ∗
            A.pool lim (M.stepEvents (fromPbDecLoopAllocEvents rem) st) sm ∗
            stackAt fsp allocHookStack ∗ Frame) Q Qp) →
      (∀ (sm : State) (sets_err : List SortedSetPt) (w416 w424 w432 : BitVec 64),
        (∃ bs ∈ rem, bs.length % 4 ≠ 0) → sets_err.length = rem.length →
        sm.pc = (blkPl_376).base + 740#64 → sm.status = .Running → AllocCallPreserved s sm →
        sm.sp = fsp → sm.readReg64 .x21 = ptsPtr → sm.readReg64 .x24 = 16#64 →
        sm.readReg64 .x29 = fsp + 448#64 → sm.trace = s0.trace →
        calleeSavedVRegs sm = calleeSavedVRegs s0 →
        SepWPp ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) sm
          (((fsp + 24#64) ↦₆₄ ptsPtr) ∗ ((fsp + 416#64) ↦₆₄ w416) ∗
            ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
            sortedSetPtListOf A.repAlloc (fsp + 32#64 + BitVec.ofNat 64 (24 * i)) sets_err ∗
            arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * i)) rem ∗
            A.pool lim (M.stepEvents (fromPbDecLoopAllocEvents rem) st) sm ∗
            stackAt fsp allocHookStack ∗ Frame) Q Qp) →
      SepWPp ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
        (((fsp + 24#64) ↦₆₄ ptsPtr) ∗ ((fsp + 416#64) ↦₆₄ v416) ∗
          ((fsp + 424#64) ↦₆₄ v424) ∗ ((fsp + 432#64) ↦₆₄ v432) ∗
          emptySlotsAt (fsp + 32#64 + BitVec.ofNat 64 (24 * i)) rem.length ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * i)) rem ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        Q Qp
  | [], hrem_ne, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => nomatch hrem_ne rfl
  | [pts], _, i, htot, st, hfit, v416, v424, v432,
      s, Frame, hpc, hrun, hsp, hx19, hx21, hx24, hx25, hx29, htr, hvregs, hok, herr => by
    have hi1 : i + 1 = 16 := by simp at htot; omega
    by_cases hmod4 : pts.length % 4 = 0
    · have hevs : fromPbDecLoopAllocEvents [pts] = fromPbDecSlotEvents pts := by
        rw [fromPbDecLoopAllocEvents_cons_ok hmod4, fromPbDecLoopAllocEvents]
        simp
      rw [hevs] at hfit
      conv => arg 4; simp only [List.length_singleton, arrayAt_cons, arrayAt_nil, sepConj_emp]
      refine align_pre_wpp
        (fromPb_outer_alloc_and_push_placed_wpp_of_hookSat hshim_sat halloc_sat hmemmove_sat
          s0 fsp ptsPtr hfsp_align i 0 (by omega) pts hmod4 st hfit
          v416 v424 v432 s Frame hpc hrun hsp hx19 hx21 hx24 hx25 hx29 htr hvregs ?_)
        (by sep_ac_rfl)
      intro sm w416 w424 w432 hpcm hrunm hacp hspm hx19m hx21m hx24m hx25m hx29m htrm hvregsm
      simp only [hi1, ↓reduceIte] at hpcm
      have hall : ∀ bs ∈ [pts], bs.length % 4 = 0 := by
        intro bs hbs; simp only [List.mem_singleton] at hbs; subst hbs; exact hmod4
      refine SepWPp.weaken_pre ?_
        (hok sm w416 w424 w432 hall hpcm hrunm hacp hspm hx21m hx24m hx29m htrm hvregsm)
      rw [hevs]
      dsimp only [sortedSetPtListOf, List.map]
      simp only [emptySlotsAt_zero, arrayAt_cons, arrayAt_nil, sepConj_emp]
      exact Entails.of_eq (by sep_ac_rfl)
    · have hevs : fromPbDecLoopAllocEvents [pts] = [] :=
        fromPbDecLoopAllocEvents_cons_err hmod4 []
      have hempty := emptySlotsAt_entails_sortedSetPtListOf A.repAlloc 1
        (fsp + 32#64 + BitVec.ofNat 64 (24 * i))
      conv => arg 4; simp only [List.length_singleton, arrayAt_cons, arrayAt_nil, sepConj_emp]
      refine SepWPp.weaken_pre (replace_sub_entails hempty
        (vecU8 A.repAlloc (ptsPtr + BitVec.ofNat 64 (24 * i)) pts ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
          ((fsp + 416#64) ↦₆₄ v416) ∗ ((fsp + 424#64) ↦₆₄ v424) ∗ ((fsp + 432#64) ↦₆₄ v432) ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame) (by sep_ac_rfl) (by sep_ac_rfl))
        (fromPb_outer_invalid_mod4_placed_wpp s0 fsp ptsPtr i pts hmod4 s
          (((fsp + 24#64) ↦₆₄ ptsPtr) ∗
            ((fsp + 416#64) ↦₆₄ v416) ∗ ((fsp + 424#64) ↦₆₄ v424) ∗ ((fsp + 432#64) ↦₆₄ v432) ∗
            sortedSetPtListOf A.repAlloc (fsp + 32#64 + BitVec.ofNat 64 (24 * i)) (List.replicate 1 { vec := [] }) ∗
            A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
          hpc hrun hsp hx19 hx21 hx24 hx25 hx29 htr hvregs ?_)
      intro sm hpcm hrunm hvm hacp hspm hx21m hx24m hx29m htrm hvregsm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (herr sm (List.replicate 1 { vec := [] }) v416 v424 v432
          ⟨pts, List.mem_singleton.mpr rfl, hmod4⟩ rfl hpcm hrunm hacp hspm hx21m hx24m hx29m htrm hvregsm)
      have hst_nil : M.stepEvents ([] : List AllocEvent) st = st := rfl
      rw [hevs, hst_nil, A.pool_of_vmPreserved hvm]
      simp only [arrayAt_cons, arrayAt_nil, sepConj_emp]; sep_ac_rfl
  | pts :: pts2 :: rem', _, i, htot, st, hfit, v416, v424, v432,
      s, Frame, hpc, hrun, hsp, hx19, hx21, hx24, hx25, hx29, htr, hvregs, hok, herr => by
    have hi1_ne : i + 1 ≠ 16 := by simp at htot; omega
    have hoff_out : (fsp + 32#64 + BitVec.ofNat 64 (24 * i)) + 24#64 =
        fsp + 32#64 + BitVec.ofNat 64 (24 * (i + 1)) := off_24_succ (fsp + 32#64) i
    have hoff_in : (ptsPtr + BitVec.ofNat 64 (24 * i)) + 24#64 =
        ptsPtr + BitVec.ofNat 64 (24 * (i + 1)) := off_24_succ ptsPtr i
    by_cases hmod4 : pts.length % 4 = 0
    · have hevs : fromPbDecLoopAllocEvents (pts :: pts2 :: rem') =
          fromPbDecSlotEvents pts ++ fromPbDecLoopAllocEvents (pts2 :: rem') :=
        fromPbDecLoopAllocEvents_cons_ok hmod4 (pts2 :: rem')
      rw [hevs] at hfit
      rcases (fitsEvents_append M lim _ _ st).mp hfit with ⟨hfit_pts, hfit_tail⟩
      conv => arg 4; rw [arrayAt_cons, hoff_in]
      refine align_pre_wpp
        (fromPb_outer_alloc_and_push_placed_wpp_of_hookSat hshim_sat halloc_sat hmemmove_sat
          s0 fsp ptsPtr hfsp_align i (pts2 :: rem').length
          (by simp at htot ⊢; omega) pts hmod4 st hfit_pts v416 v424 v432 s
          (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24
            (ptsPtr + BitVec.ofNat 64 (24 * (i + 1))) (pts2 :: rem') ∗ Frame)
          hpc hrun hsp hx19 hx21 hx24 hx25 hx29 htr hvregs ?_)
        (by sep_ac_rfl)
      intro sm w416 w424 w432 hpcm hrunm hacp1 hspm hx19m hx21m hx24m hx25m hx29m htrm hvregsm
      simp only [hi1_ne, ↓reduceIte] at hpcm
      refine align_pre_wpp
        (fromPb_outer_loop_placed_wpp hshim_sat halloc_sat hmemmove_sat s0 fsp ptsPtr hfsp_align
          (pts2 :: rem') (List.cons_ne_nil pts2 rem') (i + 1) (by simp at htot ⊢; omega)
          (M.stepEvents (fromPbDecSlotEvents pts) st) hfit_tail
          w416 w424 w432 sm
          (sortedSetPtOf A.repAlloc (fsp + 32#64 + BitVec.ofNat 64 (24 * i))
            (pushChunks4Total pts { vec := [] }) ∗
            vecU8 A.repAlloc (ptsPtr + BitVec.ofNat 64 (24 * i)) pts ∗ Frame)
          hpcm hrunm hspm hx19m hx21m hx24m hx25m hx29m htrm hvregsm ?_ ?_)
        (by sep_ac_rfl)
      · intro s_end u416 u424 u432 hall_rem hpc_end hrun_end hacp2 hsp_end hx21_end hx24_end hx29_end htr_end hvregs_end
        have hall : ∀ bs ∈ (pts :: pts2 :: rem'), bs.length % 4 = 0 := by
          intro bs hbs; rcases List.mem_cons.mp hbs with rfl | hbs'
          · exact hmod4
          · exact hall_rem bs hbs'
        refine SepWPp.weaken_pre ?_
          (hok s_end u416 u424 u432 hall hpc_end hrun_end (hacp1.trans hacp2)
            hsp_end hx21_end hx24_end hx29_end htr_end hvregs_end)
        rw [hevs, M.stepEvents_append,
          show sortedSetPtListOf A.repAlloc (fsp + 32#64 + BitVec.ofNat 64 (24 * i))
              ((pts :: pts2 :: rem').map fun bs => pushChunks4Total bs { vec := [] }) =
            sortedSetPtOf A.repAlloc (fsp + 32#64 + BitVec.ofNat 64 (24 * i)) (pushChunks4Total pts { vec := [] }) ∗
              sortedSetPtListOf A.repAlloc (fsp + 32#64 + BitVec.ofNat 64 (24 * i) + 24#64)
                ((pts2 :: rem').map fun bs => pushChunks4Total bs { vec := [] }) from rfl,
          hoff_out,
          show arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * i)) (pts :: pts2 :: rem') =
            vecU8 A.repAlloc (ptsPtr + BitVec.ofNat 64 (24 * i)) pts ∗
              arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * i) + 24#64) (pts2 :: rem') from rfl,
          hoff_in]
        exact Entails.of_eq (by sep_ac_rfl)
      · intro s_err sets_rem u416 u424 u432 hex_rem hlen_rem hpc_err hrun_err hacp2 hsp_err hx21_err hx24_err hx29_err htr_err hvregs_err
        rcases hex_rem with ⟨bs_bad, hbs_bad, hbad⟩
        have hex : ∃ bs ∈ (pts :: pts2 :: rem'), bs.length % 4 ≠ 0 :=
          ⟨bs_bad, List.mem_cons_of_mem pts hbs_bad, hbad⟩
        refine SepWPp.weaken_pre ?_
          (herr s_err (pushChunks4Total pts { vec := [] } :: sets_rem) u416 u424 u432
            hex (by simp [hlen_rem]) hpc_err hrun_err (hacp1.trans hacp2)
            hsp_err hx21_err hx24_err hx29_err htr_err hvregs_err)
        rw [hevs, M.stepEvents_append,
          show sortedSetPtListOf A.repAlloc (fsp + 32#64 + BitVec.ofNat 64 (24 * i))
              (pushChunks4Total pts { vec := [] } :: sets_rem) =
            sortedSetPtOf A.repAlloc (fsp + 32#64 + BitVec.ofNat 64 (24 * i)) (pushChunks4Total pts { vec := [] }) ∗
              sortedSetPtListOf A.repAlloc (fsp + 32#64 + BitVec.ofNat 64 (24 * i) + 24#64) sets_rem from rfl,
          hoff_out,
          show arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * i)) (pts :: pts2 :: rem') =
            vecU8 A.repAlloc (ptsPtr + BitVec.ofNat 64 (24 * i)) pts ∗
              arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * i) + 24#64) (pts2 :: rem') from rfl,
          hoff_in]
        exact Entails.of_eq (by sep_ac_rfl)
    · have hevs : fromPbDecLoopAllocEvents (pts :: pts2 :: rem') = [] :=
        fromPbDecLoopAllocEvents_cons_err hmod4 (pts2 :: rem')
      have hempty := emptySlotsAt_entails_sortedSetPtListOf A.repAlloc (pts :: pts2 :: rem').length
        (fsp + 32#64 + BitVec.ofNat 64 (24 * i))
      conv => arg 4; rw [arrayAt_cons, hoff_in]
      refine SepWPp.weaken_pre (replace_sub_entails hempty
        (vecU8 A.repAlloc (ptsPtr + BitVec.ofNat 64 (24 * i)) pts ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
          ((fsp + 416#64) ↦₆₄ v416) ∗ ((fsp + 424#64) ↦₆₄ v424) ∗ ((fsp + 432#64) ↦₆₄ v432) ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24
            (ptsPtr + BitVec.ofNat 64 (24 * (i + 1))) (pts2 :: rem') ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame) (by sep_ac_rfl) (by sep_ac_rfl))
        (fromPb_outer_invalid_mod4_placed_wpp s0 fsp ptsPtr i pts hmod4 s
          (((fsp + 24#64) ↦₆₄ ptsPtr) ∗
            ((fsp + 416#64) ↦₆₄ v416) ∗ ((fsp + 424#64) ↦₆₄ v424) ∗ ((fsp + 432#64) ↦₆₄ v432) ∗
            sortedSetPtListOf A.repAlloc (fsp + 32#64 + BitVec.ofNat 64 (24 * i))
              (List.replicate (pts :: pts2 :: rem').length { vec := [] }) ∗
            arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24
              (ptsPtr + BitVec.ofNat 64 (24 * (i + 1))) (pts2 :: rem') ∗
            A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
          hpc hrun hsp hx19 hx21 hx24 hx25 hx29 htr hvregs ?_)
      intro sm hpcm hrunm hvm hacp hspm hx21m hx24m hx29m htrm hvregsm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (herr sm (List.replicate (pts :: pts2 :: rem').length { vec := [] }) v416 v424 v432
          ⟨pts, List.mem_cons_self, hmod4⟩ (by simp) hpcm hrunm hacp hspm hx21m hx24m hx29m htrm hvregsm)
      have hst_nil : M.stepEvents ([] : List AllocEvent) st = st := rfl
      rw [hevs, hst_nil, A.pool_of_vmPreserved hvm]
      simp only [arrayAt_cons, hoff_in]; sep_ac_rfl

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
        VmPreserved s sf ∧
        (P' ⊢ stackAt s0.sp fromPbCoreStack ∗ Frame) ∧
        sf.sp = s0.sp ∧ AllocCallPreserved s sf ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  dsimp only [savedRegsAt,
    Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
    Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30,
    BitVec.ofNat_eq_ofNat] at hpc ⊢
  have hsp448_al : ((fsp + 448#64) &&& 15#64 == 0#64) = true := by revert hfsp_align; bv_bits
  have hsp_ret : fsp + 544#64 = s0.sp := by rw [hfsp.eq]; bv_omega
  by_vm_steps (
    wp_steps
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
    refine ⟨by simp [wp_norm, arm64_norm], ?_, by simp [wp_norm, arm64_norm, hsp, hsp_ret],
      by simp [AllocCallPreserved, wp_norm, arm64_norm], ?_, by simp [wp_norm, arm64_norm, htrace]⟩
    · refine Entails.trans ?_ (sepConj_mono_left (savedRegsAt_restore_fromPbCoreStack s0.sp fsp hfsp.eq s0))
      unfold savedRegsAt
      dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
        Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      exact Entails.of_eq (by sep_ac_rfl)
    · unfold CalleeSavedPreserved; simp [wp_norm, arm64_norm, *])

theorem fromPb_tail_dealloc_828_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (fsp ptsPtr cap_pts : BitVec 64)
    (hfsp : HiddenEq fsp (s0.sp - 544#64))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hcap_bound : cap_pts.toNat * 24 < 2 ^ 63)
    (st : M.σ) (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_376).base + 828#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx8 : s.readReg64 .x8 = cap_pts) (hx21 : s.readReg64 .x21 = ptsPtr)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (htrace : s.trace = s0.trace)
    (hlr_ls : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := by
      first
      | assumption
      | simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    SepWP ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.repAlloc.live ptsPtr (cap_pts.toNat * 24) 8 ∗ memRegion ptsPtr (cap_pts.toNat * 24) ∗
        savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗
        A.pool lim st s ∗ stackAt fsp dropGluePoly16Stack ∗ Frame)
      (fun sf P' =>
        (P' ⊢ A.pool lim (M.stepEvents (rustDeallocEvents (cap_pts.toNat * 24) 8) st) sf ∗
          stackAt s0.sp fromPbCoreStack ∗ Frame) ∧
        sf.sp = s0.sp ∧ AllocCallPreserved s sf ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc
  clear hdealloc
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec, spqrRustDeallocSym] at hdealloc_fo
  dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
  have hpre_dealloc : ∀ P_pool : SepProp,
      A.live ptsPtr (cap_pts.toNat * 24) 8 ∗ memRegion ptsPtr (cap_pts.toNat * 24) ∗
        savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗
        P_pool ∗ stackAt fsp dropGluePoly16Stack ∗ Frame ⊢
      A.live ptsPtr (cap_pts.toNat * 24) 8 ∗ memRegion ptsPtr (cap_pts.toNat * 24) ∗
        P_pool ∗ stackAt s0.sp allocHookStack ∗
        (memRegion (s0.sp - 4672#64) 576 ∗ Frame) := by
    intro P_pool
    have hrest := savedRegsAt_restore_fromPbCoreStack s0.sp fsp hfsp.eq s0
    rw [stackAt_fromPbCoreStack_split_bottom_allocHook s0.sp] at hrest
    exact replace_sub_entails hrest
      (A.live ptsPtr (cap_pts.toNat * 24) 8 ∗ memRegion ptsPtr (cap_pts.toNat * 24) ∗ P_pool ∗ Frame)
      (by sep_ac_rfl) (by sep_ac_rfl)
  have hpost_dealloc : ∀ P_pool : SepProp,
      P_pool ∗ stackAt s0.sp allocHookStack ∗ (memRegion (s0.sp - 4672#64) 576 ∗ Frame) ⊢
      P_pool ∗ stackAt s0.sp fromPbCoreStack ∗ Frame := by
    intro P_pool
    rw [stackAt_fromPbCoreStack_split_bottom_allocHook s0.sp]
    exact Entails.of_eq (by sep_ac_rfl)
  dsimp only [savedRegsAt,
    Reg.x8, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
    Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30,
    BitVec.ofNat_eq_ofNat] at hdealloc_fo hpre_dealloc hpc hx8 hx21 ⊢
  have hsp448_al : ((fsp + 448#64) &&& 15#64 == 0#64) = true := by revert hfsp_align; bv_bits
  have hsp_ret : fsp + 544#64 = s0.sp := by rw [hfsp.eq]; bv_omega
  have hmul24 := cap_add_lsl1_ubfm_toNat hcap_bound
  have hmul24' := cap_add_lsl1_lsl3_toNat hcap_bound
  wp_steps 12
  refine sync_pool_vm s fun hvm_step => ?_
  refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (by sep_ac_rfl)) (hpre_dealloc _)) ?_
  wp_apply
  have hacp_call : AllocCallPreserved s sf := by assumption
  rcases hacp_call with ⟨_, _, _, _, _, _, _⟩
  refine SepWP.weaken_pre (hpost_dealloc _) ?_
  wp_done

theorem fromPb_tail_820_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (fsp pbA ptsPtr cap_pts : BitVec 64)
    (hfsp : HiddenEq fsp (s0.sp - 544#64))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hcap_bound : cap_pts.toNat * 24 < 2 ^ 63)
    (st : M.σ) (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_376).base + 820#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx20 : s.readReg64 .x20 = pbA) (hx21 : s.readReg64 .x21 = ptsPtr)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (htrace : s.trace = s0.trace)
    (hlr_ls : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := by
      first
      | assumption
      | simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    SepWP ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      ((pbA ↦₆₄ cap_pts) ∗ vecVecU8BufDealloc A.repAlloc cap_pts ptsPtr ∗
        savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗
        A.pool lim st s ∗ stackAt fsp dropGluePoly16Stack ∗ Frame)
      (fun sf P' =>
        ∃ evs, FreeOnlyEvs evs ∧
          (P' ⊢ (pbA ↦₆₄ cap_pts) ∗ A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp fromPbCoreStack ∗ Frame) ∧
          sf.sp = s0.sp ∧ AllocCallPreserved s sf ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  unfold vecVecU8BufDealloc
  by_cases hcap0 : (cap_pts == 0#64) = true
  · simp only [hcap0, ↓reduceIte, emp_sepConj]
    refine seq_vm_clean
      (mid := (blkPl_376).base + 1244#64)
      (P_mid := savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗ stackAt fsp dropGluePoly16Stack ∗
        ((pbA ↦₆₄ cap_pts) ∗ A.pool lim st s ∗ Frame))
      (Q := fun sm => AllocCallPreserved s sm ∧ sm.sp = fsp ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
    · dsimp only [Reg.x20, BitVec.ofNat_eq_ofNat] at hpc hx20 ⊢
      by_vm_steps (wp_steps; simp only [AllocCallPreserved]; wp_done)
    · intro sm hpcm hrunm hvm1 ⟨hacp1, hspm, hvregsm, htrm⟩
      refine SepWP.mono
        (fromPb_tail_ret_1244_placed_sepWP s0 fsp hfsp hfsp_align sm _ hpcm hrunm hspm hvregsm htrm)
        fun sf _Pf _ _ ⟨hvm2, hPf, hspf, hacp2, hcsf, htrf⟩ => ?_
      refine ⟨[], FreeOnlyEvs.nil, Entails.trans hPf ?_, hspf, hacp1.trans hacp2, hcsf, htrf⟩
      have hst_nil : M.stepEvents ([] : List AllocEvent) st = st := rfl
      rw [hst_nil, A.pool_of_vmPreserved (hvm1.trans hvm2)]
      exact Entails.of_eq (by sep_ac_rfl)
  · have hcap_beq : (cap_pts == 0#64) = false := Bool.eq_false_iff.mpr hcap0
    simp only [hcap_beq, Bool.false_eq_true, ↓reduceIte]
    refine seq_vm_clean
      (mid := (blkPl_376).base + 828#64)
      (P_mid := A.repAlloc.live ptsPtr (cap_pts.toNat * 24) 8 ∗ memRegion ptsPtr (cap_pts.toNat * 24) ∗
        savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗
        A.pool lim st s ∗ stackAt fsp dropGluePoly16Stack ∗ ((pbA ↦₆₄ cap_pts) ∗ Frame))
      (Q := fun sm => AllocCallPreserved s sm ∧ sm.sp = fsp ∧
        sm.readReg64 .x8 = cap_pts ∧ sm.readReg64 .x21 = ptsPtr ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
    · dsimp only [Reg.x8, Reg.x20, Reg.x21, BitVec.ofNat_eq_ofNat] at hpc hx20 hx21 ⊢
      by_vm_steps (wp_steps; simp only [AllocCallPreserved]; wp_done)
    · intro sm hpcm hrunm hvm1 ⟨hacp1, hspm, hx8m, hx21m, hvregsm, htrm⟩
      rw [← A.pool_of_vmPreserved hvm1]
      refine SepWP.mono
        (fromPb_tail_dealloc_828_placed_sepWP hdealloc s0 fsp ptsPtr cap_pts hfsp hsp0_align hfsp_align hcap_bound
          st sm _ hpcm hrunm hspm hx8m hx21m hvregsm htrm (hlr_ls := hlr_ls))
        fun sf _Pf _ _ ⟨hPf, hspf, hacp2, hcsf, htrf⟩ => ?_
      refine ⟨rustDeallocEvents (cap_pts.toNat * 24) 8, FreeOnlyEvs.singleton 8 (cap_pts.toNat * 24),
        Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hspf, hacp1.trans hacp2, hcsf, htrf⟩

theorem fromPb_tail_1236_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (fsp pbA ptsPtr cap_pts : BitVec 64)
    (hfsp : HiddenEq fsp (s0.sp - 544#64))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hcap_bound : cap_pts.toNat * 24 < 2 ^ 63)
    (st : M.σ) (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_376).base + 1236#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = pbA) (hx21 : s.readReg64 .x21 = ptsPtr)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (htrace : s.trace = s0.trace)
    (hlr_ls : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := by
      first
      | assumption
      | simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    SepWP ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      ((pbA ↦₆₄ cap_pts) ∗ vecVecU8BufDealloc A.repAlloc cap_pts ptsPtr ∗
        savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗
        A.pool lim st s ∗ stackAt fsp dropGluePoly16Stack ∗ Frame)
      (fun sf P' =>
        ∃ evs, FreeOnlyEvs evs ∧
          (P' ⊢ (pbA ↦₆₄ cap_pts) ∗ A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp fromPbCoreStack ∗ Frame) ∧
          sf.sp = s0.sp ∧ AllocCallPreserved s sf ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  unfold vecVecU8BufDealloc
  by_cases hcap0 : (cap_pts == 0#64) = true
  · simp only [hcap0, ↓reduceIte, emp_sepConj]
    refine seq_vm_clean
      (mid := (blkPl_376).base + 1244#64)
      (P_mid := savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗ stackAt fsp dropGluePoly16Stack ∗
        ((pbA ↦₆₄ cap_pts) ∗ A.pool lim st s ∗ Frame))
      (Q := fun sm => AllocCallPreserved s sm ∧ sm.sp = fsp ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
    · dsimp only [Reg.x19, BitVec.ofNat_eq_ofNat] at hpc hx19 ⊢
      by_vm_steps (wp_steps; simp only [AllocCallPreserved]; wp_done)
    · intro sm hpcm hrunm hvm1 ⟨hacp1, hspm, hvregsm, htrm⟩
      refine SepWP.mono
        (fromPb_tail_ret_1244_placed_sepWP s0 fsp hfsp hfsp_align sm _ hpcm hrunm hspm hvregsm htrm)
        fun sf _Pf _ _ ⟨hvm2, hPf, hspf, hacp2, hcsf, htrf⟩ => ?_
      refine ⟨[], FreeOnlyEvs.nil, Entails.trans hPf ?_, hspf, hacp1.trans hacp2, hcsf, htrf⟩
      have hst_nil : M.stepEvents ([] : List AllocEvent) st = st := rfl
      rw [hst_nil, A.pool_of_vmPreserved (hvm1.trans hvm2)]
      exact Entails.of_eq (by sep_ac_rfl)
  · have hcap_beq : (cap_pts == 0#64) = false := Bool.eq_false_iff.mpr hcap0
    simp only [hcap_beq, Bool.false_eq_true, ↓reduceIte]
    refine seq_vm_clean
      (mid := (blkPl_376).base + 828#64)
      (P_mid := A.repAlloc.live ptsPtr (cap_pts.toNat * 24) 8 ∗ memRegion ptsPtr (cap_pts.toNat * 24) ∗
        savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗
        A.pool lim st s ∗ stackAt fsp dropGluePoly16Stack ∗ ((pbA ↦₆₄ cap_pts) ∗ Frame))
      (Q := fun sm => AllocCallPreserved s sm ∧ sm.sp = fsp ∧
        sm.readReg64 .x8 = cap_pts ∧ sm.readReg64 .x21 = ptsPtr ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
    · dsimp only [Reg.x8, Reg.x19, Reg.x21, BitVec.ofNat_eq_ofNat] at hpc hx19 hx21 ⊢
      by_vm_steps (wp_steps; simp only [AllocCallPreserved]; wp_done)
    · intro sm hpcm hrunm hvm1 ⟨hacp1, hspm, hx8m, hx21m, hvregsm, htrm⟩
      rw [← A.pool_of_vmPreserved hvm1]
      refine SepWP.mono
        (fromPb_tail_dealloc_828_placed_sepWP hdealloc s0 fsp ptsPtr cap_pts hfsp hsp0_align hfsp_align hcap_bound
          st sm _ hpcm hrunm hspm hx8m hx21m hvregsm htrm (hlr_ls := hlr_ls))
        fun sf _Pf _ _ ⟨hPf, hspf, hacp2, hcsf, htrf⟩ => ?_
      refine ⟨rustDeallocEvents (cap_pts.toNat * 24) 8, FreeOnlyEvs.singleton 8 (cap_pts.toNat * 24),
        Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hspf, hacp1.trans hacp2, hcsf, htrf⟩

/-! ## Placed `Vec<u8>` Drop Loop (`+776 / +796 -> +820`) -/

theorem fromPb_drop_vec_u8_one_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (fsp pbA ptsPtr cur cnt : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (bs : List (BitVec 8))
    (st : M.σ) (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_376).base + 796#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = cur + 8#64) (hx20 : s.readReg64 .x20 = pbA)
    (hx21 : s.readReg64 .x21 = ptsPtr) (hx24 : s.readReg64 .x24 = cnt)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (htrace : s.trace = s0.trace) :
    SepWP ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      ((blkPl_376).base + 784#64) s
      (vecU8 A.repAlloc cur bs ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
          (Pm ⊢ memRegion cur 24 ∗ A.pool lim (M.stepEvents evs st) sm ∗
            stackAt fsp allocHookStack ∗ Frame) ∧
          AllocCallPreserved s sm ∧
          sm.sp = fsp ∧ sm.readReg64 .x19 = cur + 8#64 ∧ sm.readReg64 .x20 = pbA ∧
          sm.readReg64 .x21 = ptsPtr ∧ sm.readReg64 .x24 = cnt ∧
          calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc
  clear hdealloc
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec, spqrRustDeallocSym] at hdealloc_fo
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A.repAlloc cur bs)) ?_
  apply sepWP_exists_sepConj_left; intro cap
  apply sepWP_exists_sepConj_left; intro ptr
  have hpost24 : ∀ P_pool : SepProp,
      ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ ptr) ∗ memRegion (cur + 16#64) 8) ∗
        (P_pool ∗ stackAt fsp allocHookStack ∗ Frame) ⊢
      memRegion cur 24 ∗ P_pool ∗ stackAt fsp allocHookStack ∗ Frame := fun _ =>
    Entails.trans (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap ptr))
      (Entails.of_eq (by sep_ac_rfl))
  dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live,
    Reg.x19, Reg.x20, Reg.x21, Reg.x24, BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc hx19 hx20 hx21 hx24 ⊢
  by_cases hcap : (cap == 0#64) = true
  · simp only [hcap, ↓reduceIte, sepConj_emp]
    refine SepWP.mono
      (show SepWP ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext)) ((blkPl_376).base + 784#64) s
        (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ ptr) ∗ memRegion (cur + 16#64) 8) ∗
          (A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame))
        (fun sm Pm => VmPreserved s sm ∧
          (Pm ⊢ memRegion cur 24 ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          AllocCallPreserved s sm ∧ sm.sp = fsp ∧ sm.readReg64 .x19 = cur + 8#64 ∧
          sm.readReg64 .x20 = pbA ∧ sm.readReg64 .x21 = ptsPtr ∧ sm.readReg64 .x24 = cnt ∧
          calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) from by
        by_vm_steps (
          wp_steps
          apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
          refine ⟨by simp [wp_norm, arm64_norm],
            Entails.trans (Entails.of_eq (by sep_ac_rfl)) (hpost24 _),
            by simp [AllocCallPreserved, wp_norm, arm64_norm, *]⟩))
      fun sm _Pm _ _ ⟨hvm, hPm, hacp, hq⟩ => ?_
    refine ⟨[], FreeOnlyEvs.nil, ?_, hacp, hq⟩
    have hst_nil : M.stepEvents ([] : List AllocEvent) st = st := rfl
    rw [hst_nil, A.pool_of_vmPreserved hvm]; exact hPm
  · have hcap_f : (cap == 0#64) = false := Bool.eq_false_iff.mpr hcap
    simp only [hcap_f, Bool.false_eq_true, ↓reduceIte]
    refine SepWP.mono
      (show SepWP ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext)) ((blkPl_376).base + 784#64) s
        (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ ptr) ∗ memRegion (cur + 16#64) 8 ∗
          (A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat)) ∗
          (A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame))
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 24 ∗ A.pool lim (M.stepEvents (rustDeallocEvents cap.toNat 1) st) sm ∗
            stackAt fsp allocHookStack ∗ Frame) ∧
          AllocCallPreserved s sm ∧ sm.sp = fsp ∧ sm.readReg64 .x19 = cur + 8#64 ∧
          sm.readReg64 .x20 = pbA ∧ sm.readReg64 .x21 = ptsPtr ∧ sm.readReg64 .x24 = cnt ∧
          calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) from by
        wp_steps 5
        refine sync_pool_vm s fun hvm_step => ?_
        wp_apply
        have hacp_call : AllocCallPreserved s sf := by assumption
        rcases hacp_call with ⟨_, _, _, _, _, _, _⟩
        wp_steps
        refine sync_pool_vm sf fun hvm_after => ?_
        apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_sf])
        refine ⟨?_, ?_⟩
        · rw [hsp]; exact Entails.trans (Entails.of_eq (by sep_ac_rfl)) (hpost24 _)
        · simp [AllocCallPreserved, wp_norm, arm64_norm, *])
      fun _ _ _ _ ⟨hPm, hacp, hq⟩ =>
        ⟨rustDeallocEvents cap.toNat 1, FreeOnlyEvs.singleton 1 cap.toNat, hPm, hacp, hq⟩

theorem fromPb_drop_vec_u8_loop_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (fsp pbA ptsPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rem : List (List (BitVec 8))) (hrem_ne : rem ≠ [])
      (hlen_bound : rem.length * 24 < 2 ^ 63)
      (cur : BitVec 64) (st : M.σ) (s : State) (Frame : SepProp),
      s.pc = (blkPl_376).base + 796#64 →
      s.status = .Running → s.sp = fsp →
      s.readReg64 .x19 = cur + 8#64 → s.readReg64 .x20 = pbA →
      s.readReg64 .x21 = ptsPtr → s.readReg64 .x24 = BitVec.ofNat 64 rem.length →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      s.trace = s0.trace →
      SepWP ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
        ((blkPl_376).base + 820#64) s
        (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 cur rem ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs, FreeOnlyEvs evs ∧
            (Pm ⊢ memRegion cur (rem.length * 24) ∗ A.pool lim (M.stepEvents evs st) sm ∗
              stackAt fsp allocHookStack ∗ Frame) ∧
            AllocCallPreserved s sm ∧
            sm.sp = fsp ∧ sm.readReg64 .x20 = pbA ∧ sm.readReg64 .x21 = ptsPtr ∧
            calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace)
  | [], hrem_ne, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => nomatch hrem_ne rfl
  | [bs], _, _, cur, st, s, Frame, hpc, hrun, hsp, hx19, hx20, hx21, hx24, hvregs, htr => by
    conv => arg 4; simp only [arrayAt_cons, arrayAt_nil, sepConj_emp]
    dsimp only [List.length_singleton, BitVec.ofNat_eq_ofNat] at hx24 ⊢
    refine seq_clean_evs
      (fromPb_drop_vec_u8_one_placed_sepWP hdealloc s0 fsp pbA ptsPtr cur 1#64 hfsp_align bs st s Frame
        hpc hrun hsp hx19 hx20 hx21 hx24 hvregs htr) ?_
    intro evs1 s1 hevs1 hpc1 hrun1 ⟨hacp1, hsp1, hx19_1, hx20_1, hx21_1, hx24_1, hvregs1, htr1⟩
    dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x24, BitVec.ofNat_eq_ofNat] at hpc1 hx19_1 hx20_1 hx21_1 hx24_1 ⊢
    refine SepWP.mono
      (show SepWP ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
        ((blkPl_376).base + 820#64) s1
        (memRegion cur 24 ∗ A.pool lim (M.stepEvents evs1 st) s1 ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          VmPreserved s1 sm ∧
          (Pm ⊢ memRegion cur (1 * 24) ∗ A.pool lim (M.stepEvents evs1 st) s1 ∗
            stackAt fsp allocHookStack ∗ Frame) ∧
          AllocCallPreserved s1 sm ∧
          sm.sp = fsp ∧ sm.readReg64 .x20 = pbA ∧ sm.readReg64 .x21 = ptsPtr ∧
          calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) from by
        by_vm_steps (wp_steps; simp only [AllocCallPreserved]; wp_done))
      fun sm _Pm _ _ ⟨hvm2, hPm, hacp2, hq⟩ => ?_
    refine ⟨evs1, hevs1, ?_, hacp1.trans hacp2, hq⟩
    rw [A.pool_of_vmPreserved hvm2]
    exact hPm
  | bs :: bs2 :: rest, _, hlen_bound, cur, st, s, Frame, hpc, hrun, hsp, hx19, hx20, hx21, hx24, hvregs, htr => by
    have hrem'_ne : (bs2 :: rest) ≠ [] := List.cons_ne_nil bs2 rest
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
      (seq_clean_evs
        (fromPb_drop_vec_u8_one_placed_sepWP hdealloc s0 fsp pbA ptsPtr cur (BitVec.ofNat 64 (bs :: bs2 :: rest).length)
          hfsp_align bs st s (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (cur + 24#64) (bs2 :: rest) ∗ Frame)
          hpc hrun hsp hx19 hx20 hx21 hx24 hvregs htr) ?_)
      (by sep_ac_rfl)
    intro evs1 s1 hevs1 hpc1 hrun1 ⟨hacp1, hsp1, hx19_1, hx20_1, hx21_1, hx24_1, hvregs1, htr1⟩
    refine seq_vm_clean
      (mid := (blkPl_376).base + 796#64)
      (P_mid := arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (cur + 24#64) (bs2 :: rest) ∗
        A.pool lim (M.stepEvents evs1 st) s1 ∗ stackAt fsp allocHookStack ∗ (memRegion cur 24 ∗ Frame))
      (Q := fun s2 =>
        AllocCallPreserved s1 s2 ∧
        s2.sp = fsp ∧ s2.readReg64 .x19 = (cur + 24#64) + 8#64 ∧
        s2.readReg64 .x20 = pbA ∧ s2.readReg64 .x21 = ptsPtr ∧
        s2.readReg64 .x24 = BitVec.ofNat 64 (bs2 :: rest).length ∧
        calleeSavedVRegs s2 = calleeSavedVRegs s0 ∧ s2.trace = s0.trace) ?_ ?_
    · dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x24, BitVec.ofNat_eq_ofNat] at hpc1 hx19_1 hx20_1 hx21_1 hx24_1 ⊢
      by_vm_steps (
        wp_steps
        apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
        refine ⟨by simp [wp_norm, arm64_norm], Entails.of_eq (by sep_ac_rfl), ?_⟩
        simp [AllocCallPreserved, wp_norm, arm64_norm, hcnt_sub, *])
    · intro s2 hpc2 hrun2 hvm2 ⟨hacp2, hsp2, hx19_2, hx20_2, hx21_2, hx24_2, hvregs2, htr2⟩
      rw [← A.pool_of_vmPreserved hvm2]
      refine SepWP.mono
        (fromPb_drop_vec_u8_loop_placed_sepWP hdealloc s0 fsp pbA ptsPtr hfsp_align (bs2 :: rest) hrem'_ne hrem'_bound
          (cur + 24#64) (M.stepEvents evs1 st) s2 (memRegion cur 24 ∗ Frame)
          hpc2 hrun2 hsp2 hx19_2 hx20_2 hx21_2 hx24_2 hvregs2 htr2)
        fun sm _Pm _ _ ⟨evs2, hevs2, hPm, hacp3, hq⟩ => ?_
      refine ⟨evs1 ++ evs2, hevs1.append hevs2, Entails.trans hPm ?_, (hacp1.trans hacp2).trans hacp3, hq⟩
      rw [M.stepEvents_append]
      have hlen_split : (bs :: bs2 :: rest).length * 24 = 24 + (bs2 :: rest).length * 24 := by
        simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega
      rw [hlen_split, ProofLib.memRegion_split cur 24 ((bs2 :: rest).length * 24) (by omega)]
      exact Entails.of_eq (by sep_ac_rfl)

theorem fromPb_drop_vec_u8_776_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (fsp pbA ptsPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (rem : List (List (BitVec 8))) (hrem_ne : rem ≠ [])
    (hlen_bound : rem.length * 24 < 2 ^ 63)
    (st : M.σ) (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_376).base + 776#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx20 : s.readReg64 .x20 = pbA) (hx21 : s.readReg64 .x21 = ptsPtr)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 rem.length)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (htrace : s.trace = s0.trace) :
    SepWP ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      ((blkPl_376).base + 820#64) s
      (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr rem ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
          (Pm ⊢ memRegion ptsPtr (rem.length * 24) ∗ A.pool lim (M.stepEvents evs st) sm ∗
            stackAt fsp allocHookStack ∗ Frame) ∧
          AllocCallPreserved s sm ∧
          sm.sp = fsp ∧ sm.readReg64 .x20 = pbA ∧ sm.readReg64 .x21 = ptsPtr ∧
          calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) := by
  refine seq_vm_clean
    (mid := (blkPl_376).base + 796#64)
    (P_mid := arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr rem ∗
      A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm =>
      AllocCallPreserved s sm ∧
      sm.sp = fsp ∧ sm.readReg64 .x19 = ptsPtr + 8#64 ∧
      sm.readReg64 .x20 = pbA ∧ sm.readReg64 .x21 = ptsPtr ∧
      sm.readReg64 .x24 = BitVec.ofNat 64 rem.length ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
  · dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x24, BitVec.ofNat_eq_ofNat] at hpc hx20 hx21 hx24 ⊢
    by_vm_steps (wp_steps; simp only [AllocCallPreserved]; wp_done)
  · intro sm hpcm hrunm hvm1 ⟨hacp1, hspm, hx19m, hx20m, hx21m, hx24m, hvregsm, htrm⟩
    rw [← A.pool_of_vmPreserved hvm1]
    exact SepWP.mono
      (fromPb_drop_vec_u8_loop_placed_sepWP hdealloc s0 fsp pbA ptsPtr hfsp_align rem hrem_ne hlen_bound
        ptsPtr st sm Frame hpcm hrunm hspm hx19m hx20m hx21m hx24m hvregsm htrm)
      fun sf _Pf _ _ ⟨evs, hevs, hPf, hacp2, hq⟩ => ⟨evs, hevs, hPf, hacp1.trans hacp2, hq⟩

/-! ## Placed Error Exit A (`+712 -> s0.lr`, when `pb.pts.length ≠ 16`) -/

theorem fromPb_error_exit_712_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (fsp out pbA cap_pts ptsPtr : BitVec 64)
    (hfsp : HiddenEq fsp (s0.sp - 544#64))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (bss : List (List (BitVec 8)))
    (hle : bss.length ≤ cap_pts.toNat)
    (hcap_bound : cap_pts.toNat * 24 < 2 ^ 63)
    (hlen_bound : bss.length * 24 < 2 ^ 63)
    (st : M.σ) (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_376).base + 712#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out) (hx20 : s.readReg64 .x20 = pbA)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 bss.length)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (htrace : s.trace = s0.trace)
    (hlr_ls : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := by
      first
      | assumption
      | simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    SepWP ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion out 400 ∗
        (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
        ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 bss.length) ∗
        memRegion (pbA + 24#64) 16 ∗
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr bss ∗
        (if cap_pts = 0 then emp
          else A.repAlloc.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (bss.length * 24)) ((cap_pts.toNat - bss.length) * 24)) ∗
        savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗
        A.pool lim st s ∗ stackAt fsp dropGluePoly16Stack ∗ Frame)
      (fun sf P' =>
        ∃ evs, FreeOnlyEvs evs ∧
          (P' ⊢ resultPolyDecoderFromPbAt A.repAlloc out (.error .serializationInvalid) ∗
            memRegion pbA 40 ∗ A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp fromPbCoreStack ∗ Frame) ∧
          sf.sp = s0.sp ∧ AllocCallPreserved s sf ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  conv => arg 4; rw [memRegion_400_split_err out]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro d0
  apply ProofLib.SepWP.exists_left; intro b8
  have hrejoin_pb := pbA_rejoin_40 pbA cap_pts ptsPtr (BitVec.ofNat 64 bss.length)
  have hrejoin_buf := memRegion_rejoin_vecBuf A.repAlloc 24 8 cap_pts ptsPtr bss.length hle hcap_bound
  by_cases hbss0 : bss.length = 0
  · have hbss_nil : bss = [] := List.eq_nil_of_length_eq_zero hbss0
    subst hbss_nil
    refine seq_vm_clean (mid := (blkPl_376).base + 820#64)
      (P_mid := (pbA ↦₆₄ cap_pts) ∗ vecVecU8BufDealloc A.repAlloc cap_pts ptsPtr ∗
        savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗ A.pool lim st s ∗ stackAt fsp dropGluePoly16Stack ∗
        (resultPolyDecoderFromPbAt A.repAlloc out (.error .serializationInvalid) ∗
          ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 0#64) ∗ memRegion (pbA + 24#64) 16 ∗ Frame))
      (Q := fun sm => AllocCallPreserved s sm ∧ sm.sp = fsp ∧
        sm.readReg64 .x20 = pbA ∧ sm.readReg64 .x21 = ptsPtr ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
    · dsimp only [Reg.x0, Reg.x20, Reg.x21, Reg.x24, List.length_nil, BitVec.ofNat_eq_ofNat] at hpc hx0 hx20 hx24 ⊢
      by_vm_steps (
        wp_steps
        apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
        refine ⟨by simp [wp_norm, arm64_norm], ?_, by simp [AllocCallPreserved, wp_norm, arm64_norm, *]⟩
        unfold resultPolyDecoderFromPbAt vecVecU8BufDealloc noneCap
        dsimp only [resultPolyDecoderErrByteOff, resultPolyDecoderErrTailSize, polynomialErrorByte,
          List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat]
        simp only [arrayAt_nil, BitVec.add_zero, emp_sepConj, beq_iff_eq]
        exact Entails.of_eq (by sep_ac_rfl))
    · intro sm hpcm hrunm hvm1 ⟨hacp1, hspm, hx20m, hx21m, hvregsm, htrm⟩
      rw [← A.pool_of_vmPreserved hvm1]
      refine SepWP.mono
        (fromPb_tail_820_placed_sepWP hdealloc s0 fsp pbA ptsPtr cap_pts hfsp hsp0_align hfsp_align hcap_bound
          st sm _ hpcm hrunm hspm hx20m hx21m hvregsm htrm (hlr_ls := hlr_ls))
        fun sf _Pf _ _ ⟨evs, hevs, hPf, hspf, hacp2, hcsf, htrf⟩ => ?_
      have hpost_final :
          (pbA ↦₆₄ cap_pts) ∗ A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp fromPbCoreStack ∗
            (resultPolyDecoderFromPbAt A.repAlloc out (.error .serializationInvalid) ∗
              ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 0#64) ∗ memRegion (pbA + 24#64) 16 ∗ Frame) ⊢
          resultPolyDecoderFromPbAt A.repAlloc out (.error .serializationInvalid) ∗
            memRegion pbA 40 ∗ A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp fromPbCoreStack ∗ Frame :=
        replace_sub_entails hrejoin_pb
          (resultPolyDecoderFromPbAt A.repAlloc out (.error .serializationInvalid) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp fromPbCoreStack ∗ Frame)
          (by sep_ac_rfl) (by sep_ac_rfl)
      exact ⟨evs, hevs, Entails.trans hPf hpost_final, hspf, hacp1.trans hacp2, hcsf, htrf⟩
  · have hbss_ne : bss ≠ [] := by intro h; simp [h] at hbss0
    have hbeq0 : (BitVec.ofNat 64 bss.length == 0#64) = false := ofNat_beq_zero_false (by omega) (by omega)
    rw [fromPb_stackAt_dropGluePoly16_split_bottom fsp]
    refine seq_vm_clean (mid := (blkPl_376).base + 776#64)
      (P_mid := arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr bss ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗
        (resultPolyDecoderFromPbAt A.repAlloc out (.error .serializationInvalid) ∗
          (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 bss.length) ∗
          memRegion (pbA + 24#64) 16 ∗
          (if cap_pts = 0 then emp else A.repAlloc.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (bss.length * 24)) ((cap_pts.toNat - bss.length) * 24)) ∗
          savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗ memRegion (fsp - 4128#64) 32 ∗ Frame))
      (Q := fun sm => AllocCallPreserved s sm ∧ sm.sp = fsp ∧
        sm.readReg64 .x20 = pbA ∧ sm.readReg64 .x21 = ptsPtr ∧
        sm.readReg64 .x24 = BitVec.ofNat 64 bss.length ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
    · dsimp only [Reg.x0, Reg.x20, Reg.x21, Reg.x24, BitVec.ofNat_eq_ofNat] at hpc hx0 hx20 hx24 ⊢
      by_vm_steps (
        wp_steps
        apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
        refine ⟨by simp [wp_norm, arm64_norm], ?_, by simp [AllocCallPreserved, wp_norm, arm64_norm, *]⟩
        unfold resultPolyDecoderFromPbAt noneCap
        dsimp only [resultPolyDecoderErrByteOff, resultPolyDecoderErrTailSize, polynomialErrorByte, BitVec.ofNat_eq_ofNat]
        exact Entails.of_eq (by sep_ac_rfl))
    · intro s1 hpc1 hrun1 hvm1 ⟨hacp1, hsp1, hx20_1, hx21_1, hx24_1, hvregs1, htr1⟩
      rw [← A.pool_of_vmPreserved hvm1]
      refine seq_clean_evs
        (fromPb_drop_vec_u8_776_placed_sepWP hdealloc s0 fsp pbA ptsPtr hfsp_align bss hbss_ne hlen_bound
          st s1 _ hpc1 hrun1 hsp1 hx20_1 hx21_1 hx24_1 hvregs1 htr1) ?_
      intro evs1 s2 hevs1 hpc2 hrun2 ⟨hacp2, hsp2, hx20_2, hx21_2, hvregs2, htr2⟩
      have hpre_820 :
          memRegion ptsPtr (bss.length * 24) ∗ A.pool lim (M.stepEvents evs1 st) s2 ∗ stackAt fsp allocHookStack ∗
            (resultPolyDecoderFromPbAt A.repAlloc out (.error .serializationInvalid) ∗
              (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
              ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 bss.length) ∗
              memRegion (pbA + 24#64) 16 ∗
              (if cap_pts = 0 then emp
                else A.repAlloc.live ptsPtr (cap_pts.toNat * 24) 8 ∗
                  memRegion (ptsPtr + BitVec.ofNat 64 (bss.length * 24)) ((cap_pts.toNat - bss.length) * 24)) ∗
              savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗
              memRegion (fsp - 4128#64) 32 ∗ Frame) ⊢
          (pbA ↦₆₄ cap_pts) ∗ vecVecU8BufDealloc A.repAlloc cap_pts ptsPtr ∗
            savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗
            A.pool lim (M.stepEvents evs1 st) s2 ∗ stackAt fsp dropGluePoly16Stack ∗
            (resultPolyDecoderFromPbAt A.repAlloc out (.error .serializationInvalid) ∗
              ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
              ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 bss.length) ∗
              memRegion (pbA + 24#64) 16 ∗ Frame) := by
        rw [fromPb_stackAt_dropGluePoly16_split_bottom fsp]
        unfold vecVecU8BufDealloc
        exact replace_sub_entails hrejoin_buf
          ((pbA ↦₆₄ cap_pts) ∗ savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗
            A.pool lim (M.stepEvents evs1 st) s2 ∗ memRegion (fsp - 4128#64) 32 ∗ stackAt fsp allocHookStack ∗
            resultPolyDecoderFromPbAt A.repAlloc out (.error .serializationInvalid) ∗
            ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
            ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 bss.length) ∗
            memRegion (pbA + 24#64) 16 ∗ Frame) (by sep_ac_rfl) (by sep_ac_rfl)
      refine SepWP.weaken_pre hpre_820 ?_
      refine SepWP.mono
        (fromPb_tail_820_placed_sepWP hdealloc s0 fsp pbA ptsPtr cap_pts hfsp hsp0_align hfsp_align hcap_bound
          (M.stepEvents evs1 st) s2 _ hpc2 hrun2 hsp2 hx20_2 hx21_2 hvregs2 htr2 (hlr_ls := hlr_ls))
        fun sf _Pf _ _ ⟨evs2, hevs2, hPf, hspf, hacp3, hcsf, htrf⟩ => ?_
      have hpost_final :
          (pbA ↦₆₄ cap_pts) ∗ A.pool lim (M.stepEvents evs2 (M.stepEvents evs1 st)) sf ∗
            stackAt s0.sp fromPbCoreStack ∗
            (resultPolyDecoderFromPbAt A.repAlloc out (.error .serializationInvalid) ∗
              ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
              ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 bss.length) ∗
              memRegion (pbA + 24#64) 16 ∗ Frame) ⊢
          resultPolyDecoderFromPbAt A.repAlloc out (.error .serializationInvalid) ∗
            memRegion pbA 40 ∗ A.pool lim (M.stepEvents (evs1 ++ evs2) st) sf ∗
            stackAt s0.sp fromPbCoreStack ∗ Frame := by
        rw [M.stepEvents_append]
        exact replace_sub_entails hrejoin_pb
          (resultPolyDecoderFromPbAt A.repAlloc out (.error .serializationInvalid) ∗
            A.pool lim (M.stepEvents evs2 (M.stepEvents evs1 st)) sf ∗ stackAt s0.sp fromPbCoreStack ∗ Frame)
          (by sep_ac_rfl) (by sep_ac_rfl)
      exact ⟨evs1 ++ evs2, hevs1.append hevs2, Entails.trans hPf hpost_final,
        hspf, (hacp1.trans hacp2).trans hacp3, hcsf, htrf⟩

/-! ## Placed Error Exit B (`+740 -> s0.lr`, when `pb.pts.length = 16` and some `pts.length % 4 ≠ 0`) -/

theorem fromPb_error_exit_740_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hdrop : subroutine_ok ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext))
      (lsmpl.base 264) (dropGlueSortedSetPt16Spec M A lim))
    (s0 : State) (fsp out pbA cap_pts ptsPtr w416 w424 w432 : BitVec 64)
    (hfsp : HiddenEq fsp (s0.sp - 544#64))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (sets_err : List SortedSetPt) (hsets_len : sets_err.length = 16)
    (bss : List (List (BitVec 8))) (hbss_len : bss.length = 16)
    (hle : bss.length ≤ cap_pts.toNat)
    (hcap_bound : cap_pts.toNat * 24 < 2 ^ 63)
    (st : M.σ) (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_376).base + 740#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx21 : s.readReg64 .x21 = ptsPtr)
    (hx24 : s.readReg64 .x24 = 16#64) (hx29 : s.readReg64 .x29 = fsp + 448#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (htrace : s.trace = s0.trace)
    (hlr_ls : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := by
      first
      | assumption
      | simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    SepWP ((blkPC_376).rebase (blkPl_376).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion out 400 ∗ memRegion fsp 8 ∗
        ((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
        sortedSetPtListOf A.repAlloc (fsp + 32#64) sets_err ∗
        ((fsp + 416#64) ↦₆₄ w416) ∗ ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
        memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
        (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
        memRegion (pbA + 24#64) 16 ∗
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr bss ∗
        (if cap_pts = 0 then emp
          else A.repAlloc.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (bss.length * 24)) ((cap_pts.toNat - bss.length) * 24)) ∗
        memRegion (fsp - 4128#64) 32 ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sf P' =>
        ∃ evs, FreeOnlyEvs evs ∧
          (P' ⊢ resultPolyDecoderFromPbAt A.repAlloc out (.error .serializationInvalid) ∗
            memRegion pbA 40 ∗ A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp fromPbCoreStack ∗ Frame) ∧
          sf.sp = s0.sp ∧ AllocCallPreserved s sf ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  simp only [dropGlueSortedSetPt16Spec] at hdrop
  rw [sortedSetPtListOf_eq_vecPtListOf]
  conv => arg 4; rw [memRegion_400_split_err out]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro b8
  apply ProofLib.SepWP.exists_left; intro d0
  have hvecs_len : (sets_err.map SortedSetPt.vec).length = NUM_POLYS := by
    simp [hsets_len, NUM_POLYS, CHUNK_SIZE]
  refine align_pre_wp (seq_vm_clean (mid := (blkPl_376).base + 764#64)
      (Pre := (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₈ b8) ∗ memRegion (out + 9#64) 391 ∗ memRegion fsp 8 ∗
        ((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
        vecPtListOf A.repAlloc (fsp + 32#64) (sets_err.map SortedSetPt.vec) ∗
        ((fsp + 416#64) ↦₆₄ w416) ∗ ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
        memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
        (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
        memRegion (pbA + 24#64) 16 ∗ arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr bss ∗
        (if cap_pts = 0 then emp else A.repAlloc.live ptsPtr (cap_pts.toNat * 24) 8 ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (bss.length * 24)) ((cap_pts.toNat - bss.length) * 24)) ∗
        A.pool lim st s ∗ stackAt fsp dropGluePoly16Stack ∗ Frame)
      (P_mid := vecPtListOf A.repAlloc (fsp + 32#64) (sets_err.map SortedSetPt.vec) ∗
        A.pool lim st s ∗ stackAt fsp dropGluePoly16Stack ∗
        (resultPolyDecoderFromPbAt A.repAlloc out (.error .serializationInvalid) ∗ memRegion fsp 8 ∗
          ((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
          ((fsp + 416#64) ↦₆₄ w416) ∗ ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
          memRegion (fsp + 440#64) 8 ∗ savedRegsAt fsp s0 ∗
          (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
          memRegion (pbA + 24#64) 16 ∗ arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr bss ∗
          (if cap_pts = 0 then emp else A.repAlloc.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (bss.length * 24)) ((cap_pts.toNat - bss.length) * 24)) ∗ Frame))
      (Q := fun sc => AllocCallPreserved s sc ∧ sc.sp = fsp ∧ sc.readReg64 .x0 = fsp + 32#64 ∧
        sc.readReg64 .x21 = ptsPtr ∧ sc.readReg64 .x24 = 16#64 ∧
        calleeSavedVRegs sc = calleeSavedVRegs s0 ∧ sc.trace = s0.trace) ?_ ?_)
    (by rw [fromPb_stackAt_dropGluePoly16_split_bottom fsp]; sep_ac_rfl)
  · dsimp only [Reg.x0, Reg.x21, Reg.x24, Reg.x29, BitVec.ofNat_eq_ofNat] at hpc hx21 hx24 hx29 ⊢
    by_vm_steps (
      wp_steps 6
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
      refine ⟨by simp [wp_norm, arm64_norm], ?_, by simp [AllocCallPreserved, wp_norm, arm64_norm, *]⟩
      unfold resultPolyDecoderFromPbAt noneCap
      dsimp only [resultPolyDecoderErrByteOff, resultPolyDecoderErrTailSize, polynomialErrorByte, BitVec.ofNat_eq_ofNat]
      exact Entails.of_eq (by sep_ac_rfl))
  · intro sc hpcc hrun_c hvm_c ⟨hacp_c, hsp_c, hx0_c, hx21_c, hx24_c, hvregs_c, htr_c⟩
    rw [← A.pool_of_vmPreserved hvm_c]
    refine seq_clean_evs
      (mid := (blkPl_376).base + 776#64)
      (P_evs := fun evs1 sm =>
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr bss ∗
          A.pool lim (M.stepEvents evs1 st) sm ∗ stackAt fsp allocHookStack ∗
          (resultPolyDecoderFromPbAt A.repAlloc out (.error .serializationInvalid) ∗
            memRegion fsp 448 ∗ savedRegsAt fsp s0 ∗
            (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
            memRegion (pbA + 24#64) 16 ∗
            (if cap_pts = 0 then emp
              else A.repAlloc.live ptsPtr (cap_pts.toNat * 24) 8 ∗
                memRegion (ptsPtr + BitVec.ofNat 64 (bss.length * 24)) ((cap_pts.toNat - bss.length) * 24)) ∗
            memRegion (fsp - 4128#64) 32 ∗ Frame))
      (Q := fun sm =>
        AllocCallPreserved sc sm ∧
        sm.sp = fsp ∧ sm.readReg64 .x20 = pbA ∧ sm.readReg64 .x21 = ptsPtr ∧
        sm.readReg64 .x24 = BitVec.ofNat 64 bss.length ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0 ∧ sm.trace = s0.trace) ?_ ?_
    · dsimp only [Reg.x0, Reg.x20, Reg.x21, Reg.x24, BitVec.ofNat_eq_ofNat] at hdrop hpcc hx0_c hx21_c hx24_c ⊢
      wp_steps 1
      refine sync_pool_vm sc fun hvm_step => ?_
      wp_call hdrop ((⟨fsp + 32#64, sets_err.map SortedSetPt.vec⟩ : DropGlueSortedSetPt16Ghost), st)
      have hacp_drop' : AllocCallPreserved sc sf := by assumption
      rcases hacp_drop' with ⟨_, _, _, _, _, _, _⟩
      wp_steps
      refine sync_pool_vm sf fun hvm_after => ?_
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_sf])
      refine ⟨_, ‹FreeOnlyEvs _›, ?_, ?_⟩
      · rw [hsp_c, fromPb_stackAt_dropGluePoly16_split_bottom fsp]
        dsimp only [polyArrayBytes]
        have hfsp448 := fsp_rejoin_448 fsp out pbA ptsPtr w416 w424 w432
        exact replace_sub_entails hfsp448
          (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr bss ∗
            A.pool lim (M.stepEvents _ st) _ ∗ stackAt fsp allocHookStack ∗
            (resultPolyDecoderFromPbAt A.repAlloc out (.error .serializationInvalid) ∗
              savedRegsAt fsp s0 ∗
              (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
              memRegion (pbA + 24#64) 16 ∗
              (if cap_pts = 0 then emp
                else A.repAlloc.live ptsPtr (cap_pts.toNat * 24) 8 ∗
                  memRegion (ptsPtr + BitVec.ofNat 64 (bss.length * 24)) ((cap_pts.toNat - bss.length) * 24)) ∗
              memRegion (fsp - 4128#64) 32 ∗ Frame)) (by sep_ac_rfl) (by sep_ac_rfl)
      · rw [hbss_len]
        simp [AllocCallPreserved, wp_norm, arm64_norm, *]
    · intro evs1 s1 hevs1 hpc1 hrun1 ⟨hacp1, hsp1, hx20_1, hx21_1, hx24_1, hvregs1, htr1⟩
      have hbss_ne : bss ≠ [] := by intro h; simp [h] at hbss_len
      have hlen_bound : bss.length * 24 < 2 ^ 63 := by rw [hbss_len]; decide
      have hrejoin_pb := pbA_rejoin_40 pbA cap_pts ptsPtr 16#64
      have hrejoin_buf := memRegion_rejoin_vecBuf A.repAlloc 24 8 cap_pts ptsPtr bss.length hle hcap_bound
      refine seq_clean_evs
        (fromPb_drop_vec_u8_776_placed_sepWP hdealloc s0 fsp pbA ptsPtr hfsp_align bss hbss_ne hlen_bound
          (M.stepEvents evs1 st) s1 _ hpc1 hrun1 hsp1 hx20_1 hx21_1 hx24_1 hvregs1 htr1) ?_
      intro evs2 s2 hevs2 hpc2 hrun2 ⟨hacp2, hsp2, hx20_2, hx21_2, hvregs2, htr2⟩
      have hpre_820 :
          memRegion ptsPtr (bss.length * 24) ∗ A.pool lim (M.stepEvents evs2 (M.stepEvents evs1 st)) s2 ∗
            stackAt fsp allocHookStack ∗
            (resultPolyDecoderFromPbAt A.repAlloc out (.error .serializationInvalid) ∗
              memRegion fsp 448 ∗ savedRegsAt fsp s0 ∗
              (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗
              memRegion (pbA + 24#64) 16 ∗
              (if cap_pts = 0 then emp else A.repAlloc.live ptsPtr (cap_pts.toNat * 24) 8 ∗
                memRegion (ptsPtr + BitVec.ofNat 64 (bss.length * 24)) ((cap_pts.toNat - bss.length) * 24)) ∗
              memRegion (fsp - 4128#64) 32 ∗ Frame) ⊢
          (pbA ↦₆₄ cap_pts) ∗ vecVecU8BufDealloc A.repAlloc cap_pts ptsPtr ∗ savedRegsAt fsp s0 ∗
            memRegion fsp 448 ∗ A.pool lim (M.stepEvents evs2 (M.stepEvents evs1 st)) s2 ∗
            stackAt fsp dropGluePoly16Stack ∗
            (resultPolyDecoderFromPbAt A.repAlloc out (.error .serializationInvalid) ∗
              ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗ memRegion (pbA + 24#64) 16 ∗ Frame) := by
        rw [fromPb_stackAt_dropGluePoly16_split_bottom fsp]; unfold vecVecU8BufDealloc
        exact replace_sub_entails hrejoin_buf
          ((pbA ↦₆₄ cap_pts) ∗ savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗
            A.pool lim (M.stepEvents evs2 (M.stepEvents evs1 st)) s2 ∗ memRegion (fsp - 4128#64) 32 ∗
            stackAt fsp allocHookStack ∗ resultPolyDecoderFromPbAt A.repAlloc out (.error .serializationInvalid) ∗
            ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗ memRegion (pbA + 24#64) 16 ∗ Frame)
          (by sep_ac_rfl) (by sep_ac_rfl)
      refine SepWP.weaken_pre hpre_820 (SepWP.mono
        (fromPb_tail_820_placed_sepWP hdealloc s0 fsp pbA ptsPtr cap_pts hfsp hsp0_align hfsp_align hcap_bound
          (M.stepEvents evs2 (M.stepEvents evs1 st)) s2 _ hpc2 hrun2 hsp2 hx20_2 hx21_2 hvregs2 htr2 (hlr_ls := hlr_ls))
        fun sf _Pf _ _ ⟨evs3, hevs3, hPf, hspf, hacp3, hcsf, htrf⟩ => ?_)
      have hpost_final :
          (pbA ↦₆₄ cap_pts) ∗ A.pool lim (M.stepEvents evs3 (M.stepEvents evs2 (M.stepEvents evs1 st))) sf ∗
            stackAt s0.sp fromPbCoreStack ∗
            (resultPolyDecoderFromPbAt A.repAlloc out (.error .serializationInvalid) ∗
              ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ 16#64) ∗ memRegion (pbA + 24#64) 16 ∗ Frame) ⊢
          resultPolyDecoderFromPbAt A.repAlloc out (.error .serializationInvalid) ∗ memRegion pbA 40 ∗
            A.pool lim (M.stepEvents ((evs1 ++ evs2) ++ evs3) st) sf ∗ stackAt s0.sp fromPbCoreStack ∗ Frame := by
        rw [M.stepEvents_append, M.stepEvents_append]
        exact replace_sub_entails hrejoin_pb
          (resultPolyDecoderFromPbAt A.repAlloc out (.error .serializationInvalid) ∗
            A.pool lim (M.stepEvents evs3 (M.stepEvents evs2 (M.stepEvents evs1 st))) sf ∗
            stackAt s0.sp fromPbCoreStack ∗ Frame) (by sep_ac_rfl) (by sep_ac_rfl)
      exact ⟨(evs1 ++ evs2) ++ evs3, (hevs1.append hevs2).append hevs3, Entails.trans hPf hpost_final,
        hspf, ((hacp_c.trans hacp1).trans hacp2).trans hacp3, hcsf, htrf⟩

end LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbExitPlacedBudget
