/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoderBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget
public import LibsignalBinary.Heap.IfaceBudgetBase
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hscBudgetAux
public meta import LibsignalBinary.Proofs.CodeLayout -- shake: keep
import GeneratedLean.LibsignalSessionCode -- shake: keep
meta import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Drop.Decodes
meta import LibsignalBinary.Proofs.SpqrV1.Drop.Decodes -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
meta import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Fixed-Offset Budget-Threaded SPQR Drop Glue Helpers

Fixed-offset `subroutine_ok` contracts on `dropProgAtExt` for `drop_glue::<[Poly; 16]>`,
`drop_glue::<PolyEncoder> [local#2]`, and `drop_glue::<Unchunked::SendEk::EkSent>` under
`AllocContracts4K`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsdBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (libsignalSessionCode)
open CryptoVerification.LibsignalSpqrV1 (GF16 NUM_POLYS PolyEncoder)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetProgAtExt)
open CryptoVerification.RustHeap (RustAlloc allocHookStack arrayAt)
open CryptoVerification.SpqrV1.Drop (
  DropGluePoly16Ghost DropGluePolyEncoderGhost DropUnchunkedEkSentGhost
  Saved32Preserved Saved32x19Preserved cap0_poly16_post cells4_entails_stack32_bottom
  dropGluePoly16Stack dropPoly16Name dropPoly16_fnOff dropPolyEncoderLocal2Name
  dropPolyEncoderLocal2_fnOff dropProgAtExt dropStack32 dropUnchunkedEkSentName
  list_length_16_elim polyEncoderAt_entails_tag_vecs_tail polyEncoder_local2_post_join
  stackAt_dropGluePoly16_split stackAt_dropStack32_split
  stack_restore_32_allocHook tail_dealloc_poly16_post tail_dealloc_poly16_pre_weaken
  tail_dealloc_unchunked_post threeVec80HeadersAt threeVec80HeadersAt_entails_memRegion_80
  unchunkedEkSentAt unchunkedEkSentAt_entails_dealloc unchunkedEkSentSize
  vecCapPtrDealloc vecGF16Dealloc vecGF16ListOf vecGF16Of vecGF16Of_step_entails
)
open CryptoVerification.SpqrV1.Poly (polyArrayBytes polyEncoderAt polyEncoderSize)
open CryptoVerification.SpqrV1.Layout.Stubs (
  fnOff_drop_ek_sent fnOff_drop_poly16 fnOff_drop_poly_encoder_local2 stubOff_rust_dealloc
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
  RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpecBase rustDeallocEvents
)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (trapHooks)
open LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget (AllocContracts4K)
open LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget (dropGluePoly16Spec dropGluePoly16SpecBase)
open LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoderBudget (dropGluePolyEncoderSpec dropGluePolyEncoderSpecBase)
open LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget (dropUnchunkedEkSentSpecBase)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hscBudgetAux (
  deallocFreeOnlySpec fnAddr_rebase_hooks_eq sepWP_evs_dealloc sepWP_evs_nil
  seq_clean_evs seq_vm_clean subroutine_ok_deallocFreeOnly
)
open scoped CryptoVerification.CodeLayout

open Lean Elab Tactic ProofLib ProofLib.ProgramReflection in
scoped elab "drop_fetches_sym " b:term:max H:term:max sym:str len:num : tactic => do
  let eOff ← ProofLib.CodeLookup.lookup ``CryptoVerification.libsignalSessionCode .fnOff sym.getString
  let hfn := mkCIdentFrom sym eOff.decl
  let offLit := Syntax.mkNumLit (toString eOff.val)
  evalTactic (← `(tactic|
    code_fetches CryptoVerification.libsignalSessionCode CryptoVerification.SpqrV1.Drop.spqrDropChainEpochBin $b $H $hfn $offLit $len))

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Local Step Combinators -/

private theorem sub_ok_of_addr_eq {P : Program} {a1 a2 : BitVec 64} {α : Type} {S : Spec α}
    (heq : a1 = a2) (h : subroutine_ok P a1 S) : subroutine_ok P a2 S :=
  heq ▸ h

private theorem align_pre_st {prog : Program} {target : BitVec 64} {s : State}
    {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    (heq : P = P_mid s)
    (h : SepWP prog target s (P_mid s) (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm) := by
  subst heq; exact h

private theorem seq_evs_step {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {mid target : BitVec 64}
    {s : State} {st : M.σ} {P X1 X2 X3 : SepProp}
    {P_mid : M.σ → State → SepProp}
    {Q_mid Q_out : State → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm =>
      ∃ evs1, FreeOnlyEvs evs1 ∧ (Pm ⊢ P_mid (M.stepEvents evs1 st) sm) ∧ Q_mid sm))
    (h2 : ∀ (st1 : M.σ) (sm : State),
      sm.pc = mid → sm.status = .Running → Q_mid sm →
      SepWP prog target sm (P_mid st1 sm) (fun sf Pf =>
        ∃ evs2, FreeOnlyEvs evs2 ∧
          (Pf ⊢ X1 ∗ (X2 ∗ (A.pool lim (M.stepEvents evs2 st1) sf ∗ X3))) ∧ Q_out sf)) :
    SepWP prog target s P (fun sf Pf =>
      ∃ evs, FreeOnlyEvs evs ∧
        (Pf ⊢ X1 ∗ (X2 ∗ (A.pool lim (M.stepEvents evs st) sf ∗ X3))) ∧ Q_out sf) := by
  refine SepWP.seq h1 fun sm _Pm hpc hrun ⟨evs1, hevs1, hent, hQ⟩ => ?_
  refine SepWP.weaken_pre hent ?_
  refine SepWP.mono (h2 (M.stepEvents evs1 st) sm hpc hrun hQ) fun sf _Pf _ _ ⟨evs2, hevs2, hp, hq⟩ => ?_
  refine ⟨evs1 ++ evs2, hevs1.append hevs2, ?_, hq⟩
  rwa [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]

private theorem sepWP_close_drop {prog : Program} {s0 s : State} {P : SepProp}
    {Post : State → SepProp → Prop}
    (Q_out : State → SepProp)
    (h : SepWP prog (s0.readReg64 .lr) s P (fun sf Pf =>
      (Pf ⊢ Q_out sf) ∧
      sf.sp = s0.sp ∧ sf.trace = s0.trace ∧
      AllocCallPreserved s0 sf ∧ CalleeSavedPreserved s0 sf))
    (hpost : ∀ sf Pf, (Pf ⊢ Q_out sf) → sf.sp = s0.sp → sf.trace = s0.trace →
      AllocCallPreserved s0 sf → CalleeSavedPreserved s0 sf → Post sf Pf) :
    SepWP prog (s0.readReg64 .lr) s P Post :=
  SepWP.mono h fun sf Pf _ _ ⟨hp, hsp_f, htr_f, hacp_f, hcs_f⟩ =>
    hpost sf Pf hp hsp_f htr_f hacp_f hcs_f

/-! ## Fixed-Offset `drop_glue::<[spqr::encoding::polynomial::Poly; 16]>` -/

private theorem drop_glue_poly16_part1
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc_fo : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropPoly16Name +
        bv% (ls_rel% "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>" "__rustc::__rust_dealloc"))
      (deallocFreeOnlySpec M A lim))
    (s0 : State) (fsp arrA : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (c0 c1 c2 c3 : List GF16) (rest : List (List GF16))
    (st : M.σ) (s : State) (Frame : SepProp)
    (hpc : s.pc = (dropProgAtExt b ext).fnAddr dropPoly16Name + 12#64)
    (hrun : s.status = .Running)
    (hacp : AllocCallPreserved s0 s)
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
      ((dropProgAtExt b ext).fnAddr dropPoly16Name + 112#64)
      s
      (vecGF16ListOf A.repAlloc arrA (c0 :: c1 :: c2 :: c3 :: rest) ∗
        (A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame))
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ vecGF16ListOf A.repAlloc (arrA + 96#64) rest ∗
          (memRegion arrA 96 ∗ (A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame))) ∧
        Saved32Preserved s0 sm fsp arrA ∧ AllocCallPreserved s0 sm) := by
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpecBase] at hdealloc_fo
  drop_fetches_sym b (Rust.withPanics ext)
    "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>" 116
  dsimp only [dropProgAtExt, dropPoly16Name, BitVec.ofNat_eq_ofNat] at *
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>" = fnEntry
  examples_hide_fetches
  have ⟨_, _, _, _, _, _, _⟩ := hacp
  refine seq_evs_step (mid := fnEntry + 40#64)
    (P_mid := fun st1 sm =>
      vecGF16ListOf A.repAlloc (arrA + 24#64) (c1 :: c2 :: c3 :: rest) ∗
        (memRegion arrA 24 ∗ (A.pool lim st1 sm ∗ stackAt fsp allocHookStack ∗ Frame)))
    (Q_mid := fun sm => Saved32Preserved s0 sm fsp arrA ∧ AllocCallPreserved s0 sm) ?_ ?_
  · refine LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget.SepWP.dealloc_list_cons0_step arrA c0 _ _
      (fun evs sm => A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ?_
    intro cap ptr
    dsimp only [vecGF16Dealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live, Saved32Preserved]
    by_cases hcap : (cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp]
    · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]; wp_steps; wp_done
    · apply sepWP_evs_dealloc (cap <<< 1#64).toNat 2
      wp_steps; wp_apply; rw [hsp]
      have hacp' : AllocCallPreserved s0 sf := hacp.trans (by assumption)
      rcases hacp' with ⟨_, _, _, _, _, _, _⟩
      refine align_pre_st (by sep_ac_rfl) ?_; wp_done
  · intro st1 s1 hpc1 hrun1 ⟨⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hsp_1, htrace_1, hvregs_1⟩, hacp_1⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp_1
    refine seq_evs_step (mid := fnEntry + 64#64)
      (P_mid := fun st2 sm =>
        vecGF16ListOf A.repAlloc (arrA + 48#64) (c2 :: c3 :: rest) ∗
          (memRegion arrA 48 ∗ (A.pool lim st2 sm ∗ stackAt fsp allocHookStack ∗ Frame)))
      (Q_mid := fun sm => Saved32Preserved s0 sm fsp arrA ∧ AllocCallPreserved s0 sm) ?_ ?_
    · refine LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget.SepWP.dealloc_list_cons_step arrA 24#64 32#64 40#64 48#64 24 48 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c1 _ _
        (fun evs sm => A.pool lim (M.stepEvents evs st1) sm ∗ stackAt fsp allocHookStack ∗ Frame) ?_
      intro cap ptr
      dsimp only [vecGF16Dealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live, Saved32Preserved]
      by_cases hcap : (cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp]
      · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]; wp_steps; wp_done
      · apply sepWP_evs_dealloc (cap <<< 1#64).toNat 2
        wp_steps; wp_apply; rw [hsp_1]
        have hacp' : AllocCallPreserved s0 sf := hacp_1.trans (by assumption)
        rcases hacp' with ⟨_, _, _, _, _, _, _⟩
        refine align_pre_st (by sep_ac_rfl) ?_; wp_done
    · intro st2 s2 hpc2 hrun2 ⟨⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hsp_2, htrace_2, hvregs_2⟩, hacp_2⟩
      have ⟨_, _, _, _, _, _, _⟩ := hacp_2
      refine seq_evs_step (mid := fnEntry + 88#64)
        (P_mid := fun st3 sm =>
          vecGF16ListOf A.repAlloc (arrA + 72#64) (c3 :: rest) ∗
            (memRegion arrA 72 ∗ (A.pool lim st3 sm ∗ stackAt fsp allocHookStack ∗ Frame)))
        (Q_mid := fun sm => Saved32Preserved s0 sm fsp arrA ∧ AllocCallPreserved s0 sm) ?_ ?_
      · refine LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget.SepWP.dealloc_list_cons_step arrA 48#64 56#64 64#64 72#64 48 72 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c2 _ _
          (fun evs sm => A.pool lim (M.stepEvents evs st2) sm ∗ stackAt fsp allocHookStack ∗ Frame) ?_
        intro cap ptr
        dsimp only [vecGF16Dealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live, Saved32Preserved]
        by_cases hcap : (cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp]
        · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]; wp_steps; wp_done
        · apply sepWP_evs_dealloc (cap <<< 1#64).toNat 2
          wp_steps; wp_apply; rw [hsp_2]
          have hacp' : AllocCallPreserved s0 sf := hacp_2.trans (by assumption)
          rcases hacp' with ⟨_, _, _, _, _, _, _⟩
          refine align_pre_st (by sep_ac_rfl) ?_; wp_done
      · intro st3 s3 hpc3 hrun3 ⟨⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3, hsp_3, htrace_3, hvregs_3⟩, hacp_3⟩
        have ⟨_, _, _, _, _, _, _⟩ := hacp_3
        refine LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget.SepWP.dealloc_list_cons_step arrA 72#64 80#64 88#64 96#64 72 96 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c3 _ _
          (fun evs sm => A.pool lim (M.stepEvents evs st3) sm ∗ stackAt fsp allocHookStack ∗ Frame) ?_
        intro cap ptr
        dsimp only [vecGF16Dealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live, Saved32Preserved]
        by_cases hcap : (cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp]
        · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]; wp_steps; wp_done
        · apply sepWP_evs_dealloc (cap <<< 1#64).toNat 2
          wp_steps; wp_apply; rw [hsp_3]
          have hacp' : AllocCallPreserved s0 sf := hacp_3.trans (by assumption)
          rcases hacp' with ⟨_, _, _, _, _, _, _⟩
          refine align_pre_st (by sep_ac_rfl) ?_; wp_done

private theorem drop_glue_poly16_part2
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc_fo : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropPoly16Name +
        bv% (ls_rel% "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>" "__rustc::__rust_dealloc"))
      (deallocFreeOnlySpec M A lim))
    (s0 : State) (fsp arrA : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (c4 c5 c6 c7 : List GF16) (rest : List (List GF16))
    (st : M.σ) (s : State) (Frame : SepProp)
    (hpc : s.pc = (dropProgAtExt b ext).fnAddr dropPoly16Name + 112#64)
    (hrun : s.status = .Running)
    (hpres : Saved32Preserved s0 s fsp arrA)
    (hacp : AllocCallPreserved s0 s) :
    SepWP (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropPoly16Name + 208#64)
      s
      (vecGF16ListOf A.repAlloc (arrA + 96#64) (c4 :: c5 :: c6 :: c7 :: rest) ∗
        (memRegion arrA 96 ∗ (A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)))
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ vecGF16ListOf A.repAlloc (arrA + 192#64) rest ∗
          (memRegion arrA 192 ∗ (A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame))) ∧
        Saved32Preserved s0 sm fsp arrA ∧ AllocCallPreserved s0 sm) := by
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpecBase] at hdealloc_fo
  drop_fetches_sym b (Rust.withPanics ext)
    "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>" 212
  dsimp only [dropProgAtExt, dropPoly16Name, BitVec.ofNat_eq_ofNat] at *
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>" = fnEntry
  examples_hide_fetches
  rcases hpres with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4, hsp_4, htrace_4, hvregs_4⟩
  have ⟨_, _, _, _, _, _, _⟩ := hacp
  refine seq_evs_step (mid := fnEntry + 136#64)
    (P_mid := fun st5 sm =>
      vecGF16ListOf A.repAlloc (arrA + 120#64) (c5 :: c6 :: c7 :: rest) ∗
        (memRegion arrA 120 ∗ (A.pool lim st5 sm ∗ stackAt fsp allocHookStack ∗ Frame)))
    (Q_mid := fun sm => Saved32Preserved s0 sm fsp arrA ∧ AllocCallPreserved s0 sm) ?_ ?_
  · refine LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget.SepWP.dealloc_list_cons_step arrA 96#64 104#64 112#64 120#64 96 120 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c4 _ _
      (fun evs sm => A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ?_
    intro cap ptr
    dsimp only [vecGF16Dealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live, Saved32Preserved]
    by_cases hcap : (cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp]
    · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]; wp_steps; wp_done
    · apply sepWP_evs_dealloc (cap <<< 1#64).toNat 2
      wp_steps; wp_apply; rw [hsp_4]
      have hacp' : AllocCallPreserved s0 sf := hacp.trans (by assumption)
      rcases hacp' with ⟨_, _, _, _, _, _, _⟩
      refine align_pre_st (by sep_ac_rfl) ?_; wp_done
  · intro st5 s5 hpc5 hrun5 ⟨⟨hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hx29_5, hsp_5, htrace_5, hvregs_5⟩, hacp_5⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp_5
    refine seq_evs_step (mid := fnEntry + 160#64)
      (P_mid := fun st6 sm =>
        vecGF16ListOf A.repAlloc (arrA + 144#64) (c6 :: c7 :: rest) ∗
          (memRegion arrA 144 ∗ (A.pool lim st6 sm ∗ stackAt fsp allocHookStack ∗ Frame)))
      (Q_mid := fun sm => Saved32Preserved s0 sm fsp arrA ∧ AllocCallPreserved s0 sm) ?_ ?_
    · refine LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget.SepWP.dealloc_list_cons_step arrA 120#64 128#64 136#64 144#64 120 144 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c5 _ _
        (fun evs sm => A.pool lim (M.stepEvents evs st5) sm ∗ stackAt fsp allocHookStack ∗ Frame) ?_
      intro cap ptr
      dsimp only [vecGF16Dealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live, Saved32Preserved]
      by_cases hcap : (cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp]
      · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]; wp_steps; wp_done
      · apply sepWP_evs_dealloc (cap <<< 1#64).toNat 2
        wp_steps; wp_apply; rw [hsp_5]
        have hacp' : AllocCallPreserved s0 sf := hacp_5.trans (by assumption)
        rcases hacp' with ⟨_, _, _, _, _, _, _⟩
        refine align_pre_st (by sep_ac_rfl) ?_; wp_done
    · intro st6 s6 hpc6 hrun6 ⟨⟨hx19_6, hx20_6, hx21_6, hx22_6, hx23_6, hx24_6, hx25_6, hx26_6, hx27_6, hx28_6, hx29_6, hsp_6, htrace_6, hvregs_6⟩, hacp_6⟩
      have ⟨_, _, _, _, _, _, _⟩ := hacp_6
      refine seq_evs_step (mid := fnEntry + 184#64)
        (P_mid := fun st7 sm =>
          vecGF16ListOf A.repAlloc (arrA + 168#64) (c7 :: rest) ∗
            (memRegion arrA 168 ∗ (A.pool lim st7 sm ∗ stackAt fsp allocHookStack ∗ Frame)))
        (Q_mid := fun sm => Saved32Preserved s0 sm fsp arrA ∧ AllocCallPreserved s0 sm) ?_ ?_
      · refine LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget.SepWP.dealloc_list_cons_step arrA 144#64 152#64 160#64 168#64 144 168 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c6 _ _
          (fun evs sm => A.pool lim (M.stepEvents evs st6) sm ∗ stackAt fsp allocHookStack ∗ Frame) ?_
        intro cap ptr
        dsimp only [vecGF16Dealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live, Saved32Preserved]
        by_cases hcap : (cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp]
        · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]; wp_steps; wp_done
        · apply sepWP_evs_dealloc (cap <<< 1#64).toNat 2
          wp_steps; wp_apply; rw [hsp_6]
          have hacp' : AllocCallPreserved s0 sf := hacp_6.trans (by assumption)
          rcases hacp' with ⟨_, _, _, _, _, _, _⟩
          refine align_pre_st (by sep_ac_rfl) ?_; wp_done
      · intro st7 s7 hpc7 hrun7 ⟨⟨hx19_7, hx20_7, hx21_7, hx22_7, hx23_7, hx24_7, hx25_7, hx26_7, hx27_7, hx28_7, hx29_7, hsp_7, htrace_7, hvregs_7⟩, hacp_7⟩
        have ⟨_, _, _, _, _, _, _⟩ := hacp_7
        refine LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget.SepWP.dealloc_list_cons_step arrA 168#64 176#64 184#64 192#64 168 192 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c7 _ _
          (fun evs sm => A.pool lim (M.stepEvents evs st7) sm ∗ stackAt fsp allocHookStack ∗ Frame) ?_
        intro cap ptr
        dsimp only [vecGF16Dealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live, Saved32Preserved]
        by_cases hcap : (cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp]
        · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]; wp_steps; wp_done
        · apply sepWP_evs_dealloc (cap <<< 1#64).toNat 2
          wp_steps; wp_apply; rw [hsp_7]
          have hacp' : AllocCallPreserved s0 sf := hacp_7.trans (by assumption)
          rcases hacp' with ⟨_, _, _, _, _, _, _⟩
          refine align_pre_st (by sep_ac_rfl) ?_; wp_done

private theorem drop_glue_poly16_part3
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc_fo : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropPoly16Name +
        bv% (ls_rel% "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>" "__rustc::__rust_dealloc"))
      (deallocFreeOnlySpec M A lim))
    (s0 : State) (fsp arrA : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (c8 c9 c10 c11 : List GF16) (rest : List (List GF16))
    (st : M.σ) (s : State) (Frame : SepProp)
    (hpc : s.pc = (dropProgAtExt b ext).fnAddr dropPoly16Name + 208#64)
    (hrun : s.status = .Running)
    (hpres : Saved32Preserved s0 s fsp arrA)
    (hacp : AllocCallPreserved s0 s) :
    SepWP (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropPoly16Name + 304#64)
      s
      (vecGF16ListOf A.repAlloc (arrA + 192#64) (c8 :: c9 :: c10 :: c11 :: rest) ∗
        (memRegion arrA 192 ∗ (A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)))
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ vecGF16ListOf A.repAlloc (arrA + 288#64) rest ∗
          (memRegion arrA 288 ∗ (A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame))) ∧
        Saved32Preserved s0 sm fsp arrA ∧ AllocCallPreserved s0 sm) := by
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpecBase] at hdealloc_fo
  drop_fetches_sym b (Rust.withPanics ext)
    "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>" 308
  dsimp only [dropProgAtExt, dropPoly16Name, BitVec.ofNat_eq_ofNat] at *
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>" = fnEntry
  examples_hide_fetches
  rcases hpres with ⟨hx19_8, hx20_8, hx21_8, hx22_8, hx23_8, hx24_8, hx25_8, hx26_8, hx27_8, hx28_8, hx29_8, hsp_8, htrace_8, hvregs_8⟩
  have ⟨_, _, _, _, _, _, _⟩ := hacp
  refine seq_evs_step (mid := fnEntry + 232#64)
    (P_mid := fun st9 sm =>
      vecGF16ListOf A.repAlloc (arrA + 216#64) (c9 :: c10 :: c11 :: rest) ∗
        (memRegion arrA 216 ∗ (A.pool lim st9 sm ∗ stackAt fsp allocHookStack ∗ Frame)))
    (Q_mid := fun sm => Saved32Preserved s0 sm fsp arrA ∧ AllocCallPreserved s0 sm) ?_ ?_
  · refine LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget.SepWP.dealloc_list_cons_step arrA 192#64 200#64 208#64 216#64 192 216 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c8 _ _
      (fun evs sm => A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ?_
    intro cap ptr
    dsimp only [vecGF16Dealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live, Saved32Preserved]
    by_cases hcap : (cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp]
    · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]; wp_steps; wp_done
    · apply sepWP_evs_dealloc (cap <<< 1#64).toNat 2
      wp_steps; wp_apply; rw [hsp_8]
      have hacp' : AllocCallPreserved s0 sf := hacp.trans (by assumption)
      rcases hacp' with ⟨_, _, _, _, _, _, _⟩
      refine align_pre_st (by sep_ac_rfl) ?_; wp_done
  · intro st9 s9 hpc9 hrun9 ⟨⟨hx19_9, hx20_9, hx21_9, hx22_9, hx23_9, hx24_9, hx25_9, hx26_9, hx27_9, hx28_9, hx29_9, hsp_9, htrace_9, hvregs_9⟩, hacp_9⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp_9
    refine seq_evs_step (mid := fnEntry + 256#64)
      (P_mid := fun st10 sm =>
        vecGF16ListOf A.repAlloc (arrA + 240#64) (c10 :: c11 :: rest) ∗
          (memRegion arrA 240 ∗ (A.pool lim st10 sm ∗ stackAt fsp allocHookStack ∗ Frame)))
      (Q_mid := fun sm => Saved32Preserved s0 sm fsp arrA ∧ AllocCallPreserved s0 sm) ?_ ?_
    · refine LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget.SepWP.dealloc_list_cons_step arrA 216#64 224#64 232#64 240#64 216 240 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c9 _ _
        (fun evs sm => A.pool lim (M.stepEvents evs st9) sm ∗ stackAt fsp allocHookStack ∗ Frame) ?_
      intro cap ptr
      dsimp only [vecGF16Dealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live, Saved32Preserved]
      by_cases hcap : (cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp]
      · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]; wp_steps; wp_done
      · apply sepWP_evs_dealloc (cap <<< 1#64).toNat 2
        wp_steps; wp_apply; rw [hsp_9]
        have hacp' : AllocCallPreserved s0 sf := hacp_9.trans (by assumption)
        rcases hacp' with ⟨_, _, _, _, _, _, _⟩
        refine align_pre_st (by sep_ac_rfl) ?_; wp_done
    · intro st10 s10 hpc10 hrun10 ⟨⟨hx19_10, hx20_10, hx21_10, hx22_10, hx23_10, hx24_10, hx25_10, hx26_10, hx27_10, hx28_10, hx29_10, hsp_10, htrace_10, hvregs_10⟩, hacp_10⟩
      have ⟨_, _, _, _, _, _, _⟩ := hacp_10
      refine seq_evs_step (mid := fnEntry + 280#64)
        (P_mid := fun st11 sm =>
          vecGF16ListOf A.repAlloc (arrA + 264#64) (c11 :: rest) ∗
            (memRegion arrA 264 ∗ (A.pool lim st11 sm ∗ stackAt fsp allocHookStack ∗ Frame)))
        (Q_mid := fun sm => Saved32Preserved s0 sm fsp arrA ∧ AllocCallPreserved s0 sm) ?_ ?_
      · refine LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget.SepWP.dealloc_list_cons_step arrA 240#64 248#64 256#64 264#64 240 264 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c10 _ _
          (fun evs sm => A.pool lim (M.stepEvents evs st10) sm ∗ stackAt fsp allocHookStack ∗ Frame) ?_
        intro cap ptr
        dsimp only [vecGF16Dealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live, Saved32Preserved]
        by_cases hcap : (cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp]
        · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]; wp_steps; wp_done
        · apply sepWP_evs_dealloc (cap <<< 1#64).toNat 2
          wp_steps; wp_apply; rw [hsp_10]
          have hacp' : AllocCallPreserved s0 sf := hacp_10.trans (by assumption)
          rcases hacp' with ⟨_, _, _, _, _, _, _⟩
          refine align_pre_st (by sep_ac_rfl) ?_; wp_done
      · intro st11 s11 hpc11 hrun11 ⟨⟨hx19_11, hx20_11, hx21_11, hx22_11, hx23_11, hx24_11, hx25_11, hx26_11, hx27_11, hx28_11, hx29_11, hsp_11, htrace_11, hvregs_11⟩, hacp_11⟩
        have ⟨_, _, _, _, _, _, _⟩ := hacp_11
        refine LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget.SepWP.dealloc_list_cons_step arrA 264#64 272#64 280#64 288#64 264 288 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c11 _ _
          (fun evs sm => A.pool lim (M.stepEvents evs st11) sm ∗ stackAt fsp allocHookStack ∗ Frame) ?_
        intro cap ptr
        dsimp only [vecGF16Dealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live, Saved32Preserved]
        by_cases hcap : (cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp]
        · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]; wp_steps; wp_done
        · apply sepWP_evs_dealloc (cap <<< 1#64).toNat 2
          wp_steps; wp_apply; rw [hsp_11]
          have hacp' : AllocCallPreserved s0 sf := hacp_11.trans (by assumption)
          rcases hacp' with ⟨_, _, _, _, _, _, _⟩
          refine align_pre_st (by sep_ac_rfl) ?_; wp_done

private theorem drop_glue_poly16_part4
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc_fo : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropPoly16Name +
        bv% (ls_rel% "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>" "__rustc::__rust_dealloc"))
      (deallocFreeOnlySpec M A lim))
    (s0 : State) (fsp arrA : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (c12 c13 c14 : List GF16) (rest : List (List GF16))
    (st : M.σ) (s : State) (Frame : SepProp)
    (hpc : s.pc = (dropProgAtExt b ext).fnAddr dropPoly16Name + 304#64)
    (hrun : s.status = .Running)
    (hpres : Saved32Preserved s0 s fsp arrA)
    (hacp : AllocCallPreserved s0 s) :
    SepWP (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropPoly16Name + 376#64)
      s
      (vecGF16ListOf A.repAlloc (arrA + 288#64) (c12 :: c13 :: c14 :: rest) ∗
        (memRegion arrA 288 ∗ (A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)))
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ vecGF16ListOf A.repAlloc (arrA + 360#64) rest ∗
          (memRegion arrA 360 ∗ (A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame))) ∧
        Saved32Preserved s0 sm fsp arrA ∧ AllocCallPreserved s0 sm) := by
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpecBase] at hdealloc_fo
  drop_fetches_sym b (Rust.withPanics ext)
    "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>" 380
  dsimp only [dropProgAtExt, dropPoly16Name, BitVec.ofNat_eq_ofNat] at *
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>" = fnEntry
  examples_hide_fetches
  rcases hpres with ⟨hx19_12, hx20_12, hx21_12, hx22_12, hx23_12, hx24_12, hx25_12, hx26_12, hx27_12, hx28_12, hx29_12, hsp_12, htrace_12, hvregs_12⟩
  have ⟨_, _, _, _, _, _, _⟩ := hacp
  refine seq_evs_step (mid := fnEntry + 328#64)
    (P_mid := fun st13 sm =>
      vecGF16ListOf A.repAlloc (arrA + 312#64) (c13 :: c14 :: rest) ∗
        (memRegion arrA 312 ∗ (A.pool lim st13 sm ∗ stackAt fsp allocHookStack ∗ Frame)))
    (Q_mid := fun sm => Saved32Preserved s0 sm fsp arrA ∧ AllocCallPreserved s0 sm) ?_ ?_
  · refine LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget.SepWP.dealloc_list_cons_step arrA 288#64 296#64 304#64 312#64 288 312 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c12 _ _
      (fun evs sm => A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ?_
    intro cap ptr
    dsimp only [vecGF16Dealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live, Saved32Preserved]
    by_cases hcap : (cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp]
    · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]; wp_steps; wp_done
    · apply sepWP_evs_dealloc (cap <<< 1#64).toNat 2
      wp_steps; wp_apply; rw [hsp_12]
      have hacp' : AllocCallPreserved s0 sf := hacp.trans (by assumption)
      rcases hacp' with ⟨_, _, _, _, _, _, _⟩
      refine align_pre_st (by sep_ac_rfl) ?_; wp_done
  · intro st13 s13 hpc13 hrun13 ⟨⟨hx19_13, hx20_13, hx21_13, hx22_13, hx23_13, hx24_13, hx25_13, hx26_13, hx27_13, hx28_13, hx29_13, hsp_13, htrace_13, hvregs_13⟩, hacp_13⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp_13
    refine seq_evs_step (mid := fnEntry + 352#64)
      (P_mid := fun st14 sm =>
        vecGF16ListOf A.repAlloc (arrA + 336#64) (c14 :: rest) ∗
          (memRegion arrA 336 ∗ (A.pool lim st14 sm ∗ stackAt fsp allocHookStack ∗ Frame)))
      (Q_mid := fun sm => Saved32Preserved s0 sm fsp arrA ∧ AllocCallPreserved s0 sm) ?_ ?_
    · refine LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget.SepWP.dealloc_list_cons_step arrA 312#64 320#64 328#64 336#64 312 336 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c13 _ _
        (fun evs sm => A.pool lim (M.stepEvents evs st13) sm ∗ stackAt fsp allocHookStack ∗ Frame) ?_
      intro cap ptr
      dsimp only [vecGF16Dealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live, Saved32Preserved]
      by_cases hcap : (cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp]
      · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]; wp_steps; wp_done
      · apply sepWP_evs_dealloc (cap <<< 1#64).toNat 2
        wp_steps; wp_apply; rw [hsp_13]
        have hacp' : AllocCallPreserved s0 sf := hacp_13.trans (by assumption)
        rcases hacp' with ⟨_, _, _, _, _, _, _⟩
        refine align_pre_st (by sep_ac_rfl) ?_; wp_done
    · intro st14 s14 hpc14 hrun14 ⟨⟨hx19_14, hx20_14, hx21_14, hx22_14, hx23_14, hx24_14, hx25_14, hx26_14, hx27_14, hx28_14, hx29_14, hsp_14, htrace_14, hvregs_14⟩, hacp_14⟩
      have ⟨_, _, _, _, _, _, _⟩ := hacp_14
      refine LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget.SepWP.dealloc_list_cons_step arrA 336#64 344#64 352#64 360#64 336 360 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c14 _ _
        (fun evs sm => A.pool lim (M.stepEvents evs st14) sm ∗ stackAt fsp allocHookStack ∗ Frame) ?_
      intro cap ptr
      dsimp only [vecGF16Dealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live, Saved32Preserved]
      by_cases hcap : (cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp]
      · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]; wp_steps; wp_done
      · apply sepWP_evs_dealloc (cap <<< 1#64).toNat 2
        wp_steps; wp_apply; rw [hsp_14]
        have hacp' : AllocCallPreserved s0 sf := hacp_14.trans (by assumption)
        rcases hacp' with ⟨_, _, _, _, _, _, _⟩
        refine align_pre_st (by sep_ac_rfl) ?_; wp_done

/-- Fixed-offset `core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>` satisfies
`dropGluePoly16SpecBase M A lim` on `dropProgAtExt b ext` under `AllocContracts4K b A lim ext`. -/
theorem drop_glue_poly16_ok_ext
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropPoly16Name)
      (dropGluePoly16SpecBase M A lim) := by
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropPoly16Name +
        bv% (ls_rel% "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>" "__rustc::__rust_dealloc"))
      (rustCliDeallocBudgetSpecBase M A lim) :=
    hA.dealloc_ok_at dropPoly16Name
      (num% (ls_rel% "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>" "__rustc::__rust_dealloc"))
      (by simp only [dropPoly16Name, fnOff_drop_poly16, stubOff_rust_dealloc, arm64_norm])
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_raw
  have hpart1 := drop_glue_poly16_part1 (b := b) (ext := ext) hdealloc_fo
  have hpart2 := drop_glue_poly16_part2 (b := b) (ext := ext) hdealloc_fo
  have hpart3 := drop_glue_poly16_part3 (b := b) (ext := ext) hdealloc_fo
  have hpart4 := drop_glue_poly16_part4 (b := b) (ext := ext) hdealloc_fo
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpecBase] at hdealloc_fo
  simp only [dropGluePoly16SpecBase]
  apply subroutine_ok_of_sepWP_init
  rintro ⟨⟨arrA, vecs⟩, st⟩ R s0 hpc hrun hpre hsp_align
  dsimp only [NUM_POLYS, DropGluePoly16Ghost.arrA, DropGluePoly16Ghost.vecs] at hpre ⊢
  have hpre' : s0.mem ⊨ ⌜s0.readReg64 .x0 = arrA ∧ vecs.length = 16⌝ ∗
      ((vecGF16ListOf A.repAlloc arrA vecs ∗ A.pool lim st s0 ∗ stackAt s0.sp dropGluePoly16Stack) ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨⟨hx0, hlen⟩, hpre'⟩
  refine ⟨_, hpre', ?_⟩
  subst hx0
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, rfl⟩ :=
    list_length_16_elim hlen
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 hsp_align (by decide)
  nth_rw 1 [stackAt_dropGluePoly16_split s0.sp]
  cells_unfold
  wp_pull_exists
  rename_i w0 w1 w2 w3
  refine seq_vm_clean (P := libsignalSessionCode) (b := b) (Hk := Rust.withPanics ext)
    (mid := (dropProgAtExt b ext).fnAddr dropPoly16Name + 12#64)
    (P_mid :=
      vecGF16ListOf A.repAlloc (s0.readReg64 .x0)
        [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15] ∗
      (A.pool lim st s0 ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3))))
    (Q := fun sm =>
      AllocCallPreserved s0 sm ∧
      sm.readReg64 .x0 = s0.readReg64 .x0 ∧
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
  · drop_fetches_sym b trapHooks
      "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>" 16
    dsimp only [dropProgAtExt, dropPoly16Name, BitVec.ofNat_eq_ofNat] at *
    rw [fnAddr_rebase_hooks_eq libsignalSessionCode b trapHooks (Rust.withPanics ext)] at *
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr
      "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>" = entry
    examples_hide_fetches
    by_vm_steps {
      wp_steps
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, *])
      refine ⟨by simp [wp_norm, arm64_norm], ?_, by simp [AllocCallPreserved, wp_norm, arm64_norm, *]⟩
      dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x29, Reg.x30]
      simp only [wp_norm, arm64_norm]
      exact Entails.of_eq (by sep_ac_rfl)
    }
  · intro s1 hpc1 hrun1 hvm1 ⟨hacp1, hx0_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hsp_1, htrace_1, hvregs_1⟩
    rw [← A.pool_of_vmPreserved hvm1]
    refine seq_clean_evs (mid := (dropProgAtExt b ext).fnAddr dropPoly16Name + 112#64)
      (P_evs := fun evs1 sm =>
        vecGF16ListOf A.repAlloc (s0.readReg64 .x0 + 96#64)
          [c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15] ∗
        (memRegion (s0.readReg64 .x0) 96 ∗
          (A.pool lim (M.stepEvents evs1 st) sm ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
            (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3)))))
      (Q := fun sm => Saved32Preserved s0 sm (s0.sp - 32#64) (s0.readReg64 .x0) ∧ AllocCallPreserved s0 sm)
      (hpart1 s0 (s0.sp - 32#64) (s0.readReg64 .x0) hfsp_align
        c0 c1 c2 c3 [c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15] st s1 _
        hpc1 hrun1 hacp1 hx0_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hsp_1 htrace_1 hvregs_1)
      ?_
    intro evs1 sa hevs1 hpca hruna ⟨hpresa, hacpa⟩
    refine seq_clean_evs (mid := (dropProgAtExt b ext).fnAddr dropPoly16Name + 208#64)
      (P_evs := fun evs2 sm =>
        vecGF16ListOf A.repAlloc (s0.readReg64 .x0 + 192#64)
          [c8, c9, c10, c11, c12, c13, c14, c15] ∗
        (memRegion (s0.readReg64 .x0) 192 ∗
          (A.pool lim (M.stepEvents evs2 (M.stepEvents evs1 st)) sm ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
            (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3)))))
      (Q := fun sm => Saved32Preserved s0 sm (s0.sp - 32#64) (s0.readReg64 .x0) ∧ AllocCallPreserved s0 sm)
      (hpart2 s0 (s0.sp - 32#64) (s0.readReg64 .x0) hfsp_align
        c4 c5 c6 c7 [c8, c9, c10, c11, c12, c13, c14, c15] (M.stepEvents evs1 st) sa _ hpca hruna hpresa hacpa)
      ?_
    intro evs2 s2 hevs2 hpc2 hrun2 ⟨hpres2, hacp2⟩
    refine seq_clean_evs (mid := (dropProgAtExt b ext).fnAddr dropPoly16Name + 304#64)
      (P_evs := fun evs3 sm =>
        vecGF16ListOf A.repAlloc (s0.readReg64 .x0 + 288#64) [c12, c13, c14, c15] ∗
        (memRegion (s0.readReg64 .x0) 288 ∗
          (A.pool lim (M.stepEvents evs3 (M.stepEvents evs2 (M.stepEvents evs1 st))) sm ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
            (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3)))))
      (Q := fun sm => Saved32Preserved s0 sm (s0.sp - 32#64) (s0.readReg64 .x0) ∧ AllocCallPreserved s0 sm)
      (hpart3 s0 (s0.sp - 32#64) (s0.readReg64 .x0) hfsp_align
        c8 c9 c10 c11 [c12, c13, c14, c15] (M.stepEvents evs2 (M.stepEvents evs1 st)) s2 _ hpc2 hrun2 hpres2 hacp2)
      ?_
    intro evs3 sb hevs3 hpcb hrunb ⟨hpresb, hacpb⟩
    refine seq_clean_evs (mid := (dropProgAtExt b ext).fnAddr dropPoly16Name + 376#64)
      (P_evs := fun evs4 sm =>
        vecGF16ListOf A.repAlloc (s0.readReg64 .x0 + 360#64) [c15] ∗
        (memRegion (s0.readReg64 .x0) 360 ∗
          (A.pool lim (M.stepEvents evs4 (M.stepEvents evs3 (M.stepEvents evs2 (M.stepEvents evs1 st)))) sm ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
            (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3)))))
      (Q := fun sm => Saved32Preserved s0 sm (s0.sp - 32#64) (s0.readReg64 .x0) ∧ AllocCallPreserved s0 sm)
      (hpart4 s0 (s0.sp - 32#64) (s0.readReg64 .x0) hfsp_align
        c12 c13 c14 [c15] (M.stepEvents evs3 (M.stepEvents evs2 (M.stepEvents evs1 st))) sb _ hpcb hrunb hpresb hacpb)
      ?_
    intro evs4 s3 hevs4 hpc3 hrun3 ⟨⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3, hsp_3, htrace_3, hvregs_3⟩, hacp3⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp3
    let evs14 := evs1 ++ evs2 ++ evs3 ++ evs4
    have hevs14 : FreeOnlyEvs evs14 := ((hevs1.append hevs2).append hevs3).append hevs4
    let st3 := M.stepEvents evs4 (M.stepEvents evs3 (M.stepEvents evs2 (M.stepEvents evs1 st)))
    drop_fetches_sym b (Rust.withPanics ext)
      "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>" 420
    dsimp only [dropProgAtExt, dropPoly16Name, BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc3 ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr
      "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>" = entry
    examples_hide_fetches
    have hsingleton : vecGF16ListOf A.repAlloc (s0.readReg64 .x0 + 360#64) [c15] =
        vecGF16Of A.repAlloc (s0.readReg64 .x0 + 360#64) c15 := by
      simp only [vecGF16ListOf, arrayAt, sepConj_emp]
    rw [hsingleton]
    refine SepWP.weaken_pre
      (vecGF16Of_step_entails A.repAlloc (s0.readReg64 .x0) 360#64 368#64 376#64 (by bv_omega) (by bv_omega) c15 _) ?_
    apply SepWP.exists_left; intro cap
    apply SepWP.exists_left; intro ptr
    dsimp only [vecGF16Dealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
    by_cases hcap : (cap == 0#64) = true <;>
      simp only [hcap, Bool.false_eq_true, ↓reduceIte, sepConj_emp]
    · refine sepWP_close_drop
        (fun sf => memRegion (s0.readReg64 .x0) polyArrayBytes ∗
          A.pool lim (M.stepEvents evs14 st) sf ∗ stackAt s0.sp dropGluePoly16Stack) ?_
        (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
      · have heq_st : M.stepEvents evs14 st = st3 := by
          simp only [evs14, st3, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
        rw [heq_st]
        wp_steps
        refine SepWP.weaken_pre
          (Entails.trans (Entails.of_eq (by sep_ac_rfl))
            (cap0_poly16_post (s0.readReg64 .x0) cap ptr (A.pool lim st3 s3) s0.sp
              (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) w3)) ?_
        wp_done
      · try rw [sepExists_sepConj_left]
        rw [satisfies_sepExists]; refine ⟨evs14, ?_⟩
        repeat rw [sepConj_assoc]
        rw [satisfies_pure_sepConj]
        refine ⟨⟨htr_f, hacp_f, hevs14⟩, ?_⟩
        exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm
    · refine sepWP_close_drop
        (fun sf => memRegion (s0.readReg64 .x0) polyArrayBytes ∗
          A.pool lim (M.stepEvents (evs14 ++ rustDeallocEvents (cap <<< 1#64).toNat 2) st) sf ∗
          stackAt s0.sp dropGluePoly16Stack) ?_
        (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
      · have heq_st : M.stepEvents (evs14 ++ rustDeallocEvents (cap <<< 1#64).toNat 2) st =
            M.stepEvents (rustDeallocEvents (cap <<< 1#64).toNat 2) st3 := by
          simp only [evs14, st3, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
        rw [heq_st]
        have htail : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 .lr) s3
            ((((s0.readReg64 .x0 + 360#64) ↦₆₄ cap) ∗ ((s0.readReg64 .x0 + 368#64) ↦₆₄ ptr) ∗
              memRegion (s0.readReg64 .x0 + 376#64) 8 ∗
              (A.live ptr (cap <<< 1#64).toNat 2 ∗ memRegion ptr (cap <<< 1#64).toNat)) ∗
              (memRegion (s0.readReg64 .x0) 360 ∗
                (A.pool lim st3 s3 ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
                  (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
                   ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3)))))
            (fun sf Pf =>
              (Pf ⊢ memRegion (s0.readReg64 .x0) polyArrayBytes ∗
                A.pool lim (M.stepEvents (rustDeallocEvents (cap <<< 1#64).toNat 2) st3) sf ∗
                stackAt s0.sp dropGluePoly16Stack) ∧
              sf.sp = s0.sp ∧ sf.trace = s0.trace ∧
              AllocCallPreserved s3 sf ∧ CalleeSavedPreserved s0 sf) := by
          wp_steps
          refine SepWP.weaken_pre
            (Entails.trans (Entails.of_eq (by sep_ac_rfl))
              (tail_dealloc_poly16_pre_weaken (s0.readReg64 .x0) cap ptr
                (A.live ptr (cap <<< 1#64).toNat 2 ∗ memRegion ptr (cap <<< 1#64).toNat)
                (memRegion (s0.readReg64 .x0) 360) (A.pool lim st3 s3) s0.sp
                (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) w3)) ?_
          wp_call hdealloc_fo (ptr, (cap <<< 1#64).toNat, 2, st3)
          have hpost3 : AllocCallPreserved s3 sf := by assumption
          rcases hpost3 with ⟨_, _, _, _, _, _, _⟩
          refine SepWP.weaken_pre
            (tail_dealloc_poly16_post (s0.readReg64 .x0)
              (A.pool lim (M.stepEvents (rustDeallocEvents (cap <<< 1#64).toNat 2) st3) sf) s0.sp) ?_
          wp_done
        exact SepWP.mono htail fun _ _ _ _ ⟨hp, hsp_f, htr_f, hacp_3f, hcs_f⟩ =>
          ⟨hp, hsp_f, htr_f, hacp3.trans hacp_3f, hcs_f⟩
      · try rw [sepExists_sepConj_left]
        rw [satisfies_sepExists]
        refine ⟨evs14 ++ rustDeallocEvents (cap <<< 1#64).toNat 2, ?_⟩
        repeat rw [sepConj_assoc]
        rw [satisfies_pure_sepConj]
        refine ⟨⟨htr_f, hacp_f, hevs14.append (LibsignalBinary.Heap.FreeOnlyEvs.singleton 2 (cap <<< 1#64).toNat)⟩, ?_⟩
        exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm

/-! ## Fixed-Offset `drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#2]` -/

/-- Fixed-offset `core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#2]`
(2 instructions: `add x0, x0, #8; b ...`) satisfies `dropGluePolyEncoderSpecBase M A lim`
on `dropProgAtExt b ext` under `AllocContracts4K b A lim ext`. -/
theorem drop_glue_poly_encoder_local2_ok_ext
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropPolyEncoderLocal2Name)
      (dropGluePolyEncoderSpecBase M A lim) := by
  have hpoly16_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropPolyEncoderLocal2Name +
        (0#64 - BitVec.ofNat 64 (ls_rel% "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>" "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#2]")))
      (dropGluePoly16SpecBase M A lim) := by
    have hrel : (dropProgAtExt b ext).fnAddr dropPolyEncoderLocal2Name =
        (dropProgAtExt b ext).fnAddr dropPoly16Name +
          BitVec.ofNat 64 (ls_rel% "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>" "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#2]") :=
      Program.fnAddr_rel
        (k := ls_rel% "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>" "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#2]")
        (b := b) (X := Rust.withPanics ext)
        dropPoly16_fnOff dropPolyEncoderLocal2_fnOff (by decide)
    refine sub_ok_of_addr_eq ?_ (drop_glue_poly16_ok_ext hA)
    rw [hrel, BitVec.add_assoc]
    simp
  simp only [dropGluePolyEncoderSpecBase]
  apply subroutine_ok_of_sepWP_init
  rintro ⟨⟨encA, enc⟩, st⟩ R s0 hpc hrun hpre hsp_align
  dsimp only [DropGluePolyEncoderGhost.encA, DropGluePolyEncoderGhost.enc] at hpre ⊢
  have hpre' : s0.mem ⊨ ⌜s0.readReg64 .x0 = encA⌝ ∗
      ((polyEncoderAt A.repAlloc encA enc ∗ A.pool lim st s0 ∗ stackAt s0.sp dropGluePoly16Stack) ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨hx0, hpre'⟩
  refine ⟨_, hpre', ?_⟩
  subst hx0
  refine SepWP.weaken_pre
    (sepConj_mono_left (polyEncoderAt_entails_tag_vecs_tail A.repAlloc (s0.readReg64 .x0) enc)) ?_
  rw [sepExists_sepConj_left]; apply SepWP.exists_left; intro tag
  rw [sepExists_sepConj_left]; apply SepWP.exists_left; intro vecs
  wp_focus_pure
  intro hvecs_len
  refine seq_vm_clean (P := libsignalSessionCode) (b := b) (Hk := Rust.withPanics ext)
    (mid := (dropProgAtExt b ext).fnAddr dropPolyEncoderLocal2Name +
      (0#64 - BitVec.ofNat 64 (ls_rel% "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>" "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#2]")))
    (P_mid :=
      vecGF16ListOf A.repAlloc (s0.readReg64 .x0 + 8#64) vecs ∗
      A.pool lim st s0 ∗ stackAt s0.sp dropGluePoly16Stack ∗
      ((s0.readReg64 .x0 ↦₆₄ tag) ∗ memRegion (s0.readReg64 .x0 + 392#64) 8))
    (Q := fun sc =>
      sc.sp = s0.sp ∧ sc.trace = s0.trace ∧
      sc.readReg64 .x0 = s0.readReg64 .x0 + 8#64 ∧ sc.readReg64 .lr = s0.readReg64 .lr ∧
      AllocCallPreserved s0 sc ∧ CalleeSavedPreserved s0 sc)
    ?_ ?_
  · drop_fetches_sym b trapHooks
      "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#2]" 8
    dsimp only [dropProgAtExt, dropPolyEncoderLocal2Name, BitVec.ofNat_eq_ofNat] at *
    rw [fnAddr_rebase_hooks_eq libsignalSessionCode b trapHooks (Rust.withPanics ext)] at *
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr
      "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#2]" = entry
    examples_hide_fetches
    simp only [BitVec.reduceSub]
    by_vm_steps {
      wp_steps
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, *])
      refine ⟨by simp [wp_norm, arm64_norm], ?_,
        by simp [AllocCallPreserved, CalleeSavedPreserved, wp_norm, arm64_norm, *]⟩
      simp only [wp_norm, arm64_norm]
      exact Entails.of_eq (by sep_ac_rfl)
    }
  · intro sc hpcc hrunc hvmc ⟨hsp_c, htr_c, hx0_c, hlr_c, hacp_c, hcs_c⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp_c
    rw [← A.pool_of_vmPreserved hvmc, ← hsp_c]
    dsimp only [dropProgAtExt, dropPolyEncoderLocal2Name, BitVec.ofNat_eq_ofNat] at hpoly16_raw hpcc ⊢
    simp only [BitVec.reduceSub] at hpoly16_raw hpcc
    wp_call hpoly16_raw (⟨s0.readReg64 .x0 + 8#64, vecs⟩, st)
    rw [hsp_c]
    have hacp_cf : AllocCallPreserved sc sf := by assumption
    have hevs_w : FreeOnlyEvs w := by assumption
    have hacp_f : AllocCallPreserved s0 sf := hacp_c.trans hacp_cf
    have ⟨_, _, _, _, _, _, _⟩ := hacp_f
    refine SepWP.focus_weaken
      (polyEncoder_local2_post_join (s0.readReg64 .x0) tag)
      (by sep_focus) ?_
    refine sepWP_close_drop
      (fun sf' => memRegion (s0.readReg64 .x0) polyEncoderSize ∗
        A.pool lim (M.stepEvents w st) sf' ∗ stackAt s0.sp dropGluePoly16Stack)
      (by wp_done)
      (fun sf' _Pf hp hsp_f htr_f hacp_f' hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
    try rw [sepExists_sepConj_left]
    rw [satisfies_sepExists]
    refine ⟨w, ?_⟩
    repeat rw [sepConj_assoc]
    rw [satisfies_pure_sepConj]
    exact ⟨⟨htr_f, hacp_f', hevs_w⟩,
      Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm⟩

/-! ## Fixed-Offset `drop_glue::<spqr::v1::unchunked::send_ek::EkSent>` -/

/-- Fixed-offset `core::ptr::drop_glue::<spqr::v1::unchunked::send_ek::EkSent>` (24 instructions)
satisfies `dropUnchunkedEkSentSpecBase M A lim F` on `dropProgAtExt b ext` under `AllocContracts4K b A lim ext`. -/
theorem drop_unchunked_ek_sent_ok_ext
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropUnchunkedEkSentName)
      (dropUnchunkedEkSentSpecBase M A lim F) := by
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropUnchunkedEkSentName +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::v1::unchunked::send_ek::EkSent>" "__rustc::__rust_dealloc"))
      (rustCliDeallocBudgetSpecBase M A lim) :=
    hA.dealloc_ok_at dropUnchunkedEkSentName
      (num% (ls_rel% "core::ptr::drop_glue::<spqr::v1::unchunked::send_ek::EkSent>" "__rustc::__rust_dealloc"))
      (by simp only [dropUnchunkedEkSentName, fnOff_drop_ek_sent, stubOff_rust_dealloc, arm64_norm])
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_raw
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpecBase] at hdealloc_fo
  simp only [dropUnchunkedEkSentSpecBase]
  dsimp only [unchunkedEkSentSize] at *
  apply subroutine_ok_of_sepWP_init
  rintro ⟨⟨a, st⟩, st0⟩ R s0 hpc hrun hpre hsp_align
  dsimp only [DropUnchunkedEkSentGhost.a, DropUnchunkedEkSentGhost.st] at hpre ⊢
  have hpre' : s0.mem ⊨ ⌜s0.readReg64 .x0 = a⌝ ∗
      ((unchunkedEkSentAt A.repAlloc a st ∗ A.pool lim st0 s0 ∗ stackAt s0.sp dropStack32) ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨hx0, hpre'⟩
  refine ⟨_, hpre', ?_⟩
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 hsp_align (by decide)
  nth_rw 1 [stackAt_dropStack32_split s0.sp]
  cells_unfold
  wp_pull_exists
  rename_i fp_old lr_old x19_old w3_old
  refine SepWP.weaken_pre (sepConj_mono_left (unchunkedEkSentAt_entails_dealloc A.repAlloc a st)) ?_
  rw [sepExists_sepConj_left]
  apply SepWP.exists_left; intro g
  refine seq_clean_evs (mid := (dropProgAtExt b ext).fnAddr dropUnchunkedEkSentName + 36#64)
    (P_evs := fun evs sm => (threeVec80HeadersAt a g ∗
      vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
      vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr) ∗
      A.pool lim (M.stepEvents evs st0) sm ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
    (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · dsimp only [threeVec80HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
    by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · refine seq_vm_clean (P := libsignalSessionCode) (b := b) (Hk := Rust.withPanics ext)
        (mid := (dropProgAtExt b ext).fnAddr dropUnchunkedEkSentName + 36#64)
        (P_mid := (threeVec80HeadersAt a g ∗
          vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
          vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr) ∗
          A.pool lim st0 s0 ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
          (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
        (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
        ?_ ?_
      · drop_fetches_sym b trapHooks
          "core::ptr::drop_glue::<spqr::v1::unchunked::send_ek::EkSent>" 96
        dsimp only [dropProgAtExt, dropUnchunkedEkSentName, threeVec80HeadersAt, vecCapPtrDealloc,
          LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live, BitVec.ofNat_eq_ofNat] at *
        rw [fnAddr_rebase_hooks_eq libsignalSessionCode b trapHooks (Rust.withPanics ext)] at *
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "core::ptr::drop_glue::<spqr::v1::unchunked::send_ek::EkSent>" = entry
        examples_hide_fetches
        by_vm_steps {
          wp_steps
          apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, *])
          refine ⟨by simp [wp_norm, arm64_norm], ?_,
            by simp [Saved32x19Preserved, AllocCallPreserved, wp_norm, arm64_norm, *]⟩
          dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x29, Reg.x30]
          simp only [wp_norm, arm64_norm]
          exact Entails.of_eq (by sep_ac_rfl)
        }
      · intro sm hpcm hrunm hvmm ⟨⟨hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩, hacpm, hx19m⟩
        have ⟨_, _, _, _, _, _, _⟩ := hacpm
        rw [← A.pool_of_vmPreserved hvmm]
        apply sepWP_evs_nil
        simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
        dsimp only [dropProgAtExt, dropUnchunkedEkSentName, threeVec80HeadersAt, vecCapPtrDealloc,
          LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live, BitVec.ofNat_eq_ofNat] at hpcm ⊢
        apply SepWP.done hpcm hrunm
        exact ⟨Entails.refl _, ⟨hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩, hacpm, hx19m⟩
    · refine seq_vm_clean (P := libsignalSessionCode) (b := b) (Hk := Rust.withPanics ext)
        (mid := (dropProgAtExt b ext).fnAddr dropUnchunkedEkSentName + 32#64)
        (P_mid := (threeVec80HeadersAt a g ∗
          (A.live g.v1.ptr g.v1.cap.toNat 1 ∗ memRegion g.v1.ptr g.v1.cap.toNat) ∗
          vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
          vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr) ∗
          A.pool lim st0 s0 ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
          (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
        (Q := fun sc => Saved32x19Preserved s0 sc (s0.sp - 32#64) ∧ AllocCallPreserved s0 sc ∧
          sc.readReg64 .x19 = a ∧ sc.readReg64 .x0 = g.v1.ptr ∧
          sc.readReg64 .x1 = g.v1.cap ∧ sc.readReg64 .x2 = 1#64)
        ?_ ?_
      · drop_fetches_sym b trapHooks
          "core::ptr::drop_glue::<spqr::v1::unchunked::send_ek::EkSent>" 96
        dsimp only [dropProgAtExt, dropUnchunkedEkSentName, threeVec80HeadersAt, vecCapPtrDealloc,
          LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live, BitVec.ofNat_eq_ofNat] at *
        rw [fnAddr_rebase_hooks_eq libsignalSessionCode b trapHooks (Rust.withPanics ext)] at *
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "core::ptr::drop_glue::<spqr::v1::unchunked::send_ek::EkSent>" = entry
        examples_hide_fetches
        by_vm_steps {
          wp_steps
          apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, *])
          refine ⟨by simp [wp_norm, arm64_norm], ?_,
            by simp [Saved32x19Preserved, AllocCallPreserved, wp_norm, arm64_norm, *]⟩
          dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x29, Reg.x30]
          simp only [wp_norm, arm64_norm]
          exact Entails.of_eq (by sep_ac_rfl)
        }
      · intro sc hpcc hrunc hvmc ⟨⟨hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hsp_c, htrace, hvregs⟩, hacp_c, hx19_c, hx0_c, hx1_c, hx2_c⟩
        have ⟨_, _, _, _, _, _, _⟩ := hacp_c
        rw [← A.pool_of_vmPreserved hvmc]
        drop_fetches_sym b (Rust.withPanics ext)
          "core::ptr::drop_glue::<spqr::v1::unchunked::send_ek::EkSent>" 96
        dsimp only [dropProgAtExt, dropUnchunkedEkSentName, threeVec80HeadersAt, vecCapPtrDealloc,
          LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live, BitVec.ofNat_eq_ofNat] at hdealloc_fo hpcc ⊢
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "core::ptr::drop_glue::<spqr::v1::unchunked::send_ek::EkSent>" = entry
        examples_hide_fetches
        apply sepWP_evs_dealloc g.v1.cap.toNat 1
        wp_steps; wp_apply; rw [hsp_c]
        have hacp' : AllocCallPreserved s0 sf := hacp_c.trans (by assumption)
        rcases hacp' with ⟨_, _, _, _, _, _, _⟩
        dsimp only [Saved32x19Preserved]
        refine align_pre_st (by sep_ac_rfl) ?_; wp_done
  · intro evs1 s1 hevs1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hacp_1, hx19_1⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp_1
    let st1 := M.stepEvents evs1 st0
    drop_fetches_sym b (Rust.withPanics ext)
      "core::ptr::drop_glue::<spqr::v1::unchunked::send_ek::EkSent>" 96
    dsimp only [dropProgAtExt, dropUnchunkedEkSentName, BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "core::ptr::drop_glue::<spqr::v1::unchunked::send_ek::EkSent>" = fnEntry
    examples_hide_fetches
    refine seq_clean_evs (mid := fnEntry + 56#64)
      (P_evs := fun evs sm => (threeVec80HeadersAt a g ∗
        vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr) ∗
        A.pool lim (M.stepEvents evs st1) sm ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
      (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
      ?_ ?_
    · dsimp only [threeVec80HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live, Saved32x19Preserved]
      by_cases hc2 : (g.v2.cap == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]; wp_steps; wp_done
      · apply sepWP_evs_dealloc g.v2.cap.toNat 1
        wp_steps; wp_apply; rw [hsp_1]
        have hacp' : AllocCallPreserved s0 sf := hacp_1.trans (by assumption)
        rcases hacp' with ⟨_, _, _, _, _, _, _⟩
        refine align_pre_st (by sep_ac_rfl) ?_; wp_done
    · intro evs2 s2 hevs2 hpc2 hrun2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hacp_2, hx19_2⟩
      have ⟨_, _, _, _, _, _, _⟩ := hacp_2
      let st2 := M.stepEvents evs2 st1
      dsimp only [threeVec80HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
      by_cases hc3 : (g.v3.cap == 0#64) = true <;>
        simp only [hc3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · refine sepWP_close_drop
          (fun sf => memRegion a 80 ∗
            A.pool lim (M.stepEvents (evs1 ++ evs2) st0) sf ∗
            stackAt s0.sp dropStack32) ?_
          (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
        · have heq_st : M.stepEvents (evs1 ++ evs2) st0 = st2 := by
            simp only [st1, st2, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
          rw [heq_st]
          wp_steps
          refine SepWP.weaken_pre (sepConj_mono
            (threeVec80HeadersAt_entails_memRegion_80 a g)
            (sepConj_mono_right (stack_restore_32_allocHook s0.sp _ _ _ _))) ?_
          wp_done
        · try rw [sepExists_sepConj_left]
          rw [satisfies_sepExists]; refine ⟨evs1 ++ evs2, ?_⟩
          repeat rw [sepConj_assoc]
          rw [satisfies_pure_sepConj]
          refine ⟨⟨htr_f, hacp_f, hevs1.append hevs2⟩, ?_⟩
          exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm
      · refine sepWP_close_drop
          (fun sf => memRegion a 80 ∗
            A.pool lim (M.stepEvents (evs1 ++ evs2 ++ rustDeallocEvents g.v3.cap.toNat 1) st0) sf ∗
            stackAt s0.sp dropStack32) ?_
          (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
        · have heq_st : M.stepEvents (evs1 ++ evs2 ++ rustDeallocEvents g.v3.cap.toNat 1) st0 =
              M.stepEvents (rustDeallocEvents g.v3.cap.toNat 1) st2 := by
            simp only [st1, st2, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
          rw [heq_st]
          have htail : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 .lr) s2
              ((threeVec80HeadersAt a g ∗
                (A.live g.v3.ptr g.v3.cap.toNat 1 ∗ memRegion g.v3.ptr g.v3.cap.toNat)) ∗
                A.pool lim st2 s2 ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
                (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
                 ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
              (fun sf Pf =>
                (Pf ⊢ memRegion a 80 ∗
                  A.pool lim (M.stepEvents (rustDeallocEvents g.v3.cap.toNat 1) st2) sf ∗
                  stackAt s0.sp dropStack32) ∧
                sf.sp = s0.sp ∧ sf.trace = s0.trace ∧
                AllocCallPreserved s2 sf ∧ CalleeSavedPreserved s0 sf) := by
            dsimp only [threeVec80HeadersAt]
            wp_steps
            refine SepWP.weaken_pre (sepConj_mono
              (sepConj_mono_left (threeVec80HeadersAt_entails_memRegion_80 a g))
              (sepConj_mono_right (cells4_entails_stack32_bottom s0.sp _ _ _ _))) ?_
            wp_call hdealloc_fo (g.v3.ptr, g.v3.cap.toNat, 1, st2)
            have hpost2 : AllocCallPreserved s2 sf := by assumption
            rcases hpost2 with ⟨_, _, _, _, _, _, _⟩
            refine SepWP.weaken_pre
              (tail_dealloc_unchunked_post a 80
                (A.pool lim (M.stepEvents (rustDeallocEvents g.v3.cap.toNat 1) st2) sf) s0.sp) ?_
            wp_done
          exact SepWP.mono htail fun _ _ _ _ ⟨hp, hsp_f, htr_f, hacp_2f, hcs_f⟩ =>
            ⟨hp, hsp_f, htr_f, hacp_2.trans hacp_2f, hcs_f⟩
        · try rw [sepExists_sepConj_left]
          rw [satisfies_sepExists]
          refine ⟨evs1 ++ evs2 ++ rustDeallocEvents g.v3.cap.toNat 1, ?_⟩
          repeat rw [sepConj_assoc]
          rw [satisfies_pure_sepConj]
          refine ⟨⟨htr_f, hacp_f, (hevs1.append hevs2).append
            (LibsignalBinary.Heap.FreeOnlyEvs.singleton 1 g.v3.cap.toNat)⟩, ?_⟩
          exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsdBudgetAux
