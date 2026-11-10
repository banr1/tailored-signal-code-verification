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
public import LibsignalBinary.Proofs.SpqrV1.Drop.Poly
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr

/-!
# Budget-Threaded Drop Glue for `[spqr::encoding::polynomial::Poly; 16]` (Block `265`)

Defines `dropGluePoly16Spec` under `RustCliAllocBudget M` (`FreeOnlyEvs`), `Vec<GF16>` list
deallocation combinators, and the relocatable `[LibsignalPlacement]` proof for Block `265`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

open CryptoVerification (LibsignalPlacement blkPC_265 blkPl_265 lsρ)
open CryptoVerification.LibsignalSpqrV1 (GF16 NUM_POLYS)
open CryptoVerification.RustHeap (RustAlloc allocHookStack arrayAt)
open CryptoVerification.SpqrV1.Drop (
  DropGluePoly16Ghost Saved32Preserved cap0_poly16_post dropGluePoly16Stack
  list_length_16_elim slot0_entails_memRegion_24 slot_join_memRegion_at
  stackAt_dropGluePoly16_split tail_dealloc_poly16_post tail_dealloc_poly16_pre_weaken
  vecGF16Dealloc vecGF16ListOf vecGF16Of vecGF16Of_frame_entails vecGF16Of_step_entails
)
open CryptoVerification.SpqrV1.Poly (polyArrayBytes)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
  RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents
)

namespace LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget

open Arm64 ProofLib
open ProofLib.ProgramReflection
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Budget-Threaded Specifications -/

def dropGluePoly16SpecBase (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DropGluePoly16Ghost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.arrA ∧ x.vecs.length = NUM_POLYS⌝ ∗
      vecGF16ListOf A.repAlloc x.arrA x.vecs ∗
      A.pool lim st s ∗ stackAt s.sp dropGluePoly16Stack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ FreeOnlyEvs evs⌝ ∗
      memRegion x.arrA polyArrayBytes ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp dropGluePoly16Stack

def dropGluePoly16Spec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DropGluePoly16Ghost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.arrA ∧ x.vecs.length = NUM_POLYS ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      vecGF16ListOf A.repAlloc x.arrA x.vecs ∗
      A.pool lim st s ∗ stackAt s.sp dropGluePoly16Stack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ FreeOnlyEvs evs⌝ ∗
      memRegion x.arrA polyArrayBytes ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp dropGluePoly16Stack

/-! ## Budget-Threaded `Vec<GF16>` List Step Combinators -/

/-- Budget-threaded element-0 deallocation step for `vecGF16ListOf` (used by `[Poly; 16]` and `PolyEncoder` callers). -/
theorem SepWP.dealloc_list_cons0_step {A : RustAlloc} {prog : Program} {target_pc : BitVec 64} {s : State}
    (arrA : BitVec 64) (cs : List GF16) (rest : List (List GF16))
    (TailPre : SepProp) (TailPost : List AllocEvent → State → SepProp) {Q : State → Prop}
    (h : ∀ cap ptr : BitVec 64,
      SepWP prog target_pc s
        (((arrA ↦₆₄ cap) ∗ ((arrA + 8#64) ↦₆₄ ptr) ∗ memRegion (arrA + 16#64) 8 ∗
          vecGF16Dealloc A cap ptr) ∗ (vecGF16ListOf A (arrA + 24#64) rest ∗ TailPre))
        (fun sm Pm =>
          ∃ evs, FreeOnlyEvs evs ∧
          (Pm ⊢ ((arrA ↦₆₄ cap) ∗ ((arrA + 8#64) ↦₆₄ ptr) ∗ memRegion (arrA + 16#64) 8) ∗
            (vecGF16ListOf A (arrA + 24#64) rest ∗ TailPost evs sm)) ∧
          Q sm)) :
    SepWP prog target_pc s
      (vecGF16ListOf A arrA (cs :: rest) ∗ TailPre)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ vecGF16ListOf A (arrA + 24#64) rest ∗ (memRegion arrA 24 ∗ TailPost evs sm)) ∧
        Q sm) := by
  have hpre : vecGF16ListOf A arrA (cs :: rest) ∗ TailPre =
      vecGF16Of A arrA cs ∗ (vecGF16ListOf A (arrA + 24#64) rest ∗ TailPre) := by
    show (vecGF16Of A arrA cs ∗ vecGF16ListOf A (arrA + 24#64) rest) ∗ TailPre = _
    sep_ac_rfl
  rw [hpre]
  refine SepWP.weaken_pre (vecGF16Of_frame_entails A arrA cs _) ?_
  apply SepWP.exists_left; intro cap
  apply SepWP.exists_left; intro ptr
  refine SepWP.mono (h cap ptr) fun sm _Pm _ _ ⟨evs, hevs, hp, hq⟩ =>
    ⟨evs, hevs, Entails.trans hp ?_, hq⟩
  refine Entails.trans (slot0_entails_memRegion_24 arrA cap ptr _) ?_
  exact Entails.of_eq (by sep_ac_rfl)

/-- Budget-threaded element-`k` (`k ≥ 1`) deallocation step for `vecGF16ListOf` (used by `[Poly; 16]` and `PolyEncoder` callers). -/
theorem SepWP.dealloc_list_cons_step {A : RustAlloc} {prog : Program} {target_pc : BitVec 64} {s : State}
    (arrA off off8 off16 offNext : BitVec 64) (n m : Nat)
    (hoff : arrA + BitVec.ofNat 64 n = arrA + off)
    (hoff8 : (arrA + off) + 8#64 = arrA + off8)
    (hoff16 : (arrA + off) + 16#64 = arrA + off16)
    (hoffNext : (arrA + off) + 24#64 = arrA + offNext)
    (hm : n + 24 = m) (hbound : m ≤ 2 ^ 64)
    (cs : List GF16) (rest : List (List GF16))
    (TailPre : SepProp) (TailPost : List AllocEvent → State → SepProp) {Q : State → Prop}
    (h : ∀ cap ptr : BitVec 64,
      SepWP prog target_pc s
        ((((arrA + off) ↦₆₄ cap) ∗ ((arrA + off8) ↦₆₄ ptr) ∗ memRegion (arrA + off16) 8 ∗
          vecGF16Dealloc A cap ptr) ∗
          (memRegion arrA n ∗ (vecGF16ListOf A (arrA + offNext) rest ∗ TailPre)))
        (fun sm Pm =>
          ∃ evs, FreeOnlyEvs evs ∧
          (Pm ⊢ (((arrA + off) ↦₆₄ cap) ∗ ((arrA + off8) ↦₆₄ ptr) ∗
            memRegion (arrA + off16) 8) ∗
            memRegion arrA n ∗ (vecGF16ListOf A (arrA + offNext) rest ∗ TailPost evs sm)) ∧
          Q sm)) :
    SepWP prog target_pc s
      (vecGF16ListOf A (arrA + off) (cs :: rest) ∗ (memRegion arrA n ∗ TailPre))
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ vecGF16ListOf A (arrA + offNext) rest ∗ (memRegion arrA m ∗ TailPost evs sm)) ∧
        Q sm) := by
  have hpre : vecGF16ListOf A (arrA + off) (cs :: rest) ∗ (memRegion arrA n ∗ TailPre) =
      vecGF16Of A (arrA + off) cs ∗ (memRegion arrA n ∗ (vecGF16ListOf A (arrA + offNext) rest ∗ TailPre)) := by
    show (vecGF16Of A (arrA + off) cs ∗ vecGF16ListOf A ((arrA + off) + 24#64) rest) ∗ (memRegion arrA n ∗ TailPre) = _
    rw [hoffNext]
    sep_ac_rfl
  rw [hpre]
  refine SepWP.weaken_pre (vecGF16Of_step_entails A arrA off off8 off16 hoff8 hoff16 cs _) ?_
  apply SepWP.exists_left; intro cap
  apply SepWP.exists_left; intro ptr
  refine SepWP.mono (h cap ptr) fun sm _Pm _ _ ⟨evs, hevs, hp, hq⟩ =>
    ⟨evs, hevs, Entails.trans hp ?_, hq⟩
  refine Entails.trans (slot_join_memRegion_at arrA off off8 off16 cap ptr n m hoff hoff8 hoff16 hm hbound _) ?_
  exact Entails.of_eq (by sep_ac_rfl)

/-! ## Sequencing Helpers -/

private def deallocFreeOnlySpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × Nat × Nat × M.σ) where
  pre := (rustCliDeallocBudgetSpec M A lim).pre
  post := fun (_, size, align, st) s0 sf =>
    ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf⌝ ∗
      A.pool lim (M.stepEvents (rustDeallocEvents size align) st) sf ∗ stackAt s0.sp allocHookStack

private theorem subroutine_ok_deallocFreeOnly [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
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

private theorem sepWP_evs_nil {prog : Program} {target : BitVec 64}
    {s : State} {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    (h : SepWP prog target s P (fun sm Pm => (Pm ⊢ P_evs [] sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm) :=
  SepWP.mono h fun _ _ _ _ ⟨hp, hq⟩ => ⟨[], LibsignalBinary.Heap.FreeOnlyEvs.nil, hp, hq⟩

private theorem sepWP_evs_dealloc {prog : Program} {target : BitVec 64}
    {s : State} (sz al : Nat)
    {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    (h : SepWP prog target s P (fun sm Pm =>
      (Pm ⊢ P_evs (rustDeallocEvents sz al) sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm) :=
  SepWP.mono h fun _ _ _ _ ⟨hp, hq⟩ =>
    ⟨rustDeallocEvents sz al, LibsignalBinary.Heap.FreeOnlyEvs.singleton al sz, hp, hq⟩

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

/-! ## Relocatable `[LibsignalPlacement]` Proof (Block `265`) -/

private theorem drop_glue_poly16_placed_first8 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_265).rebase (blkPl_265).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (fsp arrA : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (c0 c1 c2 c3 c4 c5 c6 c7 : List GF16) (rest : List (List GF16))
    (st : M.σ) (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_265).base + 12#64)
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
    SepWP ((blkPC_265).rebase (blkPl_265).base H)
      ((blkPl_265).base + 208#64)
      s
      (vecGF16ListOf A.repAlloc arrA (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest) ∗
        (A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame))
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ vecGF16ListOf A.repAlloc (arrA + 192#64) rest ∗
          (memRegion arrA 192 ∗ (A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame))) ∧
        Saved32Preserved s0 sm fsp arrA ∧ AllocCallPreserved s0 sm) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc
  clear hdealloc
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  have ⟨_, _, _, _, _, _, _⟩ := hacp
  refine seq_evs_step (mid := (blkPl_265).base + 40#64)
    (P_mid := fun st1 sm =>
      vecGF16ListOf A.repAlloc (arrA + 24#64) (c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest) ∗
        (memRegion arrA 24 ∗ (A.pool lim st1 sm ∗ stackAt fsp allocHookStack ∗ Frame)))
    (Q_mid := fun sm => Saved32Preserved s0 sm fsp arrA ∧ AllocCallPreserved s0 sm) ?_ ?_
  · refine SepWP.dealloc_list_cons0_step arrA c0 _ _
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
    refine seq_evs_step (mid := (blkPl_265).base + 64#64)
      (P_mid := fun st2 sm =>
        vecGF16ListOf A.repAlloc (arrA + 48#64) (c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest) ∗
          (memRegion arrA 48 ∗ (A.pool lim st2 sm ∗ stackAt fsp allocHookStack ∗ Frame)))
      (Q_mid := fun sm => Saved32Preserved s0 sm fsp arrA ∧ AllocCallPreserved s0 sm) ?_ ?_
    · refine SepWP.dealloc_list_cons_step arrA 24#64 32#64 40#64 48#64 24 48 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c1 _ _
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
      refine seq_evs_step (mid := (blkPl_265).base + 88#64)
        (P_mid := fun st3 sm =>
          vecGF16ListOf A.repAlloc (arrA + 72#64) (c3 :: c4 :: c5 :: c6 :: c7 :: rest) ∗
            (memRegion arrA 72 ∗ (A.pool lim st3 sm ∗ stackAt fsp allocHookStack ∗ Frame)))
        (Q_mid := fun sm => Saved32Preserved s0 sm fsp arrA ∧ AllocCallPreserved s0 sm) ?_ ?_
      · refine SepWP.dealloc_list_cons_step arrA 48#64 56#64 64#64 72#64 48 72 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c2 _ _
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
        refine seq_evs_step (mid := (blkPl_265).base + 112#64)
          (P_mid := fun st4 sm =>
            vecGF16ListOf A.repAlloc (arrA + 96#64) (c4 :: c5 :: c6 :: c7 :: rest) ∗
              (memRegion arrA 96 ∗ (A.pool lim st4 sm ∗ stackAt fsp allocHookStack ∗ Frame)))
          (Q_mid := fun sm => Saved32Preserved s0 sm fsp arrA ∧ AllocCallPreserved s0 sm) ?_ ?_
        · refine SepWP.dealloc_list_cons_step arrA 72#64 80#64 88#64 96#64 72 96 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c3 _ _
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
        · intro st4 s4 hpc4 hrun4 ⟨⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4, hsp_4, htrace_4, hvregs_4⟩, hacp_4⟩
          have ⟨_, _, _, _, _, _, _⟩ := hacp_4
          refine seq_evs_step (mid := (blkPl_265).base + 136#64)
            (P_mid := fun st5 sm =>
              vecGF16ListOf A.repAlloc (arrA + 120#64) (c5 :: c6 :: c7 :: rest) ∗
                (memRegion arrA 120 ∗ (A.pool lim st5 sm ∗ stackAt fsp allocHookStack ∗ Frame)))
            (Q_mid := fun sm => Saved32Preserved s0 sm fsp arrA ∧ AllocCallPreserved s0 sm) ?_ ?_
          · refine SepWP.dealloc_list_cons_step arrA 96#64 104#64 112#64 120#64 96 120 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c4 _ _
              (fun evs sm => A.pool lim (M.stepEvents evs st4) sm ∗ stackAt fsp allocHookStack ∗ Frame) ?_
            intro cap ptr
            dsimp only [vecGF16Dealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live, Saved32Preserved]
            by_cases hcap : (cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp]
            · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]; wp_steps; wp_done
            · apply sepWP_evs_dealloc (cap <<< 1#64).toNat 2
              wp_steps; wp_apply; rw [hsp_4]
              have hacp' : AllocCallPreserved s0 sf := hacp_4.trans (by assumption)
              rcases hacp' with ⟨_, _, _, _, _, _, _⟩
              refine align_pre_st (by sep_ac_rfl) ?_; wp_done
          · intro st5 s5 hpc5 hrun5 ⟨⟨hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hx29_5, hsp_5, htrace_5, hvregs_5⟩, hacp_5⟩
            have ⟨_, _, _, _, _, _, _⟩ := hacp_5
            refine seq_evs_step (mid := (blkPl_265).base + 160#64)
              (P_mid := fun st6 sm =>
                vecGF16ListOf A.repAlloc (arrA + 144#64) (c6 :: c7 :: rest) ∗
                  (memRegion arrA 144 ∗ (A.pool lim st6 sm ∗ stackAt fsp allocHookStack ∗ Frame)))
              (Q_mid := fun sm => Saved32Preserved s0 sm fsp arrA ∧ AllocCallPreserved s0 sm) ?_ ?_
            · refine SepWP.dealloc_list_cons_step arrA 120#64 128#64 136#64 144#64 120 144 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c5 _ _
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
              refine seq_evs_step (mid := (blkPl_265).base + 184#64)
                (P_mid := fun st7 sm =>
                  vecGF16ListOf A.repAlloc (arrA + 168#64) (c7 :: rest) ∗
                    (memRegion arrA 168 ∗ (A.pool lim st7 sm ∗ stackAt fsp allocHookStack ∗ Frame)))
                (Q_mid := fun sm => Saved32Preserved s0 sm fsp arrA ∧ AllocCallPreserved s0 sm) ?_ ?_
              · refine SepWP.dealloc_list_cons_step arrA 144#64 152#64 160#64 168#64 144 168 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c6 _ _
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
                refine SepWP.dealloc_list_cons_step arrA 168#64 176#64 184#64 192#64 168 192 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c7 _ _
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

private theorem drop_glue_poly16_placed_mid7 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_265).rebase (blkPl_265).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (fsp arrA : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (c8 c9 c10 c11 c12 c13 c14 : List GF16) (rest : List (List GF16))
    (st : M.σ) (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_265).base + 208#64)
    (hrun : s.status = .Running)
    (hpres : Saved32Preserved s0 s fsp arrA)
    (hacp : AllocCallPreserved s0 s) :
    SepWP ((blkPC_265).rebase (blkPl_265).base H)
      ((blkPl_265).base + 376#64)
      s
      (vecGF16ListOf A.repAlloc (arrA + 192#64) (c8 :: c9 :: c10 :: c11 :: c12 :: c13 :: c14 :: rest) ∗
        (memRegion arrA 192 ∗ (A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)))
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ vecGF16ListOf A.repAlloc (arrA + 360#64) rest ∗
          (memRegion arrA 360 ∗ (A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame))) ∧
        Saved32Preserved s0 sm fsp arrA ∧ AllocCallPreserved s0 sm) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc
  clear hdealloc
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  rcases hpres with ⟨hx19_8, hx20_8, hx21_8, hx22_8, hx23_8, hx24_8, hx25_8, hx26_8, hx27_8, hx28_8, hx29_8, hsp_8, htrace_8, hvregs_8⟩
  have ⟨_, _, _, _, _, _, _⟩ := hacp
  refine seq_evs_step (mid := (blkPl_265).base + 232#64)
    (P_mid := fun st9 sm =>
      vecGF16ListOf A.repAlloc (arrA + 216#64) (c9 :: c10 :: c11 :: c12 :: c13 :: c14 :: rest) ∗
        (memRegion arrA 216 ∗ (A.pool lim st9 sm ∗ stackAt fsp allocHookStack ∗ Frame)))
    (Q_mid := fun sm => Saved32Preserved s0 sm fsp arrA ∧ AllocCallPreserved s0 sm) ?_ ?_
  · refine SepWP.dealloc_list_cons_step arrA 192#64 200#64 208#64 216#64 192 216 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c8 _ _
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
    refine seq_evs_step (mid := (blkPl_265).base + 256#64)
      (P_mid := fun st10 sm =>
        vecGF16ListOf A.repAlloc (arrA + 240#64) (c10 :: c11 :: c12 :: c13 :: c14 :: rest) ∗
          (memRegion arrA 240 ∗ (A.pool lim st10 sm ∗ stackAt fsp allocHookStack ∗ Frame)))
      (Q_mid := fun sm => Saved32Preserved s0 sm fsp arrA ∧ AllocCallPreserved s0 sm) ?_ ?_
    · refine SepWP.dealloc_list_cons_step arrA 216#64 224#64 232#64 240#64 216 240 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c9 _ _
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
      refine seq_evs_step (mid := (blkPl_265).base + 280#64)
        (P_mid := fun st11 sm =>
          vecGF16ListOf A.repAlloc (arrA + 264#64) (c11 :: c12 :: c13 :: c14 :: rest) ∗
            (memRegion arrA 264 ∗ (A.pool lim st11 sm ∗ stackAt fsp allocHookStack ∗ Frame)))
        (Q_mid := fun sm => Saved32Preserved s0 sm fsp arrA ∧ AllocCallPreserved s0 sm) ?_ ?_
      · refine SepWP.dealloc_list_cons_step arrA 240#64 248#64 256#64 264#64 240 264 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c10 _ _
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
        refine seq_evs_step (mid := (blkPl_265).base + 304#64)
          (P_mid := fun st12 sm =>
            vecGF16ListOf A.repAlloc (arrA + 288#64) (c12 :: c13 :: c14 :: rest) ∗
              (memRegion arrA 288 ∗ (A.pool lim st12 sm ∗ stackAt fsp allocHookStack ∗ Frame)))
          (Q_mid := fun sm => Saved32Preserved s0 sm fsp arrA ∧ AllocCallPreserved s0 sm) ?_ ?_
        · refine SepWP.dealloc_list_cons_step arrA 264#64 272#64 280#64 288#64 264 288 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c11 _ _
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
        · intro st12 s12 hpc12 hrun12 ⟨⟨hx19_12, hx20_12, hx21_12, hx22_12, hx23_12, hx24_12, hx25_12, hx26_12, hx27_12, hx28_12, hx29_12, hsp_12, htrace_12, hvregs_12⟩, hacp_12⟩
          have ⟨_, _, _, _, _, _, _⟩ := hacp_12
          refine seq_evs_step (mid := (blkPl_265).base + 328#64)
            (P_mid := fun st13 sm =>
              vecGF16ListOf A.repAlloc (arrA + 312#64) (c13 :: c14 :: rest) ∗
                (memRegion arrA 312 ∗ (A.pool lim st13 sm ∗ stackAt fsp allocHookStack ∗ Frame)))
            (Q_mid := fun sm => Saved32Preserved s0 sm fsp arrA ∧ AllocCallPreserved s0 sm) ?_ ?_
          · refine SepWP.dealloc_list_cons_step arrA 288#64 296#64 304#64 312#64 288 312 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c12 _ _
              (fun evs sm => A.pool lim (M.stepEvents evs st12) sm ∗ stackAt fsp allocHookStack ∗ Frame) ?_
            intro cap ptr
            dsimp only [vecGF16Dealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live, Saved32Preserved]
            by_cases hcap : (cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp]
            · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]; wp_steps; wp_done
            · apply sepWP_evs_dealloc (cap <<< 1#64).toNat 2
              wp_steps; wp_apply; rw [hsp_12]
              have hacp' : AllocCallPreserved s0 sf := hacp_12.trans (by assumption)
              rcases hacp' with ⟨_, _, _, _, _, _, _⟩
              refine align_pre_st (by sep_ac_rfl) ?_; wp_done
          · intro st13 s13 hpc13 hrun13 ⟨⟨hx19_13, hx20_13, hx21_13, hx22_13, hx23_13, hx24_13, hx25_13, hx26_13, hx27_13, hx28_13, hx29_13, hsp_13, htrace_13, hvregs_13⟩, hacp_13⟩
            have ⟨_, _, _, _, _, _, _⟩ := hacp_13
            refine seq_evs_step (mid := (blkPl_265).base + 352#64)
              (P_mid := fun st14 sm =>
                vecGF16ListOf A.repAlloc (arrA + 336#64) (c14 :: rest) ∗
                  (memRegion arrA 336 ∗ (A.pool lim st14 sm ∗ stackAt fsp allocHookStack ∗ Frame)))
              (Q_mid := fun sm => Saved32Preserved s0 sm fsp arrA ∧ AllocCallPreserved s0 sm) ?_ ?_
            · refine SepWP.dealloc_list_cons_step arrA 312#64 320#64 328#64 336#64 312 336 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c13 _ _
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
              refine SepWP.dealloc_list_cons_step arrA 336#64 344#64 352#64 360#64 336 360 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c14 _ _
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

/-- Relocatable `core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>` (Block `265`)
satisfies `dropGluePoly16Spec M A lim` under `[LibsignalPlacement]`. -/
theorem drop_glue_poly16_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc_raw : subroutine_ok ((blkPC_265).rebase (blkPl_265).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_265).rebase (blkPl_265).base H)
      (blkPl_265).base
      (dropGluePoly16Spec M A lim) := by
  simp only [dropGluePoly16Spec]
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_raw
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  have hfirst8 := drop_glue_poly16_placed_first8 hdealloc_raw
  have hmid7 := drop_glue_poly16_placed_mid7 hdealloc_raw
  wp_init x_st s0
  rcases x_st with ⟨⟨arrA, vecs⟩, st⟩
  dsimp only [NUM_POLYS, DropGluePoly16Ghost.arrA, DropGluePoly16Ghost.vecs] at *
  subst ‹s0.readReg64 .x0 = arrA›
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, rfl⟩ :=
    list_length_16_elim (by assumption)
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropGluePoly16_split s0.sp]
  cells_unfold
  wp_pull_exists
  rename_i w0 w1 w2 w3
  refine seq_vm_clean (mid := (blkPl_265).base + 12#64)
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
  · wp_steps_vm
  · intro s1 hpc1 hrun1 hvm1 ⟨hacp1, hx0_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hsp_1, htrace_1, hvregs_1⟩
    rw [← A.pool_of_vmPreserved hvm1]
    refine seq_clean_evs (mid := (blkPl_265).base + 208#64)
      (P_evs := fun evs1 sm =>
        vecGF16ListOf A.repAlloc (s0.readReg64 .x0 + 192#64)
          [c8, c9, c10, c11, c12, c13, c14, c15] ∗
        (memRegion (s0.readReg64 .x0) 192 ∗
          (A.pool lim (M.stepEvents evs1 st) sm ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
            (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3)))))
      (Q := fun sm => Saved32Preserved s0 sm (s0.sp - 32#64) (s0.readReg64 .x0) ∧ AllocCallPreserved s0 sm)
      (hfirst8 s0 (s0.sp - 32#64) (s0.readReg64 .x0) hfsp_align
        c0 c1 c2 c3 c4 c5 c6 c7 [c8, c9, c10, c11, c12, c13, c14, c15] st s1 _
        hpc1 hrun1 hacp1 hx0_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hsp_1 htrace_1 hvregs_1)
      ?_
    intro evs1 s2 hevs1 hpc2 hrun2 ⟨hpres2, hacp2⟩
    refine seq_clean_evs (mid := (blkPl_265).base + 376#64)
      (P_evs := fun evs2 sm =>
        vecGF16ListOf A.repAlloc (s0.readReg64 .x0 + 360#64) [c15] ∗
        (memRegion (s0.readReg64 .x0) 360 ∗
          (A.pool lim (M.stepEvents evs2 (M.stepEvents evs1 st)) sm ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
            (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3)))))
      (Q := fun sm => Saved32Preserved s0 sm (s0.sp - 32#64) (s0.readReg64 .x0) ∧ AllocCallPreserved s0 sm)
      (hmid7 s0 (s0.sp - 32#64) (s0.readReg64 .x0) hfsp_align
        c8 c9 c10 c11 c12 c13 c14 [c15] (M.stepEvents evs1 st) s2 _ hpc2 hrun2 hpres2 hacp2)
      ?_
    intro evs2 s3 hevs2 hpc3 hrun3 ⟨⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3, hsp_3, htrace_3, hvregs_3⟩, hacp3⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp3
    let st3 := M.stepEvents evs2 (M.stepEvents evs1 st)
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
          A.pool lim (M.stepEvents (evs1 ++ evs2) st) sf ∗ stackAt s0.sp dropGluePoly16Stack) ?_
        (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
      · have heq_st : M.stepEvents (evs1 ++ evs2) st = st3 := by
          simp only [st3, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
        rw [heq_st]
        wp_steps
        refine SepWP.weaken_pre
          (Entails.trans (Entails.of_eq (by sep_ac_rfl))
            (cap0_poly16_post (s0.readReg64 .x0) cap ptr (A.pool lim st3 s3) s0.sp
              (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) w3)) ?_
        wp_done
      · rw [satisfies_sepExists]; refine ⟨evs1 ++ evs2, ?_⟩
        rw [satisfies_pure_sepConj]; refine ⟨⟨htr_f, hacp_f, hevs1.append hevs2⟩, ?_⟩
        exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm
    · refine sepWP_close_drop
        (fun sf => memRegion (s0.readReg64 .x0) polyArrayBytes ∗
          A.pool lim (M.stepEvents (evs1 ++ evs2 ++ rustDeallocEvents (cap <<< 1#64).toNat 2) st) sf ∗
          stackAt s0.sp dropGluePoly16Stack) ?_
        (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
      · have heq_st : M.stepEvents (evs1 ++ evs2 ++ rustDeallocEvents (cap <<< 1#64).toNat 2) st =
            M.stepEvents (rustDeallocEvents (cap <<< 1#64).toNat 2) st3 := by
          simp only [st3, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
        rw [heq_st]
        have htail : SepWP ((blkPC_265).rebase (blkPl_265).base H) (s0.readReg64 .lr) s3
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
      · rw [satisfies_sepExists]; refine ⟨evs1 ++ evs2 ++ rustDeallocEvents (cap <<< 1#64).toNat 2, ?_⟩
        rw [satisfies_pure_sepConj]
        refine ⟨⟨htr_f, hacp_f, (hevs1.append hevs2).append (LibsignalBinary.Heap.FreeOnlyEvs.singleton 2 (cap <<< 1#64).toNat)⟩, ?_⟩
        exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm

end LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget
