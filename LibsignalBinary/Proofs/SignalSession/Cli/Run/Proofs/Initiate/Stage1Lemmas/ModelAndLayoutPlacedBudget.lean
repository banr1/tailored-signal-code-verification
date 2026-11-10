/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.ModelAndLayoutPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCalleesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.Hoare.Safety

/-!
# Budget-Threaded Relocatable Stage 1 Call and Vtable Combinators

Provides `RustCliAllocBudget M` Stage 1 call combinators (`initCallPlaced`, `initCallLscro`) and
vtable `.rodata` slot introduction lemmas (`rodata_idVt_trustSlot_placed`,
`rodata_sessVt_loadSlot_placed`), while re-exporting allocator-free Stage 1 invariants and future
vtable lemmas from `ModelAndLayoutPlaced`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.ModelAndLayoutPlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoVerification (LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsInv LibsignalCodeRoLoaded NoFsEv withLsCodeRoLoaded)
open CryptoVerification.RustHeap (allocFailedIn)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli
  (cliIdentityVtSym cliSessionVtSym subroutine_ok_withFsInv withFsInv withFsInv_entry
   withFsInv_post_elim withFsInv_pre_intro)
open CryptoVerification.SignalSession.Cli.RunCompose (InitGhost RunSem)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate (initProgPlaced)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas
  (pure_sepConj_right_intro)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
  (InitPanicPostPlaced initSlotSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCalleesPlacedBudget
  (ExistingStoreCalleesEnvs InitStoreCalleesPlaced)
open Arm64.Obj (MultiPlacement)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

export CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas
  (pure_sepConj_right_intro sepWPp_step_lscro)
export CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas
  (rodata_idTrustFut_drop_placed' rodata_idTrustFut_size_placed'
   rodata_idTrustFut_align_placed' rodata_idTrustFut_poll_placed')
export CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas
  (rodata_sessLoadFut_drop_placed' rodata_sessLoadFut_size_placed'
   rodata_sessLoadFut_align_placed' rodata_sessLoadFut_poll_placed')

/-! ## Budget-threaded `withFsInv` call combinators -/

/-- Budget-threaded `withFsInv` call combinator on `initProgPlaced` over `DefsPlacedBudget.InitPanicPostPlaced`. -/
theorem initCallPlaced [LibsignalPlacement] {α : Type} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem} {x : InitGhost} {st0 : M.σ} {stk : Nat}
    {s0 s : State} {callee_pc ret_pc : BitVec 64}
    {spec : Spec α} {gx : α} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hcall : subroutine_ok (initProgPlaced mmpl gh W) callee_pc spec)
    (hpc : s.pc = callee_pc)
    (hrun : s.status = .Running)
    (hal : s.spAligned = true)
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hfs : s.fs.files = s0.fs.files)
    (hlr : s.readReg64 .lr = ret_pc)
    (hpre : P ⊢ spec.pre gx s ∗ F)
    (hpan : ∀ sf,
      spec.onPanic gx s sf ⊢
        ⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap := by
      intros; exact false_entails _)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = s.sp →
      CalleeSavedPreserved s sm →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      (sm.trace = s0.trace → sm.fs.files = s0.fs.files) →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm (spec.post gx s sm ∗ F) Q Qp oom)
    (hexit : ∀ code sf, spec.onExit gx code s sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ sf, spec.onOom gx s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp oom := by
  intro R hm hL
  have hfsInv0 : FsInv s0.fs.files s0.trace s := by
    rw [← hfs, ← htr]
    exact withFsInv_entry s
  have hcallFs :=
    subroutine_ok_withFsInv (hh.fs (prog := initProgPlaced mmpl gh W)) hcall s0.fs.files s0.trace
  have hmPre : s.mem ⊨ (withFsInv spec s0.fs.files s0.trace).pre gx s ∗ (F ∗ R) := by
    refine withFsInv_pre_intro hfsInv0 ?_
    rw [← sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left hpre) hm
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcallFs.no_fault_before_outcome gx (F ∗ R) s hpc hrun hmPre hal hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hpost⟩
  · obtain ⟨hfsInvm, hpost'⟩ := withFsInv_post_elim hpost
    rw [← sepConj_assoc] at hpost'
    rw [hlr] at hpcm
    have hinvm : LibsignalCodeRoLoaded lsmpl sm.mem :=
      hinv.of_keepsFrozen hsteps.keepsFrozen
    have hfsm : sm.trace = s0.trace → sm.fs.files = s0.fs.files := fun htm =>
      hfsInvm.files_eq (evs := []) (by simp [htm]) NoFsEv.nil
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm hinvm hfsm R hpost' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · change sm.mem ⊨ (⌜FsInv s0.fs.files s0.trace sm⌝ ∗ spec.onPanic gx s sm) ∗ (F ∗ R) at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨_, hpanMem⟩ := hpost
    have hm1 : sm.mem ⊨ (⌜allocFailedIn s sm ∧ s.trace <+: sm.trace⌝ ∗ anyHeap) ∗ (F ∗ R) :=
      Satisfies.mono (sepConj_mono_left (hpan sm)) hpanMem
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm1
    obtain ⟨⟨hA, _⟩, hmAny⟩ := hm1
    have hA0 : allocFailedIn s0 sm := by
      unfold allocFailedIn at hA ⊢
      rwa [htr] at hA
    have hmFinal : sm.mem ⊨ ((initSlotSpecPlaced A lim InitEnv S stk).onPanic (x, st0) s0 sm) ∗ R := by
      dsimp only [initSlotSpecPlaced, withLsCodeRoLoaded]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨Or.inr hA0,
        Satisfies.mono (by rw [← sepConj_assoc]; exact sepConj_mono_left (entails_anyHeap _)) hmAny⟩
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st,
      (initSlotSpecPlaced A lim InitEnv S stk).onPanic (x, st0) s0 sm, hmFinal,
      hpanic sm _ (Entails.refl _)⟩)⟩
  · change sm.mem ⊨ (⌜FsInv s0.fs.files s0.trace sm⌝ ∗ spec.onExit gx code s sm) ∗ (F ∗ R) at hpost
    rw [hexit, sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact (not_satisfies_false_sepConj hpost.2).elim
  · change sm.mem ⊨ (⌜FsInv s0.fs.files s0.trace sm⌝ ∗ spec.onOom gx s sm) ∗ (F ∗ R) at hpost
    rw [hoom, sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact (not_satisfies_false_sepConj hpost.2).elim

/-- Budget-threaded `withLsCodeRoLoaded lsmpl` call combinator on `initProgPlaced`. -/
theorem initCallLscro [LibsignalPlacement] {α : Type} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem} {x : InitGhost} {st0 : M.σ} {stk : Nat}
    {s0 s : State} {callee_pc ret_pc : BitVec 64}
    {inner : Spec α} {gx : α} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hcall : subroutine_ok (initProgPlaced mmpl gh W) callee_pc (withLsCodeRoLoaded lsmpl inner))
    (hpc : s.pc = callee_pc)
    (hrun : s.status = .Running)
    (hal : s.spAligned = true)
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hfs : s.fs.files = s0.fs.files)
    (hlr : s.readReg64 .lr = ret_pc)
    (hpre : P ⊢ inner.pre gx s ∗ F)
    (hpan : ∀ sf,
      inner.onPanic gx s sf ⊢
        ⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap := by
      intros; exact false_entails _)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = s.sp →
      CalleeSavedPreserved s sm →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      (sm.trace = s0.trace → sm.fs.files = s0.fs.files) →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm (inner.post gx s sm ∗ F) Q Qp oom)
    (hexit : ∀ code sf, inner.onExit gx code s sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ sf, inner.onOom gx s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp oom :=
  initCallPlaced hh hpanic hcall hpc hrun hal hinv htr hfs hlr
    (Entails.trans hpre (sepConj_mono_left (pure_sepConj_right_intro hinv (Entails.refl _))))
    hpan hnext hexit hoom

/-! ## Budget-threaded read-only vtable slot introduction lemmas -/

/-- Introduces the `cliIdentityVtSym + 48` (`is_trusted_identity` shim, block `601`) `.rodata` slot from `InitStoreCalleesPlaced`. -/
theorem rodata_idVt_trustSlot_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {eEnvs : ExistingStoreCalleesEnvs}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {B : RunBudgets} {stk : Nat} {s : State}
    (hStore : InitStoreCalleesPlaced A lim eEnvs mmpl gh W B stk)
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    ∀ R, (s.mem ⊨ R) →
      (s.mem ⊨ ((lsρ cliIdentityVtSym + 48#64) ↦₆₄ᵣ lsmpl.base 601) ∗ R) :=
  fun _ hR => hStore.rodata_idVt_trustSlot hinv.2 hR

/-- Introduces the `cliSessionVtSym + 24` (`load_session` shim, block `604`) `.rodata` slot from `InitStoreCalleesPlaced`. -/
theorem rodata_sessVt_loadSlot_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {eEnvs : ExistingStoreCalleesEnvs}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {B : RunBudgets} {stk : Nat} {s : State}
    (hStore : InitStoreCalleesPlaced A lim eEnvs mmpl gh W B stk)
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    ∀ R, (s.mem ⊨ R) →
      (s.mem ⊨ ((lsρ cliSessionVtSym + 24#64) ↦₆₄ᵣ lsmpl.base 604) ∗ R) :=
  fun _ hR => hStore.rodata_sessVt_loadSlot hinv.2 hR

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.ModelAndLayoutPlacedBudget
