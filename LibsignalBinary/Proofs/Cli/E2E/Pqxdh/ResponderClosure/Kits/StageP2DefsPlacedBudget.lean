/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobCutPlacedBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobErrOwnedPlacedBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerializeBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Stage P2 Shared Definitions and Callee Bundles

Defines placed budget-threaded call-framing combinators, `StageP2ClosureHooksPlaced`, SPQR V1
`InitializeBobV1Env` and `InitializeBobV1*Placed*` contracts, and `StageP2PureCalleesPlaced*` /
`StageP2BaseCalleesPlaced4K` bundles on Block `518`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (
  LibsignalPlacement lsHandleErrorSym lsLogFilterAddr lsMemcpySym lsRustAllocSym
  lsRustDeallocSym lsRustNoAllocShimSym ls_hook_ok_ultra_of_mem ls_subroutine_ok_of_block
  lsmpl lsρ subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded
)
open CryptoVerification.LibsignalTripleRatchet (
  framelessMemcpySpec withLsCodeRoLoaded
)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.LibsignalTripleRatchet.Getters (withLsRoLoaded)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open CryptoVerification.E2E.Pqxdh.Initiator (
  AcceptKeysInput Bytes DRKey Primitives WellSizedAcceptKeysInput
  bytesToBv8 encodeEC pqxdhEntryStack pqxdhEntryStackExt
)
open CryptoVerification.E2E.Pqxdh.Initiator.Model (acceptKeys)
open CryptoVerification.E2E.Pqxdh.ResponderCore (
  InitBobCallGhost bobParamsFieldsAt initBobErrAt initBobErrOwnedAt
)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (stageP2bStack)
open CryptoVerification.SpqrV1.Top.InitialState (initialStateValue)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  p2BobSession344Bv8V1 p2BobSpqrParams p2BobSpqrVecBuf
  p2_call_frame_cro_oom_prefix_placed p2_call_frame_oom_prefix_placed
  p2_panic_at_handle_error_placed p2_stackAt_split_of_le
  stageP1EntryPlaced stageP1ProgPlaced
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvent FitsEvents FitsStep
  RustCliAllocBudget SeqEnv coarseCostModel coarseStep coarseStepReserve
  rustCliAllocBudgetSpec rustCliAllocNoOomSpec rustCliDeallocBudgetSpec
  subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsBudget (
  isSameAccountDistinctSpec isSameAccountDistinctSpecExt p2BobSpqrVecBufBudget
  p2Memcpy4KSpec p2_framelessMemcpy_to_4K promoteStateEmpty4KSpec promoteStateEmptySpec
  promoteStateEmptySpec_to_4K
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptBudget (acceptSuccessEvents)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobPlacedBudget (
  InitBobSessionBuildEnv fitsEnv_initBobSessionBuildEnv_iff
  initBobSessionBuildEvents initializeBobSessionInnerPlacedSpec
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobCutPlacedBudget (
  AcceptSuccessEnv fitsEnv_acceptSuccessEnv_iff
  initializeBobSessionErrFrozenPlacedSpec initializeBobSessionErrInnerPlacedSpec
  initializeBobSessionErrPlacedSpec
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobErrOwnedPlacedBudget (
  initializeBobSessionErrOwnedFrozenPlacedSpec initializeBobSessionErrOwnedInnerPlacedSpec
  initializeBobSessionErrOwnedPlacedSpec
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesBudget (
  curveKeyPairSerdeBudgetSpec kemKeyPairFromPubPrivOkSpec preKeyRecordKeyPairBudgetSpec
)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (SpqrBoundedEvs)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  framelessMemcpyBudgetSpec noAllocShimBudgetSpec publicKeySerializeSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerializeBudget (
  public_key_serialize_placed_ok public_key_serialize_placed_ok_noOom
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec
)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (dropSpeSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionShimBudgetSpec)

export CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  p2_call_frame_oom_prefix_placed p2_call_frame_cro_oom_prefix_placed
  p2_panic_at_handle_error_placed stageP1ProgPlaced stageP1EntryPlaced
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

/-! ## 1. Placed Call-Framing Combinators -/

/-- Polymorphic-`Qp` placed call-framing combinator exposing `Steps prog s sf` in the normal-return
continuation. -/
theorem p2_call_frame_qp_placed {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hpanic : ∀ sf, sf.status = .Panicked →
      (∃ R', sf.mem ⊨ spec.onPanic x s sf ∗ R') → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      Steps prog s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by
      intro sf; first | rfl | simp only [Spec.inImage]) :
    SepWPp prog ret s P Q Qp := by
  have hmid :
      SepWPp prog ret_pc s P
        (fun sm P_m => sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧ P_m = spec.post x s sm ∗ F)
        Qp := by
    refine ProofLib.SepWPp.call_wpp (x := x) (F := F) hcall hpc hrun hsp hlr ?_
      (fun sf code _ _ hex => by
        rw [hexit_false code sf] at hex
        exact not_satisfies_false_sepConj hex)
      hpanic
      (fun sm hpcm hrunm hspm hcsm => ProofLib.SepWPp.done hpcm hrunm ⟨hspm, hcsm, rfl⟩)
      (fun sm _ _ hoom_post => by
        rw [hoom_false sm] at hoom_post
        exact (not_satisfies_false_sepConj hoom_post).elim)
    intro R hm
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  intro R hm hL
  obtain ⟨sm, hsteps, hout⟩ := hmid R hm hL
  rcases hout with ⟨hpcm, hrunm, _, hpost, hspm, hcsm, rfl⟩ | hpan | hoom_out
  · have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hsp_alm hcsm hsteps R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom_out)⟩

theorem p2_call_frame_cro_qp_placed [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hCode : LibsignalCodeRoLoaded lsmpl s.mem)
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hpanic : ∀ sf, sf.status = .Panicked →
      (∃ R', sf.mem ⊨ spec.onPanic x s sf ∗ R') → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      Steps prog s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by
      intro sf; first | rfl | simp only [Spec.inImage]) :
    SepWPp prog ret s P Q Qp :=
  p2_call_frame_qp_placed hcall hpc hrun hsp hlr hspec hφ hP hexit_false hpanic
    (fun sf hpcm hrunm hspm hsp_alm hcsm hsteps =>
      hnext sf hpcm hrunm hspm hsp_alm hcsm (hCode.of_keepsFrozen hsteps.keepsFrozen) hsteps)
    hoom_false

/-- Panic-free (`spec.onPanic = ⌜False⌝`, `spec.onOom = ⌜False⌝`) call-framing combinator for
budget-threaded Stage P2 callees. -/
theorem p2_call_frame_nopanic_placed {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      Steps prog s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by
      intro sf; first | rfl | simp only [Spec.inImage]) :
    SepWPp prog ret s P Q Qp :=
  p2_call_frame_qp_placed hcall hpc hrun hsp hlr hspec hφ hP hexit_false
    (fun sf _ ⟨_, hpan⟩ => by
      rw [hpan_false sf] at hpan
      exact (not_satisfies_false_sepConj hpan).elim)
    hnext hoom_false

theorem p2_call_frame_cro_nopanic_placed [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hCode : LibsignalCodeRoLoaded lsmpl s.mem)
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      Steps prog s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by
      intro sf; first | rfl | simp only [Spec.inImage]) :
    SepWPp prog ret s P Q Qp :=
  p2_call_frame_cro_qp_placed hCode hcall hpc hrun hsp hlr hspec hφ hP hexit_false
    (fun sf _ ⟨_, hpan⟩ => by
      rw [hpan_false sf] at hpan
      exact (not_satisfies_false_sepConj hpan).elim)
    hnext hoom_false

/-! ## 2. Placed Closure Extern Hooks & `StageP2ClosureHooksPlaced` -/

theorem p2_shim_at_closure_of_hookSat_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hShim : HookSat ext lsRustNoAllocShimSym noAllocShimBudgetSpec) :
    subroutine_ok (stageP1ProgPlaced ext) (lsρ lsRustNoAllocShimSym) noAllocShimBudgetSpec := by
  dsimp only [stageP1ProgPlaced]
  exact ls_hook_ok_ultra_of_mem hShim (by decide)

theorem p2_shim_at_closure_of_sessionShim_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hShim : HookSat ext lsRustNoAllocShimSym sessionShimBudgetSpec) :
    subroutine_ok (stageP1ProgPlaced ext) (lsρ lsRustNoAllocShimSym) noAllocShimBudgetSpec := by
  have h1 : subroutine_ok (stageP1ProgPlaced ext) (lsρ lsRustNoAllocShimSym)
      sessionShimBudgetSpec := by
    dsimp only [stageP1ProgPlaced]
    exact ls_hook_ok_ultra_of_mem hShim (by decide)
  refine subroutine_ok_mono h1 (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [sessionShimBudgetSpec, withVmPreserved,
    CryptoVerification.LibsignalTripleRatchet.sessionShimSpec, noAllocShimBudgetSpec] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj] at hq
  rw [satisfies_pure_sepConj]
  exact ⟨⟨hq.2.1, hq.1⟩, hq.2.2⟩

theorem p2_alloc_at_closure_of_hookSat_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hAlloc : HookSat ext lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok (stageP1ProgPlaced ext) (lsρ lsRustAllocSym)
      (rustCliAllocBudgetSpec M A lim false) := by
  dsimp only [stageP1ProgPlaced]
  exact ls_hook_ok_ultra_of_mem hAlloc (by decide)

theorem p2_allocNoOom_at_closure_of_hookSat_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hAlloc : HookSat ext lsRustAllocSym (rustCliAllocNoOomSpec M A lim false)) :
    subroutine_ok (stageP1ProgPlaced ext) (lsρ lsRustAllocSym)
      (rustCliAllocNoOomSpec M A lim false) := by
  dsimp only [stageP1ProgPlaced]
  exact ls_hook_ok_ultra_of_mem hAlloc (by decide)

theorem p2_dealloc_at_closure_of_hookSat_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hDealloc : HookSat ext lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (stageP1ProgPlaced ext) (lsρ lsRustDeallocSym)
      (rustCliDeallocBudgetSpec M A lim) := by
  dsimp only [stageP1ProgPlaced]
  exact ls_hook_ok_ultra_of_mem hDealloc (by decide)

theorem p2_memcpy_at_closure_4k_of_hookSat_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hMemcpy : HookSat ext lsMemcpySym p2Memcpy4KSpec) :
    subroutine_ok (stageP1ProgPlaced ext) (lsρ lsMemcpySym) p2Memcpy4KSpec := by
  dsimp only [stageP1ProgPlaced]
  exact ls_hook_ok_ultra_of_mem hMemcpy (by decide)

theorem p2_memcpy_at_closure_4k_of_frameless_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hMemcpy : HookSat ext lsMemcpySym (withVmPreserved framelessMemcpySpec)) :
    subroutine_ok (stageP1ProgPlaced ext) (lsρ lsMemcpySym) p2Memcpy4KSpec :=
  p2_framelessMemcpy_to_4K (by
    dsimp only [stageP1ProgPlaced]
    exact ls_hook_ok_ultra_of_mem hMemcpy (by decide))

theorem p2_memcpy_at_closure_4k_of_framelessBudget_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hMemcpy : HookSat ext lsMemcpySym framelessMemcpyBudgetSpec) :
    subroutine_ok (stageP1ProgPlaced ext) (lsρ lsMemcpySym) p2Memcpy4KSpec := by
  have h0 : subroutine_ok (stageP1ProgPlaced ext) (lsρ lsMemcpySym)
      framelessMemcpyBudgetSpec := by
    dsimp only [stageP1ProgPlaced]
    exact ls_hook_ok_ultra_of_mem hMemcpy (by decide)
  have h1 : subroutine_ok (stageP1ProgPlaced ext) (lsρ lsMemcpySym)
      (withVmPreserved framelessMemcpySpec) := by
    refine subroutine_ok_mono h0 (fun _ _ _ hp => hp) (fun ⟨dst, src, bs⟩ _ _ _ hq => ?_)
    dsimp only [framelessMemcpyBudgetSpec, withVmPreserved, framelessMemcpySpec] at hq ⊢
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨⟨hx0, htr, hvm⟩, hm⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hvm, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, htr⟩, hm⟩
  exact p2_framelessMemcpy_to_4K h1

/-- Budget-threaded closure-level extern callee bundle for Stage P2 basic blocks on
`stageP1ProgPlaced ext` (`shim` at `0` B, `alloc`/`dealloc`/`memcpy` at `allocHookStack = 4096` B;
no `handle_error` panic needed since budget-backed allocations never return null under `FitsEnv`). -/
structure StageP2ClosureHooksPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop where
  shim : subroutine_ok (stageP1ProgPlaced ext) (lsρ lsRustNoAllocShimSym) noAllocShimBudgetSpec
  alloc : subroutine_ok (stageP1ProgPlaced ext) (lsρ lsRustAllocSym)
    (rustCliAllocBudgetSpec M A lim false)
  dealloc : subroutine_ok (stageP1ProgPlaced ext) (lsρ lsRustDeallocSym)
    (rustCliDeallocBudgetSpec M A lim)
  memcpy4K : subroutine_ok (stageP1ProgPlaced ext) (lsρ lsMemcpySym) p2Memcpy4KSpec

theorem StageP2ClosureHooksPlaced.allocNoOom [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h : StageP2ClosureHooksPlaced A lim ext) :
    subroutine_ok (stageP1ProgPlaced ext) (lsρ lsRustAllocSym)
      (rustCliAllocNoOomSpec M A lim false) :=
  subroutine_ok_allocNoOom_of_budget h.alloc

theorem StageP2ClosureHooksPlaced.of_trapsOnly [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext1 ext2 : String → Option (State → State)}
    (hT : TrapsOnly (stageP1ProgPlaced ext1) (stageP1ProgPlaced ext2))
    (h : StageP2ClosureHooksPlaced A lim ext1) :
    StageP2ClosureHooksPlaced A lim ext2 :=
  ⟨subroutine_ok.of_trapsOnly hT h.shim,
   subroutine_ok.of_trapsOnly hT h.alloc,
   subroutine_ok.of_trapsOnly hT h.dealloc,
   subroutine_ok.of_trapsOnly hT h.memcpy4K⟩

theorem StageP2ClosureHooksPlaced.of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hShim : HookSat ext lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (hAlloc : HookSat ext lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hDealloc : HookSat ext lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : HookSat ext lsMemcpySym p2Memcpy4KSpec) :
    StageP2ClosureHooksPlaced A lim ext :=
  ⟨p2_shim_at_closure_of_hookSat_placed hShim,
   p2_alloc_at_closure_of_hookSat_placed hAlloc,
   p2_dealloc_at_closure_of_hookSat_placed hDealloc,
   p2_memcpy_at_closure_4k_of_hookSat_placed hMemcpy⟩

theorem StageP2ClosureHooksPlaced.of_sessionFramelessHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hShim : HookSat ext lsRustNoAllocShimSym sessionShimBudgetSpec)
    (hAlloc : HookSat ext lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hDealloc : HookSat ext lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : HookSat ext lsMemcpySym framelessMemcpyBudgetSpec) :
    StageP2ClosureHooksPlaced A lim ext :=
  ⟨p2_shim_at_closure_of_sessionShim_placed hShim,
   p2_alloc_at_closure_of_hookSat_placed hAlloc,
   p2_dealloc_at_closure_of_hookSat_placed hDealloc,
   p2_memcpy_at_closure_4k_of_framelessBudget_placed hMemcpy⟩

/-! ## 3. Placed SPQR V1 Bob Session Init Envelope & Contracts (`InitializeBobV1Ok*Placed`) -/

/-- Bounded SPQR `.v1` `spqr::initial_state` (`Block 327`) allocator event envelope at
`p2BobSpqrParams pqrKey`, matching `InitialStateEnv F` on `.v1` (`SpqrBoundedEvs 128 ...`). -/
def BobSpqrInitialStateEnv (_F : ShaCompress) (pqrKey : Bytes)
    (evs : List AllocEvent) : Prop :=
  SpqrBoundedEvs 128 (4 * (p2BobSpqrParams pqrKey).authKey.length + 4096) evs

/-- Default sequential allocator event envelope for the accepting SPQR V1 path of
`initialize_bob_session` (`Block 75`): `AcceptSuccessEnv inp`, followed by
`BobSpqrInitialStateEnv F drKey.pqrKey`, followed by `InitBobSessionBuildEnv`. -/
def InitializeBobV1Env (F : ShaCompress) (inp : AcceptKeysInput) (drKey : DRKey) :
    List AllocEvent → Prop :=
  SeqEnv (AcceptSuccessEnv inp)
    (SeqEnv (BobSpqrInitialStateEnv F drKey.pqrKey) InitBobSessionBuildEnv)

theorem initializeBobV1Env_of_parts {F : ShaCompress} {inp : AcceptKeysInput} {drKey : DRKey}
    {evs1 evs2 evs3 : List AllocEvent}
    (h1 : AcceptSuccessEnv inp evs1)
    (h2 : BobSpqrInitialStateEnv F drKey.pqrKey evs2)
    (h3 : InitBobSessionBuildEnv evs3) :
    InitializeBobV1Env F inp drKey (evs1 ++ evs2 ++ evs3) := by
  rw [List.append_assoc]
  exact SeqEnv.append h1 (SeqEnv.append h2 h3)

-- Concrete inhabitation witness for `InitializeBobV1Env F inp drKey`.
example (F : ShaCompress) (inp : AcceptKeysInput) (drKey : DRKey) :
    InitializeBobV1Env F inp drKey (acceptSuccessEvents inp ++ initBobSessionBuildEvents) := by
  simpa using initializeBobV1Env_of_parts (F := F) (inp := inp) (drKey := drKey)
    (evs1 := acceptSuccessEvents inp) (evs2 := []) (evs3 := initBobSessionBuildEvents)
    rfl (SpqrBoundedEvs.nil _ _) rfl

-- Concrete `FitsEnv` non-vacuity witness for the `AcceptSuccessEnv` & `InitBobSessionBuildEnv` stages under `coarseCostModel`.
example (inp : AcceptKeysInput) :
    FitsEnv coarseCostModel
      { staticCount := 64, staticBytes := 67108864, physCap := 536870912, enforced := true }
      coarseCostModel.init
      (AcceptSuccessEnv inp) ∧
    FitsEnv coarseCostModel
      { staticCount := 64, staticBytes := 67108864, physCap := 536870912, enforced := true }
      coarseCostModel.init
      InitBobSessionBuildEnv := by
  refine ⟨?_, ?_⟩
  · rw [fitsEnv_acceptSuccessEnv_iff]
    cases h : inp.opkBSk? with
    | none =>
      have hevs : acceptSuccessEvents inp =
          [.alloc 192, .alloc 32, .free 1 32, .alloc 32, .free 1 32,
           .alloc 32, .free 1 32, .free 1 192] := by
        simp [acceptSuccessEvents, h]; decide
      rw [hevs]
      dsimp only [FitsEvents, FitsEvent, AllocEvent.withinMaxAlloc, FitsStep,
        AllocCostModel.step, coarseCostModel, coarseStep, coarseStepReserve]
      decide
    | some _ =>
      have hevs : acceptSuccessEvents inp =
          [.alloc 192, .alloc 32, .free 1 32, .alloc 32, .free 1 32,
           .alloc 32, .free 1 32, .alloc 32, .free 1 32, .free 1 192] := by
        simp [acceptSuccessEvents, h]; decide
      rw [hevs]
      dsimp only [FitsEvents, FitsEvent, AllocEvent.withinMaxAlloc, FitsStep,
        AllocCostModel.step, coarseCostModel, coarseStep, coarseStepReserve]
      decide
  · have hevs : initBobSessionBuildEvents =
        [.alloc 33, .alloc 33, .alloc 32, .alloc 33,
         .alloc 32, .alloc 33, .alloc 33, .alloc 32, .alloc 32,
         .free 1 32, .free 1 33] := by decide
    rw [fitsEnv_initBobSessionBuildEnv_iff, hevs]
    dsimp only [FitsEvents, FitsEvent, AllocEvent.withinMaxAlloc, FitsStep,
      AllocCostModel.step, coarseCostModel, coarseStep, coarseStepReserve]
    decide

/-- Envelope- and stack-parameterized SPQR V1 `initialize_bob_session` success contract under
`[LibsignalPlacement]` on `stageP1ProgPlaced ext` (`lsProg_518 ext`), polymorphic in `{st : M.σ}`
and `{Qp : State → SepProp → Prop}` (panic- and OOM-free under `FitsEnv M lim st (BobV1Env inp drKey)`). -/
def InitializeBobV1OkAtPlacedOfEnv [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop)
    (ext : String → Option (State → State)) (bobV1Stk : Nat) : Prop :=
  ∀ {st : M.σ} {Qp : State → SepProp → Prop}
    (s0 : State) (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp),
    LibsignalCodeRoLoaded lsmpl s0.mem → s0.status = ExecStatus.Running →
    s0.pc = lsmpl.base 75 →
    s0.spAligned = true → s0.sp - 576#64 ≠ 0#64 →
    s0.readReg64 (.gpr 0#5) = argPtr → s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr →
    s0.readReg64 (.gpr 8#5) = outPtr →
    inp.trustedPeer = true → inp.replayOk = true →
    inp.hdr.opkId?.isSome = inp.opkBSk?.isSome →
    WellSizedAcceptKeysInput inp → ikBPk.length = 32 → spkBPk.length = 32 →
    acceptKeys P inp = some drKey →
    FitsEnv M lim st (BobV1Env inp drKey) →
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 (.gpr 30#5)) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk 0#8 ∗
       memRegion outPtr 344 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp bobV1Stk ∗ A.pool lim st s0 ∗ Frame)
      (fun sf P_f =>
        ∃ (evs : List AllocEvent),
          BobV1Env inp drKey evs ∧
          (∃ (localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
              ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr spqrCap spqrBufPtr : BitVec 64)
             (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64),
            localIkBoxPtr ≠ 0#64 ∧ remoteIkBoxPtr ≠ 0#64 ∧ rootKeyBoxPtr ≠ 0#64 ∧
            baseKeyBoxPtr ≠ 0#64 ∧ ratchetPubBoxPtr ≠ 0#64 ∧ ratchetPrivBoxPtr ≠ 0#64 ∧
            chainKeyBoxPtr ≠ 0#64 ∧ (P_f ⊢
              (outPtr ↦ₛ p2BobSession344Bv8V1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
                spqrCap spqrBufPtr
                (BitVec.ofNat 64 (initialStateValue F (p2BobSpqrParams drKey.pqrKey)).length)
                ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
                pad_f4 c0 c1 c2 c3 c4 d0 d1 d2) ∗
              p2BobSpqrVecBufBudget A spqrCap spqrBufPtr
                (initialStateValue F (p2BobSpqrParams drKey.pqrKey)) ∗
              bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
                inp ikBPk spkBPk 0#8 ∗
              (localIkBoxPtr ↦ₛ bytesToBv8 (encodeEC ikBPk)) ∗ A.live localIkBoxPtr 33 1 ∗
              (remoteIkBoxPtr ↦ₛ bytesToBv8 (encodeEC inp.hdr.ikAPk)) ∗
              A.live remoteIkBoxPtr 33 1 ∗
              (rootKeyBoxPtr ↦ₛ bytesToBv8 drKey.rootKey) ∗ A.live rootKeyBoxPtr 32 1 ∗
              (baseKeyBoxPtr ↦ₛ bytesToBv8 (encodeEC inp.hdr.ekAPk)) ∗
              A.live baseKeyBoxPtr 33 1 ∗
              (ratchetPubBoxPtr ↦ₛ bytesToBv8 (encodeEC spkBPk)) ∗
              A.live ratchetPubBoxPtr 33 1 ∗
              (ratchetPrivBoxPtr ↦ₛ bytesToBv8 inp.spkBSk) ∗ A.live ratchetPrivBoxPtr 32 1 ∗
              (chainKeyBoxPtr ↦ₛ bytesToBv8 drKey.chainKey) ∗ A.live chainKeyBoxPtr 32 1 ∗
              (lsLogFilterAddr ↦₆₄ 0#64) ∗
              stackAt s0.sp bobV1Stk ∗ A.pool lim (M.stepEvents evs st) sf ∗ Frame) ∧
            sf.status = ExecStatus.Running ∧ sf.pc = s0.readReg64 (.gpr 30#5) ∧ sf.sp = s0.sp ∧
            CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace))
      Qp

def InitializeBobV1OkPlacedOfEnv [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  InitializeBobV1OkAtPlacedOfEnv P A lim F BobV1Env ext (stageP2bStack + 0x700)

def InitializeBobV1OkPlaced4KOfEnv [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  InitializeBobV1OkAtPlacedOfEnv P A lim F BobV1Env ext (768 + pqxdhEntryStackExt)

abbrev InitializeBobV1OkAtPlaced [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) (bobV1Stk : Nat) : Prop :=
  InitializeBobV1OkAtPlacedOfEnv P A lim F (InitializeBobV1Env F) ext bobV1Stk

abbrev InitializeBobV1OkPlaced [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  InitializeBobV1OkPlacedOfEnv P A lim F (InitializeBobV1Env F) ext

abbrev InitializeBobV1OkPlaced4K [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  InitializeBobV1OkPlaced4KOfEnv P A lim F (InitializeBobV1Env F) ext

theorem InitializeBobV1OkAtPlacedOfEnv.mono_env [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {Env₁ Env₂ : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {ext : String → Option (State → State)} {bobV1Stk : Nat}
    (himp : ∀ inp drKey evs, Env₁ inp drKey evs → Env₂ inp drKey evs)
    (h : InitializeBobV1OkAtPlacedOfEnv P A lim F Env₁ ext bobV1Stk) :
    InitializeBobV1OkAtPlacedOfEnv P A lim F Env₂ ext bobV1Stk := by
  intro st Qp s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr
    drKey Frame hCode hrun hpc hsp hpqr hx0 hx1 hx8 htr hrep hopk hwell hik hspk hacc hfits
  have hfits₁ : FitsEnv M lim st (Env₁ inp drKey) :=
    fun evs hevs => hfits evs (himp inp drKey evs hevs)
  have hcall := h (st := st) (Qp := Qp) s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr
    ratchetKeyPairPtr outPtr drKey Frame
    hCode hrun hpc hsp hpqr hx0 hx1 hx8 htr hrep hopk hwell hik hspk hacc hfits₁
  intro R hm hL
  obtain ⟨sf, hst, ⟨hpc', hrun', Pf, hmf, evs, hevs, hrest⟩ | hpan⟩ := hcall R hm hL
  · exact ⟨sf, hst, Or.inl ⟨hpc', hrun', Pf, hmf, evs, himp inp drKey evs hevs, hrest⟩⟩
  · exact ⟨sf, hst, Or.inr hpan⟩

theorem InitializeBobV1OkAtPlacedOfEnv.of_trapsOnly [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {ext1 ext2 : String → Option (State → State)} {bobV1Stk : Nat}
    (hT : TrapsOnly (stageP1ProgPlaced ext1) (stageP1ProgPlaced ext2))
    (h : InitializeBobV1OkAtPlacedOfEnv P A lim F BobV1Env ext1 bobV1Stk) :
    InitializeBobV1OkAtPlacedOfEnv P A lim F BobV1Env ext2 bobV1Stk := by
  intro st Qp s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr
    drKey Frame hCode hrun hpc hsp hpqr hx0 hx1 hx8 htr hrep hopk hwell hik hspk hacc hfits
  exact SepWPp.of_trapsOnly hT
    (h s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame
      hCode hrun hpc hsp hpqr hx0 hx1 hx8 htr hrep hopk hwell hik hspk hacc hfits)

theorem InitializeBobV1OkPlacedOfEnv.of_trapsOnly [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {ext1 ext2 : String → Option (State → State)}
    (hT : TrapsOnly (stageP1ProgPlaced ext1) (stageP1ProgPlaced ext2))
    (h : InitializeBobV1OkPlacedOfEnv P A lim F BobV1Env ext1) :
    InitializeBobV1OkPlacedOfEnv P A lim F BobV1Env ext2 :=
  InitializeBobV1OkAtPlacedOfEnv.of_trapsOnly hT h

theorem InitializeBobV1OkPlaced4KOfEnv.of_trapsOnly [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {ext1 ext2 : String → Option (State → State)}
    (hT : TrapsOnly (stageP1ProgPlaced ext1) (stageP1ProgPlaced ext2))
    (h : InitializeBobV1OkPlaced4KOfEnv P A lim F BobV1Env ext1) :
    InitializeBobV1OkPlaced4KOfEnv P A lim F BobV1Env ext2 :=
  InitializeBobV1OkAtPlacedOfEnv.of_trapsOnly hT h

theorem InitializeBobV1OkPlacedOfEnv.to_4K [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (h : InitializeBobV1OkPlacedOfEnv P A lim F BobV1Env ext) :
    InitializeBobV1OkPlaced4KOfEnv P A lim F BobV1Env ext := by
  intro st Qp s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr
    drKey Frame hCode hrun hpc hsp hpqr hx0 hx1 hx8 htr hrep hopk hwell hik hspk hacc hfits
  let F_stk : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 (768 + pqxdhEntryStackExt))
      ((768 + pqxdhEntryStackExt) - (stageP2bStack + 0x700))
  have hsplit := p2_stackAt_split_of_le s0.sp (768 + pqxdhEntryStackExt)
    (stageP2bStack + 0x700) (by decide) (by decide)
  have hcall := h (st := st) (Qp := Qp) s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr
    ratchetKeyPairPtr outPtr drKey (F_stk ∗ Frame)
    hCode hrun hpc hsp hpqr hx0 hx1 hx8 htr hrep hopk hwell hik hspk hacc hfits
  intro R hm hL
  have hm' : s0.mem ⊨
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr inp ikBPk spkBPk 0#8 ∗
        memRegion outPtr 344 ∗ lsLogFilterAddr ↦₆₄ 0#64 ∗
        stackAt s0.sp (stageP2bStack + 0x700) ∗ A.pool lim st s0 ∗ (F_stk ∗ Frame)) ∗ R := by
    refine Satisfies.of_eq hm ?_; dsimp only [F_stk]; rw [hsplit]; ac_rfl
  obtain ⟨sf, hst, ⟨hpc', hrun', Pf, hmf, evs, hevs, localIkBoxPtr, remoteIkBoxPtr, rootKeyBoxPtr,
    baseKeyBoxPtr, ratchetPubBoxPtr, ratchetPrivBoxPtr, chainKeyBoxPtr, spqrCap, spqrBufPtr,
    pad_f4, c0, c1, c2, c3, c4, d0, d1, d2, hn1, hn2, hn3, hn4, hn5, hn6, hn7,
    hPf, hst'⟩ | hpan⟩ := hcall R hm' hL
  · refine ⟨sf, hst, Or.inl ⟨hpc', hrun', Pf, hmf, evs, hevs, localIkBoxPtr,
      remoteIkBoxPtr, rootKeyBoxPtr, baseKeyBoxPtr, ratchetPubBoxPtr, ratchetPrivBoxPtr,
      chainKeyBoxPtr, spqrCap, spqrBufPtr, pad_f4, c0, c1, c2, c3, c4, d0, d1, d2,
      hn1, hn2, hn3, hn4, hn5, hn6, hn7,
      Entails.trans hPf (Entails.of_eq ?_), hst'⟩⟩
    dsimp only [F_stk]; rw [hsplit]; ac_rfl
  · exact ⟨sf, hst, Or.inr hpan⟩

theorem InitializeBobV1OkPlaced.to_4K [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (h : InitializeBobV1OkPlaced P A lim F ext) :
    InitializeBobV1OkPlaced4K P A lim F ext :=
  InitializeBobV1OkPlacedOfEnv.to_4K h

/-! ## 4. 4K/`Ext` Rejecting `initialize_bob_session` Contracts & `_to_4K` Bridges -/

/-- 4K/`Ext` variant of `initializeBobSessionErrInnerPlacedSpec` at `768 + pqxdhEntryStackExt`
(`onPanic = ⌜False⌝`, `onOom = ⌜False⌝` under `FitsEnv M lim st (AcceptErrEnv g.inp)`). -/
def initializeBobSessionErr4KInnerPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop) :
    Spec (InitBobCallGhost × M.σ) where
  pre := fun (g, st) s =>
    ⌜s.readReg64 .x0 = g.argPtr ∧
      s.readReg64 .x1 = g.ratchetKeyPairPtr ∧
      s.readReg64 .x8 = g.outPtr ∧
      g.inp.trustedPeer = true ∧
      g.inp.replayOk = true ∧
      g.inp.hdr.opkId?.isSome = g.inp.opkBSk?.isSome ∧
      WellSizedAcceptKeysInput g.inp ∧
      g.ikBPk.length = 32 ∧
      g.spkBPk.length = 32 ∧
      acceptKeys P g.inp = none ∧
      FitsEnv M lim st (AcceptErrEnv g.inp)⌝ ∗
    bobParamsFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.ratchetKeyPairPtr
      g.inp g.ikBPk g.spkBPk g.sameAccountByte ∗
    memRegion g.outPtr 344 ∗
    (lsLogFilterAddr ↦₆₄ 0#64) ∗
    stackAt s.sp (768 + pqxdhEntryStackExt) ∗
    A.pool lim st s
  post := fun (g, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AcceptErrEnv g.inp evs⌝ ∗
      bobParamsFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.ratchetKeyPairPtr
        g.inp g.ikBPk g.spkBPk g.sameAccountByte ∗
      (initBobErrAt g.outPtr ∗ anyHeap) ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      stackAt s0.sp (768 + pqxdhEntryStackExt) ∗
      A.pool lim (M.stepEvents evs st) sf

def initializeBobSessionErr4KPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop) :
    Spec (InitBobCallGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl (initializeBobSessionErr4KInnerPlacedSpec P A lim AcceptErrEnv)

abbrev initializeBobSessionErrExtPlacedSpec [LibsignalPlacement] :=
  @initializeBobSessionErr4KPlacedSpec

theorem initializeBobSessionErrPlacedSpec_to_4K [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64} {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (h : subroutine_ok prog entry (initializeBobSessionErrPlacedSpec P A lim AcceptErrEnv)) :
    subroutine_ok prog entry (initializeBobSessionErr4KPlacedSpec P A lim AcceptErrEnv) := by
  refine subroutine_ok_map h ?_
  rintro ⟨g, st⟩ R s0 hpre
  let F_stk : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 (768 + pqxdhEntryStackExt))
      ((768 + pqxdhEntryStackExt) - (768 + pqxdhEntryStack))
  dsimp only [initializeBobSessionErr4KPlacedSpec, withLsCodeRoLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hro, hpre⟩
  dsimp only [initializeBobSessionErr4KInnerPlacedSpec] at hpre
  rw [p2_stackAt_split_of_le s0.sp (768 + pqxdhEntryStackExt)
    (768 + pqxdhEntryStack) (by decide) (by decide)] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hmem⟩
  have hnone : acceptKeys P g.inp = none := hpure.2.2.2.2.2.2.2.2.2.1
  refine ⟨(g, st), F_stk ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [initializeBobSessionErrPlacedSpec, withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hro, ?_⟩
    dsimp only [initializeBobSessionErrInnerPlacedSpec, F_stk]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, Satisfies.of_eq hmem (by ac_rfl)⟩
  · dsimp only [initializeBobSessionErrPlacedSpec, initializeBobSessionErrInnerPlacedSpec,
      initializeBobSessionInnerPlacedSpec, initializeBobSessionErr4KPlacedSpec,
      initializeBobSessionErr4KInnerPlacedSpec, withLsCodeRoLoaded, F_stk] at hpost ⊢
    rw [sepExists_sepConj_left] at hpost ⊢
    refine Satisfies.of_eq hpost ?_
    congr 1; funext evs
    rw [hnone]
    dsimp only
    rw [p2_stackAt_split_of_le s0.sp (768 + pqxdhEntryStackExt)
      (768 + pqxdhEntryStack) (by decide) (by decide)]
    ac_rfl

/-- 4K/`Ext` variant of `initializeBobSessionErrOwnedInnerPlacedSpec` at `768 + pqxdhEntryStackExt`. -/
def initializeBobSessionErrOwned4KInnerPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop) :
    Spec (InitBobCallGhost × M.σ) where
  pre := fun (g, st) s =>
    ⌜s.readReg64 .x0 = g.argPtr ∧
      s.readReg64 .x1 = g.ratchetKeyPairPtr ∧
      s.readReg64 .x8 = g.outPtr ∧
      g.inp.trustedPeer = true ∧
      g.inp.replayOk = true ∧
      g.inp.hdr.opkId?.isSome = g.inp.opkBSk?.isSome ∧
      WellSizedAcceptKeysInput g.inp ∧
      g.ikBPk.length = 32 ∧
      g.spkBPk.length = 32 ∧
      acceptKeys P g.inp = none ∧
      FitsEnv M lim st (AcceptErrEnv g.inp)⌝ ∗
    bobParamsFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.ratchetKeyPairPtr
      g.inp g.ikBPk g.spkBPk g.sameAccountByte ∗
    memRegion g.outPtr 344 ∗
    (lsLogFilterAddr ↦₆₄ 0#64) ∗
    stackAt s.sp (768 + pqxdhEntryStackExt) ∗
    A.pool lim st s
  post := fun (g, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AcceptErrEnv g.inp evs⌝ ∗
      bobParamsFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.ratchetKeyPairPtr
        g.inp g.ikBPk g.spkBPk g.sameAccountByte ∗
      (initBobErrOwnedAt A.repAlloc g.outPtr ∗ anyHeap) ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      stackAt s0.sp (768 + pqxdhEntryStackExt) ∗
      A.pool lim (M.stepEvents evs st) sf

def initializeBobSessionErrOwned4KPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop) :
    Spec (InitBobCallGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl (initializeBobSessionErrOwned4KInnerPlacedSpec P A lim AcceptErrEnv)

abbrev initializeBobSessionErrOwnedExtPlacedSpec [LibsignalPlacement] :=
  @initializeBobSessionErrOwned4KPlacedSpec

theorem initializeBobSessionErrOwnedPlacedSpec_to_4K [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64} {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (h : subroutine_ok prog entry (initializeBobSessionErrOwnedPlacedSpec P A lim AcceptErrEnv)) :
    subroutine_ok prog entry (initializeBobSessionErrOwned4KPlacedSpec P A lim AcceptErrEnv) := by
  refine subroutine_ok_map h ?_
  rintro ⟨g, st⟩ R s0 hpre
  let F_stk : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 (768 + pqxdhEntryStackExt))
      ((768 + pqxdhEntryStackExt) - (768 + pqxdhEntryStack))
  dsimp only [initializeBobSessionErrOwned4KPlacedSpec, withLsCodeRoLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hro, hpre⟩
  dsimp only [initializeBobSessionErrOwned4KInnerPlacedSpec] at hpre
  rw [p2_stackAt_split_of_le s0.sp (768 + pqxdhEntryStackExt)
    (768 + pqxdhEntryStack) (by decide) (by decide)] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hmem⟩
  refine ⟨(g, st), F_stk ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [initializeBobSessionErrOwnedPlacedSpec, withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hro, ?_⟩
    dsimp only [initializeBobSessionErrOwnedInnerPlacedSpec, F_stk]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, Satisfies.of_eq hmem (by ac_rfl)⟩
  · dsimp only [initializeBobSessionErrOwnedPlacedSpec,
      initializeBobSessionErrOwnedInnerPlacedSpec,
      initializeBobSessionErrOwned4KPlacedSpec,
      initializeBobSessionErrOwned4KInnerPlacedSpec, withLsCodeRoLoaded, F_stk] at hpost ⊢
    rw [sepExists_sepConj_left] at hpost ⊢
    refine Satisfies.of_eq hpost ?_
    congr 1; funext evs
    rw [p2_stackAt_split_of_le s0.sp (768 + pqxdhEntryStackExt)
      (768 + pqxdhEntryStack) (by decide) (by decide)]
    ac_rfl

/-! ## 5. Placed `<PublicKey>::serialize`, Pure `0`-Alloc Wrappers, & `StageP2PureCalleesPlaced` -/

/-- `VmPreserved`-augmented `SessionRecord::promote_matching_session` (empty-record fast path,
`0` allocations). -/
def promoteMatchingSessionEmptySpec : Spec (BitVec 64 × BitVec 64) :=
  withVmPreserved CryptoVerification.E2E.Pqxdh.ResponderStore.promoteMatchingSessionEmptySpec

/-- `VmPreserved`-augmented `drop_glue<process_prekey_impl::{closure#0}>` state-1 fast path
(`0` allocations). -/
def dropProcessPrekeyImplState1Spec : Spec (BitVec 64) :=
  withVmPreserved CryptoVerification.E2E.Pqxdh.ResponderStore.dropProcessPrekeyImplState1Spec

/-- `<PublicKey>::serialize` (`lsmpl.base 205`) meets `publicKeySerializeSpec M A lim` on
`stageP1ProgPlaced ext` under `HookSat` for `noAllocShimBudgetSpec` and `rustCliAllocBudgetSpec`. -/
theorem p2_publicKeySerialize_of_hooks_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hShim : HookSat ext lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (hAlloc : HookSat ext lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpec M A lim)) :=
  ls_subroutine_ok_of_block (i := 518) (j := 205)
    (subroutine_ok_withLsCodeLoaded_of_plain
      (public_key_serialize_placed_ok hShim hAlloc))
    (by decide)

/-- Variant of `p2_publicKeySerialize_of_hooks_placed` accepting `rustCliAllocNoOomSpec`. -/
theorem p2_publicKeySerialize_of_hooks_placed_noOom [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hShim : HookSat ext lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (hAlloc : HookSat ext lsRustAllocSym (rustCliAllocNoOomSpec M A lim false)) :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpec M A lim)) :=
  ls_subroutine_ok_of_block (i := 518) (j := 205)
    (subroutine_ok_withLsCodeLoaded_of_plain
      (public_key_serialize_placed_ok_noOom hShim hAlloc))
    (by decide)

/-- Envelope-parametric placed bundle of internal libsignal subroutine contracts invoked along
Stage P2 on `stageP1ProgPlaced ext` (`lsProg_518 ext`). -/
structure StageP2PureCalleesPlacedOfEnv [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop where
  publicKeySerialize :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpec M A lim))
  promoteMatchingSessionEmpty :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 50)
      (withLsCodeLoaded lsmpl promoteMatchingSessionEmptySpec)
  curveKeyPairSerde :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 112)
      (withLsCodeLoaded lsmpl curveKeyPairSerdeBudgetSpec)
  kemKeyPairSerde :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 113)
      (withLsCodeLoaded lsmpl (kemKeyPairFromPubPrivOkSpec M A lim))
  preKeyRecordKeyPair :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 67)
      (withLsCodeLoaded lsmpl preKeyRecordKeyPairBudgetSpec)
  dropSpe2 :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 511)
      (withLsCodeLoaded lsmpl (withLsRoLoaded lsmpl (dropSpeSpec M A lim)))
  isSameAccount :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 17)
      (withLsCodeLoaded lsmpl (isSameAccountDistinctSpec A.repAlloc uuidTryParse))
  initializeBobV1 : InitializeBobV1OkPlacedOfEnv P A lim F BobV1Env ext
  initializeBobErr :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 75)
      (initializeBobSessionErrPlacedSpec P A lim AcceptErrEnv)
  promoteStateEmpty :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 47)
      (withLsCodeLoaded lsmpl promoteStateEmptySpec)
  dropProcessPrekeyImplState1 :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 509)
      (withLsCodeLoaded lsmpl dropProcessPrekeyImplState1Spec)
  dropSessionStructure3 :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim))

structure StageP2PureCalleesPlaced4KOfEnv [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop where
  publicKeySerialize :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpec M A lim))
  promoteMatchingSessionEmpty :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 50)
      (withLsCodeLoaded lsmpl promoteMatchingSessionEmptySpec)
  curveKeyPairSerde :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 112)
      (withLsCodeLoaded lsmpl curveKeyPairSerdeBudgetSpec)
  kemKeyPairSerde :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 113)
      (withLsCodeLoaded lsmpl (kemKeyPairFromPubPrivOkSpec M A lim))
  preKeyRecordKeyPair :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 67)
      (withLsCodeLoaded lsmpl preKeyRecordKeyPairBudgetSpec)
  dropSpe2 :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 511)
      (withLsCodeLoaded lsmpl (withLsRoLoaded lsmpl (dropSpeSpec M A lim)))
  isSameAccount :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 17)
      (withLsCodeLoaded lsmpl (isSameAccountDistinctSpecExt A.repAlloc uuidTryParse))
  initializeBobV1 : InitializeBobV1OkPlaced4KOfEnv P A lim F BobV1Env ext
  initializeBobErr :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 75)
      (initializeBobSessionErr4KPlacedSpec P A lim AcceptErrEnv)
  promoteStateEmpty :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 47)
      (withLsCodeLoaded lsmpl promoteStateEmpty4KSpec)
  dropProcessPrekeyImplState1 :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 509)
      (withLsCodeLoaded lsmpl dropProcessPrekeyImplState1Spec)
  dropSessionStructure3 :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim))

abbrev StageP2PureCalleesPlaced [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  StageP2PureCalleesPlacedOfEnv P A lim F (InitializeBobV1Env F) AcceptErrEnv ext

abbrev StageP2PureCalleesPlaced4K [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  StageP2PureCalleesPlaced4KOfEnv P A lim F (InitializeBobV1Env F) AcceptErrEnv ext

abbrev StageP2PureCalleesExtPlaced [LibsignalPlacement] := @StageP2PureCalleesPlaced4K

theorem StageP2PureCalleesPlacedOfEnv.of_trapsOnly [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    {ext1 ext2 : String → Option (State → State)}
    (hT : TrapsOnly (stageP1ProgPlaced ext1) (stageP1ProgPlaced ext2))
    (h : StageP2PureCalleesPlacedOfEnv P A lim F BobV1Env AcceptErrEnv ext1) :
    StageP2PureCalleesPlacedOfEnv P A lim F BobV1Env AcceptErrEnv ext2 where
  publicKeySerialize := subroutine_ok.of_trapsOnly hT h.publicKeySerialize
  promoteMatchingSessionEmpty := subroutine_ok.of_trapsOnly hT h.promoteMatchingSessionEmpty
  curveKeyPairSerde := subroutine_ok.of_trapsOnly hT h.curveKeyPairSerde
  kemKeyPairSerde := subroutine_ok.of_trapsOnly hT h.kemKeyPairSerde
  preKeyRecordKeyPair := subroutine_ok.of_trapsOnly hT h.preKeyRecordKeyPair
  dropSpe2 := subroutine_ok.of_trapsOnly hT h.dropSpe2
  isSameAccount := subroutine_ok.of_trapsOnly hT h.isSameAccount
  initializeBobV1 := InitializeBobV1OkPlacedOfEnv.of_trapsOnly hT h.initializeBobV1
  initializeBobErr := subroutine_ok.of_trapsOnly hT h.initializeBobErr
  promoteStateEmpty := subroutine_ok.of_trapsOnly hT h.promoteStateEmpty
  dropProcessPrekeyImplState1 := subroutine_ok.of_trapsOnly hT h.dropProcessPrekeyImplState1
  dropSessionStructure3 := subroutine_ok.of_trapsOnly hT h.dropSessionStructure3

theorem StageP2PureCalleesPlaced4KOfEnv.of_trapsOnly [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    {ext1 ext2 : String → Option (State → State)}
    (hT : TrapsOnly (stageP1ProgPlaced ext1) (stageP1ProgPlaced ext2))
    (h : StageP2PureCalleesPlaced4KOfEnv P A lim F BobV1Env AcceptErrEnv ext1) :
    StageP2PureCalleesPlaced4KOfEnv P A lim F BobV1Env AcceptErrEnv ext2 where
  publicKeySerialize := subroutine_ok.of_trapsOnly hT h.publicKeySerialize
  promoteMatchingSessionEmpty := subroutine_ok.of_trapsOnly hT h.promoteMatchingSessionEmpty
  curveKeyPairSerde := subroutine_ok.of_trapsOnly hT h.curveKeyPairSerde
  kemKeyPairSerde := subroutine_ok.of_trapsOnly hT h.kemKeyPairSerde
  preKeyRecordKeyPair := subroutine_ok.of_trapsOnly hT h.preKeyRecordKeyPair
  dropSpe2 := subroutine_ok.of_trapsOnly hT h.dropSpe2
  isSameAccount := subroutine_ok.of_trapsOnly hT h.isSameAccount
  initializeBobV1 := InitializeBobV1OkPlaced4KOfEnv.of_trapsOnly hT h.initializeBobV1
  initializeBobErr := subroutine_ok.of_trapsOnly hT h.initializeBobErr
  promoteStateEmpty := subroutine_ok.of_trapsOnly hT h.promoteStateEmpty
  dropProcessPrekeyImplState1 := subroutine_ok.of_trapsOnly hT h.dropProcessPrekeyImplState1
  dropSessionStructure3 := subroutine_ok.of_trapsOnly hT h.dropSessionStructure3

/-! ## 6. `StageP2MemInv`, `InitializeBobV1{MemInv,Frozen}Ok*`, and `StageP2BaseCalleesPlaced4K` -/

export CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (StageP2MemInv)
export CryptoVerification.E2E.Pqxdh.ResponderCore (withBobMemInv)

def InitializeBobV1MemInvOkAtPlacedOfEnv [LibsignalPlacement] {M : AllocCostModel}
    (Φ : Memory → Prop)
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop)
    (ext : String → Option (State → State)) (bobV1Stk : Nat) : Prop :=
  ∀ {st : M.σ} {Qp : State → SepProp → Prop}
    (s0 : State) (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp),
    Φ s0.mem → s0.status = ExecStatus.Running →
    s0.pc = lsmpl.base 75 →
    s0.spAligned = true → s0.sp - 576#64 ≠ 0#64 →
    s0.readReg64 (.gpr 0#5) = argPtr → s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr →
    s0.readReg64 (.gpr 8#5) = outPtr →
    inp.trustedPeer = true → inp.replayOk = true →
    inp.hdr.opkId?.isSome = inp.opkBSk?.isSome →
    WellSizedAcceptKeysInput inp → ikBPk.length = 32 → spkBPk.length = 32 →
    acceptKeys P inp = some drKey →
    FitsEnv M lim st (BobV1Env inp drKey) →
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 (.gpr 30#5)) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk 0#8 ∗
       memRegion outPtr 344 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp bobV1Stk ∗ A.pool lim st s0 ∗ Frame)
      (fun sf P_f =>
        ∃ (evs : List AllocEvent),
          BobV1Env inp drKey evs ∧
          (∃ (localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
              ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr spqrCap spqrBufPtr : BitVec 64)
             (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64),
            localIkBoxPtr ≠ 0#64 ∧ remoteIkBoxPtr ≠ 0#64 ∧ rootKeyBoxPtr ≠ 0#64 ∧
            baseKeyBoxPtr ≠ 0#64 ∧ ratchetPubBoxPtr ≠ 0#64 ∧ ratchetPrivBoxPtr ≠ 0#64 ∧
            chainKeyBoxPtr ≠ 0#64 ∧ (P_f ⊢
              (outPtr ↦ₛ p2BobSession344Bv8V1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
                spqrCap spqrBufPtr
                (BitVec.ofNat 64 (initialStateValue F (p2BobSpqrParams drKey.pqrKey)).length)
                ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
                pad_f4 c0 c1 c2 c3 c4 d0 d1 d2) ∗
              p2BobSpqrVecBufBudget A spqrCap spqrBufPtr
                (initialStateValue F (p2BobSpqrParams drKey.pqrKey)) ∗
              bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
                inp ikBPk spkBPk 0#8 ∗
              (localIkBoxPtr ↦ₛ bytesToBv8 (encodeEC ikBPk)) ∗ A.live localIkBoxPtr 33 1 ∗
              (remoteIkBoxPtr ↦ₛ bytesToBv8 (encodeEC inp.hdr.ikAPk)) ∗
              A.live remoteIkBoxPtr 33 1 ∗
              (rootKeyBoxPtr ↦ₛ bytesToBv8 drKey.rootKey) ∗ A.live rootKeyBoxPtr 32 1 ∗
              (baseKeyBoxPtr ↦ₛ bytesToBv8 (encodeEC inp.hdr.ekAPk)) ∗
              A.live baseKeyBoxPtr 33 1 ∗
              (ratchetPubBoxPtr ↦ₛ bytesToBv8 (encodeEC spkBPk)) ∗
              A.live ratchetPubBoxPtr 33 1 ∗
              (ratchetPrivBoxPtr ↦ₛ bytesToBv8 inp.spkBSk) ∗ A.live ratchetPrivBoxPtr 32 1 ∗
              (chainKeyBoxPtr ↦ₛ bytesToBv8 drKey.chainKey) ∗ A.live chainKeyBoxPtr 32 1 ∗
              (lsLogFilterAddr ↦₆₄ 0#64) ∗
              stackAt s0.sp bobV1Stk ∗ A.pool lim (M.stepEvents evs st) sf ∗ Frame) ∧
            sf.status = ExecStatus.Running ∧ sf.pc = s0.readReg64 (.gpr 30#5) ∧ sf.sp = s0.sp ∧
            CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace))
      Qp

def InitializeBobV1MemInvOkPlacedOfEnv [LibsignalPlacement] {M : AllocCostModel}
    (Φ : Memory → Prop)
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  InitializeBobV1MemInvOkAtPlacedOfEnv Φ P A lim F BobV1Env ext (stageP2bStack + 0x700)

def InitializeBobV1MemInvOkPlaced4KOfEnv [LibsignalPlacement] {M : AllocCostModel}
    (Φ : Memory → Prop)
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  InitializeBobV1MemInvOkAtPlacedOfEnv Φ P A lim F BobV1Env ext (768 + pqxdhEntryStackExt)

abbrev InitializeBobV1MemInvOkAtPlaced [LibsignalPlacement] {M : AllocCostModel}
    (Φ : Memory → Prop)
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) (bobV1Stk : Nat) : Prop :=
  InitializeBobV1MemInvOkAtPlacedOfEnv Φ P A lim F (InitializeBobV1Env F) ext bobV1Stk

abbrev InitializeBobV1MemInvOkPlaced [LibsignalPlacement] {M : AllocCostModel}
    (Φ : Memory → Prop)
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  InitializeBobV1MemInvOkPlacedOfEnv Φ P A lim F (InitializeBobV1Env F) ext

abbrev InitializeBobV1MemInvOkPlaced4K [LibsignalPlacement] {M : AllocCostModel}
    (Φ : Memory → Prop)
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  InitializeBobV1MemInvOkPlaced4KOfEnv Φ P A lim F (InitializeBobV1Env F) ext

theorem InitializeBobV1MemInvOkAtPlacedOfEnv.mono_env [LibsignalPlacement] {M : AllocCostModel}
    {Φ : Memory → Prop} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {Env₁ Env₂ : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {ext : String → Option (State → State)} {bobV1Stk : Nat}
    (h : InitializeBobV1MemInvOkAtPlacedOfEnv Φ P A lim F Env₁ ext bobV1Stk)
    (hsub : ∀ inp drKey evs, Env₁ inp drKey evs → Env₂ inp drKey evs) :
    InitializeBobV1MemInvOkAtPlacedOfEnv Φ P A lim F Env₂ ext bobV1Stk := by
  intro st Qp s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr
    drKey Frame hΦ hrun hpc hsp hpqr hx0 hx1 hx8 htr hrep hopk hwell hik hspk hacc hfits
  have hfits₁ : FitsEnv M lim st (Env₁ inp drKey) :=
    fun evs hevs => hfits evs (hsub inp drKey evs hevs)
  have hcall := h (st := st) (Qp := Qp) s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr
    ratchetKeyPairPtr outPtr drKey Frame
    hΦ hrun hpc hsp hpqr hx0 hx1 hx8 htr hrep hopk hwell hik hspk hacc hfits₁
  intro R hm hL
  obtain ⟨sf, hst, ⟨hpc', hrun', Pf, hmf, evs, hevs, hrest⟩ | hpan⟩ := hcall R hm hL
  · exact ⟨sf, hst, Or.inl ⟨hpc', hrun', Pf, hmf, evs, hsub inp drKey evs hevs, hrest⟩⟩
  · exact ⟨sf, hst, Or.inr hpan⟩

theorem InitializeBobV1MemInvOkAtPlacedOfEnv.of_trapsOnly [LibsignalPlacement] {M : AllocCostModel}
    (Φ : Memory → Prop) (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop)
    (bobV1Stk : Nat) (ext : String → Option (State → State))
    (hext : ∀ sym, (stageP1ProgPlaced ext).externAt? (lsρ sym) = none) :
    (∀ s : State, (stageP1ProgPlaced ext).fetch s.pc = none) →
      InitializeBobV1MemInvOkAtPlacedOfEnv Φ P A lim F BobV1Env ext bobV1Stk := by
  let _ := hext
  intro hfetch
  exfalso
  have hnone := hfetch (((default : State)).setPC stageP1EntryPlaced)
  simp [State.setPC, stageP1ProgPlaced, stageP1EntryPlaced,
    CryptoVerification.CliHandshake.RespClosurePlaced.lsProg_518,
    CryptoVerification.CliHandshake.RespClosurePlaced.blkPC_518_rebase_fetch_base] at hnone

theorem InitializeBobV1MemInvOkPlacedOfEnv.of_trapsOnly [LibsignalPlacement] {M : AllocCostModel}
    (Φ : Memory → Prop) (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop)
    (ext : String → Option (State → State))
    (hext : ∀ sym, (stageP1ProgPlaced ext).externAt? (lsρ sym) = none) :
    (∀ s : State, (stageP1ProgPlaced ext).fetch s.pc = none) →
      InitializeBobV1MemInvOkPlacedOfEnv Φ P A lim F BobV1Env ext := by
  exact InitializeBobV1MemInvOkAtPlacedOfEnv.of_trapsOnly Φ P A lim F BobV1Env _ ext hext

theorem InitializeBobV1MemInvOkPlaced4KOfEnv.of_trapsOnly [LibsignalPlacement] {M : AllocCostModel}
    (Φ : Memory → Prop) (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop)
    (ext : String → Option (State → State))
    (hext : ∀ sym, (stageP1ProgPlaced ext).externAt? (lsρ sym) = none) :
    (∀ s : State, (stageP1ProgPlaced ext).fetch s.pc = none) →
      InitializeBobV1MemInvOkPlaced4KOfEnv Φ P A lim F BobV1Env ext := by
  exact InitializeBobV1MemInvOkAtPlacedOfEnv.of_trapsOnly Φ P A lim F BobV1Env _ ext hext

theorem InitializeBobV1MemInvOkPlacedOfEnv.to_4K [LibsignalPlacement] {M : AllocCostModel}
    {Φ : Memory → Prop} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (h : InitializeBobV1MemInvOkPlacedOfEnv Φ P A lim F BobV1Env ext) :
    InitializeBobV1MemInvOkPlaced4KOfEnv Φ P A lim F BobV1Env ext := by
  intro st Qp s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr
    drKey Frame hΦ hrun hpc hsp hpqr hx0 hx1 hx8 htr hrep hopk hwell hik hspk hacc hfits
  let F_stk : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 (768 + pqxdhEntryStackExt))
      ((768 + pqxdhEntryStackExt) - (stageP2bStack + 0x700))
  have hsplit := p2_stackAt_split_of_le s0.sp (768 + pqxdhEntryStackExt)
    (stageP2bStack + 0x700) (by decide) (by decide)
  have hcall := h (st := st) (Qp := Qp) s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr
    ratchetKeyPairPtr outPtr drKey (F_stk ∗ Frame)
    hΦ hrun hpc hsp hpqr hx0 hx1 hx8 htr hrep hopk hwell hik hspk hacc hfits
  intro R hm hL
  have hm' : s0.mem ⊨
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr inp ikBPk spkBPk 0#8 ∗
        memRegion outPtr 344 ∗ lsLogFilterAddr ↦₆₄ 0#64 ∗
        stackAt s0.sp (stageP2bStack + 0x700) ∗ A.pool lim st s0 ∗ (F_stk ∗ Frame)) ∗ R := by
    refine Satisfies.of_eq hm ?_; dsimp only [F_stk]; rw [hsplit]; ac_rfl
  obtain ⟨sf, hst, ⟨hpc', hrun', Pf, hmf, evs, hevs, localIkBoxPtr, remoteIkBoxPtr, rootKeyBoxPtr,
    baseKeyBoxPtr, ratchetPubBoxPtr, ratchetPrivBoxPtr, chainKeyBoxPtr, spqrCap, spqrBufPtr,
    pad_f4, c0, c1, c2, c3, c4, d0, d1, d2, hn1, hn2, hn3, hn4, hn5, hn6, hn7,
    hPf, hst'⟩ | hpan⟩ := hcall R hm' hL
  · refine ⟨sf, hst, Or.inl ⟨hpc', hrun', Pf, hmf, evs, hevs, localIkBoxPtr,
      remoteIkBoxPtr, rootKeyBoxPtr, baseKeyBoxPtr, ratchetPubBoxPtr, ratchetPrivBoxPtr,
      chainKeyBoxPtr, spqrCap, spqrBufPtr, pad_f4, c0, c1, c2, c3, c4, d0, d1, d2,
      hn1, hn2, hn3, hn4, hn5, hn6, hn7,
      Entails.trans hPf (Entails.of_eq ?_), hst'⟩⟩
    dsimp only [F_stk]; rw [hsplit]; ac_rfl
  · exact ⟨sf, hst, Or.inr hpan⟩

theorem InitializeBobV1MemInvOkPlaced.to_4K [LibsignalPlacement] {M : AllocCostModel}
    {Φ : Memory → Prop} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (h : InitializeBobV1MemInvOkPlaced Φ P A lim F ext) :
    InitializeBobV1MemInvOkPlaced4K Φ P A lim F ext := by
  exact InitializeBobV1MemInvOkPlacedOfEnv.to_4K h

def InitializeBobV1FrozenOkAtPlacedOfEnv [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop)
    (ext : String → Option (State → State)) (bobV1Stk : Nat) : Prop :=
  InitializeBobV1MemInvOkAtPlacedOfEnv (CryptoVerification.LibsignalFrozen lsmpl)
    P A lim F BobV1Env ext bobV1Stk

def InitializeBobV1FrozenOkPlacedOfEnv [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  InitializeBobV1MemInvOkPlacedOfEnv (CryptoVerification.LibsignalFrozen lsmpl)
    P A lim F BobV1Env ext

def InitializeBobV1FrozenOkPlaced4KOfEnv [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  InitializeBobV1MemInvOkPlaced4KOfEnv (CryptoVerification.LibsignalFrozen lsmpl)
    P A lim F BobV1Env ext

abbrev InitializeBobV1FrozenOkAtPlaced [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) (bobV1Stk : Nat) : Prop :=
  InitializeBobV1FrozenOkAtPlacedOfEnv P A lim F (InitializeBobV1Env F) ext bobV1Stk

abbrev InitializeBobV1FrozenOkPlaced [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  InitializeBobV1FrozenOkPlacedOfEnv P A lim F (InitializeBobV1Env F) ext

abbrev InitializeBobV1FrozenOkPlaced4K [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  InitializeBobV1FrozenOkPlaced4KOfEnv P A lim F (InitializeBobV1Env F) ext

theorem InitializeBobV1FrozenOkAtPlacedOfEnv.mono_env [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {Env₁ Env₂ : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {ext : String → Option (State → State)} {bobV1Stk : Nat}
    (h : InitializeBobV1FrozenOkAtPlacedOfEnv P A lim F Env₁ ext bobV1Stk)
    (hsub : ∀ inp drKey evs, Env₁ inp drKey evs → Env₂ inp drKey evs) :
    InitializeBobV1FrozenOkAtPlacedOfEnv P A lim F Env₂ ext bobV1Stk := by
  exact InitializeBobV1MemInvOkAtPlacedOfEnv.mono_env h hsub

theorem InitializeBobV1FrozenOkAtPlacedOfEnv.of_trapsOnly [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop)
    (bobV1Stk : Nat) (ext : String → Option (State → State))
    (hext : ∀ sym, (stageP1ProgPlaced ext).externAt? (lsρ sym) = none) :
    (∀ s : State, (stageP1ProgPlaced ext).fetch s.pc = none) →
      InitializeBobV1FrozenOkAtPlacedOfEnv P A lim F BobV1Env ext bobV1Stk := by
  exact InitializeBobV1MemInvOkAtPlacedOfEnv.of_trapsOnly
    (CryptoVerification.LibsignalFrozen lsmpl) P A lim F BobV1Env bobV1Stk ext hext

theorem InitializeBobV1FrozenOkPlacedOfEnv.of_trapsOnly [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop)
    (ext : String → Option (State → State))
    (hext : ∀ sym, (stageP1ProgPlaced ext).externAt? (lsρ sym) = none) :
    (∀ s : State, (stageP1ProgPlaced ext).fetch s.pc = none) →
      InitializeBobV1FrozenOkPlacedOfEnv P A lim F BobV1Env ext := by
  exact InitializeBobV1MemInvOkPlacedOfEnv.of_trapsOnly
    (CryptoVerification.LibsignalFrozen lsmpl) P A lim F BobV1Env ext hext

theorem InitializeBobV1FrozenOkPlaced4KOfEnv.of_trapsOnly [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop)
    (ext : String → Option (State → State))
    (hext : ∀ sym, (stageP1ProgPlaced ext).externAt? (lsρ sym) = none) :
    (∀ s : State, (stageP1ProgPlaced ext).fetch s.pc = none) →
      InitializeBobV1FrozenOkPlaced4KOfEnv P A lim F BobV1Env ext := by
  exact InitializeBobV1MemInvOkPlaced4KOfEnv.of_trapsOnly
    (CryptoVerification.LibsignalFrozen lsmpl) P A lim F BobV1Env ext hext

theorem InitializeBobV1FrozenOkPlacedOfEnv.to_4K [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (h : InitializeBobV1FrozenOkPlacedOfEnv P A lim F BobV1Env ext) :
    InitializeBobV1FrozenOkPlaced4KOfEnv P A lim F BobV1Env ext := by
  exact InitializeBobV1MemInvOkPlacedOfEnv.to_4K h

theorem InitializeBobV1FrozenOkPlaced.to_4K [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (h : InitializeBobV1FrozenOkPlaced P A lim F ext) :
    InitializeBobV1FrozenOkPlaced4K P A lim F ext := by
  exact InitializeBobV1MemInvOkPlacedOfEnv.to_4K h

def initializeBobSessionErrMemInv4KPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (Φ : Memory → Prop) (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop) :
    Spec (InitBobCallGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl
    (withBobMemInv Φ (initializeBobSessionErr4KInnerPlacedSpec P A lim AcceptErrEnv))

def initializeBobSessionErrFrozen4KPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop) :
    Spec (InitBobCallGhost × M.σ) :=
  initializeBobSessionErrMemInv4KPlacedSpec (CryptoVerification.LibsignalFrozen lsmpl)
    P A lim AcceptErrEnv

def initializeBobSessionErrOwnedMemInv4KPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (Φ : Memory → Prop) (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop) :
    Spec (InitBobCallGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl
    (withBobMemInv Φ (initializeBobSessionErrOwned4KInnerPlacedSpec P A lim AcceptErrEnv))

def initializeBobSessionErrOwnedFrozen4KPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop) :
    Spec (InitBobCallGhost × M.σ) :=
  initializeBobSessionErrOwnedMemInv4KPlacedSpec (CryptoVerification.LibsignalFrozen lsmpl)
    P A lim AcceptErrEnv

theorem initializeBobSessionErrFrozenPlacedSpec_to_4K [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64} {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (h : subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl (initializeBobSessionErrFrozenPlacedSpec P A lim AcceptErrEnv))) :
    subroutine_ok prog entry (initializeBobSessionErrFrozen4KPlacedSpec P A lim AcceptErrEnv) := by
  refine subroutine_ok_map h ?_
  rintro ⟨g, st⟩ R s0 hpre
  let F_stk : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 (768 + pqxdhEntryStackExt))
      ((768 + pqxdhEntryStackExt) - (768 + pqxdhEntryStack))
  dsimp only [initializeBobSessionErrFrozen4KPlacedSpec,
    initializeBobSessionErrMemInv4KPlacedSpec, withLsCodeRoLoaded, withBobMemInv] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hro, hpre⟩
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hfr, hpre⟩
  dsimp only [initializeBobSessionErr4KInnerPlacedSpec] at hpre
  rw [p2_stackAt_split_of_le s0.sp (768 + pqxdhEntryStackExt)
    (768 + pqxdhEntryStack) (by decide) (by decide)] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hmem⟩
  have hnone : acceptKeys P g.inp = none := hpure.2.2.2.2.2.2.2.2.2.1
  refine ⟨(g, st), F_stk ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [initializeBobSessionErrFrozenPlacedSpec,
      CryptoVerification.LibsignalTripleRatchet.withLsFrozen, withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hro, ?_⟩
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hfr, ?_⟩
    dsimp only [initializeBobSessionErrInnerPlacedSpec, F_stk]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, Satisfies.of_eq hmem (by ac_rfl)⟩
  · dsimp only [initializeBobSessionErrFrozenPlacedSpec,
      initializeBobSessionErrInnerPlacedSpec,
      initializeBobSessionInnerPlacedSpec,
      initializeBobSessionErrFrozen4KPlacedSpec,
      initializeBobSessionErrMemInv4KPlacedSpec,
      initializeBobSessionErr4KInnerPlacedSpec,
      CryptoVerification.LibsignalTripleRatchet.withLsFrozen,
      withLsCodeRoLoaded, withBobMemInv, F_stk] at hpost ⊢
    rw [sepExists_sepConj_left] at hpost ⊢
    refine Satisfies.of_eq hpost ?_
    congr 1; funext evs
    rw [hnone]
    dsimp only
    rw [p2_stackAt_split_of_le s0.sp (768 + pqxdhEntryStackExt)
      (768 + pqxdhEntryStack) (by decide) (by decide)]
    ac_rfl

theorem initializeBobSessionErrOwnedFrozenPlacedSpec_to_4K [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64} {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (h : subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl
        (initializeBobSessionErrOwnedFrozenPlacedSpec P A lim AcceptErrEnv))) :
    subroutine_ok prog entry
      (initializeBobSessionErrOwnedFrozen4KPlacedSpec P A lim AcceptErrEnv) := by
  refine subroutine_ok_map h ?_
  rintro ⟨g, st⟩ R s0 hpre
  let F_stk : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 (768 + pqxdhEntryStackExt))
      ((768 + pqxdhEntryStackExt) - (768 + pqxdhEntryStack))
  dsimp only [initializeBobSessionErrOwnedFrozen4KPlacedSpec,
    initializeBobSessionErrOwnedMemInv4KPlacedSpec, withLsCodeRoLoaded, withBobMemInv] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hro, hpre⟩
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hfr, hpre⟩
  dsimp only [initializeBobSessionErrOwned4KInnerPlacedSpec] at hpre
  rw [p2_stackAt_split_of_le s0.sp (768 + pqxdhEntryStackExt)
    (768 + pqxdhEntryStack) (by decide) (by decide)] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hmem⟩
  refine ⟨(g, st), F_stk ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [initializeBobSessionErrOwnedFrozenPlacedSpec,
      CryptoVerification.LibsignalTripleRatchet.withLsFrozen, withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hro, ?_⟩
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hfr, ?_⟩
    dsimp only [initializeBobSessionErrOwnedInnerPlacedSpec, F_stk]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, Satisfies.of_eq hmem (by ac_rfl)⟩
  · dsimp only [initializeBobSessionErrOwnedFrozenPlacedSpec,
      initializeBobSessionErrOwnedInnerPlacedSpec,
      initializeBobSessionErrOwnedFrozen4KPlacedSpec,
      initializeBobSessionErrOwnedMemInv4KPlacedSpec,
      initializeBobSessionErrOwned4KInnerPlacedSpec,
      CryptoVerification.LibsignalTripleRatchet.withLsFrozen,
      withLsCodeRoLoaded, withBobMemInv, F_stk] at hpost ⊢
    rw [sepExists_sepConj_left] at hpost ⊢
    refine Satisfies.of_eq hpost ?_
    congr 1; funext evs
    rw [p2_stackAt_split_of_le s0.sp (768 + pqxdhEntryStackExt)
      (768 + pqxdhEntryStack) (by decide) (by decide)]
    ac_rfl

structure StageP2BaseCalleesPlaced4K [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop where
  publicKeySerialize :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpec M A lim))
  promoteMatchingSessionEmpty :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 50)
      (withLsCodeLoaded lsmpl promoteMatchingSessionEmptySpec)
  curveKeyPairSerde :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 112)
      (withLsCodeLoaded lsmpl curveKeyPairSerdeBudgetSpec)
  kemKeyPairSerde :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 113)
      (withLsCodeLoaded lsmpl (kemKeyPairFromPubPrivOkSpec M A lim))
  preKeyRecordKeyPair :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 67)
      (withLsCodeLoaded lsmpl preKeyRecordKeyPairBudgetSpec)
  dropSpe2 :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 511)
      (withLsCodeLoaded lsmpl (withLsRoLoaded lsmpl (dropSpeSpec M A lim)))
  isSameAccount :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 17)
      (withLsCodeLoaded lsmpl (isSameAccountDistinctSpecExt A.repAlloc uuidTryParse))
  promoteStateEmpty :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 47)
      (withLsCodeLoaded lsmpl promoteStateEmpty4KSpec)
  dropProcessPrekeyImplState1 :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 509)
      (withLsCodeLoaded lsmpl dropProcessPrekeyImplState1Spec)
  dropSessionStructure3 :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim))

def VacuousBobAllocEnv (evs : List AllocEvent) : Prop :=
  evs = [.alloc (VerifiedLibraries.Mallocng.MallocngMaxAllocSize + 1)]

theorem not_fitsEnv_vacuousBobAllocEnv {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} :
    ¬ FitsEnv M lim st VacuousBobAllocEnv := by
  intro hfits
  have h := (hfits _ rfl).1.1
  dsimp only [AllocEvent.withinMaxAlloc] at h
  omega

theorem StageP2PureCalleesPlaced4KOfEnv.toStageP2BaseCalleesPlaced4K [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (h : StageP2PureCalleesPlaced4KOfEnv P A lim F BobV1Env AcceptErrEnv ext) :
    StageP2BaseCalleesPlaced4K A lim ext := by
  exact {
    publicKeySerialize := h.publicKeySerialize
    promoteMatchingSessionEmpty := h.promoteMatchingSessionEmpty
    curveKeyPairSerde := h.curveKeyPairSerde
    kemKeyPairSerde := h.kemKeyPairSerde
    preKeyRecordKeyPair := h.preKeyRecordKeyPair
    dropSpe2 := h.dropSpe2
    isSameAccount := h.isSameAccount
    promoteStateEmpty := h.promoteStateEmpty
    dropProcessPrekeyImplState1 := h.dropProcessPrekeyImplState1
    dropSessionStructure3 := h.dropSessionStructure3
  }

theorem StageP2BaseCalleesPlaced4K.toVacuousPureCalleesPlaced4KOfEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h : StageP2BaseCalleesPlaced4K A lim ext) (P : Primitives) (F : ShaCompress) :
    StageP2PureCalleesPlaced4KOfEnv P A lim F
      (fun _ _ => VacuousBobAllocEnv) (fun _ => VacuousBobAllocEnv) ext := by
  refine {
    publicKeySerialize := h.publicKeySerialize
    promoteMatchingSessionEmpty := h.promoteMatchingSessionEmpty
    curveKeyPairSerde := h.curveKeyPairSerde
    kemKeyPairSerde := h.kemKeyPairSerde
    preKeyRecordKeyPair := h.preKeyRecordKeyPair
    dropSpe2 := h.dropSpe2
    isSameAccount := h.isSameAccount
    initializeBobV1 := ?_
    initializeBobErr := ?_
    promoteStateEmpty := h.promoteStateEmpty
    dropProcessPrekeyImplState1 := h.dropProcessPrekeyImplState1
    dropSessionStructure3 := h.dropSessionStructure3
  }
  · intro st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hfits
    exact (not_fitsEnv_vacuousBobAllocEnv hfits).elim
  · apply subroutine_ok_outcome_intro
    rintro ⟨g, st⟩ R s0 _ _ hpre _
    dsimp only [initializeBobSessionErr4KPlacedSpec, withLsCodeRoLoaded,
      initializeBobSessionErr4KInnerPlacedSpec] at hpre
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨_, hpre⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
    exact (not_fitsEnv_vacuousBobAllocEnv hpre.1.2.2.2.2.2.2.2.2.2.2).elim

theorem StageP2BaseCalleesPlaced4K.of_trapsOnly [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (hext : ∀ sym, (stageP1ProgPlaced ext).externAt? (lsρ sym) = none) :
    (∀ s : State, (stageP1ProgPlaced ext).fetch s.pc = none) →
      StageP2BaseCalleesPlaced4K A lim ext := by
  let _ := hext
  intro hfetch
  exfalso
  have hnone := hfetch (((default : State)).setPC stageP1EntryPlaced)
  simp [State.setPC, stageP1ProgPlaced, stageP1EntryPlaced,
    CryptoVerification.CliHandshake.RespClosurePlaced.lsProg_518,
    CryptoVerification.CliHandshake.RespClosurePlaced.blkPC_518_rebase_fetch_base] at hnone

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget
