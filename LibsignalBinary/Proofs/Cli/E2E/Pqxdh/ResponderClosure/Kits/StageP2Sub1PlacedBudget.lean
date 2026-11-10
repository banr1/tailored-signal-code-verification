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
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksA1PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsAPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1Placed
public import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP2bAux
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs

/-!
# Budget-Threaded Relocatable Stage P2 Substage P2.1 and Call Combinators

Provides panic-free `LibsignalCodeRoLoaded` call-framing combinators, store-kit precondition
introducers, `P2Sub1Env`, and budget-threaded placed Substage P2.1 (`+0x0868 → +0x0f14`) on
Block `518`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  publicKeySerializeSpec publicKeySerializeSpecWithStack
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit hiding
  kitSpkGetShimSpec kitSpkGetPollSpec kitSpkGetPollSpecE kitKpkGetShimSpec
  SignedPreKeyStoreKitPlacedOk KyberPreKeyStoreKitPlacedOk
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderStore hiding
  sessionRecordEmptyHeaderAt promoteMatchingSessionEmptySpec promoteStateEmptySpec
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits hiding
  StageP2ClosureHooksPlaced
  StageP2PureCalleesPlaced
  StageP2PureCalleesPlaced4K
  StageP2PureCalleesExtPlaced
  InitializeBobV1OkPlaced
  InitializeBobV1OkPlaced4K
  promoteStateEmpty4KSpec
  isSameAccountDistinctAtSpec
  p2Memcpy4KSpec
  p2_seg1a_ext_placed_wp
  p2_seg1b_ext_placed_wp
  p2_seg1c_hooks_placed_wp
  p2_seg1c_ext_placed_wp
  p2_spkGetShim_pre_intro_placed
  p2_spkGetPoll_pre_intro_placed
  p2_kpkGetShim_pre_intro_placed
  promoteStateEmptySpec_lscl_to_4K
  isSameAccountDistinctSpec_lscl_to_ext
  stageP2_sub1_kits_ext_placed
  stageP2_sub1_kits_4k_placed
  stageP2_sub1_kits_hooks_placed
  stageP2_sub1_kits_placed
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvent FitsEvents FitsStep
  RustCliAllocBudget VmPreserved coarseCostModel coarseStep coarseStepReserve
  fitsEvents_append rustAllocEvents rustDeallocEvents
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  PublicKeySerializeEnv fitsEnv_publicKeySerialize_iff
  publicKeySerializeEvents publicKeySerializeSpec publicKeySerializeSpecWithStack
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitBudget (
  SignedPreKeyStoreBudgetEnv kitSpkGetPollSpec kitSpkGetPollSpecE kitSpkGetShimSpec
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget (kitKpkGetShimSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (
  SignedPreKeyStoreKitPlacedOk KyberPreKeyStoreKitPlacedOk
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsBudget (
  isSameAccountDistinctSpec isSameAccountDistinctSpecExt
  promoteStateEmpty4KSpec promoteStateEmptySpec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget (
  InitializeBobV1Env InitializeBobV1OkPlacedOfEnv
  StageP2ClosureHooksPlaced
  StageP2PureCalleesPlaced StageP2PureCalleesPlaced4K
  StageP2PureCalleesPlaced4KOfEnv StageP2PureCalleesPlacedOfEnv
  initializeBobSessionErrPlacedSpec_to_4K
  promoteMatchingSessionEmptySpec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksA1PlacedBudget (
  p2_seg1a_ext_placed_wp p2_seg1b_ext_placed_wp p2_seg1c_hooks_placed_wp
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsAPlacedBudget (
  p2_bind_sepWP_qp_frame_state_placed p2_bind_sepWPp_steps_frame_state
)

export CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  p2_bind_sepWP_qp_frame_placed
  p2_call_nopanic_rocl_steps_frame_placed
  p2_call_nopanic_lscl_steps_frame_placed
  p2_rocl_of_lscl_ro
)
export LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsAPlacedBudget (
  p2_bind_sepWP_qp_frame_state_placed
  p2_bind_sepWPp_steps_frame_state
)

set_option maxRecDepth 200000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  protocolAddressAt decryptPrekeySavedRegsAt

local macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [BitVec.add_assoc]
    | simp only [BitVec.reduceAdd]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

/-! ## 1. Placed Budget Call-Framing Combinators & `4K`/`Ext` Callee Lifts -/

abbrev p2_bind_sepWP_cro_frame_state_placed := @p2_bind_sepWP_qp_frame_state_placed

/-- `LibsignalCodeRoLoaded`-preserving `SepWPp` bind combinator mapping panic predicate `Qp₁`
into `Qp`. -/
theorem p2_bind_loaded_cro_qp [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P : SepProp} {Qm post Qp₁ Qp : State → SepProp → Prop}
    (hpan : ∀ sf Pf, Qp₁ sf Pf → Qp sf Pf)
    (hCode : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (h1 : SepWPp prog mid s P Qm Qp₁)
    (h2 : ∀ sm Pm, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem → Qm sm Pm →
      SepWPp prog target sm Pm post Qp) :
    SepWPp prog target s P post Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hmm, hQ⟩ | ⟨hp, Pm, hmm, hqp⟩ | hoom⟩ := h1 R hm hL
  · obtain ⟨sf, hsteps', hout⟩ :=
      h2 sm Pm hsteps hpcm hrunm (hCode.of_keepsFrozen hsteps.keepsFrozen) hQ R hmm
        (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hp, Pm, hmm, hpan sm Pm hqp⟩)⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

theorem p2_bind_loaded_cro_nopanic [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P : SepProp} {Qm post Qp : State → SepProp → Prop}
    (hCode : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (h1 : SepWPp prog mid s P Qm (fun _ _ => False))
    (h2 : ∀ sm Pm, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem → Qm sm Pm →
      SepWPp prog target sm Pm post Qp) :
    SepWPp prog target s P post Qp :=
  p2_bind_loaded_cro_qp (fun _ _ h => False.elim h) hCode h1 h2

/-- State-indexed spatial postcondition `SepWPp` bind combinator preserving
`LibsignalCodeRoLoaded lsmpl`. -/
theorem p2_bind_sepWPp_cro_frame_state_qp [LibsignalPlacement]
    {prog : Program} {mid ret : BitVec 64}
    {s : State} {P P_stage F : SepProp} {P_stage_post : State → SepProp}
    {Q_regs : State → Prop} {Q Qp₁ Qp : State → SepProp → Prop}
    (hpan : ∀ sf P_m, Qp₁ sf P_m → Qp sf (P_m ∗ F))
    (hCode : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hstage : SepWPp prog mid s P_stage
      (fun sm P_m => (P_m ⊢ P_stage_post sm) ∧ Q_regs sm)
      Qp₁)
    (hP : P = P_stage ∗ F)
    (hnext : ∀ sm : State, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_stage_post sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hent, hregs⟩ | ⟨hp, P_m, hmm, hqp⟩ | ⟨_, hoom⟩⟩ :=
    hstage (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P_stage_post sm ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Arm64.Satisfies.mono (sepConj_mono_left hent) hmm
    have hCodem : StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem :=
      hCode.of_keepsFrozen hsteps.keepsFrozen
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps hpcm hrunm hCodem hregs R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hmm
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hp, P_m ∗ F, hmm, hpan sm P_m hqp⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

/-- Panic-free (`Qp₁ = fun _ _ => False`) state-indexed `SepWPp` bind combinator preserving
`LibsignalCodeRoLoaded lsmpl`. -/
theorem p2_bind_sepWPp_cro_frame_state_nopanic [LibsignalPlacement]
    {prog : Program} {mid ret : BitVec 64}
    {s : State} {P P_stage F : SepProp} {P_stage_post : State → SepProp}
    {Q_regs : State → Prop} {Q Qp : State → SepProp → Prop}
    (hCode : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hstage : SepWPp prog mid s P_stage
      (fun sm P_m => (P_m ⊢ P_stage_post sm) ∧ Q_regs sm)
      (fun _ _ => False))
    (hP : P = P_stage ∗ F)
    (hnext : ∀ sm : State, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_stage_post sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp :=
  p2_bind_sepWPp_steps_frame_state hstage hP fun sm hsteps hpcm hrunm hregs =>
    hnext sm hsteps hpcm hrunm (hCode.of_keepsFrozen hsteps.keepsFrozen) hregs

/-- Panic-free (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`) call-framing combinator
for `StoreKit.withLsRoCl lsmpl spec` subroutines, accepting an entailment `P_spec ⊢ spec.pre x s`
and polymorphic in `{Qp : State → SepProp → Prop}`. -/
theorem p2_call_rocl_nopanic_steps_frame_placed [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State}
    {P P_spec F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hcall : subroutine_ok prog entry (StoreKit.withLsRoCl lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : P_spec ⊢ spec.pre x s)
    (hP : P = P_spec ∗ F)
    (hnext : ∀ sf : State, Steps prog s sf → sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by
      intro _; first | rfl | dsimp only [withVmPreserved, StoreKit.withLsLogOff, withLogOff, withEnvPre]; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by
      intro _ _; first | rfl | dsimp only [withVmPreserved, StoreKit.withLsLogOff, withLogOff, withEnvPre]; rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by
      intro _; first | rfl | dsimp only [withVmPreserved, StoreKit.withLsLogOff, withLogOff, withEnvPre]; rfl) :
    SepWPp prog ret s P Q Qp := by
  have hmid :
      SepWPp prog ret_pc s P
        (fun sm P_m =>
          sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧
          P_m = (StoreKit.withLsRoCl lsmpl spec).post x s sm ∗ F)
        Qp := by
    refine ProofLib.SepWPp.call_wpp (x := x) (F := F) hcall hpc hrun hsp hlr ?_
      (fun sf code _ _ hex => by
        dsimp only [StoreKit.withLsRoCl] at hex
        rw [hexit_false code sf] at hex
        exact not_satisfies_false_sepConj hex)
      (fun sf _ ⟨_, hpan⟩ => by
        dsimp only [StoreKit.withLsRoCl] at hpan
        rw [hpan_false sf] at hpan
        exact (not_satisfies_false_sepConj hpan).elim)
      (fun sm hpcm hrunm hspm hcsm => ProofLib.SepWPp.done hpcm hrunm ⟨hspm, hcsm, rfl⟩)
      (fun sm _ _ hoom_post => by
        dsimp only [StoreKit.withLsRoCl] at hoom_post
        rw [hoom_false sm] at hoom_post
        exact (not_satisfies_false_sepConj hoom_post).elim)
    intro R hm
    rw [hP, sepConj_assoc] at hm
    have hm0 : s.mem ⊨ spec.pre x s ∗ (F ∗ R) :=
      Arm64.Satisfies.mono (sepConj_mono_left hpre) hm
    dsimp only [StoreKit.withLsRoCl]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcrl, hm0⟩
  intro R hm hL
  obtain ⟨sm, hsteps, hout⟩ := hmid R hm hL
  rcases hout with ⟨hpcm, hrunm, _, hpost, hspm, hcsm, rfl⟩ | hpan | hoom_out
  · dsimp only [StoreKit.withLsRoCl] at hpost
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨hcrl', hpost⟩ := hpost
    rw [← sepConj_assoc] at hpost
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps hpcm hrunm hspm hsp_alm hcsm hcrl' R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom_out)⟩

/-- Panic-free (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`) call-framing combinator
for `withLsCodeLoaded lsmpl spec` subroutines, accepting an entailment `P_spec ⊢ spec.pre x s`
and polymorphic in `{Qp : State → SepProp → Prop}`. -/
theorem p2_call_lscl_nopanic_steps_frame_placed [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State}
    {P P_spec F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : P_spec ⊢ spec.pre x s)
    (hP : P = P_spec ∗ F)
    (hnext : ∀ sf : State, Steps prog s sf → sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by
      intro _; first | rfl | dsimp only [withVmPreserved, StoreKit.withLsLogOff, withLogOff, withEnvPre]; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by
      intro _ _; first | rfl | dsimp only [withVmPreserved, StoreKit.withLsLogOff, withLogOff, withEnvPre]; rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by
      intro _; first | rfl | dsimp only [withVmPreserved, StoreKit.withLsLogOff, withLogOff, withEnvPre]; rfl) :
    SepWPp prog ret s P Q Qp :=
  p2_call_rocl_nopanic_steps_frame_placed hcrl
    (StoreKit.subroutine_ok_rocl_of_withLsCodeRoLoaded
      (StoreKit.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hcall))
    hpc hrun hsp hlr hpre hP hnext hpan_false hexit_false hoom_false

/-- Budget-threaded `kitSpkGetShimSpec` precondition introduction at `b = 0#64`. -/
theorem p2_spkGetShim_pre_intro_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64}
    {x : PreKeyShimCall} {st : M.σ} {s : State}
    (hx0 : s.readReg64 .x0 = x.self) (hx1 : s.readReg32 .x1 = x.id)
    (hfits : FitsEnv M lim st (BoxAllocEnv spkKit.getBoxSize)) :
    A.pool lim st s ∗ stackAt s.sp spkKit.getShimStack ⊢
      (kitSpkGetShimSpec M A lim spkKit).pre (x, st) s := by
  dsimp only [kitSpkGetShimSpec]
  exact Entails.pure_right ⟨rfl, hx0, hx1, hfits⟩ (Entails.refl _)

/-- Budget-threaded `kitSpkGetPollSpecE` precondition introduction at `b = 0#64`. -/
theorem p2_spkGetPoll_pre_intro_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64}
    {spkEnv : SignedPreKeyStoreBudgetEnv spkKit}
    {x : PreKeyPollCall} {st0 : spkKit.SpkState} {st : M.σ} {s : State}
    (henv : spkKit.envOk s.fs.files)
    (hx0 : s.readReg64 .x0 = x.fut) (hx8 : s.readReg64 .x8 = x.out)
    (hid : spkKit.idOk x.id)
    (hfits : FitsEnv M lim st (spkEnv.getPollEnv st0 x.id)) :
    spkKit.getBoxAt x.fut x.self x.id 0#8 ∗ spkKit.storeAt x.self st0 ∗
      memRegion x.out 88 ∗ A.pool lim st s ∗ stackAt s.sp spkKit.getPollStack ⊢
        (kitSpkGetPollSpecE M A lim spkKit spkEnv).pre (x, st0, st) s := by
  dsimp only [kitSpkGetPollSpecE, withEnvPre, kitSpkGetPollSpec]
  exact Entails.pure_right henv (Entails.pure_right ⟨rfl, hx0, hx8, hid, hfits⟩ (Entails.refl _))

/-- Budget-threaded `kitKpkGetShimSpec` precondition introduction at `b = 0#64`. -/
theorem p2_kpkGetShim_pre_intro_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64}
    {x : PreKeyShimCall} {st : M.σ} {s : State}
    (hx0 : s.readReg64 .x0 = x.self) (hx1 : s.readReg32 .x1 = x.id)
    (hfits : FitsEnv M lim st (BoxAllocEnv kpkKit.getBoxSize)) :
    A.pool lim st s ∗ stackAt s.sp kpkKit.getShimStack ⊢
      (kitKpkGetShimSpec M A lim kpkKit).pre (x, st) s := by
  dsimp only [kitKpkGetShimSpec]
  exact Entails.pure_right ⟨rfl, hx0, hx1, hfits⟩ (Entails.refl _)

/-- Lift `withLsCodeLoaded lsmpl promoteStateEmptySpec` (`withVmPreserved`, `96` B stack) to
`withLsCodeLoaded lsmpl promoteStateEmpty4KSpec` (`allocHookStack = 4096` B). -/
theorem promoteStateEmptySpec_lscl_to_4K [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (withLsCodeLoaded lsmpl promoteStateEmptySpec)) :
    subroutine_ok prog entry (withLsCodeLoaded lsmpl promoteStateEmpty4KSpec) := by
  refine subroutine_ok_map h ?_
  rintro ⟨recPtr, srcPtr, bs⟩ R s0 hpre
  dsimp only [withLsCodeLoaded, promoteStateEmpty4KSpec, withVmPreserved,
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.promoteStateEmpty4KSpec] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl, hpre⟩ := hpre
  rw [stackAt_promote_state_eq s0.sp] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hmem⟩
  refine ⟨(recPtr, srcPtr, bs), stackAt (s0.sp - 96#64) (allocHookStack - 96) ∗ R,
    ?_, fun sf hpost => ?_⟩
  · dsimp only [withLsCodeLoaded, promoteStateEmptySpec, withVmPreserved,
      CryptoVerification.E2E.Pqxdh.ResponderStore.promoteStateEmptySpec]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, Satisfies.of_eq hmem (by sep_ac_rfl)⟩
  · dsimp only [withLsCodeLoaded, promoteStateEmptySpec, promoteStateEmpty4KSpec, withVmPreserved,
      CryptoVerification.E2E.Pqxdh.ResponderStore.promoteStateEmptySpec,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.promoteStateEmpty4KSpec] at hpost ⊢
    rw [stackAt_promote_state_eq s0.sp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1, hpost.2.1, Satisfies.of_eq hpost.2.2 (by sep_ac_rfl)⟩

/-- Lift `withLsCodeLoaded lsmpl (isSameAccountDistinctSpec A parse)` (`withVmPreserved`) to
`withLsCodeLoaded lsmpl (isSameAccountDistinctSpecExt A parse)`. -/
theorem isSameAccountDistinctSpec_lscl_to_ext [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64} {A : RustAlloc} {parse : UuidParser}
    (h : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (isSameAccountDistinctSpec A parse))) :
    subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (isSameAccountDistinctSpecExt A parse)) := by
  refine subroutine_ok_map h ?_
  rintro ⟨lIkA, lIk, locA, loc, rIkA, rIk, remA, rem⟩ R s0 hpre
  dsimp only [withLsCodeLoaded, isSameAccountDistinctSpecExt, withVmPreserved,
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctSpecExt] at hpre
  rw [p2_stackAt_split_of_le s0.sp
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctStackExt
    WireEntries.isSameAccountDistinctStack (by decide) (by decide)] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl, hpre⟩ := hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hmem⟩
  refine ⟨({ localIkA := lIkA, localIk := lIk, locA := locA, loc := loc,
             remoteIkA := rIkA, remoteIk := rIk, remA := remA, rem := rem } :
            WireEntries.IsSameAccountDistinctGhost),
    memRegion (s0.sp - BitVec.ofNat 64
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctStackExt)
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctStackExt -
        WireEntries.isSameAccountDistinctStack) ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [withLsCodeLoaded, isSameAccountDistinctSpec, withVmPreserved,
      CryptoVerification.E2E.Pqxdh.WireEntries.isSameAccountDistinctSpec]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, Satisfies.of_eq hmem (by sep_ac_rfl)⟩
  · dsimp only [withLsCodeLoaded, isSameAccountDistinctSpec, isSameAccountDistinctSpecExt,
      withVmPreserved, CryptoVerification.E2E.Pqxdh.WireEntries.isSameAccountDistinctSpec,
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctStackExt,
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctSpecExt] at hpost ⊢
    rw [p2_stackAt_split_of_le s0.sp
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctStackExt
      WireEntries.isSameAccountDistinctStack (by decide) (by decide)]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1, hpost.2.1, Satisfies.of_eq hpost.2.2 (by sep_ac_rfl)⟩

theorem _root_.LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget.StageP2PureCalleesPlacedOfEnv.to_4K
    [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (h : StageP2PureCalleesPlacedOfEnv P A lim F BobV1Env AcceptErrEnv ext) :
    StageP2PureCalleesPlaced4KOfEnv P A lim F BobV1Env AcceptErrEnv ext where
  publicKeySerialize := h.publicKeySerialize
  promoteMatchingSessionEmpty := h.promoteMatchingSessionEmpty
  curveKeyPairSerde := h.curveKeyPairSerde
  kemKeyPairSerde := h.kemKeyPairSerde
  preKeyRecordKeyPair := h.preKeyRecordKeyPair
  dropSpe2 := h.dropSpe2
  isSameAccount := isSameAccountDistinctSpec_lscl_to_ext h.isSameAccount
  initializeBobV1 := InitializeBobV1OkPlacedOfEnv.to_4K h.initializeBobV1
  initializeBobErr := initializeBobSessionErrPlacedSpec_to_4K h.initializeBobErr
  promoteStateEmpty := promoteStateEmptySpec_lscl_to_4K h.promoteStateEmpty
  dropProcessPrekeyImplState1 := h.dropProcessPrekeyImplState1
  dropSessionStructure3 := h.dropSessionStructure3

theorem StageP2PureCalleesPlaced_to_4K [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (h : StageP2PureCalleesPlaced P A lim F AcceptErrEnv ext) :
    StageP2PureCalleesPlaced4K P A lim F AcceptErrEnv ext :=
  h.to_4K

/-! ## 2. Substage P2.1 Event List, Envelope, & Proof (`+0x0868 -> +0x0f14`) -/

/-- Deterministic event list corresponding to `BoxAllocEnv boxSize`:
`[]` when `boxSize = 0`, `rustAllocEvents boxSize 8` when `0 < boxSize`. -/
def boxAllocEvents (boxSize : Nat) : List AllocEvent :=
  if boxSize = 0 then [] else rustAllocEvents boxSize 8

theorem boxAllocEnv_iff_eq (boxSize : Nat) (evs : List AllocEvent) :
    BoxAllocEnv boxSize evs ↔ evs = boxAllocEvents boxSize := by
  unfold BoxAllocEnv boxAllocEvents
  by_cases h0 : boxSize = 0
  · subst h0; simp
  · have hpos : 0 < boxSize := Nat.pos_of_ne_zero h0
    simp [h0, hpos]

theorem fitsEnv_boxAllocEnv_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (boxSize : Nat) :
    FitsEnv M lim st (BoxAllocEnv boxSize) ↔ FitsEvents M lim st (boxAllocEvents boxSize) := by
  constructor
  · intro h
    exact h (boxAllocEvents boxSize) ((boxAllocEnv_iff_eq boxSize _).mpr rfl)
  · intro h evs hevs
    rwa [(boxAllocEnv_iff_eq boxSize evs).mp hevs]

/-- Exact deterministic allocator event list of Substage P2.1 (`+0x0868 -> +0x0f14`):
`PublicKey::serialize` (`33` B align `1`), `__rust_dealloc(33, 1)`, and `spkKit.getShim`
(`boxAllocEvents spkBoxSize`). -/
def p2Sub1Events (spkBoxSize : Nat) : List AllocEvent :=
  publicKeySerializeEvents ++ rustDeallocEvents 33 1 ++ boxAllocEvents spkBoxSize

/-- Exact allocator event envelope of Substage P2.1 (`+0x0868 -> +0x0f14`). -/
def P2Sub1Env (spkBoxSize : Nat) (evs : List AllocEvent) : Prop :=
  evs = p2Sub1Events spkBoxSize

theorem fitsEnv_p2Sub1Env_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (spkBoxSize : Nat) :
    FitsEnv M lim st (P2Sub1Env spkBoxSize) ↔ FitsEvents M lim st (p2Sub1Events spkBoxSize) :=
  FitsEnv.eq_iff

theorem stepEvents_p2Sub1Events (M : AllocCostModel) (spkBoxSize : Nat) (st : M.σ) :
    M.stepEvents (boxAllocEvents spkBoxSize)
      (M.stepEvents (rustDeallocEvents 33 1)
        (M.stepEvents publicKeySerializeEvents st)) =
    M.stepEvents (p2Sub1Events spkBoxSize) st := by
  unfold p2Sub1Events
  rw [M.stepEvents_append, M.stepEvents_append]

-- Concrete `FitsEnv` non-vacuity witness for `P2Sub1Env 64` under `coarseCostModel`.
example :
    FitsEnv coarseCostModel
      { staticCount := 64, staticBytes := 67108864, physCap := 536870912, enforced := true }
      coarseCostModel.init
      (P2Sub1Env 64) := by
  rw [fitsEnv_p2Sub1Env_iff]
  have hevs : p2Sub1Events 64 = [.alloc 33, .free 1 33, .alloc 64] := by decide
  rw [hevs]
  dsimp only [FitsEvents, FitsEvent, AllocEvent.withinMaxAlloc, FitsStep,
    AllocCostModel.step, coarseCostModel, coarseStep, coarseStepReserve]
  decide

private theorem boxU8Buf_pk_serialize_entails_budget {M : AllocCostModel}
    (A : RustCliAllocBudget M) (ptr : BitVec 64) (pk : PublicKey) :
    boxU8Buf A.repAlloc ptr pk.serialize ⊢ A.live ptr 33 1 ∗ memRegion ptr 33 :=
  boxU8Buf_pk_serialize_entails A.repAlloc ptr pk

set_option maxHeartbeats 1200000 in
/-- Budget-Threaded Placed Kit-Generic Substage P2.1 (`+0x0868 -> +0x0f14`) on
`stageP1ProgPlaced ext`:
Serializes `baseKey` (`PublicKey::serialize`), calls `SessionRecord::promote_matching_session`
on an empty `SessionRecord`, deallocates the serialized key buffer (`33` B align `1`), and calls
`spkKit.getShim`, advancing `A.pool lim st s` to
`A.pool lim (M.stepEvents (p2Sub1Events spkKit.getBoxSize) st) sf` (`0` panics / `0` OOM under
`FitsEnv M lim st (P2Sub1Env spkKit.getBoxSize)`). -/
theorem stageP2_sub1_kits_ext_placed [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2PureCalleesPlaced4KOfEnv P A lim F BobV1Env AcceptErrEnv ext)
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64)
    (spkEnv : SignedPreKeyStoreBudgetEnv spkKit)
    (hspkOk : SignedPreKeyStoreKitPlacedOk A lim spkKit spkEnv ext)
    (stk : Nat)
    (hstk_pure : stageP2PureAndErrStack ≤ stk)
    (hstk_shim : spkKit.getShimStack ≤ stk)
    (hstk_lt : stk ≤ 2 ^ 64)
    (st : M.σ)
    (s0 s : State)
    (coroPtr msgPtr remoteAddrPtr localAddrPtr
     idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
     spkStorePtr kyberStorePtr kyberStoreVt : BitVec 64)
    (baseKey : PublicKey) (spkId : BitVec 32) (b_4f1 : BitVec 8)
    (hfits : FitsEnv M lim st (P2Sub1Env spkKit.getBoxSize))
    (hCode : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = stageP1EntryPlaced + 0x868#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx8 : s.readReg64 .x8 = kyberStorePtr)
    (hx9 : s.readReg64 .x9 = msgPtr)
    (hx10 : s.readReg64 .x10 = kyberStoreVt)
    (hx11 : s.readReg64 .x11 = preKeyStorePtr)
    (hx12 : s.readReg64 .x12 = remoteAddrPtr)
    (hx13 : s.readReg64 .x13 = preKeyStoreVt)
    (hx14 : s.readReg64 .x14 = localAddrPtr)
    (hx15 : s.readReg64 .x15 = idStorePtr)
    (hx16 : s.readReg64 .x16 = idStoreVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = spkStorePtr)
    (hx23 : s.readReg64 .x23 = coroPtr + 0xe0#64)
    (hx24 : s.readReg64 .x24 = spkKit.spk_vt) :
    SepWPp (stageP1ProgPlaced ext) (stageP1EntryPlaced + 0xf14#64) s
      (cells (coroPtr + 0x3f8#64) 6 ∗
       cells (coroPtr + 0x468#64) 4 ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗
       ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
       ((msgPtr + 0xec#64) ↦₃₂ spkId) ∗
       ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
       memRegion (s.sp + 0x3e0#64) 9 ∗
       ((spkKit.spk_vt + 0x18#64) ↦₆₄ᵣ (0#64 + spkKit.getShimOff)) ∗
       A.pool lim st s ∗
       stackAt s.sp stk)
      (fun sf P_f =>
        (P_f ⊢
          ∃∗ spkFutPtr : BitVec 64,
            ⌜sf.readReg64 .x0 = spkFutPtr ∧
              sf.readReg64 .x1 = 0#64 + spkKit.getFutVtOff ∧
              spkFutPtr ≠ 0#64 ∧
              spkFutPtr.toNat % 8 = 0⌝ ∗
            processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
              idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
              kyberStorePtr kyberStoreVt ∗
            ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
            sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗
            ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
            ((msgPtr + 0xec#64) ↦₃₂ spkId) ∗
            ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
            memRegion (s.sp + 0x3e0#64) 9 ∗
            ((spkKit.spk_vt + 0x18#64) ↦₆₄ᵣ (0#64 + spkKit.getShimOff)) ∗
            A.live spkFutPtr spkKit.getBoxSize 8 ∗
            spkKit.getBoxAt spkFutPtr spkStorePtr spkId 0#8 ∗
            A.pool lim (M.stepEvents (p2Sub1Events spkKit.getBoxSize) st) sf ∗
            stackAt s.sp stk) ∧
        sf.sp = s.sp ∧
        sf.trace = s.trace ∧
        sf.readReg64 .x19 = coroPtr ∧
        sf.readReg64 .x22 = spkStorePtr ∧
        sf.readReg64 .x23 = 0#64 ∧
        sf.readReg64 .x24 = spkKit.spk_vt ∧
        sf.readReg64 .x25 = s.sp + 0x210#64 ∧
        sf.readReg64 .x26 = 33#64 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem)
      Qp := by
  have hfits_all : FitsEvents M lim st (p2Sub1Events spkKit.getBoxSize) :=
    (fitsEnv_p2Sub1Env_iff spkKit.getBoxSize).mp hfits
  unfold p2Sub1Events at hfits_all
  rcases (fitsEvents_append M lim
      (publicKeySerializeEvents ++ rustDeallocEvents 33 1)
      (boxAllocEvents spkKit.getBoxSize) st).mp hfits_all with ⟨hfits_12, hfits_3⟩
  rcases (fitsEvents_append M lim
      publicKeySerializeEvents (rustDeallocEvents 33 1) st).mp hfits_12 with ⟨hfits_1, _⟩
  have hfits_ser : FitsEnv M lim st PublicKeySerializeEnv :=
    fitsEnv_publicKeySerialize_iff.mpr hfits_1
  let st1 := M.stepEvents publicKeySerializeEvents st
  let st2 := M.stepEvents (rustDeallocEvents 33 1) st1
  have hfits_3' : FitsEvents M lim st2 (boxAllocEvents spkKit.getBoxSize) := by
    simpa only [st1, st2, M.stepEvents_append] using hfits_3
  have hfits_shim : FitsEnv M lim st2 (BoxAllocEnv spkKit.getBoxSize) :=
    (fitsEnv_boxAllocEnv_iff spkKit.getBoxSize).mpr hfits_3'
  have hstep1 := p2_seg1a_ext_placed_wp (A := A) (lim := lim) ext st s
    coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    spkStorePtr spkKit.spk_vt kyberStorePtr kyberStoreVt b_4f1
    hpc hrun hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24
  refine p2_bind_sepWP_qp_frame_state_placed hCode hstep1 (by sep_focus)
    fun s1 _ hpc1 hrun1 hCode1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx19_1, _, hx22_1, hx23_1, hx24_1, hx25_1, _, hx27_1,
    hx28_1, hx29_1, hx30_1, hvregs1⟩
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp_align
  have hstk_ser := p2_stackAt_split_of_le s.sp stk publicKeySerializeStack
    (Nat.le_trans p2_pkSerStack_le_pure hstk_pure) hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_ser) (by sep_focus) ?_
  sep_norm
  refine p2_call_lscl_nopanic_steps_frame_placed
    (x := (⟨msgPtr + 0xa8#64, baseKey⟩, st))
    (P_spec := ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗ A.pool lim st s1 ∗
      stackAt s.sp publicKeySerializeStack)
    hCode1 hPure.publicKeySerialize hpc1 hrun1 hsp1_al hx30_1
    (by
      dsimp only [publicKeySerializeSpec, publicKeySerializeSpecWithStack, publicKeySerializeStack]
      rw [hsp1]
      exact Entails.pure_right ⟨hx0_1, hfits_ser⟩ (Entails.refl _))
    (by sep_focus)
    (hnext := fun s2 _ hpc2 hrun2 hsp2_1 _ hcs2 hCode2 => ?_)
  dsimp only [publicKeySerializeSpec, publicKeySerializeSpecWithStack,
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.boxU8Buf]
  rcases hcs2 with ⟨hcs2_19, _, _, hcs2_22, hcs2_23, hcs2_24, hcs2_25, _, hcs2_27, hcs2_28,
    hcs2_29, hvregs2_1⟩
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hcs2_19.trans hx19_1
  have hx22_2 : s2.readReg64 .x22 = spkStorePtr := hcs2_22.trans hx22_1
  have hx23_2 : s2.readReg64 .x23 = coroPtr + 0xe0#64 := hcs2_23.trans hx23_1
  have hx24_2 : s2.readReg64 .x24 = spkKit.spk_vt := hcs2_24.trans hx24_1
  have hx25_2 : s2.readReg64 .x25 = 4#64 := hcs2_25.trans hx25_1
  have hx27_2 : s2.readReg64 .x27 = s.readReg64 .x27 := hcs2_27.trans hx27_1
  have hx28_2 : s2.readReg64 .x28 = s.readReg64 .x28 := hcs2_28.trans hx28_1
  have hx29_2 : s2.readReg64 .x29 = s.readReg64 .x29 := hcs2_29.trans hx29_1
  rw [hsp1, show allocHookStack + 32 = publicKeySerializeStack from rfl]
  sep_norm
  refine SepWPp.pure_elim fun ⟨hx1_2, htr2⟩ => ?_
  refine SepWPp.weaken_frame (boxU8Buf_pk_serialize_entails_budget A (s2.readReg64 .x0) baseKey)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_ser.symm) (by sep_focus) ?_
  have hstep3 := p2_seg1b_ext_placed_wp (A := A) (lim := lim) ext st1 s2
    coroPtr (s2.readReg64 .x0) spkStorePtr
    spkKit.spk_vt hpc2 hrun2 rfl hx1_2 hx19_2 hx22_2 hx23_2 hx24_2 hx25_2
  rw [hsp2] at hstep3
  refine p2_bind_sepWP_qp_frame_state_placed hCode2 hstep3 (by sep_focus)
    fun s3 _ hpc3 hrun3 hCode3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3, htr3, hx0_3, _, _, _, hx8_3, hx19_3, hx21_3, hx22_3, _, hx24_3, _,
    hx26_3, hx27_3, hx28_3, hx29_3, hx30_3, hvregs3_2⟩
  have hsp3_al : s3.spAligned = true := by simpa only [State.spAligned, hsp3] using hsp_align
  have hstk_prom1 := p2_stackAt_split_of_le s.sp stk 1248
    (Nat.le_trans p2_prom1248_le_pure hstk_pure) hstk_lt
  have hstk_prom2 := stackAt_1248_promote_eq s.sp
  refine SepWPp.weaken_frame (Entails.of_eq hstk_prom1) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_prom2) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (memRegion_9_sp3e0_eq s.sp)) (by sep_focus) ?_
  simp only [sepConj_assoc]
  refine p2_call_nopanic_lscl_steps_frame_placed hCode3 hPure.promoteMatchingSessionEmpty
    hpc3 hrun3 hsp3_al hx30_3
    (x := (coroPtr + 0xe0#64, s.sp + 0x3e0#64))
    (R_pure := s3.readReg64 .x0 = coroPtr + 0xe0#64 ∧ s3.readReg64 .x8 = s.sp + 0x3e0#64)
    (T := sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗
      (∃∗ w0 : BitVec 64, (s.sp + 0x3e0#64) ↦₆₄ w0) ∗
      (∃∗ b8 : BitVec 8, (s.sp + 0x3e8#64) ↦₈ b8) ∗
      cells (s.sp - 1248#64) 8 ∗
      cells (s.sp - 1184#64) 10 ∗
      (∃∗ w2e0 : BitVec 64, (s.sp - 448#64) ↦₆₄ w2e0) ∗
      cells (s.sp - 96#64) 12)
    (by
      dsimp only [promoteMatchingSessionEmptySpec, withVmPreserved,
        CryptoVerification.E2E.Pqxdh.ResponderStore.promoteMatchingSessionEmptySpec]
      rw [hsp3, show (s.sp + 0x3e0#64) + 8#64 = s.sp + 0x3e8#64 by bv_omega]
      rfl)
    ⟨hx0_3, hx8_3⟩ (by sep_focus)
    (hnext := fun s4 _ hpc4 hrun4 hsp4_3 _ hcs4 hCode4 => ?_)
  dsimp only [promoteMatchingSessionEmptySpec, withVmPreserved,
    CryptoVerification.E2E.Pqxdh.ResponderStore.promoteMatchingSessionEmptySpec]
  rcases hcs4 with ⟨hcs4_19, _, hcs4_21, hcs4_22, _, hcs4_24, _, hcs4_26, hcs4_27, hcs4_28,
    hcs4_29, hvregs4_3⟩
  have hsp4 : s4.sp = s.sp := hsp4_3.trans hsp3
  have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := by rw [hsp4]; exact hsp_align
  have hx19_4 : s4.readReg64 .x19 = coroPtr := hcs4_19.trans hx19_3
  have hx21_4 : s4.readReg64 .x21 = s2.readReg64 .x0 := hcs4_21.trans hx21_3
  have hx22_4 : s4.readReg64 .x22 = spkStorePtr := hcs4_22.trans hx22_3
  have hx24_4 : s4.readReg64 .x24 = spkKit.spk_vt := hcs4_24.trans hx24_3
  have hx26_4 : s4.readReg64 .x26 = 33#64 := hcs4_26.trans hx26_3
  have hx27_4 : s4.readReg64 .x27 = s.readReg64 .x27 := hcs4_27.trans (hx27_3.trans hx27_2)
  have hx28_4 : s4.readReg64 .x28 = s.readReg64 .x28 := hcs4_28.trans (hx28_3.trans hx28_2)
  have hx29_4 : s4.readReg64 .x29 = s.readReg64 .x29 := hcs4_29.trans (hx29_3.trans hx29_2)
  rw [hsp3, show (s.sp + 0x3e0#64) + 8#64 = s.sp + 0x3e8#64 by bv_omega,
    show CryptoVerification.E2E.Pqxdh.ResponderStore.sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) =
      sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) from rfl]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun hvm4 => SepWPp.pure_elim fun htr4 => ?_
  refine SepWPp.transport_budgetPool hvm4 (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_prom2.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_prom1.symm) (by sep_focus) ?_
  have hstk_alloc := p2_stackAt_split_of_le s.sp stk allocHookStack
    (Nat.le_trans p2_alloc_le_pure hstk_pure) hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc) (by sep_focus) ?_
  have hAct_split :
      processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
        idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt kyberStorePtr kyberStoreVt =
      ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
      (((coroPtr + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗
       ((coroPtr + 0x400#64) ↦₆₄ kyberStoreVt) ∗
       ((coroPtr + 0x408#64) ↦₆₄ preKeyStorePtr) ∗
       ((coroPtr + 0x410#64) ↦₆₄ preKeyStoreVt) ∗
       ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗
       ((coroPtr + 0x420#64) ↦₆₄ idStoreVt) ∗
       ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗
       ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) ∗
       ((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64))) := by
    unfold processPrekeyActive10At; sep_ac_rfl
  refine SepWPp.weaken_frame (Entails.of_eq hAct_split) (by sep_focus) ?_
  have hstep5 := p2_seg1c_hooks_placed_wp ext hH st1 s4 coroPtr msgPtr (s2.readReg64 .x0)
    spkStorePtr spkKit.spk_vt (0#64 + spkKit.getShimOff) spkId
    hpc4 hrun4 hsp4_align hx19_4 hx21_4 hx22_4 hx24_4 hx26_4
  rw [hsp4] at hstep5
  refine p2_bind_sepWP_qp_frame_state_placed hCode4 hstep5 (by sep_focus)
    fun s5 _ hpc5 hrun5 hCode5 hregs5 => ?_
  rcases hregs5 with ⟨hsp5, htr5, hx0_5, hx1_5, hx19_5, _, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5,
    hx27_5, hx28_5, hx29_5, hx30_5, hvregs5_4⟩
  have hsp5_al : s5.spAligned = true := by simpa only [State.spAligned, hsp5] using hsp_align
  refine SepWPp.weaken_frame (Entails.of_eq hAct_split.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (sp3e0_9_entails_memRegion s.sp 0#64 0#8) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc.symm) (by sep_focus) ?_
  have hstk_shim' := p2_stackAt_split_of_le s.sp stk spkKit.getShimStack hstk_shim hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_shim') (by sep_focus) ?_
  sep_norm
  have htr5_eq : s5.trace = s.trace := by rw [htr5, htr4, htr3, htr2, htr1]
  have hx1_5_32 : s5.readReg32 .x1 = spkId := by
    change (s5.readReg64 .x1).setWidth 32 = spkId
    rw [hx1_5, p2_zext64_trunc32_id]
  refine p2_call_rocl_nopanic_steps_frame_placed
    (x := (({ self := spkStorePtr, id := spkId } : PreKeyShimCall), st2))
    hCode5 (hspkOk.getShim (by decide)) hpc5 hrun5 hsp5_al hx30_5
    (hsp5 ▸ p2_spkGetShim_pre_intro_placed hx0_5 hx1_5_32 hfits_shim)
    (by sep_focus)
    (hnext := fun sf _ hpcf hrunf hspf_5 _ hcsf hCodef => ?_)
  dsimp only [kitSpkGetShimSpec]
  rcases hcsf with ⟨hcsf_19, _, _, hcsf_22, hcsf_23, hcsf_24, hcsf_25, hcsf_26, hcsf_27, hcsf_28,
    hcsf_29, hvregsf_5⟩
  rw [hsp5]
  sep_norm
  refine SepWPp.exists_elim fun evs =>
    SepWPp.pure_elim fun ⟨hx1_f, hfut_nz, hfut_al, htrf_5, hevs_box⟩ => ?_
  have hevs_eq : evs = boxAllocEvents spkKit.getBoxSize :=
    (boxAllocEnv_iff_eq spkKit.getBoxSize evs).mp hevs_box
  have hpool_eq : M.stepEvents evs st2 = M.stepEvents (p2Sub1Events spkKit.getBoxSize) st := by
    rw [hevs_eq]
    exact stepEvents_p2Sub1Events M spkKit.getBoxSize st
  rw [hpool_eq]
  refine SepWPp.weaken_frame (Entails.of_eq hstk_shim'.symm) (by sep_focus) ?_
  have hvregs_full : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
    rw [hvregsf_5, hvregs5_4, hvregs4_3, hvregs3_2, hvregs2_1, hvregs1, hvregs]
  refine SepWPp.done hpcf hrunf ⟨?_, hspf_5.trans hsp5, htrf_5.trans htr5_eq,
    hcsf_19.trans hx19_5, hcsf_22.trans hx22_5, hcsf_23.trans hx23_5,
    hcsf_24.trans hx24_5, hcsf_25.trans hx25_5, hcsf_26.trans hx26_5,
    hcsf_27.trans (hx27_5.trans hx27_4), hcsf_28.trans (hx28_5.trans hx28_4),
    hcsf_29.trans (hx29_5.trans hx29_4), hvregs_full, hCodef⟩
  refine Entails.sepExists_right (sf.readReg64 .x0) ?_
  rw [← sepConj_assoc]
  refine Entails.pure_right ⟨rfl, hx1_f, hfut_nz, hfut_al⟩ ?_
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

abbrev stageP2_sub1_kits_4k_placed := @stageP2_sub1_kits_ext_placed
abbrev stageP2_sub1_kits_hooks_placed := @stageP2_sub1_kits_ext_placed

theorem stageP2_sub1_kits_placed [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2PureCalleesPlacedOfEnv P A lim F BobV1Env AcceptErrEnv ext)
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64)
    (spkEnv : SignedPreKeyStoreBudgetEnv spkKit)
    (hspkOk : SignedPreKeyStoreKitPlacedOk A lim spkKit spkEnv ext)
    (stk : Nat)
    (hstk_pure : stageP2PureAndErrStack ≤ stk)
    (hstk_shim : spkKit.getShimStack ≤ stk)
    (hstk_lt : stk ≤ 2 ^ 64)
    (st : M.σ)
    (s0 s : State)
    (coroPtr msgPtr remoteAddrPtr localAddrPtr
     idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
     spkStorePtr kyberStorePtr kyberStoreVt : BitVec 64)
    (baseKey : PublicKey) (spkId : BitVec 32) (b_4f1 : BitVec 8)
    (hfits : FitsEnv M lim st (P2Sub1Env spkKit.getBoxSize))
    (hCode : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = stageP1EntryPlaced + 0x868#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx8 : s.readReg64 .x8 = kyberStorePtr) (hx9 : s.readReg64 .x9 = msgPtr)
    (hx10 : s.readReg64 .x10 = kyberStoreVt) (hx11 : s.readReg64 .x11 = preKeyStorePtr)
    (hx12 : s.readReg64 .x12 = remoteAddrPtr) (hx13 : s.readReg64 .x13 = preKeyStoreVt)
    (hx14 : s.readReg64 .x14 = localAddrPtr) (hx15 : s.readReg64 .x15 = idStorePtr)
    (hx16 : s.readReg64 .x16 = idStoreVt) (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = spkStorePtr) (hx23 : s.readReg64 .x23 = coroPtr + 0xe0#64)
    (hx24 : s.readReg64 .x24 = spkKit.spk_vt) :
    SepWPp (stageP1ProgPlaced ext) (stageP1EntryPlaced + 0xf14#64) s
      (cells (coroPtr + 0x3f8#64) 6 ∗ cells (coroPtr + 0x468#64) 4 ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗ sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗
       ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗ ((msgPtr + 0xec#64) ↦₃₂ spkId) ∗
       ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗ memRegion (s.sp + 0x3e0#64) 9 ∗
       ((spkKit.spk_vt + 0x18#64) ↦₆₄ᵣ (0#64 + spkKit.getShimOff)) ∗
       A.pool lim st s ∗ stackAt s.sp stk)
      (fun sf P_f =>
        (P_f ⊢
          ∃∗ spkFutPtr : BitVec 64,
            ⌜sf.readReg64 .x0 = spkFutPtr ∧
              sf.readReg64 .x1 = 0#64 + spkKit.getFutVtOff ∧
              spkFutPtr ≠ 0#64 ∧ spkFutPtr.toNat % 8 = 0⌝ ∗
            processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
              idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt kyberStorePtr kyberStoreVt ∗
            ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗
            ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗ ((msgPtr + 0xec#64) ↦₃₂ spkId) ∗
            ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗ memRegion (s.sp + 0x3e0#64) 9 ∗
            ((spkKit.spk_vt + 0x18#64) ↦₆₄ᵣ (0#64 + spkKit.getShimOff)) ∗
            A.live spkFutPtr spkKit.getBoxSize 8 ∗
            spkKit.getBoxAt spkFutPtr spkStorePtr spkId 0#8 ∗
            A.pool lim (M.stepEvents (p2Sub1Events spkKit.getBoxSize) st) sf ∗
            stackAt s.sp stk) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧ sf.readReg64 .x19 = coroPtr ∧
        sf.readReg64 .x22 = spkStorePtr ∧ sf.readReg64 .x23 = 0#64 ∧
        sf.readReg64 .x24 = spkKit.spk_vt ∧ sf.readReg64 .x25 = s.sp + 0x210#64 ∧
        sf.readReg64 .x26 = 33#64 ∧ sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem)
      Qp :=
  stageP2_sub1_kits_ext_placed ext hH hPure.to_4K spkKit spkEnv hspkOk
    stk hstk_pure hstk_shim hstk_lt st s0 s coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt spkStorePtr kyberStorePtr kyberStoreVt
    baseKey spkId b_4f1 hfits hCode hpc hrun hsp_align hvregs
    hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1PlacedBudget
