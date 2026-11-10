/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.CodecCalleesFsTransferCoreFd
import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget
import ProofLib.CoreLemmas
import ProofLib.Hoare.SubroutineOk
import ProofLib.Invariant
import ProofLib.SepLogic.WP.StepsProcess

/-!
# Stage-B Trajectory Simulation and Pure-`fs` Transfer for `lsProg_579` Codec Callees

Combines the Stage-A trap run (`codecTrapHooks`) and the Stage-B execute-bit-stripped shadow
trajectory (`codecShadowHooks`) from `CodecCalleesFsTransferCoreFd` to prove
`codec_pure_fs_transfer_at_579` (`sf.fs = s0.fs` on normal return).
-/

public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.CodecCalleesFsTransferPlacedBudgetFd

open Arm64 ProofLib SepProp
open CryptoVerification
  (LibsignalCodeLoaded LibsignalHooks LibsignalPlacement blkPl_111 libsignalMutatedBlocks
   libsignalSessionLib lsHandleErrorSym lsmpl)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (LibsignalCodeRoLoaded extract_withLsCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet
  (TryFromGhost framelessMemcpySpec memcpyName noAllocShimSpec smallRootStack)
open CryptoVerification.LibsignalTripleRatchet.Prost (lsHandleAllocErrorSym)
open CryptoVerification.LibsignalTripleRatchet.Wire (tryFromPlacedImg)
open CryptoVerification.SignalSession
  (CliHooks cliExternsPlaced lsRustAllocSymCli lsRustDeallocSymCli
   lsRustNoAllocShimSymCli lsRustReallocSymCli)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose (PksmGhost RunSem)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks cliGhostExterns cliGhostExterns_memcpy_some)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget (hookOk_withVmPreserved)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv MallocngCostModelIface
   MallocngCostModelSound RustCliAllocBudget rustCliAllocBudgetSpec
   rustCliDeallocBudgetSpec rustCliReallocBudgetSpec)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase
  (CodeBlocksPermRX codeBlocksPermRX_of_keepsFrozen mallocngHookRustCliAllocBudget)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget (CodecHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.HopSpecsPlacedBudgetFd
  (pksmSlotSpecPlacedOkFs tryFromPlacedSpecOkFs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.CodecCalleesFsPlacedBudgetFd
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.CodecCalleesFsShadowHooksFd
  (hookOk_hookMemcpy_frameless_vm shadowFallback)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.CodecCalleesFsTransferCoreFd
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromPlacedBudget
  (SubsetA4PksmTryFromPlaced pksmSlotSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks codecHooksPlaced_of_hooks)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromBudgetAux
  (TryFromEnvGen tryFromPlacedSpecGen)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBudget (TryFromPostEnv)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromRootBudget (tryFromPlacedSpec)

/-! ## Section 1: `lsProg_579` Stripped CodeLoaded, Entry Tables, & Shadow Trajectory Contradiction -/

private theorem step_running {P : Program} {u v : State} (h : Step P u v) : u.status = .Running := by
  cases h <;> assumption

private theorem lsProg_579_codeLoaded_stripCodec [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {m : Memory} (H : LibsignalHooks)
    (hkeep : ∀ a, inLsUnmutByte a = true → keep a = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl m) :
    (lsProg_579 H).CodeLoaded (stripCodecMem keep m) := by
  have hcl := lscl_stripCodec_of_keep_unmut hkeep hcrl
  rw [CryptoVerification.IsLsBlockProg.eq_blockProgram (prog := lsProg_579 H)]
  exact hcl 579 (by decide) (by decide) H _ _

private def buildEntries (B : Nat) (pred : Nat → Bool) (sh : Nat → State) : List (State × State) :=
  ((List.range B).filter pred).map (fun j => (sh j, sh (j + 1)))

private theorem mem_buildEntries_iff {B : Nat} {pred : Nat → Bool} {sh : Nat → State}
    {p : State × State} :
    p ∈ buildEntries B pred sh ↔ ∃ j, j < B ∧ pred j = true ∧ p = (sh j, sh (j + 1)) := by
  unfold buildEntries
  simp only [List.mem_map, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨j, ⟨hj, hp⟩, rfl⟩; exact ⟨j, hj, hp, rfl⟩
  · rintro ⟨j, hj, hp, rfl⟩; exact ⟨j, ⟨hj, hp⟩, rfl⟩

private theorem nodup_map_of_inj_on {α β : Type} {l : List α} (f : α → β)
    (hnodup : l.Nodup) (hinj : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) :
    (l.map f).Nodup := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons x xs ih =>
    rw [List.nodup_cons] at hnodup
    rw [List.map_cons, List.nodup_cons, List.mem_map]
    refine ⟨?_, ih hnodup.2 (fun a ha b hb =>
      hinj a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))⟩
    rintro ⟨y, hy, hfy⟩
    exact hnodup.1 (hinj y (List.mem_cons_of_mem _ hy) x (List.mem_cons_self ..) hfy ▸ hy)

private theorem buildEntries_fst_nodup {B : Nat} (pred : Nat → Bool) {sh : Nat → State}
    (hdist : ∀ i j, i < j → j < B → sh i ≠ sh j) :
    ((buildEntries B pred sh).map Prod.fst).Nodup := by
  unfold buildEntries
  rw [List.map_map]
  have hcomp : (Prod.fst ∘ fun j => (sh j, sh (j + 1))) = sh := rfl
  rw [hcomp]
  refine nodup_map_of_inj_on sh (List.nodup_range.filter pred) ?_
  intro x hx y hy hxy
  rw [List.mem_filter, List.mem_range] at hx hy
  rcases Nat.lt_trichotomy x y with hlt | heq | hgt
  · exact False.elim (hdist x y hlt hy.1 hxy)
  · exact heq
  · exact False.elim (hdist y x hgt hx.1 hxy.symm)

private inductive StepTag where
  | fixed
  | alloc
  | dealloc
  | realloc
  | memcpy
  deriving DecidableEq

private def ShadowStepSpec [LibsignalPlacement]
    {M : AllocCostModel} (I : MallocngCostModelIface M) (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (memcpyFn : State → State) (keep : BitVec 64 → Bool) (t : StepTag) (u v : State) : Prop :=
  match t with
  | .fixed =>
      ∀ allocE deallocE reallocE memcpyE,
        Step (lsProg_579 (codecShadowHooksMc keep lim mmpl g baseExt memcpyFn
          allocE deallocE reallocE memcpyE)) u v
  | .alloc =>
      u.status = .Running ∧
      (∀ allocE deallocE reallocE memcpyE,
        (lsProg_579 (codecShadowHooksMc keep lim mmpl g baseExt memcpyFn
          allocE deallocE reallocE memcpyE)).externAt? u.pc =
          some (overrideEntries allocE (shadowFallback keep lim mmpl g.alloc))) ∧
      u.mem.KeepsFrozen v.mem ∧ v.symtab = u.symtab ∧
      HookOkAt
        (rustCliAllocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim false)
        u v
  | .dealloc =>
      u.status = .Running ∧
      (∀ allocE deallocE reallocE memcpyE,
        (lsProg_579 (codecShadowHooksMc keep lim mmpl g baseExt memcpyFn
          allocE deallocE reallocE memcpyE)).externAt? u.pc =
          some (overrideEntries deallocE (shadowFallback keep lim mmpl g.dealloc))) ∧
      u.mem.KeepsFrozen v.mem ∧ v.symtab = u.symtab ∧
      HookOkAt
        (rustCliDeallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim)
        u v
  | .realloc =>
      u.status = .Running ∧
      (∀ allocE deallocE reallocE memcpyE,
        (lsProg_579 (codecShadowHooksMc keep lim mmpl g baseExt memcpyFn
          allocE deallocE reallocE memcpyE)).externAt? u.pc =
          some (overrideEntries reallocE (shadowFallback keep lim mmpl g.realloc))) ∧
      u.mem.KeepsFrozen v.mem ∧ v.symtab = u.symtab ∧
      HookOkAt
        (rustCliReallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim)
        u v
  | .memcpy =>
      u.status = .Running ∧
      (∀ allocE deallocE reallocE memcpyE,
        (lsProg_579 (codecShadowHooksMc keep lim mmpl g baseExt memcpyFn
          allocE deallocE reallocE memcpyE)).externAt? u.pc =
          some (overrideEntries memcpyE memcpyFn)) ∧
      u.mem.KeepsFrozen v.mem ∧ v.symtab = u.symtab ∧
      HookOkAt (withVmPreserved framelessMemcpySpec) u v

private theorem contradiction_of_shadow_traj [LibsignalPlacement]
    {M : AllocCostModel} (I : MallocngCostModelIface M) (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (memcpyFn : State → State)
    (hG : CliGhostAllocHooks M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim g)
    (hMcOk : HookOk memcpyFn (withVmPreserved framelessMemcpySpec))
    {entry : BitVec 64} {β : Type} {specF : RustCliAllocBudget M → Spec β}
    (hCallee : ∀ {A' : RustCliAllocBudget M} {H' : LibsignalHooks},
      CodecHooksPlaced M A' lim H' → subroutine_ok (lsProg_579 H') entry (specF A'))
    (hPanic : ∀ A' x s0 sf, (specF A').onPanic x s0 sf = ⌜False⌝)
    (hExit : ∀ A' x code s0 sf, (specF A').onExit x code s0 sf = ⌜False⌝)
    {keep : BitVec 64 → Bool} {K : Nat} {sh : Nat → State} {tag : Nat → StepTag}
    {x : β} {R : SepProp}
    (hpc0 : (sh 0).pc = entry)
    (hrun0 : (sh 0).status = .Running)
    (hsp0 : (sh 0).spAligned = true)
    (hpre0 : (sh 0).mem ⊨
      (specF (strippedMallocngBudget keep M I hS γ mmpl tp brkStart)).pre x (sh 0) ∗ R)
    (hL0 : ∀ H', (lsProg_579 H').CodeLoaded (sh 0).mem)
    (hStepSpec : ∀ j < K,
      ShadowStepSpec I hS γ mmpl tp brkStart lim g baseExt memcpyFn keep (tag j) (sh j) (sh (j + 1)))
    (hHaltK : ∀ allocE deallocE reallocE memcpyE,
      Step (lsProg_579 (codecShadowHooksMc keep lim mmpl g baseExt memcpyFn
        allocE deallocE reallocE memcpyE))
        (sh K) ((sh K).setStatus .Halted))
    (hNoGoal : ∀ m ≤ K, ¬ SubroutineOutcome
      (specF (strippedMallocngBudget keep M I hS γ mmpl tp brkStart)) x R (sh 0) (sh m)) :
    False := by
  let A_sh := strippedMallocngBudget keep M I hS γ mmpl tp brkStart
  have runB : ∀ (B : Nat), B ≤ K → (∀ i j, i < j → j < B → sh i ≠ sh j) →
      let allocE := buildEntries B (fun j => tag j == .alloc) sh
      let deallocE := buildEntries B (fun j => tag j == .dealloc) sh
      let reallocE := buildEntries B (fun j => tag j == .realloc) sh
      let memcpyE := buildEntries B (fun j => tag j == .memcpy) sh
      let P_sh := lsProg_579 (codecShadowHooksMc keep lim mmpl g baseExt memcpyFn
        allocE deallocE reallocE memcpyE)
      (∃ uf', Steps P_sh (sh 0) uf' ∧ SubroutineOutcome (specF A_sh) x R (sh 0) uf' ∧
        uf'.status ≠ .Halted) ∧
      (∀ j < B, Step P_sh (sh j) (sh (j + 1))) := by
    intro B hBK hdist
    let allocE := buildEntries B (fun j => tag j == .alloc) sh
    let deallocE := buildEntries B (fun j => tag j == .dealloc) sh
    let reallocE := buildEntries B (fun j => tag j == .realloc) sh
    let memcpyE := buildEntries B (fun j => tag j == .memcpy) sh
    let H_sh := codecShadowHooksMc keep lim mmpl g baseExt memcpyFn allocE deallocE reallocE memcpyE
    let P_sh := lsProg_579 H_sh
    have hAllocE : ∀ p ∈ allocE, HookOkAt (rustCliAllocBudgetSpec M A_sh lim false) p.1 p.2 := by
      intro p hp
      obtain ⟨j, hj, hpred, rfl⟩ := mem_buildEntries_iff.mp hp
      have ht : tag j = .alloc := of_decide_eq_true hpred
      have hsp := hStepSpec j (by omega)
      rw [ht] at hsp; exact hsp.2.2.2.2
    have hDeallocE : ∀ p ∈ deallocE, HookOkAt (rustCliDeallocBudgetSpec M A_sh lim) p.1 p.2 := by
      intro p hp
      obtain ⟨j, hj, hpred, rfl⟩ := mem_buildEntries_iff.mp hp
      have ht : tag j = .dealloc := of_decide_eq_true hpred
      have hsp := hStepSpec j (by omega)
      rw [ht] at hsp; exact hsp.2.2.2.2
    have hReallocE : ∀ p ∈ reallocE, HookOkAt (rustCliReallocBudgetSpec M A_sh lim) p.1 p.2 := by
      intro p hp
      obtain ⟨j, hj, hpred, rfl⟩ := mem_buildEntries_iff.mp hp
      have ht : tag j = .realloc := of_decide_eq_true hpred
      have hsp := hStepSpec j (by omega)
      rw [ht] at hsp; exact hsp.2.2.2.2
    have hMemcpyE : ∀ p ∈ memcpyE, HookOkAt (withVmPreserved framelessMemcpySpec) p.1 p.2 := by
      intro p hp
      obtain ⟨j, hj, hpred, rfl⟩ := mem_buildEntries_iff.mp hp
      have ht : tag j = .memcpy := of_decide_eq_true hpred
      have hsp := hStepSpec j (by omega)
      rw [ht] at hsp; exact hsp.2.2.2.2
    have hC_sh := codecHooksPlaced_shadow_mc I hS γ mmpl tp brkStart lim g baseExt memcpyFn keep hG
      hMcOk hAllocE hDeallocE hReallocE hMemcpyE
    have hrpc := subroutine_ok_apply_full (hCallee hC_sh) x R hpc0 hrun0 hpre0
      (h_sp_align := hsp0)
      (h_no_panic := fun sf _ hp => by rw [hPanic] at hp; exact not_satisfies_false_sepConj hp)
      (h_no_exit := fun code sf _ he => by rw [hExit] at he; exact not_satisfies_false_sepConj he)
      (h_oom := fun _ _ ho => ho)
    obtain ⟨uf', hsteps_uf', hpost_uf'⟩ := hrpc (hL0 H_sh)
    have hout_nhalt : SubroutineOutcome (specF A_sh) x R (sh 0) uf' ∧ uf'.status ≠ .Halted := by
      rcases hpost_uf' with ⟨hpc_u, hrun_u, hq_u, hcc_u⟩ | ⟨hoom_u, hq_u⟩
      · exact ⟨Or.inl ⟨⟨hpc_u, hcc_u.1, hrun_u⟩, hcc_u, hq_u⟩, by rw [hrun_u]; nofun⟩
      · exact ⟨Or.inr (Or.inr (Or.inr ⟨hoom_u, hq_u⟩)), by rw [hoom_u]; nofun⟩
    refine ⟨⟨uf', hsteps_uf', hout_nhalt.1, hout_nhalt.2⟩, fun j hj => ?_⟩
    have hsp := hStepSpec j (by omega)
    cases ht : tag j <;> rw [ht] at hsp
    · exact hsp allocE deallocE reallocE memcpyE
    · obtain ⟨hr_j, hext_j, hkf_j, hsym_j, _⟩ := hsp
      have hmem : (sh j, sh (j + 1)) ∈ allocE :=
        mem_buildEntries_iff.mpr ⟨j, hj, by simp [ht], rfl⟩
      have hov := overrideEntries_eq_of_nodup (buildEntries_fst_nodup _ hdist)
        (shadowFallback keep lim mmpl g.alloc) hmem
      exact hov ▸ Step.extern hr_j (hext_j allocE deallocE reallocE memcpyE)
        (hov.symm ▸ hkf_j) (hov.symm ▸ hsym_j)
    · obtain ⟨hr_j, hext_j, hkf_j, hsym_j, _⟩ := hsp
      have hmem : (sh j, sh (j + 1)) ∈ deallocE :=
        mem_buildEntries_iff.mpr ⟨j, hj, by simp [ht], rfl⟩
      have hov := overrideEntries_eq_of_nodup (buildEntries_fst_nodup _ hdist)
        (shadowFallback keep lim mmpl g.dealloc) hmem
      exact hov ▸ Step.extern hr_j (hext_j allocE deallocE reallocE memcpyE)
        (hov.symm ▸ hkf_j) (hov.symm ▸ hsym_j)
    · obtain ⟨hr_j, hext_j, hkf_j, hsym_j, _⟩ := hsp
      have hmem : (sh j, sh (j + 1)) ∈ reallocE :=
        mem_buildEntries_iff.mpr ⟨j, hj, by simp [ht], rfl⟩
      have hov := overrideEntries_eq_of_nodup (buildEntries_fst_nodup _ hdist)
        (shadowFallback keep lim mmpl g.realloc) hmem
      exact hov ▸ Step.extern hr_j (hext_j allocE deallocE reallocE memcpyE)
        (hov.symm ▸ hkf_j) (hov.symm ▸ hsym_j)
    · obtain ⟨hr_j, hext_j, hkf_j, hsym_j, _⟩ := hsp
      have hmem : (sh j, sh (j + 1)) ∈ memcpyE :=
        mem_buildEntries_iff.mpr ⟨j, hj, by simp [ht], rfl⟩
      have hov := overrideEntries_eq_of_nodup (buildEntries_fst_nodup _ hdist) memcpyFn hmem
      exact hov ▸ Step.extern hr_j (hext_j allocE deallocE reallocE memcpyE)
        (hov.symm ▸ hkf_j) (hov.symm ▸ hsym_j)
  by_cases hRep : ∃ b, b ≤ K ∧ ∃ a < b, sh a = sh b
  · let decRep : DecidablePred (fun b => b ≤ K ∧ ∃ a < b, sh a = sh b) := Classical.decPred _
    let b₀ := @Nat.find _ decRep hRep
    obtain ⟨hb₀_le, a₀, ha₀_lt, hloop⟩ := @Nat.find_spec _ decRep hRep
    have hdist : ∀ i j, i < j → j < b₀ → sh i ≠ sh j := by
      intro i j hij hjb heq
      exact @Nat.find_min _ decRep hRep _ hjb ⟨by omega, i, hij, heq⟩
    obtain ⟨⟨uf', hsteps_uf', hout_uf', _⟩, hStepB⟩ := runB b₀ hb₀_le hdist
    obtain ⟨m, hm_lt, rfl⟩ := steps_on_lasso ha₀_lt hStepB hloop hsteps_uf'
    exact hNoGoal m (by omega) hout_uf'
  · have hdist : ∀ i j, i < j → j < K → sh i ≠ sh j := by
      intro i j hij hjK heq
      exact hRep ⟨j, by omega, i, hij, heq⟩
    obtain ⟨⟨uf', hsteps_uf', hout_uf', hnhalt⟩, hStepB⟩ := runB K (Nat.le_refl K) hdist
    rcases steps_on_halt_chain hStepB (hHaltK _ _ _ _) hsteps_uf' with ⟨m, hm, rfl⟩ | heq_halt
    · exact hNoGoal m hm hout_uf'
    · exact hnhalt (by rw [heq_halt]; rfl)

/-! ## Section 2: General Two-Stage Pure-`fs` Transfer Theorem (`codec_pure_fs_transfer_at_579`) -/

private def firstStubSym (H : LibsignalHooks) (off : Nat) : List (String × Nat) → Option String
  | [] => none
  | (n, o) :: tl => if (o == off) && (H n).isSome then some n else firstStubSym H off tl

private theorem findSome_eq_firstStubSym (H : LibsignalHooks) (off : Nat) :
    ∀ (stubs : List (String × Nat)),
      (stubs.findSome? fun (n, o) => if o == off then H n else none) =
        match firstStubSym H off stubs with
        | some sym => H sym
        | none => none
  | [] => rfl
  | (n, o) :: tl => by
    dsimp only [List.findSome?, firstStubSym]
    cases ho : o == off <;> cases hh : H n <;>
      simp only [Bool.false_and, Bool.true_and, Option.isSome, ↓reduceIte]
    · exact findSome_eq_firstStubSym H off tl
    · exact findSome_eq_firstStubSym H off tl
    · exact findSome_eq_firstStubSym H off tl
    · exact hh.symm

private theorem firstStubSym_congr {H₁ H₂ : LibsignalHooks}
    (hdom : ∀ sym, (H₁ sym).isSome = (H₂ sym).isSome) (off : Nat) :
    ∀ (stubs : List (String × Nat)), firstStubSym H₁ off stubs = firstStubSym H₂ off stubs
  | [] => rfl
  | (n, _) :: tl => by
    simp only [firstStubSym, hdom n, firstStubSym_congr hdom off tl]

private theorem findSome_stub_some_uniform {H₁ : LibsignalHooks} (off : Nat) {f : State → State}
    (stubs : List (String × Nat))
    (h : (stubs.findSome? fun (n, o) => if o == off then H₁ n else none) = some f) :
    ∃ sym, H₁ sym = some f ∧
      ∀ (H₂ : LibsignalHooks), (∀ s, (H₁ s).isSome = (H₂ s).isSome) →
        (stubs.findSome? fun (n, o) => if o == off then H₂ n else none) = H₂ sym := by
  rw [findSome_eq_firstStubSym H₁ off stubs] at h
  cases hfs : firstStubSym H₁ off stubs with
  | none => rw [hfs] at h; cases h
  | some sym =>
    rw [hfs] at h
    refine ⟨sym, h, fun H₂ hdom => ?_⟩
    rw [findSome_eq_firstStubSym H₂ off stubs, ← firstStubSym_congr hdom off stubs, hfs]

private theorem lsProg_579_externAt?_some_uniform [LibsignalPlacement]
    {H₁ : LibsignalHooks} {pc : BitVec 64} {f : State → State}
    (h : (lsProg_579 H₁).externAt? pc = some f) :
    ∃ sym, H₁ sym = some f ∧
      ∀ (H₂ : LibsignalHooks), (∀ s, (H₁ s).isSome = (H₂ s).isSome) →
        (lsProg_579 H₂).externAt? pc = H₂ sym := by
  unfold Program.externAt? at h
  rw [lsProg_579_hookAtOff?_eq H₁] at h
  obtain ⟨sym, h1, h2⟩ := findSome_stub_some_uniform _ _ h
  refine ⟨sym, h1, fun H₂ hdom => ?_⟩
  unfold Program.externAt?
  rw [lsProg_579_base_indep H₂ H₁, lsProg_579_hookAtOff?_eq H₂]
  exact h2 H₂ hdom

private theorem classify_step_before_K [LibsignalPlacement]
    {M : AllocCostModel} (I : MallocngCostModelIface M) (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (memcpyFn : State → State)
    (hG : CliGhostAllocHooks M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim g)
    (hMcOk : HookOk memcpyFn (withVmPreserved framelessMemcpySpec))
    (hMcSkf : MemcpyStripKeepsFrozen memcpyFn)
    {a_bad : BitVec 64} (hb_bad : inLsUnmutByte a_bad = false)
    {u v : State}
    (hst : Step (lsProg_579 (codecTrapHooksMc
      (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim g baseExt memcpyFn)) u v)
    (hv_run : v.status = .Running)
    (hcrl : LibsignalCodeRoLoaded lsmpl u.mem)
    (hrx : lim.enforced = true → CodeBlocksPermRX mmpl u)
    (hin_code : (lsProg_579 (codecTrapHooksMc
      (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim g baseExt memcpyFn)).externAt?
        u.pc = none → inLsUnmutCode4 u.pc = true) :
    let keep1 : BitVec 64 → Bool := fun a => decide (a ≠ a_bad)
    ∃ t : StepTag,
      (((stripCodecMem keep1 u.mem).KeepsFrozen (stripCodecMem keep1 v.mem) →
          ShadowStepSpec I hS γ mmpl tp brkStart lim g baseExt memcpyFn keep1 t
            (stripCodecS keep1 u) (stripCodecS keep1 v)) ∧
       (∀ {v' : State}, OutMallocng keep1 mmpl lim →
          (v' = v ∨ (¬ (stripCodecMem keep1 u.mem).KeepsFrozen (stripCodecMem keep1 v.mem) ∧
            v' = stripCodecS keep1 v)) →
          u.mem.KeepsFrozen v'.mem →
          ShadowStepSpec I hS γ mmpl tp brkStart lim g baseExt memcpyFn keep1 t u v')) := by
  let A0 := mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart
  let keep1 : BitVec 64 → Bool := fun a => decide (a ≠ a_bad)
  have hkeep_byte : ∀ a, inLsUnmutByte a = true → keep1 a = true := by
    intro a ha; apply decide_eq_true; intro heq; subst heq; rw [ha] at hb_bad; cases hb_bad
  cases hst with
  | halt_unmapped _ _ _ => cases hv_run
  | extern_fault _ _ _ => simp at hv_run
  | @exec inst hrun hfm =>
    have hfm0 := hfm
    unfold Program.fetchMem at hfm
    cases heg : (lsProg_579 (codecTrapHooksMc A0 lim g baseExt memcpyFn)).externAt? u.pc with
    | some f => rw [heg] at hfm; cases hfm
    | none =>
      rw [heg] at hfm
      have hin4 : inLsUnmutCode4 u.pc = true := hin_code heg
      have hnsvc0 : inst.isSvc0 = false := fetchMem_not_isSvc0_of_inLsUnmutCode4 hcrl hin4 hfm0
      have hev_t :
          (lsProg_579 (codecTrapHooksMc A0 lim g baseExt memcpyFn)).evalInst inst u =
            execInst inst u :=
        evalInst_eq_execInst_local _ hnsvc0 u
      rw [hev_t] at hv_run ⊢
      have hnoex : ∀ msg, (execInst inst u).status ≠ .Exception msg := by
        intro msg hex; rw [hex] at hv_run; cases hv_run
      have hin4' := hin4
      unfold inLsUnmutCode4 at hin4'
      simp only [Bool.and_eq_true] at hin4'
      obtain ⟨⟨⟨hb0, hb1⟩, hb2⟩, hb3⟩ := hin4'
      have hstep_sh_stripped : ∀ allocE deallocE reallocE memcpyE,
          Step (lsProg_579 (codecShadowHooksMc keep1 lim mmpl g baseExt memcpyFn
            allocE deallocE reallocE memcpyE))
            (stripCodecS keep1 u) (stripCodecS keep1 (execInst inst u)) := by
        intro allocE deallocE reallocE memcpyE
        let P_sh := lsProg_579 (codecShadowHooksMc keep1 lim mmpl g baseExt memcpyFn
          allocE deallocE reallocE memcpyE)
        have hdom := fun sym =>
          (codecShadowHooksMc_isSome_eq A0 keep1 lim mmpl g baseExt memcpyFn
            allocE deallocE reallocE memcpyE sym).symm
        have hext_sh : P_sh.externAt? u.pc = none := (lsProg_579_externAt?_none_iff hdom u.pc).mp heg
        have hfm_u : P_sh.fetchMem u.mem u.pc = some inst := by
          unfold Program.fetchMem; rw [hext_sh]; exact hfm
        have hfm_sc : P_sh.fetchMem (stripCodecS keep1 u).mem (stripCodecS keep1 u).pc = some inst := by
          change P_sh.fetchMem (stripCodecMem keep1 u.mem) u.pc = some inst
          rw [fetchMem_stripCodec_of_keep4 P_sh (hkeep_byte _ hb0) (hkeep_byte _ hb1)
            (hkeep_byte _ hb2) (hkeep_byte _ hb3)]
          exact hfm_u
        have hrun_sc : (stripCodecS keep1 u).status = .Running := hrun
        have hev_sh : P_sh.evalInst inst (stripCodecS keep1 u) = stripCodecS keep1 (execInst inst u) :=
          (evalInst_eq_execInst_local P_sh hnsvc0 _).trans
            (execInst_stripCodec_of_noException hnsvc0 keep1 u hnoex)
        exact hev_sh ▸ Step.exec hrun_sc hfm_sc
      have hstep_sh_unstripped : ∀ allocE deallocE reallocE memcpyE,
          Step (lsProg_579 (codecShadowHooksMc keep1 lim mmpl g baseExt memcpyFn
            allocE deallocE reallocE memcpyE))
            u (execInst inst u) := by
        intro allocE deallocE reallocE memcpyE
        let P_sh := lsProg_579 (codecShadowHooksMc keep1 lim mmpl g baseExt memcpyFn
          allocE deallocE reallocE memcpyE)
        have hdom := fun sym =>
          (codecShadowHooksMc_isSome_eq A0 keep1 lim mmpl g baseExt memcpyFn
            allocE deallocE reallocE memcpyE sym).symm
        have hext_sh : P_sh.externAt? u.pc = none := (lsProg_579_externAt?_none_iff hdom u.pc).mp heg
        have hfm_u : P_sh.fetchMem u.mem u.pc = some inst := by
          unfold Program.fetchMem; rw [hext_sh]; exact hfm
        exact (evalInst_eq_execInst_local P_sh hnsvc0 u) ▸ Step.exec hrun hfm_u
      refine ⟨.fixed, fun _ => hstep_sh_stripped, fun _ hv' _ => ?_⟩
      rcases hv' with rfl | ⟨hbad, _⟩
      · exact hstep_sh_unstripped
      · exact False.elim (hbad (hstep_sh_stripped [] [] [] []).keepsFrozen)
  | @extern f hrun heg hkf hsym =>
    obtain ⟨sym, htrap_sym, hunif⟩ := lsProg_579_externAt?_some_uniform heg
    have hext_any : ∀ allocE deallocE reallocE memcpyE,
        (lsProg_579 (codecShadowHooksMc keep1 lim mmpl g baseExt memcpyFn
          allocE deallocE reallocE memcpyE)).externAt? u.pc =
          codecShadowHooksMc keep1 lim mmpl g baseExt memcpyFn
            allocE deallocE reallocE memcpyE sym :=
      fun allocE deallocE reallocE memcpyE =>
        hunif _ (fun s =>
          (codecShadowHooksMc_isSome_eq A0 keep1 lim mmpl g baseExt memcpyFn
            allocE deallocE reallocE memcpyE s).symm)
    unfold codecTrapHooksMc at htrap_sym
    split_ifs at htrap_sym with h1 h2 h3 h4 h5 h6 h7
    · subst h1; injection htrap_sym with hf; subst hf
      have hmem_eq : (ProofLib.hookNoop u).mem = u.mem := rfl
      have hkf_noop : (stripCodecMem keep1 u.mem).KeepsFrozen
          (stripCodecMem keep1 (ProofLib.hookNoop u).mem) := by
        rw [hmem_eq]; exact fun _ _ => ⟨rfl, rfl, rfl, rfl⟩
      have hsh_sym : ∀ allocE deallocE reallocE memcpyE,
          codecShadowHooksMc keep1 lim mmpl g baseExt memcpyFn
            allocE deallocE reallocE memcpyE lsRustNoAllocShimSymCli =
            some ProofLib.hookNoop := by
        intro allocE deallocE reallocE memcpyE; simp [codecShadowHooksMc]
      refine ⟨.fixed, ?_, ?_⟩
      · intro _ allocE deallocE reallocE memcpyE
        have hext_sc :
            (lsProg_579 (codecShadowHooksMc keep1 lim mmpl g baseExt memcpyFn
              allocE deallocE reallocE memcpyE)).externAt?
              (stripCodecS keep1 u).pc = some ProofLib.hookNoop :=
          (hext_any allocE deallocE reallocE memcpyE).trans
            (hsh_sym allocE deallocE reallocE memcpyE)
        have hstep := Step.extern (s := stripCodecS keep1 u) hrun hext_sc
          (fun _ _ => ⟨rfl, rfl, rfl, rfl⟩) rfl
        rwa [hookNoop_stripCodec] at hstep
      · intro v' _ hv' _
        rcases hv' with rfl | ⟨hbad, _⟩
        · intro allocE deallocE reallocE memcpyE
          exact Step.extern hrun
            ((hext_any allocE deallocE reallocE memcpyE).trans
              (hsh_sym allocE deallocE reallocE memcpyE))
            hkf hsym
        · exact False.elim (hbad hkf_noop)
    · subst h2; injection htrap_sym with hf; subst hf
      have hact : ActivePre (rustCliAllocBudgetSpec M A0 lim false) u := by
        by_contra hnact
        unfold guardPre at hv_run
        split at hv_run
        · exact hnact ‹_›
        · cases hv_run
      have hgeq : guardPre (rustCliAllocBudgetSpec M A0 lim false) g.alloc u = g.alloc u := by
        unfold guardPre; simp only [hact, ↓reduceIte]
      change (guardPre (rustCliAllocBudgetSpec M A0 lim false) g.alloc u).status = .Running at hv_run
      change u.mem.KeepsFrozen (guardPre (rustCliAllocBudgetSpec M A0 lim false) g.alloc u).mem at hkf
      change (guardPre (rustCliAllocBudgetSpec M A0 lim false) g.alloc u).symtab = u.symtab at hsym
      rw [hgeq] at hv_run hkf hsym ⊢
      have hsh_sym : ∀ allocE deallocE reallocE memcpyE,
          codecShadowHooksMc keep1 lim mmpl g baseExt memcpyFn
            allocE deallocE reallocE memcpyE lsRustAllocSymCli =
            some (overrideEntries allocE (shadowFallback keep1 lim mmpl g.alloc)) := by
        intro allocE deallocE reallocE memcpyE
        simp only [codecShadowHooksMc, (by decide : lsRustAllocSymCli ≠ lsRustNoAllocShimSymCli),
          ↓reduceIte]
      refine ⟨.alloc, ?_, ?_⟩
      · intro hkf_sc
        exact ⟨hrun,
          fun allocE deallocE reallocE memcpyE =>
            (hext_any allocE deallocE reallocE memcpyE).trans
              (hsh_sym allocE deallocE reallocE memcpyE),
          hkf_sc, hsym,
          b1b_alloc_stripped I hS γ mmpl tp brkStart lim g keep1 hG hrx hsym hkf_sc⟩
      · intro v' hOut hv' hkf_v'
        have hv'_or : v' = g.alloc u ∨ v' = stripCodecS keep1 (g.alloc u) := hv'.imp id And.right
        have hsym_v' : v'.symtab = u.symtab := by rcases hv'_or with rfl | rfl <;> exact hsym
        exact ⟨hrun,
          fun allocE deallocE reallocE memcpyE =>
            (hext_any allocE deallocE reallocE memcpyE).trans
              (hsh_sym allocE deallocE reallocE memcpyE),
          hkf_v', hsym_v',
          b1b_alloc_unstripped I hS γ mmpl tp brkStart lim g keep1 hG hOut hv'_or hsym_v' hkf_v'⟩
    · subst h3; injection htrap_sym with hf; subst hf
      have hact : ActivePre (rustCliDeallocBudgetSpec M A0 lim) u := by
        by_contra hnact
        unfold guardPre at hv_run
        split at hv_run
        · exact hnact ‹_›
        · cases hv_run
      have hgeq : guardPre (rustCliDeallocBudgetSpec M A0 lim) g.dealloc u = g.dealloc u := by
        unfold guardPre; simp only [hact, ↓reduceIte]
      change (guardPre (rustCliDeallocBudgetSpec M A0 lim) g.dealloc u).status = .Running at hv_run
      change u.mem.KeepsFrozen (guardPre (rustCliDeallocBudgetSpec M A0 lim) g.dealloc u).mem at hkf
      change (guardPre (rustCliDeallocBudgetSpec M A0 lim) g.dealloc u).symtab = u.symtab at hsym
      rw [hgeq] at hv_run hkf hsym ⊢
      have hsh_sym : ∀ allocE deallocE reallocE memcpyE,
          codecShadowHooksMc keep1 lim mmpl g baseExt memcpyFn
            allocE deallocE reallocE memcpyE lsRustDeallocSymCli =
            some (overrideEntries deallocE (shadowFallback keep1 lim mmpl g.dealloc)) := by
        intro allocE deallocE reallocE memcpyE
        simp only [codecShadowHooksMc, (by decide : lsRustDeallocSymCli ≠ lsRustNoAllocShimSymCli),
          (by decide : lsRustDeallocSymCli ≠ lsRustAllocSymCli), ↓reduceIte]
      refine ⟨.dealloc, ?_, ?_⟩
      · intro hkf_sc
        exact ⟨hrun,
          fun allocE deallocE reallocE memcpyE =>
            (hext_any allocE deallocE reallocE memcpyE).trans
              (hsh_sym allocE deallocE reallocE memcpyE),
          hkf_sc, hsym,
          b1b_dealloc_stripped I hS γ mmpl tp brkStart lim g keep1 hG hrx hsym hkf_sc⟩
      · intro v' hOut hv' hkf_v'
        have hv'_or : v' = g.dealloc u ∨ v' = stripCodecS keep1 (g.dealloc u) := hv'.imp id And.right
        have hsym_v' : v'.symtab = u.symtab := by rcases hv'_or with rfl | rfl <;> exact hsym
        exact ⟨hrun,
          fun allocE deallocE reallocE memcpyE =>
            (hext_any allocE deallocE reallocE memcpyE).trans
              (hsh_sym allocE deallocE reallocE memcpyE),
          hkf_v', hsym_v',
          b1b_dealloc_unstripped I hS γ mmpl tp brkStart lim g keep1 hG hOut hv'_or hsym_v' hkf_v'⟩
    · subst h4; injection htrap_sym with hf; subst hf
      have hact : ActivePre (rustCliReallocBudgetSpec M A0 lim) u := by
        by_contra hnact
        unfold guardPre at hv_run
        split at hv_run
        · exact hnact ‹_›
        · cases hv_run
      have hgeq : guardPre (rustCliReallocBudgetSpec M A0 lim) g.realloc u = g.realloc u := by
        unfold guardPre; simp only [hact, ↓reduceIte]
      change (guardPre (rustCliReallocBudgetSpec M A0 lim) g.realloc u).status = .Running at hv_run
      change u.mem.KeepsFrozen (guardPre (rustCliReallocBudgetSpec M A0 lim) g.realloc u).mem at hkf
      change (guardPre (rustCliReallocBudgetSpec M A0 lim) g.realloc u).symtab = u.symtab at hsym
      rw [hgeq] at hv_run hkf hsym ⊢
      have hsh_sym : ∀ allocE deallocE reallocE memcpyE,
          codecShadowHooksMc keep1 lim mmpl g baseExt memcpyFn
            allocE deallocE reallocE memcpyE lsRustReallocSymCli =
            some (overrideEntries reallocE (shadowFallback keep1 lim mmpl g.realloc)) := by
        intro allocE deallocE reallocE memcpyE
        simp only [codecShadowHooksMc, (by decide : lsRustReallocSymCli ≠ lsRustNoAllocShimSymCli),
          (by decide : lsRustReallocSymCli ≠ lsRustAllocSymCli),
          (by decide : lsRustReallocSymCli ≠ lsRustDeallocSymCli), ↓reduceIte]
      refine ⟨.realloc, ?_, ?_⟩
      · intro hkf_sc
        exact ⟨hrun,
          fun allocE deallocE reallocE memcpyE =>
            (hext_any allocE deallocE reallocE memcpyE).trans
              (hsh_sym allocE deallocE reallocE memcpyE),
          hkf_sc, hsym,
          b1b_realloc_stripped I hS γ mmpl tp brkStart lim g keep1 hG hrx hsym hkf_sc⟩
      · intro v' hOut hv' hkf_v'
        have hv'_or : v' = g.realloc u ∨ v' = stripCodecS keep1 (g.realloc u) := hv'.imp id And.right
        have hsym_v' : v'.symtab = u.symtab := by rcases hv'_or with rfl | rfl <;> exact hsym
        exact ⟨hrun,
          fun allocE deallocE reallocE memcpyE =>
            (hext_any allocE deallocE reallocE memcpyE).trans
              (hsh_sym allocE deallocE reallocE memcpyE),
          hkf_v', hsym_v',
          b1b_realloc_unstripped I hS γ mmpl tp brkStart lim g keep1 hG hOut hv'_or hsym_v' hkf_v'⟩
    · subst h5; injection htrap_sym with hf; subst hf
      have hact : ActivePre (withVmPreserved framelessMemcpySpec) u := by
        by_contra hnact
        unfold guardPre at hv_run
        split at hv_run
        · exact hnact ‹_›
        · cases hv_run
      have hgeq : guardPre (withVmPreserved framelessMemcpySpec) memcpyFn u = memcpyFn u := by
        unfold guardPre; simp only [hact, ↓reduceIte]
      change (guardPre (withVmPreserved framelessMemcpySpec) memcpyFn u).status = .Running at hv_run
      change u.mem.KeepsFrozen (guardPre (withVmPreserved framelessMemcpySpec) memcpyFn u).mem at hkf
      change (guardPre (withVmPreserved framelessMemcpySpec) memcpyFn u).symtab = u.symtab at hsym
      rw [hgeq] at hv_run hkf hsym ⊢
      have hsh_sym : ∀ allocE deallocE reallocE memcpyE,
          codecShadowHooksMc keep1 lim mmpl g baseExt memcpyFn
            allocE deallocE reallocE memcpyE memcpyName =
            some (overrideEntries memcpyE memcpyFn) := by
        intro allocE deallocE reallocE memcpyE
        simp only [codecShadowHooksMc, (by decide : memcpyName ≠ lsRustNoAllocShimSymCli),
          (by decide : memcpyName ≠ lsRustAllocSymCli),
          (by decide : memcpyName ≠ lsRustDeallocSymCli),
          (by decide : memcpyName ≠ lsRustReallocSymCli), ↓reduceIte]
      refine ⟨.memcpy, ?_, ?_⟩
      · intro hkf_sc
        exact ⟨hrun,
          fun allocE deallocE reallocE memcpyE =>
            (hext_any allocE deallocE reallocE memcpyE).trans
              (hsh_sym allocE deallocE reallocE memcpyE),
          hkf_sc, hsym,
          b1b_memcpy_stripped keep1 hMcOk hsym hkf_sc⟩
      · intro v' _ hv' _
        rcases hv' with rfl | ⟨hbad, _⟩
        · exact ⟨hrun,
            fun allocE deallocE reallocE memcpyE =>
              (hext_any allocE deallocE reallocE memcpyE).trans
                (hsh_sym allocE deallocE reallocE memcpyE),
            hkf, hsym,
            b1b_memcpy_unstripped hMcOk u⟩
        · exact False.elim (hbad (hMcSkf keep1 u hact hkf))
    · subst h6; injection htrap_sym with hf; subst hf
      simp [Rust.panicked] at hv_run
    · subst h7; injection htrap_sym with hf; subst hf
      simp [Rust.panicked] at hv_run
    · generalize hother : cliGhostExterns g baseExt sym = res at htrap_sym
      cases res
      · cases htrap_sym
      · injection htrap_sym with hf; subst hf
        simp at hv_run

/-- Ghost-`memcpyFn` / `baseExt`-parametric two-stage pure-`fs` transfer for `lsProg_579`. -/
theorem codec_pure_fs_transfer_at_579_mc [LibsignalPlacement]
    {M : AllocCostModel} (I : MallocngCostModelIface M) (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (memcpyFn : State → State)
    (hG : CliGhostAllocHooks M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim g)
    (hMcRow : cliGhostExterns g baseExt memcpyName = some memcpyFn)
    (hMcOk : HookOk memcpyFn (withVmPreserved framelessMemcpySpec))
    (hMcFs : ∀ u, (memcpyFn u).fs = u.fs)
    (hMcSkf : MemcpyStripKeepsFrozen memcpyFn)
    (hPanAlloc : cliGhostExterns g baseExt lsHandleAllocErrorSym = some Rust.panicked)
    (hPanRaw : cliGhostExterns g baseExt lsHandleErrorSym = some Rust.panicked)
    {entry : BitVec 64} {β : Type} {specF : RustCliAllocBudget M → Spec β}
    (hCallee : ∀ {A' : RustCliAllocBudget M} {H' : LibsignalHooks},
      CodecHooksPlaced M A' lim H' → subroutine_ok (lsProg_579 H') entry (specF A'))
    (hSwap : SpecPoolSwap I hS γ mmpl tp brkStart lim specF)
    (hCrl : ∀ x R (s0 : State),
      (s0.mem ⊨ (specF (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart)).pre x s0 ∗ R) →
      LibsignalCodeRoLoaded lsmpl s0.mem)
    (hRx : ∀ x R (s0 : State),
      (s0.mem ⊨ (specF (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart)).pre x s0 ∗ R) →
      lim.enforced = true → CodeBlocksPermRX mmpl s0)
    (hPanic : ∀ A' x s0 sf, (specF A').onPanic x s0 sf = ⌜False⌝)
    (hExit : ∀ A' x code s0 sf, (specF A').onExit x code s0 sf = ⌜False⌝) :
    let A0 := mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart
    subroutine_ok (lsProg_579 (cliGhostExterns g baseExt)) entry
      { specF A0 with post := fun x s0 sf => ⌜sf.fs = s0.fs⌝ ∗ (specF A0).post x s0 sf } := by
  let A0 := mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart
  let H_real := cliGhostExterns g baseExt
  let P_real := lsProg_579 H_real
  let H_trap := codecTrapHooksMc A0 lim g baseExt memcpyFn
  let P_trap := lsProg_579 H_trap
  refine subroutine_ok_intro fun x R s0 hpc0 hrun0 hpre0 hsp0 hL_real => ?_
  have hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem := hCrl x R s0 hpre0
  have hrx0 : lim.enforced = true → CodeBlocksPermRX mmpl s0 := hRx x R s0 hpre0
  have hL_trap : P_trap.CodeLoaded s0.mem := (lsProg_579_codeLoaded_iff _ _ s0.mem).mp hL_real
  let Goal : State → Prop := fun sf =>
    (sf.pc = s0.readReg64 Reg.lr ∧ sf.status = .Running ∧ SubroutinePost (specF A0) x R s0 sf) ∨
      (sf.status = .OutOfMemory ∧ (sf.mem ⊨ (specF A0).onOom x s0 sf ∗ R))
  have hrpc0 := subroutine_ok_apply_full
    (hCallee (codecHooksPlaced_trap_mc g baseExt memcpyFn hG hMcOk))
    x R hpc0 hrun0 hpre0 (h_sp_align := hsp0)
    (h_no_panic := fun sf _ hp => by rw [hPanic] at hp; exact not_satisfies_false_sepConj hp)
    (h_no_exit := fun code sf _ he => by rw [hExit] at he; exact not_satisfies_false_sepConj he)
    (h_oom := fun _ _ ho => ho)
  obtain ⟨sf_init, hsteps_init, hgoal_init⟩ := hrpc0 hL_trap
  obtain ⟨n_init, hsn_init⟩ := steps_iff_exists_stepsN.mp hsteps_init
  have hExN : ∃ n, ∃ sf, CodecCalleesFsTransferCoreFd.StepsN P_trap n s0 sf ∧ Goal sf :=
    ⟨n_init, sf_init, hsn_init, hgoal_init⟩
  let decExN : DecidablePred
      (fun n => ∃ sf, CodecCalleesFsTransferCoreFd.StepsN P_trap n s0 sf ∧ Goal sf) :=
    Classical.decPred _
  let N := @Nat.find _ decExN hExN
  obtain ⟨sf, hStepsN, hGoal⟩ := @Nat.find_spec _ decExN hExN
  obtain ⟨traj, ht0, htN, hstep, hsp_n⟩ := stepsN_to_traj hStepsN
  have hcrl_at : ∀ j ≤ N, LibsignalCodeRoLoaded lsmpl (traj j).mem := by
    intro j hj
    have hkf_j : s0.mem.KeepsFrozen (traj j).mem := (hsp_n j hj).1.keepsFrozen
    refine ⟨fun i hi hni X O svc => ?_, fun sec hsec hro k hk => ?_⟩
    · have hL := hcrl0.1 i hi hni X O svc
      rw [Program.codeLoaded_iff] at hL ⊢
      obtain ⟨h1, h2, hcode⟩ := hL
      refine ⟨h1, h2, fun off hoff => ?_⟩
      obtain ⟨hr0, hp0, hlf0⟩ := hcode off hoff
      have hfr : s0.mem.Frozen ((libsignalSessionLib.blockProgram lsmpl i X O svc).base +
          BitVec.ofNat 64 off) := by
        unfold Memory.Frozen; rw [hp0]; rfl
      obtain ⟨hr, hp, hlf, _⟩ := hkf_j _ hfr
      exact ⟨hr.trans hr0, hp.trans hp0, hlf.trans hlf0⟩
    · obtain ⟨hr0, hp0, hlf0⟩ := hcrl0.2 sec hsec hro k hk
      have hfr : s0.mem.Frozen (lsmpl.ρ sec.sym + BitVec.ofNat 64 k) := by
        unfold Memory.Frozen; rw [hp0]; rfl
      obtain ⟨hr, hp, hlf, _⟩ := hkf_j _ hfr
      exact ⟨hr.trans hr0, hp.trans hp0, hlf.trans hlf0⟩
  have hrx_at : ∀ j ≤ N, lim.enforced = true → CodeBlocksPermRX mmpl (traj j) :=
    fun j hj henf => codeBlocksPermRX_of_keepsFrozen (hrx0 henf) (hsp_n j hj).1.keepsFrozen
  by_cases hOff : ∃ j, j < N ∧ P_trap.externAt? (traj j).pc = none ∧ inLsUnmutCode4 (traj j).pc = false
  · exfalso
    let decOff : DecidablePred
        (fun j => j < N ∧ P_trap.externAt? (traj j).pc = none ∧ inLsUnmutCode4 (traj j).pc = false) :=
      Classical.decPred _
    let K := @Nat.find _ decOff hOff
    obtain ⟨hK_lt, hK_ext, hK_out⟩ := @Nat.find_spec _ decOff hOff
    have hBeforeK : ∀ j < K, P_trap.externAt? (traj j).pc = none → inLsUnmutCode4 (traj j).pc = true := by
      intro j hjK hext
      cases hin : inLsUnmutCode4 (traj j).pc
      · exact False.elim (@Nat.find_min _ decOff hOff _ hjK ⟨by omega, hext, hin⟩)
      · rfl
    obtain ⟨a_bad, hb_bad, hno_exec_bad⟩ :=
      canExec_stripCodec_false_of_not_inLsUnmutCode4 (traj K).pc hK_out
    let keep1 : BitVec 64 → Bool := fun a => decide (a ≠ a_bad)
    have hkeep_byte : ∀ a, inLsUnmutByte a = true → keep1 a = true := by
      intro a ha; apply decide_eq_true; intro heq; subst heq; rw [ha] at hb_bad; cases hb_bad
    have hkeep_blk : ∀ i, i < 624 → (i ∈ libsignalMutatedBlocks) = false →
        ∀ a, InRegion (lsmpl.base i) (libsignalSessionLib.blockLib i).text.code.length a →
          keep1 a = true := by
      intro i hi hni a hin
      apply hkeep_byte
      unfold inLsUnmutByte
      rw [List.any_eq_true]
      refine ⟨i, List.mem_range.mpr hi, ?_⟩
      rw [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
      exact ⟨by intro hm; simp [hm] at hni, hin⟩
    have hClass : ∀ j (hj : j < K),
        ∃ t : StepTag,
          (((stripCodecMem keep1 (traj j).mem).KeepsFrozen
              (stripCodecMem keep1 (traj (j + 1)).mem) →
              ShadowStepSpec I hS γ mmpl tp brkStart lim g baseExt memcpyFn keep1 t
                (stripCodecS keep1 (traj j)) (stripCodecS keep1 (traj (j + 1)))) ∧
           (∀ {v' : State}, OutMallocng keep1 mmpl lim →
              (v' = traj (j + 1) ∨
                (¬ (stripCodecMem keep1 (traj j).mem).KeepsFrozen
                  (stripCodecMem keep1 (traj (j + 1)).mem) ∧
                  v' = stripCodecS keep1 (traj (j + 1)))) →
              (traj j).mem.KeepsFrozen v'.mem →
              ShadowStepSpec I hS γ mmpl tp brkStart lim g baseExt memcpyFn keep1 t (traj j) v')) :=
      fun j hj => classify_step_before_K I hS γ mmpl tp brkStart lim g baseExt memcpyFn
        hG hMcOk hMcSkf hb_bad (hstep j (by omega)) (step_running (hstep (j + 1) (by omega)))
        (hcrl_at j (by omega)) (hrx_at j (by omega)) (hBeforeK j hj)
    let tag : Nat → StepTag := fun j =>
      if hj : j < K then Classical.choose (hClass j hj) else .fixed
    have htag_spec : ∀ j (hj : j < K),
        (((stripCodecMem keep1 (traj j).mem).KeepsFrozen
            (stripCodecMem keep1 (traj (j + 1)).mem) →
            ShadowStepSpec I hS γ mmpl tp brkStart lim g baseExt memcpyFn keep1 (tag j)
              (stripCodecS keep1 (traj j)) (stripCodecS keep1 (traj (j + 1)))) ∧
         (∀ {v' : State}, OutMallocng keep1 mmpl lim →
            (v' = traj (j + 1) ∨
              (¬ (stripCodecMem keep1 (traj j).mem).KeepsFrozen
                (stripCodecMem keep1 (traj (j + 1)).mem) ∧
                v' = stripCodecS keep1 (traj (j + 1)))) →
            (traj j).mem.KeepsFrozen v'.mem →
            ShadowStepSpec I hS γ mmpl tp brkStart lim g baseExt memcpyFn keep1
              (tag j) (traj j) v')) := by
      intro j hj
      dsimp only [tag]; simp only [hj, ↓reduceDIte]
      exact Classical.choose_spec (hClass j hj)
    have hHalt_scK : ∀ allocE deallocE reallocE memcpyE,
        Step (lsProg_579 (codecShadowHooksMc keep1 lim mmpl g baseExt memcpyFn
          allocE deallocE reallocE memcpyE))
          (stripCodecS keep1 (traj K)) ((stripCodecS keep1 (traj K)).setStatus .Halted) := by
      intro allocE deallocE reallocE memcpyE
      let P_sh := lsProg_579 (codecShadowHooksMc keep1 lim mmpl g baseExt memcpyFn
        allocE deallocE reallocE memcpyE)
      have hdom := fun sym =>
        (codecShadowHooksMc_isSome_eq A0 keep1 lim mmpl g baseExt memcpyFn
          allocE deallocE reallocE memcpyE sym).symm
      have hext_K : P_sh.externAt? (stripCodecS keep1 (traj K)).pc = none :=
        (lsProg_579_externAt?_none_iff hdom (traj K).pc).mp hK_ext
      have hfm_K : P_sh.fetchMem (stripCodecS keep1 (traj K)).mem
          (stripCodecS keep1 (traj K)).pc = none := by
        change P_sh.fetchMem (stripCodecMem keep1 (traj K).mem) (traj K).pc = none
        unfold Program.fetchMem
        rw [hno_exec_bad (traj K).mem]
        simp
      exact Step.halt_unmapped (s := stripCodecS keep1 (traj K))
        ((sc_st keep1 (traj K)).trans (step_running (hstep K hK_lt))) hfm_K hext_K
    have hGoal_of_outcome : ∀ m ≤ K, SubroutineOutcome (specF A0) x R s0 (traj m) → False := by
      intro m hmK hout0
      have hgoal_m : Goal (traj m) := by
        rcases hout0 with ⟨⟨hpc_m, _, hrun_m⟩, hcc_m, hq_m⟩ |
          ⟨_, hp_m⟩ | ⟨code, _, he_m⟩ | ⟨hoom_m, hq_m⟩
        · exact Or.inl ⟨hpc_m, hrun_m, hq_m, hcc_m⟩
        · rw [hPanic] at hp_m; exact False.elim (not_satisfies_false_sepConj hp_m)
        · rw [hExit] at he_m; exact False.elim (not_satisfies_false_sepConj he_m)
        · exact Or.inr ⟨hoom_m, hq_m⟩
      exact @Nat.find_min _ decExN hExN _ (show m < N by omega) ⟨traj m, (hsp_n m (by omega)).1, hgoal_m⟩
    by_cases hBad : ∃ d, d ≤ K ∧ 0 < d ∧
        ¬ (stripCodecMem keep1 (traj (K - d)).mem).KeepsFrozen
            (stripCodecMem keep1 (traj (K - d + 1)).mem)
    · let decBad : DecidablePred (fun d => d ≤ K ∧ 0 < d ∧
          ¬ (stripCodecMem keep1 (traj (K - d)).mem).KeepsFrozen
              (stripCodecMem keep1 (traj (K - d + 1)).mem)) := Classical.decPred _
      let d₀ := @Nat.find _ decBad hBad
      obtain ⟨hd₀_le, hd₀_pos, hbad_d₀⟩ := @Nat.find_spec _ decBad hBad
      let j₁ := K - d₀
      have hj₁_lt : j₁ < K := by omega
      have hbad_j₁ : ¬ (stripCodecMem keep1 (traj j₁).mem).KeepsFrozen
          (stripCodecMem keep1 (traj (j₁ + 1)).mem) := hbad_d₀
      have hgood_after : ∀ j, j₁ < j → j < K →
          (stripCodecMem keep1 (traj j).mem).KeepsFrozen
            (stripCodecMem keep1 (traj (j + 1)).mem) := by
        intro j hj_gt hj_lt
        by_contra hnb
        have hd_lt : K - j < d₀ := by omega
        have heq_j : K - (K - j) = j := by omega
        exact @Nat.find_min _ decBad hBad _ hd_lt ⟨by omega, by omega, by rwa [heq_j]⟩
      obtain ⟨_, hkf_bridge, hOut_fn⟩ :=
        badKf_single_byte_props (hstep j₁ (by omega)).keepsFrozen hbad_j₁
      have hOut1 : OutMallocng keep1 mmpl lim := hOut_fn (hrx_at j₁ (by omega))
      let sh : Nat → State := fun j => if j ≤ j₁ then traj j else stripCodecS keep1 (traj j)
      have hsh0 : sh 0 = s0 := by simp [sh, ht0]
      have hshK : sh K = stripCodecS keep1 (traj K) := by
        have hnot : ¬ (K ≤ j₁) := by omega
        simp [sh, hnot]
      refine contradiction_of_shadow_traj I hS γ mmpl tp brkStart lim g baseExt memcpyFn hG hMcOk
        hCallee hPanic hExit (sh := sh) (tag := tag) (x := x) (R := R)
        (by rw [hsh0]; exact hpc0)
        (by rw [hsh0]; exact hrun0)
        (by rw [hsh0]; exact hsp0)
        (by rw [hsh0]; exact hSwap.pre_unstripped hOut1 hpre0)
        (fun H' => by rw [hsh0]; exact (lsProg_579_codeLoaded_iff _ H' s0.mem).mp hL_real)
        ?_
        (fun allocE deallocE reallocE memcpyE =>
          by rw [hshK]; exact hHalt_scK allocE deallocE reallocE memcpyE)
        ?_
      · intro j hjK
        obtain ⟨hsp_sc, hsp_un⟩ := htag_spec j hjK
        by_cases hj_lt1 : j < j₁
        · have hle1 : j ≤ j₁ := by omega
          have hle2 : j + 1 ≤ j₁ := by omega
          simp only [sh, hle1, hle2, ↓reduceIte]
          exact hsp_un hOut1 (Or.inl rfl) (hstep j (by omega)).keepsFrozen
        · by_cases hj_eq1 : j = j₁
          · rw [hj_eq1] at hsp_un ⊢
            have hle1 : j₁ ≤ j₁ := Nat.le_refl j₁
            have hnot2 : ¬ (j₁ + 1 ≤ j₁) := by omega
            simp only [sh, hle1, hnot2, ↓reduceIte]
            exact hsp_un hOut1 (Or.inr ⟨hbad_j₁, rfl⟩) hkf_bridge
          · have hgt1 : j₁ < j := by omega
            have hnot1 : ¬ (j ≤ j₁) := by omega
            have hnot2 : ¬ (j + 1 ≤ j₁) := by omega
            simp only [sh, hnot1, hnot2, ↓reduceIte]
            exact hsp_sc (hgood_after j hgt1 hjK)
      · intro m hmK hout_sh
        have huf : (sh m = traj m ∧ OutMallocng keep1 mmpl lim) ∨
            sh m = stripCodecS keep1 (traj m) := by
          by_cases hm_le : m ≤ j₁
          · left; simp [sh, hm_le, hOut1]
          · right; simp [sh, hm_le]
        exact hGoal_of_outcome m hmK
          (hSwap.out_back (Or.inl hsh0) huf (hrx_at m (by omega))
            (hsp_n m (by omega)).1.keepsFrozen hout_sh)
    · have hgood_all : ∀ j < K,
          (stripCodecMem keep1 (traj j).mem).KeepsFrozen
            (stripCodecMem keep1 (traj (j + 1)).mem) := by
        intro j hjK
        by_contra hnb
        have heq_j : K - (K - j) = j := by omega
        exact hBad ⟨K - j, by omega, by omega, by rwa [heq_j]⟩
      let sh : Nat → State := fun j => stripCodecS keep1 (traj j)
      have hsh0 : sh 0 = stripCodecS keep1 s0 := by simp [sh, ht0]
      refine contradiction_of_shadow_traj I hS γ mmpl tp brkStart lim g baseExt memcpyFn hG hMcOk
        hCallee hPanic hExit (sh := sh) (tag := tag) (x := x) (R := R)
        (by rw [hsh0]; exact hpc0)
        (by rw [hsh0]; exact hrun0)
        (by rw [hsh0]; exact hsp0)
        (by rw [hsh0]; exact hSwap.pre_stripped hkeep_blk hpre0)
        (fun H' => by rw [hsh0]; exact lsProg_579_codeLoaded_stripCodec H' hkeep_byte hcrl0)
        (fun j hjK => (htag_spec j hjK).1 (hgood_all j hjK))
        hHalt_scK
        ?_
      intro m hmK hout_sh
      exact hGoal_of_outcome m hmK
        (hSwap.out_back (Or.inr hsh0) (Or.inr rfl) (hrx_at m (by omega))
          (hsp_n m (by omega)).1.keepsFrozen hout_sh)
  · have hInAll : ∀ j < N, P_trap.externAt? (traj j).pc = none → inLsUnmutCode4 (traj j).pc = true := by
      intro j hj hext
      cases hin : inLsUnmutCode4 (traj j).pc
      · exact False.elim (hOff ⟨j, hj, hext, hin⟩)
      · rfl
    have hGoalStatus : sf.status = .Running ∨ sf.status = .OutOfMemory := by
      rcases hGoal with ⟨_, hr, _⟩ | ⟨ho, _⟩
      · exact Or.inl hr
      · exact Or.inr ho
    have hReplay : ∀ k ≤ N, Steps P_real (traj 0) (traj k) ∧ (traj k).fs = (traj 0).fs := by
      intro k
      induction k with
      | zero => intro _; exact ⟨Steps.refl _, rfl⟩
      | succ j ih =>
        intro hj1
        have hj : j < N := by omega
        obtain ⟨hsteps_j, hfs_j⟩ := ih (by omega)
        have hst_j := hstep j hj
        have hno_halt_ex : (traj (j + 1)).status ≠ .Halted ∧
            ∀ msg, (traj (j + 1)).status ≠ .Exception msg := by
          refine ⟨fun hh => ?_, fun msg hex => ?_⟩
          · have heq := Steps.from_not_running ((hsp_n (j + 1) hj1).2.toSteps) (by rw [hh]; nofun)
            have hsf_st : sf.status = .Halted := by cases heq; exact hh
            rcases hGoalStatus with hr | ho
            · rw [hsf_st] at hr; cases hr
            · rw [hsf_st] at ho; cases ho
          · have heq := Steps.from_not_running ((hsp_n (j + 1) hj1).2.toSteps) (by rw [hex]; nofun)
            have hsf_st : sf.status = .Exception msg := by cases heq; exact hex
            rcases hGoalStatus with hr | ho
            · rw [hsf_st] at hr; cases hr
            · rw [hsf_st] at ho; cases ho
        generalize hv_eq : traj (j + 1) = v_next at hst_j hno_halt_ex ⊢
        cases hst_j with
        | halt_unmapped _ _ _ =>
          exact False.elim (hno_halt_ex.1 rfl)
        | extern_fault _ _ _ =>
          exact False.elim (hno_halt_ex.2 _ rfl)
        | @exec inst hrun_j hfm_j =>
          have hfm0 := hfm_j
          unfold Program.fetchMem at hfm_j
          cases heg : P_trap.externAt? (traj j).pc with
          | some f => rw [heg] at hfm_j; cases hfm_j
          | none =>
            rw [heg] at hfm_j
            have hin4 := hInAll j hj heg
            have hnsvc0 := fetchMem_not_isSvc0_of_inLsUnmutCode4 (hcrl_at j (by omega)) hin4 hfm0
            have hdom := fun sym =>
              codecTrapHooksMc_isSome_eq A0 lim g baseExt memcpyFn hMcRow hPanAlloc hPanRaw sym
            have hext_r : P_real.externAt? (traj j).pc = none :=
              (lsProg_579_externAt?_none_iff hdom (traj j).pc).mp heg
            have hfm_r : P_real.fetchMem (traj j).mem (traj j).pc = some inst := by
              unfold Program.fetchMem; rw [hext_r]; exact hfm_j
            have hev_t := evalInst_eq_execInst_local P_trap hnsvc0 (traj j)
            have hev_r := evalInst_eq_execInst_local P_real hnsvc0 (traj j)
            have hstep_r : Step P_real (traj j) (P_trap.evalInst inst (traj j)) := by
              rw [hev_t]; exact hev_r ▸ Step.exec hrun_j hfm_r
            have hfs_step : (P_trap.evalInst inst (traj j)).fs = (traj j).fs := by
              rw [hev_t]
              exact (ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 (traj j)).2.2.2.2.2.2
            exact ⟨hsteps_j.trans (Steps.step hstep_r (Steps.refl _)), hfs_step.trans hfs_j⟩
        | @extern f hrun_j heg_j hkf_j hsym_j =>
          have hdom := fun sym =>
            codecTrapHooksMc_isSome_eq A0 lim g baseExt memcpyFn hMcRow hPanAlloc hPanRaw sym
          obtain ⟨sym, htrap_sym, hext_r⟩ := lsProg_579_externAt?_some hdom heg_j
          obtain ⟨g_fn, hg_fn, hgeq, hfs_step⟩ :=
            trap_extern_step_eq_and_fs_mc g baseExt memcpyFn hG hMcRow hMcFs hPanAlloc hPanRaw
              htrap_sym hno_halt_ex.2
          have hext_r' : P_real.externAt? (traj j).pc = some g_fn := hext_r.trans hg_fn
          have hstep_r : Step P_real (traj j) (f (traj j)) :=
            hgeq ▸ Step.extern hrun_j hext_r' (hgeq.symm ▸ hkf_j) (hgeq.symm ▸ hsym_j)
          exact ⟨hsteps_j.trans (Steps.step hstep_r (Steps.refl _)), hfs_step.trans hfs_j⟩
    obtain ⟨hSteps_real, hfs_real⟩ := hReplay N (Nat.le_refl N)
    rw [ht0, htN] at hSteps_real hfs_real
    refine ⟨sf, hSteps_real, ?_⟩
    rcases hGoal with ⟨hpc_sf, hrun_sf, hq_sf, hcc_sf⟩ | ⟨hoom_sf, hq_sf⟩
    · refine Or.inl ⟨hpc_sf, hrun_sf, ?_, hcc_sf⟩
      dsimp only
      rw [sepConj_assoc, ProofLib.satisfies_pure_sepConj]
      exact ⟨hfs_real, hq_sf⟩
    · exact Or.inr ⟨hoom_sf, hq_sf⟩

/-- Ghost-`memcpyFn` / `baseExt`-parametric pure-`fs` `tryFrom` (`Block 85`) at `lsProg_579`. -/
theorem tryFrom_okFs_mallocng_cli_placed_at_579_mc [LibsignalPlacement]
    {M : AllocCostModel} (I : MallocngCostModelIface M) (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (memcpyFn : State → State)
    (hG : CliGhostAllocHooks M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim g)
    (hMcRow : cliGhostExterns g baseExt memcpyName = some memcpyFn)
    (hMcOk : HookOk memcpyFn (withVmPreserved framelessMemcpySpec))
    (hMcFs : ∀ u, (memcpyFn u).fs = u.fs)
    (hMcSkf : MemcpyStripKeepsFrozen memcpyFn)
    (hPanAlloc : cliGhostExterns g baseExt lsHandleAllocErrorSym = some Rust.panicked)
    (hPanRaw : cliGhostExterns g baseExt lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok (lsProg_579 (cliGhostExterns g baseExt)) (lsmpl.base 85)
      (withLsCodeRoLoaded lsmpl
        (tryFromPlacedSpecOkFs (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim)) := by
  let A0 := mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart
  have hfull := codec_pure_fs_transfer_at_579_mc I hS γ mmpl tp brkStart lim g baseExt memcpyFn
    hG hMcRow hMcOk hMcFs hMcSkf hPanAlloc hPanRaw
    (specF := fun A => withLsCodeRoLoaded lsmpl (tryFromPlacedSpec A lim))
    (fun hC => tryFrom_at_579_of_codecHooks hC)
    (b2_specPoolSwap_tryFrom I hS γ mmpl tp brkStart lim)
    (fun _ _ _ hpre => (extract_withLsCodeRoLoaded hpre).1)
    (fun ⟨g0, st0⟩ R s0 hpre => by
      obtain ⟨_, hpre0⟩ := extract_withLsCodeRoLoaded hpre
      let preRest : SepProp :=
        ⌜s0.readReg64 .x0 = g0.bytesA ∧ (s0.readReg64 .x1).toNat = g0.bytes.length ∧
          g0.bytes.length < 2 ^ 32 ∧ s0.readReg64 .x8 = g0.ret ∧
          FitsEnv M lim st0 (TryFromEnvGen (fun q => TryFromPostEnv q.bytes) g0)⌝ ∗
          (g0.bytesA ↦ₛ g0.bytes) ∗ memRegion g0.ret 120 ∗
          CryptoVerification.LibsignalTripleRatchet.logOff tryFromPlacedImg ∗
          stackAt s0.sp smallRootStack ∗ R
      have hEq : (tryFromPlacedSpec A0 lim).pre (g0, st0) s0 ∗ R =
          A0.pool lim st0 s0 ∗ preRest := by
        dsimp only [tryFromPlacedSpec, tryFromPlacedSpecGen, preRest]
        sep_ac_rfl
      exact pool_rx_of_satisfies_mallocng (hEq ▸ hpre0))
    (fun _ _ _ _ => rfl)
    (fun _ _ _ _ _ => rfl)
  refine subroutine_ok_mono hfull (fun _ _ _ hp => hp) (fun ⟨x0, st0⟩ R s0 sf hq => ?_)
  dsimp only [tryFromPlacedSpecOkFs, withLsCodeRoLoaded] at hq ⊢
  rw [sepConj_assoc, ProofLib.satisfies_pure_sepConj] at hq ⊢
  exact ⟨fun _ => hq.1, hq.2⟩

theorem tryFrom_okFs_mallocng_cli_placed_at_579_impl [LibsignalPlacement]
    {M : AllocCostModel} (I : MallocngCostModelIface M) (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim g)
    (hMcSkf : ∀ f, g.memcpy = some f → MemcpyStripKeepsFrozen f) :
    subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 85)
      (withLsCodeRoLoaded lsmpl
        (tryFromPlacedSpecOkFs (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim)) := by
  have hC := codecHooksPlaced_of_hooks mmpl g W hG
  obtain ⟨f_mc, hf_mc, _, _, _, _, hok_fm, _, hvm_mc, hfs_mc, _⟩ := hG.memcpy
  exact tryFrom_okFs_mallocng_cli_placed_at_579_mc I hS γ mmpl tp brkStart lim g
    (cliExternsPlaced mmpl W) f_mc hG
    (cliGhostExterns_memcpy_some g (cliExternsPlaced mmpl W) hf_mc)
    (hookOk_withVmPreserved hok_fm hvm_mc) hfs_mc (hMcSkf f_mc hf_mc)
    hC.panic_alloc hC.panic_raw

/-- Ghost-`memcpyFn` / `baseExt`-parametric pure-`fs` `pksmSlot` (`Block 111`) at `lsProg_579`. -/
theorem pksmSlot_okFs_of_subsetA4_mallocng_cli_placed_at_579_mc [LibsignalPlacement]
    {M : AllocCostModel} (I : MallocngCostModelIface M) (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (memcpyFn : State → State)
    {PksmEnv : PksmGhost → List AllocEvent → Prop} {S : RunSem}
    (hG : CliGhostAllocHooks M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim g)
    (hMcRow : cliGhostExterns g baseExt memcpyName = some memcpyFn)
    (hMcOk : HookOk memcpyFn (withVmPreserved framelessMemcpySpec))
    (hMcFs : ∀ u, (memcpyFn u).fs = u.fs)
    (hMcSkf : MemcpyStripKeepsFrozen memcpyFn)
    (hPanAlloc : cliGhostExterns g baseExt lsHandleAllocErrorSym = some Rust.panicked)
    (hPanRaw : cliGhostExterns g baseExt lsHandleErrorSym = some Rust.panicked)
    (hSub : ∀ {A' : RustCliAllocBudget M} {H' : LibsignalHooks},
      CodecHooksPlaced M A' lim H' → SubsetA4PksmTryFromPlaced M A' lim PksmEnv H')
    (hParse : ∀ b, S.pksmParse b = pksmParse b) :
    subroutine_ok (lsProg_579 (cliGhostExterns g baseExt)) blkPl_111.base
      (pksmSlotSpecPlacedOkFs M
        (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim PksmEnv S) := by
  let A0 := mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart
  have hfull := codec_pure_fs_transfer_at_579_mc I hS γ mmpl tp brkStart lim g baseExt memcpyFn
    hG hMcRow hMcOk hMcFs hMcSkf hPanAlloc hPanRaw
    (specF := fun A => pksmSlotSpecPlaced M A lim PksmEnv S)
    (fun hC => pksmSlot_at_579_of_codecHooks hSub hParse hC)
    (b2_specPoolSwap_pksmSlot I hS γ mmpl tp brkStart lim PksmEnv S)
    (fun _ _ _ hpre => (extract_withLsCodeRoLoaded hpre).1)
    (fun ⟨g0, st0⟩ R s0 hpre => by
      obtain ⟨_, hpre0⟩ := extract_withLsCodeRoLoaded hpre
      have hEq : ∀ (P1 P2 P3 P4 P5 Pool : SepProp),
          (P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ Pool) ∗ R = Pool ∗ (P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ R) := by
        intros; sep_ac_rfl
      exact pool_rx_of_satisfies_mallocng (hEq _ _ _ _ _ _ ▸ hpre0))
    (fun _ _ _ _ => rfl)
    (fun _ _ _ _ _ => rfl)
  refine subroutine_ok_mono hfull (fun _ _ _ hp => hp) (fun ⟨x0, st0⟩ R s0 sf hq => ?_)
  dsimp only [pksmSlotSpecPlacedOkFs, pksmSlotSpecPlaced, withLsCodeRoLoaded] at hq ⊢
  rw [sepConj_assoc, ProofLib.satisfies_pure_sepConj] at hq ⊢
  exact ⟨fun _ => hq.1, hq.2⟩

theorem pksmSlot_okFs_of_subsetA4_mallocng_cli_placed_at_579_impl [LibsignalPlacement]
    {M : AllocCostModel} (I : MallocngCostModelIface M) (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (g : CliGhostHooks) (W : CliHooks)
    {PksmEnv : PksmGhost → List AllocEvent → Prop} {S : RunSem}
    (hG : CliGhostAllocHooks M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim g)
    (hMcSkf : ∀ f, g.memcpy = some f → MemcpyStripKeepsFrozen f)
    (hSub : ∀ {A' : RustCliAllocBudget M} {H' : LibsignalHooks},
      CodecHooksPlaced M A' lim H' → SubsetA4PksmTryFromPlaced M A' lim PksmEnv H')
    (hParse : ∀ b, S.pksmParse b = pksmParse b) :
    subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) blkPl_111.base
      (pksmSlotSpecPlacedOkFs M
        (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim PksmEnv S) := by
  have hC := codecHooksPlaced_of_hooks mmpl g W hG
  obtain ⟨f_mc, hf_mc, _, _, _, _, hok_fm, _, hvm_mc, hfs_mc, _⟩ := hG.memcpy
  exact pksmSlot_okFs_of_subsetA4_mallocng_cli_placed_at_579_mc I hS γ mmpl tp brkStart lim g
    (cliExternsPlaced mmpl W) f_mc hG
    (cliGhostExterns_memcpy_some g (cliExternsPlaced mmpl W) hf_mc)
    (hookOk_withVmPreserved hok_fm hvm_mc) hfs_mc (hMcSkf f_mc hf_mc)
    hC.panic_alloc hC.panic_raw hSub hParse

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.CodecCalleesFsTransferPlacedBudgetFd
