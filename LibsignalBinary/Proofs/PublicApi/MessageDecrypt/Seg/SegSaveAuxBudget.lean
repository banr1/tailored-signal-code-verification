/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegSaveAux
public meta import ProofLib
public meta import Lean

/-!
# Budget-Threaded Helpers for `SegSave`

Block-`197` budget callee lifters (`futDrop_197`, `dealloc_197`, `alloc_197`), `SepWPp` call tactics
for `onPanic = ⌜False⌝` budget contracts, and `A.atState` VM-preservation transport lemmas
(`atState_eq_of_vmPreserved`, `sepWP_with_vm`, `panic_outcome_of_onPanicVPlaced`).
-/

@[expose] public section

set_option autoImplicit false

open CryptoGames.LibsignalSession (Crypto)
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification (LibsignalHooks LibsignalPlacement lsRustAllocSym lsRustDeallocSym ls_externAt?_of_mem lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi (DecryptGhost)
open CryptoVerification.LibsignalPublicApi.Placed (blkPC_197 blkPl_197 lsProg_197)
open CryptoVerification.LibsignalPublicApi.StoreKit (SessionStoreSpec)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreSpec)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser)
open CryptoVerification.RustHeap (RustAlloc allocHookStack)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget VmPreserved rustCliAllocBudgetSpec rustCliAllocNoOomExternSpecWithStack rustCliDeallocBudgetExternSpecWithStack rustCliDeallocBudgetSpec)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (sepWP_rebase_vmPreserved trapHooks)

namespace LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegSaveAuxBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave
  (clearLscroInvHyps sepWPp_call_panic sepWPp_call_panic_lscro
   sepWPp_call_panic_p sepWPp_call_panic_p_lscro shim_onPanic_entails)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (futDropBudgetSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget (withStoresDecPlacedSpecV)

theorem false_onPanic_entails {F Q : SepProp} : ⌜False⌝ ∗ F ⊢ Q :=
  Entails.pure_left False.elim

/-- Lift `futDropBudgetSpec` from `lsProg_197 H` (`withLsRoCl`) to rebased Block `197`
    (`withLsCodeRoLoaded`). -/
theorem futDrop_197 [LibsignalPlacement] {H : LibsignalHooks} {off : BitVec 64}
    (h : subroutine_ok (lsProg_197 H) (0#64 + off)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsRoCl lsmpl futDropBudgetSpec)) :
    subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) off
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl futDropBudgetSpec) := by
  rw [BitVec.zero_add] at h
  exact CryptoVerification.LibsignalPublicApi.StoreKit.subroutine_ok_withLsCodeRoLoaded_of_rocl h

abbrev futDropBudget_197 := @futDrop_197

/-- Lift `rustCliDeallocBudgetSpec` `HookSat` to rebased Block `197` with `allocHookStack`. -/
theorem dealloc_197 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hsat : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsρ lsRustDeallocSym)
      (rustCliDeallocBudgetExternSpecWithStack M A lim allocHookStack) :=
  LibsignalBinary.Heap.IfaceBudgetLemmas.subroutine_ok_deallocBudget_externWithStack_of_hookSat
    (stk := allocHookStack) hsat
    (ls_externAt?_of_mem (prog := (blkPC_197).rebase (blkPl_197).base H)
      (i := 197) (sym := lsRustDeallocSym) (by decide))

abbrev deallocBudget_197 := @dealloc_197

/-- Lift `rustCliAllocBudgetSpec M A lim false` `HookSat` to rebased Block `197` with
    `allocHookStack`. -/
theorem alloc_197 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hsat : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsρ lsRustAllocSym)
      (rustCliAllocNoOomExternSpecWithStack M A lim false allocHookStack) :=
  LibsignalBinary.Heap.IfaceBudgetLemmas.subroutine_ok_allocNoOom_externWithStack_of_hookSat
    (stk := allocHookStack) hsat
    (ls_externAt?_of_mem (prog := (blkPC_197).rebase (blkPl_197).base H)
      (i := 197) (sym := lsRustAllocSym) (by decide))

abbrev allocNoOom_197 := @alloc_197

/-- Transport `A.atState lim st` across `VmPreserved s sf`. -/
theorem atState_eq_of_vmPreserved {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {s sf : State} (hvm : VmPreserved s sf) :
    A.atState lim st s = A.atState lim st sf :=
  congrArg (fun p => ({ pool := p, live := A.live } : RustAlloc))
    (A.pool_transport lim st s sf hvm).symm

/-- Run a pure basic block on `trapHooks` and expose `VmPreserved s sm` to the continuation. -/
theorem sepWP_with_vm {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)}
    {mid : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    (h : SepWP ((P.rebase b trapHooks).withSvc noSyscalls) mid s Pre
      (fun sm Pm => sm.tpidrEl0 = s.tpidrEl0 ∧ (VmPreserved s sm → post sm Pm))) :
    SepWP (P.rebase b Hk) mid s Pre post :=
  SepWP.mono (sepWP_rebase_vmPreserved h) fun _ _ _ _ ⟨hvm, hp⟩ => hp hvm

scoped syntax "by_vm_open " tacticSeq : tactic
scoped elab_rules : tactic
  | `(tactic| by_vm_open $tac:tacticSeq) => do
    Lean.Elab.Tactic.evalTactic (← `(tactic| apply sepWP_with_vm))
    let g ← Lean.Elab.Tactic.getMainGoal
    g.withContext do
      let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
      let e2 := ty.getArg! 0
      let e1 := e2.getArg! 0
      let ty1 := Lean.mkAppN ty.getAppFn #[e1, ty.getArg! 1, ty.getArg! 2, ty.getArg! 3, ty.getArg! 4, ty.getArg! 5]
      let g1 ← Lean.Meta.mkFreshExprMVar ty1
      let savedGoals ← Lean.Elab.Tactic.getGoals
      Lean.Elab.Tactic.setGoals [g1.mvarId!]
      Lean.Elab.Tactic.evalTactic (← `(tactic| ($tac)))
      let rem ← Lean.Elab.Tactic.getGoals
      unless rem.isEmpty do
        throwError "by_vm_open: inner tactic left {rem.length} unsolved goal(s)"
      Lean.Elab.Tactic.setGoals savedGoals.tail!
      let prf1 ← Lean.instantiateMVars g1
      let prf2 := prf1.replace fun sub =>
        if sub.eqv e2 then some e2 else if sub.eqv e1 then some e2 else none
      g.assign prf2

theorem sepWP_cut_here {prog : Program} {mid target : BitVec 64} {s : State}
    {P : SepProp} {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => SepWP prog target sm Pm post)) :
    SepWP prog target s P post := by
  refine SepWP.of_reaches_pc fun R hm hL => ?_
  obtain ⟨sm, hs1, ⟨_, _, Pm, hPm, h2⟩ | ⟨_, hoom⟩⟩ := SepWP.to_reaches_pc h1 hm hL
  · obtain ⟨sf, hs2, hout⟩ := SepWP.to_reaches_pc h2 hPm (hs1.codeLoaded hL)
    exact ⟨sf, hs1.trans hs2, hout⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

/-- Wrap a `Panicked` final state satisfying `(withStoresDecPlacedSpecV ...).onPanic` into
    `SubroutineOutcome`. -/
theorem panic_outcome_of_onPanicVPlaced [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {st_init : M.σ} {R : SepProp} {s0 sf : State}
    (hpan : sf.status = .Panicked)
    (hm : sf.mem ⊨
      (withStoresDecPlacedSpecV C A lim ctl parse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope).onPanic (x, st_init) s0 sf ∗ R) :
    SubroutineOutcome
      (withStoresDecPlacedSpecV C A lim ctl parse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope)
      (x, st_init) R s0 sf :=
  Or.inr (Or.inl ⟨hpan, hm⟩)

open Lean Elab Tactic in
scoped elab "messageDecrypt_call_panic_budget " hcall:term:max a:term:max : tactic => do
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  evalTactic (← `(tactic| (
    apply (sepWPp_call_panic $hcall (x := $a))
    wp_focus_close (first | wp_norm_goal | wp_norm_lhs)
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  )))
  let gs ← getGoals
  let gPre :: gPanic :: gErr :: gOom :: gCont :: rest := gs
    | throwError "messageDecrypt_call_panic_budget: unexpected subgoals"
  setGoals [gPre]
  evalTactic (← `(tactic| intro _R' _hmR'))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only
    try simp (config := { decide := true }) only [
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc, wp_norm, arm64_norm] at _hmR' ⊢
  )))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars (some hcall)
  setGoals (gPanic :: gErr :: gOom :: gCont :: rest)
  evalTactic (← `(tactic| (
    wp_focus_close (wp_unfold_specs; intro _; first
      | exact false_onPanic_entails
      | exact shim_onPanic_entails (by first | wp_norm_lhs | simp_all [wp_norm, arm64_norm]))
    wp_focus_close (wp_unfold_specs; intro _ _; rfl)
    wp_focus_close (wp_unfold_specs; intro _; rfl)
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident
  )))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId
  wpElimSpatialContext hspId

open Lean Elab Tactic in
scoped elab "messageDecrypt_call_panic_p_budget " hcall:term:max a:term:max : tactic => do
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  evalTactic (← `(tactic| (
    apply (sepWPp_call_panic_p $hcall (x := $a))
    wp_focus_close (first | wp_norm_goal | wp_norm_lhs)
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  )))
  let gs ← getGoals
  let gPre :: gPanic :: gErr :: gOom :: gCont :: rest := gs
    | throwError "messageDecrypt_call_panic_p_budget: unexpected subgoals"
  setGoals [gPre]
  evalTactic (← `(tactic| intro _R' _hmR'))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only
    try simp (config := { decide := true }) only [
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc, wp_norm, arm64_norm] at _hmR' ⊢
  )))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars (some hcall)
  setGoals (gPanic :: gErr :: gOom :: gCont :: rest)
  evalTactic (← `(tactic| (
    wp_focus_close (wp_unfold_specs; intro _; first
      | exact false_onPanic_entails
      | exact shim_onPanic_entails (by first | wp_norm_lhs | simp_all [wp_norm, arm64_norm]))
    wp_focus_close (wp_unfold_specs; intro _ _; rfl)
    wp_focus_close (wp_unfold_specs; intro _; rfl)
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident
  )))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId

open Lean Elab Tactic in
scoped elab "messageDecrypt_call_panic_budget_lscro " hcall:term:max hcrl:term:max a:term:max : tactic => do
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let hcrlId := mkIdent `hcrl_poll
  evalTactic (← `(tactic| (
    apply (sepWPp_call_panic_lscro $hcall $hcrl (x := $a))
    wp_focus_close (first | wp_norm_goal | wp_norm_lhs)
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  )))
  let gs ← getGoals
  let gPre :: gPanic :: gErr :: gOom :: gCont :: rest := gs
    | throwError "messageDecrypt_call_panic_budget_lscro: unexpected subgoals"
  let gPre ← clearLscroInvHyps gPre
  let gPanic ← clearLscroInvHyps gPanic
  let gErr ← clearLscroInvHyps gErr
  let gOom ← clearLscroInvHyps gOom
  setGoals [gPre]
  evalTactic (← `(tactic| intro _R' _hmR'))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only
    try simp (config := { decide := true }) only [
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc, wp_norm, arm64_norm] at _hmR' ⊢
  )))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars none
  setGoals (gPanic :: gErr :: gOom :: gCont :: rest)
  evalTactic (← `(tactic| (
    wp_focus_close (wp_unfold_specs; intro _; first
      | exact false_onPanic_entails
      | exact shim_onPanic_entails (by first | wp_norm_lhs | simp_all [wp_norm, arm64_norm]))
    wp_focus_close (wp_unfold_specs; intro _ _; rfl)
    wp_focus_close (wp_unfold_specs; intro _; rfl)
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident $hcrlId:ident
  )))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId
  wpElimSpatialContext hspId

open Lean Elab Tactic in
scoped elab "messageDecrypt_call_panic_p_budget_lscro " hcall:term:max hcrl:term:max a:term:max : tactic => do
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let hcrlId ← freshIdent `hcrl_sf
  evalTactic (← `(tactic| (
    apply (sepWPp_call_panic_p_lscro $hcall $hcrl (x := $a))
    wp_focus_close (first | wp_norm_goal | wp_norm_lhs)
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  )))
  let gs ← getGoals
  let gPre :: gPanic :: gErr :: gOom :: gCont :: rest := gs
    | throwError "messageDecrypt_call_panic_p_budget_lscro: unexpected subgoals"
  let gPre ← clearLscroInvHyps gPre
  let gPanic ← clearLscroInvHyps gPanic
  let gErr ← clearLscroInvHyps gErr
  let gOom ← clearLscroInvHyps gOom
  setGoals [gPre]
  evalTactic (← `(tactic| intro _R' _hmR'))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only
    try simp (config := { decide := true }) only [
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc, wp_norm, arm64_norm] at _hmR' ⊢
  )))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars none
  setGoals (gPanic :: gErr :: gOom :: gCont :: rest)
  evalTactic (← `(tactic| (
    wp_focus_close (wp_unfold_specs; intro _; first
      | exact false_onPanic_entails
      | exact shim_onPanic_entails (by first | wp_norm_lhs | simp_all [wp_norm, arm64_norm]))
    wp_focus_close (wp_unfold_specs; intro _ _; rfl)
    wp_focus_close (wp_unfold_specs; intro _; rfl)
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident $hcrlId:ident
  )))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId

end LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegSaveAuxBudget
