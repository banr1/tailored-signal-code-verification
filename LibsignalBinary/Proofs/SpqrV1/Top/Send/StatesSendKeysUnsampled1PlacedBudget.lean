/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.Placed.PlacedCallSym
public meta import Lean -- shake: keep
public meta import ProofLib.SepLogic.WP -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1StepsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendKeysUnsampled1Placed
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendKeysUnsampledPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendLeaves1PlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2Encoder
import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendKeysUnsampled1
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Inlined `.keysUnsampled` Sub-Steps (`+372..+684`, Block 124)

Verifies `step_keysUnsampled_372_to_512_placed` and `step_keysUnsampled_512_to_684_placed`
under `RustCliAllocBudget M` with exact 3-allocation envelope `KeysUnsampledAllocEnv`
(`64`B `hdr`, `1152`B `ek`, `2400`B `dk`) and zero OOM branches under `FitsEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendKeysUnsampled1PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open scoped CryptoVerification.SpqrV1.Top.Send.Placed
open CryptoVerification (LibsignalPlacement libsignalSessionCode lsmpl lsρ)
open CryptoVerification.LibsignalSpqrV1
  (Authenticator MlKem mlkemEncaps1Spec mlkemFromSeedSpec mlkemPk1Spec mlkemPk2Spec)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded extHookStack rngFillName rngFillSpec sessionMemcpyRegionSpec
   sessionShimSpec)
open CryptoVerification.LibsignalTripleRatchetRepr (tapeAfter tapeAt)
open CryptoVerification.RustHeap (allocHookStack vecU8Buf)
open CryptoVerification.SpqrV1.Alloc
  (spqrHandleErrorSym spqrRustAllocSym spqrRustNoAllocShimSym spqrRustReallocSym
   spqr_externAt?_of_mem spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Auth (AuthenticatorGhost authenticatorPinAt)
open CryptoVerification.SpqrV1.Poly.ComputeAt (spqrRustDeallocSym)
open CryptoVerification.SpqrV1.Top.Send
  (authHeapBufs authInlineWordsAt authenticatorPinAt_eq_inline_heap exists_words8_of_len64
   finish_sepWP live_pointsTo_entails_vecU8Buf memRegion_48_eq_words6 memRegion_64_eq_words8
   pointsToBytes_2400_expose_pk1 pointsToBytes_2400_expose_pk2 spqrMlkemEncaps1Sym
   spqrMlkemFromSeedSym spqrMlkemPk1Sym spqrMlkemPk2Sym spqrSendCalleeStack spqrSendPlacedEntry
   spqrSendPlacedProg stackAt_spqrSendCallee_from_extHook stackAt_spqrSendCallee_split
   stackAt_spqrSendCallee_to_extHook words8At words8At_entails_memRegion)
open CryptoVerification.SpqrV1.Top.Send.Placed (blkPC_124 blkPl_124)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvent FitsEvents FitsStep RustCliAllocBudget
   RustLayoutOk VmPreserved coarseCostModel fitsEvents_append rustAllocEvents
   rustCliAllocBudgetSpec rustCliAllocNoOomSpec rustCliDeallocBudgetSpec rustCliReallocBudgetSpec
   subroutine_ok_allocNoOom_of_budget)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (sepWP_rebase_vmPreserved trapHooks)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SpqrV1.Top.Send.DefsPlacedBudget (AllocContractsPlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1StepsPlacedBudget
  (spqrSend_session_memcpy_region_ok_placed)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec)

export CryptoVerification.SpqrV1.Top.Send
  (spqrMlkemFromSeedSym spqrMlkemPk1Sym spqrMlkemPk2Sym spqrMlkemEncaps1Sym)

variable [LibsignalPlacement]

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero

theorem tpidrEl0_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).tpidrEl0 = s.tpidrEl0 := by cases s; rfl

theorem tpidrEl0_writeVReg128_pre (s : State) (i : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 i v).tpidrEl0 = s.tpidrEl0 := by cases s; rfl

theorem tpidrEl0_writeVReg64_pre (s : State) (i : BitVec 5) (v : BitVec 64) :
    (s.writeVReg64 i v).tpidrEl0 = s.tpidrEl0 := by cases s; rfl

theorem tpidrEl0_writeVReg32_pre (s : State) (i : BitVec 5) (v : BitVec 32) :
    (s.writeVReg32 i v).tpidrEl0 = s.tpidrEl0 := by cases s; rfl

/-- Sequence a `VmPreserved`-producing `((P.rebase b trapHooks).withSvc noSyscalls)` basic block
    before a `SepWP (P.rebase b Hk)` continuation without `checkBlockNoSvc0` kernel evaluation. -/
theorem sepWP_seg_vm {P : Program} {b mid target : BitVec 64}
    {Hk : String → Option (State → State)} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop}
    (hseg : SepWP ((P.rebase b trapHooks).withSvc noSyscalls) mid s Pre
      (fun sm Pm => sm.tpidrEl0 = s.tpidrEl0 ∧
        (VmPreserved s sm → SepWP (P.rebase b Hk) target sm Pm post))) :
    SepWP (P.rebase b Hk) target s Pre post :=
  SepWP.seq (sepWP_rebase_vmPreserved (Hk := Hk) hseg)
    (fun _ _ _ _ ⟨hvm, hcont⟩ => hcont hvm)

/-- Panic-aware (`SepWPp`) counterpart of `sepWP_seg_vm`. -/
theorem sepWPp_seg_vm {P : Program} {b mid ret : BitVec 64}
    {Hk : String → Option (State → State)} {s : State} {Pre : SepProp}
    {post Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hseg : SepWP ((P.rebase b trapHooks).withSvc noSyscalls) mid s Pre
      (fun sm Pm => sm.tpidrEl0 = s.tpidrEl0 ∧
        (VmPreserved s sm → SepWPp (P.rebase b Hk) ret sm Pm post Qp oom))) :
    SepWPp (P.rebase b Hk) ret s Pre post Qp oom := by
  intro R hm hL
  rcases (sepWP_rebase_vmPreserved (Hk := Hk) hseg).elim hm hL with
    ⟨sm, hsteps, ⟨-, -, Pm, hmm, hvm, hcont⟩ | ⟨_, hfalse⟩⟩
  · obtain ⟨sf, hsteps', hout⟩ := hcont hvm R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact False.elim (not_satisfies_false_sepConj hfalse)

/-- Step a `P.rebase b Hk` basic block (including `STR`/`STP`) up to `mid`, bind
    `hvm : VmPreserved s sm`, and elaborate `rest` before `instantiateMVars` + `Expr.replace`
    so delayed metavariables under `SepWP.step_str*` / `SepWP.step_stp*` are instantiated. -/
elab "step_vm_to " mid:term:max hvm:ident " => " rest:tacticSeq : tactic => do
  let g0 ← Lean.Elab.Tactic.getMainGoal
  let isWpp ← g0.withContext do
    let ty0 := (← Lean.instantiateMVars (← g0.getType)).consumeMData
    let ty ← if ty0.isAppOfArity ``ProofLib.SepWP 6 || ty0.isAppOfArity ``ProofLib.SepWPp 7 then
        pure ty0
      else
        Lean.Meta.withReducible (Lean.Meta.whnf ty0)
    if ty.isAppOfArity ``ProofLib.SepWP 6 then pure false
    else if ty.isAppOfArity ``ProofLib.SepWPp 7 then pure true
    else throwError "step_vm_to: expected SepWP or SepWPp goal, got{Lean.indentExpr ty0}"
  if isWpp then
    Lean.Elab.Tactic.evalTactic (← `(tactic| apply sepWPp_seg_vm (mid := $mid)))
  else
    Lean.Elab.Tactic.evalTactic (← `(tactic| apply sepWP_seg_vm (mid := $mid)))
  let g ← Lean.Elab.Tactic.getMainGoal
  g.withContext do
    let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
    unless ty.getAppFn.isConstOf ``ProofLib.SepWP && ty.getAppNumArgs == 6 do
      throwError "step_vm_to: expected SepWP on withSvc, got{Lean.indentExpr ty}"
    let e2 := ty.getArg! 0
    unless e2.getAppFn.isConstOf ``Arm64.Program.withSvc && e2.getAppNumArgs == 2 do
      throwError "step_vm_to: expected Program.withSvc, got{Lean.indentExpr e2}"
    let e1 := e2.getArg! 0
    let ty1 := Lean.mkAppN ty.getAppFn #[e1, ty.getArg! 1, ty.getArg! 2, ty.getArg! 3, ty.getArg! 4, ty.getArg! 5]
    let g1 ← Lean.Meta.mkFreshExprMVar ty1
    let savedGoals ← Lean.Elab.Tactic.getGoals
    Lean.Elab.Tactic.setGoals [g1.mvarId!]
    Lean.Elab.Tactic.evalTactic (← `(tactic| (
      wp_steps
      refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
        ⟨by simp only [↓tpidrEl0_setMem_pre, tpidrEl0_writeVReg128_pre,
            tpidrEl0_writeVReg64_pre, tpidrEl0_writeVReg32_pre, wp_norm, arm64_norm],
         fun $hvm => ?_⟩
    )))
    Lean.Elab.Tactic.evalTactic (← `(tactic| ($rest)))
    let rem ← Lean.Elab.Tactic.getGoals
    unless rem.isEmpty do
      throwError "step_vm_to: continuation left {rem.length} unsolved goal(s)"
    let prf1 ← Lean.instantiateMVars g1
    let prf2 := prf1.replace fun sub =>
      if sub.eqv e2 then some e2
      else if sub.eqv e1 then some e2
      else none
    g.assign prf2
    Lean.Elab.Tactic.setGoals savedGoals.tail!

theorem transport_budgetPool_norm {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} (s0 : State) {s1 s2 : State}
    (hvm : VmPreserved s1 s2)
    {prog : Program} {target_pc : BitVec 64} {P F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : P = A.pool lim st s0 ∗ F := by sep_focus)
    (heq : A.pool lim st s0 = A.pool lim st s1 := by simp only [wp_norm, arm64_norm])
    (hnext : SepWP prog target_pc s2 (A.pool lim st s2 ∗ F) post oom) :
    SepWP prog target_pc s2 P post oom :=
  SepWP.focus_weaken
    (by rw [heq, A.pool_transport lim st s1 s2 hvm]; exact Entails.refl _)
    hf hnext

theorem wpp_transport_budgetPool_norm {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} (s0 : State) {s1 s2 : State}
    (hvm : VmPreserved s1 s2)
    {prog : Program} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hf : P = A.pool lim st s0 ∗ F := by sep_focus)
    (heq : A.pool lim st s0 = A.pool lim st s1 := by simp only [wp_norm, arm64_norm])
    (hnext : SepWPp prog ret s2 (A.pool lim st s2 ∗ F) Q Qp oom) :
    SepWPp prog ret s2 P Q Qp oom :=
  SepWPp.congr_pre
    (hf.trans (congrArg (· ∗ F) (heq.trans (A.pool_transport lim st s1 s2 hvm).symm)))
    hnext

/-- Transport `A.pool lim st` using the newest `VmPreserved` hypothesis in context and clear it,
    normalizing register/PC wrappers between the pool state in the goal and `VmPreserved`'s LHS. -/
elab "transport_pool_clear_vm" : tactic => do
  let rec findPoolState? : Nat → Lean.Expr → Option Lean.Expr
    | 0, _ => none
    | fuel + 1, e =>
      let e := e.consumeMData
      if e.isAppOfArity ``Arm64.SepProp.sepConj 2 then
        (findPoolState? fuel (e.getArg! 0)).orElse fun _ => findPoolState? fuel (e.getArg! 1)
      else if e.getAppFn.isConstOf ``LibsignalBinary.Heap.RustCliAllocBudget.pool &&
          e.getAppNumArgs == 5 then
        some (e.getArg! 4)
      else
        none
  let g ← Lean.Elab.Tactic.getMainGoal
  let (isWpp, s0Stx?) ← g.withContext do
    let lctx ← Lean.MonadLCtx.getLCtx
    let mut found? : Option Lean.LocalDecl := none
    for d? in lctx.decls.toList.reverse do
      if found?.isNone then
        if let some d := d? then
          if !d.isImplementationDetail then
            let dty := (← Lean.instantiateMVars d.type).consumeMData
            if dty.isAppOfArity ``LibsignalBinary.Heap.VmPreserved 2 then
              found? := some d
    let some decl := found?
      | throwError "transport_pool_clear_vm: no VmPreserved hypothesis in context"
    let lctx' := lctx.setUserName decl.fvarId `_hvm_cur
    let mvar ← Lean.Meta.mkFreshExprMVarAt lctx' (← Lean.Meta.getLocalInstances)
      (← g.getType) .syntheticOpaque
    g.assign mvar
    Lean.Elab.Tactic.replaceMainGoal [mvar.mvarId!]
    mvar.mvarId!.withContext do
      let ty0 := (← Lean.instantiateMVars (← mvar.mvarId!.getType)).consumeMData
      let ty ← if ty0.isAppOfArity ``ProofLib.SepWP 6 || ty0.isAppOfArity ``ProofLib.SepWPp 7 then
          pure ty0
        else
          Lean.Meta.withReducible (Lean.Meta.whnf ty0)
      let isWpp := ty.isAppOfArity ``ProofLib.SepWPp 7
      let s0Stx? ← match findPoolState? 128 (ty.getArg! 3) with
        | some s0E => some <$> Lean.Elab.Term.exprToSyntax s0E
        | none => pure none
      pure (isWpp, s0Stx?)
  let hcur := Lean.mkIdent `_hvm_cur
  match isWpp, s0Stx? with
  | true, some s0Stx =>
    Lean.Elab.Tactic.evalTactic (← `(tactic| (
      refine wpp_transport_budgetPool_norm $s0Stx $hcur (hnext := ?_)
      try clear $hcur)))
  | true, none =>
    Lean.Elab.Tactic.evalTactic (← `(tactic| (
      refine ProofLib.SepWPp.transport_budgetPool $hcur (hnext := ?_)
      try clear $hcur)))
  | false, some s0Stx =>
    Lean.Elab.Tactic.evalTactic (← `(tactic| (
      refine transport_budgetPool_norm $s0Stx $hcur (hnext := ?_)
      try clear $hcur)))
  | false, none =>
    Lean.Elab.Tactic.evalTactic (← `(tactic| (
      refine ProofLib.SepWP.transport_budgetPool $hcur (hnext := ?_)
      try clear $hcur)))

/-- Chain `hacc : VmPreserved s0 s1` with the newest `VmPreserved s1 s2` hypothesis in context,
    replacing `hacc` with `VmPreserved s0 s2` and clearing the intermediate hypotheses. -/
elab "chain_latest_vm " hacc:ident : tactic => do
  let g ← Lean.Elab.Tactic.getMainGoal
  g.withContext do
    let accFVar ← Lean.Elab.Tactic.getFVarId hacc
    let lctx ← Lean.MonadLCtx.getLCtx
    let mut found? : Option Lean.LocalDecl := none
    for d? in lctx.decls.toList.reverse do
      if found?.isNone then
        if let some d := d? then
          if !d.isImplementationDetail && d.fvarId != accFVar then
            let dty := (← Lean.instantiateMVars d.type).consumeMData
            if dty.isAppOfArity ``LibsignalBinary.Heap.VmPreserved 2 then
              found? := some d
    let some decl := found?
      | throwError "chain_latest_vm: no second VmPreserved hypothesis in context"
    let lctx' := lctx.setUserName decl.fvarId `_hvm_cur
    let mvar ← Lean.Meta.mkFreshExprMVarAt lctx' (← Lean.Meta.getLocalInstances)
      (← g.getType) .syntheticOpaque
    g.assign mvar
    Lean.Elab.Tactic.replaceMainGoal [mvar.mvarId!]
  let hcur := Lean.mkIdent `_hvm_cur
  let htmp := Lean.mkIdent `_hvm_tmp
  Lean.Elab.Tactic.evalTactic (← `(tactic| (
    have $htmp := ($hacc).trans $hcur
    clear $hacc $hcur
    have $hacc := $htmp
    clear $htmp)))

/-- Step a `P.rebase b Hk` basic block up to `mid`, transport `A.pool lim st`, and clear the
    intermediate `VmPreserved` hypothesis before running `rest`. -/
macro "step_vm_pool " mid:term:max " => " rest:tacticSeq : tactic => `(tactic|
  step_vm_to $mid _hvm_seg => (
    transport_pool_clear_vm
    ($rest)))

/-- `SepWPp` counterpart of `step_vm_pool`. -/
macro "stepp_vm_pool " mid:term:max " => " rest:tacticSeq : tactic => `(tactic|
  step_vm_to $mid _hvm_seg => (
    transport_pool_clear_vm
    ($rest)))

/-! ## Allocator Event Sequence and Envelope (`KeysUnsampledAllocEnv`) -/

/-- Exact allocator event sequence of `.keysUnsampled` sub-step `512..684`:
    `64`-byte `hdr`, `1152`-byte `ek`, and `2400`-byte `dk` heap allocations at alignment `1`. -/
def keysUnsampledAllocEvents : List AllocEvent :=
  rustAllocEvents 64 1 ++ rustAllocEvents 1152 1 ++ rustAllocEvents 2400 1

/-- Exact allocator event envelope for `.keysUnsampled` sub-step `512..684`. -/
def KeysUnsampledAllocEnv (evs : List AllocEvent) : Prop :=
  evs = keysUnsampledAllocEvents

theorem fitsEnv_keysUnsampledAlloc_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} :
    FitsEnv M lim st KeysUnsampledAllocEnv ↔ FitsEvents M lim st keysUnsampledAllocEvents := by
  constructor
  · intro h
    exact h keysUnsampledAllocEvents rfl
  · intro h evs hevs
    rw [hevs]
    exact h

example :
    FitsEnv coarseCostModel
      { staticCount := 16, staticBytes := 16 * 1024 * 1024, physCap := 256 * 1024 * 1024 }
      coarseCostModel.init KeysUnsampledAllocEnv := by
  rw [fitsEnv_keysUnsampledAlloc_iff]
  dsimp only [keysUnsampledAllocEvents, rustAllocEvents, List.nil_append, List.cons_append,
    FitsEvents, FitsEvent, FitsStep, AllocEvent.withinMaxAlloc]
  exact ⟨⟨by decide, by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide, by decide⟩, trivial⟩

/-! ## Placed Hook `subroutine_ok` Lemmas -/

theorem spqrSend_rngFill_ok_placed {ctl : BitVec 64} {ext : String → Option (State → State)}
    (hrng : HookSat (Rust.withPanics ext) rngFillName (withVmPreserved (rngFillSpec ctl))) :
    subroutine_ok (spqrSendPlacedProg ext) (lsρ rngFillName) (withVmPreserved (rngFillSpec ctl)) :=
  spqr_hook_ok_of_mem hrng

theorem spqrSend_mlkemFromSeed_ok_placed {K : MlKem} {ext : String → Option (State → State)}
    (hseed : HookSat (Rust.withPanics ext) spqrMlkemFromSeedSym
      (withVmPreserved (mlkemFromSeedSpec K))) :
    subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrMlkemFromSeedSym)
      (withVmPreserved (mlkemFromSeedSpec K)) :=
  spqr_hook_ok_of_mem hseed

theorem spqrSend_mlkemPk1_ok_placed {ext : String → Option (State → State)}
    (hpk1 : HookSat (Rust.withPanics ext) spqrMlkemPk1Sym (withVmPreserved mlkemPk1Spec)) :
    subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrMlkemPk1Sym)
      (withVmPreserved mlkemPk1Spec) :=
  spqr_hook_ok_of_mem hpk1

theorem spqrSend_mlkemPk2_ok_placed {ext : String → Option (State → State)}
    (hpk2 : HookSat (Rust.withPanics ext) spqrMlkemPk2Sym (withVmPreserved mlkemPk2Spec)) :
    subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrMlkemPk2Sym)
      (withVmPreserved mlkemPk2Spec) :=
  spqr_hook_ok_of_mem hpk2

theorem spqrSend_encapsulate1_ok_placed {K : MlKem} {ext : String → Option (State → State)}
    (henc : HookSat (Rust.withPanics ext) spqrMlkemEncaps1Sym
      (withVmPreserved (mlkemEncaps1Spec K))) :
    subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrMlkemEncaps1Sym)
      (withVmPreserved (mlkemEncaps1Spec K)) :=
  spqr_hook_ok_of_mem henc

theorem spqrSend_shim_ok_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) :
    subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrRustNoAllocShimSym) sessionShimBudgetSpec :=
  spqr_hook_ok_of_mem hA.shim

theorem spqrSend_alloc_ok_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) :
    subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrRustAllocSym)
      (rustCliAllocBudgetSpec M A lim false) :=
  spqr_hook_ok_of_mem hA.alloc

theorem spqrSend_allocNoOom_ok_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) :
    subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrRustAllocSym)
      (rustCliAllocNoOomSpec M A lim false) :=
  subroutine_ok_allocNoOom_of_budget (spqrSend_alloc_ok_placed hA)

theorem spqrSend_dealloc_ok_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) :
    subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrRustDeallocSym)
      (rustCliDeallocBudgetSpec M A lim) :=
  spqr_hook_ok_of_mem hA.dealloc

theorem spqrSend_realloc_ok_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) :
    subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrRustReallocSym)
      (rustCliReallocBudgetSpec M A lim) :=
  spqr_hook_ok_of_mem hA.realloc

theorem spqrSend_handle_error_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) :
    (spqrSendPlacedProg ext).externAt? (lsρ spqrHandleErrorSym) = some Rust.panicked :=
  (spqr_externAt?_of_mem).trans hA.handle_error

/-! ## `SepWP` / `SepWPp` Segment and Non-OOM Allocator Call Combinators -/

/-- Run a total-correctness `SepWP` segment to `mid`, propagating `LibsignalCodeRoLoaded lsmpl`
    to a `SepWPp` continuation with arbitrary `Q`, `Qp`, and `oom`. -/
theorem of_sepWP_lscro_oom {prog : Program} {mid ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h : SepWP prog mid s P (fun sm Pm => LibsignalCodeRoLoaded lsmpl sm.mem →
      SepWPp prog ret sm Pm Q Qp oom)) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hcont⟩ | ⟨_, hfalse⟩⟩
  · obtain ⟨sf, hsteps', hout⟩ :=
      hcont (hcrl.of_keepsFrozen hsteps.keepsFrozen) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact False.elim (not_satisfies_false_sepConj hfalse)

/-- Close an `of_sepWP_lscro_oom` segment at `mid` with arbitrary `Q`, `Qp`, and `oom`. -/
theorem finish_sepWP_lscro_oom {prog prog_ret : Program} {mid ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = mid) (hrun : s.status = .Running)
    (hnext : LibsignalCodeRoLoaded lsmpl s.mem → SepWPp prog_ret ret s P' Q Qp oom)
    (hent : P ⊢ P') :
    SepWP prog mid s P (fun sm Pm => LibsignalCodeRoLoaded lsmpl sm.mem →
      SepWPp prog_ret ret sm Pm Q Qp oom) :=
  SepWP.done hpc hrun fun hcrl R hm hL =>
    hnext hcrl R (Satisfies.mono (sepConj_mono_left hent) hm) hL

/-- Total-correctness `SepWP` call helper for `__rust_alloc(size, 1)` under
    `FitsEvents M lim bSt (rustAllocEvents size 1)` and `stackAt sp_call spqrSendCalleeStack`. -/
theorem call_rustAlloc_noOom {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {bSt : M.σ} {prog : Program}
    {entry_alloc ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry_alloc (rustCliAllocNoOomSpec M A lim false))
    (size : Nat) (hlay : RustLayoutOk size 1)
    (hFit : FitsEvents M lim bSt (rustAllocEvents size 1))
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry_alloc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hx0 : (s.readReg64 Reg.x0).toNat = size)
    (hx1 : (s.readReg64 Reg.x1).toNat = 1)
    (hsplit : P = (A.pool lim bSt s ∗ stackAt sp_call spqrSendCalleeStack) ∗ Frame)
    (hok : ∀ sf : State,
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf →
      sf.readReg64 (Reg.gpr 0#5) ≠ 0 →
      (sf.readReg64 (Reg.gpr 0#5) == 0#64) = false →
      sf.trace = s0.trace →
      SepWP prog target_pc sf
        ((A.live (sf.readReg64 (Reg.gpr 0#5)) size 1 ∗
          memRegion (sf.readReg64 (Reg.gpr 0#5)) size ∗
          A.pool lim (M.stepEvents (rustAllocEvents size 1) bSt) sf ∗
          stackAt sp_call spqrSendCalleeStack) ∗ Frame) post)
    (hlr_ls : LsRetAddr624 ret_pc := by
      first | assumption | simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    SepWP prog target_pc s P post := by
  let F_ext :=
    memRegion (sp_call - BitVec.ofNat 64 spqrSendCalleeStack)
      (spqrSendCalleeStack - allocHookStack) ∗ Frame
  rw [hsplit]
  refine SepWP.call_subroutine_frame hcall (x := (size, 1, bSt)) (F := F_ext)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    dsimp only [rustCliAllocNoOomSpec]
    rw [hsp, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hlay, hFit, by rw [hlr]; exact hlr_ls⟩, ?_⟩
    rw [stackAt_spqrSendCallee_split sp_call allocHookStack (by decide)] at hm
    exact Satisfies.mono (Entails.of_eq (by dsimp only [F_ext]; sep_ac_rfl)) hm
  · dsimp only [rustCliAllocNoOomSpec]
    conv => arg 4; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hsp, sepConj_assoc]
    refine SepWP.pure_elim fun ⟨hacp, hne0, _⟩ => ?_
    have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htrace
    have hne0' : sf.readReg64 (Reg.gpr 0#5) ≠ 0 := hne0
    have h0b : (sf.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_false_of_ne hne0'
    have hpre_eq :
        (A.pool lim (M.stepEvents (rustAllocEvents size 1) bSt) sf ∗
          stackAt sp_call allocHookStack ∗
          A.live (sf.readReg64 .x0) size 1 ∗
          memRegion (sf.readReg64 .x0) size) ∗ F_ext =
        (A.live (sf.readReg64 (Reg.gpr 0#5)) size 1 ∗
          memRegion (sf.readReg64 (Reg.gpr 0#5)) size ∗
          A.pool lim (M.stepEvents (rustAllocEvents size 1) bSt) sf ∗
          stackAt sp_call spqrSendCalleeStack) ∗ Frame := by
      rw [stackAt_spqrSendCallee_split sp_call allocHookStack (by decide)]
      change _ =
        (A.live (sf.readReg64 .x0) size 1 ∗
          memRegion (sf.readReg64 .x0) size ∗
          A.pool lim (M.stepEvents (rustAllocEvents size 1) bSt) sf ∗
          (memRegion (sp_call - BitVec.ofNat 64 spqrSendCalleeStack)
            (spqrSendCalleeStack - allocHookStack) ∗
            stackAt sp_call allocHookStack)) ∗ Frame
      dsimp only [F_ext]
      sep_ac_rfl
    rw [hpre_eq]
    exact hok sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf hne0' h0b htr_sf

/-- Panic-aware (`SepWPp`) wrapper around `call_rustAlloc_noOom` propagating
    `LibsignalCodeRoLoaded lsmpl` for arbitrary `post`, `Qp`, and `oom`. -/
theorem call_rustAlloc_lscro {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {bSt : M.σ} {prog : Program}
    {entry_alloc ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry_alloc (rustCliAllocNoOomSpec M A lim false))
    (size : Nat) (hlay : RustLayoutOk size 1)
    (hFit : FitsEvents M lim bSt (rustAllocEvents size 1))
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry_alloc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hx0 : (s.readReg64 Reg.x0).toNat = size)
    (hx1 : (s.readReg64 Reg.x1).toNat = 1)
    (hsplit : P = (A.pool lim bSt s ∗ stackAt sp_call spqrSendCalleeStack) ∗ Frame)
    (hok : ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf →
      sf.readReg64 (Reg.gpr 0#5) ≠ 0 →
      (sf.readReg64 (Reg.gpr 0#5) == 0#64) = false →
      sf.trace = s0.trace →
      SepWPp prog target_pc sf
        ((A.live (sf.readReg64 (Reg.gpr 0#5)) size 1 ∗
          memRegion (sf.readReg64 (Reg.gpr 0#5)) size ∗
          A.pool lim (M.stepEvents (rustAllocEvents size 1) bSt) sf ∗
          stackAt sp_call spqrSendCalleeStack) ∗ Frame) post Qp oom)
    (hlr_ls : LsRetAddr624 ret_pc := by
      first | assumption | simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    SepWPp prog target_pc s P post Qp oom := by
  refine of_sepWP_lscro_oom (mid := ret_pc) hcrl ?_
  refine call_rustAlloc_noOom hcall size hlay hFit hpc hrun hsp hsp_align hlr htrace hx0 hx1
    hsplit (fun sf hpc1 hrun1 hsp1 hcs1 hne0 h0b htr1 => ?_) hlr_ls
  exact SepWP.done hpc1 hrun1 fun hcrl1 => hok sf hcrl1 hpc1 hrun1 hsp1 hcs1 hne0 h0b htr1

private theorem stackAt_spqrSendCallee_from_extHook_of_eq {sp sp' : BitVec 64} (h : sp' = sp) :
    memRegion (sp - 123008#64) 106624 ∗ stackAt sp' extHookStack ⊢
    stackAt sp spqrSendCalleeStack := by
  rw [h]
  exact stackAt_spqrSendCallee_from_extHook sp

/-! ## Sub-Step 1a (`+372 -> +512`) -/

/-- Relocatable sub-step 1a (`spqrSendPlacedEntry + 372#64 -> spqrSendPlacedEntry + 512#64`),
    parametric in `ret` and forwarding `VmPreserved s sf`:
    copies `epoch` and inline `Authenticator` words, fills 64-byte `seed` via `rng_fill`,
    generates 2400-byte ML-KEM keypair via `from_seed` at `sp + 4704#64`, and calls `pk1`. -/
theorem step_keysUnsampled_372_to_512_placed
    {K : MlKem} {M : AllocCostModel} {A : RustCliAllocBudget M} {ctl : BitVec 64}
    {ext : String → Option (State → State)}
    (hrng : HookSat (Rust.withPanics ext) rngFillName (withVmPreserved (rngFillSpec ctl)))
    (hseed : HookSat (Rust.withPanics ext) spqrMlkemFromSeedSym
      (withVmPreserved (mlkemFromSeedSpec K)))
    (hpk1 : HookSat (Rust.withPanics ext) spqrMlkemPk1Sym (withVmPreserved mlkemPk1Spec))
    (g : AuthenticatorGhost) (auth : Authenticator) (epoch : BitVec 64)
    (sp cur : BitVec 64) (tape : List (BitVec 8))
    (h64 : 64 ≤ tape.length)
    (seed : List.Vector (BitVec 8) 64)
    (hseed_val : seed.toList = tape.take 64)
    (d4056 : BitVec 64)
    {ret : BitVec 64} {s0 s : State} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 372#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hx24 : s.readReg64 .x24 = sp + 2384#64)
    (htrace : s.trace = s0.trace)
    (hP : P = (
      authInlineWordsAt g (sp + 2392#64) auth ∗
      authHeapBufs A.repAlloc g auth ∗
      ((sp + 2440#64) ↦₆₄ epoch) ∗
      ((sp + 4056#64) ↦₆₄ d4056) ∗
      memRegion (sp + 4192#64) 504 ∗
      memRegion (sp + 4704#64) 2400 ∗
      memRegion (sp + 7136#64) 400 ∗
      memRegion (sp + 7536#64) 400 ∗
      tapeAt ctl cur tape ∗
      stackAt sp spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ sf : State,
      sf.pc = spqrSendPlacedEntry + 512#64 →
      sf.status = .Running →
      sf.sp = sp →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x21 = sp + 7008#64 →
      sf.readReg64 .x22 = epoch →
      sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x24 = sp + 2384#64 →
      sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      VmPreserved s sf →
      SepWP (spqrSendPlacedProg ext) ret sf
        ((authenticatorPinAt A.repAlloc g (sp + 7136#64) auth ∗
          memRegion (sp + 7184#64) 352 ∗
          authInlineWordsAt g (sp + 2392#64) auth ∗
          ((sp + 2440#64) ↦₆₄ epoch) ∗
          ((sp + 4056#64) ↦₆₄ epoch) ∗
          memRegion (sp + 4192#64) 504 ∗
          ((sp + 4704#64) ↦ₛ (K.fromSeed seed).2.2.toList) ∗
          memRegion (sp + 7536#64) 400 ∗
          tapeAfter ctl cur tape 64 ∗
          stackAt sp spqrSendCalleeStack) ∗ Frame) post) :
    SepWP (spqrSendPlacedProg ext) ret s P post := by
  have hrng_call := spqrSend_rngFill_ok_placed hrng
  have hseed_call := spqrSend_mlkemFromSeed_ok_placed hseed
  have hpk1_call := spqrSend_mlkemPk1_ok_placed hpk1
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat,
    withVmPreserved, rngFillSpec, mlkemFromSeedSpec, mlkemPk1Spec]
    at hpc hrng_call hseed_call hpk1_call hnext ⊢
  subst hP
  rw [ProofLib.memRegion_split' (b := sp + 4192#64) (n := 64) (k := 440) (b' := sp + 4256#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
      ProofLib.memRegion_split' (b := sp + 7136#64) (n := 48) (k := 352) (b' := sp + 7184#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
      ProofLib.memRegion_split' (b := sp + 7184#64) (n := 8) (k := 344) (b' := sp + 7192#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
      ProofLib.memRegion_eight (sp + 7184#64),
      ProofLib.memRegion_split' (b := sp + 7536#64) (n := 64) (k := 336) (b' := sp + 7600#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
      memRegion_64_eq_words8 (sp + 4192#64),
      memRegion_48_eq_words6 (sp + 7136#64),
      memRegion_64_eq_words8 (sp + 7536#64)]
  dsimp only [authInlineWordsAt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  iterate 23 (apply SepWP.exists_elim; intro _)
  step_vm_to (lsρ rngFillName) hvm_acc =>
    refine SepWP.fold (words8At_entails_memRegion (sp + 7536#64) _ _ _ _ _ _ _ _)
      (by dsimp only [words8At]; sep_focus) ?_
    wp_apply
    chain_latest_vm hvm_acc
    wp_conv_pre => rw [List.take_append_of_le_length h64, Nat.min_eq_left h64, ← hseed_val]
    obtain ⟨sw0, sw1, sw2, sw3, sw4, sw5, sw6, sw7, hseed_words⟩ :=
      exists_words8_of_len64 seed.toList (List.Vector.toList_length seed)
    wp_conv_pre => rw [hseed_words (sp + 7536#64)]; dsimp only [words8At]
    step_vm_to (lsρ spqrMlkemFromSeedSym) hvm2 =>
      have _t2 := hvm_acc.trans hvm2; clear hvm_acc hvm2; have hvm_acc := _t2; clear _t2
      have hfold_seed_4192 :
          words8At (sp + 4192#64) sw0 sw1 sw2 sw3 sw4 sw5 sw6 sw7 ⊢ ((sp + 4192#64) ↦ₛ seed.toList) := by
        rw [hseed_words (sp + 4192#64)]
        exact Entails.refl _
      refine SepWP.fold hfold_seed_4192 (by dsimp only [words8At]; sep_focus) ?_
      clear hseed_words hfold_seed_4192
      refine SepWP.fold (stackAt_spqrSendCallee_to_extHook sp) (by sep_focus) ?_
      wp_apply
      chain_latest_vm hvm_acc
      step_vm_to (lsρ spqrMlkemPk1Sym) hvm3 =>
        have _t3 := hvm_acc.trans hvm3; clear hvm_acc hvm3; have hvm_acc := _t3; clear _t3
        wp_apply
        chain_latest_vm hvm_acc
        step_vm_to ((blkPl_124).base + 512#64) hvm4 =>
          have _t4 := hvm_acc.trans hvm4; clear hvm_acc hvm4; have hvm_acc := _t4; clear _t4
          refine SepWP.fold (stackAt_spqrSendCallee_from_extHook_of_eq (sp := sp) ?_)
            (by sep_focus) ?_
          · simp only [State.sp, arm64_norm, wp_norm, *]
          have hfold_end :
              authInlineWordsAt g (sp + 7136#64) auth ∗
              authHeapBufs A.repAlloc g auth ∗
              ((sp + 7184#64) ↦₆₄ epoch) ∗
              memRegion (sp + 7192#64) 344 ∗
              ((sp + 4192#64) ↦ₛ seed.toList) ∗
              memRegion (sp + 4256#64) 440 ∗
              words8At (sp + 7536#64) sw0 sw1 sw2 sw3 sw4 sw5 sw6 sw7 ∗
              memRegion (sp + 7600#64) 336 ⊢
              authenticatorPinAt A.repAlloc g (sp + 7136#64) auth ∗
              memRegion (sp + 7184#64) 352 ∗
              memRegion (sp + 4192#64) 504 ∗
              memRegion (sp + 7536#64) 400 := by
            rw [authenticatorPinAt_eq_inline_heap A.repAlloc g (sp + 7136#64) auth,
                ProofLib.memRegion_split' (b := sp + 7184#64) (n := 8) (k := 344) (b' := sp + 7192#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
                ProofLib.memRegion_eight (sp + 7184#64),
                ProofLib.memRegion_split' (b := sp + 4192#64) (n := 64) (k := 440) (b' := sp + 4256#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
                ProofLib.memRegion_split' (b := sp + 7536#64) (n := 64) (k := 336) (b' := sp + 7600#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide)]
            have h7184 : ((sp + 7184#64) ↦₆₄ epoch) ⊢ ∃∗ d : BitVec 64, (sp + 7184#64) ↦₆₄ d :=
              Entails.sepExists_right _ (Entails.refl _)
            have h4192 := pointsToBytes_entails_memRegion (sp + 4192#64) seed.toList
            rw [List.Vector.toList_length] at h4192
            simp only [sepConj_assoc]
            exact sepConj_mono (Entails.refl _)
              (sepConj_mono (Entails.refl _)
                (sepConj_mono h7184
                  (sepConj_mono (Entails.refl _)
                    (sepConj_mono h4192
                      (sepConj_mono (Entails.refl _)
                        (sepConj_mono (words8At_entails_memRegion (sp + 7536#64) sw0 sw1 sw2 sw3 sw4 sw5 sw6 sw7)
                          (Entails.refl _)))))))
          refine SepWP.fold hfold_end
            (by dsimp only [authInlineWordsAt, words8At]; sep_focus) ?_
          refine finish_sepWP
            (hnext _
              (by simp only [wp_norm, arm64_norm, *])
              (by simp only [wp_norm, arm64_norm, *])
              (by simp only [State.sp, arm64_norm, *])
              (by simp only [Reg.x19, arm64_norm, *])
              (by simp only [Reg.x21, arm64_norm, *])
              (by simp only [Reg.x22, arm64_norm, *])
              (by simp only [Reg.x23, arm64_norm, *])
              (by simp only [Reg.x24, arm64_norm, *])
              (by simp only [Reg.x26, arm64_norm, *])
              (by simp only [Reg.x28, arm64_norm, *])
              (by simp only [wp_norm, arm64_norm, *])
              (by simp only [wp_norm, arm64_norm, *])
              hvm_acc)
            (by dsimp only [authInlineWordsAt]; simp only [BitVec.add_assoc, arm64_norm]; exact Entails.of_eq (by sep_ac_rfl))

theorem step_keysUnsampled_372_to_512_pool_placed
    {K : MlKem} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (bSt : M.σ) {ctl : BitVec 64}
    {ext : String → Option (State → State)}
    (hrng : HookSat (Rust.withPanics ext) rngFillName (withVmPreserved (rngFillSpec ctl)))
    (hseed : HookSat (Rust.withPanics ext) spqrMlkemFromSeedSym
      (withVmPreserved (mlkemFromSeedSpec K)))
    (hpk1 : HookSat (Rust.withPanics ext) spqrMlkemPk1Sym (withVmPreserved mlkemPk1Spec))
    (g : AuthenticatorGhost) (auth : Authenticator) (epoch : BitVec 64)
    (sp cur : BitVec 64) (tape : List (BitVec 8))
    (h64 : 64 ≤ tape.length)
    (seed : List.Vector (BitVec 8) 64)
    (hseed_val : seed.toList = tape.take 64)
    (d4056 : BitVec 64)
    {ret : BitVec 64} {s0 s : State} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 372#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hx24 : s.readReg64 .x24 = sp + 2384#64)
    (htrace : s.trace = s0.trace)
    (hP : P = (
      A.pool lim bSt s ∗
      authInlineWordsAt g (sp + 2392#64) auth ∗
      authHeapBufs A.repAlloc g auth ∗
      ((sp + 2440#64) ↦₆₄ epoch) ∗
      ((sp + 4056#64) ↦₆₄ d4056) ∗
      memRegion (sp + 4192#64) 504 ∗
      memRegion (sp + 4704#64) 2400 ∗
      memRegion (sp + 7136#64) 400 ∗
      memRegion (sp + 7536#64) 400 ∗
      tapeAt ctl cur tape ∗
      stackAt sp spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ sf : State,
      sf.pc = spqrSendPlacedEntry + 512#64 →
      sf.status = .Running →
      sf.sp = sp →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x21 = sp + 7008#64 →
      sf.readReg64 .x22 = epoch →
      sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x24 = sp + 2384#64 →
      sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      VmPreserved s sf →
      SepWP (spqrSendPlacedProg ext) ret sf
        ((A.pool lim bSt sf ∗
          authenticatorPinAt A.repAlloc g (sp + 7136#64) auth ∗
          memRegion (sp + 7184#64) 352 ∗
          authInlineWordsAt g (sp + 2392#64) auth ∗
          ((sp + 2440#64) ↦₆₄ epoch) ∗
          ((sp + 4056#64) ↦₆₄ epoch) ∗
          memRegion (sp + 4192#64) 504 ∗
          ((sp + 4704#64) ↦ₛ (K.fromSeed seed).2.2.toList) ∗
          memRegion (sp + 7536#64) 400 ∗
          tapeAfter ctl cur tape 64 ∗
          stackAt sp spqrSendCalleeStack) ∗ Frame) post) :
    SepWP (spqrSendPlacedProg ext) ret s P post := by
  have hP' : P = (
      authInlineWordsAt g (sp + 2392#64) auth ∗
      authHeapBufs A.repAlloc g auth ∗
      ((sp + 2440#64) ↦₆₄ epoch) ∗
      ((sp + 4056#64) ↦₆₄ d4056) ∗
      memRegion (sp + 4192#64) 504 ∗
      memRegion (sp + 4704#64) 2400 ∗
      memRegion (sp + 7136#64) 400 ∗
      memRegion (sp + 7536#64) 400 ∗
      tapeAt ctl cur tape ∗
      stackAt sp spqrSendCalleeStack) ∗ (A.pool lim bSt s ∗ Frame) := by
    rw [hP]; sep_ac_rfl
  refine step_keysUnsampled_372_to_512_placed (A := A) hrng hseed hpk1 g auth epoch sp cur tape
    h64 seed hseed_val d4056 hsp_align hpc hrun hsp hx24 htrace hP'
    (fun sf hpc1 hrun1 hsp1 hx19 hx21 hx22 hx23 hx24' hx26 hx28 htr1 hvregs hvm => ?_)
  have hpool :
      (authenticatorPinAt A.repAlloc g (sp + 7136#64) auth ∗
        memRegion (sp + 7184#64) 352 ∗
        authInlineWordsAt g (sp + 2392#64) auth ∗
        ((sp + 2440#64) ↦₆₄ epoch) ∗
        ((sp + 4056#64) ↦₆₄ epoch) ∗
        memRegion (sp + 4192#64) 504 ∗
        ((sp + 4704#64) ↦ₛ (K.fromSeed seed).2.2.toList) ∗
        memRegion (sp + 7536#64) 400 ∗
        tapeAfter ctl cur tape 64 ∗
        stackAt sp spqrSendCalleeStack) ∗ (A.pool lim bSt s ∗ Frame) =
      (A.pool lim bSt sf ∗
        authenticatorPinAt A.repAlloc g (sp + 7136#64) auth ∗
        memRegion (sp + 7184#64) 352 ∗
        authInlineWordsAt g (sp + 2392#64) auth ∗
        ((sp + 2440#64) ↦₆₄ epoch) ∗
        ((sp + 4056#64) ↦₆₄ epoch) ∗
        memRegion (sp + 4192#64) 504 ∗
        ((sp + 4704#64) ↦ₛ (K.fromSeed seed).2.2.toList) ∗
        memRegion (sp + 7536#64) 400 ∗
        tapeAfter ctl cur tape 64 ∗
        stackAt sp spqrSendCalleeStack) ∗ Frame := by
    rw [A.pool_transport lim bSt s sf hvm]; sep_ac_rfl
  rw [hpool]
  exact hnext sf hpc1 hrun1 hsp1 hx19 hx21 hx22 hx23 hx24' hx26 hx28 htr1 hvregs hvm

/-! ## Sub-Step 1b (`+512 -> +684`) -/

set_option maxHeartbeats 1200000 in
/-- Total-correctness `SepWP` relocatable sub-step 1b
    (`spqrSendPlacedEntry + 512#64 -> spqrSendPlacedEntry + 684#64`) under
    `FitsEvents M lim bSt keysUnsampledAllocEvents`:
    allocates 64-byte `hdr` buffer, 1152-byte `ek` buffer, and 2400-byte `dk` buffer without OOM,
    copies `pk1`, `pk2`, and `dk` from `sp + 4704#64`, prepares arguments for `mac_hdr`, and
    advances `A.pool lim bSt s` to `A.pool lim (M.stepEvents keysUnsampledAllocEvents bSt) sf`. -/
theorem step_keysUnsampled_512_to_684_sepWP_placed
    {K : MlKem} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {bSt : M.σ}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    (hpk2 : HookSat (Rust.withPanics ext) spqrMlkemPk2Sym (withVmPreserved mlkemPk2Spec))
    (sp epoch : BitVec 64)
    (seed : List.Vector (BitVec 8) 64)
    (hpk1_slice : ((K.fromSeed seed).2.2.toList.drop 2304).take 64 = (K.fromSeed seed).1.toList)
    (hpk2_slice : ((K.fromSeed seed).2.2.toList.drop 1152).take 1152 = (K.fromSeed seed).2.1.toList)
    (hFit : FitsEvents M lim bSt keysUnsampledAllocEvents)
    {ret : BitVec 64} {s0 s : State} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 512#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hx21 : s.readReg64 .x21 = sp + 7008#64)
    (hx22 : s.readReg64 .x22 = epoch)
    (htrace : s.trace = s0.trace)
    (hP : P = (
      ((sp + 4704#64) ↦ₛ (K.fromSeed seed).2.2.toList) ∗
      A.pool lim bSt s ∗
      stackAt sp spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ (sf : State) (hdr_ptr ek_ptr dk_ptr : BitVec 64),
      hdr_ptr ≠ 0 → (hdr_ptr == 0#64) = false →
      sf.pc = spqrSendPlacedEntry + 684#64 →
      sf.status = .Running →
      sf.sp = sp →
      sf.readReg64 .x0 = sp + 7136#64 →
      sf.readReg64 .x1 = epoch →
      sf.readReg64 .x2 = hdr_ptr →
      sf.readReg64 .x3 = 64#64 →
      sf.readReg64 .x8 = sp + 4832#64 →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = hdr_ptr →
      sf.readReg64 .x21 = ek_ptr →
      sf.readReg64 .x22 = epoch →
      sf.readReg64 .x23 = dk_ptr →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = 2400#64 →
      sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = 64#64 →
      sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP (spqrSendPlacedProg ext) ret sf
        ((A.live hdr_ptr 64 1 ∗
          (hdr_ptr ↦ₛ (K.fromSeed seed).1.toList) ∗
          vecU8Buf A.repAlloc 1152#64 ek_ptr (K.fromSeed seed).2.1.toList ∗
          vecU8Buf A.repAlloc 2400#64 dk_ptr (K.fromSeed seed).2.2.toList ∗
          memRegion (sp + 4704#64) 2400 ∗
          A.pool lim (M.stepEvents keysUnsampledAllocEvents bSt) sf ∗
          stackAt sp spqrSendCalleeStack) ∗ Frame) post) :
    SepWP (spqrSendPlacedProg ext) ret s P post := by
  have hFit12_3 : FitsEvents M lim bSt
      ((rustAllocEvents 64 1 ++ rustAllocEvents 1152 1) ++ rustAllocEvents 2400 1) := by
    simpa only [keysUnsampledAllocEvents, List.append_assoc] using hFit
  rcases (fitsEvents_append M lim _ _ bSt).mp hFit12_3 with ⟨hFit12, hFit3'⟩
  rcases (fitsEvents_append M lim _ _ bSt).mp hFit12 with ⟨hFit1, hFit2⟩
  have hFit3 : FitsEvents M lim
      (M.stepEvents (rustAllocEvents 1152 1) (M.stepEvents (rustAllocEvents 64 1) bSt))
      (rustAllocEvents 2400 1) := by
    simpa only [AllocCostModel.stepEvents_append] using hFit3'
  have hshim := spqrSend_shim_ok_placed hA
  have halloc := spqrSend_allocNoOom_ok_placed hA
  have hmemcpy := spqrSend_session_memcpy_region_ok_placed hA
  have hpk2_call := spqrSend_mlkemPk2_ok_placed hpk2
  have hek_len : (K.fromSeed seed).2.1.toList.length = 1152 := List.Vector.toList_length _
  have hdk_len : (K.fromSeed seed).2.2.toList.length = 2400 := List.Vector.toList_length _
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat,
    sessionShimBudgetSpec, sessionShimSpec,
    sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec,
    withVmPreserved, mlkemPk2Spec] at hpc hshim halloc hmemcpy hpk2_call ⊢
  subst hP
  step_vm_pool (lsρ spqrRustNoAllocShimSym) =>
    wp_apply
    transport_pool_clear_vm
    step_vm_pool (lsρ spqrRustAllocSym) =>
      refine call_rustAlloc_noOom halloc 64 ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩ hFit1
        (s0 := s0) (ret_pc := (blkPl_124).base + 528#64) (sp_call := sp)
        (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [State.sp, arm64_norm, *]) hsp_align
        (by simp only [Reg.lr, arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [Reg.x0, arm64_norm, *]) (by simp only [Reg.x1, arm64_norm, *])
        (by sep_focus)
        (fun sf1 hpc1 hrun1 hsp1 hcs1 hne0_1 h0b_1 htr_ok1 => ?_)
      rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
      simp only [wp_norm, arm64_norm, *] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
      obtain ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hpk1_words⟩ :=
        exists_words8_of_len64 (K.fromSeed seed).1.toList (List.Vector.toList_length _)
      wp_conv_pre =>
        rw [pointsToBytes_2400_expose_pk1 sp seed hpk1_slice,
            hpk1_words (sp + 7008#64),
            memRegion_64_eq_words8 (sf1.readReg64 (Reg.gpr 0#5))]
        dsimp only [words8At]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      iterate 8 (apply SepWP.exists_elim; intro _)
      step_vm_pool (lsρ spqrMlkemPk2Sym) =>
        have hfold_pk1 :
            words8At (sf1.readReg64 (Reg.gpr 0#5)) hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 ∗
            words8At (sp + 7008#64) hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 ∗
            (((sp + 4704#64) ↦ₛ ((K.fromSeed seed).2.2.toList.take 2304)) ∗
             ((sp + 7072#64) ↦ₛ (((K.fromSeed seed).2.2.toList.drop 2304).drop 64))) ⊢
            ((sf1.readReg64 (Reg.gpr 0#5)) ↦ₛ (K.fromSeed seed).1.toList) ∗
            ((sp + 4704#64) ↦ₛ (K.fromSeed seed).2.2.toList) := by
          rw [← hpk1_words (sf1.readReg64 (Reg.gpr 0#5)),
              ← hpk1_words (sp + 7008#64),
              pointsToBytes_2400_expose_pk1 sp seed hpk1_slice]
          exact Entails.of_eq (by sep_ac_rfl)
        refine SepWP.fold hfold_pk1 (by dsimp only [words8At]; sep_focus) ?_
        clear hpk1_words hfold_pk1
        refine SepWP.fold (stackAt_spqrSendCallee_to_extHook sp) (by sep_focus) ?_
        wp_apply
        transport_pool_clear_vm
        step_vm_pool (lsρ spqrRustNoAllocShimSym) =>
          refine SepWP.fold (stackAt_spqrSendCallee_from_extHook_of_eq (sp := sp) ?_)
            (by sep_focus) ?_
          · simp only [State.sp, arm64_norm, wp_norm, *]
          wp_apply
          transport_pool_clear_vm
          step_vm_pool (lsρ spqrRustAllocSym) =>
            refine call_rustAlloc_noOom halloc 1152 ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩ hFit2
              (s0 := s0) (ret_pc := (blkPl_124).base + 584#64) (sp_call := sp)
              (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
              (by simp only [State.sp, arm64_norm, *]) hsp_align
              (by simp only [Reg.lr, arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [Reg.x0, arm64_norm, *]) (by simp only [Reg.x1, arm64_norm, *])
              (by sep_focus)
              (fun sf2 hpc2 hrun2 hsp2 hcs2 hne0_2 h0b_2 htr_ok2 => ?_)
            rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
            simp only [wp_norm, arm64_norm, *] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
            have hek_mem : memRegion (sf2.readReg64 (Reg.gpr 0#5)) 1152 =
                memRegion (sf2.readReg64 (Reg.gpr 0#5)) (K.fromSeed seed).2.1.toList.length := by
              rw [hek_len]
            wp_conv_pre => rw [pointsToBytes_2400_expose_pk2 sp seed hpk2_slice, hek_mem]
            step_vm_pool (lsρ "memcpy") =>
              wp_apply
              transport_pool_clear_vm
              step_vm_pool (lsρ spqrRustNoAllocShimSym) =>
                have hfold_ek :
                    A.live (sf2.readReg64 (Reg.gpr 0#5)) 1152 1 ∗
                    ((sf2.readReg64 (Reg.gpr 0#5)) ↦ₛ (K.fromSeed seed).2.1.toList) ∗
                    ((sp + 5856#64) ↦ₛ (K.fromSeed seed).2.1.toList) ∗
                    (((sp + 4704#64) ↦ₛ ((K.fromSeed seed).2.2.toList.take 1152)) ∗
                     ((sp + 7008#64) ↦ₛ (((K.fromSeed seed).2.2.toList.drop 1152).drop 1152))) ⊢
                    vecU8Buf A.repAlloc 1152#64 (sf2.readReg64 (Reg.gpr 0#5)) (K.fromSeed seed).2.1.toList ∗
                    ((sp + 4704#64) ↦ₛ (K.fromSeed seed).2.2.toList) := by
                  rw [pointsToBytes_2400_expose_pk2 sp seed hpk2_slice, ← sepConj_assoc]
                  exact sepConj_mono
                    (live_pointsTo_entails_vecU8Buf (A := A.repAlloc)
                      (sf2.readReg64 (Reg.gpr 0#5)) (K.fromSeed seed).2.1.toList
                      1152 hek_len (by decide) (by decide) hne0_2)
                    (Entails.refl _)
                refine SepWP.fold hfold_ek (by sep_focus) ?_
                wp_apply
                transport_pool_clear_vm
                step_vm_pool (lsρ spqrRustAllocSym) =>
                  refine call_rustAlloc_noOom halloc 2400 ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩ hFit3
                    (s0 := s0) (ret_pc := (blkPl_124).base + 620#64) (sp_call := sp)
                    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
                    (by simp only [State.sp, arm64_norm, *]) hsp_align
                    (by simp only [Reg.lr, arm64_norm, *]) (by simp only [arm64_norm, *])
                    (by simp only [Reg.x0, arm64_norm, *]) (by simp only [Reg.x1, arm64_norm, *])
                    (by sep_focus)
                    (fun sf3 hpc3 hrun3 hsp3 hcs3 hne0_3 h0b_3 htr_ok3 => ?_)
                  rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hfp_3, hvregs_3⟩
                  simp only [wp_norm, arm64_norm, *] at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hfp_3 hvregs_3
                  have hdk_mem : memRegion (sf3.readReg64 (Reg.gpr 0#5)) 2400 =
                      memRegion (sf3.readReg64 (Reg.gpr 0#5)) (K.fromSeed seed).2.2.toList.length := by
                    rw [hdk_len]
                  wp_conv_pre => rw [hdk_mem]
                  step_vm_pool (lsρ "memcpy") =>
                    wp_apply
                    transport_pool_clear_vm
                    step_vm_pool ((blkPl_124).base + 684#64) =>
                      have hfold_dk :
                          A.live (sf3.readReg64 (Reg.gpr 0#5)) 2400 1 ∗
                          ((sf3.readReg64 (Reg.gpr 0#5)) ↦ₛ (K.fromSeed seed).2.2.toList) ∗
                          ((sp + 4704#64) ↦ₛ (K.fromSeed seed).2.2.toList) ⊢
                          vecU8Buf A.repAlloc 2400#64 (sf3.readReg64 (Reg.gpr 0#5)) (K.fromSeed seed).2.2.toList ∗
                          memRegion (sp + 4704#64) 2400 := by
                        have h4704 := pointsToBytes_entails_memRegion (sp + 4704#64) (K.fromSeed seed).2.2.toList
                        rw [hdk_len] at h4704
                        rw [← sepConj_assoc]
                        exact sepConj_mono
                          (live_pointsTo_entails_vecU8Buf (A := A.repAlloc)
                            (sf3.readReg64 (Reg.gpr 0#5)) (K.fromSeed seed).2.2.toList
                            2400 hdk_len (by decide) (by decide) hne0_3)
                          h4704
                      refine SepWP.fold hfold_dk (by sep_focus) ?_
                      have hstep_eq :
                          M.stepEvents (rustAllocEvents 2400 1)
                            (M.stepEvents (rustAllocEvents 1152 1)
                              (M.stepEvents (rustAllocEvents 64 1) bSt)) =
                          M.stepEvents keysUnsampledAllocEvents bSt := by
                        simp only [keysUnsampledAllocEvents, List.append_assoc, AllocCostModel.stepEvents_append]
                      refine finish_sepWP
                        (hnext _ (sf1.readReg64 (Reg.gpr 0#5)) (sf2.readReg64 (Reg.gpr 0#5)) (sf3.readReg64 (Reg.gpr 0#5))
                          hne0_1 h0b_1
                          (by simp only [spqrSendPlacedEntry, wp_norm, arm64_norm, *])
                          (by simp only [wp_norm, arm64_norm, *])
                          (by simp only [State.sp, arm64_norm, *])
                          (by simp only [Reg.x0, arm64_norm, *])
                          (by simp only [Reg.x1, arm64_norm, *])
                          (by simp only [Reg.x2, arm64_norm, *])
                          (by simp only [Reg.x3, arm64_norm, *])
                          (by simp only [Reg.x8, arm64_norm, *])
                          (by simp only [Reg.x19, arm64_norm, *])
                          (by simp only [Reg.x20, arm64_norm, *])
                          (by simp only [Reg.x21, arm64_norm, *])
                          (by simp only [Reg.x22, arm64_norm, *])
                          (by simp only [Reg.x23, arm64_norm, *])
                          (by simp only [Reg.x24, arm64_norm, *])
                          (by simp only [Reg.x25, arm64_norm, *])
                          (by simp only [Reg.x26, arm64_norm, *])
                          (by simp only [Reg.x27, arm64_norm, *])
                          (by simp only [Reg.x28, arm64_norm, *])
                          (by simp only [wp_norm, arm64_norm, *])
                          (by simp only [wp_norm, arm64_norm, *]))
                        (by rw [hstep_eq]; exact Entails.of_eq (by sep_ac_rfl))

/-- Panic-aware (`SepWPp`) counterpart of `step_keysUnsampled_512_to_684_sepWP_placed`, propagating
    `LibsignalCodeRoLoaded lsmpl` for arbitrary `post`, `Qp`, and `oom`. -/
theorem step_keysUnsampled_512_to_684_placed
    {K : MlKem} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {bSt : M.σ}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    (hpk2 : HookSat (Rust.withPanics ext) spqrMlkemPk2Sym (withVmPreserved mlkemPk2Spec))
    (sp epoch : BitVec 64)
    (seed : List.Vector (BitVec 8) 64)
    (hpk1_slice : ((K.fromSeed seed).2.2.toList.drop 2304).take 64 = (K.fromSeed seed).1.toList)
    (hpk2_slice : ((K.fromSeed seed).2.2.toList.drop 1152).take 1152 = (K.fromSeed seed).2.1.toList)
    (hFit : FitsEvents M lim bSt keysUnsampledAllocEvents)
    {ret : BitVec 64} {s0 s : State} {P Frame : SepProp}
    {post Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 512#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hx21 : s.readReg64 .x21 = sp + 7008#64)
    (hx22 : s.readReg64 .x22 = epoch)
    (htrace : s.trace = s0.trace)
    (hP : P = (
      ((sp + 4704#64) ↦ₛ (K.fromSeed seed).2.2.toList) ∗
      A.pool lim bSt s ∗
      stackAt sp spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ (sf : State) (hdr_ptr ek_ptr dk_ptr : BitVec 64),
      LibsignalCodeRoLoaded lsmpl sf.mem →
      hdr_ptr ≠ 0 → (hdr_ptr == 0#64) = false →
      sf.pc = spqrSendPlacedEntry + 684#64 →
      sf.status = .Running →
      sf.sp = sp →
      sf.readReg64 .x0 = sp + 7136#64 →
      sf.readReg64 .x1 = epoch →
      sf.readReg64 .x2 = hdr_ptr →
      sf.readReg64 .x3 = 64#64 →
      sf.readReg64 .x8 = sp + 4832#64 →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = hdr_ptr →
      sf.readReg64 .x21 = ek_ptr →
      sf.readReg64 .x22 = epoch →
      sf.readReg64 .x23 = dk_ptr →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = 2400#64 →
      sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = 64#64 →
      sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWPp (spqrSendPlacedProg ext) ret sf
        ((A.live hdr_ptr 64 1 ∗
          (hdr_ptr ↦ₛ (K.fromSeed seed).1.toList) ∗
          vecU8Buf A.repAlloc 1152#64 ek_ptr (K.fromSeed seed).2.1.toList ∗
          vecU8Buf A.repAlloc 2400#64 dk_ptr (K.fromSeed seed).2.2.toList ∗
          memRegion (sp + 4704#64) 2400 ∗
          A.pool lim (M.stepEvents keysUnsampledAllocEvents bSt) sf ∗
          stackAt sp spqrSendCalleeStack) ∗ Frame) post Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P post Qp oom := by
  refine of_sepWP_lscro_oom (mid := spqrSendPlacedEntry + 684#64) hcrl ?_
  refine step_keysUnsampled_512_to_684_sepWP_placed hA hpk2 sp epoch seed hpk1_slice hpk2_slice
    hFit hsp_align hpc hrun hsp hx21 hx22 htrace hP
    (fun sf hdr_ptr ek_ptr dk_ptr hne0 h0b hpc' hrun' hsp'
      hx0 hx1 hx2 hx3 hx8 hx19 hx20 hx21' hx22' hx23 hx24 hx25 hx26 hx27 hx28 htr' hvregs => ?_)
  exact SepWP.done hpc' hrun' fun hcrl' =>
    hnext sf hdr_ptr ek_ptr dk_ptr hcrl' hne0 h0b hpc' hrun' hsp'
      hx0 hx1 hx2 hx3 hx8 hx19 hx20 hx21' hx22' hx23 hx24 hx25 hx26 hx27 hx28 htr' hvregs

theorem step_keysUnsampled_512_to_684_ofEnv_placed
    {K : MlKem} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {bSt : M.σ}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    (hpk2 : HookSat (Rust.withPanics ext) spqrMlkemPk2Sym (withVmPreserved mlkemPk2Spec))
    (sp epoch : BitVec 64)
    (seed : List.Vector (BitVec 8) 64)
    (hpk1_slice : ((K.fromSeed seed).2.2.toList.drop 2304).take 64 = (K.fromSeed seed).1.toList)
    (hpk2_slice : ((K.fromSeed seed).2.2.toList.drop 1152).take 1152 = (K.fromSeed seed).2.1.toList)
    (hFit : FitsEnv M lim bSt KeysUnsampledAllocEnv)
    {ret : BitVec 64} {s0 s : State} {P Frame : SepProp}
    {post Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 512#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hx21 : s.readReg64 .x21 = sp + 7008#64)
    (hx22 : s.readReg64 .x22 = epoch)
    (htrace : s.trace = s0.trace)
    (hP : P = (
      ((sp + 4704#64) ↦ₛ (K.fromSeed seed).2.2.toList) ∗
      A.pool lim bSt s ∗
      stackAt sp spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ (sf : State) (hdr_ptr ek_ptr dk_ptr : BitVec 64),
      LibsignalCodeRoLoaded lsmpl sf.mem →
      hdr_ptr ≠ 0 → (hdr_ptr == 0#64) = false →
      sf.pc = spqrSendPlacedEntry + 684#64 →
      sf.status = .Running →
      sf.sp = sp →
      sf.readReg64 .x0 = sp + 7136#64 →
      sf.readReg64 .x1 = epoch →
      sf.readReg64 .x2 = hdr_ptr →
      sf.readReg64 .x3 = 64#64 →
      sf.readReg64 .x8 = sp + 4832#64 →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = hdr_ptr →
      sf.readReg64 .x21 = ek_ptr →
      sf.readReg64 .x22 = epoch →
      sf.readReg64 .x23 = dk_ptr →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = 2400#64 →
      sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = 64#64 →
      sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWPp (spqrSendPlacedProg ext) ret sf
        ((A.live hdr_ptr 64 1 ∗
          (hdr_ptr ↦ₛ (K.fromSeed seed).1.toList) ∗
          vecU8Buf A.repAlloc 1152#64 ek_ptr (K.fromSeed seed).2.1.toList ∗
          vecU8Buf A.repAlloc 2400#64 dk_ptr (K.fromSeed seed).2.2.toList ∗
          memRegion (sp + 4704#64) 2400 ∗
          A.pool lim (M.stepEvents keysUnsampledAllocEvents bSt) sf ∗
          stackAt sp spqrSendCalleeStack) ∗ Frame) post Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P post Qp oom :=
  step_keysUnsampled_512_to_684_placed hA hpk2 sp epoch seed hpk1_slice hpk2_slice
    (fitsEnv_keysUnsampledAlloc_iff.mp hFit) hcrl hsp_align hpc hrun hsp hx21 hx22 htrace hP hnext

end LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendKeysUnsampled1PlacedBudget
