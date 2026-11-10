/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public meta import ProofLib -- shake: keep
public meta import Lean -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpersPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupSpkRegPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpkPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout

/-!
# Budget-Threaded Stage 1 Error Helpers (`0x13bc`, `0x1384`, `0x11b4`, `0x0df0`) for Arm `R1b`

Verifies `r1b_err_13bc_placed` (`0x13bc → 0x2b28`, `split_signed` failure), `r1b_err_11b4_placed`
(`0x11b4 → 0x1384 → 0x2b78`, unreadable `signed-pre-key`), and `r1b_err_0df0_placed`
(`0x0df0 → 0x2b78`, malformed `registration-id` length) on Block `579` under `[LibsignalPlacement]`
and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpkPlacedBudgetAux

open Arm64 Arm64.Process ProofLib ProofLib.GenPlacedFetches ProofLib.ProgramReflection SepProp
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (speWord)
open CryptoVerification.SignalSession
  (lsRustAllocSymCli lsRustDeallocSymCli lsRustNoAllocShimSymCli)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.MainHops (RunCall ownedBytes sepWPp_weaken_pre)
open CryptoVerification.SignalSession.Cli.Run.Placed
  (blkCodeEq_579 blkLib_579 blkLib_eq_579 blkPC_579 blkPl_579 blkTree_579 lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (Init1Data InRunPlaced PanicK RejectKind r1b_CodeOk r1b_ErrCtxPlaced r1b_SpePayload
   r1b_SpePayload_str r1b_StackBounds r1b_bind_state_placed r1b_buf14_owned r1b_buf14_realign
   r1b_buf14_split1 r1b_buf22_owned r1b_buf22_realign r1b_buf22_split1 r1b_cell64_cons
   r1b_cells6_to_region48 r1b_entails_frame_core r1b_errCommon r1b_errCore r1b_fsp_align
   r1b_join_region r1b_layout1 r1b_malfSym r1b_ownedBytes_zero r1b_region16_to_cells
   r1b_ro_malformed_placed r1b_ro_split14 r1b_ro_split22 r1b_ro_unreadable_placed
   r1b_sepWPp_drop_left r1b_sepWPp_frame_core r1b_sepWPp_pure_left r1b_sepWPp_with_ro_placed
   r1b_u64_split32 r1b_unreadSym runFsp runPcPlaced runPcPlaced_eq runProgPlaced)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets runFrame)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEvents FreeOnlyEvs RustCliAllocBudget VmPreserved
   rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpersPlacedBudget
  (r1b_call_alloc_placed r1b_call_shim_pool_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CommonPlacedBudget
  (r1b_call_dealloc_ownedBytes_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupPlacedBudget
  (r1b_errCommon_atState_eq sepWP_with_vm_oom)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupSpkRegPlacedBudget
  (r1b_cleanup_2b28_placed_env r1b_cleanup_2b78_placed_env)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget (RejectKPlacedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget
  (DropSpeOwnedOkAtBlock)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local simp, local arm64_norm, local wp_norm] runPcPlaced_eq BitVec.ofNat_eq_ofNat

private def checkWordTreeNoSvc0 (rt : RelocTree) : WordTree → Nat → Option Nat
  | .empty, off => some off
  | .leaf b0 b1 b2 b3, off =>
    let w := Obj.wordOfBytesLE [b0, b1, b2, b3] 0
    let ok := match rt.lookup? off with
      | none => w != 0xd400_0001#32
      | some r => VerifiedLibraries.RustStd.checkRelocWordNoSvc0 w r
    if ok then some (off + 4) else none
  | .node _ l r, off =>
    match checkWordTreeNoSvc0 rt l off with
    | some off1 => checkWordTreeNoSvc0 rt r off1
    | none => none

private theorem checkWordTreeNoSvc0_sound {blk : Obj.CodeBlock} {rt : RelocTree}
    (hrelocs : blk.relocs = rt.toList) (hwf : rt.wf = true) :
    ∀ (wt : WordTree) (off off' : Nat) (acc : List (BitVec 8)),
      checkWordTreeNoSvc0 rt wt off = some off' →
      VerifiedLibraries.RustStd.checkBytesNoSvc0 blk off' acc = true →
      VerifiedLibraries.RustStd.checkBytesNoSvc0 blk off (wt.toBytesAux acc) = true
  | .empty, off, off', acc, hwt, hacc => by
    simp only [checkWordTreeNoSvc0, Option.some.injEq] at hwt
    subst hwt; exact hacc
  | .leaf b0 b1 b2 b3, off, off', acc, hwt, hacc => by
    dsimp only [checkWordTreeNoSvc0] at hwt
    cases hok : (match rt.lookup? off with
      | none => Obj.wordOfBytesLE [b0, b1, b2, b3] 0 != 0xd400_0001#32
      | some r =>
        VerifiedLibraries.RustStd.checkRelocWordNoSvc0 (Obj.wordOfBytesLE [b0, b1, b2, b3] 0) r) with
    | false => simp [hok] at hwt
    | true =>
      simp only [hok, ↓reduceIte, Option.some.injEq] at hwt
      subst hwt
      dsimp only [WordTree.toBytesAux, VerifiedLibraries.RustStd.checkBytesNoSvc0]
      rw [relocAt?_of_tree hrelocs hwf rfl, Bool.and_eq_true]
      exact ⟨hok, hacc⟩
  | .node _ l r, off, off', acc, hwt, hacc => by
    dsimp only [checkWordTreeNoSvc0] at hwt
    cases hl : checkWordTreeNoSvc0 rt l off with
    | none => rw [hl] at hwt; cases hwt
    | some off1 =>
      rw [hl] at hwt
      dsimp only [WordTree.toBytesAux]
      exact checkWordTreeNoSvc0_sound hrelocs hwf l off off1 (r.toBytesAux acc) hl
        (checkWordTreeNoSvc0_sound hrelocs hwf r off1 off' acc hwt hacc)

private theorem blk579_tree_noSvc0 :
    (checkWordTreeNoSvc0 blkPC_579._gpf_shared_relocTree blkTree_579 0).isSome = true ∧
    blkPC_579._gpf_shared_relocTree.toList.all
      (fun r => VerifiedLibraries.RustStd.relocKindSafeNoSvc0 r.kind) = true := by
  constructor
  · decide +kernel
  · decide +kernel

theorem blk579_noSvc0 : VerifiedLibraries.RustStd.checkBlockNoSvc0 blkLib_579.text = true := by
  unfold VerifiedLibraries.RustStd.checkBlockNoSvc0
  have ⟨hwt, hrel⟩ := blk579_tree_noSvc0
  obtain ⟨off', hoff'⟩ := Option.isSome_iff_exists.mp hwt
  rw [blkCodeEq_579, WordTree.toBytes, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · exact checkWordTreeNoSvc0_sound blkPC_579._gpf_shared_relocTree_eq
      blkPC_579._gpf_shared_relocTree_wf blkTree_579 0 off' [] hoff' rfl
  · rwa [blkPC_579._gpf_shared_relocTree_eq]

local syntax "by_vm_open " tacticSeq : tactic
local elab_rules : tactic
  | `(tactic| by_vm_open $tac:tacticSeq) => do
    Lean.Elab.Tactic.evalTactic (← `(tactic| apply sepWP_with_vm_oom))
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

theorem r1b_seq_lscro_oom [LibsignalPlacement] {prog : Program} {ret mid : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeRoLoaded lsmpl sm.mem → SepWPp prog ret sm Pm Q Qp oom) oom) :
    SepWPp prog ret s P Q Qp oom :=
  SepWPp.seq_frozen (fun _ _ h0 hkf => h0.of_keepsFrozen hkf) hcrl h

theorem freeOnlyEvs_rustDealloc_append (cap : Nat) {evs : List AllocEvent}
    (h : FreeOnlyEvs evs) :
    FreeOnlyEvs (rustDeallocEvents cap 1 ++ evs) := by
  intro ev hev
  rcases List.mem_append.mp hev with h1 | h2
  · simp only [rustDeallocEvents, List.mem_singleton] at h1
    exact ⟨_, _, h1⟩
  · exact h ev h2

local macro "r1b_prove_spe_str" : tactic =>
  `(tactic| (refine r1b_SpePayload_str _ ?_; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_bits))

local macro (priority := high) "r1b_ac" : tactic =>
  `(tactic| ((try dsimp +zetaDelta only) <;> first | rfl | simp only [emp_sepConj] | sep_ac_rfl))

private meta def r1bStripLetsRA : Nat → Lean.Expr → Lean.Expr
  | 0, e => e
  | n + 1, .letE _ _ v b _ => r1bStripLetsRA n (b.instantiate1 v)
  | n + 1, .mdata _ e => r1bStripLetsRA n e
  | _, e => e

private meta def r1bSplitSepRA : Nat → Lean.Expr → Lean.Expr → Array Lean.Expr
  | 0, _, e => #[e]
  | fuel + 1, sepSample, e =>
    let e := r1bStripLetsRA 64 e
    let fn := sepSample.getAppFn.constName!
    let ar := sepSample.getAppNumArgs
    if e.isAppOfArity fn ar then
      r1bSplitSepRA fuel sepSample (e.getArg! (ar - 2)) ++
        r1bSplitSepRA fuel sepSample (e.getArg! (ar - 1))
    else #[e]

private meta def r1bIsDefEqPureRA (x a : Lean.Expr) : Lean.Elab.TermElabM Bool := do
  let x := r1bStripLetsRA 64 x; let a := r1bStripLetsRA 64 a
  let xf := x.getAppFn; let af := a.getAppFn
  if xf.constName? != af.constName? then return false
  let n := x.getAppNumArgs
  if n != a.getAppNumArgs then return false
  let st ← Lean.saveState
  let mut ok ← if xf.constName?.isNone then
      if xf.isFVar != af.isFVar || xf.isProj != af.isProj then pure false
      else Lean.Meta.withReducibleAndInstances <| Lean.Meta.isDefEq xf af
    else pure true
  for i in [0:n] do
    if ok then
      ok ← Lean.Meta.withReducibleAndInstances <| Lean.Meta.isDefEq (x.getArg! i) (a.getArg! i)
  st.restore
  return ok

private meta def r1bComputeRestRA (ctxName : String) (p a1 : Lean.Expr) :
    Lean.Elab.TermElabM Lean.Expr := do
  let sepTy := Lean.mkConst ``SepProp []
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let ps := (r1bSplitSepRA 64 sepSample (← Lean.instantiateMVars p)).toList
  let a1s := (r1bSplitSepRA 64 sepSample (← Lean.instantiateMVars a1)).toList
  let mut rem := ps
  for a in a1s do
    let mut removed := false
    let mut next : List Lean.Expr := []
    for x in rem do
      if !removed && (← r1bIsDefEqPureRA x a) then removed := true
      else next := next.concat x
    if !removed then
      throwError "{ctxName}: unmatched atom:\n  {a}\nin:\n  {rem}"
    rem := next
  let ar := sepSample.getAppNumArgs
  let mkSep (l r : Lean.Expr) : Lean.Expr :=
    sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (ar - 2) ++ #[l, r])
  match rem.reverse with
  | [] => return empExpr
  | last :: rest => return rest.foldl (fun acc x => mkSep x acc) last

local elab (priority := high) "r1b_entails_frame " t1:term:arg h:term:arg t2:term:arg :
    term <= expectedType => do
  let exp ← Lean.instantiateMVars expectedType
  if exp.isMVar then Lean.Elab.Term.tryPostpone
  let entSample ← Lean.Elab.Term.elabTerm (← `(emp ⊢ emp)) none
  let ear := entSample.getAppNumArgs
  let expS := r1bStripLetsRA 64 exp
  let p := expS.getArg! (ear - 2)
  let q := expS.getArg! (ear - 1)
  if (← Lean.instantiateMVars p).isMVar then Lean.Elab.Term.tryPostpone
  if (← Lean.instantiateMVars q).isMVar then Lean.Elab.Term.tryPostpone
  let hExpr ← Lean.Elab.Term.elabTerm h none
  let hTy := r1bStripLetsRA 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
  let a1 := hTy.getArg! (ear - 2)
  let a2 := hTy.getArg! (ear - 1)
  let r ← r1bComputeRestRA "r1b_entails_frame" p a1
  let sepTy := Lean.mkConst ``SepProp []
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let sar := sepSample.getAppNumArgs
  let mkSep (x y : Lean.Expr) : Lean.Expr :=
    sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
  let rIsEmp ← r1bIsDefEqPureRA r empExpr
  if rIsEmp then
    let eq1 ← Lean.Meta.mkEq p a1
    let eq2 ← Lean.Meta.mkEq a2 q
    let h1Expr ← Lean.Elab.Term.elabTerm t1 (some eq1)
    let h2Expr ← Lean.Elab.Term.elabTerm t2 (some eq2)
    Lean.Meta.mkAppM ``Entails.trans #[← Lean.Meta.mkAppM ``Entails.of_eq #[h1Expr],
      ← Lean.Meta.mkAppM ``Entails.trans #[hExpr, ← Lean.Meta.mkAppM ``Entails.of_eq #[h2Expr]]]
  else
    let eq1 ← Lean.Meta.mkEq p (mkSep a1 r)
    let eq2 ← Lean.Meta.mkEq (mkSep a2 r) q
    let h1Expr ← Lean.Elab.Term.elabTerm t1 (some eq1)
    let h2Expr ← Lean.Elab.Term.elabTerm t2 (some eq2)
    Lean.Meta.mkAppOptM ``r1b_entails_frame_core
      #[some a1, some a2, some r, some p, some q, h1Expr, hExpr, h2Expr]

local elab (priority := high) "r1b_sepWPp_frame " t1:term:arg h:term:arg t2:term:arg hk:term:arg :
    term <= expectedType => do
  let exp ← Lean.instantiateMVars expectedType
  if exp.isMVar then Lean.Elab.Term.tryPostpone
  let expS := r1bStripLetsRA 64 exp
  let args := expS.getAppArgs
  let prog := args[0]!; let ret := args[1]!; let st := args[2]!; let p := args[3]!
  let q := args[4]!; let qp := args[5]!; let oom := args[6]!
  let entSample ← Lean.Elab.Term.elabTerm (← `(emp ⊢ emp)) none
  let ear := entSample.getAppNumArgs
  let hExpr ← Lean.Elab.Term.elabTerm h none
  let hTy := r1bStripLetsRA 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
  let a1 := hTy.getArg! (ear - 2)
  let a2 := hTy.getArg! (ear - 1)
  let r ← r1bComputeRestRA "r1b_sepWPp_frame" p a1
  let sepTy := Lean.mkConst ``SepProp []
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let sar := sepSample.getAppNumArgs
  let mkSep (x y : Lean.Expr) : Lean.Expr :=
    sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
  let rIsEmp ← r1bIsDefEqPureRA r empExpr
  if rIsEmp then
    let eq1 ← Lean.Meta.mkEq p a1
    let eq2 ← Lean.Meta.mkEq a2 a2
    let h1Expr ← Lean.Elab.Term.elabTerm t1 (some eq1)
    let h2Expr ← Lean.Elab.Term.elabTerm t2 (some eq2)
    let hkTy := Lean.mkAppN expS.getAppFn #[prog, ret, st, a2, q, qp, oom]
    let hkExpr ← Lean.Elab.Term.elabTerm hk (some hkTy)
    let hent ← Lean.Meta.mkAppM ``Entails.trans #[← Lean.Meta.mkAppM ``Entails.of_eq #[h1Expr],
      ← Lean.Meta.mkAppM ``Entails.trans #[hExpr, ← Lean.Meta.mkAppM ``Entails.of_eq #[h2Expr]]]
    Lean.Meta.mkAppM ``sepWPp_weaken_pre #[hent, hkExpr]
  else
    let a2IsEmp ← r1bIsDefEqPureRA a2 empExpr
    let p' := if a2IsEmp then r else mkSep a2 r
    let eq1 ← Lean.Meta.mkEq p (mkSep a1 r)
    let eq2 ← Lean.Meta.mkEq (mkSep a2 r) p'
    let h1Expr ← Lean.Elab.Term.elabTerm t1 (some eq1)
    let h2Expr ← Lean.Elab.Term.elabTerm t2 (some eq2)
    let hkTy := Lean.mkAppN expS.getAppFn #[prog, ret, st, p', q, qp, oom]
    let hkExpr ← Lean.Elab.Term.elabTerm hk (some hkTy)
    Lean.Meta.mkAppOptM ``r1b_sepWPp_frame_core
      #[some prog, some ret, some st, some a1, some a2, some r, some p, some p',
        some q, some qp, some oom, h1Expr, hExpr, h2Expr, hkExpr]

local elab:10 (priority := high) "r1b_call_frame" "<|" h:term:10 : term <= expectedType => do
  let exp ← Lean.instantiateMVars expectedType
  if exp.isMVar then Lean.Elab.Term.tryPostpone
  let expS := r1bStripLetsRA 64 exp
  let hExpr ← Lean.Elab.Term.elabTerm h none
  let hTy0 := r1bStripLetsRA 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
  for idx in [0, 1, 2, 4, 5, 6] do
    if !(← Lean.Meta.withReducibleAndInstances <| Lean.Meta.isDefEq (hTy0.getArg! idx) (expS.getArg! idx)) then
      discard <| Lean.Meta.isDefEq (hTy0.getArg! idx) (expS.getArg! idx)
  let p ← Lean.instantiateMVars (expS.getArg! 3)
  let p' ← Lean.instantiateMVars ((r1bStripLetsRA 64 (← Lean.instantiateMVars hTy0)).getArg! 3)
  let sepTy := Lean.mkConst ``SepProp []
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let sar := sepSample.getAppNumArgs
  let mkSep (x y : Lean.Expr) : Lean.Expr :=
    sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
  let ps := (r1bSplitSepRA 64 sepSample p).toList
  let p's := (r1bSplitSepRA 64 sepSample p').toList
  let mut mvarFOpt : Option Lean.Expr := none
  let mut a1s : List Lean.Expr := []
  for a in p's do
    let ai ← Lean.instantiateMVars a
    if mvarFOpt.isNone && ai.isMVar then mvarFOpt := some ai
    else a1s := a1s.concat ai
  let mut rem := ps
  for a in a1s do
    let mut removed := false
    let mut next : List Lean.Expr := []
    for x in rem do
      if !removed && (← r1bIsDefEqPureRA x a) then removed := true
      else next := next.concat x
    if !removed then
      throwError "r1b_call_frame: unmatched callee atom:\n  {a}\nin:\n  {rem}"
    rem := next
  let remProd := match rem.reverse with
    | [] => empExpr
    | last :: rest => rest.foldl (fun acc x => mkSep x acc) last
  if let some mf := mvarFOpt then
    discard <| Lean.Meta.isDefEq mf remProd
  let eqTy ← Lean.Meta.mkEq (← Lean.instantiateMVars p) (← Lean.instantiateMVars p')
  let eqProof ← Lean.Elab.Term.elabTerm (← `(by r1b_ac)) (some eqTy)
  let ent ← Lean.Meta.mkAppM ``Entails.of_eq #[eqProof]
  Lean.Meta.mkAppM ``sepWPp_weaken_pre #[ent, hExpr]

set_option maxHeartbeats 400000 in
theorem r1b_err_13bc_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {eCap ePtr spkCap spkPtr regCap regPtr : BitVec 64}
    {eBs spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x13bc)
    (hx12 : s.readReg64 (.gpr 12#5) = speWord 1)
    (hx10 : s.readReg64 (.gpr 10#5) = eCap)
    (hx27 : s.readReg64 (.gpr 27#5) = ePtr)
    (hx2 : s.readReg64 .x2 = ((BitVec.ofNat 64 eBs.length).truncate 32).zeroExtend 64)
    (henv : ∀ evsFree, FreeOnlyEvs evsFree →
      EnvAt StoresGhost.opened .postDispatch (M.stepEvents evsFree st))
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectKPlacedEnv r1b_CodeOk H A lim EnvAt g s0 resStack Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (((fsp + 0x4d0#64) ↦₆₄ speWord 1) ∗
        ((fsp + 0x4d8#64) ↦₆₄ eCap) ∗ ((fsp + 0x4e0#64) ↦₆₄ ePtr) ∗
        ((fsp + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
        memRegion (fsp + 0x4f0#64) 16 ∗
        ownedBytes A.repAlloc eCap ePtr (BitVec.ofNat 64 eBs.length) eBs ∗
        ownedBytes A.repAlloc spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
        ownedBytes A.repAlloc regCap regPtr (BitVec.ofNat 64 regBs.length) regBs ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗ memRegion (fsp + 0x188#64) 16 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16)
      Q Qp oom := by
  intro fsp
  rw [r1b_errCommon_atState_eq]
  generalize herrCore : r1b_errCore A.repAlloc g d s0 = errCore
  have hst := hc.st
  have hpc := hst.pc; have hrun := hst.run
  have hsp : s.sp = fsp := hst.sp
  have hfp := hst.fp; have hinv := hst.inv; have hvregs := hst.vregs; have hsp0 := hst.spAligned
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hsp0
  have hsplit16 := r1b_region16_to_cells (fsp + 0x4f0#64)
  have h4f8 : (fsp + 0x4f0#64) + 8#64 = fsp + 0x4f8#64 := by bv_omega
  rw [h4f8] at hsplit16
  have he8 : ((fsp + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 eBs.length) =
      ((fsp + 0x4e8#64) ↦₃₂ (BitVec.ofNat 64 eBs.length).truncate 32) ∗
        ((fsp + 0x4ec#64) ↦₃₂ ((BitVec.ofNat 64 eBs.length) >>> 32).truncate 32) := by
    have hz := r1b_u64_split32 (fsp + 0x4e8#64) (BitVec.ofNat 64 eBs.length)
    have ha : (fsp + 0x4e8#64) + 4#64 = fsp + 0x4ec#64 := by bv_omega
    rwa [ha] at hz
  rw [he8, hsplit16]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun w4 => SepWPp.exists_elim fun w5 => ?_
  change s.pc = (blkPl_579).base + 0x13bc#64 at hpc
  apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x2b28#64) hinv
  dsimp only [runProgPlaced, lsProg_579]
  by_vm_open (
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], fun hvm => ?_⟩
    refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
    rw [← hsm] at hvm
    rw [← A.pool_transport lim st s sm hvm]
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hc_m : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm 0x2b28 := hc.of_step
      { pc := by simp only [hsm, wp_norm, arm64_norm]
        run := by simp only [hsm, wp_norm, arm64_norm, hrun]
        sp := by simpa only [hsm, wp_norm, arm64_norm] using hst.sp
        fp := by simpa only [hsm, wp_norm, arm64_norm] using hfp
        inv := hinv_m
        vregs := by simpa only [calleeSavedVRegs, hsm, wp_norm, arm64_norm] using hvregs
        spAligned := hsp0 }
      (by simp only [hsm, wp_norm, arm64_norm]) (by simp only [hsm, wp_norm, arm64_norm])
      (by simp only [hsm, wp_norm, arm64_norm]) (by simp only [hsm, wp_norm, arm64_norm])
      (by simp only [hsm, wp_norm, arm64_norm])
    have hcl := r1b_cleanup_2b28_placed_env (st := st)
      (spkCap := spkCap) (spkPtr := spkPtr)
      (spkLen := BitVec.ofNat 64 spkBs.length) (spkBs := spkBs)
      (regCap := regCap) (regPtr := regPtr)
      (regLen := BitVec.ofNat 64 regBs.length) (regBs := regBs)
      hh hdrop hbnd hc_m hpanic hrej henv
    dsimp only at hcl
    rw [r1b_errCommon_atState_eq, herrCore] at hcl
    refine sepWPp_weaken_pre ?_ hcl
    have h4d0 :
        ((fsp + 0x4d0#64) ↦₆₄ speWord 1) ∗ ((fsp + 0x4d8#64) ↦₆₄ eCap) ∗
          ((fsp + 0x4e0#64) ↦₆₄ ePtr) ∗
          (((fsp + 0x4e8#64) ↦₃₂ (BitVec.ofNat 64 eBs.length).truncate 32) ∗
            ((fsp + 0x4ec#64) ↦₃₂ ((BitVec.ofNat 64 eBs.length) >>> 32).truncate 32)) ∗
          ((fsp + 0x4f0#64) ↦₆₄ w4) ∗ ((fsp + 0x4f8#64) ↦₆₄ w5) ⊢
          memRegion (fsp + 0x4d0#64) 48 := by
      rw [← he8]
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
        r1b_cells6_to_region48 (fsp + 0x4d0#64)
          (speWord 1) eCap ePtr (BitVec.ofNat 64 eBs.length) w4 w5
    have hpay : ownedBytes A.repAlloc eCap ePtr (BitVec.ofNat 64 eBs.length) eBs ⊢
        r1b_SpePayload A.repAlloc (sm.readReg64 (.gpr 12#5)) (sm.readReg64 (.gpr 10#5))
          (sm.readReg64 (.gpr 23#5)) (sm.readReg64 (.gpr 27#5))
          (sm.readReg64 (.gpr 16#5)) (sm.readReg64 (.gpr 14#5))
          (sm.readReg64 (.gpr 15#5)) (sm.readReg64 (.gpr 28#5))
          (sm.readReg64 (.gpr 2#5)) := by
      simp only [hsm, wp_norm, arm64_norm, hx12, hx10, hx27, hx2]; r1b_prove_spe_str
    exact r1b_entails_frame (by r1b_ac) (sepConj_mono hpay h4d0) (by r1b_ac)
  )

set_option maxHeartbeats 400000 in
private theorem r1b_err_1384_tail_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 sm : State} {resStack : Nat}
    {buf d2 pCap v188 regCap regPtr : BitVec 64} {regBs : List (BitVec 8)}
    {errCommon : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc_m : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm 0x2b78)
    (herrCommon : r1b_errCommon (A.atState lim st sm) g d s0 resStack = errCommon)
    (hbuf : buf ≠ 0#64)
    (hpay : ∀ eBs, ownedBytes A.repAlloc 22#64 buf 22#64 eBs ⊢
      r1b_SpePayload A.repAlloc (sm.readReg64 (.gpr 12#5)) (sm.readReg64 (.gpr 10#5))
        (sm.readReg64 (.gpr 23#5)) (sm.readReg64 (.gpr 27#5))
        (sm.readReg64 (.gpr 16#5)) (sm.readReg64 (.gpr 14#5))
        (sm.readReg64 (.gpr 15#5)) (sm.readReg64 (.gpr 28#5))
        (sm.readReg64 (.gpr 2#5)))
    (henv : ∀ evsFree, FreeOnlyEvs evsFree →
      EnvAt StoresGhost.opened .postDispatch (M.stepEvents evsFree st))
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectKPlacedEnv r1b_CodeOk H A lim EnvAt g s0 resStack Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) sm
      (((fsp + 0x170#64) ↦₆₄ 22#64) ∗ ((fsp + 0x188#64) ↦₆₄ v188) ∗
        A.repAlloc.live buf 22 1 ∗ memRegion buf 14 ∗ ((buf + 14#64) ↦₆₄ d2) ∗
        ((fsp + 0x4d0#64) ↦₆₄ pCap) ∗ memRegion (fsp + 0x4d8#64) 40 ∗
        ownedBytes A.repAlloc regCap regPtr (BitVec.ofNat 64 regBs.length) regBs ∗ errCommon ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x168#64) 8 ∗ memRegion (fsp + 0x178#64) 8 ∗
        memRegion (fsp + 0x190#64) 8 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16)
      Q Qp oom := by
  intro fsp
  refine r1b_sepWPp_frame (by r1b_ac) (r1b_buf22_owned A.repAlloc buf d2 hbuf) (by r1b_ac) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun eBs => r1b_sepWPp_pure_left fun _ => ?_
  have hcl := r1b_cleanup_2b78_placed_env (st := st) (regCap := regCap) (regPtr := regPtr)
    (regLen := BitVec.ofNat 64 regBs.length) (regBs := regBs)
    hh hdrop hbnd hc_m hpanic hrej henv
  dsimp only at hcl
  rw [herrCommon] at hcl
  refine sepWPp_weaken_pre ?_ hcl
  (try dsimp +zetaDelta only)
  generalize runFsp s0 = fsp0
  have h4d0 : ((fsp0 + 0x4d0#64) ↦₆₄ pCap) ∗ memRegion (fsp0 + 0x4d8#64) 40 ⊢
      memRegion (fsp0 + 0x4d0#64) 48 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      r1b_cell64_cons (a := fsp0 + 0x4d0#64) pCap (n := 40) (by decide)
  have h168 : memRegion (fsp0 + 0x168#64) 8 ∗ ((fsp0 + 0x170#64) ↦₆₄ 22#64) ∗
      memRegion (fsp0 + 0x178#64) 8 ⊢ memRegion (fsp0 + 0x168#64) 24 := by
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left (pointsTo64_entails_memRegion _ _))) ?_
    rw [r1b_join_region fsp0 0x170 8 8, r1b_join_region fsp0 0x168 8 16]; exact Entails.refl _
  have h188 : ((fsp0 + 0x188#64) ↦₆₄ v188) ∗ memRegion (fsp0 + 0x190#64) 8 ⊢
      memRegion (fsp0 + 0x188#64) 16 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      r1b_cell64_cons (a := fsp0 + 0x188#64) v188 (n := 8) (by decide)
  exact r1b_entails_frame (by r1b_ac)
    (sepConj_mono (hpay eBs) (sepConj_mono h4d0 (sepConj_mono h168 h188))) (by r1b_ac)

private theorem r1b_err_1384_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {buf d2 pCap v188 regCap regPtr : BitVec 64} {regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x1384)
    (hbuf : buf ≠ 0#64)
    (hx12 : s.readReg64 (.gpr 12#5) = speWord 1)
    (_hx9 : s.readReg64 (.gpr 9#5) = buf)
    (hx2 : s.readReg64 .x2 = 22#64)
    (henv : ∀ evsFree, FreeOnlyEvs evsFree →
      EnvAt StoresGhost.opened .postDispatch (M.stepEvents evsFree st))
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectKPlacedEnv r1b_CodeOk H A lim EnvAt g s0 resStack Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (A.repAlloc.live buf 22 1 ∗ memRegion buf 14 ∗ ((buf + 14#64) ↦₆₄ d2) ∗
        ((fsp + 0x4d0#64) ↦₆₄ pCap) ∗ memRegion (fsp + 0x4d8#64) 40 ∗
        ownedBytes A.repAlloc regCap regPtr (BitVec.ofNat 64 regBs.length) regBs ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x168#64) 8 ∗ ((fsp + 0x170#64) ↦₆₄ 22#64) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        ((fsp + 0x188#64) ↦₆₄ v188) ∗ memRegion (fsp + 0x190#64) 8 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16)
      Q Qp oom := by
  intro fsp
  rw [r1b_errCommon_atState_eq]
  generalize herrCore : r1b_errCore A.repAlloc g d s0 = errCore
  have hst := hc.st; have hpc := hst.pc; have hrun := hst.run
  have hsp : s.sp = fsp := hst.sp
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hst.spAligned
  change s.pc = (blkPl_579).base + 0x1384#64 at hpc
  apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x2b78#64) hst.inv
  dsimp only [runProgPlaced, lsProg_579]
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
    (by simp only [wp_norm, arm64_norm, *])
  refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
  have hvm : VmPreserved s sm := by simp only [hsm, wp_norm, arm64_norm]
  rw [← A.pool_transport lim st s sm hvm]
  change SepWPp (runProgPlaced H) _ _ _ _ _ _
  have hc_m : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm 0x2b78 := hc.of_step
    { pc := by simp only [hsm, wp_norm, arm64_norm]
      run := by simp only [hsm, wp_norm, arm64_norm, hst.run]
      sp := by simpa only [hsm, wp_norm, arm64_norm] using hst.sp
      fp := by simpa only [hsm, wp_norm, arm64_norm] using hst.fp
      inv := hinv_m
      vregs := by simpa only [calleeSavedVRegs, hsm, wp_norm, arm64_norm] using hst.vregs
      spAligned := hst.spAligned }
    (by simp only [hsm, wp_norm, arm64_norm]) (by simp only [hsm, wp_norm, arm64_norm])
    (by simp only [hsm, wp_norm, arm64_norm]) (by simp only [hsm, wp_norm, arm64_norm])
    (by simp only [hsm, wp_norm, arm64_norm])
  have hpay : ∀ eBs, ownedBytes A.repAlloc 22#64 buf 22#64 eBs ⊢
      r1b_SpePayload A.repAlloc (sm.readReg64 (.gpr 12#5)) (sm.readReg64 (.gpr 10#5))
        (sm.readReg64 (.gpr 23#5)) (sm.readReg64 (.gpr 27#5))
        (sm.readReg64 (.gpr 16#5)) (sm.readReg64 (.gpr 14#5))
        (sm.readReg64 (.gpr 15#5)) (sm.readReg64 (.gpr 28#5))
        (sm.readReg64 (.gpr 2#5)) := fun eBs => by
    simp only [hsm, wp_norm, arm64_norm, hx12, hx2]; r1b_prove_spe_str
  have herrCommon_m :
      r1b_errCommon (A.atState lim st sm) g d s0 resStack =
        errCore ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st sm ∗ anyHeap := by
    rw [r1b_errCommon_atState_eq, herrCore]
  exact sepWPp_weaken_pre
    (Entails.of_eq (by (try dsimp +zetaDelta only); generalize runFsp s0 = fsp0; r1b_ac))
    (r1b_err_1384_tail_placed hh hdrop hbnd hc_m herrCommon_m hbuf hpay henv hpanic hrej)

set_option maxHeartbeats 400000 in
private theorem r1b_err_11c4_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 sf2 : State} {resStack : Nat}
    {buf pCap pPtr regCap regPtr : BitVec 64} {pBs regBs : List (BitVec 8)}
    {errCore : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (herrCore : r1b_errCore A.repAlloc g d s0 = errCore)
    (hc2 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sf2 0x11c4)
    (hx0_buf : sf2.readReg64 .x0 = buf) (hbuf : buf ≠ 0#64)
    (hx23_2 : sf2.readReg64 (.gpr 23#5) = 0xffffffffffffffff#64)
    (hx27_2 : sf2.readReg64 (.gpr 27#5) = pPtr)
    (henv : ∀ evsFree, FreeOnlyEvs evsFree →
      EnvAt StoresGhost.opened .postDispatch (M.stepEvents evsFree st))
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectKPlacedEnv r1b_CodeOk H A lim EnvAt g s0 resStack Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf2
      (A.repAlloc.live buf 22 1 ∗ memRegion buf 22 ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st sf2 ∗
        ((fsp + 0x4d0#64) ↦₆₄ pCap) ∗ memRegion (fsp + 0x4d8#64) 40 ∗
        ownedBytes A.repAlloc pCap pPtr (BitVec.ofNat 64 pBs.length) pBs ∗
        ownedBytes A.repAlloc regCap regPtr (BitVec.ofNat 64 regBs.length) regBs ∗
        errCore ∗ anyHeap ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x168#64) 8 ∗ memRegion (fsp + 0x170#64) 8 ∗
        memRegion (fsp + 0x178#64) 8 ∗ memRegion (fsp + 0x188#64) 8 ∗
        memRegion (fsp + 0x190#64) 8 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16)
      Q Qp oom := by
  intro fsp
  have hin2 := hc2.st
  have hbuf_f : (buf == 0#64) = false := beq_false_of_ne hbuf
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hin2.sp hin2.spAligned
  have hpc2_in := hin2.pc; change sf2.pc = (blkPl_579).base + 0x11c4#64 at hpc2_in
  have hrun2_in := hin2.run
  apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x11d0#64) hin2.inv
  dsimp only [runProgPlaced, lsProg_579]
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
    (by simp only [wp_norm, arm64_norm, *])
  refine r1b_bind_state_placed fun sm_a hsm_a hinv_a => by
    have hvm_a : VmPreserved sf2 sm_a := by simp only [hsm_a, wp_norm, arm64_norm]
    rw [← A.pool_transport lim st sf2 sm_a hvm_a]
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hin2 : InRunPlaced r1b_CodeOk s0 sm_a 0x11d0 :=
      { pc := by simp only [hsm_a, wp_norm, arm64_norm]
        run := by simp only [hsm_a, wp_norm, arm64_norm, hin2.run]
        sp := by simpa only [hsm_a, wp_norm, arm64_norm] using hin2.sp
        fp := by simpa only [hsm_a, wp_norm, arm64_norm] using hin2.fp
        inv := hinv_a
        vregs := by simpa only [calleeSavedVRegs, hsm_a, wp_norm, arm64_norm] using hin2.vregs
        spAligned := hin2.spAligned }
    have hc2 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm_a 0x11d0 := hc2.of_step hin2
      (by simp only [hsm_a, wp_norm, arm64_norm]) (by simp only [hsm_a, wp_norm, arm64_norm])
      (by simp only [hsm_a, wp_norm, arm64_norm]) (by simp only [hsm_a, wp_norm, arm64_norm])
      (by simp only [hsm_a, wp_norm, arm64_norm])
    have hx0_buf : sm_a.readReg64 .x0 = buf := by
      simpa only [hsm_a, wp_norm, arm64_norm] using hx0_buf
    have hx23_2 : sm_a.readReg64 (.gpr 23#5) = 0xffffffffffffffff#64 := by
      simpa only [hsm_a, wp_norm, arm64_norm] using hx23_2
    have hx27_2 : sm_a.readReg64 (.gpr 27#5) = pPtr := by
      simpa only [hsm_a, wp_norm, arm64_norm] using hx27_2
    have hx8_ro : sm_a.readReg64 (.gpr 8#5) = lsρ r1b_unreadSym := by
      simp only [hsm_a, wp_norm, arm64_norm]
    refine r1b_sepWPp_with_ro_placed hin2.inv r1b_ro_unreadable_placed ?_
    obtain ⟨ro0, ro1, ro2, roRem, hroEq⟩ := r1b_ro_split22 (sm_a.readReg64 (.gpr 8#5))
    conv at hroEq => lhs; rw [hx8_ro]
    clear hsm_a hx8_ro
    rw [hroEq, r1b_buf22_split1 buf, ProofLib.memRegion_eight (fsp + 0x170#64),
      ProofLib.memRegion_eight (fsp + 0x188#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 =>
      SepWPp.exists_elim fun v170 => SepWPp.exists_elim fun v188 => ?_
    have hpc2 := hin2.pc; change sm_a.pc = (blkPl_579).base + 0x11d0#64 at hpc2
    have hrun2 := hin2.run; have hsp2 : sm_a.sp = fsp := hin2.sp
    apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x11e8#64) hin2.inv
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_open (
      wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm, *], fun hvm3 => ?_⟩
      refine r1b_bind_state_placed fun sm3 hsm3 hinv3 => ?_
      rw [← hsm3] at hvm3
      rw [← A.pool_transport lim st sm_a sm3 hvm3]
      change SepWPp (runProgPlaced H) _ _ _ _ _ _
      refine r1b_sepWPp_drop_left <| r1b_sepWPp_drop_left <|
        r1b_sepWPp_drop_left <| r1b_sepWPp_drop_left ?_
      refine r1b_sepWPp_frame (by r1b_ac) (r1b_buf22_realign buf _ _) (by r1b_ac) ?_
      simp only [sepExists_sepConj_left, sepConj_assoc]
      refine SepWPp.exists_elim fun d2 => ?_
      by_cases hpCap : pCap = 0#64
      · subst hpCap
        have hpc3 : sm3.pc = (blkPl_579).base + 0x11e8#64 := by
          simp only [hsm3, wp_norm, arm64_norm]
        have hrun3 : sm3.status = .Running := by
          simp only [hsm3, wp_norm, arm64_norm, hin2.run]
        have hsp3 : sm3.sp = fsp := by simpa only [hsm3, wp_norm, arm64_norm] using hin2.sp
        have hr0 : sm3.readReg64 .x0 = buf := by simpa only [hsm3, wp_norm, arm64_norm] using hx0_buf
        have hr23 : sm3.readReg64 (.gpr 23#5) = 0xffffffffffffffff#64 := by
          simpa only [hsm3, wp_norm, arm64_norm] using hx23_2
        apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x1384#64) hinv3
        dsimp only [runProgPlaced, lsProg_579]
        by_vm_open (
          wp_steps
          refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
            (by simp only [wp_norm, arm64_norm, *])
            ⟨by simp only [wp_norm, arm64_norm, *], fun hvm4 => ?_⟩
          refine r1b_bind_state_placed fun sm4 hsm4 hinv4 => ?_
          rw [← hsm4] at hvm4
          rw [← A.pool_transport lim st sm3 sm4 hvm4]
          change SepWPp (runProgPlaced H) _ _ _ _ _ _
          have hc4 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm4 0x1384 := hc2.of_step
            { pc := by simp only [hsm4, wp_norm, arm64_norm]
              run := by simp only [hsm4, wp_norm, arm64_norm, hin2.run]
              sp := by simpa only [hsm4, wp_norm, arm64_norm] using hin2.sp
              fp := by simpa only [hsm4, wp_norm, arm64_norm] using hin2.fp
              inv := hinv4
              vregs := by simpa only [calleeSavedVRegs, hsm4, wp_norm, arm64_norm] using hin2.vregs
              spAligned := hin2.spAligned }
            (by simp only [hsm4, wp_norm, arm64_norm]) (by simp only [hsm4, wp_norm, arm64_norm])
            (by simp only [hsm4, wp_norm, arm64_norm]) (by simp only [hsm4, wp_norm, arm64_norm])
            (by simp only [hsm4, wp_norm, arm64_norm])
          refine r1b_sepWPp_frame (by r1b_ac)
            (r1b_ownedBytes_zero A.repAlloc pPtr (BitVec.ofNat 64 pBs.length) pBs)
            (by simp only [emp_sepConj]) ?_
          have hcl := r1b_err_1384_placed (st := st) (d2 := ro2) (pCap := 0#64) (v188 := d0)
            (regCap := regCap) (regPtr := regPtr) (regBs := regBs) hh hdrop hbnd hc4 hbuf
            (by simp only [hsm4, wp_norm, arm64_norm, speWord])
            (by simp only [hsm4, wp_norm, arm64_norm])
            (by simp only [hsm4, wp_norm, arm64_norm]) henv hpanic hrej
          dsimp only at hcl
          rw [r1b_errCommon_atState_eq, herrCore] at hcl
          refine sepWPp_weaken_pre ?_ hcl
          (try dsimp +zetaDelta only)
          generalize runFsp s0 = fsp0; exact Entails.of_eq (by r1b_ac)
        )
      · have hpCap_f : (pCap == 0#64) = false := beq_false_of_ne hpCap
        have hpc3 : sm3.pc = (blkPl_579).base + 0x11e8#64 := by
          simp only [hsm3, wp_norm, arm64_norm]
        have hrun3 : sm3.status = .Running := by
          simp only [hsm3, wp_norm, arm64_norm, hin2.run]
        have hsp3 : sm3.sp = fsp := by simpa only [hsm3, wp_norm, arm64_norm] using hin2.sp
        have hr0 : sm3.readReg64 .x0 = buf := by simpa only [hsm3, wp_norm, arm64_norm] using hx0_buf
        apply r1b_seq_lscro_oom (mid := lsρ lsRustDeallocSymCli) hinv3
        dsimp only [runProgPlaced, lsProg_579]
        by_vm_open (
          wp_steps
          refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
            (by simp only [wp_norm, arm64_norm, *])
            ⟨by simp only [wp_norm, arm64_norm, *], fun hvm4 => ?_⟩
          refine r1b_bind_state_placed fun sm4 hsm4 hinv4 => ?_
          rw [← hsm4] at hvm4
          rw [← A.pool_transport lim st sm3 sm4 hvm4]
          change SepWPp (runProgPlaced H) _ _ _ _ _ _
          have hx0_sm4 : sm4.readReg64 .x0 = pPtr := by simp only [hsm4, wp_norm, arm64_norm]
          refine r1b_call_frame <| r1b_call_dealloc_ownedBytes_placed (bs := pBs) hh hbnd hinv4
            (by simp only [hsm4, wp_norm, arm64_norm])
            (by simp only [hsm4, wp_norm, arm64_norm, hin2.run])
            (by simpa only [hsm4, wp_norm, arm64_norm] using hin2.sp)
            (by simpa only [hsm4, wp_norm, arm64_norm] using hin2.fp)
            (by simpa only [calleeSavedVRegs, hsm4, wp_norm, arm64_norm] using hin2.vregs)
            hin2.spAligned (retOff := 0x121c)
            (by simp only [hsm4, wp_norm, arm64_norm]) hx0_sm4
            (by simp only [hsm4, wp_norm, arm64_norm]) (by simp only [hsm4, wp_norm, arm64_norm])
            hpCap hpanic fun sf4 hin4 hcs4 hfs4 htr4 => ?_
          have hc4 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sf4 0x121c := hc2.after_call
            (by simp only [hsm4, wp_norm, arm64_norm]) (by simp only [hsm4, wp_norm, arm64_norm])
            (by simp only [hsm4, wp_norm, arm64_norm]) (by simp only [hsm4, wp_norm, arm64_norm])
            (by simp only [hsm4, wp_norm, arm64_norm]) hin4 hcs4 (congrArg FsState.files hfs4) htr4
          have hx23_4 : sf4.readReg64 (.gpr 23#5) = 22#64 :=
            hcs4.2.2.2.2.1.trans (by simp only [hsm4, wp_norm, arm64_norm])
          have hx26_4 : sf4.readReg64 (.gpr 26#5) = speWord 1 :=
            hcs4.2.2.2.2.2.2.2.1.trans (by simp only [hsm4, wp_norm, arm64_norm, speWord])
          have hx27_4 : sf4.readReg64 (.gpr 27#5) = buf :=
            hcs4.2.2.2.2.2.2.2.2.1.trans (by simp only [hsm4, wp_norm, arm64_norm])
          have hpc4 := hin4.pc; change sf4.pc = (blkPl_579).base + 0x121c#64 at hpc4
          have hrun4 := hin4.run; have hsp4 : sf4.sp = fsp := hin4.sp
          have hv188 : sm3.readReg64 (.gpr 23#5) = 0xffffffffffffffff#64 := by
            simpa only [hsm3, wp_norm, arm64_norm] using hx23_2
          apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x1384#64) hin4.inv
          dsimp only [runProgPlaced, lsProg_579]
          by_vm_open (
            wp_steps
            refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
              (by simp only [wp_norm, arm64_norm, *])
              ⟨by simp only [wp_norm, arm64_norm, *], fun hvm5 => ?_⟩
            refine r1b_bind_state_placed fun sm5 hsm5 hinv5 => ?_
            rw [← hsm5] at hvm5
            rw [← A.pool_transport lim (M.stepEvents (rustDeallocEvents pCap.toNat 1) st) sf4 sm5 hvm5]
            change SepWPp (runProgPlaced H) _ _ _ _ _ _
            have hc5 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm5 0x1384 := hc4.of_step
              { pc := by simp only [hsm5, wp_norm, arm64_norm]
                run := by simp only [hsm5, wp_norm, arm64_norm, hin4.run]
                sp := by simpa only [hsm5, wp_norm, arm64_norm] using hin4.sp
                fp := by simpa only [hsm5, wp_norm, arm64_norm] using hin4.fp
                inv := hinv5
                vregs := by simpa only [calleeSavedVRegs, hsm5, wp_norm, arm64_norm] using hin4.vregs
                spAligned := hin2.spAligned }
              (by simp only [hsm5, wp_norm, arm64_norm]) (by simp only [hsm5, wp_norm, arm64_norm])
              (by simp only [hsm5, wp_norm, arm64_norm]) (by simp only [hsm5, wp_norm, arm64_norm])
              (by simp only [hsm5, wp_norm, arm64_norm])
            have hcl := r1b_err_1384_placed
              (st := M.stepEvents (rustDeallocEvents pCap.toNat 1) st)
              (d2 := ro2) (pCap := pCap) (v188 := 0xffffffffffffffff#64)
              (regCap := regCap) (regPtr := regPtr) (regBs := regBs) hh hdrop hbnd hc5 hbuf
              (by simp only [hsm5, wp_norm, arm64_norm, speWord])
              (by simp only [hsm5, wp_norm, arm64_norm])
              (by simp only [hsm5, wp_norm, arm64_norm])
              (fun evsFree hfo => by
                rw [← M.stepEvents_append]
                exact henv _ (freeOnlyEvs_rustDealloc_append pCap.toNat hfo))
              hpanic hrej
            dsimp only at hcl
            rw [r1b_errCommon_atState_eq, herrCore] at hcl
            refine sepWPp_weaken_pre ?_ hcl
            (try dsimp +zetaDelta only)
            generalize runFsp s0 = fsp0; exact Entails.of_eq (by r1b_ac)
          )
        )
    )

set_option maxHeartbeats 400000 in
theorem r1b_err_11b4_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {pCap pPtr regCap regPtr : BitVec 64} {pBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x11b4)
    (hx23 : s.readReg64 (.gpr 23#5) = 0xffffffffffffffff#64)
    (hx27 : s.readReg64 (.gpr 27#5) = pPtr)
    (hfit : FitsEvents M lim st [AllocEvent.alloc 22])
    (henv : ∀ evsFree, FreeOnlyEvs evsFree →
      EnvAt StoresGhost.opened .postDispatch (M.stepEvents ([AllocEvent.alloc 22] ++ evsFree) st))
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectKPlacedEnv r1b_CodeOk H A lim EnvAt g s0 resStack Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (((fsp + 0x4d0#64) ↦₆₄ pCap) ∗ memRegion (fsp + 0x4d8#64) 40 ∗
        ownedBytes A.repAlloc pCap pPtr (BitVec.ofNat 64 pBs.length) pBs ∗
        ownedBytes A.repAlloc regCap regPtr (BitVec.ofNat 64 regBs.length) regBs ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x168#64) 8 ∗ memRegion (fsp + 0x170#64) 8 ∗
        memRegion (fsp + 0x178#64) 8 ∗ memRegion (fsp + 0x188#64) 8 ∗
        memRegion (fsp + 0x190#64) 8 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16)
      Q Qp oom := by
  intro fsp
  rw [r1b_errCommon_atState_eq]
  generalize herrCore : r1b_errCore A.repAlloc g d s0 = errCore
  have hst := hc.st; have hpc := hst.pc; have hrun := hst.run
  change s.pc = (blkPl_579).base + 0x11b4#64 at hpc
  apply r1b_seq_lscro_oom (mid := lsρ lsRustNoAllocShimSymCli) hst.inv
  dsimp only [runProgPlaced, lsProg_579]
  by_vm_open (
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], fun hvm1 => ?_⟩
    refine r1b_bind_state_placed fun sm1 hsm1 hinv1 => ?_
    rw [← hsm1] at hvm1
    rw [← A.pool_transport lim st s sm1 hvm1]
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    refine r1b_call_frame <| r1b_call_shim_pool_placed (g := g) hh hbnd hinv1
      (by simp only [hsm1, wp_norm, arm64_norm])
      (by simp only [hsm1, wp_norm, arm64_norm, hst.run])
      (by simpa only [hsm1, wp_norm, arm64_norm] using hst.sp)
      (by simpa only [hsm1, wp_norm, arm64_norm] using hst.fp)
      (by simpa only [calleeSavedVRegs, hsm1, wp_norm, arm64_norm] using hst.vregs)
      hst.spAligned (retOff := 0x11b8)
      (by simp only [hsm1, wp_norm, arm64_norm])
      hpanic fun sf1 hin1 hcs1 hfs1 htr1 => ?_
    have hc1 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sf1 0x11b8 := hc.after_call
      (by simp only [hsm1, wp_norm, arm64_norm]) (by simp only [hsm1, wp_norm, arm64_norm])
      (by simp only [hsm1, wp_norm, arm64_norm]) (by simp only [hsm1, wp_norm, arm64_norm])
      (by simp only [hsm1, wp_norm, arm64_norm]) hin1 hcs1 (congrArg FsState.files hfs1) htr1
    have hx23_1 : sf1.readReg64 (.gpr 23#5) = 0xffffffffffffffff#64 :=
      hcs1.2.2.2.2.1.trans (by simpa only [hsm1, wp_norm, arm64_norm] using hx23)
    have hx27_1 : sf1.readReg64 (.gpr 27#5) = pPtr :=
      hcs1.2.2.2.2.2.2.2.2.1.trans (by simpa only [hsm1, wp_norm, arm64_norm] using hx27)
    have hpc1 := hin1.pc; change sf1.pc = (blkPl_579).base + 0x11b8#64 at hpc1
    have hrun1 := hin1.run
    apply r1b_seq_lscro_oom (mid := lsρ lsRustAllocSymCli) hin1.inv
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_open (
      wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm, *], fun hvm2 => ?_⟩
      refine r1b_bind_state_placed fun sm2 hsm2 hinv2 => ?_
      rw [← hsm2] at hvm2
      rw [← A.pool_transport lim st sf1 sm2 hvm2]
      change SepWPp (runProgPlaced H) _ _ _ _ _ _
      have haev : rustAllocEvents 22 1 = [AllocEvent.alloc 22] := rfl
      refine r1b_call_frame <| r1b_call_alloc_placed (size := 22) (align := 1) hh hbnd hinv2
        (by simp only [hsm2, wp_norm, arm64_norm])
        (by simp only [hsm2, wp_norm, arm64_norm, hin1.run])
        (by simpa only [hsm2, wp_norm, arm64_norm] using hin1.sp)
        (by simpa only [hsm2, wp_norm, arm64_norm] using hin1.fp)
        (by simpa only [calleeSavedVRegs, hsm2, wp_norm, arm64_norm] using hin1.vregs)
        hst.spAligned (retOff := 0x11c4)
        (by simp only [hsm2, wp_norm, arm64_norm])
        (by simp only [hsm2, wp_norm, arm64_norm]) (by simp only [hsm2, wp_norm, arm64_norm])
        (by decide) (r1b_layout1 22) (by decide) (haev ▸ hfit) hpanic
        fun sf2 buf hin2 hcs2 hx0_buf hbuf _hmod hfs2 htr2 => ?_
      have hlive_eq : A.live buf 22 1 = A.repAlloc.live buf 22 1 := rfl
      rw [hlive_eq, haev]
      have hc2 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sf2 0x11c4 := hc1.after_call
        (by simp only [hsm2, wp_norm, arm64_norm]) (by simp only [hsm2, wp_norm, arm64_norm])
        (by simp only [hsm2, wp_norm, arm64_norm]) (by simp only [hsm2, wp_norm, arm64_norm])
        (by simp only [hsm2, wp_norm, arm64_norm]) hin2 hcs2 (congrArg FsState.files hfs2) htr2
      have hx23_2 : sf2.readReg64 (.gpr 23#5) = 0xffffffffffffffff#64 :=
        hcs2.2.2.2.2.1.trans (by simpa only [hsm2, wp_norm, arm64_norm] using hx23_1)
      have hx27_2 : sf2.readReg64 (.gpr 27#5) = pPtr :=
        hcs2.2.2.2.2.2.2.2.2.1.trans (by simpa only [hsm2, wp_norm, arm64_norm] using hx27_1)
      exact sepWPp_weaken_pre (Entails.of_eq (by r1b_ac))
        (r1b_err_11c4_placed (st := M.stepEvents [AllocEvent.alloc 22] st)
          hh hdrop hbnd herrCore hc2 hx0_buf hbuf hx23_2 hx27_2
          (fun evsFree hfo => by
            rw [← M.stepEvents_append]
            exact henv evsFree hfo)
          hpanic hrej)
    )
  )

set_option maxHeartbeats 400000 in
theorem r1b_err_0df0_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {regCap regPtr : BitVec 64} {regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x0df0)
    (hfit : FitsEvents M lim st [AllocEvent.alloc 14])
    (henv : ∀ evsFree, FreeOnlyEvs evsFree →
      EnvAt StoresGhost.opened .postDispatch (M.stepEvents ([AllocEvent.alloc 14] ++ evsFree) st))
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectKPlacedEnv r1b_CodeOk H A lim EnvAt g s0 resStack Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (ownedBytes A.repAlloc regCap regPtr (BitVec.ofNat 64 regBs.length) regBs ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x168#64) 24 ∗ memRegion (fsp + 0x188#64) 16 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16 ∗ memRegion (fsp + 0x4d0#64) 48)
      Q Qp oom := by
  intro fsp
  rw [r1b_errCommon_atState_eq]
  generalize herrCore : r1b_errCore A.repAlloc g d s0 = errCore
  have hst := hc.st; have hpc := hst.pc; have hrun := hst.run
  change s.pc = (blkPl_579).base + 0x0df0#64 at hpc
  apply r1b_seq_lscro_oom (mid := lsρ lsRustNoAllocShimSymCli) hst.inv
  dsimp only [runProgPlaced, lsProg_579]
  by_vm_open (
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], fun hvm1 => ?_⟩
    refine r1b_bind_state_placed fun sm1 hsm1 hinv1 => ?_
    rw [← hsm1] at hvm1
    rw [← A.pool_transport lim st s sm1 hvm1]
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    refine r1b_call_frame <|
      r1b_call_shim_pool_placed (g := g) hh hbnd hinv1
        (by simp only [hsm1, wp_norm, arm64_norm])
        (by simp only [hsm1, wp_norm, arm64_norm, hst.run])
        (by simpa only [hsm1, wp_norm, arm64_norm] using hst.sp)
        (by simpa only [hsm1, wp_norm, arm64_norm] using hst.fp)
        (by simpa only [calleeSavedVRegs, hsm1, wp_norm, arm64_norm] using hst.vregs)
        hst.spAligned (retOff := 0x0df4)
        (by simp only [hsm1, wp_norm, arm64_norm])
        hpanic fun sf1 hin1 hcs1 hfs1 htr1 => ?_
    have hc1 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sf1 0x0df4 := hc.after_call
      (by simp only [hsm1, wp_norm, arm64_norm]) (by simp only [hsm1, wp_norm, arm64_norm])
      (by simp only [hsm1, wp_norm, arm64_norm]) (by simp only [hsm1, wp_norm, arm64_norm])
      (by simp only [hsm1, wp_norm, arm64_norm])
      hin1 hcs1 (congrArg FsState.files hfs1) htr1
    have hpc1 := hin1.pc; change sf1.pc = (blkPl_579).base + 0x0df4#64 at hpc1
    have hrun1 := hin1.run
    apply r1b_seq_lscro_oom (mid := lsρ lsRustAllocSymCli) hin1.inv
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_open (
      wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm, *], fun hvm2 => ?_⟩
      refine r1b_bind_state_placed fun sm2 hsm2 hinv2 => ?_
      rw [← hsm2] at hvm2
      rw [← A.pool_transport lim st sf1 sm2 hvm2]
      change SepWPp (runProgPlaced H) _ _ _ _ _ _
      have haev : rustAllocEvents 14 1 = [AllocEvent.alloc 14] := rfl
      refine r1b_call_frame <|
        r1b_call_alloc_placed (size := 14) (align := 1) hh hbnd hinv2
          (by simp only [hsm2, wp_norm, arm64_norm])
          (by simp only [hsm2, wp_norm, arm64_norm, hin1.run])
          (by simpa only [hsm2, wp_norm, arm64_norm] using hin1.sp)
          (by simpa only [hsm2, wp_norm, arm64_norm] using hin1.fp)
          (by simpa only [calleeSavedVRegs, hsm2, wp_norm, arm64_norm] using hin1.vregs)
          hst.spAligned (retOff := 0x0e00)
          (by simp only [hsm2, wp_norm, arm64_norm])
          (by simp only [hsm2, wp_norm, arm64_norm]) (by simp only [hsm2, wp_norm, arm64_norm])
          (by decide) (r1b_layout1 14) (by decide) (haev ▸ hfit) hpanic
          fun sf2 buf hin2 hcs2 hx0_buf hbuf _hmod hfs2 htr2 => ?_
      have hlive_eq : A.live buf 14 1 = A.repAlloc.live buf 14 1 := rfl
      rw [hlive_eq, haev]
      have hc2 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sf2 0x0e00 := hc1.after_call
        (by simp only [hsm2, wp_norm, arm64_norm]) (by simp only [hsm2, wp_norm, arm64_norm])
        (by simp only [hsm2, wp_norm, arm64_norm]) (by simp only [hsm2, wp_norm, arm64_norm])
        (by simp only [hsm2, wp_norm, arm64_norm])
        hin2 hcs2 (congrArg FsState.files hfs2) htr2
      have hbuf_f : (buf == 0#64) = false := beq_false_of_ne hbuf
      have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hin2.sp hst.spAligned
      have hpc2_in := hin2.pc; change sf2.pc = (blkPl_579).base + 0x0e00#64 at hpc2_in
      have hrun2_in := hin2.run
      apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x0e0c#64) hin2.inv
      dsimp only [runProgPlaced, lsProg_579]
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *])
      refine r1b_bind_state_placed fun sm_a hsm_a hinv_a => by
        have hvm_a : VmPreserved sf2 sm_a := by simp only [hsm_a, wp_norm, arm64_norm]
        rw [← A.pool_transport lim (M.stepEvents [AllocEvent.alloc 14] st) sf2 sm_a hvm_a]
        change SepWPp (runProgPlaced H) _ _ _ _ _ _
        have hin2 : InRunPlaced r1b_CodeOk s0 sm_a 0x0e0c :=
          { pc := by simp only [hsm_a, wp_norm, arm64_norm]
            run := by simp only [hsm_a, wp_norm, arm64_norm, hin2.run]
            sp := by simpa only [hsm_a, wp_norm, arm64_norm] using hin2.sp
            fp := by simpa only [hsm_a, wp_norm, arm64_norm] using hin2.fp
            inv := hinv_a
            vregs := by simpa only [calleeSavedVRegs, hsm_a, wp_norm, arm64_norm] using hin2.vregs
            spAligned := hst.spAligned }
        have hc2 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm_a 0x0e0c := hc2.of_step hin2
          (by simp only [hsm_a, wp_norm, arm64_norm]) (by simp only [hsm_a, wp_norm, arm64_norm])
          (by simp only [hsm_a, wp_norm, arm64_norm]) (by simp only [hsm_a, wp_norm, arm64_norm])
          (by simp only [hsm_a, wp_norm, arm64_norm])
        have hx0_buf : sm_a.readReg64 .x0 = buf := by
          simpa only [hsm_a, wp_norm, arm64_norm] using hx0_buf
        have hx8_ro : sm_a.readReg64 (.gpr 8#5) = lsρ r1b_malfSym := by
          simp only [hsm_a, wp_norm, arm64_norm]
        refine r1b_sepWPp_with_ro_placed hin2.inv r1b_ro_malformed_placed ?_
        obtain ⟨ro0, ro1, roRem, hroEq⟩ := r1b_ro_split14 (sm_a.readReg64 (.gpr 8#5))
        conv at hroEq => lhs; rw [hx8_ro]
        clear hsm_a hx8_ro
        rw [hroEq, r1b_buf14_split1 buf]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        refine SepWPp.exists_elim fun d0 => ?_
        have hpc2 := hin2.pc; change sm_a.pc = (blkPl_579).base + 0x0e0c#64 at hpc2
        have hrun2 := hin2.run; have hsp2 : sm_a.sp = fsp := hin2.sp
        apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x0e34#64) hin2.inv
        dsimp only [runProgPlaced, lsProg_579]
        by_vm_open (
          wp_steps
          refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
            (by simp only [wp_norm, arm64_norm, *])
            ⟨by simp only [wp_norm, arm64_norm, *], fun hvm3 => ?_⟩
          refine r1b_bind_state_placed fun sm3 hsm3 hinv3 => ?_
          rw [← hsm3] at hvm3
          rw [← A.pool_transport lim (M.stepEvents [AllocEvent.alloc 14] st) sm_a sm3 hvm3]
          change SepWPp (runProgPlaced H) _ _ _ _ _ _
          refine r1b_sepWPp_drop_left <| r1b_sepWPp_drop_left <| r1b_sepWPp_drop_left ?_
          refine r1b_sepWPp_frame (by r1b_ac) (r1b_buf14_realign buf _) (by r1b_ac) ?_
          simp only [sepExists_sepConj_left, sepConj_assoc]
          refine SepWPp.exists_elim fun d1 => ?_
          have hpc : sm3.pc = (blkPl_579).base + 0x0e34#64 := by
            simp only [hsm3, wp_norm, arm64_norm]
          have hrun : sm3.status = .Running := by
            simp only [hsm3, wp_norm, arm64_norm, hin2.run]
          have hr0 : sm3.readReg64 .x0 = buf := by
            simpa only [hsm3, wp_norm, arm64_norm] using hx0_buf
          apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x2b78#64) hinv3
          dsimp only [runProgPlaced, lsProg_579]
          apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
            (Q := (blkPC_579).rebase (blkPl_579).base
              (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException _))
            blkLib_eq_579 blk579_noSvc0 (mid := (blkPl_579).base + 0x2b78#64)
          intro _m_strip
          wp_steps
          refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
            (by simp only [wp_norm, arm64_norm, *]) fun _m_real hnsp => ?_
          have hvmp4 : VmPreserved sm3 _ :=
            hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
          simp only [State.setMem_setMem] at hvmp4 ⊢
          apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
          refine r1b_bind_state_placed fun sm4 hsm4 hinv4 => by
            have hvm4 : VmPreserved sm3 sm4 := hsm4 ▸ hvmp4
            rw [← A.pool_transport lim (M.stepEvents [AllocEvent.alloc 14] st) sm3 sm4 hvm4]
            change SepWPp (runProgPlaced H) _ _ _ _ _ _
            have hc4 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm4 0x2b78 := hc2.of_step
              { pc := by simp only [hsm4, wp_norm, arm64_norm]
                run := by simp only [hsm4, wp_norm, arm64_norm, hin2.run]
                sp := by simpa only [hsm4, hsm3, wp_norm, arm64_norm] using hin2.sp
                fp := by simpa only [hsm4, hsm3, wp_norm, arm64_norm] using hin2.fp
                inv := hinv4
                vregs := by
                  simpa only [calleeSavedVRegs, hsm4, hsm3, wp_norm, arm64_norm] using hin2.vregs
                spAligned := hst.spAligned }
              (by simp only [hsm4, wp_norm, arm64_norm]) (by simp only [hsm4, wp_norm, arm64_norm])
              (by simp only [hsm4, wp_norm, arm64_norm]) (by simp only [hsm4, wp_norm, arm64_norm])
              (by simp only [hsm4, wp_norm, arm64_norm])
            refine r1b_sepWPp_frame (by r1b_ac) (r1b_buf14_owned A.repAlloc buf _ hbuf)
              (by r1b_ac) ?_
            simp only [sepExists_sepConj_left, sepConj_assoc]
            refine SepWPp.exists_elim fun eBs => r1b_sepWPp_pure_left fun _ => ?_
            have hcl := r1b_cleanup_2b78_placed_env
              (st := M.stepEvents [AllocEvent.alloc 14] st)
              (regCap := regCap) (regPtr := regPtr)
              (regLen := BitVec.ofNat 64 regBs.length) (regBs := regBs)
              hh hdrop hbnd hc4 hpanic hrej
              (fun evsFree hfo => by
                rw [← M.stepEvents_append]
                exact henv evsFree hfo)
            dsimp only at hcl
            rw [r1b_errCommon_atState_eq, herrCore] at hcl
            refine sepWPp_weaken_pre ?_ hcl
            have hpay : ownedBytes A.repAlloc 14#64 buf 14#64 eBs ⊢
                r1b_SpePayload A.repAlloc (sm4.readReg64 (.gpr 12#5)) (sm4.readReg64 (.gpr 10#5))
                  (sm4.readReg64 (.gpr 23#5)) (sm4.readReg64 (.gpr 27#5))
                  (sm4.readReg64 (.gpr 16#5)) (sm4.readReg64 (.gpr 14#5))
                  (sm4.readReg64 (.gpr 15#5)) (sm4.readReg64 (.gpr 28#5))
                  (sm4.readReg64 (.gpr 2#5)) := by
              simp only [hsm4, wp_norm, arm64_norm]; r1b_prove_spe_str
            (try dsimp +zetaDelta only)
            generalize runFsp s0 = fsp0
            exact r1b_entails_frame (by r1b_ac) hpay (by r1b_ac)
        )
    )
  )

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpkPlacedBudgetAux
