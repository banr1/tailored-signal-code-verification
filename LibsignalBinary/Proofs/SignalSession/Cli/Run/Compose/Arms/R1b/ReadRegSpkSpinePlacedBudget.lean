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
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpkSpinePlacedBudgetAux
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSites

/-!
# Budget-Threaded Stage 1 Spine (`registration-id` and `signed-pre-key`) of Arm `R1b`

Proves `r1b_reg_dealloc_0784_placed` (`0x0784 → 0x1260`) and `r1b_step_reg_spk_placed`
(`0x074c → 0x1260`) on Block `579` under `[LibsignalPlacement]` and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpkSpinePlacedBudget

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalHooks LibsignalPlacement lsLogFilterAddr lsmpl lsρ)
open CryptoVerification.LibsignalTripleRatchetRepr (protocolAddressAt)
open CryptoVerification.SignalSession (lsReadFileSym lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli (StoresGhost ofLe32 splitSigned utf8)
open CryptoVerification.SignalSession.Cli.MainHops
  (RunCall cliIo cliWrOk coinsInstalledPlaced coinsOf inputOf ownedBytes runResSize sepWPp_weaken_pre
   storesAt)
open CryptoVerification.SignalSession.Cli.Run.Placed
  (blkLib_eq_579 blkPC_579 blkPl_579 lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (AtRunEntryPlaced Init1Data InRunPlaced PanicK RejectKind RunSem addrNameHeap addrUpperAt
   bundleNames r1b_CodeOk r1b_ErrCtxPlaced r1b_OkCtxPlaced r1b_StackBounds r1b_bind_state_placed
   r1b_cell64_cons r1b_cells3_to_region24 r1b_cmn1_false_of_lt63 r1b_entails_frame_core
   r1b_errCommon r1b_fsp_align r1b_init1Mem_unpack_placed r1b_init_path_facts_placed
   r1b_invCore_placed r1b_invCore_to_errCommon_placed r1b_join_region r1b_none_reg_rd
   r1b_ownedBytes_facts r1b_ownedBytes_zero r1b_region16_to_cells r1b_ro_reg_id_placed
   r1b_sepWPp_frame_core r1b_sepWPp_pure_left r1b_split_region runFiles runFsp runPcPlaced
   runPcPlaced_eq runProgPlaced runSaved)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets RunSlots runFrame)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs RustCliAllocBudget
   VmPreserved rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpersPlacedBudget
  (r1b_call_path_ro_placed r1b_call_readFile_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CommonPlacedBudget
  (r1b_call_dealloc_ownedBytes_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpkPlacedBudget
  (r1b_err_0c14_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpkPlacedBudgetAux
  (blk579_noSvc0)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpkSpinePlacedBudgetAux
  (freeOnlyEvs_r1bFreeCapEvs r1bFreeCapEvs_of_ne r1b_after_reg_dealloc_placed r1b_seq_lscro_oom)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget (RejectKPlacedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedBudget (init1MemPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget
  (DropSpeOwnedOkAtBlock)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
  (RunCalleesEnvs RunCalleesPlaced RunHooksPlaced)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local simp, local arm64_norm, local wp_norm] runPcPlaced_eq BitVec.ofNat_eq_ofNat

local macro (priority := high) "r1b_ac" : tactic =>
  `(tactic| ((try dsimp +zetaDelta only) <;> first | rfl | simp only [emp_sepConj] | sep_ac_rfl))

private meta def r1bStripLetsSP : Nat → Lean.Expr → Lean.Expr
  | 0, e => e
  | n + 1, .letE _ _ v b _ => r1bStripLetsSP n (b.instantiate1 v)
  | n + 1, .mdata _ e => r1bStripLetsSP n e
  | _, e => e

private meta def r1bSplitSepSP : Nat → Lean.Expr → Lean.Expr → Array Lean.Expr
  | 0, _, e => #[e]
  | fuel + 1, sepSample, e =>
    let e := r1bStripLetsSP 64 e
    let fn := sepSample.getAppFn.constName!
    let ar := sepSample.getAppNumArgs
    if e.isAppOfArity fn ar then
      r1bSplitSepSP fuel sepSample (e.getArg! (ar - 2)) ++
        r1bSplitSepSP fuel sepSample (e.getArg! (ar - 1))
    else #[e]

private meta def r1bIsDefEqPureSP (x a : Lean.Expr) : Lean.Elab.TermElabM Bool := do
  let x := r1bStripLetsSP 64 x; let a := r1bStripLetsSP 64 a
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

private meta def r1bComputeRestSP (ctxName : String) (p a1 : Lean.Expr) : Lean.Elab.TermElabM Lean.Expr := do
  let sepTy := Lean.mkConst ``SepProp []
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let ps := (r1bSplitSepSP 64 sepSample (← Lean.instantiateMVars p)).toList
  let a1s := (r1bSplitSepSP 64 sepSample (← Lean.instantiateMVars a1)).toList
  let mut rem := ps
  for a in a1s do
    let mut removed := false
    let mut next : List Lean.Expr := []
    for x in rem do
      if !removed && (← r1bIsDefEqPureSP x a) then removed := true
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

local elab (priority := high) "r1b_entails_frame " t1:term:arg h:term:arg t2:term:arg : term <= expectedType => do
  let exp ← Lean.instantiateMVars expectedType
  if exp.isMVar then Lean.Elab.Term.tryPostpone
  let entSample ← Lean.Elab.Term.elabTerm (← `(emp ⊢ emp)) none
  let ear := entSample.getAppNumArgs
  let expS := r1bStripLetsSP 64 exp
  let p := expS.getArg! (ear - 2)
  let q := expS.getArg! (ear - 1)
  if (← Lean.instantiateMVars p).isMVar then Lean.Elab.Term.tryPostpone
  if (← Lean.instantiateMVars q).isMVar then Lean.Elab.Term.tryPostpone
  let hExpr ← Lean.Elab.Term.elabTerm h none
  let hTy := r1bStripLetsSP 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
  let a1 := hTy.getArg! (ear - 2)
  let a2 := hTy.getArg! (ear - 1)
  let r ← r1bComputeRestSP "r1b_entails_frame" p a1
  let sepTy := Lean.mkConst ``SepProp []
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let sar := sepSample.getAppNumArgs
  let mkSep (x y : Lean.Expr) : Lean.Expr :=
    sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
  let rIsEmp ← r1bIsDefEqPureSP r empExpr
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
    Lean.Meta.mkAppOptM ``r1b_entails_frame_core #[some a1, some a2, some r, some p, some q, h1Expr, hExpr, h2Expr]

local elab (priority := high) "r1b_sepWPp_frame " t1:term:arg h:term:arg t2:term:arg hk:term:arg : term <= expectedType => do
  let exp ← Lean.instantiateMVars expectedType
  if exp.isMVar then Lean.Elab.Term.tryPostpone
  let expS := r1bStripLetsSP 64 exp
  let args := expS.getAppArgs
  let prog := args[0]!; let ret := args[1]!; let st := args[2]!; let p := args[3]!
  let q := args[4]!; let qp := args[5]!; let oom := args[6]!
  let entSample ← Lean.Elab.Term.elabTerm (← `(emp ⊢ emp)) none
  let ear := entSample.getAppNumArgs
  let hExpr ← Lean.Elab.Term.elabTerm h none
  let hTy := r1bStripLetsSP 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
  let a1 := hTy.getArg! (ear - 2)
  let a2 := hTy.getArg! (ear - 1)
  let r ← r1bComputeRestSP "r1b_sepWPp_frame" p a1
  let sepTy := Lean.mkConst ``SepProp []
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let sar := sepSample.getAppNumArgs
  let mkSep (x y : Lean.Expr) : Lean.Expr :=
    sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
  let rIsEmp ← r1bIsDefEqPureSP r empExpr
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
    let a2IsEmp ← r1bIsDefEqPureSP a2 empExpr
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
  let expS := r1bStripLetsSP 64 exp
  let hExpr ← Lean.Elab.Term.elabTerm h none
  let hTy0 := r1bStripLetsSP 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
  for idx in [0, 1, 2, 4, 5, 6] do
    if !(← Lean.Meta.withReducibleAndInstances <| Lean.Meta.isDefEq (hTy0.getArg! idx) (expS.getArg! idx)) then
      discard <| Lean.Meta.isDefEq (hTy0.getArg! idx) (expS.getArg! idx)
  let p ← Lean.instantiateMVars (expS.getArg! 3)
  let p' ← Lean.instantiateMVars ((r1bStripLetsSP 64 (← Lean.instantiateMVars hTy0)).getArg! 3)
  let sepTy := Lean.mkConst ``SepProp []
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let sar := sepSample.getAppNumArgs
  let mkSep (x y : Lean.Expr) : Lean.Expr :=
    sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
  let ps := (r1bSplitSepSP 64 sepSample p).toList
  let p's := (r1bSplitSepSP 64 sepSample p').toList
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
      if !removed && (← r1bIsDefEqPureSP x a) then removed := true
      else next := next.concat x
    if !removed then
      throwError "r1b_call_frame: unmatched callee atom:\n  {a}\nin:\n  {rem}"
    rem := next
  let remProd := match rem.reverse with
    | [] => empExpr
    | last :: rest => rest.foldl (fun acc x => mkSep x acc) last
  if let some mf := mvarFOpt then
    discard <| Lean.Meta.withReducibleAndInstances <| Lean.Meta.isDefEq mf remProd
  let eqTy ← Lean.Meta.mkEq (← Lean.instantiateMVars p) (← Lean.instantiateMVars p')
  let eqProof ← Lean.Elab.Term.elabTerm (← `(by r1b_ac)) (some eqTy)
  let ent ← Lean.Meta.mkAppM ``Entails.of_eq #[eqProof]
  Lean.Meta.mkAppM ``sepWPp_weaken_pre #[ent, hExpr]

set_option maxHeartbeats 1000000 in
theorem r1b_reg_dealloc_0784_placed [LibsignalPlacement] {M : AllocCostModel}
    {S : RunSem} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {cEnvs : RunCalleesEnvs} {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets} {σ : RunSlots}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {pCap pPtr regCap regPtr : BitVec 64}
    {pBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hc : RunCalleesPlaced A lim cEnvs H B σ)
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (he : AtRunEntryPlaced r1b_CodeOk S g s0)
    (hok : r1b_OkCtxPlaced r1b_CodeOk S g d s0 s 0x0784)
    (hreg_rd : cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") = .ok regBs)
    (hx26 : s.readReg64 (.gpr 26#5) = d.dirPtr)
    (hx27 : s.readReg64 (.gpr 27#5) = pPtr)
    (hx28 : s.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length)
    (hfit_bad_reg : ∀ evsFreeR, FreeOnlyEvs evsFreeR → regBs.length ≠ 4 →
      FitsEvents M lim (M.stepEvents evsFreeR st) [AllocEvent.alloc 14])
    (henv_bad_reg : ∀ evsFreeR evsFree, FreeOnlyEvs evsFreeR → regBs.length ≠ 4 →
      FreeOnlyEvs evsFree →
      EnvAt StoresGhost.opened .postDispatch
        (M.stepEvents (evsFreeR ++ [AllocEvent.alloc 14] ++ evsFree) st))
    (hfit_spk_path : ∀ evsFreeR, FreeOnlyEvs evsFreeR → regBs.length = 4 →
      FitsEnv M lim (M.stepEvents evsFreeR st) (PathEnv d.dir (utf8 "signed-pre-key")))
    (hfit_spk_rd : ∀ evsFreeR evsP, FreeOnlyEvs evsFreeR → regBs.length = 4 →
      PathEnv d.dir (utf8 "signed-pre-key") evsP →
      FitsEnv M lim (M.stepEvents (evsFreeR ++ evsP) st)
        (cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key")))
    (hfit_spk_rd_err : ∀ evsFreeR evsP evsRd, FreeOnlyEvs evsFreeR → regBs.length = 4 →
      PathEnv d.dir (utf8 "signed-pre-key") evsP →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") = .error () →
      cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") evsRd →
      FitsEvents M lim (M.stepEvents (evsFreeR ++ evsP ++ evsRd) st) [AllocEvent.alloc 22])
    (henv_spk_rd_err : ∀ evsFreeR evsP evsRd evsFree, FreeOnlyEvs evsFreeR → regBs.length = 4 →
      PathEnv d.dir (utf8 "signed-pre-key") evsP →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") = .error () →
      cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") evsRd →
      FreeOnlyEvs evsFree →
      EnvAt StoresGhost.opened .postDispatch
        (M.stepEvents (evsFreeR ++ evsP ++ evsRd ++ [AllocEvent.alloc 22] ++ evsFree) st))
    (hfit_spk_split : ∀ evsFreeR evsP evsRd evsFree spkBs, FreeOnlyEvs evsFreeR →
      regBs.length = 4 →
      PathEnv d.dir (utf8 "signed-pre-key") evsP →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") = .ok spkBs →
      cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") evsRd →
      FreeOnlyEvs evsFree →
      FitsEnv M lim (M.stepEvents (evsFreeR ++ evsP ++ evsRd ++ evsFree) st)
        (cEnvs.splitSigned spkBs))
    (henv_spk_split_err : ∀ evsFreeR evsP evsRd evsFree1 spkBs evsSp evsFree2,
      FreeOnlyEvs evsFreeR → regBs.length = 4 →
      PathEnv d.dir (utf8 "signed-pre-key") evsP →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") = .ok spkBs →
      cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") evsRd →
      FreeOnlyEvs evsFree1 →
      splitSigned spkBs = none →
      cEnvs.splitSigned spkBs evsSp →
      FreeOnlyEvs evsFree2 →
      EnvAt StoresGhost.opened .postDispatch
        (M.stepEvents (evsFreeR ++ evsP ++ evsRd ++ evsFree1 ++ evsSp ++ evsFree2) st))
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectKPlacedEnv r1b_CodeOk H A lim EnvAt g s0 resStack Q Qp oom)
    (hk : ∀ (sf : State) (evsFreeR evsP evsRd evsFreeS evsSp : List AllocEvent)
        (r0 r1 r2 r3 : BitVec 8)
        (spkCap spkPtr : BitVec 64) (spkBs spkKey spkSig : List (BitVec 8)) (spkId : BitVec 32),
      FreeOnlyEvs evsFreeR →
      PathEnv d.dir (utf8 "signed-pre-key") evsP →
      cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") evsRd →
      FreeOnlyEvs evsFreeS →
      cEnvs.splitSigned spkBs evsSp →
      r1b_OkCtxPlaced r1b_CodeOk S g d s0 sf 0x1260 →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") =
        .ok [r0, r1, r2, r3] →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") = .ok spkBs →
      splitSigned spkBs = some (spkId, spkKey, spkSig) →
      sf.readReg64 (.gpr 10#5) = spkPtr + 4#64 →
      sf.readReg64 (.gpr 27#5) = BitVec.ofNat 64 spkKey.length →
      sf.readReg64 .x2 = spkId.zeroExtend 64 →
      sf.readReg64 (.gpr 26#5) = d.dirPtr →
      sf.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length →
      let fsp := runFsp s0
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (((fsp + 0x4f0#64) ↦₆₄ (spkPtr + 4#64 + BitVec.ofNat 64 spkKey.length)) ∗
          ((fsp + 0x4f8#64) ↦₆₄ 64#64) ∗
          memRegion (fsp + 0x4d0#64) 32 ∗
          ownedBytes A.repAlloc spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
          ownedBytes A.repAlloc regCap regPtr 4#64 [r0, r1, r2, r3] ∗
          r1b_invCore_placed A.repAlloc g d s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
          ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
          memRegion fsp 0x110 ∗
          memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
          memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
          memRegion (fsp + 0x150#64) 16 ∗
          ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
          ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
          memRegion (fsp + 0x178#64) 8 ∗
          memRegion (fsp + 0x188#64) 8 ∗ ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
          ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
          ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
          ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
          memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
          stackAt fsp (resStack - runFrame) ∗
          A.pool lim (M.stepEvents (evsFreeR ++ evsP ++ evsRd ++ evsFreeS ++ evsSp) st) sf)
        Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (((fsp + 0x4d0#64) ↦₆₄ pCap) ∗ memRegion (fsp + 0x4d8#64) 40 ∗
        ownedBytes A.repAlloc pCap pPtr (BitVec.ofNat 64 pBs.length) pBs ∗
        ((fsp + 0x1750#64) ↦₆₄ regCap) ∗ ((fsp + 0x1758#64) ↦₆₄ regPtr) ∗
        ((fsp + 0x1760#64) ↦₆₄ BitVec.ofNat 64 regBs.length) ∗
        ownedBytes A.repAlloc regCap regPtr (BitVec.ofNat 64 regBs.length) regBs ∗
        r1b_invCore_placed A.repAlloc g d s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
        memRegion fsp 0x110 ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
        memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x164#64) 4 ∗
        memRegion (fsp + 0x168#64) 8 ∗ memRegion (fsp + 0x170#64) 8 ∗
        memRegion (fsp + 0x178#64) 8 ∗
        memRegion (fsp + 0x188#64) 8 ∗ ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
        memRegion (fsp + 0x198#64) 16 ∗ ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
        ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
        memRegion (fsp + 0x1b4#64) 4 ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s)
      Q Qp oom := by
  intro fsp
  let _ := hx26; let _ := hx27; let _ := hx28
  generalize hinvCore : r1b_invCore_placed A.repAlloc g d s0 = invCore
  have hst := hok.st
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hst.spAligned
  have hpc_in := hst.pc; change s.pc = (blkPl_579).base + 0x0784#64 at hpc_in
  refine r1b_sepWPp_frame (by r1b_ac)
    (r1b_ownedBytes_facts A.repAlloc regCap regPtr (BitVec.ofNat 64 regBs.length) regBs)
    (by r1b_ac) ?_
  try simp only [sepConj_assoc]
  refine r1b_sepWPp_pure_left fun ⟨_, hreg_cap, _, _⟩ => ?_
  have hcmn_reg : (regCap + 1#64 == 0#64) = false :=
    beq_false_of_ne (r1b_cmn1_false_of_lt63 hreg_cap)
  let _ := hcmn_reg
  have h198_sp := r1b_region16_to_cells (fsp + 0x198#64)
  have h1a0_eq : (fsp + 0x198#64) + 8#64 = fsp + 0x1a0#64 := by bv_omega
  rw [h1a0_eq] at h198_sp
  rw [h198_sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  try simp only [sepConj_assoc]
  refine SepWPp.exists_elim fun _v198 => SepWPp.exists_elim fun _v1a0 => ?_
  by_cases hpCap : pCap = 0#64
  · subst hpCap
    have hfo0 : FreeOnlyEvs ([] : List AllocEvent) := fun _ h => nomatch h
    have hpc := hpc_in; have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
    apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x0c6c#64) hst.inv
    dsimp only [runProgPlaced, lsProg_579]
    apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
      blkLib_eq_579 blk579_noSvc0 (mid := (blkPl_579).base + 0x0c6c#64)
    intro _m_strip; wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [wp_norm, arm64_norm, *]) fun _m_real hnsp3 => ?_
    have hvmp3 : VmPreserved s _ := hnsp3.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
    try simp only [State.setMem_setMem] at hvmp3 ⊢
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
    refine r1b_bind_state_placed fun sm3 hsm3 hinv3 => by
      have hvm3 : VmPreserved s sm3 := hsm3 ▸ hvmp3
      rw [← A.pool_transport lim st s sm3 hvm3]
      change SepWPp (runProgPlaced H) _ _ _ _ _ _
      have hok3 : r1b_OkCtxPlaced r1b_CodeOk S g d s0 sm3 0x0c6c := hok.of_step
        { pc := by simp only [hsm3, wp_norm, arm64_norm]
          run := by simp only [hsm3, wp_norm, arm64_norm, hst.run]
          sp := by simpa only [hsm3, wp_norm, arm64_norm] using hst.sp
          fp := by simpa only [hsm3, wp_norm, arm64_norm] using hst.fp
          inv := hinv3
          vregs := by simpa only [calleeSavedVRegs, hsm3, wp_norm, arm64_norm] using hst.vregs
          spAligned := hst.spAligned }
        (by simp only [hsm3, wp_norm, arm64_norm]) (by simp only [hsm3, wp_norm, arm64_norm])
        (by simp only [hsm3, wp_norm, arm64_norm]) (by simp only [hsm3, wp_norm, arm64_norm])
        (by simp only [hsm3, wp_norm, arm64_norm]) (by simp only [hsm3, wp_norm, arm64_norm])
      have h1750 :
          ((fsp + 0x1750#64) ↦₆₄ regCap) ∗ ((fsp + 0x1758#64) ↦₆₄ regPtr) ∗
            ((fsp + 0x1760#64) ↦₆₄ BitVec.ofNat 64 regBs.length) ⊢
            memRegion (fsp + 0x1750#64) 24 := by
        simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
          r1b_cells3_to_region24 (fsp + 0x1750#64) regCap regPtr (BitVec.ofNat 64 regBs.length)
      have h4d0 : ((fsp + 0x4d0#64) ↦₆₄ 0#64) ∗ memRegion (fsp + 0x4d8#64) 40 ⊢
          memRegion (fsp + 0x4d0#64) 48 := by
        simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
          r1b_cell64_cons (a := fsp + 0x4d0#64) 0#64 (n := 40) (by decide)
      refine r1b_sepWPp_frame (by r1b_ac)
        (r1b_ownedBytes_zero A.repAlloc pPtr (BitVec.ofNat 64 pBs.length) pBs)
        (by simp only [emp_sepConj]) ?_
      refine sepWPp_weaken_pre ?_
        (r1b_after_reg_dealloc_placed (st := st) (regCap := regCap) (regPtr := regPtr) (regBs := regBs)
          hh hc hdrop hbnd he hok3 hreg_rd
          (by simp only [hsm3, wp_norm, arm64_norm])
          (by simp only [hsm3, wp_norm, arm64_norm])
          (by simp only [hsm3, wp_norm, arm64_norm]; try exact hx26)
          (by simp only [hsm3, wp_norm, arm64_norm]; try exact hx28)
          (fun hne => by simpa only [M.stepEvents_nil] using hfit_bad_reg [] hfo0 hne)
          (fun evsFree hne hfo => by
            simpa only [List.nil_append] using henv_bad_reg [] evsFree hfo0 hne hfo)
          (fun heq => by simpa only [M.stepEvents_nil] using hfit_spk_path [] hfo0 heq)
          (fun evsP heq hp => by
            simpa only [List.nil_append] using hfit_spk_rd [] evsP hfo0 heq hp)
          (fun evsP evsRd heq hp herr hrd => by
            simpa only [List.nil_append] using hfit_spk_rd_err [] evsP evsRd hfo0 heq hp herr hrd)
          (fun evsP evsRd evsFree heq hp herr hrd hfo => by
            simpa only [List.nil_append] using
              henv_spk_rd_err [] evsP evsRd evsFree hfo0 heq hp herr hrd hfo)
          (fun evsP evsRd evsFree spkBs heq hp hok_s hrd hfo => by
            simpa only [List.nil_append] using
              hfit_spk_split [] evsP evsRd evsFree spkBs hfo0 heq hp hok_s hrd hfo)
          (fun evsP evsRd evsFree1 spkBs evsSp evsFree2 heq hp hok_s hrd hfo1 hnone hsp hfo2 => by
            simpa only [List.nil_append] using
              henv_spk_split_err [] evsP evsRd evsFree1 spkBs evsSp evsFree2
                hfo0 heq hp hok_s hrd hfo1 hnone hsp hfo2)
          hpanic hrej
          fun sf4 evsP evsRd evsFreeS evsSp r0 r1 r2 r3 spkCap spkPtr spkBs spkKey spkSig spkId
              hp hrd hfoS hsp hok4 hr hs hsp_s hx10_4 hx27_4 hx2_4 hx26_4 hx28_4 => by
            simpa only [List.nil_append] using
              hk sf4 [] evsP evsRd evsFreeS evsSp r0 r1 r2 r3 spkCap spkPtr spkBs spkKey spkSig spkId
                hfo0 hp hrd hfoS hsp hok4 hr hs hsp_s hx10_4 hx27_4 hx2_4 hx26_4 hx28_4)
      try dsimp only
      rw [hinvCore]
      exact r1b_entails_frame (by r1b_ac) (sepConj_mono h4d0 h1750) (by r1b_ac)
  · have hpCap_f : (pCap == 0#64) = false := beq_false_of_ne hpCap
    let _ := hpCap_f
    have hfo_p : FreeOnlyEvs (rustDeallocEvents pCap.toNat 1) := by
      simpa only [r1bFreeCapEvs_of_ne hpCap] using freeOnlyEvs_r1bFreeCapEvs pCap
    have hpc := hpc_in; have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
    apply r1b_seq_lscro_oom (mid := lsρ lsRustDeallocSymCli) hst.inv
    dsimp only [runProgPlaced, lsProg_579]
    apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
      blkLib_eq_579 blk579_noSvc0 (mid := lsρ lsRustDeallocSymCli)
    intro _m_strip; wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [wp_norm, arm64_norm, *]) fun _m_real hnsp3 => ?_
    have hvmp3 : VmPreserved s _ := hnsp3.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
    try simp only [State.setMem_setMem] at hvmp3 ⊢
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
    refine r1b_bind_state_placed fun sm3 hsm3 hinv3 => by
      have hvm3 : VmPreserved s sm3 := hsm3 ▸ hvmp3
      rw [← A.pool_transport lim st s sm3 hvm3]
      change SepWPp (runProgPlaced H) _ _ _ _ _ _
      refine r1b_call_frame <|
        r1b_call_dealloc_ownedBytes_placed (ptr := pPtr) (cap := pCap) (bs := pBs) hh hbnd hinv3
          (by simp only [hsm3, wp_norm, arm64_norm])
          (by simp only [hsm3, wp_norm, arm64_norm, hst.run])
          (by simpa only [hsm3, wp_norm, arm64_norm] using hst.sp)
          (by simpa only [hsm3, wp_norm, arm64_norm] using hst.fp)
          (by simpa only [calleeSavedVRegs, hsm3, wp_norm, arm64_norm] using hst.vregs)
          hst.spAligned (retOff := 0x0c68)
          (by simp only [hsm3, wp_norm, arm64_norm])
          (by simp only [hsm3, wp_norm, arm64_norm]; try exact hx27)
          (by simp only [hsm3, wp_norm, arm64_norm]) (by simp only [hsm3, wp_norm, arm64_norm])
          hpCap hpanic
          fun sf3 hin3 hcs3 hfs3 htr3 => ?_
      have hok3 : r1b_OkCtxPlaced r1b_CodeOk S g d s0 sf3 0x0c68 := hok.after_call
        (by simp only [hsm3, wp_norm, arm64_norm]) (by simp only [hsm3, wp_norm, arm64_norm])
        (by simp only [hsm3, wp_norm, arm64_norm]) (by simp only [hsm3, wp_norm, arm64_norm])
        (by simp only [hsm3, wp_norm, arm64_norm]) (by simp only [hsm3, wp_norm, arm64_norm])
        hin3 hcs3 (congrArg FsState.files hfs3) htr3
      have hx23_3 : sf3.readReg64 (.gpr 23#5) = regCap :=
        hcs3.2.2.2.2.1.trans (by simp only [hsm3, wp_norm, arm64_norm])
      have hx25_3 : sf3.readReg64 (.gpr 25#5) = BitVec.ofNat 64 regBs.length :=
        hcs3.2.2.2.2.2.2.1.trans (by simp only [hsm3, wp_norm, arm64_norm])
      have hx26_3 : sf3.readReg64 (.gpr 26#5) = d.dirPtr :=
        hcs3.2.2.2.2.2.2.2.1.trans (by simp only [hsm3, wp_norm, arm64_norm]; try exact hx26)
      have hx28_3 : sf3.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length :=
        hcs3.2.2.2.2.2.2.2.2.2.1.trans (by simp only [hsm3, wp_norm, arm64_norm]; try exact hx28)
      let _ := hx23_3; let _ := hx25_3; let _ := hx26_3; let _ := hx28_3
      have hpc3 := hin3.pc; change sf3.pc = (blkPl_579).base + 0x0c68#64 at hpc3
      have hpc := hpc3; have hrun := hin3.run; have hsp : sf3.sp = fsp := hin3.sp
      apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x0c6c#64) hin3.inv
      dsimp only [runProgPlaced, lsProg_579]
      apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
        blkLib_eq_579 blk579_noSvc0 (mid := (blkPl_579).base + 0x0c6c#64)
      intro _m_strip; wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *]) fun _m_real hnsp4 => ?_
      have hvmp4 : VmPreserved sf3 _ := hnsp4.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
      try simp only [State.setMem_setMem] at hvmp4 ⊢
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
      refine r1b_bind_state_placed fun sm4 hsm4 hinv4 => by
        have hvm4 : VmPreserved sf3 sm4 := hsm4 ▸ hvmp4
        rw [← A.pool_transport lim (M.stepEvents (rustDeallocEvents pCap.toNat 1) st) sf3 sm4 hvm4]
        change SepWPp (runProgPlaced H) _ _ _ _ _ _
        have hok4 : r1b_OkCtxPlaced r1b_CodeOk S g d s0 sm4 0x0c6c := hok3.of_step
          { pc := by simp only [hsm4, wp_norm, arm64_norm]
            run := by simp only [hsm4, wp_norm, arm64_norm, hin3.run]
            sp := by simpa only [hsm4, wp_norm, arm64_norm] using hin3.sp
            fp := by simpa only [hsm4, wp_norm, arm64_norm] using hin3.fp
            inv := hinv4
            vregs := by simpa only [calleeSavedVRegs, hsm4, wp_norm, arm64_norm] using hin3.vregs
            spAligned := hst.spAligned }
          (by simp only [hsm4, wp_norm, arm64_norm]) (by simp only [hsm4, wp_norm, arm64_norm])
          (by simp only [hsm4, wp_norm, arm64_norm]) (by simp only [hsm4, wp_norm, arm64_norm])
          (by simp only [hsm4, wp_norm, arm64_norm]) (by simp only [hsm4, wp_norm, arm64_norm])
        have h1750 :
            ((fsp + 0x1750#64) ↦₆₄ regCap) ∗ ((fsp + 0x1758#64) ↦₆₄ regPtr) ∗
              ((fsp + 0x1760#64) ↦₆₄ BitVec.ofNat 64 regBs.length) ⊢
              memRegion (fsp + 0x1750#64) 24 := by
          simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
            r1b_cells3_to_region24 (fsp + 0x1750#64) regCap regPtr (BitVec.ofNat 64 regBs.length)
        have h4d0 : ((fsp + 0x4d0#64) ↦₆₄ pCap) ∗ memRegion (fsp + 0x4d8#64) 40 ⊢
            memRegion (fsp + 0x4d0#64) 48 := by
          simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
            r1b_cell64_cons (a := fsp + 0x4d0#64) pCap (n := 40) (by decide)
        refine sepWPp_weaken_pre ?_
          (r1b_after_reg_dealloc_placed
            (st := M.stepEvents (rustDeallocEvents pCap.toNat 1) st)
            (regCap := regCap) (regPtr := regPtr) (regBs := regBs)
            hh hc hdrop hbnd he hok4 hreg_rd
            (by simp only [hsm4, wp_norm, arm64_norm]; try exact hx23_3)
            (by simp only [hsm4, wp_norm, arm64_norm]; try exact hx25_3)
            (by simp only [hsm4, wp_norm, arm64_norm]; try exact hx26_3)
            (by simp only [hsm4, wp_norm, arm64_norm]; try exact hx28_3)
            (hfit_bad_reg (rustDeallocEvents pCap.toNat 1) hfo_p)
            (fun evsFree hne hfo => by
              simpa only [M.stepEvents_append, List.append_assoc] using
                henv_bad_reg (rustDeallocEvents pCap.toNat 1) evsFree hfo_p hne hfo)
            (hfit_spk_path (rustDeallocEvents pCap.toNat 1) hfo_p)
            (fun evsP heq hp => by
              simpa only [M.stepEvents_append, List.append_assoc] using
                hfit_spk_rd (rustDeallocEvents pCap.toNat 1) evsP hfo_p heq hp)
            (fun evsP evsRd heq hp herr hrd => by
              simpa only [M.stepEvents_append, List.append_assoc] using
                hfit_spk_rd_err (rustDeallocEvents pCap.toNat 1) evsP evsRd hfo_p heq hp herr hrd)
            (fun evsP evsRd evsFree heq hp herr hrd hfo => by
              simpa only [M.stepEvents_append, List.append_assoc] using
                henv_spk_rd_err (rustDeallocEvents pCap.toNat 1) evsP evsRd evsFree
                  hfo_p heq hp herr hrd hfo)
            (fun evsP evsRd evsFree spkBs heq hp hok_s hrd hfo => by
              simpa only [M.stepEvents_append, List.append_assoc] using
                hfit_spk_split (rustDeallocEvents pCap.toNat 1) evsP evsRd evsFree spkBs
                  hfo_p heq hp hok_s hrd hfo)
            (fun evsP evsRd evsFree1 spkBs evsSp evsFree2 heq hp hok_s hrd hfo1 hnone hsp hfo2 => by
              simpa only [M.stepEvents_append, List.append_assoc] using
                henv_spk_split_err (rustDeallocEvents pCap.toNat 1) evsP evsRd evsFree1
                  spkBs evsSp evsFree2 hfo_p heq hp hok_s hrd hfo1 hnone hsp hfo2)
            hpanic hrej
            fun sf4 evsP evsRd evsFreeS evsSp r0 r1 r2 r3 spkCap spkPtr spkBs spkKey spkSig spkId
                hp hrd hfoS hsp hok4 hr hs hsp_s hx10_4 hx27_4 hx2_4 hx26_4 hx28_4 => by
              simpa only [M.stepEvents_append, List.append_assoc] using
                hk sf4 (rustDeallocEvents pCap.toNat 1) evsP evsRd evsFreeS evsSp
                  r0 r1 r2 r3 spkCap spkPtr spkBs spkKey spkSig spkId
                  hfo_p hp hrd hfoS hsp hok4 hr hs hsp_s hx10_4 hx27_4 hx2_4 hx26_4 hx28_4)
        try dsimp only
        rw [hinvCore]
        exact r1b_entails_frame (by r1b_ac) (sepConj_mono h4d0 h1750) (by r1b_ac)

set_option maxHeartbeats 1200000 in
theorem r1b_step_reg_spk_placed [LibsignalPlacement] {M : AllocCostModel}
    {S : RunSem} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {cEnvs : RunCalleesEnvs} {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets} {σ : RunSlots}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hc : RunCalleesPlaced A lim cEnvs H B σ)
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (he : AtRunEntryPlaced r1b_CodeOk S g s0)
    (hok : r1b_OkCtxPlaced r1b_CodeOk S g d s0 s 0x074c)
    (hx28 : s.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length)
    (hfit_reg_path : FitsEnv M lim st (PathEnv d.dir (utf8 "registration-id")))
    (hfit_reg_rd : ∀ evsRegP, PathEnv d.dir (utf8 "registration-id") evsRegP →
      FitsEnv M lim (M.stepEvents evsRegP st)
        (cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id")))
    (hfit_reg_rd_err : ∀ evsRegP evsRegRd,
      PathEnv d.dir (utf8 "registration-id") evsRegP →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") = .error () →
      cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") evsRegRd →
      FitsEvents M lim (M.stepEvents (evsRegP ++ evsRegRd) st) [AllocEvent.alloc 22])
    (henv_reg_rd_err : ∀ evsRegP evsRegRd evsFree,
      PathEnv d.dir (utf8 "registration-id") evsRegP →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") = .error () →
      cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") evsRegRd →
      FreeOnlyEvs evsFree →
      EnvAt StoresGhost.opened .postDispatch
        (M.stepEvents (evsRegP ++ evsRegRd ++ [AllocEvent.alloc 22] ++ evsFree) st))
    (hfit_bad_reg : ∀ evsRegP evsRegRd evsFreeR regBs,
      PathEnv d.dir (utf8 "registration-id") evsRegP →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") = .ok regBs →
      cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") evsRegRd →
      FreeOnlyEvs evsFreeR → regBs.length ≠ 4 →
      FitsEvents M lim (M.stepEvents (evsRegP ++ evsRegRd ++ evsFreeR) st) [AllocEvent.alloc 14])
    (henv_bad_reg : ∀ evsRegP evsRegRd evsFreeR regBs evsFree,
      PathEnv d.dir (utf8 "registration-id") evsRegP →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") = .ok regBs →
      cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") evsRegRd →
      FreeOnlyEvs evsFreeR → regBs.length ≠ 4 → FreeOnlyEvs evsFree →
      EnvAt StoresGhost.opened .postDispatch
        (M.stepEvents (evsRegP ++ evsRegRd ++ evsFreeR ++ [AllocEvent.alloc 14] ++ evsFree) st))
    (hfit_spk_path : ∀ evsRegP evsRegRd evsFreeR regBs,
      PathEnv d.dir (utf8 "registration-id") evsRegP →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") = .ok regBs →
      cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") evsRegRd →
      FreeOnlyEvs evsFreeR → regBs.length = 4 →
      FitsEnv M lim (M.stepEvents (evsRegP ++ evsRegRd ++ evsFreeR) st)
        (PathEnv d.dir (utf8 "signed-pre-key")))
    (hfit_spk_rd : ∀ evsRegP evsRegRd evsFreeR regBs evsSpkP,
      PathEnv d.dir (utf8 "registration-id") evsRegP →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") = .ok regBs →
      cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") evsRegRd →
      FreeOnlyEvs evsFreeR → regBs.length = 4 →
      PathEnv d.dir (utf8 "signed-pre-key") evsSpkP →
      FitsEnv M lim (M.stepEvents (evsRegP ++ evsRegRd ++ evsFreeR ++ evsSpkP) st)
        (cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key")))
    (hfit_spk_rd_err : ∀ evsRegP evsRegRd evsFreeR regBs evsSpkP evsSpkRd,
      PathEnv d.dir (utf8 "registration-id") evsRegP →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") = .ok regBs →
      cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") evsRegRd →
      FreeOnlyEvs evsFreeR → regBs.length = 4 →
      PathEnv d.dir (utf8 "signed-pre-key") evsSpkP →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") = .error () →
      cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") evsSpkRd →
      FitsEvents M lim
        (M.stepEvents (evsRegP ++ evsRegRd ++ evsFreeR ++ evsSpkP ++ evsSpkRd) st)
        [AllocEvent.alloc 22])
    (henv_spk_rd_err : ∀ evsRegP evsRegRd evsFreeR regBs evsSpkP evsSpkRd evsFree,
      PathEnv d.dir (utf8 "registration-id") evsRegP →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") = .ok regBs →
      cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") evsRegRd →
      FreeOnlyEvs evsFreeR → regBs.length = 4 →
      PathEnv d.dir (utf8 "signed-pre-key") evsSpkP →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") = .error () →
      cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") evsSpkRd →
      FreeOnlyEvs evsFree →
      EnvAt StoresGhost.opened .postDispatch
        (M.stepEvents
          (evsRegP ++ evsRegRd ++ evsFreeR ++ evsSpkP ++ evsSpkRd ++
            [AllocEvent.alloc 22] ++ evsFree) st))
    (hfit_spk_split : ∀ evsRegP evsRegRd evsFreeR regBs evsSpkP evsSpkRd evsFreeS spkBs,
      PathEnv d.dir (utf8 "registration-id") evsRegP →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") = .ok regBs →
      cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") evsRegRd →
      FreeOnlyEvs evsFreeR → regBs.length = 4 →
      PathEnv d.dir (utf8 "signed-pre-key") evsSpkP →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") = .ok spkBs →
      cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") evsSpkRd →
      FreeOnlyEvs evsFreeS →
      FitsEnv M lim
        (M.stepEvents (evsRegP ++ evsRegRd ++ evsFreeR ++ evsSpkP ++ evsSpkRd ++ evsFreeS) st)
        (cEnvs.splitSigned spkBs))
    (henv_spk_split_err :
      ∀ evsRegP evsRegRd evsFreeR regBs evsSpkP evsSpkRd evsFreeS spkBs evsSp evsFree2,
      PathEnv d.dir (utf8 "registration-id") evsRegP →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") = .ok regBs →
      cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") evsRegRd →
      FreeOnlyEvs evsFreeR → regBs.length = 4 →
      PathEnv d.dir (utf8 "signed-pre-key") evsSpkP →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") = .ok spkBs →
      cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") evsSpkRd →
      FreeOnlyEvs evsFreeS →
      splitSigned spkBs = none →
      cEnvs.splitSigned spkBs evsSp →
      FreeOnlyEvs evsFree2 →
      EnvAt StoresGhost.opened .postDispatch
        (M.stepEvents
          (evsRegP ++ evsRegRd ++ evsFreeR ++ evsSpkP ++ evsSpkRd ++
            evsFreeS ++ evsSp ++ evsFree2) st))
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectKPlacedEnv r1b_CodeOk H A lim EnvAt g s0 resStack Q Qp oom)
    (hk : ∀ (sf : State)
        (evsRegP evsRegRd evsFreeR evsSpkP evsSpkRd evsFreeS evsSp : List AllocEvent)
        (r0 r1 r2 r3 : BitVec 8)
        (regCap regPtr spkCap spkPtr : BitVec 64)
        (spkBs spkKey spkSig : List (BitVec 8)) (spkId : BitVec 32),
      PathEnv d.dir (utf8 "registration-id") evsRegP →
      cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") evsRegRd →
      FreeOnlyEvs evsFreeR →
      PathEnv d.dir (utf8 "signed-pre-key") evsSpkP →
      cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") evsSpkRd →
      FreeOnlyEvs evsFreeS →
      cEnvs.splitSigned spkBs evsSp →
      r1b_OkCtxPlaced r1b_CodeOk S g d s0 sf 0x1260 →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") =
        .ok [r0, r1, r2, r3] →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") = .ok spkBs →
      splitSigned spkBs = some (spkId, spkKey, spkSig) →
      sf.readReg64 (.gpr 10#5) = spkPtr + 4#64 →
      sf.readReg64 (.gpr 27#5) = BitVec.ofNat 64 spkKey.length →
      sf.readReg64 .x2 = spkId.zeroExtend 64 →
      sf.readReg64 (.gpr 26#5) = d.dirPtr →
      sf.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length →
      let fsp := runFsp s0
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (((fsp + 0x4f0#64) ↦₆₄ (spkPtr + 4#64 + BitVec.ofNat 64 spkKey.length)) ∗
          ((fsp + 0x4f8#64) ↦₆₄ 64#64) ∗
          memRegion (fsp + 0x4d0#64) 32 ∗
          ownedBytes A.repAlloc spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
          ownedBytes A.repAlloc regCap regPtr 4#64 [r0, r1, r2, r3] ∗
          r1b_invCore_placed A.repAlloc g d s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
          ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
          memRegion fsp 0x110 ∗
          memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
          memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
          memRegion (fsp + 0x150#64) 16 ∗
          ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
          ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
          memRegion (fsp + 0x178#64) 8 ∗
          memRegion (fsp + 0x188#64) 8 ∗ ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
          ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
          ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
          ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
          memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
          stackAt fsp (resStack - runFrame) ∗
          A.pool lim
            (M.stepEvents
              (evsRegP ++ evsRegRd ++ evsFreeR ++ evsSpkP ++ evsSpkRd ++ evsFreeS ++ evsSp) st)
            sf)
        Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (init1MemPlaced A lim st g d s0 s resStack) Q Qp oom := by
  let _ := hx28
  refine sepWPp_weaken_pre (r1b_init1Mem_unpack_placed (A.atState lim st s) g d s0 resStack) ?_
  change SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
    (r1b_invCore_placed A.repAlloc g d s0 ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
      memRegion (runFsp s0) 0x110 ∗
      memRegion (runFsp s0 + 0x110#64) 8 ∗ memRegion (runFsp s0 + 0x11c#64) 4 ∗
      memRegion (runFsp s0 + 0x120#64) 8 ∗ memRegion (runFsp s0 + 0x128#64) 8 ∗
      memRegion (runFsp s0 + 0x130#64) 8 ∗ memRegion (runFsp s0 + 0x138#64) 8 ∗
      memRegion (runFsp s0 + 0x140#64) 8 ∗ memRegion (runFsp s0 + 0x148#64) 8 ∗
      memRegion (runFsp s0 + 0x150#64) 8 ∗ memRegion (runFsp s0 + 0x158#64) 8 ∗
      memRegion (runFsp s0 + 0x164#64) 4 ∗
      memRegion (runFsp s0 + 0x168#64) 8 ∗ memRegion (runFsp s0 + 0x170#64) 8 ∗
      memRegion (runFsp s0 + 0x178#64) 8 ∗
      memRegion (runFsp s0 + 0x188#64) 8 ∗ ((runFsp s0 + 0x190#64) ↦₆₄ d.ikW3) ∗
      memRegion (runFsp s0 + 0x198#64) 16 ∗ ((runFsp s0 + 0x1a8#64) ↦₆₄ d.ikW1) ∗
      ((runFsp s0 + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
      memRegion (runFsp s0 + 0x1b4#64) 4 ∗
      memRegion (runFsp s0 + 0x4d0#64) 48 ∗ memRegion (runFsp s0 + 0x1750#64) 24 ∗
      stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s) Q Qp oom
  set fsp := runFsp s0
  have h120_m : memRegion (fsp + 0x120#64) 8 ∗ memRegion (fsp + 0x128#64) 8 =
      memRegion (fsp + 0x120#64) 16 := r1b_join_region fsp 0x120 8 8
  have h130_m : memRegion (fsp + 0x130#64) 8 ∗ memRegion (fsp + 0x138#64) 8 ∗
      memRegion (fsp + 0x140#64) 8 ∗ memRegion (fsp + 0x148#64) 8 =
      memRegion (fsp + 0x130#64) 0x20 := by
    rw [r1b_join_region fsp 0x140 8 8, r1b_join_region fsp 0x138 8 16,
      r1b_join_region fsp 0x130 8 24]
  have h150_m : memRegion (fsp + 0x150#64) 8 ∗ memRegion (fsp + 0x158#64) 8 =
      memRegion (fsp + 0x150#64) 16 := r1b_join_region fsp 0x150 8 8
  have hnorm_in :
      (memRegion (fsp + 0x120#64) 8 ∗ memRegion (fsp + 0x128#64) 8) ∗
        (memRegion (fsp + 0x130#64) 8 ∗ memRegion (fsp + 0x138#64) 8 ∗
          memRegion (fsp + 0x140#64) 8 ∗ memRegion (fsp + 0x148#64) 8) ∗
        (memRegion (fsp + 0x150#64) 8 ∗ memRegion (fsp + 0x158#64) 8) ⊢
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
          memRegion (fsp + 0x150#64) 16 := by
    rw [h120_m, h130_m, h150_m]; exact Entails.refl _
  refine r1b_sepWPp_frame (by r1b_ac) hnorm_in (by r1b_ac) ?_
  have hst := hok.st
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hst.spAligned
  have ⟨hdir32, hpaths⟩ := r1b_init_path_facts_placed he hok.callEq
  have ⟨hreg_ok, hreg_len32⟩ := hpaths "registration-id" (by simp [bundleNames])
  have hdir_nat : (BitVec.ofNat 64 d.dir.length).toNat = d.dir.length := by
    simp only [BitVec.toNat_ofNat]; omega
  generalize hinvRest :
    (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
      storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      coinsInstalledPlaced g.coins (coinsOf g.i) ∗
      tokenInitPlacedAt ∗
      addrNameHeap A.repAlloc d.meG ∗ runSaved s0 ∗
      memRegion (fsp + 0x118#64) 4 ∗ memRegion (fsp + 0x160#64) 4 ∗
      ((fsp + 0x180#64) ↦₆₄ d.ikW0) ∗
      ((fsp + 0x1b8#64) ↦₆₄ d.meG.name.ptr) ∗
      ((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗
      memRegion (fsp + 0x1d0#64) 0x90 ∗
      addrUpperAt (fsp + 0x260#64) d.meG ∗
      memRegion (fsp + 0x270#64) 0x30 ∗
      protocolAddressAt A.repAlloc d.peerG (fsp + 0x2a0#64) ∗
      memRegion (fsp + 0x2c0#64) 0x210 ∗
      memRegion (fsp + 0x500#64) 0x1250 ∗
      memRegion (fsp + 0x1768#64) 0x1288) = invRest
  have hinv_open :
      r1b_invCore_placed A.repAlloc g d s0 = ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr) ∗ invRest := by
    rw [← hinvRest]; dsimp only [r1b_invCore_placed, fsp]; sep_ac_rfl
  have h4d0_sp : memRegion (fsp + 0x4d0#64) 48 =
      memRegion (fsp + 0x4d0#64) 24 ∗ memRegion (fsp + 0x4e8#64) 24 :=
    r1b_split_region fsp 0x4d0 24 24
  rw [hinv_open, h4d0_sp]
  simp only [sepConj_assoc]
  have hpc_in := hst.pc; change s.pc = (blkPl_579).base + 0x074c#64 at hpc_in
  have hpc := hpc_in; have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
  apply r1b_seq_lscro_oom (mid := lsmpl.base 596) hst.inv
  dsimp only [runProgPlaced, lsProg_579]
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
    (by simp only [wp_norm, arm64_norm, *])
  refine r1b_bind_state_placed fun sm1 hsm1 hinv1 => by
    have hvm1 : VmPreserved s sm1 := by simp only [hsm1, wp_norm, arm64_norm]
    rw [← A.pool_transport lim st s sm1 hvm1]
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    generalize hinvCore : r1b_invCore_placed A.repAlloc g d s0 = invCore
    have hinv_close : ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr) ∗ invRest ⊢ invCore := by
      rw [← hinv_open, hinvCore]; exact Entails.refl _
    refine r1b_sepWPp_frame (by r1b_ac) hinv_close (by r1b_ac) ?_
    have h15 : (utf8 "registration-id").length = 15 := by
      simp only [utf8, List.length_map, String.toUTF8_eq_toByteArray]; decide +kernel
    have hreg_name_len : (utf8 "registration-id").length < 2 ^ 32 := by omega
    refine r1b_call_frame <|
      r1b_call_path_ro_placed hh hbnd hinv1 r1b_ro_reg_id_placed
        (by simp only [hsm1, wp_norm, arm64_norm])
        (by simp only [hsm1, wp_norm, arm64_norm, hst.run])
        (by simpa only [hsm1, wp_norm, arm64_norm] using hst.sp)
        (by simpa only [hsm1, wp_norm, arm64_norm] using hst.fp)
        (by simpa only [calleeSavedVRegs, hsm1, wp_norm, arm64_norm] using hst.vregs)
        hst.spAligned (retOff := 0x076c)
        (by simp only [hsm1, wp_norm, arm64_norm])
        (ret := fsp + 0x4d0#64) (dirCap := d.dirCap) (dirPtr := d.dirPtr) (dir := d.dir)
        (by simp only [hsm1, wp_norm, arm64_norm]; try exact congrArg (· + 0x4d0#64) hst.sp)
        (by simp only [hsm1, wp_norm, arm64_norm])
        (by simp only [hsm1, wp_norm, arm64_norm]; exact hdir_nat)
        (by simp only [hsm1, wp_norm, arm64_norm])
        (by rw [h15]; simp only [hsm1, wp_norm, arm64_norm])
        hdir32 hreg_name_len hfit_reg_path hpanic
        fun sf1 evsRegP pCap pPtr hevsRegP hin1 hcs1 hfs1 htr1 => ?_
    have hok1 : r1b_OkCtxPlaced r1b_CodeOk S g d s0 sf1 0x076c := hok.after_call
      (by simp only [hsm1, wp_norm, arm64_norm]) (by simp only [hsm1, wp_norm, arm64_norm])
      (by simp only [hsm1, wp_norm, arm64_norm]) (by simp only [hsm1, wp_norm, arm64_norm])
      (by simp only [hsm1, wp_norm, arm64_norm]) (by simp only [hsm1, wp_norm, arm64_norm])
      hin1 hcs1 hfs1 htr1
    have hx26_1 : sf1.readReg64 (.gpr 26#5) = d.dirPtr :=
      hcs1.2.2.2.2.2.2.2.1.trans (by simp only [hsm1, wp_norm, arm64_norm])
    have hx28_1 : sf1.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length :=
      hcs1.2.2.2.2.2.2.2.2.2.1.trans (by simp only [hsm1, wp_norm, arm64_norm]; try exact hx28)
    let _ := hx26_1; let _ := hx28_1
    have hreg_path_nat :
        (BitVec.ofNat 64 (d.dir ++ [0x2f#8] ++ utf8 "registration-id").length).toNat =
          (d.dir ++ [0x2f#8] ++ utf8 "registration-id").length := by
      simp only [BitVec.toNat_ofNat]; omega
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    try simp only [sepConj_assoc]
    have hpc1 := hin1.pc; change sf1.pc = (blkPl_579).base + 0x076c#64 at hpc1
    have hpc := hpc1; have hrun := hin1.run; have hsp : sf1.sp = fsp := hin1.sp
    apply r1b_seq_lscro_oom (mid := lsρ lsReadFileSym) hin1.inv
    dsimp only [runProgPlaced, lsProg_579]
    apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
      blkLib_eq_579 blk579_noSvc0 (mid := lsρ lsReadFileSym)
    intro _m_strip; wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [wp_norm, arm64_norm, *]) fun _m_real hnsp2 => ?_
    have hvmp2 : VmPreserved sf1 _ := hnsp2.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
    try simp only [State.setMem_setMem] at hvmp2 ⊢
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
    refine r1b_bind_state_placed fun sm2 hsm2 hinv2 => by
      have hvm2 : VmPreserved sf1 sm2 := hsm2 ▸ hvmp2
      rw [← A.pool_transport lim (M.stepEvents evsRegP st) sf1 sm2 hvm2]
      change SepWPp (runProgPlaced H) _ _ _ _ _ _
      have h4e0 :
          ((fsp + 0x4e0#64) ↦₆₄
            BitVec.ofNat 64 (d.dir ++ [0x2f#8] ++ utf8 "registration-id").length) ∗
            memRegion (fsp + 0x4e8#64) 24 ⊢ memRegion (fsp + 0x4e0#64) 32 := by
        simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
          r1b_cell64_cons (a := fsp + 0x4e0#64)
            (BitVec.ofNat 64 (d.dir ++ [0x2f#8] ++ utf8 "registration-id").length)
            (n := 24) (by decide)
      have h4d8 :
          ((fsp + 0x4d8#64) ↦₆₄ pPtr) ∗
            ((fsp + 0x4e0#64) ↦₆₄
              BitVec.ofNat 64 (d.dir ++ [0x2f#8] ++ utf8 "registration-id").length) ∗
            memRegion (fsp + 0x4e8#64) 24 ⊢ memRegion (fsp + 0x4d8#64) 40 := by
        refine Entails.trans (sepConj_mono_right h4e0) ?_
        simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
          r1b_cell64_cons (a := fsp + 0x4d8#64) pPtr (n := 32) (by decide)
      have hfiles_sm2 : sm2.fs.files = runFiles g.i := by
        rw [show sm2.fs.files = sf1.fs.files by simp only [hsm2, wp_norm, arm64_norm]]
        exact hok1.fs
      refine r1b_sepWPp_frame (by r1b_ac) h4d8 (by r1b_ac) ?_
      refine r1b_call_frame <|
        r1b_call_readFile_placed hh hc hbnd hinv2
          (by simp only [hsm2, wp_norm, arm64_norm])
          (by simp only [hsm2, wp_norm, arm64_norm, hin1.run])
          (by simpa only [hsm2, wp_norm, arm64_norm] using hin1.sp)
          (by simpa only [hsm2, wp_norm, arm64_norm] using hin1.fp)
          (by simpa only [calleeSavedVRegs, hsm2, wp_norm, arm64_norm] using hin1.vregs)
          hst.spAligned (retOff := 0x0784)
          (by simp only [hsm2, wp_norm, arm64_norm])
          (pathCap := pCap) (pathPtr := pPtr)
          (path := d.dir ++ [0x2f#8] ++ utf8 "registration-id") (ret := fsp + 0x1750#64)
          (by simp only [hsm2, wp_norm, arm64_norm])
          (by simpa only [hsm2, wp_norm, arm64_norm] using hreg_path_nat)
          (by simp only [hsm2, wp_norm, arm64_norm]; try exact congrArg (· + 0x1750#64) hin1.sp)
          hreg_len32 hreg_ok
          (by rw [hfiles_sm2]; exact hfit_reg_rd evsRegP hevsRegP)
          hpanic
          (fun sf2 evsRegRd w1 w2 hevsRegRd hin2 hcs2 hout2 => ?_)
          (fun sf2 evsRegRd regCap regPtr regBs hevsRegRd hin2 hcs2 hreg_rd_sf hfs2 htr2 => ?_)
      · have hevsRegRd' :
            cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") evsRegRd :=
          hfiles_sm2 ▸ hevsRegRd
        have hrd_err :
            cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") = .error () :=
          hfiles_sm2 ▸ hout2.1
        have hc2 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sf2 0x0784 :=
          hok1.after_readErr
            (by simp only [hsm2, wp_norm, arm64_norm]) (by simp only [hsm2, wp_norm, arm64_norm])
            (by simp only [hsm2, wp_norm, arm64_norm]) (by simp only [hsm2, wp_norm, arm64_norm])
            (by simp only [hsm2, wp_norm, arm64_norm]) (by simp only [hsm2, wp_norm, arm64_norm])
            hin2 hcs2 hout2 r1b_none_reg_rd
        have hx27_2 : sf2.readReg64 (.gpr 27#5) = pPtr :=
          hcs2.2.2.2.2.2.2.2.2.1.trans (by simp only [hsm2, wp_norm, arm64_norm])
        let _ := hx27_2
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        try simp only [sepConj_assoc]
        have hpc2 := hin2.pc; change sf2.pc = (blkPl_579).base + 0x0784#64 at hpc2
        have hpc := hpc2; have hrun := hin2.run; have hsp : sf2.sp = fsp := hin2.sp
        apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x0c14#64) hin2.inv
        dsimp only [runProgPlaced, lsProg_579]
        apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
          blkLib_eq_579 blk579_noSvc0 (mid := (blkPl_579).base + 0x0c14#64)
        intro _m_strip; wp_steps
        refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
          (by simp only [wp_norm, arm64_norm, *]) fun _m_real hnsp3 => ?_
        have hvmp3 : VmPreserved sf2 _ :=
          hnsp3.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
        try simp only [State.setMem_setMem] at hvmp3 ⊢
        apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
        refine r1b_bind_state_placed fun sm3 hsm3 hinv3 => by
          have hvm3 : VmPreserved sf2 sm3 := hsm3 ▸ hvmp3
          rw [← A.pool_transport lim (M.stepEvents evsRegRd (M.stepEvents evsRegP st)) sf2 sm3 hvm3]
          change SepWPp (runProgPlaced H) _ _ _ _ _ _
          have hc3 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm3 0x0c14 := hc2.of_step
            { pc := by simp only [hsm3, wp_norm, arm64_norm]
              run := by simp only [hsm3, wp_norm, arm64_norm, hin2.run]
              sp := by simpa only [hsm3, wp_norm, arm64_norm] using hin2.sp
              fp := by simpa only [hsm3, wp_norm, arm64_norm] using hin2.fp
              inv := hinv3
              vregs := by simpa only [calleeSavedVRegs, hsm3, wp_norm, arm64_norm] using hin2.vregs
              spAligned := hst.spAligned }
            (by simp only [hsm3, wp_norm, arm64_norm]) (by simp only [hsm3, wp_norm, arm64_norm])
            (by simp only [hsm3, wp_norm, arm64_norm]) (by simp only [hsm3, wp_norm, arm64_norm])
            (by simp only [hsm3, wp_norm, arm64_norm])
          have h1750 :
              ((fsp + 0x1750#64) ↦₆₄ 0xffffffffffffffff#64) ∗
                ((fsp + 0x1758#64) ↦₆₄ w1) ∗ ((fsp + 0x1760#64) ↦₆₄ w2) ⊢
                memRegion (fsp + 0x1750#64) 24 := by
            simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
              r1b_cells3_to_region24 (fsp + 0x1750#64) 0xffffffffffffffff#64 w1 w2
          refine r1b_sepWPp_frame (by r1b_ac) h1750 (by r1b_ac) ?_
          have hcore :
              (invCore ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
                ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
                memRegion fsp 0x110 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
                memRegion (fsp + 0x164#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
                stackAt fsp (resStack - runFrame) ∗
                A.pool lim (M.stepEvents evsRegRd (M.stepEvents evsRegP st)) sm3) ⊢
              r1b_errCommon
                (A.atState lim (M.stepEvents evsRegRd (M.stepEvents evsRegP st)) sm3)
                g d s0 resStack := by
            rw [← hinvCore]
            exact r1b_invCore_to_errCommon_placed
              (A.atState lim (M.stepEvents evsRegRd (M.stepEvents evsRegP st)) sm3)
              g d s0 resStack
          generalize herrCommon :
            r1b_errCommon (A.atState lim (M.stepEvents evsRegRd (M.stepEvents evsRegP st)) sm3)
              g d s0 resStack = errCommon at hcore
          have h168 :
              memRegion (fsp + 0x168#64) 8 ∗ memRegion (fsp + 0x170#64) 8 ∗
                memRegion (fsp + 0x178#64) 8 ⊢ memRegion (fsp + 0x168#64) 24 := by
            rw [r1b_join_region fsp 0x170 8 8, r1b_join_region fsp 0x168 8 16]
            exact Entails.refl _
          have h188 :
              memRegion (fsp + 0x188#64) 8 ∗ ((fsp + 0x190#64) ↦₆₄ d.ikW3) ⊢
                memRegion (fsp + 0x188#64) 16 := by
            refine Entails.trans (sepConj_mono_right (pointsTo64_entails_memRegion _ _)) ?_
            rw [r1b_join_region fsp 0x188 8 8]; exact Entails.refl _
          have h1a8 :
              ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
                ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
                memRegion (fsp + 0x1b4#64) 4 ⊢ memRegion (fsp + 0x1a8#64) 16 := by
            refine Entails.trans (sepConj_mono_right (sepConj_mono_left
              (pointsTo32_entails_memRegion _ _))) ?_
            rw [r1b_join_region fsp 0x1b0 4 4]
            simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
              r1b_cell64_cons (a := fsp + 0x1a8#64) d.ikW1 (n := 8) (by decide)
          refine sepWPp_weaken_pre ?_
            (r1b_err_0c14_placed
              (st := M.stepEvents evsRegRd (M.stepEvents evsRegP st))
              (pCap := pCap) (pPtr := pPtr)
              (pBs := d.dir ++ [0x2f#8] ++ utf8 "registration-id")
              hh hdrop hbnd hc3
              (by simp only [hsm3, wp_norm, arm64_norm])
              (by simp only [hsm3, wp_norm, arm64_norm]; try exact hx27_2)
              (by
                simpa only [M.stepEvents_append] using
                  hfit_reg_rd_err evsRegP evsRegRd hevsRegP hrd_err hevsRegRd')
              (fun evsFree hfo => by
                simpa only [M.stepEvents_append, List.append_assoc] using
                  henv_reg_rd_err evsRegP evsRegRd evsFree hevsRegP hrd_err hevsRegRd' hfo)
              hpanic hrej)
          try dsimp only
          rw [herrCommon]
          exact r1b_entails_frame (by r1b_ac)
            (sepConj_mono hcore (sepConj_mono h168 (sepConj_mono h188 h1a8)))
            (by r1b_ac)
      · have hevsRegRd' :
            cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") evsRegRd :=
          hfiles_sm2 ▸ hevsRegRd
        have hok2 : r1b_OkCtxPlaced r1b_CodeOk S g d s0 sf2 0x0784 := hok1.after_call
          (by simp only [hsm2, wp_norm, arm64_norm]) (by simp only [hsm2, wp_norm, arm64_norm])
          (by simp only [hsm2, wp_norm, arm64_norm]) (by simp only [hsm2, wp_norm, arm64_norm])
          (by simp only [hsm2, wp_norm, arm64_norm]) (by simp only [hsm2, wp_norm, arm64_norm])
          hin2 hcs2 hfs2 htr2
        have hreg_rd : cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") =
            .ok regBs := hfiles_sm2 ▸ hreg_rd_sf
        refine sepWPp_weaken_pre ?_
          (r1b_reg_dealloc_0784_placed
            (st := M.stepEvents evsRegRd (M.stepEvents evsRegP st))
            (pCap := pCap) (pPtr := pPtr) (pBs := d.dir ++ [0x2f#8] ++ utf8 "registration-id")
            (regCap := regCap) (regPtr := regPtr) (regBs := regBs)
            hh hc hdrop hbnd he hok2 hreg_rd
            (hcs2.2.2.2.2.2.2.2.1.trans (by simp only [hsm2, wp_norm, arm64_norm]; try exact hx26_1))
            (hcs2.2.2.2.2.2.2.2.2.1.trans (by simp only [hsm2, wp_norm, arm64_norm]))
            (hcs2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [hsm2, wp_norm, arm64_norm]; try exact hx28_1))
            (fun evsFreeR hfoR hne => by
              simpa only [M.stepEvents_append, List.append_assoc] using
                hfit_bad_reg evsRegP evsRegRd evsFreeR regBs hevsRegP hreg_rd hevsRegRd' hfoR hne)
            (fun evsFreeR evsFree hfoR hne hfo => by
              simpa only [M.stepEvents_append, List.append_assoc] using
                henv_bad_reg evsRegP evsRegRd evsFreeR regBs evsFree
                  hevsRegP hreg_rd hevsRegRd' hfoR hne hfo)
            (fun evsFreeR hfoR heq => by
              simpa only [M.stepEvents_append, List.append_assoc] using
                hfit_spk_path evsRegP evsRegRd evsFreeR regBs hevsRegP hreg_rd hevsRegRd' hfoR heq)
            (fun evsFreeR evsSpkP hfoR heq hpS => by
              simpa only [M.stepEvents_append, List.append_assoc] using
                hfit_spk_rd evsRegP evsRegRd evsFreeR regBs evsSpkP
                  hevsRegP hreg_rd hevsRegRd' hfoR heq hpS)
            (fun evsFreeR evsSpkP evsSpkRd hfoR heq hpS herrS hrdS => by
              simpa only [M.stepEvents_append, List.append_assoc] using
                hfit_spk_rd_err evsRegP evsRegRd evsFreeR regBs evsSpkP evsSpkRd
                  hevsRegP hreg_rd hevsRegRd' hfoR heq hpS herrS hrdS)
            (fun evsFreeR evsSpkP evsSpkRd evsFree hfoR heq hpS herrS hrdS hfo => by
              simpa only [M.stepEvents_append, List.append_assoc] using
                henv_spk_rd_err evsRegP evsRegRd evsFreeR regBs evsSpkP evsSpkRd evsFree
                  hevsRegP hreg_rd hevsRegRd' hfoR heq hpS herrS hrdS hfo)
            (fun evsFreeR evsSpkP evsSpkRd evsFreeS spkBs hfoR heq hpS hokS hrdS hfoS => by
              simpa only [M.stepEvents_append, List.append_assoc] using
                hfit_spk_split evsRegP evsRegRd evsFreeR regBs evsSpkP evsSpkRd evsFreeS spkBs
                  hevsRegP hreg_rd hevsRegRd' hfoR heq hpS hokS hrdS hfoS)
            (fun evsFreeR evsSpkP evsSpkRd evsFreeS spkBs evsSp evsFree2
                hfoR heq hpS hokS hrdS hfoS hnoneS hspS hfo2 => by
              simpa only [M.stepEvents_append, List.append_assoc] using
                henv_spk_split_err evsRegP evsRegRd evsFreeR regBs evsSpkP evsSpkRd
                  evsFreeS spkBs evsSp evsFree2
                  hevsRegP hreg_rd hevsRegRd' hfoR heq hpS hokS hrdS hfoS hnoneS hspS hfo2)
            hpanic hrej
            fun sf4 evsFreeR evsSpkP evsSpkRd evsFreeS evsSp
                r0 r1 r2 r3 spkCap spkPtr spkBs spkKey spkSig spkId
                hfoR hpS hrdS hfoS hspS hok4 hr hs hsp_s hx10_4 hx27_4 hx2_4 hx26_4 hx28_4 => by
              simpa only [M.stepEvents_append, List.append_assoc] using
                hk sf4 evsRegP evsRegRd evsFreeR evsSpkP evsSpkRd evsFreeS evsSp
                  r0 r1 r2 r3 regCap regPtr spkCap spkPtr spkBs spkKey spkSig spkId
                  hevsRegP hevsRegRd' hfoR hpS hrdS hfoS hspS
                  hok4 hr hs hsp_s hx10_4 hx27_4 hx2_4 hx26_4 hx28_4)
        try dsimp only
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        rw [hinvCore]
        exact Entails.of_eq (by r1b_ac)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpkSpinePlacedBudget
