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
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpersParsePlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpersPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CommonPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadKpkPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.WorkFramePlacedFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3Helpers
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.Layout

/-!
# `FdsGe3Closed`-Threaded Stage 2 (`kyber-pre-key`) of Arm `R1b` (`0x1260 → 0x12dc`)

Proves `r1b_step_kpk_placed_fd` (`0x1260 → 0x12dc`) on Block `579`, preserving `FdsGe3Closed` across
`bundleRead("kyber-pre-key")` and `splitSigned`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadKpkPlacedBudgetFd

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (LibsignalHooks LibsignalPlacement lsLogFilterAddr lsmpl)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr
  (okTagVec speAt speWord strRefAt vecResultAt)
open CryptoVerification.RustHeap (vecU8)
open CryptoVerification.SignalSession.Cli
  (StoresGhost getResultAt ofLe32 splitOkTag splitSigned utf8)
open CryptoVerification.SignalSession.Cli.MainHops
  (RunCall cliIo cliWrOk ownedBytes sepWPp_weaken_pre)
open CryptoVerification.SignalSession.Cli.MainHops.M3Helpers (vecU8_to_ownedBytes)
open CryptoVerification.SignalSession.Cli.Run.Placed
  (blkLib_eq_579 blkPC_579 blkPl_579 lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (AtRunEntryPlaced InRunPlaced Init1Data PanicK RejectKind RunSem bundleNames
   r1b_CodeOk r1b_ErrCtxPlaced r1b_OkCtxPlaced r1b_StackBounds r1b_bind_state_placed r1b_cell64_cons
   r1b_cells2_to_region16 r1b_entails_frame_core r1b_errCommon r1b_fsp_align
   r1b_init_path_facts_placed r1b_invCore_placed r1b_join_region r1b_none_kpk_rd
   r1b_none_kpk_split r1b_ownedBytes_borrow r1b_ownedBytes_rejoin r1b_ownedRest r1b_ro_kpk_placed
   r1b_sepWPp_borrow_core r1b_sepWPp_drop_left r1b_sepWPp_frame_core r1b_sepWPp_with_ro_placed
   r1b_spAligned_of_fsp r1b_split_region r1b_stage_to_err_placed r1b_u64_split32 runFiles runFsp
   runPcPlaced runPcPlaced_eq runProgPlaced)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets RunSlots runFrame)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpersParsePlacedBudgetFd
  (r1b_call_splitSigned_placed_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpersPlacedBudgetFd
  (r1b_call_bundleRead_ro_placed_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CommonPlacedBudget
  (r1b_files_eq_of_trace_eq_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CommonPlacedBudgetFd
  (r1b_call_withFds_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadKpkPlacedBudget
  (r1b_err_1aa8_placed r1b_err_1b60_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadKpkPlacedBudgetAux
  (r1b_seq_lscro_oom)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpkPlacedBudgetAux
  (blk579_noSvc0)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.WorkFramePlacedFd
  (r1b_OkCtxPlacedFd)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget (RejectKPlacedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget
  (DropSpeOwnedOkAtBlock)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
  (RunCalleesEnvs RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd (RunCalleesPlacedFd)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (bundleReadSpecPlaced)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local simp, local arm64_norm, local wp_norm] runPcPlaced_eq BitVec.ofNat_eq_ofNat

local macro (priority := high) "r1b_ac" : tactic =>
  `(tactic| ((try dsimp +zetaDelta only) <;> first | rfl | simp only [emp_sepConj] | sep_ac_rfl))

private meta def r1bStripLetsKP : Nat → Lean.Expr → Lean.Expr
  | 0, e => e
  | n + 1, .letE _ _ v b _ => r1bStripLetsKP n (b.instantiate1 v)
  | n + 1, .mdata _ e => r1bStripLetsKP n e
  | _, e => e

private meta def r1bSplitSepKP : Nat → Lean.Expr → Lean.Expr → Array Lean.Expr
  | 0, _, e => #[e]
  | fuel + 1, sepSample, e =>
    let e := r1bStripLetsKP 64 e
    let fn := sepSample.getAppFn.constName!
    let ar := sepSample.getAppNumArgs
    if e.isAppOfArity fn ar then
      r1bSplitSepKP fuel sepSample (e.getArg! (ar - 2)) ++
        r1bSplitSepKP fuel sepSample (e.getArg! (ar - 1))
    else #[e]

private meta def r1bIsDefEqPureKP (x a : Lean.Expr) : Lean.Elab.TermElabM Bool := do
  let x := r1bStripLetsKP 64 x; let a := r1bStripLetsKP 64 a
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

private meta def r1bComputeRestKP (ctxName : String) (p a1 : Lean.Expr) :
    Lean.Elab.TermElabM Lean.Expr := do
  let sepTy := Lean.mkConst ``SepProp []
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let ps := (r1bSplitSepKP 64 sepSample (← Lean.instantiateMVars p)).toList
  let a1s := (r1bSplitSepKP 64 sepSample (← Lean.instantiateMVars a1)).toList
  let mut rem := ps
  for a in a1s do
    let mut removed := false
    let mut next : List Lean.Expr := []
    for x in rem do
      if !removed && (← r1bIsDefEqPureKP x a) then removed := true
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

local elab (priority := high) "r1b_entails_frame_kp " t1:term:arg h:term:arg t2:term:arg :
    term <= expectedType => do
  let exp ← Lean.instantiateMVars expectedType
  if exp.isMVar then Lean.Elab.Term.tryPostpone
  let entSample ← Lean.Elab.Term.elabTerm (← `(emp ⊢ emp)) none
  let ear := entSample.getAppNumArgs
  let expS := r1bStripLetsKP 64 exp
  let p := expS.getArg! (ear - 2)
  let q := expS.getArg! (ear - 1)
  if (← Lean.instantiateMVars p).isMVar then Lean.Elab.Term.tryPostpone
  if (← Lean.instantiateMVars q).isMVar then Lean.Elab.Term.tryPostpone
  let hExpr ← Lean.Elab.Term.elabTerm h none
  let hTy := r1bStripLetsKP 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
  let a1 := hTy.getArg! (ear - 2)
  let a2 := hTy.getArg! (ear - 1)
  let r ← r1bComputeRestKP "r1b_entails_frame" p a1
  let sepTy := Lean.mkConst ``SepProp []
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let sar := sepSample.getAppNumArgs
  let mkSep (x y : Lean.Expr) : Lean.Expr :=
    sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
  let rIsEmp ← r1bIsDefEqPureKP r empExpr
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

local elab (priority := high) "r1b_sepWPp_frame_kp " t1:term:arg h:term:arg t2:term:arg hk:term:arg :
    term <= expectedType => do
  let exp ← Lean.instantiateMVars expectedType
  if exp.isMVar then Lean.Elab.Term.tryPostpone
  let expS := r1bStripLetsKP 64 exp
  let args := expS.getAppArgs
  let prog := args[0]!; let ret := args[1]!; let st := args[2]!; let p := args[3]!
  let q := args[4]!; let qp := args[5]!; let oom := args[6]!
  let entSample ← Lean.Elab.Term.elabTerm (← `(emp ⊢ emp)) none
  let ear := entSample.getAppNumArgs
  let hExpr ← Lean.Elab.Term.elabTerm h none
  let hTy := r1bStripLetsKP 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
  let a1 := hTy.getArg! (ear - 2)
  let a2 := hTy.getArg! (ear - 1)
  let r ← r1bComputeRestKP "r1b_sepWPp_frame" p a1
  let sepTy := Lean.mkConst ``SepProp []
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let sar := sepSample.getAppNumArgs
  let mkSep (x y : Lean.Expr) : Lean.Expr :=
    sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
  let rIsEmp ← r1bIsDefEqPureKP r empExpr
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
    let a2IsEmp ← r1bIsDefEqPureKP a2 empExpr
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

local elab:10 (priority := high) "r1b_call_frame_kp" "<|" h:term:10 : term <= expectedType => do
  let exp ← Lean.instantiateMVars expectedType
  if exp.isMVar then Lean.Elab.Term.tryPostpone
  let expS := r1bStripLetsKP 64 exp
  let hExpr ← Lean.Elab.Term.elabTerm h none
  let hTy0 := r1bStripLetsKP 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
  for idx in [0, 1, 2, 4, 5, 6] do
    if !(← Lean.Meta.withReducibleAndInstances <| Lean.Meta.isDefEq (hTy0.getArg! idx) (expS.getArg! idx)) then
      discard <| Lean.Meta.isDefEq (hTy0.getArg! idx) (expS.getArg! idx)
  let p ← Lean.instantiateMVars (expS.getArg! 3)
  let p' ← Lean.instantiateMVars ((r1bStripLetsKP 64 (← Lean.instantiateMVars hTy0)).getArg! 3)
  let sepTy := Lean.mkConst ``SepProp []
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let sar := sepSample.getAppNumArgs
  let mkSep (x y : Lean.Expr) : Lean.Expr :=
    sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
  let ps := (r1bSplitSepKP 64 sepSample p).toList
  let p's := (r1bSplitSepKP 64 sepSample p').toList
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
      if !removed && (← r1bIsDefEqPureKP x a) then removed := true
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

/-! ## Stage 2 Step (`0x1260 → 0x12dc`, `kyber-pre-key` `bundleRead` and `splitSigned`) -/

private theorem r1b_utf8_kpk_len_placed : (utf8 "kyber-pre-key").length = 13 := by
  simp only [utf8, List.length_map, String.toUTF8_eq_toByteArray]; decide +kernel

set_option maxHeartbeats 800000 in
theorem r1b_step_kpk_placed_fd [LibsignalPlacement] {M : AllocCostModel}
    {S : RunSem} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {cEnvs : RunCalleesEnvs} {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets} {σ : RunSlots}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {r0 r1 r2 r3 : BitVec 8}
    {regCap regPtr spkCap spkPtr : BitVec 64}
    {spkBs spkKey spkSig : List (BitVec 8)} {spkId : BitVec 32}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hc : RunCalleesPlacedFd A lim cEnvs H B σ)
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (he : AtRunEntryPlaced r1b_CodeOk S g s0)
    (hok : r1b_OkCtxPlacedFd r1b_CodeOk S g d s0 s 0x1260)
    (hreg_rd : cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") =
      .ok [r0, r1, r2, r3])
    (hspk_rd : cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") = .ok spkBs)
    (hspk_sp : splitSigned spkBs = some (spkId, spkKey, spkSig))
    (hx10 : s.readReg64 (.gpr 10#5) = spkPtr + 4#64)
    (hx27 : s.readReg64 (.gpr 27#5) = BitVec.ofNat 64 spkKey.length)
    (hx2 : s.readReg64 .x2 = spkId.zeroExtend 64)
    (hx26 : s.readReg64 (.gpr 26#5) = d.dirPtr)
    (hx28 : s.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length)
    (hfit_kpk_br : FitsEnv M lim st (cEnvs.bundleRead (runFiles g.i) d.dir (utf8 "kyber-pre-key")))
    (henv_kpk_br_err : ∀ evsKpkBr evsFree,
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "kyber-pre-key") = .error () →
      cEnvs.bundleRead (runFiles g.i) d.dir (utf8 "kyber-pre-key") evsKpkBr →
      FreeOnlyEvs evsFree →
      EnvAt StoresGhost.opened .postDispatch (M.stepEvents (evsKpkBr ++ evsFree) st))
    (hfit_kpk_split : ∀ evsKpkBr kpkBs,
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "kyber-pre-key") = .ok kpkBs →
      cEnvs.bundleRead (runFiles g.i) d.dir (utf8 "kyber-pre-key") evsKpkBr →
      FitsEnv M lim (M.stepEvents evsKpkBr st) (cEnvs.splitSigned kpkBs))
    (henv_kpk_split_err : ∀ evsKpkBr kpkBs evsKpkSp evsFree,
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "kyber-pre-key") = .ok kpkBs →
      cEnvs.bundleRead (runFiles g.i) d.dir (utf8 "kyber-pre-key") evsKpkBr →
      splitSigned kpkBs = none →
      cEnvs.splitSigned kpkBs evsKpkSp →
      FreeOnlyEvs evsFree →
      EnvAt StoresGhost.opened .postDispatch
        (M.stepEvents (evsKpkBr ++ evsKpkSp ++ evsFree) st))
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectKPlacedEnv r1b_CodeOk H A lim EnvAt g s0 resStack Q Qp oom)
    (hk : ∀ (sf : State) (evsKpkBr evsKpkSp : List AllocEvent)
        (kpkCap kpkPtr : BitVec 64)
        (kpkBs kpkKey kpkSig : List (BitVec 8)) (kpkId : BitVec 32),
      cEnvs.bundleRead (runFiles g.i) d.dir (utf8 "kyber-pre-key") evsKpkBr →
      cEnvs.splitSigned kpkBs evsKpkSp →
      r1b_OkCtxPlacedFd r1b_CodeOk S g d s0 sf 0x12dc →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "kyber-pre-key") = .ok kpkBs →
      splitSigned kpkBs = some (kpkId, kpkKey, kpkSig) →
      sf.readReg64 (.gpr 25#5) = d.dirPtr →
      sf.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length →
      sf.readReg64 (.gpr 26#5) = kpkPtr →
      sf.readReg64 (.gpr 27#5) = BitVec.ofNat 64 spkKey.length →
      sf.readReg64 (.gpr 9#5) = BitVec.ofNat 64 kpkKey.length →
      sf.readReg64 (.gpr 10#5) = kpkPtr + 4#64 →
      sf.readReg64 (.gpr 8#5) = kpkPtr + 4#64 + BitVec.ofNat 64 kpkKey.length →
      sf.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64 →
      sf.readReg64 (.gpr 24#5) = 64#64 →
      let fsp := runFsp s0
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (memRegion (fsp + 0x4d0#64) 48 ∗
          ownedBytes A.repAlloc kpkCap kpkPtr (BitVec.ofNat 64 kpkBs.length) kpkBs ∗
          ownedBytes A.repAlloc spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
          ownedBytes A.repAlloc regCap regPtr 4#64 [r0, r1, r2, r3] ∗
          r1b_invCore_placed A.repAlloc g d s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
          ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
          memRegion fsp 0x110 ∗
          memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
          memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x130#64) 24 ∗
          ((fsp + 0x148#64) ↦₆₄ 64#64) ∗
          ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗
          ((fsp + 0x158#64) ↦₆₄ (spkPtr + 4#64 + BitVec.ofNat 64 spkKey.length)) ∗
          ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
          ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
          ((fsp + 0x178#64) ↦₆₄ (spkPtr + 4#64)) ∗
          ((fsp + 0x188#64) ↦₆₄ spkId.zeroExtend 64) ∗ ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
          ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
          ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
          ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
          memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
          stackAt fsp (resStack - runFrame) ∗
          A.pool lim (M.stepEvents (evsKpkBr ++ evsKpkSp) st) sf)
        Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
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
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s)
      Q Qp oom := by
  intro fsp
  let _ := hreg_rd; let _ := hspk_rd; let _ := hspk_sp
  let _ := hx10; let _ := hx27; let _ := hx2; let _ := hx26; let _ := hx28
  generalize hinvCore : r1b_invCore_placed A.repAlloc g d s0 = invCore at *
  have hst := hok.st
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hst.spAligned
  have ⟨hdir32, hpaths⟩ := r1b_init_path_facts_placed he hok.callEq
  have ⟨hkpk_ok, _⟩ := hpaths "kyber-pre-key" (by simp [bundleNames])
  have hdir_nat : (BitVec.ofNat 64 d.dir.length).toNat = d.dir.length := by
    simp only [BitVec.toNat_ofNat]; omega
  rw [r1b_split_region fsp 0x150 8 8,
    ProofLib.memRegion_eight (fsp + 0x158#64),
    ProofLib.memRegion_eight (fsp + 0x178#64),
    ProofLib.memRegion_eight (fsp + 0x188#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun v158 => SepWPp.exists_elim fun v178 =>
    SepWPp.exists_elim fun v188 => ?_
  have hpc := hst.pc; change s.pc = (blkPl_579).base + 4704#64 at hpc
  have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
  apply r1b_seq_lscro_oom (mid := lsmpl.base 563) hst.inv
  dsimp only [runProgPlaced, lsProg_579]
  apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
    blkLib_eq_579 blk579_noSvc0 (mid := lsmpl.base 563)
  intro _m_strip; wp_steps
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
    (by simp only [wp_norm, arm64_norm, *]) fun _m_real hnsp => ?_
  have hvmp : VmPreserved s _ :=
    hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
  try simp only [State.setMem_setMem] at hvmp ⊢
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
  refine r1b_bind_state_placed fun sm1 hsm1 hinv1 => by
    have hvm1 : VmPreserved s sm1 := hsm1 ▸ hvmp
    have hfs_sm1 : sm1.fs = s.fs := by
      first
      | simp only [hsm1, wp_norm, arm64_norm]
      | simpa only [← hsm1, wp_norm, arm64_norm] using hnsp.2.2.2.2.2.2
    have hfds_sm1 : FdsGe3Closed sm1.fs := hfs_sm1 ▸ hok.fds
    rw [← A.pool_transport lim st s sm1 hvm1]
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have h4d0_48 :
        memRegion (fsp + 0x4d0#64) 32 ∗
          ((fsp + 0x4f0#64) ↦₆₄ (spkPtr + 4#64 + BitVec.ofNat 64 spkKey.length)) ∗
          ((fsp + 0x4f8#64) ↦₆₄ 64#64) ⊢ memRegion (fsp + 0x4d0#64) 48 := by
      refine Entails.trans (sepConj_mono_right (by
        simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
          r1b_cells2_to_region16 (fsp + 0x4f0#64)
            (spkPtr + 4#64 + BitVec.ofNat 64 spkKey.length) 64#64)) ?_
      rw [r1b_join_region fsp 0x4d0 32 16]; exact Entails.refl _
    have hfiles_sm1 : sm1.fs.files = runFiles g.i :=
      (congrArg (·.files) hfs_sm1).trans hok.fs
    refine r1b_sepWPp_frame_kp (by r1b_ac) h4d0_48 (by r1b_ac) ?_
    refine r1b_call_frame_kp <|
      r1b_call_bundleRead_ro_placed_fd (g := g) (ret := fsp + 0x4d0#64)
        (dirCap := d.dirCap) (dirPtr := d.dirPtr) (dir := d.dir)
        hh hc hbnd hinv1 r1b_ro_kpk_placed
        (by simp only [hsm1, wp_norm, arm64_norm])
        (by simp only [hsm1, wp_norm, arm64_norm, hst.run])
        (by simpa only [hsm1, wp_norm, arm64_norm] using hst.sp)
        (by simpa only [hsm1, wp_norm, arm64_norm] using hst.fp)
        (by simpa only [calleeSavedVRegs, hsm1, wp_norm, arm64_norm] using hst.vregs)
        hst.spAligned (retOff := 0x1294)
        (by simp only [hsm1, wp_norm, arm64_norm])
        (by simp only [hsm1, wp_norm, arm64_norm])
        (by simp only [hsm1, wp_norm, arm64_norm])
        (by simp only [hsm1, wp_norm, arm64_norm]; exact hdir_nat)
        (by simp only [hsm1, wp_norm, arm64_norm]; rfl)
        (by simp only [hsm1, wp_norm, arm64_norm, r1b_utf8_kpk_len_placed])
        hdir32 (by rw [r1b_utf8_kpk_len_placed]; decide) hkpk_ok
        (by rw [hfiles_sm1]; exact hfit_kpk_br) (hfds := hfds_sm1) hpanic
        (fun sf1 evsKpkBr eCap ePtr eBs hevsKpkBr hin1 hcs1 hout1 _hfds1 => ?_)
        (fun sf1 evsKpkBr kpkCap kpkPtr kpkBs hevsKpkBr hin1 hcs1 hkpk_rd_sf hfs1 htr1 hfds1 => ?_)
    · have hevsKpkBr' :
          cEnvs.bundleRead (runFiles g.i) d.dir (utf8 "kyber-pre-key") evsKpkBr :=
        hfiles_sm1 ▸ hevsKpkBr
      have hrd_err :
          cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "kyber-pre-key") = .error () :=
        hfiles_sm1 ▸ hout1.1
      have hc1 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sf1 0x1294 :=
        hok.after_readErr
          (by simp only [hsm1, wp_norm, arm64_norm]) (by simp only [hsm1, wp_norm, arm64_norm])
          (by simp only [hsm1, wp_norm, arm64_norm]) (by simp only [hsm1, wp_norm, arm64_norm])
          (by simp only [hsm1, wp_norm, arm64_norm]) (congrArg (·.files) hfs_sm1)
          hin1 hcs1 hout1 r1b_none_kpk_rd
      try simp only [BitVec.add_assoc]; try simp only [BitVec.reduceAdd]; try simp only [sepConj_assoc]
      try rw [← BitVec.add_assoc spkPtr 4#64]
      dsimp only [speWord]
      have hpc := hin1.pc; change sf1.pc = (blkPl_579).base + 4756#64 at hpc
      have hrun := hin1.run; have hsp : sf1.sp = fsp := hin1.sp
      apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 6824#64) hin1.inv
      dsimp only [runProgPlaced, lsProg_579]
      apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
        blkLib_eq_579 blk579_noSvc0 (mid := (blkPl_579).base + 6824#64)
      intro _m_strip; wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *]) fun _m_real hnsp => ?_
      have hvmp : VmPreserved sf1 _ :=
        hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
      try simp only [State.setMem_setMem] at hvmp ⊢
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
      refine r1b_bind_state_placed fun sm2 hsm2 hinv2 => by
        have hvm2 : VmPreserved sf1 sm2 := hsm2 ▸ hvmp
        rw [← A.pool_transport lim (M.stepEvents evsKpkBr st) sf1 sm2 hvm2]
        change SepWPp (runProgPlaced H) _ _ _ _ _ _
        try rw [← BitVec.add_assoc spkPtr 4#64]
        have hc2 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm2 0x1aa8 := hc1.of_step
          { pc := by simp only [hsm2, wp_norm, arm64_norm]
            run := by simp only [hsm2, wp_norm, arm64_norm, hin1.run]
            sp := by simpa only [hsm2, wp_norm, arm64_norm] using hin1.sp
            fp := by simpa only [hsm2, wp_norm, arm64_norm] using hin1.fp
            inv := hinv2
            vregs := by simpa only [calleeSavedVRegs, hsm2, wp_norm, arm64_norm] using hin1.vregs
            spAligned := hst.spAligned }
          (by simp only [hsm2, wp_norm, arm64_norm]) (by simp only [hsm2, wp_norm, arm64_norm])
          (by simp only [hsm2, wp_norm, arm64_norm]) (by simp only [hsm2, wp_norm, arm64_norm])
          (by simp only [hsm2, wp_norm, arm64_norm])
        try rw [hx10]
        try rw [show s.readReg64 (.gpr 2#5) = spkId.zeroExtend 64 from hx2]
        try rw [hx2]
        have h150 :
            memRegion (fsp + 0x150#64) 8 ∗
              ((fsp + 0x158#64) ↦₆₄ (spkPtr + 4#64 + BitVec.ofNat 64 spkKey.length)) ⊢
              memRegion (fsp + 0x150#64) 16 := by
          refine Entails.trans (sepConj_mono_right (pointsTo64_entails_memRegion _ _)) ?_
          rw [r1b_join_region fsp 0x150 8 8]; exact Entails.refl _
        have h178 : ((fsp + 0x178#64) ↦₆₄ (spkPtr + 4#64)) ⊢ memRegion (fsp + 0x178#64) 8 :=
          pointsTo64_entails_memRegion _ _
        generalize herrCommon :
          r1b_errCommon (A.atState lim (M.stepEvents evsKpkBr st) sm2) g d s0 resStack = errCommon
        have hst_err :
            invCore ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
              ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
              memRegion fsp 0x110 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
              ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
              ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
              ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
              ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
              memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
              stackAt fsp (resStack - runFrame) ∗ A.pool lim (M.stepEvents evsKpkBr st) sm2 ⊢
              errCommon ∗ memRegion (fsp + 0x190#64) 8 ∗ memRegion (fsp + 0x1a8#64) 16 := by
          rw [← hinvCore, ← herrCommon]
          exact r1b_stage_to_err_placed (A.atState lim (M.stepEvents evsKpkBr st) sm2)
            g d s0 resStack (ofLe32 r0 r1 r2 r3)
        have h188 : ((fsp + 0x188#64) ↦₆₄ spkId.zeroExtend 64) ∗ memRegion (fsp + 0x190#64) 8 ⊢
            memRegion (fsp + 0x188#64) 16 := by
          simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
            r1b_cell64_cons (a := fsp + 0x188#64) (spkId.zeroExtend 64) (n := 8) (by decide)
        have hex :
            (((fsp + 0x188#64) ↦₆₄ spkId.zeroExtend 64) ∗
              (invCore ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
                ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
                memRegion fsp 0x110 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
                ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
                ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
                ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
                ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
                memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
                stackAt fsp (resStack - runFrame) ∗ A.pool lim (M.stepEvents evsKpkBr st) sm2)) ⊢
              errCommon ∗
                memRegion (fsp + 0x188#64) 16 ∗ memRegion (fsp + 0x1a8#64) 16 :=
          Entails.trans (sepConj_mono_right hst_err)
            (r1b_entails_frame_kp (by r1b_ac) h188 (by r1b_ac))
        have hcl := r1b_err_1aa8_placed (st := M.stepEvents evsKpkBr st)
          (eCap := eCap) (ePtr := ePtr) (eBs := eBs)
          (spkCap := spkCap) (spkPtr := spkPtr) (spkBs := spkBs)
          (regCap := regCap) (regPtr := regPtr) (regBs := [r0, r1, r2, r3])
          hh hdrop hbnd hc2
          (by simp only [hsm2, wp_norm, arm64_norm, speWord])
          (by simp only [hsm2, wp_norm, arm64_norm])
          (by simp only [hsm2, wp_norm, arm64_norm])
          (by simp only [hsm2, wp_norm, arm64_norm])
          (fun evsFree hfo => by
            rw [← M.stepEvents_append]
            exact henv_kpk_br_err evsKpkBr evsFree hrd_err hevsKpkBr' hfo)
          hpanic hrej
        dsimp only at hcl
        rw [herrCommon] at hcl
        refine sepWPp_weaken_pre ?_ hcl
        exact r1b_entails_frame_kp (by r1b_ac) (sepConj_mono h150 (sepConj_mono h178 hex)) (by r1b_ac)
    · have hevsKpkBr' :
          cEnvs.bundleRead (runFiles g.i) d.dir (utf8 "kyber-pre-key") evsKpkBr :=
        hfiles_sm1 ▸ hevsKpkBr
      have hok1 : r1b_OkCtxPlacedFd r1b_CodeOk S g d s0 sf1 0x1294 := hok.after_call_fds
        (by simp only [hsm1, wp_norm, arm64_norm]) (by simp only [hsm1, wp_norm, arm64_norm])
        (by simp only [hsm1, wp_norm, arm64_norm]) (by simp only [hsm1, wp_norm, arm64_norm])
        (by simp only [hsm1, wp_norm, arm64_norm]) (congrArg (·.files) hfs_sm1)
        hin1 hcs1 hfs1 htr1 hfds1
      have hkpk_rd : cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "kyber-pre-key") =
          .ok kpkBs := hfiles_sm1 ▸ hkpk_rd_sf
      have hx23_1 : sf1.readReg64 (.gpr 23#5) = 64#64 :=
        hcs1.2.2.2.2.1.trans (by simp only [hsm1, wp_norm, arm64_norm])
      have hx25_1 : sf1.readReg64 (.gpr 25#5) = d.dirPtr :=
        hcs1.2.2.2.2.2.2.1.trans (by simp only [hsm1, wp_norm, arm64_norm])
      have hx27_1 : sf1.readReg64 (.gpr 27#5) = BitVec.ofNat 64 spkKey.length :=
        hcs1.2.2.2.2.2.2.2.2.1.trans
          (by solve | simp only [hsm1, wp_norm, arm64_norm] | simpa only [hsm1, wp_norm, arm64_norm] using hx27)
      have hx28_1 : sf1.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length :=
        hcs1.2.2.2.2.2.2.2.2.2.1.trans
          (by solve | simp only [hsm1, wp_norm, arm64_norm] | simpa only [hsm1, wp_norm, arm64_norm] using hx28)
      rw [r1b_split_region fsp 0x130 24 8,
        ProofLib.memRegion_eight (fsp + 0x148#64),
        ProofLib.memRegion_eight (fsp + 0x150#64)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left,
        sepExists_sepConj_right, sepConj_assoc]
      try rw [← BitVec.add_assoc spkPtr 4#64]
      refine SepWPp.exists_elim fun v148 => SepWPp.exists_elim fun v150 =>
        r1b_call_frame_kp <| r1b_sepWPp_borrow_core A.repAlloc (cap := kpkCap) (ptr := kpkPtr)
          (len := BitVec.ofNat 64 kpkBs.length) (bs := kpkBs)
          fun ⟨_, hkpk_le, hkpk_lt, hkpk_ne⟩ => ?_
      have hkpk_nat : (BitVec.ofNat 64 kpkBs.length).toNat = kpkBs.length := by
        simp only [BitVec.toNat_ofNat]; omega
      dsimp only [okTagVec]
      have hpc := hin1.pc; change sf1.pc = (blkPl_579).base + 4756#64 at hpc
      have hrun := hin1.run; have hsp : sf1.sp = fsp := hin1.sp
      apply r1b_seq_lscro_oom (mid := lsmpl.base 592) hin1.inv
      dsimp only [runProgPlaced, lsProg_579]
      apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
        blkLib_eq_579 blk579_noSvc0 (mid := lsmpl.base 592)
      intro _m_strip; wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *]) fun _m_real hnsp => ?_
      have hvmp : VmPreserved sf1 _ :=
        hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
      try simp only [State.setMem_setMem] at hvmp ⊢
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
      refine r1b_bind_state_placed fun sm2 hsm2 hinv2 => by
        have hvm2 : VmPreserved sf1 sm2 := hsm2 ▸ hvmp
        have hfs_sm2 : sm2.fs = sf1.fs := by
          first
          | simp only [hsm2, wp_norm, arm64_norm]
          | simpa only [← hsm2, wp_norm, arm64_norm] using hnsp.2.2.2.2.2.2
        rw [← A.pool_transport lim (M.stepEvents evsKpkBr st) sf1 sm2 hvm2]
        change SepWPp (runProgPlaced H) _ _ _ _ _ _
        have h4d0_48 :
            ((fsp + 0x4d0#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
              ((fsp + 0x4d8#64) ↦₆₄ kpkCap) ∗ ((fsp + 0x4e0#64) ↦₆₄ kpkPtr) ∗
              ((fsp + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 kpkBs.length) ∗
              memRegion (fsp + 0x4f0#64) 16 ⊢ memRegion (fsp + 0x4d0#64) 48 := by
          refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (by
            simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
              r1b_cell64_cons (a := fsp + 0x4e8#64) (BitVec.ofNat 64 kpkBs.length) (n := 16) (by decide))))) ?_
          refine Entails.trans (sepConj_mono_right (sepConj_mono_right (by
            simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
              r1b_cell64_cons (a := fsp + 0x4e0#64) kpkPtr (n := 24) (by decide)))) ?_
          refine Entails.trans (sepConj_mono_right (by
            simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
              r1b_cell64_cons (a := fsp + 0x4d8#64) kpkCap (n := 32) (by decide))) ?_
          simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
            r1b_cell64_cons (a := fsp + 0x4d0#64) 0xfffffffffffffffe#64 (n := 40) (by decide)
        refine r1b_sepWPp_frame_kp (by r1b_ac) h4d0_48 (by r1b_ac) ?_
        refine r1b_call_frame_kp <|
          r1b_call_splitSigned_placed_fd (g := g) (ret := fsp + 0x4d0#64) (fp := kpkPtr) (file := kpkBs)
            hh hc hbnd hinv2
            (by simp only [hsm2, wp_norm, arm64_norm])
            (by simp only [hsm2, wp_norm, arm64_norm, hin1.run])
            (by simpa only [hsm2, wp_norm, arm64_norm] using hin1.sp)
            (by simpa only [hsm2, wp_norm, arm64_norm] using hin1.fp)
            (by simpa only [calleeSavedVRegs, hsm2, wp_norm, arm64_norm] using hin1.vregs)
            hst.spAligned (retOff := 0x12bc)
            (by simp only [hsm2, wp_norm, arm64_norm])
            (by simp only [hsm2, wp_norm, arm64_norm])
            (by simp only [hsm2, wp_norm, arm64_norm])
            (by simp only [hsm2, wp_norm, arm64_norm]; exact hkpk_nat)
            (hfit_kpk_split evsKpkBr kpkBs hkpk_rd hevsKpkBr') hpanic
            (fun sf2 evsKpkSp eCap ePtr eBs hevsKpkSp hin2 hcs2 hsp_none hfs2 htr2 => ?_)
            (fun sf2 evsKpkSp kpkId kpkKey kpkSig hevsKpkSp hin2 hcs2 hsp_ok hfs_eq2 _hfs2 htr2 => ?_)
        · have hok2_plain : r1b_OkCtxPlaced r1b_CodeOk S g d s0 sf2 0x12bc := hok1.ok.after_call
            (by simp only [hsm2, wp_norm, arm64_norm]) (by simp only [hsm2, wp_norm, arm64_norm])
            (by simp only [hsm2, wp_norm, arm64_norm]) (by simp only [hsm2, wp_norm, arm64_norm])
            (by simp only [hsm2, wp_norm, arm64_norm]) (congrArg (·.files) hfs_sm2)
            hin2 hcs2 hfs2 htr2
          have hc2 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sf2 0x12bc :=
            hok2_plain.to_err (r1b_none_kpk_split hkpk_rd hsp_none)
          have hx26_2 : sf2.readReg64 (.gpr 26#5) = kpkPtr :=
            hcs2.2.2.2.2.2.2.2.1.trans (by simp only [hsm2, wp_norm, arm64_norm])
          have hrejoin := r1b_ownedBytes_rejoin A.repAlloc kpkCap kpkPtr kpkBs hkpk_le hkpk_lt hkpk_ne
          refine r1b_sepWPp_frame_kp (by r1b_ac) hrejoin (by r1b_ac) ?_
          have he8 : ((fsp + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 eBs.length) =
              ((fsp + 0x4e8#64) ↦₃₂ (BitVec.ofNat 64 eBs.length).truncate 32) ∗
                ((fsp + 0x4ec#64) ↦₃₂ ((BitVec.ofNat 64 eBs.length) >>> 32).truncate 32) := by
            have hz := r1b_u64_split32 (fsp + 0x4e8#64) (BitVec.ofNat 64 eBs.length)
            have ha : (fsp + 0x4e8#64) + 4#64 = fsp + 0x4ec#64 := by bv_omega
            rwa [ha] at hz
          try simp only [BitVec.add_assoc]; try simp only [BitVec.reduceAdd]; try simp only [sepConj_assoc]
          try rw [← BitVec.add_assoc spkPtr 4#64]
          rw [he8]
          try simp only [sepConj_assoc]
          dsimp only [speWord]
          have hpc := hin2.pc; change sf2.pc = (blkPl_579).base + 4796#64 at hpc
          have hrun := hin2.run; have hsp : sf2.sp = fsp := hin2.sp
          apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 7008#64) hin2.inv
          dsimp only [runProgPlaced, lsProg_579]
          apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
            blkLib_eq_579 blk579_noSvc0 (mid := (blkPl_579).base + 7008#64)
          intro _m_strip; wp_steps
          refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
            (by simp only [wp_norm, arm64_norm, *]) fun _m_real hnsp => ?_
          have hvmp : VmPreserved sf2 _ :=
            hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
          try simp only [State.setMem_setMem] at hvmp ⊢
          apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
          refine r1b_bind_state_placed fun sm3 hsm3 hinv3 => by
            have hvm3 : VmPreserved sf2 sm3 := hsm3 ▸ hvmp
            rw [← A.pool_transport lim (M.stepEvents evsKpkSp (M.stepEvents evsKpkBr st)) sf2 sm3 hvm3]
            change SepWPp (runProgPlaced H) _ _ _ _ _ _
            try rw [← BitVec.add_assoc spkPtr 4#64]
            have hc3 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm3 0x1b60 := hc2.of_step
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
            try rw [hx23_1]
            try rw [hx10]
            try rw [show s.readReg64 (.gpr 2#5) = spkId.zeroExtend 64 from hx2]
            try rw [hx2]
            have he8' : ((fsp + 0x4e8#64) ↦₃₂ (BitVec.ofNat 64 eBs.length).truncate 32) ∗
                ((fsp + 0x4ec#64) ↦₃₂ ((BitVec.ofNat 64 eBs.length) >>> 32).truncate 32) ⊢
                ((fsp + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 eBs.length) := by
              rw [← he8]; exact Entails.refl _
            have h130 :
                memRegion (fsp + 0x130#64) 24 ∗ ((fsp + 0x148#64) ↦₆₄ 64#64) ⊢
                  memRegion (fsp + 0x130#64) 0x20 := by
              refine Entails.trans (sepConj_mono_right (pointsTo64_entails_memRegion _ _)) ?_
              rw [r1b_join_region fsp 0x130 24 8]; exact Entails.refl _
            have h158 :
                ((fsp + 0x158#64) ↦₆₄ (spkPtr + 4#64 + BitVec.ofNat 64 spkKey.length)) ⊢
                  memRegion (fsp + 0x158#64) 8 :=
              pointsTo64_entails_memRegion _ _
            have h178 : ((fsp + 0x178#64) ↦₆₄ (spkPtr + 4#64)) ⊢
                memRegion (fsp + 0x178#64) 8 :=
              pointsTo64_entails_memRegion _ _
            refine r1b_sepWPp_frame_kp (by r1b_ac)
              (sepConj_mono he8' (sepConj_mono h130 (sepConj_mono h158 h178)))
              (by r1b_ac) ?_
            generalize herrCommon :
              r1b_errCommon
                (A.atState lim (M.stepEvents evsKpkSp (M.stepEvents evsKpkBr st)) sm3)
                g d s0 resStack = errCommon
            have hst_err :
                invCore ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
                  ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
                  memRegion fsp 0x110 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
                  ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
                  ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
                  ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
                  ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
                  memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
                  stackAt fsp (resStack - runFrame) ∗
                  A.pool lim (M.stepEvents evsKpkSp (M.stepEvents evsKpkBr st)) sm3 ⊢
                  errCommon ∗ memRegion (fsp + 0x190#64) 8 ∗ memRegion (fsp + 0x1a8#64) 16 := by
              rw [← hinvCore, ← herrCommon]
              exact r1b_stage_to_err_placed
                (A.atState lim (M.stepEvents evsKpkSp (M.stepEvents evsKpkBr st)) sm3)
                g d s0 resStack (ofLe32 r0 r1 r2 r3)
            have hcl := r1b_err_1b60_placed
              (st := M.stepEvents evsKpkSp (M.stepEvents evsKpkBr st))
              (v188_in := spkId.zeroExtend 64) (eCap := eCap) (ePtr := ePtr) (eBs := eBs)
              (kpkCap := kpkCap) (kpkPtr := kpkPtr) (kpkBs := kpkBs)
              (spkCap := spkCap) (spkPtr := spkPtr) (spkBs := spkBs)
              (regCap := regCap) (regPtr := regPtr) (regBs := [r0, r1, r2, r3])
              hh hdrop hbnd hc3
              (by simp only [hsm3, wp_norm, arm64_norm, speWord])
              (by simp only [hsm3, wp_norm, arm64_norm])
              (by simp only [hsm3, wp_norm, arm64_norm])
              (by simp only [hsm3, wp_norm, arm64_norm])
              (by solve
                | simp only [hsm3, wp_norm, arm64_norm]
                | simpa only [hsm3, wp_norm, arm64_norm] using hx26_2)
              (fun evsFree hfo => by
                simpa only [M.stepEvents_append, List.append_assoc] using
                  henv_kpk_split_err evsKpkBr kpkBs evsKpkSp evsFree
                    hkpk_rd hevsKpkBr' hsp_none hevsKpkSp hfo)
              hpanic hrej
            dsimp only at hcl
            rw [herrCommon] at hcl
            refine sepWPp_weaken_pre ?_ hcl
            exact r1b_entails_frame_kp (by r1b_ac) hst_err (by r1b_ac)
        · have hok2 : r1b_OkCtxPlacedFd r1b_CodeOk S g d s0 sf2 0x12bc := hok1.after_call
            (by simp only [hsm2, wp_norm, arm64_norm]) (by simp only [hsm2, wp_norm, arm64_norm])
            (by simp only [hsm2, wp_norm, arm64_norm]) (by simp only [hsm2, wp_norm, arm64_norm])
            (by simp only [hsm2, wp_norm, arm64_norm]) hfs_sm2
            hin2 hcs2 hfs_eq2 htr2
          have hx25_2 : sf2.readReg64 (.gpr 25#5) = d.dirPtr :=
            hcs2.2.2.2.2.2.2.1.trans
              (by solve | simp only [hsm2, wp_norm, arm64_norm] | simpa only [hsm2, wp_norm, arm64_norm] using hx25_1)
          have hx26_2 : sf2.readReg64 (.gpr 26#5) = kpkPtr :=
            hcs2.2.2.2.2.2.2.2.1.trans (by simp only [hsm2, wp_norm, arm64_norm])
          have hx27_2 : sf2.readReg64 (.gpr 27#5) = BitVec.ofNat 64 spkKey.length :=
            hcs2.2.2.2.2.2.2.2.2.1.trans
              (by solve | simp only [hsm2, wp_norm, arm64_norm] | simpa only [hsm2, wp_norm, arm64_norm] using hx27_1)
          have hx28_2 : sf2.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length :=
            hcs2.2.2.2.2.2.2.2.2.2.1.trans
              (by solve | simp only [hsm2, wp_norm, arm64_norm] | simpa only [hsm2, wp_norm, arm64_norm] using hx28_1)
          have hrejoin := r1b_ownedBytes_rejoin A.repAlloc kpkCap kpkPtr kpkBs hkpk_le hkpk_lt hkpk_ne
          refine r1b_sepWPp_frame_kp (by r1b_ac) hrejoin (by r1b_ac) ?_
          try simp only [BitVec.add_assoc]; try simp only [BitVec.reduceAdd]; try simp only [sepConj_assoc]
          try rw [← BitVec.add_assoc spkPtr 4#64]; try rw [← BitVec.add_assoc kpkPtr 4#64]
          dsimp only [splitOkTag]
          have hpc := hin2.pc; change sf2.pc = (blkPl_579).base + 4796#64 at hpc
          have hrun := hin2.run; have hsp : sf2.sp = fsp := hin2.sp
          apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 4828#64) hin2.inv
          dsimp only [runProgPlaced, lsProg_579]
          apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
            blkLib_eq_579 blk579_noSvc0 (mid := (blkPl_579).base + 4828#64)
          intro _m_strip; wp_steps
          refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
            (by simp only [wp_norm, arm64_norm, *]) fun _m_real hnsp => ?_
          have hvmp : VmPreserved sf2 _ :=
            hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
          try simp only [State.setMem_setMem] at hvmp ⊢
          apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
          refine r1b_bind_state_placed fun sm3 hsm3 hinv3 => by
            have hvm3 : VmPreserved sf2 sm3 := hsm3 ▸ hvmp
            have hfs_sm3 : sm3.fs = sf2.fs := by
              first
              | simp only [hsm3, wp_norm, arm64_norm]
              | simpa only [← hsm3, wp_norm, arm64_norm] using hnsp.2.2.2.2.2.2
            rw [← A.pool_transport lim (M.stepEvents evsKpkSp (M.stepEvents evsKpkBr st)) sf2 sm3 hvm3]
            change SepWPp (runProgPlaced H) _ _ _ _ _ _
            have hok3 : r1b_OkCtxPlacedFd r1b_CodeOk S g d s0 sm3 0x12dc := hok2.of_step
              { pc := by simp only [hsm3, wp_norm, arm64_norm]
                run := by simp only [hsm3, wp_norm, arm64_norm, hin2.run]
                sp := by simpa only [hsm3, wp_norm, arm64_norm] using hin2.sp
                fp := by simpa only [hsm3, wp_norm, arm64_norm] using hin2.fp
                inv := hinv3
                vregs := by simpa only [calleeSavedVRegs, hsm3, wp_norm, arm64_norm] using hin2.vregs
                spAligned := hst.spAligned }
              (by simp only [hsm3, wp_norm, arm64_norm]) (by simp only [hsm3, wp_norm, arm64_norm])
              (by simp only [hsm3, wp_norm, arm64_norm]) (by simp only [hsm3, wp_norm, arm64_norm])
              (by simp only [hsm3, wp_norm, arm64_norm]) hfs_sm3
            try rw [hx23_1]
            try rw [hx10]
            try rw [show s.readReg64 (.gpr 2#5) = spkId.zeroExtend 64 from hx2]
            try rw [hx2]
            have h4d0_48 :
                ((fsp + 0x4d0#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
                  ((fsp + 0x4d8#64) ↦₆₄ (kpkPtr + 4#64)) ∗
                  ((fsp + 0x4e0#64) ↦₆₄ BitVec.ofNat 64 kpkKey.length) ∗
                  ((fsp + 0x4e8#64) ↦₃₂ kpkId) ∗
                  memRegion (fsp + 0x4ec#64) 4 ∗
                  ((fsp + 0x4f0#64) ↦₆₄ (kpkPtr + 4#64 + BitVec.ofNat 64 kpkKey.length)) ∗
                  ((fsp + 0x4f8#64) ↦₆₄ 64#64) ⊢ memRegion (fsp + 0x4d0#64) 48 := by
              have h4d0_32 :
                  ((fsp + 0x4d0#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
                    ((fsp + 0x4d8#64) ↦₆₄ (kpkPtr + 4#64)) ∗
                    ((fsp + 0x4e0#64) ↦₆₄ BitVec.ofNat 64 kpkKey.length) ∗
                    (((fsp + 0x4e8#64) ↦₃₂ kpkId) ∗ memRegion (fsp + 0x4ec#64) 4) ⊢
                    memRegion (fsp + 0x4d0#64) 32 := by
                refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_left (pointsTo32_entails_memRegion _ _))))) ?_
                rw [r1b_join_region fsp 0x4e8 4 4]
                refine Entails.trans (sepConj_mono_right (sepConj_mono_right (by
                  simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
                    r1b_cell64_cons (a := fsp + 0x4e0#64) (BitVec.ofNat 64 kpkKey.length) (n := 8) (by decide)))) ?_
                refine Entails.trans (sepConj_mono_right (by
                  simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
                    r1b_cell64_cons (a := fsp + 0x4d8#64) (kpkPtr + 4#64) (n := 16) (by decide))) ?_
                simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
                  r1b_cell64_cons (a := fsp + 0x4d0#64) 0xfffffffffffffffe#64 (n := 24) (by decide)
              have h4f0_16 :
                  ((fsp + 0x4f0#64) ↦₆₄ (kpkPtr + 4#64 + BitVec.ofNat 64 kpkKey.length)) ∗
                    ((fsp + 0x4f8#64) ↦₆₄ 64#64) ⊢ memRegion (fsp + 0x4f0#64) 16 := by
                simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
                  r1b_cells2_to_region16 (fsp + 0x4f0#64)
                    (kpkPtr + 4#64 + BitVec.ofNat 64 kpkKey.length) 64#64
              refine Entails.trans (Entails.of_eq (show _ =
                (((fsp + 0x4d0#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
                  ((fsp + 0x4d8#64) ↦₆₄ (kpkPtr + 4#64)) ∗
                  ((fsp + 0x4e0#64) ↦₆₄ BitVec.ofNat 64 kpkKey.length) ∗
                  (((fsp + 0x4e8#64) ↦₃₂ kpkId) ∗ memRegion (fsp + 0x4ec#64) 4)) ∗
                (((fsp + 0x4f0#64) ↦₆₄ (kpkPtr + 4#64 + BitVec.ofNat 64 kpkKey.length)) ∗
                  ((fsp + 0x4f8#64) ↦₆₄ 64#64)) by r1b_ac)) ?_
              rw [← r1b_join_region fsp 0x4d0 32 16]
              exact sepConj_mono h4d0_32 h4f0_16
            have hcont := hk sm3 evsKpkBr evsKpkSp kpkCap kpkPtr kpkBs kpkKey kpkSig kpkId
              hevsKpkBr' hevsKpkSp hok3 hkpk_rd hsp_ok
              (by solve
                | simp only [hsm3, wp_norm, arm64_norm]
                | simpa only [hsm3, wp_norm, arm64_norm] using hx25_2)
              (by solve
                | simp only [hsm3, wp_norm, arm64_norm]
                | simpa only [hsm3, wp_norm, arm64_norm] using hx28_2)
              (by solve
                | simp only [hsm3, wp_norm, arm64_norm]
                | simpa only [hsm3, wp_norm, arm64_norm] using hx26_2)
              (by solve
                | simp only [hsm3, wp_norm, arm64_norm]
                | simpa only [hsm3, wp_norm, arm64_norm] using hx27_2)
              (by simp only [hsm3, wp_norm, arm64_norm])
              (by simp only [hsm3, wp_norm, arm64_norm])
              (by simp only [hsm3, wp_norm, arm64_norm])
              (by simp only [hsm3, wp_norm, arm64_norm])
              (by simp only [hsm3, wp_norm, arm64_norm])
            dsimp only [fsp] at h4d0_48 ⊢
            rw [← M.stepEvents_append]
            dsimp only at hcont
            refine sepWPp_weaken_pre ?_ hcont
            exact r1b_entails_frame_kp (by r1b_ac) h4d0_48 (by r1b_ac)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadKpkPlacedBudgetFd
