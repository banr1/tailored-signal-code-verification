/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.DeserCloneErrPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupUpperPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadOpkPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadOpkSpinePlacedBudget
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public meta import ProofLib -- shake: keep
public meta import Lean -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSites

/-!
# Budget-Threaded Stage 4a Deserialization Error Cleanup for Arm `R1b`

Verifies `r1b_spk_err_at_2adc_placed`, `r1b_spk_err_24fc_placed` (`0x24fc → 0x2adc`), and
`r1b_kem_err_2654_placed` (`0x2654 → 0x2adc`, freeing `spkSigPtr`) on Block `579` under
`[LibsignalPlacement]` and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.DeserCloneErrPlacedBudget

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (PublicKey SignalProtocolError)
open CryptoVerification (LibsignalHooks LibsignalPlacement lsLogFilterAddr lsρ)
open CryptoVerification.LibsignalTripleRatchet.Wire
  (deserializeResult33At memRegion33_of_err_badKeyLength memRegion33_of_err_badKeyType
   memRegion33_of_err_base)
open CryptoVerification.LibsignalTripleRatchetRepr (speWord)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli (StoresGhost ofLe32)
open CryptoVerification.SignalSession.Cli.MainHops (RunCall ownedBytes sepWPp_weaken_pre)
open CryptoVerification.SignalSession.Cli.Run.Placed
  (blkLib_eq_579 blkPC_579 blkPl_579 lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (AtRejectPlaced Init1Data PanicK RejectKind r1b_CodeOk r1b_ErrCtxPlaced r1b_SpePayload_plain
   r1b_StackBounds r1b_bind_state_placed r1b_cells2_to_region16 r1b_cells6_to_region48
   r1b_entails_frame_core r1b_errCommon r1b_errCore r1b_fsp_align r1b_invCore_placed
   r1b_invCoreBase_placed r1b_invCore_split_mid_placed r1b_invCore_to_errCommon_placed
   r1b_join_region r1b_opkStage1SpkAt r1b_opkStage1Spk_to_regions r1b_sepWPp_frame_core
   r1b_sig64_to_ownedBytes r1b_split_region rejectMem runFsp runPcPlaced runPcPlaced_eq
   runProgPlaced)
open CryptoVerification.SignalSession.Cli.RunDrop (PlainSpeTag)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets runFrame)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved
   rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CommonPlacedBudget
  (r1b_call_dealloc_ownedBytes_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupPlacedBudget
  (r1b_errCommon_atState_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadKpkPlacedBudgetAux
  (r1b_cleanup_2adc_placed r1b_seq_lscro_oom)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpkPlacedBudgetAux
  (blk579_noSvc0)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget (RejectKPlacedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget
  (DropSpeOwnedOkAtBlock)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local simp, local arm64_norm, local wp_norm] runPcPlaced_eq BitVec.ofNat_eq_ofNat

local macro (priority := high) "r1b_ac" : tactic =>
  `(tactic| ((try dsimp +zetaDelta only) <;> first | rfl | simp only [emp_sepConj] | sep_ac_rfl))

private meta def r1bStripLetsDE : Nat → Lean.Expr → Lean.Expr
  | 0, e => e
  | n + 1, .letE _ _ v b _ => r1bStripLetsDE n (b.instantiate1 v)
  | n + 1, .mdata _ e => r1bStripLetsDE n e
  | _, e => e

private meta def r1bSplitSepDE : Nat → Lean.Expr → Lean.Expr → Array Lean.Expr
  | 0, _, e => #[e]
  | fuel + 1, sepSample, e =>
    let e := r1bStripLetsDE 64 e; let ar := sepSample.getAppNumArgs
    if e.isAppOfArity sepSample.getAppFn.constName! ar then
      r1bSplitSepDE fuel sepSample (e.getArg! (ar - 2)) ++ r1bSplitSepDE fuel sepSample (e.getArg! (ar - 1))
    else #[e]

private meta def r1bIsDefEqPureDE (x a : Lean.Expr) : Lean.Elab.TermElabM Bool := do
  let x := r1bStripLetsDE 64 x; let a := r1bStripLetsDE 64 a
  let xf := x.getAppFn; let af := a.getAppFn
  if xf.constName? != af.constName? || x.getAppNumArgs != a.getAppNumArgs then return false
  let st ← Lean.saveState
  let mut ok ← if xf.constName?.isNone then
      if xf.isFVar != af.isFVar || xf.isProj != af.isProj then pure false
      else Lean.Meta.withReducibleAndInstances <| Lean.Meta.isDefEq xf af
    else pure true
  for i in [0:x.getAppNumArgs] do
    if ok then ok ← Lean.Meta.withReducibleAndInstances <| Lean.Meta.isDefEq (x.getArg! i) (a.getArg! i)
  st.restore; return ok

private meta def r1bComputeRestDE (ctxName : String) (p a1 : Lean.Expr) : Lean.Elab.TermElabM Lean.Expr := do
  let sepTy := Lean.mkConst ``SepProp []
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let mut rem := (r1bSplitSepDE 64 sepSample (← Lean.instantiateMVars p)).toList
  for a in (r1bSplitSepDE 64 sepSample (← Lean.instantiateMVars a1)).toList do
    let mut removed := false; let mut next : List Lean.Expr := []
    for x in rem do
      if !removed && (← r1bIsDefEqPureDE x a) then removed := true else next := next.concat x
    if !removed then throwError "{ctxName}: unmatched atom:\n  {a}\nin:\n  {rem}"
    rem := next
  let ar := sepSample.getAppNumArgs
  let mkSep (l r : Lean.Expr) := sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (ar - 2) ++ #[l, r])
  match rem.reverse with | [] => return empExpr | last :: rest => return rest.foldl (fun acc x => mkSep x acc) last

local elab (priority := high) "r1b_entails_frame_de " t1:term:arg h:term:arg t2:term:arg : term <= expectedType => do
  let exp ← Lean.instantiateMVars expectedType; if exp.isMVar then Lean.Elab.Term.tryPostpone
  let ear := (← Lean.Elab.Term.elabTerm (← `(emp ⊢ emp)) none).getAppNumArgs
  let expS := r1bStripLetsDE 64 exp; let p := expS.getArg! (ear - 2); let q := expS.getArg! (ear - 1)
  if (← Lean.instantiateMVars p).isMVar || (← Lean.instantiateMVars q).isMVar then Lean.Elab.Term.tryPostpone
  let hExpr ← Lean.Elab.Term.elabTerm h none
  let hTy := r1bStripLetsDE 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
  let a1 := hTy.getArg! (ear - 2); let a2 := hTy.getArg! (ear - 1)
  let r ← r1bComputeRestDE "r1b_entails_frame" p a1; let sepTy := Lean.mkConst ``SepProp []
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy); let sar := sepSample.getAppNumArgs
  let mkSep (x y : Lean.Expr) := sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
  if (← r1bIsDefEqPureDE r empExpr) then
    let h1Expr ← Lean.Elab.Term.elabTerm t1 (some (← Lean.Meta.mkEq p a1))
    let h2Expr ← Lean.Elab.Term.elabTerm t2 (some (← Lean.Meta.mkEq a2 q))
    Lean.Meta.mkAppM ``Entails.trans #[← Lean.Meta.mkAppM ``Entails.of_eq #[h1Expr],
      ← Lean.Meta.mkAppM ``Entails.trans #[hExpr, ← Lean.Meta.mkAppM ``Entails.of_eq #[h2Expr]]]
  else
    let h1Expr ← Lean.Elab.Term.elabTerm t1 (some (← Lean.Meta.mkEq p (mkSep a1 r)))
    let h2Expr ← Lean.Elab.Term.elabTerm t2 (some (← Lean.Meta.mkEq (mkSep a2 r) q))
    Lean.Meta.mkAppOptM ``r1b_entails_frame_core #[some a1, some a2, some r, some p, some q, h1Expr, hExpr, h2Expr]

local elab (priority := high) "r1b_sepWPp_frame_de " t1:term:arg h:term:arg t2:term:arg hk:term:arg : term <= expectedType => do
  let exp ← Lean.instantiateMVars expectedType; if exp.isMVar then Lean.Elab.Term.tryPostpone
  let expS := r1bStripLetsDE 64 exp; let args := expS.getAppArgs
  let prog := args[0]!; let ret := args[1]!; let st := args[2]!; let p := args[3]!
  let q := args[4]!; let qp := args[5]!; let oom := args[6]!
  let ear := (← Lean.Elab.Term.elabTerm (← `(emp ⊢ emp)) none).getAppNumArgs
  let hExpr ← Lean.Elab.Term.elabTerm h none
  let hTy := r1bStripLetsDE 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
  let a1 := hTy.getArg! (ear - 2); let a2 := hTy.getArg! (ear - 1)
  let r ← r1bComputeRestDE "r1b_sepWPp_frame" p a1; let sepTy := Lean.mkConst ``SepProp []
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy); let sar := sepSample.getAppNumArgs
  let mkSep (x y : Lean.Expr) := sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
  if (← r1bIsDefEqPureDE r empExpr) then
    let h1Expr ← Lean.Elab.Term.elabTerm t1 (some (← Lean.Meta.mkEq p a1))
    let h2Expr ← Lean.Elab.Term.elabTerm t2 (some (← Lean.Meta.mkEq a2 a2))
    let hkExpr ← Lean.Elab.Term.elabTerm hk (some (Lean.mkAppN expS.getAppFn #[prog, ret, st, a2, q, qp, oom]))
    let hent ← Lean.Meta.mkAppM ``Entails.trans #[← Lean.Meta.mkAppM ``Entails.of_eq #[h1Expr],
      ← Lean.Meta.mkAppM ``Entails.trans #[hExpr, ← Lean.Meta.mkAppM ``Entails.of_eq #[h2Expr]]]
    Lean.Meta.mkAppM ``sepWPp_weaken_pre #[hent, hkExpr]
  else
    let p' := if (← r1bIsDefEqPureDE a2 empExpr) then r else mkSep a2 r
    let h1Expr ← Lean.Elab.Term.elabTerm t1 (some (← Lean.Meta.mkEq p (mkSep a1 r)))
    let h2Expr ← Lean.Elab.Term.elabTerm t2 (some (← Lean.Meta.mkEq (mkSep a2 r) p'))
    let hkExpr ← Lean.Elab.Term.elabTerm hk (some (Lean.mkAppN expS.getAppFn #[prog, ret, st, p', q, qp, oom]))
    Lean.Meta.mkAppOptM ``r1b_sepWPp_frame_core
      #[some prog, some ret, some st, some a1, some a2, some r, some p, some p', some q, some qp, some oom,
        h1Expr, hExpr, h2Expr, hkExpr]

local elab:10 (priority := high) "r1b_call_frame_de" "<|" h:term:10 : term <= expectedType => do
  let exp ← Lean.instantiateMVars expectedType; if exp.isMVar then Lean.Elab.Term.tryPostpone
  let expS := r1bStripLetsDE 64 exp; let hExpr ← Lean.Elab.Term.elabTerm h none
  let hTy0 := r1bStripLetsDE 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
  for idx in [0, 1, 2, 4, 5, 6] do
    if !(← Lean.Meta.withReducibleAndInstances <| Lean.Meta.isDefEq (hTy0.getArg! idx) (expS.getArg! idx)) then
      discard <| Lean.Meta.isDefEq (hTy0.getArg! idx) (expS.getArg! idx)
  let p ← Lean.instantiateMVars (expS.getArg! 3)
  let p' ← Lean.instantiateMVars ((r1bStripLetsDE 64 (← Lean.instantiateMVars hTy0)).getArg! 3)
  let sepTy := Lean.mkConst ``SepProp []; let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy); let sar := sepSample.getAppNumArgs
  let mkSep (x y : Lean.Expr) := sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
  let mut mvarFOpt : Option Lean.Expr := none; let mut a1s : List Lean.Expr := []
  for a in (r1bSplitSepDE 64 sepSample p').toList do
    let ai ← Lean.instantiateMVars a
    if mvarFOpt.isNone && ai.isMVar then mvarFOpt := some ai else a1s := a1s.concat ai
  let mut rem := (r1bSplitSepDE 64 sepSample p).toList
  for a in a1s do
    let mut removed := false; let mut next : List Lean.Expr := []
    for x in rem do
      if !removed && (← r1bIsDefEqPureDE x a) then removed := true else next := next.concat x
    if !removed then throwError "r1b_call_frame: unmatched callee atom:\n  {a}\nin:\n  {rem}"
    rem := next
  let remProd := match rem.reverse with | [] => empExpr | last :: rest => rest.foldl (fun acc x => mkSep x acc) last
  if let some mf := mvarFOpt then discard <| Lean.Meta.withReducibleAndInstances <| Lean.Meta.isDefEq mf remProd
  let eqProof ← Lean.Elab.Term.elabTerm (← `(by r1b_ac)) (some (← Lean.Meta.mkEq (← Lean.instantiateMVars p) (← Lean.instantiateMVars p')))
  Lean.Meta.mkAppM ``sepWPp_weaken_pre #[← Lean.Meta.mkAppM ``Entails.of_eq #[eqProof], hExpr]

theorem r1b_spk_err_at_2adc_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {i : Nat} {v188 kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen : BitVec 64}
    {kpkBs spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2adc)
    (hi : PlainSpeTag i)
    (hx12 : s.readReg64 (.gpr 12#5) = speWord i)
    (hx1 : s.readReg64 (.gpr 1#5) = kpkCap)
    (hx26 : s.readReg64 (.gpr 26#5) = kpkPtr)
    (hpanic : PanicK g s0 Qp)
    (hrej : ∀ (sf : State) (evs : List AllocEvent),
      FreeOnlyEvs evs →
      AtRejectPlaced r1b_CodeOk g StoresGhost.opened .postDispatch s0 sf →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (rejectMem (A.atState lim (M.stepEvents evs st) sf)
          g StoresGhost.opened .postDispatch s0 resStack)
        Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (ownedBytes A.repAlloc kpkCap kpkPtr kpkLen kpkBs ∗
        ownedBytes A.repAlloc spkCap spkPtr spkLen spkBs ∗
        ownedBytes A.repAlloc regCap regPtr regLen regBs ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        ((fsp + 0x188#64) ↦₆₄ v188) ∗ memRegion (fsp + 0x190#64) 8 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16 ∗ memRegion (fsp + 0x4d0#64) 48)
      Q Qp oom := by
  intro fsp
  refine sepWPp_weaken_pre ?_
    (r1b_cleanup_2adc_placed (st := st) (v188 := v188)
      (kpkCap := kpkCap) (kpkPtr := kpkPtr) (kpkLen := kpkLen) (kpkBs := kpkBs)
      (spkCap := spkCap) (spkPtr := spkPtr) (spkLen := spkLen) (spkBs := spkBs)
      (regCap := regCap) (regPtr := regPtr) (regLen := regLen) (regBs := regBs)
      hh hdrop hbnd hc hx1 hx26 hpanic hrej)
  conv => lhs; rw [← emp_sepConj (ownedBytes A.repAlloc kpkCap kpkPtr kpkLen kpkBs ∗ _)]
  rw [hx12]
  exact sepConj_mono_left (r1b_SpePayload_plain A.repAlloc hi _ _ _ _ _ _ _ _)

theorem r1b_spk_err_at_2adc_placed_env [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {i : Nat} {v188 kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen : BitVec 64}
    {kpkBs spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2adc)
    (hi : PlainSpeTag i)
    (hx12 : s.readReg64 (.gpr 12#5) = speWord i)
    (hx1 : s.readReg64 (.gpr 1#5) = kpkCap)
    (hx26 : s.readReg64 (.gpr 26#5) = kpkPtr)
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectKPlacedEnv r1b_CodeOk H A lim EnvAt g s0 resStack Q Qp oom)
    (henv : ∀ evs, FreeOnlyEvs evs → EnvAt StoresGhost.opened .postDispatch (M.stepEvents evs st)) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (ownedBytes A.repAlloc kpkCap kpkPtr kpkLen kpkBs ∗
        ownedBytes A.repAlloc spkCap spkPtr spkLen spkBs ∗
        ownedBytes A.repAlloc regCap regPtr regLen regBs ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        ((fsp + 0x188#64) ↦₆₄ v188) ∗ memRegion (fsp + 0x190#64) 8 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16 ∗ memRegion (fsp + 0x4d0#64) 48)
      Q Qp oom :=
  r1b_spk_err_at_2adc_placed hh hdrop hbnd hc hi hx12 hx1 hx26 hpanic fun sf evs hfo hrej_f =>
    hrej sf (M.stepEvents evs st) StoresGhost.opened .postDispatch hrej_f (henv evs hfo)

/-- Budget-threaded error exit from `<PublicKey>::deserialize` on `spkKey` (`0x24fc → 0x2adc`). -/
theorem r1b_spk_err_24fc_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {kpkCap kpkPtr spkCap spkPtr regCap regPtr v188_in : BitVec 64}
    {kpkBs spkBs spkKey regBs : List (BitVec 8)}
    {e : SignalProtocolError}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x24fc)
    (_hd : PublicKey.deserialize spkKey = .error e)
    (hpanic : PanicK g s0 Qp)
    (hrej : ∀ (sf : State) (evs : List AllocEvent),
      FreeOnlyEvs evs →
      AtRejectPlaced r1b_CodeOk g StoresGhost.opened .postDispatch s0 sf →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (rejectMem (A.atState lim (M.stepEvents evs st) sf)
          g StoresGhost.opened .postDispatch s0 resStack)
        Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (deserializeResult33At (fsp + 0x4d0#64) (.error e) ∗
        memRegion (fsp + 0x4f1#64) 15 ∗
        ownedBytes A.repAlloc kpkCap kpkPtr (BitVec.ofNat 64 kpkBs.length) kpkBs ∗
        ownedBytes A.repAlloc spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
        ownedBytes A.repAlloc regCap regPtr 4#64 regBs ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 8 ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ memRegion (fsp + 0x158#64) 8 ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        ((fsp + 0x188#64) ↦₆₄ v188_in) ∗ memRegion (fsp + 0x190#64) 8 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16)
      Q Qp oom := by
  intro fsp
  rw [r1b_errCommon_atState_eq]
  generalize herrCore : r1b_errCore A.repAlloc g d s0 = errCore
  have hst := hc.st
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hst.spAligned
  have hal4e0 : (fsp + 0x4e0#64) &&& 7#64 = 0#64 := by bv_bits
  let _ := hal; let _ := hal4e0
  have hpc0 := hst.pc
  change s.pc = (blkPl_579).base + 0x24fc#64 at hpc0
  have h120_join : ∀ v : BitVec 64,
      memRegion (fsp + 0x120#64) 8 ∗ ((fsp + 0x128#64) ↦₆₄ v) ⊢
        memRegion (fsp + 0x120#64) 16 := fun v => by
    refine Entails.trans (sepConj_mono_right (pointsTo64_entails_memRegion _ _)) ?_
    rw [r1b_join_region fsp 0x120 8 8]; exact Entails.refl _
  have h150_join : ∀ v : BitVec 64,
      ((fsp + 0x150#64) ↦₆₄ v) ∗ memRegion (fsp + 0x158#64) 8 ⊢
        memRegion (fsp + 0x150#64) 16 := fun v => by
    refine Entails.trans (sepConj_mono_left (pointsTo64_entails_memRegion _ _)) ?_
    rw [r1b_join_region fsp 0x150 8 8]; exact Entails.refl _
  cases e with
  | noKeyTypeIdentifier =>
    dsimp only [deserializeResult33At]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x2adc#64) hst.inv
    have hpc := hpc0; have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
    dsimp only [runProgPlaced, lsProg_579]
    apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
      blkLib_eq_579 blk579_noSvc0 (mid := (blkPl_579).base + 0x2adc#64)
    intro _m_strip; have hpc_s : (s.setMem _m_strip).pc = (blkPl_579).base + 0x24fc#64 := hpc
    wp_steps; clear hpc_s
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [wp_norm, arm64_norm, *]) fun _m_real hnsp => ?_
    have hvmp : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
    try simp only [State.setMem_setMem] at hvmp ⊢
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    clear hpc hrun hsp
    refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
    have hvm : VmPreserved s sm := hsm ▸ hvmp
    rw [← A.pool_transport lim st s sm hvm]
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hc_m : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm 0x2adc := hc.of_step
      { pc := by rw [runPcPlaced_eq]; simp [hsm, arm64_norm]
        run := by simp [hsm, arm64_norm, hst.run]
        sp := by simpa [hsm, arm64_norm] using hst.sp
        fp := by simpa [hsm, arm64_norm] using hst.fp
        inv := hinv_m
        vregs := by simpa [calleeSavedVRegs, hsm, arm64_norm] using hst.vregs
        spAligned := hst.spAligned }
      (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
      (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
    have h4d0 :
        ((fsp + 0x4d0#64) ↦₈ 1#8) ∗ memRegion (fsp + 0x4d1#64) 7 ∗
          ((fsp + 0x4d8#64) ↦₈ 0#8) ∗ memRegion (fsp + 0x4d9#64) 24 ∗
          memRegion (fsp + 0x4f1#64) 15 ⊢ memRegion (fsp + 0x4d0#64) 48 := by
      have h33 := memRegion33_of_err_base (fsp + 0x4d0#64) 0#8
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at h33
      refine Entails.trans (r1b_entails_frame_de (by r1b_ac) h33 (by r1b_ac)) ?_
      rw [r1b_join_region fsp 0x4d0 33 15]; exact Entails.refl _
    have hcl := r1b_spk_err_at_2adc_placed (st := st) (i := 7) (v188 := 0#64)
      (kpkCap := kpkCap) (kpkPtr := kpkPtr) (kpkLen := BitVec.ofNat 64 kpkBs.length) (kpkBs := kpkBs)
      (spkCap := spkCap) (spkPtr := spkPtr) (spkLen := BitVec.ofNat 64 spkBs.length) (spkBs := spkBs)
      (regCap := regCap) (regPtr := regPtr) (regLen := 4#64) (regBs := regBs)
      hh hdrop hbnd hc_m (by decide)
      (by simp [hsm, arm64_norm, speWord])
      (by simp [hsm, arm64_norm])
      (by simp [hsm, arm64_norm])
      hpanic hrej
    dsimp only at hcl
    rw [r1b_errCommon_atState_eq, herrCore] at hcl
    exact sepWPp_weaken_pre
      (r1b_entails_frame_de (by r1b_ac)
        (sepConj_mono h4d0 (sepConj_mono (h120_join kpkPtr) (h150_join kpkCap))) (by r1b_ac))
      hcl
  | badKeyType t =>
    dsimp only [deserializeResult33At]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x2adc#64) hst.inv
    have hpc := hpc0; have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
    dsimp only [runProgPlaced, lsProg_579]
    apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
      blkLib_eq_579 blk579_noSvc0 (mid := (blkPl_579).base + 0x2adc#64)
    intro _m_strip; have hpc_s : (s.setMem _m_strip).pc = (blkPl_579).base + 0x24fc#64 := hpc
    wp_steps; clear hpc_s
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [wp_norm, arm64_norm, *]) fun _m_real hnsp => ?_
    have hvmp : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
    try simp only [State.setMem_setMem] at hvmp ⊢
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    clear hpc hrun hsp
    refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
    have hvm : VmPreserved s sm := hsm ▸ hvmp
    rw [← A.pool_transport lim st s sm hvm]
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hc_m : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm 0x2adc := hc.of_step
      { pc := by rw [runPcPlaced_eq]; simp [hsm, arm64_norm]
        run := by simp [hsm, arm64_norm, hst.run]
        sp := by simpa [hsm, arm64_norm] using hst.sp
        fp := by simpa [hsm, arm64_norm] using hst.fp
        inv := hinv_m
        vregs := by simpa [calleeSavedVRegs, hsm, arm64_norm] using hst.vregs
        spAligned := hst.spAligned }
      (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
      (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
    have h4d0 :
        ((fsp + 0x4d0#64) ↦₈ 1#8) ∗ memRegion (fsp + 0x4d1#64) 7 ∗
          ((fsp + 0x4d8#64) ↦₈ 1#8) ∗ ((fsp + 0x4d9#64) ↦₈ t) ∗
          memRegion (fsp + 0x4da#64) 23 ∗ memRegion (fsp + 0x4f1#64) 15 ⊢
          memRegion (fsp + 0x4d0#64) 48 := by
      have h33 := memRegion33_of_err_badKeyType (fsp + 0x4d0#64) t
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at h33
      refine Entails.trans (r1b_entails_frame_de (by r1b_ac) h33 (by r1b_ac)) ?_
      rw [r1b_join_region fsp 0x4d0 33 15]; exact Entails.refl _
    have hcl := r1b_spk_err_at_2adc_placed (st := st) (i := 8) (v188 := 0#64)
      (kpkCap := kpkCap) (kpkPtr := kpkPtr) (kpkLen := BitVec.ofNat 64 kpkBs.length) (kpkBs := kpkBs)
      (spkCap := spkCap) (spkPtr := spkPtr) (spkLen := BitVec.ofNat 64 spkBs.length) (spkBs := spkBs)
      (regCap := regCap) (regPtr := regPtr) (regLen := 4#64) (regBs := regBs)
      hh hdrop hbnd hc_m (by decide)
      (by simp [hsm, arm64_norm, speWord])
      (by simp [hsm, arm64_norm])
      (by simp [hsm, arm64_norm])
      hpanic hrej
    dsimp only at hcl
    rw [r1b_errCommon_atState_eq, herrCore] at hcl
    exact sepWPp_weaken_pre
      (r1b_entails_frame_de (by r1b_ac)
        (sepConj_mono h4d0 (sepConj_mono (h120_join kpkPtr) (h150_join kpkCap))) (by r1b_ac))
      hcl
  | badKeyLength n =>
    dsimp only [deserializeResult33At]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x2adc#64) hst.inv
    have hpc := hpc0; have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
    dsimp only [runProgPlaced, lsProg_579]
    apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
      blkLib_eq_579 blk579_noSvc0 (mid := (blkPl_579).base + 0x2adc#64)
    intro _m_strip; have hpc_s : (s.setMem _m_strip).pc = (blkPl_579).base + 0x24fc#64 := hpc
    wp_steps; clear hpc_s
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [wp_norm, arm64_norm, *]) fun _m_real hnsp => ?_
    have hvmp : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
    try simp only [State.setMem_setMem] at hvmp ⊢
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    clear hpc hrun hsp
    refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
    have hvm : VmPreserved s sm := hsm ▸ hvmp
    rw [← A.pool_transport lim st s sm hvm]
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hc_m : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm 0x2adc := hc.of_step
      { pc := by rw [runPcPlaced_eq]; simp [hsm, arm64_norm]
        run := by simp [hsm, arm64_norm, hst.run]
        sp := by simpa [hsm, arm64_norm] using hst.sp
        fp := by simpa [hsm, arm64_norm] using hst.fp
        inv := hinv_m
        vregs := by simpa [calleeSavedVRegs, hsm, arm64_norm] using hst.vregs
        spAligned := hst.spAligned }
      (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
      (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
    have h4d0 :
        ((fsp + 0x4d0#64) ↦₈ 1#8) ∗ memRegion (fsp + 0x4d1#64) 7 ∗
          ((fsp + 0x4d8#64) ↦₈ 2#8) ∗ memRegion (fsp + 0x4d9#64) 7 ∗
          ((fsp + 0x4e0#64) ↦₆₄ BitVec.ofNat 64 n) ∗ memRegion (fsp + 0x4e8#64) 9 ∗
          memRegion (fsp + 0x4f1#64) 15 ⊢ memRegion (fsp + 0x4d0#64) 48 := by
      have h33 := memRegion33_of_err_badKeyLength (fsp + 0x4d0#64) n
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at h33
      refine Entails.trans (r1b_entails_frame_de (by r1b_ac) h33 (by r1b_ac)) ?_
      rw [r1b_join_region fsp 0x4d0 33 15]; exact Entails.refl _
    have hcl := r1b_spk_err_at_2adc_placed (st := st) (i := 9) (v188 := BitVec.ofNat 64 n &&& -256#64)
      (kpkCap := kpkCap) (kpkPtr := kpkPtr) (kpkLen := BitVec.ofNat 64 kpkBs.length) (kpkBs := kpkBs)
      (spkCap := spkCap) (spkPtr := spkPtr) (spkLen := BitVec.ofNat 64 spkBs.length) (spkBs := spkBs)
      (regCap := regCap) (regPtr := regPtr) (regLen := 4#64) (regBs := regBs)
      hh hdrop hbnd hc_m (by decide)
      (by simp [hsm, arm64_norm, speWord])
      (by simp [hsm, arm64_norm])
      (by simp [hsm, arm64_norm])
      hpanic hrej
    dsimp only at hcl
    rw [r1b_errCommon_atState_eq, herrCore] at hcl
    exact sepWPp_weaken_pre
      (r1b_entails_frame_de (by r1b_ac)
        (sepConj_mono h4d0 (sepConj_mono (h120_join kpkPtr) (h150_join kpkCap))) (by r1b_ac))
      hcl
  | _ =>
    dsimp only [deserializeResult33At]
    exact SepWPp.pure_elim False.elim

theorem r1b_spk_err_24fc_placed_env [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {kpkCap kpkPtr spkCap spkPtr regCap regPtr v188_in : BitVec 64}
    {kpkBs spkBs spkKey regBs : List (BitVec 8)}
    {e : SignalProtocolError}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x24fc)
    (hd : PublicKey.deserialize spkKey = .error e)
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectKPlacedEnv r1b_CodeOk H A lim EnvAt g s0 resStack Q Qp oom)
    (henv : ∀ evs, FreeOnlyEvs evs → EnvAt StoresGhost.opened .postDispatch (M.stepEvents evs st)) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (deserializeResult33At (fsp + 0x4d0#64) (.error e) ∗
        memRegion (fsp + 0x4f1#64) 15 ∗
        ownedBytes A.repAlloc kpkCap kpkPtr (BitVec.ofNat 64 kpkBs.length) kpkBs ∗
        ownedBytes A.repAlloc spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
        ownedBytes A.repAlloc regCap regPtr 4#64 regBs ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 8 ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ memRegion (fsp + 0x158#64) 8 ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        ((fsp + 0x188#64) ↦₆₄ v188_in) ∗ memRegion (fsp + 0x190#64) 8 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16)
      Q Qp oom :=
  r1b_spk_err_24fc_placed hh hdrop hbnd hc hd hpanic fun sf evs hfo hrej_f =>
    hrej sf (M.stepEvents evs st) StoresGhost.opened .postDispatch hrej_f (henv evs hfo)

/-- Budget-threaded `kem::Key::deserialize` error cleanup (`0x2654 → 0x2adc`) freeing `spkSigPtr` for plain `SignalProtocolError` tag `i`. -/
theorem r1b_kem_err_2654_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {i : Nat}
    {spkW0 : BitVec 64} {spkW8 : BitVec 32} {spkW16 spkW24 : BitVec 64}
    {b0 b1 b2 b3 b4 b5 b6 : BitVec 8}
    {w0e0 w0e4 w9 : BitVec 32} {w13 : BitVec 16} {w15 w23 : BitVec 64} {b31 : BitVec 8}
    {r0 r1 r2 r3 : BitVec 8} {v11c : BitVec 32}
    {spkSigPtr kpkCap kpkPtr spkCap spkPtr regCap regPtr : BitVec 64}
    {v130 v138 w4d8 w4e0 v188_in : BitVec 64}
    {spkSig kpkBs spkBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2654)
    (hi : PlainSpeTag i)
    (hspk_ptr : spkSigPtr ≠ 0)
    (hspk_sig : spkSig.length = 64)
    (hpanic : PanicK g s0 Qp)
    (hrej : ∀ (sf : State) (evs : List AllocEvent),
      FreeOnlyEvs evs →
      AtRejectPlaced r1b_CodeOk g StoresGhost.opened .postDispatch s0 sf →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (rejectMem (A.atState lim (M.stepEvents evs st) sf)
          g StoresGhost.opened .postDispatch s0 resStack)
        Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (((fsp + 0x4d0#64) ↦₆₄ speWord i) ∗
        ((fsp + 0x4d8#64) ↦₆₄ w4d8) ∗
        ((fsp + 0x4e0#64) ↦₆₄ w4e0) ∗
        memRegion (fsp + 0x4e8#64) 24 ∗
        A.live spkSigPtr 64 1 ∗ (spkSigPtr ↦ₛ spkSig) ∗
        ownedBytes A.repAlloc kpkCap kpkPtr (BitVec.ofNat 64 kpkBs.length) kpkBs ∗
        ownedBytes A.repAlloc spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
        ownedBytes A.repAlloc regCap regPtr 4#64 [r0, r1, r2, r3] ∗
        r1b_invCoreBase_placed A.repAlloc g d s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
        r1b_opkStage1SpkAt fsp spkW0 spkW8 spkW16 spkW24
          b0 b1 b2 b3 b4 b5 b6 w0e0 w0e4 w9 w13 w15 w23 b31 ∗
        ((fsp + 0x110#64) ↦₆₄ spkSigPtr) ∗ ((fsp + 0x11c#64) ↦₃₂ v11c) ∗
        ((fsp + 0x120#64) ↦₆₄ 64#64) ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
        ((fsp + 0x130#64) ↦₆₄ v130) ∗ ((fsp + 0x138#64) ↦₆₄ v138) ∗
        ((fsp + 0x140#64) ↦₆₄ w4e0) ∗ ((fsp + 0x148#64) ↦₆₄ 64#64) ∗
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ ((fsp + 0x158#64) ↦₆₄ speWord i) ∗
        ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        ((fsp + 0x178#64) ↦₆₄ w4d8) ∗
        ((fsp + 0x188#64) ↦₆₄ v188_in) ∗ ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
        ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
        memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s)
      Q Qp oom := by
  intro fsp
  have hst := hc.st
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hst.spAligned
  have hal150 : (fsp + 0x150#64) &&& 7#64 = 0#64 := by bv_bits
  let _ := hal; let _ := hal150
  rw [r1b_split_region fsp 0x4e8 8 16, r1b_split_region fsp 0x4f0 8 8,
    ProofLib.memRegion_eight (fsp + 0x4e8#64),
    ProofLib.memRegion_eight (fsp + 0x4f0#64),
    ProofLib.memRegion_eight (fsp + 0x4f8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun w4f8 => SepWPp.exists_elim fun w4f0 =>
    SepWPp.exists_elim fun w4e8 => ?_
  have hsig_own :
      (A.live spkSigPtr 64 1 ∗ (spkSigPtr ↦ₛ spkSig)) ⊢
        ownedBytes A.repAlloc 64#64 spkSigPtr 64#64 spkSig :=
    r1b_sig64_to_ownedBytes A.repAlloc spkSigPtr spkSig hspk_ptr hspk_sig
  refine r1b_sepWPp_frame_de (by r1b_ac) hsig_own (by r1b_ac) ?_
  have hpc := hst.pc
  change s.pc = (blkPl_579).base + 0x2654#64 at hpc
  apply r1b_seq_lscro_oom (mid := lsρ lsRustDeallocSymCli) hst.inv
  have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
  dsimp only [runProgPlaced, lsProg_579]
  apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
    blkLib_eq_579 blk579_noSvc0 (mid := lsρ lsRustDeallocSymCli)
  intro _m_strip; have hpc_s : (s.setMem _m_strip).pc = (blkPl_579).base + 0x2654#64 := hpc
  wp_steps; clear hpc_s
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
    (by simp only [wp_norm, arm64_norm, *]) fun _m_real hnsp => ?_
  have hvmp : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
  try simp only [State.setMem_setMem] at hvmp ⊢
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  clear hpc hrun hsp
  refine r1b_bind_state_placed fun sm1 hsm1 hinv1 => ?_
  have hvm1 : VmPreserved s sm1 := hsm1 ▸ hvmp
  rw [← A.pool_transport lim st s sm1 hvm1]
  change SepWPp (runProgPlaced H) _ _ _ _ _ _
  refine r1b_call_frame_de <|
    r1b_call_dealloc_ownedBytes_placed (st := st) (cap := 64#64) (ptr := spkSigPtr) (len := 64#64)
      (bs := spkSig)
      hh hbnd hinv1
      (by simp [hsm1, arm64_norm])
      (by simp [hsm1, arm64_norm, hst.run])
      (by simpa [hsm1, arm64_norm] using hst.sp)
      (by simpa [hsm1, arm64_norm] using hst.fp)
      (by simpa [calleeSavedVRegs, hsm1, arm64_norm] using hst.vregs)
      hst.spAligned (retOff := 0x26a0)
      (by rw [runPcPlaced_eq]; simp [hsm1, arm64_norm])
      (by simp [hsm1, arm64_norm])
      (by simp [hsm1, arm64_norm])
      (by simp [hsm1, arm64_norm])
      (by decide) hpanic
      (fun sf1 hin1 hcs1 hfs1 htr1 => ?_)
  have hpc := hin1.pc
  change sf1.pc = (blkPl_579).base + 0x26a0#64 at hpc
  apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x2adc#64) hin1.inv
  have hrun := hin1.run; have hsp : sf1.sp = fsp := hin1.sp
  dsimp only [runProgPlaced, lsProg_579]
  apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
    blkLib_eq_579 blk579_noSvc0 (mid := (blkPl_579).base + 0x2adc#64)
  intro _m_strip; have hpc_s : (sf1.setMem _m_strip).pc = (blkPl_579).base + 0x26a0#64 := hpc
  wp_steps; clear hpc_s
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
    (by simp only [wp_norm, arm64_norm, *]) fun _m_real hnsp => ?_
  have hvmp : VmPreserved sf1 _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
  try simp only [State.setMem_setMem] at hvmp ⊢
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  clear hpc hrun hsp
  refine r1b_bind_state_placed fun sm2 hsm2 hinv2 => ?_
  have hvm2 : VmPreserved sf1 sm2 := hsm2 ▸ hvmp
  rw [← A.pool_transport lim (M.stepEvents (rustDeallocEvents (64#64).toNat 1) st) sf1 sm2 hvm2]
  change SepWPp (runProgPlaced H) _ _ _ _ _ _
  have htr_tot : sm2.trace = s.trace := by
    simp only [hsm2, arm64_norm]
    exact htr1.trans (by simp [hsm1, arm64_norm])
  have hfs_tot : sm2.fs.files = s.fs.files := by
    simp only [hsm2, arm64_norm]
    exact (congrArg FsState.files hfs1).trans (by simp [hsm1, arm64_norm])
  have hc2 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm2 0x2adc := hc.of_step
    { pc := by rw [runPcPlaced_eq]; simp [hsm2, arm64_norm]
      run := by simp [hsm2, arm64_norm, hin1.run]
      sp := by simpa [hsm2, arm64_norm] using hin1.sp
      fp := by simpa [hsm2, arm64_norm] using hin1.fp
      inv := hinv2
      vregs := by simpa [calleeSavedVRegs, hsm2, arm64_norm] using hin1.vregs
      spAligned := hst.spAligned }
    (by simpa [hsm2, arm64_norm] using hcs1.1.trans (by simp [hsm1, arm64_norm]))
    (by simpa [hsm2, arm64_norm] using hcs1.2.1.trans (by simp [hsm1, arm64_norm]))
    (by simpa [hsm2, arm64_norm] using hcs1.2.2.1.trans (by simp [hsm1, arm64_norm]))
    htr_tot hfs_tot
  have h4d0 :
      ((fsp + 0x4d0#64) ↦₆₄ speWord i) ∗ ((fsp + 0x4d8#64) ↦₆₄ w4d8) ∗
        ((fsp + 0x4e0#64) ↦₆₄ w4e0) ∗ ((fsp + 0x4e8#64) ↦₆₄ w4e8) ∗
        ((fsp + 0x4f0#64) ↦₆₄ w4f0) ∗ ((fsp + 0x4f8#64) ↦₆₄ w4f8) ⊢
        memRegion (fsp + 0x4d0#64) 48 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      r1b_cells6_to_region48 (fsp + 0x4d0#64) (speWord i) w4d8 w4e0 w4e8 w4f0 w4f8
  have h110 : ((fsp + 0x110#64) ↦₆₄ spkSigPtr) ⊢ memRegion (fsp + 0x110#64) 8 :=
    pointsTo64_entails_memRegion _ _
  have h11c : ((fsp + 0x11c#64) ↦₃₂ v11c) ⊢ memRegion (fsp + 0x11c#64) 4 :=
    pointsTo32_entails_memRegion _ _
  have h120 :
      ((fsp + 0x120#64) ↦₆₄ 64#64) ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ⊢
        memRegion (fsp + 0x120#64) 16 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      r1b_cells2_to_region16 (fsp + 0x120#64) 64#64 kpkPtr
  have h130 :
      ((fsp + 0x130#64) ↦₆₄ v130) ∗ ((fsp + 0x138#64) ↦₆₄ v138) ∗
        ((fsp + 0x140#64) ↦₆₄ w4e0) ∗ ((fsp + 0x148#64) ↦₆₄ 64#64) ⊢
        memRegion (fsp + 0x130#64) 0x20 := by
    refine Entails.trans (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (pointsTo64_entails_memRegion _ _)))) ?_
    rw [r1b_join_region fsp 0x140 8 8, r1b_join_region fsp 0x138 8 16,
      r1b_join_region fsp 0x130 8 24]
    exact Entails.refl _
  have h150 :
      ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ ((fsp + 0x158#64) ↦₆₄ speWord i) ⊢
        memRegion (fsp + 0x150#64) 16 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      r1b_cells2_to_region16 (fsp + 0x150#64) kpkCap (speWord i)
  have h178 : ((fsp + 0x178#64) ↦₆₄ w4d8) ⊢ memRegion (fsp + 0x178#64) 8 :=
    pointsTo64_entails_memRegion _ _
  have h1a8 :
      ((fsp + 0x1a8#64) ↦₆₄ w4f8) ∗
        ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
        memRegion (fsp + 0x1b4#64) 4 ⊢ memRegion (fsp + 0x1a8#64) 16 := by
    refine Entails.trans (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono_left (pointsTo32_entails_memRegion _ _))) ?_
    rw [r1b_join_region fsp 0x1b0 4 4, r1b_join_region fsp 0x1a8 8 8]
    exact Entails.refl _
  refine r1b_sepWPp_frame_de (by r1b_ac)
    (sepConj_mono
      (r1b_opkStage1Spk_to_regions fsp spkW0 spkW8 spkW16 spkW24
        b0 b1 b2 b3 b4 b5 b6 w0e0 w0e4 w9 w13 w15 w23 b31)
      (sepConj_mono h4d0 (sepConj_mono h110 (sepConj_mono h11c
        (sepConj_mono h120 (sepConj_mono h130 (sepConj_mono h150 (sepConj_mono h178 h1a8))))))))
    (by r1b_ac) ?_
  have hinv_rejoin :
      r1b_invCoreBase_placed A.repAlloc g d s0 ∗
        memRegion (fsp + 0x1d0#64) 0x90 ∗ memRegion (fsp + 0x2c0#64) 0x210 ⊢
      r1b_invCore_placed A.repAlloc g d s0 :=
    Entails.of_eq (r1b_invCore_split_mid_placed A.repAlloc g d s0).symm
  refine r1b_sepWPp_frame_de (by r1b_ac) hinv_rejoin (by r1b_ac) ?_
  have h164 : ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ⊢ memRegion (fsp + 0x164#64) 4 :=
    pointsTo32_entails_memRegion _ _
  have h190 : ((fsp + 0x190#64) ↦₆₄ d.ikW3) ⊢ memRegion (fsp + 0x190#64) 8 :=
    pointsTo64_entails_memRegion _ _
  refine r1b_sepWPp_frame_de (by r1b_ac) (sepConj_mono h164 h190) (by r1b_ac) ?_
  generalize herrCommon :
    r1b_errCommon (A.atState lim (M.stepEvents (rustDeallocEvents (64#64).toNat 1) st) sm2)
      g d s0 resStack = errCommon
  have herr_c :
      r1b_invCore_placed A.repAlloc g d s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
        memRegion fsp 0x110 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
        memRegion (fsp + 0x164#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗
        A.pool lim (M.stepEvents (rustDeallocEvents (64#64).toNat 1) st) sm2 ⊢ errCommon := by
    rw [← herrCommon]
    exact r1b_invCore_to_errCommon_placed
      (A.atState lim (M.stepEvents (rustDeallocEvents (64#64).toNat 1) st) sm2) g d s0 resStack
  refine r1b_sepWPp_frame_de (by r1b_ac) herr_c (by r1b_ac) ?_
  have hcl := r1b_spk_err_at_2adc_placed
    (st := M.stepEvents (rustDeallocEvents (64#64).toNat 1) st)
    (i := i) (v188 := w4e8)
    (kpkCap := kpkCap) (kpkPtr := kpkPtr) (kpkLen := BitVec.ofNat 64 kpkBs.length) (kpkBs := kpkBs)
    (spkCap := spkCap) (spkPtr := spkPtr) (spkLen := BitVec.ofNat 64 spkBs.length) (spkBs := spkBs)
    (regCap := regCap) (regPtr := regPtr) (regLen := 4#64) (regBs := [r0, r1, r2, r3])
    hh hdrop hbnd hc2 hi
    (by simp [hsm2, arm64_norm])
    (by simp [hsm2, arm64_norm])
    (by simp [hsm2, arm64_norm])
    hpanic fun sf_r evsFree hfo2 hrej_f => by
      rw [← M.stepEvents_append (rustDeallocEvents (64#64).toNat 1) evsFree st]
      exact hrej sf_r (rustDeallocEvents (64#64).toNat 1 ++ evsFree)
        (FreeOnlyEvs.append (FreeOnlyEvs.singleton 1 (64#64).toNat) hfo2) hrej_f
  dsimp only at hcl
  rw [herrCommon] at hcl
  exact sepWPp_weaken_pre (Entails.of_eq (by r1b_ac)) hcl

theorem r1b_kem_err_2654_placed_env [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {i : Nat}
    {spkW0 : BitVec 64} {spkW8 : BitVec 32} {spkW16 spkW24 : BitVec 64}
    {b0 b1 b2 b3 b4 b5 b6 : BitVec 8}
    {w0e0 w0e4 w9 : BitVec 32} {w13 : BitVec 16} {w15 w23 : BitVec 64} {b31 : BitVec 8}
    {r0 r1 r2 r3 : BitVec 8} {v11c : BitVec 32}
    {spkSigPtr kpkCap kpkPtr spkCap spkPtr regCap regPtr : BitVec 64}
    {v130 v138 w4d8 w4e0 v188_in : BitVec 64}
    {spkSig kpkBs spkBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2654)
    (hi : PlainSpeTag i)
    (hspk_ptr : spkSigPtr ≠ 0)
    (hspk_sig : spkSig.length = 64)
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectKPlacedEnv r1b_CodeOk H A lim EnvAt g s0 resStack Q Qp oom)
    (henv : ∀ evs, FreeOnlyEvs evs → EnvAt StoresGhost.opened .postDispatch (M.stepEvents evs st)) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (((fsp + 0x4d0#64) ↦₆₄ speWord i) ∗
        ((fsp + 0x4d8#64) ↦₆₄ w4d8) ∗
        ((fsp + 0x4e0#64) ↦₆₄ w4e0) ∗
        memRegion (fsp + 0x4e8#64) 24 ∗
        A.live spkSigPtr 64 1 ∗ (spkSigPtr ↦ₛ spkSig) ∗
        ownedBytes A.repAlloc kpkCap kpkPtr (BitVec.ofNat 64 kpkBs.length) kpkBs ∗
        ownedBytes A.repAlloc spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
        ownedBytes A.repAlloc regCap regPtr 4#64 [r0, r1, r2, r3] ∗
        r1b_invCoreBase_placed A.repAlloc g d s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
        r1b_opkStage1SpkAt fsp spkW0 spkW8 spkW16 spkW24
          b0 b1 b2 b3 b4 b5 b6 w0e0 w0e4 w9 w13 w15 w23 b31 ∗
        ((fsp + 0x110#64) ↦₆₄ spkSigPtr) ∗ ((fsp + 0x11c#64) ↦₃₂ v11c) ∗
        ((fsp + 0x120#64) ↦₆₄ 64#64) ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
        ((fsp + 0x130#64) ↦₆₄ v130) ∗ ((fsp + 0x138#64) ↦₆₄ v138) ∗
        ((fsp + 0x140#64) ↦₆₄ w4e0) ∗ ((fsp + 0x148#64) ↦₆₄ 64#64) ∗
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ ((fsp + 0x158#64) ↦₆₄ speWord i) ∗
        ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        ((fsp + 0x178#64) ↦₆₄ w4d8) ∗
        ((fsp + 0x188#64) ↦₆₄ v188_in) ∗ ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
        ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
        memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s)
      Q Qp oom :=
  r1b_kem_err_2654_placed hh hdrop hbnd hc hi hspk_ptr hspk_sig hpanic fun sf evs hfo hrej_f =>
    hrej sf (M.stepEvents evs st) StoresGhost.opened .postDispatch hrej_f (henv evs hfo)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.DeserCloneErrPlacedBudget
