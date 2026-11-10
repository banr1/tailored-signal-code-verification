/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadKpkPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadOpkPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadOpkSpinePlaced
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public meta import ProofLib -- shake: keep
public meta import Lean -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSites

/-!
# Budget-Threaded Stage 3 (`one-time-pre-key`) Spine of Arm `R1b` (`0x12dc → 0x24ec`)

Defines the Stage 3 allocation-event envelopes (`R1bStepOpkOkEnv`, `R1bStepOpkErrEnv`) and proves
`r1b_step_opk_placed` (`0x12dc → 0x24ec`) on Block `579` under `[LibsignalPlacement]` and
`RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadOpkSpinePlacedBudget

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (PublicKey)
open CryptoVerification (LibsignalHooks LibsignalPlacement lsLogFilterAddr lsmpl)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalTripleRatchet.Wire
  (deserializeResult33At exists_pkBytesOf pkBytesOf pkLayoutAt_eq_pointsToBytes)
open CryptoVerification.LibsignalTripleRatchetRepr (okTagVec speWord)
open CryptoVerification.SignalSession.Cli (StoresGhost ofLe32 splitId splitOkTag utf8)
open CryptoVerification.SignalSession.Cli.MainHops
  (RunCall blockingAncestorF cliIo cliRd ownedBytes readViewF sepWPp_weaken_pre)
open CryptoVerification.SignalSession.Cli.Run.Placed
  (blkLib_eq_579 blkPC_579 blkPl_579 lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (AtRejectPlaced AtRunEntryPlaced Init1Data PanicK RejectKind RunSem bundleNames r1b_CodeOk
   r1b_ErrCtxPlaced r1b_OkCtxPlaced r1b_StackBounds r1b_bind_state_placed r1b_cell64_cons
   r1b_cells2_to_region16 r1b_entails_frame_core r1b_errCommon r1b_fsp_align
   r1b_init_path_facts_placed r1b_invCore_placed r1b_invCoreBase_placed
   r1b_invCore_split_mid_placed r1b_invCore_to_errCommon_placed r1b_join_region
   r1b_none_opk_deser r1b_none_opk_rd r1b_none_opk_split r1b_opkStage1At r1b_opkStage1_of_regions
   r1b_ownedBytes_facts r1b_ownedBytes_rejoin r1b_ownedRest r1b_ro_opk_placed
   r1b_sepWPp_borrow_core r1b_sepWPp_frame_core r1b_splitId_bytes r1b_splitId_slice_eq
   r1b_split_region r1b_stage_to_err_placed rejectMem runFiles runFsp runPcPlaced
   runPcPlaced_eq runProgPlaced)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets RunSlots runFrame)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
   VmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpersParsePlacedBudget
  (r1b_call_pkDeserialize_pool_placed r1b_call_splitId_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpersPlacedBudget
  (r1b_call_bundleRead_ro_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadKpkPlacedBudgetAux
  (r1b_seq_lscro_oom)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadOpkPlacedBudget
  (r1b_err_1b98_placed r1b_err_2420_placed r1b_opk_copy1_2490_placed
   r1b_opk_deser_err_1360_placed r1b_opk_free_24dc_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpkPlacedBudgetAux
  (blk579_noSvc0)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget (RejectKPlacedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget
  (DropSpeOwnedOkAtBlock)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
  (RunCalleesEnvs RunCalleesPlaced RunHooksPlaced)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local simp, local arm64_norm, local wp_norm] runPcPlaced_eq BitVec.ofNat_eq_ofNat

local macro (priority := high) "r1b_ac" : tactic =>
  `(tactic| ((try dsimp +zetaDelta only) <;> first | rfl | simp only [emp_sepConj] | sep_ac_rfl))

private meta def r1bStripLetsOP : Nat → Lean.Expr → Lean.Expr
  | 0, e => e
  | n + 1, .letE _ _ v b _ => r1bStripLetsOP n (b.instantiate1 v)
  | n + 1, .mdata _ e => r1bStripLetsOP n e
  | _, e => e

private meta def r1bSplitSepOP : Nat → Lean.Expr → Lean.Expr → Array Lean.Expr
  | 0, _, e => #[e]
  | fuel + 1, sepSample, e =>
    let e := r1bStripLetsOP 64 e; let ar := sepSample.getAppNumArgs
    if e.isAppOfArity sepSample.getAppFn.constName! ar then
      r1bSplitSepOP fuel sepSample (e.getArg! (ar - 2)) ++ r1bSplitSepOP fuel sepSample (e.getArg! (ar - 1))
    else #[e]

private meta def r1bIsDefEqPureOP (x a : Lean.Expr) : Lean.Elab.TermElabM Bool := do
  let x := r1bStripLetsOP 64 x; let a := r1bStripLetsOP 64 a
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

private meta def r1bComputeRestOP (ctxName : String) (p a1 : Lean.Expr) : Lean.Elab.TermElabM Lean.Expr := do
  let sepTy := Lean.mkConst ``SepProp []
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let mut rem := (r1bSplitSepOP 64 sepSample (← Lean.instantiateMVars p)).toList
  for a in (r1bSplitSepOP 64 sepSample (← Lean.instantiateMVars a1)).toList do
    let mut removed := false; let mut next : List Lean.Expr := []
    for x in rem do
      if !removed && (← r1bIsDefEqPureOP x a) then removed := true else next := next.concat x
    if !removed then throwError "{ctxName}: unmatched atom:\n  {a}\nin:\n  {rem}"
    rem := next
  let ar := sepSample.getAppNumArgs
  let mkSep (l r : Lean.Expr) := sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (ar - 2) ++ #[l, r])
  match rem.reverse with | [] => return empExpr | last :: rest => return rest.foldl (fun acc x => mkSep x acc) last

local elab (priority := high) "r1b_entails_frame_op " t1:term:arg h:term:arg t2:term:arg : term <= expectedType => do
  let exp ← Lean.instantiateMVars expectedType; if exp.isMVar then Lean.Elab.Term.tryPostpone
  let ear := (← Lean.Elab.Term.elabTerm (← `(emp ⊢ emp)) none).getAppNumArgs
  let expS := r1bStripLetsOP 64 exp; let p := expS.getArg! (ear - 2); let q := expS.getArg! (ear - 1)
  if (← Lean.instantiateMVars p).isMVar || (← Lean.instantiateMVars q).isMVar then Lean.Elab.Term.tryPostpone
  let hExpr ← Lean.Elab.Term.elabTerm h none
  let hTy := r1bStripLetsOP 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
  let a1 := hTy.getArg! (ear - 2); let a2 := hTy.getArg! (ear - 1)
  let r ← r1bComputeRestOP "r1b_entails_frame" p a1; let sepTy := Lean.mkConst ``SepProp []
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy); let sar := sepSample.getAppNumArgs
  let mkSep (x y : Lean.Expr) := sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
  if (← r1bIsDefEqPureOP r empExpr) then
    let h1Expr ← Lean.Elab.Term.elabTerm t1 (some (← Lean.Meta.mkEq p a1))
    let h2Expr ← Lean.Elab.Term.elabTerm t2 (some (← Lean.Meta.mkEq a2 q))
    Lean.Meta.mkAppM ``Entails.trans #[← Lean.Meta.mkAppM ``Entails.of_eq #[h1Expr],
      ← Lean.Meta.mkAppM ``Entails.trans #[hExpr, ← Lean.Meta.mkAppM ``Entails.of_eq #[h2Expr]]]
  else
    let h1Expr ← Lean.Elab.Term.elabTerm t1 (some (← Lean.Meta.mkEq p (mkSep a1 r)))
    let h2Expr ← Lean.Elab.Term.elabTerm t2 (some (← Lean.Meta.mkEq (mkSep a2 r) q))
    Lean.Meta.mkAppOptM ``r1b_entails_frame_core #[some a1, some a2, some r, some p, some q, h1Expr, hExpr, h2Expr]

local elab (priority := high) "r1b_sepWPp_frame_op " t1:term:arg h:term:arg t2:term:arg hk:term:arg : term <= expectedType => do
  let exp ← Lean.instantiateMVars expectedType; if exp.isMVar then Lean.Elab.Term.tryPostpone
  let expS := r1bStripLetsOP 64 exp; let args := expS.getAppArgs
  let prog := args[0]!; let ret := args[1]!; let st := args[2]!; let p := args[3]!
  let q := args[4]!; let qp := args[5]!; let oom := args[6]!
  let ear := (← Lean.Elab.Term.elabTerm (← `(emp ⊢ emp)) none).getAppNumArgs
  let hExpr ← Lean.Elab.Term.elabTerm h none
  let hTy := r1bStripLetsOP 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
  let a1 := hTy.getArg! (ear - 2); let a2 := hTy.getArg! (ear - 1)
  let r ← r1bComputeRestOP "r1b_sepWPp_frame" p a1; let sepTy := Lean.mkConst ``SepProp []
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy); let sar := sepSample.getAppNumArgs
  let mkSep (x y : Lean.Expr) := sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
  if (← r1bIsDefEqPureOP r empExpr) then
    let h1Expr ← Lean.Elab.Term.elabTerm t1 (some (← Lean.Meta.mkEq p a1))
    let h2Expr ← Lean.Elab.Term.elabTerm t2 (some (← Lean.Meta.mkEq a2 a2))
    let hkExpr ← Lean.Elab.Term.elabTerm hk (some (Lean.mkAppN expS.getAppFn #[prog, ret, st, a2, q, qp, oom]))
    let hent ← Lean.Meta.mkAppM ``Entails.trans #[← Lean.Meta.mkAppM ``Entails.of_eq #[h1Expr],
      ← Lean.Meta.mkAppM ``Entails.trans #[hExpr, ← Lean.Meta.mkAppM ``Entails.of_eq #[h2Expr]]]
    Lean.Meta.mkAppM ``sepWPp_weaken_pre #[hent, hkExpr]
  else
    let p' := if (← r1bIsDefEqPureOP a2 empExpr) then r else mkSep a2 r
    let h1Expr ← Lean.Elab.Term.elabTerm t1 (some (← Lean.Meta.mkEq p (mkSep a1 r)))
    let h2Expr ← Lean.Elab.Term.elabTerm t2 (some (← Lean.Meta.mkEq (mkSep a2 r) p'))
    let hkExpr ← Lean.Elab.Term.elabTerm hk (some (Lean.mkAppN expS.getAppFn #[prog, ret, st, p', q, qp, oom]))
    Lean.Meta.mkAppOptM ``r1b_sepWPp_frame_core
      #[some prog, some ret, some st, some a1, some a2, some r, some p, some p', some q, some qp, some oom,
        h1Expr, hExpr, h2Expr, hkExpr]

local elab:10 (priority := high) "r1b_call_frame_op" "<|" h:term:10 : term <= expectedType => do
  let exp ← Lean.instantiateMVars expectedType; if exp.isMVar then Lean.Elab.Term.tryPostpone
  let expS := r1bStripLetsOP 64 exp; let hExpr ← Lean.Elab.Term.elabTerm h none
  let hTy0 := r1bStripLetsOP 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
  for idx in [0, 1, 2, 4, 5, 6] do
    if !(← Lean.Meta.withReducibleAndInstances <| Lean.Meta.isDefEq (hTy0.getArg! idx) (expS.getArg! idx)) then
      discard <| Lean.Meta.isDefEq (hTy0.getArg! idx) (expS.getArg! idx)
  let p ← Lean.instantiateMVars (expS.getArg! 3)
  let p' ← Lean.instantiateMVars ((r1bStripLetsOP 64 (← Lean.instantiateMVars hTy0)).getArg! 3)
  let sepTy := Lean.mkConst ``SepProp []; let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy); let sar := sepSample.getAppNumArgs
  let mkSep (x y : Lean.Expr) := sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
  let mut mvarFOpt : Option Lean.Expr := none; let mut a1s : List Lean.Expr := []
  for a in (r1bSplitSepOP 64 sepSample p').toList do
    let ai ← Lean.instantiateMVars a
    if mvarFOpt.isNone && ai.isMVar then mvarFOpt := some ai else a1s := a1s.concat ai
  let mut rem := (r1bSplitSepOP 64 sepSample p).toList
  for a in a1s do
    let mut removed := false; let mut next : List Lean.Expr := []
    for x in rem do
      if !removed && (← r1bIsDefEqPureOP x a) then removed := true else next := next.concat x
    if !removed then throwError "r1b_call_frame: unmatched callee atom:\n  {a}\nin:\n  {rem}"
    rem := next
  let remProd := match rem.reverse with | [] => empExpr | last :: rest => rest.foldl (fun acc x => mkSep x acc) last
  if let some mf := mvarFOpt then discard <| Lean.Meta.withReducibleAndInstances <| Lean.Meta.isDefEq mf remProd
  let eqProof ← Lean.Elab.Term.elabTerm (← `(by r1b_ac)) (some (← Lean.Meta.mkEq (← Lean.instantiateMVars p) (← Lean.instantiateMVars p')))
  Lean.Meta.mkAppM ``sepWPp_weaken_pre #[← Lean.Meta.mkAppM ``Entails.of_eq #[eqProof], hExpr]

private theorem r1b_utf8_opk_len_placed : (utf8 "one-time-pre-key").length = 16 := by
  simp only [utf8, List.length_map, String.toUTF8_eq_toByteArray]; decide +kernel

private theorem r1b_h130_region (fsp v1 v2 v3 v4 : BitVec 64) :
    ((fsp + 0x130#64) ↦₆₄ v1) ∗ ((fsp + 0x138#64) ↦₆₄ v2) ∗ ((fsp + 0x140#64) ↦₆₄ v3) ∗
      ((fsp + 0x148#64) ↦₆₄ v4) ⊢ memRegion (fsp + 0x130#64) 0x20 := by
  refine Entails.trans (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)))) ?_
  rw [r1b_join_region fsp 0x140 8 8, r1b_join_region fsp 0x138 8 16, r1b_join_region fsp 0x130 8 24]
  exact Entails.refl _

private theorem r1b_h4d0_vec_region (fsp v0 v1 v2 v3 : BitVec 64) :
    ((fsp + 0x4d0#64) ↦₆₄ v0) ∗ ((fsp + 0x4d8#64) ↦₆₄ v1) ∗ ((fsp + 0x4e0#64) ↦₆₄ v2) ∗
      ((fsp + 0x4e8#64) ↦₆₄ v3) ∗ memRegion (fsp + 0x4f0#64) 16 ⊢ memRegion (fsp + 0x4d0#64) 48 := by
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using r1b_cell64_cons (a := fsp + 0x4e8#64) v3 (n := 16) (by decide))))) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using r1b_cell64_cons (a := fsp + 0x4e0#64) v2 (n := 24) (by decide)))) ?_
  refine Entails.trans (sepConj_mono_right (by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using r1b_cell64_cons (a := fsp + 0x4d8#64) v1 (n := 32) (by decide))) ?_
  simpa only [BitVec.add_assoc, BitVec.reduceAdd] using r1b_cell64_cons (a := fsp + 0x4d0#64) v0 (n := 40) (by decide)

/-- Success-path allocation-event envelope of `r1b_step_opk_placed`: `bundleRead` for `"one-time-pre-key"`, optional `split_id` when `opkBs` is non-empty, and `FreeOnlyEvs` deallocation of `opkBs`. -/
def R1bStepOpkOkEnv (cEnvs : RunCalleesEnvs) (files : FsFiles)
    (dir opkBs : List (BitVec 8)) : List AllocEvent → Prop :=
  if opkBs.isEmpty then
    SeqEnv (cEnvs.bundleRead files dir (utf8 "one-time-pre-key")) FreeOnlyEvs
  else
    SeqEnv (SeqEnv (cEnvs.bundleRead files dir (utf8 "one-time-pre-key")) (cEnvs.splitId opkBs))
      FreeOnlyEvs

example (files : FsFiles) :
    R1bStepOpkOkEnv
      ⟨fun _ _ e => e = [], fun _ _ _ e => e = [], fun _ _ _ e => e = [],
       fun _ e => e = [], fun _ e => e = []⟩
      files [] [] [] :=
  Or.inl rfl

/-- Error-path allocation-event envelope of `r1b_step_opk_placed`: `bundleRead` failure followed by `FreeOnlyEvs`, or non-empty `bundleRead` followed by `splitId` or `<PublicKey>::deserialize` failure and `FreeOnlyEvs`. -/
def R1bStepOpkErrEnv (cEnvs : RunCalleesEnvs) (files : FsFiles)
    (dir : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  match cliIo.rd files (dir ++ [0x2f#8] ++ utf8 "one-time-pre-key") with
  | .error () => SeqEnv (cEnvs.bundleRead files dir (utf8 "one-time-pre-key")) FreeOnlyEvs evs
  | .ok [] => False
  | .ok (b :: bs) =>
      match splitId (b :: bs) with
      | none =>
          SeqEnv (SeqEnv (cEnvs.bundleRead files dir (utf8 "one-time-pre-key"))
            (cEnvs.splitId (b :: bs))) FreeOnlyEvs evs
      | some (_, opkKey) =>
          match PublicKey.deserialize opkKey with
          | .error _ =>
              SeqEnv (SeqEnv (cEnvs.bundleRead files dir (utf8 "one-time-pre-key"))
                (cEnvs.splitId (b :: bs))) FreeOnlyEvs evs
          | .ok _ => False

example :
    R1bStepOpkErrEnv
      ⟨fun _ _ e => e = [], fun _ _ _ e => e = [], fun _ _ _ e => e = [],
       fun _ e => e = [], fun _ e => e = []⟩
      (fun _ => some .dir) [] [] := by
  unfold R1bStepOpkErrEnv
  have hrd :
      cliIo.rd ((fun _ => some .dir) : FsFiles) ([] ++ [0x2f#8] ++ utf8 "one-time-pre-key") =
        .error () := by
    unfold cliIo cliRd readViewF blockingAncestorF
    dsimp only
    generalize List.find? _ _ = o
    cases o <;> rfl
  rw [hrd]
  exact Or.inl rfl

theorem r1b_step_opk_placed [LibsignalPlacement] {M : AllocCostModel}
    {S : RunSem} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {cEnvs : RunCalleesEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {σ : RunSlots}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {r0 r1 r2 r3 : BitVec 8}
    {kpkCap kpkPtr spkCap spkPtr regCap regPtr : BitVec 64}
    {kpkBs kpkKey spkBs spkKey : List (BitVec 8)}
    {kpkId spkId : BitVec 32}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hc : RunCalleesPlaced A lim cEnvs H B σ)
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (he : AtRunEntryPlaced r1b_CodeOk S g s0)
    (hok : r1b_OkCtxPlaced r1b_CodeOk S g d s0 s 0x12dc)
    (hx25 : s.readReg64 (.gpr 25#5) = d.dirPtr)
    (hx28 : s.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length)
    (hx26 : s.readReg64 (.gpr 26#5) = kpkPtr)
    (hx27 : s.readReg64 (.gpr 27#5) = BitVec.ofNat 64 spkKey.length)
    (hx9 : s.readReg64 (.gpr 9#5) = BitVec.ofNat 64 kpkKey.length)
    (hx10 : s.readReg64 (.gpr 10#5) = kpkPtr + 4#64)
    (hx8 : s.readReg64 (.gpr 8#5) = kpkPtr + 4#64 + BitVec.ofNat 64 kpkKey.length)
    (hx23 : s.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64)
    (hx24 : s.readReg64 (.gpr 24#5) = 64#64)
    (hfit_br : FitsEnv M lim st (cEnvs.bundleRead (runFiles g.i) d.dir (utf8 "one-time-pre-key")))
    (hfit_sp : ∀ (evs_br : List AllocEvent) (opkBs : List (BitVec 8)),
      opkBs ≠ [] →
      cEnvs.bundleRead (runFiles g.i) d.dir (utf8 "one-time-pre-key") evs_br →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "one-time-pre-key") = .ok opkBs →
      FitsEnv M lim (M.stepEvents evs_br st) (cEnvs.splitId opkBs))
    (hpanic : PanicK g s0 Qp)
    (hrej : ∀ (sf : State) (evs : List AllocEvent),
      R1bStepOpkErrEnv cEnvs (runFiles g.i) d.dir evs →
      AtRejectPlaced r1b_CodeOk g StoresGhost.opened .postDispatch s0 sf →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (rejectMem (A.atState lim (M.stepEvents evs st) sf)
          g StoresGhost.opened .postDispatch s0 resStack)
        Q Qp oom)
    (hk : ∀ (sf : State) (evs_opk : List AllocEvent) (opkBs : List (BitVec 8))
        (opk : Option (BitVec 32 × PublicKey))
        (v11c : BitVec 32)
        (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
        (w0e0 w0e4 w9 : BitVec 32) (w13 : BitVec 16) (w15 w23 : BitVec 64) (b31 : BitVec 8),
      R1bStepOpkOkEnv cEnvs (runFiles g.i) d.dir opkBs evs_opk →
      r1b_OkCtxPlaced r1b_CodeOk S g d s0 sf 0x24ec →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "one-time-pre-key") = .ok opkBs →
      ((opkBs = [] ∧ opk = none) ∨
        (∃ opkId opkKey opkPk, opkBs ≠ [] ∧ opkBs.length < 2 ^ 63 ∧
          splitId opkBs = some (opkId, opkKey) ∧
          PublicKey.deserialize opkKey = .ok opkPk ∧ opk = some (opkId, opkPk) ∧
          v11c = opkId ∧
          opkPk.bytes.toList = pkBytesOf b0 b1 b2 b3 b4 b5 b6
            (w0e4.truncate 8) (w0e0.truncate 8) w9 w13 w15 w23 b31)) →
      sf.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64 →
      sf.readReg64 (.gpr 24#5) = runFsp s0 + 0x380#64 →
      sf.readReg64 (.gpr 25#5) = BitVec.ofNat 64 opkBs.length →
      sf.readReg64 (.gpr 27#5) = BitVec.ofNat 64 spkKey.length →
      sf.readReg64 (.gpr 28#5) = 64#64 →
      let fsp := runFsp s0
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (memRegion (fsp + 0x4d0#64) 48 ∗
          ownedBytes A.repAlloc kpkCap kpkPtr (BitVec.ofNat 64 kpkBs.length) kpkBs ∗
          ownedBytes A.repAlloc spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
          ownedBytes A.repAlloc regCap regPtr 4#64 [r0, r1, r2, r3] ∗
          r1b_invCoreBase_placed A.repAlloc g d s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
          ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
          r1b_opkStage1At fsp b0 b1 b2 b3 b4 b5 b6 w0e0 w0e4 w9 w13 w15 w23 b31 ∗
          memRegion (fsp + 0x110#64) 8 ∗ ((fsp + 0x11c#64) ↦₃₂ v11c) ∗
          memRegion (fsp + 0x120#64) 8 ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
          ((fsp + 0x130#64) ↦₆₄ (kpkPtr + 4#64 + BitVec.ofNat 64 kpkKey.length)) ∗
          ((fsp + 0x138#64) ↦₆₄ BitVec.ofNat 64 kpkKey.length) ∗
          ((fsp + 0x140#64) ↦₆₄ (kpkPtr + 4#64)) ∗
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
          stackAt fsp (resStack - runFrame) ∗ A.pool lim (M.stepEvents evs_opk st) sf)
        Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
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
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s)
      Q Qp oom := by
  intro fsp
  let _ := hx25; let _ := hx28; let _ := hx26; let _ := hx27
  let _ := hx9; let _ := hx10; let _ := hx8; let _ := hx23; let _ := hx24
  generalize hinvCore : r1b_invCore_placed A.repAlloc g d s0 = invCore
  have hst := hok.st
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hst.spAligned
  have hal11c : (fsp + 0x11c#64) &&& 3#64 = 0#64 := by bv_bits
  have hal128 : (fsp + 0x128#64) &&& 7#64 = 0#64 := by bv_bits
  have hal138 : (fsp + 0x138#64) &&& 7#64 = 0#64 := by bv_bits
  have hal148 : (fsp + 0x148#64) &&& 7#64 = 0#64 := by bv_bits
  have hal158 : (fsp + 0x158#64) &&& 7#64 = 0#64 := by bv_bits
  have hal168 : (fsp + 0x168#64) &&& 7#64 = 0#64 := by bv_bits
  have hal178 : (fsp + 0x178#64) &&& 7#64 = 0#64 := by bv_bits
  have hal188 : (fsp + 0x188#64) &&& 7#64 = 0#64 := by bv_bits
  have hal4d8_8 : (fsp + 0x4d8#64) &&& 7#64 = 0#64 := by bv_bits
  have hal4d8_4 : (fsp + 0x4d8#64) &&& 3#64 = 0#64 := by bv_bits
  have hal4dc : (fsp + 0x4dc#64) &&& 3#64 = 0#64 := by bv_bits
  have hal4e8 : (fsp + 0x4e8#64) &&& 7#64 = 0#64 := by bv_bits
  have hal4f8 : (fsp + 0x4f8#64) &&& 7#64 = 0#64 := by bv_bits
  have hal198 : (fsp + 0x198#64) &&& 7#64 = 0#64 := by bv_bits
  have hal1a8 : (fsp + 0x1a8#64) &&& 7#64 = 0#64 := by bv_bits
  have hal164 : (fsp + 0x164#64) &&& 3#64 = 0#64 := by bv_bits
  have hal1b4 : (fsp + 0x1b4#64) &&& 3#64 = 0#64 := by bv_bits
  have ⟨hdir32, hpaths⟩ := r1b_init_path_facts_placed he hok.callEq
  have ⟨hopk_ok, _⟩ := hpaths "one-time-pre-key" (by simp [bundleNames])
  have hdir_nat : (BitVec.ofNat 64 d.dir.length).toNat = d.dir.length := by
    simp only [BitVec.toNat_ofNat]; omega
  rw [r1b_split_region fsp 0x130 8 16, r1b_split_region fsp 0x138 8 8,
    ProofLib.memRegion_eight (fsp + 0x130#64), ProofLib.memRegion_eight (fsp + 0x138#64),
    ProofLib.memRegion_eight (fsp + 0x140#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun v130 => SepWPp.exists_elim fun v138 =>
    SepWPp.exists_elim fun v140 => ?_
  try simp only [BitVec.add_assoc]; try simp only [BitVec.reduceAdd]; try simp only [sepConj_assoc]
  try rw [← BitVec.add_assoc kpkPtr 4#64]; try rw [← BitVec.add_assoc spkPtr 4#64]
  have hpc := hst.pc; change s.pc = (blkPl_579).base + 0x12dc#64 at hpc
  have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
  apply r1b_seq_lscro_oom (mid := lsmpl.base 563) hst.inv
  dsimp only [runProgPlaced, lsProg_579]
  apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
    blkLib_eq_579 blk579_noSvc0 (mid := lsmpl.base 563)
  intro _m_strip; have hpc_s : (s.setMem _m_strip).pc = (blkPl_579).base + 0x12dc#64 := hpc
  wp_steps; clear hpc_s
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
    (by simp only [wp_norm, arm64_norm, *]) fun _m_real hnsp => ?_
  have hvmp : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
  try simp only [State.setMem_setMem] at hvmp ⊢
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  refine r1b_bind_state_placed fun sm1 hsm1 hinv1 => by
    have hvm1 : VmPreserved s sm1 := hsm1 ▸ hvmp
    rw [← A.pool_transport lim st s sm1 hvm1]; clear hpc hrun hsp
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hfiles_sm1 : sm1.fs.files = runFiles g.i := by
      rw [show sm1.fs.files = s.fs.files by simp only [hsm1, wp_norm, arm64_norm]]; exact hok.fs
    refine r1b_call_frame_op <|
      r1b_call_bundleRead_ro_placed (g := g) (ret := fsp + 0x4d0#64)
        (dirCap := d.dirCap) (dirPtr := d.dirPtr) (dir := d.dir) hh hc hbnd hinv1 r1b_ro_opk_placed
        (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm, hst.run])
        (by simpa [hsm1, arm64_norm] using hst.sp) (by simpa [hsm1, arm64_norm] using hst.fp)
        (by simpa [calleeSavedVRegs, hsm1, arm64_norm] using hst.vregs)
        hst.spAligned (retOff := 0x1300) (by rw [runPcPlaced_eq]; simp [hsm1, arm64_norm])
        (by solve | simp [hsm1, arm64_norm] | simpa [hsm1, arm64_norm] using congrArg (· + 0x4d0#64) hst.sp)
        (by solve | simp [hsm1, arm64_norm] | simpa [hsm1, arm64_norm] using hx25)
        (by solve | (simp only [hsm1, arm64_norm]; exact hdir_nat) | (simp only [hsm1, arm64_norm, hx28]; exact hdir_nat))
        (by simp only [hsm1, arm64_norm]; rfl) (by simp [hsm1, arm64_norm, r1b_utf8_opk_len_placed])
        hdir32 (by rw [r1b_utf8_opk_len_placed]; decide) hopk_ok
        (by rw [hfiles_sm1]; exact hfit_br) hpanic
        (fun sf1 evsBr eCap ePtr eBs hevsBr hin1 hcs1 hout1 => ?_)
        (fun sf1 evsBr opkCap opkPtr opkBs hevsBr hin1 hcs1 hopk_rd_sf hfs1 htr1 => ?_)
    · have hevsBr' : cEnvs.bundleRead (runFiles g.i) d.dir (utf8 "one-time-pre-key") evsBr := hfiles_sm1 ▸ hevsBr
      have hrd_err : cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "one-time-pre-key") = .error () :=
        hfiles_sm1 ▸ hout1.1
      have hc1 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sf1 0x1300 := hok.after_readErr
        (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
        (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
        hin1 hcs1 hout1 r1b_none_opk_rd
      have hx26_1 : sf1.readReg64 (.gpr 26#5) = kpkPtr :=
        hcs1.2.2.2.2.2.2.2.1.trans (by solve | simp [hsm1, arm64_norm] | simpa [hsm1, arm64_norm] using hx26)
      try simp only [BitVec.add_assoc]; try simp only [BitVec.reduceAdd]; try simp only [sepConj_assoc]
      try rw [← BitVec.add_assoc kpkPtr 4#64]; try rw [← BitVec.add_assoc spkPtr 4#64]
      dsimp only [speWord]
      have hpc := hin1.pc; change sf1.pc = (blkPl_579).base + 0x1300#64 at hpc
      have hrun := hin1.run; have hsp : sf1.sp = fsp := hin1.sp
      apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x1b98#64) hin1.inv
      dsimp only [runProgPlaced, lsProg_579]
      apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
        blkLib_eq_579 blk579_noSvc0 (mid := (blkPl_579).base + 0x1b98#64)
      intro _m_strip; have hpc_s : (sf1.setMem _m_strip).pc = (blkPl_579).base + 0x1300#64 := hpc
      wp_steps; clear hpc_s
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *]) fun _m_real hnsp => ?_
      have hvmp : VmPreserved sf1 _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
      try simp only [State.setMem_setMem] at hvmp ⊢
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine r1b_bind_state_placed fun sm2 hsm2 hinv2 => by
        have hvm2 : VmPreserved sf1 sm2 := hsm2 ▸ hvmp
        rw [← A.pool_transport lim (M.stepEvents evsBr st) sf1 sm2 hvm2]
        change SepWPp (runProgPlaced H) _ _ _ _ _ _
        have hc2 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm2 0x1b98 := hc1.of_step
          { pc := by rw [runPcPlaced_eq]; simp [hsm2, arm64_norm]
            run := by simp [hsm2, arm64_norm, hin1.run]
            sp := by simpa [hsm2, arm64_norm] using hin1.sp
            fp := by simpa [hsm2, arm64_norm] using hin1.fp
            inv := hinv2, spAligned := hst.spAligned
            vregs := by simpa [calleeSavedVRegs, hsm2, arm64_norm] using hin1.vregs }
          (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
          (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
        try rw [hx8]; try rw [hx9]; try rw [hx10]
        have h130_m := r1b_h130_region fsp (kpkPtr + 4#64 + BitVec.ofNat 64 kpkKey.length)
          (BitVec.ofNat 64 kpkKey.length) (kpkPtr + 4#64) 64#64
        have h178 : ((fsp + 0x178#64) ↦₆₄ (spkPtr + 4#64)) ⊢ memRegion (fsp + 0x178#64) 8 :=
          pointsTo64_entails_memRegion _ _
        refine r1b_sepWPp_frame_op (by r1b_ac) (sepConj_mono h130_m h178) (by r1b_ac) ?_
        generalize herrCommon :
          r1b_errCommon (A.atState lim (M.stepEvents evsBr st) sm2) g d s0 resStack = errCommon
        have hst_err :
            invCore ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
              ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
              memRegion fsp 0x110 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
              ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
              ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗ ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
              ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
              memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
              stackAt fsp (resStack - runFrame) ∗
              A.pool lim (M.stepEvents evsBr st) sm2 ⊢
              errCommon ∗ memRegion (fsp + 0x190#64) 8 ∗ memRegion (fsp + 0x1a8#64) 16 := by
          rw [← hinvCore, ← herrCommon]
          exact r1b_stage_to_err_placed (A.atState lim (M.stepEvents evsBr st) sm2)
            g d s0 resStack (ofLe32 r0 r1 r2 r3)
        have hcl := r1b_err_1b98_placed (st := M.stepEvents evsBr st)
          (v158 := spkPtr + 4#64 + BitVec.ofNat 64 spkKey.length) (v188_in := spkId.zeroExtend 64)
          (eCap := eCap) (ePtr := ePtr) (eBs := eBs)
          (kpkCap := kpkCap) (kpkPtr := kpkPtr) (kpkBs := kpkBs)
          (spkCap := spkCap) (spkPtr := spkPtr) (spkBs := spkBs)
          (regCap := regCap) (regPtr := regPtr) (regBs := [r0, r1, r2, r3])
          hh hdrop hbnd hc2 (by simp [hsm2, arm64_norm, speWord]) (by simp [hsm2, arm64_norm])
          (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
          (by solve | simp [hsm2, arm64_norm] | simpa [hsm2, arm64_norm] using hx26_1)
          hpanic fun sf_r evsFree hfo hrej_f => by
            rw [← M.stepEvents_append evsBr evsFree st]
            exact hrej sf_r (evsBr ++ evsFree) (by
              unfold R1bStepOpkErrEnv; rw [hrd_err]; exact SeqEnv.append hevsBr' hfo) hrej_f
        dsimp only at hcl; rw [herrCommon] at hcl
        refine sepWPp_weaken_pre ?_ hcl
        exact r1b_entails_frame_op (by r1b_ac) hst_err (by r1b_ac)
    ·
      have hevsBr' : cEnvs.bundleRead (runFiles g.i) d.dir (utf8 "one-time-pre-key") evsBr :=
        hfiles_sm1 ▸ hevsBr
      have hok1 : r1b_OkCtxPlaced r1b_CodeOk S g d s0 sf1 0x1300 := hok.after_call
        (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
        (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
        (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
        hin1 hcs1 hfs1 htr1
      have hopk_rd : cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "one-time-pre-key") =
          .ok opkBs := hfiles_sm1 ▸ hopk_rd_sf
      have hx23_1 : sf1.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64 :=
        hcs1.2.2.2.2.1.trans (by solve | simp [hsm1, arm64_norm] | simpa [hsm1, arm64_norm] using hx23)
      have hx24_1 : sf1.readReg64 (.gpr 24#5) = 64#64 :=
        hcs1.2.2.2.2.2.1.trans (by solve | simp [hsm1, arm64_norm] | simpa [hsm1, arm64_norm] using hx24)
      have hx26_1 : sf1.readReg64 (.gpr 26#5) = kpkPtr :=
        hcs1.2.2.2.2.2.2.2.1.trans (by solve | simp [hsm1, arm64_norm] | simpa [hsm1, arm64_norm] using hx26)
      have hx27_1 : sf1.readReg64 (.gpr 27#5) = BitVec.ofNat 64 spkKey.length :=
        hcs1.2.2.2.2.2.2.2.2.1.trans (by solve | simp [hsm1, arm64_norm] | simpa [hsm1, arm64_norm] using hx27)
      try rw [hx8]; try rw [hx9]; try rw [hx10]
      refine r1b_sepWPp_frame_op (by r1b_ac)
        (r1b_ownedBytes_facts A.repAlloc opkCap opkPtr (BitVec.ofNat 64 opkBs.length) opkBs)
        (by r1b_ac) ?_
      try simp only [sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨_, hopk_cap63, hopk_len63, hopk_ne⟩ => ?_
      refine r1b_sepWPp_frame_op (by r1b_ac) (Entails.of_eq (ProofLib.memRegion_eight (fsp + 0x110#64))) (by r1b_ac) ?_
      simp only [sepExists_sepConj_left, sepConj_assoc]
      refine SepWPp.exists_elim fun v110_in => ?_
      refine r1b_sepWPp_frame_op (by r1b_ac) (Entails.of_eq (ProofLib.memRegion_four (fsp + 0x11c#64))) (by r1b_ac) ?_
      simp only [sepExists_sepConj_left, sepConj_assoc]
      refine SepWPp.exists_elim fun v11c_in => ?_
      have hsplit120 : memRegion (fsp + 0x120#64) 16 =
          memRegion (fsp + 0x120#64) 8 ∗ memRegion (fsp + 0x128#64) 8 := by
        simpa only [Nat.reduceAdd, BitVec.ofNat_eq_ofNat] using r1b_split_region fsp 0x120 8 8
      rw [hsplit120]
      refine r1b_sepWPp_frame_op (by r1b_ac) (Entails.of_eq (ProofLib.memRegion_eight (fsp + 0x120#64))) (by r1b_ac) ?_
      simp only [sepExists_sepConj_left, sepConj_assoc]
      refine SepWPp.exists_elim fun v120_in => ?_
      refine r1b_sepWPp_frame_op (by r1b_ac) (Entails.of_eq (ProofLib.memRegion_eight (fsp + 0x128#64))) (by r1b_ac) ?_
      simp only [sepExists_sepConj_left, sepConj_assoc]
      refine SepWPp.exists_elim fun v128_in => ?_
      try simp only [BitVec.add_assoc]; try simp only [BitVec.reduceAdd]; try simp only [sepConj_assoc]
      try rw [← BitVec.add_assoc kpkPtr 4#64]; try rw [← BitVec.add_assoc spkPtr 4#64]
      dsimp only [okTagVec]
      by_cases hopk_nil : opkBs = []
      ·
        subst hopk_nil
        simp only [List.length_nil, BitVec.ofNat_eq_ofNat]
        have hpc := hin1.pc; change sf1.pc = (blkPl_579).base + 0x1300#64 at hpc
        have hrun := hin1.run; have hsp : sf1.sp = fsp := hin1.sp
        apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x24dc#64) hin1.inv
        dsimp only [runProgPlaced, lsProg_579]
        apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
          blkLib_eq_579 blk579_noSvc0 (mid := (blkPl_579).base + 0x24dc#64)
        intro _m_strip; have hpc_s : (sf1.setMem _m_strip).pc = (blkPl_579).base + 0x1300#64 := hpc
        wp_steps; clear hpc_s
        refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
          (by simp only [wp_norm, arm64_norm, *]) fun _m_real hnsp => ?_
        have hvmp : VmPreserved sf1 _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
        try simp only [State.setMem_setMem] at hvmp ⊢
        apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        refine r1b_bind_state_placed fun sm2 hsm2 hinv2 => by
          have hvm2 : VmPreserved sf1 sm2 := hsm2 ▸ hvmp
          rw [← A.pool_transport lim (M.stepEvents evsBr st) sf1 sm2 hvm2]
          change SepWPp (runProgPlaced H) _ _ _ _ _ _
          have hok2 : r1b_OkCtxPlaced r1b_CodeOk S g d s0 sm2 0x24dc := hok1.of_step
            { pc := by rw [runPcPlaced_eq]; simp [hsm2, arm64_norm]
              run := by simp [hsm2, arm64_norm, hin1.run]
              sp := by simpa [hsm2, arm64_norm] using hin1.sp
              fp := by simpa [hsm2, arm64_norm] using hin1.fp
              inv := hinv2, spAligned := hst.spAligned
              vregs := by simpa [calleeSavedVRegs, hsm2, arm64_norm] using hin1.vregs }
            (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
            (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
          rw [← hinvCore, r1b_invCore_split_mid_placed]
          have h4d0_48 := r1b_h4d0_vec_region fsp 0xfffffffffffffffe#64 opkCap opkPtr 0#64
          have h110 : ((fsp + 0x110#64) ↦₆₄ v110_in) ⊢ memRegion (fsp + 0x110#64) 8 :=
            pointsTo64_entails_memRegion _ _
          try rw [hx26_1]
          refine r1b_sepWPp_frame_op (by r1b_ac)
            (sepConj_mono (r1b_opkStage1_of_regions fsp) (sepConj_mono h4d0_48 h110)) (by r1b_ac) ?_
          simp only [sepExists_sepConj_left, sepConj_assoc]
          refine SepWPp.exists_elim fun b0 => SepWPp.exists_elim fun b1 =>
            SepWPp.exists_elim fun b2 => SepWPp.exists_elim fun b3 =>
            SepWPp.exists_elim fun b4 => SepWPp.exists_elim fun b5 =>
            SepWPp.exists_elim fun b6 => SepWPp.exists_elim fun w0e0 =>
            SepWPp.exists_elim fun w0e4 => SepWPp.exists_elim fun w9 =>
            SepWPp.exists_elim fun w13 => SepWPp.exists_elim fun w15 =>
            SepWPp.exists_elim fun w23 => SepWPp.exists_elim fun b31 => ?_
          have hx24_2_run : sm2.readReg64 (.gpr 24#5) = runFsp s0 + 0x380#64 := by
            change sm2.readReg64 (.gpr 24#5) = fsp + 0x380#64
            solve | simp [hsm2, arm64_norm] | simpa [hsm2, arm64_norm] using congrArg (· + 0x380#64) (hin1.sp : sf1.sp = fsp)
          refine sepWPp_weaken_pre ?_
            (r1b_opk_free_24dc_placed (st := M.stepEvents evsBr st)
              (opkCap := opkCap) (opkPtr := opkPtr) (opkBs := [])
              (kpkKey := kpkKey) (kpkSig := ([] : List (BitVec 8)))
              (spkKey := spkKey) (spkSig := ([] : List (BitVec 8))) hh hbnd hok2
              (by simp [hsm2, arm64_norm])
              (by solve | simp [hsm2, arm64_norm] | simpa [hsm2, arm64_norm] using hx23_1)
              hx24_2_run (by simp [hsm2, arm64_norm])
              (by solve | simp [hsm2, arm64_norm] | simpa [hsm2, arm64_norm] using hx27_1)
              (by solve | simp [hsm2, arm64_norm] | simpa [hsm2, arm64_norm] using hx24_1)
              hpanic fun sf3 evsFree hfo hok3 hx23_3 hx24_3 hx25_3 hx27_3 hx28_3 => by
                dsimp only; rw [← M.stepEvents_append evsBr evsFree st]
                exact hk sf3 (evsBr ++ evsFree) [] none v11c_in
                  b0 b1 b2 b3 b4 b5 b6 w0e0 w0e4 w9 w13 w15 w23 b31
                  (SeqEnv.append hevsBr' hfo) hok3 hopk_rd (Or.inl ⟨rfl, rfl⟩)
                  hx23_3 hx24_3 hx25_3 hx27_3 hx28_3)
          exact Entails.of_eq (by r1b_ac)
      · have hopk_len_pos : 0 < opkBs.length := List.length_pos_of_ne_nil hopk_nil
        have hopk_nat : (BitVec.ofNat 64 opkBs.length).toNat = opkBs.length := by
          simp only [BitVec.toNat_ofNat]; omega
        have hopk_nz : (BitVec.ofNat 64 opkBs.length == 0#64) = false := by
          apply beq_false_of_ne; intro h0
          have := congrArg BitVec.toNat h0; simp only [hopk_nat, BitVec.toNat_ofNat] at this; omega
        let _ := hopk_nz
        have hpc := hin1.pc; change sf1.pc = (blkPl_579).base + 0x1300#64 at hpc
        have hrun := hin1.run; have hsp : sf1.sp = fsp := hin1.sp
        apply r1b_seq_lscro_oom (mid := lsmpl.base 593) hin1.inv
        dsimp only [runProgPlaced, lsProg_579]
        apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
          blkLib_eq_579 blk579_noSvc0 (mid := lsmpl.base 593)
        intro _m_strip; have hpc_s : (sf1.setMem _m_strip).pc = (blkPl_579).base + 0x1300#64 := hpc
        wp_steps; clear hpc_s
        refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
          (by simp only [wp_norm, arm64_norm, *]) fun _m_real hnsp => ?_
        have hvmp : VmPreserved sf1 _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
        try simp only [State.setMem_setMem] at hvmp ⊢
        apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        refine r1b_bind_state_placed fun sm2 hsm2 hinv2 => by
          have hvm2 : VmPreserved sf1 sm2 := hsm2 ▸ hvmp
          rw [← A.pool_transport lim (M.stepEvents evsBr st) sf1 sm2 hvm2]; clear hpc hrun hsp
          change SepWPp (runProgPlaced H) _ _ _ _ _ _
          try rw [hx26_1]
          have h4d0_48 := r1b_h4d0_vec_region fsp 0xfffffffffffffffe#64 opkCap opkPtr (BitVec.ofNat 64 opkBs.length)
          refine r1b_sepWPp_frame_op (by r1b_ac) h4d0_48 (by r1b_ac) ?_
          refine r1b_call_frame_op <| r1b_sepWPp_borrow_core A.repAlloc (cap := opkCap) (ptr := opkPtr)
            (len := BitVec.ofNat 64 opkBs.length) (bs := opkBs) fun ⟨_, hopk_le, _, _⟩ => ?_
          refine r1b_call_frame_op <|
            r1b_call_splitId_placed (g := g) (st := M.stepEvents evsBr st)
              (ret := fsp + 0x4d0#64) (fp := opkPtr) (file := opkBs) hh hc hbnd hinv2
              (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm, hin1.run])
              (by simpa [hsm2, arm64_norm] using hin1.sp) (by simpa [hsm2, arm64_norm] using hin1.fp)
              (by simpa [calleeSavedVRegs, hsm2, arm64_norm] using hin1.vregs)
              hst.spAligned (retOff := 0x133c) (by rw [runPcPlaced_eq]; simp [hsm2, arm64_norm])
              (by solve | simp [hsm2, arm64_norm] | simpa [hsm2, arm64_norm] using congrArg (· + 0x4d0#64) hin1.sp)
              (by simp [hsm2, arm64_norm]) (by simp only [hsm2, arm64_norm]; exact hopk_nat)
              (hfit_sp evsBr opkBs hopk_nil hevsBr' hopk_rd) hpanic
              (fun sf2 evsSp eCap ePtr eBs hevsSp hin2 hcs2 hsp_none hfs2 htr2 => ?_)
              (fun sf2 evsSp opkId opkKey hevsSp hin2 hcs2 hsp_ok hfs2 htr2 => ?_)
          · have hok2 : r1b_OkCtxPlaced r1b_CodeOk S g d s0 sf2 0x133c := hok1.after_call
              (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
              (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
              hin2 hcs2 hfs2 htr2
            have hc2 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sf2 0x133c :=
              hok2.to_err (r1b_none_opk_split hopk_rd hopk_nil hsp_none)
            have hrejoin := r1b_ownedBytes_rejoin A.repAlloc opkCap opkPtr opkBs hopk_le hopk_cap63 hopk_ne
            refine r1b_sepWPp_frame_op (by r1b_ac) hrejoin (by r1b_ac) ?_
            have h4d8 : ((fsp + 0x4d8#64) ↦₆₄ eCap) =
                ((fsp + 0x4d8#64) ↦₃₂ eCap.extractLsb' 0 32) ∗ ((fsp + 0x4dc#64) ↦₃₂ eCap.extractLsb' 32 32) := by
              simpa only [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo64_split32 (fsp + 0x4d8#64) eCap
            try simp only [BitVec.add_assoc]; try simp only [BitVec.reduceAdd]; try simp only [sepConj_assoc]
            try rw [← BitVec.add_assoc kpkPtr 4#64]; try rw [← BitVec.add_assoc spkPtr 4#64]; try rw [← BitVec.add_assoc opkPtr 4#64]
            rw [h4d8]; try simp only [sepConj_assoc]; dsimp only [speWord]
            have hpc := hin2.pc; change sf2.pc = (blkPl_579).base + 0x133c#64 at hpc
            have hrun := hin2.run; have hsp : sf2.sp = fsp := hin2.sp
            apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x2420#64) hin2.inv
            dsimp only [runProgPlaced, lsProg_579]
            apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
              blkLib_eq_579 blk579_noSvc0 (mid := (blkPl_579).base + 0x2420#64)
            intro _m_strip; have hpc_s : (sf2.setMem _m_strip).pc = (blkPl_579).base + 0x133c#64 := hpc
            wp_steps; clear hpc_s
            refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
              (by simp only [wp_norm, arm64_norm, *]) fun _m_real hnsp => ?_
            have hvmp : VmPreserved sf2 _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
            try simp only [State.setMem_setMem] at hvmp ⊢
            apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
            refine r1b_bind_state_placed fun sm3 hsm3 hinv3 => by
              have hvm3 : VmPreserved sf2 sm3 := hsm3 ▸ hvmp
              rw [← A.pool_transport lim (M.stepEvents evsSp (M.stepEvents evsBr st)) sf2 sm3 hvm3]
              change SepWPp (runProgPlaced H) _ _ _ _ _ _
              have hc3 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm3 0x2420 := hc2.of_step
                { pc := by rw [runPcPlaced_eq]; simp [hsm3, arm64_norm]
                  run := by simp [hsm3, arm64_norm, hin2.run]
                  sp := by simpa [hsm3, arm64_norm] using hin2.sp
                  fp := by simpa [hsm3, arm64_norm] using hin2.fp
                  inv := hinv3, spAligned := hst.spAligned
                  vregs := by simpa [calleeSavedVRegs, hsm3, arm64_norm] using hin2.vregs }
                (by simp [hsm3, arm64_norm]) (by simp [hsm3, arm64_norm]) (by simp [hsm3, arm64_norm])
                (by simp [hsm3, arm64_norm]) (by simp [hsm3, arm64_norm])
              have h130_m := r1b_h130_region fsp (kpkPtr + 4#64 + BitVec.ofNat 64 kpkKey.length)
                (BitVec.ofNat 64 kpkKey.length) (kpkPtr + 4#64) 64#64
              have h178 : ((fsp + 0x178#64) ↦₆₄ (spkPtr + 4#64)) ⊢ memRegion (fsp + 0x178#64) 8 :=
                pointsTo64_entails_memRegion _ _
              refine r1b_sepWPp_frame_op (by r1b_ac) (sepConj_mono h130_m h178) (by r1b_ac) ?_
              generalize herrCommon :
                r1b_errCommon (A.atState lim (M.stepEvents evsSp (M.stepEvents evsBr st)) sm3)
                  g d s0 resStack = errCommon
              have hcore_err :
                  invCore ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
                    ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
                    memRegion fsp 0x110 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
                    ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗ memRegion (fsp + 0x1750#64) 24 ∗
                    stackAt fsp (resStack - runFrame) ∗
                    A.pool lim (M.stepEvents evsSp (M.stepEvents evsBr st)) sm3 ⊢ errCommon := by
                refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
                    (pointsTo32_entails_memRegion (fsp + 0x164#64) _))))))) ?_
                rw [← hinvCore, ← herrCommon]
                exact r1b_invCore_to_errCommon_placed
                  (A.atState lim (M.stepEvents evsSp (M.stepEvents evsBr st)) sm3) g d s0 resStack
              have h1b0_cell :
                  ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
                    memRegion (fsp + 0x1b4#64) 4 ⊢
                    ∃∗ v1b0 : BitVec 64, (fsp + 0x1b0#64) ↦₆₄ v1b0 := by
                refine Entails.trans (sepConj_mono_left (pointsTo32_entails_memRegion _ _)) ?_
                rw [r1b_join_region fsp 0x1b0 4 4, ProofLib.memRegion_eight (fsp + 0x1b0#64)]
                exact Entails.refl _
              refine r1b_sepWPp_frame_op (by r1b_ac) (sepConj_mono hcore_err h1b0_cell) (by r1b_ac) ?_
              simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
              refine SepWPp.exists_elim fun v1b0_w => ?_
              have htr_eq : ((eCap.extractLsb' 0 32).zeroExtend 64).truncate 32 =
                  eCap.extractLsb' 0 32 := by bv_bits
              rw [← htr_eq]
              have hcl := r1b_err_2420_placed (st := M.stepEvents evsSp (M.stepEvents evsBr st))
                (v158 := spkPtr + 4#64 + BitVec.ofNat 64 spkKey.length) (v188 := spkId.zeroExtend 64)
                (v190 := d.ikW3) (v1a8 := d.ikW1) (v1b0 := v1b0_w)
                (eCap := eCap) (ePtr := ePtr) (eBs := eBs)
                (opkCap := opkCap) (opkPtr := opkPtr) (opkBs := opkBs)
                (kpkCap := kpkCap) (kpkPtr := kpkPtr) (kpkBs := kpkBs)
                (spkCap := spkCap) (spkPtr := spkPtr) (spkBs := spkBs)
                (regCap := regCap) (regPtr := regPtr) (regBs := [r0, r1, r2, r3])
                hh hdrop hbnd hc3 (by simp [hsm3, arm64_norm, speWord]) hpanic
                fun sf_r evsFree hfo hrej_f => by
                  rw [← M.stepEvents_append evsBr evsSp st,
                    ← M.stepEvents_append (evsBr ++ evsSp) evsFree st]
                  exact hrej sf_r ((evsBr ++ evsSp) ++ evsFree) (by
                    obtain ⟨b0', bs0', hopk_cons⟩ := List.exists_cons_of_ne_nil hopk_nil
                    have hopk_rd' :
                        cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "one-time-pre-key") =
                          .ok (b0' :: bs0') := hopk_cons ▸ hopk_rd
                    have hsp_none' : splitId (b0' :: bs0') = none := hopk_cons ▸ hsp_none
                    have hevsSp' : cEnvs.splitId (b0' :: bs0') evsSp := hopk_cons ▸ hevsSp
                    unfold R1bStepOpkErrEnv; rw [hopk_rd']; dsimp only; rw [hsp_none']
                    exact SeqEnv.append (SeqEnv.append hevsBr' hevsSp') hfo) hrej_f
              dsimp only at hcl; rw [herrCommon] at hcl
              refine sepWPp_weaken_pre ?_ hcl; exact Entails.of_eq (by r1b_ac)
          ·
            have hok2 : r1b_OkCtxPlaced r1b_CodeOk S g d s0 sf2 0x133c := hok1.after_call
              (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
              (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
              (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
              hin2 hcs2 hfs2 htr2
            have hx23_2 : sf2.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64 :=
              hcs2.2.2.2.2.1.trans (by solve | simp [hsm2, arm64_norm] | simpa [hsm2, arm64_norm] using hx23_1)
            have hx24_2 : sf2.readReg64 (.gpr 24#5) = fsp + 0x380#64 :=
              hcs2.2.2.2.2.2.1.trans (by solve | simp [hsm2, arm64_norm] | simpa [hsm2, arm64_norm] using congrArg (· + 0x380#64) (hin1.sp : sf1.sp = fsp))
            have hx25_2 : sf2.readReg64 (.gpr 25#5) = BitVec.ofNat 64 opkBs.length :=
              hcs2.2.2.2.2.2.2.1.trans (by simp [hsm2, arm64_norm])
            have hx27_2 : sf2.readReg64 (.gpr 27#5) = BitVec.ofNat 64 spkKey.length :=
              hcs2.2.2.2.2.2.2.2.2.1.trans (by solve | simp [hsm2, arm64_norm] | simpa [hsm2, arm64_norm] using hx27_1)
            have hx28_2 : sf2.readReg64 (.gpr 28#5) = 64#64 :=
              hcs2.2.2.2.2.2.2.2.2.2.1.trans (by solve | simp [hsm2, arm64_norm] | simpa [hsm2, arm64_norm] using hx24_1)
            obtain ⟨hopk_eq, ht4, hopk_len_eq⟩ := r1b_splitId_bytes hsp_ok
            have hopkKey63 : opkKey.length < 2 ^ 63 := by omega
            have hopkKey_nat : (BitVec.ofNat 64 opkKey.length).toNat = opkKey.length := by
              simp only [BitVec.toNat_ofNat]; omega
            rw [r1b_splitId_slice_eq (ptr := opkPtr) hopk_eq ht4]
            try simp only [BitVec.add_assoc]; try simp only [BitVec.reduceAdd]; try simp only [sepConj_assoc]
            try rw [← BitVec.add_assoc kpkPtr 4#64]; try rw [← BitVec.add_assoc spkPtr 4#64]; try rw [← BitVec.add_assoc opkPtr 4#64]
            dsimp only [splitOkTag]
            have hpc := hin2.pc; change sf2.pc = (blkPl_579).base + 0x133c#64 at hpc
            have hrun := hin2.run; have hsp : sf2.sp = fsp := hin2.sp
            apply r1b_seq_lscro_oom (mid := lsmpl.base 201) hin2.inv
            dsimp only [runProgPlaced, lsProg_579]
            apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
              blkLib_eq_579 blk579_noSvc0 (mid := lsmpl.base 201)
            intro _m_strip; have hpc_s : (sf2.setMem _m_strip).pc = (blkPl_579).base + 0x133c#64 := hpc
            wp_steps; clear hpc_s
            refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
              (by simp only [wp_norm, arm64_norm, *]) fun _m_real hnsp => ?_
            have hvmp : VmPreserved sf2 _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
            try simp only [State.setMem_setMem] at hvmp ⊢
            apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
            refine r1b_bind_state_placed fun sm3 hsm3 hinv3 => by
              have hvm3 : VmPreserved sf2 sm3 := hsm3 ▸ hvmp
              rw [← A.pool_transport lim (M.stepEvents evsSp (M.stepEvents evsBr st)) sf2 sm3 hvm3]
              clear hpc hrun hsp
              change SepWPp (runProgPlaced H) _ _ _ _ _ _
              have h4d0_48 :
                  ((fsp + 0x4d0#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
                    ((fsp + 0x4d8#64) ↦₃₂ opkId) ∗ memRegion (fsp + 0x4dc#64) 4 ∗
                    ((fsp + 0x4e0#64) ↦₆₄ (opkPtr + 4#64)) ∗
                    ((fsp + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 opkKey.length) ∗
                    memRegion (fsp + 0x4f0#64) 16 ⊢
                    memRegion (fsp + 0x4d0#64) 33 ∗ memRegion (fsp + 0x4f1#64) 15 := by
                have h32 :
                    ((fsp + 0x4d0#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
                      (((fsp + 0x4d8#64) ↦₃₂ opkId) ∗ memRegion (fsp + 0x4dc#64) 4) ∗
                      ((fsp + 0x4e0#64) ↦₆₄ (opkPtr + 4#64)) ∗
                      ((fsp + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 opkKey.length) ⊢
                      memRegion (fsp + 0x4d0#64) 32 := by
                  refine Entails.trans (sepConj_mono_right (sepConj_mono_left
                    (Entails.trans (sepConj_mono_left (pointsTo32_entails_memRegion _ _))
                      (Entails.of_eq (r1b_join_region fsp 0x4d8 4 4))))) ?_
                  refine Entails.trans (sepConj_mono_right (sepConj_mono_right
                    (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
                      r1b_cells2_to_region16 (fsp + 0x4e0#64) (opkPtr + 4#64) (BitVec.ofNat 64 opkKey.length)))) ?_
                  refine Entails.trans (sepConj_mono_right (Entails.of_eq (r1b_join_region fsp 0x4d8 8 16))) ?_
                  simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
                    r1b_cell64_cons (a := fsp + 0x4d0#64) 0xfffffffffffffffe#64 (n := 24) (by decide)
                have heq4d0 :
                    ((fsp + 0x4d0#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
                      ((fsp + 0x4d8#64) ↦₃₂ opkId) ∗ memRegion (fsp + 0x4dc#64) 4 ∗
                      ((fsp + 0x4e0#64) ↦₆₄ (opkPtr + 4#64)) ∗
                      ((fsp + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 opkKey.length) ∗
                      memRegion (fsp + 0x4f0#64) 16 =
                    (((fsp + 0x4d0#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
                      (((fsp + 0x4d8#64) ↦₃₂ opkId) ∗ memRegion (fsp + 0x4dc#64) 4) ∗
                      ((fsp + 0x4e0#64) ↦₆₄ (opkPtr + 4#64)) ∗
                      ((fsp + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 opkKey.length)) ∗
                      memRegion (fsp + 0x4f0#64) 16 := by r1b_ac
                rw [heq4d0]; refine Entails.trans (sepConj_mono_left h32) ?_
                rw [r1b_join_region fsp 0x4d0 32 16, r1b_split_region fsp 0x4d0 33 15]
                simpa only [Nat.reduceAdd, BitVec.ofNat_eq_ofNat] using Entails.refl _
              refine r1b_sepWPp_frame_op (by r1b_ac) h4d0_48 (by r1b_ac) ?_
              refine r1b_call_frame_op <|
                r1b_call_pkDeserialize_pool_placed (g := g)
                  (st := M.stepEvents evsSp (M.stepEvents evsBr st)) hh hinv3
                  (by simp [hsm3, arm64_norm]) (by simp [hsm3, arm64_norm, hin2.run])
                  (by simpa [hsm3, arm64_norm] using hin2.sp) (by simpa [hsm3, arm64_norm] using hin2.fp)
                  (by simpa [calleeSavedVRegs, hsm3, arm64_norm] using hin2.vregs)
                  hst.spAligned (retOff := 0x1360) (by rw [runPcPlaced_eq]; simp [hsm3, arm64_norm])
                  (ptr := opkPtr + 4#64) (bs := opkKey) (sret := fsp + 0x4d0#64)
                  (by simp [hsm3, arm64_norm]) (by simp only [hsm3, arm64_norm]; exact hopkKey_nat)
                  (by solve | simp [hsm3, arm64_norm] | simpa [hsm3, arm64_norm] using congrArg (· + 0x4d0#64) hin2.sp)
                  hopkKey63 hpanic fun sf3 hin3 hcs3 hfs3 htr3 => ?_
              have hok3 : r1b_OkCtxPlaced r1b_CodeOk S g d s0 sf3 0x1360 := hok2.after_call
                (by simp [hsm3, arm64_norm]) (by simp [hsm3, arm64_norm]) (by simp [hsm3, arm64_norm])
                (by simp [hsm3, arm64_norm]) (by simp [hsm3, arm64_norm]) (by simp [hsm3, arm64_norm])
                hin3 hcs3 hfs3 htr3
              have hx23_3 : sf3.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64 :=
                hcs3.2.2.2.2.1.trans (by solve | simp [hsm3, arm64_norm] | simpa [hsm3, arm64_norm] using hx23_2)
              have hx24_3 : sf3.readReg64 (.gpr 24#5) = fsp + 0x380#64 :=
                hcs3.2.2.2.2.2.1.trans (by solve | simp [hsm3, arm64_norm] | simpa [hsm3, arm64_norm] using hx24_2)
              have hx25_3 : sf3.readReg64 (.gpr 25#5) = BitVec.ofNat 64 opkBs.length :=
                hcs3.2.2.2.2.2.2.1.trans (by solve | simp [hsm3, arm64_norm] | simpa [hsm3, arm64_norm] using hx25_2)
              have hx27_3 : sf3.readReg64 (.gpr 27#5) = BitVec.ofNat 64 spkKey.length :=
                hcs3.2.2.2.2.2.2.2.2.1.trans (by solve | simp [hsm3, arm64_norm] | simpa [hsm3, arm64_norm] using hx27_2)
              have hx28_3 : sf3.readReg64 (.gpr 28#5) = 64#64 :=
                hcs3.2.2.2.2.2.2.2.2.2.1.trans (by solve | simp [hsm3, arm64_norm] | simpa [hsm3, arm64_norm] using hx28_2)
              have hrejoin_opk :
                  (opkPtr ↦ₛ opkBs.take 4) ∗ ((opkPtr + 4#64) ↦ₛ opkKey) ∗
                    r1b_ownedRest A.repAlloc opkCap opkPtr opkBs.length ⊢
                    ownedBytes A.repAlloc opkCap opkPtr (BitVec.ofNat 64 opkBs.length) opkBs := by
                rw [← sepConj_assoc, ← r1b_splitId_slice_eq (ptr := opkPtr) hopk_eq ht4]
                exact r1b_ownedBytes_rejoin A.repAlloc opkCap opkPtr opkBs hopk_le hopk_cap63 hopk_ne
              refine r1b_sepWPp_frame_op (by r1b_ac) hrejoin_opk (by r1b_ac) ?_
              cases hopk_d : PublicKey.deserialize opkKey with
              | error e =>
                have hc3 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sf3 0x1360 :=
                  hok3.to_err (r1b_none_opk_deser hopk_rd hopk_nil hsp_ok hopk_d)
                have h11c : ((fsp + 0x11c#64) ↦₃₂ opkId) ⊢ memRegion (fsp + 0x11c#64) 4 := pointsTo32_entails_memRegion _ _
                have h130_m := r1b_h130_region fsp (kpkPtr + 4#64 + BitVec.ofNat 64 kpkKey.length)
                  (BitVec.ofNat 64 kpkKey.length) (kpkPtr + 4#64) 64#64
                have h158 : ((fsp + 0x158#64) ↦₆₄ (spkPtr + 4#64 + BitVec.ofNat 64 spkKey.length)) ⊢
                    memRegion (fsp + 0x158#64) 8 := pointsTo64_entails_memRegion _ _
                have h178 : ((fsp + 0x178#64) ↦₆₄ (spkPtr + 4#64)) ⊢ memRegion (fsp + 0x178#64) 8 := pointsTo64_entails_memRegion _ _
                have h188 : ((fsp + 0x188#64) ↦₆₄ spkId.zeroExtend 64) ⊢ memRegion (fsp + 0x188#64) 8 := pointsTo64_entails_memRegion _ _
                refine r1b_sepWPp_frame_op (by r1b_ac)
                  (sepConj_mono h11c (sepConj_mono h130_m (sepConj_mono h158 (sepConj_mono h178 h188)))) (by r1b_ac) ?_
                generalize herrCommon :
                  r1b_errCommon (A.atState lim (M.stepEvents evsSp (M.stepEvents evsBr st)) sf3) g d s0 resStack = errCommon
                have h188_m : memRegion (fsp + 0x188#64) 8 ∗ memRegion (fsp + 0x190#64) 8 =
                    memRegion (fsp + 0x188#64) 16 := r1b_join_region fsp 0x188 8 8
                have hst_err :
                    invCore ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
                      ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
                      memRegion fsp 0x110 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
                      ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗ ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
                      ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗ ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
                      memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
                      stackAt fsp (resStack - runFrame) ∗ A.pool lim (M.stepEvents evsSp (M.stepEvents evsBr st)) sf3 ⊢
                      errCommon ∗ memRegion (fsp + 0x190#64) 8 ∗ memRegion (fsp + 0x1a8#64) 16 := by
                  rw [← hinvCore, ← herrCommon]
                  exact r1b_stage_to_err_placed (A.atState lim (M.stepEvents evsSp (M.stepEvents evsBr st)) sf3)
                    g d s0 resStack (ofLe32 r0 r1 r2 r3)
                have hcl := r1b_opk_deser_err_1360_placed (st := M.stepEvents evsSp (M.stepEvents evsBr st))
                  (opkCap := opkCap) (opkPtr := opkPtr) (opkBs := opkBs) (opkKey := opkKey)
                  (kpkCap := kpkCap) (kpkPtr := kpkPtr) (kpkBs := kpkBs)
                  (spkCap := spkCap) (spkPtr := spkPtr) (spkBs := spkBs)
                  (regCap := regCap) (regPtr := regPtr) (regBs := [r0, r1, r2, r3])
                  hh hdrop hbnd hc3 hopk_d hpanic fun sf_r evsFree hfo hrej_f => by
                    rw [← M.stepEvents_append evsBr evsSp st, ← M.stepEvents_append (evsBr ++ evsSp) evsFree st]
                    exact hrej sf_r ((evsBr ++ evsSp) ++ evsFree) (by
                      obtain ⟨b0', bs0', hopk_cons⟩ := List.exists_cons_of_ne_nil hopk_nil
                      have hopk_rd' : cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "one-time-pre-key") =
                          .ok (b0' :: bs0') := hopk_cons ▸ hopk_rd
                      have hsp_ok' : splitId (b0' :: bs0') = some (opkId, opkKey) := hopk_cons ▸ hsp_ok
                      have hevsSp' : cEnvs.splitId (b0' :: bs0') evsSp := hopk_cons ▸ hevsSp
                      unfold R1bStepOpkErrEnv; rw [hopk_rd']; dsimp only; rw [hsp_ok']; dsimp only; rw [hopk_d]
                      exact SeqEnv.append (SeqEnv.append hevsBr' hevsSp') hfo) hrej_f
                dsimp only at hcl; rw [herrCommon] at hcl
                refine sepWPp_weaken_pre ?_ hcl
                refine Entails.trans (r1b_entails_frame_op (by r1b_ac) hst_err (by r1b_ac)) ?_
                rw [← h188_m]; exact Entails.of_eq (by r1b_ac)
              | ok opkPk =>
                obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, w9, w13, w15, w23, b31, hopk_bytes⟩ :=
                  exists_pkBytesOf opkPk.bytes.toList (by simp)
                dsimp only [deserializeResult33At]
                rw [hopk_bytes, ← pkLayoutAt_eq_pointsToBytes]; try simp only [sepConj_assoc]
                have hpc := hin3.pc; change sf3.pc = (blkPl_579).base + 0x1360#64 at hpc
                have hrun := hin3.run; have hsp : sf3.sp = fsp := hin3.sp
                apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x2490#64) hin3.inv
                dsimp only [runProgPlaced, lsProg_579]
                apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
                  blkLib_eq_579 blk579_noSvc0 (mid := (blkPl_579).base + 0x2490#64)
                intro _m_strip; have hpc_s : (sf3.setMem _m_strip).pc = (blkPl_579).base + 0x1360#64 := hpc
                wp_steps; clear hpc_s
                refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
                  (by simp only [wp_norm, arm64_norm, *]) fun _m_real hnsp => ?_
                have hvmp : VmPreserved sf3 _ :=
                  hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
                try simp only [State.setMem_setMem] at hvmp ⊢
                apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
                  (by simp only [wp_norm, arm64_norm, *])
                refine r1b_bind_state_placed fun sm4 hsm4 hinv4 => by
                  have hvm4 : VmPreserved sf3 sm4 := hsm4 ▸ hvmp
                  rw [← A.pool_transport lim (M.stepEvents evsSp (M.stepEvents evsBr st)) sf3 sm4 hvm4]
                  change SepWPp (runProgPlaced H) _ _ _ _ _ _
                  have hok4 : r1b_OkCtxPlaced r1b_CodeOk S g d s0 sm4 0x2490 := hok3.of_step
                    { pc := by rw [runPcPlaced_eq]; simp [hsm4, arm64_norm]
                      run := by simp [hsm4, arm64_norm, hin3.run]
                      sp := by simpa [hsm4, arm64_norm] using hin3.sp
                      fp := by simpa [hsm4, arm64_norm] using hin3.fp
                      inv := hinv4
                      vregs := by simpa [calleeSavedVRegs, hsm4, arm64_norm] using hin3.vregs
                      spAligned := hst.spAligned }
                    (by simp [hsm4, arm64_norm]) (by simp [hsm4, arm64_norm])
                    (by simp [hsm4, arm64_norm]) (by simp [hsm4, arm64_norm])
                    (by simp [hsm4, arm64_norm]) (by simp [hsm4, arm64_norm])
                  rw [← hinvCore, r1b_invCore_split_mid_placed]
                  refine r1b_sepWPp_frame_op (by r1b_ac) (r1b_opkStage1_of_regions fsp) (by r1b_ac) ?_
                  simp only [sepExists_sepConj_left, sepConj_assoc]
                  refine SepWPp.exists_elim fun c0 => SepWPp.exists_elim fun c1 =>
                    SepWPp.exists_elim fun c2 => SepWPp.exists_elim fun c3 =>
                    SepWPp.exists_elim fun c4 => SepWPp.exists_elim fun c5 =>
                    SepWPp.exists_elim fun c6 => SepWPp.exists_elim fun w0e0_in =>
                    SepWPp.exists_elim fun w0e4_in => SepWPp.exists_elim fun w9_in =>
                    SepWPp.exists_elim fun w13_in => SepWPp.exists_elim fun w15_in =>
                    SepWPp.exists_elim fun w23_in => SepWPp.exists_elim fun b31_in => ?_
                  have htr_b8 : (b8.zeroExtend 32).truncate 8 = b8 := by bv_bits
                  have htr_b7 : (b7.zeroExtend 32).truncate 8 = b7 := by bv_bits
                  have hx24_4_run : sm4.readReg64 (.gpr 24#5) = runFsp s0 + 0x380#64 := by
                    change sm4.readReg64 (.gpr 24#5) = fsp + 0x380#64
                    solve | simp [hsm4, arm64_norm] | simpa [hsm4, arm64_norm] using hx24_3
                  refine sepWPp_weaken_pre ?_
                    (r1b_opk_copy1_2490_placed
                      (st := M.stepEvents evsSp (M.stepEvents evsBr st))
                      (opkCap := opkCap) (opkPtr := opkPtr) (opkBs := opkBs)
                      (kpkKey := kpkKey) (kpkSig := ([] : List (BitVec 8)))
                      (spkKey := spkKey) (spkSig := ([] : List (BitVec 8)))
                      (b7 := b7) (b8 := b8)
                      (c0 := c0) (c1 := c1) (c2 := c2) (c3 := c3) (c4 := c4) (c5 := c5) (c6 := c6)
                      (w0e0_in := w0e0_in) (w0e4_in := w0e4_in) (w9_in := w9_in)
                      (w13_in := w13_in) (w15_in := w15_in) (w23_in := w23_in) (b31_in := b31_in)
                      hh hbnd hok4
                      (by solve | simp [hsm4, arm64_norm] | simpa [hsm4, arm64_norm] using hx23_3)
                      hx24_4_run
                      (by solve | simp [hsm4, arm64_norm] | simpa [hsm4, arm64_norm] using hx25_3)
                      (by solve | simp [hsm4, arm64_norm] | simpa [hsm4, arm64_norm] using hx27_3)
                      (by solve | simp [hsm4, arm64_norm] | simpa [hsm4, arm64_norm] using hx28_3)
                      hpanic fun sf5 evsFree hfo hok5 hx23_5 hx24_5 hx25_5 hx27_5 hx28_5 => by
                        dsimp only
                        rw [← M.stepEvents_append evsBr evsSp st,
                          ← M.stepEvents_append (evsBr ++ evsSp) evsFree st]
                        have hok_env :
                            R1bStepOpkOkEnv cEnvs (runFiles g.i) d.dir opkBs
                              ((evsBr ++ evsSp) ++ evsFree) := by
                          obtain ⟨b0', bs0', hopk_cons⟩ := List.exists_cons_of_ne_nil hopk_nil
                          have hevsSp' : cEnvs.splitId (b0' :: bs0') evsSp := hopk_cons ▸ hevsSp
                          rw [hopk_cons]
                          exact SeqEnv.append (SeqEnv.append hevsBr' hevsSp') hfo
                        exact hk sf5 ((evsBr ++ evsSp) ++ evsFree) opkBs (some (opkId, opkPk)) opkId
                          b0 b1 b2 b3 b4 b5 b6 (b8.zeroExtend 32) (b7.zeroExtend 32)
                          w9 w13 w15 w23 b31 hok_env hok5 hopk_rd
                          (Or.inr ⟨opkId, opkKey, opkPk, hopk_nil, hopk_len63, hsp_ok, hopk_d,
                            rfl, rfl, by simpa only [htr_b8, htr_b7] using hopk_bytes⟩)
                          hx23_5 hx24_5 hx25_5 hx27_5 hx28_5)
                  exact Entails.of_eq (by r1b_ac)

theorem r1b_step_opk_placed_env [LibsignalPlacement] {M : AllocCostModel}
    {S : RunSem} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {cEnvs : RunCalleesEnvs} {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets} {σ : RunSlots}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {r0 r1 r2 r3 : BitVec 8}
    {kpkCap kpkPtr spkCap spkPtr regCap regPtr : BitVec 64}
    {kpkBs kpkKey spkBs spkKey : List (BitVec 8)}
    {kpkId spkId : BitVec 32}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hc : RunCalleesPlaced A lim cEnvs H B σ)
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (he : AtRunEntryPlaced r1b_CodeOk S g s0)
    (hok : r1b_OkCtxPlaced r1b_CodeOk S g d s0 s 0x12dc)
    (hx25 : s.readReg64 (.gpr 25#5) = d.dirPtr)
    (hx28 : s.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length)
    (hx26 : s.readReg64 (.gpr 26#5) = kpkPtr)
    (hx27 : s.readReg64 (.gpr 27#5) = BitVec.ofNat 64 spkKey.length)
    (hx9 : s.readReg64 (.gpr 9#5) = BitVec.ofNat 64 kpkKey.length)
    (hx10 : s.readReg64 (.gpr 10#5) = kpkPtr + 4#64)
    (hx8 : s.readReg64 (.gpr 8#5) = kpkPtr + 4#64 + BitVec.ofNat 64 kpkKey.length)
    (hx23 : s.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64)
    (hx24 : s.readReg64 (.gpr 24#5) = 64#64)
    (hfit_br : FitsEnv M lim st (cEnvs.bundleRead (runFiles g.i) d.dir (utf8 "one-time-pre-key")))
    (hfit_sp : ∀ (evs_br : List AllocEvent) (opkBs : List (BitVec 8)),
      opkBs ≠ [] →
      cEnvs.bundleRead (runFiles g.i) d.dir (utf8 "one-time-pre-key") evs_br →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "one-time-pre-key") = .ok opkBs →
      FitsEnv M lim (M.stepEvents evs_br st) (cEnvs.splitId opkBs))
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectKPlacedEnv r1b_CodeOk H A lim EnvAt g s0 resStack Q Qp oom)
    (henv : ∀ evs,
      R1bStepOpkErrEnv cEnvs (runFiles g.i) d.dir evs →
      EnvAt StoresGhost.opened .postDispatch (M.stepEvents evs st))
    (hk : ∀ (sf : State) (evs_opk : List AllocEvent) (opkBs : List (BitVec 8))
        (opk : Option (BitVec 32 × PublicKey))
        (v11c : BitVec 32)
        (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
        (w0e0 w0e4 w9 : BitVec 32) (w13 : BitVec 16) (w15 w23 : BitVec 64) (b31 : BitVec 8),
      R1bStepOpkOkEnv cEnvs (runFiles g.i) d.dir opkBs evs_opk →
      r1b_OkCtxPlaced r1b_CodeOk S g d s0 sf 0x24ec →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "one-time-pre-key") = .ok opkBs →
      ((opkBs = [] ∧ opk = none) ∨
        (∃ opkId opkKey opkPk, opkBs ≠ [] ∧ opkBs.length < 2 ^ 63 ∧
          splitId opkBs = some (opkId, opkKey) ∧
          PublicKey.deserialize opkKey = .ok opkPk ∧ opk = some (opkId, opkPk) ∧
          v11c = opkId ∧
          opkPk.bytes.toList = pkBytesOf b0 b1 b2 b3 b4 b5 b6
            (w0e4.truncate 8) (w0e0.truncate 8) w9 w13 w15 w23 b31)) →
      sf.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64 →
      sf.readReg64 (.gpr 24#5) = runFsp s0 + 0x380#64 →
      sf.readReg64 (.gpr 25#5) = BitVec.ofNat 64 opkBs.length →
      sf.readReg64 (.gpr 27#5) = BitVec.ofNat 64 spkKey.length →
      sf.readReg64 (.gpr 28#5) = 64#64 →
      let fsp := runFsp s0
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (memRegion (fsp + 0x4d0#64) 48 ∗
          ownedBytes A.repAlloc kpkCap kpkPtr (BitVec.ofNat 64 kpkBs.length) kpkBs ∗
          ownedBytes A.repAlloc spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
          ownedBytes A.repAlloc regCap regPtr 4#64 [r0, r1, r2, r3] ∗
          r1b_invCoreBase_placed A.repAlloc g d s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
          ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
          r1b_opkStage1At fsp b0 b1 b2 b3 b4 b5 b6 w0e0 w0e4 w9 w13 w15 w23 b31 ∗
          memRegion (fsp + 0x110#64) 8 ∗ ((fsp + 0x11c#64) ↦₃₂ v11c) ∗
          memRegion (fsp + 0x120#64) 8 ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
          ((fsp + 0x130#64) ↦₆₄ (kpkPtr + 4#64 + BitVec.ofNat 64 kpkKey.length)) ∗
          ((fsp + 0x138#64) ↦₆₄ BitVec.ofNat 64 kpkKey.length) ∗
          ((fsp + 0x140#64) ↦₆₄ (kpkPtr + 4#64)) ∗
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
          stackAt fsp (resStack - runFrame) ∗ A.pool lim (M.stepEvents evs_opk st) sf)
        Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
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
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s)
      Q Qp oom :=
  r1b_step_opk_placed hh hc hdrop hbnd he hok hx25 hx28 hx26 hx27 hx9 hx10 hx8 hx23 hx24
    hfit_br hfit_sp hpanic
    (fun sf evs herr hrej_f =>
      hrej sf (M.stepEvents evs st) StoresGhost.opened .postDispatch hrej_f (henv evs herr))
    hk

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadOpkSpinePlacedBudget
