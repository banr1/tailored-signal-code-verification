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
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.DeserCloneErrPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.DeserClonePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.DeserClonePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadOpkSpinePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.WorkFramePlacedFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.KemDeserialize.SpecBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Base
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSites
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpersParsePlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpersPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadKpkPlacedBudgetAux
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpkPlacedBudgetAux
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23

/-!
# `FdsGe3Closed`-Threaded Second Half of Stage 4a (`0x2584 → 0x25f4`) of Arm `R1b`

Proves `r1b_step_kpk_clone_2584_of_kem_placed_fd` (`0x2584 → 0x25f4`) on Block `579`, preserving
`FdsGe3Closed` across `kem::Key::deserialize`, `try_allocate_in(64, 1, 1)`, and `memcpy`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.DeserClonePlacedBudgetAuxFd

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (PublicKey)
open CryptoVerification (LibsignalHooks LibsignalPlacement lsLogFilterAddr lsmpl lsρ)
open CryptoVerification.LibsignalTripleRatchet (lsMemcpySym)
open CryptoVerification.LibsignalTripleRatchet.Wire (pkBytesOf)
open CryptoVerification.LibsignalTripleRatchetRepr (speWord)
open CryptoVerification.SignalSession.Cli (StoresGhost ofLe32 splitId splitSigned utf8)
open CryptoVerification.SignalSession.Cli.MainHops (RunCall cliIo ownedBytes sepWPp_weaken_pre)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_590)
open CryptoVerification.SignalSession.Cli.Run.Placed
  (blkLib_eq_579 blkPC_579 blkPl_579 lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (AtRejectPlaced Init1Data InRunPlaced PanicK RejectKind RunNeeds RunSem r1b_CodeOk
   r1b_ErrCtxPlaced r1b_StackBounds r1b_bind_state_placed r1b_box1568_unpack
   r1b_cell8_to_region r1b_cell64_cons r1b_cells2_to_region16 r1b_entails_frame_core
   r1b_fsp_align r1b_invCoreBase_placed r1b_join_region r1b_layout1 r1b_none_kpk_deser
   r1b_opkStage1SpkAt r1b_ownedBytes_borrow r1b_ownedBytes_rejoin r1b_ownedRest
   r1b_readBundleV_some r1b_sepWPp_frame_core r1b_sepWPp_pure_left r1b_spkBytesOf
   r1b_splitSigned_bytes r1b_splitSigned_slice_eq r1b_split_region readBundleV
   readBundleV_slice_lengths rejectMem runFiles runFsp runPcPlaced runPcPlaced_eq runProgPlaced)
open CryptoVerification.SignalSession.Cli.RunProofs (kemDeserResAt kemPkDeserialize)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets runFrame)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEvents FreeOnlyEvs RustCliAllocBudget
   VmPreserved rustAllocEvents)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (FdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpersParsePlacedBudgetFd
  (r1b_call_kemDeserialize_of_kem_placed_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpersPlacedBudget
  (r1b_call_memcpy_region_pool_placed r1b_call_tryAlloc_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.DeserCloneErrPlacedBudget
  (r1b_kem_err_2654_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.DeserClonePlacedBudget
  (R1bKpkCloneErrEnv R1bKpkCloneOkEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadKpkPlacedBudgetAux
  (r1b_seq_lscro_oom)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpkPlacedBudgetAux
  (blk579_noSvc0)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.WorkFramePlacedFd
  (r1b_OkCtxPlacedFd)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs slotsOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget
  (DropSpeOwnedOkAtBlock)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.KemDeserialize.SpecBudget
  (kemDeserializeEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd (slotWithFdsGe3Closed)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local simp, local arm64_norm, local wp_norm]
  runPcPlaced_eq BitVec.ofNat_eq_ofNat
  State.fs_writeReg64 State.fs_writeReg32 State.fs_writeVReg128
  State.fs_advancePC State.fs_setPC State.fs_setPState
  State.fs_setMem State.fs_setStatus State.fs_appendTrace

@[local simp, local arm64_norm, local wp_norm]
private theorem r1b_fs_setMem_local (s : State) (m : Memory) : (s.setMem m).fs = s.fs := rfl

@[local simp, local arm64_norm, local wp_norm]
private theorem r1b_fs_setPState_local (s : State) (ps : PState) : (s.setPState ps).fs = s.fs := rfl

local macro (priority := high) "r1b_ac_dc" : tactic =>
  `(tactic| ((try dsimp +zetaDelta only) <;> first | rfl | simp only [emp_sepConj] | sep_ac_rfl))

private meta def r1bStripLetsDC : Nat → Lean.Expr → Lean.Expr
  | 0, e => e
  | n + 1, .letE _ _ v b _ => r1bStripLetsDC n (b.instantiate1 v)
  | n + 1, .mdata _ e => r1bStripLetsDC n e
  | _, e => e

private meta def r1bSplitSepDC : Nat → Lean.Expr → Lean.Expr → Array Lean.Expr
  | 0, _, e => #[e]
  | fuel + 1, sepSample, e =>
    let e := r1bStripLetsDC 64 e
    let fn := sepSample.getAppFn.constName!
    let ar := sepSample.getAppNumArgs
    if e.isAppOfArity fn ar then
      r1bSplitSepDC fuel sepSample (e.getArg! (ar - 2)) ++
        r1bSplitSepDC fuel sepSample (e.getArg! (ar - 1))
    else #[e]

private meta def r1bIsDefEqPureDC (x a : Lean.Expr) : Lean.Elab.TermElabM Bool := do
  let x := r1bStripLetsDC 64 x; let a := r1bStripLetsDC 64 a
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

private meta def r1bComputeRestDC (ctxName : String) (p a1 : Lean.Expr) :
    Lean.Elab.TermElabM Lean.Expr := do
  let sepTy := Lean.mkConst ``SepProp []
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let ps := (r1bSplitSepDC 64 sepSample (← Lean.instantiateMVars p)).toList
  let a1s := (r1bSplitSepDC 64 sepSample (← Lean.instantiateMVars a1)).toList
  let mut rem := ps
  for a in a1s do
    let mut removed := false
    let mut next : List Lean.Expr := []
    for x in rem do
      if !removed && (← r1bIsDefEqPureDC x a) then removed := true
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

local elab (priority := high) "r1b_entails_frame_dc " t1:term:arg h:term:arg t2:term:arg :
    term <= expectedType => do
  let exp ← Lean.instantiateMVars expectedType
  if exp.isMVar then Lean.Elab.Term.tryPostpone
  let entSample ← Lean.Elab.Term.elabTerm (← `(emp ⊢ emp)) none
  let ear := entSample.getAppNumArgs
  let expS := r1bStripLetsDC 64 exp
  let p := expS.getArg! (ear - 2)
  let q := expS.getArg! (ear - 1)
  if (← Lean.instantiateMVars p).isMVar then Lean.Elab.Term.tryPostpone
  if (← Lean.instantiateMVars q).isMVar then Lean.Elab.Term.tryPostpone
  let hExpr ← Lean.Elab.Term.elabTerm h none
  let hTy := r1bStripLetsDC 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
  let a1 := hTy.getArg! (ear - 2)
  let a2 := hTy.getArg! (ear - 1)
  let r ← r1bComputeRestDC "r1b_entails_frame" p a1
  let sepTy := Lean.mkConst ``SepProp []
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let sar := sepSample.getAppNumArgs
  let mkSep (x y : Lean.Expr) : Lean.Expr :=
    sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
  let rIsEmp ← r1bIsDefEqPureDC r empExpr
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

local elab (priority := high) "r1b_sepWPp_frame_dc " t1:term:arg h:term:arg t2:term:arg hk:term:arg :
    term <= expectedType => do
  let exp ← Lean.instantiateMVars expectedType
  if exp.isMVar then Lean.Elab.Term.tryPostpone
  let expS := r1bStripLetsDC 64 exp
  let args := expS.getAppArgs
  let prog := args[0]!; let ret := args[1]!; let st := args[2]!; let p := args[3]!
  let q := args[4]!; let qp := args[5]!; let oom := args[6]!
  let entSample ← Lean.Elab.Term.elabTerm (← `(emp ⊢ emp)) none
  let ear := entSample.getAppNumArgs
  let hExpr ← Lean.Elab.Term.elabTerm h none
  let hTy := r1bStripLetsDC 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
  let a1 := hTy.getArg! (ear - 2)
  let a2 := hTy.getArg! (ear - 1)
  let r ← r1bComputeRestDC "r1b_sepWPp_frame" p a1
  let sepTy := Lean.mkConst ``SepProp []
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let sar := sepSample.getAppNumArgs
  let mkSep (x y : Lean.Expr) : Lean.Expr :=
    sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
  let rIsEmp ← r1bIsDefEqPureDC r empExpr
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
    let a2IsEmp ← r1bIsDefEqPureDC a2 empExpr
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

local elab:10 (priority := high) "r1b_call_frame_dc" "<|" h:term:10 : term <= expectedType => do
  let exp ← Lean.instantiateMVars expectedType
  if exp.isMVar then Lean.Elab.Term.tryPostpone
  let expS := r1bStripLetsDC 64 exp
  let hExpr ← Lean.Elab.Term.elabTerm h none
  let hTy0 := r1bStripLetsDC 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
  for idx in [0, 1, 2, 4, 5, 6] do
    if !(← Lean.Meta.withReducibleAndInstances <| Lean.Meta.isDefEq (hTy0.getArg! idx) (expS.getArg! idx)) then
      discard <| Lean.Meta.isDefEq (hTy0.getArg! idx) (expS.getArg! idx)
  let p ← Lean.instantiateMVars (expS.getArg! 3)
  let p' ← Lean.instantiateMVars ((r1bStripLetsDC 64 (← Lean.instantiateMVars hTy0)).getArg! 3)
  let sepTy := Lean.mkConst ``SepProp []
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let sar := sepSample.getAppNumArgs
  let mkSep (x y : Lean.Expr) : Lean.Expr :=
    sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
  let ps := (r1bSplitSepDC 64 sepSample p).toList
  let p's := (r1bSplitSepDC 64 sepSample p').toList
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
      if !removed && (← r1bIsDefEqPureDC x a) then removed := true
      else next := next.concat x
    if !removed then
      throwError "r1b_call_frame_dc: unmatched callee atom:\n  {a}\nin:\n  {rem}"
    rem := next
  let remProd := match rem.reverse with
    | [] => empExpr
    | last :: rest => rest.foldl (fun acc x => mkSep x acc) last
  if let some mf := mvarFOpt then
    discard <| Lean.Meta.isDefEq mf remProd
  let eqTy ← Lean.Meta.mkEq (← Lean.instantiateMVars p) (← Lean.instantiateMVars p')
  let eqProof ← Lean.Elab.Term.elabTerm (← `(by r1b_ac_dc)) (some eqTy)
  let ent ← Lean.Meta.mkAppM ``Entails.of_eq #[eqProof]
  Lean.Meta.mkAppM ``sepWPp_weaken_pre #[ent, hExpr]


set_option maxHeartbeats 800000 in
/-- `FdsGe3Closed`-threaded second half of Stage 4a (`0x2584 → 0x25f4`): deserializes `kpkKey`, clones `kpkSig` onto the heap, and establishes `readBundleV = some bundle`. -/
theorem r1b_step_kpk_clone_2584_of_kem_placed_fd [LibsignalPlacement] {M : AllocCostModel}
    {S : RunSem} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {sEnvs : RunSlotEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {needs : RunNeeds}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {r0 r1 r2 r3 : BitVec 8}
    {kpkCap kpkPtr spkCap spkPtr regCap regPtr spkSigPtr : BitVec 64}
    {kpkBs kpkKey kpkSig spkBs spkKey spkSig opkBs : List (BitVec 8)}
    {kpkId spkId v11c : BitVec 32}
    {spk : PublicKey}
    {spkW0 : BitVec 64} {spkW8 spkW12 : BitVec 32} {spkW16 spkW24 : BitVec 64}
    {opk : Option (BitVec 32 × PublicKey)}
    {b0 b1 b2 b3 b4 b5 b6 : BitVec 8}
    {w0e0 w0e4 w9 : BitVec 32} {w13 : BitVec 16} {w15 w23 : BitVec 64} {b31 : BitVec 8}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hkem : (slotWithFdsGe3Closed (slotsOfPlaced A lim sEnvs S needs).kemDeserialize).OkPlaced
      (lsProg_579 H) (blkPl_590).base)
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hok : r1b_OkCtxPlacedFd r1b_CodeOk S g d s0 s 0x2584)
    (hreg_rd : cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") =
      .ok [r0, r1, r2, r3])
    (hspk_rd : cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") = .ok spkBs)
    (hspk_sp : splitSigned spkBs = some (spkId, spkKey, spkSig))
    (hspk_d : PublicKey.deserialize spkKey = .ok spk)
    (hspk_bytes : spk.bytes.toList = r1b_spkBytesOf spkW0 spkW8 spkW12 spkW16 spkW24)
    (hspk_ptr : spkSigPtr ≠ 0)
    (hspk_sig : spkSig.length = 64)
    (hkpk_rd : cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "kyber-pre-key") = .ok kpkBs)
    (hkpk_sp : splitSigned kpkBs = some (kpkId, kpkKey, kpkSig))
    (hopk_rd : cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "one-time-pre-key") = .ok opkBs)
    (hopk_sem : (opkBs = [] ∧ opk = none) ∨
      (∃ opkId opkKey opkPk, opkBs ≠ [] ∧ splitId opkBs = some (opkId, opkKey) ∧
        PublicKey.deserialize opkKey = .ok opkPk ∧ opk = some (opkId, opkPk)))
    (hx23 : s.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64)
    (hx24 : s.readReg64 (.gpr 24#5) = runFsp s0 + 0x380#64)
    (hx25 : s.readReg64 (.gpr 25#5) = BitVec.ofNat 64 opkBs.length)
    (hx26 : s.readReg64 (.gpr 26#5) = spkSigPtr)
    (hx27 : s.readReg64 (.gpr 27#5) = spkW12.zeroExtend 64)
    (hx28 : s.readReg64 (.gpr 28#5) = 64#64)
    (hfit_kem : FitsEvents M lim st (kemDeserializeEvents kpkKey))
    (hfit_sig : ∀ kpk, kemPkDeserialize kpkKey = .ok kpk →
      FitsEvents M lim (M.stepEvents (kemDeserializeEvents kpkKey) st) (rustAllocEvents 64 1))
    (hpanic : PanicK g s0 Qp)
    (hrej : ∀ (sf : State) (evs : List AllocEvent),
      R1bKpkCloneErrEnv kpkKey evs →
      AtRejectPlaced r1b_CodeOk g StoresGhost.opened .postDispatch s0 sf →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (rejectMem (A.atState lim (M.stepEvents evs st) sf)
          g StoresGhost.opened .postDispatch s0 resStack)
        Q Qp oom)
    (hk : ∀ (sf : State) (evs_kpk : List AllocEvent) (kpk : List (BitVec 8))
        (kpkSigPtr kpkBuf : BitVec 64),
      R1bKpkCloneOkEnv kpkKey evs_kpk →
      r1b_OkCtxPlacedFd r1b_CodeOk S g d s0 sf 0x25f4 →
      readBundleV (runFiles g.i) d.dir d.peerV.device = some {
        idKey := d.idKey, regId := ofLe32 r0 r1 r2 r3, device := d.peerV.device,
        spkId := spkId, spk := spk, spkSig := spkSig,
        kpkId := kpkId, kpk := kpk, kpkSig := kpkSig, opk := opk
      } →
      spk.bytes.toList = r1b_spkBytesOf spkW0 spkW8 spkW12 spkW16 spkW24 →
      (spkSigPtr ≠ 0 ∧ kpkSigPtr ≠ 0 ∧ kpkBuf ≠ 0) →
      (spkSig.length = 64 ∧ kpkSig.length = 64 ∧ kpk.length = 1568) →
      sf.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64 →
      sf.readReg64 (.gpr 24#5) = runFsp s0 + 0x380#64 →
      sf.readReg64 (.gpr 25#5) = BitVec.ofNat 64 opkBs.length →
      sf.readReg64 (.gpr 27#5) = spkW12.zeroExtend 64 →
      sf.readReg64 (.gpr 28#5) = 64#64 →
      let fsp := runFsp s0
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (memRegion (fsp + 0x4d0#64) 48 ∗
          A.live spkSigPtr 64 1 ∗ (spkSigPtr ↦ₛ spkSig) ∗
          A.live kpkSigPtr 64 1 ∗ (kpkSigPtr ↦ₛ kpkSig) ∗
          A.live kpkBuf 1568 1 ∗ (kpkBuf ↦ₛ kpk) ∗
          ownedBytes A.repAlloc kpkCap kpkPtr (BitVec.ofNat 64 kpkBs.length) kpkBs ∗
          ownedBytes A.repAlloc spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
          ownedBytes A.repAlloc regCap regPtr 4#64 [r0, r1, r2, r3] ∗
          r1b_invCoreBase_placed A.repAlloc g d s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
          ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
          r1b_opkStage1SpkAt fsp spkW0 spkW8 spkW16 spkW24
            b0 b1 b2 b3 b4 b5 b6 w0e0 w0e4 w9 w13 w15 w23 b31 ∗
          ((fsp + 0x110#64) ↦₆₄ spkSigPtr) ∗ ((fsp + 0x11c#64) ↦₃₂ v11c) ∗
          ((fsp + 0x120#64) ↦₆₄ 64#64) ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
          ((fsp + 0x130#64) ↦₆₄ (kpkPtr + 4#64 + BitVec.ofNat 64 kpkKey.length)) ∗
          ((fsp + 0x138#64) ↦₆₄ kpkSigPtr) ∗
          ((fsp + 0x140#64) ↦₆₄ 1568#64) ∗
          ((fsp + 0x148#64) ↦₆₄ 64#64) ∗
          ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗
          ((fsp + 0x158#64) ↦₆₄ 64#64) ∗
          ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
          ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
          ((fsp + 0x178#64) ↦₆₄ kpkBuf) ∗
          ((fsp + 0x188#64) ↦₆₄ spkId.zeroExtend 64) ∗ ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
          ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
          ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
          ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
          memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool lim (M.stepEvents evs_kpk st) sf)
        Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (memRegion (fsp + 0x4d0#64) 24 ∗ memRegion (fsp + 0x4e8#64) 24 ∗
        A.live spkSigPtr 64 1 ∗ (spkSigPtr ↦ₛ spkSig) ∗
        ownedBytes A.repAlloc kpkCap kpkPtr (BitVec.ofNat 64 kpkBs.length) kpkBs ∗
        ownedBytes A.repAlloc spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
        ownedBytes A.repAlloc regCap regPtr 4#64 [r0, r1, r2, r3] ∗
        r1b_invCoreBase_placed A.repAlloc g d s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
        r1b_opkStage1SpkAt fsp spkW0 spkW8 spkW16 spkW24
          b0 b1 b2 b3 b4 b5 b6 w0e0 w0e4 w9 w13 w15 w23 b31 ∗
        memRegion (fsp + 0x110#64) 8 ∗ ((fsp + 0x11c#64) ↦₃₂ v11c) ∗
        ((fsp + 0x120#64) ↦₆₄ 64#64) ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
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
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s)
      Q Qp oom := by
  intro fsp
  let _ := hx23; let _ := hx24; let _ := hx25; let _ := hx26; let _ := hx27; let _ := hx28
  have hst := hok.st
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hst.spAligned
  have hal138 : (fsp + 0x138#64) &&& 7#64 = 0#64 := by bv_bits
  have hal130 : (fsp + 0x130#64) &&& 7#64 = 0#64 := by bv_bits
  let _ := hal; let _ := hal138; let _ := hal130
  have ⟨hkpk_cat, hkpk_t4, hkpk_sig_len, _⟩ := r1b_splitSigned_bytes hkpk_sp
  rw [ProofLib.memRegion_eight (fsp + 0x110#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun v110_in => ?_
  refine r1b_sepWPp_frame_dc (by r1b_ac_dc)
    (Entails.of_eq (r1b_ownedBytes_borrow A.repAlloc kpkCap kpkPtr (BitVec.ofNat 64 kpkBs.length) kpkBs))
    (by r1b_ac_dc) ?_
  simp only [sepConj_assoc]
  refine r1b_sepWPp_pure_left fun ⟨_, hkpk_le, hkpk_cap63, hkpk_ne⟩ => ?_
  have hkpk_key63 : kpkKey.length < 2 ^ 63 := by omega
  rw [r1b_splitSigned_slice_eq (ptr := kpkPtr) hkpk_cat hkpk_t4]
  simp only [sepConj_assoc]
  have hpc := hst.pc; change s.pc = (blkPl_579).base + 9604#64 at hpc
  have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
  apply r1b_seq_lscro_oom (mid := lsmpl.base 590) hst.inv
  dsimp only [runProgPlaced, lsProg_579]
  apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
    blkLib_eq_579 blk579_noSvc0 (mid := lsmpl.base 590)
  intro _m_strip; wp_steps
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
    (by simp only [wp_norm, arm64_norm, *]) fun _m_real hnsp => ?_
  have hvmp : VmPreserved s _ :=
    hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
  try simp only [State.setMem_setMem] at hvmp ⊢
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
  clear hpc hrun hsp
  refine r1b_bind_state_placed fun sm1 hsm1 hinv1 => by
    have hvm1 : VmPreserved s sm1 := hsm1 ▸ hvmp
    rw [← A.pool_transport lim st s sm1 hvm1]
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    try rw [hx26]
    have hfds1 : FdsGe3Closed sm1.fs := by
      simpa only [hsm1, wp_norm, arm64_norm] using hok.fds
    refine r1b_call_frame_dc <|
      r1b_call_kemDeserialize_of_kem_placed_fd hh hkem hbnd hinv1 hfds1
        (by simp only [hsm1, wp_norm, arm64_norm])
        (by simp only [hsm1, wp_norm, arm64_norm, hst.run])
        (by simpa only [hsm1, wp_norm, arm64_norm] using hst.sp)
        (by simpa only [hsm1, wp_norm, arm64_norm] using hst.fp)
        (by simpa only [calleeSavedVRegs, hsm1, wp_norm, arm64_norm] using hst.vregs)
        hst.spAligned (retOff := 0x2594)
        (by simp only [hsm1, wp_norm, arm64_norm])
        (r := fsp + 0x4d0#64) (p := kpkPtr + 4#64) (bs := kpkKey)
        (by simp only [hsm1, wp_norm, arm64_norm])
        (by simp only [hsm1, wp_norm, arm64_norm])
        (by simp only [hsm1, wp_norm, arm64_norm])
        hkpk_key63 hfit_kem hpanic
        (fun sf1 hin1 hcs1 hfds_sf1 hfs1 htr1 => ?_)
    have hok1 : r1b_OkCtxPlacedFd r1b_CodeOk S g d s0 sf1 0x2594 := hok.after_call_fds
      (by simp only [hsm1, wp_norm, arm64_norm]) (by simp only [hsm1, wp_norm, arm64_norm])
      (by simp only [hsm1, wp_norm, arm64_norm]) (by simp only [hsm1, wp_norm, arm64_norm])
      (by simp only [hsm1, wp_norm, arm64_norm]) (by simp only [hsm1, wp_norm, arm64_norm])
      hin1 hcs1 hfs1 htr1 hfds_sf1
    have hx23_1 : sf1.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64 :=
      hcs1.2.2.2.2.1.trans
        (by solve | simp only [hsm1, wp_norm, arm64_norm] | simpa only [hsm1, wp_norm, arm64_norm] using hx23)
    have hx24_1 : sf1.readReg64 (.gpr 24#5) = runFsp s0 + 0x380#64 :=
      hcs1.2.2.2.2.2.1.trans
        (by solve | simp only [hsm1, wp_norm, arm64_norm] | simpa only [hsm1, wp_norm, arm64_norm] using hx24)
    have hx25_1 : sf1.readReg64 (.gpr 25#5) = BitVec.ofNat 64 opkBs.length :=
      hcs1.2.2.2.2.2.2.1.trans
        (by solve | simp only [hsm1, wp_norm, arm64_norm] | simpa only [hsm1, wp_norm, arm64_norm] using hx25)
    have hx27_1 : sf1.readReg64 (.gpr 27#5) = spkW12.zeroExtend 64 :=
      hcs1.2.2.2.2.2.2.2.2.1.trans
        (by solve | simp only [hsm1, wp_norm, arm64_norm] | simpa only [hsm1, wp_norm, arm64_norm] using hx27)
    have hx28_1 : sf1.readReg64 (.gpr 28#5) = 64#64 :=
      hcs1.2.2.2.2.2.2.2.2.2.1.trans
        (by solve | simp only [hsm1, wp_norm, arm64_norm] | simpa only [hsm1, wp_norm, arm64_norm] using hx28)
    let _ := hx23_1; let _ := hx24_1; let _ := hx25_1; let _ := hx27_1; let _ := hx28_1
    have hkpk_rejoin :
        ((kpkPtr ↦ₛ kpkBs.take 4) ∗ ((kpkPtr + 4#64) ↦ₛ kpkKey) ∗
          ((kpkPtr + 4#64 + BitVec.ofNat 64 kpkKey.length) ↦ₛ kpkSig) ∗
          r1b_ownedRest A.repAlloc kpkCap kpkPtr kpkBs.length) ⊢
        ownedBytes A.repAlloc kpkCap kpkPtr (BitVec.ofNat 64 kpkBs.length) kpkBs := by
      refine Entails.trans (r1b_entails_frame_dc (by r1b_ac_dc)
        (Entails.of_eq (r1b_splitSigned_slice_eq (ptr := kpkPtr) hkpk_cat hkpk_t4).symm) (by r1b_ac_dc)) ?_
      exact r1b_ownedBytes_rejoin A.repAlloc kpkCap kpkPtr kpkBs hkpk_le hkpk_cap63 hkpk_ne
    cases hkpk_d : kemPkDeserialize kpkKey with
    | noKeyType =>
      have hc1 := hok1.to_err
        (r1b_none_kpk_deser hkpk_rd hkpk_sp fun _ h => by rw [hkpk_d] at h; cases h)
      dsimp only [kemDeserResAt]
      refine r1b_sepWPp_frame_dc (by r1b_ac_dc) hkpk_rejoin (by r1b_ac_dc) ?_
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      rw [r1b_split_region fsp 0x4d8 8 8,
        ProofLib.memRegion_eight (fsp + 0x4d8#64),
        ProofLib.memRegion_eight (fsp + 0x4e0#64)]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPp.exists_elim fun w4d8 => SepWPp.exists_elim fun w4e0 => ?_
      dsimp only [speWord]
      have hpc := hin1.pc; change sf1.pc = (blkPl_579).base + 9620#64 at hpc
      have hrun := hin1.run; have hsp : sf1.sp = fsp := hin1.sp
      apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 9812#64) hin1.inv
      dsimp only [runProgPlaced, lsProg_579]
      apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
        blkLib_eq_579 blk579_noSvc0 (mid := (blkPl_579).base + 9812#64)
      intro _m_strip; wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *]) fun _m_real hnsp => ?_
      have hvmp : VmPreserved sf1 _ :=
        hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
      try simp only [State.setMem_setMem] at hvmp ⊢
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
      clear hpc hrun hsp
      refine r1b_bind_state_placed fun sm2 hsm2 hinv2 => by
        have hvm2 : VmPreserved sf1 sm2 := hsm2 ▸ hvmp
        rw [← A.pool_transport lim (M.stepEvents (kemDeserializeEvents kpkKey) st) sf1 sm2 hvm2]
        change SepWPp (runProgPlaced H) _ _ _ _ _ _
        have hc2 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm2 0x2654 := hc1.of_step
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
        exact sepWPp_weaken_pre (Entails.of_eq (by dsimp only [speWord]; r1b_ac_dc))
          (r1b_kem_err_2654_placed (i := 7) hh hdrop hbnd hc2 (by decide) hspk_ptr hspk_sig hpanic
            fun sf_r evsFree hfo hrej_r => by
              have hst_eq : M.stepEvents evsFree (M.stepEvents (kemDeserializeEvents kpkKey) st) =
                  M.stepEvents (kemDeserializeEvents kpkKey ++ evsFree) st :=
                (M.stepEvents_append _ _ _).symm
              rw [hst_eq]
              exact hrej sf_r _ (by unfold R1bKpkCloneErrEnv; rw [hkpk_d]; exact Or.inr ⟨_, _, rfl, rfl, hfo⟩) hrej_r)
    | badType t =>
      have hc1 := hok1.to_err
        (r1b_none_kpk_deser hkpk_rd hkpk_sp fun _ h => by rw [hkpk_d] at h; cases h)
      dsimp only [kemDeserResAt]
      have h4d8 : ((fsp + 0x4d0#64 + 8#64) ↦₈ t) ∗ memRegion (fsp + 0x4d0#64 + 9#64) 15 ⊢
          memRegion (fsp + 0x4d8#64) 16 := by
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        refine Entails.trans (sepConj_mono_left (r1b_cell8_to_region _ _)) ?_
        rw [r1b_join_region fsp 0x4d8 1 15]; exact Entails.refl _
      refine r1b_sepWPp_frame_dc (by r1b_ac_dc) (sepConj_mono hkpk_rejoin h4d8) (by r1b_ac_dc) ?_
      rw [r1b_split_region fsp 0x4d8 8 8,
        ProofLib.memRegion_eight (fsp + 0x4d8#64),
        ProofLib.memRegion_eight (fsp + 0x4e0#64)]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, sepConj_assoc]
      refine SepWPp.exists_elim fun w4d8 => SepWPp.exists_elim fun w4e0 => ?_
      dsimp only [speWord]
      have hpc := hin1.pc; change sf1.pc = (blkPl_579).base + 9620#64 at hpc
      have hrun := hin1.run; have hsp : sf1.sp = fsp := hin1.sp
      apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 9812#64) hin1.inv
      dsimp only [runProgPlaced, lsProg_579]
      apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
        blkLib_eq_579 blk579_noSvc0 (mid := (blkPl_579).base + 9812#64)
      intro _m_strip; wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *]) fun _m_real hnsp => ?_
      have hvmp : VmPreserved sf1 _ :=
        hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
      try simp only [State.setMem_setMem] at hvmp ⊢
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
      clear hpc hrun hsp
      refine r1b_bind_state_placed fun sm2 hsm2 hinv2 => by
        have hvm2 : VmPreserved sf1 sm2 := hsm2 ▸ hvmp
        rw [← A.pool_transport lim (M.stepEvents (kemDeserializeEvents kpkKey) st) sf1 sm2 hvm2]
        change SepWPp (runProgPlaced H) _ _ _ _ _ _
        have hc2 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm2 0x2654 := hc1.of_step
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
        exact sepWPp_weaken_pre (Entails.of_eq (by dsimp only [speWord]; r1b_ac_dc))
          (r1b_kem_err_2654_placed (i := 31) hh hdrop hbnd hc2 (by decide) hspk_ptr hspk_sig hpanic
            fun sf_r evsFree hfo hrej_r => by
              have hst_eq : M.stepEvents evsFree (M.stepEvents (kemDeserializeEvents kpkKey) st) =
                  M.stepEvents (kemDeserializeEvents kpkKey ++ evsFree) st :=
                (M.stepEvents_append _ _ _).symm
              rw [hst_eq]
              exact hrej sf_r _ (by unfold R1bKpkCloneErrEnv; rw [hkpk_d]; exact Or.inr ⟨_, _, rfl, rfl, hfo⟩) hrej_r)
    | badLength n =>
      have hc1 := hok1.to_err
        (r1b_none_kpk_deser hkpk_rd hkpk_sp fun _ h => by rw [hkpk_d] at h; cases h)
      dsimp only [kemDeserResAt]
      refine r1b_sepWPp_frame_dc (by r1b_ac_dc) hkpk_rejoin (by r1b_ac_dc) ?_
      rw [show fsp + 0x4d0#64 + 16#64 = fsp + 0x4e0#64 from by bv_omega,
        ProofLib.memRegion_eight (fsp + 0x4e0#64)]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc,
        BitVec.reduceAdd]
      refine SepWPp.exists_elim fun w4e0 => ?_
      dsimp only [speWord]
      have hpc := hin1.pc; change sf1.pc = (blkPl_579).base + 9620#64 at hpc
      have hrun := hin1.run; have hsp : sf1.sp = fsp := hin1.sp
      apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 9812#64) hin1.inv
      dsimp only [runProgPlaced, lsProg_579]
      apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
        blkLib_eq_579 blk579_noSvc0 (mid := (blkPl_579).base + 9812#64)
      intro _m_strip; wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *]) fun _m_real hnsp => ?_
      have hvmp : VmPreserved sf1 _ :=
        hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
      try simp only [State.setMem_setMem] at hvmp ⊢
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
      clear hpc hrun hsp
      refine r1b_bind_state_placed fun sm2 hsm2 hinv2 => by
        have hvm2 : VmPreserved sf1 sm2 := hsm2 ▸ hvmp
        rw [← A.pool_transport lim (M.stepEvents (kemDeserializeEvents kpkKey) st) sf1 sm2 hvm2]
        change SepWPp (runProgPlaced H) _ _ _ _ _ _
        have hc2 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm2 0x2654 := hc1.of_step
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
        exact sepWPp_weaken_pre (Entails.of_eq (by dsimp only [speWord]; r1b_ac_dc))
          (r1b_kem_err_2654_placed (i := 33) hh hdrop hbnd hc2 (by decide) hspk_ptr hspk_sig hpanic
            fun sf_r evsFree hfo hrej_r => by
              have hst_eq : M.stepEvents evsFree (M.stepEvents (kemDeserializeEvents kpkKey) st) =
                  M.stepEvents (kemDeserializeEvents kpkKey ++ evsFree) st :=
                (M.stepEvents_append _ _ _).symm
              rw [hst_eq]
              exact hrej sf_r _ (by unfold R1bKpkCloneErrEnv; rw [hkpk_d]; exact Or.inr ⟨_, _, rfl, rfl, hfo⟩) hrej_r)
    | ok kpk =>
      have hbundle := r1b_readBundleV_some (dev := d.peerV.device) hok.ikSem hreg_rd hspk_rd hspk_sp
        hkpk_rd hkpk_sp hopk_rd hopk_sem hspk_d hkpk_d
      have h1568 : kpk.length = 1568 := (readBundleV_slice_lengths hbundle).2.2
      dsimp only [kemDeserResAt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc,
        BitVec.reduceAdd, sepConj_assoc]
      refine SepWPp.exists_elim fun kpkBuf => ?_
      refine r1b_sepWPp_frame_dc (by r1b_ac_dc)
        (r1b_box1568_unpack A.repAlloc (fsp + 0x4d8#64) kpkBuf kpk h1568) (by r1b_ac_dc) ?_
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      refine sepWPp_weaken_pre (Entails.of_eq (by r1b_ac_dc))
        (r1b_sepWPp_pure_left (φ := kpkBuf ≠ 0) fun hkpk_buf => ?_)
      have hpc := hin1.pc; change sf1.pc = (blkPl_579).base + 9620#64 at hpc
      have hrun := hin1.run; have hsp : sf1.sp = fsp := hin1.sp
      apply r1b_seq_lscro_oom (mid := lsmpl.base 588) hin1.inv
      dsimp only [runProgPlaced, lsProg_579]
      apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
        blkLib_eq_579 blk579_noSvc0 (mid := lsmpl.base 588)
      intro _m_strip; wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *]) fun _m_real hnsp => ?_
      have hvmp : VmPreserved sf1 _ :=
        hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
      try simp only [State.setMem_setMem] at hvmp ⊢
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
      clear hpc hrun hsp
      refine r1b_bind_state_placed fun sm2 hsm2 hinv2 => by
        have hvm2 : VmPreserved sf1 sm2 := hsm2 ▸ hvmp
        rw [← A.pool_transport lim (M.stepEvents (kemDeserializeEvents kpkKey) st) sf1 sm2 hvm2]
        change SepWPp (runProgPlaced H) _ _ _ _ _ _
        have h4d0_24 :
            ((fsp + 0x4d0#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
              ((fsp + 0x4d8#64) ↦₆₄ kpkBuf) ∗ ((fsp + 0x4e0#64) ↦₆₄ 1568#64) ⊢
              memRegion (fsp + 0x4d0#64) 24 := by
          refine Entails.trans (sepConj_mono_right (by
            simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
              r1b_cells2_to_region16 (fsp + 0x4d8#64) kpkBuf 1568#64)) ?_
          simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
            r1b_cell64_cons (a := fsp + 0x4d0#64) 0xfffffffffffffffe#64 (n := 16) (by decide)
        refine r1b_sepWPp_frame_dc (by r1b_ac_dc) h4d0_24 (by r1b_ac_dc) ?_
        refine r1b_call_frame_dc <|
          r1b_call_tryAlloc_placed (g := g) hh hbnd hinv2
            (by simp only [hsm2, wp_norm, arm64_norm])
            (by simp only [hsm2, wp_norm, arm64_norm, hin1.run])
            (by simpa only [hsm2, wp_norm, arm64_norm] using hin1.sp)
            (by simpa only [hsm2, wp_norm, arm64_norm] using hin1.fp)
            (by simpa only [calleeSavedVRegs, hsm2, wp_norm, arm64_norm] using hin1.vregs)
            hst.spAligned (retOff := 0x25c8)
            (by simp only [hsm2, wp_norm, arm64_norm])
            (out := fsp + 0x4d0#64) (new := 64#64) (align := 1#64) (stride := 1#64)
            (by simp only [hsm2, wp_norm, arm64_norm])
            (by simp only [hsm2, wp_norm, arm64_norm])
            (by simp only [hsm2, wp_norm, arm64_norm])
            (by simp only [hsm2, wp_norm, arm64_norm])
            (by decide) (by decide) (r1b_layout1 64)
            (by decide)
            (fun evs (hevs : evs = rustAllocEvents 64 1) => hevs ▸ hfit_sig kpk hkpk_d)
            hpanic
            (fun sf2 evs_sig kpkSigPtr hevs_sig hin2 hcs2 hkpk_ptr _ hfs2 htr2 => ?_)
        have hevs_sig_eq : evs_sig = rustAllocEvents 64 1 := hevs_sig
        subst hevs_sig_eq
        have hok2 : r1b_OkCtxPlacedFd r1b_CodeOk S g d s0 sf2 0x25c8 := hok1.after_call
          (by simp only [hsm2, wp_norm, arm64_norm]) (by simp only [hsm2, wp_norm, arm64_norm])
          (by simp only [hsm2, wp_norm, arm64_norm]) (by simp only [hsm2, wp_norm, arm64_norm])
          (by simp only [hsm2, wp_norm, arm64_norm]) (by simp only [hsm2, wp_norm, arm64_norm])
          hin2 hcs2 hfs2 htr2
        have hx23_2 : sf2.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64 :=
          hcs2.2.2.2.2.1.trans
            (by solve | simp only [hsm2, wp_norm, arm64_norm] | simpa only [hsm2, wp_norm, arm64_norm] using hx23_1)
        have hx24_2 : sf2.readReg64 (.gpr 24#5) = runFsp s0 + 0x380#64 :=
          hcs2.2.2.2.2.2.1.trans
            (by solve | simp only [hsm2, wp_norm, arm64_norm] | simpa only [hsm2, wp_norm, arm64_norm] using hx24_1)
        have hx25_2 : sf2.readReg64 (.gpr 25#5) = BitVec.ofNat 64 opkBs.length :=
          hcs2.2.2.2.2.2.2.1.trans
            (by solve | simp only [hsm2, wp_norm, arm64_norm] | simpa only [hsm2, wp_norm, arm64_norm] using hx25_1)
        have hx27_2 : sf2.readReg64 (.gpr 27#5) = spkW12.zeroExtend 64 :=
          hcs2.2.2.2.2.2.2.2.2.1.trans
            (by solve | simp only [hsm2, wp_norm, arm64_norm] | simpa only [hsm2, wp_norm, arm64_norm] using hx27_1)
        have hx28_2 : sf2.readReg64 (.gpr 28#5) = 64#64 :=
          hcs2.2.2.2.2.2.2.2.2.2.1.trans
            (by solve | simp only [hsm2, wp_norm, arm64_norm] | simpa only [hsm2, wp_norm, arm64_norm] using hx28_1)
        let _ := hx23_2; let _ := hx24_2; let _ := hx25_2; let _ := hx27_2; let _ := hx28_2
        simp only [Nat.reduceMul, Nat.reducePow, BitVec.toNat_ofNat, Nat.reduceMod,
          BitVec.add_assoc, BitVec.reduceAdd]
        have hpc := hin2.pc; change sf2.pc = (blkPl_579).base + 9672#64 at hpc
        have hrun := hin2.run; have hsp : sf2.sp = fsp := hin2.sp
        apply r1b_seq_lscro_oom (mid := lsρ lsMemcpySym) hin2.inv
        dsimp only [runProgPlaced, lsProg_579]
        apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
          blkLib_eq_579 blk579_noSvc0 (mid := lsρ lsMemcpySym)
        intro _m_strip; wp_steps
        refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
          (by simp only [wp_norm, arm64_norm, *]) fun _m_real hnsp => ?_
        have hvmp : VmPreserved sf2 _ :=
          hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
        try simp only [State.setMem_setMem] at hvmp ⊢
        apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
        clear hpc hrun hsp
        refine r1b_bind_state_placed fun sm3 hsm3 hinv3 => by
          have hvm3 : VmPreserved sf2 sm3 := hsm3 ▸ hvmp
          rw [← A.pool_transport lim
            (M.stepEvents (rustAllocEvents 64 1) (M.stepEvents (kemDeserializeEvents kpkKey) st))
            sf2 sm3 hvm3]
          change SepWPp (runProgPlaced H) _ _ _ _ _ _
          rw [show memRegion kpkSigPtr 64 = memRegion kpkSigPtr kpkSig.length from by rw [hkpk_sig_len]]
          refine r1b_call_frame_dc <|
            r1b_call_memcpy_region_pool_placed (g := g) hh hbnd hinv3
              (by simp only [hsm3, wp_norm, arm64_norm])
              (by simp only [hsm3, wp_norm, arm64_norm, hin2.run])
              (by simpa only [hsm3, wp_norm, arm64_norm] using hin2.sp)
              (by simpa only [hsm3, wp_norm, arm64_norm] using hin2.fp)
              (by simpa only [calleeSavedVRegs, hsm3, wp_norm, arm64_norm] using hin2.vregs)
              hst.spAligned (retOff := 0x25f4)
              (by simp only [hsm3, wp_norm, arm64_norm])
              (dst := kpkSigPtr) (src := kpkPtr + (4#64 + BitVec.ofNat 64 kpkKey.length)) (bs := kpkSig)
              (by simp only [hsm3, wp_norm, arm64_norm])
              (by simp only [hsm3, wp_norm, arm64_norm])
              (by simp only [hsm3, wp_norm, arm64_norm, hkpk_sig_len]; try rw [hx28_2])
              hpanic
              (fun sf3 hin3 hcs3 _ hfs3 htr3 => ?_)
          have hok3 : r1b_OkCtxPlacedFd r1b_CodeOk S g d s0 sf3 0x25f4 := hok2.after_call
            (by simp only [hsm3, wp_norm, arm64_norm]) (by simp only [hsm3, wp_norm, arm64_norm])
            (by simp only [hsm3, wp_norm, arm64_norm]) (by simp only [hsm3, wp_norm, arm64_norm])
            (by simp only [hsm3, wp_norm, arm64_norm]) (by simp only [hsm3, wp_norm, arm64_norm])
            hin3 hcs3 hfs3 htr3
          have h4d0_48 :
              ((fsp + 0x4d0#64) ↦₆₄ 0#64) ∗ ((fsp + 0x4d8#64) ↦₆₄ 64#64) ∗
                ((fsp + 0x4e0#64) ↦₆₄ kpkSigPtr) ∗ memRegion (fsp + 0x4e8#64) 24 ⊢
                memRegion (fsp + 0x4d0#64) 48 := by
            have h24 :
                ((fsp + 0x4d0#64) ↦₆₄ 0#64) ∗ ((fsp + 0x4d8#64) ↦₆₄ 64#64) ∗
                  ((fsp + 0x4e0#64) ↦₆₄ kpkSigPtr) ⊢ memRegion (fsp + 0x4d0#64) 24 := by
              refine Entails.trans (sepConj_mono_right (by
                simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
                  r1b_cells2_to_region16 (fsp + 0x4d8#64) 64#64 kpkSigPtr)) ?_
              simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
                r1b_cell64_cons (a := fsp + 0x4d0#64) 0#64 (n := 16) (by decide)
            refine Entails.trans (Entails.of_eq (show _ =
                (((fsp + 0x4d0#64) ↦₆₄ 0#64) ∗ ((fsp + 0x4d8#64) ↦₆₄ 64#64) ∗
                  ((fsp + 0x4e0#64) ↦₆₄ kpkSigPtr)) ∗ memRegion (fsp + 0x4e8#64) 24 by r1b_ac_dc))
              (Entails.trans (sepConj_mono_left h24) ?_)
            rw [r1b_join_region fsp 0x4d0 24 24]; exact Entails.refl _
          have hst_ok :
              M.stepEvents (rustAllocEvents 64 1) (M.stepEvents (kemDeserializeEvents kpkKey) st) =
                M.stepEvents (kemDeserializeEvents kpkKey ++ rustAllocEvents 64 1) st :=
            (M.stepEvents_append _ _ _).symm
          rw [hst_ok, show kpkPtr + (4#64 + BitVec.ofNat 64 kpkKey.length) =
            kpkPtr + 4#64 + BitVec.ofNat 64 kpkKey.length from (BitVec.add_assoc _ _ _).symm]
          refine r1b_sepWPp_frame_dc (by r1b_ac_dc) (sepConj_mono hkpk_rejoin h4d0_48) (by r1b_ac_dc) ?_
          exact sepWPp_weaken_pre (Entails.of_eq (by r1b_ac_dc))
            (hk sf3 (kemDeserializeEvents kpkKey ++ rustAllocEvents 64 1) kpk kpkSigPtr kpkBuf
              rfl hok3 hbundle hspk_bytes
              ⟨hspk_ptr, hkpk_ptr, hkpk_buf⟩
              ⟨hspk_sig, hkpk_sig_len, h1568⟩
              (hcs3.2.2.2.2.1.trans
                (by solve | simp only [hsm3, wp_norm, arm64_norm] | simpa only [hsm3, wp_norm, arm64_norm] using hx23_2))
              (hcs3.2.2.2.2.2.1.trans
                (by solve | simp only [hsm3, wp_norm, arm64_norm] | simpa only [hsm3, wp_norm, arm64_norm] using hx24_2))
              (hcs3.2.2.2.2.2.2.1.trans
                (by solve | simp only [hsm3, wp_norm, arm64_norm] | simpa only [hsm3, wp_norm, arm64_norm] using hx25_2))
              (hcs3.2.2.2.2.2.2.2.2.1.trans
                (by solve | simp only [hsm3, wp_norm, arm64_norm] | simpa only [hsm3, wp_norm, arm64_norm] using hx27_2))
              (hcs3.2.2.2.2.2.2.2.2.2.1.trans
                (by solve | simp only [hsm3, wp_norm, arm64_norm] | simpa only [hsm3, wp_norm, arm64_norm] using hx28_2)))


end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.DeserClonePlacedBudgetAuxFd
