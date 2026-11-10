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
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadKpkPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1bProofPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.BV.Bits
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEq
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Base
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSites
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpkPlacedBudgetAux
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq

/-!
# Budget-Threaded Final Bundle Assembly for Arm `R1b` (`0x27bc → 0x28f0`)

Proves `r1b_step_init2_27bc_placed_aux` on Block `579` (`signal_session::run`), assembling
`cliBundleAt` and `protocolAddressAt` to establish `AtInit2Placed` under `RustCliAllocBudget M`
with `VmPreserved` pool transport.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1bProofPlacedBudgetAux

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (PublicKey)
open CryptoVerification (LibsignalHooks LibsignalPlacement lsLogFilterAddr)
open CryptoVerification.LibsignalTripleRatchet.Wire
  (pkBytesOf pkLayoutAt pkLayoutAt_entails_memRegion32 pkLayoutAt_eq_pointsToBytes
   pkRestAt sevenBytesHeadAt sevenBytesHeadAt_eq_tailAt sevenBytesTailAt)
open CryptoVerification.LibsignalTripleRatchetRepr (protocolAddressAt)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession.Cli (StoresGhost cliIdentityVtSym cliSessionVtSym ofLe32)
open CryptoVerification.SignalSession.Cli.MainHops
  (RunCall coinsInstalledPlaced coinsOf inputOf ownedBytes runResSize sepWPp_weaken_pre storesAt)
open CryptoVerification.SignalSession.Cli.Run.Placed (blkLib_eq_579 blkPC_579 blkPl_579 lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (AtInit2Placed BundleV Init1Data Init2Data RunSem Words32Eq addrNameHeap cliBundleAt
   idVtPlaced init2Cells protocolAddressAt_eq_parts r1b_CodeOk r1b_OkCtxPlaced
   r1b_addrUpperAt_to_words r1b_bind_state_placed r1b_cell8_to_region r1b_cells2_to_region16
   r1b_entails_frame_core r1b_fsp_align r1b_head7_to_region r1b_invCoreBase_placed
   r1b_join_region r1b_opkStage3At r1b_region16_to_cells r1b_region48_to_cells
   r1b_sepWPp_frame_core r1b_sepWPp_pure_left r1b_spkBytesOf r1b_spk_pack_words
   r1b_split_region r1b_tail7_init r1b_words_to_addrUpperAt readBundleV runFiles runFsp
   runLocalBytes runLocals runLocalsFrom runPcPlaced_eq runProgPlaced runSaved sessVtPlaced)
open CryptoVerification.SignalSession.Cli.RunSkeleton (runFrame)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadKpkPlacedBudgetAux
  (r1b_seq_lscro_oom)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpkPlacedBudgetAux
  (blk579_noSvc0)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedBudget (init2MemPlaced)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local simp, local arm64_norm, local wp_norm] runPcPlaced_eq BitVec.ofNat_eq_ofNat

private theorem r1b_exR_64 (a v : BitVec 64) {α : Type} (Q : α → SepProp) :
    ((a ↦₆₄ v) ∗ ∃∗ y, Q y) = (∃∗ y, (a ↦₆₄ v) ∗ Q y) := sepExists_sepConj_right _ _
private theorem r1b_exR_32 (a : BitVec 64) (v : BitVec 32) {α : Type} (Q : α → SepProp) :
    ((a ↦₃₂ v) ∗ ∃∗ y, Q y) = (∃∗ y, (a ↦₃₂ v) ∗ Q y) := sepExists_sepConj_right _ _
private theorem r1b_exR_16 (a : BitVec 64) (v : BitVec 16) {α : Type} (Q : α → SepProp) :
    ((a ↦₁₆ v) ∗ ∃∗ y, Q y) = (∃∗ y, (a ↦₁₆ v) ∗ Q y) := sepExists_sepConj_right _ _
private theorem r1b_exR_8 (a : BitVec 64) (v : BitVec 8) {α : Type} (Q : α → SepProp) :
    ((a ↦₈ v) ∗ ∃∗ y, Q y) = (∃∗ y, (a ↦₈ v) ∗ Q y) := sepExists_sepConj_right _ _
private theorem r1b_exR_reg (a : BitVec 64) (n : Nat) {α : Type} (Q : α → SepProp) :
    (memRegion a n ∗ ∃∗ y, Q y) = (∃∗ y, memRegion a n ∗ Q y) := sepExists_sepConj_right _ _

private theorem r1b_sepWPp_exists_left {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {P : α → SepProp} {R : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hk : ∀ x : α, SepWPp prog ret s (P x ∗ R) Q Qp oom) :
    SepWPp prog ret s ((∃∗ x, P x) ∗ R) Q Qp oom := by
  rw [sepExists_sepConj_left]; exact SepWPp.exists_elim hk

private theorem r1b_sp_add (sp a b : BitVec 64) : (sp - a) + b = sp - (a - b) := by bv_omega
private theorem r1b_trunc32_zext64 (x : BitVec 32) : (x.zeroExtend 64).truncate 32 = x := by bv_bits
private theorem r1b_trunc8_zext64_32 (x : BitVec 32) :
    (x.zeroExtend 64).truncate 8 = x.truncate 8 := by bv_bits
private theorem r1b_trunc8_zext64_8 (x : BitVec 8) : (x.zeroExtend 64).truncate 8 = x := by bv_bits
private theorem r1b_trunc8_zext64_zext32_8 (x : BitVec 8) :
    ((x.zeroExtend 32).zeroExtend 64).truncate 8 = x := by bv_bits
private theorem r1b_trunc16_zext64 (x : BitVec 16) : (x.zeroExtend 64).truncate 16 = x := by bv_bits
private theorem r1b_trunc16_zext64_zext32 (x : BitVec 16) :
    ((x.zeroExtend 32).zeroExtend 64).truncate 16 = x := by bv_bits
private theorem r1b_fold_ite_trunc8 (b : Bool) :
    (if b = true then (1#8 : BitVec 8) else 0#8) =
      (if b = true then (1#32 : BitVec 32) else 0#32).truncate 8 := by
  cases b <;> rfl
private theorem r1b_bv128_truncate_append (hi lo : BitVec 64) :
    BitVec.truncate 64 (hi ++ lo) = lo := by bv_bits
private theorem r1b_bv128_extractLsb'_append (hi lo : BitVec 64) :
    BitVec.extractLsb' 64 64 (hi ++ lo) = hi := by bv_bits

private theorem init2MemPlaced_atState_eq [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (g : RunCall) (d : Init2Data) (s0 : State) (resStack : Nat) :
    init2MemPlaced A lim st g d s0 s resStack =
      let fsp := runFsp s0
      memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        coinsInstalledPlaced g.coins (coinsOf g.i) ∗
        tokenInitPlacedAt ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        A.live d.spkSigPtr 64 1 ∗ A.live d.kpkSigPtr 64 1 ∗ A.live d.kpkPtr 1568 1 ∗
        ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
        runSaved s0 ∗ runLocals fsp (init2Cells A.repAlloc fsp d) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s := rfl

private def r1b_init2Frozen_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (g : RunCall) (d : Init1Data) (s0 : State) (fsp : BitVec 64) (resStack : Nat)
    (spkSigPtr kpkSigPtr kpkBuf : BitVec 64)
    (spkSig kpkSig kpk : List (BitVec 8)) : SepProp :=
  A.live spkSigPtr 64 1 ∗ (spkSigPtr ↦ₛ spkSig) ∗
    A.live kpkSigPtr 64 1 ∗ (kpkSigPtr ↦ₛ kpkSig) ∗
    A.live kpkBuf 1568 1 ∗ (kpkBuf ↦ₛ kpk) ∗
    memRegion g.res runResSize ∗ memRegion g.call 56 ∗
    storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
    coinsInstalledPlaced g.coins (coinsOf g.i) ∗
    tokenInitPlacedAt ∗
    addrNameHeap A.repAlloc d.meG ∗ runSaved s0 ∗
    protocolAddressAt A.repAlloc d.peerG (fsp + 0x2a0#64) ∗
    (lsLogFilterAddr ↦₆₄ 0#64) ∗
    ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
    stackAt fsp (resStack - runFrame) ∗ A.pool lim st s

private def r1b_init2RegsFrozen (fsp : BitVec 64) : SepProp :=
  memRegion (fsp + 0x004#64) 0x0dc ∗ memRegion (fsp + 0x1b4#64) 4 ∗
    memRegion (fsp + 0x1d0#64) 0x18 ∗ memRegion (fsp + 0x1f1#64) 7 ∗
    memRegion (fsp + 0x1fe#64) 2 ∗ memRegion (fsp + 0x207#64) 0x19 ∗
    memRegion (fsp + 0x220#64) 0x40 ∗ memRegion (fsp + 0x2c0#64) 0x60 ∗
    memRegion (fsp + 0x340#64) 0x190 ∗ memRegion (fsp + 0x50c#64) 4 ∗
    memRegion (fsp + 0x53c#64) 4 ∗ memRegion (fsp + 0x58e#64) 2 ∗
    memRegion (fsp + 0x590#64) 0x11c0 ∗ memRegion (fsp + 0x1750#64) 24

private meta def r1bStripLetsTop : Nat → Lean.Expr → Lean.Expr
  | 0, e => e
  | n + 1, .letE _ _ v b _ => r1bStripLetsTop n (b.instantiate1 v)
  | n + 1, .mdata _ e => r1bStripLetsTop n e
  | _, e => e

private meta def r1bSplitSepTop : Nat → Lean.Expr → Lean.Expr → Array Lean.Expr
  | 0, _, e => #[e]
  | fuel + 1, sepSample, e =>
    let e := r1bStripLetsTop 64 e
    let fn := sepSample.getAppFn.constName!
    let ar := sepSample.getAppNumArgs
    if e.isAppOfArity fn ar then
      r1bSplitSepTop fuel sepSample (e.getArg! (ar - 2)) ++
        r1bSplitSepTop fuel sepSample (e.getArg! (ar - 1))
    else #[e]

private meta def r1bIsDefEqPureTop (x a : Lean.Expr) : Lean.Elab.TermElabM Bool := do
  let x := r1bStripLetsTop 64 x; let a := r1bStripLetsTop 64 a
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

private theorem r1b_pull_L (a l' r : SepProp) : (a ∗ l') ∗ r = a ∗ (l' ∗ r) :=
  sepConj_assoc a l' r
private theorem r1b_pull_R_atom (l a : SepProp) : l ∗ a = a ∗ l :=
  sepConj_comm l a
private theorem r1b_pull_R (l a r' : SepProp) : l ∗ (a ∗ r') = a ∗ (l ∗ r') := by
  rw [← sepConj_assoc, sepConj_comm l a, sepConj_assoc]
private theorem r1b_congr_L {l l' : SepProp} (h : l = l') (r : SepProp) : l ∗ r = l' ∗ r :=
  congrArg (· ∗ r) h
private theorem r1b_congr_R (l : SepProp) {r r' : SepProp} (h : r = r') : l ∗ r = l ∗ r' :=
  congrArg (l ∗ ·) h
private theorem r1b_congr_LR {l l' r r' : SepProp} (hl : l = l') (hr : r = r') :
    l ∗ r = l' ∗ r' := by rw [hl, hr]

private meta partial def r1bCleanEmp (fn : Lean.Name) (ar : Nat)
    (mkSep : Lean.Expr → Lean.Expr → Lean.Expr)
    (empFn : Lean.Name) (empAr : Nat) (e : Lean.Expr) :
    Lean.Elab.TermElabM (Lean.Expr × Lean.Expr) := do
  let ec := e.consumeMData
  if ec.isAppOfArity fn ar then
    let l := ec.getArg! (ar - 2)
    let r := ec.getArg! (ar - 1)
    let (l', hl) ← r1bCleanEmp fn ar mkSep empFn empAr l
    let (r', hr) ← r1bCleanEmp fn ar mkSep empFn empAr r
    let hcong ← Lean.Meta.mkAppOptM ``r1b_congr_LR #[some l, some l', some r, some r', some hl, some hr]
    if l'.consumeMData.isAppOfArity empFn empAr then
      let hemp ← Lean.Meta.mkAppM ``emp_sepConj #[r']
      return (r', ← Lean.Meta.mkEqTrans hcong hemp)
    else if r'.consumeMData.isAppOfArity empFn empAr then
      let hemp ← Lean.Meta.mkAppM ``sepConj_emp #[l']
      return (l', ← Lean.Meta.mkEqTrans hcong hemp)
    else
      return (mkSep l' r', hcong)
  else
    return (e, ← Lean.Meta.mkEqRefl e)

private meta partial def r1bAppendRight (fn : Lean.Name) (ar : Nat)
    (mkSep : Lean.Expr → Lean.Expr → Lean.Expr)
    (l r : Lean.Expr) : Lean.Elab.TermElabM (Lean.Expr × Lean.Expr) := do
  let lc := l.consumeMData
  if lc.isAppOfArity fn ar then
    let a := lc.getArg! (ar - 2)
    let l' := lc.getArg! (ar - 1)
    let h1 ← Lean.Meta.mkAppM ``r1b_pull_L #[a, l', r]
    let (rest, h2) ← r1bAppendRight fn ar mkSep l' r
    let h3 ← Lean.Meta.mkAppOptM ``r1b_congr_R #[some a, some (mkSep l' r), some rest, some h2]
    return (mkSep a rest, ← Lean.Meta.mkEqTrans h1 h3)
  else
    let out := mkSep l r
    return (out, ← Lean.Meta.mkEqRefl out)

private meta partial def r1bRightAssoc (fn : Lean.Name) (ar : Nat)
    (mkSep : Lean.Expr → Lean.Expr → Lean.Expr)
    (e : Lean.Expr) : Lean.Elab.TermElabM (Lean.Expr × Lean.Expr) := do
  let ec := e.consumeMData
  if ec.isAppOfArity fn ar then
    let l := ec.getArg! (ar - 2)
    let r := ec.getArg! (ar - 1)
    let (l', hl) ← r1bRightAssoc fn ar mkSep l
    let (r', hr) ← r1bRightAssoc fn ar mkSep r
    let hcong ← Lean.Meta.mkAppOptM ``r1b_congr_LR #[some l, some l', some r, some r', some hl, some hr]
    let (out, happ) ← r1bAppendRight fn ar mkSep l' r'
    return (out, ← Lean.Meta.mkEqTrans hcong happ)
  else
    return (e, ← Lean.Meta.mkEqRefl e)

private meta partial def r1bExtractAtom (fn : Lean.Name) (ar : Nat)
    (mkSep : Lean.Expr → Lean.Expr → Lean.Expr)
    (target e : Lean.Expr) : Lean.Elab.TermElabM (Option (Option Lean.Expr × Lean.Expr)) := do
  let ec := e.consumeMData
  if ec.isAppOfArity fn ar then
    let l := ec.getArg! (ar - 2)
    let r := ec.getArg! (ar - 1)
    if let some (rem?, hl) ← r1bExtractAtom fn ar mkSep target l then
      match rem? with
      | none =>
        let prf ← Lean.Meta.mkAppOptM ``r1b_congr_L #[some l, some target, some hl, some r]
        return some (some r, prf)
      | some l' =>
        let h1 ← Lean.Meta.mkAppOptM ``r1b_congr_L #[some l, some (mkSep target l'), some hl, some r]
        let h2 ← Lean.Meta.mkAppM ``r1b_pull_L #[target, l', r]
        return some (some (mkSep l' r), ← Lean.Meta.mkEqTrans h1 h2)
    else if let some (rem?, hr) ← r1bExtractAtom fn ar mkSep target r then
      match rem? with
      | none =>
        let h1 ← Lean.Meta.mkAppOptM ``r1b_congr_R #[some l, some r, some target, some hr]
        let h2 ← Lean.Meta.mkAppM ``r1b_pull_R_atom #[l, target]
        return some (some l, ← Lean.Meta.mkEqTrans h1 h2)
      | some r' =>
        let h1 ← Lean.Meta.mkAppOptM ``r1b_congr_R #[some l, some r, some (mkSep target r'), some hr]
        let h2 ← Lean.Meta.mkAppM ``r1b_pull_R #[l, target, r']
        return some (some (mkSep l r'), ← Lean.Meta.mkEqTrans h1 h2)
    else
      return none
  else if ← r1bIsDefEqPureTop e target then
    let eqTy ← Lean.Meta.mkEq e target
    let prf ← if e == target then Lean.Meta.mkEqRefl e
      else Lean.Meta.mkExpectedTypeHint (← Lean.Meta.mkEqRefl e) eqTy
    return some (none, prf)
  else
    return none

private meta partial def r1bPermEq (fn : Lean.Name) (ar : Nat)
    (mkSep : Lean.Expr → Lean.Expr → Lean.Expr)
    (lhs rhs : Lean.Expr) : Lean.Elab.TermElabM Lean.Expr := do
  let rc := rhs.consumeMData
  if rc.isAppOfArity fn ar then
    let b1 := rc.getArg! (ar - 2)
    let rhsRest := rc.getArg! (ar - 1)
    match ← r1bExtractAtom fn ar mkSep b1 lhs with
    | some (some lhsRest, h1) =>
      let hRest ← r1bPermEq fn ar mkSep lhsRest rhsRest
      let h2 ← Lean.Meta.mkAppOptM ``r1b_congr_R #[some b1, some lhsRest, some rhsRest, some hRest]
      Lean.Meta.mkEqTrans h1 h2
    | _ => throwError "r1b_ac_fast: unmatched atom {b1}"
  else
    match ← r1bExtractAtom fn ar mkSep rhs lhs with
    | some (none, h1) => return h1
    | _ => throwError "r1b_ac_fast: tail mismatch"

local elab (priority := 20000) "r1b_ac_fast" : tactic => Lean.Elab.Tactic.withMainContext do
  let g ← Lean.Elab.Tactic.getMainGoal
  let ty ← Lean.instantiateMVars (← g.getType)
  let some (_, origLhs, origRhs) := ty.consumeMData.eq?
    | throwError "r1b_ac_fast: expected equality goal"
  let sepTy := Lean.mkConst ``SepProp []
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let fn := sepSample.getAppFn.constName!
  let ar := sepSample.getAppNumArgs
  let mkSep (l r : Lean.Expr) : Lean.Expr :=
    sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (ar - 2) ++ #[l, r])
  let empFn := empExpr.getAppFn.constName!
  let empAr := empExpr.getAppNumArgs
  let (l1, hl1) ← r1bCleanEmp fn ar mkSep empFn empAr origLhs
  let (r1, hr1) ← r1bCleanEmp fn ar mkSep empFn empAr origRhs
  let (r2, hr2) ← r1bRightAssoc fn ar mkSep r1
  let hperm ← r1bPermEq fn ar mkSep l1 r2
  let hr12 ← Lean.Meta.mkEqTrans hr1 hr2
  let prf ← Lean.Meta.mkEqTrans hl1 (← Lean.Meta.mkEqTrans hperm (← Lean.Meta.mkEqSymm hr12))
  g.assign prf
  Lean.Elab.Tactic.replaceMainGoal []

local macro (priority := 20000) "r1b_ac" : tactic =>
  `(tactic| first | rfl | exact emp_sepConj _ | exact sepConj_emp _ | r1b_ac_fast | sep_ac_rfl)

private meta def r1bComputeRestTop (ctxName : String) (p a1 : Lean.Expr) :
    Lean.Elab.TermElabM Lean.Expr := do
  let sepTy := Lean.mkConst ``SepProp []
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let ps := (r1bSplitSepTop 256 sepSample (← Lean.instantiateMVars p)).toList
  let a1s := (r1bSplitSepTop 256 sepSample (← Lean.instantiateMVars a1)).toList
  let mut rem := ps
  for a in a1s do
    let mut removed := false
    let mut next : List Lean.Expr := []
    for x in rem do
      if !removed && (← r1bIsDefEqPureTop x a) then removed := true
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

local elab (priority := 20000) "r1b_entails_frame " t1:term:arg h:term:arg t2:term:arg :
    term <= expectedType => do
  let exp ← Lean.instantiateMVars expectedType
  if exp.isMVar then Lean.Elab.Term.tryPostpone
  let entSample ← Lean.Elab.Term.elabTerm (← `(emp ⊢ emp)) none
  let ear := entSample.getAppNumArgs
  let expS := r1bStripLetsTop 64 exp
  let p := expS.getArg! (ear - 2)
  let q := expS.getArg! (ear - 1)
  if (← Lean.instantiateMVars p).isMVar then Lean.Elab.Term.tryPostpone
  if (← Lean.instantiateMVars q).isMVar then Lean.Elab.Term.tryPostpone
  let hExpr ← Lean.Elab.Term.elabTerm h none
  let hTy := r1bStripLetsTop 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
  let a1 := hTy.getArg! (ear - 2)
  let a2 := hTy.getArg! (ear - 1)
  let r ← r1bComputeRestTop "r1b_entails_frame" p a1
  let sepTy := Lean.mkConst ``SepProp []
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let sar := sepSample.getAppNumArgs
  let mkSep (x y : Lean.Expr) : Lean.Expr :=
    sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
  let rIsEmp ← r1bIsDefEqPureTop r empExpr
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

local elab (priority := 20000) "r1b_sepWPp_frame " t1:term:arg h:term:arg t2:term:arg hk:term:arg :
    term <= expectedType => do
  let exp ← Lean.instantiateMVars expectedType
  if exp.isMVar then Lean.Elab.Term.tryPostpone
  let expS := r1bStripLetsTop 64 exp
  let args := expS.getAppArgs
  let prog := args[0]!; let ret := args[1]!; let st := args[2]!; let p := args[3]!
  let q := args[4]!; let qp := args[5]!; let oom := args[6]!
  let entSample ← Lean.Elab.Term.elabTerm (← `(emp ⊢ emp)) none
  let ear := entSample.getAppNumArgs
  let hExpr ← Lean.Elab.Term.elabTerm h none
  let hTy := r1bStripLetsTop 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
  let a1 := hTy.getArg! (ear - 2)
  let a2 := hTy.getArg! (ear - 1)
  let r ← r1bComputeRestTop "r1b_sepWPp_frame" p a1
  let sepTy := Lean.mkConst ``SepProp []
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let sar := sepSample.getAppNumArgs
  let mkSep (x y : Lean.Expr) : Lean.Expr :=
    sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
  let rIsEmp ← r1bIsDefEqPureTop r empExpr
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
    let a2IsEmp ← r1bIsDefEqPureTop a2 empExpr
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

private theorem r1b_open_bundle_dest (fsp : BitVec 64) :
    (memRegion (fsp + 0x4d0#64) 48 ∗ memRegion (fsp + 0x500#64) 0x90) ⊢
      ∃∗ m4d0 : BitVec 64, ∃∗ m4d8 : BitVec 64, ∃∗ m4e0 : BitVec 64,
      ∃∗ m4e8 : BitVec 64, ∃∗ m4f0 : BitVec 64, ∃∗ m4f8 : BitVec 64,
      ∃∗ m500 : BitVec 64, ∃∗ m508 : BitVec 32,
      ∃∗ m510 : BitVec 64, ∃∗ m518 : BitVec 64, ∃∗ m520 : BitVec 64,
      ∃∗ m528 : BitVec 64, ∃∗ m530 : BitVec 64, ∃∗ m538 : BitVec 32,
      ∃∗ m540 : BitVec 32, ∃∗ m544 : BitVec 32,
      ∃∗ m548 : BitVec 64, ∃∗ m550 : BitVec 64, ∃∗ m558 : BitVec 64, ∃∗ m560 : BitVec 64,
      ∃∗ m568 : BitVec 32, ∃∗ m56c : BitVec 8,
      ∃∗ d0 : BitVec 8, ∃∗ d1 : BitVec 8, ∃∗ d2 : BitVec 8, ∃∗ d3 : BitVec 32,
      ∃∗ m574 : BitVec 8, ∃∗ m575 : BitVec 8, ∃∗ m576 : BitVec 32, ∃∗ m57a : BitVec 16,
      ∃∗ m57c : BitVec 64, ∃∗ m584 : BitVec 64, ∃∗ m58c : BitVec 8, ∃∗ m58d : BitVec 8,
        ((fsp + 0x4d0#64) ↦₆₄ m4d0) ∗ ((fsp + 0x4d8#64) ↦₆₄ m4d8) ∗
        ((fsp + 0x4e0#64) ↦₆₄ m4e0) ∗ ((fsp + 0x4e8#64) ↦₆₄ m4e8) ∗
        ((fsp + 0x4f0#64) ↦₆₄ m4f0) ∗ ((fsp + 0x4f8#64) ↦₆₄ m4f8) ∗
        ((fsp + 0x500#64) ↦₆₄ m500) ∗ ((fsp + 0x508#64) ↦₃₂ m508) ∗
        memRegion (fsp + 0x50c#64) 4 ∗
        ((fsp + 0x510#64) ↦₆₄ m510) ∗ ((fsp + 0x518#64) ↦₆₄ m518) ∗
        ((fsp + 0x520#64) ↦₆₄ m520) ∗ ((fsp + 0x528#64) ↦₆₄ m528) ∗
        ((fsp + 0x530#64) ↦₆₄ m530) ∗ ((fsp + 0x538#64) ↦₃₂ m538) ∗
        memRegion (fsp + 0x53c#64) 4 ∗
        ((fsp + 0x540#64) ↦₃₂ m540) ∗ ((fsp + 0x544#64) ↦₃₂ m544) ∗
        ((fsp + 0x548#64) ↦₆₄ m548) ∗ ((fsp + 0x550#64) ↦₆₄ m550) ∗
        ((fsp + 0x558#64) ↦₆₄ m558) ∗ ((fsp + 0x560#64) ↦₆₄ m560) ∗
        ((fsp + 0x568#64) ↦₃₂ m568) ∗ ((fsp + 0x56c#64) ↦₈ m56c) ∗
        ((fsp + 0x56d#64) ↦₈ d0) ∗ ((fsp + 0x56e#64) ↦₈ d1) ∗
        ((fsp + 0x56f#64) ↦₈ d2) ∗ ((fsp + 0x570#64) ↦₃₂ d3) ∗
        ((fsp + 0x574#64) ↦₈ m574) ∗ ((fsp + 0x575#64) ↦₈ m575) ∗
        ((fsp + 0x576#64) ↦₃₂ m576) ∗ ((fsp + 0x57a#64) ↦₁₆ m57a) ∗
        ((fsp + 0x57c#64) ↦₆₄ m57c) ∗ ((fsp + 0x584#64) ↦₆₄ m584) ∗
        ((fsp + 0x58c#64) ↦₈ m58c) ∗ ((fsp + 0x58d#64) ↦₈ m58d) ∗
        memRegion (fsp + 0x58e#64) 2 := by
  have h48 := r1b_region48_to_cells (fsp + 0x4d0#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h48
  have h90 : memRegion (fsp + 0x500#64) 0x90 =
      memRegion (fsp + 0x500#64) 8 ∗ memRegion (fsp + 0x508#64) 4 ∗ memRegion (fsp + 0x50c#64) 4 ∗
        memRegion (fsp + 0x510#64) 8 ∗ memRegion (fsp + 0x518#64) 8 ∗ memRegion (fsp + 0x520#64) 8 ∗
        memRegion (fsp + 0x528#64) 8 ∗ memRegion (fsp + 0x530#64) 8 ∗ memRegion (fsp + 0x538#64) 4 ∗
        memRegion (fsp + 0x53c#64) 4 ∗ memRegion (fsp + 0x540#64) 4 ∗ memRegion (fsp + 0x544#64) 4 ∗
        memRegion (fsp + 0x548#64) 8 ∗ memRegion (fsp + 0x550#64) 8 ∗ memRegion (fsp + 0x558#64) 8 ∗
        memRegion (fsp + 0x560#64) 8 ∗ memRegion (fsp + 0x568#64) 4 ∗ memRegion (fsp + 0x56c#64) 1 ∗
        memRegion (fsp + 0x56d#64) 7 ∗ memRegion (fsp + 0x574#64) 1 ∗ memRegion (fsp + 0x575#64) 1 ∗
        memRegion (fsp + 0x576#64) 4 ∗ memRegion (fsp + 0x57a#64) 2 ∗ memRegion (fsp + 0x57c#64) 8 ∗
        memRegion (fsp + 0x584#64) 8 ∗ memRegion (fsp + 0x58c#64) 1 ∗ memRegion (fsp + 0x58d#64) 1 ∗
        memRegion (fsp + 0x58e#64) 2 := by
    rw [r1b_split_region fsp 0x500 8 0x88, r1b_split_region fsp 0x508 4 0x84,
      r1b_split_region fsp 0x50c 4 0x80, r1b_split_region fsp 0x510 8 0x78,
      r1b_split_region fsp 0x518 8 0x70, r1b_split_region fsp 0x520 8 0x68,
      r1b_split_region fsp 0x528 8 0x60, r1b_split_region fsp 0x530 8 0x58,
      r1b_split_region fsp 0x538 4 0x54, r1b_split_region fsp 0x53c 4 0x50,
      r1b_split_region fsp 0x540 4 0x4c, r1b_split_region fsp 0x544 4 0x48,
      r1b_split_region fsp 0x548 8 0x40, r1b_split_region fsp 0x550 8 0x38,
      r1b_split_region fsp 0x558 8 0x30, r1b_split_region fsp 0x560 8 0x28,
      r1b_split_region fsp 0x568 4 0x24, r1b_split_region fsp 0x56c 1 0x23,
      r1b_split_region fsp 0x56d 7 0x1c, r1b_split_region fsp 0x574 1 0x1b,
      r1b_split_region fsp 0x575 1 0x1a, r1b_split_region fsp 0x576 4 0x16,
      r1b_split_region fsp 0x57a 2 0x14, r1b_split_region fsp 0x57c 8 0x0c,
      r1b_split_region fsp 0x584 8 4, r1b_split_region fsp 0x58c 1 3, r1b_split_region fsp 0x58d 1 2]
  have ht7 := r1b_tail7_init (fsp + 0x56d#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at ht7
  rw [h48, h90, ht7, memRegion_eight (fsp + 0x500#64), memRegion_four (fsp + 0x508#64),
    memRegion_eight (fsp + 0x510#64), memRegion_eight (fsp + 0x518#64),
    memRegion_eight (fsp + 0x520#64), memRegion_eight (fsp + 0x528#64),
    memRegion_eight (fsp + 0x530#64), memRegion_four (fsp + 0x538#64),
    memRegion_four (fsp + 0x540#64), memRegion_four (fsp + 0x544#64),
    memRegion_eight (fsp + 0x548#64), memRegion_eight (fsp + 0x550#64),
    memRegion_eight (fsp + 0x558#64), memRegion_eight (fsp + 0x560#64),
    memRegion_four (fsp + 0x568#64), memRegion_one (fsp + 0x56c#64),
    memRegion_one (fsp + 0x574#64), memRegion_one (fsp + 0x575#64),
    memRegion_four (fsp + 0x576#64), memRegion_two (fsp + 0x57a#64),
    memRegion_eight (fsp + 0x57c#64), memRegion_eight (fsp + 0x584#64),
    memRegion_one (fsp + 0x58c#64), memRegion_one (fsp + 0x58d#64)]
  simp only [sepConj_assoc, sepExists_sepConj_left,
    r1b_exR_64, r1b_exR_32, r1b_exR_16, r1b_exR_8, r1b_exR_reg]
  exact Entails.refl _

private theorem r1b_rejoin_init2Locals (A : RustAlloc) (fsp : BitVec 64) (d2 : Init2Data)
    (w0e0 w0e4 c9 v11c v164 v1b0 : BitVec 32)
    (c13 : BitVec 16)
    (w15 spkW0 spkW16 spkW24 : BitVec 64)
    (spkW8 : BitVec 32)
    (c0 c1 c2 c3 c4 c5 c6 c31 : BitVec 8)
    (c23 kpkPtr v130 v148 kpkCap spkPtr spkCap regCap regPtr : BitVec 64)
    (ikW0 v188 ikW3 ikW1 w260 w268 : BitVec 64) :
    ((fsp ↦₃₂ 0#32) ∗ memRegion (fsp + 0x004#64) 0x0dc ∗
      ((fsp + 0x0e0#64) ↦₃₂ w0e0) ∗ ((fsp + 0x0e4#64) ↦₃₂ w0e4) ∗
      ((fsp + 0x0e8#64) ↦₆₄ w15) ∗ ((fsp + 0x0f0#64) ↦₆₄ spkW8.zeroExtend 64) ∗
      ((fsp + 0x0f8#64) ↦₆₄ spkW24) ∗ ((fsp + 0x100#64) ↦₆₄ spkW16) ∗
      ((fsp + 0x108#64) ↦₆₄ spkW0) ∗
      ((fsp + 0x110#64) ↦₆₄ d2.spkSigPtr) ∗
      memRegion (fsp + 0x118#64) 4 ∗ ((fsp + 0x11c#64) ↦₃₂ v11c) ∗
      ((fsp + 0x120#64) ↦₆₄ 64#64) ∗
      ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗ ((fsp + 0x130#64) ↦₆₄ v130) ∗
      ((fsp + 0x138#64) ↦₆₄ d2.kpkSigPtr) ∗
      ((fsp + 0x140#64) ↦₆₄ 1568#64) ∗
      ((fsp + 0x148#64) ↦₆₄ v148) ∗ ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗
      ((fsp + 0x158#64) ↦₆₄ 64#64) ∗
      memRegion (fsp + 0x160#64) 4 ∗ ((fsp + 0x164#64) ↦₃₂ v164) ∗
      ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
      ((fsp + 0x178#64) ↦₆₄ d2.kpkPtr) ∗
      ((fsp + 0x180#64) ↦₆₄ ikW0) ∗ ((fsp + 0x188#64) ↦₆₄ v188) ∗
      ((fsp + 0x190#64) ↦₆₄ ikW3) ∗ ((fsp + 0x198#64) ↦₆₄ regCap) ∗
      ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗ ((fsp + 0x1a8#64) ↦₆₄ ikW1) ∗
      ((fsp + 0x1b0#64) ↦₃₂ v1b0) ∗ memRegion (fsp + 0x1b4#64) 4 ∗
      ((fsp + 0x1b8#64) ↦₆₄ d2.meG.name.ptr) ∗
      ((fsp + 0x1c0#64) ↦₆₄ d2.dirCap) ∗
      ((fsp + 0x1c8#64) ↦₆₄ d2.dirPtr) ∗
      memRegion (fsp + 0x1d0#64) 0x18 ∗
      ((fsp + 0x1e8#64) ↦₆₄ c23) ∗ ((fsp + 0x1f0#64) ↦₈ c31) ∗
      memRegion (fsp + 0x1f1#64) 7 ∗
      ((fsp + 0x1f8#64) ↦₃₂ c9) ∗ ((fsp + 0x1fc#64) ↦₁₆ c13) ∗
      memRegion (fsp + 0x1fe#64) 2 ∗
      sevenBytesHeadAt (fsp + 0x200#64) c0 c1 c2 c3 c4 c5 c6 ∗
      memRegion (fsp + 0x207#64) 0x19 ∗
      memRegion (fsp + 0x220#64) 0x40 ∗
      ((fsp + 0x260#64) ↦₆₄ w260) ∗ ((fsp + 0x268#64) ↦₆₄ w268) ∗
      memRegion (fsp + 0x270#64) 0x30 ∗
      protocolAddressAt A d2.peerG (fsp + 0x2a0#64) ∗
      memRegion (fsp + 0x2c0#64) 0x60 ∗
      protocolAddressAt A d2.meG (fsp + 0x320#64) ∗
      memRegion (fsp + 0x340#64) 0x190 ∗
      cliBundleAt (fsp + 0x4d0#64) d2.bundle d2.spkSigPtr d2.kpkSigPtr d2.kpkPtr ∗
      memRegion (fsp + 0x590#64) 0x11c0 ∗
      memRegion (fsp + 0x1750#64) 24 ∗
      memRegion (fsp + 0x1768#64) 0x1288) ⊢
      runLocals fsp (init2Cells A fsp d2) := by
  have hg1 :
      memRegion (fsp + 0x004#64) 0x0dc ∗
        ((fsp + 0x0e0#64) ↦₃₂ w0e0) ∗ ((fsp + 0x0e4#64) ↦₃₂ w0e4) ∗
        ((fsp + 0x0e8#64) ↦₆₄ w15) ∗ ((fsp + 0x0f0#64) ↦₆₄ spkW8.zeroExtend 64) ∗
        ((fsp + 0x0f8#64) ↦₆₄ spkW24) ∗ ((fsp + 0x100#64) ↦₆₄ spkW16) ∗
        ((fsp + 0x108#64) ↦₆₄ spkW0) ⊢ memRegion (fsp + 0x004#64) 0x10c := by
    refine Entails.trans (r1b_entails_frame (by r1b_ac)
      (sepConj_mono (pointsTo32_entails_memRegion (fsp + 0x0e0#64) w0e0)
        (sepConj_mono (pointsTo32_entails_memRegion (fsp + 0x0e4#64) w0e4)
          (sepConj_mono (pointsTo64_entails_memRegion (fsp + 0x0e8#64) w15)
            (sepConj_mono (pointsTo64_entails_memRegion (fsp + 0x0f0#64) (spkW8.zeroExtend 64))
              (sepConj_mono (pointsTo64_entails_memRegion (fsp + 0x0f8#64) spkW24)
                (sepConj_mono (pointsTo64_entails_memRegion (fsp + 0x100#64) spkW16)
                  (pointsTo64_entails_memRegion (fsp + 0x108#64) spkW0))))))) (by r1b_ac)) ?_
    refine Entails.trans (Entails.of_eq (show _ =
      memRegion (fsp + 0x004#64) 0x0dc ∗
        memRegion (fsp + 0x0e0#64) 4 ∗ memRegion (fsp + 0x0e4#64) 4 ∗
        memRegion (fsp + 0x0e8#64) 8 ∗ memRegion (fsp + 0x0f0#64) 8 ∗
        memRegion (fsp + 0x0f8#64) 8 ∗ memRegion (fsp + 0x100#64) 8 ∗
        memRegion (fsp + 0x108#64) 8 by r1b_ac)) ?_
    rw [r1b_join_region fsp 0x100 8 8, r1b_join_region fsp 0x0f8 8 16,
      r1b_join_region fsp 0x0f0 8 24, r1b_join_region fsp 0x0e8 8 32,
      r1b_join_region fsp 0x0e4 4 40, r1b_join_region fsp 0x0e0 4 44,
      r1b_join_region fsp 0x004 0x0dc 0x30]
    exact Entails.refl _
  have hg2 : memRegion (fsp + 0x118#64) 4 ∗ ((fsp + 0x11c#64) ↦₃₂ v11c) ⊢
      memRegion (fsp + 0x118#64) 8 := by
    refine Entails.trans (sepConj_mono_right (pointsTo32_entails_memRegion (fsp + 0x11c#64) v11c)) ?_
    rw [r1b_join_region fsp 0x118 4 4]; exact Entails.refl _
  have hg3 : ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗ ((fsp + 0x130#64) ↦₆₄ v130) ⊢
      memRegion (fsp + 0x128#64) 16 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      r1b_cells2_to_region16 (fsp + 0x128#64) kpkPtr v130
  have hg4 : ((fsp + 0x148#64) ↦₆₄ v148) ∗ ((fsp + 0x150#64) ↦₆₄ kpkCap) ⊢
      memRegion (fsp + 0x148#64) 16 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      r1b_cells2_to_region16 (fsp + 0x148#64) v148 kpkCap
  have hg5 :
      memRegion (fsp + 0x160#64) 4 ∗ ((fsp + 0x164#64) ↦₃₂ v164) ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ⊢
        memRegion (fsp + 0x160#64) 24 := by
    refine Entails.trans (r1b_entails_frame (by r1b_ac)
      (sepConj_mono (pointsTo32_entails_memRegion (fsp + 0x164#64) v164)
        (sepConj_mono (pointsTo64_entails_memRegion (fsp + 0x168#64) spkPtr)
          (pointsTo64_entails_memRegion (fsp + 0x170#64) spkCap))) (by r1b_ac)) ?_
    refine Entails.trans (Entails.of_eq (show _ =
      memRegion (fsp + 0x160#64) 4 ∗ memRegion (fsp + 0x164#64) 4 ∗
        memRegion (fsp + 0x168#64) 8 ∗ memRegion (fsp + 0x170#64) 8 by r1b_ac)) ?_
    rw [r1b_join_region fsp 0x168 8 8, r1b_join_region fsp 0x164 4 16,
      r1b_join_region fsp 0x160 4 20]
    exact Entails.refl _
  have hg6 :
      ((fsp + 0x180#64) ↦₆₄ ikW0) ∗ ((fsp + 0x188#64) ↦₆₄ v188) ∗
        ((fsp + 0x190#64) ↦₆₄ ikW3) ∗ ((fsp + 0x198#64) ↦₆₄ regCap) ∗
        ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗ ((fsp + 0x1a8#64) ↦₆₄ ikW1) ∗
        ((fsp + 0x1b0#64) ↦₃₂ v1b0) ∗ memRegion (fsp + 0x1b4#64) 4 ⊢
        memRegion (fsp + 0x180#64) 0x38 := by
    refine Entails.trans (r1b_entails_frame (by r1b_ac)
      (sepConj_mono (pointsTo64_entails_memRegion (fsp + 0x180#64) ikW0)
        (sepConj_mono (pointsTo64_entails_memRegion (fsp + 0x188#64) v188)
          (sepConj_mono (pointsTo64_entails_memRegion (fsp + 0x190#64) ikW3)
            (sepConj_mono (pointsTo64_entails_memRegion (fsp + 0x198#64) regCap)
              (sepConj_mono (pointsTo64_entails_memRegion (fsp + 0x1a0#64) regPtr)
                (sepConj_mono (pointsTo64_entails_memRegion (fsp + 0x1a8#64) ikW1)
                  (pointsTo32_entails_memRegion (fsp + 0x1b0#64) v1b0))))))) (by r1b_ac)) ?_
    simp only [sepConj_assoc]
    rw [r1b_join_region fsp 0x1b0 4 4, r1b_join_region fsp 0x1a8 8 8,
      r1b_join_region fsp 0x1a0 8 16, r1b_join_region fsp 0x198 8 24,
      r1b_join_region fsp 0x190 8 32, r1b_join_region fsp 0x188 8 40,
      r1b_join_region fsp 0x180 8 48]
    exact Entails.refl _
  have hg7 :
      memRegion (fsp + 0x1d0#64) 0x18 ∗
        ((fsp + 0x1e8#64) ↦₆₄ c23) ∗ ((fsp + 0x1f0#64) ↦₈ c31) ∗
        memRegion (fsp + 0x1f1#64) 7 ∗
        ((fsp + 0x1f8#64) ↦₃₂ c9) ∗ ((fsp + 0x1fc#64) ↦₁₆ c13) ∗
        memRegion (fsp + 0x1fe#64) 2 ∗
        sevenBytesHeadAt (fsp + 0x200#64) c0 c1 c2 c3 c4 c5 c6 ∗
        memRegion (fsp + 0x207#64) 0x19 ∗
        memRegion (fsp + 0x220#64) 0x40 ∗
        ((fsp + 0x260#64) ↦₆₄ w260) ∗ ((fsp + 0x268#64) ↦₆₄ w268) ∗
        memRegion (fsp + 0x270#64) 0x30 ⊢
        memRegion (fsp + 0x1d0#64) 0xd0 := by
    refine Entails.trans (r1b_entails_frame (by r1b_ac)
      (sepConj_mono (pointsTo64_entails_memRegion (fsp + 0x1e8#64) c23)
        (sepConj_mono (r1b_cell8_to_region (fsp + 0x1f0#64) c31)
          (sepConj_mono (pointsTo32_entails_memRegion (fsp + 0x1f8#64) c9)
            (sepConj_mono (pointsTo16_entails_memRegion (fsp + 0x1fc#64) c13)
              (sepConj_mono (r1b_head7_to_region (fsp + 0x200#64) c0 c1 c2 c3 c4 c5 c6)
                (sepConj_mono (pointsTo64_entails_memRegion (fsp + 0x260#64) w260)
                  (pointsTo64_entails_memRegion (fsp + 0x268#64) w268))))))) (by r1b_ac)) ?_
    refine Entails.trans (Entails.of_eq (show _ =
      memRegion (fsp + 0x1d0#64) 0x18 ∗
        memRegion (fsp + 0x1e8#64) 8 ∗ memRegion (fsp + 0x1f0#64) 1 ∗
        memRegion (fsp + 0x1f1#64) 7 ∗
        memRegion (fsp + 0x1f8#64) 4 ∗ memRegion (fsp + 0x1fc#64) 2 ∗
        memRegion (fsp + 0x1fe#64) 2 ∗
        memRegion (fsp + 0x200#64) 7 ∗ memRegion (fsp + 0x207#64) 0x19 ∗
        memRegion (fsp + 0x220#64) 0x40 ∗
        memRegion (fsp + 0x260#64) 8 ∗ memRegion (fsp + 0x268#64) 8 ∗
        memRegion (fsp + 0x270#64) 0x30 by r1b_ac)) ?_
    rw [r1b_join_region fsp 0x268 8 0x30, r1b_join_region fsp 0x260 8 0x38,
      r1b_join_region fsp 0x220 0x40 0x40, r1b_join_region fsp 0x207 0x19 0x80,
      r1b_join_region fsp 0x200 7 0x99, r1b_join_region fsp 0x1fe 2 0xa0,
      r1b_join_region fsp 0x1fc 2 0xa2, r1b_join_region fsp 0x1f8 4 0xa4,
      r1b_join_region fsp 0x1f1 7 0xa8, r1b_join_region fsp 0x1f0 1 0xaf,
      r1b_join_region fsp 0x1e8 8 0xb0, r1b_join_region fsp 0x1d0 0x18 0xb8]
    exact Entails.refl _
  have hg8 :
      memRegion (fsp + 0x590#64) 0x11c0 ∗ memRegion (fsp + 0x1750#64) 24 ∗
        memRegion (fsp + 0x1768#64) 0x1288 ⊢
      memRegion (fsp + 0x590#64) 0x1e20 ∗ memRegion (fsp + 0x23b0#64) 48 ∗
        memRegion (fsp + 0x23e0#64) 0x610 := by
    rw [r1b_join_region fsp 0x1750 24 0x1288, r1b_join_region fsp 0x590 0x11c0 0x12a0,
      r1b_split_region fsp 0x590 0x1e20 0x640, r1b_split_region fsp 0x23b0 48 0x610]
    exact Entails.refl _
  refine Entails.trans (r1b_entails_frame (by r1b_ac)
    (sepConj_mono hg1 (sepConj_mono hg2 (sepConj_mono hg3 (sepConj_mono hg4
      (sepConj_mono hg5 (sepConj_mono hg6 (sepConj_mono hg7 hg8))))))) (by r1b_ac)) ?_
  dsimp only [init2Cells, runLocals, runLocalsFrom, runLocalBytes]
  simp only [Nat.reduceAdd, Nat.reduceSub, BitVec.add_zero, memRegion_zero, emp_sepConj]
  exact Entails.of_eq (by r1b_ac)

set_option maxHeartbeats 400000 in
private theorem r1b_pack_bundle_and_addr (A : RustAlloc) (fsp : BitVec 64) (d : Init1Data)
    {r0 r1 r2 r3 : BitVec 8}
    {spk : PublicKey} {kpk spkSig kpkSig : List (BitVec 8)}
    {spkSigPtr kpkSigPtr kpkBuf : BitVec 64}
    {spkW0 : BitVec 64} {spkW8 spkW12 : BitVec 32} {spkW16 spkW24 : BitVec 64}
    {spkId kpkId v11c : BitVec 32}
    {opk : Option (BitVec 32 × PublicKey)}
    {c0 c1 c2 c3 c4 c5 c6 : BitVec 8}
    {w0e0 w0e4 c9 : BitVec 32} {c13 : BitVec 16} {w15 c23 : BitVec 64} {c31 : BitVec 8}
    {w268 : BitVec 64}
    (hw268 : w268.extractLsb' 0 8 = d.meG.device)
    (hikWords : Words32Eq d.idKey.publicKey.bytes.toList d.ikW0 d.ikW1 d.ikW2 d.ikW3)
    (hspk_bytes : spk.bytes.toList = r1b_spkBytesOf spkW0 spkW8 spkW12 spkW16 spkW24)
    (hlens : spkSig.length = 64 ∧ kpkSig.length = 64 ∧ kpk.length = 1568)
    (hopk_pk : ∀ p, opk = some p → v11c = p.1 ∧
      p.2.bytes.toList = pkBytesOf c0 c1 c2 c3 c4 c5 c6
        (w0e4.truncate 8) (w0e0.truncate 8) c9 c13 w15 c23 c31) :
    let opkFlag : BitVec 32 := if opk.isSome then 1#32 else 0#32
    let bundleV : BundleV := {
      idKey := d.idKey, regId := ofLe32 r0 r1 r2 r3, device := d.peerV.device,
      spkId := spkId, spk := spk, spkSig := spkSig,
      kpkId := kpkId, kpk := kpk, kpkSig := kpkSig, opk := opk
    }
    (((fsp + 0x320#64) ↦₆₄ d.meG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ d.meG.name.ptr) ∗
      ((fsp + 0x330#64) ↦₆₄ BitVec.ofNat 64 d.meG.name.bytes.length) ∗
      ((fsp + 0x338#64) ↦₆₄ w268) ∗ addrNameHeap A d.meG ∗
      ((fsp + 0x200#64) ↦₈ c0) ∗ ((fsp + 0x201#64) ↦₈ c1) ∗
      ((fsp + 0x202#64) ↦₈ c2) ∗ ((fsp + 0x203#64) ↦₃₂ (c6 ++ c5 ++ c4 ++ c3)) ∗
      ((fsp + 0x4d0#64) ↦₆₄ 64#64) ∗ ((fsp + 0x4d8#64) ↦₆₄ spkSigPtr) ∗
      ((fsp + 0x4e0#64) ↦₆₄ 64#64) ∗ (spkSigPtr ↦ₛ spkSig) ∗
      ((fsp + 0x4e8#64) ↦₆₄ spkW0) ∗
      ((fsp + 0x4f0#64) ↦₆₄ ((spkW12.zeroExtend 64 <<< 32) ||| spkW8.zeroExtend 64)) ∗
      ((fsp + 0x4f8#64) ↦₆₄ spkW16) ∗ ((fsp + 0x500#64) ↦₆₄ spkW24) ∗
      ((fsp + 0x508#64) ↦₃₂ spkId) ∗ memRegion (fsp + 0x50c#64) 4 ∗
      ((fsp + 0x510#64) ↦₆₄ 64#64) ∗ ((fsp + 0x518#64) ↦₆₄ kpkSigPtr) ∗
      ((fsp + 0x520#64) ↦₆₄ 64#64) ∗ (kpkSigPtr ↦ₛ kpkSig) ∗
      ((fsp + 0x528#64) ↦₆₄ kpkBuf) ∗ ((fsp + 0x530#64) ↦₆₄ 1568#64) ∗ (kpkBuf ↦ₛ kpk) ∗
      ((fsp + 0x538#64) ↦₃₂ kpkId) ∗ memRegion (fsp + 0x53c#64) 4 ∗
      ((fsp + 0x540#64) ↦₃₂ opkFlag) ∗ ((fsp + 0x544#64) ↦₃₂ v11c) ∗
      ((fsp + 0x548#64) ↦₆₄ d.ikW0) ∗ ((fsp + 0x550#64) ↦₆₄ d.ikW1) ∗
      ((fsp + 0x558#64) ↦₆₄ d.ikW2) ∗ ((fsp + 0x560#64) ↦₆₄ d.ikW3) ∗
      ((fsp + 0x568#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗ ((fsp + 0x56c#64) ↦₈ opkFlag.truncate 8) ∗
      ((fsp + 0x56d#64) ↦₃₂ (c3 ++ c2 ++ c1 ++ c0)) ∗
      ((fsp + 0x571#64) ↦₈ c4) ∗ ((fsp + 0x572#64) ↦₈ c5) ∗ ((fsp + 0x573#64) ↦₈ c6) ∗
      ((fsp + 0x574#64) ↦₈ w0e4.truncate 8) ∗ ((fsp + 0x575#64) ↦₈ w0e0.truncate 8) ∗
      ((fsp + 0x576#64) ↦₃₂ c9) ∗ ((fsp + 0x57a#64) ↦₁₆ c13) ∗
      ((fsp + 0x57c#64) ↦₆₄ w15) ∗ ((fsp + 0x584#64) ↦₆₄ c23) ∗
      ((fsp + 0x58c#64) ↦₈ c31) ∗
      ((fsp + 0x58d#64) ↦₈ d.peerV.device) ∗ memRegion (fsp + 0x58e#64) 2) ⊢
    (protocolAddressAt A d.meG (fsp + 0x320#64) ∗
      sevenBytesHeadAt (fsp + 0x200#64) c0 c1 c2 c3 c4 c5 c6 ∗
      cliBundleAt (fsp + 0x4d0#64) bundleV spkSigPtr kpkSigPtr kpkBuf) := by
  have hme_pack :
      ((fsp + 0x320#64) ↦₆₄ d.meG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ d.meG.name.ptr) ∗
        ((fsp + 0x330#64) ↦₆₄ BitVec.ofNat 64 d.meG.name.bytes.length) ∗
        ((fsp + 0x338#64) ↦₆₄ w268) ∗ addrNameHeap A d.meG ⊢
      protocolAddressAt A d.meG (fsp + 0x320#64) := by
    rw [protocolAddressAt_eq_parts A d.meG (fsp + 0x320#64),
      show fsp + 0x320#64 + 8#64 = fsp + 0x328#64 from by bv_omega,
      show fsp + 0x320#64 + 16#64 = fsp + 0x330#64 from by bv_omega]
    have hup := r1b_words_to_addrUpperAt (fsp + 0x330#64) d.meG w268 hw268
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hup
    exact r1b_entails_frame (by r1b_ac) hup (by r1b_ac)
  have hback200 :
      ((fsp + 0x200#64) ↦₈ c0) ∗ ((fsp + 0x201#64) ↦₈ c1) ∗
        ((fsp + 0x202#64) ↦₈ c2) ∗ ((fsp + 0x203#64) ↦₃₂ (c6 ++ c5 ++ c4 ++ c3)) ⊢
      sevenBytesHeadAt (fsp + 0x200#64) c0 c1 c2 c3 c4 c5 c6 := by
    have heq := (sevenBytesHeadAt_eq_tailAt (fsp + 0x200#64) c0 c1 c2 c3 c4 c5 c6).symm
    dsimp only [sevenBytesTailAt] at heq
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at heq
    rw [heq]; exact Entails.refl _
  have hlay :
      ((fsp + 0x56d#64) ↦₃₂ (c3 ++ c2 ++ c1 ++ c0)) ∗
        ((fsp + 0x571#64) ↦₈ c4) ∗ ((fsp + 0x572#64) ↦₈ c5) ∗ ((fsp + 0x573#64) ↦₈ c6) ∗
        ((fsp + 0x574#64) ↦₈ w0e4.truncate 8) ∗ ((fsp + 0x575#64) ↦₈ w0e0.truncate 8) ∗
        ((fsp + 0x576#64) ↦₃₂ c9) ∗ ((fsp + 0x57a#64) ↦₁₆ c13) ∗
        ((fsp + 0x57c#64) ↦₆₄ w15) ∗ ((fsp + 0x584#64) ↦₆₄ c23) ∗
        ((fsp + 0x58c#64) ↦₈ c31) =
      pkLayoutAt (fsp + 0x56d#64) c0 c1 c2 c3 c4 c5 c6
        (w0e4.truncate 8) (w0e0.truncate 8) c9 c13 w15 c23 c31 := by
    dsimp only [pkLayoutAt, pkRestAt, sevenBytesHeadAt]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    r1b_ac
  have hspk_w := r1b_spk_pack_words (fsp + 0x4e8#64) spkW0 spkW8 spkW12 spkW16 spkW24
  have hik_w := hikWords (fsp + 0x548#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hspk_w hik_w
  cases opk with
  | none =>
    intro opkFlag bundleV
    have hopk_pack :
        ((fsp + 0x56d#64) ↦₃₂ (c3 ++ c2 ++ c1 ++ c0)) ∗
          ((fsp + 0x571#64) ↦₈ c4) ∗ ((fsp + 0x572#64) ↦₈ c5) ∗ ((fsp + 0x573#64) ↦₈ c6) ∗
          ((fsp + 0x574#64) ↦₈ w0e4.truncate 8) ∗ ((fsp + 0x575#64) ↦₈ w0e0.truncate 8) ∗
          ((fsp + 0x576#64) ↦₃₂ c9) ∗ ((fsp + 0x57a#64) ↦₁₆ c13) ∗
          ((fsp + 0x57c#64) ↦₆₄ w15) ∗ ((fsp + 0x584#64) ↦₆₄ c23) ∗
          ((fsp + 0x58c#64) ↦₈ c31) ⊢
        memRegion (fsp + 0x56d#64) 32 := by
      rw [hlay]
      exact pkLayoutAt_entails_memRegion32 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    refine Entails.trans (r1b_entails_frame (by r1b_ac)
      (sepConj_mono hme_pack (sepConj_mono hback200 hopk_pack)) (by r1b_ac)) ?_
    have hbundle_pack :
        ((fsp + 0x4d0#64) ↦₆₄ 64#64) ∗ ((fsp + 0x4d8#64) ↦₆₄ spkSigPtr) ∗
          ((fsp + 0x4e0#64) ↦₆₄ 64#64) ∗ (spkSigPtr ↦ₛ spkSig) ∗
          ((fsp + 0x4e8#64) ↦₆₄ spkW0) ∗
          ((fsp + 0x4f0#64) ↦₆₄ ((spkW12.zeroExtend 64 <<< 32) ||| spkW8.zeroExtend 64)) ∗
          ((fsp + 0x4f8#64) ↦₆₄ spkW16) ∗ ((fsp + 0x500#64) ↦₆₄ spkW24) ∗
          ((fsp + 0x508#64) ↦₃₂ spkId) ∗ memRegion (fsp + 0x50c#64) 4 ∗
          ((fsp + 0x510#64) ↦₆₄ 64#64) ∗ ((fsp + 0x518#64) ↦₆₄ kpkSigPtr) ∗
          ((fsp + 0x520#64) ↦₆₄ 64#64) ∗ (kpkSigPtr ↦ₛ kpkSig) ∗
          ((fsp + 0x528#64) ↦₆₄ kpkBuf) ∗ ((fsp + 0x530#64) ↦₆₄ 1568#64) ∗ (kpkBuf ↦ₛ kpk) ∗
          ((fsp + 0x538#64) ↦₃₂ kpkId) ∗ memRegion (fsp + 0x53c#64) 4 ∗
          ((fsp + 0x540#64) ↦₃₂ opkFlag) ∗ ((fsp + 0x544#64) ↦₃₂ v11c) ∗
          ((fsp + 0x548#64) ↦₆₄ d.ikW0) ∗ ((fsp + 0x550#64) ↦₆₄ d.ikW1) ∗
          ((fsp + 0x558#64) ↦₆₄ d.ikW2) ∗ ((fsp + 0x560#64) ↦₆₄ d.ikW3) ∗
          ((fsp + 0x568#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗ ((fsp + 0x56c#64) ↦₈ opkFlag.truncate 8) ∗
          memRegion (fsp + 0x56d#64) 32 ∗
          ((fsp + 0x58d#64) ↦₈ d.peerV.device) ∗ memRegion (fsp + 0x58e#64) 2 ⊢
        cliBundleAt (fsp + 0x4d0#64) bundleV spkSigPtr kpkSigPtr kpkBuf := by
      dsimp only [cliBundleAt, bundleV, opkFlag]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      refine Entails.sepExists_right v11c ?_
      refine Entails.pure_right ⟨hlens.1, hlens.2.1, hlens.2.2, by intro p hp; cases hp⟩ ?_
      rw [hspk_bytes, ← hspk_w, ← hik_w]
      exact Entails.of_eq (by r1b_ac)
    exact r1b_entails_frame (by r1b_ac) hbundle_pack (by r1b_ac)
  | some p =>
    rcases p with ⟨opkId_p, k⟩
    intro opkFlag bundleV
    have ⟨hv11c, hkb⟩ := hopk_pk (opkId_p, k) rfl
    have hopk_pack :
        ((fsp + 0x56d#64) ↦₃₂ (c3 ++ c2 ++ c1 ++ c0)) ∗
          ((fsp + 0x571#64) ↦₈ c4) ∗ ((fsp + 0x572#64) ↦₈ c5) ∗ ((fsp + 0x573#64) ↦₈ c6) ∗
          ((fsp + 0x574#64) ↦₈ w0e4.truncate 8) ∗ ((fsp + 0x575#64) ↦₈ w0e0.truncate 8) ∗
          ((fsp + 0x576#64) ↦₃₂ c9) ∗ ((fsp + 0x57a#64) ↦₁₆ c13) ∗
          ((fsp + 0x57c#64) ↦₆₄ w15) ∗ ((fsp + 0x584#64) ↦₆₄ c23) ∗
          ((fsp + 0x58c#64) ↦₈ c31) ⊢
        ((fsp + 0x56d#64) ↦ₛ k.bytes.toList) := by
      rw [hlay, pkLayoutAt_eq_pointsToBytes, ← hkb]
      exact Entails.refl _
    refine Entails.trans (r1b_entails_frame (by r1b_ac)
      (sepConj_mono hme_pack (sepConj_mono hback200 hopk_pack)) (by r1b_ac)) ?_
    have hbundle_pack :
        ((fsp + 0x4d0#64) ↦₆₄ 64#64) ∗ ((fsp + 0x4d8#64) ↦₆₄ spkSigPtr) ∗
          ((fsp + 0x4e0#64) ↦₆₄ 64#64) ∗ (spkSigPtr ↦ₛ spkSig) ∗
          ((fsp + 0x4e8#64) ↦₆₄ spkW0) ∗
          ((fsp + 0x4f0#64) ↦₆₄ ((spkW12.zeroExtend 64 <<< 32) ||| spkW8.zeroExtend 64)) ∗
          ((fsp + 0x4f8#64) ↦₆₄ spkW16) ∗ ((fsp + 0x500#64) ↦₆₄ spkW24) ∗
          ((fsp + 0x508#64) ↦₃₂ spkId) ∗ memRegion (fsp + 0x50c#64) 4 ∗
          ((fsp + 0x510#64) ↦₆₄ 64#64) ∗ ((fsp + 0x518#64) ↦₆₄ kpkSigPtr) ∗
          ((fsp + 0x520#64) ↦₆₄ 64#64) ∗ (kpkSigPtr ↦ₛ kpkSig) ∗
          ((fsp + 0x528#64) ↦₆₄ kpkBuf) ∗ ((fsp + 0x530#64) ↦₆₄ 1568#64) ∗ (kpkBuf ↦ₛ kpk) ∗
          ((fsp + 0x538#64) ↦₃₂ kpkId) ∗ memRegion (fsp + 0x53c#64) 4 ∗
          ((fsp + 0x540#64) ↦₃₂ opkFlag) ∗ ((fsp + 0x544#64) ↦₃₂ v11c) ∗
          ((fsp + 0x548#64) ↦₆₄ d.ikW0) ∗ ((fsp + 0x550#64) ↦₆₄ d.ikW1) ∗
          ((fsp + 0x558#64) ↦₆₄ d.ikW2) ∗ ((fsp + 0x560#64) ↦₆₄ d.ikW3) ∗
          ((fsp + 0x568#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗ ((fsp + 0x56c#64) ↦₈ opkFlag.truncate 8) ∗
          ((fsp + 0x56d#64) ↦ₛ k.bytes.toList) ∗
          ((fsp + 0x58d#64) ↦₈ d.peerV.device) ∗ memRegion (fsp + 0x58e#64) 2 ⊢
        cliBundleAt (fsp + 0x4d0#64) bundleV spkSigPtr kpkSigPtr kpkBuf := by
      dsimp only [cliBundleAt, bundleV, opkFlag]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      refine Entails.sepExists_right v11c ?_
      refine Entails.pure_right ⟨hlens.1, hlens.2.1, hlens.2.2,
        by intro p hp; cases hp; exact hv11c⟩ ?_
      rw [hspk_bytes, ← hspk_w, ← hik_w]
      exact Entails.of_eq (by r1b_ac)
    exact r1b_entails_frame (by r1b_ac) hbundle_pack (by r1b_ac)

set_option maxHeartbeats 800000 in
theorem r1b_step_init2_27bc_placed_aux [LibsignalPlacement] {M : AllocCostModel}
    {S : RunSem} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {r0 r1 r2 r3 : BitVec 8}
    {spk : PublicKey} {kpk : List (BitVec 8)}
    {spkSig kpkSig : List (BitVec 8)}
    {spkSigPtr kpkSigPtr kpkBuf : BitVec 64}
    {spkW0 : BitVec 64} {spkW8 spkW12 : BitVec 32} {spkW16 spkW24 : BitVec 64}
    {spkId kpkId v11c : BitVec 32}
    {opk : Option (BitVec 32 × PublicKey)}
    {c0 c1 c2 c3 c4 c5 c6 : BitVec 8}
    {w0e0 w0e4 c9 : BitVec 32} {c13 : BitVec 16} {w15 c23 : BitVec 64} {c31 : BitVec 8}
    {kpkPtr v130 kpkCap spkPtr spkCap regCap regPtr : BitVec 64}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hok : r1b_OkCtxPlaced r1b_CodeOk S g d s0 s 0x27bc)
    (hbundle : readBundleV (runFiles g.i) d.dir d.peerV.device = some {
      idKey := d.idKey, regId := ofLe32 r0 r1 r2 r3, device := d.peerV.device,
      spkId := spkId, spk := spk, spkSig := spkSig,
      kpkId := kpkId, kpk := kpk, kpkSig := kpkSig, opk := opk
    })
    (hspk_bytes : spk.bytes.toList = r1b_spkBytesOf spkW0 spkW8 spkW12 spkW16 spkW24)
    (hptrs : spkSigPtr ≠ 0 ∧ kpkSigPtr ≠ 0 ∧ kpkBuf ≠ 0)
    (hlens : spkSig.length = 64 ∧ kpkSig.length = 64 ∧ kpk.length = 1568)
    (hopk_pk : ∀ p, opk = some p → v11c = p.1 ∧
      p.2.bytes.toList = pkBytesOf c0 c1 c2 c3 c4 c5 c6
        (w0e4.truncate 8) (w0e0.truncate 8) c9 c13 w15 c23 c31)
    (hx23 : s.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64)
    (hx24 : s.readReg64 (.gpr 24#5) = (spkW12.zeroExtend 64) <<< 32)
    (hx25 : s.readReg64 (.gpr 25#5) = (if opk.isSome then 1#32 else 0#32).zeroExtend 64)
    (hx26 : s.readReg64 (.gpr 26#5) = (if opk.isSome then 1#32 else 0#32).zeroExtend 64)
    (hx28 : s.readReg64 (.gpr 28#5) = 64#64)
    (hnext : ∀ (s2 : State) (d2 : Init2Data),
      AtInit2Placed r1b_CodeOk g d2 s0 s2 →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s2
        (init2MemPlaced A lim st g d2 s0 s2 resStack) Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (memRegion (fsp + 0x4d0#64) 48 ∗
        A.live spkSigPtr 64 1 ∗ (spkSigPtr ↦ₛ spkSig) ∗
        A.live kpkSigPtr 64 1 ∗ (kpkSigPtr ↦ₛ kpkSig) ∗
        A.live kpkBuf 1568 1 ∗ (kpkBuf ↦ₛ kpk) ∗
        r1b_invCoreBase_placed A.repAlloc g d s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
        r1b_opkStage3At fsp spkW0 spkW8 spkW16 spkW24
          c0 c1 c2 c3 c4 c5 c6 w0e0 w0e4 c9 c13 w15 c23 c31 ∗
        ((fsp + 0x110#64) ↦₆₄ spkSigPtr) ∗ ((fsp + 0x11c#64) ↦₃₂ v11c) ∗
        ((fsp + 0x120#64) ↦₆₄ 64#64) ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
        ((fsp + 0x130#64) ↦₆₄ v130) ∗
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
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s)
      Q Qp oom := by
  intro fsp
  let _ := hx23; let _ := hx24; let _ := hx25; let _ := hx26; let _ := hx28
  have hst := hok.st
  have hs_run : s.status = .Running := hst.run
  have hs_sp : s.sp = fsp := hst.sp
  let _ := hs_run; let _ := hs_sp
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hst.spAligned
  have hal1fc : (fsp + 0x1fc#64) &&& 1#64 = 0#64 :=
    (fun (x : BitVec 64) (hx : x &&& 15#64 = 0#64) =>
      show (x + 0x1fc#64) &&& 1#64 = 0#64 by bv_bits) fsp hal
  have hal57a : (fsp + 0x57a#64) &&& 1#64 = 0#64 :=
    (fun (x : BitVec 64) (hx : x &&& 15#64 = 0#64) =>
      show (x + 0x57a#64) &&& 1#64 = 0#64 by bv_bits) fsp hal
  let _ := hal; let _ := hal1fc; let _ := hal57a
  dsimp only [r1b_invCoreBase_placed, r1b_opkStage3At]
  rw [show runFsp s0 = fsp from rfl]
  have h000 : memRegion fsp 0x0e0 =
      (∃∗ v0 : BitVec 32, (fsp ↦₃₂ v0) ∗ memRegion (fsp + 0x004#64) 0x0dc) := by
    rw [memRegion_split fsp 4 0x0dc (by decide), memRegion_four fsp, sepExists_sepConj_left]
  have h2c0 : memRegion (fsp + 0x2c0#64) 0x210 =
      ∃∗ t0 : BitVec 64, ∃∗ t1 : BitVec 64, ∃∗ t2 : BitVec 64, ∃∗ t3 : BitVec 64,
        memRegion (fsp + 0x2c0#64) 0x60 ∗
          ((fsp + 0x320#64) ↦₆₄ t0) ∗ ((fsp + 0x328#64) ↦₆₄ t1) ∗
          ((fsp + 0x330#64) ↦₆₄ t2) ∗ ((fsp + 0x338#64) ↦₆₄ t3) ∗
          memRegion (fsp + 0x340#64) 0x190 := by
    have c320 := r1b_region16_to_cells (fsp + 0x320#64)
    have c330 := r1b_region16_to_cells (fsp + 0x330#64)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at c320 c330
    rw [r1b_split_region fsp 0x2c0 0x60 0x1b0,
      r1b_split_region fsp 0x320 0x10 0x1a0,
      r1b_split_region fsp 0x330 0x10 0x190, c320, c330]
    simp only [sepConj_assoc, sepExists_sepConj_left, r1b_exR_64, r1b_exR_reg]
  have h500 : memRegion (fsp + 0x500#64) 0x1250 =
      memRegion (fsp + 0x500#64) 0x90 ∗ memRegion (fsp + 0x590#64) 0x11c0 :=
    r1b_split_region fsp 0x500 0x90 0x11c0
  rw [h500]
  have hfreeze :
      (A.live spkSigPtr 64 1 ∗ (spkSigPtr ↦ₛ spkSig) ∗
        A.live kpkSigPtr 64 1 ∗ (kpkSigPtr ↦ₛ kpkSig) ∗
        A.live kpkBuf 1568 1 ∗ (kpkBuf ↦ₛ kpk) ∗
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        coinsInstalledPlaced g.coins (coinsOf g.i) ∗
        tokenInitPlacedAt ∗
        addrNameHeap A.repAlloc d.meG ∗ runSaved s0 ∗
        protocolAddressAt A.repAlloc d.peerG (fsp + 0x2a0#64) ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗
        ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s) ⊢
      r1b_init2Frozen_placed A lim st s g d s0 fsp resStack
        spkSigPtr kpkSigPtr kpkBuf spkSig kpkSig kpk :=
    Entails.refl _
  refine r1b_sepWPp_frame (by r1b_ac) hfreeze (by r1b_ac) ?_
  refine r1b_sepWPp_frame (by r1b_ac) (r1b_addrUpperAt_to_words (fsp + 0x260#64) d.meG) (by r1b_ac) ?_
  refine r1b_sepWPp_exists_left fun w268 => ?_
  conv => arg 4; rw [show fsp + 0x260#64 + 8#64 = fsp + 0x268#64 from by bv_omega, sepConj_assoc]
  refine r1b_sepWPp_pure_left fun hw268 => ?_
  refine r1b_sepWPp_frame (by r1b_ac) (r1b_open_bundle_dest fsp) (by r1b_ac) ?_
  refine r1b_sepWPp_exists_left fun m4d0 => r1b_sepWPp_exists_left fun m4d8 =>
    r1b_sepWPp_exists_left fun m4e0 => r1b_sepWPp_exists_left fun m4e8 =>
    r1b_sepWPp_exists_left fun m4f0 => r1b_sepWPp_exists_left fun m4f8 =>
    r1b_sepWPp_exists_left fun m500 => r1b_sepWPp_exists_left fun m508 =>
    r1b_sepWPp_exists_left fun m510 => r1b_sepWPp_exists_left fun m518 =>
    r1b_sepWPp_exists_left fun m520 => r1b_sepWPp_exists_left fun m528 =>
    r1b_sepWPp_exists_left fun m530 => r1b_sepWPp_exists_left fun m538 =>
    r1b_sepWPp_exists_left fun m540 => r1b_sepWPp_exists_left fun m544 =>
    r1b_sepWPp_exists_left fun m548 => r1b_sepWPp_exists_left fun m550 =>
    r1b_sepWPp_exists_left fun m558 => r1b_sepWPp_exists_left fun m560 =>
    r1b_sepWPp_exists_left fun m568 => r1b_sepWPp_exists_left fun m56c =>
    r1b_sepWPp_exists_left fun d0 => r1b_sepWPp_exists_left fun d1 =>
    r1b_sepWPp_exists_left fun d2_b => r1b_sepWPp_exists_left fun d3 =>
    r1b_sepWPp_exists_left fun m574 => r1b_sepWPp_exists_left fun m575 =>
    r1b_sepWPp_exists_left fun m576 => r1b_sepWPp_exists_left fun m57a =>
    r1b_sepWPp_exists_left fun m57c => r1b_sepWPp_exists_left fun m584 =>
    r1b_sepWPp_exists_left fun m58c => r1b_sepWPp_exists_left fun m58d => ?_
  refine r1b_sepWPp_frame (by r1b_ac) (Entails.of_eq h000) (by r1b_ac) ?_
  refine r1b_sepWPp_exists_left fun v000 => ?_
  refine r1b_sepWPp_frame (by r1b_ac) (Entails.of_eq h2c0) (by r1b_ac) ?_
  refine r1b_sepWPp_exists_left fun t0 => r1b_sepWPp_exists_left fun t1 =>
    r1b_sepWPp_exists_left fun t2 => r1b_sepWPp_exists_left fun t3 => ?_
  have hfreeze_regs :
      (memRegion (fsp + 0x004#64) 0x0dc ∗ memRegion (fsp + 0x1b4#64) 4 ∗
        memRegion (fsp + 0x1d0#64) 0x18 ∗ memRegion (fsp + 0x1f1#64) 7 ∗
        memRegion (fsp + 0x1fe#64) 2 ∗ memRegion (fsp + 0x207#64) 0x19 ∗
        memRegion (fsp + 0x220#64) 0x40 ∗ memRegion (fsp + 0x2c0#64) 0x60 ∗
        memRegion (fsp + 0x340#64) 0x190 ∗ memRegion (fsp + 0x50c#64) 4 ∗
        memRegion (fsp + 0x53c#64) 4 ∗ memRegion (fsp + 0x58e#64) 2 ∗
        memRegion (fsp + 0x590#64) 0x11c0 ∗ memRegion (fsp + 0x1750#64) 24) ⊢
      r1b_init2RegsFrozen fsp := Entails.refl _
  refine r1b_sepWPp_frame (by r1b_ac) hfreeze_regs (by r1b_ac) ?_
  have hpc0 := hst.pc
  change s.pc = (blkPl_579).base + 0x27bc#64 at hpc0
  conv => arg 4; dsimp only [sevenBytesHeadAt]; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x2898#64) hst.inv
  dsimp only [runProgPlaced, lsProg_579]
  apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
    blkLib_eq_579 blk579_noSvc0 (mid := (blkPl_579).base + 0x2898#64)
  intro _m_strip1
  have hpc := hpc0; have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
  wp_steps
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
    (by simp only [wp_norm, arm64_norm, *]) fun _m_real1 hnsp1 => ?_
  have hvmp1 : VmPreserved s _ :=
    hnsp1.toVmPreserved (by simp only [wp_norm, arm64_norm])
  try simp only [State.setMem_setMem] at hvmp1 ⊢
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
  clear hpc hrun hsp
  refine r1b_bind_state_placed fun sm1 hsm1 hinv1 => ?_
  have hvm1 : VmPreserved s sm1 := hsm1 ▸ hvmp1
  change SepWPp (runProgPlaced H) _ _ _ _ _ _
  try (conv => arg 4; simp only [wp_norm, arm64_norm, hok.x21, hok.x22, hx23, hx24, hx25, hx26, hx28,
    r1b_bv128_truncate_append, r1b_bv128_extractLsb'_append])
  have hflip200 :
      ((fsp + 0x200#64) ↦₃₂ (c3 ++ c2 ++ c1 ++ c0)) ∗
        ((fsp + 0x204#64) ↦₈ c4) ∗ ((fsp + 0x205#64) ↦₈ c5) ∗
        ((fsp + 0x206#64) ↦₈ c6) ⊢
      ((fsp + 0x200#64) ↦₈ c0) ∗ ((fsp + 0x201#64) ↦₈ c1) ∗
        ((fsp + 0x202#64) ↦₈ c2) ∗
        ((fsp + 0x203#64) ↦₃₂ (c6 ++ c5 ++ c4 ++ c3)) := by
    have heq := sevenBytesHeadAt_eq_tailAt (fsp + 0x200#64) c0 c1 c2 c3 c4 c5 c6
    dsimp only [sevenBytesHeadAt, sevenBytesTailAt] at heq
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at heq
    rw [heq]; exact Entails.refl _
  refine r1b_sepWPp_frame (by r1b_ac) hflip200 (by r1b_ac) ?_
  conv => arg 4; rw [sepConj_assoc, sepConj_assoc, sepConj_assoc]
  apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x28a4#64) hinv1
  dsimp only [runProgPlaced, lsProg_579]
  apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
    blkLib_eq_579 blk579_noSvc0 (mid := (blkPl_579).base + 0x28a4#64)
  intro _m_strip2
  have hpc : sm1.pc = (blkPl_579).base + 0x2898#64 := by simp [hsm1, wp_norm, arm64_norm]
  have hrun : sm1.status = .Running := by simp [hsm1, wp_norm, arm64_norm, hst.run]
  have hsp : sm1.sp = fsp := by simpa [hsm1, wp_norm, arm64_norm] using hst.sp
  wp_steps
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
    (by simp only [wp_norm, arm64_norm, *]) fun _m_real2 hnsp2 => ?_
  have hvmp2 : VmPreserved sm1 _ :=
    hnsp2.toVmPreserved (by simp only [wp_norm, arm64_norm]; exact hvm1.1.2.2.symm)
  try simp only [State.setMem_setMem] at hvmp2 ⊢
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
  clear hpc hrun hsp
  refine r1b_bind_state_placed fun sm2 hsm2 hinv2 => ?_
  have hvm2 : VmPreserved sm1 sm2 := hsm2 ▸ hvmp2
  change SepWPp (runProgPlaced H) _ _ _ _ _ _
  have hw570 := r1b_trunc32_zext64 (c6 ++ c5 ++ c4 ++ c3)
  let _ := hw570
  try (conv => arg 4; simp only [hsm1, wp_norm, arm64_norm, hw570])
  have hflip56d :
      ((fsp + 0x56d#64) ↦₈ d0) ∗ ((fsp + 0x56e#64) ↦₈ d1) ∗
        ((fsp + 0x56f#64) ↦₈ d2_b) ∗
        ((fsp + 0x570#64) ↦₃₂ (c6 ++ c5 ++ c4 ++ c3)) ⊢
      ((fsp + 0x56d#64) ↦₃₂ (c3 ++ d2_b ++ d1 ++ d0)) ∗
        ((fsp + 0x571#64) ↦₈ c4) ∗ ((fsp + 0x572#64) ↦₈ c5) ∗
        ((fsp + 0x573#64) ↦₈ c6) := by
    have heq := (sevenBytesHeadAt_eq_tailAt (fsp + 0x56d#64) d0 d1 d2_b c3 c4 c5 c6).symm
    dsimp only [sevenBytesHeadAt, sevenBytesTailAt] at heq
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at heq
    rw [heq]; exact Entails.refl _
  refine r1b_sepWPp_frame (by r1b_ac) hflip56d (by r1b_ac) ?_
  conv => arg 4; rw [sepConj_assoc, sepConj_assoc, sepConj_assoc]
  apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x28f0#64) hinv2
  dsimp only [runProgPlaced, lsProg_579]
  apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
    blkLib_eq_579 blk579_noSvc0 (mid := (blkPl_579).base + 0x28f0#64)
  intro _m_strip3
  have hpc : sm2.pc = (blkPl_579).base + 0x28a4#64 := by
    simp [hsm2, hsm1, wp_norm, arm64_norm]
  have hrun : sm2.status = .Running := by
    simp [hsm2, hsm1, wp_norm, arm64_norm, hst.run]
  have hsp : sm2.sp = fsp := by simpa [hsm2, hsm1, wp_norm, arm64_norm] using hst.sp
  have hx10_2 : sm2.readReg64 (.gpr 10#5) = fsp + 0x4d0#64 := by
    simp [hsm2, hsm1, wp_norm, arm64_norm]
  let _ := hx10_2
  wp_steps
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
    (by simp only [wp_norm, arm64_norm, *]) fun _m_real3 hnsp3 => ?_
  have hvmp3 : VmPreserved sm2 _ :=
    hnsp3.toVmPreserved (by simp only [wp_norm, arm64_norm]; exact (hvm1.trans hvm2).1.2.2.symm)
  try simp only [State.setMem_setMem] at hvmp3 ⊢
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
  clear hpc hrun hsp
  refine r1b_bind_state_placed fun sm3 hsm3 hinv3 => ?_
  have hvm3 : VmPreserved sm2 sm3 := hsm3 ▸ hvmp3
  have hvm : VmPreserved s sm3 := hvm1.trans (hvm2.trans hvm3)
  change SepWPp (runProgPlaced H) _ _ _ _ _ _
  let opkFlag : BitVec 32 := if opk.isSome then 1#32 else 0#32
  let bundleV : BundleV := {
    idKey := d.idKey, regId := ofLe32 r0 r1 r2 r3, device := d.peerV.device,
    spkId := spkId, spk := spk, spkSig := spkSig,
    kpkId := kpkId, kpk := kpk, kpkSig := kpkSig, opk := opk
  }
  let d2 : Init2Data := {
    peerV := d.peerV, peerG := d.peerG, meV := d.meV, meG := d.meG,
    dir := d.dir, dirCap := d.dirCap, dirPtr := d.dirPtr,
    bundle := bundleV,
    spkSigPtr := spkSigPtr, kpkSigPtr := kpkSigPtr, kpkPtr := kpkBuf
  }
  have hi2 : AtInit2Placed r1b_CodeOk g d2 s0 sm3 := {
    base := {
      pc := by rw [runPcPlaced_eq]; simp [hsm3, hsm2, hsm1, wp_norm, arm64_norm]
      run := by simp [hsm3, hsm2, hsm1, wp_norm, arm64_norm, hst.run]
      sp := by simpa [hsm3, hsm2, hsm1, wp_norm, arm64_norm] using hst.sp
      fp := by simpa [hsm3, hsm2, hsm1, wp_norm, arm64_norm] using hst.fp
      inv := hinv3
      vregs := by simpa [calleeSavedVRegs, hsm3, hsm2, hsm1, wp_norm, arm64_norm] using hst.vregs
      spAligned := hst.spAligned }
    callEq := hok.callEq
    x0 := by simp only [hsm3, hsm2, hsm1, wp_norm, arm64_norm]; dsimp only [fsp, runFsp]; simp only [wp_norm, arm64_norm, r1b_sp_add]
    x1 := by simp only [hsm3, hsm2, hsm1, wp_norm, arm64_norm]; dsimp only [fsp, runFsp]; simp only [wp_norm, arm64_norm, r1b_sp_add]
    x2 := by simpa [hsm3, hsm2, hsm1, wp_norm, arm64_norm] using congrArg (· + 0xf0#64) hok.x19
    x3 := by dsimp only [sessVtPlaced, cliSessionVtSym]; simp only [hsm3, hsm2, hsm1, wp_norm, arm64_norm]
    x4 := by simpa [hsm3, hsm2, hsm1, wp_norm, arm64_norm] using hok.x19
    x5 := by dsimp only [idVtPlaced, cliIdentityVtSym]; simp only [hsm3, hsm2, hsm1, wp_norm, arm64_norm]
    x6 := by simp only [hsm3, hsm2, hsm1, wp_norm, arm64_norm]; dsimp only [fsp, runFsp]; simp only [wp_norm, arm64_norm, r1b_sp_add]
    x7 := by simp [hsm3, hsm2, hsm1, wp_norm, arm64_norm]
    x8 := by simp only [hsm3, hsm2, hsm1, wp_norm, arm64_norm]; dsimp only [fsp, runFsp]; simp only [wp_norm, arm64_norm, r1b_sp_add]
    x19 := by simpa [hsm3, hsm2, hsm1, wp_norm, arm64_norm] using hok.x19
    x20 := by simpa [hsm3, hsm2, hsm1, wp_norm, arm64_norm] using hok.x20
    x21 := by simpa [hsm3, hsm2, hsm1, wp_norm, arm64_norm] using hok.x21
    peerVal := hok.peerVal, meVal := hok.meVal, ownSem := hok.ownSem
    bundleSem := hbundle, ptrsNeZero := hptrs
    trace := by simpa [hsm3, hsm2, hsm1, wp_norm, arm64_norm] using hok.trace
    fs := by simpa [hsm3, hsm2, hsm1, wp_norm, arm64_norm] using hok.fs
    stdout := by simpa [hsm3, hsm2, hsm1, wp_norm, arm64_norm] using hok.stdout }
  refine sepWPp_weaken_pre ?_ (hnext sm3 d2 hi2)
  try (conv => arg 1; simp only [hsm2, hsm1, wp_norm, arm64_norm, hok.x21, hok.x22, hx23,
    hx24, hx25, hx26, hx28, r1b_bv128_truncate_append, r1b_bv128_extractLsb'_append,
    r1b_trunc32_zext64, r1b_trunc8_zext64_32, r1b_trunc8_zext64_8,
    r1b_trunc8_zext64_zext32_8, r1b_trunc16_zext64, r1b_trunc16_zext64_zext32])
  try (conv => arg 1; simp only [r1b_fold_ite_trunc8])
  dsimp only [r1b_init2Frozen_placed, r1b_init2RegsFrozen, opkFlag, bundleV]
  rw [← A.pool_transport lim st s sm3 hvm]
  have hpack := r1b_pack_bundle_and_addr A.repAlloc fsp d (r0 := r0) (r1 := r1) (r2 := r2)
    (r3 := r3) (spk := spk) (kpk := kpk) (spkSig := spkSig) (kpkSig := kpkSig)
    (spkSigPtr := spkSigPtr) (kpkSigPtr := kpkSigPtr) (kpkBuf := kpkBuf) (spkW0 := spkW0)
    (spkW8 := spkW8) (spkW12 := spkW12) (spkW16 := spkW16) (spkW24 := spkW24) (spkId := spkId)
    (kpkId := kpkId) (v11c := v11c) (opk := opk) (c0 := c0) (c1 := c1) (c2 := c2) (c3 := c3)
    (c4 := c4) (c5 := c5) (c6 := c6) (w0e0 := w0e0) (w0e4 := w0e4) (c9 := c9) (c13 := c13)
    (w15 := w15) (c23 := c23) (c31 := c31) (w268 := w268) hw268 hok.ikWords hspk_bytes hlens hopk_pk
  dsimp only [Option.isSome] at hpack
  refine Entails.trans (r1b_entails_frame (by r1b_ac) hpack (by r1b_ac)) ?_
  have hrejoin := r1b_rejoin_init2Locals A.repAlloc fsp d2 w0e0 w0e4 c9 v11c
    (ofLe32 r0 r1 r2 r3) (d.peerV.device.zeroExtend 32) c13 w15 spkW0 spkW16 spkW24 spkW8
    c0 c1 c2 c3 c4 c5 c6 c31 c23 kpkPtr v130 64#64 kpkCap spkPtr spkCap regCap regPtr
    d.ikW0 (spkId.zeroExtend 64) d.ikW3 d.ikW1 (BitVec.ofNat 64 d.meG.name.bytes.length) w268
  dsimp only [d2, bundleV] at hrejoin; rw [init2MemPlaced_atState_eq]; dsimp only [d2, bundleV]
  try rw [show runFsp s0 = fsp from rfl]
  exact r1b_entails_frame (by r1b_ac) hrejoin (by r1b_ac)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1bProofPlacedBudgetAux
