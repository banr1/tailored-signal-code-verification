/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all Init.Data.String.Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.WorkFrame
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSites
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpk
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

/-!
# Stage 1 Spine (`registration-id` and `signed-pre-key`) of Arm `R1b` (`0x074c → 0x1260`)
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton

local macro "r1b_ac0" : tactic =>
  `(tactic| ((try dsimp +zetaDelta only) <;> first | rfl | simp only [emp_sepConj] | with_reducible ac_rfl | ac_rfl))

private meta def r1bStripLets0 : Nat → Lean.Expr → Lean.Expr
  | 0, e => e
  | n + 1, .letE _ _ v b _ => r1bStripLets0 n (b.instantiate1 v)
  | n + 1, .mdata _ e => r1bStripLets0 n e
  | _, e => e

private meta def r1bSplitSep0 : Nat → Lean.Expr → Lean.Expr → Array Lean.Expr
  | 0, _, e => #[e]
  | fuel + 1, sepSample, e =>
    let e := r1bStripLets0 64 e
    let fn := sepSample.getAppFn.constName!
    let ar := sepSample.getAppNumArgs
    if e.isAppOfArity fn ar then
      r1bSplitSep0 fuel sepSample (e.getArg! (ar - 2)) ++
        r1bSplitSep0 fuel sepSample (e.getArg! (ar - 1))
    else #[e]

private meta def r1bIsDefEqPure0 (x a : Lean.Expr) : Lean.Elab.TermElabM Bool := do
  let x := r1bStripLets0 64 x; let a := r1bStripLets0 64 a
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

private meta def r1bComputeRest0 (ctxName : String) (p a1 : Lean.Expr) : Lean.Elab.TermElabM Lean.Expr := do
  let sepTy := Lean.mkConst ``SepProp []
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let ps := (r1bSplitSep0 64 sepSample (← Lean.instantiateMVars p)).toList
  let a1s := (r1bSplitSep0 64 sepSample (← Lean.instantiateMVars a1)).toList
  let mut rem := ps
  for a in a1s do
    let mut removed := false
    let mut next : List Lean.Expr := []
    for x in rem do
      if !removed && (← r1bIsDefEqPure0 x a) then removed := true
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

local elab "r1b_entails_frame0 " t1:term:arg h:term:arg t2:term:arg : term <= expectedType => do
  let exp ← Lean.instantiateMVars expectedType
  if exp.isMVar then Lean.Elab.Term.tryPostpone
  let entSample ← Lean.Elab.Term.elabTerm (← `(emp ⊢ emp)) none
  let ear := entSample.getAppNumArgs
  let expS := r1bStripLets0 64 exp
  let p := expS.getArg! (ear - 2)
  let q := expS.getArg! (ear - 1)
  if (← Lean.instantiateMVars p).isMVar then Lean.Elab.Term.tryPostpone
  if (← Lean.instantiateMVars q).isMVar then Lean.Elab.Term.tryPostpone
  let hExpr ← Lean.Elab.Term.elabTerm h none
  let hTy := r1bStripLets0 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
  let a1 := hTy.getArg! (ear - 2)
  let a2 := hTy.getArg! (ear - 1)
  let r ← r1bComputeRest0 "r1b_entails_frame0" p a1
  let sepTy := Lean.mkConst ``SepProp []
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let sar := sepSample.getAppNumArgs
  let mkSep (x y : Lean.Expr) : Lean.Expr :=
    sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
  let rIsEmp ← r1bIsDefEqPure0 r empExpr
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

local elab "r1b_sepWPp_frame0 " t1:term:arg h:term:arg t2:term:arg hk:term:arg : term <= expectedType => do
  let exp ← Lean.instantiateMVars expectedType
  if exp.isMVar then Lean.Elab.Term.tryPostpone
  let expS := r1bStripLets0 64 exp
  let args := expS.getAppArgs
  let prog := args[0]!; let ret := args[1]!; let st := args[2]!; let p := args[3]!
  let q := args[4]!; let qp := args[5]!; let oom := args[6]!
  let entSample ← Lean.Elab.Term.elabTerm (← `(emp ⊢ emp)) none
  let ear := entSample.getAppNumArgs
  let hExpr ← Lean.Elab.Term.elabTerm h none
  let hTy := r1bStripLets0 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
  let a1 := hTy.getArg! (ear - 2)
  let a2 := hTy.getArg! (ear - 1)
  let r ← r1bComputeRest0 "r1b_sepWPp_frame0" p a1
  let sepTy := Lean.mkConst ``SepProp []
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let sar := sepSample.getAppNumArgs
  let mkSep (x y : Lean.Expr) : Lean.Expr :=
    sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
  let rIsEmp ← r1bIsDefEqPure0 r empExpr
  if rIsEmp then
    let eq1 ← Lean.Meta.mkEq p a1
    let eq2 ← Lean.Meta.mkEq a2 a2
    let h1Expr ← Lean.Elab.Term.elabTerm t1 (some eq1)
    let h2Expr ← Lean.Elab.Term.elabTerm t2 (some eq2)
    let hkTy := Lean.mkAppN expS.getAppFn #[prog, ret, st, a2, q, qp, oom]
    let hkExpr ← Lean.Elab.Term.elabTerm hk (some hkTy)
    let hent ← Lean.Meta.mkAppM ``Entails.trans #[← Lean.Meta.mkAppM ``Entails.of_eq #[h1Expr],
      ← Lean.Meta.mkAppM ``Entails.trans #[hExpr, ← Lean.Meta.mkAppM ``Entails.of_eq #[h2Expr]]]
    Lean.Meta.mkAppM ``MainHops.sepWPp_weaken_pre #[hent, hkExpr]
  else
    let a2IsEmp ← r1bIsDefEqPure0 a2 empExpr
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

local elab:10 "r1b_call_frame0" "<|" h:term:10 : term <= expectedType => do
    let exp ← Lean.instantiateMVars expectedType
    if exp.isMVar then Lean.Elab.Term.tryPostpone
    let expS := r1bStripLets0 64 exp
    let hExpr ← Lean.Elab.Term.elabTerm h none
    let hTy0 := r1bStripLets0 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
    for idx in [0, 1, 2, 4, 5, 6] do
      if !(← Lean.Meta.withReducibleAndInstances <| Lean.Meta.isDefEq (hTy0.getArg! idx) (expS.getArg! idx)) then
        discard <| Lean.Meta.isDefEq (hTy0.getArg! idx) (expS.getArg! idx)
    let p ← Lean.instantiateMVars (expS.getArg! 3)
    let p' ← Lean.instantiateMVars ((r1bStripLets0 64 (← Lean.instantiateMVars hTy0)).getArg! 3)
    let sepTy := Lean.mkConst ``SepProp []
    let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
    let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
    let sar := sepSample.getAppNumArgs
    let mkSep (x y : Lean.Expr) : Lean.Expr :=
      sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
    let ps := (r1bSplitSep0 64 sepSample p).toList
    let p's := (r1bSplitSep0 64 sepSample p').toList
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
        if !removed && (← r1bIsDefEqPure0 x a) then removed := true
        else next := next.concat x
      if !removed then
        throwError "r1b_call_frame0: unmatched callee atom:\n  {a}\nin:\n  {rem}"
      rem := next
    let remProd := match rem.reverse with
      | [] => empExpr
      | last :: rest => rest.foldl (fun acc x => mkSep x acc) last
    if let some mf := mvarFOpt then
      discard <| Lean.Meta.withReducibleAndInstances <| Lean.Meta.isDefEq mf remProd
    let eqTy ← Lean.Meta.mkEq (← Lean.instantiateMVars p) (← Lean.instantiateMVars p')
    let eqProof ← Lean.Elab.Term.elabTerm (← `(by r1b_ac0)) (some eqTy)
    let ent ← Lean.Meta.mkAppM ``Entails.of_eq #[eqProof]
    Lean.Meta.mkAppM ``MainHops.sepWPp_weaken_pre #[ent, hExpr]

theorem r1b_cells3_to_region24 (a v0 v1 v2 : BitVec 64) :
    ((a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2)) ⊢ memRegion a 24 := by
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right
    (pointsTo64_entails_memRegion _ _))) ?_
  refine Entails.trans (sepConj_mono_right
    (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      r1b_cell64_cons (a := a + 8#64) v1 (n := 8) (by decide))) ?_
  simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
    r1b_cell64_cons (a := a) v0 (n := 16) (by decide)

theorem r1b_ofNat64_ne4 {n : Nat} (hlt : n < 2 ^ 63) (hne : n ≠ 4) :
    (BitVec.ofNat 64 n == 4#64) = false := by
  apply beq_false_of_ne
  intro h
  have hn : (BitVec.ofNat 64 n).toNat = (4#64).toNat := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at hn
  omega


set_option maxHeartbeats 600000 in
private theorem r1b_spk_dealloc_11f4 {S : RunSem} {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {r0 r1 r2 r3 : BitVec 8}
    {pCap pPtr regCap regPtr spkCap spkPtr : BitVec 64}
    {pBs spkBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext) (hdrop : RunDrop.DropSpeOwnedOk img A ext)
    (hbnd : r1b_StackBounds B resStack)
    (hok : r1b_OkCtx S img ext g d s0 s 0x11f4)
    (hreg_rd : cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") =
      .ok [r0, r1, r2, r3])
    (hspk_rd : cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") = .ok spkBs)
    (hx27 : s.readReg64 (.gpr 27#5) = pPtr)
    (hx23 : s.readReg64 (.gpr 23#5) = spkCap)
    (hx9 : s.readReg64 (.gpr 9#5) = spkPtr)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 spkBs.length)
    (hx12 : s.readReg64 (.gpr 12#5) = 0xfffffffffffffffe#64)
    (hx26 : s.readReg64 (.gpr 26#5) = d.dirPtr)
    (hx28 : s.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length)
    (hpanic : PanicK g s0 Qp) (hrej : RejectK img ext A g s0 resStack Q Qp)
    (hk : ∀ (sf : State) (spkId : BitVec 32) (spkKey spkSig : List (BitVec 8)),
      r1b_OkCtx S img ext g d s0 sf 0x1260 →
      splitSigned spkBs = some (spkId, spkKey, spkSig) →
      sf.readReg64 (.gpr 10#5) = spkPtr + 4#64 →
      sf.readReg64 (.gpr 27#5) = BitVec.ofNat 64 spkKey.length →
      sf.readReg64 .x2 = spkId.zeroExtend 64 →
      sf.readReg64 (.gpr 26#5) = d.dirPtr →
      sf.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length →
      let fsp := runFsp s0
      SepWPp (mProg img ext) (s0.readReg64 .lr) sf
        (((fsp + 0x4f0#64) ↦₆₄ (spkPtr + 4#64 + BitVec.ofNat 64 spkKey.length)) ∗
          ((fsp + 0x4f8#64) ↦₆₄ 64#64) ∗
          memRegion (fsp + 0x4d0#64) 32 ∗
          ownedBytes A spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
          ownedBytes A regCap regPtr 4#64 [r0, r1, r2, r3] ∗
          r1b_invCore A img g d s0 ∗ logOff img ∗
          ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
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
          stackAt fsp (resStack - runFrame) ∗ A.pool)
        Q Qp (runOom s0)) :
    let fsp := runFsp s0
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (((fsp + 0x4d0#64) ↦₆₄ pCap) ∗ memRegion (fsp + 0x4d8#64) 40 ∗
        ownedBytes A pCap pPtr (BitVec.ofNat 64 pBs.length) pBs ∗
        ownedBytes A spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
        ownedBytes A regCap regPtr 4#64 [r0, r1, r2, r3] ∗
        r1b_invCore A img g d s0 ∗ logOff img ∗
        ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
        memRegion fsp 0x110 ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
        memRegion (fsp + 0x150#64) 16 ∗
        ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
        memRegion (fsp + 0x168#64) 8 ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        memRegion (fsp + 0x188#64) 8 ∗ ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
        ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
        memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool)
      Q Qp (runOom s0) := by
  intro fsp
  let _ := hx27; let _ := hx23; let _ := hx9; let _ := hx2; let _ := hx12; let _ := hx26; let _ := hx28
  generalize hinvCore : r1b_invCore A img g d s0 = invCore
  have hst := hok.st
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hst.spAligned
  code_fetches_range CryptoVerification.libsignalSessionCode r1bDecRegSpk img.base
    (Rust.withPanics ext) r1b_run_fnOff (num% (ls_off% "libsignal_cli::run")) 0x11f4 0x3c
  have hpc_in := hst.pc
  dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc_in ⊢
  generalize_entry heq_fnBase :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase
  examples_hide_fetches
  by_cases hpCap : pCap = 0#64
  · subst hpCap
    have hpc := hpc_in; have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
    apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x1230#64) hst.inv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state fun sm1 hsm1 hinv1 => ?_
    change SepWPp (mProg img ext) _ _ _ _ _ _
    have hok1 : r1b_OkCtx S img ext g d s0 sm1 0x1230 := hok.of_step
      { pc := by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm1, arm64_norm]
        run := by simp [hsm1, arm64_norm, hst.run]
        sp := by simpa [hsm1, arm64_norm] using hst.sp
        fp := by simpa [hsm1, arm64_norm] using hst.fp
        inv := hinv1
        vregs := by simpa [calleeSavedVRegs, hsm1, arm64_norm] using hst.vregs
        spAligned := hst.spAligned }
      (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
      (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
      (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
    have h4d0 : ((fsp + 0x4d0#64) ↦₆₄ 0#64) ∗ memRegion (fsp + 0x4d8#64) 40 ⊢
        memRegion (fsp + 0x4d0#64) 48 := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
        r1b_cell64_cons (a := fsp + 0x4d0#64) 0#64 (n := 40) (by decide)
    have h0own : ownedBytes A 0#64 pPtr (BitVec.ofNat 64 pBs.length) pBs ⊢ emp :=
      r1b_ownedBytes_zero A pPtr _ pBs
    refine r1b_sepWPp_frame0 (by r1b_ac0) h0own (by simp only [emp_sepConj]) ?_
    refine MainHops.sepWPp_weaken_pre ?_
      (r1b_after_spk_dealloc himg hh hdrop hbnd hok1 hreg_rd hspk_rd
        (by simp only [hsm1, arm64_norm]; try exact hx23)
        (by simp only [hsm1, arm64_norm]; try exact hx9)
        (by simp only [hsm1, arm64_norm]; try exact hx2)
        (by simp only [hsm1, arm64_norm]; try exact hx26)
        (by simp only [hsm1, arm64_norm]; try exact hx28)
        hpanic hrej hk)
    try dsimp only
    rw [hinvCore]
    exact r1b_entails_frame0 (by r1b_ac0) h4d0 (by r1b_ac0)
  · have hpCap_f : (pCap == 0#64) = false := beq_false_of_ne hpCap
    let _ := hpCap_f
    rw [ProofLib.memRegion_eight (fsp + 0x188#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun _v188 => ?_
    have hpc := hpc_in; have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
    apply MainHops.sepWPp_seq_inImage
      (mid := fnBase + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_cli::run"))
      hst.inv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state fun sm1 hsm1 hinv1 => ?_
    change SepWPp (mProg img ext) _ _ _ _ _ _
    refine r1b_call_frame0 <|
      r1b_call_dealloc_ownedBytes (ptr := pPtr) (cap := pCap) (bs := pBs) hh hbnd hinv1
        (by dsimp only [mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm1, arm64_norm])
        (by simp [hsm1, arm64_norm, hst.run])
        (by simpa [hsm1, arm64_norm] using hst.sp)
        (by simpa [hsm1, arm64_norm] using hst.fp)
        (by simpa [calleeSavedVRegs, hsm1, arm64_norm] using hst.vregs)
        hst.spAligned (retOff := 0x121c)
        (by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm1, arm64_norm])
        (by simp only [hsm1, arm64_norm]; try exact hx27)
        (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm]) hpCap hpanic
        fun sf1 hin1 hcs1 hfs1 htr1 => ?_
    have hok1 : r1b_OkCtx S img ext g d s0 sf1 0x121c := hok.after_call
      (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
      (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
      (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
      hin1 hcs1 (congrArg FsState.files hfs1) htr1
    have hx23_1 : sf1.readReg64 (.gpr 23#5) = BitVec.ofNat 64 spkBs.length :=
      hcs1.2.2.2.2.1.trans (by simp only [hsm1, arm64_norm]; try exact hx2)
    have hx25_1 : sf1.readReg64 (.gpr 25#5) = d.dirPtr :=
      hcs1.2.2.2.2.2.2.1.trans (by simp only [hsm1, arm64_norm]; try exact hx26)
    have hx26_1 : sf1.readReg64 (.gpr 26#5) = 0xfffffffffffffffe#64 :=
      hcs1.2.2.2.2.2.2.2.1.trans (by simp only [hsm1, arm64_norm]; try exact hx12)
    have hx27_1 : sf1.readReg64 (.gpr 27#5) = spkPtr :=
      hcs1.2.2.2.2.2.2.2.2.1.trans (by simp only [hsm1, arm64_norm]; try exact hx9)
    have hx28_1 : sf1.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length :=
      hcs1.2.2.2.2.2.2.2.2.2.1.trans (by simp only [hsm1, arm64_norm]; try exact hx28)
    let _ := hx23_1; let _ := hx25_1; let _ := hx26_1; let _ := hx27_1; let _ := hx28_1
    have hv188 : ((fsp + 0x188#64) ↦₆₄ s.readReg64 (.gpr 23#5)) = ((fsp + 0x188#64) ↦₆₄ spkCap) :=
      congrArg ((fsp + 0x188#64) ↦₆₄ ·) hx23
    try rw [hv188]
    have hpc1 := hin1.pc
    dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc1 ⊢
    rw [heq_fnBase] at hpc1
    have hpc := hpc1; have hrun := hin1.run; have hsp : sf1.sp = fsp := hin1.sp
    apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x1230#64) hin1.inv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state fun sm2 hsm2 hinv2 => ?_
    change SepWPp (mProg img ext) _ _ _ _ _ _
    have hok2 : r1b_OkCtx S img ext g d s0 sm2 0x1230 := hok1.of_step
      { pc := by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm2, arm64_norm]
        run := by simp [hsm2, arm64_norm, hin1.run]
        sp := by simpa [hsm2, arm64_norm] using hin1.sp
        fp := by simpa [hsm2, arm64_norm] using hin1.fp
        inv := hinv2
        vregs := by simpa [calleeSavedVRegs, hsm2, arm64_norm] using hin1.vregs
        spAligned := hst.spAligned }
      (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
      (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
      (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
    have h4d0 : ((fsp + 0x4d0#64) ↦₆₄ pCap) ∗ memRegion (fsp + 0x4d8#64) 40 ⊢
        memRegion (fsp + 0x4d0#64) 48 := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
        r1b_cell64_cons (a := fsp + 0x4d0#64) pCap (n := 40) (by decide)
    have h188 : ((fsp + 0x188#64) ↦₆₄ spkCap) ⊢ memRegion (fsp + 0x188#64) 8 :=
      pointsTo64_entails_memRegion _ _
    refine MainHops.sepWPp_weaken_pre ?_
      (r1b_after_spk_dealloc himg hh hdrop hbnd hok2 hreg_rd hspk_rd
        (by simp [hsm2, arm64_norm])
        (by simp only [hsm2, arm64_norm]; try exact hx27_1)
        (by simp only [hsm2, arm64_norm]; try exact hx23_1)
        (by simp only [hsm2, arm64_norm]; try exact hx25_1)
        (by simp only [hsm2, arm64_norm]; try exact hx28_1)
        hpanic hrej hk)
    try dsimp only
    rw [hinvCore]
    exact r1b_entails_frame0 (by r1b_ac0) (sepConj_mono h4d0 h188) (by r1b_ac0)

set_option maxHeartbeats 900000 in
private theorem r1b_after_reg_dealloc {S : RunSem} {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets} {σ : RunSlots}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {regCap regPtr : BitVec 64} {regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext)
    (hc : RunCallees img A ext B σ)
    (hdrop : RunDrop.DropSpeOwnedOk img A ext)
    (hbnd : r1b_StackBounds B resStack)
    (he : AtRunEntry S img ext g s0)
    (hok : r1b_OkCtx S img ext g d s0 s 0x0c6c)
    (hreg_rd : cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") = .ok regBs)
    (hx23 : s.readReg64 (.gpr 23#5) = regCap)
    (hx25 : s.readReg64 (.gpr 25#5) = BitVec.ofNat 64 regBs.length)
    (hx26 : s.readReg64 (.gpr 26#5) = d.dirPtr)
    (hx28 : s.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length)
    (hpanic : PanicK g s0 Qp) (hrej : RejectK img ext A g s0 resStack Q Qp)
    (hk : ∀ (sf : State) (r0 r1 r2 r3 : BitVec 8)
        (spkCap spkPtr : BitVec 64) (spkBs spkKey spkSig : List (BitVec 8)) (spkId : BitVec 32),
      r1b_OkCtx S img ext g d s0 sf 0x1260 →
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
      SepWPp (mProg img ext) (s0.readReg64 .lr) sf
        (((fsp + 0x4f0#64) ↦₆₄ (spkPtr + 4#64 + BitVec.ofNat 64 spkKey.length)) ∗
          ((fsp + 0x4f8#64) ↦₆₄ 64#64) ∗
          memRegion (fsp + 0x4d0#64) 32 ∗
          ownedBytes A spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
          ownedBytes A regCap regPtr 4#64 [r0, r1, r2, r3] ∗
          r1b_invCore A img g d s0 ∗ logOff img ∗
          ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
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
          stackAt fsp (resStack - runFrame) ∗ A.pool)
        Q Qp (runOom s0)) :
    let fsp := runFsp s0
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (memRegion (fsp + 0x4d0#64) 48 ∗
        ownedBytes A regCap regPtr (BitVec.ofNat 64 regBs.length) regBs ∗
        r1b_invCore A img g d s0 ∗ logOff img ∗
        ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
        memRegion fsp 0x110 ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
        memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x164#64) 4 ∗
        memRegion (fsp + 0x168#64) 8 ∗ memRegion (fsp + 0x170#64) 8 ∗
        memRegion (fsp + 0x178#64) 8 ∗
        memRegion (fsp + 0x188#64) 8 ∗ ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
        ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
        memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool)
      Q Qp (runOom s0) := by
  intro fsp
  let _ := hx23; let _ := hx25; let _ := hx26; let _ := hx28
  generalize hinvCore : r1b_invCore A img g d s0 = invCore
  have hst := hok.st
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hst.spAligned
  have ⟨hdir32, hpaths⟩ := r1b_init_path_facts he hok.callEq
  have ⟨hspk_ok, hspk_len32⟩ := hpaths "signed-pre-key" (by simp [bundleNames])
  refine r1b_sepWPp_frame0 (by r1b_ac0)
    (r1b_ownedBytes_facts A regCap regPtr (BitVec.ofNat 64 regBs.length) regBs)
    (by r1b_ac0) ?_
  simp only [sepConj_assoc]
  refine r1b_sepWPp_pure_left fun ⟨_, hreg_cap, hreg_len63, _⟩ => ?_
  have hcmn_f : (regCap + 1#64 == 0#64) = false :=
    beq_false_of_ne (r1b_cmn1_false_of_lt63 hreg_cap)
  let _ := hcmn_f
  code_fetches_range CryptoVerification.libsignalSessionCode r1bDecRegSpk img.base
    (Rust.withPanics ext) r1b_run_fnOff (num% (ls_off% "libsignal_cli::run")) 0x0c6c 0x70
  have hpc_in := hst.pc
  dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc_in ⊢
  generalize_entry heq_fnBase :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase
  examples_hide_fetches
  by_cases hlen4 : regBs.length = 4
  · rcases r1b_exists_4bytes hlen4 with ⟨r0, r1, r2, r3, rfl⟩
    rw [show BitVec.ofNat 64 [r0, r1, r2, r3].length = 4#64 from rfl]
    have hx25 : s.readReg64 (.gpr 25#5) = 4#64 := hx25
    let _ := hreg_len63
    have hdir_nat : (BitVec.ofNat 64 d.dir.length).toNat = d.dir.length := by
      simp only [BitVec.toNat_ofNat]; omega
    have h4d0_sp : memRegion (fsp + 0x4d0#64) 48 =
        memRegion (fsp + 0x4d0#64) 24 ∗ memRegion (fsp + 0x4e8#64) 24 :=
      r1b_split_region fsp 0x4d0 24 24
    rw [h4d0_sp]
    simp only [sepConj_assoc]
    refine r1b_call_frame0 <|
      r1b_sepWPp_borrow_core A (cap := regCap) (ptr := regPtr) (len := 4#64)
        (bs := [r0, r1, r2, r3]) fun ⟨_, hreg_le, _, hreg_ne⟩ => ?_
    rw [r1b_pointsToBytes4_eq_u32 regPtr r0 r1 r2 r3]
    have hpc := hpc_in; have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
    apply MainHops.sepWPp_seq_inImage
      (mid := fnBase + bv% ((2 ^ 64 + ls_off% "libsignal_cli::stores::path" -
        ls_off% "libsignal_cli::run") % 2 ^ 64)) hst.inv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state fun sm1 hsm1 hinv1 => ?_
    change SepWPp (mProg img ext) _ _ _ _ _ _
    rw [← r1b_pointsToBytes4_eq_u32 regPtr r0 r1 r2 r3]
    have hrejoin_reg := r1b_ownedBytes_rejoin A regCap regPtr [r0, r1, r2, r3]
      hreg_le hreg_cap hreg_ne
    refine r1b_sepWPp_frame0 (by r1b_ac0) hrejoin_reg (by r1b_ac0) ?_
    refine r1b_call_frame0 <|
      r1b_call_path_ro (ret := fsp + 0x4d0#64) (dirCap := d.dirCap) (dirPtr := d.dirPtr) (dir := d.dir)
        himg hh hbnd hinv1 (r1b_ro_spk himg)
        (by dsimp only [mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm1, arm64_norm])
        (by simp [hsm1, arm64_norm, hst.run])
        (by simpa [hsm1, arm64_norm] using hst.sp)
        (by simpa [hsm1, arm64_norm] using hst.fp)
        (by simpa [calleeSavedVRegs, hsm1, arm64_norm] using hst.vregs)
        hst.spAligned (retOff := 0x0ca0)
        (by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm1, arm64_norm])
        (by simp only [hsm1, arm64_norm]; try exact congrArg (· + 0x4d0#64) hst.sp)
        (by simp only [hsm1, arm64_norm]; try exact hx26)
        (by simp only [hsm1, arm64_norm]; (try rw [hx28]); exact hdir_nat)
        (by have hba := RunSkeleton.base_aligned himg; let _ := hba; simp only [hsm1, arm64_norm, r1b_fnBase_eq heq_fnBase])
        (by simp only [hsm1, arm64_norm]; rfl_kernel)
        hdir32 (by rw [show (utf8 "signed-pre-key").length = 14 by rfl_kernel]; decide)
        (by simpa [hsm1, arm64_norm] using hok.trace) hpanic
        fun sf1 pCap pPtr hin1 hcs1 hfs1 htr1 => ?_
    have hok1 : r1b_OkCtx S img ext g d s0 sf1 0x0ca0 := hok.after_call
      (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
      (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
      (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
      hin1 hcs1 hfs1 htr1
    have hx25_1 : sf1.readReg64 (.gpr 25#5) = (ofLe32 r0 r1 r2 r3).zeroExtend 64 :=
      hcs1.2.2.2.2.2.2.1.trans (by simp [hsm1, arm64_norm])
    have hx26_1 : sf1.readReg64 (.gpr 26#5) = d.dirPtr :=
      hcs1.2.2.2.2.2.2.2.1.trans (by simp only [hsm1, arm64_norm]; try exact hx26)
    have hx28_1 : sf1.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length :=
      hcs1.2.2.2.2.2.2.2.2.2.1.trans (by simp only [hsm1, arm64_norm]; try exact hx28)
    let _ := hx25_1; let _ := hx26_1; let _ := hx28_1
    have hspk_path_nat :
        (BitVec.ofNat 64 (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key").length).toNat =
          (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key").length := by
      simp only [BitVec.toNat_ofNat]; omega
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    have hpc1 := hin1.pc
    dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc1 ⊢
    rw [heq_fnBase] at hpc1
    have hpc := hpc1; have hrun := hin1.run; have hsp : sf1.sp = fsp := hin1.sp
    apply MainHops.sepWPp_seq_inImage
      (mid := fnBase + bv% ((2 ^ 64 + ls_off% "libsignal_cli_io::read_file" -
        ls_off% "libsignal_cli::run") % 2 ^ 64)) hin1.inv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state fun sm2 hsm2 hinv2 => ?_
    change SepWPp (mProg img ext) _ _ _ _ _ _
    have h4e0 :
        ((fsp + 0x4e0#64) ↦₆₄
          BitVec.ofNat 64 (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key").length) ∗
          memRegion (fsp + 0x4e8#64) 24 ⊢ memRegion (fsp + 0x4e0#64) 32 := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
        r1b_cell64_cons (a := fsp + 0x4e0#64)
          (BitVec.ofNat 64 (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key").length)
          (n := 24) (by decide)
    have h4d8 :
        ((fsp + 0x4d8#64) ↦₆₄ pPtr) ∗
          ((fsp + 0x4e0#64) ↦₆₄
            BitVec.ofNat 64 (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key").length) ∗
          memRegion (fsp + 0x4e8#64) 24 ⊢ memRegion (fsp + 0x4d8#64) 40 := by
      refine Entails.trans (sepConj_mono_right h4e0) ?_
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
        r1b_cell64_cons (a := fsp + 0x4d8#64) pPtr (n := 32) (by decide)
    refine r1b_sepWPp_frame0 (by r1b_ac0) h4d8 (by r1b_ac0) ?_
    refine r1b_call_frame0 <|
      r1b_call_readFile hh hc hbnd hinv2
        (by dsimp only [mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm2, arm64_norm])
        (by simp [hsm2, arm64_norm, hin1.run])
        (by simpa [hsm2, arm64_norm] using hin1.sp)
        (by simpa [hsm2, arm64_norm] using hin1.fp)
        (by simpa [calleeSavedVRegs, hsm2, arm64_norm] using hin1.vregs)
        hst.spAligned (retOff := 0x0cb8)
        (by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm2, arm64_norm])
        (pathCap := pCap) (pathPtr := pPtr)
        (path := d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") (ret := fsp + 0x1750#64)
        (by simp [hsm2, arm64_norm])
        (by simpa [hsm2, arm64_norm] using hspk_path_nat)
        (by simp only [hsm2, arm64_norm]; try exact congrArg (· + 0x1750#64) hin1.sp)
        hspk_len32 hspk_ok (by simpa [hsm2, arm64_norm] using hok1.trace) hpanic
        (fun sf2 w1 w2 hin2 hcs2 hout2 => ?_)
        (fun sf2 spkCap spkPtr spkBs hin2 hcs2 hspk_rd_sf hfs2 htr2 => ?_)
    · have hc2 : r1b_ErrCtx img ext g d s0 sf2 0x0cb8 :=
        hok1.after_readErr
          (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
          (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
          (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
          hin2 hcs2 hout2 r1b_none_spk_rd
      have hx27_2 : sf2.readReg64 (.gpr 27#5) = pPtr :=
        hcs2.2.2.2.2.2.2.2.2.1.trans (by simp [hsm2, arm64_norm])
      let _ := hx27_2
      rw [ProofLib.memRegion_four (fsp + 0x164#64)]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      try simp only [BitVec.add_assoc]; try simp only [BitVec.reduceAdd]
      try simp only [sepConj_assoc]
      refine SepWPp.exists_elim fun _v164 => ?_
      have hpc2 := hin2.pc
      dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc2 ⊢
      rw [heq_fnBase] at hpc2
      have hpc := hpc2; have hrun := hin2.run; have hsp : sf2.sp = fsp := hin2.sp
      apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x11b4#64) hin2.inv
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
      refine r1b_bind_state fun sm3 hsm3 hinv3 => ?_
      change SepWPp (mProg img ext) _ _ _ _ _ _
      have hc3 : r1b_ErrCtx img ext g d s0 sm3 0x11b4 := hc2.of_step
        { pc := by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm3, arm64_norm]
          run := by simp [hsm3, arm64_norm, hin2.run]
          sp := by simpa [hsm3, arm64_norm] using hin2.sp
          fp := by simpa [hsm3, arm64_norm] using hin2.fp
          inv := hinv3
          vregs := by simpa [calleeSavedVRegs, hsm3, arm64_norm] using hin2.vregs
          spAligned := hst.spAligned }
        (by simp [hsm3, arm64_norm]) (by simp [hsm3, arm64_norm])
        (by simp [hsm3, arm64_norm]) (by simp [hsm3, arm64_norm])
        (by simp [hsm3, arm64_norm])
      have h1750 :
          ((fsp + 0x1750#64) ↦₆₄ 0xffffffffffffffff#64) ∗
            ((fsp + 0x1758#64) ↦₆₄ w1) ∗ ((fsp + 0x1760#64) ↦₆₄ w2) ⊢
            memRegion (fsp + 0x1750#64) 24 := by
        simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
          r1b_cells3_to_region24 (fsp + 0x1750#64) 0xffffffffffffffff#64 w1 w2
      have hst_err := r1b_stage_to_err A img g d s0 resStack ((sf2.readReg64 (.gpr 25#5)).truncate 32)
      rw [hinvCore] at hst_err
      generalize herrCommon : r1b_errCommon A g d s0 resStack = errCommon at hst_err
      refine r1b_sepWPp_frame0 (by r1b_ac0) h1750 (by r1b_ac0) ?_
      refine MainHops.sepWPp_weaken_pre ?_
        (r1b_err_11b4 (pCap := pCap) (pPtr := pPtr)
          (pBs := d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key")
          (regCap := regCap) (regPtr := regPtr) (regBs := [r0, r1, r2, r3])
          himg hh hdrop hbnd hc3
          (by simp [hsm3, arm64_norm])
          (by simp only [hsm3, arm64_norm]; try exact hx27_2)
          hpanic hrej)
      try dsimp only
      rw [herrCommon]
      exact r1b_entails_frame0 (by r1b_ac0) hst_err (by r1b_ac0)
    · have hok2 : r1b_OkCtx S img ext g d s0 sf2 0x0cb8 := hok1.after_call
        (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
        (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
        (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
        hin2 hcs2 hfs2 htr2
      have hspk_rd : cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") =
          .ok spkBs := by
        rw [← hok1.fs, ← show sm2.fs.files = sf1.fs.files by simp [hsm2, arm64_norm]]
        exact hspk_rd_sf
      have hx25_2 : sf2.readReg64 (.gpr 25#5) = (ofLe32 r0 r1 r2 r3).zeroExtend 64 :=
        hcs2.2.2.2.2.2.2.1.trans (by simp only [hsm2, arm64_norm]; try exact hx25_1)
      have hx26_2 : sf2.readReg64 (.gpr 26#5) = d.dirPtr :=
        hcs2.2.2.2.2.2.2.2.1.trans (by simp only [hsm2, arm64_norm]; try exact hx26_1)
      have hx27_2 : sf2.readReg64 (.gpr 27#5) = pPtr :=
        hcs2.2.2.2.2.2.2.2.2.1.trans (by simp [hsm2, arm64_norm])
      have hx28_2 : sf2.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length :=
        hcs2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [hsm2, arm64_norm]; try exact hx28_1)
      let _ := hx25_2; let _ := hx26_2; let _ := hx27_2; let _ := hx28_2
      refine r1b_sepWPp_frame0 (by r1b_ac0)
        (r1b_ownedBytes_facts A spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs)
        (by r1b_ac0) ?_
      try simp only [BitVec.add_assoc]; try simp only [BitVec.reduceAdd]
      try simp only [sepConj_assoc]
      refine r1b_sepWPp_pure_left fun ⟨_, hspk_cap, _, _⟩ => ?_
      have hcmn_spk : (spkCap + 1#64 == 0#64) = false :=
        beq_false_of_ne (r1b_cmn1_false_of_lt63 hspk_cap)
      let _ := hcmn_spk
      rw [ProofLib.memRegion_four (fsp + 0x164#64), ProofLib.memRegion_eight (fsp + 0x170#64)]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      try simp only [sepConj_assoc]
      refine SepWPp.exists_elim fun _v164 => SepWPp.exists_elim fun _v170 => ?_
      have hpc2 := hin2.pc
      dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc2 ⊢
      rw [heq_fnBase] at hpc2
      have hpc := hpc2; have hrun := hin2.run; have hsp : sf2.sp = fsp := hin2.sp
      apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x11f4#64) hin2.inv
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
      refine r1b_bind_state fun sm3 hsm3 hinv3 => ?_
      change SepWPp (mProg img ext) _ _ _ _ _ _
      have hok3 : r1b_OkCtx S img ext g d s0 sm3 0x11f4 := hok2.of_step
        { pc := by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm3, arm64_norm]
          run := by simp [hsm3, arm64_norm, hin2.run]
          sp := by simpa [hsm3, arm64_norm] using hin2.sp
          fp := by simpa [hsm3, arm64_norm] using hin2.fp
          inv := hinv3
          vregs := by simpa [calleeSavedVRegs, hsm3, arm64_norm] using hin2.vregs
          spAligned := hst.spAligned }
        (by simp [hsm3, arm64_norm]) (by simp [hsm3, arm64_norm])
        (by simp [hsm3, arm64_norm]) (by simp [hsm3, arm64_norm])
        (by simp [hsm3, arm64_norm]) (by simp [hsm3, arm64_norm])
      have hv164 : ((sf2.readReg64 (.gpr 25#5)).truncate 32) = ofLe32 r0 r1 r2 r3 := by
        rw [hx25_2]; bv_bits
      have hv164' : (((ofLe32 r0 r1 r2 r3).zeroExtend 64).truncate 32) = ofLe32 r0 r1 r2 r3 := by
        bv_bits
      try rw [hv164]
      try rw [hv164']
      have h1750 :
          ((fsp + 0x1750#64) ↦₆₄ spkCap) ∗
            ((fsp + 0x1758#64) ↦₆₄ spkPtr) ∗
            ((fsp + 0x1760#64) ↦₆₄ BitVec.ofNat 64 spkBs.length) ⊢
            memRegion (fsp + 0x1750#64) 24 := by
        simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
          r1b_cells3_to_region24 (fsp + 0x1750#64) spkCap spkPtr (BitVec.ofNat 64 spkBs.length)
      refine MainHops.sepWPp_weaken_pre ?_
        (r1b_spk_dealloc_11f4 (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3)
          (pCap := pCap) (pPtr := pPtr) (pBs := d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key")
          (regCap := regCap) (regPtr := regPtr) (spkCap := spkCap) (spkPtr := spkPtr)
          (spkBs := spkBs) himg hh hdrop hbnd hok3 hreg_rd hspk_rd
          (by simp only [hsm3, arm64_norm]; try exact hx27_2)
          (by simp [hsm3, arm64_norm])
          (by simp [hsm3, arm64_norm])
          (by simp [hsm3, arm64_norm])
          (by simp [hsm3, arm64_norm])
          (by simp only [hsm3, arm64_norm]; try exact hx26_2)
          (by simp only [hsm3, arm64_norm]; try exact hx28_2)
          hpanic hrej fun sf4 spkId spkKey spkSig hok4 hsp_s hx10_4 hx27_4 hx2_4 hx26_4 hx28_4 =>
            hk sf4 r0 r1 r2 r3 spkCap spkPtr spkBs spkKey spkSig spkId
              hok4 hreg_rd hspk_rd hsp_s hx10_4 hx27_4 hx2_4 hx26_4 hx28_4)
      try dsimp only
      rw [hinvCore]
      exact r1b_entails_frame0 (by r1b_ac0) h1750 (by r1b_ac0)
  · have hcmp4 : (BitVec.ofNat 64 regBs.length == 4#64) = false :=
      r1b_ofNat64_ne4 hreg_len63 hlen4
    let _ := hcmp4
    have hpc := hpc_in; have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
    apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x0df0#64) hst.inv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state fun sm1 hsm1 hinv1 => ?_
    change SepWPp (mProg img ext) _ _ _ _ _ _
    have hc1 : r1b_ErrCtx img ext g d s0 sm1 0x0df0 :=
      (hok.of_step
        { pc := by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm1, arm64_norm]
          run := by simp [hsm1, arm64_norm, hst.run]
          sp := by simpa [hsm1, arm64_norm] using hst.sp
          fp := by simpa [hsm1, arm64_norm] using hst.fp
          inv := hinv1
          vregs := by simpa [calleeSavedVRegs, hsm1, arm64_norm] using hst.vregs
          spAligned := hst.spAligned }
        (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
        (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
        (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])).to_err
      (r1b_none_reg_len hreg_rd hlen4)
    have hcore := r1b_invCore_to_errCommon A img g d s0 resStack
    rw [hinvCore] at hcore
    generalize herrCommon : r1b_errCommon A g d s0 resStack = errCommon at hcore
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
    refine MainHops.sepWPp_weaken_pre ?_
      (r1b_err_0df0 (regCap := regCap) (regPtr := regPtr) (regBs := regBs)
        himg hh hdrop hbnd hc1 hpanic hrej)
    try dsimp only
    rw [herrCommon]
    exact r1b_entails_frame0 (by r1b_ac0)
      (sepConj_mono hcore (sepConj_mono h168 (sepConj_mono h188 h1a8))) (by r1b_ac0)

set_option maxHeartbeats 900000 in
private theorem r1b_reg_dealloc_0784 {S : RunSem} {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets} {σ : RunSlots}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {pCap pPtr regCap regPtr : BitVec 64}
    {pBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext)
    (hc : RunCallees img A ext B σ)
    (hdrop : RunDrop.DropSpeOwnedOk img A ext)
    (hbnd : r1b_StackBounds B resStack)
    (he : AtRunEntry S img ext g s0)
    (hok : r1b_OkCtx S img ext g d s0 s 0x0784)
    (hreg_rd : cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") = .ok regBs)
    (hx26 : s.readReg64 (.gpr 26#5) = d.dirPtr)
    (hx27 : s.readReg64 (.gpr 27#5) = pPtr)
    (hx28 : s.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length)
    (hpanic : PanicK g s0 Qp) (hrej : RejectK img ext A g s0 resStack Q Qp)
    (hk : ∀ (sf : State) (r0 r1 r2 r3 : BitVec 8)
        (spkCap spkPtr : BitVec 64) (spkBs spkKey spkSig : List (BitVec 8)) (spkId : BitVec 32),
      r1b_OkCtx S img ext g d s0 sf 0x1260 →
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
      SepWPp (mProg img ext) (s0.readReg64 .lr) sf
        (((fsp + 0x4f0#64) ↦₆₄ (spkPtr + 4#64 + BitVec.ofNat 64 spkKey.length)) ∗
          ((fsp + 0x4f8#64) ↦₆₄ 64#64) ∗
          memRegion (fsp + 0x4d0#64) 32 ∗
          ownedBytes A spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
          ownedBytes A regCap regPtr 4#64 [r0, r1, r2, r3] ∗
          r1b_invCore A img g d s0 ∗ logOff img ∗
          ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
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
          stackAt fsp (resStack - runFrame) ∗ A.pool)
        Q Qp (runOom s0)) :
    let fsp := runFsp s0
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (((fsp + 0x4d0#64) ↦₆₄ pCap) ∗ memRegion (fsp + 0x4d8#64) 40 ∗
        ownedBytes A pCap pPtr (BitVec.ofNat 64 pBs.length) pBs ∗
        ((fsp + 0x1750#64) ↦₆₄ regCap) ∗ ((fsp + 0x1758#64) ↦₆₄ regPtr) ∗
        ((fsp + 0x1760#64) ↦₆₄ BitVec.ofNat 64 regBs.length) ∗
        ownedBytes A regCap regPtr (BitVec.ofNat 64 regBs.length) regBs ∗
        r1b_invCore A img g d s0 ∗ logOff img ∗
        ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
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
        stackAt fsp (resStack - runFrame) ∗ A.pool)
      Q Qp (runOom s0) := by
  intro fsp
  let _ := hx26; let _ := hx27; let _ := hx28
  generalize hinvCore : r1b_invCore A img g d s0 = invCore
  have hst := hok.st
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hst.spAligned
  code_fetches_range CryptoVerification.libsignalSessionCode r1bDecRegSpk img.base
    (Rust.withPanics ext) r1b_run_fnOff (num% (ls_off% "libsignal_cli::run")) 0x0784 0x20
  code_fetches_range CryptoVerification.libsignalSessionCode r1bDecRegSpk img.base
    (Rust.withPanics ext) r1b_run_fnOff (num% (ls_off% "libsignal_cli::run")) 0x0c50 0x1c
  have hpc_in := hst.pc
  dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc_in ⊢
  generalize_entry heq_fnBase :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase
  examples_hide_fetches
  refine r1b_sepWPp_frame0 (by r1b_ac0)
    (r1b_ownedBytes_facts A regCap regPtr (BitVec.ofNat 64 regBs.length) regBs)
    (by r1b_ac0) ?_
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
    have hpc := hpc_in; have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
    apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x0c6c#64) hst.inv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state fun sm3 hsm3 hinv3 => ?_
    change SepWPp (mProg img ext) _ _ _ _ _ _
    have hok3 : r1b_OkCtx S img ext g d s0 sm3 0x0c6c := hok.of_step
      { pc := by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm3, arm64_norm]
        run := by simp [hsm3, arm64_norm, hst.run]
        sp := by simpa [hsm3, arm64_norm] using hst.sp
        fp := by simpa [hsm3, arm64_norm] using hst.fp
        inv := hinv3
        vregs := by simpa [calleeSavedVRegs, hsm3, arm64_norm] using hst.vregs
        spAligned := hst.spAligned }
      (by simp [hsm3, arm64_norm]) (by simp [hsm3, arm64_norm])
      (by simp [hsm3, arm64_norm]) (by simp [hsm3, arm64_norm])
      (by simp [hsm3, arm64_norm]) (by simp [hsm3, arm64_norm])
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
    refine r1b_sepWPp_frame0 (by r1b_ac0)
      (r1b_ownedBytes_zero A pPtr (BitVec.ofNat 64 pBs.length) pBs)
      (by simp only [emp_sepConj]) ?_
    refine MainHops.sepWPp_weaken_pre ?_
      (r1b_after_reg_dealloc (regCap := regCap) (regPtr := regPtr) (regBs := regBs)
        himg hh hc hdrop hbnd he hok3 hreg_rd
        (by simp [hsm3, arm64_norm])
        (by simp [hsm3, arm64_norm])
        (by simp only [hsm3, arm64_norm]; try exact hx26)
        (by simp only [hsm3, arm64_norm]; try exact hx28)
        hpanic hrej hk)
    try dsimp only
    rw [hinvCore]
    exact r1b_entails_frame0 (by r1b_ac0) (sepConj_mono h4d0 h1750) (by r1b_ac0)
  · have hpCap_f : (pCap == 0#64) = false := beq_false_of_ne hpCap
    let _ := hpCap_f
    have hpc := hpc_in; have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
    apply MainHops.sepWPp_seq_inImage
      (mid := fnBase + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_cli::run"))
      hst.inv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state fun sm3 hsm3 hinv3 => ?_
    change SepWPp (mProg img ext) _ _ _ _ _ _
    refine r1b_call_frame0 <|
      r1b_call_dealloc_ownedBytes (ptr := pPtr) (cap := pCap) (bs := pBs) hh hbnd hinv3
        (by dsimp only [mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm3, arm64_norm])
        (by simp [hsm3, arm64_norm, hst.run])
        (by simpa [hsm3, arm64_norm] using hst.sp)
        (by simpa [hsm3, arm64_norm] using hst.fp)
        (by simpa [calleeSavedVRegs, hsm3, arm64_norm] using hst.vregs)
        hst.spAligned (retOff := 0x0c68)
        (by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm3, arm64_norm])
        (by simp only [hsm3, arm64_norm]; try exact hx27)
        (by simp [hsm3, arm64_norm]) (by simp [hsm3, arm64_norm]) hpCap hpanic
        fun sf3 hin3 hcs3 hfs3 htr3 => ?_
    have hok3 : r1b_OkCtx S img ext g d s0 sf3 0x0c68 := hok.after_call
      (by simp [hsm3, arm64_norm]) (by simp [hsm3, arm64_norm])
      (by simp [hsm3, arm64_norm]) (by simp [hsm3, arm64_norm])
      (by simp [hsm3, arm64_norm]) (by simp [hsm3, arm64_norm])
      hin3 hcs3 (congrArg FsState.files hfs3) htr3
    have hx23_3 : sf3.readReg64 (.gpr 23#5) = regCap :=
      hcs3.2.2.2.2.1.trans (by simp [hsm3, arm64_norm])
    have hx25_3 : sf3.readReg64 (.gpr 25#5) = BitVec.ofNat 64 regBs.length :=
      hcs3.2.2.2.2.2.2.1.trans (by simp [hsm3, arm64_norm])
    have hx26_3 : sf3.readReg64 (.gpr 26#5) = d.dirPtr :=
      hcs3.2.2.2.2.2.2.2.1.trans (by simp only [hsm3, arm64_norm]; try exact hx26)
    have hx28_3 : sf3.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length :=
      hcs3.2.2.2.2.2.2.2.2.2.1.trans (by simp only [hsm3, arm64_norm]; try exact hx28)
    let _ := hx23_3; let _ := hx25_3; let _ := hx26_3; let _ := hx28_3
    have hpc3 := hin3.pc
    dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc3 ⊢
    rw [heq_fnBase] at hpc3
    have hpc := hpc3; have hrun := hin3.run; have hsp : sf3.sp = fsp := hin3.sp
    apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x0c6c#64) hin3.inv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state fun sm4 hsm4 hinv4 => ?_
    change SepWPp (mProg img ext) _ _ _ _ _ _
    have hok4 : r1b_OkCtx S img ext g d s0 sm4 0x0c6c := hok3.of_step
      { pc := by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm4, arm64_norm]
        run := by simp [hsm4, arm64_norm, hin3.run]
        sp := by simpa [hsm4, arm64_norm] using hin3.sp
        fp := by simpa [hsm4, arm64_norm] using hin3.fp
        inv := hinv4
        vregs := by simpa [calleeSavedVRegs, hsm4, arm64_norm] using hin3.vregs
        spAligned := hst.spAligned }
      (by simp [hsm4, arm64_norm]) (by simp [hsm4, arm64_norm])
      (by simp [hsm4, arm64_norm]) (by simp [hsm4, arm64_norm])
      (by simp [hsm4, arm64_norm]) (by simp [hsm4, arm64_norm])
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
    refine MainHops.sepWPp_weaken_pre ?_
      (r1b_after_reg_dealloc (regCap := regCap) (regPtr := regPtr) (regBs := regBs)
        himg hh hc hdrop hbnd he hok4 hreg_rd
        (by simp only [hsm4, arm64_norm]; try exact hx23_3)
        (by simp only [hsm4, arm64_norm]; try exact hx25_3)
        (by simp only [hsm4, arm64_norm]; try exact hx26_3)
        (by simp only [hsm4, arm64_norm]; try exact hx28_3)
        hpanic hrej hk)
    try dsimp only
    rw [hinvCore]
    exact r1b_entails_frame0 (by r1b_ac0) (sepConj_mono h4d0 h1750) (by r1b_ac0)

set_option maxHeartbeats 900000 in
theorem r1b_step_reg_spk {S : RunSem} {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets} {σ : RunSlots}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext)
    (hc : RunCallees img A ext B σ)
    (hdrop : RunDrop.DropSpeOwnedOk img A ext)
    (hbnd : r1b_StackBounds B resStack)
    (he : AtRunEntry S img ext g s0)
    (hok : r1b_OkCtx S img ext g d s0 s 0x074c)
    (hx28 : s.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length)
    (hpanic : PanicK g s0 Qp) (hrej : RejectK img ext A g s0 resStack Q Qp)
    (hk : ∀ (sf : State) (r0 r1 r2 r3 : BitVec 8)
        (regCap regPtr spkCap spkPtr : BitVec 64)
        (spkBs spkKey spkSig : List (BitVec 8)) (spkId : BitVec 32),
      r1b_OkCtx S img ext g d s0 sf 0x1260 →
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
      SepWPp (mProg img ext) (s0.readReg64 .lr) sf
        (((fsp + 0x4f0#64) ↦₆₄ (spkPtr + 4#64 + BitVec.ofNat 64 spkKey.length)) ∗
          ((fsp + 0x4f8#64) ↦₆₄ 64#64) ∗
          memRegion (fsp + 0x4d0#64) 32 ∗
          ownedBytes A spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
          ownedBytes A regCap regPtr 4#64 [r0, r1, r2, r3] ∗
          r1b_invCore A img g d s0 ∗ logOff img ∗
          ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
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
          stackAt fsp (resStack - runFrame) ∗ A.pool)
        Q Qp (runOom s0)) :
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (init1Mem A img g d s0 resStack) Q Qp (runOom s0) := by
  let _ := hx28
  refine MainHops.sepWPp_weaken_pre (r1b_init1Mem_unpack A img g d s0 resStack) ?_
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
  refine r1b_sepWPp_frame0 (by r1b_ac0) hnorm_in (by r1b_ac0) ?_
  have hst := hok.st
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hst.spAligned
  have ⟨hdir32, hpaths⟩ := r1b_init_path_facts he hok.callEq
  have ⟨hreg_ok, hreg_len32⟩ := hpaths "registration-id" (by simp [bundleNames])
  have hdir_nat : (BitVec.ofNat 64 d.dir.length).toNat = d.dir.length := by
    simp only [BitVec.toNat_ofNat]; omega
  generalize hinvRest :
    (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
      storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      coinsInstalled img g.coins (MainHops.coinsOf g.i) ∗
      CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
      addrNameHeap A d.meG ∗ runSaved s0 ∗
      memRegion (fsp + 0x118#64) 4 ∗ memRegion (fsp + 0x160#64) 4 ∗
      ((fsp + 0x180#64) ↦₆₄ d.ikW0) ∗
      ((fsp + 0x1b8#64) ↦₆₄ d.meG.name.ptr) ∗
      ((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗
      memRegion (fsp + 0x1d0#64) 0x90 ∗
      addrUpperAt (fsp + 0x260#64) d.meG ∗
      memRegion (fsp + 0x270#64) 0x30 ∗
      protocolAddressAt A d.peerG (fsp + 0x2a0#64) ∗
      memRegion (fsp + 0x2c0#64) 0x210 ∗
      memRegion (fsp + 0x500#64) 0x1250 ∗
      memRegion (fsp + 0x1768#64) 0x1288) = invRest
  have hinv_open : r1b_invCore A img g d s0 = ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr) ∗ invRest := by
    rw [← hinvRest]; dsimp only [r1b_invCore, fsp]; with_reducible ac_rfl
  have h4d0_sp : memRegion (fsp + 0x4d0#64) 48 =
      memRegion (fsp + 0x4d0#64) 24 ∗ memRegion (fsp + 0x4e8#64) 24 :=
    r1b_split_region fsp 0x4d0 24 24
  rw [hinv_open, h4d0_sp]
  simp only [sepConj_assoc]
  code_fetches_range CryptoVerification.libsignalSessionCode r1bDecRegSpk img.base
    (Rust.withPanics ext) r1b_run_fnOff (num% (ls_off% "libsignal_cli::run")) 0x074c 0x44
  have hpc_in := hst.pc
  dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc_in ⊢
  generalize_entry heq_fnBase :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase
  examples_hide_fetches
  have hpc := hpc_in; have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
  apply MainHops.sepWPp_seq_inImage
    (mid := fnBase + bv% ((2 ^ 64 + ls_off% "libsignal_cli::stores::path" -
      ls_off% "libsignal_cli::run") % 2 ^ 64)) hst.inv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state fun sm1 hsm1 hinv1 => ?_
  change SepWPp (mProg img ext) _ _ _ _ _ _
  generalize hinvCore : r1b_invCore A img g d s0 = invCore
  have hinv_close : ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr) ∗ invRest ⊢ invCore := by
    rw [← hinv_open, hinvCore]; exact Entails.refl _
  refine r1b_sepWPp_frame0 (by r1b_ac0) hinv_close (by r1b_ac0) ?_
  refine r1b_call_frame0 <|
    r1b_call_path_ro himg hh hbnd hinv1 (r1b_ro_reg_id himg)
      (by dsimp only [mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm1, arm64_norm])
      (by simp [hsm1, arm64_norm, hst.run])
      (by simpa [hsm1, arm64_norm] using hst.sp)
      (by simpa [hsm1, arm64_norm] using hst.fp)
      (by simpa [calleeSavedVRegs, hsm1, arm64_norm] using hst.vregs)
      hst.spAligned (retOff := 0x076c)
      (by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm1, arm64_norm])
      (ret := fsp + 0x4d0#64) (dirCap := d.dirCap) (dirPtr := d.dirPtr) (dir := d.dir)
      (by simp only [hsm1, arm64_norm]; try exact congrArg (· + 0x4d0#64) hst.sp)
      (by simp [hsm1, arm64_norm])
      (by simp only [hsm1, arm64_norm]; (try rw [hx28]); exact hdir_nat)
      (by have hba := RunSkeleton.base_aligned himg; let _ := hba; simp only [hsm1, arm64_norm, r1b_fnBase_eq heq_fnBase])
      (by simp only [hsm1, arm64_norm]; rfl_kernel)
      hdir32 (by rw [show (utf8 "registration-id").length = 15 by rfl_kernel]; decide)
      (by simpa [hsm1, arm64_norm] using hok.trace) hpanic
      fun sf1 pCap pPtr hin1 hcs1 hfs1 htr1 => ?_
  have hok1 : r1b_OkCtx S img ext g d s0 sf1 0x076c := hok.after_call
    (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
    (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
    (by simp [hsm1, arm64_norm]) (by simp [hsm1, arm64_norm])
    hin1 hcs1 hfs1 htr1
  have hx26_1 : sf1.readReg64 (.gpr 26#5) = d.dirPtr :=
    hcs1.2.2.2.2.2.2.2.1.trans (by simp [hsm1, arm64_norm])
  have hx28_1 : sf1.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length :=
    hcs1.2.2.2.2.2.2.2.2.2.1.trans (by simp only [hsm1, arm64_norm]; try exact hx28)
  let _ := hx26_1; let _ := hx28_1
  have hreg_path_nat :
      (BitVec.ofNat 64 (d.dir ++ [0x2f#8] ++ utf8 "registration-id").length).toNat =
        (d.dir ++ [0x2f#8] ++ utf8 "registration-id").length := by
    simp only [BitVec.toNat_ofNat]; omega
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  try simp only [sepConj_assoc]
  have hpc1 := hin1.pc
  dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc1 ⊢
  rw [heq_fnBase] at hpc1
  have hpc := hpc1; have hrun := hin1.run; have hsp : sf1.sp = fsp := hin1.sp
  apply MainHops.sepWPp_seq_inImage
    (mid := fnBase + bv% ((2 ^ 64 + ls_off% "libsignal_cli_io::read_file" -
      ls_off% "libsignal_cli::run") % 2 ^ 64)) hin1.inv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state fun sm2 hsm2 hinv2 => ?_
  change SepWPp (mProg img ext) _ _ _ _ _ _
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
  refine r1b_sepWPp_frame0 (by r1b_ac0) h4d8 (by r1b_ac0) ?_
  refine r1b_call_frame0 <|
    r1b_call_readFile hh hc hbnd hinv2
      (by dsimp only [mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm2, arm64_norm])
      (by simp [hsm2, arm64_norm, hin1.run])
      (by simpa [hsm2, arm64_norm] using hin1.sp)
      (by simpa [hsm2, arm64_norm] using hin1.fp)
      (by simpa [calleeSavedVRegs, hsm2, arm64_norm] using hin1.vregs)
      hst.spAligned (retOff := 0x0784)
      (by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm2, arm64_norm])
      (pathCap := pCap) (pathPtr := pPtr)
      (path := d.dir ++ [0x2f#8] ++ utf8 "registration-id") (ret := fsp + 0x1750#64)
      (by simp [hsm2, arm64_norm])
      (by simpa [hsm2, arm64_norm] using hreg_path_nat)
      (by simp only [hsm2, arm64_norm]; try exact congrArg (· + 0x1750#64) hin1.sp)
      hreg_len32 hreg_ok (by simpa [hsm2, arm64_norm] using hok1.trace) hpanic
      (fun sf2 w1 w2 hin2 hcs2 hout2 => ?_)
      (fun sf2 regCap regPtr regBs hin2 hcs2 hreg_rd_sf hfs2 htr2 => ?_)
  · have hc2 : r1b_ErrCtx img ext g d s0 sf2 0x0784 :=
      hok1.after_readErr
        (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
        (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
        (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
        hin2 hcs2 hout2 r1b_none_reg_rd
    have hx27_2 : sf2.readReg64 (.gpr 27#5) = pPtr :=
      hcs2.2.2.2.2.2.2.2.2.1.trans (by simp [hsm2, arm64_norm])
    let _ := hx27_2
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    try simp only [sepConj_assoc]
    have hpc2 := hin2.pc
    dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc2 ⊢
    rw [heq_fnBase] at hpc2
    have hpc := hpc2; have hrun := hin2.run; have hsp : sf2.sp = fsp := hin2.sp
    apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x0c14#64) hin2.inv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state fun sm3 hsm3 hinv3 => ?_
    change SepWPp (mProg img ext) _ _ _ _ _ _
    have hc3 : r1b_ErrCtx img ext g d s0 sm3 0x0c14 := hc2.of_step
      { pc := by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm3, arm64_norm]
        run := by simp [hsm3, arm64_norm, hin2.run]
        sp := by simpa [hsm3, arm64_norm] using hin2.sp
        fp := by simpa [hsm3, arm64_norm] using hin2.fp
        inv := hinv3
        vregs := by simpa [calleeSavedVRegs, hsm3, arm64_norm] using hin2.vregs
        spAligned := hst.spAligned }
      (by simp [hsm3, arm64_norm]) (by simp [hsm3, arm64_norm])
      (by simp [hsm3, arm64_norm]) (by simp [hsm3, arm64_norm])
      (by simp [hsm3, arm64_norm])
    have h1750 :
        ((fsp + 0x1750#64) ↦₆₄ 0xffffffffffffffff#64) ∗
          ((fsp + 0x1758#64) ↦₆₄ w1) ∗ ((fsp + 0x1760#64) ↦₆₄ w2) ⊢
          memRegion (fsp + 0x1750#64) 24 := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
        r1b_cells3_to_region24 (fsp + 0x1750#64) 0xffffffffffffffff#64 w1 w2
    refine r1b_sepWPp_frame0 (by r1b_ac0) h1750 (by r1b_ac0) ?_
    have hcore := r1b_invCore_to_errCommon A img g d s0 resStack
    rw [hinvCore] at hcore
    generalize herrCommon : r1b_errCommon A g d s0 resStack = errCommon at hcore
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
    refine MainHops.sepWPp_weaken_pre ?_
      (r1b_err_0c14 (pCap := pCap) (pPtr := pPtr)
        (pBs := d.dir ++ [0x2f#8] ++ utf8 "registration-id")
        himg hh hdrop hbnd hc3
        (by simp [hsm3, arm64_norm])
        (by simp only [hsm3, arm64_norm]; try exact hx27_2)
        hpanic hrej)
    try dsimp only
    rw [herrCommon]
    exact r1b_entails_frame0 (by r1b_ac0)
      (sepConj_mono hcore (sepConj_mono h168 (sepConj_mono h188 h1a8)))
      (by r1b_ac0)
  · have hok2 : r1b_OkCtx S img ext g d s0 sf2 0x0784 := hok1.after_call
      (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
      (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
      (by simp [hsm2, arm64_norm]) (by simp [hsm2, arm64_norm])
      hin2 hcs2 hfs2 htr2
    have hreg_rd : cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") =
        .ok regBs := by
      rw [← hok1.fs, ← show sm2.fs.files = sf1.fs.files by simp [hsm2, arm64_norm]]
      exact hreg_rd_sf
    refine MainHops.sepWPp_weaken_pre ?_
      (r1b_reg_dealloc_0784
        (pCap := pCap) (pPtr := pPtr) (pBs := d.dir ++ [0x2f#8] ++ utf8 "registration-id")
        (regCap := regCap) (regPtr := regPtr) (regBs := regBs)
        himg hh hc hdrop hbnd he hok2 hreg_rd
        (hcs2.2.2.2.2.2.2.2.1.trans (by simp only [hsm2, arm64_norm]; try exact hx26_1))
        (hcs2.2.2.2.2.2.2.2.2.1.trans (by simp [hsm2, arm64_norm]))
        (hcs2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [hsm2, arm64_norm]; try exact hx28_1))
        hpanic hrej fun sf4 r0 r1 r2 r3 spkCap spkPtr spkBs spkKey spkSig spkId
          hok4 hr hs hsp_s hx10_4 hx27_4 hx2_4 hx26_4 hx28_4 =>
            hk sf4 r0 r1 r2 r3 regCap regPtr spkCap spkPtr spkBs spkKey spkSig spkId
              hok4 hr hs hsp_s hx10_4 hx27_4 hx2_4 hx26_4 hx28_4)
    try dsimp only
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rw [hinvCore]
    exact Entails.of_eq (by r1b_ac0)


end CryptoVerification.SignalSession.Cli.RunCompose
