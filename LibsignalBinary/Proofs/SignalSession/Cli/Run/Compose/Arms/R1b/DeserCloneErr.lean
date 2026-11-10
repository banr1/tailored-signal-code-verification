/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadOpk
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Loop
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSites
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupUpper
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadKpk
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpk -- shake: keep

/-!
# Stage 4a Deserialization Error Cleanup for Arm `R1b` (`0x24fc → 0x2adc`, `0x2654 → 0x2adc`)

Defines the intermediate `opk`/`spk` scratch layout `r1b_opkStage1SpkAt` and proves error cleanup
for `<PublicKey>::deserialize` (`r1b_spk_err_24fc`, `0x24fc → 0x2adc`) and
`kem::Key::deserialize` (`r1b_kem_err_2654`, `0x2654 → 0x2adc`, freeing `spkSigPtr`).
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
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton

macro (priority := 2000) "r1b_ac" : tactic =>
  `(tactic| ((try dsimp +zetaDelta only) <;> first | rfl | simp only [emp_sepConj] | with_reducible ac_rfl | ac_rfl))

private meta def r1bStripLetsT : Nat → Lean.Expr → Lean.Expr
  | 0, e => e
  | n + 1, .letE _ _ v b _ => r1bStripLetsT n (b.instantiate1 v)
  | n + 1, .mdata _ e => r1bStripLetsT n e
  | _, e => e

private meta def r1bSplitSepT : Nat → Lean.Expr → Lean.Expr → Array Lean.Expr
  | 0, _, e => #[e]
  | fuel + 1, sepSample, e =>
    let e := r1bStripLetsT 64 e
    let fn := sepSample.getAppFn.constName!
    let ar := sepSample.getAppNumArgs
    if e.isAppOfArity fn ar then
      r1bSplitSepT fuel sepSample (e.getArg! (ar - 2)) ++
        r1bSplitSepT fuel sepSample (e.getArg! (ar - 1))
    else #[e]

private meta def r1bIsDefEqPureT (x a : Lean.Expr) : Lean.Elab.TermElabM Bool := do
  let x := r1bStripLetsT 64 x; let a := r1bStripLetsT 64 a
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

private meta def r1bComputeRestT (ctxName : String) (p a1 : Lean.Expr) : Lean.Elab.TermElabM Lean.Expr := do
  let sepTy := Lean.mkConst ``SepProp []
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let ps := (r1bSplitSepT 64 sepSample (← Lean.instantiateMVars p)).toList
  let a1s := (r1bSplitSepT 64 sepSample (← Lean.instantiateMVars a1)).toList
  let mut rem := ps
  for a in a1s do
    let mut removed := false
    let mut next : List Lean.Expr := []
    for x in rem do
      if !removed && (← r1bIsDefEqPureT x a) then removed := true
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

elab (priority := 2000) "r1b_entails_frame " t1:term:arg h:term:arg t2:term:arg : term <= expectedType => do
  let exp ← Lean.instantiateMVars expectedType
  if exp.isMVar then Lean.Elab.Term.tryPostpone
  let entSample ← Lean.Elab.Term.elabTerm (← `(emp ⊢ emp)) none
  let ear := entSample.getAppNumArgs
  let expS := r1bStripLetsT 64 exp
  let p := expS.getArg! (ear - 2)
  let q := expS.getArg! (ear - 1)
  if (← Lean.instantiateMVars p).isMVar then Lean.Elab.Term.tryPostpone
  if (← Lean.instantiateMVars q).isMVar then Lean.Elab.Term.tryPostpone
  let hExpr ← Lean.Elab.Term.elabTerm h none
  let hTy := r1bStripLetsT 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
  let a1 := hTy.getArg! (ear - 2)
  let a2 := hTy.getArg! (ear - 1)
  let r ← r1bComputeRestT "r1b_entails_frame" p a1
  let sepTy := Lean.mkConst ``SepProp []
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let sar := sepSample.getAppNumArgs
  let mkSep (x y : Lean.Expr) : Lean.Expr :=
    sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
  let rIsEmp ← r1bIsDefEqPureT r empExpr
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

elab (priority := 2000) "r1b_sepWPp_frame " t1:term:arg h:term:arg t2:term:arg hk:term:arg : term <= expectedType => do
  let exp ← Lean.instantiateMVars expectedType
  if exp.isMVar then Lean.Elab.Term.tryPostpone
  let expS := r1bStripLetsT 64 exp
  let args := expS.getAppArgs
  let prog := args[0]!; let ret := args[1]!; let st := args[2]!; let p := args[3]!
  let q := args[4]!; let qp := args[5]!; let oom := args[6]!
  let entSample ← Lean.Elab.Term.elabTerm (← `(emp ⊢ emp)) none
  let ear := entSample.getAppNumArgs
  let hExpr ← Lean.Elab.Term.elabTerm h none
  let hTy := r1bStripLetsT 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
  let a1 := hTy.getArg! (ear - 2)
  let a2 := hTy.getArg! (ear - 1)
  let r ← r1bComputeRestT "r1b_sepWPp_frame" p a1
  let sepTy := Lean.mkConst ``SepProp []
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let sar := sepSample.getAppNumArgs
  let mkSep (x y : Lean.Expr) : Lean.Expr :=
    sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
  let rIsEmp ← r1bIsDefEqPureT r empExpr
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
    let a2IsEmp ← r1bIsDefEqPureT a2 empExpr
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

elab:10 (priority := 2000) "r1b_call_frame" "<|" h:term:10 : term <= expectedType => do
    let exp ← Lean.instantiateMVars expectedType
    if exp.isMVar then Lean.Elab.Term.tryPostpone
    let expS := r1bStripLetsT 64 exp
    let hExpr ← Lean.Elab.Term.elabTerm h none
    let hTy0 := r1bStripLetsT 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
    for idx in [0, 1, 2, 4, 5, 6] do
      if !(← Lean.Meta.withReducibleAndInstances <| Lean.Meta.isDefEq (hTy0.getArg! idx) (expS.getArg! idx)) then
        discard <| Lean.Meta.isDefEq (hTy0.getArg! idx) (expS.getArg! idx)
    let p ← Lean.instantiateMVars (expS.getArg! 3)
    let p' ← Lean.instantiateMVars ((r1bStripLetsT 64 (← Lean.instantiateMVars hTy0)).getArg! 3)
    let sepTy := Lean.mkConst ``SepProp []
    let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
    let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
    let sar := sepSample.getAppNumArgs
    let mkSep (x y : Lean.Expr) : Lean.Expr :=
      sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
    let ps := (r1bSplitSepT 64 sepSample p).toList
    let p's := (r1bSplitSepT 64 sepSample p').toList
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
        if !removed && (← r1bIsDefEqPureT x a) then removed := true
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
    Lean.Meta.mkAppM ``MainHops.sepWPp_weaken_pre #[ent, hExpr]

gen_decodes CryptoVerification.libsignalSessionCode_tree r1bDecDeserCloneErr
  [(ls_off% "libsignal_cli::run" + 0x24ec) → (ls_off% "libsignal_cli::run" + 0x25f4),
   (ls_off% "libsignal_cli::run" + 0x2634) → (ls_off% "libsignal_cli::run" + 0x26a8),
   (ls_off% "libsignal_cli::run" + 0x26cc) → (ls_off% "libsignal_cli::run" + 0x2740)]

/-- Stage-1 `opk` and spilled `spk` scratch layout across `0x2550 .. 0x25f4` (`[0x0f0..0x110)` populated with `spkW8.zeroExtend 64`, `spkW24`, `spkW16`, `spkW0`). -/
def r1b_opkStage1SpkAt (fsp : BitVec 64)
    (spkW0 : BitVec 64) (spkW8 : BitVec 32) (spkW16 spkW24 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (w0e0 w0e4 w9 : BitVec 32) (w13 : BitVec 16) (w15 w23 : BitVec 64) (b31 : BitVec 8) :
    SepProp :=
  memRegion fsp 0x0e0 ∗
    ((fsp + 0x0e0#64) ↦₃₂ w0e0) ∗
    ((fsp + 0x0e4#64) ↦₃₂ w0e4) ∗
    ((fsp + 0x0e8#64) ↦₆₄ w15) ∗
    ((fsp + 0x0f0#64) ↦₆₄ spkW8.zeroExtend 64) ∗
    ((fsp + 0x0f8#64) ↦₆₄ spkW24) ∗
    ((fsp + 0x100#64) ↦₆₄ spkW16) ∗
    ((fsp + 0x108#64) ↦₆₄ spkW0) ∗
    memRegion (fsp + 0x1d0#64) 0x50 ∗
    ((fsp + 0x220#64) ↦₆₄ w23) ∗
    ((fsp + 0x228#64) ↦₈ b31) ∗
    memRegion (fsp + 0x229#64) 0x37 ∗
    memRegion (fsp + 0x2c0#64) 0xf8 ∗
    Wire.sevenBytesHeadAt (fsp + 0x3b8#64) b0 b1 b2 b3 b4 b5 b6 ∗
    memRegion (fsp + 0x3bf#64) 0x19 ∗
    ((fsp + 0x3d8#64) ↦₃₂ w9) ∗
    ((fsp + 0x3dc#64) ↦₁₆ w13) ∗
    memRegion (fsp + 0x3de#64) 0xf2

theorem r1b_opkStage1Spk_to_regions (fsp : BitVec 64)
    (spkW0 : BitVec 64) (spkW8 : BitVec 32) (spkW16 spkW24 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (w0e0 w0e4 w9 : BitVec 32) (w13 : BitVec 16) (w15 w23 : BitVec 64) (b31 : BitVec 8) :
    r1b_opkStage1SpkAt fsp spkW0 spkW8 spkW16 spkW24
      b0 b1 b2 b3 b4 b5 b6 w0e0 w0e4 w9 w13 w15 w23 b31 ⊢
      memRegion fsp 0x110 ∗
        memRegion (fsp + 0x1d0#64) 0x90 ∗
        memRegion (fsp + 0x2c0#64) 0x210 := by
  have h0f0 :
      ((fsp + 0x0f0#64) ↦₆₄ spkW8.zeroExtend 64) ∗
        ((fsp + 0x0f8#64) ↦₆₄ spkW24) ∗
        ((fsp + 0x100#64) ↦₆₄ spkW16) ∗
        ((fsp + 0x108#64) ↦₆₄ spkW0) ⊢ memRegion (fsp + 0x0f0#64) 0x20 := by
    refine Entails.trans (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (pointsTo64_entails_memRegion _ _)))) ?_
    rw [r1b_join_region fsp 0x100 8 8, r1b_join_region fsp 0x0f8 8 16,
      r1b_join_region fsp 0x0f0 8 24]
    exact Entails.refl _
  refine Entails.trans ?_
    (r1b_opkStage1_to_regions fsp b0 b1 b2 b3 b4 b5 b6 w0e0 w0e4 w9 w13 w15 w23 b31)
  dsimp only [r1b_opkStage1SpkAt, r1b_opkStage1At]
  exact r1b_entails_frame (by ac_rfl) h0f0 (by ac_rfl)

theorem r1b_sig64_to_ownedBytes (A : RustAlloc) (ptr : BitVec 64)
    (sig : List (BitVec 8)) (hne : ptr ≠ 0) (hlen : sig.length = 64) :
    (A.live ptr 64 1 ∗ (ptr ↦ₛ sig)) ⊢ ownedBytes A 64#64 ptr 64#64 sig := by
  have h64 : BitVec.ofNat 64 sig.length = 64#64 := by rw [hlen]
  conv => rhs; rw [show ownedBytes A 64#64 ptr 64#64 sig = ownedBytes A 64#64 ptr (BitVec.ofNat 64 sig.length) sig by rw [h64]]
  refine Entails.trans ?_
    (r1b_ownedBytes_rejoin A 64#64 ptr sig (by simp [hlen]) (by decide) hne)
  dsimp only [r1b_ownedRest]
  have hc : (64#64 : BitVec 64) ≠ 0 := by decide
  have hsub : (64#64 : BitVec 64).toNat - sig.length = 0 := by simp [hlen]
  simp only [hc, ↓reduceIte, hsub, memRegion_zero, sepConj_emp]
  exact Entails.of_eq (by ac_rfl)

private theorem r1b_spk_err_at_2adc {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {i : Nat} {v188 kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen : BitVec 64}
    {kpkBs spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext) (hdrop : RunDrop.DropSpeOwnedOk img A ext)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtx img ext g d s0 s 0x2adc)
    (hi : RunDrop.PlainSpeTag i)
    (hx12 : s.readReg64 (.gpr 12#5) = speWord i)
    (hx1 : s.readReg64 (.gpr 1#5) = kpkCap)
    (hx26 : s.readReg64 (.gpr 26#5) = kpkPtr)
    (hpanic : PanicK g s0 Qp) (hrej : RejectK img ext A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (ownedBytes A kpkCap kpkPtr kpkLen kpkBs ∗
        ownedBytes A spkCap spkPtr spkLen spkBs ∗
        ownedBytes A regCap regPtr regLen regBs ∗
        r1b_errCommon A g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        ((fsp + 0x188#64) ↦₆₄ v188) ∗ memRegion (fsp + 0x190#64) 8 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16 ∗ memRegion (fsp + 0x4d0#64) 48)
      Q Qp (runOom s0) := by
  intro fsp
  refine MainHops.sepWPp_weaken_pre ?_
    (r1b_cleanup_2adc (v188 := v188)
      (kpkCap := kpkCap) (kpkPtr := kpkPtr) (kpkLen := kpkLen) (kpkBs := kpkBs)
      (spkCap := spkCap) (spkPtr := spkPtr) (spkLen := spkLen) (spkBs := spkBs)
      (regCap := regCap) (regPtr := regPtr) (regLen := regLen) (regBs := regBs)
      hh hdrop hbnd hc hx1 hx26 hpanic hrej)
  conv => lhs; rw [← emp_sepConj (ownedBytes A kpkCap kpkPtr kpkLen kpkBs ∗ _)]
  rw [hx12]
  exact sepConj_mono_left (r1b_SpePayload_plain A hi _ _ _ _ _ _ _ _)

set_option maxHeartbeats 600000 in
/-- Error exit from `<PublicKey>::deserialize` on `spkKey` (`0x24fc → 0x2adc`). -/
theorem r1b_spk_err_24fc {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {kpkCap kpkPtr spkCap spkPtr regCap regPtr v188_in : BitVec 64}
    {kpkBs spkBs spkKey regBs : List (BitVec 8)}
    {e : SignalProtocolError}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext) (hdrop : RunDrop.DropSpeOwnedOk img A ext)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtx img ext g d s0 s 0x24fc)
    (_hd : PublicKey.deserialize spkKey = .error e)
    (hpanic : PanicK g s0 Qp) (hrej : RejectK img ext A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (Wire.deserializeResult33At (fsp + 0x4d0#64) (.error e) ∗
        memRegion (fsp + 0x4f1#64) 15 ∗
        ownedBytes A kpkCap kpkPtr (BitVec.ofNat 64 kpkBs.length) kpkBs ∗
        ownedBytes A spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
        ownedBytes A regCap regPtr 4#64 regBs ∗
        r1b_errCommon A g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 8 ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ memRegion (fsp + 0x158#64) 8 ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        ((fsp + 0x188#64) ↦₆₄ v188_in) ∗ memRegion (fsp + 0x190#64) 8 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16)
      Q Qp (runOom s0) := by
  intro fsp
  have hst := hc.st
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hst.spAligned
  have hal4e0 : (fsp + 0x4e0#64) &&& 7#64 = 0#64 := by bv_bits
  let _ := hal; let _ := hal4e0
  code_fetches_range CryptoVerification.libsignalSessionCode r1bDecDeserCloneErr img.base
    (Rust.withPanics ext) r1b_run_fnOff (num% (ls_off% "libsignal_cli::run")) 0x24fc 0x20
  code_fetches_range CryptoVerification.libsignalSessionCode r1bDecDeserCloneErr img.base
    (Rust.withPanics ext) r1b_run_fnOff (num% (ls_off% "libsignal_cli::run")) 0x2634 0x20
  code_fetches_range CryptoVerification.libsignalSessionCode r1bDecDeserCloneErr img.base
    (Rust.withPanics ext) r1b_run_fnOff (num% (ls_off% "libsignal_cli::run")) 0x26cc 0x40
  have hpc0 := hst.pc
  dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc0 ⊢
  generalize_entry heq_fnBase :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase
  examples_hide_fetches
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
    dsimp only [Wire.deserializeResult33At]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x2adc#64) hst.inv
    have hpc := hpc0; have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    clear hpc hrun hsp
    refine r1b_bind_state fun sm hsm hinv_m => ?_
    change SepWPp (mProg img ext) _ _ _ _ _ _
    have hc_m : r1b_ErrCtx img ext g d s0 sm 0x2adc := hc.of_step
      { pc := by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm, arm64_norm]
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
      have h33 := Wire.memRegion33_of_err_base (fsp + 0x4d0#64) 0#8
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at h33
      refine Entails.trans (r1b_entails_frame (by r1b_ac) h33 (by r1b_ac)) ?_
      rw [r1b_join_region fsp 0x4d0 33 15]; exact Entails.refl _
    exact MainHops.sepWPp_weaken_pre
      (r1b_entails_frame (by r1b_ac)
        (sepConj_mono h4d0 (sepConj_mono (h120_join kpkPtr) (h150_join kpkCap))) (by r1b_ac))
      (r1b_spk_err_at_2adc (i := 7) (v188 := 0#64)
        (kpkCap := kpkCap) (kpkPtr := kpkPtr) (kpkLen := BitVec.ofNat 64 kpkBs.length) (kpkBs := kpkBs)
        (spkCap := spkCap) (spkPtr := spkPtr) (spkLen := BitVec.ofNat 64 spkBs.length) (spkBs := spkBs)
        (regCap := regCap) (regPtr := regPtr) (regLen := 4#64) (regBs := regBs)
        hh hdrop hbnd hc_m (by decide)
        (by simp [hsm, arm64_norm, speWord])
        (by simp [hsm, arm64_norm])
        (by simp [hsm, arm64_norm])
        hpanic hrej)
  | badKeyType t =>
    dsimp only [Wire.deserializeResult33At]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x2adc#64) hst.inv
    have hpc := hpc0; have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    clear hpc hrun hsp
    refine r1b_bind_state fun sm hsm hinv_m => ?_
    change SepWPp (mProg img ext) _ _ _ _ _ _
    have hc_m : r1b_ErrCtx img ext g d s0 sm 0x2adc := hc.of_step
      { pc := by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm, arm64_norm]
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
      have h33 := Wire.memRegion33_of_err_badKeyType (fsp + 0x4d0#64) t
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at h33
      refine Entails.trans (r1b_entails_frame (by r1b_ac) h33 (by r1b_ac)) ?_
      rw [r1b_join_region fsp 0x4d0 33 15]; exact Entails.refl _
    exact MainHops.sepWPp_weaken_pre
      (r1b_entails_frame (by r1b_ac)
        (sepConj_mono h4d0 (sepConj_mono (h120_join kpkPtr) (h150_join kpkCap))) (by r1b_ac))
      (r1b_spk_err_at_2adc (i := 8) (v188 := 0#64)
        (kpkCap := kpkCap) (kpkPtr := kpkPtr) (kpkLen := BitVec.ofNat 64 kpkBs.length) (kpkBs := kpkBs)
        (spkCap := spkCap) (spkPtr := spkPtr) (spkLen := BitVec.ofNat 64 spkBs.length) (spkBs := spkBs)
        (regCap := regCap) (regPtr := regPtr) (regLen := 4#64) (regBs := regBs)
        hh hdrop hbnd hc_m (by decide)
        (by simp [hsm, arm64_norm, speWord])
        (by simp [hsm, arm64_norm])
        (by simp [hsm, arm64_norm])
        hpanic hrej)
  | badKeyLength n =>
    dsimp only [Wire.deserializeResult33At]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x2adc#64) hst.inv
    have hpc := hpc0; have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    clear hpc hrun hsp
    refine r1b_bind_state fun sm hsm hinv_m => ?_
    change SepWPp (mProg img ext) _ _ _ _ _ _
    have hc_m : r1b_ErrCtx img ext g d s0 sm 0x2adc := hc.of_step
      { pc := by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm, arm64_norm]
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
      have h33 := Wire.memRegion33_of_err_badKeyLength (fsp + 0x4d0#64) n
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at h33
      refine Entails.trans (r1b_entails_frame (by r1b_ac) h33 (by r1b_ac)) ?_
      rw [r1b_join_region fsp 0x4d0 33 15]; exact Entails.refl _
    exact MainHops.sepWPp_weaken_pre
      (r1b_entails_frame (by r1b_ac)
        (sepConj_mono h4d0 (sepConj_mono (h120_join kpkPtr) (h150_join kpkCap))) (by r1b_ac))
      (r1b_spk_err_at_2adc (i := 9) (v188 := BitVec.ofNat 64 n &&& -256#64)
        (kpkCap := kpkCap) (kpkPtr := kpkPtr) (kpkLen := BitVec.ofNat 64 kpkBs.length) (kpkBs := kpkBs)
        (spkCap := spkCap) (spkPtr := spkPtr) (spkLen := BitVec.ofNat 64 spkBs.length) (spkBs := spkBs)
        (regCap := regCap) (regPtr := regPtr) (regLen := 4#64) (regBs := regBs)
        hh hdrop hbnd hc_m (by decide)
        (by simp [hsm, arm64_norm, speWord])
        (by simp [hsm, arm64_norm])
        (by simp [hsm, arm64_norm])
        hpanic hrej)
  | _ =>
    dsimp only [Wire.deserializeResult33At]
    exact SepWPp.pure_elim False.elim

set_option maxHeartbeats 400000 in
/-- Shared `kem::Key::deserialize` error cleanup (`0x2654 → 0x2adc`) freeing the 64-byte `spkSigPtr` buffer for plain `SignalProtocolError` tag `i`. -/
theorem r1b_kem_err_2654 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {i : Nat}
    {spkW0 : BitVec 64} {spkW8 : BitVec 32} {spkW16 spkW24 : BitVec 64}
    {b0 b1 b2 b3 b4 b5 b6 : BitVec 8}
    {w0e0 w0e4 w9 : BitVec 32} {w13 : BitVec 16} {w15 w23 : BitVec 64} {b31 : BitVec 8}
    {r0 r1 r2 r3 : BitVec 8} {v11c : BitVec 32}
    {spkSigPtr kpkCap kpkPtr spkCap spkPtr regCap regPtr : BitVec 64}
    {v130 v138 w4d8 w4e0 v188_in : BitVec 64}
    {spkSig kpkBs spkBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext) (hdrop : RunDrop.DropSpeOwnedOk img A ext)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtx img ext g d s0 s 0x2654)
    (hi : RunDrop.PlainSpeTag i)
    (hspk_ptr : spkSigPtr ≠ 0)
    (hspk_sig : spkSig.length = 64)
    (hpanic : PanicK g s0 Qp) (hrej : RejectK img ext A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (((fsp + 0x4d0#64) ↦₆₄ speWord i) ∗
        ((fsp + 0x4d8#64) ↦₆₄ w4d8) ∗
        ((fsp + 0x4e0#64) ↦₆₄ w4e0) ∗
        memRegion (fsp + 0x4e8#64) 24 ∗
        A.live spkSigPtr 64 1 ∗ (spkSigPtr ↦ₛ spkSig) ∗
        ownedBytes A kpkCap kpkPtr (BitVec.ofNat 64 kpkBs.length) kpkBs ∗
        ownedBytes A spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
        ownedBytes A regCap regPtr 4#64 [r0, r1, r2, r3] ∗
        r1b_invCoreBase A img g d s0 ∗ logOff img ∗
        ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
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
        stackAt fsp (resStack - runFrame) ∗ A.pool)
      Q Qp (runOom s0) := by
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
  refine r1b_sepWPp_frame (by r1b_ac)
    (r1b_sig64_to_ownedBytes A spkSigPtr spkSig hspk_ptr hspk_sig) (by r1b_ac) ?_
  code_fetches_range CryptoVerification.libsignalSessionCode r1bDecDeserCloneErr img.base
    (Rust.withPanics ext) r1b_run_fnOff (num% (ls_off% "libsignal_cli::run")) 0x2654 0x54
  code_fetches_range CryptoVerification.libsignalSessionCode r1bDecDeserCloneErr img.base
    (Rust.withPanics ext) r1b_run_fnOff (num% (ls_off% "libsignal_cli::run")) 0x270c 0x34
  have hpc0 := hst.pc
  dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc0 ⊢
  generalize_entry heq_fnBase :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase
  examples_hide_fetches
  apply MainHops.sepWPp_seq_inImage
    (mid := fnBase + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_cli::run")) hst.inv
  have hpc := hpc0; have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  clear hpc hrun hsp
  refine r1b_bind_state fun sm1 hsm1 hinv1 => ?_
  change SepWPp (mProg img ext) _ _ _ _ _ _
  refine r1b_call_frame <|
    r1b_call_dealloc_ownedBytes (cap := 64#64) (ptr := spkSigPtr) (len := 64#64) (bs := spkSig)
      hh hbnd hinv1
      (by dsimp only [mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm1, arm64_norm])
      (by simp [hsm1, arm64_norm, hst.run])
      (by simpa [hsm1, arm64_norm] using hst.sp)
      (by simpa [hsm1, arm64_norm] using hst.fp)
      (by simpa [calleeSavedVRegs, hsm1, arm64_norm] using hst.vregs)
      hst.spAligned (retOff := 0x26a0)
      (by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm1, arm64_norm])
      (by simp [hsm1, arm64_norm])
      (by simp [hsm1, arm64_norm])
      (by simp [hsm1, arm64_norm])
      (by decide) hpanic
      (fun sf1 hin1 hcs1 hfs1 htr1 => ?_)
  have hpc1 := hin1.pc
  dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc1 ⊢
  rw [heq_fnBase] at hpc1
  apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x2adc#64) hin1.inv
  have hpc := hpc1; have hrun := hin1.run; have hsp : sf1.sp = fsp := hin1.sp
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  clear hpc hrun hsp
  refine r1b_bind_state fun sm2 hsm2 hinv2 => ?_
  change SepWPp (mProg img ext) _ _ _ _ _ _
  have htr_tot : sm2.trace = s.trace := by
    simp only [hsm2, arm64_norm]
    exact htr1.trans (by simp [hsm1, arm64_norm])
  have hfs_tot : sm2.fs.files = s.fs.files := by
    simp only [hsm2, arm64_norm]
    exact (congrArg FsState.files hfs1).trans (by simp [hsm1, arm64_norm])
  have hc2 : r1b_ErrCtx img ext g d s0 sm2 0x2adc := hc.of_step
    { pc := by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm2, arm64_norm]
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
  refine r1b_sepWPp_frame (by r1b_ac)
    (sepConj_mono
      (r1b_opkStage1Spk_to_regions fsp spkW0 spkW8 spkW16 spkW24
        b0 b1 b2 b3 b4 b5 b6 w0e0 w0e4 w9 w13 w15 w23 b31)
      (sepConj_mono h4d0 (sepConj_mono h110 (sepConj_mono h11c
        (sepConj_mono h120 (sepConj_mono h130 (sepConj_mono h150 (sepConj_mono h178 h1a8))))))))
    (by r1b_ac) ?_
  have hinv_rejoin :
      r1b_invCoreBase A img g d s0 ∗
        memRegion (fsp + 0x1d0#64) 0x90 ∗ memRegion (fsp + 0x2c0#64) 0x210 ⊢
      r1b_invCore A img g d s0 :=
    Entails.of_eq (r1b_invCore_split_mid A img g d s0).symm
  refine r1b_sepWPp_frame (by r1b_ac) hinv_rejoin (by r1b_ac) ?_
  have h164 : ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ⊢ memRegion (fsp + 0x164#64) 4 :=
    pointsTo32_entails_memRegion _ _
  have h190 : ((fsp + 0x190#64) ↦₆₄ d.ikW3) ⊢ memRegion (fsp + 0x190#64) 8 :=
    pointsTo64_entails_memRegion _ _
  refine r1b_sepWPp_frame (by r1b_ac) (sepConj_mono h164 h190) (by r1b_ac) ?_
  have herr_c := r1b_invCore_to_errCommon A img g d s0 resStack
  dsimp only at herr_c
  refine r1b_sepWPp_frame (by r1b_ac) herr_c (by r1b_ac) ?_
  exact MainHops.sepWPp_weaken_pre (Entails.of_eq (by r1b_ac))
    (r1b_spk_err_at_2adc (i := i) (v188 := w4e8)
      (kpkCap := kpkCap) (kpkPtr := kpkPtr) (kpkLen := BitVec.ofNat 64 kpkBs.length) (kpkBs := kpkBs)
      (spkCap := spkCap) (spkPtr := spkPtr) (spkLen := BitVec.ofNat 64 spkBs.length) (spkBs := spkBs)
      (regCap := regCap) (regPtr := regPtr) (regLen := 4#64) (regBs := [r0, r1, r2, r3])
      hh hdrop hbnd hc2 hi
      (by simp [hsm2, arm64_norm])
      (by simp [hsm2, arm64_norm])
      (by simp [hsm2, arm64_norm])
      hpanic hrej)


end CryptoVerification.SignalSession.Cli.RunCompose
