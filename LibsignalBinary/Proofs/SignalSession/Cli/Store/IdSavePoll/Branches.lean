/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.CallSpecs
public meta import LibsignalBinary.Proofs.Common.InImageKit -- shake: keep
public import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.Fetches
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
public meta import Lean -- shake: keep

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.Store.IdSavePoll.Helpers

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.CodeLayout CryptoVerification.SignalSession.Cli

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm] calleeSavedVRegs_writeVReg128_0

@[arm64_norm, wp_norm]
theorem ispoll_extra_add_eqs (a sp v1 v2 : BitVec 64) :
    a + 0#64 = a ∧
    a + 8#64 + 8#64 = a + 16#64 ∧
    a + 16#64 + 8#64 = a + 24#64 ∧
    sp - 0x80#64 + 8#64 = sp - 0x78#64 ∧
    (v2 ++ v1 : BitVec 128).extractLsb' 0 64 = v1 ∧
    (v2 ++ v1 : BitVec 128).extractLsb' 64 64 = v2 := by
  refine ⟨by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_bits, by bv_bits⟩

@[simp, arm64_norm, wp_norm] def offAfterGet     : BitVec 64 := 68#64
@[simp, arm64_norm, wp_norm] def offAfterDecode  : BitVec 64 := 104#64
@[simp, arm64_norm, wp_norm] def offAfterDealloc : BitVec 64 := 220#64
@[simp, arm64_norm, wp_norm] def offAfterEq      : BitVec 64 := 304#64
@[simp, arm64_norm, wp_norm] def offErrShuffle   : BitVec 64 := 316#64
@[simp, arm64_norm, wp_norm] def offErrLdr60     : BitVec 64 := 332#64
@[simp, arm64_norm, wp_norm] def offErrStur11    : BitVec 64 := 352#64
@[simp, arm64_norm, wp_norm] def offOkTail       : BitVec 64 := 400#64
@[simp, arm64_norm, wp_norm] def offAfterSer     : BitVec 64 := 412#64
@[simp, arm64_norm, wp_norm] def offAfterPut     : BitVec 64 := 440#64
@[simp, arm64_norm, wp_norm] def offEpilogue     : BitVec 64 := 444#64
@[simp, arm64_norm, wp_norm] def offEpiLdur11    : BitVec 64 := 472#64
@[simp, arm64_norm, wp_norm] def offEpiStr44     : BitVec 64 := 488#64

theorem sepWP_conseq {prog : Program} {pc : BitVec 64} {s : State}
    {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : P ⊢ P') (hw : SepWP prog pc s P' post oom) :
    SepWP prog pc s P post oom := by
  unfold SepWP at hw ⊢
  exact fun R hm => hw R (Satisfies.mono (sepConj_mono_left h) hm)

theorem sepWP_step_to {prog : Program} {mid target : BitVec 64} {s : State}
    {P : SepProp} {post : State → SepProp → Prop}
    (h : SepWP prog mid s P (fun sm Pm => SepWP prog target sm Pm post)) :
    SepWP prog target s P post :=
  SepWP.seq (mid := mid) h fun _ _ _ _ hnext => hnext

theorem sepWPp_step_to_frozen {prog : Program} {img : Obj.Image} {ret mid : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hinv : ImgCallInv img s)
    (h : SepWP prog mid s P
      (fun sm Pm => img.FrozenLoaded sm → sm.symtab = img.symtab → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP_frozen hinv.1 hinv.2 h

theorem sepWPp_frame_fold {prog : Program} {ret : BitVec 64} {s : State}
    {A B P Rest : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : A ⊢ B) (heq : P = A ∗ Rest)
    (hw : SepWPp prog ret s (B ∗ Rest) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom :=
  fun R hm hL =>
    hw R (Satisfies.mono (sepConj_mono_left (Entails.trans (Entails.of_eq heq) (sepConj_mono_left h))) hm) hL

theorem ispoll_sep_assoc_r (P Q R : SepProp) : (P ∗ Q) ∗ R = P ∗ (Q ∗ R) := by ac_rfl
theorem ispoll_sep_swap (A B : SepProp) : A ∗ B = B ∗ A := by ac_rfl
theorem ispoll_sep_pull (B A R : SepProp) : B ∗ (A ∗ R) = A ∗ (B ∗ R) := by ac_rfl
theorem ispoll_sep_emp_r (P : SepProp) : P ∗ emp = P := sepConj_emp P
theorem ispoll_sep_congr_l {P P' : SepProp} (Q : SepProp) (h : P = P') : P ∗ Q = P' ∗ Q :=
  congrArg (· ∗ Q) h
theorem ispoll_sep_congr_r (P : SepProp) {Q Q' : SepProp} (h : Q = Q') : P ∗ Q = P ∗ Q' :=
  congrArg (P ∗ ·) h

section FrameTactics
open Lean Elab Tactic Meta

private meta partial def spineFnArgs (e : Expr) : Expr × Array Expr :=
  let rec go (e : Expr) (acc : List Expr) : Expr × Array Expr :=
    match e with
    | .mdata _ b => go b acc
    | .app f a   => go f (a.consumeMData :: acc)
    | _          => (e, acc.toArray)
  go e []

private meta partial def flattenSep (e : Expr) : Array Expr :=
  let (fn, args) := spineFnArgs e
  if fn.constName? == some ``Arm64.sepConj && args.size == 2 then
    flattenSep args[0]! ++ flattenSep args[1]!
  else
    #[e.consumeMData]

private meta def mkSepList (es : List Expr) : Expr :=
  match es with
  | [] => mkConst ``Arm64.emp
  | [x] => x
  | x :: xs => mkApp2 (mkConst ``Arm64.sepConj) x (mkSepList xs)

private meta def atomsMatch (p a : Expr) : MetaM Bool := do
  let p := p.consumeMData
  let a := a.consumeMData
  if p == a then return true
  let (pfn, pargs) := spineFnArgs p
  let (afn, aargs) := spineFnArgs a
  if pfn != afn || pargs.size != aargs.size then
    return false
  for i in [0 : pargs.size] do
    let pi := pargs[i]!
    let ai := aargs[i]!
    if pi != ai then
      let ty ← inferType pi
      let ok ← if ty.consumeMData.isConstOf ``Arm64.SepProp then pure false
               else withoutModifyingState (isDefEq pi ai)
      if !ok then return false
  return true

private meta def appendNorm (xs ys : List Expr) : MetaM Expr := do
  if ys.isEmpty then
    return mkApp (mkConst ``ispoll_sep_emp_r) (mkSepList xs)
  match xs with
  | [] => mkEqRefl (mkSepList ys)
  | [x] => mkEqRefl (mkApp2 (mkConst ``Arm64.sepConj) x (mkSepList ys))
  | x :: rest =>
    let restSep := mkSepList rest
    let ySep := mkSepList ys
    let rySep := mkSepList (rest ++ ys)
    let h_ry ← appendNorm rest ys
    let h1 := mkAppN (mkConst ``ispoll_sep_assoc_r) #[x, restSep, ySep]
    let h2 := mkAppN (mkConst ``ispoll_sep_congr_r)
      #[x, mkApp2 (mkConst ``Arm64.sepConj) restSep ySep, rySep, h_ry]
    mkEqTrans h1 h2

private meta partial def normSep (e : Expr) : MetaM (List Expr × Expr) := do
  let (fn, args) := spineFnArgs e
  if fn.constName? == some ``Arm64.sepConj && args.size == 2 then
    let (xs, hx) ← normSep args[0]!
    let (ys, hy) ← normSep args[1]!
    let xSep := mkSepList xs
    let ySep := mkSepList ys
    let h_l := mkAppN (mkConst ``ispoll_sep_congr_l) #[args[0]!, xSep, args[1]!, hx]
    let h_r := mkAppN (mkConst ``ispoll_sep_congr_r) #[xSep, args[1]!, ySep, hy]
    let h_app ← appendNorm xs ys
    return (xs ++ ys, ← mkEqTrans h_l (← mkEqTrans h_r h_app))
  else
    let a := e.consumeMData
    return ([a], ← mkEqRefl a)

private meta def extractOne (ps : List Expr) (a : Expr) :
    MetaM (Option (Expr × List Expr × Expr)) := do
  match ps with
  | [] => return none
  | [p] =>
    if ← atomsMatch p a then return some (p, [], ← mkEqRefl p)
    else return none
  | p :: rest =>
    if ← atomsMatch p a then
      return some (p, rest, ← mkEqRefl (mkSepList (p :: rest)))
    else
      match ← extractOne rest a with
      | none => return none
      | some (m, rem', h_sub) =>
        let restSep := mkSepList rest
        let mRemSep := mkSepList (m :: rem')
        let h1 := mkAppN (mkConst ``ispoll_sep_congr_r) #[p, restSep, mRemSep, h_sub]
        match rem' with
        | [] =>
          let h2 := mkAppN (mkConst ``ispoll_sep_swap) #[p, m]
          return some (m, [p], ← mkEqTrans h1 h2)
        | _ :: _ =>
          let remSep := mkSepList rem'
          let h2 := mkAppN (mkConst ``ispoll_sep_pull) #[p, m, remSep]
          return some (m, p :: rem', ← mkEqTrans h1 h2)

private meta def extractMany (pExpr : Expr) (ps : List Expr) :
    List Expr → MetaM (List Expr × List Expr × Expr)
  | [] => do return ([], ps, ← mkEqRefl (mkSepList ps))
  | a :: tailAtoms => do
    let some (m, rem1, h1) ← extractOne ps a
      | throwError "ispoll_frame: atom not found in precondition:\n  {a}\npre:\n  {pExpr}"
    let (ms, remFinal, h2) ← extractMany pExpr rem1 tailAtoms
    if rem1.isEmpty then
      return ([m], [], h1)
    else
      let h_step := mkAppN (mkConst ``ispoll_sep_congr_r)
        #[m, mkSepList rem1, mkSepList (ms ++ remFinal), h2]
      return (m :: ms, remFinal, ← mkEqTrans h1 h_step)

private meta def mkSplitEqProof (pExpr aExpr : Expr) : TacticM (Expr × Expr) := do
  let (ps, hpNorm) ← normSep pExpr
  let (aAtoms, haNorm) ← normSep aExpr
  let (matched, rem, hPerm) ← extractMany pExpr ps aAtoms
  let restExpr := mkSepList rem
  let aSep := mkSepList aAtoms
  let hApp ← appendNorm matched rem
  let g1 ← mkEqTrans hpNorm (← mkEqTrans hPerm (← mkEqSymm hApp))
  let g2 := mkAppN (mkConst ``ispoll_sep_congr_l) #[aSep, aExpr, restExpr, ← mkEqSymm haNorm]
  let heq ← mkEqTrans g1 g2
  return (restExpr, heq)

/-- Close `lhs = rhs` between permutations of `SepProp` atoms in O(N²) steps without `ac_rfl`. -/
elab "ispoll_ac_rfl" : tactic => withMainContext do
  let g ← getMainGoal
  let gty ← instantiateMVars (← g.getType)
  let (efn, eargs) := spineFnArgs gty
  if efn.constName? != some ``Eq || eargs.size != 3 then
    throwError "ispoll_ac_rfl expected equality goal, got: {gty}"
  let lhs := eargs[1]!
  let rhs := eargs[2]!
  let (rem, heq) ← mkSplitEqProof lhs rhs
  if !rem.isConstOf ``Arm64.emp then
    throwError "ispoll_ac_rfl: leftover atoms on LHS:\n  {rem}"
  let hEmp := mkApp (mkConst ``ispoll_sep_emp_r) rhs
  g.assign (← mkEqTrans heq hEmp)
  let gs ← getGoals
  setGoals (gs.filter (· != g))

elab "ispoll_rw_pre " h:term : tactic => withMainContext do
  let g0 ← getMainGoal
  let gty0 ← instantiateMVars (← g0.getType)
  let gty := gty0.consumeMData.headBeta.consumeMData
  let g ← if gty == gty0 then pure g0 else g0.replaceTargetDefEq gty
  let otherGoals := (← getGoals).filter (· != g0)
  let hExpr ← elabTerm h none
  let hTy := (← instantiateMVars (← inferType hExpr)).consumeMData.headBeta.consumeMData
  let (hfn, hargs) := spineFnArgs hTy
  if hfn.constName? != some ``Eq || hargs.size != 3 then
    throwError "ispoll_rw_pre expects an equality proof, got: {hTy}"
  let aExpr := hargs[1]!
  let bExpr := hargs[2]!
  let (fn, args) := spineFnArgs gty
  if args.size < 4 then
    throwError "ispoll_rw_pre expected goal of arity ≥ 4, got: {gty}"
  let pExpr := args[3]!
  let (restExpr, heqExpr) ← mkSplitEqProof pExpr aExpr
  let rhs2 := mkApp2 (mkConst ``Arm64.sepConj) bExpr restExpr
  let lamSep := Lean.mkLambda `x .default (mkConst ``Arm64.SepProp)
    (mkApp2 (mkConst ``Arm64.sepConj) (.bvar 0) restExpr)
  let hpEq ← mkEqTrans heqExpr (← mkCongrArg lamSep hExpr)
  let newGoalTy := mkAppN fn (args.set! 3 rhs2)
  let hwMVar ← mkFreshExprMVar (some newGoalTy)
  let ctxLam := Lean.mkLambda `P .default (mkConst ``Arm64.SepProp)
    (mkAppN fn (args.set! 3 (.bvar 0)))
  let hGoalEq ← mkCongrArg ctxLam (← mkEqSymm hpEq)
  g.assign (← mkEqMP hGoalEq hwMVar)
  setGoals (hwMVar.mvarId! :: otherGoals)

elab "ispoll_fold_pre " h:term : tactic => withMainContext do
  let g0 ← getMainGoal
  let gty0 ← instantiateMVars (← g0.getType)
  let gty := gty0.consumeMData.headBeta.consumeMData
  let g ← if gty == gty0 then pure g0 else g0.replaceTargetDefEq gty
  let otherGoals := (← getGoals).filter (· != g0)
  let hExpr ← elabTerm h none
  let hTy := (← instantiateMVars (← inferType hExpr)).consumeMData.headBeta.consumeMData
  let (_, hargs) := spineFnArgs hTy
  let aExpr := hargs[0]!
  let bExpr := hargs[1]!
  let (fn, args) := spineFnArgs gty
  if args.size < 7 then
    throwError "ispoll_fold_pre expected 7-arg SepWPp goal, got {args.size}: {gty}"
  let #[prog, ret, s, pExpr, qExpr, qpExpr, oom] := args | unreachable!
  let (restExpr, heqExpr) ← mkSplitEqProof pExpr aExpr
  let rhs2 := mkApp2 (mkConst ``Arm64.sepConj) bExpr restExpr
  let hwMVar ← mkFreshExprMVar
    (some (mkAppN fn #[prog, ret, s, rhs2, qExpr, qpExpr, oom]))
  g.assign (mkAppN (mkConst ``sepWPp_frame_fold)
    #[prog, ret, s, aExpr, bExpr, pExpr, restExpr, qExpr, qpExpr, oom, hExpr, heqExpr, hwMVar])
  setGoals (hwMVar.mvarId! :: otherGoals)

elab "ispoll_close_frame" : tactic => do
  inImageKitClearInvHyps
  evalTactic (← `(tactic| refine Entails.of_eq ?_))
  evalTactic (← `(tactic| (conv => lhs; simp only [wp_norm, arm64_norm, *])))
  evalTactic (← `(tactic| (conv => rhs; arg 1; simp only [wp_norm, arm64_norm, *])))
  withMainContext do
    let g ← getMainGoal
    let gty ← instantiateMVars (← g.getType)
    let (efn, eargs) := spineFnArgs gty
    if efn.constName? != some ``Eq || eargs.size != 3 then
      throwError "ispoll_close_frame expected equality goal, got: {gty}"
    let lhs := eargs[1]!
    let rhs := eargs[2]!
    let (_, rargs) := spineFnArgs rhs
    let calleePre := rargs[0]!
    let fMVar := rargs[1]!
    let (restExpr, heqExpr) ← mkSplitEqProof lhs calleePre
    fMVar.mvarId!.assign restExpr
    g.assign heqExpr
    let gs ← getGoals
    setGoals (gs.filter fun m => m != g && m != fMVar.mvarId!)

end FrameTactics

/-- Shared epilogue (`+444 .. +524`): writes `x.call.out[0..48)` and `[fut + 24] := 1#8`,
restores `x19 .. x30`, pops `0xd0` bytes, and returns to `s0.readReg64 .lr`. -/
theorem ispoll_epilogue_1bc {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s : State} (x : IdPollGhost)
    (c1 c2 c3 c4 c5 c6 c7 : BitVec 8) (s16 : BitVec 64) (s24 : BitVec 8)
    (Rest : SepProp) {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr idSavePollName + offEpilogue)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0xd0#64)
    (hsp_align : s.spAligned = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = x.call.fut)
    (hx20 : s.readReg64 .x20 = x.call.out)
    (hq : ∀ sf : State,
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s.trace →
      Q sf (epilogueOut s0 x (s.readReg64 .x25)
        ((s.readReg64 .x26).truncate 32) ((s.readReg64 .x8).truncate 32)
        (s.readReg64 .x21) (s.readReg64 .x22)
        c1 c2 c3 c4 c5 c6 c7 s16 s24 ∗ Rest)) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) s
      (epiloguePre s0 x c1 c2 c3 c4 c5 c6 c7 s16 s24 ∗ Rest) Q := by
  have hfn : libsignalSessionCode.fnOff idSavePollName =
      num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}") :=
    idSavePoll_fnOff
  code_fetches CryptoVerification.libsignalSessionCode cliIdSavePollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}")) 528
  clear hfn
  dsimp only [tripleRatchetProgAtExt, offEpilogue] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr idSavePollName = entry
  examples_hide_fetches
  conv =>
    arg 4
    unfold epiloguePre overlap7View1 idSaveBoxAt savedCalleeSlots
    rw [sret48_epilogue_split x.call.out]
    unfold overlap7View1
    simp only [wp_norm, arm64_norm, ispoll_sp_eqs, out_add_eqs,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro o0; apply SepWP.exists_elim; intro o8
  apply SepWP.exists_elim; intro o12; apply SepWP.exists_elim; intro o16
  apply SepWP.exists_elim; intro o24; apply SepWP.exists_elim; intro o32
  apply SepWP.exists_elim; intro o40
  apply SepWP.exists_elim; intro b1; apply SepWP.exists_elim; intro b2
  apply SepWP.exists_elim; intro b3; apply SepWP.exists_elim; intro b4
  apply SepWP.exists_elim; intro b5; apply SepWP.exists_elim; intro b6
  apply SepWP.exists_elim; intro b7
  apply sepWP_step_to (mid := entry + offEpiLdur11)
  dsimp only [offEpiLdur11]
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  have h7_sp :
      ((s0.sp - 0xc8#64) ↦₃₂ (c4 ++ c3 ++ c2 ++ c1)) ∗
        ((s0.sp - 0xc4#64) ↦₈ c5) ∗ ((s0.sp - 0xc3#64) ↦₁₆ (c7 ++ c6)) =
      ((s0.sp - 0xc8#64) ↦₁₆ (c2 ++ c1)) ∗
        ((s0.sp - 0xc6#64) ↦₈ c3) ∗ ((s0.sp - 0xc5#64) ↦₃₂ (c7 ++ c6 ++ c5 ++ c4)) := by
    have h7 := overlap7_realign (s0.sp - 0xc8#64) c1 c2 c3 c4 c5 c6 c7
    unfold overlap7View1 overlap7View2 at h7
    simpa only [ispoll_sp_eqs, sepConj_assoc] using h7
  ispoll_rw_pre h7_sp
  conv => arg 4; simp only [sepConj_assoc]
  apply sepWP_step_to (mid := entry + offEpiStr44)
  dsimp only [offEpiStr44]
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  have h7_out :
      ((x.call.out + 41#64) ↦₃₂ (c4 ++ c3 ++ c2 ++ c1)) ∗
        ((x.call.out + 45#64) ↦₈ b5) ∗ ((x.call.out + 46#64) ↦₁₆ (b7 ++ b6)) =
      ((x.call.out + 41#64) ↦₁₆ (c2 ++ c1)) ∗
        ((x.call.out + 43#64) ↦₈ c3) ∗ ((x.call.out + 44#64) ↦₃₂ (b7 ++ b6 ++ b5 ++ c4)) := by
    have h7 := overlap7_realign (x.call.out + 41#64) c1 c2 c3 c4 b5 b6 b7
    unfold overlap7View1 overlap7View2 at h7
    simpa only [out_add_eqs, sepConj_assoc] using h7
  ispoll_rw_pre h7_out
  conv => arg 4; simp only [sepConj_assoc]
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine Eq.mpr (congrArg (Q _) ?_)
    (hq _ (by wp_norm_goal)
      (by simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm, hvregs])
      (by wp_norm_goal))
  unfold epilogueOut overlap7View2 idSaveBoxAt savedCalleeSlots
  simp only [wp_norm, arm64_norm, ispoll_sp_eqs]
  ac_rfl

/-- Shared `Ok` tail (`+400 .. +524`): serializes `x.call.call.key`, writes `peers.put`,
sets `x25 := -2`, and runs `ispoll_epilogue_1bc`. -/
theorem ispoll_ok_tail_190 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {getStk putStk stk : Nat}
    (hC : AllocContractsX img A ext)
    (hPut : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutStrName)
      (dirPutStrSpec A img putStk))
    (hstk : saveMinStk getStk putStk ≤ stk)
    (hhi : stk ≤ 2 ^ 64)
    {s0 s : State} (x : IdPollGhost)
    (gr : Except Unit (List (BitVec 8))) (o : Option IdentityKey) (c : IdentityChange)
    (c1 c2 c3 c4 c5 c6 c7 c15 : BitVec 8)
    (s16 : BitVec 64) (s24 : BitVec 8) (s32 : BitVec 64) (s40 : BitVec 8)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr idSavePollName + offOkTail)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0xd0#64)
    (hsp_align : s.spAligned = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace)
    (hinv : ImgCallInv img s)
    (hx19 : s.readReg64 .x19 = x.call.fut)
    (hx20 : s.readReg64 .x20 = x.call.out)
    (hx24 : s.readReg64 .x24 = x.self)
    (hx26 : (s.readReg64 .x26).truncate 32 = (if c == .replacedExisting then 1#32 else 0#32))
    (hx29 : s.readReg64 .x29 = s0.sp - 0x60#64)
    (hc : idSaveOf (.ok o) x.call.call.key = .ok c)
    (hnlen : x.call.call.addr.name.bytes.length < 2 ^ 32)
    (hclen : x.peers.changed.length < 2 ^ 32)
    (hgr : gr = x.peers.get rd s0.fs.files x.call.call.addr.val.name)
    (hans : IdPeerAns gr (.ok o)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) s
      (dirAt A (x.self + 0x28#64) x.peers ∗
        memRegion x.call.out 48 ∗
        idSaveBoxAt x.call.fut x.self x.call.call.addrA x.call.call.keyA 0#8 ∗
        protocolAddressAt A x.call.call.addr x.call.call.addrA ∗
        (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗
        logOff img ∗ A.pool ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - saveMinStk getStk putStk) ∗
        stackAt (s0.sp - 0xd0#64) (saveSubMax getStk putStk) ∗
        memRegion (s0.sp - 0xd0#64) 8 ∗
        overlap7View1 (s0.sp - 0xc8#64) c1 c2 c3 c4 c5 c6 c7 ∗
        ((s0.sp - 0xc1#64) ↦₈ c15) ∗
        ((s0.sp - 0xc0#64) ↦₆₄ s16) ∗
        ((s0.sp - 0xb8#64) ↦₈ s24) ∗
        memRegion (s0.sp - 0xb7#64) 7 ∗
        ((s0.sp - 0xb0#64) ↦₆₄ s32) ∗
        ((s0.sp - 0xa8#64) ↦₈ s40) ∗
        memRegion (s0.sp - 0xa7#64) 7 ∗
        memRegion (s0.sp - 0xa0#64) 16 ∗
        memRegion (s0.sp - 0x90#64) 48 ∗
        savedCalleeSlots s0)
      (fun sf P_f => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (idSavePollSpec rd pathOk A img stk).post x s0 sf))
      (fun sf P_f => P_f ⊢ (idSavePollSpec rd pathOk A img stk).onPanic x s0 sf) := by
  have hSer := ispoll_serialize_ok_at hC
  have hPut' : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr idSavePollName +
        bv% (2 ^ 64 + ls_off% "<libsignal_cli::stores::Dir>::put::<&str>" -
          ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))
      (dirPutStrSpec A img putStk) := by
    rw [dirPutStr_fnAddr_eq]; exact hPut
  have hsub_hi : saveSubMax getStk putStk ≤ 2 ^ 64 := by
    have : saveMinStk getStk putStk ≤ 2 ^ 64 := le_trans hstk hhi
    unfold saveMinStk at this; omega
  have hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) →
      (P_f ⊢ (idSavePollSpec rd pathOk A img stk).onPanic x s0 sf) := by
    intro sf P_f hp
    simp only [idSavePollSpec, Spec.inImage]
    exact Entails.pure_right hp (entails_anyHeap _)
  have hfn : libsignalSessionCode.fnOff idSavePollName =
      num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}") :=
    idSavePoll_fnOff
  code_fetches CryptoVerification.libsignalSessionCode cliIdSavePollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}")) 444
  clear hfn hC hPut
  dsimp only [tripleRatchetProgAtExt, offOkTail] at hSer hPut' hpc ⊢
  generalize_entry hentry :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr idSavePollName = entry
  examples_hide_fetches
  conv =>
    arg 4
    rw [protocolAddressAt_borrow A x.call.call.addr x.call.call.addrA]
    unfold idSaveBoxAt
    simp only [sepConj_assoc]
  apply sepWPp_step_to_frozen hinv (mid := entry +
    bv% (2 ^ 64 + ls_off% "<libsignal_core::curve::PublicKey>::serialize" -
      ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hF_ser hsym_ser
  conv =>
    arg 4
    rw [stackAt_sub_split (s0.sp - 0xd0#64) (serStk_le_saveSubMax getStk putStk) hsub_hi]
    simp only [sepConj_assoc]
  refine ispoll_call_serialize (ret_pc := entry + offAfterSer) hSer
    x.call.call.keyA x.call.call.key.publicKey ?ispollF1
    (by wp_norm_goal) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_goal) (by wp_norm_goal)
    ⟨hF_ser, hsym_ser⟩
    (by wp_norm_goal) hpan ?ispollPre1 ?_
  case ispollPre1 => ispoll_close_frame
  intro sm1 hpc1 hrun1 hsp1 hcs1 hinv1 hx1_1 htr1
  simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm,
    hsp, htr, hx19, hx20, hx24, hx29, hvregs] at hpc1 hsp1 htr1 hx1_1 hcs1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, _, hx24_1, _, hx26_1, _, _, hx29_1, hvregs_1⟩
  have hsp_al1 : sm1.spAligned = true := by
    simp only [State.spAligned] at hsp_align ⊢
    rwa [hsp1, ← hsp]
  conv => arg 4; simp only [wp_norm, arm64_norm, hsp, hsp1]
  ispoll_rw_pre (stackAt_sub_split (s0.sp - 0xd0#64) (serStk_le_saveSubMax getStk putStk) hsub_hi).symm
  ispoll_rw_pre (slot90_split_vec24 s0.sp)
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro v0
  apply SepWPp.exists_elim; intro v1
  apply SepWPp.exists_elim; intro v2
  apply sepWPp_step_to_frozen hinv1 (mid := entry +
    bv% (2 ^ 64 + ls_off% "<libsignal_cli::stores::Dir>::put::<&str>" -
      ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hF_put hsym_put
  ispoll_fold_pre (boxU8Buf_to_vecU8_33 A s0.sp (sm1.readReg64 .x0) x.call.call.key)
  conv =>
    arg 4
    rw [stackAt_sub_split (s0.sp - 0xd0#64) (putStk_le_saveSubMax getStk putStk) hsub_hi]
    simp only [sepConj_assoc]
  have hx2_len : (BitVec.ofNat 64 x.call.call.addr.name.bytes.length).toNat =
      x.call.call.addr.name.bytes.length := by
    simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  refine ispoll_call_dirPutStr (ret_pc := entry + offAfterPut) hPut'
    { self := x.self + 0x28#64
      dir := x.peers
      nameRo := false
      nameA := x.call.call.addr.name.ptr
      name := x.call.call.addr.name.bytes
      bytesV := s0.sp - 0x90#64
      bytes := x.call.call.key.serialize } ?ispollF2
    (by wp_norm_goal) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_goal) (by wp_norm_goal)
    ⟨hF_put, hsym_put⟩
    (by simp only [wp_norm, arm64_norm])
    (by wp_norm_goal)
    (by simp only [wp_norm, arm64_norm, hx2_len])
    (by wp_norm_goal) hnlen hclen hpan
    ?ispollPre2 ?_
  case ispollPre2 => ispoll_close_frame
  intro sm2 hpc2 hrun2 hsp2 hcs2 _hinv2 htr2
  simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm,
    hsp1, htr1, hx19_1, hx20_1, hx21_1, hx22_1, hx24_1, hx29_1, hvregs_1] at hpc2 hsp2 htr2 hcs2
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, _, _, _, hx26_2, _, _, _, hvregs_2⟩
  have hsp_al2 : sm2.spAligned = true := by
    simp only [State.spAligned] at hsp_align ⊢
    rwa [hsp2, ← hsp]
  have hmerge48 :
      (memRegion (s0.sp - 0x90#64) 24 ∗ memRegion (s0.sp - 0x78#64) 24) =
        memRegion (s0.sp - 0x90#64) 48 :=
    (ProofLib.memRegion_split' (b := s0.sp - 0x90#64) (n := 24) (k := 24)
      (b' := s0.sp - 0x78#64) rfl (by bv_omega) (by decide)).symm
  conv => arg 4; simp only [wp_norm, arm64_norm, hsp, hsp1, hsp2]
  ispoll_rw_pre (stackAt_sub_split (s0.sp - 0xd0#64) (putStk_le_saveSubMax getStk putStk) hsub_hi).symm
  ispoll_rw_pre hmerge48
  let restPut : SepProp :=
    dirAt A (x.self + 0x28#64)
      (x.peers.put x.call.call.addr.name.bytes x.call.call.key.serialize) ∗
    protocolAddressAt A x.call.call.addr x.call.call.addrA ∗
    (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗
    logOff img ∗ A.pool ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - saveMinStk getStk putStk) ∗
    stackAt (s0.sp - 0xd0#64) (saveSubMax getStk putStk) ∗
    memRegion (s0.sp - 0xd0#64) 8 ∗
    ((s0.sp - 0xc1#64) ↦₈ c15) ∗
    memRegion (s0.sp - 0xb7#64) 7 ∗
    ((s0.sp - 0xb0#64) ↦₆₄ s32) ∗
    ((s0.sp - 0xa8#64) ↦₈ s40) ∗
    memRegion (s0.sp - 0xa7#64) 7 ∗
    memRegion (s0.sp - 0xa0#64) 16 ∗
    memRegion (s0.sp - 0x90#64) 48
  refine sepWPp_conseq (P' := epiloguePre s0 x c1 c2 c3 c4 c5 c6 c7 s16 s24 ∗ restPut)
    (Entails.of_eq ?_) ?_
  · dsimp only [restPut]
    rw [protocolAddressAt_borrow A x.call.call.addr x.call.call.addrA]
    unfold epiloguePre idSaveBoxAt
    ac_rfl
  apply sepWPp_of_sepWP_final
  apply sepWP_step_to (mid := entry + offEpilogue)
  dsimp only [offEpilogue]
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  change SepWP (tripleRatchetProgAtExt img.base ext) _ _ _ _
  refine ispoll_epilogue_1bc (img := img) (ext := ext) x
    c1 c2 c3 c4 c5 c6 c7 s16 s24 restPut
    (by dsimp only [tripleRatchetProgAtExt]; rw [hentry]; wp_norm_goal) (by wp_norm_lhs) (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [wp_norm, arm64_norm, hvregs_2])
    (by wp_norm_goal) (by wp_norm_goal) ?_
  intro sf hspf hcsf htrf
  refine ⟨hspf, hcsf, ?_⟩
  have htr_eq : sf.trace = s0.trace := by simp only [wp_norm, arm64_norm, htr2] at htrf; exact htrf
  simp only [wp_norm, arm64_norm] at hx26
  conv =>
    lhs; arg 1
    simp only [wp_norm, arm64_norm, hx26_2, hx26_1, hx26]
  unfold epilogueOut
  refine Entails.trans (Entails.of_eq (by dsimp only [restPut]; ac_rfl :
    _ = ((x.call.out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
          ((x.call.out + 8#64) ↦₃₂ (if c == .replacedExisting then 1#32 else 0#32)) ∗
          ((x.call.out + 12#64) ↦₃₂ (sm2.readReg64 (Reg.gpr 8#5)).truncate 32) ∗
          ((x.call.out + 16#64) ↦₆₄ sm2.readReg64 (Reg.gpr 21#5)) ∗
          ((x.call.out + 24#64) ↦₆₄ sm2.readReg64 (Reg.gpr 22#5)) ∗
          ((x.call.out + 32#64) ↦₆₄ s16) ∗
          ((x.call.out + 40#64) ↦₈ s24) ∗
          overlap7View2 (x.call.out + 41#64) c1 c2 c3 c4 c5 c6 c7) ∗
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - saveMinStk getStk putStk) ∗
          stackAt (s0.sp - 0xd0#64) (saveSubMax getStk putStk) ∗
          memRegion (s0.sp - 0xd0#64) 8 ∗
          overlap7View2 (s0.sp - 0xc8#64) c1 c2 c3 c4 c5 c6 c7 ∗
          ((s0.sp - 0xc1#64) ↦₈ c15) ∗
          ((s0.sp - 0xc0#64) ↦₆₄ s16) ∗
          ((s0.sp - 0xb8#64) ↦₈ s24) ∗
          memRegion (s0.sp - 0xb7#64) 7 ∗
          ((s0.sp - 0xb0#64) ↦₆₄ s32) ∗
          ((s0.sp - 0xa8#64) ↦₈ s40) ∗
          memRegion (s0.sp - 0xa7#64) 7 ∗
          memRegion (s0.sp - 0xa0#64) 16 ∗
          memRegion (s0.sp - 0x90#64) 48 ∗
          savedCalleeSlots s0) ∗
        (dirAt A (x.self + 0x28#64)
          (x.peers.put x.call.call.addr.name.bytes x.call.call.key.serialize) ∗
          idSaveBoxAt x.call.fut x.self x.call.call.addrA x.call.call.keyA 1#8 ∗
          protocolAddressAt A x.call.call.addr x.call.call.addrA ∗
          (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗
          logOff img ∗ A.pool))) ?_
  refine Entails.trans
    (sepConj_mono (epilogueOut_ok_reassemble A x.call.out c _ _ _ s16 s24 c1 c2 c3 c4 c5 c6 c7)
      (sepConj_mono_left (restore_savePollStack s0 hstk hhi c1 c2 c3 c4 c5 c6 c7 c15 s16 s24 s32 s40))) ?_
  simp only [idSavePollSpec, Spec.inImage, sepExists_sepConj_left]
  refine Entails.sepExists_right gr (Entails.sepExists_right (.ok o) ?_)
  have hprop_ok :
      (gr = x.peers.get rd s0.fs.files x.call.call.addr.val.name ∧ sf.trace = s0.trace) ∧
      IdPeerAns gr (.ok o) :=
    ⟨⟨hgr, htr_eq⟩, hans⟩
  simp only [hc, idSavePeers, sepConj_assoc]
  exact Entails.pure_right hprop_ok (Entails.of_eq (by ac_rfl))

/-- `Err` branch after `Dir::get` returns at `+68` (`gr = .error ()`). -/
theorem ispoll_branch_err {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {getStk putStk stk : Nat}
    (hstk : saveMinStk getStk putStk ≤ stk)
    (hhi : stk ≤ 2 ^ 64)
    {s0 s : State} (x : IdPollGhost)
    (c1 c2 c3 c4 c5 c6 c7 c15 : BitVec 8)
    (s16 : BitVec 64) (s24 : BitVec 8) (s32 : BitVec 64) (s40 : BitVec 8)
    (s48 s56w : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr idSavePollName + offAfterGet)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0xd0#64)
    (hsp_align : s.spAligned = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = x.call.fut)
    (hx20 : s.readReg64 .x20 = x.call.out)
    (hx29 : s.readReg64 .x29 = s0.sp - 0x60#64)
    (herr_case : x.peers.get rd s0.fs.files x.call.call.addr.val.name = .error () ∧ s.trace = s0.trace) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) s
      (getResultAt A (s0.sp - 0x90#64) (.error ()) ∗
        dirAt A (x.self + 0x28#64) x.peers ∗
        memRegion x.call.out 48 ∗
        idSaveBoxAt x.call.fut x.self x.call.call.addrA x.call.call.keyA 0#8 ∗
        protocolAddressAt A x.call.call.addr x.call.call.addrA ∗
        (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗
        logOff img ∗ A.pool ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - saveMinStk getStk putStk) ∗
        stackAt (s0.sp - 0xd0#64) (saveSubMax getStk putStk) ∗
        memRegion (s0.sp - 0xd0#64) 8 ∗
        overlap7View1 (s0.sp - 0xc8#64) c1 c2 c3 c4 c5 c6 c7 ∗
        ((s0.sp - 0xc1#64) ↦₈ c15) ∗
        ((s0.sp - 0xc0#64) ↦₆₄ s16) ∗
        ((s0.sp - 0xb8#64) ↦₈ s24) ∗
        memRegion (s0.sp - 0xb7#64) 7 ∗
        ((s0.sp - 0xb0#64) ↦₆₄ s32) ∗
        ((s0.sp - 0xa8#64) ↦₈ s40) ∗
        memRegion (s0.sp - 0xa7#64) 7 ∗
        ((s0.sp - 0xa0#64) ↦₆₄ s48) ∗
        ((s0.sp - 0x98#64) ↦₆₄ s56w) ∗
        savedCalleeSlots s0)
      (fun sf P_f => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (idSavePollSpec rd pathOk A img stk).post x s0 sf))
      (fun sf P_f => P_f ⊢ (idSavePollSpec rd pathOk A img stk).onPanic x s0 sf) := by
  have hfn : libsignalSessionCode.fnOff idSavePollName =
      num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}") :=
    idSavePoll_fnOff
  code_fetches CryptoVerification.libsignalSessionCode cliIdSavePollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}")) 368
  clear hfn
  dsimp only [tripleRatchetProgAtExt, offAfterGet] at hpc ⊢
  generalize_entry hentry :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr idSavePollName = entry
  examples_hide_fetches
  dsimp only [getResultAt, vecResultAt]
  conv =>
    arg 4
    rw [speAt_read_invalidState_unpack A s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro bs
  apply SepWPp.exists_elim; intro cap
  apply SepWPp.exists_elim; intro ptr
  apply SepWPp.exists_elim; intro fnPtr
  apply sepWPp_of_sepWP_final
  let w5 : BitVec 64 := BitVec.ofNat 64 (utf8 "read").length
  apply sepWP_step_to (mid := entry + offErrShuffle)
  dsimp only [offErrShuffle]
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  ispoll_rw_pre (s48_split_byte7 s0.sp fnPtr w5)
  conv =>
    arg 4
    unfold overlap7View1
    simp only [ispoll_sp_eqs, sepConj_assoc]
  apply sepWP_step_to (mid := entry + offErrLdr60)
  dsimp only [offErrLdr60]
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  have h7_97 :
      ((s0.sp - 0x97#64) ↦₃₂ (w5.extractLsb' 32 8 ++ w5.extractLsb' 24 8 ++ w5.extractLsb' 16 8 ++ w5.extractLsb' 8 8)) ∗
        ((s0.sp - 0x93#64) ↦₈ w5.extractLsb' 40 8) ∗
        ((s0.sp - 0x92#64) ↦₁₆ (w5.extractLsb' 56 8 ++ w5.extractLsb' 48 8)) =
      ((s0.sp - 0x97#64) ↦₁₆ (w5.extractLsb' 16 8 ++ w5.extractLsb' 8 8)) ∗
        ((s0.sp - 0x95#64) ↦₈ w5.extractLsb' 24 8) ∗
        ((s0.sp - 0x94#64) ↦₃₂ (w5.extractLsb' 56 8 ++ w5.extractLsb' 48 8 ++ w5.extractLsb' 40 8 ++ w5.extractLsb' 32 8)) := by
    have h7 := overlap7_realign (s0.sp - 0x97#64)
      (w5.extractLsb' 8 8) (w5.extractLsb' 16 8) (w5.extractLsb' 24 8)
      (w5.extractLsb' 32 8) (w5.extractLsb' 40 8) (w5.extractLsb' 48 8) (w5.extractLsb' 56 8)
    unfold overlap7View1 overlap7View2 at h7
    simpa only [ispoll_sp_eqs, sepConj_assoc] using h7
  ispoll_rw_pre h7_97
  conv => arg 4; simp only [sepConj_assoc]
  apply sepWP_step_to (mid := entry + offErrStur11)
  dsimp only [offErrStur11]
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  have h7_c8 :
      ((s0.sp - 0xc8#64) ↦₃₂ (w5.extractLsb' 32 8 ++ w5.extractLsb' 24 8 ++ w5.extractLsb' 16 8 ++ w5.extractLsb' 8 8)) ∗
        ((s0.sp - 0xc4#64) ↦₈ c5) ∗ ((s0.sp - 0xc3#64) ↦₁₆ (c7 ++ c6)) =
      ((s0.sp - 0xc8#64) ↦₁₆ (w5.extractLsb' 16 8 ++ w5.extractLsb' 8 8)) ∗
        ((s0.sp - 0xc6#64) ↦₈ w5.extractLsb' 24 8) ∗
        ((s0.sp - 0xc5#64) ↦₃₂ (c7 ++ c6 ++ c5 ++ w5.extractLsb' 32 8)) := by
    have h7 := overlap7_realign (s0.sp - 0xc8#64)
      (w5.extractLsb' 8 8) (w5.extractLsb' 16 8) (w5.extractLsb' 24 8)
      (w5.extractLsb' 32 8) c5 c6 c7
    unfold overlap7View1 overlap7View2 at h7
    simpa only [ispoll_sp_eqs, sepConj_assoc] using h7
  ispoll_rw_pre h7_c8
  conv => arg 4; simp only [sepConj_assoc]
  apply sepWP_step_to (mid := entry + offEpilogue)
  dsimp only [offEpilogue]
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  let restErr : SepProp :=
    ((s0.sp - 0x90#64) ↦₆₄ speWord 1) ∗
    ((s0.sp - 0x88#64) ↦₆₄ cap) ∗
    ((s0.sp - 0x80#64) ↦₆₄ ptr) ∗
    ((s0.sp - 0x78#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
    ((s0.sp - 0x70#64) ↦₆₄ fnPtr) ∗
    ((s0.sp - 0x68#64) ↦₆₄ BitVec.ofNat 64 (utf8 "read").length) ∗
    (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
      if cap = 0#64 then emp
      else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗
    (fnPtr ↦ᵣ utf8 "read") ∗
    dirAt A (x.self + 0x28#64) x.peers ∗
    protocolAddressAt A x.call.call.addr x.call.call.addrA ∗
    (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗
    logOff img ∗ A.pool ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - saveMinStk getStk putStk) ∗
    stackAt (s0.sp - 0xd0#64) (saveSubMax getStk putStk) ∗
    memRegion (s0.sp - 0xd0#64) 8 ∗
    ((s0.sp - 0xc1#64) ↦₈ c15) ∗
    memRegion (s0.sp - 0xb7#64) 7 ∗
    ((s0.sp - 0xb0#64) ↦₆₄ fnPtr) ∗
    ((s0.sp - 0xa8#64) ↦₈ w5.extractLsb' 0 8) ∗
    memRegion (s0.sp - 0xa7#64) 7
  refine sepWP_conseq (P' :=
      memRegion (s0.sp - 0xa0#64) 16 ∗
      (epiloguePre s0 x
        (w5.extractLsb' 8 8) (w5.extractLsb' 16 8) (w5.extractLsb' 24 8)
        (w5.extractLsb' 32 8) (w5.extractLsb' 40 8) (w5.extractLsb' 48 8) (w5.extractLsb' 56 8)
        fnPtr (w5.extractLsb' 0 8) ∗ restErr)) ?_ ?_
  · have hback_c8 := (overlap7_realign (s0.sp - 0xc8#64)
      (w5.extractLsb' 8 8) (w5.extractLsb' 16 8) (w5.extractLsb' 24 8)
      (w5.extractLsb' 32 8) (w5.extractLsb' 40 8) (w5.extractLsb' 48 8) (w5.extractLsb' 56 8)).symm
    have hback_97 := (overlap7_realign (s0.sp - 0x97#64)
      (w5.extractLsb' 8 8) (w5.extractLsb' 16 8) (w5.extractLsb' 24 8)
      (w5.extractLsb' 32 8) (w5.extractLsb' 40 8) (w5.extractLsb' 48 8) (w5.extractLsb' 56 8)).symm
    unfold overlap7View2 at hback_c8 hback_97
    simp only [ispoll_sp_eqs] at hback_c8 hback_97
    refine Entails.trans (Entails.of_eq ?_)
      (sepConj_mono_left (s48_byte7_entails_memRegion16 s0.sp fnPtr (w5.extractLsb' 0 8)
        (w5.extractLsb' 8 8) (w5.extractLsb' 16 8) (w5.extractLsb' 24 8)
        (w5.extractLsb' 32 8) (w5.extractLsb' 40 8) (w5.extractLsb' 48 8) (w5.extractLsb' 56 8)))
    · refine Eq.trans (by dsimp only [restErr]; ac_rfl :
        _ = (((s0.sp - 0x97#64) ↦₁₆ (w5.extractLsb' 16 8 ++ w5.extractLsb' 8 8)) ∗
              ((s0.sp - 0x95#64) ↦₈ w5.extractLsb' 24 8) ∗
              ((s0.sp - 0x94#64) ↦₃₂ (w5.extractLsb' 56 8 ++ w5.extractLsb' 48 8 ++ w5.extractLsb' 40 8 ++ w5.extractLsb' 32 8))) ∗
            (((s0.sp - 0xc8#64) ↦₁₆ (w5.extractLsb' 16 8 ++ w5.extractLsb' 8 8)) ∗
              ((s0.sp - 0xc6#64) ↦₈ w5.extractLsb' 24 8) ∗
              ((s0.sp - 0xc5#64) ↦₃₂ (w5.extractLsb' 56 8 ++ w5.extractLsb' 48 8 ++ w5.extractLsb' 40 8 ++ w5.extractLsb' 32 8))) ∗
            (((s0.sp - 0xa0#64) ↦₆₄ fnPtr) ∗
              ((s0.sp - 0x98#64) ↦₈ w5.extractLsb' 0 8) ∗
              (((s0.sp - 0xc0#64) ↦₆₄ fnPtr) ∗
                ((s0.sp - 0xb8#64) ↦₈ w5.extractLsb' 0 8) ∗
                memRegion x.call.out 48 ∗
                idSaveBoxAt x.call.fut x.self x.call.call.addrA x.call.call.keyA 0#8 ∗
                savedCalleeSlots s0 ∗ restErr))) ?_
      rw [hback_97, hback_c8]
      unfold epiloguePre
      ac_rfl
  refine sepWP_conseq (P' :=
      epiloguePre s0 x
        (w5.extractLsb' 8 8) (w5.extractLsb' 16 8) (w5.extractLsb' 24 8)
        (w5.extractLsb' 32 8) (w5.extractLsb' 40 8) (w5.extractLsb' 48 8) (w5.extractLsb' 56 8)
        fnPtr (w5.extractLsb' 0 8) ∗ (memRegion (s0.sp - 0xa0#64) 16 ∗ restErr))
    (Entails.of_eq (by ac_rfl)) ?_
  change SepWP (tripleRatchetProgAtExt img.base ext) _ _ _ _
  refine ispoll_epilogue_1bc (img := img) (ext := ext) x
    (w5.extractLsb' 8 8) (w5.extractLsb' 16 8) (w5.extractLsb' 24 8)
    (w5.extractLsb' 32 8) (w5.extractLsb' 40 8) (w5.extractLsb' 48 8) (w5.extractLsb' 56 8)
    fnPtr (w5.extractLsb' 0 8) (memRegion (s0.sp - 0xa0#64) 16 ∗ restErr)
    (by dsimp only [tripleRatchetProgAtExt]; rw [hentry]; wp_norm_goal) (by wp_norm_lhs) (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [wp_norm, arm64_norm, hvregs])
    (by wp_norm_goal) (by wp_norm_goal) ?_
  intro sf hspf hcsf htrf
  refine ⟨hspf, hcsf, ?_⟩
  have htr_s : sf.trace = s.trace := by simp only [wp_norm, arm64_norm] at htrf; exact htrf
  have hcap_lo :
      BitVec.truncate 32
        (BitVec.zeroExtend 64 (BitVec.truncate 32 cap) &&& 0xFFFFFFFF000000FF#64 |||
          (BitVec.zeroExtend 64 (BitVec.truncate 32 (cap >>> 8)) &&& 16777215#64) <<< 8) =
      cap.extractLsb' 0 32 := by
    ext i hi; interval_cases i <;> simp
  have hcap_hi : BitVec.truncate 32 (cap >>> 32) = cap.extractLsb' 32 32 := by
    ext i hi; interval_cases i <;> simp
  unfold epilogueOut
  conv =>
    lhs; arg 1
    simp only [wp_norm, arm64_norm, hcap_lo, hcap_hi]
  refine Entails.trans (Entails.of_eq (by dsimp only [restErr]; ac_rfl :
    _ = ((x.call.out ↦₆₄ speWord 1) ∗
          ((x.call.out + 8#64) ↦₃₂ cap.extractLsb' 0 32) ∗
          ((x.call.out + 12#64) ↦₃₂ cap.extractLsb' 32 32) ∗
          ((x.call.out + 16#64) ↦₆₄ ptr) ∗
          ((x.call.out + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          ((x.call.out + 32#64) ↦₆₄ fnPtr) ∗
          ((x.call.out + 40#64) ↦₈ w5.extractLsb' 0 8) ∗
          overlap7View2 (x.call.out + 41#64)
            (w5.extractLsb' 8 8) (w5.extractLsb' 16 8) (w5.extractLsb' 24 8)
            (w5.extractLsb' 32 8) (w5.extractLsb' 40 8) (w5.extractLsb' 48 8) (w5.extractLsb' 56 8) ∗
          (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
            if cap = 0#64 then emp
            else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
              memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗
          (fnPtr ↦ᵣ utf8 "read") ∗
          ((s0.sp - 0x90#64) ↦₆₄ speWord 1) ∗
          ((s0.sp - 0x88#64) ↦₆₄ cap) ∗ ((s0.sp - 0x80#64) ↦₆₄ ptr) ∗
          ((s0.sp - 0x78#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          ((s0.sp - 0x70#64) ↦₆₄ fnPtr) ∗
          ((s0.sp - 0x68#64) ↦₆₄ BitVec.ofNat 64 (utf8 "read").length)) ∗
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - saveMinStk getStk putStk) ∗
          stackAt (s0.sp - 0xd0#64) (saveSubMax getStk putStk) ∗
          memRegion (s0.sp - 0xd0#64) 8 ∗
          overlap7View2 (s0.sp - 0xc8#64)
            (w5.extractLsb' 8 8) (w5.extractLsb' 16 8) (w5.extractLsb' 24 8)
            (w5.extractLsb' 32 8) (w5.extractLsb' 40 8) (w5.extractLsb' 48 8) (w5.extractLsb' 56 8) ∗
          ((s0.sp - 0xc1#64) ↦₈ c15) ∗
          ((s0.sp - 0xc0#64) ↦₆₄ fnPtr) ∗
          ((s0.sp - 0xb8#64) ↦₈ w5.extractLsb' 0 8) ∗
          memRegion (s0.sp - 0xb7#64) 7 ∗
          ((s0.sp - 0xb0#64) ↦₆₄ fnPtr) ∗
          ((s0.sp - 0xa8#64) ↦₈ w5.extractLsb' 0 8) ∗
          memRegion (s0.sp - 0xa7#64) 7 ∗
          memRegion (s0.sp - 0xa0#64) 16 ∗
          savedCalleeSlots s0) ∗
        (dirAt A (x.self + 0x28#64) x.peers ∗
          idSaveBoxAt x.call.fut x.self x.call.call.addrA x.call.call.keyA 1#8 ∗
          protocolAddressAt A x.call.call.addr x.call.call.addrA ∗
          (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗
          logOff img ∗ A.pool))) ?_
  refine Entails.trans
    (sepConj_mono_left (epilogueOut_err_reassemble A s0.sp x.call.out bs cap ptr fnPtr)) ?_
  refine Entails.trans
    (Entails.of_eq (by ac_rfl :
      (idSaveOutAt A x.call.out (.error ()) ∗ memRegion (s0.sp - 0x90#64) 48) ∗ _ =
      idSaveOutAt A x.call.out (.error ()) ∗
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - saveMinStk getStk putStk) ∗
          stackAt (s0.sp - 0xd0#64) (saveSubMax getStk putStk) ∗
          memRegion (s0.sp - 0xd0#64) 8 ∗
          overlap7View2 (s0.sp - 0xc8#64)
            (w5.extractLsb' 8 8) (w5.extractLsb' 16 8) (w5.extractLsb' 24 8)
            (w5.extractLsb' 32 8) (w5.extractLsb' 40 8) (w5.extractLsb' 48 8) (w5.extractLsb' 56 8) ∗
          ((s0.sp - 0xc1#64) ↦₈ c15) ∗
          ((s0.sp - 0xc0#64) ↦₆₄ fnPtr) ∗
          ((s0.sp - 0xb8#64) ↦₈ w5.extractLsb' 0 8) ∗
          memRegion (s0.sp - 0xb7#64) 7 ∗
          ((s0.sp - 0xb0#64) ↦₆₄ fnPtr) ∗
          ((s0.sp - 0xa8#64) ↦₈ w5.extractLsb' 0 8) ∗
          memRegion (s0.sp - 0xa7#64) 7 ∗
          memRegion (s0.sp - 0xa0#64) 16 ∗
          memRegion (s0.sp - 0x90#64) 48 ∗
          savedCalleeSlots s0) ∗
        (dirAt A (x.self + 0x28#64) x.peers ∗
          idSaveBoxAt x.call.fut x.self x.call.call.addrA x.call.call.keyA 1#8 ∗
          protocolAddressAt A x.call.call.addr x.call.call.addrA ∗
          (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗
          logOff img ∗ A.pool))) ?_
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_left
      (restore_savePollStack s0 hstk hhi
        (w5.extractLsb' 8 8) (w5.extractLsb' 16 8) (w5.extractLsb' 24 8)
        (w5.extractLsb' 32 8) (w5.extractLsb' 40 8) (w5.extractLsb' 48 8) (w5.extractLsb' 56 8)
        c15 fnPtr (w5.extractLsb' 0 8) fnPtr (w5.extractLsb' 0 8)))) ?_
  simp only [idSavePollSpec, Spec.inImage, sepExists_sepConj_left]
  refine Entails.sepExists_right (Except.error () : Except Unit (List (BitVec 8)))
    (Entails.sepExists_right (Except.error () : Except Unit (Option IdentityKey)) ?_)
  simp only [idSaveOf, idSavePeers, sepConj_assoc]
  refine Entails.pure_right ?_ (Entails.of_eq (by ac_rfl))
  refine ⟨?_, rfl⟩
  exact ⟨herr_case.1.symm, htr_s.trans herr_case.2⟩

/-- `Ok []` branch after `Dir::get` returns at `+68` (`gr = .ok []`). -/
theorem ispoll_branch_ok_nil {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {getStk putStk stk : Nat}
    (hC : AllocContractsX img A ext)
    (hPut : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutStrName)
      (dirPutStrSpec A img putStk))
    (hstk : saveMinStk getStk putStk ≤ stk)
    (hhi : stk ≤ 2 ^ 64)
    {s0 s : State} (x : IdPollGhost)
    (c1 c2 c3 c4 c5 c6 c7 c15 : BitVec 8)
    (s16 : BitVec 64) (s24 : BitVec 8) (s32 : BitVec 64) (s40 : BitVec 8)
    (s48 s56w : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr idSavePollName + offAfterGet)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0xd0#64)
    (hsp_align : s.spAligned = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace)
    (hinv : ImgCallInv img s)
    (hx19 : s.readReg64 .x19 = x.call.fut)
    (hx20 : s.readReg64 .x20 = x.call.out)
    (hx24 : s.readReg64 .x24 = x.self)
    (hx29 : s.readReg64 .x29 = s0.sp - 0x60#64)
    (hnlen : x.call.call.addr.name.bytes.length < 2 ^ 32)
    (hclen : x.peers.changed.length < 2 ^ 32)
    (hgr : Except.ok [] = x.peers.get rd s0.fs.files x.call.call.addr.val.name) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) s
      (getResultAt A (s0.sp - 0x90#64) (.ok []) ∗
        dirAt A (x.self + 0x28#64) x.peers ∗
        memRegion x.call.out 48 ∗
        idSaveBoxAt x.call.fut x.self x.call.call.addrA x.call.call.keyA 0#8 ∗
        protocolAddressAt A x.call.call.addr x.call.call.addrA ∗
        (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗
        logOff img ∗ A.pool ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - saveMinStk getStk putStk) ∗
        stackAt (s0.sp - 0xd0#64) (saveSubMax getStk putStk) ∗
        memRegion (s0.sp - 0xd0#64) 8 ∗
        overlap7View1 (s0.sp - 0xc8#64) c1 c2 c3 c4 c5 c6 c7 ∗
        ((s0.sp - 0xc1#64) ↦₈ c15) ∗
        ((s0.sp - 0xc0#64) ↦₆₄ s16) ∗
        ((s0.sp - 0xb8#64) ↦₈ s24) ∗
        memRegion (s0.sp - 0xb7#64) 7 ∗
        ((s0.sp - 0xb0#64) ↦₆₄ s32) ∗
        ((s0.sp - 0xa8#64) ↦₈ s40) ∗
        memRegion (s0.sp - 0xa7#64) 7 ∗
        ((s0.sp - 0xa0#64) ↦₆₄ s48) ∗
        ((s0.sp - 0x98#64) ↦₆₄ s56w) ∗
        savedCalleeSlots s0)
      (fun sf P_f => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (idSavePollSpec rd pathOk A img stk).post x s0 sf))
      (fun sf P_f => P_f ⊢ (idSavePollSpec rd pathOk A img stk).onPanic x s0 sf) := by
  have hDealloc := ispoll_dealloc_ok_at hC
  have hsub_hi : saveSubMax getStk putStk ≤ 2 ^ 64 := by
    have : saveMinStk getStk putStk ≤ 2 ^ 64 := le_trans hstk hhi
    unfold saveMinStk at this; omega
  have hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) →
      (P_f ⊢ (idSavePollSpec rd pathOk A img stk).onPanic x s0 sf) := by
    intro sf P_f hp
    simp only [idSavePollSpec, Spec.inImage]
    exact Entails.pure_right hp (entails_anyHeap _)
  have hfn : libsignalSessionCode.fnOff idSavePollName =
      num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}") :=
    idSavePoll_fnOff
  code_fetches CryptoVerification.libsignalSessionCode cliIdSavePollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}")) 400
  clear hfn
  dsimp only [tripleRatchetProgAtExt, offAfterGet] at hDealloc hpc ⊢
  generalize_entry hentry :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr idSavePollName = entry
  examples_hide_fetches
  conv =>
    arg 4
    rw [getResultAt_ok_unpack A s0.sp []]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro cap
  apply SepWPp.exists_elim; intro ptr
  refine SepWPp.pure_elim fun ⟨hlen, hcap_lt, hptr⟩ => ?_
  ispoll_rw_pre (s48_split_byte7 s0.sp s48 s56w)
  conv => arg 4; simp only [sepConj_assoc]
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    ispoll_fold_pre (vecU8_free_zero A ptr hlen)
    conv => arg 4; simp only [emp_sepConj, sepConj_assoc]
    apply sepWPp_step_to_frozen hinv (mid := entry + offOkTail)
    dsimp only [offOkTail]
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hF_tail hsym_tail
    ispoll_fold_pre (slot90_words4_collapse s0.sp okTagVec 0#64 ptr (BitVec.ofNat 64 ([] : List (BitVec 8)).length))
    ispoll_fold_pre (s48_byte7_entails_memRegion16 s0.sp s48 (s56w.extractLsb' 0 8)
      (s56w.extractLsb' 8 8) (s56w.extractLsb' 16 8) (s56w.extractLsb' 24 8)
      (s56w.extractLsb' 32 8) (s56w.extractLsb' 40 8) (s56w.extractLsb' 48 8) (s56w.extractLsb' 56 8))
    change SepWPp (tripleRatchetProgAtExt img.base ext) _ _ _ _ _
    refine sepWPp_conseq ?_
      (ispoll_ok_tail_190 (pathOk := pathOk) hC hPut hstk hhi x (.ok []) none .newOrUnchanged
        c1 c2 c3 c4 c5 c6 c7 c15 s16 s24 s48 (s56w.extractLsb' 0 8)
        (by dsimp only [tripleRatchetProgAtExt]; rw [hentry]; wp_norm_goal) (by wp_norm_lhs) (by wp_norm_goal) (by wp_norm_lhs)
        (by simp only [wp_norm, arm64_norm, hvregs])
        (by wp_norm_goal)
        ⟨hF_tail, hsym_tail⟩
        (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
        (by simp only [wp_norm, arm64_norm]; rfl)
        (by wp_norm_goal) rfl hnlen hclen hgr rfl)
    exact Entails.of_eq (by ac_rfl)
  · ispoll_fold_pre (vecU8_free_ne (ptr := ptr) A hcap0 hlen hcap_lt)
    conv => arg 4; simp only [sepConj_assoc]
    apply sepWPp_step_to_frozen hinv (mid := entry +
      bv% (ls_rel%
        "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"
        "__rustc::__rust_dealloc"))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hF_dealloc hsym_dealloc
    conv =>
      arg 4
      rw [stackAt_sub_split (s0.sp - 0xd0#64) (hookStk_le_saveSubMax getStk putStk) hsub_hi]
      simp only [sepConj_assoc]
    refine ispoll_call_dealloc (ret_pc := entry + offAfterDealloc)
      hDealloc ptr cap.toNat ?ispollF
      (by wp_norm_goal) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_goal) (by wp_norm_goal)
      ⟨hF_dealloc, hsym_dealloc⟩
      (by wp_norm_goal) (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm])
      (layoutOk_u8_of_ne_zero hcap0 hcap_lt) hpan
      ?ispollPre ?_
    case ispollPre => ispoll_close_frame
    intro sm1 hpc1 hrun1 hsp1 hcs1 hinv1 htr1
    simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm,
      hsp, htr, hx19, hx20, hx24, hx29, hvregs] at hpc1 hsp1 htr1 hcs1
    rcases hcs1 with ⟨hx19_1, hx20_1, _, _, _, hx24_1, hx25_1, hx26_1, _, _, hx29_1, hvregs_1⟩
    have hsp_al1 : sm1.spAligned = true := by
      simp only [State.spAligned] at hsp_align ⊢
      rwa [hsp1, ← hsp]
    conv => arg 4; simp only [wp_norm, arm64_norm, hsp, hsp1]
    ispoll_rw_pre (stackAt_sub_split (s0.sp - 0xd0#64) (hookStk_le_saveSubMax getStk putStk) hsub_hi).symm
    apply sepWPp_step_to_frozen hinv1 (mid := entry + offOkTail)
    dsimp only [offOkTail]
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hF_tail hsym_tail
    ispoll_fold_pre (slot90_words4_collapse s0.sp okTagVec cap ptr (BitVec.ofNat 64 ([] : List (BitVec 8)).length))
    ispoll_fold_pre (s48_byte7_entails_memRegion16 s0.sp s48 (s56w.extractLsb' 0 8)
      (s56w.extractLsb' 8 8) (s56w.extractLsb' 16 8) (s56w.extractLsb' 24 8)
      (s56w.extractLsb' 32 8) (s56w.extractLsb' 40 8) (s56w.extractLsb' 48 8) (s56w.extractLsb' 56 8))
    change SepWPp (tripleRatchetProgAtExt img.base ext) _ _ _ _ _
    refine sepWPp_conseq ?_
      (ispoll_ok_tail_190 (pathOk := pathOk) hC hPut hstk hhi x (.ok []) none .newOrUnchanged
        c1 c2 c3 c4 c5 c6 c7 c15 s16 s24 s48 (s56w.extractLsb' 0 8)
        (by dsimp only [tripleRatchetProgAtExt]; rw [hentry]; wp_norm_goal) (by wp_norm_lhs) (by wp_norm_goal) (by wp_norm_lhs)
        (by simp only [wp_norm, arm64_norm, hvregs_1])
        (by wp_norm_goal)
        ⟨hF_tail, hsym_tail⟩
        (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
        (by simp only [wp_norm, arm64_norm]; rfl)
        (by wp_norm_goal) rfl hnlen hclen hgr rfl)
    exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SignalSession.Cli.Store.IdSavePoll.Helpers
