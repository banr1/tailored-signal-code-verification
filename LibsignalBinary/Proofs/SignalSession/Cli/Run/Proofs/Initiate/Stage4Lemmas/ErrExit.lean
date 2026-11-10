/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.Pure
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage2
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.ModelBridge
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTraced
import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.Link
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DerivePublicKeyBytes
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.Decode
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.Frames
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommon
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandSegsExt
public meta import Lean -- shake: keep

/-!
# Stage 4 Stack/OOM Helpers and Early `Err` Exit (`+4508 → RET`)

Stack-splitting (`stackAt_fsp_split`), OOM panic discharge (`panic_oom_close`), and the early
`Err(InvalidKeyAgreement)` exit path (`stage4_err_exit`, `+4508 → RET`) freeing `kemCtPtr`
(`1569` B) and `pqspkPtr` (`1568` B) and writing `speWord 10` to `x.ret`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage4Lemmas

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunDrop
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

macro "s4_clean_sp_attrs" : command => `(command|
  attribute [-arm64_norm]
    CryptoVerification.LibsignalTripleRatchet.Expand.sp_sub_496_eq_esp
    CryptoVerification.LibsignalTripleRatchet.Expand.sp_add_neg496_eq_esp
    CryptoVerification.LibsignalTripleRatchet.Expand.esp_add_496_sub_496
    CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
    CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
    CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
    CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
    CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
    CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
    CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688
    CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp)

s4_clean_sp_attrs

@[arm64_norm, wp_norm]
theorem s4_bv_sub_sub (x : BitVec 64) (a b : Nat) (_hab : a + b < 2 ^ 64 := by decide) :
    x - BitVec.ofNat 64 a - BitVec.ofNat 64 b = x - BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

@[arm64_norm, wp_norm]
theorem s4_bv_sub_add_lt (x : BitVec 64) (a b : Nat) (_h : b < a := by decide)
    (_ha : a < 2 ^ 64 := by decide) :
    x - BitVec.ofNat 64 a + BitVec.ofNat 64 b = x - BitVec.ofNat 64 (a - b) :=
  ProofLib.bv_sub_add_lit x a b _h _ha

@[arm64_norm, wp_norm]
theorem s4_bv_sub_add_gt (x : BitVec 64) (a b : Nat) (_h : a < b := by decide)
    (_hb : b < 2 ^ 64 := by decide) :
    x - BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (b - a) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

@[arm64_norm, wp_norm]
theorem s4_bv_add_neg64 (x c : BitVec 64) (_hc : c.msb = true := by decide) :
    x + c = x - (-c) := by
  rw [BitVec.sub_neg]

@[arm64_norm ↓, wp_norm ↓]
theorem s4_sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem s4_sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem s4_readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[arm64_norm ↓, wp_norm ↓]
theorem s4_readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem s4_readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem s4_readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem s4_readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem s4_readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm, local wp_norm] cliInitiateFrame_eq BitVec.toNat_zero
run_cmd Lean.Elab.Command.liftCoreM do
  for attrName in [`arm64_norm, `wp_norm] do
    let some ext ← Lean.Meta.Simp.getSimprocExtension? attrName
      | throwError "unknown simproc extension `{attrName}`"
    for declName in [``BitVec.reduceSub, ``BitVec.reduceNeg] do
      Lean.Meta.Simp.addSimprocAttrCore ext declName .local (post := true)

/-! ## Stack Split and OOM Panic Discharge -/

theorem stackAt_fsp_split {B : RunBudgets} {stk : Nat}
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (fsp : BitVec 64) (K : Nat) (hK : K ≤ 262144) :
    stackAt fsp (stk - cliInitiateFrame) =
      stackAt fsp K ∗
        stackAt (fsp - BitVec.ofNat 64 K) (stk - cliInitiateFrame - K) := by
  have hbase_ge := stk_sub_ge_base hstk
  have h63 := stk_sub_le_63 hstk64
  dsimp only [stackAt]
  have haddr :
      (fsp - BitVec.ofNat 64 K) - BitVec.ofNat 64 (stk - cliInitiateFrame - K) =
        fsp - BitVec.ofNat 64 (stk - cliInitiateFrame) := by
    have hadd :
        BitVec.ofNat 64 K + BitVec.ofNat 64 (stk - cliInitiateFrame - K) =
          BitVec.ofNat 64 (stk - cliInitiateFrame) :=
      bv64_ofNat_add_eq_of_mod (by omega)
    bv_omega
  rw [haddr, ProofLib.memRegion_split'
    (b := fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
    (n := stk - cliInitiateFrame - K) (k := K)
    (b' := fsp - BitVec.ofNat 64 K)
    (by omega) (by rw [← haddr]; bv_omega) (by omega)]
  ac_rfl

theorem allocFailedIn_of_trace_eq' {s0 s sm : State}
    (htr : s.trace = s0.trace) (h : allocFailedIn s sm) :
    allocFailedIn s0 sm := by
  unfold allocFailedIn at h ⊢
  rwa [htr] at h

theorem panic_oom_entails_initOnPanic (A : RustAlloc) (img : Obj.Image) (S : RunSem)
    (x : InitGhost) (stk : Nat) (s0 s sm : State) (F : SepProp) (φ : Prop)
    (htr : s.trace = s0.trace) :
    (⌜allocFailedIn s sm ∧ φ⌝ ∗ anyHeap) ∗ F ⊢
      (initSlotSpec A img S stk).onPanic x s0 sm := by
  dsimp only [initSlotSpec, Spec.inImage]
  rw [sepConj_assoc]
  exact Entails.pure_left fun h =>
    Entails.pure_right (Or.inr (allocFailedIn_of_trace_eq' htr h.1)) (entails_anyHeap _)

theorem panic_oom_only_entails_initOnPanic (A : RustAlloc) (img : Obj.Image) (S : RunSem)
    (x : InitGhost) (stk : Nat) (s0 s sm : State) (F : SepProp)
    (htr : s.trace = s0.trace) :
    (⌜allocFailedIn s sm⌝ ∗ anyHeap) ∗ F ⊢
      (initSlotSpec A img S stk).onPanic x s0 sm := by
  dsimp only [initSlotSpec, Spec.inImage]
  rw [sepConj_assoc]
  exact Entails.pure_left fun h =>
    Entails.pure_right (Or.inr (allocFailedIn_of_trace_eq' htr h)) (entails_anyHeap _)

theorem sepWPp_step_to_frozen {prog : Program} {img : Obj.Image} {ret mid : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hinv : ImgCallInv img s)
    (h : SepWP prog mid s P
      (fun sm Pm => img.FrozenLoaded sm → sm.symtab = img.symtab → SepWPp prog ret sm Pm Q Qp oom)) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨_, hfalse⟩⟩
  · have hfz_m := hinv.1.of_keepsFrozen hsteps.keepsFrozen
    have hsym_m := hsteps.symtab_eq.trans hinv.2
    obtain ⟨sf, hsteps', hout⟩ := hnext hfz_m hsym_m R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hfalse).elim

theorem sepWPp_frame_fold {prog : Program} {ret : BitVec 64} {s : State}
    {A B P Rest : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : A ⊢ B) (heq : P = A ∗ Rest)
    (hw : SepWPp prog ret s (B ∗ Rest) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom :=
  fun R hm hL =>
    hw R (Satisfies.mono (sepConj_mono_left (Entails.trans (Entails.of_eq heq) (sepConj_mono_left h))) hm) hL

theorem sepWPp_call_wpp_split {α : Type} {prog : Program} {entry ret_pc ret : BitVec 64}
    {spec : Spec α} (hcall : subroutine_ok prog entry spec)
    (x : α) {s : State} {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp} {img : Obj.Image}
    (hfz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hsplit : P = T ∗ F)
    (hpreT : T ⊢ spec.pre x s)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked →
      (∃ R', sf.mem ⊨ spec.onPanic x s sf ∗ R') → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp oom)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      wp_close_oom_default) :
    SepWPp prog ret s P Q Qp oom := by
  refine SepWPp.call_wpp_frozen (x := x) (F := F) hcall hfz hsym hpc hrun hsp hlr ?_ hexit hpanic hnext hoom
  intro R hm
  rw [← sepConj_assoc]
  exact Satisfies.mono (sepConj_mono_left (Entails.trans (Entails.of_eq hsplit) (sepConj_mono_left hpreT))) hm

theorem s4_sep_assoc_r (P Q R : SepProp) : (P ∗ Q) ∗ R = P ∗ (Q ∗ R) := by ac_rfl
theorem s4_sep_swap (A B : SepProp) : A ∗ B = B ∗ A := by ac_rfl
theorem s4_sep_pull (B A R : SepProp) : B ∗ (A ∗ R) = A ∗ (B ∗ R) := by ac_rfl
theorem s4_sep_emp_r (P : SepProp) : P ∗ emp = P := sepConj_emp P
theorem s4_sep_congr_l {P P' : SepProp} (Q : SepProp) (h : P = P') : P ∗ Q = P' ∗ Q :=
  congrArg (· ∗ Q) h
theorem s4_sep_congr_r (P : SepProp) {Q Q' : SepProp} (h : Q = Q') : P ∗ Q = P ∗ Q' :=
  congrArg (P ∗ ·) h

section S4FrameTactics
open Lean Elab Tactic Meta

private meta partial def s4SpineFnArgs (e : Expr) : Expr × Array Expr :=
  let rec go (e : Expr) (acc : List Expr) : Expr × Array Expr :=
    match e with
    | .mdata _ b => go b acc
    | .app f a   => go f (a.consumeMData :: acc)
    | _          => (e, acc.toArray)
  go e []

private meta def s4MkSepList : List Expr → Expr
  | [] => mkConst ``Arm64.emp
  | [x] => x
  | x :: xs => mkApp2 (mkConst ``Arm64.sepConj) x (s4MkSepList xs)

private meta def s4AtomsMatch (p a : Expr) : MetaM Bool := do
  let p := p.consumeMData
  let a := a.consumeMData
  if p == a then return true
  if ← withoutModifyingState (withTransparency .instances (isDefEq p a)) then
    return true
  let (pfn, pargs) := s4SpineFnArgs p
  let (afn, aargs) := s4SpineFnArgs a
  if pfn != afn || pargs.size != aargs.size then
    return false
  for i in [0 : pargs.size] do
    let pi := pargs[i]!
    let ai := aargs[i]!
    if pi != ai then
      let ty ← inferType pi
      let ok ← withoutModifyingState do
        if ← withTransparency .instances (isDefEq pi ai) then pure true
        else if ty.consumeMData.isConstOf ``Arm64.SepProp then pure false
        else if !pi.hasFVar && !ai.hasFVar then isDefEq pi ai
        else pure false
      if !ok then return false
  return true

private meta def s4AppendNorm (xs ys : List Expr) : MetaM Expr := do
  if ys.isEmpty then
    return mkApp (mkConst ``s4_sep_emp_r) (s4MkSepList xs)
  match xs with
  | [] => mkEqRefl (s4MkSepList ys)
  | [x] => mkEqRefl (mkApp2 (mkConst ``Arm64.sepConj) x (s4MkSepList ys))
  | x :: rest =>
    let restSep := s4MkSepList rest
    let ySep := s4MkSepList ys
    let rySep := s4MkSepList (rest ++ ys)
    let h_ry ← s4AppendNorm rest ys
    let h1 := mkAppN (mkConst ``s4_sep_assoc_r) #[x, restSep, ySep]
    let h2 := mkAppN (mkConst ``s4_sep_congr_r)
      #[x, mkApp2 (mkConst ``Arm64.sepConj) restSep ySep, rySep, h_ry]
    mkEqTrans h1 h2

private meta partial def s4NormSep (e : Expr) : MetaM (List Expr × Expr) := do
  let (fn, args) := s4SpineFnArgs e
  if fn.constName? == some ``Arm64.sepConj && args.size == 2 then
    let (xs, hx) ← s4NormSep args[0]!
    let (ys, hy) ← s4NormSep args[1]!
    let xSep := s4MkSepList xs
    let ySep := s4MkSepList ys
    let h_l := mkAppN (mkConst ``s4_sep_congr_l) #[args[0]!, xSep, args[1]!, hx]
    let h_r := mkAppN (mkConst ``s4_sep_congr_r) #[xSep, args[1]!, ySep, hy]
    let h_app ← s4AppendNorm xs ys
    return (xs ++ ys, ← mkEqTrans h_l (← mkEqTrans h_r h_app))
  else
    let a := e.consumeMData
    return ([a], ← mkEqRefl a)

private meta def s4ExtractOne (ps : List Expr) (a : Expr) :
    MetaM (Option (Expr × List Expr × Expr)) := do
  match ps with
  | [] => return none
  | [p] =>
    if ← s4AtomsMatch p a then return some (p, [], ← mkEqRefl p)
    else return none
  | p :: rest =>
    if ← s4AtomsMatch p a then
      return some (p, rest, ← mkEqRefl (s4MkSepList (p :: rest)))
    else
      match ← s4ExtractOne rest a with
      | none => return none
      | some (m, rem', h_sub) =>
        let restSep := s4MkSepList rest
        let mRemSep := s4MkSepList (m :: rem')
        let h1 := mkAppN (mkConst ``s4_sep_congr_r) #[p, restSep, mRemSep, h_sub]
        match rem' with
        | [] =>
          let h2 := mkAppN (mkConst ``s4_sep_swap) #[p, m]
          return some (m, [p], ← mkEqTrans h1 h2)
        | _ :: _ =>
          let remSep := s4MkSepList rem'
          let h2 := mkAppN (mkConst ``s4_sep_pull) #[p, m, remSep]
          return some (m, p :: rem', ← mkEqTrans h1 h2)

private meta def s4ExtractMany (pExpr : Expr) (ps : List Expr) :
    List Expr → MetaM (List Expr × List Expr × Expr)
  | [] => do return ([], ps, ← mkEqRefl (s4MkSepList ps))
  | a :: tailAtoms => do
    let some (m, rem1, h1) ← s4ExtractOne ps a
      | throwError "s4_frame: atom not found in precondition:\n  {a}\npre:\n  {pExpr}"
    let (ms, remFinal, h2) ← s4ExtractMany pExpr rem1 tailAtoms
    if rem1.isEmpty then
      return ([m], [], h1)
    else
      let h_step := mkAppN (mkConst ``s4_sep_congr_r)
        #[m, s4MkSepList rem1, s4MkSepList (ms ++ remFinal), h2]
      return (m :: ms, remFinal, ← mkEqTrans h1 h_step)

private meta def s4MkSplitEqProof (pExpr aExpr : Expr) : TacticM (Expr × Expr) := do
  let (ps, hpNorm) ← s4NormSep pExpr
  let (aAtoms, haNorm) ← s4NormSep aExpr
  let (matched, rem, hPerm) ← s4ExtractMany pExpr ps aAtoms
  let restExpr := s4MkSepList rem
  let aSep := s4MkSepList aAtoms
  let hApp ← s4AppendNorm matched rem
  let g1 ← mkEqTrans hpNorm (← mkEqTrans hPerm (← mkEqSymm hApp))
  let g2 := mkAppN (mkConst ``s4_sep_congr_l) #[aSep, aExpr, restExpr, ← mkEqSymm haNorm]
  let heq ← mkEqTrans g1 g2
  return (restExpr, heq)

private meta def s4SilentTac (tac : TacticM Unit) : TacticM Unit := do
  let saved ← saveState
  let logBefore ← Core.getMessageLog
  try
    tac
    if (← Core.getMessageLog).toList.length > logBefore.toList.length then
      saved.restore (restoreInfo := true)
      Core.setMessageLog logBefore
  catch _ =>
    saved.restore (restoreInfo := true)
    Core.setMessageLog logBefore

private meta def s4SimpLhs : TacticM Unit := do
  let hasFsp := (← getLCtx).findFromUserName? `fsp |>.isSome
  if hasFsp then
    let fspId : Ident := mkIdent `fsp
    s4SilentTac <| evalTactic (← `(tactic| (conv => lhs; simp only [$fspId:ident, wp_norm, arm64_norm, BitVec.sub_sub, BitVec.add_assoc, BitVec.reduceAdd])))
  else
    s4SilentTac <| evalTactic (← `(tactic| (conv => lhs; simp only [wp_norm, arm64_norm, BitVec.sub_sub, BitVec.add_assoc, BitVec.reduceAdd])))

private meta def s4SimpRhs : TacticM Unit := do
  let hasFsp := (← getLCtx).findFromUserName? `fsp |>.isSome
  if hasFsp then
    let fspId : Ident := mkIdent `fsp
    s4SilentTac <| evalTactic (← `(tactic| (conv => rhs; simp only [$fspId:ident, wp_norm, arm64_norm, BitVec.sub_sub, BitVec.add_assoc, BitVec.reduceAdd])))
  else
    s4SilentTac <| evalTactic (← `(tactic| (conv => rhs; simp only [wp_norm, arm64_norm, BitVec.sub_sub, BitVec.add_assoc, BitVec.reduceAdd])))

private meta def s4SimpRhsArg1 : TacticM Unit := do
  let hasFsp := (← getLCtx).findFromUserName? `fsp |>.isSome
  if hasFsp then
    let fspId : Ident := mkIdent `fsp
    s4SilentTac <| evalTactic (← `(tactic| (conv => rhs; arg 1; simp only [$fspId:ident, wp_norm, arm64_norm, BitVec.sub_sub, BitVec.add_assoc, BitVec.reduceAdd])))
  else
    s4SilentTac <| evalTactic (← `(tactic| (conv => rhs; arg 1; simp only [wp_norm, arm64_norm, BitVec.sub_sub, BitVec.add_assoc, BitVec.reduceAdd])))

elab "s4_ac_rfl" : tactic => do
  s4SimpLhs
  if (← getUnsolvedGoals).isEmpty then return
  s4SimpRhs
  if (← getUnsolvedGoals).isEmpty then return
  withMainContext do
    let g ← getMainGoal
    let gty ← instantiateMVars (← g.getType)
    let (efn, eargs) := s4SpineFnArgs gty
    if efn.constName? != some ``Eq || eargs.size != 3 then
      throwError "s4_ac_rfl expected equality goal, got: {gty}"
    let lhs := eargs[1]!
    let rhs := eargs[2]!
    let (rem, heq) ← s4MkSplitEqProof lhs rhs
    if !rem.isConstOf ``Arm64.emp then
      throwError "s4_ac_rfl: leftover atoms on LHS:\n  {rem}"
    let hEmp := mkApp (mkConst ``s4_sep_emp_r) rhs
    g.assign (← mkEqTrans heq hEmp)
    let gs ← getGoals
    setGoals (gs.filter (· != g))

elab "s4_split_frame" : tactic => do
  s4SimpLhs
  if (← getUnsolvedGoals).isEmpty then return
  s4SimpRhsArg1
  if (← getUnsolvedGoals).isEmpty then return
  withMainContext do
    let g ← getMainGoal
    let gty ← instantiateMVars (← g.getType)
    let (efn, eargs) := s4SpineFnArgs gty
    if efn.constName? != some ``Eq || eargs.size != 3 then
      throwError "s4_split_frame expected equality goal, got: {gty}"
    let lhs := eargs[1]!
    let rhs := eargs[2]!
    let (_, rargs) := s4SpineFnArgs rhs
    let calleePre := rargs[0]!
    let fMVar := rargs[1]!
    let (restExpr, heqExpr) ← s4MkSplitEqProof lhs calleePre
    fMVar.mvarId!.assign restExpr
    g.assign heqExpr
    let gs ← getGoals
    setGoals (gs.filter fun m => m != g && m != fMVar.mvarId!)

macro "s4_fold_pre " h:term : tactic =>
  `(tactic| refine sepWPp_frame_fold $h (by s4_split_frame) ?_)

macro "s4_rw_pre " h:term : tactic =>
  `(tactic| refine sepWPp_frame_fold (Entails.of_eq $h) (by s4_split_frame) ?_)

theorem s4_entails_fold {A B P Q Rest : SepProp}
    (h : A ⊢ B) (heq : P = A ∗ Rest) (hnext : B ∗ Rest ⊢ Q) :
    P ⊢ Q :=
  Entails.trans (Entails.of_eq heq) (Entails.trans (sepConj_mono_left h) hnext)

macro "s4_fold_ent " h:term : tactic =>
  `(tactic| refine s4_entails_fold $h (by s4_split_frame) ?_)

macro "s4_rw_ent " h:term : tactic =>
  `(tactic| refine s4_entails_fold (Entails.of_eq $h) (by s4_split_frame) ?_)

end S4FrameTactics

/-! ## Cell and Error Sret Helpers -/

@[simp, arm64_norm, wp_norm]
theorem cond_eq_adds_neg1_1 :
    ConditionHolds CondCode.EQ (addsPState64 0xffffffffffffffff#64 1#64) = true := by
  simp only [ConditionHolds, addsPState64, AddWithCarry64]
  decide

@[simp, arm64_norm, wp_norm]
theorem cond_ne_adds_speWord10_3 :
    ConditionHolds CondCode.NE (addsPState64 (speWord 10) 3#64) = true := by
  simp only [ConditionHolds, addsPState64, AddWithCarry64, speWord]
  decide

theorem cells5_eq_memRegion40 (a : BitVec 64) :
    memRegion a 40 =
      ∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64, ∃∗ u4 : BitVec 64,
        (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) ∗
          ((a + 24#64) ↦₆₄ u3) ∗ ((a + 32#64) ↦₆₄ u4) := by
  rw [memRegion_split a 8 32 (by decide),
    memRegion_split (a + 8#64) 8 24 (by decide),
    memRegion_split (a + 8#64 + 8#64) 8 16 (by decide),
    memRegion_split (a + 8#64 + 8#64 + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  s4_exists_eq

theorem cells6_eq_memRegion48 (a : BitVec 64) :
    memRegion a 48 =
      ∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
      ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64,
        (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) ∗
          ((a + 24#64) ↦₆₄ u3) ∗ ((a + 32#64) ↦₆₄ u4) ∗ ((a + 40#64) ↦₆₄ u5) := by
  rw [memRegion_split a 8 40 (by decide), ProofLib.memRegion_eight, cells5_eq_memRegion40 (a + 8#64)]
  s4_exists_eq

theorem cells6_entails_memRegion48 (a : BitVec 64)
    (v0 v1 v2 v3 v4 v5 : BitVec 64) :
    (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗
      ((a + 24#64) ↦₆₄ v3) ∗ ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5) ⊢
      memRegion a 48 := by
  rw [cells6_eq_memRegion48 a]
  exact Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2
    (Entails.sepExists_right v3 (Entails.sepExists_right v4 (Entails.sepExists_right v5
      (Entails.refl _))))))

theorem speWord10_cells5_entails_initResAt (A : RustAlloc) (a : BitVec 64)
    (v1 v2 v3 v4 v5 : BitVec 64) :
    (a ↦₆₄ speWord 10) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗
      ((a + 24#64) ↦₆₄ v3) ∗ ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5) ⊢
      initResAt A a (.error (.protocol .invalidKeyAgreement)) := by
  dsimp only [initResAt]
  refine Entails.trans ?_
    (Entails.sepExists_right (.plain 10 (by decide))
      (Entails.refl (speOwnedAt A a (.plain 10 (by decide)))))
  dsimp only [speOwnedAt]
  rw [cells5_eq_memRegion40 (a + 8#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (Entails.refl _)
    (Entails.sepExists_right v1 (Entails.sepExists_right v2
      (Entails.sepExists_right v3 (Entails.sepExists_right v4
        (Entails.sepExists_right v5 (Entails.refl _))))))

/-! ## Error Cleanup Spatial Bundle and Proof (`+4508 → RET`) -/

def errExitMem (A : RustAlloc) (img : Obj.Image) (x : InitGhost)
    (kp : IdentityKeyPair)
    (ekASk ekAPk : List (BitVec 8))
    (pqspkPtr kemCtPtr w70 w78 : BitVec 64) (opkId : BitVec 32)
    (Rest5ba Leak : SepProp) (stk : Nat) (s0 : State) : SepProp :=
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  storesAt A x.stores StoresGhost.opened ∗
    protocolAddressAt A x.peer x.peerA ∗
    protocolAddressAt A x.me x.meA ∗
    cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
    (s0.sp ↦₃₂ 0#32) ∗
    memRegion x.ret 48 ∗
    logOff img ∗
    A.pool ∗
    initSaved s0 ∗
    memRegion fsp 0x60 ∗
    ((fsp + 0x60#64) ↦₆₄ kemCtPtr) ∗ ((fsp + 0x68#64) ↦₆₄ 1569#64) ∗
    A.live kemCtPtr 1569 1 ∗ memRegion kemCtPtr 1569 ∗
    ((fsp + 0x70#64) ↦₆₄ w70) ∗ ((fsp + 0x78#64) ↦₆₄ w78) ∗
    memRegion (fsp + 0x80#64) 0x50 ∗
    initArgsAt img fsp x s0 ∗
    initFreshRecAt fsp ∗
    memRegion (fsp + 0x148#64) 0x150 ∗
    stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
    memRegion (fsp + 0x460#64) 0x158 ∗
    ((fsp + 0x5b8#64) ↦₈ 0#8) ∗
    ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
    Rest5ba ∗
    ((fsp + 5640#64) ↦₆₄ speWord 10) ∗
    memRegion (fsp + 5648#64) 40 ∗
    Leak ∗
    stackAt fsp (stk - cliInitiateFrame)

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1600000 in
theorem stage4_err_exit_ext
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)} {S : RunSem}
    {B : RunBudgets}
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    {x : InitGhost} {s0 : State} (hspk : stk ≤ s0.sp.toNat)
    {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)}
    {pqspkPtr kemCtPtr w70 w78 : BitVec 64} {opkId : BitVec 32}
    {Rest5ba Leak : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hAlloc : AllocContractsX img A (cliExternsWith ext))
    (hTrace : CryptoVerification.LibsignalPublicApi.StoreKit.TraceFsSound (s4ProgExt img ext))
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    {s : State}
    (hctrl : S4InInitiate img ext s0 s 4508)
    (htr : s.trace = s0.trace)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hekA : ekAPk.length = 32)
    (hekASk : ekASk.length = 32)
    (hkpkLen : x.bundle.kpk.length = 1568)
    (_hpqspkNonNull : pqspkPtr ≠ 0#64)
    (_hkemNonNull : kemCtPtr ≠ 0#64)
    (herr : S.initiate x.F x.peer.val x.me.val x.bundle x.coins = some none)
    (hRest : Rest5ba ∗ memRegion ((s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 5640#64) 48 ⊢
      memRegion ((s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x5ba#64) (initLocalsSize - 0x5ba)) :
    SepWPp (s4ProgExt img ext) (s0.readReg64 .lr) s
      (errExitMem A img x kp ekASk ekAPk pqspkPtr kemCtPtr w70 w78 opkId Rest5ba Leak stk s0)
      Q Qp (initOom s0) := by
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  have hfsp_eq : s0.sp - BitVec.ofNat 64 cliInitiateFrame = fsp := rfl
  have hsaved_fsp : s0.sp - 0x60#64 = fsp + 7312#64 := by
    dsimp only [fsp, cliInitiateFrame]; bv_omega
  have hs0_sp_fsp : s0.sp = fsp + 7408#64 := by
    dsimp only [fsp, cliInitiateFrame]; bv_omega
  stage4_epilogue_fetches img.base (cliExternsWith ext)
  stage4_pre_fetches img.base (cliExternsWith ext)
  stage4_spqr_fetches img.base (cliExternsWith ext)
  stage4_post_fetches img.base (cliExternsWith ext)
  stage4_cleanup_fetches img.base (cliExternsWith ext)
  stage4_bind_entry img.base (cliExternsWith ext)
  examples_hide_fetches
  have hfsp_align : ∀ (st : State), st.sp = fsp → st.spAligned = true :=
    fun st hst => fsp_aligned_of_s0 hstk hspk hst hctrl.spAligned
  have hdealloc := dealloc_ok_at_init_ext hAlloc
  have hfn_entry : s4EntryExt img ext = fnStart := fnStart_def
  have hpc_start : s.pc = fnStart + bv% (4508) := by
    rw [hctrl.pc, s4PcExt, hfn_entry]
  have hrun_start : s.status = .Running := hctrl.run
  have hsp_start : s.sp = fsp := hctrl.sp
  have halign_start : s.spAligned = true := hfsp_align s hsp_start
  have hx19_start : s.readReg64 (.gpr 19#5) = x.ret := hctrl.x19.trans hx8
  have hvregs_start : calleeSavedVRegs s = calleeSavedVRegs s0 := hctrl.vregs
  apply sepWPp_steps_post (post := fun sf Pf =>
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace ∧
      (Pf ⊢ storesAt A x.stores StoresGhost.opened ∗
        initResAt A x.ret (.error (.protocol .invalidKeyAgreement)) ∗
        protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
        cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        (s0.sp ↦₃₂ 0#32) ∗ logOff img ∗ A.pool ∗ stackAt s0.sp stk ∗ anyHeap))
  ·
    unfold errExitMem
    conv => arg 4; dsimp only
    rw [hfsp_eq,
      cells5_eq_memRegion40 (fsp + 5648#64),
      stackAt_fsp_split hstk hstk64 fsp extHookStack (by decide)]
    s4_elim_exists e0; s4_elim_exists e1; s4_elim_exists e2
    s4_elim_exists e3; s4_elim_exists e4
    conv => arg 4; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    apply sepWPp_step_to_frozen hctrl.inv
      (mid := fnStart + bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_dealloc"))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hs1_F hs1_sym
    have h48 := cells6_entails_memRegion48 (fsp + 5640#64) (speWord 10) e0 e1 e2 e3 e4
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h48
    have h5ba : (Rest5ba ∗ (((fsp + 5640#64) ↦₆₄ speWord 10) ∗
        ((fsp + 5648#64) ↦₆₄ e0) ∗ ((fsp + 5656#64) ↦₆₄ e1) ∗
        ((fsp + 5664#64) ↦₆₄ e2) ∗ ((fsp + 5672#64) ↦₆₄ e3) ∗
        ((fsp + 5680#64) ↦₆₄ e4))) ⊢
        memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) :=
      Entails.trans (sepConj_mono (Entails.refl _) h48) hRest
    s4_fold_pre h5ba
    refine sepWPp_call_wpp_split hdealloc (kemCtPtr, 1569, 1)
      (T := A.pool ∗ A.live kemCtPtr 1569 1 ∗ memRegion kemCtPtr 1569 ∗ stackAt fsp extHookStack)
      (F := ?_)
      hs1_F hs1_sym
      (by rw [s4PcExt, hfn_entry]; try wp_norm_goal) (by wp_norm_lhs) (hfsp_align _ (by wp_norm_goal)) rfl
      (by s4_split_frame)
      ?_
      (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
      (fun _ _ ⟨_, hm⟩ => (not_satisfies_false_sepConj hm).elim) ?_
    · dsimp only [Spec.inImage, rustDeallocExternSpecWithStack]
      have hs1_sp_eq := frozen_sp_eq hs1_F fsp (by wp_norm_goal)
      rw [hs1_sp_eq]
      exact Entails.pure_right ⟨hs1_F, hs1_sym⟩
        (Entails.pure_right ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, ⟨by decide, ⟨0, rfl⟩, by decide⟩⟩
          (Entails.of_eq (by s4_ac_rfl)))
    intro s2 hs2_pc hs2_run hs2_sp hs2_cs hs2_F hs2_sym
    dsimp only [Spec.inImage, rustDeallocExternSpecWithStack]
    have hs1_sp_eq := frozen_sp_eq hs1_F fsp (by wp_norm_goal)
    rw [hs1_sp_eq]
    s4_pure_elim
    intro hs2_tr_eq
    have hs2_tr : s2.trace = s0.trace := hs2_tr_eq.trans (by wp_norm_goal)
    have hs2_sp' : s2.sp = fsp := hs2_sp.trans hs1_sp_eq
    have hs2_align : s2.spAligned = true := hfsp_align s2 hs2_sp'
    have hs2_x19 : s2.readReg64 (.gpr 19#5) = x.ret :=
      (hs2_cs.gpr ⟨19, by decide⟩).trans (by wp_norm_goal)
    have hs2_x26 : s2.readReg64 (.gpr 26#5) = speWord 10 :=
      (hs2_cs.gpr ⟨26, by decide⟩).trans (by wp_norm_goal)
    have hs2_x27 : s2.readReg64 (.gpr 27#5) = e0 :=
      (hs2_cs.gpr ⟨27, by decide⟩).trans (by wp_norm_goal)
    have hs2_x25 : s2.readReg64 (.gpr 25#5) = e1 :=
      (hs2_cs.gpr ⟨25, by decide⟩).trans (by wp_norm_goal)
    have hs2_x28 : s2.readReg64 (.gpr 28#5) = e2 :=
      (hs2_cs.gpr ⟨28, by decide⟩).trans (by wp_norm_goal)
    have hs2_x24 : s2.readReg64 (.gpr 24#5) = e3 :=
      (hs2_cs.gpr ⟨24, by decide⟩).trans (by wp_norm_goal)
    have hs2_x21 : s2.readReg64 (.gpr 21#5) = e4 :=
      (hs2_cs.gpr ⟨21, by decide⟩).trans (by wp_norm_goal)
    have hs2_vr : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hs2_cs.vregs.trans hvregs_start
    have hs2_pc' : s2.pc = fnStart + bv% (4828) := by
      rw [hs2_pc]; wp_norm_goal
    unfold stage3KeySlotsAt
    conv => arg 4; dsimp only
    rw [hfsp_eq]
    conv => arg 4; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    have hkpk_mem : (pqspkPtr ↦ₛ x.bundle.kpk) ⊢ memRegion pqspkPtr 1568 :=
      hkpkLen ▸ pointsToBytes_entails_memRegion pqspkPtr x.bundle.kpk
    s4_fold_pre hkpk_mem
    apply sepWPp_step_to_frozen ⟨hs2_F, hs2_sym⟩
      (mid := fnStart + bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_dealloc"))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hs3_F hs3_sym
    refine sepWPp_call_wpp_split hdealloc (pqspkPtr, 1568, 1)
      (T := A.pool ∗ A.live pqspkPtr 1568 1 ∗ memRegion pqspkPtr 1568 ∗ stackAt fsp extHookStack)
      (F := ?_)
      hs3_F hs3_sym
      (by rw [s4PcExt, hfn_entry]; try wp_norm_goal) (by wp_norm_lhs) (hfsp_align _ (by wp_norm_goal)) rfl
      (by s4_split_frame)
      ?_
      (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
      (fun _ _ ⟨_, hm⟩ => (not_satisfies_false_sepConj hm).elim) ?_
    · dsimp only [Spec.inImage, rustDeallocExternSpecWithStack]
      have hs3_sp_eq := frozen_sp_eq hs3_F fsp (by wp_norm_goal)
      rw [hs3_sp_eq]
      exact Entails.pure_right ⟨hs3_F, hs3_sym⟩
        (Entails.pure_right ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, ⟨by decide, ⟨0, rfl⟩, by decide⟩⟩
          (Entails.of_eq (by s4_ac_rfl)))
    intro s4 hs4_pc hs4_run hs4_sp hs4_cs _hs4_F _hs4_sym
    dsimp only [Spec.inImage, rustDeallocExternSpecWithStack]
    have hs3_sp_eq := frozen_sp_eq hs3_F fsp (by wp_norm_goal)
    rw [hs3_sp_eq]
    s4_pure_elim
    intro hs4_tr_eq
    have hs4_tr : s4.trace = s0.trace := hs4_tr_eq.trans (by wp_norm_goal)
    have hs4_sp' : s4.sp = fsp := hs4_sp.trans hs3_sp_eq
    have hs4_align : s4.spAligned = true := hfsp_align s4 hs4_sp'
    have hs4_x19 : s4.readReg64 (.gpr 19#5) = x.ret :=
      (hs4_cs.gpr ⟨19, by decide⟩).trans (by wp_norm_goal)
    have hs4_x26 : s4.readReg64 (.gpr 26#5) = speWord 10 :=
      (hs4_cs.gpr ⟨26, by decide⟩).trans (by wp_norm_goal)
    have hs4_x27 : s4.readReg64 (.gpr 27#5) = e0 :=
      (hs4_cs.gpr ⟨27, by decide⟩).trans (by wp_norm_goal)
    have hs4_x25 : s4.readReg64 (.gpr 25#5) = e1 :=
      (hs4_cs.gpr ⟨25, by decide⟩).trans (by wp_norm_goal)
    have hs4_x28 : s4.readReg64 (.gpr 28#5) = e2 :=
      (hs4_cs.gpr ⟨28, by decide⟩).trans (by wp_norm_goal)
    have hs4_x24 : s4.readReg64 (.gpr 24#5) = e3 :=
      (hs4_cs.gpr ⟨24, by decide⟩).trans (by wp_norm_goal)
    have hs2_x21_4 : s4.readReg64 (.gpr 21#5) = e4 :=
      (hs4_cs.gpr ⟨21, by decide⟩).trans (by wp_norm_goal)
    have hs4_vr : calleeSavedVRegs s4 = calleeSavedVRegs s0 := hs4_cs.vregs.trans hs2_vr
    have hs4_pc' : s4.pc = fnStart + bv% (5500) := by
      rw [hs4_pc]; wp_norm_goal
    rw [cells6_eq_memRegion48 x.ret]
    unfold initFreshRecAt initSaved
    conv => arg 4; dsimp only
    rw [hsaved_fsp]
    s4_elim_exists r0; s4_elim_exists r1; s4_elim_exists r2
    s4_elim_exists r3; s4_elim_exists r4; s4_elim_exists r5
    conv => arg 4; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    have hcond1 := cond_eq_adds_neg1_1
    have hcond2 := cond_ne_adds_speWord10_3
    apply SepWPp.of_sepWP_ret
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by rw [hs0_sp_fsp]; wp_norm_goal, ?_, by wp_norm_goal, ?_⟩
    · exact ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by simp only [calleeSavedVRegs, arm64_norm]; exact hs4_vr⟩
    · have hspe := speWord10_cells5_entails_initResAt A x.ret e0 e1 e2 e3 e4
      have hany : Leak ⊢ anyHeap := entails_anyHeap _
      have hd0 := stage4Prefix_0xd0_merge fsp kemCtPtr w70 w78
      have hsaved_mem := initSaved_entails_memRegion s0
      have hstk_back := (stackAt_fsp_split hstk hstk64 fsp extHookStack (by decide)).symm
      have hstk_full := stage4FrameRegions_entails_stackAt hstk hstk64 img x kp ekASk ekAPk
        pqspkPtr opkId 0#8 0#8 s0 hekA hekASk
      have heq_saved :
          ((fsp + 7312#64) ↦₆₄ s0.readReg64 .fp) ∗
          ((fsp + 7320#64) ↦₆₄ s0.readReg64 .lr) ∗
          ((fsp + 7328#64) ↦₆₄ s0.readReg64 (.gpr 28#5)) ∗
          ((fsp + 7336#64) ↦₆₄ s0.readReg64 (.gpr 27#5)) ∗
          ((fsp + 7344#64) ↦₆₄ s0.readReg64 (.gpr 26#5)) ∗
          ((fsp + 7352#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
          ((fsp + 7360#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗
          ((fsp + 7368#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
          ((fsp + 7376#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
          ((fsp + 7384#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
          ((fsp + 7392#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
          ((fsp + 7400#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) =
            initSaved s0 := by
        unfold initSaved
        dsimp only
        rw [hsaved_fsp]
        simp only [BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd]
      have heq_fresh :
          ((fsp + 0x128#64) ↦₆₄ 0#64) ∗
          ((fsp + 0x130#64) ↦₆₄ 8#64) ∗
          ((fsp + 0x138#64) ↦₆₄ 0#64) ∗
          ((fsp + 0x140#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) =
            initFreshRecAt fsp := rfl
      s4_fold_ent hspe
      s4_fold_ent hany
      s4_fold_ent hd0
      s4_rw_ent heq_saved
      s4_fold_ent hsaved_mem
      s4_rw_ent heq_fresh
      s4_rw_ent hstk_back
      s4_fold_ent hstk_full
      exact Entails.of_eq (by s4_ac_rfl)
  ·
    intro sf Pf hsteps ⟨hsp, hcs, htr_sf, hent⟩
    apply hpost
    refine ⟨hsp, hcs, ?_⟩
    have hfiles_sf : sf.fs.files = s0.fs.files :=
      (files_eq_of_steps_trace_eq hTrace hsteps
        (htr_sf.trans htr.symm)).trans hctrl.files0
    have hslotTr : slotTrace s0 sf :=
      ⟨by rw [htr_sf], hfiles_sf, by rw [htr_sf]⟩
    have hslotOut : slotOut (S.initiate x.F x.peer.val x.me.val x.bundle x.coins)
        StoresGhost.opened (.error (.protocol .invalidKeyAgreement)) s0 sf :=
      ⟨by decide, by decide, herr⟩
    dsimp only [initSlotSpec, Spec.inImage]
    exact Entails.trans hent
      (Entails.sepExists_right StoresGhost.opened
        (Entails.sepExists_right (.error (.protocol .invalidKeyAgreement))
          (Entails.pure_right ⟨hslotTr, hslotOut⟩ (Entails.refl _))))

theorem stage4_err_exit
    {img : Obj.Image} {A : RustAlloc} {W : CliHooks} {S : RunSem}
    {B : RunBudgets}
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    {x : InitGhost} {s0 : State} (hspk : stk ≤ s0.sp.toNat)
    {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)}
    {pqspkPtr kemCtPtr w70 w78 : BitVec 64} {opkId : BitVec 32}
    {Rest5ba Leak : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooks img A (cliExterns W))
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    {s : State}
    (hctrl : InInitiate img W s0 s 4508)
    (htr : s.trace = s0.trace)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hekA : ekAPk.length = 32)
    (hekASk : ekASk.length = 32)
    (hkpkLen : x.bundle.kpk.length = 1568)
    (hpqspkNonNull : pqspkPtr ≠ 0#64)
    (hkemNonNull : kemCtPtr ≠ 0#64)
    (herr : S.initiate x.F x.peer.val x.me.val x.bundle x.coins = some none)
    (hRest : Rest5ba ∗ memRegion ((s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 5640#64) 48 ⊢
      memRegion ((s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x5ba#64) (initLocalsSize - 0x5ba)) :
    SepWPp (initProg img W) (s0.readReg64 .lr) s
      (errExitMem A img x kp ekASk ekAPk pqspkPtr kemCtPtr w70 w78 opkId Rest5ba Leak stk s0)
      Q Qp (initOom s0) :=
  stage4_err_exit_ext hstk hstk64 hspk hh.alloc (initProg_traceFsSound img W) hpost
    ⟨hctrl.pc, hctrl.run, hctrl.sp, hctrl.fp, hctrl.x19, hctrl.files0,
      hctrl.inv, hctrl.vregs, hctrl.spAligned⟩
    htr hx8 hekA hekASk hkpkLen hpqspkNonNull hkemNonNull herr hRest

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage4Lemmas
