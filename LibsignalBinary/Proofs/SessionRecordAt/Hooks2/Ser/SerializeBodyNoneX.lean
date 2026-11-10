/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersX
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Helpers
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Fetch
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `SessionRecord::serialize` (`0x1857c`): `None` Branch

Verifies `SessionRecord::serialize` (`0x1857c`, Block `52`) on a `SessionRecord` with no current
session (`serializeNoneSpecX A`) on `SP2Ext` and under relocatable `[LibsignalPlacement]`, and
defines the `wppin_*` / `wpplscl_*` weakest-precondition entry and call tactics.
-/

namespace CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.E2E.Record.Serialization
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux
open Proofs.libsignal.Hooks2

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

theorem L1_SerializeBodyNoneX : True := trivial

/-! ## `None`-branch specification -/

/-- `serialize` on a record with no current session (`serializeNoneSpec` at `serializeStackX`). -/
def serializeNoneSpecX (A : RustAlloc) : Spec (BitVec 64 × BitVec 64 × BitVec 64) where
  pre := fun (self, out, prevPtr) s =>
    ⌜s.readReg64 .x0 = self ∧ s.readReg64 .x8 = out⌝ ∗
      ((self + 8#64) ↦₆₄ prevPtr) ∗ ((self + 16#64) ↦₆₄ 0#64) ∗
      ((self + 24#64) ↦₆₄ noneCap) ∗
      memRegion out 32 ∗ stackAt s.sp serializeStackX
  post := fun (self, out, prevPtr) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ((self + 8#64) ↦₆₄ prevPtr) ∗ ((self + 16#64) ↦₆₄ 0#64) ∗
      ((self + 24#64) ↦₆₄ noneCap) ∗
      (out ↦₆₄ okTagVec) ∗ vecU8 A (out + 8#64) [] ∗
      stackAt s0.sp serializeStackX

/-! ## Pure and separation-logic helpers -/

theorem memRegion_out32_cellsX (out : BitVec 64) :
    memRegion out 32 =
      (∃∗ out3 : BitVec 64, ∃∗ out2 : BitVec 64, ∃∗ out1 : BitVec 64, ∃∗ out0 : BitVec 64,
        (out ↦₆₄ out0) ∗ ((out + 8#64) ↦₆₄ out1) ∗
        ((out + 16#64) ↦₆₄ out2) ∗ ((out + 24#64) ↦₆₄ out3)) := by
  rw [memRegion_split out 8 24 (by decide),
    memRegion_split (out + 8#64) 8 16 (by decide),
    memRegion_split (out + 8#64 + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight out,
    ProofLib.memRegion_eight (out + 8#64),
    ProofLib.memRegion_eight (out + 8#64 + 8#64),
    ProofLib.memRegion_eight (out + 8#64 + 8#64 + 8#64)]
  have h16 : out + 8#64 + 8#64 = out + 16#64 := by rw [BitVec.add_assoc]; rfl
  have h24 : out + 16#64 + 8#64 = out + 24#64 := by rw [BitVec.add_assoc]; rfl
  rw [h16, h24]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

theorem memRegion_out32_stack_noneX (out sp : BitVec 64) :
    memRegion out 32 ∗ stackAt sp serializeStackX =
      (∃∗ out3 : BitVec 64, ∃∗ out2 : BitVec 64, ∃∗ out1 : BitVec 64, ∃∗ out0 : BitVec 64,
        (out ↦₆₄ out0) ∗ ((out + 8#64) ↦₆₄ out1) ∗
        ((out + 16#64) ↦₆₄ out2) ∗ ((out + 24#64) ↦₆₄ out3)) ∗
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
       ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
       ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64,
       ∃∗ bs336 : List (BitVec 8),
       ∃∗ w_none : BitVec 64,
        ⌜bs336.length = 336⌝ ∗
        stackAt (sp - 800#64) serializeSubStackX ∗
        memRegion (sp - 800#64) 24 ∗
        ((sp - 776#64) ↦₆₄ w_none) ∗
        memRegion (sp - 768#64) 336 ∗
        ((sp - 432#64) ↦ₛ bs336) ∗
        ((sp - 96#64) ↦₆₄ c0) ∗ ((sp - 88#64) ↦₆₄ c1) ∗
        ((sp - 80#64) ↦₆₄ c2) ∗ ((sp - 72#64) ↦₆₄ c3) ∗
        ((sp - 64#64) ↦₆₄ c4) ∗ ((sp - 56#64) ↦₆₄ c5) ∗
        ((sp - 48#64) ↦₆₄ c6) ∗ ((sp - 40#64) ↦₆₄ c7) ∗
        ((sp - 32#64) ↦₆₄ c8) ∗ ((sp - 24#64) ↦₆₄ c9) ∗
        ((sp - 16#64) ↦₆₄ c10) ∗ ((sp - 8#64) ↦₆₄ c11)) := by
  rw [memRegion_out32_cellsX, stackAt_serialize_none_preX]

theorem sepWP_exists_left_sepX {α : Sort _} {prog : Program} {pc : BitVec 64} {s : State}
    {P : α → SepProp} {F : SepProp} {post : State → SepProp → Prop}
    (h : ∀ x, SepWP prog pc s (P x ∗ F) post) :
    SepWP prog pc s ((∃∗ x, P x) ∗ F) post := by
  rw [sepExists_sepConj_left]
  exact SepWP.exists_left h

theorem sepWP_pure_left_sepX {prog : Program} {pc : BitVec 64} {s : State}
    {φ : Prop} {P F : SepProp} {post : State → SepProp → Prop}
    (h : φ → SepWP prog pc s (P ∗ F) post) :
    SepWP prog pc s ((⌜φ⌝ ∗ P) ∗ F) post := by
  rw [sepConj_assoc]
  exact SepWP.pure_elim h

theorem vecU8_nil_from_out_cellsX (A : RustAlloc) (out : BitVec 64) :
    (((out + 8#64) ↦₆₄ 0#64) ∗ ((out + 16#64) ↦₆₄ 1#64) ∗ ((out + 24#64) ↦₆₄ 0#64)) ⊢
      vecU8 A (out + 8#64) [] := by
  have hp := pointsTo64_pair_out out 0#64 1#64
  have hpull :
      (((out + 8#64) ↦₆₄ 0#64) ∗ ((out + 16#64) ↦₆₄ 1#64) ∗ ((out + 24#64) ↦₆₄ 0#64)) =
      ((((out + 8#64) ↦₆₄ 0#64) ∗ ((out + 16#64) ↦₆₄ 1#64)) ∗ ((out + 24#64) ↦₆₄ 0#64)) := by
    ac_rfl
  rw [hpull, ← hp]
  exact vecU8_nil_from_out_stores A out

theorem vecU8_from_out_cellsX (A : RustAlloc) (out cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    (((out + 8#64) ↦₆₄ cap) ∗ ((out + 16#64) ↦₆₄ ptr) ∗
      ((out + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      RustHeap.vecU8Buf A cap ptr bs) ⊢
      vecU8 A (out + 8#64) bs := by
  have hp := pointsTo64_pair_out out cap ptr
  have hpull :
      (((out + 8#64) ↦₆₄ cap) ∗ ((out + 16#64) ↦₆₄ ptr) ∗
        ((out + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        RustHeap.vecU8Buf A cap ptr bs) =
      ((((out + 8#64) ↦₆₄ cap) ∗ ((out + 16#64) ↦₆₄ ptr)) ∗
        ((out + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        RustHeap.vecU8Buf A cap ptr bs) := by
    ac_rfl
  rw [hpull, ← hp]
  exact vecU8_from_out_stores A out cap ptr bs

theorem vecHeader_cells_800X (sp : BitVec 64) :
    (((sp - 800#64) ↦₆₄ 0#64) ∗ ((sp - 792#64) ↦₆₄ 8#64) ∗ ((sp - 784#64) ↦₆₄ 0#64)) =
      vecHeader (sp - 800#64) 0#64 8#64 0#64 := by
  unfold vecHeader
  have e1 : sp - 800#64 + 8#64 = sp - 792#64 := bv_sub_add_lit sp 800 8
  have e2 : sp - 800#64 + 16#64 = sp - 784#64 := bv_sub_add_lit sp 800 16
  rw [e1, e2]

theorem repack_stack_none_cellsX (sp wn w0 w1 w2 : BitVec 64)
    {bs336 : List (BitVec 8)} (h336 : bs336.length = 336) :
    (stackAt (sp - 800#64) serializeSubStackX ∗
      ((sp - 800#64) ↦₆₄ 0#64) ∗ ((sp - 792#64) ↦₆₄ 8#64) ∗ ((sp - 784#64) ↦₆₄ 0#64) ∗
      ((sp - 776#64) ↦₆₄ wn) ∗
      ((sp - 768#64) ↦ₛ bs336) ∗
      ((sp - 432#64) ↦₆₄ w0) ∗
      ((sp - 424#64) ↦₆₄ w1) ∗
      ((sp - 416#64) ↦₆₄ w2) ∗
      memRegion (sp - 408#64) 312 ∗
      cells (sp - 96#64) 12) ⊢
      stackAt sp serializeStackX := by
  have hp : ((sp - 432#64) ↦₆₄ w0) ∗ ((sp - 424#64) ↦₆₄ w1) =
      ((sp - 432#64) ↦₁₂₈ (w1 ++ w0)) := pointsTo64_pair_sub sp 432 w0 w1
  have hv := vecHeader_cells_800X sp
  have hpull :
      (stackAt (sp - 800#64) serializeSubStackX ∗
        ((sp - 800#64) ↦₆₄ 0#64) ∗ ((sp - 792#64) ↦₆₄ 8#64) ∗ ((sp - 784#64) ↦₆₄ 0#64) ∗
        ((sp - 776#64) ↦₆₄ wn) ∗
        ((sp - 768#64) ↦ₛ bs336) ∗
        ((sp - 432#64) ↦₆₄ w0) ∗
        ((sp - 424#64) ↦₆₄ w1) ∗
        ((sp - 416#64) ↦₆₄ w2) ∗
        memRegion (sp - 408#64) 312 ∗
        cells (sp - 96#64) 12) =
      (stackAt (sp - 800#64) serializeSubStackX ∗
        (((sp - 800#64) ↦₆₄ 0#64) ∗ ((sp - 792#64) ↦₆₄ 8#64) ∗ ((sp - 784#64) ↦₆₄ 0#64)) ∗
        ((sp - 776#64) ↦₆₄ wn) ∗
        ((sp - 768#64) ↦ₛ bs336) ∗
        (((sp - 432#64) ↦₆₄ w0) ∗ ((sp - 424#64) ↦₆₄ w1)) ∗
        ((sp - 416#64) ↦₆₄ w2) ∗
        memRegion (sp - 408#64) 312 ∗
        cells (sp - 96#64) 12) := by
    ac_rfl
  rw [hpull, hv, hp]
  exact repack_stack_noneX sp wn (w1 ++ w0) w2 h336

theorem allocFailedIn_of_trace_eqX {s0 sm sf : State} (htr : sm.trace = s0.trace)
    (h : allocFailedIn sm sf ∧ sm.trace <+: sf.trace) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  unfold allocFailedIn at h ⊢
  rwa [htr] at h

theorem allowPanic_frame_traceX {s0 sm sf : State} {F R : SepProp}
    (htr : sm.trace = s0.trace)
    (h : sf.mem ⊨ ((⌜allocFailedIn sm sf ∧ sm.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R :=
  allowPanic_frame (allocFailedIn_of_trace_eqX htr) h

/-! ## `SepWPpIn` entry and call tactics -/

open Lean Meta Elab Tactic in
/-- `wppin_init x s0`: like `wpp_init`, for an `.inImage img` spec, reducing `subroutine_ok` to a
`SepWPpIn img` goal via `subroutine_ok_inImage_of_sepWPpIn`. -/
elab "wppin_init " a:ident s0:ident : tactic => do
  let rId := mkIdent `R
  let hpcId := mkIdent `hpc
  let hrunId := mkIdent `hrun
  let hpreId := mkIdent `hpre
  let hspId := mkIdent `hsp_align
  evalTactic (← `(tactic| (
    apply subroutine_ok_inImage_of_sepWPpIn
    intro $a:ident $rId:ident $s0:ident $hpcId:ident $hrunId:ident $hpreId:ident $hspId:ident
    wp_unfold_specs)))
  wpSplitAndNormHyps (unpackProds := false)
  let g ← getMainGoal
  let (pExpr, fExpr) ← g.withContext do
    let lctx ← getLCtx
    let rFVar := (lctx.findFromUserName? rId.getId).map (·.toExpr)
    let mut fullPreOpt : Option Expr := none
    for decl in lctx do
      if !decl.isImplementationDetail && !decl.isAuxDecl then
        let ty ← instantiateMVars decl.type
        if ty.isAppOfArity ``SepProp.Satisfies 2 then
          fullPreOpt := some (ty.getArg! 0)
          break
    let fullPre := fullPreOpt.getD (rFVar.getD (mkConst ``SepProp.emp))
    let atoms := SepSolver.atoms fullPre
    let spatial := atoms.filter (fun (e : Expr) => rFVar != some e)
    let conj : Expr :=
      if spatial.isEmpty then mkConst ``SepProp.emp
      else
        let n := spatial.size
        (List.range (n - 1)).foldr
          (fun i acc => mkApp2 (mkConst ``SepProp.sepConj) spatial[i]! acc) spatial[n - 1]!
    Pure.pure (conj, rFVar.getD (mkConst ``SepProp.emp))
  let pStx ← g.withContext (PrettyPrinter.delab pExpr)
  let fStx ← g.withContext (PrettyPrinter.delab fExpr)
  evalTactic (← `(tactic| (
    refine ⟨$pStx, $fStx, ?_, ?_⟩
    wp_focus_close arm64_sep_close)))

open Lean Meta Elab Tactic in
/-- Eliminate leading `∃∗` / `⌜φ⌝` atoms of a `SepWPpIn` precondition (arg 5). -/
meta def wppinElimSpatialContext (hEq : Ident) : TacticM Unit := do
  let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| (
    conv =>
      arg 5
      simp (config := { decide := true }) only [
        stackFrame16, stackFrame32, stackFrame16At_def, stackFrame32At_def,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
        wp_norm, arm64_norm, $hEq:ident]))))
  for _ in [0:64] do
    let g ← getMainGoal
    let ty ← g.withContext (instantiateMVars (← g.getType))
    unless ty.isAppOfArity ``SepWPpIn 7 do return
    let P := (ty.getArg! 4).consumeMData
    if P.isAppOfArity ``SepProp.sepExists 2 then
      let wId ← freshIdent `w
      evalTactic (← `(tactic| (apply SepWPpIn.exists_elim; intro $wId:ident)))
      betaReduceTarget
    else if P.isAppOfArity ``SepProp.sepConj 2 && (P.getArg! 0).isAppOfArity ``SepProp.pure 1 then
      let hId ← freshIdent `hpost
      evalTactic (← `(tactic| (apply SepWPpIn.pure_elim; intro $hId:ident)))
      wpNormAndSplitHyp hId
    else
      return

open Lean Meta Elab Tactic in
meta def closeWppinCallSiteSetupSubgoals : TacticM Unit := do
  let gs ← getGoals
  let gPc :: gRun :: gSp :: gLr :: rest := gs
    | throwError "wppin_call: unexpected subgoals after applying SepWPpIn.call_inImage"
  setGoals [gPc]
  if !(← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| wp_focus_close (first | wp_norm_goal | wp_norm_lhs))))) then
    let ty ← gPc.withContext (instantiateMVars (← gPc.getType))
    throwError "wppin_call: call target address does not match callee entry:{indentExpr ty}"
  setGoals [gRun]
  if !(← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| wp_focus_close wp_norm_lhs)))) then
    let ty ← gRun.withContext (instantiateMVars (← gRun.getType))
    throwError "wppin_call: failed to prove machine status is `.Running`:{indentExpr ty}"
  setGoals [gSp]
  if !(← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| wp_focus_close (first | wp_norm_lhs | wp_norm_goal))))) then
    let ty ← gSp.withContext (instantiateMVars (← gSp.getType))
    throwError "wppin_call: failed to prove `s.spAligned = true`:{indentExpr ty}"
  setGoals [gLr]
  if !(← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| wp_focus_close (first | wp_norm_lhs | wp_norm_goal))))) then
    let ty ← gLr.withContext (instantiateMVars (← gLr.getType))
    throwError "wppin_call: failed to resolve link register (`s.readReg64 .lr = ret_pc`):{indentExpr ty}"
  setGoals (← rest.filterM fun m => not <$> m.isAssigned)

open Lean Meta Elab Tactic in
/-- Calls an `.inImage img` callee from a `SepWPpIn img` goal via `SepWPpIn.call_inImage`,
discharging panic and exit side conditions with `allowPanic_frame_traceX` and
`not_satisfies_false_sepConj`. -/
elab "wppin_call " hcall:term:max arg?:(ppSpace colGt term:max)? : tactic => do
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let applyStx ← match arg? with
    | some a => `(tactic| apply (SepWPpIn.call_inImage $hcall (x := $a)))
    | none => `(tactic| apply (SepWPpIn.call_inImage $hcall))
  evalTactic applyStx
  closeWppinCallSiteSetupSubgoals
  let gsAfterSetup ← getGoals
  let gPre :: gExit :: gPanic :: gCont :: rest := gsAfterSetup
    | throwError "wppin_call: unexpected subgoals after `SepWPpIn.call_inImage`"
  setGoals [gPre]
  evalTactic (← `(tactic| intro _R' _hmR'))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only
    try simp (config := { decide := true }) only [
      stackFrame16, stackFrame32, stackFrame16At_def, stackFrame32At_def,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc,
      wp_norm, arm64_norm] at _hmR' ⊢
  )))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars (some hcall)
  setGoals (gExit :: gPanic :: gCont :: rest)
  evalTactic (← `(tactic| (
    wp_focus_close (wp_unfold_specs; intro _ _ _ _ _he; exact not_satisfies_false_sepConj _he)
    wp_focus_close (wp_unfold_specs; intro _ _ _hp; first | exact allowPanic_frame_traceX (by wp_norm_lhs) _hp | exact (not_satisfies_false_sepConj (by simpa only [sepConj_assoc] using _hp)).elim | (simp only [sepConj_assoc, satisfies_pure_sepConj] at _hp; exact _hp.1.elim))
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident
  )))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId
  wppinElimSpatialContext hspId

/-! ## `None`-branch verification on `SP2Ext` -/

theorem serialize_none_okX {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr serializeName)
      ((serializeNoneSpecX A).inImage img) := by
  have hfn : libsignalSessionCode.fnOff serializeName = num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize") :=
    libsignalSessionCode_fnOff_serialize
  have hmemcpy := memcpy_sub_okX (img := img) (A := A) (ext := ext) hC
  have hvv := vecVecClone_sub_okX img.base ext
  code_fetches_from CryptoVerification.libsignalSessionCode serializeBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) 0 56
  code_fetches_from CryptoVerification.libsignalSessionCode serializeBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) 0x5c 48
  code_fetches_from CryptoVerification.libsignalSessionCode serializeBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) 0x10c 12
  code_fetches_from CryptoVerification.libsignalSessionCode serializeBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) 0x128 4
  code_fetches_from CryptoVerification.libsignalSessionCode serializeBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) 0x188 20
  code_fetches_from CryptoVerification.libsignalSessionCode serializeBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) 0x1a8 24
  code_fetches_from CryptoVerification.libsignalSessionCode serializeBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) 0x2b4 32
  code_fetches_from CryptoVerification.libsignalSessionCode serializeBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) 0x2dc 8
  code_fetches_from CryptoVerification.libsignalSessionCode serializeBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) 0x310 8
  code_fetches_from CryptoVerification.libsignalSessionCode serializeBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) 0x32c 32
  unfold serializeNoneSpecX
  simp only [noneCap, okTagVec, memRegion_out32_stack_noneX,
    sepExists_sepConj_left, sepExists_sepConj_right]
  wppin_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨self, out, prevPtr⟩ := x
  dsimp only at *
  apply SepWPpIn.of_sepWP (mid := entry + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize"))
  wp_steps
  wp_call hvv ⟨s0.sp - 800#64, prevPtr⟩
  wp_simp_pre [vecHeader, arm64_norm]
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  rw [← h]
  change subroutine_ok (SP2Ext img.base ext) (entry + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) (memcpySubSpecX.inImage img) at hmemcpy
  wppin_call hmemcpy (s0.sp - 768#64, s0.sp - 432#64, v_stk_12)
  apply SepWPpIn.of_sepWP_ret
  refine SepWP.fold (bytes336_to_w012 s0.sp h) (by sep_frame) ?_
  apply sepWP_exists_left_sepX; intro w0
  apply sepWP_exists_left_sepX; intro w1
  apply sepWP_exists_left_sepX; intro w2
  wp_steps
  refine SepWP.fold (vecU8_nil_from_out_cellsX A out) (by sep_frame) ?_
  refine SepWP.fold (cells_12_pack s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_frame) ?_
  wp_simp_pre [hsp_sf]
  refine SepWP.fold (repack_stack_none_cellsX s0.sp _ _ _ _ h) (by sep_frame) ?_
  wp_done

/-! ## Relocatable `[LibsignalPlacement]` `None`-branch proof (Block `52`) -/

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

attribute [local irreducible] Program.fetch Program.externAt?

theorem L1_SerializeBodyNoneX_Placed : True := trivial

open Lean Meta Elab Tactic in
/-- Reduces `subroutine_ok` for a `withLsCodeLoaded` spec to a `SepWPpLsCl` goal via
`subroutine_ok_withLsCodeLoaded_of_sepWPpLsCl`. -/
elab "wpplscl_init " a:ident s0:ident : tactic => do
  let rId := mkIdent `R
  let hpcId := mkIdent `hpc
  let hrunId := mkIdent `hrun
  let hpreId := mkIdent `hpre
  let hspId := mkIdent `hsp_align
  evalTactic (← `(tactic| (
    apply subroutine_ok_withLsCodeLoaded_of_sepWPpLsCl
    intro $a:ident $rId:ident $s0:ident $hpcId:ident $hrunId:ident $hpreId:ident $hspId:ident
    wp_unfold_specs)))
  wpSplitAndNormHyps (unpackProds := false)
  let g ← getMainGoal
  let (pExpr, fExpr) ← g.withContext do
    let lctx ← getLCtx
    let rFVar := (lctx.findFromUserName? rId.getId).map (·.toExpr)
    let mut fullPreOpt : Option Expr := none
    for decl in lctx do
      if !decl.isImplementationDetail && !decl.isAuxDecl then
        let ty ← instantiateMVars decl.type
        if ty.isAppOfArity ``SepProp.Satisfies 2 then
          fullPreOpt := some (ty.getArg! 0)
          break
    let fullPre := fullPreOpt.getD (rFVar.getD (mkConst ``SepProp.emp))
    let atoms := SepSolver.atoms fullPre
    let spatial := atoms.filter (fun (e : Expr) => rFVar != some e)
    let conj : Expr :=
      if spatial.isEmpty then mkConst ``SepProp.emp
      else
        let n := spatial.size
        (List.range (n - 1)).foldr
          (fun i acc => mkApp2 (mkConst ``SepProp.sepConj) spatial[i]! acc) spatial[n - 1]!
    Pure.pure (conj, rFVar.getD (mkConst ``SepProp.emp))
  let pStx ← g.withContext (PrettyPrinter.delab pExpr)
  let fStx ← g.withContext (PrettyPrinter.delab fExpr)
  evalTactic (← `(tactic| (
    refine ⟨$pStx, $fStx, ?_, ?_⟩
    wp_focus_close arm64_sep_close)))

open Lean Meta Elab Tactic in
/-- Eliminate leading `∃∗` / `⌜φ⌝` atoms of a `SepWPpLsCl` precondition (arg 5). -/
meta def wpplsclElimSpatialContext (hEq : Ident) : TacticM Unit := do
  let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| (
    conv =>
      arg 5
      simp (config := { decide := true }) only [
        stackFrame16, stackFrame32, stackFrame16At_def, stackFrame32At_def,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
        wp_norm, arm64_norm, $hEq:ident]))))
  for _ in [0:64] do
    let g ← getMainGoal
    let ty ← g.withContext (instantiateMVars (← g.getType))
    unless ty.isAppOfArity ``SepWPpLsCl 7 do return
    let P := (ty.getArg! 4).consumeMData
    if P.isAppOfArity ``SepProp.sepExists 2 then
      let wId ← freshIdent `w
      evalTactic (← `(tactic| (apply SepWPpLsCl.exists_elim; intro $wId:ident)))
      betaReduceTarget
    else if P.isAppOfArity ``SepProp.sepConj 2 && (P.getArg! 0).isAppOfArity ``SepProp.pure 1 then
      let hId ← freshIdent `hpost
      evalTactic (← `(tactic| (apply SepWPpLsCl.pure_elim; intro $hId:ident)))
      wpNormAndSplitHyp hId
    else
      return

open Lean Meta Elab Tactic in
/-- `wpplscl_call hcall ghost`: call a `withLsCodeLoaded` callee from a `SepWPpLsCl` goal. -/
elab "wpplscl_call " hcall:term:max arg?:(ppSpace colGt term:max)? : tactic => do
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let applyStx ← match arg? with
    | some a => `(tactic| apply (SepWPpLsCl.call_withLsCodeLoaded $hcall (x := $a)))
    | none => `(tactic| apply (SepWPpLsCl.call_withLsCodeLoaded $hcall))
  evalTactic applyStx
  closeWppinCallSiteSetupSubgoals
  let gsAfterSetup ← getGoals
  let gPre :: gExit :: gPanic :: gCont :: rest := gsAfterSetup
    | throwError "wpplscl_call: unexpected subgoals after `SepWPpLsCl.call_withLsCodeLoaded`"
  setGoals [gPre]
  evalTactic (← `(tactic| intro _R' _hmR'))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only
    try simp (config := { decide := true }) only [
      stackFrame16, stackFrame32, stackFrame16At_def, stackFrame32At_def,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc,
      wp_norm, arm64_norm] at _hmR' ⊢
  )))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars (some hcall)
  setGoals (gExit :: gPanic :: gCont :: rest)
  evalTactic (← `(tactic| (
    wp_focus_close (wp_unfold_specs; intro _ _ _ _ _he; exact not_satisfies_false_sepConj _he)
    wp_focus_close (wp_unfold_specs; intro _ _ _hp; first | exact allowPanic_frame_traceX (by wp_norm_lhs) _hp | exact (not_satisfies_false_sepConj (by simpa only [sepConj_assoc] using _hp)).elim | (simp only [sepConj_assoc, satisfies_pure_sepConj] at _hp; exact _hp.1.elim))
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident
  )))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId
  wpplsclElimSpatialContext hspId

theorem serialize_none_placed_okX [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced A H) :
    subroutine_ok (lsProg_52 H) (blkPl_52).base
      (withLsCodeLoaded lsmpl (serializeNoneSpecX A)) := by
  have hmemcpy := memcpy_placed_sub_okX (callerProg := lsProg_52 H) hC
  have hvv := vecVecClone_placed_sub_okX (callerProg := lsProg_52 H)
  unfold serializeNoneSpecX
  simp only [noneCap, okTagVec, memRegion_out32_stack_noneX,
    sepExists_sepConj_left, sepExists_sepConj_right]
  wpplscl_init x s0
  obtain ⟨self, out, prevPtr⟩ := x
  dsimp only at *
  apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 117)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  change subroutine_ok (lsProg_52 H) (lsmpl.base 117)
    (withLsCodeLoaded lsmpl vecVecCloneSubSpecX) at hvv
  wpplscl_call hvv ⟨s0.sp - 800#64, prevPtr⟩
  apply SepWPpLsCl.of_sepWP (mid := lsρ lsMemcpySym)
  conv => arg 4; simp only [vecHeader, arm64_norm, hsp_sf]
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  rw [← h]
  change subroutine_ok (lsProg_52 H) (lsρ lsMemcpySym)
    (withLsCodeLoaded lsmpl memcpySubSpecX) at hmemcpy
  wpplscl_call hmemcpy (s0.sp - 768#64, s0.sp - 432#64, v_stk_12)
  apply SepWPpLsCl.of_sepWP_ret
  conv => arg 4; simp only [hsp_sf, hsp_sf_1]
  refine SepWP.fold (bytes336_to_w012 s0.sp h) (by sep_frame) ?_
  apply sepWP_exists_left_sepX; intro w0
  apply sepWP_exists_left_sepX; intro w1
  apply sepWP_exists_left_sepX; intro w2
  wp_steps
  refine SepWP.fold (vecU8_nil_from_out_cellsX A out) (by sep_frame) ?_
  refine SepWP.fold (cells_12_pack s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_frame) ?_
  refine SepWP.fold (repack_stack_none_cellsX s0.sp _ _ _ _ h) (by sep_frame) ?_
  wp_done

end Placed

end CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX
