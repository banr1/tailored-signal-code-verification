/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerDefsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBodyB
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodySomeX
import ProofLib.SepLogic.WPp

/-!
# Relocatable `SessionRecord::serialize` with One Previous Session: Epilogue Tail

Relocatable `[LibsignalPlacement]` proof of `serPrev1Tail_placed_ok : SerPrev1PlacedTailStmt A H`
(`+692 .. ret` on Block `52`) and `k5_fold_q_placed`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 2000000

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection CryptoGames
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.Serialization CryptoVerification.E2E.Record.Placed
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX
open Proofs.libsignal.Hooks2

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local wp_norm] calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite calleeSavedVRegs_writeVReg64_ite
  calleeSavedVRegs_writeVReg32_ite isCalleeSavedVReg updateCalleeSavedVRegs

/-! ## Call and precondition-folding tactics on `SepWPpLsCl` -/

theorem sepWPpLsCl_fold {pl : Obj.MultiPlacement} {prog : Program} {ret : BitVec 64} {s : State}
    {P T T' F : SepProp} {Q Qp : State → SepProp → Prop}
    (hent : T ⊢ T') (hf : P = T ∗ F) (h : SepWPpLsCl pl prog ret s (T' ∗ F) Q Qp) :
    SepWPpLsCl pl prog ret s P Q Qp :=
  SepWPpLsCl.weaken_pre (hf ▸ sepConj_mono_left hent) h

open Lean Meta Elab Tactic in
/-- `k5t_placed_call hcall ghost`: `wpplscl_call` for a callee whose `onPanic` is `⌜False⌝`, under a
generic `Qp` with a local `hQp : ∀ sf P_f, PanicAllocPost s0 sf P_f → Qp sf P_f`. -/
elab "k5t_placed_call " hcall:term:max arg?:(ppSpace colGt term:max)? : tactic => do
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let hQpId := mkIdent `hQp
  let applyStx ← match arg? with
    | some a => `(tactic| apply (SepWPpLsCl.call_withLsCodeLoaded $hcall (x := $a)))
    | none => `(tactic| apply (SepWPpLsCl.call_withLsCodeLoaded $hcall))
  evalTactic applyStx
  closeWppinCallSiteSetupSubgoals
  let gsAfterSetup ← getGoals
  let gPre :: gExit :: gPanic :: gCont :: rest := gsAfterSetup
    | throwError "k5t_placed_call: unexpected subgoals after `SepWPpLsCl.call_withLsCodeLoaded`"
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
    wp_focus_close (
      intro _sfp _hstp
      apply $hQpId:ident
      intro _Rp _hmp
      exfalso
      first
        | exact k5t_false_left _hmp
        | exact k5t_false_left (by simpa only [sepConj_assoc] using _hmp)
        | (simp only [withLsCodeLoaded, sepConj_assoc, satisfies_pure_sepConj] at _hmp
           exact _hmp.1.elim)
        | (simp only [withLsCodeLoaded, dropLocal1SubSpecX, deallocSubSpecX, sepConj_assoc,
             satisfies_pure_sepConj] at _hmp
           exact _hmp.1.elim))
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident
  )))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId
  wpplsclElimSpatialContext hspId

/-- `k5t_placed_callc h S ghost`: refold `h` to `subroutine_ok _ _ S`, call it with
`k5t_placed_call`, then normalize `sp`. -/
macro "k5t_placed_callc " h:ident S:term:max g:term:max : tactic =>
  `(tactic| (change subroutine_ok _ _ $S at $h:ident; k5t_placed_call $h $g; try wpplscl_sp_norm))

/-! ## Shared epilogue (`+812 .. ret`) and tail (`+692 .. ret`) -/

set_option maxHeartbeats 400000 in
theorem serPrev1Tail_placed_epilogue [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (out q' cap' ptr' : BitVec 64) (bs : List (BitVec 8))
    {ret : BitVec 64} {s0 s : State} {P Fx : SepProp} {Q Qp : State → SepProp → Prop}
    (hQ : ∀ sf : State, sf.trace = s0.trace → sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      Q sf (((out ↦₆₄ okTagVec) ∗ vecU8 A (out + 8#64) bs ∗ A.pool ∗
        stackAt s0.sp serializeStackX) ∗ Fx))
    (hal0 : s0.sp &&& 15#64 = 0#64)
    (hpc : s.pc = (blkPl_52).base + bv% (812))
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 800#64)
    (htr : s.trace = s0.trace)
    (hvr : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P =
      (stackAt (s0.sp - 800#64) serializeSubStackX ∗
        ((s0.sp - 800#64) ↦₆₄ 1#64) ∗ ((s0.sp - 792#64) ↦₆₄ q') ∗
        ((s0.sp - 784#64) ↦₆₄ 1#64) ∗ memRegion (s0.sp - 776#64) 344 ∗
        ((s0.sp - 432#64) ↦₆₄ cap') ∗ ((s0.sp - 424#64) ↦₆₄ ptr') ∗
        ((s0.sp - 416#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        RustHeap.vecU8Buf A cap' ptr' bs ∗
        memRegion (s0.sp - 408#64) 312 ∗
        (out ↦₆₄ okTagVec) ∗ ((out + 8#64) ↦₆₄ cap') ∗
        ((out + 16#64) ↦₆₄ ptr') ∗ ((out + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        A.pool ∗ serSavedCells s0 ret) ∗ Fx) :
    SepWPpLsCl lsmpl (lsProg_52 H) ret s P Q Qp := by
  have hal0' : (s0.sp &&& 15#64 == 0#64) = true := by simp only [hal0, beq_self_eq_true]
  have hal : ((s0.sp - 800#64) &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 800#64 hal0'
  subst hP
  unfold serSavedCells
  simp only [sepConj_assoc]
  change s.pc = (blkPl_52).base + 812#64 at hpc
  apply SepWPpLsCl.of_sepWP_ret
  wp_steps
  refine SepWP.fold (vecU8_from_out_cellsX A out cap' ptr' bs) (by sep_frame) ?_
  refine SepWP.fold (cells_12_pack s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_frame) ?_
  refine SepWP.fold (repack_stack_hdr_cellsX s0.sp 1#64 q' 1#64 cap' ptr'
    (BitVec.ofNat 64 bs.length)) (by sep_frame) ?_
  refine SepWP.weaken_pre (P' := ((out ↦₆₄ okTagVec) ∗ vecU8 A (out + 8#64) bs ∗ A.pool ∗
    stackAt s0.sp serializeStackX) ∗ Fx) ?_ ?_
  · exact Entails.of_eq (by ac_rfl)
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) (hQ _ ?_ ?_ ?_)
  · simp only [wp_norm, arm64_norm, *]
  · simp only [wp_norm, arm64_norm, *]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [wp_norm, arm64_norm, *]

set_option maxHeartbeats 800000 in
theorem serPrev1Tail_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : SerContractsXPlaced A H) (hDrop : DropSessionStructureLocal1PlacedOkX A H) :
    SerPrev1PlacedTailStmt A H := by
  intro out q' capE ptrE cap' ptr' o0 o1 o2 o3 bs enc w sess' ret s0 sm Fx Q Qp
    hQp hQ hal0 hpc hrun hsp htr hx19 hx23 hx24 hvr
  have hEpi := @serPrev1Tail_placed_epilogue _ A H
  have hdrop : subroutine_ok (lsProg_52 H) (lsmpl.base 6)
      (withLsCodeLoaded lsmpl (dropLocal1SubSpecX A)) :=
    dropLocal1_placed_sub_okX (callerProg := lsProg_52 H) hDrop
  have hdealloc : subroutine_ok (lsProg_52 H) (lsρ lsRustDeallocSym)
      (withLsCodeLoaded lsmpl (deallocSubSpecX A)) :=
    dealloc_placed_sub_okX (callerProg := lsProg_52 H) hC
  have hx19' : sm.readReg64 (Reg.gpr 19#5) = out := hx19
  have hx23' : (sm.readReg64 (Reg.gpr 23#5) + 1#64 == 0#64) = false := hx23
  have hx24' : sm.readReg64 (Reg.gpr 24#5) = s0.sp - 800#64 := hx24
  have hal0' : (s0.sp &&& 15#64 == 0#64) = true := by simp only [hal0, beq_self_eq_true]
  have hal : ((s0.sp - 800#64) &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 800#64 hal0'
  have hl24 : LayoutOk 24 8 := layoutOk_24_8_ser
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  clear hx19 hx23 hx24
  rw [vecU8At_unpack_cells_432X, vecU8At_cells A q' capE ptrE enc]
  simp only [sepConj_assoc]
  change sm.pc = (blkPl_52).base + 692#64 at hpc
  refine sepWPpLsCl_fold (vecU8Buf_drop_view A capE ptrE enc) (by sep_frame) ?_
  simp only [sepConj_assoc]
  refine SepWPpLsCl.pure_elim fun hcapE63 => ?_
  apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 6)
  wp_steps
  refine SepWP.fold (sessionAt_entails_sessionStateAt A (s0.sp - 776#64) w sess') (by sep_frame) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  k5t_placed_callc hdrop (withLsCodeLoaded lsmpl (dropLocal1SubSpecX A)) ⟨s0.sp - 776#64, w, sess'.state⟩
  by_cases hc : capE = 0#64
  · rw [ite_eq_left hc, emp_sepConj]
    subst hc
    apply SepWPpLsCl.of_sepWP (mid := lsρ lsRustDeallocSym)
    wp_steps
    refine SepWP.fold (prevVec1_cap1_merge q' 0#64 ptrE (BitVec.ofNat 64 enc.length))
      (by sep_frame) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    k5t_placed_callc hdealloc (withLsCodeLoaded lsmpl (deallocSubSpecX A)) (q', 24, 8)
    exact hEpi out q' cap' ptr' bs hQ hal0
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [okTagVec]; sep_frame)
  · have hlE : LayoutOk capE.toNat 1 := layoutOk_cap_u8_ser hc hcapE63
    have hcE : (capE == 0#64) = false := beq_false_of_ne hc
    rw [ite_eq_right hc]
    simp only [sepConj_assoc]
    apply SepWPpLsCl.of_sepWP (mid := lsρ lsRustDeallocSym)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    k5t_placed_callc hdealloc (withLsCodeLoaded lsmpl (deallocSubSpecX A)) (ptrE, capE.toNat, 1)
    apply SepWPpLsCl.of_sepWP (mid := lsρ lsRustDeallocSym)
    wp_steps
    refine SepWP.fold (prevVec1_cap1_merge q' capE ptrE (BitVec.ofNat 64 enc.length))
      (by sep_frame) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    k5t_placed_callc hdealloc (withLsCodeLoaded lsmpl (deallocSubSpecX A)) (q', 24, 8)
    exact hEpi out q' cap' ptr' bs hQ hal0
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [okTagVec]; sep_frame)

theorem k5_fold_q_placed {pl : Obj.MultiPlacement} {prog : Program} {ret : BitVec 64} {s : State}
    {Q Qp : State → SepProp → Prop} (A : RustAlloc) (q capE ptrE : BitVec 64)
    (enc : List (BitVec 8)) {P F : SepProp}
    (hP : P = ((q ↦₆₄ capE) ∗ ((q + 8#64) ↦₆₄ ptrE) ∗
      ((q + 16#64) ↦₆₄ BitVec.ofNat 64 enc.length) ∗ RustHeap.vecU8Buf A capE ptrE enc) ∗ F)
    (h : SepWPpLsCl pl prog ret s (vecU8At A q capE ptrE enc ∗ F) Q Qp) :
    SepWPpLsCl pl prog ret s P Q Qp := by
  subst hP
  exact SepWPpLsCl.weaken_pre (sepConj_mono_left (Entails.of_eq (vecU8At_cells A q capE ptrE enc).symm)) h

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
