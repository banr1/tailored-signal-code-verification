/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1StepsXExt
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1StepsXExtPlaced
public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import Lean.Elab.Tactic -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.Bin.Hooks
import LibsignalBinary.Proofs.PublicApi.StoreKit.RecordMove
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Stage P1 Segment Helpers — Part 1

Proves `RustCliAllocBudget M` / `VmPreserved` Stage P1 entry and `load_session` (`None` and `Some`
header copy) segment lemmas on Block `518` (`stageP1ProgPlaced ext`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1StepsXExtPlacedBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection
open LibsignalBinary.Heap
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (sepWP_rebase_vmPreserved trapHooks)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.Pf.RecordMove
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegTrust
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

theorem sepWP_seg_rebase_vm {P : Program} {b : BitVec 64}
    {Hk : String → Option (State → State)}
    {mid target : BitVec 64} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop}
    (hseg : SepWP ((P.rebase b trapHooks).withSvc noSyscalls) mid s Pre
      (fun sm Pm => sm.tpidrEl0 = s.tpidrEl0 ∧
        (VmPreserved s sm → sm.pc = mid → sm.status = .Running →
          SepWP (P.rebase b Hk) target sm Pm post))) :
    SepWP (P.rebase b Hk) target s Pre post := by
  apply SepWP.of_reaches_pc
  intro R hm hL
  obtain ⟨sm, hsteps1, ⟨hpcm, hrunm, Pm, hPm, hvm, hcont⟩ | ⟨_, hoom⟩⟩ :=
    SepWP.to_reaches_pc (sepWP_rebase_vmPreserved hseg) hm hL
  · obtain ⟨sf, hsteps2, hout2⟩ :=
      SepWP.to_reaches_pc (hcont hvm hpcm hrunm) hPm (hsteps1.codeLoaded hL)
    exact ⟨sf, hsteps1.trans hsteps2, hout2⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

local elab "wp_steps_sync_pool_518 " _ext:term:max mid:term : tactic => do
  Lean.Elab.Tactic.evalTactic
    (← `(tactic| apply sepWP_seg_rebase_vm (P := blkPC_518) (b := blkPl_518.base) (mid := $mid)))
  let g ← Lean.Elab.Tactic.getMainGoal
  g.withContext do
    let outerLCtx ← Lean.getLCtx
    let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
    let e2 := ty.getArg! 0
    let e1 := e2.getArg! 0
    let ty1 := Lean.mkAppN ty.getAppFn
      #[e1, ty.getArg! 1, ty.getArg! 2, ty.getArg! 3, ty.getArg! 4, ty.getArg! 5]
    let g1 ← Lean.Meta.mkFreshExprMVar ty1
    let savedGoals ← Lean.Elab.Tactic.getGoals
    Lean.Elab.Tactic.setGoals [g1.mvarId!]
    Lean.Elab.Tactic.evalTactic (← `(tactic| (
      wp_steps
      refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        ⟨by first | rfl | simp only [wp_norm, arm64_norm], ?_⟩)))
    let rem ← Lean.Elab.Tactic.getGoals
    let [remId] := rem
      | throwError "wp_steps_sync_pool_518: expected 1 continuation goal, got {rem.length}"
    let (newArgFVars, newNames, contForallType) ← remId.withContext do
      let remLCtx ← Lean.getLCtx
      let mut fvs : Array Lean.Expr := #[]
      let mut argFvs : Array Lean.Expr := #[]
      let mut nms : Array Lean.Name := #[]
      for decl in remLCtx do
        if !decl.isImplementationDetail && !outerLCtx.contains decl.fvarId then
          fvs := fvs.push decl.toExpr
          if !decl.isLet then
            argFvs := argFvs.push decl.toExpr
          nms := nms.push decl.userName
      let remType ← Lean.instantiateMVars (← remId.getType)
      let cTy ← Lean.Meta.mkForallFVars fvs remType (usedLetOnly := false)
      pure (argFvs, nms, cTy)
    let gNext ← Lean.Meta.mkFreshExprMVar contForallType
    Lean.Meta.withLocalDeclD `_fn_next contForallType fun fnNext => do
      remId.assign (Lean.mkAppN fnNext newArgFVars)
      let prf1 ← Lean.instantiateMVars g1
      let prf2 := prf1.replace fun sub =>
        if sub.eqv e2 then some e2
        else if sub.eqv e1 then some e2
        else none
      let prfLam ← Lean.Meta.mkLambdaFVars #[fnNext] prf2
      g.assign (Lean.mkApp prfLam gNext)
    let mut gCur := gNext.mvarId!
    for nm in newNames do
      let (_, gCur') ← gCur.intro nm
      gCur := gCur'
    Lean.Elab.Tactic.setGoals (gCur :: savedGoals.tail!)
    let idHvm := Lean.mkIdent `_hvm
    let idHpcm := Lean.mkIdent `_hpcm
    let idHrunm := Lean.mkIdent `_hrunm
    Lean.Elab.Tactic.evalTactic
      (← `(tactic| (
        intro $idHvm:ident $idHpcm:ident $idHrunm:ident
        try refine SepWP.transport_budgetPool $idHvm:ident (hnext := ?_))))

theorem decryptPrekeyClosure_dealloc_ok_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim) := by
  dsimp only [stageP1ProgPlaced, lsProg_518]
  exact ls_hook_ok_ultra_of_mem hdealloc (by decide)

theorem decryptPrekeyClosure_dealloc_ok_ext_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (stageP1ProgPlaced (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim) := by
  obtain ⟨fn, hfn, hsat⟩ := hA
  have hne : Rust.isPanicSymbol "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" = false := by
    simp [Rust.isPanicSymbol]
  exact decryptPrekeyClosure_dealloc_ok_placed ⟨fn, by simp [Rust.withPanics, hne, hfn], hsat⟩

set_option maxHeartbeats 1200000 in
theorem p1_seg1_vregs_wp_ext_placed [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (outPtr coroPtr ctxPtr
    msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr sessStoreVt idStorePtr idStoreVt
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr
    loadShimAddr v_sp0 : BitVec 64)
    (hpc : s.pc = stageP1EntryPlaced)
    (hrun : s.status = .Running)
    (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = outPtr)
    (hx1 : s.readReg64 .x1 = coroPtr)
    (hx2 : s.readReg64 .x2 = ctxPtr) :
    SepWP (stageP1ProgPlaced ext) loadShimAddr s
      (decryptPrekeyCoroInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
        sessStorePtr sessStoreVt idStorePtr idStoreVt
        preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
        kyberStorePtr kyberStoreVt rngPtr ∗
       cells (coroPtr + 0x70#64) 14 ∗
       ((coroPtr + 0x2c0#64) ↦₈ 0#8) ∗
       ((sessStoreVt + 0x18#64) ↦₆₄ᵣ loadShimAddr) ∗
       ((s.sp - 0xcd0#64) ↦₆₄ v_sp0) ∗
       cells (s.sp - 0x60#64) 12)
      (fun s1 P_f =>
        ((P_f ⊢
          decryptPrekeyCoroInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
            sessStorePtr sessStoreVt idStorePtr idStoreVt
            preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
            kyberStorePtr kyberStoreVt rngPtr ∗
          decryptPrekeyCoroCopyAt coroPtr msgPtr remoteAddrPtr localAddrPtr
            sessStorePtr sessStoreVt idStorePtr idStoreVt
            preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
            kyberStorePtr kyberStoreVt rngPtr ∗
          ((coroPtr + 0x2c0#64) ↦₈ 0#8) ∗
          ((sessStoreVt + 0x18#64) ↦₆₄ᵣ loadShimAddr) ∗
          ((s.sp - 0xcd0#64) ↦₆₄ 0#64) ∗
          decryptPrekeySavedRegsAt s.sp s) ∧
        s1.sp = s.sp - 0xcd0#64 ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = sessStorePtr ∧
        s1.readReg64 .x1 = remoteAddrPtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x21 = s.readReg64 .x21 ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = (s.sp - 0xcd0#64) + 0x370#64 ∧
        s1.readReg64 .x25 = (s.sp - 0xcd0#64) + 0x210#64 ∧
        s1.readReg64 .x26 = outPtr ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = (s.sp - 0xcd0#64) + 0xa90#64 ∧
        s1.readReg64 .x29 = s.sp - 0x60#64 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0x130#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        VmPreserved s s1) := by
  have hx0' : s.readReg64 (Reg.gpr 0#5) = outPtr := hx0
  have hx1' : s.readReg64 (Reg.gpr 1#5) = coroPtr := hx1
  have hx2' : s.readReg64 (Reg.gpr 2#5) = ctxPtr := hx2
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hpc ⊢
  dsimp only [decryptPrekeyCoroInitAt]
  conv =>
    arg 4
    simp (config := { maxSteps := 1000000 }) only [
      cells, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub,
      bv_sub_add_lit, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat (refine SepWP.exists_elim fun _ => ?_)
  wp_steps_sync_pool_518 ext loadShimAddr
  refine SepWP.done _hpcm _hrunm ⟨⟨?_,
    by simp_all [arm64_norm], rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩, _hvm⟩
  dsimp only [decryptPrekeyCoroInitAt, decryptPrekeyCoroCopyAt, decryptPrekeySavedRegsAt,
    Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28,
    Reg.x29, Reg.x30]
  exact Entails.of_eq (by sep_ac_rfl)

set_option maxHeartbeats 800000 in
theorem p1_seg5_vregs_wp_ext_placed [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (coroPtr ctxPtr trustFutPtr trustFutVt trustPollAddr u0 u1 u2 : BitVec 64)
    (hpc : s.pc = stageP1EntryPlaced + 0x650#64)
    (hrun : s.status = .Running)
    (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = trustFutPtr)
    (hx1 : s.readReg64 .x1 = trustFutVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr) :
    SepWP (stageP1ProgPlaced ext) trustPollAddr s
      (((coroPtr + 0x398#64) ↦₆₄ u0) ∗
       ((coroPtr + 0x3a0#64) ↦₆₄ u1) ∗
       ((s.sp + 0xc0#64) ↦₆₄ u2) ∗
       ((trustFutVt + 0x18#64) ↦₆₄ᵣ trustPollAddr))
      (fun s1 P_f =>
        ((P_f ⊢
          ((coroPtr + 0x398#64) ↦₆₄ trustFutPtr) ∗
          ((coroPtr + 0x3a0#64) ↦₆₄ trustFutVt) ∗
          ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          ((trustFutVt + 0x18#64) ↦₆₄ᵣ trustPollAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = trustFutPtr ∧
        s1.readReg64 .x1 = ctxPtr ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = s.readReg64 .x21 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0x66c#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        VmPreserved s s1) := by
  have hx0' : s.readReg64 (Reg.gpr 0#5) = trustFutPtr := hx0
  have hx1' : s.readReg64 (Reg.gpr 1#5) = trustFutVt := hx1
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx27' : s.readReg64 (Reg.gpr 27#5) = ctxPtr := hx27
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hpc ⊢
  wp_steps_sync_pool_518 ext trustPollAddr
  refine SepWP.done _hpcm _hrunm ?_
  exact ⟨⟨Entails.of_eq (by sep_ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩, _hvm⟩

set_option maxHeartbeats 1200000 in
theorem p1_seg6a_any_vregs_wp_ext_placed [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (coroPtr outPtr trustFutPtr trustFutVt trustDropAddr
    w_3e0 w_3f0 w_400 w_408 u_a8 u_b0 u_b8 u_c8 u_d0 : BitVec 64)
    (d_3e9 d_3f8 d_3fc : BitVec 32) (h_3ed : BitVec 16) (b_3e8 b_3ef : BitVec 8)
    (hw_ne_neg3 : w_3e0 ≠ 0xfffffffffffffffd#64)
    (hpc : s.pc = stageP1EntryPlaced + 0x66c#64)
    (hrun : s.status = .Running)
    (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hdrop_nz : trustDropAddr ≠ 0#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = coroPtr + 0x390#64)
    (hx26 : s.readReg64 .x26 = outPtr) :
    SepWP (stageP1ProgPlaced ext) trustDropAddr s
      (((coroPtr + 0x398#64) ↦₆₄ trustFutPtr) ∗
       ((coroPtr + 0x3a0#64) ↦₆₄ trustFutVt) ∗
       ((trustFutVt + 0x0#64) ↦₆₄ᵣ trustDropAddr) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((s.sp + 0xc8#64) ↦₆₄ u_c8) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ w_3e0) ∗
       ((s.sp + 0x3e8#64) ↦₈ b_3e8) ∗
       ((s.sp + 0x3e9#64) ↦₃₂ d_3e9) ∗
       ((s.sp + 0x3ed#64) ↦₁₆ h_3ed) ∗
       ((s.sp + 0x3ef#64) ↦₈ b_3ef) ∗
       ((s.sp + 0x3f0#64) ↦₆₄ w_3f0) ∗
       ((s.sp + 0x3f8#64) ↦₃₂ d_3f8) ∗
       ((s.sp + 0x3fc#64) ↦₃₂ d_3fc) ∗
       ((s.sp + 0x400#64) ↦₆₄ w_400) ∗
       ((s.sp + 0x408#64) ↦₆₄ w_408))
      (fun s1 P_f =>
        ((P_f ⊢
          ((coroPtr + 0x398#64) ↦₆₄ trustFutPtr) ∗
          ((coroPtr + 0x3a0#64) ↦₆₄ trustFutVt) ∗
          ((trustFutVt + 0x0#64) ↦₆₄ᵣ trustDropAddr) ∗
          ((s.sp + 0xa8#64) ↦₆₄ d_3fc.zeroExtend 64) ∗
          ((s.sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
          ((s.sp + 0xb8#64) ↦₆₄ w_3f0) ∗
          ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((s.sp + 0xd0#64) ↦₆₄ d_3f8.zeroExtend 64) ∗
          memRegion (s.sp + 0x3e0#64) 48) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = trustFutPtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = w_3e0 ∧
        s1.readReg64 .x21 = trustFutPtr ∧
        s1.readReg64 .x23 = b_3e8.zeroExtend 64 ∧
        s1.readReg64 .x25 = trustFutVt ∧
        s1.readReg64 .x27 = w_408 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0x6d0#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        VmPreserved s s1) := by
  have hcond := cond_ne_adds64_of_ne_neg3_std3 hw_ne_neg3
  have hcond' : (w_3e0 + 3#64 != 0#64) = true := bne_iff_ne.mpr (by bv_omega)
  have hdrop_beq : (trustDropAddr == 0#64) = false := beq_eq_false_iff_ne.mpr hdrop_nz
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = coroPtr + 0x390#64 := hx21
  have hx26' : s.readReg64 (Reg.gpr 26#5) = outPtr := hx26
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hpc ⊢
  wp_steps_sync_pool_518 ext trustDropAddr
  apply SepWP.fold
    (trustOut48_fold_p1 s.sp w_3e0 b_3e8 d_3e9 h_3ed b_3ef w_3f0 d_3f8 d_3fc
      w_400 w_408)
    (by sep_focus)
  refine SepWP.done _hpcm _hrunm ?_
  exact ⟨⟨Entails.of_eq (by sep_ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩, _hvm⟩

set_option maxHeartbeats 1200000 in
theorem p1_post_dealloc_true_vregs_wp_ext_placed [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (coroPtr
    msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt
    u_98 u_a0 : BitVec 64)
    (b_4f2 : BitVec 8)
    (hpc : s.pc = stageP1EntryPlaced + 0x6e4#64)
    (hrun : s.status = .Running)
    (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = 0xfffffffffffffffe#64)
    (hx23 : s.readReg64 .x23 = 1#64) :
    SepWP (stageP1ProgPlaced ext) (stageP1EntryPlaced + 0x868#64) s
      (processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
         idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
         spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
       cells (coroPtr + 0x428#64) 8 ∗
       cells (coroPtr + 0x490#64) 4 ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       ((s.sp + 0x98#64) ↦₆₄ u_98) ∗
       ((s.sp + 0xa0#64) ↦₆₄ u_a0))
      (fun s1 P_f =>
        ((P_f ⊢
          processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
            idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
            spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
          processPrekeyPostTrustAt coroPtr msgPtr remoteAddrPtr localAddrPtr
            idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
            spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
          ((coroPtr + 0x4f2#64) ↦₈ 0#8) ∗
          ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((s.sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64))) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x8 = kyberStorePtr ∧
        s1.readReg64 .x9 = msgPtr ∧
        s1.readReg64 .x10 = kyberStoreVt ∧
        s1.readReg64 .x11 = preKeyStorePtr ∧
        s1.readReg64 .x12 = remoteAddrPtr ∧
        s1.readReg64 .x13 = preKeyStoreVt ∧
        s1.readReg64 .x14 = localAddrPtr ∧
        s1.readReg64 .x15 = idStorePtr ∧
        s1.readReg64 .x16 = idStoreVt ∧
        s1.readReg64 .x17 = coroPtr + 0x4f2#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = 0xfffffffffffffffe#64 ∧
        s1.readReg64 .x22 = spkStorePtr ∧
        s1.readReg64 .x23 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x24 = spkStoreVt ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x28 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        VmPreserved s s1) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = 0xfffffffffffffffe#64 := hx20
  have hx23' : s.readReg64 (Reg.gpr 23#5) = 1#64 := hx23
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hpc ⊢
  dsimp only [processPrekeyInnerInitAt]
  conv =>
    arg 4
    simp (config := { maxSteps := 1000000 }) only [
      cells, BitVec.add_assoc, BitVec.reduceAdd,
      sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat (refine SepWP.exists_elim fun _ => ?_)
  wp_steps_sync_pool_518 ext (blkPl_518.base + 0x868#64)
  refine SepWP.done _hpcm _hrunm ⟨⟨?_,
    by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩, _hvm⟩
  dsimp only [processPrekeyInnerInitAt, processPrekeyPostTrustAt]
  exact Entails.of_eq (by sep_ac_rfl)

set_option maxHeartbeats 800000 in
theorem p1_seg6_dealloc_vregs_wp_ext_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (stageP1ProgPlaced ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (s : State) (coroPtr trustFutPtr trustFutVt w_20 w_23 : BitVec 64)
    (trustBoxSize : Nat)
    (hpc : s.pc = stageP1EntryPlaced + 0x6d0#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hbs_nz : BitVec.ofNat 64 trustBoxSize ≠ 0#64)
    (hbs_lt : trustBoxSize < 2 ^ 64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = w_20)
    (hx21 : s.readReg64 .x21 = trustFutPtr)
    (hx23 : s.readReg64 .x23 = w_23)
    (hx25 : s.readReg64 .x25 = trustFutVt) :
    SepWP (stageP1ProgPlaced ext) (stageP1EntryPlaced + 0x6e4#64) s
      (((trustFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 trustBoxSize) ∗
       ((trustFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.live trustFutPtr trustBoxSize 8 ∗
       memRegion trustFutPtr trustBoxSize ∗
       A.pool lim st s ∗
       stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        let st' := M.stepEvents (rustDeallocEvents trustBoxSize 8) st
        (P_f ⊢
          ((trustFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 trustBoxSize) ∗
          ((trustFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          A.pool lim st' s1 ∗
          stackAt s.sp allocHookStack) ∧
        M.liveBytes st' ≤ M.liveBytes st ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = w_20 ∧
        s1.readReg64 .x23 = w_23 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hbs_beq : (BitVec.ofNat 64 trustBoxSize == 0#64) = false := beq_eq_false_iff_ne.mpr hbs_nz
  have hbs_toNat : (BitVec.ofNat 64 trustBoxSize).toNat = trustBoxSize := Nat.mod_eq_of_lt hbs_lt
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = w_20 := hx20
  have hx21' : s.readReg64 (Reg.gpr 21#5) = trustFutPtr := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = w_23 := hx23
  have hx25' : s.readReg64 (Reg.gpr 25#5) = trustFutVt := hx25
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hdealloc hpc ⊢
  wp_steps_sync_pool_518 ext (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
  wp_call hdealloc (trustFutPtr, trustBoxSize, 8, st)
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by sep_ac_rfl), by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm, AllocCallPreserved],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

set_option maxHeartbeats 1200000 in
theorem p1_seg4_vregs_wp_ext_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (stageP1ProgPlaced ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (s : State) (coroPtr loadFutPtr loadFutVt trustShimAddr
    msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr sessStoreVt idStorePtr idStoreVt
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr : BitVec 64)
    (loadBoxSize : Nat) (b_390 : BitVec 8)
    (hpc : s.pc = stageP1EntryPlaced + 0x238#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hbs_nz : BitVec.ofNat 64 loadBoxSize ≠ 0#64)
    (hbs_lt : loadBoxSize < 2 ^ 64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = loadFutPtr)
    (hx23 : s.readReg64 .x23 = 0xffffffffffffffff#64)
    (hx24 : s.readReg64 .x24 = loadFutVt) :
    SepWP (stageP1ProgPlaced ext) trustShimAddr s
      (((loadFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 loadBoxSize) ∗
       ((loadFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.live loadFutPtr loadBoxSize 8 ∗
       memRegion loadFutPtr loadBoxSize ∗
       A.pool lim st s ∗
       stackAt s.sp allocHookStack ∗
       decryptPrekeyCoroCopyAt coroPtr msgPtr remoteAddrPtr localAddrPtr
         sessStorePtr sessStoreVt idStorePtr idStoreVt
         preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
         kyberStorePtr kyberStoreVt rngPtr ∗
       cells (coroPtr + 0xe0#64) 4 ∗
       cells (coroPtr + 0x2c8#64) 25 ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((idStoreVt + 0x30#64) ↦₆₄ᵣ trustShimAddr))
      (fun s1 P_f =>
        let st' := M.stepEvents (rustDeallocEvents loadBoxSize 8) st
        (P_f ⊢
          ((loadFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 loadBoxSize) ∗
          ((loadFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          A.pool lim st' s1 ∗
          stackAt s.sp allocHookStack ∗
          decryptPrekeyCoroCopyAt coroPtr msgPtr remoteAddrPtr localAddrPtr
            sessStorePtr sessStoreVt idStorePtr idStoreVt
            preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
            kyberStorePtr kyberStoreVt rngPtr ∗
          sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗
          processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
            idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
            spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
          ((coroPtr + 0x390#64) ↦₈ 0#8) ∗
          ((idStoreVt + 0x30#64) ↦₆₄ᵣ trustShimAddr)) ∧
        M.liveBytes st' ≤ M.liveBytes st ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = idStorePtr ∧
        s1.readReg64 .x1 = remoteAddrPtr ∧
        s1.readReg64 .x2 = msgPtr + 0xc8#64 ∧
        s1.readReg64 .x3 = 1#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = coroPtr + 0x390#64 ∧
        s1.readReg64 .x23 = 0#64 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 8#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0x650#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hbs_beq : (BitVec.ofNat 64 loadBoxSize == 0#64) = false := beq_eq_false_iff_ne.mpr hbs_nz
  have hbs_toNat : (BitVec.ofNat 64 loadBoxSize).toNat = loadBoxSize := Nat.mod_eq_of_lt hbs_lt
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = loadFutPtr := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = loadFutVt := hx24
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hdealloc hpc ⊢
  wp_steps_sync_pool_518 ext (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
  wp_call hdealloc (loadFutPtr, loadBoxSize, 8, st)
  dsimp only [decryptPrekeyCoroCopyAt]
  conv =>
    arg 4
    simp (config := { maxSteps := 1000000 }) only [
      cells, BitVec.add_assoc, BitVec.reduceAdd,
      sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat (refine SepWP.exists_elim fun _ => ?_)
  wp_steps_sync_pool_518 ext trustShimAddr
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨?_, by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm, AllocCallPreserved],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩
  dsimp only [decryptPrekeyCoroCopyAt, sessionRecordEmptyHeaderAt, processPrekeyInnerInitAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1StepsXExtPlacedBudgetAux
