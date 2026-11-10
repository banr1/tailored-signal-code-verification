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
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1StepsXExtPlacedBudgetAux
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
# Budget-Threaded Relocatable Stage P1 Segment Helpers — Part 2

Proves `RustCliAllocBudget M` / `VmPreserved` Stage P1 post-`load_session` (`Some(r)`) and
`is_trusted_identity` segment lemmas on Block `518` (`stageP1ProgPlaced ext`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1StepsXExtPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open LibsignalBinary.Heap
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (sepWP_rebase_vmPreserved trapHooks)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (session2MemcpyBudgetSpecX)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1StepsXExtPlacedBudgetAux
  (sepWP_seg_rebase_vm)
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

export LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1StepsXExtPlacedBudgetAux
  (decryptPrekeyClosure_dealloc_ok_placed decryptPrekeyClosure_dealloc_ok_ext_placed
   p1_seg1_vregs_wp_ext_placed p1_seg5_vregs_wp_ext_placed p1_seg6a_any_vregs_wp_ext_placed
   p1_post_dealloc_true_vregs_wp_ext_placed p1_seg6_dealloc_vregs_wp_ext_placed
   p1_seg4_vregs_wp_ext_placed)

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

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

set_option maxHeartbeats 1200000 in
theorem p1_seg3_vregs_wp_ext_placed [LibsignalPlacement]
    (ext : String → Option (State → State))
    (hmemcpy : subroutine_ok (stageP1ProgPlaced ext) (lsρ "memcpy")
      (StoreKit.withLsCodeRoLoaded lsmpl session2MemcpyBudgetSpecX))
    (s : State) (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (coroPtr loadFutPtr loadFutVt loadDropAddr
    w_3e8 w_3f4 w_3fc w_404 w_40c u0 u1 u2 u3 : BitVec 64)
    (d_3f0 d_414 du4 : BitVec 32) (bs312 : List (BitVec 8))
    (hpc : s.pc = stageP1EntryPlaced + 0x14c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hbs312 : bs312.length = 312)
    (hdrop_nz : loadDropAddr ≠ 0#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = s.sp + 0x3e0#64)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) :
    SepWP (stageP1ProgPlaced ext) loadDropAddr s
      (((coroPtr + 0x2c8#64) ↦₆₄ loadFutPtr) ∗
       ((coroPtr + 0x2d0#64) ↦₆₄ loadFutVt) ∗
       ((loadFutVt + 0x0#64) ↦₆₄ᵣ loadDropAddr) ∗
       memRegion (s.sp + 0xd8#64) 312 ∗
       ((s.sp + 0x210#64) ↦₆₄ u0) ∗ ((s.sp + 0x218#64) ↦₆₄ u1) ∗
       ((s.sp + 0x220#64) ↦₆₄ u2) ∗ ((s.sp + 0x228#64) ↦₆₄ u3) ∗
       ((s.sp + 0x230#64) ↦₃₂ du4) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
       ((s.sp + 0x3e8#64) ↦₆₄ w_3e8) ∗
       ((s.sp + 0x3f0#64) ↦₃₂ d_3f0) ∗
       ((s.sp + 0x3f4#64) ↦₆₄ w_3f4) ∗
       ((s.sp + 0x3fc#64) ↦₆₄ w_3fc) ∗
       ((s.sp + 0x404#64) ↦₆₄ w_404) ∗
       ((s.sp + 0x40c#64) ↦₆₄ w_40c) ∗
       ((s.sp + 0x414#64) ↦₃₂ d_414) ∗
       ((s.sp + 0x418#64) ↦ₛ bs312) ∗
       stackAt s.sp extHookStack)
      (fun s1 P_f =>
        ((P_f ⊢
          ((coroPtr + 0x2c8#64) ↦₆₄ loadFutPtr) ∗
          ((coroPtr + 0x2d0#64) ↦₆₄ loadFutVt) ∗
          ((loadFutVt + 0x0#64) ↦₆₄ᵣ loadDropAddr) ∗
          memRegion (s.sp + 0xd8#64) 348 ∗
          memRegion (s.sp + 0x3e0#64) 368 ∗
          stackAt s.sp extHookStack) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = loadFutPtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = loadFutPtr ∧
        s1.readReg64 .x22 = d_3f0.zeroExtend 64 ∧
        s1.readReg64 .x23 = 0xffffffffffffffff#64 ∧
        s1.readReg64 .x24 = loadFutVt ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = w_3e8 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0x238#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        VmPreserved s s1) := by
  have hdrop_beq : (loadDropAddr == 0#64) = false := beq_eq_false_iff_ne.mpr hdrop_nz
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = s.sp + 0x3e0#64 := hx21
  have hx24' : s.readReg64 (Reg.gpr 24#5) = s.sp + 0x370#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hmemcpy hpc ⊢
  apply StoreKit.sepWP_seq_lscro (mid := lsρ "memcpy") hcrl
  wp_steps_sync_pool_518 ext (lsρ "memcpy")
  have hvm1 := _hvm
  refine SepWP.done _hpcm _hrunm fun ⟨hcl_m, hro_m⟩ => ?_
  conv =>
    arg 4
    rw [show memRegion (s.sp + 0xd8#64) 312 =
      memRegion (s.sp + 0xd8#64) bs312.length by rw [hbs312]]
  wp_call hmemcpy (s.sp + 0xd8#64, s.sp + 0x418#64, bs312)
  have hvm2 := hpost
  apply SepWP.fold
    (loadSessionScratch_fold_p1 s.sp 0xffffffffffffffff#64 w_3e8 w_3f4 w_3fc w_404 w_40c
      w_3f4 w_3fc w_404 w_40c d_3f0 d_414 d_414 hbs312)
    (by sep_focus)
  wp_steps_sync_pool_518 ext loadDropAddr
  have hvm3 := _hvm
  refine SepWP.done _hpcm _hrunm ?_
  refine ⟨⟨Entails.of_eq (by sep_ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩,
    hvm1.trans (hvm2.trans hvm3)⟩

set_option maxHeartbeats 1200000 in
theorem p1_load_some_seg3_vregs_wp_ext_placed [LibsignalPlacement]
    (ext : String → Option (State → State))
    (hmemcpy : subroutine_ok (stageP1ProgPlaced ext) (lsρ "memcpy")
      (StoreKit.withLsCodeRoLoaded lsmpl session2MemcpyBudgetSpecX))
    (s : State) (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (coroPtr loadFutPtr loadFutVt loadDropAddr
    w_3e0 w_3e8 w_3f4 w_3fc w_404 w_40c u0 u1 u2 u3 : BitVec 64)
    (d_3f0 d_414 du4 : BitVec 32) (bs312 : List (BitVec 8))
    (hw_ne_neg3 : w_3e0 ≠ 0xfffffffffffffffd#64)
    (hpc : s.pc = stageP1EntryPlaced + 0x14c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hbs312 : bs312.length = 312)
    (hdrop_nz : loadDropAddr ≠ 0#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = s.sp + 0x3e0#64)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) :
    SepWP (stageP1ProgPlaced ext) loadDropAddr s
      (((coroPtr + 0x2c8#64) ↦₆₄ loadFutPtr) ∗
       ((coroPtr + 0x2d0#64) ↦₆₄ loadFutVt) ∗
       ((loadFutVt + 0x0#64) ↦₆₄ᵣ loadDropAddr) ∗
       memRegion (s.sp + 0xd8#64) 312 ∗
       ((s.sp + 0x210#64) ↦₆₄ u0) ∗ ((s.sp + 0x218#64) ↦₆₄ u1) ∗
       ((s.sp + 0x220#64) ↦₆₄ u2) ∗ ((s.sp + 0x228#64) ↦₆₄ u3) ∗
       ((s.sp + 0x230#64) ↦₃₂ du4) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ w_3e0) ∗
       ((s.sp + 0x3e8#64) ↦₆₄ w_3e8) ∗
       ((s.sp + 0x3f0#64) ↦₃₂ d_3f0) ∗
       ((s.sp + 0x3f4#64) ↦₆₄ w_3f4) ∗
       ((s.sp + 0x3fc#64) ↦₆₄ w_3fc) ∗
       ((s.sp + 0x404#64) ↦₆₄ w_404) ∗
       ((s.sp + 0x40c#64) ↦₆₄ w_40c) ∗
       ((s.sp + 0x414#64) ↦₃₂ d_414) ∗
       ((s.sp + 0x418#64) ↦ₛ bs312) ∗
       stackAt s.sp extHookStack)
      (fun s1 P_f =>
        ((P_f ⊢
          ((coroPtr + 0x2c8#64) ↦₆₄ loadFutPtr) ∗
          ((coroPtr + 0x2d0#64) ↦₆₄ loadFutVt) ∗
          ((loadFutVt + 0x0#64) ↦₆₄ᵣ loadDropAddr) ∗
          ((s.sp + 0xd8#64) ↦ₛ bs312) ∗
          ((s.sp + 0x210#64) ↦₆₄ w_3f4) ∗ ((s.sp + 0x218#64) ↦₆₄ w_3fc) ∗
          ((s.sp + 0x220#64) ↦₆₄ w_404) ∗ ((s.sp + 0x228#64) ↦₆₄ w_40c) ∗
          ((s.sp + 0x230#64) ↦₃₂ d_414) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ w_3e0) ∗
          ((s.sp + 0x3e8#64) ↦₆₄ w_3e8) ∗
          ((s.sp + 0x3f0#64) ↦₃₂ d_3f0) ∗
          ((s.sp + 0x3f4#64) ↦₆₄ w_3f4) ∗
          ((s.sp + 0x3fc#64) ↦₆₄ w_3fc) ∗
          ((s.sp + 0x404#64) ↦₆₄ w_404) ∗
          ((s.sp + 0x40c#64) ↦₆₄ w_40c) ∗
          ((s.sp + 0x414#64) ↦₃₂ d_414) ∗
          ((s.sp + 0x418#64) ↦ₛ bs312) ∗
          stackAt s.sp extHookStack) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = loadFutPtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = loadFutPtr ∧
        s1.readReg64 .x22 = d_3f0.zeroExtend 64 ∧
        s1.readReg64 .x23 = w_3e0 ∧
        s1.readReg64 .x24 = loadFutVt ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = w_3e8 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0x238#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        VmPreserved s s1) := by
  have hcond := cond_ne_adds64_of_ne_neg3_std3 hw_ne_neg3
  have hcond' : (w_3e0 + 3#64 != 0#64) = true := bne_iff_ne.mpr (by bv_omega)
  have hdrop_beq : (loadDropAddr == 0#64) = false := beq_eq_false_iff_ne.mpr hdrop_nz
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = s.sp + 0x3e0#64 := hx21
  have hx24' : s.readReg64 (Reg.gpr 24#5) = s.sp + 0x370#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hmemcpy hpc ⊢
  apply StoreKit.sepWP_seq_lscro (mid := lsρ "memcpy") hcrl
  wp_steps_sync_pool_518 ext (lsρ "memcpy")
  have hvm1 := _hvm
  refine SepWP.done _hpcm _hrunm fun ⟨hcl_m, hro_m⟩ => ?_
  conv =>
    arg 4
    rw [show memRegion (s.sp + 0xd8#64) 312 =
      memRegion (s.sp + 0xd8#64) bs312.length by rw [hbs312]]
  wp_call hmemcpy (s.sp + 0xd8#64, s.sp + 0x418#64, bs312)
  have hvm2 := hpost
  wp_steps_sync_pool_518 ext loadDropAddr
  have hvm3 := _hvm
  refine SepWP.done _hpcm _hrunm ?_
  refine ⟨⟨Entails.of_eq (by sep_ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩,
    hvm1.trans (hvm2.trans hvm3)⟩

set_option maxHeartbeats 1200000 in
theorem p1_load_some_seg4_vregs_wp_ext_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (stageP1ProgPlaced ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : subroutine_ok (stageP1ProgPlaced ext) (lsρ "memcpy")
      (StoreKit.withLsCodeRoLoaded lsmpl session2MemcpyBudgetSpecX))
    (s : State) (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (coroPtr loadFutPtr loadFutVt trustShimAddr
    msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr sessStoreVt idStorePtr idStoreVt
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr
    w_3e0 w_3e8 v_210 v_218 v_220 v_228
    c0 c1 c_f4 c_fc c_104 c_10c : BitVec 64)
    (d_3f0 dv_230 c_f0 c_114 : BitVec 32)
    (bs312 : List (BitVec 8))
    (loadBoxSize : Nat) (b_390 : BitVec 8)
    (hw_ne_neg2 : w_3e0 ≠ 0xfffffffffffffffe#64)
    (hw_ne_neg1 : w_3e0 ≠ 0xffffffffffffffff#64)
    (hbs312 : bs312.length = 312)
    (hpc : s.pc = stageP1EntryPlaced + 0x238#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hbs_nz : BitVec.ofNat 64 loadBoxSize ≠ 0#64)
    (hbs_lt : loadBoxSize < 2 ^ 64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = loadFutPtr)
    (hx22 : s.readReg64 .x22 = d_3f0.zeroExtend 64)
    (hx23 : s.readReg64 .x23 = w_3e0)
    (hx24 : s.readReg64 .x24 = loadFutVt)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx28 : s.readReg64 .x28 = w_3e8) :
    SepWP (stageP1ProgPlaced ext) trustShimAddr s
      (((loadFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 loadBoxSize) ∗
       ((loadFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.live loadFutPtr loadBoxSize 8 ∗
       memRegion loadFutPtr loadBoxSize ∗
       A.pool lim st s ∗
       stackAt s.sp extHookStack ∗
       decryptPrekeyCoroCopyAt coroPtr msgPtr remoteAddrPtr localAddrPtr
         sessStorePtr sessStoreVt idStorePtr idStoreVt
         preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
         kyberStorePtr kyberStoreVt rngPtr ∗
       ((coroPtr + 0xe0#64) ↦₆₄ c0) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ c1) ∗
       ((coroPtr + 0xf0#64) ↦₃₂ c_f0) ∗
       ((coroPtr + 0xf4#64) ↦₆₄ c_f4) ∗
       ((coroPtr + 0xfc#64) ↦₆₄ c_fc) ∗
       ((coroPtr + 0x104#64) ↦₆₄ c_104) ∗
       ((coroPtr + 0x10c#64) ↦₆₄ c_10c) ∗
       ((coroPtr + 0x114#64) ↦₃₂ c_114) ∗
       memRegion (coroPtr + 0x118#64) 312 ∗
       ((s.sp + 0xd8#64) ↦ₛ bs312) ∗
       ((s.sp + 0x210#64) ↦₆₄ v_210) ∗
       ((s.sp + 0x218#64) ↦₆₄ v_218) ∗
       ((s.sp + 0x220#64) ↦₆₄ v_220) ∗
       ((s.sp + 0x228#64) ↦₆₄ v_228) ∗
       ((s.sp + 0x230#64) ↦₃₂ dv_230) ∗
       cells (coroPtr + 0x2c8#64) 25 ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((idStoreVt + 0x30#64) ↦₆₄ᵣ trustShimAddr))
      (fun s1 P_f =>
        let st' := M.stepEvents (rustDeallocEvents loadBoxSize 8) st
        (P_f ⊢
          ((loadFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 loadBoxSize) ∗
          ((loadFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          A.pool lim st' s1 ∗
          stackAt s.sp extHookStack ∗
          decryptPrekeyCoroCopyAt coroPtr msgPtr remoteAddrPtr localAddrPtr
            sessStorePtr sessStoreVt idStorePtr idStoreVt
            preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
            kyberStorePtr kyberStoreVt rngPtr ∗
          ((coroPtr + 0xe0#64) ↦₆₄ w_3e0) ∗
          ((coroPtr + 0xe8#64) ↦₆₄ w_3e8) ∗
          ((coroPtr + 0xf0#64) ↦₃₂ d_3f0) ∗
          ((coroPtr + 0xf4#64) ↦₆₄ v_210) ∗
          ((coroPtr + 0xfc#64) ↦₆₄ v_218) ∗
          ((coroPtr + 0x104#64) ↦₆₄ v_220) ∗
          ((coroPtr + 0x10c#64) ↦₆₄ v_228) ∗
          ((coroPtr + 0x114#64) ↦₃₂ dv_230) ∗
          ((coroPtr + 0x118#64) ↦ₛ bs312) ∗
          ((s.sp + 0xd8#64) ↦ₛ bs312) ∗
          ((s.sp + 0x210#64) ↦₆₄ v_210) ∗
          ((s.sp + 0x218#64) ↦₆₄ v_218) ∗
          ((s.sp + 0x220#64) ↦₆₄ v_220) ∗
          ((s.sp + 0x228#64) ↦₆₄ v_228) ∗
          ((s.sp + 0x230#64) ↦₃₂ dv_230) ∗
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
        s1.readReg64 .x23 = w_3e0 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = w_3e8 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0x650#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hstk_split := stackAt_split_of_le s.sp extHookStack allocHookStack (by decide) (by decide)
  have hcond_neg2 := cond_ne_adds64_of_ne_neg2_std3 hw_ne_neg2
  have hcond_neg1 := cond_eq_adds64_of_ne_neg1_std3 hw_ne_neg1
  have hcond_neg2' : (w_3e0 + 2#64 != 0#64) = true := bne_iff_ne.mpr (by bv_omega)
  have hcond_neg1' : (w_3e0 + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr (by bv_omega)
  have hbs_beq : (BitVec.ofNat 64 loadBoxSize == 0#64) = false := beq_eq_false_iff_ne.mpr hbs_nz
  have hbs_toNat : (BitVec.ofNat 64 loadBoxSize).toNat = loadBoxSize := Nat.mod_eq_of_lt hbs_lt
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = loadFutPtr := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = d_3f0.zeroExtend 64 := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = w_3e0 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = loadFutVt := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx28' : s.readReg64 (Reg.gpr 28#5) = w_3e8 := hx28
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hdealloc hmemcpy hpc ⊢
  apply StoreKit.sepWP_seq_lscro (mid := lsρ "memcpy") hcrl
  apply SepWP.fold (Entails.of_eq hstk_split) (by sep_focus)
  wp_simp_pre [sepConj_assoc]
  wp_steps_sync_pool_518 ext (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
  wp_call hdealloc (loadFutPtr, loadBoxSize, 8, st)
  apply SepWP.fold (Entails.of_eq hstk_split.symm) (by sep_focus)
  wp_simp_pre [sepConj_assoc]
  wp_steps_sync_pool_518 ext (lsρ "memcpy")
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) fun ⟨hcl_m, hro_m⟩ => ?_
  conv =>
    arg 4
    rw [show memRegion (coroPtr + 0x118#64) 312 =
      memRegion (coroPtr + 0x118#64) bs312.length by rw [hbs312]]
  wp_call hmemcpy (coroPtr + 0x118#64, s.sp + 0xd8#64, bs312)
  refine SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
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
  dsimp only [decryptPrekeyCoroCopyAt, processPrekeyInnerInitAt]
  simp only [hsp_sf, sepConj_assoc]
  exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1StepsXExtPlacedBudget
