/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1StepsXExtPlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1TrustExtPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedExtPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlacedBudget
public import LibsignalBinary.Proofs.Common.StringClonePlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import Lean.Elab.Tactic -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedAux
import LibsignalBinary.Proofs.E2E.Bin.Hooks
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.PublicApi.StoreKit.RecordMove
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Stage P1 Untrusted-Identity Segment Helpers

Placed `<String as Clone>::clone` bridge and `VmPreserved` instruction-segment lemmas (`+0x6e4 →
stringClone → +0x3588 → +0x359c → retAddr`) for the untrusted-identity exit on Block `518`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedExtPlacedBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees hiding
  dropSessionStructureLocal2Spec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.Pf.RecordMove
open CryptoVerification.LibsignalPublicApi.MessageDecrypt hiding lsStringCloneSym
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegTrust
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
  RustCliAllocBudget VmPreserved allocMemcpyVmSpec rustCliAllocBudgetSpec
  rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (
  rustAllocShimVmSpec stringCloneBudgetSpec
)
open LibsignalBinary.Proofs.Common.StringClonePlaced (
  lsRustAllocPlacedSym lsRustNoAllocShimPlacedSym
)
open LibsignalBinary.Proofs.Common.StringClonePlacedBudget (
  stringCloneBudget_placed_codeLoaded_ok stringCloneBudget_placed_panics_codeLoaded_ok
  stringCloneBudget_placed_panics_vm_codeLoaded_ok stringCloneBudget_placed_vm_codeLoaded_ok
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec
)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (sepWP_rebase_vmPreserved trapHooks)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1StepsXExtPlacedBudgetAux (
  sepWP_seg_rebase_vm
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1LoadTrustTailsXExtPlacedBudget (
  bind_sepWP_steps_frame_placed ret_sepWP_steps_frame_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedExtPlaced (
  lsStringCloneSym call_lscro_nopanic_steps_frame_placed
)

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero
attribute [local simp, local wp_norm, local arm64_norm] bfi_mask_lsr8_id evalBitfield_bfi_lsr8
attribute [local simp] extractLsb_hi_lo_append

local elab "wp_steps_sync_pool_518_tac " tac:tacticSeq mid:term : tactic => do
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
      ($tac)
      refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        ⟨by first | rfl | simp only [wp_norm, arm64_norm], ?_⟩)))
    let rem ← Lean.Elab.Tactic.getGoals
    let [remId] := rem
      | throwError "wp_steps_sync_pool_518_tac: expected 1 continuation goal, got {rem.length}"
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

local macro "wp_steps_sync_pool_518 " _ext:term:max mid:term : tactic =>
  `(tactic| wp_steps_sync_pool_518_tac (wp_steps) $mid)

theorem decryptPrekeyClosure_stringClone_ok_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hShim : HookSat ext lsRustNoAllocShimPlacedSym sessionShimBudgetSpec)
    (hAlloc : HookSat ext lsRustAllocPlacedSym (rustCliAllocBudgetSpec M A lim false))
    (hMemcpy : HookSat ext "memcpy" sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 623) (StoreKit.withLsCodeRoLoaded lsmpl (stringCloneBudgetSpec M A lim)) :=
  StoreKit.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (stringCloneBudget_placed_codeLoaded_ok
      (callerProg := stageP1ProgPlaced ext) (i := 518) hShim hAlloc hMemcpy (by decide))

theorem decryptPrekeyClosure_stringClone_ok_ext_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hShim : HookSat ext lsRustNoAllocShimPlacedSym sessionShimBudgetSpec)
    (hAlloc : HookSat ext lsRustAllocPlacedSym (rustCliAllocBudgetSpec M A lim false))
    (hMemcpy : HookSat ext "memcpy" sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (stageP1ProgPlaced (Rust.withPanics ext))
      (lsmpl.base 623) (StoreKit.withLsCodeRoLoaded lsmpl (stringCloneBudgetSpec M A lim)) :=
  StoreKit.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (stringCloneBudget_placed_panics_codeLoaded_ok
      (callerProg := stageP1ProgPlaced (Rust.withPanics ext)) (i := 518)
      hShim hAlloc hMemcpy (by decide))

theorem decryptPrekeyClosure_stringClone_vm_ok_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hShim : HookSat ext lsRustNoAllocShimPlacedSym rustAllocShimVmSpec)
    (hAlloc : HookSat ext lsRustAllocPlacedSym (rustCliAllocBudgetSpec M A lim false))
    (hMemcpy : HookSat ext "memcpy" allocMemcpyVmSpec) :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 623) (StoreKit.withLsCodeRoLoaded lsmpl (stringCloneBudgetSpec M A lim)) :=
  StoreKit.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (stringCloneBudget_placed_vm_codeLoaded_ok
      (callerProg := stageP1ProgPlaced ext) (i := 518) hShim hAlloc hMemcpy (by decide))

theorem decryptPrekeyClosure_stringClone_vm_ok_ext_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hShim : HookSat ext lsRustNoAllocShimPlacedSym rustAllocShimVmSpec)
    (hAlloc : HookSat ext lsRustAllocPlacedSym (rustCliAllocBudgetSpec M A lim false))
    (hMemcpy : HookSat ext "memcpy" allocMemcpyVmSpec) :
    subroutine_ok (stageP1ProgPlaced (Rust.withPanics ext))
      (lsmpl.base 623) (StoreKit.withLsCodeRoLoaded lsmpl (stringCloneBudgetSpec M A lim)) :=
  StoreKit.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (stringCloneBudget_placed_panics_vm_codeLoaded_ok
      (callerProg := stageP1ProgPlaced (Rust.withPanics ext)) (i := 518)
      hShim hAlloc hMemcpy (by decide))

set_option maxHeartbeats 400000 in
theorem p1_err_drop_none_vregs_wp_ext_placed [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (coroPtr : BitVec 64)
    (hpc : s.pc = stageP1EntryPlaced + 0x3588#64)
    (hrun : s.status = .Running)
    (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (stageP1ProgPlaced ext) (stageP1EntryPlaced + 0x359c#64) s
      (((coroPtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64))
      (fun s1 P_f =>
        (P_f ⊢ ((coroPtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        VmPreserved s s1) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hpc ⊢
  wp_steps_sync_pool_518 ext (blkPl_518.base + 0x359c#64)
  refine SepWP.done _hpcm _hrunm ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], _hvm⟩

set_option maxHeartbeats 400000 in
theorem p1_err_drop_ss_to_call_vregs_wp_ext_placed [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (coroPtr ssCap : BitVec 64)
    (hcap_ne : ssCap ≠ 0xffffffffffffffff#64)
    (hpc : s.pc = stageP1EntryPlaced + 0x3588#64)
    (hrun : s.status = .Running)
    (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (stageP1ProgPlaced ext) (lsmpl.base 512) s
      (((coroPtr + 0xf8#64) ↦₆₄ ssCap))
      (fun s1 P_f =>
        (P_f ⊢ ((coroPtr + 0xf8#64) ↦₆₄ ssCap)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0xf8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0x359c#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        VmPreserved s s1) := by
  have hcond_cap := cond_eq_adds64_of_ne_neg1_std3 hcap_ne
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hpc ⊢
  wp_steps_sync_pool_518 ext (lsmpl.base 512)
  refine SepWP.done _hpcm _hrunm ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm], _hvm⟩

set_option maxHeartbeats 800000 in
theorem p1_untrusted_to_clone_vregs_wp_ext_placed [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (coroPtr remoteAddrPtr : BitVec 64)
    (hpc : s.pc = stageP1EntryPlaced + 0x6e4#64)
    (hrun : s.status = .Running)
    (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = 0xfffffffffffffffe#64)
    (hx23 : s.readReg64 .x23 = 0#64) :
    SepWP (stageP1ProgPlaced ext) (lsmpl.base 623) s
      (((coroPtr + 0x330#64) ↦₆₄ remoteAddrPtr))
      (fun s1 P_f =>
        (P_f ⊢ ((coroPtr + 0x330#64) ↦₆₄ remoteAddrPtr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = remoteAddrPtr ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = remoteAddrPtr ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0x7e8#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        VmPreserved s s1) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = 0xfffffffffffffffe#64 := hx20
  have hx23' : s.readReg64 (Reg.gpr 23#5) = 0#64 := hx23
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hpc ⊢
  wp_steps_sync_pool_518 ext (lsmpl.base 623)
  refine SepWP.done _hpcm _hrunm ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], _hvm⟩

private theorem vmPreserved_trans_write_setPC {s sm s1 : State} {r : Reg} {v pc : BitVec 64}
    (h1 : VmPreserved s sm) (h2 : VmPreserved ((sm.writeReg64 r v).setPC pc) s1) :
    VmPreserved s s1 :=
  have h1' : VmPreserved s ((sm.writeReg64 r v).setPC pc) := by
    simp only [wp_norm, arm64_norm]; exact h1
  h1'.trans h2

set_option maxHeartbeats 1600000 in
theorem p1_untrusted_post_clone_vregs_wp_ext_placed [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (coroPtr remoteAddrPtr outPtr cap ptr len devWord
    u_250 u_258 u_260 u_268 u_270 u_278
    u_a90 u_a98 u_aa0 u_aa8 u_ab0 u_ab8
    u_370 u_378 u_380 u_388 : BitVec 64)
    (u_390 : BitVec 32)
    (d0 b_390 : BitVec 8)
    (peer : AddrGhost) (pad : List (BitVec 8))
    (hw4 : peer.device :: pad = unpack64 devWord)
    (hpc : s.pc = stageP1EntryPlaced + 0x7e8#64)
    (hrun : s.status = .Running)
    (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = remoteAddrPtr)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) :
    SepWP (stageP1ProgPlaced ext) (stageP1EntryPlaced + 0x3588#64) s
      (((remoteAddrPtr + 0x18#64) ↦₈ peer.device) ∗
       ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       FromRecordCallees.lsLogOff ∗
       ((s.sp + 0x3e0#64) ↦₆₄ cap) ∗
       ((s.sp + 0x3e8#64) ↦₆₄ ptr) ∗
       ((s.sp + 0x3f0#64) ↦₃₂ len.extractLsb' 0 32) ∗
       ((s.sp + 0x3f4#64) ↦₃₂ len.extractLsb' 32 32) ∗
       ((s.sp + 0x3f8#64) ↦₈ d0) ∗
       ((s.sp + 0x3f9#64) ↦ₛ pad) ∗
       ((coroPtr + 0x250#64) ↦₆₄ u_250) ∗
       ((coroPtr + 0x258#64) ↦₆₄ u_258) ∗
       ((coroPtr + 0x260#64) ↦₆₄ u_260) ∗
       ((coroPtr + 0x268#64) ↦₆₄ u_268) ∗
       ((coroPtr + 0x270#64) ↦₆₄ u_270) ∗
       ((coroPtr + 0x278#64) ↦₆₄ u_278) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((s.sp + 0xa90#64) ↦₆₄ u_a90) ∗
       ((s.sp + 0xa98#64) ↦₆₄ u_a98) ∗
       ((s.sp + 0xaa0#64) ↦₆₄ u_aa0) ∗
       ((s.sp + 0xaa8#64) ↦₆₄ u_aa8) ∗
       ((s.sp + 0xab0#64) ↦₆₄ u_ab0) ∗
       ((s.sp + 0xab8#64) ↦₆₄ u_ab8) ∗
       ((s.sp + 0x370#64) ↦₆₄ u_370) ∗
       ((s.sp + 0x378#64) ↦₆₄ u_378) ∗
       ((s.sp + 0x380#64) ↦₆₄ u_380) ∗
       ((s.sp + 0x388#64) ↦₆₄ u_388) ∗
       ((s.sp + 0x390#64) ↦₃₂ u_390))
      (fun s1 P_f =>
        (P_f ⊢
          ((remoteAddrPtr + 0x18#64) ↦₈ peer.device) ∗
          ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
          FromRecordCallees.lsLogOff ∗
          ((s.sp + 0x3e0#64) ↦₆₄ cap) ∗
          ((s.sp + 0x3e8#64) ↦₆₄ ptr) ∗
          ((s.sp + 0x3f0#64) ↦₃₂ len.extractLsb' 0 32) ∗
          ((s.sp + 0x3f4#64) ↦₃₂ len.extractLsb' 32 32) ∗
          ((s.sp + 0x3f8#64) ↦₆₄ devWord) ∗
          ((coroPtr + 0x250#64) ↦₆₄ 0x800000000000000c#64) ∗
          ((coroPtr + 0x258#64) ↦₆₄ cap) ∗
          ((coroPtr + 0x260#64) ↦₆₄ ptr) ∗
          ((coroPtr + 0x268#64) ↦₆₄ len) ∗
          ((coroPtr + 0x270#64) ↦₆₄ devWord) ∗
          ((coroPtr + 0x278#64) ↦₆₄ s.readReg64 .x27) ∗
          ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
          ((s.sp + 0xa90#64) ↦₆₄ 0x800000000000000c#64) ∗
          ((s.sp + 0xa98#64) ↦₃₂ cap.extractLsb' 0 32) ∗
          ((s.sp + 0xa9c#64) ↦₆₄ (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)) ∗
          ((s.sp + 0xaa4#64) ↦₆₄ (len.extractLsb' 0 32 ++ ptr.extractLsb' 32 32)) ∗
          ((s.sp + 0xaac#64) ↦₆₄ (devWord.extractLsb' 0 32 ++ len.extractLsb' 32 32)) ∗
          ((s.sp + 0xab4#64) ↦₆₄ ((s.readReg64 .x27).extractLsb' 0 32 ++ devWord.extractLsb' 32 32)) ∗
          ((s.sp + 0xabc#64) ↦₃₂ (s.readReg64 .x27).extractLsb' 32 32) ∗
          ((s.sp + 0x370#64) ↦₆₄ (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)) ∗
          ((s.sp + 0x378#64) ↦₆₄ (len.extractLsb' 0 32 ++ ptr.extractLsb' 32 32)) ∗
          ((s.sp + 0x380#64) ↦₆₄ (devWord.extractLsb' 0 32 ++ len.extractLsb' 32 32)) ∗
          ((s.sp + 0x388#64) ↦₆₄ ((s.readReg64 .x27).extractLsb' 0 32 ++ devWord.extractLsb' 32 32)) ∗
          ((s.sp + 0x390#64) ↦₃₂ (s.readReg64 .x27).extractLsb' 32 32)) ∧
        VmPreserved s s1 ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = (cap.extractLsb' 0 32).zeroExtend 64 ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = outPtr ∧
        s1.readReg64 .x28 = 0x800000000000000c#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hdev_pack := SegUntrusted.pointsTo64_of_cons_unpack64 (s.sp + 0x3f8#64) peer.device pad devWord hw4
  try simp only [BitVec.add_assoc] at hdev_pack; try simp only [BitVec.reduceAdd] at hdev_pack
  have hrealign_a98 := realign_40 (s.sp + 0xa98#64) cap ptr len devWord (s.readReg64 .x27)
  try simp only [BitVec.add_assoc] at hrealign_a98; try simp only [BitVec.reduceAdd] at hrealign_a98
  have hcond_err : ConditionHolds CondCode.NE (addsPState64 0x800000000000000c#64 2#64) = true :=
    cond_ne_adds64_of_ne_neg2_std3 (by decide)
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = remoteAddrPtr := hx21
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  dsimp only [stageP1ProgPlaced, lsProg_518, stageP1EntryPlaced, FromRecordCallees.lsLogOff,
    lsLogFilterAddr] at hpc ⊢
  wp_steps_sync_pool_518_tac (
    apply SepWP.fold (Entails.of_eq (coro_268_split32 coroPtr u_268)) (by sep_focus)
    wp_simp_pre [sepConj_assoc]
    wp_steps
    apply SepWP.fold (Entails.of_eq hdev_pack) (by sep_focus)
    wp_simp_pre [sepConj_assoc]
    wp_steps
    apply SepWP.fold (Entails.of_eq (coro_268_split32 coroPtr len).symm) (by sep_focus)
    wp_simp_pre [sepConj_assoc]
    wp_steps
  ) (blkPl_518.base + 0x17bc#64)
  have hvm_mid := _hvm
  have hrun_mid := _hrunm
  wp_step
  clear _hvm _hpcm _hrunm
  wp_steps_sync_pool_518_tac (
    wp_steps
    apply SepWP.fold (Entails.of_eq hrealign_a98) (by sep_focus)
    wp_simp_pre [sepConj_assoc]
    wp_steps
  ) (blkPl_518.base + 0x3588#64)
  refine SepWP.done _hpcm _hrunm
    ⟨Entails.of_eq (by ac_rfl),
     vmPreserved_trans_write_setPC hvm_mid _hvm,
     by simp_all [arm64_norm], by simp_all [arm64_norm],
     by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
     by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
     by simp_all [arm64_norm]⟩

set_option maxHeartbeats 800000 in
theorem p3_err_tail_b_vregs_wp_ext_placed [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (coroPtr outPtr errTag prevStatesPtr
    w_370 w_378 w_380 w_388 u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
    savedX19 savedX20 savedX21 savedX22 savedX23 savedX24
    savedX25 savedX26 savedX27 savedX28 savedX29 retAddr : BitVec 64)
    (w_22 w_390 u_ret08 u_ret2c : BitVec 32) (b_2c0 : BitVec 8)
    (hpc : s.pc = stageP1EntryPlaced + 0x359c#64)
    (hrun : s.status = .Running) (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx22 : s.readReg64 .x22 = w_22.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag) :
    SepWP (stageP1ProgPlaced ext) retAddr s
      (((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((outPtr + 0x0#64) ↦₆₄ u_ret0) ∗ ((outPtr + 0x8#64) ↦₃₂ u_ret08) ∗
       ((outPtr + 0xc#64) ↦₆₄ u_ret0c) ∗ ((outPtr + 0x14#64) ↦₆₄ u_ret14) ∗
       ((outPtr + 0x1c#64) ↦₆₄ u_ret1c) ∗ ((outPtr + 0x24#64) ↦₆₄ u_ret24) ∗
       ((outPtr + 0x2c#64) ↦₃₂ u_ret2c) ∗
       ((s.sp + 0x370#64) ↦₆₄ w_370) ∗ ((s.sp + 0x378#64) ↦₆₄ w_378) ∗
       ((s.sp + 0x380#64) ↦₆₄ w_380) ∗ ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
       ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
       ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗ ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
       ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
       ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗ ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
       ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗ ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
       ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
       ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗ ((s.sp + 0xcc8#64) ↦₆₄ savedX19))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
          ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          ((outPtr + 0x0#64) ↦₆₄ errTag) ∗ ((outPtr + 0x8#64) ↦₃₂ w_22) ∗
          ((outPtr + 0xc#64) ↦₆₄ w_370) ∗ ((outPtr + 0x14#64) ↦₆₄ w_378) ∗
          ((outPtr + 0x1c#64) ↦₆₄ w_380) ∗ ((outPtr + 0x24#64) ↦₆₄ w_388) ∗
          ((outPtr + 0x2c#64) ↦₃₂ w_390) ∗
          ((s.sp + 0x370#64) ↦₆₄ w_370) ∗ ((s.sp + 0x378#64) ↦₆₄ w_378) ∗
          ((s.sp + 0x380#64) ↦₆₄ w_380) ∗ ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
          ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
          ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗ ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
          ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
          ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗ ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
          ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗ ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
          ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
          ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗ ((s.sp + 0xcc8#64) ↦₆₄ savedX19)) ∧
        s1.sp = s.sp + 0xcd0#64 ∧ s1.trace = s.trace ∧
        s1.readReg64 .x19 = savedX19 ∧ s1.readReg64 .x20 = savedX20 ∧
        s1.readReg64 .x21 = savedX21 ∧ s1.readReg64 .x22 = savedX22 ∧
        s1.readReg64 .x23 = savedX23 ∧ s1.readReg64 .x24 = savedX24 ∧
        s1.readReg64 .x25 = savedX25 ∧ s1.readReg64 .x26 = savedX26 ∧
        s1.readReg64 .x27 = savedX27 ∧ s1.readReg64 .x28 = savedX28 ∧
        s1.readReg64 .x29 = savedX29 ∧ s1.readReg64 .x30 = retAddr ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        VmPreserved s s1) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = w_22.zeroExtend 64 := hx22
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = outPtr := hx26
  have hx28' : s.readReg64 (Reg.gpr 28#5) = errTag := hx28
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hpc ⊢
  wp_steps_sync_pool_518 ext retAddr
  refine SepWP.done _hpcm _hrunm ?_
  refine ⟨Entails.of_eq (by simp only [BitVec.add_zero]),
    by simp_all [arm64_norm], rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], _hvm⟩

set_option maxHeartbeats 1200000 in
theorem p1_err_tail_prev_dealloc_core_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (stageP1ProgPlaced ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (s : State) (coroPtr outPtr errTag prevCap prevPtr
    w_370 w_378 w_380 w_388 u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
    savedX19 savedX20 savedX21 savedX22 savedX23 savedX24
    savedX25 savedX26 savedX27 savedX28 savedX29 retAddr : BitVec 64)
    (w_22 w_390 u_ret08 u_ret2c : BitVec 32) (b_2c0 : BitVec 8)
    (hcap_nz : prevCap ≠ 0#64) (hcap_lt : prevCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = stageP1EntryPlaced + 0x359c#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx22 : s.readReg64 .x22 = w_22.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag) :
    SepWP (stageP1ProgPlaced ext) retAddr s
      (((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ A.live prevPtr (prevCap.toNat * 24) 8 ∗
       memRegion prevPtr (prevCap.toNat * 24) ∗ A.pool lim st s ∗ stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((outPtr + 0x0#64) ↦₆₄ u_ret0) ∗ ((outPtr + 0x8#64) ↦₃₂ u_ret08) ∗
       ((outPtr + 0xc#64) ↦₆₄ u_ret0c) ∗ ((outPtr + 0x14#64) ↦₆₄ u_ret14) ∗
       ((outPtr + 0x1c#64) ↦₆₄ u_ret1c) ∗ ((outPtr + 0x24#64) ↦₆₄ u_ret24) ∗
       ((outPtr + 0x2c#64) ↦₃₂ u_ret2c) ∗
       ((s.sp + 0x370#64) ↦₆₄ w_370) ∗ ((s.sp + 0x378#64) ↦₆₄ w_378) ∗
       ((s.sp + 0x380#64) ↦₆₄ w_380) ∗ ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
       ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
       ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗ ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
       ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
       ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗ ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
       ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗ ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
       ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
       ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗ ((s.sp + 0xcc8#64) ↦₆₄ savedX19))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
          ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
          A.pool lim (M.stepEvents (rustDeallocEvents (prevCap.toNat * 24) 8) st) s1 ∗
          stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          ((outPtr + 0x0#64) ↦₆₄ errTag) ∗ ((outPtr + 0x8#64) ↦₃₂ w_22) ∗
          ((outPtr + 0xc#64) ↦₆₄ w_370) ∗ ((outPtr + 0x14#64) ↦₆₄ w_378) ∗
          ((outPtr + 0x1c#64) ↦₆₄ w_380) ∗ ((outPtr + 0x24#64) ↦₆₄ w_388) ∗
          ((outPtr + 0x2c#64) ↦₃₂ w_390) ∗
          ((s.sp + 0x370#64) ↦₆₄ w_370) ∗ ((s.sp + 0x378#64) ↦₆₄ w_378) ∗
          ((s.sp + 0x380#64) ↦₆₄ w_380) ∗ ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
          ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
          ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗ ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
          ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
          ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗ ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
          ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗ ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
          ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
          ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗ ((s.sp + 0xcc8#64) ↦₆₄ savedX19)) ∧
        s1.sp = s.sp + 0xcd0#64 ∧ s1.trace = s.trace ∧
        s1.readReg64 .x19 = savedX19 ∧ s1.readReg64 .x20 = savedX20 ∧
        s1.readReg64 .x21 = savedX21 ∧ s1.readReg64 .x22 = savedX22 ∧
        s1.readReg64 .x23 = savedX23 ∧ s1.readReg64 .x24 = savedX24 ∧
        s1.readReg64 .x25 = savedX25 ∧ s1.readReg64 .x26 = savedX26 ∧
        s1.readReg64 .x27 = savedX27 ∧ s1.readReg64 .x28 = savedX28 ∧
        s1.readReg64 .x29 = savedX29 ∧ s1.readReg64 .x30 = retAddr ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hcap_beq : (prevCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_nz
  have hmul1 : 24#64 * prevCap = BitVec.ofNat 64 (prevCap.toNat * 24) := by bv_omega
  have hmul2 : prevCap * 24#64 = BitVec.ofNat 64 (prevCap.toNat * 24) := by bv_omega
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = w_22.zeroExtend 64 := hx22
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = outPtr := hx26
  have hx28' : s.readReg64 (Reg.gpr 28#5) = errTag := hx28
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hdealloc hpc ⊢
  wp_steps_sync_pool_518 ext (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
  wp_call hdealloc (prevPtr, prevCap.toNat * 24, 8, st)
  wp_steps_sync_pool_518 ext retAddr
  refine SepWP.done _hpcm _hrunm ?_
  refine ⟨Entails.of_eq (by simp only [BitVec.add_zero, arm64_norm]; sep_ac_rfl),
    by simp_all [arm64_norm], by simp_all [arm64_norm, AllocCallPreserved],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

set_option maxHeartbeats 1200000 in
theorem p1_err_drop_record_core_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st0 : M.σ}
    {ext : String → Option (State → State)}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Qp : State → SepProp → Prop}
    (hdrop_ss : subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 512)
      (StoreKit.withLsCodeRoLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (opt : Option (SessionRecord (List (BitVec 8))))
    (s : State) (coroPtr : BitVec 64)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = stageP1EntryPlaced + 0x3588#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWPp (stageP1ProgPlaced ext)
      (stageP1EntryPlaced + 0x359c#64) s
      (p1LoadedRecordAt Scope A.repAlloc coroPtr opt ∗
       A.pool lim st0 s ∗
       stackAt s.sp dropSessionStructureLocal2Stack)
      (fun s2 P_m =>
        (∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (P_m ⊢
            ∃∗ prevCap : BitVec 64, ∃∗ prevPtr : BitVec 64,
              ⌜prevCap.toNat * 24 < 2 ^ 63⌝ ∗
              ((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗
              ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
              ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
              (if prevCap = 0 then emp
               else A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24)) ∗
              memRegion (coroPtr + 0xf8#64) 344 ∗
              A.pool lim (M.stepEvents evs st0) s2 ∗
              stackAt s.sp dropSessionStructureLocal2Stack)) ∧
        s2.sp = s.sp ∧
        s2.trace = s.trace ∧
        s2.readReg64 .x19 = coroPtr ∧
        s2.readReg64 .x22 = s.readReg64 .x22 ∧
        s2.readReg64 .x25 = s.readReg64 .x25 ∧
        s2.readReg64 .x26 = s.readReg64 .x26 ∧
        s2.readReg64 .x28 = s.readReg64 .x28 ∧
        calleeSavedVRegs s2 = calleeSavedVRegs s ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem)
      Qp := by
  cases opt with
  | none =>
    dsimp only [p1LoadedRecordAt, sessionRecordEmptyHeaderAt]
    sep_norm
    have hstep := p1_err_drop_none_vregs_wp_ext_placed ext s coroPtr hpc hrun hsp_align hx19
    refine ret_sepWP_steps_frame_placed hcrl hstep (by sep_focus)
      fun s2 _ _ _ hcrl2 hregs2 => ?_
    rcases hregs2 with ⟨hsp2, htr2, hx19_2, hx22_2, hx25_2, hx26_2, hx28_2, _, hvregs2, hvm2⟩
    refine ⟨⟨[], FreeOnlyEvs.nil, ?_⟩,
      hsp2, htr2, hx19_2, hx22_2, hx25_2, hx26_2, hx28_2, hvregs2, hcrl2⟩
    dsimp only [AllocCostModel.stepEvents, List.foldl]
    rw [A.pool_of_vmPreserved hvm2]
    refine Entails.sepExists_right 0#64 (Entails.sepExists_right 8#64 ?_)
    refine Entails.pure_right (by decide) ?_
    have hite0 : (0#64 = 0) = True := eq_true rfl
    simp only [hite0, ↓reduceIte]
    sep_norm
    have hf8 :
        ((coroPtr + 248#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (coroPtr + 256#64) 336 ⊢
          memRegion (coroPtr + 248#64) 344 := by
      rw [ProofLib.memRegion_split (coroPtr + 248#64) 8 336 (by decide)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact sepConj_mono_left (pointsTo64_entails_memRegion _ _)
    refine Entails.trans (Entails.of_eq (by ac_rfl))
      (Entails.trans
        (sepConj_mono_left
          (Q := ((coroPtr + 224#64) ↦₆₄ 0#64) ∗
                ((coroPtr + 232#64) ↦₆₄ 8#64) ∗
                ((coroPtr + 240#64) ↦₆₄ 0#64) ∗
                A.pool lim st0 s ∗
                stackAt s.sp dropSessionStructureLocal2Stack) hf8)
        (Entails.of_eq (by ac_rfl)))
  | some r =>
    dsimp only [p1LoadedRecordAt]
    sep_norm
    refine SepWPp.exists_elim fun g => ?_
    refine SepWPp.pure_elim fun _ => ?_
    rw [sessionRecordAt_eq_vecAt_sep_curSessionAt A.repAlloc (coroPtr + 0xe0#64) g r]
    refine SepWPp.weaken_frame (prevVecAt_unpack A.repAlloc coroPtr g.prevCap g.prevPtr)
      (by sep_focus) ?_
    sep_norm
    refine SepWPp.pure_elim fun hprev_lt => ?_
    refine SepWPp.weaken_frame
      (Entails.refl (curSessionAt A.repAlloc (coroPtr + 0xf8#64) g.cur r.currentSession))
      (by sep_focus) ?_
    cases hcur_g : g.cur <;> cases hcur_r : r.currentSession
    · dsimp only [curSessionAt, noneCap]
      have hstep := p1_err_drop_none_vregs_wp_ext_placed ext s coroPtr hpc hrun hsp_align hx19
      refine ret_sepWP_steps_frame_placed hcrl hstep (by sep_focus)
        fun s2 _ _ _ hcrl2 hregs2 => ?_
      rcases hregs2 with ⟨hsp2, htr2, hx19_2, hx22_2, hx25_2, hx26_2, hx28_2, _, hvregs2, hvm2⟩
      refine ⟨⟨[], FreeOnlyEvs.nil, ?_⟩,
        hsp2, htr2, hx19_2, hx22_2, hx25_2, hx26_2, hx28_2, hvregs2, hcrl2⟩
      dsimp only [AllocCostModel.stepEvents, List.foldl]
      rw [A.pool_of_vmPreserved hvm2]
      refine Entails.sepExists_right g.prevCap (Entails.sepExists_right g.prevPtr ?_)
      refine Entails.pure_right hprev_lt ?_
      simp only [RustCliAllocBudget.repAlloc_live]
      have hf8 :
          ((coroPtr + 248#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (coroPtr + 256#64) 336 ⊢
            memRegion (coroPtr + 248#64) 344 := by
        rw [ProofLib.memRegion_split (coroPtr + 248#64) 8 336 (by decide)]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        exact sepConj_mono_left (pointsTo64_entails_memRegion _ _)
      refine Entails.trans (Entails.of_eq (by ac_rfl))
        (Entails.trans
          (sepConj_mono_left
            (Q := ((coroPtr + 224#64) ↦₆₄ g.prevCap) ∗
                  ((coroPtr + 232#64) ↦₆₄ g.prevPtr) ∗
                  ((coroPtr + 240#64) ↦₆₄ 0#64) ∗
                  (if g.prevCap = 0 then emp
                   else A.live g.prevPtr (g.prevCap.toNat * 24) 8 ∗
                     memRegion g.prevPtr (g.prevCap.toNat * 24)) ∗
                  A.pool lim st0 s ∗
                  stackAt s.sp dropSessionStructureLocal2Stack) hf8)
          (Entails.of_eq (by ac_rfl)))
    · dsimp only [curSessionAt]
      exact SepWPp.pure_elim False.elim
    · dsimp only [curSessionAt]
      exact SepWPp.pure_elim False.elim
    · rename_i G ses
      dsimp only [curSessionAt, sessionStateReprAt]
      sep_norm
      refine SepWPp.pure_elim fun _ => ?_
      have hss_split :
          ∃ R_ss : SepProp,
            (sessionStateAt A.repAlloc (coroPtr + 0xf8#64) G ses.state ⊢
              ⌜G.localIk.cap.toNat < 2 ^ 63⌝ ∗ ((coroPtr + 0xf8#64) ↦₆₄ G.localIk.cap) ∗ R_ss) ∧
            (((coroPtr + 0xf8#64) ↦₆₄ G.localIk.cap) ∗ R_ss ⊢
              sessionStateAt A.repAlloc (coroPtr + 0xf8#64) G ses.state) := by
        unfold sessionStateAt
        exact pure_vecGhost_sep_split
      obtain ⟨R_ss, hss_fwd, hss_bwd⟩ := hss_split
      refine SepWPp.weaken_frame hss_fwd (by sep_focus) ?_
      sep_norm
      refine SepWPp.pure_elim fun hcap_lt => ?_
      have hcap_ne : G.localIk.cap ≠ 0xffffffffffffffff#64 := by bv_omega
      have hto_call := p1_err_drop_ss_to_call_vregs_wp_ext_placed ext s coroPtr G.localIk.cap
        hcap_ne hpc hrun hsp_align hx19
      refine bind_sepWP_steps_frame_placed hcrl hto_call (by sep_focus)
        fun s1 _ hpc1 hrun1 hcrl1 hregs1 => ?_
      rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx19_1, hx22_1, hx25_1, hx26_1, hx28_1, _, hx30_1,
        hvregs1, hvm1⟩
      refine SepWPp.weaken_frame
        (Entails.of_eq (A.pool_of_vmPreserved hvm1).symm)
        (by sep_focus) ?_
      have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp_align
      refine SepWPp.weaken_frame hss_bwd (by sep_focus) ?_
      refine call_lscro_nopanic_steps_frame_placed
        (spec := dropSessionStructureLocal2Spec M A lim)
        (x := (⟨coroPtr + 0xf8#64, G, ses.state⟩, st0))
        (T := sessionStateAt A.repAlloc (coroPtr + 0xf8#64) G ses.state ∗ A.pool lim st0 s1 ∗
          stackAt s.sp dropSessionStructureLocal2Stack)
        hcrl1 hdrop_ss hpc1 hrun1 hsp1_al hx30_1
        (by dsimp only [dropSessionStructureLocal2Spec]; rw [hsp1])
        (And.intro hx0_1 (show LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (s1.readReg64 .lr) by
          simp (config := { decide := true }) [show s1.readReg64 .lr = _ from hx30_1, wp_norm]))
        (by sep_focus)
        (hoom_false := fun _ => rfl)
        (hnext := fun s2 _ hpc2 hrun2 hsp2_1 _ hcs2 hcrl2 => ?_)
      dsimp only [dropSessionStructureLocal2Spec]
      rw [hsp1]
      sep_norm
      refine SepWPp.exists_elim fun evs => ?_
      refine SepWPp.pure_elim fun ⟨htr2_1, hevs⟩ => ?_
      refine SepWPp.done hpc2 hrun2 ?_
      rcases hcs2 with ⟨hx19_cs2, _, _, hx22_cs2, _, _, hx25_cs2, hx26_cs2, _, hx28_cs2, _,
        hvregs_cs2⟩
      refine ⟨⟨evs, hevs, ?_⟩, hsp2_1.trans hsp1, htr2_1.trans htr1,
        hx19_cs2.trans hx19_1, hx22_cs2.trans hx22_1,
        hx25_cs2.trans hx25_1, hx26_cs2.trans hx26_1, hx28_cs2.trans hx28_1,
        hvregs_cs2.trans hvregs1, hcrl2⟩
      refine Entails.sepExists_right g.prevCap (Entails.sepExists_right g.prevPtr ?_)
      refine Entails.pure_right hprev_lt ?_
      exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 1200000 in
theorem p1_err_tail_prev_core_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st0 : M.σ}
    {ext : String → Option (State → State)}
    {Qp : State → SepProp → Prop}
    (hdealloc : subroutine_ok (stageP1ProgPlaced ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (s0 s : State) (sp coroPtr outPtr prevCap prevPtr cap ptr devWord u_278 : BitVec 64)
    (b_2c0 : BitVec 8)
    (peer : AddrGhost) (pad : List (BitVec 8))
    (hprev_lt : prevCap.toNat * 24 < 2 ^ 63)
    (hpad : pad.length = 7)
    (hw4 : peer.device :: pad = unpack64 devWord)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_eq : s.sp = sp)
    (hpc : s.pc = stageP1EntryPlaced + 0x359c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = (cap.extractLsb' 0 32).zeroExtend 64)
    (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = 0x800000000000000c#64) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s
      (((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       (if prevCap = 0 then emp
        else A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24)) ∗
       memRegion (coroPtr + 0xf8#64) 344 ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       memRegion outPtr 48 ∗ SegUntrusted.vecU8Buf A.repAlloc cap ptr peer.name.bytes ∗
       ((sp + 0x370#64) ↦₆₄ (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)) ∗
       ((sp + 0x378#64) ↦₆₄ ((BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)) ∗
       ((sp + 0x380#64) ↦₆₄ (devWord.extractLsb' 0 32 ++ (BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 32 32)) ∗
       ((sp + 0x388#64) ↦₆₄ (u_278.extractLsb' 0 32 ++ devWord.extractLsb' 32 32)) ∗
       ((sp + 0x390#64) ↦₃₂ u_278.extractLsb' 32 32) ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗ A.pool lim st0 s ∗ stackAt sp allocHookStack)
      (fun sf P_f =>
        (∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (P_f ⊢
            memRegion (coroPtr + 0xe0#64) 368 ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
            apiDecResultAt A.repAlloc outPtr (.error (.untrustedIdentity peer.val)) ∗
            memRegion (sp + 0x370#64) 36 ∗
            decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
            A.pool lim (M.stepEvents evs st0) sf ∗
            stackAt sp allocHookStack)) ∧
        sf.sp = sp + 0xcd0#64 ∧ sf.trace = s.trace ∧
        ClosureCalleeSaved s0 sf ∧ calleeSavedVRegs sf = calleeSavedVRegs s ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem)
      Qp := by
  have hx25_s : s.readReg64 .x25 = s.sp + 0x210#64 := by rw [hsp_eq]; exact hx25
  rw [savedRegsAt_eq_sp_c70 sp s0]
  refine SepWPp.weaken_frame (memRegion_48_out_entails outPtr) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u_ret0 =>
    SepWPp.exists_elim fun u_ret08 =>
    SepWPp.exists_elim fun u_ret0c =>
    SepWPp.exists_elim fun u_ret14 =>
    SepWPp.exists_elim fun u_ret1c =>
    SepWPp.exists_elim fun u_ret24 =>
    SepWPp.exists_elim fun u_ret2c => ?_
  have hzero64 : (0 : BitVec 64) = 0#64 := rfl
  rw [hzero64]
  by_cases hcap : prevCap = 0#64
  · subst hcap
    simp only [↓reduceIte]
    sep_norm
    have htail := p3_err_tail_b_vregs_wp_ext_placed
      ext s coroPtr outPtr 0x800000000000000c#64 prevPtr
      (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)
      ((BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)
      (devWord.extractLsb' 0 32 ++ (BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 32 32)
      (u_278.extractLsb' 0 32 ++ devWord.extractLsb' 32 32)
      u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
      (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21)
      (s0.readReg64 .x22) (s0.readReg64 .x23) (s0.readReg64 .x24)
      (s0.readReg64 .x25) (s0.readReg64 .x26) (s0.readReg64 .x27)
      (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
      (cap.extractLsb' 0 32) (u_278.extractLsb' 32 32) u_ret08 u_ret2c b_2c0
      hpc hrun hsp_align hx19 hx22 hx25_s hx26 hx28
    rw [hsp_eq] at htail
    refine ret_sepWP_steps_frame_placed hcrl htail (by sep_focus)
      fun sf _ _ _ hcrlf hregsf => ?_
    rcases hregsf with ⟨hspf, htrf, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f,
      hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, _, hvregsf, hvmf⟩
    have hcs_f : ClosureCalleeSaved s0 sf :=
      ⟨hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f,
        True.intro⟩
    refine ⟨⟨[], FreeOnlyEvs.nil, ?_⟩, hspf, htrf, hcs_f, hvregsf, hcrlf⟩
    dsimp only [AllocCostModel.stepEvents, List.foldl]
    rw [A.pool_of_vmPreserved hvmf]
    let R_tail : SepProp :=
      ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
      ((sp + 0xc70#64) ↦₆₄ s0.readReg64 .x29) ∗ ((sp + 0xc78#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((sp + 0xc80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((sp + 0xc88#64) ↦₆₄ s0.readReg64 .x27) ∗
      ((sp + 0xc90#64) ↦₆₄ s0.readReg64 .x26) ∗ ((sp + 0xc98#64) ↦₆₄ s0.readReg64 .x25) ∗
      ((sp + 0xca0#64) ↦₆₄ s0.readReg64 .x24) ∗ ((sp + 0xca8#64) ↦₆₄ s0.readReg64 .x23) ∗
      ((sp + 0xcb0#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp + 0xcb8#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((sp + 0xcc0#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp + 0xcc8#64) ↦₆₄ s0.readReg64 .x19) ∗
      A.pool lim st0 s ∗ stackAt sp allocHookStack
    have hout := untrusted_out_entails A.repAlloc outPtr cap ptr devWord u_278 peer pad hpad hw4
    simp only [BitVec.add_zero] at hout
    have hcoro := coro_e0_368_fold coroPtr 0#64 prevPtr 0#64
    have h370 := sp_370_rejoin sp
      (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)
      ((BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)
      (devWord.extractLsb' 0 32 ++ (BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 32 32)
      (u_278.extractLsb' 0 32 ++ devWord.extractLsb' 32 32)
      (u_278.extractLsb' 32 32)
    refine Entails.trans (Entails.of_eq (by dsimp only [R_tail]; simp only [BitVec.add_zero]; ac_rfl))
      (Entails.trans
        (sepConj_mono hcoro (sepConj_mono hout (sepConj_mono_left (Q := R_tail) h370)))
        (Entails.of_eq (by dsimp only [R_tail]; ac_rfl)))
  · simp only [hcap, ↓reduceIte]
    have htail := p1_err_tail_prev_dealloc_core_wp_placed (st := st0) ext hdealloc s coroPtr outPtr
      0x800000000000000c#64 prevCap prevPtr
      (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)
      ((BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)
      (devWord.extractLsb' 0 32 ++ (BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 32 32)
      (u_278.extractLsb' 0 32 ++ devWord.extractLsb' 32 32)
      u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
      (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21)
      (s0.readReg64 .x22) (s0.readReg64 .x23) (s0.readReg64 .x24)
      (s0.readReg64 .x25) (s0.readReg64 .x26) (s0.readReg64 .x27)
      (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
      (cap.extractLsb' 0 32) (u_278.extractLsb' 32 32) u_ret08 u_ret2c b_2c0
      hcap hprev_lt hpc hrun hsp_align hx19 hx22 hx25_s hx26 hx28
    rw [hsp_eq] at htail
    refine ret_sepWP_steps_frame_placed hcrl htail (by sep_focus)
      fun sf _ _ _ hcrlf hregsf => ?_
    rcases hregsf with ⟨hspf, htrf, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f,
      hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, _, hvregsf⟩
    have hcs_f : ClosureCalleeSaved s0 sf :=
      ⟨hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f,
        True.intro⟩
    refine ⟨⟨rustDeallocEvents (prevCap.toNat * 24) 8,
      FreeOnlyEvs.singleton 8 (prevCap.toNat * 24), ?_⟩,
      hspf, htrf, hcs_f, hvregsf, hcrlf⟩
    let R_tail : SepProp :=
      ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
      ((sp + 0xc70#64) ↦₆₄ s0.readReg64 .x29) ∗ ((sp + 0xc78#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((sp + 0xc80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((sp + 0xc88#64) ↦₆₄ s0.readReg64 .x27) ∗
      ((sp + 0xc90#64) ↦₆₄ s0.readReg64 .x26) ∗ ((sp + 0xc98#64) ↦₆₄ s0.readReg64 .x25) ∗
      ((sp + 0xca0#64) ↦₆₄ s0.readReg64 .x24) ∗ ((sp + 0xca8#64) ↦₆₄ s0.readReg64 .x23) ∗
      ((sp + 0xcb0#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp + 0xcb8#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((sp + 0xcc0#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp + 0xcc8#64) ↦₆₄ s0.readReg64 .x19) ∗
      A.pool lim (M.stepEvents (rustDeallocEvents (prevCap.toNat * 24) 8) st0) sf ∗
      stackAt sp allocHookStack
    have hout := untrusted_out_entails A.repAlloc outPtr cap ptr devWord u_278 peer pad hpad hw4
    simp only [BitVec.add_zero] at hout
    have hcoro := coro_e0_368_fold coroPtr prevCap prevPtr 0#64
    have h370 := sp_370_rejoin sp
      (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)
      ((BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)
      (devWord.extractLsb' 0 32 ++ (BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 32 32)
      (u_278.extractLsb' 0 32 ++ devWord.extractLsb' 32 32)
      (u_278.extractLsb' 32 32)
    refine Entails.trans (Entails.of_eq (by dsimp only [R_tail]; simp only [BitVec.add_zero]; ac_rfl))
      (Entails.trans
        (sepConj_mono hcoro (sepConj_mono hout (sepConj_mono_left (Q := R_tail) h370)))
        (Entails.of_eq (by dsimp only [R_tail]; ac_rfl)))

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedExtPlacedBudgetAux
