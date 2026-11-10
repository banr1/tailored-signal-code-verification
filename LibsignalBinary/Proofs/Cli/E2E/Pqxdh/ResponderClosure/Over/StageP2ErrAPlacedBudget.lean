/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsAPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2ErrAPlaced
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
public meta import Lean.Elab.Tactic -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3Ext
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedAux
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Defs
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b2
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Placed Stage P2 Over-Path Error Unwind Funnel and Arms 1–2

Threads `RustCliAllocBudget M` and `FreeOnlyEvs` across the `[LibsignalPlacement]` populated-record
Stage P2 error teardown (`+0x3588`, `+0x1648`) and store-error Arms 1 (`+0x0f38`) and 2 (`+0x0998`)
on block 518.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2ErrAPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (SessionState)
open CryptoVerification (LibsignalPlacement lsLogFilterAddr lsmpl withLsCodeLoaded)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost sessionStateAt)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (
  DropSessionStructureGhost dropSessionStructureLocal2Stack
)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  KyberPreKeyStoreSpec LibsignalCodeRoLoaded SignedPreKeyStoreSpec kpkGetPollOutAt speErrAt
  speWordsAt spkGetPollOutAt withLsRoCl
)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (
  ClosureCalleeSaved decryptPrekeySavedRegsAt sp370_36_split_eq
)
open CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp (weaken_frame)
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (
  cap_ne_noneCap_of_lt eq_of_sep_emp
)
open CryptoVerification.CliHandshake.RespClosurePlaced (blkPC_518 blkPl_518)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (
  coro_e0_3w_344_entails_368 prevSessionsEmptyAt prevSessionsEmptyAt_unpack
  sessionStateAt_split_localIk_cap sp370_4w64_w32_entails_36 stack_dropSS_to_alloc
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  cells6_eq cells6_fold cond_eq_adds64_of_ne_neg1_std3 memRegion_48_out_entails
  p2_bind_sepWP_qp_frame_placed p2_call_nopanic_lscl_steps_frame_placed
  p2_call_nopanic_rocl_steps_frame_placed p2_err88_to_preKeyRecordOut64
  p2_memRegion_420_join p2_preKeyRecordOut64_to_memRegion368
  p2_zeroExtend32_extractLsb_lo savedRegsAt_eq_sp_c70
  sp_a90_rejoin speWordsAt_realign_outPtr stageP1EntryPlaced stageP1ProgPlaced
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved
  rustDeallocEvents
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (futDropBudgetSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitBudget (
  SignedPreKeyStoreBudgetEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget (
  KyberPreKeyStoreBudgetEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (
  KyberPreKeyStoreKitPlacedOk SignedPreKeyStoreKitPlacedOk
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1StepsXExtPlacedBudgetAux (
  sepWP_seg_rebase_vm
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget (
  StageP2ClosureHooksPlaced dropProcessPrekeyImplState1Spec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksErrAPlacedBudget (
  drop_process_prekey_impl_state1_ext_placed_ok p2_err1a_ext_placed_wp
  p2_err1b_hooks_placed_wp p2_err_tail_a_ext_placed_wp p2_err_tail_b1_ext_placed_wp
  p3_err_tail_b_ext_placed_wp
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksErrBPlacedBudget (
  p2_err2a_ext_placed_wp p2_err2b_hooks_placed_wp
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksErrCPlacedBudget (
  p3_err_tail_prev_dealloc_hooks_placed_wp
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsAPlacedBudget (
  p2_bind_sepWP_qp_frame_state_placed
)

set_option allowUnsafeReducibility true in
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  decryptPrekeySavedRegsAt sessionStateAt
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

local macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [BitVec.add_assoc]
    | simp only [BitVec.reduceAdd]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

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
      refine SepWP.done (by simp_all +zetaDelta [arm64_norm]) (by simp_all +zetaDelta [arm64_norm])
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

private theorem p2_bind_free_evs_frame {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_stage F : SepProp} {P_stage_post : List AllocEvent → State → SepProp}
    {Q_evs : List AllocEvent → State → Prop} {Q Qp : State → SepProp → Prop}
    (hstage : SepWPp prog mid s P_stage
      (fun sm P_m => ∃ evs, FreeOnlyEvs evs ∧ (P_m ⊢ P_stage_post evs sm) ∧ Q_evs evs sm)
      (fun _ _ => False))
    (hP : P = P_stage ∗ F)
    (hnext : ∀ (evs : List AllocEvent) (sm : State), Steps prog s sm →
      sm.pc = mid → sm.status = .Running → FreeOnlyEvs evs → Q_evs evs sm →
      SepWPp prog ret sm (P_stage_post evs sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps,
      ⟨hpcm, hrunm, P_m, hmm, evs, hfree, hent, hregs⟩ | ⟨_, _, _, hpanm⟩ | ⟨_, hoom⟩⟩ :=
    hstage (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P_stage_post evs sm ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Arm64.Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext evs sm hsteps hpcm hrunm hfree hregs R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact False.elim hpanm
  · exact (not_satisfies_false_sepConj hoom).elim

private theorem p2_bind_free_tr_evs_frame {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_stage F : SepProp} {P_stage_post : List AllocEvent → State → SepProp}
    {Q_evs : List AllocEvent → State → Prop} {Q Qp : State → SepProp → Prop}
    (hstage : SepWPp prog mid s P_stage
      (fun sm P_m =>
        ∃ evs, FreeOnlyEvs evs ∧ sm.trace = s.trace ∧ (P_m ⊢ P_stage_post evs sm) ∧ Q_evs evs sm)
      (fun _ _ => False))
    (hP : P = P_stage ∗ F)
    (hnext : ∀ (evs : List AllocEvent) (sm : State), Steps prog s sm →
      sm.pc = mid → sm.status = .Running → FreeOnlyEvs evs → sm.trace = s.trace → Q_evs evs sm →
      SepWPp prog ret sm (P_stage_post evs sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps,
      ⟨hpcm, hrunm, P_m, hmm, evs, hfree, htr, hent, hregs⟩ | ⟨_, _, _, hpanm⟩ | ⟨_, hoom⟩⟩ :=
    hstage (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P_stage_post evs sm ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Arm64.Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext evs sm hsteps hpcm hrunm hfree htr hregs R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact False.elim hpanm
  · exact (not_satisfies_false_sepConj hoom).elim

/-! ## Straight-Line Teardown Blocks (`VmPreserved`) -/

set_option maxHeartbeats 800000 in
private theorem p2_err_tail_b2_to_3588_ext_placed_wp [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (coroPtr errTag outPtr
    v_a9c v_aa4 v_aac v_ab4 u_370 u_378 u_380 u_388 : BitVec 64)
    (v_a98 v_abc u_390 : BitVec 32)
    (hpc : s.pc = stageP1EntryPlaced + 0x1898#64)
    (hrun : s.status = .Running) (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = s.sp + 0xa90#64) :
    SepWP (stageP1ProgPlaced ext) (stageP1EntryPlaced + 0x3588#64) s
      (((s.sp + 0xa90#64) ↦₆₄ errTag) ∗ ((s.sp + 0xa98#64) ↦₃₂ v_a98) ∗
       ((s.sp + 0xa9c#64) ↦₆₄ v_a9c) ∗ ((s.sp + 0xaa4#64) ↦₆₄ v_aa4) ∗
       ((s.sp + 0xaac#64) ↦₆₄ v_aac) ∗ ((s.sp + 0xab4#64) ↦₆₄ v_ab4) ∗
       ((s.sp + 0xabc#64) ↦₃₂ v_abc) ∗
       ((s.sp + 0x370#64) ↦₆₄ u_370) ∗ ((s.sp + 0x378#64) ↦₆₄ u_378) ∗
       ((s.sp + 0x380#64) ↦₆₄ u_380) ∗ ((s.sp + 0x388#64) ↦₆₄ u_388) ∗
       ((s.sp + 0x390#64) ↦₃₂ u_390))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0xa90#64) ↦₆₄ errTag) ∗ ((s.sp + 0xa98#64) ↦₃₂ v_a98) ∗
          ((s.sp + 0xa9c#64) ↦₆₄ v_a9c) ∗ ((s.sp + 0xaa4#64) ↦₆₄ v_aa4) ∗
          ((s.sp + 0xaac#64) ↦₆₄ v_aac) ∗ ((s.sp + 0xab4#64) ↦₆₄ v_ab4) ∗
          ((s.sp + 0xabc#64) ↦₃₂ v_abc) ∗
          ((s.sp + 0x370#64) ↦₆₄ v_a9c) ∗ ((s.sp + 0x378#64) ↦₆₄ v_aa4) ∗
          ((s.sp + 0x380#64) ↦₆₄ v_aac) ∗ ((s.sp + 0x388#64) ↦₆₄ v_ab4) ∗
          ((s.sp + 0x390#64) ↦₃₂ v_abc)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x22 = v_a98.zeroExtend 64 ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧ s1.readReg64 .x26 = outPtr ∧
        s1.readReg64 .x28 = errTag ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = s.readReg64 .x30 ∧
        VmPreserved s s1) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = s.sp + 0x370#64 := hx21
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = outPtr := hx26
  have hx28' : s.readReg64 (Reg.gpr 28#5) = s.sp + 0xa90#64 := hx28
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hpc ⊢
  wp_steps_sync_pool_518 ext (blkPl_518.base + 13704#64)
  refine SepWP.done _hpcm _hrunm ?_
  exact ⟨Entails.of_eq (by sep_ac_rfl), rfl, rfl, by simp [calleeSavedVRegs, arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], _hvm⟩

set_option maxHeartbeats 800000 in
private theorem p2_err_drop_ss_to_call_ext_placed_wp [LibsignalPlacement]
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
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.vregs = s.vregs ∧
        s1.readReg64 .x0 = coroPtr + 0xf8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0x359c#64 ∧
        VmPreserved s s1) := by
  have _hcond_cap := cond_eq_adds64_of_ne_neg1_std3 hcap_ne
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hpc ⊢
  wp_steps_sync_pool_518 ext (lsmpl.base 512)
  refine SepWP.done _hpcm _hrunm ?_
  exact ⟨Entails.of_eq (by sep_ac_rfl), rfl, rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], _hvm⟩

/-! ## Budget-Threaded Populated-Record Error Funnel -/

set_option maxHeartbeats 1200000 in
/-- Drops `sessionStateAt` at `coroPtr + 0xf8` and `prevSessionsEmptyAt` at `coroPtr` across
`+0x3588 → s0.readReg64 .x30`, advancing the allocator state along `FreeOnlyEvs`. -/
theorem p2_over_err_drop_record_tail_hooks_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hDropSs3 : subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (s0 s : State)
    (sp coroPtr outPtr errTag w_370 w_378 w_380 w_388 : BitVec 64)
    (w_22 w_390 : BitVec 32) (b_2c0 : BitVec 8)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hCode : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_eq : s.sp = sp) (hsp_lt : dropSessionStructureLocal2Stack ≤ sp.toNat)
    (hpc : s.pc = stageP1EntryPlaced + 0x3588#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx22 : s.readReg64 .x22 = w_22.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = sp + 0x210#64) (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s
      (prevSessionsEmptyAt A.repAlloc coroPtr g ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ memRegion outPtr 48 ∗
       ((sp + 0x370#64) ↦₆₄ w_370) ∗ ((sp + 0x378#64) ↦₆₄ w_378) ∗
       ((sp + 0x380#64) ↦₆₄ w_380) ∗ ((sp + 0x388#64) ↦₆₄ w_388) ∗
       ((sp + 0x390#64) ↦₃₂ w_390) ∗ decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       A.pool lim st s ∗ stackAt sp dropSessionStructureLocal2Stack)
      (fun sf P_f =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (P_f ⊢
            memRegion (coroPtr + 0xe0#64) 368 ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
            ((outPtr + 0x0#64) ↦₆₄ errTag) ∗ ((outPtr + 0x8#64) ↦₃₂ w_22) ∗
            ((outPtr + 0xc#64) ↦₆₄ w_370) ∗ ((outPtr + 0x14#64) ↦₆₄ w_378) ∗
            ((outPtr + 0x1c#64) ↦₆₄ w_380) ∗ ((outPtr + 0x24#64) ↦₆₄ w_388) ∗
            ((outPtr + 0x2c#64) ↦₃₂ w_390) ∗ memRegion (sp + 0x370#64) 36 ∗
            decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp dropSessionStructureLocal2Stack) ∧
          sf.sp = sp + 0xcd0#64 ∧ sf.trace = s.trace ∧ ClosureCalleeSaved s0 sf ∧
          calleeSavedVRegs sf = calleeSavedVRegs s ∧ LibsignalCodeRoLoaded lsmpl sf.mem ∧
          M.liveBytes (M.stepEvents evs st) ≤ M.liveBytes st)
      Qp := by
  have hdss_le : dropSessionStructureLocal2Stack ≤ 2 ^ 64 :=
    Nat.le_trans hsp_lt (Nat.le_of_lt sp.isLt)
  refine weaken_frame (prevSessionsEmptyAt_unpack A.repAlloc coroPtr g) (by sep_focus) ?_
  dsimp only [RustCliAllocBudget.repAlloc]
  sep_norm
  refine SepWPp.pure_elim fun ⟨hprev_lt, _⟩ => ?_
  obtain ⟨R_ss, hss_fwd, hss_bwd⟩ :=
    sessionStateAt_split_localIk_cap A.repAlloc (coroPtr + 0xf8#64) recG recSt
  refine weaken_frame hss_fwd (by sep_focus) ?_
  sep_norm
  refine SepWPp.pure_elim fun hcap_lt => ?_
  have hcap_ne : recG.localIk.cap ≠ 0xffffffffffffffff#64 := cap_ne_noneCap_of_lt hcap_lt
  have hto_call := p2_err_drop_ss_to_call_ext_placed_wp ext s coroPtr recG.localIk.cap
    hcap_ne hpc hrun hsp_align hx19
  refine p2_bind_sepWP_qp_frame_placed hCode hto_call (by sep_focus)
    fun s1 _ hpc1 hrun1 hCode1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, hvregs1, hx0_1, hx19_1, hx22_1, hx25_1, hx26_1,
    hx28_1, _, hx30_1, hvm1⟩
  have hsp1 : s1.sp = sp := hsp1_s.trans hsp_eq
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1_s] using hsp_align
  refine SepWPp.transport_budgetPool hvm1 (by sep_focus) ?_
  refine weaken_frame hss_bwd (by sep_focus) ?_
  refine p2_call_nopanic_lscl_steps_frame_placed
    (spec := dropSessionStructureLocal2Spec M A lim)
    (x := ((⟨coroPtr + 0xf8#64, recG, recSt⟩ : DropSessionStructureGhost), st))
    (T := sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗ A.pool lim st s1 ∗
      stackAt sp dropSessionStructureLocal2Stack)
    hCode1 hDropSs3 hpc1 hrun1 hsp1_al hx30_1
    (by dsimp only [dropSessionStructureLocal2Spec]; rw [hsp1])
    (And.intro hx0_1 (show LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (s1.readReg64 .lr) by
      simp (config := { decide := true }) [show s1.readReg64 .lr = _ from hx30_1, wp_norm]))
    (by sep_focus)
    (hnext := fun s2 _ hpc2 hrun2 hsp2_1 _ hcs2 hCode2 => ?_)
  dsimp only [dropSessionStructureLocal2Spec]
  rw [hsp1]
  sep_norm
  refine SepWPp.exists_elim fun evs_ss => ?_
  sep_norm
  refine SepWPp.pure_elim fun ⟨htr2_1, hfree_ss⟩ => ?_
  rcases hcs2 with ⟨hx19_cs2, _, _, hx22_cs2, _, _, hx25_cs2, hx26_cs2, _, hx28_cs2, _, hvregs_cs2⟩
  have hvregs2_s : calleeSavedVRegs s2 = calleeSavedVRegs s :=
    hvregs_cs2.trans (congrArg VRegFile.calleeSaved hvregs1)
  have hsp2 : s2.sp = sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by
    rw [hsp2, ← hsp_eq]; exact hsp_align
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
  have hx22_2 : s2.readReg64 .x22 = w_22.zeroExtend 64 := hx22_cs2.trans (hx22_1.trans hx22)
  have hx25_2 : s2.readReg64 .x25 = s2.sp + 0x210#64 := by
    rw [hsp2]; exact hx25_cs2.trans (hx25_1.trans hx25)
  have hx26_2 : s2.readReg64 .x26 = outPtr := hx26_cs2.trans (hx26_1.trans hx26)
  have hx28_2 : s2.readReg64 .x28 = errTag := hx28_cs2.trans (hx28_1.trans hx28)
  refine weaken_frame (Entails.of_eq (stack_dropSS_to_alloc sp hdss_le)) (by sep_focus) ?_
  refine weaken_frame (Entails.of_eq (savedRegsAt_eq_sp_c70 sp s0)) (by sep_focus) ?_
  refine weaken_frame (memRegion_48_out_entails outPtr) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u_ret0 => SepWPp.exists_elim fun u_ret08 =>
    SepWPp.exists_elim fun u_ret0c => SepWPp.exists_elim fun u_ret14 =>
    SepWPp.exists_elim fun u_ret1c => SepWPp.exists_elim fun u_ret24 =>
    SepWPp.exists_elim fun u_ret2c => ?_
  change s2.pc = stageP1EntryPlaced + 0x359c#64 at hpc2
  by_cases hcap : g.prevCap = 0#64
  · simp only [hcap, ↓reduceIte, emp_sepConj]
    have htail := p3_err_tail_b_ext_placed_wp ext s2 coroPtr outPtr errTag g.prevPtr
      w_370 w_378 w_380 w_388 u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
      (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
      (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26)
      (s0.readReg64 .x27) (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
      w_22 w_390 u_ret08 u_ret2c b_2c0
      hpc2 hrun2 hsp2_align hx19_2 hx22_2 hx25_2 hx26_2 hx28_2
    rw [hsp2] at htail
    refine p2_bind_sepWP_qp_frame_placed hCode2 htail (by sep_focus)
      fun sf _ hpcf hrunf hCodef hregsf => ?_
    rcases hregsf with ⟨hspf, htrf, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f,
      hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, _, hvregsf, hvmf⟩
    refine SepWPp.transport_budgetPool hvmf (by sep_focus) ?_
    refine weaken_frame (sp370_4w64_w32_entails_36 sp w_370 w_378 w_380 w_388 w_390)
      (by sep_focus) ?_
    refine weaken_frame (coro_e0_3w_344_entails_368 coroPtr 0#64 g.prevPtr 0#64)
      (by sep_focus) ?_
    refine weaken_frame (Entails.of_eq (savedRegsAt_eq_sp_c70 sp s0).symm) (by sep_focus) ?_
    refine weaken_frame (Entails.of_eq (stack_dropSS_to_alloc sp hdss_le).symm) (by sep_focus) ?_
    refine SepWPp.done hpcf hrunf ?_
    exact ⟨evs_ss, hfree_ss, Entails.of_eq (eq_of_sep_emp (by sep_focus)), hspf,
      htrf.trans (htr2_1.trans htr1_s),
      ⟨hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f,
        hx29_f, True.intro⟩,
      hvregsf.trans hvregs2_s, hCodef,
      M.liveBytes_stepEvents_freeOnly_le hfree_ss st⟩
  · simp only [hcap, ↓reduceIte]
    sep_norm
    have htail := p3_err_tail_prev_dealloc_hooks_placed_wp (st := M.stepEvents evs_ss st)
      ext hH s2 coroPtr outPtr errTag
      g.prevCap g.prevPtr w_370 w_378 w_380 w_388 u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
      (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
      (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26)
      (s0.readReg64 .x27) (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
      w_22 w_390 u_ret08 u_ret2c b_2c0 hcap hprev_lt
      hpc2 hrun2 hsp2_align hx19_2 hx22_2 hx25_2 hx26_2 hx28_2
    rw [hsp2] at htail
    dsimp only [] at htail
    refine p2_bind_sepWP_qp_frame_state_placed hCode2 htail (by sep_focus)
      fun sf _ hpcf hrunf hCodef hregsf => ?_
    rcases hregsf with ⟨hspf, htrf, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f,
      hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, _, hvregsf, _hlivef⟩
    refine weaken_frame (sp370_4w64_w32_entails_36 sp w_370 w_378 w_380 w_388 w_390)
      (by sep_focus) ?_
    refine weaken_frame (coro_e0_3w_344_entails_368 coroPtr g.prevCap g.prevPtr 0#64)
      (by sep_focus) ?_
    refine weaken_frame (Entails.of_eq (savedRegsAt_eq_sp_c70 sp s0).symm) (by sep_focus) ?_
    refine weaken_frame (Entails.of_eq (stack_dropSS_to_alloc sp hdss_le).symm) (by sep_focus) ?_
    refine SepWPp.done hpcf hrunf ?_
    have hfree_all : FreeOnlyEvs (evs_ss ++ rustDeallocEvents (g.prevCap.toNat * 24) 8) :=
      hfree_ss.append (FreeOnlyEvs.singleton 8 (g.prevCap.toNat * 24))
    refine ⟨evs_ss ++ rustDeallocEvents (g.prevCap.toNat * 24) 8, hfree_all, ?_, hspf,
      htrf.trans (htr2_1.trans htr1_s),
      ⟨hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f,
        hx29_f, True.intro⟩,
      hvregsf.trans hvregs2_s, hCodef,
      M.liveBytes_stepEvents_freeOnly_le hfree_all st⟩
    rw [M.stepEvents_append]
    exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

abbrev p2_over_err_drop_record_tail_4k_placed_ok [LibsignalPlacement] :=
  @p2_over_err_drop_record_tail_hooks_placed_ok
abbrev p2_over_err_drop_record_tail_ext_placed_ok [LibsignalPlacement] :=
  @p2_over_err_drop_record_tail_hooks_placed_ok

set_option maxHeartbeats 1200000 in
/-- Budget-threaded placed populated-record Stage P2 error funnel (`+0x1648 → s0.readReg64 .x30`)
along `FreeOnlyEvs`. -/
theorem stageP2_over_err_funnel_hooks_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hDropSs3 : subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (s0 s : State) (sp coroPtr outPtr
    w0 w1 w2 w3 w4 w5 r23 u_c8 : BitVec 64)
    (b_2c0 b_390 b_4f2 : BitVec 8)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (herr_ne_neg3 : w0 ≠ 0xfffffffffffffffd#64)
    (herr_ne_neg2 : w0 ≠ 0xfffffffffffffffe#64)
    (hr23_lo : r23.extractLsb' 0 32 = w1.extractLsb' 0 32)
    (hCode : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_eq : s.sp = sp) (hsp_lt : dropSessionStructureLocal2Stack ≤ sp.toNat)
    (hpc : s.pc = stageP1EntryPlaced + 0x1648#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx10 : s.readReg64 .x10 = w2) (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = w0) (hx21 : s.readReg64 .x21 = w4 >>> 8)
    (hx22 : s.readReg64 .x22 = w1 >>> 32) (hx23 : s.readReg64 .x23 = r23)
    (hx24 : s.readReg64 .x24 = w2 >>> 32) (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr) (hx27 : s.readReg64 .x27 = w5)
    (hx28 : s.readReg64 .x28 = sp + 0xa90#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s
      (prevSessionsEmptyAt A.repAlloc coroPtr g ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
       cells (coroPtr + 0x250#64) 6 ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗ ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
       ((sp + 0xa8#64) ↦₆₄ w4) ∗ ((sp + 0xc8#64) ↦₆₄ u_c8) ∗ ((sp + 0xd0#64) ↦₆₄ w3) ∗
       memRegion (sp + 0x370#64) 36 ∗ cells (sp + 0xa90#64) 6 ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗ memRegion outPtr 48 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st s ∗ stackAt sp dropSessionStructureLocal2Stack)
      (fun sf P_f =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧ sf.trace = s.trace ∧
          (P_f ⊢
            memRegion (coroPtr + 0xe0#64) 368 ∗ cells (coroPtr + 0x250#64) 6 ∗
            ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
            ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
            ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ w4) ∗
            ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ w3) ∗
            memRegion (sp + 0x370#64) 36 ∗ cells (sp + 0xa90#64) 6 ∗
            decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗ speWordsAt outPtr w0 w1 w2 w3 w4 w5 ∗
            (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim (M.stepEvents evs st) sf ∗
            stackAt sp dropSessionStructureLocal2Stack) ∧
          sf.sp = sp + 0xcd0#64 ∧ ClosureCalleeSaved s0 sf ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0 ∧ LibsignalCodeRoLoaded lsmpl sf.mem ∧
          M.liveBytes (M.stepEvents evs st) ≤ M.liveBytes st)
      Qp := by
  have hdss_le : dropSessionStructureLocal2Stack ≤ 2 ^ 64 :=
    Nat.le_trans hsp_lt (Nat.le_of_lt sp.isLt)
  have hstep1 := p2_err_tail_a_ext_placed_wp ext s coroPtr outPtr w0 w1 w2 w4 w5 r23 u_c8 b_4f2
    herr_ne_neg3 hr23_lo hpc hrun hsp_align
    hx10 hx19 hx20 hx21 hx22 hx23 hx24 hx26 hx27
  rw [hsp_eq] at hstep1
  refine p2_bind_sepWP_qp_frame_placed hCode hstep1 (by sep_focus)
    fun s1 _ hpc1 hrun1 hCode1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1,
    hx25_1, hx26_1, hx27_1, hx28_1, _, hx30_1, hvregs1, hvm1⟩
  have hsp1_al : s1.spAligned = true := by simp only [State.spAligned, hsp1, ← hsp_eq]; exact hsp_align
  have hdrop := drop_process_prekey_impl_state1_ext_placed_ok (ext := ext)
  have hstk48 : stackAt sp allocHookStack =
      stackAt (sp - 48#64) (allocHookStack - 48) ∗ cells (sp - 48#64) 6 :=
    ProofLib.stackAt_split_cells sp (allocHookStack - 48) 6 (by decide)
  refine weaken_frame (Entails.of_eq (stack_dropSS_to_alloc sp hdss_le)) (by sep_focus) ?_
  refine weaken_frame (Entails.of_eq hstk48) (by sep_focus) ?_
  simp only [sepConj_assoc]
  refine p2_call_nopanic_lscl_steps_frame_placed
    (spec := dropProcessPrekeyImplState1Spec)
    (x := coroPtr + 0x398#64)
    (T := ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗ cells (sp - 48#64) 6)
    hCode1 hdrop hpc1 hrun1 hsp1_al hx30_1
    (by
      dsimp only [dropProcessPrekeyImplState1Spec, withVmPreserved,
        CryptoVerification.E2E.Pqxdh.ResponderStore.dropProcessPrekeyImplState1Spec]
      rw [hsp1, show (coroPtr + 0x398#64) + 0x15a#64 = coroPtr + 0x4f2#64 by rw [BitVec.add_assoc]; rfl])
    hx0_1 (by sep_focus)
    (hnext := fun s2 _ hpc2 hrun2 hsp2_1 _ hcs2 hCode2 => ?_)
  dsimp only [dropProcessPrekeyImplState1Spec, withVmPreserved,
    CryptoVerification.E2E.Pqxdh.ResponderStore.dropProcessPrekeyImplState1Spec]
  rw [hsp1,
      show (coroPtr + 0x398#64) + 0x15a#64 = coroPtr + 0x4f2#64 by rw [BitVec.add_assoc]; rfl]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun hvm2_1 => ?_
  refine SepWPp.pure_elim fun htr2_1 => ?_
  refine weaken_frame (Entails.of_eq hstk48.symm) (by sep_focus) ?_
  refine weaken_frame (Entails.of_eq (stack_dropSS_to_alloc sp hdss_le).symm) (by sep_focus) ?_
  have hsp2 : s2.sp = sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2, ← hsp_eq]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, hx20_cs2, hx21_cs2, hx22_cs2, hx23_cs2, hx24_cs2,
    hx25_cs2, hx26_cs2, hx27_cs2, hx28_cs2, _, hvregs2_1⟩
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
  have hx20_2 : s2.readReg64 .x20 = w0 := hx20_cs2.trans hx20_1
  have hx21_2 : s2.readReg64 .x21 = w4 >>> 8 := hx21_cs2.trans hx21_1
  have hx22_2 : s2.readReg64 .x22 = w2 := hx22_cs2.trans hx22_1
  have hx23_2 : s2.readReg64 .x23 = r23 := hx23_cs2.trans hx23_1
  have hx24_2 : s2.readReg64 .x24 = w1 := hx24_cs2.trans hx24_1
  have hx25_2 : s2.readReg64 .x25 = s2.sp + 0x210#64 := by rw [hx25_cs2, hx25_1, hx25, hsp2]
  have hx26_2 : s2.readReg64 .x26 = outPtr := hx26_cs2.trans hx26_1
  have hx27_2 : s2.readReg64 .x27 = w5 := hx27_cs2.trans hx27_1
  have hx28_2 : s2.readReg64 .x28 = s2.sp + 0xa90#64 := by rw [hx28_cs2, hx28_1, hx28, hsp2]
  refine weaken_frame (Entails.of_eq (cells6_eq (coroPtr + 0x250#64))) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u250 => SepWPp.exists_elim fun u258 =>
    SepWPp.exists_elim fun u260 => SepWPp.exists_elim fun u268 =>
    SepWPp.exists_elim fun u270 => SepWPp.exists_elim fun u278 => ?_
  refine weaken_frame (Entails.of_eq (cells6_eq (sp + 0xa90#64))) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun ua90 => SepWPp.exists_elim fun ua98 =>
    SepWPp.exists_elim fun uaa0 => SepWPp.exists_elim fun uaa8 =>
    SepWPp.exists_elim fun uab0 => SepWPp.exists_elim fun uab8 => ?_
  change s2.pc = stageP1EntryPlaced + 0x1698#64 at hpc2
  have hstep3 := p2_err_tail_b1_ext_placed_wp ext s2 coroPtr outPtr w0 w1 w2 w3 w4 w5 r23
    u250 u258 u260 u268 u270 u278 ua90 ua98 uaa0 uaa8 uab0 uab8 b_390
    herr_ne_neg2 hr23_lo hpc2 hrun2 hsp2_align
    hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx27_2 hx28_2
  rw [hsp2] at hstep3
  refine p2_bind_sepWP_qp_frame_placed hCode2 hstep3 (by sep_focus)
    fun s3 _ hpc3 hrun3 hCode3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3, htr3_2, hx19_3, _, hx21_3, hx25_3, hx26_3, hx28_3, _, _,
    hvregs3_2, hvm3_2⟩
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3, ← hsp_eq]; exact hsp_align
  have hc250 := cells6_fold (coroPtr + 0x250#64) w0 w1 w2 w3 w4 w5
  repeat (simp only [BitVec.add_assoc] at hc250); repeat (simp only [BitVec.reduceAdd] at hc250)
  refine weaken_frame hc250 (by sep_focus) ?_
  refine weaken_frame (Entails.of_eq (sp370_36_split_eq sp)) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u390 => SepWPp.exists_elim fun u388 =>
    SepWPp.exists_elim fun u380 => SepWPp.exists_elim fun u378 =>
    SepWPp.exists_elim fun u370 => ?_
  have hx21_3' : s3.readReg64 .x21 = s3.sp + 0x370#64 := by rw [hx21_3, hsp3]
  have hx25_3' : s3.readReg64 .x25 = s3.sp + 0x210#64 := by rw [hx25_3, hsp3]
  have hx28_3' : s3.readReg64 .x28 = s3.sp + 0xa90#64 := by rw [hx28_3, hsp3]
  change s3.pc = stageP1EntryPlaced + 0x1898#64 at hpc3
  have hstep4 := p2_err_tail_b2_to_3588_ext_placed_wp ext s3 coroPtr w0 outPtr
    (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
    (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)
    (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)
    (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)
    u370 u378 u380 u388 (w1.extractLsb' 0 32) (w5.extractLsb' 32 32) u390
    hpc3 hrun3 hsp3_align hx19_3 hx21_3' hx25_3' hx26_3 hx28_3'
  rw [hsp3] at hstep4
  refine p2_bind_sepWP_qp_frame_placed hCode3 hstep4 (by sep_focus)
    fun s4 _ hpc4 hrun4 hCode4 hregs4 => ?_
  rcases hregs4 with ⟨hsp4, htr4_3, hvregs4_3, hx19_4, hx22_4, hx25_4, hx26_4,
    hx28_4, _, _, hvm4_3⟩
  have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := by rw [hsp4, ← hsp_eq]; exact hsp_align
  have hvm4 : VmPreserved s s4 := hvm1.trans (hvm2_1.trans (hvm3_2.trans hvm4_3))
  refine SepWPp.transport_budgetPool hvm4 (by sep_focus) ?_
  refine weaken_frame (sp_a90_rejoin sp w0 w1 w2 w3 w4 w5) (by sep_focus) ?_
  have hdropTail := p2_over_err_drop_record_tail_hooks_placed_ok (st := st) (Qp := fun _ _ => False)
    hH hDropSs3 s0 s4
    sp coroPtr outPtr w0
    (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
    (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)
    (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)
    (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)
    (w1.extractLsb' 0 32) (w5.extractLsb' 32 32) b_2c0
    g recG recSt
    hCode4 hsp4 hsp_lt hpc4 hrun4 hsp4_align
    hx19_4 hx22_4 hx25_4 hx26_4 hx28_4
  refine p2_bind_free_evs_frame hdropTail (by sep_focus)
    fun evs sf _ hpcf hrunf hfree ⟨hspf, htrf, hcsf, hvregsf, hCodef, hlivef⟩ => ?_
  refine weaken_frame
    (Entails.of_eq (speWordsAt_realign_outPtr outPtr w0 w1 w2 w3 w4 w5)) (by sep_focus) ?_
  refine SepWPp.done hpcf hrunf ?_
  have hvregs_all : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
    rw [hvregsf, hvregs4_3, hvregs3_2, hvregs2_1, hvregs1, hvregs]
  refine ⟨evs, hfree, by rw [htrf, htr4_3, htr3_2, htr2_1, htr1], ?_,
    hspf, hcsf, hvregs_all, hCodef, hlivef⟩
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

abbrev stageP2_over_err_funnel_4k_placed_ok [LibsignalPlacement] :=
  @stageP2_over_err_funnel_hooks_placed_ok
abbrev stageP2_over_err_funnel_ext_placed_ok [LibsignalPlacement] :=
  @stageP2_over_err_funnel_hooks_placed_ok

/-! ## Budget-Threaded Store-Error Arms 1 and 2 -/

set_option maxHeartbeats 1200000 in
/-- Budget-threaded Error Arm 1 (`+0x0f38 → s0.readReg64 .x30`) from a direct `futDropBudgetSpec`
contract along `FreeOnlyEvs`. -/
theorem p2_over_arm1_err_drop_hooks_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    {spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64}
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hDropSs3 : subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hspk_drop : subroutine_ok (stageP1ProgPlaced ext) (0#64 + spkKit.getFutDropOff)
      (withLsRoCl lsmpl futDropBudgetSpec))
    (s0 s : State) (sp coroPtr outPtr spkStorePtr spkFutPtr ctxPtr
    v_b0 u_90 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_d0 : BitVec 64)
    (signedPreKeyId : BitVec 32) (b_2c0 b_390 b_4f2 : BitVec 8) (e : spkKit.GetErr)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hCode : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_eq : s.sp = sp)
    (hsp_lt : dropSessionStructureLocal2Stack ≤ sp.toNat)
    (hpc : s.pc = stageP1EntryPlaced + 0xf38#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = coroPtr + 0x4f2#64) (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = coroPtr + 0x398#64) (hx27 : s.readReg64 .x27 = ctxPtr)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s
      (spkGetPollOutAt spkKit (sp + 0x3e0#64) (.error e) ∗ memRegion (sp + 0x438#64) 280 ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ spkFutPtr) ∗
       ((coroPtr + 0x500#64) ↦₆₄ (0#64 + spkKit.getFutVtOff)) ∗
       A.live spkFutPtr spkKit.getBoxSize 8 ∗
       spkKit.getBoxAt spkFutPtr spkStorePtr signedPreKeyId 1#8 ∗
       ((0#64 + spkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + spkKit.getFutDropOff)) ∗
       ((0#64 + spkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 spkKit.getBoxSize) ∗
       ((0#64 + spkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((sp + 0x90#64) ↦₆₄ u_90) ∗ ((sp + 0x98#64) ↦₆₄ u_98) ∗ ((sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((sp + 0xa8#64) ↦₆₄ u_a8) ∗ ((sp + 0xb0#64) ↦₆₄ u_b0) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((sp + 0xc0#64) ↦₆₄ u_c0) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       prevSessionsEmptyAt A.repAlloc coroPtr g ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
       cells (coroPtr + 0x250#64) 6 ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗ ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       memRegion (sp + 0x370#64) 36 ∗ cells (sp + 0xa90#64) 6 ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       memRegion outPtr 48 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st s ∗
       stackAt sp dropSessionStructureLocal2Stack)
      (fun sf P_f =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          sf.trace = s.trace ∧
          (P_f ⊢
            memRegion (sp + 0x3e0#64) 368 ∗
            ((coroPtr + 0x4f8#64) ↦₆₄ spkFutPtr) ∗
            ((coroPtr + 0x500#64) ↦₆₄ (0#64 + spkKit.getFutVtOff)) ∗
            ((0#64 + spkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + spkKit.getFutDropOff)) ∗
            ((0#64 + spkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 spkKit.getBoxSize) ∗
            ((0#64 + spkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
            ((sp + 0x90#64) ↦₆₄ spkKit.getErr.w5 e) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
            ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ spkKit.getErr.w4 e) ∗
            ((sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((sp + 0xb8#64) ↦₆₄ spkKit.getErr.w2 e) ∗
            ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
            ((sp + 0xd0#64) ↦₆₄ spkKit.getErr.w3 e) ∗
            memRegion (coroPtr + 0xe0#64) 368 ∗ cells (coroPtr + 0x250#64) 6 ∗
            ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
            ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
            memRegion (sp + 0x370#64) 36 ∗ cells (sp + 0xa90#64) 6 ∗
            decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
            speErrAt spkKit.getErr outPtr e ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt sp dropSessionStructureLocal2Stack) ∧
          sf.sp = sp + 0xcd0#64 ∧ ClosureCalleeSaved s0 sf ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
          LibsignalCodeRoLoaded lsmpl sf.mem ∧
          M.liveBytes (M.stepEvents evs st) ≤ M.liveBytes st)
      Qp := by
  have hdss_le : dropSessionStructureLocal2Stack ≤ 2 ^ 64 :=
    Nat.le_trans hsp_lt (Nat.le_of_lt sp.isLt)
  dsimp only [spkGetPollOutAt]
  refine weaken_frame (p2_err88_to_preKeyRecordOut64 spkKit.getErr (sp + 0x3e0#64) e)
    (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u_418 => ?_
  have hstep1 := p2_err1a_ext_placed_wp ext s coroPtr spkFutPtr
    (0#64 + spkKit.getFutVtOff) (0#64 + spkKit.getFutDropOff) (spkKit.getErr.w0 e)
    (coroPtr + 0x398#64) (coroPtr + 0x4f2#64) v_b0 u_90 u_98 u_a0 u_b0 u_b8 u_d0
    (spkKit.getErr.w1 e) (spkKit.getErr.w2 e) (spkKit.getErr.w3 e)
    (spkKit.getErr.w4 e) (spkKit.getErr.w5 e) u_418
    (spkKit.getFutDrop_ne_zero rfl) hpc hrun hsp_align hx19 hx21 hx23 hx26
  rw [hsp_eq, BitVec.add_zero] at hstep1
  refine p2_bind_sepWP_qp_frame_placed hCode hstep1 (by sep_focus)
    fun s1 _ hpc1 hrun1 hCode1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, _, hx19_1, _, hx21_1, hx22_1, hx23_1, hx24_1,
    hx25_1, hx26_1, hx27_1, hx28_1, _, hx30_1, hvregs1, hvm1⟩
  have hsp1_al : s1.spAligned = true := by simp only [State.spAligned, hsp1, ← hsp_eq]; exact hsp_align
  refine weaken_frame (p2_memRegion_420_join sp) (by sep_focus) ?_
  refine weaken_frame
    (p2_preKeyRecordOut64_to_memRegion368 sp 0xffffffffffffffff#64
      (spkKit.getErr.w0 e) (spkKit.getErr.w1 e) (spkKit.getErr.w2 e)
      (spkKit.getErr.w3 e) (spkKit.getErr.w4 e) (spkKit.getErr.w5 e) u_418)
    (by sep_focus) ?_
  refine p2_call_nopanic_rocl_steps_frame_placed (spec := futDropBudgetSpec) (x := ()) (T := emp)
    hCode1 hspk_drop hpc1 hrun1 hsp1_al hx30_1
    (by dsimp only [futDropBudgetSpec]; exact (pure_true_sepConj emp).symm)
    True.intro (by sep_focus)
    (hnext := fun s2 _ hpc2 hrun2 hsp2_1 _ hcs2 hCode2 => ?_)
  dsimp only [futDropBudgetSpec]
  refine SepWPp.pure_elim fun ⟨htr2_1, hvm2_1⟩ => ?_
  have hvm2 : VmPreserved s s2 := hvm1.trans hvm2_1
  refine SepWPp.transport_budgetPool hvm2 (by sep_focus) ?_
  have hsp2 : s2.sp = sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2, ← hsp_eq]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, _, hx21_cs2, hx22_cs2, hx23_cs2, hx24_cs2,
    hx25_cs2, hx26_cs2, hx27_cs2, hx28_cs2, _, hvregs2_1⟩
  refine weaken_frame
    (spkKit.getBoxAt_memRegion spkFutPtr spkStorePtr signedPreKeyId 1#8) (by sep_focus) ?_
  refine weaken_frame (Entails.of_eq (stack_dropSS_to_alloc sp hdss_le)) (by sep_focus) ?_
  have hstep3 := p2_err1b_hooks_placed_wp (st := st) ext hH s2 coroPtr spkFutPtr
    (0#64 + spkKit.getFutVtOff) outPtr
    (spkKit.getErr.w0 e) (spkKit.getErr.w1 e) (spkKit.getErr.w2 e)
    (spkKit.getErr.w4 e) (spkKit.getErr.w5 e) ctxPtr u_a8 u_c0 spkKit.getBoxSize
    spkKit.getBoxSize_ne_zero spkKit.getBoxSize_lt hpc2 hrun2 hsp2_align
    (hx19_cs2.trans hx19_1) (hx21_cs2.trans hx21_1) (hx22_cs2.trans hx22_1)
    (hx23_cs2.trans hx23_1) (hx24_cs2.trans hx24_1) (hx26_cs2.trans hx26_1)
    (hx27_cs2.trans (hx27_1.trans hx27)) (hx28_cs2.trans hx28_1)
  rw [hsp2] at hstep3
  simp only [BitVec.add_assoc] at hstep3
  refine p2_bind_sepWP_qp_frame_state_placed hCode2 hstep3 (by sep_focus)
    fun s3 _ hpc3 hrun3 hCode3 hregs3 => ?_
  refine weaken_frame (Entails.of_eq (stack_dropSS_to_alloc sp hdss_le).symm) (by sep_focus) ?_
  rcases hregs3 with ⟨hsp3, htr3_2, hx10_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3,
    hx25_3, hx26_3, hx27_3, hx28_3, _, hvregs3_2, _hlive3⟩
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3, ← hsp_eq]; exact hsp_align
  have hx25_3' : s3.readReg64 .x25 = sp + 0x210#64 := by rw [hx25_3, hx25_cs2, hx25_1, hx25]
  have hvregs3 : calleeSavedVRegs s3 = calleeSavedVRegs s0 := by
    rw [hvregs3_2, hvregs2_1, hvregs1, hvregs]
  change s3.pc = stageP1EntryPlaced + 0x1648#64 at hpc3
  have hfunnel := stageP2_over_err_funnel_hooks_placed_ok
    (st := M.stepEvents (rustDeallocEvents spkKit.getBoxSize 8) st)
    (Qp := fun _ _ => False)
    hH hDropSs3 s0 s3 sp coroPtr outPtr
    (spkKit.getErr.w0 e) (spkKit.getErr.w1 e) (spkKit.getErr.w2 e)
    (spkKit.getErr.w3 e) (spkKit.getErr.w4 e) (spkKit.getErr.w5 e) (spkKit.getErr.w1 e) outPtr
    b_2c0 b_390 b_4f2 g recG recSt
    (spkKit.getErr.w0_ne_pending e) (spkKit.getErr.w0_ne_ok e) rfl
    hCode3 hsp3 hsp_lt hpc3 hrun3 hsp3_align
    hx10_3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3' hx26_3 hx27_3 hx28_3 hvregs3
  refine p2_bind_free_tr_evs_frame hfunnel (by sep_focus)
    fun evs_f sf _ hpcf hrunf hfree_f htrf ⟨hspf, hcsf, hvregsf, hCodef, _⟩ => ?_
  refine SepWPp.done hpcf hrunf ?_
  have hfree_all : FreeOnlyEvs (rustDeallocEvents spkKit.getBoxSize 8 ++ evs_f) :=
    (FreeOnlyEvs.singleton 8 spkKit.getBoxSize).append hfree_f
  refine ⟨rustDeallocEvents spkKit.getBoxSize 8 ++ evs_f, hfree_all,
    by rw [htrf, htr3_2, htr2_1, htr1], ?_, hspf, hcsf, hvregsf, hCodef,
    M.liveBytes_stepEvents_freeOnly_le hfree_all st⟩
  dsimp only [speErrAt]
  rw [M.stepEvents_append]
  sep_norm
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

theorem p2_over_arm1_err_hooks_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    {spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64}
    {spkEnv : SignedPreKeyStoreBudgetEnv spkKit}
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hDropSs3 : subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hspkOk : SignedPreKeyStoreKitPlacedOk A lim spkKit spkEnv ext)
    (s0 s : State) (sp coroPtr outPtr spkStorePtr spkFutPtr ctxPtr
    v_b0 u_90 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_d0 : BitVec 64)
    (signedPreKeyId : BitVec 32) (b_2c0 b_390 b_4f2 : BitVec 8) (e : spkKit.GetErr)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hCode : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_eq : s.sp = sp)
    (hsp_lt : dropSessionStructureLocal2Stack ≤ sp.toNat)
    (hpc : s.pc = stageP1EntryPlaced + 0xf38#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = coroPtr + 0x4f2#64) (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = coroPtr + 0x398#64) (hx27 : s.readReg64 .x27 = ctxPtr)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s
      (spkGetPollOutAt spkKit (sp + 0x3e0#64) (.error e) ∗ memRegion (sp + 0x438#64) 280 ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ spkFutPtr) ∗
       ((coroPtr + 0x500#64) ↦₆₄ (0#64 + spkKit.getFutVtOff)) ∗
       A.live spkFutPtr spkKit.getBoxSize 8 ∗
       spkKit.getBoxAt spkFutPtr spkStorePtr signedPreKeyId 1#8 ∗
       ((0#64 + spkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + spkKit.getFutDropOff)) ∗
       ((0#64 + spkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 spkKit.getBoxSize) ∗
       ((0#64 + spkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((sp + 0x90#64) ↦₆₄ u_90) ∗ ((sp + 0x98#64) ↦₆₄ u_98) ∗ ((sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((sp + 0xa8#64) ↦₆₄ u_a8) ∗ ((sp + 0xb0#64) ↦₆₄ u_b0) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((sp + 0xc0#64) ↦₆₄ u_c0) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       prevSessionsEmptyAt A.repAlloc coroPtr g ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
       cells (coroPtr + 0x250#64) 6 ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗ ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       memRegion (sp + 0x370#64) 36 ∗ cells (sp + 0xa90#64) 6 ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       memRegion outPtr 48 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st s ∗
       stackAt sp dropSessionStructureLocal2Stack)
      (fun sf P_f =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          sf.trace = s.trace ∧
          (P_f ⊢
            memRegion (sp + 0x3e0#64) 368 ∗
            ((coroPtr + 0x4f8#64) ↦₆₄ spkFutPtr) ∗
            ((coroPtr + 0x500#64) ↦₆₄ (0#64 + spkKit.getFutVtOff)) ∗
            ((0#64 + spkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + spkKit.getFutDropOff)) ∗
            ((0#64 + spkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 spkKit.getBoxSize) ∗
            ((0#64 + spkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
            ((sp + 0x90#64) ↦₆₄ spkKit.getErr.w5 e) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
            ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ spkKit.getErr.w4 e) ∗
            ((sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((sp + 0xb8#64) ↦₆₄ spkKit.getErr.w2 e) ∗
            ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
            ((sp + 0xd0#64) ↦₆₄ spkKit.getErr.w3 e) ∗
            memRegion (coroPtr + 0xe0#64) 368 ∗ cells (coroPtr + 0x250#64) 6 ∗
            ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
            ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
            memRegion (sp + 0x370#64) 36 ∗ cells (sp + 0xa90#64) 6 ∗
            decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
            speErrAt spkKit.getErr outPtr e ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt sp dropSessionStructureLocal2Stack) ∧
          sf.sp = sp + 0xcd0#64 ∧ ClosureCalleeSaved s0 sf ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
          LibsignalCodeRoLoaded lsmpl sf.mem ∧
          M.liveBytes (M.stepEvents evs st) ≤ M.liveBytes st)
      Qp :=
  p2_over_arm1_err_drop_hooks_placed_ok hH hDropSs3 (hspkOk.getFutDrop (by decide)) s0 s
    sp coroPtr outPtr spkStorePtr spkFutPtr ctxPtr
    v_b0 u_90 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_d0 signedPreKeyId b_2c0 b_390 b_4f2 e
    g recG recSt hCode hsp_eq hsp_lt hpc hrun hsp_align hx19 hx21 hx23 hx25 hx26 hx27 hvregs

abbrev p2_over_arm1_err_4k_placed_ok [LibsignalPlacement] :=
  @p2_over_arm1_err_hooks_placed_ok
abbrev p2_over_arm1_err_ext_placed_ok [LibsignalPlacement] :=
  @p2_over_arm1_err_hooks_placed_ok

set_option maxHeartbeats 1200000 in
/-- Budget-threaded Error Arm 2 (`+0x0998 → s0.readReg64 .x30`) from a direct `futDropBudgetSpec`
contract along `FreeOnlyEvs`. -/
theorem p2_over_arm2_err_drop_hooks_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    {kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64}
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hDropSs3 : subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hkpk_drop : subroutine_ok (stageP1ProgPlaced ext) (0#64 + kpkKit.getFutDropOff)
      (withLsRoCl lsmpl futDropBudgetSpec))
    (s0 s : State) (sp coroPtr outPtr kyberStorePtr kyberFutPtr ctxPtr
    v_b0 u_90 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_d0 : BitVec 64)
    (kyberPreKeyId : BitVec 32) (b_2c0 b_390 b_4f1 b_4f2 : BitVec 8) (e : kpkKit.GetErr)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hCode : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_eq : s.sp = sp)
    (hsp_lt : dropSessionStructureLocal2Stack ≤ sp.toNat)
    (hpc : s.pc = stageP1EntryPlaced + 0x998#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = coroPtr + 0x4f2#64) (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = coroPtr + 0x398#64) (hx27 : s.readReg64 .x27 = ctxPtr)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s
      (kpkGetPollOutAt kpkKit (sp + 0x3e0#64) (.error e) ∗ memRegion (sp + 0x438#64) 280 ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
       ((coroPtr + 0x500#64) ↦₆₄ (0#64 + kpkKit.getFutVtOff)) ∗
       A.live kyberFutPtr kpkKit.getBoxSize 8 ∗
       kpkKit.getBoxAt kyberFutPtr kyberStorePtr kyberPreKeyId 1#8 ∗
       ((0#64 + kpkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + kpkKit.getFutDropOff)) ∗
       ((0#64 + kpkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kpkKit.getBoxSize) ∗
       ((0#64 + kpkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((sp + 0x90#64) ↦₆₄ u_90) ∗ ((sp + 0x98#64) ↦₆₄ u_98) ∗ ((sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((sp + 0xa8#64) ↦₆₄ u_a8) ∗ ((sp + 0xb0#64) ↦₆₄ u_b0) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((sp + 0xc0#64) ↦₆₄ u_c0) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       prevSessionsEmptyAt A.repAlloc coroPtr g ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
       cells (coroPtr + 0x250#64) 6 ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗ ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗ memRegion (sp + 0x370#64) 36 ∗
       cells (sp + 0xa90#64) 6 ∗ decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       memRegion outPtr 48 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st s ∗
       stackAt sp dropSessionStructureLocal2Stack)
      (fun sf P_f =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          sf.trace = s.trace ∧
          (P_f ⊢
            memRegion (sp + 0x3e0#64) 368 ∗
            ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
            ((coroPtr + 0x500#64) ↦₆₄ (0#64 + kpkKit.getFutVtOff)) ∗
            ((0#64 + kpkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + kpkKit.getFutDropOff)) ∗
            ((0#64 + kpkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kpkKit.getBoxSize) ∗
            ((0#64 + kpkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
            ((sp + 0x90#64) ↦₆₄ kpkKit.getErr.w5 e) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
            ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ kpkKit.getErr.w4 e) ∗
            ((sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((sp + 0xb8#64) ↦₆₄ kpkKit.getErr.w2 e) ∗
            ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
            ((sp + 0xd0#64) ↦₆₄ kpkKit.getErr.w3 e) ∗
            memRegion (coroPtr + 0xe0#64) 368 ∗ cells (coroPtr + 0x250#64) 6 ∗
            ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
            ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
            memRegion (sp + 0x370#64) 36 ∗ cells (sp + 0xa90#64) 6 ∗
            decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
            speErrAt kpkKit.getErr outPtr e ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt sp dropSessionStructureLocal2Stack) ∧
          sf.sp = sp + 0xcd0#64 ∧ ClosureCalleeSaved s0 sf ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
          LibsignalCodeRoLoaded lsmpl sf.mem ∧
          M.liveBytes (M.stepEvents evs st) ≤ M.liveBytes st)
      Qp := by
  have hdss_le : dropSessionStructureLocal2Stack ≤ 2 ^ 64 :=
    Nat.le_trans hsp_lt (Nat.le_of_lt sp.isLt)
  dsimp only [kpkGetPollOutAt]
  refine weaken_frame (p2_err88_to_preKeyRecordOut64 kpkKit.getErr (sp + 0x3e0#64) e)
    (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u_418 => ?_
  have hstep1 := p2_err2a_ext_placed_wp ext s coroPtr kyberFutPtr
    (0#64 + kpkKit.getFutVtOff) (0#64 + kpkKit.getFutDropOff) (kpkKit.getErr.w0 e)
    (coroPtr + 0x398#64) (coroPtr + 0x4f2#64) v_b0 u_90 u_98 u_a0 u_a8 u_b0 u_b8 u_d0
    (kpkKit.getErr.w1 e) (kpkKit.getErr.w2 e) (kpkKit.getErr.w3 e)
    (kpkKit.getErr.w4 e) (kpkKit.getErr.w5 e) u_418
    (kpkKit.getFutDrop_ne_zero rfl) hpc hrun hsp_align hx19 hx21 hx23 hx26
  rw [hsp_eq, BitVec.add_zero] at hstep1
  refine p2_bind_sepWP_qp_frame_placed hCode hstep1 (by sep_focus)
    fun s1 _ hpc1 hrun1 hCode1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, _, hx19_1, _, hx21_1, hx22_1, hx23_1, hx24_1,
    hx25_1, _, hx27_1, hx28_1, _, hx30_1, hvregs1, hvm1⟩
  have hsp1_al : s1.spAligned = true := by simp only [State.spAligned, hsp1, ← hsp_eq]; exact hsp_align
  refine weaken_frame (p2_memRegion_420_join sp) (by sep_focus) ?_
  refine weaken_frame
    (p2_preKeyRecordOut64_to_memRegion368 sp 0xffffffffffffffff#64
      (kpkKit.getErr.w0 e) (kpkKit.getErr.w1 e) (kpkKit.getErr.w2 e)
      (kpkKit.getErr.w3 e) (kpkKit.getErr.w4 e) (kpkKit.getErr.w5 e) u_418)
    (by sep_focus) ?_
  refine p2_call_nopanic_rocl_steps_frame_placed (spec := futDropBudgetSpec) (x := ()) (T := emp)
    hCode1 hkpk_drop hpc1 hrun1 hsp1_al hx30_1
    (by dsimp only [futDropBudgetSpec]; exact (pure_true_sepConj emp).symm)
    True.intro (by sep_focus)
    (hnext := fun s2 _ hpc2 hrun2 hsp2_1 _ hcs2 hCode2 => ?_)
  dsimp only [futDropBudgetSpec]
  refine SepWPp.pure_elim fun ⟨htr2_1, hvm2_1⟩ => ?_
  have hvm2 : VmPreserved s s2 := hvm1.trans hvm2_1
  refine SepWPp.transport_budgetPool hvm2 (by sep_focus) ?_
  have hsp2 : s2.sp = sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2, ← hsp_eq]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, _, hx21_cs2, hx22_cs2, hx23_cs2, hx24_cs2,
    hx25_cs2, _, hx27_cs2, hx28_cs2, _, hvregs2_1⟩
  refine weaken_frame
    (kpkKit.getBoxAt_memRegion kyberFutPtr kyberStorePtr kyberPreKeyId 1#8) (by sep_focus) ?_
  refine weaken_frame (Entails.of_eq (stack_dropSS_to_alloc sp hdss_le)) (by sep_focus) ?_
  have hstep3 := p2_err2b_hooks_placed_wp (st := st) ext hH s2 coroPtr kyberFutPtr
    (0#64 + kpkKit.getFutVtOff) outPtr
    (kpkKit.getErr.w0 e) (kpkKit.getErr.w1 e) (kpkKit.getErr.w2 e)
    (kpkKit.getErr.w4 e) (kpkKit.getErr.w5 e) ctxPtr u_c0 b_4f1 kpkKit.getBoxSize
    kpkKit.getBoxSize_ne_zero kpkKit.getBoxSize_lt hpc2 hrun2 hsp2_align
    (hx19_cs2.trans hx19_1) (hx21_cs2.trans hx21_1) (hx22_cs2.trans hx22_1)
    (hx23_cs2.trans hx23_1) (hx24_cs2.trans hx24_1)
    (hx27_cs2.trans (hx27_1.trans hx27)) (hx28_cs2.trans hx28_1)
  rw [hsp2] at hstep3
  simp only [BitVec.add_assoc] at hstep3
  refine p2_bind_sepWP_qp_frame_state_placed hCode2 hstep3 (by sep_focus)
    fun s3 _ hpc3 hrun3 hCode3 hregs3 => ?_
  refine weaken_frame (Entails.of_eq (stack_dropSS_to_alloc sp hdss_le).symm) (by sep_focus) ?_
  rcases hregs3 with ⟨hsp3, htr3_2, hx10_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3,
    hx25_3, hx26_3, hx27_3, hx28_3, _, hvregs3_2, _hlive3⟩
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3, ← hsp_eq]; exact hsp_align
  have hx25_3' : s3.readReg64 .x25 = sp + 0x210#64 := by rw [hx25_3, hx25_cs2, hx25_1, hx25]
  have hvregs3 : calleeSavedVRegs s3 = calleeSavedVRegs s0 := by
    rw [hvregs3_2, hvregs2_1, hvregs1, hvregs]
  change s3.pc = stageP1EntryPlaced + 0x1648#64 at hpc3
  have hfunnel := stageP2_over_err_funnel_hooks_placed_ok
    (st := M.stepEvents (rustDeallocEvents kpkKit.getBoxSize 8) st)
    (Qp := fun _ _ => False)
    hH hDropSs3 s0 s3 sp coroPtr outPtr
    (kpkKit.getErr.w0 e) (kpkKit.getErr.w1 e) (kpkKit.getErr.w2 e)
    (kpkKit.getErr.w3 e) (kpkKit.getErr.w4 e) (kpkKit.getErr.w5 e)
    (((kpkKit.getErr.w1 e).extractLsb' 0 32).zeroExtend 64) outPtr
    b_2c0 b_390 b_4f2 g recG recSt
    (kpkKit.getErr.w0_ne_pending e) (kpkKit.getErr.w0_ne_ok e)
    (p2_zeroExtend32_extractLsb_lo (kpkKit.getErr.w1 e))
    hCode3 hsp3 hsp_lt hpc3 hrun3 hsp3_align
    hx10_3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3' hx26_3 hx27_3 hx28_3 hvregs3
  refine p2_bind_free_tr_evs_frame hfunnel (by sep_focus)
    fun evs_f sf _ hpcf hrunf hfree_f htrf ⟨hspf, hcsf, hvregsf, hCodef, _⟩ => ?_
  refine SepWPp.done hpcf hrunf ?_
  have hfree_all : FreeOnlyEvs (rustDeallocEvents kpkKit.getBoxSize 8 ++ evs_f) :=
    (FreeOnlyEvs.singleton 8 kpkKit.getBoxSize).append hfree_f
  refine ⟨rustDeallocEvents kpkKit.getBoxSize 8 ++ evs_f, hfree_all,
    by rw [htrf, htr3_2, htr2_1, htr1], ?_, hspf, hcsf, hvregsf, hCodef,
    M.liveBytes_stepEvents_freeOnly_le hfree_all st⟩
  dsimp only [speErrAt]
  rw [M.stepEvents_append]
  sep_norm
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

theorem p2_over_arm2_err_hooks_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    {kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64}
    {kpkEnv : KyberPreKeyStoreBudgetEnv kpkKit}
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hDropSs3 : subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hkpkOk : KyberPreKeyStoreKitPlacedOk A lim kpkKit kpkEnv ext)
    (s0 s : State) (sp coroPtr outPtr kyberStorePtr kyberFutPtr ctxPtr
    v_b0 u_90 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_d0 : BitVec 64)
    (kyberPreKeyId : BitVec 32) (b_2c0 b_390 b_4f1 b_4f2 : BitVec 8) (e : kpkKit.GetErr)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hCode : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_eq : s.sp = sp)
    (hsp_lt : dropSessionStructureLocal2Stack ≤ sp.toNat)
    (hpc : s.pc = stageP1EntryPlaced + 0x998#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = coroPtr + 0x4f2#64) (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = coroPtr + 0x398#64) (hx27 : s.readReg64 .x27 = ctxPtr)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s
      (kpkGetPollOutAt kpkKit (sp + 0x3e0#64) (.error e) ∗ memRegion (sp + 0x438#64) 280 ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
       ((coroPtr + 0x500#64) ↦₆₄ (0#64 + kpkKit.getFutVtOff)) ∗
       A.live kyberFutPtr kpkKit.getBoxSize 8 ∗
       kpkKit.getBoxAt kyberFutPtr kyberStorePtr kyberPreKeyId 1#8 ∗
       ((0#64 + kpkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + kpkKit.getFutDropOff)) ∗
       ((0#64 + kpkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kpkKit.getBoxSize) ∗
       ((0#64 + kpkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((sp + 0x90#64) ↦₆₄ u_90) ∗ ((sp + 0x98#64) ↦₆₄ u_98) ∗ ((sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((sp + 0xa8#64) ↦₆₄ u_a8) ∗ ((sp + 0xb0#64) ↦₆₄ u_b0) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((sp + 0xc0#64) ↦₆₄ u_c0) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       prevSessionsEmptyAt A.repAlloc coroPtr g ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
       cells (coroPtr + 0x250#64) 6 ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗ ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗ memRegion (sp + 0x370#64) 36 ∗
       cells (sp + 0xa90#64) 6 ∗ decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       memRegion outPtr 48 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st s ∗
       stackAt sp dropSessionStructureLocal2Stack)
      (fun sf P_f =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          sf.trace = s.trace ∧
          (P_f ⊢
            memRegion (sp + 0x3e0#64) 368 ∗
            ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
            ((coroPtr + 0x500#64) ↦₆₄ (0#64 + kpkKit.getFutVtOff)) ∗
            ((0#64 + kpkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + kpkKit.getFutDropOff)) ∗
            ((0#64 + kpkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kpkKit.getBoxSize) ∗
            ((0#64 + kpkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
            ((sp + 0x90#64) ↦₆₄ kpkKit.getErr.w5 e) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
            ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ kpkKit.getErr.w4 e) ∗
            ((sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((sp + 0xb8#64) ↦₆₄ kpkKit.getErr.w2 e) ∗
            ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
            ((sp + 0xd0#64) ↦₆₄ kpkKit.getErr.w3 e) ∗
            memRegion (coroPtr + 0xe0#64) 368 ∗ cells (coroPtr + 0x250#64) 6 ∗
            ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
            ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
            memRegion (sp + 0x370#64) 36 ∗ cells (sp + 0xa90#64) 6 ∗
            decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
            speErrAt kpkKit.getErr outPtr e ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt sp dropSessionStructureLocal2Stack) ∧
          sf.sp = sp + 0xcd0#64 ∧ ClosureCalleeSaved s0 sf ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
          LibsignalCodeRoLoaded lsmpl sf.mem ∧
          M.liveBytes (M.stepEvents evs st) ≤ M.liveBytes st)
      Qp :=
  p2_over_arm2_err_drop_hooks_placed_ok hH hDropSs3 (hkpkOk.getFutDrop (by decide)) s0 s
    sp coroPtr outPtr kyberStorePtr kyberFutPtr ctxPtr
    v_b0 u_90 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_d0 kyberPreKeyId b_2c0 b_390 b_4f1 b_4f2 e
    g recG recSt hCode hsp_eq hsp_lt hpc hrun hsp_align hx19 hx21 hx23 hx25 hx26 hx27 hvregs

abbrev p2_over_arm2_err_4k_placed_ok [LibsignalPlacement] :=
  @p2_over_arm2_err_hooks_placed_ok
abbrev p2_over_arm2_err_ext_placed_ok [LibsignalPlacement] :=
  @p2_over_arm2_err_hooks_placed_ok

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2ErrAPlacedBudget
