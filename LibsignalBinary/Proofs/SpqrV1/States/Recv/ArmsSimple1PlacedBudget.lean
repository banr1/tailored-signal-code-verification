/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceivedStepsPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSimple1Placed
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSimple1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WP.FrameAuto
import ProofLib.SepLogic.WPFrozen
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` (Block `332`): Budget-Threaded `KeysUnsampled` Arm & Shared Epilogue

Relocatable `[LibsignalPlacement]` `RustCliAllocBudget` proofs of the shared `+18996` `Ok(V1Recv)`
exit with `VmPreserved`, per-variant `subroutine_ok` bridges, and `States.keysUnsampled` (`+96`).
-/

@[expose] public section

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSimple1PlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement blkPC_332 blkPl_332 extract_withLsCodeLoaded lsProg_332
  lsmpl lsρ sepWP_seq_lscl withLsCodeLoaded
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open CryptoVerification.LibsignalSpqrV1 (Message MlKem States spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendEk (KeysUnsampled)
open CryptoVerification.LibsignalTripleRatchet (sessionMemcpySpec withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (RustAlloc allocHookStack)
open CryptoVerification.SpqrV1.Alloc (spqrMemcpySym spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Auth (authenticatorAt)
open CryptoVerification.SpqrV1.Drop (TwoVecGhost chunkedStatesAt chunkedStatesSize vecCapPtrDealloc)
open CryptoVerification.SpqrV1.States.Leaves (
  AuthWords authWordsList relocatedHeap subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
  wordsBytes
)
open CryptoVerification.SpqrV1.States.Recv (
  StatesRecvGhost TraceCalleeSaved cell48_4088_entails_memRegion_4144
  cells_456_504_entails_memRegion_4088 chunkedStatesAt_keysUnsampled_entails_dealloc
  chunkedStatesAt_keysUnsampled_extract chunkedStatesAt_keysUnsampled_unfold
  epilogueRecvOutPartA epilogueRecvOutPartB epilogueRecvOutPartB488 epilogueRecvOutPartB_eq_488
  epilogueRecvStackPartA epilogueRecvStackPartA488 epilogueRecvStackPartA_eq_488
  epilogueRecvStackPartB epilogueStack_224_512_entails_memRegion epilogue_entails_memRegion_3632
  epilogue_out_488_960_entails_memRegion_and_optNone err_epochOutOfRange_entails_resultV1RecvAt
  existsWordsAtOff keysUnsampled_out_recompose keysUnsampled_selfA_err_combine
  memRegion_3632_entails_epilogue memRegion_4088_split_456_504 memRegion_4144_split_cell48
  memRegion_472_entails_epilogue memRegion_off_eq_existsWordsAtOff memRegion_out_960_split_488_472
  memRegion_out_960_split_err optEpochSecretAt resultV1RecvAt selfA_8words_entails_memRegion_928
  sepWP_intro_ex sepWP_intro_ex_pure spqrDeallocSym stackAt_statesRecvCallee_eq_allocHook
  stack_recombine_4144 statesRecvArmOffset statesRecvCalleeStackX statesRecvPreInv
  statesRecvRoPlacedAt statesRecvSavedCells statesRecvStackX ule_false_of_gt ule_true_of_not_gt
  v1RecvSize wordsAtOff wordsAtOff_out_488_eq_epilogueOut
)
open CryptoVerification.SpqrV1.Top.MessageSerialize (messageAt messagePayloadAt)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget
  VmPreserved rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceivedStepsPlacedBudgetAux (
  seq_vm_clean seq_vm_cont
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlacedBudget (
  StatesRecvCalleeEnvs StatesRecvEnv StatesRecvPlacedContracts StatesRecvPlacedContractsOfEnv
  sepWPp_of_statesRecv_exit_cl_placed sepWPp_of_statesRecv_exit_cl_placed_ofEnv
  sepWPp_of_statesRecv_exit_cl_placed_ofPrePostEnv statesRecvVariantPlacedSpec
  statesRecvVariantPlacedSpecOfEnv statesRecvVariantPlacedSpecOfPrePostEnv
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlacedBudget (lsmpl_base_332_eq)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudgetAux (
  align_pre_st align_pre_vm deallocFreeOnlySpec sepWP_evs_dealloc sepWP_evs_nil sepWP_vm_evs_nil
  seq_evs_step subroutine_ok_deallocFreeOnly
)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (SpqrBoundedEvs)

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff CryptoVerification.blkPC_332
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit BitVec.toNat_zero
  RustCliAllocBudget.pool_setPC RustCliAllocBudget.pool_advancePC
  RustCliAllocBudget.pool_setPState RustCliAllocBudget.pool_writeReg64
  RustCliAllocBudget.pool_writeReg32 RustCliAllocBudget.pool_writeReg

local elab "by_vm_steps_nest " tac:Lean.Parser.Tactic.tacticSeq : tactic => do
  Lean.Elab.Tactic.evalTactic
    (← `(tactic| apply LibsignalBinary.Proofs.Placed.BudgetVmSteps.sepWP_rebase_vmPreserved))
  let g ← Lean.Elab.Tactic.getMainGoal
  g.withContext do
    let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
    let e2 := ty.getArg! 0
    let e1 := e2.getArg! 0
    let ty1 := Lean.mkAppN ty.getAppFn #[e1, ty.getArg! 1, ty.getArg! 2, ty.getArg! 3, ty.getArg! 4, ty.getArg! 5]
    let g1 ← Lean.Meta.mkFreshExprMVar ty1
    let savedGoals ← Lean.Elab.Tactic.getGoals
    Lean.Elab.Tactic.setGoals [g1.mvarId!]
    Lean.Elab.Tactic.evalTactic (← `(tactic| ($tac)))
    let rem ← Lean.Elab.Tactic.getGoals
    unless rem.isEmpty do
      Lean.Meta.throwTacticEx `by_vm_steps_nest g m!"inner tactic left {rem.length} unsolved goal(s)"
    Lean.Elab.Tactic.setGoals savedGoals.tail!
    let prf1 ← Lean.instantiateMVars g1
    let prf2 := prf1.replace fun sub =>
      if sub.isAppOfArity ``Arm64.Program.withSvc 2 then some sub
      else if sub.eqv e1 then some e2
      else none
    g.assign prf2

/-! ## Shared Sequencing & Envelope Helpers for `ArmsSimple{1,2,3}PlacedBudget` -/

theorem simple_seq_clean_lscl [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q sm → SepWP prog target sm P_mid post) :
    SepWP prog target s P post :=
  sepWP_seq_lscl hcl (SepWP.mono h1 fun sm _ hpc hrun ⟨hPm, hQ⟩ hcl' =>
    SepWP.weaken_pre hPm (h2 sm hpc hrun hcl' hQ))

theorem simple_seq_vm_lscl [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → VmPreserved s sm → Q sm →
      SepWP prog target sm P_mid post) :
    SepWP prog target s P post :=
  sepWP_seq_lscl hcl (SepWP.mono h1 fun sm _ hpc hrun ⟨hvm, hPm, hQ⟩ hcl' =>
    SepWP.weaken_pre hPm (h2 sm hpc hrun hcl' hvm hQ))

theorem FreeOnlyEvs_to_statesRecvEnv {F : ShaCompress}
    (x : StatesRecvGhost F) {evs : List AllocEvent} (h : FreeOnlyEvs evs) :
    StatesRecvEnv x evs :=
  SpqrBoundedEvs.mono (Nat.zero_le _) (Nat.zero_le _) (SpqrBoundedEvs.of_freeOnly h)

/-- binary post-envelope of `<States>::recv` on `States.keysUnsampled st` (`tag = 2#64`):
    deallocates at most the two `Authenticator` vectors on `msg.epoch > st.uc.epoch`, and performs
    zero allocator calls (`evs = []`) on `¬ (msg.epoch > st.uc.epoch)`. -/
def KeysUnsampledRecvPostEnv {F : ShaCompress}
    (st : KeysUnsampled (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (evs : List AllocEvent) : Prop :=
  if msg.epoch > st.uc.epoch then FreeOnlyEvs evs else evs = []

theorem KeysUnsampledRecvPostEnv_to_freeOnly {F : ShaCompress}
    {st : KeysUnsampled (spqrAuthApi F)} {msg : Message spqrPolyApi} {evs : List AllocEvent}
    (h : KeysUnsampledRecvPostEnv st msg evs) : FreeOnlyEvs evs := by
  unfold KeysUnsampledRecvPostEnv at h
  split at h
  · exact h
  · subst h; exact FreeOnlyEvs.nil

theorem KeysUnsampledRecvPostEnv_to_statesRecvEnv {F : ShaCompress}
    (outA selfA msgA : BitVec 64)
    (st : KeysUnsampled (spqrAuthApi F)) (msg : Message spqrPolyApi)
    {evs : List AllocEvent} (h : KeysUnsampledRecvPostEnv st msg evs) :
    StatesRecvEnv ⟨outA, selfA, msgA, .keysUnsampled st, msg⟩ evs :=
  FreeOnlyEvs_to_statesRecvEnv _ (KeysUnsampledRecvPostEnv_to_freeOnly h)

/-! ## `States.keysUnsampled` (`tag = 2#64`, `+96` / `0x554b4`) — Error Branch -/

theorem keysUnsampled_err_step_96_176_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st_cost : M.σ)
    (s : State) (fsp outA selfA msgA st_epoch msg_epoch v_out0 v_out16 v_fsp456 v_fsp504 : BitVec 64)
    (b_out8 : BitVec 8) (g : TwoVecGhost) (Frame : SepProp)
    (hgt : msg_epoch > st_epoch) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_332).base + 96#64) (hrun : s.status = .Running)
    (hsp : s.sp = fsp) (hx19 : s.readReg64 .x19 = outA)
    (hx1 : s.readReg64 .x1 = selfA) (hx24 : s.readReg64 .x24 = msgA) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 176#64) s
      (((outA ↦₆₄ v_out0) ∗ ((outA + 8#64) ↦₈ b_out8) ∗ ((outA + 16#64) ↦₆₄ v_out16)) ∗
       (((selfA + 8#64) ↦₆₄ g.v1.cap) ∗ ((selfA + 16#64) ↦₆₄ g.v1.ptr) ∗
        ((selfA + 32#64) ↦₆₄ g.v2.cap) ∗ ((selfA + 40#64) ↦₆₄ g.v2.ptr) ∗ ((selfA + 56#64) ↦₆₄ st_epoch)) ∗
       vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗ (msgA ↦₆₄ msg_epoch) ∗ A.pool lim st_cost s ∗
       stackAt fsp allocHookStack ∗ ((fsp + 456#64) ↦₆₄ v_fsp456) ∗ ((fsp + 504#64) ↦₆₄ v_fsp504) ∗ Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢ ((outA ↦₆₄ noneCap) ∗ ((outA + 8#64) ↦₈ 4#8) ∗ ((outA + 16#64) ↦₆₄ msg_epoch)) ∗
            (((selfA + 8#64) ↦₆₄ g.v1.cap) ∗ ((selfA + 16#64) ↦₆₄ g.v1.ptr) ∗
             ((selfA + 32#64) ↦₆₄ g.v2.cap) ∗ ((selfA + 40#64) ↦₆₄ g.v2.ptr) ∗ ((selfA + 56#64) ↦₆₄ st_epoch)) ∗
            (msgA ↦₆₄ msg_epoch) ∗ A.pool lim (M.stepEvents evs st_cost) sm ∗ stackAt fsp allocHookStack ∗
            ((fsp + 456#64) ↦₆₄ g.v2.cap) ∗ ((fsp + 504#64) ↦₆₄ st_epoch) ∗ Frame) ∧
          sm.sp = fsp ∧ AllocCallPreserved s sm ∧ sm.readReg64 .x0 = g.v2.ptr ∧
          sm.readReg64 .x29 = s.readReg64 .x29 ∧ TraceCalleeSaved sm s) := by
  have hdealloc_raw : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ spqrDeallocSym) (deallocFreeOnlySpec M A lim) :=
    subroutine_ok_deallocFreeOnly (spqr_hook_ok_of_mem (sym := spqrDeallocSym) hdealloc)
  have hule : BitVec.ule msg_epoch st_epoch = false := ule_false_of_gt hgt
  dsimp only [lsProg_332, lsρ, spqrDeallocSym] at hdealloc_raw ⊢
  subst hsp hx19 hx1 hx24
  dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live, noneCap]
  by_cases hc1 : (g.v1.cap == 0#64) = true <;>
    simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · refine sepWP_vm_evs_nil (fun sm hvm => by
      simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, A.pool_of_vmPreserved hvm]) ?_
    by_vm_steps (
      wp_steps
      refine align_pre_vm (by
        simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, wp_norm, arm64_norm]
        try sep_ac_rfl) ?_
      simp only [AllocCallPreserved, TraceCalleeSaved, wp_norm, arm64_norm]
      wp_done)
  · apply sepWP_evs_dealloc g.v1.cap.toNat 1
    refine seq_vm_cont (mid := lsmpl.ρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") ?_
    by_vm_steps_nest (
      wp_steps
      refine SepWP.done rfl (by assumption) ⟨by simp only [wp_norm, arm64_norm], fun hvm1 => ?_⟩
      wp_conv_pre => rw [← A.pool_of_vmPreserved hvm1]
      wp_apply
      have hacp_1 : AllocCallPreserved s sf := by assumption
      rcases hacp_1 with ⟨_, _, _, _, _, _, _⟩
      wp_steps
      refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_
      wp_done)

set_option maxHeartbeats 1200000 in
/-- Relocatable budget-threaded error branch (`msg.epoch > st.uc.epoch`) of `States.keysUnsampled`
    (`+96 -> s0.readReg64 .x30`). -/
theorem states_recv_keysUnsampled_err_96_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st_cost : M.σ)
    (s0 s : State) (fsp outA selfA msgA v48 : BitVec 64)
    (st : KeysUnsampled (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hgt : msg.epoch > st.uc.epoch) (hfsp_eq : fsp = s0.sp - 4240#64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_332).base + 96#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = outA) (hx1 : s.readReg64 .x1 = selfA) (hx24 : s.readReg64 .x24 = msgA)
    (htr : TraceCalleeSaved s s0)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .x30) := by
      first
      | assumption
      | simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (memRegion outA v1RecvSize ∗ chunkedStatesAt A.repAlloc selfA (.keysUnsampled st) ∗
       messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool lim st_cost s ∗
       stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 48 ∗
       ((fsp + 48#64) ↦₆₄ v48) ∗ memRegion (fsp + 56#64) 4088 ∗ statesRecvSavedCells s0)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢ resultV1RecvAt A.repAlloc (F := F) outA ((States.keysUnsampled st).recv K msg) ∗
            memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
            statesRecvRoPlacedAt ∗ A.pool lim (M.stepEvents evs st_cost) sf ∗
            stackAt s0.sp statesRecvStackX) ∧
          sf.sp = s0.sp ∧ AllocCallPreserved s sf ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hrecv : (States.keysUnsampled st).recv K msg = .error (.err (.epochOutOfRange msg.epoch)) := by
    simp only [States.recv, KeysUnsampled.epoch,
      CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.KeysUnsampled.epoch, hgt, ↓reduceIte]
  rw [hrecv, memRegion_out_960_split_err outA, memRegion_4088_split_456_504 fsp,
    stackAt_statesRecvCallee_eq_allocHook fsp]
  refine SepWP.fold (chunkedStatesAt_keysUnsampled_entails_dealloc A.repAlloc selfA st) (by sep_focus) ?_
  unfold messageAt; wp_pull_exists; rename_i v_fsp504 v_fsp456 v_out16 b_out8 v_out0 g
  have hstep1 := keysUnsampled_err_step_96_176_placed hdealloc st_cost s fsp outA selfA msgA
    st.uc.epoch msg.epoch v_out0 v_out16 v_fsp456 v_fsp504 b_out8 g
    (memRegion (outA + 9#64) 7 ∗ memRegion (outA + 24#64) 936 ∗
     (selfA ↦₆₄ 2#64) ∗ memRegion (selfA + 24#64) 8 ∗ memRegion (selfA + 48#64) 8 ∗
     memRegion (selfA + 64#64) 864 ∗ vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
     messagePayloadAt spqrPolyApi msgA msg.payload ∗ statesRecvRoPlacedAt ∗
     memRegion (fsp - 19552#64) 15456 ∗ memRegion fsp 48 ∗ ((fsp + 48#64) ↦₆₄ v48) ∗
     memRegion (fsp + 56#64) 400 ∗ memRegion (fsp + 464#64) 40 ∗ memRegion (fsp + 512#64) 3632 ∗
     statesRecvSavedCells s0) hgt hfsp_align hpc hrun hsp hx19 hx1 hx24
  let errOut := resultV1RecvAt A.repAlloc (F := F) outA (.error (.err (.epochOutOfRange msg.epoch)))
  refine SepWP.mono
    (seq_evs_step (M := M) (A := A) (lim := lim) (st := st_cost)
      (mid := (blkPl_332).base + 176#64)
      (X1 := errOut ∗ memRegion selfA chunkedStatesSize ∗
        messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt)
      (X2 := stackAt s0.sp statesRecvStackX)
      (P_mid := fun st1 sm =>
        ((outA ↦₆₄ noneCap) ∗ ((outA + 8#64) ↦₈ 4#8) ∗ ((outA + 16#64) ↦₆₄ msg.epoch)) ∗
        (((selfA + 8#64) ↦₆₄ g.v1.cap) ∗ ((selfA + 16#64) ↦₆₄ g.v1.ptr) ∗
         ((selfA + 32#64) ↦₆₄ g.v2.cap) ∗ ((selfA + 40#64) ↦₆₄ g.v2.ptr) ∗ ((selfA + 56#64) ↦₆₄ st.uc.epoch)) ∗
        (msgA ↦₆₄ msg.epoch) ∗ A.pool lim st1 sm ∗ stackAt fsp allocHookStack ∗
        ((fsp + 456#64) ↦₆₄ g.v2.cap) ∗ ((fsp + 504#64) ↦₆₄ st.uc.epoch) ∗
        (memRegion (outA + 9#64) 7 ∗ memRegion (outA + 24#64) 936 ∗
         (selfA ↦₆₄ 2#64) ∗ memRegion (selfA + 24#64) 8 ∗ memRegion (selfA + 48#64) 8 ∗
         memRegion (selfA + 64#64) 864 ∗ vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
         messagePayloadAt spqrPolyApi msgA msg.payload ∗ statesRecvRoPlacedAt ∗
         memRegion (fsp - 19552#64) 15456 ∗ memRegion fsp 48 ∗ ((fsp + 48#64) ↦₆₄ v48) ∗
         memRegion (fsp + 56#64) 400 ∗ memRegion (fsp + 464#64) 40 ∗ memRegion (fsp + 512#64) 3632 ∗
         statesRecvSavedCells s0))
      (Q_mid := fun sm =>
        sm.sp = fsp ∧ AllocCallPreserved s sm ∧ sm.readReg64 .x0 = g.v2.ptr ∧
        sm.readReg64 .x29 = s0.sp - 96#64 ∧ TraceCalleeSaved sm s0)
      (Q_out := fun sf =>
        sf.sp = s0.sp ∧ AllocCallPreserved s sf ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (by
        refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.mono hstep1 ?_)
        intro sm Pm _ _ ⟨evs1, hevs1, hPm, hsp1, hacp1, hx0_1, hx29_1, htr1⟩
        exact ⟨evs1, hevs1, hPm, hsp1, hacp1, hx0_1, hx29_1.trans hx29, htr1.trans htr⟩)
      ?_)
    (fun sf Pf _ _ ⟨evs, hevs, hPf, hq⟩ =>
      ⟨evs, hevs, Entails.trans hPf (Entails.of_eq (by dsimp only [errOut, messageAt]; sep_ac_rfl)), hq⟩)
  intro st1 s1 hpc1 hrun1 ⟨hsp1, hacp1, hx0_1, hx29_1, htr1⟩
  refine SepWP.fold (Entails.of_eq (stackAt_statesRecvCallee_eq_allocHook fsp).symm) (by sep_focus) ?_
  refine SepWP.fold (err_epochOutOfRange_entails_resultV1RecvAt A.repAlloc (F := F) outA msg.epoch) (by sep_focus) ?_
  refine SepWP.fold (keysUnsampled_selfA_err_combine selfA g.v1.cap g.v1.ptr g.v2.cap g.v2.ptr st.uc.epoch) (by sep_focus) ?_
  have hepil_fn := @DispatchPlacedBudget.states_recv_epilogue_19324_pool_placed _ M A lim ext st1 s0
  have htail_fn := @DispatchPlacedBudget.states_recv_tail_dealloc_192_placed _ M A lim ext hdealloc st1 s0
  rw [lsmpl_base_332_eq] at hepil_fn htail_fn
  dsimp only [lsProg_332] at hepil_fn htail_fn ⊢
  subst hsp1
  dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
  by_cases hc2 : (g.v2.cap == 0#64) = true <;>
    simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · refine sepWP_evs_nil ?_
    dsimp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
    refine seq_vm_clean (mid := (blkPl_332).base + 19324#64)
      (P_mid :=
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        A.pool lim st1 s1 ∗
        (errOut ∗ memRegion selfA chunkedStatesSize ∗
         messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt))
      (Q := fun sm => sm.sp = s0.sp - 4240#64 ∧ AllocCallPreserved s1 sm ∧ TraceCalleeSaved sm s0)
      ?_ ?_
    · refine SepWP.mono (post := fun sm Pm =>
          VmPreserved s1 sm ∧
          (Pm ⊢
            (errOut ∗ stackAt s1.sp statesRecvCalleeStackX ∗ memRegion selfA chunkedStatesSize) ∗
            (msgA ↦₆₄ msg.epoch) ∗ A.pool lim st1 s1 ∗
            ((s1.sp + 456#64) ↦₆₄ g.v2.cap) ∗ ((s1.sp + 504#64) ↦₆₄ st.uc.epoch) ∗
            messagePayloadAt spqrPolyApi msgA msg.payload ∗ statesRecvRoPlacedAt ∗
            memRegion s1.sp 48 ∗ ((s1.sp + 48#64) ↦₆₄ v48) ∗ memRegion (s1.sp + 56#64) 400 ∗
            memRegion (s1.sp + 464#64) 40 ∗ memRegion (s1.sp + 512#64) 3632 ∗ statesRecvSavedCells s0) ∧
          (sm.sp = s0.sp - 4240#64 ∧ AllocCallPreserved s1 sm ∧ TraceCalleeSaved sm s0))
        (by
          by_vm_steps (
            wp_steps
            refine align_pre_vm (by dsimp only [errOut]; simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_
            simp only [AllocCallPreserved, TraceCalleeSaved, hfsp_eq, htr1.1, htr1.2, wp_norm, arm64_norm]
            wp_done))
        (fun sm Pm _ _ ⟨hvm_m, hPm, hq⟩ => by
          refine ⟨hvm_m, Entails.trans hPm ?_, hq⟩
          have hc4088 := cells_456_504_entails_memRegion_4088 s1.sp g.v2.cap st.uc.epoch
          have hc4144 := cell48_4088_entails_memRegion_4144 s1.sp v48
          rw [hfsp_eq] at hc4088 hc4144 ⊢
          unfold messageAt
          refine Entails.trans (Entails.of_eq (show _ =
            (memRegion (s0.sp - 4240#64 + 56#64) 400 ∗
             ((s0.sp - 4240#64 + 456#64) ↦₆₄ g.v2.cap) ∗
             memRegion (s0.sp - 4240#64 + 464#64) 40 ∗
             ((s0.sp - 4240#64 + 504#64) ↦₆₄ st.uc.epoch) ∗
             memRegion (s0.sp - 4240#64 + 512#64) 3632) ∗
            (memRegion (s0.sp - 4240#64) 48 ∗ ((s0.sp - 4240#64 + 48#64) ↦₆₄ v48)) ∗
            (stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗
             A.pool lim st1 s1 ∗ errOut ∗ memRegion selfA chunkedStatesSize ∗
             ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
             statesRecvRoPlacedAt) by sep_ac_rfl)) ?_
          refine Entails.trans (sepConj_mono_left hc4088) ?_
          refine Entails.trans (Entails.of_eq (show _ =
            (memRegion (s0.sp - 4240#64) 48 ∗
             ((s0.sp - 4240#64 + 48#64) ↦₆₄ v48) ∗
             memRegion (s0.sp - 4240#64 + 56#64) 4088) ∗
            (stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗
             A.pool lim st1 s1 ∗
             (errOut ∗ memRegion selfA chunkedStatesSize ∗
              ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
              statesRecvRoPlacedAt)) by sep_ac_rfl)) ?_
          exact Entails.trans (sepConj_mono_left hc4144) (Entails.of_eq (by sep_ac_rfl)))
    · intro sm hpcm hrunm hvm_m ⟨hsp_m, hacp_m, htr_m⟩
      rw [← A.pool_of_vmPreserved hvm_m]
      refine SepWP.mono
        (hepil_fn sm
          (errOut ∗ memRegion selfA chunkedStatesSize ∗
           messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt)
          hsp0_align hpcm hrunm hsp_m htr_m)
        fun sf Pf _ _ ⟨_, hPf, hspf, hacp_ep, hcs, htrf⟩ =>
          ⟨Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)),
           hspf, hacp1.trans (hacp_m.trans hacp_ep), hcs, htrf⟩
  · refine seq_vm_clean (mid := (blkPl_332).base + 192#64)
      (P_mid :=
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        A.live g.v2.ptr g.v2.cap.toNat 1 ∗
        memRegion g.v2.ptr g.v2.cap.toNat ∗
        A.pool lim st1 s1 ∗
        (errOut ∗ memRegion selfA chunkedStatesSize ∗
         messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt))
      (Q := fun sm =>
        sm.sp = s0.sp - 4240#64 ∧
        sm.readReg64 .x0 = g.v2.ptr ∧
        sm.readReg64 .x1 = g.v2.cap ∧
        sm.readReg64 .x2 = 1#64 ∧
        AllocCallPreserved s1 sm ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · refine SepWP.mono (post := fun sm Pm =>
          VmPreserved s1 sm ∧
          (Pm ⊢
            (errOut ∗ stackAt s1.sp statesRecvCalleeStackX ∗ memRegion selfA chunkedStatesSize) ∗
            (msgA ↦₆₄ msg.epoch) ∗ A.pool lim st1 s1 ∗
            ((s1.sp + 456#64) ↦₆₄ g.v2.cap) ∗ ((s1.sp + 504#64) ↦₆₄ st.uc.epoch) ∗
            (A.live g.v2.ptr g.v2.cap.toNat 1 ∗ memRegion g.v2.ptr g.v2.cap.toNat) ∗
            messagePayloadAt spqrPolyApi msgA msg.payload ∗ statesRecvRoPlacedAt ∗
            memRegion s1.sp 48 ∗ ((s1.sp + 48#64) ↦₆₄ v48) ∗ memRegion (s1.sp + 56#64) 400 ∗
            memRegion (s1.sp + 464#64) 40 ∗ memRegion (s1.sp + 512#64) 3632 ∗ statesRecvSavedCells s0) ∧
          (sm.sp = s0.sp - 4240#64 ∧
           sm.readReg64 .x0 = g.v2.ptr ∧
           sm.readReg64 .x1 = g.v2.cap ∧
           sm.readReg64 .x2 = 1#64 ∧
           AllocCallPreserved s1 sm ∧
           TraceCalleeSaved sm s0))
        (by
          by_vm_steps (
            wp_steps
            refine align_pre_vm (by dsimp only [errOut]; simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_
            simp only [AllocCallPreserved, TraceCalleeSaved, hfsp_eq, hx0_1, htr1.1, htr1.2, wp_norm, arm64_norm]
            wp_done))
        (fun sm Pm _ _ ⟨hvm_m, hPm, hq⟩ => by
          refine ⟨hvm_m, Entails.trans hPm ?_, hq⟩
          have hc4088 := cells_456_504_entails_memRegion_4088 s1.sp g.v2.cap st.uc.epoch
          have hc4144 := cell48_4088_entails_memRegion_4144 s1.sp v48
          rw [hfsp_eq] at hc4088 hc4144 ⊢
          unfold messageAt
          refine Entails.trans (Entails.of_eq (show _ =
            (memRegion (s0.sp - 4240#64 + 56#64) 400 ∗
             ((s0.sp - 4240#64 + 456#64) ↦₆₄ g.v2.cap) ∗
             memRegion (s0.sp - 4240#64 + 464#64) 40 ∗
             ((s0.sp - 4240#64 + 504#64) ↦₆₄ st.uc.epoch) ∗
             memRegion (s0.sp - 4240#64 + 512#64) 3632) ∗
            (memRegion (s0.sp - 4240#64) 48 ∗ ((s0.sp - 4240#64 + 48#64) ↦₆₄ v48)) ∗
            (stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗
             A.live g.v2.ptr g.v2.cap.toNat 1 ∗ memRegion g.v2.ptr g.v2.cap.toNat ∗
             A.pool lim st1 s1 ∗ errOut ∗ memRegion selfA chunkedStatesSize ∗
             ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
             statesRecvRoPlacedAt) by sep_ac_rfl)) ?_
          refine Entails.trans (sepConj_mono_left hc4088) ?_
          refine Entails.trans (Entails.of_eq (show _ =
            (memRegion (s0.sp - 4240#64) 48 ∗
             ((s0.sp - 4240#64 + 48#64) ↦₆₄ v48) ∗
             memRegion (s0.sp - 4240#64 + 56#64) 4088) ∗
            (stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗
             A.live g.v2.ptr g.v2.cap.toNat 1 ∗ memRegion g.v2.ptr g.v2.cap.toNat ∗
             A.pool lim st1 s1 ∗
             (errOut ∗ memRegion selfA chunkedStatesSize ∗
              ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
              statesRecvRoPlacedAt)) by sep_ac_rfl)) ?_
          exact Entails.trans (sepConj_mono_left hc4144) (Entails.of_eq (by sep_ac_rfl)))
    · intro sm hpcm hrunm hvm_m ⟨hsp_m, hx0_m, hx1_m, hx2_m, hacp_m, htr_m⟩
      rw [← A.pool_of_vmPreserved hvm_m]
      refine SepWP.mono
        (htail_fn sm g.v2.ptr g.v2.cap
          (errOut ∗ memRegion selfA chunkedStatesSize ∗
           messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt)
          hsp0_align hpcm hrunm hsp_m hx0_m hx1_m hx2_m htr_m hlr_ls)
        fun sf Pf _ _ ⟨evs2, hevs2, hPf, hspf, hacp_tl, hcs, htrf⟩ =>
          ⟨evs2, hevs2, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)),
           hspf, hacp1.trans (hacp_m.trans hacp_tl), hcs, htrf⟩

/-! ## Shared `Ok(V1Recv)` Store Epilogue (`+18996 -> s0.readReg64 .x30`) for `key = none`, 488-Byte Variants -/

set_option maxHeartbeats 1600000 in
/-- Relocatable shared `Ok(V1Recv)` exit from `+18996` (`+18996 -> s0.readReg64 .x30`) when `key = none`
    (`[fsp + 232] = noneCap`) and the output `States` variant fits in the first 488 bytes of `out`,
    establishing `VmPreserved s1 sf`. -/
theorem epilogue_18996_exit_none_488_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (s0 s1 : State) (out : BitVec 64)
    (w224 w240 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 : BitVec 64)
    (w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488 : BitVec 64)
    (Rest : SepProp) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (blkPl_332).base + 18996#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 4240#64)
    (hx19 : s1.readReg64 .x19 = out) (htr1 : TraceCalleeSaved s1 s0) :
    let fsp := s0.sp - 4240#64
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 224 ∗
       epilogueRecvStackPartA488 fsp w224 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 ∗
       ((fsp + 232#64) ↦₆₄ noneCap) ∗ ((fsp + 240#64) ↦₆₄ w240) ∗
       epilogueRecvStackPartB fsp w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488 ∗
       memRegion (fsp + 512#64) 3632 ∗ statesRecvSavedCells s0 ∗ memRegion out v1RecvSize ∗ Rest)
      (fun sf Pf =>
        VmPreserved s1 sf ∧
        (Pf ⊢
          epilogueRecvOutPartA out
            w224 (s1.readReg64 .x1) (s1.readReg64 .x8) w496 w456 w376 w368 w504 w288 w432 w408 w352 w384 w336 w296
            (s1.readReg64 .x25) (s1.readReg64 .x12) (s1.readReg64 .x11) (s1.readReg64 .x10)
            (s1.readReg64 .x15) (s1.readReg64 .x28) (s1.readReg64 .x7) (s1.readReg64 .x0)
            (s1.readReg64 .x6) (s1.readReg64 .x30) (s1.readReg64 .x21) (s1.readReg64 .x9)
            (s1.readReg64 .x5) (s1.readReg64 .x4) (s1.readReg64 .x13) (s1.readReg64 .x14) ∗
          epilogueRecvOutPartB488 out
            w424 (s1.readReg64 .x23) (s1.readReg64 .x27) w440 w264 w344 w392 w272 w360 w400 w464 w304
            w328 w280 w320 (s1.readReg64 .x3) w312 (s1.readReg64 .x24) w416 (s1.readReg64 .x17) w472 (s1.readReg64 .x26)
            w448 (s1.readReg64 .x22) w480 (s1.readReg64 .x16) w488 (s1.readReg64 .x2) w248 (s1.readReg64 .x20) ∗
          memRegion (out + 488#64) 440 ∗ optEpochSecretAt A (out + 928#64) none ∗ Rest ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  intro fsp
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  have hout0 : memRegion out 488 = existsWordsAtOff out 61 0 := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceMul] using memRegion_off_eq_existsWordsAtOff out 61 0 (by decide)
  rw [memRegion_out_960_split_488_472 out, hout0]
  have hpre :
      stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 224 ∗
       epilogueRecvStackPartA488 fsp w224 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 ∗
       ((fsp + 232#64) ↦₆₄ noneCap) ∗ ((fsp + 240#64) ↦₆₄ w240) ∗
       epilogueRecvStackPartB fsp w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488 ∗
       memRegion (fsp + 512#64) 3632 ∗ statesRecvSavedCells s0 ∗
       (existsWordsAtOff out 61 0 ∗ memRegion (out + 488#64) 472) ∗ Rest ⊢
      ((∃∗ q512 : BitVec 128, (fsp + 512#64) ↦₁₂₈ q512) ∗ (∃∗ q528 : BitVec 128, (fsp + 528#64) ↦₁₂₈ q528) ∗
       (∃∗ q544 : BitVec 128, (fsp + 544#64) ↦₁₂₈ q544) ∗ (∃∗ w560 : BitVec 64, (fsp + 560#64) ↦₆₄ w560) ∗
       (∃∗ bs576 : List (BitVec 8), ⌜bs576.length = 376⌝ ∗ ((fsp + 576#64) ↦ₛ bs576)) ∗
       (∃∗ q960 : BitVec 128, (fsp + 960#64) ↦₁₂₈ q960) ∗ (∃∗ uq488 : BitVec 128, (out + 488#64) ↦₁₂₈ uq488) ∗
       (∃∗ u504 : BitVec 64, (out + 504#64) ↦₆₄ u504) ∗ (∃∗ uq888 : BitVec 128, (out + 888#64) ↦₁₂₈ uq888) ∗
       (∃∗ uq904 : BitVec 128, (out + 904#64) ↦₁₂₈ uq904) ∗ (∃∗ u920 : BitVec 64, (out + 920#64) ↦₆₄ u920) ∗
       (∃∗ u928 : BitVec 64, (out + 928#64) ↦₆₄ u928) ∗ (∃∗ u936 : BitVec 64, (out + 936#64) ↦₆₄ u936) ∗
       (∃∗ uq944 : BitVec 128, (out + 944#64) ↦₁₂₈ uq944) ∗ existsWordsAtOff out 61 0) ∗
      (stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 224 ∗
       epilogueRecvStackPartA488 fsp w224 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 ∗
       ((fsp + 232#64) ↦₆₄ noneCap) ∗ ((fsp + 240#64) ↦₆₄ w240) ∗
       epilogueRecvStackPartB fsp w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488 ∗
       memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗ memRegion (fsp + 976#64) 3168 ∗
       statesRecvSavedCells s0 ∗ memRegion (out + 512#64) 376 ∗ Rest) :=
    Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono (memRegion_3632_entails_epilogue fsp)
        (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right (memRegion_472_entails_epilogue out)))))))))))
      (Entails.of_eq (by sep_ac_rfl))
  refine SepWP.weaken_pre hpre ?_
  dsimp only [existsWordsAtOff, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]; rw [BitVec.add_zero]
  apply sepWP_intro_ex; intro q512; apply sepWP_intro_ex; intro q528; apply sepWP_intro_ex; intro q544; apply sepWP_intro_ex; intro w560
  apply sepWP_intro_ex_pure; intro bs576 hbs576; apply sepWP_intro_ex; intro q960; apply sepWP_intro_ex; intro uq488; apply sepWP_intro_ex; intro u504
  apply sepWP_intro_ex; intro uq888; apply sepWP_intro_ex; intro uq904; apply sepWP_intro_ex; intro u920; apply sepWP_intro_ex; intro u928
  apply sepWP_intro_ex; intro u936; apply sepWP_intro_ex; intro uq944
  apply sepWP_intro_ex; intro u0; apply sepWP_intro_ex; intro u8; apply sepWP_intro_ex; intro u16; apply sepWP_intro_ex; intro u24; apply sepWP_intro_ex; intro u32; apply sepWP_intro_ex; intro u40
  apply sepWP_intro_ex; intro u48; apply sepWP_intro_ex; intro u56; apply sepWP_intro_ex; intro u64; apply sepWP_intro_ex; intro u72; apply sepWP_intro_ex; intro u80; apply sepWP_intro_ex; intro u88
  apply sepWP_intro_ex; intro u96; apply sepWP_intro_ex; intro u104; apply sepWP_intro_ex; intro u112; apply sepWP_intro_ex; intro u120; apply sepWP_intro_ex; intro u128; apply sepWP_intro_ex; intro u136
  apply sepWP_intro_ex; intro u144; apply sepWP_intro_ex; intro u152; apply sepWP_intro_ex; intro u160; apply sepWP_intro_ex; intro u168; apply sepWP_intro_ex; intro u176; apply sepWP_intro_ex; intro u184
  apply sepWP_intro_ex; intro u192; apply sepWP_intro_ex; intro u200; apply sepWP_intro_ex; intro u208; apply sepWP_intro_ex; intro u216; apply sepWP_intro_ex; intro u224; apply sepWP_intro_ex; intro u232
  apply sepWP_intro_ex; intro u240; apply sepWP_intro_ex; intro u248; apply sepWP_intro_ex; intro u256; apply sepWP_intro_ex; intro u264; apply sepWP_intro_ex; intro u272; apply sepWP_intro_ex; intro u280
  apply sepWP_intro_ex; intro u288; apply sepWP_intro_ex; intro u296; apply sepWP_intro_ex; intro u304; apply sepWP_intro_ex; intro u312; apply sepWP_intro_ex; intro u320; apply sepWP_intro_ex; intro u328
  apply sepWP_intro_ex; intro u336; apply sepWP_intro_ex; intro u344; apply sepWP_intro_ex; intro u352; apply sepWP_intro_ex; intro u360; apply sepWP_intro_ex; intro u368; apply sepWP_intro_ex; intro u376
  apply sepWP_intro_ex; intro u384; apply sepWP_intro_ex; intro u392; apply sepWP_intro_ex; intro u400; apply sepWP_intro_ex; intro u408; apply sepWP_intro_ex; intro u416; apply sepWP_intro_ex; intro u424
  apply sepWP_intro_ex; intro u432; apply sepWP_intro_ex; intro u440; apply sepWP_intro_ex; intro u448; apply sepWP_intro_ex; intro u456; apply sepWP_intro_ex; intro u464; apply sepWP_intro_ex; intro u472
  apply sepWP_intro_ex; intro u480; rw [emp_sepConj]
  have hstepA := DispatchPlacedBudget.epilogue_step_18996_19128_placed (ext := ext) s1 fsp out
    u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112
    u264 u272 u280 u288 u296 u304 u312 u320 u328 u336 u344 u352 u392 u400 u424 u432
    w224 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 q960
    (stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 224 ∗ ((fsp + 232#64) ↦₆₄ noneCap) ∗ ((fsp + 240#64) ↦₆₄ w240) ∗
     epilogueRecvStackPartB fsp w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488 ∗
     ((fsp + 512#64) ↦₁₂₈ q512) ∗ ((fsp + 528#64) ↦₁₂₈ q528) ∗ ((fsp + 544#64) ↦₁₂₈ q544) ∗ ((fsp + 560#64) ↦₆₄ w560) ∗
     memRegion (fsp + 568#64) 8 ∗ ((fsp + 576#64) ↦ₛ bs576) ∗ memRegion (fsp + 952#64) 8 ∗ memRegion (fsp + 976#64) 3168 ∗
     statesRecvSavedCells s0 ∗
     epilogueRecvOutPartB out u120 u128 u136 u144 u152 u160 u168 u176 u184 u192 u200 u208 u216 u224 u232 u240 u248 u256
       u360 u368 u376 u384 u408 u416 u440 u448 u456 u464 u472 u480 uq488 u504 ∗
     memRegion (out + 512#64) 376 ∗ ((out + 888#64) ↦₁₂₈ uq888) ∗ ((out + 904#64) ↦₁₂₈ uq904) ∗
     ((out + 920#64) ↦₆₄ u920) ∗ ((out + 928#64) ↦₆₄ u928) ∗ ((out + 936#64) ↦₆₄ u936) ∗ ((out + 944#64) ↦₁₂₈ uq944) ∗ Rest)
    hfsp_align (by rwa [lsmpl_base_332_eq]) hrun1 hsp1 hx19
  refine seq_vm_clean (SepWP.weaken_pre ?_ hstepA) ?_
  · rw [epilogueRecvStackPartA_eq_488, epilogueRecvOutPartB_eq_488]; refine Entails.of_eq ?_
    trans (wordsAtOff out
      [u0, u8, u16, u24, u32, u40, u48, u56, u64, u72, u80, u88, u96, u104, u112,
       u120, u128, u136, u144, u152, u160, u168, u176, u184, u192, u200, u208, u216, u224, u232, u240, u248, u256,
       u264, u272, u280, u288, u296, u304, u312, u320, u328, u336, u344, u352,
       u360, u368, u376, u384, u392, u400, u408, u416, u424, u432, u440, u448, u456, u464, u472, u480] 0 ∗
      (stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 224 ∗
       epilogueRecvStackPartA488 fsp w224 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 ∗
       ((fsp + 960#64) ↦₁₂₈ q960) ∗ ((fsp + 232#64) ↦₆₄ noneCap) ∗ ((fsp + 240#64) ↦₆₄ w240) ∗
       epilogueRecvStackPartB fsp w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488 ∗
       ((fsp + 512#64) ↦₁₂₈ q512) ∗ ((fsp + 528#64) ↦₁₂₈ q528) ∗ ((fsp + 544#64) ↦₁₂₈ q544) ∗ ((fsp + 560#64) ↦₆₄ w560) ∗
       memRegion (fsp + 568#64) 8 ∗ ((fsp + 576#64) ↦ₛ bs576) ∗ memRegion (fsp + 952#64) 8 ∗ memRegion (fsp + 976#64) 3168 ∗
       statesRecvSavedCells s0 ∗ ((out + 488#64) ↦₁₂₈ uq488) ∗ ((out + 504#64) ↦₆₄ u504) ∗ memRegion (out + 512#64) 376 ∗
       ((out + 888#64) ↦₁₂₈ uq888) ∗ ((out + 904#64) ↦₁₂₈ uq904) ∗ ((out + 920#64) ↦₆₄ u920) ∗ ((out + 928#64) ↦₆₄ u928) ∗
       ((out + 936#64) ↦₆₄ u936) ∗ ((out + 944#64) ↦₁₂₈ uq944) ∗ Rest))
    · dsimp only [wordsAtOff, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]; rw [BitVec.add_zero]; sep_ac_rfl
    · rw [wordsAtOff_out_488_eq_epilogueOut]; sep_ac_rfl
  · intro s2 hpc2 hrun2 hvm12 ⟨hsp2, hx0_2, hx1_2, hx2_2, hx3_2, hx16_2, hx17_2, hx19_2, hx20_2, hx22_2, hx23_2, hx24_2, hx26_2, hx27_2, hx29_2, hv0_2, htr2⟩
    let outPartA := epilogueRecvOutPartA out
      w224 (s1.readReg64 .x1) (s1.readReg64 .x8) w496 w456 w376 w368 w504 w288 w432 w408 w352 w384 w336 w296
      (s1.readReg64 .x25) (s1.readReg64 .x12) (s1.readReg64 .x11) (s1.readReg64 .x10)
      (s1.readReg64 .x15) (s1.readReg64 .x28) (s1.readReg64 .x7) (s1.readReg64 .x0)
      (s1.readReg64 .x6) (s1.readReg64 .x30) (s1.readReg64 .x21) (s1.readReg64 .x9)
      (s1.readReg64 .x5) (s1.readReg64 .x4) (s1.readReg64 .x13) (s1.readReg64 .x14)
    have hstepB := DispatchPlacedBudget.epilogue_step_19128_19280_placed (ext := ext) s2 fsp out
      u120 u128 u136 u144 u152 u160 u168 u176 u184 u192 u200 u208 u216 u224 u232 u240 u248 u256
      u360 u368 u376 u384 u408 u416 u440 u448 u456 u464 u472 u480 uq488 u504
      w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488
      (outPartA ∗ epilogueRecvStackPartA fsp w224 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 q960 ∗
       stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 224 ∗ ((fsp + 232#64) ↦₆₄ noneCap) ∗ ((fsp + 240#64) ↦₆₄ w240) ∗
       ((fsp + 512#64) ↦₁₂₈ q512) ∗ ((fsp + 528#64) ↦₁₂₈ q528) ∗ ((fsp + 544#64) ↦₁₂₈ q544) ∗ ((fsp + 560#64) ↦₆₄ w560) ∗
       memRegion (fsp + 568#64) 8 ∗ ((fsp + 576#64) ↦ₛ bs576) ∗ memRegion (fsp + 952#64) 8 ∗ memRegion (fsp + 976#64) 3168 ∗
       statesRecvSavedCells s0 ∗ memRegion (out + 512#64) 376 ∗ ((out + 888#64) ↦₁₂₈ uq888) ∗ ((out + 904#64) ↦₁₂₈ uq904) ∗
       ((out + 920#64) ↦₆₄ u920) ∗ ((out + 928#64) ↦₆₄ u928) ∗ ((out + 936#64) ↦₆₄ u936) ∗ ((out + 944#64) ↦₁₂₈ uq944) ∗ Rest)
      hfsp_align hpc2 hrun2 hsp2 hx0_2 hx1_2 hx19_2
    refine seq_vm_clean (SepWP.weaken_pre (Entails.of_eq (by dsimp only [outPartA]; sep_ac_rfl)) hstepB) ?_
    intro s3 hpc3 hrun3 hvm23 ⟨hsp3, hx0_3, hx1_3, hx2_3, hx19_3, hx20_3, hx29_3, htr3⟩
    rw [hx23_2, hx27_2, hx3_2, hx24_2, hx17_2, hx26_2, hx22_2, hx16_2, hx2_2, hx20_2, hv0_2]
    let outPartB488 := epilogueRecvOutPartB488 out
      w424 (s1.readReg64 .x23) (s1.readReg64 .x27) w440 w264 w344 w392 w272 w360 w400 w464 w304
      w328 w280 w320 (s1.readReg64 .x3) w312 (s1.readReg64 .x24) w416 (s1.readReg64 .x17) w472 (s1.readReg64 .x26)
      w448 (s1.readReg64 .x22) w480 (s1.readReg64 .x16) w488 (s1.readReg64 .x2) w248 (s1.readReg64 .x20)
    have hstepC := DispatchPlacedBudget.epilogue_step_19280_19324_placed hmemcpy s3 fsp out bs576 hbs576
      uq888 uq904 uq944 q512 q528 q544 u920 u928 u936 noneCap w560
      (memRegion (fsp - 19552#64) 15456 ∗ memRegion fsp 224 ∗
       epilogueRecvStackPartA488 fsp w224 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 ∗ ((fsp + 240#64) ↦₆₄ w240) ∗
       epilogueRecvStackPartB fsp w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488 ∗
       memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗ ((fsp + 960#64) ↦₁₂₈ q960) ∗
       memRegion (fsp + 976#64) 3168 ∗ statesRecvSavedCells s0 ∗
       outPartA ∗ outPartB488 ∗ ((out + 488#64) ↦₁₂₈ q960) ∗ ((out + 504#64) ↦₆₄ w256) ∗ Rest)
      hfsp_align hpc3 hrun3 hsp3 hx0_3 hx1_3 hx2_3 hx19_3
    refine seq_vm_clean (SepWP.weaken_pre ?_ hstepC) ?_
    · rw [epilogueRecvOutPartB_eq_488, epilogueRecvStackPartA_eq_488, stackAt_statesRecvCallee_eq_allocHook fsp]
      exact Entails.of_eq (by dsimp only [outPartB488]; sep_ac_rfl)
    · intro s4 hpc4 hrun4 hvm34 ⟨hsp4, htr4⟩
      have htr40 : TraceCalleeSaved s4 s0 := htr4.trans (htr3.trans (htr2.trans htr1))
      have hepil := DispatchPlacedBudget.states_recv_epilogue_19324_placed (ext := ext) s0 s4
        (outPartA ∗ outPartB488 ∗ memRegion (out + 488#64) 440 ∗ optEpochSecretAt A (out + 928#64) none ∗ Rest)
        hsp0_align hpc4 hrun4 hsp4 htr40
      refine SepWP.mono (SepWP.weaken_pre ?_ hepil) ?_
      · have hstk288 := epilogueStack_224_512_entails_memRegion fsp
          w224 noneCap w240 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504
          w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488
        have hstk3632 := epilogue_entails_memRegion_3632 fsp q512 q528 q544 q960 w560 bs576 hbs576
        have hout440 := epilogue_out_488_960_entails_memRegion_and_optNone A out q960 q528 q544 q512 w256 w560 (s3.readReg64 .x20) bs576 hbs576
        rw [← stack_recombine_4144 fsp, stackAt_statesRecvCallee_eq_allocHook fsp]
        refine Entails.trans (Entails.of_eq (show _ =
          (memRegion (fsp - 19552#64) 15456 ∗ stackAt fsp allocHookStack ∗ memRegion fsp 224) ∗
          (epilogueRecvStackPartA488 fsp w224 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 ∗
           ((fsp + 232#64) ↦₆₄ noneCap) ∗ ((fsp + 240#64) ↦₆₄ w240) ∗
           epilogueRecvStackPartB fsp w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488) ∗
          (((fsp + 512#64) ↦₁₂₈ q512) ∗ ((fsp + 528#64) ↦₁₂₈ q528) ∗ ((fsp + 544#64) ↦₁₂₈ q544) ∗ ((fsp + 560#64) ↦₆₄ w560) ∗
           memRegion (fsp + 568#64) 8 ∗ ((fsp + 576#64) ↦ₛ bs576) ∗ memRegion (fsp + 952#64) 8 ∗ ((fsp + 960#64) ↦₁₂₈ q960) ∗
           memRegion (fsp + 976#64) 3168) ∗
          (statesRecvSavedCells s0 ∗ outPartA ∗ outPartB488) ∗
          (((out + 488#64) ↦₁₂₈ q960) ∗ ((out + 504#64) ↦₆₄ w256) ∗ ((out + 512#64) ↦ₛ bs576) ∗ ((out + 888#64) ↦₁₂₈ q528) ∗
           ((out + 904#64) ↦₁₂₈ q544) ∗ ((out + 920#64) ↦₆₄ w560) ∗ ((out + 928#64) ↦₆₄ noneCap) ∗ ((out + 936#64) ↦₆₄ s3.readReg64 .x20) ∗
           ((out + 944#64) ↦₁₂₈ q512)) ∗ Rest by sep_ac_rfl))
          (Entails.trans (sepConj_mono_right (sepConj_mono hstk288
            (sepConj_mono hstk3632 (sepConj_mono_right (sepConj_mono_left hout440)))))
            (Entails.of_eq (by sep_ac_rfl)))
      · intro sf Pf _ _ ⟨hvm4f, hPf, hsp_f, hcs_f, htr_f⟩
        exact ⟨hvm12.trans (hvm23.trans (hvm34.trans hvm4f)),
          Entails.trans hPf (Entails.of_eq (by dsimp only [outPartA, outPartB488]; sep_ac_rfl)),
          hsp_f, hcs_f, htr_f⟩

theorem epilogue_18996_exit_none_488_pool_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (st_cost : M.σ) (s0 s1 : State) (out : BitVec 64)
    (w224 w240 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 : BitVec 64)
    (w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488 : BitVec 64)
    (Rest : SepProp) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (blkPl_332).base + 18996#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 4240#64)
    (hx19 : s1.readReg64 .x19 = out) (htr1 : TraceCalleeSaved s1 s0) :
    let fsp := s0.sp - 4240#64
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 224 ∗
       epilogueRecvStackPartA488 fsp w224 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 ∗
       ((fsp + 232#64) ↦₆₄ noneCap) ∗ ((fsp + 240#64) ↦₆₄ w240) ∗
       epilogueRecvStackPartB fsp w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488 ∗
       memRegion (fsp + 512#64) 3632 ∗ statesRecvSavedCells s0 ∗ memRegion out v1RecvSize ∗
       A.pool lim st_cost s1 ∗ Rest)
      (fun sf Pf =>
        VmPreserved s1 sf ∧
        (Pf ⊢
          epilogueRecvOutPartA out
            w224 (s1.readReg64 .x1) (s1.readReg64 .x8) w496 w456 w376 w368 w504 w288 w432 w408 w352 w384 w336 w296
            (s1.readReg64 .x25) (s1.readReg64 .x12) (s1.readReg64 .x11) (s1.readReg64 .x10)
            (s1.readReg64 .x15) (s1.readReg64 .x28) (s1.readReg64 .x7) (s1.readReg64 .x0)
            (s1.readReg64 .x6) (s1.readReg64 .x30) (s1.readReg64 .x21) (s1.readReg64 .x9)
            (s1.readReg64 .x5) (s1.readReg64 .x4) (s1.readReg64 .x13) (s1.readReg64 .x14) ∗
          epilogueRecvOutPartB488 out
            w424 (s1.readReg64 .x23) (s1.readReg64 .x27) w440 w264 w344 w392 w272 w360 w400 w464 w304
            w328 w280 w320 (s1.readReg64 .x3) w312 (s1.readReg64 .x24) w416 (s1.readReg64 .x17) w472 (s1.readReg64 .x26)
            w448 (s1.readReg64 .x22) w480 (s1.readReg64 .x16) w488 (s1.readReg64 .x2) w248 (s1.readReg64 .x20) ∗
          memRegion (out + 488#64) 440 ∗ optEpochSecretAt A.repAlloc (out + 928#64) none ∗
          A.pool lim st_cost sf ∗ Rest ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  intro fsp
  refine SepWP.mono
    (epilogue_18996_exit_none_488_placed (A := A.repAlloc) hmemcpy s0 s1 out
      w224 w240 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504
      w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488
      (A.pool lim st_cost s1 ∗ Rest) hsp0_align hpc1 hrun1 hsp1 hx19 htr1)
    fun sf Pf _ _ ⟨hvm, hPf, hq⟩ =>
      ⟨hvm, Entails.trans hPf (Entails.of_eq (by rw [A.pool_of_vmPreserved hvm]; sep_ac_rfl)), hq⟩

/-! ## `States.keysUnsampled` (`tag = 2#64`, `+96` / `0x554b4`) — `Ok` Branch -/

theorem keysUnsampled_ok_step_96_18996_placed [LibsignalPlacement]
    {ext : String → Option (State → State)} (s : State) (fsp outA selfA msgA : BitVec 64)
    (w8 w16 w24 w32 w40 w48 st_epoch msg_epoch u224 u232 u368 u376 u456 u496 u504 : BitVec 64)
    (Frame : SepProp)
    (hle : ¬ (msg_epoch > st_epoch)) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_332).base + 96#64) (hrun : s.status = .Running)
    (hsp : s.sp = fsp) (hx19 : s.readReg64 .x19 = outA)
    (hx1 : s.readReg64 .x1 = selfA) (hx24 : s.readReg64 .x24 = msgA) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 18996#64) s
      ((((selfA + 8#64) ↦₆₄ w8) ∗ ((selfA + 16#64) ↦₆₄ w16) ∗ ((selfA + 24#64) ↦₆₄ w24) ∗
        ((selfA + 32#64) ↦₆₄ w32) ∗ ((selfA + 40#64) ↦₆₄ w40) ∗ ((selfA + 48#64) ↦₆₄ w48) ∗ ((selfA + 56#64) ↦₆₄ st_epoch)) ∗
       (msgA ↦₆₄ msg_epoch) ∗
       (((fsp + 224#64) ↦₆₄ u224) ∗ ((fsp + 232#64) ↦₆₄ u232) ∗ ((fsp + 368#64) ↦₆₄ u368) ∗ ((fsp + 376#64) ↦₆₄ u376) ∗
        ((fsp + 456#64) ↦₆₄ u456) ∗ ((fsp + 496#64) ↦₆₄ u496) ∗ ((fsp + 504#64) ↦₆₄ u504)) ∗ Frame)
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢
          (((selfA + 8#64) ↦₆₄ w8) ∗ ((selfA + 16#64) ↦₆₄ w16) ∗ ((selfA + 24#64) ↦₆₄ w24) ∗
           ((selfA + 32#64) ↦₆₄ w32) ∗ ((selfA + 40#64) ↦₆₄ w40) ∗ ((selfA + 48#64) ↦₆₄ w48) ∗ ((selfA + 56#64) ↦₆₄ st_epoch)) ∗
          (msgA ↦₆₄ msg_epoch) ∗
          (((fsp + 224#64) ↦₆₄ 2#64) ∗ ((fsp + 232#64) ↦₆₄ noneCap) ∗ ((fsp + 368#64) ↦₆₄ w48) ∗ ((fsp + 376#64) ↦₆₄ w40) ∗
           ((fsp + 456#64) ↦₆₄ w32) ∗ ((fsp + 496#64) ↦₆₄ w24) ∗ ((fsp + 504#64) ↦₆₄ st_epoch)) ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x1 = w8 ∧ sm.readReg64 .x8 = w16 ∧
        sm.readReg64 .x19 = outA ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧ TraceCalleeSaved sm s) := by
  have hule : BitVec.ule msg_epoch st_epoch = true := ule_true_of_not_gt hle
  dsimp only [lsProg_332, noneCap, BitVec.ofNat_eq_ofNat] at hpc ⊢
  subst hsp hx19 hx1 hx24
  by_vm_steps (
    wp_steps
    wp_done)

set_option maxHeartbeats 1600000 in
/-- Relocatable `Ok` branch (`¬ (msg.epoch > st.uc.epoch)`) of `States.keysUnsampled`
    (`+96 -> s0.readReg64 .x30`) with `VmPreserved s sf`. -/
theorem states_recv_keysUnsampled_ok_96_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (s0 s : State) (fsp outA selfA msgA v48 : BitVec 64)
    (st : KeysUnsampled (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hle : ¬ (msg.epoch > st.uc.epoch)) (hfsp_eq : fsp = s0.sp - 4240#64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_332).base + 96#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = outA) (hx1 : s.readReg64 .x1 = selfA) (hx24 : s.readReg64 .x24 = msgA)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.keysUnsampled st) ∗
       messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗
       stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 48 ∗
       ((fsp + 48#64) ↦₆₄ v48) ∗ memRegion (fsp + 56#64) 4088 ∗ statesRecvSavedCells s0)
      (fun sf Pf =>
        VmPreserved s sf ∧
        (Pf ⊢ resultV1RecvAt A (F := F) outA ((States.keysUnsampled st).recv K msg) ∗
          memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
          statesRecvRoPlacedAt ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hrecv : (States.keysUnsampled st).recv K msg = .ok ⟨none, .keysUnsampled st⟩ := by
    simp only [States.recv, KeysUnsampled.epoch,
      CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.KeysUnsampled.epoch, hle, ↓reduceIte]
  rw [hrecv]
  have hstk288 : memRegion (fsp + 224#64) 288 = existsWordsAtOff fsp 36 224 :=
    memRegion_off_eq_existsWordsAtOff fsp 36 224 (by decide)
  have hpre :
      memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.keysUnsampled st) ∗
       messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗
       stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 48 ∗
       ((fsp + 48#64) ↦₆₄ v48) ∗ memRegion (fsp + 56#64) 4088 ∗ statesRecvSavedCells s0 ⊢
      ((∃∗ g : AuthWords,
          (selfA ↦₆₄ 2#64) ∗ ((selfA + 8#64) ↦₆₄ g.v1.w0) ∗ ((selfA + 16#64) ↦₆₄ g.v1.w1) ∗ ((selfA + 24#64) ↦₆₄ g.v1.w2) ∗
          ((selfA + 32#64) ↦₆₄ g.v2.w0) ∗ ((selfA + 40#64) ↦₆₄ g.v2.w1) ∗ ((selfA + 48#64) ↦₆₄ g.v2.w2) ∗
          ((selfA + 56#64) ↦₆₄ st.uc.epoch) ∗ memRegion (selfA + 64#64) 864 ∗
          relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g))) ∗
       existsWordsAtOff fsp 36 224) ∗
      (memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗
       stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 224 ∗ memRegion (fsp + 512#64) 3632 ∗
       statesRecvSavedCells s0) := by
    refine Entails.trans (Entails.of_eq (show _ =
      chunkedStatesAt A selfA (.keysUnsampled st) ∗
      (memRegion fsp 48 ∗ ((fsp + 48#64) ↦₆₄ v48) ∗ memRegion (fsp + 56#64) 4088) ∗
      (memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗
       statesRecvRoPlacedAt ∗ stackAt fsp statesRecvCalleeStackX ∗ statesRecvSavedCells s0) by sep_ac_rfl)) ?_
    refine Entails.trans (sepConj_mono (chunkedStatesAt_keysUnsampled_extract A selfA st)
      (sepConj_mono_left (cell48_4088_entails_memRegion_4144 fsp v48))) ?_
    rw [← stack_recombine_4144 fsp, hstk288]; exact Entails.of_eq (by sep_ac_rfl)
  refine SepWP.weaken_pre hpre ?_
  dsimp only [existsWordsAtOff, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
  apply sepWP_intro_ex; intro g
  apply sepWP_intro_ex; intro w224; apply sepWP_intro_ex; intro w232; apply sepWP_intro_ex; intro w240; apply sepWP_intro_ex; intro w248; apply sepWP_intro_ex; intro w256; apply sepWP_intro_ex; intro w264
  apply sepWP_intro_ex; intro w272; apply sepWP_intro_ex; intro w280; apply sepWP_intro_ex; intro w288; apply sepWP_intro_ex; intro w296; apply sepWP_intro_ex; intro w304; apply sepWP_intro_ex; intro w312
  apply sepWP_intro_ex; intro w320; apply sepWP_intro_ex; intro w328; apply sepWP_intro_ex; intro w336; apply sepWP_intro_ex; intro w344; apply sepWP_intro_ex; intro w352; apply sepWP_intro_ex; intro w360
  apply sepWP_intro_ex; intro w368; apply sepWP_intro_ex; intro w376; apply sepWP_intro_ex; intro w384; apply sepWP_intro_ex; intro w392; apply sepWP_intro_ex; intro w400; apply sepWP_intro_ex; intro w408
  apply sepWP_intro_ex; intro w416; apply sepWP_intro_ex; intro w424; apply sepWP_intro_ex; intro w432; apply sepWP_intro_ex; intro w440; apply sepWP_intro_ex; intro w448; apply sepWP_intro_ex; intro w456
  apply sepWP_intro_ex; intro w464; apply sepWP_intro_ex; intro w472; apply sepWP_intro_ex; intro w480; apply sepWP_intro_ex; intro w488; apply sepWP_intro_ex; intro w496; apply sepWP_intro_ex; intro w504
  rw [emp_sepConj]; unfold messageAt
  have hstep1 := keysUnsampled_ok_step_96_18996_placed (ext := ext) s fsp outA selfA msgA
    g.v1.w0 g.v1.w1 g.v1.w2 g.v2.w0 g.v2.w1 g.v2.w2 st.uc.epoch msg.epoch w224 w232 w368 w376 w456 w496 w504
    ((selfA ↦₆₄ 2#64) ∗ memRegion (selfA + 64#64) 864 ∗
     relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g)) ∗
     messagePayloadAt spqrPolyApi msgA msg.payload ∗
     ((fsp + 240#64) ↦₆₄ w240) ∗ ((fsp + 288#64) ↦₆₄ w288) ∗ ((fsp + 296#64) ↦₆₄ w296) ∗
     ((fsp + 336#64) ↦₆₄ w336) ∗ ((fsp + 352#64) ↦₆₄ w352) ∗ ((fsp + 384#64) ↦₆₄ w384) ∗
     ((fsp + 408#64) ↦₆₄ w408) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
     epilogueRecvStackPartB fsp w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488 ∗
     memRegion outA v1RecvSize ∗ statesRecvRoPlacedAt ∗ stackAt fsp statesRecvCalleeStackX ∗
     memRegion fsp 224 ∗ memRegion (fsp + 512#64) 3632 ∗ statesRecvSavedCells s0)
    hle hfsp_align hpc hrun hsp hx19 hx1 hx24
  refine seq_vm_clean
    (SepWP.weaken_pre (Entails.of_eq (by dsimp only [epilogueRecvStackPartB]; sep_ac_rfl)) hstep1) ?_
  intro s1 hpc1 hrun1 hvm01 ⟨hsp1, hx1_1, hx8_1, hx19_1, hx29_1, htr1⟩
  have htr10 : TraceCalleeSaved s1 s0 := htr1.trans htr
  have hsp10 : s1.sp = s0.sp - 4240#64 := by rw [hsp1, hfsp_eq]
  have hexit := epilogue_18996_exit_none_488_placed (A := A) hmemcpy s0 s1 outA
    2#64 w240 w288 w296 w336 w352 g.v2.w2 g.v2.w1 w384 w408 w432 g.v2.w0 g.v1.w2 st.uc.epoch
    w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488
    (relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g)) ∗
     memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt)
    hsp0_align hpc1 hrun1 hsp10 hx19_1 htr10
  dsimp only at hexit; rw [← hfsp_eq] at hexit
  refine SepWP.mono (SepWP.weaken_pre ?_ hexit) ?_
  · have hself := selfA_8words_entails_memRegion_928 selfA 2#64 g.v1.w0 g.v1.w1 g.v1.w2 g.v2.w0 g.v2.w1 g.v2.w2 st.uc.epoch
    unfold messageAt epilogueRecvStackPartA488
    refine Entails.trans (Entails.of_eq (show _ =
      ((selfA ↦₆₄ 2#64) ∗ ((selfA + 8#64) ↦₆₄ g.v1.w0) ∗ ((selfA + 16#64) ↦₆₄ g.v1.w1) ∗
       ((selfA + 24#64) ↦₆₄ g.v1.w2) ∗ ((selfA + 32#64) ↦₆₄ g.v2.w0) ∗ ((selfA + 40#64) ↦₆₄ g.v2.w1) ∗
       ((selfA + 48#64) ↦₆₄ g.v2.w2) ∗ ((selfA + 56#64) ↦₆₄ st.uc.epoch) ∗ memRegion (selfA + 64#64) 864) ∗
      (stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 224 ∗
       (((fsp + 224#64) ↦₆₄ 2#64) ∗ ((fsp + 288#64) ↦₆₄ w288) ∗ ((fsp + 296#64) ↦₆₄ w296) ∗
        ((fsp + 336#64) ↦₆₄ w336) ∗ ((fsp + 352#64) ↦₆₄ w352) ∗ ((fsp + 368#64) ↦₆₄ g.v2.w2) ∗
        ((fsp + 376#64) ↦₆₄ g.v2.w1) ∗ ((fsp + 384#64) ↦₆₄ w384) ∗ ((fsp + 408#64) ↦₆₄ w408) ∗
        ((fsp + 432#64) ↦₆₄ w432) ∗ ((fsp + 456#64) ↦₆₄ g.v2.w0) ∗ ((fsp + 496#64) ↦₆₄ g.v1.w2) ∗
        ((fsp + 504#64) ↦₆₄ st.uc.epoch)) ∗
       ((fsp + 232#64) ↦₆₄ noneCap) ∗ ((fsp + 240#64) ↦₆₄ w240) ∗
       epilogueRecvStackPartB fsp w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488 ∗
       memRegion (fsp + 512#64) 3632 ∗ statesRecvSavedCells s0 ∗ memRegion outA v1RecvSize ∗
       (relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g)) ∗
        ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
        statesRecvRoPlacedAt)) by sep_ac_rfl))
      (Entails.trans (sepConj_mono_left hself) (Entails.of_eq (by sep_ac_rfl)))
  · intro sf Pf _ _ ⟨hvm1f, hPf, hsp_f, hcs_f, htr_f⟩
    rw [hx1_1, hx8_1] at hPf
    have hrec := keysUnsampled_out_recompose A outA st g w288 w432 w408 w352 w384 w336 w296
      (s1.readReg64 .x25) (s1.readReg64 .x12) (s1.readReg64 .x11) (s1.readReg64 .x10)
      (s1.readReg64 .x15) (s1.readReg64 .x28) (s1.readReg64 .x7) (s1.readReg64 .x0)
      (s1.readReg64 .x6) (s1.readReg64 .x30) (s1.readReg64 .x21) (s1.readReg64 .x9)
      (s1.readReg64 .x5) (s1.readReg64 .x4) (s1.readReg64 .x13) (s1.readReg64 .x14)
      w424 (s1.readReg64 .x23) (s1.readReg64 .x27) w440
      w264 w344 w392 w272 w360 w400 w464 w304 w328 w280 w320 (s1.readReg64 .x3)
      w312 (s1.readReg64 .x24) w416 (s1.readReg64 .x17) w472 (s1.readReg64 .x26)
      w448 (s1.readReg64 .x22) w480 (s1.readReg64 .x16) w488 (s1.readReg64 .x2) w248 (s1.readReg64 .x20)
    refine ⟨hvm01.trans hvm1f, Entails.trans hPf (Entails.trans (Entails.of_eq (show _ =
      (epilogueRecvOutPartA outA 2#64 g.v1.w0 g.v1.w1 g.v1.w2 g.v2.w0 g.v2.w1 g.v2.w2 st.uc.epoch
         w288 w432 w408 w352 w384 w336 w296
         (s1.readReg64 .x25) (s1.readReg64 .x12) (s1.readReg64 .x11) (s1.readReg64 .x10)
         (s1.readReg64 .x15) (s1.readReg64 .x28) (s1.readReg64 .x7) (s1.readReg64 .x0)
         (s1.readReg64 .x6) (s1.readReg64 .x30) (s1.readReg64 .x21) (s1.readReg64 .x9)
         (s1.readReg64 .x5) (s1.readReg64 .x4) (s1.readReg64 .x13) (s1.readReg64 .x14) ∗
       epilogueRecvOutPartB488 outA w424 (s1.readReg64 .x23) (s1.readReg64 .x27) w440
         w264 w344 w392 w272 w360 w400 w464 w304 w328 w280 w320 (s1.readReg64 .x3)
         w312 (s1.readReg64 .x24) w416 (s1.readReg64 .x17) w472 (s1.readReg64 .x26)
         w448 (s1.readReg64 .x22) w480 (s1.readReg64 .x16) w488 (s1.readReg64 .x2) w248 (s1.readReg64 .x20) ∗
       memRegion (outA + 488#64) 440 ∗ optEpochSecretAt A (outA + 928#64) none ∗
       relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g))) ∗
      (memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
       statesRecvRoPlacedAt ∗ stackAt s0.sp statesRecvStackX) by sep_ac_rfl))
      (sepConj_mono_left hrec)), hsp_f, hcs_f, htr_f⟩

theorem states_recv_keysUnsampled_ok_96_pool_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (st_cost : M.σ)
    (s0 s : State) (fsp outA selfA msgA v48 : BitVec 64)
    (st : KeysUnsampled (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hle : ¬ (msg.epoch > st.uc.epoch)) (hfsp_eq : fsp = s0.sp - 4240#64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_332).base + 96#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = outA) (hx1 : s.readReg64 .x1 = selfA) (hx24 : s.readReg64 .x24 = msgA)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (memRegion outA v1RecvSize ∗ chunkedStatesAt A.repAlloc selfA (.keysUnsampled st) ∗
       messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool lim st_cost s ∗
       stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 48 ∗
       ((fsp + 48#64) ↦₆₄ v48) ∗ memRegion (fsp + 56#64) 4088 ∗ statesRecvSavedCells s0)
      (fun sf Pf =>
        VmPreserved s sf ∧
        (Pf ⊢ resultV1RecvAt A.repAlloc (F := F) outA ((States.keysUnsampled st).recv K msg) ∗
          memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
          statesRecvRoPlacedAt ∗ A.pool lim st_cost sf ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hbase0 : SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (memRegion outA v1RecvSize ∗ chunkedStatesAt A.repAlloc selfA (.keysUnsampled st) ∗
       messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗
       stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 48 ∗
       ((fsp + 48#64) ↦₆₄ v48) ∗ memRegion (fsp + 56#64) 4088 ∗ statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢ resultV1RecvAt A.repAlloc (F := F) outA ((States.keysUnsampled st).recv K msg) ∗
          memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
          statesRecvRoPlacedAt ∗ stackAt s0.sp statesRecvStackX) ∧
        (VmPreserved s sf ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)) :=
    SepWP.mono
      (states_recv_keysUnsampled_ok_96_placed (A := A.repAlloc) (K := K) hmemcpy s0 s fsp outA selfA msgA v48
        st msg hle hfsp_eq hsp0_align hfsp_align hpc hrun hsp hx19 hx1 hx24 htr)
      fun _ _ _ _ ⟨hvm, hPf, hq⟩ => ⟨hPf, hvm, hq⟩
  have hbase := SepWP.frame_post_entails (F := A.pool lim st_cost s) hbase0
  refine SepWP.mono
    (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hbase)
    fun sf Pf _ _ ⟨hPf, hvm, hspf, hcs, htrf⟩ => ?_
  refine ⟨hvm, Entails.trans hPf ?_, hspf, hcs, htrf⟩
  rw [A.pool_of_vmPreserved hvm]
  exact Entails.of_eq (by sep_ac_rfl)

/-! ## Per-Variant `subroutine_ok` Bridges & `States.keysUnsampled` Contract -/

theorem subroutine_ok_statesRecvVariantPlacedSpecOfPrePostEnv_of_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {PreEnv PostEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (self : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hwp : ∀ (outA selfA msgA : BitVec 64) (st_cost : M.σ) (s0 : State),
      LibsignalCodeLoaded lsmpl s0.mem →
      s0.pc = lsmpl.base 332 → s0.status = .Running →
      (s0.sp &&& 15#64 == 0#64) = true →
      s0.readReg64 .x0 = outA → s0.readReg64 .x1 = selfA → s0.readReg64 .x2 = msgA →
      statesRecvPreInv self →
      FitsEnv M lim st_cost (PreEnv ⟨outA, selfA, msgA, self, msg⟩) →
      LsRetAddr624 (s0.readReg64 .lr) →
      SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s0
        (stackAt s0.sp statesRecvStackX ∗
         (memRegion outA v1RecvSize ∗ chunkedStatesAt A.repAlloc selfA self ∗
          messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool lim st_cost s0))
        (fun sf Pf =>
          (∃ evs : List AllocEvent,
            PostEnv ⟨outA, selfA, msgA, self, msg⟩ evs ∧
            (Pf ⊢ resultV1RecvAt A.repAlloc (F := F) outA (self.recv K msg) ∗
              memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
              statesRecvRoPlacedAt ∗ A.pool lim (M.stepEvents evs st_cost) sf ∗
              stackAt s0.sp statesRecvStackX)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332)
      (withLsCodeLoaded lsmpl
        (DefsPlacedBudget.statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K self msg PreEnv PostEnv)) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨⟨outA, selfA, msgA⟩, st_cost⟩ R s0 hpc0 hrun0 hpre hsp0_align
  obtain ⟨hcl, hpre⟩ := extract_withLsCodeLoaded hpre
  simp only [DefsPlacedBudget.statesRecvVariantPlacedSpecOfPrePostEnv, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hinv, hfits, hlr_ls⟩, hmem⟩
  refine ⟨stackAt s0.sp statesRecvStackX ∗
      (memRegion outA v1RecvSize ∗ chunkedStatesAt A.repAlloc selfA self ∗
       messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool lim st_cost s0), R,
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem, ?_⟩
  exact sepWPp_of_statesRecv_exit_cl_placed_ofPrePostEnv
    (PreEnv := PreEnv) (PostEnv := PostEnv) s0 s0 outA selfA msgA self msg st_cost _ R
    (hwp outA selfA msgA st_cost s0 hcl hpc0 hrun0 hsp0_align hx0 hx1 hx2 hinv hfits hlr_ls)

theorem subroutine_ok_statesRecvVariantPlacedSpecOfEnv_of_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {Env : StatesRecvGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (self : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hwp : ∀ (outA selfA msgA : BitVec 64) (st_cost : M.σ) (s0 : State),
      LibsignalCodeLoaded lsmpl s0.mem →
      s0.pc = lsmpl.base 332 → s0.status = .Running →
      (s0.sp &&& 15#64 == 0#64) = true →
      s0.readReg64 .x0 = outA → s0.readReg64 .x1 = selfA → s0.readReg64 .x2 = msgA →
      statesRecvPreInv self →
      FitsEnv M lim st_cost (Env ⟨outA, selfA, msgA, self, msg⟩) →
      LsRetAddr624 (s0.readReg64 .lr) →
      SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s0
        (stackAt s0.sp statesRecvStackX ∗
         (memRegion outA v1RecvSize ∗ chunkedStatesAt A.repAlloc selfA self ∗
          messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool lim st_cost s0))
        (fun sf Pf =>
          (∃ evs : List AllocEvent,
            Env ⟨outA, selfA, msgA, self, msg⟩ evs ∧
            (Pf ⊢ resultV1RecvAt A.repAlloc (F := F) outA (self.recv K msg) ∗
              memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
              statesRecvRoPlacedAt ∗ A.pool lim (M.stepEvents evs st_cost) sf ∗
              stackAt s0.sp statesRecvStackX)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332)
      (withLsCodeLoaded lsmpl (DefsPlacedBudget.statesRecvVariantPlacedSpecOfEnv M A lim F K self msg Env)) :=
  subroutine_ok_statesRecvVariantPlacedSpecOfPrePostEnv_of_sepWP self msg hwp

theorem subroutine_ok_statesRecvVariantPlacedSpec_of_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (self : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hwp : ∀ (outA selfA msgA : BitVec 64) (st_cost : M.σ) (s0 : State),
      LibsignalCodeLoaded lsmpl s0.mem →
      s0.pc = lsmpl.base 332 → s0.status = .Running →
      (s0.sp &&& 15#64 == 0#64) = true →
      s0.readReg64 .x0 = outA → s0.readReg64 .x1 = selfA → s0.readReg64 .x2 = msgA →
      statesRecvPreInv self →
      FitsEnv M lim st_cost (StatesRecvEnv ⟨outA, selfA, msgA, self, msg⟩) →
      LsRetAddr624 (s0.readReg64 .lr) →
      SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s0
        (stackAt s0.sp statesRecvStackX ∗
         (memRegion outA v1RecvSize ∗ chunkedStatesAt A.repAlloc selfA self ∗
          messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool lim st_cost s0))
        (fun sf Pf =>
          (∃ evs : List AllocEvent,
            StatesRecvEnv ⟨outA, selfA, msgA, self, msg⟩ evs ∧
            (Pf ⊢ resultV1RecvAt A.repAlloc (F := F) outA (self.recv K msg) ∗
              memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
              statesRecvRoPlacedAt ∗ A.pool lim (M.stepEvents evs st_cost) sf ∗
              stackAt s0.sp statesRecvStackX)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332)
      (withLsCodeLoaded lsmpl (DefsPlacedBudget.statesRecvVariantPlacedSpec M A lim F K self msg)) :=
  subroutine_ok_statesRecvVariantPlacedSpecOfPrePostEnv_of_sepWP self msg hwp

/-- Two-envelope (`PreEnv` / `KeysUnsampledRecvPostEnv`) relocatable per-variant specification
    proof for `States.keysUnsampled st` (`tag = 2#64`), requiring no `FitsEnv` assumption on
    `PreEnv` because neither branch allocates fresh heap blocks. -/
theorem states_recv_keysUnsampled_placed_ok_ext_ofPrePostEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    {envs : StatesRecvCalleeEnvs F}
    (PreEnv : StatesRecvGhost F → List AllocEvent → Prop)
    (ext : String → Option (State → State))
    (hC : DefsPlacedBudget.StatesRecvPlacedContractsOfEnv M A lim F K envs ext)
    (st : KeysUnsampled (spqrAuthApi F)) (msg : Message spqrPolyApi) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332)
      (withLsCodeLoaded lsmpl
        (DefsPlacedBudget.statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K (.keysUnsampled st) msg
          PreEnv (fun _ => KeysUnsampledRecvPostEnv st msg))) := by
  refine subroutine_ok_statesRecvVariantPlacedSpecOfPrePostEnv_of_sepWP (.keysUnsampled st) msg ?_
  intro outA selfA msgA st_cost s0 _hcl hpc0 hrun0 hsp0_align hx0 hx1 hx2 _ _hfits hlr_ls
  have _hlr_x30 : LsRetAddr624 (s0.readReg64 .x30) := hlr_ls
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  have hpro := DispatchPlacedBudget.states_recv_prologue_placed (ext := ext) s0
    (memRegion outA v1RecvSize ∗ chunkedStatesAt A.repAlloc selfA (.keysUnsampled st) ∗
     messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool lim st_cost s0)
    hsp0_align hpc0 hrun0
  refine seq_vm_clean hpro ?_
  intro s1 hpc1 hrun1 hvm01 ⟨hsp1, hx0_1, hx1_1, hx2_1, _, hx29_1, htr1⟩
  rw [hx0] at hx0_1; rw [hx1] at hx1_1; rw [hx2] at hx2_1
  rw [← A.pool_of_vmPreserved hvm01, chunkedStatesAt_keysUnsampled_unfold]
  have hdisp := DispatchPlacedBudget.states_recv_dispatch_placed (ext := ext) s1 (s0.sp - 4240#64) selfA 2#64
    (authenticatorAt A.repAlloc (selfA + 8#64) st.uc.auth ∗ ((selfA + 56#64) ↦₆₄ st.uc.epoch) ∗
     memRegion (selfA + 64#64) 864 ∗ memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗
     A.pool lim st_cost s1 ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
     memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)
    (Or.inr (Or.inr (Or.inl rfl))) hpc1 hrun1 hsp1 hx1_1
  dsimp only [statesRecvArmOffset] at hdisp
  refine seq_vm_clean (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hdisp) ?_
  intro s2 hpc2 hrun2 hvm12 ⟨hsp2, _, hx1_2, _, _, _, _, hx19_2, _, hx24_2, _, hx29_2, htr2⟩
  rw [hx0_1] at hx19_2; rw [hx2_1] at hx24_2; rw [hx29_1] at hx29_2
  rw [lsmpl_base_332_eq] at hpc2
  rw [← A.pool_of_vmPreserved hvm12]
  have htr20 : TraceCalleeSaved s2 s0 := htr2.trans htr1
  have hpre2 :
      (selfA ↦₆₄ 2#64) ∗ statesRecvRoPlacedAt ∗
      (authenticatorAt A.repAlloc (selfA + 8#64) st.uc.auth ∗ ((selfA + 56#64) ↦₆₄ st.uc.epoch) ∗
       memRegion (selfA + 64#64) 864 ∗ memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗
       A.pool lim st_cost s2 ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
       memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0) ⊢
      (∃∗ v48 : BitVec 64, (((s0.sp - 4240#64) + 48#64) ↦₆₄ v48)) ∗
      (memRegion outA v1RecvSize ∗ chunkedStatesAt A.repAlloc selfA (.keysUnsampled st) ∗
       messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool lim st_cost s2 ∗
       stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 48 ∗
       memRegion ((s0.sp - 4240#64) + 56#64) 4088 ∗ statesRecvSavedCells s0) := by
    rw [chunkedStatesAt_keysUnsampled_unfold, memRegion_4144_split_cell48 (s0.sp - 4240#64)]
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWP.weaken_pre hpre2 ?_
  rw [sepExists_sepConj_left]; apply ProofLib.SepWP.exists_left; intro v48
  by_cases hgt : msg.epoch > st.uc.epoch
  · refine SepWP.mono
      (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (states_recv_keysUnsampled_err_96_placed hC.hdealloc_sat st_cost s0 s2 (s0.sp - 4240#64)
          outA selfA msgA v48 st msg hgt rfl hsp0_align hfsp_align hpc2 hrun2 hsp2 hx29_2
          hx19_2 hx1_2 hx24_2 htr20))
      fun sf Pf _ _ ⟨evs, hevs, hPf, hspf, _, hcs, htrf⟩ =>
        ⟨⟨evs, by simp only [KeysUnsampledRecvPostEnv, hgt, ↓reduceIte]; exact hevs, hPf⟩,
         hspf, hcs, htrf⟩
  · refine SepWP.mono
      (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (states_recv_keysUnsampled_ok_96_pool_placed (A := A) (lim := lim) (K := K)
          hC.hmemcpy_sat st_cost s0 s2 (s0.sp - 4240#64)
          outA selfA msgA v48 st msg hgt rfl hsp0_align hfsp_align hpc2 hrun2 hsp2
          hx19_2 hx1_2 hx24_2 htr20))
      fun sf Pf _ _ ⟨_, hPf, hspf, hcs, htrf⟩ =>
        ⟨⟨[], by simp only [KeysUnsampledRecvPostEnv, hgt, ↓reduceIte],
          by simpa only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil] using hPf⟩,
         hspf, hcs, htrf⟩

theorem states_recv_keysUnsampled_placed_ok_cro_ext_ofPrePostEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    {envs : StatesRecvCalleeEnvs F}
    (PreEnv : StatesRecvGhost F → List AllocEvent → Prop)
    (ext : String → Option (State → State))
    (hC : DefsPlacedBudget.StatesRecvPlacedContractsOfEnv M A lim F K envs ext)
    (st : KeysUnsampled (spqrAuthApi F)) (msg : Message spqrPolyApi) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332)
      (withLsCodeRoLoaded lsmpl
        (DefsPlacedBudget.statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K (.keysUnsampled st) msg
          PreEnv (fun _ => KeysUnsampledRecvPostEnv st msg))) :=
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (states_recv_keysUnsampled_placed_ok_ext_ofPrePostEnv M A lim F K PreEnv ext hC st msg)

/-- Default `StatesRecvEnv` relocatable per-variant specification proof for
    `States.keysUnsampled st` (`tag = 2#64`) under `withLsCodeLoaded lsmpl`. -/
theorem states_recv_keysUnsampled_placed_ok_ext [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem) (ext : String → Option (State → State))
    (hC : DefsPlacedBudget.StatesRecvPlacedContracts M A lim F K ext)
    (st : KeysUnsampled (spqrAuthApi F)) (msg : Message spqrPolyApi) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332)
      (withLsCodeLoaded lsmpl
        (DefsPlacedBudget.statesRecvVariantPlacedSpec M A lim F K (.keysUnsampled st) msg)) := by
  apply subroutine_ok_outcome_intro
  rintro ⟨⟨outA, selfA, msgA⟩, st_cost⟩ R s0 hpc hrun hpre hal
  refine (states_recv_keysUnsampled_placed_ok_ext_ofPrePostEnv M A lim F K StatesRecvEnv ext hC st msg).mono_outcome
    ((outA, selfA, msgA), st_cost) R s0 hpc hrun hpre hal ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨c, hex, hpost⟩ | ⟨hoom, hpost⟩)
  · left
    refine ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, DefsPlacedBudget.statesRecvVariantPlacedSpec,
      DefsPlacedBudget.statesRecvVariantPlacedSpecOfEnv,
      DefsPlacedBudget.statesRecvVariantPlacedSpecOfPrePostEnv] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hpost⟩
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨⟨hpost.1.1, KeysUnsampledRecvPostEnv_to_statesRecvEnv outA selfA msgA st msg hpost.1.2⟩,
      hpost.2⟩
  · right; left; exact ⟨hpan, hpost⟩
  · right; right; left; exact ⟨c, hex, hpost⟩
  · right; right; right; exact ⟨hoom, hpost⟩

theorem states_recv_keysUnsampled_placed_ok_cro_ext [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem) (ext : String → Option (State → State))
    (hC : DefsPlacedBudget.StatesRecvPlacedContracts M A lim F K ext)
    (st : KeysUnsampled (spqrAuthApi F)) (msg : Message spqrPolyApi) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332)
      (withLsCodeRoLoaded lsmpl
        (DefsPlacedBudget.statesRecvVariantPlacedSpec M A lim F K (.keysUnsampled st) msg)) :=
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (states_recv_keysUnsampled_placed_ok_ext M A lim F K ext hC st msg)

end LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSimple1PlacedBudget
