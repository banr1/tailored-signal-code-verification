/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Common.SharedHelpers
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SessionStateCalleesBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobPlaced
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPFrozen

/-!
# Budget-Threaded Relocatable `initialize_bob_session` (Block `75`): Specs and Session-Build Tail

Allocator-budget-threaded (`RustCliAllocBudget M`) specifications, deterministic allocator event
envelope (`initBobSessionBuildEvents`), and post-`spqr::initial_state` session-build proofs
(`+252 → +564 → RET`) for unmutated Block `75` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (
  LibsignalCodeLoaded LibsignalHooks LibsignalPlacement blkLib_eq_75 blkPl_75 lsLogFilterAddr
  lsmpl lsProg_75 lsMemcpySym lsRustAllocSym lsRustDeallocSym lsRustNoAllocShimSym
  ls_hook_ok_of_mem ls_subroutine_ok_cl_of_block ls_subroutine_ok_cl_of_plain lsρ
  sepWP_seq_lscl withLsCl
)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (
  withLsCodeRoLoaded withLsFrozen
)
open CryptoVerification.E2E.Pqxdh.Initiator (
  AcceptKeysInput Bytes Primitives WellSizedAcceptKeysInput
  bv_add_neg64 bv_sub_add_lit' bv_sub_sub_lit bytesToBv8 encodeEC pqxdhEntryStack
  readReg_setMem_setPC_pre readReg_setPC_pre
  readReg32_setMem_setPC_pre readReg32_setPC_pre
  readReg64_setMem_setPC_pre readReg64_setPC_pre
  senderChainFieldsAt sp_setMem_setPC_pre sp_setPC_pre
)
open CryptoVerification.E2E.Pqxdh.Initiator.Model (acceptKeys)
open CryptoVerification.E2E.Pqxdh.ResponderCore (
  InitBobCallGhost bobHead144Bv8V1 bobHead144Bv8V1_length bobHead144V1_eq_pointsToBytes
  bobParamsFieldsAt bobSession344Bv8 bobSession344Bv8V1 bobSession344Bv8V1_length
  bobSession344V1_pack bobTail96Bv8 cells4_sub768_merge initBobErrAt
  initBobSavedRegs initBobSavedRegs_entails_memRegion96 memRegion_160_sub5024
  post100_pack stackAt_entry_some_merge stackAt_entry_some_split
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FitsEvent FitsStep RustCliAllocBudget
  VmPreserved coarseCostModel coarseStep coarseStepReserve fitsEvents_append rustAllocEvents
  rustCliAllocBudgetSpec rustCliAllocNoOomExternSpecWithStack rustCliDeallocBudgetSpec
  subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  subroutine_ok_rustCliAllocNoOom_externWithStack
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec rustAllocShimVmSpec)
open LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SessionStateCalleesBudget (
  ecPubKeySerializeAllocEvents ecPubKeySerializeAllocPlacedSpec
  ecPubKeySerialize_alloc_placed_ok_of_session
  withSenderChainNoneEvents withSenderChainNonePlacedSpec
  withSenderChain_none_placed_ok_of_session
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec
)

export LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptBudget (
  pqxdhAcceptOptFieldsInnerPlacedSpec
  pqxdhAcceptOptFieldsPlacedSpec
  pqxdhAcceptOptFieldsFrozenPlacedSpec
)
export CryptoVerification.E2E.Pqxdh.ResponderCore (SepWPp.call_lscro_frame)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_sub_sub_lit bv_add_neg64
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

@[local arm64_norm ↓, local wp_norm ↓]
private theorem calleeSavedVRegs_setPC_pre_bob_placed (s : State) (pc : BitVec 64) :
    calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem calleeSavedVRegs_setMem_setPC_pre_bob_placed (s : State) (pc : BitVec 64)
    (m : Memory) :
    calleeSavedVRegs ((s.setPC pc).setMem m) = calleeSavedVRegs s := rfl

@[local simp, local arm64_norm, local wp_norm]
private theorem calleeSavedVRegs_writeVReg128_0_bob_placed (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 0#5 v) = calleeSavedVRegs s := rfl

private theorem bv_add_sub_lit_bob_placed (x a b : BitVec 64) :
    (x + a) - b = x + (a - b) := by bv_omega

@[local arm64_norm, local wp_norm]
private theorem bv_sub_add_lit_bob_placed (x a b : BitVec 64) :
    (x - a) + b = x - (a - b) := bv_sub_add_lit' x a b

@[local simp, local arm64_norm, local wp_norm]
private theorem cond_ne_subs64_0_1_bob_placed :
    ConditionHolds CondCode.NE (subsPState64 0#64 1#64) = true := by
  simp only [ConditionHolds, subsPState64]; decide

private theorem hookSat_sessionShimBudget_of_rustAllocShimVm {H : LibsignalHooks}
    (h : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec) :
    HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec := by
  refine HookSat.mono h fun u R s0 hp => ⟨u, R, hp, fun sf hq => ?_⟩
  dsimp only [rustAllocShimVmSpec, sessionShimBudgetSpec,
    CryptoVerification.LibsignalTripleRatchet.sessionShimSpec] at hq ⊢
  rw [satisfies_pure_sepConj] at hq
  rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj]
  exact ⟨hq.1.2, hq.1.1.2.1, hq.2⟩

private theorem hookSat_sessionMemcpyRegionBudget_of_allocMemcpyVm {H : LibsignalHooks}
    (h : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec := by
  refine HookSat.mono h fun ⟨dst, src, bs⟩ R s0 hp => ?_
  dsimp only [sessionMemcpyRegionBudgetSpec,
    CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec,
    memcpyRegionSpec, allocMemcpyVmSpec] at hp ⊢
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hp
  rcases hp with ⟨⟨hx0, hx1, hx2⟩, hm⟩
  have hlt : bs.length < 2 ^ 64 := hx2 ▸ (s0.readReg64 .x2).isLt
  have hx2_bv : s0.readReg64 .x2 = BitVec.ofNat 64 bs.length := by
    rw [← hx2, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine ⟨(dst, src, bs), R, ?_, fun sf hq => ?_⟩
  · rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2_bv, hlt⟩, ?_⟩
    rwa [sepConj_assoc]
  · rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨⟨hx0f, hacp, hvm⟩, hm'⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hvm, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0f, hacp.2.1⟩, ?_⟩
    rwa [← sepConj_assoc]

/-! ## Session-Build Allocator Event Envelope -/

/-- Exact deterministic allocator event sequence emitted by `initBob_session_build_placed`
(`(blkPl_75).base + 252#64 → (blkPl_75).base + 564#64`):
3 `<PublicKey>::serialize` 33-byte box allocations (`ikBPk`, `ikAPk`, `ekAPk`), 1 32-byte root-key
box allocation, and `<SessionState>::with_sender_chain` (`None` branch). -/
def initBobSessionBuildEvents : List AllocEvent :=
  ecPubKeySerializeAllocEvents ++ ecPubKeySerializeAllocEvents ++
    rustAllocEvents 32 1 ++ ecPubKeySerializeAllocEvents ++ withSenderChainNoneEvents

def InitBobSessionBuildEnv (evs : List AllocEvent) : Prop :=
  evs = initBobSessionBuildEvents

theorem fitsEnv_initBobSessionBuildEnv_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} :
    FitsEnv M lim st InitBobSessionBuildEnv ↔ FitsEvents M lim st initBobSessionBuildEvents :=
  FitsEnv.eq_iff

example :
    FitsEnv coarseCostModel ⟨64, 67108864, 536870912, true⟩ coarseCostModel.init
      InitBobSessionBuildEnv := by
  have hevs : initBobSessionBuildEvents =
      [.alloc 33, .alloc 33, .alloc 32, .alloc 33,
       .alloc 32, .alloc 33, .alloc 33, .alloc 32, .alloc 32,
       .free 1 32, .free 1 33] := by decide
  rw [fitsEnv_initBobSessionBuildEnv_iff, hevs]
  dsimp only [FitsEvents, FitsEvent, AllocEvent.withinMaxAlloc, FitsStep,
    AllocCostModel.step, coarseCostModel, coarseStep, coarseStepReserve]
  decide

attribute [local irreducible] FitsEvent

/-! ## Budget-Threaded Specifications -/

/-- Budget-threaded relocatable inner contract for `initialize_bob_session` (Block `75`),
parameterized by allocator event envelope `InitBobEnv : AcceptKeysInput → List AllocEvent → Prop`
(`onPanic = ⌜False⌝`, `onOom = ⌜False⌝` under `FitsEnv M lim st (InitBobEnv g.inp)`). -/
def initializeBobSessionInnerPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (InitBobEnv : AcceptKeysInput → List AllocEvent → Prop) :
    Spec (InitBobCallGhost × M.σ) where
  pre := fun (g, st) s =>
    ⌜s.readReg64 .x0 = g.argPtr ∧
      s.readReg64 .x1 = g.ratchetKeyPairPtr ∧
      s.readReg64 .x8 = g.outPtr ∧
      g.inp.trustedPeer = true ∧
      g.inp.replayOk = true ∧
      g.inp.hdr.opkId?.isSome = g.inp.opkBSk?.isSome ∧
      WellSizedAcceptKeysInput g.inp ∧
      g.ikBPk.length = 32 ∧
      g.spkBPk.length = 32 ∧
      FitsEnv M lim st (InitBobEnv g.inp)⌝ ∗
    bobParamsFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.ratchetKeyPairPtr
      g.inp g.ikBPk g.spkBPk g.sameAccountByte ∗
    memRegion g.outPtr 344 ∗
    (lsLogFilterAddr ↦₆₄ 0#64) ∗
    stackAt s.sp (768 + pqxdhEntryStack) ∗
    A.pool lim st s
  post := fun (g, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ InitBobEnv g.inp evs⌝ ∗
      bobParamsFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.ratchetKeyPairPtr
        g.inp g.ikBPk g.spkBPk g.sameAccountByte ∗
      (match acceptKeys P g.inp with
       | some drKey =>
         ∃∗ localIkBoxPtr : BitVec 64,
         ∃∗ remoteIkBoxPtr : BitVec 64,
         ∃∗ rootKeyBoxPtr : BitVec 64,
         ∃∗ baseKeyBoxPtr : BitVec 64,
         ∃∗ ratchetPubBoxPtr : BitVec 64,
         ∃∗ ratchetPrivBoxPtr : BitVec 64,
         ∃∗ chainKeyBoxPtr : BitVec 64,
         ∃∗ pad_f4 : BitVec 32,
         ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
         ∃∗ c4 : BitVec 64,
         ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64,
           ⌜localIkBoxPtr ≠ 0 ∧ remoteIkBoxPtr ≠ 0 ∧ rootKeyBoxPtr ≠ 0 ∧ baseKeyBoxPtr ≠ 0 ∧
             ratchetPubBoxPtr ≠ 0 ∧ ratchetPrivBoxPtr ≠ 0 ∧ chainKeyBoxPtr ≠ 0⌝ ∗
           (localIkBoxPtr ↦ₛ bytesToBv8 (encodeEC g.ikBPk)) ∗ A.live localIkBoxPtr 33 1 ∗
           (remoteIkBoxPtr ↦ₛ bytesToBv8 (encodeEC g.inp.hdr.ikAPk)) ∗
           A.live remoteIkBoxPtr 33 1 ∗
           (rootKeyBoxPtr ↦ₛ bytesToBv8 drKey.rootKey) ∗ A.live rootKeyBoxPtr 32 1 ∗
           (baseKeyBoxPtr ↦ₛ bytesToBv8 (encodeEC g.inp.hdr.ekAPk)) ∗
           A.live baseKeyBoxPtr 33 1 ∗
           (ratchetPubBoxPtr ↦ₛ bytesToBv8 (encodeEC g.spkBPk)) ∗
           A.live ratchetPubBoxPtr 33 1 ∗
           (ratchetPrivBoxPtr ↦ₛ bytesToBv8 g.inp.spkBSk) ∗ A.live ratchetPrivBoxPtr 32 1 ∗
           (chainKeyBoxPtr ↦ₛ bytesToBv8 drKey.chainKey) ∗ A.live chainKeyBoxPtr 32 1 ∗
           (g.outPtr ↦ₛ bobSession344Bv8 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
             0#64 1#64 ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
             pad_f4 c0 c1 c2 c3 c4 d0 d1 d2)
       | none =>
         initBobErrAt g.outPtr ∗
         anyHeap) ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      stackAt s0.sp (768 + pqxdhEntryStack) ∗
      A.pool lim (M.stepEvents evs st) sf

def initializeBobSessionPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (InitBobEnv : AcceptKeysInput → List AllocEvent → Prop) :
    Spec (InitBobCallGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl (initializeBobSessionInnerPlacedSpec P A lim InitBobEnv)

def initializeBobSessionFrozenPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (InitBobEnv : AcceptKeysInput → List AllocEvent → Prop) :
    Spec (InitBobCallGhost × M.σ) :=
  withLsFrozen lsmpl (initializeBobSessionInnerPlacedSpec P A lim InitBobEnv)

/-! ## Post-`spqr::initial_state` Code Proofs (`+252 → +564 → RET`) -/

set_option maxHeartbeats 800000 in
/-- Relocatable epilogue (`(blkPl_75).base + 564#64 → RET`) of `initialize_bob_session`
(Block `75`) under `[LibsignalPlacement]`, additionally establishing `VmPreserved s sf` so
`A.pool lim st s` transports across the epilogue via `A.pool_transport`. -/
theorem initBob_epilogue_placed [LibsignalPlacement] {H : LibsignalHooks}
    (s0 s : State) (Frame : SepProp)
    (hsp0_align : s0.sp &&& 15#64 == 0#64)
    (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (blkPl_75).base + 564#64)
    (hsp : s.sp = s0.sp - 768#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (lsProg_75 H) (s0.readReg64 (.gpr 30#5)) s
      (initBobSavedRegs s0.sp s0 ∗ Frame)
      (fun sf Pf =>
        (Pf ⊢ memRegion (s0.sp - 96#64) 96 ∗ Frame) ∧ sf.status = ExecStatus.Running ∧
        sf.pc = s0.readReg64 (.gpr 30#5) ∧ sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧ VmPreserved s sf ∧ sf.trace = s.trace) := by
  have hs0 : s0.sp = s.sp + 768#64 := by rw [hsp]; bv_omega
  have hal : s.sp &&& 15#64 == 0#64 := by rw [hsp]; revert hsp0_align; bv_bits
  have hfold := initBobSavedRegs_entails_memRegion96 (s.sp + 768#64) s0
  dsimp only [initBobSavedRegs] at hfold ⊢
  simp only [bv_add_sub_lit_bob_placed, BitVec.reduceSub] at hfold
  rw [hs0]
  clear hsp hsp0_align hs0
  simp only [bv_add_sub_lit_bob_placed, BitVec.reduceSub, sepConj_assoc]
  apply sepWP_seg_ls_vm (Q := lsProg_75 (hooksException H)) blkLib_eq_75
    (mid := s0.readReg64 (.gpr 30#5))
  intro _m_strip
  wp_steps
  refine SepWP.fold hfold (by sep_focus) ?_
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) fun _m_real hnsp => ?_
  have hvm : VmPreserved s _ := hnsp.toVmPreserved (by wp_norm_lhs)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
     by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
     by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by simp only [arm64_norm, *]⟩,
    hvm, by wp_norm_goal⟩

private theorem sub488_split_v1 (sp : BitVec 64) :
    memRegion (sp - 488#64) 344 =
      cells (sp - 488#64) 19 ∗
      memRegion (sp - 336#64) 92 ∗
      (∃∗ pad_f4 : BitVec 32, (sp - 244#64) ↦₃₂ pad_f4) ∗
      memRegion (sp - 240#64) 96 := by
  rw [ProofLib.memRegion_split' (b := sp - 488#64) (n := 152) (k := 192)
      (b' := sp - 336#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 336#64) (n := 92) (k := 100)
      (b' := sp - 244#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 244#64) (n := 4) (k := 96)
      (b' := sp - 240#64) rfl (by bv_omega) (by decide),
    (ProofLib.memRegion_cells (sp - 488#64) 19 (by decide) :
      memRegion (sp - 488#64) 152 = cells (sp - 488#64) 19),
    ProofLib.memRegion_four (sp - 244#64)]

private theorem sepWP_congr_stackAt {prog : Program} {tgt : BitVec 64} {s : State}
    {sp' : BitVec 64} {stk : Nat} {P F : SepProp} {post : State → SepProp → Prop}
    (hsp : s.sp = sp')
    (hf : P = stackAt sp' stk ∗ F := by sep_focus)
    (hnext : SepWP prog tgt s (stackAt s.sp stk ∗ F) post) :
    SepWP prog tgt s P post :=
  SepWP.fold (by rw [hsp]; exact Entails.refl _) hf hnext

private theorem call_frame_lscl_bob {α : Type} {prog : Program} {pl : Obj.MultiPlacement}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α} {x : α} {φ : Prop}
    {T F : SepProp} {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (withLsCl pl spec))
    (hcl : LibsignalCodeLoaded pl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = ⌜φ⌝ ∗ T)
    (hφ : φ) (hP : P = T ∗ F)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      LibsignalCodeLoaded pl sf.mem →
      SepWP prog target_pc sf (spec.post x s sf ∗ F) post)
    (hpanic_eq : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWP prog target_pc s P post := by
  refine SepWP.call_subroutine_frame (x := x) (F := F) hcall hpc hrun hsp hlr ?_
    (fun _ sf _ hm => by
      dsimp only [withLsCl] at hm; rw [hpanic_eq sf] at hm; exact not_satisfies_false_sepConj hm)
    (fun _ code sf _ hm => by
      dsimp only [withLsCl] at hm; rw [hexit_eq code sf] at hm; exact not_satisfies_false_sepConj hm)
    (fun sf hpcm hrunm hspm hcsm => ?_)
    (fun _ sf _ hm => by
      dsimp only [withLsCl] at hm; rw [hoom_eq sf] at hm
      exact (not_satisfies_false_sepConj hm).elim)
  · intro R hm
    dsimp only [withLsCl]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  · dsimp only [withLsCl]
    rw [sepConj_assoc]
    exact SepWP.pure_elim (hnext sf hpcm hrunm hspm hcsm)

set_option maxHeartbeats 3200000 in
/-- Budget-threaded relocatable session-build segment
(`(blkPl_75).base + 252#64 → (blkPl_75).base + 564#64`) of `initialize_bob_session` (Block `75`)
under `[LibsignalPlacement]` with `sessionShimBudgetSpec` / `sessionMemcpyRegionBudgetSpec`
hooks, advancing `A.pool lim st s` to `A.pool lim (M.stepEvents initBobSessionBuildEvents st) sf`
with zero panic/OOM under `FitsEvents M lim st initBobSessionBuildEvents`. -/
theorem initBob_session_build_placed_of_session [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {Qp : State → SepProp → Prop}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (s0 s : State) (st : M.σ) (argPtr rkp outPtr : BitVec 64)
    (spqrCap spqrBufPtr spqrLen : BitVec 64)
    (ikBPk ikAPk ekAPk spkBPk spkBSk rk ck : Bytes)
    (Frame : SepProp)
    (hcl0 : LibsignalCodeLoaded lsmpl s.mem)
    (hfits : FitsEvents M lim st initBobSessionBuildEvents)
    (hikB_len : ikBPk.length = 32)
    (hikA_len : ikAPk.length = 32)
    (hekA_len : ekAPk.length = 32)
    (hspkPk_len : spkBPk.length = 32)
    (hspkSk_len : spkBSk.length = 32)
    (hrk_len : rk.length = 32)
    (hck_len : ck.length = 32)
    (hsp0_align : s0.sp &&& 15#64 == 0#64)
    (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (blkPl_75).base + 252#64)
    (hsp : s.sp = s0.sp - 768#64)
    (hx19 : s.readReg64 (.gpr 19#5) = outPtr)
    (hx20 : s.readReg64 (.gpr 20#5) = rkp)
    (hx21 : s.readReg64 (.gpr 21#5) = argPtr)
    (hx23 : s.readReg64 (.gpr 23#5) = s0.sp - 768#64)
    (hx27 : s.readReg64 (.gpr 27#5) = s0.sp - 488#64)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (lsProg_75 H) ((blkPl_75).base + 564#64) s
      (((s0.sp - 768#64) ↦₆₄ 0#64) ∗ ((s0.sp - 760#64) ↦₆₄ spqrCap) ∗
       ((s0.sp - 752#64) ↦₆₄ spqrBufPtr) ∗ ((s0.sp - 744#64) ↦₆₄ spqrLen) ∗
       ((s0.sp - 656#64) ↦ₛ bytesToBv8 rk) ∗ ((s0.sp - 624#64) ↦ₛ bytesToBv8 ck) ∗
       ((s0.sp - 592#64) ↦₃₂ 0#32) ∗
       memRegion (s0.sp - 488#64) 344 ∗
       (argPtr ↦ₛ bytesToBv8 ikBPk) ∗ ((argPtr + 128#64) ↦ₛ bytesToBv8 ikAPk) ∗
       ((argPtr + 160#64) ↦ₛ bytesToBv8 ekAPk) ∗
       (rkp ↦ₛ bytesToBv8 spkBPk) ∗ ((rkp + 32#64) ↦ₛ bytesToBv8 spkBSk) ∗
       memRegion outPtr 344 ∗
       stackAt (s0.sp - 768#64) pqxdhEntryStack ∗ A.pool lim st s ∗ Frame)
      (fun sf P_f =>
        ∃ (localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
           ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr : BitVec 64)
          (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64),
          localIkBoxPtr ≠ 0#64 ∧ remoteIkBoxPtr ≠ 0#64 ∧ rootKeyBoxPtr ≠ 0#64 ∧
          baseKeyBoxPtr ≠ 0#64 ∧ ratchetPubBoxPtr ≠ 0#64 ∧ ratchetPrivBoxPtr ≠ 0#64 ∧
          chainKeyBoxPtr ≠ 0#64 ∧ (P_f ⊢
            (outPtr ↦ₛ bobSession344Bv8V1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
              spqrCap spqrBufPtr spqrLen ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
              pad_f4 c0 c1 c2 c3 c4 d0 d1 d2) ∗
            memRegion (s0.sp - 768#64) 32 ∗
            ((s0.sp - 656#64) ↦ₛ bytesToBv8 rk) ∗ ((s0.sp - 624#64) ↦ₛ bytesToBv8 ck) ∗
            ((s0.sp - 592#64) ↦₃₂ 0#32) ∗
            memRegion (s0.sp - 488#64) 344 ∗
            (argPtr ↦ₛ bytesToBv8 ikBPk) ∗ ((argPtr + 128#64) ↦ₛ bytesToBv8 ikAPk) ∗
            ((argPtr + 160#64) ↦ₛ bytesToBv8 ekAPk) ∗
            (rkp ↦ₛ bytesToBv8 spkBPk) ∗ ((rkp + 32#64) ↦ₛ bytesToBv8 spkBSk) ∗
            (localIkBoxPtr ↦ₛ bytesToBv8 (encodeEC ikBPk)) ∗ A.live localIkBoxPtr 33 1 ∗
            (remoteIkBoxPtr ↦ₛ bytesToBv8 (encodeEC ikAPk)) ∗ A.live remoteIkBoxPtr 33 1 ∗
            (rootKeyBoxPtr ↦ₛ bytesToBv8 rk) ∗ A.live rootKeyBoxPtr 32 1 ∗
            (baseKeyBoxPtr ↦ₛ bytesToBv8 (encodeEC ekAPk)) ∗ A.live baseKeyBoxPtr 33 1 ∗
            (ratchetPubBoxPtr ↦ₛ bytesToBv8 (encodeEC spkBPk)) ∗
            A.live ratchetPubBoxPtr 33 1 ∗
            (ratchetPrivBoxPtr ↦ₛ bytesToBv8 spkBSk) ∗ A.live ratchetPrivBoxPtr 32 1 ∗
            (chainKeyBoxPtr ↦ₛ bytesToBv8 ck) ∗ A.live chainKeyBoxPtr 32 1 ∗
            stackAt (s0.sp - 768#64) pqxdhEntryStack ∗
            A.pool lim (M.stepEvents initBobSessionBuildEvents st) sf ∗ Frame) ∧
          LibsignalCodeLoaded lsmpl sf.mem ∧
          sf.status = ExecStatus.Running ∧
          sf.pc = (blkPl_75).base + 564#64 ∧
          sf.sp = s0.sp - 768#64 ∧ sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0)
      Qp := by
  apply SepWPp.of_sepWP_ret
  have hsp_align : s.spAligned = true := by
    simp only [State.spAligned, hsp]
    revert hsp0_align; bv_bits
  let st1 := M.stepEvents ecPubKeySerializeAllocEvents st
  let st2 := M.stepEvents ecPubKeySerializeAllocEvents st1
  let st3 := M.stepEvents (rustAllocEvents 32 1) st2
  let st4 := M.stepEvents ecPubKeySerializeAllocEvents st3
  have hfits' : FitsEvents M lim st
      (ecPubKeySerializeAllocEvents ++
        (ecPubKeySerializeAllocEvents ++
          (rustAllocEvents 32 1 ++
            (ecPubKeySerializeAllocEvents ++ withSenderChainNoneEvents)))) := by
    simpa only [initBobSessionBuildEvents, List.append_assoc] using hfits
  obtain ⟨hfe1, hfits1⟩ := (fitsEvents_append M lim ecPubKeySerializeAllocEvents _ st).mp hfits'
  obtain ⟨hfe2, hfits2⟩ := (fitsEvents_append M lim ecPubKeySerializeAllocEvents _ st1).mp hfits1
  obtain ⟨hfe3, hfits3⟩ := (fitsEvents_append M lim (rustAllocEvents 32 1) _ st2).mp hfits2
  obtain ⟨hfe4, hfe5⟩ :=
    (fitsEvents_append M lim ecPubKeySerializeAllocEvents withSenderChainNoneEvents st3).mp hfits3
  have hst_eq : M.stepEvents withSenderChainNoneEvents st4 =
      M.stepEvents initBobSessionBuildEvents st := by
    dsimp only [st4, st3, st2, st1, initBobSessionBuildEvents]
    simp only [AllocCostModel.stepEvents_append, List.append_assoc]
  have hfe_rk : FitsEvent M lim st2 (.alloc 32) :=
    (by simpa [rustAllocEvents] using hfe3 : FitsEvents M lim st2 [.alloc 32]).1
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hpos32 : 0 < (32 : Nat) := by decide
  have hal1 : (1 : Nat) ≤ 2 ^ 31 := by decide
  have hsum32 : (32 : Nat) + 1 ≤ 2 ^ 63 := by decide
  have hserPub := ls_subroutine_ok_cl_of_plain (callerProg := lsProg_75 H)
    (ecPubKeySerialize_alloc_placed_ok_of_session hshim halloc)
  change subroutine_ok _ (lsmpl.base 205)
    (withLsCl lsmpl (ecPubKeySerializeAllocPlacedSpec M A lim)) at hserPub
  have hwithSender := ls_subroutine_ok_cl_of_block (callerProg := lsProg_75 H)
    (withSenderChain_none_placed_ok_of_session hshim halloc hdealloc hmemcpy)
  change subroutine_ok _ (lsmpl.base 27)
    (withLsCl lsmpl (withSenderChainNonePlacedSpec M A lim)) at hwithSender
  have hshim' : subroutine_ok (lsProg_75 H) (lsρ lsRustNoAllocShimSym) sessionShimBudgetSpec :=
    ls_hook_ok_of_mem hshim
  have halloc0 : subroutine_ok (lsProg_75 H) (lsρ lsRustAllocSym)
      (rustCliAllocBudgetSpec M A lim false) := ls_hook_ok_of_mem halloc
  have halloc' : subroutine_ok (lsProg_75 H) (lsρ lsRustAllocSym)
      (rustCliAllocNoOomExternSpecWithStack M A lim false allocHookStack) :=
    subroutine_ok_rustCliAllocNoOom_externWithStack (stk := allocHookStack)
      (by decide) (by decide) (subroutine_ok_allocNoOom_of_budget halloc0)
  dsimp only [sessionShimBudgetSpec, CryptoVerification.LibsignalTripleRatchet.sessionShimSpec]
    at hshim'
  dsimp only [rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomSpecWithStack,
    LibsignalBinary.Heap.RustLayoutOk, CryptoVerification.RustHeap.LayoutOk, ↓reduceIte] at halloc'
  obtain ⟨rk0, rk1, rk2, rk3, _, hrk_cells⟩ :=
    exists_unpack64_of_length_32 (bs := bytesToBv8 rk) (by simp [bytesToBv8, hrk_len])
  conv =>
    arg 4
    rw [hrk_cells (s0.sp - 656#64), stackAt_entry_some_split (s0.sp - 768#64)]
    simp (config := { maxSteps := 1000000 }) only [
      bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 205)
  wp_steps_sync_pool (lsmpl.base 205)
  simp only [State.setMem_setMem]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl1
  refine call_frame_lscl_bob (spec := ecPubKeySerializeAllocPlacedSpec M A lim)
    (x := ((argPtr, ikBPk), st)) hserPub hcl1
    (by wp_norm_lhs) (by wp_norm_lhs)
    (by simp only [*, State.spAligned, arm64_norm])
    (ret_pc := (blkPl_75).base + 400#64) (by wp_norm_lhs)
    (by
      conv =>
        lhs
        dsimp only [ecPubKeySerializeAllocPlacedSpec]
        simp only [arm64_norm, hsp, hx21, bv_sub_add_lit', BitVec.reduceSub]
      try rfl)
    (by simp only [*, arm64_norm])
    (by sep_focus)
    (fun sm1 hpcm1 hrunm1 hspm1 hcsm1 hclm1 => ?_)
  simp only [*, arm64_norm] at hspm1
  dsimp only [CalleeSavedPreserved, Reg.fp] at hcsm1
  rcases hcsm1 with ⟨hcs2_19, hcs2_20, hcs2_21, hcs2_22, hcs2_23, hcs2_24, hcs2_25, hcs2_26,
    hcs2_27, hcs2_28, hcs2_29, hcs2_vregs⟩
  simp only [*, arm64_norm]
    at hcs2_19 hcs2_20 hcs2_21 hcs2_22 hcs2_23 hcs2_24 hcs2_25 hcs2_26 hcs2_27 hcs2_28 hcs2_29
       hcs2_vregs
  conv =>
    arg 4
    dsimp only [ecPubKeySerializeAllocPlacedSpec]
    simp only [arm64_norm, hsp, bv_sub_add_lit', BitVec.reduceSub,
      sepExists_sepConj_left, sepConj_assoc]
  refine SepWP.exists_elim fun localIkBoxPtr => ?_
  refine SepWP.pure_elim fun ⟨htr2, hx0_1, hx1_1, hne_localIk⟩ => ?_
  apply sepWP_seq_lscl hclm1 (mid := lsmpl.base 205)
  wp_steps_sync_pool (lsmpl.base 205)
  simp only [State.setMem_setMem]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl2
  refine call_frame_lscl_bob (spec := ecPubKeySerializeAllocPlacedSpec M A lim)
    (x := ((argPtr + 128#64, ikAPk), st1)) hserPub hcl2
    (by wp_norm_lhs) (by wp_norm_lhs)
    (by simp only [*, State.spAligned, arm64_norm])
    (ret_pc := (blkPl_75).base + 416#64) (by wp_norm_lhs)
    (by
      conv =>
        lhs
        dsimp only [ecPubKeySerializeAllocPlacedSpec]
        simp only [arm64_norm, hspm1, hcs2_21, hx21, bv_sub_add_lit', BitVec.reduceSub]
      try rfl)
    (by simp only [*, arm64_norm])
    (by sep_focus)
    (fun sm2 hpcm2 hrunm2 hspm2 hcsm2 hclm2 => ?_)
  simp only [*, arm64_norm] at hspm2
  dsimp only [CalleeSavedPreserved, Reg.fp] at hcsm2
  rcases hcsm2 with ⟨hcs3_19, hcs3_20, hcs3_21, hcs3_22, hcs3_23, hcs3_24, hcs3_25, hcs3_26,
    hcs3_27, hcs3_28, hcs3_29, hcs3_vregs⟩
  simp only [*, arm64_norm]
    at hcs3_19 hcs3_20 hcs3_21 hcs3_22 hcs3_23 hcs3_24 hcs3_25 hcs3_26 hcs3_27 hcs3_28 hcs3_29
       hcs3_vregs
  conv =>
    arg 4
    dsimp only [ecPubKeySerializeAllocPlacedSpec]
    simp only [arm64_norm, hspm1, bv_sub_add_lit', BitVec.reduceSub,
      sepExists_sepConj_left, sepConj_assoc]
  refine SepWP.exists_elim fun remoteIkBoxPtr => ?_
  refine SepWP.pure_elim fun ⟨htr3, hx0_2, hx1_2, hne_remoteIk⟩ => ?_
  apply sepWP_seq_lscl hclm2 (mid := lsmpl.base 205)
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_call hshim' ()
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  simp only [State.setMem_setMem]
  refine sepWP_congr_stackAt (sp' := s0.sp - 768#64) (stk := allocHookStack)
    (by simp only [*, arm64_norm]) (hnext := ?_)
  wp_call halloc' (32, 1, st2)
  have hne_rk : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq_rk : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne_rk
  have hm32_rk : memRegion (sf_1.readReg64 (Reg.gpr 0#5)) 32 =
      cells (sf_1.readReg64 (Reg.gpr 0#5)) 4 :=
    ProofLib.memRegion_cells (sf_1.readReg64 (Reg.gpr 0#5)) 4 (by decide)
  conv =>
    arg 4
    simp only [arm64_norm, ‹sf.sp = sm2.sp›, hspm2, hm32_rk, cells, sepConj_emp,
      sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
      sepConj_assoc]
  refine SepWP.exists_elim fun r0 => SepWP.exists_elim fun r1 =>
    SepWP.exists_elim fun r2 => SepWP.exists_elim fun r3 => ?_
  wp_steps_sync_pool (lsmpl.base 205)
  simp only [State.setMem_setMem]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl4
  refine call_frame_lscl_bob (spec := ecPubKeySerializeAllocPlacedSpec M A lim)
    (x := ((argPtr + 160#64, ekAPk), st3)) hserPub hcl4
    (by wp_norm_lhs) (by wp_norm_lhs)
    (by simp only [*, State.spAligned, arm64_norm])
    (ret_pc := (blkPl_75).base + 464#64) (by wp_norm_lhs)
    (by
      conv =>
        lhs
        dsimp only [ecPubKeySerializeAllocPlacedSpec]
        simp only [arm64_norm, ‹sf_1.sp = _›, ‹sf.sp = sm2.sp›, hspm2,
          ‹sf_1.readReg64 (.gpr 21#5) = _›, ‹sf.readReg64 (.gpr 21#5) = _›, hcs3_21, hcs2_21, hx21,
          bv_sub_add_lit', BitVec.reduceSub]
      try rfl)
    (by simp only [*, arm64_norm])
    (by sep_focus)
    (fun sm3 hpcm3 hrunm3 hspm3 hcsm3 hclm3 => ?_)
  simp only [*, arm64_norm] at hspm3
  dsimp only [CalleeSavedPreserved, Reg.fp] at hcsm3
  rcases hcsm3 with ⟨hcs4_19, hcs4_20, hcs4_21, hcs4_22, hcs4_23, hcs4_24, hcs4_25, hcs4_26,
    hcs4_27, hcs4_28, hcs4_29, hcs4_vregs⟩
  simp only [*, arm64_norm]
    at hcs4_19 hcs4_20 hcs4_21 hcs4_22 hcs4_23 hcs4_24 hcs4_25 hcs4_26 hcs4_27 hcs4_28 hcs4_29
       hcs4_vregs
  conv =>
    arg 4
    dsimp only [ecPubKeySerializeAllocPlacedSpec]
    simp only [arm64_norm, ‹sf_1.sp = _›, ‹sf.sp = sm2.sp›, hspm2,
      bv_sub_add_lit', BitVec.reduceSub, sepExists_sepConj_left, sepConj_assoc]
  refine SepWP.exists_elim fun baseKeyBoxPtr => ?_
  refine SepWP.pure_elim fun ⟨htr5, hx0_3, hx1_3, hne_baseKey⟩ => ?_
  apply sepWP_seq_lscl hclm3 (mid := lsmpl.base 27)
  conv =>
    arg 4
    rw [sub488_split_v1 s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  wp_pull_exists
  rename_i pad_f4
  conv =>
    arg 4
    simp (config := { maxSteps := 1000000 }) only [
      cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
      bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  wp_pull_exists
  conv =>
    arg 4
    rw [(ProofLib.memRegion_cells (s0.sp - 240#64) 12 (by decide) :
      memRegion (s0.sp - 240#64) 96 = cells (s0.sp - 240#64) 12)]
    simp (config := { maxSteps := 1000000 }) only [
      cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
      bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  wp_pull_exists
  rename_i w_f8 c0 c1 c2 c3 c4 w_128 d0 d1 d2 w_148 w_150
  wp_steps_sync_pool (lsmpl.base 27)
  simp only [State.setMem_setMem]
  refine SepWP.fold (Entails.of_eq (hrk_cells (sf_1.readReg64 (.gpr 0#5))).symm)
    (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (by
    have h := (hrk_cells (s0.sp - 656#64)).symm
    simp only [bv_sub_add_lit', BitVec.reduceSub] at h
    exact h)) (by sep_focus) ?_
  refine SepWP.fold (cells4_sub768_merge s0.sp _ _ _ _) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (memRegion_160_sub5024 s0.sp)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (by
    have h := bobHead144V1_eq_pointsToBytes (s0.sp - 488#64) localIkBoxPtr remoteIkBoxPtr
      (sf_1.readReg64 (.gpr 0#5)) baseKeyBoxPtr spqrCap spqrBufPtr spqrLen
    simp only [bv_sub_add_lit', BitVec.reduceSub] at h
    exact h)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (by
    have h := post100_pack (s0.sp - 488#64) pad_f4 c0 c1 c2 c3 c4 d0 d1 d2
    simp only [bv_sub_add_lit', BitVec.reduceSub] at h
    exact h)) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl5
  have hφ_ws :
      spkBPk.length = 32 ∧ spkBSk.length = 32 ∧ ck.length = 32 ∧
      (bobHead144Bv8V1 localIkBoxPtr remoteIkBoxPtr (sf_1.readReg64 (.gpr 0#5)) baseKeyBoxPtr
        spqrCap spqrBufPtr spqrLen).length = 144 ∧
      (unpack32 pad_f4 ++ bobTail96Bv8 c0 c1 c2 c3 c4 d0 d1 d2).length = 100 ∧
      FitsEvents M lim st4 withSenderChainNoneEvents :=
    ⟨hspkPk_len, hspkSk_len, hck_len, bobHead144Bv8V1_length _ _ _ _ _ _ _,
      by simp [unpack32, bobTail96Bv8], hfe5⟩
  refine call_frame_lscl_bob (spec := withSenderChainNonePlacedSpec M A lim) (x :=
    (⟨outPtr, s0.sp - 488#64, rkp, spkBPk, spkBSk, s0.sp - 624#64, ck, 0#32,
      bobHead144Bv8V1 localIkBoxPtr remoteIkBoxPtr (sf_1.readReg64 (.gpr 0#5)) baseKeyBoxPtr
        spqrCap spqrBufPtr spqrLen,
      unpack32 pad_f4 ++ bobTail96Bv8 c0 c1 c2 c3 c4 d0 d1 d2⟩, st4)) hwithSender hcl5
    (by wp_norm_lhs) (by wp_norm_lhs)
    (by simp only [*, State.spAligned, arm64_norm])
    (ret_pc := (blkPl_75).base + 564#64) (by wp_norm_lhs)
    (by
      conv =>
        lhs
        dsimp only [withSenderChainNonePlacedSpec]
        simp only [arm64_norm, hspm3, hcs4_19, hcs3_19, hcs2_19, hx19,
          hcs4_20, hcs3_20, hcs2_20, hx20, hcs4_23, hcs3_23, hcs2_23, hx23,
          hcs4_27, hcs3_27, hcs2_27, hx27, bv_sub_add_lit', BitVec.reduceSub]
      try rfl)
    hφ_ws
    (by sep_focus)
    (fun sm4 hpcm4 hrunm4 hspm4 hcsm4 hclm4 => ?_)
  simp only [*, arm64_norm] at hspm4
  dsimp only [CalleeSavedPreserved, Reg.fp] at hcsm4
  rcases hcsm4 with ⟨hcs5_19, hcs5_20, hcs5_21, hcs5_22, hcs5_23, hcs5_24, hcs5_25, hcs5_26,
    hcs5_27, hcs5_28, hcs5_29, hcs5_vregs⟩
  simp only [*, arm64_norm]
    at hcs5_19 hcs5_20 hcs5_21 hcs5_22 hcs5_23 hcs5_24 hcs5_25 hcs5_26 hcs5_27 hcs5_28 hcs5_29
       hcs5_vregs
  conv =>
    arg 4
    dsimp only [withSenderChainNonePlacedSpec]
    simp only [arm64_norm, hspm3, hst_eq, bv_sub_add_lit', BitVec.reduceSub,
      sepExists_sepConj_left, sepConj_assoc]
  refine SepWP.exists_elim fun ratchetPubBoxPtr =>
    SepWP.exists_elim fun ratchetPrivBoxPtr =>
    SepWP.exists_elim fun chainKeyBoxPtr => ?_
  refine SepWP.pure_elim fun ⟨htr6, hne_rPub, hne_rPriv, hne_ck⟩ => ?_
  refine SepWP.fold (Entails.of_eq (bobSession344V1_pack outPtr
    localIkBoxPtr remoteIkBoxPtr (sf_1.readReg64 (.gpr 0#5)) baseKeyBoxPtr
    spqrCap spqrBufPtr spqrLen ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
    pad_f4 c0 c1 c2 c3 c4 d0 d1 d2))
    (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (by
    have h := bobSession344V1_pack (s0.sp - 488#64)
      localIkBoxPtr remoteIkBoxPtr (sf_1.readReg64 (.gpr 0#5)) baseKeyBoxPtr
      spqrCap spqrBufPtr spqrLen ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
      pad_f4 c0 c1 c2 c3 c4 d0 d1 d2
    simp only [bv_sub_add_lit', BitVec.reduceSub] at h
    exact h)) (by sep_focus) ?_
  have h344_weaken :
      ((s0.sp - 488#64) ↦ₛ bobSession344Bv8V1 localIkBoxPtr remoteIkBoxPtr
        (sf_1.readReg64 (.gpr 0#5)) baseKeyBoxPtr spqrCap spqrBufPtr spqrLen
        ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
        pad_f4 c0 c1 c2 c3 c4 d0 d1 d2) ⊢
      memRegion (s0.sp - 488#64) 344 := by
    have h := pointsToBytes_entails_memRegion (s0.sp - 488#64)
      (bobSession344Bv8V1 localIkBoxPtr remoteIkBoxPtr (sf_1.readReg64 (.gpr 0#5))
        baseKeyBoxPtr spqrCap spqrBufPtr spqrLen ratchetPubBoxPtr ratchetPrivBoxPtr
        chainKeyBoxPtr pad_f4 c0 c1 c2 c3 c4 d0 d1 d2)
    rwa [bobSession344Bv8V1_length] at h
  refine SepWP.fold h344_weaken (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (stackAt_entry_some_merge s0.sp)) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨localIkBoxPtr, remoteIkBoxPtr, sf_1.readReg64 (.gpr 0#5), baseKeyBoxPtr,
    ratchetPubBoxPtr, ratchetPrivBoxPtr, chainKeyBoxPtr,
    pad_f4, c0, c1, c2, c3, c4, d0, d1, d2,
    hne_localIk, hne_remoteIk, hne_rk, hne_baseKey,
    hne_rPub, hne_rPriv, hne_ck,
    Entails.of_eq (by ac_rfl),
    hclm4, by wp_norm_goal, by wp_norm_goal, by simp only [*, arm64_norm],
    by simp only [*, arm64_norm], by simp only [*, arm64_norm]⟩

theorem initBob_session_build_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {Qp : State → SepProp → Prop}
    (hshim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym allocMemcpyVmSpec)
    (s0 s : State) (st : M.σ) (argPtr rkp outPtr : BitVec 64)
    (spqrCap spqrBufPtr spqrLen : BitVec 64)
    (ikBPk ikAPk ekAPk spkBPk spkBSk rk ck : Bytes)
    (Frame : SepProp)
    (hcl0 : LibsignalCodeLoaded lsmpl s.mem)
    (hfits : FitsEvents M lim st initBobSessionBuildEvents)
    (hikB_len : ikBPk.length = 32)
    (hikA_len : ikAPk.length = 32)
    (hekA_len : ekAPk.length = 32)
    (hspkPk_len : spkBPk.length = 32)
    (hspkSk_len : spkBSk.length = 32)
    (hrk_len : rk.length = 32)
    (hck_len : ck.length = 32)
    (hsp0_align : s0.sp &&& 15#64 == 0#64)
    (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (blkPl_75).base + 252#64)
    (hsp : s.sp = s0.sp - 768#64)
    (hx19 : s.readReg64 (.gpr 19#5) = outPtr)
    (hx20 : s.readReg64 (.gpr 20#5) = rkp)
    (hx21 : s.readReg64 (.gpr 21#5) = argPtr)
    (hx23 : s.readReg64 (.gpr 23#5) = s0.sp - 768#64)
    (hx27 : s.readReg64 (.gpr 27#5) = s0.sp - 488#64)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (lsProg_75 H) ((blkPl_75).base + 564#64) s
      (((s0.sp - 768#64) ↦₆₄ 0#64) ∗ ((s0.sp - 760#64) ↦₆₄ spqrCap) ∗
       ((s0.sp - 752#64) ↦₆₄ spqrBufPtr) ∗ ((s0.sp - 744#64) ↦₆₄ spqrLen) ∗
       ((s0.sp - 656#64) ↦ₛ bytesToBv8 rk) ∗ ((s0.sp - 624#64) ↦ₛ bytesToBv8 ck) ∗
       ((s0.sp - 592#64) ↦₃₂ 0#32) ∗
       memRegion (s0.sp - 488#64) 344 ∗
       (argPtr ↦ₛ bytesToBv8 ikBPk) ∗ ((argPtr + 128#64) ↦ₛ bytesToBv8 ikAPk) ∗
       ((argPtr + 160#64) ↦ₛ bytesToBv8 ekAPk) ∗
       (rkp ↦ₛ bytesToBv8 spkBPk) ∗ ((rkp + 32#64) ↦ₛ bytesToBv8 spkBSk) ∗
       memRegion outPtr 344 ∗
       stackAt (s0.sp - 768#64) pqxdhEntryStack ∗ A.pool lim st s ∗ Frame)
      (fun sf P_f =>
        ∃ (localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
           ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr : BitVec 64)
          (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64),
          localIkBoxPtr ≠ 0#64 ∧ remoteIkBoxPtr ≠ 0#64 ∧ rootKeyBoxPtr ≠ 0#64 ∧
          baseKeyBoxPtr ≠ 0#64 ∧ ratchetPubBoxPtr ≠ 0#64 ∧ ratchetPrivBoxPtr ≠ 0#64 ∧
          chainKeyBoxPtr ≠ 0#64 ∧ (P_f ⊢
            (outPtr ↦ₛ bobSession344Bv8V1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
              spqrCap spqrBufPtr spqrLen ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
              pad_f4 c0 c1 c2 c3 c4 d0 d1 d2) ∗
            memRegion (s0.sp - 768#64) 32 ∗
            ((s0.sp - 656#64) ↦ₛ bytesToBv8 rk) ∗ ((s0.sp - 624#64) ↦ₛ bytesToBv8 ck) ∗
            ((s0.sp - 592#64) ↦₃₂ 0#32) ∗
            memRegion (s0.sp - 488#64) 344 ∗
            (argPtr ↦ₛ bytesToBv8 ikBPk) ∗ ((argPtr + 128#64) ↦ₛ bytesToBv8 ikAPk) ∗
            ((argPtr + 160#64) ↦ₛ bytesToBv8 ekAPk) ∗
            (rkp ↦ₛ bytesToBv8 spkBPk) ∗ ((rkp + 32#64) ↦ₛ bytesToBv8 spkBSk) ∗
            (localIkBoxPtr ↦ₛ bytesToBv8 (encodeEC ikBPk)) ∗ A.live localIkBoxPtr 33 1 ∗
            (remoteIkBoxPtr ↦ₛ bytesToBv8 (encodeEC ikAPk)) ∗ A.live remoteIkBoxPtr 33 1 ∗
            (rootKeyBoxPtr ↦ₛ bytesToBv8 rk) ∗ A.live rootKeyBoxPtr 32 1 ∗
            (baseKeyBoxPtr ↦ₛ bytesToBv8 (encodeEC ekAPk)) ∗ A.live baseKeyBoxPtr 33 1 ∗
            (ratchetPubBoxPtr ↦ₛ bytesToBv8 (encodeEC spkBPk)) ∗
            A.live ratchetPubBoxPtr 33 1 ∗
            (ratchetPrivBoxPtr ↦ₛ bytesToBv8 spkBSk) ∗ A.live ratchetPrivBoxPtr 32 1 ∗
            (chainKeyBoxPtr ↦ₛ bytesToBv8 ck) ∗ A.live chainKeyBoxPtr 32 1 ∗
            stackAt (s0.sp - 768#64) pqxdhEntryStack ∗
            A.pool lim (M.stepEvents initBobSessionBuildEvents st) sf ∗ Frame) ∧
          LibsignalCodeLoaded lsmpl sf.mem ∧
          sf.status = ExecStatus.Running ∧
          sf.pc = (blkPl_75).base + 564#64 ∧
          sf.sp = s0.sp - 768#64 ∧ sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0)
      Qp :=
  initBob_session_build_placed_of_session
    (hookSat_sessionShimBudget_of_rustAllocShimVm hshim) halloc hdealloc
    (hookSat_sessionMemcpyRegionBudget_of_allocMemcpyVm hmemcpy)
    s0 s st argPtr rkp outPtr spqrCap spqrBufPtr spqrLen
    ikBPk ikAPk ekAPk spkBPk spkBSk rk ck Frame
    hcl0 hfits hikB_len hikA_len hekA_len hspkPk_len hspkSk_len hrk_len hck_len
    hsp0_align hrun hpc hsp hx19 hx20 hx21 hx23 hx27 htr hvregs

end LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobPlacedBudget
