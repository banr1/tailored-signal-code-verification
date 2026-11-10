/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.States1aPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesChainPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesChain
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop2
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.WP.Apply

/-!
# Budget-Threaded `spqr::send` Phase 3a Panic Blocks, Epilogue, and Error Cleanup

Threads `RustCliAllocBudget`, `VmPreserved`, and `FreeOnlyEvs` through the `[LibsignalPlacement]`
panic blocks (`+12004`, `+13552`), shared epilogue (`+4576 -> +4664`), and error cleanup paths
of `spqr::send::<signal_session_ratchet::Coins>`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesChainPlacedBudget

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement extract_withMemEq libsignalSessionCode lsmpl lsρ
   sepWP_seq_lscl withLsCodeLoaded withMemEq)
open CryptoVerification.Cli.SpqrV1.Drop
  (chunkedStatesLocal1JumpTablePlacedAt chunkedStatesLocal1JumpTableSym)
open CryptoVerification.Cli.SpqrV1.Top.Send (spqrSendPlacedEntry spqrSendPlacedProg)
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced (blkPC_427 blkPl_427)
open CryptoVerification.LibsignalSpqrV1 (EpochSecret States VersionNegotiationPB spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalTripleRatchet (spqrSendResultAt spqrSendStack)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Drop
  (DropChunkedStatesGhost cap_ne_zero_lt_one_false cap_ne_zero_slt_one_false chunkedStatesAt
   chunkedStatesSize dropStackPoly64 optVersionNegotiationPBAt_none_entails_memRegion_48
   vecCapPtrDealloc versionNegotiationPBAt_entails_dealloc vnHeader_entails_memRegion_48)
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation (noneCap)
open CryptoVerification.SpqrV1.Top.Send
  (chainOrigSlotAt chainOrigSlotAt_entails_memRegion_80 chainOrigSlotAt_none chainOrigSlotAt_of_ne
   memRegion_72_split_byte memRegion_72_split_words3 optEpochSecretRegSlotAt
   optEpochSecretRegSlotAt_some_entails_dealloc sendResultAt_none_of_byte
   sendResultAt_none_of_words3 spqrSendCalleeStack spqrSendSavedRegs stack_restore_spqrSend
   ule_sub_one_true_of_pos ult_sub_one_false_of_pos)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
   RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Proofs.Cli.SpqrV1.Drop.States1aPlacedBudget (dropChunkedStatesLocal1PlacedSpec)

export CryptoVerification.Cli.SpqrV1.Drop
  (chunkedStatesLocal1JumpTablePlacedAt chunkedStatesLocal1JumpTableSym)
export CryptoVerification.Cli.SpqrV1.Top.Send
  (corePanic_spqrSend_placed_extern panicSubOverflow_spqrSend_placed_extern)
export LibsignalBinary.Proofs.Cli.SpqrV1.Drop.States1aPlacedBudget (dropChunkedStatesLocal1PlacedSpec)

variable [LibsignalPlacement]

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr Program.fnOff Obj.lookup
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm]
  LibsignalBinary.Heap.RustCliAllocBudget.pool_setPC LibsignalBinary.Heap.RustCliAllocBudget.pool_advancePC
  LibsignalBinary.Heap.RustCliAllocBudget.pool_setPState LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg64
  LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg32 LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg
attribute [local simp, local arm64_norm]
  CryptoVerification.SpqrV1.Drop.none2Cap_add_two_beq_zero
  CryptoVerification.SpqrV1.Drop.noneCap_add_two_beq_zero
attribute [local simp, local arm64_norm, local wp_norm]
  CryptoVerification.SpqrV1.Top.Send.extractLsb_lo_append64
  CryptoVerification.SpqrV1.Top.Send.extractLsb_hi_append64

/-- Budget-threaded relocatable `__rust_dealloc` hook contract on `spqrSendPlacedProg ext`. -/
abbrev DeallocOkPlaced (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (spqrSendPlacedProg ext)
    (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
    (rustCliDeallocBudgetSpec M A lim)

private def deallocFreeOnlySpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × Nat × Nat × M.σ) where
  pre := (rustCliDeallocBudgetSpec M A lim).pre
  post := fun (_, size, align, st) s0 sf =>
    ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf⌝ ∗
      A.pool lim (M.stepEvents (rustDeallocEvents size align) st) sf ∗ stackAt s0.sp allocHookStack

private theorem subroutine_ok_deallocFreeOnly {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok prog entry (deallocFreeOnlySpec M A lim) := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [rustCliDeallocBudgetSpec, deallocFreeOnlySpec] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  exact ⟨⟨hq.1.1.2.1, hq.1.1⟩, hq.2⟩

omit [LibsignalPlacement] in
private theorem subroutine_ok_withMemEq_of_withLsCodeLoaded {α : Type} {prog : Program}
    {entry : BitVec 64} {pl : MultiPlacement} {spec : Spec α} {m : Memory}
    (hcl : LibsignalCodeLoaded pl m)
    (h : subroutine_ok prog entry (withLsCodeLoaded pl spec)) :
    subroutine_ok prog entry (withMemEq m spec) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => by
      obtain ⟨hm, hpre⟩ := extract_withMemEq hp
      dsimp only [withLsCodeLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨hm ▸ hcl, hpre⟩)
    (fun _ _ _ _ hq => hq)

private theorem seq_vm_lscl {Hk : String → Option (State → State)}
    {mid target : BitVec 64} {s : State}
    {Pre P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP ((blkPC_427).rebase (blkPl_427).base Hk) mid s Pre
      (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → VmPreserved s sm → Q sm →
      SepWP ((blkPC_427).rebase (blkPl_427).base Hk) target sm P_mid post) :
    SepWP ((blkPC_427).rebase (blkPl_427).base Hk) target s Pre post :=
  sepWP_seq_lscl hcl (SepWP.mono h1 fun sm _Pm hpc hrun ⟨hvm, hent, hQ⟩ hcl_m =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hcl_m hvm hQ))

/-! ## Panic Blocks (`+12004` and `+13552`) -/

/-- `+12004` (`0x33740`): steps to `lsρ "_RNvNtCskxtBwYRO61I_4core9panicking5panic"` for `sendKeySomeWithoutChain`. -/
theorem step_panic_33740_placed {ext : String → Option (State → State)}
    (s : State) (P : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry + 12004#64)
    (hrun : s.status = .Running) :
    SepWP (spqrSendPlacedProg ext)
      (lsρ "_RNvNtCskxtBwYRO61I_4core9panicking5panic") s P
      (fun sf Q => VmPreserved s sf ∧ sf.status = .Running ∧ sf.trace = s.trace ∧ sf.mem = s.mem ∧ (Q ⊢ P)) := by
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_steps
  exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, rfl, Entails.refl _⟩

/-- `+13552` (`0x33d4c`): steps to `lsρ "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_sub_overflow"`
    for `sendEpochUnderflow` (`msg.epoch == 0`). -/
theorem step_panic_33d4c_placed {ext : String → Option (State → State)}
    (s : State) (P : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry + 13552#64)
    (hrun : s.status = .Running) :
    SepWP (spqrSendPlacedProg ext)
      (lsρ "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_sub_overflow") s P
      (fun sf Q => VmPreserved s sf ∧ sf.status = .Running ∧ sf.trace = s.trace ∧ sf.mem = s.mem ∧ (Q ⊢ P)) := by
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_steps
  exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, rfl, Entails.refl _⟩

/-! ## Shared Epilogue (`+4576 -> +4600 -> +4632 -> +4664`) -/

/-- `+4632 -> +4664` (`0x31a74 -> 0x31a94`, 9 instructions = 36 bytes):
    restores `sp = s0.sp`, pops callee-saved registers `x19..x30`, and returns to `s0.readReg64 .x30`. -/
theorem step_epilogue_31a74_placed {ext : String → Option (State → State)}
    (s0 s : State) (Frame : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry + 4632#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWP (spqrSendPlacedProg ext) (s0.readReg64 .x30) s
      (stackAt s.sp spqrSendCalleeStack ∗
        memRegion s.sp 0x1f20 ∗
        spqrSendSavedRegs s.sp s0 ∗
        Frame)
      (fun sf Q => VmPreserved s sf ∧
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s0.sp ∧
        Arm64.CalleeSavedPreserved s0 sf ∧
        (Q ⊢ stackAt s0.sp spqrSendStack ∗ Frame)) := by
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, spqrSendSavedRegs, BitVec.ofNat_eq_ofNat] at hpc ⊢
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := by
    rw [hsp]; exact spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  have hsp_add1 : s.sp + 4096#64 + 3872#64 = s.sp + 0x1f20#64 := by bv_omega
  have hsp_add2_beq : ((s.sp + 0x1f20#64) &&& 15#64 == 0#64) = true := by
    rw [show s.sp + 0x1f20#64 = s0.sp - 0x60#64 by rw [hsp]; bv_omega]
    exact spAligned_sub s0.sp 0x60#64 hsp0_align (by decide)
  have hsp_add2 : (s.sp + 0x1f20#64) &&& 15#64 = 0#64 := by
    rwa [beq_iff_eq] at hsp_add2_beq
  have hsp_end : s.sp + 0x1f20#64 + 96#64 = s0.sp := by rw [hsp]; bv_omega
  by_vm_steps (
    wp_steps
    refine ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, ?_, ?_, ?_⟩
    · simp only [wp_norm, arm64_norm, hsp_add1, hsp_end]
    · simp only [Arm64.CalleeSavedPreserved, Reg.fp, wp_norm, arm64_norm, hsp_add1, hsp_end, hvregs, and_self]
    · rw [hsp]
      refine Entails.trans (Entails.of_eq ?_)
        (sepConj_mono_left (stack_restore_spqrSend s0.sp s0))
      unfold spqrSendSavedRegs
      sep_ac_rfl)

/-- `+4600 -> +4632` (`0x31a54 -> 0x31a74`, 8 instructions = 32 bytes):
    checks `x23` and (when `x23 = noneCap`) `[sp + 0x60] = noneCap`, reaching `+4632` with
    `memRegion (s.sp + 0x60#64) 80`. -/
theorem step_epilogue_31a54_placed {ext : String → Option (State → State)}
    (s : State) (x23 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry + 4600#64)
    (hrun : s.status = .Running)
    (hx23 : s.readReg64 .x23 = x23)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (spqrSendPlacedProg ext)
      (spqrSendPlacedEntry + 4632#64) s
      (chainOrigSlotAt s.sp x23 ∗ Frame)
      (fun sf Q => VmPreserved s sf ∧
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ memRegion (s.sp + 0x60#64) 80 ∗ Frame)) := by
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  by_vm_steps (
    by_cases hnone : x23 = noneCap
    · subst hnone
      rw [chainOrigSlotAt_none]
      wp_steps
      refine ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, ?_⟩
      rw [← chainOrigSlotAt_none]
      exact sepConj_mono_left (chainOrigSlotAt_entails_memRegion_80 s.sp noneCap)
    · rw [chainOrigSlotAt_of_ne hnone]
      have hcmn : (x23 + 1#64 != 0#64) = true := by
        rw [bne_iff_ne]
        intro h; apply hnone; revert h; bv_omega
      wp_steps
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, Entails.refl _⟩)

/-- `+4576 -> +4600` (`0x31a3c -> 0x31a54`, 6 instructions = 24 bytes):
    drops `optVersionNegotiationPBAt A.repAlloc (s.sp + 0x30#64) vn` and reaches `+4600` with
    `memRegion (s.sp + 0x30#64) 48`. -/
theorem step_epilogue_31a3c_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkPlaced M A lim ext)
    (s : State) (st : M.σ) (vn : Option VersionNegotiationPB) (x23 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry + 4576#64)
    (hrun : s.status = .Running)
    (hx23 : s.readReg64 .x23 = x23)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (spqrSendPlacedProg ext)
      (spqrSendPlacedEntry + 4600#64) s
      (CryptoVerification.SpqrV1.ProtoRepr.optVersionNegotiationPBAt A.repAlloc (s.sp + 0x30#64) vn ∗
        A.pool lim st s ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          AllocCallPreserved s sf ∧
          sf.status = .Running ∧
          sf.trace = s.trace ∧
          sf.sp = s.sp ∧
          sf.readReg64 .x23 = x23 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s ∧
          (Q ⊢ memRegion (s.sp + 0x30#64) 48 ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc ⊢
  have hstack_dealloc :
      stackAt s.sp spqrSendCalleeStack =
        memRegion (s.sp - 123008#64)
          (spqrSendCalleeStack - allocHookStack) ∗
          stackAt s.sp allocHookStack :=
    ProofLib.stackAt_split_bottom s.sp allocHookStack
      (spqrSendCalleeStack - allocHookStack) (by decide)
  have hadd8 : (s.sp + 48#64) + 8#64 = s.sp + 56#64 := by bv_omega
  have hadd16 : (s.sp + 48#64) + 16#64 = s.sp + 64#64 := by bv_omega
  have hmerge_none :
      ((s.sp + 48#64) ↦₆₄ CryptoVerification.LibsignalTripleRatchetRepr.noneCap) ∗ memRegion (s.sp + 56#64) 40 ⊢
        memRegion (s.sp + 48#64) 48 := by
    rw [← hadd8]
    exact optVersionNegotiationPBAt_none_entails_memRegion_48 (s.sp + 48#64)
  have hmerge_vn : ∀ c p : BitVec 64,
      ((s.sp + 48#64) ↦₆₄ c) ∗ ((s.sp + 56#64) ↦₆₄ p) ∗ memRegion (s.sp + 64#64) 32 ⊢
        memRegion (s.sp + 48#64) 48 := by
    intro c p
    have h := vnHeader_entails_memRegion_48 (s.sp + 48#64) c p
    rwa [hadd8, hadd16] at h
  cases vn with
  | none =>
    dsimp only [CryptoVerification.SpqrV1.ProtoRepr.optVersionNegotiationPBAt]
    rw [hadd8]
    wp_steps
    refine SepWP.focus_weaken hmerge_none (by sep_focus) ?_
    refine ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨[], LibsignalBinary.Heap.FreeOnlyEvs.nil, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, ?_⟩
    simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, LibsignalBinary.Heap.RustCliAllocBudget.pool_setPC,
      LibsignalBinary.Heap.RustCliAllocBudget.pool_setPState, LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg64]
    exact Entails.refl _
  | some v =>
    dsimp only [CryptoVerification.SpqrV1.ProtoRepr.optVersionNegotiationPBAt]
    refine SepWP.focus_weaken (versionNegotiationPBAt_entails_dealloc A.repAlloc (s.sp + 48#64) v) (by sep_focus) ?_
    wp_pull_exists; rename_i g; rcases g with ⟨cap, ptr⟩
    wp_focus_pure; intro hcap_lt
    dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live] at hcap_lt ⊢
    by_cases hc0 : (cap == 0#64) = true <;>
      simp only [hc0, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · have hc_eq : cap = 0#64 := by rwa [beq_iff_eq] at hc0
      subst hc_eq
      wp_steps
      refine SepWP.focus_weaken (hmerge_vn 0#64 ptr) (by sep_focus) ?_
      refine ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨[], LibsignalBinary.Heap.FreeOnlyEvs.nil, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, ?_⟩
      simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, LibsignalBinary.Heap.RustCliAllocBudget.pool_setPC,
        LibsignalBinary.Heap.RustCliAllocBudget.pool_setPState, LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg64]
      exact Entails.refl _
    · have hslt := cap_ne_zero_slt_one_false hcap_lt hc0
      have hlt_false := cap_ne_zero_lt_one_false hcap_lt hc0
      rw [hstack_dealloc]
      wp_steps
      wp_call hdealloc_fo (ptr, cap.toNat, 1, st)
      refine SepWP.focus_weaken (hmerge_vn cap ptr) (by sep_focus) ?_
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨rustDeallocEvents cap.toNat 1, LibsignalBinary.Heap.FreeOnlyEvs.singleton 1 cap.toNat,
          by simp only [wp_norm, arm64_norm, *],
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by simp only [wp_norm, arm64_norm, *],
          Entails.of_eq (by simp only [hsp_sf, ← hstack_dealloc]; sep_ac_rfl)⟩

/-! ## Error Cleanup Paths (`+3848`, `+3896`, `+3920 -> +4576`) -/

/-- `+3920 -> +4576` (`0x317ac -> 0x31a3c`, 8 instructions = 32 bytes):
    drops `optEpochSecretRegSlotAt A.repAlloc s.sp x21 x27 key` and reaches `+4576`
    with `memRegion (s.sp + 0x1bc0#64) 16`. -/
theorem step_drop_key_317ac_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkPlaced M A lim ext)
    (s : State) (st : M.σ) (x21 x27 x23 : BitVec 64) (key : Option EpochSecret) (Frame : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry + 3920#64)
    (hrun : s.status = .Running)
    (hx21 : s.readReg64 .x21 = x21)
    (hx27 : s.readReg64 .x27 = x27)
    (hx23 : s.readReg64 .x23 = x23)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (spqrSendPlacedProg ext)
      (spqrSendPlacedEntry + 4576#64) s
      (optEpochSecretRegSlotAt A.repAlloc s.sp x21 x27 key ∗
        A.pool lim st s ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          AllocCallPreserved s sf ∧
          sf.status = .Running ∧
          sf.trace = s.trace ∧
          sf.sp = s.sp ∧
          sf.readReg64 .x23 = x23 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s ∧
          (Q ⊢ memRegion (s.sp + 0x1bc0#64) 16 ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc ⊢
  have hstack_dealloc :
      stackAt s.sp spqrSendCalleeStack =
        memRegion (s.sp - 123008#64)
          (spqrSendCalleeStack - allocHookStack) ∗
          stackAt s.sp allocHookStack :=
    ProofLib.stackAt_split_bottom s.sp allocHookStack
      (spqrSendCalleeStack - allocHookStack) (by decide)
  cases key with
  | none =>
    dsimp only [optEpochSecretRegSlotAt]
    wp_focus_pure; intro hx21_eq
    subst hx21_eq
    wp_steps
    refine ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨[], LibsignalBinary.Heap.FreeOnlyEvs.nil, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, ?_⟩
    simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, LibsignalBinary.Heap.RustCliAllocBudget.pool_setPC,
      LibsignalBinary.Heap.RustCliAllocBudget.pool_setPState, LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg64]
    exact Entails.refl _
  | some es =>
    refine SepWP.focus_weaken (optEpochSecretRegSlotAt_some_entails_dealloc A.repAlloc s.sp x21 x27 es) (by sep_focus) ?_
    wp_focus_pure; intro hcap_lt
    dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live] at hcap_lt ⊢
    by_cases hc0 : (x21 == 0#64) = true <;>
      simp only [hc0, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · have hc_eq : x21 = 0#64 := by rwa [beq_iff_eq] at hc0
      subst hc_eq
      wp_steps
      refine ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨[], LibsignalBinary.Heap.FreeOnlyEvs.nil, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, ?_⟩
      simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, LibsignalBinary.Heap.RustCliAllocBudget.pool_setPC,
        LibsignalBinary.Heap.RustCliAllocBudget.pool_setPState, LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg64]
      exact Entails.refl _
    · have hult := ult_sub_one_false_of_pos hcap_lt hc0
      rw [hstack_dealloc]
      wp_steps
      wp_call hdealloc_fo (x27, x21.toNat, 1, st)
      wp_steps
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨rustDeallocEvents x21.toNat 1, LibsignalBinary.Heap.FreeOnlyEvs.singleton 1 x21.toNat,
          by simp only [wp_norm, arm64_norm, *],
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by simp only [wp_norm, arm64_norm, *],
          Entails.of_eq (by
            simp only [LibsignalBinary.Heap.RustCliAllocBudget.pool_setPC, hsp_sf, ← hstack_dealloc]
            sep_ac_rfl)⟩

/-- `+3880 -> +4576` (`0x31784 -> 0x31a3c`):
    drops `optEpochSecretRegSlotAt A.repAlloc s.sp x21 x27 key` and reaches `+4576`
    with `memRegion (s.sp + 0x1bc0#64) 16`. -/
theorem step_drop_key_31784_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkPlaced M A lim ext)
    (s : State) (st : M.σ) (x21 x27 x23 : BitVec 64) (key : Option EpochSecret) (Frame : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry + 3880#64)
    (hrun : s.status = .Running)
    (hx21 : s.readReg64 .x21 = x21)
    (hx27 : s.readReg64 .x27 = x27)
    (hx23 : s.readReg64 .x23 = x23)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (spqrSendPlacedProg ext)
      (spqrSendPlacedEntry + 4576#64) s
      (optEpochSecretRegSlotAt A.repAlloc s.sp x21 x27 key ∗
        A.pool lim st s ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          AllocCallPreserved s sf ∧
          sf.status = .Running ∧
          sf.trace = s.trace ∧
          sf.sp = s.sp ∧
          sf.readReg64 .x23 = x23 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s ∧
          (Q ⊢ memRegion (s.sp + 0x1bc0#64) 16 ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc ⊢
  have hstack_dealloc :
      stackAt s.sp spqrSendCalleeStack =
        memRegion (s.sp - 123008#64)
          (spqrSendCalleeStack - allocHookStack) ∗
          stackAt s.sp allocHookStack :=
    ProofLib.stackAt_split_bottom s.sp allocHookStack
      (spqrSendCalleeStack - allocHookStack) (by decide)
  cases key with
  | none =>
    dsimp only [optEpochSecretRegSlotAt]
    wp_focus_pure; intro hx21_eq
    subst hx21_eq
    wp_steps
    refine ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨[], LibsignalBinary.Heap.FreeOnlyEvs.nil, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, ?_⟩
    simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, LibsignalBinary.Heap.RustCliAllocBudget.pool_setPC,
      LibsignalBinary.Heap.RustCliAllocBudget.pool_setPState, LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg64]
    exact Entails.refl _
  | some es =>
    refine SepWP.focus_weaken (optEpochSecretRegSlotAt_some_entails_dealloc A.repAlloc s.sp x21 x27 es) (by sep_focus) ?_
    wp_focus_pure; intro hcap_lt
    dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live] at hcap_lt ⊢
    by_cases hc0 : (x21 == 0#64) = true <;>
      simp only [hc0, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · have hc_eq : x21 = 0#64 := by rwa [beq_iff_eq] at hc0
      subst hc_eq
      wp_steps
      refine ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨[], LibsignalBinary.Heap.FreeOnlyEvs.nil, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, ?_⟩
      simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, LibsignalBinary.Heap.RustCliAllocBudget.pool_setPC,
        LibsignalBinary.Heap.RustCliAllocBudget.pool_setPState, LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg64]
      exact Entails.refl _
    · have hule := ule_sub_one_true_of_pos hcap_lt hc0
      rw [hstack_dealloc]
      wp_steps
      wp_call hdealloc_fo (x27, x21.toNat, 1, st)
      wp_steps
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨rustDeallocEvents x21.toNat 1, LibsignalBinary.Heap.FreeOnlyEvs.singleton 1 x21.toNat,
          by simp only [wp_norm, arm64_norm, *],
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by simp only [wp_norm, arm64_norm, *],
          Entails.of_eq (by
            simp only [LibsignalBinary.Heap.RustCliAllocBudget.pool_setPC, hsp_sf, ← hstack_dealloc]
            sep_ac_rfl)⟩

/-- `+3896 -> +4576` (`0x31794 -> 0x31a3c`):
    `Error::ChainNotAvailable` cleanup when `state_pb.chain = none` and `state_pb.version_negotiation = none`.
    Writes `spqrSendResultAt A.repAlloc ret none`, drops `st1` at `s.sp + 0x190#64` via Block `443`,
    drops `key` in `(x21, x27, [s.sp + 0x1bc0])`, and reaches `+4576`. -/
theorem step_err_31794_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : DeallocOkPlaced M A lim ext)
    (hdrop_states : subroutine_ok (spqrSendPlacedProg ext)
      (lsmpl.base 443) (withLsCodeLoaded lsmpl (dropChunkedStatesLocal1PlacedSpec M A lim F)))
    (s : State) (st : M.σ) (ret x21 x27 x23 : BitVec 64)
    (st1 : States spqrPolyApi (spqrAuthApi F))
    (key : Option EpochSecret) (Frame : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 3896#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = x21)
    (hx27 : s.readReg64 .x27 = x27)
    (hx23 : s.readReg64 .x23 = x23)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (spqrSendPlacedProg ext)
      (spqrSendPlacedEntry + 4576#64) s
      (memRegion ret 72 ∗
        chunkedStatesAt A.repAlloc (s.sp + 0x190#64) st1 ∗
        optEpochSecretRegSlotAt A.repAlloc s.sp x21 x27 key ∗
        chunkedStatesLocal1JumpTablePlacedAt ∗
        A.pool lim st s ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          AllocCallPreserved s sf ∧
          sf.status = .Running ∧
          sf.trace = s.trace ∧
          sf.sp = s.sp ∧
          sf.readReg64 .x23 = x23 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s ∧
          (Q ⊢ spqrSendResultAt A.repAlloc ret none ∗
            memRegion (s.sp + 0x190#64) 928 ∗
            memRegion (s.sp + 0x1bc0#64) 16 ∗
            chunkedStatesLocal1JumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hstack_drop :
      stackAt s.sp spqrSendCalleeStack =
        memRegion (s.sp - 123008#64)
          (spqrSendCalleeStack - dropStackPoly64) ∗
          stackAt s.sp dropStackPoly64 :=
    ProofLib.stackAt_split_bottom s.sp dropStackPoly64
      (spqrSendCalleeStack - dropStackPoly64) (by decide)
  refine SepWP.seq
    (mid := spqrSendPlacedEntry + 3920#64)
    (Mid := fun s1 P1 =>
      ∃ evs₁ : List AllocEvent,
        FreeOnlyEvs evs₁ ∧
        AllocCallPreserved s s1 ∧
        s1.status = .Running ∧
        s1.trace = s.trace ∧
        s1.sp = s.sp ∧
        s1.readReg64 .x21 = x21 ∧
        s1.readReg64 .x27 = x27 ∧
        s1.readReg64 .x23 = x23 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        (P1 ⊢ optEpochSecretRegSlotAt A.repAlloc s.sp x21 x27 key ∗
          A.pool lim (M.stepEvents evs₁ st) s1 ∗
          stackAt s.sp spqrSendCalleeStack ∗
          (spqrSendResultAt A.repAlloc ret none ∗
            memRegion (s.sp + 0x190#64) 928 ∗
            chunkedStatesLocal1JumpTablePlacedAt ∗ Frame)))
    ?_ ?_
  · dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
    rw [memRegion_72_split_byte ret, hstack_drop]
    wp_pull_exists
    refine seq_vm_lscl hcl (mid := lsmpl.base 443)
      (P_mid := chunkedStatesAt A.repAlloc (s.sp + 400#64) st1 ∗
        chunkedStatesLocal1JumpTablePlacedAt ∗
        A.pool lim st s ∗ stackAt s.sp dropStackPoly64 ∗
        (spqrSendResultAt A.repAlloc ret none ∗
          optEpochSecretRegSlotAt A.repAlloc s.sp x21 x27 key ∗
          memRegion (s.sp - 123008#64) (spqrSendCalleeStack - dropStackPoly64) ∗ Frame))
      (Q := fun sc =>
        AllocCallPreserved s sc ∧
        sc.sp = s.sp ∧
        sc.trace = s.trace ∧
        sc.readReg64 .x0 = s.sp + 400#64 ∧
        sc.readReg64 .x30 = (blkPl_427).base + 3920#64 ∧
        sc.readReg64 .x21 = x21 ∧
        sc.readReg64 .x27 = x27 ∧
        sc.readReg64 .x23 = x23 ∧
        calleeSavedVRegs sc = calleeSavedVRegs s)
      ?_ ?_
    · by_vm_steps (
        wp_steps
        refine SepWP.focus_weaken (sendResultAt_none_of_byte A.repAlloc ret 15#8) (by sep_focus) ?_
        exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          ⟨by wp_norm_goal, Entails.of_eq (by sep_ac_rfl),
            by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
            by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
            by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩)
    · intro sc hpcc hrunc hcl_call hvmc
        ⟨hacpc, hspc, htrc, hx0c, hlrc, hx21c, hx27c, hx23c, hvregsc⟩
      rw [← A.pool_of_vmPreserved hvmc, ← hspc]
      have hdrop_st := subroutine_ok_withMemEq_of_withLsCodeLoaded hcl_call hdrop_states
      simp only [withMemEq, dropChunkedStatesLocal1PlacedSpec] at hdrop_st
      dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hdrop_st
      wp_call hdrop_st (⟨sc.sp + 400#64, st1⟩, st)
      rw [hspc]
      have hacp_st : AllocCallPreserved sc sf := by assumption
      have hevs_st : FreeOnlyEvs w := by assumption
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨w, hevs_st, hacpc.trans hacp_st,
          by wp_norm_goal, (by wp_norm_goal : _ = sc.trace).trans htrc,
          (by wp_norm_goal : _ = sc.sp).trans hspc,
          (by wp_norm_goal : _ = sc.readReg64 .x21).trans hx21c,
          (by wp_norm_goal : _ = sc.readReg64 .x27).trans hx27c,
          (by wp_norm_goal : _ = sc.readReg64 .x23).trans hx23c,
          (by simp only [wp_norm, arm64_norm, *] : _ = calleeSavedVRegs sc).trans hvregsc, by
            dsimp only [chunkedStatesSize]
            exact Entails.of_eq (by sep_ac_rfl)⟩
  · intro s1 P1 hpc1 _ ⟨evs₁, hevs₁, hacp₁, hrun1, htr1, hsp1, hx21_1, hx27_1, hx23_1, hvregs1, hP1⟩
    have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
    refine SepWP.weaken_pre hP1 ?_
    have hstep := step_drop_key_317ac_placed hdealloc s1 (M.stepEvents evs₁ st) x21 x27 x23 key
      (spqrSendResultAt A.repAlloc ret none ∗ memRegion (s.sp + 0x190#64) 928 ∗
        chunkedStatesLocal1JumpTablePlacedAt ∗ Frame)
      hpc1 hrun1 hx21_1 hx27_1 hx23_1 hsp1_align
    rw [hsp1] at hstep
    refine SepWP.mono hstep ?_
    intro sf Q _ _ ⟨evs₂, hevs₂, hacp₂, hrunf, htrf, hspf, hx23f, hvregsf, hQ⟩
    refine ⟨evs₁ ++ evs₂, LibsignalBinary.Heap.FreeOnlyEvs.append hevs₁ hevs₂, hacp₁.trans hacp₂,
      hrunf, htrf.trans htr1, hspf, hx23f, hvregsf.trans hvregs1, ?_⟩
    rw [M.stepEvents_append]
    exact Entails.trans hQ (Entails.of_eq (by sep_ac_rfl))

/-- `+3848 -> +4576` (`0x31764 -> 0x31a3c`):
    `Chain::from_pb` / `chain_from_version_negotiation` error cleanup.
    Loads the 24-byte error (`w1, w2, w3 : BitVec 64`) from `[s.sp + 0x1060..0x1078]`,
    writes `spqrSendResultAt A.repAlloc ret none`, drops `st1` at `s.sp + 0x190#64` via Block `443`,
    drops `key` in `(x21, x27, [s.sp + 0x1bc0])`, and reaches `+4576`. -/
theorem step_err_31764_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : DeallocOkPlaced M A lim ext)
    (hdrop_states : subroutine_ok (spqrSendPlacedProg ext)
      (lsmpl.base 443) (withLsCodeLoaded lsmpl (dropChunkedStatesLocal1PlacedSpec M A lim F)))
    (s : State) (st : M.σ) (ret x21 x27 x23 w1 w2 w3 : BitVec 64)
    (st1 : States spqrPolyApi (spqrAuthApi F))
    (key : Option EpochSecret) (Frame : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 3848#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = x21)
    (hx27 : s.readReg64 .x27 = x27)
    (hx23 : s.readReg64 .x23 = x23)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (spqrSendPlacedProg ext)
      (spqrSendPlacedEntry + 4576#64) s
      (memRegion ret 72 ∗
        ((s.sp + 0x1060#64) ↦₆₄ w1) ∗
        ((s.sp + 0x1068#64) ↦₆₄ w2) ∗
        ((s.sp + 0x1070#64) ↦₆₄ w3) ∗
        chunkedStatesAt A.repAlloc (s.sp + 0x190#64) st1 ∗
        optEpochSecretRegSlotAt A.repAlloc s.sp x21 x27 key ∗
        chunkedStatesLocal1JumpTablePlacedAt ∗
        A.pool lim st s ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          AllocCallPreserved s sf ∧
          sf.status = .Running ∧
          sf.trace = s.trace ∧
          sf.sp = s.sp ∧
          sf.readReg64 .x23 = x23 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s ∧
          (Q ⊢ spqrSendResultAt A.repAlloc ret none ∗
            memRegion (s.sp + 0x1060#64) 24 ∗
            memRegion (s.sp + 0x190#64) 928 ∗
            memRegion (s.sp + 0x1bc0#64) 16 ∗
            chunkedStatesLocal1JumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hstack_drop :
      stackAt s.sp spqrSendCalleeStack =
        memRegion (s.sp - 123008#64)
          (spqrSendCalleeStack - dropStackPoly64) ∗
          stackAt s.sp dropStackPoly64 :=
    ProofLib.stackAt_split_bottom s.sp dropStackPoly64
      (spqrSendCalleeStack - dropStackPoly64) (by decide)
  have h24 :
      ((s.sp + 4192#64) ↦₆₄ w1) ∗ ((s.sp + 4200#64) ↦₆₄ w2) ∗ ((s.sp + 4208#64) ↦₆₄ w3) ⊢
        memRegion (s.sp + 4192#64) 24 := by
    rw [ProofLib.memRegion_split' (b := s.sp + 4192#64) (n := 8) (k := 16)
          (b' := s.sp + 4200#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s.sp + 4200#64) (n := 8) (k := 8)
          (b' := s.sp + 4208#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
        (ProofLib.pointsTo64_entails_memRegion _ _))
  refine SepWP.seq
    (mid := spqrSendPlacedEntry + 3880#64)
    (Mid := fun s1 P1 =>
      ∃ evs₁ : List AllocEvent,
        FreeOnlyEvs evs₁ ∧
        AllocCallPreserved s s1 ∧
        s1.status = .Running ∧
        s1.trace = s.trace ∧
        s1.sp = s.sp ∧
        s1.readReg64 .x21 = x21 ∧
        s1.readReg64 .x27 = x27 ∧
        s1.readReg64 .x23 = x23 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        (P1 ⊢ optEpochSecretRegSlotAt A.repAlloc s.sp x21 x27 key ∗
          A.pool lim (M.stepEvents evs₁ st) s1 ∗
          stackAt s.sp spqrSendCalleeStack ∗
          (spqrSendResultAt A.repAlloc ret none ∗
            memRegion (s.sp + 0x1060#64) 24 ∗
            memRegion (s.sp + 0x190#64) 928 ∗
            chunkedStatesLocal1JumpTablePlacedAt ∗ Frame)))
    ?_ ?_
  · dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
    rw [memRegion_72_split_words3 ret, hstack_drop]
    wp_pull_exists
    refine seq_vm_lscl hcl (mid := lsmpl.base 443)
      (P_mid := chunkedStatesAt A.repAlloc (s.sp + 400#64) st1 ∗
        chunkedStatesLocal1JumpTablePlacedAt ∗
        A.pool lim st s ∗ stackAt s.sp dropStackPoly64 ∗
        (spqrSendResultAt A.repAlloc ret none ∗
          memRegion (s.sp + 4192#64) 24 ∗
          optEpochSecretRegSlotAt A.repAlloc s.sp x21 x27 key ∗
          memRegion (s.sp - 123008#64) (spqrSendCalleeStack - dropStackPoly64) ∗ Frame))
      (Q := fun sc =>
        AllocCallPreserved s sc ∧
        sc.sp = s.sp ∧
        sc.trace = s.trace ∧
        sc.readReg64 .x0 = s.sp + 400#64 ∧
        sc.readReg64 .x30 = (blkPl_427).base + 3880#64 ∧
        sc.readReg64 .x21 = x21 ∧
        sc.readReg64 .x27 = x27 ∧
        sc.readReg64 .x23 = x23 ∧
        calleeSavedVRegs sc = calleeSavedVRegs s)
      ?_ ?_
    · by_vm_steps (
        wp_steps
        refine SepWP.focus_weaken (sendResultAt_none_of_words3 A.repAlloc ret w1 w2 w3) (by sep_focus) ?_
        refine SepWP.focus_weaken h24 (by sep_focus) ?_
        exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          ⟨by wp_norm_goal, Entails.of_eq (by sep_ac_rfl),
            by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
            by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
            by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩)
    · intro sc hpcc hrunc hcl_call hvmc
        ⟨hacpc, hspc, htrc, hx0c, hlrc, hx21c, hx27c, hx23c, hvregsc⟩
      rw [← A.pool_of_vmPreserved hvmc, ← hspc]
      have hdrop_st := subroutine_ok_withMemEq_of_withLsCodeLoaded hcl_call hdrop_states
      simp only [withMemEq, dropChunkedStatesLocal1PlacedSpec] at hdrop_st
      dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hdrop_st
      wp_call hdrop_st (⟨sc.sp + 400#64, st1⟩, st)
      rw [hspc]
      have hacp_st : AllocCallPreserved sc sf := by assumption
      have hevs_st : FreeOnlyEvs w := by assumption
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨w, hevs_st, hacpc.trans hacp_st,
          by wp_norm_goal, (by wp_norm_goal : _ = sc.trace).trans htrc,
          (by wp_norm_goal : _ = sc.sp).trans hspc,
          (by wp_norm_goal : _ = sc.readReg64 .x21).trans hx21c,
          (by wp_norm_goal : _ = sc.readReg64 .x27).trans hx27c,
          (by wp_norm_goal : _ = sc.readReg64 .x23).trans hx23c,
          (by simp only [wp_norm, arm64_norm, *] : _ = calleeSavedVRegs sc).trans hvregsc, by
            dsimp only [chunkedStatesSize]
            exact Entails.of_eq (by sep_ac_rfl)⟩
  · intro s1 P1 hpc1 _ ⟨evs₁, hevs₁, hacp₁, hrun1, htr1, hsp1, hx21_1, hx27_1, hx23_1, hvregs1, hP1⟩
    have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
    refine SepWP.weaken_pre hP1 ?_
    have hstep := step_drop_key_31784_placed hdealloc s1 (M.stepEvents evs₁ st) x21 x27 x23 key
      (spqrSendResultAt A.repAlloc ret none ∗ memRegion (s.sp + 0x1060#64) 24 ∗
        memRegion (s.sp + 0x190#64) 928 ∗
        chunkedStatesLocal1JumpTablePlacedAt ∗ Frame)
      hpc1 hrun1 hx21_1 hx27_1 hx23_1 hsp1_align
    rw [hsp1] at hstep
    refine SepWP.mono hstep ?_
    intro sf Q _ _ ⟨evs₂, hevs₂, hacp₂, hrunf, htrf, hspf, hx23f, hvregsf, hQ⟩
    refine ⟨evs₁ ++ evs₂, LibsignalBinary.Heap.FreeOnlyEvs.append hevs₁ hevs₂, hacp₁.trans hacp₂,
      hrunf, htrf.trans htr1, hspf, hx23f, hvregsf.trans hvregs1, ?_⟩
    rw [M.stepEvents_append]
    exact Entails.trans hQ (Entails.of_eq (by sep_ac_rfl))

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesChainPlacedBudget
