/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.ProofPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.StepsPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternal
import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.Proof
import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeStep
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Step Lemmas for `spqr::initial_state`

`VmPreserved` basic-block steppers, `InitialStateEnv` budget decomposition lemmas, and panic/OOM-free
`.v1` body composition for `spqr::initial_state` (Block `327`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Top.InitialState.StepsPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkPC_270 blkPl_270 libsignalSessionCode lsLogFilterAddr
   lsLogFilterSym lsMemcpySym ls_subroutine_ok_cl_of_block lsmpl lsρ withLsCl withLsCodeLoaded)
open CryptoVerification.RustHeap
  (RustAlloc allocHookStack vecHeader vecU8 vecU8At vecU8Buf)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalSpqrV1
  (Bytes Direction Params PqRatchetState States Version emptyState spqrAuthApi spqrPolyApi)
open CryptoVerification.SpqrV1.Alloc (spqrRustAllocSym spqrRustNoAllocShimSym)
open CryptoVerification.SpqrV1.Auth (authNewStackX)
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts
  (LsCallInv ls_subroutine_ok_callInv_of_block subroutine_ok_withLsCallInv_of_withLsCodeLoaded
   withLsCallInv)
open CryptoVerification.SpqrV1.Drop
  (DropProtoPqRatchetStateGhost dropStack96 optProtoInnerStateJumpTablePlacedAt
   optProtoInnerStateSize protoPqRatchetStateAt protoPqRatchetStateSize)
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (PqRatchetStateEncodeToVecGhost blkPC_426 blkPl_426 encodeToVecStackX pqRatchetStatePBAt
   pqRatchetStatePBEncodedLen pqRatchetStatePBEncodedLen_eq_proto)
open CryptoVerification.SpqrV1.Top.InitInner
  (InitInnerGhost initHdrDecoder initInnerFrame initInnerResultAt initInnerStack initInnerStackX
   initV1State statesIntoPbJumpTablePlacedAt vecU8_nil_of_cells)
open CryptoVerification.SpqrV1.Top.InitialState
  (InitialStateGhost csel_maxJump_eq csel_maxOoo_eq h61s_initialStateSavedCells
   h61s_stackAt_initialState_split h61s_stack_restore_initialState initialStateCalleeStack
   initialStateFrame initialStatePB initialStatePlacedEntry initialStatePlacedProg
   initialStateResultAt initialStateStack initialStateValue memRegion_pqState_split
   memRegion_ret_32_split paramsAt readReg32_of_eq stackAt_initInner_split_allocHook
   stackAt_initInner_split_dropStack96 stackAt_initInner_split_encodeToVec testBit63_ofNat_of_lt
   vecU8Buf_nil vecU8Buf_nonempty)
open CryptoVerification.SpqrV1.Top.Placed (blkPC_324 blkPC_327 blkPl_324 blkPl_327)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
   RustCliAllocBudget RustLayoutOk VmPreserved fitsEvents_append rustAllocEvents
   rustCliAllocBudgetSpec rustCliAllocNoOomSpec subroutine_ok_allocNoOom_of_budget)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget (dropProtoPqRatchetStatePlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget (withLsRoLoaded)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsBudget
  (PqRatchetStateEncodeToVecEnv PqRatchetStateEncodeToVecPlacedOkExt pqRatchetStateEncodeToVecSpecOf
   pqRatchetStateEncodeToVecSpecOfEnv pqRatchetStateEncodeToVecSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
  (InitInnerEnv SpqrBoundedEvs initInnerPlacedSpecX initInnerPlacedSpecXOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.ProofPlacedBudgetAux
  (InitInnerBudgetPanic cloneEvs cloneEvs_of_length_zero cloneEvs_of_pos initInner_seq_sepWP_lsInv
   le_mallocngMaxAllocSize_of_fitsEnv_spqrBoundedEvs le_two_pow_48_of_fitsEnv_spqrBoundedEvs
   rustAllocEvents_one_of_pos sepWPp_call_total_keepLsInv spqrBoundedEvs_cloneEvs)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget
  (InitialStateEnv initialStatePlacedRoSpec initialStatePlacedRoSpecOfEnv initialStatePlacedSpec
   initialStatePlacedSpecOfEnv)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (framelessMemcpyBudgetSpec noAllocShimBudgetSpec)
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize)

private theorem bv_sub_add_lit (x a b : BitVec 64) : x - a + b = x - (a - b) := by
  bv_omega

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr Program.fnOff Obj.lookup
attribute [local wp_norm] csel_maxJump_eq csel_maxOoo_eq
attribute [local arm64_norm] bv_sub_add_lit

/-! ## 0. Private `VmPreserved` Stepper Helpers -/

private theorem sepWP_rebase_strengthen_vmPreserved {P : Program} {b : BitVec 64}
    {Hk : String → Option (State → State)} {target_pc : BitVec 64} {s : State}
    {Pre Q_mid Q_out : SepProp} {R : State → Prop}
    (hent : Q_mid ⊢ Q_out)
    (hwp : SepWP (P.rebase b Hk) target_pc s Pre
      (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ Q_mid) ∧ R sm)) :
    SepWP (P.rebase b Hk) target_pc s Pre
      (fun sm Pm => (Pm ⊢ Q_out) ∧ VmPreserved s sm ∧ R sm) :=
  SepWP.mono hwp fun _ _ _ _ ⟨hvm, h1, h2⟩ => ⟨Entails.trans h1 hent, hvm, h2⟩

private theorem sepWP_rebase_strengthen_vmPreserved_from {P : Program} {b : BitVec 64}
    {Hk : String → Option (State → State)} {target_pc : BitVec 64} {s0 s : State}
    {Pre Q_mid Q_out : SepProp} {R : State → Prop}
    (hvm0 : VmPreserved s0 s)
    (hent : Q_mid ⊢ Q_out)
    (hwp : SepWP (P.rebase b Hk) target_pc s Pre
      (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ Q_mid) ∧ R sm)) :
    SepWP (P.rebase b Hk) target_pc s Pre
      (fun sm Pm => (Pm ⊢ Q_out) ∧ VmPreserved s0 sm ∧ R sm) :=
  SepWP.mono hwp fun _ _ _ _ ⟨hvm, h1, h2⟩ => ⟨Entails.trans h1 hent, hvm0.trans hvm, h2⟩

private theorem seq_sepWP_vmPreserved {prog : Program} {mid target : BitVec 64} {s0 s : State}
    {Pre P_mid : SepProp} {Q : State → Prop} {Post : State → SepProp → Prop}
    (hvm0 : VmPreserved s0 s)
    (h1 : SepWP prog mid s Pre (fun sm Pm => (Pm ⊢ P_mid) ∧ VmPreserved s sm ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s0 sm → Q sm →
      SepWP prog target sm P_mid Post) :
    SepWP prog target s Pre Post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨hent, hvm1, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun (hvm0.trans hvm1) hQ)

private theorem align_pre_tp {prog : Program} {target_pc : BitVec 64} {s s0 : State}
    {P Q : SepProp} {R : State → Prop}
    (heq : P = Q)
    (h : SepWP prog target_pc s Q
      (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ (Pm ⊢ Q) ∧ R sm)) :
    SepWP prog target_pc s P
      (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ (Pm ⊢ Q) ∧ R sm) :=
  heq ▸ h

/-! ## 1. V0 Path (`+0 -> ret`), Prologue (`+0 -> +232`), and Epilogue (`+396 -> ret`) on `Block 327` -/

private theorem h61s_savedCells_entails_memRegion_placed (s0 : State) :
    h61s_initialStateSavedCells s0 ⊢ memRegion (s0.sp - 96#64) 96 := by
  unfold h61s_initialStateSavedCells
  rw [ProofLib.memRegion_cells (s0.sp - 96#64) 12 (by decide)]
  cells_unfold
  refine Entails.sepExists_right (s0.readReg64 .x29)
    (Entails.sepExists_right (s0.readReg64 .x30)
      (Entails.sepExists_right (s0.readReg64 .x28)
        (Entails.sepExists_right (s0.readReg64 .x27)
          (Entails.sepExists_right (s0.readReg64 .x26)
            (Entails.sepExists_right (s0.readReg64 .x25)
              (Entails.sepExists_right (s0.readReg64 .x24)
                (Entails.sepExists_right (s0.readReg64 .x23)
                  (Entails.sepExists_right (s0.readReg64 .x22)
                    (Entails.sepExists_right (s0.readReg64 .x21)
                      (Entails.sepExists_right (s0.readReg64 .x20)
                        (Entails.sepExists_right (s0.readReg64 .x19) ?_)))))))))))
  exact Entails.of_eq (by simp only [arm64_norm])

private theorem stackAt_initialState_placed_split (sp : BitVec 64) :
    stackAt sp initialStateStack =
      stackAt (sp - 496#64) initialStateCalleeStack ∗
      memRegion (sp - 496#64) 400 ∗
      cells (sp - 96#64) 12 := by
  unfold stackAt initialStateStack initialStateFrame
  rw [ProofLib.memRegion_split'
        (b := sp - BitVec.ofNat 64 (0x1f0 + initialStateCalleeStack))
        (n := initialStateCalleeStack) (k := 496)
        (b' := sp - 496#64) (by decide) (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 496#64) (n := 400) (k := 96)
        (b' := sp - 96#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_cells (sp - 96#64) 12 (by decide)]
  have hsub : (sp - 496#64) - BitVec.ofNat 64 initialStateCalleeStack =
      sp - BitVec.ofNat 64 (0x1f0 + initialStateCalleeStack) := by
    dsimp only [initialStateCalleeStack, initInnerStack, initInnerFrame, authNewStackX,
      encodeToVecStackX, dropStack96, allocHookStack]
    bv_omega
  rw [hsub]

private theorem stack_restore_initialState_placed (s0 : State) :
    stackAt (s0.sp - 496#64) initialStateCalleeStack ∗
    memRegion (s0.sp - 496#64) 400 ∗
    h61s_initialStateSavedCells s0 ⊢
    stackAt s0.sp initialStateStack := by
  rw [stackAt_initialState_placed_split s0.sp,
      ← ProofLib.memRegion_cells (s0.sp - 96#64) 12 (by decide)]
  exact sepConj_mono_right
    (sepConj_mono_right (h61s_savedCells_entails_memRegion_placed s0))

private theorem initial_state_prologue_0_to_32_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 : State) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = initialStatePlacedEntry)
    (hrun : s0.status = .Running) :
    SepWP (initialStatePlacedProg ext) (initialStatePlacedEntry + 32#64) s0
      (cells (s0.sp - 96#64) 12 ∗ Rest)
      (fun s1 P1 =>
        (P1 ⊢ h61s_initialStateSavedCells s0 ∗ Rest) ∧
        VmPreserved s0 s1 ∧
        s1.sp = s0.sp - 496#64 ∧
        s1.readReg64 .x29 = s0.sp - 96#64 ∧
        s1.readReg64 .x0 = s0.readReg64 .x0 ∧
        s1.readReg64 .x8 = s0.readReg64 .x8 ∧
        s1.trace = s0.trace ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s0) := by
  have hsp496_align : ((s0.sp - 496#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 496#64 hsp0_align (by decide)
  dsimp only [initialStatePlacedProg, initialStatePlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  refine sepWP_rebase_strengthen_vmPreserved (Entails.refl _) ?_
  by_vm_steps (
    cells_unfold
    wp_pull_exists
    dsimp only [h61s_initialStateSavedCells]
    wp_steps
    refine align_pre_tp (by sep_ac_rfl) ?_
    wp_done
  )

private theorem initial_state_adrp_32_to_36_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s1 : State) (P : SepProp)
    (hpc : s1.pc = initialStatePlacedEntry + 32#64)
    (hrun : s1.status = .Running) :
    SepWP (initialStatePlacedProg ext) (initialStatePlacedEntry + 36#64) s1 P
      (fun s2 P2 =>
        (P2 ⊢ P) ∧
        VmPreserved s1 s2 ∧
        s2.sp = s1.sp ∧
        s2.readReg64 .x9 = pageOf lsLogFilterAddr ∧
        s2.readReg64 .x29 = s1.readReg64 .x29 ∧
        s2.readReg64 .x0 = s1.readReg64 .x0 ∧
        s2.readReg64 .x8 = s1.readReg64 .x8 ∧
        s2.trace = s1.trace ∧
        calleeSavedVRegs s2 = calleeSavedVRegs s1) := by
  dsimp only [initialStatePlacedProg, initialStatePlacedEntry, lsLogFilterAddr, lsρ,
    lsLogFilterSym, BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_steps
  wp_done

private theorem initial_state_prologue_0_to_36_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 : State) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = initialStatePlacedEntry)
    (hrun : s0.status = .Running) :
    SepWP (initialStatePlacedProg ext) (initialStatePlacedEntry + 36#64) s0
      (cells (s0.sp - 96#64) 12 ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢ h61s_initialStateSavedCells s0 ∗ Rest) ∧
        VmPreserved s0 s2 ∧
        s2.sp = s0.sp - 496#64 ∧
        s2.readReg64 .x9 = pageOf lsLogFilterAddr ∧
        s2.readReg64 .x29 = s0.sp - 96#64 ∧
        s2.readReg64 .x0 = s0.readReg64 .x0 ∧
        s2.readReg64 .x8 = s0.readReg64 .x8 ∧
        s2.trace = s0.trace ∧
        calleeSavedVRegs s2 = calleeSavedVRegs s0) := by
  refine seq_sepWP_vmPreserved (VmPreserved.refl s0)
    (initial_state_prologue_0_to_32_placed s0 Rest hsp0_align hpc hrun) ?_
  intro s1 hpc1 hrun1 hvm01 ⟨hsp1, hx29_1, hx0_1, hx8_1, htr1, hvregs1⟩
  refine SepWP.mono
    (initial_state_adrp_32_to_36_placed s1 (h61s_initialStateSavedCells s0 ∗ Rest) hpc1 hrun1) ?_
  intro s2 _P2 _ _ ⟨hP2, hvm12, hsp2, hx9_2, hx29_2, hx0_2, hx8_2, htr2, hvregs2⟩
  exact ⟨hP2, hvm01.trans hvm12, hsp2.trans hsp1, hx9_2, hx29_2.trans hx29_1,
    hx0_2.trans hx0_1, hx8_2.trans hx8_1, htr2.trans htr1, hvregs2.trans hvregs1⟩

private theorem initialStateResultAt_v0_of_cells_placed (A : RustAlloc) (F : ShaCompress)
    (ret : BitVec 64) (p : Params) (hv : p.version = .v0) :
    (ret ↦₆₄ 0#64) ∗ ((ret + 8#64) ↦₆₄ 0#64) ∗
    ((ret + 16#64) ↦₆₄ 1#64) ∗ ((ret + 24#64) ↦₆₄ 0#64) ⊢
    initialStateResultAt A ret (initialStateValue F p) := by
  unfold initialStateResultAt initialStateValue
  rw [hv]
  dsimp [emptyState]
  have h16 : (ret + 8#64) + 8#64 = ret + 16#64 := by bv_omega
  have h24 : (ret + 8#64) + 16#64 = ret + 24#64 := by bv_omega
  have hvec := vecU8_nil_of_cells A (ret + 8#64)
  rw [h16, h24] at hvec
  exact sepConj_mono_right hvec

/-- Full `.v0` execution (`+0 -> ret`) on `Block 327` preserving `VmPreserved s0 sf`. -/
theorem initialState_v0_step_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 : State) (x : InitialStateGhost) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = initialStatePlacedEntry)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = x.pA)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hv : x.p.version = .v0) :
    SepWP (initialStatePlacedProg ext) (s0.readReg64 .x30) s0
      (paramsAt x.pA x.akPtr x.p ∗
       memRegion x.ret 32 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp initialStateStack ∗
       Rest)
      (fun sf Pf =>
        (Pf ⊢
          paramsAt x.pA x.akPtr x.p ∗
          initialStateResultAt A x.ret (initialStateValue F x.p) ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗
          stackAt s0.sp initialStateStack ∗
          Rest) ∧
        VmPreserved s0 sf ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hrestore :
      paramsAt x.pA x.akPtr x.p ∗
      ((x.ret ↦₆₄ 0#64) ∗ ((x.ret + 8#64) ↦₆₄ 0#64) ∗
       ((x.ret + 16#64) ↦₆₄ 1#64) ∗ ((x.ret + 24#64) ↦₆₄ 0#64)) ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      (stackAt (s0.sp - 496#64) initialStateCalleeStack ∗
       memRegion (s0.sp - 496#64) 400 ∗
       h61s_initialStateSavedCells s0) ∗
      Rest ⊢
      paramsAt x.pA x.akPtr x.p ∗
      initialStateResultAt A x.ret (initialStateValue F x.p) ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      stackAt s0.sp initialStateStack ∗
      Rest :=
    sepConj_mono_right (sepConj_mono (initialStateResultAt_v0_of_cells_placed A F x.ret x.p hv)
      (sepConj_mono_right (sepConj_mono_left (stack_restore_initialState_placed s0))))
  have hsp496_align : ((s0.sp - 496#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 496#64 hsp0_align (by decide)
  have hv_i32 : x.p.version.toI32 = 0#32 := by rw [hv]; rfl
  have hpre_split :
      paramsAt x.pA x.akPtr x.p ∗ memRegion x.ret 32 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
      stackAt s0.sp initialStateStack ∗ Rest ⊢
      cells (s0.sp - 96#64) 12 ∗
      (paramsAt x.pA x.akPtr x.p ∗ memRegion x.ret 32 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt (s0.sp - 496#64) initialStateCalleeStack ∗ memRegion (s0.sp - 496#64) 400 ∗ Rest) := by
    rw [stackAt_initialState_placed_split s0.sp]
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWP.weaken_pre hpre_split ?_
  refine seq_sepWP_vmPreserved (VmPreserved.refl s0)
    (initial_state_prologue_0_to_36_placed s0 _ hsp0_align hpc hrun) ?_
  intro s2 hpc2 hrun2 hvm02 ⟨hsp2, hx9_2, hx29_2, hx0_2, hx8_2, htr2, hvregs2⟩
  have hx0_s2 : s2.readReg64 .x0 = x.pA := hx0_2.trans hx0
  have hx8_s2 : s2.readReg64 .x8 = x.ret := hx8_2.trans hx8
  dsimp only [initialStatePlacedProg, initialStatePlacedEntry, lsLogFilterAddr, lsρ,
    lsLogFilterSym, Reg.x0, Reg.x8, Reg.x9, Reg.x29, BitVec.ofNat_eq_ofNat]
    at hpc2 hx9_2 hx29_2 hx0_s2 hx8_s2 ⊢
  refine sepWP_rebase_strengthen_vmPreserved_from hvm02 hrestore ?_
  by_vm_steps (
    dsimp only [lsLogFilterAddr, lsρ, lsLogFilterSym, h61s_initialStateSavedCells,
      BitVec.ofNat_eq_ofNat]
    rw [ProofLib.memRegion_cells x.ret 4 (by decide)]
    unfold paramsAt
    rw [hv_i32]
    simp only [sepConj_assoc]
    cells_unfold
    dsimp only [ProofLib.cells]
    simp only [sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm]
    wp_pull_exists
    wp_steps
    refine align_pre_tp (by sep_ac_rfl) ?_
    wp_done
  )

theorem initial_state_prologue_v1_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    (s0 : State) (x : InitialStateGhost) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = initialStatePlacedEntry)
    (hrun : s0.status = .Running) (hx0 : s0.readReg64 .x0 = x.pA) (hx8 : s0.readReg64 .x8 = x.ret)
    (hv : x.p.version = .v1) (hlen : x.p.authKey.length < 2 ^ 32) :
    SepWP (initialStatePlacedProg ext)
      (initialStatePlacedEntry + 232#64) s0
      (cells (s0.sp - 96#64) 12 ∗ paramsAt x.pA x.akPtr x.p ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ Rest)
      (fun s1 P1 =>
        (P1 ⊢ h61s_initialStateSavedCells s0 ∗ paramsAt x.pA x.akPtr x.p ∗
              (lsLogFilterAddr ↦₆₄ 0#64) ∗ Rest) ∧
        VmPreserved s0 s1 ∧
        s1.sp = s0.sp - 496#64 ∧ s1.readReg64 .x29 = s0.sp - 96#64 ∧
        s1.readReg64 .x19 = x.ret ∧ s1.readReg64 .x20 = x.pA ∧
        s1.readReg64 .x21 = BitVec.ofNat 64 x.p.authKey.length ∧
        s1.readReg64 .x22 = x.akPtr ∧ s1.readReg32 .x25 = 1#32 ∧ s1.trace = s0.trace ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s0) := by
  have hsp496_align : ((s0.sp - 496#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 496#64 hsp0_align (by decide)
  have htbz := testBit63_ofNat_of_lt hlen
  refine seq_sepWP_vmPreserved (VmPreserved.refl s0)
    (initial_state_prologue_0_to_36_placed s0
      (paramsAt x.pA x.akPtr x.p ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ Rest) hsp0_align hpc hrun) ?_
  intro s2 hpc2 hrun2 hvm02 ⟨hsp2, hx9_2, hx29_2, hx0_2, hx8_2, htr2, hvregs2⟩
  have hx0_s2 : s2.readReg64 .x0 = x.pA := hx0_2.trans hx0
  have hx8_s2 : s2.readReg64 .x8 = x.ret := hx8_2.trans hx8
  dsimp only [initialStatePlacedProg, initialStatePlacedEntry, paramsAt, lsLogFilterAddr, lsρ,
    lsLogFilterSym, State.readReg32, Reg.x0, Reg.x8, Reg.x9, Reg.x25, Reg.x29,
    BitVec.ofNat_eq_ofNat]
    at hpc2 hx9_2 hx29_2 hx0_s2 hx8_s2 ⊢
  simp only [hv, Version.toI32]
  refine sepWP_rebase_strengthen_vmPreserved_from hvm02 (Entails.refl _) ?_
  by_vm_steps (
    dsimp only [h61s_initialStateSavedCells]
    wp_steps
    refine align_pre_tp (by sep_ac_rfl) ?_
    wp_done
  )

theorem initial_state_epilogue_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    (s0 s : State) (Rest : SepProp) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = initialStatePlacedEntry + 396#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 496#64) (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (initialStatePlacedProg ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 496#64) initInnerStack ∗ memRegion (s0.sp - 496#64) 40 ∗
       memRegion (s0.sp - 456#64) 352 ∗ memRegion (s0.sp - 104#64) 8 ∗
       h61s_initialStateSavedCells s0 ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ stackAt s0.sp initialStateStack ∗ Rest) ∧
        VmPreserved s sf ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hrestore :
      (stackAt (s0.sp - 496#64) initInnerStack ∗ memRegion (s0.sp - 496#64) 40 ∗
       memRegion (s0.sp - 456#64) 352 ∗ memRegion (s0.sp - 104#64) 8 ∗
       h61s_initialStateSavedCells s0) ∗ Rest ⊢ stackAt s0.sp initialStateStack ∗ Rest :=
    sepConj_mono_left (h61s_stack_restore_initialState s0)
  have hsp496_align : ((s0.sp - 496#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 496#64 hsp0_align (by decide)
  dsimp only [initialStatePlacedProg, initialStatePlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  refine sepWP_rebase_strengthen_vmPreserved hrestore ?_
  by_vm_steps (
    dsimp only [h61s_initialStateSavedCells, BitVec.ofNat_eq_ofNat]
    wp_steps
    refine align_pre_tp (by sep_ac_rfl) ?_
    wp_done
  )

/-! ## 2. Budget Envelope & `FitsEnv` Decomposition Lemmas -/

private theorem rawV1State_initV1State_le (F : ShaCompress)
    (d : Direction) (authKey : Bytes) :
    CryptoVerification.SpqrV1.Top.StateSize.rawV1State (initV1State F d authKey).into_pb ≤ 424 := by
  have hauth := CryptoVerification.SpqrV1.Top.StateSize.Authenticator.new_rawAuth_le F authKey 1#64
  cases d with
  | a2b =>
    dsimp only [initV1State, States.into_pb,
      CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.KeysUnsampled.into_pb,
      CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.KeysUnsampled.into_pb, spqrAuthApi,
      CryptoVerification.SpqrV1.Top.StateSize.rawV1State,
      CryptoVerification.SpqrV1.Top.StateSize.optRaw,
      CryptoVerification.SpqrV1.Top.StateSize.rawInnerState,
      CryptoVerification.SpqrV1.Top.StateSize.rawChKeysUnsampled,
      CryptoVerification.SpqrV1.Top.StateSize.rawUcKeysUnsampled]
    omega
  | b2a =>
    have hdec : CryptoVerification.SpqrV1.Top.StateSize.rawPolyDec
        (spqrPolyApi.decoder_into_pb initHdrDecoder) = 352 := rfl
    dsimp only [initV1State, States.into_pb,
      CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.NoHeaderReceived.into_pb,
      CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.NoHeaderReceived.into_pb, spqrAuthApi,
      CryptoVerification.SpqrV1.Top.StateSize.rawV1State,
      CryptoVerification.SpqrV1.Top.StateSize.optRaw,
      CryptoVerification.SpqrV1.Top.StateSize.rawInnerState,
      CryptoVerification.SpqrV1.Top.StateSize.rawChNoHeaderReceived,
      CryptoVerification.SpqrV1.Top.StateSize.rawUcNoHeaderReceived]
    omega

/-- Linear upper bound on `pqRatchetStatePBEncodedLen (initialStatePB F p)`. -/
theorem pqRatchetStatePBEncodedLen_initialStatePB_le (F : ShaCompress) (p : Params) :
    pqRatchetStatePBEncodedLen (initialStatePB F p) ≤ p.authKey.length + 1176 := by
  rw [← pqRatchetStatePBEncodedLen_eq_proto]
  have h1 : (PqRatchetState.encodeRaw (initialStatePB F p)).length ≤
      CryptoVerification.SpqrV1.Top.StateSize.rawPqState (initialStatePB F p) + 752 :=
    CryptoVerification.SpqrV1.Top.StateSize.encodeState_length_le_rawPqState (initialStatePB F p)
  have hraw : CryptoVerification.SpqrV1.Top.StateSize.rawPqState (initialStatePB F p) =
      p.authKey.length + 0 +
        CryptoVerification.SpqrV1.Top.StateSize.rawV1State
          (initV1State F p.direction p.authKey).into_pb := rfl
  have h2 := rawV1State_initV1State_le F p.direction p.authKey
  omega

theorem spqrBoundedEvs_encodeToVec {st : PqRatchetState} {evs : List AllocEvent}
    (hmax : pqRatchetStatePBEncodedLen st ≤ MallocngMaxAllocSize)
    (henv : PqRatchetStateEncodeToVecEnv st evs) :
    SpqrBoundedEvs 1 (pqRatchetStatePBEncodedLen st) evs := by
  rcases henv with ⟨_, rfl⟩ | ⟨hpos, rfl⟩
  · exact SpqrBoundedEvs.nil 1 _
  · rw [rustAllocEvents_one_of_pos hpos]
    refine ⟨by simp [LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.nonFreeCount],
      fun ev hev => ?_⟩
    simp only [List.mem_singleton] at hev
    subst hev
    exact ⟨hmax, Nat.le_refl _, (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

private theorem fitsEnv_spqrBoundedEvs_of_initialStateEnv_v1
    {M : AllocCostModel} {lim : BudgetLimits} {F : ShaCompress} {st0 : M.σ}
    {x : InitialStateGhost} (hv : x.p.version = .v1)
    (hfit : FitsEnv M lim st0 (InitialStateEnv F x)) :
    FitsEnv M lim st0 (SpqrBoundedEvs 128 (4 * x.p.authKey.length + 4096)) :=
  fun evs hevs => hfit evs (by simpa only [InitialStateEnv, hv] using hevs)

theorem fitsEvents_clone_of_initialStateEnv
    {M : AllocCostModel} {lim : BudgetLimits} {F : ShaCompress} {st0 : M.σ}
    {x : InitialStateGhost}
    (hpos : 0 < x.p.authKey.length) (hv : x.p.version = .v1)
    (hfit : FitsEnv M lim st0 (InitialStateEnv F x)) :
    RustLayoutOk x.p.authKey.length 1 ∧
      FitsEvents M lim st0 (rustAllocEvents x.p.authKey.length 1) := by
  have hfit' := fitsEnv_spqrBoundedEvs_of_initialStateEnv_v1 hv hfit
  have h48 := le_two_pow_48_of_fitsEnv_spqrBoundedEvs (n := x.p.authKey.length)
    (by decide) (by omega) hfit'
  have hmax := le_mallocngMaxAllocSize_of_fitsEnv_spqrBoundedEvs (n := x.p.authKey.length)
    (by decide) (by omega) hfit'
  have hlay : RustLayoutOk x.p.authKey.length 1 :=
    ⟨⟨hpos, ⟨0, rfl⟩, by omega⟩, by decide⟩
  have hcl := spqrBoundedEvs_cloneEvs (authKey := x.p.authKey) hmax
  rw [cloneEvs_of_pos hpos] at hcl
  exact ⟨hlay, hfit' _ (SpqrBoundedEvs.mono (by decide) (by omega) hcl)⟩

theorem fitsEnv_initInner_of_initialStateEnv
    {M : AllocCostModel} {lim : BudgetLimits} {F : ShaCompress} {st0 : M.σ}
    {x : InitialStateGhost} (out : BitVec 64)
    (hv : x.p.version = .v1)
    (hfit : FitsEnv M lim st0 (InitialStateEnv F x)) :
    FitsEnv M lim (M.stepEvents (cloneEvs x.p.authKey) st0)
      (InitInnerEnv F ⟨out, .v1, x.p.direction, x.akPtr, x.p.authKey⟩) := by
  have hfit' := fitsEnv_spqrBoundedEvs_of_initialStateEnv_v1 hv hfit
  have hmax := le_mallocngMaxAllocSize_of_fitsEnv_spqrBoundedEvs (n := x.p.authKey.length)
    (by decide) (by omega) hfit'
  have h1 := spqrBoundedEvs_cloneEvs (authKey := x.p.authKey) hmax
  intro evs₂ h2
  dsimp only [InitInnerEnv] at h2
  have h12 : SpqrBoundedEvs 128 (4 * x.p.authKey.length + 4096) (cloneEvs x.p.authKey ++ evs₂) :=
    SpqrBoundedEvs.mono (by decide) (by omega) (SpqrBoundedEvs.append h1 h2)
  exact ((fitsEvents_append M lim (cloneEvs x.p.authKey) evs₂ st0).mp (hfit' _ h12)).2

theorem fitsEnv_encodeToVec_of_initialStateEnv
    {M : AllocCostModel} {lim : BudgetLimits} {F : ShaCompress} {st0 : M.σ}
    {x : InitialStateGhost} {out : BitVec 64} {evs₂ : List AllocEvent}
    (hv : x.p.version = .v1)
    (hfit : FitsEnv M lim st0 (InitialStateEnv F x))
    (h2 : InitInnerEnv F ⟨out, .v1, x.p.direction, x.akPtr, x.p.authKey⟩ evs₂) :
    FitsEnv M lim (M.stepEvents evs₂ (M.stepEvents (cloneEvs x.p.authKey) st0))
      (PqRatchetStateEncodeToVecEnv (initialStatePB F x.p)) := by
  have hfit' := fitsEnv_spqrBoundedEvs_of_initialStateEnv_v1 hv hfit
  have hpb_le := pqRatchetStatePBEncodedLen_initialStatePB_le F x.p
  have hmax1 := le_mallocngMaxAllocSize_of_fitsEnv_spqrBoundedEvs (n := x.p.authKey.length)
    (by decide) (by omega) hfit'
  have hmax3 := le_mallocngMaxAllocSize_of_fitsEnv_spqrBoundedEvs
    (n := pqRatchetStatePBEncodedLen (initialStatePB F x.p))
    (by decide) (by omega) hfit'
  dsimp only [InitInnerEnv] at h2
  have h12 : SpqrBoundedEvs 97 (2 * x.p.authKey.length + 2048) (cloneEvs x.p.authKey ++ evs₂) :=
    SpqrBoundedEvs.mono (by decide) (by omega)
      (SpqrBoundedEvs.append (spqrBoundedEvs_cloneEvs hmax1) h2)
  intro evs₃ h3
  have h3b := spqrBoundedEvs_encodeToVec hmax3 h3
  have h123 : SpqrBoundedEvs 128 (4 * x.p.authKey.length + 4096)
      ((cloneEvs x.p.authKey ++ evs₂) ++ evs₃) :=
    SpqrBoundedEvs.mono (by decide) (by omega) (SpqrBoundedEvs.append h12 h3b)
  have hf := (fitsEvents_append M lim (cloneEvs x.p.authKey ++ evs₂) evs₃ st0).mp (hfit' _ h123)
  rw [M.stepEvents_append] at hf
  exact hf.2

theorem initialStateEnv_v1_of_stages
    {M : AllocCostModel} {lim : BudgetLimits} {F : ShaCompress} {st0 : M.σ}
    {x : InitialStateGhost} {out : BitVec 64}
    {evs₂ evs₃ evs₄ : List AllocEvent}
    (hv : x.p.version = .v1)
    (hfit : FitsEnv M lim st0 (InitialStateEnv F x))
    (h2 : InitInnerEnv F ⟨out, .v1, x.p.direction, x.akPtr, x.p.authKey⟩ evs₂)
    (h3 : PqRatchetStateEncodeToVecEnv (initialStatePB F x.p) evs₃)
    (h4 : FreeOnlyEvs evs₄) :
    InitialStateEnv F x (((cloneEvs x.p.authKey ++ evs₂) ++ evs₃) ++ evs₄) := by
  have hfit' := fitsEnv_spqrBoundedEvs_of_initialStateEnv_v1 hv hfit
  have hpb_le := pqRatchetStatePBEncodedLen_initialStatePB_le F x.p
  have hmax1 := le_mallocngMaxAllocSize_of_fitsEnv_spqrBoundedEvs (n := x.p.authKey.length)
    (by decide) (by omega) hfit'
  have hmax3 := le_mallocngMaxAllocSize_of_fitsEnv_spqrBoundedEvs
    (n := pqRatchetStatePBEncodedLen (initialStatePB F x.p))
    (by decide) (by omega) hfit'
  dsimp only [InitInnerEnv] at h2
  have h12 : SpqrBoundedEvs 97 (2 * x.p.authKey.length + 2048) (cloneEvs x.p.authKey ++ evs₂) :=
    SpqrBoundedEvs.mono (by decide) (by omega)
      (SpqrBoundedEvs.append (spqrBoundedEvs_cloneEvs hmax1) h2)
  have h123 : SpqrBoundedEvs 98 (2 * x.p.authKey.length + 2048)
      ((cloneEvs x.p.authKey ++ evs₂) ++ evs₃) :=
    SpqrBoundedEvs.mono (by decide) (by omega)
      (SpqrBoundedEvs.append h12 (spqrBoundedEvs_encodeToVec hmax3 h3))
  have h1234 : SpqrBoundedEvs 128 (4 * x.p.authKey.length + 4096)
      (((cloneEvs x.p.authKey ++ evs₂) ++ evs₃) ++ evs₄) :=
    SpqrBoundedEvs.mono (by decide) (by omega)
      (SpqrBoundedEvs.append h123 (SpqrBoundedEvs.of_freeOnly h4))
  simpa only [InitialStateEnv, hv] using h1234

/-! ## 3. `auth_key.to_vec()` (`+232 -> +284`) on `Block 327` -/

theorem initial_state_to_vec_empty_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (s0 s : State) (x : InitialStateGhost) (Rest : SepProp)
    (hpc : s.pc = initialStatePlacedEntry + 232#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 496#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = x.pA) (hx21 : s.readReg64 .x21 = 0#64)
    (hx22 : s.readReg64 .x22 = x.akPtr) (hw25 : s.readReg32 .x25 = 1#32)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (initialStatePlacedProg ext)
      (initialStatePlacedEntry + 284#64) s Rest
      (fun s2 P2 =>
        (P2 ⊢ vecU8Buf A 0#64 1#64 [] ∗ Rest) ∧
        VmPreserved s s2 ∧
        s2.sp = s0.sp - 496#64 ∧ s2.readReg64 .x29 = s0.sp - 96#64 ∧
        s2.readReg64 .x19 = x.ret ∧ s2.readReg64 .x20 = x.pA ∧
        s2.readReg64 .x21 = 0#64 ∧ s2.readReg64 .x22 = x.akPtr ∧
        s2.readReg64 .x23 = 1#64 ∧ s2.readReg32 .x25 = 1#32 ∧ s2.trace = s0.trace ∧
        calleeSavedVRegs s2 = calleeSavedVRegs s0) := by
  have hbuf : Rest ⊢ vecU8Buf A 0#64 1#64 [] ∗ Rest :=
    Entails.trans (Entails.of_eq (emp_sepConj Rest).symm) (sepConj_mono_left (vecU8Buf_nil A))
  dsimp only [initialStatePlacedProg, initialStatePlacedEntry,
    State.readReg32, Reg.x25, BitVec.ofNat_eq_ofNat] at hpc hw25 ⊢
  refine sepWP_rebase_strengthen_vmPreserved hbuf ?_
  by_vm_steps (wp_steps; wp_done)

theorem initial_state_to_vec_stepA_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (x : InitialStateGhost) (P : SepProp)
    (hbeq0 : (BitVec.ofNat 64 x.p.authKey.length == 0#64) = false)
    (_hne0 : (BitVec.ofNat 64 x.p.authKey.length != 0#64) = true)
    (hpc : s.pc = initialStatePlacedEntry + 232#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 496#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = x.pA)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 x.p.authKey.length)
    (hx22 : s.readReg64 .x22 = x.akPtr) (hw25 : s.readReg32 .x25 = 1#32)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (initialStatePlacedProg ext) (lsρ spqrRustNoAllocShimSym) s P
      (fun sa Pa =>
        (Pa ⊢ P) ∧ VmPreserved s sa ∧
        sa.sp = s0.sp - 496#64 ∧ sa.readReg64 .x30 = initialStatePlacedEntry + 240#64 ∧
        sa.readReg64 .x29 = s0.sp - 96#64 ∧ sa.readReg64 .x19 = x.ret ∧
        sa.readReg64 .x20 = x.pA ∧ sa.readReg64 .x21 = BitVec.ofNat 64 x.p.authKey.length ∧
        sa.readReg64 .x22 = x.akPtr ∧ sa.readReg32 .x25 = 1#32 ∧
        sa.trace = s0.trace ∧ calleeSavedVRegs sa = calleeSavedVRegs s0) := by
  dsimp only [initialStatePlacedProg, initialStatePlacedEntry, lsρ, spqrRustNoAllocShimSym,
    State.readReg32, Reg.x25, BitVec.ofNat_eq_ofNat] at hpc hw25 ⊢
  refine sepWP_rebase_strengthen_vmPreserved (Entails.refl _) ?_
  by_vm_steps (wp_steps; wp_done)

theorem initial_state_to_vec_stepB_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 sb : State) (x : InitialStateGhost) (P : SepProp)
    (hpc : sb.pc = initialStatePlacedEntry + 240#64)
    (hrun : sb.status = .Running) (hsp : sb.sp = s0.sp - 496#64)
    (hx29 : sb.readReg64 .x29 = s0.sp - 96#64) (hx19 : sb.readReg64 .x19 = x.ret)
    (hx20 : sb.readReg64 .x20 = x.pA)
    (hx21 : sb.readReg64 .x21 = BitVec.ofNat 64 x.p.authKey.length)
    (hx22 : sb.readReg64 .x22 = x.akPtr) (hw25 : sb.readReg32 .x25 = 1#32)
    (htr : sb.trace = s0.trace) (hvregs : calleeSavedVRegs sb = calleeSavedVRegs s0) :
    SepWP (initialStatePlacedProg ext) (lsρ spqrRustAllocSym) sb P
      (fun sc Pc =>
        (Pc ⊢ P) ∧ VmPreserved sb sc ∧
        sc.sp = s0.sp - 496#64 ∧ sc.readReg64 .x30 = initialStatePlacedEntry + 256#64 ∧
        sc.readReg64 .x0 = BitVec.ofNat 64 x.p.authKey.length ∧ sc.readReg64 .x1 = 1#64 ∧
        sc.readReg64 .x29 = s0.sp - 96#64 ∧ sc.readReg64 .x19 = x.ret ∧
        sc.readReg64 .x20 = x.pA ∧ sc.readReg64 .x21 = BitVec.ofNat 64 x.p.authKey.length ∧
        sc.readReg64 .x22 = x.akPtr ∧ sc.readReg32 .x25 = 1#32 ∧
        sc.trace = s0.trace ∧ calleeSavedVRegs sc = calleeSavedVRegs s0) := by
  dsimp only [initialStatePlacedProg, initialStatePlacedEntry, lsρ, spqrRustAllocSym,
    State.readReg32, Reg.x25, BitVec.ofNat_eq_ofNat] at hpc hw25 ⊢
  refine sepWP_rebase_strengthen_vmPreserved (Entails.refl _) ?_
  by_vm_steps (wp_steps; wp_done)

theorem initial_state_to_vec_stepC_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 sd : State) (x : InitialStateGhost) (ptr_c : BitVec 64) (P : SepProp)
    (hoom_beq : (ptr_c == 0#64) = false) (_hoom_bne : (ptr_c != 0#64) = true)
    (hpc : sd.pc = initialStatePlacedEntry + 256#64)
    (hrun : sd.status = .Running) (hsp : sd.sp = s0.sp - 496#64)
    (hx0 : sd.readReg64 .x0 = ptr_c)
    (hx29 : sd.readReg64 .x29 = s0.sp - 96#64) (hx19 : sd.readReg64 .x19 = x.ret)
    (hx20 : sd.readReg64 .x20 = x.pA)
    (hx21 : sd.readReg64 .x21 = BitVec.ofNat 64 x.p.authKey.length)
    (hx22 : sd.readReg64 .x22 = x.akPtr) (hw25 : sd.readReg32 .x25 = 1#32)
    (htr : sd.trace = s0.trace) (hvregs : calleeSavedVRegs sd = calleeSavedVRegs s0) :
    SepWP (initialStatePlacedProg ext) (lsρ lsMemcpySym) sd P
      (fun se Pe =>
        (Pe ⊢ P) ∧ VmPreserved sd se ∧
        se.sp = s0.sp - 496#64 ∧ se.readReg64 .x30 = initialStatePlacedEntry + 276#64 ∧
        se.readReg64 .x0 = ptr_c ∧ se.readReg64 .x1 = x.akPtr ∧
        se.readReg64 .x2 = BitVec.ofNat 64 x.p.authKey.length ∧
        se.readReg64 .x29 = s0.sp - 96#64 ∧ se.readReg64 .x19 = x.ret ∧
        se.readReg64 .x20 = x.pA ∧ se.readReg64 .x21 = BitVec.ofNat 64 x.p.authKey.length ∧
        se.readReg64 .x22 = x.akPtr ∧ se.readReg64 .x23 = ptr_c ∧
        se.readReg32 .x25 = 1#32 ∧ se.trace = s0.trace ∧
        calleeSavedVRegs se = calleeSavedVRegs s0) := by
  dsimp only [initialStatePlacedProg, initialStatePlacedEntry, lsρ, lsMemcpySym,
    State.readReg32, Reg.x0, Reg.x25, BitVec.ofNat_eq_ofNat]
    at hpc hx0 hoom_beq hw25 ⊢
  refine sepWP_rebase_strengthen_vmPreserved (Entails.refl _) ?_
  by_vm_steps (wp_steps; wp_done)

theorem initial_state_to_vec_stepD_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (s0 sf : State) (x : InitialStateGhost) (ptr_c : BitVec 64) (Rest : SepProp)
    (hpos : 0 < x.p.authKey.length) (hlt : x.p.authKey.length < 2 ^ 63) (hptr : ptr_c ≠ 0#64)
    (hpc : sf.pc = initialStatePlacedEntry + 276#64)
    (hrun : sf.status = .Running) (hsp : sf.sp = s0.sp - 496#64)
    (hx29 : sf.readReg64 .x29 = s0.sp - 96#64) (hx19 : sf.readReg64 .x19 = x.ret)
    (hx20 : sf.readReg64 .x20 = x.pA)
    (hx21 : sf.readReg64 .x21 = BitVec.ofNat 64 x.p.authKey.length)
    (hx22 : sf.readReg64 .x22 = x.akPtr) (hx23 : sf.readReg64 .x23 = ptr_c)
    (hw25 : sf.readReg32 .x25 = 1#32)
    (htr : sf.trace = s0.trace) (hvregs : calleeSavedVRegs sf = calleeSavedVRegs s0) :
    SepWP (initialStatePlacedProg ext) (initialStatePlacedEntry + 284#64) sf
      ((A.live ptr_c x.p.authKey.length 1 ∗ (ptr_c ↦ₛ x.p.authKey)) ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ vecU8Buf A (BitVec.ofNat 64 x.p.authKey.length) ptr_c x.p.authKey ∗ Rest) ∧
        VmPreserved sf sm ∧
        sm.sp = s0.sp - 496#64 ∧ sm.readReg64 .x29 = s0.sp - 96#64 ∧
        sm.readReg64 .x19 = x.ret ∧ sm.readReg64 .x20 = x.pA ∧
        sm.readReg64 .x21 = BitVec.ofNat 64 x.p.authKey.length ∧
        sm.readReg64 .x22 = x.akPtr ∧ sm.readReg64 .x23 = ptr_c ∧
        sm.readReg32 .x25 = 1#32 ∧ sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0) := by
  have hbuf := sepConj_mono_left (Q := Rest) (vecU8Buf_nonempty A ptr_c x.p.authKey hpos hlt hptr)
  dsimp only [initialStatePlacedProg, initialStatePlacedEntry,
    State.readReg32, Reg.x25, BitVec.ofNat_eq_ofNat] at hpc hw25 ⊢
  refine sepWP_rebase_strengthen_vmPreserved hbuf ?_
  by_vm_steps (wp_steps; wp_done)

/-- Budget-threaded `auth_key.to_vec()` (`+232 -> +284`) on `Block 327`, advancing `st0` to
    `M.stepEvents (cloneEvs x.p.authKey) st0` without OOM or panic. -/
theorem initial_state_to_vec_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (hshim : subroutine_ok (initialStatePlacedProg ext) (lsρ spqrRustNoAllocShimSym)
      noAllocShimBudgetSpec)
    (halloc : subroutine_ok (initialStatePlacedProg ext) (lsρ spqrRustAllocSym)
      (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok (initialStatePlacedProg ext) (lsρ lsMemcpySym)
      framelessMemcpyBudgetSpec)
    (s0 s : State) (x : InitialStateGhost) (st0 : M.σ) (Frame R : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hlt : x.p.authKey.length < 2 ^ 63)
    (hv : x.p.version = .v1) (hfit : FitsEnv M lim st0 (InitialStateEnv F x))
    (hpc : s.pc = initialStatePlacedEntry + 232#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 496#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = x.pA)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 x.p.authKey.length)
    (hx22 : s.readReg64 .x22 = x.akPtr) (hw25 : s.readReg32 .x25 = 1#32)
    (htrace : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (sm : State) (ptr : BitVec 64),
      sm.pc = initialStatePlacedEntry + 284#64 →
      sm.status = .Running → (LsCallInv lsmpl s.mem → LsCallInv lsmpl sm.mem) →
      sm.sp = s0.sp - 496#64 → sm.readReg64 .x29 = s0.sp - 96#64 →
      sm.readReg64 .x19 = x.ret → sm.readReg64 .x20 = x.pA →
      sm.readReg64 .x21 = BitVec.ofNat 64 x.p.authKey.length →
      sm.readReg64 .x22 = x.akPtr → sm.readReg64 .x23 = ptr →
      sm.readReg32 .x25 = 1#32 → sm.trace = s0.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp (initialStatePlacedProg ext) (s0.readReg64 .x30) sm
        (vecU8Buf A.repAlloc (BitVec.ofNat 64 x.p.authKey.length) ptr x.p.authKey ∗
         (x.akPtr ↦ₛ x.p.authKey) ∗
         A.pool lim (M.stepEvents (cloneEvs x.p.authKey) st0) sm ∗
         stackAt (s0.sp - 496#64) allocHookStack ∗ Frame)
        Q (InitInnerBudgetPanic R)) :
    SepWPp (initialStatePlacedProg ext) (s0.readReg64 .x30) s
      ((x.akPtr ↦ₛ x.p.authKey) ∗ A.pool lim st0 s ∗
       stackAt (s0.sp - 496#64) allocHookStack ∗ Frame)
      Q (InitInnerBudgetPanic R) := by
  have hfsp_align : ((s0.sp - 496#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 496#64 hsp0_align (by decide)
  by_cases hlen_zero : x.p.authKey.length = 0
  · have hnil : x.p.authKey = [] := List.eq_nil_of_length_eq_zero hlen_zero
    have hx21_0 : s.readReg64 .x21 = 0#64 := by rw [hx21, hlen_zero]
    refine initInner_seq_sepWP_lsInv
      (initial_state_to_vec_empty_placed (A := A.repAlloc) s0 s x
        ((x.akPtr ↦ₛ x.p.authKey) ∗ A.pool lim st0 s ∗
         stackAt (s0.sp - 496#64) allocHookStack ∗ Frame)
        hpc hrun hsp hx29 hx19 hx20 hx21_0 hx22 hw25 htrace hvregs) ?_
    intro sm hpcm hrunm _ hinvm
      ⟨hvmm, hspm, hx29m, hx19m, hx20m, hx21m, hx22m, hx23m, hw25m, htrm, hvregsm⟩
    have hbuf_eq : vecU8Buf A.repAlloc (BitVec.ofNat 64 x.p.authKey.length) 1#64 x.p.authKey =
        vecU8Buf A.repAlloc 0#64 1#64 [] := by
      conv => lhs; rw [hnil]; dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat]
    have hx21m' : sm.readReg64 .x21 = BitVec.ofNat 64 x.p.authKey.length := by
      rw [hx21m, hlen_zero]
    have hpool :
        vecU8Buf A.repAlloc 0#64 1#64 [] ∗
        ((x.akPtr ↦ₛ x.p.authKey) ∗ A.pool lim st0 s ∗
         stackAt (s0.sp - 496#64) allocHookStack ∗ Frame) ⊢
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.p.authKey.length) 1#64 x.p.authKey ∗
        (x.akPtr ↦ₛ x.p.authKey) ∗
        A.pool lim (M.stepEvents (cloneEvs x.p.authKey) st0) sm ∗
        stackAt (s0.sp - 496#64) allocHookStack ∗ Frame := by
      rw [← hbuf_eq, cloneEvs_of_length_zero hlen_zero, M.stepEvents_nil, A.pool_of_vmPreserved hvmm]
      exact Entails.of_eq (by sep_ac_rfl)
    exact SepWPp.weaken_pre hpool
      (hnext sm 1#64 hpcm hrunm hinvm hspm hx29m hx19m hx20m hx21m' hx22m hx23m hw25m htrm hvregsm)
  · have hpos : 0 < x.p.authKey.length := Nat.pos_of_ne_zero hlen_zero
    have ⟨hlay, hfits_cl⟩ := fitsEvents_clone_of_initialStateEnv hpos hv hfit
    have halloc_noOom := subroutine_ok_allocNoOom_of_budget halloc
    have htoNat_len : (BitVec.ofNat 64 x.p.authKey.length).toNat = x.p.authKey.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hne_bv0 : BitVec.ofNat 64 x.p.authKey.length ≠ 0#64 := by
      intro h; have h1 := congrArg BitVec.toNat h; rw [htoNat_len] at h1
      change x.p.authKey.length = 0 at h1; omega
    have hbeq0 : (BitVec.ofNat 64 x.p.authKey.length == 0#64) = false :=
      beq_eq_false_iff_ne.mpr hne_bv0
    have hne0 : (BitVec.ofNat 64 x.p.authKey.length != 0#64) = true :=
      bne_iff_ne.mpr hne_bv0
    refine initInner_seq_sepWP_lsInv
      (initial_state_to_vec_stepA_placed s0 s x _ hbeq0 hne0
        hpc hrun hsp hx29 hx19 hx20 hx21 hx22 hw25 htrace hvregs) ?_
    intro sa hpca hruna _ hinva
      ⟨hvma, hspa, hlra, hx29a, hx19a, hx20a, hx21a, hx22a, hw25a, htra, hvregsa⟩
    refine sepWPp_call_total_keepLsInv ()
      (Frame := (x.akPtr ↦ₛ x.p.authKey) ∗ A.pool lim st0 s ∗
        stackAt (s0.sp - 496#64) allocHookStack ∗ Frame)
      hshim hpca hruna (by rw [State.spAligned, hspa]; exact hfsp_align) hlra
      (fun R' hm => by
        dsimp only [noAllocShimBudgetSpec]
        exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm)
      (hnext := fun sb hpcb hrunb _ hinvb hspb hcsb => ?_)
    dsimp only [noAllocShimBudgetSpec]
    refine SepWPp.pure_left fun ⟨htrb, hvmb⟩ => ?_
    obtain ⟨hx19b, hx20b, hx21b, hx22b, _, _, hx25b, _, _, _, hx29b⟩ := hcsb
    refine initInner_seq_sepWP_lsInv
      (initial_state_to_vec_stepB_placed s0 sb x _
        hpcb hrunb (hspb.trans hspa) (hx29b.1.trans hx29a) (hx19b.trans hx19a)
        (hx20b.trans hx20a) (hx21b.trans hx21a) (hx22b.trans hx22a)
        ((readReg32_of_eq hx25b).trans hw25a) (htrb.trans htra) (hx29b.2.trans hvregsa)) ?_
    intro sc hpcc hrunc _ hinvc
      ⟨hvmc, hspc, hlrc, hx0c, hx1c, hx29c, hx19c, hx20c, hx21c, hx22c, hw25c, htrc, hvregsc⟩
    have hvm_s_sc : VmPreserved s sc := hvma.trans (hvmb.trans hvmc)
    have hpre_alloc :
        (x.akPtr ↦ₛ x.p.authKey) ∗ A.pool lim st0 s ∗
        stackAt (s0.sp - 496#64) allocHookStack ∗ Frame ⊢
        (A.pool lim st0 sc ∗ stackAt sc.sp allocHookStack) ∗
        ((x.akPtr ↦ₛ x.p.authKey) ∗ Frame) := by
      rw [hspc, ← A.pool_of_vmPreserved hvm_s_sc]
      exact Entails.of_eq (by sep_ac_rfl)
    refine SepWPp.weaken_pre hpre_alloc ?_
    refine sepWPp_call_total_keepLsInv (x.p.authKey.length, 1, st0)
      (Frame := (x.akPtr ↦ₛ x.p.authKey) ∗ Frame)
      halloc_noOom hpcc hrunc (by rw [State.spAligned, hspc]; exact hfsp_align) hlrc
      (fun R' hm => by
        dsimp only [rustCliAllocNoOomSpec]
        have hlr_ls : LsRetAddr624 (sc.readReg64 .lr) := by
          change LsRetAddr624 (sc.readReg64 .x30); rw [hlrc]
          dsimp only [initialStatePlacedEntry]
          simp (config := { decide := true }) only [arm64_norm, wp_norm]
        simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
        exact ⟨⟨by rw [hx0c, htoNat_len], by rw [hx1c]; rfl, hlay, hfits_cl, hlr_ls⟩, hm⟩)
      (hnext := fun sd hpcd hrund _ hinvd hspd hcsd => ?_)
    dsimp only [rustCliAllocNoOomSpec]
    rw [sepConj_assoc]
    refine SepWPp.pure_left fun ⟨hpresd, hptr_ne0, _⟩ => ?_
    obtain ⟨hx19d, hx20d, hx21d, hx22d, _, _, hx25d, _, _, _, hx29d⟩ := hcsd
    let ptr_c := sd.readReg64 .x0
    have hoom_beq : (ptr_c == 0#64) = false := beq_eq_false_iff_ne.mpr hptr_ne0
    have hoom_bne : (ptr_c != 0#64) = true := bne_iff_ne.mpr hptr_ne0
    refine initInner_seq_sepWP_lsInv
      (initial_state_to_vec_stepC_placed s0 sd x ptr_c _ hoom_beq hoom_bne
        hpcd hrund (hspd.trans hspc) rfl
        (hx29d.1.trans hx29c) (hx19d.trans hx19c) (hx20d.trans hx20c)
        (hx21d.trans hx21c) (hx22d.trans hx22c)
        ((readReg32_of_eq hx25d).trans hw25c) (hpresd.2.1.trans htrc)
        (hx29d.2.trans hvregsc)) ?_
    intro se hpce hrune _ hinve
      ⟨hvme, hspe, hlre, hx0e, hx1e, hx2e, hx29e, hx19e, hx20e, hx21e, hx22e, hx23e,
       hw25e, htre, hvregse⟩
    have hpre_mc :
        (A.pool lim (M.stepEvents (rustAllocEvents x.p.authKey.length 1) st0) sd ∗
         stackAt sc.sp allocHookStack ∗ A.live ptr_c x.p.authKey.length 1 ∗
         memRegion ptr_c x.p.authKey.length) ∗
        ((x.akPtr ↦ₛ x.p.authKey) ∗ Frame) ⊢
        (memRegion ptr_c x.p.authKey.length ∗ (x.akPtr ↦ₛ x.p.authKey)) ∗
        (A.live ptr_c x.p.authKey.length 1 ∗
         A.pool lim (M.stepEvents (cloneEvs x.p.authKey) st0) se ∗
         stackAt (s0.sp - 496#64) allocHookStack ∗ Frame) := by
      rw [cloneEvs_of_pos hpos, hspc, ← A.pool_of_vmPreserved hvme]
      exact Entails.of_eq (by sep_ac_rfl)
    refine SepWPp.weaken_pre hpre_mc ?_
    refine sepWPp_call_total_keepLsInv (ptr_c, x.akPtr, x.p.authKey)
      (Frame := A.live ptr_c x.p.authKey.length 1 ∗
        A.pool lim (M.stepEvents (cloneEvs x.p.authKey) st0) se ∗
        stackAt (s0.sp - 496#64) allocHookStack ∗ Frame)
      hmemcpy hpce hrune (by rw [State.spAligned, hspe]; exact hfsp_align) hlre
      (fun R' hm => by
        dsimp only [framelessMemcpyBudgetSpec]
        simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
        exact ⟨⟨hx0e, hx1e, by rw [hx2e, htoNat_len]⟩, hm⟩)
      (hnext := fun sf hpcf hrunf _ hinvf hspf hcsf => ?_)
    dsimp only [framelessMemcpyBudgetSpec]
    rw [sepConj_assoc]
    refine SepWPp.pure_left fun ⟨_, htrf, hvmf⟩ => ?_
    obtain ⟨hx19f, hx20f, hx21f, hx22f, hx23f, _, hx25f, _, _, _, hx29f⟩ := hcsf
    have hre_f :
        ((ptr_c ↦ₛ x.p.authKey) ∗ (x.akPtr ↦ₛ x.p.authKey)) ∗
        (A.live ptr_c x.p.authKey.length 1 ∗
         A.pool lim (M.stepEvents (cloneEvs x.p.authKey) st0) se ∗
         stackAt (s0.sp - 496#64) allocHookStack ∗ Frame) ⊢
        (A.repAlloc.live ptr_c x.p.authKey.length 1 ∗ (ptr_c ↦ₛ x.p.authKey)) ∗
        ((x.akPtr ↦ₛ x.p.authKey) ∗
         A.pool lim (M.stepEvents (cloneEvs x.p.authKey) st0) sf ∗
         stackAt (s0.sp - 496#64) allocHookStack ∗ Frame) := by
      rw [← A.pool_of_vmPreserved hvmf]
      exact Entails.of_eq (by sep_ac_rfl)
    refine SepWPp.weaken_pre hre_f ?_
    refine initInner_seq_sepWP_lsInv
      (initial_state_to_vec_stepD_placed (A := A.repAlloc) s0 sf x ptr_c _ hpos hlt hptr_ne0
        hpcf hrunf (hspf.trans hspe) (hx29f.1.trans hx29e) (hx19f.trans hx19e)
        (hx20f.trans hx20e) (hx21f.trans hx21e) (hx22f.trans hx22e) (hx23f.trans hx23e)
        ((readReg32_of_eq hx25f).trans hw25e) (htrf.trans htre) (hx29f.2.trans hvregse)) ?_
    intro sm hpcm hrunm _ hinvm
      ⟨hvmm, hspm, hx29m, hx19m, hx20m, hx21m, hx22m, hx23m, hw25m, htrm, hvregsm⟩
    have hpool_m :
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.p.authKey.length) ptr_c x.p.authKey ∗
        ((x.akPtr ↦ₛ x.p.authKey) ∗
         A.pool lim (M.stepEvents (cloneEvs x.p.authKey) st0) sf ∗
         stackAt (s0.sp - 496#64) allocHookStack ∗ Frame) ⊢
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.p.authKey.length) ptr_c x.p.authKey ∗
        (x.akPtr ↦ₛ x.p.authKey) ∗
        A.pool lim (M.stepEvents (cloneEvs x.p.authKey) st0) sm ∗
        stackAt (s0.sp - 496#64) allocHookStack ∗ Frame := by
      rw [← A.pool_of_vmPreserved hvmm]
      exact Entails.of_eq (by sep_ac_rfl)
    exact SepWPp.weaken_pre hpool_m
      (hnext sm ptr_c hpcm hrunm
        (fun hinv => hinvm (hinvf (hinve (hinvd (hinvc (hinvb (hinva hinv)))))))
        hspm hx29m hx19m hx20m hx21m hx22m hx23m hw25m htrm hvregsm)

/-! ## 4. Callee Bridges and `spqr::init_inner` Call (`+284 -> +340`) on `Block 327` -/

theorem initialState_initInner_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hinit : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (blkPl_324).base (withLsCodeLoaded lsmpl (initInnerPlacedSpecX M A lim F))) :
    subroutine_ok (initialStatePlacedProg ext) (lsmpl.base 324)
      (withLsCallInv lsmpl (initInnerPlacedSpecX M A lim F)) := by
  apply subroutine_ok_withLsCallInv_of_withLsCodeLoaded
  exact subroutine_ok_mono
    (ls_subroutine_ok_cl_of_block (callerProg := initialStatePlacedProg ext) hinit)
    (fun _ _ _ h => h)
    (fun _ _ _ _ h => by
      dsimp only [withLsCl, withLsCodeLoaded] at h ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at h
      exact h.2)

theorem initialState_encodeToVec_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (henc : PqRatchetStateEncodeToVecPlacedOkExt A lim ext) :
    subroutine_ok (initialStatePlacedProg ext) (lsmpl.base 426)
      (withLsCallInv lsmpl (pqRatchetStateEncodeToVecSpecX A lim)) := by
  have henc_call : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext))
      (blkPl_426).base (withLsCallInv lsmpl (pqRatchetStateEncodeToVecSpecX A lim)) := by
    refine subroutine_ok_mono henc (fun x s0 R hpre => ?_) (fun _ _ _ _ hq => hq)
    dsimp only [withLsCallInv] at hpre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    obtain ⟨⟨hro, hcl⟩, hpre⟩ := hpre
    dsimp only [withLsRoLoaded, withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hro, ?_⟩
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl, hpre⟩
  exact ls_subroutine_ok_callInv_of_block (callerProg := initialStatePlacedProg ext) henc_call

theorem initialState_dropPqRatchetState_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdrop : subroutine_ok ((blkPC_270).rebase (blkPl_270).base (Rust.withPanics ext))
      (blkPl_270).base (withLsCodeLoaded lsmpl (dropProtoPqRatchetStatePlacedSpec M A lim))) :
    subroutine_ok (initialStatePlacedProg ext) (lsmpl.base 270)
      (withLsCodeLoaded lsmpl (dropProtoPqRatchetStatePlacedSpec M A lim)) :=
  subroutine_ok_mono
    (ls_subroutine_ok_cl_of_block (callerProg := initialStatePlacedProg ext) hdrop)
    (fun _ _ _ h => h)
    (fun _ _ _ _ h => by
      dsimp only [withLsCl, withLsCodeLoaded] at h ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at h
      exact h.2)

theorem initial_state_pre_init_inner_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (x : InitialStateGhost) (ptr : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = initialStatePlacedEntry + 284#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 496#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = x.pA) (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 x.p.authKey.length)
    (hx22 : s.readReg64 .x22 = x.akPtr) (hx23 : s.readReg64 .x23 = ptr)
    (hw25 : s.readReg32 .x25 = 1#32) (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (initialStatePlacedProg ext) (lsmpl.base 324) s
      (paramsAt x.pA x.akPtr x.p ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢ paramsAt x.pA x.akPtr x.p ∗ Rest) ∧
        VmPreserved s s2 ∧
        s2.sp = s0.sp - 496#64 ∧
        s2.readReg64 .x30 = initialStatePlacedEntry + 344#64 ∧
        s2.readReg64 .x0 = (s0.sp - 456#64) + 0x80#64 ∧
        s2.readReg32 .x1 = Version.v1.toI32 ∧ s2.readReg32 .x2 = x.p.direction.toI32 ∧
        s2.readReg64 .x3 = x.akPtr ∧ s2.readReg64 .x4 = BitVec.ofNat 64 x.p.authKey.length ∧
        s2.readReg64 .x29 = s0.sp - 96#64 ∧ s2.readReg64 .x19 = x.ret ∧
        s2.readReg32 .x20 = x.p.minVersion.toI32 ∧
        s2.readReg64 .x21 = BitVec.ofNat 64 x.p.authKey.length ∧ s2.readReg64 .x23 = ptr ∧
        s2.readReg32 .x24 = x.p.direction.toI32 ∧ s2.readReg32 .x25 = 1#32 ∧
        s2.readReg32 .x26 = x.p.chainParams.intoPb.maxJump ∧
        s2.readReg32 .x27 = x.p.chainParams.intoPb.maxOooKeys ∧ s2.trace = s0.trace ∧
        calleeSavedVRegs s2 = calleeSavedVRegs s0) := by
  have hsp496_align : ((s0.sp - 496#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 496#64 hsp0_align (by decide)
  dsimp only [initialStatePlacedProg, initialStatePlacedEntry, paramsAt, Version.toI32,
    State.readReg32, Reg.x1, Reg.x2, Reg.x20, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
    BitVec.ofNat_eq_ofNat] at hpc hw25 ⊢
  refine sepWP_rebase_strengthen_vmPreserved (Entails.refl _) ?_
  by_vm_steps (
    wp_steps
    refine align_pre_tp (by sep_ac_rfl) ?_
    wp_done
  )

theorem call_initInner_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hinit : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (blkPl_324).base (withLsCodeLoaded lsmpl (initInnerPlacedSpecX M A lim F)))
    {Q : State → SepProp → Prop}
    (s0 s : State) (x : InitialStateGhost) (st_in : M.σ) (Frame R : SepProp)
    (hinv : LsCallInv lsmpl s.mem) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hak_ne : x.akPtr ≠ 0#64) (hlt : 32 + x.p.authKey.length < 2 ^ 63)
    (hfit_in : FitsEnv M lim st_in
      (InitInnerEnv F ⟨(s0.sp - 456#64) + 0x80#64, .v1, x.p.direction, x.akPtr, x.p.authKey⟩))
    (hpc : s.pc = lsmpl.base 324)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 496#64)
    (hlr : s.readReg64 .x30 = initialStatePlacedEntry + 344#64)
    (hx0 : s.readReg64 .x0 = (s0.sp - 456#64) + 0x80#64)
    (hw1 : s.readReg32 .x1 = Version.v1.toI32) (hw2 : s.readReg32 .x2 = x.p.direction.toI32)
    (hx3 : s.readReg64 .x3 = x.akPtr) (hx4 : s.readReg64 .x4 = BitVec.ofNat 64 x.p.authKey.length)
    (htrace : s.trace = s0.trace)
    (hnext : ∀ (sf : State) (evs₂ : List AllocEvent),
      sf.pc = initialStatePlacedEntry + 344#64 →
      sf.status = .Running → LsCallInv lsmpl sf.mem → sf.sp = s0.sp - 496#64 →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      InitInnerEnv F ⟨(s0.sp - 456#64) + 0x80#64, .v1, x.p.direction, x.akPtr, x.p.authKey⟩ evs₂ →
      SepWPp (initialStatePlacedProg ext) (s0.readReg64 .x30) sf
        ((initInnerResultAt A.repAlloc (F := F) ((s0.sp - 456#64) + 0x80#64) .v1 x.p.direction x.p.authKey ∗
          (x.akPtr ↦ₛ x.p.authKey) ∗ statesIntoPbJumpTablePlacedAt ∗
          A.pool lim (M.stepEvents evs₂ st_in) sf ∗
          stackAt (s0.sp - 496#64) initInnerStack) ∗ Frame)
        Q (InitInnerBudgetPanic R)) :
    SepWPp (initialStatePlacedProg ext) (s0.readReg64 .x30) s
      ((memRegion ((s0.sp - 456#64) + 0x80#64) optProtoInnerStateSize ∗
        (x.akPtr ↦ₛ x.p.authKey) ∗ statesIntoPbJumpTablePlacedAt ∗
        A.pool lim st_in s ∗ stackAt (s0.sp - 496#64) initInnerStack) ∗ Frame)
      Q (InitInnerBudgetPanic R) := by
  have hfsp_align : ((s0.sp - 496#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 496#64 hsp0_align (by decide)
  have hcall := initialState_initInner_placed_ok hinit
  let gx : InitInnerGhost :=
    ⟨(s0.sp - 456#64) + 0x80#64, .v1, x.p.direction, x.akPtr, x.p.authKey⟩
  refine sepWPp_call_total_keepLsInv (gx, st_in) (Frame := Frame)
    hcall hpc hrun (by rw [State.spAligned, hsp]; exact hfsp_align) hlr
    (fun R' hm => by
      dsimp only [withLsCallInv, initInnerPlacedSpecX, initInnerPlacedSpecXOfEnv, initInnerStackX, gx]
      rw [hsp]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
      exact ⟨hinv, ⟨hx0, hw1, hw2, hx3, hx4, hak_ne, hlt, hfit_in⟩, hm⟩)
    (hnext := fun sf hpc_sf hrun_sf _ hinv_sf hsp_sf hcs_sf => ?_)
  dsimp only [withLsCallInv, initInnerPlacedSpecX, initInnerPlacedSpecXOfEnv, initInnerStackX, gx]
  rw [hsp, sepExists_sepConj_left]
  refine SepWPp.exists_elim fun evs₂ => ?_
  rw [sepConj_assoc]
  refine SepWPp.pure_left fun ⟨htr, hevs₂⟩ => ?_
  have hnext' := hnext sf evs₂ hpc_sf hrun_sf (hinv_sf hinv) (by rw [hsp_sf, hsp]) hcs_sf
    (by rw [htr, htrace]) hevs₂
  exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hnext'

/-! ## 5. `PqRatchetState` Stores (`+344 -> +380`) and `encode_to_vec` Call on `Block 327` -/

theorem initial_state_pre_encode_to_vec_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s : State) (x : InitialStateGhost) (ptr : BitVec 64) (Rest : SepProp)
    (hpbAt :
      (vecU8At A (s0.sp - 456#64) (BitVec.ofNat 64 x.p.authKey.length) ptr x.p.authKey ∗
        (((s0.sp - 456#64) + 0x18#64) ↦₃₂ 1#32) ∗
        (((s0.sp - 456#64) + 0x1c#64) ↦₃₂ x.p.chainParams.intoPb.maxJump) ∗
        (((s0.sp - 456#64) + 0x20#64) ↦₃₂ x.p.chainParams.intoPb.maxOooKeys) ∗
        (((s0.sp - 456#64) + 0x24#64) ↦₃₂ x.p.direction.toI32) ∗
        (((s0.sp - 456#64) + 0x28#64) ↦₃₂ x.p.minVersion.toI32) ∗
        memRegion ((s0.sp - 456#64) + 0x2c#64) 4 ∗
        (((s0.sp - 456#64) + 0x30#64) ↦₆₄ noneCap) ∗
        memRegion ((s0.sp - 456#64) + 0x38#64) 72 ∗
        initInnerResultAt A (F := F) ((s0.sp - 456#64) + 0x80#64) .v1 x.p.direction x.p.authKey) ⊢
      pqRatchetStatePBAt A (s0.sp - 456#64) (initialStatePB F x.p))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = initialStatePlacedEntry + 344#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 496#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) (hx19 : s.readReg64 .x19 = x.ret)
    (hw20 : s.readReg32 .x20 = x.p.minVersion.toI32)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 x.p.authKey.length) (hx23 : s.readReg64 .x23 = ptr)
    (hw24 : s.readReg32 .x24 = x.p.direction.toI32) (hw25 : s.readReg32 .x25 = 1#32)
    (hw26 : s.readReg32 .x26 = x.p.chainParams.intoPb.maxJump)
    (hw27 : s.readReg32 .x27 = x.p.chainParams.intoPb.maxOooKeys) (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (initialStatePlacedProg ext) (lsmpl.base 426) s
      (cells (s0.sp - 456#64) 3 ∗
       (∃∗ v0 : BitVec 32, ((s0.sp - 456#64) + 0x18#64) ↦₃₂ v0) ∗
       (∃∗ v1 : BitVec 32, ((s0.sp - 456#64) + 0x1c#64) ↦₃₂ v1) ∗
       (∃∗ v2 : BitVec 32, ((s0.sp - 456#64) + 0x20#64) ↦₃₂ v2) ∗
       (∃∗ v3 : BitVec 32, ((s0.sp - 456#64) + 0x24#64) ↦₃₂ v3) ∗
       (∃∗ v4 : BitVec 32, ((s0.sp - 456#64) + 0x28#64) ↦₃₂ v4) ∗
       memRegion ((s0.sp - 456#64) + 0x2c#64) 4 ∗
       (∃∗ w6 : BitVec 64, ((s0.sp - 456#64) + 0x30#64) ↦₆₄ w6) ∗
       memRegion ((s0.sp - 456#64) + 0x38#64) 72 ∗
       initInnerResultAt A (F := F) ((s0.sp - 456#64) + 0x80#64) .v1 x.p.direction x.p.authKey ∗
       vecU8Buf A (BitVec.ofNat 64 x.p.authKey.length) ptr x.p.authKey ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢ pqRatchetStatePBAt A (s0.sp - 456#64) (initialStatePB F x.p) ∗ Rest) ∧
        VmPreserved s s2 ∧
        s2.sp = s0.sp - 496#64 ∧
        s2.readReg64 .x30 = initialStatePlacedEntry + 384#64 ∧
        s2.readReg64 .x0 = x.ret + 8#64 ∧ s2.readReg64 .x1 = s0.sp - 456#64 ∧
        s2.readReg64 .x29 = s0.sp - 96#64 ∧ s2.readReg64 .x19 = x.ret ∧ s2.trace = s0.trace ∧
        calleeSavedVRegs s2 = calleeSavedVRegs s0) := by
  have hfold :
      ((((s0.sp - 456#64) ↦₆₄ BitVec.ofNat 64 x.p.authKey.length) ∗
        ((s0.sp - 448#64) ↦₆₄ ptr) ∗
        ((s0.sp - 440#64) ↦₆₄ BitVec.ofNat 64 x.p.authKey.length) ∗
        vecU8Buf A (BitVec.ofNat 64 x.p.authKey.length) ptr x.p.authKey) ∗
       (((s0.sp - 456#64) + 0x18#64) ↦₃₂ 1#32) ∗
       (((s0.sp - 456#64) + 0x1c#64) ↦₃₂ x.p.chainParams.intoPb.maxJump) ∗
       (((s0.sp - 456#64) + 0x20#64) ↦₃₂ x.p.chainParams.intoPb.maxOooKeys) ∗
       (((s0.sp - 456#64) + 0x24#64) ↦₃₂ x.p.direction.toI32) ∗
       (((s0.sp - 456#64) + 0x28#64) ↦₃₂ x.p.minVersion.toI32) ∗
       memRegion ((s0.sp - 456#64) + 0x2c#64) 4 ∗
       (((s0.sp - 456#64) + 0x30#64) ↦₆₄ noneCap) ∗
       memRegion ((s0.sp - 456#64) + 0x38#64) 72 ∗
       initInnerResultAt A (F := F) ((s0.sp - 456#64) + 0x80#64) .v1 x.p.direction x.p.authKey) ∗
      Rest ⊢ pqRatchetStatePBAt A (s0.sp - 456#64) (initialStatePB F x.p) ∗ Rest := by
    refine sepConj_mono_left (Entails.trans ?_ hpbAt)
    dsimp only [vecU8At, vecHeader, CryptoVerification.RustHeap.vecAt, vecU8Buf]
    exact Entails.of_eq (by simp only [arm64_norm])
  have hsp496_align : ((s0.sp - 496#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 496#64 hsp0_align (by decide)
  dsimp only [initialStatePlacedProg, initialStatePlacedEntry, noneCap,
    State.readReg32, Reg.x20, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
    BitVec.ofNat_eq_ofNat] at hpc hw20 hw24 hw25 hw26 hw27 ⊢
  refine sepWP_rebase_strengthen_vmPreserved hfold ?_
  by_vm_steps (
    cells_unfold
    wp_pull_exists
    wp_steps
    refine align_pre_tp (by simp only [arm64_norm]; sep_ac_rfl) ?_
    wp_done
  )

theorem call_encodeToVec_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (henc : PqRatchetStateEncodeToVecPlacedOkExt A lim ext)
    {Q : State → SepProp → Prop}
    (s0 s : State) (x : InitialStateGhost) (st_in : M.σ) (Frame R : SepProp)
    (hinv : LsCallInv lsmpl s.mem) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlen_pb : (PqRatchetState.encodeRaw (initialStatePB F x.p)).length < 2 ^ 63)
    (hfit_enc : FitsEnv M lim st_in (PqRatchetStateEncodeToVecEnv (initialStatePB F x.p)))
    (hpc : s.pc = lsmpl.base 426)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 496#64)
    (hlr : s.readReg64 .x30 = initialStatePlacedEntry + 384#64)
    (hx0 : s.readReg64 .x0 = x.ret + 8#64) (hx1 : s.readReg64 .x1 = s0.sp - 456#64)
    (htrace : s.trace = s0.trace)
    (hnext : ∀ (sf : State) (evs₃ : List AllocEvent),
      sf.pc = initialStatePlacedEntry + 384#64 →
      sf.status = .Running → LsCallInv lsmpl sf.mem → sf.sp = s0.sp - 496#64 →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      PqRatchetStateEncodeToVecEnv (initialStatePB F x.p) evs₃ →
      SepWPp (initialStatePlacedProg ext) (s0.readReg64 .x30) sf
        ((vecU8 A.repAlloc (x.ret + 8#64) (PqRatchetState.encodeRaw (initialStatePB F x.p)) ∗
          pqRatchetStatePBAt A.repAlloc (s0.sp - 456#64) (initialStatePB F x.p) ∗
          A.pool lim (M.stepEvents evs₃ st_in) sf ∗
          stackAt (s0.sp - 496#64) encodeToVecStackX) ∗ Frame)
        Q (InitInnerBudgetPanic R)) :
    SepWPp (initialStatePlacedProg ext) (s0.readReg64 .x30) s
      ((memRegion (x.ret + 8#64) 24 ∗
        pqRatchetStatePBAt A.repAlloc (s0.sp - 456#64) (initialStatePB F x.p) ∗
        A.pool lim st_in s ∗ stackAt (s0.sp - 496#64) encodeToVecStackX) ∗ Frame)
      Q (InitInnerBudgetPanic R) := by
  have hfsp_align : ((s0.sp - 496#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 496#64 hsp0_align (by decide)
  have hcall := initialState_encodeToVec_placed_ok henc
  let gx : PqRatchetStateEncodeToVecGhost := ⟨x.ret + 8#64, s0.sp - 456#64, initialStatePB F x.p⟩
  refine sepWPp_call_total_keepLsInv (gx, st_in) (Frame := Frame)
    hcall hpc hrun (by rw [State.spAligned, hsp]; exact hfsp_align) hlr
    (fun R' hm => by
      dsimp only [withLsCallInv, pqRatchetStateEncodeToVecSpecX, pqRatchetStateEncodeToVecSpecOf,
        pqRatchetStateEncodeToVecSpecOfEnv, gx]
      rw [hsp]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
      exact ⟨hinv, ⟨hx0, hx1, hlen_pb, hfit_enc⟩, hm⟩)
    (hnext := fun sf hpc_sf hrun_sf _ hinv_sf hsp_sf hcs_sf => ?_)
  dsimp only [withLsCallInv, pqRatchetStateEncodeToVecSpecX, pqRatchetStateEncodeToVecSpecOf,
    pqRatchetStateEncodeToVecSpecOfEnv, gx]
  rw [hsp, sepExists_sepConj_left]
  refine SepWPp.exists_elim fun evs₃ => ?_
  rw [sepConj_assoc]
  refine SepWPp.pure_left fun ⟨htr, hevs₃⟩ => ?_
  have hnext' := hnext sf evs₃ hpc_sf hrun_sf (hinv_sf hinv) (by rw [hsp_sf, hsp]) hcs_sf
    (by rw [htr, htrace]) hevs₃
  exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hnext'

/-! ## 6. `Ok` Tag Store (`+384 -> +392`) and `drop_glue::<PqRatchetState>` Call on `Block 327` -/

theorem initial_state_pre_drop_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s : State) (x : InitialStateGhost) (r0 : BitVec 64) (Rest : SepProp)
    (hv : x.p.version = .v1) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = initialStatePlacedEntry + 384#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 496#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) (hx19 : s.readReg64 .x19 = x.ret)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (initialStatePlacedProg ext) (lsmpl.base 270) s
      ((x.ret ↦₆₄ r0) ∗
       vecU8 A (x.ret + 8#64) (PqRatchetState.encodeRaw (initialStatePB F x.p)) ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢ initialStateResultAt A x.ret (initialStateValue F x.p) ∗ Rest) ∧
        VmPreserved s s2 ∧
        s2.sp = s0.sp - 496#64 ∧
        s2.readReg64 .x30 = initialStatePlacedEntry + 396#64 ∧
        s2.readReg64 .x0 = s0.sp - 456#64 ∧ s2.readReg64 .x29 = s0.sp - 96#64 ∧
        s2.trace = s0.trace ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0) := by
  have hres :
      ((x.ret ↦₆₄ 0#64) ∗
       vecU8 A (x.ret + 8#64) (PqRatchetState.encodeRaw (initialStatePB F x.p))) ∗ Rest ⊢
      initialStateResultAt A x.ret (initialStateValue F x.p) ∗ Rest := by
    unfold initialStateResultAt initialStateValue; rw [hv]; exact Entails.refl _
  have hsp496_align : ((s0.sp - 496#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 496#64 hsp0_align (by decide)
  dsimp only [initialStatePlacedProg, initialStatePlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  refine sepWP_rebase_strengthen_vmPreserved hres ?_
  by_vm_steps (
    wp_steps
    refine align_pre_tp (by sep_ac_rfl) ?_
    wp_done
  )

theorem call_dropPqRatchetState_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdrop : subroutine_ok ((blkPC_270).rebase (blkPl_270).base (Rust.withPanics ext))
      (blkPl_270).base (withLsCodeLoaded lsmpl (dropProtoPqRatchetStatePlacedSpec M A lim)))
    {Q : State → SepProp → Prop}
    (s0 s : State) (x : InitialStateGhost) (st_in : M.σ) (Frame R : SepProp)
    (hinv : LsCallInv lsmpl s.mem)
    (hproto_eq : protoPqRatchetStateAt A.repAlloc (s0.sp - 456#64) (initialStatePB F x.p) =
      pqRatchetStatePBAt A.repAlloc (s0.sp - 456#64) (initialStatePB F x.p))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 270)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 496#64)
    (hlr : s.readReg64 .x30 = initialStatePlacedEntry + 396#64)
    (hx0 : s.readReg64 .x0 = s0.sp - 456#64) (htrace : s.trace = s0.trace)
    (hnext : ∀ (sf : State) (evs₄ : List AllocEvent),
      sf.pc = initialStatePlacedEntry + 396#64 →
      sf.status = .Running → sf.sp = s0.sp - 496#64 →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      FreeOnlyEvs evs₄ →
      SepWPp (initialStatePlacedProg ext) (s0.readReg64 .x30) sf
        ((memRegion (s0.sp - 456#64) 352 ∗ optProtoInnerStateJumpTablePlacedAt ∗
          A.pool lim (M.stepEvents evs₄ st_in) sf ∗
          stackAt (s0.sp - 496#64) dropStack96) ∗ Frame)
        Q (InitInnerBudgetPanic R)) :
    SepWPp (initialStatePlacedProg ext) (s0.readReg64 .x30) s
      ((pqRatchetStatePBAt A.repAlloc (s0.sp - 456#64) (initialStatePB F x.p) ∗
        optProtoInnerStateJumpTablePlacedAt ∗
        A.pool lim st_in s ∗ stackAt (s0.sp - 496#64) dropStack96) ∗ Frame)
      Q (InitInnerBudgetPanic R) := by
  have hfsp_align : ((s0.sp - 496#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 496#64 hsp0_align (by decide)
  rw [← hproto_eq]
  have hcall := subroutine_ok_withLsCallInv_of_withLsCodeLoaded
    (initialState_dropPqRatchetState_placed_ok hdrop)
  let gx : DropProtoPqRatchetStateGhost := ⟨s0.sp - 456#64, initialStatePB F x.p⟩
  refine sepWPp_call_total_keepLsInv (gx, st_in) (Frame := Frame)
    hcall hpc hrun (by rw [State.spAligned, hsp]; exact hfsp_align) hlr
    (fun R' hm => by
      dsimp only [withLsCallInv, dropProtoPqRatchetStatePlacedSpec, gx]
      rw [hsp]
      have hlr_ls : LsRetAddr624 (s.readReg64 .lr) := by
        change LsRetAddr624 (s.readReg64 .x30); rw [hlr]
        dsimp only [initialStatePlacedEntry]
        simp (config := { decide := true }) only [arm64_norm, wp_norm]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
      exact ⟨hinv, ⟨hx0, hlr_ls⟩, hm⟩)
    (hnext := fun sf hpc_sf hrun_sf _ _ hsp_sf hcs_sf => ?_)
  dsimp only [withLsCallInv, withLsCodeLoaded, dropProtoPqRatchetStatePlacedSpec,
    protoPqRatchetStateSize, gx]
  rw [hsp, sepExists_sepConj_left]
  refine SepWPp.exists_elim fun evs₄ => ?_
  rw [sepConj_assoc]
  refine SepWPp.pure_left fun ⟨htr, _, hevs₄⟩ => ?_
  have hnext' := hnext sf evs₄ hpc_sf hrun_sf (by rw [hsp_sf, hsp]) hcs_sf
    (by rw [htr, htrace]) hevs₄
  exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hnext'

/-! ## 7. Full V1 Path Composition (`+0 -> ret`) on `Block 327` -/

def InitialStateV1PlacedPost [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (s0 : State) (x : InitialStateGhost) (st0 : M.σ) : State → SepProp → Prop :=
  fun sf Pf =>
    (∃ evs : List AllocEvent,
      InitialStateEnv F x evs ∧
      (Pf ⊢
        statesIntoPbJumpTablePlacedAt ∗ optProtoInnerStateJumpTablePlacedAt ∗
        paramsAt x.pA x.akPtr x.p ∗ (x.akPtr ↦ₛ x.p.authKey) ∗
        initialStateResultAt A.repAlloc x.ret (initialStateValue F x.p) ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim (M.stepEvents evs st0) sf ∗
        stackAt s0.sp initialStateStack)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace

theorem sepWPp_of_initialState_v1_placed_ro_wpp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (s0 : State) (x : InitialStateGhost) (st0 : M.σ) (P R : SepProp)
    (hwpp : SepWPp (initialStatePlacedProg ext) (s0.readReg64 .x30) s0 P
      (InitialStateV1PlacedPost M A lim F s0 x st0) (InitInnerBudgetPanic R)) :
    SepWPp (initialStatePlacedProg ext) (s0.readReg64 .x30) s0 P
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (initialStatePlacedRoSpec M A lim F).post (x, st0) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (initialStatePlacedRoSpec M A lim F).onPanic (x, st0) s0 sf ∗ R)) := by
  intro R' hm hL
  obtain ⟨sf, hsteps,
      ⟨hpcf, hrunf, P_f, hmf, ⟨⟨evs, hevs, hent⟩, hspf, hcsf, htrf⟩⟩ |
      ⟨hpan, P_f, hmf, hqp⟩ | hoom⟩ :=
    hwpp R' hm hL
  · refine ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, P_f, hmf, ⟨?_, hspf, hcsf⟩⟩⟩
    intro hmR
    have hm' := Satisfies.mono (sepConj_mono_left hent) hmR
    dsimp only [initialStatePlacedRoSpec, initialStatePlacedRoSpecOfEnv]
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨htrf, hevs⟩, by simpa only [sepConj_assoc] using hm'⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, P_f, hmf, fun hmR => hqp hmR⟩)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

theorem sepWPp_of_initialState_v1_placed_wpp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (s0 : State) (x : InitialStateGhost) (st0 : M.σ) (P R : SepProp)
    (hwpp : SepWPp (initialStatePlacedProg ext) (s0.readReg64 .x30) s0 P
      (InitialStateV1PlacedPost M A lim F s0 x st0) (InitInnerBudgetPanic R)) :
    SepWPp (initialStatePlacedProg ext) (s0.readReg64 .x30) s0 P
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (initialStatePlacedSpec M A lim F).post (x, st0) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (initialStatePlacedSpec M A lim F).onPanic (x, st0) s0 sf ∗ R)) := by
  intro R' hm hL
  obtain ⟨sf, hsteps,
      ⟨hpcf, hrunf, P_f, hmf, ⟨⟨evs, hevs, hent⟩, hspf, hcsf, htrf⟩⟩ |
      ⟨hpan, P_f, hmf, hqp⟩ | hoom⟩ :=
    hwpp R' hm hL
  · refine ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, P_f, hmf, ⟨?_, hspf, hcsf⟩⟩⟩
    intro hmR
    dsimp only [initialStatePlacedSpec, initialStatePlacedSpecOfEnv]
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨htrf, hevs⟩, ?_⟩
    have hm1 := Satisfies.mono (sepConj_mono_left hent) hmR
    have hm2 : sf.mem ⊨
        (statesIntoPbJumpTablePlacedAt ∗ optProtoInnerStateJumpTablePlacedAt) ∗
        ((paramsAt x.pA x.akPtr x.p ∗ (x.akPtr ↦ₛ x.p.authKey) ∗
          initialStateResultAt A.repAlloc x.ret (initialStateValue F x.p) ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim (M.stepEvents evs st0) sf ∗
          stackAt s0.sp initialStateStack) ∗ R) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm1
    exact Satisfies.of_sep_right hm2
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, P_f, hmf, fun hmR => hqp hmR⟩)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

theorem initial_state_v1_body_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hshim : subroutine_ok (initialStatePlacedProg ext) (lsρ spqrRustNoAllocShimSym)
      noAllocShimBudgetSpec)
    (halloc : subroutine_ok (initialStatePlacedProg ext) (lsρ spqrRustAllocSym)
      (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok (initialStatePlacedProg ext) (lsρ lsMemcpySym)
      framelessMemcpyBudgetSpec)
    (hinit : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (blkPl_324).base (withLsCodeLoaded lsmpl (initInnerPlacedSpecX M A lim F)))
    (henc : PqRatchetStateEncodeToVecPlacedOkExt A lim ext)
    (hdrop : subroutine_ok ((blkPC_270).rebase (blkPl_270).base (Rust.withPanics ext))
      (blkPl_270).base (withLsCodeLoaded lsmpl (dropProtoPqRatchetStatePlacedSpec M A lim)))
    (s0 : State) (x : InitialStateGhost) (st0 : M.σ) (R : SepProp)
    (hinv0 : LsCallInv lsmpl s0.mem)
    (hpc : s0.pc = initialStatePlacedEntry)
    (hrun : s0.status = .Running) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hv : x.p.version = .v1) (hx0 : s0.readReg64 .x0 = x.pA) (hx8 : s0.readReg64 .x8 = x.ret)
    (hak_ne : x.akPtr ≠ 0#64) (hlen : x.p.authKey.length < 2 ^ 32)
    (hfit : FitsEnv M lim st0 (InitialStateEnv F x))
    (hlen_pb : (PqRatchetState.encodeRaw (initialStatePB F x.p)).length < 2 ^ 63)
    (hproto_eq : protoPqRatchetStateAt A.repAlloc (s0.sp - 456#64) (initialStatePB F x.p) =
      pqRatchetStatePBAt A.repAlloc (s0.sp - 456#64) (initialStatePB F x.p))
    (hpbAt : ∀ ptr : BitVec 64,
      (vecU8At A.repAlloc (s0.sp - 456#64) (BitVec.ofNat 64 x.p.authKey.length) ptr x.p.authKey ∗
        (((s0.sp - 456#64) + 0x18#64) ↦₃₂ 1#32) ∗
        (((s0.sp - 456#64) + 0x1c#64) ↦₃₂ x.p.chainParams.intoPb.maxJump) ∗
        (((s0.sp - 456#64) + 0x20#64) ↦₃₂ x.p.chainParams.intoPb.maxOooKeys) ∗
        (((s0.sp - 456#64) + 0x24#64) ↦₃₂ x.p.direction.toI32) ∗
        (((s0.sp - 456#64) + 0x28#64) ↦₃₂ x.p.minVersion.toI32) ∗
        memRegion ((s0.sp - 456#64) + 0x2c#64) 4 ∗
        (((s0.sp - 456#64) + 0x30#64) ↦₆₄ noneCap) ∗
        memRegion ((s0.sp - 456#64) + 0x38#64) 72 ∗
        initInnerResultAt A.repAlloc (F := F) ((s0.sp - 456#64) + 0x80#64)
          .v1 x.p.direction x.p.authKey) ⊢
      pqRatchetStatePBAt A.repAlloc (s0.sp - 456#64) (initialStatePB F x.p)) :
    SepWPp (initialStatePlacedProg ext) (s0.readReg64 .x30) s0
      (statesIntoPbJumpTablePlacedAt ∗ optProtoInnerStateJumpTablePlacedAt ∗
       paramsAt x.pA x.akPtr x.p ∗ (x.akPtr ↦ₛ x.p.authKey) ∗ memRegion x.ret 32 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st0 s0 ∗ stackAt s0.sp initialStateStack)
      (InitialStateV1PlacedPost M A lim F s0 x st0)
      (InitInnerBudgetPanic R) := by
  have hlt63 : x.p.authKey.length < 2 ^ 63 := by omega
  have hlt32_63 : 32 + x.p.authKey.length < 2 ^ 63 := by omega
  refine SepWPp.weaken_pre (P' :=
      cells (s0.sp - 96#64) 12 ∗ paramsAt x.pA x.akPtr x.p ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
      ((x.akPtr ↦ₛ x.p.authKey) ∗ A.pool lim st0 s0 ∗ stackAt (s0.sp - 496#64) initInnerStack ∗
       memRegion (s0.sp - 496#64) 40 ∗ memRegion (s0.sp - 456#64) 352 ∗ memRegion (s0.sp - 104#64) 8 ∗
       memRegion x.ret 32 ∗ statesIntoPbJumpTablePlacedAt ∗ optProtoInnerStateJumpTablePlacedAt))
    (by rw [h61s_stackAt_initialState_split s0.sp]; exact Entails.of_eq (by sep_ac_rfl)) ?_
  refine initInner_seq_sepWP_lsInv
    (initial_state_prologue_v1_placed s0 x _ hsp0_align hpc hrun hx0 hx8 hv hlen) ?_
  intro s1 hpc1 hrun1 _ hinv1
    ⟨hvm1, hsp1, hx29_1, hx19_1, hx20_1, hx21_1, hx22_1, hw25_1, htr1, hvregs1⟩
  refine SepWPp.weaken_pre (P' :=
      (x.akPtr ↦ₛ x.p.authKey) ∗ A.pool lim st0 s1 ∗ stackAt (s0.sp - 496#64) allocHookStack ∗
      (memRegion ((s0.sp - 496#64) - 17680#64) 13584 ∗ paramsAt x.pA x.akPtr x.p ∗
       h61s_initialStateSavedCells s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       memRegion (s0.sp - 496#64) 40 ∗ memRegion (s0.sp - 456#64) 352 ∗ memRegion (s0.sp - 104#64) 8 ∗
       memRegion x.ret 32 ∗ statesIntoPbJumpTablePlacedAt ∗ optProtoInnerStateJumpTablePlacedAt))
    (by
      rw [stackAt_initInner_split_allocHook (s0.sp - 496#64), ← A.pool_of_vmPreserved hvm1]
      exact Entails.of_eq (by sep_ac_rfl)) ?_
  refine initial_state_to_vec_placed hshim halloc hmemcpy s0 s1 x st0 _ R
    hsp0_align hlt63 hv hfit
    hpc1 hrun1 hsp1 hx29_1 hx19_1 hx20_1 hx21_1 hx22_1 hw25_1 htr1 hvregs1 ?_
  intro s2 ptr hpc2 hrun2 hinv2 hsp2 hx29_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hw25_2 htr2 hvregs2
  let st1 := M.stepEvents (cloneEvs x.p.authKey) st0
  refine SepWPp.weaken_pre (P' :=
      paramsAt x.pA x.akPtr x.p ∗
      (memRegion (s0.sp - 456#64) 352 ∗ (x.akPtr ↦ₛ x.p.authKey) ∗
       statesIntoPbJumpTablePlacedAt ∗ A.pool lim st1 s2 ∗
       stackAt (s0.sp - 496#64) initInnerStack ∗
       vecU8Buf A.repAlloc (BitVec.ofNat 64 x.p.authKey.length) ptr x.p.authKey ∗
       h61s_initialStateSavedCells s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       memRegion (s0.sp - 496#64) 40 ∗ memRegion (s0.sp - 104#64) 8 ∗
       memRegion x.ret 32 ∗ optProtoInnerStateJumpTablePlacedAt))
    (by rw [stackAt_initInner_split_allocHook (s0.sp - 496#64)]; exact Entails.of_eq (by sep_ac_rfl)) ?_
  refine initInner_seq_sepWP_lsInv
    (initial_state_pre_init_inner_placed s0 s2 x ptr _ hsp0_align
      hpc2 hrun2 hsp2 hx29_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hw25_2 htr2 hvregs2) ?_
  intro s3 hpc3 hrun3 _ hinv3
    ⟨hvm3, hsp3, hlr3, hx0_3, hw1_3, hw2_3, hx3_3, hx4_3, hx29_3, hx19_3, hw20_3, hx21_3, hx23_3,
     hw24_3, hw25_3, hw26_3, hw27_3, htr3, hvregs3⟩
  refine SepWPp.weaken_pre (P' :=
      (memRegion ((s0.sp - 456#64) + 0x80#64) optProtoInnerStateSize ∗
       (x.akPtr ↦ₛ x.p.authKey) ∗ statesIntoPbJumpTablePlacedAt ∗
       A.pool lim st1 s3 ∗ stackAt (s0.sp - 496#64) initInnerStack) ∗
      (cells (s0.sp - 456#64) 3 ∗
       (∃∗ v0 : BitVec 32, ((s0.sp - 456#64) + 0x18#64) ↦₃₂ v0) ∗
       (∃∗ v1 : BitVec 32, ((s0.sp - 456#64) + 0x1c#64) ↦₃₂ v1) ∗
       (∃∗ v2 : BitVec 32, ((s0.sp - 456#64) + 0x20#64) ↦₃₂ v2) ∗
       (∃∗ v3 : BitVec 32, ((s0.sp - 456#64) + 0x24#64) ↦₃₂ v3) ∗
       (∃∗ v4 : BitVec 32, ((s0.sp - 456#64) + 0x28#64) ↦₃₂ v4) ∗
       memRegion ((s0.sp - 456#64) + 0x2c#64) 4 ∗
       (∃∗ w6 : BitVec 64, ((s0.sp - 456#64) + 0x30#64) ↦₆₄ w6) ∗
       memRegion ((s0.sp - 456#64) + 0x38#64) 72 ∗
       vecU8Buf A.repAlloc (BitVec.ofNat 64 x.p.authKey.length) ptr x.p.authKey ∗
       paramsAt x.pA x.akPtr x.p ∗ h61s_initialStateSavedCells s0 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ memRegion (s0.sp - 496#64) 40 ∗
       memRegion (s0.sp - 104#64) 8 ∗ memRegion x.ret 32 ∗ optProtoInnerStateJumpTablePlacedAt))
    (by
      rw [memRegion_pqState_split (s0.sp - 456#64), ← A.pool_of_vmPreserved hvm3]
      exact Entails.of_eq (by sep_ac_rfl)) ?_
  have hinv_s3 : LsCallInv lsmpl s3.mem := hinv3 (hinv2 (hinv1 hinv0))
  have hfit_init := fitsEnv_initInner_of_initialStateEnv ((s0.sp - 456#64) + 0x80#64) hv hfit
  refine call_initInner_placed_x hinit s0 s3 x st1 _ R hinv_s3 hsp0_align hak_ne hlt32_63 hfit_init
    hpc3 hrun3 hsp3 hlr3 hx0_3 hw1_3 hw2_3 hx3_3 hx4_3 htr3 ?_
  intro s4 evs₂ hpc4 hrun4 hinv4 hsp4 hcs4 htr4 hevs₂
  let st2 := M.stepEvents evs₂ st1
  obtain ⟨hx19_4, hx20_4, hx21_4, _, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, _, hx29_4⟩ := hcs4
  refine SepWPp.weaken_pre (P' :=
      cells (s0.sp - 456#64) 3 ∗
      (∃∗ v0 : BitVec 32, ((s0.sp - 456#64) + 0x18#64) ↦₃₂ v0) ∗
      (∃∗ v1 : BitVec 32, ((s0.sp - 456#64) + 0x1c#64) ↦₃₂ v1) ∗
      (∃∗ v2 : BitVec 32, ((s0.sp - 456#64) + 0x20#64) ↦₃₂ v2) ∗
      (∃∗ v3 : BitVec 32, ((s0.sp - 456#64) + 0x24#64) ↦₃₂ v3) ∗
      (∃∗ v4 : BitVec 32, ((s0.sp - 456#64) + 0x28#64) ↦₃₂ v4) ∗
      memRegion ((s0.sp - 456#64) + 0x2c#64) 4 ∗
      (∃∗ w6 : BitVec 64, ((s0.sp - 456#64) + 0x30#64) ↦₆₄ w6) ∗
      memRegion ((s0.sp - 456#64) + 0x38#64) 72 ∗
      initInnerResultAt A.repAlloc (F := F) ((s0.sp - 456#64) + 0x80#64) .v1 x.p.direction x.p.authKey ∗
      vecU8Buf A.repAlloc (BitVec.ofNat 64 x.p.authKey.length) ptr x.p.authKey ∗
      (memRegion x.ret 32 ∗ A.pool lim st2 s4 ∗ stackAt (s0.sp - 496#64) initInnerStack ∗
       (x.akPtr ↦ₛ x.p.authKey) ∗ paramsAt x.pA x.akPtr x.p ∗ h61s_initialStateSavedCells s0 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ memRegion (s0.sp - 496#64) 40 ∗
       memRegion (s0.sp - 104#64) 8 ∗ statesIntoPbJumpTablePlacedAt ∗
       optProtoInnerStateJumpTablePlacedAt))
    (Entails.of_eq (by sep_ac_rfl)) ?_
  refine initInner_seq_sepWP_lsInv
    (initial_state_pre_encode_to_vec_placed s0 s4 x ptr _ (hpbAt ptr) hsp0_align
      hpc4 hrun4 hsp4
      (hx29_4.1.trans hx29_3) (hx19_4.trans hx19_3)
      ((readReg32_of_eq hx20_4).trans hw20_3)
      (hx21_4.trans hx21_3) (hx23_4.trans hx23_3)
      ((readReg32_of_eq hx24_4).trans hw24_3)
      ((readReg32_of_eq hx25_4).trans hw25_3)
      ((readReg32_of_eq hx26_4).trans hw26_3)
      ((readReg32_of_eq hx27_4).trans hw27_3) htr4 (hx29_4.2.trans hvregs3)) ?_
  intro s5 hpc5 hrun5 _ hinv5 ⟨hvm5, hsp5, hlr5, hx0_5, hx1_5, hx29_5, hx19_5, htr5, hvregs5⟩
  refine SepWPp.weaken_pre (P' :=
      ∃∗ r0 : BitVec 64,
        (memRegion (x.ret + 8#64) 24 ∗
         pqRatchetStatePBAt A.repAlloc (s0.sp - 456#64) (initialStatePB F x.p) ∗
         A.pool lim st2 s5 ∗ stackAt (s0.sp - 496#64) encodeToVecStackX) ∗
        ((x.ret ↦₆₄ r0) ∗
         memRegion ((s0.sp - 496#64) - 17680#64) (initInnerStack - encodeToVecStackX) ∗
         (x.akPtr ↦ₛ x.p.authKey) ∗ paramsAt x.pA x.akPtr x.p ∗ h61s_initialStateSavedCells s0 ∗
         (lsLogFilterAddr ↦₆₄ 0#64) ∗ memRegion (s0.sp - 496#64) 40 ∗
         memRegion (s0.sp - 104#64) 8 ∗ statesIntoPbJumpTablePlacedAt ∗
         optProtoInnerStateJumpTablePlacedAt))
    (by
      rw [memRegion_ret_32_split x.ret, stackAt_initInner_split_encodeToVec (s0.sp - 496#64),
          ← A.pool_of_vmPreserved hvm5]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply Entails.sepExists_elim; intro r0
      exact Entails.sepExists_right r0 (Entails.of_eq (by sep_ac_rfl))) ?_
  refine SepWPp.exists_elim fun r0 => ?_
  have hinv_s5 : LsCallInv lsmpl s5.mem := hinv5 hinv4
  have hfit_enc := fitsEnv_encodeToVec_of_initialStateEnv hv hfit hevs₂
  refine call_encodeToVec_placed_x henc s0 s5 x st2 _ R hinv_s5 hsp0_align hlen_pb hfit_enc
    hpc5 hrun5 hsp5 hlr5 hx0_5 hx1_5 htr5 ?_
  intro s6 evs₃ hpc6 hrun6 hinv6 hsp6 hcs6 htr6 hevs₃
  let st3 := M.stepEvents evs₃ st2
  obtain ⟨hx19_6, _, _, _, _, _, _, _, _, _, hx29_6⟩ := hcs6
  refine SepWPp.weaken_pre (P' :=
      (x.ret ↦₆₄ r0) ∗ vecU8 A.repAlloc (x.ret + 8#64) (PqRatchetState.encodeRaw (initialStatePB F x.p)) ∗
      (pqRatchetStatePBAt A.repAlloc (s0.sp - 456#64) (initialStatePB F x.p) ∗
       optProtoInnerStateJumpTablePlacedAt ∗ A.pool lim st3 s6 ∗
       stackAt (s0.sp - 496#64) initInnerStack ∗
       (x.akPtr ↦ₛ x.p.authKey) ∗ paramsAt x.pA x.akPtr x.p ∗ h61s_initialStateSavedCells s0 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ memRegion (s0.sp - 496#64) 40 ∗
       memRegion (s0.sp - 104#64) 8 ∗ statesIntoPbJumpTablePlacedAt))
    (by rw [stackAt_initInner_split_encodeToVec (s0.sp - 496#64)]; exact Entails.of_eq (by sep_ac_rfl)) ?_
  refine initInner_seq_sepWP_lsInv
    (initial_state_pre_drop_placed s0 s6 x r0 _ hv hsp0_align
      hpc6 hrun6 hsp6 (hx29_6.1.trans hx29_5) (hx19_6.trans hx19_5) htr6 (hx29_6.2.trans hvregs5)) ?_
  intro s7 hpc7 hrun7 _ hinv7 ⟨hvm7, hsp7, hlr7, hx0_7, hx29_7, htr7, hvregs7⟩
  refine SepWPp.weaken_pre (P' :=
      (pqRatchetStatePBAt A.repAlloc (s0.sp - 456#64) (initialStatePB F x.p) ∗
       optProtoInnerStateJumpTablePlacedAt ∗ A.pool lim st3 s7 ∗
       stackAt (s0.sp - 496#64) dropStack96) ∗
      (memRegion ((s0.sp - 496#64) - 17680#64) 13488 ∗
       initialStateResultAt A.repAlloc x.ret (initialStateValue F x.p) ∗
       (x.akPtr ↦ₛ x.p.authKey) ∗ paramsAt x.pA x.akPtr x.p ∗ h61s_initialStateSavedCells s0 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ memRegion (s0.sp - 496#64) 40 ∗
       memRegion (s0.sp - 104#64) 8 ∗ statesIntoPbJumpTablePlacedAt))
    (by
      rw [stackAt_initInner_split_dropStack96 (s0.sp - 496#64), ← A.pool_of_vmPreserved hvm7]
      exact Entails.of_eq (by sep_ac_rfl)) ?_
  have hinv_s7 : LsCallInv lsmpl s7.mem := hinv7 hinv6
  refine call_dropPqRatchetState_placed hdrop s0 s7 x st3 _ R hinv_s7 hproto_eq hsp0_align
    hpc7 hrun7 hsp7 hlr7 hx0_7 htr7 ?_
  intro s8 evs₄ hpc8 hrun8 hsp8 hcs8 htr8 hevs₄
  let st4 := M.stepEvents evs₄ st3
  refine SepWPp.weaken_pre (P' :=
      stackAt (s0.sp - 496#64) initInnerStack ∗ memRegion (s0.sp - 496#64) 40 ∗
      memRegion (s0.sp - 456#64) 352 ∗ memRegion (s0.sp - 104#64) 8 ∗
      h61s_initialStateSavedCells s0 ∗
      (statesIntoPbJumpTablePlacedAt ∗ optProtoInnerStateJumpTablePlacedAt ∗
       paramsAt x.pA x.akPtr x.p ∗ (x.akPtr ↦ₛ x.p.authKey) ∗
       initialStateResultAt A.repAlloc x.ret (initialStateValue F x.p) ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st4 s8))
    (by rw [stackAt_initInner_split_dropStack96 (s0.sp - 496#64)]; exact Entails.of_eq (by sep_ac_rfl)) ?_
  refine initInner_seq_sepWP_lsInv
    (initial_state_epilogue_placed s0 s8 _ hsp0_align hpc8 hrun8 hsp8 htr8
      (hcs8.2.2.2.2.2.2.2.2.2.2.2.trans hvregs7)) ?_
  intro sf hpcf hrunf _ _ ⟨hvmf, hspf, hcsf, htrf⟩
  let evs := ((cloneEvs x.p.authKey ++ evs₂) ++ evs₃) ++ evs₄
  have hevs : InitialStateEnv F x evs :=
    initialStateEnv_v1_of_stages hv hfit hevs₂ hevs₃ hevs₄
  have hst_eq : st4 = M.stepEvents evs st0 := by
    dsimp only [st4, st3, st2, st1, evs]
    simp only [M.stepEvents_append]
  refine SepWPp.done hpcf hrunf ⟨⟨evs, hevs, ?_⟩, hspf, hcsf, htrf⟩
  rw [hst_eq, A.pool_of_vmPreserved hvmf]
  exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.SpqrV1.Top.InitialState.StepsPlacedBudget
