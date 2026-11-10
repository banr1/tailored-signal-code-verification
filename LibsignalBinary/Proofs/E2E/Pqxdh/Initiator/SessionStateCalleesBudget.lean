/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SessionStateCallees
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.GenLsBlock
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPFrozen
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr

/-!
# Budget-Threaded Relocatable Contracts for `SessionState` and Serialization Callees

Proves `[LibsignalPlacement]` contracts under `RustCliAllocBudget M` for `<PrivateKey>::serialize`
(Block `208`), `<PublicKey>::serialize` (Block `205`), `<RawVecInner>::finish_grow [local#1]`
(Block `45`), `<RawVec<Chain>>::grow_one` (Block `43`), `<SessionState>::new` (Block `37`),
`<SessionState>::with_sender_chain` (Block `27`), `<SessionState>::with_receiver_chain` (Block `30`),
and `<SessionState>::set_unacknowledged_pre_key_message` (Block `33`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SessionStateCalleesBudget

open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (
  IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
  libsignalMutatedBlocks libsignalSessionLib
  lsMemcpySym lsRustAllocSym lsRustDeallocSym lsRustNoAllocShimSym
  ls_hook_ok_of_mem ls_subroutine_ok_cl_of_block ls_subroutine_ok_cl_of_plain
  ls_subroutine_ok_of_block lsmpl lsρ sepWP_seq_lscl
  subroutine_ok_withLsCodeLoaded_of_plain withLsCl withLsCodeLoaded
)
open CryptoVerification.RustHeap (allocHookStack)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec
  subroutine_ok_sessionMemcpyRegionBudget_of_allocMemcpyVm
  subroutine_ok_sessionShimBudget_of_rustAllocShimVm
)
open CryptoVerification.E2E.Pqxdh.Initiator (
  Bytes CryptoLeafCall FinishGrowGhost SessionStateNewGhost
  WithReceiverChainGhost WithSenderChainGhost
  blkLib_eq_27 blkLib_eq_30 blkLib_eq_33 blkLib_eq_37 blkLib_eq_43 blkLib_eq_45
  blkLib_eq_205 blkLib_eq_208
  blkPC_27 blkPl_27 blkPC_30 blkPl_30 blkPC_33 blkPl_33 blkPC_37 blkPl_37
  blkPC_43 blkPl_43 blkPC_45 blkPl_45 blkPC_205 blkPl_205 blkPC_208 blkPl_208
  bv_sub_add_lit' bytesToBv8 cryptoLeafStubSpec encodeEC fitBv8
  lsSystemTimeDurationSinceSym pqxdhHookStack
  readReg32_setMem_setPC_pre readReg32_setPC_pre
  readReg64_setMem_setPC_pre readReg64_setPC_pre
  readReg_setMem_setPC_pre readReg_setPC_pre
  receiverChainElemAt receiverChainVecBytes24 receiverChainVecBytes24_length
  receiverChainVecFieldsAt senderChainBytes100 senderChainBytes100_length
  senderChainFieldsAt sp_setMem_setPC_pre sp_setPC_pre stackAt_split_top vecU8
  withReceiverChain_pack344 withReceiverChain_pack344_unfolded
  withSenderChain_pack344 withSenderChain_pack344_unfolded
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEvent FitsEvents RustCliAllocBudget VmPreserved
  fitsEvents_append rustAllocEvents rustCliAllocBudgetSpec
  rustCliAllocNoOomExternSpecWithStack rustCliDeallocBudgetSpec rustDeallocEvents
  subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  subroutine_ok_rustCliAllocNoOom_externWithStack
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (
  allocMemcpyVmSpec rustAllocShimVmSpec
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff FitsEvent
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

local macro "cells_unfold_fast" : tactic =>
  `(tactic| simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_right, bv_sub_add_lit', BitVec.add_assoc,
      BitVec.reduceAdd, BitVec.reduceSub])

local macro "cells_pre_unfold_fast" : tactic =>
  `(tactic| (
    conv => arg 4; simp (config := { maxSteps := 1000000 }) only [
      cells, sepConj_emp, sepExists_sepConj_right, bv_sub_add_lit', BitVec.add_assoc,
        BitVec.reduceAdd, BitVec.reduceSub]))

@[local simp, local wp_norm, local arm64_norm]
private theorem bytesToBv8_length (bs : Bytes) : (bytesToBv8 bs).length = bs.length :=
  List.length_map _

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

/-! ## 1. `rustDeallocBytesSpec` & `dealloc_bytes_placed_ok` -/

def rustDeallocBytesSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec ((BitVec 64 × List (BitVec 8) × Nat × Nat) × M.σ) where
  pre := fun ((p, bs, n, align), st) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = n ∧ (s.readReg64 .x2).toNat = align ∧
      bs.length = n ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      A.pool lim st s ∗ A.live p n align ∗ (p ↦ₛ bs) ∗ stackAt s.sp allocHookStack
  post := fun ((_, _, n, align), st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      A.pool lim (M.stepEvents (rustDeallocEvents n align) st) sf ∗ stackAt s0.sp allocHookStack

theorem dealloc_bytes_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {prog : Program}
    {H : LibsignalHooks} {i : Nat} [IsLsBlockProg prog i H]
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ lsRustDeallocSym) (rustDeallocBytesSpec M A lim) := by
  have hd : subroutine_ok prog (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) :=
    ls_hook_ok_of_mem hdealloc (by decide) hi hunmut
  apply subroutine_ok_outcome_intro
  intro ⟨⟨p, bs, n, align⟩, st⟩ R s0 hpc hrun hpre hsp
  have hpre' : s0.mem ⊨ (rustCliDeallocBudgetSpec M A lim).pre (p, n, align, st) s0 ∗ R := by
    unfold rustDeallocBytesSpec at hpre
    unfold rustCliDeallocBudgetSpec
    dsimp only at hpre ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hlen, hlr⟩, hpre⟩
    refine ⟨⟨hx0, hx1, hx2, hlr⟩, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc] at hpre ⊢
    refine Satisfies.mono ?_ hpre
    rw [← hlen]
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
      (pointsToBytes_entails_memRegion p bs)))
  refine (hd.to_outcome (p, n, align, st) R s0 hpc hrun hpre' hsp).mono_outcome ?_
  rintro sf (⟨hret, hcs, hpost⟩ | hrest)
  · left
    refine ⟨hret, hcs, ?_⟩
    unfold rustCliDeallocBudgetSpec at hpost
    unfold rustDeallocBytesSpec
    dsimp only at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨hacp, _⟩, hpost⟩
    exact ⟨hacp.2.1, hpost⟩
  · exact Or.inr hrest

/-! ## 2. `<PrivateKey>::serialize` (Block `208`) -/

private theorem stackAt_privKeySerialize (sp : BitVec 64) :
    memRegion (sp - 4128#64) 32 ∗ stackAt sp allocHookStack =
      stackAt (sp - 32#64) allocHookStack ∗ cells (sp - 32#64) 4 := by
  have h1 := stackAt_split_top sp 32 allocHookStack (by decide)
  have h2 := stackAt_split_cells sp allocHookStack 4 (by decide)
  have h3 : (32 + allocHookStack : Nat) = allocHookStack + 8 * 4 := by decide
  have h4 : BitVec.ofNat 64 (32 + allocHookStack) = 4128#64 := rfl
  have h5 : BitVec.ofNat 64 (8 * 4) = 32#64 := rfl
  rw [h4] at h1
  rw [h5] at h2
  rw [← h1, h3, h2]

def privKeySerializePlacedEvents : List AllocEvent :=
  rustAllocEvents 32 1

def PrivKeySerializePlacedEnv (evs : List AllocEvent) : Prop :=
  evs = privKeySerializePlacedEvents

def privKeySerializePlacedSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec ((BitVec 64 × List (BitVec 8) × BitVec 64) × M.σ) where
  pre := fun ((privKeyPtr, sk, outVecPtr), st) s =>
    ⌜s.readReg64 .x0 = privKeyPtr ∧ s.readReg64 .x8 = outVecPtr ∧ sk.length = 32 ∧
      FitsEvents M lim st privKeySerializePlacedEvents⌝ ∗
      (privKeyPtr ↦ₛ sk) ∗ cells outVecPtr 3 ∗
      (memRegion (s.sp - 4128#64) 32 ∗ stackAt s.sp allocHookStack) ∗ A.pool lim st s
  post := fun ((privKeyPtr, sk, outVecPtr), st) s0 sf =>
    ∃∗ bufPtr : BitVec 64,
      ⌜sf.trace = s0.trace ∧ bufPtr ≠ 0⌝ ∗ (privKeyPtr ↦ₛ sk) ∗
      (outVecPtr ↦₆₄ 32#64) ∗ ((outVecPtr + 8#64) ↦₆₄ bufPtr) ∗ ((outVecPtr + 16#64) ↦₆₄ 32#64) ∗
      (bufPtr ↦ₛ sk) ∗ A.live bufPtr 32 1 ∗
      (memRegion (s0.sp - 4128#64) 32 ∗ stackAt s0.sp allocHookStack) ∗
      A.pool lim (M.stepEvents privKeySerializePlacedEvents st) sf

theorem privKeySerialize_placed_ok_of_session [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_208).rebase (blkPl_208).base H) (blkPl_208).base
      (privKeySerializePlacedSpec M A lim) := by
  unfold privKeySerializePlacedSpec privKeySerializePlacedEvents
  simp only [stackAt_privKeySerialize]
  cells_unfold_fast
  have hshim' : subroutine_ok ((blkPC_208).rebase (blkPl_208).base H)
      (lsρ lsRustNoAllocShimSym) sessionShimBudgetSpec := ls_hook_ok_of_mem hshim
  have halloc0 : subroutine_ok ((blkPC_208).rebase (blkPl_208).base H)
      (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false) := ls_hook_ok_of_mem halloc
  have halloc' : subroutine_ok ((blkPC_208).rebase (blkPl_208).base H)
      (lsρ lsRustAllocSym) (rustCliAllocNoOomExternSpecWithStack M A lim false allocHookStack) :=
    subroutine_ok_rustCliAllocNoOom_externWithStack (stk := allocHookStack)
      (by decide) (by decide) (subroutine_ok_allocNoOom_of_budget halloc0)
  dsimp only [sessionShimBudgetSpec, CryptoVerification.LibsignalTripleRatchet.sessionShimSpec] at hshim'
  dsimp only [rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomSpecWithStack,
    LibsignalBinary.Heap.RustLayoutOk, CryptoVerification.RustHeap.LayoutOk, ↓reduceIte] at halloc'
  wp_init g s0
  rcases g with ⟨⟨privKeyPtr, sk, outVecPtr⟩, st⟩
  dsimp only at *
  subst ‹s0.readReg64 .x0 = privKeyPtr› ‹s0.readReg64 .x8 = outVecPtr›
  obtain ⟨w0, w1, w2, w3, _, hsk_cells⟩ := exists_unpack64_of_length_32 ‹sk.length = 32›
  have hfe_raw : FitsEvent M lim st (.alloc 32) :=
    (by simpa [rustAllocEvents] using ‹FitsEvents M lim st (rustAllocEvents 32 1)› :
      FitsEvents M lim st [.alloc 32]).1
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hpos : 0 < (32 : Nat) := by decide
  have hal : (1 : Nat) ≤ 2 ^ 31 := by decide
  have hsum : (32 : Nat) + 1 ≤ 2 ^ 63 := by decide
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_call hshim' ()
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc' (32, 1, st)
  have hne : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne
  have hm32 : memRegion (sf_1.readReg64 (Reg.gpr 0#5)) 32 =
      cells (sf_1.readReg64 (Reg.gpr 0#5)) 4 :=
    memRegion_cells (sf_1.readReg64 (Reg.gpr 0#5)) 4 (by decide)
  simp only [hm32, cells, sepConj_emp, sepExists_sepConj_left,
    sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWP.exists_elim fun u0 => SepWP.exists_elim fun u1 =>
    SepWP.exists_elim fun u2 => SepWP.exists_elim fun u3 => ?_
  rw [hsk_cells (s0.readReg64 (Reg.gpr 0#5))]
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  simp only [State.setMem_setMem, hsk_cells, sepConj_assoc]
  wp_done

theorem privKeySerialize_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_208).rebase (blkPl_208).base H) (blkPl_208).base
      (privKeySerializePlacedSpec M A lim) :=
  privKeySerialize_placed_ok_of_session (hookSat_sessionShimBudget_of_rustAllocShimVm hshim) halloc

/-! ## 3. `<PublicKey>::serialize` Allocating Variant (Block `205`) -/

private theorem memRegion_33_cells_alloc (a : BitVec 64) :
    memRegion a 33 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64, ∃∗ b0 : BitVec 8,
        (a ↦₈ b0) ∗ ((a + 1#64) ↦₆₄ u3) ∗ ((a + 9#64) ↦₆₄ u2) ∗ ((a + 17#64) ↦₆₄ u1) ∗ ((a +
        25#64) ↦₆₄ u0)) := by
  rw [memRegion_split a 1 32 (by decide), memRegion_split (a + 1#64) 8 24 (by decide),
    memRegion_split (a + 1#64 + 8#64) 8 16 (by decide),
    memRegion_split (a + 1#64 + 8#64 + 8#64) 8 8 (by decide), memRegion_one, memRegion_eight,
      memRegion_eight, memRegion_eight, memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem bytesToBv8_encodeEC_alloc (bs : Bytes) :
    bytesToBv8 (encodeEC bs) = 5#8 :: bytesToBv8 bs := rfl

def ecPubKeySerializeAllocEvents : List AllocEvent :=
  rustAllocEvents 33 1

def EcPubKeySerializeAllocEnv (evs : List AllocEvent) : Prop :=
  evs = ecPubKeySerializeAllocEvents

def ecPubKeySerializeAllocPlacedSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec ((BitVec 64 × Bytes) × M.σ) where
  pre := fun ((keyPtr, keyBytes), st) s =>
    ⌜s.readReg64 .x0 = keyPtr ∧ keyBytes.length = 32 ∧
      FitsEvents M lim st ecPubKeySerializeAllocEvents⌝ ∗
      (keyPtr ↦ₛ bytesToBv8 keyBytes) ∗
      (memRegion (s.sp - 4128#64) 32 ∗ stackAt s.sp allocHookStack) ∗ A.pool lim st s
  post := fun ((keyPtr, keyBytes), st) s0 sf =>
    ∃∗ slicePtr : BitVec 64,
      ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = slicePtr ∧ sf.readReg64 .x1 = 33#64 ∧
        slicePtr ≠ 0⌝ ∗
      (keyPtr ↦ₛ bytesToBv8 keyBytes) ∗ (slicePtr ↦ₛ bytesToBv8 (encodeEC keyBytes)) ∗
      A.live slicePtr 33 1 ∗
      (memRegion (s0.sp - 4128#64) 32 ∗ stackAt s0.sp allocHookStack) ∗
      A.pool lim (M.stepEvents ecPubKeySerializeAllocEvents st) sf

theorem ecPubKeySerialize_alloc_placed_ok_of_session [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_205).rebase (blkPl_205).base H) (blkPl_205).base
      (ecPubKeySerializeAllocPlacedSpec M A lim) := by
  unfold ecPubKeySerializeAllocPlacedSpec ecPubKeySerializeAllocEvents
  simp only [bytesToBv8_encodeEC_alloc, stackAt_privKeySerialize]
  cells_unfold_fast
  have hshim' : subroutine_ok ((blkPC_205).rebase (blkPl_205).base H)
      (lsρ lsRustNoAllocShimSym) sessionShimBudgetSpec := ls_hook_ok_of_mem hshim
  have halloc0 : subroutine_ok ((blkPC_205).rebase (blkPl_205).base H)
      (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false) := ls_hook_ok_of_mem halloc
  have halloc' : subroutine_ok ((blkPC_205).rebase (blkPl_205).base H)
      (lsρ lsRustAllocSym) (rustCliAllocNoOomExternSpecWithStack M A lim false allocHookStack) :=
    subroutine_ok_rustCliAllocNoOom_externWithStack (stk := allocHookStack)
      (by decide) (by decide) (subroutine_ok_allocNoOom_of_budget halloc0)
  dsimp only [sessionShimBudgetSpec, CryptoVerification.LibsignalTripleRatchet.sessionShimSpec] at hshim'
  dsimp only [rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomSpecWithStack,
    LibsignalBinary.Heap.RustLayoutOk, CryptoVerification.RustHeap.LayoutOk, ↓reduceIte] at halloc'
  wp_init g s0
  rcases g with ⟨⟨keyPtr, keyBytes⟩, st⟩
  dsimp only at *
  subst ‹s0.readReg64 .x0 = keyPtr›
  have hlen_bv : (bytesToBv8 keyBytes).length = 32 := by
    simp [bytesToBv8, ‹keyBytes.length = 32›]
  obtain ⟨w0, w1, w2, w3, _, hpk_cells⟩ := exists_unpack64_of_length_32 hlen_bv
  rw [hpk_cells (s0.readReg64 (Reg.gpr 0#5))]
  have hfe_raw : FitsEvent M lim st (.alloc 33) :=
    (by simpa [rustAllocEvents] using ‹FitsEvents M lim st (rustAllocEvents 33 1)› :
      FitsEvents M lim st [.alloc 33]).1
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hpos : 0 < (33 : Nat) := by decide
  have hal : (1 : Nat) ≤ 2 ^ 31 := by decide
  have hsum : (33 : Nat) + 1 ≤ 2 ^ 63 := by decide
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_call hshim' ()
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc' (33, 1, st)
  have hne : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne
  simp only [memRegion_33_cells_alloc, sepExists_sepConj_left,
    sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun u0 => SepWP.exists_elim fun u1 =>
    SepWP.exists_elim fun u2 => SepWP.exists_elim fun u3 =>
    SepWP.exists_elim fun b0 => ?_
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  simp only [State.setMem_setMem, pointsToBytes_cons, hpk_cells, BitVec.add_assoc, BitVec.reduceAdd,
    sepConj_assoc]
  wp_done

theorem ecPubKeySerialize_alloc_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_205).rebase (blkPl_205).base H) (blkPl_205).base
      (ecPubKeySerializeAllocPlacedSpec M A lim) :=
  ecPubKeySerialize_alloc_placed_ok_of_session
    (hookSat_sessionShimBudget_of_rustAllocShimVm hshim) halloc

/-! ## 4. `<RawVecInner>::finish_grow [local#1]` (Block `45`) -/

private theorem umulh_104_eq_zero {new : BitVec 64} (h : new.toNat * 104 ≤ 9223372036854775800) :
    BitVec.truncate 64 ((104#128 * BitVec.zeroExtend 128 new) >>> 64) = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_mul, BitVec.toNat_setWidth]
  have h1 : (104#128 : BitVec 128).toNat = 104 := rfl
  have h2 : new.toNat < 2 ^ 128 := by omega
  have h3 : 104 * new.toNat < 2 ^ 128 := by omega
  rw [h1, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3, Nat.shiftRight_eq_div_pow]
  have hdiv : 104 * new.toNat / 2 ^ 64 = 0 := Nat.div_eq_of_lt (by omega)
  rw [hdiv]
  rfl

private theorem mul_104_toNat {new : BitVec 64} (h : new.toNat * 104 < 2 ^ 64) :
    (104#64 * new).toNat = new.toNat * 104 := by
  rw [BitVec.toNat_mul]
  have : (104#64 : BitVec 64).toNat = 104 := rfl
  rw [this, Nat.mul_comm, Nat.mod_eq_of_lt h]

private theorem mul_104_ne_zero {new : BitVec 64} (h0 : 0 < new.toNat)
    (h : new.toNat * 104 < 2 ^ 64) : 104#64 * new ≠ 0#64 := by
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [mul_104_toNat h] at ht
  change new.toNat * 104 = 0 at ht
  omega

private theorem hi_104_eq_false {new : BitVec 64} (h : new.toNat * 104 ≤ 9223372036854775800) :
    (9223372036854775800#64).ult (104#64 * new) = false := by
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, mul_104_toNat (by omega)]
  change ¬ (9223372036854775800 < new.toNat * 104)
  omega

private theorem beq_mul_104_zero_eq_false {new : BitVec 64} (h0 : 0 < new.toNat)
    (h : new.toNat * 104 ≤ 9223372036854775800) : (104#64 * new == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  exact mul_104_ne_zero h0 (by omega)

private theorem SepWP.instantiate_post_exists {α : Type _} {prog : Program} {target_pc : BitVec 64}
    {s : State} {P R : SepProp} {Q : State → α → SepProp} {rest : State → Prop} (w : α)
    (h : SepWP prog target_pc s P (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ Q sf w ∗ R) ∧ rest sf)) :
    SepWP prog target_pc s P (fun sf P_f => (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ (∃∗ a, Q sf a) ∗ R) ∧
      rest sf) :=
  SepWP.mono h fun _ _ _ _ ⟨h1, h2⟩ =>
    ⟨fun hm => Satisfies.mono (sepConj_mono_left (Entails.sepExists_intro w)) (h1 hm), h2⟩

def finishGrowZeroEvents (new : BitVec 64) : List AllocEvent :=
  rustAllocEvents (new.toNat * 104) 8

def FinishGrowZeroEnv (new : BitVec 64) (evs : List AllocEvent) : Prop :=
  evs = finishGrowZeroEvents new

def finishGrowZeroSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (FinishGrowGhost × M.σ) where
  pre := fun ((out, cap, ptr, new, bs, o0, o1, o2, fsp), st) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = 8#64 ∧ s.readReg64 .x5 = 104#64 ∧
      s.sp = fsp ∧ cap = 0#64 ∧ bs.length = cap.toNat * 104 ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ new.toNat * 104 + 8 ≤ 2 ^ 63 ∧
      FitsEvents M lim st (finishGrowZeroEvents new)⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.pool lim st s ∗ cells (fsp - 48#64) 6 ∗ stackAt (fsp - 48#64) allocHookStack
  post := fun ((out, _cap, _ptr, new, _bs, _o0, _o1, _o2, fsp), st) s0 sf =>
    ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
      A.live p' (new.toNat * 104) 8 ∗ memRegion p' (new.toNat * 104) ∗
      A.pool lim (M.stepEvents (finishGrowZeroEvents new) st) sf ∗
      cells (fsp - 48#64) 6 ∗ stackAt (fsp - 48#64) allocHookStack ∗
      (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

theorem finishGrowZero_placed_ok_of_session [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (finishGrowZeroSpec M A lim) := by
  unfold finishGrowZeroSpec finishGrowZeroEvents
  cells_unfold
  have hshim' : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (lsρ lsRustNoAllocShimSym) sessionShimBudgetSpec := ls_hook_ok_of_mem hshim
  have halloc0 : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false) := ls_hook_ok_of_mem halloc
  have halloc' : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (lsρ lsRustAllocSym) (rustCliAllocNoOomExternSpecWithStack M A lim false allocHookStack) :=
    subroutine_ok_rustCliAllocNoOom_externWithStack (stk := allocHookStack)
      (by decide) (by decide) (subroutine_ok_allocNoOom_of_budget halloc0)
  dsimp only [sessionShimBudgetSpec, CryptoVerification.LibsignalTripleRatchet.sessionShimSpec] at hshim'
  dsimp only [rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomSpecWithStack,
    LibsignalBinary.Heap.RustLayoutOk, CryptoVerification.RustHeap.LayoutOk, ↓reduceIte] at halloc'
  wp_init x s0
  rcases x with ⟨⟨out, cap, ptr, new, bs, o0, o1, o2, fsp⟩, st⟩
  dsimp only at *
  subst fsp cap
  have hbound : new.toNat * 104 ≤ 9223372036854775800 := by omega
  have humulh := umulh_104_eq_zero hbound
  have hhi := hi_104_eq_false hbound
  have hcbz := beq_mul_104_zero_eq_false ‹0 < new.toNat› hbound
  have hmul : (104#64 * new).toNat = new.toNat * 104 := mul_104_toNat (by omega)
  have h8le : 8 ≤ new.toNat * 104 := by omega
  have hev_eq : rustAllocEvents (new.toNat * 104) 8 = [.alloc (new.toNat * 104)] := by
    simp only [rustAllocEvents, (by decide : (8 : Nat) ≤ 16), h8le, and_self, ↓reduceIte]
  have hfe_raw : FitsEvent M lim st (.alloc (new.toNat * 104)) :=
    (hev_eq ▸ ‹FitsEvents M lim st (rustAllocEvents (new.toNat * 104) 8)›).1
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hpos : 0 < new.toNat * 104 := by omega
  have hal : (8 : Nat) ≤ 2 ^ 31 := by decide
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_call hshim' ()
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  simp only [State.setMem_setMem]
  dsimp only [rustAllocEvents] at halloc'
  wp_call halloc' (new.toNat * 104, 8, st)
  have hne : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  simp only [State.setMem_setMem, rustAllocEvents, (by decide : (8 : Nat) ≤ 16), h8le, and_self,
    ↓reduceIte]
  apply SepWP.instantiate_post_exists (sf_1.readReg64 Reg.x0)
  wp_done

theorem finishGrowZero_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (finishGrowZeroSpec M A lim) :=
  finishGrowZero_placed_ok_of_session (hookSat_sessionShimBudget_of_rustAllocShimVm hshim) halloc

/-! ## 5. `<RawVec<Chain>>::grow_one` Zero-Capacity Variants (Block `43`) -/

private theorem stackAt_growOneChain (sp : BitVec 64) :
    memRegion (sp - 4208#64) 80 ∗ memRegion (sp - 4128#64) 32 ∗ stackAt sp allocHookStack =
      cells (sp - 64#64) 8 ∗ cells (sp - 112#64) 6 ∗ stackAt (sp - 112#64) allocHookStack := by
  have htop1 := stackAt_split_top sp 32 allocHookStack (by decide)
  have htop2 := stackAt_split_top sp 80 (32 + allocHookStack) (by decide)
  have hc1 := stackAt_split_cells sp (48 + allocHookStack) 8 (by decide)
  have hc2 := stackAt_split_cells (sp - 64#64) allocHookStack 6 (by decide)
  have hn1 : BitVec.ofNat 64 (32 + allocHookStack) = 4128#64 := rfl
  have hn2 : BitVec.ofNat 64 (80 + (32 + allocHookStack)) = 4208#64 := rfl
  have hn3 : (80 + (32 + allocHookStack) : Nat) = (48 + allocHookStack) + 8 * 8 := by decide
  have hn4 : BitVec.ofNat 64 (8 * 8) = 64#64 := rfl
  have hn5 : (48 + allocHookStack : Nat) = allocHookStack + 8 * 6 := by decide
  have hn6 : BitVec.ofNat 64 (8 * 6) = 48#64 := rfl
  have hn7 : sp - 64#64 - 48#64 = sp - 112#64 := by bv_arith
  rw [hn1] at htop1
  rw [hn2] at htop2
  rw [hn4] at hc1
  rw [hn6, hn7] at hc2
  rw [← htop1, ← htop2, hn3, hc1, hn5, hc2]
  sep_ac_rfl

def growOneChainZeroEvents : List AllocEvent :=
  rustAllocEvents 416 8

def GrowOneChainZeroEnv (evs : List AllocEvent) : Prop :=
  evs = growOneChainZeroEvents

def growOneChainZeroPlacedSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec ((BitVec 64 × BitVec 64) × M.σ) where
  pre := fun ((vecPtr, oldPtr), st) s =>
    ⌜s.readReg64 .x0 = vecPtr ∧ FitsEvents M lim st growOneChainZeroEvents⌝ ∗
      (vecPtr ↦₆₄ 0#64) ∗ ((vecPtr + 8#64) ↦₆₄ oldPtr) ∗ A.pool lim st s ∗
      cells (s.sp - 64#64) 8 ∗ cells (s.sp - 112#64) 6 ∗ stackAt (s.sp - 112#64) allocHookStack
  post := fun ((vecPtr, _oldPtr), st) s0 sf =>
    ∃∗ newPtr : BitVec 64,
      ⌜sf.trace = s0.trace ∧ newPtr ≠ 0#64⌝ ∗
      (vecPtr ↦₆₄ 4#64) ∗ ((vecPtr + 8#64) ↦₆₄ newPtr) ∗
      A.live newPtr 416 8 ∗ memRegion newPtr 416 ∗
      A.pool lim (M.stepEvents growOneChainZeroEvents st) sf ∗
      cells (s0.sp - 64#64) 8 ∗ cells (s0.sp - 112#64) 6 ∗ stackAt (s0.sp - 112#64) allocHookStack

theorem growOneChain_zero_placed_ok_of_session [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_43).rebase (blkPl_43).base H) (blkPl_43).base
      (withLsCodeLoaded lsmpl (growOneChainZeroPlacedSpec M A lim)) := by
  unfold withLsCodeLoaded growOneChainZeroPlacedSpec growOneChainZeroEvents
  cells_unfold
  have hfg0 := ls_subroutine_ok_of_block (callerProg := (blkPC_43).rebase (blkPl_43).base H)
    (subroutine_ok_withLsCodeLoaded_of_plain (finishGrowZero_placed_ok_of_session hshim halloc))
  change subroutine_ok _ (lsmpl.base 45) _ at hfg0
  simp only [withLsCodeLoaded, finishGrowZeroSpec, finishGrowZeroEvents, cells,
    sepExists_sepConj_right, sepConj_emp, bv_sub_add_lit', BitVec.reduceSub] at hfg0
  wp_init x s0
  rcases x with ⟨⟨vecPtr, oldPtr⟩, st⟩
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hfe1 : FitsEvent M lim st (.alloc 416) :=
    (by simpa [rustAllocEvents] using ‹FitsEvents M lim st (rustAllocEvents 416 8)› :
      FitsEvents M lim st [.alloc 416]).1
  subst vecPtr
  apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 45)
  wp_steps_sync_pool (lsmpl.base 45)
  simp only [State.setMem_setMem]
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcl1
  wp_call hfg0 ((s0.sp - 56#64, 0#64, oldPtr, 4#64, [], v_stk_7, v_stk_8, v_stk_9, s0.sp - 64#64), st)
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  simp only [State.setMem_setMem]
  wp_done

theorem growOneChain_zero_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_43).rebase (blkPl_43).base H) (blkPl_43).base
      (withLsCodeLoaded lsmpl (growOneChainZeroPlacedSpec M A lim)) :=
  growOneChain_zero_placed_ok_of_session (hookSat_sessionShimBudget_of_rustAllocShimVm hshim) halloc

def growOneChainZeroRegionPlacedSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec ((BitVec 64 × BitVec 64) × M.σ) where
  pre := fun ((vecPtr, oldPtr), st) s =>
    ⌜s.readReg64 .x0 = vecPtr ∧ FitsEvents M lim st growOneChainZeroEvents⌝ ∗
      (vecPtr ↦₆₄ 0#64) ∗ ((vecPtr + 8#64) ↦₆₄ oldPtr) ∗ A.pool lim st s ∗
      memRegion (s.sp - 4208#64) 80 ∗ memRegion (s.sp - 4128#64) 32 ∗ stackAt s.sp allocHookStack
  post := fun ((vecPtr, _oldPtr), st) s0 sf =>
    ∃∗ newPtr : BitVec 64,
      ⌜sf.trace = s0.trace ∧ newPtr ≠ 0#64⌝ ∗
      (vecPtr ↦₆₄ 4#64) ∗ ((vecPtr + 8#64) ↦₆₄ newPtr) ∗
      A.live newPtr 416 8 ∗ memRegion newPtr 416 ∗
      A.pool lim (M.stepEvents growOneChainZeroEvents st) sf ∗
      memRegion (s0.sp - 4208#64) 80 ∗ memRegion (s0.sp - 4128#64) 32 ∗
      stackAt s0.sp allocHookStack

theorem growOneChain_zero_region_placed_ok_of_session [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_43).rebase (blkPl_43).base H) (blkPl_43).base
      (withLsCodeLoaded lsmpl (growOneChainZeroRegionPlacedSpec M A lim)) := by
  apply subroutine_ok_outcome_intro
  intro g R s0 hpc hrun hpre hsp
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (growOneChainZeroPlacedSpec M A lim)).pre g s0 ∗ R := by
    simpa only [withLsCodeLoaded, growOneChainZeroRegionPlacedSpec, growOneChainZeroPlacedSpec,
      stackAt_growOneChain, sepConj_assoc] using hpre
  refine ((growOneChain_zero_placed_ok_of_session hshim halloc).to_outcome
    g R s0 hpc hrun hpre' hsp).mono_outcome ?_
  rintro sf (⟨hret, hcs, hpost⟩ | hrest)
  · left
    refine ⟨hret, hcs, ?_⟩
    simpa only [withLsCodeLoaded, growOneChainZeroRegionPlacedSpec, growOneChainZeroPlacedSpec,
      stackAt_growOneChain, sepConj_assoc] using hpost
  · exact Or.inr hrest

theorem growOneChain_zero_region_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_43).rebase (blkPl_43).base H) (blkPl_43).base
      (withLsCodeLoaded lsmpl (growOneChainZeroRegionPlacedSpec M A lim)) :=
  growOneChain_zero_region_placed_ok_of_session
    (hookSat_sessionShimBudget_of_rustAllocShimVm hshim) halloc

/-! ## 6. `<SessionState>::new` (Block `37`) -/

private theorem stackAt_sessionStateNew_entry (sp : BitVec 64) :
    memRegion (sp - 4224#64) 128 ∗ stackAt sp allocHookStack =
      (memRegion (sp - 96#64 - 4128#64) 32 ∗ stackAt (sp - 96#64) allocHookStack) ∗
      cells (sp - 96#64) 12 := by
  have h1 := stackAt_split_top sp 128 allocHookStack (by decide)
  have h2 := stackAt_split_cells sp (32 + allocHookStack) 12 (by decide)
  have h3 := stackAt_split_top (sp - 96#64) 32 allocHookStack (by decide)
  have h4 : (128 + allocHookStack : Nat) = (32 + allocHookStack) + 8 * 12 := by decide
  have h5 : BitVec.ofNat 64 (128 + allocHookStack) = 4224#64 := rfl
  have h6 : BitVec.ofNat 64 (8 * 12) = 96#64 := rfl
  have h7 : BitVec.ofNat 64 (32 + allocHookStack) = 4128#64 := rfl
  rw [h5] at h1
  rw [h6] at h2
  rw [h7] at h3
  rw [← h1, h4, h2, ← h3]

private theorem memRegion_344_sessionStateNew_split (outPtr : BitVec 64) :
    memRegion outPtr 344 =
      cells outPtr 19 ∗ memRegion (outPtr + 0x98#64) 96 ∗
      (∃∗ u_f8 : BitVec 64, (outPtr + 0xf8#64) ↦₆₄ u_f8) ∗
      memRegion (outPtr + 0x100#64) 40 ∗
      (∃∗ u_128 : BitVec 64, (outPtr + 0x128#64) ↦₆₄ u_128) ∗
      memRegion (outPtr + 0x130#64) 24 ∗
      (∃∗ u_148 : BitVec 32, (outPtr + 0x148#64) ↦₃₂ u_148) ∗
      (∃∗ u_14c : BitVec 64, (outPtr + 0x14c#64) ↦₆₄ u_14c) ∗
      (∃∗ u_154 : BitVec 32, (outPtr + 0x154#64) ↦₃₂ u_154) := by
  rw [memRegion_split outPtr 152 192 (by decide), memRegion_cells outPtr 19 (by decide),
    memRegion_split (outPtr + 152#64) 96 96 (by decide),
    memRegion_split (outPtr + 152#64 + 96#64) 8 88 (by decide),
    ProofLib.memRegion_eight (outPtr + 152#64 + 96#64),
    memRegion_split (outPtr + 152#64 + 96#64 + 8#64) 40 48 (by decide),
    memRegion_split (outPtr + 152#64 + 96#64 + 8#64 + 40#64) 8 40 (by decide),
    ProofLib.memRegion_eight (outPtr + 152#64 + 96#64 + 8#64 + 40#64),
    memRegion_split (outPtr + 152#64 + 96#64 + 8#64 + 40#64 + 8#64) 24 16 (by decide),
    memRegion_split (outPtr + 152#64 + 96#64 + 8#64 + 40#64 + 8#64 + 24#64) 4 12 (by decide),
    memRegion_four (outPtr + 152#64 + 96#64 + 8#64 + 40#64 + 8#64 + 24#64),
    memRegion_split (outPtr + 152#64 + 96#64 + 8#64 + 40#64 + 8#64 + 24#64 + 4#64) 8 4 (by decide),
    ProofLib.memRegion_eight (outPtr + 152#64 + 96#64 + 8#64 + 40#64 + 8#64 + 24#64 + 4#64),
    memRegion_four (outPtr + 152#64 + 96#64 + 8#64 + 40#64 + 8#64 + 24#64 + 4#64 + 8#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

def sessionStateNewEvents : List AllocEvent :=
  rustAllocEvents 33 1 ++ rustAllocEvents 33 1 ++ rustAllocEvents 32 1 ++ rustAllocEvents 33 1

def SessionStateNewEnv (evs : List AllocEvent) : Prop :=
  evs = sessionStateNewEvents

def sessionStateNewPlacedSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (SessionStateNewGhost × M.σ) where
  pre := fun (g, st) s =>
    ⌜s.readReg64 .x8 = g.outPtr ∧ s.readReg32 .x0 = g.version ∧ s.readReg64 .x1 = g.localIkPtr ∧
      s.readReg64 .x2 = g.remoteIkPtr ∧ s.readReg64 .x3 = g.rootKeyPtr ∧
      s.readReg64 .x4 = g.baseKeyPtr ∧ s.readReg64 .x5 = g.spqrVecPtr ∧
      g.localIk32.length = 32 ∧ g.remoteIk32.length = 32 ∧
      g.rootKey32.length = 32 ∧ g.baseKey32.length = 32 ∧
      FitsEvents M lim st sessionStateNewEvents⌝ ∗
      (g.localIkPtr ↦ₛ bytesToBv8 g.localIk32) ∗ (g.remoteIkPtr ↦ₛ bytesToBv8 g.remoteIk32) ∗
      (g.rootKeyPtr ↦ₛ bytesToBv8 g.rootKey32) ∗ (g.baseKeyPtr ↦ₛ bytesToBv8 g.baseKey32) ∗
      (g.spqrVecPtr ↦₆₄ g.spqrCap) ∗ ((g.spqrVecPtr + 0x08#64) ↦₆₄ g.spqrBufPtr) ∗
      ((g.spqrVecPtr + 0x10#64) ↦₆₄ g.spqrLen) ∗ memRegion g.outPtr 344 ∗
      (memRegion (s.sp - 4224#64) 128 ∗ stackAt s.sp allocHookStack) ∗ A.pool lim st s
  post := fun (g, st) s0 sf =>
    ∃∗ localIkBoxPtr : BitVec 64, ∃∗ remoteIkBoxPtr : BitVec 64,
    ∃∗ rootKeyBoxPtr : BitVec 64, ∃∗ baseKeyBoxPtr : BitVec 64,
      ⌜sf.trace = s0.trace ∧ localIkBoxPtr ≠ 0 ∧ remoteIkBoxPtr ≠ 0 ∧
        rootKeyBoxPtr ≠ 0 ∧ baseKeyBoxPtr ≠ 0⌝ ∗
      (g.localIkPtr ↦ₛ bytesToBv8 g.localIk32) ∗ (g.remoteIkPtr ↦ₛ bytesToBv8 g.remoteIk32) ∗
      (g.rootKeyPtr ↦ₛ bytesToBv8 g.rootKey32) ∗ (g.baseKeyPtr ↦ₛ bytesToBv8 g.baseKey32) ∗
      (g.spqrVecPtr ↦₆₄ g.spqrCap) ∗ ((g.spqrVecPtr + 0x08#64) ↦₆₄ g.spqrBufPtr) ∗
      ((g.spqrVecPtr + 0x10#64) ↦₆₄ g.spqrLen) ∗
      (localIkBoxPtr ↦ₛ bytesToBv8 (encodeEC g.localIk32)) ∗ A.live localIkBoxPtr 33 1 ∗
      (remoteIkBoxPtr ↦ₛ bytesToBv8 (encodeEC g.remoteIk32)) ∗ A.live remoteIkBoxPtr 33 1 ∗
      (rootKeyBoxPtr ↦ₛ bytesToBv8 g.rootKey32) ∗ A.live rootKeyBoxPtr 32 1 ∗
      (baseKeyBoxPtr ↦ₛ bytesToBv8 (encodeEC g.baseKey32)) ∗ A.live baseKeyBoxPtr 33 1 ∗
      (g.outPtr ↦₆₄ 33#64) ∗ ((g.outPtr + 0x08#64) ↦₆₄ localIkBoxPtr) ∗
      ((g.outPtr + 0x10#64) ↦₆₄ 33#64) ∗ ((g.outPtr + 0x18#64) ↦₆₄ 33#64) ∗
      ((g.outPtr + 0x20#64) ↦₆₄ remoteIkBoxPtr) ∗ ((g.outPtr + 0x28#64) ↦₆₄ 33#64) ∗
      ((g.outPtr + 0x30#64) ↦₆₄ 32#64) ∗ ((g.outPtr + 0x38#64) ↦₆₄ rootKeyBoxPtr) ∗
      ((g.outPtr + 0x40#64) ↦₆₄ 32#64) ∗ ((g.outPtr + 0x48#64) ↦₆₄ 0#64) ∗
      ((g.outPtr + 0x50#64) ↦₆₄ 8#64) ∗ ((g.outPtr + 0x58#64) ↦₆₄ 0#64) ∗
      ((g.outPtr + 0x60#64) ↦₆₄ 33#64) ∗ ((g.outPtr + 0x68#64) ↦₆₄ baseKeyBoxPtr) ∗
      ((g.outPtr + 0x70#64) ↦₆₄ 33#64) ∗ ((g.outPtr + 0x78#64) ↦₆₄ g.spqrCap) ∗
      ((g.outPtr + 0x80#64) ↦₆₄ g.spqrBufPtr) ∗ ((g.outPtr + 0x88#64) ↦₆₄ g.spqrLen) ∗
      ((g.outPtr + 0x90#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (g.outPtr + 0x98#64) 96 ∗
      ((g.outPtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (g.outPtr + 0x100#64) 40 ∗
      ((g.outPtr + 0x128#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (g.outPtr + 0x130#64) 24 ∗
      ((g.outPtr + 0x148#64) ↦₃₂ (BitVec.ofNat 32 (g.version.toNat % 256))) ∗
      ((g.outPtr + 0x14c#64) ↦₆₄ 0#64) ∗ ((g.outPtr + 0x154#64) ↦₃₂ 0#32) ∗
      (memRegion (s0.sp - 4224#64) 128 ∗ stackAt s0.sp allocHookStack) ∗
      A.pool lim (M.stepEvents sessionStateNewEvents st) sf

set_option maxHeartbeats 4000000 in
theorem sessionStateNew_placed_ok_of_session [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_37).rebase (blkPl_37).base H) (blkPl_37).base
      (withLsCodeLoaded lsmpl (sessionStateNewPlacedSpec M A lim)) := by
  unfold withLsCodeLoaded sessionStateNewPlacedSpec sessionStateNewEvents
  simp only [stackAt_sessionStateNew_entry, memRegion_344_sessionStateNew_split]
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    bv_sub_add_lit', BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub, sepConj_assoc]
  have hser := ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_37).rebase (blkPl_37).base H)
    (ecPubKeySerialize_alloc_placed_ok_of_session hshim halloc)
  change subroutine_ok _ (lsmpl.base 205)
    (withLsCl lsmpl (ecPubKeySerializeAllocPlacedSpec M A lim)) at hser
  simp only [withLsCl, ecPubKeySerializeAllocPlacedSpec, ecPubKeySerializeAllocEvents] at hser
  have hshim' : subroutine_ok ((blkPC_37).rebase (blkPl_37).base H)
      (lsρ lsRustNoAllocShimSym) sessionShimBudgetSpec := ls_hook_ok_of_mem hshim
  have halloc0 : subroutine_ok ((blkPC_37).rebase (blkPl_37).base H)
      (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false) := ls_hook_ok_of_mem halloc
  have halloc' : subroutine_ok ((blkPC_37).rebase (blkPl_37).base H)
      (lsρ lsRustAllocSym) (rustCliAllocNoOomExternSpecWithStack M A lim false allocHookStack) :=
    subroutine_ok_rustCliAllocNoOom_externWithStack (stk := allocHookStack)
      (by decide) (by decide) (subroutine_ok_allocNoOom_of_budget halloc0)
  dsimp only [sessionShimBudgetSpec, CryptoVerification.LibsignalTripleRatchet.sessionShimSpec] at hshim'
  dsimp only [rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomSpecWithStack,
    LibsignalBinary.Heap.RustLayoutOk, CryptoVerification.RustHeap.LayoutOk, ↓reduceIte] at halloc'
  wp_init x s0
  rcases x with ⟨⟨outPtr, version, localIkPtr, localIk32, remoteIkPtr, remoteIk32,
    rootKeyPtr, rootKey32, baseKeyPtr, baseKey32, spqrVecPtr, spqrCap, spqrBufPtr, spqrLen⟩, st⟩
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  subst outPtr version localIkPtr remoteIkPtr rootKeyPtr baseKeyPtr spqrVecPtr
  have hfe_all : FitsEvents M lim st [.alloc 33, .alloc 33, .alloc 32, .alloc 33] := by
    simpa [rustAllocEvents] using
      ‹FitsEvents M lim st (rustAllocEvents 33 1 ++ rustAllocEvents 33 1 ++
        rustAllocEvents 32 1 ++ rustAllocEvents 33 1)›
  rcases hfe_all with ⟨hfe1, hfe2, hfe3, hfe4, -⟩
  let st1 := M.stepEvents (rustAllocEvents 33 1) st
  let st2 := M.stepEvents (rustAllocEvents 33 1) st1
  let st3 := M.stepEvents (rustAllocEvents 32 1) st2
  have hlen_rk : (bytesToBv8 rootKey32).length = 32 := by
    simp [bytesToBv8, ‹rootKey32.length = 32›]
  obtain ⟨rk0, rk1, rk2, rk3, _, hrk_cells⟩ := exists_unpack64_of_length_32 hlen_rk
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hpos32 : 0 < (32 : Nat) := by decide
  have hal1 : (1 : Nat) ≤ 2 ^ 31 := by decide
  have hsum32 : (32 : Nat) + 1 ≤ 2 ^ 63 := by decide
  apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 205)
  wp_steps_sync_pool (lsmpl.base 205)
  simp only [State.setMem_setMem]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl1
  wp_call hser ((s0.readReg64 (.gpr 1#5), localIk32), st)
  have hcl2 : LibsignalCodeLoaded lsmpl sf.mem := by assumption
  apply sepWP_seq_lscl hcl2 (mid := lsmpl.base 205)
  wp_steps_sync_pool (lsmpl.base 205)
  simp only [State.setMem_setMem]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl3
  wp_call hser ((s0.readReg64 (.gpr 2#5), remoteIk32), st1)
  have hcl4 : LibsignalCodeLoaded lsmpl sf_1.mem := by assumption
  apply sepWP_seq_lscl hcl4 (mid := lsmpl.base 205)
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_call hshim' ()
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_2› (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc' (32, 1, st2)
  have hne_rk : sf_3.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq_rk : (sf_3.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne_rk
  have hm32 : memRegion (sf_3.readReg64 (Reg.gpr 0#5)) 32 =
      cells (sf_3.readReg64 (Reg.gpr 0#5)) 4 :=
    memRegion_cells (sf_3.readReg64 (Reg.gpr 0#5)) 4 (by decide)
  simp only [hm32, cells, sepConj_emp, sepExists_sepConj_left,
    sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWP.exists_elim fun u0 => SepWP.exists_elim fun u1 =>
    SepWP.exists_elim fun u2 => SepWP.exists_elim fun u3 => ?_
  rw [hrk_cells (s0.readReg64 (.gpr 3#5))]
  wp_steps_sync_pool (lsmpl.base 205)
  simp only [State.setMem_setMem]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl5
  wp_call hser ((s0.readReg64 (.gpr 4#5), baseKey32), st3)
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  simp only [State.setMem_setMem, hrk_cells, sepConj_assoc]
  wp_done

theorem sessionStateNew_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_37).rebase (blkPl_37).base H) (blkPl_37).base
      (withLsCodeLoaded lsmpl (sessionStateNewPlacedSpec M A lim)) :=
  sessionStateNew_placed_ok_of_session (hookSat_sessionShimBudget_of_rustAllocShimVm hshim) halloc

/-! ## 7. `<SessionState>::with_sender_chain` None Branch (Block `27`) -/

private theorem stackAt_withSenderChain_entry (sp : BitVec 64) :
    memRegion (sp - 4256#64) 160 ∗ stackAt sp allocHookStack =
      (memRegion (sp - 128#64 - 4128#64) 32 ∗ stackAt (sp - 128#64) allocHookStack) ∗
        cells (sp - 128#64) 16 := by
  have h1 := stackAt_split_top sp 160 allocHookStack (by decide)
  have h2 := stackAt_split_cells sp (32 + allocHookStack) 16 (by decide)
  have h3 := stackAt_split_top (sp - 128#64) 32 allocHookStack (by decide)
  have h4 : (160 + allocHookStack : Nat) = (32 + allocHookStack) + 8 * 16 := by decide
  have h5 : BitVec.ofNat 64 (160 + allocHookStack) = 4256#64 := rfl
  have h6 : BitVec.ofNat 64 (8 * 16) = 128#64 := rfl
  have h7 : BitVec.ofNat 64 (32 + allocHookStack) = 4128#64 := rfl
  rw [h5] at h1; rw [h6] at h2; rw [h7] at h3
  rw [← h1, h4, h2, ← h3]

private theorem memRegion_92_senderChain_split (ptr : BitVec 64) :
    memRegion (ptr + 0x98#64) 92 =
      cells (ptr + 0x98#64) 11 ∗ (∃∗ v : BitVec 32, (ptr + 0xf0#64) ↦₃₂ v) := by
  have hsplit := memRegion_split (ptr + 0x98#64) 88 4 (by decide)
  have haddr : ptr + 0x98#64 + BitVec.ofNat 64 88 = ptr + 0xf0#64 := by bv_omega
  rw [hsplit, memRegion_cells (ptr + 0x98#64) 11 (by decide), haddr, ProofLib.memRegion_four]

private theorem sepWP_focus {prog : Program} {ret : BitVec 64} {s : State}
    {P T F : SepProp} {Q : State → SepProp → Prop}
    (hf : P = T ∗ F) (h : SepWP prog ret s (T ∗ F) Q) : SepWP prog ret s P Q :=
  hf ▸ h

private theorem cells_three_entails (sp v0 v1 v2 : BitVec 64) :
    ((sp - 120#64) ↦₆₄ v0 ∗ (sp - 112#64) ↦₆₄ v1 ∗ (sp - 104#64) ↦₆₄ v2) ⊢
      cells (sp - 120#64) 3 := by
  simp only [cells, sepConj_emp, sepExists_sepConj_right, bv_sub_add_lit', BitVec.reduceSub]
  exact Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2
    (Entails.refl _)))

@[local simp, local wp_norm, local arm64_norm]
private theorem cond_eq_adds_neg1_1 :
    ConditionHolds CondCode.EQ (addsPState64 0xffffffffffffffff#64 1#64) = true := by
  simp only [ConditionHolds, addsPState64]; decide

def withSenderChainNoneEvents : List AllocEvent :=
  rustAllocEvents 32 1 ++ rustAllocEvents 33 1 ++ rustAllocEvents 33 1 ++
    rustAllocEvents 32 1 ++ rustAllocEvents 32 1 ++
    rustDeallocEvents 32 1 ++ rustDeallocEvents 33 1

def WithSenderChainNoneEnv (evs : List AllocEvent) : Prop :=
  evs = withSenderChainNoneEvents

def withSenderChainNonePlacedSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (WithSenderChainGhost × M.σ) where
  pre := fun (g, st) s =>
    ⌜s.readReg64 .x8 = g.outPtr ∧ s.readReg64 .x0 = g.inPtr ∧
      s.readReg64 .x1 = g.senderKeyPairPtr ∧ s.readReg64 .x2 = g.senderChainKeyPtr ∧
      g.senderRatchetPub32.length = 32 ∧ g.senderRatchetPriv32.length = 32 ∧
      g.senderChainKey32.length = 32 ∧ g.pre144.length = 144 ∧ g.post100.length = 100 ∧
      FitsEvents M lim st withSenderChainNoneEvents⌝ ∗
      (g.senderKeyPairPtr ↦ₛ bytesToBv8 g.senderRatchetPub32) ∗
      ((g.senderKeyPairPtr + 32#64) ↦ₛ bytesToBv8 g.senderRatchetPriv32) ∗
      (g.senderChainKeyPtr ↦ₛ bytesToBv8 g.senderChainKey32) ∗
      ((g.senderChainKeyPtr + 32#64) ↦₃₂ g.senderChainIdx) ∗
      (g.inPtr ↦ₛ g.pre144) ∗ ((g.inPtr + 0x90#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      memRegion (g.inPtr + 0x98#64) 92 ∗ ((g.inPtr + 0xf4#64) ↦ₛ g.post100) ∗
      memRegion g.outPtr 344 ∗ (memRegion (s.sp - 4256#64) 160 ∗ stackAt s.sp allocHookStack) ∗
      A.pool lim st s
  post := fun (g, st) s0 sf =>
    ∃∗ senderRatchetPubBoxPtr : BitVec 64, ∃∗ senderRatchetPrivBoxPtr : BitVec 64,
    ∃∗ senderChainKeyBoxPtr : BitVec 64,
      ⌜sf.trace = s0.trace ∧ senderRatchetPubBoxPtr ≠ 0 ∧ senderRatchetPrivBoxPtr ≠ 0 ∧
        senderChainKeyBoxPtr ≠ 0⌝ ∗
      (g.senderKeyPairPtr ↦ₛ bytesToBv8 g.senderRatchetPub32) ∗
      ((g.senderKeyPairPtr + 32#64) ↦ₛ bytesToBv8 g.senderRatchetPriv32) ∗
      (g.senderChainKeyPtr ↦ₛ bytesToBv8 g.senderChainKey32) ∗
      ((g.senderChainKeyPtr + 32#64) ↦₃₂ g.senderChainIdx) ∗
      (senderRatchetPubBoxPtr ↦ₛ bytesToBv8 (encodeEC g.senderRatchetPub32)) ∗
      A.live senderRatchetPubBoxPtr 33 1 ∗
      (senderRatchetPrivBoxPtr ↦ₛ bytesToBv8 g.senderRatchetPriv32) ∗
      A.live senderRatchetPrivBoxPtr 32 1 ∗
      (senderChainKeyBoxPtr ↦ₛ bytesToBv8 g.senderChainKey32) ∗ A.live senderChainKeyBoxPtr 32 1 ∗
      (g.outPtr ↦ₛ g.pre144) ∗
      senderChainFieldsAt g.outPtr senderRatchetPubBoxPtr senderRatchetPrivBoxPtr
        senderChainKeyBoxPtr g.senderChainIdx ∗ ((g.outPtr + 0xf4#64) ↦ₛ g.post100) ∗
      (g.inPtr ↦ₛ g.pre144) ∗
      senderChainFieldsAt g.inPtr senderRatchetPubBoxPtr senderRatchetPrivBoxPtr
        senderChainKeyBoxPtr g.senderChainIdx ∗ ((g.inPtr + 0xf4#64) ↦ₛ g.post100) ∗
      (memRegion (s0.sp - 4256#64) 160 ∗ stackAt s0.sp allocHookStack) ∗
      A.pool lim (M.stepEvents withSenderChainNoneEvents st) sf

set_option maxHeartbeats 4000000 in
theorem withSenderChain_none_placed_ok_of_session [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_27).rebase (blkPl_27).base H) (blkPl_27).base
      (withLsCodeLoaded lsmpl (withSenderChainNonePlacedSpec M A lim)) := by
  unfold withLsCodeLoaded withSenderChainNonePlacedSpec withSenderChainNoneEvents
  simp only [stackAt_withSenderChain_entry, memRegion_92_senderChain_split]
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    bv_sub_add_lit', BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub, sepConj_assoc]
  have hser := ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_27).rebase (blkPl_27).base H)
    (ecPubKeySerialize_alloc_placed_ok_of_session hshim halloc)
  change subroutine_ok _ (lsmpl.base 205)
    (withLsCl lsmpl (ecPubKeySerializeAllocPlacedSpec M A lim)) at hser
  dsimp only [withLsCl, ecPubKeySerializeAllocPlacedSpec, ecPubKeySerializeAllocEvents] at hser
  have hpser := ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_27).rebase (blkPl_27).base H)
    (privKeySerialize_placed_ok_of_session hshim halloc)
  change subroutine_ok _ (lsmpl.base 208)
    (withLsCl lsmpl (privKeySerializePlacedSpec M A lim)) at hpser
  dsimp only [withLsCl, privKeySerializePlacedSpec, privKeySerializePlacedEvents] at hpser
  have hshim' : subroutine_ok ((blkPC_27).rebase (blkPl_27).base H)
      (lsρ lsRustNoAllocShimSym) sessionShimBudgetSpec := ls_hook_ok_of_mem hshim
  have halloc0 : subroutine_ok ((blkPC_27).rebase (blkPl_27).base H)
      (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false) := ls_hook_ok_of_mem halloc
  have halloc' : subroutine_ok ((blkPC_27).rebase (blkPl_27).base H)
      (lsρ lsRustAllocSym) (rustCliAllocNoOomExternSpecWithStack M A lim false allocHookStack) :=
    subroutine_ok_rustCliAllocNoOom_externWithStack (stk := allocHookStack)
      (by decide) (by decide) (subroutine_ok_allocNoOom_of_budget halloc0)
  have hdealloc' := dealloc_bytes_placed_ok (prog := (blkPC_27).rebase (blkPl_27).base H) hdealloc
  have hmemcpy' : subroutine_ok ((blkPC_27).rebase (blkPl_27).base H)
      (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec := ls_hook_ok_of_mem hmemcpy
  dsimp only [sessionShimBudgetSpec, CryptoVerification.LibsignalTripleRatchet.sessionShimSpec] at hshim'
  dsimp only [rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomSpecWithStack,
    LibsignalBinary.Heap.RustLayoutOk, CryptoVerification.RustHeap.LayoutOk, ↓reduceIte] at halloc'
  dsimp only [rustDeallocBytesSpec] at hdealloc'
  dsimp only [sessionMemcpyRegionBudgetSpec,
    CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec, memcpyRegionSpec] at hmemcpy'
  wp_init x s0
  rcases x with ⟨⟨outPtr, inPtr, senderKeyPairPtr, senderRatchetPub32,
    senderRatchetPriv32, senderChainKeyPtr, senderChainKey32, senderChainIdx, pre144, post100⟩, st⟩
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  subst outPtr inPtr senderKeyPairPtr senderChainKeyPtr
  have hfe_all : FitsEvents M lim st
      [.alloc 32, .alloc 33, .alloc 33, .alloc 32, .alloc 32, .free 1 32, .free 1 33] := by
    simpa [rustAllocEvents, rustDeallocEvents] using
      ‹FitsEvents M lim st (rustAllocEvents 32 1 ++ rustAllocEvents 33 1 ++ rustAllocEvents 33 1 ++
        rustAllocEvents 32 1 ++ rustAllocEvents 32 1 ++
        rustDeallocEvents 32 1 ++ rustDeallocEvents 33 1)›
  rcases hfe_all with ⟨hfe1, hfe2, hfe3, hfe4, hfe5, -, -, -⟩
  let st1 := M.stepEvents (rustAllocEvents 32 1) st
  let st2 := M.stepEvents (rustAllocEvents 33 1) st1
  let st3 := M.stepEvents (rustAllocEvents 33 1) st2
  let st4 := M.stepEvents (rustAllocEvents 32 1) st3
  let st5 := M.stepEvents (rustAllocEvents 32 1) st4
  let st6 := M.stepEvents (rustDeallocEvents 32 1) st5
  have hlen_ck : (bytesToBv8 senderChainKey32).length = 32 := by
    simp [bytesToBv8, ‹senderChainKey32.length = 32›]
  obtain ⟨ck0, ck1, ck2, ck3, _, hck_cells⟩ := exists_unpack64_of_length_32 hlen_ck
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hpos32 : 0 < (32 : Nat) := by decide
  have hpos33 : 0 < (33 : Nat) := by decide
  have hal1 : (1 : Nat) ≤ 2 ^ 31 := by decide
  have hsum32 : (32 : Nat) + 1 ≤ 2 ^ 63 := by decide
  have hsum33 : (33 : Nat) + 1 ≤ 2 ^ 63 := by decide
  apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 205)
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_call hshim' ()
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc' (32, 1, st)
  have hne1 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq1 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne1
  have hm32_1 : memRegion (sf_1.readReg64 (Reg.gpr 0#5)) 32 =
      cells (sf_1.readReg64 (Reg.gpr 0#5)) 4 :=
    memRegion_cells (sf_1.readReg64 (Reg.gpr 0#5)) 4 (by decide)
  simp only [hm32_1, cells, sepConj_emp, sepExists_sepConj_left,
    sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWP.exists_elim fun u0 => SepWP.exists_elim fun u1 =>
    SepWP.exists_elim fun u2 => SepWP.exists_elim fun u3 => ?_
  rw [hck_cells (s0.readReg64 (.gpr 2#5))]
  wp_steps_sync_pool (lsmpl.base 205)
  simp only [State.setMem_setMem, hck_cells, sepConj_assoc]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl1
  wp_call hser ((s0.readReg64 (.gpr 1#5), senderRatchetPub32), st1)
  have hcl2 : LibsignalCodeLoaded lsmpl sf_2.mem := by assumption
  have henc33 : (encodeEC senderRatchetPub32).length = 33 := by
    change (0x05 :: senderRatchetPub32).length = 33; simp [‹senderRatchetPub32.length = 32›]
  have hlen_pub33 : (bytesToBv8 (encodeEC senderRatchetPub32)).length = 33 := by
    simp [bytesToBv8, henc33]
  have hlen_priv32 : (bytesToBv8 senderRatchetPriv32).length = 32 := by
    simp [bytesToBv8, ‹senderRatchetPriv32.length = 32›]
  apply sepWP_seq_lscl hcl2 (mid := lsmpl.base 208)
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_call hshim' ()
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_3› (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc' (33, 1, st2)
  have hne2 : sf_4.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq2 : (sf_4.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne2
  wp_steps_sync_pool (lsρ lsMemcpySym)
  simp only [State.setMem_setMem]
  rw [← hlen_pub33]
  wp_call hmemcpy' (sf_4.readReg64 (Reg.gpr 0#5), _, bytesToBv8 (encodeEC senderRatchetPub32))
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_5› (hnext := ?_)
  simp only [hlen_pub33, henc33]
  wp_steps_sync_pool (lsmpl.base 208)
  simp only [State.setMem_setMem]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl3
  apply SepWP.replace_pre (by sep_focus) (cells_three_entails s0.sp _ _ _)
  wp_call hpser ((s0.readReg64 (.gpr 1#5) + 32#64, bytesToBv8 senderRatchetPriv32, s0.sp - 120#64), st3)
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_call hshim' ()
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_7› (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc' (32, 1, st4)
  have hne3 : sf_8.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq3 : (sf_8.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne3
  wp_steps_sync_pool (lsρ lsMemcpySym)
  simp only [State.setMem_setMem]
  rw [← hlen_priv32]
  wp_call hmemcpy' (sf_8.readReg64 (Reg.gpr 0#5), _, bytesToBv8 senderRatchetPriv32)
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_9› (hnext := ?_)
  simp only [hlen_priv32, ‹senderRatchetPriv32.length = 32›]
  wp_steps_sync_pool (lsρ lsRustDeallocSym)
  simp only [State.setMem_setMem]
  wp_call hdealloc' ((_, bytesToBv8 senderRatchetPriv32, 32, 1), st5)
  wp_steps_sync_pool (lsρ lsRustDeallocSym)
  simp only [State.setMem_setMem]
  wp_call hdealloc' ((_, bytesToBv8 (encodeEC senderRatchetPub32), 33, 1), st6)
  wp_steps_sync_pool (lsρ lsMemcpySym)
  simp only [State.setMem_setMem]
  have hpack_in := withSenderChain_pack344_unfolded (s0.readReg64 (.gpr 0#5))
    (sf_4.readReg64 (.gpr 0#5)) (sf_8.readReg64 (.gpr 0#5)) (sf_1.readReg64 (.gpr 0#5))
    senderChainIdx pre144 post100 ‹pre144.length = 144›
  have hlen_full : (pre144 ++ (senderChainBytes100 (sf_4.readReg64 (.gpr 0#5))
      (sf_8.readReg64 (.gpr 0#5)) (sf_1.readReg64 (.gpr 0#5)) senderChainIdx ++
      post100)).length = 344 := by
    simp [‹pre144.length = 144›, ‹post100.length = 100›]
  refine sepWP_focus (T :=
    (s0.readReg64 (.gpr 0#5) ↦ₛ pre144) ∗ ((s0.readReg64 (.gpr 0#5) + 0x90#64) ↦₆₄ 33#64) ∗
    ((s0.readReg64 (.gpr 0#5) + 0x98#64) ↦₆₄ sf_4.readReg64 (.gpr 0#5)) ∗
    ((s0.readReg64 (.gpr 0#5) + 0xa0#64) ↦₆₄ 33#64) ∗
    ((s0.readReg64 (.gpr 0#5) + 0xa8#64) ↦₆₄ 32#64) ∗
    ((s0.readReg64 (.gpr 0#5) + 0xb0#64) ↦₆₄ sf_8.readReg64 (.gpr 0#5)) ∗
    ((s0.readReg64 (.gpr 0#5) + 0xb8#64) ↦₆₄ 32#64) ∗
    ((s0.readReg64 (.gpr 0#5) + 0xc0#64) ↦₆₄ 0#64) ∗
    ((s0.readReg64 (.gpr 0#5) + 0xc8#64) ↦₆₄ 8#64) ∗
    ((s0.readReg64 (.gpr 0#5) + 0xd0#64) ↦₆₄ 0#64) ∗
    ((s0.readReg64 (.gpr 0#5) + 0xd8#64) ↦₆₄ 32#64) ∗
    ((s0.readReg64 (.gpr 0#5) + 0xe0#64) ↦₆₄ sf_1.readReg64 (.gpr 0#5)) ∗
    ((s0.readReg64 (.gpr 0#5) + 0xe8#64) ↦₆₄ 32#64) ∗
    ((s0.readReg64 (.gpr 0#5) + 0xf0#64) ↦₃₂ senderChainIdx) ∗
    ((s0.readReg64 (.gpr 0#5) + 0xf4#64) ↦ₛ post100)) (by sep_focus) ?_
  rw [hpack_in, ← hlen_full]
  wp_call hmemcpy' (s0.readReg64 (.gpr 8#5), s0.readReg64 (.gpr 0#5), pre144 ++
    (senderChainBytes100 (sf_4.readReg64 (.gpr 0#5))
      (sf_8.readReg64 (.gpr 0#5)) (sf_1.readReg64 (.gpr 0#5)) senderChainIdx ++ post100))
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_12› (hnext := ?_)
  simp only [← withSenderChain_pack344 _ _ _ _ _ _ _ ‹pre144.length = 144›, sepConj_assoc]
  wp_done

theorem withSenderChain_none_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok ((blkPC_27).rebase (blkPl_27).base H) (blkPl_27).base
      (withLsCodeLoaded lsmpl (withSenderChainNonePlacedSpec M A lim)) :=
  withSenderChain_none_placed_ok_of_session
    (hookSat_sessionShimBudget_of_rustAllocShimVm hshim) halloc hdealloc
    (hookSat_sessionMemcpyRegionBudget_of_allocMemcpyVm hmemcpy)

/-! ## 8. `<SessionState>::with_receiver_chain` Empty Branch (Block `30`) -/

private theorem stackAt_withReceiverChain_entry (sp : BitVec 64) :
    memRegion (sp - 4576#64) 480 ∗ stackAt sp allocHookStack =
      memRegion (sp - 368#64 - 4208#64) 80 ∗
        (memRegion (sp - 368#64 - 4128#64) 32 ∗ stackAt (sp - 368#64) allocHookStack) ∗
        memRegion (sp - 368#64) 272 ∗ cells (sp - 96#64) 12 := by
  have h1 := stackAt_split_top sp 480 allocHookStack (by decide)
  have h2 := stackAt_split_cells sp (112 + allocHookStack) 46 (by decide)
  have h3 := stackAt_split_top (sp - 368#64) 112 allocHookStack (by decide)
  have h4 := memRegion_split (sp - 368#64 - 4208#64) 80 32 (by decide)
  have h5 : (480 + allocHookStack : Nat) = (112 + allocHookStack) + 8 * 46 := by decide
  have h6 : BitVec.ofNat 64 (480 + allocHookStack) = 4576#64 := rfl
  have h7 : BitVec.ofNat 64 (8 * 46) = 368#64 := rfl
  have h8 : BitVec.ofNat 64 (112 + allocHookStack) = 4208#64 := rfl
  have h9 : sp - 368#64 - 4208#64 + BitVec.ofNat 64 80 = sp - 368#64 - 4128#64 := by bv_omega
  have hcells46 : cells (sp - 368#64) 46 = memRegion (sp - 368#64) 272 ∗ cells (sp - 96#64) 12 := by
    rw [← memRegion_cells (sp - 368#64) 46 (by decide),
      memRegion_split (sp - 368#64) 272 96 (by decide),
      show sp - 368#64 + BitVec.ofNat 64 272 = sp - 96#64 by bv_omega,
      memRegion_cells (sp - 96#64) 12 (by decide)]
  rw [h6] at h1; rw [h7] at h2; rw [h8] at h3; rw [h9] at h4
  rw [← h1, h5, h2, h3, h4, hcells46]
  simp only [sepConj_assoc]

private theorem memRegion_416_receiverChain_split (ptr : BitVec 64) :
    memRegion ptr 416 =
      cells ptr 12 ∗ (∃∗ v : BitVec 32, (ptr + 0x60#64) ↦₃₂ v) ∗ memRegion (ptr + 0x64#64) 316 := by
  have h1 := memRegion_split ptr 96 320 (by decide)
  have h2 := memRegion_split (ptr + BitVec.ofNat 64 96) 4 316 (by decide)
  have h3 : ptr + BitVec.ofNat 64 96 = ptr + 0x60#64 := by bv_omega
  have h4 : ptr + 0x60#64 + BitVec.ofNat 64 4 = ptr + 0x64#64 := by bv_omega
  rw [h1, memRegion_cells ptr 12 (by decide), h3]
  rw [h3, h4] at h2
  rw [h2, ProofLib.memRegion_four (ptr + 0x60#64)]

@[local simp, local wp_norm, local arm64_norm]
private theorem cond_eq_subs_0_0 : ConditionHolds CondCode.EQ (subsPState64 0#64 0#64) = true := by
  simp only [ConditionHolds, subsPState64]; decide

@[local simp, local wp_norm, local arm64_norm]
private theorem cond_lt_subs_0_5 : ConditionHolds CondCode.LT (subsPState64 0#64 5#64) = true := by
  simp only [ConditionHolds, subsPState64]; decide

@[local simp, local wp_norm, local arm64_norm]
private theorem madd_zero_104 (ptr : BitVec 64) : ptr + 0#64 * 104#64 = ptr := by simp

def withReceiverChainEmptyEvents : List AllocEvent :=
  rustAllocEvents 32 1 ++ rustAllocEvents 33 1 ++ rustAllocEvents 33 1 ++
    rustDeallocEvents 33 1 ++ growOneChainZeroEvents

def WithReceiverChainEmptyEnv (evs : List AllocEvent) : Prop :=
  evs = withReceiverChainEmptyEvents

def withReceiverChainEmptyPlacedSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (WithReceiverChainGhost × M.σ) where
  pre := fun (g, st) s =>
    ⌜s.readReg64 .x8 = g.outPtr ∧ s.readReg64 .x0 = g.inPtr ∧
      s.readReg64 .x1 = g.senderRatchetPubPtr ∧ s.readReg64 .x2 = g.receiverChainKeyPtr ∧
      g.senderRatchetPub32.length = 32 ∧ g.receiverChainKey32.length = 32 ∧
      g.pre72.length = 72 ∧ g.post248.length = 248 ∧
      FitsEvents M lim st withReceiverChainEmptyEvents⌝ ∗
      (g.senderRatchetPubPtr ↦ₛ bytesToBv8 g.senderRatchetPub32) ∗
      (g.receiverChainKeyPtr ↦ₛ bytesToBv8 g.receiverChainKey32) ∗
      ((g.receiverChainKeyPtr + 32#64) ↦₃₂ g.receiverChainIdx) ∗
      (g.inPtr ↦ₛ g.pre72) ∗ ((g.inPtr + 0x48#64) ↦₆₄ 0#64) ∗
      ((g.inPtr + 0x50#64) ↦₆₄ g.oldVecPtr) ∗ ((g.inPtr + 0x58#64) ↦₆₄ 0#64) ∗
      ((g.inPtr + 0x60#64) ↦ₛ g.post248) ∗ memRegion g.outPtr 344 ∗
      (memRegion (s.sp - 4576#64) 480 ∗ stackAt s.sp allocHookStack) ∗ A.pool lim st s
  post := fun (g, st) s0 sf =>
    ∃∗ receiverRatchetPubBoxPtr : BitVec 64, ∃∗ receiverChainKeyBoxPtr : BitVec 64,
    ∃∗ chainBufPtr : BitVec 64,
      ⌜sf.trace = s0.trace ∧ receiverRatchetPubBoxPtr ≠ 0 ∧ receiverChainKeyBoxPtr ≠ 0 ∧
        chainBufPtr ≠ 0⌝ ∗
      (g.senderRatchetPubPtr ↦ₛ bytesToBv8 g.senderRatchetPub32) ∗
      (g.receiverChainKeyPtr ↦ₛ bytesToBv8 g.receiverChainKey32) ∗
      ((g.receiverChainKeyPtr + 32#64) ↦₃₂ g.receiverChainIdx) ∗
      (receiverRatchetPubBoxPtr ↦ₛ bytesToBv8 (encodeEC g.senderRatchetPub32)) ∗
      A.live receiverRatchetPubBoxPtr 33 1 ∗
      (receiverChainKeyBoxPtr ↦ₛ bytesToBv8 g.receiverChainKey32) ∗
      A.live receiverChainKeyBoxPtr 32 1 ∗ A.live chainBufPtr 416 8 ∗
      receiverChainElemAt chainBufPtr receiverRatchetPubBoxPtr receiverChainKeyBoxPtr
        g.receiverChainIdx ∗
      memRegion (chainBufPtr + 0x64#64) 316 ∗
      (g.outPtr ↦ₛ g.pre72) ∗ receiverChainVecFieldsAt g.outPtr chainBufPtr ∗
      ((g.outPtr + 0x60#64) ↦ₛ g.post248) ∗
      (g.inPtr ↦ₛ g.pre72) ∗ receiverChainVecFieldsAt g.inPtr chainBufPtr ∗
      ((g.inPtr + 0x60#64) ↦ₛ g.post248) ∗
      (memRegion (s0.sp - 4576#64) 480 ∗ stackAt s0.sp allocHookStack) ∗
      A.pool lim (M.stepEvents withReceiverChainEmptyEvents st) sf

set_option maxHeartbeats 4000000 in
theorem withReceiverChain_empty_placed_ok_of_session [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_30).rebase (blkPl_30).base H) (blkPl_30).base
      (withLsCodeLoaded lsmpl (withReceiverChainEmptyPlacedSpec M A lim)) := by
  unfold withLsCodeLoaded withReceiverChainEmptyPlacedSpec withReceiverChainEmptyEvents
  simp only [stackAt_withReceiverChain_entry]
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  have hser := ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_30).rebase (blkPl_30).base H)
    (ecPubKeySerialize_alloc_placed_ok_of_session hshim halloc)
  change subroutine_ok _ (lsmpl.base 205)
    (withLsCl lsmpl (ecPubKeySerializeAllocPlacedSpec M A lim)) at hser
  dsimp only [withLsCl, ecPubKeySerializeAllocPlacedSpec, ecPubKeySerializeAllocEvents] at hser
  have hgrow := ls_subroutine_ok_cl_of_block (callerProg := (blkPC_30).rebase (blkPl_30).base H)
    (growOneChain_zero_region_placed_ok_of_session hshim halloc)
  change subroutine_ok _ (lsmpl.base 43)
    (withLsCl lsmpl (growOneChainZeroRegionPlacedSpec M A lim)) at hgrow
  dsimp only [withLsCl, growOneChainZeroRegionPlacedSpec, growOneChainZeroEvents] at hgrow
  have hshim' : subroutine_ok ((blkPC_30).rebase (blkPl_30).base H)
      (lsρ lsRustNoAllocShimSym) sessionShimBudgetSpec := ls_hook_ok_of_mem hshim
  have halloc0 : subroutine_ok ((blkPC_30).rebase (blkPl_30).base H)
      (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false) := ls_hook_ok_of_mem halloc
  have halloc' : subroutine_ok ((blkPC_30).rebase (blkPl_30).base H)
      (lsρ lsRustAllocSym) (rustCliAllocNoOomExternSpecWithStack M A lim false allocHookStack) :=
    subroutine_ok_rustCliAllocNoOom_externWithStack (stk := allocHookStack)
      (by decide) (by decide) (subroutine_ok_allocNoOom_of_budget halloc0)
  have hdealloc' := dealloc_bytes_placed_ok (prog := (blkPC_30).rebase (blkPl_30).base H) hdealloc
  have hmemcpy' : subroutine_ok ((blkPC_30).rebase (blkPl_30).base H)
      (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec := ls_hook_ok_of_mem hmemcpy
  dsimp only [sessionShimBudgetSpec, CryptoVerification.LibsignalTripleRatchet.sessionShimSpec] at hshim'
  dsimp only [rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomSpecWithStack,
    LibsignalBinary.Heap.RustLayoutOk, CryptoVerification.RustHeap.LayoutOk, ↓reduceIte] at halloc'
  dsimp only [rustDeallocBytesSpec] at hdealloc'
  dsimp only [sessionMemcpyRegionBudgetSpec,
    CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec, memcpyRegionSpec] at hmemcpy'
  wp_init x s0
  rcases x with ⟨⟨outPtr, inPtr, senderRatchetPubPtr, senderRatchetPub32,
    receiverChainKeyPtr, receiverChainKey32, receiverChainIdx, oldVecPtr, pre72, post248⟩, st⟩
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  subst outPtr inPtr senderRatchetPubPtr receiverChainKeyPtr
  have hfe_all : FitsEvents M lim st
      [.alloc 32, .alloc 33, .alloc 33, .free 1 33, .alloc 416] := by
    simpa [growOneChainZeroEvents, rustAllocEvents, rustDeallocEvents] using
      ‹FitsEvents M lim st (rustAllocEvents 32 1 ++ rustAllocEvents 33 1 ++
        rustAllocEvents 33 1 ++ rustDeallocEvents 33 1 ++ growOneChainZeroEvents)›
  rcases hfe_all with ⟨hfe1, hfe2, hfe3, -, hfe4, -⟩
  let st1 := M.stepEvents (rustAllocEvents 32 1) st
  let st2 := M.stepEvents (rustAllocEvents 33 1) st1
  let st3 := M.stepEvents (rustAllocEvents 33 1) st2
  let st4 := M.stepEvents (rustDeallocEvents 33 1) st3
  have hlen_ck : (bytesToBv8 receiverChainKey32).length = 32 := by
    simp [bytesToBv8, ‹receiverChainKey32.length = 32›]
  obtain ⟨ck0, ck1, ck2, ck3, _, hck_cells⟩ := exists_unpack64_of_length_32 hlen_ck
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hpos32 : 0 < (32 : Nat) := by decide
  have hpos33 : 0 < (33 : Nat) := by decide
  have hal1 : (1 : Nat) ≤ 2 ^ 31 := by decide
  have hsum32 : (32 : Nat) + 1 ≤ 2 ^ 63 := by decide
  have hsum33 : (33 : Nat) + 1 ≤ 2 ^ 63 := by decide
  apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 205)
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_call hshim' ()
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc' (32, 1, st)
  have hne1 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq1 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne1
  have hm32_1 : memRegion (sf_1.readReg64 (Reg.gpr 0#5)) 32 =
      cells (sf_1.readReg64 (Reg.gpr 0#5)) 4 :=
    memRegion_cells (sf_1.readReg64 (Reg.gpr 0#5)) 4 (by decide)
  simp only [hm32_1, cells, sepConj_emp, sepExists_sepConj_left,
    sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWP.exists_elim fun u0 => SepWP.exists_elim fun u1 =>
    SepWP.exists_elim fun u2 => SepWP.exists_elim fun u3 => ?_
  rw [hck_cells (s0.readReg64 (.gpr 2#5))]
  wp_steps_sync_pool (lsmpl.base 205)
  simp only [State.setMem_setMem, hck_cells, sepConj_assoc]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl1
  wp_call hser ((s0.readReg64 (.gpr 1#5), senderRatchetPub32), st1)
  have hcl2 : LibsignalCodeLoaded lsmpl sf_2.mem := by assumption
  have henc33 : (encodeEC senderRatchetPub32).length = 33 := by
    change (0x05 :: senderRatchetPub32).length = 33; simp [‹senderRatchetPub32.length = 32›]
  have hlen_pub33 : (bytesToBv8 (encodeEC senderRatchetPub32)).length = 33 := by
    simp [bytesToBv8, henc33]
  apply sepWP_seq_lscl hcl2 (mid := lsmpl.base 43)
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_call hshim' ()
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_3› (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc' (33, 1, st2)
  have hne2 : sf_4.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq2 : (sf_4.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne2
  wp_steps_sync_pool (lsρ lsMemcpySym)
  simp only [State.setMem_setMem]
  rw [← hlen_pub33]
  wp_call hmemcpy' (sf_4.readReg64 (Reg.gpr 0#5), _, bytesToBv8 (encodeEC senderRatchetPub32))
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_5› (hnext := ?_)
  simp only [hlen_pub33, henc33]
  wp_steps_sync_pool (lsρ lsRustDeallocSym)
  simp only [State.setMem_setMem]
  wp_call hdealloc' ((_, bytesToBv8 (encodeEC senderRatchetPub32), 33, 1), st3)
  wp_steps_sync_pool (lsmpl.base 43)
  simp only [State.setMem_setMem]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl3
  wp_call hgrow ((s0.readReg64 (.gpr 0#5) + 0x48#64, oldVecPtr), st4)
  simp only [memRegion_416_receiverChain_split w_1, cells, sepConj_emp,
    sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  repeat (refine SepWP.exists_elim fun _ => ?_)
  wp_steps_sync_pool (lsρ lsMemcpySym)
  simp only [State.setMem_setMem]
  have hpack_in := withReceiverChain_pack344_unfolded (s0.readReg64 (.gpr 0#5))
    w_1 pre72 post248 ‹pre72.length = 72›
  have hlen_full : (pre72 ++ (receiverChainVecBytes24 w_1 ++ post248)).length = 344 := by
    simp [‹pre72.length = 72›, ‹post248.length = 248›]
  refine sepWP_focus (T :=
    (s0.readReg64 (.gpr 0#5) ↦ₛ pre72) ∗ ((s0.readReg64 (.gpr 0#5) + 0x48#64) ↦₆₄ 4#64) ∗
    ((s0.readReg64 (.gpr 0#5) + 0x50#64) ↦₆₄ w_1) ∗
    ((s0.readReg64 (.gpr 0#5) + 0x58#64) ↦₆₄ 1#64) ∗
    ((s0.readReg64 (.gpr 0#5) + 0x60#64) ↦ₛ post248)) (by sep_focus) ?_
  rw [hpack_in, ← hlen_full]
  wp_call hmemcpy' (s0.readReg64 (.gpr 8#5), s0.readReg64 (.gpr 0#5),
    pre72 ++ (receiverChainVecBytes24 w_1 ++ post248))
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_8› (hnext := ?_)
  simp only [← withReceiverChain_pack344 _ _ _ _ ‹pre72.length = 72›]
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  unfold receiverChainElemAt receiverChainVecFieldsAt
  simp only [State.setMem_setMem, sepConj_assoc]
  wp_done

theorem withReceiverChain_empty_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok ((blkPC_30).rebase (blkPl_30).base H) (blkPl_30).base
      (withLsCodeLoaded lsmpl (withReceiverChainEmptyPlacedSpec M A lim)) :=
  withReceiverChain_empty_placed_ok_of_session
    (hookSat_sessionShimBudget_of_rustAllocShimVm hshim) halloc hdealloc
    (hookSat_sessionMemcpyRegionBudget_of_allocMemcpyVm hmemcpy)

/-! ## 9. `<PublicKey>::serialize` Raw-Stack Variant (Block `205`) -/

def ecPubKeySerializeRawPlacedSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec ((BitVec 64 × Bytes) × M.σ) where
  pre := fun ((keyPtr, keyBytes), st) s =>
    ⌜s.readReg64 .x0 = keyPtr ∧ keyBytes.length = 32 ∧
      FitsEvents M lim st ecPubKeySerializeAllocEvents⌝ ∗
      (keyPtr ↦ₛ bytesToBv8 keyBytes) ∗ stackAt (s.sp - 32#64) allocHookStack ∗
      cells (s.sp - 32#64) 4 ∗ A.pool lim st s
  post := fun ((keyPtr, keyBytes), st) s0 sf =>
    ∃∗ slicePtr : BitVec 64,
      ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = slicePtr ∧ sf.readReg64 .x1 = 33#64 ∧
        slicePtr ≠ 0⌝ ∗
      (keyPtr ↦ₛ bytesToBv8 keyBytes) ∗ (slicePtr ↦ₛ bytesToBv8 (encodeEC keyBytes)) ∗
      A.live slicePtr 33 1 ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
      cells (s0.sp - 32#64) 4 ∗ A.pool lim (M.stepEvents ecPubKeySerializeAllocEvents st) sf

theorem ecPubKeySerializeRaw_placed_ok_of_session [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_205).rebase (blkPl_205).base H) (blkPl_205).base
      (ecPubKeySerializeRawPlacedSpec M A lim) := by
  refine subroutine_ok_mono (ecPubKeySerialize_alloc_placed_ok_of_session hshim halloc) ?_ ?_
  · intro g R s0 hp
    simpa only [ecPubKeySerializeRawPlacedSpec, ecPubKeySerializeAllocPlacedSpec,
      stackAt_privKeySerialize, sepConj_assoc] using hp
  · intro g R s0 sf hq
    simpa only [ecPubKeySerializeRawPlacedSpec, ecPubKeySerializeAllocPlacedSpec,
      stackAt_privKeySerialize, sepConj_assoc] using hq

theorem ecPubKeySerializeRaw_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_205).rebase (blkPl_205).base H) (blkPl_205).base
      (ecPubKeySerializeRawPlacedSpec M A lim) :=
  ecPubKeySerializeRaw_placed_ok_of_session
    (hookSat_sessionShimBudget_of_rustAllocShimVm hshim) halloc

/-! ## 10. `<SessionState>::set_unacknowledged_pre_key_message` (Block `33`) -/

abbrev cryptoLeafStubBudgetSpec (fn : Bytes → Bytes) (inLen outLen : Nat) : Spec CryptoLeafCall :=
  withVmPreserved (cryptoLeafStubSpec fn inLen outLen)

private def twoWordsToBytes (w0 w1 : BitVec 64) : Bytes :=
  (unpack64 w0 ++ unpack64 w1).map fun b => UInt8.ofNat b.toNat

private theorem twoWordsToBytes_length (w0 w1 : BitVec 64) :
    (twoWordsToBytes w0 w1).length = 16 := by
  simp [twoWordsToBytes, unpack64]

private theorem bytesToBv8_twoWordsToBytes (w0 w1 : BitVec 64) :
    bytesToBv8 (twoWordsToBytes w0 w1) = unpack64 w0 ++ unpack64 w1 := by
  simp only [twoWordsToBytes, bytesToBv8, List.map_map]
  have h_id : ((fun b : UInt8 => BitVec.ofNat 8 b.toNat) ∘ fun b : BitVec 8 =>
      UInt8.ofNat b.toNat) = id := by
    funext x
    apply BitVec.eq_of_toNat_eq
    have hx : x.toNat < 256 := x.isLt
    change (x.toNat % 256) % 256 = x.toNat
    omega
  rw [h_id, List.map_id]

private theorem pointsTo64_pair_eq_twoWords (a w0 w1 : BitVec 64) :
    ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1)) = (a ↦ₛ bytesToBv8 (twoWordsToBytes w0 w1)) := by
  rw [bytesToBv8_twoWordsToBytes, pointsToBytes_append, unpack64_length,
    ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes]

private theorem fitBv8_16_twoWords (w0 w1 : BitVec 64) :
    fitBv8 16 (id (twoWordsToBytes w0 w1)) = bytesToBv8 (twoWordsToBytes w0 w1) := by
  have hlen : (bytesToBv8 (twoWordsToBytes w0 w1)).length = 16 := by
    simp [bytesToBv8, twoWordsToBytes_length]
  simp [fitBv8, hlen, List.take_of_length_le (Nat.le_of_eq hlen)]

private theorem pointsTo64_pair_entails_memRegion16 (a u3 u4 : BitVec 64) :
    ((a ↦₆₄ u3) ∗ ((a + 8#64) ↦₆₄ u4)) ⊢ memRegion a 16 := by
  rw [show (16 : Nat) = 8 + 8 by decide, memRegion_split a 8 8 (by decide),
    memRegion_eight, memRegion_eight]
  exact sepConj_mono (Entails.sepExists_intro u3) (Entails.sepExists_intro u4)

private theorem memRegion_40_unack_split (statePtr : BitVec 64) :
    memRegion (statePtr + 0x100#64) 40 =
      (∃∗ w100 : BitVec 64, (statePtr + 0x100#64) ↦₆₄ w100) ∗
      (∃∗ w108 : BitVec 64, (statePtr + 0x108#64) ↦₆₄ w108) ∗
      (∃∗ w110 : BitVec 32, (statePtr + 0x110#64) ↦₃₂ w110) ∗
      (∃∗ w114 : BitVec 32, (statePtr + 0x114#64) ↦₃₂ w114) ∗
      (∃∗ w118 : BitVec 64, (statePtr + 0x118#64) ↦₆₄ w118) ∗
      (∃∗ w120 : BitVec 32, (statePtr + 0x120#64) ↦₃₂ w120) ∗
      memRegion (statePtr + 0x124#64) 4 := by
  rw [memRegion_split (statePtr + 0x100#64) 8 32 (by decide),
    memRegion_split (statePtr + 0x100#64 + 8#64) 8 24 (by decide),
    memRegion_split (statePtr + 0x100#64 + 8#64 + 8#64) 4 20 (by decide),
    memRegion_split (statePtr + 0x100#64 + 8#64 + 8#64 + 4#64) 4 16 (by decide),
    memRegion_split (statePtr + 0x100#64 + 8#64 + 8#64 + 4#64 + 4#64) 8 8 (by decide),
    memRegion_split (statePtr + 0x100#64 + 8#64 + 8#64 + 4#64 + 4#64 + 8#64) 4 4 (by decide),
    memRegion_eight, memRegion_eight, ProofLib.memRegion_four, ProofLib.memRegion_four,
    memRegion_eight, ProofLib.memRegion_four]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem unack_tail24_entails_memRegion (statePtr : BitVec 64)
    (v110 v114 v120 : BitVec 32) (v118 : BitVec 64) :
    ((statePtr + 0x110#64) ↦₃₂ v110) ∗ ((statePtr + 0x114#64) ↦₃₂ v114) ∗
      ((statePtr + 0x118#64) ↦₆₄ v118) ∗ ((statePtr + 0x120#64) ↦₃₂ v120) ∗
      memRegion (statePtr + 0x124#64) 4 ⊢ memRegion (statePtr + 0x110#64) 24 := by
  refine Entails.trans
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
      (sepConj_mono (pointsTo32_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono_left (pointsTo32_entails_memRegion _ _))))) ?_
  rw [memRegion_split (statePtr + 0x110#64) 4 20 (by decide),
    memRegion_split (statePtr + 0x110#64 + 4#64) 4 16 (by decide),
    memRegion_split (statePtr + 0x110#64 + 4#64 + 4#64) 8 8 (by decide),
    memRegion_split (statePtr + 0x110#64 + 4#64 + 4#64 + 8#64) 4 4 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.refl _

private theorem stackAt_setUnack_call (sp : BitVec 64) :
    stackAt (sp - 144#64) (allocHookStack + 32) =
      stackAt (sp - 176#64) allocHookStack ∗ cells (sp - 176#64) 4 := by
  have h1 := stackAt_split_cells (sp - 144#64) allocHookStack 4 (by decide)
  have h2 : sp - 144#64 - BitVec.ofNat 64 (8 * 4) = sp - 176#64 := by bv_arith
  rw [h2] at h1
  exact h1

private theorem stackAt_setUnack_hooks (sp : BitVec 64) :
    stackAt (sp - 176#64) allocHookStack ∗ cells (sp - 176#64) 4 =
      memRegion (sp - 4272#64) 32 ∗ stackAt (sp - 144#64) allocHookStack := by
  rw [← stackAt_setUnack_call sp]
  have h1 := stackAt_split_top (sp - 144#64) 32 allocHookStack (by decide)
  have h2 : (32 + allocHookStack : Nat) = allocHookStack + 32 := by decide
  have h3 : BitVec.ofNat 64 (32 + allocHookStack) = 4128#64 := rfl
  have h4 : sp - 144#64 - 4128#64 = sp - 4272#64 := by bv_arith
  rw [h3, h4] at h1
  rw [← h2, h1]

@[local simp, local wp_norm, local arm64_norm]
private theorem cond_lt_subs_neg1_1_true :
    ConditionHolds CondCode.LT (subsPState64 0xffffffffffffffff#64 1#64) = true := by
  simp only [ConditionHolds, subsPState64]; decide

def setUnackPreKeyMsgEvents : List AllocEvent :=
  rustAllocEvents 33 1 ++ rustAllocEvents 33 1 ++ rustDeallocEvents 33 1

def SetUnackPreKeyMsgEnv (evs : List AllocEvent) : Prop :=
  evs = setUnackPreKeyMsgEvents

def setUnackPreKeyMsgPlacedSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec ((BitVec 64 × BitVec 64 × Bytes) × M.σ) where
  pre := fun ((statePtr, baseKeyPtr, baseKeyBytes), st) s =>
    ⌜s.readReg64 .x0 = statePtr ∧ s.readReg64 .x4 = baseKeyPtr ∧ baseKeyBytes.length = 32 ∧
      FitsEvents M lim st setUnackPreKeyMsgEvents⌝ ∗
    (baseKeyPtr ↦ₛ bytesToBv8 baseKeyBytes) ∗ ((statePtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) ∗
    memRegion (statePtr + 0x100#64) 40 ∗ stackAt (s.sp - 144#64) (allocHookStack + 32) ∗
    cells (s.sp - 144#64) 18 ∗ A.pool lim st s
  post := fun ((statePtr, baseKeyPtr, baseKeyBytes), st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (baseKeyPtr ↦ₛ bytesToBv8 baseKeyBytes) ∗
    vecU8 A.repAlloc (statePtr + 0xf8#64) (bytesToBv8 (encodeEC baseKeyBytes)) ∗
    memRegion (statePtr + 0x110#64) 24 ∗
    stackAt (s0.sp - 144#64) (allocHookStack + 32) ∗
    cells (s0.sp - 144#64) 18 ∗
    A.pool lim (M.stepEvents setUnackPreKeyMsgEvents st) sf

set_option maxHeartbeats 4000000 in
theorem setUnackPreKeyMsg_placed_ok_of_session [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hTime : HookSat H lsSystemTimeDurationSinceSym (cryptoLeafStubBudgetSpec id 16 16)) :
    subroutine_ok ((blkPC_33).rebase (blkPl_33).base H) (blkPl_33).base
      (withLsCodeLoaded lsmpl (setUnackPreKeyMsgPlacedSpec M A lim)) := by
  unfold withLsCodeLoaded setUnackPreKeyMsgPlacedSpec setUnackPreKeyMsgEvents
  have hser : subroutine_ok ((blkPC_33).rebase (blkPl_33).base H) (lsmpl.base 205)
      (withLsCl lsmpl (ecPubKeySerializeRawPlacedSpec M A lim)) :=
    ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_33).rebase (blkPl_33).base H)
      (ecPubKeySerializeRaw_placed_ok_of_session hshim halloc)
  dsimp only [withLsCl, ecPubKeySerializeRawPlacedSpec, ecPubKeySerializeAllocEvents] at hser
  have hshim' : subroutine_ok ((blkPC_33).rebase (blkPl_33).base H)
      (lsρ lsRustNoAllocShimSym) sessionShimBudgetSpec := ls_hook_ok_of_mem hshim
  have halloc0 : subroutine_ok ((blkPC_33).rebase (blkPl_33).base H)
      (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false) := ls_hook_ok_of_mem halloc
  have halloc' : subroutine_ok ((blkPC_33).rebase (blkPl_33).base H)
      (lsρ lsRustAllocSym) (rustCliAllocNoOomExternSpecWithStack M A lim false allocHookStack) :=
    subroutine_ok_rustCliAllocNoOom_externWithStack (stk := allocHookStack)
      (by decide) (by decide) (subroutine_ok_allocNoOom_of_budget halloc0)
  have hdealloc' := dealloc_bytes_placed_ok (prog := (blkPC_33).rebase (blkPl_33).base H) hdealloc
  have hmemcpy' : subroutine_ok ((blkPC_33).rebase (blkPl_33).base H)
      (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec := ls_hook_ok_of_mem hmemcpy
  have htime' : subroutine_ok ((blkPC_33).rebase (blkPl_33).base H)
      (lsρ lsSystemTimeDurationSinceSym) (cryptoLeafStubBudgetSpec id 16 16) :=
    ls_hook_ok_of_mem hTime
  dsimp only [sessionShimBudgetSpec, CryptoVerification.LibsignalTripleRatchet.sessionShimSpec] at hshim'
  dsimp only [rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomSpecWithStack,
    LibsignalBinary.Heap.RustLayoutOk, CryptoVerification.RustHeap.LayoutOk, ↓reduceIte] at halloc'
  dsimp only [rustDeallocBytesSpec] at hdealloc'
  dsimp only [sessionMemcpyRegionBudgetSpec,
    CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec, memcpyRegionSpec] at hmemcpy'
  dsimp only [cryptoLeafStubBudgetSpec, withVmPreserved, cryptoLeafStubSpec] at htime'
  wp_init x s0
  rcases x with ⟨⟨statePtr, baseKeyPtr, baseKeyBytes⟩, st⟩
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  subst statePtr baseKeyPtr
  have hfe_all : FitsEvents M lim st [.alloc 33, .alloc 33, .free 1 33] := by
    simpa [rustAllocEvents, rustDeallocEvents] using
      ‹FitsEvents M lim st (rustAllocEvents 33 1 ++ rustAllocEvents 33 1 ++ rustDeallocEvents 33 1)›
  rcases hfe_all with ⟨hfe1, hfe2, -, -⟩
  let st1 := M.stepEvents (rustAllocEvents 33 1) st
  let st2 := M.stepEvents (rustAllocEvents 33 1) st1
  have henc33 : (encodeEC baseKeyBytes).length = 33 := by
    change (0x05 :: baseKeyBytes).length = 33; simp [‹baseKeyBytes.length = 32›]
  have hlen_enc : (bytesToBv8 (encodeEC baseKeyBytes)).length = 33 := by
    simp [bytesToBv8, henc33]
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hpos33 : 0 < (33 : Nat) := by decide
  have hal1 : (1 : Nat) ≤ 2 ^ 31 := by decide
  have hsum33 : (33 : Nat) + 1 ≤ 2 ^ 63 := by decide
  rw [memRegion_40_unack_split (s0.readReg64 (.gpr 0#5))]
  cells_pre_unfold_fast
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun c0 => SepWP.exists_elim fun c1 => SepWP.exists_elim fun c2 => ?_
  repeat (refine SepWP.exists_elim fun _ => ?_)
  rw (occs := .pos [1]) [stackAt_setUnack_call s0.sp]
  rw [pointsTo64_split32' (s0.sp - 128#64)]
  simp only [bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 205)
  wp_steps_sync_pool (lsmpl.base 205)
  simp only [State.setMem_setMem]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl1
  wp_call hser ((s0.readReg64 (.gpr 4#5), baseKeyBytes), st)
  apply SepWP.replace_pre (by sep_focus) (Entails.of_eq (stackAt_setUnack_hooks s0.sp))
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_call hshim' ()
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_1› (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc' (33, 1, st1)
  have hne : sf_2.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq : (sf_2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne
  wp_steps_sync_pool (lsρ lsMemcpySym)
  simp only [State.setMem_setMem]
  rw [← hlen_enc]
  wp_call hmemcpy' (sf_2.readReg64 (Reg.gpr 0#5), _, bytesToBv8 (encodeEC baseKeyBytes))
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_3› (hnext := ?_)
  simp only [hlen_enc, henc33]
  wp_steps_sync_pool (lsρ lsSystemTimeDurationSinceSym)
  simp only [State.setMem_setMem]
  have h128_eq : s0.sp - 128#64 + 4#64 = s0.sp - 124#64 := by bv_arith
  have h136_eq : s0.sp - 136#64 + 8#64 = s0.sp - 128#64 := by bv_arith
  have h120_eq : s0.sp - 120#64 + 8#64 = s0.sp - 112#64 := by bv_arith
  apply SepWP.replace_pre (by sep_focus)
    (Entails.of_eq (h128_eq ▸ pointsTo32_pair (s0.sp - 128#64) _ _))
  apply SepWP.replace_pre (by sep_focus)
    (Entails.of_eq (h136_eq ▸ pointsTo64_pair_eq_twoWords (s0.sp - 136#64) _ _))
  apply SepWP.replace_pre (by sep_focus)
    (h120_eq ▸ pointsTo64_pair_entails_memRegion16 (s0.sp - 120#64) _ _)
  have hlen_tw := twoWordsToBytes_length (s0.readReg64 (.gpr 5#5))
    (BitVec.extractLsb' 32 32 c2 ++ BitVec.truncate 32 (s0.readReg64 (.gpr 6#5)))
  wp_call htime' ⟨s0.sp - 136#64, twoWordsToBytes (s0.readReg64 (.gpr 5#5))
    (BitVec.extractLsb' 32 32 c2 ++ BitVec.truncate 32 (s0.readReg64 (.gpr 6#5))), s0.sp - 120#64⟩
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_4› (hnext := ?_)
  rw [fitBv8_16_twoWords, ← pointsTo64_pair_eq_twoWords (s0.sp - 136#64),
    ← pointsTo64_pair_eq_twoWords (s0.sp - 120#64), h136_eq, h120_eq]
  wp_steps_sync_pool (lsρ lsRustDeallocSym)
  rw [show sf_3.sp = sf_4.sp by simp only [*, arm64_norm]]
  simp only [State.setMem_setMem]
  wp_call hdealloc' ((_, bytesToBv8 (encodeEC baseKeyBytes), 33, 1), st2)
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  simp only [State.setMem_setMem]
  apply SepWP.replace_pre (by sep_focus)
    (unack_tail24_entails_memRegion (s0.readReg64 (.gpr 0#5)) _ _ _ _)
  simp only [*] at *
  apply SepWP.replace_pre (by sep_focus)
    (Entails.of_eq ((stackAt_setUnack_call s0.sp).trans (stackAt_setUnack_hooks s0.sp)).symm)
  dsimp only [st2, st1]
  simp only [vecU8, A.repAlloc_live, AllocCostModel.stepEvents_append]
  cells_unfold
  wp_done

theorem setUnackPreKeyMsg_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym allocMemcpyVmSpec)
    (hTime : HookSat H lsSystemTimeDurationSinceSym (cryptoLeafStubBudgetSpec id 16 16)) :
    subroutine_ok ((blkPC_33).rebase (blkPl_33).base H) (blkPl_33).base
      (withLsCodeLoaded lsmpl (setUnackPreKeyMsgPlacedSpec M A lim)) :=
  setUnackPreKeyMsg_placed_ok_of_session
    (hookSat_sessionShimBudget_of_rustAllocShimVm hshim) halloc hdealloc
    (hookSat_sessionMemcpyRegionBudget_of_allocMemcpyVm hmemcpy) hTime

end LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SessionStateCalleesBudget
