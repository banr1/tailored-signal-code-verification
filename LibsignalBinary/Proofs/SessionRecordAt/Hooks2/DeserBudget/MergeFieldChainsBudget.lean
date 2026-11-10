/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean -- shake: keep
public meta import ProofLib -- shake: keep
public meta import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.HookLift
public meta import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.GrowOne104Budget
public meta import LibsignalBinary.Proofs.Placed.BridgeReloc
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.ChainBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldBasicBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenSenderChain
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenReceiverChains
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.MergeSenderChainAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.MergeReceiverChains
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.MergeReceiverChainsAux.Base
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.MergeReceiverChainsAux.Steps
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.MergeFieldGenSenderChainExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.MergeFieldGenReceiverChainsExt
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `SessionStructure::merge_field` on Chain Fields and All Tags

Completes `mergeFieldAllQ_budget_placed_ok` for `SessionStructure::merge_field` (Block `15`,
`32,768` B) across all `GenFieldQ` tags (`1–7, 9–11, 13–15`), proving per-field symbolic cost
telescoping (`stepEvents_mergeFieldQ_telescope`), tag `6` (`sender_chain`), and tag `7`
(`receiver_chains` via `chainMergeGen_budget_placed_ok_cl` and `grow_one_104_budget_placed_ok_cl`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 2000000

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldChainsBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (maxReceiverChains)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks IsLsBlockProg
  LibsignalCodeLoaded LibsignalRoLoaded libsignalRoLoaded_of_keepsFrozen
  withLsCodeLoaded withLsCl lsmpl lsro8_intro
)
open CryptoVerification.RustHeap (
  RustAlloc vecAt vecBuf vecHeader arrayAt arrayAt_concat
)
open CryptoVerification.LibsignalSession (GrowGhost)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalProtoCodec (WireType)
open CryptoVerification.LibsignalTripleRatchet (
  LibsignalCodeRoLoaded withLsCodeRoLoaded extract_withLsCodeRoLoaded sepWPp_seq_lscro
)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  sliceCursorAt sliceCursorAfter
)
open CryptoVerification.LibsignalTripleRatchet.RawByteMove (
  chunks104_6QWAt
)
open CryptoVerification.E2E.Record.Placed (blkPC_15 blkPl_15 lsProg_15)
open CryptoVerification.E2E.Record.DeserializeSeed (
  mergeFieldRodataSym
  savedRegs_senderChain sp_sub_240_aligned_senderChain memRegion96_sender_split_senderChain
  mfSavedRegs_receiverChains mfFramePad_receiverChains sp_sub_240_aligned_receiverChains
  memRegion80_eq_cells10_receiverChains memRegion80_chainInit_eq_cells10_receiverChains
  cells10_entails_memRegion80_receiverChains
  chunks104_6QWAt_stack_eq_receiverChains chunks104_6QWAt_dst_eq_receiverChains
  chunks104_6QWAt_entails_memRegion104_receiverChains
  memRegion104_eq_exists_chunks104_6QWAt_receiverChains
  move_bytes_pair_receiverChains
  zext64_trunc32_and_255_eq_of_trunc8_receiverChains
)
open CryptoVerification.E2E.Record.DeserializeGeneral (
  ChainG SSG GenField ChainMergeGenGhost
)
open CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenSenderChain (
  stackAt_mergeFieldStack_split_senderChain_extW
  stackAt_32688_to_chainMerge_senderChain_extW
)
open CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenReceiverChains (
  ofNat_length_eq_cap_of_eq beq_ofNat_len_cap_false
)
open Proofs.libsignal.Stage1X (growOneChainStackX)
open Proofs.libsignal.Hooks2 (
  mergeFieldStackX mergeFieldSubStackX chainMergeStackX
)
open Symbolic.Swarm.TRREF.B3DeserQ (
  ExtraGQ SSGQ GenFieldQ MergeFieldQGhost
)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits FitsEvents fitsEvents_append
  RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (
  HasFineReallocCredit
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.Potential (
  vecCap4Of vecCap4Next IsPow2Cap4 isPow2Cap4_next
  vec104GrowEvents vec104CumOfCap vec104CumRem vec104LargeLive vec104PeakLarge
  vec104CumOfCap_le_of_pow2 vec104PeakLarge_le_of_pow2 vec104LargeLive_le_peakLarge
  stepEvents_vec104Grow_telescope
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.HookLift (
  AllocContractsBudgetPlaced
)
open scoped LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.GrowOne104Budget
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.GrowOne104Budget (
  sepWP_ret_vmPreserved cap_zero_or_ge_two_of_isPow2Cap4
  growOne104BudgetSpecX grow_one_104_budget_placed_ok_cl
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.ProstMergeBudget (
  sepWPp_seq_lsclro_vm
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.ChainBudget (
  vecU8FreshCap prostChainGAtCap prostChainGAtCap_empty_of_cells
  prostChainGAtCap_move_bytes prostChainGAtCap_move_chunks104
  chainMergeEvents chainMergeSmallCost chainMergeLargeLive chainMergePeakLarge
  stepEvents_chainMerge_bounds
  chainMergeGenBudgetRawSpecW chainMergeGenBudgetSpecW chainMergeGen_budget_placed_ok_cl
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldBasicBudget (
  pendingAt9PCap kyberAtCap prostSSGQAtCap
  prostSSGQScalars prostSSGQRest_recv prostSSGQRest_sender pendingAt9PCap_congr
  IsBasicFieldQ nextCapRecv mergeFieldQEvents mergeFieldQFitsEvents
  basicFieldSmallCost basicFieldLargeLive basicFieldPeakLarge
  stepEvents_mergeFieldBasic_bounds
  GenFieldQ.FreshBytes mergeFieldQBudgetRawSpecW mergeFieldQBudgetSpecW
  mergeFieldQBudget_of_imp mergeFieldQBudget_or
  NoPanicPost sepWPp_pure_left_and sepWPp_exists_left
  sepWP_drop_left_mfb sepWP_intro_ro8_mfb sepWPp_step_0x28_15
  entails_pure_sep_frame entails_rw_stack_4 entails_rw_stack_5
  sepWPp_call_lscl_15 sepWPp_call_lscro_15 subroutine_ok_of_field_sepWPp
  mergeFieldBasic_budget_placed_ok mergeFieldQBudget_caller_ok
)

/-! ## 1. Unified Symbolic Cost Functions & Telescoping Bounds Across All `GenFieldQ` Tags -/

/-- Unified symbolic per-field `cumSmall` charge across all `GenFieldQ` tags (`1–7, 9–11, 13–15`).
For `receiver_chains` (tag `7`), the outer `Vec<Chain>` growth charges telescope separately via
`vec104CumRem M capMaxRecv capRecv` in `stepEvents_mergeFieldQ_telescope`. -/
def fieldQSmallCost (M : AllocCostModel) [HasFineReallocCredit M] (fl : GenFieldQ) : Nat :=
  match fl with
  | .base (.sender c) => chainMergeSmallCost M c
  | .base (.recv c) => chainMergeSmallCost M c
  | fl => basicFieldSmallCost M fl

/-- Unified symbolic post-merge direct-`mmap` live cost added to `SessionStructure` fields
(excluding the outer `receiver_chains` `Vec<Chain>` buffer, tracked via `vec104LargeLive M capRecv`). -/
def fieldQLargeLive (M : AllocCostModel) [HasFineReallocCredit M] (fl : GenFieldQ) : Nat :=
  match fl with
  | .base (.sender c) => chainMergeLargeLive M c
  | .base (.recv c) => chainMergeLargeLive M c
  | fl => basicFieldLargeLive M fl

/-- Unified symbolic transient direct-`mmap` peak of merging field `fl` itself
(before any outer `receiver_chains` `grow_one<Chain>` step). -/
def fieldQPeakLarge (M : AllocCostModel) [HasFineReallocCredit M] (fl : GenFieldQ) : Nat :=
  match fl with
  | .base (.sender c) => chainMergePeakLarge M c
  | .base (.recv c) => chainMergePeakLarge M c
  | fl => basicFieldPeakLarge M fl

@[simp]
theorem fieldQSmallCost_sender (M : AllocCostModel) [HasFineReallocCredit M] (c : ChainG) :
    fieldQSmallCost M (.base (.sender c)) = chainMergeSmallCost M c := rfl

@[simp]
theorem fieldQSmallCost_recv (M : AllocCostModel) [HasFineReallocCredit M] (c : ChainG) :
    fieldQSmallCost M (.base (.recv c)) = chainMergeSmallCost M c := rfl

@[simp]
theorem fieldQLargeLive_sender (M : AllocCostModel) [HasFineReallocCredit M] (c : ChainG) :
    fieldQLargeLive M (.base (.sender c)) = chainMergeLargeLive M c := rfl

@[simp]
theorem fieldQLargeLive_recv (M : AllocCostModel) [HasFineReallocCredit M] (c : ChainG) :
    fieldQLargeLive M (.base (.recv c)) = chainMergeLargeLive M c := rfl

theorem fieldQCost_of_basic (M : AllocCostModel) [HasFineReallocCredit M]
    {fl : GenFieldQ} (hb : IsBasicFieldQ fl) :
    fieldQSmallCost M fl = basicFieldSmallCost M fl ∧
    fieldQLargeLive M fl = basicFieldLargeLive M fl ∧
    fieldQPeakLarge M fl = basicFieldPeakLarge M fl := by
  rcases hb with ⟨h6, h7⟩
  cases fl with
  | base f =>
    cases f with
    | sender _ => exact False.elim (h6 rfl)
    | recv _ => exact False.elim (h7 rfl)
    | _ => exact ⟨rfl, rfl, rfl⟩
  | _ => exact ⟨rfl, rfl, rfl⟩

/-- Master per-field symbolic telescoping theorem for `SessionStructure::merge_field` across
all `GenFieldQ` tags (`1–7, 9–11, 13–15`):
Suppose `capRecv` and `capMaxRecv` are powers of two (`IsPow2Cap4`), `capRecv ≤ capMaxRecv`,
and when `fl` pushes a new `receiver_chains` element at `curRecvLen = capRecv` we have
`capRecv < capMaxRecv` (e.g. `capMaxRecv = vecCap4Of finalRecvLen` with `curRecvLen < finalRecvLen`).
Then from:
- `cumSmall st + remSmall + fieldQSmallCost M fl + vec104CumRem M capMaxRecv capRecv ≤ C_max`,
- `liveLarge st ≤ L_ss + vec104LargeLive M capRecv`,
- `peakLarge st ≤ P_bound` (where `P_bound` dominates `P₀`, the `fl` merge peak, and
  `(L_ss + fieldQLargeLive M fl) + vec104PeakLarge M capMaxRecv`),
stepping `mergeFieldQEvents capRecv curRecvLen fl` preserves the invariant at
`capRecv' := nextCapRecv capRecv curRecvLen fl` and `L_ss' := L_ss + fieldQLargeLive M fl`. -/
theorem stepEvents_mergeFieldQ_telescope (M : AllocCostModel) [HasFineReallocCredit M]
    {fl : GenFieldQ} (hOk : fl.Ok)
    (h33 : 33 ≤ HasFineReallocCredit.smallMaxReq M)
    {capRecv capMaxRecv curRecvLen remSmall C_max L_ss P_bound : Nat} {st : M.σ}
    (hpow : IsPow2Cap4 capRecv) (hmax : IsPow2Cap4 capMaxRecv) (_hle_max : capRecv ≤ capMaxRecv)
    (hrecv_lt : ∀ c, fl = .base (.recv c) → curRecvLen = capRecv → capRecv < capMaxRecv)
    (hcum : HasFineReallocCredit.cumSmall st + remSmall + fieldQSmallCost M fl +
      vec104CumRem M capMaxRecv capRecv ≤ C_max)
    (hlive : HasFineReallocCredit.liveLarge st ≤ L_ss + vec104LargeLive M capRecv)
    (hpeak : HasFineReallocCredit.peakLarge st ≤ P_bound)
    (hp_fl : L_ss + vec104LargeLive M capRecv + fieldQPeakLarge M fl ≤ P_bound)
    (hp_grow : L_ss + fieldQLargeLive M fl + vec104PeakLarge M capMaxRecv ≤ P_bound) :
    let st' := M.stepEvents (mergeFieldQEvents capRecv curRecvLen fl) st
    let capRecv' := nextCapRecv capRecv curRecvLen fl
    HasFineReallocCredit.cumSmall st' + remSmall +
      vec104CumRem M capMaxRecv capRecv' ≤ C_max ∧
    HasFineReallocCredit.liveLarge st' ≤
      (L_ss + fieldQLargeLive M fl) + vec104LargeLive M capRecv' ∧
    HasFineReallocCredit.peakLarge st' ≤ P_bound := by
  have h8 : 8 ≤ HasFineReallocCredit.smallMaxReq M := by omega
  by_cases h6 : fl.tag = 6
  · have ⟨c, hfl⟩ : ∃ c : ChainG, fl = .base (.sender c) := by
      cases fl with
      | base f => cases f <;> simp [GenFieldQ.tag, GenField.tag] at h6; exact ⟨_, rfl⟩
      | _ => simp [GenFieldQ.tag] at h6
    subst hfl
    have hcOk : c.Ok := hOk.1
    obtain ⟨hc, hl, hp⟩ := stepEvents_chainMerge_bounds M hcOk h33 st
    dsimp only [mergeFieldQEvents, nextCapRecv, fieldQSmallCost, fieldQLargeLive,
      fieldQPeakLarge] at hcum hp_fl ⊢
    refine ⟨by omega, by omega, ?_⟩
    exact Nat.le_trans hp (Nat.max_le.mpr ⟨hpeak, by omega⟩)
  · by_cases h7 : fl.tag = 7
    · have ⟨c, hfl⟩ : ∃ c : ChainG, fl = .base (.recv c) := by
        cases fl with
        | base f => cases f <;> simp [GenFieldQ.tag, GenField.tag] at h7; exact ⟨_, rfl⟩
        | _ => simp [GenFieldQ.tag] at h7
      subst hfl
      have hcOk : c.Ok := hOk.1
      dsimp only [mergeFieldQEvents, nextCapRecv, fieldQSmallCost, fieldQLargeLive,
        fieldQPeakLarge] at hcum hp_fl hp_grow ⊢
      rw [AllocCostModel.stepEvents_append]
      obtain ⟨hc1, hl1, hp1⟩ := stepEvents_chainMerge_bounds M hcOk h33 st
      set st_mid := M.stepEvents (chainMergeEvents c) st
      have hp_mid : HasFineReallocCredit.peakLarge st_mid ≤ P_bound :=
        Nat.le_trans hp1 (Nat.max_le.mpr ⟨hpeak, by omega⟩)
      by_cases hfull : curRecvLen = capRecv
      · have hlt_max : capRecv < capMaxRecv := hrecv_lt c rfl hfull
        simp only [hfull, ↓reduceIte]
        have htel := stepEvents_vec104Grow_telescope M
          (cap := capRecv) (capMax := capMaxRecv)
          (C_max := C_max - remSmall)
          (L_other := L_ss + chainMergeLargeLive M c)
          (P₀ := P_bound) (st := st_mid)
          hpow hmax hlt_max (by omega) (by omega)
          (Nat.le_trans hp_mid (Nat.le_max_left _ _))
        have hrem_le : remSmall ≤ C_max := by omega
        refine ⟨by omega, htel.2.1, ?_⟩
        exact Nat.le_trans htel.2.2 (Nat.max_le.mpr ⟨Nat.le_refl _, hp_grow⟩)
      · simp only [hfull, ↓reduceIte, AllocCostModel.stepEvents_nil]
        exact ⟨by omega, by omega, hp_mid⟩
    · have hb : IsBasicFieldQ fl := ⟨h6, h7⟩
      obtain ⟨hcs, hcl, hcp⟩ := fieldQCost_of_basic M hb
      have hcap_eq : nextCapRecv capRecv curRecvLen fl = capRecv := by
        cases fl with
        | base f =>
          cases f with
          | sender _ => exact False.elim (h6 rfl)
          | recv _ => exact False.elim (h7 rfl)
          | _ => rfl
        | _ => rfl
      obtain ⟨hc, hl, hp⟩ := stepEvents_mergeFieldBasic_bounds M hb h8 capRecv curRecvLen st
      rw [hcs] at hcum
      rw [hcl]
      rw [hcp] at hp_fl
      rw [hcap_eq]
      refine ⟨by omega, by omega, ?_⟩
      exact Nat.le_trans hp (Nat.max_le.mpr ⟨hpeak, by omega⟩)

/-! ## 2. Local Instruction-Step & Width Normalization Setup for Block `15` -/

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite isCalleeSavedVReg

namespace ChainsVmSimp

@[local arm64_norm, local wp_norm]
theorem calleeSavedVRegs_setPC_pre (s : State) (v : BitVec 64) :
    calleeSavedVRegs (s.setPC v) = calleeSavedVRegs s := rfl

@[local arm64_norm, local wp_norm]
theorem calleeSavedVRegs_setMem_setPC_pre (s : State) (v : BitVec 64) (m : Memory) :
    calleeSavedVRegs ((s.setPC v).setMem m) = calleeSavedVRegs s := rfl

@[local arm64_norm]
theorem bv_add_neg240 (sp0 : BitVec 64) :
    sp0 + bv% (2 ^ 64 - 240) = sp0 - 240#64 := by
  simp only [BitVec.sub_eq_add_neg]; rfl

@[local arm64_norm, local wp_norm]
theorem sp_setPC_pre (s : State) (v : BitVec 64) : (s.setPC v).sp = s.sp := rfl

@[local arm64_norm, local wp_norm]
theorem sp_setMem_setPC_pre (s : State) (v : BitVec 64) (m : Memory) :
    ((s.setPC v).setMem m).sp = s.sp := rfl

@[local arm64_norm, local wp_norm]
theorem readReg64_setPC_pre (s : State) (v : BitVec 64) (r : Reg) :
    (s.setPC v).readReg64 r = s.readReg64 r := rfl

@[local arm64_norm, local wp_norm]
theorem readReg64_setMem_setPC_pre (s : State) (v : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC v).setMem m).readReg64 r = s.readReg64 r := rfl

@[local arm64_norm, local wp_norm]
theorem readReg32_setPC_pre (s : State) (v : BitVec 64) (r : Reg) :
    (s.setPC v).readReg32 r = s.readReg32 r := rfl

@[local arm64_norm, local wp_norm]
theorem readReg32_setMem_setPC_pre (s : State) (v : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC v).setMem m).readReg32 r = s.readReg32 r := rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem tpidrEl0_setPC_pre (s : State) (v : BitVec 64) :
    (s.setPC v).tpidrEl0 = s.tpidrEl0 := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem tpidrEl0_setMem_setPC_pre (s : State) (v : BitVec 64) (m : Memory) :
    ((s.setPC v).setMem m).tpidrEl0 = s.tpidrEl0 := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem mem_setPC_pre (s : State) (v : BitVec 64) :
    (s.setPC v).mem = s.mem := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_pre (s : State) (v : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC v).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_setPC_pre (s : State) (v : BitVec 64) (m : Memory)
    (w : RegWidth) (r : Reg) :
    ((s.setPC v).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

end ChainsVmSimp

attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldBasicBudget.MergeFieldVmSimp.brkStart_setPC
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldBasicBudget.MergeFieldVmSimp.brk_setPC
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldBasicBudget.MergeFieldVmSimp.physMemAvail_setPC
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldBasicBudget.MergeFieldVmSimp.brkStart_advancePC
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldBasicBudget.MergeFieldVmSimp.brk_advancePC
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldBasicBudget.MergeFieldVmSimp.physMemAvail_advancePC
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldBasicBudget.MergeFieldVmSimp.tpidrEl0_advancePC
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldBasicBudget.MergeFieldVmSimp.mem_advancePC
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldBasicBudget.MergeFieldVmSimp.brkStart_setPState
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldBasicBudget.MergeFieldVmSimp.brk_setPState
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldBasicBudget.MergeFieldVmSimp.physMemAvail_setPState
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldBasicBudget.MergeFieldVmSimp.tpidrEl0_setPState
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldBasicBudget.MergeFieldVmSimp.mem_setPState
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldBasicBudget.MergeFieldVmSimp.brkStart_writeReg64
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldBasicBudget.MergeFieldVmSimp.brk_writeReg64
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldBasicBudget.MergeFieldVmSimp.physMemAvail_writeReg64
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldBasicBudget.MergeFieldVmSimp.tpidrEl0_writeReg64
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldBasicBudget.MergeFieldVmSimp.mem_writeReg64
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldBasicBudget.MergeFieldVmSimp.brkStart_writeReg32
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldBasicBudget.MergeFieldVmSimp.brk_writeReg32
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldBasicBudget.MergeFieldVmSimp.physMemAvail_writeReg32
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldBasicBudget.MergeFieldVmSimp.tpidrEl0_writeReg32
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldBasicBudget.MergeFieldVmSimp.mem_writeReg32
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldBasicBudget.MergeFieldVmSimp.brkStart_writeReg
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldBasicBudget.MergeFieldVmSimp.brk_writeReg
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldBasicBudget.MergeFieldVmSimp.physMemAvail_writeReg
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldBasicBudget.MergeFieldVmSimp.tpidrEl0_writeReg
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldBasicBudget.MergeFieldVmSimp.mem_writeReg


/-! ## 3. Tag `6` (`sender_chain` at `ss + 0x90`, Inline `Option<Chain>`) -/

@[local arm64_norm]
private theorem setWidth8_setWidth64_setWidth32_mfc (v : BitVec 64) :
    (((v.setWidth 32).setWidth 64).setWidth 8) = v.setWidth 8 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  omega

private theorem default_cells_entail_prostChainGAtCap (A : RustAlloc) (ss : BitVec 64) :
    ((ss + 144#64) ↦₆₄ 0#64) ∗ ((ss + 152#64) ↦₆₄ 1#64) ∗ ((ss + 160#64) ↦₆₄ 0#64) ∗
      ((ss + 168#64) ↦₆₄ 0#64) ∗ ((ss + 176#64) ↦₆₄ 1#64) ∗ ((ss + 184#64) ↦₆₄ 0#64) ∗
      ((ss + 192#64) ↦₆₄ 0#64) ∗ ((ss + 200#64) ↦₆₄ 8#64) ∗ ((ss + 208#64) ↦₆₄ 0#64) ∗
      ((ss + 216#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (ss + 224#64) 24 ⊢
      prostChainGAtCap A (ss + 0x90#64) 0 ChainG.empty := by
  have h := prostChainGAtCap_empty_of_cells A (ss + 0x90#64) 1#64 1#64 8#64
    (by decide) (by decide) (by decide)
  have e0 : ss + 0x90#64 = ss + 144#64 := rfl
  have e8 : (ss + 144#64) + 8#64 = ss + 152#64 := by rw [BitVec.add_assoc]; rfl
  have e10 : (ss + 144#64) + 0x10#64 = ss + 160#64 := by rw [BitVec.add_assoc]; rfl
  have e18 : (ss + 144#64) + 0x18#64 = ss + 168#64 := by rw [BitVec.add_assoc]; rfl
  have e20 : (ss + 144#64) + 0x20#64 = ss + 176#64 := by rw [BitVec.add_assoc]; rfl
  have e28 : (ss + 144#64) + 0x28#64 = ss + 184#64 := by rw [BitVec.add_assoc]; rfl
  have e30 : (ss + 144#64) + 0x30#64 = ss + 192#64 := by rw [BitVec.add_assoc]; rfl
  have e38 : (ss + 144#64) + 0x38#64 = ss + 200#64 := by rw [BitVec.add_assoc]; rfl
  have e40 : (ss + 144#64) + 0x40#64 = ss + 208#64 := by rw [BitVec.add_assoc]; rfl
  have e48 : (ss + 144#64) + 0x48#64 = ss + 216#64 := by rw [BitVec.add_assoc]; rfl
  have e50 : (ss + 144#64) + 0x50#64 = ss + 224#64 := by rw [BitVec.add_assoc]; rfl
  have hn : noneCap = 0xffffffffffffffff#64 := rfl
  rw [e0, e8, e10, e18, e20, e28, e30, e38, e40, e48, e50, hn] at h
  exact h

set_option maxHeartbeats 800000 in
private theorem step_tag6_sender_mfc [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H)
    (ss bufRef slot ptr : BitVec 64) (c : ChainG) (hcOk : c.Ok)
    (tail : List (BitVec 8)) (st : M.σ) {s0 : State}
    (hpc : s0.pc = (blkPl_15).base) (hrun : s0.status = .Running)
    (hsp_align : s0.spAligned = true)
    (hcl : LibsignalCodeLoaded lsmpl s0.mem) (hro : LibsignalRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = ss)
    (hx1 : (s0.readReg64 .x1).setWidth 32 = 6#32)
    (hx2 : (s0.readReg64 .x2).setWidth 8 = 2#8)
    (hx3 : s0.readReg64 .x3 = bufRef)
    (hx4 : (s0.readReg64 .x4).setWidth 32 = 99#32)
    (hlen : (c.payload ++ tail).length < 2 ^ 62)
    (hfit : FitsEvents M lim st (chainMergeEvents c)) :
    SepWPp (lsProg_15 H) (s0.readReg64 .lr) s0
      ((((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96) ∗
        (bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr (c.payload ++ tail) ∗
        A.pool lim st s0 ∗ stackAt s0.sp mergeFieldStackX)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace ∧
        sf.readReg64 .x0 = 0#64 ∧
        (Pf ⊢ prostChainGAtCap A.repAlloc (ss + 0x90#64) (vecCap4Of c.keys.length) c ∗
          (bufRef ↦₆₄ slot) ∗
          sliceCursorAfter slot ptr (c.payload ++ tail) tail ∗
          A.pool lim (M.stepEvents (chainMergeEvents c) st) sf ∗
          stackAt s0.sp mergeFieldStackX))
      NoPanicPost := by
  have halign : s0.sp &&& 15#64 = 0#64 := by simpa [State.spAligned] using hsp_align
  have hsp240 := sp_sub_240_aligned_senderChain halign
  have hcallC := chainMergeGen_budget_placed_ok_cl (callerProg := lsProg_15 H) hA
  conv =>
    arg 4
    rw [memRegion96_sender_split_senderChain ss]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u1 => SepWPp.exists_elim fun u2 =>
    SepWPp.exists_elim fun u3 => SepWPp.exists_elim fun u4 =>
    SepWPp.exists_elim fun u5 => SepWPp.exists_elim fun u6 =>
    SepWPp.exists_elim fun u7 => SepWPp.exists_elim fun u8 =>
    SepWPp.exists_elim fun u9 => ?_
  conv =>
    arg 4
    rw [stackAt_mergeFieldStack_split_senderChain_extW s0.sp]
    simp only [sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun w80 => SepWPp.exists_elim fun w72 =>
    SepWPp.exists_elim fun w64 => SepWPp.exists_elim fun w56 =>
    SepWPp.exists_elim fun w48 => SepWPp.exists_elim fun w40 =>
    SepWPp.exists_elim fun w32 => SepWPp.exists_elim fun w24 =>
    SepWPp.exists_elim fun w16 => SepWPp.exists_elim fun w8 => ?_
  simp only [arm64_norm] at hx0 hx1 hx2 hx3 hx4
  have hnoneCap : noneCap = 0xffffffffffffffff#64 := rfl
  rw [hnoneCap]
  apply sepWPp_seq_lsclro_vm hcl hro (mid := (blkPl_15).base + 40#64)
  by_vm_steps_withSvc (
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm1 hcl1a hro1a
  rw [← A.pool_transport lim st s0 _ hvm1]
  apply sepWPp_step_0x28_15 hcl1a hro1a
    (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  intro hvm1b hcl1 hro1
  rw [← A.pool_transport lim st _ _ hvm1b]
  apply sepWPp_seq_lsclro_vm hcl1 hro1 (mid := lsmpl.base 11)
  refine sepWP_intro_ro8_mfb (lsmpl.ρ mergeFieldRodataSym + 5#64) 0x32#8
    (fun hm => lsro8_intro hro1 (by lsro_addr) (by decide +kernel) hm) ?_
  by_vm_steps_withSvc (
    wp_steps
    apply sepWP_drop_left_mfb
    apply SepWP.fold (default_cells_entail_prostChainGAtCap A.repAlloc ss) (by sep_frame)
    refine SepWP.done (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm2 hcl2 hro2
  rw [← A.pool_transport lim st _ _ hvm2]
  conv =>
    arg 4
    rw [stackAt_32688_to_chainMerge_senderChain_extW s0.sp]
    simp only [sepConj_assoc]
  refine sepWPp_call_lscro_15
    (x := (ChainMergeGenGhost.mk (ss + 0x90#64) c bufRef slot ptr tail, st))
    hcallC hcl2 hro2
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp240, beq_self_eq_true])
    (by simp only [wp_norm, arm64_norm]; rfl)
    (by
      dsimp only [chainMergeGenBudgetRawSpecW]
      apply entails_pure_sep_frame
      · refine ⟨?_, ?_, ?_, ?_, hcOk, hlen, hfit⟩
        · simp only [wp_norm, arm64_norm, hx2]
        · simp only [wp_norm, arm64_norm]
        · simp only [wp_norm, arm64_norm]
        · simp only [wp_norm, arm64_norm]
      · apply entails_rw_stack_5 (sp2 := s0.sp - 240#64) (w2 := chainMergeStackX)
        · simp only [wp_norm, arm64_norm]
        · rfl
        · sep_frame)
    ?_
  intro sm hpcm hrunm hspm hcsm _hclm _hrom
  dsimp only [chainMergeGenBudgetRawSpecW]
  refine sepWPp_pure_left_and fun ⟨htrm, hx0m⟩ => ?_
  have hx0m' : sm.readReg64 (Reg.gpr 0#5) = 0#64 := hx0m
  have hspm' : sm.sp = s0.sp - 240#64 := by simpa only [wp_norm, arm64_norm] using hspm
  have htrm' : sm.trace = s0.trace := by simpa only [wp_norm, arm64_norm] using htrm
  have hx26m : sm.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := by
    simpa only [wp_norm, arm64_norm] using hcsm.2.2.2.2.2.2.2.1
  have hx27m : sm.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
    simpa only [wp_norm, arm64_norm] using hcsm.2.2.2.2.2.2.2.2.1
  have hx28m : sm.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
    simpa only [wp_norm, arm64_norm] using hcsm.2.2.2.2.2.2.2.2.2.1
  have hvregsm : calleeSavedVRegs sm = calleeSavedVRegs s0 := by
    simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hcsm.2.2.2.2.2.2.2.2.2.2.2
  have hsp_align240 := sp_sub_240_aligned_senderChain halign
  conv =>
    arg 4
    rw [show stackAt _ chainMergeStackX = stackAt (s0.sp - 240#64) chainMergeStackX by
          simp only [wp_norm, arm64_norm]]
    simp only [sepConj_assoc]
  apply SepWPp.of_sepWP_ret
  apply sepWP_ret_vmPreserved
  by_vm_steps_withSvc (
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrunm])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm_end
  rw [← A.pool_transport lim (M.stepEvents (chainMergeEvents c) st) sm _ hvm_end]
  apply SepWP.done (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrunm])
  refine ⟨by simp only [wp_norm, arm64_norm, hspm'],
    by simp only [CalleeSavedPreserved, calleeSavedVRegs, wp_norm, arm64_norm,
      hx26m, hx27m, hx28m, hvregsm, and_self],
    by simp only [wp_norm, arm64_norm, htrm'],
    by simp only [wp_norm, arm64_norm, hx0m'], ?_⟩
  have hstk : stackAt (s0.sp - 80#64) 32688 ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
        ((s0.sp - 56#64) ↦₆₄ w56) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) ⊢
      stackAt s0.sp mergeFieldStackX := by
    rw [stackAt_mergeFieldStack_split_senderChain_extW s0.sp]
    exact sepConj_mono_right
      (Entails.sepExists_right (s0.readReg64 (Reg.gpr 29#5))
        (Entails.sepExists_right (s0.readReg64 (Reg.gpr 30#5))
          (Entails.sepExists_right (s0.readReg64 (Reg.gpr 25#5))
            (Entails.sepExists_right w56
              (Entails.sepExists_right (s0.readReg64 (Reg.gpr 24#5))
                (Entails.sepExists_right (s0.readReg64 (Reg.gpr 23#5))
                  (Entails.sepExists_right (s0.readReg64 (Reg.gpr 22#5))
                    (Entails.sepExists_right (s0.readReg64 (Reg.gpr 21#5))
                      (Entails.sepExists_right (s0.readReg64 (Reg.gpr 20#5))
                        (Entails.sepExists_right (s0.readReg64 (Reg.gpr 19#5))
                          (Entails.refl _)))))))))))
  rw [stackAt_32688_to_chainMerge_senderChain_extW s0.sp] at hstk
  refine Entails.trans (Entails.of_eq ?_)
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hstk))))
  sep_ac_rfl

/-- Relocatable `[LibsignalPlacement]` proof of `SessionStructure::merge_field` (Block `15`,
`lsProg_15 H`, `mergeFieldStackX`) on tag `6` (`sender_chain` at `ss + 0x90`), with
`onPanic := ⌜False⌝` and `onOom := ⌜False⌝`. -/
theorem mergeFieldSenderChain_budget_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H) :
    subroutine_ok (lsProg_15 H) (blkPl_15).base
      (mergeFieldQBudgetSpecW M A lim (fun fl => fl.tag = 6)) := by
  apply subroutine_ok_of_field_sepWPp
  intro x capRecv st s0 hpc hrun hal hcl hro hx0 hx1 hx2 hx3 hx4 hP hOk hFr _hFrB hlen
    _hpow _hle _hcap62 hfit
  generalize x.fld = fld at hx1 hx2 hP hOk hFr hlen hfit ⊢
  cases fld with
  | base f =>
    cases f with
    | sender c =>
      have hcOk : c.Ok := hOk.1
      have hs_none : x.v.base.sender = none := hFr.2
      refine ⟨((x.ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (x.ss + 0x98#64) 96,
        prostChainGAtCap A.repAlloc (x.ss + 0x90#64) (vecCap4Of c.keys.length) c,
        prostSSGQRest_sender A.repAlloc x.ss capRecv x.v, ?_, ?_, ?_⟩
      · unfold prostSSGQAtCap prostSSGQRest_sender prostSSGQScalars
        rw [hs_none]
        dsimp only
        exact Entails.of_eq (by sep_ac_rfl)
      · unfold prostSSGQAtCap nextCapRecv SSGQ.apply prostSSGQRest_sender prostSSGQScalars
        dsimp only [SSG.apply]
        rw [pendingAt9PCap_congr A.repAlloc x.ss rfl rfl rfl]
        exact Entails.of_eq (by sep_ac_rfl)
      · exact step_tag6_sender_mfc hA x.ss x.bufRef x.slot x.ptr c hcOk x.tail st
          hpc hrun hal hcl hro hx0 hx1 hx2 hx3 hx4 hlen hfit
    | _ => simp [GenFieldQ.tag, GenField.tag] at hP
  | _ => simp [GenFieldQ.tag] at hP


/-! ## 4. Tag `7` (`receiver_chains` at `ss + 0x48`, `Vec<Chain>`) -/

private theorem stackAt_sub_to_chainMerge_mfc (sp : BitVec 64) :
    stackAt sp mergeFieldSubStackX =
      memRegion (sp - 32528#64) 3856 ∗ stackAt sp chainMergeStackX := by
  change memRegion (sp - 32528#64) 32528 =
    memRegion (sp - 32528#64) 3856 ∗ memRegion (sp - 28672#64) 28672
  have h3 : (sp - 32528#64) + 3856#64 = sp - 28672#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have hsplit := memRegion_split (sp - 32528#64) 3856 28672 (by decide)
  rw [show (3856 : Nat) + 28672 = 32528 by decide,
      show BitVec.ofNat 64 3856 = 3856#64 from rfl, h3] at hsplit
  exact hsplit

private theorem stackAt_sub_to_growOne_mfc (sp : BitVec 64) :
    stackAt sp mergeFieldSubStackX =
      memRegion (sp - 32528#64) 15632 ∗ stackAt sp growOneChainStackX := by
  change memRegion (sp - 32528#64) 32528 =
    memRegion (sp - 32528#64) 15632 ∗ memRegion (sp - 16896#64) 16896
  have h3 : (sp - 32528#64) + 15632#64 = sp - 16896#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have hsplit := memRegion_split (sp - 32528#64) 15632 16896 (by decide)
  rw [show (15632 : Nat) + 16896 = 32528 by decide,
      show BitVec.ofNat 64 15632 = 15632#64 from rfl, h3] at hsplit
  exact hsplit

private theorem stackAt_mergeFieldStack_split_mfc (sp0 : BitVec 64) :
    stackAt sp0 mergeFieldStackX =
      stackAt (sp0 - 240#64) mergeFieldSubStackX ∗
        mfFramePad_receiverChains sp0 ∗
        memRegion (sp0 - 232#64) 80 ∗
        memRegion (sp0 - 152#64) 24 ∗
        memRegion (sp0 - 80#64) 80 := by
  unfold mfFramePad_receiverChains
  change memRegion (sp0 - 32768#64) 32768 =
    memRegion (sp0 - 240#64 - 32528#64) 32528 ∗
      (memRegion (sp0 - 240#64) 8 ∗ memRegion (sp0 - 128#64) 48) ∗
      memRegion (sp0 - 232#64) 80 ∗
      memRegion (sp0 - 152#64) 24 ∗
      memRegion (sp0 - 80#64) 80
  have e_base : sp0 - 240#64 - 32528#64 = sp0 - 32768#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have s1 := memRegion_split (sp0 - 32768#64) 32528 240 (by decide)
  have e1 : (sp0 - 32768#64) + BitVec.ofNat 64 32528 = sp0 - 240#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [show (32528 : Nat) + 240 = 32768 by decide, e1] at s1
  have s2 := memRegion_split (sp0 - 240#64) 8 232 (by decide)
  have e2 : (sp0 - 240#64) + BitVec.ofNat 64 8 = sp0 - 232#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [show (8 : Nat) + 232 = 240 by decide, e2] at s2
  have s3 := memRegion_split (sp0 - 232#64) 80 152 (by decide)
  have e3 : (sp0 - 232#64) + BitVec.ofNat 64 80 = sp0 - 152#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [show (80 : Nat) + 152 = 232 by decide, e3] at s3
  have s4 := memRegion_split (sp0 - 152#64) 24 128 (by decide)
  have e4 : (sp0 - 152#64) + BitVec.ofNat 64 24 = sp0 - 128#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [show (24 : Nat) + 128 = 152 by decide, e4] at s4
  have s5 := memRegion_split (sp0 - 128#64) 48 80 (by decide)
  have e5 : (sp0 - 128#64) + BitVec.ofNat 64 48 = sp0 - 80#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [show (48 : Nat) + 80 = 128 by decide, e5] at s5
  rw [e_base, s1, s2, s3, s4, s5]
  sep_ac_rfl

private theorem stackAt_mergeFieldStack_join_mfc (sp0 : BitVec 64) :
    stackAt (sp0 - 240#64) mergeFieldSubStackX ∗
      mfFramePad_receiverChains sp0 ∗
      memRegion (sp0 - 232#64) 104 ∗
      memRegion (sp0 - 80#64) 80 =
    stackAt sp0 mergeFieldStackX := by
  have s := memRegion_split (sp0 - 232#64) 80 24 (by decide)
  have e : (sp0 - 232#64) + BitVec.ofNat 64 80 = sp0 - 152#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [show (80 : Nat) + 24 = 104 by decide, e] at s
  rw [s, stackAt_mergeFieldStack_split_mfc sp0]
  sep_ac_rfl

private theorem stackAt_receiverChains_epilogue_fold_mfc
    (sp0 : BitVec 64) (s0 : State) (w56 : BitVec 64)
    (q0 q1 q2 q3 q4 q5 : BitVec 128) (w6 : BitVec 64) :
    (stackAt (sp0 - 240#64) mergeFieldSubStackX ∗
      mfFramePad_receiverChains sp0 ∗
      chunks104_6QWAt (sp0 - 232#64) q0 q1 q2 q3 q4 q5 w6 ∗
      mfSavedRegs_receiverChains sp0 s0 w56) ⊢
    stackAt sp0 mergeFieldStackX := by
  rw [← stackAt_mergeFieldStack_join_mfc sp0]
  have h1 := chunks104_6QWAt_entails_memRegion104_receiverChains (sp0 - 232#64) q0 q1 q2 q3 q4 q5 w6
  have h2 : mfSavedRegs_receiverChains sp0 s0 w56 ⊢ memRegion (sp0 - 80#64) 80 :=
    cells10_entails_memRegion80_receiverChains sp0
      (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x25) w56
      (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
      (s0.readReg64 .x20) (s0.readReg64 .x19)
  exact sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) (sepConj_mono h1 h2))

private theorem prostChainGAtCap_default_stack_mfc (A : RustAlloc) (sp0 : BitVec 64) :
    ((sp0 - 232#64) ↦₆₄ 0#64) ∗ ((sp0 - 224#64) ↦₆₄ 1#64) ∗ ((sp0 - 216#64) ↦₆₄ 0#64) ∗
      ((sp0 - 208#64) ↦₆₄ 0#64) ∗ ((sp0 - 200#64) ↦₆₄ 1#64) ∗ ((sp0 - 192#64) ↦₆₄ 0#64) ∗
      ((sp0 - 184#64) ↦₆₄ 0#64) ∗ ((sp0 - 176#64) ↦₆₄ 8#64) ∗ ((sp0 - 168#64) ↦₆₄ 0#64) ∗
      ((sp0 - 160#64) ↦₆₄ (bv% (2 ^ 64 - 1))) ∗ memRegion (sp0 - 152#64) 24 ⊢
      prostChainGAtCap A (sp0 - 232#64) 0 ChainG.empty := by
  have h := prostChainGAtCap_empty_of_cells A (sp0 - 232#64) 1#64 1#64 8#64
    (by decide) (by decide) (by decide)
  have e8 : (sp0 - 232#64) + 8#64 = sp0 - 224#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e10 : (sp0 - 232#64) + 0x10#64 = sp0 - 216#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e18 : (sp0 - 232#64) + 0x18#64 = sp0 - 208#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e20 : (sp0 - 232#64) + 0x20#64 = sp0 - 200#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e28 : (sp0 - 232#64) + 0x28#64 = sp0 - 192#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e30 : (sp0 - 232#64) + 0x30#64 = sp0 - 184#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e38 : (sp0 - 232#64) + 0x38#64 = sp0 - 176#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e40 : (sp0 - 232#64) + 0x40#64 = sp0 - 168#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e48 : (sp0 - 232#64) + 0x48#64 = sp0 - 160#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e50 : (sp0 - 232#64) + 0x50#64 = sp0 - 152#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have hn : noneCap = bv% (2 ^ 64 - 1) := rfl
  rw [e8, e10, e18, e20, e28, e30, e38, e40, e48, e50, hn] at h
  exact h

private theorem arrayAt_prostChainGAtCap_move_bytes (A : RustAlloc)
    (cs : List ChainG) (a : BitVec 64) :
    arrayAt (fun c p => prostChainGAtCap A p (vecCap4Of c.keys.length) c) 104 a cs ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜bs.length = cs.length * 104 ∧
          ∀ b : BitVec 64, ((b ↦ₛ bs) ∗ H) ⊢
            arrayAt (fun c p => prostChainGAtCap A p (vecCap4Of c.keys.length) c) 104 b cs⌝ ∗
        (a ↦ₛ bs) ∗ H := by
  induction cs generalizing a with
  | nil =>
    simp only [arrayAt, List.length_nil, Nat.zero_mul]
    refine Entails.sepExists_right [] (Entails.sepExists_right emp ?_)
    rw [pointsToBytes_nil, emp_sepConj]
    exact Entails.pure_right
      ⟨rfl, fun _ => by rw [pointsToBytes_nil, emp_sepConj]; exact Entails.refl _⟩
      (Entails.refl _)
  | cons c rest ih =>
    have hm := move_bytes_pair_receiverChains
      (P1 := fun p => prostChainGAtCap A p (vecCap4Of c.keys.length) c)
      (P2 := fun p => arrayAt (fun c' q => prostChainGAtCap A q (vecCap4Of c'.keys.length) c') 104 p rest)
      (n1 := 104) (n2 := rest.length * 104) (off := BitVec.ofNat 64 104)
      rfl
      (prostChainGAtCap_move_bytes A (vecCap4Of c.keys.length) c)
      ih a
    have hlen : 104 + rest.length * 104 = (c :: rest).length * 104 := by
      simp [Nat.add_mul, Nat.add_comm]
    rw [hlen] at hm
    exact hm


private theorem vecAt_recvCap_open (A : RustAlloc) (ss : BitVec 64) (capRecv : Nat)
    (cs : List ChainG) :
    (∃∗ ptrRecv : BitVec 64,
      vecAt A 104 8 (fun c a => prostChainGAtCap A a (vecCap4Of c.keys.length) c)
        (ss + 0x48#64) (BitVec.ofNat 64 capRecv) ptrRecv cs) ⊢
      ∃∗ ptr : BitVec 64,
        ⌜cs.length ≤ (BitVec.ofNat 64 capRecv).toNat ∧
          (BitVec.ofNat 64 capRecv).toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        ((ss + 0x48#64) ↦₆₄ BitVec.ofNat 64 capRecv) ∗
        ((ss + 0x50#64) ↦₆₄ ptr) ∗
        ((ss + 0x58#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
        (if BitVec.ofNat 64 capRecv = 0#64 then emp
         else A.live ptr ((BitVec.ofNat 64 capRecv).toNat * 104) 8 ∗
           arrayAt (fun c a => prostChainGAtCap A a (vecCap4Of c.keys.length) c) 104 ptr cs ∗
           memRegion (ptr + BitVec.ofNat 64 (cs.length * 104))
             (((BitVec.ofNat 64 capRecv).toNat - cs.length) * 104)) := by
  unfold vecAt vecHeader vecBuf
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right ptr ?_
  have e50 : ss + 0x48#64 + 8#64 = ss + 0x50#64 := by rw [BitVec.add_assoc]; rfl
  have e58 : ss + 0x48#64 + 16#64 = ss + 0x58#64 := by rw [BitVec.add_assoc]; rfl
  have h0 : (0 : BitVec 64) = 0#64 := rfl
  rw [e50, e58, h0]
  by_cases hcap : BitVec.ofNat 64 capRecv = 0#64 <;>
    simp only [hcap, ↓reduceIte] <;> exact Entails.of_eq (by sep_ac_rfl)

private theorem vecBuf_recvCap_full_open (A : RustAlloc) (cap ptr : BitVec 64) (cs : List ChainG)
    (hfull : cs.length = cap.toNat) :
    (if cap = 0#64 then emp
     else A.live ptr (cap.toNat * 104) 8 ∗
       arrayAt (fun c a => prostChainGAtCap A a (vecCap4Of c.keys.length) c) 104 ptr cs ∗
       memRegion (ptr + BitVec.ofNat 64 (cs.length * 104)) ((cap.toNat - cs.length) * 104)) ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ Hmov : SepProp,
        ⌜bs.length = cap.toNat * 104 ∧
          ∀ b : BitVec 64, ((b ↦ₛ bs) ∗ Hmov) ⊢
            arrayAt (fun c b' => prostChainGAtCap A b' (vecCap4Of c.keys.length) c) 104 b cs⌝ ∗
        (if cap = 0#64 then emp else A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗ Hmov := by
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have hcs : cs = [] := List.eq_nil_of_length_eq_zero (by simpa using hfull)
    subst hcs; simp only [↓reduceIte, BitVec.toNat_ofNat]
    refine Entails.sepExists_right [] (Entails.sepExists_right emp ?_); rw [emp_sepConj]
    refine Entails.pure_right ⟨rfl, fun b => ?_⟩ (Entails.refl _)
    rw [pointsToBytes_nil, sepConj_emp]; exact Entails.refl _
  · simp only [hcap0, ↓reduceIte]
    have hrem : (cap.toNat - cs.length) * 104 = 0 := by omega
    rw [hrem, ProofLib.memRegion_zero, sepConj_emp]
    refine Entails.trans (sepConj_mono_right (arrayAt_prostChainGAtCap_move_bytes A cs ptr)) ?_
    rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro bs
    rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro Hmov
    rw [← sepConj_assoc, sepConj_comm (A.live _ _ _), sepConj_assoc]
    apply Entails.pure_left; rintro ⟨hbs_len, hmov⟩
    have hbs_cap : bs.length = cap.toNat * 104 := by rw [hbs_len, hfull]
    refine Entails.sepExists_right bs (Entails.sepExists_right Hmov ?_)
    rw [← hbs_cap]
    exact Entails.pure_right ⟨rfl, hmov⟩ (Entails.of_eq (by sep_ac_rfl))

private theorem vecBuf_recvCap_not_full_open (A : RustAlloc) (cap ptr : BitVec 64)
    (cs : List ChainG) (hlt : cs.length < cap.toNat) (hcap_lt : cap.toNat * 104 < 2 ^ 63) :
    (if cap = 0#64 then emp
     else A.live ptr (cap.toNat * 104) 8 ∗
       arrayAt (fun c a => prostChainGAtCap A a (vecCap4Of c.keys.length) c) 104 ptr cs ∗
       memRegion (ptr + BitVec.ofNat 64 (cs.length * 104)) ((cap.toNat - cs.length) * 104)) =
      (A.live ptr (cap.toNat * 104) 8 ∗
        arrayAt (fun c b => prostChainGAtCap A b (vecCap4Of c.keys.length) c) 104 ptr cs ∗
        memRegion (ptr + BitVec.ofNat 64 cs.length * 104#64) 104 ∗
        memRegion (ptr + BitVec.ofNat 64 ((cs.length + 1) * 104))
          ((cap.toNat - (cs.length + 1)) * 104)) := by
  have hcap0 : cap ≠ 0#64 := by intro h0; subst h0; simp at hlt
  simp only [hcap0, ↓reduceIte]
  have hrem : (cap.toNat - cs.length) * 104 = 104 + (cap.toNat - (cs.length + 1)) * 104 := by
    have : cap.toNat - cs.length = 1 + (cap.toNat - (cs.length + 1)) := by omega
    rw [this, Nat.add_mul, Nat.one_mul]
  have hmul : BitVec.ofNat 64 (cs.length * 104) = BitVec.ofNat 64 cs.length * 104#64 :=
    BitVec.ofNat_mul _ _
  have hoff : ptr + BitVec.ofNat 64 (cs.length * 104) + BitVec.ofNat 64 104 =
      ptr + BitVec.ofNat 64 ((cs.length + 1) * 104) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
  rw [hrem, memRegion_split (ptr + BitVec.ofNat 64 (cs.length * 104)) 104 _ (by omega), hoff, hmul]

private theorem vecAt_recvCap_push_fold (A : RustAlloc) (ss : BitVec 64) (cap' : Nat)
    (ptr' : BitVec 64) (cs : List ChainG) (c : ChainG)
    (hlt : cs.length < cap') (hcap_lt : cap' * 104 < 2 ^ 63) (hptr : ptr' ≠ 0#64) :
    ((ss + 0x48#64) ↦₆₄ BitVec.ofNat 64 cap') ∗
      ((ss + 0x50#64) ↦₆₄ ptr') ∗
      ((ss + 0x58#64) ↦₆₄ (BitVec.ofNat 64 cs.length + 1#64)) ∗
      A.live ptr' (cap' * 104) 8 ∗
      arrayAt (fun c' a => prostChainGAtCap A a (vecCap4Of c'.keys.length) c') 104 ptr' cs ∗
      prostChainGAtCap A (ptr' + BitVec.ofNat 64 cs.length * 104#64) (vecCap4Of c.keys.length) c ∗
      memRegion (ptr' + BitVec.ofNat 64 ((cs.length + 1) * 104)) ((cap' - (cs.length + 1)) * 104) ⊢
    ∃∗ ptrRecv : BitVec 64,
      vecAt A 104 8 (fun c' a => prostChainGAtCap A a (vecCap4Of c'.keys.length) c')
        (ss + 0x48#64) (BitVec.ofNat 64 cap') ptrRecv (cs ++ [c]) := by
  have hcap_toNat : (BitVec.ofNat 64 cap').toNat = cap' := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hne0 : BitVec.ofNat 64 cap' ≠ 0 := by
    intro h0
    have h1 : (BitVec.ofNat 64 cap').toNat = 0 := by rw [h0]; rfl
    omega
  unfold vecAt vecHeader vecBuf
  refine Entails.sepExists_right ptr' ?_
  have e50 : ss + 0x48#64 + 8#64 = ss + 0x50#64 := by rw [BitVec.add_assoc]; rfl
  have e58 : ss + 0x48#64 + 16#64 = ss + 0x58#64 := by rw [BitVec.add_assoc]; rfl
  have hlen_app : (cs ++ [c]).length = cs.length + 1 := by simp
  have hlen_bv : BitVec.ofNat 64 (cs.length + 1) = BitVec.ofNat 64 cs.length + 1#64 :=
    BitVec.ofNat_add _ _
  have hmul : BitVec.ofNat 64 (cs.length * 104) = BitVec.ofNat 64 cs.length * 104#64 :=
    BitVec.ofNat_mul _ _
  have h0 : (ptr' ≠ (0 : BitVec 64)) = (ptr' ≠ 0#64) := rfl
  rw [e50, e58, hlen_app, hlen_bv, arrayAt_concat, hmul, h0, hcap_toNat]
  simp only [hne0, ↓reduceIte]
  have hgrp :
      ((ss + 0x48#64) ↦₆₄ BitVec.ofNat 64 cap') ∗
        ((ss + 0x50#64) ↦₆₄ ptr') ∗
        ((ss + 0x58#64) ↦₆₄ (BitVec.ofNat 64 cs.length + 1#64)) ∗
        A.live ptr' (cap' * 104) 8 ∗
        arrayAt (fun c' a => prostChainGAtCap A a (vecCap4Of c'.keys.length) c') 104 ptr' cs ∗
        prostChainGAtCap A (ptr' + BitVec.ofNat 64 cs.length * 104#64) (vecCap4Of c.keys.length) c ∗
        memRegion (ptr' + BitVec.ofNat 64 ((cs.length + 1) * 104))
          ((cap' - (cs.length + 1)) * 104) =
      (((ss + 0x48#64) ↦₆₄ BitVec.ofNat 64 cap') ∗
        ((ss + 0x50#64) ↦₆₄ ptr') ∗
        ((ss + 0x58#64) ↦₆₄ (BitVec.ofNat 64 cs.length + 1#64))) ∗
      (A.live ptr' (cap' * 104) 8 ∗
        (arrayAt (fun c' a => prostChainGAtCap A a (vecCap4Of c'.keys.length) c') 104 ptr' cs ∗
          prostChainGAtCap A (ptr' + BitVec.ofNat 64 cs.length * 104#64)
            (vecCap4Of c.keys.length) c) ∗
        memRegion (ptr' + BitVec.ofNat 64 ((cs.length + 1) * 104))
          ((cap' - (cs.length + 1)) * 104)) := by sep_ac_rfl
  rw [hgrp]
  exact sepConj_mono_right
    (Entails.pure_right ⟨by omega, hcap_lt, hptr⟩ (Entails.refl _))

private theorem sepWPp_pure_left_mfc {prog : Program} {ret : BitVec 64} {s : State}
    {φ : Prop} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s F Q Qp) :
    SepWPp prog ret s (⌜φ⌝ ∗ F) Q Qp := by
  intro R hm hL
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 R hm.2 hL

private theorem mfSavedRegs_intro_mfc (sp0 : BitVec 64) (s0 : State) (w56 : BitVec 64) :
    ((sp0 - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
      ((sp0 - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
      ((sp0 - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
      ((sp0 - 56#64) ↦₆₄ w56) ∗
      ((sp0 - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
      ((sp0 - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
      ((sp0 - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
      ((sp0 - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
      ((sp0 - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
      ((sp0 - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ⊢
    mfSavedRegs_receiverChains sp0 s0 w56 :=
  Entails.of_eq rfl

attribute [local irreducible] mfFramePad_receiverChains mfSavedRegs_receiverChains

set_option maxHeartbeats 800000 in
private theorem step_tag7_from_1116_mfc [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (ss bufRef slot ptr : BitVec 64) (cs : List ChainG) (c : ChainG)
    (payload tail : List (BitVec 8)) (cap' : Nat) (ptr' w56 : BitVec 64) (st' : M.σ)
    {s0 s : State}
    (hlt : cs.length < cap') (hcap_lt : cap' * 104 < 2 ^ 63) (hptr : ptr' ≠ 0#64)
    (hpc : s.pc = (blkPl_15).base + 1116#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 240#64) (hsp_align : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 .x8 = ss)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 cs.length)
    (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (lsProg_15 H) (s0.readReg64 .lr) s
      (((ss + 0x48#64) ↦₆₄ BitVec.ofNat 64 cap') ∗
        ((ss + 0x50#64) ↦₆₄ ptr') ∗
        ((ss + 0x58#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
        A.repAlloc.live ptr' (cap' * 104) 8 ∗
        arrayAt (fun c' a => prostChainGAtCap A.repAlloc a (vecCap4Of c'.keys.length) c') 104 ptr' cs ∗
        memRegion (ptr' + BitVec.ofNat 64 cs.length * 104#64) 104 ∗
        memRegion (ptr' + BitVec.ofNat 64 ((cs.length + 1) * 104))
          ((cap' - (cs.length + 1)) * 104) ∗
        prostChainGAtCap A.repAlloc (s0.sp - 232#64) (vecCap4Of c.keys.length) c ∗
        mfSavedRegs_receiverChains s0.sp s0 w56 ∗
        mfFramePad_receiverChains s0.sp ∗
        stackAt (s0.sp - 240#64) mergeFieldSubStackX ∗
        (bufRef ↦₆₄ slot) ∗
        sliceCursorAfter slot ptr (payload ++ tail) tail ∗
        A.pool lim st' s)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace ∧
        sf.readReg64 .x0 = 0#64 ∧
        (Pf ⊢
          (∃∗ ptrRecv : BitVec 64,
            vecAt A.repAlloc 104 8
              (fun c' a => prostChainGAtCap A.repAlloc a (vecCap4Of c'.keys.length) c')
              (ss + 0x48#64) (BitVec.ofNat 64 cap') ptrRecv (cs ++ [c])) ∗
          (bufRef ↦₆₄ slot) ∗
          sliceCursorAfter slot ptr (payload ++ tail) tail ∗
          A.pool lim st' sf ∗
          stackAt s0.sp mergeFieldStackX))
      NoPanicPost := by
  apply SepWPp.of_sepWP_ret
  apply SepWP.fold (prostChainGAtCap_move_chunks104 A.repAlloc
    (vecCap4Of c.keys.length) c (s0.sp - 232#64)) (by sep_frame)
  conv =>
    arg 4
    simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWP.exists_elim; intro q0
  apply SepWP.exists_elim; intro q1
  apply SepWP.exists_elim; intro q2
  apply SepWP.exists_elim; intro q3
  apply SepWP.exists_elim; intro q4
  apply SepWP.exists_elim; intro q5
  apply SepWP.exists_elim; intro w6
  apply SepWP.exists_elim; intro H_mov
  apply SepWP.pure_elim; intro hmov
  set dst : BitVec 64 := ptr' + BitVec.ofNat 64 cs.length * 104#64
  apply SepWP.fold (Entails.of_eq (memRegion104_eq_exists_chunks104_6QWAt_receiverChains dst))
    (by sep_frame)
  conv =>
    arg 4
    simp only [sepExists_sepConj_left]
  apply SepWP.exists_elim; intro d0
  apply SepWP.exists_elim; intro d1
  apply SepWP.exists_elim; intro d2
  apply SepWP.exists_elim; intro d3
  apply SepWP.exists_elim; intro d4
  apply SepWP.exists_elim; intro d5
  apply SepWP.exists_elim; intro dw6
  conv =>
    arg 4
    rw [chunks104_6QWAt_stack_eq_receiverChains s0.sp q0 q1 q2 q3 q4 q5 w6,
        chunks104_6QWAt_dst_eq_receiverChains dst d0 d1 d2 d3 d4 d5 dw6,
        mfSavedRegs_receiverChains]
    simp only [sepConj_assoc]
  apply sepWP_ret_vmPreserved
  by_vm_steps_withSvc (
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm_end
  rw [← A.pool_transport lim st' s _ hvm_end]
  apply SepWP.done (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
  refine ⟨by simp only [wp_norm, arm64_norm, hsp],
    by simp only [CalleeSavedPreserved, calleeSavedVRegs, wp_norm, arm64_norm,
      hx26, hx27, hx28, hvregs, and_self],
    by simp only [wp_norm, arm64_norm, htr],
    by simp only [wp_norm, arm64_norm], ?_⟩
  have hfold_vec := vecAt_recvCap_push_fold A.repAlloc ss cap' ptr' cs c hlt hcap_lt hptr
  have hfold_stk := stackAt_receiverChains_epilogue_fold_mfc s0.sp s0 w56 q0 q1 q2 q3 q4 q5 w6
  have hmov_dst := hmov dst
  dsimp only [dst] at hmov_dst ⊢
  refine Entails.trans (Entails.of_eq ?_)
    (Entails.trans
      (sepConj_mono (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hmov_dst))))))
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hfold_stk))))
      (sepConj_mono_left hfold_vec))
  rw [chunks104_6QWAt_stack_eq_receiverChains s0.sp q0 q1 q2 q3 q4 q5 w6,
      chunks104_6QWAt_dst_eq_receiverChains (ptr' + BitVec.ofNat 64 cs.length * 104#64)
        q0 q1 q2 q3 q4 q5 w6,
      mfSavedRegs_receiverChains]
  sep_ac_rfl


set_option maxHeartbeats 1600000 in
private theorem step_tag7_from_700_mfc [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H)
    (ss bufRef slot ptr : BitVec 64) (cs : List ChainG) (c : ChainG)
    (payload tail : List (BitVec 8)) (capRecv : Nat) (w56 : BitVec 64) (st_mid : M.σ)
    {s0 s : State}
    (hpow : IsPow2Cap4 capRecv) (_hle : cs.length ≤ capRecv) (hcap62 : capRecv < 2 ^ 62)
    (hfresh : cs.length < maxReceiverChains)
    (hfit_grow : cs.length = capRecv → FitsEvents M lim st_mid (vec104GrowEvents capRecv))
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hro : LibsignalRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_15).base + 700#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 240#64) (hsp_align : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hx20 : s.readReg64 .x20 = ss)
    (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    let cap' := if cs.length = capRecv then vecCap4Next capRecv else capRecv
    let st' := M.stepEvents (if cs.length = capRecv then vec104GrowEvents capRecv else []) st_mid
    SepWPp (lsProg_15 H) (s0.readReg64 .lr) s
      ((∃∗ ptrRecv : BitVec 64,
          vecAt A.repAlloc 104 8
            (fun c' a => prostChainGAtCap A.repAlloc a (vecCap4Of c'.keys.length) c')
            (ss + 0x48#64) (BitVec.ofNat 64 capRecv) ptrRecv cs) ∗
        prostChainGAtCap A.repAlloc (s0.sp - 232#64) (vecCap4Of c.keys.length) c ∗
        (bufRef ↦₆₄ slot) ∗
        sliceCursorAfter slot ptr (payload ++ tail) tail ∗
        A.pool lim st_mid s ∗
        stackAt (s0.sp - 240#64) chainMergeStackX ∗
        memRegion ((s0.sp - 240#64) - 32528#64) 3856 ∗
        mfSavedRegs_receiverChains s0.sp s0 w56 ∗
        mfFramePad_receiverChains s0.sp)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace ∧
        sf.readReg64 .x0 = 0#64 ∧
        (Pf ⊢
          (∃∗ ptrRecv : BitVec 64,
            vecAt A.repAlloc 104 8
              (fun c' a => prostChainGAtCap A.repAlloc a (vecCap4Of c'.keys.length) c')
              (ss + 0x48#64) (BitVec.ofNat 64 cap') ptrRecv (cs ++ [c])) ∗
          (bufRef ↦₆₄ slot) ∗
          sliceCursorAfter slot ptr (payload ++ tail) tail ∗
          A.pool lim st' sf ∗
          stackAt s0.sp mergeFieldStackX))
      NoPanicPost := by
  dsimp only
  simp only [arm64_norm] at hx0 hx20 hx26 hx27 hx28
  have hcap_toNat : (BitVec.ofNat 64 capRecv).toNat = capRecv := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  apply SepWPp.fold (Entails.of_eq (stackAt_sub_to_chainMerge_mfc (s0.sp - 240#64)).symm)
    (by sep_frame)
  apply SepWPp.fold (vecAt_recvCap_open A.repAlloc ss capRecv cs) (by sep_frame)
  conv =>
    arg 4
    simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun ptr0 => ?_
  refine sepWPp_pure_left_mfc fun ⟨hlen_le, hcap_lt, hptr0⟩ => ?_
  by_cases hfull : cs.length = capRecv
  · have hfull_bv : cs.length = (BitVec.ofNat 64 capRecv).toNat := by
      rw [hcap_toNat]; exact hfull
    apply SepWPp.fold
      (vecBuf_recvCap_full_open A.repAlloc (BitVec.ofNat 64 capRecv) ptr0 cs hfull_bv)
      (by sep_frame)
    conv =>
      arg 4
      simp only [sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun bs => SepWPp.exists_elim fun Hmov => ?_
    refine sepWPp_pure_left_mfc fun ⟨hbs_len, hmov⟩ => ?_
    have hlen_cap : BitVec.ofNat 64 cs.length = BitVec.ofNat 64 capRecv :=
      congrArg (BitVec.ofNat 64) hfull
    have hite_cap : (if cs.length = capRecv then vecCap4Next capRecv else capRecv) =
        vecCap4Next capRecv := by simp only [hfull, ↓reduceIte]
    have hite_ev : (if cs.length = capRecv then vec104GrowEvents capRecv else []) =
        vec104GrowEvents capRecv := by simp only [hfull, ↓reduceIte]
    rw [hite_cap, hite_ev]
    have h5 : maxReceiverChains = 5 := rfl
    have hmax_eq : max (2 * capRecv) 4 = vecCap4Next capRecv := by
      rcases hpow with rfl | ⟨j, rfl⟩
      · rfl
      · have hj : 1 ≤ 2 ^ j := Nat.one_le_pow j 2 (by decide)
        have hne : 4 * 2 ^ j ≠ 0 := by omega
        simp only [vecCap4Next, hne, ↓reduceIte]; omega
    have hmax_lt : max (2 * (BitVec.ofNat 64 capRecv).toNat) 4 * 104 + 8 ≤ 2 ^ 63 := by
      rw [hcap_toNat]; omega
    have hcap_or : BitVec.ofNat 64 capRecv = 0#64 ∨ 2 ≤ (BitVec.ofNat 64 capRecv).toNat :=
      cap_zero_or_ge_two_of_isPow2Cap4 (by rwa [hcap_toNat])
    have hfit_g : FitsEvents M lim st_mid (vec104GrowEvents (BitVec.ofNat 64 capRecv).toNat) := by
      rw [hcap_toNat]; exact hfit_grow hfull
    have hcallG := grow_one_104_budget_placed_ok_cl (callerProg := lsProg_15 H) hA
    rw [hlen_cap, stackAt_sub_to_growOne_mfc (s0.sp - 240#64)]
    apply sepWPp_seq_lsclro_vm hcl hro (mid := lsmpl.base 43)
    by_vm_steps_withSvc (
      wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, hrun])
        ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
    intro hvm_g hcl_g hro_g
    rw [← A.pool_transport lim st_mid s _ hvm_g]
    refine sepWPp_call_lscl_15
      (x := ((ss + 0x48#64, BitVec.ofNat 64 capRecv, ptr0, bs), st_mid))
      (ret_pc := (blkPl_15).base + 2480#64)
      hcallG hcl_g hro_g
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun])
      (by simp only [State.spAligned, wp_norm, arm64_norm] at hsp_align ⊢; exact hsp_align)
      (by simp only [wp_norm, arm64_norm])
      (by
        dsimp only [growOne104BudgetSpecX]
        apply entails_pure_sep_frame
        · refine ⟨by simp only [wp_norm, arm64_norm, hx20], hbs_len, hptr0, hcap_or, hmax_lt, hfit_g⟩
        · apply entails_rw_stack_5 (sp2 := s0.sp - 240#64) (w2 := growOneChainStackX)
          · simp only [wp_norm, arm64_norm, hsp]
          · rfl
          · have e50 : ss + 0x48#64 + 8#64 = ss + 0x50#64 := by rw [BitVec.add_assoc]; rfl
            have hl : A.live = A.repAlloc.live := rfl
            have hite_eq :
                (if BitVec.ofNat 64 capRecv = 0 then emp else A.live ptr0 bs.length 8 ∗ (ptr0 ↦ₛ bs)) =
                (if BitVec.ofNat 64 capRecv = 0#64 then emp else A.repAlloc.live ptr0 bs.length 8 ∗ (ptr0 ↦ₛ bs)) := by
              by_cases hc : BitVec.ofNat 64 capRecv = 0#64
              · rw [hc]; rfl
              · have hc0 : BitVec.ofNat 64 capRecv ≠ 0 := hc
                simp only [hc, hc0, ↓reduceIte, hl]
            rw [e50, hite_eq]
            sep_frame)
      ?_
    intro sm hpcm hrunm hspm hcsm hclm hrom
    dsimp only [growOne104BudgetSpecX]
    refine sepWPp_pure_left_and fun htrm => ?_
    conv =>
      arg 4
      simp only [sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun p' => ?_
    refine sepWPp_pure_left_mfc fun hp' => ?_
    have hp'0 : p' ≠ 0#64 := hp'
    have hspm' : sm.sp = s0.sp - 240#64 := by simpa only [wp_norm, arm64_norm, hsp] using hspm
    have htrm' : sm.trace = s0.trace := by simpa only [wp_norm, arm64_norm, htr] using htrm
    have hx19m : sm.readReg64 (Reg.gpr 19#5) = BitVec.ofNat 64 cs.length := by
      rw [hlen_cap]
      simpa only [wp_norm, arm64_norm] using hcsm.1
    have hx20m : sm.readReg64 (Reg.gpr 20#5) = ss := by
      simpa only [wp_norm, arm64_norm, hx20] using hcsm.2.1
    have hx26m : sm.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := by
      simpa only [wp_norm, arm64_norm, hx26] using hcsm.2.2.2.2.2.2.2.1
    have hx27m : sm.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
      simpa only [wp_norm, arm64_norm, hx27] using hcsm.2.2.2.2.2.2.2.2.1
    have hx28m : sm.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
      simpa only [wp_norm, arm64_norm, hx28] using hcsm.2.2.2.2.2.2.2.2.2.1
    have hvregsm : calleeSavedVRegs sm = calleeSavedVRegs s0 := by
      have h1 : calleeSavedVRegs sm = calleeSavedVRegs s := by
        simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hcsm.2.2.2.2.2.2.2.2.2.2.2
      exact h1.trans hvregs
    have hsp_align_m : sm.spAligned = true := by
      simp only [State.spAligned] at hsp_align ⊢
      rw [hspm', ← hsp]
      exact hsp_align
    have e50 : ss + 0x48#64 + 8#64 = ss + 0x50#64 := by rw [BitVec.add_assoc]; rfl
    have hl : A.live = A.repAlloc.live := rfl
    have hbs_cs : bs.length = cs.length * 104 := by rw [hbs_len, hcap_toNat, hfull]
    have hlt_next : cs.length < vecCap4Next capRecv := by rw [← hmax_eq]; omega
    have hcap_lt_next : vecCap4Next capRecv * 104 < 2 ^ 63 := by rw [← hmax_eq]; omega
    have hsplit_mr :
        memRegion (p' + BitVec.ofNat 64 bs.length) ((vecCap4Next capRecv - capRecv) * 104) =
        memRegion (p' + BitVec.ofNat 64 cs.length * 104#64) 104 ∗
          memRegion (p' + BitVec.ofNat 64 ((cs.length + 1) * 104))
            ((vecCap4Next capRecv - (cs.length + 1)) * 104) := by
      have hrem : (vecCap4Next capRecv - capRecv) * 104 =
          104 + (vecCap4Next capRecv - (cs.length + 1)) * 104 := by
        have : vecCap4Next capRecv - capRecv = 1 + (vecCap4Next capRecv - (cs.length + 1)) := by
          omega
        rw [this, Nat.add_mul, Nat.one_mul]
      have hoff : (p' + BitVec.ofNat 64 (cs.length * 104)) + BitVec.ofNat 64 104 =
          p' + BitVec.ofNat 64 ((cs.length + 1) * 104) := by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
      rw [hbs_cs, hrem, memRegion_split (p' + BitVec.ofNat 64 (cs.length * 104)) 104 _ (by omega),
          hoff, BitVec.ofNat_mul]
    conv =>
      arg 4
      rw [show stackAt _ growOneChainStackX = stackAt (s0.sp - 240#64) growOneChainStackX by
            simp only [wp_norm, arm64_norm, hsp],
          e50, hl, hcap_toNat, hmax_eq, hsplit_mr, ← hlen_cap]
      simp only [sepConj_assoc]
    apply SepWPp.fold (hmov p') (by sep_frame)
    apply SepWPp.fold (Entails.of_eq (stackAt_sub_to_growOne_mfc (s0.sp - 240#64)).symm)
      (by sep_frame)
    apply sepWPp_seq_lsclro_vm hclm hrom (mid := (blkPl_15).base + 1116#64)
    by_vm_steps_withSvc (
      wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, hrunm])
        ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
    intro hvm_2 _hcl2 _hro2
    rw [← A.pool_transport lim (M.stepEvents (vec104GrowEvents capRecv) st_mid) sm _ hvm_2]
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (step_tag7_from_1116_mfc ss bufRef slot ptr cs c payload tail
        (vecCap4Next capRecv) p' w56
        (M.stepEvents (vec104GrowEvents capRecv) st_mid)
        hlt_next hcap_lt_next hp'0
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, hrunm])
        (by simp only [wp_norm, arm64_norm, hspm'])
        (by simp only [State.spAligned, wp_norm, arm64_norm] at hsp_align_m ⊢; exact hsp_align_m)
        (by simp only [wp_norm, arm64_norm, htrm'])
        (by simp only [wp_norm, arm64_norm, hx20m])
        (by simp only [wp_norm, arm64_norm, hx19m])
        (by simp only [wp_norm, arm64_norm, hx26m])
        (by simp only [wp_norm, arm64_norm, hx27m])
        (by simp only [wp_norm, arm64_norm, hx28m])
        (by simp only [wp_norm, arm64_norm, hvregsm]))
  · simp only [hfull, ↓reduceIte, AllocCostModel.stepEvents_nil]
    have hlt : cs.length < capRecv := by omega
    have hlt_bv : cs.length < (BitVec.ofNat 64 capRecv).toNat := by rwa [hcap_toNat]
    have hbeq : (BitVec.ofNat 64 cs.length == BitVec.ofNat 64 capRecv) = false :=
      beq_ofNat_len_cap_false hlt_bv
    rw [vecBuf_recvCap_not_full_open A.repAlloc (BitVec.ofNat 64 capRecv) ptr0 cs hlt_bv hcap_lt]
    rw [hcap_toNat] at hcap_lt ⊢
    apply sepWPp_seq_lsclro_vm hcl hro (mid := (blkPl_15).base + 1116#64)
    by_vm_steps_withSvc (
      wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, hrun])
        ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
    intro hvm_nf _hcl_nf _hro_nf
    rw [← A.pool_transport lim st_mid s _ hvm_nf]
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (step_tag7_from_1116_mfc ss bufRef slot ptr cs c payload tail capRecv ptr0 w56 st_mid
        hlt hcap_lt hptr0
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, hrun])
        (by simp only [wp_norm, arm64_norm, hsp])
        (by simp only [State.spAligned, wp_norm, arm64_norm] at hsp_align ⊢; exact hsp_align)
        (by simp only [wp_norm, arm64_norm, htr])
        (by simp only [wp_norm, arm64_norm, hx20])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, hx26])
        (by simp only [wp_norm, arm64_norm, hx27])
        (by simp only [wp_norm, arm64_norm, hx28])
        (by simp only [wp_norm, arm64_norm, hvregs]))


set_option maxHeartbeats 1600000 in
private theorem step_tag7_recv_mfc [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H)
    (ss bufRef slot ptr : BitVec 64) (cs : List ChainG) (c : ChainG) (hcOk : c.Ok)
    (capRecv : Nat) (hpow : IsPow2Cap4 capRecv) (hle : cs.length ≤ capRecv)
    (hcap62 : capRecv < 2 ^ 62) (hfresh : cs.length < maxReceiverChains)
    (tail : List (BitVec 8)) (st : M.σ) {s0 : State}
    (hpc : s0.pc = (blkPl_15).base) (hrun : s0.status = .Running)
    (hsp_align : s0.spAligned = true)
    (hcl : LibsignalCodeLoaded lsmpl s0.mem) (hro : LibsignalRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = ss)
    (hx1 : (s0.readReg64 .x1).setWidth 32 = 7#32)
    (hx2 : (s0.readReg64 .x2).setWidth 8 = 2#8)
    (hx3 : s0.readReg64 .x3 = bufRef)
    (hx4 : (s0.readReg64 .x4).setWidth 32 = 99#32)
    (hlen : (c.payload ++ tail).length < 2 ^ 62)
    (hfit : FitsEvents M lim st
      (chainMergeEvents c ++ (if cs.length = capRecv then vec104GrowEvents capRecv else []))) :
    let cap' := if cs.length = capRecv then vecCap4Next capRecv else capRecv
    let st' := M.stepEvents
      (chainMergeEvents c ++ (if cs.length = capRecv then vec104GrowEvents capRecv else [])) st
    SepWPp (lsProg_15 H) (s0.readReg64 .lr) s0
      ((∃∗ ptrRecv : BitVec 64,
          vecAt A.repAlloc 104 8
            (fun c' a => prostChainGAtCap A.repAlloc a (vecCap4Of c'.keys.length) c')
            (ss + 0x48#64) (BitVec.ofNat 64 capRecv) ptrRecv cs) ∗
        (bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr (c.payload ++ tail) ∗
        A.pool lim st s0 ∗
        stackAt s0.sp mergeFieldStackX)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace ∧
        sf.readReg64 .x0 = 0#64 ∧
        (Pf ⊢
          (∃∗ ptrRecv : BitVec 64,
            vecAt A.repAlloc 104 8
              (fun c' a => prostChainGAtCap A.repAlloc a (vecCap4Of c'.keys.length) c')
              (ss + 0x48#64) (BitVec.ofNat 64 cap') ptrRecv (cs ++ [c])) ∗
          (bufRef ↦₆₄ slot) ∗
          sliceCursorAfter slot ptr (c.payload ++ tail) tail ∗
          A.pool lim st' sf ∗
          stackAt s0.sp mergeFieldStackX))
      NoPanicPost := by
  dsimp only
  have halign : s0.sp &&& 15#64 = 0#64 := by simpa [State.spAligned] using hsp_align
  have hsp240 := sp_sub_240_aligned_receiverChains halign
  have hsp240_beq : ((s0.sp - 240#64) &&& 15#64 == 0#64) = true := beq_iff_eq.mpr hsp240
  have hx2' : BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 .x2)) &&& 255#64 = 2#64 :=
    zext64_trunc32_and_255_eq_of_trunc8_receiverChains hx2
  have hcallC := chainMergeGen_budget_placed_ok_cl (callerProg := lsProg_15 H) hA
  rw [fitsEvents_append] at hfit
  obtain ⟨hfit_c, hfit_g⟩ := hfit
  conv =>
    arg 4
    rw [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun ptrRecv => ?_
  conv =>
    arg 4
    rw [stackAt_mergeFieldStack_split_mfc s0.sp,
        memRegion80_chainInit_eq_cells10_receiverChains s0.sp,
        memRegion80_eq_cells10_receiverChains s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun w80 => SepWPp.exists_elim fun w72 =>
    SepWPp.exists_elim fun w64 => SepWPp.exists_elim fun w56 =>
    SepWPp.exists_elim fun w48 => SepWPp.exists_elim fun w40 =>
    SepWPp.exists_elim fun w32 => SepWPp.exists_elim fun w24 =>
    SepWPp.exists_elim fun w16 => SepWPp.exists_elim fun w8 =>
    SepWPp.exists_elim fun c0 => SepWPp.exists_elim fun c1 =>
    SepWPp.exists_elim fun c2 => SepWPp.exists_elim fun c3 =>
    SepWPp.exists_elim fun c4 => SepWPp.exists_elim fun c5 =>
    SepWPp.exists_elim fun c6 => SepWPp.exists_elim fun c7 =>
    SepWPp.exists_elim fun c8 => SepWPp.exists_elim fun c9 => ?_
  simp only [arm64_norm] at hx0 hx1 hx2 hx2' hx3 hx4
  apply sepWPp_seq_lsclro_vm hcl hro (mid := (blkPl_15).base + 40#64)
  by_vm_steps_withSvc (
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm1 hcl1a hro1a
  rw [← A.pool_transport lim st s0 _ hvm1]
  apply sepWPp_step_0x28_15 hcl1a hro1a
    (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  intro hvm1b hcl1 hro1
  rw [← A.pool_transport lim st _ _ hvm1b]
  apply sepWPp_seq_lsclro_vm hcl1 hro1 (mid := lsmpl.base 11)
  refine sepWP_intro_ro8_mfb (lsmpl.ρ mergeFieldRodataSym + 6#64) 0x8d#8
    (fun hm => lsro8_intro hro1 (by lsro_addr) (by decide +kernel) hm) ?_
  by_vm_steps_withSvc (
    wp_steps
    apply sepWP_drop_left_mfb
    apply SepWP.fold (prostChainGAtCap_default_stack_mfc A.repAlloc s0.sp) (by sep_frame)
    apply SepWP.fold (mfSavedRegs_intro_mfc s0.sp s0 w56) (by sep_frame)
    apply SepWP.fold (Entails.of_eq (stackAt_sub_to_chainMerge_mfc (s0.sp - 240#64))) (by sep_frame)
    refine SepWP.done (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm2 hcl2 hro2
  rw [← A.pool_transport lim st _ _ hvm2]
  refine sepWPp_call_lscro_15
    (x := (ChainMergeGenGhost.mk (s0.sp - 232#64) c bufRef slot ptr tail, st))
    (ret_pc := (blkPl_15).base + 700#64)
    hcallC hcl2 hro2
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp240, beq_self_eq_true])
    (by simp only [wp_norm, arm64_norm])
    (by
      dsimp only [chainMergeGenBudgetRawSpecW]
      apply entails_pure_sep_frame
      · refine ⟨?_, ?_, ?_, ?_, hcOk, hlen, hfit_c⟩
        · simp only [wp_norm, arm64_norm]
        · simp only [wp_norm, arm64_norm]
        · simp only [wp_norm, arm64_norm]
        · simp only [wp_norm, arm64_norm]
      · apply entails_rw_stack_5 (sp2 := s0.sp - 240#64) (w2 := chainMergeStackX)
        · simp only [wp_norm, arm64_norm]
        · rfl
        · sep_frame)
    ?_
  intro sm hpcm hrunm hspm hcsm hclm hrom
  dsimp only [chainMergeGenBudgetRawSpecW]
  refine sepWPp_pure_left_and fun ⟨htrm, hx0m⟩ => ?_
  try simp only [wp_norm, arm64_norm] at hpcm
  have hspm' : sm.sp = s0.sp - 240#64 := by simpa only [wp_norm, arm64_norm] using hspm
  have hsp_align_m : sm.spAligned = true := by
    simp only [State.spAligned, hspm']
    exact hsp240_beq
  have htrm' : sm.trace = s0.trace := by simpa only [wp_norm, arm64_norm] using htrm
  have hx20m : sm.readReg64 .x20 = ss := by
    simpa only [wp_norm, arm64_norm] using hcsm.2.1
  have hx26m : sm.readReg64 .x26 = s0.readReg64 .x26 := by
    simpa only [wp_norm, arm64_norm] using hcsm.2.2.2.2.2.2.2.1
  have hx27m : sm.readReg64 .x27 = s0.readReg64 .x27 := by
    simpa only [wp_norm, arm64_norm] using hcsm.2.2.2.2.2.2.2.2.1
  have hx28m : sm.readReg64 .x28 = s0.readReg64 .x28 := by
    simpa only [wp_norm, arm64_norm] using hcsm.2.2.2.2.2.2.2.2.2.1
  have hvregsm : calleeSavedVRegs sm = calleeSavedVRegs s0 := by
    simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hcsm.2.2.2.2.2.2.2.2.2.2.2
  conv =>
    arg 4
    rw [show stackAt _ chainMergeStackX = stackAt (s0.sp - 240#64) chainMergeStackX by
          simp only [wp_norm, arm64_norm]]
    simp only [sepConj_assoc]
  rw [AllocCostModel.stepEvents_append]
  have hpack_recv :
      vecAt A.repAlloc 104 8
        (fun c' a => prostChainGAtCap A.repAlloc a (vecCap4Of c'.keys.length) c')
        (ss + 0x48#64) (BitVec.ofNat 64 capRecv) ptrRecv cs ⊢
      ∃∗ p : BitVec 64,
        vecAt A.repAlloc 104 8
          (fun c' a => prostChainGAtCap A.repAlloc a (vecCap4Of c'.keys.length) c')
          (ss + 0x48#64) (BitVec.ofNat 64 capRecv) p cs :=
    Entails.sepExists_right
      (Q := fun p => vecAt A.repAlloc 104 8
        (fun c' a => prostChainGAtCap A.repAlloc a (vecCap4Of c'.keys.length) c')
        (ss + 0x48#64) (BitVec.ofNat 64 capRecv) p cs)
      ptrRecv (Entails.refl _)
  apply SepWPp.fold hpack_recv (by sep_frame)
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (step_tag7_from_700_mfc hA ss bufRef slot ptr cs c c.payload tail capRecv w56
      (M.stepEvents (chainMergeEvents c) st)
      hpow hle hcap62 hfresh
      (fun hfull => by simpa only [hfull, ↓reduceIte] using hfit_g)
      hclm hrom hpcm hrunm hspm' hsp_align_m htrm' hx0m hx20m hx26m hx27m hx28m hvregsm)

/-- Relocatable `[LibsignalPlacement]` proof of `SessionStructure::merge_field` (Block `15`,
`lsProg_15 H`, `mergeFieldStackX`) on tag `7` (`receiver_chains` at `ss + 0x48`): combines
`chainMergeGen_budget_placed_ok` (Block `11`) with `grow_one_104_budget_placed_ok_cl` (Block `43`,
when `recv.length = capRecv`), with `onOom := ⌜False⌝` and `onPanic := ⌜False⌝`. -/
theorem mergeFieldReceiverChains_budget_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H) :
    subroutine_ok (lsProg_15 H) (blkPl_15).base
      (mergeFieldQBudgetSpecW M A lim (fun fl => fl.tag = 7)) := by
  apply subroutine_ok_of_field_sepWPp
  intro x capRecv st s0 hpc hrun hal hcl hro hx0 hx1 hx2 hx3 hx4 hP hOk hFr _hFrB hlen
    hpow hle hcap62 hfit
  generalize x.fld = fld at hx1 hx2 hP hOk hFr hlen hfit ⊢
  cases fld with
  | base f =>
    cases f with
    | recv c =>
      have hcOk : c.Ok := hOk.1
      have hfresh : x.v.base.recv.length < maxReceiverChains := hFr.2
      let cap' := if x.v.base.recv.length = capRecv then vecCap4Next capRecv else capRecv
      refine ⟨(∃∗ ptrRecv : BitVec 64,
          vecAt A.repAlloc 104 8
            (fun c' a => prostChainGAtCap A.repAlloc a (vecCap4Of c'.keys.length) c')
            (x.ss + 0x48#64) (BitVec.ofNat 64 capRecv) ptrRecv x.v.base.recv),
        (∃∗ ptrRecv : BitVec 64,
          vecAt A.repAlloc 104 8
            (fun c' a => prostChainGAtCap A.repAlloc a (vecCap4Of c'.keys.length) c')
            (x.ss + 0x48#64) (BitVec.ofNat 64 cap') ptrRecv (x.v.base.recv ++ [c])),
        prostSSGQRest_recv A.repAlloc x.ss x.v, ?_, ?_, ?_⟩
      · unfold prostSSGQAtCap prostSSGQRest_recv prostSSGQScalars
        exact Entails.of_eq (by sep_ac_rfl)
      · unfold prostSSGQAtCap nextCapRecv SSGQ.apply prostSSGQRest_recv prostSSGQScalars
        dsimp only [SSG.apply, cap']
        rw [pendingAt9PCap_congr A.repAlloc x.ss rfl rfl rfl]
        exact Entails.of_eq (by sep_ac_rfl)
      · exact step_tag7_recv_mfc hA x.ss x.bufRef x.slot x.ptr x.v.base.recv c hcOk
          capRecv hpow hle hcap62 hfresh x.tail st hpc hrun hal hcl hro
          hx0 hx1 hx2 hx3 hx4 hlen hfit
    | _ => simp [GenFieldQ.tag, GenField.tag] at hP
  | _ => simp [GenFieldQ.tag] at hP

/-! ## 5. Full `SessionStructure::merge_field` Budget Theorem Across All `GenFieldQ` Tags -/

/-- Full relocatable `[LibsignalPlacement]` proof of `SessionStructure::merge_field` (Block `15`,
`lsProg_15 H`, `mergeFieldStackX`) across all `GenFieldQ` tags (`fun _ => True`:
basic tags `1–5, 9–11, 13–15` + `sender_chain` tag `6` + `receiver_chains` tag `7`),
with `onOom := ⌜False⌝` and `onPanic := ⌜False⌝`. -/
theorem mergeFieldAllQ_budget_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H) :
    subroutine_ok (lsProg_15 H) (blkPl_15).base
      (mergeFieldQBudgetSpecW M A lim (fun _ => True)) := by
  refine mergeFieldQBudget_of_imp
    (mergeFieldQBudget_or
      (mergeFieldBasic_budget_placed_ok hA)
      (mergeFieldQBudget_or
        (mergeFieldSenderChain_budget_placed_ok hA)
        (mergeFieldReceiverChains_budget_placed_ok hA))) ?_
  intro fl _
  by_cases h6 : fl.tag = 6
  · exact Or.inr (Or.inl h6)
  · by_cases h7 : fl.tag = 7
    · exact Or.inr (Or.inr h7)
    · exact Or.inl ⟨h6, h7⟩

/-- Caller-block-polymorphic lift of `mergeFieldAllQ_budget_placed_ok` (e.g. for Block `46`,
`SessionRecord::deserialize`). -/
theorem mergeFieldAllQ_caller_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hA : AllocContractsBudgetPlaced M A lim H)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 15)
      (mergeFieldQBudgetSpecW M A lim (fun _ => True)) :=
  mergeFieldQBudget_caller_ok (mergeFieldAllQ_budget_placed_ok hA) hblk

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldChainsBudget
