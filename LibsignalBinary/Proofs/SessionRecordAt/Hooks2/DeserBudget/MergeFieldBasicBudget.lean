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
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DoReserveExt
public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.Defs
public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.MF14AuxW
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.E2E.Record.Support.Phi
import LibsignalBinary.Proofs.E2E.Record.L1GX.Leaf.MF9PAux.Pure
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.MergeFieldGenSessionVersionExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.MergeFieldGenIdentityRootKeysExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.MergeFieldGenPreviousCounterExt
import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.MF9PAuxW
import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.MF9PAuxWPlaced
import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.MergeField9PW
import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.MergeField9PWPlaced
import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.MergeField14WPlaced
import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.MergeField10_11_13_15W

/-!
# Budget-Threaded `SessionStructure::merge_field` on Basic Fields

Proves `mergeFieldBasic_budget_placed_ok` (`mergeFieldQBudgetSpecW`, Block `15`, `32,768` B) across
all 11 non-chain `GenFieldQ` tags (`IsBasicFieldQ`: `u32` varints `1, 5, 10, 11`, `Vec<u8>` fields
`2, 3, 4, 13, 15`, `PendingPreKey` tag `9`, and `PendingKyberPreKey` tag `14`) over
`[HasFineReallocCredit M]`, tracking capacity-explicit `prostSSGQAtCap` and symbolic cost bounds.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldBasicBudget

open Arm64 ProofLib SepProp
open CryptoVerification (
  LibsignalPlacement LibsignalHooks IsLsBlockProg
  LibsignalCodeLoaded LibsignalRoLoaded libsignalRoLoaded_of_keepsFrozen
  withLsCodeLoaded withLsCl lsmpl lsro8_intro
)
open CryptoVerification.RustHeap (
  RustAlloc vecOf vecAt vecBuf vecU8 vecU8At vecHeader arrayAt
)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalProtoCodec (
  WireType encodeVarint decodeVarint decodeVarint_encodeVarint
  mergeUint32 mergeBytes mergeBytes_encode
)
open CryptoVerification.E2E.Record (lenField)
open CryptoVerification.LibsignalTripleRatchet (
  DoReserveCall LibsignalCodeRoLoaded
  withLsCodeRoLoaded extract_withLsCodeRoLoaded
)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  DecodeVarintSliceGhost Int32MergeGhost BytesMergeGhost VarintSlicePre
  sliceCursorAt sliceCursorAfter varintSliceResultAt
)
open CryptoVerification.LibsignalTripleRatchet.Prost.X (
  decodeErrorHookStackW decodeVarintSliceStackW int32MergeStackW bytesMergeStackW
)
open CryptoVerification.E2E.Record.Placed (blkPC_15 blkPl_15 lsProg_15)
open CryptoVerification.E2E.Record.DeserializeSeed (mergeFieldRodataSym ls_call_ro_of_block)
open CryptoVerification.E2E.Record.DeserializeSeed.IdentityRootKeysStateSimp (
  setWidth8_setWidth64_setWidth32_identityRootKeys
  sp_sub_240_aligned_identityRootKeys
)
open CryptoVerification.E2E.Record.DeserializeGeneral (
  ChainG SSG GenField prostChainGAt prostSSGAt
)
open CryptoVerification.E2E.Record.L1GX (
  ExtraG SSGX GenFieldX pidAt kyberAt
  pendingIdBody pendingSpkBody kyberBody
)
open CryptoVerification.E2E.Record.L1GX.Leaf.MF9PAux (
  pendingB0_signExtend_1_x9p pendingB0_getLsbD_63_1_x9p
  pendingB0_signExtend_2_x9p pendingB0_getLsbD_63_2_x9p
  pendingId_payload_length_x9p pendingSpk_none_payload_length_x9p
  pendingSpk_some_payload_length_x9p
  setWidth32_setWidth64_x9p setWidth32_signExtend64_x9p
  mergeUint32_encode_64_x9p mergeBytes_k_x9p
  memRegion_40_split_x9p split_272_x9p pid_disc_lsb_x9p pid_none_entails_x9p
  emptyVec_pending_eq_vecU8At_x9p
)
open CryptoVerification.E2E.Record.L1GX.Leaf.MF14Aux (
  kyberB0 kyberB0_signExtend_getLsbD_63 kyberB0_signExtend_getLsbD_63_beq
  encodeVarint_length_bounds_mf14 innerBytes innerBytes_length
  kyberIdBytes kyberIdBytes_length
  kyber_payload_tail_length kyber_ne_payload_tail_length
  decodeVarint_kyber decodeVarint_kyber_ne
  mergeBytes_inner mergeUint32_kyberIdBytes
  memRegion_24_split_kyber emptyVec_kyber_eq_vecU8At
)
open Proofs.libsignal.Hooks2 (mergeFieldStackX mergeFieldSubStackX)
open Symbolic.Swarm.TRREF.B3DeserQ (
  ExtraGQ SSGQ GenFieldQ MergeFieldQGhost prostSSGQAt
  pendingPtr2
  len_ne_zero_x9pW sub1_and_add_neg1_x9pW subs_body_len_x9pW cmp_gt_tail_x9pW
  sliceCursorAt_int32_gen_fold_x9p sliceCursorAfter_int32_gen_unfold_x9p
  sliceCursorAt_bytes_gen_fold_x9p sliceCursorAfter_bytes_gen_unfold_x9p
  sliceCursorAt_unfold_id_x9p sliceCursorAt_unfold_spk_none_x9p
  sliceCursorAt_unfold_spk_some_x9p
  sliceCursorAfter_fold_id_x9p sliceCursorAfter_fold_spk_none_x9p
  sliceCursorAfter_fold_spk_some_x9p
  stackAt_mergeFieldX_unfold_x9pW bufRef_and_stackAt_mergeFieldX_fold_x9pW
  kyberAt14 kyberPtr2
  memRegion160_split_mf14 memRegion160_fold_mf14
  pointsTo64_zero_split32_mf14 cells24_entails_memRegion24_mf14
  sliceCursorAt_kyber_unfold_mf14 sliceCursorAt_kyber_ne_unfold_mf14
  bytes_kyber_split_mf14 bytes_kyber_ne_split_mf14
  sliceCursorAt_kyberId_fold_mf14 sliceCursorAfter_kyberId_unfold_mf14
  sliceCursorAt_inner_fold_mf14 sliceCursorAt_inner_ne_fold_mf14
  sliceCursorAfter_inner_unfold_mf14 sliceCursorAfter_inner_ne_unfold_mf14
  sliceCursorAfter_kyber_fold_mf14 sliceCursorAfter_kyber_ne_fold_mf14
  wt_and_ff_eq_mf14W wt_and_ff_64_eq_mf14W len_sub_mf14W
  stackAt_mergeField_unfold_mf14W stackAt_mergeField_fold_mf14W
  stackAt_sub_to_decode_mf14W stackAt_sub_to_int32Merge_mf14W
  stackAt_sub_to_bytesMerge_mf14W
  decode_to_int32Merge_stack_mf14W decode_to_bytesMerge_stack_mf14W
  int32Merge_to_bytesMerge_stack_mf14W
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEvent FitsEvents
  RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (
  HasFineReallocCredit fitsStep_of_fine_bounds
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.Potential (
  vecCap4Next vecCap4Of IsPow2Cap4 isPow2Cap4_next vec104GrowEvents
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.HookLift (
  AllocContractsBudgetPlaced withVmPreserved
  trapHooks sepWP_rebase_vmPreserved sepWP_seq_lscl_vm sepWP_seq_vmPreserved
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.ProstVarintVm (
  decodeVarintSliceSomeSpecW decode_varint_slice_some_placed_ok_cl
  int32MergeSomeSpecW int32_merge_some_placed_ok_cl
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.ProstMergeBudget (
  doReserveEvents doReserveBudgetSpecX do_reserve_budget_placed_ok_cl
  bytesMergeAllocEvents bytesMergeEvents bytesMergeOutCap
  bytesMergeOutCap_zero_zero bytesMergeOutCap_zero_pos
  stepEvents_bytesMergeFresh_zero stepEvents_bytesMergeFresh_small
  stepEvents_bytesMergeFresh_large
  bytesMergeFreshBudgetSpecW bytes_merge_fresh_budget_placed_okW
  bytes_merge_fresh_budget_placed_okW_cl
  sepWPp_seq_lsclro_vm
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.ChainBudget (
  vecU8FreshCap vecU8FreshCap_entails_vecU8 emptyCells_entails_vecU8FreshCap
  prostChainGAtCap prostChainGAtCap_entails_prostChainGAt
  chainMergeEvents
)

export LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.ProstMergeBudget (
  doReserveEvents doReserveBudgetSpecX do_reserve_budget_placed_ok_cl
  bytesMergeFreshBudgetSpecW bytes_merge_fresh_budget_placed_okW
)

set_option maxRecDepth 2000000

attribute [local irreducible] Program.fetch Program.externAt? FitsEvents
attribute [local simp, local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm] setWidth8_setWidth64_setWidth32_identityRootKeys
  kyberB0_signExtend_getLsbD_63 kyberB0_signExtend_getLsbD_63_beq
attribute [local wp_norm] kyberB0_signExtend_getLsbD_63 kyberB0_signExtend_getLsbD_63_beq
  pendingB0_signExtend_1_x9p pendingB0_getLsbD_63_1_x9p
  pendingB0_signExtend_2_x9p pendingB0_getLsbD_63_2_x9p

namespace MergeFieldStateSimp

@[local arm64_norm ↓, local wp_norm ↓]
theorem calleeSavedVRegs_setPC_mfb (s : State) (pc : BitVec 64) :
    calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem calleeSavedVRegs_setMem_setPC_mfb (s : State) (pc : BitVec 64) (m : Memory) :
    calleeSavedVRegs ((s.setPC pc).setMem m) = calleeSavedVRegs s := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_mfb (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_mfb (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem tpidrEl0_setPC_mfb (s : State) (pc : BitVec 64) :
    (s.setPC pc).tpidrEl0 = s.tpidrEl0 := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem tpidrEl0_setMem_setPC_mfb (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).tpidrEl0 = s.tpidrEl0 := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem mem_setPC_mfb (s : State) (pc : BitVec 64) :
    (s.setPC pc).mem = s.mem := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_mfb (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_mfb (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_mfb (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_setPC_mfb (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_mfb (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_setPC_mfb (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

end MergeFieldStateSimp

attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite isCalleeSavedVReg
attribute [local arm64_norm ↓, local wp_norm ↓]
  MergeFieldStateSimp.calleeSavedVRegs_setPC_mfb
  MergeFieldStateSimp.calleeSavedVRegs_setMem_setPC_mfb
  MergeFieldStateSimp.sp_setPC_mfb
  MergeFieldStateSimp.sp_setMem_setPC_mfb
  MergeFieldStateSimp.tpidrEl0_setPC_mfb
  MergeFieldStateSimp.tpidrEl0_setMem_setPC_mfb
  MergeFieldStateSimp.mem_setPC_mfb
  MergeFieldStateSimp.readReg64_setPC_mfb
  MergeFieldStateSimp.readReg64_setMem_setPC_mfb
  MergeFieldStateSimp.readReg32_setPC_mfb
  MergeFieldStateSimp.readReg32_setMem_setPC_mfb
  MergeFieldStateSimp.readReg_setPC_mfb
  MergeFieldStateSimp.readReg_setMem_setPC_mfb

/-! ## 1. Capacity-Explicit `prostSSGQAtCap` Layout, Erasure & Field Events -/

/-- Capacity-explicit `pending_pre_key: Option<PendingPreKey>` at `ss + 0xf8` (48 bytes). -/
def pendingAt9PCap (A : RustAlloc) (ss : BitVec 64) (v : SSGX) : SepProp :=
  match v.base.pending with
  | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
  | some k => vecU8FreshCap A (ss + 0xf8#64) k ∗
      pidAt ss v.ext.pid (((ss + 0x118#64) ↦₆₄ 0#64) ∗
        ((ss + 0x120#64) ↦₃₂ v.ext.spkId) ∗ memRegion (ss + 0x124#64) 4)

/-- Capacity-explicit `pending_kyber_pre_key: Option<PendingKyberPreKey>` at `ss + 0x128`
(32 bytes), followed by trailing scalar fields `R`. -/
def kyberAtCap (A : RustAlloc) (ss : BitVec 64) (kyber : Option (BitVec 32 × List (BitVec 8)))
    (R : SepProp) : SepProp :=
  match kyber with
  | none => ((ss + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x130#64) 24 ∗ R
  | some (i, ct) => vecU8FreshCap A (ss + 0x128#64) ct ∗ ((ss + 0x140#64) ↦₃₂ i) ∗
      memRegion (ss + 0x144#64) 4 ∗ R

/-- Standalone 32-byte capacity-explicit `pending_kyber_pre_key` layout at `ss + 0x128`. -/
def kyberAt14Cap (A : RustAlloc) (ss : BitVec 64)
    (kyber : Option (BitVec 32 × List (BitVec 8))) : SepProp :=
  match kyber with
  | none => ((ss + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x130#64) 24
  | some (i, ct) => vecU8FreshCap A (ss + 0x128#64) ct ∗ ((ss + 0x140#64) ↦₃₂ i) ∗
      memRegion (ss + 0x144#64) 4

theorem kyberAtCap_eq_kyberAt14Cap_sep (A : RustAlloc) (ss : BitVec 64)
    (kyber : Option (BitVec 32 × List (BitVec 8))) (R : SepProp) :
    kyberAtCap A ss kyber R = kyberAt14Cap A ss kyber ∗ R := by
  cases kyber with
  | none => simp only [kyberAtCap, kyberAt14Cap, sepConj_assoc]
  | some p => rcases p with ⟨i, ct⟩; simp only [kyberAtCap, kyberAt14Cap, sepConj_assoc]

theorem kyberAtCap_entails_kyberAt (A : RustAlloc) (ss : BitVec 64)
    (kyber : Option (BitVec 32 × List (BitVec 8))) (R : SepProp) :
    kyberAtCap A ss kyber R ⊢ kyberAt A ss kyber R := by
  cases kyber with
  | none => exact Entails.refl _
  | some p =>
    rcases p with ⟨i, ct⟩
    exact sepConj_mono_left (vecU8FreshCap_entails_vecU8 A (ss + 0x128#64) ct)

theorem kyberAt14Cap_entails_kyberAt14 (A : RustAlloc) (ss : BitVec 64)
    (kyber : Option (BitVec 32 × List (BitVec 8))) :
    kyberAt14Cap A ss kyber ⊢ kyberAt14 A ss kyber := by
  cases kyber with
  | none => exact Entails.refl _
  | some p =>
    rcases p with ⟨i, ct⟩
    exact sepConj_mono_left (vecU8FreshCap_entails_vecU8 A (ss + 0x128#64) ct)

theorem arrayAt_prostChainGAtCap_entails (A : RustAlloc) (cs : List ChainG) (ptr : BitVec 64) :
    arrayAt (fun c a => prostChainGAtCap A a (vecCap4Of c.keys.length) c) 104 ptr cs ⊢
      arrayAt (fun c a => prostChainGAt A a c) 104 ptr cs := by
  induction cs generalizing ptr with
  | nil => exact Entails.refl _
  | cons c rest ih =>
    simp only [arrayAt]
    exact sepConj_mono (prostChainGAtCap_entails_prostChainGAt A ptr (vecCap4Of c.keys.length) c)
      (ih (ptr + BitVec.ofNat 64 104))

/-- Capacity-explicit `SessionStructure` layout (`prostSSGQAtCap`, 344 bytes) tracking
`capRecv : Nat` (`ss + 0x48`) while preserving exact `prostSSGQAt A ss v` on existential erasure. -/
def prostSSGQAtCap (A : RustAlloc) (ss : BitVec 64) (capRecv : Nat) (v : SSGQ) : SepProp :=
  vecU8FreshCap A ss v.base.lik ∗
    vecU8FreshCap A (ss + 0x18#64) v.base.rik ∗
    vecU8FreshCap A (ss + 0x30#64) v.base.root ∗
    (∃∗ ptrRecv : BitVec 64,
      vecAt A 104 8 (fun c a => prostChainGAtCap A a (vecCap4Of c.keys.length) c)
        (ss + 0x48#64) (BitVec.ofNat 64 capRecv) ptrRecv v.base.recv) ∗
    vecU8FreshCap A (ss + 0x60#64) v.ext.abk ∗
    vecU8FreshCap A (ss + 0x78#64) v.ext.pq ∗
    (match v.base.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAtCap A (ss + 0x90#64) (vecCap4Of c.keys.length) c) ∗
    pendingAt9PCap A ss v.toSSGX ∗
    kyberAtCap A ss v.ext.kyber
      (((ss + 0x148#64) ↦₃₂ v.base.version) ∗ ((ss + 0x14c#64) ↦₃₂ v.base.prevCounter) ∗
        ((ss + 0x150#64) ↦₃₂ v.ext.remReg) ∗ ((ss + 0x154#64) ↦₃₂ v.ext.locReg))

theorem pendingAt9PCap_congr (A : RustAlloc) (ss : BitVec 64) {v1 v2 : SSGX}
    (hp : v1.base.pending = v2.base.pending)
    (hpid : v1.ext.pid = v2.ext.pid)
    (hspk : v1.ext.spkId = v2.ext.spkId) :
    pendingAt9PCap A ss v1 = pendingAt9PCap A ss v2 := by
  unfold pendingAt9PCap
  rw [hp, hpid, hspk]

abbrev prostSSGQNonScalarCap (A : RustAlloc) (ss : BitVec 64) (capRecv : Nat) (v : SSGQ) : SepProp :=
  vecU8FreshCap A ss v.base.lik ∗
    vecU8FreshCap A (ss + 0x18#64) v.base.rik ∗
    vecU8FreshCap A (ss + 0x30#64) v.base.root ∗
    (∃∗ ptrRecv : BitVec 64,
      vecAt A 104 8 (fun c a => prostChainGAtCap A a (vecCap4Of c.keys.length) c)
        (ss + 0x48#64) (BitVec.ofNat 64 capRecv) ptrRecv v.base.recv) ∗
    vecU8FreshCap A (ss + 0x60#64) v.ext.abk ∗
    vecU8FreshCap A (ss + 0x78#64) v.ext.pq ∗
    (match v.base.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAtCap A (ss + 0x90#64) (vecCap4Of c.keys.length) c) ∗
    pendingAt9PCap A ss v.toSSGX ∗
    kyberAt14Cap A ss v.ext.kyber

abbrev prostSSGQScalars (ss : BitVec 64) (v : SSGQ) : SepProp :=
  ((ss + 0x148#64) ↦₃₂ v.base.version) ∗ ((ss + 0x14c#64) ↦₃₂ v.base.prevCounter) ∗
    ((ss + 0x150#64) ↦₃₂ v.ext.remReg) ∗ ((ss + 0x154#64) ↦₃₂ v.ext.locReg)

abbrev prostSSGQRest_lik (A : RustAlloc) (ss : BitVec 64) (capRecv : Nat) (v : SSGQ) : SepProp :=
  vecU8FreshCap A (ss + 0x18#64) v.base.rik ∗
    vecU8FreshCap A (ss + 0x30#64) v.base.root ∗
    (∃∗ ptrRecv : BitVec 64,
      vecAt A 104 8 (fun c a => prostChainGAtCap A a (vecCap4Of c.keys.length) c)
        (ss + 0x48#64) (BitVec.ofNat 64 capRecv) ptrRecv v.base.recv) ∗
    vecU8FreshCap A (ss + 0x60#64) v.ext.abk ∗
    vecU8FreshCap A (ss + 0x78#64) v.ext.pq ∗
    (match v.base.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAtCap A (ss + 0x90#64) (vecCap4Of c.keys.length) c) ∗
    pendingAt9PCap A ss v.toSSGX ∗
    kyberAtCap A ss v.ext.kyber (prostSSGQScalars ss v)

abbrev prostSSGQRest_rik (A : RustAlloc) (ss : BitVec 64) (capRecv : Nat) (v : SSGQ) : SepProp :=
  vecU8FreshCap A ss v.base.lik ∗
    vecU8FreshCap A (ss + 0x30#64) v.base.root ∗
    (∃∗ ptrRecv : BitVec 64,
      vecAt A 104 8 (fun c a => prostChainGAtCap A a (vecCap4Of c.keys.length) c)
        (ss + 0x48#64) (BitVec.ofNat 64 capRecv) ptrRecv v.base.recv) ∗
    vecU8FreshCap A (ss + 0x60#64) v.ext.abk ∗
    vecU8FreshCap A (ss + 0x78#64) v.ext.pq ∗
    (match v.base.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAtCap A (ss + 0x90#64) (vecCap4Of c.keys.length) c) ∗
    pendingAt9PCap A ss v.toSSGX ∗
    kyberAtCap A ss v.ext.kyber (prostSSGQScalars ss v)

abbrev prostSSGQRest_root (A : RustAlloc) (ss : BitVec 64) (capRecv : Nat) (v : SSGQ) : SepProp :=
  vecU8FreshCap A ss v.base.lik ∗
    vecU8FreshCap A (ss + 0x18#64) v.base.rik ∗
    (∃∗ ptrRecv : BitVec 64,
      vecAt A 104 8 (fun c a => prostChainGAtCap A a (vecCap4Of c.keys.length) c)
        (ss + 0x48#64) (BitVec.ofNat 64 capRecv) ptrRecv v.base.recv) ∗
    vecU8FreshCap A (ss + 0x60#64) v.ext.abk ∗
    vecU8FreshCap A (ss + 0x78#64) v.ext.pq ∗
    (match v.base.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAtCap A (ss + 0x90#64) (vecCap4Of c.keys.length) c) ∗
    pendingAt9PCap A ss v.toSSGX ∗
    kyberAtCap A ss v.ext.kyber (prostSSGQScalars ss v)

abbrev prostSSGQRest_recv (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) : SepProp :=
  vecU8FreshCap A ss v.base.lik ∗
    vecU8FreshCap A (ss + 0x18#64) v.base.rik ∗
    vecU8FreshCap A (ss + 0x30#64) v.base.root ∗
    vecU8FreshCap A (ss + 0x60#64) v.ext.abk ∗
    vecU8FreshCap A (ss + 0x78#64) v.ext.pq ∗
    (match v.base.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAtCap A (ss + 0x90#64) (vecCap4Of c.keys.length) c) ∗
    pendingAt9PCap A ss v.toSSGX ∗
    kyberAtCap A ss v.ext.kyber (prostSSGQScalars ss v)

abbrev prostSSGQRest_abk (A : RustAlloc) (ss : BitVec 64) (capRecv : Nat) (v : SSGQ) : SepProp :=
  vecU8FreshCap A ss v.base.lik ∗
    vecU8FreshCap A (ss + 0x18#64) v.base.rik ∗
    vecU8FreshCap A (ss + 0x30#64) v.base.root ∗
    (∃∗ ptrRecv : BitVec 64,
      vecAt A 104 8 (fun c a => prostChainGAtCap A a (vecCap4Of c.keys.length) c)
        (ss + 0x48#64) (BitVec.ofNat 64 capRecv) ptrRecv v.base.recv) ∗
    vecU8FreshCap A (ss + 0x78#64) v.ext.pq ∗
    (match v.base.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAtCap A (ss + 0x90#64) (vecCap4Of c.keys.length) c) ∗
    pendingAt9PCap A ss v.toSSGX ∗
    kyberAtCap A ss v.ext.kyber (prostSSGQScalars ss v)

abbrev prostSSGQRest_pq (A : RustAlloc) (ss : BitVec 64) (capRecv : Nat) (v : SSGQ) : SepProp :=
  vecU8FreshCap A ss v.base.lik ∗
    vecU8FreshCap A (ss + 0x18#64) v.base.rik ∗
    vecU8FreshCap A (ss + 0x30#64) v.base.root ∗
    (∃∗ ptrRecv : BitVec 64,
      vecAt A 104 8 (fun c a => prostChainGAtCap A a (vecCap4Of c.keys.length) c)
        (ss + 0x48#64) (BitVec.ofNat 64 capRecv) ptrRecv v.base.recv) ∗
    vecU8FreshCap A (ss + 0x60#64) v.ext.abk ∗
    (match v.base.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAtCap A (ss + 0x90#64) (vecCap4Of c.keys.length) c) ∗
    pendingAt9PCap A ss v.toSSGX ∗
    kyberAtCap A ss v.ext.kyber (prostSSGQScalars ss v)

abbrev prostSSGQRest_sender (A : RustAlloc) (ss : BitVec 64) (capRecv : Nat) (v : SSGQ) : SepProp :=
  vecU8FreshCap A ss v.base.lik ∗
    vecU8FreshCap A (ss + 0x18#64) v.base.rik ∗
    vecU8FreshCap A (ss + 0x30#64) v.base.root ∗
    (∃∗ ptrRecv : BitVec 64,
      vecAt A 104 8 (fun c a => prostChainGAtCap A a (vecCap4Of c.keys.length) c)
        (ss + 0x48#64) (BitVec.ofNat 64 capRecv) ptrRecv v.base.recv) ∗
    vecU8FreshCap A (ss + 0x60#64) v.ext.abk ∗
    vecU8FreshCap A (ss + 0x78#64) v.ext.pq ∗
    pendingAt9PCap A ss v.toSSGX ∗
    kyberAtCap A ss v.ext.kyber (prostSSGQScalars ss v)

abbrev prostSSGQRest_pending (A : RustAlloc) (ss : BitVec 64) (capRecv : Nat) (v : SSGQ) : SepProp :=
  vecU8FreshCap A ss v.base.lik ∗
    vecU8FreshCap A (ss + 0x18#64) v.base.rik ∗
    vecU8FreshCap A (ss + 0x30#64) v.base.root ∗
    (∃∗ ptrRecv : BitVec 64,
      vecAt A 104 8 (fun c a => prostChainGAtCap A a (vecCap4Of c.keys.length) c)
        (ss + 0x48#64) (BitVec.ofNat 64 capRecv) ptrRecv v.base.recv) ∗
    vecU8FreshCap A (ss + 0x60#64) v.ext.abk ∗
    vecU8FreshCap A (ss + 0x78#64) v.ext.pq ∗
    (match v.base.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAtCap A (ss + 0x90#64) (vecCap4Of c.keys.length) c) ∗
    kyberAtCap A ss v.ext.kyber (prostSSGQScalars ss v)

abbrev prostSSGQRest_kyber (A : RustAlloc) (ss : BitVec 64) (capRecv : Nat) (v : SSGQ) : SepProp :=
  vecU8FreshCap A ss v.base.lik ∗
    vecU8FreshCap A (ss + 0x18#64) v.base.rik ∗
    vecU8FreshCap A (ss + 0x30#64) v.base.root ∗
    (∃∗ ptrRecv : BitVec 64,
      vecAt A 104 8 (fun c a => prostChainGAtCap A a (vecCap4Of c.keys.length) c)
        (ss + 0x48#64) (BitVec.ofNat 64 capRecv) ptrRecv v.base.recv) ∗
    vecU8FreshCap A (ss + 0x60#64) v.ext.abk ∗
    vecU8FreshCap A (ss + 0x78#64) v.ext.pq ∗
    (match v.base.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAtCap A (ss + 0x90#64) (vecCap4Of c.keys.length) c) ∗
    pendingAt9PCap A ss v.toSSGX ∗
    prostSSGQScalars ss v

theorem prostSSGQAtCap_entails_prostSSGQAt (A : RustAlloc) (ss : BitVec 64)
    (capRecv : Nat) (v : SSGQ) :
    prostSSGQAtCap A ss capRecv v ⊢ prostSSGQAt A ss v := by
  unfold prostSSGQAtCap prostSSGQAt
  refine sepConj_mono (vecU8FreshCap_entails_vecU8 A ss v.base.lik) ?_
  refine sepConj_mono (vecU8FreshCap_entails_vecU8 A (ss + 0x18#64) v.base.rik) ?_
  refine sepConj_mono (vecU8FreshCap_entails_vecU8 A (ss + 0x30#64) v.base.root) ?_
  refine sepConj_mono ?_ ?_
  · unfold vecOf
    apply Entails.sepExists_elim; intro ptrRecv
    refine Entails.sepExists_right (BitVec.ofNat 64 capRecv)
      (Entails.sepExists_right ptrRecv ?_)
    unfold vecAt vecBuf
    refine sepConj_mono_right (sepConj_mono_right ?_)
    split
    · exact Entails.refl _
    · exact sepConj_mono_right
        (sepConj_mono_left (arrayAt_prostChainGAtCap_entails A v.base.recv ptrRecv))
  · refine sepConj_mono (vecU8FreshCap_entails_vecU8 A (ss + 0x60#64) v.ext.abk) ?_
    refine sepConj_mono (vecU8FreshCap_entails_vecU8 A (ss + 0x78#64) v.ext.pq) ?_
    refine sepConj_mono ?_ ?_
    · cases v.base.sender with
      | none => exact Entails.refl _
      | some c => exact prostChainGAtCap_entails_prostChainGAt A (ss + 0x90#64) _ c
    · refine sepConj_mono ?_ (kyberAtCap_entails_kyberAt A ss v.ext.kyber _)
      dsimp only [pendingAt9PCap, SSGQ.toSSGX, ExtraGQ.toExtraG]
      cases v.base.pending with
      | none => exact Entails.refl _
      | some k => exact sepConj_mono_left (vecU8FreshCap_entails_vecU8 A (ss + 0xf8#64) k)

/-- Predicate selecting non-chain `GenFieldQ` tags (`1, 2, 3, 4, 5, 9, 10, 11, 13, 14, 15`). -/
def IsBasicFieldQ (fl : GenFieldQ) : Prop :=
  fl.tag ≠ 6 ∧ fl.tag ≠ 7

/-- Byte length of the single `Vec<u8>` allocated by a basic `GenFieldQ` (`0` for varints and chains). -/
def basicFieldByteLen : GenFieldQ → Nat
  | .base (.lik b) | .base (.rik b) | .base (.root b) => b.length
  | .base (.pending k) | .pendingId _ k | .pendingSpk _ k _ => k.length
  | .abk b | .pq b => b.length
  | .kyber _ ct => ct.length
  | _ => 0

/-- Next `receiver_chains` capacity after merging `fl : GenFieldQ` at current `(capRecv, curRecvLen)`. -/
def nextCapRecv (capRecv curRecvLen : Nat) : GenFieldQ → Nat
  | .base (.recv _) => if curRecvLen = capRecv then vecCap4Next capRecv else capRecv
  | _ => capRecv

/-- Complete `AllocEvent` list stepped on `M.σ` across `SessionStructure::merge_field` on `fl`. -/
def mergeFieldQEvents (capRecv curRecvLen : Nat) : GenFieldQ → List AllocEvent
  | .base (.sender c) => chainMergeEvents c
  | .base (.recv c) =>
      chainMergeEvents c ++ (if curRecvLen = capRecv then vec104GrowEvents capRecv else [])
  | fl => bytesMergeEvents 0 (basicFieldByteLen fl)

/-- Precondition `FitsEvents` list required to enter `SessionStructure::merge_field` on `fl` without OOM:
for basic byte fields, `bytes::merge` checks OOM on the two `alloc` steps before the infallible
scratch `dealloc`, i.e., `bytesMergeAllocEvents 0 (basicFieldByteLen fl)`. -/
def mergeFieldQFitsEvents (capRecv curRecvLen : Nat) : GenFieldQ → List AllocEvent
  | .base (.sender c) => chainMergeEvents c
  | .base (.recv c) =>
      chainMergeEvents c ++ (if curRecvLen = capRecv then vec104GrowEvents capRecv else [])
  | fl => bytesMergeAllocEvents 0 (basicFieldByteLen fl)

theorem fitsEvents_mergeFieldQFits_of_events {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {capRecv curRecvLen : Nat} {fl : GenFieldQ}
    (h : FitsEvents M lim st (mergeFieldQEvents capRecv curRecvLen fl)) :
    FitsEvents M lim st (mergeFieldQFitsEvents capRecv curRecvLen fl) := by
  cases fl with
  | base f =>
    cases f <;> simp only [mergeFieldQEvents, mergeFieldQFitsEvents] at h ⊢
    all_goals
      try exact h
      try
        unfold bytesMergeEvents at h
        rw [LibsignalBinary.Heap.fitsEvents_append] at h
        exact h.1
  | _ =>
    simp only [mergeFieldQEvents, mergeFieldQFitsEvents] at h ⊢
    unfold bytesMergeEvents at h
    rw [LibsignalBinary.Heap.fitsEvents_append] at h
    exact h.1

/-- Symbolic small-slot cost of a basic `GenFieldQ` (`0` for varints `1, 5, 10, 11`;
two small allocs `n` and `max n 8` when `n ≤ smallMaxReq M`; `2 * largeMetaCost M` when `n > smallMaxReq M`). -/
def basicFieldSmallCost (M : AllocCostModel) [HasFineReallocCredit M] (fl : GenFieldQ) : Nat :=
  let n := basicFieldByteLen fl
  if n = 0 then 0
  else if n ≤ HasFineReallocCredit.smallMaxReq M then
    HasFineReallocCredit.smallAllocCost M n + HasFineReallocCredit.smallAllocCost M (max n 8)
  else 2 * HasFineReallocCredit.largeMetaCost M

/-- Symbolic post-merge direct-`mmap` live cost of a basic `GenFieldQ` (`0` when `n ≤ smallMaxReq M`,
else `largeCost M n`, e.g. for large `pq_ratchet_state` on tag `15`). -/
def basicFieldLargeLive (M : AllocCostModel) [HasFineReallocCredit M] (fl : GenFieldQ) : Nat :=
  let n := basicFieldByteLen fl
  if n ≤ HasFineReallocCredit.smallMaxReq M then 0
  else HasFineReallocCredit.largeCost M n

/-- Symbolic transient direct-`mmap` peak of a basic `GenFieldQ` (`0` when `n ≤ smallMaxReq M`,
else `2 * largeCost M n` during `Bytes -> Vec<u8>` conversion in `prost::encoding::bytes::merge`). -/
def basicFieldPeakLarge (M : AllocCostModel) [HasFineReallocCredit M] (fl : GenFieldQ) : Nat :=
  let n := basicFieldByteLen fl
  if n ≤ HasFineReallocCredit.smallMaxReq M then 0
  else 2 * HasFineReallocCredit.largeCost M n

theorem stepEvents_mergeFieldBasic_bounds (M : AllocCostModel) [HasFineReallocCredit M]
    {fl : GenFieldQ} (hbasic : IsBasicFieldQ fl)
    (h8 : 8 ≤ HasFineReallocCredit.smallMaxReq M)
    (capRecv curRecvLen : Nat) (st : M.σ) :
    let st' := M.stepEvents (mergeFieldQEvents capRecv curRecvLen fl) st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st + basicFieldSmallCost M fl ∧
    HasFineReallocCredit.liveLarge st' ≤
      HasFineReallocCredit.liveLarge st + basicFieldLargeLive M fl ∧
    HasFineReallocCredit.peakLarge st' ≤
      max (HasFineReallocCredit.peakLarge st)
        (HasFineReallocCredit.liveLarge st + basicFieldPeakLarge M fl) := by
  have hev : mergeFieldQEvents capRecv curRecvLen fl =
      bytesMergeEvents 0 (basicFieldByteLen fl) := by
    rcases hbasic with ⟨h6, h7⟩
    cases fl with
    | base f =>
      cases f with
      | sender _ => exact False.elim (h6 rfl)
      | recv _ => exact False.elim (h7 rfl)
      | _ => rfl
    | _ => rfl
  dsimp only [basicFieldSmallCost, basicFieldLargeLive, basicFieldPeakLarge]
  rw [hev]
  set n := basicFieldByteLen fl
  by_cases hn0 : n = 0
  · have hle : n ≤ HasFineReallocCredit.smallMaxReq M := by omega
    simp only [hn0, hle, ↓reduceIte, stepEvents_bytesMergeFresh_zero, Nat.add_zero]
    exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_max_left _ _⟩
  · have hpos : 0 < n := by omega
    by_cases hsm : n ≤ HasFineReallocCredit.smallMaxReq M
    · have hmax : max n 8 ≤ HasFineReallocCredit.smallMaxReq M := by omega
      obtain ⟨hc, hl, hp⟩ := stepEvents_bytesMergeFresh_small M st hpos hmax
      simp only [hn0, hsm, ↓reduceIte, Nat.add_zero]
      exact ⟨by omega, hl, Nat.le_trans hp (Nat.le_max_left _ _)⟩
    · have hgt : HasFineReallocCredit.smallMaxReq M < n := by omega
      obtain ⟨hc, hl, hp⟩ := stepEvents_bytesMergeFresh_large M st h8 hgt
      simp only [hn0, hsm, ↓reduceIte]
      exact ⟨hc, hl, hp⟩

/-- Fresh-`Vec<u8>` precondition for base identity/root key tags (`2, 3, 4`), complementing
`GenFieldQ.Fresh` (which already enforces `abk = []`, `kyber = none`, `pq = []`, `pending = none`,
`sender = none`, and `recv.length < maxReceiverChains`). -/
def GenFieldQ.FreshBytes (v : SSGQ) : GenFieldQ → Prop
  | .base (.lik _) => v.base.lik = []
  | .base (.rik _) => v.base.rik = []
  | .base (.root _) => v.base.root = []
  | _ => True

/-- Image-free base contract of budget-threaded `SessionStructure::merge_field` (Block `15`,
`mergeFieldStackX`) restricted to `P : GenFieldQ → Prop`. -/
def mergeFieldQBudgetRawSpecW (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (P : GenFieldQ → Prop) :
    Spec (MergeFieldQGhost × Nat × M.σ) where
  pre := fun (x, capRecv, st) s =>
    ⌜s.readReg64 .x0 = x.ss ∧
      (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 x.fld.tag ∧
      (s.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 x.fld.wt.toNat ∧
      s.readReg64 .x3 = x.bufRef ∧
      (s.readReg64 .x4).setWidth 32 = 99#32 ∧
      P x.fld ∧ x.fld.Ok ∧ x.fld.Fresh x.v ∧ GenFieldQ.FreshBytes x.v x.fld ∧
      (x.fld.payload ++ x.tail).length < 2 ^ 62 ∧
      IsPow2Cap4 capRecv ∧ x.v.base.recv.length ≤ capRecv ∧ capRecv < 2 ^ 62 ∧
      FitsEvents M lim st (mergeFieldQFitsEvents capRecv x.v.base.recv.length x.fld)⌝ ∗
      prostSSGQAtCap A.repAlloc x.ss capRecv x.v ∗
      (x.bufRef ↦₆₄ x.slot) ∗
      sliceCursorAt x.slot x.ptr (x.fld.payload ++ x.tail) ∗
      A.pool lim st s ∗
      stackAt s.sp mergeFieldStackX
  post := fun (x, capRecv, st) s0 sf =>
    let capRecv' := nextCapRecv capRecv x.v.base.recv.length x.fld
    let st' := M.stepEvents (mergeFieldQEvents capRecv x.v.base.recv.length x.fld) st
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗
      prostSSGQAtCap A.repAlloc x.ss capRecv' (x.v.apply x.fld) ∗
      (x.bufRef ↦₆₄ x.slot) ∗
      sliceCursorAfter x.slot x.ptr (x.fld.payload ++ x.tail) x.tail ∗
      A.pool lim st' sf ∗
      stackAt s0.sp mergeFieldStackX

/-- Relocatable `[LibsignalPlacement]` budget-threaded `SessionStructure::merge_field` spec
(Block `15`, `lsProg_15 H`, `mergeFieldStackX`) restricted to `P : GenFieldQ → Prop`. -/
abbrev mergeFieldQBudgetSpecW [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (P : GenFieldQ → Prop) : Spec (MergeFieldQGhost × Nat × M.σ) :=
  withLsCodeRoLoaded lsmpl (mergeFieldQBudgetRawSpecW M A lim P)


open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.GrowOne104Budget (
  sepWP_ret_vmPreserved
)

/-! ## 2. `VmPreserved`, Spec Combinators & `SepWPp` Call Infrastructure -/

namespace MergeFieldVmSimp

@[local simp, local arm64_norm ↓, local wp_norm ↓]
theorem brkStart_setPC (s : State) (pc : BitVec 64) :
    (s.setPC pc).brkStart = s.brkStart := by cases s; rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
theorem brk_setPC (s : State) (pc : BitVec 64) :
    (s.setPC pc).brk = s.brk := by cases s; rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
theorem physMemAvail_setPC (s : State) (pc : BitVec 64) :
    (s.setPC pc).physMemAvail = s.physMemAvail := by cases s; rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
theorem brkStart_advancePC (s : State) :
    s.advancePC.brkStart = s.brkStart := by cases s; rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
theorem brk_advancePC (s : State) :
    s.advancePC.brk = s.brk := by cases s; rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
theorem physMemAvail_advancePC (s : State) :
    s.advancePC.physMemAvail = s.physMemAvail := by cases s; rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
theorem tpidrEl0_advancePC (s : State) :
    s.advancePC.tpidrEl0 = s.tpidrEl0 := by cases s; rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
theorem mem_advancePC (s : State) :
    s.advancePC.mem = s.mem := by cases s; rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
theorem brkStart_setPState (s : State) (ps : PState) :
    (s.setPState ps).brkStart = s.brkStart := by cases s; rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
theorem brk_setPState (s : State) (ps : PState) :
    (s.setPState ps).brk = s.brk := by cases s; rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
theorem physMemAvail_setPState (s : State) (ps : PState) :
    (s.setPState ps).physMemAvail = s.physMemAvail := by cases s; rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
theorem tpidrEl0_setPState (s : State) (ps : PState) :
    (s.setPState ps).tpidrEl0 = s.tpidrEl0 := by cases s; rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
theorem mem_setPState (s : State) (ps : PState) :
    (s.setPState ps).mem = s.mem := by cases s; rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
theorem brkStart_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).brkStart = s.brkStart := by cases s; cases r <;> rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
theorem brk_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).brk = s.brk := by cases s; cases r <;> rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
theorem physMemAvail_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).physMemAvail = s.physMemAvail := by cases s; cases r <;> rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
theorem tpidrEl0_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).tpidrEl0 = s.tpidrEl0 := by cases s; cases r <;> rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
theorem mem_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).mem = s.mem := by cases s; cases r <;> rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
theorem brkStart_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).brkStart = s.brkStart := by cases s; cases r <;> rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
theorem brk_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).brk = s.brk := by cases s; cases r <;> rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
theorem physMemAvail_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).physMemAvail = s.physMemAvail := by cases s; cases r <;> rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
theorem tpidrEl0_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).tpidrEl0 = s.tpidrEl0 := by cases s; cases r <;> rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
theorem mem_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).mem = s.mem := by cases s; cases r <;> rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
theorem brkStart_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).brkStart = s.brkStart := by cases s; cases w <;> cases r <;> rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
theorem brk_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).brk = s.brk := by cases s; cases w <;> cases r <;> rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
theorem physMemAvail_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).physMemAvail = s.physMemAvail := by cases s; cases w <;> cases r <;> rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
theorem tpidrEl0_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).tpidrEl0 = s.tpidrEl0 := by cases s; cases w <;> cases r <;> rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
theorem mem_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).mem = s.mem := by cases s; cases w <;> cases r <;> rfl

end MergeFieldVmSimp

attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  MergeFieldVmSimp.brkStart_setPC MergeFieldVmSimp.brk_setPC MergeFieldVmSimp.physMemAvail_setPC
  MergeFieldVmSimp.brkStart_advancePC MergeFieldVmSimp.brk_advancePC
  MergeFieldVmSimp.physMemAvail_advancePC MergeFieldVmSimp.tpidrEl0_advancePC
  MergeFieldVmSimp.mem_advancePC
  MergeFieldVmSimp.brkStart_setPState MergeFieldVmSimp.brk_setPState
  MergeFieldVmSimp.physMemAvail_setPState MergeFieldVmSimp.tpidrEl0_setPState
  MergeFieldVmSimp.mem_setPState
  MergeFieldVmSimp.brkStart_writeReg64 MergeFieldVmSimp.brk_writeReg64
  MergeFieldVmSimp.physMemAvail_writeReg64 MergeFieldVmSimp.tpidrEl0_writeReg64
  MergeFieldVmSimp.mem_writeReg64
  MergeFieldVmSimp.brkStart_writeReg32 MergeFieldVmSimp.brk_writeReg32
  MergeFieldVmSimp.physMemAvail_writeReg32 MergeFieldVmSimp.tpidrEl0_writeReg32
  MergeFieldVmSimp.mem_writeReg32
  MergeFieldVmSimp.brkStart_writeReg MergeFieldVmSimp.brk_writeReg
  MergeFieldVmSimp.physMemAvail_writeReg MergeFieldVmSimp.tpidrEl0_writeReg
  MergeFieldVmSimp.mem_writeReg

theorem mergeFieldBasicFits_of_bytesMerge {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {capRecv curRecvLen : Nat} {fl : GenFieldQ} (hbasic : IsBasicFieldQ fl)
    (h : FitsEvents M lim st (bytesMergeAllocEvents 0 (basicFieldByteLen fl))) :
    FitsEvents M lim st (mergeFieldQFitsEvents capRecv curRecvLen fl) := by
  rcases hbasic with ⟨h6, h7⟩
  cases fl with
  | base f =>
    cases f with
    | sender _ => exact False.elim (h6 rfl)
    | recv _ => exact False.elim (h7 rfl)
    | _ => exact h
  | _ => exact h

theorem mergeFieldQBudgetSpecW_pre_iff [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : GenFieldQ → Prop} {g : MergeFieldQGhost × Nat × M.σ} {s : State} {R : SepProp} :
    (s.mem ⊨ (mergeFieldQBudgetSpecW M A lim P).pre g s ∗ R) ↔
      P g.1.fld ∧ (s.mem ⊨ (mergeFieldQBudgetSpecW M A lim (fun _ => True)).pre g s ∗ R) := by
  rcases g with ⟨x, capRecv, st⟩
  simp only [mergeFieldQBudgetSpecW, withLsCodeRoLoaded, mergeFieldQBudgetRawSpecW,
    sepConj_assoc, satisfies_pure_sepConj]
  tauto

theorem mergeFieldQBudget_of_imp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {P Q : GenFieldQ → Prop}
    (hP : subroutine_ok (lsProg_15 H) (blkPl_15).base (mergeFieldQBudgetSpecW M A lim P))
    (hQP : ∀ fl, Q fl → P fl) :
    subroutine_ok (lsProg_15 H) (blkPl_15).base (mergeFieldQBudgetSpecW M A lim Q) := by
  refine subroutine_ok_outcome_intro fun g R s0 hpc hrun hpre hal => ?_
  obtain ⟨hq, hpre'⟩ := mergeFieldQBudgetSpecW_pre_iff.mp hpre
  exact hP.mono_outcome g R s0 hpc hrun
    (mergeFieldQBudgetSpecW_pre_iff.mpr ⟨hQP _ hq, hpre'⟩) hal fun _ hout => hout

theorem mergeFieldQBudget_or [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {P Q : GenFieldQ → Prop}
    (hP : subroutine_ok (lsProg_15 H) (blkPl_15).base (mergeFieldQBudgetSpecW M A lim P))
    (hQ : subroutine_ok (lsProg_15 H) (blkPl_15).base (mergeFieldQBudgetSpecW M A lim Q)) :
    subroutine_ok (lsProg_15 H) (blkPl_15).base
      (mergeFieldQBudgetSpecW M A lim (fun fl => P fl ∨ Q fl)) := by
  refine subroutine_ok_outcome_intro fun g R s0 hpc hrun hpre hal => ?_
  obtain ⟨hpq, hpre'⟩ := mergeFieldQBudgetSpecW_pre_iff.mp hpre
  rcases hpq with hp | hq
  · exact hP.mono_outcome g R s0 hpc hrun
      (mergeFieldQBudgetSpecW_pre_iff.mpr ⟨hp, hpre'⟩) hal fun _ hout => hout
  · exact hQ.mono_outcome g R s0 hpc hrun
      (mergeFieldQBudgetSpecW_pre_iff.mpr ⟨hq, hpre'⟩) hal fun _ hout => hout

abbrev NoPanicPost : State → SepProp → Prop := fun _ _ => False

theorem sepWPp_mono_post {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q1 Q2 Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q1 Qp)
    (hq : ∀ sf Pf, Q1 sf Pf → Q2 sf Pf) :
    SepWPp prog ret s P Q2 Qp := by
  intro R hm hL
  obtain ⟨sf, hsteps, hout⟩ := h R hm hL
  refine ⟨sf, hsteps, ?_⟩
  rcases hout with ⟨hpc, hrun, Pf, hmf, hQ1⟩ | hpan | hoom
  · exact Or.inl ⟨hpc, hrun, Pf, hmf, hq sf Pf hQ1⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hoom)

theorem sepWPp_pure_left_and {prog : Program} {ret : BitVec 64} {s : State}
    {φ : Prop} {B F : SepProp} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (B ∗ F) Q Qp) :
    SepWPp prog ret s ((⌜φ⌝ ∗ B) ∗ F) Q Qp := by
  intro R hm hL
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 R (by simpa only [sepConj_assoc] using hm.2) hL

theorem sepWPp_exists_left {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {P : α → SepProp} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ a : α, SepWPp prog ret s (P a ∗ F) Q Qp) :
    SepWPp prog ret s ((∃∗ a : α, P a) ∗ F) Q Qp := by
  intro R hm hL
  rw [sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨a, hma⟩ := hm
  exact h a R (by simpa only [sepConj_assoc] using hma) hL

theorem sepWP_drop_left_mfb {prog : Program} {target_pc : BitVec 64}
    {s : State} {Drop P : SepProp} {post : State → SepProp → Prop}
    (h : SepWP prog target_pc s P post) : SepWP prog target_pc s (Drop ∗ P) post := by
  unfold SepWP at h ⊢; intro R hm
  rw [sepConj_assoc] at hm; exact h R (Satisfies.of_sep_right hm)

theorem sepWP_intro_ro8_mfb [LibsignalPlacement]
    {prog : Program} {target_pc : BitVec 64} (addr : BitVec 64) (b : BitVec 8)
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hintro : ∀ {Q : SepProp}, (s.mem ⊨ Q) → (s.mem ⊨ (addr ↦₈ᵣ b) ∗ Q))
    (h : SepWP prog target_pc s ((addr ↦₈ᵣ b) ∗ P) post) :
    SepWP prog target_pc s P post := by
  unfold SepWP at h ⊢; intro R hm
  have hR := h R; rw [sepConj_assoc] at hR
  exact hR (hintro hm)

theorem vmPreserved_0x28_15 [LibsignalPlacement] (s : State) :
    VmPreserved s
      ((s.writeReg64 (.gpr 9#5) ((blkPl_15).ρ mergeFieldRodataSym)).setPC
        ((blkPl_15).base + 48#64)) :=
  ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun _ _ _ => rfl⟩

theorem sepWPp_step_0x28_15 [LibsignalPlacement] {H : LibsignalHooks}
    {ret : BitVec 64} {s : State} {Pre : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hro : LibsignalRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_15).base + 40#64) (hrun : s.status = .Running)
    (hnext :
      VmPreserved s
        ((s.writeReg64 (.gpr 9#5) ((blkPl_15).ρ mergeFieldRodataSym)).setPC
          ((blkPl_15).base + 48#64)) →
      LibsignalCodeLoaded lsmpl
        (((s.writeReg64 (.gpr 9#5) ((blkPl_15).ρ mergeFieldRodataSym)).setPC
          ((blkPl_15).base + 48#64)).mem) →
      LibsignalRoLoaded lsmpl
        (((s.writeReg64 (.gpr 9#5) ((blkPl_15).ρ mergeFieldRodataSym)).setPC
          ((blkPl_15).base + 48#64)).mem) →
      SepWPp (lsProg_15 H) ret
        ((s.writeReg64 (.gpr 9#5) ((blkPl_15).ρ mergeFieldRodataSym)).setPC
          ((blkPl_15).base + 48#64))
        Pre Q Qp) :
    SepWPp (lsProg_15 H) ret s Pre Q Qp := by
  have h1 : SepWP (lsProg_15 H) ((blkPl_15).base + 48#64) s emp
      (fun sm _ => sm = (s.writeReg64 (.gpr 9#5) ((blkPl_15).ρ mergeFieldRodataSym)).setPC
        ((blkPl_15).base + 48#64)) :=
    CryptoVerification.E2E.Record.Placed.blkPC_15_pairStep_0x28 (blkPl_15).base H rfl hpc hrun
      (SepWP.done rfl hrun rfl)
  have hnext' := hnext (vmPreserved_0x28_15 s) hcl hro
  intro R hm hL
  have hm0 : s.mem ⊨ emp ∗ (Pre ∗ R) := by rw [emp_sepConj]; exact hm
  rcases SepWP.to_reaches_pc h1 hm0 hL with ⟨sm, hst1, ⟨_, _, _, _, rfl⟩ | ⟨_, hoom⟩⟩
  · obtain ⟨sf, hst2, hout⟩ := hnext' R hm (hst1.codeLoaded hL)
    exact ⟨sf, hst1.trans hst2, hout⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

theorem sepWPp_call_lscl_15 [LibsignalPlacement] {α : Type} {H : LibsignalHooks}
    {target ret_pc ret : BitVec 64} {spec : Spec α} {x : α}
    {s : State} {Pre F : SepProp} {Q : State → SepProp → Prop}
    (hsub : subroutine_ok (lsProg_15 H) target (withLsCl lsmpl spec))
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hro : LibsignalRoLoaded lsmpl s.mem)
    (hpc : s.pc = target) (hrun : s.status = .Running) (hal : s.spAligned = true)
    (hlr : s.readReg64 .lr = ret_pc)
    (hpre : Pre ⊢ spec.pre x s ∗ F)
    (hcont : ∀ sf : State,
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp →
      CalleeSavedPreserved s sf →
      LibsignalCodeLoaded lsmpl sf.mem → LibsignalRoLoaded lsmpl sf.mem →
      SepWPp (lsProg_15 H) ret sf (spec.post x s sf ∗ F) Q NoPanicPost)
    (hpan : ∀ sf R', ¬ (sf.mem ⊨ spec.onPanic x s sf ∗ R') := by
      intro _ _ hm; exact not_satisfies_false_sepConj hm)
    (hexit : ∀ sf ec R', ¬ (sf.mem ⊨ spec.onExit x ec s sf ∗ R') := by
      intro _ _ _ hm; exact not_satisfies_false_sepConj hm)
    (hoom : ∀ sf R', ¬ (sf.mem ⊨ spec.onOom x s sf ∗ R') := by
      intro _ _ hm; exact not_satisfies_false_sepConj hm) :
    SepWPp (lsProg_15 H) ret s Pre Q NoPanicPost := by
  intro R hm hL
  have hm' : s.mem ⊨ (withLsCl lsmpl spec).pre x s ∗ (F ∗ R) := by
    have hm1 := Satisfies.mono (sepConj_mono_left hpre) hm
    dsimp only [withLsCl]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl, by simpa only [sepConj_assoc] using hm1⟩
  obtain ⟨sm, hsteps, hout, _⟩ :=
    hsub.no_fault_before_outcome x (F ∗ R) s hpc hrun hm' hal hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpostm⟩ | ⟨_, hpanm⟩ | ⟨ec, _, hexm⟩ | ⟨_, hoomm⟩
  · have hcl_m := hcl.of_keepsFrozen hsteps.keepsFrozen
    have hro_m := libsignalRoLoaded_of_keepsFrozen hro hsteps.keepsFrozen
    rw [hlr] at hpcm
    dsimp only [withLsCl] at hpostm
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpostm
    have hpostm' : sm.mem ⊨ (spec.post x s sm ∗ F) ∗ R := by
      simpa only [sepConj_assoc] using hpostm.2
    obtain ⟨sf, hsteps', hout'⟩ :=
      hcont sm hpcm hrunm hspm hcsm hcl_m hro_m R hpostm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [withLsCl] at hpanm; exact (hpan sm _ hpanm).elim
  · dsimp only [withLsCl] at hexm; exact (hexit sm ec _ hexm).elim
  · dsimp only [withLsCl] at hoomm; exact (hoom sm _ hoomm).elim

theorem sepWPp_call_lscro_15 [LibsignalPlacement] {α : Type} {H : LibsignalHooks}
    {target ret_pc ret : BitVec 64} {spec : Spec α} {x : α}
    {s : State} {Pre F : SepProp} {Q : State → SepProp → Prop}
    (hsub : subroutine_ok (lsProg_15 H) target (withLsCodeRoLoaded lsmpl spec))
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hro : LibsignalRoLoaded lsmpl s.mem)
    (hpc : s.pc = target) (hrun : s.status = .Running) (hal : s.spAligned = true)
    (hlr : s.readReg64 .lr = ret_pc)
    (hpre : Pre ⊢ spec.pre x s ∗ F)
    (hcont : ∀ sf : State,
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp →
      CalleeSavedPreserved s sf →
      LibsignalCodeLoaded lsmpl sf.mem → LibsignalRoLoaded lsmpl sf.mem →
      SepWPp (lsProg_15 H) ret sf (spec.post x s sf ∗ F) Q NoPanicPost)
    (hpan : ∀ sf R', ¬ (sf.mem ⊨ spec.onPanic x s sf ∗ R') := by
      intro _ _ hm; exact not_satisfies_false_sepConj hm)
    (hexit : ∀ sf ec R', ¬ (sf.mem ⊨ spec.onExit x ec s sf ∗ R') := by
      intro _ _ _ hm; exact not_satisfies_false_sepConj hm)
    (hoom : ∀ sf R', ¬ (sf.mem ⊨ spec.onOom x s sf ∗ R') := by
      intro _ _ hm; exact not_satisfies_false_sepConj hm) :
    SepWPp (lsProg_15 H) ret s Pre Q NoPanicPost := by
  intro R hm hL
  have hm' : s.mem ⊨ (withLsCodeRoLoaded lsmpl spec).pre x s ∗ (F ∗ R) := by
    have hm1 := Satisfies.mono (sepConj_mono_left hpre) hm
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨⟨hcl, hro⟩, by simpa only [sepConj_assoc] using hm1⟩
  obtain ⟨sm, hsteps, hout, _⟩ :=
    hsub.no_fault_before_outcome x (F ∗ R) s hpc hrun hm' hal hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpostm⟩ | ⟨_, hpanm⟩ | ⟨ec, _, hexm⟩ | ⟨_, hoomm⟩
  · have hcl_m := hcl.of_keepsFrozen hsteps.keepsFrozen
    have hro_m := libsignalRoLoaded_of_keepsFrozen hro hsteps.keepsFrozen
    rw [hlr] at hpcm
    dsimp only [withLsCodeRoLoaded] at hpostm
    have hpostm' : sm.mem ⊨ (spec.post x s sm ∗ F) ∗ R := by
      simpa only [sepConj_assoc] using hpostm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hcont sm hpcm hrunm hspm hcsm hcl_m hro_m R hpostm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [withLsCodeRoLoaded] at hpanm; exact (hpan sm _ hpanm).elim
  · dsimp only [withLsCodeRoLoaded] at hexm; exact (hexit sm ec _ hexm).elim
  · dsimp only [withLsCodeRoLoaded] at hoomm; exact (hoom sm _ hoomm).elim

theorem entails_pure_sep_frame {P : Prop} {A B F : SepProp}
    (hp : P) (h : A ⊢ B ∗ F) : A ⊢ (⌜P⌝ ∗ B) ∗ F := by
  rw [eq_true hp, pure_true, emp_sepConj]; exact h

theorem entails_rw_stack_3 {Pre B1 B2 : SepProp} {sp1 sp2 : BitVec 64} {w1 w2 : Nat} {F : SepProp}
    (hsp : sp1 = sp2) (hw : w1 = w2)
    (h : Pre ⊢ (B1 ∗ B2 ∗ stackAt sp2 w2) ∗ F) :
    Pre ⊢ (B1 ∗ B2 ∗ stackAt sp1 w1) ∗ F := by
  subst hsp; subst hw; exact h

theorem entails_rw_stack_4 {Pre B1 B2 B3 : SepProp} {sp1 sp2 : BitVec 64} {w1 w2 : Nat} {F : SepProp}
    (hsp : sp1 = sp2) (hw : w1 = w2)
    (h : Pre ⊢ (B1 ∗ B2 ∗ B3 ∗ stackAt sp2 w2) ∗ F) :
    Pre ⊢ (B1 ∗ B2 ∗ B3 ∗ stackAt sp1 w1) ∗ F := by
  subst hsp; subst hw; exact h

theorem entails_rw_stack_5 {Pre B1 B2 B3 B4 : SepProp} {sp1 sp2 : BitVec 64} {w1 w2 : Nat} {F : SepProp}
    (hsp : sp1 = sp2) (hw : w1 = w2)
    (h : Pre ⊢ (B1 ∗ B2 ∗ B3 ∗ B4 ∗ stackAt sp2 w2) ∗ F) :
    Pre ⊢ (B1 ∗ B2 ∗ B3 ∗ B4 ∗ stackAt sp1 w1) ∗ F := by
  subst hsp; subst hw; exact h

private theorem entails_swap_stack_4 {Pre B1 B2 B3 M1 S1 M2 S2 F' : SepProp}
    (hswap : M1 ∗ S1 = M2 ∗ S2)
    (h : Pre ⊢ (B1 ∗ B2 ∗ B3 ∗ M1 ∗ S1) ∗ F') :
    Pre ⊢ (B1 ∗ B2 ∗ B3 ∗ S2) ∗ (M2 ∗ F') := by
  refine Entails.trans h (Entails.of_eq ?_)
  have h1 : (B1 ∗ B2 ∗ B3 ∗ M1 ∗ S1) ∗ F' = (M1 ∗ S1) ∗ (B1 ∗ B2 ∗ B3 ∗ F') := by sep_ac_rfl
  rw [h1, hswap]
  sep_ac_rfl

private theorem entails_swap_stack_5 {Pre B1 B2 B3 B4 M1 S1 M2 S2 F' : SepProp}
    (hswap : M1 ∗ S1 = M2 ∗ S2)
    (h : Pre ⊢ (B1 ∗ B2 ∗ B3 ∗ B4 ∗ M1 ∗ S1) ∗ F') :
    Pre ⊢ (B1 ∗ B2 ∗ B3 ∗ B4 ∗ S2) ∗ (M2 ∗ F') := by
  refine Entails.trans h (Entails.of_eq ?_)
  have h1 : (B1 ∗ B2 ∗ B3 ∗ B4 ∗ M1 ∗ S1) ∗ F' = (M1 ∗ S1) ∗ (B1 ∗ B2 ∗ B3 ∗ B4 ∗ F') := by
    sep_ac_rfl
  rw [h1, hswap]
  sep_ac_rfl

theorem subroutine_ok_of_field_sepWPp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {P : GenFieldQ → Prop}
    (h : ∀ (x : MergeFieldQGhost) (capRecv : Nat) (st : M.σ) (s0 : State),
      s0.pc = (blkPl_15).base → s0.status = .Running → s0.spAligned = true →
      LibsignalCodeLoaded lsmpl s0.mem → LibsignalRoLoaded lsmpl s0.mem →
      s0.readReg64 .x0 = x.ss →
      (s0.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 x.fld.tag →
      (s0.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 x.fld.wt.toNat →
      s0.readReg64 .x3 = x.bufRef →
      (s0.readReg64 .x4).setWidth 32 = 99#32 →
      P x.fld → x.fld.Ok → x.fld.Fresh x.v → GenFieldQ.FreshBytes x.v x.fld →
      (x.fld.payload ++ x.tail).length < 2 ^ 62 →
      IsPow2Cap4 capRecv → x.v.base.recv.length ≤ capRecv → capRecv < 2 ^ 62 →
      FitsEvents M lim st (mergeFieldQFitsEvents capRecv x.v.base.recv.length x.fld) →
      ∃ FieldPre FieldPost Rest : SepProp,
        (prostSSGQAtCap A.repAlloc x.ss capRecv x.v ⊢ FieldPre ∗ Rest) ∧
        (FieldPost ∗ Rest ⊢
          prostSSGQAtCap A.repAlloc x.ss (nextCapRecv capRecv x.v.base.recv.length x.fld)
            (x.v.apply x.fld)) ∧
        SepWPp (lsProg_15 H) (s0.readReg64 .lr) s0
          (FieldPre ∗ (x.bufRef ↦₆₄ x.slot) ∗
            sliceCursorAt x.slot x.ptr (x.fld.payload ++ x.tail) ∗
            A.pool lim st s0 ∗ stackAt s0.sp mergeFieldStackX)
          (fun sf Pf =>
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace ∧
            sf.readReg64 .x0 = 0#64 ∧
            (Pf ⊢ FieldPost ∗ (x.bufRef ↦₆₄ x.slot) ∗
              sliceCursorAfter x.slot x.ptr (x.fld.payload ++ x.tail) x.tail ∗
              A.pool lim (M.stepEvents (mergeFieldQEvents capRecv x.v.base.recv.length x.fld) st) sf ∗
              stackAt s0.sp mergeFieldStackX))
          NoPanicPost) :
    subroutine_ok (lsProg_15 H) (blkPl_15).base (mergeFieldQBudgetSpecW M A lim P) := by
  refine subroutine_ok_outcome_intro fun ⟨x, capRecv, st⟩ R s0 hpc hrun hpre hal =>
    reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨⟨hcl, hro⟩, hpre_raw⟩ := extract_withLsCodeRoLoaded hpre
  rw [mergeFieldQBudgetRawSpecW, sepConj_assoc, satisfies_pure_sepConj] at hpre_raw
  obtain ⟨⟨hx0, hx1, hx2, hx3, hx4, hP, hOk, hFr, hFrB, hlen, hpow, hle, hcap62, hfit⟩, hm⟩ :=
    hpre_raw
  obtain ⟨FieldPre, FieldPost, Rest, hsplit_pre, hsplit_post, hwp⟩ :=
    h x capRecv st s0 hpc hrun hal hcl hro hx0 hx1 hx2 hx3 hx4 hP hOk hFr hFrB hlen
      hpow hle hcap62 hfit
  have hm1 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left hsplit_pre)) hm
  have hm2 : s0.mem ⊨
      (FieldPre ∗ (x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAt x.slot x.ptr (x.fld.payload ++ x.tail) ∗
        A.pool lim st s0 ∗ stackAt s0.sp mergeFieldStackX) ∗ (Rest ∗ R) := by
    refine Satisfies.mono (Entails.of_eq ?_) hm1
    sep_ac_rfl
  obtain ⟨sf, hsteps, hex⟩ := hwp (Rest ∗ R) hm2 hL
  refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
  rcases hex with ⟨hpc_f, hrun_f, Pf, hmf, hsp_f, hcs_f, htr_f, hx0_f, hent_f⟩ |
      ⟨_, _, _, hpan⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨⟨hpc_f, hsp_f, hrun_f⟩, ⟨hsp_f, hcs_f⟩, ?_⟩
    have hmf1 := Satisfies.mono (sepConj_mono_left hent_f) hmf
    have hmf2 : sf.mem ⊨
        ((FieldPost ∗ Rest) ∗ (x.bufRef ↦₆₄ x.slot) ∗
          sliceCursorAfter x.slot x.ptr (x.fld.payload ++ x.tail) x.tail ∗
          A.pool lim (M.stepEvents (mergeFieldQEvents capRecv x.v.base.recv.length x.fld) st) sf ∗
          stackAt s0.sp mergeFieldStackX) ∗ R := by
      refine Satisfies.mono (Entails.of_eq ?_) hmf1
      sep_ac_rfl
    have hmf3 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left hsplit_post)) hmf2
    dsimp only [mergeFieldQBudgetSpecW, withLsCodeRoLoaded, mergeFieldQBudgetRawSpecW]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨htr_f, hx0_f⟩, by simpa only [sepConj_assoc] using hmf3⟩
  · exact hpan.elim
  · exact (not_satisfies_false_sepConj hoom).elim

/-! ## 3. Group A (`u32` Varint Tags `1, 5, 10, 11`) & Group B (`Vec<u8>` Tags `2, 3, 4, 13, 15`) -/

private theorem stackAt_sub_int32_split (sp : BitVec 64) :
    stackAt sp mergeFieldSubStackX =
      memRegion (sp - BitVec.ofNat 64 (int32MergeStackW + 7792)) 7792 ∗ stackAt sp int32MergeStackW :=
  ProofLib.stackAt_split_bottom sp int32MergeStackW 7792 (by decide)

private theorem stackAt_sub_bytes_split (sp : BitVec 64) :
    stackAt sp mergeFieldSubStackX =
      memRegion (sp - BitVec.ofNat 64 (bytesMergeStackW + 7648)) 7648 ∗ stackAt sp bytesMergeStackW :=
  ProofLib.stackAt_split_bottom sp bytesMergeStackW 7648 (by decide)

private theorem step_epilogue_1880_vm [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (retOff : BitVec 64)
    (hret : retOff = 80#64 ∨ retOff = 180#64 ∨ retOff = 936#64 ∨ retOff = 892#64 ∨
      retOff = 600#64 ∨ retOff = 556#64 ∨ retOff = 460#64 ∨ retOff = 124#64 ∨ retOff = 224#64)
    (bufRef slot w56 : BitVec 64) (RestOut : SepProp) (st' : M.σ)
    {s0 sm : State}
    (hpcm : sm.pc = (blkPl_15).base + retOff) (hrunm : sm.status = .Running)
    (hspm : sm.sp = s0.sp - 240#64) (halign : s0.sp &&& 15#64 = 0#64)
    (htrm : sm.trace = s0.trace) (hx0m : sm.readReg64 .x0 = 0#64)
    (hx26m : sm.readReg64 .x26 = s0.readReg64 .x26)
    (hx27m : sm.readReg64 .x27 = s0.readReg64 .x27)
    (hx28m : sm.readReg64 .x28 = s0.readReg64 .x28)
    (hvregsm : calleeSavedVRegs sm = calleeSavedVRegs s0) :
    SepWPp (lsProg_15 H) (s0.readReg64 .lr) sm
      (RestOut ∗ (bufRef ↦₆₄ slot) ∗ A.pool lim st' sm ∗
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
        ((s0.sp - 56#64) ↦₆₄ w56) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
        memRegion (s0.sp - 240#64) 160 ∗
        stackAt (s0.sp - 240#64) mergeFieldSubStackX)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace ∧
        sf.readReg64 .x0 = 0#64 ∧
        (Pf ⊢ RestOut ∗ (bufRef ↦₆₄ slot) ∗ A.pool lim st' sf ∗ stackAt s0.sp mergeFieldStackX))
      NoPanicPost := by
  have hsp240 := sp_sub_240_aligned_identityRootKeys halign
  apply SepWPp.of_sepWP_ret
  apply sepWP_ret_vmPreserved
  rcases hret with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    by_vm_steps_withSvc (
      wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, hrunm])
        ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
    intro hvm_end
    rw [← A.pool_transport lim st' sm _ hvm_end]
    apply SepWP.done (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrunm])
    refine ⟨by simp only [wp_norm, arm64_norm, hspm],
      by simp only [CalleeSavedPreserved, calleeSavedVRegs, wp_norm, arm64_norm,
        hx26m, hx27m, hx28m, hvregsm, and_self],
      by simp only [wp_norm, arm64_norm, htrm],
      by simp only [wp_norm, arm64_norm, hx0m], ?_⟩
    have hstk := stackAt_mergeField_fold_mf14W s0.sp
      (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
      (s0.readReg64 (Reg.gpr 25#5)) w56
      (s0.readReg64 (Reg.gpr 24#5)) (s0.readReg64 (Reg.gpr 23#5))
      (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
      (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5))
    refine Entails.trans (Entails.of_eq ?_)
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hstk)))
    sep_ac_rfl

set_option maxHeartbeats 1600000 in
private theorem step_u32_field_mfb [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (tag : Nat) (fieldOff retOff roAddr : BitVec 64) (roByte : BitVec 8)
    (htag : (tag = 1 ∧ fieldOff = 0x148#64 ∧ retOff = 80#64 ∧
        roAddr = lsmpl.ρ mergeFieldRodataSym ∧ roByte = 0#8) ∨
      (tag = 5 ∧ fieldOff = 0x14c#64 ∧ retOff = 180#64 ∧
        roAddr = lsmpl.ρ mergeFieldRodataSym + 4#64 ∧ roByte = 25#8) ∨
      (tag = 10 ∧ fieldOff = 0x150#64 ∧ retOff = 936#64 ∧
        roAddr = lsmpl.ρ mergeFieldRodataSym + 9#64 ∧ roByte = 214#8) ∨
      (tag = 11 ∧ fieldOff = 0x154#64 ∧ retOff = 892#64 ∧
        roAddr = lsmpl.ρ mergeFieldRodataSym + 10#64 ∧ roByte = 203#8))
    (ss bufRef slot ptr : BitVec 64) (oldVal val : BitVec 32)
    (payload tail : List (BitVec 8)) (st : M.σ) {s0 : State}
    (hpc : s0.pc = (blkPl_15).base) (hrun : s0.status = .Running)
    (hsp_align : s0.spAligned = true)
    (hcl : LibsignalCodeLoaded lsmpl s0.mem) (hro : LibsignalRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = ss)
    (hx1 : (s0.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 tag)
    (hx2 : (s0.readReg64 .x2).setWidth 8 = 0#8)
    (hx3 : s0.readReg64 .x3 = bufRef)
    (hlen : (payload ++ tail).length < 2 ^ 62)
    (hmerge : mergeUint32 .varint (payload ++ tail) = some (val, tail)) :
    SepWPp (lsProg_15 H) (s0.readReg64 .lr) s0
      (((ss + fieldOff) ↦₃₂ oldVal) ∗ (bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr (payload ++ tail) ∗
        A.pool lim st s0 ∗ stackAt s0.sp mergeFieldStackX)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace ∧
        sf.readReg64 .x0 = 0#64 ∧
        (Pf ⊢ ((ss + fieldOff) ↦₃₂ val) ∗ (bufRef ↦₆₄ slot) ∗
          sliceCursorAfter slot ptr (payload ++ tail) tail ∗
          A.pool lim st sf ∗ stackAt s0.sp mergeFieldStackX))
      NoPanicPost := by
  have halign : s0.sp &&& 15#64 = 0#64 := by simpa [State.spAligned] using hsp_align
  have hsp240 := sp_sub_240_aligned_identityRootKeys halign
  have hcallI := int32_merge_some_placed_ok_cl (callerProg := lsProg_15 H)
    (errStack := decodeErrorHookStackW) (by decide)
  have hcell4 : ((ss + fieldOff) ↦₃₂ oldVal) ⊢ memRegion (ss + fieldOff) 4 := by
    rw [ProofLib.memRegion_four (ss + fieldOff)]
    exact Entails.sepExists_right oldVal (Entails.refl _)
  refine SepWPp.weaken_pre (sepConj_mono_left hcell4) ?_
  conv =>
    arg 4
    rw [stackAt_mergeFieldX_unfold_x9pW s0.sp]
    simp only [sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun w80 => SepWPp.exists_elim fun w72 =>
    SepWPp.exists_elim fun w64 => SepWPp.exists_elim fun w56 =>
    SepWPp.exists_elim fun w48 => SepWPp.exists_elim fun w40 =>
    SepWPp.exists_elim fun w32 => SepWPp.exists_elim fun w24 =>
    SepWPp.exists_elim fun w16 => SepWPp.exists_elim fun w8 => ?_
  rcases htag with ⟨rfl, hfoff, hroff, hroA, hroB⟩ | ⟨rfl, hfoff, hroff, hroA, hroB⟩ |
      ⟨rfl, hfoff, hroff, hroA, hroB⟩ | ⟨rfl, hfoff, hroff, hroA, hroB⟩
  all_goals
    simp only [arm64_norm] at hx0 hx1 hx2 hx3
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
    apply sepWPp_seq_lsclro_vm hcl1 hro1 (mid := lsmpl.base 8)
    refine sepWP_intro_ro8_mfb roAddr roByte
      (fun hm => by rw [hroA, hroB]; exact lsro8_intro hro1 (by lsro_addr) (by decide +kernel) hm) ?_
    rw [hroA, hroB]
    by_vm_steps_withSvc (
      wp_steps
      apply sepWP_drop_left_mfb
      refine SepWP.done (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, hrun])
        ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
    intro hvm2 hcl2 hro2
    rw [← A.pool_transport lim st _ _ hvm2]
    rw [stackAt_sub_int32_split (s0.sp - 240#64)]
    refine sepWPp_call_lscl_15
      (x := (⟨.varint, ss + fieldOff, bufRef, slot, ptr, payload ++ tail⟩, val, tail))
      hcallI hcl2 hro2
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun])
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp240, beq_self_eq_true])
      (by simp only [wp_norm, arm64_norm]; rfl)
      (by
        dsimp only [ProstVarintVm.int32MergeSomeSpecGen]
        apply entails_pure_sep_frame
        · refine ⟨?_, ?_, ?_, by omega, hmerge⟩
          · simp only [wp_norm, arm64_norm, hx2]
          · rw [hfoff]; simp only [wp_norm, arm64_norm, hx0]
          · simp only [wp_norm, arm64_norm, hx3]
        · apply entails_rw_stack_4 (sp2 := s0.sp - 240#64) (w2 := int32MergeStackW)
          · simp only [wp_norm, arm64_norm]
          · rfl
          · sep_frame)
      ?_
    intro sm hpcm hrunm hspm hcsm _hclm _hrom
    dsimp only [ProstVarintVm.int32MergeSomeSpecGen]
    refine sepWPp_pure_left_and fun ⟨hx0m, htrm, hvmm⟩ => ?_
    rw [← A.pool_transport lim st _ sm hvmm]
    have hpcm' : sm.pc = (blkPl_15).base + retOff := by
      rw [hroff]; simpa only [wp_norm, arm64_norm] using hpcm
    have hspm' : sm.sp = s0.sp - 240#64 := by simpa only [wp_norm, arm64_norm] using hspm
    have htrm' : sm.trace = s0.trace := by simpa only [wp_norm, arm64_norm] using htrm
    have hx26m : sm.readReg64 .x26 = s0.readReg64 .x26 := by
      simpa only [wp_norm, arm64_norm] using hcsm.2.2.2.2.2.2.2.1
    have hx27m : sm.readReg64 .x27 = s0.readReg64 .x27 := by
      simpa only [wp_norm, arm64_norm] using hcsm.2.2.2.2.2.2.2.2.1
    have hx28m : sm.readReg64 .x28 = s0.readReg64 .x28 := by
      simpa only [wp_norm, arm64_norm] using hcsm.2.2.2.2.2.2.2.2.2.1
    have hvregsm : calleeSavedVRegs sm = calleeSavedVRegs s0 := by
      simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hcsm.2.2.2.2.2.2.2.2.2.2.2
    have hstk_eq : 0x50 + (0x50 + decodeErrorHookStackW) = int32MergeStackW := rfl
    rw [hstk_eq]
    refine SepWPp.weaken_pre (Entails.of_eq ?_)
      (sepWPp_mono_post
        (step_epilogue_1880_vm (A := A) (lim := lim) retOff (by simp [hroff]) bufRef slot w56
          (((ss + fieldOff) ↦₃₂ val) ∗ sliceCursorAfter slot ptr (payload ++ tail) tail) st
          hpcm' hrunm hspm' halign htrm' hx0m hx26m hx27m hx28m hvregsm)
        ?_)
    · rw [show stackAt _ int32MergeStackW = stackAt (s0.sp - 240#64) int32MergeStackW by
            simp only [wp_norm, arm64_norm],
          stackAt_sub_int32_split (s0.sp - 240#64)]
      sep_ac_rfl
    · intro sf Pf ⟨hsp_f, hcs_f, htr_f, hx0_f, hent⟩
      exact ⟨hsp_f, hcs_f, htr_f, hx0_f,
        Entails.trans hent (Entails.of_eq (by sep_ac_rfl))⟩

theorem mergeFieldBasic_u32_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks} :
    subroutine_ok (lsProg_15 H) (blkPl_15).base
      (mergeFieldQBudgetSpecW M A lim
        (fun fl => fl.tag = 1 ∨ fl.tag = 5 ∨ fl.tag = 10 ∨ fl.tag = 11)) := by
  apply subroutine_ok_of_field_sepWPp
  intro x capRecv st s0 hpc hrun hal hcl hro hx0 hx1 hx2 hx3 _hx4 hP _hOk _hFr _hFrB hlen
    _hpow _hle _hcap62 _hfit
  generalize x.fld = fld at hx1 hx2 hP hlen ⊢
  cases fld with
  | base f =>
    cases f with
    | version val =>
      have hm : mergeUint32 .varint ((GenFieldQ.base (.version val)).payload ++ x.tail) =
          some (val, x.tail) := by
        change mergeUint32 .varint (encodeVarint (val.setWidth 64) ++ x.tail) = some (val, x.tail)
        rw [mergeUint32_encode_64_x9p, setWidth32_setWidth64_x9p]
      refine ⟨(x.ss + 0x148#64) ↦₃₂ x.v.base.version, (x.ss + 0x148#64) ↦₃₂ val,
        prostSSGQNonScalarCap A.repAlloc x.ss capRecv x.v ∗
          ((x.ss + 0x14c#64) ↦₃₂ x.v.base.prevCounter) ∗
          ((x.ss + 0x150#64) ↦₃₂ x.v.ext.remReg) ∗
          ((x.ss + 0x154#64) ↦₃₂ x.v.ext.locReg), ?_, ?_, ?_⟩
      · unfold prostSSGQAtCap prostSSGQNonScalarCap
        rw [kyberAtCap_eq_kyberAt14Cap_sep]
        exact Entails.of_eq (by sep_ac_rfl)
      · unfold prostSSGQAtCap prostSSGQNonScalarCap nextCapRecv SSGQ.apply SSG.apply
        dsimp only
        rw [kyberAtCap_eq_kyberAt14Cap_sep, pendingAt9PCap_congr A.repAlloc x.ss rfl rfl rfl]
        exact Entails.of_eq (by sep_ac_rfl)
      · have hev : M.stepEvents (mergeFieldQEvents capRecv x.v.base.recv.length
            (.base (.version val))) st = st := by
          change M.stepEvents (bytesMergeEvents 0 0) st = st
          exact stepEvents_bytesMergeFresh_zero M st
        rw [hev]
        exact step_u32_field_mfb 1 0x148#64 80#64 (lsmpl.ρ mergeFieldRodataSym) 0#8
          (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩)
          x.ss x.bufRef x.slot x.ptr x.v.base.version val _ x.tail st
          hpc hrun hal hcl hro hx0 hx1 hx2 hx3 hlen hm
    | prevCounter val =>
      have hm : mergeUint32 .varint ((GenFieldQ.base (.prevCounter val)).payload ++ x.tail) =
          some (val, x.tail) := by
        change mergeUint32 .varint (encodeVarint (val.setWidth 64) ++ x.tail) = some (val, x.tail)
        rw [mergeUint32_encode_64_x9p, setWidth32_setWidth64_x9p]
      refine ⟨(x.ss + 0x14c#64) ↦₃₂ x.v.base.prevCounter, (x.ss + 0x14c#64) ↦₃₂ val,
        prostSSGQNonScalarCap A.repAlloc x.ss capRecv x.v ∗
          ((x.ss + 0x148#64) ↦₃₂ x.v.base.version) ∗
          ((x.ss + 0x150#64) ↦₃₂ x.v.ext.remReg) ∗
          ((x.ss + 0x154#64) ↦₃₂ x.v.ext.locReg), ?_, ?_, ?_⟩
      · unfold prostSSGQAtCap prostSSGQNonScalarCap
        rw [kyberAtCap_eq_kyberAt14Cap_sep]
        exact Entails.of_eq (by sep_ac_rfl)
      · unfold prostSSGQAtCap prostSSGQNonScalarCap nextCapRecv SSGQ.apply SSG.apply
        dsimp only
        rw [kyberAtCap_eq_kyberAt14Cap_sep, pendingAt9PCap_congr A.repAlloc x.ss rfl rfl rfl]
        exact Entails.of_eq (by sep_ac_rfl)
      · have hev : M.stepEvents (mergeFieldQEvents capRecv x.v.base.recv.length
            (.base (.prevCounter val))) st = st := by
          change M.stepEvents (bytesMergeEvents 0 0) st = st
          exact stepEvents_bytesMergeFresh_zero M st
        rw [hev]
        exact step_u32_field_mfb 5 0x14c#64 180#64 (lsmpl.ρ mergeFieldRodataSym + 4#64) 25#8
          (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩))
          x.ss x.bufRef x.slot x.ptr x.v.base.prevCounter val _ x.tail st
          hpc hrun hal hcl hro hx0 hx1 hx2 hx3 hlen hm
    | _ => simp [GenFieldQ.tag, GenField.tag] at hP
  | remReg val =>
    have hm : mergeUint32 .varint ((GenFieldQ.remReg val).payload ++ x.tail) =
        some (val, x.tail) := by
      change mergeUint32 .varint (encodeVarint (val.setWidth 64) ++ x.tail) = some (val, x.tail)
      rw [mergeUint32_encode_64_x9p, setWidth32_setWidth64_x9p]
    refine ⟨(x.ss + 0x150#64) ↦₃₂ x.v.ext.remReg, (x.ss + 0x150#64) ↦₃₂ val,
      prostSSGQNonScalarCap A.repAlloc x.ss capRecv x.v ∗
        ((x.ss + 0x148#64) ↦₃₂ x.v.base.version) ∗
        ((x.ss + 0x14c#64) ↦₃₂ x.v.base.prevCounter) ∗
        ((x.ss + 0x154#64) ↦₃₂ x.v.ext.locReg), ?_, ?_, ?_⟩
    · unfold prostSSGQAtCap prostSSGQNonScalarCap
      rw [kyberAtCap_eq_kyberAt14Cap_sep]
      exact Entails.of_eq (by sep_ac_rfl)
    · unfold prostSSGQAtCap prostSSGQNonScalarCap nextCapRecv SSGQ.apply
      dsimp only
      rw [kyberAtCap_eq_kyberAt14Cap_sep, pendingAt9PCap_congr A.repAlloc x.ss rfl rfl rfl]
      exact Entails.of_eq (by sep_ac_rfl)
    · have hev : M.stepEvents (mergeFieldQEvents capRecv x.v.base.recv.length
          (.remReg val)) st = st := by
        change M.stepEvents (bytesMergeEvents 0 0) st = st
        exact stepEvents_bytesMergeFresh_zero M st
      rw [hev]
      exact step_u32_field_mfb 10 0x150#64 936#64 (lsmpl.ρ mergeFieldRodataSym + 9#64) 214#8
        (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩)))
        x.ss x.bufRef x.slot x.ptr x.v.ext.remReg val _ x.tail st
        hpc hrun hal hcl hro hx0 hx1 hx2 hx3 hlen hm
  | locReg val =>
    have hm : mergeUint32 .varint ((GenFieldQ.locReg val).payload ++ x.tail) =
        some (val, x.tail) := by
      change mergeUint32 .varint (encodeVarint (val.setWidth 64) ++ x.tail) = some (val, x.tail)
      rw [mergeUint32_encode_64_x9p, setWidth32_setWidth64_x9p]
    refine ⟨(x.ss + 0x154#64) ↦₃₂ x.v.ext.locReg, (x.ss + 0x154#64) ↦₃₂ val,
      prostSSGQNonScalarCap A.repAlloc x.ss capRecv x.v ∗
        ((x.ss + 0x148#64) ↦₃₂ x.v.base.version) ∗
        ((x.ss + 0x14c#64) ↦₃₂ x.v.base.prevCounter) ∗
        ((x.ss + 0x150#64) ↦₃₂ x.v.ext.remReg), ?_, ?_, ?_⟩
    · unfold prostSSGQAtCap prostSSGQNonScalarCap
      rw [kyberAtCap_eq_kyberAt14Cap_sep]
      exact Entails.of_eq (by sep_ac_rfl)
    · unfold prostSSGQAtCap prostSSGQNonScalarCap nextCapRecv SSGQ.apply
      dsimp only
      rw [kyberAtCap_eq_kyberAt14Cap_sep, pendingAt9PCap_congr A.repAlloc x.ss rfl rfl rfl]
      exact Entails.of_eq (by sep_ac_rfl)
    · have hev : M.stepEvents (mergeFieldQEvents capRecv x.v.base.recv.length
          (.locReg val)) st = st := by
        change M.stepEvents (bytesMergeEvents 0 0) st = st
        exact stepEvents_bytesMergeFresh_zero M st
      rw [hev]
      exact step_u32_field_mfb 11 0x154#64 892#64 (lsmpl.ρ mergeFieldRodataSym + 10#64) 203#8
        (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl, rfl⟩)))
        x.ss x.bufRef x.slot x.ptr x.v.ext.locReg val _ x.tail st
        hpc hrun hal hcl hro hx0 hx1 hx2 hx3 hlen hm
  | _ => simp [GenFieldQ.tag] at hP

set_option maxHeartbeats 1600000 in
private theorem step_bytes_field_mfb [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H)
    (tag : Nat) (fieldOff retOff roAddr : BitVec 64) (roByte : BitVec 8)
    (htag : (tag = 2 ∧ fieldOff = 0#64 ∧ retOff = 600#64 ∧
        roAddr = lsmpl.ρ mergeFieldRodataSym + 1#64 ∧ roByte = 0x82#8) ∨
      (tag = 3 ∧ fieldOff = 0x18#64 ∧ retOff = 556#64 ∧
        roAddr = lsmpl.ρ mergeFieldRodataSym + 2#64 ∧ roByte = 0x77#8) ∨
      (tag = 4 ∧ fieldOff = 0x30#64 ∧ retOff = 460#64 ∧
        roAddr = lsmpl.ρ mergeFieldRodataSym + 3#64 ∧ roByte = 0x5f#8) ∨
      (tag = 13 ∧ fieldOff = 0x60#64 ∧ retOff = 124#64 ∧
        roAddr = lsmpl.ρ mergeFieldRodataSym + 12#64 ∧ roByte = 0x0b#8) ∨
      (tag = 15 ∧ fieldOff = 0x78#64 ∧ retOff = 224#64 ∧
        roAddr = lsmpl.ρ mergeFieldRodataSym + 14#64 ∧ roByte = 0x24#8))
    (ss bufRef slot ptr : BitVec 64) (bytes payload tail : List (BitVec 8))
    (st : M.σ) {s0 : State}
    (hpc : s0.pc = (blkPl_15).base) (hrun : s0.status = .Running)
    (hsp_align : s0.spAligned = true)
    (hcl : LibsignalCodeLoaded lsmpl s0.mem) (hro : LibsignalRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = ss)
    (hx1 : (s0.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 tag)
    (hx2 : (s0.readReg64 .x2).setWidth 8 = 2#8)
    (hx3 : s0.readReg64 .x3 = bufRef)
    (hlen : (payload ++ tail).length < 2 ^ 62)
    (hmerge : mergeBytes .lengthDelimited (payload ++ tail) = some (bytes, tail))
    (hfit : FitsEvents M lim st (bytesMergeAllocEvents 0 bytes.length)) :
    SepWPp (lsProg_15 H) (s0.readReg64 .lr) s0
      (vecU8FreshCap A.repAlloc (ss + fieldOff) [] ∗ (bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr (payload ++ tail) ∗
        A.pool lim st s0 ∗ stackAt s0.sp mergeFieldStackX)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace ∧
        sf.readReg64 .x0 = 0#64 ∧
        (Pf ⊢ vecU8FreshCap A.repAlloc (ss + fieldOff) bytes ∗ (bufRef ↦₆₄ slot) ∗
          sliceCursorAfter slot ptr (payload ++ tail) tail ∗
          A.pool lim (M.stepEvents (bytesMergeEvents 0 bytes.length) st) sf ∗
          stackAt s0.sp mergeFieldStackX))
      NoPanicPost := by
  have halign : s0.sp &&& 15#64 = 0#64 := by simpa [State.spAligned] using hsp_align
  have hsp240 := sp_sub_240_aligned_identityRootKeys halign
  have hcallB := bytes_merge_fresh_budget_placed_okW_cl (callerProg := lsProg_15 H) hA
  unfold vecU8FreshCap
  rw [List.length_nil, bytesMergeOutCap_zero_zero]
  refine sepWPp_exists_left fun ptr0 => ?_
  conv =>
    arg 4
    rw [stackAt_mergeFieldX_unfold_x9pW s0.sp]
    simp only [sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun w80 => SepWPp.exists_elim fun w72 =>
    SepWPp.exists_elim fun w64 => SepWPp.exists_elim fun w56 =>
    SepWPp.exists_elim fun w48 => SepWPp.exists_elim fun w40 =>
    SepWPp.exists_elim fun w32 => SepWPp.exists_elim fun w24 =>
    SepWPp.exists_elim fun w16 => SepWPp.exists_elim fun w8 => ?_
  rcases htag with ⟨rfl, hfoff, hroff, hroA, hroB⟩ | ⟨rfl, hfoff, hroff, hroA, hroB⟩ |
      ⟨rfl, hfoff, hroff, hroA, hroB⟩ | ⟨rfl, hfoff, hroff, hroA, hroB⟩ |
      ⟨rfl, hfoff, hroff, hroA, hroB⟩
  all_goals
    simp only [arm64_norm] at hx0 hx1 hx2 hx3
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
    apply sepWPp_seq_lsclro_vm hcl1 hro1 (mid := lsmpl.base 7)
    refine sepWP_intro_ro8_mfb roAddr roByte
      (fun hm => by rw [hroA, hroB]; exact lsro8_intro hro1 (by lsro_addr) (by decide +kernel) hm) ?_
    rw [hroA, hroB]
    by_vm_steps_withSvc (
      wp_steps
      apply sepWP_drop_left_mfb
      refine SepWP.done (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, hrun])
        ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
    intro hvm2 hcl2 hro2
    rw [← A.pool_transport lim st _ _ hvm2]
    rw [stackAt_sub_bytes_split (s0.sp - 240#64)]
    refine sepWPp_call_lscro_15
      (x := (⟨.lengthDelimited, ss + fieldOff, 0#64, ptr0, [], bufRef, slot, ptr,
        payload ++ tail⟩, bytes, tail, st))
      hcallB hcl2 hro2
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun])
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp240, beq_self_eq_true])
      (by simp only [wp_norm, arm64_norm]; rfl)
      (by
        dsimp only [bytesMergeFreshBudgetSpecW]
        apply entails_pure_sep_frame
        · refine ⟨?_, ?_, ?_, by omega, rfl, rfl, hmerge, hfit⟩
          · simp only [wp_norm, arm64_norm, hx2]
          · rw [hfoff]; simp only [wp_norm, arm64_norm, hx0, BitVec.add_zero]
          · simp only [wp_norm, arm64_norm, hx3]
        · apply entails_rw_stack_5 (sp2 := s0.sp - 240#64) (w2 := bytesMergeStackW)
          · simp only [wp_norm, arm64_norm]
          · rfl
          · sep_frame)
      ?_
    intro sm hpcm hrunm hspm hcsm _hclm _hrom
    dsimp only [bytesMergeFreshBudgetSpecW]
    refine sepWPp_pure_left_and fun ⟨hx0m, htrm⟩ => ?_
    have hpcm' : sm.pc = (blkPl_15).base + retOff := by
      rw [hroff]; simpa only [wp_norm, arm64_norm] using hpcm
    have hspm' : sm.sp = s0.sp - 240#64 := by simpa only [wp_norm, arm64_norm] using hspm
    have htrm' : sm.trace = s0.trace := by simpa only [wp_norm, arm64_norm] using htrm
    have hx26m : sm.readReg64 .x26 = s0.readReg64 .x26 := by
      simpa only [wp_norm, arm64_norm] using hcsm.2.2.2.2.2.2.2.1
    have hx27m : sm.readReg64 .x27 = s0.readReg64 .x27 := by
      simpa only [wp_norm, arm64_norm] using hcsm.2.2.2.2.2.2.2.2.1
    have hx28m : sm.readReg64 .x28 = s0.readReg64 .x28 := by
      simpa only [wp_norm, arm64_norm] using hcsm.2.2.2.2.2.2.2.2.2.1
    have hvregsm : calleeSavedVRegs sm = calleeSavedVRegs s0 := by
      simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hcsm.2.2.2.2.2.2.2.2.2.2.2
    refine SepWPp.weaken_pre (Entails.of_eq ?_)
      (sepWPp_mono_post
        (step_epilogue_1880_vm (A := A) (lim := lim) retOff (by simp [hroff]) bufRef slot w56
          ((∃∗ ptr' : BitVec 64,
              vecU8At A.repAlloc (ss + fieldOff) (bytesMergeOutCap 0#64 bytes.length) ptr' bytes) ∗
            sliceCursorAfter slot ptr (payload ++ tail) tail)
          (M.stepEvents (bytesMergeEvents 0 bytes.length) st)
          hpcm' hrunm hspm' halign htrm' hx0m hx26m hx27m hx28m hvregsm)
        ?_)
    · rw [show stackAt _ bytesMergeStackW = stackAt (s0.sp - 240#64) bytesMergeStackW by
            simp only [wp_norm, arm64_norm],
          stackAt_sub_bytes_split (s0.sp - 240#64)]
      sep_ac_rfl
    · intro sf Pf ⟨hsp_f, hcs_f, htr_f, hx0_f, hent⟩
      exact ⟨hsp_f, hcs_f, htr_f, hx0_f,
        Entails.trans hent (Entails.of_eq (by sep_ac_rfl))⟩

theorem mergeFieldBasic_bytes_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H) :
    subroutine_ok (lsProg_15 H) (blkPl_15).base
      (mergeFieldQBudgetSpecW M A lim
        (fun fl => fl.tag = 2 ∨ fl.tag = 3 ∨ fl.tag = 4 ∨ fl.tag = 13 ∨ fl.tag = 15)) := by
  apply subroutine_ok_of_field_sepWPp
  intro x capRecv st s0 hpc hrun hal hcl hro hx0 hx1 hx2 hx3 _hx4 hP hOk hFr hFrB hlen
    _hpow _hle _hcap62 hfit
  generalize x.fld = fld at hx1 hx2 hP hOk hFr hFrB hlen hfit ⊢
  cases fld with
  | base f =>
    cases f with
    | lik b =>
      have hb : b.length = 33 := hOk
      have hempty : x.v.base.lik = [] := hFrB
      have hm : mergeBytes .lengthDelimited ((GenFieldQ.base (.lik b)).payload ++ x.tail) =
          some (b, x.tail) := by
        change mergeBytes .lengthDelimited
          ((encodeVarint (BitVec.ofNat 64 b.length) ++ b) ++ x.tail) = some (b, x.tail)
        rw [List.append_assoc]
        exact mergeBytes_encode b x.tail (by omega)
      refine ⟨vecU8FreshCap A.repAlloc (x.ss + 0#64) [],
        vecU8FreshCap A.repAlloc (x.ss + 0#64) b,
        prostSSGQRest_lik A.repAlloc x.ss capRecv x.v, ?_, ?_, ?_⟩
      · unfold prostSSGQAtCap prostSSGQRest_lik prostSSGQScalars
        rw [hempty, BitVec.add_zero]
        exact Entails.of_eq (by sep_ac_rfl)
      · unfold prostSSGQAtCap prostSSGQRest_lik prostSSGQScalars nextCapRecv SSGQ.apply SSG.apply
        dsimp only
        rw [BitVec.add_zero, pendingAt9PCap_congr A.repAlloc x.ss rfl rfl rfl]
        exact Entails.of_eq (by sep_ac_rfl)
      · exact step_bytes_field_mfb hA 2 0#64 600#64
          (lsmpl.ρ mergeFieldRodataSym + 1#64) 0x82#8 (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩)
          x.ss x.bufRef x.slot x.ptr b _ x.tail st
          hpc hrun hal hcl hro hx0 hx1 hx2 hx3 hlen hm hfit
    | rik b =>
      have hb : b.length = 33 := hOk
      have hempty : x.v.base.rik = [] := hFrB
      have hm : mergeBytes .lengthDelimited ((GenFieldQ.base (.rik b)).payload ++ x.tail) =
          some (b, x.tail) := by
        change mergeBytes .lengthDelimited
          ((encodeVarint (BitVec.ofNat 64 b.length) ++ b) ++ x.tail) = some (b, x.tail)
        rw [List.append_assoc]
        exact mergeBytes_encode b x.tail (by omega)
      refine ⟨vecU8FreshCap A.repAlloc (x.ss + 0x18#64) [],
        vecU8FreshCap A.repAlloc (x.ss + 0x18#64) b,
        prostSSGQRest_rik A.repAlloc x.ss capRecv x.v, ?_, ?_, ?_⟩
      · unfold prostSSGQAtCap prostSSGQRest_rik prostSSGQScalars
        rw [hempty]
        exact Entails.of_eq (by sep_ac_rfl)
      · unfold prostSSGQAtCap prostSSGQRest_rik prostSSGQScalars nextCapRecv SSGQ.apply SSG.apply
        dsimp only
        rw [pendingAt9PCap_congr A.repAlloc x.ss rfl rfl rfl]
        exact Entails.of_eq (by sep_ac_rfl)
      · exact step_bytes_field_mfb hA 3 0x18#64 556#64
          (lsmpl.ρ mergeFieldRodataSym + 2#64) 0x77#8
          (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩))
          x.ss x.bufRef x.slot x.ptr b _ x.tail st
          hpc hrun hal hcl hro hx0 hx1 hx2 hx3 hlen hm hfit
    | root b =>
      have hb : b.length = 32 := hOk
      have hempty : x.v.base.root = [] := hFrB
      have hm : mergeBytes .lengthDelimited ((GenFieldQ.base (.root b)).payload ++ x.tail) =
          some (b, x.tail) := by
        change mergeBytes .lengthDelimited
          ((encodeVarint (BitVec.ofNat 64 b.length) ++ b) ++ x.tail) = some (b, x.tail)
        rw [List.append_assoc]
        exact mergeBytes_encode b x.tail (by omega)
      refine ⟨vecU8FreshCap A.repAlloc (x.ss + 0x30#64) [],
        vecU8FreshCap A.repAlloc (x.ss + 0x30#64) b,
        prostSSGQRest_root A.repAlloc x.ss capRecv x.v, ?_, ?_, ?_⟩
      · unfold prostSSGQAtCap prostSSGQRest_root prostSSGQScalars
        rw [hempty]
        exact Entails.of_eq (by sep_ac_rfl)
      · unfold prostSSGQAtCap prostSSGQRest_root prostSSGQScalars nextCapRecv SSGQ.apply SSG.apply
        dsimp only
        rw [pendingAt9PCap_congr A.repAlloc x.ss rfl rfl rfl]
        exact Entails.of_eq (by sep_ac_rfl)
      · exact step_bytes_field_mfb hA 4 0x30#64 460#64
          (lsmpl.ρ mergeFieldRodataSym + 3#64) 0x5f#8
          (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩)))
          x.ss x.bufRef x.slot x.ptr b _ x.tail st
          hpc hrun hal hcl hro hx0 hx1 hx2 hx3 hlen hm hfit
    | _ => simp [GenFieldQ.tag, GenField.tag] at hP
  | abk b =>
    have hb : b.length = 33 := hOk
    have hempty : x.v.ext.abk = [] := hFr.1
    have hm : mergeBytes .lengthDelimited ((GenFieldQ.abk b).payload ++ x.tail) =
        some (b, x.tail) := by
      change mergeBytes .lengthDelimited
        ((encodeVarint (BitVec.ofNat 64 b.length) ++ b) ++ x.tail) = some (b, x.tail)
      rw [List.append_assoc]
      exact mergeBytes_encode b x.tail (by omega)
    refine ⟨vecU8FreshCap A.repAlloc (x.ss + 0x60#64) [],
      vecU8FreshCap A.repAlloc (x.ss + 0x60#64) b,
      prostSSGQRest_abk A.repAlloc x.ss capRecv x.v, ?_, ?_, ?_⟩
    · unfold prostSSGQAtCap prostSSGQRest_abk prostSSGQScalars
      rw [hempty]
      exact Entails.of_eq (by sep_ac_rfl)
    · unfold prostSSGQAtCap prostSSGQRest_abk prostSSGQScalars nextCapRecv SSGQ.apply
      dsimp only
      rw [pendingAt9PCap_congr A.repAlloc x.ss rfl rfl rfl]
      exact Entails.of_eq (by sep_ac_rfl)
    · exact step_bytes_field_mfb hA 13 0x60#64 124#64
        (lsmpl.ρ mergeFieldRodataSym + 12#64) 0x0b#8
        (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩))))
        x.ss x.bufRef x.slot x.ptr b _ x.tail st
        hpc hrun hal hcl hro hx0 hx1 hx2 hx3 hlen hm hfit
  | pq b =>
    have hb : b.length < 2 ^ 32 := hOk
    have hempty : x.v.ext.pq = [] := hFr
    have hm : mergeBytes .lengthDelimited ((GenFieldQ.pq b).payload ++ x.tail) =
        some (b, x.tail) := by
      change mergeBytes .lengthDelimited
        ((encodeVarint (BitVec.ofNat 64 b.length) ++ b) ++ x.tail) = some (b, x.tail)
      rw [List.append_assoc]
      exact mergeBytes_encode b x.tail (by omega)
    refine ⟨vecU8FreshCap A.repAlloc (x.ss + 0x78#64) [],
      vecU8FreshCap A.repAlloc (x.ss + 0x78#64) b,
      prostSSGQRest_pq A.repAlloc x.ss capRecv x.v, ?_, ?_, ?_⟩
    · unfold prostSSGQAtCap prostSSGQRest_pq prostSSGQScalars
      rw [hempty]
      exact Entails.of_eq (by sep_ac_rfl)
    · unfold prostSSGQAtCap prostSSGQRest_pq prostSSGQScalars nextCapRecv SSGQ.apply
      dsimp only
      rw [pendingAt9PCap_congr A.repAlloc x.ss rfl rfl rfl]
      exact Entails.of_eq (by sep_ac_rfl)
    · exact step_bytes_field_mfb hA 15 0x78#64 224#64
        (lsmpl.ρ mergeFieldRodataSym + 14#64) 0x24#8
        (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl, rfl⟩))))
        x.ss x.bufRef x.slot x.ptr b _ x.tail st
        hpc hrun hal hcl hro hx0 hx1 hx2 hx3 hlen hm hfit
  | _ => simp [GenFieldQ.tag] at hP

/-! ## 4. Group C (`PendingPreKey` Tag `9`: `.base (.pending _)`, `.pendingId`, `.pendingSpk`) -/

private theorem emptyCells_eq_vecU8At_zero (A : RustAlloc) (addr : BitVec 64) :
    (addr ↦₆₄ 0#64) ∗ ((addr + 8#64) ↦₆₄ 1#64) ∗ ((addr + 16#64) ↦₆₄ 0#64) =
      vecU8At A addr 0#64 1#64 [] := by
  unfold vecU8At vecHeader
  have hite : (if (0#64 : BitVec 64) = 0 then emp else
      A.live 1#64 (0#64 : BitVec 64).toNat 1 ∗ (1#64 ↦ₛ ([] : List (BitVec 8))) ∗
        memRegion (1#64 + BitVec.ofNat 64 ([] : List (BitVec 8)).length)
          ((0#64 : BitVec 64).toNat - ([] : List (BitVec 8)).length)) = emp := rfl
  have h0 : BitVec.ofNat 64 ([] : List (BitVec 8)).length = 0#64 := rfl
  have hp : (0 : Nat) ≤ (0#64 : BitVec 64).toNat ∧
      (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0 :=
    ⟨by decide, by decide, by decide⟩
  rw [hite, h0, List.length_nil, sepConj_emp, eq_true hp, pure_true]
  simp only [emp_sepConj, sepConj_emp]

private theorem pendingAt9PCap_fresh_unfold (A : RustAlloc) (ss : BitVec 64) (v : SSGX)
    (hp : v.base.pending = none) :
    pendingAt9PCap A ss v =
      ((ss + 0xf8#64) ↦₆₄ noneCap) ∗
      (∃∗ w100 : BitVec 64, (ss + 0x100#64) ↦₆₄ w100) ∗
      (∃∗ w108 : BitVec 64, (ss + 0x108#64) ↦₆₄ w108) ∗
      (∃∗ w110 : BitVec 64, (ss + 0x110#64) ↦₆₄ w110) ∗
      (∃∗ w118 : BitVec 64, (ss + 0x118#64) ↦₆₄ w118) ∗
      (∃∗ w120 : BitVec 32, (ss + 0x120#64) ↦₃₂ w120) ∗
      memRegion (ss + 0x124#64) 4 := by
  unfold pendingAt9PCap
  rw [hp, memRegion_40_split_x9p ss]

private theorem pendingAt9PCap_post_fold_none (A : RustAlloc) (ss v24 : BitVec 64)
    (k : List (BitVec 8)) (spk : BitVec 32) {vx : SSGX}
    (hpend : vx.base.pending = some k) (hpid : vx.ext.pid = none) (hspk : vx.ext.spkId = spk) :
    vecU8FreshCap A (ss + 248#64) k ∗
      ((ss + 272#64) ↦₆₄ (v24 &&& 18446744069414584320#64 ||| 0#64)) ∗
      ((ss + 280#64) ↦₆₄ 0#64) ∗ ((ss + 288#64) ↦₃₂ spk) ∗
      memRegion (ss + 292#64) 4 ⊢
      pendingAt9PCap A ss vx := by
  have ha0 : ss + 248#64 = ss + 0xf8#64 := rfl
  have ha1 : ss + 280#64 = ss + 0x118#64 := rfl
  have ha2 : ss + 288#64 = ss + 0x120#64 := rfl
  have ha3 : ss + 292#64 = ss + 0x124#64 := rfl
  rw [ha0, ha1, ha2, ha3]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_left (pid_none_entails_x9p ss v24))) ?_
  unfold pendingAt9PCap pidAt
  rw [hpend, hpid, hspk]
  dsimp only
  exact Entails.of_eq (by sep_ac_rfl)

private theorem pendingAt9PCap_post_fold_some (A : RustAlloc) (ss : BitVec 64)
    (i : BitVec 32) (k : List (BitVec 8)) (spk : BitVec 32) {vx : SSGX}
    (hpend : vx.base.pending = some k) (hpid : vx.ext.pid = some i) (hspk : vx.ext.spkId = spk) :
    vecU8FreshCap A (ss + 248#64) k ∗
      ((ss + 272#64) ↦₃₂ 1#32) ∗ ((ss + 276#64) ↦₃₂ i) ∗
      ((ss + 280#64) ↦₆₄ 0#64) ∗ ((ss + 288#64) ↦₃₂ spk) ∗
      memRegion (ss + 292#64) 4 ⊢
      pendingAt9PCap A ss vx := by
  unfold pendingAt9PCap pidAt
  rw [hpend, hpid, hspk]
  dsimp only
  exact Entails.of_eq (by sep_ac_rfl)

private theorem pending_payload_eq_mfb {k : List (BitVec 8)} (hk : k.length = 33) :
    (GenField.pending k).payload = 35#8 :: 18#8 :: 33#8 :: k := by
  have h1 : lenField 2 k = 18#8 :: 33#8 :: k := by
    unfold lenField
    rw [hk]
    rfl
  dsimp only [GenField.payload]
  rw [h1]
  simp only [List.length_cons, hk]
  rfl

private theorem pending_payload_length_mfb {k : List (BitVec 8)} (hk : k.length = 33) :
    (GenField.pending k).payload.length = 36 := by
  rw [pending_payload_eq_mfb hk]; simp [hk]

private theorem sliceCursorAt_pending_unfold_mfb (slot ptr : BitVec 64)
    {k : List (BitVec 8)} (hk : k.length = 33) (tail : List (BitVec 8)) :
    sliceCursorAt slot ptr ((GenField.pending k).payload ++ tail) =
      (slot ↦₆₄ ptr) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (36 + tail.length)) ∗
      (ptr ↦₈ 35#8) ∗ ((ptr + 1#64) ↦₈ 18#8) ∗
      ((ptr + 2#64) ↦ₛ (33#8 :: k ++ tail)) := by
  unfold sliceCursorAt
  rw [List.length_append, pending_payload_length_mfb hk, pending_payload_eq_mfb hk]
  simp only [List.cons_append, pointsToBytes_cons,
    show ptr + 1#64 + 1#64 = ptr + 2#64 by bv_lin, sepConj_assoc]

private theorem sliceCursorAfter_pending_fold_mfb (slot ptr : BitVec 64)
    {k : List (BitVec 8)} (hk : k.length = 33) (tail : List (BitVec 8)) :
    (slot ↦₆₄ (ptr + 2#64 + 34#64)) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
      (ptr ↦₈ 35#8) ∗ ((ptr + 1#64) ↦₈ 18#8) ∗
      ((ptr + 2#64) ↦ₛ (33#8 :: k)) ∗
      ((ptr + 2#64 + 34#64) ↦ₛ tail) =
      sliceCursorAfter slot ptr ((GenField.pending k).payload ++ tail) tail := by
  unfold sliceCursorAfter
  have hsub : ((GenField.pending k).payload ++ tail).length - tail.length = 36 := by
    rw [List.length_append, pending_payload_length_mfb hk]; omega
  rw [hsub, pending_payload_eq_mfb hk]
  simp only [List.cons_append, pointsToBytes_cons,
    show ptr + 1#64 + 1#64 = ptr + 2#64 by bv_lin,
    show ptr + 2#64 + 34#64 = ptr + 36#64 by bv_lin]
  rw [pointsToBytes_append, hk,
    show ptr + 2#64 + 1#64 + BitVec.ofNat 64 33 = ptr + 36#64 by bv_lin]
  sep_ac_rfl

private theorem pointsTo32_zero_entails_memRegion4_mfb (dst : BitVec 64) :
    (dst ↦₃₂ 0#32) ⊢ memRegion dst 4 := by
  rw [ProofLib.memRegion_four dst]
  exact Entails.sepExists_right 0#32 (Entails.refl _)

private theorem entails_frame_memRegion4 {A B F : SepProp} {dst : BitVec 64}
    (h1 : A ⊢ ((dst ↦₃₂ 0#32) ∗ B) ∗ F) :
    A ⊢ (memRegion dst 4 ∗ B) ∗ F :=
  Entails.trans h1 (sepConj_mono_left (sepConj_mono_left (pointsTo32_zero_entails_memRegion4_mfb dst)))

private theorem add_neg_body_len_mfb {L n : Nat} (_hlen : L + n < 2 ^ 62) :
    BitVec.ofNat 64 (L + n) + (-BitVec.ofNat 64 L) = BitVec.ofNat 64 n := by
  rw [← BitVec.sub_eq_add_neg]
  exact (subs_body_len_x9pW _hlen).1

set_option maxHeartbeats 1600000 in
private theorem step_tag9_pending_mfb [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H)
    (ss bufRef slot ptr : BitVec 64) (vx vx' : SSGX) (k : List (BitVec 8))
    (hk : k.length = 33) (hp : vx.base.pending = none)
    (hpend' : vx'.base.pending = some k) (hpid' : vx'.ext.pid = none)
    (hspk' : vx'.ext.spkId = 0#32)
    (tail : List (BitVec 8)) (st : M.σ) {s0 : State}
    (hpc : s0.pc = (blkPl_15).base) (hrun : s0.status = .Running)
    (hsp_align : s0.spAligned = true)
    (hcl : LibsignalCodeLoaded lsmpl s0.mem) (hro : LibsignalRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = ss)
    (hx1 : (s0.readReg64 .x1).setWidth 32 = 9#32)
    (hx2 : (s0.readReg64 .x2).setWidth 8 = 2#8)
    (hx3 : s0.readReg64 .x3 = bufRef)
    (hx4 : (s0.readReg64 .x4).setWidth 32 = 99#32)
    (hlen : ((GenField.pending k).payload ++ tail).length < 2 ^ 62)
    (hfit : FitsEvents M lim st (bytesMergeAllocEvents 0 k.length)) :
    SepWPp (lsProg_15 H) (s0.readReg64 .lr) s0
      (pendingAt9PCap A.repAlloc ss vx ∗ (bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr ((GenField.pending k).payload ++ tail) ∗
        A.pool lim st s0 ∗ stackAt s0.sp mergeFieldStackX)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace ∧
        sf.readReg64 .x0 = 0#64 ∧
        (Pf ⊢ pendingAt9PCap A.repAlloc ss vx' ∗ (bufRef ↦₆₄ slot) ∗
          sliceCursorAfter slot ptr ((GenField.pending k).payload ++ tail) tail ∗
          A.pool lim (M.stepEvents (bytesMergeEvents 0 k.length) st) sf ∗
          stackAt s0.sp mergeFieldStackX))
      NoPanicPost := by
  have halign : s0.sp &&& 15#64 = 0#64 := by simpa [State.spAligned] using hsp_align
  have hsp240 := sp_sub_240_aligned_identityRootKeys halign
  have hcallB := bytes_merge_fresh_budget_placed_okW_cl (callerProg := lsProg_15 H) hA
  rw [List.length_append, pending_payload_length_mfb hk] at hlen
  have hx1_tr : BitVec.truncate 32 (s0.readReg64 .x1) = 9#32 := hx1
  have hx4_tr : BitVec.truncate 32 (s0.readReg64 .x4) = 99#32 := hx4
  have hx2_tr := wt_and_ff_eq_mf14W (s0.readReg64 .x2) hx2
  have hx2_64 := wt_and_ff_64_eq_mf14W (s0.readReg64 .x2) hx2
  have hl_ne0 := len_ne_zero_x9pW (a := 36) (n := tail.length) (by omega) hlen
  obtain ⟨hl_s1, hl_a1⟩ := sub1_and_add_neg1_x9pW (a := 36) (a' := 35) (n := tail.length)
    (by omega) hlen
  obtain ⟨hsubL, hultL, huleL⟩ := subs_body_len_x9pW (L := 35) (n := tail.length) (by omega)
  have hadd_neg35 := add_neg_body_len_mfb (L := 35) (n := tail.length) (by omega)
  obtain ⟨hl2_s1, hl2_a1⟩ := sub1_and_add_neg1_x9pW (a := 35) (a' := 34) (n := tail.length)
    (by omega) (by omega)
  obtain ⟨hult1, hule1, hult1', hsub1⟩ := cmp_gt_tail_x9pW (a := 35) (n := tail.length)
    (by omega) (by omega)
  conv =>
    arg 4
    rw [pendingAt9PCap_fresh_unfold A.repAlloc ss vx hp,
        sliceCursorAt_pending_unfold_mfb slot ptr hk tail]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun w100 => SepWPp.exists_elim fun w108 =>
    SepWPp.exists_elim fun w110 => SepWPp.exists_elim fun w118 =>
    SepWPp.exists_elim fun w120 => ?_
  conv =>
    arg 4
    rw [stackAt_mergeFieldX_unfold_x9pW s0.sp]
    simp only [sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun s80 => SepWPp.exists_elim fun s72 =>
    SepWPp.exists_elim fun s64 => SepWPp.exists_elim fun s56 =>
    SepWPp.exists_elim fun s48 => SepWPp.exists_elim fun s40 =>
    SepWPp.exists_elim fun s32 => SepWPp.exists_elim fun s24 =>
    SepWPp.exists_elim fun s16 => SepWPp.exists_elim fun s8 => ?_
  have hlsb := pid_disc_lsb_x9p w110
  simp only [arm64_norm] at hx0 hx1 hx2 hx3 hx4
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
  apply sepWPp_seq_lsclro_vm hcl1 hro1 (mid := (blkPl_15).base + 788#64)
  refine sepWP_intro_ro8_mfb (lsmpl.ρ mergeFieldRodataSym + 8#64) 181#8
    (fun hm => lsro8_intro hro1 (by lsro_addr) (by decide +kernel) hm) ?_
  by_vm_steps_withSvc (
    wp_steps
    apply sepWP_drop_left_mfb
    refine SepWP.done (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm2 hcl2 hro2
  rw [← A.pool_transport lim st _ _ hvm2]
  apply sepWPp_seq_lsclro_vm hcl2 hro2 (mid := lsmpl.base 7)
  by_vm_steps_withSvc (
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm3 hcl3 hro3
  rw [← A.pool_transport lim st _ _ hvm3]
  rw [stackAt_sub_bytes_split (s0.sp - 240#64)]
  refine sepWPp_call_lscro_15
    (x := (⟨.lengthDelimited, ss + 248#64, 0#64, 1#64, [], bufRef, slot,
      ptr + 2#64, 33#8 :: k ++ tail⟩, k, tail, st))
    hcallB hcl3 hro3
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp240, beq_self_eq_true])
    (by simp only [wp_norm, arm64_norm]; rfl)
    (by
      dsimp only [bytesMergeFreshBudgetSpecW]
      apply entails_pure_sep_frame
      · refine ⟨?_, ?_, ?_, by simp only [List.length_cons, List.length_append, hk]; omega,
          rfl, rfl, mergeBytes_k_x9p hk tail, hfit⟩
        · simp only [wp_norm, arm64_norm]
        · simp only [wp_norm, arm64_norm]
        · simp only [wp_norm, arm64_norm]
      · apply entails_rw_stack_5 (sp2 := s0.sp - 240#64) (w2 := bytesMergeStackW)
        · simp only [wp_norm, arm64_norm]
        · rfl
        · rw [← emptyVec_pending_eq_vecU8At_x9p A.repAlloc ss,
              ← sliceCursorAt_bytes_gen_fold_x9p slot (ptr + 2#64) hk tail]
          sep_frame)
    ?_
  intro sm hpcm hrunm hspm hcsm _hclm _hrom
  dsimp only [bytesMergeFreshBudgetSpecW]
  refine sepWPp_pure_left_and fun ⟨hx0m, htrm⟩ => ?_
  try simp only [wp_norm, arm64_norm] at hpcm
  have hx0m' : sm.readReg64 (Reg.gpr 0#5) = 0#64 := hx0m
  have hspm' : sm.sp = s0.sp - 240#64 := by simpa only [wp_norm, arm64_norm] using hspm
  have htrm' : sm.trace = s0.trace := by simpa only [wp_norm, arm64_norm] using htrm
  have hx21m : sm.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tail.length := by
    simpa only [wp_norm, arm64_norm] using hcsm.2.2.1
  have hx24m : sm.readReg64 (Reg.gpr 24#5) = bufRef := by
    simpa only [wp_norm, arm64_norm] using hcsm.2.2.2.2.2.1
  have hx26m : sm.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := by
    simpa only [wp_norm, arm64_norm] using hcsm.2.2.2.2.2.2.2.1
  have hx27m : sm.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
    simpa only [wp_norm, arm64_norm] using hcsm.2.2.2.2.2.2.2.2.1
  have hx28m : sm.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
    simpa only [wp_norm, arm64_norm] using hcsm.2.2.2.2.2.2.2.2.2.1
  have hvregsm : calleeSavedVRegs sm = calleeSavedVRegs s0 := by
    simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hcsm.2.2.2.2.2.2.2.2.2.2.2
  have htail_ult_self :
      BitVec.ult (BitVec.ofNat 64 tail.length) (BitVec.ofNat 64 tail.length) = false := by
    simp [BitVec.ult]
  have htail_ule_self :
      BitVec.ule (BitVec.ofNat 64 tail.length) (BitVec.ofNat 64 tail.length) = true := by
    simp [BitVec.ule]
  conv =>
    arg 4
    rw [show stackAt _ bytesMergeStackW = stackAt (s0.sp - 240#64) bytesMergeStackW by
          simp only [wp_norm, arm64_norm],
        sliceCursorAfter_bytes_gen_unfold_x9p slot (ptr + 2#64) hk tail]
  refine SepWPp.weaken_pre (P' :=
      vecU8FreshCap A.repAlloc (ss + 248#64) k ∗
        ((ss + 272#64) ↦₆₄ (w110 &&& 18446744069414584320#64 ||| 0#64)) ∗
        ((ss + 280#64) ↦₆₄ 0#64) ∗ ((ss + 288#64) ↦₃₂ 0#32) ∗
        memRegion (ss + 292#64) 4 ∗
        (ptr ↦₈ 35#8) ∗ ((ptr + 1#64) ↦₈ 18#8) ∗
        ((ptr + 2#64) ↦ₛ (33#8 :: k)) ∗ ((ptr + 2#64 + 34#64) ↦ₛ tail) ∗
        (bufRef ↦₆₄ slot) ∗ (slot ↦₆₄ (ptr + 2#64 + 34#64)) ∗
        ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
        A.pool lim (M.stepEvents (bytesMergeEvents 0 k.length) st) sm ∗
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
        ((s0.sp - 56#64) ↦₆₄ s56) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
        memRegion (s0.sp - 240#64) 160 ∗
        stackAt (s0.sp - 240#64) mergeFieldSubStackX)
    (Entails.of_eq (by
      unfold vecU8FreshCap
      rw [stackAt_sub_bytes_split (s0.sp - 240#64)]
      sep_ac_rfl)) ?_
  apply SepWPp.of_sepWP_ret
  apply sepWP_ret_vmPreserved
  by_vm_steps_withSvc (
    iterate 19 wp_step
    refine SepWP.done (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrunm])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm_end
  rw [← A.pool_transport lim (M.stepEvents (bytesMergeEvents 0 k.length) st) sm _ hvm_end]
  apply SepWP.done (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrunm])
  refine ⟨by simp only [wp_norm, arm64_norm, hspm'],
    by simp only [CalleeSavedPreserved, calleeSavedVRegs, wp_norm, arm64_norm,
      hx26m, hx27m, hx28m, hvregsm, and_self],
    by simp only [wp_norm, arm64_norm, htrm'],
    by simp only [wp_norm, arm64_norm, hx0m'], ?_⟩
  have hstk := stackAt_mergeField_fold_mf14W s0.sp
    (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
    (s0.readReg64 (Reg.gpr 25#5)) s56
    (s0.readReg64 (Reg.gpr 24#5)) (s0.readReg64 (Reg.gpr 23#5))
    (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
    (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5))
  have hp_post := pendingAt9PCap_post_fold_none A.repAlloc ss w110 k 0#32 hpend' hpid' hspk'
  rw [← sliceCursorAfter_pending_fold_mfb slot ptr hk tail]
  refine Entails.trans (Entails.of_eq ?_)
    (sepConj_mono hp_post (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hstk))))
  sep_ac_rfl

set_option maxHeartbeats 1600000 in
private theorem step_tag9_id_mfb [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H)
    (ss bufRef slot ptr : BitVec 64) (vx vx' : SSGX) (i : BitVec 32) (k : List (BitVec 8))
    (hk : k.length = 33) (hp : vx.base.pending = none)
    (hpend' : vx'.base.pending = some k) (hpid' : vx'.ext.pid = some i)
    (hspk' : vx'.ext.spkId = 0#32)
    (tail : List (BitVec 8)) (st : M.σ) {s0 : State}
    (hpc : s0.pc = (blkPl_15).base) (hrun : s0.status = .Running)
    (hsp_align : s0.spAligned = true)
    (hcl : LibsignalCodeLoaded lsmpl s0.mem) (hro : LibsignalRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = ss)
    (hx1 : (s0.readReg64 .x1).setWidth 32 = 9#32)
    (hx2 : (s0.readReg64 .x2).setWidth 8 = 2#8)
    (hx3 : s0.readReg64 .x3 = bufRef)
    (hx4 : (s0.readReg64 .x4).setWidth 32 = 99#32)
    (hlen : ((GenFieldX.pendingId i k).payload ++ tail).length < 2 ^ 62)
    (hfit : FitsEvents M lim st (bytesMergeAllocEvents 0 k.length)) :
    SepWPp (lsProg_15 H) (s0.readReg64 .lr) s0
      (pendingAt9PCap A.repAlloc ss vx ∗ (bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr ((GenFieldX.pendingId i k).payload ++ tail) ∗
        A.pool lim st s0 ∗ stackAt s0.sp mergeFieldStackX)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace ∧
        sf.readReg64 .x0 = 0#64 ∧
        (Pf ⊢ pendingAt9PCap A.repAlloc ss vx' ∗ (bufRef ↦₆₄ slot) ∗
          sliceCursorAfter slot ptr ((GenFieldX.pendingId i k).payload ++ tail) tail ∗
          A.pool lim (M.stepEvents (bytesMergeEvents 0 k.length) st) sf ∗
          stackAt s0.sp mergeFieldStackX))
      NoPanicPost := by
  have halign : s0.sp &&& 15#64 = 0#64 := by simpa [State.spAligned] using hsp_align
  have hsp240 := sp_sub_240_aligned_identityRootKeys halign
  have hcallI := int32_merge_some_placed_ok_cl (callerProg := lsProg_15 H)
    (errStack := decodeErrorHookStackW) (by decide)
  have hcallB := bytes_merge_fresh_budget_placed_okW_cl (callerProg := lsProg_15 H) hA
  have hm := encodeVarint_length_bounds_mf14 (i.setWidth 64)
  rw [List.length_append, pendingId_payload_length_x9p i hk] at hlen
  have hx1_tr : BitVec.truncate 32 (s0.readReg64 .x1) = 9#32 := hx1
  have hx4_tr : BitVec.truncate 32 (s0.readReg64 .x4) = 99#32 := hx4
  have hx2_tr := wt_and_ff_eq_mf14W (s0.readReg64 .x2) hx2
  have hx2_64 := wt_and_ff_64_eq_mf14W (s0.readReg64 .x2) hx2
  have hl_ne0 := len_ne_zero_x9pW (a := 37 + (encodeVarint (i.setWidth 64)).length)
    (n := tail.length) (by omega) hlen
  obtain ⟨hl_s1, hl_a1⟩ := sub1_and_add_neg1_x9pW
    (a := 37 + (encodeVarint (i.setWidth 64)).length)
    (a' := 36 + (encodeVarint (i.setWidth 64)).length)
    (n := tail.length) (by omega) hlen
  obtain ⟨hsubL, hultL, huleL⟩ := subs_body_len_x9pW
    (L := 36 + (encodeVarint (i.setWidth 64)).length) (n := tail.length) (by omega)
  have hadd_negL := add_neg_body_len_mfb
    (L := 36 + (encodeVarint (i.setWidth 64)).length) (n := tail.length) (by omega)
  obtain ⟨hl2_s1, hl2_a1⟩ := sub1_and_add_neg1_x9pW
    (a := 36 + (encodeVarint (i.setWidth 64)).length)
    (a' := 35 + (encodeVarint (i.setWidth 64)).length)
    (n := tail.length) (by omega) (by omega)
  obtain ⟨hult1, hule1, hult1', hsub1⟩ := cmp_gt_tail_x9pW
    (a := 36 + (encodeVarint (i.setWidth 64)).length) (n := tail.length) (by omega) (by omega)
  obtain ⟨hl35_s1, hl35_a1⟩ := sub1_and_add_neg1_x9pW
    (a := 35) (a' := 34) (n := tail.length) (by omega) (by omega)
  obtain ⟨hult2, hule2, hult2', hsub2⟩ := cmp_gt_tail_x9pW
    (a := 35) (n := tail.length) (by omega) (by omega)
  conv =>
    arg 4
    rw [pendingAt9PCap_fresh_unfold A.repAlloc ss vx hp,
        sliceCursorAt_unfold_id_x9p slot ptr i hk tail]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun w100 => SepWPp.exists_elim fun w108 =>
    SepWPp.exists_elim fun w110 => SepWPp.exists_elim fun w118 =>
    SepWPp.exists_elim fun w120 => ?_
  conv =>
    arg 4
    rw [stackAt_mergeFieldX_unfold_x9pW s0.sp]
    simp only [sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun s80 => SepWPp.exists_elim fun s72 =>
    SepWPp.exists_elim fun s64 => SepWPp.exists_elim fun s56 =>
    SepWPp.exists_elim fun s48 => SepWPp.exists_elim fun s40 =>
    SepWPp.exists_elim fun s32 => SepWPp.exists_elim fun s24 =>
    SepWPp.exists_elim fun s16 => SepWPp.exists_elim fun s8 => ?_
  have hlsb := pid_disc_lsb_x9p w110
  simp only [arm64_norm] at hx0 hx1 hx2 hx3 hx4
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
  apply sepWPp_seq_lsclro_vm hcl1 hro1 (mid := (blkPl_15).base + 788#64)
  refine sepWP_intro_ro8_mfb (lsmpl.ρ mergeFieldRodataSym + 8#64) 181#8
    (fun hm => lsro8_intro hro1 (by lsro_addr) (by decide +kernel) hm) ?_
  by_vm_steps_withSvc (
    wp_steps
    apply sepWP_drop_left_mfb
    refine SepWP.done (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm2 hcl2 hro2
  rw [← A.pool_transport lim st _ _ hvm2]
  apply sepWPp_seq_lsclro_vm hcl2 hro2 (mid := lsmpl.base 8)
  by_vm_steps_withSvc (
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm3 hcl3 hro3
  rw [← A.pool_transport lim st _ _ hvm3]
  have hlen_i1 : 35 + (encodeVarint (i.setWidth 64)).length + tail.length =
      (encodeVarint (i.setWidth 64)).length + (18#8 :: 33#8 :: k ++ tail).length := by
    simp only [List.length_cons, List.length_append, hk]; omega
  conv =>
    arg 4
    rw [split_272_x9p ss, stackAt_sub_to_int32Merge_mf14W (s0.sp - 240#64)]
  refine sepWPp_call_lscl_15
    (x := (⟨.varint, ss + 276#64, bufRef, slot, ptr + 2#64,
      encodeVarint (i.setWidth 64) ++ (18#8 :: 33#8 :: k ++ tail)⟩, i,
      18#8 :: 33#8 :: k ++ tail))
    hcallI hcl3 hro3
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp240, beq_self_eq_true])
    (by simp only [wp_norm, arm64_norm]; rfl)
    (by
      dsimp only [ProstVarintVm.int32MergeSomeSpecGen]
      apply entails_pure_sep_frame
      · refine ⟨?_, ?_, ?_, by simp only [List.length_append, List.length_cons, hk]; omega, ?_⟩
        · simp only [wp_norm, arm64_norm]
        · simp only [wp_norm, arm64_norm]
        · simp only [wp_norm, arm64_norm]
        · rw [mergeUint32_encode_64_x9p, setWidth32_setWidth64_x9p]
      · apply entails_frame_memRegion4
        apply entails_rw_stack_4 (sp2 := s0.sp - 240#64) (w2 := int32MergeStackW)
        · simp only [wp_norm, arm64_norm]
        · rfl
        · rw [show ((slot + 8#64) ↦₆₄ BitVec.ofNat 64
                  (35 + (encodeVarint (i.setWidth 64)).length + tail.length)) =
                ((slot + 8#64) ↦₆₄ BitVec.ofNat 64
                  ((encodeVarint (i.setWidth 64)).length + (18#8 :: 33#8 :: k ++ tail).length)) by
                rw [hlen_i1],
              ← sliceCursorAt_int32_gen_fold_x9p slot (ptr + 2#64) (i.setWidth 64)
                (18#8 :: 33#8 :: k ++ tail)]
          sep_frame)
    ?_
  intro sm1 hpcm1 hrunm1 hspm1 hcsm1 hclm1 hrom1
  dsimp only [ProstVarintVm.int32MergeSomeSpecGen]
  refine sepWPp_pure_left_and fun ⟨hx0m1, htrm1, hvmm1⟩ => ?_
  rw [← A.pool_transport lim st _ sm1 hvmm1]
  try simp only [wp_norm, arm64_norm] at hpcm1
  have hx0m1' : sm1.readReg64 (Reg.gpr 0#5) = 0#64 := hx0m1
  have hspm1' : sm1.sp = s0.sp - 240#64 := by simpa only [wp_norm, arm64_norm] using hspm1
  have htrm1' : sm1.trace = s0.trace := by simpa only [wp_norm, arm64_norm] using htrm1
  have hx19m1 : sm1.readReg64 (Reg.gpr 19#5) = ss + 248#64 := by
    simpa only [wp_norm, arm64_norm] using hcsm1.1
  have hx20m1 : sm1.readReg64 (Reg.gpr 20#5) = 98#64 := by
    simpa only [wp_norm, arm64_norm] using hcsm1.2.1
  have hx21m1 : sm1.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tail.length := by
    simpa only [wp_norm, arm64_norm] using hcsm1.2.2.1
  have hx22m1 : sm1.readReg64 (Reg.gpr 22#5) = 1#64 := by
    simpa only [wp_norm, arm64_norm] using hcsm1.2.2.2.1
  have hx23m1 : sm1.readReg64 (Reg.gpr 23#5) = ss := by
    simpa only [wp_norm, arm64_norm] using hcsm1.2.2.2.2.1
  have hx24m1 : sm1.readReg64 (Reg.gpr 24#5) = bufRef := by
    simpa only [wp_norm, arm64_norm] using hcsm1.2.2.2.2.2.1
  have hx25m1 : sm1.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) := by
    simpa only [wp_norm, arm64_norm] using hcsm1.2.2.2.2.2.2.1
  have hx26m1 : sm1.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := by
    simpa only [wp_norm, arm64_norm] using hcsm1.2.2.2.2.2.2.2.1
  have hx27m1 : sm1.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
    simpa only [wp_norm, arm64_norm] using hcsm1.2.2.2.2.2.2.2.2.1
  have hx28m1 : sm1.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
    simpa only [wp_norm, arm64_norm] using hcsm1.2.2.2.2.2.2.2.2.2.1
  have hvregsm1 : calleeSavedVRegs sm1 = calleeSavedVRegs s0 := by
    simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hcsm1.2.2.2.2.2.2.2.2.2.2.2
  have hstk_i : 0x50 + (0x50 + decodeErrorHookStackW) = int32MergeStackW := rfl
  have hlen_i2 : (18#8 :: 33#8 :: k ++ tail).length = 35 + tail.length := by
    simp only [List.cons_append, List.length_cons, List.length_append, hk]; omega
  conv =>
    arg 4
    rw [hstk_i,
        show stackAt _ int32MergeStackW = stackAt (s0.sp - 240#64) int32MergeStackW by
          simp only [wp_norm, arm64_norm],
        sliceCursorAfter_int32_gen_unfold_x9p slot (ptr + 2#64) (i.setWidth 64)
          (18#8 :: 33#8 :: k ++ tail),
        hlen_i2,
        show ptr + 2#64 + BitVec.ofNat 64 (encodeVarint (i.setWidth 64)).length =
          pendingPtr2 ptr i from rfl]
    simp only [List.cons_append, pointsToBytes_cons, sepConj_assoc]
  apply sepWPp_seq_lsclro_vm hclm1 hrom1 (mid := lsmpl.base 7)
  by_vm_steps_withSvc (
    iterate 35 wp_step
    refine SepWP.done (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrunm1])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm4 hcl4 hro4
  rw [← A.pool_transport lim st sm1 _ hvm4]
  refine sepWPp_call_lscro_15
    (x := (⟨.lengthDelimited, ss + 248#64, 0#64, 1#64, [], bufRef, slot,
      pendingPtr2 ptr i + 1#64, 33#8 :: k ++ tail⟩, k, tail, st))
    hcallB hcl4 hro4
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrunm1])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hspm1', hsp240, beq_self_eq_true])
    (by simp only [wp_norm, arm64_norm]; rfl)
    (by
      dsimp only [bytesMergeFreshBudgetSpecW]
      apply entails_pure_sep_frame
      · refine ⟨?_, ?_, ?_, by simp only [List.length_cons, List.length_append, hk]; omega,
          rfl, rfl, mergeBytes_k_x9p hk tail, hfit⟩
        · simp only [wp_norm, arm64_norm]
        · simp only [wp_norm, arm64_norm, hx19m1]
        · simp only [wp_norm, arm64_norm, hx24m1]
      · apply entails_rw_stack_5 (sp2 := s0.sp - 240#64) (w2 := bytesMergeStackW)
        · simp only [wp_norm, arm64_norm, hspm1']
        · rfl
        · apply entails_swap_stack_5 (int32Merge_to_bytesMerge_stack_mf14W (s0.sp - 240#64))
          rw [← emptyVec_pending_eq_vecU8At_x9p A.repAlloc ss,
              ← sliceCursorAt_bytes_gen_fold_x9p slot (pendingPtr2 ptr i + 1#64) hk tail,
              List.cons_append, pointsToBytes_cons]
          sep_frame)
    ?_
  intro sm2 hpcm2 hrunm2 hspm2 hcsm2 _hclm2 _hrom2
  dsimp only [bytesMergeFreshBudgetSpecW]
  refine sepWPp_pure_left_and fun ⟨hx0m2, htrm2⟩ => ?_
  try simp only [wp_norm, arm64_norm] at hpcm2
  have hx0m2' : sm2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0m2
  have hspm2' : sm2.sp = s0.sp - 240#64 := by
    simpa only [wp_norm, arm64_norm, hspm1'] using hspm2
  have htrm2' : sm2.trace = s0.trace := by
    simpa only [wp_norm, arm64_norm, htrm1'] using htrm2
  have hx21m2 : sm2.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tail.length := by
    simpa only [wp_norm, arm64_norm, hx21m1] using hcsm2.2.2.1
  have hx24m2 : sm2.readReg64 (Reg.gpr 24#5) = bufRef := by
    simpa only [wp_norm, arm64_norm, hx24m1] using hcsm2.2.2.2.2.2.1
  have hx26m2 : sm2.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := by
    simpa only [wp_norm, arm64_norm, hx26m1] using hcsm2.2.2.2.2.2.2.2.1
  have hx27m2 : sm2.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
    simpa only [wp_norm, arm64_norm, hx27m1] using hcsm2.2.2.2.2.2.2.2.2.1
  have hx28m2 : sm2.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
    simpa only [wp_norm, arm64_norm, hx28m1] using hcsm2.2.2.2.2.2.2.2.2.2.1
  have hvregsm2 : calleeSavedVRegs sm2 = calleeSavedVRegs s0 := by
    have h1 : calleeSavedVRegs sm2 = calleeSavedVRegs sm1 := by
      simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hcsm2.2.2.2.2.2.2.2.2.2.2.2
    exact h1.trans hvregsm1
  have htail_ult_self :
      BitVec.ult (BitVec.ofNat 64 tail.length) (BitVec.ofNat 64 tail.length) = false := by
    simp [BitVec.ult]
  have htail_ule_self :
      BitVec.ule (BitVec.ofNat 64 tail.length) (BitVec.ofNat 64 tail.length) = true := by
    simp [BitVec.ule]
  conv =>
    arg 4
    rw [show stackAt _ bytesMergeStackW = stackAt (s0.sp - 240#64) bytesMergeStackW by
          simp only [wp_norm, arm64_norm, hspm1'],
        sliceCursorAfter_bytes_gen_unfold_x9p slot (pendingPtr2 ptr i + 1#64) hk tail]
  refine SepWPp.weaken_pre (P' :=
      vecU8FreshCap A.repAlloc (ss + 248#64) k ∗
        ((ss + 272#64) ↦₃₂ 1#32) ∗ ((ss + 276#64) ↦₃₂ i) ∗
        ((ss + 280#64) ↦₆₄ 0#64) ∗ ((ss + 288#64) ↦₃₂ 0#32) ∗
        memRegion (ss + 292#64) 4 ∗
        (ptr ↦₈ BitVec.ofNat 8 (36 + (encodeVarint (i.setWidth 64)).length)) ∗
        ((ptr + 1#64) ↦₈ 8#8) ∗
        ((ptr + 2#64) ↦ₛ encodeVarint (i.setWidth 64)) ∗
        (pendingPtr2 ptr i ↦₈ 18#8) ∗
        ((pendingPtr2 ptr i + 1#64) ↦ₛ (33#8 :: k)) ∗
        ((pendingPtr2 ptr i + 1#64 + 34#64) ↦ₛ tail) ∗
        (bufRef ↦₆₄ slot) ∗ (slot ↦₆₄ (pendingPtr2 ptr i + 1#64 + 34#64)) ∗
        ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
        A.pool lim (M.stepEvents (bytesMergeEvents 0 k.length) st) sm2 ∗
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
        ((s0.sp - 56#64) ↦₆₄ s56) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
        memRegion (s0.sp - 240#64) 160 ∗
        stackAt (s0.sp - 240#64) mergeFieldSubStackX)
    (Entails.of_eq (by
      unfold vecU8FreshCap
      rw [stackAt_sub_to_bytesMerge_mf14W (s0.sp - 240#64)]
      sep_ac_rfl)) ?_
  apply SepWPp.of_sepWP_ret
  apply sepWP_ret_vmPreserved
  by_vm_steps_withSvc (
    iterate 19 wp_step
    refine SepWP.done (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrunm2])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm_end
  rw [← A.pool_transport lim (M.stepEvents (bytesMergeEvents 0 k.length) st) sm2 _ hvm_end]
  apply SepWP.done (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrunm2])
  refine ⟨by simp only [wp_norm, arm64_norm, hspm2'],
    by simp only [CalleeSavedPreserved, calleeSavedVRegs, wp_norm, arm64_norm,
      hx26m2, hx27m2, hx28m2, hvregsm2, and_self],
    by simp only [wp_norm, arm64_norm, htrm2'],
    by simp only [wp_norm, arm64_norm, hx0m2'], ?_⟩
  have hstk := stackAt_mergeField_fold_mf14W s0.sp
    (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
    (s0.readReg64 (Reg.gpr 25#5)) s56
    (s0.readReg64 (Reg.gpr 24#5)) (s0.readReg64 (Reg.gpr 23#5))
    (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
    (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5))
  have hp_post := pendingAt9PCap_post_fold_some A.repAlloc ss i k 0#32 hpend' hpid' hspk'
  rw [← sliceCursorAfter_fold_id_x9p slot ptr i hk tail]
  refine Entails.trans (Entails.of_eq ?_)
    (sepConj_mono hp_post (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hstk))))
  sep_ac_rfl

set_option maxHeartbeats 1600000 in
private theorem step_tag9_spk_none_mfb [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H)
    (ss bufRef slot ptr : BitVec 64) (vx vx' : SSGX) (k : List (BitVec 8)) (spk : BitVec 32)
    (hk : k.length = 33) (hspk : spk ≠ 0#32) (hp : vx.base.pending = none)
    (hpend' : vx'.base.pending = some k) (hpid' : vx'.ext.pid = none)
    (hspk' : vx'.ext.spkId = spk)
    (tail : List (BitVec 8)) (st : M.σ) {s0 : State}
    (hpc : s0.pc = (blkPl_15).base) (hrun : s0.status = .Running)
    (hsp_align : s0.spAligned = true)
    (hcl : LibsignalCodeLoaded lsmpl s0.mem) (hro : LibsignalRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = ss)
    (hx1 : (s0.readReg64 .x1).setWidth 32 = 9#32)
    (hx2 : (s0.readReg64 .x2).setWidth 8 = 2#8)
    (hx3 : s0.readReg64 .x3 = bufRef)
    (hx4 : (s0.readReg64 .x4).setWidth 32 = 99#32)
    (hlen : ((GenFieldX.pendingSpk none k spk).payload ++ tail).length < 2 ^ 62)
    (hfit : FitsEvents M lim st (bytesMergeAllocEvents 0 k.length)) :
    SepWPp (lsProg_15 H) (s0.readReg64 .lr) s0
      (pendingAt9PCap A.repAlloc ss vx ∗ (bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr ((GenFieldX.pendingSpk none k spk).payload ++ tail) ∗
        A.pool lim st s0 ∗ stackAt s0.sp mergeFieldStackX)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace ∧
        sf.readReg64 .x0 = 0#64 ∧
        (Pf ⊢ pendingAt9PCap A.repAlloc ss vx' ∗ (bufRef ↦₆₄ slot) ∗
          sliceCursorAfter slot ptr ((GenFieldX.pendingSpk none k spk).payload ++ tail) tail ∗
          A.pool lim (M.stepEvents (bytesMergeEvents 0 k.length) st) sf ∗
          stackAt s0.sp mergeFieldStackX))
      NoPanicPost := by
  have halign : s0.sp &&& 15#64 = 0#64 := by simpa [State.spAligned] using hsp_align
  have hsp240 := sp_sub_240_aligned_identityRootKeys halign
  have hcallI := int32_merge_some_placed_ok_cl (callerProg := lsProg_15 H)
    (errStack := decodeErrorHookStackW) (by decide)
  have hcallB := bytes_merge_fresh_budget_placed_okW_cl (callerProg := lsProg_15 H) hA
  have hm := encodeVarint_length_bounds_mf14 (spk.signExtend 64)
  rw [List.length_append, pendingSpk_none_payload_length_x9p hk hspk] at hlen
  have hx1_tr : BitVec.truncate 32 (s0.readReg64 .x1) = 9#32 := hx1
  have hx4_tr : BitVec.truncate 32 (s0.readReg64 .x4) = 99#32 := hx4
  have hx2_tr := wt_and_ff_eq_mf14W (s0.readReg64 .x2) hx2
  have hx2_64 := wt_and_ff_64_eq_mf14W (s0.readReg64 .x2) hx2
  have hl_ne0 := len_ne_zero_x9pW (a := 37 + (encodeVarint (spk.signExtend 64)).length)
    (n := tail.length) (by omega) hlen
  obtain ⟨hl_s1, hl_a1⟩ := sub1_and_add_neg1_x9pW
    (a := 37 + (encodeVarint (spk.signExtend 64)).length)
    (a' := 36 + (encodeVarint (spk.signExtend 64)).length)
    (n := tail.length) (by omega) hlen
  obtain ⟨hsubL, hultL, huleL⟩ := subs_body_len_x9pW
    (L := 36 + (encodeVarint (spk.signExtend 64)).length) (n := tail.length) (by omega)
  have hadd_negL := add_neg_body_len_mfb
    (L := 36 + (encodeVarint (spk.signExtend 64)).length) (n := tail.length) (by omega)
  obtain ⟨hl2_s1, hl2_a1⟩ := sub1_and_add_neg1_x9pW
    (a := 36 + (encodeVarint (spk.signExtend 64)).length)
    (a' := 35 + (encodeVarint (spk.signExtend 64)).length)
    (n := tail.length) (by omega) (by omega)
  obtain ⟨hult1, hule1, hult1', hsub1⟩ := cmp_gt_tail_x9pW
    (a := 36 + (encodeVarint (spk.signExtend 64)).length) (n := tail.length) (by omega) (by omega)
  obtain ⟨hl3_s1, hl3_a1⟩ := sub1_and_add_neg1_x9pW
    (a := 1 + (encodeVarint (spk.signExtend 64)).length)
    (a' := (encodeVarint (spk.signExtend 64)).length)
    (n := tail.length) (by omega) (by omega)
  obtain ⟨hult2, hule2, hult2', hsub2⟩ := cmp_gt_tail_x9pW
    (a := 1 + (encodeVarint (spk.signExtend 64)).length) (n := tail.length) (by omega) (by omega)
  conv =>
    arg 4
    rw [pendingAt9PCap_fresh_unfold A.repAlloc ss vx hp,
        sliceCursorAt_unfold_spk_none_x9p slot ptr hk hspk tail]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun w100 => SepWPp.exists_elim fun w108 =>
    SepWPp.exists_elim fun w110 => SepWPp.exists_elim fun w118 =>
    SepWPp.exists_elim fun w120 => ?_
  conv =>
    arg 4
    rw [stackAt_mergeFieldX_unfold_x9pW s0.sp]
    simp only [sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun s80 => SepWPp.exists_elim fun s72 =>
    SepWPp.exists_elim fun s64 => SepWPp.exists_elim fun s56 =>
    SepWPp.exists_elim fun s48 => SepWPp.exists_elim fun s40 =>
    SepWPp.exists_elim fun s32 => SepWPp.exists_elim fun s24 =>
    SepWPp.exists_elim fun s16 => SepWPp.exists_elim fun s8 => ?_
  have hlsb := pid_disc_lsb_x9p w110
  simp only [arm64_norm] at hx0 hx1 hx2 hx3 hx4
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
  apply sepWPp_seq_lsclro_vm hcl1 hro1 (mid := (blkPl_15).base + 788#64)
  refine sepWP_intro_ro8_mfb (lsmpl.ρ mergeFieldRodataSym + 8#64) 181#8
    (fun hm => lsro8_intro hro1 (by lsro_addr) (by decide +kernel) hm) ?_
  by_vm_steps_withSvc (
    wp_steps
    apply sepWP_drop_left_mfb
    refine SepWP.done (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm2 hcl2 hro2
  rw [← A.pool_transport lim st _ _ hvm2]
  apply sepWPp_seq_lsclro_vm hcl2 hro2 (mid := lsmpl.base 7)
  by_vm_steps_withSvc (
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm3 hcl3 hro3
  rw [← A.pool_transport lim st _ _ hvm3]
  set restSpk := 24#8 :: (encodeVarint (spk.signExtend 64) ++ tail)
  have hlen_b1 : 35 + (encodeVarint (spk.signExtend 64)).length + tail.length =
      34 + restSpk.length := by
    simp only [restSpk, List.length_cons, List.length_append]; omega
  conv =>
    arg 4
    rw [stackAt_sub_to_bytesMerge_mf14W (s0.sp - 240#64)]
  refine sepWPp_call_lscro_15
    (x := (⟨.lengthDelimited, ss + 248#64, 0#64, 1#64, [], bufRef, slot,
      ptr + 2#64, 33#8 :: k ++ restSpk⟩, k, restSpk, st))
    hcallB hcl3 hro3
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp240, beq_self_eq_true])
    (by simp only [wp_norm, arm64_norm]; rfl)
    (by
      dsimp only [bytesMergeFreshBudgetSpecW]
      apply entails_pure_sep_frame
      · refine ⟨?_, ?_, ?_,
          by simp only [restSpk, List.length_cons, List.length_append, hk]; omega,
          rfl, rfl, mergeBytes_k_x9p hk restSpk, hfit⟩
        · simp only [wp_norm, arm64_norm]
        · simp only [wp_norm, arm64_norm]
        · simp only [wp_norm, arm64_norm]
      · apply entails_rw_stack_5 (sp2 := s0.sp - 240#64) (w2 := bytesMergeStackW)
        · simp only [wp_norm, arm64_norm]
        · rfl
        · rw [hlen_b1,
              ← emptyVec_pending_eq_vecU8At_x9p A.repAlloc ss,
              ← sliceCursorAt_bytes_gen_fold_x9p slot (ptr + 2#64) hk restSpk]
          sep_frame)
    ?_
  intro sm1 hpcm1 hrunm1 hspm1 hcsm1 hclm1 hrom1
  dsimp only [bytesMergeFreshBudgetSpecW]
  refine sepWPp_pure_left_and fun ⟨hx0m1, htrm1⟩ => ?_
  try simp only [wp_norm, arm64_norm] at hpcm1
  have hx0m1' : sm1.readReg64 (Reg.gpr 0#5) = 0#64 := hx0m1
  have hspm1' : sm1.sp = s0.sp - 240#64 := by simpa only [wp_norm, arm64_norm] using hspm1
  have htrm1' : sm1.trace = s0.trace := by simpa only [wp_norm, arm64_norm] using htrm1
  have hx19m1 : sm1.readReg64 (Reg.gpr 19#5) = ss + 248#64 := by
    simpa only [wp_norm, arm64_norm] using hcsm1.1
  have hx20m1 : sm1.readReg64 (Reg.gpr 20#5) = 98#64 := by
    simpa only [wp_norm, arm64_norm] using hcsm1.2.1
  have hx21m1 : sm1.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tail.length := by
    simpa only [wp_norm, arm64_norm] using hcsm1.2.2.1
  have hx22m1 : sm1.readReg64 (Reg.gpr 22#5) = 1#64 := by
    simpa only [wp_norm, arm64_norm] using hcsm1.2.2.2.1
  have hx23m1 : sm1.readReg64 (Reg.gpr 23#5) = ss := by
    simpa only [wp_norm, arm64_norm] using hcsm1.2.2.2.2.1
  have hx24m1 : sm1.readReg64 (Reg.gpr 24#5) = bufRef := by
    simpa only [wp_norm, arm64_norm] using hcsm1.2.2.2.2.2.1
  have hx25m1 : sm1.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) := by
    simpa only [wp_norm, arm64_norm] using hcsm1.2.2.2.2.2.2.1
  have hx26m1 : sm1.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := by
    simpa only [wp_norm, arm64_norm] using hcsm1.2.2.2.2.2.2.2.1
  have hx27m1 : sm1.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
    simpa only [wp_norm, arm64_norm] using hcsm1.2.2.2.2.2.2.2.2.1
  have hx28m1 : sm1.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
    simpa only [wp_norm, arm64_norm] using hcsm1.2.2.2.2.2.2.2.2.2.1
  have hvregsm1 : calleeSavedVRegs sm1 = calleeSavedVRegs s0 := by
    simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hcsm1.2.2.2.2.2.2.2.2.2.2.2
  have hlen_b2 : restSpk.length = 1 + (encodeVarint (spk.signExtend 64)).length + tail.length := by
    simp only [restSpk, List.length_cons, List.length_append]; omega
  conv =>
    arg 4
    rw [show stackAt _ bytesMergeStackW = stackAt (s0.sp - 240#64) bytesMergeStackW by
          simp only [wp_norm, arm64_norm],
        sliceCursorAfter_bytes_gen_unfold_x9p slot (ptr + 2#64) hk restSpk,
        hlen_b2, show ptr + 2#64 + 34#64 = ptr + 36#64 by bv_lin]
    dsimp only [restSpk]
    rw [pointsToBytes_cons (a := ptr + 36#64), show ptr + 36#64 + 1#64 = ptr + 37#64 by bv_lin]
    simp only [sepConj_assoc]
  set stB := M.stepEvents (bytesMergeEvents 0 k.length) st
  apply sepWPp_seq_lsclro_vm hclm1 hrom1 (mid := lsmpl.base 8)
  by_vm_steps_withSvc (
    iterate 33 wp_step
    refine SepWP.done (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrunm1])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm4 hcl4 hro4
  rw [← A.pool_transport lim stB sm1 _ hvm4]
  refine sepWPp_call_lscl_15
    (x := (⟨.varint, ss + 288#64, bufRef, slot, ptr + 37#64,
      encodeVarint (spk.signExtend 64) ++ tail⟩, spk, tail))
    hcallI hcl4 hro4
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrunm1])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hspm1', hsp240, beq_self_eq_true])
    (by simp only [wp_norm, arm64_norm]; rfl)
    (by
      dsimp only [ProstVarintVm.int32MergeSomeSpecGen]
      apply entails_pure_sep_frame
      · refine ⟨?_, ?_, ?_, by rw [List.length_append]; omega, ?_⟩
        · simp only [wp_norm, arm64_norm]
        · simp only [wp_norm, arm64_norm, hx23m1]
        · simp only [wp_norm, arm64_norm, hx24m1]
        · rw [mergeUint32_encode_64_x9p, setWidth32_signExtend64_x9p]
      · apply entails_rw_stack_4 (sp2 := s0.sp - 240#64) (w2 := int32MergeStackW)
        · simp only [wp_norm, arm64_norm, hspm1']
        · rfl
        · apply entails_swap_stack_4 (int32Merge_to_bytesMerge_stack_mf14W (s0.sp - 240#64)).symm
          apply entails_frame_memRegion4
          rw [← sliceCursorAt_int32_gen_fold_x9p slot (ptr + 37#64) (spk.signExtend 64) tail]
          sep_frame)
    ?_
  intro sm2 hpcm2 hrunm2 hspm2 hcsm2 _hclm2 _hrom2
  dsimp only [ProstVarintVm.int32MergeSomeSpecGen]
  refine sepWPp_pure_left_and fun ⟨hx0m2, htrm2, hvmm2⟩ => ?_
  rw [← A.pool_transport lim stB _ sm2 hvmm2]
  try simp only [wp_norm, arm64_norm] at hpcm2
  have hx0m2' : sm2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0m2
  have hspm2' : sm2.sp = s0.sp - 240#64 := by
    simpa only [wp_norm, arm64_norm, hspm1'] using hspm2
  have htrm2' : sm2.trace = s0.trace := by
    simpa only [wp_norm, arm64_norm, htrm1'] using htrm2
  have hx21m2 : sm2.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tail.length := by
    simpa only [wp_norm, arm64_norm, hx21m1] using hcsm2.2.2.1
  have hx24m2 : sm2.readReg64 (Reg.gpr 24#5) = bufRef := by
    simpa only [wp_norm, arm64_norm, hx24m1] using hcsm2.2.2.2.2.2.1
  have hx26m2 : sm2.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := by
    simpa only [wp_norm, arm64_norm, hx26m1] using hcsm2.2.2.2.2.2.2.2.1
  have hx27m2 : sm2.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
    simpa only [wp_norm, arm64_norm, hx27m1] using hcsm2.2.2.2.2.2.2.2.2.1
  have hx28m2 : sm2.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
    simpa only [wp_norm, arm64_norm, hx28m1] using hcsm2.2.2.2.2.2.2.2.2.2.1
  have hvregsm2 : calleeSavedVRegs sm2 = calleeSavedVRegs s0 := by
    have h1 : calleeSavedVRegs sm2 = calleeSavedVRegs sm1 := by
      simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hcsm2.2.2.2.2.2.2.2.2.2.2.2
    exact h1.trans hvregsm1
  have htail_ult_self :
      BitVec.ult (BitVec.ofNat 64 tail.length) (BitVec.ofNat 64 tail.length) = false := by
    simp [BitVec.ult]
  have htail_ule_self :
      BitVec.ule (BitVec.ofNat 64 tail.length) (BitVec.ofNat 64 tail.length) = true := by
    simp [BitVec.ule]
  have hstk_i : 0x50 + (0x50 + decodeErrorHookStackW) = int32MergeStackW := rfl
  conv =>
    arg 4
    rw [hstk_i,
        show stackAt _ int32MergeStackW = stackAt (s0.sp - 240#64) int32MergeStackW by
          simp only [wp_norm, arm64_norm, hspm1'],
        sliceCursorAfter_int32_gen_unfold_x9p slot (ptr + 37#64) (spk.signExtend 64) tail]
  refine SepWPp.weaken_pre (P' :=
      vecU8FreshCap A.repAlloc (ss + 248#64) k ∗
        ((ss + 272#64) ↦₆₄ (w110 &&& 18446744069414584320#64 ||| 0#64)) ∗
        ((ss + 280#64) ↦₆₄ 0#64) ∗ ((ss + 288#64) ↦₃₂ spk) ∗
        memRegion (ss + 292#64) 4 ∗
        (ptr ↦₈ BitVec.ofNat 8 (36 + (encodeVarint (spk.signExtend 64)).length)) ∗
        ((ptr + 1#64) ↦₈ 18#8) ∗
        ((ptr + 2#64) ↦ₛ (33#8 :: k)) ∗
        ((ptr + 36#64) ↦₈ 24#8) ∗
        ((ptr + 37#64) ↦ₛ encodeVarint (spk.signExtend 64)) ∗
        ((ptr + 37#64 + BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length) ↦ₛ tail) ∗
        (bufRef ↦₆₄ slot) ∗
        (slot ↦₆₄ (ptr + 37#64 + BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length)) ∗
        ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
        A.pool lim stB sm2 ∗
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
        ((s0.sp - 56#64) ↦₆₄ s56) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
        memRegion (s0.sp - 240#64) 160 ∗
        stackAt (s0.sp - 240#64) mergeFieldSubStackX)
    (Entails.of_eq (by
      unfold vecU8FreshCap
      rw [stackAt_sub_to_int32Merge_mf14W (s0.sp - 240#64)]
      sep_ac_rfl)) ?_
  apply SepWPp.of_sepWP_ret
  apply sepWP_ret_vmPreserved
  by_vm_steps_withSvc (
    iterate 19 wp_step
    refine SepWP.done (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrunm2])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm_end
  rw [← A.pool_transport lim stB sm2 _ hvm_end]
  apply SepWP.done (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrunm2])
  refine ⟨by simp only [wp_norm, arm64_norm, hspm2'],
    by simp only [CalleeSavedPreserved, calleeSavedVRegs, wp_norm, arm64_norm,
      hx26m2, hx27m2, hx28m2, hvregsm2, and_self],
    by simp only [wp_norm, arm64_norm, htrm2'],
    by simp only [wp_norm, arm64_norm, hx0m2'], ?_⟩
  have hstk := stackAt_mergeField_fold_mf14W s0.sp
    (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
    (s0.readReg64 (Reg.gpr 25#5)) s56
    (s0.readReg64 (Reg.gpr 24#5)) (s0.readReg64 (Reg.gpr 23#5))
    (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
    (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5))
  have hp_post := pendingAt9PCap_post_fold_none A.repAlloc ss w110 k spk hpend' hpid' hspk'
  rw [← sliceCursorAfter_fold_spk_none_x9p slot ptr hk hspk tail]
  refine Entails.trans (Entails.of_eq ?_)
    (sepConj_mono hp_post (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hstk))))
  sep_ac_rfl

set_option maxHeartbeats 2400000 in
private theorem step_tag9_spk_some_mfb [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H)
    (ss bufRef slot ptr : BitVec 64) (vx vx' : SSGX)
    (i : BitVec 32) (k : List (BitVec 8)) (spk : BitVec 32)
    (hk : k.length = 33) (hspk : spk ≠ 0#32) (hp : vx.base.pending = none)
    (hpend' : vx'.base.pending = some k) (hpid' : vx'.ext.pid = some i)
    (hspk' : vx'.ext.spkId = spk)
    (tail : List (BitVec 8)) (st : M.σ) {s0 : State}
    (hpc : s0.pc = (blkPl_15).base) (hrun : s0.status = .Running)
    (hsp_align : s0.spAligned = true)
    (hcl : LibsignalCodeLoaded lsmpl s0.mem) (hro : LibsignalRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = ss)
    (hx1 : (s0.readReg64 .x1).setWidth 32 = 9#32)
    (hx2 : (s0.readReg64 .x2).setWidth 8 = 2#8)
    (hx3 : s0.readReg64 .x3 = bufRef)
    (hx4 : (s0.readReg64 .x4).setWidth 32 = 99#32)
    (hlen : ((GenFieldX.pendingSpk (some i) k spk).payload ++ tail).length < 2 ^ 62)
    (hfit : FitsEvents M lim st (bytesMergeAllocEvents 0 k.length)) :
    SepWPp (lsProg_15 H) (s0.readReg64 .lr) s0
      (pendingAt9PCap A.repAlloc ss vx ∗ (bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr ((GenFieldX.pendingSpk (some i) k spk).payload ++ tail) ∗
        A.pool lim st s0 ∗ stackAt s0.sp mergeFieldStackX)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace ∧
        sf.readReg64 .x0 = 0#64 ∧
        (Pf ⊢ pendingAt9PCap A.repAlloc ss vx' ∗ (bufRef ↦₆₄ slot) ∗
          sliceCursorAfter slot ptr ((GenFieldX.pendingSpk (some i) k spk).payload ++ tail) tail ∗
          A.pool lim (M.stepEvents (bytesMergeEvents 0 k.length) st) sf ∗
          stackAt s0.sp mergeFieldStackX))
      NoPanicPost := by
  have halign : s0.sp &&& 15#64 = 0#64 := by simpa [State.spAligned] using hsp_align
  have hsp240 := sp_sub_240_aligned_identityRootKeys halign
  have hcallI := int32_merge_some_placed_ok_cl (callerProg := lsProg_15 H)
    (errStack := decodeErrorHookStackW) (by decide)
  have hcallB := bytes_merge_fresh_budget_placed_okW_cl (callerProg := lsProg_15 H) hA
  have hm1 := encodeVarint_length_bounds_mf14 (i.setWidth 64)
  have hm2 := encodeVarint_length_bounds_mf14 (spk.signExtend 64)
  rw [List.length_append, pendingSpk_some_payload_length_x9p i hk hspk] at hlen
  have hx1_tr : BitVec.truncate 32 (s0.readReg64 .x1) = 9#32 := hx1
  have hx4_tr : BitVec.truncate 32 (s0.readReg64 .x4) = 99#32 := hx4
  have hx2_tr := wt_and_ff_eq_mf14W (s0.readReg64 .x2) hx2
  have hx2_64 := wt_and_ff_64_eq_mf14W (s0.readReg64 .x2) hx2
  have hl_ne0 := len_ne_zero_x9pW
    (a := 38 + (encodeVarint (i.setWidth 64)).length + (encodeVarint (spk.signExtend 64)).length)
    (n := tail.length) (by omega) hlen
  obtain ⟨hl_s1, hl_a1⟩ := sub1_and_add_neg1_x9pW
    (a := 38 + (encodeVarint (i.setWidth 64)).length + (encodeVarint (spk.signExtend 64)).length)
    (a' := 37 + (encodeVarint (i.setWidth 64)).length + (encodeVarint (spk.signExtend 64)).length)
    (n := tail.length) (by omega) hlen
  obtain ⟨hsubL, hultL, huleL⟩ := subs_body_len_x9pW
    (L := 37 + (encodeVarint (i.setWidth 64)).length + (encodeVarint (spk.signExtend 64)).length)
    (n := tail.length) (by omega)
  have hadd_negL := add_neg_body_len_mfb
    (L := 37 + (encodeVarint (i.setWidth 64)).length + (encodeVarint (spk.signExtend 64)).length)
    (n := tail.length) (by omega)
  obtain ⟨hl2_s1, hl2_a1⟩ := sub1_and_add_neg1_x9pW
    (a := 37 + (encodeVarint (i.setWidth 64)).length + (encodeVarint (spk.signExtend 64)).length)
    (a' := 36 + (encodeVarint (i.setWidth 64)).length + (encodeVarint (spk.signExtend 64)).length)
    (n := tail.length) (by omega) (by omega)
  obtain ⟨hult1, hule1, hult1', hsub1⟩ := cmp_gt_tail_x9pW
    (a := 37 + (encodeVarint (i.setWidth 64)).length + (encodeVarint (spk.signExtend 64)).length)
    (n := tail.length) (by omega) (by omega)
  obtain ⟨hl3_s1, hl3_a1⟩ := sub1_and_add_neg1_x9pW
    (a := 36 + (encodeVarint (spk.signExtend 64)).length)
    (a' := 35 + (encodeVarint (spk.signExtend 64)).length)
    (n := tail.length) (by omega) (by omega)
  obtain ⟨hult2, hule2, hult2', hsub2⟩ := cmp_gt_tail_x9pW
    (a := 36 + (encodeVarint (spk.signExtend 64)).length) (n := tail.length) (by omega) (by omega)
  obtain ⟨hl4_s1, hl4_a1⟩ := sub1_and_add_neg1_x9pW
    (a := 1 + (encodeVarint (spk.signExtend 64)).length)
    (a' := (encodeVarint (spk.signExtend 64)).length)
    (n := tail.length) (by omega) (by omega)
  obtain ⟨hult3, hule3, hult3', hsub3⟩ := cmp_gt_tail_x9pW
    (a := 1 + (encodeVarint (spk.signExtend 64)).length) (n := tail.length) (by omega) (by omega)
  conv =>
    arg 4
    rw [pendingAt9PCap_fresh_unfold A.repAlloc ss vx hp,
        sliceCursorAt_unfold_spk_some_x9p slot ptr i hk hspk tail]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun w100 => SepWPp.exists_elim fun w108 =>
    SepWPp.exists_elim fun w110 => SepWPp.exists_elim fun w118 =>
    SepWPp.exists_elim fun w120 => ?_
  conv =>
    arg 4
    rw [stackAt_mergeFieldX_unfold_x9pW s0.sp]
    simp only [sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun s80 => SepWPp.exists_elim fun s72 =>
    SepWPp.exists_elim fun s64 => SepWPp.exists_elim fun s56 =>
    SepWPp.exists_elim fun s48 => SepWPp.exists_elim fun s40 =>
    SepWPp.exists_elim fun s32 => SepWPp.exists_elim fun s24 =>
    SepWPp.exists_elim fun s16 => SepWPp.exists_elim fun s8 => ?_
  have hlsb := pid_disc_lsb_x9p w110
  simp only [arm64_norm] at hx0 hx1 hx2 hx3 hx4
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
  apply sepWPp_seq_lsclro_vm hcl1 hro1 (mid := (blkPl_15).base + 788#64)
  refine sepWP_intro_ro8_mfb (lsmpl.ρ mergeFieldRodataSym + 8#64) 181#8
    (fun hm => lsro8_intro hro1 (by lsro_addr) (by decide +kernel) hm) ?_
  by_vm_steps_withSvc (
    wp_steps
    apply sepWP_drop_left_mfb
    refine SepWP.done (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm2 hcl2 hro2
  rw [← A.pool_transport lim st _ _ hvm2]
  apply sepWPp_seq_lsclro_vm hcl2 hro2 (mid := lsmpl.base 8)
  by_vm_steps_withSvc (
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm3 hcl3 hro3
  rw [← A.pool_transport lim st _ _ hvm3]
  set restSpk := 24#8 :: (encodeVarint (spk.signExtend 64) ++ tail)
  set restAfterId := 18#8 :: (33#8 :: k ++ restSpk)
  have hlen_i1 : 36 + (encodeVarint (i.setWidth 64)).length +
      (encodeVarint (spk.signExtend 64)).length + tail.length =
      (encodeVarint (i.setWidth 64)).length + restAfterId.length := by
    simp only [restAfterId, restSpk, List.length_cons, List.length_append, hk]; omega
  conv =>
    arg 4
    rw [split_272_x9p ss, stackAt_sub_to_int32Merge_mf14W (s0.sp - 240#64)]
  refine sepWPp_call_lscl_15
    (x := (⟨.varint, ss + 276#64, bufRef, slot, ptr + 2#64,
      encodeVarint (i.setWidth 64) ++ restAfterId⟩, i, restAfterId))
    hcallI hcl3 hro3
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp240, beq_self_eq_true])
    (by simp only [wp_norm, arm64_norm]; rfl)
    (by
      dsimp only [ProstVarintVm.int32MergeSomeSpecGen]
      apply entails_pure_sep_frame
      · refine ⟨?_, ?_, ?_,
          by simp only [restAfterId, restSpk, List.length_append, List.length_cons, hk]; omega,
          ?_⟩
        · simp only [wp_norm, arm64_norm]
        · simp only [wp_norm, arm64_norm]
        · simp only [wp_norm, arm64_norm]
        · rw [mergeUint32_encode_64_x9p, setWidth32_setWidth64_x9p]
      · apply entails_frame_memRegion4
        apply entails_rw_stack_4 (sp2 := s0.sp - 240#64) (w2 := int32MergeStackW)
        · simp only [wp_norm, arm64_norm]
        · rfl
        · rw [show ((slot + 8#64) ↦₆₄ BitVec.ofNat 64
                  (36 + (encodeVarint (i.setWidth 64)).length +
                    (encodeVarint (spk.signExtend 64)).length + tail.length)) =
                ((slot + 8#64) ↦₆₄ BitVec.ofNat 64
                  ((encodeVarint (i.setWidth 64)).length + restAfterId.length)) by
                rw [hlen_i1],
              ← sliceCursorAt_int32_gen_fold_x9p slot (ptr + 2#64) (i.setWidth 64) restAfterId]
          sep_frame)
    ?_
  intro sm1 hpcm1 hrunm1 hspm1 hcsm1 hclm1 hrom1
  dsimp only [ProstVarintVm.int32MergeSomeSpecGen]
  refine sepWPp_pure_left_and fun ⟨hx0m1, htrm1, hvmm1⟩ => ?_
  rw [← A.pool_transport lim st _ sm1 hvmm1]
  try simp only [wp_norm, arm64_norm] at hpcm1
  have hspm1' : sm1.sp = s0.sp - 240#64 := by simpa only [wp_norm, arm64_norm] using hspm1
  have htrm1' : sm1.trace = s0.trace := by simpa only [wp_norm, arm64_norm] using htrm1
  have hx19m1 : sm1.readReg64 (Reg.gpr 19#5) = ss + 248#64 := by
    simpa only [wp_norm, arm64_norm] using hcsm1.1
  have hx20m1 : sm1.readReg64 (Reg.gpr 20#5) = 98#64 := by
    simpa only [wp_norm, arm64_norm] using hcsm1.2.1
  have hx21m1 : sm1.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tail.length := by
    simpa only [wp_norm, arm64_norm] using hcsm1.2.2.1
  have hx22m1 : sm1.readReg64 (Reg.gpr 22#5) = 1#64 := by
    simpa only [wp_norm, arm64_norm] using hcsm1.2.2.2.1
  have hx23m1 : sm1.readReg64 (Reg.gpr 23#5) = ss := by
    simpa only [wp_norm, arm64_norm] using hcsm1.2.2.2.2.1
  have hx24m1 : sm1.readReg64 (Reg.gpr 24#5) = bufRef := by
    simpa only [wp_norm, arm64_norm] using hcsm1.2.2.2.2.2.1
  have hx25m1 : sm1.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) := by
    simpa only [wp_norm, arm64_norm] using hcsm1.2.2.2.2.2.2.1
  have hx26m1 : sm1.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := by
    simpa only [wp_norm, arm64_norm] using hcsm1.2.2.2.2.2.2.2.1
  have hx27m1 : sm1.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
    simpa only [wp_norm, arm64_norm] using hcsm1.2.2.2.2.2.2.2.2.1
  have hx28m1 : sm1.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
    simpa only [wp_norm, arm64_norm] using hcsm1.2.2.2.2.2.2.2.2.2.1
  have hvregsm1 : calleeSavedVRegs sm1 = calleeSavedVRegs s0 := by
    simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hcsm1.2.2.2.2.2.2.2.2.2.2.2
  have hstk_i : 0x50 + (0x50 + decodeErrorHookStackW) = int32MergeStackW := rfl
  have hlen_i2 : restAfterId.length = 36 + (encodeVarint (spk.signExtend 64)).length + tail.length := by
    simp only [restAfterId, restSpk, List.length_cons, List.length_append, hk]; omega
  conv =>
    arg 4
    rw [hstk_i,
        show stackAt _ int32MergeStackW = stackAt (s0.sp - 240#64) int32MergeStackW by
          simp only [wp_norm, arm64_norm],
        sliceCursorAfter_int32_gen_unfold_x9p slot (ptr + 2#64) (i.setWidth 64) restAfterId,
        hlen_i2,
        show ptr + 2#64 + BitVec.ofNat 64 (encodeVarint (i.setWidth 64)).length =
          pendingPtr2 ptr i from rfl]
    dsimp only [restAfterId]
    rw [pointsToBytes_cons (a := pendingPtr2 ptr i)]
    simp only [sepConj_assoc]
  apply sepWPp_seq_lsclro_vm hclm1 hrom1 (mid := lsmpl.base 7)
  by_vm_steps_withSvc (
    iterate 35 wp_step
    refine SepWP.done (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrunm1])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm4 hcl4 hro4
  rw [← A.pool_transport lim st sm1 _ hvm4]
  have hlen_b1 : 35 + (encodeVarint (spk.signExtend 64)).length + tail.length =
      34 + restSpk.length := by
    simp only [restSpk, List.length_cons, List.length_append]; omega
  refine sepWPp_call_lscro_15
    (x := (⟨.lengthDelimited, ss + 248#64, 0#64, 1#64, [], bufRef, slot,
      pendingPtr2 ptr i + 1#64, 33#8 :: k ++ restSpk⟩, k, restSpk, st))
    hcallB hcl4 hro4
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrunm1])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hspm1', hsp240, beq_self_eq_true])
    (by simp only [wp_norm, arm64_norm]; rfl)
    (by
      dsimp only [bytesMergeFreshBudgetSpecW]
      apply entails_pure_sep_frame
      · refine ⟨?_, ?_, ?_,
          by simp only [restSpk, List.length_cons, List.length_append, hk]; omega,
          rfl, rfl, mergeBytes_k_x9p hk restSpk, hfit⟩
        · simp only [wp_norm, arm64_norm]
        · simp only [wp_norm, arm64_norm, hx19m1]
        · simp only [wp_norm, arm64_norm, hx24m1]
      · apply entails_rw_stack_5 (sp2 := s0.sp - 240#64) (w2 := bytesMergeStackW)
        · simp only [wp_norm, arm64_norm, hspm1']
        · rfl
        · apply entails_swap_stack_5 (int32Merge_to_bytesMerge_stack_mf14W (s0.sp - 240#64))
          rw [show ((slot + 8#64) ↦₆₄ BitVec.ofNat 64
                  (35 + (encodeVarint (spk.signExtend 64)).length + tail.length)) =
                ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (34 + restSpk.length)) by rw [hlen_b1],
              ← emptyVec_pending_eq_vecU8At_x9p A.repAlloc ss,
              ← sliceCursorAt_bytes_gen_fold_x9p slot (pendingPtr2 ptr i + 1#64) hk restSpk]
          sep_frame)
    ?_
  intro sm2 hpcm2 hrunm2 hspm2 hcsm2 hclm2 hrom2
  dsimp only [bytesMergeFreshBudgetSpecW]
  refine sepWPp_pure_left_and fun ⟨hx0m2, htrm2⟩ => ?_
  try simp only [wp_norm, arm64_norm] at hpcm2
  have hspm2' : sm2.sp = s0.sp - 240#64 := by
    simpa only [wp_norm, arm64_norm, hspm1'] using hspm2
  have htrm2' : sm2.trace = s0.trace := by
    simpa only [wp_norm, arm64_norm, htrm1'] using htrm2
  have hx19m2 : sm2.readReg64 (Reg.gpr 19#5) = ss + 248#64 := by
    simpa only [wp_norm, arm64_norm, hx19m1] using hcsm2.1
  have hx20m2 : sm2.readReg64 (Reg.gpr 20#5) = 98#64 := by
    simpa only [wp_norm, arm64_norm, hx20m1] using hcsm2.2.1
  have hx21m2 : sm2.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tail.length := by
    simpa only [wp_norm, arm64_norm, hx21m1] using hcsm2.2.2.1
  have hx22m2 : sm2.readReg64 (Reg.gpr 22#5) = 1#64 := by
    simpa only [wp_norm, arm64_norm, hx22m1] using hcsm2.2.2.2.1
  have hx23m2 : sm2.readReg64 (Reg.gpr 23#5) = ss := by
    simpa only [wp_norm, arm64_norm, hx23m1] using hcsm2.2.2.2.2.1
  have hx24m2 : sm2.readReg64 (Reg.gpr 24#5) = bufRef := by
    simpa only [wp_norm, arm64_norm, hx24m1] using hcsm2.2.2.2.2.2.1
  have hx25m2 : sm2.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) := by
    simpa only [wp_norm, arm64_norm, hx25m1] using hcsm2.2.2.2.2.2.2.1
  have hx26m2 : sm2.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := by
    simpa only [wp_norm, arm64_norm, hx26m1] using hcsm2.2.2.2.2.2.2.2.1
  have hx27m2 : sm2.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
    simpa only [wp_norm, arm64_norm, hx27m1] using hcsm2.2.2.2.2.2.2.2.2.1
  have hx28m2 : sm2.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
    simpa only [wp_norm, arm64_norm, hx28m1] using hcsm2.2.2.2.2.2.2.2.2.2.1
  have hvregsm2 : calleeSavedVRegs sm2 = calleeSavedVRegs s0 := by
    have h1 : calleeSavedVRegs sm2 = calleeSavedVRegs sm1 := by
      simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hcsm2.2.2.2.2.2.2.2.2.2.2.2
    exact h1.trans hvregsm1
  have hlen_b2 : restSpk.length = 1 + (encodeVarint (spk.signExtend 64)).length + tail.length := by
    simp only [restSpk, List.length_cons, List.length_append]; omega
  conv =>
    arg 4
    rw [show stackAt _ bytesMergeStackW = stackAt (s0.sp - 240#64) bytesMergeStackW by
          simp only [wp_norm, arm64_norm, hspm1'],
        sliceCursorAfter_bytes_gen_unfold_x9p slot (pendingPtr2 ptr i + 1#64) hk restSpk,
        hlen_b2, show pendingPtr2 ptr i + 1#64 + 34#64 = pendingPtr2 ptr i + 35#64 by bv_lin]
    dsimp only [restSpk]
    rw [pointsToBytes_cons (a := pendingPtr2 ptr i + 35#64),
        show pendingPtr2 ptr i + 35#64 + 1#64 = pendingPtr2 ptr i + 36#64 by bv_lin]
    simp only [sepConj_assoc]
  set stB := M.stepEvents (bytesMergeEvents 0 k.length) st
  apply sepWPp_seq_lsclro_vm hclm2 hrom2 (mid := lsmpl.base 8)
  by_vm_steps_withSvc (
    iterate 33 wp_step
    refine SepWP.done (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrunm2])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm5 hcl5 hro5
  rw [← A.pool_transport lim stB sm2 _ hvm5]
  refine sepWPp_call_lscl_15
    (x := (⟨.varint, ss + 288#64, bufRef, slot, pendingPtr2 ptr i + 36#64,
      encodeVarint (spk.signExtend 64) ++ tail⟩, spk, tail))
    hcallI hcl5 hro5
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrunm2])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hspm2', hsp240, beq_self_eq_true])
    (by simp only [wp_norm, arm64_norm]; rfl)
    (by
      dsimp only [ProstVarintVm.int32MergeSomeSpecGen]
      apply entails_pure_sep_frame
      · refine ⟨?_, ?_, ?_, by rw [List.length_append]; omega, ?_⟩
        · simp only [wp_norm, arm64_norm]
        · simp only [wp_norm, arm64_norm, hx23m2]
        · simp only [wp_norm, arm64_norm, hx24m2]
        · rw [mergeUint32_encode_64_x9p, setWidth32_signExtend64_x9p]
      · apply entails_rw_stack_4 (sp2 := s0.sp - 240#64) (w2 := int32MergeStackW)
        · simp only [wp_norm, arm64_norm, hspm2']
        · rfl
        · apply entails_swap_stack_4 (int32Merge_to_bytesMerge_stack_mf14W (s0.sp - 240#64)).symm
          apply entails_frame_memRegion4
          rw [← sliceCursorAt_int32_gen_fold_x9p slot (pendingPtr2 ptr i + 36#64)
                (spk.signExtend 64) tail]
          sep_frame)
    ?_
  intro sm3 hpcm3 hrunm3 hspm3 hcsm3 _hclm3 _hrom3
  dsimp only [ProstVarintVm.int32MergeSomeSpecGen]
  refine sepWPp_pure_left_and fun ⟨hx0m3, htrm3, hvmm3⟩ => ?_
  rw [← A.pool_transport lim stB _ sm3 hvmm3]
  try simp only [wp_norm, arm64_norm] at hpcm3
  have hx0m3' : sm3.readReg64 (Reg.gpr 0#5) = 0#64 := hx0m3
  have hspm3' : sm3.sp = s0.sp - 240#64 := by
    simpa only [wp_norm, arm64_norm, hspm2'] using hspm3
  have htrm3' : sm3.trace = s0.trace := by
    simpa only [wp_norm, arm64_norm, htrm2'] using htrm3
  have hx21m3 : sm3.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tail.length := by
    simpa only [wp_norm, arm64_norm, hx21m2] using hcsm3.2.2.1
  have hx24m3 : sm3.readReg64 (Reg.gpr 24#5) = bufRef := by
    simpa only [wp_norm, arm64_norm, hx24m2] using hcsm3.2.2.2.2.2.1
  have hx26m3 : sm3.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := by
    simpa only [wp_norm, arm64_norm, hx26m2] using hcsm3.2.2.2.2.2.2.2.1
  have hx27m3 : sm3.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
    simpa only [wp_norm, arm64_norm, hx27m2] using hcsm3.2.2.2.2.2.2.2.2.1
  have hx28m3 : sm3.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
    simpa only [wp_norm, arm64_norm, hx28m2] using hcsm3.2.2.2.2.2.2.2.2.2.1
  have hvregsm3 : calleeSavedVRegs sm3 = calleeSavedVRegs s0 := by
    have h1 : calleeSavedVRegs sm3 = calleeSavedVRegs sm2 := by
      simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hcsm3.2.2.2.2.2.2.2.2.2.2.2
    exact h1.trans hvregsm2
  have htail_ult_self :
      BitVec.ult (BitVec.ofNat 64 tail.length) (BitVec.ofNat 64 tail.length) = false := by
    simp [BitVec.ult]
  have htail_ule_self :
      BitVec.ule (BitVec.ofNat 64 tail.length) (BitVec.ofNat 64 tail.length) = true := by
    simp [BitVec.ule]
  have hstk_i2 : 0x50 + (0x50 + decodeErrorHookStackW) = int32MergeStackW := rfl
  conv =>
    arg 4
    rw [hstk_i2,
        show stackAt _ int32MergeStackW = stackAt (s0.sp - 240#64) int32MergeStackW by
          simp only [wp_norm, arm64_norm, hspm2'],
        sliceCursorAfter_int32_gen_unfold_x9p slot (pendingPtr2 ptr i + 36#64)
          (spk.signExtend 64) tail]
  refine SepWPp.weaken_pre (P' :=
      vecU8FreshCap A.repAlloc (ss + 248#64) k ∗
        ((ss + 272#64) ↦₃₂ 1#32) ∗ ((ss + 276#64) ↦₃₂ i) ∗
        ((ss + 280#64) ↦₆₄ 0#64) ∗ ((ss + 288#64) ↦₃₂ spk) ∗
        memRegion (ss + 292#64) 4 ∗
        (ptr ↦₈ BitVec.ofNat 8 (37 + (encodeVarint (i.setWidth 64)).length +
          (encodeVarint (spk.signExtend 64)).length)) ∗
        ((ptr + 1#64) ↦₈ 8#8) ∗
        ((ptr + 2#64) ↦ₛ encodeVarint (i.setWidth 64)) ∗
        (pendingPtr2 ptr i ↦₈ 18#8) ∗
        ((pendingPtr2 ptr i + 1#64) ↦ₛ (33#8 :: k)) ∗
        ((pendingPtr2 ptr i + 35#64) ↦₈ 24#8) ∗
        ((pendingPtr2 ptr i + 36#64) ↦ₛ encodeVarint (spk.signExtend 64)) ∗
        ((pendingPtr2 ptr i + 36#64 +
          BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length) ↦ₛ tail) ∗
        (bufRef ↦₆₄ slot) ∗
        (slot ↦₆₄ (pendingPtr2 ptr i + 36#64 +
          BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length)) ∗
        ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
        A.pool lim stB sm3 ∗
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
        ((s0.sp - 56#64) ↦₆₄ s56) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
        memRegion (s0.sp - 240#64) 160 ∗
        stackAt (s0.sp - 240#64) mergeFieldSubStackX)
    (Entails.of_eq (by
      unfold vecU8FreshCap
      rw [stackAt_sub_to_int32Merge_mf14W (s0.sp - 240#64)]
      sep_ac_rfl)) ?_
  apply SepWPp.of_sepWP_ret
  apply sepWP_ret_vmPreserved
  by_vm_steps_withSvc (
    iterate 19 wp_step
    refine SepWP.done (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrunm3])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm_end
  rw [← A.pool_transport lim stB sm3 _ hvm_end]
  apply SepWP.done (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrunm3])
  refine ⟨by simp only [wp_norm, arm64_norm, hspm3'],
    by simp only [CalleeSavedPreserved, calleeSavedVRegs, wp_norm, arm64_norm,
      hx26m3, hx27m3, hx28m3, hvregsm3, and_self],
    by simp only [wp_norm, arm64_norm, htrm3'],
    by simp only [wp_norm, arm64_norm, hx0m3'], ?_⟩
  have hstk := stackAt_mergeField_fold_mf14W s0.sp
    (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
    (s0.readReg64 (Reg.gpr 25#5)) s56
    (s0.readReg64 (Reg.gpr 24#5)) (s0.readReg64 (Reg.gpr 23#5))
    (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
    (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5))
  have hp_post := pendingAt9PCap_post_fold_some A.repAlloc ss i k spk hpend' hpid' hspk'
  rw [← sliceCursorAfter_fold_spk_some_x9p slot ptr i hk hspk tail]
  refine Entails.trans (Entails.of_eq ?_)
    (sepConj_mono hp_post (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hstk))))
  sep_ac_rfl


theorem mergeFieldBasic_tag9_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H) :
    subroutine_ok (lsProg_15 H) (blkPl_15).base
      (mergeFieldQBudgetSpecW M A lim (fun fl => fl.tag = 9)) := by
  apply subroutine_ok_of_field_sepWPp
  intro x capRecv st s0 hpc hrun hal hcl hro hx0 hx1 hx2 hx3 hx4 hP hOk hFr _hFrB hlen
    _hpow _hle _hcap62 hfit
  generalize x.fld = fld at hx1 hx2 hP hOk hFr hlen hfit ⊢
  cases fld with
  | base f =>
    cases f with
    | pending k =>
      have hk : k.length = 33 := hOk
      have hext : x.v.ext = ExtraGQ.empty := hFr.1
      have hp : x.v.toSSGX.base.pending = none := hFr.2
      refine ⟨pendingAt9PCap A.repAlloc x.ss x.v.toSSGX,
        pendingAt9PCap A.repAlloc x.ss (x.v.apply (.base (.pending k))).toSSGX,
        prostSSGQRest_pending A.repAlloc x.ss capRecv x.v, ?_, ?_, ?_⟩
      · unfold prostSSGQAtCap prostSSGQRest_pending prostSSGQScalars
        exact Entails.of_eq (by sep_ac_rfl)
      · unfold prostSSGQAtCap nextCapRecv SSGQ.apply SSG.apply prostSSGQRest_pending prostSSGQScalars
        dsimp only
        exact Entails.of_eq (by sep_ac_rfl)
      · exact step_tag9_pending_mfb hA x.ss x.bufRef x.slot x.ptr
          x.v.toSSGX (x.v.apply (.base (.pending k))).toSSGX k hk hp
          rfl (by simp [SSGQ.apply, SSGQ.toSSGX, hext, ExtraGQ.empty, ExtraGQ.toExtraG])
          (by simp [SSGQ.apply, SSGQ.toSSGX, hext, ExtraGQ.empty, ExtraGQ.toExtraG])
          x.tail st hpc hrun hal hcl hro hx0 hx1 hx2 hx3 hx4 hlen hfit
    | _ => simp [GenFieldQ.tag, GenField.tag] at hP
  | pendingId i k =>
    have hk : k.length = 33 := hOk
    have hp : x.v.toSSGX.base.pending = none := hFr.1
    have hext : x.v.ext = ExtraGQ.empty := hFr.2
    refine ⟨pendingAt9PCap A.repAlloc x.ss x.v.toSSGX,
      pendingAt9PCap A.repAlloc x.ss (x.v.apply (.pendingId i k)).toSSGX,
      prostSSGQRest_pending A.repAlloc x.ss capRecv x.v, ?_, ?_, ?_⟩
    · unfold prostSSGQAtCap prostSSGQRest_pending prostSSGQScalars
      exact Entails.of_eq (by sep_ac_rfl)
    · unfold prostSSGQAtCap nextCapRecv SSGQ.apply prostSSGQRest_pending prostSSGQScalars
      dsimp only
      exact Entails.of_eq (by sep_ac_rfl)
    · exact step_tag9_id_mfb hA x.ss x.bufRef x.slot x.ptr
        x.v.toSSGX (x.v.apply (.pendingId i k)).toSSGX i k hk hp
        rfl rfl (by simp [SSGQ.apply, SSGQ.toSSGX, hext, ExtraGQ.empty, ExtraGQ.toExtraG])
        x.tail st hpc hrun hal hcl hro hx0 hx1 hx2 hx3 hx4 hlen hfit
  | pendingSpk o k spk =>
    obtain ⟨hk, hspk⟩ := hOk
    have hp : x.v.toSSGX.base.pending = none := hFr.1
    refine ⟨pendingAt9PCap A.repAlloc x.ss x.v.toSSGX,
      pendingAt9PCap A.repAlloc x.ss (x.v.apply (.pendingSpk o k spk)).toSSGX,
      prostSSGQRest_pending A.repAlloc x.ss capRecv x.v, ?_, ?_, ?_⟩
    · unfold prostSSGQAtCap prostSSGQRest_pending prostSSGQScalars
      exact Entails.of_eq (by sep_ac_rfl)
    · unfold prostSSGQAtCap nextCapRecv SSGQ.apply prostSSGQRest_pending prostSSGQScalars
      dsimp only
      exact Entails.of_eq (by sep_ac_rfl)
    · cases o with
      | none =>
        exact step_tag9_spk_none_mfb hA x.ss x.bufRef x.slot x.ptr
          x.v.toSSGX (x.v.apply (.pendingSpk none k spk)).toSSGX k spk hk hspk hp
          rfl rfl rfl x.tail st hpc hrun hal hcl hro hx0 hx1 hx2 hx3 hx4 hlen hfit
      | some i =>
        exact step_tag9_spk_some_mfb hA x.ss x.bufRef x.slot x.ptr
          x.v.toSSGX (x.v.apply (.pendingSpk (some i) k spk)).toSSGX i k spk hk hspk hp
          rfl rfl rfl x.tail st hpc hrun hal hcl hro hx0 hx1 hx2 hx3 hx4 hlen hfit
  | _ => simp [GenFieldQ.tag] at hP

/-! ## 5. Group D (`PendingKyberPreKey` Tag `14`: `.kyber 0#32 ct` and `.kyber i ct`) -/

private theorem kyberAt14Cap_none_unfold (A : RustAlloc) (ss : BitVec 64)
    (kyber : Option (BitVec 32 × List (BitVec 8))) (hk : kyber = none) :
    kyberAt14Cap A ss kyber =
      ((ss + 0x128#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      (∃∗ w130 : BitVec 64, (ss + 0x130#64) ↦₆₄ w130) ∗
      (∃∗ w138 : BitVec 64, (ss + 0x138#64) ↦₆₄ w138) ∗
      (∃∗ w140 : BitVec 32, (ss + 0x140#64) ↦₃₂ w140) ∗
      memRegion (ss + 0x144#64) 4 := by
  unfold kyberAt14Cap
  rw [hk, memRegion_24_split_kyber ss]
  dsimp only [noneCap]

private theorem kyberAt14Cap_some_fold (A : RustAlloc) (ss : BitVec 64)
    (i : BitVec 32) (ct : List (BitVec 8)) :
    vecU8FreshCap A (ss + 296#64) ct ∗
      ((ss + 320#64) ↦₃₂ i) ∗ memRegion (ss + 324#64) 4 ⊢
      kyberAt14Cap A ss (some (i, ct)) := by
  unfold kyberAt14Cap
  have ha0 : ss + 296#64 = ss + 0x128#64 := rfl
  have ha1 : ss + 320#64 = ss + 0x140#64 := rfl
  have ha2 : ss + 324#64 = ss + 0x144#64 := rfl
  rw [ha0, ha1, ha2]
  exact Entails.of_eq (by sep_ac_rfl)

set_option maxHeartbeats 1600000 in
private theorem step_tag14_kyber_0_mfb [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H)
    (ss bufRef slot ptr : BitVec 64)
    (kyber : Option (BitVec 32 × List (BitVec 8))) (ct : List (BitVec 8))
    (hct : ct.length = 1569) (hk : kyber = none)
    (tail : List (BitVec 8)) (st : M.σ) {s0 : State}
    (hpc : s0.pc = (blkPl_15).base) (hrun : s0.status = .Running)
    (hsp_align : s0.spAligned = true)
    (hcl : LibsignalCodeLoaded lsmpl s0.mem) (hro : LibsignalRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = ss)
    (hx1 : (s0.readReg64 .x1).setWidth 32 = 14#32)
    (hx2 : (s0.readReg64 .x2).setWidth 8 = 2#8)
    (hx3 : s0.readReg64 .x3 = bufRef)
    (hx4 : (s0.readReg64 .x4).setWidth 32 = 99#32)
    (hlen : ((GenFieldX.kyber 0#32 ct).payload ++ tail).length < 2 ^ 62)
    (hfit : FitsEvents M lim st (bytesMergeAllocEvents 0 ct.length)) :
    SepWPp (lsProg_15 H) (s0.readReg64 .lr) s0
      (kyberAt14Cap A.repAlloc ss kyber ∗ (bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr ((GenFieldX.kyber 0#32 ct).payload ++ tail) ∗
        A.pool lim st s0 ∗ stackAt s0.sp mergeFieldStackX)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace ∧
        sf.readReg64 .x0 = 0#64 ∧
        (Pf ⊢ kyberAt14Cap A.repAlloc ss (some (0#32, ct)) ∗ (bufRef ↦₆₄ slot) ∗
          sliceCursorAfter slot ptr ((GenFieldX.kyber 0#32 ct).payload ++ tail) tail ∗
          A.pool lim (M.stepEvents (bytesMergeEvents 0 ct.length) st) sf ∗
          stackAt s0.sp mergeFieldStackX))
      NoPanicPost := by
  have halign : s0.sp &&& 15#64 = 0#64 := by simpa [State.spAligned] using hsp_align
  have hsp240 := sp_sub_240_aligned_identityRootKeys halign
  have hcallD := decode_varint_slice_some_placed_ok_cl (callerProg := lsProg_15 H)
    (errStack := decodeErrorHookStackW) (by decide)
  have hcallB := bytes_merge_fresh_budget_placed_okW_cl (callerProg := lsProg_15 H) hA
  rw [kyber_payload_tail_length hct] at hlen
  have hx1_tr : BitVec.truncate 32 (s0.readReg64 .x1) = 14#32 := hx1
  have hx4_tr : BitVec.truncate 32 (s0.readReg64 .x4) = 99#32 := hx4
  have hx2_tr := wt_and_ff_eq_mf14W (s0.readReg64 .x2) hx2
  have hx2_64 := wt_and_ff_64_eq_mf14W (s0.readReg64 .x2) hx2
  have hL_ne0 : (BitVec.ofNat 64 (1574 + tail.length) == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; intro heq
    have h1 := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_ofNat] at h1; omega
  have hL_ule10 : BitVec.ule (BitVec.ofNat 64 (1574 + tail.length)) 10#64 = false := by
    simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  have hL_ult10 : BitVec.ult 10#64 (BitVec.ofNat 64 (1574 + tail.length)) = true := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
  conv =>
    arg 4
    rw [kyberAt14Cap_none_unfold A.repAlloc ss kyber hk,
        sliceCursorAt_kyber_unfold_mf14 slot ptr hct tail,
        bytes_kyber_split_mf14]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun w130 => SepWPp.exists_elim fun w138 =>
    SepWPp.exists_elim fun w140 => ?_
  conv =>
    arg 4
    rw [stackAt_mergeField_unfold_mf14W s0.sp]
    simp only [sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun s80 => SepWPp.exists_elim fun s72 =>
    SepWPp.exists_elim fun s64 => SepWPp.exists_elim fun s56 =>
    SepWPp.exists_elim fun s48 => SepWPp.exists_elim fun s40 =>
    SepWPp.exists_elim fun s32 => SepWPp.exists_elim fun s24 =>
    SepWPp.exists_elim fun s16 => SepWPp.exists_elim fun s8 => ?_
  simp only [arm64_norm] at hx0 hx1 hx2 hx3 hx4
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
  apply sepWPp_seq_lsclro_vm hcl1 hro1 (mid := (blkPl_15).base + 368#64)
  refine sepWP_intro_ro8_mfb (lsmpl.ρ mergeFieldRodataSym + 13#64) 0x4c#8
    (fun hm => lsro8_intro hro1 (by lsro_addr) (by decide +kernel) hm) ?_
  by_vm_steps_withSvc (
    wp_steps
    apply sepWP_drop_left_mfb
    refine SepWP.done (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm2 hcl2 hro2
  rw [← A.pool_transport lim st _ _ hvm2]
  apply sepWPp_seq_lsclro_vm hcl2 hro2 (mid := lsmpl.base 76)
  by_vm_steps_withSvc (
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm3 hcl3 hro3
  rw [← A.pool_transport lim st _ _ hvm3]
  set bsD := 164#8 :: 12#8 :: 18#8 :: innerBytes ct tail
  refine sepWPp_call_lscl_15
    (x := (⟨s0.sp - 232#64, ptr, bsD⟩, BitVec.ofNat 64 1572, 18#8 :: innerBytes ct tail))
    hcallD hcl3 hro3
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp240, beq_self_eq_true])
    (by simp only [wp_norm, arm64_norm]; rfl)
    (by
      dsimp only [ProstVarintVm.decodeVarintSliceSomeSpecGen]
      apply entails_pure_sep_frame
      · refine ⟨?_, ?_, ?_,
          by simp only [bsD, List.length_cons, innerBytes_length hct]; omega,
          Or.inl (by simp only [bsD, List.length_cons, innerBytes_length hct]; omega),
          decodeVarint_kyber tail⟩
        · simp only [wp_norm, arm64_norm]
        · simp only [wp_norm, arm64_norm]
        · simp only [wp_norm, arm64_norm, bsD, List.length_cons, innerBytes_length hct,
            BitVec.toNat_ofNat]; omega
      · apply entails_rw_stack_3 (sp2 := s0.sp - 240#64) (w2 := decodeVarintSliceStackW)
        · simp only [wp_norm, arm64_norm]
        · rfl
        · dsimp only [bsD]
          rw [bytes_kyber_split_mf14]
          sep_frame)
    ?_
  intro sm1 hpcm1 hrunm1 hspm1 hcsm1 hclm1 hrom1
  dsimp only [ProstVarintVm.decodeVarintSliceSomeSpecGen]
  refine sepWPp_pure_left_and fun ⟨htrm1, hvmm1⟩ => ?_
  rw [← A.pool_transport lim st _ sm1 hvmm1]
  try simp only [wp_norm, arm64_norm] at hpcm1
  have hspm1' : sm1.sp = s0.sp - 240#64 := by simpa only [wp_norm, arm64_norm] using hspm1
  have htrm1' : sm1.trace = s0.trace := by simpa only [wp_norm, arm64_norm] using htrm1
  have hx19m1 : sm1.readReg64 (Reg.gpr 19#5) = slot := by
    simpa only [wp_norm, arm64_norm] using hcsm1.1
  have hx20m1 : sm1.readReg64 (Reg.gpr 20#5) = 99#64 := by
    simpa only [wp_norm, arm64_norm] using hcsm1.2.1
  have hx21m1 : sm1.readReg64 (Reg.gpr 21#5) = ss := by
    simpa only [wp_norm, arm64_norm] using hcsm1.2.2.1
  have hx22m1 : sm1.readReg64 (Reg.gpr 22#5) = bufRef := by
    simpa only [wp_norm, arm64_norm] using hcsm1.2.2.2.1
  have hx26m1 : sm1.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := by
    simpa only [wp_norm, arm64_norm] using hcsm1.2.2.2.2.2.2.2.1
  have hx27m1 : sm1.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
    simpa only [wp_norm, arm64_norm] using hcsm1.2.2.2.2.2.2.2.2.1
  have hx28m1 : sm1.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
    simpa only [wp_norm, arm64_norm] using hcsm1.2.2.2.2.2.2.2.2.2.1
  have hvregsm1 : calleeSavedVRegs sm1 = calleeSavedVRegs s0 := by
    simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hcsm1.2.2.2.2.2.2.2.2.2.2.2
  have hstk_d : 0x50 + decodeErrorHookStackW = decodeVarintSliceStackW := rfl
  have hsub_d : bsD.length - (18#8 :: innerBytes ct tail).length = 2 := by
    simp only [bsD, List.length_cons]; omega
  conv =>
    arg 4
    rw [hstk_d, hsub_d,
        show stackAt _ decodeVarintSliceStackW = stackAt (s0.sp - 240#64) decodeVarintSliceStackW by
          simp only [wp_norm, arm64_norm],
        pointsTo64_zero_split32_mf14 s0.sp,
        show s0.sp - 232#64 + 8#64 = s0.sp - 224#64 by bv_lin,
        show s0.sp - 232#64 + 16#64 = s0.sp - 216#64 by bv_lin]
    dsimp only [bsD]
    rw [bytes_kyber_split_mf14]
    simp only [sepConj_assoc]
  have hc_ult2 : BitVec.ult (BitVec.ofNat 64 (1574 + tail.length)) 2#64 = false := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  have hc_sub2 : BitVec.ofNat 64 (1574 + tail.length) - 2#64 =
      BitVec.ofNat 64 (1572 + tail.length) := len_sub_mf14W (by omega) (by omega)
  have hc_ult1572 : BitVec.ult (BitVec.ofNat 64 (1572 + tail.length)) 1572#64 = false := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  have hc_sub1572 : BitVec.ofNat 64 (1572 + tail.length) - 1572#64 =
      BitVec.ofNat 64 tail.length := by
    simpa using len_sub_mf14W (a := 1572) (b := 1572) (n := tail.length) (by omega) (by omega)
  have hc_ule1572 : BitVec.ule 1572#64 (BitVec.ofNat 64 (1572 + tail.length)) = true := by
    simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
  have hc_ule_n2 : BitVec.ule (BitVec.ofNat 64 tail.length)
      (BitVec.ofNat 64 (1572 + tail.length)) = true := by
    simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
  have hc_ult_n : BitVec.ult (BitVec.ofNat 64 tail.length)
      (BitVec.ofNat 64 (1572 + tail.length)) = true := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
  have hc_ult_n2 : BitVec.ult (BitVec.ofNat 64 (1572 + tail.length))
      (BitVec.ofNat 64 tail.length) = false := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  have hc_ule_n : BitVec.ule (BitVec.ofNat 64 (1572 + tail.length))
      (BitVec.ofNat 64 tail.length) = false := by
    simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  have hc_eq_n : (BitVec.ofNat 64 (1572 + tail.length) == BitVec.ofNat 64 tail.length) = false := by
    rw [beq_eq_false_iff_ne]; intro heq
    have h1 := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_ofNat] at h1; omega
  have hc_sub1 : BitVec.ofNat 64 (1572 + tail.length) - 1#64 =
      BitVec.ofNat 64 (1571 + tail.length) := len_sub_mf14W (by omega) (by omega)
  apply sepWPp_seq_lsclro_vm hclm1 hrom1 (mid := lsmpl.base 7)
  by_vm_steps_withSvc (
    iterate 47 wp_step
    refine SepWP.done (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrunm1])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm4 hcl4 hro4
  rw [← A.pool_transport lim st sm1 _ hvm4]
  refine sepWPp_call_lscro_15
    (x := (⟨.lengthDelimited, ss + 296#64, 0#64, 1#64, [], bufRef, slot,
      ptr + 3#64, innerBytes ct tail⟩, ct, tail, st))
    hcallB hcl4 hro4
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrunm1])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hspm1', hsp240, beq_self_eq_true])
    (by simp only [wp_norm, arm64_norm]; rfl)
    (by
      dsimp only [bytesMergeFreshBudgetSpecW]
      apply entails_pure_sep_frame
      · refine ⟨?_, ?_, ?_, by rw [innerBytes_length hct]; omega,
          rfl, rfl, mergeBytes_inner hct tail, hfit⟩
        · simp only [wp_norm, arm64_norm]
        · simp only [wp_norm, arm64_norm, hx21m1]
        · simp only [wp_norm, arm64_norm, hx22m1]
      · apply entails_rw_stack_5 (sp2 := s0.sp - 240#64) (w2 := bytesMergeStackW)
        · simp only [wp_norm, arm64_norm, hspm1']
        · rfl
        · apply entails_swap_stack_5 (decode_to_bytesMerge_stack_mf14W (s0.sp - 240#64))
          rw [← emptyVec_kyber_eq_vecU8At A.repAlloc ss,
              ← sliceCursorAt_inner_fold_mf14 slot ptr hct tail]
          sep_frame)
    ?_
  intro sm2 hpcm2 hrunm2 hspm2 hcsm2 _hclm2 _hrom2
  dsimp only [bytesMergeFreshBudgetSpecW]
  refine sepWPp_pure_left_and fun ⟨hx0m2, htrm2⟩ => ?_
  try simp only [wp_norm, arm64_norm] at hpcm2
  have hx0m2' : sm2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0m2
  have hspm2' : sm2.sp = s0.sp - 240#64 := by
    simpa only [wp_norm, arm64_norm, hspm1'] using hspm2
  have htrm2' : sm2.trace = s0.trace := by
    simpa only [wp_norm, arm64_norm, htrm1'] using htrm2
  have hx21m2 : sm2.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tail.length := by
    simpa only [wp_norm, arm64_norm] using hcsm2.2.2.1
  have hx22m2 : sm2.readReg64 (Reg.gpr 22#5) = bufRef := by
    simpa only [wp_norm, arm64_norm, hx22m1] using hcsm2.2.2.2.1
  have hx26m2 : sm2.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := by
    simpa only [wp_norm, arm64_norm, hx26m1] using hcsm2.2.2.2.2.2.2.2.1
  have hx27m2 : sm2.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
    simpa only [wp_norm, arm64_norm, hx27m1] using hcsm2.2.2.2.2.2.2.2.2.1
  have hx28m2 : sm2.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
    simpa only [wp_norm, arm64_norm, hx28m1] using hcsm2.2.2.2.2.2.2.2.2.2.1
  have hvregsm2 : calleeSavedVRegs sm2 = calleeSavedVRegs s0 := by
    have h1 : calleeSavedVRegs sm2 = calleeSavedVRegs sm1 := by
      simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hcsm2.2.2.2.2.2.2.2.2.2.2.2
    exact h1.trans hvregsm1
  have htail_ult_self :
      BitVec.ult (BitVec.ofNat 64 tail.length) (BitVec.ofNat 64 tail.length) = false := by
    simp [BitVec.ult]
  have htail_ule_self :
      BitVec.ule (BitVec.ofNat 64 tail.length) (BitVec.ofNat 64 tail.length) = true := by
    simp [BitVec.ule]
  conv =>
    arg 4
    rw [show stackAt _ bytesMergeStackW = stackAt (s0.sp - 240#64) bytesMergeStackW by
          simp only [wp_norm, arm64_norm, hspm1'],
        sliceCursorAfter_inner_unfold_mf14 slot ptr hct tail]
  set stB := M.stepEvents (bytesMergeEvents 0 ct.length) st
  refine SepWPp.weaken_pre (P' :=
      vecU8FreshCap A.repAlloc (ss + 296#64) ct ∗
        ((ss + 320#64) ↦₃₂ 0#32) ∗ memRegion (ss + 324#64) 4 ∗
        (ptr ↦₈ 164#8) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 18#8) ∗
        ((ptr + 3#64) ↦ₛ innerBytes ct tail) ∗
        (bufRef ↦₆₄ slot) ∗
        (slot ↦₆₄ (ptr + 1574#64)) ∗
        ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
        A.pool lim stB sm2 ∗
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
        ((s0.sp - 56#64) ↦₆₄ s56) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
        memRegion (s0.sp - 240#64) 8 ∗
        ((s0.sp - 232#64) ↦₃₂ 0#32) ∗ ((s0.sp - 228#64) ↦₃₂ 0#32) ∗
        ((s0.sp - 224#64) ↦₆₄ BitVec.ofNat 64 1572) ∗ ((s0.sp - 216#64) ↦₆₄ 2#64) ∗
        memRegion (s0.sp - 208#64) 128 ∗
        stackAt (s0.sp - 240#64) mergeFieldSubStackX)
    (Entails.of_eq (by
      unfold vecU8FreshCap
      rw [stackAt_sub_to_bytesMerge_mf14W (s0.sp - 240#64)]
      sep_ac_rfl)) ?_
  apply SepWPp.of_sepWP_ret
  apply sepWP_ret_vmPreserved
  by_vm_steps_withSvc (
    iterate 19 wp_step
    refine SepWP.done (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrunm2])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm_end
  rw [← A.pool_transport lim stB sm2 _ hvm_end]
  apply SepWP.done (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrunm2])
  refine ⟨by simp only [wp_norm, arm64_norm, hspm2'],
    by simp only [CalleeSavedPreserved, calleeSavedVRegs, wp_norm, arm64_norm,
      hx26m2, hx27m2, hx28m2, hvregsm2, and_self],
    by simp only [wp_norm, arm64_norm, htrm2'],
    by simp only [wp_norm, arm64_norm, hx0m2'], ?_⟩
  have hmem160 :
      memRegion (s0.sp - 240#64) 8 ∗
        (((s0.sp - 232#64) ↦₃₂ 0#32) ∗ ((s0.sp - 228#64) ↦₃₂ 0#32) ∗
          ((s0.sp - 224#64) ↦₆₄ BitVec.ofNat 64 1572) ∗ ((s0.sp - 216#64) ↦₆₄ 2#64)) ∗
        memRegion (s0.sp - 208#64) 128 ⊢
      memRegion (s0.sp - 240#64) 160 := by
    rw [← memRegion160_fold_mf14 s0.sp]
    exact sepConj_mono_right (sepConj_mono_left
      (cells24_entails_memRegion24_mf14 s0.sp (BitVec.ofNat 64 1572) 2#64))
  have hstk :
      ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
        ((s0.sp - 56#64) ↦₆₄ s56) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
        (memRegion (s0.sp - 240#64) 8 ∗
          (((s0.sp - 232#64) ↦₃₂ 0#32) ∗ ((s0.sp - 228#64) ↦₃₂ 0#32) ∗
            ((s0.sp - 224#64) ↦₆₄ BitVec.ofNat 64 1572) ∗ ((s0.sp - 216#64) ↦₆₄ 2#64)) ∗
          memRegion (s0.sp - 208#64) 128) ∗
        stackAt (s0.sp - 240#64) mergeFieldSubStackX ⊢
      stackAt s0.sp mergeFieldStackX := by
    refine Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (Entails.trans (sepConj_mono_left hmem160) ?_)
    refine Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (stackAt_mergeField_fold_mf14W s0.sp
        (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
        (s0.readReg64 (Reg.gpr 25#5)) s56
        (s0.readReg64 (Reg.gpr 24#5)) (s0.readReg64 (Reg.gpr 23#5))
        (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
        (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5)))
  have hp_post := kyberAt14Cap_some_fold A.repAlloc ss 0#32 ct
  rw [← sliceCursorAfter_kyber_fold_mf14 slot ptr hct tail]
  refine Entails.trans (Entails.of_eq ?_)
    (sepConj_mono hp_post (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hstk))))
  sep_ac_rfl

set_option maxHeartbeats 2400000 in
private theorem step_tag14_kyber_ne_mfb [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H)
    (ss bufRef slot ptr : BitVec 64)
    (kyber : Option (BitVec 32 × List (BitVec 8))) (i : BitVec 32) (ct : List (BitVec 8))
    (hi : i ≠ 0#32) (hct : ct.length = 1569) (hk : kyber = none)
    (tail : List (BitVec 8)) (st : M.σ) {s0 : State}
    (hpc : s0.pc = (blkPl_15).base) (hrun : s0.status = .Running)
    (hsp_align : s0.spAligned = true)
    (hcl : LibsignalCodeLoaded lsmpl s0.mem) (hro : LibsignalRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = ss)
    (hx1 : (s0.readReg64 .x1).setWidth 32 = 14#32)
    (hx2 : (s0.readReg64 .x2).setWidth 8 = 2#8)
    (hx3 : s0.readReg64 .x3 = bufRef)
    (hx4 : (s0.readReg64 .x4).setWidth 32 = 99#32)
    (hlen : ((GenFieldX.kyber i ct).payload ++ tail).length < 2 ^ 62)
    (hfit : FitsEvents M lim st (bytesMergeAllocEvents 0 ct.length)) :
    SepWPp (lsProg_15 H) (s0.readReg64 .lr) s0
      (kyberAt14Cap A.repAlloc ss kyber ∗ (bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr ((GenFieldX.kyber i ct).payload ++ tail) ∗
        A.pool lim st s0 ∗ stackAt s0.sp mergeFieldStackX)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace ∧
        sf.readReg64 .x0 = 0#64 ∧
        (Pf ⊢ kyberAt14Cap A.repAlloc ss (some (i, ct)) ∗ (bufRef ↦₆₄ slot) ∗
          sliceCursorAfter slot ptr ((GenFieldX.kyber i ct).payload ++ tail) tail ∗
          A.pool lim (M.stepEvents (bytesMergeEvents 0 ct.length) st) sf ∗
          stackAt s0.sp mergeFieldStackX))
      NoPanicPost := by
  have halign : s0.sp &&& 15#64 = 0#64 := by simpa [State.spAligned] using hsp_align
  have hsp240 := sp_sub_240_aligned_identityRootKeys halign
  have hcallD := decode_varint_slice_some_placed_ok_cl (callerProg := lsProg_15 H)
    (errStack := decodeErrorHookStackW) (by decide)
  have hcallI := int32_merge_some_placed_ok_cl (callerProg := lsProg_15 H)
    (errStack := decodeErrorHookStackW) (by decide)
  have hcallB := bytes_merge_fresh_budget_placed_okW_cl (callerProg := lsProg_15 H) hA
  have hm_bounds := encodeVarint_length_bounds_mf14 (i.setWidth 64)
  rw [kyber_ne_payload_tail_length hi hct] at hlen
  have hx1_tr : BitVec.truncate 32 (s0.readReg64 .x1) = 14#32 := hx1
  have hx4_tr : BitVec.truncate 32 (s0.readReg64 .x4) = 99#32 := hx4
  have hx2_tr := wt_and_ff_eq_mf14W (s0.readReg64 .x2) hx2
  have hx2_64 := wt_and_ff_64_eq_mf14W (s0.readReg64 .x2) hx2
  have hL_ne0 : (BitVec.ofNat 64 (1575 + (encodeVarint (i.setWidth 64)).length +
      tail.length) == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; intro heq
    have h1 := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_ofNat] at h1; omega
  have hL_ule10 : BitVec.ule (BitVec.ofNat 64 (1575 + (encodeVarint (i.setWidth 64)).length +
      tail.length)) 10#64 = false := by
    simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  have hL_ult10 : BitVec.ult 10#64 (BitVec.ofNat 64 (1575 +
      (encodeVarint (i.setWidth 64)).length + tail.length)) = true := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
  conv =>
    arg 4
    rw [kyberAt14Cap_none_unfold A.repAlloc ss kyber hk,
        sliceCursorAt_kyber_ne_unfold_mf14 slot ptr hi hct tail,
        bytes_kyber_ne_split_mf14]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun w130 => SepWPp.exists_elim fun w138 =>
    SepWPp.exists_elim fun w140 => ?_
  conv =>
    arg 4
    rw [stackAt_mergeField_unfold_mf14W s0.sp]
    simp only [sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun s80 => SepWPp.exists_elim fun s72 =>
    SepWPp.exists_elim fun s64 => SepWPp.exists_elim fun s56 =>
    SepWPp.exists_elim fun s48 => SepWPp.exists_elim fun s40 =>
    SepWPp.exists_elim fun s32 => SepWPp.exists_elim fun s24 =>
    SepWPp.exists_elim fun s16 => SepWPp.exists_elim fun s8 => ?_
  simp only [arm64_norm] at hx0 hx1 hx2 hx3 hx4
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
  apply sepWPp_seq_lsclro_vm hcl1 hro1 (mid := (blkPl_15).base + 368#64)
  refine sepWP_intro_ro8_mfb (lsmpl.ρ mergeFieldRodataSym + 13#64) 0x4c#8
    (fun hm => lsro8_intro hro1 (by lsro_addr) (by decide +kernel) hm) ?_
  by_vm_steps_withSvc (
    wp_steps
    apply sepWP_drop_left_mfb
    refine SepWP.done (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm2 hcl2 hro2
  rw [← A.pool_transport lim st _ _ hvm2]
  apply sepWPp_seq_lsclro_vm hcl2 hro2 (mid := lsmpl.base 76)
  by_vm_steps_withSvc (
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm3 hcl3 hro3
  rw [← A.pool_transport lim st _ _ hvm3]
  set bsD := kyberB0 i :: 12#8 :: 8#8 :: kyberIdBytes i ct tail
  set vD := BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length)
  refine sepWPp_call_lscl_15
    (x := (⟨s0.sp - 232#64, ptr, bsD⟩, vD, 8#8 :: kyberIdBytes i ct tail))
    hcallD hcl3 hro3
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp240, beq_self_eq_true])
    (by simp only [wp_norm, arm64_norm]; rfl)
    (by
      dsimp only [ProstVarintVm.decodeVarintSliceSomeSpecGen]
      apply entails_pure_sep_frame
      · refine ⟨?_, ?_, ?_,
          by simp only [bsD, List.length_cons, kyberIdBytes_length i hct]; omega,
          Or.inl (by simp only [bsD, List.length_cons, kyberIdBytes_length i hct]; omega),
          decodeVarint_kyber_ne i tail⟩
        · simp only [wp_norm, arm64_norm]
        · simp only [wp_norm, arm64_norm]
        · simp only [wp_norm, arm64_norm, bsD, List.length_cons, kyberIdBytes_length i hct,
            BitVec.toNat_ofNat]; omega
      · apply entails_rw_stack_3 (sp2 := s0.sp - 240#64) (w2 := decodeVarintSliceStackW)
        · simp only [wp_norm, arm64_norm]
        · rfl
        · dsimp only [bsD]
          rw [bytes_kyber_ne_split_mf14]
          sep_frame)
    ?_
  intro sm1 hpcm1 hrunm1 hspm1 hcsm1 hclm1 hrom1
  dsimp only [ProstVarintVm.decodeVarintSliceSomeSpecGen]
  refine sepWPp_pure_left_and fun ⟨htrm1, hvmm1⟩ => ?_
  rw [← A.pool_transport lim st _ sm1 hvmm1]
  try simp only [wp_norm, arm64_norm] at hpcm1
  have hspm1' : sm1.sp = s0.sp - 240#64 := by simpa only [wp_norm, arm64_norm] using hspm1
  have htrm1' : sm1.trace = s0.trace := by simpa only [wp_norm, arm64_norm] using htrm1
  have hx19m1 : sm1.readReg64 (Reg.gpr 19#5) = slot := by
    simpa only [wp_norm, arm64_norm] using hcsm1.1
  have hx20m1 : sm1.readReg64 (Reg.gpr 20#5) = 99#64 := by
    simpa only [wp_norm, arm64_norm] using hcsm1.2.1
  have hx21m1 : sm1.readReg64 (Reg.gpr 21#5) = ss := by
    simpa only [wp_norm, arm64_norm] using hcsm1.2.2.1
  have hx22m1 : sm1.readReg64 (Reg.gpr 22#5) = bufRef := by
    simpa only [wp_norm, arm64_norm] using hcsm1.2.2.2.1
  have hx26m1 : sm1.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := by
    simpa only [wp_norm, arm64_norm] using hcsm1.2.2.2.2.2.2.2.1
  have hx27m1 : sm1.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
    simpa only [wp_norm, arm64_norm] using hcsm1.2.2.2.2.2.2.2.2.1
  have hx28m1 : sm1.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
    simpa only [wp_norm, arm64_norm] using hcsm1.2.2.2.2.2.2.2.2.2.1
  have hvregsm1 : calleeSavedVRegs sm1 = calleeSavedVRegs s0 := by
    simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hcsm1.2.2.2.2.2.2.2.2.2.2.2
  have hstk_d : 0x50 + decodeErrorHookStackW = decodeVarintSliceStackW := rfl
  have hsub_d : bsD.length - (8#8 :: kyberIdBytes i ct tail).length = 2 := by
    simp only [bsD, List.length_cons]; omega
  conv =>
    arg 4
    rw [hstk_d, hsub_d,
        show stackAt _ decodeVarintSliceStackW = stackAt (s0.sp - 240#64) decodeVarintSliceStackW by
          simp only [wp_norm, arm64_norm],
        pointsTo64_zero_split32_mf14 s0.sp,
        show s0.sp - 232#64 + 8#64 = s0.sp - 224#64 by bv_lin,
        show s0.sp - 232#64 + 16#64 = s0.sp - 216#64 by bv_lin]
    dsimp only [bsD, vD]
    rw [bytes_kyber_ne_split_mf14]
    simp only [sepConj_assoc]
  have hc_ult2' : BitVec.ult (BitVec.ofNat 64 (1575 + (encodeVarint (i.setWidth 64)).length +
      tail.length)) 2#64 = false := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  have hc_sub2' : BitVec.ofNat 64 (1575 + (encodeVarint (i.setWidth 64)).length +
      tail.length) - 2#64 =
      BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length + tail.length) := by
    have hsub := len_sub_mf14W (a := 1575 + (encodeVarint (i.setWidth 64)).length) (b := 2)
      (n := tail.length) (by omega) (by omega)
    have heq : 1575 + (encodeVarint (i.setWidth 64)).length - 2 + tail.length =
        1573 + (encodeVarint (i.setWidth 64)).length + tail.length := by omega
    rwa [heq] at hsub
  have hc_ult_body : BitVec.ult (BitVec.ofNat 64 (1573 +
      (encodeVarint (i.setWidth 64)).length + tail.length))
      (BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length)) = false := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  have hc_sub_body : BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length +
      tail.length) -
      BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length) =
      BitVec.ofNat 64 tail.length := by
    simpa using len_sub_mf14W (a := 1573 + (encodeVarint (i.setWidth 64)).length)
      (b := 1573 + (encodeVarint (i.setWidth 64)).length) (n := tail.length) (by omega) (by omega)
  have hc_ule_body : BitVec.ule (BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length))
      (BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length + tail.length)) = true := by
    simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
  have hc_ule_n2' : BitVec.ule (BitVec.ofNat 64 tail.length)
      (BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length + tail.length)) = true := by
    simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
  have hc_ult_n' : BitVec.ult (BitVec.ofNat 64 tail.length)
      (BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length + tail.length)) = true := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
  have hc_ult_n2' : BitVec.ult (BitVec.ofNat 64 (1573 +
      (encodeVarint (i.setWidth 64)).length + tail.length))
      (BitVec.ofNat 64 tail.length) = false := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  have hc_ule_n' : BitVec.ule (BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length +
      tail.length)) (BitVec.ofNat 64 tail.length) = false := by
    simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  have hc_eq_n' : (BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length + tail.length) ==
      BitVec.ofNat 64 tail.length) = false := by
    rw [beq_eq_false_iff_ne]; intro heq
    have h1 := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_ofNat] at h1; omega
  have hc_sub1' : BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length +
      tail.length) - 1#64 =
      BitVec.ofNat 64 (1572 + (encodeVarint (i.setWidth 64)).length + tail.length) := by
    have hsub := len_sub_mf14W (a := 1573 + (encodeVarint (i.setWidth 64)).length) (b := 1)
      (n := tail.length) (by omega) (by omega)
    have heq : 1573 + (encodeVarint (i.setWidth 64)).length - 1 + tail.length =
        1572 + (encodeVarint (i.setWidth 64)).length + tail.length := by omega
    rwa [heq] at hsub
  apply sepWPp_seq_lsclro_vm hclm1 hrom1 (mid := lsmpl.base 8)
  by_vm_steps_withSvc (
    iterate 45 wp_step
    refine SepWP.done (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrunm1])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm4 hcl4 hro4
  rw [← A.pool_transport lim st sm1 _ hvm4]
  refine sepWPp_call_lscl_15
    (x := (⟨.varint, ss + 320#64, bufRef, slot, ptr + 3#64, kyberIdBytes i ct tail⟩,
      i, 18#8 :: innerBytes ct tail))
    hcallI hcl4 hro4
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrunm1])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hspm1', hsp240, beq_self_eq_true])
    (by simp only [wp_norm, arm64_norm]; rfl)
    (by
      dsimp only [ProstVarintVm.int32MergeSomeSpecGen]
      apply entails_pure_sep_frame
      · refine ⟨?_, ?_, ?_, by rw [kyberIdBytes_length i hct]; omega,
          mergeUint32_kyberIdBytes i tail⟩
        · simp only [wp_norm, arm64_norm]
        · simp only [wp_norm, arm64_norm, hx21m1]
        · simp only [wp_norm, arm64_norm, hx22m1]
      · apply entails_rw_stack_4 (sp2 := s0.sp - 240#64) (w2 := int32MergeStackW)
        · simp only [wp_norm, arm64_norm, hspm1']
        · rfl
        · apply entails_swap_stack_4 (decode_to_int32Merge_stack_mf14W (s0.sp - 240#64))
          apply entails_frame_memRegion4
          rw [← sliceCursorAt_kyberId_fold_mf14 slot ptr i hct tail]
          sep_frame)
    ?_
  intro smI hpcmI hrunmI hspmI hcsmI hclmI hromI
  dsimp only [ProstVarintVm.int32MergeSomeSpecGen]
  refine sepWPp_pure_left_and fun ⟨hx0mI, htrmI, hvmmI⟩ => ?_
  rw [← A.pool_transport lim st _ smI hvmmI]
  try simp only [wp_norm, arm64_norm] at hpcmI
  have hspmI' : smI.sp = s0.sp - 240#64 := by
    simpa only [wp_norm, arm64_norm, hspm1'] using hspmI
  have htrmI' : smI.trace = s0.trace := by
    simpa only [wp_norm, arm64_norm, htrm1'] using htrmI
  have hx19mI : smI.readReg64 (Reg.gpr 19#5) = 98#64 := by
    simpa only [wp_norm, arm64_norm] using hcsmI.1
  have hx20mI : smI.readReg64 (Reg.gpr 20#5) = ss := by
    simpa only [wp_norm, arm64_norm, hx21m1] using hcsmI.2.1
  have hx21mI : smI.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tail.length := by
    simpa only [wp_norm, arm64_norm] using hcsmI.2.2.1
  have hx22mI : smI.readReg64 (Reg.gpr 22#5) = bufRef := by
    simpa only [wp_norm, arm64_norm, hx22m1] using hcsmI.2.2.2.1
  have hx26mI : smI.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := by
    simpa only [wp_norm, arm64_norm, hx26m1] using hcsmI.2.2.2.2.2.2.2.1
  have hx27mI : smI.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
    simpa only [wp_norm, arm64_norm, hx27m1] using hcsmI.2.2.2.2.2.2.2.2.1
  have hx28mI : smI.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
    simpa only [wp_norm, arm64_norm, hx28m1] using hcsmI.2.2.2.2.2.2.2.2.2.1
  have hvregsmI : calleeSavedVRegs smI = calleeSavedVRegs s0 := by
    have h1 : calleeSavedVRegs smI = calleeSavedVRegs sm1 := by
      simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hcsmI.2.2.2.2.2.2.2.2.2.2.2
    exact h1.trans hvregsm1
  have hstk_i : 0x50 + (0x50 + decodeErrorHookStackW) = int32MergeStackW := rfl
  conv =>
    arg 4
    rw [hstk_i,
        show stackAt _ int32MergeStackW = stackAt (s0.sp - 240#64) int32MergeStackW by
          simp only [wp_norm, arm64_norm, hspm1'],
        sliceCursorAfter_kyberId_unfold_mf14 slot ptr i hct tail]
    simp only [sepConj_assoc]
  have hc_ule_n2 : BitVec.ule (BitVec.ofNat 64 tail.length)
      (BitVec.ofNat 64 (1572 + tail.length)) = true := by
    simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
  have hc_ult_n : BitVec.ult (BitVec.ofNat 64 tail.length)
      (BitVec.ofNat 64 (1572 + tail.length)) = true := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
  have hc_ult_n2 : BitVec.ult (BitVec.ofNat 64 (1572 + tail.length))
      (BitVec.ofNat 64 tail.length) = false := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  have hc_ule_n : BitVec.ule (BitVec.ofNat 64 (1572 + tail.length))
      (BitVec.ofNat 64 tail.length) = false := by
    simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  have hc_eq_n : (BitVec.ofNat 64 (1572 + tail.length) == BitVec.ofNat 64 tail.length) = false := by
    rw [beq_eq_false_iff_ne]; intro heq
    have h1 := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_ofNat] at h1; omega
  have hc_sub1 : BitVec.ofNat 64 (1572 + tail.length) - 1#64 =
      BitVec.ofNat 64 (1571 + tail.length) := len_sub_mf14W (by omega) (by omega)
  apply sepWPp_seq_lsclro_vm hclmI hromI (mid := lsmpl.base 7)
  by_vm_steps_withSvc (
    iterate 33 wp_step
    refine SepWP.done (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrunmI])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm5 hcl5 hro5
  rw [← A.pool_transport lim st smI _ hvm5]
  refine sepWPp_call_lscro_15
    (x := (⟨.lengthDelimited, ss + 296#64, 0#64, 1#64, [], bufRef, slot,
      kyberPtr2 ptr i + 1#64, innerBytes ct tail⟩, ct, tail, st))
    hcallB hcl5 hro5
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrunmI])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hspmI', hsp240, beq_self_eq_true])
    (by simp only [wp_norm, arm64_norm]; rfl)
    (by
      dsimp only [bytesMergeFreshBudgetSpecW]
      apply entails_pure_sep_frame
      · refine ⟨?_, ?_, ?_, by rw [innerBytes_length hct]; omega,
          rfl, rfl, mergeBytes_inner hct tail, hfit⟩
        · simp only [wp_norm, arm64_norm]
        · simp only [wp_norm, arm64_norm, hx20mI]
        · simp only [wp_norm, arm64_norm, hx22mI]
      · apply entails_rw_stack_5 (sp2 := s0.sp - 240#64) (w2 := bytesMergeStackW)
        · simp only [wp_norm, arm64_norm, hspmI']
        · rfl
        · apply entails_swap_stack_5 (int32Merge_to_bytesMerge_stack_mf14W (s0.sp - 240#64))
          rw [← emptyVec_kyber_eq_vecU8At A.repAlloc ss,
              ← sliceCursorAt_inner_ne_fold_mf14 slot ptr i hct tail]
          sep_frame)
    ?_
  intro sm2 hpcm2 hrunm2 hspm2 hcsm2 _hclm2 _hrom2
  dsimp only [bytesMergeFreshBudgetSpecW]
  refine sepWPp_pure_left_and fun ⟨hx0m2, htrm2⟩ => ?_
  try simp only [wp_norm, arm64_norm] at hpcm2
  have hx0m2' : sm2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0m2
  have hspm2' : sm2.sp = s0.sp - 240#64 := by
    simpa only [wp_norm, arm64_norm, hspmI'] using hspm2
  have htrm2' : sm2.trace = s0.trace := by
    simpa only [wp_norm, arm64_norm, htrmI'] using htrm2
  have hx21m2 : sm2.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tail.length := by
    simpa only [wp_norm, arm64_norm, hx21mI] using hcsm2.2.2.1
  have hx22m2 : sm2.readReg64 (Reg.gpr 22#5) = bufRef := by
    simpa only [wp_norm, arm64_norm, hx22mI] using hcsm2.2.2.2.1
  have hx26m2 : sm2.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := by
    simpa only [wp_norm, arm64_norm, hx26mI] using hcsm2.2.2.2.2.2.2.2.1
  have hx27m2 : sm2.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
    simpa only [wp_norm, arm64_norm, hx27mI] using hcsm2.2.2.2.2.2.2.2.2.1
  have hx28m2 : sm2.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
    simpa only [wp_norm, arm64_norm, hx28mI] using hcsm2.2.2.2.2.2.2.2.2.2.1
  have hvregsm2 : calleeSavedVRegs sm2 = calleeSavedVRegs s0 := by
    have h1 : calleeSavedVRegs sm2 = calleeSavedVRegs smI := by
      simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hcsm2.2.2.2.2.2.2.2.2.2.2.2
    exact h1.trans hvregsmI
  have htail_ult_self :
      BitVec.ult (BitVec.ofNat 64 tail.length) (BitVec.ofNat 64 tail.length) = false := by
    simp [BitVec.ult]
  have htail_ule_self :
      BitVec.ule (BitVec.ofNat 64 tail.length) (BitVec.ofNat 64 tail.length) = true := by
    simp [BitVec.ule]
  conv =>
    arg 4
    rw [show stackAt _ bytesMergeStackW = stackAt (s0.sp - 240#64) bytesMergeStackW by
          simp only [wp_norm, arm64_norm, hspmI'],
        sliceCursorAfter_inner_ne_unfold_mf14 slot ptr i hct tail]
  set stB := M.stepEvents (bytesMergeEvents 0 ct.length) st
  refine SepWPp.weaken_pre (P' :=
      vecU8FreshCap A.repAlloc (ss + 296#64) ct ∗
        ((ss + 320#64) ↦₃₂ i) ∗ memRegion (ss + 324#64) 4 ∗
        (ptr ↦₈ kyberB0 i) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 8#8) ∗
        ((ptr + 3#64) ↦ₛ encodeVarint (i.setWidth 64)) ∗
        (kyberPtr2 ptr i ↦₈ 18#8) ∗
        ((kyberPtr2 ptr i + 1#64) ↦ₛ innerBytes ct tail) ∗
        (bufRef ↦₆₄ slot) ∗
        (slot ↦₆₄ (kyberPtr2 ptr i + 1572#64)) ∗
        ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
        A.pool lim stB sm2 ∗
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
        ((s0.sp - 56#64) ↦₆₄ s56) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
        memRegion (s0.sp - 240#64) 8 ∗
        ((s0.sp - 232#64) ↦₃₂ 0#32) ∗ ((s0.sp - 228#64) ↦₃₂ 0#32) ∗
        ((s0.sp - 224#64) ↦₆₄ BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length)) ∗
        ((s0.sp - 216#64) ↦₆₄ 2#64) ∗
        memRegion (s0.sp - 208#64) 128 ∗
        stackAt (s0.sp - 240#64) mergeFieldSubStackX)
    (Entails.of_eq (by
      unfold vecU8FreshCap
      rw [stackAt_sub_to_bytesMerge_mf14W (s0.sp - 240#64)]
      sep_ac_rfl)) ?_
  apply SepWPp.of_sepWP_ret
  apply sepWP_ret_vmPreserved
  by_vm_steps_withSvc (
    iterate 19 wp_step
    refine SepWP.done (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrunm2])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm_end
  rw [← A.pool_transport lim stB sm2 _ hvm_end]
  apply SepWP.done (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrunm2])
  refine ⟨by simp only [wp_norm, arm64_norm, hspm2'],
    by simp only [CalleeSavedPreserved, calleeSavedVRegs, wp_norm, arm64_norm,
      hx26m2, hx27m2, hx28m2, hvregsm2, and_self],
    by simp only [wp_norm, arm64_norm, htrm2'],
    by simp only [wp_norm, arm64_norm, hx0m2'], ?_⟩
  have hmem160 :
      memRegion (s0.sp - 240#64) 8 ∗
        (((s0.sp - 232#64) ↦₃₂ 0#32) ∗ ((s0.sp - 228#64) ↦₃₂ 0#32) ∗
          ((s0.sp - 224#64) ↦₆₄ BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length)) ∗
          ((s0.sp - 216#64) ↦₆₄ 2#64)) ∗
        memRegion (s0.sp - 208#64) 128 ⊢
      memRegion (s0.sp - 240#64) 160 := by
    rw [← memRegion160_fold_mf14 s0.sp]
    exact sepConj_mono_right (sepConj_mono_left
      (cells24_entails_memRegion24_mf14 s0.sp
        (BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length)) 2#64))
  have hstk :
      ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
        ((s0.sp - 56#64) ↦₆₄ s56) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
        (memRegion (s0.sp - 240#64) 8 ∗
          (((s0.sp - 232#64) ↦₃₂ 0#32) ∗ ((s0.sp - 228#64) ↦₃₂ 0#32) ∗
            ((s0.sp - 224#64) ↦₆₄ BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length)) ∗
            ((s0.sp - 216#64) ↦₆₄ 2#64)) ∗
          memRegion (s0.sp - 208#64) 128) ∗
        stackAt (s0.sp - 240#64) mergeFieldSubStackX ⊢
      stackAt s0.sp mergeFieldStackX := by
    refine Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (Entails.trans (sepConj_mono_left hmem160) ?_)
    refine Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (stackAt_mergeField_fold_mf14W s0.sp
        (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
        (s0.readReg64 (Reg.gpr 25#5)) s56
        (s0.readReg64 (Reg.gpr 24#5)) (s0.readReg64 (Reg.gpr 23#5))
        (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
        (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5)))
  have hp_post := kyberAt14Cap_some_fold A.repAlloc ss i ct
  rw [← sliceCursorAfter_kyber_ne_fold_mf14 slot ptr hi hct tail]
  refine Entails.trans (Entails.of_eq ?_)
    (sepConj_mono hp_post (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hstk))))
  sep_ac_rfl

theorem mergeFieldBasic_tag14_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H) :
    subroutine_ok (lsProg_15 H) (blkPl_15).base
      (mergeFieldQBudgetSpecW M A lim (fun fl => fl.tag = 14)) := by
  apply subroutine_ok_of_field_sepWPp
  intro x capRecv st s0 hpc hrun hal hcl hro hx0 hx1 hx2 hx3 hx4 hP hOk hFr _hFrB hlen
    _hpow _hle _hcap62 hfit
  generalize x.fld = fld at hx1 hx2 hP hOk hFr hlen hfit ⊢
  cases fld with
  | base f => cases f <;> simp [GenFieldQ.tag, GenField.tag] at hP
  | kyber i ct =>
    have hct : ct.length = 1569 := hOk
    have hk : x.v.ext.kyber = none := hFr.1
    refine ⟨kyberAt14Cap A.repAlloc x.ss x.v.ext.kyber,
      kyberAt14Cap A.repAlloc x.ss (some (i, ct)),
      prostSSGQRest_kyber A.repAlloc x.ss capRecv x.v, ?_, ?_, ?_⟩
    · unfold prostSSGQAtCap prostSSGQRest_kyber prostSSGQScalars
      rw [kyberAtCap_eq_kyberAt14Cap_sep]
      exact Entails.of_eq (by sep_ac_rfl)
    · unfold prostSSGQAtCap nextCapRecv SSGQ.apply prostSSGQRest_kyber prostSSGQScalars
      dsimp only
      rw [kyberAtCap_eq_kyberAt14Cap_sep, pendingAt9PCap_congr A.repAlloc x.ss rfl rfl rfl]
      exact Entails.of_eq (by sep_ac_rfl)
    · by_cases hi : i = 0#32
      · subst hi
        exact step_tag14_kyber_0_mfb hA x.ss x.bufRef x.slot x.ptr x.v.ext.kyber ct hct hk
          x.tail st hpc hrun hal hcl hro hx0 hx1 hx2 hx3 hx4 hlen hfit
      · exact step_tag14_kyber_ne_mfb hA x.ss x.bufRef x.slot x.ptr x.v.ext.kyber i ct hi hct hk
          x.tail st hpc hrun hal hcl hro hx0 hx1 hx2 hx3 hx4 hlen hfit
  | _ => simp [GenFieldQ.tag] at hP

/-! ## 6. Combined `mergeFieldBasic_budget_placed_ok` (`IsBasicFieldQ`) -/

/-- Relocatable `[LibsignalPlacement]` proof of `SessionStructure::merge_field` (Block `15`,
`lsProg_15 H`, `mergeFieldStackX`) for all non-chain tags `IsBasicFieldQ`
(`tags 1, 2, 3, 4, 5, 9, 10, 11, 13, 14, 15`), with `onPanic := ⌜False⌝` and `onOom := ⌜False⌝`. -/
theorem mergeFieldBasic_budget_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H) :
    subroutine_ok (lsProg_15 H) (blkPl_15).base
      (mergeFieldQBudgetSpecW M A lim IsBasicFieldQ) := by
  refine mergeFieldQBudget_of_imp
    (mergeFieldQBudget_or
      (mergeFieldQBudget_or mergeFieldBasic_u32_ok (mergeFieldBasic_bytes_ok hA))
      (mergeFieldQBudget_or (mergeFieldBasic_tag9_ok hA) (mergeFieldBasic_tag14_ok hA))) ?_
  intro fl ⟨h6, h7⟩
  cases fl with
  | base f =>
    cases f <;> simp [GenFieldQ.tag, GenField.tag] at h6 h7 ⊢
  | _ => simp [GenFieldQ.tag]

/-- Lift any `mergeFieldQBudgetSpecW` proof on `lsProg_15 H` to a caller block `callerProg`
via `ls_call_ro_of_block`. -/
theorem mergeFieldQBudget_caller_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {P : GenFieldQ → Prop}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (h : subroutine_ok (lsProg_15 H) (blkPl_15).base (mergeFieldQBudgetSpecW M A lim P))
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 15) (mergeFieldQBudgetSpecW M A lim P) :=
  ls_call_ro_of_block (callerProg := callerProg) h hblk

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldBasicBudget
