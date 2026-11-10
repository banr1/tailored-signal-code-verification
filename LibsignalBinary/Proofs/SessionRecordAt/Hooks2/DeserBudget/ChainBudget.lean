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
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.GrowOne104Budget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.ProstMergeBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserDefsX
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.ChainDefs
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Fields
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.ChainEntryG
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.ChainSenderRatchetKeyG
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.ChainKeyFieldG
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.ChainMessageKeysG
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.ChainKeyEpilogue
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Pure
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.MergeReceiverChainsAux.Base
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.MergeReceiverChainsAux.Steps
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.ChainEntryGExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.ChainSenderRatchetKeyGExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.ChainKeyFieldGExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.ChainMessageKeysGExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.ChainExitGExt
public import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Defs
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `prost::encoding::message::merge<Chain>` Proof

Proves the relocatable `[LibsignalPlacement]` total-correctness (`onPanic := ⌜False⌝`,
`onOom := ⌜False⌝`) contract `chainMergeGen_budget_placed_ok` (Block `11`, `chainMergeStackX`)
under `AllocContractsBudgetPlaced M A lim H` and `[HasFineReallocCredit M]`:
* Capacity-explicit `prostChainGAtCap` tracking `bytesMergeOutCap` and `vecCap4Of c.keys.length`
  (`0` when `c.keys = []`), with erasure to `prostChainGAt` and 104-byte move `prostChainGAtCap_move_chunks104`.
* Symbolic cost bounds (`chainMergeSmallCost`, `chainMergeLargeLive`, `chainMergePeakLarge`) and
  telescoping step invariants (`stepEvents_chainMerge_bounds`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 2000000

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.ChainBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (MessageKeyGenerator maxMessageKeys)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks IsLsBlockProg LibsignalCodeLoaded LibsignalRoLoaded
  libsignalRoLoaded_of_keepsFrozen withLsCodeLoaded withLsCl extract_withLsCodeLoaded lsmpl
)
open CryptoVerification.RustHeap (
  RustAlloc vecU8 vecU8At vecU8Buf vecOf vecAt vecBuf vecHeader vecHeaderBytes
  arrayAt arrayAt_nil arrayAt_cons
)
open CryptoVerification.LibsignalSession (GrowGhost)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalProtoCodec (
  WireType encodeVarint decodeVarint decodeVarint_encodeVarint mergeBytes mergeUint32
)
open CryptoVerification.LibsignalTripleRatchet (
  withLsCodeRoLoaded extract_withLsCodeRoLoaded ls_subroutine_ok_cl_of_callee ls_subroutine_ok_of_callee
)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  BytesMergeGhost Int32MergeGhost DecodeVarintSliceGhost
  sliceCursorAt sliceCursorAfter VarintSlicePre varintSliceResultAt
)
open CryptoVerification.LibsignalTripleRatchet.Prost.X (
  decodeErrorHookStackW decodeVarintSliceStackW int32MergeStackW bytesMergeStackW
)
open CryptoVerification.LibsignalTripleRatchet.RawByteMove (
  chunks104_6QWAt exists_bytes104Of6QW
  vecU8At_eq_bytes_sep_buf vecAt_eq_bytes_sep_buf
)
open CryptoVerification.E2E.Record (pbBytes pbVarint pbVarintBody)
open CryptoVerification.E2E.Record.Placed (blkPC_11 blkPl_11 lsProg_11)
open CryptoVerification.E2E.Record.DeserializeSeed (
  chainMergeSavedRegs sp_sub_256_aligned_seedChain sliceCursorAfter_append_eq_seedChain
  pbBytes_lt128_eq_seedChain pbBytes_ptr_advance_seedChain pbBytes_pointsTo_combine_seedChain
  pbVarint1_ptr_advance_seedChain pbVarint1_pointsTo_combine_seedChain
  len_cons_sub_one_seedChain bv_ofNat_add_sub_left_seedChain
  mergeBytes_lt128_seedChain mergeUint32_pbVarintBody_seedChain
  encodeVarint_lt128_seedChain ckEnc_length_bounds_seedChain
  memRegion24_split_ck_seedChain
  move_bytes_pair_receiverChains prostCkTailSome_move_bytes_receiverChains
  memRegion104_eq_exists_chunks104_6QWAt_receiverChains
  chunks104_6QWAt_dst_eq_receiverChains chunks104_6QWAt_entails_memRegion104_receiverChains
)
open CryptoVerification.E2E.Record.DeserializeGeneral (
  ChainG ChainField chainGAfter ChainMergeGenGhost prostMsgKeyAt prostChainGAt
  chainG_enc_eq_fields chainGAfter_fields
)
open Proofs.libsignal.Stage1X (growOneChainStackX lscall_of_withLsCl)
open Proofs.libsignal.Hooks2 (
  chainMergeStackX chainMergeSubStackX chainPlacedPC
  stackAt_chainMergeStackX_split_seedChain
  stackAt_sub_to_varintSlice_cmeW
  stackAt_sub_to_bytesMerge_seedChainW stackAt_sub_to_int32Merge_seedChainW
  stackAt_sub_to_growOne_seedChainW
  cbz_len_cons_false_seedChain62 ult_ofNat_add_left_false_seedChain62
  ule_ofNat_add_right_true_seedChain62 ule_ofNat_of_gt_false_seedChain62
  ult_ofNat_of_gt_true_seedChain62 ult_10_of_gt_cme62 ule_10_of_gt_false_cme62
  encodeVarint_ge128_cons_cme62
)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel RustCliAllocBudget BudgetLimits
  FitsStep FitsEvent FitsEvents fitsEvents_nil fitsEvents_append fitsEvents_of_step_monotone
  rustAllocEvents rustDeallocEvents rustReallocEvents
  VmPreserved
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (
  HasFineReallocCredit
  stepEvents_rustAlloc_small stepEvents_rustAlloc_large
  stepEvents_rustRealloc_small_small stepEvents_rustRealloc_small_large
  stepEvents_rustRealloc_large_large
  fitsStep_of_fine_bounds
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.Potential (
  vecCap4Next vecCap4Push vecCap4Of IsPow2Cap4
  vecCap4Of_zero vecCap4Of_succ vecCap4Of_pow2
  isPow2Cap4_zero isPow2Cap4_zero_or_ge_four isPow2Cap4_next isPow2Cap4_next_le_of_lt
  vecCap4Of_mono le_vecCap4Of
  vec104GrowEvents vec104CumOfCap vec104CumRem vec104LargeLive vec104PeakLarge
  vec104CumOfCap_zero vec104CumRem_zero vec104CumRem_self
  vec104LargeLive_zero vec104PeakLarge_zero vec104LargeLive_le_peakLarge
  vec104PeakLarge_le_of_pow2
  stepEvents_vec104Grow_telescope vec104Push_budget_step
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.HookLift (
  AllocContractsBudgetPlaced withVmPreserved
  trapHooks sepWP_rebase_vmPreserved
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.GrowOne104Budget (
  cap_zero_or_ge_two_of_isPow2Cap4
  growOne104BudgetSpecX grow_one_104_budget_placed_ok_cl
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.ProstVarintVm (
  decodeVarintSliceSomeSpecGen decodeVarintSliceSomeSpecW decode_varint_slice_some_placed_ok_cl
  int32MergeSomeSpecGen int32MergeSomeSpecW int32_merge_some_placed_ok_cl
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.ProstMergeBudget (
  sepWPp_seq_lsclro_vm
  bytesMergeAllocEvents bytesMergeEvents bytesMergeOutCap
  bytesMergeOutCap_zero_zero bytesMergeOutCap_zero_pos
  fitsEvents_rustAlloc_one
  stepEvents_bytesMergeFresh_zero stepEvents_bytesMergeFresh_small
  bytesMergeFreshBudgetSpecW bytes_merge_fresh_budget_placed_okW_cl
)

attribute [local irreducible] Program.fetch Program.externAt? FitsEvents
attribute [local simp, local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero

@[reducible]
private def vmDst {s1 s2 : State} (_ : VmPreserved s1 s2) : State := s2

namespace ChainMergeStateSimp

@[local arm64_norm ↓, local wp_norm ↓]
theorem calleeSavedVRegs_setPC_cb (s : State) (pc : BitVec 64) :
    calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem calleeSavedVRegs_setMem_setPC_cb (s : State) (pc : BitVec 64) (m : Memory) :
    calleeSavedVRegs ((s.setPC pc).setMem m) = calleeSavedVRegs s := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_cb (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_cb (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem tpidrEl0_setPC_cb (s : State) (pc : BitVec 64) :
    (s.setPC pc).tpidrEl0 = s.tpidrEl0 := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem tpidrEl0_setMem_setPC_cb (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).tpidrEl0 = s.tpidrEl0 := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_cb (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_cb (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_cb (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_setPC_cb (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_cb (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_setPC_cb (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local simp, local arm64_norm]
theorem getLsbD_63_eq_cb (v : BitVec 64) :
    v.getLsbD 63 = !(v >>> 56).ult 128#64 :=
  CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainEntryG.ChainMergeStateSimp.getLsbD_63_eq_seedChain v

end ChainMergeStateSimp

attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite isCalleeSavedVReg
attribute [local arm64_norm ↓, local wp_norm ↓]
  ChainMergeStateSimp.calleeSavedVRegs_setPC_cb
  ChainMergeStateSimp.calleeSavedVRegs_setMem_setPC_cb
  ChainMergeStateSimp.sp_setPC_cb
  ChainMergeStateSimp.sp_setMem_setPC_cb
  ChainMergeStateSimp.tpidrEl0_setPC_cb
  ChainMergeStateSimp.tpidrEl0_setMem_setPC_cb
  ChainMergeStateSimp.readReg64_setPC_cb
  ChainMergeStateSimp.readReg64_setMem_setPC_cb
  ChainMergeStateSimp.readReg32_setPC_cb
  ChainMergeStateSimp.readReg32_setMem_setPC_cb
  ChainMergeStateSimp.readReg_setPC_cb
  ChainMergeStateSimp.readReg_setMem_setPC_cb
attribute [local simp, local arm64_norm] ChainMergeStateSimp.getLsbD_63_eq_cb

open CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainEntryG (
  w0_and_255_eq_two_seedChain signExtend64_ofNat8_lt128_seedChain
  ofNat64_lsr56_eq_zero_seedChain signExtend64_contByte_lsr56_cme
  memRegion160_split_varint_cme
  pointsTo64_zero_split32_cme cells24_entails_memRegion24_cme
)
open CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainSenderRatchetKeyG (
  chainGAfter_succ drop_flatMap_enc mem_fields_srk_length_lt mem_fields_priv_length_lt
  lenField_eq_pbBytes preBytes curPtr payload_append_eq_preBytes
  sliceCursorAfter_eq_preBytes preBytes_succ curPtr_succ pointsToBytes_preBytes_succ
)
open CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainKeyFieldG (
  chainField_tag_three_info chainField_ck_enc_eq pfx_k rem_k
  payload_append_eq_pfx_rem rem_k_eq_cons pfx_k_succ
  combine_tag3_cursor ck_hdr_pointsTo_combine_seedChain
)
open CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainMessageKeysG (
  chainField_eq_key_of_tag4 mem_keys_of_key_mem_fields chainGAfter_keys_length_le
  chainGAfter_succ_of_key drop_fields_flatMap_enc_of_key encMessageKey_eq_pb
  encMessageKey_length_lt128 lenField_4_encMessageKey_eq
  chainMergeSavedRegs12 chainMergePad4 chainMergeSavedRegs_eq_split
  memRegion104_sp248_split memRegion80_sp248_eq_cells10 chunks104_6QWAt_sp248_eq
  mk_hdr_pointsTo_combine_seedChain sliceCursorAfter_tag4_combine
  ptr_madd_104_eq ofNat_add_one_eq
  beq_ofNat_cap_false memRegion_spare_eq_emp_of_full memRegion_spare_split_of_lt
  ult_ofNat_add_right_false_seedChain
)

/-! ## 1. Capacity-Explicit `prostChainGAtCap` Layout, Erasure & 104-Byte Move Lemmas -/

/-- Freshly-merged `Vec<u8>` at `v` with deterministic capacity `bytesMergeOutCap 0#64 bs.length`
(`0#64` when `bs = []`, `BitVec.ofNat 64 (max bs.length 8)` when `bs ≠ []`). -/
def vecU8FreshCap (A : RustAlloc) (v : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ∃∗ ptr : BitVec 64, vecU8At A v (bytesMergeOutCap 0#64 bs.length) ptr bs

theorem vecU8FreshCap_entails_vecU8 (A : RustAlloc) (v : BitVec 64) (bs : List (BitVec 8)) :
    vecU8FreshCap A v bs ⊢ vecU8 A v bs := by
  unfold vecU8FreshCap vecU8
  apply Entails.sepExists_elim; intro ptr
  exact Entails.sepExists_right (bytesMergeOutCap 0#64 bs.length)
    (Entails.sepExists_right ptr (Entails.refl _))

theorem emptyCells_entails_vecU8FreshCap (A : RustAlloc) (v ptr : BitVec 64) (hptr : ptr ≠ 0) :
    (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ 0#64) ⊢
      vecU8FreshCap A v [] := by
  unfold vecU8FreshCap
  rw [List.length_nil, bytesMergeOutCap_zero_zero]
  refine Entails.sepExists_right ptr ?_
  refine Entails.trans ?_
    (Entails.of_eq (?_ :
      ⌜(0 : Nat) ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ 0#64)) = _))
  · exact Entails.pure_right ⟨by decide, by decide, hptr⟩ (Entails.refl _)
  · unfold vecU8At vecHeader
    have hite : (if (0#64 : BitVec 64) = 0 then emp else
        A.live ptr (0#64 : BitVec 64).toNat 1 ∗ (ptr ↦ₛ []) ∗
          memRegion (ptr + BitVec.ofNat 64 ([] : List (BitVec 8)).length)
            ((0#64 : BitVec 64).toNat - ([] : List (BitVec 8)).length)) = emp := rfl
    have h0 : BitVec.ofNat 64 ([] : List (BitVec 8)).length = 0#64 := rfl
    rw [hite, h0, List.length_nil, sepConj_emp]
    sep_ac_rfl

theorem vecU8FreshCap_move_bytes (A : RustAlloc) (bs : List (BitVec 8)) (a : BitVec 64) :
    vecU8FreshCap A a bs ⊢
      ∃∗ hbs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜hbs.length = 24 ∧ ∀ b : BitVec 64, ((b ↦ₛ hbs) ∗ H) ⊢ vecU8FreshCap A b bs⌝ ∗
        (a ↦ₛ hbs) ∗ H := by
  unfold vecU8FreshCap
  apply Entails.sepExists_elim; intro ptr
  rw [vecU8At_eq_bytes_sep_buf A a (bytesMergeOutCap 0#64 bs.length) ptr bs]
  refine Entails.sepExists_right
    (vecHeaderBytes (bytesMergeOutCap 0#64 bs.length) ptr (BitVec.ofNat 64 bs.length)) ?_
  refine Entails.sepExists_right
    (vecU8Buf A (bytesMergeOutCap 0#64 bs.length) ptr bs) ?_
  refine Entails.pure_right ⟨by simp [vecHeaderBytes], fun b => ?_⟩ (Entails.refl _)
  rw [← vecU8At_eq_bytes_sep_buf A b (bytesMergeOutCap 0#64 bs.length) ptr bs]
  exact Entails.sepExists_right ptr (Entails.refl _)

/-- Capacity-explicit `prostMsgKeyAt` (104 bytes) where empty sub-vectors have `cap = 0` and
`mk.seed` has deterministic capacity `bytesMergeOutCap 0#64 mk.seed.length`. -/
def prostMsgKeyAtCap (A : RustAlloc) (mk : MessageKeyGenerator) (a : BitVec 64) : SepProp :=
  vecU8FreshCap A a [] ∗ vecU8FreshCap A (a + 24#64) [] ∗
    vecU8FreshCap A (a + 48#64) [] ∗ vecU8FreshCap A (a + 72#64) mk.seed ∗
    ((a + 96#64) ↦₃₂ mk.counter) ∗ memRegion (a + 100#64) 4

theorem prostMsgKeyAtCap_entails_prostMsgKeyAt (A : RustAlloc) (mk : MessageKeyGenerator)
    (a : BitVec 64) :
    prostMsgKeyAtCap A mk a ⊢ prostMsgKeyAt A mk a := by
  unfold prostMsgKeyAtCap prostMsgKeyAt
  exact sepConj_mono (vecU8FreshCap_entails_vecU8 A a [])
    (sepConj_mono (vecU8FreshCap_entails_vecU8 A (a + 24#64) [])
      (sepConj_mono (vecU8FreshCap_entails_vecU8 A (a + 48#64) [])
        (sepConj_mono (vecU8FreshCap_entails_vecU8 A (a + 72#64) mk.seed)
          (Entails.refl _))))

theorem arrayAt_prostMsgKeyAtCap_entails (A : RustAlloc) (keys : List MessageKeyGenerator)
    (ptr : BitVec 64) :
    arrayAt (fun mk b => prostMsgKeyAtCap A mk b) 104 ptr keys ⊢
      arrayAt (fun mk b => prostMsgKeyAt A mk b) 104 ptr keys := by
  induction keys generalizing ptr with
  | nil => exact Entails.refl _
  | cons mk rest ih =>
    simp only [arrayAt]
    exact sepConj_mono (prostMsgKeyAtCap_entails_prostMsgKeyAt A mk ptr)
      (ih (ptr + BitVec.ofNat 64 104))

theorem prostMsgKeyAtCap_move_bytes (A : RustAlloc) (mk : MessageKeyGenerator) (a : BitVec 64) :
    prostMsgKeyAtCap A mk a ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜bs.length = 104 ∧
          ∀ b : BitVec 64, ((b ↦ₛ bs) ∗ H) ⊢ prostMsgKeyAtCap A mk b⌝ ∗
        (a ↦ₛ bs) ∗ H := by
  have heq : ∀ b : BitVec 64,
      prostMsgKeyAtCap A mk b =
        (vecU8FreshCap A b [] ∗
          (vecU8FreshCap A (b + 24#64) [] ∗
            (vecU8FreshCap A ((b + 24#64) + 24#64) [] ∗
              (vecU8FreshCap A (((b + 24#64) + 24#64) + 24#64) mk.seed ∗
                ((((((b + 24#64) + 24#64) + 24#64) + 24#64) ↦₃₂ mk.counter) ∗
                  memRegion (((((b + 24#64) + 24#64) + 24#64) + 24#64) + 4#64) 4))))) := by
    intro b
    unfold prostMsgKeyAtCap
    have e48 : (b + 24#64) + 24#64 = b + 48#64 := by rw [BitVec.add_assoc]; rfl
    have e72 : (b + 48#64) + 24#64 = b + 72#64 := by rw [BitVec.add_assoc]; rfl
    have e96 : (b + 72#64) + 24#64 = b + 96#64 := by rw [BitVec.add_assoc]; rfl
    have e100 : (b + 96#64) + 4#64 = b + 100#64 := by rw [BitVec.add_assoc]; rfl
    rw [e48, e72, e96, e100]
  have hm4 := move_bytes_pair_receiverChains
    (P1 := fun b => vecU8FreshCap A b mk.seed)
    (P2 := fun b => (b ↦₃₂ mk.counter) ∗ memRegion (b + 4#64) 4)
    (n1 := 24) (n2 := 8) (off := 24#64) rfl
    (vecU8FreshCap_move_bytes A mk.seed)
    (prostCkTailSome_move_bytes_receiverChains mk.counter)
  have hm3 := move_bytes_pair_receiverChains
    (P1 := fun b => vecU8FreshCap A b [])
    (P2 := fun b => vecU8FreshCap A b mk.seed ∗
      (((b + 24#64) ↦₃₂ mk.counter) ∗ memRegion ((b + 24#64) + 4#64) 4))
    (n1 := 24) (n2 := 32) (off := 24#64) rfl
    (vecU8FreshCap_move_bytes A []) hm4
  have hm2 := move_bytes_pair_receiverChains
    (P1 := fun b => vecU8FreshCap A b [])
    (P2 := fun b => vecU8FreshCap A b [] ∗
      (vecU8FreshCap A (b + 24#64) mk.seed ∗
        ((((b + 24#64) + 24#64) ↦₃₂ mk.counter) ∗
          memRegion (((b + 24#64) + 24#64) + 4#64) 4)))
    (n1 := 24) (n2 := 56) (off := 24#64) rfl
    (vecU8FreshCap_move_bytes A []) hm3
  have hm1 := move_bytes_pair_receiverChains
    (P1 := fun b => vecU8FreshCap A b [])
    (P2 := fun b => vecU8FreshCap A b [] ∗
      (vecU8FreshCap A (b + 24#64) [] ∗
        (vecU8FreshCap A ((b + 24#64) + 24#64) mk.seed ∗
          (((((b + 24#64) + 24#64) + 24#64) ↦₃₂ mk.counter) ∗
            memRegion ((((b + 24#64) + 24#64) + 24#64) + 4#64) 4))))
    (n1 := 24) (n2 := 80) (off := 24#64) rfl
    (vecU8FreshCap_move_bytes A []) hm2 a
  simp only [show (24 : Nat) + (24 + (24 + (24 + 8))) = 104 from rfl,
    show (24 : Nat) + (24 + (24 + 8)) = 80 from rfl,
    show (24 : Nat) + (24 + 8) = 56 from rfl,
    show (24 : Nat) + 8 = 32 from rfl, ← heq] at hm1
  exact hm1

theorem prostMsgKeyAtCap_move_chunks104 (A : RustAlloc) (a : BitVec 64)
    (mk : MessageKeyGenerator) :
    prostMsgKeyAtCap A mk a ⊢
      ∃∗ q0 : BitVec 128, ∃∗ q1 : BitVec 128, ∃∗ q2 : BitVec 128,
      ∃∗ q3 : BitVec 128, ∃∗ q4 : BitVec 128, ∃∗ q5 : BitVec 128,
      ∃∗ w6 : BitVec 64, ∃∗ H : SepProp,
        ⌜∀ b : BitVec 64, (chunks104_6QWAt b q0 q1 q2 q3 q4 q5 w6 ∗ H) ⊢
          prostMsgKeyAtCap A mk b⌝ ∗
        chunks104_6QWAt a q0 q1 q2 q3 q4 q5 w6 ∗ H := by
  refine Entails.trans (prostMsgKeyAtCap_move_bytes A mk a) ?_
  apply Entails.sepExists_elim; intro bs
  apply Entails.sepExists_elim; intro H
  apply Entails.pure_left; rintro ⟨hlen, hmov⟩
  obtain ⟨q0, q1, q2, q3, q4, q5, w6, _, hchunks⟩ := exists_bytes104Of6QW hlen
  rw [hchunks a]
  refine Entails.sepExists_right q0 (Entails.sepExists_right q1
    (Entails.sepExists_right q2 (Entails.sepExists_right q3
      (Entails.sepExists_right q4 (Entails.sepExists_right q5
        (Entails.sepExists_right w6 (Entails.sepExists_right H ?_)))))))
  exact Entails.pure_right (fun b => by rw [← hchunks b]; exact hmov b) (Entails.refl _)

theorem arrayAt_prostMsgKeyAtCap_move_bytes (A : RustAlloc) (keys : List MessageKeyGenerator)
    (ptr : BitVec 64) :
    arrayAt (fun mk b => prostMsgKeyAtCap A mk b) 104 ptr keys ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜bs.length = keys.length * 104 ∧
          ∀ q : BitVec 64, ((q ↦ₛ bs) ∗ H) ⊢
            arrayAt (fun mk b => prostMsgKeyAtCap A mk b) 104 q keys⌝ ∗
        (ptr ↦ₛ bs) ∗ H := by
  induction keys generalizing ptr with
  | nil =>
    simp only [arrayAt, List.length_nil, Nat.zero_mul]
    refine Entails.sepExists_right [] (Entails.sepExists_right emp ?_)
    rw [pointsToBytes_nil, emp_sepConj]
    exact Entails.pure_right ⟨rfl, fun _ => by rw [pointsToBytes_nil, emp_sepConj]; exact Entails.refl _⟩
      (Entails.refl _)
  | cons mk rest ih =>
    simp only [arrayAt, List.length_cons]
    have hm := move_bytes_pair_receiverChains
      (P1 := fun b => prostMsgKeyAtCap A mk b)
      (P2 := fun b => arrayAt (fun m x => prostMsgKeyAtCap A m x) 104 b rest)
      (n1 := 104) (n2 := rest.length * 104) (off := BitVec.ofNat 64 104) rfl
      (prostMsgKeyAtCap_move_bytes A mk) ih ptr
    have hmul : 104 + rest.length * 104 = (rest.length + 1) * 104 := by omega
    rwa [hmul] at hm

/-- Capacity-explicit `prostChainGAt` (104 bytes) tracking `capMk : Nat` on `c.keys` (`a + 0x30`)
and `vecU8FreshCap` on `c.srk`, `c.priv`, and `c.ck`. -/
def prostChainGAtCap (A : RustAlloc) (a : BitVec 64) (capMk : Nat) (c : ChainG) : SepProp :=
  vecU8FreshCap A a c.srk ∗ vecU8FreshCap A (a + 0x18#64) c.priv ∗
    (∃∗ ptrMk : BitVec 64,
      vecAt A 104 8 (fun mk b => prostMsgKeyAtCap A mk b)
        (a + 0x30#64) (BitVec.ofNat 64 capMk) ptrMk c.keys) ∗
    match c.ck with
    | none => ((a + 0x48#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x50#64) 24
    | some (i, k) => vecU8FreshCap A (a + 0x48#64) k ∗ ((a + 0x60#64) ↦₃₂ i) ∗
        memRegion (a + 0x64#64) 4

theorem prostChainGAtCap_entails_prostChainGAt (A : RustAlloc) (a : BitVec 64)
    (capMk : Nat) (c : ChainG) :
    prostChainGAtCap A a capMk c ⊢ prostChainGAt A a c := by
  unfold prostChainGAtCap prostChainGAt
  refine sepConj_mono (vecU8FreshCap_entails_vecU8 A a c.srk)
    (sepConj_mono (vecU8FreshCap_entails_vecU8 A (a + 0x18#64) c.priv)
      (sepConj_mono ?_ ?_))
  · unfold vecOf
    apply Entails.sepExists_elim; intro ptrMk
    refine Entails.sepExists_right (BitVec.ofNat 64 capMk)
      (Entails.sepExists_right ptrMk ?_)
    unfold vecAt vecBuf
    refine sepConj_mono_right (sepConj_mono_right ?_)
    split
    · exact Entails.refl _
    · exact sepConj_mono_right (sepConj_mono_left (arrayAt_prostMsgKeyAtCap_entails A c.keys ptrMk))
  · cases c.ck with
    | none => exact Entails.refl _
    | some ik =>
      rcases ik with ⟨i, k⟩
      exact sepConj_mono_left (vecU8FreshCap_entails_vecU8 A (a + 0x48#64) k)

theorem prostChainGAtCap_move_bytes (A : RustAlloc) (capMk : Nat) (c : ChainG) (a : BitVec 64) :
    prostChainGAtCap A a capMk c ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜bs.length = 104 ∧
          ∀ b : BitVec 64, ((b ↦ₛ bs) ∗ H) ⊢ prostChainGAtCap A b capMk c⌝ ∗
        (a ↦ₛ bs) ∗ H := by
  have hkeys : ∀ b : BitVec 64,
      (∃∗ ptrMk : BitVec 64,
        vecAt A 104 8 (fun mk p => prostMsgKeyAtCap A mk p)
          b (BitVec.ofNat 64 capMk) ptrMk c.keys) ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜bs.length = 24 ∧ ∀ q : BitVec 64, ((q ↦ₛ bs) ∗ H) ⊢
          (∃∗ ptrMk : BitVec 64,
            vecAt A 104 8 (fun mk p => prostMsgKeyAtCap A mk p)
              q (BitVec.ofNat 64 capMk) ptrMk c.keys)⌝ ∗
        (b ↦ₛ bs) ∗ H := by
    intro b
    apply Entails.sepExists_elim; intro ptrMk
    rw [vecAt_eq_bytes_sep_buf A 104 8 (fun mk p => prostMsgKeyAtCap A mk p)
      b (BitVec.ofNat 64 capMk) ptrMk c.keys]
    refine Entails.sepExists_right
      (vecHeaderBytes (BitVec.ofNat 64 capMk) ptrMk (BitVec.ofNat 64 c.keys.length))
      (Entails.sepExists_right
        (vecBuf A 104 8 (fun mk p => prostMsgKeyAtCap A mk p)
          (BitVec.ofNat 64 capMk) ptrMk c.keys) ?_)
    refine Entails.pure_right ⟨by simp [vecHeaderBytes], fun q => ?_⟩ (Entails.refl _)
    rw [← vecAt_eq_bytes_sep_buf A 104 8 (fun mk p => prostMsgKeyAtCap A mk p)
      q (BitVec.ofNat 64 capMk) ptrMk c.keys]
    exact Entails.sepExists_right ptrMk (Entails.refl _)
  let ckPred : BitVec 64 → SepProp := fun b =>
    match c.ck with
    | none => (b ↦₆₄ noneCap) ∗ memRegion (b + 8#64) 24
    | some (i, k) => vecU8FreshCap A b k ∗ ((b + 0x18#64) ↦₃₂ i) ∗ memRegion (b + 0x1c#64) 4
  have hck : ∀ b : BitVec 64, ckPred b ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜bs.length = 32 ∧ ∀ q : BitVec 64, ((q ↦ₛ bs) ∗ H) ⊢ ckPred q⌝ ∗
        (b ↦ₛ bs) ∗ H := by
    intro b
    dsimp only [ckPred]
    cases c.ck with
    | none =>
      rw [pointsTo64_eq_pointsToBytes, memRegion_eq_exists_bytes (b + 8#64) 24 (by decide),
        sepExists_sepConj_right]
      apply Entails.sepExists_elim; intro pad
      rw [sepConj_pure_left_comm]
      apply Entails.pure_left; intro hpad
      have h8 : b + 8#64 = b + BitVec.ofNat 64 (unpack64 noneCap).length := rfl
      rw [h8, ← pointsToBytes_append]
      refine Entails.sepExists_right (unpack64 noneCap ++ pad)
        (Entails.sepExists_right emp ?_)
      rw [sepConj_emp]
      refine Entails.pure_right ⟨by simp [hpad], fun q => ?_⟩ (Entails.refl _)
      rw [sepConj_emp, pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes]
      apply sepConj_mono_right
      have hm := pointsToBytes_entails_memRegion (q + 8#64) pad
      rwa [hpad] at hm
    | some ik =>
      rcases ik with ⟨i, k⟩
      have heq_ck : ∀ q : BitVec 64,
          (vecU8FreshCap A q k ∗ ((q + 0x18#64) ↦₃₂ i) ∗ memRegion (q + 0x1c#64) 4) =
          (vecU8FreshCap A q k ∗ (((q + 0x18#64) ↦₃₂ i) ∗ memRegion ((q + 0x18#64) + 4#64) 4)) := by
        intro q
        have e1c : (q + 0x18#64) + 4#64 = q + 0x1c#64 := by rw [BitVec.add_assoc]; rfl
        rw [e1c]
      have hm := move_bytes_pair_receiverChains
        (P1 := fun q => vecU8FreshCap A q k)
        (P2 := fun q => (q ↦₃₂ i) ∗ memRegion (q + 4#64) 4)
        (n1 := 24) (n2 := 8) (off := 0x18#64) rfl
        (vecU8FreshCap_move_bytes A k)
        (prostCkTailSome_move_bytes_receiverChains i) b
      simp only [show (24 : Nat) + 8 = 32 from rfl, ← heq_ck] at hm
      exact hm
  have heq : ∀ b : BitVec 64,
      prostChainGAtCap A b capMk c =
        (vecU8FreshCap A b c.srk ∗
          (vecU8FreshCap A (b + 0x18#64) c.priv ∗
            ((∃∗ ptrMk : BitVec 64,
              vecAt A 104 8 (fun mk p => prostMsgKeyAtCap A mk p)
                ((b + 0x18#64) + 0x18#64) (BitVec.ofNat 64 capMk) ptrMk c.keys) ∗
              ckPred (((b + 0x18#64) + 0x18#64) + 0x18#64)))) := by
    intro b
    unfold prostChainGAtCap
    dsimp only [ckPred]
    have e30 : (b + 0x18#64) + 0x18#64 = b + 0x30#64 := by rw [BitVec.add_assoc]; rfl
    have e48 : (b + 0x30#64) + 0x18#64 = b + 0x48#64 := by rw [BitVec.add_assoc]; rfl
    have e50 : (b + 0x48#64) + 8#64 = b + 0x50#64 := by rw [BitVec.add_assoc]; rfl
    have e60 : (b + 0x48#64) + 0x18#64 = b + 0x60#64 := by rw [BitVec.add_assoc]; rfl
    have e64 : (b + 0x48#64) + 0x1c#64 = b + 0x64#64 := by rw [BitVec.add_assoc]; rfl
    rw [e30, e48, e50, e60, e64]
  have hm3 := move_bytes_pair_receiverChains (n1 := 24) (n2 := 32) (off := 0x18#64) rfl hkeys hck
  have hm2 := move_bytes_pair_receiverChains
    (P1 := fun b => vecU8FreshCap A b c.priv)
    (n1 := 24) (n2 := 56) (off := 0x18#64) rfl
    (vecU8FreshCap_move_bytes A c.priv) hm3
  have hm1 := move_bytes_pair_receiverChains
    (P1 := fun b => vecU8FreshCap A b c.srk)
    (n1 := 24) (n2 := 80) (off := 0x18#64) rfl
    (vecU8FreshCap_move_bytes A c.srk) hm2 a
  simp only [show (24 : Nat) + (24 + (24 + 32)) = 104 from rfl,
    show (24 : Nat) + (24 + 32) = 80 from rfl,
    show (24 : Nat) + 32 = 56 from rfl, ← heq] at hm1
  exact hm1

theorem prostChainGAtCap_move_chunks104 (A : RustAlloc) (capMk : Nat) (c : ChainG)
    (a : BitVec 64) :
    prostChainGAtCap A a capMk c ⊢
      ∃∗ q0 : BitVec 128, ∃∗ q1 : BitVec 128, ∃∗ q2 : BitVec 128,
      ∃∗ q3 : BitVec 128, ∃∗ q4 : BitVec 128, ∃∗ q5 : BitVec 128,
      ∃∗ w6 : BitVec 64, ∃∗ H : SepProp,
        ⌜∀ b : BitVec 64, (chunks104_6QWAt b q0 q1 q2 q3 q4 q5 w6 ∗ H) ⊢
          prostChainGAtCap A b capMk c⌝ ∗
        chunks104_6QWAt a q0 q1 q2 q3 q4 q5 w6 ∗ H := by
  refine Entails.trans (prostChainGAtCap_move_bytes A capMk c a) ?_
  apply Entails.sepExists_elim; intro bs
  apply Entails.sepExists_elim; intro H
  apply Entails.pure_left; rintro ⟨hlen, hmov⟩
  obtain ⟨q0, q1, q2, q3, q4, q5, w6, _, hchunks⟩ := exists_bytes104Of6QW hlen
  rw [hchunks a]
  refine Entails.sepExists_right q0 (Entails.sepExists_right q1
    (Entails.sepExists_right q2 (Entails.sepExists_right q3
      (Entails.sepExists_right q4 (Entails.sepExists_right q5
        (Entails.sepExists_right w6 (Entails.sepExists_right H ?_)))))))
  exact Entails.pure_right (fun b => by rw [← hchunks b]; exact hmov b) (Entails.refl _)


def prostChainGRestCap (A : RustAlloc) (a : BitVec 64) (c : ChainG) : SepProp :=
  vecU8FreshCap A a c.srk ∗ vecU8FreshCap A (a + 0x18#64) c.priv ∗
    match c.ck with
    | none => ((a + 0x48#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x50#64) 24
    | some (i, k) => vecU8FreshCap A (a + 0x48#64) k ∗ ((a + 0x60#64) ↦₃₂ i) ∗
        memRegion (a + 0x64#64) 4

theorem prostChainGAtCap_eq_keys_sep_rest (A : RustAlloc) (a : BitVec 64)
    (capMk : Nat) (c : ChainG) :
    prostChainGAtCap A a capMk c =
      (∃∗ ptrMk : BitVec 64,
        vecAt A 104 8 (fun mk b => prostMsgKeyAtCap A mk b)
          (a + 0x30#64) (BitVec.ofNat 64 capMk) ptrMk c.keys) ∗
      prostChainGRestCap A a c := by
  unfold prostChainGAtCap prostChainGRestCap
  sep_ac_rfl

theorem prostChainGRestCap_update_keys (A : RustAlloc) (a : BitVec 64) (c : ChainG)
    (ks : List MessageKeyGenerator) :
    prostChainGRestCap A a { c with keys := ks } = prostChainGRestCap A a c := rfl

theorem prostChainGAtCap_empty_of_cells (A : RustAlloc) (a p0 p1 p2 : BitVec 64)
    (hp0 : p0 ≠ 0) (hp1 : p1 ≠ 0) (hp2 : p2 ≠ 0) :
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ p0) ∗ ((a + 0x10#64) ↦₆₄ 0#64) ∗
      ((a + 0x18#64) ↦₆₄ 0#64) ∗ ((a + 0x20#64) ↦₆₄ p1) ∗ ((a + 0x28#64) ↦₆₄ 0#64) ∗
      ((a + 0x30#64) ↦₆₄ 0#64) ∗ ((a + 0x38#64) ↦₆₄ p2) ∗ ((a + 0x40#64) ↦₆₄ 0#64) ∗
      ((a + 0x48#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x50#64) 24 ⊢
      prostChainGAtCap A a 0 ChainG.empty := by
  have v0 := emptyCells_entails_vecU8FreshCap A a p0 hp0
  have v1 := emptyCells_entails_vecU8FreshCap A (a + 0x18#64) p1 hp1
  have e20 : (a + 0x18#64) + 8#64 = a + 0x20#64 := by rw [BitVec.add_assoc]; rfl
  have e28 : (a + 0x18#64) + 16#64 = a + 0x28#64 := by rw [BitVec.add_assoc]; rfl
  rw [e20, e28] at v1
  have v2 : ((a + 0x30#64) ↦₆₄ 0#64) ∗ ((a + 0x38#64) ↦₆₄ p2) ∗ ((a + 0x40#64) ↦₆₄ 0#64) ⊢
      ∃∗ ptrMk : BitVec 64,
        vecAt A 104 8 (fun mk b => prostMsgKeyAtCap A mk b) (a + 0x30#64) 0#64 ptrMk [] := by
    refine Entails.sepExists_right p2 ?_
    refine Entails.trans ?_
      (Entails.of_eq (?_ :
        ⌜(0 : Nat) ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * 104 < 2 ^ 63 ∧ p2 ≠ 0⌝ ∗
          (((a + 0x30#64) ↦₆₄ 0#64) ∗ ((a + 0x38#64) ↦₆₄ p2) ∗ ((a + 0x40#64) ↦₆₄ 0#64)) = _))
    · exact Entails.pure_right ⟨by decide, by decide, hp2⟩ (Entails.refl _)
    · unfold vecAt vecHeader vecBuf
      have e38 : (a + 0x30#64) + 8#64 = a + 0x38#64 := by rw [BitVec.add_assoc]; rfl
      have e40 : (a + 0x30#64) + 16#64 = a + 0x40#64 := by rw [BitVec.add_assoc]; rfl
      have hite : (if (0#64 : BitVec 64) = 0 then emp else
          A.live p2 ((0#64 : BitVec 64).toNat * 104) 8 ∗
            arrayAt (fun mk b => prostMsgKeyAtCap A mk b) 104 p2 [] ∗
            memRegion (p2 + BitVec.ofNat 64 (([] : List MessageKeyGenerator).length * 104))
              (((0#64 : BitVec 64).toNat - ([] : List MessageKeyGenerator).length) * 104)) = emp := rfl
      have h0 : BitVec.ofNat 64 ([] : List MessageKeyGenerator).length = 0#64 := rfl
      rw [e38, e40, hite, h0, List.length_nil, sepConj_emp]
      sep_ac_rfl
  unfold prostChainGAtCap ChainG.empty
  dsimp only [BitVec.ofNat_eq_ofNat]
  have hgrp :
      (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ p0) ∗ ((a + 0x10#64) ↦₆₄ 0#64) ∗
        ((a + 0x18#64) ↦₆₄ 0#64) ∗ ((a + 0x20#64) ↦₆₄ p1) ∗ ((a + 0x28#64) ↦₆₄ 0#64) ∗
        ((a + 0x30#64) ↦₆₄ 0#64) ∗ ((a + 0x38#64) ↦₆₄ p2) ∗ ((a + 0x40#64) ↦₆₄ 0#64) ∗
        ((a + 0x48#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x50#64) 24 =
      ((a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ p0) ∗ ((a + 0x10#64) ↦₆₄ 0#64)) ∗
      (((a + 0x18#64) ↦₆₄ 0#64) ∗ ((a + 0x20#64) ↦₆₄ p1) ∗ ((a + 0x28#64) ↦₆₄ 0#64)) ∗
      (((a + 0x30#64) ↦₆₄ 0#64) ∗ ((a + 0x38#64) ↦₆₄ p2) ∗ ((a + 0x40#64) ↦₆₄ 0#64)) ∗
      (((a + 0x48#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x50#64) 24) := by sep_ac_rfl
  rw [hgrp]
  exact sepConj_mono v0 (sepConj_mono v1 (sepConj_mono v2 (Entails.refl _)))

theorem msgKeyCap_default_of_cells (A : RustAlloc) (sp0 : BitVec 64) :
    ((sp0 - 248#64) ↦₆₄ 0#64) ∗ ((sp0 - 240#64) ↦₆₄ 1#64) ∗ ((sp0 - 232#64) ↦₆₄ 0#64) ∗
      ((sp0 - 224#64) ↦₆₄ 0#64) ∗ ((sp0 - 216#64) ↦₆₄ 1#64) ∗ ((sp0 - 208#64) ↦₆₄ 0#64) ∗
      ((sp0 - 200#64) ↦₆₄ 0#64) ∗ ((sp0 - 192#64) ↦₆₄ 1#64) ∗ ((sp0 - 184#64) ↦₆₄ 0#64) ∗
      ((sp0 - 176#64) ↦₆₄ 0#64) ∗ ((sp0 - 168#64) ↦₆₄ 1#64) ∗ ((sp0 - 160#64) ↦₆₄ 0#64) ⊢
    vecU8FreshCap A (sp0 - 248#64) [] ∗ vecU8FreshCap A (sp0 - 224#64) [] ∗
      vecU8FreshCap A (sp0 - 200#64) [] ∗ vecU8FreshCap A (sp0 - 176#64) [] := by
  have v0 := emptyCells_entails_vecU8FreshCap A (sp0 - 248#64) 1#64 (by decide)
  have v1 := emptyCells_entails_vecU8FreshCap A (sp0 - 224#64) 1#64 (by decide)
  have v2 := emptyCells_entails_vecU8FreshCap A (sp0 - 200#64) 1#64 (by decide)
  have v3 := emptyCells_entails_vecU8FreshCap A (sp0 - 176#64) 1#64 (by decide)
  have e0a : (sp0 - 248#64) + 8#64 = sp0 - 240#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e0b : (sp0 - 248#64) + 16#64 = sp0 - 232#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e1a : (sp0 - 224#64) + 8#64 = sp0 - 216#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e1b : (sp0 - 224#64) + 16#64 = sp0 - 208#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e2a : (sp0 - 200#64) + 8#64 = sp0 - 192#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e2b : (sp0 - 200#64) + 16#64 = sp0 - 184#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e3a : (sp0 - 176#64) + 8#64 = sp0 - 168#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e3b : (sp0 - 176#64) + 16#64 = sp0 - 160#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [e0a, e0b] at v0; rw [e1a, e1b] at v1; rw [e2a, e2b] at v2; rw [e3a, e3b] at v3
  have hgrp :
      ((sp0 - 248#64) ↦₆₄ 0#64) ∗ ((sp0 - 240#64) ↦₆₄ 1#64) ∗ ((sp0 - 232#64) ↦₆₄ 0#64) ∗
        ((sp0 - 224#64) ↦₆₄ 0#64) ∗ ((sp0 - 216#64) ↦₆₄ 1#64) ∗ ((sp0 - 208#64) ↦₆₄ 0#64) ∗
        ((sp0 - 200#64) ↦₆₄ 0#64) ∗ ((sp0 - 192#64) ↦₆₄ 1#64) ∗ ((sp0 - 184#64) ↦₆₄ 0#64) ∗
        ((sp0 - 176#64) ↦₆₄ 0#64) ∗ ((sp0 - 168#64) ↦₆₄ 1#64) ∗ ((sp0 - 160#64) ↦₆₄ 0#64) =
      (((sp0 - 248#64) ↦₆₄ 0#64) ∗ ((sp0 - 240#64) ↦₆₄ 1#64) ∗ ((sp0 - 232#64) ↦₆₄ 0#64)) ∗
      ((((sp0 - 224#64) ↦₆₄ 0#64) ∗ ((sp0 - 216#64) ↦₆₄ 1#64) ∗ ((sp0 - 208#64) ↦₆₄ 0#64)) ∗
      ((((sp0 - 200#64) ↦₆₄ 0#64) ∗ ((sp0 - 192#64) ↦₆₄ 1#64) ∗ ((sp0 - 184#64) ↦₆₄ 0#64)) ∗
       (((sp0 - 176#64) ↦₆₄ 0#64) ∗ ((sp0 - 168#64) ↦₆₄ 1#64) ∗ ((sp0 - 160#64) ↦₆₄ 0#64)))) := by sep_ac_rfl
  rw [hgrp]
  exact sepConj_mono v0 (sepConj_mono v1 (sepConj_mono v2 v3))

theorem prostMsgKeyAtCap_fold (A : RustAlloc) (sp0 : BitVec 64) (mk : MessageKeyGenerator) :
    vecU8FreshCap A (sp0 - 248#64) [] ∗ vecU8FreshCap A (sp0 - 224#64) [] ∗
      vecU8FreshCap A (sp0 - 200#64) [] ∗ vecU8FreshCap A (sp0 - 176#64) mk.seed ∗
      ((sp0 - 152#64) ↦₃₂ mk.counter) ∗ memRegion (sp0 - 148#64) 4 =
      prostMsgKeyAtCap A mk (sp0 - 248#64) := by
  unfold prostMsgKeyAtCap
  have e24 : (sp0 - 248#64) + 24#64 = sp0 - 224#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e48 : (sp0 - 248#64) + 48#64 = sp0 - 200#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e72 : (sp0 - 248#64) + 72#64 = sp0 - 176#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e96 : (sp0 - 248#64) + 96#64 = sp0 - 152#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e100 : (sp0 - 248#64) + 100#64 = sp0 - 148#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [e24, e48, e72, e96, e100]

private theorem arrayAt_prostMsgKeyAtCap_concat (A : RustAlloc) (keys : List MessageKeyGenerator)
    (mk : MessageKeyGenerator) (ptr : BitVec 64) :
    arrayAt (fun m b => prostMsgKeyAtCap A m b) 104 ptr (keys ++ [mk]) =
      arrayAt (fun m b => prostMsgKeyAtCap A m b) 104 ptr keys ∗
        prostMsgKeyAtCap A mk (ptr + BitVec.ofNat 64 (keys.length * 104)) := by
  induction keys generalizing ptr with
  | nil =>
    simp only [List.nil_append, arrayAt, List.length_nil, Nat.zero_mul,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, sepConj_emp, emp_sepConj]
  | cons hd tl ih =>
    simp only [List.cons_append, arrayAt, List.length_cons, ih]
    have haddr : ptr + BitVec.ofNat 64 104 + BitVec.ofNat 64 (tl.length * 104) =
        ptr + BitVec.ofNat 64 ((tl.length + 1) * 104) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
    rw [haddr]; sep_ac_rfl

theorem vecAt_keys_open (A : RustAlloc) (a cap : BitVec 64) (keys : List MessageKeyGenerator) :
    (∃∗ ptr : BitVec 64,
      vecAt A 104 8 (fun mk b => prostMsgKeyAtCap A mk b) (a + 0x30#64) cap ptr keys) ⊢
      ∃∗ ptr : BitVec 64,
        ⌜keys.length ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        ((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗
        ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length) ∗
        (if cap = 0 then emp else A.live ptr (cap.toNat * 104) 8) ∗
        arrayAt (fun mk b => prostMsgKeyAtCap A mk b) 104 ptr keys ∗
        (if cap = 0#64 then emp
         else memRegion (ptr + BitVec.ofNat 64 (keys.length * 104)) ((cap.toNat - keys.length) * 104)) := by
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right ptr ?_
  unfold vecAt vecHeader vecBuf
  have e38 : (a + 0x30#64) + 8#64 = a + 0x38#64 := by rw [BitVec.add_assoc]; rfl
  have e40 : (a + 0x30#64) + 16#64 = a + 0x40#64 := by rw [BitVec.add_assoc]; rfl
  rw [e38, e40]
  have hpure :
      (((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗ ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length)) ∗
      (⌜keys.length ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (if cap = 0 then emp
         else A.live ptr (cap.toNat * 104) 8 ∗
           arrayAt (fun mk b => prostMsgKeyAtCap A mk b) 104 ptr keys ∗
           memRegion (ptr + BitVec.ofNat 64 (keys.length * 104)) ((cap.toNat - keys.length) * 104))) =
      ⌜keys.length ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗ ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length) ∗
        (if cap = 0 then emp
         else A.live ptr (cap.toNat * 104) 8 ∗
           arrayAt (fun mk b => prostMsgKeyAtCap A mk b) 104 ptr keys ∗
           memRegion (ptr + BitVec.ofNat 64 (keys.length * 104)) ((cap.toNat - keys.length) * 104))) := by sep_ac_rfl
  rw [hpure]
  apply Entails.pure_left; rintro ⟨hlen, hcap_lt, hptr⟩
  refine Entails.pure_right ⟨hlen, hcap_lt, hptr⟩ ?_
  by_cases h0 : cap = 0#64
  · subst h0
    have hnil : keys = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst hnil
    change (((a + 0x30#64) ↦₆₄ 0#64) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗ ((a + 0x40#64) ↦₆₄ 0#64) ∗
      (if (0#64 : BitVec 64) = 0#64 then emp else _)) ⊢ _
    simp only [↓reduceIte, arrayAt, sepConj_emp]
    exact Entails.of_eq (by sep_ac_rfl)
  · have h0' : cap ≠ 0 := h0
    simp only [h0, h0', ↓reduceIte]
    exact Entails.of_eq (by sep_ac_rfl)

theorem vecAt_keys_push_fold (A : RustAlloc) (a cap ptr : BitVec 64)
    (keys : List MessageKeyGenerator) (mk : MessageKeyGenerator)
    (hcap_le : keys.length + 1 ≤ cap.toNat) (hcap_lt : cap.toNat * 104 < 2 ^ 63)
    (hptr : ptr ≠ 0) :
    ((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗
      ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 (keys.length + 1)) ∗
      A.live ptr (cap.toNat * 104) 8 ∗
      arrayAt (fun m b => prostMsgKeyAtCap A m b) 104 ptr keys ∗
      prostMsgKeyAtCap A mk (ptr + BitVec.ofNat 64 (keys.length * 104)) ∗
      memRegion (ptr + BitVec.ofNat 64 ((keys.length + 1) * 104)) ((cap.toNat - (keys.length + 1)) * 104) ⊢
      ∃∗ ptrMk : BitVec 64,
        vecAt A 104 8 (fun m b => prostMsgKeyAtCap A m b) (a + 0x30#64) cap ptrMk (keys ++ [mk]) := by
  have hne0 : cap ≠ 0 := by intro h0; subst h0; simp at hcap_le
  have hlen : (keys ++ [mk]).length = keys.length + 1 := by simp
  refine Entails.sepExists_right ptr ?_
  unfold vecAt vecHeader vecBuf
  have e38 : (a + 0x30#64) + 8#64 = a + 0x38#64 := by rw [BitVec.add_assoc]; rfl
  have e40 : (a + 0x30#64) + 16#64 = a + 0x40#64 := by rw [BitVec.add_assoc]; rfl
  rw [e38, e40, hlen, arrayAt_prostMsgKeyAtCap_concat]
  simp only [hne0, ↓reduceIte]
  have hgrp :
      (((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗
        ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 (keys.length + 1))) ∗
      (⌜keys.length + 1 ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (A.live ptr (cap.toNat * 104) 8 ∗
          (arrayAt (fun m b => prostMsgKeyAtCap A m b) 104 ptr keys ∗
            prostMsgKeyAtCap A mk (ptr + BitVec.ofNat 64 (keys.length * 104))) ∗
          memRegion (ptr + BitVec.ofNat 64 ((keys.length + 1) * 104))
            ((cap.toNat - (keys.length + 1)) * 104))) =
      ⌜keys.length + 1 ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗
        ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 (keys.length + 1)) ∗
        A.live ptr (cap.toNat * 104) 8 ∗
        arrayAt (fun m b => prostMsgKeyAtCap A m b) 104 ptr keys ∗
        prostMsgKeyAtCap A mk (ptr + BitVec.ofNat 64 (keys.length * 104)) ∗
        memRegion (ptr + BitVec.ofNat 64 ((keys.length + 1) * 104))
          ((cap.toNat - (keys.length + 1)) * 104)) := by sep_ac_rfl
  rw [hgrp]
  exact Entails.pure_right ⟨hcap_le, hcap_lt, hptr⟩ (Entails.refl _)

/-! ## 2. Freshness of `ChainG.fields`, Event Trace & Symbolic Cost Telescope -/

private def isSrkField : ChainField → Bool
  | .srk _ => true | _ => false

private def isPrivField : ChainField → Bool
  | .priv _ => true | _ => false

private theorem countP_isSrk_map_key (ks : List MessageKeyGenerator) :
    (ks.map ChainField.key).countP isSrkField = 0 := by
  induction ks with
  | nil => rfl
  | cons _ _ ih => simp [isSrkField, ih]

private theorem countP_isPriv_map_key (ks : List MessageKeyGenerator) :
    (ks.map ChainField.key).countP isPrivField = 0 := by
  induction ks with
  | nil => rfl
  | cons _ _ ih => simp [isPrivField, ih]

private theorem countP_isSrk_fields_le_one (c : ChainG) :
    c.fields.countP isSrkField ≤ 1 := by
  unfold ChainG.fields
  simp only [List.countP_append, countP_isSrk_map_key, Nat.add_zero]
  rcases c.ck with _ | ⟨i, k⟩ <;> split_ifs <;> simp [isSrkField]

private theorem countP_isPriv_fields_le_one (c : ChainG) :
    c.fields.countP isPrivField ≤ 1 := by
  unfold ChainG.fields
  simp only [List.countP_append, countP_isPriv_map_key, Nat.add_zero]
  rcases c.ck with _ | ⟨i, k⟩ <;> split_ifs <;> simp [isPrivField]

private theorem foldl_srk_of_countP_zero (fs : List ChainField) (acc : ChainG)
    (h0 : fs.countP isSrkField = 0) :
    (fs.foldl ChainG.apply acc).srk = acc.srk := by
  induction fs generalizing acc with
  | nil => rfl
  | cons fl rest ih =>
    cases fl with
    | srk b => simp [isSrkField] at h0
    | priv b => exact ih _ (by simpa [isSrkField] using h0)
    | ck i k => exact ih _ (by simpa [isSrkField] using h0)
    | key mk => exact ih _ (by simpa [isSrkField] using h0)

private theorem foldl_priv_of_countP_zero (fs : List ChainField) (acc : ChainG)
    (h0 : fs.countP isPrivField = 0) :
    (fs.foldl ChainG.apply acc).priv = acc.priv := by
  induction fs generalizing acc with
  | nil => rfl
  | cons fl rest ih =>
    cases fl with
    | srk b => exact ih _ (by simpa [isPrivField] using h0)
    | priv b => simp [isPrivField] at h0
    | ck i k => exact ih _ (by simpa [isPrivField] using h0)
    | key mk => exact ih _ (by simpa [isPrivField] using h0)

theorem chainGAfter_srk_eq_nil {c : ChainG} {k : Nat} {b : List (BitVec 8)}
    (hk : k < c.fields.length) (hfl : c.fields[k]'hk = .srk b) :
    (chainGAfter c k).srk = [] := by
  have hsplit : c.fields = c.fields.take k ++ (c.fields[k]'hk :: c.fields.drop (k + 1)) := by
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  have hcnt := countP_isSrk_fields_le_one c
  rw [hsplit, List.countP_append, List.countP_cons, hfl] at hcnt
  simp only [isSrkField, ↓reduceIte] at hcnt
  exact foldl_srk_of_countP_zero (c.fields.take k) ChainG.empty (by omega)

theorem chainGAfter_priv_eq_nil {c : ChainG} {k : Nat} {b : List (BitVec 8)}
    (hk : k < c.fields.length) (hfl : c.fields[k]'hk = .priv b) :
    (chainGAfter c k).priv = [] := by
  have hsplit : c.fields = c.fields.take k ++ (c.fields[k]'hk :: c.fields.drop (k + 1)) := by
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  have hcnt := countP_isPriv_fields_le_one c
  rw [hsplit, List.countP_append, List.countP_cons, hfl] at hcnt
  simp only [isPrivField, ↓reduceIte] at hcnt
  exact foldl_priv_of_countP_zero (c.fields.take k) ChainG.empty (by omega)

/-- Exact byte-length invariant on a single `ChainField` of a well-formed `ChainG`. -/
def ChainFieldBytesOk : ChainField → Prop
  | .srk b => b.length = 33
  | .priv b => b.length = 32
  | .ck _ key => key.length = 32
  | .key mkg => mkg.seed.length = 32

theorem mem_fields_bytes_le_33 {c : ChainG} (hcOk : c.Ok) {fl : ChainField}
    (hmem : fl ∈ c.fields) :
    ChainFieldBytesOk fl := by
  unfold ChainG.fields at hmem
  simp only [List.mem_append, List.mem_map] at hmem
  rcases hmem with ((h1 | h2) | h3) | ⟨mkg, hmk_mem, rfl⟩
  · split_ifs at h1 with hsrk
    · simp at h1
    · simp only [List.mem_singleton] at h1; subst h1; exact hcOk.1
  · split_ifs at h2 with hpriv
    · simp at h2
    · simp only [List.mem_singleton] at h2; subst h2
      exact hcOk.2.1.resolve_left hpriv
  · rcases hck : c.ck with _ | ⟨i, key⟩
    · simp [hck] at h3
    · simp only [hck, List.mem_singleton] at h3; subst h3
      exact hcOk.2.2.1 (i, key) hck
  · exact hcOk.2.2.2.1 mkg hmk_mem

/-- Allocator events emitted by one field of `c.fields` when `message_keys` currently has
`lenMk` elements (hence capacity `vecCap4Of lenMk`). -/
def chainFieldStepEvents (lenMk : Nat) : ChainField → List AllocEvent
  | .srk b => bytesMergeEvents 0 b.length
  | .priv b => bytesMergeEvents 0 b.length
  | .ck _ key => bytesMergeEvents 0 key.length
  | .key mkg =>
      bytesMergeEvents 0 mkg.seed.length ++
        (if lenMk < vecCap4Of lenMk then [] else vec104GrowEvents (vecCap4Of lenMk))

/-- Prefix of allocator events emitted by the first `k` fields of `c.fields`. -/
def chainDoneEvents (c : ChainG) : Nat → List AllocEvent
  | 0 => []
  | k + 1 =>
      if hk : k < c.fields.length then
        chainDoneEvents c k ++
          chainFieldStepEvents (chainGAfter c k).keys.length (c.fields[k]'hk)
      else chainDoneEvents c k

/-- Remaining allocator events emitted from field index `k` up to `c.fields.length`. -/
def chainRemEvents (c : ChainG) (k : Nat) : List AllocEvent :=
  if hk : k < c.fields.length then
    chainFieldStepEvents (chainGAfter c k).keys.length (c.fields[k]'hk) ++
      chainRemEvents c (k + 1)
  else []
termination_by c.fields.length - k

/-- Complete deterministic allocator event trace of `prost::encoding::message::merge<Chain>` on `c`. -/
def chainMergeEvents (c : ChainG) : List AllocEvent :=
  chainDoneEvents c c.fields.length

theorem chainRemEvents_eq_cons {c : ChainG} {k : Nat} (hk : k < c.fields.length) :
    chainRemEvents c k =
      chainFieldStepEvents (chainGAfter c k).keys.length (c.fields[k]'hk) ++
        chainRemEvents c (k + 1) := by
  rw [chainRemEvents]
  simp only [hk, ↓reduceDIte]

theorem chainRemEvents_ge {c : ChainG} {k : Nat} (hk : c.fields.length ≤ k) :
    chainRemEvents c k = [] := by
  rw [chainRemEvents]
  have hlt : ¬ (k < c.fields.length) := by omega
  simp only [hlt, ↓reduceDIte]

theorem chainDoneEvents_append_rem (c : ChainG) (k : Nat) (hk : k ≤ c.fields.length) :
    chainDoneEvents c k ++ chainRemEvents c k = chainMergeEvents c := by
  induction hrem : c.fields.length - k generalizing k with
  | zero =>
    have heq : k = c.fields.length := by omega
    subst heq
    rw [chainRemEvents_ge (Nat.le_refl _), List.append_nil]
    rfl
  | succ d ih =>
    have hlt : k < c.fields.length := by omega
    rw [chainRemEvents_eq_cons hlt, ← List.append_assoc]
    have hdone : chainDoneEvents c (k + 1) =
        chainDoneEvents c k ++
          chainFieldStepEvents (chainGAfter c k).keys.length (c.fields[k]'hlt) := by
      simp [chainDoneEvents, hlt]
    rw [← hdone]
    exact ih (k + 1) (by omega) (by omega)

@[simp]
theorem chainRemEvents_zero (c : ChainG) :
    chainRemEvents c 0 = chainMergeEvents c := by
  simpa [chainDoneEvents] using chainDoneEvents_append_rem c 0 (Nat.zero_le _)

/-- Symbolic `cumSmall` charge of a fresh `bytes::merge` of `n` bytes when `max n 8 ≤ smallMaxReq M`. -/
def bytesFreshSmallCost (M : AllocCostModel) [HasFineReallocCredit M] (n : Nat) : Nat :=
  if n = 0 then 0
  else HasFineReallocCredit.smallAllocCost M n + HasFineReallocCredit.smallAllocCost M (max n 8)

/-- Symbolic `cumSmall` charge of the `bytes::merge` call inside one `ChainField`. -/
def chainFieldBytesSmallCost (M : AllocCostModel) [HasFineReallocCredit M] : ChainField → Nat
  | .srk b => bytesFreshSmallCost M b.length
  | .priv b => bytesFreshSmallCost M b.length
  | .ck _ key => bytesFreshSmallCost M key.length
  | .key mkg => bytesFreshSmallCost M mkg.seed.length

/-- Symbolic `cumSmall` cost of `message::merge<Chain>` on `c : ChainG`:
charges `0` `Vec<MessageKey>` growth cost when `c.keys = []` (`sender_chain` zero-alloc invariant). -/
def chainMergeSmallCost (M : AllocCostModel) [HasFineReallocCredit M] (c : ChainG) : Nat :=
  (c.fields.map (chainFieldBytesSmallCost M)).sum + vec104CumOfCap M (vecCap4Of c.keys.length)

/-- Compatibility alias for `chainMergeSmallCost`. -/
abbrev chainFieldsSmallCost (M : AllocCostModel) [HasFineReallocCredit M] (c : ChainG) : Nat :=
  chainMergeSmallCost M c

/-- Post-merge direct-`mmap` live cost of `c : ChainG` (`0` when `c.keys = []` or `≤ 1024` under `hsplit`). -/
def chainMergeLargeLive (M : AllocCostModel) [HasFineReallocCredit M] (c : ChainG) : Nat :=
  vec104LargeLive M (vecCap4Of c.keys.length)

/-- Compatibility alias for `chainMergeLargeLive`. -/
abbrev chainFieldsLargeLive (M : AllocCostModel) [HasFineReallocCredit M] (c : ChainG) : Nat :=
  chainMergeLargeLive M c

/-- Transient direct-`mmap` peak of `message::merge<Chain>` on `c : ChainG`. -/
def chainMergePeakLarge (M : AllocCostModel) [HasFineReallocCredit M] (c : ChainG) : Nat :=
  vec104PeakLarge M (vecCap4Of c.keys.length)

@[simp]
theorem chainMergeLargeLive_of_keys_nil (M : AllocCostModel) [HasFineReallocCredit M]
    {c : ChainG} (hk : c.keys = []) :
    chainMergeLargeLive M c = 0 := by
  simp [chainMergeLargeLive, hk]

@[simp]
theorem chainMergePeakLarge_of_keys_nil (M : AllocCostModel) [HasFineReallocCredit M]
    {c : ChainG} (hk : c.keys = []) :
    chainMergePeakLarge M c = 0 := by
  simp [chainMergePeakLarge, hk]

private theorem stepEvents_bytesMergeFresh_le_smallMax (M : AllocCostModel) [HasFineReallocCredit M]
    {n : Nat} (st : M.σ) (h8 : 8 ≤ HasFineReallocCredit.smallMaxReq M)
    (hn : n ≤ HasFineReallocCredit.smallMaxReq M) :
    let st' := M.stepEvents (bytesMergeEvents 0 n) st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st + bytesFreshSmallCost M n ∧
    HasFineReallocCredit.liveLarge st' ≤ HasFineReallocCredit.liveLarge st ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st := by
  by_cases h0 : n = 0
  · subst h0
    simp [bytesFreshSmallCost, stepEvents_bytesMergeFresh_zero]
  · have hpos : 0 < n := by omega
    have hmax : max n 8 ≤ HasFineReallocCredit.smallMaxReq M := by omega
    have h := stepEvents_bytesMergeFresh_small M st hpos hmax
    dsimp only at h ⊢
    simp only [bytesFreshSmallCost, h0, ↓reduceIte]
    exact ⟨by omega, h.2.1, h.2.2⟩

/-- Symbolic telescoping bound for `message::merge<Chain>` (`c.Ok`, `33 ≤ smallMaxReq M`):
starting from any `st₀ : M.σ`, `st_f := M.stepEvents (chainMergeEvents c) st₀` satisfies:
- `cumSmall st_f ≤ cumSmall st₀ + chainMergeSmallCost M c` (`0` `Vec<104>` cost when `c.keys = []`),
- `liveLarge st_f ≤ liveLarge st₀ + chainMergeLargeLive M c`,
- `peakLarge st_f ≤ max (peakLarge st₀) (liveLarge st₀ + chainMergePeakLarge M c)`. -/
theorem stepEvents_chainMerge_bounds (M : AllocCostModel) [HasFineReallocCredit M]
    {c : ChainG} (hcOk : c.Ok)
    (h33 : 33 ≤ HasFineReallocCredit.smallMaxReq M)
    (st₀ : M.σ) :
    let st_f := M.stepEvents (chainMergeEvents c) st₀
    HasFineReallocCredit.cumSmall st_f ≤
      HasFineReallocCredit.cumSmall st₀ + chainMergeSmallCost M c ∧
    HasFineReallocCredit.liveLarge st_f ≤
      HasFineReallocCredit.liveLarge st₀ + chainMergeLargeLive M c ∧
    HasFineReallocCredit.peakLarge st_f ≤
      max (HasFineReallocCredit.peakLarge st₀)
        (HasFineReallocCredit.liveLarge st₀ + chainMergePeakLarge M c) := by
  have h8 : 8 ≤ HasFineReallocCredit.smallMaxReq M := by omega
  let capMax := vecCap4Of c.keys.length
  let C_max := HasFineReallocCredit.cumSmall st₀ + chainMergeSmallCost M c
  let L_other := HasFineReallocCredit.liveLarge st₀
  let P₀ := HasFineReallocCredit.peakLarge st₀
  suffices hinv : ∀ k : Nat, k ≤ c.fields.length →
      let st_k := M.stepEvents (chainDoneEvents c k) st₀
      let cap_k := vecCap4Of (chainGAfter c k).keys.length
      HasFineReallocCredit.cumSmall st_k +
        ((c.fields.drop k).map (chainFieldBytesSmallCost M)).sum +
        vec104CumRem M capMax cap_k ≤ C_max ∧
      HasFineReallocCredit.liveLarge st_k ≤ L_other + vec104LargeLive M cap_k ∧
      HasFineReallocCredit.peakLarge st_k ≤ max P₀ (L_other + vec104PeakLarge M capMax) by
    have hEnd := hinv c.fields.length (Nat.le_refl _)
    dsimp only [capMax, C_max, L_other, P₀] at hEnd
    rw [chainGAfter_fields c, List.drop_length, List.map_nil, List.sum_nil,
      vec104CumRem_self] at hEnd
    dsimp only [chainMergeEvents, chainMergeLargeLive, chainMergePeakLarge]
    exact ⟨by omega, hEnd.2.1, hEnd.2.2⟩
  intro k hk_le
  induction k with
  | zero =>
    have hkeys0 : (chainGAfter c 0).keys = [] := rfl
    dsimp only [chainDoneEvents, AllocCostModel.stepEvents_nil, C_max, chainMergeSmallCost,
      L_other, P₀, capMax]
    rw [hkeys0, List.length_nil, vecCap4Of_zero, List.drop_zero,
      vec104CumRem_zero, vec104LargeLive_zero]
    refine ⟨by omega, by omega, Nat.le_max_left _ _⟩
  | succ k ih =>
    have hk : k < c.fields.length := by omega
    obtain ⟨hcum_k, hlive_k, hpeak_k⟩ := ih (by omega)
    dsimp only [capMax, C_max, L_other, P₀] at hcum_k hlive_k hpeak_k ⊢
    set st_k := M.stepEvents (chainDoneEvents c k) st₀
    have hdone : chainDoneEvents c (k + 1) =
        chainDoneEvents c k ++
          chainFieldStepEvents (chainGAfter c k).keys.length (c.fields[k]'hk) := by
      simp [chainDoneEvents, hk]
    have hst_succ :
        M.stepEvents (chainDoneEvents c (k + 1)) st₀ =
          M.stepEvents (chainFieldStepEvents (chainGAfter c k).keys.length (c.fields[k]'hk)) st_k := by
      rw [hdone, AllocCostModel.stepEvents_append]
    have hdrop :
        ((c.fields.drop k).map (chainFieldBytesSmallCost M)).sum =
          chainFieldBytesSmallCost M (c.fields[k]'hk) +
            ((c.fields.drop (k + 1)).map (chainFieldBytesSmallCost M)).sum := by
      rw [List.drop_eq_getElem_cons hk, List.map_cons, List.sum_cons]
    rw [hdrop] at hcum_k
    have hmem_fl : c.fields[k]'hk ∈ c.fields := List.getElem_mem hk
    have hlen_fl := mem_fields_bytes_le_33 hcOk hmem_fl
    have hc_succ := chainGAfter_succ hk
    rw [hst_succ]
    generalize hfl : c.fields[k]'hk = fl at hlen_fl hc_succ hcum_k ⊢
    cases fl with
    | srk b =>
      have hb_le : b.length ≤ HasFineReallocCredit.smallMaxReq M := by dsimp [ChainFieldBytesOk] at hlen_fl; omega
      have hkeys_eq : (chainGAfter c (k + 1)).keys = (chainGAfter c k).keys := by
        rw [hc_succ]; rfl
      rw [hkeys_eq]
      dsimp only [chainFieldStepEvents, chainFieldBytesSmallCost] at hcum_k ⊢
      rcases stepEvents_bytesMergeFresh_le_smallMax M st_k h8 hb_le with ⟨hc1, hl1, hp1⟩
      exact ⟨by omega, by omega, by omega⟩
    | priv b =>
      have hb_le : b.length ≤ HasFineReallocCredit.smallMaxReq M := by dsimp [ChainFieldBytesOk] at hlen_fl; omega
      have hkeys_eq : (chainGAfter c (k + 1)).keys = (chainGAfter c k).keys := by
        rw [hc_succ]; rfl
      rw [hkeys_eq]
      dsimp only [chainFieldStepEvents, chainFieldBytesSmallCost] at hcum_k ⊢
      rcases stepEvents_bytesMergeFresh_le_smallMax M st_k h8 hb_le with ⟨hc1, hl1, hp1⟩
      exact ⟨by omega, by omega, by omega⟩
    | ck i key =>
      have hk_le' : key.length ≤ HasFineReallocCredit.smallMaxReq M := by dsimp [ChainFieldBytesOk] at hlen_fl; omega
      have hkeys_eq : (chainGAfter c (k + 1)).keys = (chainGAfter c k).keys := by
        rw [hc_succ]; rfl
      rw [hkeys_eq]
      dsimp only [chainFieldStepEvents, chainFieldBytesSmallCost] at hcum_k ⊢
      rcases stepEvents_bytesMergeFresh_le_smallMax M st_k h8 hk_le' with ⟨hc1, hl1, hp1⟩
      exact ⟨by omega, by omega, by omega⟩
    | key mk =>
      have hs_le : mk.seed.length ≤ HasFineReallocCredit.smallMaxReq M := by dsimp [ChainFieldBytesOk] at hlen_fl; omega
      have hkeys_succ_len :
          (chainGAfter c (k + 1)).keys.length = (chainGAfter c k).keys.length + 1 := by
        rw [hc_succ]; simp [ChainG.apply]
      have hlen_lt_keys : (chainGAfter c k).keys.length < c.keys.length := by
        have hle_succ := chainGAfter_keys_length_le c (k + 1)
        omega
      dsimp only [chainFieldStepEvents, chainFieldBytesSmallCost] at hcum_k ⊢
      rw [AllocCostModel.stepEvents_append, hkeys_succ_len]
      rcases stepEvents_bytesMergeFresh_le_smallMax M st_k h8 hs_le with ⟨hc1, hl1, hp1⟩
      set st_mid := M.stepEvents (bytesMergeEvents 0 mk.seed.length) st_k
      have hpush_eq :
          M.stepEvents
            (if (chainGAfter c k).keys.length < vecCap4Of (chainGAfter c k).keys.length then []
             else vec104GrowEvents (vecCap4Of (chainGAfter c k).keys.length)) st_mid =
          (if (chainGAfter c k).keys.length < vecCap4Of (chainGAfter c k).keys.length then st_mid
           else M.stepEvents (vec104GrowEvents (vecCap4Of (chainGAfter c k).keys.length)) st_mid) := by
        split_ifs <;> rfl
      rw [hpush_eq]
      have hstep := vec104Push_budget_step M
        (len := (chainGAfter c k).keys.length) (n := c.keys.length)
        (C_max := HasFineReallocCredit.cumSmall st₀ + chainMergeSmallCost M c -
          ((c.fields.drop (k + 1)).map (chainFieldBytesSmallCost M)).sum)
        (L_other := HasFineReallocCredit.liveLarge st₀)
        (P₀ := HasFineReallocCredit.peakLarge st₀) (st := st_mid)
        hlen_lt_keys (by omega) (by omega) (Nat.le_trans hp1 hpeak_k)
      exact ⟨by omega, hstep.2.1, hstep.2.2⟩

private theorem bytesMergeEvents_withinMaxAlloc {n : Nat} (hn : n ≤ 33)
    {ev : AllocEvent} (hev : ev ∈ bytesMergeEvents 0 n) :
    ev.withinMaxAlloc := by
  by_cases h0 : n = 0
  · subst h0; simp at hev
  · have hpos : 0 < n := by omega
    have hm1 : 1 ≤ n := hpos
    have hm2 : 1 ≤ max n 8 := by omega
    simp only [bytesMergeEvents, bytesMergeAllocEvents, h0, hpos, ↓reduceIte,
      ProstMergeBudget.doReserveEvents_zero, ProstMergeBudget.reserveCap_zero_zero,
      ProstMergeBudget.bytesDropEvents_ne h0, rustAllocEvents, rustDeallocEvents,
      (by decide : (1 : Nat) ≤ 16), hm1, hm2, and_self, List.mem_append, List.mem_singleton] at hev
    rcases hev with (rfl | rfl) | rfl
    · dsimp [AllocEvent.withinMaxAlloc, VerifiedLibraries.Mallocng.MallocngMaxAllocSize]; omega
    · dsimp [AllocEvent.withinMaxAlloc, VerifiedLibraries.Mallocng.MallocngMaxAllocSize]; omega
    · trivial

private theorem vec104GrowEvents_withinMaxAlloc {cap : Nat} (hcap : cap ≤ 2048)
    {ev : AllocEvent} (hev : ev ∈ vec104GrowEvents cap) :
    ev.withinMaxAlloc := by
  unfold vec104GrowEvents at hev
  by_cases h0 : cap = 0
  · subst h0
    simp only [↓reduceIte, rustAllocEvents, (by decide : (8 : Nat) ≤ 16),
      (by decide : (8 : Nat) ≤ 4 * 104), and_self, List.mem_singleton] at hev
    subst hev
    decide
  · have hm : 8 ≤ 2 * cap * 104 := by omega
    simp only [h0, ↓reduceIte, rustReallocEvents, (by decide : (8 : Nat) ≤ 16), hm, and_self,
      List.mem_singleton] at hev
    subst hev
    dsimp [AllocEvent.withinMaxAlloc, VerifiedLibraries.Mallocng.MallocngMaxAllocSize]
    omega

theorem chainMergeEvents_withinMaxAlloc {c : ChainG} (hcOk : c.Ok) :
    ∀ ev ∈ chainMergeEvents c, ev.withinMaxAlloc := by
  suffices h : ∀ k : Nat, k ≤ c.fields.length →
      ∀ ev ∈ chainDoneEvents c k, ev.withinMaxAlloc by
    exact h c.fields.length (Nat.le_refl _)
  intro k hk_le
  induction k with
  | zero => simp [chainDoneEvents]
  | succ k ih =>
    have hk : k < c.fields.length := by omega
    intro ev hev
    simp only [chainDoneEvents, hk, ↓reduceDIte, List.mem_append] at hev
    rcases hev with hev | hev
    · exact ih (by omega) ev hev
    · have hlen_fl := mem_fields_bytes_le_33 hcOk (List.getElem_mem hk)
      have hkeys_le : (chainGAfter c k).keys.length ≤ maxMessageKeys :=
        Nat.le_trans (chainGAfter_keys_length_le c k) hcOk.2.2.2.2
      have hcap_le : vecCap4Of (chainGAfter c k).keys.length ≤ 2048 := by
        have hm := vecCap4Of_mono hkeys_le
        have h2000 : vecCap4Of maxMessageKeys = 2048 := by decide
        omega
      revert hlen_fl hev
      generalize c.fields[k]'hk = fl
      cases fl with
      | srk b =>
        intro hev hl
        exact bytesMergeEvents_withinMaxAlloc (by dsimp [ChainFieldBytesOk] at hl; omega) hev
      | priv b =>
        intro hev hl
        exact bytesMergeEvents_withinMaxAlloc (by dsimp [ChainFieldBytesOk] at hl; omega) hev
      | ck i key =>
        intro hev hl
        exact bytesMergeEvents_withinMaxAlloc (by dsimp [ChainFieldBytesOk] at hl; omega) hev
      | key mk =>
        intro hev hl
        dsimp only [chainFieldStepEvents] at hev
        rw [List.mem_append] at hev
        rcases hev with hev | hev
        · exact bytesMergeEvents_withinMaxAlloc (by dsimp [ChainFieldBytesOk] at hl; omega) hev
        · split_ifs at hev with hlt
          · simp at hev
          · exact vec104GrowEvents_withinMaxAlloc hcap_le hev

/-- Discharge `FitsEvents M lim st₀ (chainMergeEvents c)` directly from `stepEvents_chainMerge_bounds`
and `fitsStep_of_fine_bounds` (`2 * maxStep` physical-RAM inequality). -/
theorem chainMergeFits_of_fine_bounds (M : AllocCostModel) [HasFineReallocCredit M]
    {lim : BudgetLimits} {c : ChainG} {st₀ : M.σ}
    {maxStep dynB cumB peakB : Nat}
    (hcOk : c.Ok)
    (h33 : 33 ≤ HasFineReallocCredit.smallMaxReq M)
    (henf : lim.enforced = true)
    (hstep : ∀ ev ∈ chainMergeEvents c,
      M.stepReserve ev (M.stepEvents (chainMergeEvents c) st₀) ≤ maxStep)
    (hdyn : M.maxDynIvs (M.stepEvents (chainMergeEvents c) st₀) ≤ dynB)
    (hcum : HasFineReallocCredit.cumSmall st₀ + chainMergeSmallCost M c ≤ cumB)
    (hlive : HasFineReallocCredit.liveLarge st₀ + chainMergeLargeLive M c ≤ peakB)
    (hpeak : max (HasFineReallocCredit.peakLarge st₀)
      (HasFineReallocCredit.liveLarge st₀ + chainMergePeakLarge M c) ≤ peakB)
    (hram : lim.staticBytes +
      (HasFineReallocCredit.baseFine (M := M) + cumB + peakB) + 2 * maxStep ≤ lim.physCap)
    (hva : MMAP_MIN_ADDR + lim.staticBytes +
      (HasFineReallocCredit.baseFine (M := M) + cumB + peakB) + maxStep +
      (lim.staticCount + dynB + 16) * (maxStep + PAGE_SIZE) + maxStep ≤ 2 ^ 48) :
    FitsEvents M lim st₀ (chainMergeEvents c) := by
  rcases stepEvents_chainMerge_bounds M hcOk h33 st₀ with ⟨hc_f, hl_f, hp_f⟩
  set st_f := M.stepEvents (chainMergeEvents c) st₀
  have hFitFinal : FitsStep lim maxStep (M.maxDynIvs st_f) (M.footprint st_f) :=
    fitsStep_of_fine_bounds M henf hdyn (by omega) (by omega) (by omega) hram hva
  refine fitsEvents_of_step_monotone M lim maxStep (chainMergeEvents c) [] st₀ ?_
  simpa only [List.append_nil] using
    ⟨fun ev hev => ⟨chainMergeEvents_withinMaxAlloc hcOk ev hev, hstep ev hev⟩, hFitFinal⟩


/-! ## 3. Total-Correctness `SepWPp` Spec, Loop Invariant & Callee Call Helpers -/

open CryptoVerification.LibsignalTripleRatchet (LibsignalCodeRoLoaded)

/-- Raw total-correctness (`onPanic := ⌜False⌝`, `onOom := ⌜False⌝`) contract for
`prost::encoding::message::merge<Chain>` (Block `11`, `chainMergeStackX`) from a freshly
defaulted `*x.a = ChainG.empty`. -/
def chainMergeGenBudgetRawSpecW (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (ChainMergeGenGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = 2#8 ∧ s.readReg64 .x1 = x.a ∧ s.readReg64 .x2 = x.bufRef ∧
      (s.readReg64 .x3).setWidth 32 = 99#32 ∧ x.c.Ok ∧
      (x.c.payload ++ x.tail).length < 2 ^ 62 ∧
      FitsEvents M lim st (chainMergeEvents x.c)⌝ ∗
      prostChainGAtCap A.repAlloc x.a 0 ChainG.empty ∗
      (x.bufRef ↦₆₄ x.slot) ∗
      sliceCursorAt x.slot x.ptr (x.c.payload ++ x.tail) ∗
      A.pool lim st s ∗
      stackAt s.sp chainMergeStackX
  post := fun (x, st) s0 sf =>
    let st' := M.stepEvents (chainMergeEvents x.c) st
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗
      prostChainGAtCap A.repAlloc x.a (vecCap4Of x.c.keys.length) x.c ∗
      (x.bufRef ↦₆₄ x.slot) ∗
      sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail) x.tail ∗
      A.pool lim st' sf ∗
      stackAt s0.sp chainMergeStackX

/-- Relocatable `[LibsignalPlacement]` total-correctness contract for `message::merge<Chain>`
(Block `11`, `lsProg_11 H`, `chainMergeStackX`), carrying `LibsignalCodeRoLoaded lsmpl`. -/
abbrev chainMergeGenBudgetSpecW [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (ChainMergeGenGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl (chainMergeGenBudgetRawSpecW M A lim)

/-- Pure state & remaining-budget loop invariant at `(blkPl_11).base + 0x120` after `k` fields. -/
def ChainLoopBudgetInv [LibsignalPlacement]
    (M : AllocCostModel) (lim : BudgetLimits)
    (x : ChainMergeGenGhost) (st₀ : M.σ) (s0 : State) (k : Nat) (s : State) : Prop :=
  s.pc = (blkPl_11).base + 0x120#64 ∧ s.status = .Running ∧ s.trace = s0.trace ∧
    calleeSavedVRegs s = calleeSavedVRegs s0 ∧
    LibsignalCodeLoaded lsmpl s.mem ∧ LibsignalRoLoaded lsmpl s.mem ∧
    s.sp = s0.sp - 256#64 ∧ s0.sp &&& 15#64 = 0#64 ∧
    s.readReg64 .x29 = s0.sp - 96#64 ∧
    s.readReg64 .x19 = x.bufRef ∧ s.readReg64 .x20 = x.a ∧
    s.readReg64 .x24 = BitVec.ofNat 64 x.tail.length ∧
    s.readReg64 .x21 = 98#64 ∧ s.readReg64 .x22 = 97#64 ∧
    s.readReg64 .x25 = s0.sp - 248#64 ∧ s.readReg64 .x26 = 1#64 ∧
    x.c.Ok ∧ (x.c.payload ++ x.tail).length < 2 ^ 62 ∧
    FitsEvents M lim (M.stepEvents (chainDoneEvents x.c k) st₀) (chainRemEvents x.c k)

/-- Spatial loop invariant at `(blkPl_11).base + 0x120` after `k` fields. -/
def ChainLoopBudgetSpatial (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : ChainMergeGenGhost) (st₀ : M.σ) (s0 : State) (k : Nat) (s : State) : SepProp :=
  prostChainGAtCap A.repAlloc x.a (vecCap4Of (chainGAfter x.c k).keys.length) (chainGAfter x.c k) ∗
    (x.bufRef ↦₆₄ x.slot) ∗
    sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail)
      (((x.c.fields.drop k).flatMap ChainField.enc) ++ x.tail) ∗
    A.pool lim (M.stepEvents (chainDoneEvents x.c k) st₀) s ∗
    stackAt (s0.sp - 256#64) chainMergeSubStackX ∗
    chainMergeSavedRegs s0.sp s0

private abbrev NoPanicPost : State → SepProp → Prop := fun _ _ => False

private theorem sepWPp_exists_left {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {P : α → SepProp} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ a : α, SepWPp prog ret s (P a ∗ F) Q Qp) :
    SepWPp prog ret s ((∃∗ a : α, P a) ∗ F) Q Qp := by
  intro R hm hL
  rw [sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨a, hma⟩ := hm
  exact h a R (by simpa only [sepConj_assoc] using hma) hL

private theorem sepWPp_pure_left_and {prog : Program} {ret : BitVec 64} {s : State}
    {φ : Prop} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s F Q Qp) :
    SepWPp prog ret s (⌜φ⌝ ∗ F) Q Qp := by
  intro R hm hL
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 R hm.2 hL

private theorem sepWPp_call_lscl [LibsignalPlacement] {α : Type} {H : LibsignalHooks}
    {target ret_pc ret : BitVec 64} {spec : Spec α} {x : α}
    {s : State} {Pre F : SepProp} {Q : State → SepProp → Prop}
    (hsub : subroutine_ok (lsProg_11 H) target (withLsCl lsmpl spec))
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hro : LibsignalRoLoaded lsmpl s.mem)
    (hpc : s.pc = target) (hrun : s.status = .Running) (hal : s.spAligned = true)
    (hlr : s.readReg64 .lr = ret_pc)
    (hpre : Pre ⊢ spec.pre x s ∗ F)
    (hpan : ∀ sf R', ¬ (sf.mem ⊨ spec.onPanic x s sf ∗ R'))
    (hexit : ∀ sf ec R', ¬ (sf.mem ⊨ spec.onExit x ec s sf ∗ R'))
    (hoom : ∀ sf R', ¬ (sf.mem ⊨ spec.onOom x s sf ∗ R'))
    (hcont : ∀ sf : State,
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp →
      CalleeSavedPreserved s sf →
      LibsignalCodeLoaded lsmpl sf.mem → LibsignalRoLoaded lsmpl sf.mem →
      SepWPp (lsProg_11 H) ret sf (spec.post x s sf ∗ F) Q NoPanicPost) :
    SepWPp (lsProg_11 H) ret s Pre Q NoPanicPost := by
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

private theorem sepWPp_call_lscro [LibsignalPlacement] {α : Type} {H : LibsignalHooks}
    {target ret_pc ret : BitVec 64} {spec : Spec α} {x : α}
    {s : State} {Pre F : SepProp} {Q : State → SepProp → Prop}
    (hsub : subroutine_ok (lsProg_11 H) target (withLsCodeRoLoaded lsmpl spec))
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hro : LibsignalRoLoaded lsmpl s.mem)
    (hpc : s.pc = target) (hrun : s.status = .Running) (hal : s.spAligned = true)
    (hlr : s.readReg64 .lr = ret_pc)
    (hpre : Pre ⊢ spec.pre x s ∗ F)
    (hpan : ∀ sf R', ¬ (sf.mem ⊨ spec.onPanic x s sf ∗ R'))
    (hexit : ∀ sf ec R', ¬ (sf.mem ⊨ spec.onExit x ec s sf ∗ R'))
    (hoom : ∀ sf R', ¬ (sf.mem ⊨ spec.onOom x s sf ∗ R'))
    (hcont : ∀ sf : State,
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp →
      CalleeSavedPreserved s sf →
      LibsignalCodeLoaded lsmpl sf.mem → LibsignalRoLoaded lsmpl sf.mem →
      SepWPp (lsProg_11 H) ret sf (spec.post x s sf ∗ F) Q NoPanicPost) :
    SepWPp (lsProg_11 H) ret s Pre Q NoPanicPost := by
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

/-- Step a `bl bytes::merge` (`lsmpl.base 7`) call inside `message::merge<Chain>` (`lsProg_11 H`)
from a fresh destination `vecU8FreshCap A.repAlloc v []`, threading `A.pool lim st` to
`A.pool lim (M.stepEvents (bytesMergeEvents 0 b.length) st)` and producing
`vecU8FreshCap A.repAlloc v b`. -/
private theorem step_chainMerge_bytesMergeFresh_budget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H)
    (v bufRef slot curPtr sp0 ret_pc : BitVec 64)
    (b rest : List (BitVec 8)) (st : M.σ)
    (hb : b.length < 128)
    (hlen_lt : ([BitVec.ofNat 8 b.length] ++ b ++ rest).length < 2 ^ 62)
    (hfit : FitsEvents M lim st (bytesMergeEvents 0 b.length))
    {ret : BitVec 64} {s0 s : State} {F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 7) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 256#64) (halign : sp0 &&& 15#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hro : LibsignalRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : (s.readReg64 .x0).setWidth 8 = 2#8)
    (hx1 : s.readReg64 .x1 = v) (hx2 : s.readReg64 .x2 = bufRef)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp0 - 256#64 →
      LibsignalCodeLoaded lsmpl sm.mem → LibsignalRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace → CalleeSavedPreserved s sm → sm.readReg64 .x0 = 0#64 →
      SepWPp (lsProg_11 H) ret sm
        ((vecU8FreshCap A.repAlloc v b ∗
          (bufRef ↦₆₄ slot) ∗
          (curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest ∗
          A.pool lim (M.stepEvents (bytesMergeEvents 0 b.length) st) sm ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F) Q NoPanicPost) :
    SepWPp (lsProg_11 H) ret s
      ((vecU8FreshCap A.repAlloc v [] ∗
        (bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot curPtr ([BitVec.ofNat 8 b.length] ++ b ++ rest) ∗
        A.pool lim st s ∗
        stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F) Q NoPanicPost := by
  have hBM := bytes_merge_fresh_budget_placed_okW_cl (callerProg := lsProg_11 H) hA
  have hal : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_256_aligned_seedChain halign
  have hfit_alloc : FitsEvents M lim st (bytesMergeAllocEvents 0 b.length) :=
    ((fitsEvents_append (M := M) (lim := lim) (st := st)
      (evs₁ := bytesMergeAllocEvents 0 b.length)
      (evs₂ := ProstMergeBudget.bytesDropEvents b.length)).mp hfit).1
  have hlen63 : ([BitVec.ofNat 8 b.length] ++ b ++ rest).length < 2 ^ 63 :=
    Nat.lt_trans hlen_lt (by decide)
  have hmB : mergeBytes .lengthDelimited ([BitVec.ofNat 8 b.length] ++ b ++ rest) = some (b, rest) :=
    mergeBytes_lt128_seedChain b rest hb
  unfold vecU8FreshCap
  rw [List.length_nil, bytesMergeOutCap_zero_zero]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun valBuf => ?_
  let gbm : BytesMergeGhost :=
    ⟨.lengthDelimited, v, 0#64, valBuf, [], bufRef, slot, curPtr,
      [BitVec.ofNat 8 b.length] ++ b ++ rest⟩
  let F_bm : SepProp :=
    memRegion (sp0 - 256#64 - BitVec.ofNat 64 chainMergeSubStackX)
      (chainMergeSubStackX - bytesMergeStackW) ∗ F
  refine sepWPp_call_lscro (x := (gbm, b, rest, st)) (F := F_bm)
    hBM hcl hro hpc hrun hal hlr ?_
    (fun _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ h => not_satisfies_false_sepConj h) ?_
  · dsimp only [bytesMergeFreshBudgetSpecW, gbm, F_bm]
    rw [hsp, stackAt_sub_to_bytesMerge_seedChainW (sp0 - 256#64)]
    refine Entails.trans
      (Entails.of_eq (?_ : _ =
        (vecU8At A.repAlloc v 0#64 valBuf [] ∗
          (bufRef ↦₆₄ slot) ∗
          sliceCursorAt slot curPtr ([BitVec.ofNat 8 b.length] ++ b ++ rest) ∗
          A.pool lim st s ∗
          stackAt (sp0 - 256#64) bytesMergeStackW) ∗
        (memRegion (sp0 - 256#64 - BitVec.ofNat 64 chainMergeSubStackX)
          (chainMergeSubStackX - bytesMergeStackW) ∗ F)))
      (sepConj_mono_left (Entails.pure_right
        ⟨hx0, hx1, hx2, hlen63, rfl, rfl, hmB, hfit_alloc⟩ (Entails.refl _)))
    · sep_ac_rfl
  · intro sm hpcm hrunm hspm hcsm hclm hrom
    rw [hsp] at hspm
    dsimp only [bytesMergeFreshBudgetSpecW, gbm, F_bm]
    rw [hsp, sepConj_assoc]
    refine sepWPp_pure_left_and fun ⟨hx0m, htrm⟩ => ?_
    have hcur := sliceCursorAfter_append_eq_seedChain slot curPtr ([BitVec.ofNat 8 b.length] ++ b) rest
    rw [show ([BitVec.ofNat 8 b.length] ++ b).length = b.length + 1 by simp] at hcur
    have hfold :
        ((∃∗ ptr' : BitVec 64, vecU8At A.repAlloc v (bytesMergeOutCap 0#64 b.length) ptr' b) ∗
          (bufRef ↦₆₄ slot) ∗
          sliceCursorAfter slot curPtr ([BitVec.ofNat 8 b.length] ++ b ++ rest) rest ∗
          A.pool lim (M.stepEvents (bytesMergeEvents 0 b.length) st) sm ∗
          stackAt (sp0 - 256#64) bytesMergeStackW) ∗
          (memRegion (sp0 - 256#64 - BitVec.ofNat 64 chainMergeSubStackX)
            (chainMergeSubStackX - bytesMergeStackW) ∗ F) =
        ((vecU8FreshCap A.repAlloc v b ∗
          (bufRef ↦₆₄ slot) ∗
          (curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest ∗
          A.pool lim (M.stepEvents (bytesMergeEvents 0 b.length) st) sm ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F) := by
      unfold vecU8FreshCap
      rw [hcur, stackAt_sub_to_bytesMerge_seedChainW (sp0 - 256#64)]
      sep_ac_rfl
    exact SepWPp.weaken_pre (Entails.of_eq hfold)
      (hnext sm hpcm hrunm hspm hclm hrom (htrm.trans htr) hcsm hx0m)

/-- Step a `bl int32::merge` (`lsmpl.base 8`) call inside `message::merge<Chain>` (`lsProg_11 H`),
transporting `A.pool lim st s` to `A.pool lim st sm` via `VmPreserved`. -/
private theorem step_chainMerge_int32Merge_budget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (dstAddr bufRefAddr slotAddr curPtrAddr sp0Addr retPc : BitVec 64)
    (w0 i : BitVec 32) (rest : List (BitVec 8)) (st : M.σ)
    (hlen_lt : (pbVarintBody 5 i.toNat ++ rest).length < 2 ^ 62)
    {ret : BitVec 64} {s0 s : State} {F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 8) (hrun : s.status = .Running)
    (hsp : s.sp = sp0Addr - 256#64) (halign : sp0Addr &&& 15#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hro : LibsignalRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = retPc)
    (hx0 : (s.readReg64 .x0).setWidth 8 = 0#8)
    (hx1 : s.readReg64 .x1 = dstAddr) (hx2 : s.readReg64 .x2 = bufRefAddr)
    (hnext : ∀ sm : State,
      sm.pc = retPc → sm.status = .Running → sm.sp = sp0Addr - 256#64 →
      LibsignalCodeLoaded lsmpl sm.mem → LibsignalRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace → CalleeSavedPreserved s sm → sm.readReg64 .x0 = 0#64 →
      SepWPp (lsProg_11 H) ret sm
        (((dstAddr ↦₃₂ i) ∗
          (bufRefAddr ↦₆₄ slotAddr) ∗
          (curPtrAddr ↦ₛ pbVarintBody 5 i.toNat) ∗
          sliceCursorAt slotAddr (curPtrAddr + BitVec.ofNat 64 (pbVarintBody 5 i.toNat).length) rest ∗
          A.pool lim st sm ∗
          stackAt (sp0Addr - 256#64) chainMergeSubStackX) ∗ F) Q NoPanicPost) :
    SepWPp (lsProg_11 H) ret s
      (((dstAddr ↦₃₂ w0) ∗
        (bufRefAddr ↦₆₄ slotAddr) ∗
        sliceCursorAt slotAddr curPtrAddr (pbVarintBody 5 i.toNat ++ rest) ∗
        A.pool lim st s ∗
        stackAt (sp0Addr - 256#64) chainMergeSubStackX) ∗ F) Q NoPanicPost := by
  have hIM := int32_merge_some_placed_ok_cl
    (callerProg := lsProg_11 H) (errStack := decodeErrorHookStackW) (by decide)
  have hal : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_256_aligned_seedChain halign
  have hlen63 : (pbVarintBody 5 i.toNat ++ rest).length < 2 ^ 63 :=
    Nat.lt_trans hlen_lt (by decide)
  have hmI := mergeUint32_pbVarintBody_seedChain i rest
  let gim : Int32MergeGhost :=
    ⟨.varint, dstAddr, bufRefAddr, slotAddr, curPtrAddr, pbVarintBody 5 i.toNat ++ rest⟩
  let F_im : SepProp :=
    A.pool lim st s ∗
      memRegion (sp0Addr - 256#64 - BitVec.ofNat 64 chainMergeSubStackX)
        (chainMergeSubStackX - int32MergeStackW) ∗ F
  refine sepWPp_call_lscl (x := (gim, i, rest)) (F := F_im)
    hIM hcl hro hpc hrun hal hlr ?_
    (fun _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ h => not_satisfies_false_sepConj h) ?_
  · dsimp only [int32MergeSomeSpecGen, gim, F_im]
    rw [hsp, stackAt_sub_to_int32Merge_seedChainW (sp0Addr - 256#64)]
    have hcell : (dstAddr ↦₃₂ w0) ⊢ memRegion dstAddr 4 := by
      rw [ProofLib.memRegion_four]
      exact Entails.sepExists_right w0 (Entails.refl _)
    have hstk_eq : 0x50 + (0x50 + decodeErrorHookStackW) = int32MergeStackW := rfl
    rw [hstk_eq]
    have hgrp :
        ((dstAddr ↦₃₂ w0) ∗ (bufRefAddr ↦₆₄ slotAddr) ∗
          sliceCursorAt slotAddr curPtrAddr (pbVarintBody 5 i.toNat ++ rest) ∗
          A.pool lim st s ∗
          (memRegion (sp0Addr - 256#64 - BitVec.ofNat 64 chainMergeSubStackX)
            (chainMergeSubStackX - int32MergeStackW) ∗
            stackAt (sp0Addr - 256#64) int32MergeStackW)) ∗ F =
        (dstAddr ↦₃₂ w0) ∗
          ((bufRefAddr ↦₆₄ slotAddr) ∗
            sliceCursorAt slotAddr curPtrAddr (pbVarintBody 5 i.toNat ++ rest) ∗
            stackAt (sp0Addr - 256#64) int32MergeStackW) ∗
          (A.pool lim st s ∗
            memRegion (sp0Addr - 256#64 - BitVec.ofNat 64 chainMergeSubStackX)
              (chainMergeSubStackX - int32MergeStackW) ∗ F) := by sep_ac_rfl
    rw [hgrp]
    refine Entails.trans (sepConj_mono_left hcell) ?_
    have hgrp2 :
        memRegion dstAddr 4 ∗
          ((bufRefAddr ↦₆₄ slotAddr) ∗
            sliceCursorAt slotAddr curPtrAddr (pbVarintBody 5 i.toNat ++ rest) ∗
            stackAt (sp0Addr - 256#64) int32MergeStackW) ∗
          (A.pool lim st s ∗
            memRegion (sp0Addr - 256#64 - BitVec.ofNat 64 chainMergeSubStackX)
              (chainMergeSubStackX - int32MergeStackW) ∗ F) =
        (memRegion dstAddr 4 ∗
          (bufRefAddr ↦₆₄ slotAddr) ∗
          sliceCursorAt slotAddr curPtrAddr (pbVarintBody 5 i.toNat ++ rest) ∗
          stackAt (sp0Addr - 256#64) int32MergeStackW) ∗
        (A.pool lim st s ∗
          memRegion (sp0Addr - 256#64 - BitVec.ofNat 64 chainMergeSubStackX)
            (chainMergeSubStackX - int32MergeStackW) ∗ F) := by sep_ac_rfl
    rw [hgrp2]
    exact sepConj_mono_left (Entails.pure_right
      ⟨hx0, hx1, hx2, hlen63, hmI⟩ (Entails.refl _))
  · intro sm hpcm hrunm hspm hcsm hclm hrom
    rw [hsp] at hspm
    dsimp only [int32MergeSomeSpecGen, gim, F_im]
    rw [hsp, sepConj_assoc]
    refine sepWPp_pure_left_and fun ⟨hx0m, htrm, hvmm⟩ => ?_
    rw [← A.pool_transport lim st s sm hvmm]
    have hcur := sliceCursorAfter_append_eq_seedChain slotAddr curPtrAddr (pbVarintBody 5 i.toNat) rest
    have hstk_eq : 0x50 + (0x50 + decodeErrorHookStackW) = int32MergeStackW := rfl
    rw [hstk_eq]
    have hfold :
        (((dstAddr ↦₃₂ i) ∗
          (bufRefAddr ↦₆₄ slotAddr) ∗
          sliceCursorAfter slotAddr curPtrAddr (pbVarintBody 5 i.toNat ++ rest) rest ∗
          stackAt (sp0Addr - 256#64) int32MergeStackW) ∗
          (A.pool lim st sm ∗
            memRegion (sp0Addr - 256#64 - BitVec.ofNat 64 chainMergeSubStackX)
              (chainMergeSubStackX - int32MergeStackW) ∗ F)) =
        (((dstAddr ↦₃₂ i) ∗
          (bufRefAddr ↦₆₄ slotAddr) ∗
          (curPtrAddr ↦ₛ pbVarintBody 5 i.toNat) ∗
          sliceCursorAt slotAddr (curPtrAddr + BitVec.ofNat 64 (pbVarintBody 5 i.toNat).length) rest ∗
          A.pool lim st sm ∗
          stackAt (sp0Addr - 256#64) chainMergeSubStackX) ∗ F) := by
      rw [hcur, stackAt_sub_to_int32Merge_seedChainW (sp0Addr - 256#64)]
      sep_ac_rfl
    exact SepWPp.weaken_pre (Entails.of_eq hfold)
      (hnext sm hpcm hrunm hspm hclm hrom (htrm.trans htr) hcsm hx0m)


/-! ## 4. Entry & Loop Body Segments (`Tags 1–4`, `Exit`) -/

local macro "cb_sep_eq" : tactic =>
  `(tactic| (
    try dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
      Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30, Reg.lr]
    try simp only [BitVec.add_assoc, BitVec.reduceAdd, bv_sub_add_lit]
    first | done | sep_ac_rfl))

private theorem chainDoneEvents_succ_of_lt {c : ChainG} {k : Nat} (hk : k < c.fields.length) :
    chainDoneEvents c (k + 1) =
      chainDoneEvents c k ++ chainFieldStepEvents (chainGAfter c k).keys.length (c.fields[k]'hk) := by
  simp [chainDoneEvents, hk]

private theorem chainLoop_fits_split {M : AllocCostModel} {lim : BudgetLimits}
    {c : ChainG} {k : Nat} {st₀ : M.σ} (hk : k < c.fields.length)
    (hfit : FitsEvents M lim (M.stepEvents (chainDoneEvents c k) st₀) (chainRemEvents c k)) :
    FitsEvents M lim (M.stepEvents (chainDoneEvents c k) st₀)
      (chainFieldStepEvents (chainGAfter c k).keys.length (c.fields[k]'hk)) ∧
    FitsEvents M lim (M.stepEvents (chainDoneEvents c (k + 1)) st₀)
      (chainRemEvents c (k + 1)) := by
  rw [chainRemEvents_eq_cons hk] at hfit
  obtain ⟨hf1, hf2⟩ := (fitsEvents_append (M := M) (lim := lim)
    (st := M.stepEvents (chainDoneEvents c k) st₀)
    (evs₁ := chainFieldStepEvents (chainGAfter c k).keys.length (c.fields[k]'hk))
    (evs₂ := chainRemEvents c (k + 1))).mp hfit
  rw [← AllocCostModel.stepEvents_append, ← chainDoneEvents_succ_of_lt hk] at hf2
  exact ⟨hf1, hf2⟩

set_option maxHeartbeats 800000 in
private theorem step_chainEntry_1byte_budget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (x : ChainMergeGenGhost) (st₀ : M.σ) {s0 : State} {Q : State → SepProp → Prop}
    (hbody_lt : x.c.enc.length < 128)
    (hpc : s0.pc = (blkPl_11).base) (hrun : s0.status = .Running)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s0.mem) (hro : LibsignalRoLoaded lsmpl s0.mem)
    (hx0 : (s0.readReg64 .x0).setWidth 8 = 2#8) (hx1 : s0.readReg64 .x1 = x.a)
    (hx2 : s0.readReg64 .x2 = x.bufRef) (hx3 : (s0.readReg64 .x3).setWidth 32 = 99#32)
    (hcOk : x.c.Ok) (hlen_lt : (x.c.payload ++ x.tail).length < 2 ^ 62)
    (hfit : FitsEvents M lim st₀ (chainMergeEvents x.c))
    (hloop : ∀ sm : State,
      ChainLoopBudgetInv M lim x st₀ s0 0 sm →
      SepWPp (lsProg_11 H) (s0.readReg64 .lr) sm
        (ChainLoopBudgetSpatial M A lim x st₀ s0 0 sm) Q NoPanicPost) :
    SepWPp (lsProg_11 H) (s0.readReg64 .lr) s0
      (prostChainGAtCap A.repAlloc x.a 0 ChainG.empty ∗
        (x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAt x.slot x.ptr (x.c.payload ++ x.tail) ∗
        A.pool lim st₀ s0 ∗
        stackAt s0.sp chainMergeStackX) Q NoPanicPost := by
  have hvar : encodeVarint (BitVec.ofNat 64 x.c.enc.length) = [BitVec.ofNat 8 x.c.enc.length] :=
    encodeVarint_lt128_seedChain x.c.enc.length hbody_lt
  have hpay : x.c.payload ++ x.tail = BitVec.ofNat 8 x.c.enc.length :: (x.c.enc ++ x.tail) := by
    unfold ChainG.payload; rw [hvar, List.singleton_append, List.cons_append]
  have hlen_lt1 : 1 + (x.c.enc.length + x.tail.length) < 2 ^ 62 := by
    rw [hpay, List.length_cons, List.length_append] at hlen_lt; omega
  have hlen_cons : (BitVec.ofNat 8 x.c.enc.length :: (x.c.enc ++ x.tail)).length < 2 ^ 62 := by
    simp only [List.length_cons, List.length_append]; omega
  have h1 : s0.readReg64 (Reg.gpr 1#5) = x.a := hx1
  have h2 : s0.readReg64 (Reg.gpr 2#5) = x.bufRef := hx2
  have hw3 : BitVec.truncate 32 (s0.readReg64 (Reg.gpr 3#5)) = 99#32 := hx3
  have hw0 : BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64 = 2#64 :=
    w0_and_255_eq_two_seedChain hx0
  have hcbz := cbz_len_cons_false_seedChain62 hlen_cons
  have hse0 := signExtend64_ofNat8_lt128_seedChain hbody_lt
  have hlsr56 := ofNat64_lsr56_eq_zero_seedChain hbody_lt
  have hsub_len := len_cons_sub_one_seedChain (BitVec.ofNat 8 x.c.enc.length) (x.c.enc ++ x.tail)
  have hlen_append : (x.c.enc ++ x.tail).length = x.c.enc.length + x.tail.length := List.length_append
  have hule_sub := ule_ofNat_add_right_true_seedChain62 (m := x.c.enc.length) (k := x.tail.length) (by omega)
  have hsub_tail := bv_ofNat_add_sub_left_seedChain x.c.enc.length x.tail.length
  rw [hpay, stackAt_chainMergeStackX_split_seedChain s0.sp]
  unfold sliceCursorAt
  rw [pointsToBytes_cons]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun w96 => SepWPp.exists_elim fun w88 =>
    SepWPp.exists_elim fun w80 => SepWPp.exists_elim fun w72 =>
    SepWPp.exists_elim fun w64 => SepWPp.exists_elim fun w56 =>
    SepWPp.exists_elim fun w48 => SepWPp.exists_elim fun w40 =>
    SepWPp.exists_elim fun w32 => SepWPp.exists_elim fun w24 =>
    SepWPp.exists_elim fun w16 => SepWPp.exists_elim fun w8 => ?_
  apply sepWPp_seq_lsclro_vm hcl hro (mid := (blkPl_11).base + 0x120#64)
  by_vm_steps_withSvc (
    iterate 31 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm1 hcl1 hro1
  rw [← A.pool_transport lim st₀ s0 _ hvm1]
  have hdrop0 : (x.c.fields.drop 0).flatMap ChainField.enc = x.c.enc := by
    rw [List.drop_zero, ← chainG_enc_eq_fields x.c]
  have hcur := sliceCursorAfter_append_eq_seedChain x.slot x.ptr
    [BitVec.ofNat 8 x.c.enc.length] (x.c.enc ++ x.tail)
  rw [List.singleton_append] at hcur
  refine SepWPp.weaken_pre ?_ (hloop _
    ⟨by simp only [arm64_norm], by simp only [hrun, arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm],
     hcl1, hro1, by simp only [arm64_norm], hsp_align,
     by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm],
     hcOk, hlen_lt, by simpa [chainDoneEvents] using hfit⟩)
  unfold ChainLoopBudgetSpatial
  have hchain0 : chainGAfter x.c 0 = ChainG.empty := rfl
  have hdone0 : M.stepEvents (chainDoneEvents x.c 0) st₀ = st₀ := rfl
  rw [hchain0, hdone0, hdrop0, hpay, hcur]
  simp only [ChainG.empty, List.length_nil, vecCap4Of_zero,
    List.length_singleton, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
  unfold sliceCursorAt chainMergeSavedRegs
  rw [← hlen_append]
  exact Entails.of_eq (by cb_sep_eq)

set_option maxHeartbeats 800000 in
private theorem step_chainEntry_ge128_post_budget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (x : ChainMergeGenGhost) (st₀ : M.σ) (vlen : Nat)
    {s0 s2 : State} {Q : State → SepProp → Prop}
    (hvlen : vlen = (encodeVarint (BitVec.ofNat 64 x.c.enc.length)).length)
    (hlen_tot : (x.c.payload ++ x.tail).length = vlen + (x.c.enc.length + x.tail.length))
    (hpc2 : s2.pc = (blkPl_11).base + 0x9c#64) (hrun2 : s2.status = .Running)
    (hsp2 : s2.sp = s0.sp - 256#64) (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hcl2 : LibsignalCodeLoaded lsmpl s2.mem) (hro2 : LibsignalRoLoaded lsmpl s2.mem)
    (htr2 : s2.trace = s0.trace) (hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0)
    (hx19 : s2.readReg64 .x19 = x.bufRef) (hx20 : s2.readReg64 .x20 = x.a)
    (hx21 : s2.readReg64 .x21 = x.slot) (hx22 : s2.readReg64 .x22 = 99#64)
    (hx29 : s2.readReg64 .x29 = s0.sp - 96#64)
    (hcOk : x.c.Ok) (hlen_lt : (x.c.payload ++ x.tail).length < 2 ^ 62)
    (hfit : FitsEvents M lim st₀ (chainMergeEvents x.c))
    (hloop : ∀ sm : State,
      ChainLoopBudgetInv M lim x st₀ s0 0 sm →
      SepWPp (lsProg_11 H) (s0.readReg64 .lr) sm
        (ChainLoopBudgetSpatial M A lim x st₀ s0 0 sm) Q NoPanicPost) :
    let savedTail : SepProp :=
      ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
      ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)
    SepWPp (lsProg_11 H) (s0.readReg64 .lr) s2
      (((x.bufRef ↦₆₄ x.slot) ∗ (x.slot ↦₆₄ x.ptr) ∗
        ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 (vlen + (x.c.enc.length + x.tail.length))) ∗
        ((s0.sp - 248#64) ↦₃₂ 0#32) ∗ ((s0.sp - 244#64) ↦₃₂ 0#32) ∗
        ((s0.sp - 240#64) ↦₆₄ BitVec.ofNat 64 x.c.enc.length) ∗
        ((s0.sp - 232#64) ↦₆₄ BitVec.ofNat 64 vlen)) ∗
        (x.ptr ↦ₛ (x.c.payload ++ x.tail)) ∗
        stackAt (s0.sp - 256#64) chainMergeSubStackX ∗
        memRegion (s0.sp - 256#64) 8 ∗ memRegion (s0.sp - 224#64) 128 ∗
        savedTail ∗ prostChainGAtCap A.repAlloc x.a 0 ChainG.empty ∗
        A.pool lim st₀ s2) Q NoPanicPost := by
  intro savedTail
  have hsp_sub_align : s2.sp &&& 15#64 = 0#64 := by
    rw [hsp2]; exact sp_sub_256_aligned_seedChain hsp_align
  have hlen_lt_v : vlen + (x.c.enc.length + x.tail.length) < 2 ^ 62 := by
    rw [← hlen_tot]; exact hlen_lt
  have h19 : s2.readReg64 (Reg.gpr 19#5) = x.bufRef := hx19
  have h20 : s2.readReg64 (Reg.gpr 20#5) = x.a := hx20
  have h21 : s2.readReg64 (Reg.gpr 21#5) = x.slot := hx21
  have h22 : s2.readReg64 (Reg.gpr 22#5) = 99#64 := hx22
  have h29 : s2.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64 := hx29
  have hlen_append : (x.c.enc ++ x.tail).length = x.c.enc.length + x.tail.length := List.length_append
  have hsub_vlen := bv_ofNat_add_sub_left_seedChain vlen (x.c.enc.length + x.tail.length)
  have hult_vlen := ult_ofNat_add_left_false_seedChain62 (m := vlen) (k := x.c.enc.length + x.tail.length) hlen_lt_v
  have hule_vlen := ule_ofNat_add_right_true_seedChain62 (m := vlen) (k := x.c.enc.length + x.tail.length) hlen_lt_v
  have hsub_tail := bv_ofNat_add_sub_left_seedChain x.c.enc.length x.tail.length
  have hbody_tail_lt : x.c.enc.length + x.tail.length < 2 ^ 62 := by omega
  have hule_sub := ule_ofNat_add_right_true_seedChain62 (m := x.c.enc.length) (k := x.tail.length) hbody_tail_lt
  have hult_sub := ult_ofNat_add_left_false_seedChain62 (m := x.c.enc.length) (k := x.tail.length) hbody_tail_lt
  subst hvlen
  apply sepWPp_seq_lsclro_vm hcl2 hro2 (mid := (blkPl_11).base + 0x120#64)
  by_vm_steps_withSvc (
    iterate 19 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm3 hcl3 hro3
  rw [← A.pool_transport lim st₀ s2 _ hvm3]
  let vlen0 := (encodeVarint (BitVec.ofNat 64 x.c.enc.length)).length
  have hcells := cells24_entails_memRegion24_cme s0.sp
    (BitVec.ofNat 64 x.c.enc.length) (BitVec.ofNat 64 vlen0)
  have hdrop0 : (x.c.fields.drop 0).flatMap ChainField.enc = x.c.enc := by
    rw [List.drop_zero, ← chainG_enc_eq_fields x.c]
  have hlen_sub : (x.c.payload ++ x.tail).length - (x.c.enc ++ x.tail).length = vlen0 := by
    rw [hlen_tot, hlen_append, Nat.add_sub_cancel_right]
  have hsaved : chainMergeSavedRegs s0.sp s0 =
      memRegion (s0.sp - 256#64) 8 ∗ memRegion (s0.sp - 248#64) 24 ∗
        memRegion (s0.sp - 224#64) 128 ∗ savedTail := by
    unfold chainMergeSavedRegs
    rw [memRegion160_split_varint_cme s0.sp]
    dsimp only [savedTail]; cb_sep_eq
  refine SepWPp.weaken_pre ?_ (hloop _
    ⟨by simp only [arm64_norm], by simp only [hrun2, arm64_norm],
     by simp only [htr2, arm64_norm], by simp only [hvregs2, arm64_norm],
     hcl3, hro3, by simp only [hsp2, arm64_norm], hsp_align,
     by simp only [h29, arm64_norm], by simp only [h19, arm64_norm],
     by simp only [h20, arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm],
     hcOk, hlen_lt, by simpa [chainDoneEvents] using hfit⟩)
  unfold ChainLoopBudgetSpatial
  have hchain0 : chainGAfter x.c 0 = ChainG.empty := rfl
  have hdone0 : M.stepEvents (chainDoneEvents x.c 0) st₀ = st₀ := rfl
  rw [hchain0, hdone0, hdrop0, hsaved]
  simp only [ChainG.empty, List.length_nil, vecCap4Of_zero]
  unfold sliceCursorAfter
  rw [hlen_sub, ← hlen_append]
  refine Entails.trans
    (Entails.of_eq (?_ : _ =
      (((s0.sp - 248#64) ↦₃₂ 0#32) ∗ ((s0.sp - 244#64) ↦₃₂ 0#32) ∗
        ((s0.sp - 240#64) ↦₆₄ BitVec.ofNat 64 x.c.enc.length) ∗
        ((s0.sp - 232#64) ↦₆₄ BitVec.ofNat 64 vlen0)) ∗
      (prostChainGAtCap A.repAlloc x.a 0 ChainG.empty ∗
        (x.bufRef ↦₆₄ x.slot) ∗
        ((x.ptr ↦ₛ (x.c.payload ++ x.tail)) ∗
          (x.slot ↦₆₄ (x.ptr + BitVec.ofNat 64 vlen0)) ∗
          ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 (x.c.enc ++ x.tail).length)) ∗
        A.pool lim st₀ (vmDst hvm3) ∗
        stackAt (s0.sp - 256#64) chainMergeSubStackX ∗
        memRegion (s0.sp - 256#64) 8 ∗ memRegion (s0.sp - 224#64) 128 ∗ savedTail)))
    (Entails.trans (sepConj_mono_left hcells) (Entails.of_eq (by cb_sep_eq)))
  · cb_sep_eq

set_option maxHeartbeats 800000 in
private theorem step_chainEntry_ge128_pre_budget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (x : ChainMergeGenGhost) (st₀ : M.σ) (rest0 : List (BitVec 8))
    {s0 : State} {Q : State → SepProp → Prop}
    (hpay : x.c.payload ++ x.tail = BitVec.ofNat 8 (x.c.enc.length % 128 + 128) :: rest0)
    (hgt10 : 10 < (BitVec.ofNat 8 (x.c.enc.length % 128 + 128) :: rest0).length)
    (hlen_lt0 : (BitVec.ofNat 8 (x.c.enc.length % 128 + 128) :: rest0).length < 2 ^ 62)
    (hpc : s0.pc = (blkPl_11).base) (hrun : s0.status = .Running)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s0.mem) (hro : LibsignalRoLoaded lsmpl s0.mem)
    (hx0 : (s0.readReg64 .x0).setWidth 8 = 2#8) (hx1 : s0.readReg64 .x1 = x.a)
    (hx2 : s0.readReg64 .x2 = x.bufRef) (hx3 : (s0.readReg64 .x3).setWidth 32 = 99#32)
    (hnext : ∀ s1 : State,
      s1.pc = lsmpl.base 76 → s1.status = .Running → s1.sp = s0.sp - 256#64 →
      s1.trace = s0.trace → calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      LibsignalCodeLoaded lsmpl s1.mem → LibsignalRoLoaded lsmpl s1.mem →
      s1.readReg64 .lr = (blkPl_11).base + 0x9c#64 →
      s1.readReg64 .x0 = s0.sp - 248#64 → s1.readReg64 .x1 = x.ptr →
      s1.readReg64 .x2 = BitVec.ofNat 64 (BitVec.ofNat 8 (x.c.enc.length % 128 + 128) :: rest0).length →
      s1.readReg64 .x19 = x.bufRef → s1.readReg64 .x20 = x.a →
      s1.readReg64 .x21 = x.slot → s1.readReg64 .x22 = 99#64 →
      s1.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp (lsProg_11 H) (s0.readReg64 .lr) s1
        (prostChainGAtCap A.repAlloc x.a 0 ChainG.empty ∗
          (x.bufRef ↦₆₄ x.slot) ∗
          sliceCursorAt x.slot x.ptr (x.c.payload ++ x.tail) ∗
          A.pool lim st₀ s1 ∗
          stackAt (s0.sp - 256#64) chainMergeSubStackX ∗
          chainMergeSavedRegs s0.sp s0) Q NoPanicPost) :
    SepWPp (lsProg_11 H) (s0.readReg64 .lr) s0
      (prostChainGAtCap A.repAlloc x.a 0 ChainG.empty ∗
        (x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAt x.slot x.ptr (x.c.payload ++ x.tail) ∗
        A.pool lim st₀ s0 ∗
        stackAt s0.sp chainMergeStackX) Q NoPanicPost := by
  have h1 : s0.readReg64 (Reg.gpr 1#5) = x.a := hx1
  have h2 : s0.readReg64 (Reg.gpr 2#5) = x.bufRef := hx2
  have hw3 : BitVec.truncate 32 (s0.readReg64 (Reg.gpr 3#5)) = 99#32 := hx3
  have hw0 : BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64 = 2#64 :=
    w0_and_255_eq_two_seedChain hx0
  have hcbz := cbz_len_cons_false_seedChain62 hlen_lt0
  have hlsr56 := signExtend64_contByte_lsr56_cme x.c.enc.length
  have hhi10 := ult_10_of_gt_cme62 hgt10 hlen_lt0
  have hule10 := ule_10_of_gt_false_cme62 hgt10 hlen_lt0
  rw [hpay, stackAt_chainMergeStackX_split_seedChain s0.sp]
  unfold sliceCursorAt
  rw [pointsToBytes_cons]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun w96 => SepWPp.exists_elim fun w88 =>
    SepWPp.exists_elim fun w80 => SepWPp.exists_elim fun w72 =>
    SepWPp.exists_elim fun w64 => SepWPp.exists_elim fun w56 =>
    SepWPp.exists_elim fun w48 => SepWPp.exists_elim fun w40 =>
    SepWPp.exists_elim fun w32 => SepWPp.exists_elim fun w24 =>
    SepWPp.exists_elim fun w16 => SepWPp.exists_elim fun w8 => ?_
  apply sepWPp_seq_lsclro_vm hcl hro (mid := lsmpl.base 76)
  by_vm_steps_withSvc (
    iterate 24 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm1 hcl1 hro1
  rw [← A.pool_transport lim st₀ s0 _ hvm1]
  refine SepWPp.weaken_pre ?_ (hnext _
    (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    hcl1 hro1
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]))
  rw [hpay]
  unfold sliceCursorAt chainMergeSavedRegs
  rw [pointsToBytes_cons]
  exact Entails.of_eq (by cb_sep_eq)

private theorem step_chainEntry_budget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (x : ChainMergeGenGhost) (st₀ : M.σ) {s0 : State} {Q : State → SepProp → Prop}
    (hpc : s0.pc = (blkPl_11).base) (hrun : s0.status = .Running)
    (hal : s0.spAligned = true)
    (hcl : LibsignalCodeLoaded lsmpl s0.mem) (hro : LibsignalRoLoaded lsmpl s0.mem)
    (hx0 : (s0.readReg64 .x0).setWidth 8 = 2#8) (hx1 : s0.readReg64 .x1 = x.a)
    (hx2 : s0.readReg64 .x2 = x.bufRef) (hx3 : (s0.readReg64 .x3).setWidth 32 = 99#32)
    (hcOk : x.c.Ok) (hlen_lt : (x.c.payload ++ x.tail).length < 2 ^ 62)
    (hfit : FitsEvents M lim st₀ (chainMergeEvents x.c))
    (hloop : ∀ sm : State,
      ChainLoopBudgetInv M lim x st₀ s0 0 sm →
      SepWPp (lsProg_11 H) (s0.readReg64 .lr) sm
        (ChainLoopBudgetSpatial M A lim x st₀ s0 0 sm) Q NoPanicPost) :
    SepWPp (lsProg_11 H) (s0.readReg64 .lr) s0
      (prostChainGAtCap A.repAlloc x.a 0 ChainG.empty ∗
        (x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAt x.slot x.ptr (x.c.payload ++ x.tail) ∗
        A.pool lim st₀ s0 ∗
        stackAt s0.sp chainMergeStackX) Q NoPanicPost := by
  have hsp_align : s0.sp &&& 15#64 = 0#64 := by simpa [State.spAligned, beq_iff_eq] using hal
  by_cases hbody_lt : x.c.enc.length < 128
  · exact step_chainEntry_1byte_budget x st₀ hbody_lt hpc hrun hsp_align hcl hro
      hx0 hx1 hx2 hx3 hcOk hlen_lt hfit hloop
  · have hbody_ge : 128 ≤ x.c.enc.length := by omega
    have hbody_lt62 : x.c.enc.length < 2 ^ 62 := by
      unfold ChainG.payload at hlen_lt; simp only [List.length_append] at hlen_lt; omega
    obtain ⟨vtail, hvar⟩ := encodeVarint_ge128_cons_cme62 hbody_ge hbody_lt62
    let b0 := BitVec.ofNat 8 (x.c.enc.length % 128 + 128)
    let rest0 := vtail ++ (x.c.enc ++ x.tail)
    have hpay : x.c.payload ++ x.tail = b0 :: rest0 := by
      unfold ChainG.payload; dsimp only [b0, rest0]
      rw [hvar, List.cons_append, List.cons_append, List.append_assoc]
    have hgt10 : 10 < (b0 :: rest0).length := by
      rw [← hpay]; unfold ChainG.payload; simp only [List.length_append]; omega
    have hlen_lt0 : (b0 :: rest0).length < 2 ^ 62 := by rw [← hpay]; exact hlen_lt
    refine step_chainEntry_ge128_pre_budget x st₀ rest0 hpay hgt10 hlen_lt0
      hpc hrun hsp_align hcl hro hx0 hx1 hx2 hx3 ?_
    intro s1 hpc1 hrun1 hsp1 htr1 hvregs1 hcl1 hro1 hlr1 hx0_1 hx1_1 hx2_1 hx19_1 hx20_1 hx21_1 hx22_1 hx29_1
    have hsub_vs := decode_varint_slice_some_placed_ok_cl
      (callerProg := lsProg_11 H) (errStack := decodeErrorHookStackW) (by decide)
    have hal1 : s1.spAligned = true := by
      simp only [State.spAligned, hsp1, beq_iff_eq]
      exact sp_sub_256_aligned_seedChain hsp_align
    have hx2_1_nat : (s1.readReg64 .x2).toNat = (x.c.payload ++ x.tail).length := by
      rw [hx2_1, ← hpay, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hlen_lt63 : (x.c.payload ++ x.tail).length < 2 ^ 63 := Nat.lt_trans hlen_lt (by decide)
    have hpre_slice : VarintSlicePre (x.c.payload ++ x.tail) := by
      refine Or.inl ?_; rw [hpay]; omega
    have hpay_split : x.c.payload ++ x.tail =
        encodeVarint (BitVec.ofNat 64 x.c.enc.length) ++ (x.c.enc ++ x.tail) := by
      unfold ChainG.payload; rw [List.append_assoc]
    have hdec : decodeVarint (x.c.payload ++ x.tail) =
        some (BitVec.ofNat 64 x.c.enc.length, x.c.enc ++ x.tail) := by
      rw [hpay_split]; exact decodeVarint_encodeVarint (BitVec.ofNat 64 x.c.enc.length) (x.c.enc ++ x.tail)
    let vlen := (encodeVarint (BitVec.ofNat 64 x.c.enc.length)).length
    have hlen_sub : (x.c.payload ++ x.tail).length - (x.c.enc ++ x.tail).length = vlen := by
      rw [hpay_split, List.length_append, Nat.add_sub_cancel_right]
    have hlen_tot : (x.c.payload ++ x.tail).length = vlen + (x.c.enc.length + x.tail.length) := by
      rw [hpay_split, List.length_append, List.length_append]
    let savedTail : SepProp :=
      ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
      ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)
    have hsaved : chainMergeSavedRegs s0.sp s0 =
        memRegion (s0.sp - 256#64) 8 ∗ memRegion (s0.sp - 248#64) 24 ∗
          memRegion (s0.sp - 224#64) 128 ∗ savedTail := by
      unfold chainMergeSavedRegs
      rw [memRegion160_split_varint_cme s0.sp]
      dsimp only [savedTail]; cb_sep_eq
    let gvs : DecodeVarintSliceGhost := ⟨s0.sp - 248#64, x.ptr, x.c.payload ++ x.tail⟩
    let F_vs : SepProp :=
      (x.bufRef ↦₆₄ x.slot) ∗ (x.slot ↦₆₄ x.ptr) ∗
      ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 (x.c.payload ++ x.tail).length) ∗
      memRegion (s0.sp - 256#64 - BitVec.ofNat 64 chainMergeSubStackX)
        (chainMergeSubStackX - decodeVarintSliceStackW) ∗
      memRegion (s0.sp - 256#64) 8 ∗ memRegion (s0.sp - 224#64) 128 ∗
      savedTail ∗ prostChainGAtCap A.repAlloc x.a 0 ChainG.empty ∗ A.pool lim st₀ s1
    have hstk_vs : 0x50 + decodeErrorHookStackW = decodeVarintSliceStackW := rfl
    refine sepWPp_call_lscl
      (x := (gvs, BitVec.ofNat 64 x.c.enc.length, x.c.enc ++ x.tail)) (F := F_vs)
      hsub_vs hcl1 hro1 hpc1 hrun1 hal1 hlr1 ?_
      (fun _ _ h => not_satisfies_false_sepConj h)
      (fun _ _ _ h => not_satisfies_false_sepConj h)
      (fun _ _ h => not_satisfies_false_sepConj h) ?_
    · dsimp only [decodeVarintSliceSomeSpecGen, gvs, F_vs]
      rw [hsp1, hstk_vs, stackAt_sub_to_varintSlice_cmeW (s0.sp - 256#64), hsaved]
      unfold sliceCursorAt
      have hgrp :
          prostChainGAtCap A.repAlloc x.a 0 ChainG.empty ∗
            (x.bufRef ↦₆₄ x.slot) ∗
            ((x.slot ↦₆₄ x.ptr) ∗
              ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 (x.c.payload ++ x.tail).length) ∗
              (x.ptr ↦ₛ (x.c.payload ++ x.tail))) ∗
            A.pool lim st₀ s1 ∗
            (memRegion (s0.sp - 256#64 - BitVec.ofNat 64 chainMergeSubStackX)
              (chainMergeSubStackX - decodeVarintSliceStackW) ∗
              stackAt (s0.sp - 256#64) decodeVarintSliceStackW) ∗
            (memRegion (s0.sp - 256#64) 8 ∗ memRegion (s0.sp - 248#64) 24 ∗
              memRegion (s0.sp - 224#64) 128 ∗ savedTail) =
          (memRegion (s0.sp - 248#64) 24 ∗
            (x.ptr ↦ₛ (x.c.payload ++ x.tail)) ∗
            stackAt (s0.sp - 256#64) decodeVarintSliceStackW) ∗
          ((x.bufRef ↦₆₄ x.slot) ∗ (x.slot ↦₆₄ x.ptr) ∗
            ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 (x.c.payload ++ x.tail).length) ∗
            memRegion (s0.sp - 256#64 - BitVec.ofNat 64 chainMergeSubStackX)
              (chainMergeSubStackX - decodeVarintSliceStackW) ∗
            memRegion (s0.sp - 256#64) 8 ∗ memRegion (s0.sp - 224#64) 128 ∗
            savedTail ∗ prostChainGAtCap A.repAlloc x.a 0 ChainG.empty ∗ A.pool lim st₀ s1) := by
        cb_sep_eq
      rw [hgrp]
      exact sepConj_mono_left (Entails.pure_right
        ⟨hx0_1, hx1_1, hx2_1_nat, hlen_lt63, hpre_slice, hdec⟩ (Entails.refl _))
    · intro s2 hpc2 hrun2 hsp2 hcs2 hcl2 hro2
      rw [hsp1] at hsp2
      dsimp only [decodeVarintSliceSomeSpecGen, gvs, F_vs]
      rw [hsp1, hstk_vs, sepConj_assoc]
      refine sepWPp_pure_left_and fun ⟨htr2, hvm2⟩ => ?_
      rw [← A.pool_transport lim st₀ s1 s2 hvm2]
      have ha8 : (s0.sp - 248#64) + 8#64 = s0.sp - 240#64 := by
        simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
      have ha16 : (s0.sp - 248#64) + 16#64 = s0.sp - 232#64 := by
        simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
      refine SepWPp.weaken_pre ?_
        (step_chainEntry_ge128_post_budget x st₀ vlen rfl hlen_tot
          hpc2 hrun2 hsp2 hsp_align hcl2 hro2 (htr2.trans htr1)
          (hcs2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs1)
          (hcs2.1.trans hx19_1) (hcs2.2.1.trans hx20_1)
          (hcs2.2.2.1.trans hx21_1) (hcs2.2.2.2.1.trans hx22_1)
          (hcs2.2.2.2.2.2.2.2.2.2.2.1.trans hx29_1)
          hcOk hlen_lt hfit hloop)
      rw [ha8, ha16, hlen_sub, hlen_tot, pointsTo64_zero_split32_cme s0.sp,
        stackAt_sub_to_varintSlice_cmeW (s0.sp - 256#64)]
      exact Entails.of_eq (by cb_sep_eq)

private def LoopRegs (sp0 bufRef a : BitVec 64) (tailLen : Nat) (s : State) : Prop :=
  s.sp = sp0 - 256#64 ∧
    s.readReg64 .x29 = sp0 - 96#64 ∧
    s.readReg64 .x19 = bufRef ∧
    s.readReg64 .x20 = a ∧
    s.readReg64 .x24 = BitVec.ofNat 64 tailLen ∧
    s.readReg64 .x21 = 98#64 ∧
    s.readReg64 .x22 = 97#64 ∧
    s.readReg64 .x25 = sp0 - 248#64 ∧
    s.readReg64 .x26 = 1#64

private theorem LoopRegs.of_calleeSaved {sp0 bufRef a : BitVec 64} {tailLen : Nat} {s1 s2 : State}
    (h1 : LoopRegs sp0 bufRef a tailLen s1) (hsp2 : s2.sp = sp0 - 256#64)
    (hcs : CalleeSavedPreserved s1 s2) :
    LoopRegs sp0 bufRef a tailLen s2 := by
  rcases hcs with ⟨c19, c20, c21, c22, _, c24, c25, c26, _, _, c29, _⟩
  rcases h1 with ⟨_, h29, h19, h20, h24, h21, h22, h25, h26⟩
  exact ⟨hsp2, c29.trans h29, c19.trans h19, c20.trans h20, c24.trans h24,
    c21.trans h21, c22.trans h22, c25.trans h25, c26.trans h26⟩

set_option maxHeartbeats 800000 in
private theorem step_chainTag1_raw_budget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H)
    (a bufRef slot ptr sp0 : BitVec 64)
    (srk rest tail : List (BitVec 8)) (st : M.σ)
    (hsrk_lt : srk.length < 128)
    (hlen_lt : (pbBytes 1 srk ++ rest ++ tail).length < 2 ^ 62)
    (hfit : FitsEvents M lim st (bytesMergeEvents 0 srk.length))
    {ret : BitVec 64} {s0 s : State} {F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_11).base + 0x120#64) (hrun : s.status = .Running)
    (halign : sp0 &&& 15#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hro : LibsignalRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : LoopRegs sp0 bufRef a tail.length s)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_11).base + 0x120#64 → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → LibsignalRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace → calleeSavedVRegs sm = calleeSavedVRegs s0 →
      LoopRegs sp0 bufRef a tail.length sm →
      SepWPp (lsProg_11 H) ret sm
        (((bufRef ↦₆₄ slot) ∗
          vecU8FreshCap A.repAlloc a srk ∗
          (ptr ↦ₛ pbBytes 1 srk) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbBytes 1 srk).length) (rest ++ tail) ∗
          A.pool lim (M.stepEvents (bytesMergeEvents 0 srk.length) st) sm ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F) Q NoPanicPost) :
    SepWPp (lsProg_11 H) ret s
      (((bufRef ↦₆₄ slot) ∗
        vecU8FreshCap A.repAlloc a [] ∗
        sliceCursorAt slot ptr (pbBytes 1 srk ++ (rest ++ tail)) ∗
        A.pool lim st s ∗
        stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F) Q NoPanicPost := by
  rcases hregs with ⟨hsp, hx29, hx19, hx20, hx24, hx21, hx22, hx25, hx26⟩
  have hpb : pbBytes 1 srk = 0x0a#8 :: BitVec.ofNat 8 srk.length :: srk :=
    pbBytes_lt128_eq_seedChain 1 (by decide) srk hsrk_lt
  let rem1 : List (BitVec 8) := [BitVec.ofNat 8 srk.length] ++ srk ++ (rest ++ tail)
  have hcons_eq : pbBytes 1 srk ++ (rest ++ tail) = 0x0a#8 :: rem1 := by
    rw [hpb]; simp [rem1, List.cons_append, List.append_assoc]
  have hlen_gt : tail.length < (0x0a#8 :: rem1).length := by
    simp only [rem1, List.length_cons, List.length_append]; omega
  have hlen_cons_lt : (0x0a#8 :: rem1).length < 2 ^ 62 := by
    rw [← hcons_eq]; simpa [List.append_assoc] using hlen_lt
  have hule_ls := ule_ofNat_of_gt_false_seedChain62 hlen_gt hlen_cons_lt
  have hult_ls := ult_ofNat_of_gt_true_seedChain62 hlen_gt hlen_cons_lt
  have hsub1 := len_cons_sub_one_seedChain 0x0a#8 rem1
  have h19 : s.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h20 : s.readReg64 (Reg.gpr 20#5) = a := hx20
  have h24 : s.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 tail.length := hx24
  have h21 : s.readReg64 (Reg.gpr 21#5) = 98#64 := hx21
  have h22 : s.readReg64 (Reg.gpr 22#5) = 97#64 := hx22
  have h25 : s.readReg64 (Reg.gpr 25#5) = sp0 - 248#64 := hx25
  have h26 : s.readReg64 (Reg.gpr 26#5) = 1#64 := hx26
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp0 - 96#64 := hx29
  refine (?_ :
    (∀ s1 : State,
      s1.pc = lsmpl.base 7 → s1.status = .Running →
      LibsignalCodeLoaded lsmpl s1.mem → LibsignalRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace → calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      s1.readReg64 .lr = (blkPl_11).base + 0x25c#64 →
      (s1.readReg64 .x0).setWidth 8 = 2#8 → s1.readReg64 .x1 = a → s1.readReg64 .x2 = bufRef →
      LoopRegs sp0 bufRef a tail.length s1 →
      SepWPp (lsProg_11 H) ret s1
        ((vecU8FreshCap A.repAlloc a [] ∗
          (bufRef ↦₆₄ slot) ∗
          sliceCursorAt slot (ptr + 1#64) rem1 ∗
          A.pool lim st s1 ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ ((ptr ↦₈ 0x0a#8) ∗ F)) Q NoPanicPost) → _) ?_
  · intro hnext1
    rw [hcons_eq]
    unfold sliceCursorAt
    rw [pointsToBytes_cons]
    apply sepWPp_seq_lsclro_vm hcl hro (mid := lsmpl.base 7)
    by_vm_steps_withSvc (
      iterate 26 wp_step
      refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
    intro hvm1 hcl1 hro1
    rw [← A.pool_transport lim st s _ hvm1]
    refine SepWPp.weaken_pre ?_ (hnext1 _
      (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      hcl1 hro1 (by simp only [htr, arm64_norm]) (by simp only [hvregs, arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      ⟨by simp only [hsp, arm64_norm], by simp only [h29, arm64_norm],
       by simp only [h19, arm64_norm], by simp only [h20, arm64_norm],
       by simp only [h24, arm64_norm], by simp only [h21, arm64_norm],
       by simp only [h22, arm64_norm], by simp only [h25, arm64_norm],
       by simp only [h26, arm64_norm]⟩)
    unfold sliceCursorAt
    exact Entails.of_eq (by cb_sep_eq)
  · intro s1 hpc1 hrun1 hcl1 hro1 htr1 hvregs1 hlr1 hx0_1 hx1_1 hx2_1 hregs1
    have hrem1_lt : ([BitVec.ofNat 8 srk.length] ++ srk ++ (rest ++ tail)).length < 2 ^ 62 := by
      simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
    refine step_chainMerge_bytesMergeFresh_budget hA a bufRef slot (ptr + 1#64) sp0
      ((blkPl_11).base + 0x25c#64) srk (rest ++ tail) st hsrk_lt hrem1_lt hfit
      hpc1 hrun1 hregs1.1 halign hcl1 hro1 htr1 hlr1 hx0_1 hx1_1 hx2_1 ?_
    intro s2 hpc2 hrun2 hsp2 hcl2 hro2 htr2 hcs2 hx0_2
    have hregs2 := hregs1.of_calleeSaved hsp2 hcs2
    have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := by
      rcases hcs2 with ⟨_, _, _, _, _, _, _, _, _, _, _, hcv⟩; exact hcv.trans hvregs1
    rcases hregs2 with ⟨hsp2, hx29_2, hx19_2, hx20_2, hx24_2, hx21_2, hx22_2, hx25_2, hx26_2⟩
    have h0_2 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    apply sepWPp_seq_lsclro_vm hcl2 hro2 (mid := (blkPl_11).base + 0x120#64)
    by_vm_steps_withSvc (
      iterate 2 wp_step
      refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
    intro hvm3 hcl3 hro3
    rw [← A.pool_transport lim _ s2 _ hvm3]
    refine SepWPp.weaken_pre ?_ (hnext _
      (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
      hcl3 hro3 (by simp only [htr2, arm64_norm]) (by simp only [hvregs2, arm64_norm])
      ⟨by simp only [hsp2, arm64_norm], by simp only [hx29_2, arm64_norm],
       by simp only [hx19_2, arm64_norm], by simp only [hx20_2, arm64_norm],
       by simp only [hx24_2, arm64_norm], by simp only [hx21_2, arm64_norm],
       by simp only [hx22_2, arm64_norm], by simp only [hx25_2, arm64_norm],
       by simp only [hx26_2, arm64_norm]⟩)
    rw [pbBytes_ptr_advance_seedChain 1 (by decide) ptr srk hsrk_lt,
      ← pbBytes_pointsTo_combine_seedChain 1 (by decide) ptr srk hsrk_lt]
    exact Entails.of_eq (by cb_sep_eq)

set_option maxHeartbeats 800000 in
private theorem step_chainTag2_raw_budget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H)
    (a bufRef slot ptr sp0 : BitVec 64)
    (priv rest tail : List (BitVec 8)) (st : M.σ)
    (hpriv_lt : priv.length < 128)
    (hlen_lt : (pbBytes 2 priv ++ rest ++ tail).length < 2 ^ 62)
    (hfit : FitsEvents M lim st (bytesMergeEvents 0 priv.length))
    {ret : BitVec 64} {s0 s : State} {F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_11).base + 0x120#64) (hrun : s.status = .Running)
    (halign : sp0 &&& 15#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hro : LibsignalRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : LoopRegs sp0 bufRef a tail.length s)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_11).base + 0x120#64 → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → LibsignalRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace → calleeSavedVRegs sm = calleeSavedVRegs s0 →
      LoopRegs sp0 bufRef a tail.length sm →
      SepWPp (lsProg_11 H) ret sm
        (((bufRef ↦₆₄ slot) ∗
          vecU8FreshCap A.repAlloc (a + 0x18#64) priv ∗
          (ptr ↦ₛ pbBytes 2 priv) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbBytes 2 priv).length) (rest ++ tail) ∗
          A.pool lim (M.stepEvents (bytesMergeEvents 0 priv.length) st) sm ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F) Q NoPanicPost) :
    SepWPp (lsProg_11 H) ret s
      (((bufRef ↦₆₄ slot) ∗
        vecU8FreshCap A.repAlloc (a + 0x18#64) [] ∗
        sliceCursorAt slot ptr (pbBytes 2 priv ++ (rest ++ tail)) ∗
        A.pool lim st s ∗
        stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F) Q NoPanicPost := by
  rcases hregs with ⟨hsp, hx29, hx19, hx20, hx24, hx21, hx22, hx25, hx26⟩
  have hpb : pbBytes 2 priv = 0x12#8 :: BitVec.ofNat 8 priv.length :: priv :=
    pbBytes_lt128_eq_seedChain 2 (by decide) priv hpriv_lt
  let rem1 : List (BitVec 8) := [BitVec.ofNat 8 priv.length] ++ priv ++ (rest ++ tail)
  have hcons_eq : pbBytes 2 priv ++ (rest ++ tail) = 0x12#8 :: rem1 := by
    rw [hpb]; simp [rem1, List.cons_append, List.append_assoc]
  have hlen_gt : tail.length < (0x12#8 :: rem1).length := by
    simp only [rem1, List.length_cons, List.length_append]; omega
  have hlen_cons_lt : (0x12#8 :: rem1).length < 2 ^ 62 := by
    rw [← hcons_eq]; simpa [List.append_assoc] using hlen_lt
  have hule_ls := ule_ofNat_of_gt_false_seedChain62 hlen_gt hlen_cons_lt
  have hult_ls := ult_ofNat_of_gt_true_seedChain62 hlen_gt hlen_cons_lt
  have hsub1 := len_cons_sub_one_seedChain 0x12#8 rem1
  have h19 : s.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h20 : s.readReg64 (Reg.gpr 20#5) = a := hx20
  have h24 : s.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 tail.length := hx24
  have h21 : s.readReg64 (Reg.gpr 21#5) = 98#64 := hx21
  have h22 : s.readReg64 (Reg.gpr 22#5) = 97#64 := hx22
  have h25 : s.readReg64 (Reg.gpr 25#5) = sp0 - 248#64 := hx25
  have h26 : s.readReg64 (Reg.gpr 26#5) = 1#64 := hx26
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp0 - 96#64 := hx29
  refine (?_ :
    (∀ s1 : State,
      s1.pc = lsmpl.base 7 → s1.status = .Running →
      LibsignalCodeLoaded lsmpl s1.mem → LibsignalRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace → calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      s1.readReg64 .lr = (blkPl_11).base + 0x1d0#64 →
      (s1.readReg64 .x0).setWidth 8 = 2#8 →
      s1.readReg64 .x1 = a + 0x18#64 → s1.readReg64 .x2 = bufRef →
      LoopRegs sp0 bufRef a tail.length s1 →
      SepWPp (lsProg_11 H) ret s1
        ((vecU8FreshCap A.repAlloc (a + 0x18#64) [] ∗
          (bufRef ↦₆₄ slot) ∗
          sliceCursorAt slot (ptr + 1#64) rem1 ∗
          A.pool lim st s1 ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ ((ptr ↦₈ 0x12#8) ∗ F)) Q NoPanicPost) → _) ?_
  · intro hnext1
    rw [hcons_eq]
    unfold sliceCursorAt
    rw [pointsToBytes_cons]
    apply sepWPp_seq_lsclro_vm hcl hro (mid := lsmpl.base 7)
    by_vm_steps_withSvc (
      iterate 28 wp_step
      refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
    intro hvm1 hcl1 hro1
    rw [← A.pool_transport lim st s _ hvm1]
    refine SepWPp.weaken_pre ?_ (hnext1 _
      (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      hcl1 hro1 (by simp only [htr, arm64_norm]) (by simp only [hvregs, arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      ⟨by simp only [hsp, arm64_norm], by simp only [h29, arm64_norm],
       by simp only [h19, arm64_norm], by simp only [h20, arm64_norm],
       by simp only [h24, arm64_norm], by simp only [h21, arm64_norm],
       by simp only [h22, arm64_norm], by simp only [h25, arm64_norm],
       by simp only [h26, arm64_norm]⟩)
    unfold sliceCursorAt
    exact Entails.of_eq (by cb_sep_eq)
  · intro s1 hpc1 hrun1 hcl1 hro1 htr1 hvregs1 hlr1 hx0_1 hx1_1 hx2_1 hregs1
    have hrem1_lt : ([BitVec.ofNat 8 priv.length] ++ priv ++ (rest ++ tail)).length < 2 ^ 62 := by
      simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
    refine step_chainMerge_bytesMergeFresh_budget hA (a + 0x18#64) bufRef slot (ptr + 1#64) sp0
      ((blkPl_11).base + 0x1d0#64) priv (rest ++ tail) st hpriv_lt hrem1_lt hfit
      hpc1 hrun1 hregs1.1 halign hcl1 hro1 htr1 hlr1 hx0_1 hx1_1 hx2_1 ?_
    intro s2 hpc2 hrun2 hsp2 hcl2 hro2 htr2 hcs2 hx0_2
    have hregs2 := hregs1.of_calleeSaved hsp2 hcs2
    have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := by
      rcases hcs2 with ⟨_, _, _, _, _, _, _, _, _, _, _, hcv⟩; exact hcv.trans hvregs1
    rcases hregs2 with ⟨hsp2, hx29_2, hx19_2, hx20_2, hx24_2, hx21_2, hx22_2, hx25_2, hx26_2⟩
    have h0_2 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    apply sepWPp_seq_lsclro_vm hcl2 hro2 (mid := (blkPl_11).base + 0x120#64)
    by_vm_steps_withSvc (
      iterate 2 wp_step
      refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
    intro hvm3 hcl3 hro3
    rw [← A.pool_transport lim _ s2 _ hvm3]
    refine SepWPp.weaken_pre ?_ (hnext _
      (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
      hcl3 hro3 (by simp only [htr2, arm64_norm]) (by simp only [hvregs2, arm64_norm])
      ⟨by simp only [hsp2, arm64_norm], by simp only [hx29_2, arm64_norm],
       by simp only [hx19_2, arm64_norm], by simp only [hx20_2, arm64_norm],
       by simp only [hx24_2, arm64_norm], by simp only [hx21_2, arm64_norm],
       by simp only [hx22_2, arm64_norm], by simp only [hx25_2, arm64_norm],
       by simp only [hx26_2, arm64_norm]⟩)
    rw [pbBytes_ptr_advance_seedChain 2 (by decide) ptr priv hpriv_lt,
      ← pbBytes_pointsTo_combine_seedChain 2 (by decide) ptr priv hpriv_lt]
    exact Entails.of_eq (by cb_sep_eq)

private theorem step_chainTag12_budget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H)
    (x : ChainMergeGenGhost) (st₀ : M.σ) {s0 s : State} {k : Nat}
    {Q : State → SepProp → Prop}
    (hk : k < x.c.fields.length)
    (htag : (x.c.fields[k]'hk).tag = 1 ∨ (x.c.fields[k]'hk).tag = 2)
    (hinv : ChainLoopBudgetInv M lim x st₀ s0 k s)
    (hnext : ∀ sm : State,
      ChainLoopBudgetInv M lim x st₀ s0 (k + 1) sm →
      SepWPp (lsProg_11 H) (s0.readReg64 .lr) sm
        (ChainLoopBudgetSpatial M A lim x st₀ s0 (k + 1) sm) Q NoPanicPost) :
    SepWPp (lsProg_11 H) (s0.readReg64 .lr) s
      (ChainLoopBudgetSpatial M A lim x st₀ s0 k s) Q NoPanicPost := by
  rcases hinv with ⟨hpc, hrun, htr, hvregs, hcl, hro, hsp, halign,
    hx29, hx19, hx20, hx24, hx21, hx22, hx25, hx26, hcOk, hlen, hfit⟩
  have hregs0 : LoopRegs s0.sp x.bufRef x.a x.tail.length s :=
    ⟨hsp, hx29, hx19, hx20, hx24, hx21, hx22, hx25, hx26⟩
  obtain ⟨hfit_step, hfit_rem⟩ := chainLoop_fits_split hk hfit
  let rest : List (BitVec 8) := (x.c.fields.drop (k + 1)).flatMap ChainField.enc
  have hlen_rem : ((x.c.fields[k]'hk).enc ++ rest ++ x.tail).length < 2 ^ 62 := by
    have h1 := hlen
    rw [payload_append_eq_preBytes x.c x.tail k, drop_flatMap_enc hk] at h1
    simp only [rest, List.length_append] at h1 ⊢; omega
  let ck := chainGAfter x.c k
  let capMk := vecCap4Of ck.keys.length
  let st_k := M.stepEvents (chainDoneEvents x.c k) st₀
  generalize hfl_eq : x.c.fields[k]'hk = fl
  cases fl with
  | ck i key =>
    rw [hfl_eq] at htag; simp [ChainField.tag] at htag
  | key mk =>
    rw [hfl_eq] at htag; simp [ChainField.tag] at htag
  | srk b =>
    have hb_mem : ChainField.srk b ∈ x.c.fields := hfl_eq ▸ List.getElem_mem hk
    have hb_lt : b.length < 128 := mem_fields_srk_length_lt hcOk hb_mem
    have henc : (x.c.fields[k]'hk).enc = pbBytes 1 b := by
      rw [hfl_eq]; exact lenField_eq_pbBytes 1 (Or.inl rfl) b hb_lt
    have hlen_pb : (pbBytes 1 b ++ rest ++ x.tail).length < 2 ^ 62 := by rwa [← henc]
    have hck_srk : ck.srk = [] := chainGAfter_srk_eq_nil hk hfl_eq
    have hfit_b : FitsEvents M lim st_k (bytesMergeEvents 0 b.length) := by
      simpa [st_k, hfl_eq, chainFieldStepEvents] using hfit_step
    have hst_succ :
        M.stepEvents (bytesMergeEvents 0 b.length) st_k =
          M.stepEvents (chainDoneEvents x.c (k + 1)) st₀ := by
      rw [chainDoneEvents_succ_of_lt hk, AllocCostModel.stepEvents_append, hfl_eq]
      rfl
    let ckRest : SepProp :=
      vecU8FreshCap A.repAlloc (x.a + 0x18#64) ck.priv ∗
        (∃∗ ptrMk : BitVec 64,
          vecAt A.repAlloc 104 8 (fun mk p => prostMsgKeyAtCap A.repAlloc mk p)
            (x.a + 0x30#64) (BitVec.ofNat 64 capMk) ptrMk ck.keys) ∗
        match ck.ck with
        | none => ((x.a + 0x48#64) ↦₆₄ noneCap) ∗ memRegion (x.a + 0x50#64) 24
        | some (i, key) => vecU8FreshCap A.repAlloc (x.a + 0x48#64) key ∗
            ((x.a + 0x60#64) ↦₃₂ i) ∗ memRegion (x.a + 0x64#64) 4
    let F1 : SepProp :=
      (x.ptr ↦ₛ preBytes x.c k) ∗ ckRest ∗ chainMergeSavedRegs s0.sp s0
    refine SepWPp.weaken_pre
      (P' := (((x.bufRef ↦₆₄ x.slot) ∗
        vecU8FreshCap A.repAlloc x.a [] ∗
        sliceCursorAt x.slot (curPtr x.ptr x.c k) (pbBytes 1 b ++ (rest ++ x.tail)) ∗
        A.pool lim st_k s ∗
        stackAt (s0.sp - 256#64) chainMergeSubStackX) ∗ F1))
      (by
        unfold ChainLoopBudgetSpatial prostChainGAtCap
        dsimp only [ck, capMk, st_k, F1, ckRest, rest]
        rw [hck_srk, sliceCursorAfter_eq_preBytes x.slot x.ptr x.c x.tail k,
          drop_flatMap_enc hk, henc, List.append_assoc]
        exact Entails.of_eq (by cb_sep_eq))
      (step_chainTag1_raw_budget hA x.a x.bufRef x.slot (curPtr x.ptr x.c k) s0.sp
        b rest x.tail st_k hb_lt hlen_pb hfit_b hpc hrun halign hcl hro htr hvregs hregs0 ?_)
    intro sm hpcm hrunm hclm hrom htrm hvregsm hregsm
    rcases hregsm with ⟨hspm, hx29m, hx19m, hx20m, hx24m, hx21m, hx22m, hx25m, hx26m⟩
    refine SepWPp.weaken_pre ?_ (hnext sm
      ⟨hpcm, hrunm, htrm, hvregsm, hclm, hrom, hspm, halign,
       hx29m, hx19m, hx20m, hx24m, hx21m, hx22m, hx25m, hx26m, hcOk, hlen, hfit_rem⟩)
    unfold ChainLoopBudgetSpatial prostChainGAtCap
    have hc_succ : chainGAfter x.c (k + 1) = { ck with srk := b } := by
      rw [chainGAfter_succ hk, hfl_eq]; rfl
    rw [hst_succ, hc_succ, ← henc, ← curPtr_succ x.ptr hk,
      sliceCursorAfter_eq_preBytes x.slot x.ptr x.c x.tail (k + 1),
      ← pointsToBytes_preBytes_succ x.ptr hk]
    dsimp only [ck, capMk, F1, ckRest, rest]
    exact Entails.of_eq (by cb_sep_eq)
  | priv b =>
    have hb_mem : ChainField.priv b ∈ x.c.fields := hfl_eq ▸ List.getElem_mem hk
    have hb_lt : b.length < 128 := mem_fields_priv_length_lt hcOk hb_mem
    have henc : (x.c.fields[k]'hk).enc = pbBytes 2 b := by
      rw [hfl_eq]; exact lenField_eq_pbBytes 2 (Or.inr rfl) b hb_lt
    have hlen_pb : (pbBytes 2 b ++ rest ++ x.tail).length < 2 ^ 62 := by rwa [← henc]
    have hck_priv : ck.priv = [] := chainGAfter_priv_eq_nil hk hfl_eq
    have hfit_b : FitsEvents M lim st_k (bytesMergeEvents 0 b.length) := by
      simpa [st_k, hfl_eq, chainFieldStepEvents] using hfit_step
    have hst_succ :
        M.stepEvents (bytesMergeEvents 0 b.length) st_k =
          M.stepEvents (chainDoneEvents x.c (k + 1)) st₀ := by
      rw [chainDoneEvents_succ_of_lt hk, AllocCostModel.stepEvents_append, hfl_eq]
      rfl
    let ckRest : SepProp :=
      vecU8FreshCap A.repAlloc x.a ck.srk ∗
        (∃∗ ptrMk : BitVec 64,
          vecAt A.repAlloc 104 8 (fun mk p => prostMsgKeyAtCap A.repAlloc mk p)
            (x.a + 0x30#64) (BitVec.ofNat 64 capMk) ptrMk ck.keys) ∗
        match ck.ck with
        | none => ((x.a + 0x48#64) ↦₆₄ noneCap) ∗ memRegion (x.a + 0x50#64) 24
        | some (i, key) => vecU8FreshCap A.repAlloc (x.a + 0x48#64) key ∗
            ((x.a + 0x60#64) ↦₃₂ i) ∗ memRegion (x.a + 0x64#64) 4
    let F2 : SepProp :=
      (x.ptr ↦ₛ preBytes x.c k) ∗ ckRest ∗ chainMergeSavedRegs s0.sp s0
    refine SepWPp.weaken_pre
      (P' := (((x.bufRef ↦₆₄ x.slot) ∗
        vecU8FreshCap A.repAlloc (x.a + 0x18#64) [] ∗
        sliceCursorAt x.slot (curPtr x.ptr x.c k) (pbBytes 2 b ++ (rest ++ x.tail)) ∗
        A.pool lim st_k s ∗
        stackAt (s0.sp - 256#64) chainMergeSubStackX) ∗ F2))
      (by
        unfold ChainLoopBudgetSpatial prostChainGAtCap
        dsimp only [ck, capMk, st_k, F2, ckRest, rest]
        rw [hck_priv, sliceCursorAfter_eq_preBytes x.slot x.ptr x.c x.tail k,
          drop_flatMap_enc hk, henc, List.append_assoc]
        exact Entails.of_eq (by cb_sep_eq))
      (step_chainTag2_raw_budget hA x.a x.bufRef x.slot (curPtr x.ptr x.c k) s0.sp
        b rest x.tail st_k hb_lt hlen_pb hfit_b hpc hrun halign hcl hro htr hvregs hregs0 ?_)
    intro sm hpcm hrunm hclm hrom htrm hvregsm hregsm
    rcases hregsm with ⟨hspm, hx29m, hx19m, hx20m, hx24m, hx21m, hx22m, hx25m, hx26m⟩
    refine SepWPp.weaken_pre ?_ (hnext sm
      ⟨hpcm, hrunm, htrm, hvregsm, hclm, hrom, hspm, halign,
       hx29m, hx19m, hx20m, hx24m, hx21m, hx22m, hx25m, hx26m, hcOk, hlen, hfit_rem⟩)
    unfold ChainLoopBudgetSpatial prostChainGAtCap
    have hc_succ : chainGAfter x.c (k + 1) = { ck with priv := b } := by
      rw [chainGAfter_succ hk, hfl_eq]; rfl
    rw [hst_succ, hc_succ, ← henc, ← curPtr_succ x.ptr hk,
      sliceCursorAfter_eq_preBytes x.slot x.ptr x.c x.tail (k + 1),
      ← pointsToBytes_preBytes_succ x.ptr hk]
    dsimp only [ck, capMk, F2, ckRest, rest]
    exact Entails.of_eq (by cb_sep_eq)

private def InnerLoopRegs (sp0 bufRef a : BitVec 64) (outerTailLen afterCkLen : Nat)
    (s : State) : Prop :=
  s.sp = sp0 - 256#64 ∧
    s.readReg64 .x29 = sp0 - 96#64 ∧
    s.readReg64 .x19 = bufRef ∧
    s.readReg64 .x20 = a ∧
    s.readReg64 .x21 = 98#64 ∧
    s.readReg64 .x22 = 97#64 ∧
    s.readReg64 .x23 = BitVec.ofNat 64 afterCkLen ∧
    s.readReg64 .x24 = BitVec.ofNat 64 outerTailLen ∧
    s.readReg64 .x25 = sp0 - 248#64 ∧
    s.readReg64 .x26 = 1#64

private theorem InnerLoopRegs.of_calleeSaved {sp0 bufRef a : BitVec 64}
    {outerTailLen afterCkLen : Nat} {s1 s2 : State}
    (h1 : InnerLoopRegs sp0 bufRef a outerTailLen afterCkLen s1)
    (hsp2 : s2.sp = sp0 - 256#64) (hcs : CalleeSavedPreserved s1 s2) :
    InnerLoopRegs sp0 bufRef a outerTailLen afterCkLen s2 := by
  rcases hcs with ⟨c19, c20, c21, c22, c23, c24, c25, c26, _, _, c29, _⟩
  rcases h1 with ⟨_, h29, h19, h20, h21, h22, h23, h24, h25, h26⟩
  exact ⟨hsp2, c29.trans h29, c19.trans h19, c20.trans h20, c21.trans h21,
    c22.trans h22, c23.trans h23, c24.trans h24, c25.trans h25, c26.trans h26⟩

set_option maxHeartbeats 800000 in
private theorem step_chainTag3_seg3a_budget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (a bufRef slot ptr sp0 : BitVec 64)
    (ck_body afterCk : List (BitVec 8)) (outerTailLen : Nat) (st : M.σ)
    (hck_lt : ck_body.length < 128) (houter_le : outerTailLen ≤ afterCk.length)
    (hlen_lt : 2 + (ck_body.length + afterCk.length) < 2 ^ 62)
    {ret : BitVec 64} {s0 s : State} {F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_11).base + 0x120#64) (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hro : LibsignalRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : LoopRegs sp0 bufRef a outerTailLen s)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_11).base + 0x4c8#64 → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → LibsignalRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace → calleeSavedVRegs sm = calleeSavedVRegs s0 →
      InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length sm →
      SepWPp (lsProg_11 H) ret sm
        (((bufRef ↦₆₄ slot) ∗
          vecU8FreshCap A.repAlloc (a + 0x48#64) [] ∗
          ((a + 0x60#64) ↦₃₂ 0#32) ∗
          memRegion (a + 0x64#64) 4 ∗
          (ptr ↦ₛ [0x1a#8, BitVec.ofNat 8 ck_body.length]) ∗
          sliceCursorAt slot (ptr + 2#64) (ck_body ++ afterCk) ∗
          A.pool lim st sm ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F) Q NoPanicPost) :
    SepWPp (lsProg_11 H) ret s
      (((bufRef ↦₆₄ slot) ∗
        ((a + 0x48#64) ↦₆₄ noneCap) ∗
        memRegion (a + 0x50#64) 24 ∗
        sliceCursorAt slot ptr (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)) ∗
        A.pool lim st s ∗
        stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F) Q NoPanicPost := by
  rcases hregs with ⟨hsp, hx29, hx19, hx20, hx24, hx21, hx22, hx25, hx26⟩
  have hlen_gt : outerTailLen < (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)).length := by
    simp only [List.length_cons, List.length_append]; omega
  have hlen_cons_lt : (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)).length < 2 ^ 62 := by
    simp only [List.length_cons, List.length_append]; omega
  have hule_ls := ule_ofNat_of_gt_false_seedChain62 hlen_gt hlen_cons_lt
  have hult_ls := ult_ofNat_of_gt_true_seedChain62 hlen_gt hlen_cons_lt
  have hsub1 := len_cons_sub_one_seedChain 0x1a#8 (BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk))
  have hrem1_lt : (BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)).length < 2 ^ 62 := by
    simp only [List.length_cons, List.length_append]; omega
  have hcbz2 := cbz_len_cons_false_seedChain62 (b0 := BitVec.ofNat 8 ck_body.length)
    (bs1 := ck_body ++ afterCk) hrem1_lt
  have hse0 := signExtend64_ofNat8_lt128_seedChain hck_lt
  have hlsr56 := ofNat64_lsr56_eq_zero_seedChain hck_lt
  have hsub2 := len_cons_sub_one_seedChain (BitVec.ofNat 8 ck_body.length) (ck_body ++ afterCk)
  have hlen_ck_append : (ck_body ++ afterCk).length = ck_body.length + afterCk.length := List.length_append
  have hule_ck_sub := ule_ofNat_add_right_true_seedChain62 (m := ck_body.length) (k := afterCk.length) (by omega)
  have hsub_ck_tail := bv_ofNat_add_sub_left_seedChain ck_body.length afterCk.length
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp0 - 96#64 := hx29
  have h19 : s.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h20 : s.readReg64 (Reg.gpr 20#5) = a := hx20
  have h21 : s.readReg64 (Reg.gpr 21#5) = 98#64 := hx21
  have h22 : s.readReg64 (Reg.gpr 22#5) = 97#64 := hx22
  have h24 : s.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 outerTailLen := hx24
  have h25 : s.readReg64 (Reg.gpr 25#5) = sp0 - 248#64 := hx25
  have h26 : s.readReg64 (Reg.gpr 26#5) = 1#64 := hx26
  rw [memRegion24_split_ck_seedChain a]
  unfold sliceCursorAt noneCap
  rw [pointsToBytes_cons, pointsToBytes_cons]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun w50 =>
    SepWPp.exists_elim fun w58 =>
    SepWPp.exists_elim fun w60 => ?_
  apply sepWPp_seq_lsclro_vm hcl hro (mid := (blkPl_11).base + 0x4c8#64)
  by_vm_steps_withSvc (
    iterate 44 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm1 hcl1 hro1
  rw [← A.pool_transport lim st s _ hvm1]
  have hvec := emptyCells_entails_vecU8FreshCap A.repAlloc (a + 0x48#64) 1#64 (by decide)
  have h48_8 : (a + 0x48#64) + 8#64 = a + 0x50#64 := by rw [BitVec.add_assoc]; rfl
  have h48_16 : (a + 0x48#64) + 16#64 = a + 0x58#64 := by rw [BitVec.add_assoc]; rfl
  have hptr2 : ptr + 1#64 + 1#64 = ptr + 2#64 := by rw [BitVec.add_assoc]; rfl
  rw [h48_8, h48_16] at hvec
  refine SepWPp.weaken_pre ?_ (hnext _
    (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
    hcl1 hro1 (by simp only [htr, arm64_norm]) (by simp only [hvregs, arm64_norm])
    ⟨by simp only [hsp, arm64_norm], by simp only [h29, arm64_norm],
     by simp only [h19, arm64_norm], by simp only [h20, arm64_norm],
     by simp only [h21, arm64_norm], by simp only [h22, arm64_norm],
     by simp only [arm64_norm], by simp only [h24, arm64_norm],
     by simp only [h25, arm64_norm], by simp only [h26, arm64_norm]⟩)
  unfold sliceCursorAt
  rw [← hlen_ck_append, ← ck_hdr_pointsTo_combine_seedChain ptr ck_body.length, hptr2]
  refine Entails.trans
    (Entails.of_eq (?_ : _ =
      (((a + 0x48#64) ↦₆₄ 0#64) ∗ ((a + 0x50#64) ↦₆₄ 1#64) ∗ ((a + 0x58#64) ↦₆₄ 0#64)) ∗
      ((bufRef ↦₆₄ slot) ∗
        ((a + 0x60#64) ↦₃₂ 0#32) ∗ memRegion (a + 0x64#64) 4 ∗
        ((ptr ↦₈ 0x1a#8) ∗ ((ptr + 1#64) ↦₈ BitVec.ofNat 8 ck_body.length)) ∗
        ((slot ↦₆₄ (ptr + 2#64)) ∗
          ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (ck_body ++ afterCk).length) ∗
          ((ptr + 2#64) ↦ₛ (ck_body ++ afterCk))) ∗
        A.pool lim st (vmDst hvm1) ∗
        stackAt (sp0 - 256#64) chainMergeSubStackX ∗ F)))
    (Entails.trans (sepConj_mono_left hvec) (Entails.of_eq (by cb_sep_eq)))
  · cb_sep_eq

set_option maxHeartbeats 800000 in
private theorem step_chainTag3_seg3b_budget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (a bufRef slot ptr sp0 : BitVec 64)
    (i : BitVec 32) (rest afterCk : List (BitVec 8)) (outerTailLen : Nat) (st : M.σ)
    (hlen_lt : (pbVarint 1 i.toNat ++ rest ++ afterCk).length < 2 ^ 62)
    {ret : BitVec 64} {s0 s : State} {F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_11).base + 0x4c8#64) (hrun : s.status = .Running)
    (halign : sp0 &&& 15#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hro : LibsignalRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_11).base + 0x4c8#64 → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → LibsignalRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace → calleeSavedVRegs sm = calleeSavedVRegs s0 →
      InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length sm →
      SepWPp (lsProg_11 H) ret sm
        (((bufRef ↦₆₄ slot) ∗
          ((a + 0x60#64) ↦₃₂ i) ∗
          (ptr ↦ₛ pbVarint 1 i.toNat) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbVarint 1 i.toNat).length) (rest ++ afterCk) ∗
          A.pool lim st sm ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F) Q NoPanicPost) :
    SepWPp (lsProg_11 H) ret s
      (((bufRef ↦₆₄ slot) ∗
        ((a + 0x60#64) ↦₃₂ 0#32) ∗
        sliceCursorAt slot ptr (pbVarint 1 i.toNat ++ (rest ++ afterCk)) ∗
        A.pool lim st s ∗
        stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F) Q NoPanicPost := by
  by_cases hi0 : i = 0#32
  · subst hi0
    have hpb0 : pbVarint 1 (0#32).toNat = [] := rfl
    rw [hpb0] at hnext ⊢
    simp only [List.nil_append, List.length_nil, BitVec.ofNat_eq_ofNat,
      BitVec.add_zero, pointsToBytes_nil] at hnext ⊢
    exact SepWPp.weaken_pre (Entails.of_eq (by cb_sep_eq))
      (hnext s hpc hrun hcl hro htr hvregs hregs)
  · rcases hregs with ⟨hsp, hx29, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26⟩
    have hi_pos : i.toNat ≠ 0 := by
      intro h; apply hi0; apply BitVec.eq_of_toNat_eq; simpa using h
    have hpb : pbVarint 1 i.toNat = 0x08#8 :: pbVarintBody 5 i.toNat := by
      unfold pbVarint; simp [hi_pos]; rfl
    let rem1 : List (BitVec 8) := pbVarintBody 5 i.toNat ++ (rest ++ afterCk)
    have hcons_eq : pbVarint 1 i.toNat ++ (rest ++ afterCk) = 0x08#8 :: rem1 := by
      rw [hpb]; simp [rem1, List.cons_append]
    have hlen_gt : afterCk.length < (0x08#8 :: rem1).length := by
      simp only [rem1, List.length_cons, List.length_append]; omega
    have hlen_cons_lt : (0x08#8 :: rem1).length < 2 ^ 62 := by
      rw [← hcons_eq]; simpa [List.append_assoc] using hlen_lt
    have hule_ls := ule_ofNat_of_gt_false_seedChain62 hlen_gt hlen_cons_lt
    have hult_ls := ult_ofNat_of_gt_true_seedChain62 hlen_gt hlen_cons_lt
    have hsub1 := len_cons_sub_one_seedChain 0x08#8 rem1
    have h29 : s.readReg64 (Reg.gpr 29#5) = sp0 - 96#64 := hx29
    have h19 : s.readReg64 (Reg.gpr 19#5) = bufRef := hx19
    have h20 : s.readReg64 (Reg.gpr 20#5) = a := hx20
    have h21 : s.readReg64 (Reg.gpr 21#5) = 98#64 := hx21
    have h22 : s.readReg64 (Reg.gpr 22#5) = 97#64 := hx22
    have h23 : s.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 afterCk.length := hx23
    have h24 : s.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 outerTailLen := hx24
    have h25 : s.readReg64 (Reg.gpr 25#5) = sp0 - 248#64 := hx25
    have h26 : s.readReg64 (Reg.gpr 26#5) = 1#64 := hx26
    refine (?_ :
      (∀ s1 : State,
        s1.pc = lsmpl.base 8 → s1.status = .Running →
        LibsignalCodeLoaded lsmpl s1.mem → LibsignalRoLoaded lsmpl s1.mem →
        s1.trace = s0.trace → calleeSavedVRegs s1 = calleeSavedVRegs s0 →
        s1.readReg64 .lr = (blkPl_11).base + 0x588#64 →
        (s1.readReg64 .x0).setWidth 8 = 0#8 →
        s1.readReg64 .x1 = a + 0x60#64 → s1.readReg64 .x2 = bufRef →
        InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s1 →
        SepWPp (lsProg_11 H) ret s1
          ((((a + 0x60#64) ↦₃₂ 0#32) ∗
            (bufRef ↦₆₄ slot) ∗
            sliceCursorAt slot (ptr + 1#64) rem1 ∗
            A.pool lim st s1 ∗
            stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ ((ptr ↦₈ 0x08#8) ∗ F)) Q NoPanicPost) → _) ?_
    · intro hnext1
      rw [hcons_eq]
      unfold sliceCursorAt
      rw [pointsToBytes_cons]
      apply sepWPp_seq_lsclro_vm hcl hro (mid := lsmpl.base 8)
      by_vm_steps_withSvc (
        iterate 24 wp_step
        refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
          ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
      intro hvm1 hcl1 hro1
      rw [← A.pool_transport lim st s _ hvm1]
      refine SepWPp.weaken_pre ?_ (hnext1 _
        (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        hcl1 hro1 (by simp only [htr, arm64_norm]) (by simp only [hvregs, arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        ⟨by simp only [hsp, arm64_norm], by simp only [h29, arm64_norm],
         by simp only [h19, arm64_norm], by simp only [h20, arm64_norm],
         by simp only [h21, arm64_norm], by simp only [h22, arm64_norm],
         by simp only [h23, arm64_norm], by simp only [h24, arm64_norm],
         by simp only [h25, arm64_norm], by simp only [h26, arm64_norm]⟩)
      unfold sliceCursorAt
      exact Entails.of_eq (by cb_sep_eq)
    · intro s1 hpc1 hrun1 hcl1 hro1 htr1 hvregs1 hlr1 hx0_1 hx1_1 hx2_1 hregs1
      have hrem1_lt : (pbVarintBody 5 i.toNat ++ (rest ++ afterCk)).length < 2 ^ 62 := by
        simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
      refine step_chainMerge_int32Merge_budget (a + 0x60#64) bufRef slot (ptr + 1#64) sp0
        ((blkPl_11).base + 0x588#64) 0#32 i (rest ++ afterCk) st hrem1_lt
        hpc1 hrun1 hregs1.1 halign hcl1 hro1 htr1 hlr1 hx0_1 hx1_1 hx2_1 ?_
      intro s2 hpc2 hrun2 hsp2 hcl2 hro2 htr2 hcs2 hx0_2
      have hregs2 := hregs1.of_calleeSaved hsp2 hcs2
      have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := by
        rcases hcs2 with ⟨_, _, _, _, _, _, _, _, _, _, _, hcv⟩; exact hcv.trans hvregs1
      rcases hregs2 with ⟨hsp2, hx29_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2⟩
      have h0_2 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
      apply sepWPp_seq_lsclro_vm hcl2 hro2 (mid := (blkPl_11).base + 0x4c8#64)
      by_vm_steps_withSvc (
        iterate 2 wp_step
        refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
          ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
      intro hvm3 hcl3 hro3
      rw [← A.pool_transport lim st s2 _ hvm3]
      refine SepWPp.weaken_pre ?_ (hnext _
        (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        hcl3 hro3 (by simp only [htr2, arm64_norm]) (by simp only [hvregs2, arm64_norm])
        ⟨by simp only [hsp2, arm64_norm], by simp only [hx29_2, arm64_norm],
         by simp only [hx19_2, arm64_norm], by simp only [hx20_2, arm64_norm],
         by simp only [hx21_2, arm64_norm], by simp only [hx22_2, arm64_norm],
         by simp only [hx23_2, arm64_norm], by simp only [hx24_2, arm64_norm],
         by simp only [hx25_2, arm64_norm], by simp only [hx26_2, arm64_norm]⟩)
      rw [pbVarint1_ptr_advance_seedChain ptr i.toNat hi_pos,
        ← pbVarint1_pointsTo_combine_seedChain ptr i.toNat hi_pos]
      exact Entails.of_eq (by cb_sep_eq)

set_option maxHeartbeats 800000 in
private theorem step_chainTag3_seg3c_budget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H)
    (a bufRef slot ptr sp0 : BitVec 64)
    (key afterCk : List (BitVec 8)) (outerTailLen : Nat) (st : M.σ)
    (hkey_lt : key.length < 128)
    (hlen_lt : (pbBytes 2 key ++ afterCk).length < 2 ^ 62)
    (hfit : FitsEvents M lim st (bytesMergeEvents 0 key.length))
    {ret : BitVec 64} {s0 s : State} {F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_11).base + 0x4c8#64) (hrun : s.status = .Running)
    (halign : sp0 &&& 15#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hro : LibsignalRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_11).base + 0x4c8#64 → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → LibsignalRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace → calleeSavedVRegs sm = calleeSavedVRegs s0 →
      InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length sm →
      SepWPp (lsProg_11 H) ret sm
        (((bufRef ↦₆₄ slot) ∗
          vecU8FreshCap A.repAlloc (a + 0x48#64) key ∗
          (ptr ↦ₛ pbBytes 2 key) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbBytes 2 key).length) afterCk ∗
          A.pool lim (M.stepEvents (bytesMergeEvents 0 key.length) st) sm ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F) Q NoPanicPost) :
    SepWPp (lsProg_11 H) ret s
      (((bufRef ↦₆₄ slot) ∗
        vecU8FreshCap A.repAlloc (a + 0x48#64) [] ∗
        sliceCursorAt slot ptr (pbBytes 2 key ++ afterCk) ∗
        A.pool lim st s ∗
        stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F) Q NoPanicPost := by
  rcases hregs with ⟨hsp, hx29, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26⟩
  have hpb : pbBytes 2 key = 0x12#8 :: BitVec.ofNat 8 key.length :: key :=
    pbBytes_lt128_eq_seedChain 2 (by decide) key hkey_lt
  let rem1 : List (BitVec 8) := [BitVec.ofNat 8 key.length] ++ key ++ afterCk
  have hcons_eq : pbBytes 2 key ++ afterCk = 0x12#8 :: rem1 := by
    rw [hpb]; simp [rem1, List.cons_append, List.append_assoc]
  have hlen_gt : afterCk.length < (0x12#8 :: rem1).length := by
    simp only [rem1, List.length_cons, List.length_append]; omega
  have hlen_cons_lt : (0x12#8 :: rem1).length < 2 ^ 62 := by rw [← hcons_eq]; exact hlen_lt
  have hule_ls := ule_ofNat_of_gt_false_seedChain62 hlen_gt hlen_cons_lt
  have hult_ls := ult_ofNat_of_gt_true_seedChain62 hlen_gt hlen_cons_lt
  have hsub1 := len_cons_sub_one_seedChain 0x12#8 rem1
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp0 - 96#64 := hx29
  have h19 : s.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h20 : s.readReg64 (Reg.gpr 20#5) = a := hx20
  have h21 : s.readReg64 (Reg.gpr 21#5) = 98#64 := hx21
  have h22 : s.readReg64 (Reg.gpr 22#5) = 97#64 := hx22
  have h23 : s.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 afterCk.length := hx23
  have h24 : s.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 outerTailLen := hx24
  have h25 : s.readReg64 (Reg.gpr 25#5) = sp0 - 248#64 := hx25
  have h26 : s.readReg64 (Reg.gpr 26#5) = 1#64 := hx26
  refine (?_ :
    (∀ s1 : State,
      s1.pc = lsmpl.base 7 → s1.status = .Running →
      LibsignalCodeLoaded lsmpl s1.mem → LibsignalRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace → calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      s1.readReg64 .lr = (blkPl_11).base + 0x570#64 →
      (s1.readReg64 .x0).setWidth 8 = 2#8 →
      s1.readReg64 .x1 = a + 0x48#64 → s1.readReg64 .x2 = bufRef →
      InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s1 →
      SepWPp (lsProg_11 H) ret s1
        ((vecU8FreshCap A.repAlloc (a + 0x48#64) [] ∗
          (bufRef ↦₆₄ slot) ∗
          sliceCursorAt slot (ptr + 1#64) rem1 ∗
          A.pool lim st s1 ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ ((ptr ↦₈ 0x12#8) ∗ F)) Q NoPanicPost) → _) ?_
  · intro hnext1
    rw [hcons_eq]
    unfold sliceCursorAt
    rw [pointsToBytes_cons]
    apply sepWPp_seq_lsclro_vm hcl hro (mid := lsmpl.base 7)
    by_vm_steps_withSvc (
      iterate 26 wp_step
      refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
    intro hvm1 hcl1 hro1
    rw [← A.pool_transport lim st s _ hvm1]
    refine SepWPp.weaken_pre ?_ (hnext1 _
      (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      hcl1 hro1 (by simp only [htr, arm64_norm]) (by simp only [hvregs, arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      ⟨by simp only [hsp, arm64_norm], by simp only [h29, arm64_norm],
       by simp only [h19, arm64_norm], by simp only [h20, arm64_norm],
       by simp only [h21, arm64_norm], by simp only [h22, arm64_norm],
       by simp only [h23, arm64_norm], by simp only [h24, arm64_norm],
       by simp only [h25, arm64_norm], by simp only [h26, arm64_norm]⟩)
    unfold sliceCursorAt
    exact Entails.of_eq (by cb_sep_eq)
  · intro s1 hpc1 hrun1 hcl1 hro1 htr1 hvregs1 hlr1 hx0_1 hx1_1 hx2_1 hregs1
    have hrem1_lt : ([BitVec.ofNat 8 key.length] ++ key ++ afterCk).length < 2 ^ 62 := by
      simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
    refine step_chainMerge_bytesMergeFresh_budget hA (a + 0x48#64) bufRef slot (ptr + 1#64) sp0
      ((blkPl_11).base + 0x570#64) key afterCk st hkey_lt hrem1_lt hfit
      hpc1 hrun1 hregs1.1 halign hcl1 hro1 htr1 hlr1 hx0_1 hx1_1 hx2_1 ?_
    intro s2 hpc2 hrun2 hsp2 hcl2 hro2 htr2 hcs2 hx0_2
    have hregs2 := hregs1.of_calleeSaved hsp2 hcs2
    have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := by
      rcases hcs2 with ⟨_, _, _, _, _, _, _, _, _, _, _, hcv⟩; exact hcv.trans hvregs1
    rcases hregs2 with ⟨hsp2, hx29_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2⟩
    have h0_2 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    apply sepWPp_seq_lsclro_vm hcl2 hro2 (mid := (blkPl_11).base + 0x4c8#64)
    by_vm_steps_withSvc (
      iterate 2 wp_step
      refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
    intro hvm3 hcl3 hro3
    rw [← A.pool_transport lim _ s2 _ hvm3]
    refine SepWPp.weaken_pre ?_ (hnext _
      (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
      hcl3 hro3 (by simp only [htr2, arm64_norm]) (by simp only [hvregs2, arm64_norm])
      ⟨by simp only [hsp2, arm64_norm], by simp only [hx29_2, arm64_norm],
       by simp only [hx19_2, arm64_norm], by simp only [hx20_2, arm64_norm],
       by simp only [hx21_2, arm64_norm], by simp only [hx22_2, arm64_norm],
       by simp only [hx23_2, arm64_norm], by simp only [hx24_2, arm64_norm],
       by simp only [hx25_2, arm64_norm], by simp only [hx26_2, arm64_norm]⟩)
    rw [pbBytes_ptr_advance_seedChain 2 (by decide) ptr key hkey_lt,
      ← pbBytes_pointsTo_combine_seedChain 2 (by decide) ptr key hkey_lt]
    exact Entails.of_eq (by cb_sep_eq)

set_option maxHeartbeats 800000 in
private theorem step_chainTag3_seg3d_budget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (a bufRef slot ptr sp0 : BitVec 64)
    (afterCk : List (BitVec 8)) (outerTailLen : Nat) (st : M.σ)
    {ret : BitVec 64} {s0 s : State} {F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_11).base + 0x4c8#64) (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hro : LibsignalRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_11).base + 0x120#64 → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → LibsignalRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace → calleeSavedVRegs sm = calleeSavedVRegs s0 →
      LoopRegs sp0 bufRef a outerTailLen sm →
      SepWPp (lsProg_11 H) ret sm
        (((bufRef ↦₆₄ slot) ∗
          sliceCursorAt slot ptr afterCk ∗
          A.pool lim st sm ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F) Q NoPanicPost) :
    SepWPp (lsProg_11 H) ret s
      (((bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr afterCk ∗
        A.pool lim st s ∗
        stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F) Q NoPanicPost := by
  rcases hregs with ⟨hsp, hx29, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26⟩
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp0 - 96#64 := hx29
  have h19 : s.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h20 : s.readReg64 (Reg.gpr 20#5) = a := hx20
  have h21 : s.readReg64 (Reg.gpr 21#5) = 98#64 := hx21
  have h22 : s.readReg64 (Reg.gpr 22#5) = 97#64 := hx22
  have h23 : s.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 afterCk.length := hx23
  have h24 : s.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 outerTailLen := hx24
  have h25 : s.readReg64 (Reg.gpr 25#5) = sp0 - 248#64 := hx25
  have h26 : s.readReg64 (Reg.gpr 26#5) = 1#64 := hx26
  unfold sliceCursorAt
  apply sepWPp_seq_lsclro_vm hcl hro (mid := (blkPl_11).base + 0x120#64)
  by_vm_steps_withSvc (
    iterate 7 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm1 hcl1 hro1
  rw [← A.pool_transport lim st s _ hvm1]
  refine SepWPp.weaken_pre ?_ (hnext _
    (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
    hcl1 hro1 (by simp only [htr, arm64_norm]) (by simp only [hvregs, arm64_norm])
    ⟨by simp only [hsp, arm64_norm], by simp only [h29, arm64_norm],
     by simp only [h19, arm64_norm], by simp only [h20, arm64_norm],
     by simp only [h24, arm64_norm], by simp only [h21, arm64_norm],
     by simp only [h22, arm64_norm], by simp only [h25, arm64_norm],
     by simp only [h26, arm64_norm]⟩)
  unfold sliceCursorAt
  exact Entails.of_eq (by cb_sep_eq)

private theorem step_chainTag3_budget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H)
    (x : ChainMergeGenGhost) (st₀ : M.σ) {s0 s : State} {k : Nat}
    {Q : State → SepProp → Prop}
    (hk : k < x.c.fields.length)
    (htag : (x.c.fields[k]'hk).tag = 3)
    (hinv : ChainLoopBudgetInv M lim x st₀ s0 k s)
    (hnext : ∀ sm : State,
      ChainLoopBudgetInv M lim x st₀ s0 (k + 1) sm →
      SepWPp (lsProg_11 H) (s0.readReg64 .lr) sm
        (ChainLoopBudgetSpatial M A lim x st₀ s0 (k + 1) sm) Q NoPanicPost) :
    SepWPp (lsProg_11 H) (s0.readReg64 .lr) s
      (ChainLoopBudgetSpatial M A lim x st₀ s0 k s) Q NoPanicPost := by
  rcases hinv with ⟨hpc, hrun, htr, hvregs, hcl, hro, hsp, halign,
    hx29, hx19, hx20, hx24, hx21, hx22, hx25, hx26, hcOk, hlen_lt, hfit⟩
  have hregs0 : LoopRegs s0.sp x.bufRef x.a x.tail.length s :=
    ⟨hsp, hx29, hx19, hx20, hx24, hx21, hx22, hx25, hx26⟩
  obtain ⟨⟨i, key, hck_some, hfl_eq⟩, hck_none⟩ := chainField_tag_three_info x.c k hk htag
  obtain ⟨hfit_step, hfit_rem⟩ := chainLoop_fits_split hk hfit
  have hkey_len : key.length = 32 := hcOk.2.2.1 (i, key) hck_some
  have hkey_lt : key.length < 128 := by omega
  have hck_bounds := ckEnc_length_bounds_seedChain i hkey_len
  let b3b : List (BitVec 8) := pbVarint 1 i.toNat
  let b3c : List (BitVec 8) := pbBytes 2 key
  let ck_body : List (BitVec 8) := b3b ++ b3c
  have hck_lt : ck_body.length < 128 := by dsimp [ck_body, b3b, b3c]; omega
  let b3a : List (BitVec 8) := [0x1a#8, BitVec.ofNat 8 ck_body.length]
  let pfx : List (BitVec 8) := pfx_k x.c k
  let afterCk : List (BitVec 8) := rem_k x.c (k + 1) x.tail
  have hfl_enc : (x.c.fields[k]'hk).enc = b3a ++ (b3b ++ b3c) := by
    rw [hfl_eq]; exact chainField_ck_enc_eq i hkey_len
  have hrem_k : rem_k x.c k x.tail =
      0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk) := by
    rw [rem_k_eq_cons x.c k x.tail hk, hfl_enc]; dsimp [b3a, ck_body]
  have hpay_eq : x.c.payload ++ x.tail = pfx ++ rem_k x.c k x.tail :=
    payload_append_eq_pfx_rem x.c k x.tail
  have houter_le : x.tail.length ≤ afterCk.length := by
    dsimp [afterCk, rem_k]; simp only [List.length_append]; omega
  have hlen_lt3a : 2 + (ck_body.length + afterCk.length) < 2 ^ 62 := by
    have h1 := hlen_lt
    rw [hpay_eq, hrem_k] at h1
    simp only [List.length_append, List.length_cons] at h1; omega
  have hlen_lt3b : (b3b ++ b3c ++ afterCk).length < 2 ^ 62 := by
    have h1 : (b3b ++ b3c ++ afterCk).length = ck_body.length + afterCk.length :=
      List.length_append
    omega
  have hlen_lt3c : (b3c ++ afterCk).length < 2 ^ 62 := by
    simp only [List.length_append] at hlen_lt3b ⊢; omega
  let c0 : ChainG := chainGAfter x.c k
  let capMk := vecCap4Of c0.keys.length
  let st_k := M.stepEvents (chainDoneEvents x.c k) st₀
  have hfit_key : FitsEvents M lim st_k (bytesMergeEvents 0 key.length) := by
    simpa [st_k, hfl_eq, chainFieldStepEvents] using hfit_step
  have hst_succ :
      M.stepEvents (bytesMergeEvents 0 key.length) st_k =
        M.stepEvents (chainDoneEvents x.c (k + 1)) st₀ := by
    rw [chainDoneEvents_succ_of_lt hk, AllocCostModel.stepEvents_append, hfl_eq]
    rfl
  let ptr3a : BitVec 64 := x.ptr + BitVec.ofNat 64 pfx.length
  let ptr3b : BitVec 64 := ptr3a + 2#64
  let ptr3c : BitVec 64 := ptr3b + BitVec.ofNat 64 b3b.length
  let ptrEnd : BitVec 64 := ptr3c + BitVec.ofNat 64 b3c.length
  have hcur_init :
      sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail)
        (((x.c.fields.drop k).flatMap ChainField.enc) ++ x.tail) =
      (x.ptr ↦ₛ pfx) ∗
        sliceCursorAt x.slot ptr3a
          (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)) := by
    change sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail) (rem_k x.c k x.tail) = _
    rw [hpay_eq, sliceCursorAfter_append_eq_seedChain x.slot x.ptr pfx (rem_k x.c k x.tail), hrem_k]
  let ckHead : SepProp :=
    vecU8FreshCap A.repAlloc x.a c0.srk ∗
      vecU8FreshCap A.repAlloc (x.a + 0x18#64) c0.priv ∗
      (∃∗ ptrMk : BitVec 64,
        vecAt A.repAlloc 104 8 (fun mk p => prostMsgKeyAtCap A.repAlloc mk p)
          (x.a + 0x30#64) (BitVec.ofNat 64 capMk) ptrMk c0.keys)
  refine SepWPp.weaken_pre
    (P' := (((x.bufRef ↦₆₄ x.slot) ∗
      ((x.a + 0x48#64) ↦₆₄ noneCap) ∗
      memRegion (x.a + 0x50#64) 24 ∗
      sliceCursorAt x.slot ptr3a
        (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)) ∗
      A.pool lim st_k s ∗
      stackAt (s0.sp - 256#64) chainMergeSubStackX) ∗
      (ckHead ∗ (x.ptr ↦ₛ pfx) ∗ chainMergeSavedRegs s0.sp s0)))
    (by
      unfold ChainLoopBudgetSpatial prostChainGAtCap
      dsimp only [c0, capMk, st_k, ckHead]
      rw [hck_none, hcur_init]
      exact Entails.of_eq (by cb_sep_eq))
    (step_chainTag3_seg3a_budget x.a x.bufRef x.slot ptr3a s0.sp
      ck_body afterCk x.tail.length st_k hck_lt houter_le hlen_lt3a
      hpc hrun hcl hro htr hvregs hregs0 ?_)
  intro s4 hpc4 hrun4 hcl4 hro4 htr4 hvregs4 hregs4
  refine SepWPp.weaken_pre
    (P' := (((x.bufRef ↦₆₄ x.slot) ∗
      ((x.a + 0x60#64) ↦₃₂ 0#32) ∗
      sliceCursorAt x.slot ptr3b (b3b ++ (b3c ++ afterCk)) ∗
      A.pool lim st_k s4 ∗
      stackAt (s0.sp - 256#64) chainMergeSubStackX) ∗
      ((ptr3a ↦ₛ b3a) ∗ vecU8FreshCap A.repAlloc (x.a + 0x48#64) [] ∗
        memRegion (x.a + 0x64#64) 4 ∗ ckHead ∗ (x.ptr ↦ₛ pfx) ∗
        chainMergeSavedRegs s0.sp s0)))
    (by
      have hck_eq : ck_body ++ afterCk = b3b ++ (b3c ++ afterCk) := by
        simp [ck_body, b3b, b3c, List.append_assoc]
      dsimp only [ptr3b, b3a]; rw [hck_eq]; exact Entails.of_eq (by cb_sep_eq))
    (step_chainTag3_seg3b_budget x.a x.bufRef x.slot ptr3b s0.sp
      i b3c afterCk x.tail.length st_k hlen_lt3b
      hpc4 hrun4 halign hcl4 hro4 htr4 hvregs4 hregs4 ?_)
  intro s5 hpc5 hrun5 hcl5 hro5 htr5 hvregs5 hregs5
  refine SepWPp.weaken_pre
    (P' := (((x.bufRef ↦₆₄ x.slot) ∗
      vecU8FreshCap A.repAlloc (x.a + 0x48#64) [] ∗
      sliceCursorAt x.slot ptr3c (b3c ++ afterCk) ∗
      A.pool lim st_k s5 ∗
      stackAt (s0.sp - 256#64) chainMergeSubStackX) ∗
      ((ptr3a ↦ₛ b3a) ∗ (ptr3b ↦ₛ b3b) ∗ ((x.a + 0x60#64) ↦₃₂ i) ∗
        memRegion (x.a + 0x64#64) 4 ∗ ckHead ∗ (x.ptr ↦ₛ pfx) ∗
        chainMergeSavedRegs s0.sp s0)))
    (by dsimp only [ptr3c, b3b]; exact Entails.of_eq (by cb_sep_eq))
    (step_chainTag3_seg3c_budget hA x.a x.bufRef x.slot ptr3c s0.sp
      key afterCk x.tail.length st_k hkey_lt hlen_lt3c hfit_key
      hpc5 hrun5 halign hcl5 hro5 htr5 hvregs5 hregs5 ?_)
  intro s6 hpc6 hrun6 hcl6 hro6 htr6 hvregs6 hregs6
  refine SepWPp.weaken_pre
    (P' := (((x.bufRef ↦₆₄ x.slot) ∗
      sliceCursorAt x.slot ptrEnd afterCk ∗
      A.pool lim (M.stepEvents (bytesMergeEvents 0 key.length) st_k) s6 ∗
      stackAt (s0.sp - 256#64) chainMergeSubStackX) ∗
      ((ptr3a ↦ₛ b3a) ∗ (ptr3b ↦ₛ b3b) ∗ (ptr3c ↦ₛ b3c) ∗
        vecU8FreshCap A.repAlloc (x.a + 0x48#64) key ∗
        ((x.a + 0x60#64) ↦₃₂ i) ∗ memRegion (x.a + 0x64#64) 4 ∗
        ckHead ∗ (x.ptr ↦ₛ pfx) ∗ chainMergeSavedRegs s0.sp s0)))
    (by dsimp only [ptrEnd, b3c]; exact Entails.of_eq (by cb_sep_eq))
    (step_chainTag3_seg3d_budget x.a x.bufRef x.slot ptrEnd s0.sp
      afterCk x.tail.length (M.stepEvents (bytesMergeEvents 0 key.length) st_k)
      hpc6 hrun6 hcl6 hro6 htr6 hvregs6 hregs6 ?_)
  intro sf hpcf hrunf hclf hrof htrf hvregsf hregsf
  rcases hregsf with ⟨hspf, hx29f, hx19f, hx20f, hx24f, hx21f, hx22f, hx25f, hx26f⟩
  refine SepWPp.weaken_pre ?_ (hnext sf
    ⟨hpcf, hrunf, htrf, hvregsf, hclf, hrof, hspf, halign,
     hx29f, hx19f, hx20f, hx24f, hx21f, hx22f, hx25f, hx26f, hcOk, hlen_lt, hfit_rem⟩)
  unfold ChainLoopBudgetSpatial prostChainGAtCap
  have hc_succ : chainGAfter x.c (k + 1) = { c0 with ck := some (i, key) } := by
    rw [chainGAfter_succ hk, hfl_eq]; rfl
  have hcur_end := combine_tag3_cursor x.slot x.ptr pfx b3a b3b b3c afterCk rfl
  dsimp only at hcur_end
  have htotal_end : (pfx ++ (b3a ++ (b3b ++ b3c))) ++ afterCk = x.c.payload ++ x.tail := by
    rw [← hfl_enc, ← pfx_k_succ x.c k hk]
    exact (payload_append_eq_pfx_rem x.c (k + 1) x.tail).symm
  rw [htotal_end] at hcur_end
  change _ ⊢
    (vecU8FreshCap A.repAlloc x.a (chainGAfter x.c (k + 1)).srk ∗
      vecU8FreshCap A.repAlloc (x.a + 0x18#64) (chainGAfter x.c (k + 1)).priv ∗
      (∃∗ ptrMk : BitVec 64,
        vecAt A.repAlloc 104 8 (fun mk p => prostMsgKeyAtCap A.repAlloc mk p)
          (x.a + 0x30#64) (BitVec.ofNat 64 (vecCap4Of (chainGAfter x.c (k + 1)).keys.length))
          ptrMk (chainGAfter x.c (k + 1)).keys) ∗
      match (chainGAfter x.c (k + 1)).ck with
      | none => ((x.a + 0x48#64) ↦₆₄ noneCap) ∗ memRegion (x.a + 0x50#64) 24
      | some (i', k') => vecU8FreshCap A.repAlloc (x.a + 0x48#64) k' ∗
          ((x.a + 0x60#64) ↦₃₂ i') ∗ memRegion (x.a + 0x64#64) 4) ∗
    (x.bufRef ↦₆₄ x.slot) ∗
    sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail) afterCk ∗
    A.pool lim (M.stepEvents (chainDoneEvents x.c (k + 1)) st₀) sf ∗
    stackAt (s0.sp - 256#64) chainMergeSubStackX ∗
    chainMergeSavedRegs s0.sp s0
  rw [hst_succ, hc_succ, ← hcur_end]
  dsimp only [c0, capMk, ckHead, ptr3a, ptr3b, ptr3c, ptrEnd]
  exact Entails.of_eq (by cb_sep_eq)


private def Tag4Regs (sp0 bufRef a : BitVec 64) (tailLen restLen : Nat) (s : State) : Prop :=
  s.sp = sp0 - 256#64 ∧
    s.readReg64 .x19 = bufRef ∧
    s.readReg64 .x20 = a ∧
    s.readReg64 .x21 = 98#64 ∧
    s.readReg64 .x22 = 97#64 ∧
    s.readReg64 .x24 = BitVec.ofNat 64 tailLen ∧
    s.readReg64 .x25 = sp0 - 248#64 ∧
    s.readReg64 .x26 = 1#64 ∧
    s.readReg64 .x28 = BitVec.ofNat 64 restLen ∧
    s.readReg64 .x29 = sp0 - 96#64

private theorem Tag4Regs.of_calleeSaved {sp0 bufRef a : BitVec 64} {tailLen restLen : Nat}
    {s1 s2 : State} (h1 : Tag4Regs sp0 bufRef a tailLen restLen s1)
    (hsp2 : s2.sp = sp0 - 256#64) (hcs : CalleeSavedPreserved s1 s2) :
    Tag4Regs sp0 bufRef a tailLen restLen s2 := by
  rcases hcs with ⟨c19, c20, c21, c22, _, c24, c25, c26, _, c28, c29, _⟩
  rcases h1 with ⟨_, h19, h20, h21, h22, h24, h25, h26, h28, h29⟩
  exact ⟨hsp2, c19.trans h19, c20.trans h20, c21.trans h21, c22.trans h22,
    c24.trans h24, c25.trans h25, c26.trans h26, c28.trans h28, c29.trans h29⟩

private theorem vecCap4Of_le_two_mul_max4 (n : Nat) :
    vecCap4Of n ≤ max (2 * n) 4 := by
  induction n with
  | zero => simp [vecCap4Of]
  | succ m ih =>
    rw [vecCap4Of_succ]
    unfold vecCap4Push vecCap4Next
    split_ifs <;> omega

private theorem vecCap4Next_eq_max_of_pow2 {c : Nat} (h : IsPow2Cap4 c) :
    vecCap4Next c = max (2 * c) 4 := by
  unfold vecCap4Next
  rcases isPow2Cap4_zero_or_ge_four h with rfl | hge4
  · simp
  · have hne : c ≠ 0 := by omega
    simp only [hne, ↓reduceIte]; omega

set_option maxHeartbeats 1200000 in
private theorem step_tag4a_budget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (a bufRef slot ptr sp0 : BitVec 64)
    (mk_body rest : List (BitVec 8)) (tailLen : Nat) (st : M.σ)
    (hmk_lt : mk_body.length < 128)
    (htail_le : tailLen ≤ rest.length)
    (hlen_lt : 2 + (mk_body.length + rest.length) < 2 ^ 62)
    {ret : BitVec 64} {s0 s : State} {F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_11).base + 0x120#64) (hrun : s.status = .Running)
    (halign : sp0 &&& 15#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hro : LibsignalRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : LoopRegs sp0 bufRef a tailLen s)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_11).base + 0x300#64 → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → LibsignalRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace → calleeSavedVRegs sm = calleeSavedVRegs s0 →
      Tag4Regs sp0 bufRef a tailLen rest.length sm →
      SepWPp (lsProg_11 H) ret sm
        (((bufRef ↦₆₄ slot) ∗
          vecU8FreshCap A.repAlloc (sp0 - 248#64) [] ∗
          vecU8FreshCap A.repAlloc (sp0 - 224#64) [] ∗
          vecU8FreshCap A.repAlloc (sp0 - 200#64) [] ∗
          vecU8FreshCap A.repAlloc (sp0 - 176#64) [] ∗
          ((sp0 - 152#64) ↦₃₂ 0#32) ∗ memRegion (sp0 - 148#64) 4 ∗
          (ptr ↦ₛ [0x22#8, BitVec.ofNat 8 mk_body.length]) ∗
          sliceCursorAt slot (ptr + 2#64) (mk_body ++ rest) ∗
          A.pool lim st sm ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F) Q NoPanicPost) :
    SepWPp (lsProg_11 H) ret s
      (((bufRef ↦₆₄ slot) ∗
        memRegion (sp0 - 248#64) 104 ∗
        sliceCursorAt slot ptr (0x22#8 :: BitVec.ofNat 8 mk_body.length :: (mk_body ++ rest)) ∗
        A.pool lim st s ∗
        stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F) Q NoPanicPost := by
  rcases hregs with ⟨hsp, hx29, hx19, hx20, hx24, hx21, hx22, hx25, hx26⟩
  have hsp_align_bv : s.sp &&& 15#64 = 0#64 := by
    rw [hsp]; exact sp_sub_256_aligned_seedChain halign
  have hlen_gt : tailLen < (0x22#8 :: BitVec.ofNat 8 mk_body.length :: (mk_body ++ rest)).length := by
    simp only [List.length_cons, List.length_append]; omega
  have hlen_cons_lt : (0x22#8 :: BitVec.ofNat 8 mk_body.length :: (mk_body ++ rest)).length < 2 ^ 62 := by
    simp only [List.length_cons, List.length_append]; omega
  have hule_ls := ule_ofNat_of_gt_false_seedChain62 hlen_gt hlen_cons_lt
  have hult_ls := ult_ofNat_of_gt_true_seedChain62 hlen_gt hlen_cons_lt
  have hsub1 := len_cons_sub_one_seedChain 0x22#8 (BitVec.ofNat 8 mk_body.length :: (mk_body ++ rest))
  have hrem1_lt : (BitVec.ofNat 8 mk_body.length :: (mk_body ++ rest)).length < 2 ^ 62 := by
    simp only [List.length_cons, List.length_append]; omega
  have hcbz2 := cbz_len_cons_false_seedChain62 hrem1_lt
  have hse0 := signExtend64_ofNat8_lt128_seedChain hmk_lt
  have hlsr56 := ofNat64_lsr56_eq_zero_seedChain hmk_lt
  have hsub2 := len_cons_sub_one_seedChain (BitVec.ofNat 8 mk_body.length) (mk_body ++ rest)
  have hlen_mk_append : (mk_body ++ rest).length = mk_body.length + rest.length := List.length_append
  have hult_mk_sub := ult_ofNat_add_right_false_seedChain (m := mk_body.length) (k := rest.length) (by omega)
  have hsub_mk_rest := bv_ofNat_add_sub_left_seedChain mk_body.length rest.length
  have h19 : s.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h20 : s.readReg64 (Reg.gpr 20#5) = a := hx20
  have h21 : s.readReg64 (Reg.gpr 21#5) = 98#64 := hx21
  have h22 : s.readReg64 (Reg.gpr 22#5) = 97#64 := hx22
  have h24 : s.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 tailLen := hx24
  have h25 : s.readReg64 (Reg.gpr 25#5) = sp0 - 248#64 := hx25
  have h26 : s.readReg64 (Reg.gpr 26#5) = 1#64 := hx26
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp0 - 96#64 := hx29
  rw [memRegion104_sp248_split sp0, memRegion80_sp248_eq_cells10 sp0]
  unfold sliceCursorAt
  rw [pointsToBytes_cons, pointsToBytes_cons]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun c0 => SepWPp.exists_elim fun c1 =>
    SepWPp.exists_elim fun c2 => SepWPp.exists_elim fun c3 =>
    SepWPp.exists_elim fun c4 => SepWPp.exists_elim fun c5 =>
    SepWPp.exists_elim fun c6 => SepWPp.exists_elim fun c7 =>
    SepWPp.exists_elim fun c8 => SepWPp.exists_elim fun c9 =>
    SepWPp.exists_elim fun c10 => SepWPp.exists_elim fun c11 =>
    SepWPp.exists_elim fun wc => ?_
  apply sepWPp_seq_lsclro_vm hcl hro (mid := (blkPl_11).base + 0x300#64)
  by_vm_steps_withSvc (
    iterate 48 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm1 hcl1 hro1
  rw [← A.pool_transport lim st s _ hvm1]
  have hdef := msgKeyCap_default_of_cells A.repAlloc sp0
  refine SepWPp.weaken_pre ?_ (hnext _
    (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
    hcl1 hro1 (by simp only [htr, arm64_norm]) (by simp only [hvregs, arm64_norm])
    ⟨by simp only [hsp, arm64_norm], by simp only [h19, arm64_norm],
     by simp only [h20, arm64_norm], by simp only [h21, arm64_norm],
     by simp only [h22, arm64_norm], by simp only [h24, arm64_norm],
     by simp only [h25, arm64_norm], by simp only [h26, arm64_norm],
     by simp only [arm64_norm], by simp only [h29, arm64_norm]⟩)
  unfold sliceCursorAt
  have hptr2 : ptr + 1#64 + 1#64 = ptr + 2#64 := by rw [BitVec.add_assoc]; rfl
  rw [← hlen_mk_append, ← mk_hdr_pointsTo_combine_seedChain ptr mk_body.length, hptr2]
  refine Entails.trans
    (Entails.of_eq (?_ : _ =
      (((sp0 - 248#64) ↦₆₄ 0#64) ∗ ((sp0 - 240#64) ↦₆₄ 1#64) ∗ ((sp0 - 232#64) ↦₆₄ 0#64) ∗
        ((sp0 - 224#64) ↦₆₄ 0#64) ∗ ((sp0 - 216#64) ↦₆₄ 1#64) ∗ ((sp0 - 208#64) ↦₆₄ 0#64) ∗
        ((sp0 - 200#64) ↦₆₄ 0#64) ∗ ((sp0 - 192#64) ↦₆₄ 1#64) ∗ ((sp0 - 184#64) ↦₆₄ 0#64) ∗
        ((sp0 - 176#64) ↦₆₄ 0#64) ∗ ((sp0 - 168#64) ↦₆₄ 1#64) ∗ ((sp0 - 160#64) ↦₆₄ 0#64)) ∗
      ((bufRef ↦₆₄ slot) ∗
        ((sp0 - 152#64) ↦₃₂ 0#32) ∗ memRegion (sp0 - 148#64) 4 ∗
        ((ptr ↦₈ 0x22#8) ∗ ((ptr + 1#64) ↦₈ BitVec.ofNat 8 mk_body.length)) ∗
        ((slot ↦₆₄ (ptr + 2#64)) ∗
          ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (mk_body ++ rest).length) ∗
          ((ptr + 2#64) ↦ₛ (mk_body ++ rest))) ∗
        A.pool lim st (vmDst hvm1) ∗
        stackAt (sp0 - 256#64) chainMergeSubStackX ∗ F)))
    (Entails.trans (sepConj_mono_left hdef) (Entails.of_eq (by cb_sep_eq)))
  · cb_sep_eq

set_option maxHeartbeats 800000 in
private theorem step_tag4b_budget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (a bufRef slot ptr sp0 : BitVec 64) (i : BitVec 32)
    (rest_mk rest : List (BitVec 8)) (tailLen : Nat) (st : M.σ)
    (hlen_lt : (pbVarint 1 i.toNat ++ rest_mk ++ rest).length < 2 ^ 62)
    {ret : BitVec 64} {s0 s : State} {F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_11).base + 0x300#64) (hrun : s.status = .Running)
    (halign : sp0 &&& 15#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hro : LibsignalRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : Tag4Regs sp0 bufRef a tailLen rest.length s)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_11).base + 0x300#64 → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → LibsignalRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace → calleeSavedVRegs sm = calleeSavedVRegs s0 →
      Tag4Regs sp0 bufRef a tailLen rest.length sm →
      SepWPp (lsProg_11 H) ret sm
        (((bufRef ↦₆₄ slot) ∗
          ((sp0 - 152#64) ↦₃₂ i) ∗
          (ptr ↦ₛ pbVarint 1 i.toNat) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbVarint 1 i.toNat).length) (rest_mk ++ rest) ∗
          A.pool lim st sm ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F) Q NoPanicPost) :
    SepWPp (lsProg_11 H) ret s
      (((bufRef ↦₆₄ slot) ∗
        ((sp0 - 152#64) ↦₃₂ 0#32) ∗
        sliceCursorAt slot ptr (pbVarint 1 i.toNat ++ (rest_mk ++ rest)) ∗
        A.pool lim st s ∗
        stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F) Q NoPanicPost := by
  by_cases hi0 : i = 0#32
  · subst hi0
    have hpb0 : pbVarint 1 (0#32).toNat = [] := rfl
    rw [hpb0] at hnext ⊢
    simp only [List.nil_append, List.length_nil, BitVec.add_zero, pointsToBytes_nil] at hnext ⊢
    exact SepWPp.weaken_pre (Entails.of_eq (by cb_sep_eq))
      (hnext s hpc hrun hcl hro htr hvregs hregs)
  · rcases hregs with ⟨hsp, hx19, hx20, hx21, hx22, hx24, hx25, hx26, hx28, hx29⟩
    have hi_pos : i.toNat ≠ 0 := by
      intro h; apply hi0; apply BitVec.eq_of_toNat_eq; simpa using h
    have hpb : pbVarint 1 i.toNat = 0x08#8 :: pbVarintBody 5 i.toNat := by
      unfold pbVarint; simp [hi_pos]; rfl
    let rem1 : List (BitVec 8) := pbVarintBody 5 i.toNat ++ (rest_mk ++ rest)
    have hcons_eq : pbVarint 1 i.toNat ++ (rest_mk ++ rest) = 0x08#8 :: rem1 := by
      rw [hpb]; simp [rem1, List.cons_append]
    have hlen_gt : rest.length < (0x08#8 :: rem1).length := by
      simp only [rem1, List.length_cons, List.length_append]; omega
    have hlen_cons_lt : (0x08#8 :: rem1).length < 2 ^ 62 := by
      rw [← hcons_eq]; simpa [List.append_assoc] using hlen_lt
    have hule_ls := ule_ofNat_of_gt_false_seedChain62 hlen_gt hlen_cons_lt
    have hult_ls := ult_ofNat_of_gt_true_seedChain62 hlen_gt hlen_cons_lt
    have hsub1 := len_cons_sub_one_seedChain 0x08#8 rem1
    have h19 : s.readReg64 (Reg.gpr 19#5) = bufRef := hx19
    have h20 : s.readReg64 (Reg.gpr 20#5) = a := hx20
    have h21 : s.readReg64 (Reg.gpr 21#5) = 98#64 := hx21
    have h22 : s.readReg64 (Reg.gpr 22#5) = 97#64 := hx22
    have h24 : s.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 tailLen := hx24
    have h25 : s.readReg64 (Reg.gpr 25#5) = sp0 - 248#64 := hx25
    have h26 : s.readReg64 (Reg.gpr 26#5) = 1#64 := hx26
    have h28 : s.readReg64 (Reg.gpr 28#5) = BitVec.ofNat 64 rest.length := hx28
    have h29 : s.readReg64 (Reg.gpr 29#5) = sp0 - 96#64 := hx29
    refine (?_ :
      (∀ s1 : State,
        s1.pc = lsmpl.base 8 → s1.status = .Running →
        LibsignalCodeLoaded lsmpl s1.mem → LibsignalRoLoaded lsmpl s1.mem →
        s1.trace = s0.trace → calleeSavedVRegs s1 = calleeSavedVRegs s0 →
        s1.readReg64 .lr = (blkPl_11).base + 0x424#64 →
        (s1.readReg64 .x0).setWidth 8 = 0#8 →
        s1.readReg64 .x1 = sp0 - 152#64 → s1.readReg64 .x2 = bufRef →
        Tag4Regs sp0 bufRef a tailLen rest.length s1 →
        SepWPp (lsProg_11 H) ret s1
          ((((sp0 - 152#64) ↦₃₂ 0#32) ∗
            (bufRef ↦₆₄ slot) ∗
            sliceCursorAt slot (ptr + 1#64) rem1 ∗
            A.pool lim st s1 ∗
            stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ ((ptr ↦₈ 0x08#8) ∗ F)) Q NoPanicPost) → _) ?_
    · intro hnext1
      rw [hcons_eq]
      unfold sliceCursorAt
      rw [pointsToBytes_cons]
      apply sepWPp_seq_lsclro_vm hcl hro (mid := lsmpl.base 8)
      by_vm_steps_withSvc (
        iterate 25 wp_step
        refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
          ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
      intro hvm1 hcl1 hro1
      rw [← A.pool_transport lim st s _ hvm1]
      refine SepWPp.weaken_pre ?_ (hnext1 _
        (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        hcl1 hro1 (by simp only [htr, arm64_norm]) (by simp only [hvregs, arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        ⟨by simp only [hsp, arm64_norm], by simp only [h19, arm64_norm],
         by simp only [h20, arm64_norm], by simp only [h21, arm64_norm],
         by simp only [h22, arm64_norm], by simp only [h24, arm64_norm],
         by simp only [h25, arm64_norm], by simp only [h26, arm64_norm],
         by simp only [h28, arm64_norm], by simp only [h29, arm64_norm]⟩)
      unfold sliceCursorAt
      exact Entails.of_eq (by cb_sep_eq)
    · intro s1 hpc1 hrun1 hcl1 hro1 htr1 hvregs1 hlr1 hx0_1 hx1_1 hx2_1 hregs1
      have hrem1_lt : (pbVarintBody 5 i.toNat ++ (rest_mk ++ rest)).length < 2 ^ 62 := by
        simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
      refine step_chainMerge_int32Merge_budget (sp0 - 152#64) bufRef slot (ptr + 1#64) sp0
        ((blkPl_11).base + 0x424#64) 0#32 i (rest_mk ++ rest) st hrem1_lt
        hpc1 hrun1 hregs1.1 halign hcl1 hro1 htr1 hlr1 hx0_1 hx1_1 hx2_1 ?_
      intro s2 hpc2 hrun2 hsp2 hcl2 hro2 htr2 hcs2 hx0_2
      have hregs2 := hregs1.of_calleeSaved hsp2 hcs2
      have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := by
        rcases hcs2 with ⟨_, _, _, _, _, _, _, _, _, _, _, hcv⟩; exact hcv.trans hvregs1
      rcases hregs2 with ⟨hsp2, hx19_2, hx20_2, hx21_2, hx22_2, hx24_2, hx25_2, hx26_2, hx28_2, hx29_2⟩
      have h0_2 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
      apply sepWPp_seq_lsclro_vm hcl2 hro2 (mid := (blkPl_11).base + 0x300#64)
      by_vm_steps_withSvc (
        iterate 3 wp_step
        refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
          ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
      intro hvm3 hcl3 hro3
      rw [← A.pool_transport lim st s2 _ hvm3]
      refine SepWPp.weaken_pre ?_ (hnext _
        (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        hcl3 hro3 (by simp only [htr2, arm64_norm]) (by simp only [hvregs2, arm64_norm])
        ⟨by simp only [hsp2, arm64_norm], by simp only [hx19_2, arm64_norm],
         by simp only [hx20_2, arm64_norm], by simp only [hx21_2, arm64_norm],
         by simp only [hx22_2, arm64_norm], by simp only [hx24_2, arm64_norm],
         by simp only [hx25_2, arm64_norm], by simp only [hx26_2, arm64_norm],
         by simp only [hx28_2, arm64_norm], by simp only [hx29_2, arm64_norm]⟩)
      rw [pbVarint1_ptr_advance_seedChain ptr i.toNat hi_pos,
        ← pbVarint1_pointsTo_combine_seedChain ptr i.toNat hi_pos]
      exact Entails.of_eq (by cb_sep_eq)

set_option maxHeartbeats 800000 in
private theorem step_tag4c_budget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H)
    (a bufRef slot ptr sp0 : BitVec 64)
    (seed rest : List (BitVec 8)) (tailLen : Nat) (st : M.σ)
    (hseed_lt : seed.length < 128)
    (hlen_lt : (pbBytes 5 seed ++ rest).length < 2 ^ 62)
    (hfit : FitsEvents M lim st (bytesMergeEvents 0 seed.length))
    {ret : BitVec 64} {s0 s : State} {F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_11).base + 0x300#64) (hrun : s.status = .Running)
    (halign : sp0 &&& 15#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hro : LibsignalRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : Tag4Regs sp0 bufRef a tailLen rest.length s)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_11).base + 0x300#64 → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → LibsignalRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace → calleeSavedVRegs sm = calleeSavedVRegs s0 →
      Tag4Regs sp0 bufRef a tailLen rest.length sm →
      SepWPp (lsProg_11 H) ret sm
        (((bufRef ↦₆₄ slot) ∗
          vecU8FreshCap A.repAlloc (sp0 - 176#64) seed ∗
          (ptr ↦ₛ pbBytes 5 seed) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbBytes 5 seed).length) rest ∗
          A.pool lim (M.stepEvents (bytesMergeEvents 0 seed.length) st) sm ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F) Q NoPanicPost) :
    SepWPp (lsProg_11 H) ret s
      (((bufRef ↦₆₄ slot) ∗
        vecU8FreshCap A.repAlloc (sp0 - 176#64) [] ∗
        sliceCursorAt slot ptr (pbBytes 5 seed ++ rest) ∗
        A.pool lim st s ∗
        stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F) Q NoPanicPost := by
  rcases hregs with ⟨hsp, hx19, hx20, hx21, hx22, hx24, hx25, hx26, hx28, hx29⟩
  have hpb : pbBytes 5 seed = 0x2a#8 :: BitVec.ofNat 8 seed.length :: seed :=
    pbBytes_lt128_eq_seedChain 5 (by decide) seed hseed_lt
  let rem1 : List (BitVec 8) := [BitVec.ofNat 8 seed.length] ++ seed ++ rest
  have hcons_eq : pbBytes 5 seed ++ rest = 0x2a#8 :: rem1 := by
    rw [hpb]; simp [rem1, List.cons_append, List.append_assoc]
  have hlen_gt : rest.length < (0x2a#8 :: rem1).length := by
    simp only [rem1, List.length_cons, List.length_append]; omega
  have hlen_cons_lt : (0x2a#8 :: rem1).length < 2 ^ 62 := by rw [← hcons_eq]; exact hlen_lt
  have hule_ls := ule_ofNat_of_gt_false_seedChain62 hlen_gt hlen_cons_lt
  have hult_ls := ult_ofNat_of_gt_true_seedChain62 hlen_gt hlen_cons_lt
  have hsub1 := len_cons_sub_one_seedChain 0x2a#8 rem1
  have h19 : s.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h20 : s.readReg64 (Reg.gpr 20#5) = a := hx20
  have h21 : s.readReg64 (Reg.gpr 21#5) = 98#64 := hx21
  have h22 : s.readReg64 (Reg.gpr 22#5) = 97#64 := hx22
  have h24 : s.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 tailLen := hx24
  have h25 : s.readReg64 (Reg.gpr 25#5) = sp0 - 248#64 := hx25
  have h26 : s.readReg64 (Reg.gpr 26#5) = 1#64 := hx26
  have h28 : s.readReg64 (Reg.gpr 28#5) = BitVec.ofNat 64 rest.length := hx28
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp0 - 96#64 := hx29
  refine (?_ :
    (∀ s1 : State,
      s1.pc = lsmpl.base 7 → s1.status = .Running →
      LibsignalCodeLoaded lsmpl s1.mem → LibsignalRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace → calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      s1.readReg64 .lr = (blkPl_11).base + 0x3b4#64 →
      (s1.readReg64 .x0).setWidth 8 = 2#8 →
      s1.readReg64 .x1 = sp0 - 176#64 → s1.readReg64 .x2 = bufRef →
      Tag4Regs sp0 bufRef a tailLen rest.length s1 →
      SepWPp (lsProg_11 H) ret s1
        ((vecU8FreshCap A.repAlloc (sp0 - 176#64) [] ∗
          (bufRef ↦₆₄ slot) ∗
          sliceCursorAt slot (ptr + 1#64) rem1 ∗
          A.pool lim st s1 ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ ((ptr ↦₈ 0x2a#8) ∗ F)) Q NoPanicPost) → _) ?_
  · intro hnext1
    rw [hcons_eq]
    unfold sliceCursorAt
    rw [pointsToBytes_cons]
    apply sepWPp_seq_lsclro_vm hcl hro (mid := lsmpl.base 7)
    by_vm_steps_withSvc (
      iterate 29 wp_step
      refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
    intro hvm1 hcl1 hro1
    rw [← A.pool_transport lim st s _ hvm1]
    refine SepWPp.weaken_pre ?_ (hnext1 _
      (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      hcl1 hro1 (by simp only [htr, arm64_norm]) (by simp only [hvregs, arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      ⟨by simp only [hsp, arm64_norm], by simp only [h19, arm64_norm],
       by simp only [h20, arm64_norm], by simp only [h21, arm64_norm],
       by simp only [h22, arm64_norm], by simp only [h24, arm64_norm],
       by simp only [h25, arm64_norm], by simp only [h26, arm64_norm],
       by simp only [h28, arm64_norm], by simp only [h29, arm64_norm]⟩)
    unfold sliceCursorAt
    exact Entails.of_eq (by cb_sep_eq)
  · intro s1 hpc1 hrun1 hcl1 hro1 htr1 hvregs1 hlr1 hx0_1 hx1_1 hx2_1 hregs1
    have hrem1_lt : ([BitVec.ofNat 8 seed.length] ++ seed ++ rest).length < 2 ^ 62 := by
      simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
    refine step_chainMerge_bytesMergeFresh_budget hA (sp0 - 176#64) bufRef slot (ptr + 1#64) sp0
      ((blkPl_11).base + 0x3b4#64) seed rest st hseed_lt hrem1_lt hfit
      hpc1 hrun1 hregs1.1 halign hcl1 hro1 htr1 hlr1 hx0_1 hx1_1 hx2_1 ?_
    intro s2 hpc2 hrun2 hsp2 hcl2 hro2 htr2 hcs2 hx0_2
    have hregs2 := hregs1.of_calleeSaved hsp2 hcs2
    have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := by
      rcases hcs2 with ⟨_, _, _, _, _, _, _, _, _, _, _, hcv⟩; exact hcv.trans hvregs1
    rcases hregs2 with ⟨hsp2, hx19_2, hx20_2, hx21_2, hx22_2, hx24_2, hx25_2, hx26_2, hx28_2, hx29_2⟩
    have h0_2 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    apply sepWPp_seq_lsclro_vm hcl2 hro2 (mid := (blkPl_11).base + 0x300#64)
    by_vm_steps_withSvc (
      iterate 3 wp_step
      refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
    intro hvm3 hcl3 hro3
    rw [← A.pool_transport lim _ s2 _ hvm3]
    refine SepWPp.weaken_pre ?_ (hnext _
      (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
      hcl3 hro3 (by simp only [htr2, arm64_norm]) (by simp only [hvregs2, arm64_norm])
      ⟨by simp only [hsp2, arm64_norm], by simp only [hx19_2, arm64_norm],
       by simp only [hx20_2, arm64_norm], by simp only [hx21_2, arm64_norm],
       by simp only [hx22_2, arm64_norm], by simp only [hx24_2, arm64_norm],
       by simp only [hx25_2, arm64_norm], by simp only [hx26_2, arm64_norm],
       by simp only [hx28_2, arm64_norm], by simp only [hx29_2, arm64_norm]⟩)
    rw [pbBytes_ptr_advance_seedChain 5 (by decide) ptr seed hseed_lt,
      ← pbBytes_pointsTo_combine_seedChain 5 (by decide) ptr seed hseed_lt]
    exact Entails.of_eq (by cb_sep_eq)


set_option maxHeartbeats 1200000 in
private theorem step_tag4d_budget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H)
    (a bufRef slot ptr_rest sp0 : BitVec 64)
    (keys : List MessageKeyGenerator) (rest : List (BitVec 8)) (tailLen : Nat) (st : M.σ)
    (hbound : keys.length ≤ maxMessageKeys)
    (hfit_grow : FitsEvents M lim st
      (if keys.length < vecCap4Of keys.length then [] else vec104GrowEvents (vecCap4Of keys.length)))
    {ret : BitVec 64} {s0 s : State} {F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_11).base + 0x300#64) (hrun : s.status = .Running)
    (halign : sp0 &&& 15#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hro : LibsignalRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : Tag4Regs sp0 bufRef a tailLen rest.length s)
    (hnext : ∀ (sm : State) (ptr' : BitVec 64),
      let cap' := BitVec.ofNat 64 (vecCap4Of (keys.length + 1))
      let st' := M.stepEvents
        (if keys.length < vecCap4Of keys.length then [] else vec104GrowEvents (vecCap4Of keys.length)) st
      keys.length + 1 ≤ cap'.toNat → cap'.toNat * 104 < 2 ^ 63 → ptr' ≠ 0 →
      sm.pc = (blkPl_11).base + 0x5c8#64 → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → LibsignalRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace → calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.sp = sp0 - 256#64 →
      sm.readReg64 .x19 = bufRef → sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = 98#64 → sm.readReg64 .x22 = 97#64 →
      sm.readReg64 .x23 = BitVec.ofNat 64 keys.length →
      sm.readReg64 .x24 = BitVec.ofNat 64 tailLen →
      sm.readReg64 .x25 = sp0 - 248#64 → sm.readReg64 .x26 = 1#64 →
      sm.readReg64 .x29 = sp0 - 96#64 →
      SepWPp (lsProg_11 H) ret sm
        (((bufRef ↦₆₄ slot) ∗
          sliceCursorAt slot ptr_rest rest ∗
          ((a + 0x30#64) ↦₆₄ cap') ∗ ((a + 0x38#64) ↦₆₄ ptr') ∗
          ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length) ∗
          A.repAlloc.live ptr' (cap'.toNat * 104) 8 ∗
          arrayAt (fun m b => prostMsgKeyAtCap A.repAlloc m b) 104 ptr' keys ∗
          memRegion (ptr' + BitVec.ofNat 64 (keys.length * 104)) 104 ∗
          memRegion (ptr' + BitVec.ofNat 64 ((keys.length + 1) * 104))
            ((cap'.toNat - (keys.length + 1)) * 104) ∗
          A.pool lim st' sm ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F) Q NoPanicPost) :
    SepWPp (lsProg_11 H) ret s
      (((bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr_rest rest ∗
        (∃∗ ptrMk : BitVec 64,
          vecAt A.repAlloc 104 8 (fun m b => prostMsgKeyAtCap A.repAlloc m b)
            (a + 0x30#64) (BitVec.ofNat 64 (vecCap4Of keys.length)) ptrMk keys) ∗
        A.pool lim st s ∗
        stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F) Q NoPanicPost := by
  rcases hregs with ⟨hsp, hx19, hx20, hx21, hx22, hx24, hx25, hx26, hx28, hx29⟩
  let cap_k := vecCap4Of keys.length
  let cap : BitVec 64 := BitVec.ofNat 64 cap_k
  have hcap_k_le : cap_k ≤ max (2 * keys.length) 4 := vecCap4Of_le_two_mul_max4 keys.length
  have hcap_nat : cap.toNat = cap_k := by
    dsimp [cap]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold maxMessageKeys at hbound; omega)]
  have hule_r : BitVec.ule (BitVec.ofNat 64 rest.length) (BitVec.ofNat 64 rest.length) = true := by
    simp [BitVec.ule]
  have hbne_r : (BitVec.ofNat 64 rest.length != BitVec.ofNat 64 rest.length) = false :=
    bne_self_eq_false _
  have h19 : s.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h20 : s.readReg64 (Reg.gpr 20#5) = a := hx20
  have h21 : s.readReg64 (Reg.gpr 21#5) = 98#64 := hx21
  have h22 : s.readReg64 (Reg.gpr 22#5) = 97#64 := hx22
  have h24 : s.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 tailLen := hx24
  have h25 : s.readReg64 (Reg.gpr 25#5) = sp0 - 248#64 := hx25
  have h26 : s.readReg64 (Reg.gpr 26#5) = 1#64 := hx26
  have h28 : s.readReg64 (Reg.gpr 28#5) = BitVec.ofNat 64 rest.length := hx28
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp0 - 96#64 := hx29
  refine SepWPp.weaken_pre
    (P' := (∃∗ ptr : BitVec 64,
      ⌜keys.length ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗
      ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length) ∗
      (if cap = 0 then emp else A.repAlloc.live ptr (cap.toNat * 104) 8) ∗
      arrayAt (fun m b => prostMsgKeyAtCap A.repAlloc m b) 104 ptr keys ∗
      (if cap = 0#64 then emp
       else memRegion (ptr + BitVec.ofNat 64 (keys.length * 104)) ((cap.toNat - keys.length) * 104))) ∗
      ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr_rest rest ∗
        A.pool lim st s ∗ stackAt (sp0 - 256#64) chainMergeSubStackX ∗ F))
    (by
      have hgrp :
          ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr_rest rest ∗
            (∃∗ ptrMk : BitVec 64,
              vecAt A.repAlloc 104 8 (fun m b => prostMsgKeyAtCap A.repAlloc m b)
                (a + 0x30#64) cap ptrMk keys) ∗
            A.pool lim st s ∗ stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F =
          (∃∗ ptrMk : BitVec 64,
            vecAt A.repAlloc 104 8 (fun m b => prostMsgKeyAtCap A.repAlloc m b)
              (a + 0x30#64) cap ptrMk keys) ∗
          ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr_rest rest ∗
            A.pool lim st s ∗ stackAt (sp0 - 256#64) chainMergeSubStackX ∗ F) := by cb_sep_eq
      dsimp only [cap, cap_k] at hgrp ⊢
      rw [hgrp]
      exact sepConj_mono_left (vecAt_keys_open A.repAlloc a cap keys)) ?_
  refine sepWPp_exists_left fun ptr => ?_
  rw [sepConj_assoc]
  refine sepWPp_pure_left_and fun ⟨hcap_le, hcap_lt, hptr⟩ => ?_
  by_cases hlt_cap : keys.length < cap_k
  · have hcap_le' : keys.length + 1 ≤ cap.toNat := by omega
    have hfull_ne : keys.length ≠ cap.toNat := by omega
    have hbeq_cap : (BitVec.ofNat 64 keys.length == cap) = false :=
      beq_ofNat_cap_false hcap_le hfull_ne
    have hcap_ne0 : cap ≠ 0 := by intro h0; rw [h0] at hcap_le'; simp at hcap_le'
    have hcap_next : vecCap4Of (keys.length + 1) = cap_k := by
      rw [vecCap4Of_succ]; simp [vecCap4Push, cap_k, hlt_cap]
    rw [memRegion_spare_split_of_lt cap ptr keys.length hcap_le' hcap_lt]
    simp only [hcap_ne0, ↓reduceIte]
    unfold sliceCursorAt
    apply sepWPp_seq_lsclro_vm hcl hro (mid := (blkPl_11).base + 0x5c8#64)
    by_vm_steps_withSvc (
      iterate 9 wp_step
      refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
    intro hvm1 hcl1 hro1
    rw [← A.pool_transport lim st s (vmDst hvm1) hvm1]
    have hnext_sp := hnext (vmDst hvm1) ptr
    dsimp only at hnext_sp
    have hcap'_eq : BitVec.ofNat 64 (vecCap4Of (keys.length + 1)) = cap := by
      rw [hcap_next]
    rw [hcap'_eq] at hnext_sp
    simp only [cap_k, hlt_cap, ↓reduceIte, AllocCostModel.stepEvents] at hnext_sp
    refine SepWPp.weaken_pre ?_ (hnext_sp hcap_le' hcap_lt hptr
      (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      hcl1 hro1 (by simp only [htr, arm64_norm]) (by simp only [hvregs, arm64_norm])
      (by simp only [hsp, arm64_norm])
      (by simp only [h19, arm64_norm]) (by simp only [h20, arm64_norm])
      (by simp only [h21, arm64_norm]) (by simp only [h22, arm64_norm])
      (by simp only [arm64_norm]) (by simp only [h24, arm64_norm])
      (by simp only [h25, arm64_norm]) (by simp only [h26, arm64_norm])
      (by simp only [h29, arm64_norm]))
    unfold sliceCursorAt
    exact Entails.of_eq (by cb_sep_eq)
  · have hfull_k : keys.length = cap_k := by omega
    have hfull : keys.length = cap.toNat := by omega
    have hbeq_cap : (BitVec.ofNat 64 keys.length == cap) = true := by rw [hfull]; simp
    have hpow2 : IsPow2Cap4 cap.toNat := by rw [hcap_nat]; exact vecCap4Of_pow2 keys.length
    have hcap_or : cap = 0#64 ∨ 2 ≤ cap.toNat := cap_zero_or_ge_two_of_isPow2Cap4 hpow2
    have hmax_le : max (2 * cap.toNat) 4 * 104 + 8 ≤ 2 ^ 63 := by
      unfold maxMessageKeys at hbound; omega
    have hcap_next : vecCap4Of (keys.length + 1) = max (2 * cap.toNat) 4 := by
      rw [vecCap4Of_succ]
      unfold vecCap4Push
      simp only [show ¬ (keys.length < vecCap4Of keys.length) from hlt_cap, ↓reduceIte]
      rw [vecCap4Next_eq_max_of_pow2 (vecCap4Of_pow2 keys.length), hcap_nat]
    have hfit_g : FitsEvents M lim st (vec104GrowEvents cap.toNat) := by
      simpa only [cap_k, hlt_cap, ↓reduceIte, hcap_nat] using hfit_grow
    rw [memRegion_spare_eq_emp_of_full cap ptr keys.length hfull]
    simp only [sepConj_emp]
    refine SepWPp.weaken_pre
      (P' := (∃∗ bs : List (BitVec 8), ∃∗ Hmov : SepProp,
        ⌜bs.length = keys.length * 104 ∧
          ∀ q : BitVec 64, ((q ↦ₛ bs) ∗ Hmov) ⊢
            arrayAt (fun m b => prostMsgKeyAtCap A.repAlloc m b) 104 q keys⌝ ∗
        (ptr ↦ₛ bs) ∗ Hmov) ∗
        (((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗
          ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length) ∗
          (if cap = 0 then emp else A.repAlloc.live ptr (cap.toNat * 104) 8) ∗
          (bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr_rest rest ∗
          A.pool lim st s ∗ stackAt (sp0 - 256#64) chainMergeSubStackX ∗ F))
      (by
        refine Entails.trans
          (Entails.of_eq (?_ : _ =
            arrayAt (fun m b => prostMsgKeyAtCap A.repAlloc m b) 104 ptr keys ∗
            (((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗
              ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length) ∗
              (if cap = 0 then emp else A.repAlloc.live ptr (cap.toNat * 104) 8) ∗
              (bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr_rest rest ∗
              A.pool lim st s ∗ stackAt (sp0 - 256#64) chainMergeSubStackX ∗ F)))
          (sepConj_mono_left (arrayAt_prostMsgKeyAtCap_move_bytes A.repAlloc keys ptr))
        · cb_sep_eq) ?_
    refine sepWPp_exists_left fun bs => sepWPp_exists_left fun Hmov => ?_
    rw [sepConj_assoc]
    refine sepWPp_pure_left_and fun ⟨hbs_len, hmov⟩ => ?_
    have hbs_cap : bs.length = cap.toNat * 104 := by rw [hbs_len, hfull]
    unfold sliceCursorAt
    apply sepWPp_seq_lsclro_vm hcl hro (mid := lsmpl.base 43)
    by_vm_steps_withSvc (
      iterate 11 wp_step
      refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
    intro hvm1 hcl1 hro1
    rw [← A.pool_transport lim st s _ hvm1]
    have hG := grow_one_104_budget_placed_ok_cl (callerProg := lsProg_11 H) hA
    have hal1 : (vmDst hvm1).spAligned = true := by
      simp only [vmDst, State.spAligned, hsp, arm64_norm, beq_iff_eq]
      exact halign
    have hlive_bs :
        (if cap = 0 then emp else A.repAlloc.live ptr (cap.toNat * 104) 8) ∗ (ptr ↦ₛ bs) =
        (if cap = 0 then emp else A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) := by
      by_cases hc0 : cap = 0
      · have hcap0 : cap.toNat = 0 := by rw [hc0]; rfl
        have hbs_nil : bs = [] := List.eq_nil_of_length_eq_zero (by rw [hbs_cap, hcap0])
        rw [hc0, hbs_nil]
        simp [pointsToBytes_nil]
      · simp only [hc0, ↓reduceIte, hbs_cap]; rfl
    have e38 : (a + 0x30#64) + 8#64 = a + 0x38#64 := by rw [BitVec.add_assoc]; rfl
    let F_grow : SepProp :=
      Hmov ∗ ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length) ∗
      (bufRef ↦₆₄ slot) ∗ (slot ↦₆₄ ptr_rest) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗ (ptr_rest ↦ₛ rest) ∗
      memRegion (sp0 - 256#64 - BitVec.ofNat 64 chainMergeSubStackX)
        (chainMergeSubStackX - growOneChainStackX) ∗ F
    refine sepWPp_call_lscl (x := ((a + 0x30#64, cap, ptr, bs), st)) (F := F_grow)
      (ret_pc := (blkPl_11).base + 0x624#64)
      hG hcl1 hro1
      (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      hal1 (by simp only [arm64_norm]) ?_
      (fun _ _ h => not_satisfies_false_sepConj h)
      (fun _ _ _ h => not_satisfies_false_sepConj h)
      (fun _ _ h => not_satisfies_false_sepConj h) ?_
    · dsimp only [growOne104BudgetSpecX, F_grow]
      have hsp1_eq : (vmDst hvm1).sp = sp0 - 256#64 := by simp only [vmDst, hsp, arm64_norm]
      rw [hsp1_eq, e38, stackAt_sub_to_growOne_seedChainW (sp0 - 256#64), ← hlive_bs]
      refine Entails.trans
        (Entails.of_eq (?_ : _ =
          (((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗
            ((if cap = 0 then emp else A.repAlloc.live ptr (cap.toNat * 104) 8) ∗ (ptr ↦ₛ bs)) ∗
            A.pool lim st (vmDst hvm1) ∗
            stackAt (sp0 - 256#64) growOneChainStackX) ∗
          (Hmov ∗ ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length) ∗
            (bufRef ↦₆₄ slot) ∗ (slot ↦₆₄ ptr_rest) ∗
            ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗ (ptr_rest ↦ₛ rest) ∗
            memRegion (sp0 - 256#64 - BitVec.ofNat 64 chainMergeSubStackX)
              (chainMergeSubStackX - growOneChainStackX) ∗ F)))
        (sepConj_mono_left (Entails.pure_right
          ⟨by simp only [h20, arm64_norm], hbs_cap, hptr, hcap_or, hmax_le, hfit_g⟩
          (Entails.refl _)))
      · cb_sep_eq
    · intro sm hpcm hrunm hspm hcsm hclm hrom
      have hsp1_eq : (vmDst hvm1).sp = sp0 - 256#64 := by simp only [vmDst, hsp, arm64_norm]
      rw [hsp1_eq] at hspm
      have ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, _, _, h29_2, hvregs_m⟩ := hcsm
      simp only [h19, h20, h21, h22, h24, h25, h26, h29, hsp, arm64_norm] at h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h29_2
      have hvregs_m' : calleeSavedVRegs sm = calleeSavedVRegs s0 := by
        simpa only [hvregs, arm64_norm] using hvregs_m
      have hx23_m : sm.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 keys.length := by
        rw [h23_2, hfull, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      dsimp only [growOne104BudgetSpecX, F_grow]
      rw [hsp1_eq, e38, sepConj_assoc]
      refine sepWPp_pure_left_and fun htr_m => ?_
      have htr_m' : sm.trace = s0.trace := by simpa only [htr, arm64_norm] using htr_m
      simp only [sepExists_sepConj_left]
      refine SepWPp.exists_elim fun p' => ?_
      rw [sepConj_assoc]
      refine sepWPp_pure_left_and fun hp' => ?_
      apply sepWPp_seq_lsclro_vm hclm hrom (mid := (blkPl_11).base + 0x5c8#64)
      by_vm_steps_withSvc (
        wp_step
        refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrunm, arm64_norm])
          ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
      intro hvm2 hcl2 hro2
      rw [← A.pool_transport lim _ sm (vmDst hvm2) hvm2]
      let cap_new := max (2 * cap.toNat) 4
      let cap' : BitVec 64 := BitVec.ofNat 64 cap_new
      have hcap'_nat : cap'.toNat = cap_new := by
        dsimp [cap', cap_new]
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold maxMessageKeys at hbound; omega)]
      have hcap'_le : keys.length + 1 ≤ cap'.toNat := by rw [hcap'_nat]; dsimp [cap_new]; omega
      have hcap'_lt : cap'.toNat * 104 < 2 ^ 63 := by
        rw [hcap'_nat]; dsimp [cap_new]; unfold maxMessageKeys at hbound; omega
      have hnext_sp := hnext (vmDst hvm2) p'
      dsimp only at hnext_sp
      rw [hcap_next] at hnext_sp
      have hite_grow :
          (if keys.length < vecCap4Of keys.length then ([] : List AllocEvent)
           else vec104GrowEvents (vecCap4Of keys.length)) =
          vec104GrowEvents cap.toNat := by
        simp only [show ¬ (keys.length < vecCap4Of keys.length) from hlt_cap, ↓reduceIte]
        exact congrArg vec104GrowEvents hcap_nat.symm
      rw [hite_grow] at hnext_sp
      refine SepWPp.weaken_pre ?_ (hnext_sp hcap'_le hcap'_lt hp'
        (by simp only [arm64_norm]) (by simp only [hrunm, arm64_norm])
        hcl2 hro2 (by simp only [htr_m', arm64_norm]) (by simp only [hvregs_m', arm64_norm])
        (by simp only [hspm, arm64_norm])
        (by simp only [h19_2, arm64_norm]) (by simp only [h20_2, arm64_norm])
        (by simp only [h21_2, arm64_norm]) (by simp only [h22_2, arm64_norm])
        (by simp only [hx23_m, arm64_norm]) (by simp only [h24_2, arm64_norm])
        (by simp only [h25_2, arm64_norm]) (by simp only [h26_2, arm64_norm])
        (by simp only [h29_2, arm64_norm]))
      unfold sliceCursorAt
      have hrem_eq : (cap_new - cap.toNat) * 104 = 104 + (cap'.toNat - (keys.length + 1)) * 104 := by
        rw [hcap'_nat, ← hfull]; dsimp [cap_new]; omega
      have hsplit_sp := memRegion_split (p' + BitVec.ofNat 64 (keys.length * 104)) 104
        ((cap'.toNat - (keys.length + 1)) * 104) (by unfold maxMessageKeys at hbound; omega)
      have hp_add : (p' + BitVec.ofNat 64 (keys.length * 104)) + BitVec.ofNat 64 104 =
          p' + BitVec.ofNat 64 ((keys.length + 1) * 104) := by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
      rw [hp_add] at hsplit_sp
      rw [hbs_len, hrem_eq, hsplit_sp]
      dsimp only [cap', cap_new] at hcap'_nat ⊢
      rw [hcap'_nat]
      have hlive_eq : A.live p' (max (2 * cap.toNat) 4 * 104) 8 =
          A.repAlloc.live p' (max (2 * cap.toNat) 4 * 104) 8 := rfl
      rw [hlive_eq]
      refine Entails.trans
        (Entails.of_eq (?_ : _ =
          ((p' ↦ₛ bs) ∗ Hmov) ∗
          ((bufRef ↦₆₄ slot) ∗
            ((slot ↦₆₄ ptr_rest) ∗
              ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗ (ptr_rest ↦ₛ rest)) ∗
            ((a + 0x30#64) ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗
            ((a + 0x38#64) ↦₆₄ p') ∗
            ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length) ∗
            A.repAlloc.live p' (max (2 * cap.toNat) 4 * 104) 8 ∗
            memRegion (p' + BitVec.ofNat 64 (keys.length * 104)) 104 ∗
            memRegion (p' + BitVec.ofNat 64 ((keys.length + 1) * 104))
              ((max (2 * cap.toNat) 4 - (keys.length + 1)) * 104) ∗
            A.pool lim (M.stepEvents (vec104GrowEvents cap.toNat) st) (vmDst hvm2) ∗
            stackAt (sp0 - 256#64) chainMergeSubStackX ∗ F)))
        (Entails.trans (sepConj_mono_left (hmov p')) (Entails.of_eq (by cb_sep_eq)))
      · rw [stackAt_sub_to_growOne_seedChainW (sp0 - 256#64)]; cb_sep_eq

set_option maxHeartbeats 1200000 in
private theorem step_tag4e_budget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (a cap' ptr' sp0 bufRef : BitVec 64) (tailLen : Nat)
    (keys : List MessageKeyGenerator) (mk : MessageKeyGenerator) (st : M.σ)
    (hcap_le : keys.length + 1 ≤ cap'.toNat) (hcap_lt : cap'.toNat * 104 < 2 ^ 63)
    (hptr : ptr' ≠ 0)
    {ret : BitVec 64} {s0 s : State} {F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_11).base + 0x5c8#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 256#64) (halign : sp0 &&& 15#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hro : LibsignalRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = bufRef) (hx20 : s.readReg64 .x20 = a)
    (hx21 : s.readReg64 .x21 = 98#64) (hx22 : s.readReg64 .x22 = 97#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 keys.length)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 tailLen)
    (hx25 : s.readReg64 .x25 = sp0 - 248#64) (hx26 : s.readReg64 .x26 = 1#64)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_11).base + 0x120#64 → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → LibsignalRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace → calleeSavedVRegs sm = calleeSavedVRegs s0 →
      LoopRegs sp0 bufRef a tailLen sm →
      SepWPp (lsProg_11 H) ret sm
        (((∃∗ ptrMk : BitVec 64,
            vecAt A.repAlloc 104 8 (fun m b => prostMsgKeyAtCap A.repAlloc m b)
              (a + 0x30#64) cap' ptrMk (keys ++ [mk])) ∗
          memRegion (sp0 - 248#64) 104 ∗
          A.pool lim st sm) ∗ F) Q NoPanicPost) :
    SepWPp (lsProg_11 H) ret s
      ((((a + 0x30#64) ↦₆₄ cap') ∗ ((a + 0x38#64) ↦₆₄ ptr') ∗
        ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length) ∗
        A.repAlloc.live ptr' (cap'.toNat * 104) 8 ∗
        arrayAt (fun m b => prostMsgKeyAtCap A.repAlloc m b) 104 ptr' keys ∗
        memRegion (ptr' + BitVec.ofNat 64 (keys.length * 104)) 104 ∗
        memRegion (ptr' + BitVec.ofNat 64 ((keys.length + 1) * 104))
          ((cap'.toNat - (keys.length + 1)) * 104) ∗
        prostMsgKeyAtCap A.repAlloc mk (sp0 - 248#64) ∗
        A.pool lim st s) ∗ F) Q NoPanicPost := by
  have hsp_align_bv : s.sp &&& 15#64 = 0#64 := by
    rw [hsp]; exact sp_sub_256_aligned_seedChain halign
  have hmadd := ptr_madd_104_eq ptr' keys.length
  have hadd1 := ofNat_add_one_eq keys.length
  have h19 : s.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h20 : s.readReg64 (Reg.gpr 20#5) = a := hx20
  have h21 : s.readReg64 (Reg.gpr 21#5) = 98#64 := hx21
  have h22 : s.readReg64 (Reg.gpr 22#5) = 97#64 := hx22
  have h23 : s.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 keys.length := hx23
  have h24 : s.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 tailLen := hx24
  have h25 : s.readReg64 (Reg.gpr 25#5) = sp0 - 248#64 := hx25
  have h26 : s.readReg64 (Reg.gpr 26#5) = 1#64 := hx26
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp0 - 96#64 := hx29
  let dst := ptr' + BitVec.ofNat 64 (keys.length * 104)
  refine SepWPp.weaken_pre
    (P' := (∃∗ q0 : BitVec 128, ∃∗ q1 : BitVec 128, ∃∗ q2 : BitVec 128,
      ∃∗ q3 : BitVec 128, ∃∗ q4 : BitVec 128, ∃∗ q5 : BitVec 128,
      ∃∗ w6 : BitVec 64, ∃∗ Hmov : SepProp,
        ⌜∀ b : BitVec 64, (chunks104_6QWAt b q0 q1 q2 q3 q4 q5 w6 ∗ Hmov) ⊢
          prostMsgKeyAtCap A.repAlloc mk b⌝ ∗
        chunks104_6QWAt (sp0 - 248#64) q0 q1 q2 q3 q4 q5 w6 ∗ Hmov) ∗
      ((∃∗ d0 : BitVec 128, ∃∗ d1 : BitVec 128, ∃∗ d2 : BitVec 128,
        ∃∗ d3 : BitVec 128, ∃∗ d4 : BitVec 128, ∃∗ d5 : BitVec 128,
        ∃∗ dw6 : BitVec 64,
          chunks104_6QWAt dst d0 d1 d2 d3 d4 d5 dw6) ∗
        (((a + 0x30#64) ↦₆₄ cap') ∗ ((a + 0x38#64) ↦₆₄ ptr') ∗
          ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length) ∗
          A.repAlloc.live ptr' (cap'.toNat * 104) 8 ∗
          arrayAt (fun m b => prostMsgKeyAtCap A.repAlloc m b) 104 ptr' keys ∗
          memRegion (ptr' + BitVec.ofNat 64 ((keys.length + 1) * 104))
            ((cap'.toNat - (keys.length + 1)) * 104) ∗
          A.pool lim st s ∗ F)))
    (by
      rw [← memRegion104_eq_exists_chunks104_6QWAt_receiverChains dst]
      have hgrp :
          (((a + 0x30#64) ↦₆₄ cap') ∗ ((a + 0x38#64) ↦₆₄ ptr') ∗
            ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length) ∗
            A.repAlloc.live ptr' (cap'.toNat * 104) 8 ∗
            arrayAt (fun m b => prostMsgKeyAtCap A.repAlloc m b) 104 ptr' keys ∗
            memRegion dst 104 ∗
            memRegion (ptr' + BitVec.ofNat 64 ((keys.length + 1) * 104))
              ((cap'.toNat - (keys.length + 1)) * 104) ∗
            prostMsgKeyAtCap A.repAlloc mk (sp0 - 248#64) ∗
            A.pool lim st s) ∗ F =
          prostMsgKeyAtCap A.repAlloc mk (sp0 - 248#64) ∗
          (memRegion dst 104 ∗
            (((a + 0x30#64) ↦₆₄ cap') ∗ ((a + 0x38#64) ↦₆₄ ptr') ∗
              ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length) ∗
              A.repAlloc.live ptr' (cap'.toNat * 104) 8 ∗
              arrayAt (fun m b => prostMsgKeyAtCap A.repAlloc m b) 104 ptr' keys ∗
              memRegion (ptr' + BitVec.ofNat 64 ((keys.length + 1) * 104))
                ((cap'.toNat - (keys.length + 1)) * 104) ∗
              A.pool lim st s ∗ F)) := by cb_sep_eq
      dsimp only [dst] at hgrp ⊢
      rw [hgrp]
      exact sepConj_mono_left (prostMsgKeyAtCap_move_chunks104 A.repAlloc (sp0 - 248#64) mk)) ?_
  refine sepWPp_exists_left fun q0 => sepWPp_exists_left fun q1 =>
    sepWPp_exists_left fun q2 => sepWPp_exists_left fun q3 =>
    sepWPp_exists_left fun q4 => sepWPp_exists_left fun q5 =>
    sepWPp_exists_left fun w6 => sepWPp_exists_left fun Hmov => ?_
  rw [sepConj_assoc]
  refine sepWPp_pure_left_and fun hmov => ?_
  rw [← sepConj_assoc]
  have hcomm_d :
      (chunks104_6QWAt (sp0 - 248#64) q0 q1 q2 q3 q4 q5 w6 ∗ Hmov) ∗
        (∃∗ d0 : BitVec 128, ∃∗ d1 : BitVec 128, ∃∗ d2 : BitVec 128,
          ∃∗ d3 : BitVec 128, ∃∗ d4 : BitVec 128, ∃∗ d5 : BitVec 128,
          ∃∗ dw6 : BitVec 64, chunks104_6QWAt dst d0 d1 d2 d3 d4 d5 dw6) =
      (∃∗ d0 : BitVec 128, ∃∗ d1 : BitVec 128, ∃∗ d2 : BitVec 128,
        ∃∗ d3 : BitVec 128, ∃∗ d4 : BitVec 128, ∃∗ d5 : BitVec 128,
        ∃∗ dw6 : BitVec 64, chunks104_6QWAt dst d0 d1 d2 d3 d4 d5 dw6) ∗
      (chunks104_6QWAt (sp0 - 248#64) q0 q1 q2 q3 q4 q5 w6 ∗ Hmov) := sepConj_comm _ _
  rw [hcomm_d, sepConj_assoc]
  refine sepWPp_exists_left fun d0 => sepWPp_exists_left fun d1 =>
    sepWPp_exists_left fun d2 => sepWPp_exists_left fun d3 =>
    sepWPp_exists_left fun d4 => sepWPp_exists_left fun d5 =>
    sepWPp_exists_left fun dw6 => ?_
  rw [chunks104_6QWAt_sp248_eq sp0 q0 q1 q2 q3 q4 q5 w6,
    chunks104_6QWAt_dst_eq_receiverChains dst d0 d1 d2 d3 d4 d5 dw6]
  apply sepWPp_seq_lsclro_vm hcl hro (mid := (blkPl_11).base + 0x120#64)
  by_vm_steps_withSvc (
    iterate 22 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm1 hcl1 hro1
  rw [← A.pool_transport lim st s _ hvm1]
  refine SepWPp.weaken_pre ?_ (hnext _
    (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
    hcl1 hro1 (by simp only [htr, arm64_norm]) (by simp only [hvregs, arm64_norm])
    ⟨by simp only [hsp, arm64_norm], by simp only [h29, arm64_norm],
     by simp only [h19, arm64_norm], by simp only [h20, arm64_norm],
     by simp only [h24, arm64_norm], by simp only [h21, arm64_norm],
     by simp only [h22, arm64_norm], by simp only [h25, arm64_norm],
     by simp only [h26, arm64_norm]⟩)
  have hdst_fold := chunks104_6QWAt_dst_eq_receiverChains dst q0 q1 q2 q3 q4 q5 w6
  have hsp_fold := chunks104_6QWAt_sp248_eq sp0 q0 q1 q2 q3 q4 q5 w6
  have hsp_mem := chunks104_6QWAt_entails_memRegion104_receiverChains (sp0 - 248#64) q0 q1 q2 q3 q4 q5 w6
  have hpush := vecAt_keys_push_fold A.repAlloc a cap' ptr' keys mk hcap_le hcap_lt hptr
  dsimp only [dst] at hdst_fold ⊢
  refine Entails.trans
    (Entails.of_eq (?_ : _ =
      (chunks104_6QWAt (ptr' + BitVec.ofNat 64 (keys.length * 104)) q0 q1 q2 q3 q4 q5 w6 ∗ Hmov) ∗
      (chunks104_6QWAt (sp0 - 248#64) q0 q1 q2 q3 q4 q5 w6 ∗
        (((a + 0x30#64) ↦₆₄ cap') ∗ ((a + 0x38#64) ↦₆₄ ptr') ∗
          ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 (keys.length + 1)) ∗
          A.repAlloc.live ptr' (cap'.toNat * 104) 8 ∗
          arrayAt (fun m b => prostMsgKeyAtCap A.repAlloc m b) 104 ptr' keys ∗
          memRegion (ptr' + BitVec.ofNat 64 ((keys.length + 1) * 104))
            ((cap'.toNat - (keys.length + 1)) * 104) ∗
          A.pool lim st (vmDst hvm1) ∗ F)))) ?_
  · rw [hdst_fold, hsp_fold]; cb_sep_eq
  · refine Entails.trans (sepConj_mono (hmov (ptr' + BitVec.ofNat 64 (keys.length * 104)))
      (sepConj_mono_left hsp_mem)) ?_
    refine Entails.trans
      (Entails.of_eq (?_ : _ =
        (((a + 0x30#64) ↦₆₄ cap') ∗ ((a + 0x38#64) ↦₆₄ ptr') ∗
          ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 (keys.length + 1)) ∗
          A.repAlloc.live ptr' (cap'.toNat * 104) 8 ∗
          arrayAt (fun m b => prostMsgKeyAtCap A.repAlloc m b) 104 ptr' keys ∗
          prostMsgKeyAtCap A.repAlloc mk (ptr' + BitVec.ofNat 64 (keys.length * 104)) ∗
          memRegion (ptr' + BitVec.ofNat 64 ((keys.length + 1) * 104))
            ((cap'.toNat - (keys.length + 1)) * 104)) ∗
        (memRegion (sp0 - 248#64) 104 ∗ A.pool lim st (vmDst hvm1) ∗ F)))
      (Entails.trans (sepConj_mono_left hpush) (Entails.of_eq (by cb_sep_eq)))
    · cb_sep_eq


private theorem step_chainTag4_budget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H)
    (x : ChainMergeGenGhost) (st₀ : M.σ) {s0 s : State} {k : Nat}
    {Q : State → SepProp → Prop}
    (hk : k < x.c.fields.length)
    (htag : (x.c.fields[k]'hk).tag = 4)
    (hinv : ChainLoopBudgetInv M lim x st₀ s0 k s)
    (hnext : ∀ sm : State,
      ChainLoopBudgetInv M lim x st₀ s0 (k + 1) sm →
      SepWPp (lsProg_11 H) (s0.readReg64 .lr) sm
        (ChainLoopBudgetSpatial M A lim x st₀ s0 (k + 1) sm) Q NoPanicPost) :
    SepWPp (lsProg_11 H) (s0.readReg64 .lr) s
      (ChainLoopBudgetSpatial M A lim x st₀ s0 k s) Q NoPanicPost := by
  rcases hinv with ⟨hpc, hrun, htr, hvregs, hcl, hro, hsp, halign,
    hx29, hx19, hx20, hx24, hx21, hx22, hx25, hx26, hcOk, hlen_lt, hfit⟩
  have hregs0 : LoopRegs s0.sp x.bufRef x.a x.tail.length s :=
    ⟨hsp, hx29, hx19, hx20, hx24, hx21, hx22, hx25, hx26⟩
  obtain ⟨mk, hfl⟩ := chainField_eq_key_of_tag4 htag
  obtain ⟨hfit_step, hfit_rem⟩ := chainLoop_fits_split hk hfit
  have hmk_mem : mk ∈ x.c.keys := mem_keys_of_key_mem_fields (hfl ▸ List.getElem_mem hk)
  have hseed : mk.seed.length = 32 := hcOk.2.2.2.1 mk hmk_mem
  have hseed_lt : mk.seed.length < 128 := by omega
  let c0 : ChainG := chainGAfter x.c k
  have hbound : c0.keys.length ≤ maxMessageKeys :=
    Nat.le_trans (chainGAfter_keys_length_le x.c k) hcOk.2.2.2.2
  let pfx : List (BitVec 8) := pfx_k x.c k
  let rest : List (BitVec 8) := (x.c.fields.drop (k + 1)).flatMap ChainField.enc ++ x.tail
  let v1 : List (BitVec 8) := pbVarint 1 mk.counter.toNat
  let v2 : List (BitVec 8) := pbBytes 5 mk.seed
  have hpay_eq : x.c.payload ++ x.tail =
      pfx ++ (0x22#8 :: BitVec.ofNat 8 (v1 ++ v2).length :: ((v1 ++ v2) ++ rest)) := by
    rw [payload_append_eq_pfx_rem x.c k x.tail]
    dsimp only [pfx, rem_k]
    rw [drop_fields_flatMap_enc_of_key hk hfl x.tail, lenField_4_encMessageKey_eq hseed,
      encMessageKey_eq_pb hseed]
    rfl
  have hcur_open :
      sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail)
        (((x.c.fields.drop k).flatMap ChainField.enc) ++ x.tail) =
      (x.ptr ↦ₛ pfx) ∗
        sliceCursorAt x.slot (x.ptr + BitVec.ofNat 64 pfx.length)
          (0x22#8 :: BitVec.ofNat 8 (v1 ++ v2).length :: ((v1 ++ v2) ++ rest)) := by
    have hrem : (x.c.fields.drop k).flatMap ChainField.enc ++ x.tail =
        0x22#8 :: BitVec.ofNat 8 (v1 ++ v2).length :: ((v1 ++ v2) ++ rest) := by
      rw [drop_fields_flatMap_enc_of_key hk hfl x.tail, lenField_4_encMessageKey_eq hseed,
        encMessageKey_eq_pb hseed]
      rfl
    rw [hrem, hpay_eq, sliceCursorAfter_append_eq_seedChain]
  have hmk_lt : (v1 ++ v2).length < 128 := by
    rw [← encMessageKey_eq_pb hseed]; exact encMessageKey_length_lt128 hseed
  have htail_le : x.tail.length ≤ rest.length := by simp [rest]
  have hlen_a : 2 + ((v1 ++ v2).length + rest.length) < 2 ^ 62 := by
    have h := hlen_lt; rw [hpay_eq] at h; simp only [List.length_append, List.length_cons] at h ⊢; omega
  have hlen_b : (v1 ++ v2 ++ rest).length < 2 ^ 62 := by
    simp only [List.length_append] at hlen_a ⊢; omega
  have hlen_c : (v2 ++ rest).length < 2 ^ 62 := by
    simp only [List.length_append] at hlen_a ⊢; omega
  let st_k := M.stepEvents (chainDoneEvents x.c k) st₀
  let growEvs :=
    if c0.keys.length < vecCap4Of c0.keys.length then ([] : List AllocEvent)
    else vec104GrowEvents (vecCap4Of c0.keys.length)
  have hfit_pair :
      FitsEvents M lim st_k (bytesMergeEvents 0 mk.seed.length) ∧
      FitsEvents M lim (M.stepEvents (bytesMergeEvents 0 mk.seed.length) st_k) growEvs := by
    have hf : FitsEvents M lim st_k (bytesMergeEvents 0 mk.seed.length ++ growEvs) := by
      simpa [st_k, c0, growEvs, hfl, chainFieldStepEvents] using hfit_step
    exact (fitsEvents_append (M := M) (lim := lim) (st := st_k)
      (evs₁ := bytesMergeEvents 0 mk.seed.length) (evs₂ := growEvs)).mp hf
  have hst_succ :
      M.stepEvents growEvs (M.stepEvents (bytesMergeEvents 0 mk.seed.length) st_k) =
        M.stepEvents (chainDoneEvents x.c (k + 1)) st₀ := by
    dsimp only [st_k, growEvs, c0]
    rw [chainDoneEvents_succ_of_lt hk, hfl]
    dsimp only [chainFieldStepEvents]
    simp only [AllocCostModel.stepEvents_append]
  let ptr4a : BitVec 64 := x.ptr + BitVec.ofNat 64 pfx.length
  let ptr4b : BitVec 64 := ptr4a + 2#64
  let ptr4c : BitVec 64 := ptr4b + BitVec.ofNat 64 v1.length
  let ptrRest : BitVec 64 := ptr4c + BitVec.ofNat 64 v2.length
  let F_base : SepProp :=
    prostChainGRestCap A.repAlloc x.a c0 ∗
    chainMergePad4 s0.sp ∗ chainMergeSavedRegs12 s0.sp s0 ∗ (x.ptr ↦ₛ pfx)
  refine SepWPp.weaken_pre
    (P' := (((x.bufRef ↦₆₄ x.slot) ∗
      memRegion (s0.sp - 248#64) 104 ∗
      sliceCursorAt x.slot ptr4a
        (0x22#8 :: BitVec.ofNat 8 (v1 ++ v2).length :: ((v1 ++ v2) ++ rest)) ∗
      A.pool lim st_k s ∗
      stackAt (s0.sp - 256#64) chainMergeSubStackX) ∗
      ((∃∗ ptrMk : BitVec 64,
        vecAt A.repAlloc 104 8 (fun m b => prostMsgKeyAtCap A.repAlloc m b)
          (x.a + 0x30#64) (BitVec.ofNat 64 (vecCap4Of c0.keys.length)) ptrMk c0.keys) ∗ F_base)))
    (by
      unfold ChainLoopBudgetSpatial
      dsimp only [c0, st_k, ptr4a, F_base]
      rw [prostChainGAtCap_eq_keys_sep_rest A.repAlloc x.a (vecCap4Of (chainGAfter x.c k).keys.length)
        (chainGAfter x.c k), chainMergeSavedRegs_eq_split s0.sp s0, hcur_open]
      exact Entails.of_eq (by cb_sep_eq))
    (step_tag4a_budget x.a x.bufRef x.slot ptr4a s0.sp (v1 ++ v2) rest x.tail.length st_k
      hmk_lt htail_le hlen_a hpc hrun halign hcl hro htr hvregs hregs0 ?_)
  intro s1 hpc1 hrun1 hcl1 hro1 htr1 hvregs1 hregs1
  refine SepWPp.weaken_pre
    (P' := (((x.bufRef ↦₆₄ x.slot) ∗
      ((s0.sp - 152#64) ↦₃₂ 0#32) ∗
      sliceCursorAt x.slot ptr4b (v1 ++ (v2 ++ rest)) ∗
      A.pool lim st_k s1 ∗
      stackAt (s0.sp - 256#64) chainMergeSubStackX) ∗
      (vecU8FreshCap A.repAlloc (s0.sp - 248#64) [] ∗
        vecU8FreshCap A.repAlloc (s0.sp - 224#64) [] ∗
        vecU8FreshCap A.repAlloc (s0.sp - 200#64) [] ∗
        vecU8FreshCap A.repAlloc (s0.sp - 176#64) [] ∗
        memRegion (s0.sp - 148#64) 4 ∗
        (ptr4a ↦ₛ [0x22#8, BitVec.ofNat 8 (v1 ++ v2).length]) ∗
        (∃∗ ptrMk : BitVec 64,
          vecAt A.repAlloc 104 8 (fun m b => prostMsgKeyAtCap A.repAlloc m b)
            (x.a + 0x30#64) (BitVec.ofNat 64 (vecCap4Of c0.keys.length)) ptrMk c0.keys) ∗ F_base)))
    (by
      rw [List.append_assoc v1 v2 rest]
      dsimp only [ptr4b]
      exact Entails.of_eq (by cb_sep_eq))
    (step_tag4b_budget x.a x.bufRef x.slot ptr4b s0.sp mk.counter v2 rest x.tail.length st_k
      hlen_b hpc1 hrun1 halign hcl1 hro1 htr1 hvregs1 hregs1 ?_)
  intro s2 hpc2 hrun2 hcl2 hro2 htr2 hvregs2 hregs2
  refine SepWPp.weaken_pre
    (P' := (((x.bufRef ↦₆₄ x.slot) ∗
      vecU8FreshCap A.repAlloc (s0.sp - 176#64) [] ∗
      sliceCursorAt x.slot ptr4c (v2 ++ rest) ∗
      A.pool lim st_k s2 ∗
      stackAt (s0.sp - 256#64) chainMergeSubStackX) ∗
      (vecU8FreshCap A.repAlloc (s0.sp - 248#64) [] ∗
        vecU8FreshCap A.repAlloc (s0.sp - 224#64) [] ∗
        vecU8FreshCap A.repAlloc (s0.sp - 200#64) [] ∗
        ((s0.sp - 152#64) ↦₃₂ mk.counter) ∗
        memRegion (s0.sp - 148#64) 4 ∗
        (ptr4a ↦ₛ [0x22#8, BitVec.ofNat 8 (v1 ++ v2).length]) ∗
        (ptr4b ↦ₛ v1) ∗
        (∃∗ ptrMk : BitVec 64,
          vecAt A.repAlloc 104 8 (fun m b => prostMsgKeyAtCap A.repAlloc m b)
            (x.a + 0x30#64) (BitVec.ofNat 64 (vecCap4Of c0.keys.length)) ptrMk c0.keys) ∗ F_base)))
    (by dsimp only [ptr4c, v1]; exact Entails.of_eq (by cb_sep_eq))
    (step_tag4c_budget hA x.a x.bufRef x.slot ptr4c s0.sp mk.seed rest x.tail.length st_k
      hseed_lt hlen_c hfit_pair.1 hpc2 hrun2 halign hcl2 hro2 htr2 hvregs2 hregs2 ?_)
  intro s3 hpc3 hrun3 hcl3 hro3 htr3 hvregs3 hregs3
  let st_mid := M.stepEvents (bytesMergeEvents 0 mk.seed.length) st_k
  refine SepWPp.weaken_pre
    (P' := (((x.bufRef ↦₆₄ x.slot) ∗
      sliceCursorAt x.slot ptrRest rest ∗
      (∃∗ ptrMk : BitVec 64,
        vecAt A.repAlloc 104 8 (fun m b => prostMsgKeyAtCap A.repAlloc m b)
          (x.a + 0x30#64) (BitVec.ofNat 64 (vecCap4Of c0.keys.length)) ptrMk c0.keys) ∗
      A.pool lim st_mid s3 ∗
      stackAt (s0.sp - 256#64) chainMergeSubStackX) ∗
      (prostMsgKeyAtCap A.repAlloc mk (s0.sp - 248#64) ∗
        (ptr4a ↦ₛ [0x22#8, BitVec.ofNat 8 (v1 ++ v2).length]) ∗
        (ptr4b ↦ₛ v1) ∗ (ptr4c ↦ₛ v2) ∗ F_base)))
    (by
      dsimp only [ptrRest, v2, st_mid]
      rw [← prostMsgKeyAtCap_fold A.repAlloc s0.sp mk]
      exact Entails.of_eq (by cb_sep_eq))
    (step_tag4d_budget hA x.a x.bufRef x.slot ptrRest s0.sp c0.keys rest x.tail.length st_mid
      hbound hfit_pair.2 hpc3 hrun3 halign hcl3 hro3 htr3 hvregs3 hregs3 ?_)
  intro s4 ptr' cap' st_end hcap'_le hcap'_lt hptr' hpc4 hrun4 hcl4 hro4 htr4 hvregs4
    hsp4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx29_4
  refine SepWPp.weaken_pre
    (P' := ((((x.a + 0x30#64) ↦₆₄ cap') ∗ ((x.a + 0x38#64) ↦₆₄ ptr') ∗
      ((x.a + 0x40#64) ↦₆₄ BitVec.ofNat 64 c0.keys.length) ∗
      A.repAlloc.live ptr' (cap'.toNat * 104) 8 ∗
      arrayAt (fun m b => prostMsgKeyAtCap A.repAlloc m b) 104 ptr' c0.keys ∗
      memRegion (ptr' + BitVec.ofNat 64 (c0.keys.length * 104)) 104 ∗
      memRegion (ptr' + BitVec.ofNat 64 ((c0.keys.length + 1) * 104))
        ((cap'.toNat - (c0.keys.length + 1)) * 104) ∗
      prostMsgKeyAtCap A.repAlloc mk (s0.sp - 248#64) ∗
      A.pool lim st_end s4) ∗
      ((x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot ptrRest rest ∗
        stackAt (s0.sp - 256#64) chainMergeSubStackX ∗
        (ptr4a ↦ₛ [0x22#8, BitVec.ofNat 8 (v1 ++ v2).length]) ∗
        (ptr4b ↦ₛ v1) ∗ (ptr4c ↦ₛ v2) ∗ F_base)))
    (by dsimp only [cap', st_end, growEvs]; exact Entails.of_eq (by cb_sep_eq))
    (step_tag4e_budget x.a cap' ptr' s0.sp x.bufRef x.tail.length c0.keys mk st_end
      hcap'_le hcap'_lt hptr' hpc4 hrun4 hsp4 halign hcl4 hro4 htr4 hvregs4
      hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx29_4 ?_)
  intro sf hpcf hrunf hclf hrof htrf hvregsf hregsf
  rcases hregsf with ⟨hspf, hx29f, hx19f, hx20f, hx24f, hx21f, hx22f, hx25f, hx26f⟩
  refine SepWPp.weaken_pre ?_ (hnext sf
    ⟨hpcf, hrunf, htrf, hvregsf, hclf, hrof, hspf, halign,
     hx29f, hx19f, hx20f, hx24f, hx21f, hx22f, hx25f, hx26f, hcOk, hlen_lt, hfit_rem⟩)
  unfold ChainLoopBudgetSpatial
  have hc_succ : chainGAfter x.c (k + 1) = { c0 with keys := c0.keys ++ [mk] } :=
    chainGAfter_succ_of_key hk hfl
  have hlen_succ : (c0.keys ++ [mk]).length = c0.keys.length + 1 := by simp
  have hcur_comb := sliceCursorAfter_tag4_combine x.slot x.ptr (x.c.payload ++ x.tail)
    pfx v1 v2 rest hpay_eq
  rw [hc_succ, hlen_succ,
    prostChainGAtCap_eq_keys_sep_rest A.repAlloc x.a (vecCap4Of (c0.keys.length + 1))
      { c0 with keys := c0.keys ++ [mk] },
    prostChainGRestCap_update_keys,
    chainMergeSavedRegs_eq_split s0.sp s0]
  dsimp only [cap', st_end, st_mid, F_base, ptr4a, ptr4b, ptr4c, ptrRest]
  rw [hst_succ, ← hcur_comb]
  exact Entails.of_eq (by cb_sep_eq)


/-! ## 5. Loop Exit, Loop Induction & Top-Level `chainMergeGen_budget_placed_ok` -/

set_option maxHeartbeats 800000 in
private theorem step_chainExit_budget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (x : ChainMergeGenGhost) (st₀ : M.σ) {s0 s : State}
    (hinv : ChainLoopBudgetInv M lim x st₀ s0 x.c.fields.length s) :
    SepWPp (lsProg_11 H) (s0.readReg64 .lr) s
      (ChainLoopBudgetSpatial M A lim x st₀ s0 x.c.fields.length s)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
          (Pf ⊢ (chainMergeGenBudgetSpecW M A lim).post (x, st₀) s0 sf))
      NoPanicPost := by
  rcases hinv with ⟨hpc, hrun, htr, hvregs, hcl, hro, hsp, halign,
    _, hx19, _, hx24, _, _, _, _, _, _, _⟩
  have hsp_sub_align : s.sp &&& 15#64 = 0#64 := by
    rw [hsp]; exact sp_sub_256_aligned_seedChain halign
  have hsp_restore : s0.sp - 256#64 + 256#64 = s0.sp := BitVec.sub_add_cancel s0.sp 256#64
  have h19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef := hx19
  have h24 : s.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 x.tail.length := hx24
  have h30_init : s0.readReg64 (Reg.gpr 30#5) = s0.readReg64 .lr := rfl
  let ptrEnd := x.ptr + BitVec.ofNat 64 x.c.payload.length
  unfold ChainLoopBudgetSpatial
  rw [chainGAfter_fields x.c, List.drop_length, List.flatMap_nil, List.nil_append,
    sliceCursorAfter_append_eq_seedChain x.slot x.ptr x.c.payload x.tail]
  have hdone_eq : chainDoneEvents x.c x.c.fields.length = chainMergeEvents x.c := rfl
  rw [hdone_eq]
  unfold sliceCursorAt chainMergeSavedRegs
  apply sepWPp_seq_lsclro_vm hcl hro (mid := s0.readReg64 .lr)
  by_vm_steps_withSvc (
    iterate 15 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm1 _ _
  rw [← A.pool_transport lim (M.stepEvents (chainMergeEvents x.c) st₀) s _ hvm1]
  refine SepWPp.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
    ⟨by simp only [arm64_norm],
     ⟨by simp only [arm64_norm], by simp only [arm64_norm],
      by simp only [arm64_norm], by simp only [arm64_norm],
      by simp only [arm64_norm], by simp only [arm64_norm],
      by simp only [arm64_norm], by simp only [arm64_norm],
      by simp only [arm64_norm], by simp only [arm64_norm],
      by simp only [arm64_norm], by simp only [hvregs, arm64_norm]⟩, ?_⟩
  dsimp only [chainMergeGenBudgetSpecW, withLsCodeRoLoaded, chainMergeGenBudgetRawSpecW]
  rw [sliceCursorAfter_append_eq_seedChain x.slot x.ptr x.c.payload x.tail,
    stackAt_chainMergeStackX_split_seedChain s0.sp]
  unfold sliceCursorAt
  refine Entails.pure_right ⟨by simp only [htr, arm64_norm], by simp only [arm64_norm]⟩ ?_
  have hsaved12 :
      ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
      ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ⊢
      (∃∗ w96 : BitVec 64, ∃∗ w88 : BitVec 64, ∃∗ w80 : BitVec 64, ∃∗ w72 : BitVec 64,
       ∃∗ w64 : BitVec 64, ∃∗ w56 : BitVec 64, ∃∗ w48 : BitVec 64, ∃∗ w40 : BitVec 64,
       ∃∗ w32 : BitVec 64, ∃∗ w24 : BitVec 64, ∃∗ w16 : BitVec 64, ∃∗ w8 : BitVec 64,
        ((s0.sp - 96#64) ↦₆₄ w96) ∗ ((s0.sp - 88#64) ↦₆₄ w88) ∗
        ((s0.sp - 80#64) ↦₆₄ w80) ∗ ((s0.sp - 72#64) ↦₆₄ w72) ∗
        ((s0.sp - 64#64) ↦₆₄ w64) ∗ ((s0.sp - 56#64) ↦₆₄ w56) ∗
        ((s0.sp - 48#64) ↦₆₄ w48) ∗ ((s0.sp - 40#64) ↦₆₄ w40) ∗
        ((s0.sp - 32#64) ↦₆₄ w32) ∗ ((s0.sp - 24#64) ↦₆₄ w24) ∗
        ((s0.sp - 16#64) ↦₆₄ w16) ∗ ((s0.sp - 8#64) ↦₆₄ w8)) :=
    Entails.sepExists_right (s0.readReg64 .x29)
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
                          (Entails.sepExists_right (s0.readReg64 .x19)
                            (Entails.refl _))))))))))))
  refine Entails.trans
    (Entails.of_eq (?_ : _ =
      (((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗
      (prostChainGAtCap A.repAlloc x.a (vecCap4Of x.c.keys.length) x.c ∗
        (x.bufRef ↦₆₄ x.slot) ∗
        ((x.ptr ↦ₛ x.c.payload) ∗
          ((x.slot ↦₆₄ (x.ptr + BitVec.ofNat 64 x.c.payload.length)) ∗
            ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 x.tail.length) ∗
            ((x.ptr + BitVec.ofNat 64 x.c.payload.length) ↦ₛ x.tail))) ∗
        A.pool lim (M.stepEvents (chainMergeEvents x.c) st₀) (vmDst hvm1) ∗
        stackAt (s0.sp - 256#64) chainMergeSubStackX ∗
        memRegion (s0.sp - 256#64) 160)))
    (Entails.trans (sepConj_mono_left hsaved12) (Entails.of_eq (by cb_sep_eq)))
  · cb_sep_eq

private theorem chainLoop_budget_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H)
    (x : ChainMergeGenGhost) (st₀ : M.σ) {s0 : State} :
    ∀ (d k : Nat) (s : State),
      k ≤ x.c.fields.length →
      x.c.fields.length - k = d →
      ChainLoopBudgetInv M lim x st₀ s0 k s →
      SepWPp (lsProg_11 H) (s0.readReg64 .lr) s
        (ChainLoopBudgetSpatial M A lim x st₀ s0 k s)
        (fun sf Pf =>
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
            (Pf ⊢ (chainMergeGenBudgetSpecW M A lim).post (x, st₀) s0 sf))
        NoPanicPost
  | 0, k, s, hle, hd, hinv => by
    have hk_eq : k = x.c.fields.length := by omega
    subst hk_eq
    exact step_chainExit_budget x st₀ hinv
  | d + 1, k, s, _hle, hd, hinv => by
    have hk : k < x.c.fields.length := by omega
    have hrem : x.c.fields.length - (k + 1) = d := by omega
    have ih : ∀ sm : State,
        ChainLoopBudgetInv M lim x st₀ s0 (k + 1) sm →
        SepWPp (lsProg_11 H) (s0.readReg64 .lr) sm
          (ChainLoopBudgetSpatial M A lim x st₀ s0 (k + 1) sm) _ NoPanicPost :=
      fun sm hinv' => chainLoop_budget_ok hA x st₀ d (k + 1) sm (by omega) hrem hinv'
    cases hfl : x.c.fields[k]'hk with
    | srk b => exact step_chainTag12_budget hA x st₀ hk (Or.inl (by simp [hfl, ChainField.tag])) hinv ih
    | priv b => exact step_chainTag12_budget hA x st₀ hk (Or.inr (by simp [hfl, ChainField.tag])) hinv ih
    | ck i key => exact step_chainTag3_budget hA x st₀ hk (by simp [hfl, ChainField.tag]) hinv ih
    | key mk => exact step_chainTag4_budget hA x st₀ hk (by simp [hfl, ChainField.tag]) hinv ih

/-- Relocatable `[LibsignalPlacement]` total-correctness (`onPanic := ⌜False⌝`, `onOom := ⌜False⌝`)
proof of `prost::encoding::message::merge<Chain>` (Block `11`, `lsProg_11 H`, `chainMergeStackX`). -/
theorem chainMergeGen_budget_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H) :
    subroutine_ok (lsProg_11 H) (blkPl_11).base (chainMergeGenBudgetSpecW M A lim) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st₀⟩ R s0 hpc hrun hpre hal =>
    reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨⟨hcl, hro⟩, hpre⟩ := extract_withLsCodeRoLoaded hpre
  rw [chainMergeGenBudgetRawSpecW, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hx3, hcOk, hlen_lt, hfit⟩, hm⟩ := hpre
  have hwp : SepWPp (lsProg_11 H) (s0.readReg64 .lr) s0
      (prostChainGAtCap A.repAlloc x.a 0 ChainG.empty ∗
        (x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAt x.slot x.ptr (x.c.payload ++ x.tail) ∗
        A.pool lim st₀ s0 ∗
        stackAt s0.sp chainMergeStackX)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
          (Pf ⊢ (chainMergeGenBudgetSpecW M A lim).post (x, st₀) s0 sf))
      NoPanicPost :=
    step_chainEntry_budget x st₀ hpc hrun hal hcl hro hx0 hx1 hx2 hx3 hcOk hlen_lt hfit
      (fun sm hinv0 =>
        chainLoop_budget_ok hA x st₀ x.c.fields.length 0 sm (Nat.zero_le _) (Nat.sub_zero _) hinv0)
  obtain ⟨sf, hsteps, hex⟩ := hwp R hm hL
  refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
  rcases hex with ⟨hpc_f, hrun_f, Pf, hmf, hsp_f, hcs_f, hent_f⟩ | ⟨_, _, _, hpan⟩ | ⟨_, hoom⟩
  · exact Or.inl ⟨⟨hpc_f, hsp_f, hrun_f⟩, ⟨hsp_f, hcs_f⟩,
      Satisfies.mono (sepConj_mono_left hent_f) hmf⟩
  · exact hpan.elim
  · exact (not_satisfies_false_sepConj hoom).elim

private theorem ls_subroutine_ok_ro_of_callee_11 [LibsignalPlacement] {α : Type}
    {H : LibsignalHooks} {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H] {spec : Spec α}
    (h : subroutine_ok ((blkPC_11).rebase (blkPl_11).base H) (blkPl_11).base
      (withLsCodeRoLoaded lsmpl spec)) :
    subroutine_ok callerProg (lsmpl.base 11) (withLsCodeRoLoaded lsmpl spec) := by
  let specRo : Spec α :=
    { spec with pre := fun x s0 => ⌜LibsignalRoLoaded lsmpl s0.mem⌝ ∗ spec.pre x s0 }
  have h1 : subroutine_ok ((blkPC_11).rebase (blkPl_11).base H) (blkPl_11).base
      (withLsCodeLoaded lsmpl specRo) := by
    refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
    obtain ⟨hcl, hpre_ro⟩ := extract_withLsCodeLoaded hpre
    dsimp only [specRo] at hpre_ro
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_ro
    obtain ⟨hro, hm⟩ := hpre_ro
    have hpre' : s0.mem ⊨ (withLsCodeRoLoaded lsmpl spec).pre x s0 ∗ R := by
      dsimp only [withLsCodeRoLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨⟨hcl, hro⟩, hm⟩
    exact h.mono_outcome x R s0 hpc hrun hpre' hal (fun _ hout => hout)
  have h2 : subroutine_ok callerProg (lsmpl.base 11) (withLsCodeLoaded lsmpl specRo) :=
    ls_subroutine_ok_of_callee (j := 11) h1
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  obtain ⟨⟨hcl, hro⟩, hm⟩ := extract_withLsCodeRoLoaded hpre
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl specRo).pre x s0 ∗ R := by
    dsimp only [withLsCodeLoaded, specRo]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hro, hm⟩
  exact h2.mono_outcome x R s0 hpc hrun hpre' hal (fun _ hout => hout)

/-- Caller-block-polymorphic `withLsCodeRoLoaded` form of `chainMergeGen_budget_placed_ok`. -/
theorem chainMergeGen_budget_placed_ok_cl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hA : AllocContractsBudgetPlaced M A lim H) :
    subroutine_ok callerProg (lsmpl.base 11) (chainMergeGenBudgetSpecW M A lim) :=
  ls_subroutine_ok_ro_of_callee_11 (chainMergeGen_budget_placed_ok hA)

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.ChainBudget
