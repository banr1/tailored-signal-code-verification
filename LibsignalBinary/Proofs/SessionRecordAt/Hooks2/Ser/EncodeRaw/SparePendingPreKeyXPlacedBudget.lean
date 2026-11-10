/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.PendingPreKeyFields
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.PendingPreKeyHeader
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.BaseXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.BaseX
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PendingPreKeyFieldsXAPlaced
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PendingPreKeyFieldsXBPlaced
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PendingPreKeyFieldsXBPlacedBudgetAux
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.SpareBaseXBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.E2E.Record.Serialization.ChainLenAux.Pure
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.SenderReceiverChains
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PendingPreKeyFieldsXA
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PendingPreKeyFieldsXB
import ProofLib.SepLogic.WPp

/-!
# Pre-Reserved `SessionStructure::encode_raw` Tag 9: `pending_pre_key` (`536` → `1080`)

Proves zero-allocation (`VmPreserved`-preserving) relocatable step lemmas for protobuf tag 9
(`pending_pre_key`, Block `14` offsets `536..1080`) when the output buffer has sufficient spare
capacity.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.SparePendingPreKeyXPlacedBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSessionApi (PendingPreKey)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks lsmpl lsMemcpySym lsρ
)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8At)
open CryptoVerification.LibsignalTripleRatchetRepr (TailVecGhost optTailVecAt)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  vecU8Buf vecU8At_eq_header_sep_buf cap_beq_len_false
  ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32 optU32Tag
)
open CryptoVerification.E2E.Record (
  optUint32Field bytesField int32Field uint64Field PendingRel
)
open CryptoVerification.E2E.Record.Placed (blkPl_14 lsProg_14)
open CryptoVerification.E2E.Record.Serialization (
  encodeRawSubStackX encPendingMem encPendingFieldMem
  sepWPpLsCl_extract_vecU8At_bounds sepWPpLsCl_extract_pending_some
  bv_add_neg80_3b
)
open CryptoVerification.E2E.Record.Serialization.EncodeRawAux (
  entails_of_sep_focus EncRawUpperSaved sp_sub_80_spAligned
  vecSrcRest vecCopyDone optU32ValAt optU32ValAt_some pendingTailRest pendingOpenAt
  optU32Tag_bne1_pc optUint32Field1_none_eq optUint32Field1_some_eq
  optUint32Field1_length_le int32Field3_length_le
  int32Field3_zero_eq int32Field3_nonzero_eq zext64_beq_zero_false_3b
  uint64Field4_zero_eq uint64Field4_nonzero_eq uint64Field4_nonzero_length_bv
  encPendingMem_length_bv encPendingMem_length_bv_ts_zero
  lenField9_eq bytesField2_nonempty_eq
  optTailVecAt_pending_none_eq optTailVecAt_pending_some_eq_open
  publicKey_deserialize_ne_nil
  bv64_beq_zero_false ofNat64_len_beq_zero_false
  truncate32_signExtend64_er er_truncate32_zext64_lsr6
  erHwVarintLen_eq_encodeVarint_length erHwVarintLen_bvShift_eq_encodeVarint_length
  bv_add_neg80_3a cmn1_beq_zero_false cap_beq_noneCap_false
  vecU8At_open_one vecU8At_close_one vecU8At_close_slice
  cmp_hi_false_of_le encodeVarint_length_le_10
)
open Proofs.libsignal.Hooks2 (SepWPpLsCl)
open LibsignalBinary.Heap (
  VmPreserved AllocCostModel BudgetLimits RustCliAllocBudget
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (
  SerContractsXPlaced
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.BaseXBudget (
  sepWPpLsCl_of_sepWP_vm
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.SpareBaseXBudget (
  encraw_call_encodeVarint_prealloc_placed_x encraw_call_memcpy_buf_prealloc_placed_x
)

abbrev step_tag9_len1_placed_x :=
  @PendingPreKeyFieldsXBPlacedBudgetAux.step_tag9_len1_placed_x
abbrev step_tag9_len2_placed_x :=
  @PendingPreKeyFieldsXBPlacedBudgetAux.step_tag9_len2_placed_x
abbrev step_tag9_len3_placed_x :=
  @PendingPreKeyFieldsXBPlacedBudgetAux.step_tag9_len3_placed_x

/-! ## Header and nested length varint (`536 → 824/872`) -/

section Seg3a

set_option allowUnsafeReducibility true in
attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
  stackAt vecU8Buf vecSrcRest vecCopyDone optU32ValAt pendingTailRest

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  truncate32_signExtend64_er truncate32_zeroExtend64
  ofNat_countLeadingZeros_64
  ofNat_countLeadingZeros_32
  CryptoVerification.LibsignalTripleRatchet.Prost.truncate32_ofNat64
  er_truncate32_zext64_lsr6
  erHwVarintLen_eq_encodeVarint_length
  erHwVarintLen_bvShift_eq_encodeVarint_length
  bv_add_neg80_3a

theorem step_tag9_write_tag_prealloc_placed_x [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (bs : List (BitVec 8))
    (hcap_g : g.vec.cap.toNat < 2 ^ 63)
    (hlt : bs.length < cap.toNat)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 536#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (pendingOpenAt A ss g p ∗ vecU8At A v cap ptr bs ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_14).base + (if p.preKeyId.isSome then 596#64 else 764#64) →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x24 = BitVec.zeroExtend 64 (optU32Tag p.preKeyId) →
      EncRawUpperSaved s0 sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((pendingOpenAt A ss g p ∗ vecU8At A v cap ptr (bs ++ [74#8]) ∗
          stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hcmn1 := cmn1_beq_zero_false hcap_g
  have hcmn2 := cap_beq_noneCap_false hcap_g
  have hbeq_cap := cap_beq_len_false hlt
  rw [hP, vecU8At_open_one A v cap ptr bs hlt]
  unfold pendingOpenAt
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPpLsCl.exists_elim fun old => ?_
  apply sepWPpLsCl_of_sepWP_vm
    (mid := (blkPl_14).base + (if p.preKeyId.isSome then 596#64 else 764#64))
  by_vm_steps
    wp_steps
    refine SepWP.done
      (by simp only [arm64_norm, optU32Tag_bne1_pc, *])
      (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm_end => ?_⟩
    refine SepWPpLsCl.weaken_pre ?_ (hnext _ hvm_end
      (by simp only [arm64_norm, optU32Tag_bne1_pc, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
    rw [← vecU8At_close_one A v cap ptr bs 74#8 hlt]
    unfold pendingOpenAt
    simp only [sepConj_assoc]
    exact entails_of_sep_focus (by sep_focus)

theorem step_tag9_len4_prealloc_placed_x [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) {H : LibsignalHooks}
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (bs : List (BitVec 8))
    (hspare : (bs.length + 1) + (encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)).length ≤ cap.toNat)
    (hlen_lt : bs.length + 12 < 2 ^ 61)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + (if p.timestamp == 0#64 then 800#64 else 708#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hx24 : s.readReg64 .x24 = BitVec.zeroExtend 64 (optU32Tag p.preKeyId))
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (optUint32Field 1 p.preKeyId).length)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 (bytesField 2 g.vec.bytes).length)
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 (int32Field 3 p.signedPreKeyId).length)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length)
    (hx22 : s.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId)
    (hx21 : s.readReg64 .x21 = p.timestamp)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (pendingOpenAt A.repAlloc ss g p ∗ vecU8At A.repAlloc v cap ptr (bs ++ [74#8]) ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_14).base + (if p.preKeyId.isSome then 824#64 else 872#64) →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length →
      sm.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId →
      sm.readReg64 .x21 = p.timestamp →
      EncRawUpperSaved s0 sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((pendingOpenAt A.repAlloc ss g p ∗
          vecU8At A.repAlloc v cap ptr
            (bs ++ [74#8] ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ∗
          stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hCallEV := @encraw_call_encodeVarint_prealloc_placed_x _ M A H
  rw [hP]
  by_cases hts : p.timestamp = 0#64
  · simp only [hts, beq_self_eq_true, ↓reduceIte] at hpc
    apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm_call => ?_⟩
      refine hCallEV sp0 (BitVec.ofNat 64 (encPendingMem g p).length) v cap ptr
        ((blkPl_14).base + 820#64) (bs ++ [74#8])
        (by simp only [List.length_append, List.length_singleton]; omega)
        (by simp only [List.length_append, List.length_singleton]; omega)
        (s0 := s0)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
        (by simp only [arm64_norm, ← encPendingMem_length_bv_ts_zero g p hts, *])
        (by simp only [arm64_norm, *]) (by sep_focus) ?_
      intro sm hvm1 hpcm hrunm hspm htrm hcsm
      have hx19m : sm.readReg64 .x19 = v := by
        have := hcsm.1; simp only [arm64_norm, *] at this; exact this
      have hx20m : sm.readReg64 .x20 = ss := by
        have := hcsm.2.1; simp only [arm64_norm, *] at this; exact this
      have hx21m : sm.readReg64 .x21 = p.timestamp := by
        have := hcsm.2.2.1; simp only [arm64_norm, *] at this; rw [hts]; exact this
      have hx22m : sm.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId := by
        have := hcsm.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx23m : sm.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length := by
        have := hcsm.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx24m : sm.readReg64 .x24 = BitVec.zeroExtend 64 (optU32Tag p.preKeyId) := by
        have := hcsm.2.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hcsm' : EncRawUpperSaved s0 sm :=
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
          (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
      cases hpk : p.preKeyId with
      | none =>
        simp only [hpk, optU32Tag] at hx24m
        apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 872#64)
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [wp_norm, arm64_norm], fun hvm_end => ?_⟩
          refine SepWPpLsCl.weaken_pre ?_ (hnext _ ((hvm_call.trans hvm1).trans hvm_end)
            (by simp only [arm64_norm, Bool.false_eq_true, ↓reduceIte, *])
            (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *])
            (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
          simp only [sepConj_assoc]
          exact entails_of_sep_focus (by sep_focus)
      | some pkId =>
        simp only [hpk, optU32Tag] at hx24m
        apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 824#64)
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [wp_norm, arm64_norm], fun hvm_end => ?_⟩
          refine SepWPpLsCl.weaken_pre ?_ (hnext _ ((hvm_call.trans hvm1).trans hvm_end)
            (by simp only [arm64_norm, ↓reduceIte, *])
            (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *])
            (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
          simp only [sepConj_assoc]
          exact entails_of_sep_focus (by sep_focus)
  · have hts_beq : (p.timestamp == 0#64) = false := bv64_beq_zero_false hts
    simp only [hts_beq, Bool.false_eq_true, ↓reduceIte] at hpc
    apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm_call => ?_⟩
      refine hCallEV sp0 (BitVec.ofNat 64 (encPendingMem g p).length) v cap ptr
        ((blkPl_14).base + 756#64) (bs ++ [74#8])
        (by simp only [List.length_append, List.length_singleton]; omega)
        (by simp only [List.length_append, List.length_singleton]; omega)
        (s0 := s0)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
        (by simp only [arm64_norm, ← uint64Field4_nonzero_length_bv hts, ← encPendingMem_length_bv g p, *])
        (by simp only [arm64_norm, *]) (by sep_focus) ?_
      intro sm hvm1 hpcm hrunm hspm htrm hcsm
      have hx19m : sm.readReg64 .x19 = v := by
        have := hcsm.1; simp only [arm64_norm, *] at this; exact this
      have hx20m : sm.readReg64 .x20 = ss := by
        have := hcsm.2.1; simp only [arm64_norm, *] at this; exact this
      have hx21m : sm.readReg64 .x21 = p.timestamp := by
        have := hcsm.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx22m : sm.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId := by
        have := hcsm.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx23m : sm.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length := by
        have := hcsm.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx24m : sm.readReg64 .x24 = BitVec.zeroExtend 64 (optU32Tag p.preKeyId) := by
        have := hcsm.2.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hcsm' : EncRawUpperSaved s0 sm :=
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
          (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
      cases hpk : p.preKeyId with
      | none =>
        simp only [hpk, optU32Tag] at hx24m
        apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 872#64)
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [wp_norm, arm64_norm], fun hvm_end => ?_⟩
          refine SepWPpLsCl.weaken_pre ?_ (hnext _ ((hvm_call.trans hvm1).trans hvm_end)
            (by simp only [arm64_norm, Bool.false_eq_true, ↓reduceIte, *])
            (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *])
            (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
          simp only [sepConj_assoc]
          exact entails_of_sep_focus (by sep_focus)
      | some pkId =>
        simp only [hpk, optU32Tag] at hx24m
        apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 824#64)
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [wp_norm, arm64_norm], fun hvm_end => ?_⟩
          refine SepWPpLsCl.weaken_pre ?_ (hnext _ ((hvm_call.trans hvm1).trans hvm_end)
            (by simp only [arm64_norm, ↓reduceIte, *])
            (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *])
            (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
          simp only [sepConj_assoc]
          exact entails_of_sep_focus (by sep_focus)

end Seg3a

/-! ## Subfields 1 and 2 (`pre_key_id`, `base_key`, `824/872 → 976`) -/

section Seg3bA

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  truncate32_signExtend64_er truncate32_zeroExtend64 bv_add_neg80_3b

theorem step_tag9_sub1_prealloc_placed_x [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) {H : LibsignalHooks}
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (bs : List (BitVec 8))
    (hspare : bs.length + (optUint32Field 1 p.preKeyId).length ≤ cap.toNat)
    (hlen_lt : bs.length + 12 < 2 ^ 60)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + (if p.preKeyId.isSome then 824#64 else 872#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length)
    (hx22 : s.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId)
    (hx21 : s.readReg64 .x21 = p.timestamp)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (pendingOpenAt A.repAlloc ss g p ∗ vecU8At A.repAlloc v cap ptr bs ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_14).base + 872#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length →
      sm.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId →
      sm.readReg64 .x21 = p.timestamp →
      EncRawUpperSaved s0 sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((pendingOpenAt A.repAlloc ss g p ∗
          vecU8At A.repAlloc v cap ptr (bs ++ optUint32Field 1 p.preKeyId) ∗
          stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  cases hpk : p.preKeyId with
  | none =>
    simp only [hpk, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc
    rw [hP]
    refine SepWPpLsCl.weaken_pre ?_
      (hnext s (VmPreserved.refl s) hpc hrun hsp htr hx19 hx20 hx23 hx22 hx21 hcs)
    simp only [hpk, optUint32Field1_none_eq, List.append_nil]
    exact entails_of_sep_focus (by sep_focus)
  | some pkId =>
    simp only [hpk, Option.isSome_some, ↓reduceIte] at hpc
    have hCallEV := @encraw_call_encodeVarint_prealloc_placed_x _ M A H
    have hpk_val : optU32ValAt (ss + 276#64) g.tail (some pkId) = ((ss + 276#64) ↦₃₂ pkId) :=
      optU32ValAt_some _ _ _
    have hflen : (optUint32Field 1 (some pkId)).length =
        1 + (encodeVarint (BitVec.zeroExtend 64 pkId)).length := by
      rw [← optUint32Field1_some_eq pkId]
      simp only [List.length_append, List.length_singleton]
    rw [hpk] at hspare
    have hlt : bs.length < cap.toNat := by omega
    have hbeq_cap := cap_beq_len_false hlt
    rw [hP, vecU8At_open_one A.repAlloc v cap ptr bs hlt]
    unfold pendingOpenAt
    rw [hpk, hpk_val]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPpLsCl.exists_elim fun old => ?_
    apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm0 => ?_⟩
      have hclose := vecU8At_close_one A.repAlloc v cap ptr bs 8#8 hlt
      refine SepWPpLsCl.weaken_pre (P' :=
          (vecU8At A.repAlloc v cap ptr (bs ++ [8#8]) ∗
            stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
            (pendingOpenAt A.repAlloc ss g p ∗ F))
        (by
          rw [← hclose]
          unfold pendingOpenAt
          rw [hpk, hpk_val]
          simp only [sepConj_assoc]
          exact entails_of_sep_focus (by sep_focus)) ?_
      refine hCallEV sp0 (BitVec.zeroExtend 64 pkId) v cap ptr ((blkPl_14).base + 872#64) (bs ++ [8#8])
        (by simp only [List.length_append, List.length_singleton]; omega)
        (by simp only [List.length_append, List.length_singleton]; omega)
        (s0 := s0) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
      · simp only [arm64_norm]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
      · simp only [arm64_norm, *]
      · simp only [arm64_norm]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm]
      · intro s1 hvm1 hpc1 hrun1 hsp1 htr1 hcs1
        have hx19_1 : s1.readReg64 .x19 = v := by
          have := hcs1.1; simp only [arm64_norm, *] at this; exact this
        have hx20_1 : s1.readReg64 .x20 = ss := by
          have := hcs1.2.1; simp only [arm64_norm, *] at this; exact this
        have hx21_1 : s1.readReg64 .x21 = p.timestamp := by
          have := hcs1.2.2.1; simp only [arm64_norm, *] at this; exact this
        have hx22_1 : s1.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId := by
          have := hcs1.2.2.2.1; simp only [arm64_norm, *] at this; exact this
        have hx23_1 : s1.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length := by
          have := hcs1.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
        have hcs_1 : EncRawUpperSaved s0 s1 :=
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
            (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
        refine SepWPpLsCl.weaken_pre ?_ (hnext s1 (hvm0.trans hvm1) hpc1 hrun1 hsp1 htr1
          hx19_1 hx20_1 hx23_1 hx22_1 hx21_1 hcs_1)
        rw [List.append_assoc, hpk, optUint32Field1_some_eq pkId]
        simp only [sepConj_assoc]
        exact entails_of_sep_focus (by sep_focus)

theorem step_tag9_sub2_a_prealloc_placed_x [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) {H : LibsignalHooks}
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (bs : List (BitVec 8))
    (hne_vec : g.vec.bytes ≠ []) (hlt_vec : g.vec.bytes.length < 2 ^ 63)
    (hspare : bs.length + ([18#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length)).length ≤ cap.toNat)
    (hlen_lt : bs.length + 12 < 2 ^ 60)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 872#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length)
    (hx22 : s.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId)
    (hx21 : s.readReg64 .x21 = p.timestamp)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (pendingOpenAt A.repAlloc ss g p ∗ vecU8At A.repAlloc v cap ptr bs ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_14).base + 928#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x24 = g.vec.ptr →
      sm.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length →
      sm.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId →
      sm.readReg64 .x21 = p.timestamp →
      EncRawUpperSaved s0 sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((pendingOpenAt A.repAlloc ss g p ∗
          vecU8At A.repAlloc v cap ptr (bs ++ ([18#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length))) ∗
          stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hCallEV := @encraw_call_encodeVarint_prealloc_placed_x _ M A H
  have hbeq0 := ofNat64_len_beq_zero_false hne_vec hlt_vec
  have hflen : ([18#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length)).length =
      1 + (encodeVarint (BitVec.ofNat 64 g.vec.bytes.length)).length := by
    simp only [List.length_append, List.length_singleton]
  have hlt : bs.length < cap.toNat := by omega
  have hbeq_cap := cap_beq_len_false hlt
  rw [hP, vecU8At_open_one A.repAlloc v cap ptr bs hlt]
  unfold pendingOpenAt
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPpLsCl.exists_elim fun old => ?_
  apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm0 => ?_⟩
    have hclose := vecU8At_close_one A.repAlloc v cap ptr bs 18#8 hlt
    refine SepWPpLsCl.weaken_pre (P' :=
        (vecU8At A.repAlloc v cap ptr (bs ++ [18#8]) ∗
          stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
          (pendingOpenAt A.repAlloc ss g p ∗ F))
      (by
        rw [← hclose]
        unfold pendingOpenAt
        simp only [sepConj_assoc]
        exact entails_of_sep_focus (by sep_focus)) ?_
    refine hCallEV sp0 (BitVec.ofNat 64 g.vec.bytes.length) v cap ptr ((blkPl_14).base + 928#64) (bs ++ [18#8])
      (by simp only [List.length_append, List.length_singleton]; omega)
      (by simp only [List.length_append, List.length_singleton]; omega)
      (s0 := s0) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
    · simp only [arm64_norm]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm]
    · intro s1 hvm1 hpc1 hrun1 hsp1 htr1 hcs1
      have hx19_1 : s1.readReg64 .x19 = v := by
        have := hcs1.1; simp only [arm64_norm, *] at this; exact this
      have hx20_1 : s1.readReg64 .x20 = ss := by
        have := hcs1.2.1; simp only [arm64_norm, *] at this; exact this
      have hx21_1 : s1.readReg64 .x21 = p.timestamp := by
        have := hcs1.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx22_1 : s1.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId := by
        have := hcs1.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx23_1 : s1.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length := by
        have := hcs1.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx24_1 : s1.readReg64 .x24 = g.vec.ptr := by
        have := hcs1.2.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hcs_1 : EncRawUpperSaved s0 s1 :=
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
          (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
      refine SepWPpLsCl.weaken_pre ?_ (hnext s1 (hvm0.trans hvm1) hpc1 hrun1 hsp1 htr1
        hx19_1 hx20_1 hx24_1 hx23_1 hx22_1 hx21_1 hcs_1)
      rw [List.append_assoc]
      simp only [sepConj_assoc]
      exact entails_of_sep_focus (by sep_focus)

theorem step_tag9_sub2_b_prealloc_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (ss v sp0 cap1 ptr1 : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (bs1 : List (BitVec 8))
    (hne_vec : g.vec.bytes ≠ [])
    (hroom : bs1.length + g.vec.bytes.length ≤ cap1.toNat)
    (hfit1 : bs1.length + g.vec.bytes.length < 2 ^ 60)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 928#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hx24 : s.readReg64 .x24 = g.vec.ptr)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length)
    (hx22 : s.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId)
    (hx21 : s.readReg64 .x21 = p.timestamp)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (pendingOpenAt A.repAlloc ss g p ∗ vecU8At A.repAlloc v cap1 ptr1 bs1 ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_14).base + 976#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId →
      sm.readReg64 .x21 = p.timestamp →
      EncRawUpperSaved s0 sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((pendingOpenAt A.repAlloc ss g p ∗ vecU8At A.repAlloc v cap1 ptr1 (bs1 ++ g.vec.bytes) ∗
          stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hCallMC := @encraw_call_memcpy_buf_prealloc_placed_x _ M A lim H hC
  rw [hP]
  refine sepWPpLsCl_extract_vecU8At_bounds (A := A.repAlloc) (v := v) (cap := cap1) (ptr := ptr1) (bs := bs1)
    (hfocus := by sep_focus) (h := fun _ hcap1 hptr1 => ?_)
  rw [vecU8At_eq_header_sep_buf A.repAlloc v cap1 ptr1 bs1]
  unfold pendingOpenAt
  simp only [vecHeader, sepConj_assoc]
  have hx2_nat : (BitVec.ofNat 64 g.vec.bytes.length).toNat = g.vec.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hhi := cmp_hi_false_of_le hroom hcap1
  apply sepWPpLsCl_of_sepWP_vm (mid := lsρ lsMemcpySym)
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm0 => ?_⟩
    refine hCallMC sp0 v cap1 ptr1 g.vec.ptr ((blkPl_14).base + 968#64) bs1 g.vec.bytes
      hroom hcap1 hptr1 hne_vec (s0 := s0)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
    · simp only [arm64_norm]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · intro sm hvm1 hpcm hrunm hspm htrm hcsm
      have hx19m : sm.readReg64 .x19 = v := by
        have := hcsm.1; simp only [arm64_norm, *] at this; exact this
      have hx20m : sm.readReg64 .x20 = ss := by
        have := hcsm.2.1; simp only [arm64_norm, *] at this; exact this
      have hx21m : sm.readReg64 .x21 = p.timestamp := by
        have := hcsm.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx22m : sm.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId := by
        have := hcsm.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx23m : sm.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length := by
        have := hcsm.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx25m : sm.readReg64 .x25 = BitVec.ofNat 64 bs1.length := by
        have := hcsm.2.2.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hcsm' : EncRawUpperSaved s0 sm :=
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
          (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
      apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 976#64)
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm], fun hvmm => ?_⟩
        refine SepWPpLsCl.weaken_pre ?_ (hnext _ ((hvm0.trans hvm1).trans hvmm)
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
        rw [← vecU8At_close_slice A.repAlloc v cap1 ptr1 bs1 g.vec.bytes hroom hcap1 hptr1 hne_vec]
        unfold pendingOpenAt
        simp only [sepConj_assoc]
        exact entails_of_sep_focus (by sep_focus)

end Seg3bA

/-! ## Subfields 3 and 4 and combined Tag 9 (`536 → 1080`) -/

section Seg3bB

set_option allowUnsafeReducibility true in
attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
  stackAt vecU8Buf vecSrcRest vecCopyDone optU32ValAt pendingTailRest

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  truncate32_signExtend64_er truncate32_zeroExtend64 bv_add_neg80_3b

theorem step_tag9_sub3_prealloc_placed_x [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) {H : LibsignalHooks}
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (bs : List (BitVec 8))
    (hspare : bs.length + (int32Field 3 p.signedPreKeyId).length ≤ cap.toNat)
    (hlen_lt : bs.length + 12 < 2 ^ 60)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 976#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hx22 : s.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId)
    (hx21 : s.readReg64 .x21 = p.timestamp)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (pendingOpenAt A.repAlloc ss g p ∗ vecU8At A.repAlloc v cap ptr bs ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_14).base + 1028#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x21 = p.timestamp →
      EncRawUpperSaved s0 sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((pendingOpenAt A.repAlloc ss g p ∗
          vecU8At A.repAlloc v cap ptr (bs ++ int32Field 3 p.signedPreKeyId) ∗
          stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hCallEV := @encraw_call_encodeVarint_prealloc_placed_x _ M A H
  rw [hP]
  by_cases hspk : p.signedPreKeyId = 0#32
  · simp only [sepConj_assoc]
    apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 1028#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm_end => ?_⟩
      refine SepWPpLsCl.weaken_pre ?_ (hnext _ hvm_end
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      simp only [hspk, int32Field3_zero_eq, List.append_nil, sepConj_assoc]
      exact entails_of_sep_focus (by sep_focus)
  · have hbeq0 := zext64_beq_zero_false_3b hspk
    have hflen : (int32Field 3 p.signedPreKeyId).length =
        1 + (encodeVarint (BitVec.signExtend 64 p.signedPreKeyId)).length := by
      rw [← int32Field3_nonzero_eq hspk]
      simp only [List.length_append, List.length_singleton]
    have hlt : bs.length < cap.toNat := by omega
    have hbeq_cap := cap_beq_len_false hlt
    rw [vecU8At_open_one A.repAlloc v cap ptr bs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPpLsCl.exists_elim fun old => ?_
    apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm0 => ?_⟩
      refine SepWPpLsCl.weaken_pre
        (P' := (vecU8At A.repAlloc v cap ptr (bs ++ [24#8]) ∗
            stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
          pendingOpenAt A.repAlloc ss g p ∗ F)
        (by
          rw [← vecU8At_close_one A.repAlloc v cap ptr bs 24#8 hlt]
          simp only [sepConj_assoc]
          exact entails_of_sep_focus (by sep_focus))
        (hCallEV sp0 (BitVec.signExtend 64 p.signedPreKeyId) v cap ptr ((blkPl_14).base + 1028#64)
          (bs ++ [24#8])
          (by simp only [List.length_append, List.length_singleton]; omega)
          (by simp only [List.length_append, List.length_singleton]; omega)
          (s0 := s0)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by sep_focus) ?_)
      intro s1 hvm1 hpc1 hrun1 hsp1 htr1 hcs1
      have hx19_1 : s1.readReg64 .x19 = v := by
        have := hcs1.1; simp only [arm64_norm, *] at this; exact this
      have hx20_1 : s1.readReg64 .x20 = ss := by
        have := hcs1.2.1; simp only [arm64_norm, *] at this; exact this
      have hx21_1 : s1.readReg64 .x21 = p.timestamp := by
        have := hcs1.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hcs_1 : EncRawUpperSaved s0 s1 :=
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
          (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
      refine SepWPpLsCl.weaken_pre ?_
        (hnext s1 (hvm0.trans hvm1) hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hcs_1)
      rw [List.append_assoc, int32Field3_nonzero_eq hspk]
      simp only [sepConj_assoc]
      exact entails_of_sep_focus (by sep_focus)

theorem step_tag9_sub4_prealloc_placed_x [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) {H : LibsignalHooks}
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (bs : List (BitVec 8))
    (hspare : bs.length + (uint64Field 4 p.timestamp).length ≤ cap.toNat)
    (hlen_lt : bs.length + 12 < 2 ^ 60)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 1028#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hx21 : s.readReg64 .x21 = p.timestamp)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (pendingOpenAt A.repAlloc ss g p ∗ vecU8At A.repAlloc v cap ptr bs ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_14).base + 1080#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((pendingOpenAt A.repAlloc ss g p ∗
          vecU8At A.repAlloc v cap ptr (bs ++ uint64Field 4 p.timestamp) ∗
          stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hCallEV := @encraw_call_encodeVarint_prealloc_placed_x _ M A H
  rw [hP]
  by_cases hts : p.timestamp = 0#64
  · simp only [sepConj_assoc]
    apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 1080#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm_end => ?_⟩
      refine SepWPpLsCl.weaken_pre ?_ (hnext _ hvm_end
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      simp only [hts, uint64Field4_zero_eq, List.append_nil, sepConj_assoc]
      exact entails_of_sep_focus (by sep_focus)
  · have hbeq0 := bv64_beq_zero_false hts
    have hfield_len : (uint64Field 4 p.timestamp).length =
        1 + (encodeVarint p.timestamp).length := by
      rw [← uint64Field4_nonzero_eq hts, List.length_append, List.length_singleton]
    have hlt : bs.length < cap.toNat := by omega
    have hbeq_cap := cap_beq_len_false hlt
    rw [vecU8At_open_one A.repAlloc v cap ptr bs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPpLsCl.exists_elim fun old => ?_
    apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm0 => ?_⟩
      have hclose := vecU8At_close_one A.repAlloc v cap ptr bs 32#8 hlt
      refine SepWPpLsCl.weaken_pre (P' :=
          (vecU8At A.repAlloc v cap ptr (bs ++ [32#8]) ∗
            stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
            (pendingOpenAt A.repAlloc ss g p ∗ F))
        (by
          rw [← hclose]
          exact entails_of_sep_focus (by sep_focus)) ?_
      refine hCallEV sp0 p.timestamp v cap ptr ((blkPl_14).base + 1080#64) (bs ++ [32#8])
        (by simp only [List.length_append, List.length_singleton]; omega)
        (by simp only [List.length_append, List.length_singleton]; omega)
        (s0 := s0)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by sep_focus) ?_
      intro s1 hvm1 hpc1 hrun1 hsp1 htr1 hcs1
      have hx19_1 : s1.readReg64 .x19 = v := by
        have := hcs1.1; simp only [arm64_norm, *] at this; exact this
      have hx20_1 : s1.readReg64 .x20 = ss := by
        have := hcs1.2.1; simp only [arm64_norm, *] at this; exact this
      have hcs_1 : EncRawUpperSaved s0 s1 :=
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
          (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
      refine SepWPpLsCl.weaken_pre ?_ (hnext s1 (hvm0.trans hvm1) hpc1 hrun1 hsp1 htr1
        hx19_1 hx20_1 hcs_1)
      rw [List.append_assoc, uint64Field4_nonzero_eq hts]
      exact entails_of_sep_focus (by sep_focus)

/-- Pre-reserved (`0`-allocation, `VmPreserved`) Tag 9 (`pending_pre_key`, offsets `536 → 1080`)
    of Block `14` (`encode_raw`). -/
theorem step_encraw_tag9_prealloc_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (ss v sp0 cap ptr : BitVec 64)
    (G_pending : Option TailVecGhost) (s_pending : Option PendingPreKey) (bs : List (BitVec 8))
    (hrel : PendingRel G_pending s_pending)
    (hbound : match G_pending with | none => True | some g => g.vec.bytes.length < 2 ^ 32)
    (hbs_lt : bs.length < 2 ^ 32)
    (hspare : bs.length + (encPendingFieldMem G_pending s_pending).length ≤ cap.toNat)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 536#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (optTailVecAt A.repAlloc 48 (ss + 248#64) G_pending ∗ vecU8At A.repAlloc v cap ptr bs ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_14).base + 1080#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((optTailVecAt A.repAlloc 48 (ss + 248#64) G_pending ∗
          vecU8At A.repAlloc v cap ptr (bs ++ encPendingFieldMem G_pending s_pending) ∗
          stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  cases G_pending with
  | none =>
    cases s_pending with
    | some p => exact False.elim hrel
    | none =>
      rw [hP, optTailVecAt_pending_none_eq]
      simp only [sepConj_assoc]
      apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 1080#64)
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm], fun hvm_end => ?_⟩
        refine SepWPpLsCl.weaken_pre ?_ (hnext _ hvm_end
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
        rw [optTailVecAt_pending_none_eq]
        simp only [encPendingFieldMem, List.append_nil, sepConj_assoc]
        exact entails_of_sep_focus (by sep_focus)
  | some g =>
    cases s_pending with
    | none => exact False.elim hrel
    | some p =>
      have hne_vec : g.vec.bytes ≠ [] := publicKey_deserialize_ne_nil hrel.1
      have hlt_vec31 : g.vec.bytes.length < 2 ^ 32 := hbound
      have hlt_vec63 : g.vec.bytes.length < 2 ^ 63 := by omega
      have hlen0_le := encodeVarint_length_le_10 (BitVec.ofNat 64 (encPendingMem g p).length)
      have hlen1_le := optUint32Field1_length_le p.preKeyId
      have hlen2_le := encodeVarint_length_le_10 (BitVec.ofNat 64 g.vec.bytes.length)
      have hlen3_le := int32Field3_length_le p.signedPreKeyId
      have hbytes_eq :
          ((((((bs ++ [74#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ++
            optUint32Field 1 p.preKeyId) ++
            ([18#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length))) ++ g.vec.bytes) ++
            int32Field 3 p.signedPreKeyId) ++ uint64Field 4 p.timestamp =
          bs ++ encPendingFieldMem (some g) (some p) := by
        rw [← lenField9_eq g p, ← bytesField2_nonempty_eq hne_vec]
        simp only [List.append_assoc]
      have htotal_spare :
          bs.length + 1 +
            (encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)).length +
            (optUint32Field 1 p.preKeyId).length +
            1 + (encodeVarint (BitVec.ofNat 64 g.vec.bytes.length)).length +
            g.vec.bytes.length +
            (int32Field 3 p.signedPreKeyId).length +
            (uint64Field 4 p.timestamp).length ≤ cap.toNat := by
        have hlen := congrArg List.length hbytes_eq
        simp only [List.length_append, List.length_singleton] at hlen
        omega
      rw [hP]
      refine sepWPpLsCl_extract_pending_some (A := A.repAlloc) (ss := ss) (g := g)
        (hfocus := by sep_focus) (h := fun hlen24 hle_g hcap_g _ => ?_)
      have hopen := optTailVecAt_pending_some_eq_open A.repAlloc ss g p hlen24 hle_g hrel
      rw [hopen]
      refine step_tag9_write_tag_prealloc_placed_x ss v sp0 cap ptr g p bs hcap_g (by omega)
        hpc hrun hsp htr hx19 hx20 hcs (by sep_focus) ?_
      intro s1 hvm01 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx24_1 hcs1
      refine step_tag9_len1_placed_x ss v sp0 g p hne_vec hlt_vec63
        hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx24_1 hcs1 (by sep_focus) ?_
      intro s2 hvm12 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx24_2 hx8_2 hx23_2 hcs2
      refine step_tag9_len2_placed_x ss v sp0 g p hne_vec
        hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx24_2 hx8_2 hx23_2 hcs2 (by sep_focus) ?_
      intro s3 hvm23 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx24_3 hx8_3 hx9_3 hx23_3 hx22_3 hcs3
      refine step_tag9_len3_placed_x ss v sp0 g p
        hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx24_3 hx8_3 hx9_3 hx23_3 hx22_3 hcs3 (by sep_focus) ?_
      intro s4 hvm34 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hx24_4 hx8_4 hx9_4 hx10_4 hx23_4 hx22_4 hx21_4 hcs4
      refine step_tag9_len4_prealloc_placed_x A ss v sp0 cap ptr g p bs
        (by omega) (by omega)
        hpc4 hrun4 hsp4 halign htr4 hx19_4 hx20_4 hx24_4 hx8_4 hx9_4 hx10_4 hx23_4 hx22_4 hx21_4 hcs4
        (by sep_focus) ?_
      intro s5 hvm45 hpc5 hrun5 hsp5 htr5 hx19_5 hx20_5 hx23_5 hx22_5 hx21_5 hcs5
      refine step_tag9_sub1_prealloc_placed_x A ss v sp0 cap ptr g p
        ((bs ++ [74#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length))
        (by simp only [List.length_append, List.length_singleton]; omega)
        (by simp only [List.length_append, List.length_singleton]; omega)
        hpc5 hrun5 hsp5 halign htr5 hx19_5 hx20_5 hx23_5 hx22_5 hx21_5 hcs5 (by sep_focus) ?_
      intro s6 hvm56 hpc6 hrun6 hsp6 htr6 hx19_6 hx20_6 hx23_6 hx22_6 hx21_6 hcs6
      refine step_tag9_sub2_a_prealloc_placed_x A ss v sp0 cap ptr g p
        (((bs ++ [74#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ++
          optUint32Field 1 p.preKeyId)
        hne_vec hlt_vec63
        (by simp only [List.length_append, List.length_singleton]; omega)
        (by simp only [List.length_append, List.length_singleton]; omega)
        hpc6 hrun6 hsp6 halign htr6 hx19_6 hx20_6 hx23_6 hx22_6 hx21_6 hcs6 (by sep_focus) ?_
      intro s7 hvm67 hpc7 hrun7 hsp7 htr7 hx19_7 hx20_7 hx24_7 hx23_7 hx22_7 hx21_7 hcs7
      refine step_tag9_sub2_b_prealloc_placed_x hC ss v sp0 cap ptr g p
        ((((bs ++ [74#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ++
          optUint32Field 1 p.preKeyId) ++
          ([18#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length)))
        hne_vec
        (by simp only [List.length_append, List.length_singleton]; omega)
        (by simp only [List.length_append, List.length_singleton]; omega)
        hpc7 hrun7 hsp7 halign htr7 hx19_7 hx20_7 hx24_7 hx23_7 hx22_7 hx21_7 hcs7 (by sep_focus) ?_
      intro s8 hvm78 hpc8 hrun8 hsp8 htr8 hx19_8 hx20_8 hx22_8 hx21_8 hcs8
      refine step_tag9_sub3_prealloc_placed_x A ss v sp0 cap ptr g p
        (((((bs ++ [74#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ++
          optUint32Field 1 p.preKeyId) ++
          ([18#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length))) ++ g.vec.bytes)
        (by simp only [List.length_append, List.length_singleton]; omega)
        (by simp only [List.length_append, List.length_singleton]; omega)
        hpc8 hrun8 hsp8 halign htr8 hx19_8 hx20_8 hx22_8 hx21_8 hcs8 (by sep_focus) ?_
      intro s9 hvm89 hpc9 hrun9 hsp9 htr9 hx19_9 hx20_9 hx21_9 hcs9
      refine step_tag9_sub4_prealloc_placed_x A ss v sp0 cap ptr g p
        ((((((bs ++ [74#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ++
          optUint32Field 1 p.preKeyId) ++
          ([18#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length))) ++ g.vec.bytes) ++
          int32Field 3 p.signedPreKeyId)
        (by simp only [List.length_append, List.length_singleton]; omega)
        (by simp only [List.length_append, List.length_singleton]; omega)
        hpc9 hrun9 hsp9 halign htr9 hx19_9 hx20_9 hx21_9 hcs9 (by sep_focus) ?_
      intro s10 hvm910 hpc10 hrun10 hsp10 htr10 hx19_10 hx20_10 hcs10
      have hvm_all : VmPreserved s s10 :=
        hvm01.trans (hvm12.trans (hvm23.trans (hvm34.trans (hvm45.trans
          (hvm56.trans (hvm67.trans (hvm78.trans (hvm89.trans hvm910))))))))
      refine SepWPpLsCl.weaken_pre ?_
        (hnext s10 hvm_all hpc10 hrun10 hsp10 htr10 hx19_10 hx20_10 hcs10)
      rw [← hopen, hbytes_eq]
      simp only [sepConj_assoc]
      exact entails_of_sep_focus (by sep_focus)

end Seg3bB

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.SparePendingPreKeyXPlacedBudget
