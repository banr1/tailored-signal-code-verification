/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.BaseBudget
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.PendingKyberPreKey
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.BaseXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.BaseX
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PendingKyberPreKeyXPlaced
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PendingKyberPreKeyXPlacedBudgetAux
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PqRatchetStateEpilogueX
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PqRatchetStateEpilogueXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.RegistrationIdsBaseKeyXPlaced
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.SpareBaseXBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBase
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.E2E.Record.Serialization.ChainLenAux.Pure
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.PendingPreKeyFields
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.RemoteIdentityRootKeyCounter
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.SenderReceiverChains
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PendingKyberPreKeyX
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PrologueVersionLocalIdentityX
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.RegistrationIdsBaseKeyX
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Pre-Reserved `SessionStructure::encode_raw` Tags 10, 11, 13–15, and Epilogue (`1080` → `1736`)

Proves zero-allocation (`VmPreserved`-preserving) relocatable step lemmas for protobuf tags 10
(`remote_registration_id`), 11 (`local_registration_id`), 13 (`alice_base_key`), 14
(`pending_kyber_pre_key`), and 15 (`pq_ratchet_state`), together with the epilogue (`1080..1736`) of
Block `14` when the output buffer has spare capacity.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.SpareTailTagsXPlacedBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSessionApi (PendingKyberPreKey)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks lsmpl lsMemcpySym lsρ
)
open CryptoVerification.RustHeap (vecHeader vecU8At)
open CryptoVerification.LibsignalTripleRatchetRepr (TailVecGhost optTailVecAt)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  vecU8Buf vecU8At_eq_header_sep_buf cap_beq_len_false
  ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
)
open CryptoVerification.E2E.Record (
  uint32Field bytesField msgField encPendingKyber KyberRel
)
open CryptoVerification.E2E.Record.Placed (blkPl_14 lsProg_14)
open CryptoVerification.E2E.Record.Serialization (
  encodeRawSubStackX sepWPpLsCl_extract_vecU8At_bounds
  bv_add_neg80_4a bv_add_neg80_4c
)
open CryptoVerification.E2E.Record.Serialization.EncodeRawAux (
  entails_of_sep_focus EncRawUpperSaved sp_sub_80_spAligned
  bv32_beq_zero_false ofNat64_len_beq_zero_false
  uint32Field_zero uint32Field_ne_zero bytesField_nil bytesField_ne_nil
  vecSrcRest vecCopyDone encodeVarint_length_le_10
  vecU8At_open_src vecU8At_close_slice vecU8At_open_one vecU8At_close_one
  vecU8At_open_src_off' vecU8At_Nil_off' cmp_hi_false_of_le
  kyberTailRest kyberOpenAt optTailVecAt_kyber_none_eq optTailVecAt_kyber_some_eq_open
  uint32Field1_length_le uint32Field1_zero_eq_er uint32Field1_nonzero_eq_er
  msgField14_some_eq bv_add_neg80_4b
  encPendingKyber_length_bv encPendingKyber_length_bv_ct_nil
  truncate32_signExtend64_er bytesField2_nonempty_length_bv er_truncate32_zext64_lsr6
  erHwVarintLen_eq_encodeVarint_length erHwVarintLen_bvShift_eq_encodeVarint_length
  zext64_beq_zero_false_3b cmn1_beq_zero_false cap_beq_noneCap_false
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

abbrev sepWPpLsCl_extract_kyber_some :=
  @CryptoVerification.E2E.Record.Serialization.sepWPpLsCl_extract_kyber_some
abbrev step_tag14_len1_placed_x :=
  @PendingKyberPreKeyXPlacedBudgetAux.step_tag14_len1_placed_x
abbrev step_encraw_epilogue_placed_x :=
  @PqRatchetStateEpilogueXBudget.step_encraw_epilogue_placed_x

/-! ## Tags 10, 11, and 13 (`1080..1292`) -/

section Seg4a

set_option allowUnsafeReducibility true in
attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
  stackAt vecU8Buf vecSrcRest vecCopyDone Program.fnOff

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_add_neg80_4a

theorem step_encraw_tag10_prealloc_placed_x [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) {H : LibsignalHooks}
    (ss v sp0 cap ptr : BitVec 64) (remReg : BitVec 32) (bs : List (BitVec 8))
    (hspare : bs.length + (uint32Field 10 remReg).length ≤ cap.toNat)
    (hlen_lt : bs.length + (uint32Field 10 remReg).length < 2 ^ 32)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 1080#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (((ss + 336#64) ↦₃₂ remReg) ∗ vecU8At A.repAlloc v cap ptr bs ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_14).base + 1132#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((((ss + 336#64) ↦₃₂ remReg) ∗ vecU8At A.repAlloc v cap ptr (bs ++ uint32Field 10 remReg) ∗
          stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hCallEV := @encraw_call_encodeVarint_prealloc_placed_x _ M A H
  rw [hP]
  by_cases hver : remReg = 0#32
  · subst hver
    simp only [sepConj_assoc]
    apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 1132#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvmm => ?_⟩
      refine SepWPpLsCl.weaken_pre ?_ (hnext _ hvmm
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      simp only [uint32Field_zero, List.append_nil, sepConj_assoc]
      exact entails_of_sep_focus (by sep_focus)
  · have hver_beq : (remReg == 0#32) = false := bv32_beq_zero_false hver
    have hfield_eq : bs ++ uint32Field 10 remReg =
        (bs ++ [80#8]) ++ encodeVarint (BitVec.zeroExtend 64 remReg) := by
      rw [uint32Field_ne_zero (k := 80#8) hver, List.append_assoc]
    have hfield_len : (uint32Field 10 remReg).length =
        1 + (encodeVarint (BitVec.zeroExtend 64 remReg)).length := by
      rw [uint32Field_ne_zero (k := 80#8) hver, List.length_append, List.length_singleton]
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
      have hclose := vecU8At_close_one A.repAlloc v cap ptr bs 80#8 hlt
      refine SepWPpLsCl.weaken_pre (P' :=
          (vecU8At A.repAlloc v cap ptr (bs ++ [80#8]) ∗
            stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ (((ss + 336#64) ↦₃₂ remReg) ∗ F))
        (by rw [← hclose]; simp only [sepConj_assoc]; exact entails_of_sep_focus (by sep_focus)) ?_
      refine hCallEV sp0 (BitVec.zeroExtend 64 remReg) v cap ptr ((blkPl_14).base + 1132#64)
        (bs ++ [80#8])
        (by simp only [List.length_append, List.length_singleton]; omega)
        (by simp only [List.length_append, List.length_singleton]; omega)
        (s0 := s0)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by sep_focus) ?_
      intro sm hvm1 hpcm hrunm hspm htrm hcsm
      have hx19m : sm.readReg64 .x19 = v := by
        have := hcsm.1; simp only [arm64_norm, *] at this; exact this
      have hx20m : sm.readReg64 .x20 = ss := by
        have := hcsm.2.1; simp only [arm64_norm, *] at this; exact this
      have hcsm' : EncRawUpperSaved s0 sm :=
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
          (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
      rw [← hfield_eq]
      refine SepWPpLsCl.weaken_pre ?_ (hnext sm (hvm0.trans hvm1) hpcm hrunm hspm htrm hx19m hx20m hcsm')
      exact entails_of_sep_focus (by sep_focus)

theorem step_encraw_tag11_prealloc_placed_x [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) {H : LibsignalHooks}
    (ss v sp0 cap ptr : BitVec 64) (locReg : BitVec 32) (bs : List (BitVec 8))
    (hspare : bs.length + (uint32Field 11 locReg).length ≤ cap.toNat)
    (hlen_lt : bs.length + (uint32Field 11 locReg).length < 2 ^ 32)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 1132#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (((ss + 340#64) ↦₃₂ locReg) ∗ vecU8At A.repAlloc v cap ptr bs ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_14).base + 1184#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((((ss + 340#64) ↦₃₂ locReg) ∗ vecU8At A.repAlloc v cap ptr (bs ++ uint32Field 11 locReg) ∗
          stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hCallEV := @encraw_call_encodeVarint_prealloc_placed_x _ M A H
  rw [hP]
  by_cases hver : locReg = 0#32
  · subst hver
    simp only [sepConj_assoc]
    apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 1184#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvmm => ?_⟩
      refine SepWPpLsCl.weaken_pre ?_ (hnext _ hvmm
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      simp only [uint32Field_zero, List.append_nil, sepConj_assoc]
      exact entails_of_sep_focus (by sep_focus)
  · have hver_beq : (locReg == 0#32) = false := bv32_beq_zero_false hver
    have hfield_eq : bs ++ uint32Field 11 locReg =
        (bs ++ [88#8]) ++ encodeVarint (BitVec.zeroExtend 64 locReg) := by
      rw [uint32Field_ne_zero (k := 88#8) hver, List.append_assoc]
    have hfield_len : (uint32Field 11 locReg).length =
        1 + (encodeVarint (BitVec.zeroExtend 64 locReg)).length := by
      rw [uint32Field_ne_zero (k := 88#8) hver, List.length_append, List.length_singleton]
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
      have hclose := vecU8At_close_one A.repAlloc v cap ptr bs 88#8 hlt
      refine SepWPpLsCl.weaken_pre (P' :=
          (vecU8At A.repAlloc v cap ptr (bs ++ [88#8]) ∗
            stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ (((ss + 340#64) ↦₃₂ locReg) ∗ F))
        (by rw [← hclose]; simp only [sepConj_assoc]; exact entails_of_sep_focus (by sep_focus)) ?_
      refine hCallEV sp0 (BitVec.zeroExtend 64 locReg) v cap ptr ((blkPl_14).base + 1184#64)
        (bs ++ [88#8])
        (by simp only [List.length_append, List.length_singleton]; omega)
        (by simp only [List.length_append, List.length_singleton]; omega)
        (s0 := s0)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by sep_focus) ?_
      intro sm hvm1 hpcm hrunm hspm htrm hcsm
      have hx19m : sm.readReg64 .x19 = v := by
        have := hcsm.1; simp only [arm64_norm, *] at this; exact this
      have hx20m : sm.readReg64 .x20 = ss := by
        have := hcsm.2.1; simp only [arm64_norm, *] at this; exact this
      have hcsm' : EncRawUpperSaved s0 sm :=
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
          (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
      rw [← hfield_eq]
      refine SepWPpLsCl.weaken_pre ?_ (hnext sm (hvm0.trans hvm1) hpcm hrunm hspm htrm hx19m hx20m hcsm')
      exact entails_of_sep_focus (by sep_focus)

theorem step_encraw_tag13_b_prealloc_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (ss v sp0 fCap fPtr cap1 ptr1 : BitVec 64) (bs1 fBs : List (BitVec 8))
    (hf_nil : fBs ≠ []) (hf_le : fBs.length ≤ fCap.toNat) (hf_cap : fCap.toNat < 2 ^ 63)
    (hspare : bs1.length + fBs.length ≤ cap1.toNat)
    (_hlen_lt : bs1.length + fBs.length < 2 ^ 61)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 1244#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 fBs.length)
    (hx22 : s.readReg64 .x22 = fPtr)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (vecU8At A.repAlloc (ss + 96#64) fCap fPtr fBs ∗ vecU8At A.repAlloc v cap1 ptr1 bs1 ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_14).base + 1292#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((vecU8At A.repAlloc (ss + 96#64) fCap fPtr fBs ∗
          vecU8At A.repAlloc v cap1 ptr1 (bs1 ++ fBs) ∗
          stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hCallMC := @encraw_call_memcpy_buf_prealloc_placed_x _ M A lim H hC
  rw [hP]
  refine sepWPpLsCl_extract_vecU8At_bounds (A := A.repAlloc) (v := v) (cap := cap1) (ptr := ptr1) (bs := bs1)
    (hfocus := by sep_focus) (h := fun _ hcap1 hptr1 => ?_)
  have hf_nat : (BitVec.ofNat 64 fBs.length).toNat = fBs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hbs1_nat : (BitVec.ofNat 64 bs1.length).toNat = bs1.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [vecU8At_open_src A.repAlloc (ss + 96#64) fCap fPtr fBs hf_nil hf_le,
      vecU8At_eq_header_sep_buf A.repAlloc v cap1 ptr1 bs1]
  simp only [vecHeader, sepConj_assoc]
  have hhi := cmp_hi_false_of_le hspare hcap1
  apply sepWPpLsCl_of_sepWP_vm (mid := lsρ lsMemcpySym)
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm0 => ?_⟩
    refine hCallMC sp0 v cap1 ptr1 fPtr ((blkPl_14).base + 1284#64) bs1 fBs
      hspare hcap1 hptr1 hf_nil (s0 := s0)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by sep_focus) ?_
    intro sm hvm1 hpcm hrunm hspm htrm hcsm
    have hx19m : sm.readReg64 .x19 = v := by
      have := hcsm.1; simp only [arm64_norm, *] at this; exact this
    have hx20m : sm.readReg64 .x20 = ss := by
      have := hcsm.2.1; simp only [arm64_norm, *] at this; exact this
    have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 fBs.length := by
      have := hcsm.2.2.1; simp only [arm64_norm, *] at this; exact this
    have hx23m : sm.readReg64 .x23 = BitVec.ofNat 64 bs1.length := by
      have := hcsm.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
    have hspm' : sm.sp = sp0 - 80#64 := hspm
    have hcsm' : EncRawUpperSaved s0 sm :=
      (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
        (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
    apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 1292#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvmm' => ?_⟩
      refine SepWPpLsCl.weaken_pre ?_ (hnext _ (hvm0.trans (hvm1.trans hvmm'))
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      rw [vecU8At_open_src A.repAlloc (ss + 96#64) fCap fPtr fBs hf_nil hf_le,
          ← vecU8At_close_slice A.repAlloc v cap1 ptr1 bs1 fBs hspare hcap1 hptr1 hf_nil]
      simp only [sepConj_assoc]
      exact entails_of_sep_focus (by sep_focus)

theorem step_encraw_tag13_prealloc_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (ss v sp0 fCap fPtr cap ptr : BitVec 64) (bs fBs : List (BitVec 8))
    (hspare : bs.length + (bytesField 13 fBs).length ≤ cap.toNat)
    (hlen_lt : bs.length + (bytesField 13 fBs).length < 2 ^ 32)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 1184#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (vecU8At A.repAlloc (ss + 96#64) fCap fPtr fBs ∗ vecU8At A.repAlloc v cap ptr bs ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_14).base + 1292#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((vecU8At A.repAlloc (ss + 96#64) fCap fPtr fBs ∗
          vecU8At A.repAlloc v cap ptr (bs ++ bytesField 13 fBs) ∗
          stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hCallEV := @encraw_call_encodeVarint_prealloc_placed_x _ M A H
  have hStepB := @step_encraw_tag13_b_prealloc_placed_x _ M A lim H hC
  rw [hP]
  refine sepWPpLsCl_extract_vecU8At_bounds (A := A.repAlloc) (v := ss + 96#64) (cap := fCap) (ptr := fPtr) (bs := fBs)
    (hfocus := by sep_focus) (h := fun hf_le hf_cap _ => ?_)
  by_cases hf_nil : fBs = []
  · subst hf_nil
    rw [vecU8At_Nil_off' A.repAlloc ss 96#64 104#64 112#64 fCap fPtr]
    simp only [sepConj_assoc]
    apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 1292#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvmm => ?_⟩
      refine SepWPpLsCl.weaken_pre ?_ (hnext _ hvmm
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      rw [vecU8At_Nil_off' A.repAlloc ss 96#64 104#64 112#64 fCap fPtr]
      simp only [bytesField_nil, List.append_nil, sepConj_assoc]
      exact entails_of_sep_focus (by sep_focus)
  · have hfield_eq : bs ++ bytesField 13 fBs =
        ((bs ++ [106#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) ++ fBs := by
      rw [bytesField_ne_nil (k := 106#8) hf_nil]; simp only [List.append_assoc]
    have hfield_len : (bytesField 13 fBs).length =
        (1 + (encodeVarint (BitVec.ofNat 64 fBs.length)).length) + fBs.length := by
      rw [bytesField_ne_nil (k := 106#8) hf_nil]
      simp only [List.length_append, List.length_singleton]
    have hf_beq : (BitVec.ofNat 64 fBs.length == 0#64) = false :=
      ofNat64_len_beq_zero_false hf_nil (by omega)
    have h10 := encodeVarint_length_le_10 (BitVec.ofNat 64 fBs.length)
    have hlt : bs.length < cap.toNat := by omega
    have hbeq_cap := cap_beq_len_false hlt
    rw [vecU8At_open_src_off' A.repAlloc ss 96#64 104#64 112#64 fCap fPtr fBs hf_nil hf_le,
        vecU8At_open_one A.repAlloc v cap ptr bs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPpLsCl.exists_elim fun old => ?_
    apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm0 => ?_⟩
      have hclose_one := vecU8At_close_one A.repAlloc v cap ptr bs 106#8 hlt
      refine SepWPpLsCl.weaken_pre (P' :=
          (vecU8At A.repAlloc v cap ptr (bs ++ [106#8]) ∗
            stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
            (vecU8At A.repAlloc (ss + 96#64) fCap fPtr fBs ∗ F))
        (by
          rw [← hclose_one, vecU8At_open_src_off' A.repAlloc ss 96#64 104#64 112#64 fCap fPtr fBs hf_nil hf_le]
          simp only [sepConj_assoc]
          exact entails_of_sep_focus (by sep_focus)) ?_
      refine hCallEV sp0 (BitVec.ofNat 64 fBs.length) v cap ptr ((blkPl_14).base + 1244#64)
        (bs ++ [106#8])
        (by simp only [List.length_append, List.length_singleton]; omega)
        (by simp only [List.length_append, List.length_singleton]; omega)
        (s0 := s0)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by sep_focus) ?_
      intro s1 hvm1 hpc1 hrun1 hsp1 htr1 hcs1
      have hx19_1 : s1.readReg64 .x19 = v := by
        have := hcs1.1; simp only [arm64_norm, *] at this; exact this
      have hx20_1 : s1.readReg64 .x20 = ss := by
        have := hcs1.2.1; simp only [arm64_norm, *] at this; exact this
      have hx21_1 : s1.readReg64 .x21 = BitVec.ofNat 64 fBs.length := by
        have := hcs1.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx22_1 : s1.readReg64 .x22 = fPtr := by
        have := hcs1.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hcs_1 : EncRawUpperSaved s0 s1 :=
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
          (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
      refine hStepB ss v sp0 fCap fPtr cap ptr
        ((bs ++ [106#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) fBs
        hf_nil hf_le hf_cap
        (by simp only [List.length_append, List.length_singleton]; omega)
        (by simp only [List.length_append, List.length_singleton]; omega)
        hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1 hx21_1 hx22_1 hcs_1 (by sep_focus) ?_
      intro sm hvm2 hpcm hrunm hspm htrm hx19m hx20m hcsm'
      rw [← hfield_eq]
      refine SepWPpLsCl.weaken_pre ?_
        (hnext sm (hvm0.trans (hvm1.trans hvm2)) hpcm hrunm hspm htrm hx19m hx20m hcsm')
      exact entails_of_sep_focus (by sep_focus)

end Seg4a

/-! ## Tag 14: `pending_kyber_pre_key` (`1292..1608`) -/

section Seg4b

set_option allowUnsafeReducibility true in
attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
  stackAt vecU8Buf vecSrcRest vecCopyDone kyberTailRest

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  truncate32_signExtend64_er truncate32_zeroExtend64
  ofNat_countLeadingZeros_64
  ofNat_countLeadingZeros_32
  CryptoVerification.LibsignalTripleRatchet.Prost.truncate32_ofNat64
  er_truncate32_zext64_lsr6
  erHwVarintLen_eq_encodeVarint_length
  erHwVarintLen_bvShift_eq_encodeVarint_length
  bv_add_neg80_4b

theorem step_tag14_write_tag_prealloc_placed_x [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) {H : LibsignalHooks}
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (k : PendingKyberPreKey)
    (bs : List (BitVec 8))
    (hcap_g : g.vec.cap.toNat < 2 ^ 63)
    (hspare : bs.length + 1 ≤ cap.toNat)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 1292#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (kyberOpenAt A.repAlloc ss g k ∗ vecU8At A.repAlloc v cap ptr bs ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_14).base + 1348#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x22 = BitVec.zeroExtend 64 k.preKeyId →
      sm.readReg64 .x21 = BitVec.ofNat 64 k.ciphertext.length →
      EncRawUpperSaved s0 sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((kyberOpenAt A.repAlloc ss g k ∗ vecU8At A.repAlloc v cap ptr (bs ++ [114#8]) ∗
          stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have h8 : (ss + 296#64) + 8#64 = ss + 304#64 := BitVec.add_assoc ss 296#64 8#64
  have h16 : (ss + 296#64) + 16#64 = ss + 312#64 := BitVec.add_assoc ss 296#64 16#64
  rw [hP]
  have hcmn1 := cmn1_beq_zero_false hcap_g
  have hcmn2 := cap_beq_noneCap_false hcap_g
  have hlt : bs.length < cap.toNat := by omega
  have hbeq_cap := cap_beq_len_false hlt
  rw [vecU8At_open_one A.repAlloc v cap ptr bs hlt]
  unfold kyberOpenAt
  rw [vecU8At_eq_header_sep_buf A.repAlloc (ss + 296#64) g.vec.cap g.vec.ptr k.ciphertext]
  simp only [vecHeader, h8, h16, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPpLsCl.exists_elim fun old => ?_
  apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 1348#64)
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm0 => ?_⟩
    refine SepWPpLsCl.weaken_pre ?_ (hnext _ hvm0
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
    rw [← vecU8At_close_one A.repAlloc v cap ptr bs 114#8 hlt]
    unfold kyberOpenAt
    rw [vecU8At_eq_header_sep_buf A.repAlloc (ss + 296#64) g.vec.cap g.vec.ptr k.ciphertext]
    simp only [vecHeader, h8, h16, sepConj_assoc]
    exact entails_of_sep_focus (by sep_focus)

theorem step_tag14_len2_prealloc_placed_x [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) {H : LibsignalHooks}
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (k : PendingKyberPreKey)
    (bs : List (BitVec 8))
    (hspare : (bs.length + 1) + (encodeVarint (BitVec.ofNat 64 (encPendingKyber k).length)).length ≤ cap.toNat)
    (hlen_lt : bs.length + 12 < 2 ^ 60)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base +
      (if k.ciphertext.isEmpty then 1440#64 else 1384#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (uint32Field 1 k.preKeyId).length)
    (hx22 : s.readReg64 .x22 = BitVec.zeroExtend 64 k.preKeyId)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 k.ciphertext.length)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (kyberOpenAt A.repAlloc ss g k ∗ vecU8At A.repAlloc v cap ptr (bs ++ [114#8]) ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_14).base +
        (if k.preKeyId == 0#32 then 1504#64 else 1456#64) →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x22 = BitVec.zeroExtend 64 k.preKeyId →
      sm.readReg64 .x21 = BitVec.ofNat 64 k.ciphertext.length →
      EncRawUpperSaved s0 sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((kyberOpenAt A.repAlloc ss g k ∗
          vecU8At A.repAlloc v cap ptr
            ((bs ++ [114#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingKyber k).length)) ∗
          stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hCallEV := @encraw_call_encodeVarint_prealloc_placed_x _ M A H
  rw [hP]
  by_cases hct : k.ciphertext = []
  · have hempty : k.ciphertext.isEmpty = true := List.isEmpty_iff.mpr hct
    simp only [hempty, ↓reduceIte] at hpc
    apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm0 => ?_⟩
      refine hCallEV sp0 (BitVec.ofNat 64 (encPendingKyber k).length) v cap ptr
        ((blkPl_14).base + 1452#64) (bs ++ [114#8])
        (by simp only [List.length_append, List.length_singleton]; omega)
        (by simp only [List.length_append, List.length_singleton]; omega)
        (s0 := s0)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
        (by simp only [arm64_norm, ← encPendingKyber_length_bv_ct_nil k hct, *])
        (by simp only [arm64_norm, *]) (by sep_focus) ?_
      intro s1 hvm1 hpc1 hrun1 hsp1 htr1 hcs1
      have hx19_1 : s1.readReg64 .x19 = v := by
        have := hcs1.1; simp only [arm64_norm, hx19] at this; exact this
      have hx20_1 : s1.readReg64 .x20 = ss := by
        have := hcs1.2.1; simp only [arm64_norm, hx20] at this; exact this
      have hx21_1 : s1.readReg64 .x21 = BitVec.ofNat 64 k.ciphertext.length := by
        have := hcs1.2.2.1; simp only [arm64_norm, hx21] at this; exact this
      have hx22_1 : s1.readReg64 .x22 = BitVec.zeroExtend 64 k.preKeyId := by
        have := hcs1.2.2.2.1; simp only [arm64_norm, hx22] at this; exact this
      have hcs_1 : EncRawUpperSaved s0 s1 :=
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
          (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
      by_cases hpk : k.preKeyId = 0#32
      · have hpk_beq : (k.preKeyId == 0#32) = true := beq_iff_eq.mpr hpk
        apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 1504#64)
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [wp_norm, arm64_norm], fun hvm2 => ?_⟩
          refine SepWPpLsCl.weaken_pre ?_ (hnext _ (hvm0.trans (hvm1.trans hvm2))
            (by simp only [arm64_norm, ↓reduceIte, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
          exact entails_of_sep_focus (by sep_focus)
      · have hpk_beq : (k.preKeyId == 0#32) = false := beq_false_of_ne hpk
        have hbeq0 := zext64_beq_zero_false_3b hpk
        apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 1456#64)
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [wp_norm, arm64_norm], fun hvm2 => ?_⟩
          refine SepWPpLsCl.weaken_pre ?_ (hnext _ (hvm0.trans (hvm1.trans hvm2))
            (by simp only [arm64_norm, Bool.false_eq_true, ↓reduceIte, *])
            (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
          exact entails_of_sep_focus (by sep_focus)
  · have hempty : k.ciphertext.isEmpty = false := List.isEmpty_eq_false_iff.mpr hct
    simp only [hempty, Bool.false_eq_true, ↓reduceIte] at hpc
    apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm0 => ?_⟩
      refine hCallEV sp0 (BitVec.ofNat 64 (encPendingKyber k).length) v cap ptr
        ((blkPl_14).base + 1424#64) (bs ++ [114#8])
        (by simp only [List.length_append, List.length_singleton]; omega)
        (by simp only [List.length_append, List.length_singleton]; omega)
        (s0 := s0)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
        (by simp only [arm64_norm, ← encPendingKyber_length_bv k, ← bytesField2_nonempty_length_bv hct, *])
        (by simp only [arm64_norm, *]) (by sep_focus) ?_
      intro s1 hvm1 hpc1 hrun1 hsp1 htr1 hcs1
      have hx19_1 : s1.readReg64 .x19 = v := by
        have := hcs1.1; simp only [arm64_norm, *] at this; exact this
      have hx20_1 : s1.readReg64 .x20 = ss := by
        have := hcs1.2.1; simp only [arm64_norm, *] at this; exact this
      have hx21_1 : s1.readReg64 .x21 = BitVec.ofNat 64 k.ciphertext.length := by
        have := hcs1.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx22_1 : s1.readReg64 .x22 = BitVec.zeroExtend 64 k.preKeyId := by
        have := hcs1.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hcs_1 : EncRawUpperSaved s0 s1 :=
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
          (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
      by_cases hpk : k.preKeyId = 0#32
      · have hpk_beq : (k.preKeyId == 0#32) = true := beq_iff_eq.mpr hpk
        apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 1504#64)
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [wp_norm, arm64_norm], fun hvm2 => ?_⟩
          refine SepWPpLsCl.weaken_pre ?_ (hnext _ (hvm0.trans (hvm1.trans hvm2))
            (by simp only [arm64_norm, ↓reduceIte, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
          exact entails_of_sep_focus (by sep_focus)
      · have hpk_beq : (k.preKeyId == 0#32) = false := beq_false_of_ne hpk
        have hbeq0 := zext64_beq_zero_false_3b hpk
        apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 1456#64)
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [wp_norm, arm64_norm], fun hvm2 => ?_⟩
          refine SepWPpLsCl.weaken_pre ?_ (hnext _ (hvm0.trans (hvm1.trans hvm2))
            (by simp only [arm64_norm, Bool.false_eq_true, ↓reduceIte, *])
            (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
          exact entails_of_sep_focus (by sep_focus)

theorem step_tag14_sub1_prealloc_placed_x [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) {H : LibsignalHooks}
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (k : PendingKyberPreKey)
    (bs : List (BitVec 8))
    (hspare : bs.length + (uint32Field 1 k.preKeyId).length ≤ cap.toNat)
    (hlen_lt : bs.length + 12 < 2 ^ 60)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base +
      (if k.preKeyId == 0#32 then 1504#64 else 1456#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hx22 : s.readReg64 .x22 = BitVec.zeroExtend 64 k.preKeyId)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 k.ciphertext.length)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (kyberOpenAt A.repAlloc ss g k ∗ vecU8At A.repAlloc v cap ptr bs ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_14).base + 1504#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x21 = BitVec.ofNat 64 k.ciphertext.length →
      EncRawUpperSaved s0 sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((kyberOpenAt A.repAlloc ss g k ∗
          vecU8At A.repAlloc v cap ptr (bs ++ uint32Field 1 k.preKeyId) ∗
          stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  by_cases hpk : k.preKeyId = 0#32
  · simp only [hpk, beq_self_eq_true, ↓reduceIte] at hpc
    rw [hP]
    refine SepWPpLsCl.weaken_pre ?_
      (hnext s (VmPreserved.refl s) hpc hrun hsp htr hx19 hx20 hx21 hcs)
    simp only [hpk, uint32Field1_zero_eq_er, List.append_nil]
    exact entails_of_sep_focus (by sep_focus)
  · have hpk_beq : (k.preKeyId == 0#32) = false := beq_false_of_ne hpk
    simp only [hpk_beq, Bool.false_eq_true, ↓reduceIte] at hpc
    have hCallEV := @encraw_call_encodeVarint_prealloc_placed_x _ M A H
    have hflen : (uint32Field 1 k.preKeyId).length =
        1 + (encodeVarint (BitVec.zeroExtend 64 k.preKeyId)).length := by
      rw [← uint32Field1_nonzero_eq_er hpk]
      simp only [List.length_append, List.length_singleton]
    have hlt : bs.length < cap.toNat := by omega
    have hbeq_cap := cap_beq_len_false hlt
    rw [hP, vecU8At_open_one A.repAlloc v cap ptr bs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPpLsCl.exists_elim fun old => ?_
    apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm0 => ?_⟩
      refine SepWPpLsCl.weaken_pre
        (P' := (vecU8At A.repAlloc v cap ptr (bs ++ [8#8]) ∗
            stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
          kyberOpenAt A.repAlloc ss g k ∗ F)
        (by
          rw [← vecU8At_close_one A.repAlloc v cap ptr bs 8#8 hlt]
          simp only [sepConj_assoc]
          exact entails_of_sep_focus (by sep_focus))
        (hCallEV sp0 (BitVec.zeroExtend 64 k.preKeyId) v cap ptr ((blkPl_14).base + 1504#64)
          (bs ++ [8#8])
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
      have hx21_1 : s1.readReg64 .x21 = BitVec.ofNat 64 k.ciphertext.length := by
        have := hcs1.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hcs_1 : EncRawUpperSaved s0 s1 :=
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
          (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
      refine SepWPpLsCl.weaken_pre ?_
        (hnext s1 (hvm0.trans hvm1) hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hcs_1)
      rw [List.append_assoc, uint32Field1_nonzero_eq_er hpk]
      exact entails_of_sep_focus (by sep_focus)

theorem step_tag14_sub2_b_prealloc_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (ss v sp0 fCap fPtr cap1 ptr1 : BitVec 64) (bs1 fBs : List (BitVec 8))
    (hf_nil : fBs ≠ []) (hf_le : fBs.length ≤ fCap.toNat) (hf_cap : fCap.toNat < 2 ^ 63)
    (hspare : bs1.length + fBs.length ≤ cap1.toNat)
    (_hlen_lt : bs1.length + fBs.length < 2 ^ 61)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 1560#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 fBs.length)
    (hx22 : s.readReg64 .x22 = fPtr)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (vecU8At A.repAlloc (ss + 296#64) fCap fPtr fBs ∗
      vecU8At A.repAlloc v cap1 ptr1 bs1 ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_14).base + 1608#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((vecU8At A.repAlloc (ss + 296#64) fCap fPtr fBs ∗
          vecU8At A.repAlloc v cap1 ptr1 (bs1 ++ fBs) ∗
          stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hCallMC := @encraw_call_memcpy_buf_prealloc_placed_x _ M A lim H hC
  rw [hP]
  refine sepWPpLsCl_extract_vecU8At_bounds (A := A.repAlloc) (v := v) (cap := cap1) (ptr := ptr1) (bs := bs1)
    (hfocus := by sep_focus) (h := fun _ hcap1 hptr1 => ?_)
  have hf_nat : (BitVec.ofNat 64 fBs.length).toNat = fBs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hbs1_nat : (BitVec.ofNat 64 bs1.length).toNat = bs1.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [vecU8At_open_src A.repAlloc (ss + 296#64) fCap fPtr fBs hf_nil hf_le,
      vecU8At_eq_header_sep_buf A.repAlloc v cap1 ptr1 bs1]
  simp only [vecHeader, sepConj_assoc]
  have hhi := cmp_hi_false_of_le hspare hcap1
  apply sepWPpLsCl_of_sepWP_vm (mid := lsρ lsMemcpySym)
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm0 => ?_⟩
    refine hCallMC sp0 v cap1 ptr1 fPtr ((blkPl_14).base + 1600#64) bs1 fBs
      hspare hcap1 hptr1 hf_nil (s0 := s0)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by sep_focus) ?_
    intro sm hvm1 hpcm hrunm hspm htrm hcsm
    have hx19m : sm.readReg64 .x19 = v := by
      have := hcsm.1; simp only [arm64_norm, *] at this; exact this
    have hx20m : sm.readReg64 .x20 = ss := by
      have := hcsm.2.1; simp only [arm64_norm, *] at this; exact this
    have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 fBs.length := by
      have := hcsm.2.2.1; simp only [arm64_norm, *] at this; exact this
    have hx23m : sm.readReg64 .x23 = BitVec.ofNat 64 bs1.length := by
      have := hcsm.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
    have hcsm' : EncRawUpperSaved s0 sm :=
      (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
        (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
    apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 1608#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvmm => ?_⟩
      refine SepWPpLsCl.weaken_pre ?_ (hnext _ (hvm0.trans (hvm1.trans hvmm))
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      rw [vecU8At_open_src A.repAlloc (ss + 296#64) fCap fPtr fBs hf_nil hf_le,
          ← vecU8At_close_slice A.repAlloc v cap1 ptr1 bs1 fBs hspare hcap1 hptr1 hf_nil]
      simp only [sepConj_assoc]
      exact entails_of_sep_focus (by sep_focus)

theorem step_tag14_sub2_prealloc_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (ss v sp0 fCap fPtr cap ptr : BitVec 64) (bs fBs : List (BitVec 8))
    (hspare : bs.length + (bytesField 2 fBs).length ≤ cap.toNat)
    (hlen_lt : bs.length + 11 + fBs.length < 2 ^ 61)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 1504#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 fBs.length)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (vecU8At A.repAlloc (ss + 296#64) fCap fPtr fBs ∗
      vecU8At A.repAlloc v cap ptr bs ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_14).base + 1608#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((vecU8At A.repAlloc (ss + 296#64) fCap fPtr fBs ∗
          vecU8At A.repAlloc v cap ptr (bs ++ bytesField 2 fBs) ∗
          stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hCallEV := @encraw_call_encodeVarint_prealloc_placed_x _ M A H
  have hStepB := @step_tag14_sub2_b_prealloc_placed_x _ M A lim H hC
  rw [hP]
  refine sepWPpLsCl_extract_vecU8At_bounds (A := A.repAlloc) (v := ss + 296#64) (cap := fCap) (ptr := fPtr) (bs := fBs)
    (hfocus := by sep_focus) (h := fun hf_le hf_cap _ => ?_)
  by_cases hf_nil : fBs = []
  · subst hf_nil
    simp only [sepConj_assoc]
    apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 1608#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm0 => ?_⟩
      refine SepWPpLsCl.weaken_pre ?_ (hnext _ hvm0
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      simp only [bytesField_nil, List.append_nil, sepConj_assoc]
      exact entails_of_sep_focus (by sep_focus)
  · have hf_beq : (BitVec.ofNat 64 fBs.length == 0#64) = false :=
      ofNat64_len_beq_zero_false hf_nil (by omega)
    have hfield_eq : bs ++ bytesField 2 fBs =
        ((bs ++ [18#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) ++ fBs := by
      rw [bytesField_ne_nil (k := 18#8) hf_nil]; simp only [List.append_assoc]
    have h10 := encodeVarint_length_le_10 (BitVec.ofNat 64 fBs.length)
    have hflen : (bytesField 2 fBs).length =
        (1 + (encodeVarint (BitVec.ofNat 64 fBs.length)).length) + fBs.length := by
      rw [bytesField_ne_nil (k := 18#8) hf_nil]
      simp only [List.length_append, List.length_singleton]
    have hlt : bs.length < cap.toNat := by omega
    have hbeq_cap := cap_beq_len_false hlt
    rw [vecU8At_open_src_off' A.repAlloc ss 296#64 304#64 312#64 fCap fPtr fBs hf_nil hf_le,
        vecU8At_open_one A.repAlloc v cap ptr bs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPpLsCl.exists_elim fun old => ?_
    apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm0 => ?_⟩
      refine SepWPpLsCl.weaken_pre
        (P' := (vecU8At A.repAlloc v cap ptr (bs ++ [18#8]) ∗
            stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
          vecU8At A.repAlloc (ss + 296#64) fCap fPtr fBs ∗ F)
        (by
          rw [vecU8At_open_src_off' A.repAlloc ss 296#64 304#64 312#64 fCap fPtr fBs hf_nil hf_le,
              ← vecU8At_close_one A.repAlloc v cap ptr bs 18#8 hlt]
          simp only [sepConj_assoc]
          exact entails_of_sep_focus (by sep_focus))
        (hCallEV sp0 (BitVec.ofNat 64 fBs.length) v cap ptr ((blkPl_14).base + 1560#64)
          (bs ++ [18#8])
          (by simp only [List.length_append, List.length_singleton]; omega)
          (by simp only [List.length_append, List.length_singleton]; omega)
          (s0 := s0)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by sep_focus) ?_)
      intro s1 hvm1 hpc1 hrun1 hsp1 htr1 hcs1
      have hx19_1 : s1.readReg64 .x19 = v := by
        have := hcs1.1; simp only [arm64_norm, *] at this; exact this
      have hx20_1 : s1.readReg64 .x20 = ss := by
        have := hcs1.2.1; simp only [arm64_norm, *] at this; exact this
      have hx21_1 : s1.readReg64 .x21 = BitVec.ofNat 64 fBs.length := by
        have := hcs1.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx22_1 : s1.readReg64 .x22 = fPtr := by
        have := hcs1.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hcs_1 : EncRawUpperSaved s0 s1 :=
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
          (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
      refine hStepB ss v sp0 fCap fPtr cap ptr
        ((bs ++ [18#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) fBs
        hf_nil hf_le hf_cap
        (by simp only [List.length_append, List.length_singleton]; omega)
        (by simp only [List.length_append, List.length_singleton]; omega)
        hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1 hx21_1 hx22_1 hcs_1
        (by sep_focus) ?_
      intro sm hvm2 hpcm hrunm hspm htrm hx19m hx20m hcsm'
      rw [← hfield_eq]
      refine SepWPpLsCl.weaken_pre ?_
        (hnext sm (hvm0.trans (hvm1.trans hvm2)) hpcm hrunm hspm htrm hx19m hx20m hcsm')
      exact entails_of_sep_focus (by sep_focus)

theorem step_encraw_tag14_prealloc_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (ss v sp0 cap ptr : BitVec 64)
    (G_kyber : Option TailVecGhost) (s_kyber : Option PendingKyberPreKey)
    (bs : List (BitVec 8))
    (hrel : KyberRel G_kyber s_kyber)
    (hbound : match s_kyber with | none => True | some k => k.ciphertext.length < 2 ^ 32)
    (hspare : bs.length + (msgField 14 (s_kyber.map encPendingKyber)).length ≤ cap.toNat)
    (hbs_lt : bs.length < 2 ^ 32)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 1292#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (optTailVecAt A.repAlloc 32 (ss + 296#64) G_kyber ∗ vecU8At A.repAlloc v cap ptr bs ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_14).base + 1608#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((optTailVecAt A.repAlloc 32 (ss + 296#64) G_kyber ∗
          vecU8At A.repAlloc v cap ptr (bs ++ msgField 14 (s_kyber.map encPendingKyber)) ∗
          stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  cases G_kyber with
  | none =>
    cases s_kyber with
    | some k => exact False.elim hrel
    | none =>
      rw [hP, optTailVecAt_kyber_none_eq]
      simp only [sepConj_assoc]
      apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 1608#64)
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm], fun hvm0 => ?_⟩
        refine SepWPpLsCl.weaken_pre ?_ (hnext _ hvm0
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
        rw [optTailVecAt_kyber_none_eq]
        simp only [Option.map_none, msgField, List.append_nil, sepConj_assoc]
        exact entails_of_sep_focus (by sep_focus)
  | some g =>
    cases s_kyber with
    | none => exact False.elim hrel
    | some k =>
      have hlt_ct31 : k.ciphertext.length < 2 ^ 32 := hbound
      have hlt_ct63 : k.ciphertext.length < 2 ^ 63 := by omega
      have hlen0_le := encodeVarint_length_le_10 (BitVec.ofNat 64 (encPendingKyber k).length)
      have hlen1_le := uint32Field1_length_le k.preKeyId
      let L0 := (encodeVarint (BitVec.ofNat 64 (encPendingKyber k).length)).length
      let L1 := (uint32Field 1 k.preKeyId).length
      let L2 := (bytesField 2 k.ciphertext).length
      have hmsg_len : (msgField 14 (Option.map encPendingKyber (some k))).length =
          ((1 + L0) + L1) + L2 := by
        simp only [Option.map_some, ← msgField14_some_eq k, List.length_append,
          List.length_singleton, L0, L1, L2]
      rw [hmsg_len] at hspare
      rw [hP]
      refine sepWPpLsCl_extract_kyber_some (A := A.repAlloc) (ss := ss) (g := g)
        (hfocus := by sep_focus) (h := fun hlen8 _ hcap_g _ => ?_)
      have hopen := optTailVecAt_kyber_some_eq_open A.repAlloc ss g k hlen8 hrel
      rw [hopen]
      refine step_tag14_write_tag_prealloc_placed_x A ss v sp0 cap ptr g k bs hcap_g (by omega)
        hpc hrun hsp htr hx19 hx20 hcs (by sep_focus) ?_
      intro s1 hvm0 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx22_1 hx21_1 hcs1
      refine step_tag14_len1_placed_x ss v sp0 k hlt_ct63
        hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx22_1 hx21_1 hcs1 ?_
      intro s2 hvm1 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx8_2 hx22_2 hx21_2 hcs2
      refine step_tag14_len2_prealloc_placed_x A ss v sp0 cap ptr g k bs
        (by omega) (by omega)
        hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2 hx8_2 hx22_2 hx21_2 hcs2 (by sep_focus) ?_
      intro s3 hvm2 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx22_3 hx21_3 hcs3
      refine step_tag14_sub1_prealloc_placed_x A ss v sp0 cap ptr g k
        ((bs ++ [114#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingKyber k).length))
        (by simp only [List.length_append, List.length_singleton]; omega)
        (by simp only [List.length_append, List.length_singleton]; omega)
        hpc3 hrun3 hsp3 halign htr3 hx19_3 hx20_3 hx22_3 hx21_3 hcs3 (by sep_focus) ?_
      intro s4 hvm3 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hx21_4 hcs4
      unfold kyberOpenAt
      refine step_tag14_sub2_prealloc_placed_x hC ss v sp0 g.vec.cap g.vec.ptr cap ptr
        (((bs ++ [114#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingKyber k).length)) ++
          uint32Field 1 k.preKeyId)
        k.ciphertext
        (by simp only [List.length_append, List.length_singleton]; omega)
        (by simp only [List.length_append, List.length_singleton]; omega)
        hpc4 hrun4 hsp4 halign htr4 hx19_4 hx20_4 hx21_4 hcs4 (by sep_focus) ?_
      intro s5 hvm4 hpc5 hrun5 hsp5 htr5 hx19_5 hx20_5 hcs5
      refine SepWPpLsCl.weaken_pre ?_
        (hnext s5 (hvm0.trans (hvm1.trans (hvm2.trans (hvm3.trans hvm4))))
          hpc5 hrun5 hsp5 htr5 hx19_5 hx20_5 hcs5)
      rw [hopen]
      unfold kyberOpenAt
      have hbytes :
          ((((bs ++ [114#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingKyber k).length)) ++
            uint32Field 1 k.preKeyId) ++ bytesField 2 k.ciphertext) =
          bs ++ msgField 14 (Option.map encPendingKyber (some k)) := by
        simp only [Option.map_some, ← msgField14_some_eq k, List.append_assoc]
      rw [hbytes]
      simp only [sepConj_assoc]
      exact entails_of_sep_focus (by sep_focus)

end Seg4b

/-! ## Tag 15: `pq_ratchet_state` and epilogue (`1608..1736`) -/

section Seg4c

set_option allowUnsafeReducibility true in
attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
  stackAt vecU8Buf vecSrcRest vecCopyDone Program.fnOff

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_add_neg80_4c

theorem step_encraw_tag15_b_prealloc_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (ss v sp0 fCap fPtr cap1 ptr1 : BitVec 64) (bs1 fBs : List (BitVec 8))
    (hf_nil : fBs ≠ []) (hf_le : fBs.length ≤ fCap.toNat) (hf_cap : fCap.toNat < 2 ^ 63)
    (hspare : bs1.length + fBs.length ≤ cap1.toNat)
    (_hlen_lt : bs1.length + fBs.length < 2 ^ 61)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 1668#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = fPtr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 fBs.length)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (vecU8At A.repAlloc (ss + 120#64) fCap fPtr fBs ∗
      vecU8At A.repAlloc v cap1 ptr1 bs1 ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_14).base + 1716#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      EncRawUpperSaved s0 sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((vecU8At A.repAlloc (ss + 120#64) fCap fPtr fBs ∗
          vecU8At A.repAlloc v cap1 ptr1 (bs1 ++ fBs) ∗
          stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hCallMC := @encraw_call_memcpy_buf_prealloc_placed_x _ M A lim H hC
  rw [hP]
  refine sepWPpLsCl_extract_vecU8At_bounds (A := A.repAlloc) (v := v) (cap := cap1) (ptr := ptr1) (bs := bs1)
    (hfocus := by sep_focus) (h := fun _ hcap1 hptr1 => ?_)
  have hf_nat : (BitVec.ofNat 64 fBs.length).toNat = fBs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hbs1_nat : (BitVec.ofNat 64 bs1.length).toNat = bs1.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [vecU8At_open_src A.repAlloc (ss + 120#64) fCap fPtr fBs hf_nil hf_le,
      vecU8At_eq_header_sep_buf A.repAlloc v cap1 ptr1 bs1]
  simp only [vecHeader, sepConj_assoc]
  have hhi := cmp_hi_false_of_le hspare hcap1
  apply sepWPpLsCl_of_sepWP_vm (mid := lsρ lsMemcpySym)
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm0 => ?_⟩
    refine hCallMC sp0 v cap1 ptr1 fPtr ((blkPl_14).base + 1708#64) bs1 fBs
      hspare hcap1 hptr1 hf_nil (s0 := s0)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by sep_focus) ?_
    intro sm hvm1 hpcm hrunm hspm htrm hcsm
    have hx19m : sm.readReg64 .x19 = v := by
      have := hcsm.1; simp only [arm64_norm, *] at this; exact this
    have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 fBs.length := by
      have := hcsm.2.2.1; simp only [arm64_norm, *] at this; exact this
    have hx22m : sm.readReg64 .x22 = BitVec.ofNat 64 bs1.length := by
      have := hcsm.2.2.2.1; simp only [arm64_norm, *] at this; exact this
    have hspm' : sm.sp = sp0 - 80#64 := hspm
    have hcsm' : EncRawUpperSaved s0 sm :=
      (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
        (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
    apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 1716#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvmm => ?_⟩
      refine SepWPpLsCl.weaken_pre ?_ (hnext _ (hvm0.trans (hvm1.trans hvmm))
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      rw [vecU8At_open_src A.repAlloc (ss + 120#64) fCap fPtr fBs hf_nil hf_le,
          ← vecU8At_close_slice A.repAlloc v cap1 ptr1 bs1 fBs hspare hcap1 hptr1 hf_nil]
      simp only [sepConj_assoc]
      exact entails_of_sep_focus (by sep_focus)

theorem step_encraw_tag15_prealloc_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (ss v sp0 fCap fPtr cap ptr : BitVec 64) (bs fBs : List (BitVec 8))
    (hspare : bs.length + (bytesField 15 fBs).length ≤ cap.toNat)
    (hlen_lt : bs.length + 11 + fBs.length < 2 ^ 61)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 1608#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (vecU8At A.repAlloc (ss + 120#64) fCap fPtr fBs ∗
      vecU8At A.repAlloc v cap ptr bs ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_14).base + 1716#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      EncRawUpperSaved s0 sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((vecU8At A.repAlloc (ss + 120#64) fCap fPtr fBs ∗
          vecU8At A.repAlloc v cap ptr (bs ++ bytesField 15 fBs) ∗
          stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hCallEV := @encraw_call_encodeVarint_prealloc_placed_x _ M A H
  have hStepB := @step_encraw_tag15_b_prealloc_placed_x _ M A lim H hC
  rw [hP]
  refine sepWPpLsCl_extract_vecU8At_bounds (A := A.repAlloc) (v := ss + 120#64) (cap := fCap) (ptr := fPtr) (bs := fBs)
    (hfocus := by sep_focus) (h := fun hf_le hf_cap _ => ?_)
  by_cases hf_nil : fBs = []
  · subst hf_nil
    rw [vecU8At_Nil_off' A.repAlloc ss 120#64 128#64 136#64 fCap fPtr]
    simp only [sepConj_assoc]
    apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 1716#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvmm => ?_⟩
      refine SepWPpLsCl.weaken_pre ?_ (hnext _ hvmm
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      rw [vecU8At_Nil_off' A.repAlloc ss 120#64 128#64 136#64 fCap fPtr]
      simp only [bytesField_nil, List.append_nil, sepConj_assoc]
      exact entails_of_sep_focus (by sep_focus)
  · have hfield_eq : bs ++ bytesField 15 fBs =
        ((bs ++ [122#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) ++ fBs := by
      rw [bytesField_ne_nil (k := 122#8) hf_nil]; simp only [List.append_assoc]
    have h10 := encodeVarint_length_le_10 (BitVec.ofNat 64 fBs.length)
    have hflen : (bytesField 15 fBs).length =
        (1 + (encodeVarint (BitVec.ofNat 64 fBs.length)).length) + fBs.length := by
      rw [bytesField_ne_nil (k := 122#8) hf_nil]
      simp only [List.length_append, List.length_singleton]
    have hf_beq : (BitVec.ofNat 64 fBs.length == 0#64) = false :=
      ofNat64_len_beq_zero_false hf_nil (by omega)
    have hlt : bs.length < cap.toNat := by omega
    have hbeq_cap := cap_beq_len_false hlt
    rw [vecU8At_open_src_off' A.repAlloc ss 120#64 128#64 136#64 fCap fPtr fBs hf_nil hf_le,
        vecU8At_open_one A.repAlloc v cap ptr bs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPpLsCl.exists_elim fun old => ?_
    apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm0 => ?_⟩
      refine SepWPpLsCl.weaken_pre
        (P' := (vecU8At A.repAlloc v cap ptr (bs ++ [122#8]) ∗
            stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
          vecU8At A.repAlloc (ss + 120#64) fCap fPtr fBs ∗ F)
        (by
          rw [vecU8At_open_src_off' A.repAlloc ss 120#64 128#64 136#64 fCap fPtr fBs hf_nil hf_le,
              ← vecU8At_close_one A.repAlloc v cap ptr bs 122#8 hlt]
          simp only [sepConj_assoc]
          exact entails_of_sep_focus (by sep_focus))
        (hCallEV sp0 (BitVec.ofNat 64 fBs.length) v cap ptr ((blkPl_14).base + 1668#64)
          (bs ++ [122#8])
          (by simp only [List.length_append, List.length_singleton]; omega)
          (by simp only [List.length_append, List.length_singleton]; omega)
          (s0 := s0)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by sep_focus) ?_)
      intro s1 hvm1 hpc1 hrun1 hsp1 htr1 hcs1
      have hx19_1 : s1.readReg64 .x19 = v := by
        have := hcs1.1; simp only [arm64_norm, *] at this; exact this
      have hx20_1 : s1.readReg64 .x20 = fPtr := by
        have := hcs1.2.1; simp only [arm64_norm, *] at this; exact this
      have hx21_1 : s1.readReg64 .x21 = BitVec.ofNat 64 fBs.length := by
        have := hcs1.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hcs_1 : EncRawUpperSaved s0 s1 :=
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
          (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
      refine hStepB ss v sp0 fCap fPtr cap ptr
        ((bs ++ [122#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) fBs
        hf_nil hf_le hf_cap
        (by simp only [List.length_append, List.length_singleton]; omega)
        (by simp only [List.length_append, List.length_singleton]; omega)
        hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1 hx21_1 hcs_1 (by sep_focus) ?_
      intro sm hvm2 hpcm hrunm hspm htrm hcsm'
      rw [← hfield_eq]
      refine SepWPpLsCl.weaken_pre ?_
        (hnext sm (hvm0.trans (hvm1.trans hvm2)) hpcm hrunm hspm htrm hcsm')
      exact entails_of_sep_focus (by sep_focus)

end Seg4c

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.SpareTailTagsXPlacedBudget
