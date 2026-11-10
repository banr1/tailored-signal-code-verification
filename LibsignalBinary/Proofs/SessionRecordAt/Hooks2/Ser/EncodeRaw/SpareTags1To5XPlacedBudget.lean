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
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.PrologueVersionLocalIdentity
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.BaseXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.BaseX
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PrologueVersionLocalIdentityXPlaced
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PrologueVersionLocalIdentityXPlacedBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.RemoteIdentityRootKeyCounterXPlaced
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.SpareBaseXBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBase
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.RemoteIdentityRootKeyCounter
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PrologueVersionLocalIdentityX
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.RemoteIdentityRootKeyCounterX
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Pre-Reserved `SessionStructure::encode_raw` Prologue and Tags 1–5 (`+0` → `+460`)

Proves zero-allocation (`VmPreserved`-preserving) relocatable step lemmas for the prologue and
protobuf tags 1–5 (`session_version`, `local_identity_public`, `remote_identity_public`, `root_key`,
and `previous_counter`, Block `14` offsets `0..460`) when the output buffer has spare capacity.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.SpareTags1To5XPlacedBudget

open Arm64 ProofLib SepProp
open CryptoVerification (
  LibsignalPlacement LibsignalHooks lsmpl lsMemcpySym lsρ
)
open CryptoVerification.RustHeap (vecHeader vecU8At)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  vecU8Buf vecU8At_eq_header_sep_buf cap_beq_len_false
)
open CryptoVerification.E2E.Record (uint32Field bytesField)
open CryptoVerification.E2E.Record.Placed (blkPl_14 lsProg_14)
open CryptoVerification.E2E.Record.Serialization (
  encodeRawSubStackX sepWPpLsCl_extract_vecU8At_bounds
  bv_add_neg80_x bv_add_neg80_1b_x
)
open CryptoVerification.E2E.Record.Serialization.EncodeRawAux (
  entails_of_sep_focus EncRawUpperSaved sp_sub_80_spAligned
  bv32_beq_zero_false ofNat64_len_beq_zero_false
  uint32Field_zero uint32Field_ne_zero bytesField_nil bytesField_ne_nil
  vecSrcRest vecCopyDone encodeVarint_length_le_10
  vecU8At_open_src vecU8At_close_slice
  vecU8At_open_one vecU8At_close_one vecU8At_Nil_eq
  vecU8At_open_src_off' vecU8At_Nil_off'
  cmp_hi_false_of_le
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

abbrev step_encraw_prologue_placed_x :=
  @PrologueVersionLocalIdentityXPlacedBudget.step_encraw_prologue_placed_x

/-! ## Tags 1 and 2 (`+28 → +192`) -/

section Tags1To2

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_add_neg80_x

theorem step_encraw_tag1_prealloc_placed_x [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) {H : LibsignalHooks}
    (ss v sp0 cap ptr : BitVec 64) (ver : BitVec 32) (bs : List (BitVec 8))
    (hspare : bs.length + (uint32Field 1 ver).length ≤ cap.toNat)
    (hlen_lt : bs.length + (uint32Field 1 ver).length < 2 ^ 32)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 28#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = ss)
    (hx1 : s.readReg64 .x1 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (((ss + 0x148#64) ↦₃₂ ver) ∗ vecU8At A.repAlloc v cap ptr bs ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_14).base + 84#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((((ss + 0x148#64) ↦₃₂ ver) ∗ vecU8At A.repAlloc v cap ptr (bs ++ uint32Field 1 ver) ∗
          stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hCallEV := @encraw_call_encodeVarint_prealloc_placed_x _ M A H
  rw [hP]
  by_cases hver : ver = 0#32
  · subst hver
    apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 84#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
      refine SepWPpLsCl.weaken_pre ?_
        (hnext _ hvm
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      simp only [uint32Field_zero, List.append_nil]
      exact entails_of_sep_focus (by sep_focus)
  · have hver_beq : (ver == 0#32) = false := bv32_beq_zero_false hver
    have hfield_eq : bs ++ uint32Field 1 ver =
        (bs ++ [0x08#8]) ++ encodeVarint (BitVec.zeroExtend 64 ver) := by
      rw [uint32Field_ne_zero (k := 0x08#8) hver, List.append_assoc]
    have hflen : (uint32Field 1 ver).length =
        1 + (encodeVarint (BitVec.zeroExtend 64 ver)).length := by
      rw [uint32Field_ne_zero (k := 0x08#8) hver]
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
        (P' := (vecU8At A.repAlloc v cap ptr (bs ++ [0x08#8]) ∗
            stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
          ((ss + 0x148#64) ↦₃₂ ver) ∗ F)
        (by
          rw [← vecU8At_close_one A.repAlloc v cap ptr bs 0x08#8 hlt]
          simp only [sepConj_assoc]
          exact entails_of_sep_focus (by sep_focus))
        (hCallEV sp0 (BitVec.zeroExtend 64 ver) v cap ptr ((blkPl_14).base + 84#64)
          (bs ++ [0x08#8])
          (by simp only [List.length_append, List.length_singleton]; omega)
          (by simp only [List.length_append, List.length_singleton]; omega)
          (s0 := s0)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by sep_focus) ?_)
      intro sm hvm1 hpcm hrunm hspm htrm hcsm
      have hx19m : sm.readReg64 .x19 = v := by
        have := hcsm.1; simp only [arm64_norm, *] at this; exact this
      have hx20m : sm.readReg64 .x20 = ss := by
        have := hcsm.2.1; simp only [arm64_norm, *] at this; exact this
      have hcsm' : EncRawUpperSaved s0 sm :=
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
          (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
      rw [← hfield_eq]
      refine SepWPpLsCl.weaken_pre ?_
        (hnext sm (hvm0.trans hvm1) hpcm hrunm hspm htrm hx19m hx20m hcsm')
      exact entails_of_sep_focus (by sep_focus)

theorem step_encraw_tag2_b_prealloc_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (ss v sp0 fCap fPtr cap1 ptr1 : BitVec 64) (bs1 fBs : List (BitVec 8))
    (hf_nil : fBs ≠ [])
    (hf_le : fBs.length ≤ fCap.toNat)
    (hf_cap : fCap.toNat < 2 ^ 63)
    (hcap_fit : bs1.length + fBs.length ≤ cap1.toNat)
    (_hlen_lt : bs1.length + fBs.length < 2 ^ 61)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 144#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 fBs.length)
    (hx22 : s.readReg64 .x22 = fPtr)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (vecU8At A.repAlloc ss fCap fPtr fBs ∗ vecU8At A.repAlloc v cap1 ptr1 bs1 ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_14).base + 192#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((vecU8At A.repAlloc ss fCap fPtr fBs ∗ vecU8At A.repAlloc v cap1 ptr1 (bs1 ++ fBs) ∗
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
  rw [vecU8At_open_src A.repAlloc ss fCap fPtr fBs hf_nil hf_le,
      vecU8At_eq_header_sep_buf A.repAlloc v cap1 ptr1 bs1]
  simp only [vecHeader, sepConj_assoc]
  have hhi := cmp_hi_false_of_le hcap_fit hcap1
  apply sepWPpLsCl_of_sepWP_vm (mid := lsρ lsMemcpySym)
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm0 => ?_⟩
    refine hCallMC sp0 v cap1 ptr1 fPtr ((blkPl_14).base + 184#64) bs1 fBs
      hcap_fit hcap1 hptr1 hf_nil (s0 := s0)
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
    apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 192#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvmm => ?_⟩
      refine SepWPpLsCl.weaken_pre ?_
        (hnext _ ((hvm0.trans hvm1).trans hvmm)
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      rw [vecU8At_open_src A.repAlloc ss fCap fPtr fBs hf_nil hf_le,
          ← vecU8At_close_slice A.repAlloc v cap1 ptr1 bs1 fBs hcap_fit hcap1 hptr1 hf_nil]
      simp only [sepConj_assoc]
      exact entails_of_sep_focus (by sep_focus)

theorem step_encraw_tag2_prealloc_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (ss v sp0 fCap fPtr cap ptr : BitVec 64) (bs fBs : List (BitVec 8))
    (hspare : bs.length + (bytesField 2 fBs).length ≤ cap.toNat)
    (hlen_lt : bs.length + (bytesField 2 fBs).length < 2 ^ 32)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 84#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (vecU8At A.repAlloc ss fCap fPtr fBs ∗ vecU8At A.repAlloc v cap ptr bs ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_14).base + 192#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((vecU8At A.repAlloc ss fCap fPtr fBs ∗
          vecU8At A.repAlloc v cap ptr (bs ++ bytesField 2 fBs) ∗
          stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hCallEV := @encraw_call_encodeVarint_prealloc_placed_x _ M A H
  have hStepB := @step_encraw_tag2_b_prealloc_placed_x _ M A lim H hC
  rw [hP]
  refine sepWPpLsCl_extract_vecU8At_bounds (A := A.repAlloc) (v := ss) (cap := fCap) (ptr := fPtr) (bs := fBs)
    (hfocus := by sep_focus) (h := fun hf_le hf_cap _ => ?_)
  by_cases hf_nil : fBs = []
  · subst hf_nil
    rw [vecU8At_Nil_eq A.repAlloc ss fCap fPtr]
    simp only [sepConj_assoc]
    apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 192#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
      refine SepWPpLsCl.weaken_pre ?_
        (hnext _ hvm
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      rw [vecU8At_Nil_eq A.repAlloc ss fCap fPtr]
      simp only [bytesField_nil, List.append_nil, sepConj_assoc]
      exact entails_of_sep_focus (by sep_focus)
  · have hf_pos : 1 ≤ fBs.length := List.length_pos_of_ne_nil hf_nil
    have hflen : (bytesField 2 fBs).length =
        (1 + (encodeVarint (BitVec.ofNat 64 fBs.length)).length) + fBs.length := by
      rw [bytesField_ne_nil (k := 0x12#8) hf_nil]
      simp only [List.length_append, List.length_singleton]
    have hf_beq : (BitVec.ofNat 64 fBs.length == 0#64) = false :=
      ofNat64_len_beq_zero_false hf_nil (by omega)
    have hfield_eq : bs ++ bytesField 2 fBs =
        ((bs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) ++ fBs := by
      rw [bytesField_ne_nil (k := 0x12#8) hf_nil]; simp only [List.append_assoc]
    have hlt : bs.length < cap.toNat := by omega
    have hbeq_cap := cap_beq_len_false hlt
    rw [vecU8At_open_src A.repAlloc ss fCap fPtr fBs hf_nil hf_le,
        vecU8At_open_one A.repAlloc v cap ptr bs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPpLsCl.exists_elim fun old => ?_
    apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm0 => ?_⟩
      refine SepWPpLsCl.weaken_pre
        (P' := (vecU8At A.repAlloc v cap ptr (bs ++ [0x12#8]) ∗
            stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
          vecU8At A.repAlloc ss fCap fPtr fBs ∗ F)
        (by
          rw [vecU8At_open_src A.repAlloc ss fCap fPtr fBs hf_nil hf_le,
              ← vecU8At_close_one A.repAlloc v cap ptr bs 0x12#8 hlt]
          simp only [sepConj_assoc]
          exact entails_of_sep_focus (by sep_focus))
        (hCallEV sp0 (BitVec.ofNat 64 fBs.length) v cap ptr ((blkPl_14).base + 144#64)
          (bs ++ [0x12#8])
          (by simp only [List.length_append, List.length_singleton]; omega)
          (by simp only [List.length_append, List.length_singleton]; omega)
          (s0 := s0)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by sep_focus) ?_)
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
        ((bs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) fBs
        hf_nil hf_le hf_cap
        (by simp only [List.length_append, List.length_singleton]; omega)
        (by simp only [List.length_append, List.length_singleton]; omega)
        hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1 hx21_1 hx22_1 hcs_1
        (by sep_focus) ?_
      intro sm hvm2 hpcm hrunm hspm htrm hx19m hx20m hcsm'
      rw [← hfield_eq]
      refine SepWPpLsCl.weaken_pre ?_
        (hnext sm ((hvm0.trans hvm1).trans hvm2) hpcm hrunm hspm htrm hx19m hx20m hcsm')
      exact entails_of_sep_focus (by sep_focus)

end Tags1To2

/-! ## Tags 3, 4, and 5 (`+192 → +460`) -/

section Tags3To5

set_option allowUnsafeReducibility true in
attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
  stackAt vecU8Buf vecSrcRest vecCopyDone Program.fnOff

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_add_neg80_1b_x

theorem step_encraw_tag3_b_prealloc_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (ss v sp0 fCap fPtr cap1 ptr1 : BitVec 64) (bs1 fBs : List (BitVec 8))
    (hf_nil : fBs ≠ [])
    (hf_le : fBs.length ≤ fCap.toNat)
    (hf_cap : fCap.toNat < 2 ^ 63)
    (hfit_cap : bs1.length + fBs.length ≤ cap1.toNat)
    (_hlen_lt : bs1.length + fBs.length < 2 ^ 61)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 252#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 fBs.length)
    (hx22 : s.readReg64 .x22 = fPtr)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (vecU8At A.repAlloc (ss + 24#64) fCap fPtr fBs ∗ vecU8At A.repAlloc v cap1 ptr1 bs1 ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_14).base + 300#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((vecU8At A.repAlloc (ss + 24#64) fCap fPtr fBs ∗
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
  rw [vecU8At_open_src A.repAlloc (ss + 24#64) fCap fPtr fBs hf_nil hf_le,
      vecU8At_eq_header_sep_buf A.repAlloc v cap1 ptr1 bs1]
  simp only [vecHeader, sepConj_assoc]
  have hhi := cmp_hi_false_of_le hfit_cap hcap1
  apply sepWPpLsCl_of_sepWP_vm (mid := lsρ lsMemcpySym)
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm0 => ?_⟩
    refine hCallMC sp0 v cap1 ptr1 fPtr ((blkPl_14).base + 292#64) bs1 fBs
      hfit_cap hcap1 hptr1 hf_nil (s0 := s0)
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
    have hspm' : sm.sp = sp0 - 80#64 := hspm
    have hcsm' : EncRawUpperSaved s0 sm :=
      (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
        (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
    apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 300#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvmm' => ?_⟩
      refine SepWPpLsCl.weaken_pre ?_
        (hnext _ ((hvm0.trans hvm1).trans hvmm')
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      rw [vecU8At_open_src A.repAlloc (ss + 24#64) fCap fPtr fBs hf_nil hf_le,
          ← vecU8At_close_slice A.repAlloc v cap1 ptr1 bs1 fBs hfit_cap hcap1 hptr1 hf_nil]
      simp only [sepConj_assoc]
      exact entails_of_sep_focus (by sep_focus)

theorem step_encraw_tag3_prealloc_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (ss v sp0 fCap fPtr cap ptr : BitVec 64) (bs fBs : List (BitVec 8))
    (hspare : bs.length + (bytesField 3 fBs).length ≤ cap.toNat)
    (hlen_lt : bs.length + (bytesField 3 fBs).length < 2 ^ 32)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 192#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (vecU8At A.repAlloc (ss + 24#64) fCap fPtr fBs ∗ vecU8At A.repAlloc v cap ptr bs ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_14).base + 300#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((vecU8At A.repAlloc (ss + 24#64) fCap fPtr fBs ∗
          vecU8At A.repAlloc v cap ptr (bs ++ bytesField 3 fBs) ∗
          stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hCallEV := @encraw_call_encodeVarint_prealloc_placed_x _ M A H
  have hStepB := @step_encraw_tag3_b_prealloc_placed_x _ M A lim H hC
  rw [hP]
  refine sepWPpLsCl_extract_vecU8At_bounds (A := A.repAlloc) (v := ss + 24#64) (cap := fCap) (ptr := fPtr) (bs := fBs)
    (hfocus := by sep_focus) (h := fun hf_le hf_cap _ => ?_)
  by_cases hf_nil : fBs = []
  · subst hf_nil
    rw [vecU8At_Nil_off' A.repAlloc ss 24#64 32#64 40#64 fCap fPtr]
    simp only [sepConj_assoc]
    apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 300#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvmm => ?_⟩
      refine SepWPpLsCl.weaken_pre ?_
        (hnext _ hvmm
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      rw [vecU8At_Nil_off' A.repAlloc ss 24#64 32#64 40#64 fCap fPtr]
      simp only [bytesField_nil, List.append_nil, sepConj_assoc]
      exact entails_of_sep_focus (by sep_focus)
  · have hf_pos : 1 ≤ fBs.length := List.length_pos_of_ne_nil hf_nil
    have hfield_len : (bytesField 3 fBs).length =
        (1 + (encodeVarint (BitVec.ofNat 64 fBs.length)).length) + fBs.length := by
      rw [bytesField_ne_nil (k := 26#8) hf_nil]
      simp only [List.length_append, List.length_singleton]
    have hf_beq : (BitVec.ofNat 64 fBs.length == 0#64) = false :=
      ofNat64_len_beq_zero_false hf_nil (by omega)
    have hfield_eq : bs ++ bytesField 3 fBs =
        ((bs ++ [26#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) ++ fBs := by
      rw [bytesField_ne_nil (k := 26#8) hf_nil]; simp only [List.append_assoc]
    have hlt : bs.length < cap.toNat := by omega
    have hbeq_cap := cap_beq_len_false hlt
    rw [vecU8At_open_src_off' A.repAlloc ss 24#64 32#64 40#64 fCap fPtr fBs hf_nil hf_le,
        vecU8At_open_one A.repAlloc v cap ptr bs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPpLsCl.exists_elim fun old => ?_
    apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm0 => ?_⟩
      have hclose_one := vecU8At_close_one A.repAlloc v cap ptr bs 26#8 hlt
      refine SepWPpLsCl.weaken_pre (P' :=
          (vecU8At A.repAlloc v cap ptr (bs ++ [26#8]) ∗
            stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
            (vecU8At A.repAlloc (ss + 24#64) fCap fPtr fBs ∗ F))
        (by
          rw [← hclose_one, vecU8At_open_src_off' A.repAlloc ss 24#64 32#64 40#64 fCap fPtr fBs hf_nil hf_le]
          simp only [sepConj_assoc]
          exact entails_of_sep_focus (by sep_focus)) ?_
      refine hCallEV sp0 (BitVec.ofNat 64 fBs.length) v cap ptr ((blkPl_14).base + 252#64)
        (bs ++ [26#8])
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
        ((bs ++ [26#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) fBs
        hf_nil hf_le hf_cap
        (by simp only [List.length_append, List.length_singleton]; omega)
        (by simp only [List.length_append, List.length_singleton]; omega)
        hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1 hx21_1 hx22_1 hcs_1 (by sep_focus) ?_
      intro sm hvm2 hpcm hrunm hspm htrm hx19m hx20m hcsm'
      rw [← hfield_eq]
      refine SepWPpLsCl.weaken_pre ?_
        (hnext sm ((hvm0.trans hvm1).trans hvm2) hpcm hrunm hspm htrm hx19m hx20m hcsm')
      exact entails_of_sep_focus (by sep_focus)

theorem step_encraw_tag4_b_prealloc_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (ss v sp0 fCap fPtr cap1 ptr1 : BitVec 64) (bs1 fBs : List (BitVec 8))
    (hf_nil : fBs ≠ [])
    (hf_le : fBs.length ≤ fCap.toNat)
    (hf_cap : fCap.toNat < 2 ^ 63)
    (hfit_cap : bs1.length + fBs.length ≤ cap1.toNat)
    (_hlen_lt : bs1.length + fBs.length < 2 ^ 61)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 360#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 fBs.length)
    (hx22 : s.readReg64 .x22 = fPtr)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (vecU8At A.repAlloc (ss + 48#64) fCap fPtr fBs ∗ vecU8At A.repAlloc v cap1 ptr1 bs1 ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_14).base + 408#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((vecU8At A.repAlloc (ss + 48#64) fCap fPtr fBs ∗
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
  rw [vecU8At_open_src A.repAlloc (ss + 48#64) fCap fPtr fBs hf_nil hf_le,
      vecU8At_eq_header_sep_buf A.repAlloc v cap1 ptr1 bs1]
  simp only [vecHeader, sepConj_assoc]
  have hhi := cmp_hi_false_of_le hfit_cap hcap1
  apply sepWPpLsCl_of_sepWP_vm (mid := lsρ lsMemcpySym)
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm0 => ?_⟩
    refine hCallMC sp0 v cap1 ptr1 fPtr ((blkPl_14).base + 400#64) bs1 fBs
      hfit_cap hcap1 hptr1 hf_nil (s0 := s0)
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
    have hspm' : sm.sp = sp0 - 80#64 := hspm
    have hcsm' : EncRawUpperSaved s0 sm :=
      (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
        (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
    apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 408#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvmm' => ?_⟩
      refine SepWPpLsCl.weaken_pre ?_
        (hnext _ ((hvm0.trans hvm1).trans hvmm')
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      rw [vecU8At_open_src A.repAlloc (ss + 48#64) fCap fPtr fBs hf_nil hf_le,
          ← vecU8At_close_slice A.repAlloc v cap1 ptr1 bs1 fBs hfit_cap hcap1 hptr1 hf_nil]
      simp only [sepConj_assoc]
      exact entails_of_sep_focus (by sep_focus)

theorem step_encraw_tag4_prealloc_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (ss v sp0 fCap fPtr cap ptr : BitVec 64) (bs fBs : List (BitVec 8))
    (hspare : bs.length + (bytesField 4 fBs).length ≤ cap.toNat)
    (hlen_lt : bs.length + (bytesField 4 fBs).length < 2 ^ 32)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 300#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (vecU8At A.repAlloc (ss + 48#64) fCap fPtr fBs ∗ vecU8At A.repAlloc v cap ptr bs ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_14).base + 408#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((vecU8At A.repAlloc (ss + 48#64) fCap fPtr fBs ∗
          vecU8At A.repAlloc v cap ptr (bs ++ bytesField 4 fBs) ∗
          stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hCallEV := @encraw_call_encodeVarint_prealloc_placed_x _ M A H
  have hStepB := @step_encraw_tag4_b_prealloc_placed_x _ M A lim H hC
  rw [hP]
  refine sepWPpLsCl_extract_vecU8At_bounds (A := A.repAlloc) (v := ss + 48#64) (cap := fCap) (ptr := fPtr) (bs := fBs)
    (hfocus := by sep_focus) (h := fun hf_le hf_cap _ => ?_)
  by_cases hf_nil : fBs = []
  · subst hf_nil
    rw [vecU8At_Nil_off' A.repAlloc ss 48#64 56#64 64#64 fCap fPtr]
    simp only [sepConj_assoc]
    apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 408#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvmm => ?_⟩
      refine SepWPpLsCl.weaken_pre ?_
        (hnext _ hvmm
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      rw [vecU8At_Nil_off' A.repAlloc ss 48#64 56#64 64#64 fCap fPtr]
      simp only [bytesField_nil, List.append_nil, sepConj_assoc]
      exact entails_of_sep_focus (by sep_focus)
  · have hf_pos : 1 ≤ fBs.length := List.length_pos_of_ne_nil hf_nil
    have hfield_len : (bytesField 4 fBs).length =
        (1 + (encodeVarint (BitVec.ofNat 64 fBs.length)).length) + fBs.length := by
      rw [bytesField_ne_nil (k := 34#8) hf_nil]
      simp only [List.length_append, List.length_singleton]
    have hf_beq : (BitVec.ofNat 64 fBs.length == 0#64) = false :=
      ofNat64_len_beq_zero_false hf_nil (by omega)
    have hfield_eq : bs ++ bytesField 4 fBs =
        ((bs ++ [34#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) ++ fBs := by
      rw [bytesField_ne_nil (k := 34#8) hf_nil]; simp only [List.append_assoc]
    have hlt : bs.length < cap.toNat := by omega
    have hbeq_cap := cap_beq_len_false hlt
    rw [vecU8At_open_src_off' A.repAlloc ss 48#64 56#64 64#64 fCap fPtr fBs hf_nil hf_le,
        vecU8At_open_one A.repAlloc v cap ptr bs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPpLsCl.exists_elim fun old => ?_
    apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm0 => ?_⟩
      have hclose_one := vecU8At_close_one A.repAlloc v cap ptr bs 34#8 hlt
      refine SepWPpLsCl.weaken_pre (P' :=
          (vecU8At A.repAlloc v cap ptr (bs ++ [34#8]) ∗
            stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
            (vecU8At A.repAlloc (ss + 48#64) fCap fPtr fBs ∗ F))
        (by
          rw [← hclose_one, vecU8At_open_src_off' A.repAlloc ss 48#64 56#64 64#64 fCap fPtr fBs hf_nil hf_le]
          simp only [sepConj_assoc]
          exact entails_of_sep_focus (by sep_focus)) ?_
      refine hCallEV sp0 (BitVec.ofNat 64 fBs.length) v cap ptr ((blkPl_14).base + 360#64)
        (bs ++ [34#8])
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
        ((bs ++ [34#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) fBs
        hf_nil hf_le hf_cap
        (by simp only [List.length_append, List.length_singleton]; omega)
        (by simp only [List.length_append, List.length_singleton]; omega)
        hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1 hx21_1 hx22_1 hcs_1 (by sep_focus) ?_
      intro sm hvm2 hpcm hrunm hspm htrm hx19m hx20m hcsm'
      rw [← hfield_eq]
      refine SepWPpLsCl.weaken_pre ?_
        (hnext sm ((hvm0.trans hvm1).trans hvm2) hpcm hrunm hspm htrm hx19m hx20m hcsm')
      exact entails_of_sep_focus (by sep_focus)

theorem step_encraw_tag5_prealloc_placed_x [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) {H : LibsignalHooks}
    (ss v sp0 cap ptr : BitVec 64) (prevCnt : BitVec 32) (bs : List (BitVec 8))
    (hspare : bs.length + (uint32Field 5 prevCnt).length ≤ cap.toNat)
    (hlen_lt : bs.length + (uint32Field 5 prevCnt).length < 2 ^ 32)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 408#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (((ss + 332#64) ↦₃₂ prevCnt) ∗ vecU8At A.repAlloc v cap ptr bs ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_14).base + 460#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((((ss + 332#64) ↦₃₂ prevCnt) ∗ vecU8At A.repAlloc v cap ptr (bs ++ uint32Field 5 prevCnt) ∗
          stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hCallEV := @encraw_call_encodeVarint_prealloc_placed_x _ M A H
  rw [hP]
  by_cases hver : prevCnt = 0#32
  · subst hver
    simp only [sepConj_assoc]
    apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 460#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvmm => ?_⟩
      refine SepWPpLsCl.weaken_pre ?_
        (hnext _ hvmm
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      simp only [uint32Field_zero, List.append_nil, sepConj_assoc]
      exact entails_of_sep_focus (by sep_focus)
  · have hver_beq : (prevCnt == 0#32) = false := bv32_beq_zero_false hver
    have hfield_eq : bs ++ uint32Field 5 prevCnt =
        (bs ++ [40#8]) ++ encodeVarint (BitVec.zeroExtend 64 prevCnt) := by
      rw [uint32Field_ne_zero (k := 40#8) hver, List.append_assoc]
    have hfield_len : (uint32Field 5 prevCnt).length =
        1 + (encodeVarint (BitVec.zeroExtend 64 prevCnt)).length := by
      rw [uint32Field_ne_zero (k := 40#8) hver, List.length_append, List.length_singleton]
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
      have hclose := vecU8At_close_one A.repAlloc v cap ptr bs 40#8 hlt
      refine SepWPpLsCl.weaken_pre (P' :=
          (vecU8At A.repAlloc v cap ptr (bs ++ [40#8]) ∗
            stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ (((ss + 332#64) ↦₃₂ prevCnt) ∗ F))
        (by rw [← hclose]; exact entails_of_sep_focus (by sep_focus)) ?_
      refine hCallEV sp0 (BitVec.zeroExtend 64 prevCnt) v cap ptr ((blkPl_14).base + 460#64)
        (bs ++ [40#8])
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
      refine SepWPpLsCl.weaken_pre ?_
        (hnext sm (hvm0.trans hvm1) hpcm hrunm hspm htrm hx19m hx20m hcsm')
      exact entails_of_sep_focus (by sep_focus)

end Tags3To5

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.SpareTags1To5XPlacedBudget
