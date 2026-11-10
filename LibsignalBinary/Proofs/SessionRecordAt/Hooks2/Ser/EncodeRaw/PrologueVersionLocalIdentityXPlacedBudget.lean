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
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.PrologueVersionLocalIdentity
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.BaseXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.BaseX
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.BaseXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PrologueVersionLocalIdentityXPlaced
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PrologueVersionLocalIdentityX
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `SessionStructure::encode_raw` Prologue and Tags 1–2 (`+0` → `+192`)

Verifies the `VmPreserved` prologue (`+0 → +28`), protobuf tag 1 (`session_version`, `+28 → +84`),
and protobuf tag 2 (`local_identity_public`, `+84 → +192`) of Block `14` under
`RustCliAllocBudget M` and `EncRawSegEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PrologueVersionLocalIdentityXPlacedBudget

open Arm64 ProofLib SepProp
open CryptoVerification (
  LibsignalPlacement LibsignalHooks lsmpl lsMemcpySym lsρ
)
open CryptoVerification.RustHeap (vecHeader vecU8At)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  vecU8Buf vecU8At_eq_header_sep_buf cap_beq_len_false cap_eq_ofNat_len
)
open CryptoVerification.E2E.Record (uint32Field bytesField)
open CryptoVerification.E2E.Record.Placed (blkPl_14 lsProg_14)
open CryptoVerification.E2E.Record.Serialization (
  encodeRawSubStackX stackAt_encodeRawStackX_unfold
  sepWPpLsCl_extract_vecU8At_bounds bv_add_neg80_x
)
open CryptoVerification.E2E.Record.Serialization.EncodeRawAux (
  entails_of_sep_focus encRawSavedRegs EncRawUpperSaved sp_sub_80_spAligned
  bv32_beq_zero_false ofNat64_len_beq_zero_false
  uint32Field_zero uint32Field_ne_zero bytesField_nil bytesField_ne_nil
  vecSrcRest vecCopyDone encodeVarint_length_le_10
  vecU8At_open_src vecU8At_close_src vecU8At_close_slice
  vecU8At_open_one vecU8At_close_one vecU8At_Nil_eq
  cmp_hi_false_of_le cmp_hi_true_of_gt cmp_ls_true_of_le
)
open Proofs.libsignal.Hooks2 (SepWPpLsCl)
open LibsignalBinary.Heap (
  VmPreserved AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget (
  EncodeVarintEnv
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  DoReserveEnv
)
open LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.BaseBudget (
  EncRawSegEnv encRawSegEnv_nil encRawSegEnv_mono encRawSegEnv_append
  fitsEnv_encRawSeg_left fitsEnv_encRawSeg_right
  fitsEnv_doReserve_of_encRawSeg fitsEnv_encodeVarint_of_encRawSeg
  doReserveEnv_sub_boundedRustEvs encodeVarintEnv_sub_boundedRustEvs
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (
  encodeRawStackX SerContractsXPlaced
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget (
  EncodeVarintPlacedOkX DoReservePlacedOkX
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.BaseXBudget (
  sepWPpLsCl_of_sepWP_vm sepWPpLsCl_transport_budgetPool
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.BaseXBudget (
  encraw_call_doReserve_placed_x encraw_call_encodeVarint_placed_x encraw_call_memcpy_placed_x
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_add_neg80_x

/-! ## Buffer call helpers on `lsProg_14 H` -/

theorem encraw_call_doReserve_buf_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hDR : DoReservePlacedOkX M A lim H)
    (sp0 v cap ptr ret_pc : BitVec 64) (bs : List (BitVec 8)) (add : Nat)
    (st : M.σ)
    (hcap_le : cap.toNat ≤ bs.length + add)
    (hlen_lt : bs.length + add < 2 ^ 62)
    (hfit : FitsEnv M lim st (DoReserveEnv (DoReserveCall.mk v cap ptr bs add)))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 13)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v)
    (hx1 : (s.readReg64 .x1).toNat = bs.length)
    (hx2 : (s.readReg64 .x2).toNat = add)
    (hx3 : s.readReg64 .x3 = 1#64)
    (hx4 : s.readReg64 .x4 = 1#64)
    (hP : P = ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8Buf A.repAlloc cap ptr bs ∗ A.pool lim st s ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (newCap p' : BitVec 64) (evs : List AllocEvent),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      DoReserveEnv (DoReserveCall.mk v cap ptr bs add) evs →
      bs.length + add ≤ newCap.toNat →
      newCap.toNat < 2 ^ 63 →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((vecU8At A.repAlloc v newCap p' bs ∗ A.pool lim (M.stepEvents evs st) sm ∗
          stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hP' : P = (vecU8At A.repAlloc v cap ptr bs ∗ A.pool lim st s ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by
    rw [hP, vecU8At_eq_header_sep_buf]
    simp only [vecHeader, sepConj_assoc]
  exact encraw_call_doReserve_placed_x hDR sp0 v cap ptr ret_pc bs add st hcap_le hlen_lt hfit
    hpc hrun hsp halign htr hlr hx0 hx1 hx2 hx3 hx4 hP' hnext

theorem encraw_call_memcpy_buf_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (sp0 v cap ptr srcPtr ret_pc : BitVec 64) (bs payload : List (BitVec 8))
    (st : M.σ)
    (hle : bs.length + payload.length ≤ cap.toNat)
    (hcap : cap.toNat < 2 ^ 63)
    (hptr : ptr ≠ 0#64)
    (hne : payload ≠ [])
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsρ lsMemcpySym)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = ptr + BitVec.ofNat 64 bs.length)
    (hx1 : s.readReg64 .x1 = srcPtr)
    (hx2 : (s.readReg64 .x2).toNat = payload.length)
    (hP : P = (((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8Buf A.repAlloc cap ptr bs ∗ (srcPtr ↦ₛ payload)) ∗
      A.pool lim st s ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          vecCopyDone A.repAlloc cap ptr bs payload ∗ (srcPtr ↦ₛ payload)) ∗
          A.pool lim st sm ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hP' : P = (vecU8At A.repAlloc v cap ptr bs ∗ (srcPtr ↦ₛ payload) ∗ A.pool lim st s ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by
    rw [hP, vecU8At_eq_header_sep_buf]
    simp only [vecHeader, sepConj_assoc]
  refine encraw_call_memcpy_placed_x hC sp0 v cap ptr srcPtr ret_pc bs payload st hle hcap hptr hne
    hpc hrun hsp halign htr hlr hx0 hx1 hx2 hP' ?_
  intro sm hvm hpcm hrunm hspm htrm hcsm
  refine SepWPpLsCl.weaken_pre ?_ (hnext sm hvm hpcm hrunm hspm htrm hcsm)
  rw [vecCopyDone.eq_def]
  have hpure : (bs.length + payload.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧
      ptr ≠ 0#64 ∧ payload ≠ []) = True :=
    eq_true ⟨hle, hcap, hptr, hne⟩
  rw [hpure, pure_true, emp_sepConj]
  exact Entails.of_eq (by sep_ac_rfl)

/-! ## Prologue (`+0 → +28`) -/

theorem step_encraw_prologue_placed_x [LibsignalPlacement] (H : LibsignalHooks)
    (ss v sp0 : BitVec 64)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = ss)
    (hx1 : s.readReg64 .x1 = v)
    (hcs0 : CalleeSavedPreserved s0 s)
    (hlr0 : s.readReg64 .lr = s0.readReg64 .lr)
    (hP : P = stackAt sp0 encodeRawStackX ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (v56 : BitVec 64),
      VmPreserved s sm →
      sm.pc = (blkPl_14).base + 28#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x0 = ss →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((encRawSavedRegs sp0 s0 v56 ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F) Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  rcases hcs0 with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩
  rw [hP, stackAt_encodeRawStackX_unfold sp0]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPpLsCl.exists_elim fun v80 => SepWPpLsCl.exists_elim fun v72 =>
    SepWPpLsCl.exists_elim fun v64 => SepWPpLsCl.exists_elim fun v56 =>
    SepWPpLsCl.exists_elim fun v48 => SepWPpLsCl.exists_elim fun v40 =>
    SepWPpLsCl.exists_elim fun v32 => SepWPpLsCl.exists_elim fun v24 =>
    SepWPpLsCl.exists_elim fun v16 => SepWPpLsCl.exists_elim fun v8 => ?_
  apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 28#64)
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
    rw [show
        ((sp0 - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((sp0 - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((sp0 - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
        ((sp0 - 56#64) ↦₆₄ v56) ∗
        ((sp0 - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
        ((sp0 - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((sp0 - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((sp0 - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((sp0 - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((sp0 - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
        stackAt (sp0 - 80#64) encodeRawSubStackX ∗ F =
        (encRawSavedRegs sp0 s0 v56 ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F by
      simp only [encRawSavedRegs, Reg.lr, Reg.x25, Reg.x24, Reg.x23, Reg.x22, Reg.x21,
        Reg.x20, Reg.x19, sepConj_assoc]]
    exact hnext _ v56 hvm
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩

/-! ## Tag 1 (`session_version`, `+28 → +84`, reserve `+1740..+1776`) -/

theorem step_encraw_tag1_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hDR : DoReservePlacedOkX M A lim H)
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (ss v sp0 cap ptr : BitVec 64) (ver : BitVec 32) (bs : List (BitVec 8))
    (st : M.σ)
    (hlen_lt : bs.length + 11 < 2 ^ 61)
    (hfit : FitsEnv M lim st (EncRawSegEnv bs.length (uint32Field 1 ver).length))
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
      A.pool lim st s ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_14).base + 84#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      EncRawSegEnv bs.length (uint32Field 1 ver).length evs →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((((ss + 0x148#64) ↦₃₂ ver) ∗ vecU8At A.repAlloc v cap' ptr' (bs ++ uint32Field 1 ver) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hCallDR := @encraw_call_doReserve_placed_x _ M A lim H hDR
  have hCallEV := @encraw_call_encodeVarint_placed_x _ M A lim H hEV
  rw [hP]
  by_cases hver : ver = 0#32
  · subst hver
    apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 84#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm =>
          sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := st) hvm (by sep_focus) ?_⟩
      refine SepWPpLsCl.weaken_pre ?_
        (hnext _ cap ptr []
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
          (by rw [uint32Field_zero]; exact encRawSegEnv_nil _ _))
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
    have hvlen10 := encodeVarint_length_le_10 (BitVec.zeroExtend 64 ver)
    refine sepWPpLsCl_extract_vecU8At_bounds (A := A.repAlloc) (v := v) (cap := cap) (ptr := ptr) (bs := bs)
      (hfocus := by sep_focus) (h := fun hle _ _ => ?_)
    by_cases hlt : bs.length < cap.toNat
    · have hbeq_cap := cap_beq_len_false hlt
      rw [vecU8At_open_one A.repAlloc v cap ptr bs hlt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPpLsCl.exists_elim fun old => ?_
      apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm], fun hvm0 =>
            sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := st) hvm0 (by sep_focus) ?_⟩
        have hfitEV : FitsEnv M lim st
            (EncodeVarintEnv ⟨BitVec.zeroExtend 64 ver, v, cap, ptr, bs ++ [0x08#8]⟩) :=
          fitsEnv_encodeVarint_of_encRawSeg (by dsimp only; omega)
            (by (try dsimp only); (try simp only [List.length_append, List.length_singleton]); omega)
            (by (try dsimp only); (try simp only [List.length_append, List.length_singleton]); omega) hfit
        refine SepWPpLsCl.weaken_pre
          (P' := (vecU8At A.repAlloc v cap ptr (bs ++ [0x08#8]) ∗
              A.pool lim st _ ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
            ((ss + 0x148#64) ↦₃₂ ver) ∗ F)
          (by
            rw [← vecU8At_close_one A.repAlloc v cap ptr bs 0x08#8 hlt]
            simp only [sepConj_assoc]
            exact entails_of_sep_focus (by sep_focus))
          (hCallEV sp0 (BitVec.zeroExtend 64 ver) v cap ptr ((blkPl_14).base + 84#64)
            (bs ++ [0x08#8]) st (by simp; omega) hfitEV (s0 := s0)
            ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_)
        · simp only [arm64_norm]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · intro sm cap' ptr' evs hpcm hrunm hspm htrm hcsm hevs
          have hx19m : sm.readReg64 .x19 = v := by
            have := hcsm.1; simp only [arm64_norm, *] at this; exact this
          have hx20m : sm.readReg64 .x20 = ss := by
            have := hcsm.2.1; simp only [arm64_norm, *] at this; exact this
          have hcsm' : EncRawUpperSaved s0 sm :=
            (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
              (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
          have hevs_seg : EncRawSegEnv bs.length (uint32Field 1 ver).length evs := by
            have hb := encodeVarintEnv_sub_boundedRustEvs
              (outLen := bs.length + (uint32Field 1 ver).length)
              (by (try dsimp only); (try simp only [List.length_append, List.length_singleton]); omega)
              (by (try dsimp only); omega) hevs
            exact hb.mono (by dsimp only; omega) (Nat.le_refl _)
          rw [← hfield_eq]
          refine SepWPpLsCl.weaken_pre ?_
            (hnext sm cap' ptr' evs hpcm hrunm hspm htrm hx19m hx20m hcsm' hevs_seg)
          exact entails_of_sep_focus (by sep_focus)
    · have hcap_eq : cap.toNat = bs.length := by omega
      have hcap_bv := cap_eq_ofNat_len hcap_eq
      rw [hflen] at hfit
      have hfit1 : FitsEnv M lim st (EncRawSegEnv bs.length 1) :=
        fitsEnv_encRawSeg_left hfit
      have hfitDR : FitsEnv M lim st (DoReserveEnv (DoReserveCall.mk v cap ptr bs 1)) :=
        fitsEnv_doReserve_of_encRawSeg (by omega) (by dsimp only; omega)
          (by dsimp only; omega) (by omega) hfit1
      rw [vecU8At_eq_header_sep_buf A.repAlloc v cap ptr bs]
      simp only [vecHeader, sepConj_assoc]
      apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 13)
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm], fun hvm0 =>
            sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := st) hvm0 (by sep_focus) ?_⟩
        have hx1_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        refine SepWPpLsCl.weaken_pre
          (P' := (vecU8At A.repAlloc v cap ptr bs ∗
              A.pool lim st _ ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
            ((ss + 0x148#64) ↦₃₂ ver) ∗ F)
          (by
            rw [vecU8At_eq_header_sep_buf A.repAlloc v cap ptr bs]
            simp only [vecHeader, sepConj_assoc]
            exact entails_of_sep_focus (by sep_focus))
          (hCallDR sp0 v cap ptr ((blkPl_14).base + 1764#64) bs 1 st
            (by omega) (by omega) hfitDR (s0 := s0)
            ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_)
        · simp only [arm64_norm]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm]
        · simp only [arm64_norm]
        · simp only [arm64_norm]
        · intro s1 newCap p' evs1 hpc1 hrun1 hsp1 htr1 hcs1 hevs1 hnew_ge _
          have he1_seg : EncRawSegEnv bs.length 1 evs1 :=
            (doReserveEnv_sub_boundedRustEvs (outLen := bs.length + 1)
              (by dsimp only; omega) (by dsimp only; omega) (by omega) hevs1).mono
              (by omega) (Nat.le_refl _)
          have hfit2 : FitsEnv M lim (M.stepEvents evs1 st)
              (EncRawSegEnv (bs.length + 1) (encodeVarint (BitVec.zeroExtend 64 ver)).length) :=
            fitsEnv_encRawSeg_right hfit he1_seg
          have hx19_1 : s1.readReg64 .x19 = v := by
            have := hcs1.1; simp only [arm64_norm, *] at this; exact this
          have hx20_1 : s1.readReg64 .x20 = ss := by
            have := hcs1.2.1; simp only [arm64_norm, *] at this; exact this
          have hx21_1 : s1.readReg64 .x21 = BitVec.zeroExtend 64 ver := by
            have := hcs1.2.2.1; simp only [arm64_norm, *] at this; exact this
          have hcs_1 : EncRawUpperSaved s0 s1 :=
            (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
              (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
          have hnew_gt : bs.length < newCap.toNat := by omega
          rw [vecU8At_open_one A.repAlloc v newCap p' bs hnew_gt]
          simp only [sepExists_sepConj_left, sepConj_assoc]
          refine SepWPpLsCl.exists_elim fun old => ?_
          apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
          by_vm_steps
            wp_steps
            refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              ⟨by simp only [wp_norm, arm64_norm], fun hvm2 =>
                sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := M.stepEvents evs1 st) hvm2 (by sep_focus) ?_⟩
            have hfitEV : FitsEnv M lim (M.stepEvents evs1 st)
                (EncodeVarintEnv ⟨BitVec.zeroExtend 64 ver, v, newCap, p', bs ++ [0x08#8]⟩) :=
              fitsEnv_encodeVarint_of_encRawSeg (by dsimp only; omega)
                (by (try dsimp only); (try simp only [List.length_append, List.length_singleton]); omega)
                (by (try dsimp only); (try simp only [List.length_append, List.length_singleton]); omega) hfit2
            refine SepWPpLsCl.weaken_pre
              (P' := (vecU8At A.repAlloc v newCap p' (bs ++ [0x08#8]) ∗
                  A.pool lim (M.stepEvents evs1 st) _ ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
                ((ss + 0x148#64) ↦₃₂ ver) ∗ F)
              (by
                rw [← vecU8At_close_one A.repAlloc v newCap p' bs 0x08#8 hnew_gt]
                simp only [sepConj_assoc]
                exact entails_of_sep_focus (by sep_focus))
              (hCallEV sp0 (BitVec.zeroExtend 64 ver) v newCap p' ((blkPl_14).base + 84#64)
                (bs ++ [0x08#8]) (M.stepEvents evs1 st) (by simp; omega) hfitEV (s0 := s0)
                ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_)
            · simp only [arm64_norm]
            · simp only [arm64_norm, *]
            · simp only [arm64_norm, *]
            · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
            · simp only [arm64_norm, *]
            · simp only [arm64_norm, *]
            · simp only [arm64_norm, *]
            · simp only [arm64_norm, *]
            · intro sm cap' ptr' evs2 hpcm hrunm hspm htrm hcsm hevs2
              have hx19m : sm.readReg64 .x19 = v := by
                have := hcsm.1; simp only [arm64_norm, *] at this; exact this
              have hx20m : sm.readReg64 .x20 = ss := by
                have := hcsm.2.1; simp only [arm64_norm, *] at this; exact this
              have hcsm' : EncRawUpperSaved s0 sm :=
                (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
                  (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
              have he2_seg : EncRawSegEnv (bs.length + 1)
                  (encodeVarint (BitVec.zeroExtend 64 ver)).length evs2 :=
                (encodeVarintEnv_sub_boundedRustEvs
                  (outLen := (bs.length + 1) + (encodeVarint (BitVec.zeroExtend 64 ver)).length)
                  (by (try dsimp only); (try simp only [List.length_append, List.length_singleton]); omega)
                  (by (try dsimp only); omega) hevs2).mono (by dsimp only; omega) (Nat.le_refl _)
              have he12 : EncRawSegEnv bs.length (uint32Field 1 ver).length (evs1 ++ evs2) := by
                rw [hflen]; exact encRawSegEnv_append he1_seg he2_seg
              rw [← hfield_eq, ← M.stepEvents_append]
              refine SepWPpLsCl.weaken_pre ?_
                (hnext sm cap' ptr' (evs1 ++ evs2) hpcm hrunm hspm htrm hx19m hx20m hcsm' he12)
              exact entails_of_sep_focus (by sep_focus)

/-! ## Tag 2 (`local_identity_public`, `+84 → +192`, reserve `+1776..+1876`) -/

theorem step_encraw_tag2_b_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hDR : DoReservePlacedOkX M A lim H)
    (hC : SerContractsXPlaced M A lim H)
    (ss v sp0 fCap fPtr cap1 ptr1 : BitVec 64) (bs1 fBs : List (BitVec 8))
    (st : M.σ)
    (hf_nil : fBs ≠ [])
    (hf_le : fBs.length ≤ fCap.toNat)
    (hf_cap : fCap.toNat < 2 ^ 63)
    (hlen_lt : bs1.length + fBs.length < 2 ^ 61)
    (hfit : FitsEnv M lim st (EncRawSegEnv bs1.length fBs.length))
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
      A.pool lim st s ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_14).base + 192#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      EncRawSegEnv bs1.length fBs.length evs →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((vecU8At A.repAlloc ss fCap fPtr fBs ∗ vecU8At A.repAlloc v cap' ptr' (bs1 ++ fBs) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hCallDR := @encraw_call_doReserve_buf_placed_x _ M A lim H hDR
  have hCallMC := @encraw_call_memcpy_buf_placed_x _ M A lim H hC
  have hf_pos : 1 ≤ fBs.length := List.length_pos_of_ne_nil hf_nil
  rw [hP]
  refine sepWPpLsCl_extract_vecU8At_bounds (A := A.repAlloc) (v := v) (cap := cap1) (ptr := ptr1) (bs := bs1)
    (hfocus := by sep_focus) (h := fun hle1 hcap1 hptr1 => ?_)
  have hf_nat : (BitVec.ofNat 64 fBs.length).toNat = fBs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hbs1_nat : (BitVec.ofNat 64 bs1.length).toNat = bs1.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [vecU8At_open_src A.repAlloc ss fCap fPtr fBs hf_nil hf_le,
      vecU8At_eq_header_sep_buf A.repAlloc v cap1 ptr1 bs1]
  simp only [vecHeader, sepConj_assoc]
  by_cases hcap_fit : bs1.length + fBs.length ≤ cap1.toNat
  · have hhi := cmp_hi_false_of_le hcap_fit hcap1
    apply sepWPpLsCl_of_sepWP_vm (mid := lsρ lsMemcpySym)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm0 =>
          sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := st) hvm0 (by sep_focus) ?_⟩
      refine hCallMC sp0 v cap1 ptr1 fPtr ((blkPl_14).base + 184#64) bs1 fBs st
        hcap_fit hcap1 hptr1 hf_nil (s0 := s0)
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
      · intro sm _ hpcm hrunm hspm htrm hcsm
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
            ⟨by simp only [wp_norm, arm64_norm], fun hvmm =>
              sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := st) hvmm (by sep_focus) ?_⟩
          refine SepWPpLsCl.weaken_pre ?_ (hnext _ cap1 ptr1 []
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
            (encRawSegEnv_nil _ _))
          rw [vecU8At_open_src A.repAlloc ss fCap fPtr fBs hf_nil hf_le,
              ← vecU8At_close_slice A.repAlloc v cap1 ptr1 bs1 fBs hcap_fit hcap1 hptr1 hf_nil]
          simp only [sepConj_assoc]
          exact entails_of_sep_focus (by sep_focus)
  · have hhi := cmp_hi_true_of_gt (add := fBs.length) hle1 (by omega) hcap1 (by omega)
    have hfitDR : FitsEnv M lim st (DoReserveEnv (DoReserveCall.mk v cap1 ptr1 bs1 fBs.length)) :=
      fitsEnv_doReserve_of_encRawSeg hf_pos (by dsimp only; omega) (by dsimp only; omega) hlen_lt hfit
    apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 13)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm0 =>
          sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := st) hvm0 (by sep_focus) ?_⟩
      refine hCallDR sp0 v cap1 ptr1 ((blkPl_14).base + 1828#64) bs1 fBs.length st
        (by omega) (by omega) hfitDR (s0 := s0)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
      · simp only [arm64_norm]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm]
      · simp only [arm64_norm]
      · intro s1 newCap p' evs hpc1 hrun1 hsp1 htr1 hcs1 hevs hnew_ge hnew_lt
        have hevs_seg : EncRawSegEnv bs1.length fBs.length evs :=
          (doReserveEnv_sub_boundedRustEvs (outLen := bs1.length + fBs.length)
            (by dsimp only; omega) (by dsimp only; omega) hlen_lt hevs).mono (by omega) (Nat.le_refl _)
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
        have hls := cmp_ls_true_of_le hnew_ge hnew_lt
        refine sepWPpLsCl_extract_vecU8At_bounds (A := A.repAlloc) (v := v) (cap := newCap) (ptr := p') (bs := bs1)
          (hfocus := by sep_focus) (h := fun _ _ hp'_ne => ?_)
        rw [vecU8At_eq_header_sep_buf A.repAlloc v newCap p' bs1]
        simp only [vecHeader, sepConj_assoc]
        apply sepWPpLsCl_of_sepWP_vm (mid := lsρ lsMemcpySym)
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [wp_norm, arm64_norm], fun hvm2 =>
              sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := M.stepEvents evs st) hvm2 (by sep_focus) ?_⟩
          refine hCallMC sp0 v newCap p' fPtr ((blkPl_14).base + 184#64) bs1 fBs
            (M.stepEvents evs st) hnew_ge hnew_lt hp'_ne hf_nil (s0 := s0)
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
          · intro sm _ hpcm hrunm hspm htrm hcsm
            have hx19m : sm.readReg64 .x19 = v := by
              have := hcsm.1; simp only [arm64_norm, *] at this; exact this
            have hx20m : sm.readReg64 .x20 = ss := by
              have := hcsm.2.1; simp only [arm64_norm, *] at this; exact this
            have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 fBs.length := by
              have := hcsm.2.2.1; simp only [arm64_norm, *] at this; exact this
            have hx23m : sm.readReg64 .x23 = BitVec.ofNat 64 bs1.length := by
              have := hcsm.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
            have hcsm' : EncRawUpperSaved s0 sm :=
              (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
                (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
            apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 192#64)
            by_vm_steps
              wp_steps
              refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                ⟨by simp only [wp_norm, arm64_norm], fun hvmm =>
                  sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := M.stepEvents evs st) hvmm (by sep_focus) ?_⟩
              refine SepWPpLsCl.weaken_pre ?_ (hnext _ newCap p' evs
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
                hevs_seg)
              rw [vecU8At_open_src A.repAlloc ss fCap fPtr fBs hf_nil hf_le,
                  ← vecU8At_close_slice A.repAlloc v newCap p' bs1 fBs hnew_ge hnew_lt hp'_ne hf_nil]
              simp only [sepConj_assoc]
              exact entails_of_sep_focus (by sep_focus)

theorem step_encraw_tag2_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hDR : DoReservePlacedOkX M A lim H)
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (hC : SerContractsXPlaced M A lim H)
    (ss v sp0 fCap fPtr cap ptr : BitVec 64) (bs fBs : List (BitVec 8))
    (st : M.σ)
    (hlen_lt : bs.length + 11 + fBs.length < 2 ^ 61)
    (hfit : FitsEnv M lim st (EncRawSegEnv bs.length (bytesField 2 fBs).length))
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
      A.pool lim st s ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_14).base + 192#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      EncRawSegEnv bs.length (bytesField 2 fBs).length evs →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((vecU8At A.repAlloc ss fCap fPtr fBs ∗
          vecU8At A.repAlloc v cap' ptr' (bs ++ bytesField 2 fBs) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hCallDR := @encraw_call_doReserve_buf_placed_x _ M A lim H hDR
  have hCallEV := @encraw_call_encodeVarint_placed_x _ M A lim H hEV
  have hStepB := @step_encraw_tag2_b_placed_x _ M A lim H hDR hC
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
        ⟨by simp only [wp_norm, arm64_norm], fun hvm =>
          sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := st) hvm (by sep_focus) ?_⟩
      refine SepWPpLsCl.weaken_pre ?_
        (hnext _ cap ptr []
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
          (by rw [bytesField_nil]; exact encRawSegEnv_nil _ _))
      rw [vecU8At_Nil_eq A.repAlloc ss fCap fPtr]
      simp only [bytesField_nil, List.append_nil, sepConj_assoc]
      exact entails_of_sep_focus (by sep_focus)
  · have hf_beq : (BitVec.ofNat 64 fBs.length == 0#64) = false :=
      ofNat64_len_beq_zero_false hf_nil (by omega)
    have hfield_eq : bs ++ bytesField 2 fBs =
        ((bs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) ++ fBs := by
      rw [bytesField_ne_nil (k := 0x12#8) hf_nil]; simp only [List.append_assoc]
    have h10 := encodeVarint_length_le_10 (BitVec.ofNat 64 fBs.length)
    have hflen : (bytesField 2 fBs).length =
        (1 + (encodeVarint (BitVec.ofNat 64 fBs.length)).length) + fBs.length := by
      rw [bytesField_ne_nil (k := 0x12#8) hf_nil]
      simp only [List.length_append, List.length_singleton]
    have hlen_bs1 :
        ((bs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)).length + fBs.length < 2 ^ 61 := by
      simp only [List.length_append, List.length_singleton]
      omega
    have hbs1_len_eq :
        ((bs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)).length =
          bs.length + (1 + (encodeVarint (BitVec.ofNat 64 fBs.length)).length) := by
      simp only [List.length_append, List.length_singleton]; omega
    rw [hflen] at hfit
    have hfit_hdr : FitsEnv M lim st
        (EncRawSegEnv bs.length (1 + (encodeVarint (BitVec.ofNat 64 fBs.length)).length)) :=
      fitsEnv_encRawSeg_left hfit
    refine sepWPpLsCl_extract_vecU8At_bounds (A := A.repAlloc) (v := v) (cap := cap) (ptr := ptr) (bs := bs)
      (hfocus := by sep_focus) (h := fun hle _ _ => ?_)
    rw [vecU8At_open_src A.repAlloc ss fCap fPtr fBs hf_nil hf_le]
    by_cases hlt : bs.length < cap.toNat
    · have hbeq_cap := cap_beq_len_false hlt
      rw [vecU8At_open_one A.repAlloc v cap ptr bs hlt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPpLsCl.exists_elim fun old => ?_
      apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm], fun hvm0 =>
            sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := st) hvm0 (by sep_focus) ?_⟩
        have hfitEV : FitsEnv M lim st
            (EncodeVarintEnv ⟨BitVec.ofNat 64 fBs.length, v, cap, ptr, bs ++ [0x12#8]⟩) :=
          fitsEnv_encodeVarint_of_encRawSeg (by dsimp only; omega)
            (by (try dsimp only); (try simp only [List.length_append, List.length_singleton]); omega)
            (by (try dsimp only); (try simp only [List.length_append, List.length_singleton]); omega) hfit_hdr
        refine SepWPpLsCl.weaken_pre
          (P' := (vecU8At A.repAlloc v cap ptr (bs ++ [0x12#8]) ∗
              A.pool lim st _ ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
            vecU8At A.repAlloc ss fCap fPtr fBs ∗ F)
          (by
            rw [vecU8At_open_src A.repAlloc ss fCap fPtr fBs hf_nil hf_le,
                ← vecU8At_close_one A.repAlloc v cap ptr bs 0x12#8 hlt]
            simp only [sepConj_assoc]
            exact entails_of_sep_focus (by sep_focus))
          (hCallEV sp0 (BitVec.ofNat 64 fBs.length) v cap ptr ((blkPl_14).base + 144#64)
            (bs ++ [0x12#8]) st (by simp; omega) hfitEV (s0 := s0)
            ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_)
        · simp only [arm64_norm]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · intro s1 cap1 ptr1 evs1 hpc1 hrun1 hsp1 htr1 hcs1 hevs1
          have he1_hdr : EncRawSegEnv bs.length
              (1 + (encodeVarint (BitVec.ofNat 64 fBs.length)).length) evs1 :=
            (encodeVarintEnv_sub_boundedRustEvs
              (outLen := bs.length + (1 + (encodeVarint (BitVec.ofNat 64 fBs.length)).length))
              (by (try dsimp only); (try simp only [List.length_append, List.length_singleton]); omega)
              (by (try dsimp only); omega) hevs1).mono (by dsimp only; omega) (Nat.le_refl _)
          have hfit_body : FitsEnv M lim (M.stepEvents evs1 st)
              (EncRawSegEnv ((bs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)).length
                fBs.length) := by
            rw [hbs1_len_eq]
            exact fitsEnv_encRawSeg_right hfit he1_hdr
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
          refine hStepB ss v sp0 fCap fPtr cap1 ptr1
            ((bs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) fBs
            (M.stepEvents evs1 st) hf_nil hf_le hf_cap hlen_bs1 hfit_body
            hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1 hx21_1 hx22_1 hcs_1
            (by sep_focus) ?_
          intro sm cap' ptr' evs2 hpcm hrunm hspm htrm hx19m hx20m hcsm' hevs2
          rw [hbs1_len_eq] at hevs2
          have he12 : EncRawSegEnv bs.length (bytesField 2 fBs).length (evs1 ++ evs2) := by
            rw [hflen]; exact encRawSegEnv_append he1_hdr hevs2
          rw [← hfield_eq, ← M.stepEvents_append]
          refine SepWPpLsCl.weaken_pre ?_
            (hnext sm cap' ptr' (evs1 ++ evs2) hpcm hrunm hspm htrm hx19m hx20m hcsm' he12)
          exact entails_of_sep_focus (by sep_focus)
    · have hcap_eq : cap.toNat = bs.length := by omega
      have hcap_bv := cap_eq_ofNat_len hcap_eq
      have hfit1 : FitsEnv M lim st (EncRawSegEnv bs.length 1) :=
        fitsEnv_encRawSeg_left hfit_hdr
      have hfitDR : FitsEnv M lim st (DoReserveEnv (DoReserveCall.mk v cap ptr bs 1)) :=
        fitsEnv_doReserve_of_encRawSeg (by omega) (by dsimp only; omega)
          (by dsimp only; omega) (by omega) hfit1
      rw [vecU8At_eq_header_sep_buf A.repAlloc v cap ptr bs]
      simp only [vecHeader, sepConj_assoc]
      apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 13)
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm], fun hvm0 =>
            sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := st) hvm0 (by sep_focus) ?_⟩
        have hx1_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        refine hCallDR sp0 v cap ptr ((blkPl_14).base + 1796#64) bs 1 st
          (by omega) (by omega) hfitDR (s0 := s0)
          ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
        · simp only [arm64_norm]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm]
        · simp only [arm64_norm]
        · simp only [arm64_norm]
        · intro s1 newCap p' evs_dr hpc1 hrun1 hsp1 htr1 hcs1 hevs_dr hnew_ge _
          have he_dr : EncRawSegEnv bs.length 1 evs_dr :=
            (doReserveEnv_sub_boundedRustEvs (outLen := bs.length + 1)
              (by dsimp only; omega) (by dsimp only; omega) (by omega) hevs_dr).mono
              (by omega) (Nat.le_refl _)
          have hfit_ev_seg : FitsEnv M lim (M.stepEvents evs_dr st)
              (EncRawSegEnv (bs.length + 1) (encodeVarint (BitVec.ofNat 64 fBs.length)).length) :=
            fitsEnv_encRawSeg_right hfit_hdr he_dr
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
          have hnew_gt : bs.length < newCap.toNat := by omega
          rw [vecU8At_open_one A.repAlloc v newCap p' bs hnew_gt]
          simp only [sepExists_sepConj_left, sepConj_assoc]
          refine SepWPpLsCl.exists_elim fun old => ?_
          apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
          by_vm_steps
            wp_steps
            refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              ⟨by simp only [wp_norm, arm64_norm], fun hvm2 =>
                sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := M.stepEvents evs_dr st) hvm2 (by sep_focus) ?_⟩
            have hfitEV : FitsEnv M lim (M.stepEvents evs_dr st)
                (EncodeVarintEnv ⟨BitVec.ofNat 64 fBs.length, v, newCap, p', bs ++ [0x12#8]⟩) :=
              fitsEnv_encodeVarint_of_encRawSeg (by dsimp only; omega)
                (by (try dsimp only); (try simp only [List.length_append, List.length_singleton]); omega)
                (by (try dsimp only); (try simp only [List.length_append, List.length_singleton]); omega) hfit_ev_seg
            refine SepWPpLsCl.weaken_pre
              (P' := (vecU8At A.repAlloc v newCap p' (bs ++ [0x12#8]) ∗
                  A.pool lim (M.stepEvents evs_dr st) _ ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
                vecU8At A.repAlloc ss fCap fPtr fBs ∗ F)
              (by
                rw [vecU8At_open_src A.repAlloc ss fCap fPtr fBs hf_nil hf_le,
                    ← vecU8At_close_one A.repAlloc v newCap p' bs 0x12#8 hnew_gt]
                simp only [sepConj_assoc]
                exact entails_of_sep_focus (by sep_focus))
              (hCallEV sp0 (BitVec.ofNat 64 fBs.length) v newCap p' ((blkPl_14).base + 144#64)
                (bs ++ [0x12#8]) (M.stepEvents evs_dr st) (by simp; omega) hfitEV (s0 := s0)
                ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_)
            · simp only [arm64_norm]
            · simp only [arm64_norm, *]
            · simp only [arm64_norm, *]
            · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
            · simp only [arm64_norm, *]
            · simp only [arm64_norm, *]
            · simp only [arm64_norm, *]
            · simp only [arm64_norm, *]
            · intro s2 cap1 ptr1 evs_ev hpc2 hrun2 hsp2 htr2 hcs2 hevs_ev
              have he_ev : EncRawSegEnv (bs.length + 1)
                  (encodeVarint (BitVec.ofNat 64 fBs.length)).length evs_ev :=
                (encodeVarintEnv_sub_boundedRustEvs
                  (outLen := (bs.length + 1) + (encodeVarint (BitVec.ofNat 64 fBs.length)).length)
                  (by (try dsimp only); (try simp only [List.length_append, List.length_singleton]); omega)
                  (by (try dsimp only); omega) hevs_ev).mono (by dsimp only; omega) (Nat.le_refl _)
              have he1_hdr : EncRawSegEnv bs.length
                  (1 + (encodeVarint (BitVec.ofNat 64 fBs.length)).length) (evs_dr ++ evs_ev) :=
                encRawSegEnv_append he_dr he_ev
              have hfit_body : FitsEnv M lim (M.stepEvents (evs_dr ++ evs_ev) st)
                  (EncRawSegEnv ((bs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)).length
                    fBs.length) := by
                rw [hbs1_len_eq]
                exact fitsEnv_encRawSeg_right hfit he1_hdr
              have hx19_2 : s2.readReg64 .x19 = v := by
                have := hcs2.1; simp only [arm64_norm, *] at this; exact this
              have hx20_2 : s2.readReg64 .x20 = ss := by
                have := hcs2.2.1; simp only [arm64_norm, *] at this; exact this
              have hx21_2 : s2.readReg64 .x21 = BitVec.ofNat 64 fBs.length := by
                have := hcs2.2.2.1; simp only [arm64_norm, *] at this; exact this
              have hx22_2 : s2.readReg64 .x22 = fPtr := by
                have := hcs2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
              have hcs_2 : EncRawUpperSaved s0 s2 :=
                (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
                  (EncRawUpperSaved.of_calleeSavedPreserved hcs2)
              rw [← M.stepEvents_append]
              refine hStepB ss v sp0 fCap fPtr cap1 ptr1
                ((bs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) fBs
                (M.stepEvents (evs_dr ++ evs_ev) st) hf_nil hf_le hf_cap hlen_bs1 hfit_body
                hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2 hx21_2 hx22_2 hcs_2
                (by sep_focus) ?_
              intro sm cap' ptr' evs2 hpcm hrunm hspm htrm hx19m hx20m hcsm' hevs2
              rw [hbs1_len_eq] at hevs2
              have he_all : EncRawSegEnv bs.length (bytesField 2 fBs).length
                  ((evs_dr ++ evs_ev) ++ evs2) := by
                rw [hflen]; exact encRawSegEnv_append he1_hdr hevs2
              rw [← hfield_eq, ← M.stepEvents_append]
              refine SepWPpLsCl.weaken_pre ?_
                (hnext sm cap' ptr' ((evs_dr ++ evs_ev) ++ evs2)
                  hpcm hrunm hspm htrm hx19m hx20m hcsm' he_all)
              exact entails_of_sep_focus (by sep_focus)

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PrologueVersionLocalIdentityXPlacedBudget
