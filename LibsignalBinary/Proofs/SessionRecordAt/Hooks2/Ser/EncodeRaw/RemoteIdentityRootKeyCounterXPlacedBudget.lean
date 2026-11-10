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
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.BaseXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.BaseX
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.BaseXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PrologueVersionLocalIdentityXPlacedBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.RemoteIdentityRootKeyCounterXPlaced
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.RemoteIdentityRootKeyCounterXPlacedBudgetAux
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
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
# Budget-Threaded `SessionStructure::encode_raw` Tags 3, 4, and 5 (`192` → `460`)

Re-exports protobuf tag 3 (`remote_identity_public`) and verifies protobuf tags 4 (`root_key`) and
5 (`previous_counter`, Block `14` offsets `192..460`, cold `1880..2120`) under
`RustCliAllocBudget M` and `EncRawSegEnv`.
-/

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

@[expose] public section

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.RemoteIdentityRootKeyCounterXPlacedBudget

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
  encodeRawSubStackX sepWPpLsCl_extract_vecU8At_bounds bv_add_neg80_1b_x
)
open CryptoVerification.E2E.Record.Serialization.EncodeRawAux (
  entails_of_sep_focus
  EncRawUpperSaved sp_sub_80_spAligned bv32_beq_zero_false ofNat64_len_beq_zero_false
  uint32Field_zero uint32Field_ne_zero bytesField_nil bytesField_ne_nil
  vecSrcRest vecCopyDone encodeVarint_length_le_10
  vecU8At_open_src vecU8At_close_slice vecU8At_open_one vecU8At_close_one
  vecU8At_open_src_off' vecU8At_Nil_off'
  cmp_hi_false_of_le cmp_hi_true_of_gt cmp_ls_true_of_le
)
open Proofs.libsignal.Hooks2 (SepWPpLsCl)
open LibsignalBinary.Heap (
  VmPreserved AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  DoReserveEnv
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget (
  EncodeVarintEnv
)
open LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.BaseBudget (
  EncRawSegEnv encRawSegEnv_nil encRawSegEnv_append
  fitsEnv_encRawSeg_left fitsEnv_encRawSeg_right
  fitsEnv_doReserve_of_encRawSeg fitsEnv_encodeVarint_of_encRawSeg
  doReserveEnv_sub_boundedRustEvs encodeVarintEnv_sub_boundedRustEvs
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (
  SerContractsXPlaced
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget (
  EncodeVarintPlacedOkX DoReservePlacedOkX
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.BaseXBudget (
  sepWPpLsCl_of_sepWP_vm sepWPpLsCl_transport_budgetPool
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.BaseXBudget (
  encraw_call_doReserve_placed_x encraw_call_encodeVarint_placed_x
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PrologueVersionLocalIdentityXPlacedBudget (
  encraw_call_doReserve_buf_placed_x encraw_call_memcpy_buf_placed_x
)

abbrev step_encraw_tag3_b_placed_x :=
  @RemoteIdentityRootKeyCounterXPlacedBudgetAux.step_encraw_tag3_b_placed_x
abbrev step_encraw_tag3_placed_x :=
  @RemoteIdentityRootKeyCounterXPlacedBudgetAux.step_encraw_tag3_placed_x

set_option allowUnsafeReducibility true in
attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
  stackAt vecU8Buf vecSrcRest vecCopyDone Program.fnOff

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_add_neg80_1b_x

theorem step_encraw_tag4_b_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (hDR : DoReservePlacedOkX M A lim H)
    (ss v sp0 fCap fPtr cap1 ptr1 : BitVec 64) (bs1 fBs : List (BitVec 8)) (st : M.σ)
    (hf_nil : fBs ≠ [])
    (hf_le : fBs.length ≤ fCap.toNat)
    (hf_cap : fCap.toNat < 2 ^ 63)
    (hlen_lt : bs1.length + fBs.length < 2 ^ 61)
    (hfit : FitsEnv M lim st (EncRawSegEnv bs1.length fBs.length))
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
      A.pool lim st s ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_14).base + 408#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      EncRawSegEnv bs1.length fBs.length evs →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((vecU8At A.repAlloc (ss + 48#64) fCap fPtr fBs ∗
          vecU8At A.repAlloc v cap' ptr' (bs1 ++ fBs) ∗
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
  rw [vecU8At_open_src A.repAlloc (ss + 48#64) fCap fPtr fBs hf_nil hf_le,
      vecU8At_eq_header_sep_buf A.repAlloc v cap1 ptr1 bs1]
  simp only [vecHeader, sepConj_assoc]
  by_cases hfit_cap : bs1.length + fBs.length ≤ cap1.toNat
  · have hhi := cmp_hi_false_of_le hfit_cap hcap1
    apply sepWPpLsCl_of_sepWP_vm (mid := lsρ lsMemcpySym)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm0 =>
          sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := st) hvm0 (by sep_focus) ?_⟩
      refine hCallMC sp0 v cap1 ptr1 fPtr ((blkPl_14).base + 400#64) bs1 fBs st
        hfit_cap hcap1 hptr1 hf_nil (s0 := s0)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by sep_focus) ?_
      intro sm _ hpcm hrunm hspm htrm hcsm
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
          ⟨by simp only [wp_norm, arm64_norm], fun hvmm' =>
            sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := st) hvmm' (by sep_focus) ?_⟩
        refine SepWPpLsCl.weaken_pre ?_ (hnext _ cap1 ptr1 []
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
          (encRawSegEnv_nil _ _))
        rw [vecU8At_open_src A.repAlloc (ss + 48#64) fCap fPtr fBs hf_nil hf_le,
            ← vecU8At_close_slice A.repAlloc v cap1 ptr1 bs1 fBs hfit_cap hcap1 hptr1 hf_nil]
        simp only [sepConj_assoc]
        exact entails_of_sep_focus (by sep_focus)
  · have hhi := cmp_hi_true_of_gt (add := fBs.length) hle1 (by omega) hcap1 (by omega)
    have hfitDR : FitsEnv M lim st (DoReserveEnv (DoReserveCall.mk v cap1 ptr1 bs1 fBs.length)) :=
      fitsEnv_doReserve_of_encRawSeg hf_pos (by dsimp only; omega)
        (by dsimp only; omega) hlen_lt hfit
    apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 13)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm0 =>
          sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := st) hvm0 (by sep_focus) ?_⟩
      refine hCallDR sp0 v cap1 ptr1 ((blkPl_14).base + 2036#64) bs1 fBs.length st
        (by omega) (by omega) hfitDR (s0 := s0)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by sep_focus) ?_
      intro s1 newCap p' evs hpc1 hrun1 hsp1 htr1 hcs1 hevs hnew_ge hnew_lt
      have hevs_seg : EncRawSegEnv bs1.length fBs.length evs :=
        (doReserveEnv_sub_boundedRustEvs (outLen := bs1.length + fBs.length)
          (by dsimp only; omega) (by dsimp only; omega) hlen_lt hevs).mono
          (by omega) (Nat.le_refl _)
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
        refine hCallMC sp0 v newCap p' fPtr ((blkPl_14).base + 400#64) bs1 fBs (M.stepEvents evs st)
          hnew_ge hnew_lt hp'_ne hf_nil (s0 := s0)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by sep_focus) ?_
        intro sm _ hpcm hrunm hspm htrm hcsm
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
          (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
            (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
        apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 408#64)
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [wp_norm, arm64_norm], fun hvmm' =>
              sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := M.stepEvents evs st) hvmm' (by sep_focus) ?_⟩
          refine SepWPpLsCl.weaken_pre ?_ (hnext _ newCap p' evs
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
            hevs_seg)
          rw [vecU8At_open_src A.repAlloc (ss + 48#64) fCap fPtr fBs hf_nil hf_le,
              ← vecU8At_close_slice A.repAlloc v newCap p' bs1 fBs hnew_ge hnew_lt hp'_ne hf_nil]
          simp only [sepConj_assoc]
          exact entails_of_sep_focus (by sep_focus)

theorem step_encraw_tag4_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (hDR : DoReservePlacedOkX M A lim H)
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (ss v sp0 fCap fPtr cap ptr : BitVec 64) (bs fBs : List (BitVec 8)) (st : M.σ)
    (hlen_lt : bs.length + 11 + fBs.length < 2 ^ 61)
    (hfit : FitsEnv M lim st (EncRawSegEnv bs.length (bytesField 4 fBs).length))
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
      A.pool lim st s ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_14).base + 408#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      EncRawSegEnv bs.length (bytesField 4 fBs).length evs →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((vecU8At A.repAlloc (ss + 48#64) fCap fPtr fBs ∗
          vecU8At A.repAlloc v cap' ptr' (bs ++ bytesField 4 fBs) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hCallDR := @encraw_call_doReserve_buf_placed_x _ M A lim H hDR
  have hCallEV := @encraw_call_encodeVarint_placed_x _ M A lim H hEV
  have hStepB := @step_encraw_tag4_b_placed_x _ M A lim H hC hDR
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
        ⟨by simp only [wp_norm, arm64_norm], fun hvmm =>
          sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := st) hvmm (by sep_focus) ?_⟩
      refine SepWPpLsCl.weaken_pre ?_ (hnext _ cap ptr []
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
        (encRawSegEnv_nil _ _))
      rw [vecU8At_Nil_off' A.repAlloc ss 48#64 56#64 64#64 fCap fPtr]
      simp only [bytesField_nil, List.append_nil, sepConj_assoc]
      exact entails_of_sep_focus (by sep_focus)
  · have hf_beq : (BitVec.ofNat 64 fBs.length == 0#64) = false :=
      ofNat64_len_beq_zero_false hf_nil (by omega)
    have hfield_eq : bs ++ bytesField 4 fBs =
        ((bs ++ [34#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) ++ fBs := by
      rw [bytesField_ne_nil (k := 34#8) hf_nil]; simp only [List.append_assoc]
    have hfield_len : (bytesField 4 fBs).length =
        (1 + (encodeVarint (BitVec.ofNat 64 fBs.length)).length) + fBs.length := by
      rw [bytesField_ne_nil (k := 34#8) hf_nil]
      simp only [List.length_append, List.length_singleton]
    have h10 := encodeVarint_length_le_10 (BitVec.ofNat 64 fBs.length)
    have hlen_bs1 :
        ((bs ++ [34#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)).length + fBs.length < 2 ^ 61 := by
      simp only [List.length_append, List.length_singleton]
      omega
    have hfit_hdr : FitsEnv M lim st
        (EncRawSegEnv bs.length (1 + (encodeVarint (BitVec.ofNat 64 fBs.length)).length)) := by
      have hf := hfit; rw [hfield_len] at hf
      exact fitsEnv_encRawSeg_left hf
    refine sepWPpLsCl_extract_vecU8At_bounds (A := A.repAlloc) (v := v) (cap := cap) (ptr := ptr) (bs := bs)
      (hfocus := by sep_focus) (h := fun hle _ _ => ?_)
    rw [vecU8At_open_src_off' A.repAlloc ss 48#64 56#64 64#64 fCap fPtr fBs hf_nil hf_le]
    by_cases hlt : bs.length < cap.toNat
    · have hbeq_cap := cap_beq_len_false hlt
      have hfitEV : FitsEnv M lim st
          (EncodeVarintEnv ⟨BitVec.ofNat 64 fBs.length, v, cap, ptr, bs ++ [34#8]⟩) :=
        fitsEnv_encodeVarint_of_encRawSeg (by dsimp only; omega)
          (by simp only [List.length_append, List.length_singleton]; omega)
          (by omega) hfit_hdr
      rw [vecU8At_open_one A.repAlloc v cap ptr bs hlt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPpLsCl.exists_elim fun old => ?_
      apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm], fun hvm0 =>
            sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := st) hvm0 (by sep_focus) ?_⟩
        have hclose_one := vecU8At_close_one A.repAlloc v cap ptr bs 34#8 hlt
        refine SepWPpLsCl.weaken_pre (P' :=
            (vecU8At A.repAlloc v cap ptr (bs ++ [34#8]) ∗ A.pool lim st _ ∗
              stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
              (vecU8At A.repAlloc (ss + 48#64) fCap fPtr fBs ∗ F))
          (by
            rw [← hclose_one, vecU8At_open_src_off' A.repAlloc ss 48#64 56#64 64#64 fCap fPtr fBs hf_nil hf_le]
            simp only [sepConj_assoc]
            exact entails_of_sep_focus (by sep_focus)) ?_
        refine hCallEV sp0 (BitVec.ofNat 64 fBs.length) v cap ptr ((blkPl_14).base + 360#64)
          (bs ++ [34#8]) st (by simp; omega) hfitEV (s0 := s0)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by sep_focus) ?_
        intro s1 cap1 ptr1 evs1 hpc1 hrun1 hsp1 htr1 hcs1 hevs1
        have hevs1_hdr : EncRawSegEnv bs.length
            (1 + (encodeVarint (BitVec.ofNat 64 fBs.length)).length) evs1 :=
          (encodeVarintEnv_sub_boundedRustEvs
            (outLen := bs.length + (1 + (encodeVarint (BitVec.ofNat 64 fBs.length)).length))
            (by simp only [List.length_append, List.length_singleton]; omega)
            (by omega) hevs1).mono (by dsimp only; omega) (Nat.le_refl _)
        have hfitB : FitsEnv M lim (M.stepEvents evs1 st)
            (EncRawSegEnv ((bs ++ [34#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)).length fBs.length) := by
          have hf := hfit; rw [hfield_len] at hf
          have h := fitsEnv_encRawSeg_right hf hevs1_hdr
          have hlen_eq : bs.length + (1 + (encodeVarint (BitVec.ofNat 64 fBs.length)).length) =
              ((bs ++ [34#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)).length := by
            simp only [List.length_append, List.length_singleton]; omega
          rwa [← hlen_eq]
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
          ((bs ++ [34#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) fBs
          (M.stepEvents evs1 st)
          hf_nil hf_le hf_cap hlen_bs1 hfitB hpc1 hrun1 hsp1 halign htr1
          hx19_1 hx20_1 hx21_1 hx22_1 hcs_1 (by sep_focus) ?_
        intro sm cap' ptr' evs2 hpcm hrunm hspm htrm hx19m hx20m hcsm' hevs2
        have hevs_all : EncRawSegEnv bs.length (bytesField 4 fBs).length (evs1 ++ evs2) := by
          rw [hfield_len]
          refine encRawSegEnv_append hevs1_hdr ?_
          have hlen_eq : bs.length + (1 + (encodeVarint (BitVec.ofNat 64 fBs.length)).length) =
              ((bs ++ [34#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)).length := by
            simp only [List.length_append, List.length_singleton]; omega
          rwa [hlen_eq]
        rw [← hfield_eq]
        refine SepWPpLsCl.weaken_pre ?_ (hnext sm cap' ptr' (evs1 ++ evs2) hpcm hrunm hspm htrm hx19m hx20m hcsm' hevs_all)
        rw [← M.stepEvents_append]
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
        refine hCallDR sp0 v cap ptr ((blkPl_14).base + 2004#64) bs 1 st
          (by omega) (by omega) hfitDR (s0 := s0)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by sep_focus) ?_
        intro s1 newCap p' evs1 hpc1 hrun1 hsp1 htr1 hcs1 hevs1 hnew_ge _
        have hevs1_seg : EncRawSegEnv bs.length 1 evs1 :=
          (doReserveEnv_sub_boundedRustEvs (outLen := bs.length + 1)
            (by dsimp only; omega) (by dsimp only; omega) (by omega) hevs1).mono
            (by omega) (Nat.le_refl _)
        have hfit2 : FitsEnv M lim (M.stepEvents evs1 st)
            (EncRawSegEnv (bs.length + 1) (encodeVarint (BitVec.ofNat 64 fBs.length)).length) :=
          fitsEnv_encRawSeg_right hfit_hdr hevs1_seg
        have hfitEV : FitsEnv M lim (M.stepEvents evs1 st)
            (EncodeVarintEnv ⟨BitVec.ofNat 64 fBs.length, v, newCap, p', bs ++ [34#8]⟩) :=
          fitsEnv_encodeVarint_of_encRawSeg (by dsimp only; omega)
            (by simp only [List.length_append, List.length_singleton]; omega)
            (by omega) hfit2
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
              sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := M.stepEvents evs1 st) hvm2 (by sep_focus) ?_⟩
          have hclose_one := vecU8At_close_one A.repAlloc v newCap p' bs 34#8 hnew_gt
          refine SepWPpLsCl.weaken_pre (P' :=
              (vecU8At A.repAlloc v newCap p' (bs ++ [34#8]) ∗
                A.pool lim (M.stepEvents evs1 st) _ ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
                (vecU8At A.repAlloc (ss + 48#64) fCap fPtr fBs ∗ F))
            (by
              rw [← hclose_one, vecU8At_open_src_off' A.repAlloc ss 48#64 56#64 64#64 fCap fPtr fBs hf_nil hf_le]
              simp only [sepConj_assoc]
              exact entails_of_sep_focus (by sep_focus)) ?_
          refine hCallEV sp0 (BitVec.ofNat 64 fBs.length) v newCap p' ((blkPl_14).base + 360#64)
            (bs ++ [34#8]) (M.stepEvents evs1 st) (by simp; omega) hfitEV (s0 := s0)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by sep_focus) ?_
          intro s2 cap1 ptr1 evs2 hpc2 hrun2 hsp2 htr2 hcs2 hevs2
          have hevs2_seg : EncRawSegEnv (bs.length + 1)
              (encodeVarint (BitVec.ofNat 64 fBs.length)).length evs2 :=
            (encodeVarintEnv_sub_boundedRustEvs
              (outLen := (bs.length + 1) + (encodeVarint (BitVec.ofNat 64 fBs.length)).length)
              (by simp only [List.length_append, List.length_singleton]; omega)
              (by omega) hevs2).mono (by dsimp only; omega) (Nat.le_refl _)
          have hevs12_hdr : EncRawSegEnv bs.length
              (1 + (encodeVarint (BitVec.ofNat 64 fBs.length)).length) (evs1 ++ evs2) :=
            encRawSegEnv_append hevs1_seg hevs2_seg
          have hfitB : FitsEnv M lim (M.stepEvents evs2 (M.stepEvents evs1 st))
              (EncRawSegEnv ((bs ++ [34#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)).length fBs.length) := by
            have hf := hfit; rw [hfield_len] at hf
            have h := fitsEnv_encRawSeg_right hf hevs12_hdr
            rw [← M.stepEvents_append]
            have hlen_eq : bs.length + (1 + (encodeVarint (BitVec.ofNat 64 fBs.length)).length) =
                ((bs ++ [34#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)).length := by
              simp only [List.length_append, List.length_singleton]; omega
            rwa [← hlen_eq]
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
          refine hStepB ss v sp0 fCap fPtr cap1 ptr1
            ((bs ++ [34#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) fBs
            (M.stepEvents evs2 (M.stepEvents evs1 st))
            hf_nil hf_le hf_cap hlen_bs1 hfitB hpc2 hrun2 hsp2 halign htr2
            hx19_2 hx20_2 hx21_2 hx22_2 hcs_2 (by sep_focus) ?_
          intro sm cap' ptr' evs3 hpcm hrunm hspm htrm hx19m hx20m hcsm' hevs3
          have hevs_all : EncRawSegEnv bs.length (bytesField 4 fBs).length ((evs1 ++ evs2) ++ evs3) := by
            rw [hfield_len]
            refine encRawSegEnv_append hevs12_hdr ?_
            have hlen_eq : bs.length + (1 + (encodeVarint (BitVec.ofNat 64 fBs.length)).length) =
                ((bs ++ [34#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)).length := by
              simp only [List.length_append, List.length_singleton]; omega
            rwa [hlen_eq]
          rw [← hfield_eq]
          refine SepWPpLsCl.weaken_pre ?_ (hnext sm cap' ptr' ((evs1 ++ evs2) ++ evs3) hpcm hrunm hspm htrm hx19m hx20m hcsm' hevs_all)
          simp only [← M.stepEvents_append]
          exact entails_of_sep_focus (by sep_focus)

theorem step_encraw_tag5_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hDR : DoReservePlacedOkX M A lim H)
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (ss v sp0 cap ptr : BitVec 64) (prevCnt : BitVec 32) (bs : List (BitVec 8)) (st : M.σ)
    (hlen_lt : bs.length + 11 < 2 ^ 61)
    (hfit : FitsEnv M lim st (EncRawSegEnv bs.length (uint32Field 5 prevCnt).length))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 408#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (((ss + 332#64) ↦₃₂ prevCnt) ∗ vecU8At A.repAlloc v cap ptr bs ∗ A.pool lim st s ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_14).base + 460#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      EncRawSegEnv bs.length (uint32Field 5 prevCnt).length evs →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((((ss + 332#64) ↦₃₂ prevCnt) ∗ vecU8At A.repAlloc v cap' ptr' (bs ++ uint32Field 5 prevCnt) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hCallDR := @encraw_call_doReserve_placed_x _ M A lim H hDR
  have hCallEV := @encraw_call_encodeVarint_placed_x _ M A lim H hEV
  rw [hP]
  by_cases hver : prevCnt = 0#32
  · subst hver
    simp only [sepConj_assoc]
    apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 460#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvmm =>
          sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := st) hvmm (by sep_focus) ?_⟩
      refine SepWPpLsCl.weaken_pre ?_ (hnext _ cap ptr []
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
        (encRawSegEnv_nil _ _))
      simp only [uint32Field_zero, List.append_nil, sepConj_assoc]
      exact entails_of_sep_focus (by sep_focus)
  · have hver_beq : (prevCnt == 0#32) = false := bv32_beq_zero_false hver
    have hfield_eq : bs ++ uint32Field 5 prevCnt =
        (bs ++ [40#8]) ++ encodeVarint (BitVec.zeroExtend 64 prevCnt) := by
      rw [uint32Field_ne_zero (k := 40#8) hver, List.append_assoc]
    have hfield_len : (uint32Field 5 prevCnt).length =
        1 + (encodeVarint (BitVec.zeroExtend 64 prevCnt)).length := by
      rw [uint32Field_ne_zero (k := 40#8) hver, List.length_append, List.length_singleton]
    have h10 := encodeVarint_length_le_10 (BitVec.zeroExtend 64 prevCnt)
    refine sepWPpLsCl_extract_vecU8At_bounds (A := A.repAlloc) (v := v) (cap := cap) (ptr := ptr) (bs := bs)
      (hfocus := by sep_focus) (h := fun hle _ _ => ?_)
    by_cases hlt : bs.length < cap.toNat
    · have hbeq_cap := cap_beq_len_false hlt
      have hfitEV : FitsEnv M lim st
          (EncodeVarintEnv ⟨BitVec.zeroExtend 64 prevCnt, v, cap, ptr, bs ++ [40#8]⟩) :=
        fitsEnv_encodeVarint_of_encRawSeg (by dsimp only; omega)
          (by simp only [List.length_append, List.length_singleton]; omega)
          (by omega) hfit
      rw [vecU8At_open_one A.repAlloc v cap ptr bs hlt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPpLsCl.exists_elim fun old => ?_
      apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm], fun hvm0 =>
            sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := st) hvm0 (by sep_focus) ?_⟩
        have hclose := vecU8At_close_one A.repAlloc v cap ptr bs 40#8 hlt
        refine SepWPpLsCl.weaken_pre (P' :=
            (vecU8At A.repAlloc v cap ptr (bs ++ [40#8]) ∗ A.pool lim st _ ∗
              stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ (((ss + 332#64) ↦₃₂ prevCnt) ∗ F))
          (by rw [← hclose]; exact entails_of_sep_focus (by sep_focus)) ?_
        refine hCallEV sp0 (BitVec.zeroExtend 64 prevCnt) v cap ptr ((blkPl_14).base + 460#64)
          (bs ++ [40#8]) st (by simp; omega) hfitEV (s0 := s0)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by sep_focus) ?_
        intro sm cap' ptr' evs hpcm hrunm hspm htrm hcsm hevs
        have hevs_seg : EncRawSegEnv bs.length (uint32Field 5 prevCnt).length evs :=
          (encodeVarintEnv_sub_boundedRustEvs
            (outLen := bs.length + (uint32Field 5 prevCnt).length)
            (by simp only [List.length_append, List.length_singleton]; omega)
            (by omega) hevs).mono (by dsimp only; omega) (Nat.le_refl _)
        have hx19m : sm.readReg64 .x19 = v := by
          have := hcsm.1; simp only [arm64_norm, *] at this; exact this
        have hx20m : sm.readReg64 .x20 = ss := by
          have := hcsm.2.1; simp only [arm64_norm, *] at this; exact this
        have hcsm' : EncRawUpperSaved s0 sm :=
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
            (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
        rw [← hfield_eq]
        refine SepWPpLsCl.weaken_pre ?_ (hnext sm cap' ptr' evs hpcm hrunm hspm htrm hx19m hx20m hcsm' hevs_seg)
        exact entails_of_sep_focus (by sep_focus)
    · have hcap_eq : cap.toNat = bs.length := by omega
      have hcap_bv := cap_eq_ofNat_len hcap_eq
      have hfit1 : FitsEnv M lim st (EncRawSegEnv bs.length 1) := by
        rw [hfield_len] at hfit; exact fitsEnv_encRawSeg_left hfit
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
        refine SepWPpLsCl.weaken_pre (P' :=
            (vecU8At A.repAlloc v cap ptr bs ∗ A.pool lim st _ ∗
              stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ (((ss + 332#64) ↦₃₂ prevCnt) ∗ F))
          (by rw [vecU8At_eq_header_sep_buf]; simp only [vecHeader, sepConj_assoc]
              exact entails_of_sep_focus (by sep_focus)) ?_
        have hx1_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        refine hCallDR sp0 v cap ptr ((blkPl_14).base + 2112#64) bs 1 st
          (by omega) (by omega) hfitDR (s0 := s0)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by sep_focus) ?_
        intro s1 newCap p' evs1 hpc1 hrun1 hsp1 htr1 hcs1 hevs1 hnew_ge _
        have hevs1_seg : EncRawSegEnv bs.length 1 evs1 :=
          (doReserveEnv_sub_boundedRustEvs (outLen := bs.length + 1)
            (by dsimp only; omega) (by dsimp only; omega) (by omega) hevs1).mono
            (by omega) (Nat.le_refl _)
        have hfit2 : FitsEnv M lim (M.stepEvents evs1 st)
            (EncRawSegEnv (bs.length + 1) (encodeVarint (BitVec.zeroExtend 64 prevCnt)).length) := by
          have hf := hfit; rw [hfield_len] at hf
          exact fitsEnv_encRawSeg_right hf hevs1_seg
        have hfitEV : FitsEnv M lim (M.stepEvents evs1 st)
            (EncodeVarintEnv ⟨BitVec.zeroExtend 64 prevCnt, v, newCap, p', bs ++ [40#8]⟩) :=
          fitsEnv_encodeVarint_of_encRawSeg (by dsimp only; omega)
            (by simp only [List.length_append, List.length_singleton]; omega)
            (by omega) hfit2
        have hx19_1 : s1.readReg64 .x19 = v := by
          have := hcs1.1; simp only [arm64_norm, *] at this; exact this
        have hx20_1 : s1.readReg64 .x20 = ss := by
          have := hcs1.2.1; simp only [arm64_norm, *] at this; exact this
        have hx21_1 : s1.readReg64 .x21 = BitVec.zeroExtend 64 prevCnt := by
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
          have hclose := vecU8At_close_one A.repAlloc v newCap p' bs 40#8 hnew_gt
          refine SepWPpLsCl.weaken_pre (P' :=
              (vecU8At A.repAlloc v newCap p' (bs ++ [40#8]) ∗
                A.pool lim (M.stepEvents evs1 st) _ ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
                (((ss + 332#64) ↦₃₂ prevCnt) ∗ F))
            (by rw [← hclose]; exact entails_of_sep_focus (by sep_focus)) ?_
          refine hCallEV sp0 (BitVec.zeroExtend 64 prevCnt) v newCap p' ((blkPl_14).base + 460#64)
            (bs ++ [40#8]) (M.stepEvents evs1 st) (by simp; omega) hfitEV (s0 := s0)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by sep_focus) ?_
          intro sm cap' ptr' evs2 hpcm hrunm hspm htrm hcsm hevs2
          have hevs2_seg : EncRawSegEnv (bs.length + 1)
              (encodeVarint (BitVec.zeroExtend 64 prevCnt)).length evs2 :=
            (encodeVarintEnv_sub_boundedRustEvs
              (outLen := (bs.length + 1) + (encodeVarint (BitVec.zeroExtend 64 prevCnt)).length)
              (by simp only [List.length_append, List.length_singleton]; omega)
              (by omega) hevs2).mono (by dsimp only; omega) (Nat.le_refl _)
          have hevs_all : EncRawSegEnv bs.length (uint32Field 5 prevCnt).length (evs1 ++ evs2) := by
            rw [hfield_len]; exact encRawSegEnv_append hevs1_seg hevs2_seg
          have hx19m : sm.readReg64 .x19 = v := by
            have := hcsm.1; simp only [arm64_norm, *] at this; exact this
          have hx20m : sm.readReg64 .x20 = ss := by
            have := hcsm.2.1; simp only [arm64_norm, *] at this; exact this
          have hcsm' : EncRawUpperSaved s0 sm :=
            (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
              (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
          rw [← hfield_eq]
          refine SepWPpLsCl.weaken_pre ?_ (hnext sm cap' ptr' (evs1 ++ evs2) hpcm hrunm hspm htrm hx19m hx20m hcsm' hevs_all)
          rw [← M.stepEvents_append]
          exact entails_of_sep_focus (by sep_focus)

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.RemoteIdentityRootKeyCounterXPlacedBudget
