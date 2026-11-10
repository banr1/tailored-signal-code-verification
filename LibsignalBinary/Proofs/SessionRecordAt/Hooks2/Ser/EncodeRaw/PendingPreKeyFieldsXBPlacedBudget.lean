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
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.PendingPreKeyFields
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.PendingPreKeyHeader
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.BaseXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.BaseX
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.BaseXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PendingPreKeyFieldsXAPlacedBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PendingPreKeyFieldsXBPlaced
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PendingPreKeyFieldsXBPlacedBudgetAux
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PrologueVersionLocalIdentityXPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.E2E.Record.Serialization.ChainLenAux.Pure
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.SenderReceiverChains
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PendingPreKeyFieldsXB
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `SessionStructure::encode_raw` Tag 9: `pending_pre_key` (`536` → `1080`)

Verifies subfields 3 (`signed_pre_key_id`) and 4 (`timestamp`) and assembles the combined protobuf
tag 9 (`pending_pre_key`, Block `14` offsets `536..1080`) under `RustCliAllocBudget M` and
`EncRawSegEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PendingPreKeyFieldsXBPlacedBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSessionApi (PendingPreKey)
open CryptoVerification (LibsignalPlacement LibsignalHooks lsmpl)
open CryptoVerification.RustHeap (vecHeader vecU8At)
open CryptoVerification.LibsignalTripleRatchetRepr (TailVecGhost optTailVecAt)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  vecU8Buf vecU8At_eq_header_sep_buf cap_beq_len_false cap_eq_ofNat_len
)
open CryptoVerification.E2E.Record (
  optUint32Field int32Field uint64Field PendingRel
)
open CryptoVerification.E2E.Record.Placed (blkPl_14 lsProg_14)
open CryptoVerification.E2E.Record.Serialization (
  encodeRawSubStackX encPendingMem encPendingFieldMem sepWPpLsCl_extract_vecU8At_bounds
)
open CryptoVerification.E2E.Record.Serialization.EncodeRawAux (
  entails_of_sep_focus EncRawUpperSaved
  vecSrcRest vecCopyDone optU32ValAt pendingTailRest pendingOpenAt
  optTailVecAt_pending_none_eq optTailVecAt_pending_some_eq_open
  publicKey_deserialize_ne_nil optUint32Field1_length_le int32Field3_length_le
  int32Field3_zero_eq int32Field3_nonzero_eq zext64_beq_zero_false_3b
  uint64Field4_zero_eq uint64Field4_nonzero_eq
  lenField9_eq bytesField2_nonempty_eq
  bv64_beq_zero_false truncate32_signExtend64_er bv_add_neg80_3b
  vecU8At_open_one vecU8At_close_one
  sp_sub_80_spAligned encodeVarint_length_le_10
)
open Proofs.libsignal.Hooks2 (SepWPpLsCl)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (DoReserveEnv)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget (EncodeVarintEnv)
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
  encraw_call_encodeVarint_placed_x
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PrologueVersionLocalIdentityXPlacedBudget (
  encraw_call_doReserve_buf_placed_x
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PendingPreKeyFieldsXAPlacedBudget (
  step_tag9_sub1_placed_x step_tag9_sub2_a_placed_x step_tag9_sub2_b_placed_x
)

abbrev sepWPpLsCl_extract_pending_some :=
  @CryptoVerification.E2E.Record.Serialization.sepWPpLsCl_extract_pending_some
abbrev step_tag9_write_tag_placed_x :=
  @PendingPreKeyFieldsXBPlacedBudgetAux.step_tag9_write_tag_placed_x
abbrev step_tag9_len1_placed_x :=
  @PendingPreKeyFieldsXBPlacedBudgetAux.step_tag9_len1_placed_x
abbrev step_tag9_len2_placed_x :=
  @PendingPreKeyFieldsXBPlacedBudgetAux.step_tag9_len2_placed_x
abbrev step_tag9_len3_placed_x :=
  @PendingPreKeyFieldsXBPlacedBudgetAux.step_tag9_len3_placed_x
abbrev step_tag9_len4_placed_x :=
  @PendingPreKeyFieldsXBPlacedBudgetAux.step_tag9_len4_placed_x

set_option allowUnsafeReducibility true in
attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
  stackAt vecU8Buf vecSrcRest vecCopyDone optU32ValAt pendingTailRest

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  truncate32_signExtend64_er truncate32_zeroExtend64 bv_add_neg80_3b

/-! ## Subfield 3 (`signed_pre_key_id`, `976 → 1028`, cold `2564..2592`) -/

theorem step_tag9_sub3_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (hDR : DoReservePlacedOkX M A lim H)
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (bs : List (BitVec 8))
    (st : M.σ)
    (hlen_lt : bs.length + 12 < 2 ^ 60)
    (hfit : FitsEnv M lim st (EncRawSegEnv bs.length (int32Field 3 p.signedPreKeyId).length))
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
      A.pool lim st s ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_14).base + 1028#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x21 = p.timestamp →
      EncRawUpperSaved s0 sm →
      EncRawSegEnv bs.length (int32Field 3 p.signedPreKeyId).length evs →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((pendingOpenAt A.repAlloc ss g p ∗
          vecU8At A.repAlloc v cap' ptr' (bs ++ int32Field 3 p.signedPreKeyId) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hCallEV := @encraw_call_encodeVarint_placed_x _ M A lim H hEV
  have hCallDR := @encraw_call_doReserve_buf_placed_x _ M A lim H hDR
  rw [hP]
  by_cases hspk : p.signedPreKeyId = 0#32
  · simp only [sepConj_assoc]
    apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 1028#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm_end =>
          sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := st) hvm_end (by sep_focus) ?_⟩
      refine SepWPpLsCl.weaken_pre ?_ (hnext _ cap ptr []
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
        (by rw [hspk, int32Field3_zero_eq]; exact encRawSegEnv_nil _ _))
      simp only [hspk, int32Field3_zero_eq, List.append_nil, sepConj_assoc]
      exact entails_of_sep_focus (by sep_focus)
  · have hbeq0 := zext64_beq_zero_false_3b hspk
    have hflen : (int32Field 3 p.signedPreKeyId).length =
        1 + (encodeVarint (BitVec.signExtend 64 p.signedPreKeyId)).length := by
      rw [← int32Field3_nonzero_eq hspk]
      simp only [List.length_append, List.length_singleton]
    have hvlen10 := encodeVarint_length_le_10 (BitVec.signExtend 64 p.signedPreKeyId)
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
            (EncodeVarintEnv ⟨BitVec.signExtend 64 p.signedPreKeyId, v, cap, ptr, bs ++ [24#8]⟩) :=
          fitsEnv_encodeVarint_of_encRawSeg (by dsimp only; omega)
            (by simp only [List.length_append, List.length_singleton]; omega)
            (by omega) hfit
        refine SepWPpLsCl.weaken_pre
          (P' := (vecU8At A.repAlloc v cap ptr (bs ++ [24#8]) ∗
              A.pool lim st _ ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
            pendingOpenAt A.repAlloc ss g p ∗ F)
          (by
            rw [← vecU8At_close_one A.repAlloc v cap ptr bs 24#8 hlt]
            simp only [sepConj_assoc]
            exact entails_of_sep_focus (by sep_focus))
          (hCallEV sp0 (BitVec.signExtend 64 p.signedPreKeyId) v cap ptr ((blkPl_14).base + 1028#64)
            (bs ++ [24#8]) st (by simp; omega) hfitEV (s0 := s0)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by sep_focus) ?_)
        intro s1 cap' ptr' evs hpc1 hrun1 hsp1 htr1 hcs1 hevs
        have hevs_seg : EncRawSegEnv bs.length (int32Field 3 p.signedPreKeyId).length evs :=
          (encodeVarintEnv_sub_boundedRustEvs
            (outLen := bs.length + (int32Field 3 p.signedPreKeyId).length)
            (by simp only [List.length_append, List.length_singleton]; omega)
            (by omega) hevs).mono (by dsimp only; omega) (Nat.le_refl _)
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
          (hnext s1 cap' ptr' evs hpc1 hrun1 hsp1 htr1
            hx19_1 hx20_1 hx21_1 hcs_1 hevs_seg)
        rw [List.append_assoc, int32Field3_nonzero_eq hspk]
        simp only [sepConj_assoc]
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
        refine hCallDR sp0 v cap ptr ((blkPl_14).base + 2584#64) bs 1 st
          (by omega) (by omega) hfitDR (s0 := s0)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by sep_focus) ?_
        intro s1 newCap p1 evs1 hpc1 hrun1 hsp1 htr1 hcs1 hevs1 hnew_ge _
        have he1_seg : EncRawSegEnv bs.length 1 evs1 :=
          (doReserveEnv_sub_boundedRustEvs (outLen := bs.length + 1)
            (by dsimp only; omega) (by dsimp only; omega) (by omega) hevs1).mono
            (by omega) (Nat.le_refl _)
        have hfit2 : FitsEnv M lim (M.stepEvents evs1 st)
            (EncRawSegEnv (bs.length + 1)
              (encodeVarint (BitVec.signExtend 64 p.signedPreKeyId)).length) :=
          fitsEnv_encRawSeg_right hfit he1_seg
        have hx19_1 : s1.readReg64 .x19 = v := by
          have := hcs1.1; simp only [arm64_norm, *] at this; exact this
        have hx20_1 : s1.readReg64 .x20 = ss := by
          have := hcs1.2.1; simp only [arm64_norm, *] at this; exact this
        have hx21_1 : s1.readReg64 .x21 = p.timestamp := by
          have := hcs1.2.2.1; simp only [arm64_norm, *] at this; exact this
        have hx22_1 : s1.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId := by
          have := hcs1.2.2.2.1; simp only [arm64_norm, *] at this; exact this
        have hcs_1 : EncRawUpperSaved s0 s1 :=
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
            (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
        have hlt_new : bs.length < newCap.toNat := by omega
        rw [vecU8At_open_one A.repAlloc v newCap p1 bs hlt_new]
        simp only [sepExists_sepConj_left, sepConj_assoc]
        refine SepWPpLsCl.exists_elim fun old => ?_
        apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [wp_norm, arm64_norm], fun hvm2 =>
              sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := M.stepEvents evs1 st) hvm2 (by sep_focus) ?_⟩
          have hfitEV : FitsEnv M lim (M.stepEvents evs1 st)
              (EncodeVarintEnv ⟨BitVec.signExtend 64 p.signedPreKeyId, v, newCap, p1, bs ++ [24#8]⟩) :=
            fitsEnv_encodeVarint_of_encRawSeg (by dsimp only; omega)
              (by simp only [List.length_append, List.length_singleton]; omega)
              (by omega) hfit2
          refine SepWPpLsCl.weaken_pre
            (P' := (vecU8At A.repAlloc v newCap p1 (bs ++ [24#8]) ∗
                A.pool lim (M.stepEvents evs1 st) _ ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
              pendingOpenAt A.repAlloc ss g p ∗ F)
            (by
              rw [← vecU8At_close_one A.repAlloc v newCap p1 bs 24#8 hlt_new]
              simp only [sepConj_assoc]
              exact entails_of_sep_focus (by sep_focus))
            (hCallEV sp0 (BitVec.signExtend 64 p.signedPreKeyId) v newCap p1 ((blkPl_14).base + 1028#64)
              (bs ++ [24#8]) (M.stepEvents evs1 st) (by simp; omega) hfitEV (s0 := s0)
              (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by sep_focus) ?_)
          intro s2 cap' ptr' evs2 hpc2 hrun2 hsp2 htr2 hcs2 hevs2
          have he2_seg : EncRawSegEnv (bs.length + 1)
              (encodeVarint (BitVec.signExtend 64 p.signedPreKeyId)).length evs2 :=
            (encodeVarintEnv_sub_boundedRustEvs
              (outLen := (bs.length + 1) +
                (encodeVarint (BitVec.signExtend 64 p.signedPreKeyId)).length)
              (by simp only [List.length_append, List.length_singleton]; omega)
              (by omega) hevs2).mono (by dsimp only; omega) (Nat.le_refl _)
          have he12 : EncRawSegEnv bs.length (int32Field 3 p.signedPreKeyId).length (evs1 ++ evs2) := by
            rw [hflen]; exact encRawSegEnv_append he1_seg he2_seg
          have hx19_2 : s2.readReg64 .x19 = v := by
            have := hcs2.1; simp only [arm64_norm, *] at this; exact this
          have hx20_2 : s2.readReg64 .x20 = ss := by
            have := hcs2.2.1; simp only [arm64_norm, *] at this; exact this
          have hx21_2 : s2.readReg64 .x21 = p.timestamp := by
            have := hcs2.2.2.1; simp only [arm64_norm, *] at this; exact this
          have hcs_2 : EncRawUpperSaved s0 s2 :=
            (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
              (EncRawUpperSaved.of_calleeSavedPreserved hcs2)
          rw [← M.stepEvents_append]
          refine SepWPpLsCl.weaken_pre ?_
            (hnext s2 cap' ptr' (evs1 ++ evs2) hpc2 hrun2 hsp2 htr2
              hx19_2 hx20_2 hx21_2 hcs_2 he12)
          rw [List.append_assoc, int32Field3_nonzero_eq hspk]
          simp only [sepConj_assoc]
          exact entails_of_sep_focus (by sep_focus)

/-! ## Subfield 4 (`timestamp`, `1028 → 1080`, cold `2592..2620`) -/

theorem step_tag9_sub4_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (hDR : DoReservePlacedOkX M A lim H)
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (bs : List (BitVec 8))
    (st : M.σ)
    (hlen_lt : bs.length + 12 < 2 ^ 60)
    (hfit : FitsEnv M lim st (EncRawSegEnv bs.length (uint64Field 4 p.timestamp).length))
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
      A.pool lim st s ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_14).base + 1080#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      EncRawSegEnv bs.length (uint64Field 4 p.timestamp).length evs →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((pendingOpenAt A.repAlloc ss g p ∗
          vecU8At A.repAlloc v cap' ptr' (bs ++ uint64Field 4 p.timestamp) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hCallEV := @encraw_call_encodeVarint_placed_x _ M A lim H hEV
  have hCallDR := @encraw_call_doReserve_buf_placed_x _ M A lim H hDR
  rw [hP]
  by_cases hts : p.timestamp = 0#64
  · simp only [sepConj_assoc]
    apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 1080#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm_end =>
          sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := st) hvm_end (by sep_focus) ?_⟩
      refine SepWPpLsCl.weaken_pre ?_ (hnext _ cap ptr []
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
        (encRawSegEnv_nil _ _))
      simp only [hts, uint64Field4_zero_eq, List.append_nil, sepConj_assoc]
      exact entails_of_sep_focus (by sep_focus)
  · have hbeq0 := bv64_beq_zero_false hts
    have hfield_len : (uint64Field 4 p.timestamp).length =
        1 + (encodeVarint p.timestamp).length := by
      rw [← uint64Field4_nonzero_eq hts, List.length_append, List.length_singleton]
    have h10 := encodeVarint_length_le_10 p.timestamp
    refine sepWPpLsCl_extract_vecU8At_bounds (A := A.repAlloc) (v := v) (cap := cap) (ptr := ptr) (bs := bs)
      (hfocus := by sep_focus) (h := fun hle _ _ => ?_)
    by_cases hlt : bs.length < cap.toNat
    · have hbeq_cap := cap_beq_len_false hlt
      have hfitEV : FitsEnv M lim st
          (EncodeVarintEnv ⟨p.timestamp, v, cap, ptr, bs ++ [32#8]⟩) :=
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
        have hclose := vecU8At_close_one A.repAlloc v cap ptr bs 32#8 hlt
        refine SepWPpLsCl.weaken_pre (P' :=
            (vecU8At A.repAlloc v cap ptr (bs ++ [32#8]) ∗ A.pool lim st _ ∗
              stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
              (pendingOpenAt A.repAlloc ss g p ∗ F))
          (by
            rw [← hclose]
            exact entails_of_sep_focus (by sep_focus)) ?_
        refine hCallEV sp0 p.timestamp v cap ptr ((blkPl_14).base + 1080#64) (bs ++ [32#8]) st
          (by simp; omega) hfitEV (s0 := s0)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by sep_focus) ?_
        intro s1 cap' ptr' evs hpc1 hrun1 hsp1 htr1 hcs1 hevs
        have hevs_seg : EncRawSegEnv bs.length (uint64Field 4 p.timestamp).length evs :=
          (encodeVarintEnv_sub_boundedRustEvs
            (outLen := bs.length + (uint64Field 4 p.timestamp).length)
            (by simp only [List.length_append, List.length_singleton]; omega)
            (by omega) hevs).mono (by dsimp only; omega) (Nat.le_refl _)
        have hx19_1 : s1.readReg64 .x19 = v := by
          have := hcs1.1; simp only [arm64_norm, *] at this; exact this
        have hx20_1 : s1.readReg64 .x20 = ss := by
          have := hcs1.2.1; simp only [arm64_norm, *] at this; exact this
        have hcs_1 : EncRawUpperSaved s0 s1 :=
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
            (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
        refine SepWPpLsCl.weaken_pre ?_ (hnext s1 cap' ptr' evs hpc1 hrun1 hsp1 htr1
          hx19_1 hx20_1 hcs_1 hevs_seg)
        rw [List.append_assoc, uint64Field4_nonzero_eq hts]
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
        have hx1_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        refine hCallDR sp0 v cap ptr ((blkPl_14).base + 2612#64) bs 1 st
          (by omega) (by omega) hfitDR (s0 := s0)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by sep_focus) ?_
        intro s1 newCap p1 evs1 hpc1 hrun1 hsp1 htr1 hcs1 hevs1 hnew_ge _
        have hevs1_seg : EncRawSegEnv bs.length 1 evs1 :=
          (doReserveEnv_sub_boundedRustEvs (outLen := bs.length + 1)
            (by dsimp only; omega) (by dsimp only; omega) (by omega) hevs1).mono
            (by omega) (Nat.le_refl _)
        have hfit2 : FitsEnv M lim (M.stepEvents evs1 st)
            (EncRawSegEnv (bs.length + 1) (encodeVarint p.timestamp).length) := by
          have hf := hfit; rw [hfield_len] at hf
          exact fitsEnv_encRawSeg_right hf hevs1_seg
        have hfitEV : FitsEnv M lim (M.stepEvents evs1 st)
            (EncodeVarintEnv ⟨p.timestamp, v, newCap, p1, bs ++ [32#8]⟩) :=
          fitsEnv_encodeVarint_of_encRawSeg (by dsimp only; omega)
            (by simp only [List.length_append, List.length_singleton]; omega)
            (by omega) hfit2
        have hx19_1 : s1.readReg64 .x19 = v := by
          have := hcs1.1; simp only [arm64_norm, *] at this; exact this
        have hx20_1 : s1.readReg64 .x20 = ss := by
          have := hcs1.2.1; simp only [arm64_norm, *] at this; exact this
        have hx21_1 : s1.readReg64 .x21 = p.timestamp := by
          have := hcs1.2.2.1; simp only [arm64_norm, *] at this; exact this
        have hcs_1 : EncRawUpperSaved s0 s1 :=
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
            (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
        have hlt_new : bs.length < newCap.toNat := by omega
        rw [vecU8At_open_one A.repAlloc v newCap p1 bs hlt_new]
        simp only [sepExists_sepConj_left, sepConj_assoc]
        refine SepWPpLsCl.exists_elim fun old => ?_
        apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [wp_norm, arm64_norm], fun hvm2 =>
              sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := M.stepEvents evs1 st) hvm2 (by sep_focus) ?_⟩
          have hclose := vecU8At_close_one A.repAlloc v newCap p1 bs 32#8 hlt_new
          refine SepWPpLsCl.weaken_pre (P' :=
              (vecU8At A.repAlloc v newCap p1 (bs ++ [32#8]) ∗
                A.pool lim (M.stepEvents evs1 st) _ ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
                (pendingOpenAt A.repAlloc ss g p ∗ F))
            (by
              rw [← hclose]
              exact entails_of_sep_focus (by sep_focus)) ?_
          refine hCallEV sp0 p.timestamp v newCap p1 ((blkPl_14).base + 1080#64) (bs ++ [32#8])
            (M.stepEvents evs1 st) (by simp; omega) hfitEV (s0 := s0)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by sep_focus) ?_
          intro s2 cap' ptr' evs2 hpc2 hrun2 hsp2 htr2 hcs2 hevs2
          have hevs2_seg : EncRawSegEnv (bs.length + 1) (encodeVarint p.timestamp).length evs2 :=
            (encodeVarintEnv_sub_boundedRustEvs
              (outLen := (bs.length + 1) + (encodeVarint p.timestamp).length)
              (by simp only [List.length_append, List.length_singleton]; omega)
              (by omega) hevs2).mono (by dsimp only; omega) (Nat.le_refl _)
          have hevs_all : EncRawSegEnv bs.length (uint64Field 4 p.timestamp).length (evs1 ++ evs2) := by
            rw [hfield_len]; exact encRawSegEnv_append hevs1_seg hevs2_seg
          have hx19_2 : s2.readReg64 .x19 = v := by
            have := hcs2.1; simp only [arm64_norm, *] at this; exact this
          have hx20_2 : s2.readReg64 .x20 = ss := by
            have := hcs2.2.1; simp only [arm64_norm, *] at this; exact this
          have hcs_2 : EncRawUpperSaved s0 s2 :=
            (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
              (EncRawUpperSaved.of_calleeSavedPreserved hcs2)
          refine SepWPpLsCl.weaken_pre ?_ (hnext s2 cap' ptr' (evs1 ++ evs2) hpc2 hrun2 hsp2 htr2
            hx19_2 hx20_2 hcs_2 hevs_all)
          rw [List.append_assoc, uint64Field4_nonzero_eq hts, ← M.stepEvents_append]
          exact entails_of_sep_focus (by sep_focus)

/-! ## Combined Tag 9 (`pending_pre_key`, `536 → 1080`) -/

theorem step_encraw_tag9_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (hDR : DoReservePlacedOkX M A lim H)
    (ss v sp0 cap ptr : BitVec 64)
    (G_pending : Option TailVecGhost) (s_pending : Option PendingPreKey) (bs : List (BitVec 8))
    (st : M.σ)
    (hrel : PendingRel G_pending s_pending)
    (hbound : match G_pending with | none => True | some g => g.vec.bytes.length < 2 ^ 32)
    (hbs_lt : bs.length < 2 ^ 32)
    (hfit : FitsEnv M lim st
      (EncRawSegEnv bs.length (encPendingFieldMem G_pending s_pending).length))
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
      A.pool lim st s ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_14).base + 1080#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      EncRawSegEnv bs.length (encPendingFieldMem G_pending s_pending).length evs →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((optTailVecAt A.repAlloc 48 (ss + 248#64) G_pending ∗
          vecU8At A.repAlloc v cap' ptr' (bs ++ encPendingFieldMem G_pending s_pending) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
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
          ⟨by simp only [wp_norm, arm64_norm], fun hvm_end =>
            sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := st) hvm_end (by sep_focus) ?_⟩
        refine SepWPpLsCl.weaken_pre ?_ (hnext _ cap ptr []
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
          (encRawSegEnv_nil _ _))
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
      let d1 := 1
      let d2 := (encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)).length
      let d3 := (optUint32Field 1 p.preKeyId).length
      let d4 := ([18#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length)).length
      let d5 := g.vec.bytes.length
      let d6 := (int32Field 3 p.signedPreKeyId).length
      let d7 := (uint64Field 4 p.timestamp).length
      have htotal_len : (encPendingFieldMem (some g) (some p)).length =
          d1 + (d2 + (d3 + (d4 + (d5 + (d6 + d7))))) := by
        have hlen := congrArg List.length hbytes_eq
        simp only [List.length_append, List.length_singleton] at hlen
        simp only [d1, d2, d3, d4, d5, d6, d7, List.length_append, List.length_singleton]
        omega
      have hfit0 : FitsEnv M lim st
          (EncRawSegEnv bs.length (d1 + (d2 + (d3 + (d4 + (d5 + (d6 + d7))))))) := by
        rwa [← htotal_len]
      rw [hP]
      refine sepWPpLsCl_extract_pending_some (A := A.repAlloc) (ss := ss) (g := g)
        (hfocus := by sep_focus) (h := fun hlen24 hle_g hcap_g _ => ?_)
      have hopen := optTailVecAt_pending_some_eq_open A.repAlloc ss g p hlen24 hle_g hrel
      rw [hopen]
      refine step_tag9_write_tag_placed_x hDR ss v sp0 cap ptr g p bs st hcap_g (by omega)
        (fitsEnv_encRawSeg_left hfit0)
        hpc hrun hsp halign htr hx19 hx20 hcs (by sep_focus) ?_
      intro s1 cap1 ptr1 evs1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx24_1 hcs1 hevs1
      have hfit_r1 := fitsEnv_encRawSeg_right hfit0 hevs1
      refine step_tag9_len1_placed_x ss v sp0 g p hne_vec hlt_vec63
        hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx24_1 hcs1 (by sep_focus) ?_
      intro s2 hvm12 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx24_2 hx8_2 hx23_2 hcs2
      refine step_tag9_len2_placed_x ss v sp0 g p hne_vec
        hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx24_2 hx8_2 hx23_2 hcs2 (by sep_focus) ?_
      intro s3 hvm23 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx24_3 hx8_3 hx9_3 hx23_3 hx22_3 hcs3
      refine step_tag9_len3_placed_x ss v sp0 g p
        hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx24_3 hx8_3 hx9_3 hx23_3 hx22_3 hcs3 (by sep_focus) ?_
      intro s4 hvm34 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hx24_4 hx8_4 hx9_4 hx10_4 hx23_4 hx22_4 hx21_4 hcs4
      refine sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := M.stepEvents evs1 st)
        (hvm12.trans (hvm23.trans hvm34)) (by sep_focus) ?_
      refine step_tag9_len4_placed_x hEV ss v sp0 cap1 ptr1 g p bs (M.stepEvents evs1 st)
        (by omega) (fitsEnv_encRawSeg_left hfit_r1)
        hpc4 hrun4 hsp4 halign htr4 hx19_4 hx20_4 hx24_4 hx8_4 hx9_4 hx10_4 hx23_4 hx22_4 hx21_4 hcs4
        (by sep_focus) ?_
      intro s5 cap5 ptr5 evs2 hpc5 hrun5 hsp5 htr5 hx19_5 hx20_5 hx23_5 hx22_5 hx21_5 hcs5 hevs2
      have hfit_r2 : FitsEnv M lim (M.stepEvents evs2 (M.stepEvents evs1 st))
          (EncRawSegEnv ((bs ++ [74#8] ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)).length)
            (d3 + (d4 + (d5 + (d6 + d7))))) := by
        have h := fitsEnv_encRawSeg_right hfit_r1 hevs2
        have hlen_eq : (bs.length + d1) + d2 =
            (bs ++ [74#8] ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)).length := by
          simp only [List.length_append, List.length_singleton, d1, d2]
        rwa [← hlen_eq]
      refine step_tag9_sub1_placed_x hEV hDR ss v sp0 cap5 ptr5 g p
        ((bs ++ [74#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length))
        (M.stepEvents evs2 (M.stepEvents evs1 st))
        (by simp only [List.length_append, List.length_singleton]; omega)
        (fitsEnv_encRawSeg_left hfit_r2)
        hpc5 hrun5 hsp5 halign htr5 hx19_5 hx20_5 hx23_5 hx22_5 hx21_5 hcs5 (by sep_focus) ?_
      intro s6 cap6 ptr6 evs3 hpc6 hrun6 hsp6 htr6 hx19_6 hx20_6 hx23_6 hx22_6 hx21_6 hcs6 hevs3
      have hfit_r3 : FitsEnv M lim (M.stepEvents evs3 (M.stepEvents evs2 (M.stepEvents evs1 st)))
          (EncRawSegEnv
            ((((bs ++ [74#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ++
              optUint32Field 1 p.preKeyId).length)
            (d4 + (d5 + (d6 + d7)))) := by
        have h := fitsEnv_encRawSeg_right hfit_r2 hevs3
        have hlen_eq :
            ((bs ++ [74#8] ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)).length) + d3 =
            ((((bs ++ [74#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ++
              optUint32Field 1 p.preKeyId).length) := by
          simp only [List.length_append, d3]
        rwa [← hlen_eq]
      refine step_tag9_sub2_a_placed_x hEV hDR ss v sp0 cap6 ptr6 g p
        (((bs ++ [74#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ++
          optUint32Field 1 p.preKeyId)
        (M.stepEvents evs3 (M.stepEvents evs2 (M.stepEvents evs1 st)))
        hne_vec hlt_vec63
        (by simp only [List.length_append, List.length_singleton]; omega)
        (fitsEnv_encRawSeg_left hfit_r3)
        hpc6 hrun6 hsp6 halign htr6 hx19_6 hx20_6 hx23_6 hx22_6 hx21_6 hcs6 (by sep_focus) ?_
      intro s7 cap7 ptr7 evs4 hpc7 hrun7 hsp7 htr7 hx19_7 hx20_7 hx24_7 hx23_7 hx22_7 hx21_7 hcs7 hevs4
      have hfit_r4 : FitsEnv M lim
          (M.stepEvents evs4 (M.stepEvents evs3 (M.stepEvents evs2 (M.stepEvents evs1 st))))
          (EncRawSegEnv
            (((((bs ++ [74#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ++
              optUint32Field 1 p.preKeyId) ++
              ([18#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length))).length)
            (d5 + (d6 + d7))) := by
        have h := fitsEnv_encRawSeg_right hfit_r3 hevs4
        have hlen_eq :
            ((((bs ++ [74#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ++
              optUint32Field 1 p.preKeyId).length) + d4 =
            (((((bs ++ [74#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ++
              optUint32Field 1 p.preKeyId) ++
              ([18#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length))).length) := by
          simp only [List.length_append, List.length_singleton, d4]
        rwa [← hlen_eq]
      refine step_tag9_sub2_b_placed_x hDR hC ss v sp0 cap7 ptr7 g p
        ((((bs ++ [74#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ++
          optUint32Field 1 p.preKeyId) ++
          ([18#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length)))
        (M.stepEvents evs4 (M.stepEvents evs3 (M.stepEvents evs2 (M.stepEvents evs1 st))))
        hne_vec
        (by simp only [List.length_append, List.length_singleton]; omega)
        (fitsEnv_encRawSeg_left hfit_r4)
        hpc7 hrun7 hsp7 halign htr7 hx19_7 hx20_7 hx24_7 hx23_7 hx22_7 hx21_7 hcs7 (by sep_focus) ?_
      intro s8 cap8 ptr8 evs5 hpc8 hrun8 hsp8 htr8 hx19_8 hx20_8 hx22_8 hx21_8 hcs8 hevs5
      have hfit_r5 : FitsEnv M lim
          (M.stepEvents evs5 (M.stepEvents evs4 (M.stepEvents evs3 (M.stepEvents evs2 (M.stepEvents evs1 st)))))
          (EncRawSegEnv
            ((((((bs ++ [74#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ++
              optUint32Field 1 p.preKeyId) ++
              ([18#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length))) ++ g.vec.bytes).length)
            (d6 + d7)) := by
        have h := fitsEnv_encRawSeg_right hfit_r4 hevs5
        have hlen_eq :
            (((((bs ++ [74#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ++
              optUint32Field 1 p.preKeyId) ++
              ([18#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length))).length) + d5 =
            ((((((bs ++ [74#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ++
              optUint32Field 1 p.preKeyId) ++
              ([18#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length))) ++ g.vec.bytes).length) := by
          simp only [List.length_append, d5]
        rwa [← hlen_eq]
      refine step_tag9_sub3_placed_x hEV hDR ss v sp0 cap8 ptr8 g p
        (((((bs ++ [74#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ++
          optUint32Field 1 p.preKeyId) ++
          ([18#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length))) ++ g.vec.bytes)
        (M.stepEvents evs5 (M.stepEvents evs4 (M.stepEvents evs3 (M.stepEvents evs2 (M.stepEvents evs1 st)))))
        (by simp only [List.length_append, List.length_singleton]; omega)
        (fitsEnv_encRawSeg_left hfit_r5)
        hpc8 hrun8 hsp8 halign htr8 hx19_8 hx20_8 hx22_8 hx21_8 hcs8 (by sep_focus) ?_
      intro s9 cap9 ptr9 evs6 hpc9 hrun9 hsp9 htr9 hx19_9 hx20_9 hx21_9 hcs9 hevs6
      have hfit_r6 : FitsEnv M lim
          (M.stepEvents evs6 (M.stepEvents evs5 (M.stepEvents evs4 (M.stepEvents evs3 (M.stepEvents evs2 (M.stepEvents evs1 st))))))
          (EncRawSegEnv
            (((((((bs ++ [74#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ++
              optUint32Field 1 p.preKeyId) ++
              ([18#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length))) ++ g.vec.bytes) ++
              int32Field 3 p.signedPreKeyId).length)
            d7) := by
        have h := fitsEnv_encRawSeg_right hfit_r5 hevs6
        have hlen_eq :
            ((((((bs ++ [74#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ++
              optUint32Field 1 p.preKeyId) ++
              ([18#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length))) ++ g.vec.bytes).length) + d6 =
            (((((((bs ++ [74#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ++
              optUint32Field 1 p.preKeyId) ++
              ([18#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length))) ++ g.vec.bytes) ++
              int32Field 3 p.signedPreKeyId).length) := by
          simp only [List.length_append, d6]
        rwa [← hlen_eq]
      refine step_tag9_sub4_placed_x hEV hDR ss v sp0 cap9 ptr9 g p
        ((((((bs ++ [74#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ++
          optUint32Field 1 p.preKeyId) ++
          ([18#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length))) ++ g.vec.bytes) ++
          int32Field 3 p.signedPreKeyId)
        (M.stepEvents evs6 (M.stepEvents evs5 (M.stepEvents evs4 (M.stepEvents evs3 (M.stepEvents evs2 (M.stepEvents evs1 st))))))
        (by simp only [List.length_append, List.length_singleton]; omega)
        hfit_r6
        hpc9 hrun9 hsp9 halign htr9 hx19_9 hx20_9 hx21_9 hcs9 (by sep_focus) ?_
      intro s10 cap10 ptr10 evs7 hpc10 hrun10 hsp10 htr10 hx19_10 hx20_10 hcs10 hevs7
      have hevs_67 : EncRawSegEnv
          ((((((bs ++ [74#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ++
            optUint32Field 1 p.preKeyId) ++
            ([18#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length))) ++ g.vec.bytes).length)
          (d6 + d7) (evs6 ++ evs7) := by
        refine encRawSegEnv_append hevs6 ?_
        have hlen_eq :
            ((((((bs ++ [74#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ++
              optUint32Field 1 p.preKeyId) ++
              ([18#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length))) ++ g.vec.bytes).length) + d6 =
            (((((((bs ++ [74#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ++
              optUint32Field 1 p.preKeyId) ++
              ([18#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length))) ++ g.vec.bytes) ++
              int32Field 3 p.signedPreKeyId).length) := by
          simp only [List.length_append, d6]
        rwa [hlen_eq]
      have hevs_57 : EncRawSegEnv
          (((((bs ++ [74#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ++
            optUint32Field 1 p.preKeyId) ++
            ([18#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length))).length)
          (d5 + (d6 + d7)) (evs5 ++ (evs6 ++ evs7)) := by
        refine encRawSegEnv_append hevs5 ?_
        have hlen_eq :
            (((((bs ++ [74#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ++
              optUint32Field 1 p.preKeyId) ++
              ([18#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length))).length) + d5 =
            ((((((bs ++ [74#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ++
              optUint32Field 1 p.preKeyId) ++
              ([18#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length))) ++ g.vec.bytes).length) := by
          simp only [List.length_append, d5]
        rwa [hlen_eq]
      have hevs_47 : EncRawSegEnv
          ((((bs ++ [74#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ++
            optUint32Field 1 p.preKeyId).length)
          (d4 + (d5 + (d6 + d7))) (evs4 ++ (evs5 ++ (evs6 ++ evs7))) := by
        refine encRawSegEnv_append hevs4 ?_
        have hlen_eq :
            ((((bs ++ [74#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ++
              optUint32Field 1 p.preKeyId).length) + d4 =
            (((((bs ++ [74#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ++
              optUint32Field 1 p.preKeyId) ++
              ([18#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length))).length) := by
          simp only [List.length_append, List.length_singleton, d4]
        rwa [hlen_eq]
      have hevs_37 : EncRawSegEnv
          (((bs ++ [74#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)).length)
          (d3 + (d4 + (d5 + (d6 + d7)))) (evs3 ++ (evs4 ++ (evs5 ++ (evs6 ++ evs7)))) := by
        refine encRawSegEnv_append hevs3 ?_
        have hlen_eq :
            (((bs ++ [74#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)).length) + d3 =
            ((((bs ++ [74#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ++
              optUint32Field 1 p.preKeyId).length) := by
          simp only [List.length_append, d3]
        rwa [hlen_eq]
      have hevs_27 : EncRawSegEnv (bs.length + d1)
          (d2 + (d3 + (d4 + (d5 + (d6 + d7)))))
          (evs2 ++ (evs3 ++ (evs4 ++ (evs5 ++ (evs6 ++ evs7))))) := by
        refine encRawSegEnv_append hevs2 ?_
        have hlen_eq : (bs.length + d1) + d2 =
            (((bs ++ [74#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)).length) := by
          simp only [List.length_append, List.length_singleton, d1, d2]
        rwa [hlen_eq]
      have hevs_all : EncRawSegEnv bs.length (encPendingFieldMem (some g) (some p)).length
          (evs1 ++ (evs2 ++ (evs3 ++ (evs4 ++ (evs5 ++ (evs6 ++ evs7)))))) := by
        rw [htotal_len]
        exact encRawSegEnv_append hevs1 hevs_27
      refine SepWPpLsCl.weaken_pre ?_ (hnext s10 cap10 ptr10
        (evs1 ++ (evs2 ++ (evs3 ++ (evs4 ++ (evs5 ++ (evs6 ++ evs7))))))
        hpc10 hrun10 hsp10 htr10 hx19_10 hx20_10 hcs10 hevs_all)
      rw [← hopen, hbytes_eq]
      simp only [← M.stepEvents_append, List.append_assoc]
      exact entails_of_sep_focus (by sep_focus)

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PendingPreKeyFieldsXBPlacedBudget
