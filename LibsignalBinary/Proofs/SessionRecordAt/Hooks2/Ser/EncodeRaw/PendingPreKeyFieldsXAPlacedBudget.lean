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
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.PendingPreKeyHeader
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.BaseXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.BaseX
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.BaseXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PendingPreKeyFieldsXAPlaced
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PrologueVersionLocalIdentityXPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PendingPreKeyFieldsXA
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `SessionStructure::encode_raw` Tag 9 Subfields 1 and 2 (`824` → `976`)

Verifies relocatable subfields 1 (`pre_key_id`) and 2 (`base_key`) of protobuf tag 9
(`pending_pre_key`, Block `14` offsets `824/872..976`) under `RustCliAllocBudget M` and
`EncRawSegEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PendingPreKeyFieldsXAPlacedBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSessionApi (PendingPreKey)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks lsmpl lsMemcpySym lsρ
)
open CryptoVerification.RustHeap (vecHeader vecU8At)
open CryptoVerification.LibsignalTripleRatchetRepr (TailVecGhost)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  vecU8At_eq_header_sep_buf cap_beq_len_false cap_eq_ofNat_len
)
open CryptoVerification.E2E.Record (optUint32Field)
open CryptoVerification.E2E.Record.Placed (blkPl_14 lsProg_14)
open CryptoVerification.E2E.Record.Serialization (
  encodeRawSubStackX sepWPpLsCl_extract_vecU8At_bounds bv_add_neg80_3b
)
open CryptoVerification.E2E.Record.Serialization.EncodeRawAux (
  entails_of_sep_focus EncRawUpperSaved sp_sub_80_spAligned
  ofNat64_len_beq_zero_false encodeVarint_length_le_10
  vecU8At_close_slice vecU8At_open_one vecU8At_close_one
  cmp_hi_false_of_le cmp_hi_true_of_gt cmp_ls_true_of_le
  truncate32_signExtend64_er optUint32Field1_none_eq optUint32Field1_some_eq
  optU32ValAt optU32ValAt_some pendingOpenAt
)
open Proofs.libsignal.Hooks2 (SepWPpLsCl)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv
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
  encraw_call_doReserve_buf_placed_x encraw_call_memcpy_buf_placed_x
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  truncate32_signExtend64_er truncate32_zeroExtend64 bv_add_neg80_3b

/-! ## Subfield 1 (`pre_key_id`, `824/872 → 872`, cold `2752..2784`) -/

theorem step_tag9_sub1_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (hDR : DoReservePlacedOkX M A lim H)
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (bs : List (BitVec 8))
    (st : M.σ)
    (hlen_lt : bs.length + 12 < 2 ^ 60)
    (hfit : FitsEnv M lim st (EncRawSegEnv bs.length (optUint32Field 1 p.preKeyId).length))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base +
      (if p.preKeyId.isSome then 824#64 else 872#64))
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
      A.pool lim st s ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64) (evs : List AllocEvent),
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
      EncRawSegEnv bs.length (optUint32Field 1 p.preKeyId).length evs →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((pendingOpenAt A.repAlloc ss g p ∗
          vecU8At A.repAlloc v cap' ptr' (bs ++ optUint32Field 1 p.preKeyId) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  cases hpk : p.preKeyId with
  | none =>
    simp only [hpk, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc
    rw [hP]
    refine SepWPpLsCl.weaken_pre ?_
      (hnext s cap ptr [] hpc hrun hsp htr hx19 hx20 hx23 hx22 hx21 hcs
        (by rw [hpk, optUint32Field1_none_eq]; exact encRawSegEnv_nil _ _))
    simp only [hpk, optUint32Field1_none_eq, List.append_nil]
    exact entails_of_sep_focus (by sep_focus)
  | some pkId =>
    simp only [hpk, Option.isSome_some, ↓reduceIte] at hpc
    have hCallEV := @encraw_call_encodeVarint_placed_x _ M A lim H hEV
    have hCallDR := @encraw_call_doReserve_buf_placed_x _ M A lim H hDR
    have hpk_val : optU32ValAt (ss + 276#64) g.tail (some pkId) = ((ss + 276#64) ↦₃₂ pkId) :=
      optU32ValAt_some _ _ _
    have hflen : (optUint32Field 1 (some pkId)).length =
        1 + (encodeVarint (BitVec.zeroExtend 64 pkId)).length := by
      rw [← optUint32Field1_some_eq pkId]
      simp only [List.length_append, List.length_singleton]
    have hvlen10 := encodeVarint_length_le_10 (BitVec.zeroExtend 64 pkId)
    rw [hpk] at hfit
    rw [hP]
    refine sepWPpLsCl_extract_vecU8At_bounds (A := A.repAlloc) (v := v) (cap := cap) (ptr := ptr) (bs := bs)
      (hfocus := by sep_focus) (h := fun hle _ _ => ?_)
    by_cases hlt : bs.length < cap.toNat
    · have hbeq_cap := cap_beq_len_false hlt
      rw [vecU8At_open_one A.repAlloc v cap ptr bs hlt]
      unfold pendingOpenAt
      rw [hpk, hpk_val]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPpLsCl.exists_elim fun old => ?_
      apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm], fun hvm0 =>
            sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := st) hvm0 (by sep_focus) ?_⟩
        have hfitEV : FitsEnv M lim st
            (EncodeVarintEnv ⟨BitVec.zeroExtend 64 pkId, v, cap, ptr, bs ++ [8#8]⟩) :=
          fitsEnv_encodeVarint_of_encRawSeg (by dsimp only; omega)
            (by (try dsimp only); (try simp only [List.length_append, List.length_singleton]); omega)
            (by (try dsimp only); (try simp only [List.length_append, List.length_singleton]); omega) hfit
        have hclose := vecU8At_close_one A.repAlloc v cap ptr bs 8#8 hlt
        refine SepWPpLsCl.weaken_pre (P' :=
            (vecU8At A.repAlloc v cap ptr (bs ++ [8#8]) ∗ A.pool lim st _ ∗
              stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
              (pendingOpenAt A.repAlloc ss g p ∗ F))
          (by
            rw [← hclose]
            unfold pendingOpenAt
            rw [hpk, hpk_val]
            simp only [sepConj_assoc]
            exact entails_of_sep_focus (by sep_focus)) ?_
        refine hCallEV sp0 (BitVec.zeroExtend 64 pkId) v cap ptr ((blkPl_14).base + 872#64) (bs ++ [8#8])
          st (by simp; omega) hfitEV (s0 := s0) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
        · simp only [arm64_norm]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
        · simp only [arm64_norm, *]
        · simp only [arm64_norm]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm]
        · intro s1 cap' ptr' evs hpc1 hrun1 hsp1 htr1 hcs1 hevs
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
          have hevs_seg : EncRawSegEnv bs.length (optUint32Field 1 p.preKeyId).length evs := by
            rw [hpk]
            have hb := encodeVarintEnv_sub_boundedRustEvs
              (outLen := bs.length + (optUint32Field 1 (some pkId)).length)
              (by (try dsimp only); (try simp only [List.length_append, List.length_singleton]); omega)
              (by (try dsimp only); omega) hevs
            exact hb.mono (by dsimp only; omega) (Nat.le_refl _)
          refine SepWPpLsCl.weaken_pre ?_ (hnext s1 cap' ptr' evs hpc1 hrun1 hsp1 htr1
            hx19_1 hx20_1 hx23_1 hx22_1 hx21_1 hcs_1 hevs_seg)
          rw [List.append_assoc, hpk, optUint32Field1_some_eq pkId]
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
      unfold pendingOpenAt
      rw [hpk, hpk_val]
      simp only [vecHeader, sepConj_assoc]
      apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 13)
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm], fun hvm0 =>
            sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := st) hvm0 (by sep_focus) ?_⟩
        have hx1_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        refine hCallDR sp0 v cap ptr ((blkPl_14).base + 2776#64) bs 1 st
          (by omega) (by omega) hfitDR (s0 := s0)
          ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
        · simp only [arm64_norm]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
        · simp only [arm64_norm, *]
        · simp only [arm64_norm]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm]
        · simp only [arm64_norm]
        · simp only [arm64_norm]
        · intro s1 newCap p1 evs1 hpc1 hrun1 hsp1 htr1 hcs1 hevs1 hnew_ge _
          have he1_seg : EncRawSegEnv bs.length 1 evs1 :=
            (doReserveEnv_sub_boundedRustEvs (outLen := bs.length + 1)
              (by dsimp only; omega) (by dsimp only; omega) (by omega) hevs1).mono
              (by omega) (Nat.le_refl _)
          have hfit2 : FitsEnv M lim (M.stepEvents evs1 st)
              (EncRawSegEnv (bs.length + 1) (encodeVarint (BitVec.zeroExtend 64 pkId)).length) :=
            fitsEnv_encRawSeg_right hfit he1_seg
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
          have hx24_1 : s1.readReg64 .x24 = BitVec.zeroExtend 64 pkId := by
            have := hcs1.2.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
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
                (EncodeVarintEnv ⟨BitVec.zeroExtend 64 pkId, v, newCap, p1, bs ++ [8#8]⟩) :=
              fitsEnv_encodeVarint_of_encRawSeg (by dsimp only; omega)
                (by (try dsimp only); (try simp only [List.length_append, List.length_singleton]); omega)
                (by (try dsimp only); (try simp only [List.length_append, List.length_singleton]); omega) hfit2
            have hclose := vecU8At_close_one A.repAlloc v newCap p1 bs 8#8 hlt_new
            refine SepWPpLsCl.weaken_pre (P' :=
                (vecU8At A.repAlloc v newCap p1 (bs ++ [8#8]) ∗
                  A.pool lim (M.stepEvents evs1 st) _ ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
                  (pendingOpenAt A.repAlloc ss g p ∗ F))
              (by
                rw [← hclose]
                unfold pendingOpenAt
                rw [hpk, hpk_val]
                simp only [sepConj_assoc]
                exact entails_of_sep_focus (by sep_focus)) ?_
            refine hCallEV sp0 (BitVec.zeroExtend 64 pkId) v newCap p1 ((blkPl_14).base + 872#64) (bs ++ [8#8])
              (M.stepEvents evs1 st) (by simp; omega) hfitEV (s0 := s0)
              ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
            · simp only [arm64_norm]
            · simp only [arm64_norm, *]
            · simp only [arm64_norm, *]
            · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
            · simp only [arm64_norm, *]
            · simp only [arm64_norm, *]
            · simp only [arm64_norm, *]
            · simp only [arm64_norm]
            · intro s2 cap' ptr' evs2 hpc2 hrun2 hsp2 htr2 hcs2 hevs2
              have hx19_2 : s2.readReg64 .x19 = v := by
                have := hcs2.1; simp only [arm64_norm, *] at this; exact this
              have hx20_2 : s2.readReg64 .x20 = ss := by
                have := hcs2.2.1; simp only [arm64_norm, *] at this; exact this
              have hx21_2 : s2.readReg64 .x21 = p.timestamp := by
                have := hcs2.2.2.1; simp only [arm64_norm, *] at this; exact this
              have hx22_2 : s2.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId := by
                have := hcs2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
              have hx23_2 : s2.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length := by
                have := hcs2.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
              have hcs_2 : EncRawUpperSaved s0 s2 :=
                (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
                  (EncRawUpperSaved.of_calleeSavedPreserved hcs2)
              have he2_seg : EncRawSegEnv (bs.length + 1)
                  (encodeVarint (BitVec.zeroExtend 64 pkId)).length evs2 :=
                (encodeVarintEnv_sub_boundedRustEvs
                  (outLen := (bs.length + 1) + (encodeVarint (BitVec.zeroExtend 64 pkId)).length)
                  (by (try dsimp only); (try simp only [List.length_append, List.length_singleton]); omega)
                  (by (try dsimp only); omega) hevs2).mono (by dsimp only; omega) (Nat.le_refl _)
              have he12 : EncRawSegEnv bs.length (optUint32Field 1 p.preKeyId).length (evs1 ++ evs2) := by
                rw [hpk, hflen]; exact encRawSegEnv_append he1_seg he2_seg
              rw [← M.stepEvents_append]
              refine SepWPpLsCl.weaken_pre ?_ (hnext s2 cap' ptr' (evs1 ++ evs2) hpc2 hrun2 hsp2 htr2
                hx19_2 hx20_2 hx23_2 hx22_2 hx21_2 hcs_2 he12)
              rw [List.append_assoc, hpk, optUint32Field1_some_eq pkId]
              simp only [sepConj_assoc]
              exact entails_of_sep_focus (by sep_focus)

/-! ## Subfield 2 (`base_key`) header and varint (`872 → 928`, cold `2460..2488`) -/

theorem step_tag9_sub2_a_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (hDR : DoReservePlacedOkX M A lim H)
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (bs : List (BitVec 8))
    (st : M.σ)
    (hne_vec : g.vec.bytes ≠ []) (hlt_vec : g.vec.bytes.length < 2 ^ 63)
    (hlen_lt : bs.length + 12 < 2 ^ 60)
    (hfit : FitsEnv M lim st
      (EncRawSegEnv bs.length ([18#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length)).length))
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
      A.pool lim st s ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64) (evs : List AllocEvent),
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
      EncRawSegEnv bs.length ([18#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length)).length evs →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((pendingOpenAt A.repAlloc ss g p ∗
          vecU8At A.repAlloc v cap' ptr' (bs ++ ([18#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length))) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hCallEV := @encraw_call_encodeVarint_placed_x _ M A lim H hEV
  have hCallDR := @encraw_call_doReserve_buf_placed_x _ M A lim H hDR
  have hbeq0 := ofNat64_len_beq_zero_false hne_vec hlt_vec
  have hvlen10 := encodeVarint_length_le_10 (BitVec.ofNat 64 g.vec.bytes.length)
  have hflen : ([18#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length)).length =
      1 + (encodeVarint (BitVec.ofNat 64 g.vec.bytes.length)).length := by
    simp only [List.length_append, List.length_singleton]
  rw [hP]
  refine sepWPpLsCl_extract_vecU8At_bounds (A := A.repAlloc) (v := v) (cap := cap) (ptr := ptr) (bs := bs)
    (hfocus := by sep_focus) (h := fun hle _ _ => ?_)
  by_cases hlt : bs.length < cap.toNat
  · have hbeq_cap := cap_beq_len_false hlt
    rw [vecU8At_open_one A.repAlloc v cap ptr bs hlt]
    unfold pendingOpenAt
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPpLsCl.exists_elim fun old => ?_
    apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm0 =>
          sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := st) hvm0 (by sep_focus) ?_⟩
      have hfitEV : FitsEnv M lim st
          (EncodeVarintEnv ⟨BitVec.ofNat 64 g.vec.bytes.length, v, cap, ptr, bs ++ [18#8]⟩) :=
        fitsEnv_encodeVarint_of_encRawSeg (by dsimp only; omega)
          (by (try dsimp only); (try simp only [List.length_append, List.length_singleton]); omega)
          (by (try dsimp only); (try simp only [List.length_append, List.length_singleton]); omega) hfit
      have hclose := vecU8At_close_one A.repAlloc v cap ptr bs 18#8 hlt
      refine SepWPpLsCl.weaken_pre (P' :=
          (vecU8At A.repAlloc v cap ptr (bs ++ [18#8]) ∗ A.pool lim st _ ∗
            stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
            (pendingOpenAt A.repAlloc ss g p ∗ F))
        (by
          rw [← hclose]
          unfold pendingOpenAt
          simp only [sepConj_assoc]
          exact entails_of_sep_focus (by sep_focus)) ?_
      refine hCallEV sp0 (BitVec.ofNat 64 g.vec.bytes.length) v cap ptr ((blkPl_14).base + 928#64) (bs ++ [18#8])
        st (by simp; omega) hfitEV (s0 := s0) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
      · simp only [arm64_norm]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm]
      · intro s1 cap' ptr' evs hpc1 hrun1 hsp1 htr1 hcs1 hevs
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
        have hevs_seg : EncRawSegEnv bs.length
            ([18#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length)).length evs :=
          (encodeVarintEnv_sub_boundedRustEvs
            (outLen := bs.length + ([18#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length)).length)
            (by (try dsimp only); (try simp only [List.length_append, List.length_singleton]); omega)
            (by (try dsimp only); omega) hevs).mono (by dsimp only; omega) (Nat.le_refl _)
        refine SepWPpLsCl.weaken_pre ?_ (hnext s1 cap' ptr' evs hpc1 hrun1 hsp1 htr1
          hx19_1 hx20_1 hx24_1 hx23_1 hx22_1 hx21_1 hcs_1 hevs_seg)
        rw [List.append_assoc]
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
    unfold pendingOpenAt
    simp only [vecHeader, sepConj_assoc]
    apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 13)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm0 =>
          sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := st) hvm0 (by sep_focus) ?_⟩
      have hx1_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      refine hCallDR sp0 v cap ptr ((blkPl_14).base + 2480#64) bs 1 st
        (by omega) (by omega) hfitDR (s0 := s0)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
      · simp only [arm64_norm]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
      · simp only [arm64_norm, *]
      · simp only [arm64_norm]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm]
      · simp only [arm64_norm]
      · simp only [arm64_norm]
      · intro s1 newCap p1 evs1 hpc1 hrun1 hsp1 htr1 hcs1 hevs1 hnew_ge _
        have he1_seg : EncRawSegEnv bs.length 1 evs1 :=
          (doReserveEnv_sub_boundedRustEvs (outLen := bs.length + 1)
            (by dsimp only; omega) (by dsimp only; omega) (by omega) hevs1).mono
            (by omega) (Nat.le_refl _)
        have hfit2 : FitsEnv M lim (M.stepEvents evs1 st)
            (EncRawSegEnv (bs.length + 1) (encodeVarint (BitVec.ofNat 64 g.vec.bytes.length)).length) :=
          fitsEnv_encRawSeg_right hfit he1_seg
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
              (EncodeVarintEnv ⟨BitVec.ofNat 64 g.vec.bytes.length, v, newCap, p1, bs ++ [18#8]⟩) :=
            fitsEnv_encodeVarint_of_encRawSeg (by dsimp only; omega)
              (by (try dsimp only); (try simp only [List.length_append, List.length_singleton]); omega)
              (by (try dsimp only); (try simp only [List.length_append, List.length_singleton]); omega) hfit2
          have hclose := vecU8At_close_one A.repAlloc v newCap p1 bs 18#8 hlt_new
          refine SepWPpLsCl.weaken_pre (P' :=
              (vecU8At A.repAlloc v newCap p1 (bs ++ [18#8]) ∗
                A.pool lim (M.stepEvents evs1 st) _ ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
                (pendingOpenAt A.repAlloc ss g p ∗ F))
            (by
              rw [← hclose]
              unfold pendingOpenAt
              simp only [sepConj_assoc]
              exact entails_of_sep_focus (by sep_focus)) ?_
          refine hCallEV sp0 (BitVec.ofNat 64 g.vec.bytes.length) v newCap p1 ((blkPl_14).base + 928#64) (bs ++ [18#8])
            (M.stepEvents evs1 st) (by simp; omega) hfitEV (s0 := s0)
            ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
          · simp only [arm64_norm]
          · simp only [arm64_norm, *]
          · simp only [arm64_norm, *]
          · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
          · simp only [arm64_norm, *]
          · simp only [arm64_norm, *]
          · simp only [arm64_norm, *]
          · simp only [arm64_norm]
          · intro s2 cap' ptr' evs2 hpc2 hrun2 hsp2 htr2 hcs2 hevs2
            have hx19_2 : s2.readReg64 .x19 = v := by
              have := hcs2.1; simp only [arm64_norm, *] at this; exact this
            have hx20_2 : s2.readReg64 .x20 = ss := by
              have := hcs2.2.1; simp only [arm64_norm, *] at this; exact this
            have hx21_2 : s2.readReg64 .x21 = p.timestamp := by
              have := hcs2.2.2.1; simp only [arm64_norm, *] at this; exact this
            have hx22_2 : s2.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId := by
              have := hcs2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
            have hx23_2 : s2.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length := by
              have := hcs2.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
            have hx24_2 : s2.readReg64 .x24 = g.vec.ptr := by
              have := hcs2.2.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
            have hcs_2 : EncRawUpperSaved s0 s2 :=
              (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
                (EncRawUpperSaved.of_calleeSavedPreserved hcs2)
            have he2_seg : EncRawSegEnv (bs.length + 1)
                (encodeVarint (BitVec.ofNat 64 g.vec.bytes.length)).length evs2 :=
              (encodeVarintEnv_sub_boundedRustEvs
                (outLen := (bs.length + 1) + (encodeVarint (BitVec.ofNat 64 g.vec.bytes.length)).length)
                (by (try dsimp only); (try simp only [List.length_append, List.length_singleton]); omega)
                (by (try dsimp only); omega) hevs2).mono (by dsimp only; omega) (Nat.le_refl _)
            have he12 : EncRawSegEnv bs.length
                ([18#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length)).length (evs1 ++ evs2) := by
              rw [hflen]; exact encRawSegEnv_append he1_seg he2_seg
            rw [← M.stepEvents_append]
            refine SepWPpLsCl.weaken_pre ?_ (hnext s2 cap' ptr' (evs1 ++ evs2) hpc2 hrun2 hsp2 htr2
              hx19_2 hx20_2 hx24_2 hx23_2 hx22_2 hx21_2 hcs_2 he12)
            rw [List.append_assoc]
            simp only [sepConj_assoc]
            exact entails_of_sep_focus (by sep_focus)

/-! ## Subfield 2 (`base_key`) reserve and `memcpy` (`928 → 976`, cold `2488..2564`) -/

theorem step_tag9_sub2_b_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hDR : DoReservePlacedOkX M A lim H)
    (hC : SerContractsXPlaced M A lim H)
    (ss v sp0 cap1 ptr1 : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (bs1 : List (BitVec 8))
    (st : M.σ)
    (hne_vec : g.vec.bytes ≠ [])
    (hfit1 : bs1.length + g.vec.bytes.length < 2 ^ 60)
    (hfit : FitsEnv M lim st (EncRawSegEnv bs1.length g.vec.bytes.length))
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
      A.pool lim st s ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_14).base + 976#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId →
      sm.readReg64 .x21 = p.timestamp →
      EncRawUpperSaved s0 sm →
      EncRawSegEnv bs1.length g.vec.bytes.length evs →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((pendingOpenAt A.repAlloc ss g p ∗ vecU8At A.repAlloc v cap' ptr' (bs1 ++ g.vec.bytes) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hCallDR := @encraw_call_doReserve_buf_placed_x _ M A lim H hDR
  have hCallMC := @encraw_call_memcpy_buf_placed_x _ M A lim H hC
  have hvec_pos : 1 ≤ g.vec.bytes.length := List.length_pos_of_ne_nil hne_vec
  rw [hP]
  refine sepWPpLsCl_extract_vecU8At_bounds (A := A.repAlloc) (v := v) (cap := cap1) (ptr := ptr1) (bs := bs1)
    (hfocus := by sep_focus) (h := fun hle1 hcap1 hptr1 => ?_)
  rw [vecU8At_eq_header_sep_buf A.repAlloc v cap1 ptr1 bs1]
  unfold pendingOpenAt
  simp only [vecHeader, sepConj_assoc]
  have hx2_nat : (BitVec.ofNat 64 g.vec.bytes.length).toNat = g.vec.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  by_cases hroom : bs1.length + g.vec.bytes.length ≤ cap1.toNat
  · have hhi := cmp_hi_false_of_le hroom hcap1
    apply sepWPpLsCl_of_sepWP_vm (mid := lsρ lsMemcpySym)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm0 =>
          sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := st) hvm0 (by sep_focus) ?_⟩
      refine hCallMC sp0 v cap1 ptr1 g.vec.ptr ((blkPl_14).base + 968#64) bs1 g.vec.bytes
        st hroom hcap1 hptr1 hne_vec (s0 := s0)
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
            ⟨by simp only [wp_norm, arm64_norm], fun hvmm =>
              sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := st) hvmm (by sep_focus) ?_⟩
          refine SepWPpLsCl.weaken_pre ?_ (hnext _ cap1 ptr1 []
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
            (encRawSegEnv_nil _ _))
          rw [← vecU8At_close_slice A.repAlloc v cap1 ptr1 bs1 g.vec.bytes hroom hcap1 hptr1 hne_vec]
          unfold pendingOpenAt
          simp only [sepConj_assoc]
          exact entails_of_sep_focus (by sep_focus)
  · have hhi := cmp_hi_true_of_gt (add := g.vec.bytes.length) hle1 (by omega) hcap1 (by omega)
    have hfitDR : FitsEnv M lim st (DoReserveEnv (DoReserveCall.mk v cap1 ptr1 bs1 g.vec.bytes.length)) :=
      fitsEnv_doReserve_of_encRawSeg hvec_pos (by dsimp only; omega)
        (by dsimp only; omega) (by omega) hfit
    apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 13)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm0 =>
          sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := st) hvm0 (by sep_focus) ?_⟩
      have hx1_nat : (BitVec.ofNat 64 bs1.length).toNat = bs1.length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      refine hCallDR sp0 v cap1 ptr1 ((blkPl_14).base + 2512#64) bs1 g.vec.bytes.length
        st (by omega) (by omega) hfitDR (s0 := s0)
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
        have hevs_seg : EncRawSegEnv bs1.length g.vec.bytes.length evs :=
          (doReserveEnv_sub_boundedRustEvs (outLen := bs1.length + g.vec.bytes.length)
            (by dsimp only; omega) (by dsimp only; omega) (by omega) hevs).mono
            (by omega) (Nat.le_refl _)
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
          refine hCallMC sp0 v newCap p' g.vec.ptr ((blkPl_14).base + 968#64) bs1 g.vec.bytes
            (M.stepEvents evs st) hnew_ge hnew_lt hp'_ne hne_vec (s0 := s0)
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
            have hx21m : sm.readReg64 .x21 = p.timestamp := by
              have := hcsm.2.2.1; simp only [arm64_norm, *] at this; exact this
            have hx22m : sm.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId := by
              have := hcsm.2.2.2.1; simp only [arm64_norm, *] at this; exact this
            have hx23m : sm.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length := by
              have := hcsm.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
            have hx25m : sm.readReg64 .x25 = BitVec.ofNat 64 bs1.length := by
              have := hcsm.2.2.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
            have hcsm' : EncRawUpperSaved s0 sm :=
              (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
                (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
            apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 976#64)
            by_vm_steps
              wp_steps
              refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                ⟨by simp only [wp_norm, arm64_norm], fun hvmm =>
                  sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := M.stepEvents evs st) hvmm (by sep_focus) ?_⟩
              refine SepWPpLsCl.weaken_pre ?_ (hnext _ newCap p' evs
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
                hevs_seg)
              rw [← vecU8At_close_slice A.repAlloc v newCap p' bs1 g.vec.bytes hnew_ge hnew_lt hp'_ne hne_vec]
              unfold pendingOpenAt
              simp only [sepConj_assoc]
              exact entails_of_sep_focus (by sep_focus)

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PendingPreKeyFieldsXAPlacedBudget
