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
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PendingPreKeyFieldsXBPlaced
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PrologueVersionLocalIdentityXPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.E2E.Record.Serialization.ChainLenAux.Pure
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.PendingPreKeyFields
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.SenderReceiverChains
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PendingPreKeyFieldsXB
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `SessionStructure::encode_raw` Tag 9 Header (`536` → `824/872`)

Proves budget-threaded step lemmas for the `0x4a` tag write, subfield length accumulation, and outer
length varint of protobuf tag 9 (`pending_pre_key`, Block `14` offsets `536..824/872`) under
`RustCliAllocBudget M` and `EncRawSegEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PendingPreKeyFieldsXBPlacedBudgetAux

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSessionApi (PendingPreKey)
open CryptoVerification (LibsignalPlacement LibsignalHooks lsmpl)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8At)
open CryptoVerification.LibsignalTripleRatchetRepr (TailVecGhost)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  vecU8Buf vecU8At_eq_header_sep_buf cap_beq_len_false cap_eq_ofNat_len
  ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32 optU32Tag
)
open CryptoVerification.E2E.Record (
  optUint32Field bytesField int32Field
)
open CryptoVerification.E2E.Record.Placed (blkPl_14 lsProg_14)
open CryptoVerification.E2E.Record.Serialization (
  encodeRawSubStackX encPendingMem sepWPpLsCl_extract_vecU8At_bounds
)
open CryptoVerification.E2E.Record.Serialization.EncodeRawAux (
  entails_of_sep_focus EncRawUpperSaved
  vecSrcRest vecCopyDone optU32ValAt optU32ValAt_some pendingTailRest pendingOpenAt
  optU32Tag_bne1_pc optUint32Field1_none_eq optUint32Field1_some_length_bv
  bytesField2_nonempty_length_bv int32Field3_zero_eq int32Field3_nonzero_length_bv
  uint64Field4_nonzero_length_bv encPendingMem_length_bv encPendingMem_length_bv_ts_zero
  spk_cbz_pc ts_cbnz_pc ts_cbz_pc bv32_beq_zero_false bv64_beq_zero_false
  ofNat64_len_beq_zero_false ofNat64_len_bne_zero_true
  truncate32_signExtend64_er er_truncate32_zext64_lsr6
  erHwVarintLen_eq_encodeVarint_length erHwVarintLen_bvShift_eq_encodeVarint_length
  bv_add_neg80_3a cmn1_beq_zero_false cap_beq_noneCap_false
  vecU8At_open_one vecU8At_close_one
  sp_sub_80_spAligned encodeVarint_length_le_10
)
open Proofs.libsignal.Hooks2 (SepWPpLsCl)
open LibsignalBinary.Heap (
  VmPreserved AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (DoReserveEnv)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget (EncodeVarintEnv)
open LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.BaseBudget (
  EncRawSegEnv encRawSegEnv_nil
  fitsEnv_doReserve_of_encRawSeg fitsEnv_encodeVarint_of_encRawSeg
  doReserveEnv_sub_boundedRustEvs encodeVarintEnv_sub_boundedRustEvs
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

/-! ## Tag `74#8` write (`536..596/764`, cold `2124..2152`) -/

theorem step_tag9_write_tag_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hDR : DoReservePlacedOkX M A lim H)
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (bs : List (BitVec 8))
    (st : M.σ)
    (hcap_g : g.vec.cap.toNat < 2 ^ 63)
    (hlen_lt : bs.length + 1 < 2 ^ 60)
    (hfit : FitsEnv M lim st (EncRawSegEnv bs.length 1))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 536#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (pendingOpenAt A.repAlloc ss g p ∗ vecU8At A.repAlloc v cap ptr bs ∗
      A.pool lim st s ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_14).base + (if p.preKeyId.isSome then 596#64 else 764#64) →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x24 = BitVec.zeroExtend 64 (optU32Tag p.preKeyId) →
      EncRawUpperSaved s0 sm →
      EncRawSegEnv bs.length 1 evs →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((pendingOpenAt A.repAlloc ss g p ∗ vecU8At A.repAlloc v cap' ptr' (bs ++ [74#8]) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hCallDR := @encraw_call_doReserve_buf_placed_x _ M A lim H hDR
  rw [hP]
  refine sepWPpLsCl_extract_vecU8At_bounds (A := A.repAlloc) (v := v) (cap := cap) (ptr := ptr) (bs := bs)
    (hfocus := by sep_focus) (h := fun hle _ _ => ?_)
  have hcmn1 := cmn1_beq_zero_false hcap_g
  have hcmn2 := cap_beq_noneCap_false hcap_g
  by_cases hlt : bs.length < cap.toNat
  · have hbeq_cap := cap_beq_len_false hlt
    rw [vecU8At_open_one A.repAlloc v cap ptr bs hlt]
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
        ⟨by simp only [wp_norm, arm64_norm], fun hvm_end =>
          sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := st) hvm_end (by sep_focus) ?_⟩
      refine SepWPpLsCl.weaken_pre ?_ (hnext _ cap ptr []
        (by simp only [arm64_norm, optU32Tag_bne1_pc, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
        (encRawSegEnv_nil _ _))
      rw [← vecU8At_close_one A.repAlloc v cap ptr bs 74#8 hlt]
      unfold pendingOpenAt
      simp only [sepConj_assoc]
      exact entails_of_sep_focus (by sep_focus)
  · have hcap_eq : cap.toNat = bs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    have hfitDR : FitsEnv M lim st (DoReserveEnv (DoReserveCall.mk v cap ptr bs 1)) :=
      fitsEnv_doReserve_of_encRawSeg (by omega) (by dsimp only; omega)
        (by dsimp only; omega) (by omega) hfit
    rw [vecU8At_eq_header_sep_buf A.repAlloc v cap ptr bs]
    unfold pendingOpenAt
    simp only [vecHeader, sepConj_assoc]
    apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 13)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm_call =>
          sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := st) hvm_call (by sep_focus) ?_⟩
      have hx1_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      refine hCallDR sp0 v cap ptr ((blkPl_14).base + 2144#64) bs 1 st
        (by omega) (by omega) hfitDR (s0 := s0)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by sep_focus) ?_
      intro s1 newCap p1 evs hpc1 hrun1 hsp1 htr1 hcs1 hevs hnew_ge _
      have hevs_seg : EncRawSegEnv bs.length 1 evs :=
        (doReserveEnv_sub_boundedRustEvs (outLen := bs.length + 1)
          (by dsimp only; omega) (by dsimp only; omega) (by omega) hevs).mono
          (by omega) (Nat.le_refl _)
      have hx19_1 : s1.readReg64 .x19 = v := by
        have := hcs1.1; simp only [arm64_norm, *] at this; exact this
      have hx20_1 : s1.readReg64 .x20 = ss := by
        have := hcs1.2.1; simp only [arm64_norm, *] at this; exact this
      have hcs_1 : EncRawUpperSaved s0 s1 :=
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
          (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
      have hlt_new : bs.length < newCap.toNat := by omega
      rw [vecU8At_open_one A.repAlloc v newCap p1 bs hlt_new]
      simp only [sepExists_sepConj_left, sepConj_assoc]
      refine SepWPpLsCl.exists_elim fun old => ?_
      apply sepWPpLsCl_of_sepWP_vm
        (mid := (blkPl_14).base + (if p.preKeyId.isSome then 596#64 else 764#64))
      by_vm_steps
        wp_steps
        refine SepWP.done
          (by simp only [arm64_norm, optU32Tag_bne1_pc, *])
          (by simp only [arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm], fun hvm_end =>
            sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := M.stepEvents evs st) hvm_end (by sep_focus) ?_⟩
        refine SepWPpLsCl.weaken_pre ?_ (hnext _ newCap p1 evs
          (by simp only [arm64_norm, optU32Tag_bne1_pc, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
          hevs_seg)
        rw [← vecU8At_close_one A.repAlloc v newCap p1 bs 74#8 hlt_new]
        unfold pendingOpenAt
        simp only [sepConj_assoc]
        exact entails_of_sep_focus (by sep_focus)

/-! ## Subfield 1 (`pre_key_id`) length and `base_key.length` load (`596/764 → 636`) -/

theorem step_tag9_len1_placed_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (ss v sp0 : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (hne_vec : g.vec.bytes ≠ []) (hlt_vec : g.vec.bytes.length < 2 ^ 63)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + (if p.preKeyId.isSome then 596#64 else 764#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hx24 : s.readReg64 .x24 = BitVec.zeroExtend 64 (optU32Tag p.preKeyId))
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = pendingOpenAt A ss g p ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_14).base + 636#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x24 = BitVec.zeroExtend 64 (optU32Tag p.preKeyId) →
      sm.readReg64 .x8 = BitVec.ofNat 64 (optUint32Field 1 p.preKeyId).length →
      sm.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length →
      EncRawUpperSaved s0 sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm (pendingOpenAt A ss g p ∗ F) Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hbeq0 := ofNat64_len_beq_zero_false hne_vec hlt_vec
  have hbne0 := ofNat64_len_bne_zero_true hne_vec hlt_vec
  rw [hP]
  unfold pendingOpenAt
  cases hpk : p.preKeyId with
  | none =>
    simp only [hpk, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc
    simp only [sepConj_assoc]
    apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 636#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm_end => ?_⟩
      refine SepWPpLsCl.weaken_pre ?_ (hnext _ hvm_end
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, hpk, optUint32Field1_none_eq])
        (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      unfold pendingOpenAt
      simp only [hpk]
      exact entails_of_sep_focus (by sep_focus)
  | some pkId =>
    simp only [hpk, Option.isSome_some, ↓reduceIte] at hpc
    have hpk_val : optU32ValAt (ss + 276#64) g.tail (some pkId) = ((ss + 276#64) ↦₃₂ pkId) :=
      optU32ValAt_some _ _ _
    rw [hpk_val]
    simp only [sepConj_assoc]
    apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 636#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm_end => ?_⟩
      refine SepWPpLsCl.weaken_pre ?_ (hnext _ hvm_end
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, ← optUint32Field1_some_length_bv pkId, *])
        (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      unfold pendingOpenAt
      simp only [hpk, hpk_val]
      exact entails_of_sep_focus (by sep_focus)

/-! ## Subfield 2 (`base_key`) length and `signed_pre_key_id` load (`636 → 672/788`) -/

theorem step_tag9_len2_placed_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (ss v sp0 : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (hne_vec : g.vec.bytes ≠ [])
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 636#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hx24 : s.readReg64 .x24 = BitVec.zeroExtend 64 (optU32Tag p.preKeyId))
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (optUint32Field 1 p.preKeyId).length)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = pendingOpenAt A ss g p ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_14).base + (if p.signedPreKeyId == 0#32 then 788#64 else 672#64) →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x24 = BitVec.zeroExtend 64 (optU32Tag p.preKeyId) →
      sm.readReg64 .x8 = BitVec.ofNat 64 (optUint32Field 1 p.preKeyId).length →
      sm.readReg64 .x9 = BitVec.ofNat 64 (bytesField 2 g.vec.bytes).length →
      sm.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length →
      sm.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId →
      EncRawUpperSaved s0 sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm (pendingOpenAt A ss g p ∗ F) Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  rw [hP]
  unfold pendingOpenAt
  simp only [sepConj_assoc]
  apply sepWPpLsCl_of_sepWP_vm
    (mid := (blkPl_14).base + (if p.signedPreKeyId == 0#32 then 788#64 else 672#64))
  by_vm_steps
    wp_steps
    refine SepWP.done
      (by simp only [arm64_norm, spk_cbz_pc, *])
      (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm_end => ?_⟩
    refine SepWPpLsCl.weaken_pre ?_ (hnext _ hvm_end
      (by simp only [arm64_norm, spk_cbz_pc, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, ← bytesField2_nonempty_length_bv hne_vec, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
    unfold pendingOpenAt
    exact entails_of_sep_focus (by sep_focus)

/-! ## Subfield 3 (`signed_pre_key_id`) length and `timestamp` load (`672/788 → 708/800`) -/

theorem step_tag9_len3_placed_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (ss v sp0 : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + (if p.signedPreKeyId == 0#32 then 788#64 else 672#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hx24 : s.readReg64 .x24 = BitVec.zeroExtend 64 (optU32Tag p.preKeyId))
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (optUint32Field 1 p.preKeyId).length)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 (bytesField 2 g.vec.bytes).length)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length)
    (hx22 : s.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = pendingOpenAt A ss g p ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_14).base + (if p.timestamp == 0#64 then 800#64 else 708#64) →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x24 = BitVec.zeroExtend 64 (optU32Tag p.preKeyId) →
      sm.readReg64 .x8 = BitVec.ofNat 64 (optUint32Field 1 p.preKeyId).length →
      sm.readReg64 .x9 = BitVec.ofNat 64 (bytesField 2 g.vec.bytes).length →
      sm.readReg64 .x10 = BitVec.ofNat 64 (int32Field 3 p.signedPreKeyId).length →
      sm.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length →
      sm.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId →
      sm.readReg64 .x21 = p.timestamp →
      EncRawUpperSaved s0 sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm (pendingOpenAt A ss g p ∗ F) Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  rw [hP]
  unfold pendingOpenAt
  simp only [sepConj_assoc]
  by_cases hspk : p.signedPreKeyId = 0#32
  · simp only [hspk, beq_self_eq_true, ↓reduceIte] at hpc
    apply sepWPpLsCl_of_sepWP_vm
      (mid := (blkPl_14).base + (if p.timestamp == 0#64 then 800#64 else 708#64))
    by_vm_steps
      wp_steps
      refine SepWP.done
        (by simp only [arm64_norm, ts_cbnz_pc, *])
        (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm_end => ?_⟩
      refine SepWPpLsCl.weaken_pre ?_ (hnext _ hvm_end
        (by simp only [arm64_norm, ts_cbnz_pc, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, hspk, int32Field3_zero_eq])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      unfold pendingOpenAt
      exact entails_of_sep_focus (by sep_focus)
  · have hspk_beq : (p.signedPreKeyId == 0#32) = false := bv32_beq_zero_false hspk
    simp only [hspk_beq, Bool.false_eq_true, ↓reduceIte] at hpc
    apply sepWPpLsCl_of_sepWP_vm
      (mid := (blkPl_14).base + (if p.timestamp == 0#64 then 800#64 else 708#64))
    by_vm_steps
      wp_steps
      refine SepWP.done
        (by simp only [arm64_norm, ts_cbz_pc, *])
        (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm_end => ?_⟩
      refine SepWPpLsCl.weaken_pre ?_ (hnext _ hvm_end
        (by simp only [arm64_norm, ts_cbz_pc, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, ← int32Field3_nonzero_length_bv hspk, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      unfold pendingOpenAt
      exact entails_of_sep_focus (by sep_focus)

/-! ## Subfield 4 length, outer length varint, and `w24` dispatch (`708/800 → 824/872`) -/

theorem step_tag9_len4_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (bs : List (BitVec 8))
    (st : M.σ)
    (hlen_lt : bs.length + 12 < 2 ^ 61)
    (hfit : FitsEnv M lim st
      (EncRawSegEnv (bs.length + 1)
        (encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)).length))
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
      A.pool lim st s ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64) (evs : List AllocEvent),
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
      EncRawSegEnv (bs.length + 1)
        (encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)).length evs →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((pendingOpenAt A.repAlloc ss g p ∗
          vecU8At A.repAlloc v cap' ptr'
            (bs ++ [74#8] ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hCallEV := @encraw_call_encodeVarint_placed_x _ M A lim H hEV
  have h10 := encodeVarint_length_le_10 (BitVec.ofNat 64 (encPendingMem g p).length)
  have hfitEV : FitsEnv M lim st
      (EncodeVarintEnv ⟨BitVec.ofNat 64 (encPendingMem g p).length, v, cap, ptr, bs ++ [74#8]⟩) :=
    fitsEnv_encodeVarint_of_encRawSeg (by dsimp only; omega)
      (by simp only [List.length_append, List.length_singleton]; omega)
      (by omega) hfit
  rw [hP]
  by_cases hts : p.timestamp = 0#64
  · simp only [hts, beq_self_eq_true, ↓reduceIte] at hpc
    apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm_call =>
          sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := st) hvm_call (by sep_focus) ?_⟩
      refine hCallEV sp0 (BitVec.ofNat 64 (encPendingMem g p).length) v cap ptr
        ((blkPl_14).base + 820#64) (bs ++ [74#8]) st (by simp; omega) hfitEV (s0 := s0)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
        (by simp only [arm64_norm, ← encPendingMem_length_bv_ts_zero g p hts, *])
        (by simp only [arm64_norm, *]) (by sep_focus) ?_
      intro sm cap' ptr' evs hpcm hrunm hspm htrm hcsm hevs
      have hevs_seg : EncRawSegEnv (bs.length + 1)
          (encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)).length evs :=
        (encodeVarintEnv_sub_boundedRustEvs
          (outLen := (bs.length + 1) +
            (encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)).length)
          (by simp only [List.length_append, List.length_singleton]; omega)
          (by omega) hevs).mono (by dsimp only; omega) (Nat.le_refl _)
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
            ⟨by simp only [wp_norm, arm64_norm], fun hvm_end =>
              sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := M.stepEvents evs st) hvm_end (by sep_focus) ?_⟩
          refine SepWPpLsCl.weaken_pre ?_ (hnext _ cap' ptr' evs
            (by simp only [arm64_norm, Bool.false_eq_true, ↓reduceIte, *])
            (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *])
            (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
            hevs_seg)
          simp only [sepConj_assoc]
          exact entails_of_sep_focus (by sep_focus)
      | some pkId =>
        simp only [hpk, optU32Tag] at hx24m
        apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 824#64)
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [wp_norm, arm64_norm], fun hvm_end =>
              sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := M.stepEvents evs st) hvm_end (by sep_focus) ?_⟩
          refine SepWPpLsCl.weaken_pre ?_ (hnext _ cap' ptr' evs
            (by simp only [arm64_norm, ↓reduceIte, *])
            (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *])
            (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
            hevs_seg)
          simp only [sepConj_assoc]
          exact entails_of_sep_focus (by sep_focus)
  · have hts_beq : (p.timestamp == 0#64) = false := bv64_beq_zero_false hts
    simp only [hts_beq, Bool.false_eq_true, ↓reduceIte] at hpc
    apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm_call =>
          sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := st) hvm_call (by sep_focus) ?_⟩
      refine hCallEV sp0 (BitVec.ofNat 64 (encPendingMem g p).length) v cap ptr
        ((blkPl_14).base + 756#64) (bs ++ [74#8]) st (by simp; omega) hfitEV (s0 := s0)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
        (by simp only [arm64_norm, ← uint64Field4_nonzero_length_bv hts, ← encPendingMem_length_bv g p, *])
        (by simp only [arm64_norm, *]) (by sep_focus) ?_
      intro sm cap' ptr' evs hpcm hrunm hspm htrm hcsm hevs
      have hevs_seg : EncRawSegEnv (bs.length + 1)
          (encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)).length evs :=
        (encodeVarintEnv_sub_boundedRustEvs
          (outLen := (bs.length + 1) +
            (encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)).length)
          (by simp only [List.length_append, List.length_singleton]; omega)
          (by omega) hevs).mono (by dsimp only; omega) (Nat.le_refl _)
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
            ⟨by simp only [wp_norm, arm64_norm], fun hvm_end =>
              sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := M.stepEvents evs st) hvm_end (by sep_focus) ?_⟩
          refine SepWPpLsCl.weaken_pre ?_ (hnext _ cap' ptr' evs
            (by simp only [arm64_norm, Bool.false_eq_true, ↓reduceIte, *])
            (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *])
            (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
            hevs_seg)
          simp only [sepConj_assoc]
          exact entails_of_sep_focus (by sep_focus)
      | some pkId =>
        simp only [hpk, optU32Tag] at hx24m
        apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 824#64)
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [wp_norm, arm64_norm], fun hvm_end =>
              sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := M.stepEvents evs st) hvm_end (by sep_focus) ?_⟩
          refine SepWPpLsCl.weaken_pre ?_ (hnext _ cap' ptr' evs
            (by simp only [arm64_norm, ↓reduceIte, *])
            (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *])
            (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
            hevs_seg)
          simp only [sepConj_assoc]
          exact entails_of_sep_focus (by sep_focus)

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PendingPreKeyFieldsXBPlacedBudgetAux
