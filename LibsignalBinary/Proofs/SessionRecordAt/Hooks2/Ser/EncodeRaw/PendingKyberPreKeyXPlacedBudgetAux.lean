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
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.BaseXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PendingKyberPreKeyXPlaced
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PrologueVersionLocalIdentityXPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.E2E.Record.Serialization.ChainLenAux.Pure
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.PendingPreKeyFields
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.RemoteIdentityRootKeyCounter
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.SenderReceiverChains
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PendingKyberPreKeyX
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `SessionStructure::encode_raw` Tag 14 Prefix (`1292` → `1504`)

Proves budget-threaded step lemmas for the `0x72` tag write, nested length calculation, outer length
varint, and subfield 1 (`pre_key_id`) of protobuf tag 14 (`pending_kyber_pre_key`, Block `14`
offsets `1292..1504`) under `RustCliAllocBudget M` and `EncRawSegEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PendingKyberPreKeyXPlacedBudgetAux

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSessionApi (PendingKyberPreKey)
open CryptoVerification (LibsignalPlacement LibsignalHooks lsmpl)
open CryptoVerification.RustHeap (vecHeader vecU8At)
open CryptoVerification.LibsignalTripleRatchetRepr (TailVecGhost)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  vecU8Buf vecU8At_eq_header_sep_buf cap_beq_len_false cap_eq_ofNat_len
  ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
)
open CryptoVerification.E2E.Record (uint32Field encPendingKyber)
open CryptoVerification.E2E.Record.Placed (blkPl_14 lsProg_14)
open CryptoVerification.E2E.Record.Serialization (
  encodeRawSubStackX sepWPpLsCl_extract_vecU8At_bounds
)
open CryptoVerification.E2E.Record.Serialization.EncodeRawAux (
  entails_of_sep_focus EncRawUpperSaved
  vecSrcRest vecCopyDone kyberTailRest kyberOpenAt
  uint32Field1_zero_eq_er uint32Field1_nonzero_eq_er uint32Field1_nonzero_length_bv_er
  encPendingKyber_length_bv encPendingKyber_length_bv_ct_nil bv_add_neg80_4b
  truncate32_signExtend64_er bytesField2_nonempty_length_bv er_truncate32_zext64_lsr6
  erHwVarintLen_eq_encodeVarint_length erHwVarintLen_bvShift_eq_encodeVarint_length
  zext64_beq_zero_false_3b cmn1_beq_zero_false cap_beq_noneCap_false
  vecU8At_open_one vecU8At_close_one sp_sub_80_spAligned
  ofNat64_len_beq_zero_false encodeVarint_length_le_10
)
open Proofs.libsignal.Hooks2 (SepWPpLsCl)
open LibsignalBinary.Heap (
  VmPreserved AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (DoReserveEnv)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget (EncodeVarintEnv)
open LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.BaseBudget (
  EncRawSegEnv encRawSegEnv_nil encRawSegEnv_append
  fitsEnv_encRawSeg_left fitsEnv_encRawSeg_right
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

/-! ## Tag `114#8` write and field loads (`1292 → 1348`, cold `2328..2352`) -/

theorem step_tag14_write_tag_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hDR : DoReservePlacedOkX M A lim H)
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (k : PendingKyberPreKey)
    (bs : List (BitVec 8))
    (st : M.σ)
    (hcap_g : g.vec.cap.toNat < 2 ^ 63)
    (hlen_lt : bs.length + 1 < 2 ^ 60)
    (hfit : FitsEnv M lim st (EncRawSegEnv bs.length 1))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 1292#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (kyberOpenAt A.repAlloc ss g k ∗ vecU8At A.repAlloc v cap ptr bs ∗
      A.pool lim st s ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_14).base + 1348#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x22 = BitVec.zeroExtend 64 k.preKeyId →
      sm.readReg64 .x21 = BitVec.ofNat 64 k.ciphertext.length →
      EncRawUpperSaved s0 sm →
      EncRawSegEnv bs.length 1 evs →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((kyberOpenAt A.repAlloc ss g k ∗ vecU8At A.repAlloc v cap' ptr' (bs ++ [114#8]) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hCallDR := @encraw_call_doReserve_buf_placed_x _ M A lim H hDR
  have h8 : (ss + 296#64) + 8#64 = ss + 304#64 := BitVec.add_assoc ss 296#64 8#64
  have h16 : (ss + 296#64) + 16#64 = ss + 312#64 := BitVec.add_assoc ss 296#64 16#64
  rw [hP]
  refine sepWPpLsCl_extract_vecU8At_bounds (A := A.repAlloc) (v := v) (cap := cap) (ptr := ptr) (bs := bs)
    (hfocus := by sep_focus) (h := fun hle _ _ => ?_)
  have hcmn1 := cmn1_beq_zero_false hcap_g
  have hcmn2 := cap_beq_noneCap_false hcap_g
  by_cases hlt : bs.length < cap.toNat
  · have hbeq_cap := cap_beq_len_false hlt
    rw [vecU8At_open_one A.repAlloc v cap ptr bs hlt]
    unfold kyberOpenAt
    rw [vecU8At_eq_header_sep_buf A.repAlloc (ss + 296#64) g.vec.cap g.vec.ptr k.ciphertext]
    simp only [vecHeader, h8, h16, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPpLsCl.exists_elim fun old => ?_
    apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 1348#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm0 =>
          sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := st) hvm0 (by sep_focus) ?_⟩
      refine SepWPpLsCl.weaken_pre ?_ (hnext _ cap ptr []
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
        (encRawSegEnv_nil _ _))
      rw [← vecU8At_close_one A.repAlloc v cap ptr bs 114#8 hlt]
      unfold kyberOpenAt
      rw [vecU8At_eq_header_sep_buf A.repAlloc (ss + 296#64) g.vec.cap g.vec.ptr k.ciphertext]
      simp only [vecHeader, h8, h16, sepConj_assoc]
      exact entails_of_sep_focus (by sep_focus)
  · have hcap_eq : cap.toNat = bs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    have hfitDR : FitsEnv M lim st (DoReserveEnv (DoReserveCall.mk v cap ptr bs 1)) :=
      fitsEnv_doReserve_of_encRawSeg (by omega) (by dsimp only; omega)
        (by dsimp only; omega) (by omega) hfit
    rw [vecU8At_eq_header_sep_buf A.repAlloc v cap ptr bs]
    unfold kyberOpenAt
    rw [vecU8At_eq_header_sep_buf A.repAlloc (ss + 296#64) g.vec.cap g.vec.ptr k.ciphertext]
    simp only [vecHeader, h8, h16, sepConj_assoc]
    apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 13)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm0 =>
          sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := st) hvm0 (by sep_focus) ?_⟩
      have hx1_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      refine hCallDR sp0 v cap ptr ((blkPl_14).base + 2348#64) bs 1 st
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
      apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 1348#64)
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm], fun hvm2 =>
            sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := M.stepEvents evs st) hvm2 (by sep_focus) ?_⟩
        refine SepWPpLsCl.weaken_pre ?_ (hnext _ newCap p1 evs
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
          hevs_seg)
        rw [← vecU8At_close_one A.repAlloc v newCap p1 bs 114#8 hlt_new]
        unfold kyberOpenAt
        rw [vecU8At_eq_header_sep_buf A.repAlloc (ss + 296#64) g.vec.cap g.vec.ptr k.ciphertext]
        simp only [vecHeader, h8, h16, sepConj_assoc]
        exact entails_of_sep_focus (by sep_focus)

/-! ## Subfield 1 (`pre_key_id`) length (`1348 → 1384/1440`) -/

theorem step_tag14_len1_placed_x [LibsignalPlacement] {H : LibsignalHooks}
    (ss v sp0 : BitVec 64) (k : PendingKyberPreKey)
    (hlt_ct : k.ciphertext.length < 2 ^ 63)
    {ret : BitVec 64} {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 1348#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hx22 : s.readReg64 .x22 = BitVec.zeroExtend 64 k.preKeyId)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 k.ciphertext.length)
    (hcs : EncRawUpperSaved s0 s)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_14).base +
        (if k.ciphertext.isEmpty then 1440#64 else 1384#64) →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x8 = BitVec.ofNat 64 (uint32Field 1 k.preKeyId).length →
      sm.readReg64 .x22 = BitVec.zeroExtend 64 k.preKeyId →
      sm.readReg64 .x21 = BitVec.ofNat 64 k.ciphertext.length →
      EncRawUpperSaved s0 sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm P Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  by_cases hpk : k.preKeyId = 0#32
  · by_cases hct : k.ciphertext = []
    · apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 1440#64)
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm], fun hvm0 => ?_⟩
        exact hnext _ hvm0 (by simp only [arm64_norm, List.isEmpty_nil, ↓reduceIte, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hpk, uint32Field1_zero_eq_er])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
    · have hempty : k.ciphertext.isEmpty = false := List.isEmpty_eq_false_iff.mpr hct
      have hbeq_ct := ofNat64_len_beq_zero_false hct hlt_ct
      apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 1384#64)
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm], fun hvm0 => ?_⟩
        exact hnext _ hvm0 (by simp only [arm64_norm, Bool.false_eq_true, ↓reduceIte, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hpk, uint32Field1_zero_eq_er])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
  · have hbeq0 := zext64_beq_zero_false_3b hpk
    by_cases hct : k.ciphertext = []
    · apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 1440#64)
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm], fun hvm0 => ?_⟩
        exact hnext _ hvm0 (by simp only [arm64_norm, List.isEmpty_nil, ↓reduceIte, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, ← uint32Field1_nonzero_length_bv_er hpk, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
    · have hempty : k.ciphertext.isEmpty = false := List.isEmpty_eq_false_iff.mpr hct
      have hbeq_ct := ofNat64_len_beq_zero_false hct hlt_ct
      apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 1384#64)
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm], fun hvm0 => ?_⟩
        exact hnext _ hvm0 (by simp only [arm64_norm, Bool.false_eq_true, ↓reduceIte, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, ← uint32Field1_nonzero_length_bv_er hpk, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)

/-! ## Subfield 2 length and outer length varint (`1384/1440 → 1456/1504`) -/

theorem step_tag14_len2_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (k : PendingKyberPreKey)
    (bs : List (BitVec 8))
    (st : M.σ)
    (hlen_lt : bs.length + 12 < 2 ^ 60)
    (hfit : FitsEnv M lim st
      (EncRawSegEnv (bs.length + 1)
        (encodeVarint (BitVec.ofNat 64 (encPendingKyber k).length)).length))
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
      A.pool lim st s ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64) (evs : List AllocEvent),
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
      EncRawSegEnv (bs.length + 1)
        (encodeVarint (BitVec.ofNat 64 (encPendingKyber k).length)).length evs →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((kyberOpenAt A.repAlloc ss g k ∗
          vecU8At A.repAlloc v cap' ptr'
            ((bs ++ [114#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingKyber k).length)) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  have hCallEV := @encraw_call_encodeVarint_placed_x _ M A lim H hEV
  have h10 := encodeVarint_length_le_10 (BitVec.ofNat 64 (encPendingKyber k).length)
  have hfitEV : FitsEnv M lim st
      (EncodeVarintEnv ⟨BitVec.ofNat 64 (encPendingKyber k).length, v, cap, ptr, bs ++ [114#8]⟩) :=
    fitsEnv_encodeVarint_of_encRawSeg (by dsimp only; omega)
      (by simp only [List.length_append, List.length_singleton]; omega)
      (by omega) hfit
  rw [hP]
  by_cases hct : k.ciphertext = []
  · have hempty : k.ciphertext.isEmpty = true := List.isEmpty_iff.mpr hct
    simp only [hempty, ↓reduceIte] at hpc
    apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm0 =>
          sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := st) hvm0 (by sep_focus) ?_⟩
      refine hCallEV sp0 (BitVec.ofNat 64 (encPendingKyber k).length) v cap ptr
        ((blkPl_14).base + 1452#64) (bs ++ [114#8]) st (by simp; omega) hfitEV (s0 := s0)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
        (by simp only [arm64_norm, ← encPendingKyber_length_bv_ct_nil k hct, *])
        (by simp only [arm64_norm, *]) (by sep_focus) ?_
      intro s1 cap' ptr' evs hpc1 hrun1 hsp1 htr1 hcs1 hevs
      have hevs_seg : EncRawSegEnv (bs.length + 1)
          (encodeVarint (BitVec.ofNat 64 (encPendingKyber k).length)).length evs :=
        (encodeVarintEnv_sub_boundedRustEvs
          (outLen := (bs.length + 1) +
            (encodeVarint (BitVec.ofNat 64 (encPendingKyber k).length)).length)
          (by simp only [List.length_append, List.length_singleton]; omega)
          (by omega) hevs).mono (by dsimp only; omega) (Nat.le_refl _)
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
            ⟨by simp only [wp_norm, arm64_norm], fun hvm2 =>
              sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := M.stepEvents evs st) hvm2 (by sep_focus) ?_⟩
          refine SepWPpLsCl.weaken_pre ?_ (hnext _ cap' ptr' evs
            (by simp only [arm64_norm, ↓reduceIte, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
            hevs_seg)
          exact entails_of_sep_focus (by sep_focus)
      · have hpk_beq : (k.preKeyId == 0#32) = false := beq_false_of_ne hpk
        have hbeq0 := zext64_beq_zero_false_3b hpk
        apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 1456#64)
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [wp_norm, arm64_norm], fun hvm2 =>
              sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := M.stepEvents evs st) hvm2 (by sep_focus) ?_⟩
          refine SepWPpLsCl.weaken_pre ?_ (hnext _ cap' ptr' evs
            (by simp only [arm64_norm, Bool.false_eq_true, ↓reduceIte, *])
            (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
            hevs_seg)
          exact entails_of_sep_focus (by sep_focus)
  · have hempty : k.ciphertext.isEmpty = false := List.isEmpty_eq_false_iff.mpr hct
    simp only [hempty, Bool.false_eq_true, ↓reduceIte] at hpc
    apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm0 =>
          sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := st) hvm0 (by sep_focus) ?_⟩
      refine hCallEV sp0 (BitVec.ofNat 64 (encPendingKyber k).length) v cap ptr
        ((blkPl_14).base + 1424#64) (bs ++ [114#8]) st (by simp; omega) hfitEV (s0 := s0)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
        (by simp only [arm64_norm, ← encPendingKyber_length_bv k, ← bytesField2_nonempty_length_bv hct, *])
        (by simp only [arm64_norm, *]) (by sep_focus) ?_
      intro s1 cap' ptr' evs hpc1 hrun1 hsp1 htr1 hcs1 hevs
      have hevs_seg : EncRawSegEnv (bs.length + 1)
          (encodeVarint (BitVec.ofNat 64 (encPendingKyber k).length)).length evs :=
        (encodeVarintEnv_sub_boundedRustEvs
          (outLen := (bs.length + 1) +
            (encodeVarint (BitVec.ofNat 64 (encPendingKyber k).length)).length)
          (by simp only [List.length_append, List.length_singleton]; omega)
          (by omega) hevs).mono (by dsimp only; omega) (Nat.le_refl _)
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
            ⟨by simp only [wp_norm, arm64_norm], fun hvm2 =>
              sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := M.stepEvents evs st) hvm2 (by sep_focus) ?_⟩
          refine SepWPpLsCl.weaken_pre ?_ (hnext _ cap' ptr' evs
            (by simp only [arm64_norm, ↓reduceIte, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
            hevs_seg)
          exact entails_of_sep_focus (by sep_focus)
      · have hpk_beq : (k.preKeyId == 0#32) = false := beq_false_of_ne hpk
        have hbeq0 := zext64_beq_zero_false_3b hpk
        apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_14).base + 1456#64)
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [wp_norm, arm64_norm], fun hvm2 =>
              sepWPpLsCl_transport_budgetPool (A := A) (lim := lim) (st := M.stepEvents evs st) hvm2 (by sep_focus) ?_⟩
          refine SepWPpLsCl.weaken_pre ?_ (hnext _ cap' ptr' evs
            (by simp only [arm64_norm, Bool.false_eq_true, ↓reduceIte, *])
            (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
            hevs_seg)
          exact entails_of_sep_focus (by sep_focus)

/-! ## Subfield 1 (`pre_key_id`) encoding (`1456/1504 → 1504`, cold `2620..2644`) -/

theorem step_tag14_sub1_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (hDR : DoReservePlacedOkX M A lim H)
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (k : PendingKyberPreKey)
    (bs : List (BitVec 8))
    (st : M.σ)
    (hlen_lt : bs.length + 12 < 2 ^ 60)
    (hfit : FitsEnv M lim st (EncRawSegEnv bs.length (uint32Field 1 k.preKeyId).length))
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
      A.pool lim st s ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_14).base + 1504#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x21 = BitVec.ofNat 64 k.ciphertext.length →
      EncRawUpperSaved s0 sm →
      EncRawSegEnv bs.length (uint32Field 1 k.preKeyId).length evs →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((kyberOpenAt A.repAlloc ss g k ∗
          vecU8At A.repAlloc v cap' ptr' (bs ++ uint32Field 1 k.preKeyId) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q Qp := by
  by_cases hpk : k.preKeyId = 0#32
  · simp only [hpk, beq_self_eq_true, ↓reduceIte] at hpc
    rw [hP]
    refine SepWPpLsCl.weaken_pre ?_
      (hnext s cap ptr [] hpc hrun hsp htr hx19 hx20 hx21 hcs
        (by rw [hpk, uint32Field1_zero_eq_er]; exact encRawSegEnv_nil _ _))
    simp only [hpk, uint32Field1_zero_eq_er, List.append_nil]
    exact entails_of_sep_focus (by sep_focus)
  · have hpk_beq : (k.preKeyId == 0#32) = false := beq_false_of_ne hpk
    simp only [hpk_beq, Bool.false_eq_true, ↓reduceIte] at hpc
    have hCallEV := @encraw_call_encodeVarint_placed_x _ M A lim H hEV
    have hCallDR := @encraw_call_doReserve_buf_placed_x _ M A lim H hDR
    have hflen : (uint32Field 1 k.preKeyId).length =
        1 + (encodeVarint (BitVec.zeroExtend 64 k.preKeyId)).length := by
      rw [← uint32Field1_nonzero_eq_er hpk]
      simp only [List.length_append, List.length_singleton]
    have hvlen10 := encodeVarint_length_le_10 (BitVec.zeroExtend 64 k.preKeyId)
    rw [hP]
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
            (EncodeVarintEnv ⟨BitVec.zeroExtend 64 k.preKeyId, v, cap, ptr, bs ++ [8#8]⟩) :=
          fitsEnv_encodeVarint_of_encRawSeg (by dsimp only; omega)
            (by simp only [List.length_append, List.length_singleton]; omega)
            (by omega) hfit
        refine SepWPpLsCl.weaken_pre
          (P' := (vecU8At A.repAlloc v cap ptr (bs ++ [8#8]) ∗
              A.pool lim st _ ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
            kyberOpenAt A.repAlloc ss g k ∗ F)
          (by
            rw [← vecU8At_close_one A.repAlloc v cap ptr bs 8#8 hlt]
            simp only [sepConj_assoc]
            exact entails_of_sep_focus (by sep_focus))
          (hCallEV sp0 (BitVec.zeroExtend 64 k.preKeyId) v cap ptr ((blkPl_14).base + 1504#64)
            (bs ++ [8#8]) st (by simp; omega) hfitEV (s0 := s0)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by sep_focus) ?_)
        intro s1 cap' ptr' evs hpc1 hrun1 hsp1 htr1 hcs1 hevs
        have hevs_seg : EncRawSegEnv bs.length (uint32Field 1 k.preKeyId).length evs :=
          (encodeVarintEnv_sub_boundedRustEvs
            (outLen := bs.length + (uint32Field 1 k.preKeyId).length)
            (by simp only [List.length_append, List.length_singleton]; omega)
            (by omega) hevs).mono (by dsimp only; omega) (Nat.le_refl _)
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
          (hnext s1 cap' ptr' evs hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hcs_1 hevs_seg)
        rw [List.append_assoc, uint32Field1_nonzero_eq_er hpk]
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
        refine hCallDR sp0 v cap ptr ((blkPl_14).base + 2640#64) bs 1 st
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
              (encodeVarint (BitVec.zeroExtend 64 k.preKeyId)).length) :=
          fitsEnv_encRawSeg_right hfit he1_seg
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
              (EncodeVarintEnv ⟨BitVec.zeroExtend 64 k.preKeyId, v, newCap, p1, bs ++ [8#8]⟩) :=
            fitsEnv_encodeVarint_of_encRawSeg (by dsimp only; omega)
              (by simp only [List.length_append, List.length_singleton]; omega)
              (by omega) hfit2
          refine SepWPpLsCl.weaken_pre
            (P' := (vecU8At A.repAlloc v newCap p1 (bs ++ [8#8]) ∗
                A.pool lim (M.stepEvents evs1 st) _ ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
              kyberOpenAt A.repAlloc ss g k ∗ F)
            (by
              rw [← vecU8At_close_one A.repAlloc v newCap p1 bs 8#8 hlt_new]
              simp only [sepConj_assoc]
              exact entails_of_sep_focus (by sep_focus))
            (hCallEV sp0 (BitVec.zeroExtend 64 k.preKeyId) v newCap p1 ((blkPl_14).base + 1504#64)
              (bs ++ [8#8]) (M.stepEvents evs1 st) (by simp; omega) hfitEV (s0 := s0)
              (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (sp_sub_80_spAligned halign (by simp only [arm64_norm, *]))
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by sep_focus) ?_)
          intro s2 cap' ptr' evs2 hpc2 hrun2 hsp2 htr2 hcs2 hevs2
          have he2_seg : EncRawSegEnv (bs.length + 1)
              (encodeVarint (BitVec.zeroExtend 64 k.preKeyId)).length evs2 :=
            (encodeVarintEnv_sub_boundedRustEvs
              (outLen := (bs.length + 1) +
                (encodeVarint (BitVec.zeroExtend 64 k.preKeyId)).length)
              (by simp only [List.length_append, List.length_singleton]; omega)
              (by omega) hevs2).mono (by dsimp only; omega) (Nat.le_refl _)
          have he12 : EncRawSegEnv bs.length (uint32Field 1 k.preKeyId).length (evs1 ++ evs2) := by
            rw [hflen]; exact encRawSegEnv_append he1_seg he2_seg
          have hx19_2 : s2.readReg64 .x19 = v := by
            have := hcs2.1; simp only [arm64_norm, *] at this; exact this
          have hx20_2 : s2.readReg64 .x20 = ss := by
            have := hcs2.2.1; simp only [arm64_norm, *] at this; exact this
          have hx21_2 : s2.readReg64 .x21 = BitVec.ofNat 64 k.ciphertext.length := by
            have := hcs2.2.2.1; simp only [arm64_norm, *] at this; exact this
          have hcs_2 : EncRawUpperSaved s0 s2 :=
            (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
              (EncRawUpperSaved.of_calleeSavedPreserved hcs2)
          rw [← M.stepEvents_append]
          refine SepWPpLsCl.weaken_pre ?_
            (hnext s2 cap' ptr' (evs1 ++ evs2) hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hcs_2 he12)
          rw [List.append_assoc, uint32Field1_nonzero_eq_er hpk]
          exact entails_of_sep_focus (by sep_focus)

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PendingKyberPreKeyXPlacedBudgetAux
