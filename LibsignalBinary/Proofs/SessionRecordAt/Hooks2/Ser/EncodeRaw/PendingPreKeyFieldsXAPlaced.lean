/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.PendingPreKeyHeader
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.BaseX
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PendingPreKeyFieldsXA
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PrologueVersionLocalIdentityXPlaced
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# Relocatable `SessionStructure::encode_raw` Tag 9 Subfields 1 and 2 (Block `14`)

Verifies subfields 1 (`pre_key_id`) and 2 (`base_key`) of protobuf tag 9 (`pending_pre_key`,
Block `14` offsets `824/872..976`) under `[LibsignalPlacement]`.
-/

namespace CryptoVerification.E2E.Record.Serialization

open Arm64 Arm64.Obj ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.Placed
open CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.E2E.Record.Serialization.EncodeRawAux
open Proofs.libsignal.Hooks2

set_option allowUnsafeReducibility true
attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local irreducible] stackAt vecRest RustHeap.vecU8Buf vecSrcRest vecCopyDone
attribute [local irreducible] optU32ValAt pendingTailRest
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  truncate32_signExtend64_er truncate32_zeroExtend64 bv_add_neg80_3b

set_option maxHeartbeats 400000

section Placed

/-! ## Subfield 1 (`pre_key_id`, `824/872 → 872`, cold `2752..2784`) -/

theorem step_tag9_sub1_placed_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hEV : EncodeVarintPlacedOkX A H)
    (hDR : DoReservePlacedOkX A H)
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (bs : List (BitVec 8))
    (hlen_lt : bs.length + 12 < 2 ^ 60)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
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
    (hP : P = (pendingOpenAt A ss g p ∗ vecU8At A v cap ptr bs ∗
      A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_frame)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
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
        ((pendingOpenAt A ss g p ∗ vecU8At A v cap' ptr' (bs ++ optUint32Field 1 p.preKeyId) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q (PanicAllocPost s0) := by
  cases hpk : p.preKeyId with
  | none =>
    simp only [hpk, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc
    rw [hP]
    refine SepWPpLsCl.weaken_pre ?_ (hnext s cap ptr hpc hrun hsp htr hx19 hx20 hx23 hx22 hx21 hcs)
    simp only [hpk, optUint32Field1_none_eq, List.append_nil]
    exact (by sep_frame)
  | some pkId =>
    simp only [hpk, Option.isSome_some, ↓reduceIte] at hpc
    have hCallEV := @encraw_call_encodeVarint_placed_x _ A H hEV
    have hCallDR := @encraw_call_doReserve_buf_placed_x _ A H hDR
    have hpk_val : optU32ValAt (ss + 276#64) g.tail (some pkId) = ((ss + 276#64) ↦₃₂ pkId) :=
      optU32ValAt_some _ _ _
    rw [hP]
    refine sepWPpLsCl_extract_vecU8At_bounds (A := A) (v := v) (cap := cap) (ptr := ptr) (bs := bs)
      (h := fun hle _ _ => ?_)
    by_cases hlt : bs.length < cap.toNat
    · have hbeq_cap := cap_beq_len_false hlt
      rw [vecU8At_open_one A v cap ptr bs hlt]
      unfold pendingOpenAt
      rw [hpk, hpk_val]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPpLsCl.exists_elim fun old => ?_
      apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 10)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      have hclose := vecU8At_close_one A v cap ptr bs 8#8 hlt
      refine SepWPpLsCl.weaken_pre (P' :=
          (vecU8At A v cap ptr (bs ++ [8#8]) ∗ A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
            (pendingOpenAt A ss g p ∗ F))
        (by
          rw [← hclose]
          unfold pendingOpenAt
          rw [hpk, hpk_val]
          exact (by sep_frame)) ?_
      refine hCallEV sp0 (BitVec.zeroExtend 64 pkId) v cap ptr ((blkPl_14).base + 872#64) (bs ++ [8#8])
        (by simp; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_frame) ?_
      · simp only [arm64_norm]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
      · simp only [arm64_norm, *]
      · simp only [arm64_norm]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm]
      · intro s1 cap' ptr' hpc1 hrun1 hsp1 htr1 hcs1
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
        refine SepWPpLsCl.weaken_pre ?_ (hnext s1 cap' ptr' hpc1 hrun1 hsp1 htr1
          hx19_1 hx20_1 hx23_1 hx22_1 hx21_1 hcs_1)
        rw [List.append_assoc, hpk, optUint32Field1_some_eq pkId]
        exact (by sep_frame)
    · have hcap_eq : cap.toNat = bs.length := by omega
      have hcap_bv := cap_eq_ofNat_len hcap_eq
      rw [Prost.vecU8At_eq_header_sep_buf A v cap ptr bs]
      unfold pendingOpenAt
      rw [hpk, hpk_val]
      simp only [vecHeader, sepConj_assoc]
      apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 13)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      have hx1_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      refine hCallDR sp0 v cap ptr ((blkPl_14).base + 2776#64) bs 1
        (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_frame) ?_
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
      · intro s1 newCap p1 hpc1 hrun1 hsp1 htr1 hcs1 hnew_ge _
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
        rw [vecU8At_open_one A v newCap p1 bs hlt_new]
        simp only [sepExists_sepConj_left, sepConj_assoc]
        refine SepWPpLsCl.exists_elim fun old => ?_
        apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 10)
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        have hclose := vecU8At_close_one A v newCap p1 bs 8#8 hlt_new
        refine SepWPpLsCl.weaken_pre (P' :=
            (vecU8At A v newCap p1 (bs ++ [8#8]) ∗ A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
              (pendingOpenAt A ss g p ∗ F))
          (by
            rw [← hclose]
            unfold pendingOpenAt
            rw [hpk, hpk_val]
            exact (by sep_frame)) ?_
        refine hCallEV sp0 (BitVec.zeroExtend 64 pkId) v newCap p1 ((blkPl_14).base + 872#64) (bs ++ [8#8])
          (by simp; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_frame) ?_
        · simp only [arm64_norm]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm]
        · intro s2 cap' ptr' hpc2 hrun2 hsp2 htr2 hcs2
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
          refine SepWPpLsCl.weaken_pre ?_ (hnext s2 cap' ptr' hpc2 hrun2 hsp2 htr2
            hx19_2 hx20_2 hx23_2 hx22_2 hx21_2 hcs_2)
          rw [List.append_assoc, hpk, optUint32Field1_some_eq pkId]
          exact (by sep_frame)

/-! ## Subfield 2 (`base_key`) header and varint (`872 → 928`, cold `2460..2488`) -/

theorem step_tag9_sub2_a_placed_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hEV : EncodeVarintPlacedOkX A H)
    (hDR : DoReservePlacedOkX A H)
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (bs : List (BitVec 8))
    (hne_vec : g.vec.bytes ≠ []) (hlt_vec : g.vec.bytes.length < 2 ^ 63)
    (hlen_lt : bs.length + 12 < 2 ^ 60)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
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
    (hP : P = (pendingOpenAt A ss g p ∗ vecU8At A v cap ptr bs ∗
      A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_frame)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
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
        ((pendingOpenAt A ss g p ∗
          vecU8At A v cap' ptr' (bs ++ ([18#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length))) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q (PanicAllocPost s0) := by
  have hCallEV := @encraw_call_encodeVarint_placed_x _ A H hEV
  have hCallDR := @encraw_call_doReserve_buf_placed_x _ A H hDR
  have hbeq0 := ofNat64_len_beq_zero_false hne_vec hlt_vec
  rw [hP]
  refine sepWPpLsCl_extract_vecU8At_bounds (A := A) (v := v) (cap := cap) (ptr := ptr) (bs := bs)
    (h := fun hle _ _ => ?_)
  by_cases hlt : bs.length < cap.toNat
  · have hbeq_cap := cap_beq_len_false hlt
    rw [vecU8At_open_one A v cap ptr bs hlt]
    unfold pendingOpenAt
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPpLsCl.exists_elim fun old => ?_
    apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 10)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    have hclose := vecU8At_close_one A v cap ptr bs 18#8 hlt
    refine SepWPpLsCl.weaken_pre (P' :=
        (vecU8At A v cap ptr (bs ++ [18#8]) ∗ A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
          (pendingOpenAt A ss g p ∗ F))
      (by
        rw [← hclose]
        unfold pendingOpenAt
        exact (by sep_frame)) ?_
    refine hCallEV sp0 (BitVec.ofNat 64 g.vec.bytes.length) v cap ptr ((blkPl_14).base + 928#64) (bs ++ [18#8])
      (by simp; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_frame) ?_
    · simp only [arm64_norm]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm]
    · intro s1 cap' ptr' hpc1 hrun1 hsp1 htr1 hcs1
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
      refine SepWPpLsCl.weaken_pre ?_ (hnext s1 cap' ptr' hpc1 hrun1 hsp1 htr1
        hx19_1 hx20_1 hx24_1 hx23_1 hx22_1 hx21_1 hcs_1)
      rw [List.append_assoc]
      exact (by sep_frame)
  · have hcap_eq : cap.toNat = bs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    rw [Prost.vecU8At_eq_header_sep_buf A v cap ptr bs]
    unfold pendingOpenAt
    simp only [vecHeader, sepConj_assoc]
    apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 13)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    have hx1_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine hCallDR sp0 v cap ptr ((blkPl_14).base + 2480#64) bs 1
      (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_frame) ?_
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
    · intro s1 newCap p1 hpc1 hrun1 hsp1 htr1 hcs1 hnew_ge _
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
      rw [vecU8At_open_one A v newCap p1 bs hlt_new]
      simp only [sepExists_sepConj_left, sepConj_assoc]
      refine SepWPpLsCl.exists_elim fun old => ?_
      apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 10)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      have hclose := vecU8At_close_one A v newCap p1 bs 18#8 hlt_new
      refine SepWPpLsCl.weaken_pre (P' :=
          (vecU8At A v newCap p1 (bs ++ [18#8]) ∗ A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
            (pendingOpenAt A ss g p ∗ F))
        (by
          rw [← hclose]
          unfold pendingOpenAt
          exact (by sep_frame)) ?_
      refine hCallEV sp0 (BitVec.ofNat 64 g.vec.bytes.length) v newCap p1 ((blkPl_14).base + 928#64) (bs ++ [18#8])
        (by simp; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_frame) ?_
      · simp only [arm64_norm]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm]
      · intro s2 cap' ptr' hpc2 hrun2 hsp2 htr2 hcs2
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
        refine SepWPpLsCl.weaken_pre ?_ (hnext s2 cap' ptr' hpc2 hrun2 hsp2 htr2
          hx19_2 hx20_2 hx24_2 hx23_2 hx22_2 hx21_2 hcs_2)
        rw [List.append_assoc]
        exact (by sep_frame)

/-! ## Subfield 2 (`base_key`) reserve and `memcpy` (`928 → 976`, cold `2488..2564`) -/

theorem step_tag9_sub2_b_placed_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hDR : DoReservePlacedOkX A H)
    (hC : SerContractsXPlaced A H)
    (ss v sp0 cap1 ptr1 : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (bs1 : List (BitVec 8))
    (hne_vec : g.vec.bytes ≠ [])
    (hfit1 : bs1.length + g.vec.bytes.length < 2 ^ 60)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
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
    (hP : P = (pendingOpenAt A ss g p ∗ vecU8At A v cap1 ptr1 bs1 ∗
      A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_frame)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
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
        ((pendingOpenAt A ss g p ∗ vecU8At A v cap' ptr' (bs1 ++ g.vec.bytes) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q (PanicAllocPost s0) := by
  have hCallDR := @encraw_call_doReserve_buf_placed_x _ A H hDR
  have hCallMC := @encraw_call_memcpy_buf_placed_x _ A H hC
  rw [hP]
  refine sepWPpLsCl_extract_vecU8At_bounds (A := A) (v := v) (cap := cap1) (ptr := ptr1) (bs := bs1)
    (h := fun hle1 hcap1 hptr1 => ?_)
  rw [Prost.vecU8At_eq_header_sep_buf A v cap1 ptr1 bs1]
  unfold pendingOpenAt
  simp only [vecHeader, sepConj_assoc]
  have hx2_nat : (BitVec.ofNat 64 g.vec.bytes.length).toNat = g.vec.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  by_cases hroom : bs1.length + g.vec.bytes.length ≤ cap1.toNat
  · have hhi := cmp_hi_false_of_le hroom hcap1
    apply SepWPpLsCl.of_sepWP (mid := lsρ CryptoVerification.lsMemcpySym)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine hCallMC sp0 v cap1 ptr1 g.vec.ptr ((blkPl_14).base + 968#64) bs1 g.vec.bytes hroom hcap1 hptr1 hne_vec
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_frame) ?_
    · simp only [arm64_norm]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · intro sm hpcm hrunm hspm htrm hcsm
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
      have hspm' : sm.sp = sp0 - 80#64 := hspm
      have hcsm' : EncRawUpperSaved s0 sm :=
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
          (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
      apply SepWPpLsCl.of_sepWP (mid := (blkPl_14).base + 976#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      rw [vecU8At_close_slice A v cap1 ptr1 bs1 g.vec.bytes hroom hcap1 hptr1 hne_vec]
      refine SepWPpLsCl.weaken_pre ?_ (hnext _ cap1 ptr1
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      unfold pendingOpenAt
      exact (by sep_frame)
  · have hhi := cmp_hi_true_of_gt (add := g.vec.bytes.length) hle1 (by omega) hcap1 (by omega)
    apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 13)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    have hx1_nat : (BitVec.ofNat 64 bs1.length).toNat = bs1.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hx2_nat : (BitVec.ofNat 64 g.vec.bytes.length).toNat = g.vec.bytes.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine hCallDR sp0 v cap1 ptr1 ((blkPl_14).base + 2512#64) bs1 g.vec.bytes.length
      (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_frame) ?_
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
    · intro s1 newCap p' hpc1 hrun1 hsp1 htr1 hcs1 hnew_ge hnew_lt
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
      refine sepWPpLsCl_extract_vecU8At_bounds (A := A) (v := v) (cap := newCap) (ptr := p') (bs := bs1)
        (h := fun _ _ hp'_ne => ?_)
      rw [Prost.vecU8At_eq_header_sep_buf A v newCap p' bs1]
      simp only [vecHeader, sepConj_assoc]
      apply SepWPpLsCl.of_sepWP (mid := lsρ CryptoVerification.lsMemcpySym)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      refine hCallMC sp0 v newCap p' g.vec.ptr ((blkPl_14).base + 968#64) bs1 g.vec.bytes hnew_ge hnew_lt hp'_ne hne_vec
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_frame) ?_
      · simp only [arm64_norm]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · intro sm hpcm hrunm hspm htrm hcsm
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
        have hspm' : sm.sp = sp0 - 80#64 := hspm
        have hcsm' : EncRawUpperSaved s0 sm :=
          (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
            (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
        apply SepWPpLsCl.of_sepWP (mid := (blkPl_14).base + 976#64)
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        rw [vecU8At_close_slice A v newCap p' bs1 g.vec.bytes hnew_ge hnew_lt hp'_ne hne_vec]
        refine SepWPpLsCl.weaken_pre ?_ (hnext _ newCap p'
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
        unfold pendingOpenAt
        exact (by sep_frame)

end Placed

end CryptoVerification.E2E.Record.Serialization
