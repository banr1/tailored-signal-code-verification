/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.PendingPreKeyHeader
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `SessionStructure::encode_raw` tag 9 (`pending_pre_key` subfields 1–4, `+0x338..+0x438`)
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.Serialization.EncodeRawAux

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.E2E.Record

theorem optUint32Field1_length_le (opt : Option (BitVec 32)) :
    (optUint32Field 1 opt).length ≤ 11 := by
  cases opt with
  | none => simp [optUint32Field1_none_eq]
  | some pkId =>
    rw [← optUint32Field1_some_eq pkId]
    have h := encodeVarint_length_le_10 (BitVec.zeroExtend 64 pkId)
    simp only [List.length_append, List.length_singleton]
    omega

theorem bytesField2_length_le (bs : List (BitVec 8)) :
    (bytesField 2 bs).length ≤ bs.length + 11 := by
  by_cases hne : bs = []
  · subst hne; simp [bytesField]
  · rw [← bytesField2_nonempty_eq hne]
    have h := encodeVarint_length_le_10 (BitVec.ofNat 64 bs.length)
    simp only [List.length_append, List.length_singleton]
    omega

theorem int32Field3_length_le (v : BitVec 32) :
    (int32Field 3 v).length ≤ 11 := by
  by_cases hv : v = 0#32
  · subst hv; simp [int32Field3_zero_eq]
  · rw [← int32Field3_nonzero_eq hv]
    have h := encodeVarint_length_le_10 (BitVec.signExtend 64 v)
    simp only [List.length_append, List.length_singleton]
    omega

theorem uint64Field4_length_le (v : BitVec 64) :
    (uint64Field 4 v).length ≤ 11 := by
  by_cases hv : v = 0#64
  · subst hv; simp [uint64Field4_zero_eq]
  · rw [← uint64Field4_nonzero_eq hv]
    have h := encodeVarint_length_le_10 v
    simp only [List.length_append, List.length_singleton]
    omega

theorem encPendingMem_length_le (g : TailVecGhost) (p : PendingPreKey) :
    (encPendingMem g p).length ≤ g.vec.bytes.length + 44 := by
  unfold encPendingMem
  have h1 := optUint32Field1_length_le p.preKeyId
  have h2 := bytesField2_length_le g.vec.bytes
  have h3 := int32Field3_length_le p.signedPreKeyId
  have h4 := uint64Field4_length_le p.timestamp
  simp only [List.length_append]
  omega

theorem encPendingFieldMem_length_le (G_pending : Option TailVecGhost) (s_pending : Option PendingPreKey)
    (hbound : match G_pending with | none => True | some g => g.vec.bytes.length < 2 ^ 32) :
    (encPendingFieldMem G_pending s_pending).length < 2 ^ 32 + 60 := by
  cases G_pending with
  | none =>
    cases s_pending <;> simp [encPendingFieldMem]
  | some g =>
    cases s_pending with
    | none => simp [encPendingFieldMem]
    | some p =>
      rw [← lenField9_eq g p]
      have h0 := encodeVarint_length_le_10 (BitVec.ofNat 64 (encPendingMem g p).length)
      have h1 := optUint32Field1_length_le p.preKeyId
      have h2 := bytesField2_length_le g.vec.bytes
      have h3 := int32Field3_length_le p.signedPreKeyId
      have h4 := uint64Field4_length_le p.timestamp
      simp only [List.length_append, List.length_singleton]
      omega

theorem optTailVecAt_pending_none_eq (A : RustAlloc) (ss : BitVec 64) :
    optTailVecAt A 48 (ss + 248#64) none =
      ((ss + 248#64) ↦₆₄ noneCap) ∗ memRegion (ss + 256#64) (48 - 8) := by
  have hadd : (ss + 248#64) + 8#64 = ss + 256#64 := by bv_lin
  dsimp only [optTailVecAt]
  rw [hadd]

set_option allowUnsafeReducibility true
attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local irreducible] stackAt vecRest vecU8Buf vecSrcRest vecCopyDone
attribute [local irreducible] optU32ValAt pendingTailRest
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  truncate32_signExtend64_er truncate32_zeroExtend64

@[local arm64_norm]
theorem bv_add_neg80_3b (x : BitVec 64) : x + bv% (2 ^ 64 - 80) = x - 80#64 :=
  (BitVec.sub_eq_add_neg x 80#64).symm

set_option maxHeartbeats 400000

/-! ## Subfield 1 (`pre_key_id`, `824/872..872`) -/

theorem step_tag9_sub1 {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hEV : OkAt b C ctl abs encodeVarintName (encodeVarintSpec A))
    (hDR : OkAt b C ctl abs doReserveName (doReserveSpec A))
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (bs : List (BitVec 8))
    (hlen_lt : bs.length + 12 < 2 ^ 60)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName +
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
      A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName + 872#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length →
      sm.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId →
      sm.readReg64 .x21 = p.timestamp →
      EncRawUpperSaved s0 sm →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        ((pendingOpenAt A ss g p ∗ vecU8At A v cap' ptr' (bs ++ optUint32Field 1 p.preKeyId) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q (PanicAllocPost s0) := by
  cases hpk : p.preKeyId with
  | none =>
    simp only [hpk, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc
    rw [hP]
    refine SepWPp.weaken_pre ?_ (hnext s cap ptr hpc hrun hsp htr hx19 hx20 hx23 hx22 hx21 hcs)
    simp only [hpk, optUint32Field1_none_eq, List.append_nil]
    exact entails_of_sep_focus (by sep_focus)
  | some pkId =>
    simp only [hpk, Option.isSome_some, ↓reduceIte] at hpc
    have hCallEV := @encraw_call_encodeVarint b C A ctl abs hEV
    have hCallDR := @encraw_call_doReserve_buf b C A ctl abs hDR
    encraw_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 824 872
    encraw_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 2752 2784
    generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName = entry
    examples_hide_fetches
    have hpk_val : optU32ValAt (ss + 276#64) g.tail (some pkId) = ((ss + 276#64) ↦₃₂ pkId) :=
      optU32ValAt_some _ _ _
    rw [hP]
    refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap) (ptr := ptr) (bs := bs)
      (h := fun hle _ _ => ?_)
    by_cases hlt : bs.length < cap.toNat
    · have hbeq_cap := cap_beq_len_false hlt
      rw [vecU8At_open_one A v cap ptr bs hlt]
      unfold pendingOpenAt
      rw [hpk, hpk_val]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPp.exists_elim fun old => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      have hclose := vecU8At_close_one A v cap ptr bs 0x08#8 hlt
      refine SepWPp.weaken_pre (P' :=
          (vecU8At A v cap ptr (bs ++ [0x08#8]) ∗ A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗
            (pendingOpenAt A ss g p ∗ F))
        (by
          rw [← hclose]
          unfold pendingOpenAt
          rw [hpk, hpk_val]
          exact entails_of_sep_focus (by sep_focus)) ?_
      refine hCallEV sp0 (BitVec.zeroExtend 64 pkId) v cap ptr (entry + bv% (872)) (bs ++ [0x08#8])
        (by simp; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
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
        refine SepWPp.weaken_pre ?_ (hnext s1 cap' ptr' hpc1 hrun1 hsp1 htr1
          hx19_1 hx20_1 hx23_1 hx22_1 hx21_1 hcs_1)
        rw [List.append_assoc, hpk, optUint32Field1_some_eq pkId]
        exact entails_of_sep_focus (by sep_focus)
    · have hcap_eq : cap.toNat = bs.length := by omega
      have hcap_bv := cap_eq_ofNat_len hcap_eq
      rw [vecU8At_eq_header_sep_buf A v cap ptr bs]
      unfold pendingOpenAt
      rw [hpk, hpk_val]
      simp only [vecHeader, sepConj_assoc]
      apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      have hx1_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      refine hCallDR sp0 v cap ptr (entry + bv% (2776)) bs 1
        (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
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
        refine SepWPp.exists_elim fun old => ?_
        apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        have hclose := vecU8At_close_one A v newCap p1 bs 0x08#8 hlt_new
        refine SepWPp.weaken_pre (P' :=
            (vecU8At A v newCap p1 (bs ++ [0x08#8]) ∗ A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗
              (pendingOpenAt A ss g p ∗ F))
          (by
            rw [← hclose]
            unfold pendingOpenAt
            rw [hpk, hpk_val]
            exact entails_of_sep_focus (by sep_focus)) ?_
        refine hCallEV sp0 (BitVec.zeroExtend 64 pkId) v newCap p1 (entry + bv% (872)) (bs ++ [0x08#8])
          (by simp; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
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
          refine SepWPp.weaken_pre ?_ (hnext s2 cap' ptr' hpc2 hrun2 hsp2 htr2
            hx19_2 hx20_2 hx23_2 hx22_2 hx21_2 hcs_2)
          rw [List.append_assoc, hpk, optUint32Field1_some_eq pkId]
          exact entails_of_sep_focus (by sep_focus)

/-! ## Subfield 2 header and length varint (`base_key`, `872..928`) -/

theorem step_tag9_sub2_a {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hEV : OkAt b C ctl abs encodeVarintName (encodeVarintSpec A))
    (hDR : OkAt b C ctl abs doReserveName (doReserveSpec A))
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (bs : List (BitVec 8))
    (hne_vec : g.vec.bytes ≠ []) (hlt_vec : g.vec.bytes.length < 2 ^ 63)
    (hlen_lt : bs.length + 12 < 2 ^ 60)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName + 872#64)
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
      A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName + 928#64 →
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
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        ((pendingOpenAt A ss g p ∗
          vecU8At A v cap' ptr' (bs ++ ([0x12#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length))) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q (PanicAllocPost s0) := by
  have hCallEV := @encraw_call_encodeVarint b C A ctl abs hEV
  have hCallDR := @encraw_call_doReserve_buf b C A ctl abs hDR
  encraw_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 872 928
  encraw_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 2460 2488
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName = entry
  examples_hide_fetches
  have hbeq0 := ofNat64_len_beq_zero_false hne_vec hlt_vec
  rw [hP]
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap) (ptr := ptr) (bs := bs)
    (h := fun hle _ _ => ?_)
  by_cases hlt : bs.length < cap.toNat
  · have hbeq_cap := cap_beq_len_false hlt
    rw [vecU8At_open_one A v cap ptr bs hlt]
    unfold pendingOpenAt
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun old => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    have hclose := vecU8At_close_one A v cap ptr bs 0x12#8 hlt
    refine SepWPp.weaken_pre (P' :=
        (vecU8At A v cap ptr (bs ++ [0x12#8]) ∗ A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗
          (pendingOpenAt A ss g p ∗ F))
      (by
        rw [← hclose]
        unfold pendingOpenAt
        exact entails_of_sep_focus (by sep_focus)) ?_
    refine hCallEV sp0 (BitVec.ofNat 64 g.vec.bytes.length) v cap ptr (entry + bv% (928)) (bs ++ [0x12#8])
      (by simp; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
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
      refine SepWPp.weaken_pre ?_ (hnext s1 cap' ptr' hpc1 hrun1 hsp1 htr1
        hx19_1 hx20_1 hx24_1 hx23_1 hx22_1 hx21_1 hcs_1)
      rw [List.append_assoc]
      exact entails_of_sep_focus (by sep_focus)
  · have hcap_eq : cap.toNat = bs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    rw [vecU8At_eq_header_sep_buf A v cap ptr bs]
    unfold pendingOpenAt
    simp only [vecHeader, sepConj_assoc]
    apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    have hx1_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine hCallDR sp0 v cap ptr (entry + bv% (2480)) bs 1
      (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
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
      refine SepWPp.exists_elim fun old => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      have hclose := vecU8At_close_one A v newCap p1 bs 0x12#8 hlt_new
      refine SepWPp.weaken_pre (P' :=
          (vecU8At A v newCap p1 (bs ++ [0x12#8]) ∗ A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗
            (pendingOpenAt A ss g p ∗ F))
        (by
          rw [← hclose]
          unfold pendingOpenAt
          exact entails_of_sep_focus (by sep_focus)) ?_
      refine hCallEV sp0 (BitVec.ofNat 64 g.vec.bytes.length) v newCap p1 (entry + bv% (928)) (bs ++ [0x12#8])
        (by simp; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
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
        refine SepWPp.weaken_pre ?_ (hnext s2 cap' ptr' hpc2 hrun2 hsp2 htr2
          hx19_2 hx20_2 hx24_2 hx23_2 hx22_2 hx21_2 hcs_2)
        rw [List.append_assoc]
        exact entails_of_sep_focus (by sep_focus)

/-! ## Subfield 2 reserve and `memcpy` (`base_key`, `928..976`) -/

theorem step_tag9_sub2_b {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hDR : OkAt b C ctl abs doReserveName (doReserveSpec A))
    (ss v sp0 cap1 ptr1 : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (bs1 : List (BitVec 8))
    (hne_vec : g.vec.bytes ≠ [])
    (hfit1 : bs1.length + g.vec.bytes.length < 2 ^ 60)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName + 928#64)
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
      A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName + 976#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId →
      sm.readReg64 .x21 = p.timestamp →
      EncRawUpperSaved s0 sm →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        ((pendingOpenAt A ss g p ∗ vecU8At A v cap' ptr' (bs1 ++ g.vec.bytes) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q (PanicAllocPost s0) := by
  have hCallDR := @encraw_call_doReserve_buf b C A ctl abs hDR
  have hCallMC := @encraw_call_memcpy_buf b C A ctl abs
  encraw_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 928 976
  encraw_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 2488 2564
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName = entry
  examples_hide_fetches
  rw [hP]
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap1) (ptr := ptr1) (bs := bs1)
    (h := fun hle1 hcap1 hptr1 => ?_)
  rw [vecU8At_eq_header_sep_buf A v cap1 ptr1 bs1]
  unfold pendingOpenAt
  simp only [vecHeader, sepConj_assoc]
  have hx2_nat : (BitVec.ofNat 64 g.vec.bytes.length).toNat = g.vec.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  by_cases hroom : bs1.length + g.vec.bytes.length ≤ cap1.toNat
  · have hhi := cmp_hi_false_of_le hroom hcap1
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine hCallMC v cap1 ptr1 g.vec.ptr (entry + bv% (968)) bs1 g.vec.bytes hroom hcap1 hptr1 hne_vec
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
    · simp only [arm64_norm]
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
      have hspm' : sm.sp = sp0 - 80#64 := by
        rw [hspm]; simp only [arm64_norm, *]
      have hcsm' : EncRawUpperSaved s0 sm :=
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
          (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
      apply SepWPp.of_sepWP (mid := entry + bv% (976))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      rw [vecU8At_close_slice A v cap1 ptr1 bs1 g.vec.bytes hroom hcap1 hptr1 hne_vec]
      refine SepWPp.weaken_pre ?_ (hnext _ cap1 ptr1
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      unfold pendingOpenAt
      exact entails_of_sep_focus (by sep_focus)
  · have hhi := cmp_hi_true_of_gt (add := g.vec.bytes.length) hle1 (by omega) hcap1 (by omega)
    apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    have hx1_nat : (BitVec.ofNat 64 bs1.length).toNat = bs1.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hx2_nat : (BitVec.ofNat 64 g.vec.bytes.length).toNat = g.vec.bytes.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine hCallDR sp0 v cap1 ptr1 (entry + bv% (2512)) bs1 g.vec.bytes.length
      (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
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
      refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := newCap) (ptr := p') (bs := bs1)
        (h := fun _ _ hp'_ne => ?_)
      rw [vecU8At_eq_header_sep_buf A v newCap p' bs1]
      simp only [vecHeader, sepConj_assoc]
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>"))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      refine hCallMC v newCap p' g.vec.ptr (entry + bv% (968)) bs1 g.vec.bytes hnew_ge hnew_lt hp'_ne hne_vec
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
      · simp only [arm64_norm]
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
        have hspm' : sm.sp = sp0 - 80#64 := by
          rw [hspm]; simp only [arm64_norm, *]
        have hcsm' : EncRawUpperSaved s0 sm :=
          (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
            (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
        apply SepWPp.of_sepWP (mid := entry + bv% (976))
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        rw [vecU8At_close_slice A v newCap p' bs1 g.vec.bytes hnew_ge hnew_lt hp'_ne hne_vec]
        refine SepWPp.weaken_pre ?_ (hnext _ newCap p'
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
        unfold pendingOpenAt
        exact entails_of_sep_focus (by sep_focus)

/-! ## Subfield 3 (`signed_pre_key_id`, `976..1028`) -/

theorem zext64_beq_zero_false_3b {v : BitVec 32} (h : v ≠ 0#32) :
    (BitVec.zeroExtend 64 v == 0#64) = false := by
  rw [zext64_beq_zero_eq v]
  exact beq_false_of_ne h

theorem step_tag9_sub3 {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hEV : OkAt b C ctl abs encodeVarintName (encodeVarintSpec A))
    (hDR : OkAt b C ctl abs doReserveName (doReserveSpec A))
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (bs : List (BitVec 8))
    (hlen_lt : bs.length + 12 < 2 ^ 60)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName + 976#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hx22 : s.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId)
    (hx21 : s.readReg64 .x21 = p.timestamp)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (pendingOpenAt A ss g p ∗ vecU8At A v cap ptr bs ∗
      A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName + 1028#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x21 = p.timestamp →
      EncRawUpperSaved s0 sm →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        ((pendingOpenAt A ss g p ∗ vecU8At A v cap' ptr' (bs ++ int32Field 3 p.signedPreKeyId) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q (PanicAllocPost s0) := by
  have hCallEV := @encraw_call_encodeVarint b C A ctl abs hEV
  have hCallDR := @encraw_call_doReserve_buf b C A ctl abs hDR
  encraw_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 976 1028
  encraw_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 2564 2592
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName = entry
  examples_hide_fetches
  rw [hP]
  by_cases hspk : p.signedPreKeyId = 0#32
  · simp only [sepConj_assoc]
    apply SepWPp.of_sepWP (mid := entry + bv% (1028))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine SepWPp.weaken_pre ?_ (hnext _ cap ptr
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
    simp only [hspk, int32Field3_zero_eq, List.append_nil]
    exact entails_of_sep_focus (by sep_focus)
  · have hbeq0 := zext64_beq_zero_false_3b hspk
    refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap) (ptr := ptr) (bs := bs)
      (h := fun hle _ _ => ?_)
    by_cases hlt : bs.length < cap.toNat
    · have hbeq_cap := cap_beq_len_false hlt
      rw [vecU8At_open_one A v cap ptr bs hlt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPp.exists_elim fun old => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      have hclose := vecU8At_close_one A v cap ptr bs 0x18#8 hlt
      refine SepWPp.weaken_pre (P' :=
          (vecU8At A v cap ptr (bs ++ [0x18#8]) ∗ A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗
            (pendingOpenAt A ss g p ∗ F))
        (by
          rw [← hclose]
          exact entails_of_sep_focus (by sep_focus)) ?_
      refine hCallEV sp0 (BitVec.signExtend 64 p.signedPreKeyId) v cap ptr (entry + bv% (1028)) (bs ++ [0x18#8])
        (by simp; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
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
        have hcs_1 : EncRawUpperSaved s0 s1 :=
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
            (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
        refine SepWPp.weaken_pre ?_ (hnext s1 cap' ptr' hpc1 hrun1 hsp1 htr1
          hx19_1 hx20_1 hx21_1 hcs_1)
        rw [List.append_assoc, int32Field3_nonzero_eq hspk]
        exact entails_of_sep_focus (by sep_focus)
    · have hcap_eq : cap.toNat = bs.length := by omega
      have hcap_bv := cap_eq_ofNat_len hcap_eq
      rw [vecU8At_eq_header_sep_buf A v cap ptr bs]
      simp only [vecHeader, sepConj_assoc]
      apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      have hx1_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      refine hCallDR sp0 v cap ptr (entry + bv% (2584)) bs 1
        (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
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
        have hcs_1 : EncRawUpperSaved s0 s1 :=
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
            (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
        have hlt_new : bs.length < newCap.toNat := by omega
        rw [vecU8At_open_one A v newCap p1 bs hlt_new]
        simp only [sepExists_sepConj_left, sepConj_assoc]
        refine SepWPp.exists_elim fun old => ?_
        apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        have hclose := vecU8At_close_one A v newCap p1 bs 0x18#8 hlt_new
        refine SepWPp.weaken_pre (P' :=
            (vecU8At A v newCap p1 (bs ++ [0x18#8]) ∗ A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗
              (pendingOpenAt A ss g p ∗ F))
          (by
            rw [← hclose]
            exact entails_of_sep_focus (by sep_focus)) ?_
        refine hCallEV sp0 (BitVec.signExtend 64 p.signedPreKeyId) v newCap p1 (entry + bv% (1028)) (bs ++ [0x18#8])
          (by simp; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
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
          have hcs_2 : EncRawUpperSaved s0 s2 :=
            (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
              (EncRawUpperSaved.of_calleeSavedPreserved hcs2)
          refine SepWPp.weaken_pre ?_ (hnext s2 cap' ptr' hpc2 hrun2 hsp2 htr2
            hx19_2 hx20_2 hx21_2 hcs_2)
          rw [List.append_assoc, int32Field3_nonzero_eq hspk]
          exact entails_of_sep_focus (by sep_focus)

/-! ## Subfield 4 (`timestamp`, `1028..1080`) -/

theorem step_tag9_sub4 {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hEV : OkAt b C ctl abs encodeVarintName (encodeVarintSpec A))
    (hDR : OkAt b C ctl abs doReserveName (doReserveSpec A))
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (bs : List (BitVec 8))
    (hlen_lt : bs.length + 12 < 2 ^ 60)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName + 1028#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hx21 : s.readReg64 .x21 = p.timestamp)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (pendingOpenAt A ss g p ∗ vecU8At A v cap ptr bs ∗
      A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName + 1080#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        ((pendingOpenAt A ss g p ∗ vecU8At A v cap' ptr' (bs ++ uint64Field 4 p.timestamp) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q (PanicAllocPost s0) := by
  have hCallEV := @encraw_call_encodeVarint b C A ctl abs hEV
  have hCallDR := @encraw_call_doReserve_buf b C A ctl abs hDR
  encraw_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 1028 1080
  encraw_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 2592 2620
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName = entry
  examples_hide_fetches
  rw [hP]
  by_cases hts : p.timestamp = 0#64
  · simp only [sepConj_assoc]
    apply SepWPp.of_sepWP (mid := entry + bv% (1080))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine SepWPp.weaken_pre ?_ (hnext _ cap ptr
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
    simp only [hts, uint64Field4_zero_eq, List.append_nil]
    exact entails_of_sep_focus (by sep_focus)
  · have hbeq0 := bv64_beq_zero_false hts
    refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap) (ptr := ptr) (bs := bs)
      (h := fun hle _ _ => ?_)
    by_cases hlt : bs.length < cap.toNat
    · have hbeq_cap := cap_beq_len_false hlt
      rw [vecU8At_open_one A v cap ptr bs hlt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPp.exists_elim fun old => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      have hclose := vecU8At_close_one A v cap ptr bs 0x20#8 hlt
      refine SepWPp.weaken_pre (P' :=
          (vecU8At A v cap ptr (bs ++ [0x20#8]) ∗ A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗
            (pendingOpenAt A ss g p ∗ F))
        (by
          rw [← hclose]
          exact entails_of_sep_focus (by sep_focus)) ?_
      refine hCallEV sp0 p.timestamp v cap ptr (entry + bv% (1080)) (bs ++ [0x20#8])
        (by simp; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
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
        have hcs_1 : EncRawUpperSaved s0 s1 :=
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
            (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
        refine SepWPp.weaken_pre ?_ (hnext s1 cap' ptr' hpc1 hrun1 hsp1 htr1
          hx19_1 hx20_1 hcs_1)
        rw [List.append_assoc, uint64Field4_nonzero_eq hts]
        exact entails_of_sep_focus (by sep_focus)
    · have hcap_eq : cap.toNat = bs.length := by omega
      have hcap_bv := cap_eq_ofNat_len hcap_eq
      rw [vecU8At_eq_header_sep_buf A v cap ptr bs]
      simp only [vecHeader, sepConj_assoc]
      apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      have hx1_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      refine hCallDR sp0 v cap ptr (entry + bv% (2612)) bs 1
        (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
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
        have hcs_1 : EncRawUpperSaved s0 s1 :=
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
            (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
        have hlt_new : bs.length < newCap.toNat := by omega
        rw [vecU8At_open_one A v newCap p1 bs hlt_new]
        simp only [sepExists_sepConj_left, sepConj_assoc]
        refine SepWPp.exists_elim fun old => ?_
        apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        have hclose := vecU8At_close_one A v newCap p1 bs 0x20#8 hlt_new
        refine SepWPp.weaken_pre (P' :=
            (vecU8At A v newCap p1 (bs ++ [0x20#8]) ∗ A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗
              (pendingOpenAt A ss g p ∗ F))
          (by
            rw [← hclose]
            exact entails_of_sep_focus (by sep_focus)) ?_
        refine hCallEV sp0 p.timestamp v newCap p1 (entry + bv% (1080)) (bs ++ [0x20#8])
          (by simp; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
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
          have hcs_2 : EncRawUpperSaved s0 s2 :=
            (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
              (EncRawUpperSaved.of_calleeSavedPreserved hcs2)
          refine SepWPp.weaken_pre ?_ (hnext s2 cap' ptr' hpc2 hrun2 hsp2 htr2
            hx19_2 hx20_2 hcs_2)
          rw [List.append_assoc, uint64Field4_nonzero_eq hts]
          exact entails_of_sep_focus (by sep_focus)

/-! ## Combined tag-9 step (`536..1080`) -/

theorem step_encraw_tag9 {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hEV : OkAt b C ctl abs encodeVarintName (encodeVarintSpec A))
    (hDR : OkAt b C ctl abs doReserveName (doReserveSpec A))
    (ss v sp0 cap ptr : BitVec 64)
    (G_pending : Option TailVecGhost) (s_pending : Option PendingPreKey)
    (bs : List (BitVec 8))
    (hrel : PendingRel G_pending s_pending)
    (hbound : match G_pending with | none => True | some g => g.vec.bytes.length < 2 ^ 32)
    (hbs_lt : bs.length < 2 ^ 32)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName + 536#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (optTailVecAt A 48 (ss + 248#64) G_pending ∗ vecU8At A v cap ptr bs ∗
      A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName + 1080#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        ((optTailVecAt A 48 (ss + 248#64) G_pending ∗
          vecU8At A v cap' ptr' (bs ++ encPendingFieldMem G_pending s_pending) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q (PanicAllocPost s0) := by
  cases G_pending with
  | none =>
    cases s_pending with
    | some p => exact False.elim hrel
    | none =>
      encraw_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 536 548
      generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName = entry
      examples_hide_fetches
      rw [hP, optTailVecAt_pending_none_eq]
      simp only [sepConj_assoc]
      apply SepWPp.of_sepWP (mid := entry + bv% (1080))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      refine SepWPp.weaken_pre ?_ (hnext _ cap ptr
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      rw [optTailVecAt_pending_none_eq]
      simp only [encPendingFieldMem, List.append_nil]
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
      rw [hP]
      refine sepWPp_extract_pending_some (A := A) (ss := ss) (g := g)
        (h := fun hlen24 hle_g hcap_g _ => ?_)
      have hopen := optTailVecAt_pending_some_eq_open A ss g p hlen24 hle_g hrel
      rw [hopen]
      refine step_tag9_write_tag hDR ss v sp0 cap ptr g p bs hcap_g (by omega)
        hpc hrun hsp halign htr hx19 hx20 hcs (by sep_focus) ?_
      intro s1 cap1 ptr1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx24_1 hcs1
      refine step_tag9_len1 ss v sp0 g p hne_vec hlt_vec63
        hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx24_1 hcs1 (by sep_focus) ?_
      intro s2 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx24_2 hx8_2 hx23_2 hcs2
      refine step_tag9_len2 ss v sp0 g p hne_vec
        hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx24_2 hx8_2 hx23_2 hcs2 (by sep_focus) ?_
      intro s3 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx24_3 hx8_3 hx9_3 hx23_3 hx22_3 hcs3
      refine step_tag9_len3 ss v sp0 g p
        hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx24_3 hx8_3 hx9_3 hx23_3 hx22_3 hcs3 (by sep_focus) ?_
      intro s4 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hx24_4 hx8_4 hx9_4 hx10_4 hx23_4 hx22_4 hx21_4 hcs4
      refine step_tag9_len4 hEV ss v sp0 cap1 ptr1 g p bs
        (by omega)
        hpc4 hrun4 hsp4 halign htr4 hx19_4 hx20_4 hx24_4 hx8_4 hx9_4 hx10_4 hx23_4 hx22_4 hx21_4 hcs4
        (by sep_focus) ?_
      intro s5 cap5 ptr5 hpc5 hrun5 hsp5 htr5 hx19_5 hx20_5 hx23_5 hx22_5 hx21_5 hcs5
      refine step_tag9_sub1 hEV hDR ss v sp0 cap5 ptr5 g p
        ((bs ++ [0x4a#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length))
        (by simp only [List.length_append, List.length_singleton]; omega)
        hpc5 hrun5 hsp5 halign htr5 hx19_5 hx20_5 hx23_5 hx22_5 hx21_5 hcs5 (by sep_focus) ?_
      intro s6 cap6 ptr6 hpc6 hrun6 hsp6 htr6 hx19_6 hx20_6 hx23_6 hx22_6 hx21_6 hcs6
      refine step_tag9_sub2_a hEV hDR ss v sp0 cap6 ptr6 g p
        (((bs ++ [0x4a#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ++
          optUint32Field 1 p.preKeyId)
        hne_vec hlt_vec63
        (by simp only [List.length_append, List.length_singleton]; omega)
        hpc6 hrun6 hsp6 halign htr6 hx19_6 hx20_6 hx23_6 hx22_6 hx21_6 hcs6 (by sep_focus) ?_
      intro s7 cap7 ptr7 hpc7 hrun7 hsp7 htr7 hx19_7 hx20_7 hx24_7 hx23_7 hx22_7 hx21_7 hcs7
      refine step_tag9_sub2_b hDR ss v sp0 cap7 ptr7 g p
        ((((bs ++ [0x4a#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ++
          optUint32Field 1 p.preKeyId) ++
          ([0x12#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length)))
        hne_vec
        (by simp only [List.length_append, List.length_singleton]; omega)
        hpc7 hrun7 hsp7 halign htr7 hx19_7 hx20_7 hx24_7 hx23_7 hx22_7 hx21_7 hcs7 (by sep_focus) ?_
      intro s8 cap8 ptr8 hpc8 hrun8 hsp8 htr8 hx19_8 hx20_8 hx22_8 hx21_8 hcs8
      refine step_tag9_sub3 hEV hDR ss v sp0 cap8 ptr8 g p
        (((((bs ++ [0x4a#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ++
          optUint32Field 1 p.preKeyId) ++
          ([0x12#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length))) ++ g.vec.bytes)
        (by simp only [List.length_append, List.length_singleton]; omega)
        hpc8 hrun8 hsp8 halign htr8 hx19_8 hx20_8 hx22_8 hx21_8 hcs8 (by sep_focus) ?_
      intro s9 cap9 ptr9 hpc9 hrun9 hsp9 htr9 hx19_9 hx20_9 hx21_9 hcs9
      refine step_tag9_sub4 hEV hDR ss v sp0 cap9 ptr9 g p
        ((((((bs ++ [0x4a#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ++
          optUint32Field 1 p.preKeyId) ++
          ([0x12#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length))) ++ g.vec.bytes) ++
          int32Field 3 p.signedPreKeyId)
        (by simp only [List.length_append, List.length_singleton]; omega)
        hpc9 hrun9 hsp9 halign htr9 hx19_9 hx20_9 hx21_9 hcs9 (by sep_focus) ?_
      intro s10 cap10 ptr10 hpc10 hrun10 hsp10 htr10 hx19_10 hx20_10 hcs10
      refine SepWPp.weaken_pre ?_ (hnext s10 cap10 ptr10 hpc10 hrun10 hsp10 htr10 hx19_10 hx20_10 hcs10)
      rw [← hopen]
      have hbytes :
          ((((((bs ++ [0x4a#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ++
            optUint32Field 1 p.preKeyId) ++
            ([0x12#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length))) ++ g.vec.bytes) ++
            int32Field 3 p.signedPreKeyId) ++ uint64Field 4 p.timestamp =
          bs ++ encPendingFieldMem (some g) (some p) := by
        rw [← lenField9_eq g p, ← bytesField2_nonempty_eq hne_vec]
        simp only [List.append_assoc]
      rw [hbytes]
      exact entails_of_sep_focus (by sep_focus)

/-! ## Relocatable `[LibsignalPlacement]` proofs (block `14`) -/

section Placed

set_option allowUnsafeReducibility false

open CryptoVerification CryptoVerification.E2E.Record.Placed

variable [LibsignalPlacement]

theorem step_tag9_sub1_placed {A : RustAlloc}
    {H : String → Option (State → State)}
    (hEV : subroutine_ok (lsProg_10 H) (blkPl_10).base (withLsCodeLoaded lsmpl (encodeVarintSpec A)))
    (hDR : subroutine_ok (lsProg_13 H) (blkPl_13).base (withLsCodeLoaded lsmpl (doReserveSpec A)))
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (bs : List (BitVec 8))
    (hlen_lt : bs.length + 12 < 2 ^ 60)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + (if p.preKeyId.isSome then 824#64 else 872#64))
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
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
      A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (blkPl_14).base + 872#64 →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length →
      sm.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId →
      sm.readReg64 .x21 = p.timestamp →
      EncRawUpperSaved s0 sm →
      SepWPp (lsProg_14 H) ret sm
        ((pendingOpenAt A ss g p ∗ vecU8At A v cap' ptr' (bs ++ optUint32Field 1 p.preKeyId) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPp (lsProg_14 H) ret s P Q (PanicAllocPost s0) := by
  cases hpk : p.preKeyId with
  | none =>
    simp only [hpk, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc
    rw [hP]
    refine SepWPp.weaken_pre ?_ (hnext s cap ptr hpc hrun hcl hsp htr hx19 hx20 hx23 hx22 hx21 hcs)
    simp only [hpk, optUint32Field1_none_eq, List.append_nil]
    exact entails_of_sep_focus (by sep_focus)
  | some pkId =>
    simp only [hpk, Option.isSome_some, ↓reduceIte] at hpc
    have hCallEV := @encraw_call_encodeVarint_placed _ A H hEV
    have hCallDR := @encraw_call_doReserve_buf_placed _ A H hDR
    have hpk_val : optU32ValAt (ss + 276#64) g.tail (some pkId) = ((ss + 276#64) ↦₃₂ pkId) :=
      optU32ValAt_some _ _ _
    rw [hP]
    refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap) (ptr := ptr) (bs := bs)
      (h := fun hle _ _ => ?_)
    by_cases hlt : bs.length < cap.toNat
    · have hbeq_cap := cap_beq_len_false hlt
      rw [vecU8At_open_one A v cap ptr bs hlt]
      unfold pendingOpenAt
      rw [hpk, hpk_val]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPp.exists_elim fun old => ?_
      apply sepWPp_of_sepWP_lscl_er hcl (mid := lsmpl.base 10)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcl0
      have hclose := vecU8At_close_one A v cap ptr bs 0x08#8 hlt
      refine SepWPp.weaken_pre (P' :=
          (vecU8At A v cap ptr (bs ++ [0x08#8]) ∗ A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗
            (pendingOpenAt A ss g p ∗ F))
        (by
          rw [← hclose]
          unfold pendingOpenAt
          rw [hpk, hpk_val]
          exact entails_of_sep_focus (by sep_focus)) ?_
      refine hCallEV sp0 (BitVec.zeroExtend 64 pkId) v cap ptr ((blkPl_14).base + 872#64) (bs ++ [0x08#8])
        (by simp; omega) ?_ ?_ hcl0 ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
      · simp only [arm64_norm]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
      · simp only [arm64_norm, *]
      · simp only [arm64_norm]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm]
      · intro s1 cap' ptr' hpc1 hrun1 hcl1 hsp1 htr1 hcs1
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
        refine SepWPp.weaken_pre ?_ (hnext s1 cap' ptr' hpc1 hrun1 hcl1 hsp1 htr1
          hx19_1 hx20_1 hx23_1 hx22_1 hx21_1 hcs_1)
        rw [List.append_assoc, hpk, optUint32Field1_some_eq pkId]
        exact entails_of_sep_focus (by sep_focus)
    · have hcap_eq : cap.toNat = bs.length := by omega
      have hcap_bv := cap_eq_ofNat_len hcap_eq
      rw [vecU8At_eq_header_sep_buf A v cap ptr bs]
      unfold pendingOpenAt
      rw [hpk, hpk_val]
      simp only [vecHeader, sepConj_assoc]
      apply sepWPp_of_sepWP_lscl_er hcl (mid := lsmpl.base 13)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcl0
      have hx1_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      refine hCallDR sp0 v cap ptr ((blkPl_14).base + 2776#64) bs 1
        (by omega) (by omega) ?_ ?_ hcl0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
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
      · intro s1 newCap p1 hpc1 hrun1 hcl1 hsp1 htr1 hcs1 hnew_ge _
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
        refine SepWPp.exists_elim fun old => ?_
        apply sepWPp_of_sepWP_lscl_er hcl1 (mid := lsmpl.base 10)
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        intro hcl2
        have hclose := vecU8At_close_one A v newCap p1 bs 0x08#8 hlt_new
        refine SepWPp.weaken_pre (P' :=
            (vecU8At A v newCap p1 (bs ++ [0x08#8]) ∗ A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗
              (pendingOpenAt A ss g p ∗ F))
          (by
            rw [← hclose]
            unfold pendingOpenAt
            rw [hpk, hpk_val]
            exact entails_of_sep_focus (by sep_focus)) ?_
        refine hCallEV sp0 (BitVec.zeroExtend 64 pkId) v newCap p1 ((blkPl_14).base + 872#64) (bs ++ [0x08#8])
          (by simp; omega) ?_ ?_ hcl2 ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
        · simp only [arm64_norm]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm]
        · intro s2 cap' ptr' hpc2 hrun2 hcl2' hsp2 htr2 hcs2
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
          refine SepWPp.weaken_pre ?_ (hnext s2 cap' ptr' hpc2 hrun2 hcl2' hsp2 htr2
            hx19_2 hx20_2 hx23_2 hx22_2 hx21_2 hcs_2)
          rw [List.append_assoc, hpk, optUint32Field1_some_eq pkId]
          exact entails_of_sep_focus (by sep_focus)

theorem step_tag9_sub2_a_placed {A : RustAlloc}
    {H : String → Option (State → State)}
    (hEV : subroutine_ok (lsProg_10 H) (blkPl_10).base (withLsCodeLoaded lsmpl (encodeVarintSpec A)))
    (hDR : subroutine_ok (lsProg_13 H) (blkPl_13).base (withLsCodeLoaded lsmpl (doReserveSpec A)))
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (bs : List (BitVec 8))
    (hne_vec : g.vec.bytes ≠ []) (hlt_vec : g.vec.bytes.length < 2 ^ 63)
    (hlen_lt : bs.length + 12 < 2 ^ 60)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 872#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
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
      A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (blkPl_14).base + 928#64 →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x24 = g.vec.ptr →
      sm.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length →
      sm.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId →
      sm.readReg64 .x21 = p.timestamp →
      EncRawUpperSaved s0 sm →
      SepWPp (lsProg_14 H) ret sm
        ((pendingOpenAt A ss g p ∗
          vecU8At A v cap' ptr' (bs ++ ([0x12#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length))) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPp (lsProg_14 H) ret s P Q (PanicAllocPost s0) := by
  have hCallEV := @encraw_call_encodeVarint_placed _ A H hEV
  have hCallDR := @encraw_call_doReserve_buf_placed _ A H hDR
  have hbeq0 := ofNat64_len_beq_zero_false hne_vec hlt_vec
  rw [hP]
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap) (ptr := ptr) (bs := bs)
    (h := fun hle _ _ => ?_)
  by_cases hlt : bs.length < cap.toNat
  · have hbeq_cap := cap_beq_len_false hlt
    rw [vecU8At_open_one A v cap ptr bs hlt]
    unfold pendingOpenAt
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun old => ?_
    apply sepWPp_of_sepWP_lscl_er hcl (mid := lsmpl.base 10)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl0
    have hclose := vecU8At_close_one A v cap ptr bs 0x12#8 hlt
    refine SepWPp.weaken_pre (P' :=
        (vecU8At A v cap ptr (bs ++ [0x12#8]) ∗ A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗
          (pendingOpenAt A ss g p ∗ F))
      (by
        rw [← hclose]
        unfold pendingOpenAt
        exact entails_of_sep_focus (by sep_focus)) ?_
    refine hCallEV sp0 (BitVec.ofNat 64 g.vec.bytes.length) v cap ptr ((blkPl_14).base + 928#64) (bs ++ [0x12#8])
      (by simp; omega) ?_ ?_ hcl0 ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
    · simp only [arm64_norm]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm]
    · intro s1 cap' ptr' hpc1 hrun1 hcl1 hsp1 htr1 hcs1
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
      refine SepWPp.weaken_pre ?_ (hnext s1 cap' ptr' hpc1 hrun1 hcl1 hsp1 htr1
        hx19_1 hx20_1 hx24_1 hx23_1 hx22_1 hx21_1 hcs_1)
      rw [List.append_assoc]
      exact entails_of_sep_focus (by sep_focus)
  · have hcap_eq : cap.toNat = bs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    rw [vecU8At_eq_header_sep_buf A v cap ptr bs]
    unfold pendingOpenAt
    simp only [vecHeader, sepConj_assoc]
    apply sepWPp_of_sepWP_lscl_er hcl (mid := lsmpl.base 13)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl0
    have hx1_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine hCallDR sp0 v cap ptr ((blkPl_14).base + 2480#64) bs 1
      (by omega) (by omega) ?_ ?_ hcl0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
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
    · intro s1 newCap p1 hpc1 hrun1 hcl1 hsp1 htr1 hcs1 hnew_ge _
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
      refine SepWPp.exists_elim fun old => ?_
      apply sepWPp_of_sepWP_lscl_er hcl1 (mid := lsmpl.base 10)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcl2
      have hclose := vecU8At_close_one A v newCap p1 bs 0x12#8 hlt_new
      refine SepWPp.weaken_pre (P' :=
          (vecU8At A v newCap p1 (bs ++ [0x12#8]) ∗ A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗
            (pendingOpenAt A ss g p ∗ F))
        (by
          rw [← hclose]
          unfold pendingOpenAt
          exact entails_of_sep_focus (by sep_focus)) ?_
      refine hCallEV sp0 (BitVec.ofNat 64 g.vec.bytes.length) v newCap p1 ((blkPl_14).base + 928#64) (bs ++ [0x12#8])
        (by simp; omega) ?_ ?_ hcl2 ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
      · simp only [arm64_norm]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm]
      · intro s2 cap' ptr' hpc2 hrun2 hcl2' hsp2 htr2 hcs2
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
        refine SepWPp.weaken_pre ?_ (hnext s2 cap' ptr' hpc2 hrun2 hcl2' hsp2 htr2
          hx19_2 hx20_2 hx24_2 hx23_2 hx22_2 hx21_2 hcs_2)
        rw [List.append_assoc]
        exact entails_of_sep_focus (by sep_focus)

theorem step_tag9_sub2_b_placed {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDR : subroutine_ok (lsProg_13 H) (blkPl_13).base (withLsCodeLoaded lsmpl (doReserveSpec A)))
    (hmc : HookSat H lsMemcpySym framelessMemcpySpec)
    (ss v sp0 cap1 ptr1 : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (bs1 : List (BitVec 8))
    (hne_vec : g.vec.bytes ≠ [])
    (hfit1 : bs1.length + g.vec.bytes.length < 2 ^ 60)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 928#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
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
      A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (blkPl_14).base + 976#64 →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId →
      sm.readReg64 .x21 = p.timestamp →
      EncRawUpperSaved s0 sm →
      SepWPp (lsProg_14 H) ret sm
        ((pendingOpenAt A ss g p ∗ vecU8At A v cap' ptr' (bs1 ++ g.vec.bytes) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPp (lsProg_14 H) ret s P Q (PanicAllocPost s0) := by
  have hCallDR := @encraw_call_doReserve_buf_placed _ A H hDR
  have hCallMC := @encraw_call_memcpy_buf_placed _ A H hmc
  rw [hP]
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap1) (ptr := ptr1) (bs := bs1)
    (h := fun hle1 hcap1 hptr1 => ?_)
  rw [vecU8At_eq_header_sep_buf A v cap1 ptr1 bs1]
  unfold pendingOpenAt
  simp only [vecHeader, sepConj_assoc]
  have hx2_nat : (BitVec.ofNat 64 g.vec.bytes.length).toNat = g.vec.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  by_cases hroom : bs1.length + g.vec.bytes.length ≤ cap1.toNat
  · have hhi := cmp_hi_false_of_le hroom hcap1
    apply sepWPp_of_sepWP_lscl_er hcl (mid := lsρ lsMemcpySym)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl0
    refine hCallMC v cap1 ptr1 g.vec.ptr ((blkPl_14).base + 968#64) bs1 g.vec.bytes hroom hcap1 hptr1 hne_vec
      ?_ ?_ hcl0 ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
    · simp only [arm64_norm]
    · simp only [arm64_norm, *]
    · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · intro sm hpcm hrunm hclm hspm htrm hcsm
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
      have hspm' : sm.sp = sp0 - 80#64 := by
        rw [hspm]; simp only [arm64_norm, *]
      have hcsm' : EncRawUpperSaved s0 sm :=
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
          (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
      apply sepWPp_of_sepWP_lscl_er hclm (mid := (blkPl_14).base + 976#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcl_end
      rw [vecU8At_close_slice A v cap1 ptr1 bs1 g.vec.bytes hroom hcap1 hptr1 hne_vec]
      refine SepWPp.weaken_pre ?_ (hnext _ cap1 ptr1
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl_end
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      unfold pendingOpenAt
      exact entails_of_sep_focus (by sep_focus)
  · have hhi := cmp_hi_true_of_gt (add := g.vec.bytes.length) hle1 (by omega) hcap1 (by omega)
    apply sepWPp_of_sepWP_lscl_er hcl (mid := lsmpl.base 13)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl0
    have hx1_nat : (BitVec.ofNat 64 bs1.length).toNat = bs1.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hx2_nat : (BitVec.ofNat 64 g.vec.bytes.length).toNat = g.vec.bytes.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine hCallDR sp0 v cap1 ptr1 ((blkPl_14).base + 2512#64) bs1 g.vec.bytes.length
      (by omega) (by omega) ?_ ?_ hcl0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
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
    · intro s1 newCap p' hpc1 hrun1 hcl1 hsp1 htr1 hcs1 hnew_ge hnew_lt
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
      refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := newCap) (ptr := p') (bs := bs1)
        (h := fun _ _ hp'_ne => ?_)
      rw [vecU8At_eq_header_sep_buf A v newCap p' bs1]
      simp only [vecHeader, sepConj_assoc]
      apply sepWPp_of_sepWP_lscl_er hcl1 (mid := lsρ lsMemcpySym)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcl2
      refine hCallMC v newCap p' g.vec.ptr ((blkPl_14).base + 968#64) bs1 g.vec.bytes hnew_ge hnew_lt hp'_ne hne_vec
        ?_ ?_ hcl2 ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
      · simp only [arm64_norm]
      · simp only [arm64_norm, *]
      · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · intro sm hpcm hrunm hclm hspm htrm hcsm
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
        have hspm' : sm.sp = sp0 - 80#64 := by
          rw [hspm]; simp only [arm64_norm, *]
        have hcsm' : EncRawUpperSaved s0 sm :=
          (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
            (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
        apply sepWPp_of_sepWP_lscl_er hclm (mid := (blkPl_14).base + 976#64)
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        intro hcl_end
        rw [vecU8At_close_slice A v newCap p' bs1 g.vec.bytes hnew_ge hnew_lt hp'_ne hne_vec]
        refine SepWPp.weaken_pre ?_ (hnext _ newCap p'
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl_end
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
        unfold pendingOpenAt
        exact entails_of_sep_focus (by sep_focus)

theorem step_tag9_sub3_placed {A : RustAlloc}
    {H : String → Option (State → State)}
    (hEV : subroutine_ok (lsProg_10 H) (blkPl_10).base (withLsCodeLoaded lsmpl (encodeVarintSpec A)))
    (hDR : subroutine_ok (lsProg_13 H) (blkPl_13).base (withLsCodeLoaded lsmpl (doReserveSpec A)))
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (bs : List (BitVec 8))
    (hlen_lt : bs.length + 12 < 2 ^ 60)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 976#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hx22 : s.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId)
    (hx21 : s.readReg64 .x21 = p.timestamp)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (pendingOpenAt A ss g p ∗ vecU8At A v cap ptr bs ∗
      A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (blkPl_14).base + 1028#64 →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x21 = p.timestamp →
      EncRawUpperSaved s0 sm →
      SepWPp (lsProg_14 H) ret sm
        ((pendingOpenAt A ss g p ∗ vecU8At A v cap' ptr' (bs ++ int32Field 3 p.signedPreKeyId) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPp (lsProg_14 H) ret s P Q (PanicAllocPost s0) := by
  have hCallEV := @encraw_call_encodeVarint_placed _ A H hEV
  have hCallDR := @encraw_call_doReserve_buf_placed _ A H hDR
  rw [hP]
  by_cases hspk : p.signedPreKeyId = 0#32
  · simp only [sepConj_assoc]
    apply sepWPp_of_sepWP_lscl_er hcl (mid := (blkPl_14).base + 1028#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl_end
    refine SepWPp.weaken_pre ?_ (hnext _ cap ptr
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl_end
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
    simp only [hspk, int32Field3_zero_eq, List.append_nil]
    exact entails_of_sep_focus (by sep_focus)
  · have hbeq0 := zext64_beq_zero_false_3b hspk
    refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap) (ptr := ptr) (bs := bs)
      (h := fun hle _ _ => ?_)
    by_cases hlt : bs.length < cap.toNat
    · have hbeq_cap := cap_beq_len_false hlt
      rw [vecU8At_open_one A v cap ptr bs hlt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPp.exists_elim fun old => ?_
      apply sepWPp_of_sepWP_lscl_er hcl (mid := lsmpl.base 10)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcl0
      have hclose := vecU8At_close_one A v cap ptr bs 0x18#8 hlt
      refine SepWPp.weaken_pre (P' :=
          (vecU8At A v cap ptr (bs ++ [0x18#8]) ∗ A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗
            (pendingOpenAt A ss g p ∗ F))
        (by
          rw [← hclose]
          exact entails_of_sep_focus (by sep_focus)) ?_
      refine hCallEV sp0 (BitVec.signExtend 64 p.signedPreKeyId) v cap ptr ((blkPl_14).base + 1028#64) (bs ++ [0x18#8])
        (by simp; omega) ?_ ?_ hcl0 ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
      · simp only [arm64_norm]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm]
      · intro s1 cap' ptr' hpc1 hrun1 hcl1 hsp1 htr1 hcs1
        have hx19_1 : s1.readReg64 .x19 = v := by
          have := hcs1.1; simp only [arm64_norm, *] at this; exact this
        have hx20_1 : s1.readReg64 .x20 = ss := by
          have := hcs1.2.1; simp only [arm64_norm, *] at this; exact this
        have hx21_1 : s1.readReg64 .x21 = p.timestamp := by
          have := hcs1.2.2.1; simp only [arm64_norm, *] at this; exact this
        have hcs_1 : EncRawUpperSaved s0 s1 :=
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
            (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
        refine SepWPp.weaken_pre ?_ (hnext s1 cap' ptr' hpc1 hrun1 hcl1 hsp1 htr1
          hx19_1 hx20_1 hx21_1 hcs_1)
        rw [List.append_assoc, int32Field3_nonzero_eq hspk]
        exact entails_of_sep_focus (by sep_focus)
    · have hcap_eq : cap.toNat = bs.length := by omega
      have hcap_bv := cap_eq_ofNat_len hcap_eq
      rw [vecU8At_eq_header_sep_buf A v cap ptr bs]
      simp only [vecHeader, sepConj_assoc]
      apply sepWPp_of_sepWP_lscl_er hcl (mid := lsmpl.base 13)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcl0
      have hx1_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      refine hCallDR sp0 v cap ptr ((blkPl_14).base + 2584#64) bs 1
        (by omega) (by omega) ?_ ?_ hcl0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
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
      · intro s1 newCap p1 hpc1 hrun1 hcl1 hsp1 htr1 hcs1 hnew_ge _
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
        rw [vecU8At_open_one A v newCap p1 bs hlt_new]
        simp only [sepExists_sepConj_left, sepConj_assoc]
        refine SepWPp.exists_elim fun old => ?_
        apply sepWPp_of_sepWP_lscl_er hcl1 (mid := lsmpl.base 10)
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        intro hcl2
        have hclose := vecU8At_close_one A v newCap p1 bs 0x18#8 hlt_new
        refine SepWPp.weaken_pre (P' :=
            (vecU8At A v newCap p1 (bs ++ [0x18#8]) ∗ A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗
              (pendingOpenAt A ss g p ∗ F))
          (by
            rw [← hclose]
            exact entails_of_sep_focus (by sep_focus)) ?_
        refine hCallEV sp0 (BitVec.signExtend 64 p.signedPreKeyId) v newCap p1 ((blkPl_14).base + 1028#64) (bs ++ [0x18#8])
          (by simp; omega) ?_ ?_ hcl2 ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
        · simp only [arm64_norm]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm]
        · intro s2 cap' ptr' hpc2 hrun2 hcl2' hsp2 htr2 hcs2
          have hx19_2 : s2.readReg64 .x19 = v := by
            have := hcs2.1; simp only [arm64_norm, *] at this; exact this
          have hx20_2 : s2.readReg64 .x20 = ss := by
            have := hcs2.2.1; simp only [arm64_norm, *] at this; exact this
          have hx21_2 : s2.readReg64 .x21 = p.timestamp := by
            have := hcs2.2.2.1; simp only [arm64_norm, *] at this; exact this
          have hcs_2 : EncRawUpperSaved s0 s2 :=
            (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
              (EncRawUpperSaved.of_calleeSavedPreserved hcs2)
          refine SepWPp.weaken_pre ?_ (hnext s2 cap' ptr' hpc2 hrun2 hcl2' hsp2 htr2
            hx19_2 hx20_2 hx21_2 hcs_2)
          rw [List.append_assoc, int32Field3_nonzero_eq hspk]
          exact entails_of_sep_focus (by sep_focus)

theorem step_tag9_sub4_placed {A : RustAlloc}
    {H : String → Option (State → State)}
    (hEV : subroutine_ok (lsProg_10 H) (blkPl_10).base (withLsCodeLoaded lsmpl (encodeVarintSpec A)))
    (hDR : subroutine_ok (lsProg_13 H) (blkPl_13).base (withLsCodeLoaded lsmpl (doReserveSpec A)))
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (bs : List (BitVec 8))
    (hlen_lt : bs.length + 12 < 2 ^ 60)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 1028#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hx21 : s.readReg64 .x21 = p.timestamp)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (pendingOpenAt A ss g p ∗ vecU8At A v cap ptr bs ∗
      A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (blkPl_14).base + 1080#64 →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPp (lsProg_14 H) ret sm
        ((pendingOpenAt A ss g p ∗ vecU8At A v cap' ptr' (bs ++ uint64Field 4 p.timestamp) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPp (lsProg_14 H) ret s P Q (PanicAllocPost s0) := by
  have hCallEV := @encraw_call_encodeVarint_placed _ A H hEV
  have hCallDR := @encraw_call_doReserve_buf_placed _ A H hDR
  rw [hP]
  by_cases hts : p.timestamp = 0#64
  · simp only [sepConj_assoc]
    apply sepWPp_of_sepWP_lscl_er hcl (mid := (blkPl_14).base + 1080#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl_end
    refine SepWPp.weaken_pre ?_ (hnext _ cap ptr
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl_end
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
    simp only [hts, uint64Field4_zero_eq, List.append_nil]
    exact entails_of_sep_focus (by sep_focus)
  · have hbeq0 := bv64_beq_zero_false hts
    refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap) (ptr := ptr) (bs := bs)
      (h := fun hle _ _ => ?_)
    by_cases hlt : bs.length < cap.toNat
    · have hbeq_cap := cap_beq_len_false hlt
      rw [vecU8At_open_one A v cap ptr bs hlt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPp.exists_elim fun old => ?_
      apply sepWPp_of_sepWP_lscl_er hcl (mid := lsmpl.base 10)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcl0
      have hclose := vecU8At_close_one A v cap ptr bs 0x20#8 hlt
      refine SepWPp.weaken_pre (P' :=
          (vecU8At A v cap ptr (bs ++ [0x20#8]) ∗ A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗
            (pendingOpenAt A ss g p ∗ F))
        (by
          rw [← hclose]
          exact entails_of_sep_focus (by sep_focus)) ?_
      refine hCallEV sp0 p.timestamp v cap ptr ((blkPl_14).base + 1080#64) (bs ++ [0x20#8])
        (by simp; omega) ?_ ?_ hcl0 ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
      · simp only [arm64_norm]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm]
      · intro s1 cap' ptr' hpc1 hrun1 hcl1 hsp1 htr1 hcs1
        have hx19_1 : s1.readReg64 .x19 = v := by
          have := hcs1.1; simp only [arm64_norm, *] at this; exact this
        have hx20_1 : s1.readReg64 .x20 = ss := by
          have := hcs1.2.1; simp only [arm64_norm, *] at this; exact this
        have hcs_1 : EncRawUpperSaved s0 s1 :=
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
            (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
        refine SepWPp.weaken_pre ?_ (hnext s1 cap' ptr' hpc1 hrun1 hcl1 hsp1 htr1
          hx19_1 hx20_1 hcs_1)
        rw [List.append_assoc, uint64Field4_nonzero_eq hts]
        exact entails_of_sep_focus (by sep_focus)
    · have hcap_eq : cap.toNat = bs.length := by omega
      have hcap_bv := cap_eq_ofNat_len hcap_eq
      rw [vecU8At_eq_header_sep_buf A v cap ptr bs]
      simp only [vecHeader, sepConj_assoc]
      apply sepWPp_of_sepWP_lscl_er hcl (mid := lsmpl.base 13)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcl0
      have hx1_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      refine hCallDR sp0 v cap ptr ((blkPl_14).base + 2612#64) bs 1
        (by omega) (by omega) ?_ ?_ hcl0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
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
      · intro s1 newCap p1 hpc1 hrun1 hcl1 hsp1 htr1 hcs1 hnew_ge _
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
        rw [vecU8At_open_one A v newCap p1 bs hlt_new]
        simp only [sepExists_sepConj_left, sepConj_assoc]
        refine SepWPp.exists_elim fun old => ?_
        apply sepWPp_of_sepWP_lscl_er hcl1 (mid := lsmpl.base 10)
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        intro hcl2
        have hclose := vecU8At_close_one A v newCap p1 bs 0x20#8 hlt_new
        refine SepWPp.weaken_pre (P' :=
            (vecU8At A v newCap p1 (bs ++ [0x20#8]) ∗ A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗
              (pendingOpenAt A ss g p ∗ F))
          (by
            rw [← hclose]
            exact entails_of_sep_focus (by sep_focus)) ?_
        refine hCallEV sp0 p.timestamp v newCap p1 ((blkPl_14).base + 1080#64) (bs ++ [0x20#8])
          (by simp; omega) ?_ ?_ hcl2 ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
        · simp only [arm64_norm]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm]
        · intro s2 cap' ptr' hpc2 hrun2 hcl2' hsp2 htr2 hcs2
          have hx19_2 : s2.readReg64 .x19 = v := by
            have := hcs2.1; simp only [arm64_norm, *] at this; exact this
          have hx20_2 : s2.readReg64 .x20 = ss := by
            have := hcs2.2.1; simp only [arm64_norm, *] at this; exact this
          have hcs_2 : EncRawUpperSaved s0 s2 :=
            (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
              (EncRawUpperSaved.of_calleeSavedPreserved hcs2)
          refine SepWPp.weaken_pre ?_ (hnext s2 cap' ptr' hpc2 hrun2 hcl2' hsp2 htr2
            hx19_2 hx20_2 hcs_2)
          rw [List.append_assoc, uint64Field4_nonzero_eq hts]
          exact entails_of_sep_focus (by sep_focus)

theorem step_encraw_tag9_placed {A : RustAlloc}
    {H : String → Option (State → State)}
    (hEV : subroutine_ok (lsProg_10 H) (blkPl_10).base (withLsCodeLoaded lsmpl (encodeVarintSpec A)))
    (hDR : subroutine_ok (lsProg_13 H) (blkPl_13).base (withLsCodeLoaded lsmpl (doReserveSpec A)))
    (hmc : HookSat H lsMemcpySym framelessMemcpySpec)
    (ss v sp0 cap ptr : BitVec 64)
    (G_pending : Option TailVecGhost) (s_pending : Option PendingPreKey)
    (bs : List (BitVec 8))
    (hrel : PendingRel G_pending s_pending)
    (hbound : match G_pending with | none => True | some g => g.vec.bytes.length < 2 ^ 32)
    (hbs_lt : bs.length < 2 ^ 32)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 536#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (optTailVecAt A 48 (ss + 248#64) G_pending ∗ vecU8At A v cap ptr bs ∗
      A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (blkPl_14).base + 1080#64 →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPp (lsProg_14 H) ret sm
        ((optTailVecAt A 48 (ss + 248#64) G_pending ∗
          vecU8At A v cap' ptr' (bs ++ encPendingFieldMem G_pending s_pending) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPp (lsProg_14 H) ret s P Q (PanicAllocPost s0) := by
  cases G_pending with
  | none =>
    cases s_pending with
    | some p => exact False.elim hrel
    | none =>
      rw [hP, optTailVecAt_pending_none_eq]
      simp only [sepConj_assoc]
      apply sepWPp_of_sepWP_lscl_er hcl (mid := (blkPl_14).base + 1080#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcl_end
      refine SepWPp.weaken_pre ?_ (hnext _ cap ptr
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl_end
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      rw [optTailVecAt_pending_none_eq]
      simp only [encPendingFieldMem, List.append_nil]
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
      rw [hP]
      refine sepWPp_extract_pending_some (A := A) (ss := ss) (g := g)
        (h := fun hlen24 hle_g hcap_g _ => ?_)
      have hopen := optTailVecAt_pending_some_eq_open A ss g p hlen24 hle_g hrel
      rw [hopen]
      refine step_tag9_write_tag_placed hDR ss v sp0 cap ptr g p bs hcap_g (by omega)
        hpc hrun hcl hsp halign htr hx19 hx20 hcs (by sep_focus) ?_
      intro s1 cap1 ptr1 hpc1 hrun1 hcl1 hsp1 htr1 hx19_1 hx20_1 hx24_1 hcs1
      refine step_tag9_len1_placed ss v sp0 g p hne_vec hlt_vec63
        hpc1 hrun1 hcl1 hsp1 htr1 hx19_1 hx20_1 hx24_1 hcs1 (by sep_focus) ?_
      intro s2 hpc2 hrun2 hcl2 hsp2 htr2 hx19_2 hx20_2 hx24_2 hx8_2 hx23_2 hcs2
      refine step_tag9_len2_placed ss v sp0 g p hne_vec
        hpc2 hrun2 hcl2 hsp2 htr2 hx19_2 hx20_2 hx24_2 hx8_2 hx23_2 hcs2 (by sep_focus) ?_
      intro s3 hpc3 hrun3 hcl3 hsp3 htr3 hx19_3 hx20_3 hx24_3 hx8_3 hx9_3 hx23_3 hx22_3 hcs3
      refine step_tag9_len3_placed ss v sp0 g p
        hpc3 hrun3 hcl3 hsp3 htr3 hx19_3 hx20_3 hx24_3 hx8_3 hx9_3 hx23_3 hx22_3 hcs3 (by sep_focus) ?_
      intro s4 hpc4 hrun4 hcl4 hsp4 htr4 hx19_4 hx20_4 hx24_4 hx8_4 hx9_4 hx10_4 hx23_4 hx22_4 hx21_4 hcs4
      refine step_tag9_len4_placed hEV ss v sp0 cap1 ptr1 g p bs
        (by omega)
        hpc4 hrun4 hcl4 hsp4 halign htr4 hx19_4 hx20_4 hx24_4 hx8_4 hx9_4 hx10_4 hx23_4 hx22_4 hx21_4 hcs4
        (by sep_focus) ?_
      intro s5 cap5 ptr5 hpc5 hrun5 hcl5 hsp5 htr5 hx19_5 hx20_5 hx23_5 hx22_5 hx21_5 hcs5
      refine step_tag9_sub1_placed hEV hDR ss v sp0 cap5 ptr5 g p
        ((bs ++ [0x4a#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length))
        (by simp only [List.length_append, List.length_singleton]; omega)
        hpc5 hrun5 hcl5 hsp5 halign htr5 hx19_5 hx20_5 hx23_5 hx22_5 hx21_5 hcs5 (by sep_focus) ?_
      intro s6 cap6 ptr6 hpc6 hrun6 hcl6 hsp6 htr6 hx19_6 hx20_6 hx23_6 hx22_6 hx21_6 hcs6
      refine step_tag9_sub2_a_placed hEV hDR ss v sp0 cap6 ptr6 g p
        (((bs ++ [0x4a#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ++
          optUint32Field 1 p.preKeyId)
        hne_vec hlt_vec63
        (by simp only [List.length_append, List.length_singleton]; omega)
        hpc6 hrun6 hcl6 hsp6 halign htr6 hx19_6 hx20_6 hx23_6 hx22_6 hx21_6 hcs6 (by sep_focus) ?_
      intro s7 cap7 ptr7 hpc7 hrun7 hcl7 hsp7 htr7 hx19_7 hx20_7 hx24_7 hx23_7 hx22_7 hx21_7 hcs7
      refine step_tag9_sub2_b_placed hDR hmc ss v sp0 cap7 ptr7 g p
        ((((bs ++ [0x4a#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ++
          optUint32Field 1 p.preKeyId) ++
          ([0x12#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length)))
        hne_vec
        (by simp only [List.length_append, List.length_singleton]; omega)
        hpc7 hrun7 hcl7 hsp7 halign htr7 hx19_7 hx20_7 hx24_7 hx23_7 hx22_7 hx21_7 hcs7 (by sep_focus) ?_
      intro s8 cap8 ptr8 hpc8 hrun8 hcl8 hsp8 htr8 hx19_8 hx20_8 hx22_8 hx21_8 hcs8
      refine step_tag9_sub3_placed hEV hDR ss v sp0 cap8 ptr8 g p
        (((((bs ++ [0x4a#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ++
          optUint32Field 1 p.preKeyId) ++
          ([0x12#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length))) ++ g.vec.bytes)
        (by simp only [List.length_append, List.length_singleton]; omega)
        hpc8 hrun8 hcl8 hsp8 halign htr8 hx19_8 hx20_8 hx22_8 hx21_8 hcs8 (by sep_focus) ?_
      intro s9 cap9 ptr9 hpc9 hrun9 hcl9 hsp9 htr9 hx19_9 hx20_9 hx21_9 hcs9
      refine step_tag9_sub4_placed hEV hDR ss v sp0 cap9 ptr9 g p
        ((((((bs ++ [0x4a#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ++
          optUint32Field 1 p.preKeyId) ++
          ([0x12#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length))) ++ g.vec.bytes) ++
          int32Field 3 p.signedPreKeyId)
        (by simp only [List.length_append, List.length_singleton]; omega)
        hpc9 hrun9 hcl9 hsp9 halign htr9 hx19_9 hx20_9 hx21_9 hcs9 (by sep_focus) ?_
      intro s10 cap10 ptr10 hpc10 hrun10 hcl10 hsp10 htr10 hx19_10 hx20_10 hcs10
      refine SepWPp.weaken_pre ?_ (hnext s10 cap10 ptr10 hpc10 hrun10 hcl10 hsp10 htr10 hx19_10 hx20_10 hcs10)
      rw [← hopen]
      have hbytes :
          ((((((bs ++ [0x4a#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ++
            optUint32Field 1 p.preKeyId) ++
            ([0x12#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length))) ++ g.vec.bytes) ++
            int32Field 3 p.signedPreKeyId) ++ uint64Field 4 p.timestamp =
          bs ++ encPendingFieldMem (some g) (some p) := by
        rw [← lenField9_eq g p, ← bytesField2_nonempty_eq hne_vec]
        simp only [List.append_assoc]
      rw [hbytes]
      exact entails_of_sep_focus (by sep_focus)

end Placed

end CryptoVerification.E2E.Record.Serialization.EncodeRawAux
