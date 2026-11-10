/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.EncodeRawAux.PendingPreKeyHeader
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.EncodeRawAux.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `SessionStructure::encode_raw` Segment 3b (Part 1): Tag 9 `pending_pre_key` Subfields 1 and 2a
-/

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
open CryptoVerification.E2E.Record.Serialization

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet hiding stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.LibsignalTripleRatchet.Prost hiding vecU8Buf vecU8At_eq_header_sep_buf
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

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local irreducible] vecRest vecU8Buf vecSrcRest vecCopyDone
attribute [local irreducible] optU32ValAt pendingTailRest
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  truncate32_signExtend64_er truncate32_zeroExtend64

@[local arm64_norm]
theorem bv_add_neg80_3b (x : BitVec 64) : x + bv% (2 ^ 64 - 80) = x - 80#64 :=
  (BitVec.sub_eq_add_neg x 80#64).symm

set_option maxHeartbeats 400000

/-! ## 1. Step 3b.1 (`824/872 → 872`, cold `2752..2784`): subfield 1 (`pre_key_id`) -/

theorem step_tag9_sub1 {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hEV : EncodeVarintOkExtX img A ext)
    (hDR : OkAtX img ext doReserveName (doReserveSpecX A))
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (bs : List (BitVec 8))
    (hlen_lt : bs.length + 12 < 2 ^ 60)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName +
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
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + 872#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length →
      sm.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId →
      sm.readReg64 .x21 = p.timestamp →
      EncRawUpperSaved s0 sm →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        ((pendingOpenAt A ss g p ∗ vecU8At A v cap' ptr' (bs ++ optUint32Field 1 p.preKeyId) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q (PanicAllocPost s0) := by
  cases hpk : p.preKeyId with
  | none =>
    simp only [hpk, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc
    rw [hP]
    refine SepWPpX.weaken_pre ?_ (hnext s cap ptr hpc hrun hsp htr hx19 hx20 hx23 hx22 hx21 hcs)
    simp only [hpk, optUint32Field1_none_eq, List.append_nil]
    exact entails_of_sep_focus (by sep_focus)
  | some pkId =>
    simp only [hpk, Option.isSome_some, ↓reduceIte] at hpc
    have hCallEV := @encraw_call_encodeVarint img A ext hEV
    have hCallDR := @encraw_call_doReserve_buf img A ext hDR
    encraw_fetches_range img.base (Rust.withPanics ext) 824 872
    encraw_fetches_range img.base (Rust.withPanics ext) 2752 2784
    generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName = entry
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
      refine SepWPpX.exists_elim fun old => ?_
      apply SepWPpX.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      have hclose := vecU8At_close_one A v cap ptr bs 0x08#8 hlt
      refine SepWPpX.weaken_pre (P' :=
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
        refine SepWPpX.weaken_pre ?_ (hnext s1 cap' ptr' hpc1 hrun1 hsp1 htr1
          hx19_1 hx20_1 hx23_1 hx22_1 hx21_1 hcs_1)
        rw [List.append_assoc, hpk, optUint32Field1_some_eq pkId]
        exact entails_of_sep_focus (by sep_focus)
    · have hcap_eq : cap.toNat = bs.length := by omega
      have hcap_bv := cap_eq_ofNat_len hcap_eq
      rw [vecU8At_eq_header_sep_buf A v cap ptr bs]
      unfold pendingOpenAt
      rw [hpk, hpk_val]
      simp only [vecHeader, sepConj_assoc]
      apply SepWPpX.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
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
        refine SepWPpX.exists_elim fun old => ?_
        apply SepWPpX.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        have hclose := vecU8At_close_one A v newCap p1 bs 0x08#8 hlt_new
        refine SepWPpX.weaken_pre (P' :=
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
          refine SepWPpX.weaken_pre ?_ (hnext s2 cap' ptr' hpc2 hrun2 hsp2 htr2
            hx19_2 hx20_2 hx23_2 hx22_2 hx21_2 hcs_2)
          rw [List.append_assoc, hpk, optUint32Field1_some_eq pkId]
          exact entails_of_sep_focus (by sep_focus)

/-! ## 2. Step 3b.2a (`872 → 928`, cold `2460..2488`): subfield 2 (`base_key`) header & varint -/

theorem step_tag9_sub2_a {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hEV : EncodeVarintOkExtX img A ext)
    (hDR : OkAtX img ext doReserveName (doReserveSpecX A))
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (bs : List (BitVec 8))
    (hne_vec : g.vec.bytes ≠ []) (hlt_vec : g.vec.bytes.length < 2 ^ 63)
    (hlen_lt : bs.length + 12 < 2 ^ 60)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + 872#64)
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
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + 928#64 →
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
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        ((pendingOpenAt A ss g p ∗
          vecU8At A v cap' ptr' (bs ++ ([0x12#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length))) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q (PanicAllocPost s0) := by
  have hCallEV := @encraw_call_encodeVarint img A ext hEV
  have hCallDR := @encraw_call_doReserve_buf img A ext hDR
  encraw_fetches_range img.base (Rust.withPanics ext) 872 928
  encraw_fetches_range img.base (Rust.withPanics ext) 2460 2488
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName = entry
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
    refine SepWPpX.exists_elim fun old => ?_
    apply SepWPpX.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    have hclose := vecU8At_close_one A v cap ptr bs 0x12#8 hlt
    refine SepWPpX.weaken_pre (P' :=
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
      refine SepWPpX.weaken_pre ?_ (hnext s1 cap' ptr' hpc1 hrun1 hsp1 htr1
        hx19_1 hx20_1 hx24_1 hx23_1 hx22_1 hx21_1 hcs_1)
      rw [List.append_assoc]
      exact entails_of_sep_focus (by sep_focus)
  · have hcap_eq : cap.toNat = bs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    rw [vecU8At_eq_header_sep_buf A v cap ptr bs]
    unfold pendingOpenAt
    simp only [vecHeader, sepConj_assoc]
    apply SepWPpX.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
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
      refine SepWPpX.exists_elim fun old => ?_
      apply SepWPpX.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      have hclose := vecU8At_close_one A v newCap p1 bs 0x12#8 hlt_new
      refine SepWPpX.weaken_pre (P' :=
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
        refine SepWPpX.weaken_pre ?_ (hnext s2 cap' ptr' hpc2 hrun2 hsp2 htr2
          hx19_2 hx20_2 hx24_2 hx23_2 hx22_2 hx21_2 hcs_2)
        rw [List.append_assoc]
        exact entails_of_sep_focus (by sep_focus)

/-! ## 3. Step 3b.2b (`928 → 976`, cold `2488..2564`): subfield 2 (`base_key`) reserve & memcpy -/

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
