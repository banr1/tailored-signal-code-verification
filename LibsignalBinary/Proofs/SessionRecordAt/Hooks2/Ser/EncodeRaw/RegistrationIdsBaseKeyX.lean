/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.BaseX
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.RemoteIdentityRootKeyCounter
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PrologueVersionLocalIdentityX
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `SessionStructure::encode_raw` Tags 10, 11, and 13 (`+0x438` → `+0x50c`)

Verifies protobuf tags 10 (`remote_registration_id`), 11 (`local_registration_id`), and 13
(`alice_base_key`, offsets `1080..1292`, cold `2152..2324`) of `SessionStructure::encode_raw`
(`0x4d38`) on `SP2Ext`.
-/

namespace CryptoVerification.E2E.Record.Serialization

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.E2E.Record.Serialization.EncodeRawAux
open Proofs.libsignal.Hooks2

theorem L1_EncodeRawRegistrationIdsBaseKeyX : True := trivial

set_option allowUnsafeReducibility true
attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr stackAt vecRest RustHeap.vecU8Buf vecSrcRest vecCopyDone Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local arm64_norm]
theorem bv_add_neg80_4a (x : BitVec 64) : x + bv% (2 ^ 64 - 80) = x - 80#64 :=
  (BitVec.sub_eq_add_neg x 80#64).symm

set_option maxHeartbeats 400000

/-! ## Tag 10 (`remote_registration_id`, `1080..1132`, cold `2152..2184`) -/

theorem step_encraw_tag10_x {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hDR : DoReserveOkX img A ext)
    (hEV : EncodeVarintOkX img A ext)
    (ss v sp0 cap ptr : BitVec 64) (remReg : BitVec 32) (bs : List (BitVec 8))
    (hlen_lt : bs.length + 11 < 2 ^ 62)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr encodeRawName + 1080#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (((ss + 0x150#64) ↦₃₂ remReg) ∗ vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_frame)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (SP2Ext img.base ext).fnAddr encodeRawName + 1132#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPpIn img (SP2Ext img.base ext) ret sm
        ((((ss + 0x150#64) ↦₃₂ remReg) ∗ vecU8At A v cap' ptr' (bs ++ uint32Field 10 remReg) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpIn img (SP2Ext img.base ext) ret s P Q (PanicAllocPost s0) := by
  have hCallDR := @encraw_call_doReserve_buf_x img A ext hDR
  have hCallEV := @encraw_call_encodeVarint_x img A ext hEV
  encraw_fetches_range img.base (Rust.withPanics ext) 1080 1132
  encraw_fetches_range img.base (Rust.withPanics ext) 2152 2184
  generalize_entry (SP2Ext img.base ext).fnAddr encodeRawName = entry
  examples_hide_fetches
  rw [hP]
  by_cases hver : remReg = 0#32
  · subst hver
    apply SepWPpIn.of_sepWP (mid := entry + bv% (1132))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    simpa only [uint32Field_zero, List.append_nil] using
      hnext _ cap ptr
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
  · have hver_beq : (remReg == 0#32) = false := bv32_beq_zero_false hver
    have hfield_eq : bs ++ uint32Field 10 remReg =
        (bs ++ [0x50#8]) ++ encodeVarint (BitVec.zeroExtend 64 remReg) := by
      rw [uint32Field_ne_zero (k := 0x50#8) hver, List.append_assoc]
    refine sepWPpIn_extract_vecU8At_bounds (A := A) (v := v) (cap := cap) (ptr := ptr) (bs := bs)
      (h := fun hle _ _ => ?_)
    by_cases hlt : bs.length < cap.toNat
    · have hbeq_cap := cap_beq_len_false hlt
      rw [vecU8At_open_one A v cap ptr bs hlt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPpIn.exists_elim fun old => ?_
      apply SepWPpIn.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      rw [vecU8At_close_one A v cap ptr bs 0x50#8 hlt]
      refine hCallEV sp0 (BitVec.zeroExtend 64 remReg) v cap ptr (entry + bv% (1132))
        (bs ++ [0x50#8]) (by simp; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_frame) ?_
      · simp only [arm64_norm]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · intro sm cap' ptr' hpcm hrunm hspm htrm hcsm
        have hx19m : sm.readReg64 .x19 = v := by
          have := hcsm.1; simp only [arm64_norm, *] at this; exact this
        have hx20m : sm.readReg64 .x20 = ss := by
          have := hcsm.2.1; simp only [arm64_norm, *] at this; exact this
        have hcsm' : EncRawUpperSaved s0 sm :=
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
            (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
        rw [← hfield_eq]
        refine SepWPpIn.weaken_pre ?_ (hnext sm cap' ptr' hpcm hrunm hspm htrm hx19m hx20m hcsm')
        exact (by sep_frame)
    · have hcap_eq : cap.toNat = bs.length := by omega
      have hcap_bv := cap_eq_ofNat_len hcap_eq
      rw [Prost.vecU8At_eq_header_sep_buf A v cap ptr bs]
      simp only [vecHeader, sepConj_assoc]
      apply SepWPpIn.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      have hx1_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      refine hCallDR sp0 v cap ptr (entry + bv% (2176)) bs 1 (by omega) (by omega)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_frame) ?_
      · simp only [arm64_norm]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
      · simp only [arm64_norm, *]
      · simp only [arm64_norm]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm]; exact hx1_nat
      · simp only [arm64_norm]
      · simp only [arm64_norm]
      · simp only [arm64_norm]
      · intro sm newCap p' hpcm hrunm hspm htrm hcsm hnew_ge _
        have hx19m : sm.readReg64 .x19 = v := by
          have := hcsm.1; simp only [arm64_norm, *] at this; exact this
        have hx20m : sm.readReg64 .x20 = ss := by
          have := hcsm.2.1; simp only [arm64_norm, *] at this; exact this
        have hx21m : sm.readReg64 .x21 = BitVec.zeroExtend 64 remReg := by
          have := hcsm.2.2.1; simp only [arm64_norm, *] at this; exact this
        have hcsm' : EncRawUpperSaved s0 sm :=
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
            (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
        have hlt_new : bs.length < newCap.toNat := by omega
        rw [vecU8At_open_one A v newCap p' bs hlt_new]
        simp only [sepExists_sepConj_left, sepConj_assoc]
        refine SepWPpIn.exists_elim fun old => ?_
        apply SepWPpIn.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        rw [vecU8At_close_one A v newCap p' bs 0x50#8 hlt_new]
        refine hCallEV sp0 (BitVec.zeroExtend 64 remReg) v newCap p' (entry + bv% (1132))
          (bs ++ [0x50#8]) (by simp; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_frame) ?_
        · simp only [arm64_norm]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · intro s1 cap1 ptr1 hpc1 hrun1 hsp1 htr1 hcs1
          have hx19_1 : s1.readReg64 .x19 = v := by
            have := hcs1.1; simp only [arm64_norm, *] at this; exact this
          have hx20_1 : s1.readReg64 .x20 = ss := by
            have := hcs1.2.1; simp only [arm64_norm, *] at this; exact this
          have hcs_1 : EncRawUpperSaved s0 s1 :=
            (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
              (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
          rw [← hfield_eq]
          refine SepWPpIn.weaken_pre ?_ (hnext s1 cap1 ptr1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hcs_1)
          exact (by sep_frame)

/-! ## Tag 11 (`local_registration_id`, `1132..1184`, cold `2188..2220`) -/

theorem step_encraw_tag11_x {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hDR : DoReserveOkX img A ext)
    (hEV : EncodeVarintOkX img A ext)
    (ss v sp0 cap ptr : BitVec 64) (locReg : BitVec 32) (bs : List (BitVec 8))
    (hlen_lt : bs.length + 11 < 2 ^ 62)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr encodeRawName + 1132#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (((ss + 0x154#64) ↦₃₂ locReg) ∗ vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_frame)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (SP2Ext img.base ext).fnAddr encodeRawName + 1184#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPpIn img (SP2Ext img.base ext) ret sm
        ((((ss + 0x154#64) ↦₃₂ locReg) ∗ vecU8At A v cap' ptr' (bs ++ uint32Field 11 locReg) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpIn img (SP2Ext img.base ext) ret s P Q (PanicAllocPost s0) := by
  have hCallDR := @encraw_call_doReserve_buf_x img A ext hDR
  have hCallEV := @encraw_call_encodeVarint_x img A ext hEV
  encraw_fetches_range img.base (Rust.withPanics ext) 1132 1184
  encraw_fetches_range img.base (Rust.withPanics ext) 2188 2220
  generalize_entry (SP2Ext img.base ext).fnAddr encodeRawName = entry
  examples_hide_fetches
  rw [hP]
  by_cases hver : locReg = 0#32
  · subst hver
    apply SepWPpIn.of_sepWP (mid := entry + bv% (1184))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    simpa only [uint32Field_zero, List.append_nil] using
      hnext _ cap ptr
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
  · have hver_beq : (locReg == 0#32) = false := bv32_beq_zero_false hver
    have hfield_eq : bs ++ uint32Field 11 locReg =
        (bs ++ [0x58#8]) ++ encodeVarint (BitVec.zeroExtend 64 locReg) := by
      rw [uint32Field_ne_zero (k := 0x58#8) hver, List.append_assoc]
    refine sepWPpIn_extract_vecU8At_bounds (A := A) (v := v) (cap := cap) (ptr := ptr) (bs := bs)
      (h := fun hle _ _ => ?_)
    by_cases hlt : bs.length < cap.toNat
    · have hbeq_cap := cap_beq_len_false hlt
      rw [vecU8At_open_one A v cap ptr bs hlt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPpIn.exists_elim fun old => ?_
      apply SepWPpIn.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      rw [vecU8At_close_one A v cap ptr bs 0x58#8 hlt]
      refine hCallEV sp0 (BitVec.zeroExtend 64 locReg) v cap ptr (entry + bv% (1184))
        (bs ++ [0x58#8]) (by simp; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_frame) ?_
      · simp only [arm64_norm]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · intro sm cap' ptr' hpcm hrunm hspm htrm hcsm
        have hx19m : sm.readReg64 .x19 = v := by
          have := hcsm.1; simp only [arm64_norm, *] at this; exact this
        have hx20m : sm.readReg64 .x20 = ss := by
          have := hcsm.2.1; simp only [arm64_norm, *] at this; exact this
        have hcsm' : EncRawUpperSaved s0 sm :=
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
            (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
        rw [← hfield_eq]
        refine SepWPpIn.weaken_pre ?_ (hnext sm cap' ptr' hpcm hrunm hspm htrm hx19m hx20m hcsm')
        exact (by sep_frame)
    · have hcap_eq : cap.toNat = bs.length := by omega
      have hcap_bv := cap_eq_ofNat_len hcap_eq
      rw [Prost.vecU8At_eq_header_sep_buf A v cap ptr bs]
      simp only [vecHeader, sepConj_assoc]
      apply SepWPpIn.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      have hx1_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      refine hCallDR sp0 v cap ptr (entry + bv% (2212)) bs 1 (by omega) (by omega)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_frame) ?_
      · simp only [arm64_norm]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
      · simp only [arm64_norm, *]
      · simp only [arm64_norm]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm]; exact hx1_nat
      · simp only [arm64_norm]
      · simp only [arm64_norm]
      · simp only [arm64_norm]
      · intro sm newCap p' hpcm hrunm hspm htrm hcsm hnew_ge _
        have hx19m : sm.readReg64 .x19 = v := by
          have := hcsm.1; simp only [arm64_norm, *] at this; exact this
        have hx20m : sm.readReg64 .x20 = ss := by
          have := hcsm.2.1; simp only [arm64_norm, *] at this; exact this
        have hx21m : sm.readReg64 .x21 = BitVec.zeroExtend 64 locReg := by
          have := hcsm.2.2.1; simp only [arm64_norm, *] at this; exact this
        have hcsm' : EncRawUpperSaved s0 sm :=
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
            (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
        have hlt_new : bs.length < newCap.toNat := by omega
        rw [vecU8At_open_one A v newCap p' bs hlt_new]
        simp only [sepExists_sepConj_left, sepConj_assoc]
        refine SepWPpIn.exists_elim fun old => ?_
        apply SepWPpIn.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        rw [vecU8At_close_one A v newCap p' bs 0x58#8 hlt_new]
        refine hCallEV sp0 (BitVec.zeroExtend 64 locReg) v newCap p' (entry + bv% (1184))
          (bs ++ [0x58#8]) (by simp; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_frame) ?_
        · simp only [arm64_norm]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · intro s1 cap1 ptr1 hpc1 hrun1 hsp1 htr1 hcs1
          have hx19_1 : s1.readReg64 .x19 = v := by
            have := hcs1.1; simp only [arm64_norm, *] at this; exact this
          have hx20_1 : s1.readReg64 .x20 = ss := by
            have := hcs1.2.1; simp only [arm64_norm, *] at this; exact this
          have hcs_1 : EncRawUpperSaved s0 s1 :=
            (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
              (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
          rw [← hfield_eq]
          refine SepWPpIn.weaken_pre ?_ (hnext s1 cap1 ptr1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hcs_1)
          exact (by sep_frame)

/-! ## Tag 13 (`alice_base_key`) reserve and `memcpy` (`1184..1292`, cold `2224..2324`) -/

theorem step_encraw_tag13_b_x {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hDR : DoReserveOkX img A ext)
    (hC : SerContractsX img A ext)
    (ss v sp0 fCap fPtr cap1 ptr1 : BitVec 64) (bs1 fBs : List (BitVec 8))
    (hf_nil : fBs ≠ []) (hf_le : fBs.length ≤ fCap.toNat) (hf_cap : fCap.toNat < 2 ^ 63)
    (hlen_lt : bs1.length + fBs.length < 2 ^ 62)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr encodeRawName + 1244#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 fBs.length)
    (hx22 : s.readReg64 .x22 = fPtr)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (vecU8At A (ss + 96#64) fCap fPtr fBs ∗ vecU8At A v cap1 ptr1 bs1 ∗ A.pool ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_frame)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (SP2Ext img.base ext).fnAddr encodeRawName + 1292#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPpIn img (SP2Ext img.base ext) ret sm
        ((vecU8At A (ss + 96#64) fCap fPtr fBs ∗ vecU8At A v cap' ptr' (bs1 ++ fBs) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpIn img (SP2Ext img.base ext) ret s P Q (PanicAllocPost s0) := by
  have hCallDR := @encraw_call_doReserve_buf_x img A ext hDR
  have hCallMC := @encraw_call_memcpy_buf_x img A ext hC
  encraw_fetches_range img.base (Rust.withPanics ext) 1244 1292
  encraw_fetches_range img.base (Rust.withPanics ext) 2252 2324
  generalize_entry (SP2Ext img.base ext).fnAddr encodeRawName = entry
  examples_hide_fetches
  rw [hP]
  refine sepWPpIn_extract_vecU8At_bounds (A := A) (v := v) (cap := cap1) (ptr := ptr1) (bs := bs1)
    (h := fun hle1 hcap1 hptr1 => ?_)
  have hf_nat : (BitVec.ofNat 64 fBs.length).toNat = fBs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hbs1_nat : (BitVec.ofNat 64 bs1.length).toNat = bs1.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [vecU8At_open_src A (ss + 96#64) fCap fPtr fBs hf_nil hf_le,
      Prost.vecU8At_eq_header_sep_buf A v cap1 ptr1 bs1]
  simp only [vecHeader, sepConj_assoc]
  by_cases hfit : bs1.length + fBs.length ≤ cap1.toNat
  · have hhi := cmp_hi_false_of_le hfit hcap1
    apply SepWPpIn.of_sepWP (mid := entry + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine hCallMC sp0 v cap1 ptr1 fPtr (entry + bv% (1284)) bs1 fBs hfit hcap1 hptr1 hf_nil
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
      have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 fBs.length := by
        have := hcsm.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx23m : sm.readReg64 .x23 = BitVec.ofNat 64 bs1.length := by
        have := hcsm.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hspm' : sm.sp = sp0 - 80#64 := hspm
      have hcsm' : EncRawUpperSaved s0 sm :=
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
          (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
      apply SepWPpIn.of_sepWP (mid := entry + bv% (1292))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      rw [vecU8At_close_slice A v cap1 ptr1 bs1 fBs hfit hcap1 hptr1 hf_nil]
      refine SepWPpIn.weaken_pre ?_ (hnext _ cap1 ptr1
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      rw [vecU8At_open_src A (ss + 96#64) fCap fPtr fBs hf_nil hf_le]
      exact (by sep_frame)
  · have hhi := cmp_hi_true_of_gt (add := fBs.length) hle1 (by omega) hcap1 (by omega)
    apply SepWPpIn.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine hCallDR sp0 v cap1 ptr1 (entry + bv% (2276)) bs1 fBs.length
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
    · intro sm newCap p' hpcm hrunm hspm htrm hcsm hnew_ge hnew_lt
      have hx19m : sm.readReg64 .x19 = v := by
        have := hcsm.1; simp only [arm64_norm, *] at this; exact this
      have hx20m : sm.readReg64 .x20 = ss := by
        have := hcsm.2.1; simp only [arm64_norm, *] at this; exact this
      have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 fBs.length := by
        have := hcsm.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx22m : sm.readReg64 .x22 = fPtr := by
        have := hcsm.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx23m : sm.readReg64 .x23 = BitVec.ofNat 64 bs1.length := by
        have := hcsm.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hcs_1 : EncRawUpperSaved s0 sm :=
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
          (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
      have hls := cmp_ls_true_of_le hnew_ge hnew_lt
      refine sepWPpIn_extract_vecU8At_bounds (A := A) (v := v) (cap := newCap) (ptr := p') (bs := bs1)
        (h := fun _ _ hp'_ne => ?_)
      rw [Prost.vecU8At_eq_header_sep_buf A v newCap p' bs1]
      simp only [vecHeader, sepConj_assoc]
      apply SepWPpIn.of_sepWP (mid := entry + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>"))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      refine hCallMC sp0 v newCap p' fPtr (entry + bv% (1284)) bs1 fBs hnew_ge hnew_lt hp'_ne hf_nil
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
      · intro s1 hpc1 hrun1 hsp1 htr1 hcs1
        have hx19_1 : s1.readReg64 .x19 = v := by
          have := hcs1.1; simp only [arm64_norm, *] at this; exact this
        have hx20_1 : s1.readReg64 .x20 = ss := by
          have := hcs1.2.1; simp only [arm64_norm, *] at this; exact this
        have hx21_1 : s1.readReg64 .x21 = BitVec.ofNat 64 fBs.length := by
          have := hcs1.2.2.1; simp only [arm64_norm, *] at this; exact this
        have hx23_1 : s1.readReg64 .x23 = BitVec.ofNat 64 bs1.length := by
          have := hcs1.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
        have hsp1' : s1.sp = sp0 - 80#64 := hsp1
        have hcs_2 : EncRawUpperSaved s0 s1 :=
          (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
            (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
        apply SepWPpIn.of_sepWP (mid := entry + bv% (1292))
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        rw [vecU8At_close_slice A v newCap p' bs1 fBs hnew_ge hnew_lt hp'_ne hf_nil]
        refine SepWPpIn.weaken_pre ?_ (hnext _ newCap p'
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs_2.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
        rw [vecU8At_open_src A (ss + 96#64) fCap fPtr fBs hf_nil hf_le]
        exact (by sep_frame)

/-! ## Combined Tag 13 (`alice_base_key`, `1184..1292`) -/

theorem step_encraw_tag13_x {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hDR : DoReserveOkX img A ext)
    (hEV : EncodeVarintOkX img A ext)
    (hC : SerContractsX img A ext)
    (ss v sp0 fCap fPtr cap ptr : BitVec 64) (bs fBs : List (BitVec 8))
    (hlen_lt : bs.length + 11 + fBs.length < 2 ^ 62)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr encodeRawName + 1184#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (vecU8At A (ss + 96#64) fCap fPtr fBs ∗ vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_frame)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (SP2Ext img.base ext).fnAddr encodeRawName + 1292#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPpIn img (SP2Ext img.base ext) ret sm
        ((vecU8At A (ss + 96#64) fCap fPtr fBs ∗ vecU8At A v cap' ptr' (bs ++ bytesField 13 fBs) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpIn img (SP2Ext img.base ext) ret s P Q (PanicAllocPost s0) := by
  have hCallDR := @encraw_call_doReserve_buf_x img A ext hDR
  have hCallEV := @encraw_call_encodeVarint_x img A ext hEV
  have hStepB := @step_encraw_tag13_b_x img A ext hDR hC
  encraw_fetches_range img.base (Rust.withPanics ext) 1184 1244
  encraw_fetches_range img.base (Rust.withPanics ext) 2224 2248
  generalize_entry (SP2Ext img.base ext).fnAddr encodeRawName = entry
  examples_hide_fetches
  rw [hP]
  refine sepWPpIn_extract_vecU8At_bounds (A := A) (v := ss + 96#64) (cap := fCap) (ptr := fPtr) (bs := fBs)
    (h := fun hf_le hf_cap _ => ?_)
  by_cases hf_nil : fBs = []
  · subst hf_nil
    rw [vecU8At_Nil_off' A ss 96#64 104#64 112#64 fCap fPtr]
    simp only [sepConj_assoc]
    apply SepWPpIn.of_sepWP (mid := entry + bv% (1292))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [show
        ((ss + 96#64) ↦₆₄ fCap) ∗ ((ss + 104#64) ↦₆₄ fPtr) ∗ ((ss + 112#64) ↦₆₄ 0#64) ∗
        Prost.vecU8Buf A fCap fPtr [] ∗ vecU8At A v cap ptr bs ∗ A.pool ∗
        stackAt (sp0 - 80#64) encodeRawSubStackX ∗ F =
        (vecU8At A (ss + 96#64) fCap fPtr [] ∗ vecU8At A v cap ptr bs ∗ A.pool ∗
          stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F by
      rw [vecU8At_Nil_off' A ss 96#64 104#64 112#64 fCap fPtr]; simp only [sepConj_assoc]]
    simpa only [bytesField_nil, List.append_nil] using
      hnext _ cap ptr
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
  · have hf_beq : (BitVec.ofNat 64 fBs.length == 0#64) = false :=
      ofNat64_len_beq_zero_false hf_nil (by omega)
    have hfield_eq : bs ++ bytesField 13 fBs =
        ((bs ++ [0x6a#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) ++ fBs := by
      rw [bytesField_ne_nil (k := 0x6a#8) hf_nil]; simp only [List.append_assoc]
    have hlen_bs1 :
        ((bs ++ [0x6a#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)).length + fBs.length < 2 ^ 62 := by
      have h10 := encodeVarint_length_le_10 (BitVec.ofNat 64 fBs.length)
      simp only [List.length_append, List.length_singleton]
      omega
    refine sepWPpIn_extract_vecU8At_bounds (A := A) (v := v) (cap := cap) (ptr := ptr) (bs := bs)
      (h := fun hle _ _ => ?_)
    rw [vecU8At_open_src_off' A ss 96#64 104#64 112#64 fCap fPtr fBs hf_nil hf_le]
    by_cases hlt : bs.length < cap.toNat
    · have hbeq_cap := cap_beq_len_false hlt
      rw [vecU8At_open_one A v cap ptr bs hlt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPpIn.exists_elim fun old => ?_
      apply SepWPpIn.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      rw [vecU8At_close_src_off' A ss 96#64 104#64 112#64 fCap fPtr fBs hf_nil hf_le,
          vecU8At_close_one A v cap ptr bs 0x6a#8 hlt]
      refine hCallEV sp0 (BitVec.ofNat 64 fBs.length) v cap ptr (entry + bv% (1244))
        (bs ++ [0x6a#8]) (by simp; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_frame) ?_
      · simp only [arm64_norm]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · intro s1 cap1 ptr1 hpc1 hrun1 hsp1 htr1 hcs1
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
          ((bs ++ [0x6a#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) fBs
          hf_nil hf_le hf_cap hlen_bs1 hpc1 hrun1 hsp1 halign htr1
          hx19_1 hx20_1 hx21_1 hx22_1 hcs_1 (by sep_frame) ?_
        intro sm cap' ptr' hpcm hrunm hspm htrm hx19m hx20m hcsm'
        rw [← hfield_eq]
        refine SepWPpIn.weaken_pre ?_ (hnext sm cap' ptr' hpcm hrunm hspm htrm hx19m hx20m hcsm')
        exact (by sep_frame)
    · have hcap_eq : cap.toNat = bs.length := by omega
      have hcap_bv := cap_eq_ofNat_len hcap_eq
      rw [Prost.vecU8At_eq_header_sep_buf A v cap ptr bs]
      simp only [vecHeader, sepConj_assoc]
      apply SepWPpIn.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      have hx1_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      refine hCallDR sp0 v cap ptr (entry + bv% (2244)) bs 1
        (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_frame) ?_
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
      · intro s1 newCap p' hpc1 hrun1 hsp1 htr1 hcs1 hnew_ge _
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
        rw [vecU8At_open_one A v newCap p' bs hnew_gt]
        simp only [sepExists_sepConj_left, sepConj_assoc]
        refine SepWPpIn.exists_elim fun old => ?_
        apply SepWPpIn.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        rw [vecU8At_close_one A v newCap p' bs 0x6a#8 hnew_gt]
        refine hCallEV sp0 (BitVec.ofNat 64 fBs.length) v newCap p' (entry + bv% (1244))
          (bs ++ [0x6a#8]) (by simp; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_frame) ?_
        · simp only [arm64_norm]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · intro s2 cap1 ptr1 hpc2 hrun2 hsp2 htr2 hcs2
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
          have hCloseSrc :
              (vecU8At A v cap1 ptr1 ((bs ++ [0x6a#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) ∗
                A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
              ((ss + 96#64) ↦₆₄ fCap) ∗ ((ss + 104#64) ↦₆₄ fPtr) ∗
              ((ss + 112#64) ↦₆₄ BitVec.ofNat 64 fBs.length) ∗
              (fPtr ↦ₛ fBs) ∗ vecSrcRest A fCap fPtr fBs ∗ F =
              (vecU8At A v cap1 ptr1 ((bs ++ [0x6a#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) ∗
                A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
              vecU8At A (ss + 96#64) fCap fPtr fBs ∗ F := by
            rw [vecU8At_close_src_off' A ss 96#64 104#64 112#64 fCap fPtr fBs hf_nil hf_le]
          rw [hCloseSrc]; clear hCloseSrc
          refine hStepB ss v sp0 fCap fPtr cap1 ptr1
            ((bs ++ [0x6a#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) fBs
            hf_nil hf_le hf_cap hlen_bs1 hpc2 hrun2 hsp2 halign htr2
            hx19_2 hx20_2 hx21_2 hx22_2 hcs_2 (by sep_frame) ?_
          intro sm cap' ptr' hpcm hrunm hspm htrm hx19m hx20m hcsm'
          rw [← hfield_eq]
          refine SepWPpIn.weaken_pre ?_ (hnext sm cap' ptr' hpcm hrunm hspm htrm hx19m hx20m hcsm')
          exact (by sep_frame)

end CryptoVerification.E2E.Record.Serialization
