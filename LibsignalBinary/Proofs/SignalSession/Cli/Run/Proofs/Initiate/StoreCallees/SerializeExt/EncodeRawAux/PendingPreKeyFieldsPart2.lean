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
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.EncodeRawAux.PendingPreKeyFieldsPart1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `SessionStructure::encode_raw` Segment 3b (Part 2): Tag 9 `pending_pre_key` Subfields 2b–4 and Composition
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
open CryptoVerification.E2E.Record.Serialization
open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet hiding stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.LibsignalTripleRatchet.Prost hiding vecU8Buf vecU8At_eq_header_sep_buf
open CryptoVerification.E2E.Record

theorem step_tag9_sub2_b {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)} (hA : AllocContractsX img A ext)
    (hDR : OkAtX img ext doReserveName (doReserveSpecX A))
    (ss v sp0 cap1 ptr1 : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (bs1 : List (BitVec 8))
    (hne_vec : g.vec.bytes ≠ [])
    (hfit1 : bs1.length + g.vec.bytes.length < 2 ^ 60)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + 928#64)
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
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + 976#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId →
      sm.readReg64 .x21 = p.timestamp →
      EncRawUpperSaved s0 sm →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        ((pendingOpenAt A ss g p ∗ vecU8At A v cap' ptr' (bs1 ++ g.vec.bytes) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q (PanicAllocPost s0) := by
  have hCallDR := @encraw_call_doReserve_buf img A ext hDR
  have hCallMC := @encraw_call_memcpy_buf img A ext hA
  encraw_fetches_range img.base (Rust.withPanics ext) 928 976
  encraw_fetches_range img.base (Rust.withPanics ext) 2488 2564
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName = entry
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
    apply SepWPpX.of_sepWP (mid := entry + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>"))
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
      apply SepWPpX.of_sepWP (mid := entry + bv% (976))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      rw [vecU8At_close_slice A v cap1 ptr1 bs1 g.vec.bytes hroom hcap1 hptr1 hne_vec]
      refine SepWPpX.weaken_pre ?_ (hnext _ cap1 ptr1
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      unfold pendingOpenAt
      exact entails_of_sep_focus (by sep_focus)
  · have hhi := cmp_hi_true_of_gt (add := g.vec.bytes.length) hle1 (by omega) hcap1 (by omega)
    apply SepWPpX.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
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
      apply SepWPpX.of_sepWP (mid := entry + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>"))
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
        apply SepWPpX.of_sepWP (mid := entry + bv% (976))
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        rw [vecU8At_close_slice A v newCap p' bs1 g.vec.bytes hnew_ge hnew_lt hp'_ne hne_vec]
        refine SepWPpX.weaken_pre ?_ (hnext _ newCap p'
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
        unfold pendingOpenAt
        exact entails_of_sep_focus (by sep_focus)

/-! ## 4. Step 3b.3 (`976 → 1028`, cold `2564..2592`): subfield 3 (`signed_pre_key_id`) -/

theorem zext64_beq_zero_false_3b {v : BitVec 32} (h : v ≠ 0#32) :
    (BitVec.zeroExtend 64 v == 0#64) = false := by
  rw [zext64_beq_zero_eq v]
  exact beq_false_of_ne h

theorem step_tag9_sub3 {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hEV : EncodeVarintOkExtX img A ext)
    (hDR : OkAtX img ext doReserveName (doReserveSpecX A))
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (bs : List (BitVec 8))
    (hlen_lt : bs.length + 12 < 2 ^ 60)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + 976#64)
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
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + 1028#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x21 = p.timestamp →
      EncRawUpperSaved s0 sm →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        ((pendingOpenAt A ss g p ∗ vecU8At A v cap' ptr' (bs ++ int32Field 3 p.signedPreKeyId) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q (PanicAllocPost s0) := by
  have hCallEV := @encraw_call_encodeVarint img A ext hEV
  have hCallDR := @encraw_call_doReserve_buf img A ext hDR
  encraw_fetches_range img.base (Rust.withPanics ext) 976 1028
  encraw_fetches_range img.base (Rust.withPanics ext) 2564 2592
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName = entry
  examples_hide_fetches
  rw [hP]
  by_cases hspk : p.signedPreKeyId = 0#32
  · simp only [sepConj_assoc]
    apply SepWPpX.of_sepWP (mid := entry + bv% (1028))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine SepWPpX.weaken_pre ?_ (hnext _ cap ptr
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
      refine SepWPpX.exists_elim fun old => ?_
      apply SepWPpX.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      have hclose := vecU8At_close_one A v cap ptr bs 0x18#8 hlt
      refine SepWPpX.weaken_pre (P' :=
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
        refine SepWPpX.weaken_pre ?_ (hnext s1 cap' ptr' hpc1 hrun1 hsp1 htr1
          hx19_1 hx20_1 hx21_1 hcs_1)
        rw [List.append_assoc, int32Field3_nonzero_eq hspk]
        exact entails_of_sep_focus (by sep_focus)
    · have hcap_eq : cap.toNat = bs.length := by omega
      have hcap_bv := cap_eq_ofNat_len hcap_eq
      rw [vecU8At_eq_header_sep_buf A v cap ptr bs]
      simp only [vecHeader, sepConj_assoc]
      apply SepWPpX.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
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
        refine SepWPpX.exists_elim fun old => ?_
        apply SepWPpX.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        have hclose := vecU8At_close_one A v newCap p1 bs 0x18#8 hlt_new
        refine SepWPpX.weaken_pre (P' :=
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
          refine SepWPpX.weaken_pre ?_ (hnext s2 cap' ptr' hpc2 hrun2 hsp2 htr2
            hx19_2 hx20_2 hx21_2 hcs_2)
          rw [List.append_assoc, int32Field3_nonzero_eq hspk]
          exact entails_of_sep_focus (by sep_focus)

/-! ## 5. Step 3b.4 (`1028 → 1080`, cold `2592..2620`): subfield 4 (`timestamp`) -/

theorem step_tag9_sub4 {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hEV : EncodeVarintOkExtX img A ext)
    (hDR : OkAtX img ext doReserveName (doReserveSpecX A))
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (bs : List (BitVec 8))
    (hlen_lt : bs.length + 12 < 2 ^ 60)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + 1028#64)
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
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + 1080#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        ((pendingOpenAt A ss g p ∗ vecU8At A v cap' ptr' (bs ++ uint64Field 4 p.timestamp) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q (PanicAllocPost s0) := by
  have hCallEV := @encraw_call_encodeVarint img A ext hEV
  have hCallDR := @encraw_call_doReserve_buf img A ext hDR
  encraw_fetches_range img.base (Rust.withPanics ext) 1028 1080
  encraw_fetches_range img.base (Rust.withPanics ext) 2592 2620
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName = entry
  examples_hide_fetches
  rw [hP]
  by_cases hts : p.timestamp = 0#64
  · simp only [sepConj_assoc]
    apply SepWPpX.of_sepWP (mid := entry + bv% (1080))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine SepWPpX.weaken_pre ?_ (hnext _ cap ptr
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
      refine SepWPpX.exists_elim fun old => ?_
      apply SepWPpX.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      have hclose := vecU8At_close_one A v cap ptr bs 0x20#8 hlt
      refine SepWPpX.weaken_pre (P' :=
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
        refine SepWPpX.weaken_pre ?_ (hnext s1 cap' ptr' hpc1 hrun1 hsp1 htr1
          hx19_1 hx20_1 hcs_1)
        rw [List.append_assoc, uint64Field4_nonzero_eq hts]
        exact entails_of_sep_focus (by sep_focus)
    · have hcap_eq : cap.toNat = bs.length := by omega
      have hcap_bv := cap_eq_ofNat_len hcap_eq
      rw [vecU8At_eq_header_sep_buf A v cap ptr bs]
      simp only [vecHeader, sepConj_assoc]
      apply SepWPpX.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
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
        refine SepWPpX.exists_elim fun old => ?_
        apply SepWPpX.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        have hclose := vecU8At_close_one A v newCap p1 bs 0x20#8 hlt_new
        refine SepWPpX.weaken_pre (P' :=
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
          refine SepWPpX.weaken_pre ?_ (hnext s2 cap' ptr' hpc2 hrun2 hsp2 htr2
            hx19_2 hx20_2 hcs_2)
          rw [List.append_assoc, uint64Field4_nonzero_eq hts]
          exact entails_of_sep_focus (by sep_focus)

/-! ## 6. Combined Tag 9 step (`536 → 1080`) -/

theorem step_encraw_tag9 {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)} (hA : AllocContractsX img A ext)
    (hEV : EncodeVarintOkExtX img A ext)
    (hDR : OkAtX img ext doReserveName (doReserveSpecX A))
    (ss v sp0 cap ptr : BitVec 64)
    (G_pending : Option TailVecGhost) (s_pending : Option PendingPreKey)
    (bs : List (BitVec 8))
    (hrel : PendingRel G_pending s_pending)
    (hbound : match G_pending with | none => True | some g => g.vec.bytes.length < 2 ^ 32)
    (hbs_lt : bs.length < 2 ^ 32)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + 536#64)
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
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + 1080#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        ((optTailVecAt A 48 (ss + 248#64) G_pending ∗
          vecU8At A v cap' ptr' (bs ++ encPendingFieldMem G_pending s_pending) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q (PanicAllocPost s0) := by
  cases G_pending with
  | none =>
    cases s_pending with
    | some p => exact False.elim hrel
    | none =>
      encraw_fetches_range img.base (Rust.withPanics ext) 536 548
      generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName = entry
      examples_hide_fetches
      rw [hP, optTailVecAt_pending_none_eq]
      simp only [sepConj_assoc]
      apply SepWPpX.of_sepWP (mid := entry + bv% (1080))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      refine SepWPpX.weaken_pre ?_ (hnext _ cap ptr
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
      refine step_tag9_sub2_b hA hDR ss v sp0 cap7 ptr7 g p
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
      refine SepWPpX.weaken_pre ?_ (hnext s10 cap10 ptr10 hpc10 hrun10 hsp10 htr10 hx19_10 hx20_10 hcs10)
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

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
