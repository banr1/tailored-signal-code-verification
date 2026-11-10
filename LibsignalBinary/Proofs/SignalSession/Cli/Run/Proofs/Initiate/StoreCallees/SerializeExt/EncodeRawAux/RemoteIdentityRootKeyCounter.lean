/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.EncodeRawAux.PrologueVersionLocalIdentity
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.EncodeRawAux.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `SessionStructure::encode_raw` Segment 1b: Tags 3 (`remote_identity_public`), 4 (`root_key`), and 5 (`previous_counter`)
-/

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
open CryptoVerification.E2E.Record.Serialization

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet hiding stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.LibsignalTripleRatchet.Prost hiding vecU8Buf vecU8At_eq_header_sep_buf

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local irreducible] vecRest vecU8Buf vecSrcRest vecCopyDone

@[local arm64_norm]
theorem bv_add_neg80_1b (x : BitVec 64) : x + bv% (2 ^ 64 - 80) = x - 80#64 :=
  (BitVec.sub_eq_add_neg x 80#64).symm

theorem vecU8At_open_src_off' (A : RustAlloc) (ss off a8 a16 cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hne : bs ≠ []) (hle : bs.length ≤ cap.toNat)
    (h8 : off + 8#64 = a8 := by rfl)
    (h16 : off + 16#64 = a16 := by rfl) :
    vecU8At A (ss + off) cap ptr bs =
      ((ss + off) ↦₆₄ cap) ∗ ((ss + a8) ↦₆₄ ptr) ∗ ((ss + a16) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (ptr ↦ₛ bs) ∗ vecSrcRest A cap ptr bs := by
  subst h8; subst h16
  rw [vecU8At_open_src A (ss + off) cap ptr bs hne hle, BitVec.add_assoc, BitVec.add_assoc]

theorem vecU8At_close_src_off' (A : RustAlloc) (ss off a8 a16 cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hne : bs ≠ []) (hle : bs.length ≤ cap.toNat) (R : SepProp)
    (h8 : off + 8#64 = a8 := by rfl)
    (h16 : off + 16#64 = a16 := by rfl) :
    ((ss + off) ↦₆₄ cap) ∗ ((ss + a8) ↦₆₄ ptr) ∗ ((ss + a16) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (ptr ↦ₛ bs) ∗ vecSrcRest A cap ptr bs ∗ R =
      vecU8At A (ss + off) cap ptr bs ∗ R := by
  subst h8; subst h16
  rw [← BitVec.add_assoc ss off 8#64, ← BitVec.add_assoc ss off 16#64,
      vecU8At_close_src A (ss + off) cap ptr bs hne hle R]

theorem vecU8At_Nil_off' (A : RustAlloc) (ss off a8 a16 cap ptr : BitVec 64)
    (h8 : off + 8#64 = a8 := by rfl)
    (h16 : off + 16#64 = a16 := by rfl) :
    vecU8At A (ss + off) cap ptr [] =
      ((ss + off) ↦₆₄ cap) ∗ ((ss + a8) ↦₆₄ ptr) ∗ ((ss + a16) ↦₆₄ 0#64) ∗
      vecU8Buf A cap ptr [] := by
  subst h8; subst h16
  rw [vecU8At_Nil_eq, BitVec.add_assoc, BitVec.add_assoc]

set_option maxHeartbeats 400000

/-! ## 1. Tag 3 (`remote_identity_public`, `+0x0c0 → +0x12c`, reserve `+0x758..+0x7bc`) -/

/-- Second half of Tag 3 (`+0x0fc..+0x12c`, reserve `+0x774..+0x7bc`): reserves `fBs.length` bytes
if needed and copies `fBs` via `memcpy`. -/
theorem step_encraw_tag3_b {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)} (hA : AllocContractsX img A ext)
    (hDR : OkAtX img ext doReserveName (doReserveSpecX A))
    (ss v sp0 fCap fPtr cap1 ptr1 : BitVec 64) (bs1 fBs : List (BitVec 8))
    (hf_nil : fBs ≠ [])
    (hf_le : fBs.length ≤ fCap.toNat)
    (hf_cap : fCap.toNat < 2 ^ 63)
    (hlen_lt : bs1.length + fBs.length < 2 ^ 62)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + 252#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 fBs.length)
    (hx22 : s.readReg64 .x22 = fPtr)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (vecU8At A (ss + 24#64) fCap fPtr fBs ∗ vecU8At A v cap1 ptr1 bs1 ∗ A.pool ∗
      stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + 300#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        ((vecU8At A (ss + 24#64) fCap fPtr fBs ∗ vecU8At A v cap' ptr' (bs1 ++ fBs) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q (PanicAllocPost s0) := by
  have hCallDR := @encraw_call_doReserve_buf img A ext hDR
  have hCallMC := @encraw_call_memcpy_buf img A ext hA
  encraw_fetches_range img.base (Rust.withPanics ext) 252 300
  encraw_fetches_range img.base (Rust.withPanics ext) 1908 1980
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName = entry
  examples_hide_fetches
  rw [hP]
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap1) (ptr := ptr1) (bs := bs1)
    (h := fun hle1 hcap1 hptr1 => ?_)
  have hf_nat : (BitVec.ofNat 64 fBs.length).toNat = fBs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hbs1_nat : (BitVec.ofNat 64 bs1.length).toNat = bs1.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [vecU8At_open_src A (ss + 24#64) fCap fPtr fBs hf_nil hf_le,
      vecU8At_eq_header_sep_buf A v cap1 ptr1 bs1]
  simp only [vecHeader, sepConj_assoc]
  by_cases hfit : bs1.length + fBs.length ≤ cap1.toNat
  · have hhi := cmp_hi_false_of_le hfit hcap1
    apply SepWPpX.of_sepWP (mid := entry + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine hCallMC v cap1 ptr1 fPtr (entry + bv% (292)) bs1 fBs hfit hcap1 hptr1 hf_nil
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
      have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 fBs.length := by
        have := hcsm.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx23m : sm.readReg64 .x23 = BitVec.ofNat 64 bs1.length := by
        have := hcsm.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hspm' : sm.sp = sp0 - 80#64 := by
        rw [hspm]; simp only [arm64_norm, *]
      have hcsm' : EncRawUpperSaved s0 sm :=
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
          (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
      apply SepWPpX.of_sepWP (mid := entry + bv% (300))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      rw [vecU8At_close_slice A v cap1 ptr1 bs1 fBs hfit hcap1 hptr1 hf_nil]
      refine SepWPpX.weaken_pre ?_ (hnext _ cap1 ptr1
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      rw [vecU8At_open_src A (ss + 24#64) fCap fPtr fBs hf_nil hf_le]
      exact entails_of_sep_focus (by sep_focus)
  · have hhi := cmp_hi_true_of_gt (add := fBs.length) hle1 (by omega) hcap1 (by omega)
    apply SepWPpX.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine hCallDR sp0 v cap1 ptr1 (entry + bv% (1932)) bs1 fBs.length
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
      have hx21_1 : s1.readReg64 .x21 = BitVec.ofNat 64 fBs.length := by
        have := hcs1.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx22_1 : s1.readReg64 .x22 = fPtr := by
        have := hcs1.2.2.2.1; simp only [arm64_norm, *] at this; exact this
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
      refine hCallMC v newCap p' fPtr (entry + bv% (292)) bs1 fBs hnew_ge hnew_lt hp'_ne hf_nil
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
        have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 fBs.length := by
          have := hcsm.2.2.1; simp only [arm64_norm, *] at this; exact this
        have hx23m : sm.readReg64 .x23 = BitVec.ofNat 64 bs1.length := by
          have := hcsm.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
        have hspm' : sm.sp = sp0 - 80#64 := by
          rw [hspm]; simp only [arm64_norm, *]
        have hcsm' : EncRawUpperSaved s0 sm :=
          (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
            (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
        apply SepWPpX.of_sepWP (mid := entry + bv% (300))
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        rw [vecU8At_close_slice A v newCap p' bs1 fBs hnew_ge hnew_lt hp'_ne hf_nil]
        refine SepWPpX.weaken_pre ?_ (hnext _ newCap p'
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
        rw [vecU8At_open_src A (ss + 24#64) fCap fPtr fBs hf_nil hf_le]
        exact entails_of_sep_focus (by sep_focus)

/-- Tag 3 (`+0x0c0..+0x12c`, reserve `+0x758..+0x7bc`): appends `bytesField 3 fBs`
(`remote_identity_public` at `ss + 0x18`) to `v`. -/
theorem step_encraw_tag3 {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)} (hA : AllocContractsX img A ext)
    (hDR : OkAtX img ext doReserveName (doReserveSpecX A))
    (hEV : Prost.EncodeVarintOkExtX img A ext)
    (ss v sp0 fCap fPtr cap ptr : BitVec 64) (bs fBs : List (BitVec 8))
    (hlen_lt : bs.length + 11 + fBs.length < 2 ^ 62)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + 192#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (vecU8At A (ss + 24#64) fCap fPtr fBs ∗ vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + 300#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        ((vecU8At A (ss + 24#64) fCap fPtr fBs ∗ vecU8At A v cap' ptr' (bs ++ bytesField 3 fBs) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q (PanicAllocPost s0) := by
  have hCallDR := @encraw_call_doReserve_buf img A ext hDR
  have hCallEV := @encraw_call_encodeVarint img A ext hEV
  have hStepB := @step_encraw_tag3_b img A ext hA hDR
  encraw_fetches_range img.base (Rust.withPanics ext) 192 252
  encraw_fetches_range img.base (Rust.withPanics ext) 1880 1904
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName = entry
  examples_hide_fetches
  rw [hP]
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := ss + 24#64) (cap := fCap) (ptr := fPtr) (bs := fBs)
    (h := fun hf_le hf_cap _ => ?_)
  by_cases hf_nil : fBs = []
  · subst hf_nil
    rw [vecU8At_Nil_off' A ss 24#64 32#64 40#64 fCap fPtr]
    simp only [sepConj_assoc]
    apply SepWPpX.of_sepWP (mid := entry + bv% (300))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [show
        ((ss + 24#64) ↦₆₄ fCap) ∗ ((ss + 32#64) ↦₆₄ fPtr) ∗ ((ss + 40#64) ↦₆₄ 0#64) ∗
        vecU8Buf A fCap fPtr [] ∗ vecU8At A v cap ptr bs ∗ A.pool ∗
        stackAt (sp0 - 80#64) encodeRawSubStack ∗ F =
        (vecU8At A (ss + 24#64) fCap fPtr [] ∗ vecU8At A v cap ptr bs ∗ A.pool ∗
          stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F by
      rw [vecU8At_Nil_off' A ss 24#64 32#64 40#64 fCap fPtr]; simp only [sepConj_assoc]]
    simpa only [bytesField_nil, List.append_nil] using
      hnext _ cap ptr
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
  · have hf_beq : (BitVec.ofNat 64 fBs.length == 0#64) = false :=
      ofNat64_len_beq_zero_false hf_nil (by omega)
    have hfield_eq : bs ++ bytesField 3 fBs =
        ((bs ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) ++ fBs := by
      rw [bytesField_ne_nil (k := 0x1a#8) hf_nil]; simp only [List.append_assoc]
    have hlen_bs1 :
        ((bs ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)).length + fBs.length < 2 ^ 62 := by
      have h10 := encodeVarint_length_le_10 (BitVec.ofNat 64 fBs.length)
      simp only [List.length_append, List.length_singleton]
      omega
    refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap) (ptr := ptr) (bs := bs)
      (h := fun hle _ _ => ?_)
    rw [vecU8At_open_src_off' A ss 24#64 32#64 40#64 fCap fPtr fBs hf_nil hf_le]
    by_cases hlt : bs.length < cap.toNat
    · have hbeq_cap := cap_beq_len_false hlt
      rw [vecU8At_open_one A v cap ptr bs hlt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPpX.exists_elim fun old => ?_
      apply SepWPpX.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      rw [vecU8At_close_src_off' A ss 24#64 32#64 40#64 fCap fPtr fBs hf_nil hf_le,
          vecU8At_close_one A v cap ptr bs 0x1a#8 hlt]
      refine hCallEV sp0 (BitVec.ofNat 64 fBs.length) v cap ptr (entry + bv% (252))
        (bs ++ [0x1a#8]) (by simp; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
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
          ((bs ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) fBs
          hf_nil hf_le hf_cap hlen_bs1 hpc1 hrun1 hsp1 halign htr1
          hx19_1 hx20_1 hx21_1 hx22_1 hcs_1 (by sep_focus) ?_
        intro sm cap' ptr' hpcm hrunm hspm htrm hx19m hx20m hcsm'
        rw [← hfield_eq]
        refine SepWPpX.weaken_pre ?_ (hnext sm cap' ptr' hpcm hrunm hspm htrm hx19m hx20m hcsm')
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
      refine hCallDR sp0 v cap ptr (entry + bv% (1900)) bs 1
        (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
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
        refine SepWPpX.exists_elim fun old => ?_
        apply SepWPpX.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        rw [vecU8At_close_one A v newCap p' bs 0x1a#8 hnew_gt]
        refine hCallEV sp0 (BitVec.ofNat 64 fBs.length) v newCap p' (entry + bv% (252))
          (bs ++ [0x1a#8]) (by simp; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
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
              (vecU8At A v cap1 ptr1 ((bs ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) ∗
                A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗
              ((ss + 24#64) ↦₆₄ fCap) ∗ ((ss + 32#64) ↦₆₄ fPtr) ∗
              ((ss + 40#64) ↦₆₄ BitVec.ofNat 64 fBs.length) ∗
              (fPtr ↦ₛ fBs) ∗ vecSrcRest A fCap fPtr fBs ∗ F =
              (vecU8At A v cap1 ptr1 ((bs ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) ∗
                A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗
              vecU8At A (ss + 24#64) fCap fPtr fBs ∗ F := by
            rw [vecU8At_close_src_off' A ss 24#64 32#64 40#64 fCap fPtr fBs hf_nil hf_le]
          rw [hCloseSrc]; clear hCloseSrc
          refine hStepB ss v sp0 fCap fPtr cap1 ptr1
            ((bs ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) fBs
            hf_nil hf_le hf_cap hlen_bs1 hpc2 hrun2 hsp2 halign htr2
            hx19_2 hx20_2 hx21_2 hx22_2 hcs_2 (by sep_focus) ?_
          intro sm cap' ptr' hpcm hrunm hspm htrm hx19m hx20m hcsm'
          rw [← hfield_eq]
          refine SepWPpX.weaken_pre ?_ (hnext sm cap' ptr' hpcm hrunm hspm htrm hx19m hx20m hcsm')
          exact entails_of_sep_focus (by sep_focus)

/-! ## 2. Tag 4 (`root_key`, `+0x12c → +0x198`, reserve `+0x7c0..+0x824`) -/

/-- Second half of Tag 4 (`+0x168..+0x198`, reserve `+0x7dc..+0x824`): reserves `fBs.length` bytes
if needed and copies `fBs` via `memcpy`. -/
theorem step_encraw_tag4_b {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)} (hA : AllocContractsX img A ext)
    (hDR : OkAtX img ext doReserveName (doReserveSpecX A))
    (ss v sp0 fCap fPtr cap1 ptr1 : BitVec 64) (bs1 fBs : List (BitVec 8))
    (hf_nil : fBs ≠ [])
    (hf_le : fBs.length ≤ fCap.toNat)
    (hf_cap : fCap.toNat < 2 ^ 63)
    (hlen_lt : bs1.length + fBs.length < 2 ^ 62)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + 360#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 fBs.length)
    (hx22 : s.readReg64 .x22 = fPtr)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (vecU8At A (ss + 48#64) fCap fPtr fBs ∗ vecU8At A v cap1 ptr1 bs1 ∗ A.pool ∗
      stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + 408#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        ((vecU8At A (ss + 48#64) fCap fPtr fBs ∗ vecU8At A v cap' ptr' (bs1 ++ fBs) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q (PanicAllocPost s0) := by
  have hCallDR := @encraw_call_doReserve_buf img A ext hDR
  have hCallMC := @encraw_call_memcpy_buf img A ext hA
  encraw_fetches_range img.base (Rust.withPanics ext) 360 408
  encraw_fetches_range img.base (Rust.withPanics ext) 2012 2084
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName = entry
  examples_hide_fetches
  rw [hP]
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap1) (ptr := ptr1) (bs := bs1)
    (h := fun hle1 hcap1 hptr1 => ?_)
  have hf_nat : (BitVec.ofNat 64 fBs.length).toNat = fBs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hbs1_nat : (BitVec.ofNat 64 bs1.length).toNat = bs1.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [vecU8At_open_src A (ss + 48#64) fCap fPtr fBs hf_nil hf_le,
      vecU8At_eq_header_sep_buf A v cap1 ptr1 bs1]
  simp only [vecHeader, sepConj_assoc]
  by_cases hfit : bs1.length + fBs.length ≤ cap1.toNat
  · have hhi := cmp_hi_false_of_le hfit hcap1
    apply SepWPpX.of_sepWP (mid := entry + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine hCallMC v cap1 ptr1 fPtr (entry + bv% (400)) bs1 fBs hfit hcap1 hptr1 hf_nil
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
      have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 fBs.length := by
        have := hcsm.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx23m : sm.readReg64 .x23 = BitVec.ofNat 64 bs1.length := by
        have := hcsm.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hspm' : sm.sp = sp0 - 80#64 := by
        rw [hspm]; simp only [arm64_norm, *]
      have hcsm' : EncRawUpperSaved s0 sm :=
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
          (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
      apply SepWPpX.of_sepWP (mid := entry + bv% (408))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      rw [vecU8At_close_slice A v cap1 ptr1 bs1 fBs hfit hcap1 hptr1 hf_nil]
      refine SepWPpX.weaken_pre ?_ (hnext _ cap1 ptr1
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      rw [vecU8At_open_src A (ss + 48#64) fCap fPtr fBs hf_nil hf_le]
      exact entails_of_sep_focus (by sep_focus)
  · have hhi := cmp_hi_true_of_gt (add := fBs.length) hle1 (by omega) hcap1 (by omega)
    apply SepWPpX.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine hCallDR sp0 v cap1 ptr1 (entry + bv% (2036)) bs1 fBs.length
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
      have hx21_1 : s1.readReg64 .x21 = BitVec.ofNat 64 fBs.length := by
        have := hcs1.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx22_1 : s1.readReg64 .x22 = fPtr := by
        have := hcs1.2.2.2.1; simp only [arm64_norm, *] at this; exact this
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
      refine hCallMC v newCap p' fPtr (entry + bv% (400)) bs1 fBs hnew_ge hnew_lt hp'_ne hf_nil
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
        have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 fBs.length := by
          have := hcsm.2.2.1; simp only [arm64_norm, *] at this; exact this
        have hx23m : sm.readReg64 .x23 = BitVec.ofNat 64 bs1.length := by
          have := hcsm.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
        have hspm' : sm.sp = sp0 - 80#64 := by
          rw [hspm]; simp only [arm64_norm, *]
        have hcsm' : EncRawUpperSaved s0 sm :=
          (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
            (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
        apply SepWPpX.of_sepWP (mid := entry + bv% (408))
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        rw [vecU8At_close_slice A v newCap p' bs1 fBs hnew_ge hnew_lt hp'_ne hf_nil]
        refine SepWPpX.weaken_pre ?_ (hnext _ newCap p'
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
        rw [vecU8At_open_src A (ss + 48#64) fCap fPtr fBs hf_nil hf_le]
        exact entails_of_sep_focus (by sep_focus)

/-- Tag 4 (`+0x12c..+0x198`, reserve `+0x7c0..+0x824`): appends `bytesField 4 fBs`
(`root_key` at `ss + 0x30`) to `v`. -/
theorem step_encraw_tag4 {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)} (hA : AllocContractsX img A ext)
    (hDR : OkAtX img ext doReserveName (doReserveSpecX A))
    (hEV : Prost.EncodeVarintOkExtX img A ext)
    (ss v sp0 fCap fPtr cap ptr : BitVec 64) (bs fBs : List (BitVec 8))
    (hlen_lt : bs.length + 11 + fBs.length < 2 ^ 62)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + 300#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (vecU8At A (ss + 48#64) fCap fPtr fBs ∗ vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + 408#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        ((vecU8At A (ss + 48#64) fCap fPtr fBs ∗ vecU8At A v cap' ptr' (bs ++ bytesField 4 fBs) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q (PanicAllocPost s0) := by
  have hCallDR := @encraw_call_doReserve_buf img A ext hDR
  have hCallEV := @encraw_call_encodeVarint img A ext hEV
  have hStepB := @step_encraw_tag4_b img A ext hA hDR
  encraw_fetches_range img.base (Rust.withPanics ext) 300 360
  encraw_fetches_range img.base (Rust.withPanics ext) 1984 2008
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName = entry
  examples_hide_fetches
  rw [hP]
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := ss + 48#64) (cap := fCap) (ptr := fPtr) (bs := fBs)
    (h := fun hf_le hf_cap _ => ?_)
  by_cases hf_nil : fBs = []
  · subst hf_nil
    rw [vecU8At_Nil_off' A ss 48#64 56#64 64#64 fCap fPtr]
    simp only [sepConj_assoc]
    apply SepWPpX.of_sepWP (mid := entry + bv% (408))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [show
        ((ss + 48#64) ↦₆₄ fCap) ∗ ((ss + 56#64) ↦₆₄ fPtr) ∗ ((ss + 64#64) ↦₆₄ 0#64) ∗
        vecU8Buf A fCap fPtr [] ∗ vecU8At A v cap ptr bs ∗ A.pool ∗
        stackAt (sp0 - 80#64) encodeRawSubStack ∗ F =
        (vecU8At A (ss + 48#64) fCap fPtr [] ∗ vecU8At A v cap ptr bs ∗ A.pool ∗
          stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F by
      rw [vecU8At_Nil_off' A ss 48#64 56#64 64#64 fCap fPtr]; simp only [sepConj_assoc]]
    simpa only [bytesField_nil, List.append_nil] using
      hnext _ cap ptr
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
  · have hf_beq : (BitVec.ofNat 64 fBs.length == 0#64) = false :=
      ofNat64_len_beq_zero_false hf_nil (by omega)
    have hfield_eq : bs ++ bytesField 4 fBs =
        ((bs ++ [0x22#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) ++ fBs := by
      rw [bytesField_ne_nil (k := 0x22#8) hf_nil]; simp only [List.append_assoc]
    have hlen_bs1 :
        ((bs ++ [0x22#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)).length + fBs.length < 2 ^ 62 := by
      have h10 := encodeVarint_length_le_10 (BitVec.ofNat 64 fBs.length)
      simp only [List.length_append, List.length_singleton]
      omega
    refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap) (ptr := ptr) (bs := bs)
      (h := fun hle _ _ => ?_)
    rw [vecU8At_open_src_off' A ss 48#64 56#64 64#64 fCap fPtr fBs hf_nil hf_le]
    by_cases hlt : bs.length < cap.toNat
    · have hbeq_cap := cap_beq_len_false hlt
      rw [vecU8At_open_one A v cap ptr bs hlt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPpX.exists_elim fun old => ?_
      apply SepWPpX.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      rw [vecU8At_close_src_off' A ss 48#64 56#64 64#64 fCap fPtr fBs hf_nil hf_le,
          vecU8At_close_one A v cap ptr bs 0x22#8 hlt]
      refine hCallEV sp0 (BitVec.ofNat 64 fBs.length) v cap ptr (entry + bv% (360))
        (bs ++ [0x22#8]) (by simp; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
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
          ((bs ++ [0x22#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) fBs
          hf_nil hf_le hf_cap hlen_bs1 hpc1 hrun1 hsp1 halign htr1
          hx19_1 hx20_1 hx21_1 hx22_1 hcs_1 (by sep_focus) ?_
        intro sm cap' ptr' hpcm hrunm hspm htrm hx19m hx20m hcsm'
        rw [← hfield_eq]
        refine SepWPpX.weaken_pre ?_ (hnext sm cap' ptr' hpcm hrunm hspm htrm hx19m hx20m hcsm')
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
      refine hCallDR sp0 v cap ptr (entry + bv% (2004)) bs 1
        (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
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
        refine SepWPpX.exists_elim fun old => ?_
        apply SepWPpX.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        rw [vecU8At_close_one A v newCap p' bs 0x22#8 hnew_gt]
        refine hCallEV sp0 (BitVec.ofNat 64 fBs.length) v newCap p' (entry + bv% (360))
          (bs ++ [0x22#8]) (by simp; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
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
              (vecU8At A v cap1 ptr1 ((bs ++ [0x22#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) ∗
                A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗
              ((ss + 48#64) ↦₆₄ fCap) ∗ ((ss + 56#64) ↦₆₄ fPtr) ∗
              ((ss + 64#64) ↦₆₄ BitVec.ofNat 64 fBs.length) ∗
              (fPtr ↦ₛ fBs) ∗ vecSrcRest A fCap fPtr fBs ∗ F =
              (vecU8At A v cap1 ptr1 ((bs ++ [0x22#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) ∗
                A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗
              vecU8At A (ss + 48#64) fCap fPtr fBs ∗ F := by
            rw [vecU8At_close_src_off' A ss 48#64 56#64 64#64 fCap fPtr fBs hf_nil hf_le]
          rw [hCloseSrc]; clear hCloseSrc
          refine hStepB ss v sp0 fCap fPtr cap1 ptr1
            ((bs ++ [0x22#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) fBs
            hf_nil hf_le hf_cap hlen_bs1 hpc2 hrun2 hsp2 halign htr2
            hx19_2 hx20_2 hx21_2 hx22_2 hcs_2 (by sep_focus) ?_
          intro sm cap' ptr' hpcm hrunm hspm htrm hx19m hx20m hcsm'
          rw [← hfield_eq]
          refine SepWPpX.weaken_pre ?_ (hnext sm cap' ptr' hpcm hrunm hspm htrm hx19m hx20m hcsm')
          exact entails_of_sep_focus (by sep_focus)

/-! ## 3. Tag 5 (`previous_counter`, `+0x198 → +0x1cc`, reserve `+0x828..+0x848`) -/

/-- Tag 5 (`+0x198..+0x1cc`, reserve `+0x828..+0x848`): reads `previous_counter` (`u32`) at
`ss + 0x14c` (`332`), and appends `uint32Field 5 prevCnt` to `v`. -/
theorem step_encraw_tag5 {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hDR : OkAtX img ext doReserveName (doReserveSpecX A))
    (hEV : Prost.EncodeVarintOkExtX img A ext)
    (ss v sp0 cap ptr : BitVec 64) (prevCnt : BitVec 32) (bs : List (BitVec 8))
    (hlen_lt : bs.length + 11 < 2 ^ 62)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + 408#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (((ss + 0x14c#64) ↦₃₂ prevCnt) ∗ vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + 460#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        ((((ss + 0x14c#64) ↦₃₂ prevCnt) ∗ vecU8At A v cap' ptr' (bs ++ uint32Field 5 prevCnt) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q (PanicAllocPost s0) := by
  have hCallDR := @encraw_call_doReserve img A ext hDR
  have hCallEV := @encraw_call_encodeVarint img A ext hEV
  encraw_fetches_range img.base (Rust.withPanics ext) 408 460
  encraw_fetches_range img.base (Rust.withPanics ext) 2088 2120
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName = entry
  examples_hide_fetches
  rw [hP]
  by_cases hver : prevCnt = 0#32
  · subst hver
    apply SepWPpX.of_sepWP (mid := entry + bv% (460))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    simpa only [uint32Field_zero, List.append_nil] using
      hnext _ cap ptr
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
  · have hver_beq : (prevCnt == 0#32) = false := bv32_beq_zero_false hver
    have hfield_eq : bs ++ uint32Field 5 prevCnt =
        (bs ++ [0x28#8]) ++ encodeVarint (BitVec.zeroExtend 64 prevCnt) := by
      rw [uint32Field_ne_zero (k := 0x28#8) hver, List.append_assoc]
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
      rw [vecU8At_close_one A v cap ptr bs 0x28#8 hlt]
      refine hCallEV sp0 (BitVec.zeroExtend 64 prevCnt) v cap ptr (entry + bv% (460))
        (bs ++ [0x28#8]) (by simp; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
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
        refine SepWPpX.weaken_pre ?_ (hnext sm cap' ptr' hpcm hrunm hspm htrm hx19m hx20m hcsm')
        exact entails_of_sep_focus (by sep_focus)
    · have hcap_eq : cap.toNat = bs.length := by omega
      have hcap_bv := cap_eq_ofNat_len hcap_eq
      rw [vecU8At_eq_header_sep_buf A v cap ptr bs]
      simp only [vecHeader, sepConj_assoc]
      apply SepWPpX.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      rw [show
          ((ss + 0x14c#64) ↦₃₂ prevCnt) ∗ (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8Buf A cap ptr bs ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack ∗ F =
          ((ss + 0x14c#64) ↦₃₂ prevCnt) ∗ vecU8At A v cap ptr bs ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack ∗ F by
        rw [vecU8At_eq_header_sep_buf]; simp only [vecHeader, sepConj_assoc]]
      have hx1_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      refine hCallDR sp0 v cap ptr (entry + bv% (2112)) bs 1
        (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
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
        have hx21_1 : s1.readReg64 .x21 = BitVec.zeroExtend 64 prevCnt := by
          have := hcs1.2.2.1; simp only [arm64_norm, *] at this; exact this
        have hcs_1 : EncRawUpperSaved s0 s1 :=
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
            (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
        have hnew_gt : bs.length < newCap.toNat := by omega
        rw [vecU8At_open_one A v newCap p' bs hnew_gt]
        simp only [sepExists_sepConj_left, sepConj_assoc]
        refine SepWPpX.exists_elim fun old => ?_
        apply SepWPpX.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        rw [vecU8At_close_one A v newCap p' bs 0x28#8 hnew_gt]
        refine hCallEV sp0 (BitVec.zeroExtend 64 prevCnt) v newCap p' (entry + bv% (460))
          (bs ++ [0x28#8]) (by simp; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
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
            (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
              (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
          rw [← hfield_eq]
          refine SepWPpX.weaken_pre ?_ (hnext sm cap' ptr' hpcm hrunm hspm htrm hx19m hx20m hcsm')
          exact entails_of_sep_focus (by sep_focus)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
