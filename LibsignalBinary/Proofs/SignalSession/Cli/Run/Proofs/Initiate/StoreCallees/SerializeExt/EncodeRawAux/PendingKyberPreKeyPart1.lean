/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.EncodeRawAux.BasePart2
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.EncodeRawAux.Fetch
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.EncodeRawAux.PendingPreKeyFieldsPart2
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.EncodeRawAux.SenderReceiverChains
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `SessionStructure::encode_raw` Segment 4b (Part 1): Tag 14 `pending_kyber_pre_key` Header and Length
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

theorem uint32Field1_zero_eq_er : uint32Field 1 0#32 = [] := rfl

theorem uint32Field1_nonzero_eq_er {v : BitVec 32} (h : v ≠ 0#32) :
    [0x08#8] ++ encodeVarint (BitVec.zeroExtend 64 v) = uint32Field 1 v := by
  rw [uint32Field_ne_zero (k := 0x08#8) h]

theorem uint32Field1_nonzero_length_bv_er {v : BitVec 32} (h : v ≠ 0#32) :
    BitVec.ofNat 64 (encodeVarint (BitVec.zeroExtend 64 v)).length + 1#64 =
      BitVec.ofNat 64 (uint32Field 1 v).length := by
  rw [← uint32Field1_nonzero_eq_er h]
  simp only [List.length_append, List.length_singleton, ← BitVec.ofNat_add, Nat.add_comm]

theorem uint32Field1_length_le (v : BitVec 32) :
    (uint32Field 1 v).length ≤ 11 := by
  by_cases hv : v = 0#32
  · subst hv; simp [uint32Field1_zero_eq_er]
  · rw [← uint32Field1_nonzero_eq_er hv]
    have h := encodeVarint_length_le_10 (BitVec.zeroExtend 64 v)
    simp only [List.length_append, List.length_singleton]
    omega

theorem encPendingKyber_length_bv (k : PendingKyberPreKey) :
    BitVec.ofNat 64 (bytesField 2 k.ciphertext).length +
      BitVec.ofNat 64 (uint32Field 1 k.preKeyId).length =
      BitVec.ofNat 64 (encPendingKyber k).length := by
  unfold encPendingKyber
  simp only [List.length_append, ← BitVec.ofNat_add, Nat.add_comm]

theorem encPendingKyber_length_bv_ct_nil (k : PendingKyberPreKey) (hct : k.ciphertext = []) :
    0#64 + BitVec.ofNat 64 (uint32Field 1 k.preKeyId).length =
      BitVec.ofNat 64 (encPendingKyber k).length := by
  rw [← encPendingKyber_length_bv k, hct, bytesField_nil]
  rfl

theorem msgField14_some_eq (k : PendingKyberPreKey) :
    [0x72#8] ++ encodeVarint (BitVec.ofNat 64 (encPendingKyber k).length) ++
      uint32Field 1 k.preKeyId ++ bytesField 2 k.ciphertext =
      msgField 14 (some (encPendingKyber k)) := by
  unfold msgField lenField encPendingKyber
  have hk : encodeKey 14 .lengthDelimited = [0x72#8] := by decide +kernel
  rw [hk]
  simp only [List.append_assoc]

theorem optTailVecAt_kyber_none_eq (A : RustAlloc) (ss : BitVec 64) :
    optTailVecAt A 32 (ss + 296#64) none =
      ((ss + 296#64) ↦₆₄ noneCap) ∗ memRegion (ss + 304#64) (32 - 8) := by
  have hadd : (ss + 296#64) + 8#64 = ss + 304#64 := by bv_lin
  dsimp only [optTailVecAt]
  rw [hadd]

def kyberTailRest (ss : BitVec 64) (g : TailVecGhost) : SepProp :=
  (ss + 324#64) ↦ₛ g.tail.drop 4

def kyberOpenAt (A : RustAlloc) (ss : BitVec 64) (g : TailVecGhost) (k : PendingKyberPreKey) : SepProp :=
  vecU8At A (ss + 296#64) g.vec.cap g.vec.ptr k.ciphertext ∗
  ((ss + 320#64) ↦₃₂ k.preKeyId) ∗
  kyberTailRest ss g

theorem optTailVecAt_kyber_some_eq_open (A : RustAlloc) (ss : BitVec 64)
    (g : TailVecGhost) (k : PendingKyberPreKey)
    (hlen8 : g.tail.length = 8)
    (hrel : KyberRel (some g) (some k)) :
    optTailVecAt A 32 (ss + 296#64) (some g) = kyberOpenAt A ss g k := by
  obtain ⟨hvec, hpk⟩ := hrel
  have hpure : (g.tail.length = 32 - 24) = True := eq_true hlen8
  have hadd : (ss + 296#64) + 24#64 = ss + 320#64 := by bv_lin
  dsimp only [optTailVecAt, vecGhostAt]
  rw [hpure, pure_true, emp_sepConj, hadd, hvec,
      pointsToBytes_kyber_tail_eq ss hpk]
  unfold kyberOpenAt kyberTailRest
  ac_rfl

theorem sepWPp_extract_kyber_some {img : Obj.Image} {prog : Program} {ret : BitVec 64} {s : State}
    {A : RustAlloc} {ss : BitVec 64} {g : TailVecGhost} {P F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hfocus : P = optTailVecAt A 32 (ss + 296#64) (some g) ∗ F := by sep_focus)
    (h : g.tail.length = 8 → g.vec.bytes.length ≤ g.vec.cap.toNat →
      g.vec.cap.toNat < 2 ^ 63 → g.vec.ptr ≠ 0#64 →
      SepWPpX img prog ret s P Q Qp) :
    SepWPpX img prog ret s P Q Qp := by
  have hfocus1 : P = ⌜g.tail.length = 8⌝ ∗
      (vecU8At A (ss + 296#64) g.vec.cap g.vec.ptr g.vec.bytes ∗
        ((ss + 296#64 + 24#64) ↦ₛ g.tail) ∗ F) := by
    rw [hfocus]; dsimp only [optTailVecAt, vecGhostAt]; ac_rfl
  intro hinv R hm hL
  have hm1 := hm
  rw [hfocus1, sepConj_assoc, satisfies_pure_sepConj] at hm1
  have hfocus2 : P = vecU8At A (ss + 296#64) g.vec.cap g.vec.ptr g.vec.bytes ∗
      (⌜g.tail.length = 8⌝ ∗ ((ss + 296#64 + 24#64) ↦ₛ g.tail) ∗ F) := by
    rw [hfocus]; dsimp only [optTailVecAt, vecGhostAt]; ac_rfl
  exact sepWPp_extract_vecU8At_bounds (hfocus := hfocus2)
    (fun hle hcap hptr => h hm1.1 hle hcap hptr) hinv R hm hL

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local irreducible] vecRest vecU8Buf vecSrcRest vecCopyDone kyberTailRest
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  truncate32_signExtend64_er truncate32_zeroExtend64
  Prost.ofNat_countLeadingZeros_64
  Prost.ofNat_countLeadingZeros_32
  Prost.truncate32_ofNat64
  er_truncate32_zext64_lsr6
  erHwVarintLen_eq_encodeVarint_length
  erHwVarintLen_bvShift_eq_encodeVarint_length

@[local arm64_norm]
theorem bv_add_neg80_4b (x : BitVec 64) : x + bv% (2 ^ 64 - 80) = x - 80#64 :=
  (BitVec.sub_eq_add_neg x 80#64).symm

set_option maxHeartbeats 400000

/-! ## 1. Step 4b.0 (`1292 → 1348`, cold `2328..2352`): write tag `0x72#8` & load `x22, x21` -/

theorem step_tag14_write_tag {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hDR : OkAtX img ext doReserveName (doReserveSpecX A))
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (k : PendingKyberPreKey)
    (bs : List (BitVec 8))
    (hcap_g : g.vec.cap.toNat < 2 ^ 63)
    (hlen_lt : bs.length + 1 < 2 ^ 60)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + 1292#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (kyberOpenAt A ss g k ∗ vecU8At A v cap ptr bs ∗
      A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + 1348#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x22 = BitVec.zeroExtend 64 k.preKeyId →
      sm.readReg64 .x21 = BitVec.ofNat 64 k.ciphertext.length →
      EncRawUpperSaved s0 sm →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        ((kyberOpenAt A ss g k ∗ vecU8At A v cap' ptr' (bs ++ [0x72#8]) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q (PanicAllocPost s0) := by
  have hCallDR := @encraw_call_doReserve_buf img A ext hDR
  encraw_fetches_range img.base (Rust.withPanics ext) 1292 1348
  encraw_fetches_range img.base (Rust.withPanics ext) 2328 2352
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName = entry
  examples_hide_fetches
  have h8 : (ss + 296#64) + 8#64 = ss + 304#64 := BitVec.add_assoc ss 296#64 8#64
  have h16 : (ss + 296#64) + 16#64 = ss + 312#64 := BitVec.add_assoc ss 296#64 16#64
  rw [hP]
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap) (ptr := ptr) (bs := bs)
    (h := fun hle _ _ => ?_)
  have hcmn1 := cmn1_beq_zero_false hcap_g
  have hcmn2 := cap_beq_noneCap_false hcap_g
  by_cases hlt : bs.length < cap.toNat
  · have hbeq_cap := cap_beq_len_false hlt
    rw [vecU8At_open_one A v cap ptr bs hlt]
    unfold kyberOpenAt
    rw [vecU8At_eq_header_sep_buf A (ss + 296#64) g.vec.cap g.vec.ptr k.ciphertext]
    simp only [vecHeader, h8, h16, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPpX.exists_elim fun old => ?_
    apply SepWPpX.of_sepWP (mid := entry + bv% (1348))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine SepWPpX.weaken_pre ?_ (hnext _ cap ptr
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
    rw [← vecU8At_close_one A v cap ptr bs 0x72#8 hlt]
    unfold kyberOpenAt
    rw [vecU8At_eq_header_sep_buf A (ss + 296#64) g.vec.cap g.vec.ptr k.ciphertext]
    simp only [vecHeader, h8, h16]
    exact entails_of_sep_focus (by sep_focus)
  · have hcap_eq : cap.toNat = bs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    rw [vecU8At_eq_header_sep_buf A v cap ptr bs]
    unfold kyberOpenAt
    rw [vecU8At_eq_header_sep_buf A (ss + 296#64) g.vec.cap g.vec.ptr k.ciphertext]
    simp only [vecHeader, h8, h16, sepConj_assoc]
    apply SepWPpX.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    have hx1_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine hCallDR sp0 v cap ptr (entry + bv% (2348)) bs 1
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
      have hcs_1 : EncRawUpperSaved s0 s1 :=
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
          (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
      have hlt_new : bs.length < newCap.toNat := by omega
      rw [vecU8At_open_one A v newCap p1 bs hlt_new]
      simp only [sepExists_sepConj_left, sepConj_assoc]
      refine SepWPpX.exists_elim fun old => ?_
      apply SepWPpX.of_sepWP (mid := entry + bv% (1348))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      refine SepWPpX.weaken_pre ?_ (hnext _ newCap p1
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      rw [← vecU8At_close_one A v newCap p1 bs 0x72#8 hlt_new]
      unfold kyberOpenAt
      rw [vecU8At_eq_header_sep_buf A (ss + 296#64) g.vec.cap g.vec.ptr k.ciphertext]
      simp only [vecHeader, h8, h16]
      exact entails_of_sep_focus (by sep_focus)

/-! ## 2. Step 4b.1 (`1348 → 1384/1440`): subfield 1 length (`pre_key_id`) -/

theorem step_tag14_len1 {img : Obj.Image} {ext : String → Option (State → State)}
    (ss v sp0 : BitVec 64) (k : PendingKyberPreKey)
    (hlt_ct : k.ciphertext.length < 2 ^ 63)
    {ret : BitVec 64} {s0 s : State} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + 1348#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hx22 : s.readReg64 .x22 = BitVec.zeroExtend 64 k.preKeyId)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 k.ciphertext.length)
    (hcs : EncRawUpperSaved s0 s)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName +
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
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm P Q (PanicAllocPost s0)) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q (PanicAllocPost s0) := by
  encraw_fetches_range img.base (Rust.withPanics ext) 1348 1384
  encraw_fetches_range img.base (Rust.withPanics ext) 1432 1440
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName = entry
  examples_hide_fetches
  by_cases hpk : k.preKeyId = 0#32
  · by_cases hct : k.ciphertext = []
    · apply SepWPpX.of_sepWP (mid := entry + bv% (1440))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      exact hnext _
        (by simp only [arm64_norm, List.isEmpty_nil, ↓reduceIte, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, hpk, uint32Field1_zero_eq_er])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
    · have hempty : k.ciphertext.isEmpty = false := by
        cases h : k.ciphertext <;> simp_all
      have hbeq_ct := ofNat64_len_beq_zero_false hct hlt_ct
      apply SepWPpX.of_sepWP (mid := entry + bv% (1384))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      exact hnext _
        (by simp only [arm64_norm, Bool.false_eq_true, ↓reduceIte, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, hpk, uint32Field1_zero_eq_er])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
  · have hbeq0 := zext64_beq_zero_false_3b hpk
    by_cases hct : k.ciphertext = []
    · apply SepWPpX.of_sepWP (mid := entry + bv% (1440))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      exact hnext _
        (by simp only [arm64_norm, List.isEmpty_nil, ↓reduceIte, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, ← uint32Field1_nonzero_length_bv_er hpk, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
    · have hempty : k.ciphertext.isEmpty = false := by
        cases h : k.ciphertext <;> simp_all
      have hbeq_ct := ofNat64_len_beq_zero_false hct hlt_ct
      apply SepWPpX.of_sepWP (mid := entry + bv% (1384))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      exact hnext _
        (by simp only [arm64_norm, Bool.false_eq_true, ↓reduceIte, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, ← uint32Field1_nonzero_length_bv_er hpk, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)

/-! ## 3. Step 4b.2 (`1384/1440 → 1456/1504`): subfield 2 length & `encode_varint(total_len)` -/

theorem zext64_bne_zero_true_4b {v : BitVec 32} (h : v ≠ 0#32) :
    (BitVec.zeroExtend 64 v != 0#64) = true := by
  simp only [bne, zext64_beq_zero_false_3b h, Bool.not_false]

theorem step_tag14_len2 {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hEV : EncodeVarintOkExtX img A ext)
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (k : PendingKyberPreKey)
    (bs : List (BitVec 8))
    (hlen_lt : bs.length + 12 < 2 ^ 60)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName +
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
    (hP : P = (kyberOpenAt A ss g k ∗ vecU8At A v cap ptr (bs ++ [0x72#8]) ∗
      A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName +
        (if k.preKeyId == 0#32 then 1504#64 else 1456#64) →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x22 = BitVec.zeroExtend 64 k.preKeyId →
      sm.readReg64 .x21 = BitVec.ofNat 64 k.ciphertext.length →
      EncRawUpperSaved s0 sm →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        ((kyberOpenAt A ss g k ∗
          vecU8At A v cap' ptr'
            ((bs ++ [0x72#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingKyber k).length)) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q (PanicAllocPost s0) := by
  have hCallEV := @encraw_call_encodeVarint img A ext hEV
  encraw_fetches_range img.base (Rust.withPanics ext) 1384 1432
  encraw_fetches_range img.base (Rust.withPanics ext) 1440 1456
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName = entry
  examples_hide_fetches
  rw [hP]
  by_cases hct : k.ciphertext = []
  · have hempty : k.ciphertext.isEmpty = true := List.isEmpty_iff.mpr hct
    simp only [hempty, ↓reduceIte] at hpc
    apply SepWPpX.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine hCallEV sp0 (BitVec.ofNat 64 (encPendingKyber k).length) v cap ptr (entry + bv% (1452))
      (bs ++ [0x72#8]) (by simp; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
    · simp only [arm64_norm]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
    · simp only [arm64_norm, *]
    · simp only [arm64_norm]
    · simp only [arm64_norm, ← encPendingKyber_length_bv_ct_nil k hct, *]
    · simp only [arm64_norm, *]
    · intro s1 cap' ptr' hpc1 hrun1 hsp1 htr1 hcs1
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
        apply SepWPpX.of_sepWP (mid := entry + bv% (1504))
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        refine SepWPpX.weaken_pre ?_ (hnext _ cap' ptr'
          (by simp only [arm64_norm, ↓reduceIte, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
        exact entails_of_sep_focus (by sep_focus)
      · have hpk_beq : (k.preKeyId == 0#32) = false := beq_false_of_ne hpk
        have hbeq0 := zext64_beq_zero_false_3b hpk
        apply SepWPpX.of_sepWP (mid := entry + bv% (1456))
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        refine SepWPpX.weaken_pre ?_ (hnext _ cap' ptr'
          (by simp only [arm64_norm, Bool.false_eq_true, ↓reduceIte, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
        exact entails_of_sep_focus (by sep_focus)
  · have hempty : k.ciphertext.isEmpty = false := by
      cases h : k.ciphertext <;> simp_all
    simp only [hempty, Bool.false_eq_true, ↓reduceIte] at hpc
    apply SepWPpX.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine hCallEV sp0 (BitVec.ofNat 64 (encPendingKyber k).length) v cap ptr (entry + bv% (1424))
      (bs ++ [0x72#8]) (by simp; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
    · simp only [arm64_norm]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
    · simp only [arm64_norm, *]
    · simp only [arm64_norm]
    · simp only [arm64_norm, ← encPendingKyber_length_bv k, ← bytesField2_nonempty_length_bv hct, *]
    · simp only [arm64_norm, *]
    · intro s1 cap' ptr' hpc1 hrun1 hsp1 htr1 hcs1
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
        apply SepWPpX.of_sepWP (mid := entry + bv% (1504))
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        refine SepWPpX.weaken_pre ?_ (hnext _ cap' ptr'
          (by simp only [arm64_norm, ↓reduceIte, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
        exact entails_of_sep_focus (by sep_focus)
      · have hpk_beq : (k.preKeyId == 0#32) = false := beq_false_of_ne hpk
        have hbeq0 := zext64_beq_zero_false_3b hpk
        apply SepWPpX.of_sepWP (mid := entry + bv% (1456))
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        refine SepWPpX.weaken_pre ?_ (hnext _ cap' ptr'
          (by simp only [arm64_norm, Bool.false_eq_true, ↓reduceIte, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
        exact entails_of_sep_focus (by sep_focus)

/-! ## 4. Step 4b.3 (`1456/1504 → 1504`, cold `2620..2644`): subfield 1 (`pre_key_id`) -/

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
