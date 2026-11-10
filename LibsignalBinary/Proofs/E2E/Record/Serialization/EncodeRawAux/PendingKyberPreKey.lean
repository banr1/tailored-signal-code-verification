/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.Base
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.PendingPreKeyFields
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.RemoteIdentityRootKeyCounter
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.SenderReceiverChains
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `SessionStructure::encode_raw` tag 14 (`pending_kyber_pre_key`, `+0x50c..+0x648`)
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.Serialization.EncodeRawAux

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
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

theorem sepWPp_extract_kyber_some {prog : Program} {ret : BitVec 64} {s : State}
    {A : RustAlloc} {ss : BitVec 64} {g : TailVecGhost} {P F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hfocus : P = optTailVecAt A 32 (ss + 296#64) (some g) ∗ F := by sep_focus)
    (h : g.tail.length = 8 → g.vec.bytes.length ≤ g.vec.cap.toNat →
      g.vec.cap.toNat < 2 ^ 63 → g.vec.ptr ≠ 0#64 →
      SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s P Q Qp := by
  have hfocus1 : P = ⌜g.tail.length = 8⌝ ∗
      (vecU8At A (ss + 296#64) g.vec.cap g.vec.ptr g.vec.bytes ∗
        ((ss + 296#64 + 24#64) ↦ₛ g.tail) ∗ F) := by
    rw [hfocus]; dsimp only [optTailVecAt, vecGhostAt]; ac_rfl
  intro R hm hL
  have hm1 := hm
  rw [hfocus1, sepConj_assoc, satisfies_pure_sepConj] at hm1
  have hfocus2 : P = vecU8At A (ss + 296#64) g.vec.cap g.vec.ptr g.vec.bytes ∗
      (⌜g.tail.length = 8⌝ ∗ ((ss + 296#64 + 24#64) ↦ₛ g.tail) ∗ F) := by
    rw [hfocus]; dsimp only [optTailVecAt, vecGhostAt]; ac_rfl
  exact sepWPp_extract_vecU8At_bounds (hfocus := hfocus2)
    (fun hle hcap hptr => h hm1.1 hle hcap hptr) R hm hL

set_option allowUnsafeReducibility true
attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local irreducible] stackAt vecRest vecU8Buf vecSrcRest vecCopyDone kyberTailRest
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

/-! ## Outer tag `0x72` (`1292..1348`) -/

theorem step_tag14_write_tag {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hDR : OkAt b C ctl abs doReserveName (doReserveSpec A))
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (k : PendingKyberPreKey)
    (bs : List (BitVec 8))
    (hcap_g : g.vec.cap.toNat < 2 ^ 63)
    (hlen_lt : bs.length + 1 < 2 ^ 60)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName + 1292#64)
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
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName + 1348#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x22 = BitVec.zeroExtend 64 k.preKeyId →
      sm.readReg64 .x21 = BitVec.ofNat 64 k.ciphertext.length →
      EncRawUpperSaved s0 sm →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        ((kyberOpenAt A ss g k ∗ vecU8At A v cap' ptr' (bs ++ [0x72#8]) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q (PanicAllocPost s0) := by
  have hCallDR := @encraw_call_doReserve_buf b C A ctl abs hDR
  encraw_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 1292 1348
  encraw_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 2328 2352
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName = entry
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
    refine SepWPp.exists_elim fun old => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (1348))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine SepWPp.weaken_pre ?_ (hnext _ cap ptr
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
    apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
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
      refine SepWPp.exists_elim fun old => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (1348))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      refine SepWPp.weaken_pre ?_ (hnext _ newCap p1
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

/-! ## `pre_key_id` subfield length (`1348..1384/1440`) -/

theorem step_tag14_len1 {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (ss v sp0 : BitVec 64) (k : PendingKyberPreKey)
    (hlt_ct : k.ciphertext.length < 2 ^ 63)
    {ret : BitVec 64} {s0 s : State} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName + 1348#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hx22 : s.readReg64 .x22 = BitVec.zeroExtend 64 k.preKeyId)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 k.ciphertext.length)
    (hcs : EncRawUpperSaved s0 s)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName +
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
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm P Q (PanicAllocPost s0)) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q (PanicAllocPost s0) := by
  encraw_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 1348 1384
  encraw_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 1432 1440
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName = entry
  examples_hide_fetches
  by_cases hpk : k.preKeyId = 0#32
  · by_cases hct : k.ciphertext = []
    · apply SepWPp.of_sepWP (mid := entry + bv% (1440))
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
      apply SepWPp.of_sepWP (mid := entry + bv% (1384))
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
    · apply SepWPp.of_sepWP (mid := entry + bv% (1440))
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
      apply SepWPp.of_sepWP (mid := entry + bv% (1384))
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

/-! ## `ciphertext` subfield length and outer length varint (`1384/1440..1456/1504`) -/

theorem zext64_bne_zero_true_4b {v : BitVec 32} (h : v ≠ 0#32) :
    (BitVec.zeroExtend 64 v != 0#64) = true := by
  simp only [bne, zext64_beq_zero_false_3b h, Bool.not_false]

theorem step_tag14_len2 {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hEV : OkAt b C ctl abs encodeVarintName (encodeVarintSpec A))
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (k : PendingKyberPreKey)
    (bs : List (BitVec 8))
    (hlen_lt : bs.length + 12 < 2 ^ 60)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName +
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
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName +
        (if k.preKeyId == 0#32 then 1504#64 else 1456#64) →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x22 = BitVec.zeroExtend 64 k.preKeyId →
      sm.readReg64 .x21 = BitVec.ofNat 64 k.ciphertext.length →
      EncRawUpperSaved s0 sm →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        ((kyberOpenAt A ss g k ∗
          vecU8At A v cap' ptr'
            ((bs ++ [0x72#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingKyber k).length)) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q (PanicAllocPost s0) := by
  have hCallEV := @encraw_call_encodeVarint b C A ctl abs hEV
  encraw_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 1384 1432
  encraw_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 1440 1456
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName = entry
  examples_hide_fetches
  rw [hP]
  by_cases hct : k.ciphertext = []
  · have hempty : k.ciphertext.isEmpty = true := List.isEmpty_iff.mpr hct
    simp only [hempty, ↓reduceIte] at hpc
    apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
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
        apply SepWPp.of_sepWP (mid := entry + bv% (1504))
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        refine SepWPp.weaken_pre ?_ (hnext _ cap' ptr'
          (by simp only [arm64_norm, ↓reduceIte, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
        exact entails_of_sep_focus (by sep_focus)
      · have hpk_beq : (k.preKeyId == 0#32) = false := beq_false_of_ne hpk
        have hbeq0 := zext64_beq_zero_false_3b hpk
        apply SepWPp.of_sepWP (mid := entry + bv% (1456))
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        refine SepWPp.weaken_pre ?_ (hnext _ cap' ptr'
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
    apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
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
        apply SepWPp.of_sepWP (mid := entry + bv% (1504))
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        refine SepWPp.weaken_pre ?_ (hnext _ cap' ptr'
          (by simp only [arm64_norm, ↓reduceIte, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
        exact entails_of_sep_focus (by sep_focus)
      · have hpk_beq : (k.preKeyId == 0#32) = false := beq_false_of_ne hpk
        have hbeq0 := zext64_beq_zero_false_3b hpk
        apply SepWPp.of_sepWP (mid := entry + bv% (1456))
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        refine SepWPp.weaken_pre ?_ (hnext _ cap' ptr'
          (by simp only [arm64_norm, Bool.false_eq_true, ↓reduceIte, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
        exact entails_of_sep_focus (by sep_focus)

/-! ## `pre_key_id` subfield encoding (`1456/1504..1504`) -/

theorem step_tag14_sub1 {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hEV : OkAt b C ctl abs encodeVarintName (encodeVarintSpec A))
    (hDR : OkAt b C ctl abs doReserveName (doReserveSpec A))
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (k : PendingKyberPreKey)
    (bs : List (BitVec 8))
    (hlen_lt : bs.length + 12 < 2 ^ 60)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName +
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
    (hP : P = (kyberOpenAt A ss g k ∗ vecU8At A v cap ptr bs ∗
      A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName + 1504#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x21 = BitVec.ofNat 64 k.ciphertext.length →
      EncRawUpperSaved s0 sm →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        ((kyberOpenAt A ss g k ∗ vecU8At A v cap' ptr' (bs ++ uint32Field 1 k.preKeyId) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q (PanicAllocPost s0) := by
  by_cases hpk : k.preKeyId = 0#32
  · simp only [hpk, beq_self_eq_true, ↓reduceIte] at hpc
    rw [hP]
    refine SepWPp.weaken_pre ?_ (hnext s cap ptr hpc hrun hsp htr hx19 hx20 hx21 hcs)
    simp only [hpk, uint32Field1_zero_eq_er, List.append_nil]
    exact entails_of_sep_focus (by sep_focus)
  · have hpk_beq : (k.preKeyId == 0#32) = false := beq_false_of_ne hpk
    simp only [hpk_beq, Bool.false_eq_true, ↓reduceIte] at hpc
    have hCallEV := @encraw_call_encodeVarint b C A ctl abs hEV
    have hCallDR := @encraw_call_doReserve_buf b C A ctl abs hDR
    encraw_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 1456 1504
    encraw_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 2620 2644
    generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName = entry
    examples_hide_fetches
    rw [hP]
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
      have hclose := vecU8At_close_one A v cap ptr bs 0x08#8 hlt
      refine SepWPp.weaken_pre (P' :=
          (vecU8At A v cap ptr (bs ++ [0x08#8]) ∗ A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗
            (kyberOpenAt A ss g k ∗ F))
        (by
          rw [← hclose]
          exact entails_of_sep_focus (by sep_focus)) ?_
      refine hCallEV sp0 (BitVec.zeroExtend 64 k.preKeyId) v cap ptr (entry + bv% (1504)) (bs ++ [0x08#8])
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
        have hx21_1 : s1.readReg64 .x21 = BitVec.ofNat 64 k.ciphertext.length := by
          have := hcs1.2.2.1; simp only [arm64_norm, *] at this; exact this
        have hcs_1 : EncRawUpperSaved s0 s1 :=
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
            (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
        refine SepWPp.weaken_pre ?_ (hnext s1 cap' ptr' hpc1 hrun1 hsp1 htr1
          hx19_1 hx20_1 hx21_1 hcs_1)
        rw [List.append_assoc, uint32Field1_nonzero_eq_er hpk]
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
      refine hCallDR sp0 v cap ptr (entry + bv% (2640)) bs 1
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
        have hx21_1 : s1.readReg64 .x21 = BitVec.ofNat 64 k.ciphertext.length := by
          have := hcs1.2.2.1; simp only [arm64_norm, *] at this; exact this
        have hx22_1 : s1.readReg64 .x22 = BitVec.zeroExtend 64 k.preKeyId := by
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
        have hclose := vecU8At_close_one A v newCap p1 bs 0x08#8 hlt_new
        refine SepWPp.weaken_pre (P' :=
            (vecU8At A v newCap p1 (bs ++ [0x08#8]) ∗ A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗
              (kyberOpenAt A ss g k ∗ F))
          (by
            rw [← hclose]
            exact entails_of_sep_focus (by sep_focus)) ?_
        refine hCallEV sp0 (BitVec.zeroExtend 64 k.preKeyId) v newCap p1 (entry + bv% (1504)) (bs ++ [0x08#8])
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
          have hx21_2 : s2.readReg64 .x21 = BitVec.ofNat 64 k.ciphertext.length := by
            have := hcs2.2.2.1; simp only [arm64_norm, *] at this; exact this
          have hcs_2 : EncRawUpperSaved s0 s2 :=
            (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
              (EncRawUpperSaved.of_calleeSavedPreserved hcs2)
          refine SepWPp.weaken_pre ?_ (hnext s2 cap' ptr' hpc2 hrun2 hsp2 htr2
            hx19_2 hx20_2 hx21_2 hcs_2)
          rw [List.append_assoc, uint32Field1_nonzero_eq_er hpk]
          exact entails_of_sep_focus (by sep_focus)

/-! ## `ciphertext` subfield encoding (`1504..1608`) -/

theorem step_tag14_sub2_b {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hDR : OkAt b C ctl abs doReserveName (doReserveSpec A))
    (ss v sp0 fCap fPtr cap1 ptr1 : BitVec 64) (bs1 fBs : List (BitVec 8))
    (hf_nil : fBs ≠ []) (hf_le : fBs.length ≤ fCap.toNat) (hf_cap : fCap.toNat < 2 ^ 63)
    (hlen_lt : bs1.length + fBs.length < 2 ^ 62)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName + 1560#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 fBs.length)
    (hx22 : s.readReg64 .x22 = fPtr)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (vecU8At A (ss + 296#64) fCap fPtr fBs ∗ vecU8At A v cap1 ptr1 bs1 ∗ A.pool ∗
      stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName + 1608#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        ((vecU8At A (ss + 296#64) fCap fPtr fBs ∗ vecU8At A v cap' ptr' (bs1 ++ fBs) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q (PanicAllocPost s0) := by
  have hCallDR := @encraw_call_doReserve_buf b C A ctl abs hDR
  have hCallMC := @encraw_call_memcpy_buf b C A ctl abs
  encraw_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 1560 1608
  encraw_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 2676 2748
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName = entry
  examples_hide_fetches
  rw [hP]
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap1) (ptr := ptr1) (bs := bs1)
    (h := fun hle1 hcap1 hptr1 => ?_)
  have hf_nat : (BitVec.ofNat 64 fBs.length).toNat = fBs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hbs1_nat : (BitVec.ofNat 64 bs1.length).toNat = bs1.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [vecU8At_open_src A (ss + 296#64) fCap fPtr fBs hf_nil hf_le,
      vecU8At_eq_header_sep_buf A v cap1 ptr1 bs1]
  simp only [vecHeader, sepConj_assoc]
  by_cases hfit : bs1.length + fBs.length ≤ cap1.toNat
  · have hhi := cmp_hi_false_of_le hfit hcap1
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine hCallMC v cap1 ptr1 fPtr (entry + bv% (1600)) bs1 fBs hfit hcap1 hptr1 hf_nil
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
      apply SepWPp.of_sepWP (mid := entry + bv% (1608))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      rw [vecU8At_close_slice A v cap1 ptr1 bs1 fBs hfit hcap1 hptr1 hf_nil]
      refine SepWPp.weaken_pre ?_ (hnext _ cap1 ptr1
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      rw [vecU8At_open_src A (ss + 296#64) fCap fPtr fBs hf_nil hf_le]
      exact entails_of_sep_focus (by sep_focus)
  · have hhi := cmp_hi_true_of_gt (add := fBs.length) hle1 (by omega) hcap1 (by omega)
    apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine hCallDR sp0 v cap1 ptr1 (entry + bv% (2700)) bs1 fBs.length
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
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>"))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      refine hCallMC v newCap p' fPtr (entry + bv% (1600)) bs1 fBs hnew_ge hnew_lt hp'_ne hf_nil
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
        apply SepWPp.of_sepWP (mid := entry + bv% (1608))
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        rw [vecU8At_close_slice A v newCap p' bs1 fBs hnew_ge hnew_lt hp'_ne hf_nil]
        refine SepWPp.weaken_pre ?_ (hnext _ newCap p'
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
        rw [vecU8At_open_src A (ss + 296#64) fCap fPtr fBs hf_nil hf_le]
        exact entails_of_sep_focus (by sep_focus)

theorem step_tag14_sub2 {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hDR : OkAt b C ctl abs doReserveName (doReserveSpec A))
    (hEV : Prost.EncodeVarintOk b C A ctl abs)
    (ss v sp0 fCap fPtr cap ptr : BitVec 64) (bs fBs : List (BitVec 8))
    (hlen_lt : bs.length + 11 + fBs.length < 2 ^ 62)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName + 1504#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 fBs.length)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (vecU8At A (ss + 296#64) fCap fPtr fBs ∗ vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName + 1608#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        ((vecU8At A (ss + 296#64) fCap fPtr fBs ∗ vecU8At A v cap' ptr' (bs ++ bytesField 2 fBs) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q (PanicAllocPost s0) := by
  have hCallDR := @encraw_call_doReserve_buf b C A ctl abs hDR
  have hCallEV := @encraw_call_encodeVarint b C A ctl abs hEV
  have hStepB := @step_tag14_sub2_b b C A ctl abs hDR
  encraw_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 1504 1560
  encraw_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 2648 2672
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName = entry
  examples_hide_fetches
  rw [hP]
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := ss + 296#64) (cap := fCap) (ptr := fPtr) (bs := fBs)
    (h := fun hf_le hf_cap _ => ?_)
  by_cases hf_nil : fBs = []
  · subst hf_nil
    simp only [sepConj_assoc]
    apply SepWPp.of_sepWP (mid := entry + bv% (1608))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine SepWPp.weaken_pre ?_ (hnext _ cap ptr
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
    simp only [bytesField_nil, List.append_nil]
    exact entails_of_sep_focus (by sep_focus)
  · have hf_beq : (BitVec.ofNat 64 fBs.length == 0#64) = false :=
      ofNat64_len_beq_zero_false hf_nil (by omega)
    have hfield_eq : bs ++ bytesField 2 fBs =
        ((bs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) ++ fBs := by
      rw [bytesField_ne_nil (k := 0x12#8) hf_nil]; simp only [List.append_assoc]
    have hlen_bs1 :
        ((bs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)).length + fBs.length < 2 ^ 62 := by
      have h10 := encodeVarint_length_le_10 (BitVec.ofNat 64 fBs.length)
      simp only [List.length_append, List.length_singleton]
      omega
    refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap) (ptr := ptr) (bs := bs)
      (h := fun hle _ _ => ?_)
    rw [vecU8At_open_src_off' A ss 296#64 304#64 312#64 fCap fPtr fBs hf_nil hf_le]
    by_cases hlt : bs.length < cap.toNat
    · have hbeq_cap := cap_beq_len_false hlt
      rw [vecU8At_open_one A v cap ptr bs hlt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPp.exists_elim fun old => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      rw [vecU8At_close_src_off' A ss 296#64 304#64 312#64 fCap fPtr fBs hf_nil hf_le,
          vecU8At_close_one A v cap ptr bs 0x12#8 hlt]
      refine hCallEV sp0 (BitVec.ofNat 64 fBs.length) v cap ptr (entry + bv% (1560))
        (bs ++ [0x12#8]) (by simp; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
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
          ((bs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) fBs
          hf_nil hf_le hf_cap hlen_bs1 hpc1 hrun1 hsp1 halign htr1
          hx19_1 hx20_1 hx21_1 hx22_1 hcs_1 (by sep_focus) ?_
        intro sm cap' ptr' hpcm hrunm hspm htrm hx19m hx20m hcsm'
        rw [← hfield_eq]
        refine SepWPp.weaken_pre ?_ (hnext sm cap' ptr' hpcm hrunm hspm htrm hx19m hx20m hcsm')
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
      refine hCallDR sp0 v cap ptr (entry + bv% (2668)) bs 1
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
        refine SepWPp.exists_elim fun old => ?_
        apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        rw [vecU8At_close_one A v newCap p' bs 0x12#8 hnew_gt]
        refine hCallEV sp0 (BitVec.ofNat 64 fBs.length) v newCap p' (entry + bv% (1560))
          (bs ++ [0x12#8]) (by simp; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
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
              (vecU8At A v cap1 ptr1 ((bs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) ∗
                A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗
              ((ss + 296#64) ↦₆₄ fCap) ∗ ((ss + 304#64) ↦₆₄ fPtr) ∗
              ((ss + 312#64) ↦₆₄ BitVec.ofNat 64 fBs.length) ∗
              (fPtr ↦ₛ fBs) ∗ vecSrcRest A fCap fPtr fBs ∗ F =
              (vecU8At A v cap1 ptr1 ((bs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) ∗
                A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗
              vecU8At A (ss + 296#64) fCap fPtr fBs ∗ F := by
            rw [vecU8At_close_src_off' A ss 296#64 304#64 312#64 fCap fPtr fBs hf_nil hf_le]
          rw [hCloseSrc]; clear hCloseSrc
          refine hStepB ss v sp0 fCap fPtr cap1 ptr1
            ((bs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) fBs
            hf_nil hf_le hf_cap hlen_bs1 hpc2 hrun2 hsp2 halign htr2
            hx19_2 hx20_2 hx21_2 hx22_2 hcs_2 (by sep_focus) ?_
          intro sm cap' ptr' hpcm hrunm hspm htrm hx19m hx20m hcsm'
          rw [← hfield_eq]
          refine SepWPp.weaken_pre ?_ (hnext sm cap' ptr' hpcm hrunm hspm htrm hx19m hx20m hcsm')
          exact entails_of_sep_focus (by sep_focus)

/-! ## Combined tag-14 step (`1292..1608`) -/

theorem step_encraw_tag14 {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hEV : OkAt b C ctl abs encodeVarintName (encodeVarintSpec A))
    (hDR : OkAt b C ctl abs doReserveName (doReserveSpec A))
    (ss v sp0 cap ptr : BitVec 64)
    (G_kyber : Option TailVecGhost) (s_kyber : Option PendingKyberPreKey)
    (bs : List (BitVec 8))
    (hrel : KyberRel G_kyber s_kyber)
    (hbound : match s_kyber with | none => True | some k => k.ciphertext.length < 2 ^ 32)
    (hbs_lt : bs.length < 2 ^ 32)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName + 1292#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (optTailVecAt A 32 (ss + 296#64) G_kyber ∗ vecU8At A v cap ptr bs ∗
      A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName + 1608#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        ((optTailVecAt A 32 (ss + 296#64) G_kyber ∗
          vecU8At A v cap' ptr' (bs ++ msgField 14 (s_kyber.map encPendingKyber)) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q (PanicAllocPost s0) := by
  cases G_kyber with
  | none =>
    cases s_kyber with
    | some k => exact False.elim hrel
    | none =>
      encraw_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 1292 1304
      generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName = entry
      examples_hide_fetches
      rw [hP, optTailVecAt_kyber_none_eq]
      simp only [sepConj_assoc]
      apply SepWPp.of_sepWP (mid := entry + bv% (1608))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      refine SepWPp.weaken_pre ?_ (hnext _ cap ptr
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      rw [optTailVecAt_kyber_none_eq]
      simp only [Option.map_none, msgField, List.append_nil]
      exact entails_of_sep_focus (by sep_focus)
  | some g =>
    cases s_kyber with
    | none => exact False.elim hrel
    | some k =>
      have hlt_ct31 : k.ciphertext.length < 2 ^ 32 := hbound
      have hlt_ct63 : k.ciphertext.length < 2 ^ 63 := by omega
      have hlen0_le := encodeVarint_length_le_10 (BitVec.ofNat 64 (encPendingKyber k).length)
      have hlen1_le := uint32Field1_length_le k.preKeyId
      rw [hP]
      refine sepWPp_extract_kyber_some (A := A) (ss := ss) (g := g)
        (h := fun hlen8 _ hcap_g _ => ?_)
      have hopen := optTailVecAt_kyber_some_eq_open A ss g k hlen8 hrel
      rw [hopen]
      refine step_tag14_write_tag hDR ss v sp0 cap ptr g k bs hcap_g (by omega)
        hpc hrun hsp halign htr hx19 hx20 hcs (by sep_focus) ?_
      intro s1 cap1 ptr1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx22_1 hx21_1 hcs1
      refine step_tag14_len1 ss v sp0 k hlt_ct63
        hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx22_1 hx21_1 hcs1 ?_
      intro s2 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx8_2 hx22_2 hx21_2 hcs2
      refine step_tag14_len2 hEV ss v sp0 cap1 ptr1 g k bs (by omega)
        hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2 hx8_2 hx22_2 hx21_2 hcs2 (by sep_focus) ?_
      intro s3 cap3 ptr3 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx22_3 hx21_3 hcs3
      refine step_tag14_sub1 hEV hDR ss v sp0 cap3 ptr3 g k
        ((bs ++ [0x72#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingKyber k).length))
        (by simp only [List.length_append, List.length_singleton]; omega)
        hpc3 hrun3 hsp3 halign htr3 hx19_3 hx20_3 hx22_3 hx21_3 hcs3 (by sep_focus) ?_
      intro s4 cap4 ptr4 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hx21_4 hcs4
      unfold kyberOpenAt
      refine step_tag14_sub2 hDR hEV ss v sp0 g.vec.cap g.vec.ptr cap4 ptr4
        (((bs ++ [0x72#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingKyber k).length)) ++
          uint32Field 1 k.preKeyId)
        k.ciphertext
        (by simp only [List.length_append, List.length_singleton]; omega)
        hpc4 hrun4 hsp4 halign htr4 hx19_4 hx20_4 hx21_4 hcs4 (by sep_focus) ?_
      intro s5 cap5 ptr5 hpc5 hrun5 hsp5 htr5 hx19_5 hx20_5 hcs5
      refine SepWPp.weaken_pre ?_ (hnext s5 cap5 ptr5 hpc5 hrun5 hsp5 htr5 hx19_5 hx20_5 hcs5)
      rw [hopen]
      unfold kyberOpenAt
      have hbytes :
          ((((bs ++ [0x72#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingKyber k).length)) ++
            uint32Field 1 k.preKeyId) ++ bytesField 2 k.ciphertext) =
          bs ++ msgField 14 (Option.map encPendingKyber (some k)) := by
        simp only [Option.map_some, ← msgField14_some_eq k, List.append_assoc]
      rw [hbytes]
      exact entails_of_sep_focus (by sep_focus)

end CryptoVerification.E2E.Record.Serialization.EncodeRawAux
