/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionLenAux.StepsFront
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionLenAux.Decode
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionLenAux.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Tail step lemmas (`+0x1bc..+0x43c`, Tags 9–15 + epilogue) for `SessionStructure::encoded_len` (`0x25fd0`)

Symbolic execution step lemmas for protobuf tags 9 (`pending_pre_key`), 10 (`remote_registration_id`),
11 (`local_registration_id`), 13 (`alice_base_key`), 14 (`pending_kyber_pre_key`), and 15
(`pq_ratchet_state`), plus the epilogue and relocatable `[LibsignalPlacement]` counterparts.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.Serialization.SessionLenAux

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.E2E.Record CryptoVerification.E2E.Record.Serialization

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm]
  bv_sub_add_lit BitVec.toNat_zero
  sessHwVarintLen_eq_encodeVarint_length
  sessHwVarintLen_bvShift_eq_encodeVarint_length
  Prost.ofNat_countLeadingZeros_64
  Prost.ofNat_countLeadingZeros_32
  Prost.truncate32_ofNat64
  sess_truncate32_zext64_lsr6
  sessHwVarintLen_w32_eq_encodeVarint_length
  sessHwVarintLen_w32_natShift_eq_encodeVarint_length
  Prost.noneCap_add_one_beq_zero
  Prost.noneCap_add_one_bne_zero
  Prost.optU32Tag_beq_one
  Prost.optU32Tag_bne_one
  Prost.zext64_optU32Tag_truncate32
  sess_ule_zero_64
  sess_ult_zero_64

/-! ## Branch-target and `BitVec` normalization helpers -/

@[local simp, local arm64_norm]
theorem add_neg440_eq_624 (entry : BitVec 64) :
    entry + bv% (1064) + bv% (2 ^ 64 - 440) = entry + bv% (624) := by
  bv_omega

@[local simp, local arm64_norm]
theorem add_neg416_eq_652 (entry : BitVec 64) :
    entry + bv% (1068) + bv% (2 ^ 64 - 416) = entry + bv% (652) := by
  bv_omega

@[local simp, local arm64_norm]
theorem add_neg164_eq_912 (entry : BitVec 64) :
    entry + bv% (1076) + bv% (2 ^ 64 - 164) = entry + bv% (912) := by
  bv_omega

@[local simp, local arm64_norm]
theorem add_neg140_eq_940 (entry : BitVec 64) :
    entry + bv% (1080) + bv% (2 ^ 64 - 140) = entry + bv% (940) := by
  bv_omega

@[local simp, local arm64_norm]
theorem truncate32_signExtend64 (w : BitVec 32) :
    BitVec.truncate 32 (BitVec.signExtend 64 w) = w := by
  ext i hi
  simp [BitVec.getLsbD_signExtend, hi]
  omega

@[local simp, local arm64_norm]
theorem bv_encPendingMem_sum (g : TailVecGhost) (p : PendingPreKey) :
    BitVec.ofNat 64 (bytesField 2 g.vec.bytes).length +
      BitVec.ofNat 64 (optUint32Field 1 p.preKeyId).length +
      (BitVec.ofNat 64 (int32Field 3 p.signedPreKeyId).length +
       BitVec.ofNat 64 (uint64Field 4 p.timestamp).length) =
      BitVec.ofNat 64 (encPendingMem g p).length := by
  rw [encPendingMem_length]
  simp only [← BitVec.ofNat_add]
  congr 1
  omega

@[local simp, local arm64_norm]
theorem bv_encPendingKyber_sum (k : PendingKyberPreKey) :
    BitVec.ofNat 64 (bytesField 2 k.ciphertext).length +
      BitVec.ofNat 64 (uint32Field 1 k.preKeyId).length =
      BitVec.ofNat 64 (encPendingKyber k).length := by
  rw [encPendingKyber_length, ← BitVec.ofNat_add, Nat.add_comm]

theorem pendingUnpacked_some_ss (A : RustAlloc) (ss : BitVec 64)
    (g : TailVecGhost) (p : PendingPreKey) :
    pendingUnpacked A (ss + 248#64) (some g) (some p) =
      ((ss + 248#64) ↦₆₄ g.vec.cap) ∗
      ((ss + 256#64) ↦₆₄ g.vec.ptr) ∗
      ((ss + 264#64) ↦₆₄ BitVec.ofNat 64 g.vec.bytes.length) ∗
      ((ss + 272#64) ↦₃₂ optU32Tag p.preKeyId) ∗
      pendingPreKeyIdValAt (ss + 276#64) g.tail p.preKeyId ∗
      ((ss + 280#64) ↦₆₄ p.timestamp) ∗
      ((ss + 288#64) ↦₃₂ p.signedPreKeyId) ∗
      ((ss + 292#64) ↦ₛ g.tail.drop 20) ∗
      vecU8Buf A g.vec.cap g.vec.ptr g.vec.bytes := by
  dsimp only [pendingUnpacked]
  simp only [arm64_norm]

theorem kyberUnpacked_some_ss (A : RustAlloc) (ss : BitVec 64)
    (g : TailVecGhost) (k : PendingKyberPreKey) :
    kyberUnpacked A (ss + 296#64) (some g) (some k) =
      ((ss + 296#64) ↦₆₄ g.vec.cap) ∗
      ((ss + 304#64) ↦₆₄ g.vec.ptr) ∗
      ((ss + 312#64) ↦₆₄ BitVec.ofNat 64 k.ciphertext.length) ∗
      ((ss + 320#64) ↦₃₂ k.preKeyId) ∗
      ((ss + 324#64) ↦ₛ g.tail.drop 4) ∗
      vecU8Buf A g.vec.cap g.vec.ptr k.ciphertext := by
  dsimp only [kyberUnpacked]
  simp only [arm64_norm]

/-! ## Tag 9 (`pending_pre_key` at `ss + 248`, `+0x1bc..+0x2bc` and `+0x420..+0x430`) -/

theorem step_sessLen_pending_a (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (ss : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (hbk_fit : (bytesField 2 g.vec.bytes).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr sessionLenName + 444#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ss)
    (hP : P = pendingUnpacked A (ss + 248#64) (some g) (some p) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr sessionLenName + 580#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = ss →
      sm.readReg64 .x8 = s.readReg64 .x8 →
      sm.readReg64 .x9 = BitVec.ofNat 64 (optUint32Field 1 p.preKeyId).length →
      sm.readReg64 .x10 = BitVec.ofNat 64 (bytesField 2 g.vec.bytes).length →
      SessLenCalleeSaved s sm →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q Qp := by
  intro R hm hL
  have hm_cap : s.mem ⊨ pendingUnpacked A (ss + 248#64) (some g) (some p) ∗ (F ∗ R) := by
    rw [← sepConj_assoc, ← hP]; exact hm
  have hcap_lt : g.vec.cap.toNat < 2 ^ 63 := pendingUnpacked_cap_lt hm_cap
  have hcap_beq : (g.vec.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_false hcap_lt
  clear hm_cap
  revert R hm hL
  change SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q Qp
  sesslen_fetches b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 444 512
  sesslen_fetches b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 540 580
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr sessionLenName = entry
  examples_hide_fetches
  have hbk_beq := ofNat64_length_beq_zero_of_bytesField_lt hbk_fit
  have hbk_bne := ofNat64_length_bne_zero_of_bytesField_lt hbk_fit
  cases hpk : p.preKeyId with
  | none =>
    have hU : P = (((ss + 248#64) ↦₆₄ g.vec.cap) ∗
        ((ss + 256#64) ↦₆₄ g.vec.ptr) ∗
        ((ss + 264#64) ↦₆₄ BitVec.ofNat 64 g.vec.bytes.length) ∗
        ((ss + 272#64) ↦₃₂ 0#32) ∗
        ((ss + 276#64) ↦ₛ (g.tail.drop 4).take 4) ∗
        ((ss + 280#64) ↦₆₄ p.timestamp) ∗
        ((ss + 288#64) ↦₃₂ p.signedPreKeyId) ∗
        ((ss + 292#64) ↦ₛ g.tail.drop 20) ∗
        vecU8Buf A g.vec.cap g.vec.ptr g.vec.bytes) ∗ F := by
      rw [hP, pendingUnpacked_some_ss, hpk]; rfl
    rw [hU]
    by_cases hbk : g.vec.bytes = []
    · have hbk_b : (g.vec.bytes == []) = true := beq_iff_eq.mpr hbk
      have hbk_bn : (g.vec.bytes != []) = false := bne_eq_false_iff_eq.mpr hbk
      apply SepWPp.of_sepWP (mid := entry + bv% (580))
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hU]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [optUint32Field]) (by simp_all [bytesField])
        (by simp_all [SessLenCalleeSaved])
    · have hbk_b : (g.vec.bytes == []) = false := beq_eq_false_iff_ne.mpr hbk
      have hbk_bn : (g.vec.bytes != []) = true := bne_iff_ne.mpr hbk
      have henc2 := bv_bytesField_nonempty_length (t := 2) hbk rfl
      apply SepWPp.of_sepWP (mid := entry + bv% (580))
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hU]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [optUint32Field]) (by simp_all)
        (by simp_all [SessLenCalleeSaved])
  | some v =>
    have hU : P = (((ss + 248#64) ↦₆₄ g.vec.cap) ∗
        ((ss + 256#64) ↦₆₄ g.vec.ptr) ∗
        ((ss + 264#64) ↦₆₄ BitVec.ofNat 64 g.vec.bytes.length) ∗
        ((ss + 272#64) ↦₃₂ 1#32) ∗
        ((ss + 276#64) ↦₃₂ v) ∗
        ((ss + 280#64) ↦₆₄ p.timestamp) ∗
        ((ss + 288#64) ↦₃₂ p.signedPreKeyId) ∗
        ((ss + 292#64) ↦ₛ g.tail.drop 20) ∗
        vecU8Buf A g.vec.cap g.vec.ptr g.vec.bytes) ∗ F := by
      rw [hP, pendingUnpacked_some_ss, hpk]; rfl
    rw [hU]
    have henc1 := bv_optUint32Field_some_length (t := 1) v rfl
    by_cases hbk : g.vec.bytes = []
    · have hbk_b : (g.vec.bytes == []) = true := beq_iff_eq.mpr hbk
      have hbk_bn : (g.vec.bytes != []) = false := bne_eq_false_iff_eq.mpr hbk
      apply SepWPp.of_sepWP (mid := entry + bv% (580))
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hU]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all) (by simp_all [bytesField])
        (by simp_all [SessLenCalleeSaved])
    · have hbk_b : (g.vec.bytes == []) = false := beq_eq_false_iff_ne.mpr hbk
      have hbk_bn : (g.vec.bytes != []) = true := bne_iff_ne.mpr hbk
      have henc2 := bv_bytesField_nonempty_length (t := 2) hbk rfl
      apply SepWPp.of_sepWP (mid := entry + bv% (580))
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hU]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all [SessLenCalleeSaved])

theorem step_sessLen_pending_b (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (ss : BitVec 64) (g : TailVecGhost) (p : PendingPreKey) (s1_7 : Nat)
    (hfit : s1_7 + (lenField 9 (encPendingMem g p)).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr sessionLenName + 580#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ss)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1_7)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 (optUint32Field 1 p.preKeyId).length)
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 (bytesField 2 g.vec.bytes).length)
    (hP : P = pendingUnpacked A (ss + 248#64) (some g) (some p) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr sessionLenName + 700#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = ss →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s1_7 + (lenField 9 (encPendingMem g p)).length) →
      SessLenCalleeSaved s sm →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q Qp := by
  sesslen_fetches b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 580 700
  sesslen_fetches b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 1056 1072
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr sessionLenName = entry
  examples_hide_fetches
  have henc_outer := bv_lenField_length (t := 9) (bs := encPendingMem g p) rfl
  have hcc_ult := ult_ofNat_add_of_lt hfit
  have hadd := bv_add_ofNat_comm s1_7 (lenField 9 (encPendingMem g p)).length
  subst hP
  have hU := pendingUnpacked_some_ss A ss g p
  rw [hU]
  by_cases hspk : p.signedPreKeyId = 0#32
  · have hspk_b : (p.signedPreKeyId == 0#32) = true := beq_iff_eq.mpr hspk
    by_cases hts : p.timestamp = 0#64
    · have hts_b : (p.timestamp == 0#64) = true := beq_iff_eq.mpr hts
      have hts_bn : (p.timestamp != 0#64) = false := bne_eq_false_iff_eq.mpr hts
      have hsum : BitVec.ofNat 64 (bytesField 2 g.vec.bytes).length +
          BitVec.ofNat 64 (optUint32Field 1 p.preKeyId).length =
          BitVec.ofNat 64 (encPendingMem g p).length := by
        rw [encPendingMem_length]
        have h3 : (int32Field 3 p.signedPreKeyId).length = 0 := by simp [int32Field, hspk]
        have h4 : (uint64Field 4 p.timestamp).length = 0 := by simp [uint64Field, hts]
        rw [h3, h4, ← BitVec.ofNat_add]; congr 1; omega
      apply SepWPp.of_sepWP (mid := entry + bv% (700))
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hU]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [SessLenCalleeSaved])
    · have hts_b : (p.timestamp == 0#64) = false := beq_eq_false_iff_ne.mpr hts
      have hts_bn : (p.timestamp != 0#64) = true := bne_iff_ne.mpr hts
      have henc4 := bv_uint64Field_nonzero_length (t := 4) hts rfl
      have hsum : BitVec.ofNat 64 (bytesField 2 g.vec.bytes).length +
          BitVec.ofNat 64 (optUint32Field 1 p.preKeyId).length +
          BitVec.ofNat 64 (uint64Field 4 p.timestamp).length =
          BitVec.ofNat 64 (encPendingMem g p).length := by
        rw [encPendingMem_length]
        have h3 : (int32Field 3 p.signedPreKeyId).length = 0 := by simp [int32Field, hspk]
        rw [h3]; simp only [← BitVec.ofNat_add]; congr 1; omega
      apply SepWPp.of_sepWP (mid := entry + bv% (700))
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hU]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [SessLenCalleeSaved])
  · have hspk_b : (p.signedPreKeyId == 0#32) = false := beq_eq_false_iff_ne.mpr hspk
    have henc3 := bv_int32Field_nonzero_length (t := 3) hspk rfl
    by_cases hts : p.timestamp = 0#64
    · have hts_b : (p.timestamp == 0#64) = true := beq_iff_eq.mpr hts
      have hts_bn : (p.timestamp != 0#64) = false := bne_eq_false_iff_eq.mpr hts
      have hsum : BitVec.ofNat 64 (bytesField 2 g.vec.bytes).length +
          BitVec.ofNat 64 (optUint32Field 1 p.preKeyId).length +
          BitVec.ofNat 64 (int32Field 3 p.signedPreKeyId).length =
          BitVec.ofNat 64 (encPendingMem g p).length := by
        rw [encPendingMem_length]
        have h4 : (uint64Field 4 p.timestamp).length = 0 := by simp [uint64Field, hts]
        rw [h4]; simp only [← BitVec.ofNat_add]; congr 1; omega
      apply SepWPp.of_sepWP (mid := entry + bv% (700))
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hU]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [SessLenCalleeSaved])
    · have hts_b : (p.timestamp == 0#64) = false := beq_eq_false_iff_ne.mpr hts
      have hts_bn : (p.timestamp != 0#64) = true := bne_iff_ne.mpr hts
      have henc4 := bv_uint64Field_nonzero_length (t := 4) hts rfl
      apply SepWPp.of_sepWP (mid := entry + bv% (700))
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hU]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [SessLenCalleeSaved])

theorem step_sessLen_f7 (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (ss : BitVec 64) (G : SessionGhost) (m : Session (List (BitVec 8))) (s1_7 : Nat)
    (hrel : PendingRel G.pending m.pendingPreKey)
    (hfit : s1_7 + (encPendingFieldMem G.pending m.pendingPreKey).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr sessionLenName + 444#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ss)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1_7)
    (hP : P = pendingUnpacked A (ss + 248#64) G.pending m.pendingPreKey ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr sessionLenName + 700#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = ss →
      sm.readReg64 .x8 = BitVec.ofNat 64
        (s1_7 + (encPendingFieldMem G.pending m.pendingPreKey).length) →
      SessLenCalleeSaved s sm →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q Qp := by
  cases hgp : G.pending with
  | none =>
    cases hmp : m.pendingPreKey with
    | none =>
      sesslen_fetches b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 444 456
      sesslen_fetches b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 532 540
      sesslen_fetches b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 692 700
      generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr sessionLenName = entry
      examples_hide_fetches
      have hP0 : P = ((ss + 248#64) ↦₆₄ noneCap) ∗ (memRegion (ss + 248#64 + 8#64) 40 ∗ F) := by
        rw [hP, hgp, hmp]; dsimp only [pendingUnpacked]; ac_rfl
      rw [hP0]
      apply SepWPp.of_sepWP (mid := entry + bv% (700))
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hP0]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all [encPendingFieldMem]) (by simp_all [SessLenCalleeSaved])
    | some _ =>
      rw [hgp, hmp] at hrel; exact hrel.elim
  | some g =>
    cases hmp : m.pendingPreKey with
    | none =>
      rw [hgp, hmp] at hrel; exact hrel.elim
    | some p =>
      have hP' : P = pendingUnpacked A (ss + 248#64) (some g) (some p) ∗ F := by
        rw [hP, hgp, hmp]
      simp only [hgp, hmp, encPendingFieldMem] at hfit
      have hbk_fit : (bytesField 2 g.vec.bytes).length < 2 ^ 64 := by
        have := lenField_length (t := 9) (encPendingMem g p) rfl
        have := encPendingMem_length g p
        omega
      refine step_sessLen_pending_a b C A ctl abs ss g p hbk_fit hpc hrun hx19 hP' ?_
      intro s1 hpc1 hrun1 hsp1 htr1 hx19_1 hx8_1 hx9_1 hx10_1 hcs1
      refine step_sessLen_pending_b b C A ctl abs ss g p s1_7 hfit
        hpc1 hrun1 hx19_1 (hx8_1.trans hx8) hx9_1 hx10_1 hP' ?_
      intro s2 hpc2 hrun2 hsp2 htr2 hx19_2 hx8_2 hcs2
      refine hnext s2 hpc2 hrun2 (hsp2.trans hsp1) (htr2.trans htr1) hx19_2 ?_ (hcs1.trans hcs2)
      simpa only [hgp, hmp, encPendingFieldMem] using hx8_2

/-! ## Tag 10 (`remote_registration_id` at `ss + 336`, `+0x2bc..+0x2f4`) -/

theorem step_sessLen_f8 (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (ss : BitVec 64) (m : Session (List (BitVec 8))) (s1_8 : Nat)
    (hfit : s1_8 + (uint32Field 10 m.remoteRegistrationId).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr sessionLenName + 700#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ss)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1_8)
    (hP : P = tags10to15Cells ss m ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr sessionLenName + 756#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = ss →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s1_8 + (uint32Field 10 m.remoteRegistrationId).length) →
      SessLenCalleeSaved s sm →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q Qp := by
  sesslen_fetches b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 700 756
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr sessionLenName = entry
  examples_hide_fetches
  subst hP
  have hT : tags10to15Cells ss m =
      ((ss + 112#64) ↦₆₄ BitVec.ofNat 64 m.aliceBaseKey.length) ∗
      ((ss + 136#64) ↦₆₄ BitVec.ofNat 64 m.state.pqRatchetState.length) ∗
      ((ss + 336#64) ↦₃₂ m.remoteRegistrationId) ∗
      ((ss + 340#64) ↦₃₂ m.localRegistrationId) := rfl
  rw [hT]
  by_cases hrem : m.remoteRegistrationId = 0#32
  · have hrem_b : (m.remoteRegistrationId == 0#32) = true := beq_iff_eq.mpr hrem
    apply SepWPp.of_sepWP (mid := entry + bv% (756))
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hT]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all [uint32Field]) (by simp_all [SessLenCalleeSaved])
  · have hrem_b : (m.remoteRegistrationId == 0#32) = false := beq_eq_false_iff_ne.mpr hrem
    have henc := bv_uint32Field_nonzero_length (t := 10) hrem rfl
    have hcc := ule_ofNat_add_of_lt hfit
    have hcc_ult := ult_ofNat_add_of_lt hfit
    have hadd := bv_add_ofNat_comm s1_8 (uint32Field 10 m.remoteRegistrationId).length
    apply SepWPp.of_sepWP (mid := entry + bv% (756))
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hT]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [SessLenCalleeSaved])

/-! ## Tag 11 (`local_registration_id` at `ss + 340`, `+0x2f4..+0x32c`) -/

theorem step_sessLen_f9 (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (ss : BitVec 64) (m : Session (List (BitVec 8))) (s1_9 : Nat)
    (hfit : s1_9 + (uint32Field 11 m.localRegistrationId).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr sessionLenName + 756#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ss)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1_9)
    (hP : P = tags10to15Cells ss m ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr sessionLenName + 812#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = ss →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s1_9 + (uint32Field 11 m.localRegistrationId).length) →
      SessLenCalleeSaved s sm →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q Qp := by
  sesslen_fetches b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 756 812
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr sessionLenName = entry
  examples_hide_fetches
  subst hP
  have hT : tags10to15Cells ss m =
      ((ss + 112#64) ↦₆₄ BitVec.ofNat 64 m.aliceBaseKey.length) ∗
      ((ss + 136#64) ↦₆₄ BitVec.ofNat 64 m.state.pqRatchetState.length) ∗
      ((ss + 336#64) ↦₃₂ m.remoteRegistrationId) ∗
      ((ss + 340#64) ↦₃₂ m.localRegistrationId) := rfl
  rw [hT]
  by_cases hloc : m.localRegistrationId = 0#32
  · have hloc_b : (m.localRegistrationId == 0#32) = true := beq_iff_eq.mpr hloc
    apply SepWPp.of_sepWP (mid := entry + bv% (812))
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hT]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all [uint32Field]) (by simp_all [SessLenCalleeSaved])
  · have hloc_b : (m.localRegistrationId == 0#32) = false := beq_eq_false_iff_ne.mpr hloc
    have henc := bv_uint32Field_nonzero_length (t := 11) hloc rfl
    have hcc := ule_ofNat_add_of_lt hfit
    have hcc_ult := ult_ofNat_add_of_lt hfit
    have hadd := bv_add_ofNat_comm s1_9 (uint32Field 11 m.localRegistrationId).length
    apply SepWPp.of_sepWP (mid := entry + bv% (812))
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hT]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [SessLenCalleeSaved])

/-! ## Tag 13 (`alice_base_key` at `ss + 112`, `+0x32c..+0x358`) -/

theorem step_sessLen_f10 (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (ss : BitVec 64) (m : Session (List (BitVec 8))) (s1_10 : Nat)
    (hfit : s1_10 + (bytesField 13 m.aliceBaseKey).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr sessionLenName + 812#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ss)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1_10)
    (hP : P = tags10to15Cells ss m ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr sessionLenName + 856#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = ss →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s1_10 + (bytesField 13 m.aliceBaseKey).length) →
      SessLenCalleeSaved s sm →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q Qp := by
  sesslen_fetches b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 812 856
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr sessionLenName = entry
  examples_hide_fetches
  have halice_fit : (bytesField 13 m.aliceBaseKey).length < 2 ^ 64 := by omega
  have halice_beq := ofNat64_length_beq_zero_of_bytesField_lt halice_fit
  subst hP
  have hT : tags10to15Cells ss m =
      ((ss + 112#64) ↦₆₄ BitVec.ofNat 64 m.aliceBaseKey.length) ∗
      ((ss + 136#64) ↦₆₄ BitVec.ofNat 64 m.state.pqRatchetState.length) ∗
      ((ss + 336#64) ↦₃₂ m.remoteRegistrationId) ∗
      ((ss + 340#64) ↦₃₂ m.localRegistrationId) := rfl
  rw [hT]
  by_cases halice : m.aliceBaseKey = []
  · have halice_b : (m.aliceBaseKey == []) = true := beq_iff_eq.mpr halice
    apply SepWPp.of_sepWP (mid := entry + bv% (856))
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hT]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all [bytesField]) (by simp_all [SessLenCalleeSaved])
  · have halice_b : (m.aliceBaseKey == []) = false := beq_eq_false_iff_ne.mpr halice
    have henc := bv_bytesField_nonempty_length (t := 13) halice rfl
    have hcc_ult := ult_ofNat_add_of_lt hfit
    have hadd := bv_add_ofNat_comm s1_10 (bytesField 13 m.aliceBaseKey).length
    apply SepWPp.of_sepWP (mid := entry + bv% (856))
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hT]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [SessLenCalleeSaved])

/-! ## Tag 14 (`pending_kyber_pre_key` at `ss + 296`, `+0x358..+0x3e0` and `+0x430..+0x43c`) -/

theorem step_sessLen_kyber_some (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (ss : BitVec 64) (g : TailVecGhost) (k : PendingKyberPreKey) (s1_11 : Nat)
    (hfit : s1_11 + (lenField 14 (encPendingKyber k)).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr sessionLenName + 856#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ss)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1_11)
    (hP : P = kyberUnpacked A (ss + 296#64) (some g) (some k) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr sessionLenName + 992#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = ss →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s1_11 + (lenField 14 (encPendingKyber k)).length) →
      SessLenCalleeSaved s sm →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q Qp := by
  intro R hm hL
  have hm_cap : s.mem ⊨ kyberUnpacked A (ss + 296#64) (some g) (some k) ∗ (F ∗ R) := by
    rw [← sepConj_assoc, ← hP]; exact hm
  have hcap_lt : g.vec.cap.toNat < 2 ^ 63 := kyberUnpacked_cap_lt hm_cap
  have hcap_beq : (g.vec.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_false hcap_lt
  clear hm_cap
  revert R hm hL
  change SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q Qp
  sesslen_fetches b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 856 984
  sesslen_fetches b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 1072 1084
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr sessionLenName = entry
  examples_hide_fetches
  have hct_fit : (bytesField 2 k.ciphertext).length < 2 ^ 64 := by
    have := lenField_length (t := 14) (encPendingKyber k) rfl
    have := encPendingKyber_length k
    omega
  have hct_beq := ofNat64_length_beq_zero_of_bytesField_lt hct_fit
  have hct_bne := ofNat64_length_bne_zero_of_bytesField_lt hct_fit
  have henc_outer := bv_lenField_length (t := 14) (bs := encPendingKyber k) rfl
  have hcc := ule_ofNat_add_of_lt hfit
  have hcc_ult := ult_ofNat_add_of_lt hfit
  have hadd := bv_add_ofNat_comm s1_11 (lenField 14 (encPendingKyber k)).length
  subst hP
  have hU := kyberUnpacked_some_ss A ss g k
  rw [hU]
  by_cases hid : k.preKeyId = 0#32
  · have hid_b : (k.preKeyId == 0#32) = true := beq_iff_eq.mpr hid
    by_cases hct : k.ciphertext = []
    · have hct_b : (k.ciphertext == []) = true := beq_iff_eq.mpr hct
      have hct_bn : (k.ciphertext != []) = false := bne_eq_false_iff_eq.mpr hct
      have h0 : (encPendingKyber k).length = 0 := by
        simp [encPendingKyber, uint32Field, hid, bytesField, hct]
      have hlen14 : (lenField 14 (encPendingKyber k)).length = 2 := by
        rw [lenField_length (t := 14) (encPendingKyber k) rfl, h0]; rfl
      apply SepWPp.of_sepWP (mid := entry + bv% (992))
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hU]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [SessLenCalleeSaved])
    · have hct_b : (k.ciphertext == []) = false := beq_eq_false_iff_ne.mpr hct
      have hct_bn : (k.ciphertext != []) = true := bne_iff_ne.mpr hct
      have henc2 := bv_bytesField_nonempty_length (t := 2) hct rfl
      have hsum : BitVec.ofNat 64 (bytesField 2 k.ciphertext).length =
          BitVec.ofNat 64 (encPendingKyber k).length := by
        rw [encPendingKyber_length]
        have hid0 : (uint32Field 1 k.preKeyId).length = 0 := by simp [uint32Field, hid]
        rw [hid0, Nat.zero_add]
      apply SepWPp.of_sepWP (mid := entry + bv% (992))
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hU]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [SessLenCalleeSaved])
  · have hid_b : (k.preKeyId == 0#32) = false := beq_eq_false_iff_ne.mpr hid
    have henc1 := bv_uint32Field_nonzero_length (t := 1) hid rfl
    by_cases hct : k.ciphertext = []
    · have hct_b : (k.ciphertext == []) = true := beq_iff_eq.mpr hct
      have hct_bn : (k.ciphertext != []) = false := bne_eq_false_iff_eq.mpr hct
      have hsum : BitVec.ofNat 64 (uint32Field 1 k.preKeyId).length =
          BitVec.ofNat 64 (encPendingKyber k).length := by
        rw [encPendingKyber_length]
        have hct0 : (bytesField 2 k.ciphertext).length = 0 := by simp [bytesField, hct]
        rw [hct0, Nat.add_zero]
      apply SepWPp.of_sepWP (mid := entry + bv% (992))
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hU]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [SessLenCalleeSaved])
    · have hct_b : (k.ciphertext == []) = false := beq_eq_false_iff_ne.mpr hct
      have hct_bn : (k.ciphertext != []) = true := bne_iff_ne.mpr hct
      have henc2 := bv_bytesField_nonempty_length (t := 2) hct rfl
      apply SepWPp.of_sepWP (mid := entry + bv% (992))
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hU]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [SessLenCalleeSaved])

theorem step_sessLen_f11 (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (ss : BitVec 64) (G : SessionGhost) (m : Session (List (BitVec 8))) (s1_11 : Nat)
    (hrel : KyberRel G.kyber m.pendingKyberPreKey)
    (hfit : s1_11 + (msgField 14 (m.pendingKyberPreKey.map encPendingKyber)).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr sessionLenName + 856#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ss)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1_11)
    (hP : P = kyberUnpacked A (ss + 296#64) G.kyber m.pendingKyberPreKey ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr sessionLenName + 992#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = ss →
      sm.readReg64 .x8 = BitVec.ofNat 64
        (s1_11 + (msgField 14 (m.pendingKyberPreKey.map encPendingKyber)).length) →
      SessLenCalleeSaved s sm →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q Qp := by
  cases hgk : G.kyber with
  | none =>
    cases hmk : m.pendingKyberPreKey with
    | none =>
      sesslen_fetches b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 856 868
      sesslen_fetches b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 984 992
      generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr sessionLenName = entry
      examples_hide_fetches
      have hP0 : P = ((ss + 296#64) ↦₆₄ noneCap) ∗ (memRegion (ss + 296#64 + 8#64) 24 ∗ F) := by
        rw [hP, hgk, hmk]; dsimp only [kyberUnpacked]; ac_rfl
      rw [hP0]
      apply SepWPp.of_sepWP (mid := entry + bv% (992))
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hP0]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all [msgField]) (by simp_all [SessLenCalleeSaved])
    | some _ =>
      rw [hgk, hmk] at hrel; exact hrel.elim
  | some g =>
    cases hmk : m.pendingKyberPreKey with
    | none =>
      rw [hgk, hmk] at hrel; exact hrel.elim
    | some k =>
      have hP' : P = kyberUnpacked A (ss + 296#64) (some g) (some k) ∗ F := by
        rw [hP, hgk, hmk]
      simp only [hmk, Option.map_some, msgField] at hfit
      refine step_sessLen_kyber_some b C A ctl abs ss g k s1_11 hfit hpc hrun hx19 hx8 hP' ?_
      intro s1 hpc1 hrun1 hsp1 htr1 hx19_1 hx8_1 hcs1
      refine hnext s1 hpc1 hrun1 hsp1 htr1 hx19_1 ?_ hcs1
      simpa only [hmk, Option.map_some, msgField] using hx8_1

/-! ## Tag 15 (`pq_ratchet_state` at `ss + 136`) and epilogue (`+0x3e0..+0x420`) -/

theorem step_sessLen_f12 (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (ss sp0 : BitVec 64) (m : Session (List (BitVec 8))) (s1_12 : Nat)
    (hfit : s1_12 + (bytesField 15 m.state.pqRatchetState).length < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr sessionLenName + 992#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 64#64)
    (halign : (sp0 &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = ss)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1_12)
    (hcs : SessLenCalleeSaved s0 s)
    (hP : P = (tags10to15Cells ss m ∗
      frameCells sp0 (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x24) (s0.readReg64 .x23)
        (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp0 →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (s1_12 + (bytesField 15 m.state.pqRatchetState).length) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPp (tripleRatchetProgAt b C ctl abs) (s0.readReg64 .lr) s P Q Qp := by
  sesslen_fetches b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 992 1056
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr sessionLenName = entry
  examples_hide_fetches
  rcases hcs with ⟨h25, h26, h27, h28, hvregs⟩
  have hpq_fit : (bytesField 15 m.state.pqRatchetState).length < 2 ^ 64 := by omega
  have hpq_beq := ofNat64_length_beq_zero_of_bytesField_lt hpq_fit
  subst hP
  have hT : tags10to15Cells ss m =
      ((ss + 112#64) ↦₆₄ BitVec.ofNat 64 m.aliceBaseKey.length) ∗
      ((ss + 136#64) ↦₆₄ BitVec.ofNat 64 m.state.pqRatchetState.length) ∗
      ((ss + 336#64) ↦₃₂ m.remoteRegistrationId) ∗
      ((ss + 340#64) ↦₃₂ m.localRegistrationId) := rfl
  have hFr : frameCells sp0 (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x24) (s0.readReg64 .x23)
        (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19) =
      ((sp0 - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp0 - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp0 - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((sp0 - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
      ((sp0 - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp0 - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((sp0 - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp0 - 8#64) ↦₆₄ s0.readReg64 .x19) := rfl
  rw [hT, hFr]
  by_cases hpq : m.state.pqRatchetState = []
  · have hpq_b : (m.state.pqRatchetState == []) = true := beq_iff_eq.mpr hpq
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hT, ← hFr]
    apply SepWPp.done (by simp_all) (by simp_all)
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all [bytesField]) (by simp_all [CalleeSavedPreserved])
  · have hpq_b : (m.state.pqRatchetState == []) = false := beq_eq_false_iff_ne.mpr hpq
    have henc := bv_bytesField_nonempty_length (t := 15) hpq rfl
    have hcc_ult := ult_ofNat_add_of_lt hfit
    have hadd := bv_add_ofNat_comm s1_12 (bytesField 15 m.state.pqRatchetState).length
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hT, ← hFr]
    apply SepWPp.done (by simp_all) (by simp_all)
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all [CalleeSavedPreserved])

/-! ## Relocatable `[LibsignalPlacement]` tail step lemmas (block `86`) -/

section Placed

open CryptoVerification CryptoVerification.E2E.Record.Placed

theorem step_sessLen_pending_a_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (ss : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (hbk_fit : (bytesField 2 g.vec.bytes).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_86).base + 444#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ss)
    (hP : P = pendingUnpacked A (ss + 248#64) (some g) (some p) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_86).base + 580#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = ss →
      sm.readReg64 .x8 = s.readReg64 .x8 →
      sm.readReg64 .x9 = BitVec.ofNat 64 (optUint32Field 1 p.preKeyId).length →
      sm.readReg64 .x10 = BitVec.ofNat 64 (bytesField 2 g.vec.bytes).length →
      SessLenCalleeSaved s sm →
      SepWPp (lsProg_86 H) ret sm P Q Qp) :
    SepWPp (lsProg_86 H) ret s P Q Qp := by
  intro R hm hL
  have hm_cap : s.mem ⊨ pendingUnpacked A (ss + 248#64) (some g) (some p) ∗ (F ∗ R) := by
    rw [← sepConj_assoc, ← hP]; exact hm
  have hcap_lt : g.vec.cap.toNat < 2 ^ 63 := pendingUnpacked_cap_lt hm_cap
  have hcap_beq : (g.vec.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_false hcap_lt
  clear hm_cap
  revert R hm hL
  change SepWPp (lsProg_86 H) ret s P Q Qp
  have hbk_beq := ofNat64_length_beq_zero_of_bytesField_lt hbk_fit
  have hbk_bne := ofNat64_length_bne_zero_of_bytesField_lt hbk_fit
  cases hpk : p.preKeyId with
  | none =>
    have hU : P = (((ss + 248#64) ↦₆₄ g.vec.cap) ∗
        ((ss + 256#64) ↦₆₄ g.vec.ptr) ∗
        ((ss + 264#64) ↦₆₄ BitVec.ofNat 64 g.vec.bytes.length) ∗
        ((ss + 272#64) ↦₃₂ 0#32) ∗
        ((ss + 276#64) ↦ₛ (g.tail.drop 4).take 4) ∗
        ((ss + 280#64) ↦₆₄ p.timestamp) ∗
        ((ss + 288#64) ↦₃₂ p.signedPreKeyId) ∗
        ((ss + 292#64) ↦ₛ g.tail.drop 20) ∗
        vecU8Buf A g.vec.cap g.vec.ptr g.vec.bytes) ∗ F := by
      rw [hP, pendingUnpacked_some_ss, hpk]; rfl
    rw [hU]
    by_cases hbk : g.vec.bytes = []
    · have hbk_b : (g.vec.bytes == []) = true := beq_iff_eq.mpr hbk
      have hbk_bn : (g.vec.bytes != []) = false := bne_eq_false_iff_eq.mpr hbk
      apply SepWPp.of_sepWP (mid := (blkPl_86).base + bv% (580))
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hU]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [optUint32Field]) (by simp_all [bytesField])
        (by simp_all [SessLenCalleeSaved])
    · have hbk_b : (g.vec.bytes == []) = false := beq_eq_false_iff_ne.mpr hbk
      have hbk_bn : (g.vec.bytes != []) = true := bne_iff_ne.mpr hbk
      have henc2 := bv_bytesField_nonempty_length (t := 2) hbk rfl
      apply SepWPp.of_sepWP (mid := (blkPl_86).base + bv% (580))
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hU]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [optUint32Field]) (by simp_all)
        (by simp_all [SessLenCalleeSaved])
  | some v =>
    have hU : P = (((ss + 248#64) ↦₆₄ g.vec.cap) ∗
        ((ss + 256#64) ↦₆₄ g.vec.ptr) ∗
        ((ss + 264#64) ↦₆₄ BitVec.ofNat 64 g.vec.bytes.length) ∗
        ((ss + 272#64) ↦₃₂ 1#32) ∗
        ((ss + 276#64) ↦₃₂ v) ∗
        ((ss + 280#64) ↦₆₄ p.timestamp) ∗
        ((ss + 288#64) ↦₃₂ p.signedPreKeyId) ∗
        ((ss + 292#64) ↦ₛ g.tail.drop 20) ∗
        vecU8Buf A g.vec.cap g.vec.ptr g.vec.bytes) ∗ F := by
      rw [hP, pendingUnpacked_some_ss, hpk]; rfl
    rw [hU]
    have henc1 := bv_optUint32Field_some_length (t := 1) v rfl
    by_cases hbk : g.vec.bytes = []
    · have hbk_b : (g.vec.bytes == []) = true := beq_iff_eq.mpr hbk
      have hbk_bn : (g.vec.bytes != []) = false := bne_eq_false_iff_eq.mpr hbk
      apply SepWPp.of_sepWP (mid := (blkPl_86).base + bv% (580))
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hU]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all) (by simp_all [bytesField])
        (by simp_all [SessLenCalleeSaved])
    · have hbk_b : (g.vec.bytes == []) = false := beq_eq_false_iff_ne.mpr hbk
      have hbk_bn : (g.vec.bytes != []) = true := bne_iff_ne.mpr hbk
      have henc2 := bv_bytesField_nonempty_length (t := 2) hbk rfl
      apply SepWPp.of_sepWP (mid := (blkPl_86).base + bv% (580))
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hU]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all [SessLenCalleeSaved])

theorem step_sessLen_pending_b_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (ss : BitVec 64) (g : TailVecGhost) (p : PendingPreKey) (s1_7 : Nat)
    (hfit : s1_7 + (lenField 9 (encPendingMem g p)).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_86).base + 580#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ss)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1_7)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 (optUint32Field 1 p.preKeyId).length)
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 (bytesField 2 g.vec.bytes).length)
    (hP : P = pendingUnpacked A (ss + 248#64) (some g) (some p) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_86).base + 700#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = ss →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s1_7 + (lenField 9 (encPendingMem g p)).length) →
      SessLenCalleeSaved s sm →
      SepWPp (lsProg_86 H) ret sm P Q Qp) :
    SepWPp (lsProg_86 H) ret s P Q Qp := by
  have henc_outer := bv_lenField_length (t := 9) (bs := encPendingMem g p) rfl
  have hcc_ult := ult_ofNat_add_of_lt hfit
  have hadd := bv_add_ofNat_comm s1_7 (lenField 9 (encPendingMem g p)).length
  subst hP
  have hU := pendingUnpacked_some_ss A ss g p
  rw [hU]
  by_cases hspk : p.signedPreKeyId = 0#32
  · have hspk_b : (p.signedPreKeyId == 0#32) = true := beq_iff_eq.mpr hspk
    by_cases hts : p.timestamp = 0#64
    · have hts_b : (p.timestamp == 0#64) = true := beq_iff_eq.mpr hts
      have hts_bn : (p.timestamp != 0#64) = false := bne_eq_false_iff_eq.mpr hts
      have hsum : BitVec.ofNat 64 (bytesField 2 g.vec.bytes).length +
          BitVec.ofNat 64 (optUint32Field 1 p.preKeyId).length =
          BitVec.ofNat 64 (encPendingMem g p).length := by
        rw [encPendingMem_length]
        have h3 : (int32Field 3 p.signedPreKeyId).length = 0 := by simp [int32Field, hspk]
        have h4 : (uint64Field 4 p.timestamp).length = 0 := by simp [uint64Field, hts]
        rw [h3, h4, ← BitVec.ofNat_add]; congr 1; omega
      apply SepWPp.of_sepWP (mid := (blkPl_86).base + bv% (700))
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hU]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [SessLenCalleeSaved])
    · have hts_b : (p.timestamp == 0#64) = false := beq_eq_false_iff_ne.mpr hts
      have hts_bn : (p.timestamp != 0#64) = true := bne_iff_ne.mpr hts
      have henc4 := bv_uint64Field_nonzero_length (t := 4) hts rfl
      have hsum : BitVec.ofNat 64 (bytesField 2 g.vec.bytes).length +
          BitVec.ofNat 64 (optUint32Field 1 p.preKeyId).length +
          BitVec.ofNat 64 (uint64Field 4 p.timestamp).length =
          BitVec.ofNat 64 (encPendingMem g p).length := by
        rw [encPendingMem_length]
        have h3 : (int32Field 3 p.signedPreKeyId).length = 0 := by simp [int32Field, hspk]
        rw [h3]; simp only [← BitVec.ofNat_add]; congr 1; omega
      apply SepWPp.of_sepWP (mid := (blkPl_86).base + bv% (700))
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hU]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [SessLenCalleeSaved])
  · have hspk_b : (p.signedPreKeyId == 0#32) = false := beq_eq_false_iff_ne.mpr hspk
    have henc3 := bv_int32Field_nonzero_length (t := 3) hspk rfl
    by_cases hts : p.timestamp = 0#64
    · have hts_b : (p.timestamp == 0#64) = true := beq_iff_eq.mpr hts
      have hts_bn : (p.timestamp != 0#64) = false := bne_eq_false_iff_eq.mpr hts
      have hsum : BitVec.ofNat 64 (bytesField 2 g.vec.bytes).length +
          BitVec.ofNat 64 (optUint32Field 1 p.preKeyId).length +
          BitVec.ofNat 64 (int32Field 3 p.signedPreKeyId).length =
          BitVec.ofNat 64 (encPendingMem g p).length := by
        rw [encPendingMem_length]
        have h4 : (uint64Field 4 p.timestamp).length = 0 := by simp [uint64Field, hts]
        rw [h4]; simp only [← BitVec.ofNat_add]; congr 1; omega
      apply SepWPp.of_sepWP (mid := (blkPl_86).base + bv% (700))
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hU]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [SessLenCalleeSaved])
    · have hts_b : (p.timestamp == 0#64) = false := beq_eq_false_iff_ne.mpr hts
      have hts_bn : (p.timestamp != 0#64) = true := bne_iff_ne.mpr hts
      have henc4 := bv_uint64Field_nonzero_length (t := 4) hts rfl
      apply SepWPp.of_sepWP (mid := (blkPl_86).base + bv% (700))
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hU]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [SessLenCalleeSaved])

theorem step_sessLen_f7_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (ss : BitVec 64) (G : SessionGhost) (m : Session (List (BitVec 8))) (s1_7 : Nat)
    (hrel : PendingRel G.pending m.pendingPreKey)
    (hfit : s1_7 + (encPendingFieldMem G.pending m.pendingPreKey).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_86).base + 444#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ss)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1_7)
    (hP : P = pendingUnpacked A (ss + 248#64) G.pending m.pendingPreKey ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_86).base + 700#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = ss →
      sm.readReg64 .x8 = BitVec.ofNat 64
        (s1_7 + (encPendingFieldMem G.pending m.pendingPreKey).length) →
      SessLenCalleeSaved s sm →
      SepWPp (lsProg_86 H) ret sm P Q Qp) :
    SepWPp (lsProg_86 H) ret s P Q Qp := by
  cases hgp : G.pending with
  | none =>
    cases hmp : m.pendingPreKey with
    | none =>
      have hP0 : P = ((ss + 248#64) ↦₆₄ noneCap) ∗ (memRegion (ss + 248#64 + 8#64) 40 ∗ F) := by
        rw [hP, hgp, hmp]; dsimp only [pendingUnpacked]; ac_rfl
      rw [hP0]
      apply SepWPp.of_sepWP (mid := (blkPl_86).base + bv% (700))
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hP0]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all [encPendingFieldMem]) (by simp_all [SessLenCalleeSaved])
    | some _ =>
      rw [hgp, hmp] at hrel; exact hrel.elim
  | some g =>
    cases hmp : m.pendingPreKey with
    | none =>
      rw [hgp, hmp] at hrel; exact hrel.elim
    | some p =>
      have hP' : P = pendingUnpacked A (ss + 248#64) (some g) (some p) ∗ F := by
        rw [hP, hgp, hmp]
      simp only [hgp, hmp, encPendingFieldMem] at hfit
      have hbk_fit : (bytesField 2 g.vec.bytes).length < 2 ^ 64 := by
        have := lenField_length (t := 9) (encPendingMem g p) rfl
        have := encPendingMem_length g p
        omega
      refine step_sessLen_pending_a_placed A H ss g p hbk_fit hpc hrun hx19 hP' ?_
      intro s1 hpc1 hrun1 hsp1 htr1 hx19_1 hx8_1 hx9_1 hx10_1 hcs1
      refine step_sessLen_pending_b_placed A H ss g p s1_7 hfit
        hpc1 hrun1 hx19_1 (hx8_1.trans hx8) hx9_1 hx10_1 hP' ?_
      intro s2 hpc2 hrun2 hsp2 htr2 hx19_2 hx8_2 hcs2
      refine hnext s2 hpc2 hrun2 (hsp2.trans hsp1) (htr2.trans htr1) hx19_2 ?_ (hcs1.trans hcs2)
      simpa only [hgp, hmp, encPendingFieldMem] using hx8_2

theorem step_sessLen_f8_placed [LibsignalPlacement]
    (H : String → Option (State → State))
    (ss : BitVec 64) (m : Session (List (BitVec 8))) (s1_8 : Nat)
    (hfit : s1_8 + (uint32Field 10 m.remoteRegistrationId).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_86).base + 700#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ss)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1_8)
    (hP : P = tags10to15Cells ss m ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_86).base + 756#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = ss →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s1_8 + (uint32Field 10 m.remoteRegistrationId).length) →
      SessLenCalleeSaved s sm →
      SepWPp (lsProg_86 H) ret sm P Q Qp) :
    SepWPp (lsProg_86 H) ret s P Q Qp := by
  subst hP
  have hT : tags10to15Cells ss m =
      ((ss + 112#64) ↦₆₄ BitVec.ofNat 64 m.aliceBaseKey.length) ∗
      ((ss + 136#64) ↦₆₄ BitVec.ofNat 64 m.state.pqRatchetState.length) ∗
      ((ss + 336#64) ↦₃₂ m.remoteRegistrationId) ∗
      ((ss + 340#64) ↦₃₂ m.localRegistrationId) := rfl
  rw [hT]
  by_cases hrem : m.remoteRegistrationId = 0#32
  · have hrem_b : (m.remoteRegistrationId == 0#32) = true := beq_iff_eq.mpr hrem
    apply SepWPp.of_sepWP (mid := (blkPl_86).base + bv% (756))
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hT]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all [uint32Field]) (by simp_all [SessLenCalleeSaved])
  · have hrem_b : (m.remoteRegistrationId == 0#32) = false := beq_eq_false_iff_ne.mpr hrem
    have henc := bv_uint32Field_nonzero_length (t := 10) hrem rfl
    have hcc := ule_ofNat_add_of_lt hfit
    have hcc_ult := ult_ofNat_add_of_lt hfit
    have hadd := bv_add_ofNat_comm s1_8 (uint32Field 10 m.remoteRegistrationId).length
    apply SepWPp.of_sepWP (mid := (blkPl_86).base + bv% (756))
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hT]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [SessLenCalleeSaved])

theorem step_sessLen_f9_placed [LibsignalPlacement]
    (H : String → Option (State → State))
    (ss : BitVec 64) (m : Session (List (BitVec 8))) (s1_9 : Nat)
    (hfit : s1_9 + (uint32Field 11 m.localRegistrationId).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_86).base + 756#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ss)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1_9)
    (hP : P = tags10to15Cells ss m ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_86).base + 812#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = ss →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s1_9 + (uint32Field 11 m.localRegistrationId).length) →
      SessLenCalleeSaved s sm →
      SepWPp (lsProg_86 H) ret sm P Q Qp) :
    SepWPp (lsProg_86 H) ret s P Q Qp := by
  subst hP
  have hT : tags10to15Cells ss m =
      ((ss + 112#64) ↦₆₄ BitVec.ofNat 64 m.aliceBaseKey.length) ∗
      ((ss + 136#64) ↦₆₄ BitVec.ofNat 64 m.state.pqRatchetState.length) ∗
      ((ss + 336#64) ↦₃₂ m.remoteRegistrationId) ∗
      ((ss + 340#64) ↦₃₂ m.localRegistrationId) := rfl
  rw [hT]
  by_cases hloc : m.localRegistrationId = 0#32
  · have hloc_b : (m.localRegistrationId == 0#32) = true := beq_iff_eq.mpr hloc
    apply SepWPp.of_sepWP (mid := (blkPl_86).base + bv% (812))
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hT]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all [uint32Field]) (by simp_all [SessLenCalleeSaved])
  · have hloc_b : (m.localRegistrationId == 0#32) = false := beq_eq_false_iff_ne.mpr hloc
    have henc := bv_uint32Field_nonzero_length (t := 11) hloc rfl
    have hcc := ule_ofNat_add_of_lt hfit
    have hcc_ult := ult_ofNat_add_of_lt hfit
    have hadd := bv_add_ofNat_comm s1_9 (uint32Field 11 m.localRegistrationId).length
    apply SepWPp.of_sepWP (mid := (blkPl_86).base + bv% (812))
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hT]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [SessLenCalleeSaved])

theorem step_sessLen_f10_placed [LibsignalPlacement]
    (H : String → Option (State → State))
    (ss : BitVec 64) (m : Session (List (BitVec 8))) (s1_10 : Nat)
    (hfit : s1_10 + (bytesField 13 m.aliceBaseKey).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_86).base + 812#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ss)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1_10)
    (hP : P = tags10to15Cells ss m ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_86).base + 856#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = ss →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s1_10 + (bytesField 13 m.aliceBaseKey).length) →
      SessLenCalleeSaved s sm →
      SepWPp (lsProg_86 H) ret sm P Q Qp) :
    SepWPp (lsProg_86 H) ret s P Q Qp := by
  have halice_fit : (bytesField 13 m.aliceBaseKey).length < 2 ^ 64 := by omega
  have halice_beq := ofNat64_length_beq_zero_of_bytesField_lt halice_fit
  subst hP
  have hT : tags10to15Cells ss m =
      ((ss + 112#64) ↦₆₄ BitVec.ofNat 64 m.aliceBaseKey.length) ∗
      ((ss + 136#64) ↦₆₄ BitVec.ofNat 64 m.state.pqRatchetState.length) ∗
      ((ss + 336#64) ↦₃₂ m.remoteRegistrationId) ∗
      ((ss + 340#64) ↦₃₂ m.localRegistrationId) := rfl
  rw [hT]
  by_cases halice : m.aliceBaseKey = []
  · have halice_b : (m.aliceBaseKey == []) = true := beq_iff_eq.mpr halice
    apply SepWPp.of_sepWP (mid := (blkPl_86).base + bv% (856))
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hT]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all [bytesField]) (by simp_all [SessLenCalleeSaved])
  · have halice_b : (m.aliceBaseKey == []) = false := beq_eq_false_iff_ne.mpr halice
    have henc := bv_bytesField_nonempty_length (t := 13) halice rfl
    have hcc_ult := ult_ofNat_add_of_lt hfit
    have hadd := bv_add_ofNat_comm s1_10 (bytesField 13 m.aliceBaseKey).length
    apply SepWPp.of_sepWP (mid := (blkPl_86).base + bv% (856))
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hT]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [SessLenCalleeSaved])

theorem step_sessLen_kyber_some_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (ss : BitVec 64) (g : TailVecGhost) (k : PendingKyberPreKey) (s1_11 : Nat)
    (hfit : s1_11 + (lenField 14 (encPendingKyber k)).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_86).base + 856#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ss)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1_11)
    (hP : P = kyberUnpacked A (ss + 296#64) (some g) (some k) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_86).base + 992#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = ss →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s1_11 + (lenField 14 (encPendingKyber k)).length) →
      SessLenCalleeSaved s sm →
      SepWPp (lsProg_86 H) ret sm P Q Qp) :
    SepWPp (lsProg_86 H) ret s P Q Qp := by
  intro R hm hL
  have hm_cap : s.mem ⊨ kyberUnpacked A (ss + 296#64) (some g) (some k) ∗ (F ∗ R) := by
    rw [← sepConj_assoc, ← hP]; exact hm
  have hcap_lt : g.vec.cap.toNat < 2 ^ 63 := kyberUnpacked_cap_lt hm_cap
  have hcap_beq : (g.vec.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_false hcap_lt
  clear hm_cap
  revert R hm hL
  change SepWPp (lsProg_86 H) ret s P Q Qp
  have hct_fit : (bytesField 2 k.ciphertext).length < 2 ^ 64 := by
    have := lenField_length (t := 14) (encPendingKyber k) rfl
    have := encPendingKyber_length k
    omega
  have hct_beq := ofNat64_length_beq_zero_of_bytesField_lt hct_fit
  have hct_bne := ofNat64_length_bne_zero_of_bytesField_lt hct_fit
  have henc_outer := bv_lenField_length (t := 14) (bs := encPendingKyber k) rfl
  have hcc := ule_ofNat_add_of_lt hfit
  have hcc_ult := ult_ofNat_add_of_lt hfit
  have hadd := bv_add_ofNat_comm s1_11 (lenField 14 (encPendingKyber k)).length
  subst hP
  have hU := kyberUnpacked_some_ss A ss g k
  rw [hU]
  by_cases hid : k.preKeyId = 0#32
  · have hid_b : (k.preKeyId == 0#32) = true := beq_iff_eq.mpr hid
    by_cases hct : k.ciphertext = []
    · have hct_b : (k.ciphertext == []) = true := beq_iff_eq.mpr hct
      have hct_bn : (k.ciphertext != []) = false := bne_eq_false_iff_eq.mpr hct
      have h0 : (encPendingKyber k).length = 0 := by
        simp [encPendingKyber, uint32Field, hid, bytesField, hct]
      have hlen14 : (lenField 14 (encPendingKyber k)).length = 2 := by
        rw [lenField_length (t := 14) (encPendingKyber k) rfl, h0]; rfl
      apply SepWPp.of_sepWP (mid := (blkPl_86).base + bv% (992))
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hU]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [SessLenCalleeSaved])
    · have hct_b : (k.ciphertext == []) = false := beq_eq_false_iff_ne.mpr hct
      have hct_bn : (k.ciphertext != []) = true := bne_iff_ne.mpr hct
      have henc2 := bv_bytesField_nonempty_length (t := 2) hct rfl
      have hsum : BitVec.ofNat 64 (bytesField 2 k.ciphertext).length =
          BitVec.ofNat 64 (encPendingKyber k).length := by
        rw [encPendingKyber_length]
        have hid0 : (uint32Field 1 k.preKeyId).length = 0 := by simp [uint32Field, hid]
        rw [hid0, Nat.zero_add]
      apply SepWPp.of_sepWP (mid := (blkPl_86).base + bv% (992))
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hU]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [SessLenCalleeSaved])
  · have hid_b : (k.preKeyId == 0#32) = false := beq_eq_false_iff_ne.mpr hid
    have henc1 := bv_uint32Field_nonzero_length (t := 1) hid rfl
    by_cases hct : k.ciphertext = []
    · have hct_b : (k.ciphertext == []) = true := beq_iff_eq.mpr hct
      have hct_bn : (k.ciphertext != []) = false := bne_eq_false_iff_eq.mpr hct
      have hsum : BitVec.ofNat 64 (uint32Field 1 k.preKeyId).length =
          BitVec.ofNat 64 (encPendingKyber k).length := by
        rw [encPendingKyber_length]
        have hct0 : (bytesField 2 k.ciphertext).length = 0 := by simp [bytesField, hct]
        rw [hct0, Nat.add_zero]
      apply SepWPp.of_sepWP (mid := (blkPl_86).base + bv% (992))
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hU]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [SessLenCalleeSaved])
    · have hct_b : (k.ciphertext == []) = false := beq_eq_false_iff_ne.mpr hct
      have hct_bn : (k.ciphertext != []) = true := bne_iff_ne.mpr hct
      have henc2 := bv_bytesField_nonempty_length (t := 2) hct rfl
      apply SepWPp.of_sepWP (mid := (blkPl_86).base + bv% (992))
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hU]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [SessLenCalleeSaved])

theorem step_sessLen_f11_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (ss : BitVec 64) (G : SessionGhost) (m : Session (List (BitVec 8))) (s1_11 : Nat)
    (hrel : KyberRel G.kyber m.pendingKyberPreKey)
    (hfit : s1_11 + (msgField 14 (m.pendingKyberPreKey.map encPendingKyber)).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_86).base + 856#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ss)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1_11)
    (hP : P = kyberUnpacked A (ss + 296#64) G.kyber m.pendingKyberPreKey ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_86).base + 992#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = ss →
      sm.readReg64 .x8 = BitVec.ofNat 64
        (s1_11 + (msgField 14 (m.pendingKyberPreKey.map encPendingKyber)).length) →
      SessLenCalleeSaved s sm →
      SepWPp (lsProg_86 H) ret sm P Q Qp) :
    SepWPp (lsProg_86 H) ret s P Q Qp := by
  cases hgk : G.kyber with
  | none =>
    cases hmk : m.pendingKyberPreKey with
    | none =>
      have hP0 : P = ((ss + 296#64) ↦₆₄ noneCap) ∗ (memRegion (ss + 296#64 + 8#64) 24 ∗ F) := by
        rw [hP, hgk, hmk]; dsimp only [kyberUnpacked]; ac_rfl
      rw [hP0]
      apply SepWPp.of_sepWP (mid := (blkPl_86).base + bv% (992))
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hP0]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all [msgField]) (by simp_all [SessLenCalleeSaved])
    | some _ =>
      rw [hgk, hmk] at hrel; exact hrel.elim
  | some g =>
    cases hmk : m.pendingKyberPreKey with
    | none =>
      rw [hgk, hmk] at hrel; exact hrel.elim
    | some k =>
      have hP' : P = kyberUnpacked A (ss + 296#64) (some g) (some k) ∗ F := by
        rw [hP, hgk, hmk]
      simp only [hmk, Option.map_some, msgField] at hfit
      refine step_sessLen_kyber_some_placed A H ss g k s1_11 hfit hpc hrun hx19 hx8 hP' ?_
      intro s1 hpc1 hrun1 hsp1 htr1 hx19_1 hx8_1 hcs1
      refine hnext s1 hpc1 hrun1 hsp1 htr1 hx19_1 ?_ hcs1
      simpa only [hmk, Option.map_some, msgField] using hx8_1

theorem step_sessLen_f12_placed [LibsignalPlacement]
    (H : String → Option (State → State))
    (ss sp0 : BitVec 64) (m : Session (List (BitVec 8))) (s1_12 : Nat)
    (hfit : s1_12 + (bytesField 15 m.state.pqRatchetState).length < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_86).base + 992#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 64#64)
    (halign : (sp0 &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = ss)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1_12)
    (hcs : SessLenCalleeSaved s0 s)
    (hP : P = (tags10to15Cells ss m ∗
      frameCells sp0 (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x24) (s0.readReg64 .x23)
        (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp0 →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (s1_12 + (bytesField 15 m.state.pqRatchetState).length) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPp (lsProg_86 H) (s0.readReg64 .lr) s P Q Qp := by
  rcases hcs with ⟨h25, h26, h27, h28, hvregs⟩
  have hpq_fit : (bytesField 15 m.state.pqRatchetState).length < 2 ^ 64 := by omega
  have hpq_beq := ofNat64_length_beq_zero_of_bytesField_lt hpq_fit
  subst hP
  have hT : tags10to15Cells ss m =
      ((ss + 112#64) ↦₆₄ BitVec.ofNat 64 m.aliceBaseKey.length) ∗
      ((ss + 136#64) ↦₆₄ BitVec.ofNat 64 m.state.pqRatchetState.length) ∗
      ((ss + 336#64) ↦₃₂ m.remoteRegistrationId) ∗
      ((ss + 340#64) ↦₃₂ m.localRegistrationId) := rfl
  have hFr : frameCells sp0 (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x24) (s0.readReg64 .x23)
        (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19) =
      ((sp0 - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp0 - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp0 - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((sp0 - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
      ((sp0 - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp0 - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((sp0 - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp0 - 8#64) ↦₆₄ s0.readReg64 .x19) := rfl
  rw [hT, hFr]
  by_cases hpq : m.state.pqRatchetState = []
  · have hpq_b : (m.state.pqRatchetState == []) = true := beq_iff_eq.mpr hpq
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hT, ← hFr]
    apply SepWPp.done (by simp_all) (by simp_all)
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all [bytesField]) (by simp_all [CalleeSavedPreserved])
  · have hpq_b : (m.state.pqRatchetState == []) = false := beq_eq_false_iff_ne.mpr hpq
    have henc := bv_bytesField_nonempty_length (t := 15) hpq rfl
    have hcc_ult := ult_ofNat_add_of_lt hfit
    have hadd := bv_add_ofNat_comm s1_12 (bytesField 15 m.state.pqRatchetState).length
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hT, ← hFr]
    apply SepWPp.done (by simp_all) (by simp_all)
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all [CalleeSavedPreserved])

end Placed

end CryptoVerification.E2E.Record.Serialization.SessionLenAux
