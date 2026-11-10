/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionLenAux.StepsFront
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.E2E.Record.Serialization.ChainLenAux.Pure
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionLen
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionLenAux.Decode
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionLenAux.StepsBack
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerializeLenExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SessionLenStepsFrontExt
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.HooksX
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `<SessionStructure as prost::Message>::encoded_len` (`0x25fd0`)

Verifies protobuf tags 9–15 and the epilogue, and assembles the full subroutine contract of
`<SessionStructure as prost::Message>::encoded_len` (`0x25fd0`, Block `86`) against `sessionLenSpec`
on `SP2Ext` and under relocatable `[LibsignalPlacement]`.
-/

namespace CryptoVerification.E2E.Record.Serialization.SessionLenAux

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.E2E.Record CryptoVerification.E2E.Record.Serialization
open Proofs.libsignal.Hooks2

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
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
  add_neg440_eq_624
  add_neg416_eq_652
  add_neg164_eq_912
  add_neg140_eq_940
  truncate32_signExtend64
  bv_encPendingMem_sum
  bv_encPendingKyber_sum

/-! ## Tag 9 (`pending_pre_key` at `ss + 248`, `444..700` and `1056..1072`) -/

/-- `Some` branch first half (`+444..+580`): subfields 1 (`preKeyId`) and 2 (`baseKey`). -/
theorem step_sessLen_pending_a_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (ss : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (hbk_fit : (bytesField 2 g.vec.bytes).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext b ext).fnAddr sessionLenName + 444#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ss)
    (hP : P = pendingUnpacked A (ss + 248#64) (some g) (some p) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (SP2Ext b ext).fnAddr sessionLenName + 580#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = ss →
      sm.readReg64 .x8 = s.readReg64 .x8 →
      sm.readReg64 .x9 = BitVec.ofNat 64 (optUint32Field 1 p.preKeyId).length →
      sm.readReg64 .x10 = BitVec.ofNat 64 (bytesField 2 g.vec.bytes).length →
      SessLenCalleeSaved s sm →
      SepWPp (SP2Ext b ext) ret sm P Q Qp) :
    SepWPp (SP2Ext b ext) ret s P Q Qp := by
  intro R hm hL
  have hm_cap : s.mem ⊨ pendingUnpacked A (ss + 248#64) (some g) (some p) ∗ (F ∗ R) := by
    rw [← sepConj_assoc, ← hP]; exact hm
  have hcap_lt : g.vec.cap.toNat < 2 ^ 63 := pendingUnpacked_cap_lt hm_cap
  have hcap_beq : (g.vec.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_false hcap_lt
  clear hm_cap
  revert R hm hL
  change SepWPp (SP2Ext b ext) ret s P Q Qp
  sesslen_fetches b (Rust.withPanics ext) 444 512
  sesslen_fetches b (Rust.withPanics ext) 540 580
  generalize_entry (SP2Ext b ext).fnAddr sessionLenName = entry
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
        RustHeap.vecU8Buf A g.vec.cap g.vec.ptr g.vec.bytes) ∗ F := by
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
        RustHeap.vecU8Buf A g.vec.cap g.vec.ptr g.vec.bytes) ∗ F := by
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

/-- `Some` branch second half (`+580..+700` and `+1056..+1072`): subfields 3 (`signedPreKeyId`)
and 4 (`timestamp`) plus outer Tag 9 length accumulation. -/
theorem step_sessLen_pending_b_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (ss : BitVec 64) (g : TailVecGhost) (p : PendingPreKey) (s1_7 : Nat)
    (hfit : s1_7 + (lenField 9 (encPendingMem g p)).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext b ext).fnAddr sessionLenName + 580#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ss)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1_7)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 (optUint32Field 1 p.preKeyId).length)
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 (bytesField 2 g.vec.bytes).length)
    (hP : P = pendingUnpacked A (ss + 248#64) (some g) (some p) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (SP2Ext b ext).fnAddr sessionLenName + 700#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = ss →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s1_7 + (lenField 9 (encPendingMem g p)).length) →
      SessLenCalleeSaved s sm →
      SepWPp (SP2Ext b ext) ret sm P Q Qp) :
    SepWPp (SP2Ext b ext) ret s P Q Qp := by
  sesslen_fetches b (Rust.withPanics ext) 580 700
  sesslen_fetches b (Rust.withPanics ext) 1056 1072
  generalize_entry (SP2Ext b ext).fnAddr sessionLenName = entry
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

/-- Combined Tag 9 (`pending_pre_key` at `ss + 248`, `444..700`). -/
theorem step_sessLen_f7_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (ss : BitVec 64) (G : SessionGhost) (m : Session (List (BitVec 8))) (s1_7 : Nat)
    (hrel : PendingRel G.pending m.pendingPreKey)
    (hfit : s1_7 + (encPendingFieldMem G.pending m.pendingPreKey).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext b ext).fnAddr sessionLenName + 444#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ss)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1_7)
    (hP : P = pendingUnpacked A (ss + 248#64) G.pending m.pendingPreKey ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (SP2Ext b ext).fnAddr sessionLenName + 700#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = ss →
      sm.readReg64 .x8 = BitVec.ofNat 64
        (s1_7 + (encPendingFieldMem G.pending m.pendingPreKey).length) →
      SessLenCalleeSaved s sm →
      SepWPp (SP2Ext b ext) ret sm P Q Qp) :
    SepWPp (SP2Ext b ext) ret s P Q Qp := by
  cases hgp : G.pending with
  | none =>
    cases hmp : m.pendingPreKey with
    | none =>
      sesslen_fetches b (Rust.withPanics ext) 444 456
      sesslen_fetches b (Rust.withPanics ext) 532 540
      sesslen_fetches b (Rust.withPanics ext) 692 700
      generalize_entry (SP2Ext b ext).fnAddr sessionLenName = entry
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
      refine step_sessLen_pending_a_ext b A ext ss g p hbk_fit hpc hrun hx19 hP' ?_
      intro s1 hpc1 hrun1 hsp1 htr1 hx19_1 hx8_1 hx9_1 hx10_1 hcs1
      refine step_sessLen_pending_b_ext b A ext ss g p s1_7 hfit
        hpc1 hrun1 hx19_1 (hx8_1.trans hx8) hx9_1 hx10_1 hP' ?_
      intro s2 hpc2 hrun2 hsp2 htr2 hx19_2 hx8_2 hcs2
      refine hnext s2 hpc2 hrun2 (hsp2.trans hsp1) (htr2.trans htr1) hx19_2 ?_ (hcs1.trans hcs2)
      simpa only [hgp, hmp, encPendingFieldMem] using hx8_2

/-! ## Tag 10 (`remote_registration_id` at `ss + 336`, `700..756`) -/

theorem step_sessLen_f8_ext (b : BitVec 64)
    (ext : String → Option (State → State))
    (ss : BitVec 64) (m : Session (List (BitVec 8))) (s1_8 : Nat)
    (hfit : s1_8 + (uint32Field 10 m.remoteRegistrationId).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext b ext).fnAddr sessionLenName + 700#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ss)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1_8)
    (hP : P = tags10to15Cells ss m ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (SP2Ext b ext).fnAddr sessionLenName + 756#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = ss →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s1_8 + (uint32Field 10 m.remoteRegistrationId).length) →
      SessLenCalleeSaved s sm →
      SepWPp (SP2Ext b ext) ret sm P Q Qp) :
    SepWPp (SP2Ext b ext) ret s P Q Qp := by
  sesslen_fetches b (Rust.withPanics ext) 700 756
  generalize_entry (SP2Ext b ext).fnAddr sessionLenName = entry
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

/-! ## Tag 11 (`local_registration_id` at `ss + 340`, `756..812`) -/

theorem step_sessLen_f9_ext (b : BitVec 64)
    (ext : String → Option (State → State))
    (ss : BitVec 64) (m : Session (List (BitVec 8))) (s1_9 : Nat)
    (hfit : s1_9 + (uint32Field 11 m.localRegistrationId).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext b ext).fnAddr sessionLenName + 756#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ss)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1_9)
    (hP : P = tags10to15Cells ss m ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (SP2Ext b ext).fnAddr sessionLenName + 812#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = ss →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s1_9 + (uint32Field 11 m.localRegistrationId).length) →
      SessLenCalleeSaved s sm →
      SepWPp (SP2Ext b ext) ret sm P Q Qp) :
    SepWPp (SP2Ext b ext) ret s P Q Qp := by
  sesslen_fetches b (Rust.withPanics ext) 756 812
  generalize_entry (SP2Ext b ext).fnAddr sessionLenName = entry
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

/-! ## Tag 13 (`alice_base_key` at `ss + 112`, `812..856`) -/

theorem step_sessLen_f10_ext (b : BitVec 64)
    (ext : String → Option (State → State))
    (ss : BitVec 64) (m : Session (List (BitVec 8))) (s1_10 : Nat)
    (hfit : s1_10 + (bytesField 13 m.aliceBaseKey).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext b ext).fnAddr sessionLenName + 812#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ss)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1_10)
    (hP : P = tags10to15Cells ss m ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (SP2Ext b ext).fnAddr sessionLenName + 856#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = ss →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s1_10 + (bytesField 13 m.aliceBaseKey).length) →
      SessLenCalleeSaved s sm →
      SepWPp (SP2Ext b ext) ret sm P Q Qp) :
    SepWPp (SP2Ext b ext) ret s P Q Qp := by
  sesslen_fetches b (Rust.withPanics ext) 812 856
  generalize_entry (SP2Ext b ext).fnAddr sessionLenName = entry
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

/-! ## Tag 14 (`pending_kyber_pre_key` at `ss + 296`, `856..992` and `1072..1084`) -/

theorem step_sessLen_kyber_some_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (ss : BitVec 64) (g : TailVecGhost) (k : PendingKyberPreKey) (s1_11 : Nat)
    (hfit : s1_11 + (lenField 14 (encPendingKyber k)).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext b ext).fnAddr sessionLenName + 856#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ss)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1_11)
    (hP : P = kyberUnpacked A (ss + 296#64) (some g) (some k) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (SP2Ext b ext).fnAddr sessionLenName + 992#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = ss →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s1_11 + (lenField 14 (encPendingKyber k)).length) →
      SessLenCalleeSaved s sm →
      SepWPp (SP2Ext b ext) ret sm P Q Qp) :
    SepWPp (SP2Ext b ext) ret s P Q Qp := by
  intro R hm hL
  have hm_cap : s.mem ⊨ kyberUnpacked A (ss + 296#64) (some g) (some k) ∗ (F ∗ R) := by
    rw [← sepConj_assoc, ← hP]; exact hm
  have hcap_lt : g.vec.cap.toNat < 2 ^ 63 := kyberUnpacked_cap_lt hm_cap
  have hcap_beq : (g.vec.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_false hcap_lt
  clear hm_cap
  revert R hm hL
  change SepWPp (SP2Ext b ext) ret s P Q Qp
  sesslen_fetches b (Rust.withPanics ext) 856 984
  sesslen_fetches b (Rust.withPanics ext) 1072 1084
  generalize_entry (SP2Ext b ext).fnAddr sessionLenName = entry
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

/-- Combined Tag 14 (`pending_kyber_pre_key` at `ss + 296`, `856..992`). -/
theorem step_sessLen_f11_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (ss : BitVec 64) (G : SessionGhost) (m : Session (List (BitVec 8))) (s1_11 : Nat)
    (hrel : KyberRel G.kyber m.pendingKyberPreKey)
    (hfit : s1_11 + (msgField 14 (m.pendingKyberPreKey.map encPendingKyber)).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext b ext).fnAddr sessionLenName + 856#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ss)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1_11)
    (hP : P = kyberUnpacked A (ss + 296#64) G.kyber m.pendingKyberPreKey ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (SP2Ext b ext).fnAddr sessionLenName + 992#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = ss →
      sm.readReg64 .x8 = BitVec.ofNat 64
        (s1_11 + (msgField 14 (m.pendingKyberPreKey.map encPendingKyber)).length) →
      SessLenCalleeSaved s sm →
      SepWPp (SP2Ext b ext) ret sm P Q Qp) :
    SepWPp (SP2Ext b ext) ret s P Q Qp := by
  cases hgk : G.kyber with
  | none =>
    cases hmk : m.pendingKyberPreKey with
    | none =>
      sesslen_fetches b (Rust.withPanics ext) 856 868
      sesslen_fetches b (Rust.withPanics ext) 984 992
      generalize_entry (SP2Ext b ext).fnAddr sessionLenName = entry
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
      refine step_sessLen_kyber_some_ext b A ext ss g k s1_11 hfit hpc hrun hx19 hx8 hP' ?_
      intro s1 hpc1 hrun1 hsp1 htr1 hx19_1 hx8_1 hcs1
      refine hnext s1 hpc1 hrun1 hsp1 htr1 hx19_1 ?_ hcs1
      simpa only [hmk, Option.map_some, msgField] using hx8_1

/-! ## Tag 15 (`pq_ratchet_state` at `ss + 136`) and epilogue (`992..1056`) -/

theorem step_sessLen_f12_ext (b : BitVec 64)
    (ext : String → Option (State → State))
    (ss sp0 : BitVec 64) (m : Session (List (BitVec 8))) (s1_12 : Nat)
    (hfit : s1_12 + (bytesField 15 m.state.pqRatchetState).length < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext b ext).fnAddr sessionLenName + 992#64)
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
    SepWPp (SP2Ext b ext) (s0.readReg64 .lr) s P Q Qp := by
  sesslen_fetches b (Rust.withPanics ext) 992 1056
  generalize_entry (SP2Ext b ext).fnAddr sessionLenName = entry
  examples_hide_fetches
  rcases hcs with ⟨h25, h26, h27, h28⟩
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

end CryptoVerification.E2E.Record.Serialization.SessionLenAux

namespace CryptoVerification.E2E.Record.Serialization

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Record.Serialization.SessionLenAux
open Proofs.libsignal.Hooks2

private def pendingTailLen (opt : Option TailVecGhost) : Prop :=
  match opt with | none => True | some g => g.tail.length = 24

private def kyberTailLen (opt : Option TailVecGhost) : Prop :=
  match opt with | none => True | some g => g.tail.length = 8

private def tailLensPure (G : SessionGhost) : SepProp :=
  ⌜pendingTailLen G.pending⌝ ∗ ⌜kyberTailLen G.kyber⌝

private theorem optTailVecAt_pending_eq' (A : RustAlloc) (a : BitVec 64)
    (opt : Option TailVecGhost) (m : Option PendingPreKey) :
    PendingRel opt m →
    optTailVecAt A 48 a opt = ⌜pendingTailLen opt⌝ ∗ pendingUnpacked A a opt m := by
  intro hrel
  rw [optTailVecAt_pending_eq A a opt m hrel]
  cases opt <;> rfl

private theorem optTailVecAt_kyber_eq' (A : RustAlloc) (a : BitVec 64)
    (opt : Option TailVecGhost) (m : Option PendingKyberPreKey) :
    KyberRel opt m →
    optTailVecAt A 32 a opt = ⌜kyberTailLen opt⌝ ∗ kyberUnpacked A a opt m := by
  intro hrel
  rw [optTailVecAt_kyber_eq A a opt m hrel]
  cases opt <;> rfl

/-- Fully unpacked heap body of `sessionStateAt` with `pendingUnpacked` and `kyberUnpacked`. -/
private def sessionFullUnpacked (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (s : Session (List (BitVec 8))) : SepProp :=
  tags1to5Cells ss G s ∗
  optSenderChainAt A (ss + 144#64) G.sender s.state.senderChain ∗
  (((ss + 80#64) ↦₆₄ G.chainsPtr) ∗
   ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 (G.chains.zip s.state.receiverChains).length) ∗
   vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr (G.chains.zip s.state.receiverChains)) ∗
  pendingUnpacked A (ss + 248#64) G.pending s.pendingPreKey ∗
  tags10to15Cells ss s ∗
  kyberUnpacked A (ss + 296#64) G.kyber s.pendingKyberPreKey ∗
  sessionUnused A ss G s ∗
  tailLensPure G

private theorem sessionBodyUnpacked_eq (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (s : Session (List (BitVec 8)))
    (hpending : PendingRel G.pending s.pendingPreKey)
    (hkyber : KyberRel G.kyber s.pendingKyberPreKey) :
    sessionBodyUnpacked A ss G s = sessionFullUnpacked A ss G s := by
  unfold sessionBodyUnpacked sessionFullUnpacked tailLensPure
  rw [optTailVecAt_pending_eq' A (ss + 248#64) G.pending s.pendingPreKey hpending,
      optTailVecAt_kyber_eq' A (ss + 296#64) G.kyber s.pendingKyberPreKey hkyber]
  ac_rfl

private theorem sp_sub64_aligned {sp : BitVec 64} (h : sp &&& 15#64 = 0#64) :
    ((sp - 64#64) &&& 15#64 == 0#64) = true := by
  have hmod : ∀ x : BitVec 64, (x &&& 15#64).toNat = x.toNat % 16 := fun x => by
    rw [BitVec.toNat_and, show (15#64).toNat = 2 ^ 4 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod]
  have h0 : sp.toNat % 16 = 0 := by
    have := congrArg BitVec.toNat h
    simpa [hmod] using this
  rw [beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  have := sp.isLt
  simp only [hmod, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceSub]
  omega

/-- `SessionStructure::encoded_len` (`0x25fd0`) meets `sessionLenSpec` on `SP2Ext b ext`. -/
theorem sessionLen_ok_ext (A : RustAlloc) (b : BitVec 64)
    (ext : String → Option (State → State)) :
    subroutine_ok (SP2Ext b ext)
      ((SP2Ext b ext).fnAddr sessionLenName)
      (sessionLenSpec A) := by
  have hchain : subroutine_ok (SP2Ext b ext) ((SP2Ext b ext).fnAddr chainLenName) (chainLenSpec A) :=
    chainLen_ok_ext b ext A (msgKeyLen_ok_ext b ext A)
  apply subroutine_ok_of_sepWPp
  intro ⟨ss, G, m⟩ R s0 hpc0 hrun0 hpre hsp0
  have halign0 : s0.sp &&& 15#64 = 0#64 := by
    simp only [State.spAligned, beq_iff_eq] at hsp0; exact hsp0
  have halign0_b : (s0.sp &&& 15#64 == 0#64) = true := hsp0
  dsimp only [sessionLenSpec, sessionStateReprAt, sessionStateAt] at hpre
  rw [stackAt_sessionLen_eq] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨v64, v56, v48, v40, v32, v24, v16, v8, ⟨hx0, hfit⟩,
    ⟨hpending, hkyber, halice, hrem_id, hloc_id⟩,
    ⟨hlik, hrik, hchains, hpendsome, hreg_len, hlik33, hrik33⟩, hpre⟩
  have hbody :
      (vecGhostAt A G.localIk ss ∗ vecGhostAt A G.remoteIk (ss + 0x18#64) ∗
        vecU8At A (ss + 0x30#64) G.root.cap G.root.ptr (HMAC.keyToBytes32 m.state.rootKey) ∗
        vecAt A 104 8 (chainAt A) (ss + 0x48#64) G.chainsCap G.chainsPtr
          (G.chains.zip m.state.receiverChains) ∗
        vecGhostAt A G.alice (ss + 0x60#64) ∗
        vecU8At A (ss + 0x78#64) G.pq.cap G.pq.ptr m.state.pqRatchetState ∗
        optSenderChainAt A (ss + 0x90#64) G.sender m.state.senderChain ∗
        optTailVecAt A 48 (ss + 0xf8#64) G.pending ∗
        optTailVecAt A 32 (ss + 0x128#64) G.kyber ∗
        ((ss + 0x148#64) ↦₃₂ m.state.sessionVersion) ∗ ((ss + 0x14c#64) ↦₃₂ m.state.previousCounter) ∗
        ((ss + 0x150#64) ↦ₛ G.regIds)) =
      sessionFullUnpacked A ss G m := by
    rw [sessionStateAt_body_eq A ss G m halice hreg_len hrem_id hloc_id,
        sessionBodyUnpacked_eq A ss G m hpending hkyber]
  let P0 : SepProp :=
    sessionFullUnpacked A ss G m ∗
    stackAt (s0.sp - 64#64) chainLenStack ∗
    frameCells s0.sp v64 v56 v48 v40 v32 v24 v16 v8 ∗ R
  have hpre' : s0.mem ⊨ P0 := by
    dsimp only [P0]
    rw [← hbody]
    convert hpre using 1; ac_rfl
  have hfit_eq := encSessionMem_length_eq G m
  refine ⟨P0, emp, by rw [sepConj_emp]; exact hpre', ?_⟩
  let FrSave : SepProp :=
    frameCells s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
      (s0.readReg64 .x24) (s0.readReg64 .x23)
      (s0.readReg64 .x22) (s0.readReg64 .x21)
      (s0.readReg64 .x20) (s0.readReg64 .x19)
  let P : SepProp :=
    sessionFullUnpacked A ss G m ∗
    stackAt (s0.sp - 64#64) chainLenStack ∗
    FrSave ∗ R
  have hP0 : P0 = (tags1to5Cells ss G m ∗ frameCells s0.sp v64 v56 v48 v40 v32 v24 v16 v8) ∗
      (optSenderChainAt A (ss + 144#64) G.sender m.state.senderChain ∗
       (((ss + 80#64) ↦₆₄ G.chainsPtr) ∗
        ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 (G.chains.zip m.state.receiverChains).length) ∗
        vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr (G.chains.zip m.state.receiverChains)) ∗
       pendingUnpacked A (ss + 248#64) G.pending m.pendingPreKey ∗
       tags10to15Cells ss m ∗
       kyberUnpacked A (ss + 296#64) G.kyber m.pendingKyberPreKey ∗
       sessionUnused A ss G m ∗ tailLensPure G ∗
       stackAt (s0.sp - 64#64) chainLenStack ∗ R) := by
    dsimp only [P0, sessionFullUnpacked]; ac_rfl
  refine step_sessLen_f1_ext b ext ss s0.sp v64 v56 v48 v40 v32 v24 v16 v8 G m
    (by omega) hpc0 hrun0 rfl halign0 hx0 hP0 ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx19_1 hx8_1 hx9_1 hcs1
  have hP_f1 : ((tags1to5Cells ss G m ∗ FrSave) ∗
      (optSenderChainAt A (ss + 144#64) G.sender m.state.senderChain ∗
       (((ss + 80#64) ↦₆₄ G.chainsPtr) ∗
        ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 (G.chains.zip m.state.receiverChains).length) ∗
        vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr (G.chains.zip m.state.receiverChains)) ∗
       pendingUnpacked A (ss + 248#64) G.pending m.pendingPreKey ∗
       tags10to15Cells ss m ∗
       kyberUnpacked A (ss + 296#64) G.kyber m.pendingKyberPreKey ∗
       sessionUnused A ss G m ∗ tailLensPure G ∗
       stackAt (s0.sp - 64#64) chainLenStack ∗ R)) = P := by
    dsimp only [P, FrSave, sessionFullUnpacked]; ac_rfl
  rw [hP_f1]
  have hP_1to5 : P = tags1to5Cells ss G m ∗
      (optSenderChainAt A (ss + 144#64) G.sender m.state.senderChain ∗
       (((ss + 80#64) ↦₆₄ G.chainsPtr) ∗
        ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 (G.chains.zip m.state.receiverChains).length) ∗
        vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr (G.chains.zip m.state.receiverChains)) ∗
       pendingUnpacked A (ss + 248#64) G.pending m.pendingPreKey ∗
       tags10to15Cells ss m ∗
       kyberUnpacked A (ss + 296#64) G.kyber m.pendingKyberPreKey ∗
       sessionUnused A ss G m ∗ tailLensPure G ∗
       stackAt (s0.sp - 64#64) chainLenStack ∗ FrSave ∗ R) := by
    dsimp only [P, sessionFullUnpacked]; ac_rfl
  refine step_sessLen_f2_ext b ext ss G m
    (uint32Field 1 m.state.sessionVersion).length
    (by omega) hpc1 hrun1 hx19_1 hx8_1 hx9_1 hP_1to5 ?_
  intro s2 hpc2 hrun2 hsp2 htr2 hx19_2 hx8_2 hx9_2 hcs2
  refine step_sessLen_f3_ext b ext ss G m
    ((uint32Field 1 m.state.sessionVersion).length + (bytesField 2 G.localIk.bytes).length)
    (by omega) hpc2 hrun2 hx19_2 hx8_2 hx9_2 hP_1to5 ?_
  intro s3 hpc3 hrun3 hsp3 htr3 hx19_3 hx8_3 hcs3
  refine step_sessLen_f4_ext b ext ss G m
    ((uint32Field 1 m.state.sessionVersion).length + (bytesField 2 G.localIk.bytes).length +
     (bytesField 3 G.remoteIk.bytes).length +
     (bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)).length)
    (by omega) hpc3 hrun3 hx19_3 hx8_3 hP_1to5 ?_
  intro s4 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hcs4
  have hsp4' : s4.sp = s0.sp - 64#64 := by rw [hsp4, hsp3, hsp2, hsp1]
  have hsp4_align : s4.spAligned = true := by
    simp only [State.spAligned, hsp4']
    exact sp_sub64_aligned halign0
  have hP_f5 : P = (optSenderChainAt A (ss + 144#64) G.sender m.state.senderChain ∗
      stackAt s4.sp chainLenStack) ∗
      (tags1to5Cells ss G m ∗
       (((ss + 80#64) ↦₆₄ G.chainsPtr) ∗
        ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 (G.chains.zip m.state.receiverChains).length) ∗
        vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr (G.chains.zip m.state.receiverChains)) ∗
       pendingUnpacked A (ss + 248#64) G.pending m.pendingPreKey ∗
       tags10to15Cells ss m ∗
       kyberUnpacked A (ss + 296#64) G.kyber m.pendingKyberPreKey ∗
       sessionUnused A ss G m ∗ tailLensPure G ∗ FrSave ∗ R) := by
    rw [hsp4']; dsimp only [P, sessionFullUnpacked]; ac_rfl
  refine step_sessLen_f5_ext b A ext hchain ss G m
    ((uint32Field 1 m.state.sessionVersion).length + (bytesField 2 G.localIk.bytes).length +
     (bytesField 3 G.remoteIk.bytes).length +
     (bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)).length +
     (uint32Field 5 m.state.previousCounter).length)
    (by omega) (by omega) hpc4 hrun4 hsp4_align hx19_4 hx20_4 hP_f5 ?_
  intro s5 hpc5 hrun5 hsp5 htr5 hx19_5 hx21_5 hcs5
  have hsp5' : s5.sp = s0.sp - 64#64 := hsp5.trans hsp4'
  have hsp5_align : s5.spAligned = true := by simpa only [State.spAligned, hsp5] using hsp4_align
  have hP_f6 : P = (((ss + 80#64) ↦₆₄ G.chainsPtr) ∗
      ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 (G.chains.zip m.state.receiverChains).length) ∗
      vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr (G.chains.zip m.state.receiverChains) ∗
      stackAt s5.sp chainLenStack) ∗
      (tags1to5Cells ss G m ∗
       optSenderChainAt A (ss + 144#64) G.sender m.state.senderChain ∗
       pendingUnpacked A (ss + 248#64) G.pending m.pendingPreKey ∗
       tags10to15Cells ss m ∗
       kyberUnpacked A (ss + 296#64) G.kyber m.pendingKyberPreKey ∗
       sessionUnused A ss G m ∗ tailLensPure G ∗ FrSave ∗ R) := by
    rw [hsp5']; dsimp only [P, sessionFullUnpacked]; ac_rfl
  refine step_sessLen_f6_ext b A ext hchain ss G m
    ((uint32Field 1 m.state.sessionVersion).length + (bytesField 2 G.localIk.bytes).length +
     (bytesField 3 G.remoteIk.bytes).length +
     (bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)).length +
     (uint32Field 5 m.state.previousCounter).length +
     (encSenderFieldMem G.sender m.state.senderChain).length)
    (by omega) hpc5 hrun5 hsp5_align hx19_5 hx21_5 hP_f6 ?_
  intro s6 hpc6 hrun6 hsp6 htr6 hx19_6 hx8_6 hcs6
  have hP_f7 : P = pendingUnpacked A (ss + 248#64) G.pending m.pendingPreKey ∗
      (tags1to5Cells ss G m ∗
       optSenderChainAt A (ss + 144#64) G.sender m.state.senderChain ∗
       (((ss + 80#64) ↦₆₄ G.chainsPtr) ∗
        ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 (G.chains.zip m.state.receiverChains).length) ∗
        vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr (G.chains.zip m.state.receiverChains)) ∗
       tags10to15Cells ss m ∗
       kyberUnpacked A (ss + 296#64) G.kyber m.pendingKyberPreKey ∗
       sessionUnused A ss G m ∗ tailLensPure G ∗
       stackAt (s0.sp - 64#64) chainLenStack ∗ FrSave ∗ R) := by
    dsimp only [P, sessionFullUnpacked]; ac_rfl
  refine step_sessLen_f7_ext b A ext ss G m
    ((uint32Field 1 m.state.sessionVersion).length + (bytesField 2 G.localIk.bytes).length +
     (bytesField 3 G.remoteIk.bytes).length +
     (bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)).length +
     (uint32Field 5 m.state.previousCounter).length +
     (encSenderFieldMem G.sender m.state.senderChain).length +
     chainsTotalLen (G.chains.zip m.state.receiverChains))
    hpending (by omega) hpc6 hrun6 hx19_6 hx8_6 hP_f7 ?_
  intro s7 hpc7 hrun7 hsp7 htr7 hx19_7 hx8_7 hcs7
  have hP_10to15 : P = tags10to15Cells ss m ∗
      (tags1to5Cells ss G m ∗
       optSenderChainAt A (ss + 144#64) G.sender m.state.senderChain ∗
       (((ss + 80#64) ↦₆₄ G.chainsPtr) ∗
        ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 (G.chains.zip m.state.receiverChains).length) ∗
        vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr (G.chains.zip m.state.receiverChains)) ∗
       pendingUnpacked A (ss + 248#64) G.pending m.pendingPreKey ∗
       kyberUnpacked A (ss + 296#64) G.kyber m.pendingKyberPreKey ∗
       sessionUnused A ss G m ∗ tailLensPure G ∗
       stackAt (s0.sp - 64#64) chainLenStack ∗ FrSave ∗ R) := by
    dsimp only [P, sessionFullUnpacked]; ac_rfl
  refine step_sessLen_f8_ext b ext ss m
    ((uint32Field 1 m.state.sessionVersion).length + (bytesField 2 G.localIk.bytes).length +
     (bytesField 3 G.remoteIk.bytes).length +
     (bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)).length +
     (uint32Field 5 m.state.previousCounter).length +
     (encSenderFieldMem G.sender m.state.senderChain).length +
     chainsTotalLen (G.chains.zip m.state.receiverChains) +
     (encPendingFieldMem G.pending m.pendingPreKey).length)
    (by omega) hpc7 hrun7 hx19_7 hx8_7 hP_10to15 ?_
  intro s8 hpc8 hrun8 hsp8 htr8 hx19_8 hx8_8 hcs8
  refine step_sessLen_f9_ext b ext ss m
    ((uint32Field 1 m.state.sessionVersion).length + (bytesField 2 G.localIk.bytes).length +
     (bytesField 3 G.remoteIk.bytes).length +
     (bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)).length +
     (uint32Field 5 m.state.previousCounter).length +
     (encSenderFieldMem G.sender m.state.senderChain).length +
     chainsTotalLen (G.chains.zip m.state.receiverChains) +
     (encPendingFieldMem G.pending m.pendingPreKey).length +
     (uint32Field 10 m.remoteRegistrationId).length)
    (by omega) hpc8 hrun8 hx19_8 hx8_8 hP_10to15 ?_
  intro s9 hpc9 hrun9 hsp9 htr9 hx19_9 hx8_9 hcs9
  refine step_sessLen_f10_ext b ext ss m
    ((uint32Field 1 m.state.sessionVersion).length + (bytesField 2 G.localIk.bytes).length +
     (bytesField 3 G.remoteIk.bytes).length +
     (bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)).length +
     (uint32Field 5 m.state.previousCounter).length +
     (encSenderFieldMem G.sender m.state.senderChain).length +
     chainsTotalLen (G.chains.zip m.state.receiverChains) +
     (encPendingFieldMem G.pending m.pendingPreKey).length +
     (uint32Field 10 m.remoteRegistrationId).length +
     (uint32Field 11 m.localRegistrationId).length)
    (by omega) hpc9 hrun9 hx19_9 hx8_9 hP_10to15 ?_
  intro s10 hpc10 hrun10 hsp10 htr10 hx19_10 hx8_10 hcs10
  have hP_f11 : P = kyberUnpacked A (ss + 296#64) G.kyber m.pendingKyberPreKey ∗
      (tags1to5Cells ss G m ∗
       optSenderChainAt A (ss + 144#64) G.sender m.state.senderChain ∗
       (((ss + 80#64) ↦₆₄ G.chainsPtr) ∗
        ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 (G.chains.zip m.state.receiverChains).length) ∗
        vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr (G.chains.zip m.state.receiverChains)) ∗
       pendingUnpacked A (ss + 248#64) G.pending m.pendingPreKey ∗
       tags10to15Cells ss m ∗
       sessionUnused A ss G m ∗ tailLensPure G ∗
       stackAt (s0.sp - 64#64) chainLenStack ∗ FrSave ∗ R) := by
    dsimp only [P, sessionFullUnpacked]; ac_rfl
  refine step_sessLen_f11_ext b A ext ss G m
    ((uint32Field 1 m.state.sessionVersion).length + (bytesField 2 G.localIk.bytes).length +
     (bytesField 3 G.remoteIk.bytes).length +
     (bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)).length +
     (uint32Field 5 m.state.previousCounter).length +
     (encSenderFieldMem G.sender m.state.senderChain).length +
     chainsTotalLen (G.chains.zip m.state.receiverChains) +
     (encPendingFieldMem G.pending m.pendingPreKey).length +
     (uint32Field 10 m.remoteRegistrationId).length +
     (uint32Field 11 m.localRegistrationId).length +
     (bytesField 13 m.aliceBaseKey).length)
    hkyber (by omega) hpc10 hrun10 hx19_10 hx8_10 hP_f11 ?_
  intro s11 hpc11 hrun11 hsp11 htr11 hx19_11 hx8_11 hcs11
  have hsp11' : s11.sp = s0.sp - 64#64 := by
    rw [hsp11, hsp10, hsp9, hsp8, hsp7, hsp6, hsp5']
  have hcs11' : SessLenCalleeSaved s0 s11 :=
    hcs1.trans (hcs2.trans (hcs3.trans (hcs4.trans (hcs5.trans
      (hcs6.trans (hcs7.trans (hcs8.trans (hcs9.trans (hcs10.trans hcs11)))))))))
  have hP_f12 : P = (tags10to15Cells ss m ∗ FrSave) ∗
      (tags1to5Cells ss G m ∗
       optSenderChainAt A (ss + 144#64) G.sender m.state.senderChain ∗
       (((ss + 80#64) ↦₆₄ G.chainsPtr) ∗
        ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 (G.chains.zip m.state.receiverChains).length) ∗
        vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr (G.chains.zip m.state.receiverChains)) ∗
       pendingUnpacked A (ss + 248#64) G.pending m.pendingPreKey ∗
       kyberUnpacked A (ss + 296#64) G.kyber m.pendingKyberPreKey ∗
       sessionUnused A ss G m ∗ tailLensPure G ∗
       stackAt (s0.sp - 64#64) chainLenStack ∗ R) := by
    dsimp only [P, FrSave, sessionFullUnpacked]; ac_rfl
  refine step_sessLen_f12_ext b ext ss s0.sp m
    ((uint32Field 1 m.state.sessionVersion).length + (bytesField 2 G.localIk.bytes).length +
     (bytesField 3 G.remoteIk.bytes).length +
     (bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)).length +
     (uint32Field 5 m.state.previousCounter).length +
     (encSenderFieldMem G.sender m.state.senderChain).length +
     chainsTotalLen (G.chains.zip m.state.receiverChains) +
     (encPendingFieldMem G.pending m.pendingPreKey).length +
     (uint32Field 10 m.remoteRegistrationId).length +
     (uint32Field 11 m.localRegistrationId).length +
     (bytesField 13 m.aliceBaseKey).length +
     (msgField 14 (m.pendingKyberPreKey.map encPendingKyber)).length)
    (by omega) hpc11 hrun11 hsp11' halign0_b hx19_11 hx8_11 hcs11' hP_f12 ?_
  intro sf hpcf hrunf hspf htrf hx0_f hcsf
  have htr_all : sf.trace = s0.trace := by
    rw [htrf, htr11, htr10, htr9, htr8, htr7, htr6, htr5, htr4, htr3, htr2, htr1]
  rw [← hfit_eq] at hx0_f
  refine ⟨?_, hspf, hcsf⟩
  intro hm_f
  rw [sepConj_emp] at hm_f
  dsimp only [sessionLenSpec, sessionStateReprAt, sessionStateAt]
  rw [stackAt_sessionLen_eq]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨s0.readReg64 .fp, s0.readReg64 .lr, s0.readReg64 .x24, s0.readReg64 .x23,
    s0.readReg64 .x22, s0.readReg64 .x21, s0.readReg64 .x20, s0.readReg64 .x19,
    ⟨hx0_f, htr_all⟩,
    ⟨hpending, hkyber, halice, hrem_id, hloc_id⟩,
    ⟨hlik, hrik, hchains, hpendsome, hreg_len, hlik33, hrik33⟩, ?_⟩
  have hm_f' : sf.mem ⊨ P := hm_f
  dsimp only [P, FrSave] at hm_f'
  rw [← hbody] at hm_f'
  convert hm_f' using 1; ac_rfl

/-! ## Relocatable `[LibsignalPlacement]` proofs (Block `86`) -/

section Placed

open CryptoVerification.E2E.Record.Placed

/-- Block `86` (`<SessionStructure as prost::Message>::encoded_len`) under `[LibsignalPlacement]`. -/
theorem sessionLen_placed_ok_ext [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) :
    subroutine_ok (lsProg_86 H) (blkPl_86).base
      (withLsCodeLoaded lsmpl (sessionLenSpec A)) :=
  sessionLen_placed_ok A H

theorem sessionLen_placed_ok_cl [LibsignalPlacement] (A : RustAlloc)
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H] :
    subroutine_ok callerProg (lsmpl.base 86)
      (withLsCl lsmpl (sessionLenSpec A)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg) (sessionLen_placed_ok A H)

end Placed

end CryptoVerification.E2E.Record.Serialization
