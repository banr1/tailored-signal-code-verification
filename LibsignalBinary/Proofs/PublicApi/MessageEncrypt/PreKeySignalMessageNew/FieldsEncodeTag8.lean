/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodeTags1To4
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodeDecodes
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodeTags4To7
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodeVarintBase
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

/-!
# `PreKeySignalMessage::new` Tag 8 Encoding and Core Composition

Symbolic execution of protobuf tag 8 (`kyber_ciphertext`, `+0x450..+0x4c4`) and composition of
tags 1–8 from `SeamA` to `SeamB`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncode

set_option maxHeartbeats 400000

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split
open scoped EncodeVarintNorm

@[local simp, local arm64_norm, local wp_norm]
theorem noneCap_add_one_beq_zero : (noneCap + 1#64 == 0#64) = true := by decide

theorem ct_len_add_one_beq_zero_false {n : Nat} (hlt : n < 2 ^ 63) :
    (BitVec.ofNat 64 n + 1#64 == 0#64) = false := by
  apply beq_false_of_ne
  intro h
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
  omega

/-! ## Tag 8 (`kyber_ciphertext`, `+0x450..+0x4c4`) -/

theorem step_preKeyMsg_tag8_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hMc : HookSat ext memcpyName (sessionMemcpySpec allocHookStack))
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64)
    (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 1104#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : s.spAligned = true)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx19 : s.readReg64 .x19 =
      (match x.kp with
       | none => noneCap
       | some k => BitVec.ofNat 64 k.ciphertext.length))
    (hP : P = (((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗
      ((sp + 56#64) ↦₆₄ x.bkA) ∗
      ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix7 x).length) ∗
      vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix7 x) ∗
      optKyberCopyBuf A g.kyberCopyPtr x.kp ∗
      A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ (sm : State) (lenW : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 1220#64 →
      sm.status = .Running →
      sm.sp = sp →
      sm.trace = s.trace →
      sm.readReg64 .x8 = x.bkA →
      sm.readReg64 .x23 = BitVec.ofNat 64 (serPrefix8 x).length →
      sm.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length →
      PreKeyMsgTagRegs s sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗
          ((sp + 56#64) ↦₆₄ x.bkA) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ lenW) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix8 x) ∗
          optKyberCopyBuf A g.kyberCopyPtr x.kp ∗
          A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q Qp := by
  have hf1104 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 1104)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15580
  have hf1108 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 1108)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15584
  have hf1112 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 1112)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15588
  have hf1116 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 1116)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x1558c
  have hf1120 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 1120)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15590
  rcases hwf with ⟨hser_lt, _⟩
  have hcap_toNat : (BitVec.ofNat 64 x.model.serialized.length).toNat = x.model.serialized.length := by
    simp only [BitVec.toNat_ofNat]; omega
  have ⟨h0_len, h01_le, h12_le, h23_le, h34_le, h45_le, h56_le, h67_le, h78_le, h8_len⟩ :=
    serPrefix_lengths_le x
  have hcap_pos : 0 < (BitVec.ofNat 64 x.model.serialized.length).toNat := by omega
  subst hP
  cases hkp : x.kp with
  | none =>
    rw [hkp] at hx19 hnext
    have hser8 : serPrefix8 x = serPrefix7 x := by
      simp [serPrefix8, hkp, LibsignalSessionApi.Prost.bytesField]
    clear h8_len
    revert hpc hnext hf1104 hf1108 hf1112 hf1116 hf1120
    generalize (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName = entry0
    intro hpc hnext hf1104 hf1108 hf1112 hf1116 hf1120
    examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry0 + 1220#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [← hser8]
    exact hnext _ (BitVec.ofNat 64 (serPrefix8 x).length)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by rw [hser8]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self])
  | some k =>
    rw [hkp] at hx19 hnext
    have hct_lt : k.ciphertext.length < 2 ^ 63 := by
      have : k.ciphertext.length ≤ (serPrefix8 x).length := by
        simp [serPrefix8, hkp, LibsignalSessionApi.Prost.bytesField]; omega
      omega
    have hct_lt64 : k.ciphertext.length < 2 ^ 64 := by omega
    have hadd1 := ct_len_add_one_beq_zero_false hct_lt
    have hvar_pos : 1 ≤ (encodeVarint (BitVec.ofNat 64 k.ciphertext.length)).length := by
      unfold encodeVarint encodeVarintAux; split <;> simp
    have hser8 : (serPrefix7 x ++ 66#8 :: encodeVarint (BitVec.ofNat 64 k.ciphertext.length)) ++
        k.ciphertext = serPrefix8 x := by
      rw [serPrefix8, hkp, Option.map_some, prost_bytesField_some 8 k.ciphertext hct_lt64, prost_key_8_2]
      simp only [← List.append_assoc, List.singleton_append]
    have h8_len_eq : (serPrefix8 x).length = (serPrefix7 x).length + 1 +
        (encodeVarint (BitVec.ofNat 64 k.ciphertext.length)).length + k.ciphertext.length := by
      rw [← hser8, List.length_append, List.length_append, List.length_cons]; omega
    have hlt7 : (serPrefix7 x).length < (BitVec.ofNat 64 x.model.serialized.length).toNat := by omega
    have hbeq7 := cap_beq_len_false hlt7
    have hle_var : (serPrefix7 x ++ [66#8]).length +
        (encodeVarint (BitVec.ofNat 64 k.ciphertext.length)).length ≤
        (BitVec.ofNat 64 x.model.serialized.length).toNat := by
      rw [List.length_append, List.length_singleton]; omega
    have hle_slice : (serPrefix7 x ++ 66#8 :: encodeVarint (BitVec.ofNat 64 k.ciphertext.length)).length +
        k.ciphertext.length ≤ (BitVec.ofNat 64 x.model.serialized.length).toNat := by
      rw [List.length_append, List.length_cons]; omega
    clear h8_len
    dsimp only [optKyberCopyBuf] at hnext ⊢
    rw [vecU8Buf_eq_open_one A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix7 x) hlt7]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    have hf1124 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 1124)
      libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15594
    have hf1128 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 1128)
      libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15598
    have hf1132 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 1132)
      libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x1559c
    have hf1136 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 1136)
      libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x155a0
    have hf1140 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 1140)
      libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x155a4
    have hf1144 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 1144)
      libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x155a8
    have hf1148 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 1148)
      libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x155ac
    have hf1152 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 1152)
      libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x155b0
    have hf1156 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 1156)
      libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x155b4
    have hf1160 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 1160)
      libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x155b8
    revert hpc hf1104 hf1108 hf1112 hf1116 hf1120 hf1124 hf1128 hf1132 hf1136 hf1140 hf1144 hf1148 hf1152 hf1156 hf1160
    generalize h_entry1 : (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName = entry1
    intro hpc hf1104 hf1108 hf1112 hf1116 hf1120 hf1124 hf1128 hf1132 hf1136 hf1140 hf1144 hf1148 hf1152 hf1156 hf1160
    examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry1 + 18446744073709477744#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [← h_entry1]; clear h_entry1
    rw [vecU8Buf_snoc_eq A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix7 x) 66#8 hlt7,
      bv_len_add_one (serPrefix7 x) 66#8]
    refine step_call_encVarint_trap b A ext (BitVec.ofNat 64 k.ciphertext.length) (sp + 224#64)
      (BitVec.ofNat 64 x.model.serialized.length) g.serPtr sp
      ((tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 1164#64)
      (serPrefix7 x ++ [66#8]) s.trace s hle_var
      (F := ((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗ ((sp + 56#64) ↦₆₄ x.bkA) ∗
        boxU8Buf A g.kyberCopyPtr k.ciphertext ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simpa only [State.spAligned, arm64_norm, *] using halign)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by ac_rfl)
      fun sf1 hpcf1 hrunf1 hspf1 htrf1 hregs1 => ?_
    simp only [List.append_assoc, List.singleton_append]
    have halign1 : sf1.spAligned = true := by simpa only [State.spAligned, hspf1, hsp] using halign
    have hfp1 : sf1.readReg64 .fp = sp + 272#64 := by reg_chain
    have hx19_1 : sf1.readReg64 .x19 = BitVec.ofNat 64 k.ciphertext.length := hregs1.1.trans hx19
    have hult1 := cap_sub_len_ult_false hle_slice
    have hule1 := cap_sub_len_ule_true hle_slice
    have hf1164 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 1164)
      libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x155bc
    have hf1168 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 1168)
      libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x155c0
    have hf1172 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 1172)
      libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x155c4
    have hf1176 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 1176)
      libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x155c8
    have hf1180 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 1180)
      libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x155cc
    have hf1184 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 1184)
      libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x155d0
    have hf1188 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 1188)
      libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x155d4
    by_cases hct_nil : k.ciphertext = []
    · have hser8_nil : serPrefix7 x ++ 66#8 :: encodeVarint (BitVec.ofNat 64 k.ciphertext.length) = serPrefix8 x := by
        simpa [hct_nil] using hser8
      have hct_bv0 : BitVec.ofNat 64 k.ciphertext.length = 0#64 := by simp [hct_nil]
      clear hct_nil h8_len_eq hser8
      rw [hser8_nil] at hult1 hule1 ⊢
      rw [hct_bv0] at hx19_1 hult1 hule1
      revert hnext hpcf1 hf1164 hf1168 hf1172 hf1176 hf1180 hf1184 hf1188
      generalize (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName = entry2
      intro hnext hpcf1 hf1164 hf1168 hf1172 hf1176 hf1180 hf1184 hf1188
      examples_hide_fetches
      apply SepWPp.of_sepWP (mid := entry2 + 1220#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      have hpost_nil :
          (((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
            (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
            (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix8 x).length) ∗
            vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix8 x) ∗
            A.pool ∗ stackAt sp preKeyMsgSubStack) ∗
          (((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗ ((sp + 56#64) ↦₆₄ x.bkA) ∗
            boxU8Buf A g.kyberCopyPtr k.ciphertext ∗ F) =
          ((((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗
            ((sp + 56#64) ↦₆₄ x.bkA) ∗
            ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
            (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
            (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix8 x).length) ∗
            vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix8 x) ∗
            boxU8Buf A g.kyberCopyPtr k.ciphertext ∗
            A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F) := by ac_rfl
      rw [hpost_nil]
      exact hnext _ (BitVec.ofNat 64 (serPrefix8 x).length)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (PreKeyMsgTagRegs.trans hregs1 (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self]))
    · have hct_pos : 0 < k.ciphertext.length := List.length_pos_of_ne_nil hct_nil
      have hct_beq := bv_len_beq_zero_false hct_pos hct_lt64
      have hct_toNat : (BitVec.ofNat 64 k.ciphertext.length).toNat = k.ciphertext.length := by
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hct_lt64]
      rw [vecU8Buf_eq_open_slice A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
        (serPrefix7 x ++ 66#8 :: encodeVarint (BitVec.ofNat 64 k.ciphertext.length))
        k.ciphertext.length hle_slice hcap_pos,
        boxU8Buf_nonempty_eq A g.kyberCopyPtr k.ciphertext hct_nil]
      have hf1192 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
        (H := Rust.withPanics (ext)) (k := 1192)
        libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x155d8
      have hf1196 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
        (H := Rust.withPanics (ext)) (k := 1196)
        libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x155dc
      have hf1200 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
        (H := Rust.withPanics (ext)) (k := 1200)
        libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x155e0
      have hf1204 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
        (H := Rust.withPanics (ext)) (k := 1204)
        libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x155e4
      have hf1208 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
        (H := Rust.withPanics (ext)) (k := 1208)
        libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x155e8
      revert hpcf1 hf1164 hf1168 hf1172 hf1176 hf1180 hf1184 hf1188 hf1192 hf1196 hf1200 hf1204 hf1208
      generalize h_entry2 : (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName = entry2
      intro hpcf1 hf1164 hf1168 hf1172 hf1176 hf1180 hf1184 hf1188 hf1192 hf1196 hf1200 hf1204 hf1208
      examples_hide_fetches
      apply SepWPp.of_sepWP (mid := entry2 + bv% (ls_off% "memcpy" - 0x15130))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      rw [← h_entry2]; clear h_entry2
      refine step_call_memcpy_ext b ext hMc
        (g.serPtr + BitVec.ofNat 64 (serPrefix7 x ++ 66#8 :: encodeVarint (BitVec.ofNat 64 k.ciphertext.length)).length)
        g.kyberCopyPtr sp ((tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 1212#64)
        (BitVec.ofNat 64 (serPrefix7 x ++ 66#8 :: encodeVarint (BitVec.ofNat 64 k.ciphertext.length)).length)
        (BitVec.ofNat 64 x.model.serialized.length)
        k.ciphertext s.trace s
        (F := ((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗ ((sp + 56#64) ↦₆₄ x.bkA) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄
            BitVec.ofNat 64 (serPrefix7 x ++ 66#8 :: encodeVarint (BitVec.ofNat 64 k.ciphertext.length)).length) ∗
          vecSliceRest A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
            (serPrefix7 x ++ 66#8 :: encodeVarint (BitVec.ofNat 64 k.ciphertext.length))
            k.ciphertext.length ∗
          A.pool ∗
          (⌜g.kyberCopyPtr ≠ 0#64 ∧ k.ciphertext.length < 2 ^ 63⌝ ∗
            A.live g.kyberCopyPtr k.ciphertext.length 1) ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simpa only [State.spAligned, arm64_norm, *] using halign1)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (PreKeyMsgTagRegs.trans hregs1 (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self]))
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by ac_rfl)
        fun sf2 hpcf2 hrunf2 hspf2 htrf2 hregs2 hx23_2 hx26_2 => ?_
      have halign2 : sf2.spAligned = true := by simpa only [State.spAligned, hspf2, hsp] using halign
      have hx19_2 : sf2.readReg64 .x19 = BitVec.ofNat 64 k.ciphertext.length := hregs2.1.trans hx19
      simp only [arm64_norm] at hx23_2 hx19_2
      have hadd_len :
          BitVec.ofNat 64 (serPrefix7 x ++ 66#8 :: encodeVarint (BitVec.ofNat 64 k.ciphertext.length)).length +
            BitVec.ofNat 64 k.ciphertext.length =
          BitVec.ofNat 64 (serPrefix8 x).length := by
        simp only [h8_len_eq, List.length_append, List.length_cons, BitVec.ofNat_add]
        ac_rfl
      clear h8_len_eq
      have hpost_eq :
          (((g.serPtr + BitVec.ofNat 64 (serPrefix7 x ++ 66#8 :: encodeVarint (BitVec.ofNat 64 k.ciphertext.length)).length) ↦ₛ
              k.ciphertext) ∗
            (g.kyberCopyPtr ↦ₛ k.ciphertext) ∗ stackAt sp preKeyMsgSubStack) ∗
          (((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗ ((sp + 56#64) ↦₆₄ x.bkA) ∗
            ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
            (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
            (((sp + 224#64) + 16#64) ↦₆₄
              BitVec.ofNat 64 (serPrefix7 x ++ 66#8 :: encodeVarint (BitVec.ofNat 64 k.ciphertext.length)).length) ∗
            vecSliceRest A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
              (serPrefix7 x ++ 66#8 :: encodeVarint (BitVec.ofNat 64 k.ciphertext.length))
              k.ciphertext.length ∗
            A.pool ∗
            (⌜g.kyberCopyPtr ≠ 0#64 ∧ k.ciphertext.length < 2 ^ 63⌝ ∗
              A.live g.kyberCopyPtr k.ciphertext.length 1) ∗ F) =
          ((((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗
            ((sp + 56#64) ↦₆₄ x.bkA) ∗
            ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
            (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
            (((sp + 224#64) + 16#64) ↦₆₄
              BitVec.ofNat 64 (serPrefix7 x ++ 66#8 :: encodeVarint (BitVec.ofNat 64 k.ciphertext.length)).length) ∗
            vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix8 x) ∗
            boxU8Buf A g.kyberCopyPtr k.ciphertext ∗
            A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F) := by
        rw [← hser8,
          ← vecU8Buf_append_eq A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
            (serPrefix7 x ++ 66#8 :: encodeVarint (BitVec.ofNat 64 k.ciphertext.length))
            k.ciphertext hcap_pos,
          boxU8Buf_nonempty_eq A g.kyberCopyPtr k.ciphertext hct_nil]
        ac_rfl
      rw [hpost_eq]
      have hf1212 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
        (H := Rust.withPanics (ext)) (k := 1212)
        libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x155ec
      have hf1216 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
        (H := Rust.withPanics (ext)) (k := 1216)
        libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x155f0
      revert hnext hpcf2 hf1212 hf1216
      generalize (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName = entry3
      intro hnext hpcf2 hf1212 hf1216
      examples_hide_fetches
      apply SepWPp.of_sepWP (mid := entry3 + 1220#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      exact hnext _
        (BitVec.ofNat 64 (serPrefix7 x ++ 66#8 :: encodeVarint (BitVec.ofNat 64 k.ciphertext.length)).length)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (PreKeyMsgTagRegs.trans hregs2 (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self]))

theorem step_preKeyMsg_tag8_trap (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) (hmemcpy : Rust.withPanics ext "memcpy" = some hookMemcpy)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64) (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 1104#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (halign : s.spAligned = true)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx19 : s.readReg64 .x19 =
      (match x.kp with | none => noneCap | some k => BitVec.ofNat 64 k.ciphertext.length))
    (hP : P = (((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗ ((sp + 56#64) ↦₆₄ x.bkA) ∗
      ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix7 x).length) ∗
      vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix7 x) ∗
      optKyberCopyBuf A g.kyberCopyPtr x.kp ∗ A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ (sm : State) (lenW : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 1220#64 →
      sm.status = .Running → sm.sp = sp → sm.trace = s.trace →
      sm.readReg64 .x8 = x.bkA → sm.readReg64 .x23 = BitVec.ofNat 64 (serPrefix8 x).length →
      sm.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length → PreKeyMsgTagRegs s sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗ ((sp + 56#64) ↦₆₄ x.bkA) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗ (((sp + 224#64) + 16#64) ↦₆₄ lenW) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix8 x) ∗
          optKyberCopyBuf A g.kyberCopyPtr x.kp ∗ A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q Qp :=
  step_preKeyMsg_tag8_ext b A ext (hookSat_memcpy_of_withPanics hmemcpy) x g sp hwf
    hpc hrun hsp halign hfp hx19 hP hnext

theorem step_preKeyMsg_tag8 (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64)
    (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName + 1104#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : s.spAligned = true)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx19 : s.readReg64 .x19 =
      (match x.kp with
       | none => noneCap
       | some k => BitVec.ofNat 64 k.ciphertext.length))
    (hP : P = (((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗
      ((sp + 56#64) ↦₆₄ x.bkA) ∗
      ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix7 x).length) ∗
      vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix7 x) ∗
      optKyberCopyBuf A g.kyberCopyPtr x.kp ∗
      A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ (sm : State) (lenW : BitVec 64),
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName + 1220#64 →
      sm.status = .Running →
      sm.sp = sp →
      sm.trace = s.trace →
      sm.readReg64 .x8 = x.bkA →
      sm.readReg64 .x23 = BitVec.ofNat 64 (serPrefix8 x).length →
      sm.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length →
      PreKeyMsgTagRegs s sm →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        ((((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗
          ((sp + 56#64) ↦₆₄ x.bkA) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ lenW) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix8 x) ∗
          optKyberCopyBuf A g.kyberCopyPtr x.kp ∗
          A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q Qp :=
  step_preKeyMsg_tag8_trap b A (tripleRatchetExterns C ctl abs) rfl x g sp hwf hpc hrun hsp halign hfp hx19 hP hnext

/-! ## Core Composition (`SeamA → SeamB`) -/

theorem preKeyMsgFrameSlotsAt_open_buf (A : RustAlloc) (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost)
    (s0 : State) (lenW : BitVec 64) (bs : List (BitVec 8)) :
    preKeyMsgFrameSlotsAt' A x g s0 lenW bs ∗ preKeyMsgHeapAt A x g s0 =
      let sp := s0.sp - 368#64
      ((sp ↦₆₄ g.msgCopyPtr) ∗
        ((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗
        ((sp + 24#64) ↦₃₂ x.regId) ∗
        ((sp + 44#64) ↦₃₂ g.kyberId32) ∗
        ((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗
        ((sp + 56#64) ↦₆₄ x.bkA) ∗
        ((sp + 72#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
        ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
        (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
        (((sp + 224#64) + 16#64) ↦₆₄ lenW) ∗
        vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr bs ∗
        boxU8Buf A g.bkSerPtr x.baseKey.serialize ∗
        boxU8Buf A g.ikSerPtr x.ik.serialize ∗
        boxU8Buf A g.msgCopyPtr x.msg.serialized ∗
        optKyberCopyBuf A g.kyberCopyPtr x.kp ∗
        A.pool ∗
        stackAt sp preKeyMsgSubStack) ∗
      (((sp + 8#64) ↦₆₄ x.ikA) ∗
        memRegion (sp + 28#64) 8 ∗
        ((sp + 36#64) ↦₃₂ g.ver32) ∗
        ((sp + 40#64) ↦₃₂ x.spk) ∗
        ((sp + 64#64) ↦₆₄ x.ret) ∗
        ((sp + 76#64) ↦₃₂ (if x.preKeyId.isSome then 1#32 else 0#32)) ∗
        ((sp + 80#64) ↦₆₄ x.msgA) ∗
        ((sp + 88#64) ↦₆₄ x.kyA) ∗
        memRegion (sp + 96#64) 128 ∗
        memRegion (sp + 248#64) 24 ∗
        preKeyMsgSavedRegs s0.sp s0 ∗
        (s0.sp ↦₆₄ x.msgA) ∗
        optKyberAt A x.kyA x.kyPtr x.kp ∗
        (x.bkA ↦ₛ x.baseKey.bytes.toList) ∗
        (x.ikA ↦ₛ x.ik.publicKey.bytes.toList) ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗
        memRegion x.ret 248) := by
  dsimp only [preKeyMsgFrameSlotsAt', preKeyMsgHeapAt]
  rw [vecU8AtLen_eq_header_sep_buf A (s0.sp - 368#64 + 224#64)
    (BitVec.ofNat 64 x.model.serialized.length) g.serPtr lenW bs, vecHeader]
  ac_rfl

theorem fields_encode_core_ok_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hMc : HookSat ext memcpyName (sessionMemcpySpec allocHookStack))
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (R : SepProp) (s0 s : State)
    (hA : SeamA img A x g R s0 s) :
    PreKeyMsgSegExit_ext img A ext x R s0 s (SeamB img A x g R s0) := by
  rcases hA with ⟨hpc0, hwf, hcommon, hmem⟩
  rcases hcommon with
    ⟨hrun, hsp, halign0, halign, htr, hfp0, hx19, hx20, hx21, hx22, hx24, hx25, hx27, hx28, hvregs0⟩
  let sp := s0.sp - 368#64
  have hfp : s.readReg64 .fp = sp + 272#64 := by
    have : s0.sp - 96#64 = sp + 272#64 := by dsimp [sp]; bv_omega
    exact hfp0.trans this
  have hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyMsgNewName + 604#64 := by
    rw [hpc0, preKeyMsgSeamAPC, preKeyMsgNewEntry, preKeyMsgNew_fnAddr_eq_trap img.base ext]
  let F_rest : SepProp :=
    ((sp + 8#64) ↦₆₄ x.ikA) ∗
      memRegion (sp + 28#64) 8 ∗
      ((sp + 36#64) ↦₃₂ g.ver32) ∗
      ((sp + 40#64) ↦₃₂ x.spk) ∗
      ((sp + 64#64) ↦₆₄ x.ret) ∗
      ((sp + 76#64) ↦₃₂ (if x.preKeyId.isSome then 1#32 else 0#32)) ∗
      ((sp + 80#64) ↦₆₄ x.msgA) ∗
      ((sp + 88#64) ↦₆₄ x.kyA) ∗
      memRegion (sp + 96#64) 128 ∗
      memRegion (sp + 248#64) 24 ∗
      preKeyMsgSavedRegs s0.sp s0 ∗
      (s0.sp ↦₆₄ x.msgA) ∗
      optKyberAt A x.kyA x.kyPtr x.kp ∗
      (x.bkA ↦ₛ x.baseKey.bytes.toList) ∗
      (x.ikA ↦ₛ x.ik.publicKey.bytes.toList) ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗
      memRegion x.ret 248
  let P_init : SepProp :=
    ((sp ↦₆₄ g.msgCopyPtr) ∗
      ((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗
      ((sp + 24#64) ↦₃₂ x.regId) ∗
      ((sp + 44#64) ↦₃₂ g.kyberId32) ∗
      ((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗
      ((sp + 56#64) ↦₆₄ x.bkA) ∗
      ((sp + 72#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
      ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ 1#64) ∗
      vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix0 x) ∗
      boxU8Buf A g.bkSerPtr x.baseKey.serialize ∗
      boxU8Buf A g.ikSerPtr x.ik.serialize ∗
      boxU8Buf A g.msgCopyPtr x.msg.serialized ∗
      optKyberCopyBuf A g.kyberCopyPtr x.kp ∗
      A.pool ∗
      stackAt sp preKeyMsgSubStack) ∗ F_rest
  have hmem_init : s.mem ⊨ P_init ∗ R := by
    have h1 : preKeyMsgFrameSlotsAt' A x g s0 1#64 [versionByte x.ver] ∗ preKeyMsgHeapAt A x g s0 = P_init :=
      preKeyMsgFrameSlotsAt_open_buf A x g s0 1#64 (serPrefix0 x)
    rw [← sepConj_assoc, h1] at hmem
    exact hmem
  have hwp : SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyMsgNewName + 1220#64) s P_init
      (fun sf P_f =>
        sf.sp = sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x8 = x.bkA ∧
        sf.readReg64 .x23 = BitVec.ofNat 64 x.model.serialized.length ∧
        sf.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length ∧
        PreKeyMsgTagRegs s sf ∧
        ∃ lenW, P_f = preKeyMsgFrameSlotsAt' A x g s0 lenW x.model.serialized ∗ preKeyMsgHeapAt A x g s0)
      (fun _ _ => False) := by
    refine step_preKeyMsg_tag1_trap img.base A ext x g sp hwf hpc hrun hsp halign hfp hx20 hx25
      (F := (sp ↦₆₄ g.msgCopyPtr) ∗ ((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗ ((sp + 24#64) ↦₃₂ x.regId) ∗
        ((sp + 44#64) ↦₃₂ g.kyberId32) ∗ ((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗
        ((sp + 56#64) ↦₆₄ x.bkA) ∗ ((sp + 72#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
        boxU8Buf A g.bkSerPtr x.baseKey.serialize ∗ boxU8Buf A g.ikSerPtr x.ik.serialize ∗
        boxU8Buf A g.msgCopyPtr x.msg.serialized ∗ optKyberCopyBuf A g.kyberCopyPtr x.kp ∗ F_rest)
      (by dsimp [P_init]; ac_rfl)
      fun s1 hpc1 hrun1 hsp1 htr1 hx1_1 hregs1 => ?_
    have halign1 : s1.spAligned = true := by simpa only [State.spAligned, hsp1, hsp] using halign
    have hfp1 : s1.readReg64 .fp = sp + 272#64 := by reg_chain
    have hx24_1 : s1.readReg64 .x24 = 33#64 := by reg_chain
    have hx28_1 : s1.readReg64 .x28 = g.bkSerPtr := by reg_chain
    refine step_preKeyMsg_tag2_ext img.base A ext hMc x g sp hwf hpc1 hrun1 hsp1 halign1 hfp1
      hx1_1 hx24_1 hx28_1
      (F := (sp ↦₆₄ g.msgCopyPtr) ∗ ((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗ ((sp + 24#64) ↦₃₂ x.regId) ∗
        ((sp + 44#64) ↦₃₂ g.kyberId32) ∗ ((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗
        ((sp + 56#64) ↦₆₄ x.bkA) ∗ ((sp + 72#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
        boxU8Buf A g.ikSerPtr x.ik.serialize ∗ boxU8Buf A g.msgCopyPtr x.msg.serialized ∗
        optKyberCopyBuf A g.kyberCopyPtr x.kp ∗ F_rest)
      (by ac_rfl)
      fun s2 hpc2 hrun2 hsp2 htr2 hx23_2 hx26_2 hregs2 => ?_
    have halign2 : s2.spAligned = true := by simpa only [State.spAligned, hsp2, hsp] using halign
    have hfp2 : s2.readReg64 .fp = sp + 272#64 := by reg_chain
    have hx22_2 : s2.readReg64 .x22 = 33#64 := by reg_chain
    refine step_preKeyMsg_tag3_ext img.base A ext hMc x g sp hwf hpc2 hrun2 hsp2 halign2 hfp2
      hx22_2 hx23_2 hx26_2
      (F := (sp ↦₆₄ g.msgCopyPtr) ∗ ((sp + 24#64) ↦₃₂ x.regId) ∗
        ((sp + 44#64) ↦₃₂ g.kyberId32) ∗ ((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗
        ((sp + 56#64) ↦₆₄ x.bkA) ∗ ((sp + 72#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
        boxU8Buf A g.bkSerPtr x.baseKey.serialize ∗ boxU8Buf A g.msgCopyPtr x.msg.serialized ∗
        optKyberCopyBuf A g.kyberCopyPtr x.kp ∗ F_rest)
      (by ac_rfl)
      fun s3 hpc3 hrun3 hsp3 htr3 hx23_3 hx26_3 hregs3 => ?_
    have halign3 : s3.spAligned = true := by simpa only [State.spAligned, hsp3, hsp] using halign
    have hfp3 : s3.readReg64 .fp = sp + 272#64 := by reg_chain
    have hx27_3 : s3.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length := by reg_chain
    refine step_preKeyMsg_tag4_ext img.base A ext hMc x g sp hwf hpc3 hrun3 hsp3 halign3 hfp3
      hx23_3 hx26_3 hx27_3
      (F := ((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗ ((sp + 24#64) ↦₃₂ x.regId) ∗
        ((sp + 44#64) ↦₃₂ g.kyberId32) ∗ ((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗
        ((sp + 56#64) ↦₆₄ x.bkA) ∗ ((sp + 72#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
        boxU8Buf A g.bkSerPtr x.baseKey.serialize ∗ boxU8Buf A g.ikSerPtr x.ik.serialize ∗
        optKyberCopyBuf A g.kyberCopyPtr x.kp ∗ F_rest)
      (by ac_rfl)
      fun s4 hpc4 hrun4 hsp4 htr4 hx23_4 hx26_4 hregs4 => ?_
    have halign4 : s4.spAligned = true := by simpa only [State.spAligned, hsp4, hsp] using halign
    have hfp4 : s4.readReg64 .fp = sp + 272#64 := by reg_chain
    refine step_preKeyMsg_tag5_trap img.base A ext x g sp hwf hpc4 hrun4 hsp4 halign4 hfp4
      hx23_4 hx26_4
      (F := (sp ↦₆₄ g.msgCopyPtr) ∗ ((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗
        ((sp + 44#64) ↦₃₂ g.kyberId32) ∗ ((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗
        ((sp + 56#64) ↦₆₄ x.bkA) ∗ ((sp + 72#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
        boxU8Buf A g.bkSerPtr x.baseKey.serialize ∗ boxU8Buf A g.ikSerPtr x.ik.serialize ∗
        boxU8Buf A g.msgCopyPtr x.msg.serialized ∗ optKyberCopyBuf A g.kyberCopyPtr x.kp ∗ F_rest)
      (by ac_rfl)
      fun s5 hpc5 hrun5 hsp5 htr5 hx1_5 hx8_5 hregs5 => ?_
    have halign5 : s5.spAligned = true := by simpa only [State.spAligned, hsp5, hsp] using halign
    have hfp5 : s5.readReg64 .fp = sp + 272#64 := by reg_chain
    have hx21_5 : (s5.readReg64 .x21).setWidth 32 = x.spk := by reg_chain
    refine step_preKeyMsg_tag6_trap img.base A ext x g sp hwf hpc5 hrun5 hsp5 halign5 hfp5
      hx1_5 hx8_5 hx21_5
      (F := (sp ↦₆₄ g.msgCopyPtr) ∗ ((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗ ((sp + 24#64) ↦₃₂ x.regId) ∗
        ((sp + 44#64) ↦₃₂ g.kyberId32) ∗ ((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗
        ((sp + 56#64) ↦₆₄ x.bkA) ∗ ((sp + 72#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
        boxU8Buf A g.bkSerPtr x.baseKey.serialize ∗ boxU8Buf A g.ikSerPtr x.ik.serialize ∗
        boxU8Buf A g.msgCopyPtr x.msg.serialized ∗ optKyberCopyBuf A g.kyberCopyPtr x.kp ∗ F_rest)
      (by ac_rfl)
      fun s6 hpc6 hrun6 hsp6 htr6 hregs6 => ?_
    have halign6 : s6.spAligned = true := by simpa only [State.spAligned, hsp6, hsp] using halign
    have hfp6 : s6.readReg64 .fp = sp + 272#64 := by reg_chain
    refine step_preKeyMsg_tag7_trap img.base A ext x g sp hwf hpc6 hrun6 hsp6 halign6 hfp6
      (F := (sp ↦₆₄ g.msgCopyPtr) ∗ ((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗ ((sp + 24#64) ↦₃₂ x.regId) ∗
        ((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗ ((sp + 56#64) ↦₆₄ x.bkA) ∗
        boxU8Buf A g.bkSerPtr x.baseKey.serialize ∗ boxU8Buf A g.ikSerPtr x.ik.serialize ∗
        boxU8Buf A g.msgCopyPtr x.msg.serialized ∗ optKyberCopyBuf A g.kyberCopyPtr x.kp ∗ F_rest)
      (by ac_rfl)
      fun s7 hpc7 hrun7 hsp7 htr7 hregs7 => ?_
    have halign7 : s7.spAligned = true := by simpa only [State.spAligned, hsp7, hsp] using halign
    have hfp7 : s7.readReg64 .fp = sp + 272#64 := by reg_chain
    have hx19_7 : s7.readReg64 .x19 =
        (match x.kp with | none => noneCap | some k => BitVec.ofNat 64 k.ciphertext.length) :=
      (show s7.readReg64 .x19 = s.readReg64 .x19 by reg_chain).trans hx19
    refine step_preKeyMsg_tag8_ext img.base A ext hMc x g sp hwf hpc7 hrun7 hsp7 halign7 hfp7 hx19_7
      (F := (sp ↦₆₄ g.msgCopyPtr) ∗ ((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗ ((sp + 24#64) ↦₃₂ x.regId) ∗
        ((sp + 44#64) ↦₃₂ g.kyberId32) ∗ ((sp + 72#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
        boxU8Buf A g.bkSerPtr x.baseKey.serialize ∗ boxU8Buf A g.ikSerPtr x.ik.serialize ∗
        boxU8Buf A g.msgCopyPtr x.msg.serialized ∗ F_rest)
      (by ac_rfl)
      fun s8 lenW hpc8 hrun8 hsp8 htr8 hx8_8 hx23_8 hx26_8 hregs8 => ?_
    apply SepWPp.done hpc8 hrun8
    refine ⟨hsp8, by reg_chain, hx8_8, ?_, hx26_8, by reg_chain, lenW, ?_⟩
    · rw [serPrefix8_eq_model_serialized x] at hx23_8; exact hx23_8
    · rw [serPrefix8_eq_model_serialized x]
      have hopen8 := preKeyMsgFrameSlotsAt_open_buf A x g s0 lenW x.model.serialized
      rw [hopen8]
      dsimp only [F_rest, sp]
      ac_rfl
  intro hL
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, hspf, htrf, hx8f, hx23f, hx26f, hregsf, lenW, hPf⟩ | ⟨_, _, _, hfalse⟩ | ⟨_, _hoom⟩⟩ :=
    hwp R hmem_init hL
  · refine ⟨sf, hsteps, Or.inl ?_⟩
    have hpcf' : sf.pc = preKeyMsgSeamBPC img := by
      rw [preKeyMsgSeamBPC, preKeyMsgNewEntry, ← preKeyMsgNew_fnAddr_eq_trap img.base ext]
      exact hpcf
    have halignf : sf.spAligned = true := by simpa only [State.spAligned, hspf, hsp] using halign
    refine ⟨hpcf', hwf, ?_, hx8f, hx23f, hx26f, lenW, ?_⟩
    · exact ⟨hrunf, hspf, halign0, halignf, by reg_chain⟩
    · rw [hPf, sepConj_assoc] at hmf
      exact hmf
  · exact False.elim hfalse
  · dsimp only at _hoom
    exact (not_satisfies_false_sepConj _hoom).elim

theorem fields_encode_core_ok_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (R : SepProp) (s0 s : State)
    (hA : SeamA img A x g R s0 s) :
    PreKeyMsgSegExit_trap img C A abs x R s0 s (SeamB img A x g R s0) :=
  fields_encode_core_ok_ext (hookSat_memcpy_of_withPanics rfl) x g R s0 s hA

theorem fields_encode_core_ok {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (R : SepProp) (s0 s : State)
    (hA : SeamA img A x g R s0 s) :
    PreKeyMsgSegExit img C A ctl abs x R s0 s (SeamB img A x g R s0) :=
  preKeyMsgSegExit_of_trap (fun _ hB => hB.2.2.1.1) (fields_encode_core_ok_trap x g R s0 s hA)

/-! ## Relocatable Placement Proofs -/

section Placed

open CryptoVerification.LibsignalPublicApi.Placed

set_option maxRecDepth 200000
attribute [local irreducible] Program.fetch Program.externAt?

theorem step_preKeyMsg_tag8_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hmemcpy : HookSat H "memcpy" framelessMemcpySpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64) (s_base : State)
    (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_41).base + 1104#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (halign : s.spAligned = true) (htr : s.trace = s_base.trace)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx19 : s.readReg64 .x19 =
      (match x.kp with
       | none => noneCap
       | some k => BitVec.ofNat 64 k.ciphertext.length))
    (hP : P = (((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗
      ((sp + 56#64) ↦₆₄ x.bkA) ∗
      ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix7 x).length) ∗
      vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix7 x) ∗
      optKyberCopyBuf A g.kyberCopyPtr x.kp ∗
      A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ (sm : State) (lenW : BitVec 64),
      sm.pc = (blkPl_41).base + 1220#64 → sm.status = .Running →
      sm.sp = sp → sm.trace = s_base.trace → LibsignalCodeLoaded lsmpl sm.mem →
      sm.readReg64 .x8 = x.bkA →
      sm.readReg64 .x23 = BitVec.ofNat 64 (serPrefix8 x).length →
      sm.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length →
      PreKeyMsgTagRegs s sm →
      SepWPp (lsProg_41 H) ret sm
        ((((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗
          ((sp + 56#64) ↦₆₄ x.bkA) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ lenW) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix8 x) ∗
          optKyberCopyBuf A g.kyberCopyPtr x.kp ∗
          A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
        Q (EncodePanicPost s_base)) :
    SepWPp (lsProg_41 H) ret s P Q (EncodePanicPost s_base) := by
  rcases hwf with ⟨hser_lt, _⟩
  have hcap_toNat : (BitVec.ofNat 64 x.model.serialized.length).toNat = x.model.serialized.length := by
    simp only [BitVec.toNat_ofNat]; omega
  have ⟨h0_len, h01_le, h12_le, h23_le, h34_le, h45_le, h56_le, h67_le, h78_le, h8_len⟩ :=
    serPrefix_lengths_le x
  have hcap_pos : 0 < (BitVec.ofNat 64 x.model.serialized.length).toNat := by omega
  subst hP
  cases hkp : x.kp with
  | none =>
    rw [hkp] at hx19 hnext
    have hser8 : serPrefix8 x = serPrefix7 x := by
      simp [serPrefix8, hkp, LibsignalSessionApi.Prost.bytesField]
    clear h8_len
    apply SepWPp.of_sepWP_lscl hcl (mid := (blkPl_41).base + 1220#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl1
    rw [← hser8]
    exact hnext _ (BitVec.ofNat 64 (serPrefix8 x).length)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl1
      (by simp only [arm64_norm, *])
      (by rw [hser8]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self])
  | some k =>
    rw [hkp] at hx19 hnext
    have hct_lt : k.ciphertext.length < 2 ^ 63 := by
      have : k.ciphertext.length ≤ (serPrefix8 x).length := by
        simp [serPrefix8, hkp, LibsignalSessionApi.Prost.bytesField]; omega
      omega
    have hct_lt64 : k.ciphertext.length < 2 ^ 64 := by omega
    have hadd1 := ct_len_add_one_beq_zero_false hct_lt
    have hvar_pos : 1 ≤ (encodeVarint (BitVec.ofNat 64 k.ciphertext.length)).length := by
      unfold encodeVarint encodeVarintAux; split <;> simp
    have hser8 : (serPrefix7 x ++ 66#8 :: encodeVarint (BitVec.ofNat 64 k.ciphertext.length)) ++
        k.ciphertext = serPrefix8 x := by
      rw [serPrefix8, hkp, Option.map_some, prost_bytesField_some 8 k.ciphertext hct_lt64, prost_key_8_2]
      simp only [← List.append_assoc, List.singleton_append]
    have h8_len_eq : (serPrefix8 x).length = (serPrefix7 x).length + 1 +
        (encodeVarint (BitVec.ofNat 64 k.ciphertext.length)).length + k.ciphertext.length := by
      rw [← hser8, List.length_append, List.length_append, List.length_cons]; omega
    have hlt7 : (serPrefix7 x).length < (BitVec.ofNat 64 x.model.serialized.length).toNat := by omega
    have hbeq7 := cap_beq_len_false hlt7
    have hle_var : (serPrefix7 x ++ [66#8]).length +
        (encodeVarint (BitVec.ofNat 64 k.ciphertext.length)).length ≤
        (BitVec.ofNat 64 x.model.serialized.length).toNat := by
      rw [List.length_append, List.length_singleton]; omega
    have hle_slice : (serPrefix7 x ++ 66#8 :: encodeVarint (BitVec.ofNat 64 k.ciphertext.length)).length +
        k.ciphertext.length ≤ (BitVec.ofNat 64 x.model.serialized.length).toNat := by
      rw [List.length_append, List.length_cons]; omega
    clear h8_len
    dsimp only [optKyberCopyBuf] at hnext ⊢
    rw [vecU8Buf_eq_open_one A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix7 x) hlt7]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    apply SepWPp.of_sepWP_lscl hcl (mid := (blkPl_10).base); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, *])
    intro hcl0
    rw [vecU8Buf_snoc_eq A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix7 x) 66#8 hlt7,
      bv_len_add_one (serPrefix7 x) 66#8]
    refine step_call_encVarint_placed hshim halloc hrealloc hpanic
      (BitVec.ofNat 64 k.ciphertext.length) (sp + 224#64)
      (BitVec.ofNat 64 x.model.serialized.length) g.serPtr sp
      ((blkPl_41).base + 1164#64) (serPrefix7 x ++ [66#8]) s_base s hle_var (by omega)
      (F := ((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗ ((sp + 56#64) ↦₆₄ x.bkA) ∗
        boxU8Buf A g.kyberCopyPtr k.ciphertext ∗ F) hcl0
      (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simpa only [State.spAligned, arm64_norm, *] using halign)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by ac_rfl)
      fun sf1 hpcf1 hrunf1 hspf1 htrf1 hclf1 hregs1 => ?_
    simp only [List.append_assoc, List.singleton_append]
    have halign1 : sf1.spAligned = true := by simpa only [State.spAligned, hspf1, hsp] using halign
    have hfp1 : sf1.readReg64 .fp = sp + 272#64 := by reg_chain
    have hx19_1 : sf1.readReg64 .x19 = BitVec.ofNat 64 k.ciphertext.length := hregs1.1.trans hx19
    have hult1 := cap_sub_len_ult_false hle_slice
    have hule1 := cap_sub_len_ule_true hle_slice
    by_cases hct_nil : k.ciphertext = []
    · have hser8_nil : serPrefix7 x ++ 66#8 :: encodeVarint (BitVec.ofNat 64 k.ciphertext.length) = serPrefix8 x := by
        simpa [hct_nil] using hser8
      have hct_bv0 : BitVec.ofNat 64 k.ciphertext.length = 0#64 := by simp [hct_nil]
      clear hct_nil h8_len_eq hser8
      rw [hser8_nil] at hult1 hule1 ⊢
      rw [hct_bv0] at hx19_1 hult1 hule1
      apply SepWPp.of_sepWP_lscl hclf1 (mid := (blkPl_41).base + 1220#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hclf2
      have hpost_nil :
          (((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
            (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
            (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix8 x).length) ∗
            vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix8 x) ∗
            A.pool ∗ stackAt sp preKeyMsgSubStack) ∗
          (((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗ ((sp + 56#64) ↦₆₄ x.bkA) ∗
            boxU8Buf A g.kyberCopyPtr k.ciphertext ∗ F) =
          ((((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗
            ((sp + 56#64) ↦₆₄ x.bkA) ∗
            ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
            (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
            (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix8 x).length) ∗
            vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix8 x) ∗
            boxU8Buf A g.kyberCopyPtr k.ciphertext ∗
            A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F) := by ac_rfl
      rw [hpost_nil]
      exact hnext _ (BitVec.ofNat 64 (serPrefix8 x).length)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hclf2
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (PreKeyMsgTagRegs.trans hregs1 (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self]))
    · have hct_pos : 0 < k.ciphertext.length := List.length_pos_of_ne_nil hct_nil
      have hct_beq := bv_len_beq_zero_false hct_pos hct_lt64
      have hct_toNat : (BitVec.ofNat 64 k.ciphertext.length).toNat = k.ciphertext.length := by
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hct_lt64]
      rw [vecU8Buf_eq_open_slice A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
        (serPrefix7 x ++ 66#8 :: encodeVarint (BitVec.ofNat 64 k.ciphertext.length))
        k.ciphertext.length hle_slice hcap_pos,
        boxU8Buf_nonempty_eq A g.kyberCopyPtr k.ciphertext hct_nil]
      apply SepWPp.of_sepWP_lscl hclf1 (mid := lsρ "memcpy"); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hclf1'
      refine step_call_memcpy_placed hmemcpy
        (g.serPtr + BitVec.ofNat 64 (serPrefix7 x ++ 66#8 :: encodeVarint (BitVec.ofNat 64 k.ciphertext.length)).length)
        g.kyberCopyPtr sp ((blkPl_41).base + 1212#64)
        (BitVec.ofNat 64 (serPrefix7 x ++ 66#8 :: encodeVarint (BitVec.ofNat 64 k.ciphertext.length)).length)
        (BitVec.ofNat 64 x.model.serialized.length)
        k.ciphertext s_base.trace s
        (F := ((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗ ((sp + 56#64) ↦₆₄ x.bkA) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄
            BitVec.ofNat 64 (serPrefix7 x ++ 66#8 :: encodeVarint (BitVec.ofNat 64 k.ciphertext.length)).length) ∗
          vecSliceRest A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
            (serPrefix7 x ++ 66#8 :: encodeVarint (BitVec.ofNat 64 k.ciphertext.length))
            k.ciphertext.length ∗
          A.pool ∗ stackAt sp preKeyMsgSubStack ∗
          (⌜g.kyberCopyPtr ≠ 0#64 ∧ k.ciphertext.length < 2 ^ 63⌝ ∗
            A.live g.kyberCopyPtr k.ciphertext.length 1) ∗ F)
        hclf1' (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simpa only [State.spAligned, arm64_norm, *] using halign1)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (PreKeyMsgTagRegs.trans hregs1 (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self]))
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by ac_rfl)
        fun sf2 hpcf2 hrunf2 hspf2 htrf2 hclf2 hregs2 hx23_2 hx26_2 => ?_
      have halign2 : sf2.spAligned = true := by simpa only [State.spAligned, hspf2, hsp] using halign
      have hx19_2 : sf2.readReg64 .x19 = BitVec.ofNat 64 k.ciphertext.length := hregs2.1.trans hx19
      simp only [arm64_norm] at hx23_2 hx19_2
      have hadd_len :
          BitVec.ofNat 64 (serPrefix7 x ++ 66#8 :: encodeVarint (BitVec.ofNat 64 k.ciphertext.length)).length +
            BitVec.ofNat 64 k.ciphertext.length =
          BitVec.ofNat 64 (serPrefix8 x).length := by
        simp only [h8_len_eq, List.length_append, List.length_cons, BitVec.ofNat_add]
        ac_rfl
      clear h8_len_eq
      have hpost_eq :
          (((g.serPtr + BitVec.ofNat 64 (serPrefix7 x ++ 66#8 :: encodeVarint (BitVec.ofNat 64 k.ciphertext.length)).length) ↦ₛ
              k.ciphertext) ∗
            (g.kyberCopyPtr ↦ₛ k.ciphertext)) ∗
          (((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗ ((sp + 56#64) ↦₆₄ x.bkA) ∗
            ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
            (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
            (((sp + 224#64) + 16#64) ↦₆₄
              BitVec.ofNat 64 (serPrefix7 x ++ 66#8 :: encodeVarint (BitVec.ofNat 64 k.ciphertext.length)).length) ∗
            vecSliceRest A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
              (serPrefix7 x ++ 66#8 :: encodeVarint (BitVec.ofNat 64 k.ciphertext.length))
              k.ciphertext.length ∗
            A.pool ∗ stackAt sp preKeyMsgSubStack ∗
            (⌜g.kyberCopyPtr ≠ 0#64 ∧ k.ciphertext.length < 2 ^ 63⌝ ∗
              A.live g.kyberCopyPtr k.ciphertext.length 1) ∗ F) =
          ((((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗
            ((sp + 56#64) ↦₆₄ x.bkA) ∗
            ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
            (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
            (((sp + 224#64) + 16#64) ↦₆₄
              BitVec.ofNat 64 (serPrefix7 x ++ 66#8 :: encodeVarint (BitVec.ofNat 64 k.ciphertext.length)).length) ∗
            vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix8 x) ∗
            boxU8Buf A g.kyberCopyPtr k.ciphertext ∗
            A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F) := by
        rw [← hser8,
          ← vecU8Buf_append_eq A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
            (serPrefix7 x ++ 66#8 :: encodeVarint (BitVec.ofNat 64 k.ciphertext.length))
            k.ciphertext hcap_pos,
          boxU8Buf_nonempty_eq A g.kyberCopyPtr k.ciphertext hct_nil]
        ac_rfl
      rw [hpost_eq]
      apply SepWPp.of_sepWP_lscl hclf2 (mid := (blkPl_41).base + 1220#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hclf3
      exact hnext _
        (BitVec.ofNat 64 (serPrefix7 x ++ 66#8 :: encodeVarint (BitVec.ofNat 64 k.ciphertext.length)).length)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hclf3
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (PreKeyMsgTagRegs.trans hregs2 (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self]))

theorem fields_encode_core_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hmemcpy : HookSat H "memcpy" framelessMemcpySpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (R : SepProp) (s0 s : State)
    (hA : SeamA_placed A x g R s0 s) :
    PreKeyMsgSegExit_placed A H x R s0 s (SeamB_placed A x g R s0) := by
  rcases hA with ⟨hpc, hcl, hwf, hcommon, hmem⟩
  rcases hcommon with
    ⟨hrun, hsp, halign0, halign, htr, hfp0, hx19, hx20, hx21, hx22, hx24, hx25, hx27, hx28, hvregs0⟩
  let sp := s0.sp - 368#64
  have hfp : s.readReg64 .fp = sp + 272#64 := by
    have : s0.sp - 96#64 = sp + 272#64 := by dsimp [sp]; bv_omega
    exact hfp0.trans this
  let F_rest : SepProp :=
    ((sp + 8#64) ↦₆₄ x.ikA) ∗
      memRegion (sp + 28#64) 8 ∗
      ((sp + 36#64) ↦₃₂ g.ver32) ∗
      ((sp + 40#64) ↦₃₂ x.spk) ∗
      ((sp + 64#64) ↦₆₄ x.ret) ∗
      ((sp + 76#64) ↦₃₂ (if x.preKeyId.isSome then 1#32 else 0#32)) ∗
      ((sp + 80#64) ↦₆₄ x.msgA) ∗
      ((sp + 88#64) ↦₆₄ x.kyA) ∗
      memRegion (sp + 96#64) 128 ∗
      memRegion (sp + 248#64) 24 ∗
      preKeyMsgSavedRegs s0.sp s0 ∗
      (s0.sp ↦₆₄ x.msgA) ∗
      optKyberAt A x.kyA x.kyPtr x.kp ∗
      (x.bkA ↦ₛ x.baseKey.bytes.toList) ∗
      (x.ikA ↦ₛ x.ik.publicKey.bytes.toList) ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗
      memRegion x.ret 248
  let P_init : SepProp :=
    ((sp ↦₆₄ g.msgCopyPtr) ∗
      ((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗
      ((sp + 24#64) ↦₃₂ x.regId) ∗
      ((sp + 44#64) ↦₃₂ g.kyberId32) ∗
      ((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗
      ((sp + 56#64) ↦₆₄ x.bkA) ∗
      ((sp + 72#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
      ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ 1#64) ∗
      vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix0 x) ∗
      boxU8Buf A g.bkSerPtr x.baseKey.serialize ∗
      boxU8Buf A g.ikSerPtr x.ik.serialize ∗
      boxU8Buf A g.msgCopyPtr x.msg.serialized ∗
      optKyberCopyBuf A g.kyberCopyPtr x.kp ∗
      A.pool ∗
      stackAt sp preKeyMsgSubStack) ∗ F_rest
  have hmem_init : s.mem ⊨ P_init ∗ R := by
    have h1 : preKeyMsgFrameSlotsAt' A x g s0 1#64 [versionByte x.ver] ∗ preKeyMsgHeapAt A x g s0 = P_init :=
      preKeyMsgFrameSlotsAt_open_buf A x g s0 1#64 (serPrefix0 x)
    rw [← sepConj_assoc, h1] at hmem
    exact hmem
  have hwp : SepWPp (lsProg_41 H)
      ((blkPl_41).base + 1220#64) s P_init
      (fun sf P_f =>
        sf.sp = sp ∧ sf.trace = s0.trace ∧ LibsignalCodeLoaded lsmpl sf.mem ∧
        sf.readReg64 .x8 = x.bkA ∧
        sf.readReg64 .x23 = BitVec.ofNat 64 x.model.serialized.length ∧
        sf.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length ∧
        PreKeyMsgTagRegs s sf ∧
        ∃ lenW, P_f = preKeyMsgFrameSlotsAt' A x g s0 lenW x.model.serialized ∗ preKeyMsgHeapAt A x g s0)
      (EncodePanicPost s0) := by
    refine step_preKeyMsg_tag1_placed hshim halloc hrealloc hpanic x g sp s0 hwf hcl hpc hrun hsp halign htr hfp hx20 hx25
      (F := (sp ↦₆₄ g.msgCopyPtr) ∗ ((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗ ((sp + 24#64) ↦₃₂ x.regId) ∗
        ((sp + 44#64) ↦₃₂ g.kyberId32) ∗ ((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗
        ((sp + 56#64) ↦₆₄ x.bkA) ∗ ((sp + 72#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
        boxU8Buf A g.bkSerPtr x.baseKey.serialize ∗ boxU8Buf A g.ikSerPtr x.ik.serialize ∗
        boxU8Buf A g.msgCopyPtr x.msg.serialized ∗ optKyberCopyBuf A g.kyberCopyPtr x.kp ∗ F_rest)
      (by dsimp [P_init]; ac_rfl)
      fun s1 hpc1 hrun1 hsp1 htr1 hcl1 hx1_1 hregs1 => ?_
    have halign1 : s1.spAligned = true := by simpa only [State.spAligned, hsp1, hsp] using halign
    have hfp1 : s1.readReg64 .fp = sp + 272#64 := by reg_chain
    have hx24_1 : s1.readReg64 .x24 = 33#64 := by reg_chain
    have hx28_1 : s1.readReg64 .x28 = g.bkSerPtr := by reg_chain
    refine step_preKeyMsg_tag2_placed hshim halloc hrealloc hmemcpy hpanic x g sp s0 hwf hcl1 hpc1 hrun1 hsp1 halign1 htr1 hfp1
      hx1_1 hx24_1 hx28_1
      (F := (sp ↦₆₄ g.msgCopyPtr) ∗ ((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗ ((sp + 24#64) ↦₃₂ x.regId) ∗
        ((sp + 44#64) ↦₃₂ g.kyberId32) ∗ ((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗
        ((sp + 56#64) ↦₆₄ x.bkA) ∗ ((sp + 72#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
        boxU8Buf A g.ikSerPtr x.ik.serialize ∗ boxU8Buf A g.msgCopyPtr x.msg.serialized ∗
        optKyberCopyBuf A g.kyberCopyPtr x.kp ∗ F_rest)
      (by ac_rfl)
      fun s2 hpc2 hrun2 hsp2 htr2 hcl2 hx23_2 hx26_2 hregs2 => ?_
    have halign2 : s2.spAligned = true := by simpa only [State.spAligned, hsp2, hsp] using halign
    have hfp2 : s2.readReg64 .fp = sp + 272#64 := by reg_chain
    have hx22_2 : s2.readReg64 .x22 = 33#64 := by reg_chain
    refine step_preKeyMsg_tag3_placed hshim halloc hrealloc hmemcpy hpanic x g sp s0 hwf hcl2 hpc2 hrun2 hsp2 halign2 htr2 hfp2
      hx22_2 hx23_2 hx26_2
      (F := (sp ↦₆₄ g.msgCopyPtr) ∗ ((sp + 24#64) ↦₃₂ x.regId) ∗
        ((sp + 44#64) ↦₃₂ g.kyberId32) ∗ ((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗
        ((sp + 56#64) ↦₆₄ x.bkA) ∗ ((sp + 72#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
        boxU8Buf A g.bkSerPtr x.baseKey.serialize ∗ boxU8Buf A g.msgCopyPtr x.msg.serialized ∗
        optKyberCopyBuf A g.kyberCopyPtr x.kp ∗ F_rest)
      (by ac_rfl)
      fun s3 hpc3 hrun3 hsp3 htr3 hcl3 hx23_3 hx26_3 hregs3 => ?_
    have halign3 : s3.spAligned = true := by simpa only [State.spAligned, hsp3, hsp] using halign
    have hfp3 : s3.readReg64 .fp = sp + 272#64 := by reg_chain
    have hx27_3 : s3.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length := by reg_chain
    refine step_preKeyMsg_tag4_placed hshim halloc hrealloc hmemcpy hpanic x g sp s0 hwf hcl3 hpc3 hrun3 hsp3 halign3 htr3 hfp3
      hx23_3 hx26_3 hx27_3
      (F := ((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗ ((sp + 24#64) ↦₃₂ x.regId) ∗
        ((sp + 44#64) ↦₃₂ g.kyberId32) ∗ ((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗
        ((sp + 56#64) ↦₆₄ x.bkA) ∗ ((sp + 72#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
        boxU8Buf A g.bkSerPtr x.baseKey.serialize ∗ boxU8Buf A g.ikSerPtr x.ik.serialize ∗
        optKyberCopyBuf A g.kyberCopyPtr x.kp ∗ F_rest)
      (by ac_rfl)
      fun s4 hpc4 hrun4 hsp4 htr4 hcl4 hx23_4 hx26_4 hregs4 => ?_
    have halign4 : s4.spAligned = true := by simpa only [State.spAligned, hsp4, hsp] using halign
    have hfp4 : s4.readReg64 .fp = sp + 272#64 := by reg_chain
    refine step_preKeyMsg_tag5_placed hshim halloc hrealloc hpanic x g sp s0 hwf hcl4 hpc4 hrun4 hsp4 halign4 htr4 hfp4
      hx23_4 hx26_4
      (F := (sp ↦₆₄ g.msgCopyPtr) ∗ ((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗
        ((sp + 44#64) ↦₃₂ g.kyberId32) ∗ ((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗
        ((sp + 56#64) ↦₆₄ x.bkA) ∗ ((sp + 72#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
        boxU8Buf A g.bkSerPtr x.baseKey.serialize ∗ boxU8Buf A g.ikSerPtr x.ik.serialize ∗
        boxU8Buf A g.msgCopyPtr x.msg.serialized ∗ optKyberCopyBuf A g.kyberCopyPtr x.kp ∗ F_rest)
      (by ac_rfl)
      fun s5 hpc5 hrun5 hsp5 htr5 hcl5 hx1_5 hx8_5 hregs5 => ?_
    have halign5 : s5.spAligned = true := by simpa only [State.spAligned, hsp5, hsp] using halign
    have hfp5 : s5.readReg64 .fp = sp + 272#64 := by reg_chain
    have hx21_5 : (s5.readReg64 .x21).setWidth 32 = x.spk := by reg_chain
    refine step_preKeyMsg_tag6_placed hshim halloc hrealloc hpanic x g sp s0 hwf hcl5 hpc5 hrun5 hsp5 halign5 htr5 hfp5
      hx1_5 hx8_5 hx21_5
      (F := (sp ↦₆₄ g.msgCopyPtr) ∗ ((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗ ((sp + 24#64) ↦₃₂ x.regId) ∗
        ((sp + 44#64) ↦₃₂ g.kyberId32) ∗ ((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗
        ((sp + 56#64) ↦₆₄ x.bkA) ∗ ((sp + 72#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
        boxU8Buf A g.bkSerPtr x.baseKey.serialize ∗ boxU8Buf A g.ikSerPtr x.ik.serialize ∗
        boxU8Buf A g.msgCopyPtr x.msg.serialized ∗ optKyberCopyBuf A g.kyberCopyPtr x.kp ∗ F_rest)
      (by ac_rfl)
      fun s6 hpc6 hrun6 hsp6 htr6 hcl6 hregs6 => ?_
    have halign6 : s6.spAligned = true := by simpa only [State.spAligned, hsp6, hsp] using halign
    have hfp6 : s6.readReg64 .fp = sp + 272#64 := by reg_chain
    refine step_preKeyMsg_tag7_placed hshim halloc hrealloc hpanic x g sp s0 hwf hcl6 hpc6 hrun6 hsp6 halign6 htr6 hfp6
      (F := (sp ↦₆₄ g.msgCopyPtr) ∗ ((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗ ((sp + 24#64) ↦₃₂ x.regId) ∗
        ((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗ ((sp + 56#64) ↦₆₄ x.bkA) ∗
        boxU8Buf A g.bkSerPtr x.baseKey.serialize ∗ boxU8Buf A g.ikSerPtr x.ik.serialize ∗
        boxU8Buf A g.msgCopyPtr x.msg.serialized ∗ optKyberCopyBuf A g.kyberCopyPtr x.kp ∗ F_rest)
      (by ac_rfl)
      fun s7 hpc7 hrun7 hsp7 htr7 hcl7 hregs7 => ?_
    have halign7 : s7.spAligned = true := by simpa only [State.spAligned, hsp7, hsp] using halign
    have hfp7 : s7.readReg64 .fp = sp + 272#64 := by reg_chain
    have hx19_7 : s7.readReg64 .x19 =
        (match x.kp with | none => noneCap | some k => BitVec.ofNat 64 k.ciphertext.length) :=
      (show s7.readReg64 .x19 = s.readReg64 .x19 by reg_chain).trans hx19
    refine step_preKeyMsg_tag8_placed hshim halloc hrealloc hmemcpy hpanic x g sp s0 hwf hcl7 hpc7 hrun7 hsp7 halign7 htr7 hfp7 hx19_7
      (F := (sp ↦₆₄ g.msgCopyPtr) ∗ ((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗ ((sp + 24#64) ↦₃₂ x.regId) ∗
        ((sp + 44#64) ↦₃₂ g.kyberId32) ∗ ((sp + 72#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
        boxU8Buf A g.bkSerPtr x.baseKey.serialize ∗ boxU8Buf A g.ikSerPtr x.ik.serialize ∗
        boxU8Buf A g.msgCopyPtr x.msg.serialized ∗ F_rest)
      (by ac_rfl)
      fun s8 lenW hpc8 hrun8 hsp8 htr8 hcl8 hx8_8 hx23_8 hx26_8 hregs8 => ?_
    apply SepWPp.done hpc8 hrun8
    refine ⟨hsp8, htr8, hcl8, hx8_8, ?_, hx26_8, by reg_chain, lenW, ?_⟩
    · rw [serPrefix8_eq_model_serialized x] at hx23_8; exact hx23_8
    · rw [serPrefix8_eq_model_serialized x]
      have hopen8 := preKeyMsgFrameSlotsAt_open_buf A x g s0 lenW x.model.serialized
      rw [hopen8]
      dsimp only [F_rest, sp]
      ac_rfl
  intro hL
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, hspf, htrf, hclf, hx8f, hx23f, hx26f, hregsf, lenW, hPf⟩ | ⟨hpan, P_f, hmf, hp⟩ | ⟨_, _hoom⟩⟩ :=
    hwp R hmem_init hL
  · refine ⟨sf, hsteps, Or.inl ?_⟩
    have halignf : sf.spAligned = true := by simpa only [State.spAligned, hspf, hsp] using halign
    refine ⟨hpcf, hclf, hwf, ?_, hx8f, hx23f, hx26f, lenW, ?_⟩
    · exact ⟨hrunf, hspf, halign0, halignf, htrf, by reg_chain⟩
    · rw [hPf, sepConj_assoc] at hmf
      exact hmf
  · have hpan' : sf.status = .Panicked := by simpa [Rust.panicked] using hpan
    exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inl ⟨hpan', hp R hmf⟩))⟩
  · dsimp only at _hoom
    exact (not_satisfies_false_sepConj _hoom).elim

end Placed

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncode
