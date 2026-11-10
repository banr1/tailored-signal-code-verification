/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodeTags1To4
import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodeDecodes
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodeVarintBase
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

/-!
# `PreKeySignalMessage::new` Field Encoding: Tags 4–7

Symbolic execution steps for protobuf tags 4 (`message`), 5 (`registration_id`),
6 (`signed_pre_key_id`), and 7 (`kyber_pre_key_id`) (`+0x35c..+0x450`).
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

/-! ## Tag 4 (`message`, `+0x35c..+0x3b8`) -/

theorem step_preKeyMsg_tag4_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hMc : HookSat ext memcpyName (sessionMemcpySpec allocHookStack))
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64)
    (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 860#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : s.spAligned = true)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (serPrefix3 x).length)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length)
    (hP : P = ((sp ↦₆₄ g.msgCopyPtr) ∗
      ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix3 x).length) ∗
      vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix3 x) ∗
      boxU8Buf A g.msgCopyPtr x.msg.serialized ∗
      A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 952#64 →
      sm.status = .Running →
      sm.sp = sp →
      sm.trace = s.trace →
      sm.readReg64 .x23 = BitVec.ofNat 64 (serPrefix4 x).length →
      sm.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length →
      PreKeyMsgTagRegs s sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        (((sp ↦₆₄ g.msgCopyPtr) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix4 x).length) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix4 x) ∗
          boxU8Buf A g.msgCopyPtr x.msg.serialized ∗
          A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q Qp := by
  rcases hwf with ⟨hser_lt, _⟩
  have hcap_toNat : (BitVec.ofNat 64 x.model.serialized.length).toNat = x.model.serialized.length := by
    simp only [BitVec.toNat_ofNat]; omega
  have ⟨h0_len, h01_le, h12_le, h23_le, h34_le, h45_le, h56_le, h67_le, h78_le, h8_len⟩ :=
    serPrefix_lengths_le x
  have hcap_pos : 0 < (BitVec.ofNat 64 x.model.serialized.length).toNat := by omega
  have hvar_pos : 1 ≤ (encodeVarint (BitVec.ofNat 64 x.msg.serialized.length)).length := by
    unfold encodeVarint encodeVarintAux; split <;> simp
  have hmsg_lt : x.msg.serialized.length < 2 ^ 64 := by
    have : x.msg.serialized.length ≤ (serPrefix4 x).length := by
      simp [serPrefix4, LibsignalSessionApi.Prost.bytesField]; omega
    omega
  have hser4 : (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length)) ++
      x.msg.serialized = serPrefix4 x := by
    rw [serPrefix4, prost_bytesField_some 4 x.msg.serialized hmsg_lt, prost_key_4_2]
    simp only [← List.append_assoc, List.singleton_append]
  have h4_len : (serPrefix4 x).length = (serPrefix3 x).length + 1 +
      (encodeVarint (BitVec.ofNat 64 x.msg.serialized.length)).length + x.msg.serialized.length := by
    rw [← hser4, List.length_append, List.length_append, List.length_cons]; omega
  have hlt3 : (serPrefix3 x).length < (BitVec.ofNat 64 x.model.serialized.length).toNat := by omega
  have hbeq3 := cap_beq_len_false hlt3
  have hle_var : (serPrefix3 x ++ [34#8]).length +
      (encodeVarint (BitVec.ofNat 64 x.msg.serialized.length)).length ≤
      (BitVec.ofNat 64 x.model.serialized.length).toNat := by
    rw [List.length_append, List.length_singleton]; omega
  have hle_slice : (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length)).length +
      x.msg.serialized.length ≤ (BitVec.ofNat 64 x.model.serialized.length).toNat := by
    rw [List.length_append, List.length_cons]; omega
  subst hP
  rw [vecU8Buf_eq_open_one A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix3 x) hlt3]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun y => ?_
  have hf860 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 860)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x1548c
  have hf864 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 864)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15490
  have hf868 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 868)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15494
  have hf872 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 872)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15498
  have hf876 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 876)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x1549c
  have hf880 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 880)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x154a0
  have hf884 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 884)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x154a4
  have hf888 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 888)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x154a8
  have hf892 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 892)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x154ac
  have hf896 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 896)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x154b0
  revert hpc hf860 hf864 hf868 hf872 hf876 hf880 hf884 hf888 hf892 hf896
  generalize h_entry1 : (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName = entry1
  intro hpc hf860 hf864 hf868 hf872 hf876 hf880 hf884 hf888 hf892 hf896
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry1 + 18446744073709477744#64)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  rw [← h_entry1]; clear h_entry1
  rw [vecU8Buf_snoc_eq A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix3 x) 34#8 hlt3,
    bv_len_add_one (serPrefix3 x) 34#8]
  refine step_call_encVarint_trap b A ext (BitVec.ofNat 64 x.msg.serialized.length) (sp + 224#64)
    (BitVec.ofNat 64 x.model.serialized.length) g.serPtr sp
    ((tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 900#64)
    (serPrefix3 x ++ [34#8]) s.trace s hle_var
    (F := (sp ↦₆₄ g.msgCopyPtr) ∗ boxU8Buf A g.msgCopyPtr x.msg.serialized ∗ F)
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
  have hx27_1 : sf1.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length := by reg_chain
  have hult1 := cap_sub_len_ult_false hle_slice
  have hule1 := cap_sub_len_ule_true hle_slice
  have hf900 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 900)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x154b4
  have hf904 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 904)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x154b8
  have hf908 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 908)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x154bc
  have hf912 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 912)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x154c0
  have hf916 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 916)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x154c4
  have hf920 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 920)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x154c8
  by_cases hmsg_nil : x.msg.serialized = []
  · have hser4_nil : serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length) = serPrefix4 x := by
      simpa [hmsg_nil] using hser4
    have hmsg_bv0 : BitVec.ofNat 64 x.msg.serialized.length = 0#64 := by simp [hmsg_nil]
    clear hmsg_nil h4_len hser4
    rw [hser4_nil] at hult1 hule1 ⊢
    rw [hmsg_bv0] at hx27_1 hult1 hule1
    revert hnext hpcf1 hf900 hf904 hf908 hf912 hf916 hf920
    generalize (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName = entry2
    intro hnext hpcf1 hf900 hf904 hf908 hf912 hf916 hf920
    examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry2 + 952#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    have hpost_nil :
        (((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix4 x).length) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix4 x) ∗
          A.pool ∗ stackAt sp preKeyMsgSubStack) ∗
        ((sp ↦₆₄ g.msgCopyPtr) ∗ boxU8Buf A g.msgCopyPtr x.msg.serialized ∗ F) =
        (((sp ↦₆₄ g.msgCopyPtr) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix4 x).length) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix4 x) ∗
          boxU8Buf A g.msgCopyPtr x.msg.serialized ∗
          A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F) := by ac_rfl
    rw [hpost_nil]
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (PreKeyMsgTagRegs.trans hregs1 (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self]))
  · have hmsg_pos : 0 < x.msg.serialized.length := List.length_pos_of_ne_nil hmsg_nil
    have hmsg_beq := bv_len_beq_zero_false hmsg_pos hmsg_lt
    have hmsg_toNat : (BitVec.ofNat 64 x.msg.serialized.length).toNat = x.msg.serialized.length := by
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmsg_lt]
    rw [vecU8Buf_eq_open_slice A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
      (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length))
      x.msg.serialized.length hle_slice hcap_pos,
      boxU8Buf_nonempty_eq A g.msgCopyPtr x.msg.serialized hmsg_nil]
    have hf924 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 924)
      libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x154cc
    have hf928 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 928)
      libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x154d0
    have hf932 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 932)
      libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x154d4
    have hf936 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 936)
      libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x154d8
    have hf940 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 940)
      libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x154dc
    revert hpcf1 hf900 hf904 hf908 hf912 hf916 hf920 hf924 hf928 hf932 hf936 hf940
    generalize h_entry2 : (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName = entry2
    intro hpcf1 hf900 hf904 hf908 hf912 hf916 hf920 hf924 hf928 hf932 hf936 hf940
    examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry2 + bv% (ls_off% "memcpy" - 0x15130))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [← h_entry2]; clear h_entry2
    refine step_call_memcpy_ext b ext hMc
      (g.serPtr + BitVec.ofNat 64 (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length)).length)
      g.msgCopyPtr sp ((tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 944#64)
      (BitVec.ofNat 64 (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length)).length)
      (BitVec.ofNat 64 x.model.serialized.length)
      x.msg.serialized s.trace s
      (F := (sp ↦₆₄ g.msgCopyPtr) ∗
        ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
        (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
        (((sp + 224#64) + 16#64) ↦₆₄
          BitVec.ofNat 64 (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length)).length) ∗
        vecSliceRest A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
          (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length))
          x.msg.serialized.length ∗
        A.pool ∗
        (⌜g.msgCopyPtr ≠ 0#64 ∧ x.msg.serialized.length < 2 ^ 63⌝ ∗
          A.live g.msgCopyPtr x.msg.serialized.length 1) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simpa only [State.spAligned, arm64_norm, *] using halign1)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (PreKeyMsgTagRegs.trans hregs1 (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self]))
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by ac_rfl)
      fun sf2 hpcf2 hrunf2 hspf2 htrf2 hregs2 hx23_2 hx26_2 => ?_
    have hfp2 : sf2.readReg64 .fp = sp + 272#64 := by reg_chain
    have hx27_2 : sf2.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length := by reg_chain
    simp only [arm64_norm] at hx23_2 hx27_2
    have hadd_len :
        BitVec.ofNat 64 (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length)).length +
          BitVec.ofNat 64 x.msg.serialized.length =
        BitVec.ofNat 64 (serPrefix4 x).length := by
      simp only [h4_len, List.length_append, List.length_cons, BitVec.ofNat_add]
      ac_rfl
    clear h4_len
    have hpost_eq :
        (((g.serPtr + BitVec.ofNat 64 (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length)).length) ↦ₛ
            x.msg.serialized) ∗
          (g.msgCopyPtr ↦ₛ x.msg.serialized) ∗ stackAt sp preKeyMsgSubStack) ∗
        ((sp ↦₆₄ g.msgCopyPtr) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄
            BitVec.ofNat 64 (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length)).length) ∗
          vecSliceRest A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
            (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length))
            x.msg.serialized.length ∗
          A.pool ∗
          (⌜g.msgCopyPtr ≠ 0#64 ∧ x.msg.serialized.length < 2 ^ 63⌝ ∗
            A.live g.msgCopyPtr x.msg.serialized.length 1) ∗ F) =
        (((sp ↦₆₄ g.msgCopyPtr) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄
            BitVec.ofNat 64 (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length)).length) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix4 x) ∗
          boxU8Buf A g.msgCopyPtr x.msg.serialized ∗
          A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F) := by
      rw [← hser4,
        ← vecU8Buf_append_eq A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
          (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length))
          x.msg.serialized hcap_pos,
        boxU8Buf_nonempty_eq A g.msgCopyPtr x.msg.serialized hmsg_nil]
      ac_rfl
    rw [hpost_eq]
    have hf944 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 944)
      libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x154e0
    have hf948 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 948)
      libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x154e4
    revert hnext hpcf2 hf944 hf948
    generalize (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName = entry3
    intro hnext hpcf2 hf944 hf948
    examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry3 + 952#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (PreKeyMsgTagRegs.trans hregs2 (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self]))

theorem step_preKeyMsg_tag4_trap (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) (hmemcpy : Rust.withPanics ext "memcpy" = some hookMemcpy)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64) (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 860#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (halign : s.spAligned = true)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (serPrefix3 x).length)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length)
    (hP : P = ((sp ↦₆₄ g.msgCopyPtr) ∗
      ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix3 x).length) ∗
      vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix3 x) ∗
      boxU8Buf A g.msgCopyPtr x.msg.serialized ∗ A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 952#64 →
      sm.status = .Running → sm.sp = sp → sm.trace = s.trace →
      sm.readReg64 .x23 = BitVec.ofNat 64 (serPrefix4 x).length →
      sm.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length →
      PreKeyMsgTagRegs s sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        (((sp ↦₆₄ g.msgCopyPtr) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix4 x).length) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix4 x) ∗
          boxU8Buf A g.msgCopyPtr x.msg.serialized ∗ A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q Qp :=
  step_preKeyMsg_tag4_ext b A ext (hookSat_memcpy_of_withPanics hmemcpy) x g sp hwf
    hpc hrun hsp halign hfp hx23 hx26 hx27 hP hnext

theorem step_preKeyMsg_tag4 (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64)
    (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName + 860#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : s.spAligned = true)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (serPrefix3 x).length)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length)
    (hP : P = ((sp ↦₆₄ g.msgCopyPtr) ∗
      ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix3 x).length) ∗
      vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix3 x) ∗
      boxU8Buf A g.msgCopyPtr x.msg.serialized ∗
      A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName + 952#64 →
      sm.status = .Running →
      sm.sp = sp →
      sm.trace = s.trace →
      sm.readReg64 .x23 = BitVec.ofNat 64 (serPrefix4 x).length →
      sm.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length →
      PreKeyMsgTagRegs s sm →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        (((sp ↦₆₄ g.msgCopyPtr) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix4 x).length) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix4 x) ∗
          boxU8Buf A g.msgCopyPtr x.msg.serialized ∗
          A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q Qp :=
  step_preKeyMsg_tag4_trap b A (tripleRatchetExterns C ctl abs) rfl x g sp hwf hpc hrun hsp halign hfp hx23 hx26 hx27 hP hnext

/-! ## Tag 5 (`registration_id`, `+0x3b8..+0x3ec`) -/

theorem step_preKeyMsg_tag5_trap (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64)
    (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 952#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : s.spAligned = true)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (serPrefix4 x).length)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length)
    (hP : P = (((sp + 24#64) ↦₃₂ x.regId) ∗
      ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix4 x).length) ∗
      vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix4 x) ∗
      A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 1004#64 →
      sm.status = .Running →
      sm.sp = sp →
      sm.trace = s.trace →
      sm.readReg64 .x1 = BitVec.ofNat 64 (serPrefix5 x).length →
      sm.readReg64 .x8 = BitVec.ofNat 64 x.model.serialized.length →
      PreKeyMsgTagRegs s sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((((sp + 24#64) ↦₃₂ x.regId) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix5 x).length) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix5 x) ∗
          A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q Qp := by
  rcases hwf with ⟨hser_lt, _⟩
  have hcap_toNat : (BitVec.ofNat 64 x.model.serialized.length).toNat = x.model.serialized.length := by
    simp only [BitVec.toNat_ofNat]; omega
  have ⟨h0_len, h01_le, h12_le, h23_le, h34_le, h45_le, h56_le, h67_le, h78_le, h8_len⟩ :=
    serPrefix_lengths_le x
  have hvar_pos : 1 ≤ (encodeVarint (x.regId.zeroExtend 64)).length := by
    unfold encodeVarint encodeVarintAux; split <;> simp
  have hser5 : (serPrefix4 x ++ [40#8]) ++ encodeVarint (x.regId.zeroExtend 64) = serPrefix5 x := by
    simp [serPrefix5, prost_uint32Field_some, prost_key_5_0, List.append_assoc]
  have h5_len : (serPrefix5 x).length = (serPrefix4 x).length + 1 +
      (encodeVarint (x.regId.zeroExtend 64)).length := by
    rw [← hser5, List.length_append, List.length_append, List.length_singleton]
  have hlt4 : (serPrefix4 x).length < (BitVec.ofNat 64 x.model.serialized.length).toNat := by omega
  have hbeq4 := cap_beq_len_false hlt4
  have hle_var : (serPrefix4 x ++ [40#8]).length +
      (encodeVarint (x.regId.zeroExtend 64)).length ≤
      (BitVec.ofNat 64 x.model.serialized.length).toNat := by
    rw [List.length_append, List.length_singleton]; omega
  subst hP
  rw [vecU8Buf_eq_open_one A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix4 x) hlt4]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun y => ?_
  have hf952 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 952)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x154e8
  have hf956 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 956)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x154ec
  have hf960 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 960)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x154f0
  have hf964 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 964)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x154f4
  have hf968 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 968)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x154f8
  have hf972 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 972)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x154fc
  have hf976 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 976)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15500
  have hf980 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 980)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15504
  have hf984 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 984)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15508
  have hf988 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 988)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x1550c
  have hf992 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 992)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15510
  revert hpc hf952 hf956 hf960 hf964 hf968 hf972 hf976 hf980 hf984 hf988 hf992
  generalize h_entry1 : (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName = entry1
  intro hpc hf952 hf956 hf960 hf964 hf968 hf972 hf976 hf980 hf984 hf988 hf992
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry1 + 18446744073709477744#64)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  rw [← h_entry1]; clear h_entry1
  rw [vecU8Buf_snoc_eq A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix4 x) 40#8 hlt4,
    bv_len_add_one (serPrefix4 x) 40#8]
  refine step_call_encVarint_trap b A ext (x.regId.zeroExtend 64) (sp + 224#64)
    (BitVec.ofNat 64 x.model.serialized.length) g.serPtr sp
    ((tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 996#64)
    (serPrefix4 x ++ [40#8]) s.trace s hle_var
    (F := ((sp + 24#64) ↦₃₂ x.regId) ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simpa only [State.spAligned, arm64_norm, *] using halign)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by ac_rfl)
    fun sf1 hpcf1 hrunf1 hspf1 htrf1 hregs1 => ?_
  have hfp1 : sf1.readReg64 .fp = sp + 272#64 := by reg_chain
  rw [hser5]
  have hpost_eq :
      (((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
        (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
        (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix5 x).length) ∗
        vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix5 x) ∗
        A.pool ∗ stackAt sp preKeyMsgSubStack) ∗
      (((sp + 24#64) ↦₃₂ x.regId) ∗ F) =
      ((((sp + 24#64) ↦₃₂ x.regId) ∗
        ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
        (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
        (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix5 x).length) ∗
        vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix5 x) ∗
        A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F) := by ac_rfl
  rw [hpost_eq]
  have hf996 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 996)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15514
  have hf1000 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 1000)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15518
  revert hnext hpcf1 hf996 hf1000
  generalize (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName = entry2
  intro hnext hpcf1 hf996 hf1000
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry2 + 1004#64)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (PreKeyMsgTagRegs.trans hregs1 (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self]))

theorem step_preKeyMsg_tag5 (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64)
    (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName + 952#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : s.spAligned = true)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (serPrefix4 x).length)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length)
    (hP : P = (((sp + 24#64) ↦₃₂ x.regId) ∗
      ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix4 x).length) ∗
      vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix4 x) ∗
      A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName + 1004#64 →
      sm.status = .Running →
      sm.sp = sp →
      sm.trace = s.trace →
      sm.readReg64 .x1 = BitVec.ofNat 64 (serPrefix5 x).length →
      sm.readReg64 .x8 = BitVec.ofNat 64 x.model.serialized.length →
      PreKeyMsgTagRegs s sm →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        ((((sp + 24#64) ↦₃₂ x.regId) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix5 x).length) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix5 x) ∗
          A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q Qp :=
  step_preKeyMsg_tag5_trap b A (tripleRatchetExterns C ctl abs) x g sp hwf hpc hrun hsp halign hfp hx23 hx26 hP hnext

/-! ## Tag 6 (`signed_pre_key_id`, `+0x3ec..+0x414`) -/

theorem step_preKeyMsg_tag6_trap (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64)
    (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 1004#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : s.spAligned = true)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (serPrefix5 x).length)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 x.model.serialized.length)
    (hx21 : (s.readReg64 .x21).setWidth 32 = x.spk)
    (hP : P = (((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix5 x).length) ∗
      vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix5 x) ∗
      A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 1044#64 →
      sm.status = .Running →
      sm.sp = sp →
      sm.trace = s.trace →
      PreKeyMsgTagRegs s sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix6 x).length) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix6 x) ∗
          A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q Qp := by
  rcases hwf with ⟨hser_lt, _⟩
  have hcap_toNat : (BitVec.ofNat 64 x.model.serialized.length).toNat = x.model.serialized.length := by
    simp only [BitVec.toNat_ofNat]; omega
  have ⟨h0_len, h01_le, h12_le, h23_le, h34_le, h45_le, h56_le, h67_le, h78_le, h8_len⟩ :=
    serPrefix_lengths_le x
  have hw21 : s.readReg32 .x21 = x.spk := by simpa [State.readReg32] using hx21
  have hvar_pos : 1 ≤ (encodeVarint (x.spk.zeroExtend 64)).length := by
    unfold encodeVarint encodeVarintAux; split <;> simp
  have hser6 : (serPrefix5 x ++ [48#8]) ++ encodeVarint (x.spk.zeroExtend 64) = serPrefix6 x := by
    simp [serPrefix6, prost_uint32Field_some, prost_key_6_0, List.append_assoc]
  have h6_len : (serPrefix6 x).length = (serPrefix5 x).length + 1 +
      (encodeVarint (x.spk.zeroExtend 64)).length := by
    rw [← hser6, List.length_append, List.length_append, List.length_singleton]
  have hlt5 : (serPrefix5 x).length < (BitVec.ofNat 64 x.model.serialized.length).toNat := by omega
  have hbeq5 := cap_beq_len_false hlt5
  have hle_var : (serPrefix5 x ++ [48#8]).length +
      (encodeVarint (x.spk.zeroExtend 64)).length ≤
      (BitVec.ofNat 64 x.model.serialized.length).toNat := by
    rw [List.length_append, List.length_singleton]; omega
  subst hP
  rw [vecU8Buf_eq_open_one A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix5 x) hlt5]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun y => ?_
  have hf1004 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 1004)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x1551c
  have hf1008 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 1008)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15520
  have hf1012 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 1012)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15524
  have hf1016 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 1016)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15528
  have hf1020 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 1020)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x1552c
  have hf1024 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 1024)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15530
  have hf1028 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 1028)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15534
  have hf1032 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 1032)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15538
  have hf1036 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 1036)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x1553c
  have hf1040 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 1040)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15540
  revert hpc hf1004 hf1008 hf1012 hf1016 hf1020 hf1024 hf1028 hf1032 hf1036 hf1040
  generalize h_entry1 : (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName = entry1
  intro hpc hf1004 hf1008 hf1012 hf1016 hf1020 hf1024 hf1028 hf1032 hf1036 hf1040
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry1 + 18446744073709477744#64)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  rw [← h_entry1]; clear h_entry1
  rw [vecU8Buf_snoc_eq A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix5 x) 48#8 hlt5,
    bv_len_add_one (serPrefix5 x) 48#8]
  refine step_call_encVarint_trap b A ext (x.spk.zeroExtend 64) (sp + 224#64)
    (BitVec.ofNat 64 x.model.serialized.length) g.serPtr sp
    ((tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 1044#64)
    (serPrefix5 x ++ [48#8]) s.trace s hle_var
    (F := F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simpa only [State.spAligned, arm64_norm, *] using halign)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by ac_rfl)
    fun sf1 hpcf1 hrunf1 hspf1 htrf1 hregs1 => ?_
  rw [hser6]
  exact hnext sf1 hpcf1 hrunf1 hspf1 htrf1 hregs1

theorem step_preKeyMsg_tag6 (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64)
    (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName + 1004#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : s.spAligned = true)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (serPrefix5 x).length)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 x.model.serialized.length)
    (hx21 : (s.readReg64 .x21).setWidth 32 = x.spk)
    (hP : P = (((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix5 x).length) ∗
      vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix5 x) ∗
      A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName + 1044#64 →
      sm.status = .Running →
      sm.sp = sp →
      sm.trace = s.trace →
      PreKeyMsgTagRegs s sm →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        ((((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix6 x).length) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix6 x) ∗
          A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q Qp :=
  step_preKeyMsg_tag6_trap b A (tripleRatchetExterns C ctl abs) x g sp hwf hpc hrun hsp halign hfp hx1 hx8 hx21 hP hnext

/-! ## Tag 7 (`kyber_pre_key_id`, `+0x414..+0x450`) -/

theorem step_preKeyMsg_tag7_trap (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64)
    (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 1044#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : s.spAligned = true)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hP : P = (((sp + 44#64) ↦₃₂ g.kyberId32) ∗
      ((sp + 72#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
      ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix6 x).length) ∗
      vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix6 x) ∗
      A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 1104#64 →
      sm.status = .Running →
      sm.sp = sp →
      sm.trace = s.trace →
      PreKeyMsgTagRegs s sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((((sp + 44#64) ↦₃₂ g.kyberId32) ∗
          ((sp + 72#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix7 x).length) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix7 x) ∗
          A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q Qp := by
  have hf1044 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 1044)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15544
  have hf1048 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 1048)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15548
  rcases hwf with ⟨hser_lt, _, _, hkp_val⟩
  have hcap_toNat : (BitVec.ofNat 64 x.model.serialized.length).toNat = x.model.serialized.length := by
    simp only [BitVec.toNat_ofNat]; omega
  have ⟨h0_len, h01_le, h12_le, h23_le, h34_le, h45_le, h56_le, h67_le, h78_le, h8_len⟩ :=
    serPrefix_lengths_le x
  subst hP
  cases hkp : x.kp with
  | none =>
    have hser7 : serPrefix7 x = serPrefix6 x := by
      simp [serPrefix7, hkp, LibsignalSessionApi.Prost.uint32Field]
    simp only [hkp, Option.isSome, Bool.false_eq_true, ↓reduceIte] at hnext ⊢
    revert hpc hf1044 hf1048 hnext
    generalize (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName = entry0
    intro hpc hf1044 hf1048 hnext
    examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry0 + 1104#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [← hser7]
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self])
  | some k =>
    have hkid : g.kyberId32 = k.preKeyId := hkp_val k hkp
    have hser7 : (serPrefix6 x ++ [56#8]) ++ encodeVarint (k.preKeyId.zeroExtend 64) = serPrefix7 x := by
      simp [serPrefix7, hkp, prost_uint32Field_some, prost_key_7_0, List.append_assoc]
    have h7_len : (serPrefix7 x).length = (serPrefix6 x).length + 1 +
        (encodeVarint (k.preKeyId.zeroExtend 64)).length := by
      rw [← hser7, List.length_append, List.length_append, List.length_singleton]
    have hvar_pos : 1 ≤ (encodeVarint (k.preKeyId.zeroExtend 64)).length := by
      unfold encodeVarint encodeVarintAux; split <;> simp
    have hlt6 : (serPrefix6 x).length < (BitVec.ofNat 64 x.model.serialized.length).toNat := by omega
    have hbeq6 := cap_beq_len_false hlt6
    have hle_var : (serPrefix6 x ++ [56#8]).length +
        (encodeVarint (k.preKeyId.zeroExtend 64)).length ≤
        (BitVec.ofNat 64 x.model.serialized.length).toNat := by
      rw [List.length_append, List.length_singleton]; omega
    simp only [hkp, Option.isSome, ↓reduceIte] at hnext ⊢
    rw [vecU8Buf_eq_open_one A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix6 x) hlt6]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    have hf1052 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 1052)
      libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x1554c
    have hf1056 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 1056)
      libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15550
    have hf1060 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 1060)
      libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15554
    have hf1064 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 1064)
      libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15558
    have hf1068 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 1068)
      libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x1555c
    have hf1072 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 1072)
      libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15560
    have hf1076 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 1076)
      libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15564
    have hf1080 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 1080)
      libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15568
    have hf1084 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 1084)
      libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x1556c
    have hf1088 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 1088)
      libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15570
    have hf1092 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 1092)
      libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15574
    have hf1096 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 1096)
      libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15578
    have hf1100 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 1100)
      libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x1557c
    revert hpc hf1044 hf1048 hf1052 hf1056 hf1060 hf1064 hf1068 hf1072 hf1076 hf1080 hf1084 hf1088 hf1092 hf1096 hf1100
    generalize h_entry1 : (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName = entry1
    intro hpc hf1044 hf1048 hf1052 hf1056 hf1060 hf1064 hf1068 hf1072 hf1076 hf1080 hf1084 hf1088 hf1092 hf1096 hf1100
    examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry1 + 18446744073709477744#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [← h_entry1]; clear h_entry1
    rw [vecU8Buf_snoc_eq A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix6 x) 56#8 hlt6,
      bv_len_add_one (serPrefix6 x) 56#8]
    refine step_call_encVarint_trap b A ext (k.preKeyId.zeroExtend 64) (sp + 224#64)
      (BitVec.ofNat 64 x.model.serialized.length) g.serPtr sp
      ((tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 1104#64)
      (serPrefix6 x ++ [56#8]) s.trace s hle_var
      (F := ((sp + 44#64) ↦₃₂ g.kyberId32) ∗ ((sp + 72#64) ↦₃₂ 1#32) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simpa only [State.spAligned, arm64_norm, *] using halign)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by ac_rfl)
      fun sf1 hpcf1 hrunf1 hspf1 htrf1 hregs1 => ?_
    rw [hser7]
    have hpost_eq :
        (((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix7 x).length) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix7 x) ∗
          A.pool ∗ stackAt sp preKeyMsgSubStack) ∗
        (((sp + 44#64) ↦₃₂ g.kyberId32) ∗ ((sp + 72#64) ↦₃₂ 1#32) ∗ F) =
        ((((sp + 44#64) ↦₃₂ g.kyberId32) ∗
          ((sp + 72#64) ↦₃₂ 1#32) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix7 x).length) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix7 x) ∗
          A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F) := by ac_rfl
    rw [hpost_eq]
    exact hnext sf1 hpcf1 hrunf1 hspf1 htrf1 hregs1

theorem step_preKeyMsg_tag7 (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64)
    (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName + 1044#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : s.spAligned = true)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hP : P = (((sp + 44#64) ↦₃₂ g.kyberId32) ∗
      ((sp + 72#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
      ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix6 x).length) ∗
      vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix6 x) ∗
      A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName + 1104#64 →
      sm.status = .Running →
      sm.sp = sp →
      sm.trace = s.trace →
      PreKeyMsgTagRegs s sm →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        ((((sp + 44#64) ↦₃₂ g.kyberId32) ∗
          ((sp + 72#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix7 x).length) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix7 x) ∗
          A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q Qp :=
  step_preKeyMsg_tag7_trap b A (tripleRatchetExterns C ctl abs) x g sp hwf hpc hrun hsp halign hfp hP hnext

/-! ## Relocatable Placement Proofs -/

section Placed

open CryptoVerification.LibsignalPublicApi.Placed

set_option maxRecDepth 200000
attribute [local irreducible] Program.fetch Program.externAt?

theorem step_preKeyMsg_tag4_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hmemcpy : HookSat H "memcpy" framelessMemcpySpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64) (s_base : State)
    (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_41).base + 860#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (halign : s.spAligned = true) (htr : s.trace = s_base.trace)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (serPrefix3 x).length)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length)
    (hP : P = ((sp ↦₆₄ g.msgCopyPtr) ∗
      ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix3 x).length) ∗
      vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix3 x) ∗
      boxU8Buf A g.msgCopyPtr x.msg.serialized ∗
      A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State, sm.pc = (blkPl_41).base + 952#64 → sm.status = .Running →
      sm.sp = sp → sm.trace = s_base.trace → LibsignalCodeLoaded lsmpl sm.mem →
      sm.readReg64 .x23 = BitVec.ofNat 64 (serPrefix4 x).length →
      sm.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length →
      PreKeyMsgTagRegs s sm →
      SepWPp (lsProg_41 H) ret sm
        (((sp ↦₆₄ g.msgCopyPtr) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix4 x).length) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix4 x) ∗
          boxU8Buf A g.msgCopyPtr x.msg.serialized ∗
          A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
        Q (EncodePanicPost s_base)) :
    SepWPp (lsProg_41 H) ret s P Q (EncodePanicPost s_base) := by
  rcases hwf with ⟨hser_lt, _⟩
  have hcap_toNat : (BitVec.ofNat 64 x.model.serialized.length).toNat = x.model.serialized.length := by
    simp only [BitVec.toNat_ofNat]; omega
  have ⟨h0_len, h01_le, h12_le, h23_le, h34_le, h45_le, h56_le, h67_le, h78_le, h8_len⟩ :=
    serPrefix_lengths_le x
  have hcap_pos : 0 < (BitVec.ofNat 64 x.model.serialized.length).toNat := by omega
  have hvar_pos : 1 ≤ (encodeVarint (BitVec.ofNat 64 x.msg.serialized.length)).length := by
    unfold encodeVarint encodeVarintAux; split <;> simp
  have hmsg_lt : x.msg.serialized.length < 2 ^ 64 := by
    have : x.msg.serialized.length ≤ (serPrefix4 x).length := by
      simp [serPrefix4, LibsignalSessionApi.Prost.bytesField]; omega
    omega
  have hser4 : (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length)) ++
      x.msg.serialized = serPrefix4 x := by
    rw [serPrefix4, prost_bytesField_some 4 x.msg.serialized hmsg_lt, prost_key_4_2]
    simp only [← List.append_assoc, List.singleton_append]
  have h4_len : (serPrefix4 x).length = (serPrefix3 x).length + 1 +
      (encodeVarint (BitVec.ofNat 64 x.msg.serialized.length)).length + x.msg.serialized.length := by
    rw [← hser4, List.length_append, List.length_append, List.length_cons]; omega
  have hlt3 : (serPrefix3 x).length < (BitVec.ofNat 64 x.model.serialized.length).toNat := by omega
  have hbeq3 := cap_beq_len_false hlt3
  have hle_var : (serPrefix3 x ++ [34#8]).length +
      (encodeVarint (BitVec.ofNat 64 x.msg.serialized.length)).length ≤
      (BitVec.ofNat 64 x.model.serialized.length).toNat := by
    rw [List.length_append, List.length_singleton]; omega
  have hle_slice : (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length)).length +
      x.msg.serialized.length ≤ (BitVec.ofNat 64 x.model.serialized.length).toNat := by
    rw [List.length_append, List.length_cons]; omega
  subst hP
  rw [vecU8Buf_eq_open_one A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix3 x) hlt3]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_lscl hcl (mid := (blkPl_10).base); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, *])
  intro hcl0
  rw [vecU8Buf_snoc_eq A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix3 x) 34#8 hlt3,
    bv_len_add_one (serPrefix3 x) 34#8]
  refine step_call_encVarint_placed hshim halloc hrealloc hpanic
    (BitVec.ofNat 64 x.msg.serialized.length) (sp + 224#64)
    (BitVec.ofNat 64 x.model.serialized.length) g.serPtr sp
    ((blkPl_41).base + 900#64) (serPrefix3 x ++ [34#8]) s_base s hle_var (by omega)
    (F := (sp ↦₆₄ g.msgCopyPtr) ∗ boxU8Buf A g.msgCopyPtr x.msg.serialized ∗ F) hcl0
    (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simpa only [State.spAligned, arm64_norm, *] using halign)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by ac_rfl)
    fun sf1 hpcf1 hrunf1 hspf1 htrf1 hclf1 hregs1 => ?_
  simp only [List.append_assoc, List.singleton_append]
  have halign1 : sf1.spAligned = true := by simpa only [State.spAligned, hspf1, hsp] using halign
  have hfp1 : sf1.readReg64 .fp = sp + 272#64 := by reg_chain
  have hx27_1 : sf1.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length := by reg_chain
  have hult1 := cap_sub_len_ult_false hle_slice
  have hule1 := cap_sub_len_ule_true hle_slice
  by_cases hmsg_nil : x.msg.serialized = []
  · have hser4_nil : serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length) = serPrefix4 x := by
      simpa [hmsg_nil] using hser4
    have hmsg_bv0 : BitVec.ofNat 64 x.msg.serialized.length = 0#64 := by simp [hmsg_nil]
    clear hmsg_nil h4_len hser4
    rw [hser4_nil] at hult1 hule1 ⊢
    rw [hmsg_bv0] at hx27_1 hult1 hule1
    apply SepWPp.of_sepWP_lscl hclf1 (mid := (blkPl_41).base + 952#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hclf2
    have hpost_nil :
        (((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix4 x).length) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix4 x) ∗
          A.pool ∗ stackAt sp preKeyMsgSubStack) ∗
        ((sp ↦₆₄ g.msgCopyPtr) ∗ boxU8Buf A g.msgCopyPtr x.msg.serialized ∗ F) =
        (((sp ↦₆₄ g.msgCopyPtr) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix4 x).length) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix4 x) ∗
          boxU8Buf A g.msgCopyPtr x.msg.serialized ∗
          A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F) := by ac_rfl
    rw [hpost_nil]
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hclf2
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (PreKeyMsgTagRegs.trans hregs1 (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self]))
  · have hmsg_pos : 0 < x.msg.serialized.length := List.length_pos_of_ne_nil hmsg_nil
    have hmsg_beq := bv_len_beq_zero_false hmsg_pos hmsg_lt
    have hmsg_toNat : (BitVec.ofNat 64 x.msg.serialized.length).toNat = x.msg.serialized.length := by
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmsg_lt]
    rw [vecU8Buf_eq_open_slice A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
      (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length))
      x.msg.serialized.length hle_slice hcap_pos,
      boxU8Buf_nonempty_eq A g.msgCopyPtr x.msg.serialized hmsg_nil]
    apply SepWPp.of_sepWP_lscl hclf1 (mid := lsρ "memcpy"); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hclf1'
    refine step_call_memcpy_placed hmemcpy
      (g.serPtr + BitVec.ofNat 64 (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length)).length)
      g.msgCopyPtr sp ((blkPl_41).base + 944#64)
      (BitVec.ofNat 64 (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length)).length)
      (BitVec.ofNat 64 x.model.serialized.length)
      x.msg.serialized s_base.trace s
      (F := (sp ↦₆₄ g.msgCopyPtr) ∗
        ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
        (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
        (((sp + 224#64) + 16#64) ↦₆₄
          BitVec.ofNat 64 (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length)).length) ∗
        vecSliceRest A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
          (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length))
          x.msg.serialized.length ∗
        A.pool ∗ stackAt sp preKeyMsgSubStack ∗
        (⌜g.msgCopyPtr ≠ 0#64 ∧ x.msg.serialized.length < 2 ^ 63⌝ ∗
          A.live g.msgCopyPtr x.msg.serialized.length 1) ∗ F)
      hclf1' (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simpa only [State.spAligned, arm64_norm, *] using halign1)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (PreKeyMsgTagRegs.trans hregs1 (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self]))
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl)
      fun sf2 hpcf2 hrunf2 hspf2 htrf2 hclf2 hregs2 hx23_2 hx26_2 => ?_
    have hfp2 : sf2.readReg64 .fp = sp + 272#64 := by reg_chain
    have hx27_2 : sf2.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length := by reg_chain
    simp only [arm64_norm] at hx23_2 hx27_2
    have hadd_len :
        BitVec.ofNat 64 (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length)).length +
          BitVec.ofNat 64 x.msg.serialized.length =
        BitVec.ofNat 64 (serPrefix4 x).length := by
      simp only [h4_len, List.length_append, List.length_cons, BitVec.ofNat_add]
      ac_rfl
    clear h4_len
    have hpost_eq :
        (((g.serPtr + BitVec.ofNat 64 (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length)).length) ↦ₛ
            x.msg.serialized) ∗
          (g.msgCopyPtr ↦ₛ x.msg.serialized)) ∗
        ((sp ↦₆₄ g.msgCopyPtr) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄
            BitVec.ofNat 64 (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length)).length) ∗
          vecSliceRest A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
            (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length))
            x.msg.serialized.length ∗
          A.pool ∗ stackAt sp preKeyMsgSubStack ∗
          (⌜g.msgCopyPtr ≠ 0#64 ∧ x.msg.serialized.length < 2 ^ 63⌝ ∗
            A.live g.msgCopyPtr x.msg.serialized.length 1) ∗ F) =
        (((sp ↦₆₄ g.msgCopyPtr) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄
            BitVec.ofNat 64 (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length)).length) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix4 x) ∗
          boxU8Buf A g.msgCopyPtr x.msg.serialized ∗
          A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F) := by
      rw [← hser4,
        ← vecU8Buf_append_eq A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
          (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length))
          x.msg.serialized hcap_pos,
        boxU8Buf_nonempty_eq A g.msgCopyPtr x.msg.serialized hmsg_nil]
      ac_rfl
    rw [hpost_eq]
    apply SepWPp.of_sepWP_lscl hclf2 (mid := (blkPl_41).base + 952#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hclf3
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hclf3
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (PreKeyMsgTagRegs.trans hregs2 (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self]))

theorem step_preKeyMsg_tag5_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64) (s_base : State)
    (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_41).base + 952#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (halign : s.spAligned = true) (htr : s.trace = s_base.trace)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (serPrefix4 x).length)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length)
    (hP : P = (((sp + 24#64) ↦₃₂ x.regId) ∗
      ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix4 x).length) ∗
      vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix4 x) ∗
      A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State, sm.pc = (blkPl_41).base + 1004#64 → sm.status = .Running →
      sm.sp = sp → sm.trace = s_base.trace → LibsignalCodeLoaded lsmpl sm.mem →
      sm.readReg64 .x1 = BitVec.ofNat 64 (serPrefix5 x).length →
      sm.readReg64 .x8 = BitVec.ofNat 64 x.model.serialized.length →
      PreKeyMsgTagRegs s sm →
      SepWPp (lsProg_41 H) ret sm
        ((((sp + 24#64) ↦₃₂ x.regId) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix5 x).length) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix5 x) ∗
          A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
        Q (EncodePanicPost s_base)) :
    SepWPp (lsProg_41 H) ret s P Q (EncodePanicPost s_base) := by
  rcases hwf with ⟨hser_lt, _⟩
  have hcap_toNat : (BitVec.ofNat 64 x.model.serialized.length).toNat = x.model.serialized.length := by
    simp only [BitVec.toNat_ofNat]; omega
  have ⟨h0_len, h01_le, h12_le, h23_le, h34_le, h45_le, h56_le, h67_le, h78_le, h8_len⟩ :=
    serPrefix_lengths_le x
  have hvar_pos : 1 ≤ (encodeVarint (x.regId.zeroExtend 64)).length := by
    unfold encodeVarint encodeVarintAux; split <;> simp
  have hser5 : (serPrefix4 x ++ [40#8]) ++ encodeVarint (x.regId.zeroExtend 64) = serPrefix5 x := by
    simp [serPrefix5, prost_uint32Field_some, prost_key_5_0, List.append_assoc]
  have h5_len : (serPrefix5 x).length = (serPrefix4 x).length + 1 +
      (encodeVarint (x.regId.zeroExtend 64)).length := by
    rw [← hser5, List.length_append, List.length_append, List.length_singleton]
  have hlt4 : (serPrefix4 x).length < (BitVec.ofNat 64 x.model.serialized.length).toNat := by omega
  have hbeq4 := cap_beq_len_false hlt4
  have hle_var : (serPrefix4 x ++ [40#8]).length +
      (encodeVarint (x.regId.zeroExtend 64)).length ≤
      (BitVec.ofNat 64 x.model.serialized.length).toNat := by
    rw [List.length_append, List.length_singleton]; omega
  subst hP
  rw [vecU8Buf_eq_open_one A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix4 x) hlt4]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_lscl hcl (mid := (blkPl_10).base); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, *])
  intro hcl0
  rw [vecU8Buf_snoc_eq A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix4 x) 40#8 hlt4,
    bv_len_add_one (serPrefix4 x) 40#8]
  refine step_call_encVarint_placed hshim halloc hrealloc hpanic
    (x.regId.zeroExtend 64) (sp + 224#64)
    (BitVec.ofNat 64 x.model.serialized.length) g.serPtr sp
    ((blkPl_41).base + 996#64) (serPrefix4 x ++ [40#8]) s_base s hle_var (by omega)
    (F := ((sp + 24#64) ↦₃₂ x.regId) ∗ F) hcl0
    (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simpa only [State.spAligned, arm64_norm, *] using halign)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by ac_rfl)
    fun sf1 hpcf1 hrunf1 hspf1 htrf1 hclf1 hregs1 => ?_
  have hfp1 : sf1.readReg64 .fp = sp + 272#64 := by reg_chain
  rw [hser5]
  have hpost_eq :
      (((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
        (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
        (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix5 x).length) ∗
        vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix5 x) ∗
        A.pool ∗ stackAt sp preKeyMsgSubStack) ∗
      (((sp + 24#64) ↦₃₂ x.regId) ∗ F) =
      ((((sp + 24#64) ↦₃₂ x.regId) ∗
        ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
        (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
        (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix5 x).length) ∗
        vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix5 x) ∗
        A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F) := by ac_rfl
  rw [hpost_eq]
  apply SepWPp.of_sepWP_lscl hclf1 (mid := (blkPl_41).base + 1004#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hclf2
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hclf2
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (PreKeyMsgTagRegs.trans hregs1 (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self]))

theorem step_preKeyMsg_tag6_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64) (s_base : State)
    (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_41).base + 1004#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (halign : s.spAligned = true) (htr : s.trace = s_base.trace)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (serPrefix5 x).length)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 x.model.serialized.length)
    (hx21 : (s.readReg64 .x21).setWidth 32 = x.spk)
    (hP : P = (((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix5 x).length) ∗
      vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix5 x) ∗
      A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State, sm.pc = (blkPl_41).base + 1044#64 → sm.status = .Running →
      sm.sp = sp → sm.trace = s_base.trace → LibsignalCodeLoaded lsmpl sm.mem →
      PreKeyMsgTagRegs s sm →
      SepWPp (lsProg_41 H) ret sm
        ((((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix6 x).length) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix6 x) ∗
          A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
        Q (EncodePanicPost s_base)) :
    SepWPp (lsProg_41 H) ret s P Q (EncodePanicPost s_base) := by
  rcases hwf with ⟨hser_lt, _⟩
  have hcap_toNat : (BitVec.ofNat 64 x.model.serialized.length).toNat = x.model.serialized.length := by
    simp only [BitVec.toNat_ofNat]; omega
  have ⟨h0_len, h01_le, h12_le, h23_le, h34_le, h45_le, h56_le, h67_le, h78_le, h8_len⟩ :=
    serPrefix_lengths_le x
  have hw21 : s.readReg32 .x21 = x.spk := by simpa [State.readReg32] using hx21
  have hvar_pos : 1 ≤ (encodeVarint (x.spk.zeroExtend 64)).length := by
    unfold encodeVarint encodeVarintAux; split <;> simp
  have hser6 : (serPrefix5 x ++ [48#8]) ++ encodeVarint (x.spk.zeroExtend 64) = serPrefix6 x := by
    simp [serPrefix6, prost_uint32Field_some, prost_key_6_0, List.append_assoc]
  have h6_len : (serPrefix6 x).length = (serPrefix5 x).length + 1 +
      (encodeVarint (x.spk.zeroExtend 64)).length := by
    rw [← hser6, List.length_append, List.length_append, List.length_singleton]
  have hlt5 : (serPrefix5 x).length < (BitVec.ofNat 64 x.model.serialized.length).toNat := by omega
  have hbeq5 := cap_beq_len_false hlt5
  have hle_var : (serPrefix5 x ++ [48#8]).length +
      (encodeVarint (x.spk.zeroExtend 64)).length ≤
      (BitVec.ofNat 64 x.model.serialized.length).toNat := by
    rw [List.length_append, List.length_singleton]; omega
  subst hP
  rw [vecU8Buf_eq_open_one A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix5 x) hlt5]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_lscl hcl (mid := (blkPl_10).base); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, *])
  intro hcl0
  rw [vecU8Buf_snoc_eq A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix5 x) 48#8 hlt5,
    bv_len_add_one (serPrefix5 x) 48#8]
  refine step_call_encVarint_placed hshim halloc hrealloc hpanic
    (x.spk.zeroExtend 64) (sp + 224#64)
    (BitVec.ofNat 64 x.model.serialized.length) g.serPtr sp
    ((blkPl_41).base + 1044#64) (serPrefix5 x ++ [48#8]) s_base s hle_var (by omega)
    (F := F) hcl0
    (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simpa only [State.spAligned, arm64_norm, *] using halign)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by ac_rfl)
    fun sf1 hpcf1 hrunf1 hspf1 htrf1 hclf1 hregs1 => ?_
  rw [hser6]
  exact hnext sf1 hpcf1 hrunf1 hspf1 htrf1 hclf1 hregs1

theorem step_preKeyMsg_tag7_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64) (s_base : State)
    (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_41).base + 1044#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (halign : s.spAligned = true) (htr : s.trace = s_base.trace)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hP : P = (((sp + 44#64) ↦₃₂ g.kyberId32) ∗
      ((sp + 72#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
      ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix6 x).length) ∗
      vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix6 x) ∗
      A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State, sm.pc = (blkPl_41).base + 1104#64 → sm.status = .Running →
      sm.sp = sp → sm.trace = s_base.trace → LibsignalCodeLoaded lsmpl sm.mem →
      PreKeyMsgTagRegs s sm →
      SepWPp (lsProg_41 H) ret sm
        ((((sp + 44#64) ↦₃₂ g.kyberId32) ∗
          ((sp + 72#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix7 x).length) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix7 x) ∗
          A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
        Q (EncodePanicPost s_base)) :
    SepWPp (lsProg_41 H) ret s P Q (EncodePanicPost s_base) := by
  rcases hwf with ⟨hser_lt, _, _, hkp_val⟩
  have hcap_toNat : (BitVec.ofNat 64 x.model.serialized.length).toNat = x.model.serialized.length := by
    simp only [BitVec.toNat_ofNat]; omega
  have ⟨h0_len, h01_le, h12_le, h23_le, h34_le, h45_le, h56_le, h67_le, h78_le, h8_len⟩ :=
    serPrefix_lengths_le x
  subst hP
  cases hkp : x.kp with
  | none =>
    have hser7 : serPrefix7 x = serPrefix6 x := by
      simp [serPrefix7, hkp, LibsignalSessionApi.Prost.uint32Field]
    simp only [hkp, Option.isSome, Bool.false_eq_true, ↓reduceIte] at hnext ⊢
    apply SepWPp.of_sepWP_lscl hcl (mid := (blkPl_41).base + 1104#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl1
    rw [← hser7]
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl1
      (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self])
  | some k =>
    have hkid : g.kyberId32 = k.preKeyId := hkp_val k hkp
    have hser7 : (serPrefix6 x ++ [56#8]) ++ encodeVarint (k.preKeyId.zeroExtend 64) = serPrefix7 x := by
      simp [serPrefix7, hkp, prost_uint32Field_some, prost_key_7_0, List.append_assoc]
    have h7_len : (serPrefix7 x).length = (serPrefix6 x).length + 1 +
        (encodeVarint (k.preKeyId.zeroExtend 64)).length := by
      rw [← hser7, List.length_append, List.length_append, List.length_singleton]
    have hvar_pos : 1 ≤ (encodeVarint (k.preKeyId.zeroExtend 64)).length := by
      unfold encodeVarint encodeVarintAux; split <;> simp
    have hlt6 : (serPrefix6 x).length < (BitVec.ofNat 64 x.model.serialized.length).toNat := by omega
    have hbeq6 := cap_beq_len_false hlt6
    have hle_var : (serPrefix6 x ++ [56#8]).length +
        (encodeVarint (k.preKeyId.zeroExtend 64)).length ≤
        (BitVec.ofNat 64 x.model.serialized.length).toNat := by
      rw [List.length_append, List.length_singleton]; omega
    simp only [hkp, Option.isSome, ↓reduceIte] at hnext ⊢
    rw [vecU8Buf_eq_open_one A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix6 x) hlt6]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    apply SepWPp.of_sepWP_lscl hcl (mid := (blkPl_10).base); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, *])
    intro hcl0
    rw [vecU8Buf_snoc_eq A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix6 x) 56#8 hlt6,
      bv_len_add_one (serPrefix6 x) 56#8]
    refine step_call_encVarint_placed hshim halloc hrealloc hpanic
      (k.preKeyId.zeroExtend 64) (sp + 224#64)
      (BitVec.ofNat 64 x.model.serialized.length) g.serPtr sp
      ((blkPl_41).base + 1104#64) (serPrefix6 x ++ [56#8]) s_base s hle_var (by omega)
      (F := ((sp + 44#64) ↦₃₂ g.kyberId32) ∗ ((sp + 72#64) ↦₃₂ 1#32) ∗ F) hcl0
      (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simpa only [State.spAligned, arm64_norm, *] using halign)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by ac_rfl)
      fun sf1 hpcf1 hrunf1 hspf1 htrf1 hclf1 hregs1 => ?_
    rw [hser7]
    have hpost_eq :
        (((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix7 x).length) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix7 x) ∗
          A.pool ∗ stackAt sp preKeyMsgSubStack) ∗
        (((sp + 44#64) ↦₃₂ g.kyberId32) ∗ ((sp + 72#64) ↦₃₂ 1#32) ∗ F) =
        ((((sp + 44#64) ↦₃₂ g.kyberId32) ∗
          ((sp + 72#64) ↦₃₂ 1#32) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix7 x).length) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix7 x) ∗
          A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F) := by ac_rfl
    rw [hpost_eq]
    exact hnext sf1 hpcf1 hrunf1 hspf1 htrf1 hclf1 hregs1

end Placed

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncode
