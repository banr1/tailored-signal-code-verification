/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Record.Defs
import all Init.Data.String.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Record.FetchTail
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Record

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace SegTailRegReadSimp

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

end SegTailRegReadSimp

open SegTailRegReadSimp

/-! ## `.rodata` string `"decryption failed"` at `0x4f1a8` -/

private theorem rodata_0x451a8_eq :
    (libsignalSessionImage.data.drop
      (num% (ls_xref% (ls_off% "session_message_decrypt_signal" + 6324) (ls_off% "session_message_decrypt_signal" + 6328)) - num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)))).take 17 =
      decryptionFailedStr := by
  rfl_kernel

private theorem rodata_decryptionFailed_intro {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {m : Memory} {P : SepProp} (hro : img.RoDataLoaded m) (hP : m ⊨ P) :
    m ⊨ ((img.base + bv% (ls_xref% (ls_off% "session_message_decrypt_signal" + 6324) (ls_off% "session_message_decrypt_signal" + 6328))) ↦ᵣ decryptionFailedStr) ∗ P := by
  have h := ProofLib.Satisfies.of_rodata_loads himg
    (secOff := num% (ls_xref% (ls_off% "session_message_decrypt_signal" + 6324) (ls_off% "session_message_decrypt_signal" + 6328))) (secLen := 17)
    (dataOff := num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)))
    rfl (List.mem_of_elem_eq_true (by rfl_kernel)) (by decide) (by decide)
    (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) hro hP
  rwa [rodata_0x451a8_eq] at h

theorem decryptionFailedStr_split_shared_lb :
    decryptionFailedStr =
      [0x64#8, 0x65#8, 0x63#8, 0x72#8, 0x79#8, 0x70#8, 0x74#8, 0x69#8] ++
      ([0x6f#8, 0x6e#8, 0x20#8, 0x66#8, 0x61#8, 0x69#8, 0x6c#8, 0x65#8] ++ [0x64#8]) := by
  decide +kernel

private theorem pointsToBytesRO_decryptionFailed (a : BitVec 64) :
    (a ↦ᵣ decryptionFailedStr) =
      (a ↦₆₄ᵣ 0x6974707972636564#64) ∗ ((a + 8#64) ↦₆₄ᵣ 0x656c696166206e6f#64) ∗
        ((a + 16#64) ↦₈ᵣ 0x64#8) := by
  rw [decryptionFailedStr_split_shared_lb, pointsToBytesRO_append, pointsToBytesRO_append]
  change (a ↦ᵣ [0x64#8, 0x65#8, 0x63#8, 0x72#8, 0x79#8, 0x70#8, 0x74#8, 0x69#8]) ∗
    (((a + 8#64) ↦ᵣ [0x6f#8, 0x6e#8, 0x20#8, 0x66#8, 0x61#8, 0x69#8, 0x6c#8, 0x65#8]) ∗
     ((a + 8#64 + 8#64) ↦ᵣ [0x64#8])) = _
  rw [pointsToBytesRO8_eq_pointsTo64RO, pointsToBytesRO8_eq_pointsTo64RO,
    pointsToBytesRO_cons, pointsToBytesRO_nil, sepConj_emp]
  have h16 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
  rw [h16]
  rfl

private theorem pointsToBytes_decryptionFailed (a : BitVec 64) :
    (a ↦₆₄ 0x6974707972636564#64) ∗ ((a + 8#64) ↦₆₄ 0x656c696166206e6f#64) ∗
      ((a + 16#64) ↦₈ 0x64#8) = (a ↦ₛ decryptionFailedStr) := by
  rw [decryptionFailedStr_split_shared_lb, pointsToBytes_append, pointsToBytes_append]
  change _ = (a ↦ₛ [0x64#8, 0x65#8, 0x63#8, 0x72#8, 0x79#8, 0x70#8, 0x74#8, 0x69#8]) ∗
    (((a + 8#64) ↦ₛ [0x6f#8, 0x6e#8, 0x20#8, 0x66#8, 0x61#8, 0x69#8, 0x6c#8, 0x65#8]) ∗
     ((a + 8#64 + 8#64) ↦ₛ [0x64#8]))
  rw [pointsToBytes8_eq_pointsTo64, pointsToBytes8_eq_pointsTo64,
    pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
  have h16 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
  rw [h16]
  rfl

/-! ## `sessionStateAt` head word exposure -/

def vecGhostRestAt_shared_lb (A : RustAlloc) (g : VecGhost) (a : BitVec 64) : SepProp :=
  ((a + 8#64) ↦₆₄ g.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length) ∗
    ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
    (if g.cap = 0 then emp
     else A.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗
       memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length))

theorem vecGhostAt_split_cap_shared_lb (A : RustAlloc) (g : VecGhost) (a : BitVec 64) :
    vecGhostAt A g a = (a ↦₆₄ g.cap) ∗ vecGhostRestAt_shared_lb A g a := by
  simp only [vecGhostAt, vecU8At, vecHeader, vecGhostRestAt_shared_lb, sepConj_assoc]

theorem vecGhostRestAt_cap_lt_shared_lb {A : RustAlloc} {g : VecGhost} {a : BitVec 64}
    {m : Memory} {R : SepProp} (h : m ⊨ vecGhostRestAt_shared_lb A g a ∗ R) : g.cap.toNat < 2 ^ 63 := by
  unfold vecGhostRestAt_shared_lb at h
  have h1 := Satisfies.of_sep_left h
  have h2 := Satisfies.of_sep_right h1
  have h3 := Satisfies.of_sep_right h2
  have h4 := Satisfies.of_sep_left h3
  rw [satisfies_pure] at h4
  exact h4.2.1

def sessionStateExposedAt_shared_lb (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) : SepProp :=
  ⌜PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey ∧
    (match st.remoteIdentity with
     | none => G.remoteIk.bytes = []
     | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
    G.chains.length = st.receiverChains.length ∧
    G.pending.isSome = st.pendingPreKey ∧ G.regIds.length = 8 ∧
    G.localIk.bytes.length = 33 ∧
    (st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)⌝ ∗
    vecGhostRestAt_shared_lb A G.localIk ss ∗ vecGhostAt A G.remoteIk (ss + 0x18#64) ∗
    vecU8At A (ss + 0x30#64) G.root.cap G.root.ptr (keyToBytes32 st.rootKey) ∗
    vecAt A 104 8 (chainAt A) (ss + 0x48#64) G.chainsCap G.chainsPtr
      (G.chains.zip st.receiverChains) ∗
    vecGhostAt A G.alice (ss + 0x60#64) ∗
    vecU8At A (ss + 0x78#64) G.pq.cap G.pq.ptr st.pqRatchetState ∗
    optSenderChainAt A (ss + 0x90#64) G.sender st.senderChain ∗
    optTailVecAt A 48 (ss + 0xf8#64) G.pending ∗
    optTailVecAt A 32 (ss + 0x128#64) G.kyber ∗
    ((ss + 0x148#64) ↦₃₂ st.sessionVersion) ∗ ((ss + 0x14c#64) ↦₃₂ st.previousCounter) ∗
    ((ss + 0x150#64) ↦ₛ G.regIds)

theorem sessionStateAt_expose_shared_lb (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) :
    sessionStateAt A ss G st =
      (ss ↦₆₄ G.localIk.cap) ∗ sessionStateExposedAt_shared_lb A ss G st := by
  unfold sessionStateAt sessionStateExposedAt_shared_lb
  rw [vecGhostAt_split_cap_shared_lb A G.localIk ss]
  ac_rfl

theorem sessionStateAt_localIk_cap_lt_shared_lb {A : RustAlloc} {ss : BitVec 64}
    {G : SessionGhost} {st : SessionState (List (BitVec 8))} {m : Memory} {P R : SepProp}
    (h : m ⊨ P ∗ sessionStateAt A ss G st ∗ R) : G.localIk.cap.toNat < 2 ^ 63 := by
  have h1 := Satisfies.of_sep_right h
  have h2 := Satisfies.of_sep_left h1
  rw [sessionStateAt_expose_shared_lb] at h2
  have h3 := Satisfies.of_sep_right h2
  unfold sessionStateExposedAt_shared_lb at h3
  have h4 := Satisfies.of_sep_right h3
  exact vecGhostRestAt_cap_lt_shared_lb h4

private theorem cap_add_one_ne_zero {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    cap + 1#64 ≠ 0#64 := by
  bv_omega

/-! ## Address, stack, and slot lemmas -/

private theorem libsignalSessionCode_fnOff_dropLocal2 :
    libsignalSessionCode.fnOff FromRecordCallees.dropSessionStructureLocal2Name = 219708 :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#2]")

private theorem libsignalSessionCode_fnOff_msgDecrypt :
    libsignalSessionCode.fnOff msgDecryptName = num% (ls_off% "session_message_decrypt_signal") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) libsignalSessionCode_fnOff_sym_3a4a8

private theorem dropLocal2_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr FromRecordCallees.dropSessionStructureLocal2Name =
      (tripleRatchetProgAtExt b ext).fnAddr msgDecryptName + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#2]") - (ls_off% "session_message_decrypt_signal")) := by
  have h1 : (tripleRatchetProgAtExt b ext).fnAddr FromRecordCallees.dropSessionStructureLocal2Name = b + bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#2]") := by
    rw [tripleRatchetProgAtExt, Program.fnAddr_rebase, libsignalSessionCode_fnOff_dropLocal2]
  have h2 : (tripleRatchetProgAtExt b ext).fnAddr msgDecryptName = b + bv% (ls_off% "session_message_decrypt_signal") := by
    rw [tripleRatchetProgAtExt, Program.fnAddr_rebase, libsignalSessionCode_fnOff_msgDecrypt]
  rw [h1, h2]
  bv_omega

private theorem adrp_logFlag_eq {base entry : BitVec 64}
    (hb : base &&& 0xfff#64 = 0#64) (he : entry = base + bv% (ls_off% "session_message_decrypt_signal")) :
    ((entry + bv% (6840)) &&& bv% (2 ^ 64 - 4096)) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - page% (ls_off% "session_message_decrypt_signal" + 6840)) = base + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) := by
  subst he; bv_kernel

private theorem adrp_rodata_sym_49000_eq {base entry : BitVec 64}
    (hb : base &&& 0xfff#64 = 0#64) (he : entry = base + bv% (ls_off% "session_message_decrypt_signal")) :
    ((entry + bv% (7660)) &&& bv% (2 ^ 64 - 4096)) +
      bv% (page% (ls_xref% (ls_off% "session_message_decrypt_signal" + 6324) (ls_off% "session_message_decrypt_signal" + 6328)) - page% (ls_off% "session_message_decrypt_signal" + 7000)) =
      base + bv% (page% (ls_xref% (ls_off% "session_message_decrypt_signal" + 6324) (ls_off% "session_message_decrypt_signal" + 6328))) := by
  subst he; bv_kernel

private theorem stackAt_root_split_dropLocal2 (sp : BitVec 64) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - FromRecordCallees.dropSessionStructureLocal2Stack) ∗
        stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack :=
  stackAt_split_bottom sp FromRecordCallees.dropSessionStructureLocal2Stack
    (rootStack - FromRecordCallees.dropSessionStructureLocal2Stack) (by decide)

private theorem stackAt_dropLocal2_split_alloc (sp : BitVec 64) :
    stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack =
      memRegion (sp - BitVec.ofNat 64 FromRecordCallees.dropSessionStructureLocal2Stack) 96 ∗
        stackAt sp allocHookStack :=
  stackAt_split_bottom sp allocHookStack 96 (by decide)

private theorem memRegion_0x6b0_split (a : BitVec 64) :
    memRegion a 0x6b0 = (∃∗ w : BitVec 64, (a ↦₆₄ w) ∗ memRegion (a + 8#64) 0x6a8) := by
  rw [memRegion_split a 8 0x6a8 (by decide), memRegion_eight, sepExists_sepConj_left]

private theorem memRegion_slot48_split (a : BitVec 64) :
    memRegion a 48 =
      (∃∗ b4 : BitVec 8, ∃∗ w3 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
        ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₈ b4) ∗ memRegion (a + 33#64) 15) := by
  rw [memRegion_split a 8 40 (by decide),
    memRegion_split (a + 8#64) 8 32 (by decide),
    memRegion_split (a + 8#64 + 8#64) 8 24 (by decide),
    memRegion_split (a + 8#64 + 8#64 + 8#64) 8 16 (by decide),
    memRegion_split (a + 8#64 + 8#64 + 8#64 + 8#64) 1 15 (by decide),
    memRegion_eight, memRegion_eight, memRegion_eight, memRegion_eight, memRegion_one]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd]

private theorem memRegion_17_split (p : BitVec 64) :
    memRegion p 17 =
      (∃∗ u2 : BitVec 8, ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
        (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₆₄ u1) ∗ ((p + 16#64) ↦₈ u2)) := by
  rw [memRegion_split p 8 9 (by decide),
    memRegion_split (p + 8#64) 8 1 (by decide),
    memRegion_eight, memRegion_eight, memRegion_one]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd]

private theorem recFrame_expose (A : RustAlloc) (img : Obj.Image) (x : RecordDecryptGhost)
    (sp : BitVec 64) :
    recFrame A img x sp =
      ∃∗ w5f0 : BitVec 64,
        memRegion sp 0x80 ∗
        ((sp + 0x80#64) ↦₆₄ x.sret) ∗ ((sp + 0x88#64) ↦₆₄ x.locA) ∗ ((sp + 0x90#64) ↦₆₄ x.msgA) ∗
        memRegion (sp + 0x98#64) 4 ∗ ((sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
        ((sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((sp + 0xf0#64) ↦₆₄ x.locA) ∗
        ((sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
        memRegion (sp + 0x4e0#64) 0xd0 ∗
        ((sp + 0x5b0#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x5b8#64) 4 ∗
        ((sp + 0x5bc#64) ↦₈ msgTypeByte .whisper) ∗ memRegion (sp + 0x5bd#64) 3 ∗
        ((sp + 0x5c0#64) ↦₆₄ (sp + 0x5bc#64)) ∗ ((sp + 0x5c8#64) ↦₆₄ x.msgA) ∗
        ((sp + 0x5d0#64) ↦₆₄ (sp + 0x5b0#64)) ∗
        (((sp + 0x5f0#64) ↦₆₄ w5f0) ∗ memRegion (sp + 0x5f0#64 + 8#64) 0x6a8) ∗
        memRegion (sp + 0xdf8#64) 8 ∗
        protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗ ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        (memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - FromRecordCallees.dropSessionStructureLocal2Stack) ∗
          stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack) ∗ A.pool := by
  unfold recFrame logOff
  rw [memRegion_0x6b0_split (sp + 0x5f0#64), stackAt_root_split_dropLocal2 sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

private theorem sepWPp_pure_mid {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B ∗ C) Q Qp) :
    SepWPp prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) Q Qp := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWPp.pure_elim h

private def segTailAct (A : RustAlloc) (img : Obj.Image) (x : RecordDecryptGhost) (sp : BitVec 64)
    (w5f0 w0 w1 w2 w3 : BitVec 64) (b4 : BitVec 8)
    (G₂ : SessionGhost) (st₂ : SessionState (List (BitVec 8))) : SepProp :=
  ((img.base + bv% (ls_xref% (ls_off% "session_message_decrypt_signal" + 6324) (ls_off% "session_message_decrypt_signal" + 6328))) ↦₆₄ᵣ 0x6974707972636564#64) ∗
  ((img.base + bv% (ls_xref% (ls_off% "session_message_decrypt_signal" + 6324) (ls_off% "session_message_decrypt_signal" + 6328)) + 8#64) ↦₆₄ᵣ 0x656c696166206e6f#64) ∗
  ((img.base + bv% (ls_xref% (ls_off% "session_message_decrypt_signal" + 6324) (ls_off% "session_message_decrypt_signal" + 6328)) + 16#64) ↦₈ᵣ 0x64#8) ∗
  ((sp + 0x80#64) ↦₆₄ x.sret) ∗ ((sp + 0x128#64) ↦₆₄ x.prevPtr) ∗
  ((sp + 0x130#64) ↦₆₄ 0#64) ∗ ((sp + 0x138#64) ↦₆₄ x.G.localIk.cap) ∗
  ((sp + 0x5bc#64) ↦₈ msgTypeByte .whisper) ∗
  ((sp + 0x5f0#64) ↦₆₄ w5f0) ∗ ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
  sessionStateAt A (sp + 0xca0#64) G₂ st₂ ∗
  ((sp + 0x4b0#64) ↦₆₄ w0) ∗ ((sp + 0x4b0#64 + 8#64) ↦₆₄ w1) ∗
  ((sp + 0x4b0#64 + 16#64) ↦₆₄ w2) ∗ ((sp + 0x4b0#64 + 24#64) ↦₆₄ w3) ∗
  ((sp + 0x4b0#64 + 32#64) ↦₈ b4) ∗ memRegion (sp + 0x4b0#64 + 33#64) 15 ∗
  stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack ∗ A.pool

theorem recordResultAt_decryptionFailed_intro_shared_lb (A : RustAlloc) (r p : BitVec 64)
    (hp : p ≠ 0) {m : Memory} {F : SepProp}
    (hm : m ⊨ ((r ↦₆₄ speWord 24) ∗ ((r + 8#64) ↦₆₄ 17#64) ∗ ((r + 16#64) ↦₆₄ p) ∗
      ((r + 24#64) ↦₆₄ 17#64) ∗ ((r + 32#64) ↦₈ msgTypeByte .whisper) ∗
      memRegion (r + 33#64) 15 ∗ A.live p 17 1 ∗ (p ↦₆₄ 0x6974707972636564#64) ∗
      ((p + 8#64) ↦₆₄ 0x656c696166206e6f#64) ∗ ((p + 16#64) ↦₈ 0x64#8)) ∗ F) :
    m ⊨ recordResultAt A r (.error (.invalidMessage .whisper .decryptionFailed)) ∗ F := by
  have hlen : decryptionFailedStr.length = 17 := by decide +kernel
  have h1 : m ⊨ ((r ↦₆₄ speWord 24) ∗ ((((r + 8#64) ↦₆₄ 17#64) ∗ ((r + 16#64) ↦₆₄ p) ∗
      ((r + 24#64) ↦₆₄ 17#64)) ∗ (A.live p 17 1 ∗ ((p ↦₆₄ 0x6974707972636564#64) ∗
      ((p + 8#64) ↦₆₄ 0x656c696166206e6f#64) ∗ ((p + 16#64) ↦₈ 0x64#8)) ∗
      memRegion (p + 17#64) 0)) ∗ ((r + 32#64) ↦₈ msgTypeByte .whisper) ∗
      memRegion (r + 33#64) 15) ∗ F := by
    rw [memRegion_zero, sepConj_emp]
    arm64_sep_close
  rw [pointsToBytes_decryptionFailed p] at h1
  unfold recordResultAt vecU8 vecU8At vecHeader
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
  refine ⟨17#64, p, ?_⟩
  have hp' : ¬ p = 0#64 := hp
  simp only [hlen, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.le_refl,
    Nat.sub_self, BitVec.ofNat_eq_ofNat]
  rw [show (r + 8#64 + 8#64) = r + 16#64 by bv_omega,
      show (r + 8#64 + 16#64) = r + 24#64 by bv_omega]
  simpa [sepConj_assoc, satisfies_pure_sepConj, hp'] using h1

private def segTailFrame (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (x : RecordDecryptGhost) (sp : BitVec 64) (r_err : RecErr) : SepProp :=
  memRegion sp 0x80 ∗
  ((sp + 0x88#64) ↦₆₄ x.locA) ∗ ((sp + 0x90#64) ↦₆₄ x.msgA) ∗
  memRegion (sp + 0x98#64) 4 ∗ ((sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
  ((sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((sp + 0xf0#64) ↦₆₄ x.locA) ∗
  memRegion (sp + 0x4e0#64) 0xd0 ∗
  ((sp + 0x5b0#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x5b8#64) 4 ∗
  memRegion (sp + 0x5bd#64) 3 ∗
  ((sp + 0x5c0#64) ↦₆₄ (sp + 0x5bc#64)) ∗ ((sp + 0x5c8#64) ↦₆₄ x.msgA) ∗
  ((sp + 0x5d0#64) ↦₆₄ (sp + 0x5b0#64)) ∗
  memRegion (sp + 0x5f0#64 + 8#64) 0x6a8 ∗ memRegion (sp + 0xdf8#64) 8 ∗
  protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
  signalMessageAt A x.msgG x.msgA x.msg ∗
  memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - FromRecordCallees.dropSessionStructureLocal2Stack) ∗
  sessionStateExposedAt_shared_lb A (sp + 0x138#64) x.G x.st ∗
  errsAt A (sp + 0x5d8#64) [r_err] ∗
  tapeAfter ctl x.cur x.rest (x.draws C)

private def segTailPost (A : RustAlloc) (img : Obj.Image) (x : RecordDecryptGhost)
    (sp : BitVec 64) : SepProp :=
  ((sp + 0x80#64) ↦₆₄ x.sret) ∗ ((sp + 0x128#64) ↦₆₄ x.prevPtr) ∗
  ((sp + 0x130#64) ↦₆₄ 0#64) ∗ ((sp + 0x138#64) ↦₆₄ x.G.localIk.cap) ∗
  ((sp + 0x5bc#64) ↦₈ msgTypeByte .whisper) ∗
  ((sp + 0x5f0#64) ↦₆₄ (bv% (2 ^ 64 - 1))) ∗
  ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
  memRegion (sp + 0xca0#64) 344 ∗
  recordResultAt A (sp + 0x4b0#64) (.error (.invalidMessage .whisper .decryptionFailed)) ∗
  stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack ∗ A.pool

/-- Drops the cloned `SessionStructure`, observes no previous sessions, allocates
`"decryption failed"` (17 B), writes `InvalidMessage(Whisper, "decryption failed")` to `sp + 0x4b0`,
and jumps to `recJPC img` (`+0x1e8c`). -/
theorem segTail_ok_ext {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)} :
    SegTailSpecExt img C A ctl uuidTryParse S ext := by
  intro himg hhooks hdrop2 x R s0 s hF hL
  obtain ⟨hpc_s, ⟨hrun, hsp, hsp_align, hx29, htrace, hfl, hsym, hvregs⟩, hmodel, hmem⟩ := hF
  have hsp0_align : (s0.sp &&& 15#64 == 0#64) = true := by
    simpa [State.spAligned, hsp] using hsp_align
  have hcap_lt : x.G.localIk.cap.toNat < 2 ^ 63 :=
    sessionStateAt_localIk_cap_lt_shared_lb (P := recFrame A img x s0.sp) hmem
  have hcap_ne : x.G.localIk.cap + 1#64 ≠ 0#64 := cap_add_one_ne_zero hcap_lt
  have hro : img.RoDataLoaded s.mem := (Obj.Image.frozenLoaded_iff.mp hfl).2.1
  have hb : img.base &&& 0xfff#64 = 0#64 := ProofLib.ObjectLoad.base_aligned_of_loads himg
  rw [recFPC, entryOf_eq_tripleRatchetProgAtExt ext himg msgDecryptName] at hpc_s
  have hdrop2' : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#2]") - (ls_off% "session_message_decrypt_signal")))
      (FromRecordCallees.dropSessionStructureLocal2Spec A) := by
    unfold FromRecordCallees.DropSessionStructureLocal2OkExt at hdrop2
    rwa [dropLocal2_fnAddr_eq] at hdrop2
  clear hdrop2
  have hfn : libsignalSessionCode.fnOff msgDecryptName = num% (ls_off% "session_message_decrypt_signal") :=
    libsignalSessionCode_fnOff_msgDecrypt
  have hshim := hhooks.toAllocContracts.shim_ok_at msgDecryptName (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "session_message_decrypt_signal"))
    (by rw [hfn, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  have halloc := hhooks.toAllocContracts.alloc_ok_at msgDecryptName (num% (ls_off% "__rustc::__rust_alloc" - ls_off% "session_message_decrypt_signal"))
    (by rw [hfn, (ls_stub% "__rustc::__rust_alloc")])
  have hpanic := panic_at_handle_error_ext img.base ext msgDecryptName (num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "session_message_decrypt_signal"))
    (by rw [hfn, (ls_stub% "alloc::raw_vec::handle_error")])
  have hadp_log :
      (((tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 6840#64) &&&
        bv% (2 ^ 64 - 4096)) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - page% (ls_off% "session_message_decrypt_signal" + 6840)) = img.base + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) :=
    adrp_logFlag_eq hb (by rw [tripleRatchetProgAtExt, Program.fnAddr_rebase, hfn])
  have hadp_ro :
      (((tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 7660#64) &&&
        bv% (2 ^ 64 - 4096)) + bv% (page% (ls_xref% (ls_off% "session_message_decrypt_signal" + 6324) (ls_off% "session_message_decrypt_signal" + 6328)) - page% (ls_off% "session_message_decrypt_signal" + 7000)) =
        img.base + bv% (page% (ls_xref% (ls_off% "session_message_decrypt_signal" + 6324) (ls_off% "session_message_decrypt_signal" + 6328))) :=
    adrp_rodata_sym_49000_eq hb (by rw [tripleRatchetProgAtExt, Program.fnAddr_rebase, hfn])
  have hmem_ro := rodata_decryptionFailed_intro himg hro hmem
  clear hmem
  rw [pointsToBytesRO_decryptionFailed, recFrame_expose,
    sessionStateAt_expose_shared_lb A (s0.sp + 0x138#64) x.G x.st,
    memRegion_slot48_split (s0.sp + 0x4b0#64)] at hmem_ro
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem_ro
  obtain ⟨b4, w3, w2, w1, w0, r_err, G₂, st₂, w5f0, hmem_ro⟩ := hmem_ro
  have hmem_split : s.mem ⊨
      segTailAct A img x s0.sp w5f0 w0 w1 w2 w3 b4 G₂ st₂ ∗
      (segTailFrame C A ctl x s0.sp r_err ∗ R) := by
    dsimp only [segTailAct, segTailFrame]
    arm64_sep_close
  clear hmem_ro
  have hwp : SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 7820#64) s
      (segTailAct A img x s0.sp w5f0 w0 w1 w2 w3 b4 G₂ st₂)
      (fun s' P_f =>
        s'.sp = s0.sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x29 = s0.readReg64 .x29 ∧ s'.trace = s0.trace ∧
        s'.readReg64 .x26 = s0.sp + 0xa0#64 ∧ s'.readReg64 .x27 = x.sret ∧
        s'.readReg64 .x28 = speWord 24 ∧ calleeSavedVRegs s' = calleeSavedVRegs s0 ∧
        (∀ m F, (m ⊨ P_f ∗ F) → (m ⊨ segTailPost A img x s0.sp ∗ F)))
      (fun s' _ => allocFailedIn s0 s' ∧ s0.trace <+: s'.trace) := by
    dsimp only [segTailAct]
    segTail_fetches img.base (Rust.withPanics ext) hfn 0x850 28
    segTail_fetches img.base (Rust.withPanics ext) hfn 0x16e4 16
    segTail_fetches img.base (Rust.withPanics ext) hfn 0x1ab4 32
    segTail_fetches img.base (Rust.withPanics ext) hfn 0x1cf0 8
    segTail_fetches img.base (Rust.withPanics ext) hfn 0x1dd4 88
    segTail_fetches img.base (Rust.withPanics ext) hfn 0x2640 12
    dsimp only [tripleRatchetProgAtExt] at hpc_s hdrop2' hshim halloc hpanic hadp_log hadp_ro ⊢
    clear himg hhooks hfn hb
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)).fnAddr msgDecryptName = entry
    examples_hide_fetches
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hlay : LayoutOk 17 1 := ⟨by decide, hpow2, by decide⟩
    have hcap_beq : (x.G.localIk.cap + 1#64 == 0#64) = false :=
      beq_eq_false_iff_ne.mpr hcap_ne
    apply SepWPp.of_sepWP (mid := entry + bv% (7652))
    wp_steps
    wp_apply
    rw [hsp, stackAt_dropLocal2_split_alloc s0.sp]
    wp_steps
    wp_apply
    wp_steps
    wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom : sf_2.readReg64 (Reg.gpr 0#5) = 0#64
    · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]
      refine sepWPp_pure_mid fun htr_oom => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "session_message_decrypt_signal"))
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) ?_
      simp [allocFailedIn, Rust.panicked, htr_oom, h_10, hpost, htrace]
    · have hoom' : sf_2.readReg64 (Reg.gpr 0#5) ≠ 0 := hoom
      have hoom_beq : (sf_2.readReg64 (Reg.gpr 0#5) == 0#64) = false :=
        beq_eq_false_iff_ne.mpr hoom
      simp only [hoom', ite_false, sepConj_assoc]
      refine sepWPp_pure_mid fun ⟨_, htr_ok⟩ => ?_
      rw [memRegion_17_split (sf_2.readReg64 (Reg.gpr 0#5))]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun u2 => SepWPp.exists_elim fun u1 =>
        SepWPp.exists_elim fun u0 => ?_
      apply SepWPp.of_sepWP_ret
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [wp_norm, arm64_norm, *],
        by simp only [State.spAligned, wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [speWord, wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], ?_⟩
      intro m F hm
      rw [h_11, hsp_sf, hsp] at hm
      have hm_drop : m ⊨
          (((img.base + bv% (ls_xref% (ls_off% "session_message_decrypt_signal" + 6324) (ls_off% "session_message_decrypt_signal" + 6328))) ↦₆₄ᵣ 7598822138193339748#64) ∗
           ((img.base + bv% ((ls_xref% (ls_off% "session_message_decrypt_signal" + 6324) (ls_off% "session_message_decrypt_signal" + 6328)) + 8)) ↦₆₄ᵣ 7308332162361618031#64) ∗
           ((img.base + bv% ((ls_xref% (ls_off% "session_message_decrypt_signal" + 6324) (ls_off% "session_message_decrypt_signal" + 6328)) + 16)) ↦₈ᵣ 100#8)) ∗
          (((s0.sp + 0x4b0#64) ↦₆₄ speWord 24 ∗ ((s0.sp + 0x4b0#64 + 8#64) ↦₆₄ 17#64) ∗
            ((s0.sp + 0x4b0#64 + 16#64) ↦₆₄ sf_2.readReg64 (Reg.gpr 0#5)) ∗
            ((s0.sp + 0x4b0#64 + 24#64) ↦₆₄ 17#64) ∗
            ((s0.sp + 0x4b0#64 + 32#64) ↦₈ msgTypeByte .whisper) ∗
            memRegion (s0.sp + 0x4b0#64 + 33#64) 15 ∗
            A.live (sf_2.readReg64 (Reg.gpr 0#5)) 17 1 ∗
            (sf_2.readReg64 (Reg.gpr 0#5) ↦₆₄ 0x6974707972636564#64) ∗
            ((sf_2.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ 0x656c696166206e6f#64) ∗
            ((sf_2.readReg64 (Reg.gpr 0#5) + 16#64) ↦₈ 0x64#8)) ∗
           ((memRegion (s0.sp - BitVec.ofNat 64 FromRecordCallees.dropSessionStructureLocal2Stack) 96 ∗
             stackAt s0.sp allocHookStack) ∗
            (((s0.sp + 0x80#64) ↦₆₄ x.sret) ∗ ((s0.sp + 0x128#64) ↦₆₄ x.prevPtr) ∗
             ((s0.sp + 0x130#64) ↦₆₄ 0#64) ∗ ((s0.sp + 0x138#64) ↦₆₄ x.G.localIk.cap) ∗
             ((s0.sp + 0x5bc#64) ↦₈ msgTypeByte .whisper) ∗
             ((s0.sp + 0x5f0#64) ↦₆₄ (bv% (2 ^ 64 - 1))) ∗
             ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
             memRegion (s0.sp + 0xca0#64) 344 ∗ A.pool) ∗ F)) := by
        dsimp only [speWord, FromRecordCallees.dropSessionStructureLocal2Stack]
        arm64_sep_close
      clear hm
      have hm_keep := Satisfies.of_sep_right hm_drop
      clear hm_drop
      have hm_res := recordResultAt_decryptionFailed_intro_shared_lb A (s0.sp + 0x4b0#64)
        (sf_2.readReg64 (Reg.gpr 0#5)) hoom' hm_keep
      clear hm_keep
      rw [← stackAt_dropLocal2_split_alloc s0.sp] at hm_res
      exact Eq.mp (congrArg (m ⊨ ·) (by unfold segTailPost; ac_rfl)) hm_res
  obtain ⟨s', hsteps, hout⟩ := hwp (segTailFrame C A ctl x s0.sp r_err ∗ R) hmem_split hL
  rcases hout with ⟨hpc', hrun', P_f, hmf, hsp', hsp_align', hx29', htr', hx26', hx27', hx28', hvregs', hent⟩ |
      ⟨hpan, P_f, hmf, hP⟩ | ⟨_, hoom⟩
  · refine ⟨s', hsteps, Or.inl ?_⟩
    have hpc_j : s'.pc = recJPC img := by
      rw [recJPC, entryOf_eq_tripleRatchetProgAtExt ext himg msgDecryptName]
      exact hpc'
    have hmeta' : recMeta img s0 s' :=
      ⟨hrun', hsp', hsp_align', hx29', htr', hsteps.frozenLoaded hfl, hsteps.symtab_eq.trans hsym, hvregs'⟩
    have hno_pan : (x.model C S uuidTryParse).1 ≠ .error .panic := by
      rw [hmodel]; decide
    have htag : s'.readReg64 .x28 = recordResultTag (x.model C S uuidTryParse).1 := by
      rw [hmodel, recordResultTag]; exact hx28'
    refine ⟨hpc_j, hmeta', hno_pan, hx26', hx27', htag, ?_⟩
    have hmf' := hent s'.mem (segTailFrame C A ctl x s0.sp r_err ∗ R) hmf
    clear hmf
    rw [hmodel]
    rw [recFrame_expose, sessionStateAt_expose_shared_lb A (s0.sp + 0x138#64) x.G x.st]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    refine ⟨[r_err], bv% (2 ^ 64 - 1), ?_⟩
    dsimp only [segTailPost, segTailFrame] at hmf'
    arm64_sep_close
  · refine ⟨s', hsteps, Or.inr (Or.inr ⟨hpan, ?_⟩)⟩
    have hmf' : s'.mem ⊨ (P_f ∗ segTailFrame C A ctl x s0.sp r_err) ∗ R := by
      rwa [← sepConj_assoc] at hmf
    exact allowPanic_panicked ⟨Or.inr (Or.inr hP.1), hP.2⟩ hmf'
  · exact (not_satisfies_false_sepConj hoom).elim

theorem segTail_ok {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)} :
    SegTailSpec img C A ctl uuidTryParse S abs :=
  fun himg hhooks hdrop2 =>
    segTail_ok_ext himg (Stage2Contracts.of_tripleRatchetProgAt' hhooks) hdrop2

/-! ## Relocatable `[LibsignalPlacement]` `segTail_placed_ok` -/

abbrev decryptionFailedSym : String :=
  "libsignal_session:.rodata..Lanon.43"

private theorem rodata_decryptionFailed_placed_intro [LibsignalPlacement]
    {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ ((lsmpl.ρ decryptionFailedSym) ↦ᵣ decryptionFailedStr) ∗ P :=
  lsro_intro_chk hro (by rfl_kernel) hP

private theorem recFramePlaced_expose [LibsignalPlacement] (A : RustAlloc) (x : RecordDecryptGhost)
    (sp : BitVec 64) :
    recFramePlaced A x sp =
      ∃∗ w5f0 : BitVec 64,
        memRegion sp 0x80 ∗
        ((sp + 0x80#64) ↦₆₄ x.sret) ∗ ((sp + 0x88#64) ↦₆₄ x.locA) ∗ ((sp + 0x90#64) ↦₆₄ x.msgA) ∗
        memRegion (sp + 0x98#64) 4 ∗ ((sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
        ((sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((sp + 0xf0#64) ↦₆₄ x.locA) ∗
        ((sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
        memRegion (sp + 0x4e0#64) 0xd0 ∗
        ((sp + 0x5b0#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x5b8#64) 4 ∗
        ((sp + 0x5bc#64) ↦₈ msgTypeByte .whisper) ∗ memRegion (sp + 0x5bd#64) 3 ∗
        ((sp + 0x5c0#64) ↦₆₄ (sp + 0x5bc#64)) ∗ ((sp + 0x5c8#64) ↦₆₄ x.msgA) ∗
        ((sp + 0x5d0#64) ↦₆₄ (sp + 0x5b0#64)) ∗
        (((sp + 0x5f0#64) ↦₆₄ w5f0) ∗ memRegion (sp + 0x5f0#64 + 8#64) 0x6a8) ∗
        memRegion (sp + 0xdf8#64) 8 ∗
        protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        (memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - FromRecordCallees.dropSessionStructureLocal2Stack) ∗
          stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack) ∗ A.pool := by
  unfold recFramePlaced FromRecordCallees.lsLogOff
  rw [memRegion_0x6b0_split (sp + 0x5f0#64), stackAt_root_split_dropLocal2 sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

private def segTailActPlaced [LibsignalPlacement] (A : RustAlloc) (x : RecordDecryptGhost) (sp : BitVec 64)
    (w5f0 w0 w1 w2 w3 : BitVec 64) (b4 : BitVec 8)
    (G₂ : SessionGhost) (st₂ : SessionState (List (BitVec 8))) : SepProp :=
  ((lsmpl.ρ decryptionFailedSym) ↦₆₄ᵣ 0x6974707972636564#64) ∗
  ((lsmpl.ρ decryptionFailedSym + 8#64) ↦₆₄ᵣ 0x656c696166206e6f#64) ∗
  ((lsmpl.ρ decryptionFailedSym + 16#64) ↦₈ᵣ 0x64#8) ∗
  ((sp + 0x80#64) ↦₆₄ x.sret) ∗ ((sp + 0x128#64) ↦₆₄ x.prevPtr) ∗
  ((sp + 0x130#64) ↦₆₄ 0#64) ∗ ((sp + 0x138#64) ↦₆₄ x.G.localIk.cap) ∗
  ((sp + 0x5bc#64) ↦₈ msgTypeByte .whisper) ∗
  ((sp + 0x5f0#64) ↦₆₄ w5f0) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
  sessionStateAt A (sp + 0xca0#64) G₂ st₂ ∗
  ((sp + 0x4b0#64) ↦₆₄ w0) ∗ ((sp + 0x4b0#64 + 8#64) ↦₆₄ w1) ∗
  ((sp + 0x4b0#64 + 16#64) ↦₆₄ w2) ∗ ((sp + 0x4b0#64 + 24#64) ↦₆₄ w3) ∗
  ((sp + 0x4b0#64 + 32#64) ↦₈ b4) ∗ memRegion (sp + 0x4b0#64 + 33#64) 15 ∗
  stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack ∗ A.pool

private def segTailPostPlaced [LibsignalPlacement] (A : RustAlloc) (x : RecordDecryptGhost)
    (sp : BitVec 64) : SepProp :=
  ((sp + 0x80#64) ↦₆₄ x.sret) ∗ ((sp + 0x128#64) ↦₆₄ x.prevPtr) ∗
  ((sp + 0x130#64) ↦₆₄ 0#64) ∗ ((sp + 0x138#64) ↦₆₄ x.G.localIk.cap) ∗
  ((sp + 0x5bc#64) ↦₈ msgTypeByte .whisper) ∗
  ((sp + 0x5f0#64) ↦₆₄ (bv% (2 ^ 64 - 1))) ∗
  (lsLogFilterAddr ↦₆₄ 0#64) ∗
  memRegion (sp + 0xca0#64) 344 ∗
  recordResultAt A (sp + 0x4b0#64) (.error (.invalidMessage .whisper .decryptionFailed)) ∗
  stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack ∗ A.pool

theorem segTail_placed_ok [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)} :
    SegTailPlacedSpec C A ctl uuidTryParse S H := by
  intro hshim_sat halloc_sat hpanic_eq hdrop2 x R s0 s hF hL
  obtain ⟨hpc_s, ⟨hrun, hsp, hsp_align, hx29, htrace, hfl, hvregs⟩, hmodel, hmem⟩ := hF
  dsimp only [recFPCPlaced] at hpc_s
  have hsp0_align : (s0.sp &&& 15#64 == 0#64) = true := by
    simpa [State.spAligned, hsp] using hsp_align
  have hcap_lt : x.G.localIk.cap.toNat < 2 ^ 63 :=
    sessionStateAt_localIk_cap_lt_shared_lb (P := recFramePlaced A x s0.sp) hmem
  have hcap_ne : x.G.localIk.cap + 1#64 ≠ 0#64 := cap_add_one_ne_zero hcap_lt
  have hcl : LibsignalCodeLoaded lsmpl s.mem := hfl.1
  have hro := hfl.2
  have hshim := ls_hook_ok_226 (by decide) hshim_sat
  have halloc := ls_hook_ok_226 (by decide) halloc_sat
  have hpanic : ((blkPC_197).rebase (blkPl_197).base H).externAt? (lsmpl.ρ lsHandleErrorSym) =
      some Rust.panicked := by
    rw [ls_externAt?_226 (by decide), hpanic_eq]
  have hmem_ro := rodata_decryptionFailed_placed_intro hro hmem
  clear hmem
  rw [pointsToBytesRO_decryptionFailed, recFramePlaced_expose,
    sessionStateAt_expose_shared_lb A (s0.sp + 0x138#64) x.G x.st,
    memRegion_slot48_split (s0.sp + 0x4b0#64)] at hmem_ro
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem_ro
  obtain ⟨b4, w3, w2, w1, w0, r_err, G₂, st₂, w5f0, hmem_ro⟩ := hmem_ro
  have hmem_split : s.mem ⊨
      segTailActPlaced A x s0.sp w5f0 w0 w1 w2 w3 b4 G₂ st₂ ∗
      (segTailFrame C A ctl x s0.sp r_err ∗ R) := by
    dsimp only [segTailActPlaced, segTailFrame]
    arm64_sep_close
  clear hmem_ro
  have hwp : SepWPp ((blkPC_197).rebase (blkPl_197).base H)
      ((blkPl_197).base + 7820#64) s
      (segTailActPlaced A x s0.sp w5f0 w0 w1 w2 w3 b4 G₂ st₂)
      (fun s' P_f =>
        s'.sp = s0.sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x29 = s0.readReg64 .x29 ∧ s'.trace = s0.trace ∧
        s'.readReg64 .x26 = s0.sp + 0xa0#64 ∧ s'.readReg64 .x27 = x.sret ∧
        s'.readReg64 .x28 = speWord 24 ∧ calleeSavedVRegs s' = calleeSavedVRegs s0 ∧
        (∀ m F, (m ⊨ P_f ∗ F) → (m ⊨ segTailPostPlaced A x s0.sp ∗ F)))
      (fun s' _ => allocFailedIn s0 s' ∧ s0.trace <+: s'.trace) := by
    dsimp only [segTailActPlaced]
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hlay : LayoutOk 17 1 := ⟨by decide, hpow2, by decide⟩
    have hcap_beq : (x.G.localIk.cap + 1#64 == 0#64) = false :=
      beq_eq_false_iff_ne.mpr hcap_ne
    apply SepWPp.of_sepWP (mid := (blkPl_197).base + bv% (7652))
    wp_steps
    wp_apply
    rw [hsp, stackAt_dropLocal2_split_alloc s0.sp]
    wp_steps
    wp_apply
    wp_steps
    wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom : sf_2.readReg64 (Reg.gpr 0#5) = 0#64
    · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]
      refine sepWPp_pure_mid fun htr_oom => ?_
      apply SepWPp.of_sepWP (mid := lsmpl.ρ lsHandleErrorSym)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) ?_
      simp [allocFailedIn, Rust.panicked, htr_oom, h_10, hpost, htrace]
    · have hoom' : sf_2.readReg64 (Reg.gpr 0#5) ≠ 0 := hoom
      have hoom_beq : (sf_2.readReg64 (Reg.gpr 0#5) == 0#64) = false :=
        beq_eq_false_iff_ne.mpr hoom
      simp only [hoom', ite_false, sepConj_assoc]
      refine sepWPp_pure_mid fun ⟨_, htr_ok⟩ => ?_
      rw [memRegion_17_split (sf_2.readReg64 (Reg.gpr 0#5))]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun u2 => SepWPp.exists_elim fun u1 =>
        SepWPp.exists_elim fun u0 => ?_
      apply SepWPp.of_sepWP_ret
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [wp_norm, arm64_norm, *],
        by simp only [State.spAligned, wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [speWord, wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], ?_⟩
      intro m F hm
      rw [h_11, hsp_sf, hsp] at hm
      have hm_drop : m ⊨
          (((lsmpl.ρ decryptionFailedSym) ↦₆₄ᵣ 7598822138193339748#64) ∗
           ((lsmpl.ρ decryptionFailedSym + 8#64) ↦₆₄ᵣ 7308332162361618031#64) ∗
           ((lsmpl.ρ decryptionFailedSym + 16#64) ↦₈ᵣ 100#8)) ∗
          (((s0.sp + 0x4b0#64) ↦₆₄ speWord 24 ∗ ((s0.sp + 0x4b0#64 + 8#64) ↦₆₄ 17#64) ∗
            ((s0.sp + 0x4b0#64 + 16#64) ↦₆₄ sf_2.readReg64 (Reg.gpr 0#5)) ∗
            ((s0.sp + 0x4b0#64 + 24#64) ↦₆₄ 17#64) ∗
            ((s0.sp + 0x4b0#64 + 32#64) ↦₈ msgTypeByte .whisper) ∗
            memRegion (s0.sp + 0x4b0#64 + 33#64) 15 ∗
            A.live (sf_2.readReg64 (Reg.gpr 0#5)) 17 1 ∗
            (sf_2.readReg64 (Reg.gpr 0#5) ↦₆₄ 0x6974707972636564#64) ∗
            ((sf_2.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ 0x656c696166206e6f#64) ∗
            ((sf_2.readReg64 (Reg.gpr 0#5) + 16#64) ↦₈ 0x64#8)) ∗
           ((memRegion (s0.sp - BitVec.ofNat 64 FromRecordCallees.dropSessionStructureLocal2Stack) 96 ∗
             stackAt s0.sp allocHookStack) ∗
            (((s0.sp + 0x80#64) ↦₆₄ x.sret) ∗ ((s0.sp + 0x128#64) ↦₆₄ x.prevPtr) ∗
             ((s0.sp + 0x130#64) ↦₆₄ 0#64) ∗ ((s0.sp + 0x138#64) ↦₆₄ x.G.localIk.cap) ∗
             ((s0.sp + 0x5bc#64) ↦₈ msgTypeByte .whisper) ∗
             ((s0.sp + 0x5f0#64) ↦₆₄ (bv% (2 ^ 64 - 1))) ∗
             (lsLogFilterAddr ↦₆₄ 0#64) ∗
             memRegion (s0.sp + 0xca0#64) 344 ∗ A.pool) ∗ F)) := by
        dsimp only [speWord, FromRecordCallees.dropSessionStructureLocal2Stack]
        arm64_sep_close
      clear hm
      have hm_keep := Satisfies.of_sep_right hm_drop
      clear hm_drop
      have hm_res := recordResultAt_decryptionFailed_intro_shared_lb A (s0.sp + 0x4b0#64)
        (sf_2.readReg64 (Reg.gpr 0#5)) hoom' hm_keep
      clear hm_keep
      rw [← stackAt_dropLocal2_split_alloc s0.sp] at hm_res
      exact Eq.mp (congrArg (m ⊨ ·) (by unfold segTailPostPlaced; ac_rfl)) hm_res
  obtain ⟨s', hsteps, hout⟩ := hwp (segTailFrame C A ctl x s0.sp r_err ∗ R) hmem_split hL
  rcases hout with ⟨hpc', hrun', P_f, hmf, hsp', hsp_align', hx29', htr', hx26', hx27', hx28', hvregs', hent⟩ |
      ⟨hpan, P_f, hmf, hP⟩ | ⟨_, hoom⟩
  · refine ⟨s', hsteps, Or.inl ?_⟩
    have hmeta' : recMetaPlaced s0 s' :=
      ⟨hrun', hsp', hsp_align', hx29', htr', hfl.of_keepsFrozen hsteps.keepsFrozen, hvregs'⟩
    have hno_pan : (x.model C S uuidTryParse).1 ≠ .error .panic := by
      rw [hmodel]; decide
    have htag : s'.readReg64 .x28 = recordResultTag (x.model C S uuidTryParse).1 := by
      rw [hmodel, recordResultTag]; exact hx28'
    refine ⟨hpc', hmeta', hno_pan, hx26', hx27', htag, ?_⟩
    have hmf' := hent s'.mem (segTailFrame C A ctl x s0.sp r_err ∗ R) hmf
    clear hmf
    rw [hmodel]
    rw [recFramePlaced_expose, sessionStateAt_expose_shared_lb A (s0.sp + 0x138#64) x.G x.st]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    refine ⟨[r_err], bv% (2 ^ 64 - 1), ?_⟩
    dsimp only [segTailPostPlaced, segTailFrame] at hmf'
    arm64_sep_close
  · refine ⟨s', hsteps, Or.inr (Or.inr ⟨hpan, ?_⟩)⟩
    have hmf' : s'.mem ⊨ (P_f ∗ segTailFrame C A ctl x s0.sp r_err) ∗ R := by
      rwa [← sepConj_assoc] at hmf
    dsimp only [recordDecryptPlacedSpec]
    exact allowPanic_panicked ⟨Or.inr (Or.inr hP.1), hP.2⟩ hmf'
  · exact (not_satisfies_false_sepConj hoom).elim

end CryptoVerification.LibsignalTripleRatchet.Record
