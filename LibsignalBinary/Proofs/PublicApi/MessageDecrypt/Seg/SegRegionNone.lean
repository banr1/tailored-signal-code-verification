/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Defs
import all Init.Data.String.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegRegionNoneFetch
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.InImageCalleesCodeSym
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.WP.Apply

/-!
# `MessageDecrypt` Empty-Session Region Segment (`SegRegionNone`)

Verifies the 69-instruction path (`+0x1a8 → +0x1f50`) through `try_decrypt_from_record` when
`r.currentSession = none` (`[sp + 0x138] = noneCap`, `errs = []`): skipping the current- and
previous-session decrypt blocks, allocating and copying the 17-byte `"decryption failed"` error
payload (`0x4f1a8`), writing `.error (.invalidMessage .whisper .decryptionFailed)` at `sp + 0x4b0`,
and exiting to `PostNone` at `+0x1f50`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegRegionNone

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace NormHelpers

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

end NormHelpers

open NormHelpers

/-! ## 1. `.rodata` String `"decryption failed"` at `0x4f1a8` -/

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
    (secOff := num% (ls_xref% (ls_off% "session_message_decrypt_signal" + 6324) (ls_off% "session_message_decrypt_signal" + 6328))) (secLen := 17) (dataOff := num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)))
    rfl (List.mem_of_elem_eq_true (by rfl_kernel)) (by decide) (by decide)
    (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) hro hP
  rwa [rodata_0x451a8_eq] at h

private theorem decryptionFailedStr_split :
    decryptionFailedStr =
      [0x64#8, 0x65#8, 0x63#8, 0x72#8, 0x79#8, 0x70#8, 0x74#8, 0x69#8] ++
      ([0x6f#8, 0x6e#8, 0x20#8, 0x66#8, 0x61#8, 0x69#8, 0x6c#8, 0x65#8] ++ [0x64#8]) := by
  rfl_kernel

theorem pointsToBytesRO_decryptionFailed_shared_lb (a : BitVec 64) :
    (a ↦ᵣ decryptionFailedStr) =
      (a ↦₆₄ᵣ 0x6974707972636564#64) ∗ ((a + 8#64) ↦₆₄ᵣ 0x656c696166206e6f#64) ∗
        ((a + 16#64) ↦₈ᵣ 0x64#8) := by
  rw [decryptionFailedStr_split, pointsToBytesRO_append, pointsToBytesRO_append]
  change (a ↦ᵣ [0x64#8, 0x65#8, 0x63#8, 0x72#8, 0x79#8, 0x70#8, 0x74#8, 0x69#8]) ∗
    (((a + 8#64) ↦ᵣ [0x6f#8, 0x6e#8, 0x20#8, 0x66#8, 0x61#8, 0x69#8, 0x6c#8, 0x65#8]) ∗
     ((a + 8#64 + 8#64) ↦ᵣ [0x64#8])) = _
  rw [pointsToBytesRO8_eq_pointsTo64RO, pointsToBytesRO8_eq_pointsTo64RO,
    pointsToBytesRO_cons, pointsToBytesRO_nil, sepConj_emp]
  have h16 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
  rw [h16]
  rfl

theorem pointsToBytes_decryptionFailed_shared_lb (a : BitVec 64) :
    (a ↦₆₄ 0x6974707972636564#64) ∗ ((a + 8#64) ↦₆₄ 0x656c696166206e6f#64) ∗
      ((a + 16#64) ↦₈ 0x64#8) = (a ↦ₛ decryptionFailedStr) := by
  rw [decryptionFailedStr_split, pointsToBytes_append, pointsToBytes_append]
  change _ = (a ↦ₛ [0x64#8, 0x65#8, 0x63#8, 0x72#8, 0x79#8, 0x70#8, 0x74#8, 0x69#8]) ∗
    (((a + 8#64) ↦ₛ [0x6f#8, 0x6e#8, 0x20#8, 0x66#8, 0x61#8, 0x69#8, 0x6c#8, 0x65#8]) ∗
     ((a + 8#64 + 8#64) ↦ₛ [0x64#8]))
  rw [pointsToBytes8_eq_pointsTo64, pointsToBytes8_eq_pointsTo64,
    pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
  have h16 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
  rw [h16]
  rfl

/-! ## 2. Address, Stack, and Frame Split/Fold Lemmas -/

private theorem adrp_logFlag_eq {base entry : BitVec 64}
    (hb : base &&& 0xfff#64 = 0#64) (he : entry = base + bv% (ls_off% "session_message_decrypt_signal")) :
    ((entry + bv% (6840)) &&& bv% (2 ^ 64 - 4096)) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - page% (ls_off% "session_message_decrypt_signal" + 6840)) = base + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) := by
  subst he
  rw [BitVec.add_assoc,
    show (bv% (2 ^ 64 - 4096) : BitVec 64) = 0xfffffffffffff000#64 from rfl,
    ProofLib.ObjectLoad.adrp_page_of_aligned hb,
    show (238988#64 + 6840#64 : BitVec 64) &&& 0xfffffffffffff000#64 = 245760#64 by decide]
  bv_omega

private theorem adrp_rodata_sym_49000_eq {base entry : BitVec 64}
    (hb : base &&& 0xfff#64 = 0#64) (he : entry = base + bv% (ls_off% "session_message_decrypt_signal")) :
    ((entry + bv% (7660)) &&& bv% (2 ^ 64 - 4096)) +
      bv% (page% (ls_xref% (ls_off% "session_message_decrypt_signal" + 6324) (ls_off% "session_message_decrypt_signal" + 6328)) - page% (ls_off% "session_message_decrypt_signal" + 7000)) =
      base + bv% (page% (ls_xref% (ls_off% "session_message_decrypt_signal" + 6324) (ls_off% "session_message_decrypt_signal" + 6328))) := by
  subst he
  rw [BitVec.add_assoc,
    show (bv% (2 ^ 64 - 4096) : BitVec 64) = 0xfffffffffffff000#64 from rfl,
    ProofLib.ObjectLoad.adrp_page_of_aligned hb,
    show (238988#64 + 7660#64 : BitVec 64) &&& 0xfffffffffffff000#64 = 245760#64 by decide]
  bv_omega

private theorem stackAt_root_split_alloc (sp : BitVec 64) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - allocHookStack) ∗
        stackAt sp allocHookStack :=
  stackAt_split_bottom sp allocHookStack (rootStack - allocHookStack) (by decide)

private theorem memRegion_0xa0_split (sp : BitVec 64) :
    memRegion sp 0xa0 =
      (∃∗ w9c : BitVec 32, ∃∗ w90 : BitVec 64, ∃∗ w88 : BitVec 64, ∃∗ w80 : BitVec 64,
        memRegion sp 0x80 ∗ ((sp + 0x80#64) ↦₆₄ w80) ∗ ((sp + 0x88#64) ↦₆₄ w88) ∗
          ((sp + 0x90#64) ↦₆₄ w90) ∗ memRegion (sp + 0x98#64) 4 ∗ ((sp + 0x9c#64) ↦₃₂ w9c)) := by
  rw [memRegion_split sp 0x80 32 (by decide),
    memRegion_split (sp + 0x80#64) 8 24 (by decide),
    memRegion_split (sp + 0x80#64 + 8#64) 8 16 (by decide),
    memRegion_split (sp + 0x80#64 + 8#64 + 8#64) 8 8 (by decide),
    memRegion_split (sp + 0x80#64 + 8#64 + 8#64 + 8#64) 4 4 (by decide),
    ProofLib.memRegion_eight (sp + 0x80#64),
    ProofLib.memRegion_eight (sp + 0x80#64 + 8#64),
    ProofLib.memRegion_eight (sp + 0x80#64 + 8#64 + 8#64),
    memRegion_four (sp + 0x80#64 + 8#64 + 8#64 + 8#64 + 4#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

theorem frame_low_entails_0xa0_shared_lb (sp : BitVec 64) (w80 w88 w90 : BitVec 64) (w9c : BitVec 32) :
    memRegion sp 0x80 ∗ ((sp + 0x80#64) ↦₆₄ w80) ∗ ((sp + 0x88#64) ↦₆₄ w88) ∗
      ((sp + 0x90#64) ↦₆₄ w90) ∗ memRegion (sp + 0x98#64) 4 ∗ ((sp + 0x9c#64) ↦₃₂ w9c) ⊢
      memRegion sp 0xa0 := by
  rw [show (0xa0 : Nat) = 0x80 + 32 from rfl, memRegion_split sp 0x80 32 (by decide),
      show (32 : Nat) = 8 + 24 from rfl, memRegion_split (sp + BitVec.ofNat 64 0x80) 8 24 (by decide),
      show (24 : Nat) = 8 + 16 from rfl, memRegion_split (sp + BitVec.ofNat 64 0x80 + BitVec.ofNat 64 8) 8 16 (by decide),
      show (16 : Nat) = 8 + 8 from rfl, memRegion_split (sp + BitVec.ofNat 64 0x80 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8) 8 8 (by decide),
      show (8 : Nat) = 4 + 4 from rfl, memRegion_split (sp + BitVec.ofNat 64 0x80 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8) 4 4 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono_right (pointsTo32_entails_memRegion _ _)))))

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
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, memRegion_one]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd]

private theorem memRegion_0x920_split (sp : BitVec 64) :
    memRegion (sp + 0x4e0#64) 0x920 =
      (∃∗ w5f0 : BitVec 64, ∃∗ w5e8 : BitVec 64, ∃∗ w5e0 : BitVec 64, ∃∗ w5d8 : BitVec 64,
       ∃∗ w5d0 : BitVec 64, ∃∗ w5c8 : BitVec 64, ∃∗ w5c0 : BitVec 64, ∃∗ b5bc : BitVec 8,
       ∃∗ w5b0 : BitVec 64,
        memRegion (sp + 0x4e0#64) 0xd0 ∗
        ((sp + 0x5b0#64) ↦₆₄ w5b0) ∗ memRegion (sp + 0x5b8#64) 4 ∗
        ((sp + 0x5bc#64) ↦₈ b5bc) ∗ memRegion (sp + 0x5bd#64) 3 ∗
        ((sp + 0x5c0#64) ↦₆₄ w5c0) ∗ ((sp + 0x5c8#64) ↦₆₄ w5c8) ∗
        ((sp + 0x5d0#64) ↦₆₄ w5d0) ∗ ((sp + 0x5d8#64) ↦₆₄ w5d8) ∗
        ((sp + 0x5e0#64) ↦₆₄ w5e0) ∗ ((sp + 0x5e8#64) ↦₆₄ w5e8) ∗
        ((sp + 0x5f0#64) ↦₆₄ w5f0) ∗ memRegion (sp + 0x5f8#64) 0x808) := by
  rw [memRegion_split (sp + 0x4e0#64) 0xd0 2128 (by decide),
      memRegion_split (sp + 0x4e0#64 + 0xd0#64) 8 2120 (by decide),
      memRegion_split (sp + 0x4e0#64 + 0xd0#64 + 8#64) 4 2116 (by decide),
      memRegion_split (sp + 0x4e0#64 + 0xd0#64 + 8#64 + 4#64) 1 2115 (by decide),
      memRegion_split (sp + 0x4e0#64 + 0xd0#64 + 8#64 + 4#64 + 1#64) 3 2112 (by decide),
      memRegion_split (sp + 0x4e0#64 + 0xd0#64 + 8#64 + 4#64 + 1#64 + 3#64) 8 2104 (by decide),
      memRegion_split (sp + 0x4e0#64 + 0xd0#64 + 8#64 + 4#64 + 1#64 + 3#64 + 8#64) 8 2096 (by decide),
      memRegion_split (sp + 0x4e0#64 + 0xd0#64 + 8#64 + 4#64 + 1#64 + 3#64 + 8#64 + 8#64) 8 2088 (by decide),
      memRegion_split (sp + 0x4e0#64 + 0xd0#64 + 8#64 + 4#64 + 1#64 + 3#64 + 8#64 + 8#64 + 8#64) 8 2080 (by decide),
      memRegion_split (sp + 0x4e0#64 + 0xd0#64 + 8#64 + 4#64 + 1#64 + 3#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 2072 (by decide),
      memRegion_split (sp + 0x4e0#64 + 0xd0#64 + 8#64 + 4#64 + 1#64 + 3#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 2064 (by decide),
      memRegion_split (sp + 0x4e0#64 + 0xd0#64 + 8#64 + 4#64 + 1#64 + 3#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 0x808 (by decide),
      ProofLib.memRegion_eight (sp + 0x4e0#64 + 0xd0#64),
      memRegion_one (sp + 0x4e0#64 + 0xd0#64 + 8#64 + 4#64),
      ProofLib.memRegion_eight (sp + 0x4e0#64 + 0xd0#64 + 8#64 + 4#64 + 1#64 + 3#64),
      ProofLib.memRegion_eight (sp + 0x4e0#64 + 0xd0#64 + 8#64 + 4#64 + 1#64 + 3#64 + 8#64),
      ProofLib.memRegion_eight (sp + 0x4e0#64 + 0xd0#64 + 8#64 + 4#64 + 1#64 + 3#64 + 8#64 + 8#64),
      ProofLib.memRegion_eight (sp + 0x4e0#64 + 0xd0#64 + 8#64 + 4#64 + 1#64 + 3#64 + 8#64 + 8#64 + 8#64),
      ProofLib.memRegion_eight (sp + 0x4e0#64 + 0xd0#64 + 8#64 + 4#64 + 1#64 + 3#64 + 8#64 + 8#64 + 8#64 + 8#64),
      ProofLib.memRegion_eight (sp + 0x4e0#64 + 0xd0#64 + 8#64 + 4#64 + 1#64 + 3#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64),
      ProofLib.memRegion_eight (sp + 0x4e0#64 + 0xd0#64 + 8#64 + 4#64 + 1#64 + 3#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem frame_high_entails_0x920 (sp : BitVec 64)
    (w5b0 : BitVec 64) (b5bc : BitVec 8) (w5c0 w5c8 w5d0 w5d8 w5e0 w5e8 w5f0 : BitVec 64) :
    memRegion (sp + 0x4e0#64) 0xd0 ∗
      ((sp + 0x5b0#64) ↦₆₄ w5b0) ∗ memRegion (sp + 0x5b8#64) 4 ∗
      ((sp + 0x5bc#64) ↦₈ b5bc) ∗ memRegion (sp + 0x5bd#64) 3 ∗
      ((sp + 0x5c0#64) ↦₆₄ w5c0) ∗ ((sp + 0x5c8#64) ↦₆₄ w5c8) ∗
      ((sp + 0x5d0#64) ↦₆₄ w5d0) ∗ ((sp + 0x5d8#64) ↦₆₄ w5d8) ∗
      ((sp + 0x5e0#64) ↦₆₄ w5e0) ∗ ((sp + 0x5e8#64) ↦₆₄ w5e8) ∗
      ((sp + 0x5f0#64) ↦₆₄ w5f0) ∗ memRegion (sp + 0x5f8#64) 0x808 ⊢
      memRegion (sp + 0x4e0#64) 0x920 := by
  rw [show (0x920 : Nat) = 0xd0 + 2128 from rfl, memRegion_split (sp + 0x4e0#64) 0xd0 2128 (by decide),
      show (2128 : Nat) = 8 + 2120 from rfl, memRegion_split (sp + 0x4e0#64 + BitVec.ofNat 64 0xd0) 8 2120 (by decide),
      show (2120 : Nat) = 4 + 2116 from rfl, memRegion_split (sp + 0x4e0#64 + BitVec.ofNat 64 0xd0 + BitVec.ofNat 64 8) 4 2116 (by decide),
      show (2116 : Nat) = 1 + 2115 from rfl, memRegion_split (sp + 0x4e0#64 + BitVec.ofNat 64 0xd0 + BitVec.ofNat 64 8 + BitVec.ofNat 64 4) 1 2115 (by decide),
      show (2115 : Nat) = 3 + 2112 from rfl, memRegion_split (sp + 0x4e0#64 + BitVec.ofNat 64 0xd0 + BitVec.ofNat 64 8 + BitVec.ofNat 64 4 + BitVec.ofNat 64 1) 3 2112 (by decide),
      show (2112 : Nat) = 8 + 2104 from rfl, memRegion_split (sp + 0x4e0#64 + BitVec.ofNat 64 0xd0 + BitVec.ofNat 64 8 + BitVec.ofNat 64 4 + BitVec.ofNat 64 1 + BitVec.ofNat 64 3) 8 2104 (by decide),
      show (2104 : Nat) = 8 + 2096 from rfl, memRegion_split (sp + 0x4e0#64 + BitVec.ofNat 64 0xd0 + BitVec.ofNat 64 8 + BitVec.ofNat 64 4 + BitVec.ofNat 64 1 + BitVec.ofNat 64 3 + BitVec.ofNat 64 8) 8 2096 (by decide),
      show (2096 : Nat) = 8 + 2088 from rfl, memRegion_split (sp + 0x4e0#64 + BitVec.ofNat 64 0xd0 + BitVec.ofNat 64 8 + BitVec.ofNat 64 4 + BitVec.ofNat 64 1 + BitVec.ofNat 64 3 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8) 8 2088 (by decide),
      show (2088 : Nat) = 8 + 2080 from rfl, memRegion_split (sp + 0x4e0#64 + BitVec.ofNat 64 0xd0 + BitVec.ofNat 64 8 + BitVec.ofNat 64 4 + BitVec.ofNat 64 1 + BitVec.ofNat 64 3 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8) 8 2080 (by decide),
      show (2080 : Nat) = 8 + 2072 from rfl, memRegion_split (sp + 0x4e0#64 + BitVec.ofNat 64 0xd0 + BitVec.ofNat 64 8 + BitVec.ofNat 64 4 + BitVec.ofNat 64 1 + BitVec.ofNat 64 3 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8) 8 2072 (by decide),
      show (2072 : Nat) = 8 + 2064 from rfl, memRegion_split (sp + 0x4e0#64 + BitVec.ofNat 64 0xd0 + BitVec.ofNat 64 8 + BitVec.ofNat 64 4 + BitVec.ofNat 64 1 + BitVec.ofNat 64 3 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8) 8 2064 (by decide),
      show (2064 : Nat) = 8 + 0x808 from rfl, memRegion_split (sp + 0x4e0#64 + BitVec.ofNat 64 0xd0 + BitVec.ofNat 64 8 + BitVec.ofNat 64 4 + BitVec.ofNat 64 1 + BitVec.ofNat 64 3 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8) 8 0x808 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono_right (sepConj_mono (pointsTo8_entails_memRegion _ _)
      (sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (sepConj_mono (pointsTo64_entails_memRegion _ _)
                (sepConj_mono (pointsTo64_entails_memRegion _ _)
                  (sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _))))))))))))

private theorem memRegion_17_split (p : BitVec 64) :
    memRegion p 17 =
      (∃∗ u2 : BitVec 8, ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
        (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₆₄ u1) ∗ ((p + 16#64) ↦₈ u2)) := by
  rw [memRegion_split p 8 9 (by decide),
    memRegion_split (p + 8#64) 8 1 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, memRegion_one]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd]

def signalMessageRestAt_shared_lb (A : RustAlloc) (g : SignalMessageGhost) (a : BitVec 64)
    (m : SignalMessage) : SepProp :=
  ⌜macLength + 1 ≤ m.serialized.length ∧ m.serialized.length < 2 ^ 40 ∧
    m.ciphertext.length < 2 ^ 40 ∧ m.pqRatchet.length < 2 ^ 40 ∧
    (∀ ad, m.addresses = some ad → ad.length < 2 ^ 40)⌝ ∗
    vecU8At A a g.pqCap g.pqPtr m.pqRatchet ∗
    boxU8At A (a + 0x18#64) g.ctPtr m.ciphertext ∗
    boxU8At A (a + 0x28#64) g.serPtr m.serialized ∗
    ((a + 0x38#64) ↦ₛ m.senderRatchetKey.bytes.toList) ∗
    optBoxU8At A (a + 0x58#64) g.addrPtr m.addresses ∗
    ((a + 0x68#64) ↦₃₂ m.counter) ∗ ((a + 0x6c#64) ↦₃₂ m.previousCounter) ∗
    memRegion (a + 0x71#64) 7

theorem signalMessageAt_expose_shared_lb (A : RustAlloc) (g : SignalMessageGhost) (a : BitVec 64)
    (m : SignalMessage) :
    signalMessageAt A g a m =
      ((a + 0x70#64) ↦₈ m.messageVersion) ∗ signalMessageRestAt_shared_lb A g a m := by
  unfold signalMessageAt signalMessageRestAt_shared_lb
  ac_rfl

private theorem sepWPp_pure_mid {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B ∗ C) Q Qp) :
    SepWPp prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) Q Qp := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWPp.pure_elim h

private theorem recordResultAt_decryptionFailed_intro (A : RustAlloc) (r p : BitVec 64)
    (hp : p ≠ 0) {m : Memory} {F : SepProp}
    (hm : m ⊨ ((r ↦₆₄ speWord 24) ∗ ((r + 8#64) ↦₆₄ 17#64) ∗ ((r + 16#64) ↦₆₄ p) ∗
      ((r + 24#64) ↦₆₄ 17#64) ∗ ((r + 32#64) ↦₈ msgTypeByte .whisper) ∗
      memRegion (r + 33#64) 15 ∗ A.live p 17 1 ∗ (p ↦₆₄ 0x6974707972636564#64) ∗
      ((p + 8#64) ↦₆₄ 0x656c696166206e6f#64) ∗ ((p + 16#64) ↦₈ 0x64#8)) ∗ F) :
    m ⊨ recordResultAt A r (.error (.invalidMessage .whisper .decryptionFailed)) ∗ F := by
  have hlen : decryptionFailedStr.length = 17 := by rw [decryptionFailedStr_split]; rfl
  have h1 : m ⊨ ((r ↦₆₄ speWord 24) ∗ ((((r + 8#64) ↦₆₄ 17#64) ∗ ((r + 16#64) ↦₆₄ p) ∗
      ((r + 24#64) ↦₆₄ 17#64)) ∗ (A.live p 17 1 ∗ ((p ↦₆₄ 0x6974707972636564#64) ∗
      ((p + 8#64) ↦₆₄ 0x656c696166206e6f#64) ∗ ((p + 16#64) ↦₈ 0x64#8)) ∗
      memRegion (p + 17#64) 0)) ∗ ((r + 32#64) ↦₈ msgTypeByte .whisper) ∗
      memRegion (r + 33#64) 15) ∗ F := by
    rw [ProofLib.memRegion_zero, sepConj_emp]
    arm64_sep_close
  rw [pointsToBytes_decryptionFailed_shared_lb p] at h1
  unfold recordResultAt vecU8 vecU8At vecHeader
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
  refine ⟨17#64, p, ?_⟩
  have hp' : ¬ p = 0#64 := hp
  simp only [hlen, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.le_refl,
    Nat.sub_self, BitVec.ofNat_eq_ofNat]
  rw [show (r + 8#64 + 8#64) = r + 16#64 by bv_omega,
      show (r + 8#64 + 16#64) = r + 24#64 by bv_omega]
  simpa [sepConj_assoc, satisfies_pure_sepConj, hp'] using h1

theorem allocFailedIn_of_load_oom_shared_lb {s0 s s_call sf_2 s' : State} {evs : List TraceEvent}
    (htr : s.trace = s0.trace ++ evs)
    (hcall : s_call.trace = s.trace)
    (hoom : sf_2.trace = s_call.trace ++ [allocFailedEvent])
    (hpref : sf_2.trace <+: s'.trace) :
    s0.trace <+: s'.trace ∧ allocFailedIn s0 s' := by
  rcases hpref with ⟨tail, htr'⟩
  rw [hoom, hcall, htr, List.append_assoc, List.append_assoc] at htr'
  refine ⟨⟨evs ++ ([allocFailedEvent] ++ tail), htr'⟩, ?_⟩
  unfold allocFailedIn
  rw [← htr', List.drop_left]
  exact List.mem_append_right _ (List.mem_cons_self ..)

/-! ## 3. Active Footprint, Passive Frame, and `segRegionNone_ok` -/

private def segRegionNoneAct (A : RustAlloc) (img : Obj.Image) (x : DecryptGhost) (sp : BitVec 64)
    (w80 w88 w90 : BitVec 64) (w9c : BitVec 32)
    (w0 w1 w2 w3 : BitVec 64) (b4 : BitVec 8)
    (w5b0 : BitVec 64) (b5bc : BitVec 8) (w5c0 w5c8 w5d0 w5d8 w5e0 w5e8 w5f0 : BitVec 64) :
    SepProp :=
  ((img.base + bv% (ls_xref% (ls_off% "session_message_decrypt_signal" + 6324) (ls_off% "session_message_decrypt_signal" + 6328))) ↦₆₄ᵣ 0x6974707972636564#64) ∗
  ((img.base + bv% (ls_xref% (ls_off% "session_message_decrypt_signal" + 6324) (ls_off% "session_message_decrypt_signal" + 6328)) + 8#64) ↦₆₄ᵣ 0x656c696166206e6f#64) ∗
  ((img.base + bv% (ls_xref% (ls_off% "session_message_decrypt_signal" + 6324) (ls_off% "session_message_decrypt_signal" + 6328)) + 16#64) ↦₈ᵣ 0x64#8) ∗
  ((sp + 0x80#64) ↦₆₄ w80) ∗ ((sp + 0x88#64) ↦₆₄ w88) ∗ ((sp + 0x90#64) ↦₆₄ w90) ∗
  ((sp + 0x9c#64) ↦₃₂ w9c) ∗
  ((sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((sp + 0xf0#64) ↦₆₄ x.locA) ∗
  ((sp + 0x130#64) ↦₆₄ 0#64) ∗ ((sp + 0x138#64) ↦₆₄ noneCap) ∗
  ((x.msgA + 0x70#64) ↦₈ x.msg.messageVersion) ∗
  ((sp + 0x4b0#64) ↦₆₄ w0) ∗ ((sp + 0x4b0#64 + 8#64) ↦₆₄ w1) ∗
  ((sp + 0x4b0#64 + 16#64) ↦₆₄ w2) ∗ ((sp + 0x4b0#64 + 24#64) ↦₆₄ w3) ∗
  ((sp + 0x4b0#64 + 32#64) ↦₈ b4) ∗ memRegion (sp + 0x4b0#64 + 33#64) 15 ∗
  ((sp + 0x5b0#64) ↦₆₄ w5b0) ∗ ((sp + 0x5bc#64) ↦₈ b5bc) ∗
  ((sp + 0x5c0#64) ↦₆₄ w5c0) ∗ ((sp + 0x5c8#64) ↦₆₄ w5c8) ∗
  ((sp + 0x5d0#64) ↦₆₄ w5d0) ∗ ((sp + 0x5d8#64) ↦₆₄ w5d8) ∗
  ((sp + 0x5e0#64) ↦₆₄ w5e0) ∗ ((sp + 0x5e8#64) ↦₆₄ w5e8) ∗
  ((sp + 0x5f0#64) ↦₆₄ w5f0) ∗
  ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
  stackAt sp allocHookStack ∗ A.pool

private def segRegionNoneFrame (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (x : DecryptGhost)
    (s0 : State) (sp prevCap prevPtr : BitVec 64) : SepProp :=
  memRegion sp 0x80 ∗ memRegion (sp + 0x98#64) 4 ∗
  ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ memRegion (sp + 0x140#64) 336 ∗
  memRegion (sp + 0x4e0#64) 0xd0 ∗ memRegion (sp + 0x5b8#64) 4 ∗
  memRegion (sp + 0x5bd#64) 3 ∗ memRegion (sp + 0x5f8#64) 0x808 ∗
  protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
  signalMessageRestAt_shared_lb A x.msgG x.msgA x.msg ∗ tapeAt ctl x.cur x.rest ∗
  memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - allocHookStack) ∗
  wsRegionFrameV img kit ikit x s0 prevCap prevPtr ∗
  decStoreExtra kit ikit st0 ist0 s0

private def segRegionNonePost (A : RustAlloc) (img : Obj.Image) (x : DecryptGhost) (sp : BitVec 64) :
    SepProp :=
  ((sp + 0x80#64) ↦₆₄ x.ret) ∗ ((sp + 0x88#64) ↦₆₄ x.locA) ∗ ((sp + 0x90#64) ↦₆₄ x.msgA) ∗
  ((sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
  ((sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((sp + 0xf0#64) ↦₆₄ x.locA) ∗
  ((sp + 0x130#64) ↦₆₄ 0#64) ∗ ((sp + 0x138#64) ↦₆₄ noneCap) ∗
  ((x.msgA + 0x70#64) ↦₈ x.msg.messageVersion) ∗
  recordResultAt A (sp + 0x4b0#64) (.error (.invalidMessage .whisper .decryptionFailed)) ∗
  ((sp + 0x5b0#64) ↦₆₄ x.remA) ∗ ((sp + 0x5bc#64) ↦₈ msgTypeByte .whisper) ∗
  ((sp + 0x5c0#64) ↦₆₄ (sp + 0x5bc#64)) ∗ ((sp + 0x5c8#64) ↦₆₄ x.msgA) ∗
  ((sp + 0x5d0#64) ↦₆₄ (sp + 0x5b0#64)) ∗ ((sp + 0x5d8#64) ↦₆₄ 0#64) ∗
  ((sp + 0x5e0#64) ↦₆₄ 8#64) ∗ ((sp + 0x5e8#64) ↦₆₄ 0#64) ∗
  ((sp + 0x5f0#64) ↦₆₄ (bv% (2 ^ 64 - 1))) ∗
  ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
  stackAt sp allocHookStack ∗ A.pool

theorem segRegionNoneV_ok {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} :
    SegRegionNoneSpecV img C A ctl uuidTryParse S encRecord abs kit ikit st0 ist0 Scope := by
  intro hhyps x ans R s0 s hRN hL
  have himg := hhyps.loads
  have hhooks := hhyps.hooks.toTripleRatchetHooks
  clear hhyps
  obtain ⟨hpc_s, ⟨hrun, hsp, hsp0_align, hsp_align, hx29, hx27, hfl, hsym, hvregs⟩,
    rec, prevCap, prevPtr, hans, hscope, hcur, htrace, hmem⟩ := hRN
  set sp := s0.sp - 0xee0#64
  have hsp_align_bv : (sp &&& 15#64 == 0#64) = true := by
    simpa [State.spAligned, hsp] using hsp_align
  have hro : img.RoDataLoaded s.mem := (Obj.Image.frozenLoaded_iff.mp hfl).2.1
  have hb : img.base &&& 0xfff#64 = 0#64 := ProofLib.ObjectLoad.base_aligned_of_loads himg
  rw [recordRegionEntry,
    entryOf_eq_tripleRatchetProgAt (C := C) (ctl := ctl) (abs := abs) himg msgDecryptName] at hpc_s
  have hfn : libsignalSessionCode.fnOff msgDecryptName = num% (ls_off% "session_message_decrypt_signal") :=
    libsignalSessionCode_fnOff_sym_3a4a8
  have hshim := shim_ok_at img.base C ctl abs msgDecryptName (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "session_message_decrypt_signal"))
    (by rw [hfn, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  have halloc := alloc_ok_at img.base C A ctl abs
    hhooks.alloc msgDecryptName (num% (ls_off% "__rustc::__rust_alloc" - ls_off% "session_message_decrypt_signal"))
    (by rw [hfn, (ls_stub% "__rustc::__rust_alloc")])
  have hpanic := panic_at_handle_error img.base C ctl abs msgDecryptName (num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "session_message_decrypt_signal"))
    (by rw [hfn, (ls_stub% "alloc::raw_vec::handle_error")])
  have hadp_log :
      (((tripleRatchetProgAt img.base C ctl abs).fnAddr msgDecryptName + 6840#64) &&&
        bv% (2 ^ 64 - 4096)) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - page% (ls_off% "session_message_decrypt_signal" + 6840)) = img.base + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) :=
    adrp_logFlag_eq hb (by rw [tripleRatchetProgAt, Program.fnAddr_rebase, hfn])
  have hadp_ro :
      (((tripleRatchetProgAt img.base C ctl abs).fnAddr msgDecryptName + 7660#64) &&&
        bv% (2 ^ 64 - 4096)) + bv% (page% (ls_xref% (ls_off% "session_message_decrypt_signal" + 6324) (ls_off% "session_message_decrypt_signal" + 6328)) - page% (ls_off% "session_message_decrypt_signal" + 7000)) =
        img.base + bv% (page% (ls_xref% (ls_off% "session_message_decrypt_signal" + 6324) (ls_off% "session_message_decrypt_signal" + 6328))) :=
    adrp_rodata_sym_49000_eq hb (by rw [tripleRatchetProgAt, Program.fnAddr_rebase, hfn])
  unfold regionNonePre logOff at hmem
  rw [hsp, sepConj_assoc, satisfies_pure_sepConj] at hmem
  obtain ⟨⟨_, _, _, _, hx19, hx23, hx24, _hroot⟩, hmem⟩ := hmem
  have hmem_ro := rodata_decryptionFailed_intro himg hro hmem
  clear hmem
  rw [pointsToBytesRO_decryptionFailed_shared_lb,
    memRegion_0xa0_split sp,
    show (0x950 : Nat) = 48 + 0x920 from rfl,
    memRegion_split (sp + 0x4b0#64) 48 0x920 (by decide),
    show sp + 0x4b0#64 + 48#64 = sp + 0x4e0#64 by bv_omega,
    memRegion_slot48_split (sp + 0x4b0#64),
    memRegion_0x920_split sp,
    signalMessageAt_expose_shared_lb A x.msgG x.msgA x.msg,
    stackAt_root_split_alloc sp] at hmem_ro
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem_ro
  obtain ⟨w5f0, w5e8, w5e0, w5d8, w5d0, w5c8, w5c0, b5bc, w5b0,
    b4, w3, w2, w1, w0, w9c, w90, w88, w80, hmem_ro⟩ := hmem_ro
  have hmem_split : s.mem ⊨
      segRegionNoneAct A img x sp w80 w88 w90 w9c w0 w1 w2 w3 b4
        w5b0 b5bc w5c0 w5c8 w5d0 w5d8 w5e0 w5e8 w5f0 ∗
      (segRegionNoneFrame A ctl img kit ikit st0 ist0 x s0 sp prevCap prevPtr ∗ R) := by
    dsimp only [segRegionNoneAct, segRegionNoneFrame]
    arm64_sep_close
  clear hmem_ro
  have hwp : SepWPp (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr msgDecryptName + 8016#64) s
      (segRegionNoneAct A img x sp w80 w88 w90 w9c w0 w1 w2 w3 b4
        w5b0 b5bc w5c0 w5c8 w5d0 w5d8 w5e0 w5e8 w5f0)
      (fun s' P_f =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x29 = s0.sp - 96#64 ∧ s'.trace = s.trace ∧
        s'.readReg64 .x26 = sp + 0xa0#64 ∧ s'.readReg64 .x27 = x.ret ∧
        s'.readReg64 .x28 = speWord 24 ∧ calleeSavedVRegs s' = calleeSavedVRegs s0 ∧
        (∀ m F, (m ⊨ P_f ∗ F) → (m ⊨ segRegionNonePost A img x sp ∗ F)))
      (fun s' _ => s0.trace <+: s'.trace ∧ allocFailedIn s0 s') := by
    dsimp only [segRegionNoneAct]
    messageDecryptRegionNone_fetches img.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x1a8 84
    messageDecryptRegionNone_fetches img.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x85c 16
    messageDecryptRegionNone_fetches img.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x16e4 16
    messageDecryptRegionNone_fetches img.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x1ab4 20
    messageDecryptRegionNone_fetches img.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x1b00 12
    messageDecryptRegionNone_fetches img.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x1cf0 8
    messageDecryptRegionNone_fetches img.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x1dd4 88
    messageDecryptRegionNone_fetches img.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x2640 12
    messageDecryptRegionNone_fetches img.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x1e8c 12
    messageDecryptRegionNone_fetches img.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x1f34 8
    dsimp only [tripleRatchetProgAt] at hpc_s hshim halloc hpanic hadp_log hadp_ro ⊢
    clear himg hhooks hfn hb
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr msgDecryptName = entry
    examples_hide_fetches
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hlay : LayoutOk 17 1 := ⟨by decide, hpow2, by decide⟩
    have hnone_beq : (noneCap + 1#64 == 0#64) = true := by decide
    apply SepWPp.of_sepWP (mid := entry + bv% (7652))
    wp_steps
    wp_apply
    wp_steps
    wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
    · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]
      refine sepWPp_pure_mid fun htr_oom => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "session_message_decrypt_signal"))
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) ?_
      exact allocFailedIn_of_load_oom_shared_lb htrace (by simp only [wp_norm, arm64_norm, *])
        htr_oom (by simp [Rust.panicked, wp_norm, arm64_norm, *])
    · have hoom' : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0 := hoom
      have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false :=
        beq_eq_false_iff_ne.mpr hoom
      simp only [hoom', ite_false, sepConj_assoc]
      refine sepWPp_pure_mid fun ⟨_, htr_ok⟩ => ?_
      rw [memRegion_17_split (sf_1.readReg64 (Reg.gpr 0#5))]
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
      rw [h_1, hsp] at hm
      have hm_drop : m ⊨
          (((img.base + bv% (ls_xref% (ls_off% "session_message_decrypt_signal" + 6324) (ls_off% "session_message_decrypt_signal" + 6328))) ↦₆₄ᵣ 7598822138193339748#64) ∗
           ((img.base + bv% ((ls_xref% (ls_off% "session_message_decrypt_signal" + 6324) (ls_off% "session_message_decrypt_signal" + 6328)) + 8)) ↦₆₄ᵣ 7308332162361618031#64) ∗
           ((img.base + bv% ((ls_xref% (ls_off% "session_message_decrypt_signal" + 6324) (ls_off% "session_message_decrypt_signal" + 6328)) + 16)) ↦₈ᵣ 100#8)) ∗
          (((sp + 0x4b0#64) ↦₆₄ speWord 24 ∗ ((sp + 0x4b0#64 + 8#64) ↦₆₄ 17#64) ∗
            ((sp + 0x4b0#64 + 16#64) ↦₆₄ sf_1.readReg64 (Reg.gpr 0#5)) ∗
            ((sp + 0x4b0#64 + 24#64) ↦₆₄ 17#64) ∗
            ((sp + 0x4b0#64 + 32#64) ↦₈ msgTypeByte .whisper) ∗
            memRegion (sp + 0x4b0#64 + 33#64) 15 ∗
            A.live (sf_1.readReg64 (Reg.gpr 0#5)) 17 1 ∗
            (sf_1.readReg64 (Reg.gpr 0#5) ↦₆₄ 0x6974707972636564#64) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ 0x656c696166206e6f#64) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 16#64) ↦₈ 0x64#8)) ∗
           (((sp + 0x80#64) ↦₆₄ x.ret) ∗ ((sp + 0x88#64) ↦₆₄ x.locA) ∗
            ((sp + 0x90#64) ↦₆₄ x.msgA) ∗
            ((sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
            ((sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((sp + 0xf0#64) ↦₆₄ x.locA) ∗
            ((sp + 0x130#64) ↦₆₄ 0#64) ∗ ((sp + 0x138#64) ↦₆₄ noneCap) ∗
            ((x.msgA + 0x70#64) ↦₈ x.msg.messageVersion) ∗
            ((sp + 0x5b0#64) ↦₆₄ x.remA) ∗ ((sp + 0x5bc#64) ↦₈ msgTypeByte .whisper) ∗
            ((sp + 0x5c0#64) ↦₆₄ (sp + 0x5bc#64)) ∗ ((sp + 0x5c8#64) ↦₆₄ x.msgA) ∗
            ((sp + 0x5d0#64) ↦₆₄ (sp + 0x5b0#64)) ∗ ((sp + 0x5d8#64) ↦₆₄ 0#64) ∗
            ((sp + 0x5e0#64) ↦₆₄ 8#64) ∗ ((sp + 0x5e8#64) ↦₆₄ 0#64) ∗
            ((sp + 0x5f0#64) ↦₆₄ (bv% (2 ^ 64 - 1))) ∗
            ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
            stackAt sp allocHookStack ∗ A.pool ∗ F)) := by
        dsimp only [speWord, msgTypeByte]
        arm64_sep_close
      clear hm
      have hm_keep := Satisfies.of_sep_right hm_drop
      clear hm_drop
      have hm_res := recordResultAt_decryptionFailed_intro A (sp + 0x4b0#64)
        (sf_1.readReg64 (Reg.gpr 0#5)) hoom' hm_keep
      clear hm_keep
      exact Eq.mp (congrArg (m ⊨ ·) (by unfold segRegionNonePost; ac_rfl)) hm_res
  obtain ⟨s', hsteps, hout⟩ :=
    hwp (segRegionNoneFrame A ctl img kit ikit st0 ist0 x s0 sp prevCap prevPtr ∗ R) hmem_split hL
  rcases hout with ⟨hpc', hrun', P_f, hmf, hsp', hsp_align', hx29', htr', hx26', hx27', hx28', hvregs', hent⟩ |
      ⟨hpan, P_f, hmf, hP⟩ | ⟨_, _hoom⟩
  · refine ⟨s', hsteps, Or.inl ?_⟩
    have hpc_exit : s'.pc = recordRegionExit img := by
      rw [recordRegionExit,
        entryOf_eq_tripleRatchetProgAt (C := C) (ctl := ctl) (abs := abs) himg msgDecryptName]
      exact hpc'
    have hmeta' : wsMeta img x s0 s' :=
      ⟨hrun', hsp', hsp0_align, hsp_align', hx29', hx27',
        hsteps.frozenLoaded hfl, hsteps.symtab_eq.trans hsym, hvregs'⟩
    refine ⟨hpc_exit, hmeta', hx26', hx28', rec, prevCap, prevPtr, hans, hscope, hcur,
      htr'.trans htrace, ?_⟩
    have hmf' := hent s'.mem (segRegionNoneFrame A ctl img kit ikit st0 ist0 x s0 sp prevCap prevPtr ∗ R) hmf
    clear hmf
    have hmf_rearr : s'.mem ⊨
        (memRegion sp 0x80 ∗ ((sp + 0x80#64) ↦₆₄ x.ret) ∗ ((sp + 0x88#64) ↦₆₄ x.locA) ∗
          ((sp + 0x90#64) ↦₆₄ x.msgA) ∗ memRegion (sp + 0x98#64) 4 ∗
          ((sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32)) ∗
        ((memRegion (sp + 0x4e0#64) 0xd0 ∗
          ((sp + 0x5b0#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x5b8#64) 4 ∗
          ((sp + 0x5bc#64) ↦₈ msgTypeByte .whisper) ∗ memRegion (sp + 0x5bd#64) 3 ∗
          ((sp + 0x5c0#64) ↦₆₄ (sp + 0x5bc#64)) ∗ ((sp + 0x5c8#64) ↦₆₄ x.msgA) ∗
          ((sp + 0x5d0#64) ↦₆₄ (sp + 0x5b0#64)) ∗ ((sp + 0x5d8#64) ↦₆₄ 0#64) ∗
          ((sp + 0x5e0#64) ↦₆₄ 8#64) ∗ ((sp + 0x5e8#64) ↦₆₄ 0#64) ∗
          ((sp + 0x5f0#64) ↦₆₄ (bv% (2 ^ 64 - 1))) ∗ memRegion (sp + 0x5f8#64) 0x808) ∗
         (wsMsgCells x sp ∗
          ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
          ((sp + 0x138#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x140#64) 336 ∗
          recordResultAt A (sp + 0x4b0#64) (.error (.invalidMessage .whisper .decryptionFailed)) ∗
          protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
          (((x.msgA + 0x70#64) ↦₈ x.msg.messageVersion) ∗
            signalMessageRestAt_shared_lb A x.msgG x.msgA x.msg) ∗
          tapeAt ctl x.cur x.rest ∗ logOff img ∗
          (memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - allocHookStack) ∗
            stackAt sp allocHookStack) ∗
          A.pool ∗ wsRegionFrameV img kit ikit x s0 prevCap prevPtr ∗
          decStoreExtra kit ikit st0 ist0 s0 ∗ R)) := by
      dsimp only [segRegionNonePost, segRegionNoneFrame, wsMsgCells, logOff] at hmf' ⊢
      arm64_sep_close
    clear hmf'
    rw [← signalMessageAt_expose_shared_lb A x.msgG x.msgA x.msg,
        ← stackAt_root_split_alloc sp] at hmf_rearr
    have hmf_fold := Satisfies.mono
      (sepConj_mono (frame_low_entails_0xa0_shared_lb sp x.ret x.locA x.msgA _)
        (sepConj_mono_left (frame_high_entails_0x920 sp x.remA (msgTypeByte .whisper)
          (sp + 0x5bc#64) x.msgA (sp + 0x5b0#64) 0#64 8#64 0#64 (bv% (2 ^ 64 - 1)))))
      hmf_rearr
    clear hmf_rearr
    dsimp only [sp] at hmf_fold
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmf_fold
  · refine ⟨s', hsteps, Or.inr (Or.inr (Or.inl ⟨hpan, ?_⟩))⟩
    have hmf' : s'.mem ⊨
        (P_f ∗ segRegionNoneFrame A ctl img kit ikit st0 ist0 x s0 sp prevCap prevPtr) ∗ R := by
      rwa [← sepConj_assoc] at hmf
    exact allowPanic_panicked ⟨hP.1, Or.inl hP.2⟩ hmf'
  · dsimp only at _hoom
    exact (not_satisfies_false_sepConj _hoom).elim

theorem segRegionNone_ok {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} :
    SegRegionNoneSpec img C A ctl uuidTryParse S encRecord abs :=
  segRegionNoneV_ok

/-! ## Relocatable `[LibsignalPlacement]` Proofs -/

section Placed

open CryptoVerification CryptoVerification.LibsignalPublicApi.Placed

private abbrev decryptionFailedSym : String :=
  "libsignal_session:.rodata..Lanon.43"

private theorem rodata_decryptionFailed_placed_intro [LibsignalPlacement]
    {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ ((lsmpl.ρ decryptionFailedSym) ↦ᵣ decryptionFailedStr) ∗ P :=
  lsro_intro_chk hro (by rfl_kernel) hP

private def segRegionNoneActPlaced [LibsignalPlacement] (A : RustAlloc) (x : DecryptGhost)
    (sp : BitVec 64) (w80 w88 w90 : BitVec 64) (w9c : BitVec 32)
    (w0 w1 w2 w3 : BitVec 64) (b4 : BitVec 8)
    (w5b0 : BitVec 64) (b5bc : BitVec 8) (w5c0 w5c8 w5d0 w5d8 w5e0 w5e8 w5f0 : BitVec 64) :
    SepProp :=
  ((lsmpl.ρ decryptionFailedSym) ↦₆₄ᵣ 0x6974707972636564#64) ∗
  ((lsmpl.ρ decryptionFailedSym + 8#64) ↦₆₄ᵣ 0x656c696166206e6f#64) ∗
  ((lsmpl.ρ decryptionFailedSym + 16#64) ↦₈ᵣ 0x64#8) ∗
  ((sp + 0x80#64) ↦₆₄ w80) ∗ ((sp + 0x88#64) ↦₆₄ w88) ∗ ((sp + 0x90#64) ↦₆₄ w90) ∗
  ((sp + 0x9c#64) ↦₃₂ w9c) ∗
  ((sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((sp + 0xf0#64) ↦₆₄ x.locA) ∗
  ((sp + 0x130#64) ↦₆₄ 0#64) ∗ ((sp + 0x138#64) ↦₆₄ noneCap) ∗
  ((x.msgA + 0x70#64) ↦₈ x.msg.messageVersion) ∗
  ((sp + 0x4b0#64) ↦₆₄ w0) ∗ ((sp + 0x4b0#64 + 8#64) ↦₆₄ w1) ∗
  ((sp + 0x4b0#64 + 16#64) ↦₆₄ w2) ∗ ((sp + 0x4b0#64 + 24#64) ↦₆₄ w3) ∗
  ((sp + 0x4b0#64 + 32#64) ↦₈ b4) ∗ memRegion (sp + 0x4b0#64 + 33#64) 15 ∗
  ((sp + 0x5b0#64) ↦₆₄ w5b0) ∗ ((sp + 0x5bc#64) ↦₈ b5bc) ∗
  ((sp + 0x5c0#64) ↦₆₄ w5c0) ∗ ((sp + 0x5c8#64) ↦₆₄ w5c8) ∗
  ((sp + 0x5d0#64) ↦₆₄ w5d0) ∗ ((sp + 0x5d8#64) ↦₆₄ w5d8) ∗
  ((sp + 0x5e0#64) ↦₆₄ w5e0) ∗ ((sp + 0x5e8#64) ↦₆₄ w5e8) ∗
  ((sp + 0x5f0#64) ↦₆₄ w5f0) ∗
  (lsLogFilterAddr ↦₆₄ 0#64) ∗
  stackAt sp allocHookStack ∗ A.pool

private def segRegionNoneFramePlaced (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (x : DecryptGhost)
    (s0 : State) (sp prevCap prevPtr : BitVec 64) : SepProp :=
  memRegion sp 0x80 ∗ memRegion (sp + 0x98#64) 4 ∗
  ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ memRegion (sp + 0x140#64) 336 ∗
  memRegion (sp + 0x4e0#64) 0xd0 ∗ memRegion (sp + 0x5b8#64) 4 ∗
  memRegion (sp + 0x5bd#64) 3 ∗ memRegion (sp + 0x5f8#64) 0x808 ∗
  protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
  signalMessageRestAt_shared_lb A x.msgG x.msgA x.msg ∗ tapeAt ctl x.cur x.rest ∗
  memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - allocHookStack) ∗
  wsRegionFrameVPlaced kit ikit x s0 prevCap prevPtr ∗
  decStoreExtraPlaced kit ikit st0 ist0 s0

private def segRegionNonePostPlaced [LibsignalPlacement] (A : RustAlloc) (x : DecryptGhost)
    (sp : BitVec 64) : SepProp :=
  ((sp + 0x80#64) ↦₆₄ x.ret) ∗ ((sp + 0x88#64) ↦₆₄ x.locA) ∗ ((sp + 0x90#64) ↦₆₄ x.msgA) ∗
  ((sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
  ((sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((sp + 0xf0#64) ↦₆₄ x.locA) ∗
  ((sp + 0x130#64) ↦₆₄ 0#64) ∗ ((sp + 0x138#64) ↦₆₄ noneCap) ∗
  ((x.msgA + 0x70#64) ↦₈ x.msg.messageVersion) ∗
  recordResultAt A (sp + 0x4b0#64) (.error (.invalidMessage .whisper .decryptionFailed)) ∗
  ((sp + 0x5b0#64) ↦₆₄ x.remA) ∗ ((sp + 0x5bc#64) ↦₈ msgTypeByte .whisper) ∗
  ((sp + 0x5c0#64) ↦₆₄ (sp + 0x5bc#64)) ∗ ((sp + 0x5c8#64) ↦₆₄ x.msgA) ∗
  ((sp + 0x5d0#64) ↦₆₄ (sp + 0x5b0#64)) ∗ ((sp + 0x5d8#64) ↦₆₄ 0#64) ∗
  ((sp + 0x5e0#64) ↦₆₄ 8#64) ∗ ((sp + 0x5e8#64) ↦₆₄ 0#64) ∗
  ((sp + 0x5f0#64) ↦₆₄ (bv% (2 ^ 64 - 1))) ∗
  (lsLogFilterAddr ↦₆₄ 0#64) ∗
  stackAt sp allocHookStack ∗ A.pool

theorem segRegionNoneVPlaced_ok [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} :
    SegRegionNoneSpecVPlaced C A ctl uuidTryParse S encRecord H kit ikit st0 ist0 Scope := by
  intro hhyps x ans R s0 s hRN hL
  obtain ⟨hpc_s, ⟨hrun, hsp, hsp0_align, hsp_align, hx29, hx27, hcrl, hvregs⟩,
    rec, prevCap, prevPtr, hans, hscope, hcur, htrace, hmem⟩ := hRN
  set sp := s0.sp - 0xee0#64
  have hsp_align_bv : (sp &&& 15#64 == 0#64) = true := by
    simpa [State.spAligned, hsp] using hsp_align
  have hro : LibsignalRoLoaded lsmpl s.mem := hcrl.2
  dsimp only [Record.recEntryPlaced] at hpc_s
  change s.pc = (blkPl_197).base + 424#64 at hpc_s
  have hshim : subroutine_ok (lsProg_197 H) (lsρ lsRustNoAllocShimSym) sessionShimSpec :=
    ls_hook_ok_of_mem (i := 197) hhyps.hooks.shim
  have halloc : subroutine_ok (lsProg_197 H) (lsρ lsRustAllocSym) (rustAllocSpec A) :=
    ls_hook_ok_of_mem (i := 197) hhyps.hooks.alloc
  have hpanic : (lsProg_197 H).externAt? (lsρ lsHandleErrorSym) = some Rust.panicked := by
    rw [ls_externAt?_of_mem (prog := lsProg_197 H) (i := 197), hhyps.hooks.handleError]
  clear hhyps
  unfold regionNonePrePlaced FromRecordCallees.lsLogOff at hmem
  rw [hsp, sepConj_assoc, satisfies_pure_sepConj] at hmem
  obtain ⟨⟨_, _, _, hx19, hx23, hx24, _hroot⟩, hmem⟩ := hmem
  have hmem_ro := rodata_decryptionFailed_placed_intro hro hmem
  clear hmem
  rw [pointsToBytesRO_decryptionFailed_shared_lb,
    memRegion_0xa0_split sp,
    show (0x950 : Nat) = 48 + 0x920 from rfl,
    memRegion_split (sp + 0x4b0#64) 48 0x920 (by decide),
    show sp + 0x4b0#64 + 48#64 = sp + 0x4e0#64 by bv_omega,
    memRegion_slot48_split (sp + 0x4b0#64),
    memRegion_0x920_split sp,
    signalMessageAt_expose_shared_lb A x.msgG x.msgA x.msg,
    stackAt_root_split_alloc sp] at hmem_ro
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem_ro
  obtain ⟨w5f0, w5e8, w5e0, w5d8, w5d0, w5c8, w5c0, b5bc, w5b0,
    b4, w3, w2, w1, w0, w9c, w90, w88, w80, hmem_ro⟩ := hmem_ro
  have hmem_split : s.mem ⊨
      segRegionNoneActPlaced A x sp w80 w88 w90 w9c w0 w1 w2 w3 b4
        w5b0 b5bc w5c0 w5c8 w5d0 w5d8 w5e0 w5e8 w5f0 ∗
      (segRegionNoneFramePlaced A ctl kit ikit st0 ist0 x s0 sp prevCap prevPtr ∗ R) := by
    dsimp only [segRegionNoneActPlaced, segRegionNoneFramePlaced]
    arm64_sep_close
  clear hmem_ro
  have hwp : SepWPp (lsProg_197 H)
      (blkPl_197.base + 8016#64) s
      (segRegionNoneActPlaced A x sp w80 w88 w90 w9c w0 w1 w2 w3 b4
        w5b0 b5bc w5c0 w5c8 w5d0 w5d8 w5e0 w5e8 w5f0)
      (fun s' P_f =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x29 = s0.sp - 96#64 ∧ s'.trace = s.trace ∧
        s'.readReg64 .x26 = sp + 0xa0#64 ∧ s'.readReg64 .x27 = x.ret ∧
        s'.readReg64 .x28 = speWord 24 ∧ calleeSavedVRegs s' = calleeSavedVRegs s0 ∧
        (∀ m F, (m ⊨ P_f ∗ F) → (m ⊨ segRegionNonePostPlaced A x sp ∗ F)))
      (fun s' _ => s0.trace <+: s'.trace ∧ allocFailedIn s0 s') := by
    dsimp only [segRegionNoneActPlaced]
    dsimp only [lsProg_197] at hpc_s hshim halloc hpanic ⊢
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hlay : LayoutOk 17 1 := ⟨by decide, hpow2, by decide⟩
    have hnone_beq : (noneCap + 1#64 == 0#64) = true := by decide
    apply SepWPp.of_sepWP (mid := blkPl_197.base + bv% (7652))
    wp_steps
    wp_apply
    wp_steps
    wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
    · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]
      refine sepWPp_pure_mid fun htr_oom => ?_
      apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) ?_
      exact allocFailedIn_of_load_oom_shared_lb htrace (by simp only [wp_norm, arm64_norm, *])
        htr_oom (by simp [Rust.panicked, wp_norm, arm64_norm, *])
    · have hoom' : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0 := hoom
      have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false :=
        beq_eq_false_iff_ne.mpr hoom
      simp only [hoom', ite_false, sepConj_assoc]
      refine sepWPp_pure_mid fun ⟨_, htr_ok⟩ => ?_
      rw [memRegion_17_split (sf_1.readReg64 (Reg.gpr 0#5))]
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
      rw [h_1, hsp] at hm
      have hm_drop : m ⊨
          (((lsmpl.ρ decryptionFailedSym) ↦₆₄ᵣ 7598822138193339748#64) ∗
           ((lsmpl.ρ decryptionFailedSym + 8#64) ↦₆₄ᵣ 7308332162361618031#64) ∗
           ((lsmpl.ρ decryptionFailedSym + 16#64) ↦₈ᵣ 100#8)) ∗
          (((sp + 0x4b0#64) ↦₆₄ speWord 24 ∗ ((sp + 0x4b0#64 + 8#64) ↦₆₄ 17#64) ∗
            ((sp + 0x4b0#64 + 16#64) ↦₆₄ sf_1.readReg64 (Reg.gpr 0#5)) ∗
            ((sp + 0x4b0#64 + 24#64) ↦₆₄ 17#64) ∗
            ((sp + 0x4b0#64 + 32#64) ↦₈ msgTypeByte .whisper) ∗
            memRegion (sp + 0x4b0#64 + 33#64) 15 ∗
            A.live (sf_1.readReg64 (Reg.gpr 0#5)) 17 1 ∗
            (sf_1.readReg64 (Reg.gpr 0#5) ↦₆₄ 0x6974707972636564#64) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ 0x656c696166206e6f#64) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 16#64) ↦₈ 0x64#8)) ∗
           (((sp + 0x80#64) ↦₆₄ x.ret) ∗ ((sp + 0x88#64) ↦₆₄ x.locA) ∗
            ((sp + 0x90#64) ↦₆₄ x.msgA) ∗
            ((sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
            ((sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((sp + 0xf0#64) ↦₆₄ x.locA) ∗
            ((sp + 0x130#64) ↦₆₄ 0#64) ∗ ((sp + 0x138#64) ↦₆₄ noneCap) ∗
            ((x.msgA + 0x70#64) ↦₈ x.msg.messageVersion) ∗
            ((sp + 0x5b0#64) ↦₆₄ x.remA) ∗ ((sp + 0x5bc#64) ↦₈ msgTypeByte .whisper) ∗
            ((sp + 0x5c0#64) ↦₆₄ (sp + 0x5bc#64)) ∗ ((sp + 0x5c8#64) ↦₆₄ x.msgA) ∗
            ((sp + 0x5d0#64) ↦₆₄ (sp + 0x5b0#64)) ∗ ((sp + 0x5d8#64) ↦₆₄ 0#64) ∗
            ((sp + 0x5e0#64) ↦₆₄ 8#64) ∗ ((sp + 0x5e8#64) ↦₆₄ 0#64) ∗
            ((sp + 0x5f0#64) ↦₆₄ (bv% (2 ^ 64 - 1))) ∗
            (lsLogFilterAddr ↦₆₄ 0#64) ∗
            stackAt sp allocHookStack ∗ A.pool ∗ F)) := by
        dsimp only [speWord, msgTypeByte]
        arm64_sep_close
      clear hm
      have hm_keep := Satisfies.of_sep_right hm_drop
      clear hm_drop
      have hm_res := recordResultAt_decryptionFailed_intro A (sp + 0x4b0#64)
        (sf_1.readReg64 (Reg.gpr 0#5)) hoom' hm_keep
      clear hm_keep
      exact Eq.mp (congrArg (m ⊨ ·) (by unfold segRegionNonePostPlaced; ac_rfl)) hm_res
  obtain ⟨s', hsteps, hout⟩ :=
    hwp (segRegionNoneFramePlaced A ctl kit ikit st0 ist0 x s0 sp prevCap prevPtr ∗ R) hmem_split hL
  rcases hout with ⟨hpc', hrun', P_f, hmf, hsp', hsp_align', hx29', htr', hx26', hx27', hx28', hvregs', hent⟩ |
      ⟨hpan, P_f, hmf, hP⟩ | ⟨_, _hoom⟩
  · refine ⟨s', hsteps, Or.inl ?_⟩
    have hpc_exit : s'.pc = Record.recExitPlaced := hpc'
    have hmeta' : wsMetaPlaced x s0 s' :=
      ⟨hrun', hsp', hsp0_align, hsp_align', hx29', hx27',
        hcrl.of_keepsFrozen hsteps.keepsFrozen, hvregs'⟩
    refine ⟨hpc_exit, hmeta', hx26', hx28', rec, prevCap, prevPtr, hans, hscope, hcur,
      htr'.trans htrace, ?_⟩
    have hmf' := hent s'.mem (segRegionNoneFramePlaced A ctl kit ikit st0 ist0 x s0 sp prevCap prevPtr ∗ R) hmf
    clear hmf
    have hmf_rearr : s'.mem ⊨
        (memRegion sp 0x80 ∗ ((sp + 0x80#64) ↦₆₄ x.ret) ∗ ((sp + 0x88#64) ↦₆₄ x.locA) ∗
          ((sp + 0x90#64) ↦₆₄ x.msgA) ∗ memRegion (sp + 0x98#64) 4 ∗
          ((sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32)) ∗
        ((memRegion (sp + 0x4e0#64) 0xd0 ∗
          ((sp + 0x5b0#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x5b8#64) 4 ∗
          ((sp + 0x5bc#64) ↦₈ msgTypeByte .whisper) ∗ memRegion (sp + 0x5bd#64) 3 ∗
          ((sp + 0x5c0#64) ↦₆₄ (sp + 0x5bc#64)) ∗ ((sp + 0x5c8#64) ↦₆₄ x.msgA) ∗
          ((sp + 0x5d0#64) ↦₆₄ (sp + 0x5b0#64)) ∗ ((sp + 0x5d8#64) ↦₆₄ 0#64) ∗
          ((sp + 0x5e0#64) ↦₆₄ 8#64) ∗ ((sp + 0x5e8#64) ↦₆₄ 0#64) ∗
          ((sp + 0x5f0#64) ↦₆₄ (bv% (2 ^ 64 - 1))) ∗ memRegion (sp + 0x5f8#64) 0x808) ∗
         (wsMsgCells x sp ∗
          ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
          ((sp + 0x138#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x140#64) 336 ∗
          recordResultAt A (sp + 0x4b0#64) (.error (.invalidMessage .whisper .decryptionFailed)) ∗
          protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
          (((x.msgA + 0x70#64) ↦₈ x.msg.messageVersion) ∗
            signalMessageRestAt_shared_lb A x.msgG x.msgA x.msg) ∗
          tapeAt ctl x.cur x.rest ∗ FromRecordCallees.lsLogOff ∗
          (memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - allocHookStack) ∗
            stackAt sp allocHookStack) ∗
          A.pool ∗ wsRegionFrameVPlaced kit ikit x s0 prevCap prevPtr ∗
          decStoreExtraPlaced kit ikit st0 ist0 s0 ∗ R)) := by
      dsimp only [segRegionNonePostPlaced, segRegionNoneFramePlaced, wsMsgCells,
        FromRecordCallees.lsLogOff] at hmf' ⊢
      arm64_sep_close
    clear hmf'
    rw [← signalMessageAt_expose_shared_lb A x.msgG x.msgA x.msg,
        ← stackAt_root_split_alloc sp] at hmf_rearr
    have hmf_fold := Satisfies.mono
      (sepConj_mono (frame_low_entails_0xa0_shared_lb sp x.ret x.locA x.msgA _)
        (sepConj_mono_left (frame_high_entails_0x920 sp x.remA (msgTypeByte .whisper)
          (sp + 0x5bc#64) x.msgA (sp + 0x5b0#64) 0#64 8#64 0#64 (bv% (2 ^ 64 - 1)))))
      hmf_rearr
    clear hmf_rearr
    dsimp only [sp] at hmf_fold
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmf_fold
  · refine ⟨s', hsteps, Or.inr (Or.inr (Or.inl ⟨hpan, ?_⟩))⟩
    have hmf' : s'.mem ⊨
        (P_f ∗ segRegionNoneFramePlaced A ctl kit ikit st0 ist0 x s0 sp prevCap prevPtr) ∗ R := by
      rwa [← sepConj_assoc] at hmf
    exact allowPanic_panicked ⟨hP.1, Or.inl hP.2⟩ hmf'
  · dsimp only at _hoom
    exact (not_satisfies_false_sepConj _hoom).elim

end Placed

end CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegRegionNone
