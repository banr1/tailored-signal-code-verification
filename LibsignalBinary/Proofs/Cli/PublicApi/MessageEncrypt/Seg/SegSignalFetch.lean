/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.Specifications.LibsignalPublicApi
public import LibsignalBinary.Proofs.Cli.Specifications.LibsignalTripleRatchet
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tails
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# Instruction Decode Tables and Step Lemmas for `segSignal` (`+0x344..+0x418`)

Generates instruction decode tables and proves basic-block `SepWP` stepping lemmas for the
non-pre-key `SignalMessage` encryption path in `signal_session_ratchet::encrypt`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames.LibsignalSession

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails

set_option maxRecDepth 200000

/-- `session_message_encrypt_with_stores` (`CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName`) starts at image offset `(ls_off% "signal_session_ratchet::encrypt")`. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.libsignalSessionCode_fnOff_0x3cbd8 :
    libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = (ls_off% "libsignal_cli_ratchet::encrypt") := by
  fnoff_eq

gen_decodes libsignalSessionCode_tree segSignalBinCli [(ls_off% "libsignal_cli_ratchet::encrypt" + 836) → (ls_off% "libsignal_cli_ratchet::encrypt" + 1048)]

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Address of `SessionState::unacknowledged_pre_key_message_items` relative to `encryptWithStoresName`. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.unack_addr_eq_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) :
    (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + bv% ((2^64 + ls_off% "<libsignal_protocol::state::session::SessionState>::unacknowledged_pre_key_message_items" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64) =
      b + bv% (ls_off% "<libsignal_protocol::state::session::SessionState>::unacknowledged_pre_key_message_items") := by
  simp only [trTrapProgAt, Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt")]
  bv_omega

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.unack_addr_eq (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + bv% ((2^64 + ls_off% "<libsignal_protocol::state::session::SessionState>::unacknowledged_pre_key_message_items" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64) =
      b + 0x1245c#64 := by
  simp only [tripleRatchetProgAt, Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt")]
  bv_omega

/-- Address of `OutgoingTripleRatchet::encrypt` relative to `encryptWithStoresName`. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.otrEnc_addr_eq_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) :
    (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + bv% ((2^64 + ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64) =
      (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName := by
  simp only [trTrapProgAt, Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt")]
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName = (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>") := by
    fnoff_eq
  rw [hfn]
  bv_omega

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.otrEnc_addr_eq (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + bv% ((2^64 + ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64) =
      (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName := by
  simp only [tripleRatchetProgAt, Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt")]
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName = (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>") := by
    fnoff_eq
  rw [hfn]
  bv_omega

/-- `+0x344`: `bl` the pre-key items getter. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_step_bl_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} {sp u : BitVec 64} {s : State}
    (hs_pc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x344#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (_hal : s.spAligned = true) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + bv% ((2^64 + ls_off% "<libsignal_protocol::state::session::SessionState>::unacknowledged_pre_key_message_items" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64))
      s ((sp + 0x280#64) ↦₆₄ u)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.trace = s.trace ∧
        sm.readReg64 .x0 = s.readReg64 .x0 ∧ sm.readReg64 .x8 = s.readReg64 .x8 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x23 = s.readReg64 .x23 ∧ sm.readReg64 .x25 = s.readReg64 .x25 ∧
        sm.readReg64 .x26 = s.readReg64 .x26 ∧ sm.readReg64 .x27 = s.readReg64 .x27 ∧
        sm.readReg64 .x28 = s.readReg64 .x28 ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        sm.readReg64 Reg.lr = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x348#64 ∧
        (Pm ⊢ (sp + 0x280#64) ↦₆₄ u)) := by
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt] at hs_pc ⊢
  code_fetches_range CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignalBinCli b
    (Rust.withPanics (trTrapExterns C abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 836 4
  examples_generalize_entry
  examples_hide_fetches
  wp_steps
  wp_done

set_option maxHeartbeats 1600000 in

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_step_bl {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {sp u : BitVec 64} {s : State}
    (hs_pc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x344#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (_hal : s.spAligned = true) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + bv% ((2^64 + ls_off% "<libsignal_protocol::state::session::SessionState>::unacknowledged_pre_key_message_items" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64))
      s ((sp + 0x280#64) ↦₆₄ u)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.trace = s.trace ∧
        sm.readReg64 .x0 = s.readReg64 .x0 ∧ sm.readReg64 .x8 = s.readReg64 .x8 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x23 = s.readReg64 .x23 ∧ sm.readReg64 .x25 = s.readReg64 .x25 ∧
        sm.readReg64 .x26 = s.readReg64 .x26 ∧ sm.readReg64 .x27 = s.readReg64 .x27 ∧
        sm.readReg64 .x28 = s.readReg64 .x28 ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        sm.readReg64 Reg.lr = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x348#64 ∧
        (Pm ⊢ (sp + 0x280#64) ↦₆₄ u)) := by
  dsimp only [tripleRatchetProgAt] at hs_pc ⊢
  code_fetches_range CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignalBinCli b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 836 4
  examples_generalize_entry
  examples_hide_fetches
  wp_steps
  wp_done

set_option maxHeartbeats 1600000 in
/-- `+0x348..+0x3a0`: the getter returned `None` (tag 2); spill the key / OTR pointers, copy the
junk `sp+0x59c..0x5c0` to `sp+0x870..0x894`, `bl OTR::encrypt(sp+0x580, sp+0x288, ptA, len, 0,
remA)`. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_step_enc_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} {sp : BitVec 64} {s : State}
    {u38 u40 u48 ptA len remA a1 a2 c0 c1 c2 c3 e0 e1 e2 e3 : BitVec 64}
    {a0 a3 c4 e4 : BitVec 32}
    (hs_pc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x348#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hal : s.spAligned = true)
    (hx23 : s.readReg64 .x23 = sp + 0x58#64) (hx25 : s.readReg64 .x25 = sp + 0x580#64)
    (hx27 : s.readReg64 .x27 = sp + 0xc0#64) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + bv% ((2^64 + ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64))
      s (((sp + 0x38#64) ↦₆₄ u38) ∗ ((sp + 0x40#64) ↦₆₄ u40) ∗ ((sp + 0x48#64) ↦₆₄ u48) ∗
        ((sp + 0xb0#64) ↦₆₄ ptA) ∗ ((sp + 0xb8#64) ↦₆₄ len) ∗ ((sp + 0xc0#64) ↦₆₄ remA) ∗
        ((sp + 0x580#64) ↦₃₂ 2#32) ∗ ((sp + 0x584#64) ↦₃₂ a0) ∗ ((sp + 0x588#64) ↦₆₄ a1) ∗
        ((sp + 0x590#64) ↦₆₄ a2) ∗ ((sp + 0x598#64) ↦₃₂ a3) ∗ ((sp + 0x59c#64) ↦₆₄ c0) ∗
        ((sp + 0x5a4#64) ↦₆₄ c1) ∗ ((sp + 0x5ac#64) ↦₆₄ c2) ∗ ((sp + 0x5b4#64) ↦₆₄ c3) ∗
        ((sp + 0x5bc#64) ↦₃₂ c4) ∗
        ((sp + 0x870#64) ↦₆₄ e0) ∗ ((sp + 0x878#64) ↦₆₄ e1) ∗ ((sp + 0x880#64) ↦₆₄ e2) ∗
        ((sp + 0x888#64) ↦₆₄ e3) ∗ ((sp + 0x890#64) ↦₃₂ e4))
      (fun sm Pm =>
        sm.sp = sp ∧ sm.trace = s.trace ∧
        sm.readReg64 .x0 = sp + 0x580#64 ∧ sm.readReg64 .x1 = sp + 0x288#64 ∧
        sm.readReg64 .x2 = ptA ∧ sm.readReg64 .x3 = len ∧ sm.readReg64 .x4 = 0#64 ∧
        sm.readReg64 .x5 = remA ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x25 = s.readReg64 .x25 ∧ sm.readReg64 .x26 = s.readReg64 .x26 ∧
        sm.readReg64 .x28 = s.readReg64 .x28 ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        sm.readReg64 Reg.lr = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x3a4#64 ∧
        (Pm ⊢ ((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗ ((sp + 0x40#64) ↦₆₄ (sp + 0x350#64)) ∗
          ((sp + 0x48#64) ↦₆₄ (sp + 0xc0#64)) ∗
          ((sp + 0xb0#64) ↦₆₄ ptA) ∗ ((sp + 0xb8#64) ↦₆₄ len) ∗ ((sp + 0xc0#64) ↦₆₄ remA) ∗
          ((sp + 0x580#64) ↦₃₂ 2#32) ∗ ((sp + 0x584#64) ↦₃₂ a0) ∗ ((sp + 0x588#64) ↦₆₄ a1) ∗
          ((sp + 0x590#64) ↦₆₄ a2) ∗ ((sp + 0x598#64) ↦₃₂ a3) ∗ ((sp + 0x59c#64) ↦₆₄ c0) ∗
          ((sp + 0x5a4#64) ↦₆₄ c1) ∗ ((sp + 0x5ac#64) ↦₆₄ c2) ∗ ((sp + 0x5b4#64) ↦₆₄ c3) ∗
          ((sp + 0x5bc#64) ↦₃₂ c4) ∗
          ((sp + 0x870#64) ↦₆₄ c0) ∗ ((sp + 0x878#64) ↦₆₄ c1) ∗ ((sp + 0x880#64) ↦₆₄ c2) ∗
          ((sp + 0x888#64) ↦₆₄ c3) ∗ ((sp + 0x890#64) ↦₃₂ c4))) := by
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt] at hs_pc ⊢
  code_fetches_range CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignalBinCli b
    (Rust.withPanics (trTrapExterns C abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 840 92
  examples_generalize_entry
  examples_hide_fetches
  wp_steps
  wp_done

set_option maxHeartbeats 1600000 in

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_step_enc {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {sp : BitVec 64} {s : State}
    {u38 u40 u48 ptA len remA a1 a2 c0 c1 c2 c3 e0 e1 e2 e3 : BitVec 64}
    {a0 a3 c4 e4 : BitVec 32}
    (hs_pc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x348#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hal : s.spAligned = true)
    (hx23 : s.readReg64 .x23 = sp + 0x58#64) (hx25 : s.readReg64 .x25 = sp + 0x580#64)
    (hx27 : s.readReg64 .x27 = sp + 0xc0#64) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + bv% ((2^64 + ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64))
      s (((sp + 0x38#64) ↦₆₄ u38) ∗ ((sp + 0x40#64) ↦₆₄ u40) ∗ ((sp + 0x48#64) ↦₆₄ u48) ∗
        ((sp + 0xb0#64) ↦₆₄ ptA) ∗ ((sp + 0xb8#64) ↦₆₄ len) ∗ ((sp + 0xc0#64) ↦₆₄ remA) ∗
        ((sp + 0x580#64) ↦₃₂ 2#32) ∗ ((sp + 0x584#64) ↦₃₂ a0) ∗ ((sp + 0x588#64) ↦₆₄ a1) ∗
        ((sp + 0x590#64) ↦₆₄ a2) ∗ ((sp + 0x598#64) ↦₃₂ a3) ∗ ((sp + 0x59c#64) ↦₆₄ c0) ∗
        ((sp + 0x5a4#64) ↦₆₄ c1) ∗ ((sp + 0x5ac#64) ↦₆₄ c2) ∗ ((sp + 0x5b4#64) ↦₆₄ c3) ∗
        ((sp + 0x5bc#64) ↦₃₂ c4) ∗
        ((sp + 0x870#64) ↦₆₄ e0) ∗ ((sp + 0x878#64) ↦₆₄ e1) ∗ ((sp + 0x880#64) ↦₆₄ e2) ∗
        ((sp + 0x888#64) ↦₆₄ e3) ∗ ((sp + 0x890#64) ↦₃₂ e4))
      (fun sm Pm =>
        sm.sp = sp ∧ sm.trace = s.trace ∧
        sm.readReg64 .x0 = sp + 0x580#64 ∧ sm.readReg64 .x1 = sp + 0x288#64 ∧
        sm.readReg64 .x2 = ptA ∧ sm.readReg64 .x3 = len ∧ sm.readReg64 .x4 = 0#64 ∧
        sm.readReg64 .x5 = remA ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x25 = s.readReg64 .x25 ∧ sm.readReg64 .x26 = s.readReg64 .x26 ∧
        sm.readReg64 .x28 = s.readReg64 .x28 ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        sm.readReg64 Reg.lr = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x3a4#64 ∧
        (Pm ⊢ ((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗ ((sp + 0x40#64) ↦₆₄ (sp + 0x350#64)) ∗
          ((sp + 0x48#64) ↦₆₄ (sp + 0xc0#64)) ∗
          ((sp + 0xb0#64) ↦₆₄ ptA) ∗ ((sp + 0xb8#64) ↦₆₄ len) ∗ ((sp + 0xc0#64) ↦₆₄ remA) ∗
          ((sp + 0x580#64) ↦₃₂ 2#32) ∗ ((sp + 0x584#64) ↦₃₂ a0) ∗ ((sp + 0x588#64) ↦₆₄ a1) ∗
          ((sp + 0x590#64) ↦₆₄ a2) ∗ ((sp + 0x598#64) ↦₃₂ a3) ∗ ((sp + 0x59c#64) ↦₆₄ c0) ∗
          ((sp + 0x5a4#64) ↦₆₄ c1) ∗ ((sp + 0x5ac#64) ↦₆₄ c2) ∗ ((sp + 0x5b4#64) ↦₆₄ c3) ∗
          ((sp + 0x5bc#64) ↦₃₂ c4) ∗
          ((sp + 0x870#64) ↦₆₄ c0) ∗ ((sp + 0x878#64) ↦₆₄ c1) ∗ ((sp + 0x880#64) ↦₆₄ c2) ∗
          ((sp + 0x888#64) ↦₆₄ c3) ∗ ((sp + 0x890#64) ↦₃₂ c4))) := by
  dsimp only [tripleRatchetProgAt] at hs_pc ⊢
  code_fetches_range CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignalBinCli b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 840 92
  examples_generalize_entry
  examples_hide_fetches
  wp_steps
  wp_done

set_option maxHeartbeats 1600000 in
/-- `+0x3a4..+0x3c8`: `OTR::encrypt` returned `Err` (word 0 = `errTag`): `w0..w2` to
`x27, x21, x23`, `w3..w5` to `sp+0xb00..0xb18`, `b.eq` to the T5 signal tail `+0xc14`. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_step_err_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} {sp : BitVec 64} {s : State}
    {w0 w1 w2 w3 w4 w5 v0 v1 v2 : BitVec 64}
    (hs_pc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x3a4#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hal : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = sp + 0x580#64) (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hx29 : s.readReg64 .x29 = sp + 0xb80#64) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xc14#64)
      s (((sp + 0x580#64) ↦₆₄ errTag) ∗ words64At (sp + 0x588#64) [w0, w1, w2, w3, w4, w5] ∗
        words64At (sp + 0xb00#64) [v0, v1, v2])
      (fun sm Pm =>
        sm.sp = sp ∧ sm.trace = s.trace ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x21 = w1 ∧ sm.readReg64 .x23 = w2 ∧
        sm.readReg64 .x25 = s.readReg64 .x25 ∧ sm.readReg64 .x26 = s.readReg64 .x26 ∧
        sm.readReg64 .x27 = w0 ∧
        sm.readReg64 .x28 = s.readReg64 .x28 ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        (Pm ⊢ ((sp + 0x580#64) ↦₆₄ errTag) ∗ words64At (sp + 0x588#64) [w0, w1, w2, w3, w4, w5] ∗
          words64At (sp + 0xb00#64) [w3, w4, w5])) := by
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt, errTag] at hs_pc ⊢
  simp only [words64At, sepConj_emp, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]
  code_fetches_range CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignalBinCli b
    (Rust.withPanics (trTrapExterns C abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 932 40
  examples_generalize_entry
  examples_hide_fetches
  wp_steps
  wp_done

set_option maxHeartbeats 3200000 in

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_step_err {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {sp : BitVec 64} {s : State}
    {w0 w1 w2 w3 w4 w5 v0 v1 v2 : BitVec 64}
    (hs_pc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x3a4#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hal : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = sp + 0x580#64) (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hx29 : s.readReg64 .x29 = sp + 0xb80#64) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xc14#64)
      s (((sp + 0x580#64) ↦₆₄ errTag) ∗ words64At (sp + 0x588#64) [w0, w1, w2, w3, w4, w5] ∗
        words64At (sp + 0xb00#64) [v0, v1, v2])
      (fun sm Pm =>
        sm.sp = sp ∧ sm.trace = s.trace ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x21 = w1 ∧ sm.readReg64 .x23 = w2 ∧
        sm.readReg64 .x25 = s.readReg64 .x25 ∧ sm.readReg64 .x26 = s.readReg64 .x26 ∧
        sm.readReg64 .x27 = w0 ∧
        sm.readReg64 .x28 = s.readReg64 .x28 ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        (Pm ⊢ ((sp + 0x580#64) ↦₆₄ errTag) ∗ words64At (sp + 0x588#64) [w0, w1, w2, w3, w4, w5] ∗
          words64At (sp + 0xb00#64) [w3, w4, w5])) := by
  dsimp only [tripleRatchetProgAt, errTag] at hs_pc ⊢
  simp only [words64At, sepConj_emp, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]
  code_fetches_range CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignalBinCli b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 932 40
  examples_generalize_entry
  examples_hide_fetches
  wp_steps
  wp_done

set_option maxHeartbeats 3200000 in
/-- `+0x3a4..+0x418`: `OTR::encrypt` returned `Ok` (word 0 = the message's pq `Vec` capacity,
`≠ -1`): copy the 15 words `sp+0x580 → sp+0x378`, the tag `ctSignalTag` to `sp+0x370`, `b` to the
Cm seam `+0xa70`. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_step_ok_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} {sp : BitVec 64} {s : State}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 v0 v1 v2 : BitVec 64}
    {d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 : BitVec 64}
    (hs_pc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x3a4#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hal : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = sp + 0x580#64) (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hx29 : s.readReg64 .x29 = sp + 0xb80#64) (hw0 : w0 + 1#64 ≠ 0#64) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xa70#64)
      s (words64At (sp + 0x580#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13,
          w14] ∗
        words64At (sp + 0xb00#64) [v0, v1, v2] ∗
        words64At (sp + 0x370#64) [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13,
          d14, d15])
      (fun sm Pm =>
        sm.sp = sp ∧ sm.trace = s.trace ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x25 = s.readReg64 .x25 ∧ sm.readReg64 .x26 = s.readReg64 .x26 ∧
        sm.readReg64 .x28 = s.readReg64 .x28 ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        (Pm ⊢ words64At (sp + 0x580#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12,
            w13, w14] ∗
          words64At (sp + 0xb00#64) [w4, w5, w6] ∗
          words64At (sp + 0x370#64) [0x8000000000000000#64, w0, w1, w2, w3, w4, w5, w6, w7, w8,
            w9, w10, w11, w12, w13, w14])) := by
  have hw0_beq : (w0 + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hw0
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt] at hs_pc ⊢
  simp only [words64At, sepConj_emp, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]
  code_fetches_range CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignalBinCli b
    (Rust.withPanics (trTrapExterns C abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 932 120
  examples_generalize_entry
  examples_hide_fetches
  wp_steps
  wp_done

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_step_ok {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {sp : BitVec 64} {s : State}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 v0 v1 v2 : BitVec 64}
    {d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 : BitVec 64}
    (hs_pc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x3a4#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hal : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = sp + 0x580#64) (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hx29 : s.readReg64 .x29 = sp + 0xb80#64) (hw0 : w0 + 1#64 ≠ 0#64) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xa70#64)
      s (words64At (sp + 0x580#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13,
          w14] ∗
        words64At (sp + 0xb00#64) [v0, v1, v2] ∗
        words64At (sp + 0x370#64) [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13,
          d14, d15])
      (fun sm Pm =>
        sm.sp = sp ∧ sm.trace = s.trace ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x25 = s.readReg64 .x25 ∧ sm.readReg64 .x26 = s.readReg64 .x26 ∧
        sm.readReg64 .x28 = s.readReg64 .x28 ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        (Pm ⊢ words64At (sp + 0x580#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12,
            w13, w14] ∗
          words64At (sp + 0xb00#64) [w4, w5, w6] ∗
          words64At (sp + 0x370#64) [0x8000000000000000#64, w0, w1, w2, w3, w4, w5, w6, w7, w8,
            w9, w10, w11, w12, w13, w14])) := by
  have hw0_beq : (w0 + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hw0
  dsimp only [tripleRatchetProgAt] at hs_pc ⊢
  simp only [words64At, sepConj_emp, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]
  code_fetches_range CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignalBinCli b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 932 120
  examples_generalize_entry
  examples_hide_fetches
  wp_steps
  wp_done

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal
