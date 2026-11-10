/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegIdentityFetch
public import LibsignalBinary.Proofs.Cli.Specifications.LibsignalPublicApi
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import ProofLib.SepLogic.WPp

/-!
# CLI `SegIdentity` Instruction Decodes

Pre-decoded instruction tables for the `SegIdentity` segment (`+0x2c8..+0x344`) of
`session_message_encrypt_with_stores`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames.LibsignalSession

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.Getters

open CryptoVerification.LibsignalPublicApi

set_option maxRecDepth 200000 in
/-- Entry offset of `session_message_encrypt_with_stores` in `libsignalSessionCode`. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity.libsignalSessionCode_fnOff_sym_3caf4 :
    libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = num% (ls_off% "libsignal_cli_ratchet::encrypt") := by
  exact (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt")

gen_decodes libsignalSessionCode_tree segIdentityBinCli [(ls_off% "libsignal_cli_ratchet::encrypt" + 712) → (ls_off% "libsignal_cli_ratchet::encrypt" + 832)]

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity.remoteIk_addr_eq_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) :
    (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::state::session::SessionState>::remote_identity_key") - (ls_off% "libsignal_cli_ratchet::encrypt")) =
      (trTrapProgAt b C abs).fnAddr remoteIdentityKeyName := by
  simp only [trTrapProgAt, Program.fnAddr_rebase, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity.libsignalSessionCode_fnOff_sym_3caf4]
  have hfn : libsignalSessionCode.fnOff remoteIdentityKeyName = num% (ls_off% "<libsignal_protocol::state::session::SessionState>::remote_identity_key") := by
    fnoff_eq
  rw [hfn]
  bv_omega

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity.remoteIk_addr_eq (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::state::session::SessionState>::remote_identity_key") - (ls_off% "libsignal_cli_ratchet::encrypt")) =
      (tripleRatchetProgAt b C ctl abs).fnAddr remoteIdentityKeyName := by
  simp only [tripleRatchetProgAt, Program.fnAddr_rebase, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity.libsignalSessionCode_fnOff_sym_3caf4]
  have hfn : libsignalSessionCode.fnOff remoteIdentityKeyName = num% (ls_off% "<libsignal_protocol::state::session::SessionState>::remote_identity_key") := by
    fnoff_eq
  rw [hfn]
  bv_omega

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity.segIdentity_step_pre_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} {sp : BitVec 64} {s : State}
    (hs_pc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 712#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::state::session::SessionState>::remote_identity_key") - (ls_off% "libsignal_cli_ratchet::encrypt")))
      s emp
      (fun sm Pm =>
        sm.sp = sp ∧ sm.trace = s.trace ∧
        sm.readReg64 .x0 = s.readReg64 .x0 ∧
        sm.readReg64 .x8 = s.readReg64 .x8 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x22 = s.readReg64 .x22 ∧
        sm.readReg64 .x23 = s.readReg64 .x23 ∧
        sm.readReg64 .x24 = s.readReg64 .x24 ∧
        sm.readReg64 .x25 = s.readReg64 .x25 ∧
        sm.readReg64 .x26 = s.readReg64 .x26 ∧
        sm.readReg64 .x27 = s.readReg64 .x27 ∧
        sm.readReg64 .x28 = s.readReg64 .x28 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.readReg64 Reg.lr = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 716#64 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        (Pm ⊢ emp)) := by
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt] at hs_pc ⊢
  code_fetches_range CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity.segIdentityBinCli b
    (Rust.withPanics (trTrapExterns C abs))
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity.libsignalSessionCode_fnOff_sym_3caf4 (num% (ls_off% "libsignal_cli_ratchet::encrypt")) 712 4
  examples_generalize_entry
  examples_hide_fetches
  wp_steps
  wp_done


theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity.segIdentity_step_pre {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {sp : BitVec 64} {s : State}
    (hs_pc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 712#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::state::session::SessionState>::remote_identity_key") - (ls_off% "libsignal_cli_ratchet::encrypt")))
      s emp
      (fun sm Pm =>
        sm.sp = sp ∧ sm.trace = s.trace ∧
        sm.readReg64 .x0 = s.readReg64 .x0 ∧
        sm.readReg64 .x8 = s.readReg64 .x8 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x22 = s.readReg64 .x22 ∧
        sm.readReg64 .x23 = s.readReg64 .x23 ∧
        sm.readReg64 .x24 = s.readReg64 .x24 ∧
        sm.readReg64 .x25 = s.readReg64 .x25 ∧
        sm.readReg64 .x26 = s.readReg64 .x26 ∧
        sm.readReg64 .x27 = s.readReg64 .x27 ∧
        sm.readReg64 .x28 = s.readReg64 .x28 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.readReg64 Reg.lr = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 716#64 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        (Pm ⊢ emp)) := by
  dsimp only [tripleRatchetProgAt] at hs_pc ⊢
  code_fetches_range CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity.segIdentityBinCli b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity.libsignalSessionCode_fnOff_sym_3caf4 (num% (ls_off% "libsignal_cli_ratchet::encrypt")) 712 4
  examples_generalize_entry
  examples_hide_fetches
  wp_steps
  wp_done

set_option maxHeartbeats 1200000 in
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity.segIdentity_step_ok_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} {sp : BitVec 64}
    {c0 d0 u868 : BitVec 32} {c4 c30 d4 d30 u86c ub08 : BitVec 16}
    {c6 c14 c22 d6 d14 d22 ub00 : BitVec 64} {s : State}
    (hs_pc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 716#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hal : s.spAligned = true)
    (hx23 : s.readReg64 .x23 = sp + 0x58#64)
    (hx24 : s.readReg64 .x24 = sp + 0x58#64)
    (hx25 : s.readReg64 .x25 = sp + 0x580#64)
    (hx29 : s.readReg64 .x29 = sp + 0xb80#64) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x344#64)
      s (((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        ikChunks6 (sp + 0x350#64) d0 d4 d6 d14 d22 d30 ∗
        ((sp + 0x580#64) ↦₈ 0#8) ∗ ((sp + 0x581#64) ↦₈ 1#8) ∗
        ikChunks6 (sp + 0x582#64) c0 c4 c6 c14 c22 c30 ∗
        ((sp + 0x868#64) ↦₃₂ u868) ∗ ((sp + 0x86c#64) ↦₁₆ u86c) ∗
        ((sp + 0xb00#64) ↦₆₄ ub00) ∗ ((sp + 0xb08#64) ↦₁₆ ub08))
      (fun sm Pm =>
        sm.sp = sp ∧ sm.trace = s.trace ∧
        sm.readReg64 .x0 = sp + 0x128#64 ∧
        sm.readReg64 .x8 = sp + 0x580#64 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x22 = s.readReg64 .x22 ∧
        sm.readReg64 .x23 = sp + 0x58#64 ∧
        sm.readReg64 .x25 = sp + 0x580#64 ∧
        sm.readReg64 .x26 = s.readReg64 .x26 ∧
        sm.readReg64 .x27 = s.readReg64 .x27 ∧
        sm.readReg64 .x28 = s.readReg64 .x28 ∧
        sm.readReg64 .x29 = sp + 0xb80#64 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        (Pm ⊢ ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
          ikChunks6 (sp + 0x350#64) c0 c4 c6 c14 c22 c30 ∗
          ((sp + 0x580#64) ↦₈ 0#8) ∗ ((sp + 0x581#64) ↦₈ 1#8) ∗
          ikChunks6 (sp + 0x582#64) c0 c4 c6 c14 c22 c30 ∗
          ((sp + 0x868#64) ↦₃₂ c0) ∗ ((sp + 0x86c#64) ↦₁₆ c4) ∗
          ((sp + 0xb00#64) ↦₆₄ c22) ∗ ((sp + 0xb08#64) ↦₁₆ c30))) := by
  dsimp only [trTrapProgAt, ikChunks6] at hs_pc ⊢
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  code_fetches_range CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity.segIdentityBinCli b
    (Rust.withPanics (trTrapExterns C abs))
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity.libsignalSessionCode_fnOff_sym_3caf4 (num% (ls_off% "libsignal_cli_ratchet::encrypt")) 716 120
  examples_generalize_entry
  examples_hide_fetches
  wp_steps
  wp_done

set_option maxHeartbeats 1200000 in
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity.segIdentity_step_ok {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {sp : BitVec 64}
    {c0 d0 u868 : BitVec 32} {c4 c30 d4 d30 u86c ub08 : BitVec 16}
    {c6 c14 c22 d6 d14 d22 ub00 : BitVec 64} {s : State}
    (hs_pc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 716#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hal : s.spAligned = true)
    (hx23 : s.readReg64 .x23 = sp + 0x58#64)
    (hx24 : s.readReg64 .x24 = sp + 0x58#64)
    (hx25 : s.readReg64 .x25 = sp + 0x580#64)
    (hx29 : s.readReg64 .x29 = sp + 0xb80#64) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x344#64)
      s (((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        ikChunks6 (sp + 0x350#64) d0 d4 d6 d14 d22 d30 ∗
        ((sp + 0x580#64) ↦₈ 0#8) ∗ ((sp + 0x581#64) ↦₈ 1#8) ∗
        ikChunks6 (sp + 0x582#64) c0 c4 c6 c14 c22 c30 ∗
        ((sp + 0x868#64) ↦₃₂ u868) ∗ ((sp + 0x86c#64) ↦₁₆ u86c) ∗
        ((sp + 0xb00#64) ↦₆₄ ub00) ∗ ((sp + 0xb08#64) ↦₁₆ ub08))
      (fun sm Pm =>
        sm.sp = sp ∧ sm.trace = s.trace ∧
        sm.readReg64 .x0 = sp + 0x128#64 ∧
        sm.readReg64 .x8 = sp + 0x580#64 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x22 = s.readReg64 .x22 ∧
        sm.readReg64 .x23 = sp + 0x58#64 ∧
        sm.readReg64 .x25 = sp + 0x580#64 ∧
        sm.readReg64 .x26 = s.readReg64 .x26 ∧
        sm.readReg64 .x27 = s.readReg64 .x27 ∧
        sm.readReg64 .x28 = s.readReg64 .x28 ∧
        sm.readReg64 .x29 = sp + 0xb80#64 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        (Pm ⊢ ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
          ikChunks6 (sp + 0x350#64) c0 c4 c6 c14 c22 c30 ∗
          ((sp + 0x580#64) ↦₈ 0#8) ∗ ((sp + 0x581#64) ↦₈ 1#8) ∗
          ikChunks6 (sp + 0x582#64) c0 c4 c6 c14 c22 c30 ∗
          ((sp + 0x868#64) ↦₃₂ c0) ∗ ((sp + 0x86c#64) ↦₁₆ c4) ∗
          ((sp + 0xb00#64) ↦₆₄ c22) ∗ ((sp + 0xb08#64) ↦₁₆ c30))) := by
  dsimp only [tripleRatchetProgAt, ikChunks6] at hs_pc ⊢
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  code_fetches_range CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity.segIdentityBinCli b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity.libsignalSessionCode_fnOff_sym_3caf4 (num% (ls_off% "libsignal_cli_ratchet::encrypt")) 716 120
  examples_generalize_entry
  examples_hide_fetches
  wp_steps
  wp_done

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity
