/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Getters.Defs
public import LibsignalBinary.Proofs.CodeLayout
public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Specifications.LibsignalPublicApi
import ProofLib.SepLogic.WPp

/-!
# Instruction Decode and Stepping Lemmas for `segIdentity_ok`

Decode and basic-block stepping lemmas for `+0x2c8..+0x344` (`Otr → Key`) of
`session_message_encrypt_with_stores` (`0x3caf4`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalPublicApi

set_option maxRecDepth 200000 in
theorem libsignalSessionCode_fnOff_sym_3caf4 :
    libsignalSessionCode.fnOff encryptWithStoresName = num% (ls_off% "session_message_encrypt") := by
  exact (ls_lemma% fnOff "session_message_encrypt")

gen_decodes libsignalSessionCode_tree segIdentityBin [(ls_off% "session_message_encrypt" + 712) → (ls_off% "session_message_encrypt" + 832)]

def ikChunks6 (o : BitVec 64) (c0 : BitVec 32) (c4 : BitVec 16)
    (c6 c14 c22 : BitVec 64) (c30 : BitVec 16) : SepProp :=
  (o ↦₃₂ c0) ∗ ((o + 0x04#64) ↦₁₆ c4) ∗ ((o + 0x06#64) ↦₆₄ c6) ∗
  ((o + 0x0e#64) ↦₆₄ c14) ∗ ((o + 0x16#64) ↦₆₄ c22) ∗ ((o + 0x1e#64) ↦₁₆ c30)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem remoteIk_addr_eq (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::state::session::SessionState>::remote_identity_key") - (ls_off% "session_message_encrypt")) =
      (tripleRatchetProgAt b C ctl abs).fnAddr remoteIdentityKeyName := by
  simp only [tripleRatchetProgAt, Program.fnAddr_rebase, libsignalSessionCode_fnOff_sym_3caf4]
  have hfn : libsignalSessionCode.fnOff remoteIdentityKeyName = num% (ls_off% "<libsignal_protocol::state::session::SessionState>::remote_identity_key") := by
    simp only [remoteIdentityKeyName, arm64_norm]
  rw [hfn]
  bv_omega

theorem segIdentity_step_pre {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {sp : BitVec 64} {s : State}
    (hs_pc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 712#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::state::session::SessionState>::remote_identity_key") - (ls_off% "session_message_encrypt")))
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
        sm.readReg64 Reg.lr = (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 716#64 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        (Pm ⊢ emp)) := by
  dsimp only [tripleRatchetProgAt] at hs_pc ⊢
  code_fetches_range CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity.segIdentityBin b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    libsignalSessionCode_fnOff_sym_3caf4 (num% (ls_off% "session_message_encrypt")) 712 4
  examples_generalize_entry
  examples_hide_fetches
  wp_steps
  wp_done

set_option maxHeartbeats 1200000 in
theorem segIdentity_step_ok {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {sp : BitVec 64}
    {c0 d0 u868 : BitVec 32} {c4 c30 d4 d30 u86c ub08 : BitVec 16}
    {c6 c14 c22 d6 d14 d22 ub00 : BitVec 64} {s : State}
    (hs_pc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 716#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hal : s.spAligned = true)
    (hx23 : s.readReg64 .x23 = sp + 0x58#64)
    (hx24 : s.readReg64 .x24 = sp + 0x58#64)
    (hx25 : s.readReg64 .x25 = sp + 0x580#64)
    (hx29 : s.readReg64 .x29 = sp + 0xb80#64) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0x344#64)
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
    CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity.segIdentityBin b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    libsignalSessionCode_fnOff_sym_3caf4 (num% (ls_off% "session_message_encrypt")) 716 120
  examples_generalize_entry
  examples_hide_fetches
  wp_steps
  wp_done

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity
