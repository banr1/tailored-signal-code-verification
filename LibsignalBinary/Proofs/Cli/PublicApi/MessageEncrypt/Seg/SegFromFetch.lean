/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegFromFetch
public import LibsignalBinary.Proofs.Cli.Specifications.LibsignalPublicApi
public import LibsignalBinary.Proofs.TripleRatchet.TrapRng
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- shake: keep

/-!
# CLI `SegFrom` Instruction Decodes

Pre-decoded instruction tables and entry-offset lemma for the `SegFrom` segment (`+0x20c..+0x2c8`)
of `session_message_encrypt_with_stores`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames.LibsignalSession

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalPublicApi

set_option maxRecDepth 200000 in
/-- Entry offset of `session_message_encrypt_with_stores` in `libsignalSessionCode`. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.libsignalSessionCode_fnOff_sym_3caf4 :
    libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = num% (ls_off% "libsignal_cli_ratchet::encrypt") := by
  exact (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt")

gen_decodes libsignalSessionCode_tree segFromBinCli [(ls_off% "libsignal_cli_ratchet::encrypt" + 524) → (ls_off% "libsignal_cli_ratchet::encrypt" + 708)]

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.otrFrom_addr_eq_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) :
    (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state") - (ls_off% "libsignal_cli_ratchet::encrypt")) =
      (trTrapProgAt b C abs).fnAddr otrFromName := by
  simp only [trTrapProgAt, Program.fnAddr_rebase, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.libsignalSessionCode_fnOff_sym_3caf4]
  have hfn : libsignalSessionCode.fnOff otrFromName = num% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state") := by
    fnoff_eq
  rw [hfn]
  bv_omega

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.otrFrom_addr_eq (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state") - (ls_off% "libsignal_cli_ratchet::encrypt")) =
      (tripleRatchetProgAt b C ctl abs).fnAddr otrFromName := by
  simp only [tripleRatchetProgAt, Program.fnAddr_rebase, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.libsignalSessionCode_fnOff_sym_3caf4]
  have hfn : libsignalSessionCode.fnOff otrFromName = num% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state") := by
    fnoff_eq
  rw [hfn]
  bv_omega

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.segFrom_step_pre_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} {sp u280 : BitVec 64} {s : State}
    (hs_pc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 524#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hal : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = sp + 0x58#64)
    (hx21 : s.readReg64 .x21 = sp + 0x128#64)
    (hx25 : s.readReg64 .x25 = sp + 0x580#64)
    (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hx28 : s.readReg64 .x28 = sp + 0x4a0#64) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state") - (ls_off% "libsignal_cli_ratchet::encrypt")))
      s ((sp + 0x280#64) ↦₆₄ u280)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.trace = s.trace ∧
        sm.readReg64 .x0 = sp + 0x128#64 ∧
        sm.readReg64 .x8 = sp + 0x580#64 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = sp + 0x58#64 ∧
        sm.readReg64 .x21 = sp + 0x580#64 ∧
        sm.readReg64 .x24 = sp + 0x58#64 ∧
        sm.readReg64 .x25 = sp + 0x580#64 ∧
        sm.readReg64 .x26 = sp + 0x9d0#64 ∧
        sm.readReg64 .x27 = sp + 0xc0#64 ∧
        sm.readReg64 .x28 = sp + 0x4a0#64 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.readReg64 Reg.lr = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x228#64 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        (Pm ⊢ (sp + 0x280#64) ↦₆₄ (sp + 0x128#64))) := by
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt] at hs_pc ⊢
  code_fetches_range CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.segFromBinCli b
    (Rust.withPanics (trTrapExterns C abs))
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.libsignalSessionCode_fnOff_sym_3caf4 (num% (ls_off% "libsignal_cli_ratchet::encrypt")) 524 28
  examples_generalize_entry
  examples_hide_fetches
  wp_steps
  wp_done

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.segFrom_step_pre {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {sp u280 : BitVec 64} {s : State}
    (hs_pc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 524#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hal : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = sp + 0x58#64)
    (hx21 : s.readReg64 .x21 = sp + 0x128#64)
    (hx25 : s.readReg64 .x25 = sp + 0x580#64)
    (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hx28 : s.readReg64 .x28 = sp + 0x4a0#64) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state") - (ls_off% "libsignal_cli_ratchet::encrypt")))
      s ((sp + 0x280#64) ↦₆₄ u280)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.trace = s.trace ∧
        sm.readReg64 .x0 = sp + 0x128#64 ∧
        sm.readReg64 .x8 = sp + 0x580#64 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = sp + 0x58#64 ∧
        sm.readReg64 .x21 = sp + 0x580#64 ∧
        sm.readReg64 .x24 = sp + 0x58#64 ∧
        sm.readReg64 .x25 = sp + 0x580#64 ∧
        sm.readReg64 .x26 = sp + 0x9d0#64 ∧
        sm.readReg64 .x27 = sp + 0xc0#64 ∧
        sm.readReg64 .x28 = sp + 0x4a0#64 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.readReg64 Reg.lr = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x228#64 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        (Pm ⊢ (sp + 0x280#64) ↦₆₄ (sp + 0x128#64))) := by
  dsimp only [tripleRatchetProgAt] at hs_pc ⊢
  code_fetches_range CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.segFromBinCli b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.libsignalSessionCode_fnOff_sym_3caf4 (num% (ls_off% "libsignal_cli_ratchet::encrypt")) 524 28
  examples_generalize_entry
  examples_hide_fetches
  wp_steps
  wp_done

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.segFrom_step_err_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} {sp : BitVec 64} {s : State}
    (hs_pc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x228#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hal : s.spAligned = true) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x49c#64)
      s ((sp + 0x580#64) ↦₆₄ errTag)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.trace = s.trace ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x21 = s.readReg64 .x21 ∧
        sm.readReg64 .x25 = s.readReg64 .x25 ∧
        sm.readReg64 .x26 = s.readReg64 .x26 ∧
        sm.readReg64 .x28 = s.readReg64 .x28 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        (Pm ⊢ (sp + 0x580#64) ↦₆₄ errTag)) := by
  dsimp only [trTrapProgAt, errTag] at hs_pc ⊢
  code_fetches_range CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.segFromBinCli b
    (Rust.withPanics (trTrapExterns C abs))
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.libsignalSessionCode_fnOff_sym_3caf4 (num% (ls_off% "libsignal_cli_ratchet::encrypt")) 552 12
  examples_generalize_entry
  examples_hide_fetches
  wp_steps
  wp_done


theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.segFrom_step_err {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {sp : BitVec 64} {s : State}
    (hs_pc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x228#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hal : s.spAligned = true) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x49c#64)
      s ((sp + 0x580#64) ↦₆₄ errTag)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.trace = s.trace ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x21 = s.readReg64 .x21 ∧
        sm.readReg64 .x25 = s.readReg64 .x25 ∧
        sm.readReg64 .x26 = s.readReg64 .x26 ∧
        sm.readReg64 .x28 = s.readReg64 .x28 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        (Pm ⊢ (sp + 0x580#64) ↦₆₄ errTag)) := by
  dsimp only [tripleRatchetProgAt, errTag] at hs_pc ⊢
  code_fetches_range CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.segFromBinCli b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.libsignalSessionCode_fnOff_sym_3caf4 (num% (ls_off% "libsignal_cli_ratchet::encrypt")) 552 12
  examples_generalize_entry
  examples_hide_fetches
  wp_steps
  wp_done

set_option maxHeartbeats 1600000 in
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.segFrom_step_ok_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} {sp : BitVec 64}
    {pqCap w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 :
      BitVec 64}
    {d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 d21 d22 d23 d24 :
      BitVec 64}
    {u850 u858 u860 u950 u958 u960 : BitVec 64} {u469 : BitVec 8} {s : State}
    (hs_pc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x228#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hal : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = sp + 0x58#64)
    (hx24 : s.readReg64 .x24 = sp + 0x58#64)
    (hx25 : s.readReg64 .x25 = sp + 0x580#64)
    (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hx27 : s.readReg64 .x27 = sp + 0xc0#64)
    (hx28 : s.readReg64 .x28 = sp + 0x4a0#64)
    (hpq : pqCap + 1#64 ≠ 0#64) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x2c8#64)
      s (((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        otrWords25 (sp + 0x288#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17
          d18 d19 d20 d21 d22 d23 d24 ∗
        ((sp + 0x469#64) ↦₈ u469) ∗
        otrWords25 (sp + 0x580#64) pqCap w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16
          w17 w18 w19 w20 w21 w22 w23 w24 ∗
        ((sp + 0x850#64) ↦₆₄ u850) ∗ ((sp + 0x858#64) ↦₆₄ u858) ∗ ((sp + 0x860#64) ↦₆₄ u860) ∗
        ((sp + 0x950#64) ↦₆₄ u950) ∗ ((sp + 0x958#64) ↦₆₄ u958) ∗ ((sp + 0x960#64) ↦₆₄ u960))
      (fun sm Pm =>
        sm.sp = sp ∧ sm.trace = s.trace ∧
        sm.readReg64 .x0 = sp + 0x128#64 ∧
        sm.readReg64 .x8 = sp + 0x580#64 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = sp + 0x58#64 ∧
        sm.readReg64 .x22 = sp + 0x8b8#64 ∧
        sm.readReg64 .x23 = sp + 0x58#64 ∧
        sm.readReg64 .x24 = sp + 0x58#64 ∧
        sm.readReg64 .x25 = sp + 0x580#64 ∧
        sm.readReg64 .x26 = sp + 0x9d0#64 ∧
        sm.readReg64 .x27 = sp + 0xc0#64 ∧
        sm.readReg64 .x28 = sp + 0x4a0#64 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        (Pm ⊢ ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
          otrWords25 (sp + 0x288#64) pqCap w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16
            w17 w18 w19 w20 w21 w22 w23 w24 ∗
          ((sp + 0x469#64) ↦₈ 1#8) ∗
          otrWords25 (sp + 0x580#64) pqCap w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16
            w17 w18 w19 w20 w21 w22 w23 w24 ∗
          ((sp + 0x850#64) ↦₆₄ w4) ∗ ((sp + 0x858#64) ↦₆₄ w5) ∗ ((sp + 0x860#64) ↦₆₄ w6) ∗
          ((sp + 0x950#64) ↦₆₄ w4) ∗ ((sp + 0x958#64) ↦₆₄ w5) ∗ ((sp + 0x960#64) ↦₆₄ w6))) := by
  have hpq_beq : (pqCap + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hpq
  dsimp only [trTrapProgAt, otrWords25] at hs_pc ⊢
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  code_fetches_range CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.segFromBinCli b
    (Rust.withPanics (trTrapExterns C abs))
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.libsignalSessionCode_fnOff_sym_3caf4 (num% (ls_off% "libsignal_cli_ratchet::encrypt")) 552 160
  examples_generalize_entry
  examples_hide_fetches
  wp_steps
  wp_done

set_option maxHeartbeats 1600000 in
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.segFrom_step_ok {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {sp : BitVec 64}
    {pqCap w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 :
      BitVec 64}
    {d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 d21 d22 d23 d24 :
      BitVec 64}
    {u850 u858 u860 u950 u958 u960 : BitVec 64} {u469 : BitVec 8} {s : State}
    (hs_pc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x228#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hal : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = sp + 0x58#64)
    (hx24 : s.readReg64 .x24 = sp + 0x58#64)
    (hx25 : s.readReg64 .x25 = sp + 0x580#64)
    (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hx27 : s.readReg64 .x27 = sp + 0xc0#64)
    (hx28 : s.readReg64 .x28 = sp + 0x4a0#64)
    (hpq : pqCap + 1#64 ≠ 0#64) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x2c8#64)
      s (((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        otrWords25 (sp + 0x288#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17
          d18 d19 d20 d21 d22 d23 d24 ∗
        ((sp + 0x469#64) ↦₈ u469) ∗
        otrWords25 (sp + 0x580#64) pqCap w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16
          w17 w18 w19 w20 w21 w22 w23 w24 ∗
        ((sp + 0x850#64) ↦₆₄ u850) ∗ ((sp + 0x858#64) ↦₆₄ u858) ∗ ((sp + 0x860#64) ↦₆₄ u860) ∗
        ((sp + 0x950#64) ↦₆₄ u950) ∗ ((sp + 0x958#64) ↦₆₄ u958) ∗ ((sp + 0x960#64) ↦₆₄ u960))
      (fun sm Pm =>
        sm.sp = sp ∧ sm.trace = s.trace ∧
        sm.readReg64 .x0 = sp + 0x128#64 ∧
        sm.readReg64 .x8 = sp + 0x580#64 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = sp + 0x58#64 ∧
        sm.readReg64 .x22 = sp + 0x8b8#64 ∧
        sm.readReg64 .x23 = sp + 0x58#64 ∧
        sm.readReg64 .x24 = sp + 0x58#64 ∧
        sm.readReg64 .x25 = sp + 0x580#64 ∧
        sm.readReg64 .x26 = sp + 0x9d0#64 ∧
        sm.readReg64 .x27 = sp + 0xc0#64 ∧
        sm.readReg64 .x28 = sp + 0x4a0#64 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        (Pm ⊢ ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
          otrWords25 (sp + 0x288#64) pqCap w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16
            w17 w18 w19 w20 w21 w22 w23 w24 ∗
          ((sp + 0x469#64) ↦₈ 1#8) ∗
          otrWords25 (sp + 0x580#64) pqCap w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16
            w17 w18 w19 w20 w21 w22 w23 w24 ∗
          ((sp + 0x850#64) ↦₆₄ w4) ∗ ((sp + 0x858#64) ↦₆₄ w5) ∗ ((sp + 0x860#64) ↦₆₄ w6) ∗
          ((sp + 0x950#64) ↦₆₄ w4) ∗ ((sp + 0x958#64) ↦₆₄ w5) ∗ ((sp + 0x960#64) ↦₆₄ w6))) := by
  have hpq_beq : (pqCap + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hpq
  dsimp only [tripleRatchetProgAt, otrWords25] at hs_pc ⊢
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  code_fetches_range CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.segFromBinCli b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.libsignalSessionCode_fnOff_sym_3caf4 (num% (ls_off% "libsignal_cli_ratchet::encrypt")) 552 160
  examples_generalize_entry
  examples_hide_fetches
  wp_steps
  wp_done

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom
