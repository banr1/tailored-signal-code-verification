/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.AllocContractsMem4K
public import ProofLib.SepLogic.WP
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClosureStubs4K
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# Stage P3 `Ok` Closure Segment `+0x1cd8 → set_session_state`

Proves `adrp_closure_logMaxLevel_seg7a`, `p3_seg7a_x24_ext_4k_wp`, and `p3_seg7a_x24_ext_wp`
on `tripleRatchetProgAtExt b ext`.
-/

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local wp_norm] sessionMemcpySpec libcMemcpySpec

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")
  (ls_stub% "memcpy")

theorem adrp_closure_logMaxLevel_seg7a {b entry : BitVec 64}
    (hb : b &&& 0xfff#64 = 0#64)
    (he : entry = b + (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}"))) :
    (((entry + 0x1cec#64) &&& 0xfffffffffffff000#64) +
      bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) -
        (page% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7404))) =
      b + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256))) ∧
    ((((bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) + (b + 0x1cec#64)) &&& 0xfffffffffffff000#64) +
      bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) -
        (page% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7404))) =
      b + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256))) := by
  refine ⟨?_, ?_⟩
  · rw [he, BitVec.add_assoc, ProofLib.adrp_page_of_aligned hb, BitVec.add_assoc]; rfl
  · rw [← BitVec.add_assoc, BitVec.add_comm _ b, BitVec.add_assoc,
        ProofLib.adrp_page_of_aligned hb, BitVec.add_assoc]
    rfl

theorem p3_seg7a_x24_ext_4k_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : AllocContractsMem4K b A ext)
    (s : State) (coroPtr retPtr : BitVec 64)
    (ssBytes : List (BitVec 8))
    (hb : b &&& 0xfff#64 = 0#64)
    (hss_len : ssBytes.length = 344)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x1cd8#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAtExt b ext)
      (b + (bv% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state"))) s
      (((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
       ((s.sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
       ((s.sp + 0xa90#64) ↦ₛ ssBytes) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗ stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
          ((s.sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          ((s.sp + 0xa90#64) ↦ₛ ssBytes) ∗ ((s.sp + 0x3e0#64) ↦ₛ ssBytes) ∗ stackAt s.sp allocHookStack) ∧ s1.sp = s.sp ∧
        s1.trace = s.trace ∧ s1.readReg64 .x0 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x1 = s.sp + 0x3e0#64 ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧ s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = retPtr ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x1dfc#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hmemcpy := decryptPrekeyClosure_memcpy_ok_ext_4k hA
  closure_fetches_range_cli b (Rust.withPanics ext) 0x1cd8 0x1cf8
  closure_fetches_range_cli b (Rust.withPanics ext) 0x1de0 0x1df8
  dsimp only [tripleRatchetProgAtExt] at hmemcpy hpc ⊢
  have hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName =
      b + (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have hadrp0 := (adrp_closure_logMaxLevel_seg7a hb hentry).1
  have hadrp := (adrp_closure_logMaxLevel_seg7a hb hentry).2
  have htarget : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName +
      0x1df8#64 + bv% ((2^64 + ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state" - (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7672)) % 2^64) =
      b + (bv% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state")) := by
    rw [hentry]; bv_omega
  clear hentry
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hlog : (b + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256))) + bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096) = b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) := by bv_arith
  rw [← hss_len]
  wp_steps
  wp_call hmemcpy (s.sp + 0x3e0#64, s.sp + 0xa90#64, ssBytes)
  wp_steps
  refine SepWP.done (by rw [← htarget]; simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

theorem p3_seg7a_x24_ext_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : AllocContracts b A ext)
    (s : State) (coroPtr retPtr : BitVec 64)
    (ssBytes : List (BitVec 8))
    (hb : b &&& 0xfff#64 = 0#64)
    (hss_len : ssBytes.length = 344)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x1cd8#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAtExt b ext)
      (b + (bv% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state"))) s
      (((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
       ((s.sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
       ((s.sp + 0xa90#64) ↦ₛ ssBytes) ∗ memRegion (s.sp + 0x3e0#64) 344)
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
          ((s.sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          ((s.sp + 0xa90#64) ↦ₛ ssBytes) ∗ ((s.sp + 0x3e0#64) ↦ₛ ssBytes)) ∧ s1.sp = s.sp ∧
        s1.trace = s.trace ∧ s1.readReg64 .x0 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x1 = s.sp + 0x3e0#64 ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧ s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = retPtr ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x1dfc#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hmemcpy := decryptPrekeyClosure_memcpy_ok_ext hA
  closure_fetches_range_cli b (Rust.withPanics ext) 0x1cd8 0x1cf8
  closure_fetches_range_cli b (Rust.withPanics ext) 0x1de0 0x1df8
  dsimp only [tripleRatchetProgAtExt] at hmemcpy hpc ⊢
  have hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName =
      b + (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have hadrp0 := (adrp_closure_logMaxLevel_seg7a hb hentry).1
  have hadrp := (adrp_closure_logMaxLevel_seg7a hb hentry).2
  have htarget : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName +
      0x1df8#64 + bv% ((2^64 + ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state" - (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7672)) % 2^64) =
      b + (bv% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state")) := by
    rw [hentry]; bv_omega
  clear hentry
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hlog : (b + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256))) + bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096) = b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) := by bv_arith
  rw [← hss_len]
  wp_steps
  wp_call hmemcpy (s.sp + 0x3e0#64, s.sp + 0xa90#64, ssBytes)
  wp_steps
  refine SepWP.done (by rw [← htarget]; simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
