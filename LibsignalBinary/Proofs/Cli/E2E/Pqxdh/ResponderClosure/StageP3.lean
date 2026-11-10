/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch
public import LibsignalBinary.Proofs.TripleRatchet.TrapRng
public import ProofLib.SepLogic.WP
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.StageP1
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.StageP2a
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StageP3 -- shake: keep

/-!
# Responder Closure Stage P3 (`+0x1778 → +0x1df8`)

Symbolic-execution segment proofs for Stage P3 of the CLI responder prekey decryption closure,
cloning the promoted `SessionState` (`local_identity_public`, `remote_identity_public`, `root_key`,
`sender_chain`, `alice_base_key`, and `bob_kyber_ciphertext`), calling
`try_decrypt_with_state::<Coins>`, and persisting the updated state via
`SessionRecord::set_session_state`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E.Pqxdh.ResponderClosure

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000

set_option maxHeartbeats 1600000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")

/-! ## 1. Isolated Callee Contracts for Stage P3 (`+0x1778..+0x1e00`) -/

structure _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.StageP3CalleeContracts_trap (A : RustAlloc) (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (chainCloneSpec tryDecryptWithStateSpec setSessionStateSpec : Spec) : Prop where
  alloc : AllocHooks A abs
  chainClone : subroutine_ok (trTrapProgAt b C abs) (b + (bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#4]"))) chainCloneSpec
  tryDecryptWithState : subroutine_ok (trTrapProgAt b C abs)
    (b + (bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))) tryDecryptWithStateSpec
  setSessionState : subroutine_ok (trTrapProgAt b C abs)
    (b + (bv% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state"))) setSessionStateSpec

/-- External callee contracts for Stage P3 (`Chain::clone`, `try_decrypt_with_state::<Coins>`, and
`SessionRecord::set_session_state`). -/
structure _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.StageP3CalleeContracts (A : RustAlloc) (b : BitVec 64) (C : Crypto)
    (ctl : BitVec 64) (abs : String → Option (State → State))
    (chainCloneSpec tryDecryptWithStateSpec setSessionStateSpec : Spec) : Prop where
  alloc : AllocHooks A abs
  chainClone : subroutine_ok (tripleRatchetProgAt b C ctl abs) (b + (bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#4]"))) chainCloneSpec
  tryDecryptWithState : subroutine_ok (tripleRatchetProgAt b C ctl abs)
    (b + (bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))) tryDecryptWithStateSpec
  setSessionState : subroutine_ok (tripleRatchetProgAt b C ctl abs)
    (b + 0x174d4#64) setSessionStateSpec

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.StageP3CalleeContracts_of_trap
    {A : RustAlloc} {b : BitVec 64} {C : Crypto} (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    {chainCloneSpec tryDecryptWithStateSpec setSessionStateSpec : Spec}
    (h : CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.StageP3CalleeContracts_trap A b C abs
      chainCloneSpec tryDecryptWithStateSpec setSessionStateSpec) :
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.StageP3CalleeContracts A b C ctl abs
      chainCloneSpec tryDecryptWithStateSpec setSessionStateSpec :=
  ⟨h.alloc,
   subroutine_ok_kit_of_trTrap h.chainClone,
   subroutine_ok_kit_of_trTrap h.tryDecryptWithState,
   subroutine_ok_kit_of_trTrap h.setSessionState⟩


/-- Address of `log::STATIC_MAX_LEVEL` (`b + 0xaa080#64`) computed by `adrp x8, +0xf000; ldr x8,
[x8, #0x810]`
at `0x4cdb8` (`+0x1cec`). -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.adrp_logMaxLevel_0x1cec {b entry : BitVec 64}
    (hb : b &&& 0xfff#64 = 0#64)
    (hentry : entry = b + (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}"))) :
    (((entry + 0x1cec#64) &&& 18446744073709547520#64) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - (page% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7404))) = b + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256))) ∧
    ((((entry + 0x1cec#64) &&& 18446744073709547520#64) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - (page% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7404)))) + bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096) =
      b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) := by
  refine ⟨?_, ?_⟩
  · rw [hentry, BitVec.add_assoc, ProofLib.adrp_page_of_aligned hb, BitVec.add_assoc]; rfl
  · rw [hentry, BitVec.add_assoc b, ProofLib.adrp_page_of_aligned hb, BitVec.add_assoc b,
        BitVec.add_assoc b]
    rfl

/-! ## 2. Substage P3.1 (`+0x1778 -> +0x18e0`, `local_identity_public` clone) -/

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg1a_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr locIdPtr locIdLen u_d0 : BitVec 64)
    (sessionVer u_7c : BitVec 32)
    (hlen_nz : locIdLen ≠ 0#64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1778#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x179c#64) s
      (((coroPtr + 0x100#64) ↦₆₄ locIdPtr) ∗
       ((coroPtr + 0x108#64) ↦₆₄ locIdLen) ∗
       ((coroPtr + 0x240#64) ↦₃₂ sessionVer) ∗
       ((s.sp + 0x7c#64) ↦₃₂ u_7c) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x100#64) ↦₆₄ locIdPtr) ∗
          ((coroPtr + 0x108#64) ↦₆₄ locIdLen) ∗
          ((coroPtr + 0x240#64) ↦₃₂ sessionVer) ∗
          ((s.sp + 0x7c#64) ↦₃₂ sessionVer) ∗
          ((s.sp + 0xd0#64) ↦₆₄ locIdLen)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = locIdLen ∧
        s1.readReg64 .x1 = 1#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = locIdPtr ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  have hshim := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_shim_ok_trap (b := b) (C := C)
    (abs := abs)
  have hlen_beq : (locIdLen == 0#64) = false := beq_eq_false_iff_ne.mpr hlen_nz
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x1778 0x1798
  dsimp only [trTrapProgAt] at hshim hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  wp_call hshim ()
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- Segment P3.1a (`+0x1778 → +0x179c`): reads `local_identity_public` length/pointer (`≠ 0`) and
prepares `__rust_alloc(locIdLen, 1)`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg1a_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr locIdPtr locIdLen u_d0 : BitVec 64)
    (sessionVer u_7c : BitVec 32)
    (hlen_nz : locIdLen ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1778#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x179c#64) s
      (((coroPtr + 0x100#64) ↦₆₄ locIdPtr) ∗
       ((coroPtr + 0x108#64) ↦₆₄ locIdLen) ∗
       ((coroPtr + 0x240#64) ↦₃₂ sessionVer) ∗
       ((s.sp + 0x7c#64) ↦₃₂ u_7c) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x100#64) ↦₆₄ locIdPtr) ∗
          ((coroPtr + 0x108#64) ↦₆₄ locIdLen) ∗
          ((coroPtr + 0x240#64) ↦₃₂ sessionVer) ∗
          ((s.sp + 0x7c#64) ↦₃₂ sessionVer) ∗
          ((s.sp + 0xd0#64) ↦₆₄ locIdLen)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = locIdLen ∧
        s1.readReg64 .x1 = 1#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = locIdPtr ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg1a_wp_trap b C abs s
      coroPtr locIdPtr locIdLen u_d0 sessionVer u_7c hlen_nz hpc hrun hsp_align hx19)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg1b_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr locIdPtr newLocIdPtr : BitVec 64)
    (locIdBytes : List (BitVec 8))
    (hnew_nz : newLocIdPtr ≠ 0#64)
    (hlen_lt : locIdBytes.length < 2 ^ 64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x17a0#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = newLocIdPtr)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = locIdPtr) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x18e0#64) s
      (((s.sp + 0xd0#64) ↦₆₄ BitVec.ofNat 64 locIdBytes.length) ∗
       (locIdPtr ↦ₛ locIdBytes) ∗
       memRegion newLocIdPtr locIdBytes.length)
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0xd0#64) ↦₆₄ BitVec.ofNat 64 locIdBytes.length) ∗
          (locIdPtr ↦ₛ locIdBytes) ∗
          (newLocIdPtr ↦ₛ locIdBytes)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x23 = newLocIdPtr ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  have hmemcpy := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_memcpy_ok_trap (b := b) (C := C)
    (abs := abs)
  have hnew_beq : (newLocIdPtr == 0#64) = false := beq_eq_false_iff_ne.mpr hnew_nz
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x17a0 0x17b4
  dsimp only [trTrapProgAt] at hmemcpy hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx0' : s.readReg64 (Reg.gpr 0#5) = newLocIdPtr := hx0
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = locIdPtr := hx21
  wp_steps
  wp_call hmemcpy (newLocIdPtr, locIdPtr, locIdBytes)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

/-- Segment P3.1b (`+0x17a0 → +0x18e0`): copies `local_identity_public` into `newLocIdPtr` via
`memcpy` and branches to `+0x18e0`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg1b_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr locIdPtr newLocIdPtr : BitVec 64)
    (locIdBytes : List (BitVec 8))
    (hnew_nz : newLocIdPtr ≠ 0#64)
    (hlen_lt : locIdBytes.length < 2 ^ 64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x17a0#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = newLocIdPtr)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = locIdPtr) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x18e0#64) s
      (((s.sp + 0xd0#64) ↦₆₄ BitVec.ofNat 64 locIdBytes.length) ∗
       (locIdPtr ↦ₛ locIdBytes) ∗
       memRegion newLocIdPtr locIdBytes.length)
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0xd0#64) ↦₆₄ BitVec.ofNat 64 locIdBytes.length) ∗
          (locIdPtr ↦ₛ locIdBytes) ∗
          (newLocIdPtr ↦ₛ locIdBytes)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x23 = newLocIdPtr ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg1b_wp_trap b C abs s
      coroPtr locIdPtr newLocIdPtr locIdBytes hnew_nz hlen_lt hpc hrun hsp_align hx0 hx19 hx21)

/-! ## 3. Substage P3.2 (`+0x18e0 -> +0x191c`, `remote_identity_public` clone) -/

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg2a_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr remIdPtr remIdLen : BitVec 64)
    (hlen_nz : remIdLen ≠ 0#64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x18e0#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x18fc#64) s
      (((coroPtr + 0x118#64) ↦₆₄ remIdPtr) ∗
       ((coroPtr + 0x120#64) ↦₆₄ remIdLen))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x118#64) ↦₆₄ remIdPtr) ∗
          ((coroPtr + 0x120#64) ↦₆₄ remIdLen)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = remIdLen ∧
        s1.readReg64 .x1 = 1#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = remIdPtr ∧
        s1.readReg64 .x22 = s.sp + 0x930#64 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = remIdLen ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  have hshim := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_shim_ok_trap (b := b) (C := C)
    (abs := abs)
  have hlen_beq : (remIdLen == 0#64) = false := beq_eq_false_iff_ne.mpr hlen_nz
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x18e0 0x18f8
  dsimp only [trTrapProgAt] at hshim hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  wp_call hshim ()
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- Segment P3.2a (`+0x18e0 → +0x18fc`): reads `remote_identity_public` length/pointer (`≠ 0`) and
prepares `__rust_alloc(remIdLen, 1)`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg2a_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr remIdPtr remIdLen : BitVec 64)
    (hlen_nz : remIdLen ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x18e0#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x18fc#64) s
      (((coroPtr + 0x118#64) ↦₆₄ remIdPtr) ∗
       ((coroPtr + 0x120#64) ↦₆₄ remIdLen))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x118#64) ↦₆₄ remIdPtr) ∗
          ((coroPtr + 0x120#64) ↦₆₄ remIdLen)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = remIdLen ∧
        s1.readReg64 .x1 = 1#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = remIdPtr ∧
        s1.readReg64 .x22 = s.sp + 0x930#64 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = remIdLen ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg2a_wp_trap b C abs s
      coroPtr remIdPtr remIdLen hlen_nz hpc hrun hsp_align hx19)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg2b_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr remIdPtr newRemIdPtr : BitVec 64)
    (remIdBytes : List (BitVec 8))
    (hnew_nz : newRemIdPtr ≠ 0#64)
    (hlen_lt : remIdBytes.length < 2 ^ 64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1900#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = newRemIdPtr)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = remIdPtr)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 remIdBytes.length) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x191c#64) s
      ((remIdPtr ↦ₛ remIdBytes) ∗
       memRegion newRemIdPtr remIdBytes.length)
      (fun s1 P_f =>
        (P_f ⊢
          (remIdPtr ↦ₛ remIdBytes) ∗
          (newRemIdPtr ↦ₛ remIdBytes)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = BitVec.ofNat 64 remIdBytes.length ∧
        s1.readReg64 .x25 = newRemIdPtr ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  have hmemcpy := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_memcpy_ok_trap (b := b) (C := C)
    (abs := abs)
  have hnew_beq : (newRemIdPtr == 0#64) = false := beq_eq_false_iff_ne.mpr hnew_nz
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x1900 0x1914
  dsimp only [trTrapProgAt] at hmemcpy hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx0' : s.readReg64 (Reg.gpr 0#5) = newRemIdPtr := hx0
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = remIdPtr := hx21
  have hx24' : s.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 remIdBytes.length := hx24
  wp_steps
  wp_call hmemcpy (newRemIdPtr, remIdPtr, remIdBytes)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

/-- Segment P3.2b (`+0x1900 → +0x191c`): copies `remote_identity_public` into `newRemIdPtr` via
`memcpy` and branches to `+0x191c`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg2b_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr remIdPtr newRemIdPtr : BitVec 64)
    (remIdBytes : List (BitVec 8))
    (hnew_nz : newRemIdPtr ≠ 0#64)
    (hlen_lt : remIdBytes.length < 2 ^ 64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1900#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = newRemIdPtr)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = remIdPtr)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 remIdBytes.length) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x191c#64) s
      ((remIdPtr ↦ₛ remIdBytes) ∗
       memRegion newRemIdPtr remIdBytes.length)
      (fun s1 P_f =>
        (P_f ⊢
          (remIdPtr ↦ₛ remIdBytes) ∗
          (newRemIdPtr ↦ₛ remIdBytes)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = BitVec.ofNat 64 remIdBytes.length ∧
        s1.readReg64 .x25 = newRemIdPtr ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg2b_wp_trap b C abs s
      coroPtr remIdPtr newRemIdPtr remIdBytes hnew_nz hlen_lt hpc hrun hsp_align hx0 hx19 hx21 hx24)

/-! ## 4. Substage P3.3 (`+0x191c -> +0x195c`, `root_key` clone) -/

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg3a_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr rootKeyPtr rootKeyLen u_98 : BitVec 64)
    (hlen_nz : rootKeyLen ≠ 0#64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x191c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1938#64) s
      (((coroPtr + 0x130#64) ↦₆₄ rootKeyPtr) ∗
       ((coroPtr + 0x138#64) ↦₆₄ rootKeyLen) ∗
       ((s.sp + 0x98#64) ↦₆₄ u_98))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x130#64) ↦₆₄ rootKeyPtr) ∗
          ((coroPtr + 0x138#64) ↦₆₄ rootKeyLen) ∗
          ((s.sp + 0x98#64) ↦₆₄ rootKeyLen)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = rootKeyLen ∧
        s1.readReg64 .x1 = 1#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = rootKeyPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = rootKeyLen ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  have hshim := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_shim_ok_trap (b := b) (C := C)
    (abs := abs)
  have hlen_beq : (rootKeyLen == 0#64) = false := beq_eq_false_iff_ne.mpr hlen_nz
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x191c 0x1934
  dsimp only [trTrapProgAt] at hshim hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  wp_call hshim ()
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- Segment P3.3a (`+0x191c → +0x1938`): reads `root_key` length/pointer (`≠ 0`) and prepares
`__rust_alloc(rootKeyLen, 1)`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg3a_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr rootKeyPtr rootKeyLen u_98 : BitVec 64)
    (hlen_nz : rootKeyLen ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x191c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1938#64) s
      (((coroPtr + 0x130#64) ↦₆₄ rootKeyPtr) ∗
       ((coroPtr + 0x138#64) ↦₆₄ rootKeyLen) ∗
       ((s.sp + 0x98#64) ↦₆₄ u_98))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x130#64) ↦₆₄ rootKeyPtr) ∗
          ((coroPtr + 0x138#64) ↦₆₄ rootKeyLen) ∗
          ((s.sp + 0x98#64) ↦₆₄ rootKeyLen)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = rootKeyLen ∧
        s1.readReg64 .x1 = 1#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = rootKeyPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = rootKeyLen ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg3a_wp_trap b C abs s
      coroPtr rootKeyPtr rootKeyLen u_98 hlen_nz hpc hrun hsp_align hx19)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg3b_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr rootKeyPtr newRootKeyPtr u_50 : BitVec 64)
    (rootKeyBytes : List (BitVec 8))
    (hnew_nz : newRootKeyPtr ≠ 0#64)
    (hlen_lt : rootKeyBytes.length < 2 ^ 64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x193c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = newRootKeyPtr)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = rootKeyPtr)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 rootKeyBytes.length) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x195c#64) s
      (((s.sp + 0x50#64) ↦₆₄ u_50) ∗
       (rootKeyPtr ↦ₛ rootKeyBytes) ∗
       memRegion newRootKeyPtr rootKeyBytes.length)
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗
          (rootKeyPtr ↦ₛ rootKeyBytes) ∗
          (newRootKeyPtr ↦ₛ rootKeyBytes)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  have hmemcpy := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_memcpy_ok_trap (b := b) (C := C)
    (abs := abs)
  have hnew_beq : (newRootKeyPtr == 0#64) = false := beq_eq_false_iff_ne.mpr hnew_nz
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x193c 0x1950
  dsimp only [trTrapProgAt] at hmemcpy hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx0' : s.readReg64 (Reg.gpr 0#5) = newRootKeyPtr := hx0
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = rootKeyPtr := hx21
  have hx26' : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 rootKeyBytes.length := hx26
  wp_steps
  wp_call hmemcpy (newRootKeyPtr, rootKeyPtr, rootKeyBytes)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

/-- Segment P3.3b (`+0x193c → +0x195c`): copies `root_key` into `newRootKeyPtr` via `memcpy` and
branches to `+0x195c`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg3b_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr rootKeyPtr newRootKeyPtr u_50 : BitVec 64)
    (rootKeyBytes : List (BitVec 8))
    (hnew_nz : newRootKeyPtr ≠ 0#64)
    (hlen_lt : rootKeyBytes.length < 2 ^ 64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x193c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = newRootKeyPtr)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = rootKeyPtr)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 rootKeyBytes.length) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x195c#64) s
      (((s.sp + 0x50#64) ↦₆₄ u_50) ∗
       (rootKeyPtr ↦ₛ rootKeyBytes) ∗
       memRegion newRootKeyPtr rootKeyBytes.length)
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗
          (rootKeyPtr ↦ₛ rootKeyBytes) ∗
          (newRootKeyPtr ↦ₛ rootKeyBytes)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg3b_wp_trap b C abs s
      coroPtr rootKeyPtr newRootKeyPtr u_50 rootKeyBytes hnew_nz hlen_lt hpc hrun hsp_align hx0 hx19 hx21 hx26)

/-! ## 5. Substage P3.4 (`+0x195c -> +0x1b20`, `sender_chain`, `receiver_chains`, `pending_*`) -/

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg4a1_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr sc0 : BitVec 64)
    (prevCounter u_5c : BitVec 32)
    (hsc_ne : sc0 + 1#64 ≠ 0#64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x195c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (trTrapProgAt b C abs) (b + (bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#4]"))) s
      (((coroPtr + 0x188#64) ↦₆₄ sc0) ∗
       ((coroPtr + 0x244#64) ↦₃₂ prevCounter) ∗
       ((s.sp + 0x5c#64) ↦₃₂ u_5c))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x188#64) ↦₆₄ sc0) ∗
          ((coroPtr + 0x244#64) ↦₃₂ prevCounter) ∗
          ((s.sp + 0x5c#64) ↦₃₂ prevCounter)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x1 = coroPtr + 0x188#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x197c#64) := by
  have hsc_beq : (sc0 + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hsc_ne
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x195c 0x1978
  dsimp only [trTrapProgAt] at hpc ⊢
  have hentry : (libsignalSessionCode.rebase b
      (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName =
      b + (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have htarget : (libsignalSessionCode.rebase b
      (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
      0x1978#64 + bv% ((2^64 + ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#4]" - (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 6520)) % 2^64) = b + (bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#4]")) := by
    rw [hentry]; bv_omega
  clear hentry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  refine SepWP.done (by rw [← htarget]; simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

/-- Segment P3.4a1 (`+0x195c → +0x1978`): saves `prevCounter` and calls `Chain::clone` on
`sender_chain` (`coroPtr + 0x188`). -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg4a1_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr sc0 : BitVec 64)
    (prevCounter u_5c : BitVec 32)
    (hsc_ne : sc0 + 1#64 ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x195c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAt b C ctl abs) (b + (bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#4]"))) s
      (((coroPtr + 0x188#64) ↦₆₄ sc0) ∗
       ((coroPtr + 0x244#64) ↦₃₂ prevCounter) ∗
       ((s.sp + 0x5c#64) ↦₃₂ u_5c))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x188#64) ↦₆₄ sc0) ∗
          ((coroPtr + 0x244#64) ↦₃₂ prevCounter) ∗
          ((s.sp + 0x5c#64) ↦₃₂ prevCounter)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x1 = coroPtr + 0x188#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x197c#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg4a1_wp_trap b C abs s
      coroPtr sc0 prevCounter u_5c hsc_ne hpc hrun hsp_align hx19)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg4a2_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr u_48
    c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12
    u930 u938 u940 u948 u950 u958 u960 u968 u970 u978 u980 u988 : BitVec 64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x197c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = s.sp + 0x930#64)
    (hx27 : s.readReg64 .x27 = s.sp + 0x370#64) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x19b0#64) s
      (((s.sp + 0x48#64) ↦₆₄ u_48) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ c0) ∗ ((s.sp + 0x3e8#64) ↦₆₄ c1) ∗
       ((s.sp + 0x3f0#64) ↦₆₄ c2) ∗ ((s.sp + 0x3f8#64) ↦₆₄ c3) ∗
       ((s.sp + 0x400#64) ↦₆₄ c4) ∗ ((s.sp + 0x408#64) ↦₆₄ c5) ∗
       ((s.sp + 0x410#64) ↦₆₄ c6) ∗ ((s.sp + 0x418#64) ↦₆₄ c7) ∗
       ((s.sp + 0x420#64) ↦₆₄ c8) ∗ ((s.sp + 0x428#64) ↦₆₄ c9) ∗
       ((s.sp + 0x430#64) ↦₆₄ c10) ∗ ((s.sp + 0x438#64) ↦₆₄ c11) ∗
       ((s.sp + 0x440#64) ↦₆₄ c12) ∗
       ((s.sp + 0x930#64) ↦₆₄ u930) ∗ ((s.sp + 0x938#64) ↦₆₄ u938) ∗
       ((s.sp + 0x940#64) ↦₆₄ u940) ∗ ((s.sp + 0x948#64) ↦₆₄ u948) ∗
       ((s.sp + 0x950#64) ↦₆₄ u950) ∗ ((s.sp + 0x958#64) ↦₆₄ u958) ∗
       ((s.sp + 0x960#64) ↦₆₄ u960) ∗ ((s.sp + 0x968#64) ↦₆₄ u968) ∗
       ((s.sp + 0x970#64) ↦₆₄ u970) ∗ ((s.sp + 0x978#64) ↦₆₄ u978) ∗
       ((s.sp + 0x980#64) ↦₆₄ u980) ∗ ((s.sp + 0x988#64) ↦₆₄ u988))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x48#64) ↦₆₄ c0) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ c0) ∗ ((s.sp + 0x3e8#64) ↦₆₄ c1) ∗
          ((s.sp + 0x3f0#64) ↦₆₄ c2) ∗ ((s.sp + 0x3f8#64) ↦₆₄ c3) ∗
          ((s.sp + 0x400#64) ↦₆₄ c4) ∗ ((s.sp + 0x408#64) ↦₆₄ c5) ∗
          ((s.sp + 0x410#64) ↦₆₄ c6) ∗ ((s.sp + 0x418#64) ↦₆₄ c7) ∗
          ((s.sp + 0x420#64) ↦₆₄ c8) ∗ ((s.sp + 0x428#64) ↦₆₄ c9) ∗
          ((s.sp + 0x430#64) ↦₆₄ c10) ∗ ((s.sp + 0x438#64) ↦₆₄ c11) ∗
          ((s.sp + 0x440#64) ↦₆₄ c12) ∗
          ((s.sp + 0x930#64) ↦₆₄ c1) ∗ ((s.sp + 0x938#64) ↦₆₄ c2) ∗
          ((s.sp + 0x940#64) ↦₆₄ c3) ∗ ((s.sp + 0x948#64) ↦₆₄ c4) ∗
          ((s.sp + 0x950#64) ↦₆₄ c5) ∗ ((s.sp + 0x958#64) ↦₆₄ c6) ∗
          ((s.sp + 0x960#64) ↦₆₄ c7) ∗ ((s.sp + 0x968#64) ↦₆₄ c8) ∗
          ((s.sp + 0x970#64) ↦₆₄ c9) ∗ ((s.sp + 0x978#64) ↦₆₄ c10) ∗
          ((s.sp + 0x980#64) ↦₆₄ c11) ∗ ((s.sp + 0x988#64) ↦₆₄ c12)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x27 = s.sp + 0x370#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x197c 0x19a8
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = s.sp + 0x930#64 := hx22
  have hx27' : s.readReg64 (Reg.gpr 27#5) = s.sp + 0x370#64 := hx27
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- Segment P3.4a2 (`+0x197c → +0x19b0`): stages the 104-byte cloned `Chain` into `[sp + 0x48]` and
`sp + 0x930..0x990`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg4a2_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr u_48
    c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12
    u930 u938 u940 u948 u950 u958 u960 u968 u970 u978 u980 u988 : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x197c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = s.sp + 0x930#64)
    (hx27 : s.readReg64 .x27 = s.sp + 0x370#64) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x19b0#64) s
      (((s.sp + 0x48#64) ↦₆₄ u_48) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ c0) ∗ ((s.sp + 0x3e8#64) ↦₆₄ c1) ∗
       ((s.sp + 0x3f0#64) ↦₆₄ c2) ∗ ((s.sp + 0x3f8#64) ↦₆₄ c3) ∗
       ((s.sp + 0x400#64) ↦₆₄ c4) ∗ ((s.sp + 0x408#64) ↦₆₄ c5) ∗
       ((s.sp + 0x410#64) ↦₆₄ c6) ∗ ((s.sp + 0x418#64) ↦₆₄ c7) ∗
       ((s.sp + 0x420#64) ↦₆₄ c8) ∗ ((s.sp + 0x428#64) ↦₆₄ c9) ∗
       ((s.sp + 0x430#64) ↦₆₄ c10) ∗ ((s.sp + 0x438#64) ↦₆₄ c11) ∗
       ((s.sp + 0x440#64) ↦₆₄ c12) ∗
       ((s.sp + 0x930#64) ↦₆₄ u930) ∗ ((s.sp + 0x938#64) ↦₆₄ u938) ∗
       ((s.sp + 0x940#64) ↦₆₄ u940) ∗ ((s.sp + 0x948#64) ↦₆₄ u948) ∗
       ((s.sp + 0x950#64) ↦₆₄ u950) ∗ ((s.sp + 0x958#64) ↦₆₄ u958) ∗
       ((s.sp + 0x960#64) ↦₆₄ u960) ∗ ((s.sp + 0x968#64) ↦₆₄ u968) ∗
       ((s.sp + 0x970#64) ↦₆₄ u970) ∗ ((s.sp + 0x978#64) ↦₆₄ u978) ∗
       ((s.sp + 0x980#64) ↦₆₄ u980) ∗ ((s.sp + 0x988#64) ↦₆₄ u988))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x48#64) ↦₆₄ c0) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ c0) ∗ ((s.sp + 0x3e8#64) ↦₆₄ c1) ∗
          ((s.sp + 0x3f0#64) ↦₆₄ c2) ∗ ((s.sp + 0x3f8#64) ↦₆₄ c3) ∗
          ((s.sp + 0x400#64) ↦₆₄ c4) ∗ ((s.sp + 0x408#64) ↦₆₄ c5) ∗
          ((s.sp + 0x410#64) ↦₆₄ c6) ∗ ((s.sp + 0x418#64) ↦₆₄ c7) ∗
          ((s.sp + 0x420#64) ↦₆₄ c8) ∗ ((s.sp + 0x428#64) ↦₆₄ c9) ∗
          ((s.sp + 0x430#64) ↦₆₄ c10) ∗ ((s.sp + 0x438#64) ↦₆₄ c11) ∗
          ((s.sp + 0x440#64) ↦₆₄ c12) ∗
          ((s.sp + 0x930#64) ↦₆₄ c1) ∗ ((s.sp + 0x938#64) ↦₆₄ c2) ∗
          ((s.sp + 0x940#64) ↦₆₄ c3) ∗ ((s.sp + 0x948#64) ↦₆₄ c4) ∗
          ((s.sp + 0x950#64) ↦₆₄ c5) ∗ ((s.sp + 0x958#64) ↦₆₄ c6) ∗
          ((s.sp + 0x960#64) ↦₆₄ c7) ∗ ((s.sp + 0x968#64) ↦₆₄ c8) ∗
          ((s.sp + 0x970#64) ↦₆₄ c9) ∗ ((s.sp + 0x978#64) ↦₆₄ c10) ∗
          ((s.sp + 0x980#64) ↦₆₄ c11) ∗ ((s.sp + 0x988#64) ↦₆₄ c12)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x27 = s.sp + 0x370#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg4a2_wp_trap b C abs s
    coroPtr u_48 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12
    u930 u938 u940 u948 u950 u958 u960 u968 u970 u978 u980 u988 hpc hrun hsp_align hx19 hx22 hx27)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg4b_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr rootKeyLen newLocIdPtr newRemIdPtr remIdLen ctxPtr
    u_60 u_68 u_70 : BitVec 64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x19b0#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx23 : s.readReg64 .x23 = newLocIdPtr)
    (hx24 : s.readReg64 .x24 = remIdLen)
    (hx25 : s.readReg64 .x25 = newRemIdPtr) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1b20#64) s
      (((coroPtr + 0x150#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x1f0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
       ((coroPtr + 0x220#64) ↦₆₄ 0xffffffffffffffff#64) ∗
       ((s.sp + 0x60#64) ↦₆₄ u_60) ∗
       ((s.sp + 0x68#64) ↦₆₄ u_68) ∗
       ((s.sp + 0x70#64) ↦₆₄ u_70) ∗
       ((s.sp + 0x98#64) ↦₆₄ rootKeyLen) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x150#64) ↦₆₄ 0#64) ∗
          ((coroPtr + 0x1f0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
          ((coroPtr + 0x220#64) ↦₆₄ 0xffffffffffffffff#64) ∗
          ((s.sp + 0x60#64) ↦₆₄ newRemIdPtr) ∗
          ((s.sp + 0x68#64) ↦₆₄ remIdLen) ∗
          ((s.sp + 0x70#64) ↦₆₄ newLocIdPtr) ∗
          ((s.sp + 0x98#64) ↦₆₄ rootKeyLen) ∗
          ((s.sp + 0xc0#64) ↦₆₄ ctxPtr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x22 = 0xffffffffffffffff#64 ∧
        s1.readReg64 .x23 = 0#64 ∧
        s1.readReg64 .x25 = 8#64 ∧
        s1.readReg64 .x26 = 0xffffffffffffffff#64 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = rootKeyLen ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x19b0 0x19c0
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x1a58 0x1a68
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x1ab0 0x1ab8
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x1ac8 0x1ad0
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x1b10 0x1b14
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx23' : s.readReg64 (Reg.gpr 23#5) = newLocIdPtr := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = remIdLen := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = newRemIdPtr := hx25
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- Segment P3.4b (`+0x19b0 → +0x1b20`): fast path for a fresh responder session with empty
`receiver_chains`, `pending_key_exchange = None`, and `pending_pre_key = None`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg4b_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr rootKeyLen newLocIdPtr newRemIdPtr remIdLen ctxPtr
    u_60 u_68 u_70 : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x19b0#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx23 : s.readReg64 .x23 = newLocIdPtr)
    (hx24 : s.readReg64 .x24 = remIdLen)
    (hx25 : s.readReg64 .x25 = newRemIdPtr) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1b20#64) s
      (((coroPtr + 0x150#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x1f0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
       ((coroPtr + 0x220#64) ↦₆₄ 0xffffffffffffffff#64) ∗
       ((s.sp + 0x60#64) ↦₆₄ u_60) ∗
       ((s.sp + 0x68#64) ↦₆₄ u_68) ∗
       ((s.sp + 0x70#64) ↦₆₄ u_70) ∗
       ((s.sp + 0x98#64) ↦₆₄ rootKeyLen) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x150#64) ↦₆₄ 0#64) ∗
          ((coroPtr + 0x1f0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
          ((coroPtr + 0x220#64) ↦₆₄ 0xffffffffffffffff#64) ∗
          ((s.sp + 0x60#64) ↦₆₄ newRemIdPtr) ∗
          ((s.sp + 0x68#64) ↦₆₄ remIdLen) ∗
          ((s.sp + 0x70#64) ↦₆₄ newLocIdPtr) ∗
          ((s.sp + 0x98#64) ↦₆₄ rootKeyLen) ∗
          ((s.sp + 0xc0#64) ↦₆₄ ctxPtr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x22 = 0xffffffffffffffff#64 ∧
        s1.readReg64 .x23 = 0#64 ∧
        s1.readReg64 .x25 = 8#64 ∧
        s1.readReg64 .x26 = 0xffffffffffffffff#64 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = rootKeyLen ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg4b_wp_trap b C abs s
    coroPtr rootKeyLen newLocIdPtr newRemIdPtr remIdLen ctxPtr u_60 u_68 u_70
    hpc hrun hsp_align hx19 hx23 hx24 hx25)

/-! ## 6. Substage P3.5 (`+0x1b20 -> +0x1bac`, `alice_base_key` & `bob_kyber_ciphertext` clone) -/

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg5a1_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr aliceBasePtr aliceBaseLen u_38 u_40 : BitVec 64)
    (f248 f24c u_30 u_34 : BitVec 32)
    (hlen_nz : aliceBaseLen ≠ 0#64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1b20#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx23 : s.readReg64 .x23 = 0#64)
    (hx26 : s.readReg64 .x26 = 0xffffffffffffffff#64) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1b48#64) s
      (((coroPtr + 0x160#64) ↦₆₄ aliceBasePtr) ∗
       ((coroPtr + 0x168#64) ↦₆₄ aliceBaseLen) ∗
       ((coroPtr + 0x248#64) ↦₃₂ f248) ∗
       ((coroPtr + 0x24c#64) ↦₃₂ f24c) ∗
       ((s.sp + 0x30#64) ↦₃₂ u_30) ∗
       ((s.sp + 0x34#64) ↦₃₂ u_34) ∗
       ((s.sp + 0x38#64) ↦₆₄ u_38) ∗
       ((s.sp + 0x40#64) ↦₆₄ u_40))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x160#64) ↦₆₄ aliceBasePtr) ∗
          ((coroPtr + 0x168#64) ↦₆₄ aliceBaseLen) ∗
          ((coroPtr + 0x248#64) ↦₃₂ f248) ∗
          ((coroPtr + 0x24c#64) ↦₃₂ f24c) ∗
          ((s.sp + 0x30#64) ↦₃₂ f248) ∗
          ((s.sp + 0x34#64) ↦₃₂ f24c) ∗
          ((s.sp + 0x38#64) ↦₆₄ 0xffffffffffffffff#64) ∗
          ((s.sp + 0x40#64) ↦₆₄ 0#64)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = aliceBaseLen ∧
        s1.readReg64 .x1 = 1#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x21 = aliceBasePtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x24 = aliceBaseLen ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  have hshim := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_shim_ok_trap (b := b) (C := C)
    (abs := abs)
  have hlen_beq : (aliceBaseLen == 0#64) = false := beq_eq_false_iff_ne.mpr hlen_nz
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x1b20 0x1b44
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt] at hshim hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx23' : s.readReg64 (Reg.gpr 23#5) = 0#64 := hx23
  have hx26' : s.readReg64 (Reg.gpr 26#5) = 0xffffffffffffffff#64 := hx26
  wp_steps
  wp_call hshim ()
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

/-- Segment P3.5a1 (`+0x1b20 → +0x1b48`): reads `alice_base_key` length/pointer (`≠ 0`) and prepares
`__rust_alloc(aliceBaseLen, 1)`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg5a1_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr aliceBasePtr aliceBaseLen u_38 u_40 : BitVec 64)
    (f248 f24c u_30 u_34 : BitVec 32)
    (hlen_nz : aliceBaseLen ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1b20#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx23 : s.readReg64 .x23 = 0#64)
    (hx26 : s.readReg64 .x26 = 0xffffffffffffffff#64) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1b48#64) s
      (((coroPtr + 0x160#64) ↦₆₄ aliceBasePtr) ∗
       ((coroPtr + 0x168#64) ↦₆₄ aliceBaseLen) ∗
       ((coroPtr + 0x248#64) ↦₃₂ f248) ∗
       ((coroPtr + 0x24c#64) ↦₃₂ f24c) ∗
       ((s.sp + 0x30#64) ↦₃₂ u_30) ∗
       ((s.sp + 0x34#64) ↦₃₂ u_34) ∗
       ((s.sp + 0x38#64) ↦₆₄ u_38) ∗
       ((s.sp + 0x40#64) ↦₆₄ u_40))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x160#64) ↦₆₄ aliceBasePtr) ∗
          ((coroPtr + 0x168#64) ↦₆₄ aliceBaseLen) ∗
          ((coroPtr + 0x248#64) ↦₃₂ f248) ∗
          ((coroPtr + 0x24c#64) ↦₃₂ f24c) ∗
          ((s.sp + 0x30#64) ↦₃₂ f248) ∗
          ((s.sp + 0x34#64) ↦₃₂ f24c) ∗
          ((s.sp + 0x38#64) ↦₆₄ 0xffffffffffffffff#64) ∗
          ((s.sp + 0x40#64) ↦₆₄ 0#64)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = aliceBaseLen ∧
        s1.readReg64 .x1 = 1#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x21 = aliceBasePtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x24 = aliceBaseLen ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg5a1_wp_trap b C abs s
    coroPtr aliceBasePtr aliceBaseLen u_38 u_40 f248 f24c u_30 u_34
    hlen_nz hpc hrun hsp_align hx19 hx23 hx26)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg5a2_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr aliceBasePtr newAliceBasePtr : BitVec 64)
    (aliceBaseBytes : List (BitVec 8))
    (hnew_nz : newAliceBasePtr ≠ 0#64)
    (hlen_lt : aliceBaseBytes.length < 2 ^ 64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1b4c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = newAliceBasePtr)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = aliceBasePtr)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 aliceBaseBytes.length) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1b68#64) s
      ((aliceBasePtr ↦ₛ aliceBaseBytes) ∗
       memRegion newAliceBasePtr aliceBaseBytes.length)
      (fun s1 P_f =>
        (P_f ⊢
          (aliceBasePtr ↦ₛ aliceBaseBytes) ∗
          (newAliceBasePtr ↦ₛ aliceBaseBytes)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = newAliceBasePtr ∧
        s1.readReg64 .x24 = BitVec.ofNat 64 aliceBaseBytes.length ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  have hmemcpy := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_memcpy_ok_trap (b := b) (C := C)
    (abs := abs)
  have hnew_beq : (newAliceBasePtr == 0#64) = false := beq_eq_false_iff_ne.mpr hnew_nz
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x1b4c 0x1b60
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt] at hmemcpy hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx0' : s.readReg64 (Reg.gpr 0#5) = newAliceBasePtr := hx0
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = aliceBasePtr := hx21
  have hx24' : s.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 aliceBaseBytes.length := hx24
  wp_steps
  wp_call hmemcpy (newAliceBasePtr, aliceBasePtr, aliceBaseBytes)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- Segment P3.5a2 (`+0x1b4c → +0x1b68`): copies `alice_base_key` into `newAliceBasePtr` via `memcpy`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg5a2_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr aliceBasePtr newAliceBasePtr : BitVec 64)
    (aliceBaseBytes : List (BitVec 8))
    (hnew_nz : newAliceBasePtr ≠ 0#64)
    (hlen_lt : aliceBaseBytes.length < 2 ^ 64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1b4c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = newAliceBasePtr)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = aliceBasePtr)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 aliceBaseBytes.length) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1b68#64) s
      ((aliceBasePtr ↦ₛ aliceBaseBytes) ∗
       memRegion newAliceBasePtr aliceBaseBytes.length)
      (fun s1 P_f =>
        (P_f ⊢
          (aliceBasePtr ↦ₛ aliceBaseBytes) ∗
          (newAliceBasePtr ↦ₛ aliceBaseBytes)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = newAliceBasePtr ∧
        s1.readReg64 .x24 = BitVec.ofNat 64 aliceBaseBytes.length ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg5a2_wp_trap b C abs s
    coroPtr aliceBasePtr newAliceBasePtr aliceBaseBytes hnew_nz hlen_lt hpc hrun hsp_align hx0 hx19 hx21 hx24)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg5b1_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr bobKyberPtr bobKyberLen : BitVec 64)
    (hlen_nz : bobKyberLen ≠ 0#64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1b68#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1b84#64) s
      (((coroPtr + 0x178#64) ↦₆₄ bobKyberPtr) ∗
       ((coroPtr + 0x180#64) ↦₆₄ bobKyberLen))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x178#64) ↦₆₄ bobKyberPtr) ∗
          ((coroPtr + 0x180#64) ↦₆₄ bobKyberLen)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = bobKyberLen ∧
        s1.readReg64 .x1 = 1#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = bobKyberLen ∧
        s1.readReg64 .x27 = bobKyberPtr ∧
        s1.readReg64 .x28 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  have hshim := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_shim_ok_trap (b := b) (C := C)
    (abs := abs)
  have hlen_beq : (bobKyberLen == 0#64) = false := beq_eq_false_iff_ne.mpr hlen_nz
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x1b68 0x1b80
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt] at hshim hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  wp_call hshim ()
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- Segment P3.5b1 (`+0x1b68 → +0x1b84`): reads `bob_kyber_ciphertext` length/pointer (`≠ 0`) and
prepares `__rust_alloc(bobKyberLen, 1)`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg5b1_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr bobKyberPtr bobKyberLen : BitVec 64)
    (hlen_nz : bobKyberLen ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1b68#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1b84#64) s
      (((coroPtr + 0x178#64) ↦₆₄ bobKyberPtr) ∗
       ((coroPtr + 0x180#64) ↦₆₄ bobKyberLen))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x178#64) ↦₆₄ bobKyberPtr) ∗
          ((coroPtr + 0x180#64) ↦₆₄ bobKyberLen)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = bobKyberLen ∧
        s1.readReg64 .x1 = 1#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = bobKyberLen ∧
        s1.readReg64 .x27 = bobKyberPtr ∧
        s1.readReg64 .x28 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg5b1_wp_trap b C abs s
    coroPtr bobKyberPtr bobKyberLen hlen_nz hpc hrun hsp_align hx19)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg5b2_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr bobKyberPtr newBobKyberPtr rootKeyLen : BitVec 64)
    (bobKyberBytes : List (BitVec 8))
    (hnew_nz : newBobKyberPtr ≠ 0#64)
    (hlen_lt : bobKyberBytes.length < 2 ^ 64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1b88#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = newBobKyberPtr)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 bobKyberBytes.length)
    (hx27 : s.readReg64 .x27 = bobKyberPtr) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1bac#64) s
      (((s.sp + 0x98#64) ↦₆₄ rootKeyLen) ∗
       (bobKyberPtr ↦ₛ bobKyberBytes) ∗
       memRegion newBobKyberPtr bobKyberBytes.length)
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x98#64) ↦₆₄ rootKeyLen) ∗
          (bobKyberPtr ↦ₛ bobKyberBytes) ∗
          (newBobKyberPtr ↦ₛ bobKyberBytes)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x21 = newBobKyberPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = BitVec.ofNat 64 bobKyberBytes.length ∧
        s1.readReg64 .x27 = s.readReg64 .x28 ∧
        s1.readReg64 .x28 = rootKeyLen ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  have hmemcpy := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_memcpy_ok_trap (b := b) (C := C)
    (abs := abs)
  have hnew_beq : (newBobKyberPtr == 0#64) = false := beq_eq_false_iff_ne.mpr hnew_nz
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x1b88 0x1ba4
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt] at hmemcpy hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx0' : s.readReg64 (Reg.gpr 0#5) = newBobKyberPtr := hx0
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx26' : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 bobKyberBytes.length := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = bobKyberPtr := hx27
  wp_steps
  wp_call hmemcpy (newBobKyberPtr, bobKyberPtr, bobKyberBytes)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- Segment P3.5b2 (`+0x1b88 → +0x1bac`): copies `bob_kyber_ciphertext` into `newBobKyberPtr` via
`memcpy` and restores spilled registers. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg5b2_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr bobKyberPtr newBobKyberPtr rootKeyLen : BitVec 64)
    (bobKyberBytes : List (BitVec 8))
    (hnew_nz : newBobKyberPtr ≠ 0#64)
    (hlen_lt : bobKyberBytes.length < 2 ^ 64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1b88#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = newBobKyberPtr)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 bobKyberBytes.length)
    (hx27 : s.readReg64 .x27 = bobKyberPtr) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1bac#64) s
      (((s.sp + 0x98#64) ↦₆₄ rootKeyLen) ∗
       (bobKyberPtr ↦ₛ bobKyberBytes) ∗
       memRegion newBobKyberPtr bobKyberBytes.length)
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x98#64) ↦₆₄ rootKeyLen) ∗
          (bobKyberPtr ↦ₛ bobKyberBytes) ∗
          (newBobKyberPtr ↦ₛ bobKyberBytes)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x21 = newBobKyberPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = BitVec.ofNat 64 bobKyberBytes.length ∧
        s1.readReg64 .x27 = s.readReg64 .x28 ∧
        s1.readReg64 .x28 = rootKeyLen ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg5b2_wp_trap b C abs s
    coroPtr bobKyberPtr newBobKyberPtr rootKeyLen bobKyberBytes
    hnew_nz hlen_lt hpc hrun hsp_align hx0 hx19 hx26 hx27)

/-! ## 7. Substage P3.6 (`+0x1bac -> 0x480b8`, write cloned `SessionState` & call
`try_decrypt_with_state`) -/

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg6_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr remAddrPtr locAddrPtr whisperMsgPtr
    v08 v10 v18 v38 v40 c0 newRootKeyPtr newRemIdPtr remIdLen newLocIdPtr locIdLen
    c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12
    ua90 ua98 uaa0 uaa8 uab0 uab8 uac0 uac8 uad0 uad8 uae0 uae8 uaf0 uaf8
    ub00 ub08 ub10 ub18 ub20 ub28 ub30 ub38 ub40 ub48 ub50 ub58 ub60 ub68
    ub70 ub78 ub80 ub88 ub90 ub98 uba8 ubb8 ubc0 ubc8 : BitVec 64)
    (v24 v28 v2c f248 f24c prevCounter
     uba0 uba4 ubb0 ubd0 ubd8 ubdc ube0 ube4 : BitVec 32)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1bac#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (trTrapProgAt b C abs) (b + (bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))) s
      (((s.sp + 0x8#64) ↦₆₄ v08) ∗ ((s.sp + 0x10#64) ↦₆₄ v10) ∗
       ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp + 0x24#64) ↦₃₂ v24) ∗
       ((s.sp + 0x28#64) ↦₃₂ v28) ∗ ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗
       ((s.sp + 0x30#64) ↦₃₂ f248) ∗ ((s.sp + 0x34#64) ↦₃₂ f24c) ∗
       ((s.sp + 0x38#64) ↦₆₄ v38) ∗ ((s.sp + 0x40#64) ↦₆₄ v40) ∗
       ((s.sp + 0x48#64) ↦₆₄ c0) ∗ ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗
       ((s.sp + 0x5c#64) ↦₃₂ prevCounter) ∗ ((s.sp + 0x60#64) ↦₆₄ newRemIdPtr) ∗
       ((s.sp + 0x68#64) ↦₆₄ remIdLen) ∗ ((s.sp + 0x70#64) ↦₆₄ newLocIdPtr) ∗
       ((s.sp + 0x7c#64) ↦₃₂ 3#32) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
       ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ 3#32) ∗
       ((s.sp + 0xd0#64) ↦₆₄ locIdLen) ∗ ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗
       ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
       ((s.sp + 0x930#64) ↦₆₄ c1) ∗ ((s.sp + 0x938#64) ↦₆₄ c2) ∗
       ((s.sp + 0x940#64) ↦₆₄ c3) ∗ ((s.sp + 0x948#64) ↦₆₄ c4) ∗
       ((s.sp + 0x950#64) ↦₆₄ c5) ∗ ((s.sp + 0x958#64) ↦₆₄ c6) ∗
       ((s.sp + 0x960#64) ↦₆₄ c7) ∗ ((s.sp + 0x968#64) ↦₆₄ c8) ∗
       ((s.sp + 0x970#64) ↦₆₄ c9) ∗ ((s.sp + 0x978#64) ↦₆₄ c10) ∗
       ((s.sp + 0x980#64) ↦₆₄ c11) ∗ ((s.sp + 0x988#64) ↦₆₄ c12) ∗
       ((s.sp + 0xa90#64) ↦₆₄ ua90) ∗ ((s.sp + 0xa98#64) ↦₆₄ ua98) ∗
       ((s.sp + 0xaa0#64) ↦₆₄ uaa0) ∗ ((s.sp + 0xaa8#64) ↦₆₄ uaa8) ∗
       ((s.sp + 0xab0#64) ↦₆₄ uab0) ∗ ((s.sp + 0xab8#64) ↦₆₄ uab8) ∗
       ((s.sp + 0xac0#64) ↦₆₄ uac0) ∗ ((s.sp + 0xac8#64) ↦₆₄ uac8) ∗
       ((s.sp + 0xad0#64) ↦₆₄ uad0) ∗ ((s.sp + 0xad8#64) ↦₆₄ uad8) ∗
       ((s.sp + 0xae0#64) ↦₆₄ uae0) ∗ ((s.sp + 0xae8#64) ↦₆₄ uae8) ∗
       ((s.sp + 0xaf0#64) ↦₆₄ uaf0) ∗ ((s.sp + 0xaf8#64) ↦₆₄ uaf8) ∗
       ((s.sp + 0xb00#64) ↦₆₄ ub00) ∗ ((s.sp + 0xb08#64) ↦₆₄ ub08) ∗
       ((s.sp + 0xb10#64) ↦₆₄ ub10) ∗ ((s.sp + 0xb18#64) ↦₆₄ ub18) ∗
       ((s.sp + 0xb20#64) ↦₆₄ ub20) ∗ ((s.sp + 0xb28#64) ↦₆₄ ub28) ∗
       ((s.sp + 0xb30#64) ↦₆₄ ub30) ∗ ((s.sp + 0xb38#64) ↦₆₄ ub38) ∗
       ((s.sp + 0xb40#64) ↦₆₄ ub40) ∗ ((s.sp + 0xb48#64) ↦₆₄ ub48) ∗
       ((s.sp + 0xb50#64) ↦₆₄ ub50) ∗ ((s.sp + 0xb58#64) ↦₆₄ ub58) ∗
       ((s.sp + 0xb60#64) ↦₆₄ ub60) ∗ ((s.sp + 0xb68#64) ↦₆₄ ub68) ∗
       ((s.sp + 0xb70#64) ↦₆₄ ub70) ∗ ((s.sp + 0xb78#64) ↦₆₄ ub78) ∗
       ((s.sp + 0xb80#64) ↦₆₄ ub80) ∗ ((s.sp + 0xb88#64) ↦₆₄ ub88) ∗
       ((s.sp + 0xb90#64) ↦₆₄ ub90) ∗ ((s.sp + 0xb98#64) ↦₆₄ ub98) ∗
       ((s.sp + 0xba0#64) ↦₃₂ uba0) ∗ ((s.sp + 0xba4#64) ↦₃₂ uba4) ∗
       ((s.sp + 0xba8#64) ↦₆₄ uba8) ∗ ((s.sp + 0xbb0#64) ↦₃₂ ubb0) ∗
       ((s.sp + 0xbb8#64) ↦₆₄ ubb8) ∗ ((s.sp + 0xbc0#64) ↦₆₄ ubc0) ∗ ((s.sp + 0xbc8#64) ↦₆₄ ubc8) ∗
       ((s.sp + 0xbd0#64) ↦₃₂ ubd0) ∗ ((s.sp + 0xbd8#64) ↦₃₂ ubd8) ∗
       ((s.sp + 0xbdc#64) ↦₃₂ ubdc) ∗ ((s.sp + 0xbe0#64) ↦₃₂ ube0) ∗
       ((s.sp + 0xbe4#64) ↦₃₂ ube4))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x8#64) ↦₆₄ v08) ∗ ((s.sp + 0x10#64) ↦₆₄ v10) ∗
          ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp + 0x24#64) ↦₃₂ v24) ∗
          ((s.sp + 0x28#64) ↦₃₂ v28) ∗ ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗
          ((s.sp + 0x30#64) ↦₃₂ f248) ∗ ((s.sp + 0x34#64) ↦₃₂ f24c) ∗
          ((s.sp + 0x38#64) ↦₆₄ v38) ∗ ((s.sp + 0x40#64) ↦₆₄ v40) ∗
          ((s.sp + 0x48#64) ↦₆₄ c0) ∗ ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗
          ((s.sp + 0x5c#64) ↦₃₂ prevCounter) ∗ ((s.sp + 0x60#64) ↦₆₄ newRemIdPtr) ∗
          ((s.sp + 0x68#64) ↦₆₄ remIdLen) ∗ ((s.sp + 0x70#64) ↦₆₄ newLocIdPtr) ∗
          ((s.sp + 0x7c#64) ↦₃₂ 3#32) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
          ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ 3#32) ∗
          ((s.sp + 0xd0#64) ↦₆₄ locIdLen) ∗ ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗
          ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
          ((s.sp + 0x930#64) ↦₆₄ c1) ∗ ((s.sp + 0x938#64) ↦₆₄ c2) ∗
          ((s.sp + 0x940#64) ↦₆₄ c3) ∗ ((s.sp + 0x948#64) ↦₆₄ c4) ∗
          ((s.sp + 0x950#64) ↦₆₄ c5) ∗ ((s.sp + 0x958#64) ↦₆₄ c6) ∗
          ((s.sp + 0x960#64) ↦₆₄ c7) ∗ ((s.sp + 0x968#64) ↦₆₄ c8) ∗
          ((s.sp + 0x970#64) ↦₆₄ c9) ∗ ((s.sp + 0x978#64) ↦₆₄ c10) ∗
          ((s.sp + 0x980#64) ↦₆₄ c11) ∗ ((s.sp + 0x988#64) ↦₆₄ c12) ∗
          ((s.sp + 0xa90#64) ↦₆₄ locIdLen) ∗ ((s.sp + 0xa98#64) ↦₆₄ newLocIdPtr) ∗
          ((s.sp + 0xaa0#64) ↦₆₄ locIdLen) ∗ ((s.sp + 0xaa8#64) ↦₆₄ remIdLen) ∗
          ((s.sp + 0xab0#64) ↦₆₄ newRemIdPtr) ∗ ((s.sp + 0xab8#64) ↦₆₄ remIdLen) ∗
          ((s.sp + 0xac0#64) ↦₆₄ s.readReg64 .x28) ∗ ((s.sp + 0xac8#64) ↦₆₄ newRootKeyPtr) ∗
          ((s.sp + 0xad0#64) ↦₆₄ s.readReg64 .x28) ∗ ((s.sp + 0xad8#64) ↦₆₄ v40) ∗
          ((s.sp + 0xae0#64) ↦₆₄ s.readReg64 .x25) ∗ ((s.sp + 0xae8#64) ↦₆₄ v40) ∗
          ((s.sp + 0xaf0#64) ↦₆₄ s.readReg64 .x24) ∗ ((s.sp + 0xaf8#64) ↦₆₄ s.readReg64 .x23) ∗
          ((s.sp + 0xb00#64) ↦₆₄ s.readReg64 .x24) ∗ ((s.sp + 0xb08#64) ↦₆₄ s.readReg64 .x26) ∗
          ((s.sp + 0xb10#64) ↦₆₄ s.readReg64 .x21) ∗ ((s.sp + 0xb18#64) ↦₆₄ s.readReg64 .x26) ∗
          ((s.sp + 0xb20#64) ↦₆₄ c0) ∗ ((s.sp + 0xb28#64) ↦₆₄ c1) ∗
          ((s.sp + 0xb30#64) ↦₆₄ c2) ∗ ((s.sp + 0xb38#64) ↦₆₄ c3) ∗
          ((s.sp + 0xb40#64) ↦₆₄ c4) ∗ ((s.sp + 0xb48#64) ↦₆₄ c5) ∗
          ((s.sp + 0xb50#64) ↦₆₄ c6) ∗ ((s.sp + 0xb58#64) ↦₆₄ c7) ∗
          ((s.sp + 0xb60#64) ↦₆₄ c8) ∗ ((s.sp + 0xb68#64) ↦₆₄ c9) ∗
          ((s.sp + 0xb70#64) ↦₆₄ c10) ∗ ((s.sp + 0xb78#64) ↦₆₄ c11) ∗
          ((s.sp + 0xb80#64) ↦₆₄ c12) ∗ ((s.sp + 0xb88#64) ↦₆₄ s.readReg64 .x22) ∗
          ((s.sp + 0xb90#64) ↦₆₄ v18) ∗ ((s.sp + 0xb98#64) ↦₆₄ s.readReg64 .x22) ∗
          ((s.sp + 0xba0#64) ↦₃₂ v2c) ∗ ((s.sp + 0xba4#64) ↦₃₂ (s.readReg64 .x20).truncate 32) ∗
          ((s.sp + 0xba8#64) ↦₆₄ v10) ∗ ((s.sp + 0xbb0#64) ↦₃₂ v28) ∗
          ((s.sp + 0xbb8#64) ↦₆₄ v38) ∗ ((s.sp + 0xbc0#64) ↦₆₄ v08) ∗ ((s.sp + 0xbc8#64) ↦₆₄ v38) ∗
          ((s.sp + 0xbd0#64) ↦₃₂ v24) ∗ ((s.sp + 0xbd8#64) ↦₃₂ 3#32) ∗
          ((s.sp + 0xbdc#64) ↦₃₂ prevCounter) ∗ ((s.sp + 0xbe0#64) ↦₃₂ f248) ∗
          ((s.sp + 0xbe4#64) ↦₃₂ f24c)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = s.sp + 0x270#64 ∧
        s1.readReg64 .x1 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x2 = remAddrPtr ∧
        s1.readReg64 .x3 = locAddrPtr ∧
        s1.readReg64 .x4 = whisperMsgPtr ∧
        s1.readReg64 .x5 = 3#64 ∧
        s1.readReg64 .x6 = 0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1cd8#64) := by
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x1bac 0x1cd4
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt] at hpc ⊢
  have hentry : (libsignalSessionCode.rebase b
      (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName =
      b + (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have htarget : (libsignalSessionCode.rebase b
      (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
      0x1cd4#64 + bv% ((2^64 + ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>" - (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7380)) % 2^64) = b + (bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")) := by
    rw [hentry]; bv_omega
  clear hentry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  refine SepWP.done (by rw [← htarget]; simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- Segment P3.6 (`+0x1bac → +0x1cd4`): materializes the 344-byte cloned `SessionState` at
`sp + 0xa90..0xbe8`, checks `session_version == 3`, and calls `try_decrypt_with_state::<Coins>`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg6_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr remAddrPtr locAddrPtr whisperMsgPtr
    v08 v10 v18 v38 v40 c0 newRootKeyPtr newRemIdPtr remIdLen newLocIdPtr locIdLen
    c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12
    ua90 ua98 uaa0 uaa8 uab0 uab8 uac0 uac8 uad0 uad8 uae0 uae8 uaf0 uaf8
    ub00 ub08 ub10 ub18 ub20 ub28 ub30 ub38 ub40 ub48 ub50 ub58 ub60 ub68
    ub70 ub78 ub80 ub88 ub90 ub98 uba8 ubb8 ubc0 ubc8 : BitVec 64)
    (v24 v28 v2c f248 f24c prevCounter
     uba0 uba4 ubb0 ubd0 ubd8 ubdc ube0 ube4 : BitVec 32)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1bac#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAt b C ctl abs) (b + (bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))) s
      (((s.sp + 0x8#64) ↦₆₄ v08) ∗ ((s.sp + 0x10#64) ↦₆₄ v10) ∗
       ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp + 0x24#64) ↦₃₂ v24) ∗
       ((s.sp + 0x28#64) ↦₃₂ v28) ∗ ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗
       ((s.sp + 0x30#64) ↦₃₂ f248) ∗ ((s.sp + 0x34#64) ↦₃₂ f24c) ∗
       ((s.sp + 0x38#64) ↦₆₄ v38) ∗ ((s.sp + 0x40#64) ↦₆₄ v40) ∗
       ((s.sp + 0x48#64) ↦₆₄ c0) ∗ ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗
       ((s.sp + 0x5c#64) ↦₃₂ prevCounter) ∗ ((s.sp + 0x60#64) ↦₆₄ newRemIdPtr) ∗
       ((s.sp + 0x68#64) ↦₆₄ remIdLen) ∗ ((s.sp + 0x70#64) ↦₆₄ newLocIdPtr) ∗
       ((s.sp + 0x7c#64) ↦₃₂ 3#32) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
       ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ 3#32) ∗
       ((s.sp + 0xd0#64) ↦₆₄ locIdLen) ∗ ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗
       ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
       ((s.sp + 0x930#64) ↦₆₄ c1) ∗ ((s.sp + 0x938#64) ↦₆₄ c2) ∗
       ((s.sp + 0x940#64) ↦₆₄ c3) ∗ ((s.sp + 0x948#64) ↦₆₄ c4) ∗
       ((s.sp + 0x950#64) ↦₆₄ c5) ∗ ((s.sp + 0x958#64) ↦₆₄ c6) ∗
       ((s.sp + 0x960#64) ↦₆₄ c7) ∗ ((s.sp + 0x968#64) ↦₆₄ c8) ∗
       ((s.sp + 0x970#64) ↦₆₄ c9) ∗ ((s.sp + 0x978#64) ↦₆₄ c10) ∗
       ((s.sp + 0x980#64) ↦₆₄ c11) ∗ ((s.sp + 0x988#64) ↦₆₄ c12) ∗
       ((s.sp + 0xa90#64) ↦₆₄ ua90) ∗ ((s.sp + 0xa98#64) ↦₆₄ ua98) ∗
       ((s.sp + 0xaa0#64) ↦₆₄ uaa0) ∗ ((s.sp + 0xaa8#64) ↦₆₄ uaa8) ∗
       ((s.sp + 0xab0#64) ↦₆₄ uab0) ∗ ((s.sp + 0xab8#64) ↦₆₄ uab8) ∗
       ((s.sp + 0xac0#64) ↦₆₄ uac0) ∗ ((s.sp + 0xac8#64) ↦₆₄ uac8) ∗
       ((s.sp + 0xad0#64) ↦₆₄ uad0) ∗ ((s.sp + 0xad8#64) ↦₆₄ uad8) ∗
       ((s.sp + 0xae0#64) ↦₆₄ uae0) ∗ ((s.sp + 0xae8#64) ↦₆₄ uae8) ∗
       ((s.sp + 0xaf0#64) ↦₆₄ uaf0) ∗ ((s.sp + 0xaf8#64) ↦₆₄ uaf8) ∗
       ((s.sp + 0xb00#64) ↦₆₄ ub00) ∗ ((s.sp + 0xb08#64) ↦₆₄ ub08) ∗
       ((s.sp + 0xb10#64) ↦₆₄ ub10) ∗ ((s.sp + 0xb18#64) ↦₆₄ ub18) ∗
       ((s.sp + 0xb20#64) ↦₆₄ ub20) ∗ ((s.sp + 0xb28#64) ↦₆₄ ub28) ∗
       ((s.sp + 0xb30#64) ↦₆₄ ub30) ∗ ((s.sp + 0xb38#64) ↦₆₄ ub38) ∗
       ((s.sp + 0xb40#64) ↦₆₄ ub40) ∗ ((s.sp + 0xb48#64) ↦₆₄ ub48) ∗
       ((s.sp + 0xb50#64) ↦₆₄ ub50) ∗ ((s.sp + 0xb58#64) ↦₆₄ ub58) ∗
       ((s.sp + 0xb60#64) ↦₆₄ ub60) ∗ ((s.sp + 0xb68#64) ↦₆₄ ub68) ∗
       ((s.sp + 0xb70#64) ↦₆₄ ub70) ∗ ((s.sp + 0xb78#64) ↦₆₄ ub78) ∗
       ((s.sp + 0xb80#64) ↦₆₄ ub80) ∗ ((s.sp + 0xb88#64) ↦₆₄ ub88) ∗
       ((s.sp + 0xb90#64) ↦₆₄ ub90) ∗ ((s.sp + 0xb98#64) ↦₆₄ ub98) ∗
       ((s.sp + 0xba0#64) ↦₃₂ uba0) ∗ ((s.sp + 0xba4#64) ↦₃₂ uba4) ∗
       ((s.sp + 0xba8#64) ↦₆₄ uba8) ∗ ((s.sp + 0xbb0#64) ↦₃₂ ubb0) ∗
       ((s.sp + 0xbb8#64) ↦₆₄ ubb8) ∗ ((s.sp + 0xbc0#64) ↦₆₄ ubc0) ∗ ((s.sp + 0xbc8#64) ↦₆₄ ubc8) ∗
       ((s.sp + 0xbd0#64) ↦₃₂ ubd0) ∗ ((s.sp + 0xbd8#64) ↦₃₂ ubd8) ∗
       ((s.sp + 0xbdc#64) ↦₃₂ ubdc) ∗ ((s.sp + 0xbe0#64) ↦₃₂ ube0) ∗
       ((s.sp + 0xbe4#64) ↦₃₂ ube4))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x8#64) ↦₆₄ v08) ∗ ((s.sp + 0x10#64) ↦₆₄ v10) ∗
          ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp + 0x24#64) ↦₃₂ v24) ∗
          ((s.sp + 0x28#64) ↦₃₂ v28) ∗ ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗
          ((s.sp + 0x30#64) ↦₃₂ f248) ∗ ((s.sp + 0x34#64) ↦₃₂ f24c) ∗
          ((s.sp + 0x38#64) ↦₆₄ v38) ∗ ((s.sp + 0x40#64) ↦₆₄ v40) ∗
          ((s.sp + 0x48#64) ↦₆₄ c0) ∗ ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗
          ((s.sp + 0x5c#64) ↦₃₂ prevCounter) ∗ ((s.sp + 0x60#64) ↦₆₄ newRemIdPtr) ∗
          ((s.sp + 0x68#64) ↦₆₄ remIdLen) ∗ ((s.sp + 0x70#64) ↦₆₄ newLocIdPtr) ∗
          ((s.sp + 0x7c#64) ↦₃₂ 3#32) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
          ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ 3#32) ∗
          ((s.sp + 0xd0#64) ↦₆₄ locIdLen) ∗ ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗
          ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
          ((s.sp + 0x930#64) ↦₆₄ c1) ∗ ((s.sp + 0x938#64) ↦₆₄ c2) ∗
          ((s.sp + 0x940#64) ↦₆₄ c3) ∗ ((s.sp + 0x948#64) ↦₆₄ c4) ∗
          ((s.sp + 0x950#64) ↦₆₄ c5) ∗ ((s.sp + 0x958#64) ↦₆₄ c6) ∗
          ((s.sp + 0x960#64) ↦₆₄ c7) ∗ ((s.sp + 0x968#64) ↦₆₄ c8) ∗
          ((s.sp + 0x970#64) ↦₆₄ c9) ∗ ((s.sp + 0x978#64) ↦₆₄ c10) ∗
          ((s.sp + 0x980#64) ↦₆₄ c11) ∗ ((s.sp + 0x988#64) ↦₆₄ c12) ∗
          ((s.sp + 0xa90#64) ↦₆₄ locIdLen) ∗ ((s.sp + 0xa98#64) ↦₆₄ newLocIdPtr) ∗
          ((s.sp + 0xaa0#64) ↦₆₄ locIdLen) ∗ ((s.sp + 0xaa8#64) ↦₆₄ remIdLen) ∗
          ((s.sp + 0xab0#64) ↦₆₄ newRemIdPtr) ∗ ((s.sp + 0xab8#64) ↦₆₄ remIdLen) ∗
          ((s.sp + 0xac0#64) ↦₆₄ s.readReg64 .x28) ∗ ((s.sp + 0xac8#64) ↦₆₄ newRootKeyPtr) ∗
          ((s.sp + 0xad0#64) ↦₆₄ s.readReg64 .x28) ∗ ((s.sp + 0xad8#64) ↦₆₄ v40) ∗
          ((s.sp + 0xae0#64) ↦₆₄ s.readReg64 .x25) ∗ ((s.sp + 0xae8#64) ↦₆₄ v40) ∗
          ((s.sp + 0xaf0#64) ↦₆₄ s.readReg64 .x24) ∗ ((s.sp + 0xaf8#64) ↦₆₄ s.readReg64 .x23) ∗
          ((s.sp + 0xb00#64) ↦₆₄ s.readReg64 .x24) ∗ ((s.sp + 0xb08#64) ↦₆₄ s.readReg64 .x26) ∗
          ((s.sp + 0xb10#64) ↦₆₄ s.readReg64 .x21) ∗ ((s.sp + 0xb18#64) ↦₆₄ s.readReg64 .x26) ∗
          ((s.sp + 0xb20#64) ↦₆₄ c0) ∗ ((s.sp + 0xb28#64) ↦₆₄ c1) ∗
          ((s.sp + 0xb30#64) ↦₆₄ c2) ∗ ((s.sp + 0xb38#64) ↦₆₄ c3) ∗
          ((s.sp + 0xb40#64) ↦₆₄ c4) ∗ ((s.sp + 0xb48#64) ↦₆₄ c5) ∗
          ((s.sp + 0xb50#64) ↦₆₄ c6) ∗ ((s.sp + 0xb58#64) ↦₆₄ c7) ∗
          ((s.sp + 0xb60#64) ↦₆₄ c8) ∗ ((s.sp + 0xb68#64) ↦₆₄ c9) ∗
          ((s.sp + 0xb70#64) ↦₆₄ c10) ∗ ((s.sp + 0xb78#64) ↦₆₄ c11) ∗
          ((s.sp + 0xb80#64) ↦₆₄ c12) ∗ ((s.sp + 0xb88#64) ↦₆₄ s.readReg64 .x22) ∗
          ((s.sp + 0xb90#64) ↦₆₄ v18) ∗ ((s.sp + 0xb98#64) ↦₆₄ s.readReg64 .x22) ∗
          ((s.sp + 0xba0#64) ↦₃₂ v2c) ∗ ((s.sp + 0xba4#64) ↦₃₂ (s.readReg64 .x20).truncate 32) ∗
          ((s.sp + 0xba8#64) ↦₆₄ v10) ∗ ((s.sp + 0xbb0#64) ↦₃₂ v28) ∗
          ((s.sp + 0xbb8#64) ↦₆₄ v38) ∗ ((s.sp + 0xbc0#64) ↦₆₄ v08) ∗ ((s.sp + 0xbc8#64) ↦₆₄ v38) ∗
          ((s.sp + 0xbd0#64) ↦₃₂ v24) ∗ ((s.sp + 0xbd8#64) ↦₃₂ 3#32) ∗
          ((s.sp + 0xbdc#64) ↦₃₂ prevCounter) ∗ ((s.sp + 0xbe0#64) ↦₃₂ f248) ∗
          ((s.sp + 0xbe4#64) ↦₃₂ f24c)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = s.sp + 0x270#64 ∧
        s1.readReg64 .x1 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x2 = remAddrPtr ∧
        s1.readReg64 .x3 = locAddrPtr ∧
        s1.readReg64 .x4 = whisperMsgPtr ∧
        s1.readReg64 .x5 = 3#64 ∧
        s1.readReg64 .x6 = 0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1cd8#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg6_wp_trap b C abs s
    coroPtr remAddrPtr locAddrPtr whisperMsgPtr
    v08 v10 v18 v38 v40 c0 newRootKeyPtr newRemIdPtr remIdLen newLocIdPtr locIdLen
    c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12
    ua90 ua98 uaa0 uaa8 uab0 uab8 uac0 uac8 uad0 uad8 uae0 uae8 uaf0 uaf8
    ub00 ub08 ub10 ub18 ub20 ub28 ub30 ub38 ub40 ub48 ub50 ub58 ub60 ub68
    ub70 ub78 ub80 ub88 ub90 ub98 uba8 ubb8 ubc0 ubc8
    v24 v28 v2c f248 f24c prevCounter uba0 uba4 ubb0 ubd0 ubd8 ubdc ube0 ube4
    hpc hrun hsp_align hx19)

/-! ## 8. Substage P3.7 (`+0x1cd8 -> +0x34dc`, post-`try_decrypt_with_state` &
`SessionRecord::set_session_state`) -/

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg7a_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr retPtr : BitVec 64)
    (ssBytes : List (BitVec 8))
    (hb : b &&& 0xfff#64 = 0#64)
    (hss_len : ssBytes.length = 344)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1cd8#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (trTrapProgAt b C abs)
      (b + (bv% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state"))) s
      (((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
       ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
       ((s.sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
       ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
       ((s.sp + 0xa90#64) ↦ₛ ssBytes) ∗
       memRegion (s.sp + 0x3e0#64) 344)
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
          ((s.sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
          ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          ((s.sp + 0xa90#64) ↦ₛ ssBytes) ∗
          ((s.sp + 0x3e0#64) ↦ₛ ssBytes)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x1 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = retPtr ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1dfc#64) := by
  have hmemcpy := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_memcpy_ok_trap (b := b) (C := C)
    (abs := abs)
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x1cd8 0x1cf8
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x1de0 0x1df8
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt] at hmemcpy hpc ⊢
  have hentry : (libsignalSessionCode.rebase b
      (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName =
      b + (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have hadrp0 := (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.adrp_logMaxLevel_0x1cec hb hentry).1
  have hadrp := (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.adrp_logMaxLevel_0x1cec hb hentry).2
  have htarget : (libsignalSessionCode.rebase b
      (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
      0x1df8#64 + bv% ((2^64 + ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state" - (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7672)) % 2^64) = b + (bv% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state")) := by
    rw [hentry]; bv_omega
  clear hentry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hadrp_ws : (b + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256))) + bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096) = b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) := by bv_arith
  wp_steps
  wp_call hmemcpy (s.sp + 0x3e0#64, s.sp + 0xa90#64, ssBytes)
  wp_steps
  refine SepWP.done (by rw [← htarget]; simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- Segment P3.7a (`+0x1cd8 → +0x1df8`): handles `Ok(ptext)`, checks `log::STATIC_MAX_LEVEL = 0`,
copies the updated `SessionState` to `sp + 0x3e0..0x538`, and calls `SessionRecord::set_session_state`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg7a_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr retPtr : BitVec 64)
    (ssBytes : List (BitVec 8))
    (hb : b &&& 0xfff#64 = 0#64)
    (hss_len : ssBytes.length = 344)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1cd8#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAt b C ctl abs) (b + 0x174d4#64) s
      (((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
       ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
       ((s.sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
       ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
       ((s.sp + 0xa90#64) ↦ₛ ssBytes) ∗
       memRegion (s.sp + 0x3e0#64) 344)
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
          ((s.sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
          ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          ((s.sp + 0xa90#64) ↦ₛ ssBytes) ∗
          ((s.sp + 0x3e0#64) ↦ₛ ssBytes)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x1 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = retPtr ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1dfc#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg7a_wp_trap b C abs s
    coroPtr retPtr ssBytes hb hss_len hpc hrun hsp_align hx19)

end CryptoVerification.E2E.Pqxdh.ResponderClosure
