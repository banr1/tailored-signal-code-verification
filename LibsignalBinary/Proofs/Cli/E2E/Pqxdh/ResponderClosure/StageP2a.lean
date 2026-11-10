/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StageP2a
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.StageP1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.WPp

/-!
# Responder Closure Stages P2.1 to P2.4 (`+0x0868 → +0x36a8`)

Symbolic-execution segment proofs for the first half of Stage P2 of the CLI responder prekey
decryption closure, covering `PublicKey::serialize`, `SessionRecord::promote_matching_session`,
signed prekey lookup and reconstruction, Kyber prekey lookup and ML-KEM key-pair reconstruction,
optional one-time prekey lookup, and dispatch to `get_identity_key_pair`.
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

/-! ## 1. Isolated Callee Contracts for Stage P2 -/

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_shim_ok_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + bv% ((2^64 + ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) % 2^64))
      noAllocShimSpec :=
  noAllocShim_ok_at_trap (b := b) (C := C)
    (abs := abs) (name := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName) (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")))

/-- `__rust_no_alloc_shim_is_unstable_v2` (`0x51adc`, `+0x6a10` from `0x4b0cc`) on
`tripleRatchetProgAt`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_shim_ok {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + bv% ((2^64 + ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) % 2^64))
      noAllocShimSpec := by
  rw [← trTrapProgAt_fnAddr_eq b C ctl abs]
  exact subroutine_ok_kit_of_trTrap
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_shim_ok_trap

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_alloc_ok_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + bv% ((2^64 + ls_off% "__rustc::__rust_alloc" - (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) % 2^64))
      (rustAllocSpec A) :=
  alloc_ok_at_norm_ext (AllocContracts.of_tripleRatchetProgAt_trap b C A abs hA)
    (name := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName) (k := num% (ls_off% "__rustc::__rust_alloc" - (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")))

/-- `__rust_alloc` (`0x51ae0`, `+0x6a14` from `0x4b0cc`) on `tripleRatchetProgAt`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_alloc_ok {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + bv% ((2^64 + ls_off% "__rustc::__rust_alloc" - (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) % 2^64))
      (rustAllocSpec A) := by
  rw [← trTrapProgAt_fnAddr_eq b C ctl abs]
  exact subroutine_ok_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_alloc_ok_trap hA)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.adrp_missingKyber_0xd0c {b entry : BitVec 64}
    (hb : b &&& 0xfff#64 = 0#64) (he : entry = b + (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}"))) :
    (((entry + 0xd0c#64) &&& 18446744073709547520#64) + bv% (page% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3340) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3344)) - (page% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3340))) = b + bv% (page% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3340) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3344)))) ∧
    ((((entry + 0xd0c#64) &&& 18446744073709547520#64) + bv% (page% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3340) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3344)) - (page% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3340)))) + bv% ((ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3340) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3344)) % 4096) =
      b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3340) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3344))) := by
  refine ⟨?_, ?_⟩
  · rw [he, BitVec.add_assoc, ProofLib.adrp_page_of_aligned hb, BitVec.add_assoc]; rfl
  · rw [he, BitVec.add_assoc b, ProofLib.adrp_page_of_aligned hb, BitVec.add_assoc b,
        BitVec.add_assoc b]
    rfl

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.adrp_logLevel_0xd64 {b entry : BitVec 64}
    (hb : b &&& 0xfff#64 = 0#64) (he : entry = b + (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}"))) :
    (((entry + 0xd64#64) &&& 18446744073709547520#64) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - (page% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3428))) = b + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256))) ∧
    ((((entry + 0xd64#64) &&& 18446744073709547520#64) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - (page% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3428)))) + bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096) =
      b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) := by
  refine ⟨?_, ?_⟩
  · rw [he, BitVec.add_assoc, ProofLib.adrp_page_of_aligned hb, BitVec.add_assoc]; rfl
  · rw [he, BitVec.add_assoc b, ProofLib.adrp_page_of_aligned hb, BitVec.add_assoc b,
        BitVec.add_assoc b]
    rfl

/-! ## 2. Stage P2.1–P2.3 Segment Proofs (`+0x0868 → +0x0d58`) -/

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg1a_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt : BitVec 64)
    (b_4f1 : BitVec 8)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x868#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = kyberStorePtr)
    (hx9 : s.readReg64 .x9 = msgPtr)
    (hx10 : s.readReg64 .x10 = kyberStoreVt)
    (hx11 : s.readReg64 .x11 = preKeyStorePtr)
    (hx12 : s.readReg64 .x12 = remoteAddrPtr)
    (hx13 : s.readReg64 .x13 = preKeyStoreVt)
    (hx14 : s.readReg64 .x14 = localAddrPtr)
    (hx15 : s.readReg64 .x15 = idStorePtr)
    (hx16 : s.readReg64 .x16 = idStoreVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = spkStorePtr)
    (hx23 : s.readReg64 .x23 = coroPtr + 0xe0#64)
    (hx24 : s.readReg64 .x24 = spkStoreVt) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + bv% ((2^64 + ls_off% "<libsignal_core::curve::PublicKey>::serialize" - ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64)) s
      (cells (coroPtr + 0x3f8#64) 6 ∗
       cells (coroPtr + 0x468#64) 4 ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       ((msgPtr + 0xf0#64) ↦₈ 4#8))
      (fun s1 P_f =>
        (P_f ⊢
          processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
            idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
            kyberStorePtr kyberStoreVt ∗
          ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
          ((msgPtr + 0xf0#64) ↦₈ 4#8)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = msgPtr + 0xa8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x22 = spkStorePtr ∧
        s1.readReg64 .x23 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x24 = spkStoreVt ∧
        s1.readReg64 .x25 = 4#64 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x8a0#64) := by
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x868 0x89c
  dsimp only [trTrapProgAt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx8' : s.readReg64 (Reg.gpr 8#5) = kyberStorePtr := hx8
  have hx9' : s.readReg64 (Reg.gpr 9#5) = msgPtr := hx9
  have hx10' : s.readReg64 (Reg.gpr 10#5) = kyberStoreVt := hx10
  have hx11' : s.readReg64 (Reg.gpr 11#5) = preKeyStorePtr := hx11
  have hx12' : s.readReg64 (Reg.gpr 12#5) = remoteAddrPtr := hx12
  have hx13' : s.readReg64 (Reg.gpr 13#5) = preKeyStoreVt := hx13
  have hx14' : s.readReg64 (Reg.gpr 14#5) = localAddrPtr := hx14
  have hx15' : s.readReg64 (Reg.gpr 15#5) = idStorePtr := hx15
  have hx16' : s.readReg64 (Reg.gpr 16#5) = idStoreVt := hx16
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = spkStorePtr := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = coroPtr + 0xe0#64 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = spkStoreVt := hx24
  conv =>
    arg 4
    simp (config := { maxSteps := 1000000 }) only [
      cells, BitVec.add_assoc, BitVec.reduceAdd,
      sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat (refine SepWP.exists_elim fun _ => ?_)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨?_, rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩
  dsimp only [processPrekeyActive10At]
  exact Entails.of_eq (by ac_rfl)

/-- Segment P2.1a (`+0x0868 → +0x089c`): initializes `process_prekey_impl` words at
`coroPtr + 0x3f8..0x488` and calls `PublicKey::serialize` on `message.base_key`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg1a_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt : BitVec 64)
    (b_4f1 : BitVec 8)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x868#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = kyberStorePtr)
    (hx9 : s.readReg64 .x9 = msgPtr)
    (hx10 : s.readReg64 .x10 = kyberStoreVt)
    (hx11 : s.readReg64 .x11 = preKeyStorePtr)
    (hx12 : s.readReg64 .x12 = remoteAddrPtr)
    (hx13 : s.readReg64 .x13 = preKeyStoreVt)
    (hx14 : s.readReg64 .x14 = localAddrPtr)
    (hx15 : s.readReg64 .x15 = idStorePtr)
    (hx16 : s.readReg64 .x16 = idStoreVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = spkStorePtr)
    (hx23 : s.readReg64 .x23 = coroPtr + 0xe0#64)
    (hx24 : s.readReg64 .x24 = spkStoreVt) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + bv% ((2^64 + ls_off% "<libsignal_core::curve::PublicKey>::serialize" - ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64)) s
      (cells (coroPtr + 0x3f8#64) 6 ∗
       cells (coroPtr + 0x468#64) 4 ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       ((msgPtr + 0xf0#64) ↦₈ 4#8))
      (fun s1 P_f =>
        (P_f ⊢
          processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
            idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
            kyberStorePtr kyberStoreVt ∗
          ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
          ((msgPtr + 0xf0#64) ↦₈ 4#8)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = msgPtr + 0xa8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x22 = spkStorePtr ∧
        s1.readReg64 .x23 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x24 = spkStoreVt ∧
        s1.readReg64 .x25 = 4#64 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x8a0#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg1a_wp_trap b C abs s coroPtr msgPtr
      remoteAddrPtr localAddrPtr idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt spkStorePtr
      spkStoreVt kyberStorePtr kyberStoreVt b_4f1 hpc hrun hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15
      hx16 hx19 hx22 hx23 hx24)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg1b_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr serPtr spkStorePtr spkStoreVt : BitVec 64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x8a0#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = serPtr)
    (hx1 : s.readReg64 .x1 = 33#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = spkStorePtr)
    (hx23 : s.readReg64 .x23 = coroPtr + 0xe0#64)
    (hx24 : s.readReg64 .x24 = spkStoreVt)
    (hx25 : s.readReg64 .x25 = 4#64) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + bv% ((2^64 + ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session" - ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64)) s
      emp
      (fun s1 P_f =>
        (P_f ⊢ emp) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x1 = 4#64 ∧
        s1.readReg64 .x2 = serPtr ∧
        s1.readReg64 .x3 = 33#64 ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = serPtr ∧
        s1.readReg64 .x22 = spkStorePtr ∧
        s1.readReg64 .x23 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x24 = spkStoreVt ∧
        s1.readReg64 .x25 = 4#64 ∧
        s1.readReg64 .x26 = 33#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x8c0#64) := by
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x8a0 0x8bc
  dsimp only [trTrapProgAt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx0' : s.readReg64 (Reg.gpr 0#5) = serPtr := hx0
  have hx1' : s.readReg64 (Reg.gpr 1#5) = 33#64 := hx1
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = spkStorePtr := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = coroPtr + 0xe0#64 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = spkStoreVt := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = 4#64 := hx25
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.refl _, rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

/-- Segment P2.1b (`+0x08a0 → +0x08bc`): calls `SessionRecord::promote_matching_session` with the
serialized 33-byte base key. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg1b_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr serPtr spkStorePtr spkStoreVt : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x8a0#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = serPtr)
    (hx1 : s.readReg64 .x1 = 33#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = spkStorePtr)
    (hx23 : s.readReg64 .x23 = coroPtr + 0xe0#64)
    (hx24 : s.readReg64 .x24 = spkStoreVt)
    (hx25 : s.readReg64 .x25 = 4#64) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + bv% ((2^64 + ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session" - ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64)) s
      emp
      (fun s1 P_f =>
        (P_f ⊢ emp) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x1 = 4#64 ∧
        s1.readReg64 .x2 = serPtr ∧
        s1.readReg64 .x3 = 33#64 ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = serPtr ∧
        s1.readReg64 .x22 = spkStorePtr ∧
        s1.readReg64 .x23 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x24 = spkStoreVt ∧
        s1.readReg64 .x25 = 4#64 ∧
        s1.readReg64 .x26 = 33#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x8c0#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg1b_wp_trap b C abs s coroPtr serPtr
      spkStorePtr spkStoreVt hpc hrun hx0 hx1 hx19 hx22 hx23 hx24 hx25)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg1c_wp_trap {A : RustAlloc} (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s : State) (coroPtr msgPtr serPtr spkStorePtr spkStoreVt spkLoadShimAddr : BitVec 64)
    (spkId : BitVec 32)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x8c0#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = serPtr)
    (hx22 : s.readReg64 .x22 = spkStorePtr)
    (hx24 : s.readReg64 .x24 = spkStoreVt)
    (hx26 : s.readReg64 .x26 = 33#64) :
    SepWP (trTrapProgAt b C abs) spkLoadShimAddr s
      (((s.sp + 0x3e0#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3e8#64) ↦₈ 0#8) ∗
       A.live serPtr 33 1 ∗
       memRegion serPtr 33 ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((msgPtr + 0xec#64) ↦₃₂ spkId) ∗
       ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
       ((spkStoreVt + 0x18#64) ↦₆₄ᵣ spkLoadShimAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3e0#64) ↦₆₄ 0#64) ∗
          ((s.sp + 0x3e8#64) ↦₈ 0#8) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
          ((msgPtr + 0xec#64) ↦₃₂ spkId) ∗
          ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
          ((spkStoreVt + 0x18#64) ↦₆₄ᵣ spkLoadShimAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = spkStorePtr ∧
        s1.readReg64 .x1 = spkId.zeroExtend 64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = serPtr ∧
        s1.readReg64 .x22 = spkStorePtr ∧
        s1.readReg64 .x23 = 0#64 ∧
        s1.readReg64 .x24 = spkStoreVt ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = 33#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xf14#64) := by
  have hdealloc := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_dealloc_ok_trap (b := b) (C := C)
    (abs := abs) hA
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x8c0 0x8c4
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x910 0x914
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0xa08 0xa2c
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0xf04 0xf10
  dsimp only [trTrapProgAt] at hdealloc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = serPtr := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = spkStorePtr := hx22
  have hx24' : s.readReg64 (Reg.gpr 24#5) = spkStoreVt := hx24
  have hx26' : s.readReg64 (Reg.gpr 26#5) = 33#64 := hx26
  wp_steps
  wp_call hdealloc (serPtr, 33, 1)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

/-- Segment P2.1c (`+0x08c0 → +0x0f10`): handles `Ok(false)` from `promote_matching_session`,
deallocates `serPtr`, checks version `4`, and invokes `get_signed_pre_key` (`blr x8`). -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg1c_wp {A : RustAlloc} (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s : State) (coroPtr msgPtr serPtr spkStorePtr spkStoreVt spkLoadShimAddr : BitVec 64)
    (spkId : BitVec 32)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x8c0#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = serPtr)
    (hx22 : s.readReg64 .x22 = spkStorePtr)
    (hx24 : s.readReg64 .x24 = spkStoreVt)
    (hx26 : s.readReg64 .x26 = 33#64) :
    SepWP (tripleRatchetProgAt b C ctl abs) spkLoadShimAddr s
      (((s.sp + 0x3e0#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3e8#64) ↦₈ 0#8) ∗
       A.live serPtr 33 1 ∗
       memRegion serPtr 33 ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((msgPtr + 0xec#64) ↦₃₂ spkId) ∗
       ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
       ((spkStoreVt + 0x18#64) ↦₆₄ᵣ spkLoadShimAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3e0#64) ↦₆₄ 0#64) ∗
          ((s.sp + 0x3e8#64) ↦₈ 0#8) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
          ((msgPtr + 0xec#64) ↦₃₂ spkId) ∗
          ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
          ((spkStoreVt + 0x18#64) ↦₆₄ᵣ spkLoadShimAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = spkStorePtr ∧
        s1.readReg64 .x1 = spkId.zeroExtend 64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = serPtr ∧
        s1.readReg64 .x22 = spkStorePtr ∧
        s1.readReg64 .x23 = 0#64 ∧
        s1.readReg64 .x24 = spkStoreVt ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = 33#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xf14#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg1c_wp_trap b C abs hA s coroPtr
      msgPtr serPtr spkStorePtr spkStoreVt spkLoadShimAddr spkId hpc hrun hsp_align
      hx19 hx21 hx22 hx24 hx26)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg2a_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr ctxPtr spkFutPtr spkFutVt spkPollAddr
    v_98 v_a0 v_b0 u_4f8 u_500 : BitVec 64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xf14#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = spkFutPtr)
    (hx1 : s.readReg64 .x1 = spkFutVt)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (trTrapProgAt b C abs) spkPollAddr s
      (((s.sp + 0x98#64) ↦₆₄ v_98) ∗
       ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
       ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ u_4f8) ∗
       ((coroPtr + 0x500#64) ↦₆₄ u_500) ∗
       ((spkFutVt + 0x18#64) ↦₆₄ᵣ spkPollAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
          ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
          ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ spkFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ spkFutVt) ∗
          ((spkFutVt + 0x18#64) ↦₆₄ᵣ spkPollAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = spkFutPtr ∧
        s1.readReg64 .x1 = ctxPtr ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = v_b0 ∧
        s1.readReg64 .x23 = v_a0 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = v_98 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xf38#64) := by
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0xf14 0xf34
  dsimp only [trTrapProgAt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx0' : s.readReg64 (Reg.gpr 0#5) = spkFutPtr := hx0
  have hx1' : s.readReg64 (Reg.gpr 1#5) = spkFutVt := hx1
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- Segment P2.2a (`+0x0f14 → +0x0f34`): stores `(spkFutPtr, spkFutVt)` at `coroPtr + 0x4f8..0x500`
and polls `get_signed_pre_key` (`blr x9`). -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg2a_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr ctxPtr spkFutPtr spkFutVt spkPollAddr
    v_98 v_a0 v_b0 u_4f8 u_500 : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xf14#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = spkFutPtr)
    (hx1 : s.readReg64 .x1 = spkFutVt)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAt b C ctl abs) spkPollAddr s
      (((s.sp + 0x98#64) ↦₆₄ v_98) ∗
       ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
       ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ u_4f8) ∗
       ((coroPtr + 0x500#64) ↦₆₄ u_500) ∗
       ((spkFutVt + 0x18#64) ↦₆₄ᵣ spkPollAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
          ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
          ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ spkFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ spkFutVt) ∗
          ((spkFutVt + 0x18#64) ↦₆₄ᵣ spkPollAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = spkFutPtr ∧
        s1.readReg64 .x1 = ctxPtr ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = v_b0 ∧
        s1.readReg64 .x23 = v_a0 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = v_98 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xf38#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg2a_wp_trap b C abs s coroPtr ctxPtr
      spkFutPtr spkFutVt spkPollAddr v_98 v_a0 v_b0 u_4f8 u_500 hpc hrun hsp_align hx0 hx1 hx19)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg2b_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr spkFutPtr spkFutVt spkDropAddr
    spkPubPtr spkPrivCap spkPrivPtr spkSigCap spkSigPtr
    v_98 v_a0 v_b0 u_90 u_98 u_a0 u_b0 u_b8 u_d0 : BitVec 64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xf38#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hdrop_nz : spkDropAddr ≠ 0#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = v_a0)
    (hx26 : s.readReg64 .x26 = v_98) :
    SepWP (trTrapProgAt b C abs) spkDropAddr s
      (preKeyRecordOut64At (s.sp + 0x3e0#64)
         33#64 spkPubPtr 33#64 spkPrivCap spkPrivPtr 32#64 spkSigCap spkSigPtr ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ spkFutPtr) ∗
       ((coroPtr + 0x500#64) ↦₆₄ spkFutVt) ∗
       ((spkFutVt + 0x0#64) ↦₆₄ᵣ spkDropAddr) ∗
       ((s.sp + 0x90#64) ↦₆₄ u_90) ∗
       ((s.sp + 0x98#64) ↦₆₄ u_98) ∗
       ((s.sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((s.sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0))
      (fun s1 P_f =>
        (P_f ⊢
          preKeyRecordOut64At (s.sp + 0x3e0#64)
            33#64 spkPubPtr 33#64 spkPrivCap spkPrivPtr 32#64 spkSigCap spkSigPtr ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ spkFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ spkFutVt) ∗
          ((spkFutVt + 0x0#64) ↦₆₄ᵣ spkDropAddr) ∗
          ((s.sp + 0x90#64) ↦₆₄ spkSigCap) ∗
          ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
          ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
          ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((s.sp + 0xb8#64) ↦₆₄ spkPrivCap) ∗
          ((s.sp + 0xd0#64) ↦₆₄ spkPrivPtr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = spkFutPtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = spkSigPtr ∧
        s1.readReg64 .x21 = spkFutPtr ∧
        s1.readReg64 .x22 = spkPubPtr ∧
        s1.readReg64 .x23 = 33#64 ∧
        s1.readReg64 .x24 = spkFutVt ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = 32#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 33#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xf98#64) := by
  have hdrop_beq : (spkDropAddr == 0#64) = false := beq_eq_false_iff_ne.mpr hdrop_nz
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0xf38 0xf40
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0xf54 0xf94
  dsimp only [trTrapProgAt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = v_b0 := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = v_a0 := hx23
  have hx26' : s.readReg64 (Reg.gpr 26#5) = v_98 := hx26
  dsimp only [preKeyRecordOut64At]
  conv =>
    arg 4
    simp (config := { maxSteps := 1000000 }) only [
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨?_, rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

/-- Segment P2.2b (`+0x0f38 → +0x0f94`): reads `SignedPreKeyRecord` from `sp + 0x3e0..0x420` and
invokes `spkDropAddr` (`blr x8`). -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg2b_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr spkFutPtr spkFutVt spkDropAddr
    spkPubPtr spkPrivCap spkPrivPtr spkSigCap spkSigPtr
    v_98 v_a0 v_b0 u_90 u_98 u_a0 u_b0 u_b8 u_d0 : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xf38#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hdrop_nz : spkDropAddr ≠ 0#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = v_a0)
    (hx26 : s.readReg64 .x26 = v_98) :
    SepWP (tripleRatchetProgAt b C ctl abs) spkDropAddr s
      (preKeyRecordOut64At (s.sp + 0x3e0#64)
         33#64 spkPubPtr 33#64 spkPrivCap spkPrivPtr 32#64 spkSigCap spkSigPtr ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ spkFutPtr) ∗
       ((coroPtr + 0x500#64) ↦₆₄ spkFutVt) ∗
       ((spkFutVt + 0x0#64) ↦₆₄ᵣ spkDropAddr) ∗
       ((s.sp + 0x90#64) ↦₆₄ u_90) ∗
       ((s.sp + 0x98#64) ↦₆₄ u_98) ∗
       ((s.sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((s.sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0))
      (fun s1 P_f =>
        (P_f ⊢
          preKeyRecordOut64At (s.sp + 0x3e0#64)
            33#64 spkPubPtr 33#64 spkPrivCap spkPrivPtr 32#64 spkSigCap spkSigPtr ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ spkFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ spkFutVt) ∗
          ((spkFutVt + 0x0#64) ↦₆₄ᵣ spkDropAddr) ∗
          ((s.sp + 0x90#64) ↦₆₄ spkSigCap) ∗
          ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
          ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
          ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((s.sp + 0xb8#64) ↦₆₄ spkPrivCap) ∗
          ((s.sp + 0xd0#64) ↦₆₄ spkPrivPtr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = spkFutPtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = spkSigPtr ∧
        s1.readReg64 .x21 = spkFutPtr ∧
        s1.readReg64 .x22 = spkPubPtr ∧
        s1.readReg64 .x23 = 33#64 ∧
        s1.readReg64 .x24 = spkFutVt ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = 32#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 33#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xf98#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg2b_wp_trap b C abs s coroPtr
      spkFutPtr spkFutVt spkDropAddr spkPubPtr spkPrivCap spkPrivPtr spkSigCap spkSigPtr
      v_98 v_a0 v_b0 u_90 u_98 u_a0 u_b0 u_b8 u_d0 hpc hrun hsp_align hdrop_nz
      hx19 hx21 hx23 hx26)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg2c_wp_trap {A : RustAlloc} (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s : State) (coroPtr spkFutPtr spkFutVt spkPubPtr spkPrivPtr spkSigPtr : BitVec 64)
    (spkBoxSize : Nat)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xf98#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hbs_nz : BitVec.ofNat 64 spkBoxSize ≠ 0#64)
    (hbs_lt : spkBoxSize < 2 ^ 64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = spkSigPtr)
    (hx21 : s.readReg64 .x21 = spkFutPtr)
    (hx22 : s.readReg64 .x22 = spkPubPtr)
    (hx23 : s.readReg64 .x23 = 33#64)
    (hx24 : s.readReg64 .x24 = spkFutVt)
    (hx26 : s.readReg64 .x26 = 32#64)
    (hx28 : s.readReg64 .x28 = 33#64) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + bv% ((2^64 + ls_off% "<libsignal_core::curve::KeyPair as libsignal_protocol::state::signed_prekey::KeyPairSerde>::from_public_and_private" - ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64)) s
      (((spkFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 spkBoxSize) ∗
       ((spkFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.live spkFutPtr spkBoxSize 8 ∗
       memRegion spkFutPtr spkBoxSize ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       ((s.sp + 0xd0#64) ↦₆₄ spkPrivPtr))
      (fun s1 P_f =>
        (P_f ⊢
          ((spkFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 spkBoxSize) ∗
          ((spkFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          ((s.sp + 0xd0#64) ↦₆₄ spkPrivPtr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = spkPubPtr ∧
        s1.readReg64 .x1 = 33#64 ∧
        s1.readReg64 .x2 = spkPrivPtr ∧
        s1.readReg64 .x3 = 32#64 ∧
        s1.readReg64 .x8 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = spkSigPtr ∧
        s1.readReg64 .x22 = spkPubPtr ∧
        s1.readReg64 .x23 = 33#64 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = 32#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 33#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xfcc#64) := by
  have hdealloc := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_dealloc_ok_trap (b := b) (C := C)
    (abs := abs) hA
  have hbs_beq : (BitVec.ofNat 64 spkBoxSize == 0#64) = false := beq_eq_false_iff_ne.mpr hbs_nz
  have hbs_toNat : (BitVec.ofNat 64 spkBoxSize).toNat = spkBoxSize := Nat.mod_eq_of_lt hbs_lt
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0xf98 0xfc8
  dsimp only [trTrapProgAt] at hdealloc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = spkSigPtr := hx20
  have hx21' : s.readReg64 (Reg.gpr 21#5) = spkFutPtr := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = spkPubPtr := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = 33#64 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = spkFutVt := hx24
  have hx26' : s.readReg64 (Reg.gpr 26#5) = 32#64 := hx26
  have hx28' : s.readReg64 (Reg.gpr 28#5) = 33#64 := hx28
  wp_steps
  wp_call hdealloc (spkFutPtr, spkBoxSize, 8)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- Segment P2.2c (`+0x0f98 → +0x0fc8`): deallocates `spkFutPtr` and calls
`KeyPair::from_public_and_private` on the signed prekey buffers. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg2c_wp {A : RustAlloc} (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s : State) (coroPtr spkFutPtr spkFutVt spkPubPtr spkPrivPtr spkSigPtr : BitVec 64)
    (spkBoxSize : Nat)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xf98#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hbs_nz : BitVec.ofNat 64 spkBoxSize ≠ 0#64)
    (hbs_lt : spkBoxSize < 2 ^ 64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = spkSigPtr)
    (hx21 : s.readReg64 .x21 = spkFutPtr)
    (hx22 : s.readReg64 .x22 = spkPubPtr)
    (hx23 : s.readReg64 .x23 = 33#64)
    (hx24 : s.readReg64 .x24 = spkFutVt)
    (hx26 : s.readReg64 .x26 = 32#64)
    (hx28 : s.readReg64 .x28 = 33#64) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + bv% ((2^64 + ls_off% "<libsignal_core::curve::KeyPair as libsignal_protocol::state::signed_prekey::KeyPairSerde>::from_public_and_private" - ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64)) s
      (((spkFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 spkBoxSize) ∗
       ((spkFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.live spkFutPtr spkBoxSize 8 ∗
       memRegion spkFutPtr spkBoxSize ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       ((s.sp + 0xd0#64) ↦₆₄ spkPrivPtr))
      (fun s1 P_f =>
        (P_f ⊢
          ((spkFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 spkBoxSize) ∗
          ((spkFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          ((s.sp + 0xd0#64) ↦₆₄ spkPrivPtr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = spkPubPtr ∧
        s1.readReg64 .x1 = 33#64 ∧
        s1.readReg64 .x2 = spkPrivPtr ∧
        s1.readReg64 .x3 = 32#64 ∧
        s1.readReg64 .x8 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = spkSigPtr ∧
        s1.readReg64 .x22 = spkPubPtr ∧
        s1.readReg64 .x23 = 33#64 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = 32#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 33#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xfcc#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg2c_wp_trap b C abs hA s coroPtr
      spkFutPtr spkFutVt spkPubPtr spkPrivPtr spkSigPtr spkBoxSize hpc hrun hsp_align hbs_nz hbs_lt
      hx19 hx20 hx21 hx22 hx23 hx24 hx26 hx28)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg2d_wp_trap {A : RustAlloc} (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s : State) (coroPtr msgPtr spkPubPtr spkPrivPtr spkSigPtr
    kyberCtCap kyberStorePtr kyberStoreVt kyberLoadShimAddr
    v_a0 v_b0 u_3e0 : BitVec 64)
    (kyberPreKeyId : BitVec 32)
    (b0 b1 b2 b3 b4 b5 b6 b63
     s0 s1_b s2 s3 s4 s5 s6
     c0 c1 c2 c3 c4 c5 c6 c63 b_3e8 : BitVec 8)
    (w0 w1 w2 w3 w4 w5 w6
     cw0 cw1 cw2 cw3 cw4 cw5 cw6 : BitVec 64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xfcc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hkyber_nz : kyberCtCap ≠ 0#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = spkSigPtr)
    (hx22 : s.readReg64 .x22 = spkPubPtr)
    (hx28 : s.readReg64 .x28 = 33#64) :
    SepWP (trTrapProgAt b C abs) kyberLoadShimAddr s
      (((s.sp + 0xa90#64) ↦₈ 0#8) ∗
       keyPair64UnalignedAt (s.sp + 0xa91#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
       bytes7At (s.sp + 0x930#64) s0 s1_b s2 s3 s4 s5 s6 ∗
       keyPair64UnalignedAt
         (coroPtr + 0x398#64) c0 c1 c2 c3 c4 c5 c6 cw0 cw1 cw2 cw3 cw4 cw5 cw6 c63 ∗
       ((s.sp + 0x90#64) ↦₆₄ 64#64) ∗
       ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
       ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ 32#64) ∗
       ((s.sp + 0xd0#64) ↦₆₄ spkPrivPtr) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ u_3e0) ∗
       ((s.sp + 0x3e8#64) ↦₈ b_3e8) ∗
       A.live spkPubPtr 33 1 ∗ memRegion spkPubPtr 33 ∗
       A.live spkPrivPtr 32 1 ∗ memRegion spkPrivPtr 32 ∗
       A.live spkSigPtr 64 1 ∗ memRegion spkSigPtr 64 ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗
       ((coroPtr + 0x400#64) ↦₆₄ kyberStoreVt) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
       ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
       ((kyberStoreVt + 0x18#64) ↦₆₄ᵣ kyberLoadShimAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0xa90#64) ↦₈ 0#8) ∗
          keyPair64UnalignedAt (s.sp + 0xa91#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
          bytes7At (s.sp + 0x930#64) b0 b1 b2 b3 b4 b5 b6 ∗
          keyPair64UnalignedAt (coroPtr + 0x398#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
          ((s.sp + 0x90#64) ↦₆₄ 64#64) ∗
          ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
          ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((s.sp + 0xb8#64) ↦₆₄ 32#64) ∗
          ((s.sp + 0xd0#64) ↦₆₄ spkPrivPtr) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ w6) ∗
          ((s.sp + 0x3e8#64) ↦₈ b63) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗
          ((coroPtr + 0x400#64) ↦₆₄ kyberStoreVt) ∗
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
          ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
          ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
          ((kyberStoreVt + 0x18#64) ↦₆₄ᵣ kyberLoadShimAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = kyberStorePtr ∧
        s1.readReg64 .x1 = kyberPreKeyId.zeroExtend 64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = spkSigPtr ∧
        s1.readReg64 .x21 = v_b0 ∧
        s1.readReg64 .x22 = spkPubPtr ∧
        s1.readReg64 .x23 = v_a0 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = coroPtr + 0x398#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1460#64) := by
  have hdealloc := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_dealloc_ok_trap (b := b) (C := C)
    (abs := abs) hA
  have hkyber_beq : (kyberCtCap == 0#64) = false := beq_eq_false_iff_ne.mpr hkyber_nz
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0xfcc 0xfd4
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x138c 0x145c
  dsimp only [trTrapProgAt] at hdealloc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = spkSigPtr := hx20
  have hx22' : s.readReg64 (Reg.gpr 22#5) = spkPubPtr := hx22
  have hx28' : s.readReg64 (Reg.gpr 28#5) = 33#64 := hx28
  dsimp only [keyPair64UnalignedAt, bytes7At]
  conv =>
    arg 4
    simp (config := { maxSteps := 1000000 }) only [
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  wp_call hdealloc (spkPubPtr, 33, 1)
  wp_steps
  wp_call hdealloc (spkPrivPtr, 32, 1)
  wp_steps
  rw [hsp_sf]
  wp_call hdealloc (spkSigPtr, 64, 1)
  wp_steps
  rw [hsp_sf_1, hsp_sf]
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨?_, by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

/-- Segment P2.2d (`+0x0fcc → +0x145c`): stores the 64-byte SPK `KeyPair`, deallocates SPK record
buffers, checks `kyberCtCap ≠ 0`, and invokes `get_kyber_pre_key` (`blr x8`). -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg2d_wp {A : RustAlloc} (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s : State) (coroPtr msgPtr spkPubPtr spkPrivPtr spkSigPtr
    kyberCtCap kyberStorePtr kyberStoreVt kyberLoadShimAddr
    v_a0 v_b0 u_3e0 : BitVec 64)
    (kyberPreKeyId : BitVec 32)
    (b0 b1 b2 b3 b4 b5 b6 b63
     s0 s1_b s2 s3 s4 s5 s6
     c0 c1 c2 c3 c4 c5 c6 c63 b_3e8 : BitVec 8)
    (w0 w1 w2 w3 w4 w5 w6
     cw0 cw1 cw2 cw3 cw4 cw5 cw6 : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xfcc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hkyber_nz : kyberCtCap ≠ 0#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = spkSigPtr)
    (hx22 : s.readReg64 .x22 = spkPubPtr)
    (hx28 : s.readReg64 .x28 = 33#64) :
    SepWP (tripleRatchetProgAt b C ctl abs) kyberLoadShimAddr s
      (((s.sp + 0xa90#64) ↦₈ 0#8) ∗
       keyPair64UnalignedAt (s.sp + 0xa91#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
       bytes7At (s.sp + 0x930#64) s0 s1_b s2 s3 s4 s5 s6 ∗
       keyPair64UnalignedAt
         (coroPtr + 0x398#64) c0 c1 c2 c3 c4 c5 c6 cw0 cw1 cw2 cw3 cw4 cw5 cw6 c63 ∗
       ((s.sp + 0x90#64) ↦₆₄ 64#64) ∗
       ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
       ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ 32#64) ∗
       ((s.sp + 0xd0#64) ↦₆₄ spkPrivPtr) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ u_3e0) ∗
       ((s.sp + 0x3e8#64) ↦₈ b_3e8) ∗
       A.live spkPubPtr 33 1 ∗ memRegion spkPubPtr 33 ∗
       A.live spkPrivPtr 32 1 ∗ memRegion spkPrivPtr 32 ∗
       A.live spkSigPtr 64 1 ∗ memRegion spkSigPtr 64 ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗
       ((coroPtr + 0x400#64) ↦₆₄ kyberStoreVt) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
       ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
       ((kyberStoreVt + 0x18#64) ↦₆₄ᵣ kyberLoadShimAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0xa90#64) ↦₈ 0#8) ∗
          keyPair64UnalignedAt (s.sp + 0xa91#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
          bytes7At (s.sp + 0x930#64) b0 b1 b2 b3 b4 b5 b6 ∗
          keyPair64UnalignedAt (coroPtr + 0x398#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
          ((s.sp + 0x90#64) ↦₆₄ 64#64) ∗
          ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
          ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((s.sp + 0xb8#64) ↦₆₄ 32#64) ∗
          ((s.sp + 0xd0#64) ↦₆₄ spkPrivPtr) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ w6) ∗
          ((s.sp + 0x3e8#64) ↦₈ b63) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗
          ((coroPtr + 0x400#64) ↦₆₄ kyberStoreVt) ∗
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
          ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
          ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
          ((kyberStoreVt + 0x18#64) ↦₆₄ᵣ kyberLoadShimAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = kyberStorePtr ∧
        s1.readReg64 .x1 = kyberPreKeyId.zeroExtend 64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = spkSigPtr ∧
        s1.readReg64 .x21 = v_b0 ∧
        s1.readReg64 .x22 = spkPubPtr ∧
        s1.readReg64 .x23 = v_a0 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = coroPtr + 0x398#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1460#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg2d_wp_trap b C abs hA s coroPtr
      msgPtr spkPubPtr spkPrivPtr spkSigPtr kyberCtCap kyberStorePtr kyberStoreVt kyberLoadShimAddr
      v_a0 v_b0 u_3e0 kyberPreKeyId b0 b1 b2 b3 b4 b5 b6 b63 s0 s1_b s2 s3 s4 s5 s6
      c0 c1 c2 c3 c4 c5 c6 c63 b_3e8 w0 w1 w2 w3 w4 w5 w6 cw0 cw1 cw2 cw3 cw4 cw5 cw6
      hpc hrun hsp_align hkyber_nz hx19 hx20 hx22 hx28)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg3a_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr ctxPtr kyberFutPtr kyberFutVt kyberPollAddr u_4f8 u_500 : BitVec 64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1460#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = kyberFutPtr)
    (hx1 : s.readReg64 .x1 = kyberFutVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr) :
    SepWP (trTrapProgAt b C abs) kyberPollAddr s
      (((coroPtr + 0x4f8#64) ↦₆₄ u_4f8) ∗
       ((coroPtr + 0x500#64) ↦₆₄ u_500) ∗
       ((kyberFutVt + 0x18#64) ↦₆₄ᵣ kyberPollAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ kyberFutVt) ∗
          ((kyberFutVt + 0x18#64) ↦₆₄ᵣ kyberPollAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = kyberFutPtr ∧
        s1.readReg64 .x1 = ctxPtr ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = s.readReg64 .x21 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x998#64) := by
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x1460 0x1468
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x988 0x994
  dsimp only [trTrapProgAt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx0' : s.readReg64 (Reg.gpr 0#5) = kyberFutPtr := hx0
  have hx1' : s.readReg64 (Reg.gpr 1#5) = kyberFutVt := hx1
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx27' : s.readReg64 (Reg.gpr 27#5) = ctxPtr := hx27
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- Segment P2.3a (`+0x1460 → +0x0994`): stores `(kyberFutPtr, kyberFutVt)` at
`coroPtr + 0x4f8..0x500` and polls `get_kyber_pre_key` (`blr x9`). -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg3a_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr ctxPtr kyberFutPtr kyberFutVt kyberPollAddr u_4f8 u_500 : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1460#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = kyberFutPtr)
    (hx1 : s.readReg64 .x1 = kyberFutVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr) :
    SepWP (tripleRatchetProgAt b C ctl abs) kyberPollAddr s
      (((coroPtr + 0x4f8#64) ↦₆₄ u_4f8) ∗
       ((coroPtr + 0x500#64) ↦₆₄ u_500) ∗
       ((kyberFutVt + 0x18#64) ↦₆₄ᵣ kyberPollAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ kyberFutVt) ∗
          ((kyberFutVt + 0x18#64) ↦₆₄ᵣ kyberPollAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = kyberFutPtr ∧
        s1.readReg64 .x1 = ctxPtr ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = s.readReg64 .x21 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x998#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg3a_wp_trap b C abs s coroPtr ctxPtr
      kyberFutPtr kyberFutVt kyberPollAddr u_4f8 u_500 hpc hrun hx0 hx1 hx19 hx27)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg3b_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr kyberFutPtr kyberFutVt kyberDropAddr
    kyberPubPtr kyberSecCap kyberSecPtr kyberSigCap kyberSigPtr
    v_98 v_a0 v_b0 u_90 u_98 u_a0 u_a8 u_b0 u_b8 u_d0 : BitVec 64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x998#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hdrop_nz : kyberDropAddr ≠ 0#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = v_a0)
    (hx26 : s.readReg64 .x26 = v_98) :
    SepWP (trTrapProgAt b C abs) kyberDropAddr s
      (preKeyRecordOut64At (s.sp + 0x3e0#64)
         1569#64 kyberPubPtr 1569#64 kyberSecCap kyberSecPtr 3169#64 kyberSigCap kyberSigPtr ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
       ((coroPtr + 0x500#64) ↦₆₄ kyberFutVt) ∗
       ((kyberFutVt + 0x0#64) ↦₆₄ᵣ kyberDropAddr) ∗
       ((s.sp + 0x90#64) ↦₆₄ u_90) ∗
       ((s.sp + 0x98#64) ↦₆₄ u_98) ∗
       ((s.sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0))
      (fun s1 P_f =>
        (P_f ⊢
          preKeyRecordOut64At (s.sp + 0x3e0#64)
            1569#64 kyberPubPtr 1569#64 kyberSecCap kyberSecPtr 3169#64 kyberSigCap kyberSigPtr ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ kyberFutVt) ∗
          ((kyberFutVt + 0x0#64) ↦₆₄ᵣ kyberDropAddr) ∗
          ((s.sp + 0x90#64) ↦₆₄ kyberSigCap) ∗
          ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
          ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
          ((s.sp + 0xa8#64) ↦₆₄ 3169#64) ∗
          ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((s.sp + 0xb8#64) ↦₆₄ kyberSecCap) ∗
          ((s.sp + 0xd0#64) ↦₆₄ kyberSecPtr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = kyberFutPtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = kyberSigPtr ∧
        s1.readReg64 .x21 = kyberFutPtr ∧
        s1.readReg64 .x22 = 1569#64 ∧
        s1.readReg64 .x23 = kyberPubPtr ∧
        s1.readReg64 .x24 = kyberFutVt ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = v_98 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 1569#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xc3c#64) := by
  have hdrop_beq : (kyberDropAddr == 0#64) = false := beq_eq_false_iff_ne.mpr hdrop_nz
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x998 0x9a0
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0xbf4 0xc38
  dsimp only [trTrapProgAt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = v_b0 := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = v_a0 := hx23
  have hx26' : s.readReg64 (Reg.gpr 26#5) = v_98 := hx26
  dsimp only [preKeyRecordOut64At]
  conv =>
    arg 4
    simp (config := { maxSteps := 1000000 }) only [
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨?_, rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

/-- Segment P2.3b (`+0x0998 → +0x0c38`): reads `KyberPreKeyRecord` from `sp + 0x3e0..0x420` and
invokes `kyberDropAddr` (`blr x8`). -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg3b_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr kyberFutPtr kyberFutVt kyberDropAddr
    kyberPubPtr kyberSecCap kyberSecPtr kyberSigCap kyberSigPtr
    v_98 v_a0 v_b0 u_90 u_98 u_a0 u_a8 u_b0 u_b8 u_d0 : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x998#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hdrop_nz : kyberDropAddr ≠ 0#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = v_a0)
    (hx26 : s.readReg64 .x26 = v_98) :
    SepWP (tripleRatchetProgAt b C ctl abs) kyberDropAddr s
      (preKeyRecordOut64At (s.sp + 0x3e0#64)
         1569#64 kyberPubPtr 1569#64 kyberSecCap kyberSecPtr 3169#64 kyberSigCap kyberSigPtr ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
       ((coroPtr + 0x500#64) ↦₆₄ kyberFutVt) ∗
       ((kyberFutVt + 0x0#64) ↦₆₄ᵣ kyberDropAddr) ∗
       ((s.sp + 0x90#64) ↦₆₄ u_90) ∗
       ((s.sp + 0x98#64) ↦₆₄ u_98) ∗
       ((s.sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0))
      (fun s1 P_f =>
        (P_f ⊢
          preKeyRecordOut64At (s.sp + 0x3e0#64)
            1569#64 kyberPubPtr 1569#64 kyberSecCap kyberSecPtr 3169#64 kyberSigCap kyberSigPtr ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ kyberFutVt) ∗
          ((kyberFutVt + 0x0#64) ↦₆₄ᵣ kyberDropAddr) ∗
          ((s.sp + 0x90#64) ↦₆₄ kyberSigCap) ∗
          ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
          ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
          ((s.sp + 0xa8#64) ↦₆₄ 3169#64) ∗
          ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((s.sp + 0xb8#64) ↦₆₄ kyberSecCap) ∗
          ((s.sp + 0xd0#64) ↦₆₄ kyberSecPtr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = kyberFutPtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = kyberSigPtr ∧
        s1.readReg64 .x21 = kyberFutPtr ∧
        s1.readReg64 .x22 = 1569#64 ∧
        s1.readReg64 .x23 = kyberPubPtr ∧
        s1.readReg64 .x24 = kyberFutVt ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = v_98 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 1569#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xc3c#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg3b_wp_trap b C abs s coroPtr
      kyberFutPtr kyberFutVt kyberDropAddr kyberPubPtr kyberSecCap kyberSecPtr kyberSigCap kyberSigPtr
      v_98 v_a0 v_b0 u_90 u_98 u_a0 u_a8 u_b0 u_b8 u_d0 hpc hrun hsp_align hdrop_nz
      hx19 hx21 hx23 hx26)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg3c_wp_trap {A : RustAlloc} (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s : State) (coroPtr ctxPtr kyberFutPtr kyberFutVt kyberPubPtr kyberSecPtr kyberSigPtr
    u_c0 : BitVec 64)
    (kyberBoxSize : Nat)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xc3c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hbs_nz : BitVec.ofNat 64 kyberBoxSize ≠ 0#64)
    (hbs_lt : kyberBoxSize < 2 ^ 64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = kyberSigPtr)
    (hx21 : s.readReg64 .x21 = kyberFutPtr)
    (hx22 : s.readReg64 .x22 = 1569#64)
    (hx23 : s.readReg64 .x23 = kyberPubPtr)
    (hx24 : s.readReg64 .x24 = kyberFutVt)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 1569#64) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + bv% ((2^64 + ls_off% "<libsignal_protocol::kem::KeyPair as libsignal_protocol::state::signed_prekey::KeyPairSerde>::from_public_and_private" - ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64)) s
      (((kyberFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 kyberBoxSize) ∗
       ((kyberFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.live kyberFutPtr kyberBoxSize 8 ∗
       memRegion kyberFutPtr kyberBoxSize ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       ((s.sp + 0xa8#64) ↦₆₄ 3169#64) ∗
       ((s.sp + 0xc0#64) ↦₆₄ u_c0) ∗
       ((s.sp + 0xd0#64) ↦₆₄ kyberSecPtr))
      (fun s1 P_f =>
        (P_f ⊢
          ((kyberFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 kyberBoxSize) ∗
          ((kyberFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          ((s.sp + 0xa8#64) ↦₆₄ 3169#64) ∗
          ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          ((s.sp + 0xd0#64) ↦₆₄ kyberSecPtr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = kyberPubPtr ∧
        s1.readReg64 .x1 = 1569#64 ∧
        s1.readReg64 .x2 = kyberSecPtr ∧
        s1.readReg64 .x3 = 3169#64 ∧
        s1.readReg64 .x8 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = kyberSigPtr ∧
        s1.readReg64 .x22 = 1569#64 ∧
        s1.readReg64 .x23 = kyberPubPtr ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = 1569#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xc74#64) := by
  have hdealloc := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_dealloc_ok_trap (b := b) (C := C)
    (abs := abs) hA
  have hbs_beq : (BitVec.ofNat 64 kyberBoxSize == 0#64) = false := beq_eq_false_iff_ne.mpr hbs_nz
  have hbs_toNat : (BitVec.ofNat 64 kyberBoxSize).toNat = kyberBoxSize := Nat.mod_eq_of_lt hbs_lt
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0xc3c 0xc70
  dsimp only [trTrapProgAt] at hdealloc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = kyberSigPtr := hx20
  have hx21' : s.readReg64 (Reg.gpr 21#5) = kyberFutPtr := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = 1569#64 := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = kyberPubPtr := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = kyberFutVt := hx24
  have hx27' : s.readReg64 (Reg.gpr 27#5) = ctxPtr := hx27
  have hx28' : s.readReg64 (Reg.gpr 28#5) = 1569#64 := hx28
  wp_steps
  wp_call hdealloc (kyberFutPtr, kyberBoxSize, 8)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- Segment P2.3c (`+0x0c3c → +0x0c70`): deallocates `kyberFutPtr` and calls
`kem::KeyPair::from_public_and_private`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg3c_wp {A : RustAlloc} (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s : State) (coroPtr ctxPtr kyberFutPtr kyberFutVt kyberPubPtr kyberSecPtr kyberSigPtr
    u_c0 : BitVec 64)
    (kyberBoxSize : Nat)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xc3c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hbs_nz : BitVec.ofNat 64 kyberBoxSize ≠ 0#64)
    (hbs_lt : kyberBoxSize < 2 ^ 64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = kyberSigPtr)
    (hx21 : s.readReg64 .x21 = kyberFutPtr)
    (hx22 : s.readReg64 .x22 = 1569#64)
    (hx23 : s.readReg64 .x23 = kyberPubPtr)
    (hx24 : s.readReg64 .x24 = kyberFutVt)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 1569#64) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + bv% ((2^64 + ls_off% "<libsignal_protocol::kem::KeyPair as libsignal_protocol::state::signed_prekey::KeyPairSerde>::from_public_and_private" - ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64)) s
      (((kyberFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 kyberBoxSize) ∗
       ((kyberFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.live kyberFutPtr kyberBoxSize 8 ∗
       memRegion kyberFutPtr kyberBoxSize ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       ((s.sp + 0xa8#64) ↦₆₄ 3169#64) ∗
       ((s.sp + 0xc0#64) ↦₆₄ u_c0) ∗
       ((s.sp + 0xd0#64) ↦₆₄ kyberSecPtr))
      (fun s1 P_f =>
        (P_f ⊢
          ((kyberFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 kyberBoxSize) ∗
          ((kyberFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          ((s.sp + 0xa8#64) ↦₆₄ 3169#64) ∗
          ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          ((s.sp + 0xd0#64) ↦₆₄ kyberSecPtr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = kyberPubPtr ∧
        s1.readReg64 .x1 = 1569#64 ∧
        s1.readReg64 .x2 = kyberSecPtr ∧
        s1.readReg64 .x3 = 3169#64 ∧
        s1.readReg64 .x8 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = kyberSigPtr ∧
        s1.readReg64 .x22 = 1569#64 ∧
        s1.readReg64 .x23 = kyberPubPtr ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = 1569#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xc74#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg3c_wp_trap b C abs hA s coroPtr
      ctxPtr kyberFutPtr kyberFutVt kyberPubPtr kyberSecPtr kyberSigPtr u_c0 kyberBoxSize
      hpc hrun hsp_align hbs_nz hbs_lt hx19 hx20 hx21 hx22 hx23 hx24 hx27 hx28)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg3d1_wp_trap {A : RustAlloc} (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s : State) (coroPtr msgPtr kyberPubPtr kyberSecPtr kyberSigPtr
    pkBuf skBuf kyberCtCap v_98 v_a0
    u_3d8 u_3e0 u_3e8 u_3f0 : BitVec 64)
    (b_4f1 : BitVec 8)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xc74#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = kyberSigPtr)
    (hx23 : s.readReg64 .x23 = kyberPubPtr)
    (hx28 : s.readReg64 .x28 = 1569#64) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xd04#64) s
      (((s.sp + 0xa90#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
       ((s.sp + 0xa98#64) ↦₆₄ pkBuf) ∗
       ((s.sp + 0xaa0#64) ↦₆₄ 0x620#64) ∗
       ((s.sp + 0xaa8#64) ↦₆₄ skBuf) ∗
       ((s.sp + 0xab0#64) ↦₆₄ 0xc60#64) ∗
       ((coroPtr + 0x3d8#64) ↦₆₄ u_3d8) ∗
       ((coroPtr + 0x3e0#64) ↦₆₄ u_3e0) ∗
       ((coroPtr + 0x3e8#64) ↦₆₄ u_3e8) ∗
       ((coroPtr + 0x3f0#64) ↦₆₄ u_3f0) ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       ((s.sp + 0x90#64) ↦₆₄ 64#64) ∗
       ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
       ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ 3169#64) ∗
       ((s.sp + 0xd0#64) ↦₆₄ kyberSecPtr) ∗
       A.live kyberPubPtr 1569 1 ∗ memRegion kyberPubPtr 1569 ∗
       A.live kyberSecPtr 3169 1 ∗ memRegion kyberSecPtr 3169 ∗
       A.live kyberSigPtr 64 1 ∗ memRegion kyberSigPtr 64 ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0xa90#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
          ((s.sp + 0xa98#64) ↦₆₄ pkBuf) ∗
          ((s.sp + 0xaa0#64) ↦₆₄ 0x620#64) ∗
          ((s.sp + 0xaa8#64) ↦₆₄ skBuf) ∗
          ((s.sp + 0xab0#64) ↦₆₄ 0xc60#64) ∗
          ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗
          ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
          ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗
          ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
          ((coroPtr + 0x4f1#64) ↦₈ 1#8) ∗
          ((s.sp + 0x90#64) ↦₆₄ 64#64) ∗
          ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
          ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
          ((s.sp + 0xb8#64) ↦₆₄ 3169#64) ∗
          ((s.sp + 0xd0#64) ↦₆₄ kyberSecPtr) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
          ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = 21#64 ∧
        s1.readReg64 .x1 = 1#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = msgPtr + 0x90#64 ∧
        s1.readReg64 .x22 = kyberCtCap ∧
        s1.readReg64 .x23 = v_a0 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = v_98 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  have hdealloc := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_dealloc_ok_trap (b := b) (C := C)
    (abs := abs) hA
  have hshim := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_shim_ok_trap (b := b) (C := C)
    (abs := abs)
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0xc74 0xd00
  dsimp only [trTrapProgAt] at hdealloc hshim hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = kyberSigPtr := hx20
  have hx23' : s.readReg64 (Reg.gpr 23#5) = kyberPubPtr := hx23
  have hx28' : s.readReg64 (Reg.gpr 28#5) = 1569#64 := hx28
  wp_steps
  wp_call hdealloc (kyberPubPtr, 1569, 1)
  wp_steps
  wp_call hdealloc (kyberSecPtr, 3169, 1)
  wp_steps
  wp_call hdealloc (kyberSigPtr, 64, 1)
  wp_steps
  wp_call hshim ()
  wp_steps
  have hsp_sf1 : sf_1.sp = s.sp := by simp_all [arm64_norm]
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by rw [hsp_sf1]; ac_rfl), by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- Segment P2.3d1 (`+0x0c74 → +0x0d04`): stores the ML-KEM key-pair pointers at
`coroPtr + 0x3d8..0x3f8`, deallocates Kyber record buffers, and prepares `__rust_alloc(21, 1)`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg3d1_wp {A : RustAlloc} (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s : State) (coroPtr msgPtr kyberPubPtr kyberSecPtr kyberSigPtr
    pkBuf skBuf kyberCtCap v_98 v_a0
    u_3d8 u_3e0 u_3e8 u_3f0 : BitVec 64)
    (b_4f1 : BitVec 8)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xc74#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = kyberSigPtr)
    (hx23 : s.readReg64 .x23 = kyberPubPtr)
    (hx28 : s.readReg64 .x28 = 1569#64) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xd04#64) s
      (((s.sp + 0xa90#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
       ((s.sp + 0xa98#64) ↦₆₄ pkBuf) ∗
       ((s.sp + 0xaa0#64) ↦₆₄ 0x620#64) ∗
       ((s.sp + 0xaa8#64) ↦₆₄ skBuf) ∗
       ((s.sp + 0xab0#64) ↦₆₄ 0xc60#64) ∗
       ((coroPtr + 0x3d8#64) ↦₆₄ u_3d8) ∗
       ((coroPtr + 0x3e0#64) ↦₆₄ u_3e0) ∗
       ((coroPtr + 0x3e8#64) ↦₆₄ u_3e8) ∗
       ((coroPtr + 0x3f0#64) ↦₆₄ u_3f0) ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       ((s.sp + 0x90#64) ↦₆₄ 64#64) ∗
       ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
       ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ 3169#64) ∗
       ((s.sp + 0xd0#64) ↦₆₄ kyberSecPtr) ∗
       A.live kyberPubPtr 1569 1 ∗ memRegion kyberPubPtr 1569 ∗
       A.live kyberSecPtr 3169 1 ∗ memRegion kyberSecPtr 3169 ∗
       A.live kyberSigPtr 64 1 ∗ memRegion kyberSigPtr 64 ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0xa90#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
          ((s.sp + 0xa98#64) ↦₆₄ pkBuf) ∗
          ((s.sp + 0xaa0#64) ↦₆₄ 0x620#64) ∗
          ((s.sp + 0xaa8#64) ↦₆₄ skBuf) ∗
          ((s.sp + 0xab0#64) ↦₆₄ 0xc60#64) ∗
          ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗
          ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
          ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗
          ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
          ((coroPtr + 0x4f1#64) ↦₈ 1#8) ∗
          ((s.sp + 0x90#64) ↦₆₄ 64#64) ∗
          ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
          ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
          ((s.sp + 0xb8#64) ↦₆₄ 3169#64) ∗
          ((s.sp + 0xd0#64) ↦₆₄ kyberSecPtr) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
          ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = 21#64 ∧
        s1.readReg64 .x1 = 1#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = msgPtr + 0x90#64 ∧
        s1.readReg64 .x22 = kyberCtCap ∧
        s1.readReg64 .x23 = v_a0 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = v_98 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg3d1_wp_trap b C abs hA s coroPtr
      msgPtr kyberPubPtr kyberSecPtr kyberSigPtr pkBuf skBuf kyberCtCap v_98 v_a0
      u_3d8 u_3e0 u_3e8 u_3f0 b_4f1 hpc hrun hsp_align hx19 hx20 hx23 hx28)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg3d2a_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr errStrPtr ro0 ro8 : BitVec 64)
    (hb : b &&& 0xfff#64 = 0#64)
    (herr_nz : errStrPtr ≠ 0#64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xd08#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = errStrPtr)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xd1c#64) s
      (((b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3340) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3344))) ↦₆₄ᵣ ro0) ∗
       ((b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3340) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3344) + 8)) ↦₆₄ᵣ ro8))
      (fun s1 P_f =>
        (P_f ⊢
          ((b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3340) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3344))) ↦₆₄ᵣ ro0) ∗
          ((b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3340) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3344) + 8)) ↦₆₄ᵣ ro8)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = errStrPtr ∧
        s1.readReg64 .x8 = b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3340) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3344)) ∧
        s1.readReg64 .x9 = 3#64 ∧
        s1.readVReg128 0#5 = ro8 ++ ro0 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = s.readReg64 .x21 ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  have herr_beq : (errStrPtr == 0#64) = false := beq_eq_false_iff_ne.mpr herr_nz
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0xd08 0xd18
  dsimp only [trTrapProgAt] at hpc ⊢
  have hentry : (libsignalSessionCode.rebase b
      (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName =
      b + (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have hadrp0 := (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.adrp_missingKyber_0xd0c hb hentry).1
  have hadrp := (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.adrp_missingKyber_0xd0c hb hentry).2
  clear hentry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx0' : s.readReg64 (Reg.gpr 0#5) = errStrPtr := hx0
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have h5b0a5 : (b + bv% (page% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3340) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3344)))) + bv% ((ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3340) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3344)) % 4096) = b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3340) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3344)) := by bv_arith
  have h5b0ad : (b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3340) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3344))) + 8#64 = b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3340) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3344) + 8) := by bv_arith
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

/-- Segment P2.3d2a (`+0x0d08 → +0x0d1c`): checks `errStrPtr ≠ 0` and loads the first 16 bytes of
`"missing pq ciphertext"` into `q0`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg3d2a_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr errStrPtr ro0 ro8 : BitVec 64)
    (hb : b &&& 0xfff#64 = 0#64)
    (herr_nz : errStrPtr ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xd08#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = errStrPtr)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xd1c#64) s
      (((b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3340) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3344))) ↦₆₄ᵣ ro0) ∗
       ((b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3340) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3344) + 8)) ↦₆₄ᵣ ro8))
      (fun s1 P_f =>
        (P_f ⊢
          ((b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3340) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3344))) ↦₆₄ᵣ ro0) ∗
          ((b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3340) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3344) + 8)) ↦₆₄ᵣ ro8)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = errStrPtr ∧
        s1.readReg64 .x8 = b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3340) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3344)) ∧
        s1.readReg64 .x9 = 3#64 ∧
        s1.readVReg128 0#5 = ro8 ++ ro0 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = s.readReg64 .x21 ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg3d2a_wp_trap b C abs s coroPtr
      errStrPtr ro0 ro8 hb herr_nz hpc hrun hx0 hx19)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg3d2b_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr errStrPtr ro0 ro8 ro13 u0 u8 u_3f0 : BitVec 64)
    (b_400 : BitVec 8)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xd1c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = errStrPtr)
    (hx8 : s.readReg64 .x8 = b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3340) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3344)))
    (hx9 : s.readReg64 .x9 = 3#64)
    (hq0 : s.readVReg128 0#5 = ro8 ++ ro0)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xd38#64) s
      (((b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3340) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3344) + 13)) ↦₆₄ᵣ ro13) ∗
       (errStrPtr ↦₆₄ u0) ∗
       ((errStrPtr + 8#64) ↦₆₄ u8) ∗
       ((s.sp + 0x3f0#64) ↦₆₄ u_3f0) ∗
       ((s.sp + 0x400#64) ↦₈ b_400))
      (fun s1 P_f =>
        (P_f ⊢
          ((b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3340) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3344) + 13)) ↦₆₄ᵣ ro13) ∗
          (errStrPtr ↦₆₄ ro0) ∗
          ((errStrPtr + 8#64) ↦₆₄ ro8) ∗
          ((s.sp + 0x3f0#64) ↦₆₄ errStrPtr) ∗
          ((s.sp + 0x400#64) ↦₈ 3#8)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = errStrPtr ∧
        s1.readReg64 .x8 = ro13 ∧
        s1.readReg64 .x9 = 0x8000000000000006#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = s.readReg64 .x21 ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0xd1c 0xd34
  dsimp only [trTrapProgAt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx0' : s.readReg64 (Reg.gpr 0#5) = errStrPtr := hx0
  have hx8' : s.readReg64 (Reg.gpr 8#5) = b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3340) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3344)) := hx8
  have hx9' : s.readReg64 (Reg.gpr 9#5) = 3#64 := hx9
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hq0_lo : (s.readVReg128 0#5).extractLsb' 0 64 = ro0 := by rw [hq0]; clear * -; bv_slice
  have hq0_hi : (s.readVReg128 0#5).extractLsb' 64 64 = ro8 := by rw [hq0]; clear * -; bv_slice
  have h5b0b2 : (b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3340) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3344))) + 13#64 = b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3340) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3344) + 13) := by bv_arith
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- Segment P2.3d2b (`+0x0d1c → +0x0d38`): loads the trailing 8 bytes of `"missing pq ciphertext"`
and writes the first 16 bytes to `errStrPtr`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg3d2b_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr errStrPtr ro0 ro8 ro13 u0 u8 u_3f0 : BitVec 64)
    (b_400 : BitVec 8)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xd1c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = errStrPtr)
    (hx8 : s.readReg64 .x8 = b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3340) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3344)))
    (hx9 : s.readReg64 .x9 = 3#64)
    (hq0 : s.readVReg128 0#5 = ro8 ++ ro0)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xd38#64) s
      (((b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3340) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3344) + 13)) ↦₆₄ᵣ ro13) ∗
       (errStrPtr ↦₆₄ u0) ∗
       ((errStrPtr + 8#64) ↦₆₄ u8) ∗
       ((s.sp + 0x3f0#64) ↦₆₄ u_3f0) ∗
       ((s.sp + 0x400#64) ↦₈ b_400))
      (fun s1 P_f =>
        (P_f ⊢
          ((b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3340) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3344) + 13)) ↦₆₄ᵣ ro13) ∗
          (errStrPtr ↦₆₄ ro0) ∗
          ((errStrPtr + 8#64) ↦₆₄ ro8) ∗
          ((s.sp + 0x3f0#64) ↦₆₄ errStrPtr) ∗
          ((s.sp + 0x400#64) ↦₈ 3#8)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = errStrPtr ∧
        s1.readReg64 .x8 = ro13 ∧
        s1.readReg64 .x9 = 0x8000000000000006#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = s.readReg64 .x21 ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg3d2b_wp_trap b C abs s coroPtr
      errStrPtr ro0 ro8 ro13 u0 u8 u_3f0 b_400 hpc hrun hsp_align hx0 hx8 hx9 hq0 hx19)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg3d2c_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr errStrPtr kyberCtCap ro13 u13 u_3e0 u_3e8 u_3f8 : BitVec 64)
    (hkyber_nz : kyberCtCap ≠ 0#64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xd38#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = errStrPtr)
    (hx8 : s.readReg64 .x8 = ro13)
    (hx9 : s.readReg64 .x9 = 0x8000000000000006#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = kyberCtCap) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" - ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64)) s
      (((errStrPtr + 13#64) ↦₆₄ u13) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ u_3e0) ∗
       ((s.sp + 0x3e8#64) ↦₆₄ u_3e8) ∗
       ((s.sp + 0x3f8#64) ↦₆₄ u_3f8))
      (fun s1 P_f =>
        (P_f ⊢
          ((errStrPtr + 13#64) ↦₆₄ ro13) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ 0x8000000000000018#64) ∗
          ((s.sp + 0x3e8#64) ↦₆₄ 21#64) ∗
          ((s.sp + 0x3f8#64) ↦₆₄ 21#64)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = 0x8000000000000018#64 ∧
        s1.readReg64 .x21 = s.readReg64 .x21 ∧
        s1.readReg64 .x22 = kyberCtCap ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xd5c#64) := by
  have hkyber_beq : (kyberCtCap == 0#64) = false := beq_eq_false_iff_ne.mpr hkyber_nz
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0xd38 0xd58
  dsimp only [trTrapProgAt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx0' : s.readReg64 (Reg.gpr 0#5) = errStrPtr := hx0
  have hx8' : s.readReg64 (Reg.gpr 8#5) = ro13 := hx8
  have hx9' : s.readReg64 (Reg.gpr 9#5) = 0x8000000000000006#64 := hx9
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = kyberCtCap := hx22
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- Segment P2.3d2c (`+0x0d38 → +0x0d58`): completes the eager `SignalProtocolError` string,
verifies `kyberCtCap ≠ 0`, and drops the unused error via `drop_glue::<SignalProtocolError>`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg3d2c_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr errStrPtr kyberCtCap ro13 u13 u_3e0 u_3e8 u_3f8 : BitVec 64)
    (hkyber_nz : kyberCtCap ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xd38#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = errStrPtr)
    (hx8 : s.readReg64 .x8 = ro13)
    (hx9 : s.readReg64 .x9 = 0x8000000000000006#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = kyberCtCap) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" - ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64)) s
      (((errStrPtr + 13#64) ↦₆₄ u13) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ u_3e0) ∗
       ((s.sp + 0x3e8#64) ↦₆₄ u_3e8) ∗
       ((s.sp + 0x3f8#64) ↦₆₄ u_3f8))
      (fun s1 P_f =>
        (P_f ⊢
          ((errStrPtr + 13#64) ↦₆₄ ro13) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ 0x8000000000000018#64) ∗
          ((s.sp + 0x3e8#64) ↦₆₄ 21#64) ∗
          ((s.sp + 0x3f8#64) ↦₆₄ 21#64)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = 0x8000000000000018#64 ∧
        s1.readReg64 .x21 = s.readReg64 .x21 ∧
        s1.readReg64 .x22 = kyberCtCap ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xd5c#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg3d2c_wp_trap b C abs s coroPtr
      errStrPtr kyberCtCap ro13 u13 u_3e0 u_3e8 u_3f8 hkyber_nz hpc hrun hsp_align
      hx0 hx8 hx9 hx19 hx22)



/-! ## 3. Stage P2.4 Segment Proofs (`+0x0d5c → +0x36a8`) -/

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg4_none_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr msgPtr ctxPtr idStorePtr idStoreVt getIdKpShimAddr
    v_b0 u_488 : BitVec 64)
    (kyberPreKeyId opkId : BitVec 32) (b_4b0 : BitVec 8)
    (hb : b &&& 0xfff#64 = 0#64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xd5c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = kyberPreKeyId.zeroExtend 64) :
    SepWP (trTrapProgAt b C abs) getIdKpShimAddr s
      (((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗
       ((coroPtr + 0x420#64) ↦₆₄ idStoreVt) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((coroPtr + 0x488#64) ↦₆₄ u_488) ∗
       ((coroPtr + 0x4b0#64) ↦₈ b_4b0) ∗
       ((msgPtr + 0x78#64) ↦₃₂ 0#32) ∗
       ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
       ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
       ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((idStoreVt + 0x18#64) ↦₆₄ᵣ getIdKpShimAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗
          ((coroPtr + 0x420#64) ↦₆₄ idStoreVt) ∗
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
          ((coroPtr + 0x488#64) ↦₆₄ kyberPreKeyId.zeroExtend 64) ∗
          ((coroPtr + 0x4b0#64) ↦₈ 0#8) ∗
          ((msgPtr + 0x78#64) ↦₃₂ 0#32) ∗
          ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
          ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          ((idStoreVt + 0x18#64) ↦₆₄ᵣ getIdKpShimAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = idStorePtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = v_b0 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x36ac#64) := by
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0xd5c 0xd74
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x3630 0x363c
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x3694 0x36a8
  dsimp only [trTrapProgAt] at hpc ⊢
  have hentry : (libsignalSessionCode.rebase b
      (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName =
      b + (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have hadrp0 := (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.adrp_logLevel_0xd64 hb hentry).1
  have hadrp := (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.adrp_logLevel_0xd64 hb hentry).2
  clear hentry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = kyberPreKeyId.zeroExtend 64 := hx21
  have h5b810 : (b + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256))) + bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096) = b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) := by bv_arith
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- Segment P2.4-None (`+0x0d5c → +0x36a8`): `opkId? = none` path storing `kyberPreKeyId`, marking
`[coroPtr + 0x4b0] = 0`, and invoking `get_identity_key_pair` (`blr x8`). -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg4_none_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr msgPtr ctxPtr idStorePtr idStoreVt getIdKpShimAddr
    v_b0 u_488 : BitVec 64)
    (kyberPreKeyId opkId : BitVec 32) (b_4b0 : BitVec 8)
    (hb : b &&& 0xfff#64 = 0#64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xd5c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = kyberPreKeyId.zeroExtend 64) :
    SepWP (tripleRatchetProgAt b C ctl abs) getIdKpShimAddr s
      (((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗
       ((coroPtr + 0x420#64) ↦₆₄ idStoreVt) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((coroPtr + 0x488#64) ↦₆₄ u_488) ∗
       ((coroPtr + 0x4b0#64) ↦₈ b_4b0) ∗
       ((msgPtr + 0x78#64) ↦₃₂ 0#32) ∗
       ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
       ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
       ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((idStoreVt + 0x18#64) ↦₆₄ᵣ getIdKpShimAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗
          ((coroPtr + 0x420#64) ↦₆₄ idStoreVt) ∗
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
          ((coroPtr + 0x488#64) ↦₆₄ kyberPreKeyId.zeroExtend 64) ∗
          ((coroPtr + 0x4b0#64) ↦₈ 0#8) ∗
          ((msgPtr + 0x78#64) ↦₃₂ 0#32) ∗
          ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
          ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          ((idStoreVt + 0x18#64) ↦₆₄ᵣ getIdKpShimAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = idStorePtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = v_b0 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x36ac#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg4_none_wp_trap b C abs s coroPtr
      msgPtr ctxPtr idStorePtr idStoreVt getIdKpShimAddr v_b0 u_488 kyberPreKeyId opkId b_4b0
      hb hpc hrun hsp_align hx19 hx21)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg4a_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr msgPtr ctxPtr preKeyStorePtr preKeyStoreVt opkLoadShimAddr
    u_488 : BitVec 64)
    (kyberPreKeyId opkId : BitVec 32)
    (hb : b &&& 0xfff#64 = 0#64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xd5c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = kyberPreKeyId.zeroExtend 64) :
    SepWP (trTrapProgAt b C abs) opkLoadShimAddr s
      (((coroPtr + 0x408#64) ↦₆₄ preKeyStorePtr) ∗
       ((coroPtr + 0x410#64) ↦₆₄ preKeyStoreVt) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((coroPtr + 0x488#64) ↦₆₄ u_488) ∗
       ((msgPtr + 0x78#64) ↦₃₂ 1#32) ∗
       ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
       ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((preKeyStoreVt + 0x18#64) ↦₆₄ᵣ opkLoadShimAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x408#64) ↦₆₄ preKeyStorePtr) ∗
          ((coroPtr + 0x410#64) ↦₆₄ preKeyStoreVt) ∗
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
          ((coroPtr + 0x488#64) ↦₆₄ kyberPreKeyId.zeroExtend 64) ∗
          ((msgPtr + 0x78#64) ↦₃₂ 1#32) ∗
          ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
          ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          ((preKeyStoreVt + 0x18#64) ↦₆₄ᵣ opkLoadShimAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = preKeyStorePtr ∧
        s1.readReg64 .x1 = opkId.zeroExtend 64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = opkId.zeroExtend 64 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xdec#64) := by
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0xd5c 0xd80
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0xdd8 0xde8
  dsimp only [trTrapProgAt] at hpc ⊢
  have hentry : (libsignalSessionCode.rebase b
      (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName =
      b + (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have hadrp0 := (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.adrp_logLevel_0xd64 hb hentry).1
  have hadrp := (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.adrp_logLevel_0xd64 hb hentry).2
  clear hentry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = kyberPreKeyId.zeroExtend 64 := hx21
  have h5b810 : (b + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256))) + bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096) = b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) := by bv_arith
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- Segment P2.4a (`+0x0d5c → +0x0de8`): `opkId? = some opkId` path storing `kyberPreKeyId` and
invoking `get_pre_key` (`blr x8`). -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg4a_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr msgPtr ctxPtr preKeyStorePtr preKeyStoreVt opkLoadShimAddr
    u_488 : BitVec 64)
    (kyberPreKeyId opkId : BitVec 32)
    (hb : b &&& 0xfff#64 = 0#64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xd5c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = kyberPreKeyId.zeroExtend 64) :
    SepWP (tripleRatchetProgAt b C ctl abs) opkLoadShimAddr s
      (((coroPtr + 0x408#64) ↦₆₄ preKeyStorePtr) ∗
       ((coroPtr + 0x410#64) ↦₆₄ preKeyStoreVt) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((coroPtr + 0x488#64) ↦₆₄ u_488) ∗
       ((msgPtr + 0x78#64) ↦₃₂ 1#32) ∗
       ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
       ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((preKeyStoreVt + 0x18#64) ↦₆₄ᵣ opkLoadShimAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x408#64) ↦₆₄ preKeyStorePtr) ∗
          ((coroPtr + 0x410#64) ↦₆₄ preKeyStoreVt) ∗
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
          ((coroPtr + 0x488#64) ↦₆₄ kyberPreKeyId.zeroExtend 64) ∗
          ((msgPtr + 0x78#64) ↦₃₂ 1#32) ∗
          ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
          ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          ((preKeyStoreVt + 0x18#64) ↦₆₄ᵣ opkLoadShimAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = preKeyStorePtr ∧
        s1.readReg64 .x1 = opkId.zeroExtend 64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = opkId.zeroExtend 64 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xdec#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg4a_wp_trap b C abs s coroPtr
      msgPtr ctxPtr preKeyStorePtr preKeyStoreVt opkLoadShimAddr u_488 kyberPreKeyId opkId
      hb hpc hrun hsp_align hx19 hx21)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg4b_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr ctxPtr opkFutPtr opkFutVt opkPollAddr v_b0 u_4f8 u_500 : BitVec 64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xdec#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = opkFutPtr)
    (hx1 : s.readReg64 .x1 = opkFutVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr) :
    SepWP (trTrapProgAt b C abs) opkPollAddr s
      (((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ u_4f8) ∗
       ((coroPtr + 0x500#64) ↦₆₄ u_500) ∗
       ((opkFutVt + 0x18#64) ↦₆₄ᵣ opkPollAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ opkFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ opkFutVt) ∗
          ((opkFutVt + 0x18#64) ↦₆₄ᵣ opkPollAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = opkFutPtr ∧
        s1.readReg64 .x1 = ctxPtr ∧
        s1.readReg64 .x8 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = v_b0 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x9c4#64) := by
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0xdec 0xdf8
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x9b4 0x9c0
  dsimp only [trTrapProgAt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx0' : s.readReg64 (Reg.gpr 0#5) = opkFutPtr := hx0
  have hx1' : s.readReg64 (Reg.gpr 1#5) = opkFutVt := hx1
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx27' : s.readReg64 (Reg.gpr 27#5) = ctxPtr := hx27
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- Segment P2.4b (`+0x0dec → +0x09c0`): stores `(opkFutPtr, opkFutVt)` at `coroPtr + 0x4f8..0x500`
and polls `get_pre_key` (`blr x9`). -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg4b_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr ctxPtr opkFutPtr opkFutVt opkPollAddr v_b0 u_4f8 u_500 : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xdec#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = opkFutPtr)
    (hx1 : s.readReg64 .x1 = opkFutVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr) :
    SepWP (tripleRatchetProgAt b C ctl abs) opkPollAddr s
      (((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ u_4f8) ∗
       ((coroPtr + 0x500#64) ↦₆₄ u_500) ∗
       ((opkFutVt + 0x18#64) ↦₆₄ᵣ opkPollAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ opkFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ opkFutVt) ∗
          ((opkFutVt + 0x18#64) ↦₆₄ᵣ opkPollAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = opkFutPtr ∧
        s1.readReg64 .x1 = ctxPtr ∧
        s1.readReg64 .x8 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = v_b0 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x9c4#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg4b_wp_trap b C abs s coroPtr
      ctxPtr opkFutPtr opkFutVt opkPollAddr v_b0 u_4f8 u_500 hpc hrun hsp_align hx0 hx1 hx19 hx27)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg4d_wp_trap {A : RustAlloc} (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s : State) (coroPtr opkFutPtr opkFutVt opkPubPtr opkPubCap opkSecPtr opkSecCap opkIdWord
    r0 r1 r2 r3 r4 r5 r6 : BitVec 64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xe40#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = opkFutPtr)
    (hx22 : s.readReg64 .x22 = 33#64)
    (hx23 : s.readReg64 .x23 = 32#64)
    (hx24 : s.readReg64 .x24 = opkFutVt)
    (hx26 : s.readReg64 .x26 = opkPubPtr)
    (hx27 : s.readReg64 .x27 = opkIdWord) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + bv% ((2^64 + ls_off% "<libsignal_protocol::state::prekey::PreKeyRecord>::key_pair" - ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64)) s
      (((opkFutVt + 0x8#64) ↦₆₄ᵣ 16#64) ∗
       ((opkFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.live opkFutPtr 16 8 ∗
       memRegion opkFutPtr 16 ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       ((s.sp + 0xa8#64) ↦₆₄ opkSecCap) ∗
       ((s.sp + 0xb8#64) ↦₆₄ opkPubCap) ∗
       ((s.sp + 0xd0#64) ↦₆₄ opkSecPtr) ∗
       ((s.sp + 0x930#64) ↦₆₄ r0) ∗
       ((s.sp + 0x938#64) ↦₆₄ r1) ∗
       ((s.sp + 0x940#64) ↦₆₄ r2) ∗
       ((s.sp + 0x948#64) ↦₆₄ r3) ∗
       ((s.sp + 0x950#64) ↦₆₄ r4) ∗
       ((s.sp + 0x958#64) ↦₆₄ r5) ∗
       ((s.sp + 0x960#64) ↦₆₄ r6))
      (fun s1 P_f =>
        (P_f ⊢
          ((opkFutVt + 0x8#64) ↦₆₄ᵣ 16#64) ∗
          ((opkFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          ((s.sp + 0xa8#64) ↦₆₄ opkSecCap) ∗
          ((s.sp + 0xb8#64) ↦₆₄ opkPubCap) ∗
          ((s.sp + 0xd0#64) ↦₆₄ opkSecPtr) ∗
          ((s.sp + 0x930#64) ↦₆₄ 33#64) ∗
          ((s.sp + 0x938#64) ↦₆₄ opkPubPtr) ∗
          ((s.sp + 0x940#64) ↦₆₄ 32#64) ∗
          ((s.sp + 0x948#64) ↦₆₄ opkPubCap) ∗
          ((s.sp + 0x950#64) ↦₆₄ opkSecPtr) ∗
          ((s.sp + 0x958#64) ↦₆₄ opkSecCap) ∗
          ((s.sp + 0x960#64) ↦₆₄ opkIdWord)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = s.sp + 0x930#64 ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = opkFutPtr ∧
        s1.readReg64 .x22 = 33#64 ∧
        s1.readReg64 .x23 = 32#64 ∧
        s1.readReg64 .x24 = opkFutVt ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = opkPubPtr ∧
        s1.readReg64 .x27 = opkIdWord ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xe90#64) := by
  have hdealloc := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_dealloc_ok_trap (b := b) (C := C)
    (abs := abs) hA
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0xe40 0xe8c
  dsimp only [trTrapProgAt] at hdealloc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = opkFutPtr := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = 33#64 := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = 32#64 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = opkFutVt := hx24
  have hx26' : s.readReg64 (Reg.gpr 26#5) = opkPubPtr := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = opkIdWord := hx27
  wp_steps
  wp_call hdealloc (opkFutPtr, 16, 8)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

/-- Segment P2.4d (`+0x0e40 → +0x0e8c`): deallocates `opkFutPtr`, copies `PreKeyRecord` to
`sp + 0x930..0x960`, and calls `PreKeyRecord::key_pair`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg4d_wp {A : RustAlloc} (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s : State) (coroPtr opkFutPtr opkFutVt opkPubPtr opkPubCap opkSecPtr opkSecCap opkIdWord
    r0 r1 r2 r3 r4 r5 r6 : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xe40#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = opkFutPtr)
    (hx22 : s.readReg64 .x22 = 33#64)
    (hx23 : s.readReg64 .x23 = 32#64)
    (hx24 : s.readReg64 .x24 = opkFutVt)
    (hx26 : s.readReg64 .x26 = opkPubPtr)
    (hx27 : s.readReg64 .x27 = opkIdWord) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + bv% ((2^64 + ls_off% "<libsignal_protocol::state::prekey::PreKeyRecord>::key_pair" - ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64)) s
      (((opkFutVt + 0x8#64) ↦₆₄ᵣ 16#64) ∗
       ((opkFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.live opkFutPtr 16 8 ∗
       memRegion opkFutPtr 16 ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       ((s.sp + 0xa8#64) ↦₆₄ opkSecCap) ∗
       ((s.sp + 0xb8#64) ↦₆₄ opkPubCap) ∗
       ((s.sp + 0xd0#64) ↦₆₄ opkSecPtr) ∗
       ((s.sp + 0x930#64) ↦₆₄ r0) ∗
       ((s.sp + 0x938#64) ↦₆₄ r1) ∗
       ((s.sp + 0x940#64) ↦₆₄ r2) ∗
       ((s.sp + 0x948#64) ↦₆₄ r3) ∗
       ((s.sp + 0x950#64) ↦₆₄ r4) ∗
       ((s.sp + 0x958#64) ↦₆₄ r5) ∗
       ((s.sp + 0x960#64) ↦₆₄ r6))
      (fun s1 P_f =>
        (P_f ⊢
          ((opkFutVt + 0x8#64) ↦₆₄ᵣ 16#64) ∗
          ((opkFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          ((s.sp + 0xa8#64) ↦₆₄ opkSecCap) ∗
          ((s.sp + 0xb8#64) ↦₆₄ opkPubCap) ∗
          ((s.sp + 0xd0#64) ↦₆₄ opkSecPtr) ∗
          ((s.sp + 0x930#64) ↦₆₄ 33#64) ∗
          ((s.sp + 0x938#64) ↦₆₄ opkPubPtr) ∗
          ((s.sp + 0x940#64) ↦₆₄ 32#64) ∗
          ((s.sp + 0x948#64) ↦₆₄ opkPubCap) ∗
          ((s.sp + 0x950#64) ↦₆₄ opkSecPtr) ∗
          ((s.sp + 0x958#64) ↦₆₄ opkSecCap) ∗
          ((s.sp + 0x960#64) ↦₆₄ opkIdWord)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = s.sp + 0x930#64 ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = opkFutPtr ∧
        s1.readReg64 .x22 = 33#64 ∧
        s1.readReg64 .x23 = 32#64 ∧
        s1.readReg64 .x24 = opkFutVt ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = opkPubPtr ∧
        s1.readReg64 .x27 = opkIdWord ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xe90#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg4d_wp_trap b C abs hA s coroPtr
      opkFutPtr opkFutVt opkPubPtr opkPubCap opkSecPtr opkSecCap opkIdWord
      r0 r1 r2 r3 r4 r5 r6 hpc hrun hsp_align hx19 hx21 hx22 hx23 hx24 hx26 hx27)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg4e_wp_trap {A : RustAlloc} (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s : State) (coroPtr msgPtr ctxPtr opkPubPtr opkSecPtr idStorePtr idStoreVt getIdKpShimAddr
    v_98 v_a0 v_b0 u_270 : BitVec 64)
    (opkId : BitVec 32)
    (b0 b1 b2 b3 b4 b5 b6 b63
     s0 s1_b s2 s3 s4 s5 s6
     c0 c1 c2 c3 c4 c5 c6 c63 b_4b0 b_278 : BitVec 8)
    (w0 w1 w2 w3 w4 w5 w6
     cw0 cw1 cw2 cw3 cw4 cw5 cw6 : BitVec 64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xe90#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = 33#64)
    (hx26 : s.readReg64 .x26 = opkPubPtr) :
    SepWP (trTrapProgAt b C abs) getIdKpShimAddr s
      (((s.sp + 0x3e0#64) ↦₈ 0#8) ∗
       keyPair64UnalignedAt (s.sp + 0x3e1#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
       bytes7At (s.sp + 0x3b0#64) s0 s1_b s2 s3 s4 s5 s6 ∗
       ((coroPtr + 0x4b0#64) ↦₈ b_4b0) ∗
       keyPair64UnalignedAt
         (coroPtr + 0x4b1#64) c0 c1 c2 c3 c4 c5 c6 cw0 cw1 cw2 cw3 cw4 cw5 cw6 c63 ∗
       ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
       ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
       ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ 32#64) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((s.sp + 0xd0#64) ↦₆₄ opkSecPtr) ∗
       ((s.sp + 0x270#64) ↦₆₄ u_270) ∗
       ((s.sp + 0x278#64) ↦₈ b_278) ∗
       A.live opkPubPtr 33 1 ∗ memRegion opkPubPtr 33 ∗
       A.live opkSecPtr 32 1 ∗ memRegion opkSecPtr 32 ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗
       ((coroPtr + 0x420#64) ↦₆₄ idStoreVt) ∗
       ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
       ((idStoreVt + 0x18#64) ↦₆₄ᵣ getIdKpShimAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3e0#64) ↦₈ 0#8) ∗
          keyPair64UnalignedAt (s.sp + 0x3e1#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
          bytes7At (s.sp + 0x3b0#64) b0 b1 b2 b3 b4 b5 b6 ∗
          ((coroPtr + 0x4b0#64) ↦₈ 1#8) ∗
          keyPair64UnalignedAt (coroPtr + 0x4b1#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
          ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
          ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
          ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((s.sp + 0xb8#64) ↦₆₄ 32#64) ∗
          ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          ((s.sp + 0xd0#64) ↦₆₄ opkSecPtr) ∗
          ((s.sp + 0x270#64) ↦₆₄ w6) ∗
          ((s.sp + 0x278#64) ↦₈ b63) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗
          ((coroPtr + 0x420#64) ↦₆₄ idStoreVt) ∗
          ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
          ((idStoreVt + 0x18#64) ↦₆₄ᵣ getIdKpShimAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = idStorePtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = v_b0 ∧
        s1.readReg64 .x23 = v_a0 ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = v_98 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x36ac#64) := by
  have hdealloc := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_dealloc_ok_trap (b := b) (C := C)
    (abs := abs) hA
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0xe90 0xe98
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x1504 0x15b4
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x369c 0x36a8
  dsimp only [trTrapProgAt] at hdealloc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = 33#64 := hx22
  have hx26' : s.readReg64 (Reg.gpr 26#5) = opkPubPtr := hx26
  dsimp only [keyPair64UnalignedAt, bytes7At]
  conv =>
    arg 4
    simp (config := { maxSteps := 1000000 }) only [
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  wp_call hdealloc (opkPubPtr, 33, 1)
  wp_steps
  wp_call hdealloc (opkSecPtr, 32, 1)
  wp_steps
  rw [hsp_sf]
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨?_, by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

/-- Segment P2.4e (`+0x0e90 → +0x36a8`): stores the 64-byte OPK `KeyPair` at `coroPtr + 0x4b0..0x4f0`,
deallocates OPK buffers, and invokes `get_identity_key_pair` (`blr x8`). -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg4e_wp {A : RustAlloc} (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s : State) (coroPtr msgPtr ctxPtr opkPubPtr opkSecPtr idStorePtr idStoreVt getIdKpShimAddr
    v_98 v_a0 v_b0 u_270 : BitVec 64)
    (opkId : BitVec 32)
    (b0 b1 b2 b3 b4 b5 b6 b63
     s0 s1_b s2 s3 s4 s5 s6
     c0 c1 c2 c3 c4 c5 c6 c63 b_4b0 b_278 : BitVec 8)
    (w0 w1 w2 w3 w4 w5 w6
     cw0 cw1 cw2 cw3 cw4 cw5 cw6 : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xe90#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = 33#64)
    (hx26 : s.readReg64 .x26 = opkPubPtr) :
    SepWP (tripleRatchetProgAt b C ctl abs) getIdKpShimAddr s
      (((s.sp + 0x3e0#64) ↦₈ 0#8) ∗
       keyPair64UnalignedAt (s.sp + 0x3e1#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
       bytes7At (s.sp + 0x3b0#64) s0 s1_b s2 s3 s4 s5 s6 ∗
       ((coroPtr + 0x4b0#64) ↦₈ b_4b0) ∗
       keyPair64UnalignedAt
         (coroPtr + 0x4b1#64) c0 c1 c2 c3 c4 c5 c6 cw0 cw1 cw2 cw3 cw4 cw5 cw6 c63 ∗
       ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
       ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
       ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ 32#64) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((s.sp + 0xd0#64) ↦₆₄ opkSecPtr) ∗
       ((s.sp + 0x270#64) ↦₆₄ u_270) ∗
       ((s.sp + 0x278#64) ↦₈ b_278) ∗
       A.live opkPubPtr 33 1 ∗ memRegion opkPubPtr 33 ∗
       A.live opkSecPtr 32 1 ∗ memRegion opkSecPtr 32 ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗
       ((coroPtr + 0x420#64) ↦₆₄ idStoreVt) ∗
       ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
       ((idStoreVt + 0x18#64) ↦₆₄ᵣ getIdKpShimAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3e0#64) ↦₈ 0#8) ∗
          keyPair64UnalignedAt (s.sp + 0x3e1#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
          bytes7At (s.sp + 0x3b0#64) b0 b1 b2 b3 b4 b5 b6 ∗
          ((coroPtr + 0x4b0#64) ↦₈ 1#8) ∗
          keyPair64UnalignedAt (coroPtr + 0x4b1#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
          ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
          ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
          ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((s.sp + 0xb8#64) ↦₆₄ 32#64) ∗
          ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          ((s.sp + 0xd0#64) ↦₆₄ opkSecPtr) ∗
          ((s.sp + 0x270#64) ↦₆₄ w6) ∗
          ((s.sp + 0x278#64) ↦₈ b63) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗
          ((coroPtr + 0x420#64) ↦₆₄ idStoreVt) ∗
          ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
          ((idStoreVt + 0x18#64) ↦₆₄ᵣ getIdKpShimAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = idStorePtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = v_b0 ∧
        s1.readReg64 .x23 = v_a0 ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = v_98 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x36ac#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg4e_wp_trap b C abs hA s coroPtr
      msgPtr ctxPtr opkPubPtr opkSecPtr idStorePtr idStoreVt getIdKpShimAddr
      v_98 v_a0 v_b0 u_270 opkId b0 b1 b2 b3 b4 b5 b6 b63
      s0 s1_b s2 s3 s4 s5 s6 c0 c1 c2 c3 c4 c5 c6 c63 b_4b0 b_278
      w0 w1 w2 w3 w4 w5 w6 cw0 cw1 cw2 cw3 cw4 cw5 cw6 hpc hrun hsp_align hx19 hx22 hx26)

end CryptoVerification.E2E.Pqxdh.ResponderClosure
