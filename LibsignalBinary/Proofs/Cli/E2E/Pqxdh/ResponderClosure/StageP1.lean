/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StageP1
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import ProofLib.SepLogic.WPp

/-!
# Responder Closure Stage P1 (`+0x0000..+0x0868`)

Symbolic-execution segment proofs for Stage P1 of the CLI responder prekey decryption closure
(`message_decrypt_prekey::<signal_session_handshake::Coins>::{closure#0}`), covering session-store
load (`Poll::Ready(Ok(None))`), empty `SessionRecord` initialization, and identity-store trust
verification (`Poll::Ready(Ok(true))`).
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

set_option maxHeartbeats 1200000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")

/-! ## Isolated Callee Contracts and Stage P1 Segments (`+0x0000..+0x0868`) -/

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_memcpy_ok_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + bv% ((2^64 + ls_off% "memcpy" - (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) % 2^64))
      framelessMemcpySpec :=
  CryptoVerification.LibsignalTripleRatchet.session_memcpy_region_ok_at_trap b C abs
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName
    (num% (ls_off% "memcpy" - (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")))
    (by simp only [arm64_norm])

/-- `memcpy` (`0x51b0c`, `+0x6a40` from `0x4b0cc`) on `tripleRatchetProgAt`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_memcpy_ok {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + bv% ((2^64 + ls_off% "memcpy" - (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) % 2^64))
      framelessMemcpySpec := by
  rw [← trTrapProgAt_fnAddr_eq b C ctl abs]
  exact subroutine_ok_kit_of_trTrap
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_memcpy_ok_trap

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_dealloc_ok_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) % 2^64))
      (rustDeallocSpec A) :=
  dealloc_ok_at_norm_ext (AllocContracts.of_tripleRatchetProgAt_trap b C A abs hA)
    (name := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName) (k := num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")))

/-- `__rust_dealloc` (`0x51aec`, `+0x6a20` from `0x4b0cc`) on `tripleRatchetProgAt`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_dealloc_ok {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) % 2^64))
      (rustDeallocSpec A) := by
  rw [← trTrapProgAt_fnAddr_eq b C ctl abs]
  exact subroutine_ok_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_dealloc_ok_trap hA)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p1_seg1_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (outPtr coroPtr ctxPtr
    msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr sessStoreVt idStorePtr idStoreVt
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr
    loadShimAddr v_sp0 : BitVec 64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = outPtr)
    (hx1 : s.readReg64 .x1 = coroPtr)
    (hx2 : s.readReg64 .x2 = ctxPtr) :
    SepWP (trTrapProgAt b C abs) loadShimAddr s
      (decryptPrekeyCoroInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
        sessStorePtr sessStoreVt idStorePtr idStoreVt
        preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
        kyberStorePtr kyberStoreVt rngPtr ∗
       cells (coroPtr + 0x70#64) 14 ∗
       ((coroPtr + 0x2c0#64) ↦₈ 0#8) ∗
       ((sessStoreVt + 0x18#64) ↦₆₄ᵣ loadShimAddr) ∗
       ((s.sp - 0xcd0#64) ↦₆₄ v_sp0) ∗
       cells (s.sp - 0x60#64) 12)
      (fun s1 P_f =>
        (P_f ⊢
          decryptPrekeyCoroInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
            sessStorePtr sessStoreVt idStorePtr idStoreVt
            preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
            kyberStorePtr kyberStoreVt rngPtr ∗
          decryptPrekeyCoroCopyAt coroPtr msgPtr remoteAddrPtr localAddrPtr
            sessStorePtr sessStoreVt idStorePtr idStoreVt
            preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
            kyberStorePtr kyberStoreVt rngPtr ∗
          ((coroPtr + 0x2c0#64) ↦₈ 0#8) ∗
          ((sessStoreVt + 0x18#64) ↦₆₄ᵣ loadShimAddr) ∗
          ((s.sp - 0xcd0#64) ↦₆₄ 0#64) ∗
          decryptPrekeySavedRegsAt s.sp s) ∧
        s1.sp = s.sp - 0xcd0#64 ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = sessStorePtr ∧
        s1.readReg64 .x1 = remoteAddrPtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x21 = s.readReg64 .x21 ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = (s.sp - 0xcd0#64) + 0x370#64 ∧
        s1.readReg64 .x25 = (s.sp - 0xcd0#64) + 0x210#64 ∧
        s1.readReg64 .x26 = outPtr ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = (s.sp - 0xcd0#64) + 0xa90#64 ∧
        s1.readReg64 .x29 = s.sp - 0x60#64 ∧
        s1.readReg64 .x30 =
          (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x130#64) := by
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x0 0x40
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x88 0x90
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0xe4 0x12c
  dsimp only [trTrapProgAt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  subst hx0 hx1 hx2
  dsimp only [decryptPrekeyCoroInitAt]
  conv =>
    arg 4
    simp (config := { maxSteps := 1000000 }) only [
      cells, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub,
      bv_sub_add_lit, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat (refine SepWP.exists_elim fun _ => ?_)
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) ?_
  refine ⟨?_, by simp [arm64_norm], rfl,
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm]⟩
  dsimp only [decryptPrekeyCoroInitAt, decryptPrekeyCoroCopyAt, decryptPrekeySavedRegsAt,
    Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28,
      Reg.x29, Reg.x30]
  exact Entails.of_eq (by ac_rfl)

/-- Segment P1.1 (`+0x0000 → +0x012c`): frame prologue (`sp - 0xcd0`), initial state check
`[coroPtr + 0x2c0] == 0`, 14-word coroutine copy, and `load_session` shim call (`blr x8`). -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p1_seg1_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (outPtr coroPtr ctxPtr
    msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr sessStoreVt idStorePtr idStoreVt
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr
    loadShimAddr v_sp0 : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = outPtr)
    (hx1 : s.readReg64 .x1 = coroPtr)
    (hx2 : s.readReg64 .x2 = ctxPtr) :
    SepWP (tripleRatchetProgAt b C ctl abs) loadShimAddr s
      (decryptPrekeyCoroInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
        sessStorePtr sessStoreVt idStorePtr idStoreVt
        preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
        kyberStorePtr kyberStoreVt rngPtr ∗
       cells (coroPtr + 0x70#64) 14 ∗
       ((coroPtr + 0x2c0#64) ↦₈ 0#8) ∗
       ((sessStoreVt + 0x18#64) ↦₆₄ᵣ loadShimAddr) ∗
       ((s.sp - 0xcd0#64) ↦₆₄ v_sp0) ∗
       cells (s.sp - 0x60#64) 12)
      (fun s1 P_f =>
        (P_f ⊢
          decryptPrekeyCoroInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
            sessStorePtr sessStoreVt idStorePtr idStoreVt
            preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
            kyberStorePtr kyberStoreVt rngPtr ∗
          decryptPrekeyCoroCopyAt coroPtr msgPtr remoteAddrPtr localAddrPtr
            sessStorePtr sessStoreVt idStorePtr idStoreVt
            preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
            kyberStorePtr kyberStoreVt rngPtr ∗
          ((coroPtr + 0x2c0#64) ↦₈ 0#8) ∗
          ((sessStoreVt + 0x18#64) ↦₆₄ᵣ loadShimAddr) ∗
          ((s.sp - 0xcd0#64) ↦₆₄ 0#64) ∗
          decryptPrekeySavedRegsAt s.sp s) ∧
        s1.sp = s.sp - 0xcd0#64 ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = sessStorePtr ∧
        s1.readReg64 .x1 = remoteAddrPtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x21 = s.readReg64 .x21 ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = (s.sp - 0xcd0#64) + 0x370#64 ∧
        s1.readReg64 .x25 = (s.sp - 0xcd0#64) + 0x210#64 ∧
        s1.readReg64 .x26 = outPtr ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = (s.sp - 0xcd0#64) + 0xa90#64 ∧
        s1.readReg64 .x29 = s.sp - 0x60#64 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x130#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p1_seg1_wp_trap b C abs s outPtr coroPtr
      ctxPtr msgPtr remoteAddrPtr localAddrPtr sessStorePtr sessStoreVt idStorePtr idStoreVt
      preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt rngPtr
      loadShimAddr v_sp0 hpc hrun hsp_align hx0 hx1 hx2)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p1_seg2_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr ctxPtr loadFutPtr loadFutVt loadPollAddr u0 u1 : BitVec 64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x130#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = loadFutPtr)
    (hx1 : s.readReg64 .x1 = loadFutVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr) :
    SepWP (trTrapProgAt b C abs) loadPollAddr s
      (((coroPtr + 0x2c8#64) ↦₆₄ u0) ∗
       ((coroPtr + 0x2d0#64) ↦₆₄ u1) ∗
       ((loadFutVt + 0x18#64) ↦₆₄ᵣ loadPollAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x2c8#64) ↦₆₄ loadFutPtr) ∗
          ((coroPtr + 0x2d0#64) ↦₆₄ loadFutVt) ∗
          ((loadFutVt + 0x18#64) ↦₆₄ᵣ loadPollAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = loadFutPtr ∧
        s1.readReg64 .x1 = ctxPtr ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x14c#64) := by
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x130 0x148
  dsimp only [trTrapProgAt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  subst hx0 hx1 hx19 hx27
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩

/-- Segment P1.2 (`+0x0130 → +0x0148`): stores `(loadFutPtr, loadFutVt)` at `coroPtr + 0x2c8..0x2d0`
and polls the `load_session` future (`blr x9`). -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p1_seg2_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr ctxPtr loadFutPtr loadFutVt loadPollAddr u0 u1 : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x130#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = loadFutPtr)
    (hx1 : s.readReg64 .x1 = loadFutVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr) :
    SepWP (tripleRatchetProgAt b C ctl abs) loadPollAddr s
      (((coroPtr + 0x2c8#64) ↦₆₄ u0) ∗
       ((coroPtr + 0x2d0#64) ↦₆₄ u1) ∗
       ((loadFutVt + 0x18#64) ↦₆₄ᵣ loadPollAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x2c8#64) ↦₆₄ loadFutPtr) ∗
          ((coroPtr + 0x2d0#64) ↦₆₄ loadFutVt) ∗
          ((loadFutVt + 0x18#64) ↦₆₄ᵣ loadPollAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = loadFutPtr ∧
        s1.readReg64 .x1 = ctxPtr ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x14c#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p1_seg2_wp_trap b C abs s coroPtr ctxPtr
      loadFutPtr loadFutVt loadPollAddr u0 u1 hpc hrun hx0 hx1 hx19 hx27)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p1_seg3_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr loadFutPtr loadFutVt loadDropAddr
    w_3e8 w_3f4 w_3fc w_404 w_40c u0 u1 u2 u3 : BitVec 64)
    (d_3f0 d_414 du4 : BitVec 32) (bs312 : List (BitVec 8))
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x14c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hbs312 : bs312.length = 312)
    (hdrop_nz : loadDropAddr ≠ 0#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = s.sp + 0x3e0#64)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) :
    SepWP (trTrapProgAt b C abs) loadDropAddr s
      (((coroPtr + 0x2c8#64) ↦₆₄ loadFutPtr) ∗
       ((coroPtr + 0x2d0#64) ↦₆₄ loadFutVt) ∗
       ((loadFutVt + 0x0#64) ↦₆₄ᵣ loadDropAddr) ∗
       memRegion (s.sp + 0xd8#64) 312 ∗
       ((s.sp + 0x210#64) ↦₆₄ u0) ∗ ((s.sp + 0x218#64) ↦₆₄ u1) ∗
       ((s.sp + 0x220#64) ↦₆₄ u2) ∗ ((s.sp + 0x228#64) ↦₆₄ u3) ∗
       ((s.sp + 0x230#64) ↦₃₂ du4) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
       ((s.sp + 0x3e8#64) ↦₆₄ w_3e8) ∗
       ((s.sp + 0x3f0#64) ↦₃₂ d_3f0) ∗
       ((s.sp + 0x3f4#64) ↦₆₄ w_3f4) ∗
       ((s.sp + 0x3fc#64) ↦₆₄ w_3fc) ∗
       ((s.sp + 0x404#64) ↦₆₄ w_404) ∗
       ((s.sp + 0x40c#64) ↦₆₄ w_40c) ∗
       ((s.sp + 0x414#64) ↦₃₂ d_414) ∗
       ((s.sp + 0x418#64) ↦ₛ bs312))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x2c8#64) ↦₆₄ loadFutPtr) ∗
          ((coroPtr + 0x2d0#64) ↦₆₄ loadFutVt) ∗
          ((loadFutVt + 0x0#64) ↦₆₄ᵣ loadDropAddr) ∗
          memRegion (s.sp + 0xd8#64) 348 ∗
          memRegion (s.sp + 0x3e0#64) 368) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = loadFutPtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = loadFutPtr ∧
        s1.readReg64 .x22 = d_3f0.zeroExtend 64 ∧
        s1.readReg64 .x23 = 0xffffffffffffffff#64 ∧
        s1.readReg64 .x24 = loadFutVt ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = w_3e8 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x238#64) := by
  have hmemcpy := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_memcpy_ok_trap (b := b) (C := C)
    (abs := abs)
  have hdrop_beq : (loadDropAddr == 0#64) = false := beq_eq_false_iff_ne.mpr hdrop_nz
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x14c 0x154
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x1f4 0x234
  dsimp only [trTrapProgAt] at hmemcpy hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = s.sp + 0x3e0#64 := hx21
  have hx24' : s.readReg64 (Reg.gpr 24#5) = s.sp + 0x370#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  wp_steps
  conv =>
    arg 4
    rw [show memRegion (s.sp + 0xd8#64) 312 =
      memRegion (s.sp + 0xd8#64) bs312.length by rw [hbs312]]
  wp_call hmemcpy (s.sp + 0xd8#64, s.sp + 0x418#64, bs312)
  apply SepWP.fold
    (loadSessionScratch_fold_p1 s.sp 0xffffffffffffffff#64 w_3e8 w_3f4 w_3fc w_404 w_40c
      w_3f4 w_3fc w_404 w_40c d_3f0 d_414 d_414 hbs312)
    (by sep_focus)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- Segment P1.3 (`+0x014c → +0x0234`): handles `Poll::Ready(Ok(None))`, copies the 36-byte header
and 312-byte payload (`memcpy`), and invokes `loadDropAddr` (`blr x8`). -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p1_seg3_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr loadFutPtr loadFutVt loadDropAddr
    w_3e8 w_3f4 w_3fc w_404 w_40c u0 u1 u2 u3 : BitVec 64)
    (d_3f0 d_414 du4 : BitVec 32) (bs312 : List (BitVec 8))
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x14c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hbs312 : bs312.length = 312)
    (hdrop_nz : loadDropAddr ≠ 0#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = s.sp + 0x3e0#64)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) :
    SepWP (tripleRatchetProgAt b C ctl abs) loadDropAddr s
      (((coroPtr + 0x2c8#64) ↦₆₄ loadFutPtr) ∗
       ((coroPtr + 0x2d0#64) ↦₆₄ loadFutVt) ∗
       ((loadFutVt + 0x0#64) ↦₆₄ᵣ loadDropAddr) ∗
       memRegion (s.sp + 0xd8#64) 312 ∗
       ((s.sp + 0x210#64) ↦₆₄ u0) ∗ ((s.sp + 0x218#64) ↦₆₄ u1) ∗
       ((s.sp + 0x220#64) ↦₆₄ u2) ∗ ((s.sp + 0x228#64) ↦₆₄ u3) ∗
       ((s.sp + 0x230#64) ↦₃₂ du4) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
       ((s.sp + 0x3e8#64) ↦₆₄ w_3e8) ∗
       ((s.sp + 0x3f0#64) ↦₃₂ d_3f0) ∗
       ((s.sp + 0x3f4#64) ↦₆₄ w_3f4) ∗
       ((s.sp + 0x3fc#64) ↦₆₄ w_3fc) ∗
       ((s.sp + 0x404#64) ↦₆₄ w_404) ∗
       ((s.sp + 0x40c#64) ↦₆₄ w_40c) ∗
       ((s.sp + 0x414#64) ↦₃₂ d_414) ∗
       ((s.sp + 0x418#64) ↦ₛ bs312))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x2c8#64) ↦₆₄ loadFutPtr) ∗
          ((coroPtr + 0x2d0#64) ↦₆₄ loadFutVt) ∗
          ((loadFutVt + 0x0#64) ↦₆₄ᵣ loadDropAddr) ∗
          memRegion (s.sp + 0xd8#64) 348 ∗
          memRegion (s.sp + 0x3e0#64) 368) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = loadFutPtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = loadFutPtr ∧
        s1.readReg64 .x22 = d_3f0.zeroExtend 64 ∧
        s1.readReg64 .x23 = 0xffffffffffffffff#64 ∧
        s1.readReg64 .x24 = loadFutVt ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = w_3e8 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x238#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p1_seg3_wp_trap b C abs s coroPtr loadFutPtr
      loadFutVt loadDropAddr w_3e8 w_3f4 w_3fc w_404 w_40c u0 u1 u2 u3 d_3f0 d_414 du4 bs312
      hpc hrun hsp_align hbs312 hdrop_nz hx19 hx21 hx24 hx25)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p1_seg4_wp_trap {A : RustAlloc} (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s : State) (coroPtr loadFutPtr loadFutVt trustShimAddr
    msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr sessStoreVt idStorePtr idStoreVt
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr : BitVec 64)
    (loadBoxSize : Nat) (b_390 : BitVec 8)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x238#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hbs_nz : BitVec.ofNat 64 loadBoxSize ≠ 0#64)
    (hbs_lt : loadBoxSize < 2 ^ 64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = loadFutPtr)
    (hx23 : s.readReg64 .x23 = 0xffffffffffffffff#64)
    (hx24 : s.readReg64 .x24 = loadFutVt) :
    SepWP (trTrapProgAt b C abs) trustShimAddr s
      (((loadFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 loadBoxSize) ∗
       ((loadFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.live loadFutPtr loadBoxSize 8 ∗
       memRegion loadFutPtr loadBoxSize ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       decryptPrekeyCoroCopyAt coroPtr msgPtr remoteAddrPtr localAddrPtr
         sessStorePtr sessStoreVt idStorePtr idStoreVt
         preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
         kyberStorePtr kyberStoreVt rngPtr ∗
       cells (coroPtr + 0xe0#64) 4 ∗
       cells (coroPtr + 0x2c8#64) 25 ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((idStoreVt + 0x30#64) ↦₆₄ᵣ trustShimAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((loadFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 loadBoxSize) ∗
          ((loadFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          decryptPrekeyCoroCopyAt coroPtr msgPtr remoteAddrPtr localAddrPtr
            sessStorePtr sessStoreVt idStorePtr idStoreVt
            preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
            kyberStorePtr kyberStoreVt rngPtr ∗
          sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗
          processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
            idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
            spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
          ((coroPtr + 0x390#64) ↦₈ 0#8) ∗
          ((idStoreVt + 0x30#64) ↦₆₄ᵣ trustShimAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = idStorePtr ∧
        s1.readReg64 .x1 = remoteAddrPtr ∧
        s1.readReg64 .x2 = msgPtr + 0xc8#64 ∧
        s1.readReg64 .x3 = 1#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = coroPtr + 0x390#64 ∧
        s1.readReg64 .x23 = 0#64 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 8#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x650#64) := by
  have hdealloc := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_dealloc_ok_trap (b := b) (C := C)
    (abs := abs) hA
  have hbs_beq : (BitVec.ofNat 64 loadBoxSize == 0#64) = false := beq_eq_false_iff_ne.mpr hbs_nz
  have hbs_toNat : (BitVec.ofNat 64 loadBoxSize).toNat = loadBoxSize := Nat.mod_eq_of_lt hbs_lt
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x238 0x250
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x4c0 0x4c8
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x578 0x64c
  dsimp only [trTrapProgAt] at hdealloc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = loadFutPtr := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = loadFutVt := hx24
  dsimp only [decryptPrekeyCoroCopyAt]
  conv =>
    arg 4
    simp (config := { maxSteps := 1000000 }) only [
      cells, BitVec.add_assoc, BitVec.reduceAdd,
      sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat (refine SepWP.exists_elim fun _ => ?_)
  wp_steps
  wp_call hdealloc (loadFutPtr, loadBoxSize, 8)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨?_, by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩
  dsimp only [decryptPrekeyCoroCopyAt, sessionRecordEmptyHeaderAt, processPrekeyInnerInitAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact Entails.of_eq (by ac_rfl)

/-- Segment P1.4 (`+0x0238 → +0x064c`): deallocates `loadFutPtr`, initializes an empty
`SessionRecord` (`coroPtr + 0xe0..0x100`) and `process_prekey_impl` frame (`coroPtr + 0x2c8..0x390`),
and invokes `is_trusted_identity` (`blr x8`). -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p1_seg4_wp {A : RustAlloc} (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s : State) (coroPtr loadFutPtr loadFutVt trustShimAddr
    msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr sessStoreVt idStorePtr idStoreVt
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr : BitVec 64)
    (loadBoxSize : Nat) (b_390 : BitVec 8)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x238#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hbs_nz : BitVec.ofNat 64 loadBoxSize ≠ 0#64)
    (hbs_lt : loadBoxSize < 2 ^ 64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = loadFutPtr)
    (hx23 : s.readReg64 .x23 = 0xffffffffffffffff#64)
    (hx24 : s.readReg64 .x24 = loadFutVt) :
    SepWP (tripleRatchetProgAt b C ctl abs) trustShimAddr s
      (((loadFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 loadBoxSize) ∗
       ((loadFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.live loadFutPtr loadBoxSize 8 ∗
       memRegion loadFutPtr loadBoxSize ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       decryptPrekeyCoroCopyAt coroPtr msgPtr remoteAddrPtr localAddrPtr
         sessStorePtr sessStoreVt idStorePtr idStoreVt
         preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
         kyberStorePtr kyberStoreVt rngPtr ∗
       cells (coroPtr + 0xe0#64) 4 ∗
       cells (coroPtr + 0x2c8#64) 25 ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((idStoreVt + 0x30#64) ↦₆₄ᵣ trustShimAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((loadFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 loadBoxSize) ∗
          ((loadFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          decryptPrekeyCoroCopyAt coroPtr msgPtr remoteAddrPtr localAddrPtr
            sessStorePtr sessStoreVt idStorePtr idStoreVt
            preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
            kyberStorePtr kyberStoreVt rngPtr ∗
          sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗
          processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
            idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
            spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
          ((coroPtr + 0x390#64) ↦₈ 0#8) ∗
          ((idStoreVt + 0x30#64) ↦₆₄ᵣ trustShimAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = idStorePtr ∧
        s1.readReg64 .x1 = remoteAddrPtr ∧
        s1.readReg64 .x2 = msgPtr + 0xc8#64 ∧
        s1.readReg64 .x3 = 1#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = coroPtr + 0x390#64 ∧
        s1.readReg64 .x23 = 0#64 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 8#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x650#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p1_seg4_wp_trap b C abs hA s coroPtr
      loadFutPtr loadFutVt trustShimAddr msgPtr remoteAddrPtr localAddrPtr sessStorePtr
      sessStoreVt idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
      kyberStorePtr kyberStoreVt rngPtr loadBoxSize b_390 hpc hrun hsp_align hbs_nz hbs_lt
      hx19 hx21 hx23 hx24)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p1_seg5_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr ctxPtr trustFutPtr trustFutVt trustPollAddr u0 u1 u2 : BitVec 64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x650#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = trustFutPtr)
    (hx1 : s.readReg64 .x1 = trustFutVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr) :
    SepWP (trTrapProgAt b C abs) trustPollAddr s
      (((coroPtr + 0x398#64) ↦₆₄ u0) ∗
       ((coroPtr + 0x3a0#64) ↦₆₄ u1) ∗
       ((s.sp + 0xc0#64) ↦₆₄ u2) ∗
       ((trustFutVt + 0x18#64) ↦₆₄ᵣ trustPollAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x398#64) ↦₆₄ trustFutPtr) ∗
          ((coroPtr + 0x3a0#64) ↦₆₄ trustFutVt) ∗
          ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          ((trustFutVt + 0x18#64) ↦₆₄ᵣ trustPollAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = trustFutPtr ∧
        s1.readReg64 .x1 = ctxPtr ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = s.readReg64 .x21 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x66c#64) := by
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x650 0x668
  dsimp only [trTrapProgAt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  subst hx0 hx1 hx19 hx27
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩

/-- Segment P1.5 (`+0x0650 → +0x0668`): stores `(trustFutPtr, trustFutVt)` at `coroPtr + 0x398..0x3a0`
and polls the `is_trusted_identity` future (`blr x9`). -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p1_seg5_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr ctxPtr trustFutPtr trustFutVt trustPollAddr u0 u1 u2 : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x650#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = trustFutPtr)
    (hx1 : s.readReg64 .x1 = trustFutVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr) :
    SepWP (tripleRatchetProgAt b C ctl abs) trustPollAddr s
      (((coroPtr + 0x398#64) ↦₆₄ u0) ∗
       ((coroPtr + 0x3a0#64) ↦₆₄ u1) ∗
       ((s.sp + 0xc0#64) ↦₆₄ u2) ∗
       ((trustFutVt + 0x18#64) ↦₆₄ᵣ trustPollAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x398#64) ↦₆₄ trustFutPtr) ∗
          ((coroPtr + 0x3a0#64) ↦₆₄ trustFutVt) ∗
          ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          ((trustFutVt + 0x18#64) ↦₆₄ᵣ trustPollAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = trustFutPtr ∧
        s1.readReg64 .x1 = ctxPtr ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = s.readReg64 .x21 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x66c#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p1_seg5_wp_trap b C abs s coroPtr ctxPtr
      trustFutPtr trustFutVt trustPollAddr u0 u1 u2 hpc hrun hsp_align hx0 hx1 hx19 hx27)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p1_seg6a_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr outPtr trustFutPtr trustFutVt trustDropAddr
    w_3f0 w_400 w_408 u_a8 u_b0 u_b8 u_c8 u_d0 : BitVec 64)
    (d_3e9 d_3f8 d_3fc : BitVec 32) (h_3ed : BitVec 16) (b_3ef : BitVec 8)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x66c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hdrop_nz : trustDropAddr ≠ 0#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = coroPtr + 0x390#64)
    (hx26 : s.readReg64 .x26 = outPtr) :
    SepWP (trTrapProgAt b C abs) trustDropAddr s
      (((coroPtr + 0x398#64) ↦₆₄ trustFutPtr) ∗
       ((coroPtr + 0x3a0#64) ↦₆₄ trustFutVt) ∗
       ((trustFutVt + 0x0#64) ↦₆₄ᵣ trustDropAddr) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((s.sp + 0xc8#64) ↦₆₄ u_c8) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
       ((s.sp + 0x3e8#64) ↦₈ 1#8) ∗
       ((s.sp + 0x3e9#64) ↦₃₂ d_3e9) ∗
       ((s.sp + 0x3ed#64) ↦₁₆ h_3ed) ∗
       ((s.sp + 0x3ef#64) ↦₈ b_3ef) ∗
       ((s.sp + 0x3f0#64) ↦₆₄ w_3f0) ∗
       ((s.sp + 0x3f8#64) ↦₃₂ d_3f8) ∗
       ((s.sp + 0x3fc#64) ↦₃₂ d_3fc) ∗
       ((s.sp + 0x400#64) ↦₆₄ w_400) ∗
       ((s.sp + 0x408#64) ↦₆₄ w_408))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x398#64) ↦₆₄ trustFutPtr) ∗
          ((coroPtr + 0x3a0#64) ↦₆₄ trustFutVt) ∗
          ((trustFutVt + 0x0#64) ↦₆₄ᵣ trustDropAddr) ∗
          ((s.sp + 0xa8#64) ↦₆₄ d_3fc.zeroExtend 64) ∗
          ((s.sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
          ((s.sp + 0xb8#64) ↦₆₄ w_3f0) ∗
          ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((s.sp + 0xd0#64) ↦₆₄ d_3f8.zeroExtend 64) ∗
          memRegion (s.sp + 0x3e0#64) 48) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = trustFutPtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = 0xfffffffffffffffe#64 ∧
        s1.readReg64 .x21 = trustFutPtr ∧
        s1.readReg64 .x23 = 1#64 ∧
        s1.readReg64 .x25 = trustFutVt ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x6d0#64) := by
  have hdrop_beq : (trustDropAddr == 0#64) = false := beq_eq_false_iff_ne.mpr hdrop_nz
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x66c 0x674
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x680 0x6cc
  dsimp only [trTrapProgAt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = coroPtr + 0x390#64 := hx21
  have hx26' : s.readReg64 (Reg.gpr 26#5) = outPtr := hx26
  wp_steps
  apply SepWP.fold
    (trustOut48_fold_p1 s.sp 0xfffffffffffffffe#64 1#8 d_3e9 h_3ed b_3ef w_3f0 d_3f8 d_3fc w_400
      w_408)
    (by sep_focus)
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- Segment P1.6a (`+0x066c → +0x06cc`): reads `Poll::Ready(Ok(true))`, spills `(outPtr, coroPtr + 0x390)`,
and invokes `trustDropAddr` (`blr x8`). -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p1_seg6a_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr outPtr trustFutPtr trustFutVt trustDropAddr
    w_3f0 w_400 w_408 u_a8 u_b0 u_b8 u_c8 u_d0 : BitVec 64)
    (d_3e9 d_3f8 d_3fc : BitVec 32) (h_3ed : BitVec 16) (b_3ef : BitVec 8)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x66c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hdrop_nz : trustDropAddr ≠ 0#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = coroPtr + 0x390#64)
    (hx26 : s.readReg64 .x26 = outPtr) :
    SepWP (tripleRatchetProgAt b C ctl abs) trustDropAddr s
      (((coroPtr + 0x398#64) ↦₆₄ trustFutPtr) ∗
       ((coroPtr + 0x3a0#64) ↦₆₄ trustFutVt) ∗
       ((trustFutVt + 0x0#64) ↦₆₄ᵣ trustDropAddr) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((s.sp + 0xc8#64) ↦₆₄ u_c8) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
       ((s.sp + 0x3e8#64) ↦₈ 1#8) ∗
       ((s.sp + 0x3e9#64) ↦₃₂ d_3e9) ∗
       ((s.sp + 0x3ed#64) ↦₁₆ h_3ed) ∗
       ((s.sp + 0x3ef#64) ↦₈ b_3ef) ∗
       ((s.sp + 0x3f0#64) ↦₆₄ w_3f0) ∗
       ((s.sp + 0x3f8#64) ↦₃₂ d_3f8) ∗
       ((s.sp + 0x3fc#64) ↦₃₂ d_3fc) ∗
       ((s.sp + 0x400#64) ↦₆₄ w_400) ∗
       ((s.sp + 0x408#64) ↦₆₄ w_408))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x398#64) ↦₆₄ trustFutPtr) ∗
          ((coroPtr + 0x3a0#64) ↦₆₄ trustFutVt) ∗
          ((trustFutVt + 0x0#64) ↦₆₄ᵣ trustDropAddr) ∗
          ((s.sp + 0xa8#64) ↦₆₄ d_3fc.zeroExtend 64) ∗
          ((s.sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
          ((s.sp + 0xb8#64) ↦₆₄ w_3f0) ∗
          ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((s.sp + 0xd0#64) ↦₆₄ d_3f8.zeroExtend 64) ∗
          memRegion (s.sp + 0x3e0#64) 48) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = trustFutPtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = 0xfffffffffffffffe#64 ∧
        s1.readReg64 .x21 = trustFutPtr ∧
        s1.readReg64 .x23 = 1#64 ∧
        s1.readReg64 .x25 = trustFutVt ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x6d0#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p1_seg6a_wp_trap b C abs s coroPtr outPtr
      trustFutPtr trustFutVt trustDropAddr w_3f0 w_400 w_408 u_a8 u_b0 u_b8 u_c8 u_d0
      d_3e9 d_3f8 d_3fc h_3ed b_3ef hpc hrun hsp_align hdrop_nz hx19 hx21 hx26)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p1_seg6b_wp_trap {A : RustAlloc} (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s : State) (coroPtr trustFutPtr trustFutVt
    msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt
    u_98 u_a0 : BitVec 64)
    (trustBoxSize : Nat) (b_4f2 : BitVec 8)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x6d0#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hbs_nz : BitVec.ofNat 64 trustBoxSize ≠ 0#64)
    (hbs_lt : trustBoxSize < 2 ^ 64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = 0xfffffffffffffffe#64)
    (hx21 : s.readReg64 .x21 = trustFutPtr)
    (hx23 : s.readReg64 .x23 = 1#64)
    (hx25 : s.readReg64 .x25 = trustFutVt) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x868#64) s
      (((trustFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 trustBoxSize) ∗
       ((trustFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.live trustFutPtr trustBoxSize 8 ∗
       memRegion trustFutPtr trustBoxSize ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
         idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
         spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
       cells (coroPtr + 0x428#64) 8 ∗
       cells (coroPtr + 0x490#64) 4 ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       ((s.sp + 0x98#64) ↦₆₄ u_98) ∗
       ((s.sp + 0xa0#64) ↦₆₄ u_a0))
      (fun s1 P_f =>
        (P_f ⊢
          ((trustFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 trustBoxSize) ∗
          ((trustFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
            idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
            spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
          processPrekeyPostTrustAt coroPtr msgPtr remoteAddrPtr localAddrPtr
            idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
            spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
          ((coroPtr + 0x4f2#64) ↦₈ 0#8) ∗
          ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((s.sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64))) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x8 = kyberStorePtr ∧
        s1.readReg64 .x9 = msgPtr ∧
        s1.readReg64 .x10 = kyberStoreVt ∧
        s1.readReg64 .x11 = preKeyStorePtr ∧
        s1.readReg64 .x12 = remoteAddrPtr ∧
        s1.readReg64 .x13 = preKeyStoreVt ∧
        s1.readReg64 .x14 = localAddrPtr ∧
        s1.readReg64 .x15 = idStorePtr ∧
        s1.readReg64 .x16 = idStoreVt ∧
        s1.readReg64 .x17 = coroPtr + 0x4f2#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = 0xfffffffffffffffe#64 ∧
        s1.readReg64 .x21 = trustFutPtr ∧
        s1.readReg64 .x22 = spkStorePtr ∧
        s1.readReg64 .x23 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x24 = spkStoreVt ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  have hdealloc := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_dealloc_ok_trap (b := b) (C := C)
    (abs := abs) hA
  have hbs_beq : (BitVec.ofNat 64 trustBoxSize == 0#64) = false := beq_eq_false_iff_ne.mpr hbs_nz
  have hbs_toNat : (BitVec.ofNat 64 trustBoxSize).toNat = trustBoxSize := Nat.mod_eq_of_lt hbs_lt
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x6d0 0x76c
  dsimp only [trTrapProgAt] at hdealloc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = 0xfffffffffffffffe#64 := hx20
  have hx21' : s.readReg64 (Reg.gpr 21#5) = trustFutPtr := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = 1#64 := hx23
  have hx25' : s.readReg64 (Reg.gpr 25#5) = trustFutVt := hx25
  dsimp only [processPrekeyInnerInitAt]
  conv =>
    arg 4
    simp (config := { maxSteps := 1000000 }) only [
      cells, BitVec.add_assoc, BitVec.reduceAdd,
      sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat (refine SepWP.exists_elim fun _ => ?_)
  wp_steps
  wp_call hdealloc (trustFutPtr, trustBoxSize, 8)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨?_, by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩
  dsimp only [processPrekeyInnerInitAt, processPrekeyPostTrustAt]
  exact Entails.of_eq (by ac_rfl)

/-- Segment P1.6b (`+0x06d0 → +0x0868`): deallocates `trustFutPtr`, checks `trusted == true`,
populates `processPrekeyPostTrustAt`, and branches to Stage P2 (`+0x0868`). -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p1_seg6b_wp {A : RustAlloc} (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s : State) (coroPtr trustFutPtr trustFutVt
    msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt
    u_98 u_a0 : BitVec 64)
    (trustBoxSize : Nat) (b_4f2 : BitVec 8)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x6d0#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hbs_nz : BitVec.ofNat 64 trustBoxSize ≠ 0#64)
    (hbs_lt : trustBoxSize < 2 ^ 64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = 0xfffffffffffffffe#64)
    (hx21 : s.readReg64 .x21 = trustFutPtr)
    (hx23 : s.readReg64 .x23 = 1#64)
    (hx25 : s.readReg64 .x25 = trustFutVt) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x868#64) s
      (((trustFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 trustBoxSize) ∗
       ((trustFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.live trustFutPtr trustBoxSize 8 ∗
       memRegion trustFutPtr trustBoxSize ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
         idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
         spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
       cells (coroPtr + 0x428#64) 8 ∗
       cells (coroPtr + 0x490#64) 4 ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       ((s.sp + 0x98#64) ↦₆₄ u_98) ∗
       ((s.sp + 0xa0#64) ↦₆₄ u_a0))
      (fun s1 P_f =>
        (P_f ⊢
          ((trustFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 trustBoxSize) ∗
          ((trustFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
            idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
            spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
          processPrekeyPostTrustAt coroPtr msgPtr remoteAddrPtr localAddrPtr
            idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
            spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
          ((coroPtr + 0x4f2#64) ↦₈ 0#8) ∗
          ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((s.sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64))) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x8 = kyberStorePtr ∧
        s1.readReg64 .x9 = msgPtr ∧
        s1.readReg64 .x10 = kyberStoreVt ∧
        s1.readReg64 .x11 = preKeyStorePtr ∧
        s1.readReg64 .x12 = remoteAddrPtr ∧
        s1.readReg64 .x13 = preKeyStoreVt ∧
        s1.readReg64 .x14 = localAddrPtr ∧
        s1.readReg64 .x15 = idStorePtr ∧
        s1.readReg64 .x16 = idStoreVt ∧
        s1.readReg64 .x17 = coroPtr + 0x4f2#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = 0xfffffffffffffffe#64 ∧
        s1.readReg64 .x21 = trustFutPtr ∧
        s1.readReg64 .x22 = spkStorePtr ∧
        s1.readReg64 .x23 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x24 = spkStoreVt ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p1_seg6b_wp_trap b C abs hA s coroPtr
      trustFutPtr trustFutVt msgPtr remoteAddrPtr localAddrPtr idStorePtr idStoreVt
      preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt
      u_98 u_a0 trustBoxSize b_4f2 hpc hrun hsp_align hbs_nz hbs_lt hx19 hx20 hx21 hx23 hx25)

end CryptoVerification.E2E.Pqxdh.ResponderClosure
