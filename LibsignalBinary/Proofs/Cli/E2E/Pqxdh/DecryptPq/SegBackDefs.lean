/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegBackDefs

/-!
# Tail-Segment Fetch Macros and Callee Wrappers for CLI `try_decrypt_with_state::<Coins>`

Instruction-fetch macro `decrypt_fetches_cli`, branch-target and extern-stub lookup lemmas, and
`SepWPp` composition helpers shared by `SegBackS7`, `SegBackS8`, and `SegBackS9`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Getters

open CryptoVerification.LibsignalTripleRatchet.DecryptPq

open CryptoVerification.LibsignalSession

open ProofLib.ProgramReflection

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] BitVec.toNat_zero

namespace BS10

end BS10

/-- Instruction-fetch macro for `try_decrypt_with_state::<signal_session_handshake::Coins>` covering `len` bytes from function-relative offset `k0`. -/
macro "decrypt_fetches_cli " b:term:max C:term:max ctl:term:max abs:term:max
    hfn:ident k0:num len:num : tactic =>
  `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode libsignalTripleRatchetBinCli $b
    (Rust.withPanics (tripleRatchetExterns $C $ctl $abs)) $hfn (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") $k0 $len)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.hfn_tryDecrypt : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") :=
  (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")

/-! ## Branch Targets and Extern Hook Wrappers -/

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.tryDecryptEntry_eq_fnAddr {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (C : Crypto) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img = (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName :=
  entryOf_eq_tripleRatchetProgAt himg CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.segS7PC_eq {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (C : Crypto) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS7PC img
      = (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + BitVec.ofNat 64 0x63c := by
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS7PC, CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.tryDecryptEntry_eq_fnAddr himg]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.segS8PC_eq {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (C : Crypto) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS8PC img
      = (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + BitVec.ofNat 64 0x678 := by
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS8PC, CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.tryDecryptEntry_eq_fnAddr himg]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.segS9PC_eq {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (C : Crypto) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS9PC img
      = (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + BitVec.ofNat 64 0x6a4 := by
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS9PC, CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.tryDecryptEntry_eq_fnAddr himg]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.errTailPC_eq {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (C : Crypto) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.errTailPC img
      = (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + BitVec.ofNat 64 0x30c := by
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.errTailPC, CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.tryDecryptEntry_eq_fnAddr himg]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.bl_verifyMac_target (img : Obj.Image) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + bv% ((2^64 + ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64) =
      (tripleRatchetProgAt img.base C ctl abs).fnAddr verifyMacWithAddressesName := by
  unfold tripleRatchetProgAt
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"), libsignalSessionCode_fnOff_0x1d5a0]
  bv_omega

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.bl_trApply_target (img : Obj.Image) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + bv% ((2^64 + ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::apply_to_session_state" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64) =
      (tripleRatchetProgAt img.base C ctl abs).fnAddr trApplyName := by
  unfold tripleRatchetProgAt
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"), libsignalSessionCode_fnOff_0x1cbf4]
  bv_omega

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.bl_clearUpk_target (img : Obj.Image) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + bv% ((2^64 + ls_off% "<libsignal_protocol::state::session::SessionState>::clear_unacknowledged_pre_key_message" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64) =
      (tripleRatchetProgAt img.base C ctl abs).fnAddr clearUpkName := by
  unfold tripleRatchetProgAt
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"), libsignalSessionCode_fnOff_0x12404]
  bv_omega

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.shim_ok_at (img : Obj.Image) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + BitVec.ofNat 64 (num%
        (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))))
      sessionShimSpec :=
  hook_ok_at (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") (by decide) (by decide)
    (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2") (by simp [Rust.isPanicSymbol])
    ⟨hookNoop, rfl, sessionShim_hookOk⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.memcpy_ok_at (img : Obj.Image) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + BitVec.ofNat 64 (num%
        (ls_off% "memcpy" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))))
      sessionMemcpyRegionSpec :=
  hook_ok_at (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") (by decide) (by decide)
    (ls_hook% "memcpy") (by simp [Rust.isPanicSymbol])
    ⟨hookMemcpy, rfl, sessionMemcpyRegion_hookOk⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.alloc_ok_at (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (hS : TripleRatchetHooks C A S abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + BitVec.ofNat 64 (num%
        (ls_off% "__rustc::__rust_alloc" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))))
      (rustAllocSpec A) := by
  refine hook_ok_at (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") (by decide) (by decide)
    (ls_hook% "__rustc::__rust_alloc") (by simp [Rust.isPanicSymbol]) ?_
  obtain ⟨f, hf, hok⟩ := hS.alloc.alloc
  exact ⟨f, by simp [tripleRatchetExterns, sessionExterns, dhName, pubFromSecretName,
    staticDropName,
    sharedDropName, rngFillName,
    noHookNames, hf], hok⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.dealloc_ok_at (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (hS : TripleRatchetHooks C A S abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + BitVec.ofNat 64 (num%
        (ls_off% "__rustc::__rust_dealloc" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))))
      (rustDeallocSpec A) := by
  refine hook_ok_at (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") (by decide) (by decide)
    (ls_hook% "__rustc::__rust_dealloc") (by simp [Rust.isPanicSymbol]) ?_
  obtain ⟨f, hf, hok⟩ := hS.alloc.dealloc
  exact ⟨f, by simp [tripleRatchetExterns, sessionExterns, dhName, pubFromSecretName,
    staticDropName,
    sharedDropName, rngFillName,
    noHookNames, hf], hok⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.formatInner_ok_at (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (hS : TripleRatchetHooks C A S abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + BitVec.ofNat 64 (num%
        (ls_off% "alloc::fmt::format::format_inner" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))))
      (formatInnerSpec A) := by
  refine hook_ok_at (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") (by decide) (by decide)
    (ls_hook% "alloc::fmt::format::format_inner") (by simp [Rust.isPanicSymbol]) ?_
  obtain ⟨f, hf, hok⟩ := hS.formatInner
  exact ⟨f, by simp [tripleRatchetExterns, sessionExterns, dhName, pubFromSecretName,
    staticDropName,
    sharedDropName, rngFillName,
    noHookNames, hf], hok⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.aesDec_ok_at (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (hS : TripleRatchetHooks C A S abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + BitVec.ofNat 64 (num%
        (ls_off% "signal_crypto::aes_cbc::aes_256_cbc_decrypt" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))))
      (aesDecSpec C.D A) := by
  refine hook_ok_at (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") (by decide) (by decide)
    (ls_hook% "signal_crypto::aes_cbc::aes_256_cbc_decrypt") (by simp [Rust.isPanicSymbol]) ?_
  obtain ⟨f, hf, hok⟩ := hS.aesDec
  exact ⟨f, by simp [tripleRatchetExterns, sessionExterns, dhName, pubFromSecretName,
    staticDropName,
    sharedDropName, rngFillName,
    noHookNames, hf], hok⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.externAt_handle_error (img : Obj.Image) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt img.base C ctl abs).externAt?
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + BitVec.ofNat 64 (num%
        (ls_off% "alloc::raw_vec::handle_error" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")))) =
      some Rust.panicked :=
  panic_at_panicSymbol (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
    (by decide) (by decide) (ls_hook% "alloc::raw_vec::handle_error") (by simp [Rust.isPanicSymbol])

/-! ## `SepWPp` Segment and Panic Bridge Lemmas -/

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.tryDecrypt_onPanic_of_callee (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (img : Obj.Image)
    (x : TryDecryptGhost) (s0 sm sf : State) (F R : SepProp)
    (h0m : s0.trace <+: sm.trace)
    (hm : sf.mem ⊨ ((⌜allocFailedIn sm sf ∧ sm.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 sf ∗ R := by
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec Spec.inImage
  exact allowPanic_frame
    (fun ⟨haf, hmf⟩ => ⟨Or.inr (Or.inr (allocFailedIn_trans h0m haf)), h0m.trans hmf⟩) hm

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.tryDecrypt_onPanic_of_direct (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (img : Obj.Image)
    (x : TryDecryptGhost) (s0 sf : State) (P R : SepProp)
    (haf : allocFailedIn s0 sf) (htr : s0.trace <+: sf.trace)
    (hm : sf.mem ⊨ P ∗ R) :
    sf.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 sf ∗ R := by
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec Spec.inImage
  exact allowPanic_panicked ⟨Or.inr (Or.inr haf), htr⟩ hm

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.panic_direct (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (img : Obj.Image)
    (abs : String → Option (State → State))
    (x : TryDecryptGhost) (s0 s : State) (ret panic_pc : BitVec 64)
    (P R : SepProp) {Q : State → SepProp → Prop}
    (hpc : s.pc = panic_pc) (hrun : s.status = .Running)
    (hext : (tripleRatchetProgAt img.base C ctl abs).externAt? panic_pc = some Rust.panicked)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAt img.base C ctl abs) ret s P Q
      (fun sf P_f => sf.status = .Panicked → (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 sf ∗ R)) := by
  refine SepWPp.panic_at hpc hrun hext fun _ hm_pan => ?_
  have htr_f : (Rust.panicked s).trace = s0.trace ++ [allocFailedEvent] := htr
  have haf : allocFailedIn s0 (Rust.panicked s) := by
    unfold allocFailedIn
    rw [htr_f, List.drop_left]
    exact List.Mem.head _
  have hpre : s0.trace <+: (Rust.panicked s).trace := by
    rw [htr_f]
    exact ⟨[allocFailedEvent], rfl⟩
  exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.tryDecrypt_onPanic_of_direct C A ctl S img x s0 (Rust.panicked s) P R haf hpre hm_pan

end CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD
