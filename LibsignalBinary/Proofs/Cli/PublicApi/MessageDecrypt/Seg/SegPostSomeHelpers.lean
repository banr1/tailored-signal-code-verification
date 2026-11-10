/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Proofs.Cli.Specifications.LibsignalTripleRatchet
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.Defs
import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.ExtDefs
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.TripleRatchet.Hooks

/-!
# CLI `SegPostSome` Instruction Decodes and Callee Helpers

Instruction decode tables and `remote_identity_key` callee lifting for `SegPostSome` in
`signal_session_ratchet::decrypt_signal`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostSome

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoVerification.RustHeap CryptoGames.LibsignalSession

open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalPublicApiRepr

open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession

open CryptoGames CryptoGames.LibsignalSessionApi

open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit

open CryptoVerification.LibsignalPublicApi.MessageDecrypt


set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Instruction decode lemmas -/

gen_decodes libsignalSessionCode_tree messageDecryptPostSomeBinCli [(ls_off% "libsignal_cli_ratchet::decrypt_signal" + 8016) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 8092), raw (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 8096), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 8100) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 8136), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 8372) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 8400), (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 9568) → (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 9588)]

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegPostSome.remoteIdentityKey_ok_at_msgDecrypt {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (h : OutgoingRatchet.RemoteIdentityKeyOk img C A ctl abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x1fa0#64 + bv% (((2^64 + ls_off% "<libsignal_protocol::state::session::SessionState>::remote_identity_key" - ls_off% "libsignal_cli_ratchet::decrypt_signal" - 8096) % 2^64)))
      (Getters.remoteIdentityKeySpec A img) := by
  have hk : BitVec.ofNat 64 (libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName) + 0x1fa0#64 +
      bv% (((2^64 + ls_off% "<libsignal_protocol::state::session::SessionState>::remote_identity_key" - ls_off% "libsignal_cli_ratchet::decrypt_signal" - 8096) % 2^64)) =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff Getters.remoteIdentityKeyName) := by
    simp only [arm64_norm]
  have haddr :
      (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x1fa0#64 + bv% (((2^64 + ls_off% "<libsignal_protocol::state::session::SessionState>::remote_identity_key" - ls_off% "libsignal_cli_ratchet::decrypt_signal" - 8096) % 2^64)) =
      (tripleRatchetProgAt img.base C ctl abs).fnAddr Getters.remoteIdentityKeyName := by
    simp only [tripleRatchetProgAt, Program.fnAddr_rebase]
    rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.add_assoc (BitVec.ofNat 64 _), hk]
  rwa [haddr]

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegPostSome.panic_at_expect_failed_msgDecrypt (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).externAt?
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + bv% ((2^64 + ls_off% "core::option::expect_failed" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64)) = some Rust.panicked :=
  panic_at_sym b C ctl abs CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName "core::option::expect_failed" num% (ls_off% "core::option::expect_failed" - ls_off% "libsignal_cli_ratchet::decrypt_signal")
    (by simp only [arm64_norm]) (hp := by simp [Rust.isPanicSymbol])

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegPostSome.remoteIdentityKey_ok_at_msgDecrypt_trap
    {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    (h : subroutine_ok (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr Getters.remoteIdentityKeyName)
      (Getters.remoteIdentityKeySpec A img)) :
    subroutine_ok (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
        0x1fa0#64 + bv% (((2^64 + ls_off% "<libsignal_protocol::state::session::SessionState>::remote_identity_key" - ls_off% "libsignal_cli_ratchet::decrypt_signal" - 8096) % 2^64)))
      (Getters.remoteIdentityKeySpec A img) :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT.remoteIdentityKey_ok_at_msgDecrypt_ext h

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegPostSome.panic_at_expect_failed_msgDecrypt_trap
    (b : BitVec 64) (C : Crypto) (abs : String → Option (State → State)) :
    (trTrapProgAt b C abs).externAt?
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
        bv% ((2^64 + ls_off% "core::option::expect_failed" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64)) =
      some Rust.panicked :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT.panic_at_expect_failed_msgDecrypt_ext
    b (trTrapExterns C abs)

end CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostSome
