/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegDhDefs
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SignalSession.Coins.Fill
import ProofLib.SepLogic.WPp

/-!
# Trap-at-RNG Segment S3 Callee Helpers

Provides `signal_session_coins_fill` (`coinsFillAtSpec`) and `StaticSecret::drop` callee
helpers for `try_decrypt_with_state::<signal_session_handshake::Coins>` on `trTrapProgAt`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegB

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Getters

open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet

open CryptoVerification.LibsignalTripleRatchet.DecryptPq

open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace ChainArrayBytes

end ChainArrayBytes

namespace BS10

/-- The `try_decrypt_with_state::<signal_session_handshake::Coins>` `+0x77c` callee
(`bl signal_session_coins_fill`, a real function in the CLI image) meets
`coinsFillAtSpec b tryDecryptSubStack cur rest` (replaces `rngFill_ok_at2_td`). -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.BS10.coinsFillAt_ok_td_trap
    {b : BitVec 64} {C : Crypto} {A : RustAlloc} {cur : BitVec 64}
    {rest : List (BitVec 8)} {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) (hb : b &&& 0xfff#64 = 0#64) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + bv% ((2^64 + ls_off%
        "signal_session_coins_fill" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")) % 2^64))
      (CryptoVerification.SignalSession.Coins.coinsFillAtSpec b tryDecryptSubStack cur rest) :=
  CryptoVerification.SignalSession.Coins.coinsFillAt_of_after0
    (CryptoVerification.SignalSession.Coins.coinsFill_ok_at (ext := trTrapExterns C abs)
      (AllocContracts.of_tripleRatchetProgAt_trap b C A abs hA) hb tryDecryptSubStack (by decide) (by decide)
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName
      (num% (ls_off% "signal_session_coins_fill" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))
      (by fnoff_eq))

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.BS10.staticDrop_ok_at2_td_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + bv% ((2^64 + ls_off%
        "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")) % 2^64))
      zeroizeSecretSpec :=
  hook_ok_at (hname := staticDropName) (off := (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")) (stub :=
    num% (ls_off% "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop")) (k :=
    num% (ls_off% "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")))
    (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") rfl (by decide)
    (ls_hook% "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop")
    (by dsimp [staticDropName]; simp [Rust.isPanicSymbol])
    ⟨zeroizeSecretHook, rfl, zeroize32_hookOk⟩

end BS10

end CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegB
