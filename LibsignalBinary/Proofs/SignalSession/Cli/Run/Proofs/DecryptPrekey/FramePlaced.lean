/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Frame
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.CliHandshakeCodeSymC
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.RespClosureCodeSym
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Placed Stack-Frame Layout and Epilogue Helpers for `decrypt_prekey`

Relocatable (`[LibsignalPlacement]`) program/entry abbreviations and stack-frame layout helpers for
Block `520` (`signal_session_handshake::decrypt_prekey`, `lsProg_520`) and Block `518`
(`message_decrypt_prekey::{closure#0}`, `lsProg_518`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession.Cli CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.CliHandshake.Placed
open CryptoVerification.CliHandshake.RespClosurePlaced

/-- Block `520` (`signal_session_handshake::decrypt_prekey`) program with `Rust.withPanics ext`. -/
abbrev dpWrapProgPlaced [LibsignalPlacement] (ext : String → Option (State → State)) : Program :=
  lsProg_520 (Rust.withPanics ext)

/-- Entry address of Block `520` (`signal_session_handshake::decrypt_prekey`). -/
abbrev dpWrapEntryPlaced [LibsignalPlacement] : BitVec 64 :=
  (blkPl_520).base

/-- Block `518` (`message_decrypt_prekey::<signal_session_handshake::Coins>::{closure#0}`) program
with `Rust.withPanics ext`. -/
abbrev dpPollProgPlaced [LibsignalPlacement] (ext : String → Option (State → State)) : Program :=
  lsProg_518 (Rust.withPanics ext)

/-- Entry address of Block `518` (`message_decrypt_prekey::<signal_session_handshake::Coins>::{closure#0}`). -/
abbrev dpPollEntryPlaced [LibsignalPlacement] : BitVec 64 :=
  (blkPl_518).base

theorem dpWrapEntryPlaced_eq_lsmpl_base [LibsignalPlacement] :
    dpWrapEntryPlaced = lsmpl.base 520 := rfl

theorem dpPollEntryPlaced_eq_lsmpl_base [LibsignalPlacement] :
    dpPollEntryPlaced = lsmpl.base 518 := rfl

end CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers
end
