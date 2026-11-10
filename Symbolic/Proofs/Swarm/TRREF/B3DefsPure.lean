/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.SpecLemmas.CliPureBytes

/-!
# Receive-Wire Ghost Bundle

Defines `RecvWireGhost` for tracking the in-memory and wire-serialized session record state across
the binary's receive path, and re-exports `encodeRecord`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E.Pqxdh.WireEntries.SymP3

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Bin

abbrev encodeRecord := CryptoVerification.E2E.Record.encodeRecord

structure RecvWireGhost where
  who        : BitVec 32
  aPtr       : BitVec 64
  meBytes    : List (BitVec 8)
  stateBytes : List (BitVec 8)
  sess       : Session (List (BitVec 8))
  wirePtr    : BitVec 64
  wireBytes  : List (BitVec 8)
  cur        : BitVec 64
  rest       : List (BitVec 8)
  tlsInit    : Option (BitVec 64 × BitVec 64)

end CryptoVerification.E2E.Pqxdh.WireEntries.SymP3

namespace Symbolic.Swarm.TRREF.B3Defs.SymP3

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.RecordX
open CryptoVerification.E2E.Pqxdh.WireEntries CryptoVerification.E2E.Pqxdh.WireEntries.SymP3

end Symbolic.Swarm.TRREF.B3Defs.SymP3
