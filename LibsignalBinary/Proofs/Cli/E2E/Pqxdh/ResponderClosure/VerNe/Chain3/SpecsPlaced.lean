/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Specs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.CliHandshakeCodeSymA
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.CliHandshakeCodeSymB
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.CliHandshakeCodeSymC
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Callee Specifications for `message::merge<Chain>`

Relocatable (`[LibsignalPlacement]`) subroutine contracts and `Chain3CalleePlacedKit` bundle for
`prost::encoding::message::merge<Chain> [local#4]` on `lsProg_516`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3

open Arm64 ProofLib SepProp ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.E2E.Record (A0)
open Proofs.libsignal.Hooks2
open Proofs.libsignal.Stage1X
open CryptoVerification.CliHandshake.Placed

/-- Relocatable contract for `prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#5]`
(Block `514`). -/
abbrev bytesMerge3PlacedSpec [LibsignalPlacement] (A : RustAlloc) : Spec BytesMergeGhost :=
  withLsCl lsmpl (bytesMerge3RawSpec A)

/-- Callee contract bundle for `message::merge<Chain>` on `lsProg_516`, grouping
`decode_varint [local#4]` (Block `515`), `bytes::merge [local#5]` (Block `514`), and
`RawVec<Chain>::grow_one` (Block `43`). -/
structure Chain3CalleePlacedKit [LibsignalPlacement] : Prop where
  dv : ∀ (ext : String → Option (State → State)),
    subroutine_ok (lsProg_516 ext) (lsmpl.base 515)
      (withLsCl lsmpl (decodeVarint2SpecX A0))
  bm : ∀ (ext : String → Option (State → State)),
    subroutine_ok (lsProg_516 ext) (lsmpl.base 514)
      (bytesMerge3PlacedSpec A0)
  grow : ∀ (ext : String → Option (State → State)),
    subroutine_ok (lsProg_516 ext) (lsmpl.base 43)
      (withLsCl lsmpl (growOneChainSpecX A0))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3
