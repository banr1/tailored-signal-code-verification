/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeDefs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ConstsMergePlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafVarintPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafReservePlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.CliHandshakeCodeSymA
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.VarintBridge

/-!
# Relocatable Handshake `bytes::merge [local#5]` Definitions

Relocatable (`[LibsignalPlacement]`) specifications (`bytesMerge3PlacedSpec`,
`bytesMerge3ProtoPlacedSpec`) and contract propositions (`BytesMerge6PlacedOkExt`,
`BytesMerge6ProtoPlacedOkExt`) for `prost::encoding::bytes::merge [local#5]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.VarintBridge
open CryptoVerification.CodeLayout
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.CliHandshake.Placed

/-- Relocatable `[LibsignalPlacement]` spec of `prost::encoding::bytes::merge [local#5]`
using `mergeBytes` on `lsProg_518 ext`. -/
abbrev bytesMerge3PlacedSpec [LibsignalPlacement] (A : RustAlloc) : Spec BytesMergeGhost :=
  withLsCl lsmpl (bytesMerge3RawSpec A)

/-- Relocatable `[LibsignalPlacement]` spec of `prost::encoding::bytes::merge [local#5]`
using `LibsignalSpqrV1.Proto.mergeBytes` on `lsProg_518 ext`. -/
abbrev bytesMerge3ProtoPlacedSpec [LibsignalPlacement] (A : RustAlloc) : Spec BytesMergeProtoGhost :=
  withLsCl lsmpl (bytesMerge3ProtoRawSpec A)

/-- Relocatable `[LibsignalPlacement]` contract for
`prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#5]`
(Block `508`, `(blkPl_507).base = lsmpl.base 507`) against `bytesMerge3PlacedSpec A`. -/
def BytesMerge6PlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_518 ext) (lsmpl.base 507)
    (bytesMerge3PlacedSpec A)

/-- Relocatable `[LibsignalPlacement]` contract for
`prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#5]`
(Block `508`, `(blkPl_507).base = lsmpl.base 507`) against `bytesMerge3ProtoPlacedSpec A`. -/
def BytesMerge6ProtoPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_518 ext) (lsmpl.base 507)
    (bytesMerge3ProtoPlacedSpec A)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
