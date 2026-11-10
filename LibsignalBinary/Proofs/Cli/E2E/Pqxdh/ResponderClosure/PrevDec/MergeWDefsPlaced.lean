/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeWDefs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeDefsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.VarintBridge

/-!
# Relocatable Handshake `bytes::merge [local#5]` W-Mode Definitions

Relocatable (`[LibsignalPlacement]`) W-mode specification (`bytesMerge3PlacedSpecW`) and contract
proposition (`BytesMerge6PlacedOkExtW`, `x.bs.length < 2 ^ 62`) on `lsProg_518 ext`.
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

/-- Relocatable `[LibsignalPlacement]` W-spec (`x.bs.length < 2 ^ 62`) of
`prost::encoding::bytes::merge [local#5]` on `lsProg_518 ext`. -/
abbrev bytesMerge3PlacedSpecW [LibsignalPlacement] (A : RustAlloc) : Spec BytesMergeGhost :=
  withLsCl lsmpl (bytesMerge3RawSpecW A)

/-- Relocatable `[LibsignalPlacement]` contract for
`prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#5]`
(Block `508`, `(blkPl_507).base = lsmpl.base 507`) against `bytesMerge3PlacedSpecW A`. -/
def BytesMerge6PlacedOkExtW [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_518 ext) (lsmpl.base 507)
    (bytesMerge3PlacedSpecW A)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
