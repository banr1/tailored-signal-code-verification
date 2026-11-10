/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize.Defs
public import LibsignalBinary.Proofs.SpqrV1.Top.TopLeafCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternal

/-!
# Relocatable Contract Definition for `<Message>::deserialize`

Defines `MessageDeserializePlacedOkX` for `<spqr::v1::chunked::states::Message>::deserialize`
(Block `351`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Top.MessageDeserialize

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Top.Placed

def spqrFormatInnerSym : String := "_RNvNvNtCs69KKACWg7bl_5alloc3fmt6format12format_inner"
def spqrDeallocSym : String := "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"

/-- Relocatable `subroutine_ok` contract for `<spqr::v1::chunked::states::Message>::deserialize`
    (`Block 351`). -/
def MessageDeserializePlacedOkX [LibsignalPlacement] (P_poly : PolyApi) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_351).rebase (blkPl_351).base (Rust.withPanics ext))
    (blkPl_351).base
    (withLsCallInv lsmpl (messageDeserializeSpecX P_poly A))

end CryptoVerification.SpqrV1.Top.MessageDeserialize
