/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Specs.SpeOwned
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `SpeOwned` and `dropSpeOwnedSpecPlaced` Projections

Re-exports `dropSpeOwnedSpecPlaced`, `DropSpeOwnedOkPlaced`, and `DropSpeOwnedOkAtBlock` under
`[LibsignalPlacement]`, and proves agreement with `withLsCodeRoLoaded lsmpl (DropSpeProof.dropSpeSpecStk A stk)`
on `.proto`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunDrop

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli

theorem dropSpeOwnedSpecPlaced_proto_pre [LibsignalPlacement]
    (A : RustAlloc) (stk : Nat) (a : BitVec 64)
    (fnName : List (BitVec 8)) (e : SignalProtocolError) :
    (dropSpeOwnedSpecPlaced A stk).pre ⟨a, .proto fnName e⟩ =
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (DropSpeProof.dropSpeSpecStk A stk)).pre ⟨a, fnName, e⟩ := rfl

theorem dropSpeOwnedSpecPlaced_proto_post [LibsignalPlacement]
    (A : RustAlloc) (stk : Nat) (a : BitVec 64)
    (fnName : List (BitVec 8)) (e : SignalProtocolError) :
    (dropSpeOwnedSpecPlaced A stk).post ⟨a, .proto fnName e⟩ =
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (DropSpeProof.dropSpeSpecStk A stk)).post ⟨a, fnName, e⟩ := rfl

end CryptoVerification.SignalSession.Cli.RunDrop
