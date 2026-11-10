/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsV1StateBudget
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1State

/-!
# `VmPreserved` Placed Propositions for `V1State::encoded_len`

Defines `[LibsignalPlacement]` `subroutine_ok` propositions for `V1State::encoded_len [local#1, #2]`
(Blocks `177` and `405`) against `DefsV1StateBudget.v1StateEncodedLenRo{Pinned,}Spec`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1StateBudget

open Arm64 ProofLib
open CryptoVerification
  (LibsignalPlacement lsmpl withLsCodeLoaded lsρ blkPC_177 blkPl_177 blkPC_405 blkPl_405)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetExterns)
open CryptoVerification.SpqrV1.ProtoRepr (v1StateJtSymLocal1 v1StateJtSymLocal2)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsV1StateBudget
  (v1StateEncodedLenRoPinnedSpec v1StateEncodedLenRoSpec)

def V1StateEncodedLenLocal1PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_177).rebase (blkPl_177).base (Rust.withPanics ext)) (blkPl_177).base
    (withLsCodeLoaded lsmpl (v1StateEncodedLenRoPinnedSpec A (lsρ v1StateJtSymLocal1)))

def V1StateEncodedLenLocal1PlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_177).rebase (blkPl_177).base (Rust.withPanics ext)) (blkPl_177).base
    (withLsCodeLoaded lsmpl (v1StateEncodedLenRoSpec A (lsρ v1StateJtSymLocal1)))

def V1StateEncodedLenLocal1PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  V1StateEncodedLenLocal1PinnedPlacedOkExt A (tripleRatchetExterns C ctl abs)

def V1StateEncodedLenLocal1PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  V1StateEncodedLenLocal1PlacedOkExt A (tripleRatchetExterns C ctl abs)

def V1StateEncodedLenLocal2PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_405).rebase (blkPl_405).base (Rust.withPanics ext)) (blkPl_405).base
    (withLsCodeLoaded lsmpl (v1StateEncodedLenRoPinnedSpec A (lsρ v1StateJtSymLocal2)))

def V1StateEncodedLenLocal2PlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_405).rebase (blkPl_405).base (Rust.withPanics ext)) (blkPl_405).base
    (withLsCodeLoaded lsmpl (v1StateEncodedLenRoSpec A (lsρ v1StateJtSymLocal2)))

def V1StateEncodedLenLocal2PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  V1StateEncodedLenLocal2PinnedPlacedOkExt A (tripleRatchetExterns C ctl abs)

def V1StateEncodedLenLocal2PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  V1StateEncodedLenLocal2PlacedOkExt A (tripleRatchetExterns C ctl abs)

end LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1StateBudget
