/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.ChainEncodedLenBase

/-!
# `VmPreserved` Placed Propositions for `Chain::encoded_len`

Defines `[LibsignalPlacement]` `subroutine_ok` propositions for `Chain::encoded_len [local#1, #2]`
(Blocks `178` and `406`) against `DefsBudget.chainEncodedLen{Pinned,}Spec`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.ProtoRepr.ChainEncodedLenBaseBudget

open _root_.Arm64 ProofLib
open CryptoVerification
  (LibsignalPlacement lsmpl withLsCodeLoaded blkPC_178 blkPl_178 blkPC_406 blkPl_406)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetExterns)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget
  (chainEncodedLenPinnedSpec chainEncodedLenSpec)

def ChainEncodedLenLocal1PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_178).rebase (blkPl_178).base (Rust.withPanics ext))
    (blkPl_178).base (withLsCodeLoaded lsmpl (chainEncodedLenPinnedSpec A))

def ChainEncodedLenLocal1PlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_178).rebase (blkPl_178).base (Rust.withPanics ext))
    (blkPl_178).base (withLsCodeLoaded lsmpl (chainEncodedLenSpec A))

def ChainEncodedLenLocal1PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  ChainEncodedLenLocal1PinnedPlacedOkExt A (tripleRatchetExterns C ctl abs)

def ChainEncodedLenLocal1PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  ChainEncodedLenLocal1PlacedOkExt A (tripleRatchetExterns C ctl abs)

def ChainEncodedLenLocal2PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_406).rebase (blkPl_406).base (Rust.withPanics ext))
    (blkPl_406).base (withLsCodeLoaded lsmpl (chainEncodedLenPinnedSpec A))

def ChainEncodedLenLocal2PlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_406).rebase (blkPl_406).base (Rust.withPanics ext))
    (blkPl_406).base (withLsCodeLoaded lsmpl (chainEncodedLenSpec A))

def ChainEncodedLenLocal2PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  ChainEncodedLenLocal2PinnedPlacedOkExt A (tripleRatchetExterns C ctl abs)

def ChainEncodedLenLocal2PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  ChainEncodedLenLocal2PlacedOkExt A (tripleRatchetExterns C ctl abs)

end LibsignalBinary.Proofs.SpqrV1.ProtoRepr.ChainEncodedLenBaseBudget
