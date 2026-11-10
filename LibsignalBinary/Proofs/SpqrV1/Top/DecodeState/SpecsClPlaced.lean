/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlaced
public import LibsignalBinary.Proofs.Placed.GenLsBlock

/-!
# Code-Loaded `[LibsignalPlacement]` Callee Contracts for `spqr::decode_state` (Block `325`)

Bundles code-loaded callee contracts (`DecodeStateCalleeContractsClPlaced` and
`DecodeStateCalleeContractsClPlacedX`) for Block `325`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SpqrV1.Top.DecodeState

open Arm64 Arm64.Obj ProofLib
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Top.DecodeState.Placed

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr Obj.lookup

/-- Code-loaded bundle of relocatable callee contracts used by `spqr::decode_state` (Block `325`).
Every cross-block callee carries `withLsCodeLoaded lsmpl` or `withLsCl lsmpl`. -/
structure DecodeStateCalleeContractsClPlaced [LibsignalPlacement] (H_inner : V1InnerHeapPred)
    (A : RustAlloc) (ext : String → Option (State → State)) : Prop where
  of_drop_inner : ∀ a opt,
    CryptoVerification.SpqrV1.Drop.optProtoInnerStateAt A a opt ⊢
      optProtoInnerStateAt H_inner A a opt
  of_cap_inner : ∀ a remLen opt,
    OptInnerStatePolyBound remLen opt →
    Prost.MessageMerge.optProtoInnerStateCapAt A a remLen opt ⊢
      optProtoInnerStateCapOkAt H_inner A a remLen opt
  dealloc : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A)
  memcpy : ∀ hookStack : Nat,
    subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsρ "memcpy") (libcMemcpySpec hookStack)
  session_memcpy : ∀ hookStack : Nat,
    subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsρ "memcpy") (sessionMemcpySpec hookStack)
  decodeErrorFrom : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromSpec A))
  decodeErrorPush : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushSpec A))
  decodeVarint2 : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (lsmpl.base 291) (withLsCodeLoaded lsmpl (Varint.decodeVarint2Spec A))
  skipField3 : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A))
  chainParamsMerge : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (lsmpl.base 294) (withLsCodeLoaded lsmpl (chainParamsMergeSpec A))
  growOneChainEpoch : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (lsmpl.base 356) (withLsCodeLoaded lsmpl (growOneStrideFullSpec A 112 8))
  dropOptProtoInnerState : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (lsmpl.base 267) (withLsCl lsmpl (dropOptProtoInnerStatePlacedSpec H_inner A))
  dropProtoPqRatchetState : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (lsmpl.base 270) (withLsCl lsmpl (dropProtoPqRatchetStatePlacedSpec H_inner A))

/-- Full code-loaded relocatable callee contracts for `spqr::decode_state` (Block `325`), extending
`DecodeStateCalleeContractsClPlaced` with `withLsCodeRoLoaded lsmpl` contracts for callees that
invoke `bytes::merge [local#3]` (`bytesMerge3`, `epochDirectionMerge`, `v1StateMerge`). -/
structure DecodeStateCalleeContractsClPlacedX [LibsignalPlacement] (H_inner : V1InnerHeapPred)
    (A : RustAlloc) (ext : String → Option (State → State)) : Prop extends
    DecodeStateCalleeContractsClPlaced H_inner A ext where
  bytesMerge3 : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A))
  epochDirectionMerge : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (lsmpl.base 299) (withLsCodeRoLoaded lsmpl (epochDirectionMergeSpec A))
  v1StateMerge : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (lsmpl.base 298) (withLsCodeRoLoaded lsmpl (Prost.MessageMerge.v1StateMergePlacedSpec A))

end CryptoVerification.SpqrV1.Top.DecodeState
