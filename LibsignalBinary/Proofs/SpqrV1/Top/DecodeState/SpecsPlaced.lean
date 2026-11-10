/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.Specs
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DecodeStateCodeSym

/-!
# Relocatable `[LibsignalPlacement]` Specifications for `spqr::decode_state` (Block `325`)
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Top.DecodeState

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Top.DecodeState.Placed

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr Obj.lookup

/-- Relocatable contract for `core::ptr::drop_glue::<Option<spqr::proto::pq_ratchet::v1_state::InnerState>>` (Block `267`). -/
def dropOptProtoInnerStatePlacedSpec [LibsignalPlacement] (H_inner : V1InnerHeapPred) (A : RustAlloc) :
    Spec DropOptProtoInnerStateGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗
      optProtoInnerStateAt H_inner A x.a x.st ∗
      v1StateJumpTablesPlacedAt ∗
      A.pool ∗ stackAt s.sp dropOptProtoInnerStateStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.a 224 ∗
      v1StateJumpTablesPlacedAt ∗
      A.pool ∗ stackAt s0.sp dropOptProtoInnerStateStack
  onPanic := fun _ _ _ => ⌜False⌝

/-- Relocatable contract for `core::ptr::drop_glue::<spqr::proto::pq_ratchet::PqRatchetState>` (Block `270`). -/
def dropProtoPqRatchetStatePlacedSpec [LibsignalPlacement] (H_inner : V1InnerHeapPred) (A : RustAlloc) :
    Spec DropProtoPqRatchetStateGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗
      protoPqRatchetStateAt H_inner A x.a x.st ∗
      v1StateJumpTablesPlacedAt ∗
      A.pool ∗ stackAt s.sp dropOptProtoInnerStateStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.a 352 ∗
      v1StateJumpTablesPlacedAt ∗
      A.pool ∗ stackAt s0.sp dropOptProtoInnerStateStack
  onPanic := fun _ _ _ => ⌜False⌝

/-- Relocatable specification of `spqr::decode_state` (Block `325`, 745 instructions) against
    trusted `spqrDecodeState`. -/
def spqrDecodeStatePlacedSpec [LibsignalPlacement] (H_inner : V1InnerHeapPred) (A : RustAlloc) :
    Spec DecodeStateGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.outPtr ∧
      s.readReg64 .x0 = x.st.v ∧
      x.st.bytes.length < 2 ^ 32⌝ ∗
      v1StateJumpTablesPlacedAt ∗
      x.st.at A ∗
      memRegion x.outPtr 352 ∗
      A.pool ∗ stackAt s.sp decodeStateStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      v1StateJumpTablesPlacedAt ∗
      x.st.at A ∗
      decodeStateResultAt H_inner A x.outPtr (spqrDecodeState x.st.bytes) ∗
      A.pool ∗ stackAt s0.sp decodeStateStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

abbrev decodeStatePlacedSpecX [LibsignalPlacement] (H_inner : V1InnerHeapPred) (A : RustAlloc) :
    Spec DecodeStateGhost :=
  spqrDecodeStatePlacedSpec H_inner A

/-- Bundle of relocatable callee contracts used by `spqr::decode_state` (Block `325`). -/
structure DecodeStateCalleeContractsPlaced [LibsignalPlacement] (H_inner : V1InnerHeapPred)
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
    (lsmpl.base 261) (decodeErrorFromSpec A)
  decodeErrorPush : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (lsmpl.base 257) (decodeErrorPushSpec A)
  decodeVarint2 : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (lsmpl.base 291) (Varint.decodeVarint2Spec A)
  skipField3 : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (lsmpl.base 263) (skipField3Spec A)
  chainParamsMerge : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (lsmpl.base 294) (chainParamsMergeSpec A)
  growOneChainEpoch : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (lsmpl.base 356) (growOneStrideFullSpec A 112 8)
  dropOptProtoInnerState : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (lsmpl.base 267) (dropOptProtoInnerStatePlacedSpec H_inner A)
  dropProtoPqRatchetState : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (lsmpl.base 270) (dropProtoPqRatchetStatePlacedSpec H_inner A)

/-- Full relocatable callee contracts for `spqr::decode_state` (Block `325`), extending
    `DecodeStateCalleeContractsPlaced` with `withLsCodeRoLoaded lsmpl` contracts for callees that
    invoke `bytes::merge [local#3]` (`bytesMerge3`, `epochDirectionMerge`, `v1StateMerge`). -/
structure DecodeStateCalleeContractsPlacedX [LibsignalPlacement] (H_inner : V1InnerHeapPred)
    (A : RustAlloc) (ext : String → Option (State → State)) : Prop extends
    DecodeStateCalleeContractsPlaced H_inner A ext where
  bytesMerge3 : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A))
  epochDirectionMerge : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (lsmpl.base 299) (withLsCodeRoLoaded lsmpl (epochDirectionMergeSpec A))
  v1StateMerge : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (lsmpl.base 298) (withLsCodeRoLoaded lsmpl (Prost.MessageMerge.v1StateMergePlacedSpec A))

/-- `spqr::decode_state` (Block `325`) meets `withLsCodeRoLoaded lsmpl (spqrDecodeStatePlacedSpec H_inner A)`
    on `(blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext)`. -/
def DecodeStatePlacedOk [LibsignalPlacement] (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (blkPl_325).base
    (withLsCodeRoLoaded lsmpl (spqrDecodeStatePlacedSpec H_inner A))

abbrev DecodeStatePlacedOkX [LibsignalPlacement] (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  DecodeStatePlacedOk H_inner A ext

end CryptoVerification.SpqrV1.Top.DecodeState
