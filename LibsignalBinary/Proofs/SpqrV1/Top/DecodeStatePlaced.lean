/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.InnerReloc
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.OuterLoopPlaced

/-!
# Top-Level Relocatable Verification of `spqr::decode_state` (`Block 325`, 553 insns)

Instantiates `decodeState_placed_ok` from `Top/DecodeState/OuterLoopPlaced.lean` with the
canonical `V1State` inner heap representation `canonicalV1InnerHeap` (`InnerReloc.lean`),
matching `Drop.optProtoInnerStateAt` and `Prost.MessageMerge.v1StateMergePlacedSpec`, and proves
`spqr_decode_state_placed_ok` and `spqr_decode_state_placed_ok_x` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Top.DecodeState

open Arm64
open ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSpqr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Top.DecodeState.Placed

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr Program.fnOff Obj.lookup

/-! ## 1. Canonical Representation Bridges for `Drop` & `MessageMerge` Specifications on `Block 325` -/

/-- Lift `subroutine_ok` for `Drop.dropOptProtoInnerStatePlacedSpec A` to
`DecodeState.dropOptProtoInnerStatePlacedSpec canonicalV1InnerHeap A`. -/
theorem dropOptProtoInnerState_canonical_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hdrop : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 267) (CryptoVerification.SpqrV1.Drop.dropOptProtoInnerStatePlacedSpec A)) :
    subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 267) (dropOptProtoInnerStatePlacedSpec canonicalV1InnerHeap A) := by
  refine subroutine_ok_outcome_intro fun ⟨a, opt⟩ R s0 hpc hrun hpre halign => ?_
  dsimp only [dropOptProtoInnerStatePlacedSpec, v1StateJumpTablesPlacedAt] at hpre
  rw [optProtoInnerStateAt_canonical_eq_drop, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hx0, hm⟩
  let R' := v1StateMergeJumpTablePlacedExpanded ∗ R
  have hpre' : s0.mem ⊨
      (CryptoVerification.SpqrV1.Drop.dropOptProtoInnerStatePlacedSpec A).pre ⟨a, opt⟩ s0 ∗ R' := by
    dsimp only [CryptoVerification.SpqrV1.Drop.dropOptProtoInnerStatePlacedSpec,
      CryptoVerification.SpqrV1.Drop.optProtoInnerStateSize,
      CryptoVerification.SpqrV1.Drop.dropStack96, dropOptProtoInnerStateStack, R']
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hx0, ?_⟩
    refine Satisfies.mono (Entails.of_eq ?_) hm
    ac_rfl
  refine (hdrop.to_outcome ⟨a, opt⟩ R' s0 hpc hrun hpre' halign).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    dsimp only [CryptoVerification.SpqrV1.Drop.dropOptProtoInnerStatePlacedSpec,
      CryptoVerification.SpqrV1.Drop.optProtoInnerStateSize,
      CryptoVerification.SpqrV1.Drop.dropStack96, R'] at hpost
    dsimp only [dropOptProtoInnerStatePlacedSpec, v1StateJumpTablesPlacedAt, dropOptProtoInnerStateStack]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    refine ⟨htr, Satisfies.mono (Entails.of_eq ?_) hpost⟩
    ac_rfl
  · dsimp only [CryptoVerification.SpqrV1.Drop.dropOptProtoInnerStatePlacedSpec] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · dsimp only [CryptoVerification.SpqrV1.Drop.dropOptProtoInnerStatePlacedSpec] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim

/-- Lift `subroutine_ok` for `Drop.dropProtoPqRatchetStatePlacedSpec A` to
`DecodeState.dropProtoPqRatchetStatePlacedSpec canonicalV1InnerHeap A`. -/
theorem dropProtoPqRatchetState_canonical_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hdrop : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 270) (CryptoVerification.SpqrV1.Drop.dropProtoPqRatchetStatePlacedSpec A)) :
    subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 270) (dropProtoPqRatchetStatePlacedSpec canonicalV1InnerHeap A) := by
  refine subroutine_ok_outcome_intro fun ⟨a, st⟩ R s0 hpc hrun hpre halign => ?_
  dsimp only [dropProtoPqRatchetStatePlacedSpec, v1StateJumpTablesPlacedAt] at hpre
  rw [protoPqRatchetStateAt_canonical_eq_drop, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hx0, hm⟩
  let R' := v1StateMergeJumpTablePlacedExpanded ∗ R
  have hpre' : s0.mem ⊨
      (CryptoVerification.SpqrV1.Drop.dropProtoPqRatchetStatePlacedSpec A).pre ⟨a, st⟩ s0 ∗ R' := by
    dsimp only [CryptoVerification.SpqrV1.Drop.dropProtoPqRatchetStatePlacedSpec,
      CryptoVerification.SpqrV1.Drop.protoPqRatchetStateSize,
      CryptoVerification.SpqrV1.Drop.dropStack96, dropOptProtoInnerStateStack, R']
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hx0, ?_⟩
    refine Satisfies.mono (Entails.of_eq ?_) hm
    ac_rfl
  refine (hdrop.to_outcome ⟨a, st⟩ R' s0 hpc hrun hpre' halign).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    dsimp only [CryptoVerification.SpqrV1.Drop.dropProtoPqRatchetStatePlacedSpec,
      CryptoVerification.SpqrV1.Drop.protoPqRatchetStateSize,
      CryptoVerification.SpqrV1.Drop.dropStack96, R'] at hpost
    dsimp only [dropProtoPqRatchetStatePlacedSpec, v1StateJumpTablesPlacedAt, dropOptProtoInnerStateStack]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    refine ⟨htr, Satisfies.mono (Entails.of_eq ?_) hpost⟩
    ac_rfl
  · dsimp only [CryptoVerification.SpqrV1.Drop.dropProtoPqRatchetStatePlacedSpec] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · dsimp only [CryptoVerification.SpqrV1.Drop.dropProtoPqRatchetStatePlacedSpec] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim

/-! ## 2. Canonical `DecodeStateCalleeContractsPlaced` & `DecodeStateCalleeContractsPlacedX` Assembly -/

/-- Assemble `DecodeStateCalleeContractsPlaced canonicalV1InnerHeap A ext` from callee contracts on `Block 325`. -/
theorem mkDecodeStateCalleeContractsPlaced [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hmemcpy : ∀ hookStack : Nat,
      subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
        (lsρ "memcpy") (libcMemcpySpec hookStack))
    (hsession_memcpy : ∀ hookStack : Nat,
      subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
        (lsρ "memcpy") (sessionMemcpySpec hookStack))
    (hfrom : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 261) (decodeErrorFromSpec A))
    (hpush : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 257) (decodeErrorPushSpec A))
    (hvarint : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 291) (Varint.decodeVarint2Spec A))
    (hskip : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 263) (skipField3Spec A))
    (hcp : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 294) (chainParamsMergeSpec A))
    (hgrow : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 356) (growOneStrideFullSpec A 112 8))
    (hdrop_inner : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 267) (CryptoVerification.SpqrV1.Drop.dropOptProtoInnerStatePlacedSpec A))
    (hdrop_pqr : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 270) (CryptoVerification.SpqrV1.Drop.dropProtoPqRatchetStatePlacedSpec A)) :
    DecodeStateCalleeContractsPlaced canonicalV1InnerHeap A ext where
  of_drop_inner := of_drop_inner_canonical A
  of_cap_inner := of_cap_inner_ok A
  dealloc := hdealloc
  memcpy := hmemcpy
  session_memcpy := hsession_memcpy
  decodeErrorFrom := hfrom
  decodeErrorPush := hpush
  decodeVarint2 := hvarint
  skipField3 := hskip
  chainParamsMerge := hcp
  growOneChainEpoch := hgrow
  dropOptProtoInnerState := dropOptProtoInnerState_canonical_placed_ok hdrop_inner
  dropProtoPqRatchetState := dropProtoPqRatchetState_canonical_placed_ok hdrop_pqr

/-- Assemble `DecodeStateCalleeContractsPlacedX canonicalV1InnerHeap A ext` from callee contracts on `Block 325`. -/
theorem mkDecodeStateCalleeContractsPlacedX [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hmemcpy : ∀ hookStack : Nat,
      subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
        (lsρ "memcpy") (libcMemcpySpec hookStack))
    (hsession_memcpy : ∀ hookStack : Nat,
      subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
        (lsρ "memcpy") (sessionMemcpySpec hookStack))
    (hfrom : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 261) (decodeErrorFromSpec A))
    (hpush : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 257) (decodeErrorPushSpec A))
    (hvarint : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 291) (Varint.decodeVarint2Spec A))
    (hskip : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 263) (skipField3Spec A))
    (hcp : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 294) (chainParamsMergeSpec A))
    (hgrow : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 356) (growOneStrideFullSpec A 112 8))
    (hdrop_inner : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 267) (CryptoVerification.SpqrV1.Drop.dropOptProtoInnerStatePlacedSpec A))
    (hdrop_pqr : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 270) (CryptoVerification.SpqrV1.Drop.dropProtoPqRatchetStatePlacedSpec A))
    (hbytes : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)))
    (hed : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 299) (withLsCodeRoLoaded lsmpl (epochDirectionMergeSpec A)))
    (hv1 : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 298) (withLsCodeRoLoaded lsmpl (Prost.MessageMerge.v1StateMergePlacedSpec A))) :
    DecodeStateCalleeContractsPlacedX canonicalV1InnerHeap A ext where
  toDecodeStateCalleeContractsPlaced :=
    mkDecodeStateCalleeContractsPlaced hdealloc hmemcpy hsession_memcpy
      hfrom hpush hvarint hskip hcp hgrow hdrop_inner hdrop_pqr
  bytesMerge3 := hbytes
  epochDirectionMerge := hed
  v1StateMerge := hv1

/-! ## 3. Top-Level Relocatable Theorems (`spqr_decode_state_placed_ok_x` & `spqr_decode_state_placed_ok`) -/

/-- Top-level relocatable `spqr::decode_state` (`Block 325`) theorem with `decodeStateStackX`
for the canonical `V1State` inner heap representation `canonicalV1InnerHeap`. -/
theorem spqr_decode_state_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hmemcpy : ∀ hookStack : Nat,
      subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
        (lsρ "memcpy") (libcMemcpySpec hookStack))
    (hsession_memcpy : ∀ hookStack : Nat,
      subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
        (lsρ "memcpy") (sessionMemcpySpec hookStack))
    (hfrom : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 261) (decodeErrorFromSpec A))
    (hpush : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 257) (decodeErrorPushSpec A))
    (hvarint : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 291) (Varint.decodeVarint2Spec A))
    (hskip : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 263) (skipField3Spec A))
    (hcp : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 294) (chainParamsMergeSpec A))
    (hgrow : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 356) (growOneStrideFullSpec A 112 8))
    (hdrop_inner : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 267) (CryptoVerification.SpqrV1.Drop.dropOptProtoInnerStatePlacedSpec A))
    (hdrop_pqr : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 270) (CryptoVerification.SpqrV1.Drop.dropProtoPqRatchetStatePlacedSpec A))
    (hbytes : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)))
    (hed : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 299) (withLsCodeRoLoaded lsmpl (epochDirectionMergeSpec A)))
    (hv1 : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 298) (withLsCodeRoLoaded lsmpl (Prost.MessageMerge.v1StateMergePlacedSpec A))) :
    DecodeStatePlacedOkX canonicalV1InnerHeap A ext :=
  decodeState_placed_ok
    (mkDecodeStateCalleeContractsPlacedX hdealloc hmemcpy hsession_memcpy
      hfrom hpush hvarint hskip hcp hgrow hdrop_inner hdrop_pqr hbytes hed hv1)

/-- Top-level relocatable `spqr::decode_state` (`Block 325`) theorem with `decodeStateStack`
for the canonical `V1State` inner heap representation `canonicalV1InnerHeap`. -/
theorem spqr_decode_state_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hmemcpy : ∀ hookStack : Nat,
      subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
        (lsρ "memcpy") (libcMemcpySpec hookStack))
    (hsession_memcpy : ∀ hookStack : Nat,
      subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
        (lsρ "memcpy") (sessionMemcpySpec hookStack))
    (hfrom : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 261) (decodeErrorFromSpec A))
    (hpush : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 257) (decodeErrorPushSpec A))
    (hvarint : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 291) (Varint.decodeVarint2Spec A))
    (hskip : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 263) (skipField3Spec A))
    (hcp : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 294) (chainParamsMergeSpec A))
    (hgrow : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 356) (growOneStrideFullSpec A 112 8))
    (hdrop_inner : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 267) (CryptoVerification.SpqrV1.Drop.dropOptProtoInnerStatePlacedSpec A))
    (hdrop_pqr : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 270) (CryptoVerification.SpqrV1.Drop.dropProtoPqRatchetStatePlacedSpec A))
    (hbytes : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)))
    (hed : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 299) (withLsCodeRoLoaded lsmpl (epochDirectionMergeSpec A)))
    (hv1 : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 298) (withLsCodeRoLoaded lsmpl (Prost.MessageMerge.v1StateMergePlacedSpec A))) :
    DecodeStatePlacedOk canonicalV1InnerHeap A ext :=
  spqr_decode_state_placed_ok_x hdealloc hmemcpy hsession_memcpy
    hfrom hpush hvarint hskip hcp hgrow hdrop_inner hdrop_pqr hbytes hed hv1

/-- `libsignalSessionLib.blockProgram lsmpl 325 (Rust.withPanics ext)` form of
`spqr_decode_state_placed_ok_x`. -/
theorem spqr_decode_state_placed_ok_blockProgram [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX canonicalV1InnerHeap A ext) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 325 (Rust.withPanics ext))
      (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl (decodeStatePlacedSpecX canonicalV1InnerHeap A)) := by
  have hok := decodeState_placed_ok hc
  dsimp only [DecodeStatePlacedOkX, DecodeStatePlacedOk, decodeStatePlacedProg, decodeStatePlacedEntry] at hok
  rw [IsLsBlockProg.eq_blockProgram (prog := (blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))] at hok
  exact hok

end CryptoVerification.SpqrV1.Top.DecodeState
