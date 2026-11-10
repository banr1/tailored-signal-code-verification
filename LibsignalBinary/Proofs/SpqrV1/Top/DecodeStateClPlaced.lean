/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.InnerReloc
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsClPlaced
import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSymB
import LibsignalBinary.Proofs.SpqrV1.Drop.DropCodeSym
import LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.BytesMergeCodeSym
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.MessageMergeCodeSym
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.MessageMergePart2CodeSym
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.OuterLoopClPlaced
import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs

/-!
# Code-Loaded `[LibsignalPlacement]` Verification of `spqr::decode_state` (`Block 325`, 553 insns)

Instantiates `decodeState_cl_placed_ok` with `canonicalV1InnerHeap`, wiring code-loaded own-block
callee contracts into `spqr_decode_state_cl` on
`libsignalSessionLib.blockProgram lsmpl 325 (Rust.withPanics ext)`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Top.DecodeState

open Arm64
open ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification
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

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr Program.fnOff Obj.lookup

/-! ## 1. Canonical Representation Bridges for `Drop` Specifications under `withLsCl` -/

/-- Lift `subroutine_ok` for `withLsCl lsmpl (Drop.dropOptProtoInnerStatePlacedSpec A)` to
`withLsCl lsmpl (DecodeState.dropOptProtoInnerStatePlacedSpec canonicalV1InnerHeap A)`. -/
theorem dropOptProtoInnerState_canonical_cl_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hdrop : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 267) (withLsCl lsmpl (CryptoVerification.SpqrV1.Drop.dropOptProtoInnerStatePlacedSpec A))) :
    subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 267) (withLsCl lsmpl (dropOptProtoInnerStatePlacedSpec canonicalV1InnerHeap A)) := by
  refine subroutine_ok_outcome_intro fun ⟨a, opt⟩ R s0 hpc hrun hpre halign => ?_
  dsimp only [withLsCl, dropOptProtoInnerStatePlacedSpec, v1StateJumpTablesPlacedAt] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl0, hpre⟩
  rw [optProtoInnerStateAt_canonical_eq_drop, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hx0, hm⟩
  let R' := v1StateMergeJumpTablePlacedExpanded ∗ R
  have hpre' : s0.mem ⊨
      (withLsCl lsmpl (CryptoVerification.SpqrV1.Drop.dropOptProtoInnerStatePlacedSpec A)).pre ⟨a, opt⟩ s0 ∗ R' := by
    dsimp only [withLsCl, CryptoVerification.SpqrV1.Drop.dropOptProtoInnerStatePlacedSpec,
      CryptoVerification.SpqrV1.Drop.optProtoInnerStateSize,
      CryptoVerification.SpqrV1.Drop.dropStack96, dropOptProtoInnerStateStack, R']
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hx0, ?_⟩
    refine Satisfies.mono (Entails.of_eq ?_) hm
    ac_rfl
  refine (hdrop.to_outcome ⟨a, opt⟩ R' s0 hpc hrun hpre' halign).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    dsimp only [withLsCl, CryptoVerification.SpqrV1.Drop.dropOptProtoInnerStatePlacedSpec,
      CryptoVerification.SpqrV1.Drop.optProtoInnerStateSize,
      CryptoVerification.SpqrV1.Drop.dropStack96, R'] at hpost
    dsimp only [withLsCl, dropOptProtoInnerStatePlacedSpec, v1StateJumpTablesPlacedAt, dropOptProtoInnerStateStack]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hclf, hpost⟩
    refine ⟨hclf, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    refine ⟨htr, Satisfies.mono (Entails.of_eq ?_) hpost⟩
    ac_rfl
  · dsimp only [withLsCl, CryptoVerification.SpqrV1.Drop.dropOptProtoInnerStatePlacedSpec] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · dsimp only [withLsCl, CryptoVerification.SpqrV1.Drop.dropOptProtoInnerStatePlacedSpec] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim

/-- Lift `subroutine_ok` for `withLsCl lsmpl (Drop.dropProtoPqRatchetStatePlacedSpec A)` to
`withLsCl lsmpl (DecodeState.dropProtoPqRatchetStatePlacedSpec canonicalV1InnerHeap A)`. -/
theorem dropProtoPqRatchetState_canonical_cl_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hdrop : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 270) (withLsCl lsmpl (CryptoVerification.SpqrV1.Drop.dropProtoPqRatchetStatePlacedSpec A))) :
    subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 270) (withLsCl lsmpl (dropProtoPqRatchetStatePlacedSpec canonicalV1InnerHeap A)) := by
  refine subroutine_ok_outcome_intro fun ⟨a, st⟩ R s0 hpc hrun hpre halign => ?_
  dsimp only [withLsCl, dropProtoPqRatchetStatePlacedSpec, v1StateJumpTablesPlacedAt] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl0, hpre⟩
  rw [protoPqRatchetStateAt_canonical_eq_drop, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hx0, hm⟩
  let R' := v1StateMergeJumpTablePlacedExpanded ∗ R
  have hpre' : s0.mem ⊨
      (withLsCl lsmpl (CryptoVerification.SpqrV1.Drop.dropProtoPqRatchetStatePlacedSpec A)).pre ⟨a, st⟩ s0 ∗ R' := by
    dsimp only [withLsCl, CryptoVerification.SpqrV1.Drop.dropProtoPqRatchetStatePlacedSpec,
      CryptoVerification.SpqrV1.Drop.protoPqRatchetStateSize,
      CryptoVerification.SpqrV1.Drop.dropStack96, dropOptProtoInnerStateStack, R']
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hx0, ?_⟩
    refine Satisfies.mono (Entails.of_eq ?_) hm
    ac_rfl
  refine (hdrop.to_outcome ⟨a, st⟩ R' s0 hpc hrun hpre' halign).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    dsimp only [withLsCl, CryptoVerification.SpqrV1.Drop.dropProtoPqRatchetStatePlacedSpec,
      CryptoVerification.SpqrV1.Drop.protoPqRatchetStateSize,
      CryptoVerification.SpqrV1.Drop.dropStack96, R'] at hpost
    dsimp only [withLsCl, dropProtoPqRatchetStatePlacedSpec, v1StateJumpTablesPlacedAt, dropOptProtoInnerStateStack]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hclf, hpost⟩
    refine ⟨hclf, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    refine ⟨htr, Satisfies.mono (Entails.of_eq ?_) hpost⟩
    ac_rfl
  · dsimp only [withLsCl, CryptoVerification.SpqrV1.Drop.dropProtoPqRatchetStatePlacedSpec] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · dsimp only [withLsCl, CryptoVerification.SpqrV1.Drop.dropProtoPqRatchetStatePlacedSpec] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim

/-! ## 2. Canonical `DecodeStateCalleeContractsClPlaced` & `DecodeStateCalleeContractsClPlacedX` Assembly -/

/-- Assemble `DecodeStateCalleeContractsClPlaced canonicalV1InnerHeap A ext` from callee contracts on `Block 325`. -/
theorem mkDecodeStateCalleeContractsClPlaced [LibsignalPlacement]
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
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromSpec A)))
    (hpush : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushSpec A)))
    (hvarint : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (Varint.decodeVarint2Spec A)))
    (hskip : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A)))
    (hcp : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 294) (withLsCodeLoaded lsmpl (chainParamsMergeSpec A)))
    (hgrow : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 356) (withLsCodeLoaded lsmpl (growOneStrideFullSpec A 112 8)))
    (hdrop_inner : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 267) (withLsCl lsmpl (CryptoVerification.SpqrV1.Drop.dropOptProtoInnerStatePlacedSpec A)))
    (hdrop_pqr : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 270) (withLsCl lsmpl (CryptoVerification.SpqrV1.Drop.dropProtoPqRatchetStatePlacedSpec A))) :
    DecodeStateCalleeContractsClPlaced canonicalV1InnerHeap A ext where
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
  dropOptProtoInnerState := dropOptProtoInnerState_canonical_cl_placed_ok hdrop_inner
  dropProtoPqRatchetState := dropProtoPqRatchetState_canonical_cl_placed_ok hdrop_pqr

private theorem ls_subroutine_ok_of_blockProgram_ext [LibsignalPlacement] {α : Type}
    {callerProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    {entry : BitVec 64} {spec : Spec α}
    (hext_j : (libsignalSessionLib.blockLib j).text.externs = libsignalSessionExterns)
    (hcallee : subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) entry
      (withLsCodeLoaded lsmpl spec))
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsCodeLoaded lsmpl spec) :=
  @ls_subroutine_ok_of_block _ _ callerProg
    (libsignalSessionLib.blockProgram lsmpl j H) i j H hcaller ⟨rfl, hext_j⟩ entry spec
    hcallee _ _ _ _ hi hj hj_unmut

private theorem ls_subroutine_ok_cl_of_blockProgram_ext [LibsignalPlacement] {α : Type}
    {callerProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    {entry : BitVec 64} {spec : Spec α}
    (hext_j : (libsignalSessionLib.blockLib j).text.externs = libsignalSessionExterns)
    (hcallee : subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) entry
      (withLsCodeLoaded lsmpl spec))
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsCl lsmpl spec) :=
  @ls_subroutine_ok_cl_of_block _ _ callerProg
    (libsignalSessionLib.blockProgram lsmpl j H) i j H hcaller ⟨rfl, hext_j⟩ entry spec
    hcallee _ _ _ _ hi hj hj_unmut

private theorem ls_subroutine_ok_cro_of_blockProgram_ext [LibsignalPlacement] {α : Type}
    {callerProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    {entry : BitVec 64} {spec : Spec α}
    (hext_j : (libsignalSessionLib.blockLib j).text.externs = libsignalSessionExterns)
    (hcallee : subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) entry
      (withLsCodeRoLoaded lsmpl spec))
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsCodeRoLoaded lsmpl spec) :=
  @keys_ls_subroutine_ok_of_block_cro _ _ callerProg
    (libsignalSessionLib.blockProgram lsmpl j H) i j H hcaller ⟨rfl, hext_j⟩ entry spec
    hcallee _ _ _ _ hi hj hj_unmut

/-- Assemble `DecodeStateCalleeContractsClPlacedX canonicalV1InnerHeap A ext` from own-block
code-loaded contracts on `libsignalSessionLib.blockProgram lsmpl <j> (Rust.withPanics ext)`. -/
theorem mkDecodeStateCalleeContractsClPlacedX_of_blocks [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hmemcpy : ∀ hookStack : Nat,
      subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
        (lsρ "memcpy") (libcMemcpySpec hookStack))
    (hsession_memcpy : ∀ hookStack : Nat,
      subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
        (lsρ "memcpy") (sessionMemcpySpec hookStack))
    (hfrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromSpec A)))
    (hpush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushSpec A)))
    (hvarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (Varint.decodeVarint2Spec A)))
    (hskip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A)))
    (hcp : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 294 (Rust.withPanics ext))
      (lsmpl.base 294) (withLsCodeLoaded lsmpl (chainParamsMergeSpec A)))
    (hgrow : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 356 (Rust.withPanics ext))
      (lsmpl.base 356) (withLsCodeLoaded lsmpl (growOneStrideFullSpec A 112 8)))
    (hdrop_inner : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 267 (Rust.withPanics ext))
      (lsmpl.base 267) (withLsCodeLoaded lsmpl (CryptoVerification.SpqrV1.Drop.dropOptProtoInnerStatePlacedSpec A)))
    (hdrop_pqr : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 270 (Rust.withPanics ext))
      (lsmpl.base 270) (withLsCodeLoaded lsmpl (CryptoVerification.SpqrV1.Drop.dropProtoPqRatchetStatePlacedSpec A)))
    (hbytes : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)))
    (hed : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 299 (Rust.withPanics ext))
      (lsmpl.base 299) (withLsCodeRoLoaded lsmpl (epochDirectionMergeSpec A)))
    (hv1 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 298 (Rust.withPanics ext))
      (lsmpl.base 298) (withLsCodeRoLoaded lsmpl (Prost.MessageMerge.v1StateMergePlacedSpec A))) :
    DecodeStateCalleeContractsClPlacedX canonicalV1InnerHeap A ext where
  toDecodeStateCalleeContractsClPlaced :=
    mkDecodeStateCalleeContractsClPlaced hdealloc hmemcpy hsession_memcpy
      (ls_subroutine_ok_of_blockProgram_ext
        (IsLsBlockProg.externs_eq (prog := (blkPC_261).rebase (blkPl_261).base (fun _ => none))) hfrom)
      (ls_subroutine_ok_of_blockProgram_ext
        (IsLsBlockProg.externs_eq (prog := (RecordCodecs.Placed.blkPC_257).rebase (RecordCodecs.Placed.blkPl_257).base (fun _ => none))) hpush)
      (ls_subroutine_ok_of_blockProgram_ext
        (IsLsBlockProg.externs_eq (prog := (blkPC_291).rebase (blkPl_291).base (fun _ => none))) hvarint)
      (ls_subroutine_ok_of_blockProgram_ext
        (IsLsBlockProg.externs_eq (prog := (blkPC_263).rebase (blkPl_263).base (fun _ => none))) hskip)
      (ls_subroutine_ok_of_blockProgram_ext
        (IsLsBlockProg.externs_eq (prog := (blkPC_294).rebase (blkPl_294).base (fun _ => none))) hcp)
      (ls_subroutine_ok_of_blockProgram_ext
        (IsLsBlockProg.externs_eq (prog := (blkPC_356).rebase (blkPl_356).base (fun _ => none))) hgrow)
      (ls_subroutine_ok_cl_of_blockProgram_ext
        (IsLsBlockProg.externs_eq (prog := (blkPC_267).rebase (blkPl_267).base (fun _ => none))) hdrop_inner)
      (ls_subroutine_ok_cl_of_blockProgram_ext
        (IsLsBlockProg.externs_eq (prog := (blkPC_270).rebase (blkPl_270).base (fun _ => none))) hdrop_pqr)
  bytesMerge3 :=
    ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (blkPC_290).rebase (blkPl_290).base (fun _ => none))) hbytes
  epochDirectionMerge :=
    ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (blkPC_299).rebase (blkPl_299).base (fun _ => none))) hed
  v1StateMerge :=
    ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (Prost.MessageMerge.Part2.blkPC_298).rebase (Prost.MessageMerge.Part2.blkPl_298).base (fun _ => none))) hv1

/-! ## 3. Own-Block Code-Loaded Theorems (`spqr_decode_state_cl_ok_x` & `spqr_decode_state_cl`) -/

/-- Own-block code-loaded `spqr::decode_state` (`Block 325`) theorem on `decodeStatePlacedProg ext`
(`DecodeStatePlacedOkX canonicalV1InnerHeap A ext`), taking own-block code-loaded contracts for all
cross-block callees. -/
theorem spqr_decode_state_cl_ok_x [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hmemcpy : ∀ hookStack : Nat,
      subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
        (lsρ "memcpy") (libcMemcpySpec hookStack))
    (hsession_memcpy : ∀ hookStack : Nat,
      subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
        (lsρ "memcpy") (sessionMemcpySpec hookStack))
    (hfrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromSpec A)))
    (hpush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushSpec A)))
    (hvarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (Varint.decodeVarint2Spec A)))
    (hskip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A)))
    (hcp : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 294 (Rust.withPanics ext))
      (lsmpl.base 294) (withLsCodeLoaded lsmpl (chainParamsMergeSpec A)))
    (hgrow : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 356 (Rust.withPanics ext))
      (lsmpl.base 356) (withLsCodeLoaded lsmpl (growOneStrideFullSpec A 112 8)))
    (hdrop_inner : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 267 (Rust.withPanics ext))
      (lsmpl.base 267) (withLsCodeLoaded lsmpl (CryptoVerification.SpqrV1.Drop.dropOptProtoInnerStatePlacedSpec A)))
    (hdrop_pqr : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 270 (Rust.withPanics ext))
      (lsmpl.base 270) (withLsCodeLoaded lsmpl (CryptoVerification.SpqrV1.Drop.dropProtoPqRatchetStatePlacedSpec A)))
    (hbytes : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)))
    (hed : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 299 (Rust.withPanics ext))
      (lsmpl.base 299) (withLsCodeRoLoaded lsmpl (epochDirectionMergeSpec A)))
    (hv1 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 298 (Rust.withPanics ext))
      (lsmpl.base 298) (withLsCodeRoLoaded lsmpl (Prost.MessageMerge.v1StateMergePlacedSpec A))) :
    DecodeStatePlacedOkX canonicalV1InnerHeap A ext :=
  decodeState_cl_placed_ok
    (mkDecodeStateCalleeContractsClPlacedX_of_blocks hdealloc hmemcpy hsession_memcpy
      hfrom hpush hvarint hskip hcp hgrow hdrop_inner hdrop_pqr hbytes hed hv1)

/-- Own-block code-loaded `spqr::decode_state` (`Block 325`) theorem on
`libsignalSessionLib.blockProgram lsmpl 325 (Rust.withPanics ext)`. -/
theorem spqr_decode_state_cl [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hmemcpy : ∀ hookStack : Nat,
      subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
        (lsρ "memcpy") (libcMemcpySpec hookStack))
    (hsession_memcpy : ∀ hookStack : Nat,
      subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
        (lsρ "memcpy") (sessionMemcpySpec hookStack))
    (hfrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromSpec A)))
    (hpush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushSpec A)))
    (hvarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (Varint.decodeVarint2Spec A)))
    (hskip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A)))
    (hcp : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 294 (Rust.withPanics ext))
      (lsmpl.base 294) (withLsCodeLoaded lsmpl (chainParamsMergeSpec A)))
    (hgrow : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 356 (Rust.withPanics ext))
      (lsmpl.base 356) (withLsCodeLoaded lsmpl (growOneStrideFullSpec A 112 8)))
    (hdrop_inner : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 267 (Rust.withPanics ext))
      (lsmpl.base 267) (withLsCodeLoaded lsmpl (CryptoVerification.SpqrV1.Drop.dropOptProtoInnerStatePlacedSpec A)))
    (hdrop_pqr : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 270 (Rust.withPanics ext))
      (lsmpl.base 270) (withLsCodeLoaded lsmpl (CryptoVerification.SpqrV1.Drop.dropProtoPqRatchetStatePlacedSpec A)))
    (hbytes : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)))
    (hed : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 299 (Rust.withPanics ext))
      (lsmpl.base 299) (withLsCodeRoLoaded lsmpl (epochDirectionMergeSpec A)))
    (hv1 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 298 (Rust.withPanics ext))
      (lsmpl.base 298) (withLsCodeRoLoaded lsmpl (Prost.MessageMerge.v1StateMergePlacedSpec A))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 325 (Rust.withPanics ext))
      (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl (decodeStatePlacedSpecX canonicalV1InnerHeap A)) := by
  have hok := spqr_decode_state_cl_ok_x hdealloc hmemcpy hsession_memcpy
    hfrom hpush hvarint hskip hcp hgrow hdrop_inner hdrop_pqr hbytes hed hv1
  dsimp only [DecodeStatePlacedOkX, DecodeStatePlacedOk, decodeStatePlacedProg, decodeStatePlacedEntry] at hok
  rw [IsLsBlockProg.eq_blockProgram (prog := (blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))] at hok
  exact hok

end CryptoVerification.SpqrV1.Top.DecodeState
