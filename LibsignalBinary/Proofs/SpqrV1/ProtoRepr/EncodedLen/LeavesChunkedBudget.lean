/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsChunkedV1Budget
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesChunked

/-!
# `VmPreserved` Bridges and Placed Propositions for `Chunked.Ct1Sampled::encoded_len`

Unpinning bridges and `[LibsignalPlacement]` `subroutine_ok` propositions for
`V1State.Chunked.Ct1Sampled::encoded_len` (Blocks `179`, `407`) with `VmPreserved`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesChunkedBudget

open _root_.Arm64 _root_.Arm64.Obj ProofLib SepProp
open CryptoVerification
  (LibsignalPlacement lsmpl withLsCodeLoaded blkPC_179 blkPl_179 blkPC_407 blkPl_407)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SpqrV1.ProtoRepr (chunkedCt1SampledPBAt_eq_exists_pinned)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetExterns)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsChunkedV1Budget
  (chunkedCt1SampledEncodedLenPinnedSpec chunkedCt1SampledEncodedLenSpec)

theorem chunkedCt1SampledEncodedLen_ok_of_pinned {prog : Program} {entry : BitVec 64}
    {A : RustAlloc}
    (hpinned : subroutine_ok prog entry (chunkedCt1SampledEncodedLenPinnedSpec A)) :
    subroutine_ok prog entry (chunkedCt1SampledEncodedLenSpec A) := by
  refine subroutine_ok_outcome_intro fun ⟨a, m⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [chunkedCt1SampledEncodedLenSpec, withVmPreserved] at hpre
  simp only [CryptoVerification.SpqrV1.ProtoRepr.chunkedCt1SampledEncodedLenSpec,
    chunkedCt1SampledPBAt_eq_exists_pinned,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine hpinned.mono_outcome ⟨a, g, m⟩ R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [chunkedCt1SampledEncodedLenPinnedSpec, chunkedCt1SampledEncodedLenSpec,
      withVmPreserved] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hvm, hpost⟩
    refine ⟨hvm, ?_⟩
    simp only [CryptoVerification.SpqrV1.ProtoRepr.chunkedCt1SampledEncodedLenSpec,
      chunkedCt1SampledPBAt_eq_exists_pinned,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    exact ⟨g, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

theorem chunkedCt1SampledEncodedLen_lscl_ok_of_pinned {prog : Program} {entry : BitVec 64}
    {pl : MultiPlacement} {A : RustAlloc}
    (hpinned : subroutine_ok prog entry
      (withLsCodeLoaded pl (chunkedCt1SampledEncodedLenPinnedSpec A))) :
    subroutine_ok prog entry (withLsCodeLoaded pl (chunkedCt1SampledEncodedLenSpec A)) := by
  refine subroutine_ok_outcome_intro fun ⟨a, m⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [withLsCodeLoaded, chunkedCt1SampledEncodedLenSpec, withVmPreserved] at hpre
  simp only [CryptoVerification.SpqrV1.ProtoRepr.chunkedCt1SampledEncodedLenSpec,
    chunkedCt1SampledPBAt_eq_exists_pinned,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine hpinned.mono_outcome ⟨a, g, m⟩ R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, chunkedCt1SampledEncodedLenPinnedSpec,
      chunkedCt1SampledEncodedLenSpec, withVmPreserved] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hvm, hpost⟩
    refine ⟨hvm, ?_⟩
    simp only [CryptoVerification.SpqrV1.ProtoRepr.chunkedCt1SampledEncodedLenSpec,
      chunkedCt1SampledPBAt_eq_exists_pinned,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    exact ⟨g, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

def ChunkedCt1SampledEncodedLenLocal1PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_179).rebase (blkPl_179).base (Rust.withPanics ext))
    (blkPl_179).base (withLsCodeLoaded lsmpl (chunkedCt1SampledEncodedLenPinnedSpec A))

def ChunkedCt1SampledEncodedLenLocal1PlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_179).rebase (blkPl_179).base (Rust.withPanics ext))
    (blkPl_179).base (withLsCodeLoaded lsmpl (chunkedCt1SampledEncodedLenSpec A))

def ChunkedCt1SampledEncodedLenLocal1PinnedPlacedOk [LibsignalPlacement] (C : Crypto)
    (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  ChunkedCt1SampledEncodedLenLocal1PinnedPlacedOkExt A (tripleRatchetExterns C ctl abs)

def ChunkedCt1SampledEncodedLenLocal1PlacedOk [LibsignalPlacement] (C : Crypto)
    (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  ChunkedCt1SampledEncodedLenLocal1PlacedOkExt A (tripleRatchetExterns C ctl abs)

def ChunkedCt1SampledEncodedLenLocal2PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_407).rebase (blkPl_407).base (Rust.withPanics ext))
    (blkPl_407).base (withLsCodeLoaded lsmpl (chunkedCt1SampledEncodedLenPinnedSpec A))

def ChunkedCt1SampledEncodedLenLocal2PlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_407).rebase (blkPl_407).base (Rust.withPanics ext))
    (blkPl_407).base (withLsCodeLoaded lsmpl (chunkedCt1SampledEncodedLenSpec A))

def ChunkedCt1SampledEncodedLenLocal2PinnedPlacedOk [LibsignalPlacement] (C : Crypto)
    (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  ChunkedCt1SampledEncodedLenLocal2PinnedPlacedOkExt A (tripleRatchetExterns C ctl abs)

def ChunkedCt1SampledEncodedLenLocal2PlacedOk [LibsignalPlacement] (C : Crypto)
    (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  ChunkedCt1SampledEncodedLenLocal2PlacedOkExt A (tripleRatchetExterns C ctl abs)

end LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesChunkedBudget
