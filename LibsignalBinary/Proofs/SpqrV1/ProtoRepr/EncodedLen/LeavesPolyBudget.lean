/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsChunkedV1Budget
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesPoly

/-!
# `VmPreserved` Placed Verification of `Polynomial{Decoder,Encoder}::encoded_len`

Unpinning bridges and `[LibsignalPlacement]` `subroutine_ok` theorems with `VmPreserved` for
`PolynomialDecoder::encoded_len` (Blocks `186`, `413`) and `PolynomialEncoder::encoded_len` (Blocks
`173`, `401`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesPolyBudget

open Arm64 ProofLib SepProp
open CryptoVerification
  (LibsignalPlacement blkPC_173 blkPl_173 blkPC_186 blkPl_186
   blkPC_401 blkPl_401 blkPC_413 blkPl_413)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SpqrV1.ProtoRepr
  (polynomialDecoderPBAt_eq_exists_pinned polynomialEncoderPBAt_eq_exists_pinned
   polyDec_entry_pinned_ok polyEnc_entry_pinned_ok)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetExterns)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget
  (withVmPreserved ls_subroutine_ok_plain_vmPreserved)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsChunkedV1Budget
  (polynomialDecoderEncodedLenPinnedSpec polynomialDecoderEncodedLenSpec
   polynomialEncoderEncodedLenPinnedSpec polynomialEncoderEncodedLenSpec)

/-! ## Part 1: `PolynomialDecoder::encoded_len` (Blocks `186`, `413`) -/

theorem polynomialDecoderEncodedLen_ok_of_pinned {prog : Program} {entry : BitVec 64}
    {A : RustAlloc}
    (hpinned : subroutine_ok prog entry (polynomialDecoderEncodedLenPinnedSpec A)) :
    subroutine_ok prog entry (polynomialDecoderEncodedLenSpec A) := by
  refine subroutine_ok_outcome_intro fun ⟨a, pb⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [polynomialDecoderEncodedLenSpec, withVmPreserved] at hpre
  simp only [CryptoVerification.SpqrV1.ProtoRepr.polynomialDecoderEncodedLenSpec,
    polynomialDecoderPBAt_eq_exists_pinned,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine hpinned.mono_outcome ⟨a, g, pb⟩ R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [polynomialDecoderEncodedLenPinnedSpec, polynomialDecoderEncodedLenSpec,
      withVmPreserved] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hvm, hpost⟩
    refine ⟨hvm, ?_⟩
    simp only [CryptoVerification.SpqrV1.ProtoRepr.polynomialDecoderEncodedLenSpec,
      polynomialDecoderPBAt_eq_exists_pinned,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    exact ⟨g, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

def PolynomialDecoderEncodedLenLocal1PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_186).rebase (blkPl_186).base (Rust.withPanics ext))
    (blkPl_186).base (polynomialDecoderEncodedLenPinnedSpec A)

def PolynomialDecoderEncodedLenLocal1PlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_186).rebase (blkPl_186).base (Rust.withPanics ext))
    (blkPl_186).base (polynomialDecoderEncodedLenSpec A)

def PolynomialDecoderEncodedLenLocal1PinnedPlacedOk [LibsignalPlacement] (C : Crypto)
    (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_186).rebase (blkPl_186).base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)))
    (blkPl_186).base (polynomialDecoderEncodedLenPinnedSpec A)

def PolynomialDecoderEncodedLenLocal1PlacedOk [LibsignalPlacement] (C : Crypto)
    (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_186).rebase (blkPl_186).base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)))
    (blkPl_186).base (polynomialDecoderEncodedLenSpec A)

def PolynomialDecoderEncodedLenLocal2PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_413).rebase (blkPl_413).base (Rust.withPanics ext))
    (blkPl_413).base (polynomialDecoderEncodedLenPinnedSpec A)

def PolynomialDecoderEncodedLenLocal2PlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_413).rebase (blkPl_413).base (Rust.withPanics ext))
    (blkPl_413).base (polynomialDecoderEncodedLenSpec A)

def PolynomialDecoderEncodedLenLocal2PinnedPlacedOk [LibsignalPlacement] (C : Crypto)
    (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_413).rebase (blkPl_413).base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)))
    (blkPl_413).base (polynomialDecoderEncodedLenPinnedSpec A)

def PolynomialDecoderEncodedLenLocal2PlacedOk [LibsignalPlacement] (C : Crypto)
    (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_413).rebase (blkPl_413).base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)))
    (blkPl_413).base (polynomialDecoderEncodedLenSpec A)

theorem polynomialDecoderEncodedLen_local1_pinned_placed_ok_hooks [inst : LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_186).rebase (blkPl_186).base H)
      (blkPl_186).base (polynomialDecoderEncodedLenPinnedSpec A) :=
  ls_subroutine_ok_plain_vmPreserved (i := 186) (by decide +kernel)
    (hok := polyDec_entry_pinned_ok _ A _
      (Or.inr ⟨inst, hooksException H, Or.inl ⟨rfl, rfl⟩⟩))

theorem polynomialDecoderEncodedLen_local1_placed_ok_hooks [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_186).rebase (blkPl_186).base H)
      (blkPl_186).base (polynomialDecoderEncodedLenSpec A) :=
  polynomialDecoderEncodedLen_ok_of_pinned
    (polynomialDecoderEncodedLen_local1_pinned_placed_ok_hooks A H)

theorem polynomialDecoderEncodedLen_local1_pinned_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    PolynomialDecoderEncodedLenLocal1PinnedPlacedOkExt A ext :=
  polynomialDecoderEncodedLen_local1_pinned_placed_ok_hooks A (Rust.withPanics ext)

theorem polynomialDecoderEncodedLen_local1_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    PolynomialDecoderEncodedLenLocal1PlacedOkExt A ext :=
  polynomialDecoderEncodedLen_ok_of_pinned
    (polynomialDecoderEncodedLen_local1_pinned_placed_ok_ext A ext)

theorem polynomialDecoderEncodedLen_local1_pinned_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    PolynomialDecoderEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  polynomialDecoderEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem polynomialDecoderEncodedLen_local1_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    PolynomialDecoderEncodedLenLocal1PlacedOk C A ctl abs :=
  polynomialDecoderEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem polynomialDecoderEncodedLen_local2_pinned_placed_ok_hooks [inst : LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_413).rebase (blkPl_413).base H)
      (blkPl_413).base (polynomialDecoderEncodedLenPinnedSpec A) :=
  ls_subroutine_ok_plain_vmPreserved (i := 413) (by decide +kernel)
    (hok := polyDec_entry_pinned_ok _ A _
      (Or.inr ⟨inst, hooksException H, Or.inr ⟨rfl, rfl⟩⟩))

theorem polynomialDecoderEncodedLen_local2_placed_ok_hooks [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_413).rebase (blkPl_413).base H)
      (blkPl_413).base (polynomialDecoderEncodedLenSpec A) :=
  polynomialDecoderEncodedLen_ok_of_pinned
    (polynomialDecoderEncodedLen_local2_pinned_placed_ok_hooks A H)

theorem polynomialDecoderEncodedLen_local2_pinned_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    PolynomialDecoderEncodedLenLocal2PinnedPlacedOkExt A ext :=
  polynomialDecoderEncodedLen_local2_pinned_placed_ok_hooks A (Rust.withPanics ext)

theorem polynomialDecoderEncodedLen_local2_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    PolynomialDecoderEncodedLenLocal2PlacedOkExt A ext :=
  polynomialDecoderEncodedLen_ok_of_pinned
    (polynomialDecoderEncodedLen_local2_pinned_placed_ok_ext A ext)

theorem polynomialDecoderEncodedLen_local2_pinned_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    PolynomialDecoderEncodedLenLocal2PinnedPlacedOk C A ctl abs :=
  polynomialDecoderEncodedLen_local2_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem polynomialDecoderEncodedLen_local2_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    PolynomialDecoderEncodedLenLocal2PlacedOk C A ctl abs :=
  polynomialDecoderEncodedLen_local2_placed_ok_ext A (tripleRatchetExterns C ctl abs)

/-! ## Part 2: `PolynomialEncoder::encoded_len` (Blocks `173`, `401`) -/

theorem polynomialEncoderEncodedLen_ok_of_pinned {prog : Program} {entry : BitVec 64}
    {A : RustAlloc}
    (hpinned : subroutine_ok prog entry (polynomialEncoderEncodedLenPinnedSpec A)) :
    subroutine_ok prog entry (polynomialEncoderEncodedLenSpec A) := by
  refine subroutine_ok_outcome_intro fun ⟨a, pb⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [polynomialEncoderEncodedLenSpec, withVmPreserved] at hpre
  simp only [CryptoVerification.SpqrV1.ProtoRepr.polynomialEncoderEncodedLenSpec,
    polynomialEncoderPBAt_eq_exists_pinned,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine hpinned.mono_outcome ⟨a, g, pb⟩ R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [polynomialEncoderEncodedLenPinnedSpec, polynomialEncoderEncodedLenSpec,
      withVmPreserved] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hvm, hpost⟩
    refine ⟨hvm, ?_⟩
    simp only [CryptoVerification.SpqrV1.ProtoRepr.polynomialEncoderEncodedLenSpec,
      polynomialEncoderPBAt_eq_exists_pinned,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    exact ⟨g, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

def PolynomialEncoderEncodedLenLocal1PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_173).rebase (blkPl_173).base (Rust.withPanics ext))
    (blkPl_173).base (polynomialEncoderEncodedLenPinnedSpec A)

def PolynomialEncoderEncodedLenLocal1PlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_173).rebase (blkPl_173).base (Rust.withPanics ext))
    (blkPl_173).base (polynomialEncoderEncodedLenSpec A)

def PolynomialEncoderEncodedLenLocal1PinnedPlacedOk [LibsignalPlacement] (C : Crypto)
    (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_173).rebase (blkPl_173).base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)))
    (blkPl_173).base (polynomialEncoderEncodedLenPinnedSpec A)

def PolynomialEncoderEncodedLenLocal1PlacedOk [LibsignalPlacement] (C : Crypto)
    (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_173).rebase (blkPl_173).base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)))
    (blkPl_173).base (polynomialEncoderEncodedLenSpec A)

def PolynomialEncoderEncodedLenLocal2PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_401).rebase (blkPl_401).base (Rust.withPanics ext))
    (blkPl_401).base (polynomialEncoderEncodedLenPinnedSpec A)

def PolynomialEncoderEncodedLenLocal2PlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_401).rebase (blkPl_401).base (Rust.withPanics ext))
    (blkPl_401).base (polynomialEncoderEncodedLenSpec A)

def PolynomialEncoderEncodedLenLocal2PinnedPlacedOk [LibsignalPlacement] (C : Crypto)
    (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_401).rebase (blkPl_401).base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)))
    (blkPl_401).base (polynomialEncoderEncodedLenPinnedSpec A)

def PolynomialEncoderEncodedLenLocal2PlacedOk [LibsignalPlacement] (C : Crypto)
    (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_401).rebase (blkPl_401).base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)))
    (blkPl_401).base (polynomialEncoderEncodedLenSpec A)

theorem polynomialEncoderEncodedLen_local1_pinned_placed_ok_hooks [inst : LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_173).rebase (blkPl_173).base H)
      (blkPl_173).base (polynomialEncoderEncodedLenPinnedSpec A) :=
  ls_subroutine_ok_plain_vmPreserved (i := 173) (by decide +kernel)
    (hok := polyEnc_entry_pinned_ok _ A _
      (Or.inr ⟨inst, hooksException H, Or.inl ⟨rfl, rfl⟩⟩))

theorem polynomialEncoderEncodedLen_local1_placed_ok_hooks [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_173).rebase (blkPl_173).base H)
      (blkPl_173).base (polynomialEncoderEncodedLenSpec A) :=
  polynomialEncoderEncodedLen_ok_of_pinned
    (polynomialEncoderEncodedLen_local1_pinned_placed_ok_hooks A H)

theorem polynomialEncoderEncodedLen_local1_pinned_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    PolynomialEncoderEncodedLenLocal1PinnedPlacedOkExt A ext :=
  polynomialEncoderEncodedLen_local1_pinned_placed_ok_hooks A (Rust.withPanics ext)

theorem polynomialEncoderEncodedLen_local1_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    PolynomialEncoderEncodedLenLocal1PlacedOkExt A ext :=
  polynomialEncoderEncodedLen_ok_of_pinned
    (polynomialEncoderEncodedLen_local1_pinned_placed_ok_ext A ext)

theorem polynomialEncoderEncodedLen_local1_pinned_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    PolynomialEncoderEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  polynomialEncoderEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem polynomialEncoderEncodedLen_local1_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    PolynomialEncoderEncodedLenLocal1PlacedOk C A ctl abs :=
  polynomialEncoderEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem polynomialEncoderEncodedLen_local2_pinned_placed_ok_hooks [inst : LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_401).rebase (blkPl_401).base H)
      (blkPl_401).base (polynomialEncoderEncodedLenPinnedSpec A) :=
  ls_subroutine_ok_plain_vmPreserved (i := 401) (by decide +kernel)
    (hok := polyEnc_entry_pinned_ok _ A _
      (Or.inr ⟨inst, hooksException H, Or.inr ⟨rfl, rfl⟩⟩))

theorem polynomialEncoderEncodedLen_local2_placed_ok_hooks [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_401).rebase (blkPl_401).base H)
      (blkPl_401).base (polynomialEncoderEncodedLenSpec A) :=
  polynomialEncoderEncodedLen_ok_of_pinned
    (polynomialEncoderEncodedLen_local2_pinned_placed_ok_hooks A H)

theorem polynomialEncoderEncodedLen_local2_pinned_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    PolynomialEncoderEncodedLenLocal2PinnedPlacedOkExt A ext :=
  polynomialEncoderEncodedLen_local2_pinned_placed_ok_hooks A (Rust.withPanics ext)

theorem polynomialEncoderEncodedLen_local2_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    PolynomialEncoderEncodedLenLocal2PlacedOkExt A ext :=
  polynomialEncoderEncodedLen_ok_of_pinned
    (polynomialEncoderEncodedLen_local2_pinned_placed_ok_ext A ext)

theorem polynomialEncoderEncodedLen_local2_pinned_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    PolynomialEncoderEncodedLenLocal2PinnedPlacedOk C A ctl abs :=
  polynomialEncoderEncodedLen_local2_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem polynomialEncoderEncodedLen_local2_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    PolynomialEncoderEncodedLenLocal2PlacedOk C A ctl abs :=
  polynomialEncoderEncodedLen_local2_placed_ok_ext A (tripleRatchetExterns C ctl abs)

end LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesPolyBudget
