/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncodedLen
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncodedLenBaseBudget
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `VmPreserved` `[LibsignalPlacement]` Proofs for `PolynomialDecoder::encoded_len` and `PolynomialEncoder::encoded_len`

Proves `[LibsignalPlacement]` `VmPreserved` contracts for `PolynomialDecoder::encoded_len [local#1, #2]`
(`Blocks 186 & 413`) and `PolynomialEncoder::encoded_len [local#1, #2]` (`Blocks 173 & 401`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncodedLenBudget

open Arm64 ProofLib
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification (LibsignalPlacement lsmpl lsProg_186 lsProg_413 lsProg_173 lsProg_401)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget
  (withVmPreserved ls_subroutine_ok_plain_vmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncodedLenBaseBudget
  (polynomialDecoderEncodedLenPinnedSpec polynomialDecoderEncodedLenSpec
   polynomialEncoderEncodedLenPinnedSpec polynomialEncoderEncodedLenSpec)
open CryptoVerification.SpqrV1.Prost.MessageEncode
  (protoPolynomialDecoderAt_eq_exists_pinned protoPolynomialEncoderAt_eq_exists_pinned)

theorem polynomialDecoderEncodedLen_ok_of_pinned {prog : Program} {entry : BitVec 64} {A : RustAlloc}
    (hpinned : subroutine_ok prog entry (polynomialDecoderEncodedLenPinnedSpec A)) :
    subroutine_ok prog entry (polynomialDecoderEncodedLenSpec A) := by
  apply subroutine_ok_outcome_intro
  intro ⟨a, pb⟩ R s0 hpc hrun hpre hsp
  simp only [polynomialDecoderEncodedLenSpec, withVmPreserved,
    CryptoVerification.SpqrV1.Prost.MessageEncode.polynomialDecoderEncodedLenSpec,
    protoPolynomialDecoderAt_eq_exists_pinned,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine hpinned.mono_outcome ⟨a, g, pb⟩ R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [polynomialDecoderEncodedLenSpec, withVmPreserved,
      CryptoVerification.SpqrV1.Prost.MessageEncode.polynomialDecoderEncodedLenSpec,
      protoPolynomialDecoderAt_eq_exists_pinned,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    exact ⟨g, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

theorem polynomialEncoderEncodedLen_ok_of_pinned {prog : Program} {entry : BitVec 64} {A : RustAlloc}
    (hpinned : subroutine_ok prog entry (polynomialEncoderEncodedLenPinnedSpec A)) :
    subroutine_ok prog entry (polynomialEncoderEncodedLenSpec A) := by
  apply subroutine_ok_outcome_intro
  intro ⟨a, pb⟩ R s0 hpc hrun hpre hsp
  simp only [polynomialEncoderEncodedLenSpec, withVmPreserved,
    CryptoVerification.SpqrV1.Prost.MessageEncode.polynomialEncoderEncodedLenSpec,
    protoPolynomialEncoderAt_eq_exists_pinned,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine hpinned.mono_outcome ⟨a, g, pb⟩ R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [polynomialEncoderEncodedLenSpec, withVmPreserved,
      CryptoVerification.SpqrV1.Prost.MessageEncode.polynomialEncoderEncodedLenSpec,
      protoPolynomialEncoderAt_eq_exists_pinned,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    exact ⟨g, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

section PlacedDec
variable [LibsignalPlacement]

theorem polynomialDecoderEncodedLen_local1_pinned_placed_ok_ext (A : RustAlloc)
    (H : String → Option (State → State)) :
    subroutine_ok (lsProg_186 H) (lsmpl.base 186)
      (polynomialDecoderEncodedLenPinnedSpec A) :=
  ls_subroutine_ok_plain_vmPreserved (by decide +kernel)
    (hok := CryptoVerification.SpqrV1.Prost.MessageEncode.polynomialDecoderEncodedLen_local1_pinned_placed_ok_ext
      A (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException H))

theorem polynomialDecoderEncodedLen_local1_placed_ok_ext (A : RustAlloc)
    (H : String → Option (State → State)) :
    subroutine_ok (lsProg_186 H) (lsmpl.base 186)
      (polynomialDecoderEncodedLenSpec A) :=
  polynomialDecoderEncodedLen_ok_of_pinned
    (polynomialDecoderEncodedLen_local1_pinned_placed_ok_ext A H)

theorem polynomialDecoderEncodedLen_local2_pinned_placed_ok_ext (A : RustAlloc)
    (H : String → Option (State → State)) :
    subroutine_ok (lsProg_413 H) (lsmpl.base 413)
      (polynomialDecoderEncodedLenPinnedSpec A) :=
  ls_subroutine_ok_plain_vmPreserved (by decide +kernel)
    (hok := CryptoVerification.SpqrV1.Prost.MessageEncode.polynomialDecoderEncodedLen_local2_pinned_placed_ok_ext
      A (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException H))

theorem polynomialDecoderEncodedLen_local2_placed_ok_ext (A : RustAlloc)
    (H : String → Option (State → State)) :
    subroutine_ok (lsProg_413 H) (lsmpl.base 413)
      (polynomialDecoderEncodedLenSpec A) :=
  polynomialDecoderEncodedLen_ok_of_pinned
    (polynomialDecoderEncodedLen_local2_pinned_placed_ok_ext A H)

end PlacedDec

section PlacedEnc
variable [LibsignalPlacement]

theorem polynomialEncoderEncodedLen_local1_pinned_placed_ok_ext (A : RustAlloc)
    (H : String → Option (State → State)) :
    subroutine_ok (lsProg_173 H) (lsmpl.base 173)
      (polynomialEncoderEncodedLenPinnedSpec A) :=
  ls_subroutine_ok_plain_vmPreserved (by decide +kernel)
    (hok := CryptoVerification.SpqrV1.Prost.MessageEncode.polynomialEncoderEncodedLen_local1_pinned_placed_ok_ext
      A (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException H))

theorem polynomialEncoderEncodedLen_local1_placed_ok_ext (A : RustAlloc)
    (H : String → Option (State → State)) :
    subroutine_ok (lsProg_173 H) (lsmpl.base 173)
      (polynomialEncoderEncodedLenSpec A) :=
  polynomialEncoderEncodedLen_ok_of_pinned
    (polynomialEncoderEncodedLen_local1_pinned_placed_ok_ext A H)

theorem polynomialEncoderEncodedLen_local2_pinned_placed_ok_ext (A : RustAlloc)
    (H : String → Option (State → State)) :
    subroutine_ok (lsProg_401 H) (lsmpl.base 401)
      (polynomialEncoderEncodedLenPinnedSpec A) :=
  ls_subroutine_ok_plain_vmPreserved (by decide +kernel)
    (hok := CryptoVerification.SpqrV1.Prost.MessageEncode.polynomialEncoderEncodedLen_local2_pinned_placed_ok_ext
      A (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException H))

theorem polynomialEncoderEncodedLen_local2_placed_ok_ext (A : RustAlloc)
    (H : String → Option (State → State)) :
    subroutine_ok (lsProg_401 H) (lsmpl.base 401)
      (polynomialEncoderEncodedLenSpec A) :=
  polynomialEncoderEncodedLen_ok_of_pinned
    (polynomialEncoderEncodedLen_local2_pinned_placed_ok_ext A H)

end PlacedEnc

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncodedLenBudget
