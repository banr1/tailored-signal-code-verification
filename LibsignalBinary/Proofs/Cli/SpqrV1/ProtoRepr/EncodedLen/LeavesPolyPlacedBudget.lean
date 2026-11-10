/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesPolyPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncodedLenBaseBudget
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsChunkedV1Budget
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesPolyBudget

/-!
# `VmPreserved` Placed Proofs for `PolynomialDecoder` and `PolynomialEncoder` `encoded_len`

Lifts `[LibsignalPlacement]` `subroutine_ok` contracts and `MessageEncode` bridges to `VmPreserved`
for CLI Blocks `493` (`PolynomialDecoder::encoded_len [local#3]`) and `480`
(`PolynomialEncoder::encoded_len [local#3]`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesPolyPlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetExterns)
open CryptoVerification.Cli.SpqrV1.ProtoRepr.EncodedLen.ChunkedPlaced
  (lsProg_493 blkPl_493 lsProg_480 blkPl_480)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget (ls_subroutine_ok_plain_vmPreserved)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsChunkedV1Budget
  (polynomialDecoderEncodedLenPinnedSpec polynomialDecoderEncodedLenSpec
   polynomialEncoderEncodedLenPinnedSpec polynomialEncoderEncodedLenSpec)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesPolyBudget
  (polynomialDecoderEncodedLen_ok_of_pinned polynomialEncoderEncodedLen_ok_of_pinned)

/-! ## Part 1: Block `493` — `PolynomialDecoder::encoded_len [local#3]` -/

theorem polynomialDecoderEncodedLen_local1_pinned_placed_ok_x
    [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok (lsProg_493 H) (blkPl_493).base (polynomialDecoderEncodedLenPinnedSpec A) :=
  ls_subroutine_ok_plain_vmPreserved (i := 493) (by decide +kernel)
    (hok := CryptoVerification.Cli.SpqrV1.ProtoRepr.polynomialDecoderEncodedLen_local1_pinned_placed_ok_x
      A (hooksException H))

theorem polynomialDecoderEncodedLen_local1_placed_ok_x
    [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok (lsProg_493 H) (blkPl_493).base (polynomialDecoderEncodedLenSpec A) :=
  polynomialDecoderEncodedLen_ok_of_pinned
    (polynomialDecoderEncodedLen_local1_pinned_placed_ok_x A H)

def PolynomialDecoderEncodedLenLocal1PinnedPlacedOkExt
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_493 (Rust.withPanics ext)) (blkPl_493).base
    (polynomialDecoderEncodedLenPinnedSpec A)

def PolynomialDecoderEncodedLenLocal1PlacedOkExt
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_493 (Rust.withPanics ext)) (blkPl_493).base
    (polynomialDecoderEncodedLenSpec A)

def PolynomialDecoderEncodedLenLocal1PinnedPlacedOk
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_493 (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_493).base
    (polynomialDecoderEncodedLenPinnedSpec A)

def PolynomialDecoderEncodedLenLocal1PlacedOk
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_493 (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_493).base
    (polynomialDecoderEncodedLenSpec A)

theorem polynomialDecoderEncodedLen_local1_pinned_placed_ok_ext
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) :
    PolynomialDecoderEncodedLenLocal1PinnedPlacedOkExt A ext :=
  polynomialDecoderEncodedLen_local1_pinned_placed_ok_x A (Rust.withPanics ext)

theorem polynomialDecoderEncodedLen_local1_placed_ok_ext
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) :
    PolynomialDecoderEncodedLenLocal1PlacedOkExt A ext :=
  polynomialDecoderEncodedLen_ok_of_pinned
    (polynomialDecoderEncodedLen_local1_pinned_placed_ok_ext A ext)

theorem polynomialDecoderEncodedLen_local1_pinned_placed_ok
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    PolynomialDecoderEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  polynomialDecoderEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem polynomialDecoderEncodedLen_local1_placed_ok
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    PolynomialDecoderEncodedLenLocal1PlacedOk C A ctl abs :=
  polynomialDecoderEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)

/-! ## Part 2: Block `480` — `PolynomialEncoder::encoded_len [local#3]` -/

theorem polynomialEncoderEncodedLen_local1_pinned_placed_ok_x
    [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok (lsProg_480 H) (blkPl_480).base (polynomialEncoderEncodedLenPinnedSpec A) :=
  ls_subroutine_ok_plain_vmPreserved (i := 480) (by decide +kernel)
    (hok := CryptoVerification.Cli.SpqrV1.ProtoRepr.polynomialEncoderEncodedLen_local1_pinned_placed_ok_x
      A (hooksException H))

theorem polynomialEncoderEncodedLen_local1_placed_ok_x
    [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok (lsProg_480 H) (blkPl_480).base (polynomialEncoderEncodedLenSpec A) :=
  polynomialEncoderEncodedLen_ok_of_pinned
    (polynomialEncoderEncodedLen_local1_pinned_placed_ok_x A H)

def PolynomialEncoderEncodedLenLocal1PinnedPlacedOkExt
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_480 (Rust.withPanics ext)) (blkPl_480).base
    (polynomialEncoderEncodedLenPinnedSpec A)

def PolynomialEncoderEncodedLenLocal1PlacedOkExt
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_480 (Rust.withPanics ext)) (blkPl_480).base
    (polynomialEncoderEncodedLenSpec A)

def PolynomialEncoderEncodedLenLocal1PinnedPlacedOk
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_480 (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_480).base
    (polynomialEncoderEncodedLenPinnedSpec A)

def PolynomialEncoderEncodedLenLocal1PlacedOk
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_480 (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_480).base
    (polynomialEncoderEncodedLenSpec A)

theorem polynomialEncoderEncodedLen_local1_pinned_placed_ok_ext
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) :
    PolynomialEncoderEncodedLenLocal1PinnedPlacedOkExt A ext :=
  polynomialEncoderEncodedLen_local1_pinned_placed_ok_x A (Rust.withPanics ext)

theorem polynomialEncoderEncodedLen_local1_placed_ok_ext
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) :
    PolynomialEncoderEncodedLenLocal1PlacedOkExt A ext :=
  polynomialEncoderEncodedLen_ok_of_pinned
    (polynomialEncoderEncodedLen_local1_pinned_placed_ok_ext A ext)

theorem polynomialEncoderEncodedLen_local1_pinned_placed_ok
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    PolynomialEncoderEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  polynomialEncoderEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem polynomialEncoderEncodedLen_local1_placed_ok
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    PolynomialEncoderEncodedLenLocal1PlacedOk C A ctl abs :=
  polynomialEncoderEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)

/-! ## Part 3: Prost `MessageEncode` Bridges for `PolyDecoder1Placed` / `PolyEncoder1Placed` -/

theorem polynomialDecoderEncodedLen_local1_prost_pinned_placed_ok_x
    [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok (lsProg_493 H) (blkPl_493).base
      (LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncodedLenBaseBudget.polynomialDecoderEncodedLenPinnedSpec A) :=
  ls_subroutine_ok_plain_vmPreserved (i := 493) (by decide +kernel)
    (hok := CryptoVerification.Cli.SpqrV1.ProtoRepr.polynomialDecoderEncodedLen_local1_prost_pinned_placed_ok_x
      A (hooksException H))

theorem polynomialDecoderEncodedLen_local1_prost_placed_ok_x
    [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok (lsProg_493 H) (blkPl_493).base
      (LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncodedLenBaseBudget.polynomialDecoderEncodedLenSpec A) :=
  ls_subroutine_ok_plain_vmPreserved (i := 493) (by decide +kernel)
    (hok := CryptoVerification.Cli.SpqrV1.ProtoRepr.polynomialDecoderEncodedLen_local1_prost_placed_ok_x
      A (hooksException H))

theorem polynomialDecoderEncodedLen_local1_prost_pinned_placed_ok_ext
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) :
    subroutine_ok (lsProg_493 (Rust.withPanics ext)) (blkPl_493).base
      (LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncodedLenBaseBudget.polynomialDecoderEncodedLenPinnedSpec A) :=
  polynomialDecoderEncodedLen_local1_prost_pinned_placed_ok_x A (Rust.withPanics ext)

theorem polynomialDecoderEncodedLen_local1_prost_placed_ok_ext
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) :
    subroutine_ok (lsProg_493 (Rust.withPanics ext)) (blkPl_493).base
      (LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncodedLenBaseBudget.polynomialDecoderEncodedLenSpec A) :=
  polynomialDecoderEncodedLen_local1_prost_placed_ok_x A (Rust.withPanics ext)

theorem polynomialEncoderEncodedLen_local1_prost_pinned_placed_ok_x
    [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok (lsProg_480 H) (blkPl_480).base
      (LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncodedLenBaseBudget.polynomialEncoderEncodedLenPinnedSpec A) :=
  ls_subroutine_ok_plain_vmPreserved (i := 480) (by decide +kernel)
    (hok := CryptoVerification.Cli.SpqrV1.ProtoRepr.polynomialEncoderEncodedLen_local1_prost_pinned_placed_ok_x
      A (hooksException H))

theorem polynomialEncoderEncodedLen_local1_prost_placed_ok_x
    [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok (lsProg_480 H) (blkPl_480).base
      (LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncodedLenBaseBudget.polynomialEncoderEncodedLenSpec A) :=
  ls_subroutine_ok_plain_vmPreserved (i := 480) (by decide +kernel)
    (hok := CryptoVerification.Cli.SpqrV1.ProtoRepr.polynomialEncoderEncodedLen_local1_prost_placed_ok_x
      A (hooksException H))

theorem polynomialEncoderEncodedLen_local1_prost_pinned_placed_ok_ext
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) :
    subroutine_ok (lsProg_480 (Rust.withPanics ext)) (blkPl_480).base
      (LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncodedLenBaseBudget.polynomialEncoderEncodedLenPinnedSpec A) :=
  polynomialEncoderEncodedLen_local1_prost_pinned_placed_ok_x A (Rust.withPanics ext)

theorem polynomialEncoderEncodedLen_local1_prost_placed_ok_ext
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) :
    subroutine_ok (lsProg_480 (Rust.withPanics ext)) (blkPl_480).base
      (LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncodedLenBaseBudget.polynomialEncoderEncodedLenSpec A) :=
  polynomialEncoderEncodedLen_local1_prost_placed_ok_x A (Rust.withPanics ext)

end LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesPolyPlacedBudget
