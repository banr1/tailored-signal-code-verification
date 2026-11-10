/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyEncodedLenBasePlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesPolyPlaced

/-!
# Relocatable Contracts for `PolynomialDecoder` and `PolynomialEncoder` `encoded_len`

Proves `[LibsignalPlacement]` `subroutine_ok` contracts for CLI Blocks `493`
(`PolynomialDecoder::encoded_len [local#3]`) and `480`
(`PolynomialEncoder::encoded_len [local#3]`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.Cli.SpqrV1.Prost.MessageEncode

open Arm64 Arm64.Obj ProofLib CryptoVerification
  CryptoVerification.RustHeap
  CryptoGames.LibsignalSession
  CryptoVerification.LibsignalSession
  CryptoVerification.LibsignalTripleRatchet
  CryptoVerification.SpqrV1.Prost.MessageEncode
  CryptoVerification.Cli.SpqrV1.ProtoRepr.EncodedLen.ChunkedPlaced

/-! ## Block `493`: `PolynomialDecoder::encoded_len [local#3]` -/

theorem polynomialDecoderEncodedLen_local1_pinned_placed_ok_x [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    PolynomialDecoderEncodedLenLocal1PinnedPlacedOkX A H :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.polynomialDecoderEncodedLen_local1_prost_pinned_placed_ok_x A H

theorem polynomialDecoderEncodedLen_local1_placed_ok_x [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    PolynomialDecoderEncodedLenLocal1PlacedOkX A H :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.polynomialDecoderEncodedLen_local1_prost_placed_ok_x A H

theorem polynomialDecoderEncodedLen_local1_pinned_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    PolynomialDecoderEncodedLenLocal1PinnedPlacedOkExt A ext :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.polynomialDecoderEncodedLen_local1_prost_pinned_placed_ok_ext A ext

theorem polynomialDecoderEncodedLen_local1_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    PolynomialDecoderEncodedLenLocal1PlacedOkExt A ext :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.polynomialDecoderEncodedLen_local1_prost_placed_ok_ext A ext

theorem polynomialDecoderEncodedLen_local1_pinned_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    PolynomialDecoderEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  polynomialDecoderEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem polynomialDecoderEncodedLen_local1_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    PolynomialDecoderEncodedLenLocal1PlacedOk C A ctl abs :=
  polynomialDecoderEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem polynomialDecoderEncodedLen_local1_pinned_placed_lscl_ok_x [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok (lsProg_493 H) (blkPl_493).base
      (withLsCodeLoaded lsmpl (polynomialDecoderEncodedLenPinnedSpec A)) :=
  subroutine_ok_withLsCodeLoaded (polynomialDecoderEncodedLen_local1_pinned_placed_ok_x A H)

theorem polynomialDecoderEncodedLen_local1_placed_lscl_ok_x [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok (lsProg_493 H) (blkPl_493).base
      (withLsCodeLoaded lsmpl (polynomialDecoderEncodedLenSpec A)) :=
  subroutine_ok_withLsCodeLoaded (polynomialDecoderEncodedLen_local1_placed_ok_x A H)

/-! ## Block `480`: `PolynomialEncoder::encoded_len [local#3]` -/

theorem polynomialEncoderEncodedLen_local1_pinned_placed_ok_x [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    PolynomialEncoderEncodedLenLocal1PinnedPlacedOkX A H :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.polynomialEncoderEncodedLen_local1_prost_pinned_placed_ok_x A H

theorem polynomialEncoderEncodedLen_local1_placed_ok_x [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    PolynomialEncoderEncodedLenLocal1PlacedOkX A H :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.polynomialEncoderEncodedLen_local1_prost_placed_ok_x A H

theorem polynomialEncoderEncodedLen_local1_pinned_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    PolynomialEncoderEncodedLenLocal1PinnedPlacedOkExt A ext :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.polynomialEncoderEncodedLen_local1_prost_pinned_placed_ok_ext A ext

theorem polynomialEncoderEncodedLen_local1_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    PolynomialEncoderEncodedLenLocal1PlacedOkExt A ext :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.polynomialEncoderEncodedLen_local1_prost_placed_ok_ext A ext

theorem polynomialEncoderEncodedLen_local1_pinned_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    PolynomialEncoderEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  polynomialEncoderEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem polynomialEncoderEncodedLen_local1_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    PolynomialEncoderEncodedLenLocal1PlacedOk C A ctl abs :=
  polynomialEncoderEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem polynomialEncoderEncodedLen_local1_pinned_placed_lscl_ok_x [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok (lsProg_480 H) (blkPl_480).base
      (withLsCodeLoaded lsmpl (polynomialEncoderEncodedLenPinnedSpec A)) :=
  subroutine_ok_withLsCodeLoaded (polynomialEncoderEncodedLen_local1_pinned_placed_ok_x A H)

theorem polynomialEncoderEncodedLen_local1_placed_lscl_ok_x [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok (lsProg_480 H) (blkPl_480).base
      (withLsCodeLoaded lsmpl (polynomialEncoderEncodedLenSpec A)) :=
  subroutine_ok_withLsCodeLoaded (polynomialEncoderEncodedLen_local1_placed_ok_x A H)

end CryptoVerification.Cli.SpqrV1.Prost.MessageEncode
