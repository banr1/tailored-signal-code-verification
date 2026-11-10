/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyEncodedLenBase
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.FetchChunkedV1Placed
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.MsgEncPlacedCS
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncodedLenBase

/-!
# Relocatable Base Definitions for `PolynomialDecoder` and `PolynomialEncoder` `encoded_len`

Defines cross-block `withMsgEnc48CSPlaced` lifting and placed contract propositions for CLI Blocks
`493` (`PolynomialDecoder::encoded_len [local#3]`) and `480`
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

abbrev polynomialDecoderEncodedLenLocal1BlkIdx : Nat := 493
abbrev polynomialEncoderEncodedLenLocal1BlkIdx : Nat := 480

@[simp, arm64_norm, wp_norm]
theorem polynomialDecoderEncodedLenLocal1_fnAddr (pl : MultiPlacement) :
    libsignalSessionLib.fnAddr pl polynomialDecoderEncodedLenLocal1Name =
      pl.base polynomialDecoderEncodedLenLocal1BlkIdx :=
  ls_fnAddr_block (by decide +kernel)

@[simp, arm64_norm, wp_norm]
theorem polynomialEncoderEncodedLenLocal1_fnAddr (pl : MultiPlacement) :
    libsignalSessionLib.fnAddr pl polynomialEncoderEncodedLenLocal1Name =
      pl.base polynomialEncoderEncodedLenLocal1BlkIdx :=
  ls_fnAddr_block (by decide +kernel)

/-- Cross-block `withMsgEnc48CSPlaced` lift for plain (`lsProg_j H`) `subroutine_ok` contracts
    (such as `PolynomialDecoder::encoded_len` and `PolynomialEncoder::encoded_len`). -/
theorem subroutine_ok_withMsgEnc48CSPlaced_of_plain_blk [LibsignalPlacement] {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α} (s0 : State) (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (hcallee : subroutine_ok calleeProg entry spec)
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withMsgEnc48CSPlaced s0 spec) :=
  subroutine_ok_withMsgEnc48CSPlaced_placed_blk s0 hcl0
    (subroutine_ok_withLsCodeLoaded hcallee) hi hj hj_unmut

/-! ## Placed Contract Propositions for Block `493` (`PolynomialDecoder::encoded_len [local#3]`) -/

def PolynomialDecoderEncodedLenLocal1PinnedPlacedOkX [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_493 H) (blkPl_493).base (polynomialDecoderEncodedLenPinnedSpec A)

def PolynomialDecoderEncodedLenLocal1PlacedOkX [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_493 H) (blkPl_493).base (polynomialDecoderEncodedLenSpec A)

def PolynomialDecoderEncodedLenLocal1PinnedPlacedOkExt [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_493 (Rust.withPanics ext)) (blkPl_493).base
    (polynomialDecoderEncodedLenPinnedSpec A)

def PolynomialDecoderEncodedLenLocal1PlacedOkExt [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_493 (Rust.withPanics ext)) (blkPl_493).base
    (polynomialDecoderEncodedLenSpec A)

def PolynomialDecoderEncodedLenLocal1PinnedPlacedOk [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_493 (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_493).base
    (polynomialDecoderEncodedLenPinnedSpec A)

def PolynomialDecoderEncodedLenLocal1PlacedOk [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_493 (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_493).base
    (polynomialDecoderEncodedLenSpec A)

/-! ## Placed Contract Propositions for Block `480` (`PolynomialEncoder::encoded_len [local#3]`) -/

def PolynomialEncoderEncodedLenLocal1PinnedPlacedOkX [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_480 H) (blkPl_480).base (polynomialEncoderEncodedLenPinnedSpec A)

def PolynomialEncoderEncodedLenLocal1PlacedOkX [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_480 H) (blkPl_480).base (polynomialEncoderEncodedLenSpec A)

def PolynomialEncoderEncodedLenLocal1PinnedPlacedOkExt [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_480 (Rust.withPanics ext)) (blkPl_480).base
    (polynomialEncoderEncodedLenPinnedSpec A)

def PolynomialEncoderEncodedLenLocal1PlacedOkExt [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_480 (Rust.withPanics ext)) (blkPl_480).base
    (polynomialEncoderEncodedLenSpec A)

def PolynomialEncoderEncodedLenLocal1PinnedPlacedOk [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_480 (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_480).base
    (polynomialEncoderEncodedLenPinnedSpec A)

def PolynomialEncoderEncodedLenLocal1PlacedOk [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_480 (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_480).base
    (polynomialEncoderEncodedLenSpec A)

end CryptoVerification.Cli.SpqrV1.Prost.MessageEncode
