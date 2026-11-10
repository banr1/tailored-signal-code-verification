/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.DefsChunkedV1
public import GeneratedLean.LibsignalSessionPlacedObj
import LibsignalBinary.Proofs.Placed.PlacedCallSym
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core

/-!
# Relocatable Entry Resolution for Polynomial and Chunked `encoded_len`

Defines `[LibsignalPlacement]` block indices and entry resolution for CLI Blocks `480`, `486`,
`493`, and `495`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace CryptoVerification.Cli.SpqrV1.ProtoRepr

open Arm64 Arm64.Obj ProofLib CryptoVerification

abbrev polynomialEncoderEncodedLenLocal1BlkIdx : Nat := 480
abbrev chunkedCt1SampledEncodedLenLocal1BlkIdx : Nat := 486
abbrev polynomialDecoderEncodedLenLocal1BlkIdx : Nat := 493
abbrev chunkedHeaderSentEncodedLenLocal1BlkIdx : Nat := 495

@[simp, arm64_norm, wp_norm]
theorem polynomialDecoderEncodedLenLocal1_fnAddr (pl : MultiPlacement) :
    libsignalSessionLib.fnAddr pl polynomialDecoderEncodedLenLocal1Name = pl.base polynomialDecoderEncodedLenLocal1BlkIdx :=
  ls_fnAddr_block (by decide +kernel)

@[simp, arm64_norm, wp_norm]
theorem polynomialEncoderEncodedLenLocal1_fnAddr (pl : MultiPlacement) :
    libsignalSessionLib.fnAddr pl polynomialEncoderEncodedLenLocal1Name = pl.base polynomialEncoderEncodedLenLocal1BlkIdx :=
  ls_fnAddr_block (by decide +kernel)

@[simp, arm64_norm, wp_norm]
theorem chunkedCt1SampledEncodedLenLocal1_fnAddr (pl : MultiPlacement) :
    libsignalSessionLib.fnAddr pl chunkedCt1SampledEncodedLenLocal1Name = pl.base chunkedCt1SampledEncodedLenLocal1BlkIdx :=
  ls_fnAddr_block (by decide +kernel)

@[simp, arm64_norm, wp_norm]
theorem chunkedHeaderSentEncodedLenLocal1_fnAddr (pl : MultiPlacement) :
    libsignalSessionLib.fnAddr pl chunkedHeaderSentEncodedLenLocal1Name = pl.base chunkedHeaderSentEncodedLenLocal1BlkIdx :=
  ls_fnAddr_block (by decide +kernel)

end CryptoVerification.Cli.SpqrV1.ProtoRepr
