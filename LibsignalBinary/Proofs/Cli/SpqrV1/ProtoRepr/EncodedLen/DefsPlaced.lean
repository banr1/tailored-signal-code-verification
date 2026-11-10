/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.Defs
public import GeneratedLean.LibsignalSessionPlacedObj
import LibsignalBinary.Proofs.Placed.PlacedCallSym
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core

/-!
# Relocatable Entry Resolution for Unchunked `encoded_len` Leaves

Defines `[LibsignalPlacement]` block indices and entry resolution for CLI Blocks `469`, `470`,
`479`, `482`, `487`, `492`, `496`, `499`, and `500`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace CryptoVerification.Cli.SpqrV1.ProtoRepr

open Arm64 Arm64.Obj ProofLib CryptoVerification

abbrev ct1SentEkReceivedEncodedLenLocal1BlkIdx : Nat := 469
abbrev ct2SentEncodedLenLocal1BlkIdx : Nat := 470
abbrev keysUnsampledEncodedLenLocal1BlkIdx : Nat := 479
abbrev headerReceivedEncodedLenLocal1BlkIdx : Nat := 482
abbrev ct1SentEncodedLenLocal1BlkIdx : Nat := 487
abbrev headerSentEncodedLenLocal1BlkIdx : Nat := 492
abbrev ekSentEncodedLenLocal1BlkIdx : Nat := 496
abbrev ekSentCt1ReceivedEncodedLenLocal1BlkIdx : Nat := 499
abbrev noHeaderReceivedEncodedLenLocal1BlkIdx : Nat := 500

@[simp, arm64_norm, wp_norm]
theorem keysUnsampledEncodedLenLocal1_fnAddr (pl : MultiPlacement) :
    libsignalSessionLib.fnAddr pl keysUnsampledEncodedLenLocal1Name = pl.base keysUnsampledEncodedLenLocal1BlkIdx :=
  ls_fnAddr_block (by decide +kernel)

@[simp, arm64_norm, wp_norm]
theorem noHeaderReceivedEncodedLenLocal1_fnAddr (pl : MultiPlacement) :
    libsignalSessionLib.fnAddr pl noHeaderReceivedEncodedLenLocal1Name = pl.base noHeaderReceivedEncodedLenLocal1BlkIdx :=
  ls_fnAddr_block (by decide +kernel)

@[simp, arm64_norm, wp_norm]
theorem ct2SentEncodedLenLocal1_fnAddr (pl : MultiPlacement) :
    libsignalSessionLib.fnAddr pl ct2SentEncodedLenLocal1Name = pl.base ct2SentEncodedLenLocal1BlkIdx :=
  ls_fnAddr_block (by decide +kernel)

@[simp, arm64_norm, wp_norm]
theorem ekSentEncodedLenLocal1_fnAddr (pl : MultiPlacement) :
    libsignalSessionLib.fnAddr pl ekSentEncodedLenLocal1Name = pl.base ekSentEncodedLenLocal1BlkIdx :=
  ls_fnAddr_block (by decide +kernel)

@[simp, arm64_norm, wp_norm]
theorem headerReceivedEncodedLenLocal1_fnAddr (pl : MultiPlacement) :
    libsignalSessionLib.fnAddr pl headerReceivedEncodedLenLocal1Name = pl.base headerReceivedEncodedLenLocal1BlkIdx :=
  ls_fnAddr_block (by decide +kernel)

@[simp, arm64_norm, wp_norm]
theorem headerSentEncodedLenLocal1_fnAddr (pl : MultiPlacement) :
    libsignalSessionLib.fnAddr pl headerSentEncodedLenLocal1Name = pl.base headerSentEncodedLenLocal1BlkIdx :=
  ls_fnAddr_block (by decide +kernel)

@[simp, arm64_norm, wp_norm]
theorem ekSentCt1ReceivedEncodedLenLocal1_fnAddr (pl : MultiPlacement) :
    libsignalSessionLib.fnAddr pl ekSentCt1ReceivedEncodedLenLocal1Name = pl.base ekSentCt1ReceivedEncodedLenLocal1BlkIdx :=
  ls_fnAddr_block (by decide +kernel)

@[simp, arm64_norm, wp_norm]
theorem ct1SentEncodedLenLocal1_fnAddr (pl : MultiPlacement) :
    libsignalSessionLib.fnAddr pl ct1SentEncodedLenLocal1Name = pl.base ct1SentEncodedLenLocal1BlkIdx :=
  ls_fnAddr_block (by decide +kernel)

@[simp, arm64_norm, wp_norm]
theorem ct1SentEkReceivedEncodedLenLocal1_fnAddr (pl : MultiPlacement) :
    libsignalSessionLib.fnAddr pl ct1SentEkReceivedEncodedLenLocal1Name = pl.base ct1SentEkReceivedEncodedLenLocal1BlkIdx :=
  ls_fnAddr_block (by decide +kernel)

end CryptoVerification.Cli.SpqrV1.ProtoRepr
