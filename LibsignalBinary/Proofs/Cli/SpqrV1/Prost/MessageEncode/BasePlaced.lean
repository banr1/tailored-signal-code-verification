/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.Base
public import GeneratedLean.LibsignalSessionPlacedObj
import LibsignalBinary.Proofs.Placed.PlacedCallSym
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core
import GeneratedLean.LibsignalSessionObj

/-!
# Relocatable Block Indices and Entry Resolution for `MessageEncode`

Defines `[LibsignalPlacement]` block indices and entry-offset lemmas for CLI SPQR V1 message
encoders (Blocks `453` and `455`–`459`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace CryptoVerification.Cli.SpqrV1.Prost.MessageEncode

open Arm64 Arm64.Obj ProofLib CryptoVerification

abbrev encodeChainParams1BlkIdx : Nat := 453
abbrev encodePolyDecoder1BlkIdx : Nat := 455
abbrev encodePolyEncoder1BlkIdx : Nat := 456
abbrev encodeEpochDirection1BlkIdx : Nat := 457
abbrev encodeEkSentCt1Received1BlkIdx : Nat := 458
abbrev encodeCt1Sent1BlkIdx : Nat := 459

abbrev encodeEkSentCt1Received1CliName : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::v1_state::unchunked::EkSentCt1Received, alloc::vec::Vec<u8>> [local#3]"

abbrev encodeCt1Sent1CliName : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent, alloc::vec::Vec<u8>> [local#3]"

@[simp, arm64_norm, wp_norm]
theorem encodePolyEncoder1_fnAddr (pl : MultiPlacement) :
    libsignalSessionLib.fnAddr pl encodePolyEncoder1Name = pl.base encodePolyEncoder1BlkIdx :=
  ls_fnAddr_block (by decide +kernel)

@[simp, arm64_norm, wp_norm]
theorem encodeChainParams1_fnAddr (pl : MultiPlacement) :
    libsignalSessionLib.fnAddr pl encodeChainParams1Name = pl.base encodeChainParams1BlkIdx :=
  ls_fnAddr_block (by decide +kernel)

@[simp, arm64_norm, wp_norm]
theorem encodePolyDecoder1_fnAddr (pl : MultiPlacement) :
    libsignalSessionLib.fnAddr pl encodePolyDecoder1Name = pl.base encodePolyDecoder1BlkIdx :=
  ls_fnAddr_block (by decide +kernel)

@[simp, arm64_norm, wp_norm]
theorem encodeEpochDirection1_fnAddr (pl : MultiPlacement) :
    libsignalSessionLib.fnAddr pl encodeEpochDirection1Name = pl.base encodeEpochDirection1BlkIdx :=
  ls_fnAddr_block (by decide +kernel)

@[simp, arm64_norm, wp_norm]
theorem encodeEkSentCt1Received1Cli_fnAddr (pl : MultiPlacement) :
    libsignalSessionLib.fnAddr pl encodeEkSentCt1Received1CliName = pl.base encodeEkSentCt1Received1BlkIdx :=
  ls_fnAddr_block (by decide +kernel)

@[simp, arm64_norm, wp_norm]
theorem encodeCt1Sent1Cli_fnAddr (pl : MultiPlacement) :
    libsignalSessionLib.fnAddr pl encodeCt1Sent1CliName = pl.base encodeCt1Sent1BlkIdx :=
  ls_fnAddr_block (by decide +kernel)

end CryptoVerification.Cli.SpqrV1.Prost.MessageEncode
