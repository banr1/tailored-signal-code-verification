/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core

/-!
# CLI SPQR V1 `prost::encoding::message::encode` Symbol Names and Offsets

Defines CLI symbol names and `fnOff` lemmas for `PolynomialEncoder`, `ChainParams`,
`PolynomialDecoder`, and `EpochDirection` message encoders (`[local#3]`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Prost.MessageEncode

open Arm64 ProofLib ProofLib.ProgramReflection
  CryptoVerification.CodeLayout

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

/-! ## Symbol Names & Offsets -/

abbrev _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodePolyEncoder1Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialEncoder, alloc::vec::Vec<u8>> [local#3]"

abbrev _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeChainParams1Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#3]"

abbrev _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodePolyDecoder1Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialDecoder, alloc::vec::Vec<u8>> [local#3]"

abbrev _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]"

@[simp, arm64_norm] theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodePolyEncoder1_fnOff :
    libsignalSessionCode.fnOff CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodePolyEncoder1Name = (ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialEncoder, alloc::vec::Vec<u8>> [local#3]") :=
  (ls_lemma% fnOff "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialEncoder, alloc::vec::Vec<u8>> [local#3]")

@[simp, arm64_norm] theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeChainParams1_fnOff :
    libsignalSessionCode.fnOff CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeChainParams1Name = (ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#3]") :=
  (ls_lemma% fnOff "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#3]")

@[simp, arm64_norm] theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodePolyDecoder1_fnOff :
    libsignalSessionCode.fnOff CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodePolyDecoder1Name = (ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialDecoder, alloc::vec::Vec<u8>> [local#3]") :=
  (ls_lemma% fnOff "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialDecoder, alloc::vec::Vec<u8>> [local#3]")

@[simp, arm64_norm] theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1_fnOff :
    libsignalSessionCode.fnOff CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encodeEpochDirection1Name = (ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]") :=
  (ls_lemma% fnOff "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#3]")

end CryptoVerification.SpqrV1.Prost.MessageEncode
