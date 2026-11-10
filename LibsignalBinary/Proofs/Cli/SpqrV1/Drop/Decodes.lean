/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Drop.Decodes

/-!
# Instruction Decodes for CLI SPQR V1 Leaf Drop Glue

Defines symbol names, `fnOff` lemmas, and `spqrDropChainEpochBinCli` instruction decode tables for
the seven leaf SPQR V1 `drop_glue` functions in `libsignalSessionCode_tree`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Drop

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoVerification.RustHeap

open CryptoVerification.CodeLayout

/-- `core::ptr::drop_glue::<[spqr::chain::ChainEpoch]> [local#3]` (34 insns). -/
abbrev _root_.CryptoVerification.Cli.SpqrV1.Drop.dropChainEpochSliceLocal1Name : String :=
  "core::ptr::drop_glue::<[spqr::chain::ChainEpoch]> [local#3]"

/-- `core::ptr::drop_glue::<spqr::proto::pq_ratchet::Chain> [local#2]` (56 insns). -/
abbrev _root_.CryptoVerification.Cli.SpqrV1.Drop.dropProtoSpqrChainName : String :=
  "core::ptr::drop_glue::<spqr::proto::pq_ratchet::Chain> [local#2]"

/-- `core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#3]` (105 insns). -/
abbrev _root_.CryptoVerification.Cli.SpqrV1.Drop.dropPolyEncoderLocal1Name : String :=
  "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#3]"

/-- `core::ptr::drop_glue::<spqr::encoding::polynomial::PolyDecoder> [local#2]` (105 insns). -/
abbrev _root_.CryptoVerification.Cli.SpqrV1.Drop.dropPolyDecoderName : String :=
  "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyDecoder> [local#2]"

/-- `core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::PolynomialEncoder>> [local#2]` (57 insns). -/
abbrev _root_.CryptoVerification.Cli.SpqrV1.Drop.dropOptProtoPolyEncoderName : String :=
  "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::PolynomialEncoder>> [local#2]"

/-- `core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#3]` (34 insns). -/
abbrev _root_.CryptoVerification.Cli.SpqrV1.Drop.dropUnchunkedCt1SentLocal1Name : String :=
  "core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#3]"

/-- `core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent>> [local#2]` (39 insns). -/
abbrev _root_.CryptoVerification.Cli.SpqrV1.Drop.dropOptProtoUnchunkedCt1SentName : String :=
  "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent>> [local#2]"

@[simp, arm64_norm] theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.dropChainEpochSliceLocal1_fnOff :
    libsignalSessionCode.fnOff CryptoVerification.Cli.SpqrV1.Drop.dropChainEpochSliceLocal1Name =
      num% (ls_off% "core::ptr::drop_glue::<[spqr::chain::ChainEpoch]> [local#3]") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<[spqr::chain::ChainEpoch]> [local#3]"

@[simp, arm64_norm] theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.dropProtoSpqrChain_fnOff :
    libsignalSessionCode.fnOff CryptoVerification.Cli.SpqrV1.Drop.dropProtoSpqrChainName =
      num% (ls_off% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::Chain> [local#2]") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<spqr::proto::pq_ratchet::Chain> [local#2]"

@[simp, arm64_norm] theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.dropPolyEncoderLocal1_fnOff :
    libsignalSessionCode.fnOff CryptoVerification.Cli.SpqrV1.Drop.dropPolyEncoderLocal1Name =
      num% (ls_off% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#3]") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#3]"

@[simp, arm64_norm] theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.dropPolyDecoder_fnOff :
    libsignalSessionCode.fnOff CryptoVerification.Cli.SpqrV1.Drop.dropPolyDecoderName =
      num% (ls_off% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyDecoder> [local#2]") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyDecoder> [local#2]"

@[simp, arm64_norm] theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.dropOptProtoPolyEncoder_fnOff :
    libsignalSessionCode.fnOff CryptoVerification.Cli.SpqrV1.Drop.dropOptProtoPolyEncoderName =
      num% (ls_off% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::PolynomialEncoder>> [local#2]") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::PolynomialEncoder>> [local#2]"

@[simp, arm64_norm] theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.dropUnchunkedCt1SentLocal1_fnOff :
    libsignalSessionCode.fnOff CryptoVerification.Cli.SpqrV1.Drop.dropUnchunkedCt1SentLocal1Name =
      num% (ls_off% "core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#3]") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#3]"

@[simp, arm64_norm] theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.dropOptProtoUnchunkedCt1Sent_fnOff :
    libsignalSessionCode.fnOff CryptoVerification.Cli.SpqrV1.Drop.dropOptProtoUnchunkedCt1SentName =
      num% (ls_off% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent>> [local#2]") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent>> [local#2]"

end CryptoVerification.SpqrV1.Drop

namespace CryptoVerification.SpqrV1.Layout.L1

open Lean Meta Elab Command Arm64 CryptoVerification.CodeLayout

end CryptoVerification.SpqrV1.Layout.L1

namespace CryptoVerification.SpqrV1.Drop

open CryptoVerification.SpqrV1.Layout.L1

gen_fn_decodes libsignalSessionCode_tree spqrDropChainEpochBinCli ["core::ptr::drop_glue::<[spqr::chain::ChainEpoch]> [local#3]", "core::ptr::drop_glue::<spqr::proto::pq_ratchet::Chain> [local#2]", "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#3]", "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyDecoder> [local#2]", "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::PolynomialEncoder>> [local#2]", "core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#3]", "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent>> [local#2]"]

end CryptoVerification.SpqrV1.Drop
