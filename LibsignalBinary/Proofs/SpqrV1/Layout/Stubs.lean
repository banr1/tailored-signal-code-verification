/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout

/-!
# Layout-Independent Stub and Function Offset Aliases

Symbolic aliases for `libsignalSessionCode` external stub offset lemmas and internal function
offset lemmas resolved by symbol name via `ls_stub%` and `ls_lemma% fnOff`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Layout.Stubs

open CryptoVerification
open CryptoVerification.CodeLayout

@[simp, arm64_norm ↓, wp_norm ↓]
abbrev stubOff_rust_no_alloc_shim :=
  ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2"

@[simp, arm64_norm ↓, wp_norm ↓]
abbrev stubOff_rust_alloc :=
  ls_stub% "__rustc::__rust_alloc"

@[simp, arm64_norm ↓, wp_norm ↓]
abbrev stubOff_rust_dealloc :=
  ls_stub% "__rustc::__rust_dealloc"

@[simp, arm64_norm ↓, wp_norm ↓]
abbrev stubOff_rust_realloc :=
  ls_stub% "__rustc::__rust_realloc"

@[simp, arm64_norm ↓, wp_norm ↓]
abbrev stubOff_memcpy :=
  ls_stub% "memcpy"

@[simp, arm64_norm ↓, wp_norm ↓]
abbrev stubOff_memmove :=
  ls_stub% "memmove"

@[simp, arm64_norm ↓, wp_norm ↓]
abbrev stubOff_memset :=
  ls_stub% "memset"

@[simp, arm64_norm ↓, wp_norm ↓]
abbrev stubOff_handle_error :=
  ls_stub% "alloc::raw_vec::handle_error"

@[simp, arm64_norm ↓, wp_norm ↓]
abbrev fnOff_drop_poly16 :=
  ls_lemma% fnOff "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>"

@[simp, arm64_norm ↓, wp_norm ↓]
abbrev fnOff_drop_proto_poly_encoder :=
  ls_lemma% fnOff "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>"

@[simp, arm64_norm ↓, wp_norm ↓]
abbrev fnOff_drop_poly_encoder_local2 :=
  ls_lemma% fnOff "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#2]"

@[simp, arm64_norm ↓, wp_norm ↓]
abbrev fnOff_drop_ct1_sent_local2 :=
  ls_lemma% fnOff "core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#2]"

@[simp, arm64_norm ↓, wp_norm ↓]
abbrev fnOff_drop_ek_sent :=
  ls_lemma% fnOff "core::ptr::drop_glue::<spqr::v1::unchunked::send_ek::EkSent>"

@[simp, arm64_norm ↓, wp_norm ↓]
abbrev fnOff_drop_proto_ct1_sent_ek_received :=
  ls_lemma% fnOff "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived>"

@[simp, arm64_norm ↓, wp_norm ↓]
abbrev fnOff_ct1_sent_from_pb :=
  ls_lemma% fnOff "<spqr::v1::unchunked::send_ct::Ct1Sent>::from_pb"

@[simp, arm64_norm ↓, wp_norm ↓]
abbrev fnOff_ek_sent_ct1_received_from_pb :=
  ls_lemma% fnOff "<spqr::v1::unchunked::send_ek::EkSentCt1Received>::from_pb"

@[simp, arm64_norm ↓, wp_norm ↓]
abbrev fnOff_poly_encoder_from_pb :=
  ls_lemma% fnOff "<spqr::encoding::polynomial::PolyEncoder>::from_pb"

@[simp, arm64_norm ↓, wp_norm ↓]
abbrev fnOff_poly_decoder_from_pb :=
  ls_lemma% fnOff "<spqr::encoding::polynomial::PolyDecoder>::from_pb"

end CryptoVerification.SpqrV1.Layout.Stubs
