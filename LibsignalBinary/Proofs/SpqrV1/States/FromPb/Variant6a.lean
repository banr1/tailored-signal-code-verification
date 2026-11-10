/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBase
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Epilogue
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 6 (`HeaderReceived`, `+1464`) — Part A

Header unpacking (`pbA + 8..128`), low-stack layout, `+10396` error epilogue, inline
`ProtoPolynomialDecoder` deallocation (`+10316..+10396`), and entry header-load steps (`+1464 -> +1520 | +3760`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff libsignalSessionCode
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  statesFromPb_fnOff
  stubOff_rust_no_alloc_shim
  stubOff_rust_alloc
  stubOff_rust_dealloc
  stubOff_memcpy
  stubOff_handle_error

/-! ## 1. Pure Model & Header Unpacking (`pbA + 8..128`) -/

/-- The 15 header words/subwords at `pbA + 8..128` read by `+1464..+1504`. -/
def v6hr_headersAt (pbA : BitVec 64)
    (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 : BitVec 64) : SepProp :=
  ((pbA + 8#64) ↦₆₄ w8) ∗ ((pbA + 16#64) ↦₆₄ w16) ∗
  ((pbA + 24#64) ↦₆₄ w24) ∗ ((pbA + 32#64) ↦₆₄ w32) ∗
  ((pbA + 40#64) ↦₆₄ w40) ∗ ((pbA + 48#64) ↦₆₄ w48) ∗
  ((pbA + 56#64) ↦₆₄ w56) ∗ ((pbA + 64#64) ↦₆₄ w64) ∗
  ((pbA + 72#64) ↦₆₄ w72) ∗ ((pbA + 80#64) ↦₆₄ w80) ∗
  ((pbA + 88#64) ↦₆₄ w88) ∗ ((pbA + 96#64) ↦₆₄ w96) ∗
  ((pbA + 104#64) ↦₆₄ w104) ∗
  ((pbA + 112#64) ↦₃₂ d112) ∗ ((pbA + 116#64) ↦₃₂ d116) ∗
  ((pbA + 120#64) ↦₆₄ w120)

theorem v6hr_headersAt_entails_memRegion_120 (pbA : BitVec 64)
    (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 : BitVec 64) :
    v6hr_headersAt pbA w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 d112 d116 w120 ⊢
      memRegion (pbA + 8#64) 120 := by
  unfold v6hr_headersAt
  exact collapse_top <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (pointsTo32_entails_memRegion_4 _ _) <|
    collapse_step (pointsTo32_entails_memRegion_4 _ _) <|
    Drop.pointsTo64_entails_memRegion _ _

theorem v6hr_headersAt_entails_dealloc (pbA : BitVec 64)
    (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 : BitVec 64) :
    (pbA ↦₆₄ 0x8000000000000006#64) ∗
    v6hr_headersAt pbA w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 d112 d116 w120 ∗
    memRegion (pbA + 128#64) 96 ⊢
      memRegion pbA optProtoInnerStateSize := by
  dsimp only [optProtoInnerStateSize]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left
    (v6hr_headersAt_entails_memRegion_120 pbA w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 d112 d116 w120))) ?_
  exact collapse_top <|
    collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Entails.refl _) <|
    Entails.refl _

theorem v6hr_optProtoInnerStateAt_headerReceived (A : RustAlloc) (pbA : BitVec 64)
    (s : V1State.Chunked.HeaderReceived) :
    optProtoInnerStateAt A pbA (some (.headerReceived s)) =
      (pbA ↦₆₄ 0x8000000000000006#64) ∗
      optProtoUnchunkedHeaderReceivedAt A (pbA + 8#64) s.uc ∗
      optProtoPolynomialDecoderAt A (pbA + 88#64) (s.receivingEk.map pbToProtoPolyDecoder) ∗
      memRegion (pbA + 128#64) 96 := by
  have h88 : pbA + 8#64 + 80#64 = pbA + 88#64 := by bv_omega
  simp only [optProtoInnerStateAt, protoInnerStateAt,
    protoChunkedHeaderReceivedAt, h88, sepConj_assoc]

theorem v6hr_uc_none_unpack (A : RustAlloc) (pbA : BitVec 64) :
    optProtoUnchunkedHeaderReceivedAt A (pbA + 8#64) none ⊢
      (∃∗ w16 : BitVec 64, ∃∗ w24 : BitVec 64, ∃∗ w32 : BitVec 64,
       ∃∗ w40 : BitVec 64, ∃∗ w48 : BitVec 64, ∃∗ w56 : BitVec 64,
       ∃∗ w64 : BitVec 64, ∃∗ w72 : BitVec 64, ∃∗ w80 : BitVec 64,
        ((pbA + 8#64) ↦₆₄ noneCap) ∗
        ((pbA + 16#64) ↦₆₄ w16) ∗ ((pbA + 24#64) ↦₆₄ w24) ∗
        ((pbA + 32#64) ↦₆₄ w32) ∗ ((pbA + 40#64) ↦₆₄ w40) ∗
        ((pbA + 48#64) ↦₆₄ w48) ∗ ((pbA + 56#64) ↦₆₄ w56) ∗
        ((pbA + 64#64) ↦₆₄ w64) ∗ ((pbA + 72#64) ↦₆₄ w72) ∗
        ((pbA + 80#64) ↦₆₄ w80)) := by
  have h16 : pbA + 8#64 + 8#64 = pbA + 16#64 := by bv_omega
  unfold optProtoUnchunkedHeaderReceivedAt
  rw [h16]
  have hsplit : memRegion (pbA + 16#64) 72 ⊢
      (∃∗ w16 : BitVec 64, ((pbA + 16#64) ↦₆₄ w16)) ∗
      (∃∗ w24 : BitVec 64, ((pbA + 24#64) ↦₆₄ w24)) ∗
      (∃∗ w32 : BitVec 64, ((pbA + 32#64) ↦₆₄ w32)) ∗
      (∃∗ w40 : BitVec 64, ((pbA + 40#64) ↦₆₄ w40)) ∗
      (∃∗ w48 : BitVec 64, ((pbA + 48#64) ↦₆₄ w48)) ∗
      (∃∗ w56 : BitVec 64, ((pbA + 56#64) ↦₆₄ w56)) ∗
      (∃∗ w64 : BitVec 64, ((pbA + 64#64) ↦₆₄ w64)) ∗
      (∃∗ w72 : BitVec 64, ((pbA + 72#64) ↦₆₄ w72)) ∗
      (∃∗ w80 : BitVec 64, ((pbA + 80#64) ↦₆₄ w80)) := by
    exact split_top <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      mem64_entails _
  refine Entails.trans (sepConj_mono_right hsplit) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro w80
  apply Entails.sepExists_elim; intro w72
  apply Entails.sepExists_elim; intro w64
  apply Entails.sepExists_elim; intro w56
  apply Entails.sepExists_elim; intro w48
  apply Entails.sepExists_elim; intro w40
  apply Entails.sepExists_elim; intro w32
  apply Entails.sepExists_elim; intro w24
  apply Entails.sepExists_elim; intro w16
  apply Entails.sepExists_right w16; apply Entails.sepExists_right w24
  apply Entails.sepExists_right w32; apply Entails.sepExists_right w40
  apply Entails.sepExists_right w48; apply Entails.sepExists_right w56
  apply Entails.sepExists_right w64; apply Entails.sepExists_right w72
  apply Entails.sepExists_right w80
  exact Entails.of_eq (by ac_rfl)

theorem v6hr_uc_some_auth_none_unpack (A : RustAlloc) (pbA : BitVec 64)
    (hdr : List (BitVec 8)) (epoch : BitVec 64) :
    optProtoUnchunkedHeaderReceivedAt A (pbA + 8#64)
      (some { hdr := hdr, auth := none, epoch := epoch }) ⊢
      (∃∗ cap_hdr : BitVec 64, ∃∗ ptr_hdr : BitVec 64,
       ∃∗ w40 : BitVec 64, ∃∗ w48 : BitVec 64, ∃∗ w56 : BitVec 64,
       ∃∗ w64 : BitVec 64, ∃∗ w72 : BitVec 64,
        ((pbA + 8#64) ↦₆₄ cap_hdr) ∗
        ((pbA + 16#64) ↦₆₄ ptr_hdr) ∗
        ((pbA + 24#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗
        ((pbA + 32#64) ↦₆₄ noneCap) ∗
        ((pbA + 40#64) ↦₆₄ w40) ∗ ((pbA + 48#64) ↦₆₄ w48) ∗
        ((pbA + 56#64) ↦₆₄ w56) ∗ ((pbA + 64#64) ↦₆₄ w64) ∗
        ((pbA + 72#64) ↦₆₄ w72) ∗ ((pbA + 80#64) ↦₆₄ epoch) ∗
        vecU8Payload A cap_hdr ptr_hdr hdr) := by
  have h16 : pbA + 8#64 + 8#64 = pbA + 16#64 := by bv_omega
  have h24 : pbA + 8#64 + 16#64 = pbA + 24#64 := by bv_omega
  have h32 : pbA + 8#64 + 24#64 = pbA + 32#64 := by bv_omega
  have h40 : pbA + 32#64 + 8#64 = pbA + 40#64 := by bv_omega
  have h80 : pbA + 8#64 + 72#64 = pbA + 80#64 := by bv_omega
  unfold optProtoUnchunkedHeaderReceivedAt protoUnchunkedHeaderReceivedAt
    optProtoAuthenticatorAt vecU8 vecU8At vecHeader vecU8Payload
  dsimp only
  rw [h16, h24, h32, h40, h80]
  have hsplit : memRegion (pbA + 40#64) 40 ⊢
      (∃∗ w40 : BitVec 64, ((pbA + 40#64) ↦₆₄ w40)) ∗
      (∃∗ w48 : BitVec 64, ((pbA + 48#64) ↦₆₄ w48)) ∗
      (∃∗ w56 : BitVec 64, ((pbA + 56#64) ↦₆₄ w56)) ∗
      (∃∗ w64 : BitVec 64, ((pbA + 64#64) ↦₆₄ w64)) ∗
      (∃∗ w72 : BitVec 64, ((pbA + 72#64) ↦₆₄ w72)) := by
    exact split_top <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      mem64_entails _
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right hsplit))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro w72
  apply Entails.sepExists_elim; intro w64
  apply Entails.sepExists_elim; intro w56
  apply Entails.sepExists_elim; intro w48
  apply Entails.sepExists_elim; intro w40
  apply Entails.sepExists_elim; intro cap_hdr
  apply Entails.sepExists_elim; intro ptr_hdr
  apply Entails.sepExists_right cap_hdr; apply Entails.sepExists_right ptr_hdr
  apply Entails.sepExists_right w40; apply Entails.sepExists_right w48
  apply Entails.sepExists_right w56; apply Entails.sepExists_right w64
  apply Entails.sepExists_right w72
  exact Entails.of_eq (by ac_rfl)

theorem v6hr_uc_some_auth_some_unpack (A : RustAlloc) (pbA : BitVec 64)
    (hdr : List (BitVec 8)) (authPb : ProtoAuthenticator) (epoch : BitVec 64) :
    optProtoUnchunkedHeaderReceivedAt A (pbA + 8#64)
      (some { hdr := hdr, auth := some authPb, epoch := epoch }) ⊢
      (∃∗ cap_hdr : BitVec 64, ∃∗ ptr_hdr : BitVec 64,
       ∃∗ c1 : BitVec 64, ∃∗ p1 : BitVec 64,
       ∃∗ c2 : BitVec 64, ∃∗ p2 : BitVec 64,
        ((pbA + 8#64) ↦₆₄ cap_hdr) ∗
        ((pbA + 16#64) ↦₆₄ ptr_hdr) ∗
        ((pbA + 24#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗
        ((pbA + 32#64) ↦₆₄ c1) ∗
        ((pbA + 40#64) ↦₆₄ p1) ∗
        ((pbA + 48#64) ↦₆₄ BitVec.ofNat 64 authPb.rootKey.length) ∗
        ((pbA + 56#64) ↦₆₄ c2) ∗
        ((pbA + 64#64) ↦₆₄ p2) ∗
        ((pbA + 72#64) ↦₆₄ BitVec.ofNat 64 authPb.macKey.length) ∗
        ((pbA + 80#64) ↦₆₄ epoch) ∗
        vecU8Payload A cap_hdr ptr_hdr hdr ∗
        vecU8Payload A c1 p1 authPb.rootKey ∗
        vecU8Payload A c2 p2 authPb.macKey) := by
  have h16 : pbA + 8#64 + 8#64 = pbA + 16#64 := by bv_omega
  have h24 : pbA + 8#64 + 16#64 = pbA + 24#64 := by bv_omega
  have h32 : pbA + 8#64 + 24#64 = pbA + 32#64 := by bv_omega
  have h40 : pbA + 32#64 + 8#64 = pbA + 40#64 := by bv_omega
  have h48 : pbA + 32#64 + 16#64 = pbA + 48#64 := by bv_omega
  have h56 : pbA + 32#64 + 24#64 = pbA + 56#64 := by bv_omega
  have h64 : pbA + 56#64 + 8#64 = pbA + 64#64 := by bv_omega
  have h72 : pbA + 56#64 + 16#64 = pbA + 72#64 := by bv_omega
  have h80 : pbA + 8#64 + 72#64 = pbA + 80#64 := by bv_omega
  unfold optProtoUnchunkedHeaderReceivedAt protoUnchunkedHeaderReceivedAt
    optProtoAuthenticatorAt protoAuthenticatorAt vecU8 vecU8At vecHeader vecU8Payload
  dsimp only
  rw [h16, h24, h32, h40, h48, h56, h64, h72, h80]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro c2
  apply Entails.sepExists_elim; intro p2
  apply Entails.sepExists_elim; intro c1
  apply Entails.sepExists_elim; intro p1
  apply Entails.sepExists_elim; intro cap_hdr
  apply Entails.sepExists_elim; intro ptr_hdr
  apply Entails.sepExists_right cap_hdr; apply Entails.sepExists_right ptr_hdr
  apply Entails.sepExists_right c1; apply Entails.sepExists_right p1
  apply Entails.sepExists_right c2; apply Entails.sepExists_right p2
  exact Entails.of_eq (by ac_rfl)

theorem v6hr_dec_none_unpack (A : RustAlloc) (pbA : BitVec 64) :
    optProtoPolynomialDecoderAt A (pbA + 88#64) none ⊢
      (∃∗ w96 : BitVec 64, ∃∗ w104 : BitVec 64,
       ∃∗ d112 : BitVec 32, ∃∗ d116 : BitVec 32, ∃∗ w120 : BitVec 64,
        ((pbA + 88#64) ↦₆₄ noneCap) ∗
        ((pbA + 96#64) ↦₆₄ w96) ∗
        ((pbA + 104#64) ↦₆₄ w104) ∗
        ((pbA + 112#64) ↦₃₂ d112) ∗
        ((pbA + 116#64) ↦₃₂ d116) ∗
        ((pbA + 120#64) ↦₆₄ w120)) := by
  have h96 : pbA + 88#64 + 8#64 = pbA + 96#64 := by bv_omega
  unfold optProtoPolynomialDecoderAt
  rw [h96]
  have hsplit : memRegion (pbA + 96#64) 32 ⊢
      (∃∗ w96 : BitVec 64, ((pbA + 96#64) ↦₆₄ w96)) ∗
      (∃∗ w104 : BitVec 64, ((pbA + 104#64) ↦₆₄ w104)) ∗
      (∃∗ d112 : BitVec 32, ((pbA + 112#64) ↦₃₂ d112)) ∗
      (∃∗ d116 : BitVec 32, ((pbA + 116#64) ↦₃₂ d116)) ∗
      (∃∗ w120 : BitVec 64, ((pbA + 120#64) ↦₆₄ w120)) := by
    exact split_top <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      split_step (mem32_entails _) <|
      split_step (mem32_entails _) <|
      mem64_entails _
  refine Entails.trans (sepConj_mono_right hsplit) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro w120
  apply Entails.sepExists_elim; intro d116
  apply Entails.sepExists_elim; intro d112
  apply Entails.sepExists_elim; intro w104
  apply Entails.sepExists_elim; intro w96
  apply Entails.sepExists_right w96; apply Entails.sepExists_right w104
  apply Entails.sepExists_right d112; apply Entails.sepExists_right d116
  apply Entails.sepExists_right w120
  exact Entails.of_eq (by ac_rfl)

theorem v6hr_pointsTo64_split_1_4_2_1 (a w : BitVec 64) :
    (a ↦₆₄ w) =
      (a ↦₈ w.extractLsb' 0 8) ∗
      ((a + 1#64) ↦₃₂ w.extractLsb' 8 32) ∗
      ((a + 5#64) ↦₁₆ w.extractLsb' 40 16) ∗
      ((a + 7#64) ↦₈ w.extractLsb' 56 8) := by
  have hb1 : (w.extractLsb' 8 32).extractLsb' 0 8 = w.extractLsb' 8 8 := by bv_kernel
  have hb2 : (w.extractLsb' 8 32).extractLsb' 8 8 = w.extractLsb' 16 8 := by bv_kernel
  have hb3 : (w.extractLsb' 8 32).extractLsb' 16 8 = w.extractLsb' 24 8 := by bv_kernel
  have hb4 : (w.extractLsb' 8 32).extractLsb' 24 8 = w.extractLsb' 32 8 := by bv_kernel
  have hb5 : (w.extractLsb' 40 16).extractLsb' 0 8 = w.extractLsb' 40 8 := by bv_kernel
  have hb6 : (w.extractLsb' 40 16).extractLsb' 8 8 = w.extractLsb' 48 8 := by bv_kernel
  rw [ProofLib.pointsTo64_eq_pointsToBytes a w,
      ProofLib.pointsTo32_eq_pointsToBytes (a + 1#64) (w.extractLsb' 8 32),
      ProofLib.pointsTo16_eq_pointsToBytes (a + 5#64) (w.extractLsb' 40 16)]
  simp only [unpack64, unpack32, unpack16,
    ProofLib.pointsToBytes_cons, ProofLib.pointsToBytes_nil,
    hb1, hb2, hb3, hb4, hb5, hb6,
    sepConj_emp, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]

theorem v6hr_byte_pad7_entails_64 (a : BitVec 64) (b : BitVec 8) :
    (a ↦₈ b) ∗ memRegion (a + 1#64) 7 ⊢
      ∃∗ w : BitVec 64, ⌜EncoderFromPb.loByte w = b⌝ ∗ (a ↦₆₄ w) := by
  have hsplit : memRegion (a + 1#64) 7 ⊢
      (∃∗ d1 : BitVec 32, ((a + 1#64) ↦₃₂ d1)) ∗
      (∃∗ h5 : BitVec 16, ((a + 5#64) ↦₁₆ h5)) ∗
      (∃∗ b7 : BitVec 8, ((a + 7#64) ↦₈ b7)) := by
    exact split_top <|
      split_step (mem32_entails _) <|
      split_step (mem16_entails _) <|
      mem8_entails _
  refine Entails.trans (sepConj_mono_right hsplit) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro b7
  apply Entails.sepExists_elim; intro h5
  apply Entails.sepExists_elim; intro d1
  let w : BitVec 64 := b7 ++ h5 ++ d1 ++ b
  refine Entails.sepExists_right w ?_
  have hw0 : w.extractLsb' 0 8 = b := by dsimp [w]; bv_kernel
  have hw1 : w.extractLsb' 8 32 = d1 := by dsimp [w]; bv_kernel
  have hw5 : w.extractLsb' 40 16 = h5 := by dsimp [w]; bv_kernel
  have hw7 : w.extractLsb' 56 8 = b7 := by dsimp [w]; bv_kernel
  have hlo : EncoderFromPb.loByte w = b := hw0
  refine Entails.pure_right hlo ?_
  rw [v6hr_pointsTo64_split_1_4_2_1 a w, hw0, hw1, hw5, hw7]
  exact Entails.refl _

theorem v6hr_pointsTo64_entails_byte_pad7 (a w : BitVec 64) (b : BitVec 8)
    (hw : EncoderFromPb.loByte w = b) :
    (a ↦₆₄ w) ⊢ (a ↦₈ b) ∗ memRegion (a + 1#64) 7 := by
  rw [pointsTo64_split_1_7 a w, hw]
  exact sepConj_mono_right
    (EncoderFromPb.length_hiBytes7 w ▸ ProofLib.pointsToBytes_entails_memRegion (a + 1#64) (EncoderFromPb.hiBytes7 w))

theorem v6hr_dec_some_unpack (A : RustAlloc) (pbA : BitVec 64)
    (d : ProtoPolynomialDecoder) :
    optProtoPolynomialDecoderAt A (pbA + 88#64) (some d) ⊢
      (∃∗ ptsCap : BitVec 64, ∃∗ ptsPtr : BitVec 64, ∃∗ w120 : BitVec 64,
        ⌜d.pts.length ≤ ptsCap.toNat ∧ ptsCap.toNat * 24 < 2 ^ 63 ∧ ptsPtr ≠ 0#64 ∧
         EncoderFromPb.loByte w120 = boolByte d.isComplete⌝ ∗
        ((pbA + 88#64) ↦₆₄ ptsCap) ∗
        ((pbA + 96#64) ↦₆₄ ptsPtr) ∗
        ((pbA + 104#64) ↦₆₄ BitVec.ofNat 64 d.pts.length) ∗
        ((pbA + 112#64) ↦₃₂ d.ptsNeeded) ∗
        ((pbA + 116#64) ↦₃₂ d.polys) ∗
        ((pbA + 120#64) ↦₆₄ w120) ∗
        (if ptsCap = 0#64 then emp
         else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr d.pts ∗
           memRegion (ptsPtr + BitVec.ofNat 64 (d.pts.length * 24))
             ((ptsCap.toNat - d.pts.length) * 24))) := by
  have h96 : pbA + 88#64 + 8#64 = pbA + 96#64 := by bv_omega
  have h104 : pbA + 88#64 + 16#64 = pbA + 104#64 := by bv_omega
  have h112 : pbA + 88#64 + 24#64 = pbA + 112#64 := by bv_omega
  have h116 : pbA + 88#64 + 28#64 = pbA + 116#64 := by bv_omega
  have h120 : pbA + 88#64 + 32#64 = pbA + 120#64 := by bv_omega
  have h121 : pbA + 88#64 + 33#64 = pbA + 120#64 + 1#64 := by bv_omega
  unfold optProtoPolynomialDecoderAt protoPolynomialDecoderAt vecVecU8At vecOf
    Poly.vecHeaderBytes vecAt vecBuf vecHeader protoPolynomialDecoderPtsNeededOff
    protoPolynomialDecoderPolysOff protoPolynomialDecoderIsCompleteOff
    protoPolynomialDecoderPadOff protoPolynomialDecoderPadSize
  rw [h96, h104, h112, h116, h120, h121]
  have h8_64 := v6hr_byte_pad7_entails_64 (pbA + 120#64) (boolByte d.isComplete)
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro ptsCap; apply Entails.sepExists_right ptsCap
  apply Entails.sepExists_elim; intro ptsPtr; apply Entails.sepExists_right ptsPtr
  refine Entails.trans
    (Entails.of_eq (show _ =
      (((pbA + 120#64) ↦₈ boolByte d.isComplete) ∗ memRegion (pbA + 120#64 + 1#64) 7) ∗
      (((pbA + 88#64) ↦₆₄ ptsCap) ∗ ((pbA + 96#64) ↦₆₄ ptsPtr) ∗
       ((pbA + 104#64) ↦₆₄ BitVec.ofNat 64 d.pts.length) ∗
       ⌜d.pts.length ≤ ptsCap.toNat ∧ ptsCap.toNat * 24 < 2 ^ 63 ∧ ptsPtr ≠ 0#64⌝ ∗
       (if ptsCap = 0#64 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr d.pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (d.pts.length * 24))
            ((ptsCap.toNat - d.pts.length) * 24)) ∗
       ((pbA + 112#64) ↦₃₂ d.ptsNeeded) ∗
       ((pbA + 116#64) ↦₃₂ d.polys)) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left h8_64) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro w120; apply Entails.sepExists_right w120
  simp only [sepConj_assoc]
  apply Entails.pure_left; intro hw120
  refine Entails.trans
    (Entails.of_eq (show _ =
      ⌜d.pts.length ≤ ptsCap.toNat ∧ ptsCap.toNat * 24 < 2 ^ 63 ∧ ptsPtr ≠ 0#64⌝ ∗
      (((pbA + 88#64) ↦₆₄ ptsCap) ∗ ((pbA + 96#64) ↦₆₄ ptsPtr) ∗
       ((pbA + 104#64) ↦₆₄ BitVec.ofNat 64 d.pts.length) ∗
       ((pbA + 112#64) ↦₃₂ d.ptsNeeded) ∗ ((pbA + 116#64) ↦₃₂ d.polys) ∗
       ((pbA + 120#64) ↦₆₄ w120) ∗
       (if ptsCap = 0#64 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr d.pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (d.pts.length * 24))
            ((ptsCap.toNat - d.pts.length) * 24))) by ac_rfl)) ?_
  apply Entails.pure_left; intro ⟨h1, h2, h3⟩
  exact Entails.pure_right ⟨h1, h2, h3, hw120⟩ (Entails.of_eq (by ac_rfl))

/-! ## 2. Low-Stack Layout (`sp + 0..240`), Error Epilogue (`+10396`), & Decoder Deallocation (`+10316..+10396`) -/
def v6hr_lowStackGaps (sp0 : BitVec 64) : SepProp :=
  memRegion (sp0 - 2400#64) 80 ∗
  memRegion (sp0 - 2312#64) 40 ∗
  memRegion (sp0 - 2248#64) 32 ∗
  memRegion (sp0 - 2212#64) 4 ∗
  memRegion (sp0 - 2196#64) 4

def v6hr_lowStackAt (sp0 : BitVec 64)
    (v80 v128 v136 v144 : BitVec 64) (d184 : BitVec 32)
    (v192 : BitVec 64) (d200 : BitVec 32)
    (v208 v216 v224 v232 : BitVec 64) : SepProp :=
  ((sp0 - 2320#64) ↦₆₄ v80) ∗
  ((sp0 - 2272#64) ↦₆₄ v128) ∗
  ((sp0 - 2264#64) ↦₆₄ v136) ∗
  ((sp0 - 2256#64) ↦₆₄ v144) ∗
  ((sp0 - 2216#64) ↦₃₂ d184) ∗
  ((sp0 - 2208#64) ↦₆₄ v192) ∗
  ((sp0 - 2200#64) ↦₃₂ d200) ∗
  ((sp0 - 2192#64) ↦₆₄ v208) ∗
  ((sp0 - 2184#64) ↦₆₄ v216) ∗
  ((sp0 - 2176#64) ↦₆₄ v224) ∗
  ((sp0 - 2168#64) ↦₆₄ v232) ∗
  v6hr_lowStackGaps sp0

theorem v6hr_memRegion_2304_split_fsp (fsp : BitVec 64) :
    memRegion fsp 2304 ⊢
      memRegion fsp 80 ∗
      (∃∗ v80 : BitVec 64, ((fsp + 80#64) ↦₆₄ v80)) ∗
      memRegion (fsp + 88#64) 40 ∗
      (∃∗ v128 : BitVec 64, ((fsp + 128#64) ↦₆₄ v128)) ∗
      (∃∗ v136 : BitVec 64, ((fsp + 136#64) ↦₆₄ v136)) ∗
      (∃∗ v144 : BitVec 64, ((fsp + 144#64) ↦₆₄ v144)) ∗
      memRegion (fsp + 152#64) 32 ∗
      (∃∗ d184 : BitVec 32, ((fsp + 184#64) ↦₃₂ d184)) ∗
      memRegion (fsp + 188#64) 4 ∗
      (∃∗ v192 : BitVec 64, ((fsp + 192#64) ↦₆₄ v192)) ∗
      (∃∗ d200 : BitVec 32, ((fsp + 200#64) ↦₃₂ d200)) ∗
      memRegion (fsp + 204#64) 4 ∗
      (∃∗ v208 : BitVec 64, ((fsp + 208#64) ↦₆₄ v208)) ∗
      (∃∗ v216 : BitVec 64, ((fsp + 216#64) ↦₆₄ v216)) ∗
      (∃∗ v224 : BitVec 64, ((fsp + 224#64) ↦₆₄ v224)) ∗
      (∃∗ v232 : BitVec 64, ((fsp + 232#64) ↦₆₄ v232)) ∗
      memRegion (fsp + 240#64) 2064 := by
  exact split_top <|
    split_step0 (Entails.refl _) <|
    split_step (mem64_entails _) <|
    split_step (Entails.refl _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (Entails.refl _) <|
    split_step (mem32_entails _) <|
    split_step (Entails.refl _) <|
    split_step (mem64_entails _) <|
    split_step (mem32_entails _) <|
    split_step (Entails.refl _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    Entails.refl _

theorem v6hr_memRegion_2304_entails_lowStackAt (sp0 : BitVec 64) :
    memRegion (sp0 - 2400#64) 2304 ⊢
      ∃∗ v80 : BitVec 64, ∃∗ v128 : BitVec 64, ∃∗ v136 : BitVec 64, ∃∗ v144 : BitVec 64,
      ∃∗ d184 : BitVec 32, ∃∗ v192 : BitVec 64, ∃∗ d200 : BitVec 32,
      ∃∗ v208 : BitVec 64, ∃∗ v216 : BitVec 64, ∃∗ v224 : BitVec 64, ∃∗ v232 : BitVec 64,
        v6hr_lowStackAt sp0 v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 ∗
        memRegion (sp0 - 2160#64) 2064 := by
  have hsplit := v6hr_memRegion_2304_split_fsp (sp0 - 2400#64)
  rw [show (sp0 - 2400#64) + 80#64 = sp0 - 2320#64 by bv_omega,
      show (sp0 - 2400#64) + 88#64 = sp0 - 2312#64 by bv_omega,
      show (sp0 - 2400#64) + 128#64 = sp0 - 2272#64 by bv_omega,
      show (sp0 - 2400#64) + 136#64 = sp0 - 2264#64 by bv_omega,
      show (sp0 - 2400#64) + 144#64 = sp0 - 2256#64 by bv_omega,
      show (sp0 - 2400#64) + 152#64 = sp0 - 2248#64 by bv_omega,
      show (sp0 - 2400#64) + 184#64 = sp0 - 2216#64 by bv_omega,
      show (sp0 - 2400#64) + 188#64 = sp0 - 2212#64 by bv_omega,
      show (sp0 - 2400#64) + 192#64 = sp0 - 2208#64 by bv_omega,
      show (sp0 - 2400#64) + 200#64 = sp0 - 2200#64 by bv_omega,
      show (sp0 - 2400#64) + 204#64 = sp0 - 2196#64 by bv_omega,
      show (sp0 - 2400#64) + 208#64 = sp0 - 2192#64 by bv_omega,
      show (sp0 - 2400#64) + 216#64 = sp0 - 2184#64 by bv_omega,
      show (sp0 - 2400#64) + 224#64 = sp0 - 2176#64 by bv_omega,
      show (sp0 - 2400#64) + 232#64 = sp0 - 2168#64 by bv_omega,
      show (sp0 - 2400#64) + 240#64 = sp0 - 2160#64 by bv_omega] at hsplit
  refine Entails.trans hsplit ?_
  unfold v6hr_lowStackAt v6hr_lowStackGaps
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro v232
  apply Entails.sepExists_elim; intro v224
  apply Entails.sepExists_elim; intro v216
  apply Entails.sepExists_elim; intro v208
  apply Entails.sepExists_elim; intro d200
  apply Entails.sepExists_elim; intro v192
  apply Entails.sepExists_elim; intro d184
  apply Entails.sepExists_elim; intro v144
  apply Entails.sepExists_elim; intro v136
  apply Entails.sepExists_elim; intro v128
  apply Entails.sepExists_elim; intro v80
  apply Entails.sepExists_right v80; apply Entails.sepExists_right v128
  apply Entails.sepExists_right v136; apply Entails.sepExists_right v144
  apply Entails.sepExists_right d184; apply Entails.sepExists_right v192
  apply Entails.sepExists_right d200; apply Entails.sepExists_right v208
  apply Entails.sepExists_right v216; apply Entails.sepExists_right v224
  apply Entails.sepExists_right v232
  exact Entails.of_eq (by ac_rfl)

theorem v6hr_memRegion_2304_collapse_fsp (fsp : BitVec 64)
    (v80 v128 v136 v144 : BitVec 64) (d184 : BitVec 32)
    (v192 : BitVec 64) (d200 : BitVec 32)
    (v208 v216 v224 v232 : BitVec 64) :
    memRegion fsp 80 ∗
    ((fsp + 80#64) ↦₆₄ v80) ∗
    memRegion (fsp + 88#64) 40 ∗
    ((fsp + 128#64) ↦₆₄ v128) ∗
    ((fsp + 136#64) ↦₆₄ v136) ∗
    ((fsp + 144#64) ↦₆₄ v144) ∗
    memRegion (fsp + 152#64) 32 ∗
    ((fsp + 184#64) ↦₃₂ d184) ∗
    memRegion (fsp + 188#64) 4 ∗
    ((fsp + 192#64) ↦₆₄ v192) ∗
    ((fsp + 200#64) ↦₃₂ d200) ∗
    memRegion (fsp + 204#64) 4 ∗
    ((fsp + 208#64) ↦₆₄ v208) ∗
    ((fsp + 216#64) ↦₆₄ v216) ∗
    ((fsp + 224#64) ↦₆₄ v224) ∗
    ((fsp + 232#64) ↦₆₄ v232) ∗
    memRegion (fsp + 240#64) 2064 ⊢
    memRegion fsp 2304 := by
  exact collapse_top <|
    collapse_step0 (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Entails.refl _) <|
    collapse_step (pointsTo32_entails_memRegion_4 _ _) <|
    collapse_step (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (pointsTo32_entails_memRegion_4 _ _) <|
    collapse_step (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    Entails.refl _

theorem v6hr_lowStackAt_entails_memRegion_2304 (sp0 : BitVec 64)
    (v80 v128 v136 v144 : BitVec 64) (d184 : BitVec 32)
    (v192 : BitVec 64) (d200 : BitVec 32)
    (v208 v216 v224 v232 : BitVec 64) :
    v6hr_lowStackAt sp0 v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 ∗
    memRegion (sp0 - 2160#64) 2064 ⊢
      memRegion (sp0 - 2400#64) 2304 := by
  have hcol := v6hr_memRegion_2304_collapse_fsp (sp0 - 2400#64)
    v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232
  rw [show (sp0 - 2400#64) + 80#64 = sp0 - 2320#64 by bv_omega,
      show (sp0 - 2400#64) + 88#64 = sp0 - 2312#64 by bv_omega,
      show (sp0 - 2400#64) + 128#64 = sp0 - 2272#64 by bv_omega,
      show (sp0 - 2400#64) + 136#64 = sp0 - 2264#64 by bv_omega,
      show (sp0 - 2400#64) + 144#64 = sp0 - 2256#64 by bv_omega,
      show (sp0 - 2400#64) + 152#64 = sp0 - 2248#64 by bv_omega,
      show (sp0 - 2400#64) + 184#64 = sp0 - 2216#64 by bv_omega,
      show (sp0 - 2400#64) + 188#64 = sp0 - 2212#64 by bv_omega,
      show (sp0 - 2400#64) + 192#64 = sp0 - 2208#64 by bv_omega,
      show (sp0 - 2400#64) + 200#64 = sp0 - 2200#64 by bv_omega,
      show (sp0 - 2400#64) + 204#64 = sp0 - 2196#64 by bv_omega,
      show (sp0 - 2400#64) + 208#64 = sp0 - 2192#64 by bv_omega,
      show (sp0 - 2400#64) + 216#64 = sp0 - 2184#64 by bv_omega,
      show (sp0 - 2400#64) + 224#64 = sp0 - 2176#64 by bv_omega,
      show (sp0 - 2400#64) + 232#64 = sp0 - 2168#64 by bv_omega,
      show (sp0 - 2400#64) + 240#64 = sp0 - 2160#64 by bv_omega] at hcol
  unfold v6hr_lowStackAt v6hr_lowStackGaps
  exact Entails.trans (Entails.of_eq (by ac_rfl)) hcol

set_option maxHeartbeats 800000 in
theorem v6hr_states_from_pb_err_10396
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64)
    (v80 v128 v136 v144 : BitVec 64) (d184 : BitVec 32)
    (v192 : BitVec 64) (d200 : BitVec 32)
    (v208 v216 v224 v232 : BitVec 64)
    (err : LibsignalSpqrV1.Error) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10396#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx25_1 : (s1.readReg64 .x25).extractLsb' 0 8 = spqrErrorByte err)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 ∗
        memRegion (s0.sp - 2160#64) 2064 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err err)) ∗
          Rest ∗
          stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  rw [memRegion_out_928_split_32 out]
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro v24
  apply ProofLib.SepWP.exists_left; intro v16
  apply ProofLib.SepWP.exists_left; intro v8
  apply ProofLib.SepWP.exists_left; intro v0
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 60#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗
      (out ↦₆₄ v0) ∗
      ((out + 8#64) ↦₈ spqrErrorByte err) ∗
      memRegion (out + 9#64) 919 ∗
      Rest)
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x8 = noneCap ∧
      sm.readReg64 .x19 = out ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · unfold v6hr_lowStackAt
    simp only [sepConj_assoc]
    states_from_pb_fetches_range b (Rust.withPanics ext) 10396 20
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have htail := out_8_32_entails_err_tail out (s1.readReg64 .x25)
        (s1.readReg64 .x26) v216
      rw [hx25_1] at htail
      have hst := v6hr_lowStackAt_entails_memRegion_2304 s0.sp
        v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232
      unfold v6hr_lowStackAt at hst
      simp only [sepConj_assoc] at hst
      refine Entails.trans
        (Entails.of_eq (show _ =
          (((s0.sp - 2320#64) ↦₆₄ v80) ∗
           ((s0.sp - 2272#64) ↦₆₄ v128) ∗
           ((s0.sp - 2264#64) ↦₆₄ v136) ∗
           ((s0.sp - 2256#64) ↦₆₄ v144) ∗
           ((s0.sp - 2216#64) ↦₃₂ d184) ∗
           ((s0.sp - 2208#64) ↦₆₄ v192) ∗
           ((s0.sp - 2200#64) ↦₃₂ d200) ∗
           ((s0.sp - 2192#64) ↦₆₄ v208) ∗
           ((s0.sp - 2184#64) ↦₆₄ v216) ∗
           ((s0.sp - 2176#64) ↦₆₄ v224) ∗
           ((s0.sp - 2168#64) ↦₆₄ v232) ∗
           v6hr_lowStackGaps s0.sp ∗
           memRegion (s0.sp - 2160#64) 2064) ∗
          (((out + 8#64) ↦₆₄ s1.readReg64 .x25) ∗
           ((out + 16#64) ↦₆₄ s1.readReg64 .x26) ∗
           ((out + 24#64) ↦₆₄ v216) ∗
           memRegion (out + 32#64) 896) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           statesFromPbSavedCells s0 ∗
           (out ↦₆₄ v0) ∗
           Rest) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hst (sepConj_mono_left htail)) (Entails.of_eq (by ac_rfl))
    · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx8_2, hx19_2, htr2⟩
    exact states_from_pb_epilogue_60 s0 s2 out err v0 Rest
      hsp0_align hpc2 hrun2 hsp2 hx8_2 hx19_2 htr2

@[reducible]
def v6hr_Saved10324Preserved (s0 s : State) (fsp out ptsPtr ptsCap x25_val : BitVec 64) : Prop :=
  s.sp = fsp ∧
  s.readReg64 .x19 = out ∧
  s.readReg64 .x21 = ptsPtr ∧
  s.readReg64 .x28 = ptsCap ∧
  s.readReg64 .x25 = x25_val ∧
  TraceCalleeSaved s s0

theorem v6hr_sub_ok_dealloc_125316
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + (bv% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_dealloc")))
      (rustDeallocSpec A) :=
  sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_dealloc"))) (b := b) (X := Rust.withPanics ext)
      statesFromPb_fnOff stubOff_rust_dealloc (by decide))
    hA.dealloc

theorem v6hr_proto_decoder_dealloc_body_10348
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 : State) (fsp out ptsPtr ptsCap x25_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10348#64 →
      s.status = .Running →
      v6hr_Saved10324Preserved s0 s fsp out ptsPtr ptsCap x25_val →
      s.readReg64 .x23 = cnt →
      s.readReg64 .x20 = cur + 8#64 →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10336#64) s
        (vecU8 A cur bs ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v6hr_Saved10324Preserved s0 sm fsp out ptsPtr ptsCap x25_val ∧
          sm.readReg64 .x23 = cnt ∧
          sm.readReg64 .x20 = cur + 8#64) := by
  have hdealloc := v6hr_sub_ok_dealloc_125316 (b := b) (A := A) (ext := ext) hA
  simp only [rustDeallocSpec] at hdealloc
  states_from_pb_fetches_range b (Rust.withPanics ext) 10348 24
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  intro cur cnt bs s Frame hpc hrun hpres hx23 hx20
  rcases hpres with ⟨hsp, hx19, hx21, hx28, hx25, htrace⟩
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A cur bs)) ?_
  apply SepWP.exists_sepConj_left; intro cap
  apply SepWP.exists_sepConj_left; intro vptr
  have hstep : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (entry + 10336#64) s
      (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8 ∗
        vecCapPtrDealloc A cap vptr) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v6hr_Saved10324Preserved s0 sm fsp out ptsPtr ptsCap x25_val ∧
        sm.readReg64 .x23 = cnt ∧
        sm.readReg64 .x20 = cur + 8#64) := by
    dsimp only [vecCapPtrDealloc]
    by_cases hcap : (cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; wp_done
    · wp_steps; wp_apply; wp_steps; refine Drop.align_pre (by rw [hsp]; ac_rfl) ?_; wp_done
  exact SepWP.strengthen_entails_const
    (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)) hstep

theorem v6hr_proto_decoder_dealloc_loop_10348
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 : State) (fsp out ptsPtr ptsCap x25_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10348#64 →
      s.status = .Running →
      v6hr_Saved10324Preserved s0 s fsp out ptsPtr ptsCap x25_val →
      s.readReg64 .x23 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x20 = cur + 8#64 →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10372#64) s
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v6hr_Saved10324Preserved s0 sm fsp out ptsPtr ptsCap x25_val) := by
  have hbody := v6hr_proto_decoder_dealloc_body_10348 (b := b) (A := A) (ext := ext)
    hA s0 fsp out ptsPtr ptsCap x25_val hfsp_align
  states_from_pb_fetches_range b (Rust.withPanics ext) 10336 12
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hbody ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  intro rest
  induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur s Frame _ hlen hpc hrun hpres hx23 hx20
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine Drop.seq_clean (mid := entry + 10336#64)
      (P_mid := memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) tl ∗ Frame))
      (Q := fun sm => v6hr_Saved10324Preserved s0 sm fsp out ptsPtr ptsCap x25_val ∧
        sm.readReg64 .x23 = BitVec.ofNat 64 (bs :: tl).length ∧
        sm.readReg64 .x20 = cur + 8#64)
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs s _ hpc hrun hpres hx23 hx20) ?_
    intro s1 hpc1 hrun1 ⟨hpres1, hx23_1, hx20_1⟩
    rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx23_1 ⊢
      rcases hpres1 with ⟨hsp_1, hx19_1, hx21_1, hx28_1, hx25_1, htrace_1⟩
      wp_steps; wp_done
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_add_one_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [List.length_cons, ofNat_succ_eq_add_one] at hx23_1
      refine Drop.seq_clean (mid := entry + 10348#64)
        (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) (bs2 :: tl2) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ (memRegion cur 24 ∗ Frame))
        (Q := fun sm => v6hr_Saved10324Preserved s0 sm fsp out ptsPtr ptsCap x25_val ∧
          sm.readReg64 .x23 = BitVec.ofNat 64 (bs2 :: tl2).length ∧
          sm.readReg64 .x20 = (cur + 24#64) + 8#64)
        ?_ ?_
      · rcases hpres1 with ⟨hsp_1, hx19_1, hx21_1, hx28_1, hx25_1, htrace_1⟩
        rw [sep_push_body]; wp_steps; rw [add_24_add_8]; wp_done
      · intro s2 hpc2 hrun2 ⟨hpres2, hx23_2, hx20_2⟩
        have hrec := ih (cur + 24#64) s2 (memRegion cur 24 ∗ Frame)
          (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 hpres2 hx23_2 hx20_2
        refine SepWP.strengthen_entails_const ?_ hrec
        have hsplit := cons_len_mul bs (bs2 :: tl2) 24
        have hbound : 24 + (bs2 :: tl2).length * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 24 ((bs2 :: tl2).length * 24) hbound]
        exact Entails.refl _

theorem v6hr_states_from_pb_dealloc_proto_decoder_10324
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s : State) (fsp out ptsPtr ptsCap x25_val : BitVec 64)
    (pts : List (List (BitVec 8))) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10324#64)
    (hrun : s.status = .Running)
    (hpres : v6hr_Saved10324Preserved s0 s fsp out ptsPtr ptsCap x25_val)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 pts.length) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10396#64) s
      ((if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v6hr_Saved10324Preserved s0 sm fsp out ptsPtr ptsCap x25_val) := by
  have hdealloc := v6hr_sub_ok_dealloc_125316 (b := b) (A := A) (ext := ext) hA
  have hloop := v6hr_proto_decoder_dealloc_loop_10348 (b := b) (A := A) (ext := ext)
    hA s0 fsp out ptsPtr ptsCap x25_val hfsp_align
  simp only [rustDeallocSpec] at hdealloc
  states_from_pb_fetches_range b (Rust.withPanics ext) 10324 12
  states_from_pb_fetches_range b (Rust.withPanics ext) 10372 24
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc hloop hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  refine Drop.seq_clean (mid := entry + 10372#64)
    (P_mid := (if ptsCap = 0#64 then emp
      else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗ memRegion ptsPtr (ptsCap.toNat * 24)) ∗
      A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => v6hr_Saved10324Preserved s0 sm fsp out ptsPtr ptsCap x25_val)
    ?_ ?_
  · cases pts with
    | nil =>
      rcases hpres with ⟨hsp, hx19, hx21, hx28, hx25, htrace⟩
      simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, arrayAt, emp_sepConj] at hx23 ⊢
      wp_steps; refine Drop.align_pre (by ac_rfl) ?_; wp_done
    | cons bs tl =>
      have hlen_pos : 0 < (bs :: tl).length := by simp
      have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by
        have : (bs :: tl).length * 24 ≤ ptsCap.toNat * 24 := Nat.mul_le_mul_right 24 hpts_le
        omega
      have hne0 := ofNat_beq_zero_false_24 hlen_pos hlen_lt
      have hcap_ne : ptsCap ≠ 0#64 := by intro hc0; rw [hc0] at hpts_le; simp at hpts_le
      simp only [hcap_ne, ↓reduceIte]
      refine Drop.seq_clean (mid := entry + 10348#64)
        (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr (bs :: tl) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗
          (A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           memRegion (ptsPtr + BitVec.ofNat 64 ((bs :: tl).length * 24))
             ((ptsCap.toNat - (bs :: tl).length) * 24) ∗
           Frame))
        (Q := fun sm => v6hr_Saved10324Preserved s0 sm fsp out ptsPtr ptsCap x25_val ∧
          sm.readReg64 .x23 = BitVec.ofNat 64 (bs :: tl).length ∧
          sm.readReg64 .x20 = ptsPtr + 8#64)
        ?_ ?_
      · rcases hpres with ⟨hsp, hx19, hx21, hx28, hx25, htrace⟩
        wp_steps; refine Drop.align_pre (by ac_rfl) ?_; wp_done
      · intro s_loop hpc_loop hrun_loop ⟨hpres_loop, hx23_loop, hx20_loop⟩
        refine SepWP.strengthen_entails_const ?_
          (hloop (bs :: tl) ptsPtr s_loop _
            (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hpres_loop
            hx23_loop hx20_loop)
        have hsplit : ptsCap.toNat * 24 =
            (bs :: tl).length * 24 + (ptsCap.toNat - (bs :: tl).length) * 24 := by
          rw [← Nat.add_mul]; congr 1; omega
        have hbound : (bs :: tl).length * 24 + (ptsCap.toNat - (bs :: tl).length) * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; omega
        have hjoin : A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
            memRegion ptsPtr ((bs :: tl).length * 24) ∗
            memRegion (ptsPtr + BitVec.ofNat 64 ((bs :: tl).length * 24))
              ((ptsCap.toNat - (bs :: tl).length) * 24) ⊢
            A.live ptsPtr (ptsCap.toNat * 24) 8 ∗ memRegion ptsPtr (ptsCap.toNat * 24) := by
          rw [hsplit, ProofLib.memRegion_split ptsPtr ((bs :: tl).length * 24)
            ((ptsCap.toNat - (bs :: tl).length) * 24) hbound]
          exact Entails.of_eq (by ac_rfl)
        refine Entails.trans
          (Entails.of_eq (show _ =
            (A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
             memRegion ptsPtr ((bs :: tl).length * 24) ∗
             memRegion (ptsPtr + BitVec.ofNat 64 ((bs :: tl).length * 24))
               ((ptsCap.toNat - (bs :: tl).length) * 24)) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame by ac_rfl))
          (sepConj_mono_left hjoin)
  · intro s3 hpc3 hrun3 ⟨hsp_3, hx19_3, hx21_3, hx28_3, hx25_3, htrace_3⟩
    by_cases hc : ptsCap = 0#64
    · have hc_beq : (ptsCap == 0#64) = true := by rw [beq_iff_eq]; exact hc
      simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp] at hx28_3 ⊢
      wp_steps; wp_done
    · have hc_beq : ¬((ptsCap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
      have hlsl := cap_mul_24 hpts_cap_lt
      simp only [hc, ↓reduceIte]
      wp_steps
      wp_apply
      wp_done

theorem v6hr_states_from_pb_dealloc_none_proto_decoder_10316
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (fsp out ptsPtr x25_val : BitVec 64) (P : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10316#64)
    (hrun : s.status = .Running)
    (hpres : v6hr_Saved10324Preserved s0 s fsp out ptsPtr noneCap x25_val) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10396#64) s P
      (fun sm Pm =>
        (Pm ⊢ P) ∧
        v6hr_Saved10324Preserved s0 sm fsp out ptsPtr noneCap x25_val) := by
  states_from_pb_fetches_range b (Rust.withPanics ext) 10316 8
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  rcases hpres with ⟨hsp, hx19, hx21, hx28, hx25, htrace⟩
  change s.readReg64 .x28 = 0xffffffffffffffff#64 at hx28
  wp_steps
  wp_done

theorem v6hr_states_from_pb_dealloc_some_proto_decoder_10316
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s : State) (fsp out ptsPtr ptsCap x25_val : BitVec 64)
    (pts : List (List (BitVec 8))) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10316#64)
    (hrun : s.status = .Running)
    (hpres : v6hr_Saved10324Preserved s0 s fsp out ptsPtr ptsCap x25_val)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 pts.length) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10396#64) s
      ((if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v6hr_Saved10324Preserved s0 sm fsp out ptsPtr ptsCap x25_val) := by
  have h10324 := v6hr_states_from_pb_dealloc_proto_decoder_10324
    hA s0
  states_from_pb_fetches_range b (Rust.withPanics ext) 10316 8
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at h10324 hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  refine Drop.seq_clean (mid := entry + 10324#64)
    (P_mid := (if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => v6hr_Saved10324Preserved s0 sm fsp out ptsPtr ptsCap x25_val ∧
      sm.readReg64 .x23 = BitVec.ofNat 64 pts.length)
    ?_ ?_
  · rcases hpres with ⟨hsp, hx19, hx21, hx28, hx25, htrace⟩
    have hne : ¬((ptsCap + 1#64 == 0#64) = true) := cap_add_one_beq_zero_false (by omega)
    wp_steps
    wp_done
  · intro s1 hpc1 hrun1 ⟨hpres1, hx23_1⟩
    exact h10324 s1 fsp out ptsPtr ptsCap x25_val pts Frame
      hfsp_align hpts_le hpts_cap_lt hpc1 hrun1 hpres1 hx23_1

/-! ## 3. Header Load Step (`+1464 -> +1520` / `+3760`) -/

@[reducible]
def v6hr_Regs1508 (s0 s : State) (out : BitVec 64)
    (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 : BitVec 64) : Prop :=
  s.sp = s0.sp - 2400#64 ∧
  s.readReg64 .x8 = w80 ∧
  s.readReg64 .x9 = w16 ∧
  s.readReg64 .x10 = w24 ∧
  s.readReg64 .x11 = d112.zeroExtend 64 ∧
  s.readReg64 .x12 = d116.zeroExtend 64 ∧
  s.readReg64 .x13 = w120 ∧
  s.readReg64 .x14 = w64 ∧
  s.readReg64 .x19 = out ∧
  s.readReg64 .x20 = w8 ∧
  s.readReg64 .x21 = w56 ∧
  s.readReg64 .x22 = w48 ∧
  s.readReg64 .x23 = w104 ∧
  s.readReg64 .x24 = w32 ∧
  s.readReg64 .x25 = w72 ∧
  s.readReg64 .x26 = w40 ∧
  s.readReg64 .x28 = w88 ∧
  TraceCalleeSaved s s0

theorem v6hr_load_headers_1464_none_to_3760
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w96 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 v232 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1464#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3760#64) s1
      (((s0.sp - 2168#64) ↦₆₄ v232) ∗
        (pbA ↦₆₄ 0x8000000000000006#64) ∗
        v6hr_headersAt pbA w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 noneCap w96 w104 d112 d116 w120 ∗
        memRegion (pbA + 128#64) 96 ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          ((s0.sp - 2168#64) ↦₆₄ w96) ∗
          memRegion pbA optProtoInnerStateSize ∗
          Rest) ∧
        v6hr_Regs1508 s0 sm out w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 noneCap w104 d112 d116 w120) := by
  unfold v6hr_headersAt
  dsimp only [noneCap]
  simp only [sepConj_assoc]
  states_from_pb_fetches_range b (Rust.withPanics ext) 1464 48
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · have hpb := v6hr_headersAt_entails_dealloc pbA w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 noneCap w96 w104 d112 d116 w120
    unfold v6hr_headersAt at hpb
    dsimp only [noneCap] at hpb
    refine Entails.trans
      (Entails.of_eq (show _ =
        ((pbA ↦₆₄ 0x8000000000000006#64) ∗
         (((pbA + 8#64) ↦₆₄ w8) ∗ ((pbA + 16#64) ↦₆₄ w16) ∗
          ((pbA + 24#64) ↦₆₄ w24) ∗ ((pbA + 32#64) ↦₆₄ w32) ∗
          ((pbA + 40#64) ↦₆₄ w40) ∗ ((pbA + 48#64) ↦₆₄ w48) ∗
          ((pbA + 56#64) ↦₆₄ w56) ∗ ((pbA + 64#64) ↦₆₄ w64) ∗
          ((pbA + 72#64) ↦₆₄ w72) ∗ ((pbA + 80#64) ↦₆₄ w80) ∗
          ((pbA + 88#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((pbA + 96#64) ↦₆₄ w96) ∗
          ((pbA + 104#64) ↦₆₄ w104) ∗
          ((pbA + 112#64) ↦₃₂ d112) ∗ ((pbA + 116#64) ↦₃₂ d116) ∗
          ((pbA + 120#64) ↦₆₄ w120)) ∗
         memRegion (pbA + 128#64) 96) ∗
        (((s0.sp - 2168#64) ↦₆₄ w96) ∗ Rest) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hpb) (Entails.of_eq (by ac_rfl))
  · wp_done

theorem v6hr_load_headers_1464_some_eq_to_3760
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 : BitVec 64)
    (d116 : BitVec 32) (w120 v232 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hw88 : w88.toNat < 2 ^ 63)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1464#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3760#64) s1
      (((s0.sp - 2168#64) ↦₆₄ v232) ∗
        (pbA ↦₆₄ 0x8000000000000006#64) ∗
        v6hr_headersAt pbA w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 576#32 d116 w120 ∗
        memRegion (pbA + 128#64) 96 ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          ((s0.sp - 2168#64) ↦₆₄ w96) ∗
          memRegion pbA optProtoInnerStateSize ∗
          Rest) ∧
        v6hr_Regs1508 s0 sm out w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w104 576#32 d116 w120) := by
  have hne_w88 := cap_add_one_beq_zero_false hw88
  unfold v6hr_headersAt
  simp only [sepConj_assoc]
  states_from_pb_fetches_range b (Rust.withPanics ext) 1464 56
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · have hpb := v6hr_headersAt_entails_dealloc pbA w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 576#32 d116 w120
    unfold v6hr_headersAt at hpb
    refine Entails.trans
      (Entails.of_eq (show _ =
        ((pbA ↦₆₄ 0x8000000000000006#64) ∗
         (((pbA + 8#64) ↦₆₄ w8) ∗ ((pbA + 16#64) ↦₆₄ w16) ∗
          ((pbA + 24#64) ↦₆₄ w24) ∗ ((pbA + 32#64) ↦₆₄ w32) ∗
          ((pbA + 40#64) ↦₆₄ w40) ∗ ((pbA + 48#64) ↦₆₄ w48) ∗
          ((pbA + 56#64) ↦₆₄ w56) ∗ ((pbA + 64#64) ↦₆₄ w64) ∗
          ((pbA + 72#64) ↦₆₄ w72) ∗ ((pbA + 80#64) ↦₆₄ w80) ∗
          ((pbA + 88#64) ↦₆₄ w88) ∗ ((pbA + 96#64) ↦₆₄ w96) ∗
          ((pbA + 104#64) ↦₆₄ w104) ∗
          ((pbA + 112#64) ↦₃₂ 576#32) ∗ ((pbA + 116#64) ↦₃₂ d116) ∗
          ((pbA + 120#64) ↦₆₄ w120)) ∗
         memRegion (pbA + 128#64) 96) ∗
        (((s0.sp - 2168#64) ↦₆₄ w96) ∗ Rest) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hpb) (Entails.of_eq (by ac_rfl))
  · wp_done

theorem v6hr_load_headers_1464_some_ne_to_1520
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 v232 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hw88 : w88.toNat < 2 ^ 63)
    (hd112 : (d112 == 576#32) = false)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1464#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1520#64) s1
      (((s0.sp - 2168#64) ↦₆₄ v232) ∗
        (pbA ↦₆₄ 0x8000000000000006#64) ∗
        v6hr_headersAt pbA w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 d112 d116 w120 ∗
        memRegion (pbA + 128#64) 96 ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          ((s0.sp - 2168#64) ↦₆₄ w96) ∗
          memRegion pbA optProtoInnerStateSize ∗
          Rest) ∧
        v6hr_Regs1508 s0 sm out w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w104 d112 d116 w120) := by
  have hne_w88 := cap_add_one_beq_zero_false hw88
  have hd112_ne : ¬((d112 == 576#32) = true) := by rw [hd112]; decide
  unfold v6hr_headersAt
  simp only [sepConj_assoc]
  states_from_pb_fetches_range b (Rust.withPanics ext) 1464 56
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · have hpb := v6hr_headersAt_entails_dealloc pbA w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 d112 d116 w120
    unfold v6hr_headersAt at hpb
    refine Entails.trans
      (Entails.of_eq (show _ =
        ((pbA ↦₆₄ 0x8000000000000006#64) ∗
         (((pbA + 8#64) ↦₆₄ w8) ∗ ((pbA + 16#64) ↦₆₄ w16) ∗
          ((pbA + 24#64) ↦₆₄ w24) ∗ ((pbA + 32#64) ↦₆₄ w32) ∗
          ((pbA + 40#64) ↦₆₄ w40) ∗ ((pbA + 48#64) ↦₆₄ w48) ∗
          ((pbA + 56#64) ↦₆₄ w56) ∗ ((pbA + 64#64) ↦₆₄ w64) ∗
          ((pbA + 72#64) ↦₆₄ w72) ∗ ((pbA + 80#64) ↦₆₄ w80) ∗
          ((pbA + 88#64) ↦₆₄ w88) ∗ ((pbA + 96#64) ↦₆₄ w96) ∗
          ((pbA + 104#64) ↦₆₄ w104) ∗
          ((pbA + 112#64) ↦₃₂ d112) ∗ ((pbA + 116#64) ↦₃₂ d116) ∗
          ((pbA + 120#64) ↦₆₄ w120)) ∗
         memRegion (pbA + 128#64) 96) ∗
        (((s0.sp - 2168#64) ↦₆₄ w96) ∗ Rest) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hpb) (Entails.of_eq (by ac_rfl))
  · wp_done

end CryptoVerification.SpqrV1.States.FromPb
