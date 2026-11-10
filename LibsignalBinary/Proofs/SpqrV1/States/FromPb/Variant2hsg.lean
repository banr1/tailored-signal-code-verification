/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsb
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsc
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsb0
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 2 (`HeaderSent`, `+508`) — Part G

Error-branch exits and prefix composition (`+508 -> +9036`) reducing `InnerState.headerSent` to
the `sendingEk = some pbEnc` continuation.
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

set_option linter.style.longLine false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff libsignalSessionCode
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

attribute [local simp, local arm64_norm, local wp_norm]
  v1_bv_add_add_lit v1_bv_sub_sub_lit

/-! ## Unpack & Stack Split/Collapse Helpers (`v2hstop_*`) -/

theorem v2hstop_vecU8Heap_entails_dealloc (A : RustAlloc) (bs : List (BitVec 8))
    (cap ptr len : BitVec 64) :
    v4b_vecU8Heap A bs cap ptr len ⊢ vecCapPtrDealloc A cap ptr := by
  dsimp only [v4b_vecU8Heap]; apply Entails.pure_left; intro _
  exact vecU8Payload_entails_dealloc A cap ptr bs

theorem v2hstop_optProtoInnerStateAt_headerSent_unpack (A : RustAlloc) (pbA : BitVec 64)
    (s : V1State.Chunked.HeaderSent) :
    optProtoInnerStateAt A pbA (some (.headerSent s)) ⊢
      ∃∗ u8 : BitVec 64, ∃∗ u16 : BitVec 64, ∃∗ u24 : BitVec 64,
      ∃∗ u32 : BitVec 64, ∃∗ u40 : BitVec 64, ∃∗ u48 : BitVec 64,
      ∃∗ u56 : BitVec 64, ∃∗ u64 : BitVec 64, ∃∗ u72 : BitVec 64, ∃∗ u80 : BitVec 64,
      ∃∗ w0 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w16 : BitVec 64,
      ∃∗ w24 : BitVec 64, ∃∗ w32 : BitVec 64, ∃∗ w40 : BitVec 64, ∃∗ w48 : BitVec 64,
      ∃∗ d_w0 : BitVec 64, ∃∗ d_w8 : BitVec 64, ∃∗ d_w16 : BitVec 64,
      ∃∗ d_w24 : BitVec 64, ∃∗ d_w32 : BitVec 64,
        (pbA ↦₆₄ 0x8000000000000002#64) ∗
        v2hs_pb128At (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
          w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (pbA + 184#64) 40 ∗
        v2hs_optProtoUcHeap A s.uc u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        v1_optProtoPolyEncoderHeap A (s.sendingEk.map pbToProtoPolyEncoder)
          w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderHeap A (s.receivingCt1.map pbToProtoPolyDecoder)
          d_w0 d_w8 d_w16 d_w24 d_w32 := by
  dsimp only [optProtoInnerStateAt, protoInnerStateAt, protoChunkedHeaderSentAt]
  have hu := v2hs_optProtoUcAt_unpack A (pbA + 8#64) s.uc
  have he := v1_optProtoPolyEncoderAt_unpack A (pbA + 88#64) (s.sendingEk.map pbToProtoPolyEncoder)
  have hd := v2hs_optProtoDecoderAt_unpack A (pbA + 144#64) (s.receivingCt1.map pbToProtoPolyDecoder)
  have ha88 : (pbA + 8#64) + 80#64 = pbA + 88#64 := by bv_omega
  have ha144 : (pbA + 8#64) + 136#64 = pbA + 144#64 := by bv_omega
  rw [ha88, ha144]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left (sepConj_mono hu (sepConj_mono he hd)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro d_w0; apply Entails.sepExists_elim; intro d_w8
  apply Entails.sepExists_elim; intro d_w16; apply Entails.sepExists_elim; intro d_w24
  apply Entails.sepExists_elim; intro d_w32
  apply Entails.sepExists_elim; intro w0; apply Entails.sepExists_elim; intro w8
  apply Entails.sepExists_elim; intro w16; apply Entails.sepExists_elim; intro w24
  apply Entails.sepExists_elim; intro w32; apply Entails.sepExists_elim; intro w40
  apply Entails.sepExists_elim; intro w48
  apply Entails.sepExists_elim; intro u8; apply Entails.sepExists_elim; intro u16
  apply Entails.sepExists_elim; intro u24; apply Entails.sepExists_elim; intro u32
  apply Entails.sepExists_elim; intro u40; apply Entails.sepExists_elim; intro u48
  apply Entails.sepExists_elim; intro u56; apply Entails.sepExists_elim; intro u64
  apply Entails.sepExists_elim; intro u72; apply Entails.sepExists_elim; intro u80
  refine Entails.sepExists_right u8 (Entails.sepExists_right u16 (Entails.sepExists_right u24
    (Entails.sepExists_right u32 (Entails.sepExists_right u40 (Entails.sepExists_right u48
    (Entails.sepExists_right u56 (Entails.sepExists_right u64 (Entails.sepExists_right u72
    (Entails.sepExists_right u80 (Entails.sepExists_right w0 (Entails.sepExists_right w8
    (Entails.sepExists_right w16 (Entails.sepExists_right w24 (Entails.sepExists_right w32
    (Entails.sepExists_right w40 (Entails.sepExists_right w48 (Entails.sepExists_right d_w0
    (Entails.sepExists_right d_w8 (Entails.sepExists_right d_w16 (Entails.sepExists_right d_w24
    (Entails.sepExists_right d_w32 ?_)))))))))))))))))))))
  have h128 := v2hs_words_eq_pb128 (pbA + 8#64)
    u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32
  rw [ha88, ha144] at h128; rw [← h128]; exact Entails.of_eq (by ac_rfl)

theorem v2hstop_optProtoDecoderWordsAt_eq_v2hsc (a d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64) :
    v2hs_optProtoDecoderWordsAt a d_w0 d_w8 d_w16 d_w24 d_w32 =
      v2hsc_optProtoPolyDecoderWordsAt a d_w0 d_w8 d_w16
        (d_w24.extractLsb' 0 32) (d_w24.extractLsb' 32 32) d_w32 := by
  unfold v2hs_optProtoDecoderWordsAt v2hsc_optProtoPolyDecoderWordsAt
  have hpair := ProofLib.pointsTo32_pair (a + 24#64) (d_w24.extractLsb' 0 32) (d_w24.extractLsb' 32 32)
  have hcat : d_w24.extractLsb' 32 32 ++ d_w24.extractLsb' 0 32 = d_w24 := by bv_kernel
  have ha28 : (a + 24#64) + 4#64 = a + 28#64 := by bv_omega
  rw [hcat, ha28] at hpair; rw [← hpair]; ac_rfl

theorem v2hstop_optProtoDecoderHeap_eq_v2hsc (A : RustAlloc)
    (optDec : Option ProtoPolynomialDecoder) (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64) :
    v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 =
      v2hsc_optProtoPolyDecoderHeap A optDec d_w0 d_w8 d_w16
        (d_w24.extractLsb' 0 32) (d_w24.extractLsb' 32 32) d_w32 := by
  cases optDec <;> rfl

theorem v2hstop_optProtoDecoderHeap_none_extract (A : RustAlloc)
    (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64) :
    v2hs_optProtoDecoderHeap A none d_w0 d_w8 d_w16 d_w24 d_w32 ⊢
      ⌜d_w0 = noneCap⌝ ∗
      v2hs_optProtoDecoderHeap A none d_w0 d_w8 d_w16 d_w24 d_w32 := by
  dsimp only [v2hs_optProtoDecoderHeap, v4b_optProtoPolyDecoderHeap]
  conv_lhs => rw [← sepConj_emp (⌜d_w0 = noneCap⌝)]
  apply Entails.pure_left; intro hd_w0
  refine Entails.pure_right hd_w0 ?_
  rw [← sepConj_emp (⌜d_w0 = noneCap⌝)]
  exact Entails.pure_right hd_w0 (Entails.refl _)

theorem v2hstop_optProtoDecoderHeap_some_extract (A : RustAlloc) (d : PolynomialDecoder)
    (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64) :
    v2hs_optProtoDecoderHeap A (some (pbToProtoPolyDecoder d)) d_w0 d_w8 d_w16 d_w24 d_w32 ⊢
      ⌜d_w0.toNat * 24 < 2 ^ 63 ∧ d_w24.extractLsb' 0 32 = d.ptsNeeded⌝ ∗
      v2hs_optProtoDecoderHeap A (some (pbToProtoPolyDecoder d)) d_w0 d_w8 d_w16 d_w24 d_w32 := by
  dsimp only [v2hs_optProtoDecoderHeap, v4b_optProtoPolyDecoderHeap, pbToProtoPolyDecoder]
  apply Entails.pure_left; rintro ⟨hd16, hd24, hd28, hle, hcap, hptr, h32⟩
  exact Entails.pure_right ⟨hcap, hd24⟩
    (Entails.pure_right ⟨hd16, hd24, hd28, hle, hcap, hptr, h32⟩ (Entails.refl _))

theorem v2hstop_optProtoUcHeap_some_extract (A : RustAlloc) (u : V1State.Unchunked.EkSent)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 : BitVec 64) :
    v2hs_optProtoUcHeap A (some u) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ⊢
      ⌜u8.toNat < 2 ^ 63 ∧ u24 = BitVec.ofNat 64 u.dk.length ∧
        u.dk.length < 2 ^ 63 ∧ u80 = u.epoch⌝ ∗
      v4b_vecU8Heap A u.dk u8 u16 u24 ∗
      v1_optProtoAuthHeap A u.auth u32 u40 u48 u56 u64 u72 := by
  dsimp only [v2hs_optProtoUcHeap, v4b_vecU8Heap, vecU8Payload]
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜u24 = BitVec.ofNat 64 u.dk.length ∧ u8.toNat < 2 ^ 63⌝ ∗
    (⌜u.dk.length ≤ u8.toNat ∧ u8.toNat < 2 ^ 63 ∧ u16 ≠ 0#64⌝ ∗
     (⌜u80 = u.epoch⌝ ∗
      ((if u8 = 0#64 then emp
        else A.live u16 u8.toNat 1 ∗ (u16 ↦ₛ u.dk) ∗
          memRegion (u16 + BitVec.ofNat 64 u.dk.length) (u8.toNat - u.dk.length)) ∗
       v1_optProtoAuthHeap A u.auth u32 u40 u48 u56 u64 u72))) by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨hu24, hcap⟩
  apply Entails.pure_left; rintro ⟨hle, _, hptr⟩
  apply Entails.pure_left; intro hu80
  refine Entails.pure_right ⟨hcap, hu24, Nat.lt_of_le_of_lt hle hcap, hu80⟩ ?_
  rw [← sepConj_assoc]
  exact sepConj_mono_left (Entails.pure_right ⟨hu24, hcap⟩
    (Entails.pure_right ⟨hle, hcap, hptr⟩ (Entails.refl _)))

theorem v2hstop_optProtoAuthHeap_some_extract (A : RustAlloc) (auth : ProtoAuthenticator)
    (u32 u40 u48 u56 u64 u72 : BitVec 64) :
    v1_optProtoAuthHeap A (some auth) u32 u40 u48 u56 u64 u72 ⊢
      ⌜u32.toNat < 2 ^ 63 ∧ u48 = BitVec.ofNat 64 auth.rootKey.length ∧
        u72 = BitVec.ofNat 64 auth.macKey.length ∧ auth.rootKey.length < 2 ^ 63⌝ ∗
      vecU8Payload A u32 u40 auth.rootKey ∗
      vecU8Payload A u56 u64 auth.macKey := by
  dsimp only [v1_optProtoAuthHeap, vecU8Payload]
  simp only [sepConj_assoc]
  apply Entails.pure_left; rintro ⟨_, hu48, hu72⟩
  apply Entails.pure_left; rintro ⟨hr_le, hr_cap, hr_ptr⟩
  refine Entails.pure_right ⟨hr_cap, hu48, hu72, Nat.lt_of_le_of_lt hr_le hr_cap⟩ ?_
  exact Entails.pure_right
    (show auth.rootKey.length ≤ u32.toNat ∧ u32.toNat < 2 ^ 63 ∧ u40 ≠ 0#64 from
      ⟨hr_le, hr_cap, hr_ptr⟩) (Entails.refl _)

theorem v2hstop_collapse_976_from_err_uc
    (fsp w96 w152 w184 w216 w224 w232 : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 : BitVec 64) :
    ((fsp + 96#64) ↦₆₄ w96) ∗ ((fsp + 152#64) ↦₆₄ w152) ∗ memRegion (fsp + 176#64) 8 ∗
      ((fsp + 184#64) ↦₆₄ w184) ∗ memRegion (fsp + 200#64) 8 ∗ ((fsp + 216#64) ↦₆₄ w216) ∗
      ((fsp + 224#64) ↦₆₄ w224) ∗ ((fsp + 232#64) ↦₆₄ w232) ∗ memRegion (fsp + 240#64) 656 ∗
      v2hs_stack896ScratchRest fsp ∗
      v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ⊢
      memRegion fsp 976 := by
  have h184 := Drop.pointsTo64_entails_memRegion (fsp + 184#64) w184
  have h896 := v2hs_memRegion_896_unsplit_scratch fsp w96 w152 w216 w224 w232
  have h976 := v2hs_memRegion_896_ucWords_to_976 fsp u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h184)))) ?_
  refine Entails.trans (Entails.of_eq (show _ =
    (((fsp + 96#64) ↦₆₄ w96) ∗ ((fsp + 152#64) ↦₆₄ w152) ∗ memRegion (fsp + 176#64) 8 ∗
     memRegion (fsp + 184#64) 8 ∗ memRegion (fsp + 200#64) 8 ∗ ((fsp + 216#64) ↦₆₄ w216) ∗
     ((fsp + 224#64) ↦₆₄ w224) ∗ ((fsp + 232#64) ↦₆₄ w232) ∗ memRegion (fsp + 240#64) 656 ∗
     v2hs_stack896ScratchRest fsp) ∗
    v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 by ac_rfl)) ?_
  exact Entails.trans (sepConj_mono_left h896) h976

theorem v2hstop_ekSentWordsAt_entails_80 (a u48 pa1 u72 pa2 u8 u16 u24 u80 : BitVec 64) :
    v2hs_ekSentWordsAt a u48 pa1 u72 pa2 u8 u16 u24 u80 ⊢ memRegion a 80 := by
  unfold v2hs_ekSentWordsAt
  exact collapse_top <|
    collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    Drop.pointsTo64_entails_memRegion _ _

theorem v2hstop_collapse_2304_from_9228
    (fsp u8 u16 u24 u40 u48 u72 u80 pa1 pa2 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64) (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64) :
    ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
      ((fsp + 184#64) ↦₆₄ pa2) ∗ ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
      ((fsp + 224#64) ↦₆₄ u80) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗ memRegion (fsp + 240#64) 736 ∗
      v2hs_stack896ScratchRest fsp ∗
      v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
      v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
      memRegion (fsp + 1072#64) 192 ∗
      v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
      memRegion (fsp + 1344#64) 960 ⊢
      memRegion fsp 2304 := by
  dsimp only [v2hs_stack896ScratchRest]
  have h56 := v1_optProtoPolyEncoderWordsAt_entails_56 (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48
  have h40 := v2hs_optProtoDecoderWordsAt_entails_40 (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32
  have h80 := v2hstop_ekSentWordsAt_entails_80 (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80
  have hcol :
      memRegion fsp 96 ∗ ((fsp + 96#64) ↦₆₄ u24) ∗ memRegion (fsp + 104#64) 48 ∗
      ((fsp + 152#64) ↦₆₄ u8) ∗ memRegion (fsp + 160#64) 16 ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
      ((fsp + 184#64) ↦₆₄ pa2) ∗ memRegion (fsp + 192#64) 8 ∗ ((fsp + 200#64) ↦₆₄ u48) ∗
      memRegion (fsp + 208#64) 8 ∗ ((fsp + 216#64) ↦₆₄ u40) ∗ ((fsp + 224#64) ↦₆₄ u80) ∗
      ((fsp + 232#64) ↦₆₄ u72) ∗ memRegion (fsp + 240#64) 736 ∗
      memRegion (fsp + 976#64) 56 ∗ memRegion (fsp + 1032#64) 40 ∗
      memRegion (fsp + 1072#64) 192 ∗ memRegion (fsp + 1264#64) 80 ∗
      memRegion (fsp + 1344#64) 960 ⊢
      memRegion fsp 2304 :=
    collapse_top <|
      collapse_step0 (Entails.refl _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Entails.refl _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Entails.refl _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Entails.refl _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Entails.refl _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <| collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <| collapse_step (Entails.refl _) <| Entails.refl _
  refine Entails.trans (Entails.of_eq (show _ =
    v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
    v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
    (memRegion fsp 96 ∗ ((fsp + 96#64) ↦₆₄ u24) ∗ memRegion (fsp + 104#64) 48 ∗
     ((fsp + 152#64) ↦₆₄ u8) ∗ memRegion (fsp + 160#64) 16 ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
     ((fsp + 184#64) ↦₆₄ pa2) ∗ memRegion (fsp + 192#64) 8 ∗ ((fsp + 200#64) ↦₆₄ u48) ∗
     memRegion (fsp + 208#64) 8 ∗ ((fsp + 216#64) ↦₆₄ u40) ∗ ((fsp + 224#64) ↦₆₄ u80) ∗
     ((fsp + 232#64) ↦₆₄ u72) ∗ memRegion (fsp + 240#64) 736 ∗
     memRegion (fsp + 1072#64) 192 ∗ memRegion (fsp + 1344#64) 960) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono h56 (sepConj_mono h40 (sepConj_mono_left h80))) ?_
  exact Entails.trans (Entails.of_eq (by ac_rfl)) hcol

/-! ## Error Branch Helpers (`+9152 -> s0.x30`, `+3348 (bad dk) -> s0.x30`, `+3348 (auth none) -> s0.x30`) -/

theorem v2hstop_branch_sendingEk_none_9152
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (s0 s : State) (out : BitVec 64)
    (dk : List (BitVec 8)) (auth : ProtoAuthenticator)
    (u8 u16 u24 u40 u48 u72 u80 pa1 pa2 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64)
    (Rest : SepProp)
    (hu48 : u48 = BitVec.ofNat 64 auth.rootKey.length)
    (hu72 : u72 = BitVec.ofNat 64 auth.macKey.length)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9152#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx0 : s.readReg64 .x0 = pa2) (hx19 : s.readReg64 .x19 = out)
    (hx22 : s.readReg64 .x22 = d_w0) (hx25 : s.readReg64 .x25 = u48)
    (hx26 : s.readReg64 .x26 = u8) (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2400#64 + 96#64) ↦₆₄ u24) ∗ ((s0.sp - 2400#64 + 152#64) ↦₆₄ u8) ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗ ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ u48) ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u80) ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ u72) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 736 ∗ v2hs_stack896ScratchRest (s0.sp - 2400#64) ∗
        v4b_vecU8Heap A dk u8 u16 u24 ∗ vecU8Payload A u48 pa1 auth.rootKey ∗
        vecU8Payload A u72 pa2 auth.macKey ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (s0.sp - 2400#64 + 1072#64) 192 ∗
        v2hs_ekSentWordsAt (s0.sp - 2400#64 + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
        memRegion (s0.sp - 2400#64 + 1344#64) 960 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          A.pool ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  let fsp := s0.sp - 2400#64
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have hd_dk := v2hstop_vecU8Heap_entails_dealloc A dk u8 u16 u24
  have hd_r : vecU8Payload A u48 pa1 auth.rootKey ⊢ vecCapPtrDealloc A u48 pa1 := by
    rw [hu48]; exact vecU8Payload_entails_dealloc A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey
  have hd_m : vecU8Payload A u72 pa2 auth.macKey ⊢ vecCapPtrDealloc A u72 pa2 := by
    rw [hu72]; exact vecU8Payload_entails_dealloc A (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey
  have hek_split :
      v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 =
      ((fsp + 1272#64) ↦₆₄ pa1) ∗
      (((fsp + 1264#64) ↦₆₄ u48) ∗ ((fsp + 1280#64) ↦₆₄ u48) ∗ ((fsp + 1288#64) ↦₆₄ u72) ∗
       ((fsp + 1296#64) ↦₆₄ pa2) ∗ ((fsp + 1304#64) ↦₆₄ u72) ∗ ((fsp + 1312#64) ↦₆₄ u8) ∗
       ((fsp + 1320#64) ↦₆₄ u16) ∗ ((fsp + 1328#64) ↦₆₄ u24) ∗ ((fsp + 1336#64) ↦₆₄ u80)) := by
    dsimp only [v2hs_ekSentWordsAt, fsp]; simp only [arm64_norm]; ac_rfl
  let EkRest : SepProp :=
    ((fsp + 1264#64) ↦₆₄ u48) ∗ ((fsp + 1280#64) ↦₆₄ u48) ∗ ((fsp + 1288#64) ↦₆₄ u72) ∗
    ((fsp + 1296#64) ↦₆₄ pa2) ∗ ((fsp + 1304#64) ↦₆₄ u72) ∗ ((fsp + 1312#64) ↦₆₄ u8) ∗
    ((fsp + 1320#64) ↦₆₄ u16) ∗ ((fsp + 1328#64) ↦₆₄ u24) ∗ ((fsp + 1336#64) ↦₆₄ u80)
  let Frame9152 : SepProp :=
    ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 200#64) ↦₆₄ u48) ∗
    ((fsp + 216#64) ↦₆₄ u40) ∗ ((fsp + 224#64) ↦₆₄ u80) ∗ memRegion (fsp + 240#64) 736 ∗
    v2hs_stack896ScratchRest fsp ∗
    v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
    v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    memRegion (fsp + 1072#64) 192 ∗ EkRest ∗ memRegion (fsp + 1344#64) 960 ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest
  have hpre9152 :
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗ ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
        ((fsp + 224#64) ↦₆₄ u80) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗ memRegion (fsp + 240#64) 736 ∗
        v2hs_stack896ScratchRest fsp ∗ v4b_vecU8Heap A dk u8 u16 u24 ∗
        vecU8Payload A u48 pa1 auth.rootKey ∗ vecU8Payload A u72 pa2 auth.macKey ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (fsp + 1072#64) 192 ∗
        v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
        memRegion (fsp + 1344#64) 960 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest) ⊢
      stackAt fsp encoderFromPbStack ∗ ((fsp + 1272#64) ↦₆₄ pa1) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 232#64) ↦₆₄ u72) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
        vecCapPtrDealloc A u48 pa1 ∗ vecCapPtrDealloc A u72 pa2 ∗ vecCapPtrDealloc A u8 u16 ∗
        A.pool ∗ Frame9152 := by
    rw [hek_split]; dsimp only [Frame9152, EkRest]
    refine Entails.trans (Entails.of_eq (show _ =
      vecU8Payload A u48 pa1 auth.rootKey ∗ vecU8Payload A u72 pa2 auth.macKey ∗
      v4b_vecU8Heap A dk u8 u16 u24 ∗
      (stackAt fsp encoderFromPbStack ∗ ((fsp + 1272#64) ↦₆₄ pa1) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
       ((fsp + 232#64) ↦₆₄ u72) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗ A.pool ∗
       (((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 200#64) ↦₆₄ u48) ∗
        ((fsp + 216#64) ↦₆₄ u40) ∗ ((fsp + 224#64) ↦₆₄ u80) ∗ memRegion (fsp + 240#64) 736 ∗
        v2hs_stack896ScratchRest fsp ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (fsp + 1072#64) 192 ∗
        (((fsp + 1264#64) ↦₆₄ u48) ∗ ((fsp + 1280#64) ↦₆₄ u48) ∗ ((fsp + 1288#64) ↦₆₄ u72) ∗
         ((fsp + 1296#64) ↦₆₄ pa2) ∗ ((fsp + 1304#64) ↦₆₄ u72) ∗ ((fsp + 1312#64) ↦₆₄ u8) ∗
         ((fsp + 1320#64) ↦₆₄ u16) ∗ ((fsp + 1328#64) ↦₆₄ u24) ∗ ((fsp + 1336#64) ↦₆₄ u80)) ∗
        memRegion (fsp + 1344#64) 960 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest)) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono hd_r (sepConj_mono hd_m (sepConj_mono_left hd_dk)))
      (Entails.of_eq (by ac_rfl))
  refine SepWP.weaken_pre hpre9152 ?_
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9212#64)
    (P_mid := stackAt fsp encoderFromPbStack ∗ ((fsp + 1272#64) ↦₆₄ pa1) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
      ((fsp + 232#64) ↦₆₄ u72) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗ A.pool ∗ Frame9152)
    (Q := fun s1 => s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧
      s1.readReg64 .x22 = d_w0 ∧ TraceCalleeSaved s1 s0)
    (v2hsc_cleanup_9152_to_9212 hA s0 s fsp out d_w0 u48 pa1 u72 pa2 u8 u16 Frame9152
      hfsp_align hpc hrun hsp hx0 hx19 hx22 hx25 hx26 htr) ?_
  intro s1 hpc1 hrun1 ⟨hsp1, hx19_1, hx22_1, htr1⟩
  let Frame9212 : SepProp :=
    ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
    ((fsp + 184#64) ↦₆₄ pa2) ∗ ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
    ((fsp + 224#64) ↦₆₄ u80) ∗ memRegion (fsp + 240#64) 736 ∗ v2hs_stack896ScratchRest fsp ∗
    v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
    memRegion (fsp + 1072#64) 192 ∗
    v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
    memRegion (fsp + 1344#64) 960 ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest
  have hpre9212 :
      (stackAt fsp encoderFromPbStack ∗ ((fsp + 1272#64) ↦₆₄ pa1) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 232#64) ↦₆₄ u72) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗ A.pool ∗ Frame9152) =
      (stackAt fsp encoderFromPbStack ∗
        v2hsc_optProtoPolyDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16
          (d_w24.extractLsb' 0 32) (d_w24.extractLsb' 32 32) d_w32 ∗
        v2hsc_optProtoPolyDecoderHeap A optDec d_w0 d_w8 d_w16
          (d_w24.extractLsb' 0 32) (d_w24.extractLsb' 32 32) d_w32 ∗
        ((fsp + 232#64) ↦₆₄ u72) ∗ A.pool ∗ Frame9212) := by
    dsimp only [Frame9152, Frame9212, EkRest]
    rw [hek_split,
        v2hstop_optProtoDecoderWordsAt_eq_v2hsc (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32,
        v2hstop_optProtoDecoderHeap_eq_v2hsc A optDec d_w0 d_w8 d_w16 d_w24 d_w32]
    ac_rfl
  refine SepWP.weaken_pre (Entails.of_eq hpre9212) ?_
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9228#64)
    (P_mid := stackAt fsp encoderFromPbStack ∗
      v2hsc_optProtoPolyDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16
        (d_w24.extractLsb' 0 32) (d_w24.extractLsb' 32 32) d_w32 ∗
      ((fsp + 232#64) ↦₆₄ u72) ∗ A.pool ∗ Frame9212)
    (Q := fun s2 => s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧
      s2.readReg64 .x23 = 0#64 ∧ TraceCalleeSaved s2 s0)
    (v2hsc_cleanup_9212_to_9228 hA s0 s1 fsp out optDec d_w0 d_w8 d_w16
      (d_w24.extractLsb' 0 32) (d_w24.extractLsb' 32 32) d_w32 u72 Frame9212
      hfsp_align hpc1 hrun1 hsp1 hx19_1 hx22_1 htr1) ?_
  intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx23_2, htr2⟩
  have hcol2304 := v2hstop_collapse_2304_from_9228 fsp u8 u16 u24 u40 u48 u72 u80 pa1 pa2
    w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32
  have hpre9228 :
      (stackAt fsp encoderFromPbStack ∗
        v2hsc_optProtoPolyDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16
          (d_w24.extractLsb' 0 32) (d_w24.extractLsb' 32 32) d_w32 ∗
        ((fsp + 232#64) ↦₆₄ u72) ∗ A.pool ∗ Frame9212) ⊢
      stackAt fsp encoderFromPbStack ∗ memRegion fsp 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (A.pool ∗ Rest) := by
    rw [← v2hstop_optProtoDecoderWordsAt_eq_v2hsc (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32]
    dsimp only [Frame9212]
    refine Entails.trans (Entails.of_eq (show _ =
      (((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
       ((fsp + 184#64) ↦₆₄ pa2) ∗ ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
       ((fsp + 224#64) ↦₆₄ u80) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗ memRegion (fsp + 240#64) 736 ∗
       v2hs_stack896ScratchRest fsp ∗
       v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
       v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
       memRegion (fsp + 1072#64) 192 ∗
       v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
       memRegion (fsp + 1344#64) 960) ∗
      (stackAt fsp encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗ (A.pool ∗ Rest)) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hcol2304) (Entails.of_eq (by ac_rfl))
  refine SepWP.weaken_pre hpre9228 ?_
  have hx23_lo : (s2.readReg64 .x23).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
    rw [hx23_2]; rfl
  have h9228 := v2hs_err_cleanup_9228 (A := A) (F := F) s0 s2 out .stateDecode (A.pool ∗ Rest)
    hsp0_align hpc2 hrun2 hsp2 hx19_2 hx23_lo htr2
  exact SepWP.mono h9228 fun sf Pf _ _ ⟨hPf, hspf, hcsf, htrf⟩ =>
    ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hspf, hcsf, htrf⟩

theorem v2hstop_branch_bad_dk_3348
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (s0 s : State) (out : BitVec 64)
    (u : V1State.Unchunked.EkSent)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 : BitVec 64)
    (w96 w152 w176 w184 w200 w216 w224 w232 : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hu8 : u8.toNat < 2 ^ 63) (hdk : (u24 == 2400#64) = false)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3348#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out) (hx22 : s.readReg64 .x22 = d_w0)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2400#64 + 96#64) ↦₆₄ w96) ∗ ((s0.sp - 2400#64 + 152#64) ↦₆₄ w152) ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ w176) ∗ ((s0.sp - 2400#64 + 184#64) ↦₆₄ w184) ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ w200) ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ w216) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ w224) ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ w232) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 656 ∗ v2hs_stack896ScratchRest (s0.sp - 2400#64) ∗
        v2hs_ucWordsAt (s0.sp - 2400#64 + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        v4b_vecU8Heap A u.dk u8 u16 u24 ∗
        v1_optProtoAuthHeap A u.auth u32 u40 u48 u56 u64 u72 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          A.pool ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  let fsp := s0.sp - 2400#64
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have hd_dk := v2hstop_vecU8Heap_entails_dealloc A u.dk u8 u16 u24
  let Rest3348 : SepProp :=
    stackAt fsp encoderFromPbStack ∗ ((fsp + 176#64) ↦₆₄ w176) ∗ ((fsp + 184#64) ↦₆₄ w184) ∗
    ((fsp + 200#64) ↦₆₄ w200) ∗ ((fsp + 216#64) ↦₆₄ w216) ∗ ((fsp + 224#64) ↦₆₄ w224) ∗
    ((fsp + 232#64) ↦₆₄ w232) ∗ memRegion (fsp + 240#64) 656 ∗ v2hs_stack896ScratchRest fsp ∗
    vecCapPtrDealloc A u8 u16 ∗ v1_optProtoAuthHeap A u.auth u32 u40 u48 u56 u64 u72 ∗
    v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
    v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
    v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    memRegion (fsp + 1072#64) 1232 ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest
  have hpre3348 :
      (stackAt fsp encoderFromPbStack ∗ ((fsp + 96#64) ↦₆₄ w96) ∗ ((fsp + 152#64) ↦₆₄ w152) ∗
        ((fsp + 176#64) ↦₆₄ w176) ∗ ((fsp + 184#64) ↦₆₄ w184) ∗ ((fsp + 200#64) ↦₆₄ w200) ∗
        ((fsp + 216#64) ↦₆₄ w216) ∗ ((fsp + 224#64) ↦₆₄ w224) ∗ ((fsp + 232#64) ↦₆₄ w232) ∗
        memRegion (fsp + 240#64) 656 ∗ v2hs_stack896ScratchRest fsp ∗
        v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        v4b_vecU8Heap A u.dk u8 u16 u24 ∗
        v1_optProtoAuthHeap A u.auth u32 u40 u48 u56 u64 u72 ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (fsp + 1072#64) 1232 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest) ⊢
      ((fsp + 96#64) ↦₆₄ w96) ∗ ((fsp + 152#64) ↦₆₄ w152) ∗
        v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗ Rest3348 := by
    dsimp only [Rest3348]
    refine Entails.trans (Entails.of_eq (show _ =
      v4b_vecU8Heap A u.dk u8 u16 u24 ∗
      (((fsp + 96#64) ↦₆₄ w96) ∗ ((fsp + 152#64) ↦₆₄ w152) ∗
       v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
       stackAt fsp encoderFromPbStack ∗ ((fsp + 176#64) ↦₆₄ w176) ∗ ((fsp + 184#64) ↦₆₄ w184) ∗
       ((fsp + 200#64) ↦₆₄ w200) ∗ ((fsp + 216#64) ↦₆₄ w216) ∗ ((fsp + 224#64) ↦₆₄ w224) ∗
       ((fsp + 232#64) ↦₆₄ w232) ∗ memRegion (fsp + 240#64) 656 ∗ v2hs_stack896ScratchRest fsp ∗
       v1_optProtoAuthHeap A u.auth u32 u40 u48 u56 u64 u72 ∗
       v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
       v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
       v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
       v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
       memRegion (fsp + 1072#64) 1232 ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hd_dk) (Entails.of_eq (by ac_rfl))
  refine SepWP.weaken_pre hpre3348 ?_
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4660#64)
    (P_mid := ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
      v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗ Rest3348)
    (Q := fun s1 => s1.sp = fsp ∧ s1.readReg64 .x0 = u40 ∧ s1.readReg64 .x9 = u16 ∧
      s1.readReg64 .x19 = out ∧ s1.readReg64 .x22 = d_w0 ∧
      s1.readReg64 .x24 = u56 ∧ s1.readReg64 .x25 = u64 ∧
      s1.readReg64 .x26 = u32 ∧ TraceCalleeSaved s1 s0)
    (v2hs_validate_err_dk_3348_to_4660 s0 s out d_w0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
      w96 w152 Rest3348 hsp0_align hu8 hdk hpc hrun hsp hx19 hx22 htr) ?_
  intro s1 hpc1 hrun1 ⟨hsp1, hx0_1, hx9_1, hx19_1, hx22_1, hx24_1, hx25_1, hx26_1, htr1⟩
  let Frame4660 : SepProp :=
    memRegion (fsp - 5152#64) 1056 ∗ ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 184#64) ↦₆₄ w184) ∗
    ((fsp + 216#64) ↦₆₄ w216) ∗ ((fsp + 224#64) ↦₆₄ w224) ∗ ((fsp + 232#64) ↦₆₄ w232) ∗
    memRegion (fsp + 240#64) 656 ∗ v2hs_stack896ScratchRest fsp ∗
    v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
    v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
    v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
    v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    memRegion (fsp + 1072#64) 1232 ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest
  have hpre4660 :
      (((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
        v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗ Rest3348) =
      (((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ w176) ∗ ((fsp + 200#64) ↦₆₄ w200) ∗
        vecCapPtrDealloc A u8 u16 ∗ v1_optProtoAuthHeap A u.auth u32 u40 u48 u56 u64 u72 ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame4660) := by
    dsimp only [Rest3348, Frame4660]
    rw [stackAt_encoderFromPb_split_allocHook fsp]; ac_rfl
  refine SepWP.weaken_pre (Entails.of_eq hpre4660) ?_
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4396#64)
    (P_mid := ((fsp + 152#64) ↦₆₄ u8) ∗ memRegion (fsp + 176#64) 8 ∗ memRegion (fsp + 200#64) 8 ∗
      A.pool ∗ stackAt fsp allocHookStack ∗ Frame4660)
    (Q := fun s2 => s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧ s2.readReg64 .x22 = d_w0 ∧
      s2.readReg64 .x23 = (spqrErrorByte .stateDecode).zeroExtend 64 ∧ TraceCalleeSaved s2 s0)
    (v2hs_err_uc_4660_to_4396 hA s0 s1 fsp out u8 u16 u32 u40 u48 u56 u64 u72 w176 w200 d_w0
      u.auth Frame4660 hfsp_align hpc1 hrun1 hsp1 hx0_1 hx9_1 hx19_1 hx22_1 hx24_1 hx25_1 hx26_1 htr1) ?_
  intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx23_2, htr2⟩
  have hcol976 := v2hstop_collapse_976_from_err_uc fsp u24 u8 w184 w216 w224 w232
    u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
  have hpre4396 :
      (((fsp + 152#64) ↦₆₄ u8) ∗ memRegion (fsp + 176#64) 8 ∗ memRegion (fsp + 200#64) 8 ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame4660) ⊢
      stackAt fsp encoderFromPbStack ∗ memRegion fsp 976 ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (fsp + 1072#64) 1232 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest := by
    have hre :
        (((fsp + 152#64) ↦₆₄ u8) ∗ memRegion (fsp + 176#64) 8 ∗ memRegion (fsp + 200#64) 8 ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame4660) =
        (((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗ memRegion (fsp + 176#64) 8 ∗
         ((fsp + 184#64) ↦₆₄ w184) ∗ memRegion (fsp + 200#64) 8 ∗ ((fsp + 216#64) ↦₆₄ w216) ∗
         ((fsp + 224#64) ↦₆₄ w224) ∗ ((fsp + 232#64) ↦₆₄ w232) ∗ memRegion (fsp + 240#64) 656 ∗
         v2hs_stack896ScratchRest fsp ∗
         v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80) ∗
        ((memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack) ∗
         v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
         v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
         v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
         v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
         memRegion (fsp + 1072#64) 1232 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest) := by
      dsimp only [Frame4660]; ac_rfl
    rw [← stackAt_encoderFromPb_split_allocHook fsp] at hre
    exact Entails.trans (Entails.of_eq hre)
      (Entails.trans (sepConj_mono_left hcol976) (Entails.of_eq (by ac_rfl)))
  refine SepWP.weaken_pre hpre4396 ?_
  exact v2hs_epilogue_4396_ret (A := A) (F := F) hA s0 s2 out .stateDecode
    optEnc w0 w8 w16 w24 w32 w40 w48 optDec d_w0 d_w8 d_w16 d_w24 d_w32 Rest
    hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx23_2 htr2

theorem v2hstop_branch_auth_none_3348
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (s0 s : State) (out : BitVec 64)
    (dk : List (BitVec 8))
    (u8 u16 u24 u40 u48 u56 u64 u72 u80 : BitVec 64)
    (w96 w152 w176 w184 w200 w216 w224 w232 : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hu8 : u8.toNat < 2 ^ 63) (hdk : (u24 == 2400#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3348#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out) (hx22 : s.readReg64 .x22 = d_w0)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2400#64 + 96#64) ↦₆₄ w96) ∗ ((s0.sp - 2400#64 + 152#64) ↦₆₄ w152) ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ w176) ∗ ((s0.sp - 2400#64 + 184#64) ↦₆₄ w184) ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ w200) ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ w216) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ w224) ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ w232) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 656 ∗ v2hs_stack896ScratchRest (s0.sp - 2400#64) ∗
        v2hs_ucWordsAt (s0.sp - 2400#64 + 896#64) u8 u16 u24 noneCap u40 u48 u56 u64 u72 u80 ∗
        v4b_vecU8Heap A dk u8 u16 u24 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          A.pool ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  let fsp := s0.sp - 2400#64
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have hd_dk := v2hstop_vecU8Heap_entails_dealloc A dk u8 u16 u24
  let Rest3348 : SepProp :=
    stackAt fsp encoderFromPbStack ∗ ((fsp + 176#64) ↦₆₄ w176) ∗ ((fsp + 184#64) ↦₆₄ w184) ∗
    ((fsp + 200#64) ↦₆₄ w200) ∗ ((fsp + 216#64) ↦₆₄ w216) ∗ ((fsp + 224#64) ↦₆₄ w224) ∗
    ((fsp + 232#64) ↦₆₄ w232) ∗ memRegion (fsp + 240#64) 656 ∗ v2hs_stack896ScratchRest fsp ∗
    vecCapPtrDealloc A u8 u16 ∗
    v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
    v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
    v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    memRegion (fsp + 1072#64) 1232 ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest
  have hpre3348 :
      (stackAt fsp encoderFromPbStack ∗ ((fsp + 96#64) ↦₆₄ w96) ∗ ((fsp + 152#64) ↦₆₄ w152) ∗
        ((fsp + 176#64) ↦₆₄ w176) ∗ ((fsp + 184#64) ↦₆₄ w184) ∗ ((fsp + 200#64) ↦₆₄ w200) ∗
        ((fsp + 216#64) ↦₆₄ w216) ∗ ((fsp + 224#64) ↦₆₄ w224) ∗ ((fsp + 232#64) ↦₆₄ w232) ∗
        memRegion (fsp + 240#64) 656 ∗ v2hs_stack896ScratchRest fsp ∗
        v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 noneCap u40 u48 u56 u64 u72 u80 ∗
        v4b_vecU8Heap A dk u8 u16 u24 ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (fsp + 1072#64) 1232 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest) ⊢
      ((fsp + 96#64) ↦₆₄ w96) ∗ ((fsp + 152#64) ↦₆₄ w152) ∗
        v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 noneCap u40 u48 u56 u64 u72 u80 ∗ Rest3348 := by
    dsimp only [Rest3348]
    refine Entails.trans (Entails.of_eq (show _ =
      v4b_vecU8Heap A dk u8 u16 u24 ∗
      (((fsp + 96#64) ↦₆₄ w96) ∗ ((fsp + 152#64) ↦₆₄ w152) ∗
       v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 noneCap u40 u48 u56 u64 u72 u80 ∗
       stackAt fsp encoderFromPbStack ∗ ((fsp + 176#64) ↦₆₄ w176) ∗ ((fsp + 184#64) ↦₆₄ w184) ∗
       ((fsp + 200#64) ↦₆₄ w200) ∗ ((fsp + 216#64) ↦₆₄ w216) ∗ ((fsp + 224#64) ↦₆₄ w224) ∗
       ((fsp + 232#64) ↦₆₄ w232) ∗ memRegion (fsp + 240#64) 656 ∗ v2hs_stack896ScratchRest fsp ∗
       v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
       v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
       v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
       v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
       memRegion (fsp + 1072#64) 1232 ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hd_dk) (Entails.of_eq (by ac_rfl))
  refine SepWP.weaken_pre hpre3348 ?_
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4720#64)
    (P_mid := ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
      v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 noneCap u40 u48 u56 u64 u72 u80 ∗ Rest3348)
    (Q := fun s1 => s1.sp = fsp ∧ s1.readReg64 .x9 = u16 ∧
      s1.readReg64 .x19 = out ∧ s1.readReg64 .x22 = d_w0 ∧ TraceCalleeSaved s1 s0)
    (v2hs_validate_err_auth_3348_to_4720 s0 s out d_w0 u8 u16 u24 u40 u48 u56 u64 u72 u80
      w96 w152 Rest3348 hsp0_align hu8 hdk hpc hrun hsp hx19 hx22 htr) ?_
  intro s1 hpc1 hrun1 ⟨hsp1, hx9_1, hx19_1, hx22_1, htr1⟩
  let Frame4720 : SepProp :=
    memRegion (fsp - 5152#64) 1056 ∗ ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 184#64) ↦₆₄ w184) ∗
    ((fsp + 216#64) ↦₆₄ w216) ∗ ((fsp + 224#64) ↦₆₄ w224) ∗ ((fsp + 232#64) ↦₆₄ w232) ∗
    memRegion (fsp + 240#64) 656 ∗ v2hs_stack896ScratchRest fsp ∗
    v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 noneCap u40 u48 u56 u64 u72 u80 ∗
    v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
    v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
    v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    memRegion (fsp + 1072#64) 1232 ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest
  have hpre4720 :
      (((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
        v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 noneCap u40 u48 u56 u64 u72 u80 ∗ Rest3348) =
      (((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ w176) ∗ ((fsp + 200#64) ↦₆₄ w200) ∗
        vecCapPtrDealloc A u8 u16 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame4720) := by
    dsimp only [Rest3348, Frame4720]
    rw [stackAt_encoderFromPb_split_allocHook fsp]; ac_rfl
  refine SepWP.weaken_pre (Entails.of_eq hpre4720) ?_
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4396#64)
    (P_mid := ((fsp + 152#64) ↦₆₄ u8) ∗ memRegion (fsp + 176#64) 8 ∗ memRegion (fsp + 200#64) 8 ∗
      A.pool ∗ stackAt fsp allocHookStack ∗ Frame4720)
    (Q := fun s2 => s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧ s2.readReg64 .x22 = d_w0 ∧
      s2.readReg64 .x23 = (spqrErrorByte .stateDecode).zeroExtend 64 ∧ TraceCalleeSaved s2 s0)
    (v2hs_err_uc_4720_to_4396 hA s0 s1 fsp out u8 u16 w176 w200 d_w0
      Frame4720 hfsp_align hpc1 hrun1 hsp1 hx9_1 hx19_1 hx22_1 htr1) ?_
  intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx23_2, htr2⟩
  have hcol976 := v2hstop_collapse_976_from_err_uc fsp u24 u8 w184 w216 w224 w232
    u8 u16 u24 noneCap u40 u48 u56 u64 u72 u80
  have hpre4396 :
      (((fsp + 152#64) ↦₆₄ u8) ∗ memRegion (fsp + 176#64) 8 ∗ memRegion (fsp + 200#64) 8 ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame4720) ⊢
      stackAt fsp encoderFromPbStack ∗ memRegion fsp 976 ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (fsp + 1072#64) 1232 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest := by
    have hre :
        (((fsp + 152#64) ↦₆₄ u8) ∗ memRegion (fsp + 176#64) 8 ∗ memRegion (fsp + 200#64) 8 ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame4720) =
        (((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗ memRegion (fsp + 176#64) 8 ∗
         ((fsp + 184#64) ↦₆₄ w184) ∗ memRegion (fsp + 200#64) 8 ∗ ((fsp + 216#64) ↦₆₄ w216) ∗
         ((fsp + 224#64) ↦₆₄ w224) ∗ ((fsp + 232#64) ↦₆₄ w232) ∗ memRegion (fsp + 240#64) 656 ∗
         v2hs_stack896ScratchRest fsp ∗
         v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 noneCap u40 u48 u56 u64 u72 u80) ∗
        ((memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack) ∗
         v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
         v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
         v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
         v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
         memRegion (fsp + 1072#64) 1232 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest) := by
      dsimp only [Frame4720]; ac_rfl
    rw [← stackAt_encoderFromPb_split_allocHook fsp] at hre
    exact Entails.trans (Entails.of_eq hre)
      (Entails.trans (sepConj_mono_left hcol976) (Entails.of_eq (by ac_rfl)))
  refine SepWP.weaken_pre hpre4396 ?_
  exact v2hs_epilogue_4396_ret (A := A) (F := F) hA s0 s2 out .stateDecode
    optEnc w0 w8 w16 w24 w32 w40 w48 optDec d_w0 d_w8 d_w16 d_w24 d_w32 Rest
    hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx23_2 htr2

/-! ## `+9036` (`sendingEk = some pbEnc`) Continuation Interface & `+3436 / +3348 / +508 -> s0.x30` -/

/-- Partially collapsed 224-byte `pbA` region keeping `pbA + 96..144` (`w8..w48` of `sendingEk`) exposed for `+9036`. -/
def v2hstop_pbEncTailAt (pbA w8 w16 w24 w32 w40 w48 : BitVec 64) : SepProp :=
  memRegion pbA 96 ∗
  ((pbA + 96#64) ↦₆₄ w8) ∗ ((pbA + 104#64) ↦₆₄ w16) ∗ ((pbA + 112#64) ↦₆₄ w24) ∗
  ((pbA + 120#64) ↦₆₄ w32) ∗ ((pbA + 128#64) ↦₆₄ w40) ∗ ((pbA + 136#64) ↦₆₄ w48) ∗
  memRegion (pbA + 144#64) 80

theorem v2hstop_pb128_entails_pbEncTailAt
    (pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
     w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64) :
    (pbA ↦₆₄ 0x8000000000000002#64) ∗
      v2hs_pb128At (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
        w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32 ∗
      memRegion (pbA + 184#64) 40 ⊢
      v2hstop_pbEncTailAt pbA w8 w16 w24 w32 w40 w48 := by
  rw [← v2hs_words_eq_pb128]
  dsimp only [v1_optProtoPolyEncoderWordsAt, v2hstop_pbEncTailAt]
  have h80 := v2hs_ucWordsAt_entails_80 (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
  have h40 := v2hs_optProtoDecoderWordsAt_entails_40 (pbA + 144#64) d_w0 d_w8 d_w16 d_w24 d_w32
  have h96 : (pbA ↦₆₄ 0x8000000000000002#64) ∗ memRegion (pbA + 8#64) 80 ∗ ((pbA + 88#64) ↦₆₄ w0) ⊢
      memRegion pbA 96 :=
    collapse_top <| collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Entails.refl _) <| Drop.pointsTo64_entails_memRegion _ _
  have h80_tail : memRegion (pbA + 144#64) 40 ∗ memRegion (pbA + 184#64) 40 ⊢
      memRegion (pbA + 144#64) 80 :=
    collapse_step (Entails.refl _) (Entails.refl _)
  simp only [arm64_norm] at h40 ⊢
  refine Entails.trans (Entails.of_eq (show _ =
    ((pbA ↦₆₄ 0x8000000000000002#64) ∗
     v2hs_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
     ((pbA + 88#64) ↦₆₄ w0)) ∗
    ((pbA + 96#64) ↦₆₄ w8) ∗ ((pbA + 104#64) ↦₆₄ w16) ∗ ((pbA + 112#64) ↦₆₄ w24) ∗
    ((pbA + 120#64) ↦₆₄ w32) ∗ ((pbA + 128#64) ↦₆₄ w40) ∗ ((pbA + 136#64) ↦₆₄ w48) ∗
    (v2hs_optProtoDecoderWordsAt (pbA + 144#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
     memRegion (pbA + 184#64) 40) by ac_rfl)) ?_
  exact sepConj_mono (Entails.trans (sepConj_mono_right (sepConj_mono_left h80)) h96)
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right
        (Entails.trans (sepConj_mono_left h40) h80_tail)))))))

theorem v2hstop_pbEncTailAt_entails_full_224 (pbA w8 w16 w24 w32 w40 w48 : BitVec 64) :
    v2hstop_pbEncTailAt pbA w8 w16 w24 w32 w40 w48 ⊢ memRegion pbA optProtoInnerStateSize := by
  unfold v2hstop_pbEncTailAt
  exact collapse_top <| collapse_step0 (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    Entails.refl _

theorem v2hstop_pbEncTailAt_eq_128 (pbA w8 w16 w24 w32 w40 w48 : BitVec 64) :
    v2hstop_pbEncTailAt pbA w8 w16 w24 w32 w40 w48 =
      memRegion pbA 96 ∗
      ((pbA + 96#64) ↦₁₂₈ (w16 ++ w8)) ∗
      ((pbA + 112#64) ↦₁₂₈ (w32 ++ w24)) ∗
      ((pbA + 128#64) ↦₁₂₈ (w48 ++ w40)) ∗
      memRegion (pbA + 144#64) 80 := by
  unfold v2hstop_pbEncTailAt
  simp only [← EncoderFromPb.pointsTo64_pair_eq_pointsTo128, arm64_norm, sepConj_assoc]

/-- Interface hypothesis for the `+9036 -> s0.x30` (`sendingEk = some pbEnc`) continuation of Variant 2 (`HeaderSent`). -/
def v2hstop_SomeEnc9036Hyp
    (A : RustAlloc) (F : ShaCompress) (b : BitVec 64)
    (ext : String → Option (State → State)) (s : V1State.Chunked.HeaderSent) : Prop :=
  ∀ (s0 sm : State) (out pbA : BitVec 64) (R : SepProp)
    (u : V1State.Unchunked.EkSent) (auth : ProtoAuthenticator) (pbEnc : PolynomialEncoder)
    (u8 u16 u24 u40 u48 u72 u80 pa1 pa2 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64) (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64),
    optEncoderPtsBound s.sendingEk →
    (match s.receivingCt1 with | none => True | some d => (d.ptsNeeded == 480#32) = true) →
    s.uc = some u → u.dk.length = 2400 → u.auth = some auth → s.sendingEk = some pbEnc →
    u8.toNat < 2 ^ 63 → u24 = 2400#64 → u48 = BitVec.ofNat 64 auth.rootKey.length →
    u72 = BitVec.ofNat 64 auth.macKey.length → u80 = u.epoch → auth.rootKey.length < 2 ^ 63 →
    (s0.sp &&& 15#64 == 0#64) = true →
    sm.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9036#64 →
    sm.status = .Running → sm.sp = s0.sp - 2400#64 →
    sm.readReg64 .x0 = pa2 → sm.readReg64 .x8 = w0 → sm.readReg64 .x9 = u24 →
    sm.readReg64 .x10 = (s0.sp - 2400#64) + 1264#64 → sm.readReg64 .x19 = out →
    sm.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64 →
    sm.readReg64 .x22 = d_w0 → sm.readReg64 .x23 = pa1 → sm.readReg64 .x25 = u48 →
    sm.readReg64 .x26 = u8 → sm.readReg64 .x27 = pbA → sm.readReg64 .x28 = u80 →
    TraceCalleeSaved sm s0 →
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sm
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2400#64 + 96#64) ↦₆₄ u24) ∗ ((s0.sp - 2400#64 + 152#64) ↦₆₄ u8) ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗ ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ u48) ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u80) ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ u72) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 736 ∗ v2hs_stack896ScratchRest (s0.sp - 2400#64) ∗
        v4b_vecU8Heap A u.dk u8 u16 u24 ∗ vecU8Payload A u48 pa1 auth.rootKey ∗
        vecU8Payload A u72 pa2 auth.macKey ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (s0.sp - 2400#64 + 1072#64) 192 ∗
        v2hs_ekSentWordsAt (s0.sp - 2400#64 + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
        memRegion (s0.sp - 2400#64 + 1344#64) 960 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        v2hstop_pbEncTailAt pbA w8 w16 w24 w32 w40 w48 ∗ statesFromPbJumpTableAt b ∗ A.pool)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.headerSent s) }) ∗
          memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool ∗
          stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R))

end CryptoVerification.SpqrV1.States.FromPb
