/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.EpilogueExt
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2a
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aExt
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 1 (`KeysSampled`, `+1104`) — Part B

**Checked by Lean.**

Header unpacking, stack copy (`+1104..+1192`), validation (`+1196..+1292`), and `auth.rootKey`
cloning (`+1292 -> +8756`) for `InnerState.keysSampled`.
-/

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  statesFromPb_fnOff
  stubOff_rust_no_alloc_shim
  stubOff_rust_alloc
  stubOff_rust_dealloc
  stubOff_memcpy
  stubOff_handle_error

@[local simp, local arm64_norm, local wp_norm]
theorem v1_bv_add_add_lit' (x : BitVec 64) (a b : Nat) :
    x + BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v1_bv_sub_sub_lit' (x : BitVec 64) (a b : Nat) :
    x - BitVec.ofNat 64 a - BitVec.ofNat 64 b = x - BitVec.ofNat 64 (a + b) := by
  bv_omega

/-! ## Unpacking `optProtoUnchunkedHeaderSentAt` into `v1_ucWordsAt` -/

/-- Heap and pure constraints of `Option<V1State.Unchunked.HeaderSent>` associated with words `u8..u104`. -/
def v1_optProtoUcHeap (A : RustAlloc) :
    Option V1State.Unchunked.HeaderSent →
    BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 →
    BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 →
    BitVec 64 → SepProp
  | none, u8, _, _, _, _, _, _, _, _, _, _, _, _ => ⌜u8 = noneCap⌝
  | some uc, u8, u16, u24, u32, u40, u48, u56, u64, u72, u80, u88, u96, u104 =>
    ⌜u8.toNat < 2 ^ 63 ∧ u24 = BitVec.ofNat 64 uc.ek.length ∧
      u32.toNat < 2 ^ 63 ∧ u48 = BitVec.ofNat 64 uc.dk.length ∧
      u104 = uc.epoch⌝ ∗
    vecU8Payload A u8 u16 uc.ek ∗
    vecU8Payload A u32 u40 uc.dk ∗
    v1_optProtoAuthHeap A uc.auth u56 u64 u72 u80 u88 u96

theorem v1_vecU8_unpack (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A a bs ⊢
      ∃∗ c : BitVec 64, ∃∗ p : BitVec 64, ∃∗ l : BitVec 64,
        ⌜c.toNat < 2 ^ 63 ∧ l = BitVec.ofNat 64 bs.length⌝ ∗
        (a ↦₆₄ c) ∗ ((a + 8#64) ↦₆₄ p) ∗ ((a + 16#64) ↦₆₄ l) ∗
        vecU8Payload A c p bs := by
  unfold vecU8 vecU8At vecHeader
  apply Entails.sepExists_elim; intro c
  apply Entails.sepExists_elim; intro p
  unfold vecU8Payload
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜bs.length ≤ c.toNat ∧ c.toNat < 2 ^ 63 ∧ p ≠ 0#64⌝ ∗
    ((a ↦₆₄ c) ∗ ((a + 8#64) ↦₆₄ p) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
     if c = 0#64 then emp
     else A.live p c.toNat 1 ∗ (p ↦ₛ bs) ∗
       memRegion (p + BitVec.ofNat 64 bs.length) (c.toNat - bs.length)) by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨hle, hc_lt, hp_ne⟩
  refine Entails.sepExists_right c (Entails.sepExists_right p
    (Entails.sepExists_right (BitVec.ofNat 64 bs.length) ?_))
  refine Entails.pure_right ⟨hc_lt, rfl⟩ ?_
  have hpure : bs.length ≤ c.toNat ∧ c.toNat < 2 ^ 63 ∧ p ≠ 0#64 := ⟨hle, hc_lt, hp_ne⟩
  exact Entails.trans (Entails.pure_right hpure (Entails.refl _)) (Entails.of_eq (by ac_rfl))

theorem v1_optProtoAuthAt_unpack (A : RustAlloc) (a : BitVec 64)
    (optAuth : Option ProtoAuthenticator) :
    optProtoAuthenticatorAt A a optAuth ⊢
      ∃∗ u56 : BitVec 64, ∃∗ u64 : BitVec 64, ∃∗ u72 : BitVec 64,
      ∃∗ u80 : BitVec 64, ∃∗ u88 : BitVec 64, ∃∗ u96 : BitVec 64,
        ((a ↦₆₄ u56) ∗ ((a + 8#64) ↦₆₄ u64) ∗ ((a + 16#64) ↦₆₄ u72) ∗
         ((a + 24#64) ↦₆₄ u80) ∗ ((a + 32#64) ↦₆₄ u88) ∗ ((a + 40#64) ↦₆₄ u96)) ∗
        v1_optProtoAuthHeap A optAuth u56 u64 u72 u80 u88 u96 := by
  cases optAuth with
  | none =>
    unfold optProtoAuthenticatorAt v1_optProtoAuthHeap
    have hsplit : memRegion (a + 8#64) 40 ⊢
        (∃∗ u64 : BitVec 64, (a + 8#64) ↦₆₄ u64) ∗
        (∃∗ u72 : BitVec 64, (a + 16#64) ↦₆₄ u72) ∗
        (∃∗ u80 : BitVec 64, (a + 24#64) ↦₆₄ u80) ∗
        (∃∗ u88 : BitVec 64, (a + 32#64) ↦₆₄ u88) ∗
        (∃∗ u96 : BitVec 64, (a + 40#64) ↦₆₄ u96) := by
      exact split_top <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        mem64_entails _
    refine Entails.trans (sepConj_mono_right hsplit) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro u96
    apply Entails.sepExists_elim; intro u88
    apply Entails.sepExists_elim; intro u80
    apply Entails.sepExists_elim; intro u72
    apply Entails.sepExists_elim; intro u64
    refine Entails.sepExists_right noneCap (Entails.sepExists_right u64
      (Entails.sepExists_right u72 (Entails.sepExists_right u80
        (Entails.sepExists_right u88 (Entails.sepExists_right u96 ?_)))))
    exact Entails.trans (Entails.pure_right (rfl : noneCap = noneCap) (Entails.refl _))
      (Entails.of_eq (by ac_rfl))
  | some auth =>
    unfold optProtoAuthenticatorAt protoAuthenticatorAt v1_optProtoAuthHeap
    refine Entails.trans (sepConj_mono (v1_vecU8_unpack A a auth.rootKey)
      (v1_vecU8_unpack A (a + 24#64) auth.macKey)) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro u80
    apply Entails.sepExists_elim; intro u88
    apply Entails.sepExists_elim; intro u96
    apply Entails.sepExists_elim; intro u56
    apply Entails.sepExists_elim; intro u64
    apply Entails.sepExists_elim; intro u72
    have ha32 : a + 24#64 + 8#64 = a + 32#64 := by bv_omega
    have ha40 : a + 24#64 + 16#64 = a + 40#64 := by bv_omega
    rw [ha32, ha40]
    refine Entails.trans (Entails.of_eq (show _ =
      ⌜u56.toNat < 2 ^ 63 ∧ u72 = BitVec.ofNat 64 auth.rootKey.length⌝ ∗
      ⌜u80.toNat < 2 ^ 63 ∧ u96 = BitVec.ofNat 64 auth.macKey.length⌝ ∗
      ((a ↦₆₄ u56) ∗ ((a + 8#64) ↦₆₄ u64) ∗ ((a + 16#64) ↦₆₄ u72) ∗
       ((a + 24#64) ↦₆₄ u80) ∗ ((a + 32#64) ↦₆₄ u88) ∗ ((a + 40#64) ↦₆₄ u96) ∗
       vecU8Payload A u56 u64 auth.rootKey ∗
       vecU8Payload A u80 u88 auth.macKey) by ac_rfl)) ?_
    apply Entails.pure_left; rintro ⟨hu56, hu72⟩
    apply Entails.pure_left; rintro ⟨_, hu96⟩
    refine Entails.sepExists_right u56 (Entails.sepExists_right u64
      (Entails.sepExists_right u72 (Entails.sepExists_right u80
        (Entails.sepExists_right u88 (Entails.sepExists_right u96 ?_)))))
    have hpure : u56.toNat < 2 ^ 63 ∧ u72 = BitVec.ofNat 64 auth.rootKey.length ∧
        u96 = BitVec.ofNat 64 auth.macKey.length := ⟨hu56, hu72, hu96⟩
    exact Entails.trans (Entails.pure_right hpure (Entails.refl _)) (Entails.of_eq (by ac_rfl))

theorem v1_optProtoUnchunkedHeaderSentAt_unpack (A : RustAlloc) (a : BitVec 64)
    (optUc : Option V1State.Unchunked.HeaderSent) :
    optProtoUnchunkedHeaderSentAt A a optUc ⊢
      ∃∗ u8 : BitVec 64, ∃∗ u16 : BitVec 64, ∃∗ u24 : BitVec 64,
      ∃∗ u32 : BitVec 64, ∃∗ u40 : BitVec 64, ∃∗ u48 : BitVec 64,
      ∃∗ u56 : BitVec 64, ∃∗ u64 : BitVec 64, ∃∗ u72 : BitVec 64,
      ∃∗ u80 : BitVec 64, ∃∗ u88 : BitVec 64, ∃∗ u96 : BitVec 64,
      ∃∗ u104 : BitVec 64,
        v1_ucWordsAt a u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
        v1_optProtoUcHeap A optUc u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 := by
  cases optUc with
  | none =>
    unfold optProtoUnchunkedHeaderSentAt v1_optProtoUcHeap
    have hsplit : memRegion (a + 8#64) 96 ⊢
        (∃∗ u16 : BitVec 64, (a + 8#64) ↦₆₄ u16) ∗
        (∃∗ u24 : BitVec 64, (a + 16#64) ↦₆₄ u24) ∗
        (∃∗ u32 : BitVec 64, (a + 24#64) ↦₆₄ u32) ∗
        (∃∗ u40 : BitVec 64, (a + 32#64) ↦₆₄ u40) ∗
        (∃∗ u48 : BitVec 64, (a + 40#64) ↦₆₄ u48) ∗
        (∃∗ u56 : BitVec 64, (a + 48#64) ↦₆₄ u56) ∗
        (∃∗ u64 : BitVec 64, (a + 56#64) ↦₆₄ u64) ∗
        (∃∗ u72 : BitVec 64, (a + 64#64) ↦₆₄ u72) ∗
        (∃∗ u80 : BitVec 64, (a + 72#64) ↦₆₄ u80) ∗
        (∃∗ u88 : BitVec 64, (a + 80#64) ↦₆₄ u88) ∗
        (∃∗ u96 : BitVec 64, (a + 88#64) ↦₆₄ u96) ∗
        (∃∗ u104 : BitVec 64, (a + 96#64) ↦₆₄ u104) := by
      exact split_top <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        split_step (mem64_entails _) <| mem64_entails _
    refine Entails.trans (sepConj_mono_right hsplit) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro u104
    apply Entails.sepExists_elim; intro u96
    apply Entails.sepExists_elim; intro u88
    apply Entails.sepExists_elim; intro u80
    apply Entails.sepExists_elim; intro u72
    apply Entails.sepExists_elim; intro u64
    apply Entails.sepExists_elim; intro u56
    apply Entails.sepExists_elim; intro u48
    apply Entails.sepExists_elim; intro u40
    apply Entails.sepExists_elim; intro u32
    apply Entails.sepExists_elim; intro u24
    apply Entails.sepExists_elim; intro u16
    refine Entails.sepExists_right noneCap (Entails.sepExists_right u16
      (Entails.sepExists_right u24 (Entails.sepExists_right u32
        (Entails.sepExists_right u40 (Entails.sepExists_right u48
          (Entails.sepExists_right u56 (Entails.sepExists_right u64
            (Entails.sepExists_right u72 (Entails.sepExists_right u80
               (Entails.sepExists_right u88 (Entails.sepExists_right u96
                (Entails.sepExists_right u104 ?_))))))))))))
    unfold v1_ucWordsAt
    exact Entails.trans (Entails.pure_right (rfl : noneCap = noneCap) (Entails.refl _))
      (Entails.of_eq (by ac_rfl))
  | some uc =>
    unfold optProtoUnchunkedHeaderSentAt protoUnchunkedHeaderSentAt
    refine Entails.trans (sepConj_mono (v1_vecU8_unpack A a uc.ek)
      (sepConj_mono (v1_vecU8_unpack A (a + 24#64) uc.dk)
        (sepConj_mono_left (v1_optProtoAuthAt_unpack A (a + 48#64) uc.auth)))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro u56
    apply Entails.sepExists_elim; intro u64
    apply Entails.sepExists_elim; intro u72
    apply Entails.sepExists_elim; intro u80
    apply Entails.sepExists_elim; intro u88
    apply Entails.sepExists_elim; intro u96
    apply Entails.sepExists_elim; intro u32
    apply Entails.sepExists_elim; intro u40
    apply Entails.sepExists_elim; intro u48
    apply Entails.sepExists_elim; intro u8
    apply Entails.sepExists_elim; intro u16
    apply Entails.sepExists_elim; intro u24
    have ha32 : a + 24#64 + 8#64 = a + 32#64 := by bv_omega
    have ha40 : a + 24#64 + 16#64 = a + 40#64 := by bv_omega
    have ha56 : a + 48#64 + 8#64 = a + 56#64 := by bv_omega
    have ha64 : a + 48#64 + 16#64 = a + 64#64 := by bv_omega
    have ha72 : a + 48#64 + 24#64 = a + 72#64 := by bv_omega
    have ha80 : a + 48#64 + 32#64 = a + 80#64 := by bv_omega
    have ha88 : a + 48#64 + 40#64 = a + 88#64 := by bv_omega
    rw [ha32, ha40, ha56, ha64, ha72, ha80, ha88]
    refine Entails.trans (Entails.of_eq (show _ =
      ⌜u8.toNat < 2 ^ 63 ∧ u24 = BitVec.ofNat 64 uc.ek.length⌝ ∗
      ⌜u32.toNat < 2 ^ 63 ∧ u48 = BitVec.ofNat 64 uc.dk.length⌝ ∗
      ((a ↦₆₄ u8) ∗ ((a + 8#64) ↦₆₄ u16) ∗ ((a + 16#64) ↦₆₄ u24) ∗
       ((a + 24#64) ↦₆₄ u32) ∗ ((a + 32#64) ↦₆₄ u40) ∗ ((a + 40#64) ↦₆₄ u48) ∗
       ((a + 48#64) ↦₆₄ u56) ∗ ((a + 56#64) ↦₆₄ u64) ∗ ((a + 64#64) ↦₆₄ u72) ∗
       ((a + 72#64) ↦₆₄ u80) ∗ ((a + 80#64) ↦₆₄ u88) ∗ ((a + 88#64) ↦₆₄ u96) ∗
       ((a + 96#64) ↦₆₄ uc.epoch) ∗
       vecU8Payload A u8 u16 uc.ek ∗
       vecU8Payload A u32 u40 uc.dk ∗
       v1_optProtoAuthHeap A uc.auth u56 u64 u72 u80 u88 u96) by ac_rfl)) ?_
    apply Entails.pure_left; rintro ⟨hu8, hu24⟩
    apply Entails.pure_left; rintro ⟨hu32, hu48⟩
    refine Entails.sepExists_right u8 (Entails.sepExists_right u16
      (Entails.sepExists_right u24 (Entails.sepExists_right u32
        (Entails.sepExists_right u40 (Entails.sepExists_right u48
          (Entails.sepExists_right u56 (Entails.sepExists_right u64
            (Entails.sepExists_right u72 (Entails.sepExists_right u80
              (Entails.sepExists_right u88 (Entails.sepExists_right u96
                (Entails.sepExists_right uc.epoch ?_))))))))))))
    dsimp only [v1_optProtoUcHeap]
    refine Entails.trans (Entails.of_eq (show _ =
      v1_ucWordsAt a u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 uc.epoch ∗
      (vecU8Payload A u8 u16 uc.ek ∗
       vecU8Payload A u32 u40 uc.dk ∗
       v1_optProtoAuthHeap A uc.auth u56 u64 u72 u80 u88 u96) by
      unfold v1_ucWordsAt; ac_rfl)) ?_
    exact sepConj_mono_right (Entails.pure_right ⟨hu8, hu24, hu32, hu48, rfl⟩ (Entails.refl _))

/-! ## PB-to-Stack Copy (`+1104..+1192`) -/

theorem v1_memRegion_2304_split_1392_160_752 (fsp : BitVec 64) :
    memRegion fsp 2304 ⊢
      memRegion fsp 1392 ∗
      (∃∗ q0 : BitVec 128, (fsp + 1392#64) ↦₁₂₈ q0) ∗
      (∃∗ q1 : BitVec 128, (fsp + 1408#64) ↦₁₂₈ q1) ∗
      (∃∗ q2 : BitVec 128, (fsp + 1424#64) ↦₁₂₈ q2) ∗
      (∃∗ q3 : BitVec 128, (fsp + 1440#64) ↦₁₂₈ q3) ∗
      (∃∗ q4 : BitVec 128, (fsp + 1456#64) ↦₁₂₈ q4) ∗
      (∃∗ q5 : BitVec 128, (fsp + 1472#64) ↦₁₂₈ q5) ∗
      (∃∗ q6 : BitVec 128, (fsp + 1488#64) ↦₁₂₈ q6) ∗
      (∃∗ q7 : BitVec 128, (fsp + 1504#64) ↦₁₂₈ q7) ∗
      (∃∗ q8 : BitVec 128, (fsp + 1520#64) ↦₁₂₈ q8) ∗
      (∃∗ q9 : BitVec 128, (fsp + 1536#64) ↦₁₂₈ q9) ∗
      memRegion (fsp + 1552#64) 752 := by
  exact split_top <|
    split_step0 (Entails.refl _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    Entails.refl _

theorem v1_pointsTo128_eq_pair64_1008 (sp u8 u16 : BitVec 64) :
    ((sp - 1008#64) ↦₁₂₈ (u16 ++ u8)) =
      ((sp - 1008#64) ↦₆₄ u8) ∗ ((sp - 1000#64) ↦₆₄ u16) := by
  rw [← EncoderFromPb.pointsTo64_pair_eq_pointsTo128 (sp - 1008#64) u8 u16]
  have ha : sp - 1008#64 + 8#64 = sp - 1000#64 := by bv_omega
  rw [ha]

/-- Copy the 160-byte payload `pbA + 8..168` to `fsp + 1392..1552` (`+1104..+1192`),
    branching to `+4204` if `u8 + 1 == 0` (`u8 = noneCap`) or falling through to `+1196`. -/
theorem v1_copy_pb_to_stack_1104
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1104#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      (if (u8 + 1#64 == 0#64) = true
       then (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4204#64
       else (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1196#64)
      s1
      (memRegion (s0.sp - 2400#64) 2304 ∗
        v1_pb128At pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
          w0 w8 w16 w24 w32 w40 w48 ∗
        Rest)
      (fun s2 P2 =>
        (P2 ⊢
          memRegion (s0.sp - 2400#64) 1392 ∗
          v1_ucWordsAt (s0.sp - 2400#64 + 1392#64)
            u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
          v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64)
            w0 w8 w16 w24 w32 w40 w48 ∗
          memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
          v1_pb128At pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
            w0 w8 w16 w24 w32 w40 w48 ∗
          Rest) ∧
        s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x20 = u8 ∧
        s2.readReg64 .x27 = pbA ∧
        TraceCalleeSaved s2 s0) := by
  rw [← v1_uc_and_enc_words_eq_pb128 pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 w0 w8 w16 w24 w32 w40 w48]
  refine SepWP.weaken_pre (sepConj_mono_left (v1_memRegion_2304_split_1392_160_752 (s0.sp - 2400#64))) ?_
  wp_simp_pre [v1_ucWordsAt, v1_optProtoPolyEncoderWordsAt, pointsTo128,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro q9
  apply ProofLib.SepWP.exists_left; intro q8
  apply ProofLib.SepWP.exists_left; intro q7
  apply ProofLib.SepWP.exists_left; intro q6
  apply ProofLib.SepWP.exists_left; intro q5
  apply ProofLib.SepWP.exists_left; intro q4
  apply ProofLib.SepWP.exists_left; intro q3
  apply ProofLib.SepWP.exists_left; intro q2
  apply ProofLib.SepWP.exists_left; intro q1
  apply ProofLib.SepWP.exists_left; intro q0
  states_from_pb_fetches_range b (Rust.withPanics ext) 1104 92
  dsimp only [tripleRatchetProgAtExt, statesFromPbName,
    BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  by_cases hcmn : (u8 + 1#64 == 0#64) = true <;>
    simp only [hcmn, Bool.false_eq_true, ↓reduceIte]
  · wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · dsimp only [v1_ucWordsAt, v1_optProtoPolyEncoderWordsAt]
      simp only [arm64_norm]
      exact Entails.of_eq (by ac_rfl)
    · wp_done
  · wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · dsimp only [v1_ucWordsAt, v1_optProtoPolyEncoderWordsAt]
      simp only [arm64_norm]
      exact Entails.of_eq (by ac_rfl)
    · wp_done

theorem v1_merge_1392_104_1496 (fsp : BitVec 64) :
    memRegion fsp 1392 ∗ memRegion (fsp + 1392#64) 104 ⊢ memRegion fsp 1496 :=
  collapse_top <| collapse_step0 (Entails.refl _) <| Entails.refl _

/-- Variant 1 error path when `s.uc = none` (`+1104 -> +4204 -> s0.x30`). -/
theorem v1_keysSampled_uc_none_sfa
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : StatesFromPbAlloc b A ext)
    (s0 s1 : State) (out pbA : BitVec 64)
    (u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1104#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        (pbA ↦₆₄ 0x8000000000000001#64) ∗
        v1_pb128At pbA noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
          w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (pbA + 168#64) 56 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        statesFromPbJumpTableAt b ∗
        A.pool)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTableAt b ∗
          A.pool ∗
          stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hcopy := v1_copy_pb_to_stack_1104 s0 s1 out pbA
    noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 w0 w8 w16 w24 w32 w40 w48
    (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
     statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗
     (pbA ↦₆₄ 0x8000000000000001#64) ∗
     memRegion (pbA + 168#64) 56 ∗
     v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
     statesFromPbJumpTableAt b ∗
     A.pool)
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1
  have hcmn : (noneCap + 1#64 == 0#64) = true := by decide
  simp only [hcmn, ↓reduceIte] at hcopy
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4204#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 1496 ∗
      v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
      v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
      memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      A.pool ∗
      (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b))
    (Q := fun s2 =>
      s2.sp = s0.sp - 2400#64 ∧
      s2.readReg64 .x19 = out ∧
      TraceCalleeSaved s2 s0)
    (SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (SepWP.mono hcopy fun s2 P2 _ _ ⟨hP2, hsp2, hx19_2, _, _, htr2⟩ => ?_)) ?_
  · refine ⟨Entails.trans hP2 ?_, hsp2, hx19_2, htr2⟩
    have huc := v1_ucWordsAt_entails_104 (s0.sp - 2400#64 + 1392#64)
      noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
    have h1496 := v1_merge_1392_104_1496 (s0.sp - 2400#64)
    have hpb := v1_pb128_entails_full_224 pbA
      noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 w0 w8 w16 w24 w32 w40 w48
    refine Entails.trans (Entails.of_eq (show _ =
      (memRegion (s0.sp - 2400#64) 1392 ∗
       v1_ucWordsAt (s0.sp - 2400#64 + 1392#64)
         noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104) ∗
      ((pbA ↦₆₄ 0x8000000000000001#64) ∗
       v1_pb128At pbA noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
         w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion (pbA + 168#64) 56) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
       v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       A.pool ∗
       statesFromPbJumpTableAt b) by ac_rfl)) ?_
    exact Entails.trans
      (sepConj_mono (Entails.trans (sepConj_mono_right huc) h1496) (sepConj_mono_left hpb))
      (Entails.of_eq (by ac_rfl))
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, htr2⟩
    have hdrop := v1_drop_sendingHdr_4204_sfa (A := A) (F := F) hA s0 s2 out optEnc
      w0 w8 w16 w24 w32 w40 w48
      (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b)
      hsp0_align hpc2 hrun2 hsp2 hx19_2 htr2
    refine SepWP.mono hdrop fun sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩ =>
      ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcc_f, htr_f⟩

/-! ## Validation (`+1196..+1260`) and `Authenticator::from_pb` (`+1260..+4016`) -/

theorem v1_memRegion_1392_split_frame (fsp : BitVec 64) :
    memRegion fsp 1392 ⊢
      memRegion fsp 64 ∗
      (∃∗ w64 : BitVec 64, (fsp + 64#64) ↦₆₄ w64) ∗
      memRegion (fsp + 72#64) 104 ∗
      (∃∗ w176 : BitVec 64, (fsp + 176#64) ↦₆₄ w176) ∗
      (∃∗ w184 : BitVec 64, (fsp + 184#64) ↦₆₄ w184) ∗
      (∃∗ w192 : BitVec 64, (fsp + 192#64) ↦₆₄ w192) ∗
      (∃∗ w200 : BitVec 64, (fsp + 200#64) ↦₆₄ w200) ∗
      memRegion (fsp + 208#64) 8 ∗
      (∃∗ w216 : BitVec 64, (fsp + 216#64) ↦₆₄ w216) ∗
      (∃∗ w224 : BitVec 64, (fsp + 224#64) ↦₆₄ w224) ∗
      (∃∗ w232 : BitVec 64, (fsp + 232#64) ↦₆₄ w232) ∗
      memRegion (fsp + 240#64) 1152 := by
  exact split_top <|
    split_step0 (Entails.refl _) <|
    split_step (mem64_entails _) <|
    split_step (Entails.refl _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (Entails.refl _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    Entails.refl _

theorem v1_frame_entails_192_216_224_1496
    (fsp w64 w176 w184 w192 w200 w216 w224 w232 : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 : BitVec 64) :
    memRegion fsp 64 ∗
      ((fsp + 64#64) ↦₆₄ w64) ∗
      memRegion (fsp + 72#64) 104 ∗
      ((fsp + 176#64) ↦₆₄ w176) ∗
      ((fsp + 184#64) ↦₆₄ w184) ∗
      ((fsp + 192#64) ↦₆₄ w192) ∗
      ((fsp + 200#64) ↦₆₄ w200) ∗
      memRegion (fsp + 208#64) 8 ∗
      ((fsp + 216#64) ↦₆₄ w216) ∗
      ((fsp + 224#64) ↦₆₄ w224) ∗
      ((fsp + 232#64) ↦₆₄ w232) ∗
      memRegion (fsp + 240#64) 1152 ∗
      v1_ucWordsAt (fsp + 1392#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ⊢
      memRegion fsp 192 ∗
      ((fsp + 192#64) ↦₆₄ w192) ∗
      memRegion (fsp + 200#64) 16 ∗
      ((fsp + 216#64) ↦₆₄ w216) ∗
      ((fsp + 224#64) ↦₆₄ w224) ∗
      memRegion (fsp + 232#64) 1264 := by
  have h192 : memRegion fsp 64 ∗ ((fsp + 64#64) ↦₆₄ w64) ∗ memRegion (fsp + 72#64) 104 ∗
      ((fsp + 176#64) ↦₆₄ w176) ∗ ((fsp + 184#64) ↦₆₄ w184) ⊢ memRegion fsp 192 :=
    collapse_top <| collapse_step0 (Entails.refl _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Entails.refl _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      Drop.pointsTo64_entails_memRegion _ _
  have h16 : ((fsp + 200#64) ↦₆₄ w200) ∗ memRegion (fsp + 208#64) 8 ⊢ memRegion (fsp + 200#64) 16 :=
    collapse_top <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| Entails.refl _
  have huc := v1_ucWordsAt_entails_104 (fsp + 1392#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
  have h1264 : ((fsp + 232#64) ↦₆₄ w232) ∗ memRegion (fsp + 240#64) 1152 ∗ memRegion (fsp + 1392#64) 104 ⊢
      memRegion (fsp + 232#64) 1264 :=
    collapse_top <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Entails.refl _) <| Entails.refl _
  refine Entails.trans (Entails.of_eq (show _ =
    (memRegion fsp 64 ∗ ((fsp + 64#64) ↦₆₄ w64) ∗ memRegion (fsp + 72#64) 104 ∗
     ((fsp + 176#64) ↦₆₄ w176) ∗ ((fsp + 184#64) ↦₆₄ w184)) ∗
    ((fsp + 192#64) ↦₆₄ w192) ∗
    (((fsp + 200#64) ↦₆₄ w200) ∗ memRegion (fsp + 208#64) 8) ∗
    ((fsp + 216#64) ↦₆₄ w216) ∗
    ((fsp + 224#64) ↦₆₄ w224) ∗
    (((fsp + 232#64) ↦₆₄ w232) ∗ memRegion (fsp + 240#64) 1152 ∗
     v1_ucWordsAt (fsp + 1392#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104) by ac_rfl)) ?_
  exact sepConj_mono h192 (sepConj_mono_right (sepConj_mono h16 (sepConj_mono_right (sepConj_mono_right
    (Entails.trans (sepConj_mono_right (sepConj_mono_right huc)) h1264)))))

/-- Validation error paths at `+1196`: when `u48 != 2400#64`, `u24 != 1152#64`, or `uc.auth = none`,
    cleans up `uc` and `sendingHdr` and returns `Err(StateDecode)`. -/
theorem v1_validate_err_1196_sfa
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : StatesFromPbAlloc b A ext)
    (s0 s1 : State) (out pbA : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 : BitVec 64)
    (optAuth : Option ProtoAuthenticator)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (herr : (u48 == 2400#64) = false ∨ (u24 == 1152#64) = false ∨ optAuth = none)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1196#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = u8)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1392 ∗
        v1_ucWordsAt (s0.sp - 2400#64 + 1392#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64)
          w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A u8 u16 ∗
        vecCapPtrDealloc A u32 u40 ∗
        v1_optProtoAuthHeap A optAuth u56 u64 u72 u80 u88 u96 ∗
        A.pool ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          A.pool ∗
          Rest ∗
          stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left
    (v1_memRegion_1392_split_frame (s0.sp - 2400#64)))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro w232
  apply ProofLib.SepWP.exists_left; intro w224
  apply ProofLib.SepWP.exists_left; intro w216
  apply ProofLib.SepWP.exists_left; intro w200
  apply ProofLib.SepWP.exists_left; intro w192
  apply ProofLib.SepWP.exists_left; intro w184
  apply ProofLib.SepWP.exists_left; intro w176
  apply ProofLib.SepWP.exists_left; intro w64
  by_cases hdk : (u48 == 2400#64) = true
  · by_cases hek : (u24 == 1152#64) = true
    · have hauth : optAuth = none := by
        rcases herr with h | h | h
        · rw [hdk] at h; cases h
        · rw [hek] at h; cases h
        · exact h
      subst hauth
      dsimp only [v1_optProtoAuthHeap]
      wp_simp_pre [sepConj_assoc, sepConj_left_comm _ ⌜_⌝, sepConj_comm _ ⌜_⌝]
      apply SepWP.pure_elim; intro hu56
      subst hu56
      refine EncoderFromPb.seq_clean
        (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3936#64)
        (P_mid :=
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 192 ∗
          ((s0.sp - 2400#64 + 192#64) ↦₆₄ w192) ∗
          memRegion (s0.sp - 2400#64 + 200#64) 16 ∗
          ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
          ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
          memRegion (s0.sp - 2400#64 + 232#64) 1264 ∗
          v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
          v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
          memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
          statesFromPbSavedCells s0 ∗
          memRegion out chunkedStatesSize ∗
          vecCapPtrDealloc A u8 u16 ∗
          vecCapPtrDealloc A u32 u40 ∗
          A.pool ∗
          Rest)
        (Q := fun s2 =>
          s2.sp = s0.sp - 2400#64 ∧
          s2.readReg64 .x19 = out ∧
          s2.readReg64 .x20 = u8 ∧
          s2.readReg64 .x9 = u16 ∧
          TraceCalleeSaved s2 s0)
        ?_ ?_
      · states_from_pb_fetches_range b (Rust.withPanics ext) 1196 64
        dsimp only [tripleRatchetProgAtExt, statesFromPbName, v1_ucWordsAt, noneCap,
          BitVec.ofNat_eq_ofNat] at hpc1 hdk hek ⊢
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "<spqr::v1::chunked::states::States>::from_pb" = entry
        examples_hide_fetches
        wp_steps
        refine EncoderFromPb.align_pre ?_ ?_
        · have hf := v1_frame_entails_192_216_224_1496 (s0.sp - 2400#64)
            w64 w176 w184 w192 w200 u40 u32 w232
            u8 u16 u24 u32 u40 u48 18446744073709551615#64 u64 u72 u80 u88 u96 u104
          dsimp only [v1_ucWordsAt] at hf
          simp only [arm64_norm] at hf ⊢
          refine Entails.trans (Entails.of_eq (show _ =
            (memRegion (s0.sp - 2400#64) 64 ∗
             ((s0.sp - 2336#64) ↦₆₄ w64) ∗
             memRegion (s0.sp - 2328#64) 104 ∗
             ((s0.sp - 2224#64) ↦₆₄ w176) ∗
             ((s0.sp - 2216#64) ↦₆₄ w184) ∗
             ((s0.sp - 2208#64) ↦₆₄ w192) ∗
             ((s0.sp - 2200#64) ↦₆₄ w200) ∗
             memRegion (s0.sp - 2192#64) 8 ∗
             ((s0.sp - 2184#64) ↦₆₄ u40) ∗
             ((s0.sp - 2176#64) ↦₆₄ u32) ∗
             ((s0.sp - 2168#64) ↦₆₄ w232) ∗
             memRegion (s0.sp - 2160#64) 1152 ∗
             ((s0.sp - 1008#64) ↦₆₄ u8) ∗ ((s0.sp - 1000#64) ↦₆₄ u16) ∗
             ((s0.sp - 992#64) ↦₆₄ u24) ∗ ((s0.sp - 984#64) ↦₆₄ u32) ∗
             ((s0.sp - 976#64) ↦₆₄ u40) ∗ ((s0.sp - 968#64) ↦₆₄ u48) ∗
             ((s0.sp - 960#64) ↦₆₄ 18446744073709551615#64) ∗ ((s0.sp - 952#64) ↦₆₄ u64) ∗
             ((s0.sp - 944#64) ↦₆₄ u72) ∗ ((s0.sp - 936#64) ↦₆₄ u80) ∗
             ((s0.sp - 928#64) ↦₆₄ u88) ∗ ((s0.sp - 920#64) ↦₆₄ u96) ∗
             ((s0.sp - 912#64) ↦₆₄ u104)) ∗
            (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
             v1_optProtoPolyEncoderWordsAt (s0.sp - 904#64) w0 w8 w16 w24 w32 w40 w48 ∗
             v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
             memRegion (s0.sp - 848#64) 752 ∗
             statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
             vecCapPtrDealloc A u8 u16 ∗ vecCapPtrDealloc A u32 u40 ∗ A.pool ∗ Rest) by ac_rfl)) ?_
          exact Entails.trans (sepConj_mono_left hf) (Entails.of_eq (by ac_rfl))
        · wp_done
      · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx20_2, hx9_2, htr2⟩
        exact v1_drop_uc_and_sendingHdr_3936_sfa (A := A) (F := F) hA s0 s2 out
          u8 u16 u32 u40 w192 optEnc w0 w8 w16 w24 w32 w40 w48 Rest
          hsp0_align hpc2 hrun2 hsp2 hx19_2 hx20_2 hx9_2 htr2
    · have hek_f : (u24 == 1152#64) = false := Bool.eq_false_iff.mpr hek
      refine EncoderFromPb.seq_clean
        (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3872#64)
        (P_mid :=
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 192 ∗
          ((s0.sp - 2400#64 + 192#64) ↦₆₄ w192) ∗
          memRegion (s0.sp - 2400#64 + 200#64) 16 ∗
          ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
          ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
          memRegion (s0.sp - 2400#64 + 232#64) 1264 ∗
          v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
          v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
          memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
          statesFromPbSavedCells s0 ∗
          memRegion out chunkedStatesSize ∗
          vecCapPtrDealloc A u8 u16 ∗
          vecCapPtrDealloc A u32 u40 ∗
          v1_optProtoAuthHeap A optAuth u56 u64 u72 u80 u88 u96 ∗
          A.pool ∗
          Rest)
        (Q := fun s2 =>
          s2.sp = s0.sp - 2400#64 ∧
          s2.readReg64 .x19 = out ∧
          s2.readReg64 .x20 = u8 ∧
          s2.readReg64 .x9 = u16 ∧
          s2.readReg64 .x25 = u56 ∧
          s2.readReg64 .x28 = u64 ∧
          s2.readReg64 .x23 = u80 ∧
          s2.readReg64 .x24 = u88 ∧
          TraceCalleeSaved s2 s0)
        ?_ ?_
      · states_from_pb_fetches_range b (Rust.withPanics ext) 1196 56
        dsimp only [tripleRatchetProgAtExt, statesFromPbName, v1_ucWordsAt,
          BitVec.ofNat_eq_ofNat] at hpc1 hdk hek_f ⊢
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "<spqr::v1::chunked::states::States>::from_pb" = entry
        examples_hide_fetches
        wp_steps
        refine EncoderFromPb.align_pre ?_ ?_
        · have hf := v1_frame_entails_192_216_224_1496 (s0.sp - 2400#64)
            w64 w176 w184 w192 w200 u40 u32 w232
            u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
          dsimp only [v1_ucWordsAt] at hf
          simp only [arm64_norm] at hf ⊢
          refine Entails.trans (Entails.of_eq (show _ =
            (memRegion (s0.sp - 2400#64) 64 ∗
             ((s0.sp - 2336#64) ↦₆₄ w64) ∗
             memRegion (s0.sp - 2328#64) 104 ∗
             ((s0.sp - 2224#64) ↦₆₄ w176) ∗
             ((s0.sp - 2216#64) ↦₆₄ w184) ∗
             ((s0.sp - 2208#64) ↦₆₄ w192) ∗
             ((s0.sp - 2200#64) ↦₆₄ w200) ∗
             memRegion (s0.sp - 2192#64) 8 ∗
             ((s0.sp - 2184#64) ↦₆₄ u40) ∗
             ((s0.sp - 2176#64) ↦₆₄ u32) ∗
             ((s0.sp - 2168#64) ↦₆₄ w232) ∗
             memRegion (s0.sp - 2160#64) 1152 ∗
             ((s0.sp - 1008#64) ↦₆₄ u8) ∗ ((s0.sp - 1000#64) ↦₆₄ u16) ∗
             ((s0.sp - 992#64) ↦₆₄ u24) ∗ ((s0.sp - 984#64) ↦₆₄ u32) ∗
             ((s0.sp - 976#64) ↦₆₄ u40) ∗ ((s0.sp - 968#64) ↦₆₄ u48) ∗
             ((s0.sp - 960#64) ↦₆₄ u56) ∗ ((s0.sp - 952#64) ↦₆₄ u64) ∗
             ((s0.sp - 944#64) ↦₆₄ u72) ∗ ((s0.sp - 936#64) ↦₆₄ u80) ∗
             ((s0.sp - 928#64) ↦₆₄ u88) ∗ ((s0.sp - 920#64) ↦₆₄ u96) ∗
             ((s0.sp - 912#64) ↦₆₄ u104)) ∗
            (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
             v1_optProtoPolyEncoderWordsAt (s0.sp - 904#64) w0 w8 w16 w24 w32 w40 w48 ∗
             v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
             memRegion (s0.sp - 848#64) 752 ∗
             statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
             vecCapPtrDealloc A u8 u16 ∗ vecCapPtrDealloc A u32 u40 ∗
             v1_optProtoAuthHeap A optAuth u56 u64 u72 u80 u88 u96 ∗ A.pool ∗ Rest) by ac_rfl)) ?_
          exact Entails.trans (sepConj_mono_left hf) (Entails.of_eq (by ac_rfl))
        · wp_done
      · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx20_2, hx9_2, hx25_2, hx28_2, hx23_2, hx24_2, htr2⟩
        exact v1_drop_uc_and_sendingHdr_3872_sfa (A := A) (F := F) hA s0 s2 out
          u8 u16 u32 u40 w192 optAuth u56 u64 u72 u80 u88 u96
          optEnc w0 w8 w16 w24 w32 w40 w48 Rest
          hsp0_align hpc2 hrun2 hsp2 hx19_2 hx20_2 hx9_2 hx25_2 hx28_2 hx23_2 hx24_2 htr2
  · have hdk_f : (u48 == 2400#64) = false := Bool.eq_false_iff.mpr hdk
    refine EncoderFromPb.seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3872#64)
      (P_mid :=
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 192 ∗
        ((s0.sp - 2400#64 + 192#64) ↦₆₄ w192) ∗
        memRegion (s0.sp - 2400#64 + 200#64) 16 ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
        memRegion (s0.sp - 2400#64 + 232#64) 1264 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A u8 u16 ∗
        vecCapPtrDealloc A u32 u40 ∗
        v1_optProtoAuthHeap A optAuth u56 u64 u72 u80 u88 u96 ∗
        A.pool ∗
        Rest)
      (Q := fun s2 =>
        s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x20 = u8 ∧
        s2.readReg64 .x9 = u16 ∧
        s2.readReg64 .x25 = u56 ∧
        s2.readReg64 .x28 = u64 ∧
        s2.readReg64 .x23 = u80 ∧
        s2.readReg64 .x24 = u88 ∧
        TraceCalleeSaved s2 s0)
      ?_ ?_
    · states_from_pb_fetches_range b (Rust.withPanics ext) 1196 44
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, v1_ucWordsAt,
        BitVec.ofNat_eq_ofNat] at hpc1 hdk_f ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · have hf := v1_frame_entails_192_216_224_1496 (s0.sp - 2400#64)
          w64 w176 w184 w192 w200 u40 u32 w232
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
        dsimp only [v1_ucWordsAt] at hf
        simp only [arm64_norm] at hf ⊢
        refine Entails.trans (Entails.of_eq (show _ =
          (memRegion (s0.sp - 2400#64) 64 ∗
           ((s0.sp - 2336#64) ↦₆₄ w64) ∗
           memRegion (s0.sp - 2328#64) 104 ∗
           ((s0.sp - 2224#64) ↦₆₄ w176) ∗
           ((s0.sp - 2216#64) ↦₆₄ w184) ∗
           ((s0.sp - 2208#64) ↦₆₄ w192) ∗
           ((s0.sp - 2200#64) ↦₆₄ w200) ∗
           memRegion (s0.sp - 2192#64) 8 ∗
           ((s0.sp - 2184#64) ↦₆₄ u40) ∗
           ((s0.sp - 2176#64) ↦₆₄ u32) ∗
           ((s0.sp - 2168#64) ↦₆₄ w232) ∗
           memRegion (s0.sp - 2160#64) 1152 ∗
           ((s0.sp - 1008#64) ↦₆₄ u8) ∗ ((s0.sp - 1000#64) ↦₆₄ u16) ∗
           ((s0.sp - 992#64) ↦₆₄ u24) ∗ ((s0.sp - 984#64) ↦₆₄ u32) ∗
           ((s0.sp - 976#64) ↦₆₄ u40) ∗ ((s0.sp - 968#64) ↦₆₄ u48) ∗
           ((s0.sp - 960#64) ↦₆₄ u56) ∗ ((s0.sp - 952#64) ↦₆₄ u64) ∗
           ((s0.sp - 944#64) ↦₆₄ u72) ∗ ((s0.sp - 936#64) ↦₆₄ u80) ∗
           ((s0.sp - 928#64) ↦₆₄ u88) ∗ ((s0.sp - 920#64) ↦₆₄ u96) ∗
           ((s0.sp - 912#64) ↦₆₄ u104)) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           v1_optProtoPolyEncoderWordsAt (s0.sp - 904#64) w0 w8 w16 w24 w32 w40 w48 ∗
           v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
           memRegion (s0.sp - 848#64) 752 ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
           vecCapPtrDealloc A u8 u16 ∗ vecCapPtrDealloc A u32 u40 ∗
           v1_optProtoAuthHeap A optAuth u56 u64 u72 u80 u88 u96 ∗ A.pool ∗ Rest) by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hf) (Entails.of_eq (by ac_rfl))
      · wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx20_2, hx9_2, hx25_2, hx28_2, hx23_2, hx24_2, htr2⟩
      exact v1_drop_uc_and_sendingHdr_3872_sfa (A := A) (F := F) hA s0 s2 out
        u8 u16 u32 u40 w192 optAuth u56 u64 u72 u80 u88 u96
        optEnc w0 w8 w16 w24 w32 w40 w48 Rest
        hsp0_align hpc2 hrun2 hsp2 hx19_2 hx20_2 hx9_2 hx25_2 hx28_2 hx23_2 hx24_2 htr2

theorem v1_merge_240_1152_104_1256 (fsp : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 : BitVec 64) :
    memRegion (fsp + 240#64) 1152 ∗
      v1_ucWordsAt (fsp + 1392#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ⊢
      memRegion (fsp + 240#64) 1256 := by
  have huc := v1_ucWordsAt_entails_104 (fsp + 1392#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
  have hm : memRegion (fsp + 240#64) 1152 ∗ memRegion (fsp + 1392#64) 104 ⊢ memRegion (fsp + 240#64) 1256 :=
    collapse_top <| collapse_step (Entails.refl _) <| Entails.refl _
  exact Entails.trans (sepConj_mono_right huc) hm

/-- Validation success step (`+1196 -> +1292`): when `u48 = 2400#64`, `u24 = 1152#64`, and
    `u56.toNat < 2 ^ 63`, stores stack slots `64, 176, 192, 216, 224, 232` and collapses
    `v1_ucWordsAt (fsp + 1392#64)` into `memRegion (fsp + 240#64) 1256`. -/
theorem v1_validate_ok_1196_1292
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 : BitVec 64)
    (w64 w176 w192 w216 w224 w232 : BitVec 64)
    (Rest : SepProp)
    (hdk : (u48 == 2400#64) = true)
    (hek : (u24 == 1152#64) = true)
    (hu56 : u56.toNat < 2 ^ 63)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1196#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = u8)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1292#64) s1
      (((s0.sp - 2400#64 + 64#64) ↦₆₄ w64) ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ w176) ∗
        ((s0.sp - 2400#64 + 192#64) ↦₆₄ w192) ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ w216) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ w224) ∗
        ((s0.sp - 2400#64 + 232#64) ↦₆₄ w232) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 1152 ∗
        v1_ucWordsAt (s0.sp - 2400#64 + 1392#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
        Rest)
      (fun s2 P2 =>
        (P2 ⊢
          ((s0.sp - 2400#64 + 64#64) ↦₆₄ u104) ∗
          ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
          ((s0.sp - 2400#64 + 192#64) ↦₆₄ u48) ∗
          ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
          ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
          ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
          memRegion (s0.sp - 2400#64 + 240#64) 1256 ∗
          Rest) ∧
        s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x20 = u72 ∧
        s2.readReg64 .x21 = u8 ∧
        s2.readReg64 .x22 = u48 ∧
        s2.readReg64 .x23 = u80 ∧
        s2.readReg64 .x24 = u88 ∧
        s2.readReg64 .x25 = u56 ∧
        s2.readReg64 .x27 = pbA ∧
        s2.readReg64 .x28 = u64 ∧
        s2.readReg64 .x9 = u96 ∧
        TraceCalleeSaved s2 s0) := by
  have hcmn : (u56 + 1#64 == 0#64) = false :=
    Bool.eq_false_iff.mpr (cap_add_one_beq_zero_false hu56)
  states_from_pb_fetches_range b (Rust.withPanics ext) 1196 96
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, v1_ucWordsAt,
    BitVec.ofNat_eq_ofNat] at hpc1 hdk hek ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · have hm := v1_merge_240_1152_104_1256 (s0.sp - 2400#64)
      u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
    have hdk_eq : u48 = 2400#64 := beq_iff_eq.mp hdk
    dsimp only [v1_ucWordsAt] at hm
    simp only [arm64_norm] at hm ⊢
    refine Entails.trans (Entails.of_eq (show _ =
      (memRegion (s0.sp - 2160#64) 1152 ∗
       ((s0.sp - 1008#64) ↦₆₄ u8) ∗ ((s0.sp - 1000#64) ↦₆₄ u16) ∗
       ((s0.sp - 992#64) ↦₆₄ u24) ∗ ((s0.sp - 984#64) ↦₆₄ u32) ∗
       ((s0.sp - 976#64) ↦₆₄ u40) ∗ ((s0.sp - 968#64) ↦₆₄ u48) ∗
       ((s0.sp - 960#64) ↦₆₄ u56) ∗ ((s0.sp - 952#64) ↦₆₄ u64) ∗
       ((s0.sp - 944#64) ↦₆₄ u72) ∗ ((s0.sp - 936#64) ↦₆₄ u80) ∗
       ((s0.sp - 928#64) ↦₆₄ u88) ∗ ((s0.sp - 920#64) ↦₆₄ u96) ∗
       ((s0.sp - 912#64) ↦₆₄ u104)) ∗
      (((s0.sp - 2336#64) ↦₆₄ u104) ∗
       ((s0.sp - 2224#64) ↦₆₄ u16) ∗
       ((s0.sp - 2208#64) ↦₆₄ 2400#64) ∗
       ((s0.sp - 2184#64) ↦₆₄ u40) ∗
       ((s0.sp - 2176#64) ↦₆₄ u32) ∗
       ((s0.sp - 2168#64) ↦₆₄ u96) ∗
       Rest) by ac_rfl)) ?_
    rw [hdk_eq] at hm ⊢
    exact Entails.trans (sepConj_mono_left hm) (Entails.of_eq (by ac_rfl))
  · wp_done

set_option maxHeartbeats 800000 in
/-- `Authenticator::from_pb` segment (`+1292 -> +8756`) in Variant 1:
    allocates and copies `auth.rootKey` into `pa1 = s1.readReg64 .x26` (or `1#64` if empty). -/
theorem v1_auth_from_pb_step1_1292_8756_sfa
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : StatesFromPbAlloc b A ext) (s0 s : State) (target_pc fsp out pbA : BitVec 64)
    (u8 u56 u64 u80 u88 u96 : BitVec 64)
    (auth : ProtoAuthenticator) (Frame R : SepProp)
    (post : State → SepProp → Prop) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1292#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length)
    (hx21 : s.readReg64 .x21 = u8)
    (hx23 : s.readReg64 .x23 = u80)
    (hx24 : s.readReg64 .x24 = u88)
    (hx25 : s.readReg64 .x25 = u56)
    (hx27 : s.readReg64 .x27 = pbA)
    (hx28 : s.readReg64 .x28 = u64)
    (hx9 : s.readReg64 .x9 = u96)
    (hu96 : u96 = BitVec.ofNat 64 auth.macKey.length)
    (htr : TraceCalleeSaved s s0)
    (hnext : ∀ (pa1 : BitVec 64) (s1 : State),
      s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8756#64 →
      s1.status = .Running →
      (s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧
       s1.readReg64 .x21 = u8 ∧
       s1.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length ∧
       s1.readReg64 .x23 = u80 ∧ s1.readReg64 .x24 = u88 ∧
       s1.readReg64 .x25 = u56 ∧ s1.readReg64 .x26 = pa1 ∧
       s1.readReg64 .x27 = pbA ∧ s1.readReg64 .x28 = u64 ∧
       s1.readReg64 .x9 = u96 ∧ TraceCalleeSaved s1 s0) →
      SepWPp (tripleRatchetProgAtExt b ext) target_pc s1
        (stackAt fsp encoderFromPbStack ∗
         ((fsp + 232#64) ↦₆₄ u96) ∗
         vecCapPtrDealloc A u56 u64 ∗
         vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
         A.pool ∗ Frame)
        post (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) target_pc s
      (stackAt fsp encoderFromPbStack ∗
       ((fsp + 232#64) ↦₆₄ u96) ∗
       vecU8Payload A u56 u64 auth.rootKey ∗
       A.pool ∗ Frame)
      post (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  have hr_cases : auth.rootKey = [] ∨ 0 < auth.rootKey.length := by cases auth.rootKey <;> simp
  rcases hr_cases with hr_nil | hr_pos
  · refine sepWPp_seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8756#64)
      (P_mid := stackAt fsp encoderFromPbStack ∗ ((fsp + 232#64) ↦₆₄ u96) ∗
        vecCapPtrDealloc A u56 u64 ∗
        vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) 1#64 auth.rootKey ∗ A.pool ∗ Frame)
      (Q_regs := fun s1 => s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧
        s1.readReg64 .x21 = u8 ∧
        s1.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length ∧
        s1.readReg64 .x23 = u80 ∧ s1.readReg64 .x24 = u88 ∧
        s1.readReg64 .x25 = u56 ∧ s1.readReg64 .x26 = 1#64 ∧
        s1.readReg64 .x27 = pbA ∧ s1.readReg64 .x28 = u64 ∧
        s1.readReg64 .x9 = u96 ∧ TraceCalleeSaved s1 s0)
      ?_ (hnext 1#64)
    clear hnext; rw [hr_nil] at hx20 ⊢
    states_from_pb_fetches_range b (Rust.withPanics ext) 1292 4
    states_from_pb_fetches_range b (Rust.withPanics ext) 8748 8
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, List.length_nil, BitVec.ofNat_eq_ofNat] at hpc hx20 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches; wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have hd := vecU8Payload_entails_dealloc A u56 u64 []
      have hn := vecU8Payload_of_nil A
      dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hn
      refine Entails.trans (Entails.of_eq (show _ =
        vecU8Payload A u56 u64 [] ∗ emp ∗
        stackAt fsp encoderFromPbStack ∗ ((fsp + 232#64) ↦₆₄ u96) ∗ A.pool ∗ Frame by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hd (sepConj_mono_left hn)) (Entails.of_eq (by ac_rfl))
    · wp_done
  · refine SepWPp.weaken_pre (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (vecU8Payload_pos_unpack A u56 u64 auth.rootKey hr_pos)))) ?_
    rw [show stackAt fsp encoderFromPbStack ∗ ((fsp + 232#64) ↦₆₄ u96) ∗
          (⌜auth.rootKey.length ≤ u56.toNat ∧ u56.toNat < 2 ^ 63 ∧
            u64 ≠ 0#64 ∧ u56 ≠ 0#64⌝ ∗
           (A.live u64 u56.toNat 1 ∗ (u64 ↦ₛ auth.rootKey) ∗
            memRegion (u64 + BitVec.ofNat 64 auth.rootKey.length) (u56.toNat - auth.rootKey.length))) ∗
          A.pool ∗ Frame =
        ⌜auth.rootKey.length ≤ u56.toNat ∧ u56.toNat < 2 ^ 63 ∧
          u64 ≠ 0#64 ∧ u56 ≠ 0#64⌝ ∗
        (stackAt fsp encoderFromPbStack ∗ ((fsp + 232#64) ↦₆₄ u96) ∗
         A.live u64 u56.toNat 1 ∗ (u64 ↦ₛ auth.rootKey) ∗
         memRegion (u64 + BitVec.ofNat 64 auth.rootKey.length) (u56.toNat - auth.rootKey.length) ∗
         A.pool ∗ Frame) by ac_rfl]
    refine SepWPp.pure_elim fun ⟨hr_le, hr_cap, hptr0, hcap0_ne⟩ => ?_
    have hr_lt63 : auth.rootKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hr_le hr_cap
    have hr_lt64 : auth.rootKey.length < 2 ^ 64 := by omega
    have hr_toNat : (BitVec.ofNat 64 auth.rootKey.length).toNat = auth.rootKey.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr_lt64]
    have hr_ne0 : (BitVec.ofNat 64 auth.rootKey.length == 0#64) = false := ofNat_beq_zero_false hr_pos hr_lt64
    have hpow1 : ∃ k : Nat, 1 = 2 ^ k := ⟨0, rfl⟩
    have hr_lay3 : auth.rootKey.length + 1 ≤ 2 ^ 63 := hr_lt63
    have h1_toNat : (1#64 : BitVec 64).toNat = 1 := rfl
    rw [stackAt_encoderFromPb_split_allocHook fsp]; wp_simp_pre [sepConj_assoc]
    have hfn : libsignalSessionCode.fnOff statesFromPbName = 0x54cac := statesFromPb_fnOff
    have hshim := hA.shim_ok_at statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_no_alloc_shim_is_unstable_v2")); simp only [sessionShimSpec] at hshim
    have halloc := hA.alloc_ok_at statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_alloc")); simp only [rustAllocSpec] at halloc
    have hmc := hA.session_memcpy_ok_at statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "memcpy")); simp only [sessionMemcpySpec] at hmc
    have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
      (name := statesFromPbName) (k := (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "alloc::raw_vec::handle_error"))) (by rw [hfn, stubOff_handle_error])
    states_from_pb_fetches_range b (Rust.withPanics ext) 1292 52
    states_from_pb_fetches_range b (Rust.withPanics ext) 11608 12
    dsimp only [contractProg, tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hshim halloc hmc hpanic hpc hnext ⊢
    clear hfn hA
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)) = prog
      reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWPp]
    examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry + 1312#64)
    wp_steps; wp_apply; wp_steps; wp_call halloc (auth.rootKey.length, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom0 : sf_1.readReg64 Reg.x0 = 0#64
    · simp only [hoom0, BitVec.ofNat_eq_ofNat, ↓reduceIte]; rw [pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + (bv% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "alloc::raw_vec::handle_error"))); wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [statesFromPbOnPanic, sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [hoom0, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
      have hoom0_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom0
      rw [pull_alloc_pure]; refine SepWPp.pure_elim fun ⟨_, htr_alloc⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by rw [htr_alloc]; simp only [wp_norm, arm64_norm, *]
      refine sepWPp_seq_clean (mid := entry + 8756#64)
        (P_mid := stackAt fsp encoderFromPbStack ∗ ((fsp + 232#64) ↦₆₄ u96) ∗
          vecCapPtrDealloc A u56 u64 ∗
          vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) (sf_1.readReg64 Reg.x0) auth.rootKey ∗
          A.pool ∗ Frame)
        (Q_regs := fun s1 => s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧
          s1.readReg64 .x21 = u8 ∧
          s1.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length ∧
          s1.readReg64 .x23 = u80 ∧ s1.readReg64 .x24 = u88 ∧
          s1.readReg64 .x25 = u56 ∧ s1.readReg64 .x26 = sf_1.readReg64 Reg.x0 ∧
          s1.readReg64 .x27 = pbA ∧ s1.readReg64 .x28 = u64 ∧
          s1.readReg64 .x9 = u96 ∧ TraceCalleeSaved s1 s0)
        ?_ (hnext (sf_1.readReg64 Reg.x0))
      clear hnext
      have hsp_sf1 : sf_1.sp = fsp := by simp only [wp_norm, arm64_norm, *]
      wp_steps; wp_apply; wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · rw [stackAt_encoderFromPb_split_allocHook fsp, hsp_sf1]
        have hd := vecU8Payload_pos_dealloc A u56 u64 auth.rootKey hr_le hr_cap hptr0 hcap0_ne
        have hp := vecU8Payload_pos A (sf_1.readReg64 Reg.x0) auth.rootKey hr_pos hr_lt63 hoom0
        simp only [arm64_norm] at hd hp ⊢
        refine Entails.trans (Entails.of_eq (show _ =
          (A.live u64 u56.toNat 1 ∗ (u64 ↦ₛ auth.rootKey) ∗
           memRegion (u64 + BitVec.ofNat 64 auth.rootKey.length) (u56.toNat - auth.rootKey.length)) ∗
          (A.live (sf_1.readReg64 Reg.x0) auth.rootKey.length 1 ∗ (sf_1.readReg64 Reg.x0 ↦ₛ auth.rootKey)) ∗
          memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack ∗
          ((fsp + 232#64) ↦₆₄ u96) ∗ A.pool ∗ Frame by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono hd (sepConj_mono_left hp)) (Entails.of_eq (by ac_rfl))
      · wp_done

theorem v1_keysSampled_uc_none {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) (s0 s1 : State) (out pbA : BitVec 64)
    (u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (ha : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1104#64)
    (hr : s1.status = .Running) (hsp : s1.sp = s0.sp - 2400#64)
    (hx19 : s1.readReg64 .x19 = out) (hx27 : s1.readReg64 .x27 = pbA) (htr : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (pbA ↦₆₄ 0x8000000000000001#64) ∗
        v1_pb128At pbA noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (pbA + 168#64) 56 ∗ v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        statesFromPbJumpTableAt b ∗ A.pool)
      (fun sf Pf => (Pf ⊢ resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v1_keysSampled_uc_none_sfa (.of_allocContracts hA) s0 s1 out pbA
    u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 optEnc w0 w8 w16 w24 w32 w40 w48
    ha hpc hr hsp hx19 hx27 htr

theorem v1_validate_err_1196 {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) (s0 s1 : State) (out pbA : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 : BitVec 64) (optAuth : Option ProtoAuthenticator)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64) (Rest : SepProp)
    (herr : (u48 == 2400#64) = false ∨ (u24 == 1152#64) = false ∨ optAuth = none)
    (ha : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1196#64)
    (hr : s1.status = .Running) (hsp : s1.sp = s0.sp - 2400#64)
    (hx19 : s1.readReg64 .x19 = out) (hx20 : s1.readReg64 .x20 = u8) (htr : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 1392 ∗
        v1_ucWordsAt (s0.sp - 2400#64 + 1392#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗ statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗ vecCapPtrDealloc A u8 u16 ∗ vecCapPtrDealloc A u32 u40 ∗
        v1_optProtoAuthHeap A optAuth u56 u64 u72 u80 u88 u96 ∗ A.pool ∗ Rest)
      (fun sf Pf => (Pf ⊢ resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          A.pool ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v1_validate_err_1196_sfa (.of_allocContracts hA) s0 s1 out pbA
    u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 optAuth optEnc w0 w8 w16 w24 w32 w40 w48 Rest
    herr ha hpc hr hsp hx19 hx20 htr

theorem v1_auth_from_pb_step1_1292_8756 {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (s0 s : State) (target_pc fsp out pbA u8 u56 u64 u80 u88 u96 : BitVec 64)
    (auth : ProtoAuthenticator) (Frame R : SepProp) (post : State → SepProp → Prop)
    (ha : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1292#64)
    (hr : s.status = .Running) (hsp : s.sp = fsp) (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length) (hx21 : s.readReg64 .x21 = u8)
    (hx23 : s.readReg64 .x23 = u80) (hx24 : s.readReg64 .x24 = u88) (hx25 : s.readReg64 .x25 = u56)
    (hx27 : s.readReg64 .x27 = pbA) (hx28 : s.readReg64 .x28 = u64) (hx9 : s.readReg64 .x9 = u96)
    (hu96 : u96 = BitVec.ofNat 64 auth.macKey.length) (htr : TraceCalleeSaved s s0)
    (hnext : ∀ (pa1 : BitVec 64) (s1 : State),
      s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8756#64 → s1.status = .Running →
      (s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧ s1.readReg64 .x21 = u8 ∧
       s1.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length ∧ s1.readReg64 .x23 = u80 ∧
       s1.readReg64 .x24 = u88 ∧ s1.readReg64 .x25 = u56 ∧ s1.readReg64 .x26 = pa1 ∧
       s1.readReg64 .x27 = pbA ∧ s1.readReg64 .x28 = u64 ∧ s1.readReg64 .x9 = u96 ∧ TraceCalleeSaved s1 s0) →
      SepWPp (tripleRatchetProgAtExt b ext) target_pc s1
        (stackAt fsp encoderFromPbStack ∗ ((fsp + 232#64) ↦₆₄ u96) ∗ vecCapPtrDealloc A u56 u64 ∗
         vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗ A.pool ∗ Frame)
        post (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) target_pc s
      (stackAt fsp encoderFromPbStack ∗ ((fsp + 232#64) ↦₆₄ u96) ∗
       vecU8Payload A u56 u64 auth.rootKey ∗ A.pool ∗ Frame)
      post (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) :=
  v1_auth_from_pb_step1_1292_8756_sfa (.of_allocContracts hA) s0 s target_pc fsp out pbA
    u8 u56 u64 u80 u88 u96 auth Frame R post ha hpc hr hsp hx19 hx20 hx21 hx23 hx24 hx25 hx27 hx28 hx9 hu96 htr hnext

end CryptoVerification.SpqrV1.States.FromPb
