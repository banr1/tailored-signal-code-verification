/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2a
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-! # `<spqr::v1::chunked::states::States>::from_pb`: Variant 1 (`KeysSampled`) `PolyEncoder` Staging (`+4016..+6848`) -/

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

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  statesFromPb_fnOff

@[local simp, local arm64_norm, local wp_norm]
theorem v1d_bv_add_add_lit (x : BitVec 64) (a b : Nat) :
    x + BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  bv_omega

/-! ## `PolyEncoder` Cell Unpacking / Relocation (`fsp + 1888 -> out + 8`) -/

/-- Pack 8 bytes (little-endian) from `bs` into a `BitVec 64`. -/
def v1_pack64 (bs : List (BitVec 8)) : BitVec 64 :=
  (bs.getD 7 0#8) ++ (bs.getD 6 0#8) ++ (bs.getD 5 0#8) ++ (bs.getD 4 0#8) ++
  (bs.getD 3 0#8) ++ (bs.getD 2 0#8) ++ (bs.getD 1 0#8) ++ (bs.getD 0 0#8)

theorem v1_unpack64_pack64 (bs : List (BitVec 8)) (h : bs.length = 8) :
    unpack64 (v1_pack64 bs) = bs := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try (simp at h; done)
  change [_, _, _, _, _, _, _, _] = [b0, b1, b2, b3, b4, b5, b6, b7]
  dsimp only [v1_pack64, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
  simp only [List.cons.injEq, and_true]
  exact ⟨by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel,
         by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel⟩

theorem v1_pointsToBytes_eq_pack64 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 8) :
    (a ↦ₛ bs) = (a ↦₆₄ v1_pack64 bs) := by
  rw [pointsTo64_eq_pointsToBytes, v1_unpack64_pack64 bs h]

/-- Pack 16 bytes (little-endian) from `bs` into a `BitVec 128`. -/
def v1_pack128 (bs : List (BitVec 8)) : BitVec 128 :=
  v1_pack64 (bs.drop 8) ++ v1_pack64 (bs.take 8)

theorem v1_pointsToBytes_eq_pack128 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 16) :
    (a ↦ₛ bs) = (a ↦₁₂₈ v1_pack128 bs) := by
  have h1 : (bs.take 8).length = 8 := by simp [h]
  have h2 : (bs.drop 8).length = 8 := by simp [h]
  nth_rw 1 [← List.take_append_drop 8 bs]
  rw [ProofLib.pointsToBytes_append a (bs.take 8) (bs.drop 8), h1]
  change (a ↦ₛ bs.take 8) ∗ ((a + 8#64) ↦ₛ bs.drop 8) = (a ↦₁₂₈ v1_pack128 bs)
  rw [v1_pointsToBytes_eq_pack64 a (bs.take 8) h1,
      v1_pointsToBytes_eq_pack64 (a + 8#64) (bs.drop 8) h2,
      pointsTo64_pair_eq_pointsTo128]
  rfl

/-- 8-byte word at byte offset `i` within `bs`. -/
def v1_wordAt (bs : List (BitVec 8)) (i : Nat) : BitVec 64 :=
  v1_pack64 ((bs.drop i).take 8)

/-- 16-byte quadword at byte offset `i` within `bs`. -/
def v1_quadAt (bs : List (BitVec 8)) (i : Nat) : BitVec 128 :=
  v1_pack128 ((bs.drop i).take 16)

theorem v1_bs_drop_step8 {bs : List (BitVec 8)} (hbs : bs.length = 384)
    (a o1 o2 : BitVec 64) (i : Nat) {Q : SepProp}
    (hrest : ((a + o2) ↦ₛ bs.drop (i + 8)) = Q)
    (hi : i + 8 ≤ 384 := by decide)
    (ho : o1 + 8#64 = o2 := by rfl) :
    ((a + o1) ↦ₛ bs.drop i) = ((a + o1) ↦₆₄ v1_wordAt bs i) ∗ Q := by
  have htake_len : ((bs.drop i).take 8).length = 8 := by
    rw [List.length_take, List.length_drop, hbs]; omega
  have hsplit : bs.drop i = (bs.drop i).take 8 ++ bs.drop (i + 8) := by
    rw [← List.drop_drop, List.take_append_drop]
  have ha : (a + o1) + BitVec.ofNat 64 ((bs.drop i).take 8).length = a + o2 := by
    rw [htake_len, BitVec.add_assoc, ho]
  rw [hsplit, ProofLib.pointsToBytes_append (a + o1) ((bs.drop i).take 8) (bs.drop (i + 8)),
      ha, v1_pointsToBytes_eq_pack64 (a + o1) ((bs.drop i).take 8) htake_len, hrest]
  rfl

theorem v1_bs_drop_step16 {bs : List (BitVec 8)} (hbs : bs.length = 384)
    (a o1 o2 : BitVec 64) (i : Nat) {Q : SepProp}
    (hrest : ((a + o2) ↦ₛ bs.drop (i + 16)) = Q)
    (hi : i + 16 ≤ 384 := by decide)
    (ho : o1 + 16#64 = o2 := by rfl) :
    ((a + o1) ↦ₛ bs.drop i) = ((a + o1) ↦₁₂₈ v1_quadAt bs i) ∗ Q := by
  have htake_len : ((bs.drop i).take 16).length = 16 := by
    rw [List.length_take, List.length_drop, hbs]; omega
  have hsplit : bs.drop i = (bs.drop i).take 16 ++ bs.drop (i + 16) := by
    rw [← List.drop_drop, List.take_append_drop]
  have ha : (a + o1) + BitVec.ofNat 64 ((bs.drop i).take 16).length = a + o2 := by
    rw [htake_len, BitVec.add_assoc, ho]
  rw [hsplit, ProofLib.pointsToBytes_append (a + o1) ((bs.drop i).take 16) (bs.drop (i + 16)),
      ha, v1_pointsToBytes_eq_pack128 (a + o1) ((bs.drop i).take 16) htake_len, hrest]
  rfl

theorem v1_bs_drop_end8 {bs : List (BitVec 8)} (hbs : bs.length = 384)
    (a o1 : BitVec 64) :
    ((a + o1) ↦ₛ bs.drop 376) = ((a + o1) ↦₆₄ v1_wordAt bs 376) := by
  have hlen : (bs.drop 376).length = 8 := by rw [List.length_drop, hbs]
  have htake : (bs.drop 376).take 8 = bs.drop 376 := List.take_of_length_le (by omega)
  rw [v1_pointsToBytes_eq_pack64 (a + o1) (bs.drop 376) hlen]
  unfold v1_wordAt
  rw [htake]

/-- The 384-byte `PolyEncoder` vector-headers region at `a + 8..a + 392` decomposed into
the exact 64-bit and 128-bit cells accessed at `+6568..+6848` (for `a = fsp + 1888`) and
written by `epilogueOutFull` (for `a = out + 8`). -/
def v1_encCellsAt (a : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ((a + 8#64) ↦₆₄ v1_wordAt bs 0) ∗
  ((a + 16#64) ↦₆₄ v1_wordAt bs 8) ∗
  ((a + 24#64) ↦₆₄ v1_wordAt bs 16) ∗
  ((a + 32#64) ↦₆₄ v1_wordAt bs 24) ∗
  ((a + 40#64) ↦₆₄ v1_wordAt bs 32) ∗
  ((a + 48#64) ↦₆₄ v1_wordAt bs 40) ∗
  ((a + 56#64) ↦₆₄ v1_wordAt bs 48) ∗
  ((a + 64#64) ↦₆₄ v1_wordAt bs 56) ∗
  ((a + 72#64) ↦₆₄ v1_wordAt bs 64) ∗
  ((a + 80#64) ↦₆₄ v1_wordAt bs 72) ∗
  ((a + 88#64) ↦₆₄ v1_wordAt bs 80) ∗
  ((a + 96#64) ↦₆₄ v1_wordAt bs 88) ∗
  ((a + 104#64) ↦₆₄ v1_wordAt bs 96) ∗
  ((a + 112#64) ↦₆₄ v1_wordAt bs 104) ∗
  ((a + 120#64) ↦₆₄ v1_wordAt bs 112) ∗
  ((a + 128#64) ↦₆₄ v1_wordAt bs 120) ∗
  ((a + 136#64) ↦₆₄ v1_wordAt bs 128) ∗
  ((a + 144#64) ↦₆₄ v1_wordAt bs 136) ∗
  ((a + 152#64) ↦₆₄ v1_wordAt bs 144) ∗
  ((a + 160#64) ↦₁₂₈ v1_quadAt bs 152) ∗
  ((a + 176#64) ↦₁₂₈ v1_quadAt bs 168) ∗
  ((a + 192#64) ↦₁₂₈ v1_quadAt bs 184) ∗
  ((a + 208#64) ↦₁₂₈ v1_quadAt bs 200) ∗
  ((a + 224#64) ↦₁₂₈ v1_quadAt bs 216) ∗
  ((a + 240#64) ↦₁₂₈ v1_quadAt bs 232) ∗
  ((a + 256#64) ↦₁₂₈ v1_quadAt bs 248) ∗
  ((a + 272#64) ↦₁₂₈ v1_quadAt bs 264) ∗
  ((a + 288#64) ↦₁₂₈ v1_quadAt bs 280) ∗
  ((a + 304#64) ↦₁₂₈ v1_quadAt bs 296) ∗
  ((a + 320#64) ↦₁₂₈ v1_quadAt bs 312) ∗
  ((a + 336#64) ↦₁₂₈ v1_quadAt bs 328) ∗
  ((a + 352#64) ↦₁₂₈ v1_quadAt bs 344) ∗
  ((a + 368#64) ↦₁₂₈ v1_quadAt bs 360) ∗
  ((a + 384#64) ↦₆₄ v1_wordAt bs 376)

theorem v1_bs384_eq_encCells (bs : List (BitVec 8)) (hbs : bs.length = 384) (a : BitVec 64) :
    ((a + 8#64) ↦ₛ bs) = v1_encCellsAt a bs := by
  unfold v1_encCellsAt
  change ((a + 8#64) ↦ₛ bs.drop 0) = _
  exact
    v1_bs_drop_step8 hbs a 8#64 16#64 0 <| v1_bs_drop_step8 hbs a 16#64 24#64 8 <|
    v1_bs_drop_step8 hbs a 24#64 32#64 16 <| v1_bs_drop_step8 hbs a 32#64 40#64 24 <|
    v1_bs_drop_step8 hbs a 40#64 48#64 32 <| v1_bs_drop_step8 hbs a 48#64 56#64 40 <|
    v1_bs_drop_step8 hbs a 56#64 64#64 48 <| v1_bs_drop_step8 hbs a 64#64 72#64 56 <|
    v1_bs_drop_step8 hbs a 72#64 80#64 64 <| v1_bs_drop_step8 hbs a 80#64 88#64 72 <|
    v1_bs_drop_step8 hbs a 88#64 96#64 80 <| v1_bs_drop_step8 hbs a 96#64 104#64 88 <|
    v1_bs_drop_step8 hbs a 104#64 112#64 96 <| v1_bs_drop_step8 hbs a 112#64 120#64 104 <|
    v1_bs_drop_step8 hbs a 120#64 128#64 112 <| v1_bs_drop_step8 hbs a 128#64 136#64 120 <|
    v1_bs_drop_step8 hbs a 136#64 144#64 128 <| v1_bs_drop_step8 hbs a 144#64 152#64 136 <|
    v1_bs_drop_step8 hbs a 152#64 160#64 144 <| v1_bs_drop_step16 hbs a 160#64 176#64 152 <|
    v1_bs_drop_step16 hbs a 176#64 192#64 168 <| v1_bs_drop_step16 hbs a 192#64 208#64 184 <|
    v1_bs_drop_step16 hbs a 208#64 224#64 200 <| v1_bs_drop_step16 hbs a 224#64 240#64 216 <|
    v1_bs_drop_step16 hbs a 240#64 256#64 232 <| v1_bs_drop_step16 hbs a 256#64 272#64 248 <|
    v1_bs_drop_step16 hbs a 272#64 288#64 264 <| v1_bs_drop_step16 hbs a 288#64 304#64 280 <|
    v1_bs_drop_step16 hbs a 304#64 320#64 296 <| v1_bs_drop_step16 hbs a 320#64 336#64 312 <|
    v1_bs_drop_step16 hbs a 336#64 352#64 328 <| v1_bs_drop_step16 hbs a 352#64 368#64 344 <|
    v1_bs_drop_step16 hbs a 368#64 384#64 360 <| v1_bs_drop_end8 hbs a 384#64

theorem v1_pointsTo32_pair_eq_pointsTo64 (a : BitVec 64) (lo hi : BitVec 32) :
    ((a ↦₃₂ lo) ∗ ((a + 4#64) ↦₃₂ hi)) = (a ↦₆₄ (hi ++ lo)) := by
  rw [pointsTo64_eq_pointsToBytes, pointsTo32_eq_pointsToBytes, pointsTo32_eq_pointsToBytes]
  change (a ↦ₛ unpack32 lo) ∗ ((a + BitVec.ofNat 64 (unpack32 lo).length) ↦ₛ unpack32 hi) = _
  rw [← ProofLib.pointsToBytes_append a (unpack32 lo) (unpack32 hi)]
  congr 1
  unfold unpack64 unpack32
  simp only [List.singleton_append, List.cons_append, List.nil_append, List.cons.injEq, and_true]
  exact ⟨by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel,
         by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel⟩

theorem v1_polyEncoderAt_relocate (A : RustAlloc) (a1 a2 : BitVec 64) (enc : PolyEncoder) :
    polyEncoderAt A a1 enc ⊢
      ∃∗ tag : BitVec 64, ∃∗ bs : { l : List (BitVec 8) // l.length = 384 },
      ∃∗ hi32 : BitVec 32, ∃∗ P_heap : SepProp,
        ⌜(tag = 0#64 ∨ tag = 1#64) ∧
          ((a2 ↦₆₄ tag) ∗ ((a2 + 8#64) ↦ₛ bs.val) ∗
           ((a2 + 392#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ P_heap ⊢
            polyEncoderAt A a2 enc)⌝ ∗
        (a1 ↦₆₄ tag) ∗
        ((a1 + 8#64) ↦ₛ bs.val) ∗
        ((a1 + 392#64) ↦₆₄ (hi32 ++ enc.idx)) ∗
        P_heap := by
  unfold polyEncoderAt encoderStateAt polyEncoderPointsTag polyEncoderPolysTag
    polyEncoderVecsOff polyEncoderIdxOff polyEncoderPadOff polyEncoderPadSize
  rw [ProofLib.memRegion_four (a1 + 396#64)]
  cases hs : enc.s with
  | points pts =>
    dsimp only
    rw [pointListOf_eq_vecGF16ListOf A pts (a1 + 8#64)]
    refine Entails.trans
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
        (vecGF16ListOf_entails_headers_heaps A (pts.map Point.value) (a1 + 8#64))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro hi32
    apply Entails.sepExists_elim; intro pins
    apply Entails.pure_left; rintro ⟨hpts_len, hpts_bound⟩
    rw [sepConj_pure_left_comm]
    apply Entails.pure_left; intro hpins_len
    have hbs_len : (vecHeadersBytesOf pins (pts.map Point.value)).length = 384 := by
      rw [length_vecHeadersBytesOf pins (pts.map Point.value) hpins_len, List.length_map, hpts_len]
      rfl
    have ha1_396 : a1 + 396#64 = (a1 + 392#64) + 4#64 := by bv_omega
    rw [ha1_396, v1_pointsTo32_pair_eq_pointsTo64 (a1 + 392#64) enc.idx hi32]
    refine Entails.sepExists_right 0#64
      (Entails.sepExists_right ⟨vecHeadersBytesOf pins (pts.map Point.value), hbs_len⟩
        (Entails.sepExists_right hi32
          (Entails.sepExists_right (vecGF16HeapList A pins (pts.map Point.value)) ?_)))
    refine Entails.pure_right ⟨Or.inl rfl, ?_⟩ (Entails.of_eq (by ac_rfl))
    rw [pointListOf_eq_vecGF16ListOf A pts (a2 + 8#64),
        ← v1_pointsTo32_pair_eq_pointsTo64 (a2 + 392#64) enc.idx hi32]
    have ha2_396 : (a2 + 392#64) + 4#64 = a2 + 396#64 := by bv_omega
    rw [ha2_396]
    have hvec2 := headers_heaps_entails_vecGF16ListOf A pins (pts.map Point.value) (a2 + 8#64) hpins_len
    have hm4 : ((a2 + 396#64) ↦₃₂ hi32) ⊢ memRegion (a2 + 396#64) 4 := by
      rw [ProofLib.memRegion_four (a2 + 396#64)]
      exact Entails.sepExists_right hi32 (Entails.refl _)
    refine Entails.trans (Entails.of_eq (show _ =
      (a2 ↦₆₄ 0#64) ∗
      (((a2 + 8#64) ↦ₛ vecHeadersBytesOf pins (pts.map Point.value)) ∗
       vecGF16HeapList A pins (pts.map Point.value)) ∗
      ((a2 + 392#64) ↦₃₂ enc.idx) ∗
      ((a2 + 396#64) ↦₃₂ hi32) by ac_rfl)) ?_
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono hvec2 (sepConj_mono_right hm4))) ?_
    exact Entails.pure_right ⟨hpts_len, hpts_bound⟩ (Entails.of_eq (by ac_rfl))
  | polys ps =>
    dsimp only
    rw [polyListOf_eq_vecGF16ListOf A ps (a1 + 8#64)]
    refine Entails.trans
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
        (vecGF16ListOf_entails_headers_heaps A (ps.map LibsignalSpqrV1.Poly.coefficients) (a1 + 8#64))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro hi32
    apply Entails.sepExists_elim; intro pins
    apply Entails.pure_left; intro hps_len
    rw [sepConj_pure_left_comm]
    apply Entails.pure_left; intro hpins_len
    have hbs_len : (vecHeadersBytesOf pins (ps.map LibsignalSpqrV1.Poly.coefficients)).length = 384 := by
      rw [length_vecHeadersBytesOf pins (ps.map LibsignalSpqrV1.Poly.coefficients) hpins_len, List.length_map, hps_len]
      rfl
    have ha1_396 : a1 + 396#64 = (a1 + 392#64) + 4#64 := by bv_omega
    rw [ha1_396, v1_pointsTo32_pair_eq_pointsTo64 (a1 + 392#64) enc.idx hi32]
    refine Entails.sepExists_right 1#64
      (Entails.sepExists_right ⟨vecHeadersBytesOf pins (ps.map LibsignalSpqrV1.Poly.coefficients), hbs_len⟩
        (Entails.sepExists_right hi32
          (Entails.sepExists_right (vecGF16HeapList A pins (ps.map LibsignalSpqrV1.Poly.coefficients)) ?_)))
    refine Entails.pure_right ⟨Or.inr rfl, ?_⟩ (Entails.of_eq (by ac_rfl))
    rw [polyListOf_eq_vecGF16ListOf A ps (a2 + 8#64),
        ← v1_pointsTo32_pair_eq_pointsTo64 (a2 + 392#64) enc.idx hi32]
    have ha2_396 : (a2 + 392#64) + 4#64 = a2 + 396#64 := by bv_omega
    rw [ha2_396]
    have hvec2 := headers_heaps_entails_vecGF16ListOf A pins (ps.map LibsignalSpqrV1.Poly.coefficients) (a2 + 8#64) hpins_len
    have hm4 : ((a2 + 396#64) ↦₃₂ hi32) ⊢ memRegion (a2 + 396#64) 4 := by
      rw [ProofLib.memRegion_four (a2 + 396#64)]
      exact Entails.sepExists_right hi32 (Entails.refl _)
    refine Entails.trans (Entails.of_eq (show _ =
      (a2 ↦₆₄ 1#64) ∗
      (((a2 + 8#64) ↦ₛ vecHeadersBytesOf pins (ps.map LibsignalSpqrV1.Poly.coefficients)) ∗
       vecGF16HeapList A pins (ps.map LibsignalSpqrV1.Poly.coefficients)) ∗
      ((a2 + 392#64) ↦₃₂ enc.idx) ∗
      ((a2 + 396#64) ↦₃₂ hi32) by ac_rfl)) ?_
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono hvec2 (sepConj_mono_right hm4))) ?_
    exact Entails.pure_right hps_len (Entails.of_eq (by ac_rfl))

/-- The 128-bit quadword loaded from `fsp + 2025` (`x11 + 137`) and stored to `fsp + 848`. -/
def v1_midQ128 (w128 w136 w144 : BitVec 64) : BitVec 128 :=
  unshiftWord w136 (loByte w144) ++ unshiftWord w128 (loByte w136)

theorem v1_hiBytes7_eq_loBytes7_lsr8 (w : BitVec 64) :
    EncoderFromPb.hiBytes7 w = EncoderFromPb.loBytes7 (w >>> 8) := by
  change [_, _, _, _, _, _, _] = [_, _, _, _, _, _, _]
  refine congrArg (_ :: ·) (congrArg (_ :: ·) (congrArg (_ :: ·)
    (congrArg (_ :: ·) (congrArg (_ :: ·) (congrArg (_ :: ·) (congrArg (· :: []) ?_))))))
  all_goals bv_kernel

theorem v1_lsr8_lsl8 (v : BitVec 64) :
    (v >>> 8) <<< 8 = v &&& 0xffffffffffffff00#64 := by
  bv_kernel

theorem v1_unshift_lsr56 (w0 v : BitVec 64) :
    (unshiftWord w0 (loByte v)) >>> 56 = v &&& 0xff#64 := by
  unfold unshiftWord loByte
  bv_kernel

theorem v1_overlapWord7_unshift_lsr8 (w0 w8 : BitVec 64) :
    overlapWord7 (unshiftWord w0 (loByte w8)) (w8 >>> 8) = w8 := by
  unfold overlapWord7
  rw [v1_unshift_lsr56 w0 w8, v1_lsr8_lsl8 w8]
  bv_kernel

theorem v1_overlapWord7_midQ128_lsr8 (w128 w136 w144 : BitVec 64) :
    overlapWord7 ((v1_midQ128 w128 w136 w144).extractLsb' 64 64) (w144 >>> 8) = w144 := by
  have hhi : (v1_midQ128 w128 w136 w144).extractLsb' 64 64 = unshiftWord w136 (loByte w144) := by
    unfold v1_midQ128
    bv_kernel
  rw [hhi]
  exact v1_overlapWord7_unshift_lsr8 w136 w144

theorem v1_fsp_1888_entails_epilogue (fsp tag w2280 : BitVec 64)
    (bs : List (BitVec 8)) (hbs : bs.length = 384) :
    ((fsp + 1888#64) ↦₆₄ tag) ∗
      v1_encCellsAt (fsp + 1888#64) bs ∗
      ((fsp + 2280#64) ↦₆₄ w2280) ∗
      memRegion (fsp + 2288#64) 16 ⊢
    ((fsp + 1888#64) ↦₁₂₈ (v1_wordAt bs 0 ++ tag)) ∗
      ((fsp + 1904#64) ↦₁₂₈ (v1_wordAt bs 16 ++ v1_wordAt bs 8)) ∗
      ((fsp + 1920#64) ↦₆₄ v1_wordAt bs 24) ∗
      memRegion (fsp + 1928#64) 376 := by
  rw [← v1_bs384_eq_encCells bs hbs (fsp + 1888#64)]
  have ha1896 : (fsp + 1888#64) + 8#64 = fsp + 1896#64 := by bv_omega
  rw [ha1896]
  have hbs_split : ((fsp + 1896#64) ↦ₛ bs) =
      ((fsp + 1896#64) ↦₆₄ v1_wordAt bs 0) ∗
      ((fsp + 1904#64) ↦₆₄ v1_wordAt bs 8) ∗
      ((fsp + 1912#64) ↦₆₄ v1_wordAt bs 16) ∗
      ((fsp + 1920#64) ↦₆₄ v1_wordAt bs 24) ∗
      ((fsp + 1928#64) ↦ₛ bs.drop 32) := by
    have h :=
      v1_bs_drop_step8 hbs (fsp + 1888#64) 8#64 16#64 0 <|
      v1_bs_drop_step8 hbs (fsp + 1888#64) 16#64 24#64 8 <|
      v1_bs_drop_step8 hbs (fsp + 1888#64) 24#64 32#64 16 <|
      v1_bs_drop_step8 hbs (fsp + 1888#64) 32#64 40#64 24 rfl
    change (((fsp + 1888#64) + 8#64) ↦ₛ bs) = _ at h
    simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd, sepConj_assoc] at h
    exact h
  rw [hbs_split]
  have hq1888 : ((fsp + 1888#64) ↦₆₄ tag) ∗ ((fsp + 1896#64) ↦₆₄ v1_wordAt bs 0) =
      ((fsp + 1888#64) ↦₁₂₈ (v1_wordAt bs 0 ++ tag)) := by
    rw [← ha1896, pointsTo64_pair_eq_pointsTo128]
  have hq1904 : ((fsp + 1904#64) ↦₆₄ v1_wordAt bs 8) ∗ ((fsp + 1912#64) ↦₆₄ v1_wordAt bs 16) =
      ((fsp + 1904#64) ↦₁₂₈ (v1_wordAt bs 16 ++ v1_wordAt bs 8)) := by
    have ha : (fsp + 1904#64) + 8#64 = fsp + 1912#64 := by bv_omega
    rw [← ha, pointsTo64_pair_eq_pointsTo128]
  have hlen352 : (bs.drop 32).length = 352 := by rw [List.length_drop, hbs]
  have hm352 : ((fsp + 1928#64) ↦ₛ bs.drop 32) ⊢ memRegion (fsp + 1928#64) 352 :=
    hlen352 ▸ ProofLib.pointsToBytes_entails_memRegion (fsp + 1928#64) (bs.drop 32)
  have hm376 : ((fsp + 1928#64) ↦ₛ bs.drop 32) ∗
      ((fsp + 2280#64) ↦₆₄ w2280) ∗ memRegion (fsp + 2288#64) 16 ⊢
      memRegion (fsp + 1928#64) 376 := by
    rw [ProofLib.memRegion_split' (b := fsp + 1928#64) (n := 352) (k := 24)
          (b' := fsp + 2280#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 2280#64) (n := 8) (k := 16)
          (b' := fsp + 2288#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono hm352
      (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (fsp + 2280#64) w2280))
  refine Entails.trans (Entails.of_eq (show _ =
    (((fsp + 1888#64) ↦₆₄ tag) ∗ ((fsp + 1896#64) ↦₆₄ v1_wordAt bs 0)) ∗
    (((fsp + 1904#64) ↦₆₄ v1_wordAt bs 8) ∗ ((fsp + 1912#64) ↦₆₄ v1_wordAt bs 16)) ∗
    ((fsp + 1920#64) ↦₆₄ v1_wordAt bs 24) ∗
    (((fsp + 1928#64) ↦ₛ bs.drop 32) ∗ ((fsp + 2280#64) ↦₆₄ w2280) ∗ memRegion (fsp + 2288#64) 16) by ac_rfl)) ?_
  rw [hq1888, hq1904]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hm376))

theorem v1_triple64_eq_byte_q128_tail7 (a w0 w8 w16 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) =
      (a ↦₈ loByte w0) ∗
      ((a + 1#64) ↦₁₂₈ (unshiftWord w8 (loByte w16) ++ unshiftWord w0 (loByte w8))) ∗
      ((a + 17#64) ↦ₛ EncoderFromPb.hiBytes7 w16) := by
  have h2 := pair64_to_byte_word_tail7 (a + 8#64) w8 w16
  have ha16 : (a + 8#64) + 8#64 = a + 16#64 := by bv_omega
  have ha9 : (a + 8#64) + 1#64 = a + 9#64 := by bv_omega
  have ha17 : (a + 8#64) + 9#64 = a + 17#64 := by bv_omega
  rw [ha16, ha9, ha17] at h2
  have h1b :
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₈ loByte w8) =
        (a ↦₈ loByte w0) ∗ ((a + 1#64) ↦₆₄ unshiftWord w0 (loByte w8)) := by
    rw [pointsTo64_eq_pointsToBytes a w0, pointsTo64_eq_pointsToBytes (a + 1#64),
        ← ProofLib.pointsToBytes_cons, loByte_cons_unpack64_unshiftWord w0 (loByte w8),
        ProofLib.pointsToBytes_append a (unpack64 w0) [loByte w8], unpack64_length]
    simp only [ProofLib.pointsToBytes_cons, ProofLib.pointsToBytes_nil, sepConj_emp]
  have hq := pointsTo64_pair_eq_pointsTo128 (a + 1#64)
    (unshiftWord w0 (loByte w8)) (unshiftWord w8 (loByte w16))
  have ha1_8 : (a + 1#64) + 8#64 = a + 9#64 := by bv_omega
  rw [ha1_8] at hq
  rw [h2, ← sepConj_assoc, ← sepConj_assoc, h1b,
      sepConj_assoc (a ↦₈ loByte w0), sepConj_assoc, hq]

theorem v1_right64_eq_unshift_hiBytes7 (p ptr len : BitVec 64) :
    (p ↦ₛ EncoderFromPb.loBytes7 (unshiftWord ptr (loByte len))) ∗ ((p + 7#64) ↦₆₄ len) =
      (p ↦₆₄ unshiftWord ptr (loByte len)) ∗ ((p + 8#64) ↦ₛ EncoderFromPb.hiBytes7 len) := by
  rw [pointsTo64_eq_pointsToBytes (p + 7#64) len]
  have h7 : p + BitVec.ofNat 64 (EncoderFromPb.loBytes7 (unshiftWord ptr (loByte len))).length = p + 7#64 := by
    rw [length_loBytes7]
  rw [← h7, ← ProofLib.pointsToBytes_append p (EncoderFromPb.loBytes7 (unshiftWord ptr (loByte len))) (unpack64 len),
      loBytes7_unshiftWord_append_unpack64 ptr len,
      ProofLib.pointsToBytes_append p (unpack64 (unshiftWord ptr (loByte len))) (EncoderFromPb.hiBytes7 len),
      unpack64_length, ← pointsTo64_eq_pointsToBytes p (unshiftWord ptr (loByte len))]

theorem v1_dst24_realign_final (a w0 w8 w16 : BitVec 64) :
    (a ↦₈ loByte w0) ∗
      ((a + 1#64) ↦₆₄ unshiftWord w0 (loByte w8)) ∗
      ((a + 9#64) ↦ₛ EncoderFromPb.loBytes7 (unshiftWord w8 (loByte w16))) ∗
      ((a + 16#64) ↦₆₄ w16) =
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) := by
  have hr := v1_right64_eq_unshift_hiBytes7 (a + 9#64) w8 w16
  have ha16 : (a + 9#64) + 7#64 = a + 16#64 := by bv_omega
  have ha17 : (a + 9#64) + 8#64 = a + 17#64 := by bv_omega
  rw [ha16, ha17] at hr
  have hq := pointsTo64_pair_eq_pointsTo128 (a + 1#64)
    (unshiftWord w0 (loByte w8)) (unshiftWord w8 (loByte w16))
  have ha9 : (a + 1#64) + 8#64 = a + 9#64 := by bv_omega
  rw [ha9] at hq
  rw [hr, ← sepConj_assoc ((a + 1#64) ↦₆₄ _), hq,
      ← v1_triple64_eq_byte_q128_tail7 a w0 w8 w16]

@[local arm64_norm, local wp_norm]
theorem v1_orr_x27_w80 (w80 : BitVec 64) :
    ((w80.extractLsb' 8 32).zeroExtend 64 |||
      ((((w80.extractLsb' 40 16).zeroExtend 32 |||
        ((w80.extractLsb' 56 8).zeroExtend 32 <<< 16#64)).zeroExtend 64) <<< 32#64)) =
      (w80.extractLsb' 8 56).zeroExtend 64 := by
  bv_kernel

@[local arm64_norm, local wp_norm]
theorem v1_w80_d97 (w80 : BitVec 64) :
    ((w80.extractLsb' 8 56).zeroExtend 64).setWidth 32 = w80.extractLsb' 8 32 := by
  bv_kernel

@[local arm64_norm, local wp_norm]
theorem v1_w80_h101 (w80 : BitVec 64) :
    ((((w80.extractLsb' 8 56).zeroExtend 64) >>> 32).setWidth 32).setWidth 16 =
      w80.extractLsb' 40 16 := by
  bv_kernel

@[local arm64_norm, local wp_norm]
theorem v1_w80_b103 (w80 : BitVec 64) :
    ((((w80.extractLsb' 8 56).zeroExtend 64) >>> 48).setWidth 32).setWidth 8 =
      w80.extractLsb' 56 8 := by
  bv_kernel

@[local arm64_norm, local wp_norm]
theorem v1_zext32_setWidth8 (b : BitVec 8) :
    (b.zeroExtend 32).setWidth 8 = b := by
  bv_kernel

@[local arm64_norm, local wp_norm]
theorem v1_fsp_1888_add_89 (fsp : BitVec 64) :
    (fsp + 1888#64) + 89#64 = fsp + 1977#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem v1_fsp_1888_add_93 (fsp : BitVec 64) :
    (fsp + 1888#64) + 93#64 = fsp + 1981#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem v1_fsp_1888_add_113 (fsp : BitVec 64) :
    (fsp + 1888#64) + 113#64 = fsp + 2001#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem v1_fsp_1888_add_137 (fsp : BitVec 64) :
    (fsp + 1888#64) + 137#64 = fsp + 2025#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem v1_fsp_848_add_39 (fsp : BitVec 64) :
    (fsp + 848#64) + 39#64 = fsp + 887#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem v1_fsp_848_add_15 (fsp : BitVec 64) :
    (fsp + 848#64) + 15#64 = fsp + 863#64 := by bv_omega

theorem v1_pointsTo64_split_1_4_2_1 (a w : BitVec 64) :
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

theorem v1_fsp_1976_split_rest (fsp w80 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1976#64) ↦₆₄ w80) ∗ Rest =
      ((fsp + 1976#64) ↦₈ w80.extractLsb' 0 8) ∗
      ((fsp + 1977#64) ↦₃₂ w80.extractLsb' 8 32) ∗
      ((fsp + 1981#64) ↦₁₆ w80.extractLsb' 40 16) ∗
      ((fsp + 1983#64) ↦₈ w80.extractLsb' 56 8) ∗ Rest := by
  have h := v1_pointsTo64_split_1_4_2_1 (fsp + 1976#64) w80
  have ha1 : (fsp + 1976#64) + 1#64 = fsp + 1977#64 := by bv_omega
  have ha5 : (fsp + 1976#64) + 5#64 = fsp + 1981#64 := by bv_omega
  have ha7 : (fsp + 1976#64) + 7#64 = fsp + 1983#64 := by bv_omega
  rw [ha1, ha5, ha7] at h
  have h' := congrArg (· ∗ Rest) h
  exact Eq.trans (by ac_rfl) (Eq.trans h' (by ac_rfl))

theorem v1_fsp_1976_unsplit_rest (fsp w80 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1976#64) ↦₈ w80.extractLsb' 0 8) ∗
      ((fsp + 1977#64) ↦₃₂ w80.extractLsb' 8 32) ∗
      ((fsp + 1981#64) ↦₁₆ w80.extractLsb' 40 16) ∗
      ((fsp + 1983#64) ↦₈ w80.extractLsb' 56 8) ∗ Rest =
      ((fsp + 1976#64) ↦₆₄ w80) ∗ Rest :=
  (v1_fsp_1976_split_rest fsp w80 Rest).symm

theorem v1_fsp_2024_realign_rest (fsp w128 w136 w144 : BitVec 64) (Rest : SepProp) :
    ((fsp + 2024#64) ↦₆₄ w128) ∗ ((fsp + 2032#64) ↦₆₄ w136) ∗ ((fsp + 2040#64) ↦₆₄ w144) ∗ Rest =
      ((fsp + 2024#64) ↦₈ loByte w128) ∗
      ((fsp + 2025#64) ↦₆₄ (v1_midQ128 w128 w136 w144).extractLsb' 0 64) ∗
      ((fsp + 2033#64) ↦₆₄ (v1_midQ128 w128 w136 w144).extractLsb' 64 64) ∗
      ((fsp + 2041#64) ↦ₛ EncoderFromPb.hiBytes7 w144) ∗ Rest := by
  have h := v1_triple64_eq_byte_q128_tail7 (fsp + 2024#64) w128 w136 w144
  have ha8 : (fsp + 2024#64) + 8#64 = fsp + 2032#64 := by bv_omega
  have ha16 : (fsp + 2024#64) + 16#64 = fsp + 2040#64 := by bv_omega
  have ha1 : (fsp + 2024#64) + 1#64 = fsp + 2025#64 := by bv_omega
  have ha17 : (fsp + 2024#64) + 17#64 = fsp + 2041#64 := by bv_omega
  have ha2033 : (fsp + 2025#64) + 8#64 = fsp + 2033#64 := by bv_omega
  rw [ha8, ha16, ha1, ha17] at h
  change _ = ((fsp + 2024#64) ↦₈ loByte w128) ∗
    ((fsp + 2025#64) ↦₁₂₈ v1_midQ128 w128 w136 w144) ∗
    ((fsp + 2041#64) ↦ₛ EncoderFromPb.hiBytes7 w144) at h
  unfold pointsTo128 at h
  rw [ha2033] at h
  have h' := congrArg (· ∗ Rest) h
  exact Eq.trans (by ac_rfl) (Eq.trans h' (by ac_rfl))

theorem v1_fsp_2024_unrealign_rest (fsp w128 w136 w144 : BitVec 64) (Rest : SepProp) :
    ((fsp + 2024#64) ↦₈ loByte w128) ∗
      ((fsp + 2025#64) ↦₆₄ (v1_midQ128 w128 w136 w144).extractLsb' 0 64) ∗
      ((fsp + 2033#64) ↦₆₄ (v1_midQ128 w128 w136 w144).extractLsb' 64 64) ∗
      ((fsp + 2041#64) ↦ₛ EncoderFromPb.hiBytes7 w144) ∗ Rest =
    ((fsp + 2024#64) ↦₆₄ w128) ∗ ((fsp + 2032#64) ↦₆₄ w136) ∗ ((fsp + 2040#64) ↦₆₄ w144) ∗ Rest :=
  (v1_fsp_2024_realign_rest fsp w128 w136 w144 Rest).symm

theorem v1_fsp_2024_split_1_7_rest (fsp w128 : BitVec 64) (Rest : SepProp) :
    ((fsp + 2024#64) ↦₆₄ w128) ∗ Rest =
      ((fsp + 2024#64) ↦₈ loByte w128) ∗
      ((fsp + 2025#64) ↦ₛ EncoderFromPb.hiBytes7 w128) ∗ Rest := by
  have h := pointsTo64_split_1_7 (fsp + 2024#64) w128
  have ha1 : (fsp + 2024#64) + 1#64 = fsp + 2025#64 := by bv_omega
  rw [ha1] at h
  rw [← sepConj_assoc, h, sepConj_assoc]

theorem v1_fsp_2024_unsplit_1_7_rest (fsp w128 : BitVec 64) (Rest : SepProp) :
    ((fsp + 2024#64) ↦₈ loByte w128) ∗
      ((fsp + 2025#64) ↦ₛ EncoderFromPb.hiBytes7 w128) ∗ Rest =
      ((fsp + 2024#64) ↦₆₄ w128) ∗ Rest :=
  (v1_fsp_2024_split_1_7_rest fsp w128 Rest).symm

theorem v1_fsp_2000_realign_rest (fsp w104 w112 : BitVec 64) (Rest : SepProp) :
    ((fsp + 2000#64) ↦₆₄ w104) ∗ ((fsp + 2008#64) ↦₆₄ w112) ∗ Rest =
      ((fsp + 2000#64) ↦₈ loByte w104) ∗
      ((fsp + 2001#64) ↦₆₄ unshiftWord w104 (loByte w112)) ∗
      ((fsp + 2009#64) ↦ₛ EncoderFromPb.hiBytes7 w112) ∗ Rest := by
  have h := pair64_to_byte_word_tail7 (fsp + 2000#64) w104 w112
  have ha8 : (fsp + 2000#64) + 8#64 = fsp + 2008#64 := by bv_omega
  have ha1 : (fsp + 2000#64) + 1#64 = fsp + 2001#64 := by bv_omega
  have ha9 : (fsp + 2000#64) + 9#64 = fsp + 2009#64 := by bv_omega
  rw [ha8, ha1, ha9] at h
  have h' := congrArg (· ∗ Rest) h
  exact Eq.trans (by ac_rfl) (Eq.trans h' (by ac_rfl))

theorem v1_fsp_2000_unrealign_rest (fsp w104 w112 : BitVec 64) (Rest : SepProp) :
    ((fsp + 2000#64) ↦₈ loByte w104) ∗
      ((fsp + 2001#64) ↦₆₄ unshiftWord w104 (loByte w112)) ∗
      ((fsp + 2009#64) ↦ₛ EncoderFromPb.hiBytes7 w112) ∗ Rest =
      ((fsp + 2000#64) ↦₆₄ w104) ∗ ((fsp + 2008#64) ↦₆₄ w112) ∗ Rest :=
  (v1_fsp_2000_realign_rest fsp w104 w112 Rest).symm

theorem v1_fsp_880_realign_rest (fsp u880 w112 : BitVec 64) (Rest : SepProp) :
    ((fsp + 880#64) ↦ₛ EncoderFromPb.loBytes7 u880) ∗ ((fsp + 887#64) ↦₆₄ w112) ∗ Rest =
      ((fsp + 880#64) ↦₆₄ overlapLow7 u880 w112) ∗
      ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 (w112 >>> 8)) ∗ Rest := by
  have h := loBytes7_pointsTo64_eq_overlap (fsp + 880#64) u880 w112
  have ha7 : (fsp + 880#64) + 7#64 = fsp + 887#64 := by bv_omega
  have ha8 : (fsp + 880#64) + 8#64 = fsp + 888#64 := by bv_omega
  rw [ha7, ha8, v1_hiBytes7_eq_loBytes7_lsr8 w112] at h
  rw [← sepConj_assoc, h, sepConj_assoc]

theorem v1_fsp_856_realign_rest (fsp w856 u864 : BitVec 64) (Rest : SepProp) :
    ((fsp + 856#64) ↦₆₄ w856) ∗ ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 u864) ∗ Rest =
      ((fsp + 856#64) ↦ₛ EncoderFromPb.loBytes7 w856) ∗
      ((fsp + 863#64) ↦₆₄ overlapWord7 w856 u864) ∗ Rest := by
  have h := pointsTo64_loBytes7_eq_loBytes7_overlapWord7 (fsp + 856#64) w856 u864
  have ha8 : (fsp + 856#64) + 8#64 = fsp + 864#64 := by bv_omega
  have ha7 : (fsp + 856#64) + 7#64 = fsp + 863#64 := by bv_omega
  rw [ha8, ha7] at h
  rw [← sepConj_assoc, h, sepConj_assoc]

theorem v1_fsp_856_unrealign_midQ128_rest (fsp w128 w136 w144 : BitVec 64) (Rest : SepProp) :
    ((fsp + 856#64) ↦ₛ EncoderFromPb.loBytes7 ((v1_midQ128 w128 w136 w144).extractLsb' 64 64)) ∗
      ((fsp + 863#64) ↦₆₄ w144) ∗ Rest =
    ((fsp + 856#64) ↦₆₄ (v1_midQ128 w128 w136 w144).extractLsb' 64 64) ∗
      ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 (w144 >>> 8)) ∗ Rest := by
  have h := (v1_fsp_856_realign_rest fsp ((v1_midQ128 w128 w136 w144).extractLsb' 64 64)
    (w144 >>> 8) Rest).symm
  rwa [v1_overlapWord7_midQ128_lsr8 w128 w136 w144] at h

theorem v1_out_96_realign (out w80 : BitVec 64) :
    ((out + 96#64) ↦₈ w80.extractLsb' 0 8) ∗
      ((out + 97#64) ↦₃₂ w80.extractLsb' 8 32) ∗
      ((out + 101#64) ↦₁₆ w80.extractLsb' 40 16) ∗
      ((out + 103#64) ↦₈ w80.extractLsb' 56 8) =
    (out + 96#64) ↦₆₄ w80 := by
  have h := (v1_pointsTo64_split_1_4_2_1 (out + 96#64) w80).symm
  have ha97 : (out + 96#64) + 1#64 = out + 97#64 := by bv_omega
  have ha101 : (out + 96#64) + 5#64 = out + 101#64 := by bv_omega
  have ha103 : (out + 96#64) + 7#64 = out + 103#64 := by bv_omega
  rw [ha97, ha101, ha103] at h
  exact h

theorem v1_out_120_realign (out w104 w112 : BitVec 64) :
    ((out + 120#64) ↦₈ loByte w104) ∗
      ((out + 121#64) ↦₆₄ unshiftWord w104 (loByte w112)) ∗
      ((out + 129#64) ↦ₛ EncoderFromPb.hiBytes7
        (overlapWord7 (unshiftWord w104 (loByte w112)) (w112 >>> 8))) =
    ((out + 120#64) ↦₆₄ w104) ∗ ((out + 128#64) ↦₆₄ w112) := by
  rw [v1_overlapWord7_unshift_lsr8 w104 w112]
  have h := (pair64_to_byte_word_tail7 (out + 120#64) w104 w112).symm
  have ha121 : (out + 120#64) + 1#64 = out + 121#64 := by bv_omega
  have ha129 : (out + 120#64) + 9#64 = out + 129#64 := by bv_omega
  have ha128 : (out + 120#64) + 8#64 = out + 128#64 := by bv_omega
  rw [ha121, ha129, ha128] at h
  exact h

theorem v1_out_144_realign (out w128 w136 w144 : BitVec 64) :
    ((out + 144#64) ↦₈ ((loByte w128).zeroExtend 32).setWidth 8) ∗
      ((out + 145#64) ↦₆₄ (v1_midQ128 w128 w136 w144).extractLsb' 0 64) ∗
      ((out + 153#64) ↦ₛ EncoderFromPb.loBytes7 ((v1_midQ128 w128 w136 w144).extractLsb' 64 64)) ∗
      ((out + 160#64) ↦₆₄
        overlapWord7 ((v1_midQ128 w128 w136 w144).extractLsb' 64 64) (w144 >>> 8)) =
    ((out + 144#64) ↦₆₄ w128) ∗ ((out + 152#64) ↦₆₄ w136) ∗ ((out + 160#64) ↦₆₄ w144) := by
  rw [v1_zext32_setWidth8 (loByte w128)]
  have hlo : (v1_midQ128 w128 w136 w144).extractLsb' 0 64 = unshiftWord w128 (loByte w136) := by
    unfold v1_midQ128; bv_kernel
  have hhi : (v1_midQ128 w128 w136 w144).extractLsb' 64 64 = unshiftWord w136 (loByte w144) := by
    unfold v1_midQ128; bv_kernel
  rw [hlo, hhi, v1_overlapWord7_unshift_lsr8 w136 w144]
  have hdst := v1_dst24_realign_final (out + 144#64) w128 w136 w144
  have hd145 : (out + 144#64) + 1#64 = out + 145#64 := by bv_omega
  have hd153 : (out + 144#64) + 9#64 = out + 153#64 := by bv_omega
  have hd160 : (out + 144#64) + 16#64 = out + 160#64 := by bv_omega
  have hd152 : (out + 144#64) + 8#64 = out + 152#64 := by bv_omega
  rw [hd145, hd153, hd160, hd152] at hdst
  exact hdst

theorem v1_out_16_to_400_eq_bs (out : BitVec 64) (bs : List (BitVec 8)) (hbs : bs.length = 384) :
    ((out + 16#64) ↦₆₄ v1_wordAt bs 0) ∗
      ((out + 24#64) ↦₆₄ v1_wordAt bs 8) ∗
      ((out + 32#64) ↦₆₄ v1_wordAt bs 16) ∗
      ((out + 40#64) ↦₆₄ v1_wordAt bs 24) ∗
      ((out + 48#64) ↦₆₄ v1_wordAt bs 32) ∗
      ((out + 56#64) ↦₆₄ v1_wordAt bs 40) ∗
      ((out + 64#64) ↦₆₄ v1_wordAt bs 48) ∗
      ((out + 72#64) ↦₆₄ v1_wordAt bs 56) ∗
      ((out + 80#64) ↦₆₄ v1_wordAt bs 64) ∗
      ((out + 88#64) ↦₆₄ v1_wordAt bs 72) ∗
      (((out + 96#64) ↦₈ (v1_wordAt bs 80).extractLsb' 0 8) ∗
       ((out + 97#64) ↦₃₂ (v1_wordAt bs 80).extractLsb' 8 32) ∗
       ((out + 101#64) ↦₁₆ (v1_wordAt bs 80).extractLsb' 40 16) ∗
       ((out + 103#64) ↦₈ (v1_wordAt bs 80).extractLsb' 56 8)) ∗
      ((out + 104#64) ↦₆₄ v1_wordAt bs 88) ∗
      ((out + 112#64) ↦₆₄ v1_wordAt bs 96) ∗
      (((out + 120#64) ↦₈ loByte (v1_wordAt bs 104)) ∗
       ((out + 121#64) ↦₆₄ unshiftWord (v1_wordAt bs 104) (loByte (v1_wordAt bs 112))) ∗
       ((out + 129#64) ↦ₛ EncoderFromPb.hiBytes7
         (overlapWord7 (unshiftWord (v1_wordAt bs 104) (loByte (v1_wordAt bs 112)))
           (v1_wordAt bs 112 >>> 8)))) ∗
      ((out + 136#64) ↦₆₄ v1_wordAt bs 120) ∗
      (((out + 144#64) ↦₈ ((loByte (v1_wordAt bs 128)).zeroExtend 32).setWidth 8) ∗
       ((out + 145#64) ↦₆₄
         (v1_midQ128 (v1_wordAt bs 128) (v1_wordAt bs 136) (v1_wordAt bs 144)).extractLsb' 0 64) ∗
       ((out + 153#64) ↦ₛ EncoderFromPb.loBytes7
         ((v1_midQ128 (v1_wordAt bs 128) (v1_wordAt bs 136) (v1_wordAt bs 144)).extractLsb' 64 64)) ∗
       ((out + 160#64) ↦₆₄
         overlapWord7
           ((v1_midQ128 (v1_wordAt bs 128) (v1_wordAt bs 136) (v1_wordAt bs 144)).extractLsb' 64 64)
           (v1_wordAt bs 144 >>> 8))) ∗
      ((out + 168#64) ↦₁₂₈ v1_quadAt bs 152) ∗
      ((out + 184#64) ↦₁₂₈ v1_quadAt bs 168) ∗
      ((out + 200#64) ↦₁₂₈ v1_quadAt bs 184) ∗
      ((out + 216#64) ↦₁₂₈ v1_quadAt bs 200) ∗
      ((out + 232#64) ↦₁₂₈ v1_quadAt bs 216) ∗
      ((out + 248#64) ↦₁₂₈ v1_quadAt bs 232) ∗
      ((out + 264#64) ↦₁₂₈ v1_quadAt bs 248) ∗
      ((out + 280#64) ↦₁₂₈ v1_quadAt bs 264) ∗
      ((out + 296#64) ↦₁₂₈ v1_quadAt bs 280) ∗
      ((out + 312#64) ↦₁₂₈ v1_quadAt bs 296) ∗
      ((out + 328#64) ↦₁₂₈ v1_quadAt bs 312) ∗
      ((out + 344#64) ↦₁₂₈ v1_quadAt bs 328) ∗
      ((out + 360#64) ↦₁₂₈ v1_quadAt bs 344) ∗
      ((out + 376#64) ↦₁₂₈ v1_quadAt bs 360) ∗
      ((out + 392#64) ↦₆₄ v1_wordAt bs 376) =
    ((out + 8#64) + 8#64) ↦ₛ bs := by
  rw [v1_out_96_realign out (v1_wordAt bs 80),
      v1_out_120_realign out (v1_wordAt bs 104) (v1_wordAt bs 112),
      v1_out_144_realign out (v1_wordAt bs 128) (v1_wordAt bs 136) (v1_wordAt bs 144),
      v1_bs384_eq_encCells bs hbs (out + 8#64)]
  unfold v1_encCellsAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

/-! ## Staging & Epilogue Bridge Helpers (`+4016 -> +4112 -> +6568 -> +6848 -> +8180`) -/

theorem v1_unchunkedHeaderSentAt_408_pack (A : RustAlloc) {F : ShaCompress}
    (out l1 pa1 l2 pa2 cap_ek ptr_ek len_ek cap_dk ptr_dk len_dk ep : BitVec 64)
    (ek dk rootKey macKey : List (BitVec 8))
    (hek : len_ek = BitVec.ofNat 64 ek.length)
    (hdk : len_dk = BitVec.ofNat 64 dk.length)
    (hl1 : l1 = BitVec.ofNat 64 rootKey.length)
    (hl2 : l2 = BitVec.ofNat 64 macKey.length) :
    ((out + 408#64) ↦₆₄ l1) ∗ ((out + 416#64) ↦₆₄ pa1) ∗ ((out + 424#64) ↦₆₄ l1) ∗
      ((out + 432#64) ↦₆₄ l2) ∗ ((out + 440#64) ↦₆₄ pa2) ∗ ((out + 448#64) ↦₆₄ l2) ∗
      ((out + 456#64) ↦₆₄ cap_ek) ∗ ((out + 464#64) ↦₆₄ ptr_ek) ∗ ((out + 472#64) ↦₆₄ len_ek) ∗
      ((out + 480#64) ↦₆₄ cap_dk) ∗ ((out + 488#64) ↦₆₄ ptr_dk) ∗ ((out + 496#64) ↦₆₄ len_dk) ∗
      ((out + 504#64) ↦₆₄ ep) ∗
      vecU8Payload A cap_ek ptr_ek ek ∗
      vecU8Payload A cap_dk ptr_dk dk ∗
      vecU8Payload A l1 pa1 rootKey ∗
      vecU8Payload A l2 pa2 macKey ⊢
    unchunkedHeaderSentAt A (F := F) (out + 408#64)
      { ek := ek, dk := dk,
        auth := { rootKey := rootKey, macKey := macKey },
        epoch := ep } := by
  subst hek hdk hl1 hl2
  dsimp only [unchunkedHeaderSentAt, authenticatorAt]
  have hrk_v := vecU8_of_header_payload A (out + 408#64) (BitVec.ofNat 64 rootKey.length) pa1 rootKey
  have hmk_v := vecU8_of_header_payload A (out + 432#64) (BitVec.ofNat 64 macKey.length) pa2 macKey
  have hek_v := vecU8_of_header_payload A (out + 456#64) cap_ek ptr_ek ek
  have hdk_v := vecU8_of_header_payload A (out + 480#64) cap_dk ptr_dk dk
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrk_v hmk_v hek_v hdk_v ⊢
  refine Entails.trans (Entails.of_eq (show _ =
    (((out + 408#64) ↦₆₄ BitVec.ofNat 64 rootKey.length) ∗ ((out + 416#64) ↦₆₄ pa1) ∗
     ((out + 424#64) ↦₆₄ BitVec.ofNat 64 rootKey.length) ∗
     vecU8Payload A (BitVec.ofNat 64 rootKey.length) pa1 rootKey) ∗
    (((out + 432#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗ ((out + 440#64) ↦₆₄ pa2) ∗
     ((out + 448#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗
     vecU8Payload A (BitVec.ofNat 64 macKey.length) pa2 macKey) ∗
    (((out + 456#64) ↦₆₄ cap_ek) ∗ ((out + 464#64) ↦₆₄ ptr_ek) ∗
     ((out + 472#64) ↦₆₄ BitVec.ofNat 64 ek.length) ∗ vecU8Payload A cap_ek ptr_ek ek) ∗
    (((out + 480#64) ↦₆₄ cap_dk) ∗ ((out + 488#64) ↦₆₄ ptr_dk) ∗
     ((out + 496#64) ↦₆₄ BitVec.ofNat 64 dk.length) ∗ vecU8Payload A cap_dk ptr_dk dk) ∗
    ((out + 504#64) ↦₆₄ ep) by ac_rfl)) ?_
  refine Entails.trans
    (sepConj_mono hrk_v (sepConj_mono hmk_v (sepConj_mono hek_v (sepConj_mono_left hdk_v)))) ?_
  exact Entails.of_eq (by ac_rfl)

theorem v1_epilogueOutFull_entails_keysSampled (A : RustAlloc) {F : ShaCompress}
    (out tag l1 pa1 l2 pa2 cap_ek ptr_ek len_ek cap_dk ptr_dk len_dk ep : BitVec 64)
    (bs : List (BitVec 8)) (hbs : bs.length = 384)
    (hi32 : BitVec 32) (enc : PolyEncoder) (P_heap : SepProp)
    (hreloc :
      ((out + 8#64) ↦₆₄ tag) ∗ (((out + 8#64) + 8#64) ↦ₛ bs) ∗
        (((out + 8#64) + 392#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ P_heap ⊢
        polyEncoderAt A (out + 8#64) enc)
    (ek dk rootKey macKey : List (BitVec 8))
    (hek : len_ek = BitVec.ofNat 64 ek.length)
    (hdk : len_dk = BitVec.ofNat 64 dk.length)
    (hl1 : l1 = BitVec.ofNat 64 rootKey.length)
    (hl2 : l2 = BitVec.ofNat 64 macKey.length)
    (w512 w520 w528 : BitVec 64)
    (b536 : BitVec 8) (q537 : BitVec 128) (w552 : BitVec 64)
    (bs240 : List (BitVec 8)) (hbs240 : bs240.length = 328)
    (q888 q904 : BitVec 128) (w920 : BitVec 64) :
    epilogueOutFull out
      3#64 tag (v1_wordAt bs 0) (v1_wordAt bs 8)
      (v1_wordAt bs 16) (v1_wordAt bs 24) (v1_wordAt bs 32) (v1_wordAt bs 40)
      (v1_wordAt bs 48) (v1_wordAt bs 56) (v1_wordAt bs 64) (v1_wordAt bs 72)
      ((v1_wordAt bs 80).extractLsb' 0 8) ((v1_wordAt bs 80).extractLsb' 8 32)
      ((v1_wordAt bs 80).extractLsb' 40 16) ((v1_wordAt bs 80).extractLsb' 56 8)
      (v1_wordAt bs 88) (v1_wordAt bs 96) (loByte (v1_wordAt bs 104))
      (unshiftWord (v1_wordAt bs 104) (loByte (v1_wordAt bs 112)))
      (overlapWord7 (unshiftWord (v1_wordAt bs 104) (loByte (v1_wordAt bs 112)))
        (v1_wordAt bs 112 >>> 8))
      (v1_wordAt bs 120)
      (((loByte (v1_wordAt bs 128)).zeroExtend 32).setWidth 8)
      (v1_midQ128 (v1_wordAt bs 128) (v1_wordAt bs 136) (v1_wordAt bs 144))
      (overlapWord7
        ((v1_midQ128 (v1_wordAt bs 128) (v1_wordAt bs 136) (v1_wordAt bs 144)).extractLsb' 64 64)
        (v1_wordAt bs 144 >>> 8))
      (v1_quadAt bs 152) (v1_quadAt bs 168) (v1_quadAt bs 184) (v1_quadAt bs 200)
      (v1_quadAt bs 216) (v1_quadAt bs 232) (v1_quadAt bs 248) (v1_quadAt bs 264)
      (v1_quadAt bs 280) (v1_quadAt bs 296) (v1_quadAt bs 312) (v1_quadAt bs 328)
      (v1_quadAt bs 344) (v1_quadAt bs 360)
      (v1_wordAt bs 376) (hi32 ++ enc.idx)
      l1 pa1 l1 l2 pa2 l2 cap_ek ptr_ek len_ek cap_dk ptr_dk len_dk ep
      w512 w520 w528
      b536 q537 w552 bs240 q888 q904 w920 ∗
      P_heap ∗
      vecU8Payload A cap_ek ptr_ek ek ∗
      vecU8Payload A cap_dk ptr_dk dk ∗
      vecU8Payload A l1 pa1 rootKey ∗
      vecU8Payload A l2 pa2 macKey ⊢
    resultChunkedStatesAt A (F := F) out
      (.ok (.keysSampled
        { uc := { ek := ek, dk := dk,
                  auth := { rootKey := rootKey, macKey := macKey },
                  epoch := ep },
          sending_hdr := enc })) := by
  dsimp only [resultChunkedStatesAt, chunkedStatesAt, chunkedKeysSampledAt]
  have ha408 : (out + 8#64) + 400#64 = out + 408#64 := by bv_omega
  have ha400 : (out + 8#64) + 392#64 = out + 400#64 := by bv_omega
  rw [ha408, sepConj_assoc (polyEncoderAt A (out + 8#64) enc)]
  rw [ha400] at hreloc
  unfold epilogueOutFull
  have hbs_eq := v1_out_16_to_400_eq_bs out bs hbs
  have huc := v1_unchunkedHeaderSentAt_408_pack A (F := F) out
    l1 pa1 l2 pa2 cap_ek ptr_ek len_ek cap_dk ptr_dk len_dk ep
    ek dk rootKey macKey hek hdk hl1 hl2
  have htail := epilogueOut_tail_512_entails_416 out
    w512 w520 w528 b536 q537 w552 bs240 hbs240 q888 q904 w920
  refine Entails.trans (Entails.of_eq (show _ =
    (out ↦₆₄ 3#64) ∗
    (((out + 8#64) ↦₆₄ tag) ∗
     (((out + 16#64) ↦₆₄ v1_wordAt bs 0) ∗
      ((out + 24#64) ↦₆₄ v1_wordAt bs 8) ∗
      ((out + 32#64) ↦₆₄ v1_wordAt bs 16) ∗
      ((out + 40#64) ↦₆₄ v1_wordAt bs 24) ∗
      ((out + 48#64) ↦₆₄ v1_wordAt bs 32) ∗
      ((out + 56#64) ↦₆₄ v1_wordAt bs 40) ∗
      ((out + 64#64) ↦₆₄ v1_wordAt bs 48) ∗
      ((out + 72#64) ↦₆₄ v1_wordAt bs 56) ∗
      ((out + 80#64) ↦₆₄ v1_wordAt bs 64) ∗
      ((out + 88#64) ↦₆₄ v1_wordAt bs 72) ∗
      (((out + 96#64) ↦₈ (v1_wordAt bs 80).extractLsb' 0 8) ∗
       ((out + 97#64) ↦₃₂ (v1_wordAt bs 80).extractLsb' 8 32) ∗
       ((out + 101#64) ↦₁₆ (v1_wordAt bs 80).extractLsb' 40 16) ∗
       ((out + 103#64) ↦₈ (v1_wordAt bs 80).extractLsb' 56 8)) ∗
      ((out + 104#64) ↦₆₄ v1_wordAt bs 88) ∗
      ((out + 112#64) ↦₆₄ v1_wordAt bs 96) ∗
      (((out + 120#64) ↦₈ loByte (v1_wordAt bs 104)) ∗
       ((out + 121#64) ↦₆₄ unshiftWord (v1_wordAt bs 104) (loByte (v1_wordAt bs 112))) ∗
       ((out + 129#64) ↦ₛ EncoderFromPb.hiBytes7
         (overlapWord7 (unshiftWord (v1_wordAt bs 104) (loByte (v1_wordAt bs 112)))
           (v1_wordAt bs 112 >>> 8)))) ∗
      ((out + 136#64) ↦₆₄ v1_wordAt bs 120) ∗
      (((out + 144#64) ↦₈ ((loByte (v1_wordAt bs 128)).zeroExtend 32).setWidth 8) ∗
       ((out + 145#64) ↦₆₄
         (v1_midQ128 (v1_wordAt bs 128) (v1_wordAt bs 136) (v1_wordAt bs 144)).extractLsb' 0 64) ∗
       ((out + 153#64) ↦ₛ EncoderFromPb.loBytes7
         ((v1_midQ128 (v1_wordAt bs 128) (v1_wordAt bs 136) (v1_wordAt bs 144)).extractLsb' 64 64)) ∗
       ((out + 160#64) ↦₆₄
         overlapWord7
           ((v1_midQ128 (v1_wordAt bs 128) (v1_wordAt bs 136) (v1_wordAt bs 144)).extractLsb' 64 64)
           (v1_wordAt bs 144 >>> 8))) ∗
      ((out + 168#64) ↦₁₂₈ v1_quadAt bs 152) ∗
      ((out + 184#64) ↦₁₂₈ v1_quadAt bs 168) ∗
      ((out + 200#64) ↦₁₂₈ v1_quadAt bs 184) ∗
      ((out + 216#64) ↦₁₂₈ v1_quadAt bs 200) ∗
      ((out + 232#64) ↦₁₂₈ v1_quadAt bs 216) ∗
      ((out + 248#64) ↦₁₂₈ v1_quadAt bs 232) ∗
      ((out + 264#64) ↦₁₂₈ v1_quadAt bs 248) ∗
      ((out + 280#64) ↦₁₂₈ v1_quadAt bs 264) ∗
      ((out + 296#64) ↦₁₂₈ v1_quadAt bs 280) ∗
      ((out + 312#64) ↦₁₂₈ v1_quadAt bs 296) ∗
      ((out + 328#64) ↦₁₂₈ v1_quadAt bs 312) ∗
      ((out + 344#64) ↦₁₂₈ v1_quadAt bs 328) ∗
      ((out + 360#64) ↦₁₂₈ v1_quadAt bs 344) ∗
      ((out + 376#64) ↦₁₂₈ v1_quadAt bs 360) ∗
      ((out + 392#64) ↦₆₄ v1_wordAt bs 376)) ∗
     ((out + 400#64) ↦₆₄ (hi32 ++ enc.idx)) ∗
     P_heap) ∗
    (((out + 408#64) ↦₆₄ l1) ∗ ((out + 416#64) ↦₆₄ pa1) ∗ ((out + 424#64) ↦₆₄ l1) ∗
     ((out + 432#64) ↦₆₄ l2) ∗ ((out + 440#64) ↦₆₄ pa2) ∗ ((out + 448#64) ↦₆₄ l2) ∗
     ((out + 456#64) ↦₆₄ cap_ek) ∗ ((out + 464#64) ↦₆₄ ptr_ek) ∗ ((out + 472#64) ↦₆₄ len_ek) ∗
     ((out + 480#64) ↦₆₄ cap_dk) ∗ ((out + 488#64) ↦₆₄ ptr_dk) ∗ ((out + 496#64) ↦₆₄ len_dk) ∗
     ((out + 504#64) ↦₆₄ ep) ∗
     vecU8Payload A cap_ek ptr_ek ek ∗
     vecU8Payload A cap_dk ptr_dk dk ∗
     vecU8Payload A l1 pa1 rootKey ∗
     vecU8Payload A l2 pa2 macKey) ∗
    (((out + 512#64) ↦₆₄ w512) ∗ ((out + 520#64) ↦₆₄ w520) ∗ ((out + 528#64) ↦₆₄ w528) ∗
     (((out + 536#64) ↦₈ b536) ∗ ((out + 537#64) ↦₁₂₈ q537) ∗
      ((out + 553#64) ↦ₛ EncoderFromPb.hiBytes7 w552) ∗ ((out + 560#64) ↦ₛ bs240) ∗
      ((out + 888#64) ↦₁₂₈ q888) ∗ ((out + 904#64) ↦₁₂₈ q904) ∗ ((out + 920#64) ↦₆₄ w920))) by ac_rfl)) ?_
  rw [hbs_eq]
  exact sepConj_mono_right (sepConj_mono hreloc (sepConj_mono huc htail))

theorem v1_resultPolyEncoder_err_entails_tag_392 (A : RustAlloc) (fsp : BitVec 64)
    (err : PolynomialError) :
    resultPolyEncoderFromPbAt A (fsp + 1888#64) (.error err) ⊢
      ((fsp + 1888#64) ↦₆₄ 2#64) ∗ memRegion (fsp + 1896#64) 392 := by
  dsimp only [resultPolyEncoderFromPbAt, polyEncoderNicheTag,
    resultPolyEncoderErrByteOff, resultPolyEncoderErrTailSize]
  have hm8 : ((fsp + 1896#64) ↦₈ polynomialErrorByte err) ∗ memRegion (fsp + 1897#64) 391 ⊢
      memRegion (fsp + 1896#64) 392 := by
    rw [ProofLib.memRegion_split' (b := fsp + 1896#64) (n := 1) (k := 391)
          (b' := fsp + 1897#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (ProofLib.pointsTo8_entails_memRegion (fsp + 1896#64) (polynomialErrorByte err))
  have ha1896 : (fsp + 1888#64) + 8#64 = fsp + 1896#64 := by bv_omega
  have ha1897 : (fsp + 1888#64) + 9#64 = fsp + 1897#64 := by bv_omega
  rw [ha1896, ha1897]
  exact sepConj_mono_right hm8

@[local simp, local arm64_norm, local wp_norm]
theorem v1_bfm_pa1 (pa1 : BitVec 64) :
    (BitVec.zeroExtend 64 (BitVec.truncate 32 pa1) &&& 255#64 |||
      (pa1 >>> 8 &&& 72057594037927935#64) <<< 8) = pa1 := by
  bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem v1_x23_add_57 (fsp : BitVec 64) :
    fsp + 848#64 + 57#64 = fsp + 905#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v1_x23_add_57_sext (fsp : BitVec 64) :
    (fsp + 848#64) + (57#64).signExtend 64 = fsp + 905#64 := by bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem v1_x25_sub_887 (fsp : BitVec 64) :
    fsp + 1792#64 + 18446744073709550729#64 = fsp + 905#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v1_x25_add_96 (fsp : BitVec 64) :
    fsp + 1792#64 + 96#64 = fsp + 1888#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v1_pbA_add_121 (pbA : BitVec 64) :
    pbA + (121#64).signExtend 64 = pbA + 121#64 := by bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem v1_pbA_144_add_8 (pbA : BitVec 64) :
    pbA + 144#64 + 8#64 = pbA + 152#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v1_pbA_121_add_8 (pbA : BitVec 64) :
    pbA + 121#64 + 8#64 = pbA + 129#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v1_fsp_928_add_8 (fsp : BitVec 64) :
    fsp + 928#64 + 8#64 = fsp + 936#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v1_fsp_905_add_8 (fsp : BitVec 64) :
    fsp + 905#64 + 8#64 = fsp + 913#64 := by bv_omega

theorem v1_memRegion_896_56_split (fsp : BitVec 64) :
    memRegion (fsp + 896#64) 56 ⊢
      (∃∗ d0 : BitVec 64, (fsp + 896#64) ↦₆₄ d0) ∗
      (∃∗ d8 : BitVec 64, (fsp + 904#64) ↦₆₄ d8) ∗
      (∃∗ d16 : BitVec 64, (fsp + 912#64) ↦₆₄ d16) ∗
      (∃∗ d24 : BitVec 64, (fsp + 920#64) ↦₆₄ d24) ∗
      (∃∗ q32 : BitVec 128, (fsp + 928#64) ↦₁₂₈ q32) ∗
      (∃∗ d48 : BitVec 64, (fsp + 944#64) ↦₆₄ d48) := by
  exact split_top <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem128_entails _) <|
    mem64_entails _

theorem v1_fsp_904_triple_rest (fsp d8 d16 d24 : BitVec 64) (R : SepProp) :
    ((fsp + 904#64) ↦₆₄ d8) ∗ ((fsp + 912#64) ↦₆₄ d16) ∗ ((fsp + 920#64) ↦₆₄ d24) ∗ R =
      ((fsp + 904#64) ↦₈ loByte d8) ∗
      ((fsp + 905#64) ↦₆₄ unshiftWord d8 (loByte d16)) ∗
      ((fsp + 913#64) ↦₆₄ unshiftWord d16 (loByte d24)) ∗
      ((fsp + 921#64) ↦ₛ EncoderFromPb.hiBytes7 d24) ∗ R := by
  have h := v1_triple64_eq_byte_q128_tail7 (fsp + 904#64) d8 d16 d24
  rw [← EncoderFromPb.pointsTo64_pair_eq_pointsTo128 ((fsp + 904#64) + 1#64)
        (unshiftWord d8 (loByte d16)) (unshiftWord d16 (loByte d24))] at h
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
  rw [show ((fsp + 904#64) ↦₆₄ d8) ∗ ((fsp + 912#64) ↦₆₄ d16) ∗ ((fsp + 920#64) ↦₆₄ d24) ∗ R =
        (((fsp + 904#64) ↦₆₄ d8) ∗ ((fsp + 912#64) ↦₆₄ d16) ∗ ((fsp + 920#64) ↦₆₄ d24)) ∗ R by ac_rfl,
      h]
  simp only [sepConj_assoc]

theorem v1_pbA_120_triple_rest (pbA w8 w16 w24 : BitVec 64) (R : SepProp) :
    ((pbA + 120#64) ↦₆₄ w8) ∗ ((pbA + 128#64) ↦₆₄ w16) ∗ ((pbA + 136#64) ↦₆₄ w24) ∗ R =
      ((pbA + 120#64) ↦₈ loByte w8) ∗
      ((pbA + 121#64) ↦₆₄ unshiftWord w8 (loByte w16)) ∗
      ((pbA + 129#64) ↦₆₄ unshiftWord w16 (loByte w24)) ∗
      ((pbA + 137#64) ↦ₛ EncoderFromPb.hiBytes7 w24) ∗ R := by
  have h120 := v1_triple64_eq_byte_q128_tail7 (pbA + 120#64) w8 w16 w24
  rw [← EncoderFromPb.pointsTo64_pair_eq_pointsTo128 ((pbA + 120#64) + 1#64)
        (unshiftWord w8 (loByte w16)) (unshiftWord w16 (loByte w24))] at h120
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h120
  rw [show ((pbA + 120#64) ↦₆₄ w8) ∗ ((pbA + 128#64) ↦₆₄ w16) ∗ ((pbA + 136#64) ↦₆₄ w24) ∗ R =
        (((pbA + 120#64) ↦₆₄ w8) ∗ ((pbA + 128#64) ↦₆₄ w16) ∗ ((pbA + 136#64) ↦₆₄ w24)) ∗ R by ac_rfl,
      h120]
  simp only [sepConj_assoc]

theorem v1_fsp_913_realign_rest (fsp u1 d24 : BitVec 64) (Rest : SepProp) :
    ((fsp + 913#64) ↦₆₄ u1) ∗
      ((fsp + 921#64) ↦ₛ EncoderFromPb.hiBytes7 d24) ∗ Rest =
      ((fsp + 913#64) ↦ₛ EncoderFromPb.loBytes7 u1) ∗
      ((fsp + 920#64) ↦₆₄ overlapWord7 u1 (d24 >>> 8)) ∗ Rest := by
  have ha920 : (fsp + 913#64) + 7#64 = fsp + 920#64 := by bv_omega
  have ha921 : (fsp + 913#64) + 8#64 = fsp + 921#64 := by bv_omega
  have h := pointsTo64_loBytes7_eq_loBytes7_overlapWord7 (fsp + 913#64) u1 (d24 >>> 8)
  rw [ha921, ha920, ← v1_hiBytes7_eq_loBytes7_lsr8 d24] at h
  rw [← sepConj_assoc ((fsp + 913#64) ↦₆₄ u1), h]
  simp only [sepConj_assoc]

/-- At `+4016`, when `s.sendingHdr = none` (`[fsp + 1496] = noneCap`), reconstructs `x0 := pa1`
    and branches at `+4032` (`b.eq +5860`) to `+5860`. -/
theorem v1_sendingHdr_none_4016_5860
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (fsp out pa1 u8 u32 u72 : BitVec 64) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4016#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = pa1 >>> 8)
    (hx21 : s.readReg64 .x21 = u8)
    (hx22 : s.readReg64 .x22 = u72)
    (hx26 : s.readReg64 .x26 = pa1)
    (hx28 : s.readReg64 .x28 = u32)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5860#64) s
      (((fsp + 1496#64) ↦₆₄ noneCap) ∗ Rest)
      (fun s1 P1 =>
        (P1 ⊢ ((fsp + 1496#64) ↦₆₄ noneCap) ∗ Rest) ∧
        s1.sp = fsp ∧
        s1.readReg64 .x0 = pa1 ∧
        s1.readReg64 .x19 = out ∧
        s1.readReg64 .x21 = u8 ∧
        s1.readReg64 .x22 = u72 ∧
        s1.readReg64 .x28 = u32 ∧
        TraceCalleeSaved s1 s0) := by
  states_from_pb_fetches_range b (Rust.withPanics ext) 4016 20
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, noneCap, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_steps
  refine EncoderFromPb.align_pre (Entails.of_eq (by ac_rfl)) ?_
  wp_done

/-- At `+4016`, when `s.sendingHdr = some pbEnc` (`w0.toNat < 2 ^ 63`), copies the 56-byte
    `ProtoPolynomialEncoder` from `pbA + 112..168` to `fsp + 896..952`, stores `pa1` at
    `[fsp + 200]`, sets `x0 = fsp + 1888, x1 = fsp + 896, x23 = fsp + 848`, and reaches `+4096`
    (`bl <PolyEncoder>::from_pb`). -/
theorem v1_sendingHdr_some_copy_4016_4096
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (fsp out pbA pa1 v200 u8 u32 u72 : BitVec 64)
    (pbEnc : ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hw0 : w0.toNat < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4016#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = pa1 >>> 8)
    (hx21 : s.readReg64 .x21 = u8)
    (hx22 : s.readReg64 .x22 = u72)
    (hx25 : s.readReg64 .x25 = fsp + 1792#64)
    (hx26 : s.readReg64 .x26 = pa1)
    (hx27 : s.readReg64 .x27 = pbA)
    (hx28 : s.readReg64 .x28 = u32)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4096#64) s
      (((fsp + 200#64) ↦₆₄ v200) ∗
        memRegion (fsp + 896#64) 56 ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A (some pbEnc) w0 w8 w16 w24 w32 w40 w48 ∗
        Rest)
      (fun s1 P1 =>
        (P1 ⊢
          ((fsp + 200#64) ↦₆₄ pa1) ∗
          protoPolynomialEncoderAt A (fsp + 896#64) pbEnc ∗
          memRegion (fsp + 1496#64) 56 ∗
          memRegion (pbA + 112#64) 56 ∗
          Rest) ∧
        s1.sp = fsp ∧
        s1.readReg64 .x0 = fsp + 1888#64 ∧
        s1.readReg64 .x1 = fsp + 896#64 ∧
        s1.readReg64 .x19 = out ∧
        s1.readReg64 .x21 = u8 ∧
        s1.readReg64 .x22 = u72 ∧
        s1.readReg64 .x23 = fsp + 848#64 ∧
        s1.readReg64 .x25 = fsp + 1792#64 ∧
        s1.readReg64 .x28 = u32 ∧
        TraceCalleeSaved s1 s0) := by
  subst hsp
  have hcmn : (w0 + 1#64 == 0#64) = false :=
    Bool.eq_false_iff.mpr (cap_add_one_beq_zero_false hw0)
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left (v1_memRegion_896_56_split s.sp))) ?_
  dsimp only [v1_optProtoPolyEncoderWordsAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [pointsTo64_split_1_7 (s.sp + 1504#64) w8]
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, pointsTo128, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro d48
  apply ProofLib.SepWP.exists_left; intro q32
  apply ProofLib.SepWP.exists_left; intro d24
  apply ProofLib.SepWP.exists_left; intro d16
  apply ProofLib.SepWP.exists_left; intro d8
  apply ProofLib.SepWP.exists_left; intro d0
  states_from_pb_fetches_range b (Rust.withPanics ext) 4016 80
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_conv_pre =>
    rw [v1_fsp_904_triple_rest s.sp d8 d16 d24,
        v1_pbA_120_triple_rest pbA w8 w16 w24]
  wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step
  wp_conv_pre =>
    rw [← v1_pbA_120_triple_rest pbA w8 w16 w24]
  wp_step; wp_step; wp_step; wp_step; wp_step
  wp_conv_pre =>
    rw [v1_fsp_913_realign_rest s.sp _ d24]
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · have hdst := v1_dst24_realign_final (s.sp + 904#64) w8 w16 w24
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hdst
    have hfsp1504 : ((s.sp + 1504#64) ↦₈ loByte w8) ∗ ((s.sp + 1505#64) ↦ₛ EncoderFromPb.hiBytes7 w8) =
        ((s.sp + 1504#64) ↦₆₄ w8) := by
      have h := (pointsTo64_split_1_7 (s.sp + 1504#64) w8).symm
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h
    have hpack := v1_optProtoPolyEncoderAt_pack_some A (s.sp + 896#64) pbEnc w0 w8 w16 w24 w32 w40 w48
    have hm1496 := v1_optProtoPolyEncoderWordsAt_entails_56 (s.sp + 1496#64) w0 w8 w16 w24 w32 w40 w48
    have hm112 := v1_optProtoPolyEncoderWordsAt_entails_56 (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48
    dsimp only [v1_optProtoPolyEncoderWordsAt] at hpack hm1496 hm112
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hpack hm1496 hm112
    refine Entails.trans (Entails.of_eq (show _ =
      ((s.sp + 200#64) ↦₆₄ pa1) ∗
      (((s.sp + 896#64) ↦₆₄ w0) ∗
       (((s.sp + 904#64) ↦₈ loByte w8) ∗
        ((s.sp + 905#64) ↦₆₄ unshiftWord w8 (loByte w16)) ∗
        ((s.sp + 913#64) ↦ₛ EncoderFromPb.loBytes7 (unshiftWord w16 (loByte w24))) ∗
        ((s.sp + 920#64) ↦₆₄ w24)) ∗
       ((s.sp + 928#64) ↦₆₄ w32) ∗
       ((s.sp + 936#64) ↦₆₄ w40) ∗
       ((s.sp + 944#64) ↦₆₄ w48) ∗
       v1_optProtoPolyEncoderHeap A (some pbEnc) w0 w8 w16 w24 w32 w40 w48) ∗
      (((s.sp + 1496#64) ↦₆₄ w0) ∗
       (((s.sp + 1504#64) ↦₈ loByte w8) ∗ ((s.sp + 1505#64) ↦ₛ EncoderFromPb.hiBytes7 w8)) ∗
       ((s.sp + 1512#64) ↦₆₄ w16) ∗
       ((s.sp + 1520#64) ↦₆₄ w24) ∗
       ((s.sp + 1528#64) ↦₆₄ w32) ∗
       ((s.sp + 1536#64) ↦₆₄ w40) ∗
       ((s.sp + 1544#64) ↦₆₄ w48)) ∗
      (((pbA + 112#64) ↦₆₄ w0) ∗
       ((pbA + 120#64) ↦₆₄ w8) ∗
       ((pbA + 128#64) ↦₆₄ w16) ∗
       ((pbA + 136#64) ↦₆₄ w24) ∗
       ((pbA + 144#64) ↦₆₄ w32) ∗
       ((pbA + 152#64) ↦₆₄ w40) ∗
       ((pbA + 160#64) ↦₆₄ w48)) ∗
      Rest by ac_rfl)) ?_
    rw [hdst, hfsp1504]
    have h896 : ((s.sp + 896#64) ↦₆₄ w0) ∗
        (((s.sp + 904#64) ↦₆₄ w8) ∗ ((s.sp + 912#64) ↦₆₄ w16) ∗ ((s.sp + 920#64) ↦₆₄ w24)) ∗
        ((s.sp + 928#64) ↦₆₄ w32) ∗
        ((s.sp + 936#64) ↦₆₄ w40) ∗
        ((s.sp + 944#64) ↦₆₄ w48) ∗
        v1_optProtoPolyEncoderHeap A (some pbEnc) w0 w8 w16 w24 w32 w40 w48 =
        (((s.sp + 896#64) ↦₆₄ w0) ∗ ((s.sp + 904#64) ↦₆₄ w8) ∗ ((s.sp + 912#64) ↦₆₄ w16) ∗
         ((s.sp + 920#64) ↦₆₄ w24) ∗ ((s.sp + 928#64) ↦₆₄ w32) ∗
         ((s.sp + 936#64) ↦₆₄ w40) ∗ ((s.sp + 944#64) ↦₆₄ w48)) ∗
        v1_optProtoPolyEncoderHeap A (some pbEnc) w0 w8 w16 w24 w32 w40 w48 := by ac_rfl
    rw [h896]
    exact sepConj_mono_right (sepConj_mono hpack (sepConj_mono hm1496 (sepConj_mono_left hm112)))
  · wp_done

end CryptoVerification.SpqrV1.States.FromPb

