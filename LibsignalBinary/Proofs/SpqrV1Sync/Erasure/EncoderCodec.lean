/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1Sync.ErasureDefs
public import LibsignalBinary.Specifications.LibsignalSpqrV1.GF16

@[expose] public section

set_option autoImplicit false

/-!
# SPQR V1 Erasure Encoder Protobuf Round-Trip

Big-endian `GF16` coefficient serialization length (`2 * cs.length`), 16-lane `msgPoints` length,
and `PolyEncoder.fromPb ∘ PolyEncoder.intoPb` round-trip under `EncInv`.
-/

namespace CryptoVerification.SpqrV1Sync.Erasure.EncoderCodec

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync.Erasure
theorem flatMap_u16ToBeBytes_length (cs : List GF16) :
    (cs.flatMap (fun c => u16ToBeBytes c.value)).length = 2 * cs.length := by
  induction cs with
  | nil => simp
  | cons c rest ih =>
    rw [List.flatMap_cons, List.length_append, ih]
    simp [u16ToBeBytes]
    omega

theorem msgPoints_length (msg : List (BitVec 8)) : (msgPoints msg).length = 16 := by
  simp [msgPoints]


/-! ## Encoder protobuf round-trip -/

section MoveCompat
private theorem u16FromBeBytes_u16ToBeBytes (v : BitVec 16) :
    u16FromBeBytes ((v >>> 8).setWidth 8) (v.setWidth 8) = v := by
  ext i hi
  simp only [u16FromBeBytes, BitVec.zeroExtend, BitVec.getElem_or, BitVec.getElem_shiftLeft,
    BitVec.getElem_setWidth]
  by_cases h8 : i < 8
  · simp [h8, hi, BitVec.getLsbD_eq_getElem]
  · have h2 : i - 8 < 8 := by omega
    have h3 : 8 + (i - 8) = i := by omega
    simp [h8, h2, h3, hi, BitVec.getLsbD_eq_getElem]

@[local simp]
private theorem gf16_new_value (g : GF16) : GF16.new g.value = g := by
  cases g
  rfl

private theorem bytesToGF16List_flatMap_u16ToBeBytes (cs : List GF16) :
    Poly.bytesToGF16List (cs.flatMap (fun c => u16ToBeBytes c.value)) = .ok cs := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
    rw [List.flatMap_cons]
    change Poly.bytesToGF16List
      ((c.value >>> 8).setWidth 8 :: c.value.setWidth 8 ::
        rest.flatMap (fun c => u16ToBeBytes c.value)) = .ok (c :: rest)
    simp only [Poly.bytesToGF16List, bind, Except.bind, ih, pure, Except.pure,
      u16FromBeBytes_u16ToBeBytes, gf16_new_value]

private theorem decodePbPoints_map_flatMap (points : List Point) :
    PolyEncoder.decodePbPoints
      (points.map (fun pt => pt.value.flatMap (fun g => u16ToBeBytes g.value))) =
      .ok (.ok points) := by
  induction points with
  | nil => rfl
  | cons pt rest ih =>
    have hlen : (pt.value.flatMap (fun g => u16ToBeBytes g.value)).length % 2 = 0 := by
      rw [flatMap_u16ToBeBytes_length]
      omega
    cases pt with
    | mk val =>
      simp only [List.map_cons, PolyEncoder.decodePbPoints, hlen, bne_self_eq_false,
        Bool.false_eq_true, ↓reduceIte, bind, Except.bind,
        bytesToGF16List_flatMap_u16ToBeBytes, ih, pure, Except.pure]

private theorem poly_deserialize_serialize (p : Poly) (hne : 0 < p.coefficients.length) :
    Poly.deserialize (Poly.serialize p) = .ok (.ok p) := by
  cases p with
  | mk cs =>
    have hlen2 : (cs.flatMap (fun c => u16ToBeBytes c.value)).length = 2 * cs.length :=
      flatMap_u16ToBeBytes_length cs
    have hemp : (cs.flatMap (fun c => u16ToBeBytes c.value)).isEmpty = false := by
      rw [List.isEmpty_eq_false_iff, ← List.length_pos_iff_ne_nil]
      simp only at hne
      omega
    have hmod : ((cs.flatMap (fun c => u16ToBeBytes c.value)).length % 2 == 1) = false := by
      rw [beq_eq_false_iff_ne]
      omega
    simp only [Poly.deserialize, Poly.serialize, hemp, hmod, Bool.or_self, Bool.false_eq_true,
      ↓reduceIte, bind, Except.bind, bytesToGF16List_flatMap_u16ToBeBytes, pure, Except.pure]

private theorem decodePbPolys_map_serialize (polys : List Poly)
    (hne : ∀ p ∈ polys, 0 < p.coefficients.length) :
    PolyEncoder.decodePbPolys (polys.map Poly.serialize) = .ok (.ok polys) := by
  induction polys with
  | nil => rfl
  | cons p rest ih =>
    have hp : 0 < p.coefficients.length := hne p (List.mem_cons_self ..)
    have hrest : ∀ q ∈ rest, 0 < q.coefficients.length :=
      fun q hq => hne q (List.mem_cons_of_mem p hq)
    simp only [List.map_cons, PolyEncoder.decodePbPolys, poly_deserialize_serialize p hp,
      ih hrest, bind, Except.bind, pure, Except.pure]

private theorem needed_pos (len j : Nat) (hshort : 32 ≤ len) : 0 < needed len j := by
  unfold needed
  split <;> omega

theorem encoder_fromPb_intoPb_proof (msg : List (BitVec 8)) (e : PolyEncoder) (he : EncInv msg e)
    (_hlen : msg.length ≤ 2 ^ 20) (hshort : 32 ≤ msg.length) :
    PolyEncoder.fromPb e.intoPb = .ok (.ok e) := by
  rcases e with ⟨idx, s⟩
  rcases he with hpts | ⟨polys, hpolys, hlen16, hcoeff⟩
  · simp only at hpts
    subst hpts
    have hpbLen :
        ((msgPoints msg).map (fun pt => pt.value.flatMap (fun g => u16ToBeBytes g.value))).length = 16 := by
      rw [List.length_map, msgPoints_length]
    have hpbNonEmpty :
        (!((msgPoints msg).map (fun pt => pt.value.flatMap (fun g => u16ToBeBytes g.value))).isEmpty) = true := by
      rw [Bool.not_eq_true', List.isEmpty_eq_false_iff, ← List.length_pos_iff_ne_nil]
      omega
    have hpbNumPolys :
        (((msgPoints msg).map (fun pt => pt.value.flatMap (fun g => u16ToBeBytes g.value))).length != NUM_POLYS) = false := by
      change (((msgPoints msg).map (fun pt => pt.value.flatMap (fun g => u16ToBeBytes g.value))).length != 16) = false
      rw [bne_eq_false_iff_eq]
      exact hpbLen
    simp only [PolyEncoder.intoPb, PolyEncoder.fromPb, hpbNonEmpty, ↓reduceIte,
      List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, hpbNumPolys,
      bind, Except.bind, decodePbPoints_map_flatMap, pure, Except.pure]
  · simp only at hpolys
    subst hpolys
    have hne : ∀ p ∈ polys, 0 < p.coefficients.length := by
      intro p hp
      rcases List.mem_iff_getElem.mp hp with ⟨j, hj, rfl⟩
      rw [(hcoeff j hj).1]
      exact needed_pos msg.length j hshort
    have hpbLen : ((polys.map Poly.serialize).length == NUM_POLYS) = true := by
      change ((polys.map Poly.serialize).length == 16) = true
      rw [beq_iff_eq, List.length_map]
      exact hlen16
    simp only [PolyEncoder.intoPb, PolyEncoder.fromPb, List.isEmpty_nil, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, hpbLen, bind, Except.bind,
      decodePbPolys_map_serialize polys hne, pure, Except.pure]

end MoveCompat

end CryptoVerification.SpqrV1Sync.Erasure.EncoderCodec
