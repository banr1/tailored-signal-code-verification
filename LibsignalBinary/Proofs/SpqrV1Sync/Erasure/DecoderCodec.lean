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
# SPQR V1 Erasure Decoder Protobuf Round-Trip

Point-list serialization length (`4 * l.length`) and `PolyDecoder.fromPb ∘ PolyDecoder.intoPb`
round-trip under `DecInv`.
-/

namespace CryptoVerification.SpqrV1Sync.Erasure.DecoderCodec

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync.Erasure
theorem length_flatMap_serialize (l : List Pt) :
    (l.flatMap Pt.serialize).length = 4 * l.length := by
  induction l with
  | nil => simp
  | cons p ps ih =>
    rw [List.flatMap_cons, List.length_append, ih]
    simp [Pt.serialize, u16ToBeBytes]
    omega


/-! ## Decoder protobuf round-trip -/

section MoveCompat
private theorem u16FromBeBytes_hi_lo (v : BitVec 16) :
    u16FromBeBytes ((v >>> 8).setWidth 8) (v.setWidth 8) = v := by
  unfold u16FromBeBytes
  ext i hi
  simp only [BitVec.zeroExtend, BitVec.getElem_or, BitVec.getElem_shiftLeft,
    BitVec.getElem_setWidth]
  by_cases h8 : i < 8
  · simp [h8, hi]
  · have hsub : i - 8 < 8 := by omega
    have hadd : 8 + (i - 8) = i := by omega
    simp [h8, hsub, hadd, hi]

@[local simp] private theorem gf16_new_value (g : GF16) : GF16.new g.value = g := by
  cases g
  rfl

@[local simp] private theorem pt_deserialize_hi_lo (pt : Pt) :
    Pt.deserialize
      [(pt.x.value >>> 8).setWidth 8, pt.x.value.setWidth 8,
       (pt.y.value >>> 8).setWidth 8, pt.y.value.setWidth 8] = .ok pt := by
  cases pt
  simp [Pt.deserialize, u16FromBeBytes_hi_lo]

private theorem pt_cmp_eq_gt_of_lt {a b : Pt} (h : b.x.value.toNat < a.x.value.toNat) :
    Pt.cmp a b = .gt := by
  unfold Pt.cmp Ord.compare instOrdNat compareOfLessAndEq
  dsimp only
  split
  · omega
  · split
    · omega
    · rfl

private theorem sortedSetPt_push_fst_of_forall_lt (v : SortedSetPt) (pt : Pt)
    (h : ∀ p ∈ v.vec, p.x.value.toNat < pt.x.value.toNat) :
    (v.push pt).1 = { vec := v.vec ++ [pt] } := by
  unfold SortedSetPt.push
  cases hlast : v.vec.getLast? with
  | none =>
    have hnil : v.vec = [] := List.getLast?_eq_none_iff.mp hlast
    simp [hnil]
  | some last =>
    have hmem : last ∈ v.vec := List.mem_of_getLast? hlast
    have hlt : last.x.value.toNat < pt.x.value.toNat := h last hmem
    have hcmp : Pt.cmp pt last = .gt := pt_cmp_eq_gt_of_lt hlt
    simp [hcmp]

private theorem pushChunksExact4_flatMap_serialize_aux (l : List Pt) (acc : List Pt)
    (hsorted : (l.map fun pt => pt.x.value.toNat).Pairwise (· < ·))
    (hacc : ∀ p ∈ acc, ∀ q ∈ l, p.x.value.toNat < q.x.value.toNat) :
    PolyDecoder.pushChunksExact4 (l.flatMap Pt.serialize) { vec := acc } =
      .ok { vec := acc ++ l } := by
  induction l generalizing acc with
  | nil =>
    simp [PolyDecoder.pushChunksExact4]
  | cons pt rest ih =>
    rcases List.pairwise_cons.mp hsorted with ⟨hpt_rest, hsorted_rest⟩
    have hlt_acc : ∀ p ∈ acc, p.x.value.toNat < pt.x.value.toNat :=
      fun p hp => hacc p hp pt List.mem_cons_self
    have hpush : (({ vec := acc } : SortedSetPt).push pt).1 = { vec := acc ++ [pt] } :=
      sortedSetPt_push_fst_of_forall_lt { vec := acc } pt hlt_acc
    have hacc' : ∀ p ∈ acc ++ [pt], ∀ q ∈ rest, p.x.value.toNat < q.x.value.toNat := by
      intro p hp q hq
      rcases List.mem_append.mp hp with hp_acc | hp_pt
      · exact hacc p hp_acc q (List.mem_cons_of_mem pt hq)
      · rw [List.mem_singleton.mp hp_pt]
        exact hpt_rest q.x.value.toNat (List.mem_map_of_mem hq)
    have hflat : (pt :: rest).flatMap Pt.serialize =
        (pt.x.value >>> 8).setWidth 8 :: pt.x.value.setWidth 8 ::
        (pt.y.value >>> 8).setWidth 8 :: pt.y.value.setWidth 8 ::
        rest.flatMap Pt.serialize := rfl
    rw [hflat]
    unfold PolyDecoder.pushChunksExact4
    rw [pt_deserialize_hi_lo]
    change PolyDecoder.pushChunksExact4 (rest.flatMap Pt.serialize)
      (({ vec := acc } : SortedSetPt).push pt).1 = .ok { vec := acc ++ (pt :: rest) }
    rw [hpush, ih (acc ++ [pt]) hsorted_rest hacc']
    simp [List.append_assoc]

private theorem pushChunksExact4_flatMap_serialize (s : SortedSetPt)
    (hsorted : (s.vec.map fun pt => pt.x.value.toNat).Pairwise (· < ·)) (cap : Nat) :
    PolyDecoder.pushChunksExact4 (s.vec.flatMap Pt.serialize) (SortedSetPt.withCapacity cap) =
      .ok s := by
  cases s with
  | mk vec =>
    unfold SortedSetPt.withCapacity
    rw [pushChunksExact4_flatMap_serialize_aux vec [] hsorted (by intro p hp; nomatch hp)]
    rfl

private theorem decodeDecoderPbPts_map_serialize (pts : List SortedSetPt)
    (hsorted : ∀ s ∈ pts, (s.vec.map fun pt => pt.x.value.toNat).Pairwise (· < ·)) :
    PolyDecoder.decodeDecoderPbPts (pts.map fun s => s.vec.flatMap Pt.serialize) =
      .ok (.ok pts) := by
  induction pts with
  | nil => rfl
  | cons s rest ih =>
    have hs : (s.vec.map fun pt => pt.x.value.toNat).Pairwise (· < ·) :=
      hsorted s List.mem_cons_self
    have hrest : ∀ s' ∈ rest, (s'.vec.map fun pt => pt.x.value.toNat).Pairwise (· < ·) :=
      fun s' hs' => hsorted s' (List.mem_cons_of_mem s hs')
    have hmod : (s.vec.flatMap Pt.serialize).length % 4 = 0 := by
      rw [length_flatMap_serialize]
      omega
    simp only [List.map_cons, PolyDecoder.decodeDecoderPbPts, hmod, bne_self_eq_false,
      Bool.false_eq_true, ↓reduceIte]
    rw [pushChunksExact4_flatMap_serialize s hs, ih hrest]
    rfl

private theorem decoder_fromPb_intoPb_of_wf (dec : PolyDecoder)
    (hptsNeeded : dec.ptsNeeded < 2 ^ 32)
    (hlen : dec.pts.length = 16)
    (hsorted : ∀ j (h : j < dec.pts.length),
      (dec.pts[j].vec.map fun pt => pt.x.value.toNat).Pairwise (· < ·)) :
    PolyDecoder.fromPb dec.intoPb = .ok (.ok dec) := by
  have hsortedMem : ∀ s ∈ dec.pts, (s.vec.map fun pt => pt.x.value.toNat).Pairwise (· < ·) := by
    intro s hs
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hs
    exact hsorted j hj
  have hdecPts :
      PolyDecoder.decodeDecoderPbPts (dec.pts.map fun s => s.vec.flatMap Pt.serialize) =
        .ok (.ok dec.pts) :=
    decodeDecoderPbPts_map_serialize dec.pts hsortedMem
  have hptsNeededBv : (BitVec.ofNat 32 dec.ptsNeeded).toNat = dec.ptsNeeded := by
    rw [BitVec.toNat_ofNat]
    omega
  cases dec with
  | mk ptsNeeded pts isComplete =>
    unfold PolyDecoder.fromPb PolyDecoder.intoPb
    simp only [List.length_map, hlen, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    rw [hdecPts]
    simp only [bind, Except.bind, pure, Except.pure, hptsNeededBv]

theorem decoder_fromPb_intoPb (msg : List (BitVec 8)) (S : Finset Nat) (dec : PolyDecoder)
    (hd : DecInv msg S dec) (hlen : msg.length ≤ 2 ^ 20) :
    PolyDecoder.fromPb dec.intoPb = .ok (.ok dec) :=
  decoder_fromPb_intoPb_of_wf dec (by rw [hd.ptsNeeded]; omega) hd.len hd.sorted

end MoveCompat

end CryptoVerification.SpqrV1Sync.Erasure.DecoderCodec
