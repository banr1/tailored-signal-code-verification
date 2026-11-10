/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.Defs
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Auth
public import LibsignalBinary.Specifications.LibsignalSpqrV1.GF16
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Proto
public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import ProofLib

set_option autoImplicit false

/-!
# Braid Protobuf Round-Trip on Well-Formed States

Proves `States.from_pb ∘ into_pb = .ok` on any `BOk` braid state (`st_bCodec`), lifting `EncWF`
and `DecWF` to `Codec.EncOk` and `Codec.DecOk` across all eleven `States` variants.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.SendTotal

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync.InSync
open CryptoVerification.SpqrV1Sync.Braid
open CryptoGames.LibsignalSession (ShaCompress)

private theorem bcd_u16FromBeBytes_u16ToBeBytes (v : BitVec 16) :
    u16FromBeBytes ((v >>> 8).setWidth 8) (v.setWidth 8) = v := by
  simp only [u16FromBeBytes]
  bv_slice

private theorem bcd_gf16_new_value (g : GF16) : GF16.new g.value = g := by
  cases g
  rfl

private theorem bcd_pt_deserialize_bytes (pt : Pt) :
    Pt.deserialize
      [(pt.x.value >>> 8).setWidth 8, pt.x.value.setWidth 8,
       (pt.y.value >>> 8).setWidth 8, pt.y.value.setWidth 8] = .ok pt := by
  cases pt with
  | mk x y =>
    simp [Pt.deserialize, bcd_u16FromBeBytes_u16ToBeBytes, bcd_gf16_new_value]

private theorem bcd_sortedSetPt_push_gt (acc : List Pt) (pt : Pt)
    (hgt : ∀ a ∈ acc, a.x.value.toNat < pt.x.value.toNat) :
    ((SortedSetPt.mk acc).push pt).1 = SortedSetPt.mk (acc ++ [pt]) := by
  by_cases hnil : acc = []
  · subst hnil
    simp [SortedSetPt.push]
  · have hlast : acc.getLast? = some (acc.getLast hnil) := List.getLast?_eq_some_getLast hnil
    have hmem : acc.getLast hnil ∈ acc := List.mem_of_getLast? hlast
    have hlt : (acc.getLast hnil).x.value.toNat < pt.x.value.toNat := hgt _ hmem
    have hcmp : Pt.cmp pt (acc.getLast hnil) = .gt := Nat.compare_eq_gt.mpr hlt
    simp [SortedSetPt.push, hlast, hcmp]

private theorem bcd_length_flatMap_ptSerialize (xs : List Pt) :
    (xs.flatMap Pt.serialize).length = 4 * xs.length := by
  induction xs with
  | nil => rfl
  | cons pt rest ih =>
    have hp : Pt.serialize pt =
        [(pt.x.value >>> 8).setWidth 8, pt.x.value.setWidth 8,
         (pt.y.value >>> 8).setWidth 8, pt.y.value.setWidth 8] := rfl
    rw [List.flatMap_cons, hp]
    simp only [List.cons_append, List.nil_append, List.length_cons, ih]
    omega

private theorem bcd_pushChunksExact4_sorted (xs : List Pt) (acc : List Pt)
    (hbet : ∀ a ∈ acc, ∀ b ∈ xs, a.x.value.toNat < b.x.value.toNat)
    (hsort : xs.Pairwise (fun a b => a.x.value.toNat < b.x.value.toNat)) :
    PolyDecoder.pushChunksExact4 (xs.flatMap Pt.serialize) ⟨acc⟩ = .ok ⟨acc ++ xs⟩ := by
  induction xs generalizing acc with
  | nil =>
    simp [PolyDecoder.pushChunksExact4]
  | cons pt rest ih =>
    rw [List.pairwise_cons] at hsort
    rcases hsort with ⟨hpt_rest, hrest_sort⟩
    have hpush := bcd_sortedSetPt_push_gt acc pt (fun a ha => hbet a ha pt (List.Mem.head rest))
    have hbet' : ∀ a ∈ acc ++ [pt], ∀ b ∈ rest, a.x.value.toNat < b.x.value.toNat := by
      intro a ha b hb
      rcases List.mem_append.mp ha with ha_acc | ha_pt
      · exact hbet a ha_acc b (List.mem_cons_of_mem pt hb)
      · simp only [List.mem_singleton] at ha_pt
        subst ha_pt
        exact hpt_rest b hb
    have hstep :
        PolyDecoder.pushChunksExact4 ((pt :: rest).flatMap Pt.serialize) ⟨acc⟩ =
          PolyDecoder.pushChunksExact4 (rest.flatMap Pt.serialize) (((SortedSetPt.mk acc).push pt).1) := by
      simp [List.flatMap_cons, Pt.serialize, u16ToBeBytes, PolyDecoder.pushChunksExact4,
        bcd_pt_deserialize_bytes, Bind.bind, Except.bind]
    rw [hstep, hpush, ih (acc ++ [pt]) hbet' hrest_sort, List.append_assoc]
    rfl

private theorem bcd_decodeDecoderPbPts_map (ss : List SortedSetPt)
    (hsort : ∀ s ∈ ss, (s.vec.map fun pt => pt.x.value.toNat).Pairwise (· < ·)) :
    PolyDecoder.decodeDecoderPbPts (ss.map (fun s => s.vec.flatMap Pt.serialize)) =
      .ok (.ok ss) := by
  induction ss with
  | nil => rfl
  | cons s rest ih =>
    have hs_sort : s.vec.Pairwise (fun a b => a.x.value.toNat < b.x.value.toNat) :=
      List.pairwise_map.mp (hsort s (List.Mem.head rest))
    have hmod : ((s.vec.flatMap Pt.serialize).length % 4 != 0) = false := by
      rw [bcd_length_flatMap_ptSerialize]
      simp
    have hpush :
        PolyDecoder.pushChunksExact4 (s.vec.flatMap Pt.serialize)
          (SortedSetPt.withCapacity ((s.vec.flatMap Pt.serialize).length / 4)) = .ok s := by
      unfold SortedSetPt.withCapacity
      rw [bcd_pushChunksExact4_sorted s.vec [] (by intro a ha; cases ha) hs_sort]
      cases s
      rfl
    have hrest := ih (fun t ht => hsort t (List.mem_cons_of_mem s ht))
    simp only [List.map_cons, PolyDecoder.decodeDecoderPbPts, hmod, Bool.false_eq_true, ↓reduceIte,
      hpush, hrest, Bind.bind, Except.bind, pure, Except.pure]

private theorem bcd_encOk_of_encWF {len : Nat} {e : PolyEncoder}
    (he : EncWF len e) (hlo : 32 ≤ len) (hhi : len ≤ 2 ^ 20) :
    Codec.EncOk spqrPolyApi e := by
  rcases he with ⟨msg, hinv, rfl⟩
  exact Codec.spqr_encOk_of_EncInv msg e hinv hhi hlo

private theorem bcd_decOk_of_decWF {n : Nat} {d : PolyDecoder}
    (hd : DecWF n d) (hn : n < 2 ^ 32) :
    Codec.DecOk spqrPolyApi n d := by
  rcases hd with ⟨hpn0, hl, hsort0⟩
  refine ⟨?_, ?_⟩
  · rcases d with ⟨ptsNeeded, pts, isComplete⟩
    simp only at hpn0 hl hsort0
    have hsort : ∀ s ∈ pts, (s.vec.map fun pt => pt.x.value.toNat).Pairwise (· < ·) := by
      intro s hs
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hs
      exact hsort0 j hj
    have hpn : (BitVec.ofNat 32 ptsNeeded).toNat = ptsNeeded := by
      rw [BitVec.toNat_ofNat]
      omega
    simp [spqrPolyApi, protoPolyDecoderToPb, pbToProtoPolyDecoder,
      PolyDecoder.intoPb, PolyDecoder.fromPb, hl, bcd_decodeDecoderPbPts_map pts hsort, hpn,
      Bind.bind, Except.bind, pure, Except.pure, Except.mapError]
  · simp [spqrPolyApi, protoPolyDecoderToPb, PolyDecoder.intoPb, hpn0]

private theorem bcd_bok_wf {F : ShaCompress} (st : St F) (hbok : BOk st) : st.WF := by
  cases st with
  | keysUnsampled _ => trivial
  | keysSampled s =>
    rcases hbok with ⟨_, huc, henc⟩
    exact ⟨huc, bcd_encOk_of_encWF henc (by omega) (by omega)⟩
  | headerSent s =>
    rcases hbok with ⟨_, huc, henc, hdec⟩
    exact ⟨huc, bcd_encOk_of_encWF henc (by omega) (by omega), bcd_decOk_of_decWF hdec (by omega)⟩
  | ct1Received s =>
    rcases hbok with ⟨_, huc, henc⟩
    exact ⟨huc, bcd_encOk_of_encWF henc (by omega) (by omega)⟩
  | ekSentCt1Received s =>
    rcases hbok with ⟨_, huc, hdec⟩
    exact ⟨huc, bcd_decOk_of_decWF hdec (by omega)⟩
  | noHeaderReceived s =>
    rcases hbok with ⟨_, hdec⟩
    exact bcd_decOk_of_decWF hdec (by omega)
  | headerReceived s =>
    rcases hbok with ⟨_, huc, hdec⟩
    exact ⟨huc, bcd_decOk_of_decWF hdec (by omega)⟩
  | ct1Sampled s =>
    rcases hbok with ⟨_, huc, henc, hdec⟩
    exact ⟨huc, bcd_encOk_of_encWF henc (by omega) (by omega), bcd_decOk_of_decWF hdec (by omega)⟩
  | ekReceivedCt1Sampled s =>
    rcases hbok with ⟨_, huc, henc⟩
    exact ⟨huc, bcd_encOk_of_encWF henc (by omega) (by omega)⟩
  | ct1Acknowledged s =>
    rcases hbok with ⟨_, huc, hdec⟩
    exact ⟨huc, bcd_decOk_of_decWF hdec (by omega)⟩
  | ct2Sampled s =>
    rcases hbok with ⟨_, henc⟩
    exact bcd_encOk_of_encWF henc (by omega) (by omega)

/-- `States.from_pb` inverts `States.into_pb` on any well-formed braid state (`BOk`). -/
theorem st_bCodec (F : ShaCompress) : BCodecStmt F := by
  intro st hbok
  exact Codec.states_from_pb_into_pb (Codec.spqrAuthApi_auOk F) st (bcd_bok_wf st hbok)

end CryptoVerification.SpqrV1Sync.SendTotal
