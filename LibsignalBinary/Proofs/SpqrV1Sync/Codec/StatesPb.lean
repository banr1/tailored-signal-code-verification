/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbState
public import Batteries.Tactic.OpenPrivate
public import LibsignalBinary.Proofs.SpqrV1Sync.ErasureDefs
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Auth
public import LibsignalBinary.Specifications.LibsignalSpqrV1.GF16
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Proto
public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import ProofLib

/-!
# Braid State Protobuf Conversion Round-Trip (`States.from_pb ∘ States.into_pb`)

`Top.send` and `Top.recv` persist the braid state via `States.into_pb` and reload it via
`States.from_pb`, which re-validates key-material byte lengths (`UcOk.*`), polynomial
encoder/decoder deserialization (`EncOk`, `DecOk`), and per-phase `pts_needed` counts (`DecOk P n`).
Under the combined well-formedness predicate `States.WF`, `States.from_pb` inverts `States.into_pb`
(`states_from_pb_into_pb`), and composing with `PbState` yields the full byte-level state
round-trip `decodeState_spqrDeps_statesFromPb`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.Codec

open CryptoVerification.LibsignalSpqrV1 hiding WireType DecodeErr decodeVarint encodeVarint
open CryptoGames.LibsignalSession (ShaCompress)
/-- `Authenticator::from_pb ∘ into_pb = id`. -/
def AuOk (Au : AuthApi) : Prop := ∀ a, Au.from_pb (Au.into_pb a) = a

/-- `PolyEncoder::from_pb ∘ into_pb = Ok`. -/
def EncOk (P : PolyApi) (e : P.PolyEncoder) : Prop :=
  P.encoder_from_pb (P.encoder_into_pb e) = .ok (.ok e)

/-- `PolyDecoder::from_pb ∘ into_pb = Ok`, and `into_pb` writes `pts_needed = n`. -/
def DecOk (P : PolyApi) (n : Nat) (d : P.PolyDecoder) : Prop :=
  P.decoder_from_pb (P.decoder_into_pb d) = .ok (.ok d) ∧
    (P.decoder_into_pb d).ptsNeeded = BitVec.ofNat 32 n

private theorem encoderFromPbStateDecode_ok {P : PolyApi} {e : P.PolyEncoder}
    (he : EncOk P e) :
    encoderFromPbStateDecode P (some (P.encoder_into_pb e)) = .ok e := by
  have he' : P.encoder_from_pb (P.encoder_into_pb e) = .ok (.ok e) := he
  simp [encoderFromPbStateDecode, he', StatesResult.ofPanic, Bind.bind, Except.bind]

private theorem decoderFromPbStateDecode_ok {P : PolyApi} {n : Nat} {d : P.PolyDecoder}
    (hd : DecOk P n d) :
    decoderFromPbStateDecode P (some (P.decoder_into_pb d)) = .ok d := by
  simp [decoderFromPbStateDecode, hd.1, StatesResult.ofPanic, Bind.bind, Except.bind]

private theorem u16FromBeBytes_u16ToBeBytes (v : BitVec 16) :
    u16FromBeBytes ((v >>> 8).setWidth 8) (v.setWidth 8) = v := by
  simp only [u16FromBeBytes]
  bv_slice

private theorem gf16_new_value (g : GF16) : GF16.new g.value = g := by
  cases g
  rfl

private theorem length_flatMap_u16ToBeBytes (l : List GF16) :
    (l.flatMap (fun g => u16ToBeBytes g.value)).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons g tl ih =>
    have hu : u16ToBeBytes g.value = [(g.value >>> 8).setWidth 8, g.value.setWidth 8] := rfl
    rw [List.flatMap_cons, hu]
    simp only [List.cons_append, List.nil_append, List.length_cons, ih]
    omega

private theorem bytesToGF16List_flatMap (l : List GF16) :
    Poly.bytesToGF16List (l.flatMap (fun g => u16ToBeBytes g.value)) = .ok l := by
  induction l with
  | nil => rfl
  | cons g tl ih =>
    have hu : u16ToBeBytes g.value = [(g.value >>> 8).setWidth 8, g.value.setWidth 8] := rfl
    rw [List.flatMap_cons, hu]
    simp only [List.cons_append, List.nil_append, Poly.bytesToGF16List,
      Bind.bind, Except.bind, pure, Except.pure, ih, u16FromBeBytes_u16ToBeBytes, gf16_new_value]

private theorem decodePbPoints_map (pts : List Point) :
    PolyEncoder.decodePbPoints
      (pts.map (fun pt => pt.value.flatMap (fun g => u16ToBeBytes g.value))) = .ok (.ok pts) := by
  induction pts with
  | nil => rfl
  | cons pt rest ih =>
    have heven : ((pt.value.flatMap (fun g => u16ToBeBytes g.value)).length % 2 != 0) = false := by
      rw [length_flatMap_u16ToBeBytes]
      simp
    simp only [List.map_cons, PolyEncoder.decodePbPoints, heven, Bool.false_eq_true, ↓reduceIte,
      bytesToGF16List_flatMap, ih, Bind.bind, Except.bind, pure, Except.pure]

private theorem poly_deserialize_serialize (p : Poly) (hne : p.coefficients ≠ []) :
    Poly.deserialize (Poly.serialize p) = .ok (.ok p) := by
  cases p with
  | mk coeffs =>
    cases coeffs with
    | nil => exact absurd rfl hne
    | cons c0 cs =>
      have hlen : (((c0 :: cs).flatMap (fun c => u16ToBeBytes c.value)).length % 2 == 1) = false := by
        rw [length_flatMap_u16ToBeBytes]
        simp
      have hempty : ((c0 :: cs).flatMap (fun c => u16ToBeBytes c.value)).isEmpty = false := by
        simp [u16ToBeBytes]
      simp only [Poly.serialize, Poly.deserialize, hempty, hlen, Bool.or_self,
        Bool.false_eq_true, ↓reduceIte, bytesToGF16List_flatMap,
        Bind.bind, Except.bind, pure, Except.pure]

private theorem decodePbPolys_map (ps : List Poly) (hne : ∀ p ∈ ps, p.coefficients ≠ []) :
    PolyEncoder.decodePbPolys (ps.map Poly.serialize) = .ok (.ok ps) := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
    have hp : p.coefficients ≠ [] := hne p (List.Mem.head rest)
    have hrest : ∀ q ∈ rest, q.coefficients ≠ [] :=
      fun q hq => hne q (List.mem_cons_of_mem p hq)
    simp only [List.map_cons, PolyEncoder.decodePbPolys, poly_deserialize_serialize p hp, ih hrest,
      Bind.bind, Except.bind, pure, Except.pure]

private theorem needed_pos {len : Nat} (hshort : 32 ≤ len) (j : Nat) :
    1 ≤ Erasure.needed len j := by
  unfold Erasure.needed
  split <;> omega

private theorem pt_deserialize_bytes (pt : Pt) :
    Pt.deserialize
      [(pt.x.value >>> 8).setWidth 8, pt.x.value.setWidth 8,
       (pt.y.value >>> 8).setWidth 8, pt.y.value.setWidth 8] = .ok pt := by
  cases pt with
  | mk x y =>
    simp [Pt.deserialize, u16FromBeBytes_u16ToBeBytes, gf16_new_value]

private theorem sortedSetPt_push_gt (acc : List Pt) (pt : Pt)
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

private theorem length_flatMap_ptSerialize (xs : List Pt) :
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

private theorem pushChunksExact4_sorted (xs : List Pt) (acc : List Pt)
    (hbet : ∀ a ∈ acc, ∀ b ∈ xs, a.x.value.toNat < b.x.value.toNat)
    (hsort : xs.Pairwise (fun a b => a.x.value.toNat < b.x.value.toNat)) :
    PolyDecoder.pushChunksExact4 (xs.flatMap Pt.serialize) ⟨acc⟩ = .ok ⟨acc ++ xs⟩ := by
  induction xs generalizing acc with
  | nil =>
    simp [PolyDecoder.pushChunksExact4]
  | cons pt rest ih =>
    rw [List.pairwise_cons] at hsort
    rcases hsort with ⟨hpt_rest, hrest_sort⟩
    have hpush := sortedSetPt_push_gt acc pt (fun a ha => hbet a ha pt (List.Mem.head rest))
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
        pt_deserialize_bytes, Bind.bind, Except.bind]
    rw [hstep, hpush, ih (acc ++ [pt]) hbet' hrest_sort, List.append_assoc]
    rfl

private theorem decodeDecoderPbPts_map (ss : List SortedSetPt)
    (hsort : ∀ s ∈ ss, (s.vec.map fun pt => pt.x.value.toNat).Pairwise (· < ·)) :
    PolyDecoder.decodeDecoderPbPts (ss.map (fun s => s.vec.flatMap Pt.serialize)) =
      .ok (.ok ss) := by
  induction ss with
  | nil => rfl
  | cons s rest ih =>
    have hs_sort : s.vec.Pairwise (fun a b => a.x.value.toNat < b.x.value.toNat) :=
      List.pairwise_map.mp (hsort s (List.Mem.head rest))
    have hmod : ((s.vec.flatMap Pt.serialize).length % 4 != 0) = false := by
      rw [length_flatMap_ptSerialize]
      simp
    have hpush :
        PolyDecoder.pushChunksExact4 (s.vec.flatMap Pt.serialize)
          (SortedSetPt.withCapacity ((s.vec.flatMap Pt.serialize).length / 4)) = .ok s := by
      unfold SortedSetPt.withCapacity
      rw [pushChunksExact4_sorted s.vec [] (by intro a ha; cases ha) hs_sort]
      cases s
      rfl
    have hrest := ih (fun t ht => hsort t (List.mem_cons_of_mem s ht))
    simp only [List.map_cons, PolyDecoder.decodeDecoderPbPts, hmod, Bool.false_eq_true, ↓reduceIte,
      hpush, hrest, Bind.bind, Except.bind, pure, Except.pure]

/-! ## Unchunked and chunked per-variant round-trips -/

theorem fromPb_intoPb_ekKeysUnsampled {Au : AuthApi} (hAu : AuOk Au)
    (s : Unchunked.SendEk.KeysUnsampled Au) :
    Unchunked.SendEk.KeysUnsampled.from_pb Au s.into_pb = .ok s := by
  rcases s with ⟨epoch, auth⟩
  simp [Unchunked.SendEk.KeysUnsampled.into_pb, Unchunked.SendEk.KeysUnsampled.from_pb, hAu auth]

def UcOk.ekHeaderSent {Au : AuthApi} (s : Unchunked.SendEk.HeaderSent Au) : Prop :=
  s.dk.length = DECAPSULATION_KEY_SIZE ∧ s.ek.length = ENCAPSULATION_KEY_SIZE

theorem fromPb_intoPb_ekHeaderSent {Au : AuthApi} (hAu : AuOk Au)
    (s : Unchunked.SendEk.HeaderSent Au)
    (h : UcOk.ekHeaderSent s) :
    Unchunked.SendEk.HeaderSent.from_pb Au s.into_pb = .ok s := by
  rcases s with ⟨epoch, auth, ek, dk⟩
  rcases h with ⟨hdk, hek⟩
  simp [Unchunked.SendEk.HeaderSent.into_pb, Unchunked.SendEk.HeaderSent.from_pb,
    hdk, hek, hAu auth]

def UcOk.ekEkSent {Au : AuthApi} (s : Unchunked.SendEk.EkSent Au) : Prop :=
  s.dk.length = DECAPSULATION_KEY_SIZE

theorem fromPb_intoPb_ekEkSent {Au : AuthApi} (hAu : AuOk Au) (s : Unchunked.SendEk.EkSent Au)
    (h : UcOk.ekEkSent s) :
    Unchunked.SendEk.EkSent.from_pb Au s.into_pb = .ok s := by
  rcases s with ⟨epoch, auth, dk⟩
  have hdk : dk.length = DECAPSULATION_KEY_SIZE := h
  simp [Unchunked.SendEk.EkSent.into_pb, Unchunked.SendEk.EkSent.from_pb, hdk, hAu auth]

def UcOk.ekEkSentCt1Received {Au : AuthApi} (s : Unchunked.SendEk.EkSentCt1Received Au) : Prop :=
  s.dk.length = DECAPSULATION_KEY_SIZE ∧ s.ct1.length = CIPHERTEXT1_SIZE

theorem fromPb_intoPb_ekEkSentCt1Received {Au : AuthApi} (hAu : AuOk Au)
    (s : Unchunked.SendEk.EkSentCt1Received Au)
    (h : UcOk.ekEkSentCt1Received s) :
    Unchunked.SendEk.EkSentCt1Received.from_pb Au s.into_pb = .ok s := by
  rcases s with ⟨epoch, auth, dk, ct1⟩
  rcases h with ⟨hdk, hct1⟩
  simp [Unchunked.SendEk.EkSentCt1Received.into_pb, Unchunked.SendEk.EkSentCt1Received.from_pb,
    hdk, hct1, hAu auth]

theorem fromPb_intoPb_ctNoHeaderReceived {Au : AuthApi} (hAu : AuOk Au)
    (s : Unchunked.SendCt.NoHeaderReceived Au) :
    Unchunked.SendCt.NoHeaderReceived.from_pb Au s.into_pb = .ok s := by
  rcases s with ⟨epoch, auth⟩
  simp [Unchunked.SendCt.NoHeaderReceived.into_pb, Unchunked.SendCt.NoHeaderReceived.from_pb,
    hAu auth]

def UcOk.ctHeaderReceived {Au : AuthApi} (s : Unchunked.SendCt.HeaderReceived Au) : Prop :=
  s.hdr.length = HEADER_SIZE

theorem fromPb_intoPb_ctHeaderReceived {Au : AuthApi} (hAu : AuOk Au)
    (s : Unchunked.SendCt.HeaderReceived Au)
    (h : UcOk.ctHeaderReceived s) :
    Unchunked.SendCt.HeaderReceived.from_pb Au s.into_pb = .ok s := by
  rcases s with ⟨epoch, auth, hdr⟩
  have hhdr : hdr.length = HEADER_SIZE := h
  simp [Unchunked.SendCt.HeaderReceived.into_pb, Unchunked.SendCt.HeaderReceived.from_pb,
    hhdr, hAu auth]

def UcOk.ctCt1Sent {Au : AuthApi} (s : Unchunked.SendCt.Ct1Sent Au) : Prop :=
  s.hdr.length = HEADER_SIZE ∧
    s.es.length = ENCAPSULATION_STATE_SIZE ∧
    s.ct1.length = CIPHERTEXT1_SIZE

theorem fromPb_intoPb_ctCt1Sent {Au : AuthApi} (hAu : AuOk Au) (s : Unchunked.SendCt.Ct1Sent Au)
    (h : UcOk.ctCt1Sent s) :
    Unchunked.SendCt.Ct1Sent.from_pb Au s.into_pb = .ok s := by
  rcases s with ⟨epoch, auth, hdr, es, ct1⟩
  rcases h with ⟨hhdr, hes, hct1⟩
  simp [Unchunked.SendCt.Ct1Sent.into_pb, Unchunked.SendCt.Ct1Sent.from_pb,
    hhdr, hes, hct1, hAu auth]

def UcOk.ctCt1SentEkReceived {Au : AuthApi} (s : Unchunked.SendCt.Ct1SentEkReceived Au) : Prop :=
  s.es.length = ENCAPSULATION_STATE_SIZE ∧
    s.ct1.length = CIPHERTEXT1_SIZE ∧
    s.ek.length = ENCAPSULATION_KEY_SIZE

theorem fromPb_intoPb_ctCt1SentEkReceived {Au : AuthApi} (hAu : AuOk Au)
    (s : Unchunked.SendCt.Ct1SentEkReceived Au)
    (h : UcOk.ctCt1SentEkReceived s) :
    Unchunked.SendCt.Ct1SentEkReceived.from_pb Au s.into_pb = .ok s := by
  rcases s with ⟨epoch, auth, es, ek, ct1⟩
  rcases h with ⟨hes, hct1, hek⟩
  simp [Unchunked.SendCt.Ct1SentEkReceived.into_pb, Unchunked.SendCt.Ct1SentEkReceived.from_pb,
    hes, hct1, hek, hAu auth]

theorem fromPb_intoPb_ctCt2Sent {Au : AuthApi} (hAu : AuOk Au) (s : Unchunked.SendCt.Ct2Sent Au) :
    Unchunked.SendCt.Ct2Sent.from_pb Au s.into_pb = .ok s := by
  rcases s with ⟨epoch, auth⟩
  simp [Unchunked.SendCt.Ct2Sent.into_pb, Unchunked.SendCt.Ct2Sent.from_pb, hAu auth]

theorem fromPb_intoPb_keysUnsampled {Au : AuthApi} (hAu : AuOk Au)
    (s : Chunked.SendEk.KeysUnsampled Au) :
    Chunked.SendEk.KeysUnsampled.from_pb Au s.into_pb = .ok s := by
  cases s with
  | mk uc =>
    simp [Chunked.SendEk.KeysUnsampled.into_pb, Chunked.SendEk.KeysUnsampled.from_pb,
      fromPb_intoPb_ekKeysUnsampled hAu uc, Bind.bind, Except.bind]

def ChOk.keysSampled {P : PolyApi} {Au : AuthApi} (s : Chunked.SendEk.KeysSampled P Au) : Prop :=
  UcOk.ekHeaderSent s.uc ∧ EncOk P s.sending_hdr

theorem fromPb_intoPb_keysSampled {P : PolyApi} {Au : AuthApi} (hAu : AuOk Au)
    (s : Chunked.SendEk.KeysSampled P Au)
    (h : ChOk.keysSampled s) :
    Chunked.SendEk.KeysSampled.from_pb P Au s.into_pb = .ok s := by
  cases s with
  | mk uc sending_hdr =>
    rcases h with ⟨huc, henc⟩
    simp [Chunked.SendEk.KeysSampled.into_pb, Chunked.SendEk.KeysSampled.from_pb,
      fromPb_intoPb_ekHeaderSent hAu uc huc, encoderFromPbStateDecode_ok henc,
      Bind.bind, Except.bind]

def ChOk.headerSent {P : PolyApi} {Au : AuthApi} (s : Chunked.SendEk.HeaderSent P Au) : Prop :=
  UcOk.ekEkSent s.uc ∧ EncOk P s.sending_ek ∧ DecOk P 480 s.receiving_ct1

theorem fromPb_intoPb_headerSent {P : PolyApi} {Au : AuthApi} (hAu : AuOk Au)
    (s : Chunked.SendEk.HeaderSent P Au)
    (h : ChOk.headerSent s) :
    Chunked.SendEk.HeaderSent.from_pb P Au s.into_pb = .ok s := by
  cases s with
  | mk uc sending_ek receiving_ct1 =>
    rcases h with ⟨huc, henc, hdec⟩
    simp [Chunked.SendEk.HeaderSent.into_pb, Chunked.SendEk.HeaderSent.from_pb,
      hdec.2, CIPHERTEXT1_SIZE, fromPb_intoPb_ekEkSent hAu uc huc,
      encoderFromPbStateDecode_ok henc, decoderFromPbStateDecode_ok hdec,
      Bind.bind, Except.bind]

def ChOk.ct1Received {P : PolyApi} {Au : AuthApi} (s : Chunked.SendEk.Ct1Received P Au) : Prop :=
  UcOk.ekEkSentCt1Received s.uc ∧ EncOk P s.sending_ek

theorem fromPb_intoPb_ct1Received {P : PolyApi} {Au : AuthApi} (hAu : AuOk Au)
    (s : Chunked.SendEk.Ct1Received P Au)
    (h : ChOk.ct1Received s) :
    Chunked.SendEk.Ct1Received.from_pb P Au s.into_pb = .ok s := by
  cases s with
  | mk uc sending_ek =>
    rcases h with ⟨huc, henc⟩
    simp [Chunked.SendEk.Ct1Received.into_pb, Chunked.SendEk.Ct1Received.from_pb,
      fromPb_intoPb_ekEkSentCt1Received hAu uc huc, encoderFromPbStateDecode_ok henc,
      Bind.bind, Except.bind]

def ChOk.ekSentCt1Received {P : PolyApi} {Au : AuthApi}
    (s : Chunked.SendEk.EkSentCt1Received P Au) : Prop :=
  UcOk.ekEkSentCt1Received s.uc ∧ DecOk P 80 s.receiving_ct2

theorem fromPb_intoPb_ekSentCt1Received {P : PolyApi} {Au : AuthApi} (hAu : AuOk Au)
    (s : Chunked.SendEk.EkSentCt1Received P Au)
    (h : ChOk.ekSentCt1Received s) :
    Chunked.SendEk.EkSentCt1Received.from_pb P Au s.into_pb = .ok s := by
  cases s with
  | mk uc receiving_ct2 =>
    rcases h with ⟨huc, hdec⟩
    simp [Chunked.SendEk.EkSentCt1Received.into_pb, Chunked.SendEk.EkSentCt1Received.from_pb,
      hdec.2, CIPHERTEXT2_SIZE, AUTHENTICATOR_MACSIZE,
      fromPb_intoPb_ekEkSentCt1Received hAu uc huc, decoderFromPbStateDecode_ok hdec,
      Bind.bind, Except.bind]

def ChOk.noHeaderReceived {P : PolyApi} {Au : AuthApi}
    (s : Chunked.SendCt.NoHeaderReceived P Au) : Prop :=
  DecOk P 48 s.receiving_hdr

theorem fromPb_intoPb_noHeaderReceived {P : PolyApi} {Au : AuthApi} (hAu : AuOk Au)
    (s : Chunked.SendCt.NoHeaderReceived P Au)
    (h : ChOk.noHeaderReceived s) :
    Chunked.SendCt.NoHeaderReceived.from_pb P Au s.into_pb = .ok s := by
  cases s with
  | mk uc receiving_hdr =>
    have hdec : DecOk P 48 receiving_hdr := h
    simp [Chunked.SendCt.NoHeaderReceived.into_pb, Chunked.SendCt.NoHeaderReceived.from_pb,
      hdec.2, HEADER_SIZE, AUTHENTICATOR_MACSIZE,
      fromPb_intoPb_ctNoHeaderReceived hAu uc, decoderFromPbStateDecode_ok hdec,
      Bind.bind, Except.bind]

def ChOk.headerReceived {P : PolyApi} {Au : AuthApi}
    (s : Chunked.SendCt.HeaderReceived P Au) : Prop :=
  UcOk.ctHeaderReceived s.uc ∧ DecOk P 576 s.receiving_ek

theorem fromPb_intoPb_headerReceived {P : PolyApi} {Au : AuthApi} (hAu : AuOk Au)
    (s : Chunked.SendCt.HeaderReceived P Au)
    (h : ChOk.headerReceived s) :
    Chunked.SendCt.HeaderReceived.from_pb P Au s.into_pb = .ok s := by
  cases s with
  | mk uc receiving_ek =>
    rcases h with ⟨huc, hdec⟩
    simp [Chunked.SendCt.HeaderReceived.into_pb, Chunked.SendCt.HeaderReceived.from_pb,
      hdec.2, ENCAPSULATION_KEY_SIZE,
      fromPb_intoPb_ctHeaderReceived hAu uc huc, decoderFromPbStateDecode_ok hdec,
      Bind.bind, Except.bind]

def ChOk.ct1Sampled {P : PolyApi} {Au : AuthApi} (s : Chunked.SendCt.Ct1Sampled P Au) : Prop :=
  UcOk.ctCt1Sent s.uc ∧ EncOk P s.sending_ct1 ∧ DecOk P 576 s.receiving_ek

theorem fromPb_intoPb_ct1Sampled {P : PolyApi} {Au : AuthApi} (hAu : AuOk Au)
    (s : Chunked.SendCt.Ct1Sampled P Au)
    (h : ChOk.ct1Sampled s) :
    Chunked.SendCt.Ct1Sampled.from_pb P Au s.into_pb = .ok s := by
  cases s with
  | mk uc sending_ct1 receiving_ek =>
    rcases h with ⟨huc, henc, hdec⟩
    simp [Chunked.SendCt.Ct1Sampled.into_pb, Chunked.SendCt.Ct1Sampled.from_pb,
      hdec.2, ENCAPSULATION_KEY_SIZE,
      fromPb_intoPb_ctCt1Sent hAu uc huc, encoderFromPbStateDecode_ok henc,
      decoderFromPbStateDecode_ok hdec, Bind.bind, Except.bind]

def ChOk.ekReceivedCt1Sampled {P : PolyApi} {Au : AuthApi}
    (s : Chunked.SendCt.EkReceivedCt1Sampled P Au) : Prop :=
  UcOk.ctCt1SentEkReceived s.uc ∧ EncOk P s.sending_ct1

theorem fromPb_intoPb_ekReceivedCt1Sampled {P : PolyApi} {Au : AuthApi} (hAu : AuOk Au)
    (s : Chunked.SendCt.EkReceivedCt1Sampled P Au)
    (h : ChOk.ekReceivedCt1Sampled s) :
    Chunked.SendCt.EkReceivedCt1Sampled.from_pb P Au s.into_pb = .ok s := by
  cases s with
  | mk uc sending_ct1 =>
    rcases h with ⟨huc, henc⟩
    simp [Chunked.SendCt.EkReceivedCt1Sampled.into_pb, Chunked.SendCt.EkReceivedCt1Sampled.from_pb,
      fromPb_intoPb_ctCt1SentEkReceived hAu uc huc, encoderFromPbStateDecode_ok henc,
      Bind.bind, Except.bind]

def ChOk.ct1Acknowledged {P : PolyApi} {Au : AuthApi}
    (s : Chunked.SendCt.Ct1Acknowledged P Au) : Prop :=
  UcOk.ctCt1Sent s.uc ∧ DecOk P 576 s.receiving_ek

theorem fromPb_intoPb_ct1Acknowledged {P : PolyApi} {Au : AuthApi} (hAu : AuOk Au)
    (s : Chunked.SendCt.Ct1Acknowledged P Au)
    (h : ChOk.ct1Acknowledged s) :
    Chunked.SendCt.Ct1Acknowledged.from_pb P Au s.into_pb = .ok s := by
  cases s with
  | mk uc receiving_ek =>
    rcases h with ⟨huc, hdec⟩
    simp [Chunked.SendCt.Ct1Acknowledged.into_pb, Chunked.SendCt.Ct1Acknowledged.from_pb,
      hdec.2, ENCAPSULATION_KEY_SIZE,
      fromPb_intoPb_ctCt1Sent hAu uc huc, decoderFromPbStateDecode_ok hdec,
      Bind.bind, Except.bind]

def ChOk.ct2Sampled {P : PolyApi} {Au : AuthApi} (s : Chunked.SendCt.Ct2Sampled P Au) : Prop :=
  EncOk P s.sending_ct2

theorem fromPb_intoPb_ct2Sampled {P : PolyApi} {Au : AuthApi} (hAu : AuOk Au)
    (s : Chunked.SendCt.Ct2Sampled P Au)
    (h : ChOk.ct2Sampled s) :
    Chunked.SendCt.Ct2Sampled.from_pb P Au s.into_pb = .ok s := by
  cases s with
  | mk uc sending_ct2 =>
    have henc : EncOk P sending_ct2 := h
    simp [Chunked.SendCt.Ct2Sampled.into_pb, Chunked.SendCt.Ct2Sampled.from_pb,
      fromPb_intoPb_ctCt2Sent hAu uc, encoderFromPbStateDecode_ok henc,
      Bind.bind, Except.bind]

/-- Per-variant side conditions under which `States.from_pb` inverts `States.into_pb`. -/
def _root_.CryptoVerification.LibsignalSpqrV1.States.WF {P : PolyApi} {Au : AuthApi} :
    States P Au → Prop
  | .keysUnsampled _ => True
  | .keysSampled s => ChOk.keysSampled s
  | .headerSent s => ChOk.headerSent s
  | .ct1Received s => ChOk.ct1Received s
  | .ekSentCt1Received s => ChOk.ekSentCt1Received s
  | .noHeaderReceived s => ChOk.noHeaderReceived s
  | .headerReceived s => ChOk.headerReceived s
  | .ct1Sampled s => ChOk.ct1Sampled s
  | .ekReceivedCt1Sampled s => ChOk.ekReceivedCt1Sampled s
  | .ct1Acknowledged s => ChOk.ct1Acknowledged s
  | .ct2Sampled s => ChOk.ct2Sampled s

/-- `States.from_pb` inverts `States.into_pb` on well-formed states. -/
theorem states_from_pb_into_pb {P : PolyApi} {Au : AuthApi} (hAu : AuOk Au) (st : States P Au)
    (h : st.WF) : States.from_pb P Au st.into_pb = .ok st := by
  cases st with
  | keysUnsampled s =>
    simp [States.into_pb, States.from_pb, fromPb_intoPb_keysUnsampled hAu s,
      Functor.map, Except.map]
  | keysSampled s =>
    simp [States.into_pb, States.from_pb, fromPb_intoPb_keysSampled hAu s h,
      Functor.map, Except.map]
  | headerSent s =>
    simp [States.into_pb, States.from_pb, fromPb_intoPb_headerSent hAu s h,
      Functor.map, Except.map]
  | ct1Received s =>
    simp [States.into_pb, States.from_pb, fromPb_intoPb_ct1Received hAu s h,
      Functor.map, Except.map]
  | ekSentCt1Received s =>
    simp [States.into_pb, States.from_pb, fromPb_intoPb_ekSentCt1Received hAu s h,
      Functor.map, Except.map]
  | noHeaderReceived s =>
    simp [States.into_pb, States.from_pb, fromPb_intoPb_noHeaderReceived hAu s h,
      Functor.map, Except.map]
  | headerReceived s =>
    simp [States.into_pb, States.from_pb, fromPb_intoPb_headerReceived hAu s h,
      Functor.map, Except.map]
  | ct1Sampled s =>
    simp [States.into_pb, States.from_pb, fromPb_intoPb_ct1Sampled hAu s h,
      Functor.map, Except.map]
  | ekReceivedCt1Sampled s =>
    simp [States.into_pb, States.from_pb, fromPb_intoPb_ekReceivedCt1Sampled hAu s h,
      Functor.map, Except.map]
  | ct1Acknowledged s =>
    simp [States.into_pb, States.from_pb, fromPb_intoPb_ct1Acknowledged hAu s h,
      Functor.map, Except.map]
  | ct2Sampled s =>
    simp [States.into_pb, States.from_pb, fromPb_intoPb_ct2Sampled hAu s h,
      Functor.map, Except.map]

theorem spqrAuthApi_auOk (F : ShaCompress) : AuOk (spqrAuthApi F) := by
  intro a
  exact Authenticator.fromPb_intoPb a

/-- `Erasure.EncInv` implies `EncOk spqrPolyApi` for messages of length in `[32, 2 ^ 20]`. -/
theorem spqr_encOk_of_EncInv (msg : List (BitVec 8)) (e : PolyEncoder) (he : Erasure.EncInv msg e)
    (hlen : msg.length ≤ 2 ^ 20) (hshort : 32 ≤ msg.length) : EncOk spqrPolyApi e := by
  let _ := hlen
  unfold EncOk spqrPolyApi protoPolyEncoderToPb pbToProtoPolyEncoder
  rcases e with ⟨idx, s⟩
  rcases he with hs | ⟨polys, hs, hlen16, hpoly⟩
  · simp only at hs
    subst hs
    have hlen_mp : (Erasure.msgPoints msg).length = 16 := by simp [Erasure.msgPoints]
    have hne_mp : Erasure.msgPoints msg ≠ [] := by
      intro h0
      rw [h0] at hlen_mp
      simp at hlen_mp
    simp [PolyEncoder.intoPb, PolyEncoder.fromPb, hlen_mp, hne_mp, NUM_POLYS, CHUNK_SIZE,
      decodePbPoints_map, Bind.bind, Except.bind, pure, Except.pure, Except.mapError]
  · simp only at hs
    subst hs
    have hne : ∀ p ∈ polys, p.coefficients ≠ [] := by
      intro p hp
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hp
      have hc := (hpoly j hj).1
      have hpos := needed_pos hshort j
      intro hnil
      rw [hnil] at hc
      simp at hc
      omega
    simp [PolyEncoder.intoPb, PolyEncoder.fromPb, hlen16, NUM_POLYS, CHUNK_SIZE,
      decodePbPolys_map polys hne, Bind.bind, Except.bind, pure, Except.pure, Except.mapError]

/-- `Erasure.DecInv` implies `DecOk spqrPolyApi (msg.length / 2)` for messages of length `≤ 2 ^ 20`. -/
theorem spqr_decOk_of_DecInv (msg : List (BitVec 8)) (S : Finset Nat) (d : PolyDecoder)
    (hd : Erasure.DecInv msg S d) (hlen : msg.length ≤ 2 ^ 20) (n : Nat) (hn : msg.length / 2 = n) :
    DecOk spqrPolyApi n d := by
  refine ⟨?_, ?_⟩
  · rcases d with ⟨ptsNeeded, pts, isComplete⟩
    have hsort : ∀ s ∈ pts, (s.vec.map fun pt => pt.x.value.toNat).Pairwise (· < ·) := by
      intro s hs
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hs
      exact hd.sorted j hj
    have hl : pts.length = 16 := hd.len
    have hpn : (BitVec.ofNat 32 ptsNeeded).toNat = ptsNeeded := by
      have hp := hd.ptsNeeded
      simp only at hp
      rw [BitVec.toNat_ofNat]
      omega
    simp [spqrPolyApi, protoPolyDecoderToPb, pbToProtoPolyDecoder,
      PolyDecoder.intoPb, PolyDecoder.fromPb, hl, decodeDecoderPbPts_map pts hsort, hpn,
      Bind.bind, Except.bind, pure, Except.pure, Except.mapError]
  · simp [spqrPolyApi, protoPolyDecoderToPb, PolyDecoder.intoPb, hd.ptsNeeded, hn]

theorem spqrDeps_statesFromPb_statesIntoPb (F : ShaCompress) (K : MlKem)
    (st : States spqrPolyApi (spqrAuthApi F)) (h : st.WF) :
    (spqrDeps F K).statesFromPb ((spqrDeps F K).statesIntoPb st) = .ok st := by
  unfold spqrDeps
  simp only [states_from_pb_into_pb (spqrAuthApi_auOk F) st h, liftStatesResult]

/-- End-to-end state round-trip: `decodeState` and `statesFromPb` recover `st` from the protobuf
bytes written by `Top.send` and `Top.recv`. -/
theorem decodeState_spqrDeps_statesFromPb (F : ShaCompress) (K : MlKem)
    (st : States spqrPolyApi (spqrAuthApi F)) (h : st.WF)
    (vn : Option VersionNegotiationPB) (ch : Option ChainPB)
    (hlen : ((spqrDeps F K).encodeState
      { inner := some ((spqrDeps F K).statesIntoPb st), versionNegotiation := vn,
        chain := ch }).length < 2 ^ 64) :
    decodeState (spqrDeps F K) ((spqrDeps F K).encodeState
        { inner := some ((spqrDeps F K).statesIntoPb st), versionNegotiation := vn,
          chain := ch }) =
      .ok { inner := some ((spqrDeps F K).statesIntoPb st), versionNegotiation := vn,
            chain := ch } ∧
    (spqrDeps F K).statesFromPb ((spqrDeps F K).statesIntoPb st) = .ok st := by
  exact ⟨decodeState_spqrDeps_encodeState F K
      { inner := some ((spqrDeps F K).statesIntoPb st), versionNegotiation := vn, chain := ch }
      hlen,
    spqrDeps_statesFromPb_statesIntoPb F K st h⟩

end CryptoVerification.SpqrV1Sync.Codec
