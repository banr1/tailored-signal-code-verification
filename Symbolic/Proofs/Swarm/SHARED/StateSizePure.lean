/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.SpecLemmas.ProofHubsPure
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Model
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Assemble

/-!
# SPQR V1 Serialized State-Size Bounds

Checked by Lean.

Establishes byte-length bounds on `KeyHistory`, `Chain`, `Authenticator`, `States`, and
`Proto.encodeState` across SPQR V1 initialization, send, and receive transitions.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Top.StateSize.SymP3

open CryptoGames.HMAC (toBEBytes)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1

theorem except_bind_eq_ok {ε α β : Type} {m : Except ε α} {f : α → Except ε β} {b : β}
    (h : (m >>= f) = Except.ok b) : ∃ a, m = Except.ok a ∧ f a = Except.ok b := by
  cases m with
  | error _ => contradiction
  | ok a => exact ⟨a, rfl, h⟩
theorem toBEBytes_length {w : Nat} (n : Nat) (x : BitVec w) :
    (toBEBytes n x).length = n := by
  unfold toBEBytes; simp
theorem KeyHistory.add_length_le (kh : KeyHistory) (k : BitVec 32 × Bytes) (params : ChainParamsPB)
    (hk : k.2.length ≤ 32) :
    (kh.add k params).data.length ≤ kh.data.length + 36 := by
  unfold KeyHistory.add; simp only [List.length_append, toBEBytes_length]; omega
theorem KeyHistory.remove_length_le (kh : KeyHistory) (i : Nat) (params : ChainParamsPB) :
    (kh.remove i params).data.length ≤ kh.data.length := by
  unfold KeyHistory.remove; split <;> simp only [List.length_take] <;> omega
theorem KeyHistory.gcLoop_length_le (kh : KeyHistory) (th : Bytes) (params : ChainParamsPB)
    (i : Nat) {kh' : KeyHistory} (h : kh.gcLoop th params i = .ok kh') :
    kh'.data.length ≤ kh.data.length := by
  suffices ∀ n (kh : KeyHistory) i, kh.data.length - i ≤ n → kh.gcLoop th params i = .ok kh' →
      kh'.data.length ≤ kh.data.length from this (kh.data.length - i) kh i (Nat.le_refl _) h
  intro n; induction n with
  | zero =>
    intro kh i hn h; unfold KeyHistory.gcLoop at h; split at h
    · omega
    · simp only [Except.ok.injEq] at h; subst h; exact Nat.le_refl _
  | succ n ih =>
    intro kh i hn h; unfold KeyHistory.gcLoop at h; split at h
    · rename_i hi; split at h
      · contradiction
      · dsimp only [] at h; split at h
        · have hlt := KeyHistory.remove_length_lt kh i params hi
          exact Nat.le_trans (ih (kh.remove i params) i (by omega) h) (by omega)
        · exact ih kh (i + KeyHistory.KEY_SIZE) (by simp only [KeyHistory.KEY_SIZE]; omega) h
    · simp only [Except.ok.injEq] at h; subst h; exact Nat.le_refl _
theorem KeyHistory.gc_length_le (kh : KeyHistory) (ck : BitVec 32) (params : ChainParamsPB)
    {kh' : KeyHistory} (h : kh.gc ck params = .ok kh') :
    kh'.data.length ≤ kh.data.length := by
  unfold KeyHistory.gc at h; dsimp only [] at h; split at h
  · split at h
    · contradiction
    · exact KeyHistory.gcLoop_length_le kh _ params 0 h
  · simp only [Except.ok.injEq] at h; subst h; exact Nat.le_refl _
theorem KeyHistory.getLoop_length_le (kh : KeyHistory) (atIdx : BitVec 32) (want : Bytes)
    (params : ChainParamsPB) (i : Nat) {kh' : KeyHistory} {out : Bytes}
    (h : kh.getLoop atIdx want params i = .ok (kh', out)) :
    kh'.data.length ≤ kh.data.length := by
  suffices ∀ n (kh : KeyHistory) i, kh.data.length - i ≤ n →
      kh.getLoop atIdx want params i = .ok (kh', out) → kh'.data.length ≤ kh.data.length from
    this (kh.data.length - i) kh i (Nat.le_refl _) h
  intro n; induction n with
  | zero =>
    intro kh i hn h; unfold KeyHistory.getLoop at h; split at h
    · omega
    · contradiction
  | succ n ih =>
    intro kh i hn h; unfold KeyHistory.getLoop at h; split at h
    · split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, _⟩; exact KeyHistory.remove_length_le kh i params
      · exact ih kh (i + KeyHistory.KEY_SIZE) (by simp only [KeyHistory.KEY_SIZE]; omega) h
    · contradiction
theorem KeyHistory.get_length_le (kh : KeyHistory) (atIdx ctr : BitVec 32) (params : ChainParamsPB)
    {kh' : KeyHistory} {out : Bytes} (h : kh.get atIdx ctr params = .ok (kh', out)) :
    kh'.data.length ≤ kh.data.length := by
  unfold KeyHistory.get at h; dsimp only [] at h; split at h
  · contradiction
  · split at h
    · contradiction
    · split at h
      · contradiction
      · exact KeyHistory.getLoop_length_le kh atIdx _ params 0 h
theorem ChainEpochDirection.nextKeyInternal_length_le (hkdf : HkdfFn) (next : Bytes) (ctr : BitVec 32)
    {next' : Bytes} {ctr' : BitVec 32} {k : BitVec 32 × Bytes}
    (h : ChainEpochDirection.nextKeyInternal hkdf next ctr = .ok (next', ctr', k)) :
    next'.length ≤ 32 ∧ k.2.length ≤ 32 := by
  unfold ChainEpochDirection.nextKeyInternal at h; split at h
  · contradiction
  · split at h
    · contradiction
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      exact ⟨List.length_take_le _ _, List.length_take_le _ _⟩
theorem ChainEpochDirection.keyAdvanceLoop_length_le (hkdf : HkdfFn) (ed : ChainEpochDirection)
    (atIdx : BitVec 32) (params : ChainParamsPB) {ed' : ChainEpochDirection}
    (h : ed.keyAdvanceLoop hkdf atIdx params = .ok ed') :
    ed'.next.length ≤ max ed.next.length 32 ∧
      ed'.prev.data.length ≤ ed.prev.data.length + 36 * (atIdx.toNat - ed.ctr.toNat) := by
  suffices ∀ n (ed : ChainEpochDirection), atIdx.toNat - ed.ctr.toNat ≤ n →
      ed.keyAdvanceLoop hkdf atIdx params = .ok ed' →
      ed'.next.length ≤ max ed.next.length 32 ∧
        ed'.prev.data.length ≤ ed.prev.data.length + 36 * (atIdx.toNat - ed.ctr.toNat) from
    this (atIdx.toNat - ed.ctr.toNat) ed (Nat.le_refl _) h
  intro n; induction n with
  | zero =>
    intro ed hn h; unfold ChainEpochDirection.keyAdvanceLoop at h; split at h
    · omega
    · split at h
      · contradiction
      · simp only [Except.ok.injEq] at h; subst h; exact ⟨by omega, by omega⟩
  | succ n ih =>
    intro ed hn h; unfold ChainEpochDirection.keyAdvanceLoop at h; split at h
    · rename_i hlt; split at h
      · contradiction
      · rename_i next' ctr' k hnk
        have hctr' := ChainEpochDirection.nextKeyInternal_ctr hkdf ed.next next' ed.ctr ctr' k hnk
        dsimp only [] at h; split at h
        · contradiction
        · obtain ⟨hnk1, hnk2⟩ := ChainEpochDirection.nextKeyInternal_length_le hkdf ed.next ed.ctr hnk
          obtain ⟨ihn, ihp⟩ := ih _ (by dsimp only []; omega) h
          dsimp only [] at ihn ihp
          refine ⟨by omega, ?_⟩
          have hprev : (if ctr' + params.maxOooKeysOrDefault ≥ atIdx then ed.prev.add k params else ed.prev).data.length ≤
              ed.prev.data.length + 36 := by
            split
            · exact KeyHistory.add_length_le ed.prev k params hnk2
            · omega
          have hsub : 36 + 36 * (atIdx.toNat - ctr'.toNat) = 36 * (atIdx.toNat - ed.ctr.toNat) := by
            have : atIdx.toNat - ed.ctr.toNat = (atIdx.toNat - ctr'.toNat) + 1 := by omega
            rw [this, Nat.mul_add]; omega
          omega
    · split at h
      · contradiction
      · simp only [Except.ok.injEq] at h; subst h; exact ⟨by omega, by omega⟩
theorem sum_map_set_le {α : Type} (f : α → Nat) (l : List α) (i : Nat) (x y : α) (d : Nat)
    (hi : l[i]? = some x) (hy : f y ≤ f x + d) :
    ((l.set i y).map f).sum ≤ (l.map f).sum + d := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi
      simp only [List.set_cons_zero, List.map_cons, List.sum_cons]; omega
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      simp only [List.set_cons_succ, List.map_cons, List.sum_cons]
      have := ih i hi; omega
@[simp] theorem Authenticator.rawAuth_intoPb_fromPb (pb : ProtoAuthenticator) :
    rawAuth (Authenticator.fromPb pb).intoPb = rawAuth pb := rfl
theorem Authenticator.update_rawAuth_le (F : CryptoGames.HMAC.ShaState → List (BitVec 8) → CryptoGames.HMAC.ShaState)
    (self : Authenticator) (ep : Epoch) (k : Bytes) :
    rawAuth (self.update F ep k).intoPb ≤ 64 := by
  unfold Authenticator.update Authenticator.intoPb rawAuth; dsimp only []
  have h2 : (hkdfToVecUnchecked F (List.replicate 32 0) (self.rootKey ++ k)
      (Authenticator.updateLabel ++ toBEBytes 8 ep) 64).length ≤ 64 := List.length_take_le _ _
  generalize hkdfToVecUnchecked F (List.replicate 32 0) (self.rootKey ++ k)
      (Authenticator.updateLabel ++ toBEBytes 8 ep) 64 = kdfOut at h2 ⊢
  have h1 : (kdfOut.take 32).length ≤ 32 := List.length_take_le _ _
  simp only [List.length_drop]; omega
theorem Authenticator.new_rawAuth_le (F : CryptoGames.HMAC.ShaState → List (BitVec 8) → CryptoGames.HMAC.ShaState)
    (rootKey : Bytes) (ep : Epoch) :
    rawAuth (Authenticator.new F rootKey ep).intoPb ≤ 64 :=
  Authenticator.update_rawAuth_le F _ ep rootKey
theorem flatMap_ptSerialize_length (l : List Pt) :
    (l.flatMap Pt.serialize).length = 4 * l.length := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.flatMap_cons, List.length_append, ih, List.length_cons]
    have : (Pt.serialize p).length = 4 := rfl; omega
def ptSetRaw (s : SortedSetPt) : Nat := 4 * s.vec.length + 22
theorem map_intoPb_decoder_pts (pts : List SortedSetPt) :
    ((pts.map (fun s => s.vec.flatMap Pt.serialize)).map (fun b => b.length + 22)) =
    pts.map ptSetRaw := by
  induction pts with
  | nil => rfl
  | cons s ss ih =>
    rw [List.map_cons, List.map_cons, List.map_cons, ih]; simp only [ptSetRaw, flatMap_ptSerialize_length]
theorem SortedSetPt.replace_length_le (s : SortedSetPt) (el : Pt) :
    (s.replace el).1.vec.length ≤ s.vec.length + 1 := by
  unfold SortedSetPt.replace; split
  · simp
  · simp only [List.length_append, List.length_cons, List.length_take, List.length_drop]; omega
theorem SortedSetPt.push_length_le (s : SortedSetPt) (el : Pt) :
    (s.push el).1.vec.length ≤ s.vec.length + 1 := by
  unfold SortedSetPt.push; split
  · split
    · simp
    · simp only [List.length_append, List.length_dropLast, List.length_singleton]; omega
    · exact SortedSetPt.replace_length_le s el
  · simp
theorem PolyDecoder.pushChunksExact4_length_le (bs : List (BitVec 8)) (v : SortedSetPt)
    {v' : SortedSetPt} (h : PolyDecoder.pushChunksExact4 bs v = .ok v') :
    4 * v'.vec.length ≤ 4 * v.vec.length + bs.length := by
  suffices ∀ n (bs : List (BitVec 8)) (v : SortedSetPt), bs.length ≤ n →
      PolyDecoder.pushChunksExact4 bs v = .ok v' →
      4 * v'.vec.length ≤ 4 * v.vec.length + bs.length from
    this bs.length bs v (Nat.le_refl _) h
  intro n; induction n with
  | zero =>
    intro bs v hn h; cases bs with
    | nil => unfold PolyDecoder.pushChunksExact4 at h; simp only [Except.ok.injEq] at h; subst h; omega
    | cons _ _ => simp at hn
  | succ n ih =>
    intro bs v hn h
    rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, rest⟩⟩⟩⟩
    · unfold PolyDecoder.pushChunksExact4 at h; simp only [Except.ok.injEq] at h; subst h; omega
    · unfold PolyDecoder.pushChunksExact4 at h; contradiction
    · unfold PolyDecoder.pushChunksExact4 at h; contradiction
    · unfold PolyDecoder.pushChunksExact4 at h; contradiction
    · unfold PolyDecoder.pushChunksExact4 at h
      simp only [Pt.deserialize, Bind.bind, Except.bind] at h
      have hpush := SortedSetPt.push_length_le v
        { x := GF16.new (u16FromBeBytes b0 b1), y := GF16.new (u16FromBeBytes b2 b3) }
      have hih := ih rest _ (by simp only [List.length_cons] at hn; omega) h
      simp only [List.length_cons]; omega
theorem PolyDecoder.decodeDecoderPbPts_sum_le {pbs : List (List (BitVec 8))}
    {outPts : List SortedSetPt}
    (h : PolyDecoder.decodeDecoderPbPts pbs = .ok (.ok outPts)) :
    (outPts.map ptSetRaw).sum ≤ (pbs.map (fun b => b.length + 22)).sum := by
  induction pbs generalizing outPts with
  | nil => unfold PolyDecoder.decodeDecoderPbPts at h; simp only [Except.ok.injEq] at h; subst h; rfl
  | cons pts rest ih =>
    unfold PolyDecoder.decodeDecoderPbPts at h; split at h
    · simp [pure, Except.pure] at h
    · rcases hv : PolyDecoder.pushChunksExact4 pts (SortedSetPt.withCapacity (pts.length / 4)) with e | v
      · simp [hv, Bind.bind, Except.bind] at h
      · simp only [hv, Bind.bind, Except.bind] at h
        rcases htail : PolyDecoder.decodeDecoderPbPts rest with e | tailRes
        · simp [htail] at h
        · simp only [htail] at h
          cases tailRes with
          | error e => simp [pure, Except.pure] at h
          | ok tail =>
            simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
            have hvle := PolyDecoder.pushChunksExact4_length_le pts (SortedSetPt.withCapacity (pts.length / 4)) hv
            have hcap : (SortedSetPt.withCapacity (pts.length / 4)).vec.length = 0 := rfl
            have hih := ih htail
            simp only [List.map_cons, List.sum_cons, ptSetRaw]; omega
theorem PolyDecoder.fromPb_raw_le {pb : PolynomialDecoder} {dec : PolyDecoder}
    (h : PolyDecoder.fromPb (pbToProtoPolyDecoder pb) = .ok (.ok dec)) :
    rawPolyDec (protoPolyDecoderToPb dec.intoPb) ≤ rawPolyDec pb := by
  unfold PolyDecoder.fromPb at h; split at h
  · simp [pure, Except.pure] at h
  · rcases hpts : PolyDecoder.decodeDecoderPbPts (pbToProtoPolyDecoder pb).pts with e | ptsRes
    · simp [hpts, Bind.bind, Except.bind] at h
    · simp only [hpts, Bind.bind, Except.bind] at h
      cases ptsRes with
      | error e => simp [pure, Except.pure] at h
      | ok outPts =>
        simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        have hsum := PolyDecoder.decodeDecoderPbPts_sum_le hpts
        simp only [PolyDecoder.intoPb, protoPolyDecoderToPb, rawPolyDec, map_intoPb_decoder_pts]
        exact hsum
theorem PolyDecoder.new_raw_le {lenBytes : Nat} {dec : PolyDecoder}
    (h : PolyDecoder.new lenBytes = .ok (.ok dec)) :
    rawPolyDec (protoPolyDecoderToPb dec.intoPb) ≤ 352 := by
  unfold PolyDecoder.new PolyDecoder.newWithPolyCount at h; split at h
  · simp [pure, Except.pure] at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    have : rawPolyDec (protoPolyDecoderToPb ({ ptsNeeded := lenBytes / 2, pts := List.replicate 16 SortedSetPt.new, isComplete := false } : PolyDecoder).intoPb) = 352 := rfl
    omega
theorem ptSetRaw_push_le (s : SortedSetPt) (el : Pt) :
    ptSetRaw (s.push el).1 ≤ ptSetRaw s + 4 := by
  have := SortedSetPt.push_length_le s el; simp only [ptSetRaw]; omega
theorem PolyDecoder.addChunkLoop_sum_le (chunk : Chunk) (i rem : Nat) (self : PolyDecoder)
    {self' : PolyDecoder} (h : PolyDecoder.addChunkLoop chunk i rem self = .ok self') :
    (self'.pts.map ptSetRaw).sum ≤ (self.pts.map ptSetRaw).sum + 4 * rem := by
  induction rem generalizing i self with
  | zero => unfold PolyDecoder.addChunkLoop at h; simp only [Except.ok.injEq] at h; subst h; omega
  | succ rem ih =>
    unfold PolyDecoder.addChunkLoop at h; dsimp only [] at h; split at h
    · rename_i polyPts hpoly
      have hih := ih (i + 1) _ h; split at hih
      · dsimp only [] at hih
        have hset := Nat.le_trans hih (Nat.add_le_add_right
          (sum_map_set_le ptSetRaw self.pts _ polyPts _ 4 hpoly (ptSetRaw_push_le polyPts _)) (4 * rem))
        omega
      · omega
    · contradiction
theorem PolyDecoder.addChunk_raw_le {dec dec' : PolyDecoder} {chunk : Chunk}
    (h : dec.addChunk chunk = .ok dec') :
    rawPolyDec (protoPolyDecoderToPb dec'.intoPb) ≤ rawPolyDec (protoPolyDecoderToPb dec.intoPb) + 64 := by
  have hsum := PolyDecoder.addChunkLoop_sum_le chunk 0 16 dec h
  simp only [PolyDecoder.intoPb, protoPolyDecoderToPb, rawPolyDec, map_intoPb_decoder_pts]; omega
theorem flatMap_u16ToBeBytes_length (l : List GF16) :
    (l.flatMap (fun g => u16ToBeBytes g.value)).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.flatMap_cons, List.length_append, ih, List.length_cons]
    have : (u16ToBeBytes g.value).length = 2 := rfl; omega
theorem Poly.serialize_length (p : Poly) :
    p.serialize.length = 2 * p.coefficients.length :=
  flatMap_u16ToBeBytes_length p.coefficients
def pointRaw (pt : Point) : Nat := 2 * pt.value.length + 22
def polyRaw (p : Poly) : Nat := 2 * p.coefficients.length + 22
theorem map_intoPb_encoder_pts (pts : List Point) :
    ((pts.map (fun pt => pt.value.flatMap (fun g => u16ToBeBytes g.value))).map (fun b => b.length + 22)) =
    pts.map pointRaw := by
  induction pts with
  | nil => rfl
  | cons pt ps ih =>
    rw [List.map_cons, List.map_cons, List.map_cons, ih]; simp only [pointRaw, flatMap_u16ToBeBytes_length]
theorem map_intoPb_encoder_polys (polys : List Poly) :
    ((polys.map Poly.serialize).map (fun b => b.length + 22)) =
    polys.map polyRaw := by
  induction polys with
  | nil => rfl
  | cons p ps ih =>
    rw [List.map_cons, List.map_cons, List.map_cons, ih]; simp only [polyRaw, Poly.serialize_length]
theorem Poly.bytesToGF16List_length {bs : List (BitVec 8)} {gs : List GF16}
    (h : Poly.bytesToGF16List bs = .ok gs) : 2 * gs.length = bs.length := by
  suffices ∀ n (bs : List (BitVec 8)) (gs : List GF16), bs.length ≤ n →
      Poly.bytesToGF16List bs = .ok gs → 2 * gs.length = bs.length from
    this bs.length bs gs (Nat.le_refl _) h
  intro n; induction n with
  | zero =>
    intro bs gs hn h; cases bs with
    | nil => unfold Poly.bytesToGF16List at h; simp only [Except.ok.injEq] at h; subst h; rfl
    | cons _ _ => simp at hn
  | succ n ih =>
    intro bs gs hn h
    rcases bs with _ | ⟨b0, _ | ⟨b1, rest⟩⟩
    · unfold Poly.bytesToGF16List at h; simp only [Except.ok.injEq] at h; subst h; rfl
    · unfold Poly.bytesToGF16List at h; contradiction
    · unfold Poly.bytesToGF16List at h
      rcases htail : Poly.bytesToGF16List rest with e | tail
      · simp [htail, Bind.bind, Except.bind] at h
      · simp only [htail, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h; subst h
        have hih := ih rest tail (by simp only [List.length_cons] at hn; omega) htail
        simp only [List.length_cons]; omega
theorem Poly.deserialize_length {bs : List (BitVec 8)} {p : Poly}
    (h : Poly.deserialize bs = .ok (.ok p)) : 2 * p.coefficients.length = bs.length := by
  unfold Poly.deserialize at h; split at h
  · simp [pure, Except.pure] at h
  · rcases hgs : Poly.bytesToGF16List bs with e | gs
    · simp [hgs, Bind.bind, Except.bind] at h
    · simp only [hgs, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h; subst h
      exact Poly.bytesToGF16List_length hgs
theorem PolyEncoder.decodePbPoints_sum_eq {pbs : List Bytes} {out : List Point}
    (h : PolyEncoder.decodePbPoints pbs = .ok (.ok out)) :
    (out.map pointRaw).sum = (pbs.map (fun b => b.length + 22)).sum := by
  induction pbs generalizing out with
  | nil => unfold PolyEncoder.decodePbPoints at h; simp only [Except.ok.injEq] at h; subst h; rfl
  | cons pts rest ih =>
    unfold PolyEncoder.decodePbPoints at h; split at h
    · simp [pure, Except.pure] at h
    · rcases hv : Poly.bytesToGF16List pts with e | v
      · simp [hv, Bind.bind, Except.bind] at h
      · simp only [hv, Bind.bind, Except.bind] at h
        rcases htail : PolyEncoder.decodePbPoints rest with e | tailRes
        · simp [htail] at h
        · simp only [htail] at h
          cases tailRes with
          | error e => simp [pure, Except.pure] at h
          | ok tail =>
            simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
            simp only [List.map_cons, List.sum_cons, pointRaw, Poly.bytesToGF16List_length hv, ih htail]
theorem PolyEncoder.decodePbPolys_sum_eq {pbs : List Bytes} {out : List Poly}
    (h : PolyEncoder.decodePbPolys pbs = .ok (.ok out)) :
    (out.map polyRaw).sum = (pbs.map (fun b => b.length + 22)).sum := by
  induction pbs generalizing out with
  | nil => unfold PolyEncoder.decodePbPolys at h; simp only [Except.ok.injEq] at h; subst h; rfl
  | cons polyBytes rest ih =>
    unfold PolyEncoder.decodePbPolys at h
    rcases hp : Poly.deserialize polyBytes with e | pRes
    · simp [hp, Bind.bind, Except.bind] at h
    · simp only [hp, Bind.bind, Except.bind] at h
      cases pRes with
      | error e => simp [pure, Except.pure] at h
      | ok p =>
        simp only [] at h
        rcases htail : PolyEncoder.decodePbPolys rest with e | tailRes
        · simp [htail] at h
        · simp only [htail] at h
          cases tailRes with
          | error e => simp [pure, Except.pure] at h
          | ok tail =>
            simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
            simp only [List.map_cons, List.sum_cons, polyRaw, Poly.deserialize_length hp, ih htail]
theorem PolyEncoder.fromPb_raw_le {pb : PolynomialEncoder} {enc : PolyEncoder}
    (h : PolyEncoder.fromPb (pbToProtoPolyEncoder pb) = .ok (.ok enc)) :
    rawPolyEnc (protoPolyEncoderToPb enc.intoPb) ≤ rawPolyEnc pb := by
  unfold PolyEncoder.fromPb at h; split at h
  · split at h
    · simp [pure, Except.pure] at h
    · split at h
      · simp [pure, Except.pure] at h
      · rcases hpts : PolyEncoder.decodePbPoints (pbToProtoPolyEncoder pb).pts with e | ptsRes
        · simp [hpts, Bind.bind, Except.bind] at h
        · simp only [hpts, Bind.bind, Except.bind] at h
          cases ptsRes with
          | error e => simp [pure, Except.pure] at h
          | ok out =>
            simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
            have hsum := PolyEncoder.decodePbPoints_sum_eq hpts
            simp only [PolyEncoder.intoPb, protoPolyEncoderToPb, pbToProtoPolyEncoder, rawPolyEnc,
              map_intoPb_encoder_pts, List.map_nil, List.sum_nil] at hsum ⊢; omega
  · split at h
    · rcases hpolys : PolyEncoder.decodePbPolys (pbToProtoPolyEncoder pb).polys with e | polysRes
      · simp [hpolys, Bind.bind, Except.bind] at h
      · simp only [hpolys, Bind.bind, Except.bind] at h
        cases polysRes with
        | error e => simp [pure, Except.pure] at h
        | ok out =>
          simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
          have hsum := PolyEncoder.decodePbPolys_sum_eq hpolys
          simp only [PolyEncoder.intoPb, protoPolyEncoderToPb, pbToProtoPolyEncoder, rawPolyEnc,
            map_intoPb_encoder_polys, List.map_nil, List.sum_nil] at hsum ⊢; omega
    · simp [pure, Except.pure] at h
theorem parallelMult_length (a : GF16) (l : List GF16) :
    (parallelMult a l).length = l.length := by
  fun_induction parallelMult a l with
  | case1 => rfl
  | case2 _ => rfl
  | case3 _ _ _ _ _ _ ih => simp only [List.length_cons, ih]
theorem addAssignCoeffs_length (l1 l2 : List GF16) :
    (Poly.addAssignCoeffs l1 l2).length = max l1.length l2.length := by
  fun_induction Poly.addAssignCoeffs l1 l2 with
  | case1 _ => simp
  | case2 _ _ => simp
  | case3 _ _ _ _ ih => simp only [List.length_cons, ih]; omega
theorem mem_zip_snd {α β : Type} {xs : List α} {ys : List β} {p : α × β}
    (h : p ∈ xs.zip ys) : p.2 ∈ ys := by
  induction xs generalizing ys with
  | nil => simp at h
  | cons x rest ih =>
    cases ys with
    | nil => simp at h
    | cons y yrest =>
      simp only [List.zip_cons_cons, List.mem_cons] at h
      rcases h with rfl | h
      · exact List.Mem.head _
      · exact List.Mem.tail _ (ih h)
theorem lagrangeSum_foldl_length_le (pairs : List (Pt × Poly)) (acc : Poly) (n : Nat)
    (hacc : acc.coefficients.length ≤ n)
    (hpairs : ∀ pair ∈ pairs, pair.2.coefficients.length ≤ n) :
    (pairs.foldl (fun out (pt, poly) =>
      let p := poly.multAssign pt.y
      out.addAssign p) acc).coefficients.length ≤ n := by
  induction pairs generalizing acc with
  | nil => exact hacc
  | cons pair rest ih =>
    simp only [List.foldl_cons]; apply ih
    · have hp : pair.2.coefficients.length ≤ n := hpairs pair (List.Mem.head _)
      simp only [Poly.addAssign, Poly.multAssign, addAssignCoeffs_length, parallelMult_length]; omega
    · intro p hp; exact hpairs p (List.Mem.tail _ hp)
theorem Poly.lagrangeSum_length_le (pts : List Pt) (polys : List Poly) (n : Nat)
    (h : ∀ p ∈ polys, p.coefficients.length ≤ n) :
    (Poly.lagrangeSum pts polys).coefficients.length ≤ n := by
  apply lagrangeSum_foldl_length_le (pts.zip polys) (Poly.zero pts.length) n
  · simp [Poly.zero]
  · intro pair hp; exact h pair.2 (mem_zip_snd hp)
theorem PolyConst.multXdiff_length_le {n : Nat} {self p' : PolyConst n} {diff : GF16}
    (h : self.multXdiff diff = .ok p') :
    p'.coefficients.length ≤ n := by
  unfold PolyConst.multXdiff at h; split at h
  · contradiction
  · rename_i hn0; have hn : n ≠ 0 := by simpa using hn0
    split at h
    · split at h
      · contradiction
      · dsimp only [] at h; simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        simp only [List.length_map, List.length_zip, List.length_cons, List.length_take]; omega
    · contradiction
theorem PolyConst.lagrangeInterpolatePtLoop_length_le (n : Nat) (pts : List Pt) (pix : GF16)
    (j rem : Nat) (p : PolyConst n) (denom : GF16) {p' : PolyConst n} {denom' : GF16}
    (hp : p.coefficients.length ≤ n)
    (h : PolyConst.lagrangeInterpolatePtLoop n pts pix j rem p denom = .ok (p', denom')) :
    p'.coefficients.length ≤ n := by
  induction rem generalizing j p denom with
  | zero =>
    unfold PolyConst.lagrangeInterpolatePtLoop at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h; rcases h with ⟨rfl, _⟩; exact hp
  | succ rem ih =>
    unfold PolyConst.lagrangeInterpolatePtLoop at h; split at h
    · split at h
      · exact ih (j + 1) p denom hp h
      · rcases except_bind_eq_ok h with ⟨p1, hp1, h⟩
        exact ih (j + 1) p1 _ (PolyConst.multXdiff_length_le hp1) h
    · contradiction
theorem PolyConst.lagrangeInterpolatePt_length_le (n : Nat) (pts : List Pt) (i : Nat)
    {cp : PolyConst n} (h : PolyConst.lagrangeInterpolatePt n pts i = .ok cp) :
    cp.coefficients.length ≤ n := by
  unfold PolyConst.lagrangeInterpolatePt at h; split at h
  · split at h
    · contradiction
    · rename_i hn0; have hn : n ≠ 0 := by simpa using hn0
      rcases except_bind_eq_ok h with ⟨⟨p, denom⟩, hloop, h⟩
      simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
      have hp0 : ({ coefficients := GF16.ONE :: List.replicate (n - 1) GF16.ZERO } : PolyConst n).coefficients.length ≤ n := by
        simp only [List.length_cons, List.length_replicate]; omega
      have hpl := PolyConst.lagrangeInterpolatePtLoop_length_le n pts _ 0 n _ GF16.ONE hp0 hloop
      simpa [PolyConst.mult] using hpl
  · contradiction
theorem forall_mem_of_mapM_ok {ε α β : Type} {f : α → Except ε β} {xs : List α} {ys : List β}
    {P : β → Prop} (h : xs.mapM f = .ok ys) (hP : ∀ x y, f x = .ok y → P y) :
    ∀ y ∈ ys, P y := by
  induction xs generalizing ys with
  | nil => simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h; intro _ hm; nomatch hm
  | cons x rest ih =>
    simp only [List.mapM_cons] at h
    rcases except_bind_eq_ok h with ⟨y0, hy0, h⟩
    rcases except_bind_eq_ok h with ⟨tail, htail, h⟩
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; intro y hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hP x y hy0
    · exact ih htail y hm
theorem lagrangePolysForCompletePoints_length_le (n : Nat) {cps : List (PolyConst n)}
    (h : lagrangePolysForCompletePoints n = .ok cps) :
    ∀ p ∈ constPolysToPolys cps, p.coefficients.length ≤ n := by
  unfold lagrangePolysForCompletePoints at h
  have hcps := forall_mem_of_mapM_ok h (fun i cp hi => PolyConst.lagrangeInterpolatePt_length_le n _ i hi)
  intro p hp; simp only [constPolysToPolys, List.mem_map] at hp
  rcases hp with ⟨cp, hcp, rfl⟩; exact hcps cp hcp
theorem Poly.multXdiffAssignTrailingLoop_length (diff : GF16) (i rem : Nat) (coeffs : List GF16)
    {coeffs' : List GF16} (h : Poly.multXdiffAssignTrailingLoop diff i rem coeffs = .ok coeffs') :
    coeffs'.length = coeffs.length := by
  induction rem generalizing i coeffs with
  | zero => unfold Poly.multXdiffAssignTrailingLoop at h; simp only [Except.ok.injEq] at h; subst h; rfl
  | succ rem ih =>
    unfold Poly.multXdiffAssignTrailingLoop at h; split at h
    · contradiction
    · split at h
      · rw [ih (i + 1) _ h, List.length_set]
      · contradiction
theorem Poly.multXdiffAssignTrailing_length (self : Poly) (start : Nat) (diff : GF16)
    {p' : Poly} (h : self.multXdiffAssignTrailing start diff = .ok p') :
    p'.coefficients.length = self.coefficients.length := by
  unfold Poly.multXdiffAssignTrailing at h; dsimp only [] at h; split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rfl
  · rcases except_bind_eq_ok h with ⟨coeffs', hloop, h⟩
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    exact Poly.multXdiffAssignTrailingLoop_length diff start _ self.coefficients hloop
theorem Poly.lagrangeInterpolatePrepareLoop_length (pts : List Pt) (offset i rem : Nat) (p : Poly)
    {p' : Poly} (h : Poly.lagrangeInterpolatePrepareLoop pts offset i rem p = .ok p') :
    p'.coefficients.length = p.coefficients.length := by
  induction rem generalizing i p with
  | zero => unfold Poly.lagrangeInterpolatePrepareLoop at h; simp only [Except.ok.injEq] at h; subst h; rfl
  | succ rem ih =>
    unfold Poly.lagrangeInterpolatePrepareLoop at h; split at h
    · split at h
      · contradiction
      · rcases except_bind_eq_ok h with ⟨p1, hp1, h⟩
        rw [ih (i + 1) p1 h, Poly.multXdiffAssignTrailing_length p _ _ hp1]
    · contradiction
theorem Poly.lagrangeInterpolatePrepare_length (pts : List Pt) {p : Poly}
    (h : Poly.lagrangeInterpolatePrepare pts = .ok p) :
    p.coefficients.length = pts.length + 1 := by
  unfold Poly.lagrangeInterpolatePrepare at h; dsimp only [] at h; split at h
  · contradiction
  · rw [Poly.lagrangeInterpolatePrepareLoop_length pts pts.length 0 pts.length _ h]; simp
theorem Poly.lagrangeCompleteDivLoop_length (pix scale : GF16) (len j rem : Nat) (coeffs : List GF16)
    {coeffs' : List GF16} (h : Poly.lagrangeCompleteDivLoop pix scale len j rem coeffs = .ok coeffs') :
    coeffs'.length = coeffs.length := by
  induction rem generalizing j coeffs with
  | zero => unfold Poly.lagrangeCompleteDivLoop at h; simp only [Except.ok.injEq] at h; subst h; rfl
  | succ rem ih =>
    unfold Poly.lagrangeCompleteDivLoop at h; split at h
    · contradiction
    · dsimp only [] at h; split at h
      · contradiction
      · split at h
        · rw [ih (j + 1) _ h, List.length_set, List.length_set]
        · contradiction
theorem Poly.lagrangeInterpolateComplete_length (self : Poly) (pts : List Pt) (i : Nat)
    {p' : Poly} (h : self.lagrangeInterpolateComplete pts i = .ok p') :
    p'.coefficients.length = self.coefficients.length := by
  unfold Poly.lagrangeInterpolateComplete at h; split at h
  · dsimp only [] at h; split at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rfl
    · rcases except_bind_eq_ok h with ⟨coeffs', hloop, h⟩
      simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
      exact Poly.lagrangeCompleteDivLoop_length _ _ _ 1 _ self.coefficients hloop
  · contradiction
theorem Poly.lagrangeInterpolatePt_length_le (pts : List Pt) (i : Nat) {p : Poly}
    (h : Poly.lagrangeInterpolatePt pts i = .ok p) :
    p.coefficients.length ≤ pts.length := by
  unfold Poly.lagrangeInterpolatePt at h
  rcases except_bind_eq_ok h with ⟨r1, hr1, h⟩
  rcases except_bind_eq_ok h with ⟨r2, hr2, h⟩
  have hlen1 := Poly.lagrangeInterpolatePrepare_length pts hr1
  have hlen2 := Poly.lagrangeInterpolateComplete_length r1 pts i hr2
  cases hc : r2.coefficients with
  | nil => simp [hc] at h
  | cons c rest =>
    simp only [hc, pure, Except.pure, Except.ok.injEq] at h; subst h
    simp only [hc, List.length_cons] at hlen2; dsimp only; omega
theorem fromCompletePoints_const_branch {pts : List Pt} {m : Nat} {p : Poly}
    (hm : pts.length = m)
    (h : ((do
      let cps ← lagrangePolysForCompletePoints m
      let polys ← pure (constPolysToPolys cps)
      pure (Except.ok (Poly.lagrangeSum pts polys))) : Except PolyPanic (Except Unit Poly)) = Except.ok (Except.ok p)) :
    p.coefficients.length ≤ pts.length := by
  rcases except_bind_eq_ok h with ⟨cps, hcps, h⟩
  simp only [Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
  subst h; rw [hm]
  exact Poly.lagrangeSum_length_le pts _ m (lagrangePolysForCompletePoints_length_le m hcps)
theorem Poly.fromCompletePoints_length_le (pts : List Pt) {p : Poly}
    (h : Poly.fromCompletePoints pts = .ok (.ok p)) :
    p.coefficients.length ≤ pts.length := by
  unfold Poly.fromCompletePoints at h; split at h
  · simp [pure, Except.pure] at h
  · dsimp only [] at h; split at h
    · simp only [Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst h; apply Poly.lagrangeSum_length_le; intro _ hm; nomatch hm
    · split at h
      · rename_i _ hn1; exact fromCompletePoints_const_branch (of_decide_eq_true hn1) h
      · split at h
        · rename_i _ _ hn3; exact fromCompletePoints_const_branch (of_decide_eq_true hn3) h
        · split at h
          · rename_i _ _ _ hn5; exact fromCompletePoints_const_branch (of_decide_eq_true hn5) h
          · split at h
            · rename_i _ _ _ _ hn30; exact fromCompletePoints_const_branch (of_decide_eq_true hn30) h
            · split at h
              · rename_i _ _ _ _ _ hn34; exact fromCompletePoints_const_branch (of_decide_eq_true hn34) h
              · split at h
                · rename_i _ _ _ _ _ _ hn36; exact fromCompletePoints_const_branch (of_decide_eq_true hn36) h
                · rcases except_bind_eq_ok h with ⟨polys, hpolys, h⟩
                  simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
                  apply Poly.lagrangeSum_length_le
                  have hall := forall_mem_of_mapM_ok hpolys (fun i q hq => Poly.lagrangeInterpolatePt_length_le _ i hq)
                  simpa using hall
theorem enumeratePts_length (x : Nat) (l : List GF16) :
    (PolyEncoder.enumeratePts x l).length = l.length := by
  induction l generalizing x with
  | nil => rfl
  | cons _ rest ih => simp [PolyEncoder.enumeratePts, ih]
theorem sum_map_drop_of_getElem? {α : Type} (f : α → Nat) (xs : List α) (i : Nat) (x : α)
    (h : xs[i]? = some x) :
    ((xs.drop i).map f).sum = f x + ((xs.drop (i + 1)).map f).sum := by
  induction xs generalizing i with
  | nil => simp at h
  | cons a rest ih =>
    cases i with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h; simp
    | succ i' => simp only [List.getElem?_cons_succ] at h; simpa [List.drop_succ_cons] using ih i' h
theorem PolyEncoder.pointsToPolysLoop_sum_le (pts : List Point) (i rem : Nat) (acc : List Poly)
    {polys : List Poly} (h : PolyEncoder.pointsToPolysLoop pts i rem acc = .ok polys) :
    (polys.map polyRaw).sum ≤ (acc.map polyRaw).sum + ((pts.drop i).map pointRaw).sum := by
  induction rem generalizing i acc with
  | zero => unfold PolyEncoder.pointsToPolysLoop at h; simp only [Except.ok.injEq] at h; subst h; omega
  | succ rem ih =>
    unfold PolyEncoder.pointsToPolysLoop at h; split at h
    · rename_i ptList hpt; dsimp only [] at h
      rcases except_bind_eq_ok h with ⟨res, hres, h⟩
      cases res with
      | error _ => contradiction
      | ok p =>
        have hp := Poly.fromCompletePoints_length_le _ hres
        rw [enumeratePts_length] at hp
        have hih := ih (i + 1) (acc ++ [p]) h
        have hdrop := sum_map_drop_of_getElem? pointRaw pts i ptList hpt
        simp only [List.map_append, List.map_singleton, List.sum_append, List.sum_cons, List.sum_nil] at hih
        simp only [polyRaw, pointRaw] at hp hih hdrop; omega
    · contradiction
theorem PolyEncoder.pointAt_raw_le (self : PolyEncoder) (poly idx : Nat)
    {self' : PolyEncoder} {val : GF16} (h : self.pointAt poly idx = .ok (self', val)) :
    rawPolyEnc (protoPolyEncoderToPb self'.intoPb) ≤ rawPolyEnc (protoPolyEncoderToPb self.intoPb) := by
  unfold PolyEncoder.pointAt at h
  cases hs : self.s with
  | points pts =>
    simp only [hs] at h; split at h
    · split at h
      · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, _⟩; exact Nat.le_refl _
      · rcases hloop : PolyEncoder.pointsToPolysLoop pts 0 NUM_POLYS [] with e | polys
        · simp [hloop, Bind.bind, Except.bind] at h
        · simp only [hloop, Bind.bind, Except.bind, pure, Except.pure] at h; split at h
          · rcases except_bind_eq_ok h with ⟨_, _, h⟩
            simp only [Except.ok.injEq, Prod.mk.injEq] at h; rcases h with ⟨rfl, _⟩
            have hsum := PolyEncoder.pointsToPolysLoop_sum_le pts 0 NUM_POLYS [] hloop
            simp only [List.map_nil, List.sum_nil, List.drop_zero, Nat.zero_add] at hsum
            simp only [PolyEncoder.intoPb, hs, protoPolyEncoderToPb, rawPolyEnc,
              map_intoPb_encoder_pts, map_intoPb_encoder_polys, List.map_nil, List.sum_nil]; omega
          · contradiction
    · simp [Bind.bind, Except.bind] at h
  | polys polys =>
    simp only [hs, Bind.bind, Except.bind, pure, Except.pure] at h; split at h
    · rcases except_bind_eq_ok h with ⟨_, _, h⟩
      simp only [Except.ok.injEq, Prod.mk.injEq] at h; rcases h with ⟨rfl, _⟩
      simp [PolyEncoder.intoPb, hs]
    · contradiction
theorem PolyEncoder.chunkAtLoop_raw_le (idx : BitVec 16) (i rem : Nat) (self : PolyEncoder)
    {self' : PolyEncoder} {vec : List.Vector (BitVec 8) (2 * rem)}
    (h : PolyEncoder.chunkAtLoop idx i rem self = .ok (self', vec)) :
    rawPolyEnc (protoPolyEncoderToPb self'.intoPb) ≤ rawPolyEnc (protoPolyEncoderToPb self.intoPb) := by
  induction rem generalizing i self with
  | zero =>
    unfold PolyEncoder.chunkAtLoop at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h; rcases h with ⟨rfl, _⟩; exact Nat.le_refl _
  | succ rem ih =>
    unfold PolyEncoder.chunkAtLoop at h; dsimp only [] at h
    rcases except_bind_eq_ok h with ⟨⟨self1, p⟩, hp, h⟩
    rcases except_bind_eq_ok h with ⟨⟨self2, tail⟩, htail, h⟩
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h; rcases h with ⟨rfl, _⟩
    exact Nat.le_trans (ih (i + 1) self1 htail) (PolyEncoder.pointAt_raw_le self _ _ hp)
theorem PolyEncoder.nextChunk_raw_le (self : PolyEncoder) {self' : PolyEncoder} {chunk : Chunk}
    (h : self.nextChunk = .ok (self', chunk)) :
    rawPolyEnc (protoPolyEncoderToPb self'.intoPb) ≤ rawPolyEnc (protoPolyEncoderToPb self.intoPb) := by
  unfold PolyEncoder.nextChunk PolyEncoder.chunkAt at h
  rcases except_bind_eq_ok h with ⟨⟨self1, out⟩, hchunk, h⟩
  rcases except_bind_eq_ok hchunk with ⟨⟨self2, data⟩, hloop, hchunk⟩
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h hchunk
  rcases hchunk with ⟨rfl, _⟩; rcases h with ⟨rfl, _⟩
  have hle := PolyEncoder.chunkAtLoop_raw_le (self.idx.setWidth 16) 0 16 self hloop
  cases hs : self2.s <;> simpa [PolyEncoder.intoPb, hs, protoPolyEncoderToPb, rawPolyEnc] using hle
@[simp] private theorem pure_bind_except {ε α β : Type} (x : α) (f : α → Except ε β) :
    (pure x >>= f) = f x := rfl
@[simp] private theorem ok_bind_except {ε α β : Type} (x : α) (f : α → Except ε β) :
    (Except.ok x >>= f) = f x := rfl
@[simp] private theorem except_mapError_eq_ok_iff {ε ε' α : Type} {f : ε → ε'}
    {m : Except ε α} {a : α} : m.mapError f = .ok a ↔ m = .ok a := by cases m <;> simp [Except.mapError]
@[simp] private theorem liftSpqrPanic_eq_ok {α : Type} {r : Except SpqrPanic α} {v : α} :
    liftSpqrPanic r = .ok v ↔ r = .ok v := by cases r <;> simp [liftSpqrPanic]
@[simp] private theorem statesResult_ofPanic_eq_ok {ε α : Type} [ToStatesPanic ε]
    {r : Except ε α} {v : α} : StatesResult.ofPanic r = .ok v ↔ r = .ok v := by
  cases r <;> simp [StatesResult.ofPanic]
theorem PolyDecoder.fromPb_ptsNeeded {pb : PolynomialDecoder} {dec : PolyDecoder}
    (h : PolyDecoder.fromPb (pbToProtoPolyDecoder pb) = .ok (.ok dec)) :
    dec.ptsNeeded = pb.ptsNeeded.toNat := by
  unfold PolyDecoder.fromPb pbToProtoPolyDecoder at h; split at h
  · simp [Pure.pure, Except.pure] at h
  · rcases except_bind_eq_ok h with ⟨ptsRes, _, h2⟩; cases ptsRes with
    | error _ => simp [Pure.pure, Except.pure] at h2
    | ok outPts => have hinj := Except.ok.inj (Except.ok.inj h2); subst hinj; rfl
theorem PolyDecoder.newWithPolyCount_ptsNeeded {lenBytes polys : Nat} {dec : PolyDecoder}
    (h : PolyDecoder.newWithPolyCount lenBytes polys = .ok (.ok dec)) :
    dec.ptsNeeded = lenBytes / 2 := by
  unfold PolyDecoder.newWithPolyCount at h; split at h
  · simp [Pure.pure, Except.pure] at h
  · have hinj := Except.ok.inj (Except.ok.inj h); subst hinj; rfl
theorem PolyDecoder.new_ptsNeeded {lenBytes : Nat} {dec : PolyDecoder}
    (h : PolyDecoder.new lenBytes = .ok (.ok dec)) : dec.ptsNeeded = lenBytes / 2 :=
  PolyDecoder.newWithPolyCount_ptsNeeded h
theorem PolyDecoder.addChunkLoop_ptsNeeded (chunk : Chunk) :
    ∀ (i rem : Nat) (self self' : PolyDecoder),
      PolyDecoder.addChunkLoop chunk i rem self = .ok self' → self'.ptsNeeded = self.ptsNeeded
  | _, 0, self, self', h => by rw [PolyDecoder.addChunkLoop] at h; exact (Except.ok.inj h) ▸ rfl
  | i, rem + 1, self, self', h => by
    rw [PolyDecoder.addChunkLoop] at h; cases hget : self.pts[(chunk.index.toNat * 16 + i) % 16]? with
    | none => rw [hget] at h; contradiction
    | some polyPts =>
      rw [hget] at h; rw [PolyDecoder.addChunkLoop_ptsNeeded chunk (i + 1) rem _ self' h]; split <;> rfl
theorem PolyDecoder.addChunk_ptsNeeded {self self' : PolyDecoder} {chunk : Chunk}
    (h : self.addChunk chunk = .ok self') : self'.ptsNeeded = self.ptsNeeded :=
  PolyDecoder.addChunkLoop_ptsNeeded chunk 0 16 self self' h
theorem PolyDecoder.decodedMessageLoop_length (self : PolyDecoder) (pointsVecs : List (List Pt)) :
    ∀ (i rem : Nat) (polys polys' : List (Option Poly)) (out out' : Bytes),
      PolyDecoder.decodedMessageLoop self pointsVecs i rem polys out = .ok (polys', out') → out'.length = out.length + 2 * rem
  | _, 0, _, _, out, out', h => by
    rw [PolyDecoder.decodedMessageLoop] at h; have hinj := (Prod.mk.inj (Except.ok.inj h)).2; subst hinj; omega
  | i, rem + 1, polys, polys', out, out', h => by
    rw [PolyDecoder.decodedMessageLoop] at h; cases hpts : self.pts[i % 16]? with
    | none => rw [hpts] at h; nomatch h
    | some polyPts =>
      rw [hpts] at h; dsimp only [] at h; have hu16 : ∀ v, (u16ToBeBytes v).length = 2 := fun _ => rfl
      split at h
      · split at h <;> [skip; exact nomatch h]
        have ih := PolyDecoder.decodedMessageLoop_length self pointsVecs (i + 1) rem polys polys' _ out' h
        rw [ih, List.length_append, hu16]; omega
      · split at h <;> [skip; exact nomatch h]; rename_i optPoly _; cases optPoly with
        | some _ =>
          dsimp only [] at h; simp only [pure_bind_except] at h; split at h <;> [skip; exact nomatch h]
          rcases except_bind_eq_ok h with ⟨yVal, _, h2⟩
          have ih := PolyDecoder.decodedMessageLoop_length self pointsVecs (i + 1) rem polys polys' _ out' h2
          rw [ih, List.length_append, hu16]; omega
        | none =>
          dsimp only [] at h; split at h <;> [skip; exact nomatch h]
          rcases except_bind_eq_ok h with ⟨interp, _, h1⟩; simp only [pure_bind_except] at h1
          split at h1 <;> [skip; exact nomatch h1]; rcases except_bind_eq_ok h1 with ⟨yVal, _, h2⟩
          have ih := PolyDecoder.decodedMessageLoop_length self pointsVecs (i + 1) rem _ polys' _ out' h2
          rw [ih, List.length_append, hu16]; omega
theorem PolyDecoder.decodedMessage_length {self : PolyDecoder} {out : Bytes}
    (h : self.decodedMessage = .ok (some out)) : out.length = 2 * self.ptsNeeded := by
  unfold PolyDecoder.decodedMessage at h; dsimp only [] at h; split at h
  · simp [Pure.pure, Except.pure] at h
  · rcases except_bind_eq_ok h with ⟨⟨retNone, pointsVecs⟩, _, h1⟩; dsimp only [] at h1; split at h1
    · simp [Pure.pure, Except.pure] at h1
    · split at h1 <;> [contradiction; skip]
      rcases except_bind_eq_ok h1 with ⟨⟨polys', out1⟩, hloop, h2⟩
      have hinj := Option.some.inj (Except.ok.inj h2); subst hinj
      simpa using PolyDecoder.decodedMessageLoop_length self pointsVecs 0 self.ptsNeeded
        (List.replicate 16 none) polys' [] out1 hloop
private theorem poly_decoderNew_liftM_eq_ok {lenBytes : Nat}
    {res : Except spqrPolyApi.EncodingError spqrPolyApi.PolyDecoder}
    (h : (liftM (spqrPolyApi.decoder_new lenBytes) :
      Except StatesPanic (Except spqrPolyApi.EncodingError spqrPolyApi.PolyDecoder)) = .ok res) :
    PolyDecoder.new lenBytes = .ok res := by
  unfold spqrPolyApi at h; dsimp only [liftM, monadLift, MonadLift.monadLift] at h
  exact except_mapError_eq_ok_iff.mp (liftSpqrPanic_eq_ok.mp h)
theorem expectDecoderNew_raw_le {site : String} {lenBytes : Nat} {dec : PolyDecoder}
    (h : expectDecoderNew spqrPolyApi site lenBytes = .ok dec) :
    rawPolyDec (protoPolyDecoderToPb dec.intoPb) ≤ 352 ∧ dec.ptsNeeded = lenBytes / 2 := by
  unfold expectDecoderNew at h; rcases except_bind_eq_ok h with ⟨res, h1, h2⟩
  have h1' := poly_decoderNew_liftM_eq_ok h1; cases res with
  | error _ => contradiction
  | ok dec' => have hinj := Except.ok.inj h2; subst hinj; exact ⟨PolyDecoder.new_raw_le h1', PolyDecoder.new_ptsNeeded h1'⟩
theorem encoderFromPbStateDecode_raw_le {pb? : Option PolynomialEncoder} {dec : PolyEncoder}
    (h : encoderFromPbStateDecode spqrPolyApi pb? = .ok dec) :
    rawPolyEnc (protoPolyEncoderToPb dec.intoPb) ≤ optRaw rawPolyEnc pb? := by
  unfold encoderFromPbStateDecode spqrPolyApi at h; cases pb? with
  | none => contradiction
  | some pb =>
    dsimp only [] at h; rcases except_bind_eq_ok h with ⟨res, h1, h2⟩
    have h1' := except_mapError_eq_ok_iff.mp (statesResult_ofPanic_eq_ok.mp h1); cases res with
    | error _ => contradiction
    | ok enc' => have hinj := Except.ok.inj h2; subst hinj; exact PolyEncoder.fromPb_raw_le h1'
theorem decoderFromPbStateDecode_raw_le {pb? : Option PolynomialDecoder} {dec : PolyDecoder}
    (h : decoderFromPbStateDecode spqrPolyApi pb? = .ok dec) :
    rawPolyDec (protoPolyDecoderToPb dec.intoPb) ≤ optRaw rawPolyDec pb? ∧
      ∃ d, pb? = some d ∧ dec.ptsNeeded = d.ptsNeeded.toNat := by
  unfold decoderFromPbStateDecode spqrPolyApi at h; cases pb? with
  | none => contradiction
  | some pb =>
    dsimp only [] at h; rcases except_bind_eq_ok h with ⟨res, h1, h2⟩
    have h1' := except_mapError_eq_ok_iff.mp (statesResult_ofPanic_eq_ok.mp h1); cases res with
    | error _ => contradiction
    | ok dec' => have hinj := Except.ok.inj h2; subst hinj; exact ⟨PolyDecoder.fromPb_raw_le h1', pb, rfl, PolyDecoder.fromPb_ptsNeeded h1'⟩
theorem generate_lengths {K : MlKem} {tape tape' : Bytes} {keys : Keys}
    (h : generate K tape = .ok (keys, tape')) :
    keys.ek.length = 1152 ∧ keys.dk.length = 2400 ∧ keys.hdr.length = 64 := by
  unfold generate at h; dsimp only [] at h; split at h <;> [contradiction; skip]
  have hinj := (Prod.mk.inj (Except.ok.inj h)).1; subst hinj
  exact ⟨List.Vector.toList_length _, List.Vector.toList_length _, List.Vector.toList_length _⟩
theorem encaps1_lengths {K : MlKem} {hdr tape tape' : Bytes}
    {ct1 : Ciphertext1} {es : EncapsulationState} {ss : Secret}
    (h : encaps1 K hdr tape = .ok ((ct1, es, ss), tape')) :
    ct1.length = 960 ∧ es.length = 2080 ∧ ss.length = 32 := by
  unfold encaps1 at h; split at h <;> [contradiction; skip]; split at h <;> [contradiction; skip]
  have hinj := (Prod.mk.inj (Except.ok.inj h)).1
  have h1 := (Prod.mk.inj hinj).1; have h2 := (Prod.mk.inj (Prod.mk.inj hinj).2).1
  have h3 := (Prod.mk.inj (Prod.mk.inj hinj).2).2; subst h1; subst h2; subst h3
  exact ⟨List.Vector.toList_length _, List.Vector.toList_length _, List.Vector.toList_length _⟩
theorem ek_matches_header_length {K : MlKem} {ek : EncapsulationKey} {hdr : Header}
    (h : ek_matches_header K ek hdr = true) : ek.length = 1152 := by
  unfold ek_matches_header MlKem.validPkBytes at h
  exact of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).2
@[local simp] private theorem spqrPolyApi_encoder_into_pb (enc : spqrPolyApi.PolyEncoder) :
    spqrPolyApi.encoder_into_pb enc = protoPolyEncoderToPb (PolyEncoder.intoPb enc) := rfl
@[local simp] private theorem spqrPolyApi_encoder_into_pb' (enc : PolyEncoder) :
    spqrPolyApi.encoder_into_pb enc = protoPolyEncoderToPb (PolyEncoder.intoPb enc) := rfl
@[local simp] private theorem spqrPolyApi_decoder_into_pb (dec : spqrPolyApi.PolyDecoder) :
    spqrPolyApi.decoder_into_pb dec = protoPolyDecoderToPb (PolyDecoder.intoPb dec) := rfl
@[local simp] private theorem spqrPolyApi_decoder_into_pb' (dec : PolyDecoder) :
    spqrPolyApi.decoder_into_pb dec = protoPolyDecoderToPb (PolyDecoder.intoPb dec) := rfl
@[local simp] private theorem spqrAuthApi_into_pb' {F : ShaCompress} (a : Authenticator) :
    (spqrAuthApi F).into_pb a = Authenticator.intoPb a := rfl
attribute [local simp]
  States.into_pb Chunked.SendEk.KeysUnsampled.into_pb Chunked.SendCt.NoHeaderReceived.into_pb
  Unchunked.SendEk.KeysUnsampled.into_pb Unchunked.SendCt.NoHeaderReceived.into_pb
  rawV1State rawInnerState rawChKeysUnsampled rawChNoHeaderReceived
  rawUcKeysUnsampled rawUcNoHeaderReceived rawPqInner Option.map optRaw_none optRaw_some
def StatesPtsNeededBound {F : ShaCompress} : States spqrPolyApi (spqrAuthApi F) → Prop
  | .headerSent s => s.receiving_ct1.ptsNeeded ≤ 480
  | _ => True
theorem States.init_a_raw_le {F : ShaCompress} {authKey : Bytes}
    {st : States spqrPolyApi (spqrAuthApi F)}
    (h : States.init_a spqrPolyApi (spqrAuthApi F) authKey = .ok st) :
    rawV1State st.into_pb ≤ 72 ∧ StatesPtsNeededBound st := by
  unfold States.init_a Chunked.SendEk.KeysUnsampled.new Unchunked.SendEk.KeysUnsampled.new spqrAuthApi at h
  dsimp only [Bind.bind, Except.bind] at h; have hinj := Except.ok.inj h; subst hinj
  have hauth := Authenticator.new_rawAuth_le F authKey 1#64; refine ⟨?_, trivial⟩; simp; omega
theorem States.init_b_raw_le {F : ShaCompress} {authKey : Bytes}
    {st : States spqrPolyApi (spqrAuthApi F)}
    (h : States.init_b spqrPolyApi (spqrAuthApi F) authKey = .ok st) :
    rawV1State st.into_pb ≤ 424 ∧ StatesPtsNeededBound st := by
  unfold States.init_b at h; rcases except_bind_eq_ok h with ⟨s, hs, hst⟩
  have hst_eq := Except.ok.inj hst; subst hst_eq
  unfold Chunked.SendCt.NoHeaderReceived.new Unchunked.SendCt.NoHeaderReceived.new at hs
  rcases except_bind_eq_ok hs with ⟨decRes, hdec, hs1⟩; rcases except_bind_eq_ok hs1 with ⟨uc, huc, h2⟩
  unfold spqrAuthApi at huc; dsimp only [Bind.bind, Except.bind] at huc
  have huc_eq := Except.ok.inj huc; subst huc_eq
  have hdec' := poly_decoderNew_liftM_eq_ok hdec; cases decRes with
  | error _ => contradiction
  | ok dec =>
    have hinj := Except.ok.inj h2; subst hinj
    have hauth := Authenticator.new_rawAuth_le F authKey 1#64
    have hpoly := PolyDecoder.new_raw_le hdec'; refine ⟨?_, trivial⟩; simp; omega
theorem spqrDeps_initV1Inner_raw_le {F : ShaCompress} {K : MlKem}
    {dir : Direction} {authKey : Bytes} {v1pb : V1State}
    (h : (spqrDeps F K).initV1Inner dir authKey = .ok v1pb) : rawV1State v1pb ≤ 424 := by
  unfold spqrDeps at h; dsimp only at h; cases dir with
  | a2b =>
    cases ha : States.init_a spqrPolyApi (spqrAuthApi F) authKey <;> rw [ha] at h; · contradiction
    have hinj := Except.ok.inj h; subst hinj; have hle := (States.init_a_raw_le ha).1; omega
  | b2a =>
    cases hb : States.init_b spqrPolyApi (spqrAuthApi F) authKey <;> rw [hb] at h; · contradiction
    have hinj := Except.ok.inj h; subst hinj; exact (States.init_b_raw_le hb).1
theorem initInner_spqrDeps_raw_le {F : ShaCompress} {K : MlKem}
    {v : Version} {dir : Direction} {authKey : Bytes} {inner? : Option V1State}
    (h : initInner (spqrDeps F K) v dir authKey = .ok inner?) :
    optRaw rawPqInner (inner?.map PqRatchetState.Inner.v1) ≤ 424 := by
  unfold initInner at h; cases v with
  | v0 => dsimp only at h; have hinj := Except.ok.inj h; subst hinj; simp
  | v1 =>
    dsimp only [Functor.map, Except.map] at h; split at h <;> try contradiction
    rename_i v1pb hv1; have hinj := Except.ok.inj h; subst hinj
    simpa only [Option.map, optRaw_some, rawPqInner] using spqrDeps_initV1Inner_raw_le hv1
theorem encodeState_length_lt_of_rawPqState_le {st : PqRatchetState}
    (h : rawPqState st ≤ 356 * 2 ^ 32 + 2000000) :
    (Proto.encodeState st).length < 2 ^ 61 ∧ (Proto.encodeState st).length < 2 ^ 62 - 10 ∧
      (Proto.encodeState st).length < 2 ^ 63 ∧ (Proto.encodeState st).length < 2 ^ 64 := by
  have h1 := encodeState_length_le_rawPqState st; omega

end CryptoVerification.SpqrV1.Top.StateSize.SymP3
