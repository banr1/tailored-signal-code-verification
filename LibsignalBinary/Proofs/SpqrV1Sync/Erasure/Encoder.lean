/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1Sync.ErasureDefs

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1Sync.Erasure

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync.GF16Field
open Polynomial

/-! ## `EncodeBytes` helpers -/

namespace EncodeBytes

def msgPointsPrefix (msg : List (BitVec 8)) (i : Nat) : List Point :=
  (List.range 16).map fun j =>
    ⟨(List.range (needed (2 * i) j)).map fun k => msgVal msg (16 * k + j)⟩

theorem length_msgPointsPrefix (msg : List (BitVec 8)) (i : Nat) :
    (msgPointsPrefix msg i).length = 16 := by
  simp [msgPointsPrefix]

theorem getElem_msgPointsPrefix (msg : List (BitVec 8)) (i j : Nat) (hj : j < 16) :
    (msgPointsPrefix msg i)[j]'(by rw [length_msgPointsPrefix]; exact hj) =
      ⟨(List.range (needed (2 * i) j)).map fun k => msgVal msg (16 * k + j)⟩ := by
  simp [msgPointsPrefix]

theorem needed_zero (j : Nat) : needed 0 j = 0 := by
  simp [needed]

theorem msgPointsPrefix_zero (msg : List (BitVec 8)) :
    msgPointsPrefix msg 0 = List.replicate NUM_POLYS { value := [] } := by
  have h :
      (fun j => ({ value := (List.range (needed (2 * 0) j)).map fun k => msgVal msg (16 * k + j) } : Point)) =
        (fun _ => ({ value := [] } : Point)) := by
    funext j
    simp [needed_zero]
  unfold msgPointsPrefix
  rw [h]
  rfl

theorem needed_two_mul (i j : Nat) :
    needed (2 * i) j = if j < i % 16 then i / 16 + 1 else i / 16 := by
  simp [needed]

theorem needed_at_mod (i : Nat) : needed (2 * i) (i % 16) = i / 16 := by
  rw [needed_two_mul]
  split_ifs <;> omega

theorem needed_succ_mod (i : Nat) : needed (2 * (i + 1)) (i % 16) = i / 16 + 1 := by
  rw [needed_two_mul]
  split_ifs <;> omega

theorem needed_succ_ne (i j : Nat) (hj : j < 16) (hne : j ≠ i % 16) :
    needed (2 * (i + 1)) j = needed (2 * i) j := by
  rw [needed_two_mul, needed_two_mul]
  split_ifs <;> omega

theorem msgPointsPrefix_step (msg : List (BitVec 8)) (i : Nat) :
    (msgPointsPrefix msg i).set (i % 16)
      { value :=
          ((msgPointsPrefix msg i)[i % 16]'(by rw [length_msgPointsPrefix]; omega)).value ++
            [msgVal msg i] } =
      msgPointsPrefix msg (i + 1) := by
  apply List.ext_getElem
  · simp [msgPointsPrefix]
  · intro j hj1 hj2
    have hj : j < 16 := by simpa [msgPointsPrefix] using hj2
    rw [List.getElem_set]
    split
    · next heq =>
      subst heq
      rw [getElem_msgPointsPrefix msg i (i % 16) (by omega),
        getElem_msgPointsPrefix msg (i + 1) (i % 16) (by omega)]
      simp only [Point.mk.injEq]
      rw [needed_at_mod, needed_succ_mod, List.range_succ, List.map_append, List.map_singleton]
      have hdiv : 16 * (i / 16) + i % 16 = i := by omega
      rw [hdiv]
    · next hne =>
      have hne' : j ≠ i % 16 := fun h => hne h.symm
      rw [getElem_msgPointsPrefix msg i j hj, getElem_msgPointsPrefix msg (i + 1) j hj,
        needed_succ_ne i j hj hne']

theorem drop_two_step (msg : List (BitVec 8)) (i : Nat) (h : 2 * i + 1 < msg.length) :
    msg.drop (2 * i) =
      msg.getD (2 * i) 0#8 :: msg.getD (2 * i + 1) 0#8 :: msg.drop (2 * (i + 1)) := by
  have h0 : 2 * i < msg.length := by omega
  have h1 : msg.drop (2 * i) = msg[2 * i] :: msg.drop (2 * i + 1) :=
    List.drop_eq_getElem_cons h0
  have h2 : msg.drop (2 * i + 1) = msg[2 * i + 1] :: msg.drop (2 * i + 2) :=
    List.drop_eq_getElem_cons h
  have hd0 : msg.getD (2 * i) 0#8 = msg[2 * i] := by
    simp [List.getD, List.getElem?_eq_getElem h0]
  have hd1 : msg.getD (2 * i + 1) 0#8 = msg[2 * i + 1] := by
    simp [List.getD, List.getElem?_eq_getElem h]
  have hidx : 2 * i + 2 = 2 * (i + 1) := by omega
  rw [h1, h2, hd0, hd1, hidx]

theorem distributeMsgChunks_drop (msg : List (BitVec 8)) :
    ∀ (m i : Nat), 2 * i + 2 * m = msg.length →
      PolyEncoder.distributeMsgChunks i (msg.drop (2 * i)) (msgPointsPrefix msg i) =
        .ok (msgPoints msg)
  | 0, i, h => by
    have hi : 2 * i = msg.length := by omega
    have hdrop : msg.drop (2 * i) = [] := by simp [hi]
    have hpts : msgPointsPrefix msg i = msgPoints msg := by
      simp [msgPointsPrefix, msgPoints, hi]
    rw [hdrop, hpts]
    rfl
  | m + 1, i, h => by
    have hlt : 2 * i + 1 < msg.length := by omega
    rw [drop_two_step msg i hlt]
    unfold PolyEncoder.distributeMsgChunks
    dsimp only
    have hlen : (msgPointsPrefix msg i).length = 16 := length_msgPointsPrefix msg i
    have hget : (msgPointsPrefix msg i)[i % (msgPointsPrefix msg i).length]? =
        some ((msgPointsPrefix msg i)[i % 16]'(by rw [hlen]; omega)) := by
      simp only [hlen]
      exact List.getElem?_eq_getElem (by rw [hlen]; omega)
    rw [hget]
    dsimp only
    simp only [hlen]
    change PolyEncoder.distributeMsgChunks (i + 1) (msg.drop (2 * (i + 1)))
      ((msgPointsPrefix msg i).set (i % 16)
        { value :=
            ((msgPointsPrefix msg i)[i % 16]'(by rw [hlen]; omega)).value ++
              [msgVal msg i] }) = .ok (msgPoints msg)
    rw [msgPointsPrefix_step]
    exact distributeMsgChunks_drop msg m (i + 1) (by omega)

theorem encodeBytes_spec_aux (msg : List (BitVec 8)) (heven : msg.length % 2 = 0)
    (hlen : msg.length ≤ 2 ^ 20) :
    PolyEncoder.encodeBytes msg = .ok (.ok { idx := 0#32, s := .points (msgPoints msg) }) := by
  unfold PolyEncoder.encodeBytes PolyEncoder.encodeBytesBase
  have h1 : (msg.length % 2 != 0) = false := by
    simp [heven]
  have h2 : ¬ (msg.length > (1 <<< 16) * NUM_POLYS) := by
    change ¬ (msg.length > 1048576)
    omega
  simp only [h1, Bool.false_eq_true, ↓reduceIte, h2, ← msgPointsPrefix_zero msg]
  have hdist := distributeMsgChunks_drop msg (msg.length / 2) 0 (by omega)
  simp only [Nat.mul_zero, List.drop_zero] at hdist
  rw [hdist]
  rfl

end EncodeBytes

/-! ## `ChunkAt` helpers -/

namespace ChunkAt

def chunkDataOfVal (val : Nat → BitVec 16) (i rem : Nat) :
    List.Vector (BitVec 8) (2 * rem) :=
  List.Vector.ofFn fun b : Fin (2 * rem) =>
    let v := val (i + b.val / 2)
    if b.val % 2 = 0 then (v >>> 8).setWidth 8 else v.setWidth 8

theorem ofFn_two_mul_succ {α : Type} (rem : Nat) (f : Fin (2 * (rem + 1)) → α) :
    List.Vector.ofFn f =
      f 0 ::ᵥ f (Fin.succ 0) ::ᵥ List.Vector.ofFn (fun b : Fin (2 * rem) => f b.succ.succ) :=
  rfl

theorem chunkDataOfVal_cons (val : Nat → BitVec 16) (i rem : Nat) :
    ((val i >>> 8).setWidth 8) ::ᵥ
      ((val i).setWidth 8) ::ᵥ
        chunkDataOfVal val (i + 1) rem =
      chunkDataOfVal val i (rem + 1) := by
  unfold chunkDataOfVal
  rw [ofFn_two_mul_succ]
  have h0 : (0 : Fin (2 * (rem + 1))).val = 0 := rfl
  have h1 : (Fin.succ (0 : Fin (2 * rem + 1))).val = 1 := rfl
  have htail :
      (fun b : Fin (2 * rem) =>
        let v := val (i + b.succ.succ.val / 2)
        if b.succ.succ.val % 2 = 0 then (v >>> 8).setWidth 8 else v.setWidth 8) =
      (fun b : Fin (2 * rem) =>
        let v := val (i + 1 + b.val / 2)
        if b.val % 2 = 0 then (v >>> 8).setWidth 8 else v.setWidth 8) := by
    funext b
    have hb : b.succ.succ.val = b.val + 2 := rfl
    have hdiv : (b.val + 2) / 2 = b.val / 2 + 1 := by omega
    have hmod : (b.val + 2) % 2 = b.val % 2 := by omega
    have hadd : i + (b.val / 2 + 1) = i + 1 + b.val / 2 := by omega
    simp only [hb, hdiv, hmod, hadd]
  have hdiv1 : 1 / 2 = 0 := rfl
  have hmod1 : (1 % 2 = 0) = False := by decide
  simp only [h0, h1, Nat.add_zero, Nat.zero_mod, ↓reduceIte,
    hdiv1, hmod1, htail]

theorem chunkDataOfVal_zero (val : Nat → BitVec 16) :
    chunkDataOfVal val 0 16 =
      List.Vector.ofFn fun b : Fin 32 =>
        let v := val (b.val / 2)
        if b.val % 2 = 0 then (v >>> 8).setWidth 8 else v.setWidth 8 := by
  unfold chunkDataOfVal
  exact congrArg (@List.Vector.ofFn (BitVec 8) 32) (by
    funext b
    simp only [Nat.zero_add])

theorem chunkAtLoop_spec (msg : List (BitVec 8)) (idx : BitVec 16)
    (hpt : ∀ (e : PolyEncoder), EncInv msg e → ∀ j k, j < 16 → k < 2 ^ 16 →
      ∃ e', e.pointAt j k = .ok (e', (msgPoly msg j).eval (idxPt k)) ∧
        EncInv msg e' ∧ e'.idx = e.idx) :
    ∀ (rem i : Nat) (e : PolyEncoder), EncInv msg e → i + rem ≤ 16 →
      ∃ e', PolyEncoder.chunkAtLoop idx i rem e =
          .ok (e', chunkDataOfVal (fun j => (chunkVal msg idx j).value) i rem) ∧
        EncInv msg e' ∧ e'.idx = e.idx
  | 0, i, e, he, _ => by
    refine ⟨e, ?_, he, rfl⟩
    unfold PolyEncoder.chunkAtLoop chunkDataOfVal
    rfl
  | rem + 1, i, e, he, hle => by
    unfold PolyEncoder.chunkAtLoop
    dsimp only
    have hi : i < 16 := by omega
    have hidx : idx.toNat < 2 ^ 16 := idx.isLt
    have hmod : (idx.toNat * 16 + i) % 16 = i := by omega
    have hdiv : (idx.toNat * 16 + i) / 16 = idx.toNat := by omega
    rw [hmod, hdiv]
    obtain ⟨e1, he1, hinv1, hidx1⟩ := hpt e he i idx.toNat hi hidx
    obtain ⟨e2, he2, hinv2, hidx2⟩ := chunkAtLoop_spec msg idx hpt rem (i + 1) e1 hinv1 (by omega)
    refine ⟨e2, ?_, hinv2, hidx2.trans hidx1⟩
    change (do
      let (self', p) ← e.pointAt i idx.toNat
      let (self'', tail) ← PolyEncoder.chunkAtLoop idx (i + 1) rem self'
      let b0 : BitVec 8 := (p.value >>> 8).setWidth 8
      let b1 : BitVec 8 := p.value.setWidth 8
      return (self'', b0 ::ᵥ b1 ::ᵥ tail)) =
        .ok (e2, chunkDataOfVal (fun j => (chunkVal msg idx j).value) i (rem + 1))
    rw [he1]
    change (do
      let (self'', tail) ← PolyEncoder.chunkAtLoop idx (i + 1) rem e1
      let b0 : BitVec 8 := ((chunkVal msg idx i).value >>> 8).setWidth 8
      let b1 : BitVec 8 := (chunkVal msg idx i).value.setWidth 8
      return (self'', b0 ::ᵥ b1 ::ᵥ tail)) =
        .ok (e2, chunkDataOfVal (fun j => (chunkVal msg idx j).value) i (rem + 1))
    rw [he2]
    change Except.ok (e2,
      (((chunkVal msg idx i).value >>> 8).setWidth 8) ::ᵥ
        ((chunkVal msg idx i).value.setWidth 8) ::ᵥ
          chunkDataOfVal (fun j => (chunkVal msg idx j).value) (i + 1) rem) =
      .ok (e2, chunkDataOfVal (fun j => (chunkVal msg idx j).value) i (rem + 1))
    rw [chunkDataOfVal_cons (fun j => (chunkVal msg idx j).value) i rem]

theorem chunkAt_spec_of_pointAt (msg : List (BitVec 8)) (e : PolyEncoder) (he : EncInv msg e)
    (idx : BitVec 16)
    (hpt : ∀ (e : PolyEncoder), EncInv msg e → ∀ j k, j < 16 → k < 2 ^ 16 →
      ∃ e', e.pointAt j k = .ok (e', (msgPoly msg j).eval (idxPt k)) ∧
        EncInv msg e' ∧ e'.idx = e.idx) :
    ∃ e', e.chunkAt idx = .ok (e', { index := idx, data := chunkData msg idx }) ∧
      EncInv msg e' ∧ e'.idx = e.idx := by
  unfold PolyEncoder.chunkAt
  obtain ⟨e', he', hinv', hidx'⟩ := chunkAtLoop_spec msg idx hpt 16 0 e he (by omega)
  refine ⟨e', ?_, hinv', hidx'⟩
  rw [he', chunkDataOfVal_zero (fun j => (chunkVal msg idx j).value)]
  rfl

end ChunkAt

/-! ## `NextChunk` helpers -/

namespace NextChunk

theorem nextChunk_spec_of_chunkAt (msg : List (BitVec 8)) (e : PolyEncoder)
    (hchunk : ∃ e', e.chunkAt (e.idx.setWidth 16) =
        .ok (e', { index := e.idx.setWidth 16, data := chunkData msg (e.idx.setWidth 16) }) ∧
      EncInv msg e' ∧ e'.idx = e.idx) :
    ∃ e', e.nextChunk =
        .ok (e', { index := e.idx.setWidth 16, data := chunkData msg (e.idx.setWidth 16) }) ∧
      EncInv msg e' ∧ e'.idx = e.idx + 1#32 := by
  obtain ⟨e1, he1, hinv1, hidx1⟩ := hchunk
  refine ⟨({ e1 with idx := e1.idx + 1#32 } : PolyEncoder), ?_, hinv1, by simp [hidx1]⟩
  unfold PolyEncoder.nextChunk
  rw [he1]
  rfl

end NextChunk

/-! ## `DecoderNew` helpers -/

namespace DecoderNew

def initDecoder (lenBytes : Nat) : PolyDecoder :=
  { ptsNeeded := lenBytes / 2
    pts := List.replicate 16 SortedSetPt.new
    isComplete := false }

theorem initDecoder_getElem (lenBytes j : Nat) (hj : j < (initDecoder lenBytes).pts.length) :
    (initDecoder lenBytes).pts[j] = SortedSetPt.new := by
  unfold initDecoder
  exact List.getElem_replicate hj

theorem decoderNew_spec_aux (msg : List (BitVec 8)) (heven : msg.length % 2 = 0) :
    ∃ dec, PolyDecoder.new msg.length = .ok (.ok dec) ∧ DecInv msg ∅ dec := by
  refine ⟨initDecoder msg.length, ?_, ?_⟩
  · unfold PolyDecoder.new PolyDecoder.newWithPolyCount initDecoder
    have h1 : (msg.length % 2 != 0) = false := by simp [heven]
    simp only [h1, Bool.false_eq_true, ↓reduceIte]
    rfl
  · refine
      { ptsNeeded := rfl
        notComplete := rfl
        len := by simp [initDecoder]
        sorted := fun j hj => by
          rw [initDecoder_getElem msg.length j hj]
          simp [SortedSetPt.new]
        onPoly := fun j hj pt hpt => by
          rw [initDecoder_getElem msg.length j hj] at hpt
          simp [SortedSetPt.new] at hpt
        atNode := fun j hj pt hpt => by
          rw [initDecoder_getElem msg.length j hj] at hpt
          simp [SortedSetPt.new] at hpt
        enough := fun j hj => by
          rw [initDecoder_getElem msg.length j hj]
          simp [SortedSetPt.new] }

end DecoderNew

end CryptoVerification.SpqrV1Sync.Erasure
