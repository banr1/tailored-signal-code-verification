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
import LibsignalBinary.Proofs.SpqrV1Sync.ErasureRoundTrip

/-!
# Erasure-Code Well-Formedness (`PolyDecoder.new`, `nextChunk`, `encodeBytes`)

Proves `DecFreshStmt` (`st_decFresh`), `EncNextStmt` (`st_encNext`), and `EncNewStmt` (`st_encNew`)
for `EncWF` and `DecWF`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.SendTotal

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync.InSync

private def msgPtsAt (msg : Bytes) (s : ℕ) : List Point :=
  (List.range 16).map fun j =>
    ⟨(List.range (Erasure.needed (2 * s) j)).map fun k => Erasure.msgVal msg (16 * k + j)⟩

private theorem needed_two_mul_succ (s j : ℕ) (hj : j < 16) :
    Erasure.needed (2 * (s + 1)) j =
      if j = s % 16 then Erasure.needed (2 * s) j + 1 else Erasure.needed (2 * s) j := by
  simp only [Erasure.needed, Nat.mul_div_right _ (by decide : 0 < 2)]
  split <;> split <;> split <;> omega

private theorem distributeMsgChunks_step (msg : Bytes) :
    ∀ (rem s : ℕ), 2 * (s + rem) = msg.length →
      PolyEncoder.distributeMsgChunks s (msg.drop (2 * s)) (msgPtsAt msg s) =
        .ok (msgPtsAt msg (s + rem))
  | 0, s, h => by
    have hd : msg.drop (2 * s) = [] := List.drop_eq_nil_of_le (by omega)
    rw [hd]
    simp [PolyEncoder.distributeMsgChunks]
  | rem + 1, s, h => by
    have h0 : 2 * s < msg.length := by omega
    have h1 : 2 * s + 1 < msg.length := by omega
    have hd : msg.drop (2 * s) = msg[2 * s] :: msg[2 * s + 1] :: msg.drop (2 * (s + 1)) := by
      have h2 : 2 * s + 1 + 1 = 2 * (s + 1) := by omega
      rw [← List.cons_getElem_drop_succ (h := h0), ← List.cons_getElem_drop_succ (h := h1), h2]
    have hlen : (msgPtsAt msg s).length = 16 := by simp [msgPtsAt]
    have hpoly : s % 16 < (msgPtsAt msg s).length := by rw [hlen]; omega
    have hget? : (msgPtsAt msg s)[s % 16]? = some ((msgPtsAt msg s)[s % 16]'hpoly) :=
      List.getElem?_eq_getElem hpoly
    have hval : GF16.new ((msg[2 * s].zeroExtend 16 <<< 8) + msg[2 * s + 1].zeroExtend 16) =
        Erasure.msgVal msg s := by
      simp [Erasure.msgVal, List.getD, List.getElem?_eq_getElem h0, List.getElem?_eq_getElem h1]
    have hset : (msgPtsAt msg s).set (s % 16)
        { value := ((msgPtsAt msg s)[s % 16]'hpoly).value ++ [Erasure.msgVal msg s] } =
        msgPtsAt msg (s + 1) := by
      apply List.ext_getElem
      · simp [msgPtsAt]
      · intro j hj1 hj2
        have hj : j < 16 := by simpa [msgPtsAt] using hj2
        rw [List.getElem_set]
        by_cases hjeq : s % 16 = j
        · subst hjeq
          simp only [↓reduceIte, msgPtsAt, List.getElem_map, List.getElem_range]
          rw [needed_two_mul_succ s (s % 16) (by omega)]
          simp only [↓reduceIte, List.range_succ, List.map_append]
          have hdiv : Erasure.needed (2 * s) (s % 16) = s / 16 := by
            simp [Erasure.needed, Nat.mul_div_right _ (by decide : 0 < 2)]
          have hidx : 16 * Erasure.needed (2 * s) (s % 16) + s % 16 = s := by omega
          simp [hidx]
        · have hjne : j ≠ s % 16 := Ne.symm hjeq
          simp only [hjeq, ↓reduceIte, msgPtsAt, List.getElem_map, List.getElem_range]
          rw [needed_two_mul_succ s j hj]
          simp only [hjne, ↓reduceIte]
    rw [hd]
    unfold PolyEncoder.distributeMsgChunks
    simp only [hlen, hget?, hval, hset]
    have heq : s + (rem + 1) = (s + 1) + rem := by omega
    rw [heq]
    exact distributeMsgChunks_step msg rem (s + 1) (by omega)

/-- `PolyDecoder.new` on an even byte length produces `16` empty point sets satisfying
`DecWF (len / 2)`. -/
theorem st_decFresh : DecFreshStmt := by
  intro len heven
  refine ⟨{ ptsNeeded := len / 2, pts := List.replicate 16 SortedSetPt.new, isComplete := false }, ?_, ?_⟩
  · unfold PolyDecoder.new PolyDecoder.newWithPolyCount
    have hne : (len % 2 != 0) = false := by simp [heven]
    rw [hne]
    rfl
  · refine ⟨rfl, by simp, ?_⟩
    intro j hj
    simp only [List.getElem_replicate, SortedSetPt.new, List.map_nil, List.Pairwise.nil]

/-- `PolyEncoder.nextChunk` succeeds and preserves `EncWF len` when `len ≤ 2 ^ 20`. -/
theorem st_encNext : EncNextStmt := by
  rintro len e ⟨msg, hinv, rfl⟩ hlen
  obtain ⟨e', hrun, hinv'⟩ := Erasure.runChunks_spec msg hlen 1 e hinv
  simp only [Erasure.runChunks, Erasure.honestIdxs, List.map] at hrun
  cases hnc : e.nextChunk with
  | error p =>
    rw [hnc] at hrun
    cases hrun
  | ok pair =>
    rcases pair with ⟨e1, c⟩
    rw [hnc] at hrun
    dsimp only [Bind.bind, Except.bind, pure, Except.pure] at hrun
    injection hrun with hp
    injection hp with heq _
    subst heq
    exact ⟨e1, c, rfl, msg, hinv', rfl⟩

/-- `PolyEncoder.encodeBytes` succeeds on even-length messages `≤ 2 ^ 20` bytes and establishes
`EncWF msg.length`. -/
theorem st_encNew : EncNewStmt := by
  intro msg heven hlen
  unfold PolyEncoder.encodeBytes PolyEncoder.encodeBytesBase
  have hmod : (msg.length % 2 != 0) = false := by simp [heven]
  have hgt : ¬ (msg.length > (1 <<< 16) * NUM_POLYS) := by
    have hc : (1 <<< 16) * NUM_POLYS = 1048576 := by decide
    omega
  have hinit : List.replicate NUM_POLYS ({ value := [] } : Point) = msgPtsAt msg 0 := by
    apply List.ext_getElem
    · simp [NUM_POLYS, CHUNK_SIZE, msgPtsAt]
    · intro j hj1 _
      have hj : j < 16 := by simpa [NUM_POLYS, CHUNK_SIZE] using hj1
      have hn0 : Erasure.needed 0 j = 0 := by simp [Erasure.needed]
      simp [msgPtsAt, hn0]
  have hdist : PolyEncoder.distributeMsgChunks 0 msg (msgPtsAt msg 0) =
      .ok (msgPtsAt msg (msg.length / 2)) := by
    simpa using distributeMsgChunks_step msg (msg.length / 2) 0 (by omega)
  have hfin : msgPtsAt msg (msg.length / 2) = Erasure.msgPoints msg := by
    have h2 : 2 * (msg.length / 2) = msg.length := by omega
    unfold msgPtsAt Erasure.msgPoints
    rw [h2]
  rw [hmod]
  simp only [Bool.false_eq_true, ↓reduceIte, hgt, hinit]
  rw [hdist, hfin]
  exact ⟨{ idx := 0#32, s := .points (Erasure.msgPoints msg) }, rfl, msg, Or.inl rfl, rfl⟩

end CryptoVerification.SpqrV1Sync.SendTotal
