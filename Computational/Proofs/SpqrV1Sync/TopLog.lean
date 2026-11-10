/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1Sync.RunTight
public import LibsignalBinary.Proofs.SpqrV1Sync.TopInSync
public import Computational.Proofs.CryptoGames.Ratchet.LibsignalSpqrWindowHonest
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.Varint
import LibsignalBinary.Proofs.SpqrV1Sync.TopSize
import ProofLib.BV.WidthNorm

/-!
# SPQR V1 Ghost-Log Agreement, Good Runs, and Honest FIFO Acceptance

Relates the SPQR game's receiver window `spqrWindowOk` to the binary chain invariant via `LogAgree`
(`spqrWindowOk_iff`). Proves via the coupled braid-and-chain invariant `TopInv` that KEM-good
executions of `spqrGame (spqrV1SessionUniformCoins F K)` never set `win` (`goodRun_win_false`), and
that honest FIFO schedules are accepted with the sender's salt (`fifoRun_accepted`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.TopLog

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync.ChainSync
open CryptoGames.LibsignalSession (ShaCompress SpqrLog spqrPos spqrWindowOk)

/-! ## Ghost-log agreement and receiver window -/

private def elp_payloadBytes {P : PolyApi} : MessagePayload P → Bytes
  | .hdr c | .ek c | .ekCt1Ack c | .ct1 c | .ct2 c => encode_chunk c
  | .none | .ct1Ack _ => []

private theorem elp_serialize_eq {P : PolyApi} (m : Message P) (index : BitVec 32) :
    m.serialize index =
      1#8 :: (encode_varint m.epoch [] ++ (encode_varint (index.zeroExtend 64) [] ++
        ((MessageType.from_payload m.payload).toU8 :: elp_payloadBytes m.payload))) := by
  rcases m with ⟨e, p⟩
  cases p <;> simp [Message.serialize, elp_payloadBytes, encode_chunk, encode_varint, List.append_assoc]

private theorem elp_msg_preamble_serialize {P : PolyApi} (m : Message P) (index : BitVec 32)
    (he : m.epoch ≠ 0#64) :
    msg_preamble (m.serialize index) =
      .ok { version := 1#8, epoch := m.epoch, index := index,
            remaining := (MessageType.from_payload m.payload).toU8 :: elp_payloadBytes m.payload } := by
  have h32 : (index.zeroExtend 64).toNat < 2 ^ 32 := by
    simp only [BitVec.zeroExtend, BitVec.toNat_setWidth]
    have := index.isLt; omega
  have hidx : (index.zeroExtend 64).setWidth 32 = index := by
    simp only [BitVec.zeroExtend, BitVec.setWidth_setWidth_of_le _ (by omega : 32 ≤ 64),
      BitVec.setWidth_eq]
  rw [elp_serialize_eq]
  simp only [msg_preamble, Codec.decode_varint_encode_varint, he, h32, hidx, bind, Except.bind,
    ↓reduceIte]

theorem spqrPos_serialize {P : PolyApi} (m : Message P) (idx : BitVec 32) (hE : m.epoch ≠ 0#64) :
    spqrPos (m.serialize idx) = some (m.epoch.toNat, idx.toNat) := by
  have hpre := elp_msg_preamble_serialize m idx hE
  rw [msg_preamble_eq_msgPreamble?] at hpre
  unfold spqrPos
  cases hp : CryptoVerification.LibsignalSpqr.msgPreamble? (m.serialize idx) with
  | none => simp [hp] at hpre
  | some p =>
    simp only [hp, Except.ok.injEq, MsgPreamble.ofLibsignalSpqr] at hpre
    rcases p with ⟨v, ep, ix, rem⟩
    injection hpre with hv hep hix hrem
    subst hep hix
    rfl

theorem spqrPos_msgSerialize (F : ShaCompress) (K : MlKem) (m : (spqrDeps F K).MessageV1)
    (idx : BitVec 32) (hE : (spqrDeps F K).msgEpoch m ≠ 0#64) :
    spqrPos ((spqrDeps F K).msgSerialize m idx) =
      some (((spqrDeps F K).msgEpoch m).toNat, idx.toNat) := by
  exact spqrPos_serialize m idx hE

abbrev posList (ms : List (List (BitVec 8))) : List (ℕ × ℕ) := ms.filterMap spqrPos

/-- Agreement between a party's `SpqrLog` header positions and the chain ghost `(sE, sC, R)`. -/
structure LogAgree (log : SpqrLog) (sE : ℕ) (sC : ℕ → ℕ) (R : ℕ → Finset ℕ) : Prop where
  hsE : sE = log.maxSendEpoch - 1
  hsent : ∀ E i, (E, i) ∈ posList log.sent ↔ 1 ≤ E ∧ 1 ≤ i ∧ i ≤ sC (E - 1)
  hsentParse : ∀ m ∈ log.sent, (spqrPos m).isSome
  hrecvd : ∀ E i, (E, i) ∈ posList log.recvd ↔ 1 ≤ E ∧ i ∈ R (E - 1)

theorem logAgree_init : LogAgree default 0 (fun _ => 0) (fun _ => ∅) := by
  refine ⟨rfl, fun _ _ => ⟨fun h => (by cases h), fun ⟨_, _, _⟩ => (by omega)⟩,
    fun _ hm => (by cases hm), fun _ _ => ⟨fun h => (by cases h), fun ⟨_, hi⟩ => (by simp at hi)⟩⟩

private theorem elc_foldl_max_eq_sup (L : List (ℕ × ℕ)) (a : ℕ) :
    L.foldl (fun m p => max m p.2) a = max a ((L.map Prod.snd).toFinset.sup id) := by
  induction L generalizing a with
  | nil => simp
  | cons p ps ih =>
    simp only [List.foldl_cons, List.map_cons, List.toFinset_cons, Finset.sup_insert, id_eq, ih]
    exact Nat.max_assoc a p.2 _

theorem recvCtr_eq_sup {log : SpqrLog} {sE : ℕ} {sC : ℕ → ℕ} {R : ℕ → Finset ℕ}
    (h : LogAgree log sE sC R) (E : ℕ) (hE : 1 ≤ E) : log.recvCtr E = (R (E - 1)).sup id := by
  unfold SpqrLog.recvCtr
  rw [elc_foldl_max_eq_sup, Nat.zero_max]
  congr 1
  ext i
  simp only [List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq, Prod.exists]
  constructor
  · rintro ⟨E', i', ⟨hmem, rfl⟩, rfl⟩
    exact ((h.hrecvd E' i').mp hmem).2
  · intro hi
    exact ⟨E, i, ⟨(h.hrecvd E i).mpr ⟨hE, hi⟩, rfl⟩, rfl⟩

private theorem elw_sup_mem_of_pos (S : Finset ℕ) (h : 1 ≤ S.sup id) : S.sup id ∈ S := by
  induction S using Finset.induction_on with
  | empty => simp at h
  | @insert a s _ ih =>
    rw [Finset.sup_insert, id_eq] at h ⊢
    rw [Finset.mem_insert]
    rcases le_total (s.sup id) a with hle | hle
    · left; exact sup_eq_left.2 hle
    · right
      rw [sup_eq_right.2 hle] at h ⊢
      exact ih h

/-- Under `LogAgree`, `spqrWindowOk` on header `(E, i)` with `1 ≤ E` matches the chain acceptance
conditions at epoch `E - 1`. -/
theorem spqrWindowOk_iff {log : SpqrLog} {sE : ℕ} {sC : ℕ → ℕ} {R : ℕ → Finset ℕ}
    (h : LogAgree log sE sC R) (m : List (BitVec 8)) (E i : ℕ) (hpos : spqrPos m = some (E, i))
    (hE : 1 ≤ E) :
    spqrWindowOk log m = true ↔
      (sE - 1 ≤ E - 1 ∧ 1 ≤ i ∧ i ∉ R (E - 1) ∧
        ((R (E - 1)).sup id < i → i - (R (E - 1)).sup id ≤ 25000) ∧
        (i < (R (E - 1)).sup id → (R (E - 1)).sup id ≤ i + 2000)) := by
  have hE0 : E ≠ 0 := by omega
  have hctr : log.recvCtr E = (R (E - 1)).sup id := recvCtr_eq_sup h E hE
  have hsE := h.hsE
  have hrecvd : (E, i) ∈ posList log.recvd ↔ i ∈ R (E - 1) := by
    rw [h.hrecvd E i]
    exact and_iff_right hE
  simp only [spqrWindowOk, hpos, hE0, ↓reduceIte, hctr, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, Bool.eq_false_iff, ne_eq, List.contains, List.elem_iff]
  rw [show (E, i) ∈ log.recvd.filterMap spqrPos ↔ i ∈ R (E - 1) from hrecvd]
  constructor
  · rintro ⟨⟨⟨⟨⟨h1, h2⟩, _⟩, h4⟩, h5⟩, h6⟩
    exact ⟨by omega, h2, h6, h4, h5⟩
  · rintro ⟨h1, h2, h6, h4, h5⟩
    have h3 : i ≠ (R (E - 1)).sup id := by
      rintro rfl
      exact h6 (elw_sup_mem_of_pos (R (E - 1)) h2)
    exact ⟨⟨⟨⟨⟨by omega, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩

theorem recvKey_ok_of_window (F : ShaCompress) (authKey : Bytes) (dir : Direction)
    (secret : ℕ → Bytes) (sendCtr : ℕ → ℕ) (recvSet : ℕ → Finset ℕ) (ch : Chain)
    (hch : ChainOk F authKey dir secret sendCtr recvSet ch) (log : SpqrLog) (sC : ℕ → ℕ)
    (hlog : LogAgree log ch.sendEpoch.toNat sC recvSet) (m : List (BitVec 8)) (e : Epoch)
    (idx : BitVec 32) (hpos : spqrPos m = some (e.toNat + 1, idx.toNat))
    (hwin : spqrWindowOk log m = true) (hhi : e.toNat ≤ ch.currentEpoch.toNat)
    (hb : idx.toNat + 2000 ≤ 2 ^ 32) (hR : (recvSet e.toNat).sup id + 2000 ≤ 2 ^ 32) :
    ∃ ch', ch.recvKey (spqrHkdfWith F) e idx =
        .ok (ch', keyAt F (seedAt F authKey secret dir.switch e.toNat) (idx.toNat - 1)) ∧
      ch'.currentEpoch = ch.currentEpoch ∧ ch'.sendEpoch = ch.sendEpoch ∧
      ChainOk F authKey dir secret sendCtr
        (Function.update recvSet e.toNat (insert idx.toNat (recvSet e.toNat))) ch' := by
  have hiff := (spqrWindowOk_iff hlog m (e.toNat + 1) idx.toNat hpos (by omega)).mp hwin
  simp only [Nat.add_sub_cancel] at hiff
  rcases hiff with ⟨hlo, hidx, hnew, hjump, htrim⟩
  have h := recvKey_ok F authKey dir secret sendCtr recvSet ch hch e idx.toNat hlo hhi hidx hnew hjump htrim hb hR
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using h

theorem recvKey_err_of_window (F : ShaCompress) (authKey : Bytes) (dir : Direction)
    (secret : ℕ → Bytes) (sendCtr : ℕ → ℕ) (recvSet : ℕ → Finset ℕ) (ch : Chain)
    (hch : ChainOk F authKey dir secret sendCtr recvSet ch) (log : SpqrLog) (sC : ℕ → ℕ)
    (hlog : LogAgree log ch.sendEpoch.toNat sC recvSet) (m : List (BitVec 8)) (e : Epoch)
    (idx : BitVec 32) (hpos : spqrPos m = some (e.toNat + 1, idx.toNat)) (hidx : 1 ≤ idx.toNat)
    (hwin : spqrWindowOk log m = false) :
    ∀ r, ch.recvKey (spqrHkdfWith F) e idx ≠ .ok r := by
  have hiff := spqrWindowOk_iff hlog m (e.toNat + 1) idx.toNat hpos (by omega)
  simp only [hwin, Bool.false_eq_true, Nat.add_sub_cancel, false_iff] at hiff
  have hout : e.toNat + 1 < ch.sendEpoch.toNat ∨ ch.currentEpoch.toNat < e.toNat ∨
      idx.toNat ∈ recvSet e.toNat ∨
      ((recvSet e.toNat).sup id < idx.toNat ∧ 25000 < idx.toNat - (recvSet e.toNat).sup id) ∨
      (idx.toNat < (recvSet e.toNat).sup id ∧ idx.toNat + 2000 < (recvSet e.toNat).sup id) := by
    by_cases h1 : ch.sendEpoch.toNat - 1 ≤ e.toNat
    · by_cases h3 : idx.toNat ∈ recvSet e.toNat
      · exact .inr (.inr (.inl h3))
      · by_cases h4 : (recvSet e.toNat).sup id < idx.toNat → idx.toNat - (recvSet e.toNat).sup id ≤ 25000
        · have h5 : ¬ (idx.toNat < (recvSet e.toNat).sup id → (recvSet e.toNat).sup id ≤ idx.toNat + 2000) :=
            fun h5 => hiff ⟨h1, hidx, h3, h4, h5⟩
          exact .inr (.inr (.inr (.inr (by omega))))
        · exact .inr (.inr (.inr (.inl (by omega))))
    · exact .inl (by omega)
  have h := recvKey_err F authKey dir secret sendCtr recvSet ch hch e idx.toNat hidx idx.isLt hout
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using h

private theorem els_foldl_max_init {α : Type} (f : α → ℕ) (xs : List α) (a : ℕ) :
    xs.foldl (fun m p => max m (f p)) a = max a (xs.foldl (fun m p => max m (f p)) 0) := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, Nat.zero_max]
    rw [ih (max a (f x)), ih (f x), Nat.max_assoc]

private theorem els_foldl_max_cons {α : Type} (f : α → ℕ) (x : α) (xs : List α) :
    (x :: xs).foldl (fun m p => max m (f p)) 0 =
      max (f x) (xs.foldl (fun m p => max m (f p)) 0) := by
  simp only [List.foldl_cons, Nat.zero_max, els_foldl_max_init f xs (f x)]

private theorem els_maxSendEpoch_cons (log : SpqrLog) (m : List (BitVec 8)) (E i : ℕ)
    (hpos : spqrPos m = some (E, i)) :
    ({ log with sent := m :: log.sent } : SpqrLog).maxSendEpoch = max E log.maxSendEpoch := by
  simp [SpqrLog.maxSendEpoch, hpos, els_foldl_max_cons (fun p : ℕ × ℕ => p.1)]

theorem logAgree_send {log : SpqrLog} {sE : ℕ} {sC : ℕ → ℕ} {R : ℕ → Finset ℕ}
    (h : LogAgree log sE sC R) (m : List (BitVec 8)) (E : ℕ) (hE : 1 ≤ E)
    (hmono : log.maxSendEpoch ≤ E) (hpos : spqrPos m = some (E, sC (E - 1) + 1)) :
    LogAgree { log with sent := m :: log.sent } (E - 1)
      (Function.update sC (E - 1) (sC (E - 1) + 1)) R := by
  refine
    { hsE := ?_
      hsent := fun E' i => ?_
      hsentParse := fun m' hm' => ?_
      hrecvd := h.hrecvd }
  · rw [els_maxSendEpoch_cons log m E (sC (E - 1) + 1) hpos]
    omega
  · simp only [posList, List.filterMap_cons, hpos, List.mem_cons, Prod.mk.injEq, h.hsent E' i]
    by_cases hEE : E' = E
    · subst hEE
      rw [Function.update_self]
      omega
    · by_cases hE'1 : 1 ≤ E'
      · have hne : E' - 1 ≠ E - 1 := by omega
        rw [Function.update_of_ne hne]
        simp [hEE]
      · omega
  · rcases List.mem_cons.mp hm' with rfl | hm'
    · simp [hpos]
    · exact h.hsentParse m' hm'

theorem logAgree_recv {log : SpqrLog} {sE : ℕ} {sC : ℕ → ℕ} {R : ℕ → Finset ℕ}
    (h : LogAgree log sE sC R) (m : List (BitVec 8)) (E i : ℕ) (hE : 1 ≤ E)
    (hpos : spqrPos m = some (E, i)) :
    LogAgree { log with recvd := m :: log.recvd } sE sC
      (Function.update R (E - 1) (insert i (R (E - 1)))) := by
  refine
    { hsE := h.hsE
      hsent := h.hsent
      hsentParse := h.hsentParse
      hrecvd := ?_ }
  intro E' i'
  simp only [posList, List.filterMap_cons_some hpos, List.mem_cons, Prod.mk.injEq, h.hrecvd]
  by_cases hEE : E' = E
  · subst hEE
    simp only [true_and, Function.update_self, Finset.mem_insert]
    exact ⟨fun h' => ⟨hE, h'.imp id And.right⟩,
      fun ⟨_, h'⟩ => h'.imp id (fun hm => ⟨hE, hm⟩)⟩
  · simp only [hEE, false_and, false_or]
    refine ⟨fun ⟨hE', hi'⟩ => ⟨hE', ?_⟩, fun ⟨hE', hi'⟩ => ⟨hE', ?_⟩⟩
    · have hne : E' - 1 ≠ E - 1 := by omega
      rwa [Function.update_of_ne hne]
    · have hne : E' - 1 ≠ E - 1 := by omega
      rwa [Function.update_of_ne hne] at hi'

theorem sendCtr_le_length {log : SpqrLog} {sE : ℕ} {sC : ℕ → ℕ} {R : ℕ → Finset ℕ}
    (h : LogAgree log sE sC R) (E : ℕ) (hE : 1 ≤ E) : sC (E - 1) ≤ log.sent.length := by
  let emb : ℕ ↪ ℕ × ℕ := ⟨fun i => (E, i), fun _ _ heq => (Prod.mk.injEq .. |>.mp heq).2⟩
  let S := (Finset.Icc 1 (sC (E - 1))).map emb
  have hcard : S.card = sC (E - 1) := by
    simp [S, Nat.card_Icc]
  have hsub : S ⊆ (posList log.sent).toFinset := by
    intro p hp
    rcases Finset.mem_map.mp hp with ⟨i, hi, rfl⟩
    rw [Finset.mem_Icc] at hi
    rw [List.mem_toFinset]
    exact (h.hsent E i).mpr ⟨hE, hi.1, hi.2⟩
  calc
    sC (E - 1) = S.card := hcard.symm
    _ ≤ (posList log.sent).toFinset.card := Finset.card_le_card hsub
    _ ≤ (posList log.sent).length := List.toFinset_card_le _
    _ ≤ log.sent.length := List.length_filterMap_le _ _

theorem sendCtr_sum_le_length {log : SpqrLog} {sE : ℕ} {sC : ℕ → ℕ} {R : ℕ → Finset ℕ}
    (h : LogAgree log sE sC R) (n : ℕ) : ∑ e ∈ Finset.range n, sC e ≤ log.sent.length := by
  let emb : (Σ _ : ℕ, ℕ) ↪ ℕ × ℕ :=
    ⟨fun p => (p.1 + 1, p.2), by
      rintro ⟨e₁, i₁⟩ ⟨e₂, i₂⟩ heq
      simp only [Prod.mk.injEq, Sigma.mk.inj_iff, heq_eq_eq] at heq ⊢
      omega⟩
  let S := ((Finset.range n).sigma (fun e => Finset.Icc 1 (sC e))).map emb
  have hcard : S.card = ∑ e ∈ Finset.range n, sC e := by
    simp [S, Finset.card_sigma, Nat.card_Icc]
  have hsub : S ⊆ (posList log.sent).toFinset := by
    intro p hp
    rcases Finset.mem_map.mp hp with ⟨⟨e, i⟩, hmem, rfl⟩
    rw [Finset.mem_sigma, Finset.mem_Icc] at hmem
    rw [List.mem_toFinset]
    exact (h.hsent (e + 1) i).mpr ⟨by omega, hmem.2.1, hmem.2.2⟩
  calc
    ∑ e ∈ Finset.range n, sC e = S.card := hcard.symm
    _ ≤ (posList log.sent).toFinset.card := Finset.card_le_card hsub
    _ ≤ (posList log.sent).length := List.toFinset_card_le _
    _ ≤ log.sent.length := List.length_filterMap_le _ _

theorem recvSet_sup_le {logP logQ : SpqrLog} {sEP sEQ : ℕ} {sCP sCQ : ℕ → ℕ}
    {RP RQ : ℕ → Finset ℕ} (hP : LogAgree logP sEP sCP RP) (hQ : LogAgree logQ sEQ sCQ RQ)
    (hsub : ∀ p ∈ posList logQ.recvd, p ∈ posList logP.sent) (E : ℕ) (hE : 1 ≤ E) :
    (RQ (E - 1)).sup id ≤ sCP (E - 1) := by
  apply Finset.sup_le
  intro i hi
  have hrec : (E, i) ∈ posList logQ.recvd := (hQ.hrecvd E i).mpr ⟨hE, hi⟩
  have hsent : (E, i) ∈ posList logP.sent := hsub (E, i) hrec
  exact ((hP.hsent E i).mp hsent).2.2

theorem spqrWindowOk_congr {log log' : SpqrLog} {m m' : List (BitVec 8)}
    (hs : posList log.sent = posList log'.sent) (hr : posList log.recvd = posList log'.recvd)
    (hm : spqrPos m = spqrPos m') : spqrWindowOk log m = spqrWindowOk log' m' := by
  unfold spqrWindowOk SpqrLog.maxSendEpoch SpqrLog.recvCtr
  unfold posList at hs hr
  rw [hm, hs, hr]

/-! ## Coupled game invariant and `GoodRun` -/

open CryptoVerification.SpqrV1Sync.Braid
open CryptoVerification.SpqrV1Sync.InSync (St Msg Seed)
open CryptoVerification.SpqrV1Sync.TopSync (PartyTop chainCur)
open CryptoGames.LibsignalSM.Corr (SpqrGameState spqrSendStep spqrDeliverStep spqrDir)

def braidParty : CryptoGames.Party → Braid.Party
  | .A => .a
  | .B => .b

def partyDir (P : CryptoGames.Party) : Direction :=
  Direction.ofSpqrDirection (spqrDir P)

theorem partyDir_other (P : CryptoGames.Party) : partyDir P.other = (partyDir P).switch := by
  cases P <;> rfl

/-- Ghost state coupling a tight honest braid run (`RunT`), logged sends, and per-party chain
counters. -/
structure Ghost (F : ShaCompress) where
  e : Epoch
  auth : Authenticator
  c : Coins
  st : CryptoGames.Party → St F
  toP : CryptoGames.Party → List Msg
  sentB : List (Msg × BitVec 32)
  secret : ℕ → Bytes
  sendCtr : CryptoGames.Party → ℕ → ℕ
  recvSet : CryptoGames.Party → ℕ → Finset ℕ

abbrev authOf (k : BitVec 256) : Bytes := CryptoGames.HMAC.keyToBytes32 k

def initGhost (F : ShaCompress) (k : BitVec 256) (stA stB : St F) : Ghost F where
  e := 1#64
  auth := Authenticator.new F (authOf k) 1#64
  c := .init
  st := fun P => match P with | .A => stA | .B => stB
  toP := fun _ => []
  sentB := []
  secret := fun _ => []
  sendCtr := fun _ _ => 0
  recvSet := fun _ _ => ∅

/-- Ghost transition for a successful `send` by `P` with coins `r`. -/
noncomputable def ghostSend (F : ShaCompress) (K : MlKem) (g : Ghost F) (P : CryptoGames.Party)
    (r : BitVec 512) : Ghost F :=
  match (g.st P).send K (coinBytes r) with
  | .ok (out, _) =>
    let E := out.msg.epoch.toNat - 1
    let n := g.sendCtr P E
    { g with
      c := nextCoins F g.c (g.st P) (coinBytes r)
      st := Function.update g.st P out.state
      toP := Function.update g.toP P.other (g.toP P.other ++ [out.msg])
      sentB := g.sentB ++ [(out.msg, BitVec.ofNat 32 (n + 1))]
      secret := match out.key with
        | some es => Function.update g.secret es.epoch.toNat es.secret
        | none => g.secret
      sendCtr := Function.update g.sendCtr P (Function.update (g.sendCtr P) E (n + 1)) }
  | .error _ => g

/-- Ghost transition for a committed, accepted delivery of send `j` to `P`. -/
noncomputable def ghostDeliver (F : ShaCompress) (K : MlKem) (g : Ghost F) (P : CryptoGames.Party)
    (j : ℕ) : Ghost F :=
  match g.sentB[j]? with
  | none => g
  | some (m, i) =>
    match (g.st P).recv K m with
    | .ok out =>
      let E := m.epoch.toNat - 1
      let g1 : Ghost F :=
        { g with
          st := Function.update g.st P out.state
          secret := match out.key with
            | some es => Function.update g.secret es.epoch.toNat es.secret
            | none => g.secret
          recvSet := Function.update g.recvSet P
            (Function.update (g.recvSet P) E (insert i.toNat (g.recvSet P E))) }
      if m = noneMsg (g.e + 1#64) then
        match g.c with
        | .both s r => { g1 with e := g.e + 1#64, auth := authNext F K g.e g.auth s r, c := .init }
        | _ => g1
      else g1
    | .error _ => g

/-- Per-party invariant combining `PartyTop` and `LogAgree` against `g`. -/
def PartyOk (F : ShaCompress) (K : MlKem) (k : BitVec 256) (s : SpqrGameState (List (BitVec 8)))
    (g : Ghost F) (P : CryptoGames.Party) : Prop :=
  ∃ sE, PartyTop F K (authOf k) (partyDir P) g.secret (g.st P) sE (g.sendCtr P) (g.recvSet P)
      (s.st P).1 ∧
    LogAgree (s.st P).2 sE (g.sendCtr P) (g.recvSet P)

/-- Coupled braid, chain, and log invariant for `spqrGame (spqrV1SessionUniformCoins F K)` implying
`s.win = false`. -/
structure TopInv (F : ShaCompress) (K : MlKem) (k : BitVec 256)
    (s : SpqrGameState (List (BitVec 8))) (g : Ghost F) : Prop where
  hrun : RunT F K (authOf k) g.e g.auth g.c (g.st .A) (g.st .B) (g.toP .A) (g.toP .B)
  hparty : ∀ P, PartyOk F K k s g P
  hsize : ∀ P, (s.st P).1.length < 2 ^ 64
  hsecret : ∀ sd rd, g.c = .both sd rd → g.secret g.e.toNat = secOf F K g.e sd rd
  hsentLen : s.sent.length = g.sentB.length
  hlogSent : ∀ P, (s.st P).2.sent.length ≤ s.sent.length
  hsent : ∀ (j : ℕ) (Q : CryptoGames.Party) (msg : List (BitVec 8)) (salt : CryptoGames.HKDF.Salt),
    s.sent[j]? = some (Q, msg, salt) →
    ∃ m i, g.sentB[j]? = some (m, i) ∧ msg = m.serialize i ∧ m ∈ g.toP Q.other ∧
      1 ≤ m.epoch.toNat ∧ m.payload ≠ .ct1Ack false ∧
      1 ≤ i.toNat ∧ i.toNat ≤ g.sendCtr Q (m.epoch.toNat - 1) ∧
      salt = some ⟨keyAt F (seedAt F (authOf k) g.secret (partyDir Q) (m.epoch.toNat - 1))
        (i.toNat - 1), length_keyAt _ _ _⟩
  hepochSent : ∀ n, 2 ≤ n → n ≤ g.e.toNat → ∃ p ∈ g.sentB, p.1.epoch.toNat = n
  hdeliv : ∀ P, ∀ p ∈ posList (s.st P).2.recvd, p ∈ posList (s.st P.other).2.sent
  hwin : s.win = false

/-- KEM correctness event on the encapsulation coins drawn by `P` during a send step. -/
def KemGood (F : ShaCompress) (K : MlKem) (g : Ghost F) (P : CryptoGames.Party) (r : BitVec 512) :
    Prop :=
  ekSide g.e ≠ braidParty P → ∀ (s : Seed) (r' : EncRand), DrawsEnc F g.c (g.st P) s →
    r'.toList = (coinBytes r).take 32 → KemOk K s r'

/-- Reachable executions of `spqrGame` paired with their `Ghost` in which every send satisfies
`KemGood`. -/
inductive GoodRun (F : ShaCompress) (K : MlKem) (k : BitVec 256) :
    SpqrGameState (List (BitVec 8)) → Ghost F → Prop
  | init (stA stB : St F)
      (hA : States.init_a spqrPolyApi (spqrAuthApi F) (authOf k) = .ok stA)
      (hB : States.init_b spqrPolyApi (spqrAuthApi F) (authOf k) = .ok stB) :
      GoodRun F K k
        ⟨fun P => (spqrV1SessionUniformCoins F K).withLog.init (spqrDir P) k, [], false⟩
        (initGhost F k stA stB)
  | send {s : SpqrGameState (List (BitVec 8))} {g : Ghost F} (hr : GoodRun F K k s g)
      (P : CryptoGames.Party) (r : BitVec 512) (hkem : KemGood F K g P r) :
      GoodRun F K k (spqrSendStep (spqrV1SessionUniformCoins F K) s P r).2
        (if (spqrSendStep (spqrV1SessionUniformCoins F K) s P r).2.sent.length = s.sent.length + 1
          then ghostSend F K g P r else g)
  | deliver {s : SpqrGameState (List (BitVec 8))} {g : Ghost F} (hr : GoodRun F K k s g)
      (P : CryptoGames.Party) (j : ℕ) (commit : Bool) :
      GoodRun F K k (spqrDeliverStep (spqrV1SessionUniformCoins F K) s P j commit).2
        (if (spqrDeliverStep (spqrV1SessionUniformCoins F K) s P j commit).2.st P ≠ s.st P
          then ghostDeliver F K g P j else g)

theorem partyTop_sendCtr_fresh {F : ShaCompress} {K : MlKem} {authKey : Bytes} {dir : Direction}
    {secret : ℕ → Bytes} {st : St F} {sendEp : ℕ} {sendCtr : ℕ → ℕ} {recvSet : ℕ → Finset ℕ}
    {bytes : Bytes} (h : PartyTop F K authKey dir secret st sendEp sendCtr recvSet bytes)
    (e : ℕ) (he : chainCur st < e) : sendCtr e = 0 := by
  obtain ⟨vn?, ch?, chE, hw⟩ := h
  exact hw.hok.hfreshSend e (by rw [hw.hcur]; exact he)

theorem epoch_le_of_sent (L : List (Msg × BitVec 32)) (E : ℕ)
    (h : ∀ n, 2 ≤ n → n ≤ E → ∃ p ∈ L, p.1.epoch.toNat = n) : E ≤ L.length + 1 := by
  have hsub : Finset.Icc 2 E ⊆ (L.map fun p => p.1.epoch.toNat).toFinset := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    obtain ⟨p, hp, hpn⟩ := h n hn.1 hn.2
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨p, hp, hpn⟩
  have hcard := Finset.card_le_card hsub
  have h2 := List.toFinset_card_le (L.map fun p => p.1.epoch.toNat)
  rw [Nat.card_Icc] at hcard
  rw [List.length_map] at h2
  omega

theorem TopInv.epoch_le {F : ShaCompress} {K : MlKem} {k : BitVec 256}
    {s : SpqrGameState (List (BitVec 8))} {g : Ghost F} (h : TopInv F K k s g) :
    g.e.toNat ≤ s.sent.length + 1 := by
  rw [h.hsentLen]
  exact epoch_le_of_sent g.sentB g.e.toNat h.hepochSent

theorem TopInv.epoch_lt {F : ShaCompress} {K : MlKem} {k : BitVec 256}
    {s : SpqrGameState (List (BitVec 8))} {g : Ghost F} (h : TopInv F K k s g) (q : ℕ)
    (hq : q + 2000 ≤ 2 ^ 32) (hlen : s.sent.length ≤ q) : g.e.toNat + 2 < 2 ^ 64 := by
  have h1 := h.epoch_le
  omega

theorem runT_epoch_pos {F : ShaCompress} {K : MlKem} {authKey : Bytes} {e : Epoch}
    {auth : Authenticator} {c : Coins} {stA stB : St F} {toA toB : List Msg}
    (hr : RunT F K authKey e auth c stA stB toA toB) : 1 ≤ e.toNat := by
  induction hr <;>
    first
    | assumption
    | decide
    | (simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)

private theorem fcc_inSyncE_chainCur (F : ShaCompress) (K : MlKem) (e : Epoch)
    (auth : Authenticator) (c : Coins) (x y : St F) (toY toX : List Msg)
    (h : InSyncE F K e auth c x y toY toX) (he : 1 ≤ e.toNat) :
    (chainCur x = e.toNat - 1 ∨ (chainCur x = e.toNat ∧ ∃ sd rd, c = .both sd rd)) ∧
      (chainCur y = e.toNat - 1 ∨ (chainCur y = e.toNat ∧ ∃ sd rd, c = .both sd rd)) := by
  have hep := h.hepoch
  have hx := h.hx
  have hy := h.hy
  refine ⟨?_, ?_⟩
  · rcases c with _ | s | ⟨s, r⟩
    · rcases hx with rfl; exact Or.inl rfl
    · rcases hx with ⟨_, _, rfl⟩; exact Or.inl rfl
    · rcases hx with ⟨_, _, rfl⟩ | ⟨_, _, _, _, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | rfl
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inl rfl
      · refine Or.inr ⟨?_, s, r, rfl⟩
        simp only [chainCur, States.epoch, Chunked.SendCt.NoHeaderReceived.epoch,
          TopSync.keyedB, Bool.false_eq_true, ↓reduceIte, BitVec.toNat_add, BitVec.toNat_ofNat]
        omega
  · rcases c with _ | s | ⟨s, r⟩
    · rcases hy with rfl; exact Or.inl rfl
    · rcases hy with ⟨_, _, _, _, rfl⟩ | rfl <;> exact Or.inl rfl
    · refine Or.inr ⟨?_, s, r, rfl⟩
      rcases hy with ⟨_, _, _, _, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, rfl⟩ <;> {
        simp only [chainCur, States.epoch, Chunked.SendCt.Ct1Sampled.epoch,
          Chunked.SendCt.EkReceivedCt1Sampled.epoch, Chunked.SendCt.Ct1Acknowledged.epoch,
          Chunked.SendCt.Ct2Sampled.epoch, TopSync.keyedB, ↓reduceIte]
        omega
      }

theorem inSync_chainCur (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (c : Coins) (stA stB : St F) (toA toB : List Msg) (h : InSync F K e auth c stA stB toA toB)
    (he : 1 ≤ e.toNat) :
    (chainCur stA = e.toNat - 1 ∨ (chainCur stA = e.toNat ∧ ∃ sd rd, c = .both sd rd)) ∧
      (chainCur stB = e.toNat - 1 ∨ (chainCur stB = e.toNat ∧ ∃ sd rd, c = .both sd rd)) := by
  rcases hs : ekSide e with _ | _
  · exact fcc_inSyncE_chainCur F K e auth c stA stB toB toA ((inSync_of_a hs).1 h) he
  · exact (fcc_inSyncE_chainCur F K e auth c stB stA toA toB ((inSync_of_b hs).1 h) he).symm

theorem send_key_fresh (F : ShaCompress) (K : MlKem) (k : BitVec 256) (g : Ghost F)
    (hrun : RunT F K (authOf k) g.e g.auth g.c (g.st .A) (g.st .B) (g.toP .A) (g.toP .B))
    (P : CryptoGames.Party) (r : BitVec 512) (hkem : KemGood F K g P r) (m : Msg)
    (es : EpochSecret) (st' : St F) (tape' : Bytes)
    (hsend : (g.st P).send K (coinBytes r) = .ok ({ msg := m, key := some es, state := st' }, tape')) :
    es.epoch = g.e ∧
      (∃ sd rd, nextCoins F g.c (g.st P) (coinBytes r) = .both sd rd ∧
        es.secret = secOf F K g.e sd rd) ∧
      ∀ Q, chainCur (g.st Q) + 1 = g.e.toNat := by
  have hsync := runT_inSync F K (authOf k) hrun
  have he_pos := runT_epoch_pos hrun
  have htape : 64 ≤ (coinBytes r).length := by rw [coinBytes_length]
  have hcs : CoinStep F K g.e (coinBytes r) g.c (nextCoins F g.c (g.st P) (coinBytes r)) (some es) := by
    cases P with
    | A =>
      obtain ⟨m', key', stA', tape'', hsend', hcs, -⟩ :=
        inSync_sendA_tight F K g.e g.auth g.c (g.st .A) (g.st .B) (g.toP .A) (g.toP .B)
          hsync (coinBytes r) htape (fun hs => hkem (by rw [hs]; decide))
      rw [hsend] at hsend'
      cases hsend'
      exact hcs
    | B =>
      obtain ⟨m', key', stB', tape'', hsend', hcs, -⟩ :=
        inSync_sendB_tight F K g.e g.auth g.c (g.st .A) (g.st .B) (g.toP .A) (g.toP .B)
          hsync (coinBytes r) htape (fun hs => hkem (by rw [hs]; decide))
      rw [hsend] at hsend'
      cases hsend'
      exact hcs
  rcases hcs with ⟨-, hnone⟩ | ⟨-, hnone, -⟩ | ⟨sd, rd, hc, -, hnext, hkey⟩
  · cases hnone
  · cases hnone
  · cases hkey
    have hcur := inSync_chainCur F K g.e g.auth g.c (g.st .A) (g.st .B) (g.toP .A) (g.toP .B) hsync he_pos
    refine ⟨rfl, ⟨sd, rd, hnext, rfl⟩, fun Q => ?_⟩
    cases Q with
    | A =>
      rcases hcur.1 with hA | ⟨-, sd', rd', hboth⟩
      · omega
      · rw [hc] at hboth; cases hboth
    | B =>
      rcases hcur.2 with hB | ⟨-, sd', rd', hboth⟩
      · omega
      · rw [hc] at hboth; cases hboth

theorem topInv_init (F : ShaCompress) (K : MlKem) (k : BitVec 256) (stA stB : St F)
    (hA : States.init_a spqrPolyApi (spqrAuthApi F) (authOf k) = .ok stA)
    (hB : States.init_b spqrPolyApi (spqrAuthApi F) (authOf k) = .ok stB) :
    TopInv F K k ⟨fun P => (spqrV1SessionUniformCoins F K).withLog.init (spqrDir P) k, [], false⟩
      (initGhost F k stA stB) := by
  have hpt : ∀ P,
      PartyTop F K (authOf k) (partyDir P) (fun _ => []) ((initGhost F k stA stB).st P) 0
        (fun _ => 0) (fun _ => ∅)
        (((spqrV1SessionUniformCoins F K).withLog.init (spqrDir P) k).1) := fun P => by
    refine TopSync.top_init F K (spqrDir P) k (fun _ => []) _ ?_
    cases P
    · exact hA
    · exact hB
  have hrun : RunT F K (authOf k) 1#64 (Authenticator.new F (authOf k) 1#64) .init stA stB [] [] :=
    RunT.init stA stB hA hB
  have hcur := inSync_chainCur F K 1#64 (Authenticator.new F (authOf k) 1#64) .init stA stB [] []
    (runT_inSync F K (authOf k) hrun) (by decide)
  have hraw := TopSync.runT_rawV1State_le F K (authOf k) hrun
  refine
    { hrun := hrun
      hparty := fun P => ⟨0, hpt P, logAgree_init⟩
      hsize := fun P => ?_
      hsecret := fun _ _ hc => by cases hc
      hsentLen := rfl
      hlogSent := fun _ => le_rfl
      hsent := fun _ _ _ _ hj => by simp at hj
      hepochSent := fun n h2 h1 => by
        change n ≤ 1 at h1
        omega
      hdeliv := fun _ _ hp => by cases hp
      hwin := rfl }
  have hauth : (authOf k).length ≤ 2 ^ 40 := by
    simp [authOf, CryptoGames.HMAC.keyToBytes32]
  have hcurP : chainCur ((initGhost F k stA stB).st P) ≤ 2 ^ 40 := by
    cases P
    · rcases hcur.1 with h1 | ⟨-, _, _, hboth⟩
      · dsimp [initGhost]; rw [h1]; decide
      · cases hboth
    · rcases hcur.2 with h2 | ⟨-, _, _, hboth⟩
      · dsimp [initGhost]; rw [h2]; decide
      · cases hboth
  have hrecvP :
      ∑ e ∈ Finset.range (chainCur ((initGhost F k stA stB).st P) + 1),
        ((initGhost F k stA stB).recvSet P e).sup id ≤ 2 ^ 40 := by
    simp [initGhost]
  exact TopSync.partyTop_length_lt F K (authOf k) (partyDir P) (fun _ => [])
    ((initGhost F k stA stB).st P) 0 (fun _ => 0) (fun _ => ∅)
    (((spqrV1SessionUniformCoins F K).withLog.init (spqrDir P) k).1)
    (hpt P) hauth hcurP hrecvP
    (by cases P; exact hraw.1; exact hraw.2)

private theorem fts_send_runT (F : ShaCompress) (K : MlKem) (k : BitVec 256) (g : Ghost F)
    (hrun : RunT F K (authOf k) g.e g.auth g.c (g.st .A) (g.st .B) (g.toP .A) (g.toP .B))
    (P : CryptoGames.Party) (r : BitVec 512) (hkem : KemGood F K g P r) :
    ∃ (m : Msg) (key : Option EpochSecret) (st' : St F) (tape' : Bytes),
      (g.st P).send K (coinBytes r) = .ok ({ msg := m, key := key, state := st' }, tape') ∧
      CoinStep F K g.e (coinBytes r) g.c (nextCoins F g.c (g.st P) (coinBytes r)) key ∧
      States.from_pb spqrPolyApi (spqrAuthApi F) (g.st P).into_pb = .ok (g.st P) ∧
      RunT F K (authOf k) g.e g.auth (nextCoins F g.c (g.st P) (coinBytes r))
        (Function.update g.st P st' .A) (Function.update g.st P st' .B)
        (Function.update g.toP P.other (g.toP P.other ++ [m]) .A)
        (Function.update g.toP P.other (g.toP P.other ++ [m]) .B) := by
  have hsync := runT_inSync F K (authOf k) hrun
  have hcod := inSync_codec F K g.e g.auth g.c (g.st .A) (g.st .B) (g.toP .A) (g.toP .B) hsync
  have htape : 64 ≤ (coinBytes r).length := by rw [coinBytes_length]
  cases P with
  | A =>
    have hkemA : ekSide g.e = .b → ∀ (s : Seed) (r' : EncRand), DrawsEnc F g.c (g.st .A) s →
        r'.toList = (coinBytes r).take 32 → KemOk K s r' :=
      fun hs => hkem (by rw [hs]; decide)
    obtain ⟨m, key, stA', tape', hsend, hcs, -⟩ :=
      inSync_sendA_tight F K g.e g.auth g.c (g.st .A) (g.st .B) (g.toP .A) (g.toP .B)
        hsync (coinBytes r) htape hkemA
    refine ⟨m, key, stA', tape', hsend, hcs, hcod.1, ?_⟩
    simpa [CryptoGames.Party.other] using
      RunT.sendA hrun (coinBytes r) htape hkemA m key stA' tape' hsend
  | B =>
    have hkemB : ekSide g.e = .a → ∀ (s : Seed) (r' : EncRand), DrawsEnc F g.c (g.st .B) s →
        r'.toList = (coinBytes r).take 32 → KemOk K s r' :=
      fun hs => hkem (by rw [hs]; decide)
    obtain ⟨m, key, stB', tape', hsend, hcs, -⟩ :=
      inSync_sendB_tight F K g.e g.auth g.c (g.st .A) (g.st .B) (g.toP .A) (g.toP .B)
        hsync (coinBytes r) htape hkemB
    refine ⟨m, key, stB', tape', hsend, hcs, hcod.2, ?_⟩
    simpa [CryptoGames.Party.other] using
      RunT.sendB hrun (coinBytes r) htape hkemB m key stB' tape' hsend

private def fts_secret (secret : ℕ → Bytes) (key : Option EpochSecret) : ℕ → Bytes :=
  match key with
  | some es => Function.update secret es.epoch.toNat es.secret
  | none => secret

private theorem fts_secret_facts (F : ShaCompress) (K : MlKem) (k : BitVec 256) (g : Ghost F)
    (hrun : RunT F K (authOf k) g.e g.auth g.c (g.st .A) (g.st .B) (g.toP .A) (g.toP .B))
    (hsecret : ∀ sd rd, g.c = .both sd rd → g.secret g.e.toNat = secOf F K g.e sd rd)
    (P : CryptoGames.Party) (r : BitVec 512) (hkem : KemGood F K g P r)
    (m : Msg) (key : Option EpochSecret) (st' : St F) (tape' : Bytes)
    (hsend : (g.st P).send K (coinBytes r) = .ok ({ msg := m, key := key, state := st' }, tape'))
    (hcs : CoinStep F K g.e (coinBytes r) g.c (nextCoins F g.c (g.st P) (coinBytes r)) key) :
    (∀ Q e, 1 ≤ e → e ≤ chainCur (g.st Q) → fts_secret g.secret key e = g.secret e) ∧
      (∀ es, key = some es → es.secret = fts_secret g.secret key es.epoch.toNat) ∧
      (∀ sd rd, nextCoins F g.c (g.st P) (coinBytes r) = .both sd rd →
        fts_secret g.secret key g.e.toNat = secOf F K g.e sd rd) := by
  cases key with
  | none =>
    dsimp only [fts_secret]
    refine ⟨fun _ _ _ _ => rfl, fun _ h => (by cases h), fun sd rd hboth => ?_⟩
    rcases hcs with ⟨hc, -⟩ | ⟨-, -, s, -, hc⟩ | ⟨_, _, -, -, -, hnone⟩
    · exact hsecret sd rd (hc ▸ hboth)
    · rw [hc] at hboth; cases hboth
    · cases hnone
  | some es =>
    dsimp only [fts_secret]
    obtain ⟨hes_ep, ⟨sd, rd, hnext, hes_sec⟩, hcur⟩ :=
      send_key_fresh F K k g hrun P r hkem m es st' tape' hsend
    refine ⟨fun Q e _ he => ?_, fun es' hes' => ?_, fun sd' rd' hboth => ?_⟩
    · have hQ := hcur Q
      have hne : e ≠ es.epoch.toNat := by rw [hes_ep]; omega
      exact Function.update_of_ne hne es.secret g.secret
    · cases hes'
      exact (Function.update_self es.epoch.toNat es.secret g.secret).symm
    · rw [hnext] at hboth
      cases hboth
      rw [hes_ep, Function.update_self, hes_sec]

private theorem fts_partyTop_length_lt (F : ShaCompress) (K : MlKem) (k : BitVec 256) (q : ℕ)
    (hq : q + 2000 ≤ 2 ^ 32) (s : SpqrGameState (List (BitVec 8))) (g : Ghost F)
    (h : TopInv F K k s g) (hlen : s.sent.length ≤ q) (P : CryptoGames.Party)
    (secret' : ℕ → Bytes) (st' : St F) (sE' : ℕ) (sC' : ℕ → ℕ) (bytes' : Bytes)
    (hpt' : PartyTop F K (authOf k) (partyDir P) secret' st' sE' sC' (g.recvSet P) bytes')
    (c' : Coins) (toP' : CryptoGames.Party → List Msg)
    (hrun' : RunT F K (authOf k) g.e g.auth c'
      (Function.update g.st P st' .A) (Function.update g.st P st' .B)
      (toP' .A) (toP' .B)) :
    bytes'.length < 2 ^ 64 := by
  have hauth : (authOf k).length ≤ 2 ^ 40 := by
    simp [authOf, CryptoGames.HMAC.keyToBytes32]
  have hsync' := runT_inSync F K (authOf k) hrun'
  have he_pos := runT_epoch_pos h.hrun
  have hcur_both := inSync_chainCur F K g.e g.auth c' _ _ _ _ hsync' he_pos
  have hcur_le : chainCur st' ≤ g.e.toNat := by
    cases P with
    | A =>
      have hA := hcur_both.1
      simp only [Function.update_self] at hA
      rcases hA with hA | ⟨hA, -⟩ <;> omega
    | B =>
      have hB := hcur_both.2
      simp only [Function.update_self] at hB
      rcases hB with hB | ⟨hB, -⟩ <;> omega
  have hep_le := h.epoch_le
  have hcur : chainCur st' ≤ 2 ^ 40 := by omega
  obtain ⟨_, _, hlaP⟩ := h.hparty P
  obtain ⟨_, _, hlaQ⟩ := h.hparty P.other
  have hle_sum : ∑ e ∈ Finset.range (chainCur st' + 1), (g.recvSet P e).sup id ≤
      ∑ e ∈ Finset.range (chainCur st' + 1), g.sendCtr P.other e := by
    refine Finset.sum_le_sum fun e _ => ?_
    simpa using recvSet_sup_le hlaQ hlaP (h.hdeliv P) (e + 1) (by omega)
  have hsum_len := sendCtr_sum_le_length hlaQ (chainCur st' + 1)
  have hlogQ := h.hlogSent P.other
  have hrecv : ∑ e ∈ Finset.range (chainCur st' + 1), (g.recvSet P e).sup id ≤ 2 ^ 40 := by omega
  have hraw := TopSync.runT_rawV1State_le F K (authOf k) hrun'
  have hbraid : CryptoVerification.SpqrV1.Top.StateSize.rawV1State st'.into_pb ≤ 2 ^ 40 := by
    cases P with
    | A => simpa using hraw.1
    | B => simpa using hraw.2
  exact TopSync.partyTop_length_lt F K (authOf k) (partyDir P) secret' st' sE' sC' (g.recvSet P)
    bytes' hpt' hauth hcur hrecv hbraid

private theorem tl_sendPanics_eq_false_of_isSome (F : ShaCompress) (K : MlKem)
    (st : List (BitVec 8)) (r : BitVec 512) (h : ((spqrV1SessionUniformCoins F K).send st r).isSome) :
    (spqrV1SessionUniformCoins F K).sendPanics st r = false := by
  simp only [spqrV1SessionUniformCoins, spqrV1_eq, toSpqrModel, sendPanicsPureB] at h ⊢
  split at h
  · rename_i heq
    rw [heq]
  · simp at h

theorem topInv_send (F : ShaCompress) (K : MlKem) (k : BitVec 256) (q : ℕ)
    (hq : q + 2000 ≤ 2 ^ 32) (s : SpqrGameState (List (BitVec 8))) (g : Ghost F)
    (h : TopInv F K k s g) (hlen : s.sent.length ≤ q) (P : CryptoGames.Party) (r : BitVec 512)
    (hkem : KemGood F K g P r) :
    (spqrSendStep (spqrV1SessionUniformCoins F K) s P r).2.sent.length = s.sent.length + 1 ∧
      TopInv F K k (spqrSendStep (spqrV1SessionUniformCoins F K) s P r).2 (ghostSend F K g P r) := by
  have hsentLen := h.hsentLen
  obtain ⟨sE, hpt, hla⟩ := h.hparty P
  have hep_pos : 1 ≤ (g.st P).epoch.toNat := TopSync.partyTop_epoch_pos hpt
  obtain ⟨m, key, st', tape', hsendB, hcs, hcodec, hrun'⟩ :=
    fts_send_runT F K k g h.hrun P r hkem
  obtain ⟨hm_ep, hst'_ep, hpay, -⟩ :=
    TopSync.send_facts F K (g.st P) st' (coinBytes r) tape' m key hsendB
  have hE1 : 1 ≤ m.epoch.toNat := hm_ep ▸ hep_pos
  have he_ne : m.epoch ≠ 0#64 := by
    intro h0
    have : m.epoch.toNat = 0 := congrArg BitVec.toNat h0
    omega
  obtain ⟨hsec_eq, hsec_key, hsecret'⟩ :=
    fts_secret_facts F K k g h.hrun h.hsecret P r hkem m key st' tape' hsendB hcs
  let secret' : ℕ → Bytes := fts_secret g.secret key
  have hpt_sec' : PartyTop F K (authOf k) (partyDir P) secret' (g.st P) sE
      (g.sendCtr P) (g.recvSet P) (s.st P).1 :=
    TopSync.partyTop_congr secret' hpt (hsec_eq P)
  have hctr_le := sendCtr_le_length hla (g.st P).epoch.toNat hep_pos
  have hlogP := h.hlogSent P
  have hctr : g.sendCtr P ((g.st P).epoch.toNat - 1) + 1 < 2 ^ 32 := by omega
  obtain ⟨bytes', htop_send, hpt'⟩ :=
    TopSync.top_send F K (authOf k) (partyDir P) secret' (g.st P) st' sE
      (g.sendCtr P) (g.recvSet P) (s.st P).1 hpt_sec' (h.hsize P) hcodec
      (coinBytes r) tape' m key hsendB hsec_key hctr
  rw [← hm_ep] at htop_send hpt' hctr
  let eP := m.epoch.toNat - 1
  let n := g.sendCtr P eP
  let idx := BitVec.ofNat 32 (n + 1)
  let msg₀ := Message.serialize m idx
  let salt₀ : CryptoGames.HKDF.Salt :=
    some ⟨keyAt F (seedAt F (authOf k) secret' (partyDir P) eP) n, length_keyAt _ _ _⟩
  let stP' : List (BitVec 8) × SpqrLog :=
    (bytes', { (s.st P).2 with sent := msg₀ :: (s.st P).2.sent })
  have hnp : (spqrV1 F K).sendPanics (s.st P).1 (coinBytes r) = false :=
    tl_sendPanics_eq_false_of_isSome F K (s.st P).1 r (by
      change ((spqrV1 F K).send (s.st P).1 (coinBytes r)).isSome = true
      rw [htop_send]; rfl)
  have hstep_eq : (spqrSendStep (spqrV1SessionUniformCoins F K) s P r).2 =
      { s with st := Function.update s.st P stP', sent := s.sent ++ [(P, msg₀, salt₀)] } := by
    unfold spqrSendStep
    rw [h.hwin]
    simp only [Bool.false_eq_true, ↓reduceIte, CryptoGames.LibsignalSession.Spqr.withLog,
      spqrV1SessionUniformCoins, hnp, htop_send, Option.map]
    rfl
  rw [hstep_eq]
  refine ⟨by simp, ?_⟩
  have hghost_eq : ghostSend F K g P r =
      { g with
        c := nextCoins F g.c (g.st P) (coinBytes r)
        st := Function.update g.st P st'
        toP := Function.update g.toP P.other (g.toP P.other ++ [m])
        sentB := g.sentB ++ [(m, idx)]
        secret := secret'
        sendCtr := Function.update g.sendCtr P (Function.update (g.sendCtr P) eP (n + 1)) } := by
    unfold ghostSend
    rw [hsendB]
    rfl
  rw [hghost_eq]
  have hidx_nat : idx.toNat = n + 1 := by
    simp only [idx, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hctr
  have hpos : spqrPos msg₀ = some (m.epoch.toNat, n + 1) := by
    rw [← hidx_nat]
    exact spqrPos_serialize m idx he_ne
  have hmono : (s.st P).2.maxSendEpoch ≤ m.epoch.toNat := by
    obtain ⟨_, _, _, hw⟩ := hpt
    have hsE := hla.hsE
    have hle := hw.hsendLe
    rw [hm_ep]
    omega
  refine
    { hrun := hrun'
      hparty := fun Q => ?_
      hsize := fun Q => ?_
      hsecret := hsecret'
      hsentLen := by simp [hsentLen]
      hlogSent := fun Q => ?_
      hsent := fun j Q msg salt hj => ?_
      hepochSent := fun n' h2 hn' => ?_
      hdeliv := fun Q p hp => ?_
      hwin := h.hwin }
  · by_cases hQP : Q = P
    · subst Q
      simp only [PartyOk, Function.update_self, stP']
      exact ⟨eP, hpt', logAgree_send hla msg₀ m.epoch.toNat hE1 hmono hpos⟩
    · obtain ⟨sEQ, hptQ, hlaQ⟩ := h.hparty Q
      simp only [PartyOk, Function.update_of_ne hQP]
      exact ⟨sEQ, TopSync.partyTop_congr secret' hptQ (hsec_eq Q), hlaQ⟩
  · by_cases hQP : Q = P
    · subst Q
      simp only [Function.update_self, stP']
      exact fts_partyTop_length_lt F K k q hq s g h hlen P secret' st' eP
        (Function.update (g.sendCtr P) eP (n + 1)) bytes' hpt' _ _ hrun'
    · simp only [Function.update_of_ne hQP]
      exact h.hsize Q
  · by_cases hQP : Q = P
    · subst Q
      simp only [Function.update_self, stP', List.length_cons, List.length_append]
      omega
    · have hlogQ := h.hlogSent Q
      simp only [Function.update_of_ne hQP, List.length_append]
      omega
  · dsimp only at hj ⊢
    by_cases hj_lt : j < s.sent.length
    · rw [List.getElem?_append_left hj_lt] at hj
      obtain ⟨m', i', hsentB_j, hmsg, hm'_toP, hE1', hpay', hi1', hi_le', hsalt⟩ :=
        h.hsent j Q msg salt hj
      refine ⟨m', i', ?_, hmsg, ?_, hE1', hpay', hi1', ?_, ?_⟩
      · rw [List.getElem?_append_left (by omega)]
        exact hsentB_j
      · by_cases hQPo : Q.other = P.other
        · rw [hQPo, Function.update_self]
          exact List.mem_append_left _ (hQPo ▸ hm'_toP)
        · rw [Function.update_of_ne hQPo]
          exact hm'_toP
      · by_cases hQP : Q = P
        · subst Q
          rw [Function.update_self]
          by_cases he : m'.epoch.toNat - 1 = eP
          · rw [he, Function.update_self]
            have : i'.toNat ≤ n := by
              dsimp only [n]
              rw [← he]
              exact hi_le'
            omega
          · rw [Function.update_of_ne he]
            exact hi_le'
        · rw [Function.update_of_ne hQP]
          exact hi_le'
      · obtain ⟨_, hptQ, _⟩ := h.hparty Q
        have hcurQ : m'.epoch.toNat - 1 ≤ chainCur (g.st Q) := by
          by_contra hgt
          have h0 := partyTop_sendCtr_fresh hptQ (m'.epoch.toNat - 1) (by omega)
          omega
        have hgen : genAt F (authOf k) secret' (m'.epoch.toNat - 1) =
            genAt F (authOf k) g.secret (m'.epoch.toNat - 1) :=
          genAt_congr F (authOf k) g.secret secret' (m'.epoch.toNat - 1)
            (fun i h1 h2 => hsec_eq Q i h1 (by omega))
        have hseed : seedAt F (authOf k) secret' (partyDir Q) (m'.epoch.toNat - 1) =
            seedAt F (authOf k) g.secret (partyDir Q) (m'.epoch.toNat - 1) := by
          unfold seedAt
          rw [hgen]
        rw [hseed]
        exact hsalt
    · rw [List.getElem?_append_right (by omega)] at hj
      cases hk : j - s.sent.length with
      | zero =>
        rw [hk] at hj
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hj
        obtain ⟨rfl, rfl, rfl⟩ := hj
        have hj_eq : j = g.sentB.length := by omega
        subst hj_eq
        refine ⟨m, idx, ?_, rfl, ?_, hE1, hpay, ?_, ?_, ?_⟩
        · simp
        · rw [Function.update_self]
          exact List.mem_append_right _ (List.mem_singleton_self m)
        · omega
        · simp only [eP, Function.update_self, hidx_nat, le_rfl]
        · simp only [hidx_nat, Nat.add_sub_cancel, salt₀, eP, n]
      | succ k' =>
        rw [hk] at hj
        simp at hj
  · dsimp only
    obtain ⟨p, hp, hpn⟩ := h.hepochSent n' h2 hn'
    exact ⟨p, List.mem_append_left _ hp, hpn⟩
  · dsimp only at hp ⊢
    have hrec : (Function.update s.st P stP' Q).2.recvd = (s.st Q).2.recvd := by
      by_cases hQP : Q = P
      · subst Q; simp [stP']
      · simp [Function.update_of_ne hQP]
    rw [hrec] at hp
    have hsent_old := h.hdeliv Q p hp
    by_cases hQPo : Q.other = P
    · rw [hQPo, Function.update_self]
      simp only [stP', posList, List.filterMap_cons, hpos, List.mem_cons]
      exact Or.inr (hQPo ▸ hsent_old)
    · rw [Function.update_of_ne hQPo]
      exact hsent_old

private theorem fiw_ghostDeliver_facts (F : ShaCompress) (K : MlKem) (k : BitVec 256) (q : ℕ)
    (hq : q + 2000 ≤ 2 ^ 32) (s : SpqrGameState (List (BitVec 8))) (g : Ghost F)
    (h : TopInv F K k s g) (hlen : s.sent.length ≤ q) (P : CryptoGames.Party) (j : ℕ)
    (m : Msg) (i : BitVec 32) (hjB : g.sentB[j]? = some (m, i)) (hm_toP : m ∈ g.toP P) :
    let g' := ghostDeliver F K g P j
    ∃ key stP',
      (g.st P).recv K m = .ok { key := key, state := stP' } ∧
      (∀ es, key = some es → es.secret = g.secret es.epoch.toNat) ∧
      g'.st = Function.update g.st P stP' ∧
      g'.secret = g.secret ∧
      g'.toP = g.toP ∧
      g'.sentB = g.sentB ∧
      g'.sendCtr = g.sendCtr ∧
      g'.recvSet = Function.update g.recvSet P
        (Function.update (g.recvSet P) (m.epoch.toNat - 1)
          (insert i.toNat (g.recvSet P (m.epoch.toNat - 1)))) ∧
      RunT F K (authOf k) g'.e g'.auth g'.c (g'.st .A) (g'.st .B) (g'.toP .A) (g'.toP .B) ∧
      (∀ sd rd, g'.c = .both sd rd → g'.secret g'.e.toNat = secOf F K g'.e sd rd) ∧
      (∀ n, 2 ≤ n → n ≤ g'.e.toNat → ∃ p ∈ g'.sentB, p.1.epoch.toNat = n) := by
  have hsync := runT_inSync F K (authOf k) h.hrun
  have hnext : g.e.toNat + 2 < 2 ^ 64 := h.epoch_lt q hq hlen
  by_cases hne : m = noneMsg (g.e + 1#64)
  · have hadv : ∃ sd rd, g.c = .both sd rd ∧ ∃ stP',
        (g.st P).recv K m = .ok { key := none, state := stP' } ∧
        RunT F K (authOf k) (g.e + 1#64) (authNext F K g.e g.auth sd rd) .init
          (Function.update g.st P stP' .A) (Function.update g.st P stP' .B)
          (g.toP .A) (g.toP .B) := by
      cases P with
      | A =>
        obtain ⟨sd, rd, hc, stA', hrecv, _⟩ :=
          inSync_advanceA F K g.e g.auth g.c (g.st .A) (g.st .B) (g.toP .A) (g.toP .B)
            hsync (hne ▸ hm_toP) hnext
        have hrun0 := h.hrun
        rw [hc] at hrun0
        exact ⟨sd, rd, hc, stA', hne.symm ▸ hrecv,
          RunT.advanceA hrun0 (hne ▸ hm_toP) hnext stA' hrecv⟩
      | B =>
        obtain ⟨sd, rd, hc, stB', hrecv, _⟩ :=
          inSync_advanceB F K g.e g.auth g.c (g.st .A) (g.st .B) (g.toP .A) (g.toP .B)
            hsync (hne ▸ hm_toP) hnext
        have hrun0 := h.hrun
        rw [hc] at hrun0
        exact ⟨sd, rd, hc, stB', hne.symm ▸ hrecv,
          RunT.advanceB hrun0 (hne ▸ hm_toP) hnext stB' hrecv⟩
    obtain ⟨sd, rd, hc, stP', hrecvB, hrun'⟩ := hadv
    have hg' : ghostDeliver F K g P j =
        { g with
          e := g.e + 1#64
          auth := authNext F K g.e g.auth sd rd
          c := .init
          st := Function.update g.st P stP'
          recvSet := Function.update g.recvSet P
            (Function.update (g.recvSet P) (m.epoch.toNat - 1)
              (insert i.toNat (g.recvSet P (m.epoch.toNat - 1)))) } := by
      unfold ghostDeliver
      rw [hjB]; dsimp only
      rw [hrecvB]; dsimp only
      rw [ite_eq_left hne, hc]
    refine ⟨none, stP', hrecvB, nofun, ?_⟩
    rw [hg']
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, hrun', nofun, fun n hn2 hn_le => ?_⟩
    dsimp only at hn_le ⊢
    have he1 : (g.e + 1#64).toNat = g.e.toNat + 1 := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    by_cases hn : n ≤ g.e.toNat
    · exact h.hepochSent n hn2 hn
    · refine ⟨(m, i), List.mem_of_getElem? hjB, ?_⟩
      rw [hne]
      change (g.e + 1#64).toNat = n
      omega
  · have hstay : ∃ key stP',
        (g.st P).recv K m = .ok { key := key, state := stP' } ∧
        RecvKey F K g.e g.c key ∧
        RunT F K (authOf k) g.e g.auth g.c
          (Function.update g.st P stP' .A) (Function.update g.st P stP' .B)
          (g.toP .A) (g.toP .B) := by
      cases P with
      | A =>
        obtain ⟨key, stA', hrecv, hkey, _⟩ :=
          inSync_recvA_stay F K g.e g.auth g.c (g.st .A) (g.st .B) (g.toP .A) (g.toP .B)
            hsync m hm_toP hne
        exact ⟨key, stA', hrecv, hkey, RunT.recvA h.hrun m hm_toP hne key stA' hrecv⟩
      | B =>
        obtain ⟨key, stB', hrecv, hkey, _⟩ :=
          inSync_recvB_stay F K g.e g.auth g.c (g.st .A) (g.st .B) (g.toP .A) (g.toP .B)
            hsync m hm_toP hne
        exact ⟨key, stB', hrecv, hkey, RunT.recvB h.hrun m hm_toP hne key stB' hrecv⟩
    obtain ⟨key, stP', hrecvB, hkey, hrun'⟩ := hstay
    have hsec : ∀ es, key = some es → es.secret = g.secret es.epoch.toNat := by
      intro es hes
      rcases hkey with rfl | ⟨sd, rd, hc, hkey'⟩
      · cases hes
      · rw [hes, Option.some.injEq] at hkey'
        subst hkey'
        exact (h.hsecret sd rd hc).symm
    have hg' : ghostDeliver F K g P j =
        { g with
          st := Function.update g.st P stP'
          recvSet := Function.update g.recvSet P
            (Function.update (g.recvSet P) (m.epoch.toNat - 1)
              (insert i.toNat (g.recvSet P (m.epoch.toNat - 1)))) } := by
      unfold ghostDeliver
      rw [hjB]; dsimp only
      rw [hrecvB]; dsimp only
      rw [ite_eq_right hne]
      cases key with
      | none => rfl
      | some es =>
        dsimp only
        rw [hsec es rfl, Function.update_eq_self]
    refine ⟨key, stP', hrecvB, hsec, ?_⟩
    rw [hg']
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, hrun', h.hsecret, h.hepochSent⟩

theorem deliver_inWindow (F : ShaCompress) (K : MlKem) (k : BitVec 256) (q : ℕ)
    (hq : q + 2000 ≤ 2 ^ 32) (s : SpqrGameState (List (BitVec 8))) (g : Ghost F)
    (h : TopInv F K k s g) (hlen : s.sent.length ≤ q) (P : CryptoGames.Party) (j : ℕ)
    (msg : List (BitVec 8)) (salt : CryptoGames.HKDF.Salt)
    (hj : s.sent[j]? = some (P.other, msg, salt)) (hinW : spqrWindowOk (s.st P).2 msg = true) :
    ∃ st', (spqrV1SessionUniformCoins F K).withLog.recv (s.st P) msg = .ok (st', salt) ∧ st' ≠ s.st P ∧
      TopInv F K k { s with st := Function.update s.st P st' } (ghostDeliver F K g P j) := by
  obtain ⟨m, i, hjB, hmsg, hm_toPO, hE1, hpay, hi1, hi_le, hsalt⟩ :=
    h.hsent j P.other msg salt hj
  have hm_toP : m ∈ g.toP P := by cases P <;> exact hm_toPO
  have he_ne : m.epoch ≠ 0#64 := by
    intro h0
    have : m.epoch.toNat = 0 := congrArg BitVec.toNat h0
    omega
  have hpos : spqrPos msg = some (m.epoch.toNat, i.toNat) :=
    hmsg ▸ spqrPos_serialize m i he_ne
  obtain ⟨sE, hpt, hla⟩ := h.hparty P
  obtain ⟨sEO, hptO, hlaO⟩ := h.hparty P.other
  obtain ⟨h1, _, hnew, hjump, htrim⟩ :=
    (spqrWindowOk_iff hla msg m.epoch.toNat i.toNat hpos hE1).mp hinW
  have hsendE : sE ≤ m.epoch.toNat := by omega
  have hctrO : g.sendCtr P.other (m.epoch.toNat - 1) ≤ q :=
    (sendCtr_le_length hlaO m.epoch.toNat hE1).trans ((h.hlogSent P.other).trans hlen)
  have hb : i.toNat + 2000 ≤ 2 ^ 32 := by omega
  have hsup_le : (g.recvSet P (m.epoch.toNat - 1)).sup id ≤ g.sendCtr P.other (m.epoch.toNat - 1) :=
    recvSet_sup_le hlaO hla (h.hdeliv P) m.epoch.toNat hE1
  have hR : (g.recvSet P (m.epoch.toNat - 1)).sup id + 2000 ≤ 2 ^ 32 := by omega
  have hsync := runT_inSync F K (authOf k) h.hrun
  have hcodec : States.from_pb spqrPolyApi (spqrAuthApi F) (g.st P).into_pb = .ok (g.st P) := by
    have hc := inSync_codec F K g.e g.auth g.c (g.st .A) (g.st .B) (g.toP .A) (g.toP .B) hsync
    cases P
    · exact hc.1
    · exact hc.2
  have hEcur : m.epoch.toNat ≤ chainCur (g.st P) + 1 := by
    cases P
    · exact TopSync.inSync_toA_chainCur F K g.e g.auth g.c (g.st .A) (g.st .B)
        (g.toP .A) (g.toP .B) hsync m hm_toP
    · exact TopSync.inSync_toB_chainCur F K g.e g.auth g.c (g.st .A) (g.st .B)
        (g.toP .A) (g.toP .B) hsync m hm_toP
  obtain ⟨key, stP', hrecvB, hsec, hg_st, hg_sec, hg_toP, hg_sentB, hg_sC, hg_rS,
      hrun', hsecret', hepochSent'⟩ :=
    fiw_ghostDeliver_facts F K k q hq s g h hlen P j m i hjB hm_toP
  obtain ⟨bytes', htop_recv, hpt'⟩ :=
    TopSync.top_recv F K (authOf k) (partyDir P) g.secret (g.st P) stP' sE
      (g.sendCtr P) (g.recvSet P) (s.st P).1 hpt (h.hsize P) hcodec m key hrecvB hsec
      hpay hE1 hEcur hsendE i.toNat hi1 hnew hjump htrim hb hR
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, ← hmsg, ← partyDir_other P, ← hsalt]
    at htop_recv
  let log' : SpqrLog := { (s.st P).2 with recvd := msg :: (s.st P).2.recvd }
  let st' : List (BitVec 8) × SpqrLog := (bytes', log')
  have hwithLog : (spqrV1SessionUniformCoins F K).withLog.recv (s.st P) msg = .ok (st', salt) := by
    dsimp [CryptoGames.LibsignalSession.Spqr.withLog, spqrV1SessionUniformCoins]
    rw [htop_recv]
    rfl
  have hne_st : st' ≠ s.st P := by
    intro heq
    have := congrArg (fun x : List (BitVec 8) × SpqrLog => x.2.recvd.length) heq
    simp [st', log'] at this
  have hla' : LogAgree log' sE (g.sendCtr P)
      (Function.update (g.recvSet P) (m.epoch.toNat - 1)
        (insert i.toNat (g.recvSet P (m.epoch.toNat - 1)))) :=
    logAgree_recv hla msg m.epoch.toNat i.toNat hE1 hpos
  have hdelivP' : ∀ p ∈ posList log'.recvd, p ∈ posList (s.st P.other).2.sent := by
    intro p hp
    simp only [log', posList, List.filterMap_cons_some hpos, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact (hlaO.hsent m.epoch.toNat i.toNat).mpr ⟨hE1, hi1, hi_le⟩
    · exact h.hdeliv P p hp
  have hsizeP' : bytes'.length < 2 ^ 64 := by
    have hauth : (authOf k).length ≤ 2 ^ 40 := by
      simp [authOf, CryptoGames.HMAC.keyToBytes32]
    have hsync' := runT_inSync F K (authOf k) hrun'
    have hcur_all := inSync_chainCur F K (ghostDeliver F K g P j).e (ghostDeliver F K g P j).auth
      (ghostDeliver F K g P j).c ((ghostDeliver F K g P j).st .A) ((ghostDeliver F K g P j).st .B)
      ((ghostDeliver F K g P j).toP .A) ((ghostDeliver F K g P j).toP .B)
      hsync' (runT_epoch_pos hrun')
    have hcur_e : chainCur ((ghostDeliver F K g P j).st P) ≤ (ghostDeliver F K g P j).e.toNat := by
      cases P
      · rcases hcur_all.1 with h1 | ⟨h1, -⟩ <;> omega
      · rcases hcur_all.2 with h1 | ⟨h1, -⟩ <;> omega
    rw [hg_st, Function.update_self] at hcur_e
    have hep_le : (ghostDeliver F K g P j).e.toNat ≤ s.sent.length + 1 := by
      rw [h.hsentLen, ← hg_sentB]
      exact epoch_le_of_sent (ghostDeliver F K g P j).sentB (ghostDeliver F K g P j).e.toNat
        hepochSent'
    have hcur : chainCur stP' ≤ 2 ^ 40 := by omega
    have hsum1 : ∑ e ∈ Finset.range (chainCur stP' + 1),
        (Function.update (g.recvSet P) (m.epoch.toNat - 1)
          (insert i.toNat (g.recvSet P (m.epoch.toNat - 1))) e).sup id ≤
        ∑ e ∈ Finset.range (chainCur stP' + 1), g.sendCtr P.other e :=
      Finset.sum_le_sum fun e _ => recvSet_sup_le hlaO hla' hdelivP' (e + 1) (by omega)
    have hsum2 := sendCtr_sum_le_length hlaO (chainCur stP' + 1)
    have hlogO := h.hlogSent P.other
    have hrecv : ∑ e ∈ Finset.range (chainCur stP' + 1),
        (Function.update (g.recvSet P) (m.epoch.toNat - 1)
          (insert i.toNat (g.recvSet P (m.epoch.toNat - 1))) e).sup id ≤ 2 ^ 40 := by omega
    have hbr := TopSync.runT_rawV1State_le F K (authOf k) hrun'
    have hbrP : CryptoVerification.SpqrV1.Top.StateSize.rawV1State
        ((ghostDeliver F K g P j).st P).into_pb ≤ 2 ^ 40 := by
      cases P
      · exact hbr.1
      · exact hbr.2
    rw [hg_st, Function.update_self] at hbrP
    exact TopSync.partyTop_length_lt F K (authOf k) (partyDir P) g.secret stP' sE
      (g.sendCtr P)
      (Function.update (g.recvSet P) (m.epoch.toNat - 1)
        (insert i.toNat (g.recvSet P (m.epoch.toNat - 1))))
      bytes' hpt' hauth hcur hrecv hbrP
  have hsent_eq : ∀ Q, (Function.update s.st P st' Q).2.sent = (s.st Q).2.sent := by
    intro Q
    by_cases hQ : Q = P
    · subst hQ; simp [st', log']
    · simp [hQ]
  refine ⟨st', hwithLog, hne_st, ?_⟩
  refine
    { hrun := hrun'
      hparty := fun Q => ?_
      hsize := fun Q => ?_
      hsecret := hsecret'
      hsentLen := by rw [hg_sentB]; exact h.hsentLen
      hlogSent := fun Q => by dsimp only; rw [hsent_eq Q]; exact h.hlogSent Q
      hsent := fun j' Q msg' salt' hj' => by
        rw [hg_sentB, hg_toP, hg_sC, hg_sec]
        exact h.hsent j' Q msg' salt' hj'
      hepochSent := hepochSent'
      hdeliv := fun Q p hp => ?_
      hwin := h.hwin }
  · unfold PartyOk
    rw [hg_sec, hg_st, hg_sC, hg_rS]
    by_cases hQ : Q = P
    · subst hQ
      simp only [Function.update_self]
      exact ⟨sE, hpt', hla'⟩
    · simp only [Function.update_of_ne hQ]
      exact h.hparty Q
  · dsimp only
    by_cases hQ : Q = P
    · subst hQ
      simp only [Function.update_self]
      exact hsizeP'
    · simp only [Function.update_of_ne hQ]
      exact h.hsize Q
  · dsimp only at hp ⊢
    rw [hsent_eq Q.other]
    by_cases hQ : Q = P
    · subst hQ
      rw [Function.update_self] at hp
      exact hdelivP' p hp
    · rw [Function.update_of_ne hQ] at hp
      exact h.hdeliv Q p hp

theorem deliver_outWindow (F : ShaCompress) (K : MlKem) (k : BitVec 256)
    (s : SpqrGameState (List (BitVec 8))) (g : Ghost F) (h : TopInv F K k s g)
    (P Q : CryptoGames.Party) (j : ℕ) (msg : List (BitVec 8)) (salt : CryptoGames.HKDF.Salt)
    (hj : s.sent[j]? = some (Q, msg, salt)) (hout : spqrWindowOk (s.st P).2 msg = false) :
    ∀ r, (spqrV1SessionUniformCoins F K).withLog.recv (s.st P) msg ≠ .ok r := by
  obtain ⟨m, i, _, hmsg, _, hE1, hpay, hi1, _, _⟩ := h.hsent j Q msg salt hj
  have he_ne : m.epoch ≠ 0#64 := by
    intro h0
    have : m.epoch.toNat = 0 := congrArg BitVec.toNat h0
    omega
  obtain ⟨rem, hpre, _⟩ := TopSync.msg_roundtrip F K m i he_ne hpay
  have hpos : spqrPos msg = some (m.epoch.toNat, i.toNat) := by
    rw [hmsg]
    exact spqrPos_serialize m i he_ne
  obtain ⟨sE, hpt, hla⟩ := h.hparty P
  have hiff := spqrWindowOk_iff hla msg m.epoch.toNat i.toNat hpos hE1
  simp only [hout, Bool.false_eq_true, false_iff] at hiff
  have hout' : m.epoch.toNat < sE ∨
      i.toNat ∈ g.recvSet P (m.epoch.toNat - 1) ∨
      ((g.recvSet P (m.epoch.toNat - 1)).sup id < i.toNat ∧
        25000 < i.toNat - (g.recvSet P (m.epoch.toNat - 1)).sup id) ∨
      (i.toNat < (g.recvSet P (m.epoch.toNat - 1)).sup id ∧
        i.toNat + 2000 < (g.recvSet P (m.epoch.toNat - 1)).sup id) := by
    by_cases h1 : sE - 1 ≤ m.epoch.toNat - 1
    · by_cases h3 : i.toNat ∈ g.recvSet P (m.epoch.toNat - 1)
      · exact .inr (.inl h3)
      · by_cases h4 : (g.recvSet P (m.epoch.toNat - 1)).sup id < i.toNat →
            i.toNat - (g.recvSet P (m.epoch.toNat - 1)).sup id ≤ 25000
        · have h5 : ¬ (i.toNat < (g.recvSet P (m.epoch.toNat - 1)).sup id →
              (g.recvSet P (m.epoch.toNat - 1)).sup id ≤ i.toNat + 2000) :=
            fun h5 => hiff ⟨h1, hi1, h3, h4, h5⟩
          exact .inr (.inr (.inr (by omega)))
        · exact .inr (.inr (.inl (by omega)))
    · exact .inl (by omega)
  have herr := TopSync.top_recv_err F K (authOf k) (partyDir P) g.secret (g.st P) sE
    (g.sendCtr P) (g.recvSet P) (s.st P).1 hpt (h.hsize P) msg
    { version := 1#8, epoch := m.epoch, index := i, remaining := rem }
    (hmsg ▸ hpre) rfl hE1 hi1 hout'
  intro r hok
  dsimp [CryptoGames.LibsignalSession.Spqr.withLog, spqrV1SessionUniformCoins] at hok
  cases hrecv : (spqrV1 F K).recv (s.st P).1 msg with
  | error e =>
    rw [hrecv] at hok
    cases hok
  | ok x =>
    exact herr x hrecv

/-- Hypothesis that out-of-window honest messages fail cleanly with `.err` rather than panicking. -/
def OutWindowNoPanicStmt (F : ShaCompress) (K : MlKem) : Prop :=
  ∀ (k : BitVec 256) (q : ℕ), q + 2000 ≤ 2 ^ 32 →
  ∀ (s : SpqrGameState (List (BitVec 8))) (g : Ghost F), TopInv F K k s g → s.sent.length ≤ q →
  ∀ (P : CryptoGames.Party) (j : ℕ) (msg : List (BitVec 8)) (salt : CryptoGames.HKDF.Salt),
    s.sent[j]? = some (P.other, msg, salt) → spqrWindowOk (s.st P).2 msg = false →
    ∃ e, LibsignalSpqrV1.recv (spqrDeps F K) (spqrHkdfWith F) (s.st P).1 msg = .error (.err e)

private theorem tl_recvPanics_eq_false_of_err (F : ShaCompress) (K : MlKem)
    (st : List (BitVec 8) × SpqrLog) (msg : List (BitVec 8))
    (h : ∃ e, LibsignalSpqrV1.recv (spqrDeps F K) (spqrHkdfWith F) st.1 msg = .error (.err e)) :
    (spqrV1SessionUniformCoins F K).withLog.recvPanics st msg = false := by
  obtain ⟨e, he⟩ := h
  simp only [CryptoGames.LibsignalSession.Spqr.withLog, spqrV1SessionUniformCoins, spqrV1_eq, toSpqrModel,
    recvPanicsB, he]

private theorem tl_recvPanics_eq_false_of_ok (F : ShaCompress) (K : MlKem)
    (st : List (BitVec 8) × SpqrLog) (msg : List (BitVec 8)) (st' : List (BitVec 8) × SpqrLog)
    (salt : CryptoGames.HKDF.Salt)
    (h : (spqrV1SessionUniformCoins F K).withLog.recv st msg = .ok (st', salt)) :
    (spqrV1SessionUniformCoins F K).withLog.recvPanics st msg = false := by
  simp only [CryptoGames.LibsignalSession.Spqr.withLog, spqrV1SessionUniformCoins, spqrV1_eq, toSpqrModel,
    recvPanicsB] at h ⊢
  cases hr : LibsignalSpqrV1.recv (spqrDeps F K) (spqrHkdfWith F) st.1 msg with
  | ok x => rfl
  | error e =>
    cases e with
    | err e => rfl
    | panic p => rw [hr] at h; cases h

theorem topInv_deliver (F : ShaCompress) (K : MlKem) (hout : OutWindowNoPanicStmt F K)
    (k : BitVec 256) (q : ℕ)
    (hq : q + 2000 ≤ 2 ^ 32) (s : SpqrGameState (List (BitVec 8))) (g : Ghost F)
    (h : TopInv F K k s g) (hlen : s.sent.length ≤ q) (P : CryptoGames.Party) (j : ℕ)
    (commit : Bool) :
    TopInv F K k (spqrDeliverStep (spqrV1SessionUniformCoins F K) s P j commit).2
      (if (spqrDeliverStep (spqrV1SessionUniformCoins F K) s P j commit).2.st P ≠ s.st P
        then ghostDeliver F K g P j else g) := by
  have hwin := h.hwin
  have hs_win : { s with win := false } = s := by
    cases s; simp_all
  unfold spqrDeliverStep
  rw [hwin]
  simp only [Bool.false_eq_true, ↓reduceIte]
  cases hj : s.sent[j]? with
  | none =>
    simp only [ne_eq, not_true_eq_false, ↓reduceIte]
    exact h
  | some val =>
    rcases val with ⟨Q, msg, salt⟩
    by_cases hQ : Q = P.other
    · subst hQ
      simp only [ne_eq, not_true_eq_false, ↓reduceIte]
      cases hinW : spqrWindowOk (s.st P).2 msg with
      | false =>
        have hnpR : (spqrV1SessionUniformCoins F K).withLog.recvPanics (s.st P) msg = false :=
          tl_recvPanics_eq_false_of_err F K (s.st P) msg
            (hout k q hq s g h hlen P j msg salt hj hinW)
        simp only [hnpR, Bool.false_eq_true, ↓reduceIte]
        have hnoOk := deliver_outWindow F K k s g h P P.other j msg salt hj hinW
        cases hrecv : (spqrV1SessionUniformCoins F K).withLog.recv (s.st P) msg with
        | ok r => exact False.elim (hnoOk r hrecv)
        | error e =>
          simp only [hs_win, not_true_eq_false, ↓reduceIte]
          exact h
      | true =>
        obtain ⟨st', hrecv, hne, hinv'⟩ :=
          deliver_inWindow F K k q hq s g h hlen P j msg salt hj hinW
        have hnpR : (spqrV1SessionUniformCoins F K).withLog.recvPanics (s.st P) msg = false :=
          tl_recvPanics_eq_false_of_ok F K (s.st P) msg st' salt hrecv
        simp only [hnpR, Bool.false_eq_true, ↓reduceIte]
        rw [hrecv]
        simp only [not_true_eq_false, decide_false]
        cases commit with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, hs_win, not_true_eq_false]
          exact h
        | true =>
          have hs'_win :
              { s with st := Function.update s.st P st', win := false } =
                { s with st := Function.update s.st P st' } := by
            cases s; simp_all
          simp only [↓reduceIte, hs'_win, Function.update_self, hne]
          exact hinv'
    · simp only [ne_eq, hQ, not_false_eq_true, ↓reduceIte, not_true_eq_false]
      exact h

private theorem fgr_send_sent_length_le {PQ PQC : Type}
    (S : CryptoGames.LibsignalSession.Spqr PQ PQC) (s : SpqrGameState PQ)
    (P : CryptoGames.Party) (r : PQC) :
    s.sent.length ≤ (spqrSendStep S s P r).2.sent.length := by
  unfold spqrSendStep
  split
  · exact le_rfl
  · split
    · exact le_rfl
    · split
      · exact le_rfl
      · simp

private theorem fgr_deliver_sent_eq {PQ PQC : Type}
    (S : CryptoGames.LibsignalSession.Spqr PQ PQC) (s : SpqrGameState PQ)
    (P : CryptoGames.Party) (j : ℕ) (commit : Bool) :
    (spqrDeliverStep S s P j commit).2.sent = s.sent := by
  unfold spqrDeliverStep
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · split
          · rfl
          · split <;> rfl

private theorem fgr_goodRun_topInv (F : ShaCompress) (K : MlKem) (hout : OutWindowNoPanicStmt F K)
    (k : BitVec 256) (q : ℕ)
    (hq : q + 2000 ≤ 2 ^ 32) {s : SpqrGameState (List (BitVec 8))} {g : Ghost F}
    (hr : GoodRun F K k s g) (hlen : s.sent.length ≤ q) :
    TopInv F K k s g := by
  induction hr with
  | init stA stB hA hB =>
    exact topInv_init F K k stA stB hA hB
  | @send s g _ P r hkem ih =>
    have hs : s.sent.length ≤ q :=
      le_trans (fgr_send_sent_length_le (spqrV1SessionUniformCoins F K) s P r) hlen
    have hinv := ih hs
    obtain ⟨heq, hinv'⟩ := topInv_send F K k q hq s g hinv hs P r hkem
    simpa only [heq, ↓reduceIte] using hinv'
  | @deliver s g _ P j commit ih =>
    have hs : s.sent.length ≤ q := by
      rwa [fgr_deliver_sent_eq (spqrV1SessionUniformCoins F K) s P j commit] at hlen
    exact topInv_deliver F K hout k q hq s g (ih hs) hs P j commit

/-- Every `GoodRun` with at most `q` sends (`q + 2000 ≤ 2 ^ 32`) keeps `s.win = false`. -/
theorem goodRun_win_false (F : ShaCompress) (K : MlKem) (hout : OutWindowNoPanicStmt F K)
    (k : BitVec 256) (q : ℕ)
    (hq : q + 2000 ≤ 2 ^ 32) (s : SpqrGameState (List (BitVec 8))) (g : Ghost F)
    (hr : GoodRun F K k s g) (hlen : s.sent.length ≤ q) : s.win = false :=
  (fgr_goodRun_topInv F K hout k q hq hr hlen).hwin

theorem goodRun_topInv (F : ShaCompress) (K : MlKem) (hout : OutWindowNoPanicStmt F K)
    (k : BitVec 256) (q : ℕ)
    (hq : q + 2000 ≤ 2 ^ 32) (s : SpqrGameState (List (BitVec 8))) (g : Ghost F)
    (hr : GoodRun F K k s g) (hlen : s.sent.length ≤ q) : TopInv F K k s g :=
  fgr_goodRun_topInv F K hout k q hq hr hlen

/-! ## Honest FIFO schedules -/

open CryptoGames.LibsignalSpqrWindowHonest (SimState honestMsg spqrPos_honestMsg
  honest_fifo_in_window)

def sendIdx (sent : List (CryptoGames.Party × List (BitVec 8) × CryptoGames.HKDF.Salt))
    (Q : CryptoGames.Party) : List ℕ :=
  (List.range sent.length).filter fun j => decide ((sent[j]?.map Prod.fst) = some Q)

/-- Index in `s.sent` of the oldest undelivered message from `P.other` to `P`. -/
def fifoNext (s : SpqrGameState (List (BitVec 8))) (P : CryptoGames.Party) : Option ℕ :=
  (sendIdx s.sent P.other)[(s.st P).2.recvd.length]?

def pendingPos (s : SpqrGameState (List (BitVec 8))) (Q : CryptoGames.Party) : List (ℕ × ℕ) :=
  ((sendIdx s.sent Q).drop (s.st Q.other).2.recvd.length).filterMap fun j =>
    s.sent[j]?.bind fun p => spqrPos p.2.1

def maxRecvEpoch (log : SpqrLog) : ℕ :=
  (posList log.recvd).foldl (fun m p => max m p.1) 0

/-- `GoodRun` executions whose deliveries follow per-direction FIFO order without drops or replays. -/
inductive FifoRun (F : ShaCompress) (K : MlKem) (k : BitVec 256) :
    SpqrGameState (List (BitVec 8)) → Ghost F → Prop
  | init (stA stB : St F)
      (hA : States.init_a spqrPolyApi (spqrAuthApi F) (authOf k) = .ok stA)
      (hB : States.init_b spqrPolyApi (spqrAuthApi F) (authOf k) = .ok stB) :
      FifoRun F K k
        ⟨fun P => (spqrV1SessionUniformCoins F K).withLog.init (spqrDir P) k, [], false⟩
        (initGhost F k stA stB)
  | send {s : SpqrGameState (List (BitVec 8))} {g : Ghost F} (hr : FifoRun F K k s g)
      (P : CryptoGames.Party) (r : BitVec 512) (hkem : KemGood F K g P r) :
      FifoRun F K k (spqrSendStep (spqrV1SessionUniformCoins F K) s P r).2
        (if (spqrSendStep (spqrV1SessionUniformCoins F K) s P r).2.sent.length = s.sent.length + 1
          then ghostSend F K g P r else g)
  | deliver {s : SpqrGameState (List (BitVec 8))} {g : Ghost F} (hr : FifoRun F K k s g)
      (P : CryptoGames.Party) (j : ℕ) (hj : fifoNext s P = some j) :
      FifoRun F K k (spqrDeliverStep (spqrV1SessionUniformCoins F K) s P j true).2
        (if (spqrDeliverStep (spqrV1SessionUniformCoins F K) s P j true).2.st P ≠ s.st P
          then ghostDeliver F K g P j else g)

theorem FifoRun.goodRun {F : ShaCompress} {K : MlKem} {k : BitVec 256}
    {s : SpqrGameState (List (BitVec 8))} {g : Ghost F} (hr : FifoRun F K k s g) :
    GoodRun F K k s g := by
  induction hr with
  | init stA stB hA hB => exact .init stA stB hA hB
  | send _ P r hkem ih => exact .send ih P r hkem
  | deliver _ P j _ ih => exact .deliver ih P j true

/-- Simulation relation coupling `(s, g)` to `LibsignalSpqrWindowHonest.SimState` on header
positions. -/
structure FifoSim (F : ShaCompress) (s : SpqrGameState (List (BitVec 8))) (g : Ghost F)
    (sim : SimState) : Prop where
  hsent : ∀ P, posList (sim.log P).sent = posList (s.st P).2.sent
  hrecvd : ∀ P, posList (sim.log P).recvd = posList (s.st P).2.recvd
  hinFlight : ∀ Q, sim.inFlight Q = pendingPos s Q
  hcount : ∀ Q, (s.st Q.other).2.recvd.length ≤ (sendIdx s.sent Q).length
  hlast : ∀ P, sim.last P =
    ((s.st P).2.maxSendEpoch, g.sendCtr P ((s.st P).2.maxSendEpoch - 1))
  hmaxRecv : ∀ P, sim.maxRecv P = maxRecvEpoch (s.st P).2
  hhonest : sim.honest = true

/-- Invariant combining `TopInv`, braid epoch causality, and `FifoSim` for an honest simulator
schedule. -/
structure FifoAll (F : ShaCompress) (K : MlKem) (k : BitVec 256)
    (s : SpqrGameState (List (BitVec 8))) (g : Ghost F) : Prop where
  htop : TopInv F K k s g
  hcausal : ∀ P, (g.st P).epoch.toNat ≤ maxRecvEpoch (s.st P).2 + 1
  hsim : ∃ evs : List CryptoGames.LibsignalSpqrWindowHonest.Ev,
    (evs.filter CryptoGames.LibsignalSpqrWindowHonest.Ev.isSend).length = s.sent.length ∧
      FifoSim F s g (CryptoGames.LibsignalSpqrWindowHonest.run evs)

private theorem elf_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error _ => cases h
  | ok a => exact ⟨a, rfl, h⟩

private theorem elf_foldl_max_ge (L : List (ℕ × ℕ)) (a : ℕ) :
    a ≤ L.foldl (fun m p => max m p.1) a ∧ ∀ p ∈ L, p.1 ≤ L.foldl (fun m p => max m p.1) a := by
  induction L generalizing a with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨h1, h2⟩ := ih (max a x.1)
    simp only [List.foldl_cons]
    refine ⟨le_trans (le_max_left _ _) h1, fun p hp => ?_⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · exact le_trans (le_max_right _ _) h1
    · exact h2 p hp

theorem init_epoch (F : ShaCompress) (authKey : Bytes) (stA stB : St F)
    (hA : States.init_a spqrPolyApi (spqrAuthApi F) authKey = .ok stA)
    (hB : States.init_b spqrPolyApi (spqrAuthApi F) authKey = .ok stB) :
    stA.epoch = 1#64 ∧ stB.epoch = 1#64 := by
  constructor
  · unfold States.init_a Chunked.SendEk.KeysUnsampled.new Unchunked.SendEk.KeysUnsampled.new at hA
    obtain ⟨s1, h1, h2⟩ := elf_bind_ok hA
    cases h2
    obtain ⟨uc, h3, h4⟩ := elf_bind_ok h1
    cases h4
    obtain ⟨au, -, h6⟩ := elf_bind_ok h3
    cases h6
    rfl
  · unfold States.init_b Chunked.SendCt.NoHeaderReceived.new Unchunked.SendCt.NoHeaderReceived.new at hB
    obtain ⟨s1, h1, h2⟩ := elf_bind_ok hB
    cases h2
    obtain ⟨dr, -, h4⟩ := elf_bind_ok h1
    obtain ⟨uc, h5, h6⟩ := elf_bind_ok h4
    obtain ⟨au, -, h8⟩ := elf_bind_ok h5
    cases h8
    split at h6
    · cases h6
      rfl
    · cases h6

theorem ghostSend_st_other (F : ShaCompress) (K : MlKem) (g : Ghost F) (P Q : CryptoGames.Party)
    (r : BitVec 512) (hQ : Q ≠ P) : (ghostSend F K g P r).st Q = g.st Q := by
  unfold ghostSend
  split
  · exact Function.update_of_ne hQ _ _
  · rfl

theorem ghostDeliver_st_other (F : ShaCompress) (K : MlKem) (g : Ghost F) (P Q : CryptoGames.Party)
    (j : ℕ) (hQ : Q ≠ P) : (ghostDeliver F K g P j).st Q = g.st Q := by
  unfold ghostDeliver
  repeat' split
  all_goals first | rfl | exact Function.update_of_ne hQ _ _

theorem ghostDeliver_sendCtr (F : ShaCompress) (K : MlKem) (g : Ghost F) (P : CryptoGames.Party)
    (j : ℕ) : (ghostDeliver F K g P j).sendCtr = g.sendCtr := by
  unfold ghostDeliver
  repeat' split
  all_goals rfl

theorem recv_epoch_causal (F : ShaCompress) (K : MlKem) (st st' : St F) (m : Msg)
    (key : Option EpochSecret) (h : st.recv K m = .ok { key := key, state := st' }) :
    st'.epoch.toNat ≤ max st.epoch.toNat (m.epoch.toNat + 1) :=
  TopSync.rec_recv_epoch_causal F K st st' m key h

theorem ghostDeliver_epoch_le (F : ShaCompress) (K : MlKem) (g : Ghost F) (P : CryptoGames.Party)
    (j : ℕ) (m : Msg) (i : BitVec 32) (hj : g.sentB[j]? = some (m, i)) :
    ((ghostDeliver F K g P j).st P).epoch.toNat ≤
      max (g.st P).epoch.toNat (m.epoch.toNat + 1) := by
  unfold ghostDeliver
  rw [hj]
  dsimp only
  cases hrecv : (g.st P).recv K m with
  | error _ => exact le_max_left _ _
  | ok out =>
    have hc := recv_epoch_causal F K (g.st P) out.state m out.key hrecv
    dsimp only
    split
    · split <;> simpa only [Function.update_self] using hc
    · simpa only [Function.update_self] using hc

theorem withLog_recv_ok {PQ PQC : Type} (S : CryptoGames.LibsignalSession.Spqr PQ PQC)
    (st : PQ × SpqrLog) (msg : List (BitVec 8)) (st' : PQ × SpqrLog) (salt : CryptoGames.HKDF.Salt)
    (h : S.withLog.recv st msg = .ok (st', salt)) :
    S.recv st.1 msg = .ok (st'.1, salt) ∧ st'.2 = { st.2 with recvd := msg :: st.2.recvd } := by
  simp only [CryptoGames.LibsignalSession.Spqr.withLog] at h
  cases hr : S.recv st.1 msg with
  | error e => rw [hr] at h; cases h
  | ok x =>
    rw [hr] at h
    simp only [Except.map] at h
    cases h
    exact ⟨rfl, rfl⟩

theorem spqrSendStep_succ {PQ PQC : Type} (S : CryptoGames.LibsignalSession.Spqr PQ PQC)
    (s : SpqrGameState PQ) (P : CryptoGames.Party) (r : PQC)
    (h : (spqrSendStep S s P r).2.sent.length = s.sent.length + 1) :
    ∃ st' salt msg, S.send (s.st P).1 r = some (st', salt, msg) ∧
      (spqrSendStep S s P r).2 =
        { s with st := Function.update s.st P (st', { (s.st P).2 with sent := msg :: (s.st P).2.sent })
                 sent := s.sent ++ [(P, msg, salt)] } := by
  unfold spqrSendStep at h ⊢
  by_cases hw : s.win
  · simp [hw] at h
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hw)] at h ⊢
    by_cases hp : S.sendPanics (s.st P).1 r = true
    · simp [CryptoGames.LibsignalSession.Spqr.withLog, hp] at h
    · cases hs : S.send (s.st P).1 r with
      | none => simp [CryptoGames.LibsignalSession.Spqr.withLog, hs, hp] at h
      | some x =>
        obtain ⟨st', salt, msg⟩ := x
        refine ⟨st', salt, msg, rfl, ?_⟩
        simp [CryptoGames.LibsignalSession.Spqr.withLog, hs, hp]

theorem spqrSendStep_sent_length {PQ PQC : Type} (S : CryptoGames.LibsignalSession.Spqr PQ PQC)
    (s : SpqrGameState PQ) (P : CryptoGames.Party) (r : PQC) :
    s.sent.length ≤ (spqrSendStep S s P r).2.sent.length := by
  unfold spqrSendStep
  split
  · exact le_rfl
  · split
    · exact le_rfl
    · split
      · exact le_rfl
      · simp

theorem spqrDeliverStep_sent {PQ PQC : Type} (S : CryptoGames.LibsignalSession.Spqr PQ PQC)
    (s : SpqrGameState PQ) (P : CryptoGames.Party) (j : ℕ) (commit : Bool) :
    (spqrDeliverStep S s P j commit).2.sent = s.sent := by
  unfold spqrDeliverStep
  repeat' split
  all_goals rfl

theorem spqrDeliverStep_accept {PQ PQC : Type} (S : CryptoGames.LibsignalSession.Spqr PQ PQC)
    (s : SpqrGameState PQ) (P : CryptoGames.Party) (j : ℕ) (msg : List (BitVec 8))
    (salt : CryptoGames.HKDF.Salt) (st' : PQ × SpqrLog) (hwin : s.win = false)
    (hj : s.sent[j]? = some (P.other, msg, salt))
    (hrecv : S.withLog.recv (s.st P) msg = .ok (st', salt))
    (hnp : S.withLog.recvPanics (s.st P) msg = false) :
    spqrDeliverStep S s P j true = (some salt, { s with st := Function.update s.st P st' }) := by
  simp only [spqrDeliverStep, hwin, hj, hnp, hrecv, Bool.false_eq_true, ↓reduceIte, ne_eq,
    not_true_eq_false, decide_false]

theorem sendIdx_append_self (sent : List (CryptoGames.Party × List (BitVec 8) × CryptoGames.HKDF.Salt))
    (Q : CryptoGames.Party) (x : List (BitVec 8) × CryptoGames.HKDF.Salt) :
    sendIdx (sent ++ [(Q, x)]) Q = sendIdx sent Q ++ [sent.length] := by
  unfold sendIdx
  rw [List.length_append, List.length_singleton, List.range_succ, List.filter_append]
  congr 1
  · apply List.filter_congr
    intro i hi
    rw [List.mem_range] at hi
    simp only [List.getElem?_append_left hi]
  · simp

theorem sendIdx_append_other (sent : List (CryptoGames.Party × List (BitVec 8) × CryptoGames.HKDF.Salt))
    (Q Q' : CryptoGames.Party) (x : List (BitVec 8) × CryptoGames.HKDF.Salt) (hQ : Q' ≠ Q) :
    sendIdx (sent ++ [(Q, x)]) Q' = sendIdx sent Q' := by
  unfold sendIdx
  rw [List.length_append, List.length_singleton, List.range_succ, List.filter_append]
  have h2 : List.filter (fun j => decide (((sent ++ [(Q, x)])[j]?.map Prod.fst) = some Q'))
      [sent.length] = [] := by
    simp [Ne.symm hQ]
  rw [h2, List.append_nil]
  apply List.filter_congr
  intro i hi
  rw [List.mem_range] at hi
  simp only [List.getElem?_append_left hi]

theorem fifoNext_sent (s : SpqrGameState (List (BitVec 8))) (P : CryptoGames.Party) (j : ℕ)
    (hj : fifoNext s P = some j) :
    ∃ msg salt, s.sent[j]? = some (P.other, msg, salt) := by
  unfold fifoNext at hj
  have hmem : j ∈ sendIdx s.sent P.other := List.mem_of_getElem? hj
  unfold sendIdx at hmem
  rw [List.mem_filter, List.mem_range, decide_eq_true_eq] at hmem
  obtain ⟨_, hQ⟩ := hmem
  cases hs : s.sent[j]? with
  | none => rw [hs] at hQ; cases hQ
  | some p =>
    rw [hs] at hQ
    obtain ⟨Q, msg, salt⟩ := p
    simp only [Option.map_some, Option.some.injEq] at hQ
    subst hQ
    exact ⟨msg, salt, rfl⟩

theorem pendingPos_head (s : SpqrGameState (List (BitVec 8))) (P : CryptoGames.Party) (j : ℕ)
    (hj : fifoNext s P = some j) (msg : List (BitVec 8)) (salt : CryptoGames.HKDF.Salt)
    (hjs : s.sent[j]? = some (P.other, msg, salt)) (E i : ℕ) (hpos : spqrPos msg = some (E, i)) :
    pendingPos s P.other = (E, i) ::
      ((sendIdx s.sent P.other).drop ((s.st P).2.recvd.length + 1)).filterMap fun j =>
        s.sent[j]?.bind fun p => spqrPos p.2.1 := by
  unfold fifoNext at hj
  unfold pendingPos
  rw [CryptoGames.Party.other_other]
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hj
  rw [List.drop_eq_getElem_cons hlt, hget]
  simp only [List.filterMap_cons, hjs, Option.bind_some, hpos]

theorem sendIdx_lt (sent : List (CryptoGames.Party × List (BitVec 8) × CryptoGames.HKDF.Salt))
    (Q : CryptoGames.Party) (j : ℕ) (hj : j ∈ sendIdx sent Q) : j < sent.length := by
  unfold sendIdx at hj
  exact List.mem_range.mp (List.mem_filter.mp hj).1

theorem filterMap_sent_append
    (sent : List (CryptoGames.Party × List (BitVec 8) × CryptoGames.HKDF.Salt))
    (x : CryptoGames.Party × List (BitVec 8) × CryptoGames.HKDF.Salt) (Q : CryptoGames.Party)
    (n : ℕ) :
    ((sendIdx sent Q).drop n).filterMap (fun j => (sent ++ [x])[j]?.bind fun p => spqrPos p.2.1) =
      ((sendIdx sent Q).drop n).filterMap (fun j => sent[j]?.bind fun p => spqrPos p.2.1) := by
  apply List.filterMap_congr
  intro j hj
  rw [List.getElem?_append_left (sendIdx_lt sent Q j (List.mem_of_mem_drop hj))]

private theorem elf_drop_append_of_le {α : Type} (l1 l2 : List α) (n : ℕ) (h : n ≤ l1.length) :
    (l1 ++ l2).drop n = l1.drop n ++ l2 := by
  induction l1 generalizing n with
  | nil => simp at h; subst h; rfl
  | cons a l ih =>
    cases n with
    | zero => rfl
    | succ n => simp only [List.cons_append, List.drop_succ_cons]; exact ih n (by simpa using h)

theorem le_maxSendEpoch (log : SpqrLog) (E i : ℕ) (h : (E, i) ∈ posList log.sent) :
    E ≤ log.maxSendEpoch := by
  exact (elf_foldl_max_ge _ 0).2 _ h

theorem sendCtr_eq_zero_of_lt {log : SpqrLog} {sE : ℕ} {sC : ℕ → ℕ} {R : ℕ → Finset ℕ}
    (h : LogAgree log sE sC R) (E : ℕ) (hE : 1 ≤ E) (hlt : log.maxSendEpoch < E) :
    sC (E - 1) = 0 := by
  by_contra hne
  have hmem : (E, 1) ∈ posList log.sent := (h.hsent E 1).mpr ⟨hE, le_refl 1, by omega⟩
  have := le_maxSendEpoch log E 1 hmem
  omega

theorem PartyOk.maxSendEpoch_le {F : ShaCompress} {K : MlKem} {k : BitVec 256}
    {s : SpqrGameState (List (BitVec 8))} {g : Ghost F} {P : CryptoGames.Party}
    (h : PartyOk F K k s g P) : (s.st P).2.maxSendEpoch ≤ (g.st P).epoch.toNat := by
  obtain ⟨sE, hpt, hla⟩ := h
  obtain ⟨vn?, ch?, chE, hw⟩ := hpt
  have h1 := hla.hsE
  have h2 := hw.hsendLe
  omega

theorem maxRecvEpoch_cons (log : SpqrLog) (m : List (BitVec 8)) (E i : ℕ)
    (hpos : spqrPos m = some (E, i)) :
    maxRecvEpoch { log with recvd := m :: log.recvd } = max E (maxRecvEpoch log) := by
  unfold maxRecvEpoch
  simp only [posList, List.filterMap_cons, hpos]
  exact els_foldl_max_cons (fun p : ℕ × ℕ => p.1) (E, i) _

theorem send_step_shape (F : ShaCompress) (K : MlKem) (k : BitVec 256) (q : ℕ)
    (hq : q + 2000 ≤ 2 ^ 32) (s : SpqrGameState (List (BitVec 8))) (g : Ghost F)
    (h : TopInv F K k s g) (hlen : s.sent.length ≤ q) (P : CryptoGames.Party) (r : BitVec 512)
    (hkem : KemGood F K g P r) :
    ∃ bytes' salt msg,
      (spqrSendStep (spqrV1SessionUniformCoins F K) s P r).2 =
        { s with
          st := Function.update s.st P (bytes', { (s.st P).2 with sent := msg :: (s.st P).2.sent })
          sent := s.sent ++ [(P, msg, salt)] } ∧
      spqrPos msg = some ((g.st P).epoch.toNat,
        g.sendCtr P ((g.st P).epoch.toNat - 1) + 1) ∧
      ((ghostSend F K g P r).st P).epoch = (g.st P).epoch ∧
      (ghostSend F K g P r).sendCtr = Function.update g.sendCtr P
        (Function.update (g.sendCtr P) ((g.st P).epoch.toNat - 1)
          (g.sendCtr P ((g.st P).epoch.toNat - 1) + 1)) := by
  obtain ⟨hsucc, hinv'⟩ := topInv_send F K k q hq s g h hlen P r hkem
  obtain ⟨bytes', salt, msg, -, hstep⟩ := spqrSendStep_succ (spqrV1SessionUniformCoins F K) s P r hsucc
  refine ⟨bytes', salt, msg, hstep, ?_⟩
  cases hbraid : (g.st P).send K (coinBytes r) with
  | error _ =>
    have hlen' := hinv'.hsentLen
    have hlen0 := h.hsentLen
    simp only [ghostSend, hbraid] at hlen'
    omega
  | ok val =>
    rcases val with ⟨⟨m, key, st'⟩, tape'⟩
    obtain ⟨hm_ep, hst'_ep, -, -⟩ :=
      TopSync.send_facts F K (g.st P) st' (coinBytes r) tape' m key hbraid
    have hget_sent :
        (spqrSendStep (spqrV1SessionUniformCoins F K) s P r).2.sent[s.sent.length]? =
          some (P, msg, salt) := by
      rw [hstep]
      simp
    obtain ⟨m', i', hget_sentB, hmsg, -, hE1, -, -, -, -⟩ :=
      hinv'.hsent s.sent.length P msg salt hget_sent
    have hget_sentB' :
        (ghostSend F K g P r).sentB[s.sent.length]? =
          some (m, BitVec.ofNat 32 (g.sendCtr P ((g.st P).epoch.toNat - 1) + 1)) := by
      simp only [ghostSend, hbraid, hm_ep, h.hsentLen, List.getElem?_append_right (le_refl _),
        Nat.sub_self, List.getElem?_cons_zero]
    rw [hget_sentB'] at hget_sentB
    cases hget_sentB
    have hE_ne : m.epoch ≠ 0#64 := by
      intro h0
      rw [h0] at hE1
      simp at hE1
    obtain ⟨sE, -, hla⟩ := h.hparty P
    have hctr_le : g.sendCtr P ((g.st P).epoch.toNat - 1) ≤ (s.st P).2.sent.length :=
      sendCtr_le_length hla (g.st P).epoch.toNat (hm_ep ▸ hE1)
    have hlog_le := h.hlogSent P
    have hi_toNat :
        (BitVec.ofNat 32 (g.sendCtr P ((g.st P).epoch.toNat - 1) + 1)).toNat =
          g.sendCtr P ((g.st P).epoch.toNat - 1) + 1 := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    refine ⟨?_, ?_, ?_⟩
    · rw [hmsg, spqrPos_serialize m _ hE_ne, hm_ep, hi_toNat]
    · simp only [ghostSend, hbraid, Function.update_self, hst'_ep]
    · simp only [ghostSend, hbraid, hm_ep]

theorem fifoAll_init (F : ShaCompress) (K : MlKem) (k : BitVec 256) (stA stB : St F)
    (hA : States.init_a spqrPolyApi (spqrAuthApi F) (authOf k) = .ok stA)
    (hB : States.init_b spqrPolyApi (spqrAuthApi F) (authOf k) = .ok stB) :
    FifoAll F K k ⟨fun P => (spqrV1SessionUniformCoins F K).withLog.init (spqrDir P) k, [], false⟩
      (initGhost F k stA stB) := by
  have hep := init_epoch F (authOf k) stA stB hA hB
  refine ⟨topInv_init F K k stA stB hA hB, ?_, [], rfl, ?_⟩
  · intro P
    cases P <;> simp [initGhost, hep.1, hep.2]
  · exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => Nat.zero_le _, fun _ => rfl,
      fun _ => rfl, rfl⟩

theorem fifo_window (F : ShaCompress) (K : MlKem) (k : BitVec 256)
    (s : SpqrGameState (List (BitVec 8))) (g : Ghost F) (h : FifoAll F K k s g)
    (hlen : s.sent.length < 2 ^ 32) (P : CryptoGames.Party) (j : ℕ) (hj : fifoNext s P = some j) :
    ∃ msg salt, s.sent[j]? = some (P.other, msg, salt) ∧ spqrWindowOk (s.st P).2 msg = true := by
  obtain ⟨msg, salt, hjs⟩ := fifoNext_sent s P j hj
  refine ⟨msg, salt, hjs, ?_⟩
  obtain ⟨m, i, -, hmsg, -, hE1, -, -, -, -⟩ := h.htop.hsent j P.other msg salt hjs
  have hE0 : m.epoch ≠ 0#64 := by
    intro h0
    rw [h0] at hE1
    simp at hE1
  have hpos : spqrPos msg = some (m.epoch.toNat, i.toNat) := by
    rw [hmsg]; exact spqrPos_serialize m i hE0
  obtain ⟨evs, hcnt, hsim⟩ := h.hsim
  have hfl := hsim.hinFlight P.other
  rw [pendingPos_head s P j hj msg salt hjs _ _ hpos] at hfl
  have hrun : CryptoGames.LibsignalSpqrWindowHonest.run
      (evs ++ [CryptoGames.LibsignalSpqrWindowHonest.Ev.deliver P]) =
      (CryptoGames.LibsignalSpqrWindowHonest.run evs).step
        (CryptoGames.LibsignalSpqrWindowHonest.Ev.deliver P) := by
    simp only [CryptoGames.LibsignalSpqrWindowHonest.run, List.foldl_append, List.foldl_cons,
      List.foldl_nil]
  have hhon : (CryptoGames.LibsignalSpqrWindowHonest.run
      (evs ++ [CryptoGames.LibsignalSpqrWindowHonest.Ev.deliver P])).honest = true := by
    rw [hrun]
    simp only [SimState.step, hfl]
    exact hsim.hhonest
  have hq' : ((evs ++ [CryptoGames.LibsignalSpqrWindowHonest.Ev.deliver P]).filter
      CryptoGames.LibsignalSpqrWindowHonest.Ev.isSend).length < 2 ^ 32 := by
    rw [List.filter_append, List.length_append, hcnt]
    simpa [CryptoGames.LibsignalSpqrWindowHonest.Ev.isSend] using hlen
  have hw := honest_fifo_in_window _ hq' hhon
  rw [hrun] at hw
  simp only [SimState.step, hfl, Bool.and_eq_true] at hw
  have hE64 : m.epoch.toNat < 2 ^ 64 := m.epoch.isLt
  have hi32 : i.toNat < 2 ^ 32 := i.isLt
  have hm : spqrPos msg = spqrPos (honestMsg m.epoch.toNat i.toNat) := by
    rw [hpos, spqrPos_honestMsg hE1 hE64 hi32]
  rw [spqrWindowOk_congr (m := msg) (m' := honestMsg m.epoch.toNat i.toNat)
    (hsim.hsent P).symm (hsim.hrecvd P).symm hm]
  exact hw.2

theorem fifoAll_send (F : ShaCompress) (K : MlKem) (k : BitVec 256) (q : ℕ)
    (hq : q + 2000 ≤ 2 ^ 32) (s : SpqrGameState (List (BitVec 8))) (g : Ghost F)
    (h : FifoAll F K k s g) (hlen : s.sent.length ≤ q) (P : CryptoGames.Party) (r : BitVec 512)
    (hkem : KemGood F K g P r) :
    (spqrSendStep (spqrV1SessionUniformCoins F K) s P r).2.sent.length = s.sent.length + 1 ∧
      FifoAll F K k (spqrSendStep (spqrV1SessionUniformCoins F K) s P r).2 (ghostSend F K g P r) := by
  obtain ⟨hsucc, htop'⟩ := topInv_send F K k q hq s g h.htop hlen P r hkem
  obtain ⟨bytes', salt, msg, hstep, hpos0, hep, hctr⟩ :=
    send_step_shape F K k q hq s g h.htop hlen P r hkem
  refine ⟨hsucc, ?_⟩
  rw [hstep] at htop' ⊢
  have hne : P.other ≠ P := CryptoGames.Party.other_ne P
  have hQo : ∀ Q, Q ≠ P → Q.other = P := by
    intro Q hQ; cases P <;> cases Q <;> first | rfl | exact absurd rfl hQ
  obtain ⟨sE, hpt, hla⟩ := h.htop.hparty P
  have hE1 : 1 ≤ (g.st P).epoch.toNat := TopSync.partyTop_epoch_pos hpt
  have hE64 : (g.st P).epoch.toNat < 2 ^ 64 := (g.st P).epoch.isLt
  have hn : g.sendCtr P ((g.st P).epoch.toNat - 1) ≤ s.sent.length :=
    le_trans (sendCtr_le_length hla _ hE1) (h.htop.hlogSent P)
  have hn32 : g.sendCtr P ((g.st P).epoch.toNat - 1) + 1 < 2 ^ 32 := by omega
  have hMle : (s.st P).2.maxSendEpoch ≤ (g.st P).epoch.toNat :=
    (h.htop.hparty P).maxSendEpoch_le
  have hposH : spqrPos (honestMsg (g.st P).epoch.toNat
      (g.sendCtr P ((g.st P).epoch.toNat - 1) + 1)) =
      some ((g.st P).epoch.toNat, g.sendCtr P ((g.st P).epoch.toNat - 1) + 1) :=
    spqrPos_honestMsg hE1 hE64 hn32
  obtain ⟨evs, hcnt, hsim⟩ := h.hsim
  have ham : (if ((CryptoGames.LibsignalSpqrWindowHonest.run evs).last P).1 =
        (g.st P).epoch.toNat
      then ((CryptoGames.LibsignalSpqrWindowHonest.run evs).last P).2 + 1 else 1) =
      g.sendCtr P ((g.st P).epoch.toNat - 1) + 1 := by
    rw [hsim.hlast P]
    dsimp only
    split
    · rename_i heq; rw [heq]
    · rename_i hneq
      rw [sendCtr_eq_zero_of_lt hla _ hE1 (lt_of_le_of_ne hMle hneq)]
  have hrun : CryptoGames.LibsignalSpqrWindowHonest.run
      (evs ++ [CryptoGames.LibsignalSpqrWindowHonest.Ev.send P (g.st P).epoch.toNat]) =
      (CryptoGames.LibsignalSpqrWindowHonest.run evs).step
        (CryptoGames.LibsignalSpqrWindowHonest.Ev.send P (g.st P).epoch.toNat) := by
    simp only [CryptoGames.LibsignalSpqrWindowHonest.run, List.foldl_append, List.foldl_cons,
      List.foldl_nil]
  refine ⟨htop', ?_,
    evs ++ [CryptoGames.LibsignalSpqrWindowHonest.Ev.send P (g.st P).epoch.toNat], ?_, ?_⟩
  · intro Q
    by_cases hQ : Q = P
    · subst Q
      simp only [Function.update_self, hep]
      exact h.hcausal P
    · simp only [Function.update_of_ne hQ, ghostSend_st_other F K g P Q r hQ]
      exact h.hcausal Q
  · rw [List.filter_append, List.length_append, hcnt]
    simp only [List.length_append, List.length_singleton]
    rfl
  · rw [hrun]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro Q
      by_cases hQ : Q = P
      · subst Q
        have h0 := hsim.hsent P
        simp only [posList] at h0 ⊢
        simp only [SimState.step, Function.update_self]
        rw [ham]
        simp only [List.filterMap_cons, hposH, hpos0, h0]
      · simp only [SimState.step, Function.update_of_ne hQ]
        exact hsim.hsent Q
    · intro Q
      by_cases hQ : Q = P
      · subst Q
        simp only [SimState.step, Function.update_self]
        exact hsim.hrecvd P
      · simp only [SimState.step, Function.update_of_ne hQ]
        exact hsim.hrecvd Q
    · intro Q
      by_cases hQ : Q = P
      · subst Q
        simp only [SimState.step, Function.update_self]
        rw [ham, hsim.hinFlight P]
        unfold pendingPos
        simp only [Function.update_of_ne hne]
        rw [sendIdx_append_self, elf_drop_append_of_le _ _ _ (hsim.hcount P), List.filterMap_append,
          filterMap_sent_append]
        simp [hpos0]
      · simp only [SimState.step, Function.update_of_ne hQ]
        rw [hsim.hinFlight Q]
        unfold pendingPos
        rw [hQo Q hQ]
        simp only [Function.update_self]
        rw [sendIdx_append_other _ _ _ _ hQ, filterMap_sent_append]
    · intro Q
      by_cases hQ : Q = P
      · subst Q
        simp only [Function.update_of_ne hne]
        rw [sendIdx_append_self, List.length_append, List.length_singleton]
        have := hsim.hcount P
        omega
      · have := hsim.hcount Q
        rw [hQo Q hQ] at this ⊢
        simp only [Function.update_self]
        rw [sendIdx_append_other _ _ _ _ hQ]
        exact this
    · intro Q
      by_cases hQ : Q = P
      · subst Q
        simp only [SimState.step, Function.update_self]
        rw [ham, hctr]
        have hM : ({ (s.st P).2 with sent := msg :: (s.st P).2.sent } : SpqrLog).maxSendEpoch =
            (g.st P).epoch.toNat := by
          rw [els_maxSendEpoch_cons _ _ _ _ hpos0]; omega
        rw [hM]
        simp only [Function.update_self]
      · simp only [SimState.step, Function.update_of_ne hQ]
        rw [hsim.hlast Q, hctr]
        simp only [Function.update_of_ne hQ]
    · intro Q
      by_cases hQ : Q = P
      · subst Q
        simp only [SimState.step, Function.update_self]
        rw [hsim.hmaxRecv P]
        rfl
      · simp only [SimState.step, Function.update_of_ne hQ]
        exact hsim.hmaxRecv Q
    · simp [SimState.step, hsim.hhonest, hsim.hlast P, hsim.hmaxRecv P, hE1, hMle, h.hcausal P]

theorem fifoAll_deliver (F : ShaCompress) (K : MlKem) (k : BitVec 256) (q : ℕ)
    (hq : q + 2000 ≤ 2 ^ 32) (s : SpqrGameState (List (BitVec 8))) (g : Ghost F)
    (h : FifoAll F K k s g) (hlen : s.sent.length ≤ q) (P : CryptoGames.Party) (j : ℕ)
    (hj : fifoNext s P = some j) :
    (spqrDeliverStep (spqrV1SessionUniformCoins F K) s P j true).2.st P ≠ s.st P ∧
      FifoAll F K k (spqrDeliverStep (spqrV1SessionUniformCoins F K) s P j true).2 (ghostDeliver F K g P j) := by
  have hlt : s.sent.length < 2 ^ 32 := by omega
  obtain ⟨msg, salt, hjs, hwin⟩ := fifo_window F K k s g h hlt P j hj
  obtain ⟨st', hrecv, hst', htop'⟩ :=
    deliver_inWindow F K k q hq s g h.htop hlen P j msg salt hjs hwin
  rw [spqrDeliverStep_accept (spqrV1SessionUniformCoins F K) s P j msg salt st' h.htop.hwin hjs hrecv
    (tl_recvPanics_eq_false_of_ok F K (s.st P) msg st' salt hrecv)]
  dsimp only
  refine ⟨by simp only [Function.update_self]; exact hst', ?_⟩
  obtain ⟨-, hlog⟩ := withLog_recv_ok (spqrV1SessionUniformCoins F K) (s.st P) msg st' salt hrecv
  obtain ⟨m, i, hmi, hmsg, -, hE1, -, -, -, -⟩ := h.htop.hsent j P.other msg salt hjs
  have hE0 : m.epoch ≠ 0#64 := by
    intro h0
    rw [h0] at hE1
    simp at hE1
  have hpos : spqrPos msg = some (m.epoch.toNat, i.toNat) := by
    rw [hmsg]; exact spqrPos_serialize m i hE0
  have hposH : spqrPos (honestMsg m.epoch.toNat i.toNat) = some (m.epoch.toNat, i.toNat) :=
    spqrPos_honestMsg hE1 m.epoch.isLt i.isLt
  have hne : P.other ≠ P := CryptoGames.Party.other_ne P
  have hj' : (sendIdx s.sent P.other)[(s.st P).2.recvd.length]? = some j := hj
  obtain ⟨hltj, -⟩ := List.getElem?_eq_some_iff.mp hj'
  obtain ⟨evs, hcnt, hsim⟩ := h.hsim
  have hfl := hsim.hinFlight P.other
  rw [pendingPos_head s P j hj msg salt hjs _ _ hpos] at hfl
  have hrun : CryptoGames.LibsignalSpqrWindowHonest.run
      (evs ++ [CryptoGames.LibsignalSpqrWindowHonest.Ev.deliver P]) =
      (CryptoGames.LibsignalSpqrWindowHonest.run evs).step
        (CryptoGames.LibsignalSpqrWindowHonest.Ev.deliver P) := by
    simp only [CryptoGames.LibsignalSpqrWindowHonest.run, List.foldl_append, List.foldl_cons,
      List.foldl_nil]
  have hmaxR : maxRecvEpoch st'.2 = max m.epoch.toNat (maxRecvEpoch (s.st P).2) := by
    rw [hlog]; exact maxRecvEpoch_cons _ _ _ _ hpos
  refine ⟨htop', ?_, evs ++ [CryptoGames.LibsignalSpqrWindowHonest.Ev.deliver P], ?_, ?_⟩
  · intro Q
    by_cases hQ : Q = P
    · subst Q
      simp only [Function.update_self]
      rw [hmaxR]
      have h1 := ghostDeliver_epoch_le F K g P j m i hmi
      have h2 := h.hcausal P
      have h3 : max (g.st P).epoch.toNat (m.epoch.toNat + 1) ≤
          max m.epoch.toNat (maxRecvEpoch (s.st P).2) + 1 := by
        apply max_le
        · exact le_trans h2 (Nat.add_le_add_right (le_max_right _ _) 1)
        · exact Nat.add_le_add_right (le_max_left _ _) 1
      exact le_trans h1 h3
    · simp only [Function.update_of_ne hQ, ghostDeliver_st_other F K g P Q j hQ]
      exact h.hcausal Q
  · rw [List.filter_append, List.length_append, hcnt]
    rfl
  · rw [hrun]
    simp only [SimState.step, hfl]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro Q
      by_cases hQ : Q = P
      · subst Q
        simp only [Function.update_self, hlog]
        exact hsim.hsent P
      · simp only [Function.update_of_ne hQ]
        exact hsim.hsent Q
    · intro Q
      by_cases hQ : Q = P
      · subst Q
        have h0 := hsim.hrecvd P
        simp only [posList] at h0 ⊢
        simp only [Function.update_self, hlog, List.filterMap_cons, hposH, hpos, h0]
      · simp only [Function.update_of_ne hQ]
        exact hsim.hrecvd Q
    · intro Q
      by_cases hQ : Q = P.other
      · subst Q
        simp only [Function.update_self]
        unfold pendingPos
        simp only [CryptoGames.Party.other_other, Function.update_self, hlog, List.length_cons]
      · have hQP : Q = P := by
          cases P <;> cases Q <;> first | rfl | exact absurd rfl hQ
        subst Q
        simp only [Function.update_of_ne hne.symm]
        rw [hsim.hinFlight P]
        unfold pendingPos
        simp only [Function.update_of_ne hne]
    · intro Q
      by_cases hQ : Q = P.other
      · subst Q
        simp only [CryptoGames.Party.other_other, Function.update_self, hlog, List.length_cons]
        omega
      · have hQP : Q = P := by
          cases P <;> cases Q <;> first | rfl | exact absurd rfl hQ
        subst Q
        simp only [Function.update_of_ne hne]
        exact hsim.hcount P
    · intro Q
      by_cases hQ : Q = P
      · subst Q
        simp only [Function.update_self, hlog, ghostDeliver_sendCtr]
        exact hsim.hlast P
      · simp only [Function.update_of_ne hQ, ghostDeliver_sendCtr]
        exact hsim.hlast Q
    · intro Q
      by_cases hQ : Q = P
      · subst Q
        simp only [Function.update_self]
        rw [hmaxR, hsim.hmaxRecv P, max_comm]
      · simp only [Function.update_of_ne hQ]
        exact hsim.hmaxRecv Q
    · exact hsim.hhonest

theorem fifoRun_fifoAll (F : ShaCompress) (K : MlKem) (k : BitVec 256) (q : ℕ)
    (hq : q + 2000 ≤ 2 ^ 32) (s : SpqrGameState (List (BitVec 8))) (g : Ghost F)
    (hr : FifoRun F K k s g) (hlen : s.sent.length ≤ q) : FifoAll F K k s g := by
  revert hlen
  induction hr with
  | init stA stB hA hB => intro _; exact fifoAll_init F K k stA stB hA hB
  | @send s g _ P r hkem ih =>
    intro hlen
    have hle := spqrSendStep_sent_length (spqrV1SessionUniformCoins F K) s P r
    obtain ⟨hsucc, hnew⟩ :=
      fifoAll_send F K k q hq s g (ih (le_trans hle hlen)) (le_trans hle hlen) P r hkem
    rw [ite_eq_left_of_eq_true _ _ (eq_true hsucc)]
    exact hnew
  | @deliver s g _ P j hj ih =>
    intro hlen
    have hsent := spqrDeliverStep_sent (spqrV1SessionUniformCoins F K) s P j true
    have hlen0 : s.sent.length ≤ q := by rw [← hsent]; exact hlen
    obtain ⟨hne, hnew⟩ := fifoAll_deliver F K k q hq s g (ih hlen0) hlen0 P j hj
    rw [ite_eq_left_of_eq_true _ _ (eq_true hne)]
    exact hnew

/-- Every `FifoRun` with at most `q` sends (`q + 2000 ≤ 2 ^ 32`) keeps `s.win = false` and accepts
each next FIFO delivery with the sender's salt. -/
theorem fifoRun_accepted (F : ShaCompress) (K : MlKem) (k : BitVec 256) (q : ℕ)
    (hq : q + 2000 ≤ 2 ^ 32) (s : SpqrGameState (List (BitVec 8))) (g : Ghost F)
    (hr : FifoRun F K k s g) (hlen : s.sent.length ≤ q) :
    s.win = false ∧
      ∀ P j, fifoNext s P = some j →
        ∃ msg salt st', s.sent[j]? = some (P.other, msg, salt) ∧
          spqrWindowOk (s.st P).2 msg = true ∧
          (spqrV1SessionUniformCoins F K).withLog.recv (s.st P) msg = .ok (st', salt) ∧
          spqrDeliverStep (spqrV1SessionUniformCoins F K) s P j true =
            (some salt, { s with st := Function.update s.st P st' }) := by
  have hfa := fifoRun_fifoAll F K k q hq s g hr hlen
  refine ⟨hfa.htop.hwin, fun P j hj => ?_⟩
  obtain ⟨msg, salt, hjs, hwin⟩ := fifo_window F K k s g hfa (by omega) P j hj
  obtain ⟨st', hrecv, -, -⟩ :=
    deliver_inWindow F K k q hq s g hfa.htop hlen P j msg salt hjs hwin
  exact ⟨msg, salt, st', hjs, hwin, hrecv,
    spqrDeliverStep_accept _ s P j msg salt st' hfa.htop.hwin hjs hrecv
      (tl_recvPanics_eq_false_of_ok F K (s.st P) msg st' salt hrecv)⟩

/-- Every `KemGood` send step from a `FifoRun` with at most `q` sends appends to `s.sent`. -/
theorem fifoRun_send_ok (F : ShaCompress) (K : MlKem) (k : BitVec 256) (q : ℕ)
    (hq : q + 2000 ≤ 2 ^ 32) (s : SpqrGameState (List (BitVec 8))) (g : Ghost F)
    (hr : FifoRun F K k s g) (hlen : s.sent.length ≤ q) (P : CryptoGames.Party) (r : BitVec 512)
    (hkem : KemGood F K g P r) :
    (spqrSendStep (spqrV1SessionUniformCoins F K) s P r).2.sent.length = s.sent.length + 1 := by
  exact (fifoAll_send F K k q hq s g (fifoRun_fifoAll F K k q hq s g hr hlen) hlen P r hkem).1

end CryptoVerification.SpqrV1Sync.TopLog
