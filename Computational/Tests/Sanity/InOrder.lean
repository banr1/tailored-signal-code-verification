/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Construction
public import Computational.Proofs.CryptoGames.AEAD.PrimitivesProofDefs

/-!
# Perfect Correctness of the In-Order FS-AEAD Ratchet

**Checked by Lean.**

For the strict in-order ratchet `fromAEADPRG ae G 0` (`maxSkip = 0`) over a correct AEAD
(`ae.Correct`), the FS-AEAD `deliver` oracle never changes `win` (`deliver_win_eq`,
`Reachable.deliver_win_eq`), so `win` can only be set by an accepted forgery via `inject`.
Every state reachable from `initState` maintains the invariant `Inv k st`: `A` and `B` lie on the
same PRG chain `chainKeyAt G k` with no skipped keys, in-transit records carry honest encryptions,
and while `win = false` every uncompromised in-transit record has `receiverIdx < idx`. Because
`receive` with `maxSkip = 0` accepts only `receiverIdx + 1` and advances the chain independently of
the ciphertext, accepted injections keep `B` on the chain while uncompromised in-window deliveries
match `receiverIdx + 1` and decrypt honestly.
-/

@[expose] public section

namespace CryptoGames.FSAEAD.InOrder

variable {ChainKey MessageKey AssocData Message Ciphertext : Type}
  (ae : AEADScheme MessageKey (ℕ × AssocData) Message Ciphertext)
  (G : ℕ → PRGScheme ChainKey (ChainKey × MessageKey))

/-- Chain key after `n` PRG steps from `k`, where step `n` applies `G n`. -/
def chainKeyAt (k : ChainKey) : ℕ → ChainKey
  | 0 => k
  | n + 1 => ((G n).gen (chainKeyAt k n)).1

/-- Message key of index `i ≥ 1`: derived from the chain key after `i - 1` steps. -/
def messageKeyAt (k : ChainKey) (i : ℕ) : MessageKey :=
  ((G (i - 1)).gen (chainKeyAt G k (i - 1))).2

theorem send_chain (k : ChainKey) (L : ℕ) (a : AssocData) (m : Message) :
    (fromAEADPRG ae G 0).send ⟨chainKeyAt G k L, L⟩ a m =
      (⟨chainKeyAt G k (L + 1), L + 1⟩,
        (L + 1, ae.enc (messageKeyAt G k (L + 1)) (L + 1, a) m)) := rfl

/-- With `maxSkip = 0` and no skipped keys, `receive` at chain position `R` accepts only index
`R + 1` and advances to `R + 1` on valid decryption. -/
theorem receive_chain (k : ChainKey) (R : ℕ) (a : AssocData) (i : ℕ) (e : Ciphertext) :
    (fromAEADPRG ae G 0).receive ⟨chainKeyAt G k R, R, []⟩ a (i, e) =
      if i = R + 1 then
        (ae.dec (messageKeyAt G k (R + 1)) (R + 1, a) e).map
          fun m => (⟨chainKeyAt G k (R + 1), R + 1, []⟩, R + 1, m)
      else none := by
  by_cases h : i = R + 1
  · subst h
    simp [fromAEADPRG, skipKeys, messageKeyAt, chainKeyAt]
  · simp only [fromAEADPRG, h]
    simp
    omega

theorem isCompromised_eq_false_iff {S R A M C : Type} (st : State S R A M C) (i : ℕ) :
    st.isCompromised i = false ↔ ∀ j, st.senderCorruptedAt = some j → i ≤ j := by
  unfold State.isCompromised
  split <;> simp_all

local notation "Ratchet" => fromAEADPRG ae G 0

local notation "GameState" => State (RatchetSenderState ChainKey)
  (RatchetReceiverState ChainKey MessageKey) AssocData Message (ℕ × Ciphertext)

/-- State invariant of the FS-AEAD game against `fromAEADPRG ae G 0` for shared key `k`. -/
structure Inv (k : ChainKey) (st : GameState) : Prop where
  /-- `A` is at chain position `lastSentIdx`. -/
  sender : st.senderState = ⟨chainKeyAt G k st.lastSentIdx, st.lastSentIdx⟩
  /-- `B` is at chain position `receiverIdx` with no skipped keys. -/
  receiver : st.receiverState = ⟨chainKeyAt G k st.receiverIdx, st.receiverIdx, []⟩
  /-- In-transit records were sent by `A`. -/
  inTransit_le : ∀ r ∈ st.inTransit, r.idx ≤ st.lastSentIdx
  /-- In-transit records are honest encryptions under the chain's message keys. -/
  inTransit_ct : ∀ r ∈ st.inTransit,
    r.ct = (r.idx, ae.enc (messageKeyAt G k r.idx) (r.idx, r.ad) r.msg)
  /-- `A` was corrupted at an index it had already reached. -/
  corruptedAt_le : ∀ j, st.senderCorruptedAt = some j → j ≤ st.lastSentIdx
  /-- Unless the adversary already won, uncompromised in-transit records are ahead of `B`. -/
  inTransit_ahead : st.win = false → ∀ r ∈ st.inTransit,
    (∀ j, st.senderCorruptedAt = some j → r.idx ≤ j) → st.receiverIdx < r.idx
  /-- While `win = false` and `A` is uncorrupted, `B` is not ahead of `A` (after `corruptSender`,
  injected ciphertexts may advance `B` past `lastSentIdx`). -/
  next_ahead : st.win = false → st.senderCorruptedAt = none → st.receiverIdx ≤ st.lastSentIdx

variable {ae G}

theorem initState_inv (k : ChainKey) (b : Bool) : Inv ae G k (initState Ratchet k b) := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [initState]

theorem transmit_inv {k : ChainKey} {st : GameState} (h : Inv ae G k st) (a : AssocData)
    (m : Message) : Inv ae G k (transmit Ratchet st a m).2 := by
  obtain ⟨hS, hR, hle, hct, hcorr, hahead, hnext⟩ := h
  unfold transmit
  split
  · exact ⟨hS, hR, hle, hct, hcorr, hahead, hnext⟩
  · simp only [hS, send_chain]
    refine ⟨rfl, hR, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.mem_cons, forall_eq_or_imp]
      exact ⟨le_rfl, fun r hr => Nat.le_succ_of_le (hle r hr)⟩
    · simp only [List.mem_cons, forall_eq_or_imp]
      exact ⟨trivial, hct⟩
    · exact fun j hj => Nat.le_succ_of_le (hcorr j hj)
    · simp only [List.mem_cons, forall_eq_or_imp]
      refine fun hw => ⟨fun hc => ?_, hahead hw⟩
      cases hcs : st.senderCorruptedAt with
      | none => have := hnext hw hcs; omega
      | some j => have := hcorr j hcs; have := hc j hcs; omega
    · exact fun hw hc => Nat.le_succ_of_le (hnext hw hc)

theorem challenge_inv {k : ChainKey} {st : GameState} (h : Inv ae G k st) (a : AssocData)
    (m₀ m₁ : Message) : Inv ae G k (challenge Ratchet st a m₀ m₁).2 := by
  obtain ⟨hS, hR, hle, hct, hcorr, hahead, hnext⟩ := h
  unfold challenge
  split
  · exact ⟨hS, hR, hle, hct, hcorr, hahead, hnext⟩
  · simp only [hS, send_chain]
    refine ⟨rfl, hR, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.mem_cons, forall_eq_or_imp]
      exact ⟨le_rfl, fun r hr => Nat.le_succ_of_le (hle r hr)⟩
    · simp only [List.mem_cons, forall_eq_or_imp]
      exact ⟨trivial, hct⟩
    · exact fun j hj => Nat.le_succ_of_le (hcorr j hj)
    · simp only [List.mem_cons, forall_eq_or_imp]
      refine fun hw => ⟨fun hc => ?_, hahead hw⟩
      cases hcs : st.senderCorruptedAt with
      | none => have := hnext hw hcs; omega
      | some j => have := hcorr j hcs; have := hc j hcs; omega
    · exact fun hw hc => Nat.le_succ_of_le (hnext hw hc)

theorem corruptSender_inv {k : ChainKey} {st : GameState} (h : Inv ae G k st) :
    Inv ae G k (corruptSender st).2 := by
  obtain ⟨hS, hR, hle, hct, hcorr, hahead, hnext⟩ := h
  unfold corruptSender
  split
  · exact ⟨hS, hR, hle, hct, hcorr, hahead, hnext⟩
  · refine ⟨hS, hR, hle, hct, ?_, ?_, ?_⟩
    · cases hcs : st.senderCorruptedAt with
      | none => simp
      | some j => simpa using hcorr j hcs
    · intro hw r hr hc
      cases hcs : st.senderCorruptedAt with
      | none => exact hahead hw r hr (by simp [hcs])
      | some j => exact hahead hw r hr (fun j' hj' => hc j' (by simp_all))
    · simp

theorem corruptReceiver_inv {k : ChainKey} {st : GameState} (h : Inv ae G k st) :
    Inv ae G k (corruptReceiver st).2 := by
  obtain ⟨hS, hR, hle, hct, hcorr, hahead, hnext⟩ := h
  unfold corruptReceiver
  split
  · exact ⟨hS, hR, hle, hct, hcorr, hahead, hnext⟩
  · exact ⟨hS, hR, hle, hct, hcorr, hahead, hnext⟩

theorem maxSkip_ratchet : (Ratchet).maxSkip = 0 := rfl

variable [DecidableEq AssocData] [DecidableEq Message] [DecidableEq Ciphertext]

theorem deliver_inv (hae : ae.Correct) {k : ChainKey} {st : GameState} (h : Inv ae G k st)
    (a : AssocData) (e : ℕ × Ciphertext) : Inv ae G k (deliver Ratchet st a e).2 := by
  obtain ⟨hS, hR, hle, hct, hcorr, hahead, hnext⟩ := h
  unfold deliver
  split
  · exact ⟨hS, hR, hle, hct, hcorr, hahead, hnext⟩
  split
  · exact ⟨hS, hR, hle, hct, hcorr, hahead, hnext⟩
  rename_i r hfind
  have hr : r ∈ st.inTransit := List.mem_of_find?_eq_some hfind
  have hre := List.find?_some hfind
  simp only [Bool.and_eq_true, beq_iff_eq] at hre
  obtain ⟨rfl, rfl⟩ := hre
  rw [hR, hct r hr, receive_chain]
  by_cases hi : r.idx = st.receiverIdx + 1
  · have hdec := hae (messageKeyAt G k (st.receiverIdx + 1)) (st.receiverIdx + 1, r.ad) r.msg
    have hmax : max st.receiverIdx (st.receiverIdx + 1) = st.receiverIdx + 1 := by omega
    simp only [hi, ↓reduceIte, hdec, Option.map_some, bne_self_eq_false, Bool.or_false,
      Bool.and_false, hmax, State.removeFromTransit]
    refine ⟨hS, rfl, ?_, ?_, hcorr, ?_, ?_⟩
    · simp only [List.mem_filter]
      exact fun r' hr' => hle r' hr'.1
    · simp only [List.mem_filter]
      exact fun r' hr' => hct r' hr'.1
    · simp only [List.mem_filter, bne_iff_ne, ne_eq]
      intro hw r' hr' hc
      have := hahead hw r' hr'.1 hc
      omega
    · intro _ _
      dsimp only
      have := hle r hr
      omega
  · simp only [hi, ↓reduceIte]
    refine ⟨hS, rfl, hle, hct, hcorr, ?_, ?_⟩
    · intro hw
      simp only [Bool.or_eq_false_iff] at hw
      exact hahead hw.1
    · intro hw
      simp only [Bool.or_eq_false_iff] at hw
      exact hnext hw.1

omit [DecidableEq Message] in
theorem inject_inv {k : ChainKey} {st : GameState} (h : Inv ae G k st) (a : AssocData)
    (e : ℕ × Ciphertext) : Inv ae G k (inject Ratchet st a e).2 := by
  obtain ⟨hS, hR, hle, hct, hcorr, hahead, hnext⟩ := h
  obtain ⟨i, c⟩ := e
  unfold inject
  split
  · exact ⟨hS, hR, hle, hct, hcorr, hahead, hnext⟩
  rw [hR, receive_chain]
  by_cases hi : i = st.receiverIdx + 1
  · subst hi
    simp only [↓reduceIte]
    cases hdec : ae.dec (messageKeyAt G k (st.receiverIdx + 1)) (st.receiverIdx + 1, a) c with
    | none =>
      simp only [Option.map_none]
      exact ⟨hS, hR, hle, hct, hcorr, hahead, hnext⟩
    | some m =>
      have hmax : max st.receiverIdx (st.receiverIdx + 1) = st.receiverIdx + 1 := by omega
      simp only [Option.map_some, hmax, State.removeFromTransit]
      refine ⟨hS, rfl, ?_, ?_, hcorr, ?_, ?_⟩
      · simp only [List.mem_filter]
        exact fun r' hr' => hle r' hr'.1
      · simp only [List.mem_filter]
        exact fun r' hr' => hct r' hr'.1
      · simp only [List.mem_filter, bne_iff_ne, ne_eq, Bool.or_eq_false_iff]
        intro hw r' hr' hc
        have := hahead hw.1 r' hr'.1 hc
        omega
      · intro hw hc
        dsimp only at hc hw
        simp [State.isCompromised, hc] at hw
  · simp only [hi, ↓reduceIte]
    exact ⟨hS, hR, hle, hct, hcorr, hahead, hnext⟩

/-- Under `Inv`, `deliver` leaves `win` unchanged: any uncompromised in-window record has index
`receiverIdx + 1` and decrypts to its original index and message. -/
theorem deliver_win_eq (hae : ae.Correct) {k : ChainKey} {st : GameState} (h : Inv ae G k st)
    (a : AssocData) (e : ℕ × Ciphertext) : (deliver Ratchet st a e).2.win = st.win := by
  obtain ⟨hS, hR, hle, hct, hcorr, hahead, hnext⟩ := h
  unfold deliver
  split
  · rfl
  split
  · rfl
  rename_i r hfind
  have hr : r ∈ st.inTransit := List.mem_of_find?_eq_some hfind
  have hre := List.find?_some hfind
  simp only [Bool.and_eq_true, beq_iff_eq] at hre
  obtain ⟨rfl, rfl⟩ := hre
  rw [hR, hct r hr, receive_chain]
  by_cases hi : r.idx = st.receiverIdx + 1
  · have hdec := hae (messageKeyAt G k (st.receiverIdx + 1)) (st.receiverIdx + 1, r.ad) r.msg
    simp [hi, hdec, State.removeFromTransit]
  · simp only [hi, ↓reduceIte]
    cases hw : st.win
    · rcases hc : st.isCompromised r.idx
      · have := hahead hw r hr ((isCompromised_eq_false_iff _ _).1 hc)
        simp [maxSkip_ratchet]
        omega
      · simp
    · rfl

/-- One-directional corollary of `deliver_win_eq`: if `win` holds after `deliver`, it already held
before. -/
theorem deliver_win_imp (hae : ae.Correct) {k : ChainKey} {st : GameState} (h : Inv ae G k st)
    (a : AssocData) (e : ℕ × Ciphertext) :
    (deliver Ratchet st a e).2.win = true → st.win = true := by
  rw [deliver_win_eq hae h]
  exact id

variable (ae G)

/-- Game states reachable from `initState` under shared key `k` via the six FS-AEAD oracle
transitions. -/
inductive Reachable (k : ChainKey) : GameState → Prop
  | init (b : Bool) : Reachable k (initState Ratchet k b)
  | ofTransmit {st} (a : AssocData) (m : Message) :
      Reachable k st → Reachable k (transmit Ratchet st a m).2
  | ofChallenge {st} (a : AssocData) (m₀ m₁ : Message) :
      Reachable k st → Reachable k (challenge Ratchet st a m₀ m₁).2
  | ofCorruptSender {st} : Reachable k st → Reachable k (corruptSender st).2
  | ofCorruptReceiver {st} : Reachable k st → Reachable k (corruptReceiver st).2
  | ofDeliver {st} (a : AssocData) (e : ℕ × Ciphertext) :
      Reachable k st → Reachable k (deliver Ratchet st a e).2
  | ofInject {st} (a : AssocData) (e : ℕ × Ciphertext) :
      Reachable k st → Reachable k (inject Ratchet st a e).2

variable {ae G}

theorem Reachable.inv (hae : ae.Correct) {k : ChainKey} {st : GameState}
    (h : Reachable ae G k st) : Inv ae G k st := by
  induction h with
  | init b => exact initState_inv k b
  | ofTransmit a m _ ih => exact transmit_inv ih a m
  | ofChallenge a m₀ m₁ _ ih => exact challenge_inv ih a m₀ m₁
  | ofCorruptSender _ ih => exact corruptSender_inv ih
  | ofCorruptReceiver _ ih => exact corruptReceiver_inv ih
  | ofDeliver a e _ ih => exact deliver_inv hae ih a e
  | ofInject a e _ ih => exact inject_inv ih a e

/-- In every reachable state, `deliver` leaves `win` unchanged, so `win` can only be set by
`inject`. -/
theorem Reachable.deliver_win_eq (hae : ae.Correct) {k : ChainKey} {st : GameState}
    (h : Reachable ae G k st) (a : AssocData) (e : ℕ × Ciphertext) :
    (deliver Ratchet st a e).2.win = st.win :=
  InOrder.deliver_win_eq hae (h.inv hae) a e

end CryptoGames.FSAEAD.InOrder
