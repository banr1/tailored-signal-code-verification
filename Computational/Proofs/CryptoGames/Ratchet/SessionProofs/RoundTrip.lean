/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.LibsignalWireRoundTrip

/-!
# Wire-codec round-trip bundle `RtHyp`

**Checked by Lean.** Bundles the wire-codec hypotheses (`SignalRoundTripShort`, `LengthsOk`, `SignalEncodeFits32`) into `RtHyp` and derives parsing and `< 2 ^ 32` wire-length lemmas for honest session messages.
-/

@[expose] public section

namespace CryptoGames.LibsignalSM.Proofs.RoundTrip

open LibsignalSession LibsignalAead CBC

/-- Wire-codec hypotheses of the refinement and correctness theorems. -/
structure RtHyp {PQ PQC : Type} (P : Params PQ PQC) (ℓ : ℕ) : Prop where
  /-- The codec round-trips short version-4 headers. -/
  rt : SignalRoundTripShort P.codec
  /-- The session's byte strings are short. -/
  len : LengthsOk P ℓ
  /-- Honest short wire messages encode with their 8-byte tag to fewer than `2 ^ 32` bytes (DEV-LS23). -/
  fits : SignalEncodeFits32 P.codec

theorem length_blockToBytesLE (b : Block) : (blockToBytesLE b).length = 16 := by
  simp [blockToBytesLE]

theorem length_flatMap_blockToBytesLE (cs : List Block) :
    (cs.flatMap blockToBytesLE).length = 16 * cs.length := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp [List.flatMap_cons, length_blockToBytesLE, ih]
    omega

theorem length_cbcBody {n : ℕ} (v : List.Vector Block n) :
    (v.toList.flatMap blockToBytesLE).length = 16 * n := by
  rw [length_flatMap_blockToBytesLE, v.toList_length]

theorem length_aesCbcEncrypt (E : AesKey → Block → Block) (key : AesKey) (iv : Block)
    (ptext : List (BitVec 8)) :
    (aesCbcEncrypt E key iv ptext).length = 16 * nBlocks ptext.length := by
  unfold aesCbcEncrypt
  exact length_cbcBody _

variable {PQ PQC : Type} {P : Params PQ PQC} {ℓ : ℕ}

theorem LengthsOk.body_lt32 (hL : LengthsOk P ℓ) : 16 * nBlocks ℓ < 2 ^ 31 + 16 := by
  have h := hL.1
  unfold nBlocks
  omega

theorem LengthsOk.body_lt (hL : LengthsOk P ℓ) : 16 * nBlocks ℓ < rustLenBound := by
  have h := LengthsOk.body_lt32 hL
  unfold rustLenBound
  omega

/-- A `pq_ratchet` field the session can send: empty or an output of `spqr.send`. -/
def SentPq (P : Params PQ PQC) (pq : List (BitVec 8)) : Prop :=
  pq = [] ∨ ∃ st rq st' salt, P.spqr.send st rq = some (st', salt, pq)

/-- An `addresses` field the session can send. -/
def SentAddrs (P : Params PQ PQC) (a : Option (List (BitVec 8))) : Prop :=
  a = none ∨ a = P.addrAB ∨ a = P.addrBA

theorem sentAddrs_send (P : Params PQ PQC) (b : Bool) (Q : Party) :
    SentAddrs P (if b then P.sendAddrs Q else none) := by
  cases b
  · exact Or.inl rfl
  · cases Q
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

theorem LengthsOk.pq_lt29 (hL : LengthsOk P ℓ) {pq : List (BitVec 8)} (hpq : SentPq P pq) :
    pq.length < 2 ^ 29 := by
  rcases hpq with hpq | ⟨st, rq, st', salt, hs⟩
  · rw [hpq]; decide
  · exact hL.2.1 st rq st' salt _ hs

theorem LengthsOk.addrs_lt29 (hL : LengthsOk P ℓ) {addrs : Option (List (BitVec 8))}
    (ha : SentAddrs P addrs) (a : List (BitVec 8)) (hav : addrs = some a) :
    a.length < 2 ^ 29 := by
  rcases ha with ha | ha | ha
  · rw [ha] at hav; cases hav
  · rw [ha] at hav; exact hL.2.2.1 a hav
  · rw [ha] at hav; exact hL.2.2.2 a hav

theorem LengthsOk.short (hL : LengthsOk P ℓ) {h : SignalHeader} {body : List (BitVec 8)}
    (hv : h.messageVersion = currentVersion) (hpq : SentPq P h.pqRatchet)
    (ha : SentAddrs P h.addresses) (hb : body.length = 16 * nBlocks ℓ) :
    SignalWireShort h body := by
  have h29 : 2 ^ 29 < rustLenBound := by unfold rustLenBound; decide
  refine ⟨hv, (LengthsOk.pq_lt29 hL hpq).trans h29, ?_, ?_⟩
  · intro a hav
    exact (LengthsOk.addrs_lt29 hL ha a hav).trans h29
  · rw [hb]; exact LengthsOk.body_lt hL

theorem parse_of_rt (hrt : SignalRoundTripShort P.codec) (hL : LengthsOk P ℓ) (h : SignalHeader)
    (body : List (BitVec 8))
    (hv : h.messageVersion = currentVersion) (hpq : SentPq P h.pqRatchet)
    (ha : SentAddrs P h.addresses) (hb : body.length = 16 * nBlocks ℓ) :
    (signalWireCodec P.codec).parse ((signalWireCodec P.codec).encode h body) = some (h, body) :=
  hrt h body (LengthsOk.short hL hv hpq ha hb)

/-- Every message built by the session round-trips through `signalWireCodec`. -/
theorem RtHyp.parse (hrt : RtHyp P ℓ) (h : SignalHeader) (body : List (BitVec 8))
    (hv : h.messageVersion = currentVersion) (hpq : SentPq P h.pqRatchet)
    (ha : SentAddrs P h.addresses) (hb : body.length = 16 * nBlocks ℓ) :
    (signalWireCodec P.codec).parse ((signalWireCodec P.codec).encode h body) = some (h, body) :=
  hrt.rt h body (LengthsOk.short hrt.len hv hpq ha hb)

/-- Every message built by the session encodes with its 8-byte tag in fewer than `2 ^ 32` bytes. -/
theorem RtHyp.encode_length_lt (hrt : RtHyp P ℓ) (h : SignalHeader) (body : List (BitVec 8))
    (hpq : SentPq P h.pqRatchet) (ha : SentAddrs P h.addresses) (hb : body.length = 16 * nBlocks ℓ) :
    ((signalWireCodec P.codec).encode h body).length + 8 < 2 ^ 32 :=
  hrt.fits h body (LengthsOk.pq_lt29 hrt.len hpq) (LengthsOk.addrs_lt29 hrt.len ha)
    (by rw [hb]; exact LengthsOk.body_lt32 hrt.len)

private theorem mexec_bind {σ α β : Type} (m : Mut σ α) (f : α → Mut σ β) (s : σ) :
    Mut.exec (m >>= f) s = match Mut.exec m s with
      | (.ok a, s') => Mut.exec (f a) s'
      | (.error e, s') => (.error e, s') := by
  unfold Mut.exec; simp only [Bind.bind, ExceptT.bind, ExceptT.mk,
    ExceptT.run, StateT.run, StateT.bind, ExceptT.bindCont]
  rcases m s with ⟨res, s'⟩; cases res <;> rfl

theorem RtHyp.encrypt_serialized_lt (hrt : RtHyp P ℓ) (ptext : List (BitVec 8))
    (hpt : ptext.length = ℓ) (addrs : Option (List (BitVec 8))) (ha : SentAddrs P addrs)
    (coins : PQC) (o o' : OutgoingTripleRatchet PQ) (msg : SignalMessage)
    (hex : Mut.exec (OutgoingTripleRatchet.encrypt P.C P.codec P.spqr ptext addrs coins) o =
      (.ok msg, o')) :
    msg.serialized.length < 2 ^ 32 := by
  unfold OutgoingTripleRatchet.encrypt at hex
  rw [mexec_bind] at hex
  have hg : Mut.exec (get : Mut (OutgoingTripleRatchet PQ) _) o = (.ok o, o) := rfl
  rw [hg] at hex
  try dsimp only at hex
  split at hex
  · cases hex
  · cases hsnd : P.spqr.send o.pqrState coins with
    | none => rw [hsnd] at hex; cases hex
    | some out =>
      rcases out with ⟨newPqr, pqrKey, pqrMsg⟩
      rw [hsnd] at hex
      try dsimp only at hex
      rw [mexec_bind] at hex
      cases hnk : o.senderChainKey.nextChainKey P.C.F with
      | error _ => rw [hnk] at hex; cases hex
      | ok nextCk =>
        rw [hnk] at hex
        have hl : Mut.exec (liftE (.ok nextCk) : Mut (OutgoingTripleRatchet PQ) ChainKey) o =
            (.ok nextCk, o) := rfl
        rw [hl] at hex
        try dsimp only at hex
        rw [mexec_bind] at hex
        have hs : ∀ (s' : OutgoingTripleRatchet PQ),
            Mut.exec (set s' : Mut (OutgoingTripleRatchet PQ) Unit) o = (.ok (), s') := fun _ => rfl
        rw [hs] at hex
        try dsimp only at hex
        rcases Prod.mk.inj hex with ⟨hm, _⟩
        cases hm
        let mks := (o.senderChainKey.messageKeys P.C.F).generateKeys P.C.F pqrKey
        let ctext := aesCbcEncrypt P.C.E mks.cipherKey mks.iv ptext
        let h : SignalHeader := ⟨o.sessionVersion, o.senderRatchetKey.publicKey,
          o.senderChainKey.index, o.previousCounter, pqrMsg, addrs⟩
        have hfit := hrt.fits h ctext (hrt.len.2.1 _ _ _ _ _ hsnd)
          (LengthsOk.addrs_lt29 hrt.len ha)
          (by rw [length_aesCbcEncrypt, hpt]; exact LengthsOk.body_lt32 hrt.len)
        have hmac : (computeMac P.C.F o.localIdentityKey o.remoteIdentityKey mks.macKey
            ((signalWireCodec P.codec).encode h ctext)).length ≤ 8 := by
          unfold computeMac
          exact List.length_take_le _ _
        change ((signalWireCodec P.codec).encode h ctext ++
          computeMac P.C.F o.localIdentityKey o.remoteIdentityKey mks.macKey
            ((signalWireCodec P.codec).encode h ctext)).length < 2 ^ 32
        rw [List.length_append]
        omega

theorem RtHyp.send_length_lt [Inhabited PQ] (hrt : RtHyp P ℓ) (g : GhostState PQ)
    (m : List (BitVec 8)) (hm : m.length = ℓ) (r : PQC) :
    (P.send g m r).2.length < 2 ^ 32 := by
  unfold Params.send
  rcases hme : SessionState.messageEncrypt P.C P.codec P.spqr (P.sendAddrs g.party) m r g.session
    with ⟨res, s⟩
  cases res with
  | error _ => simp
  | ok msg =>
    dsimp only
    unfold SessionState.messageEncrypt at hme
    split at hme
    · cases hme
    · split at hme
      · cases hme
      · rename_i hex
        cases hme
        exact hrt.encrypt_serialized_lt m hm _
          (by unfold SessionState.encryptAddresses; exact sentAddrs_send P _ _) r _ _ msg hex

end CryptoGames.LibsignalSM.Proofs.RoundTrip
