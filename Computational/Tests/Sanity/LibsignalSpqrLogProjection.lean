/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.LibsignalSpqrCorrect
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSMInstance
public import Computational.Proofs.CryptoGames.Ratchet.LibsignalSMInstanceProofDefs

/-!
# Session-Level Projection of the Ghost SPQR Log

**Checked by Lean.** Proves that `libsignalSessionScheme P.withSpqrLog` projects onto
`libsignalSessionScheme P` under `GhostState.mapPQ Prod.fst`: each `SMSchemeR` operation (`initA`,
`initB`, `send`, `receive`) produces identical wire outputs, epochs, indices, plaintexts, and
errors, and updates the non-log session state identically (`libSessionR_withSpqrLog_initA`,
`libSessionR_withSpqrLog_initB`, `libSessionR_withSpqrLog_send`, `libSessionR_withSpqrLog_receive`).
-/

@[expose] public section

namespace CryptoGames
namespace LibsignalSpqrLogProjection

open LibsignalSession LibsignalSM Ratchet.LibsignalInst CBC

variable {PQ PQC Pt : Type}

/-- Applies `f` to `pqRatchetState`, leaving all other `SessionState` fields unchanged. -/
def SessionState.mapPQ {PQ PQ' : Type} (f : PQ → PQ') (s : SessionState PQ) : SessionState PQ' :=
  ⟨s.sessionVersion, s.localIdentity, s.remoteIdentity, s.rootKey, s.previousCounter,
    s.senderChain, s.receiverChains, s.pendingPreKey, f s.pqRatchetState⟩

/-- Lifts `SessionState.mapPQ f` to `GhostState`, preserving `party`, `epoch`, and `chainEpochs`. -/
def GhostState.mapPQ {PQ PQ' : Type} (f : PQ → PQ') (g : GhostState PQ) : GhostState PQ' :=
  ⟨g.party, SessionState.mapPQ f g.session, g.epoch, g.chainEpochs⟩

theorem initializeInitiatorSession_withLog (C : Crypto) (S : Spqr PQ PQC)
    (ourIdentity theirIdentity : IdentityKey) (theirRatchetKey : PublicKey) (rootKey : RootKey)
    (chainKey pqrKey coins : BitVec 256) :
    (initializeInitiatorSession C S.withLog ourIdentity theirIdentity theirRatchetKey rootKey
        chainKey pqrKey coins).map (SessionState.mapPQ Prod.fst) =
      initializeInitiatorSession C S ourIdentity theirIdentity theirRatchetKey rootKey chainKey
        pqrKey coins := by
  simp only [initializeInitiatorSession]
  cases rootCreateChain C rootKey theirRatchetKey (KeyPair.generate C coins).privateKey <;> rfl

theorem initA_withSpqrLog (P : Params PQ PQC) (k : InitKeys) :
    GhostState.mapPQ Prod.fst (P.withSpqrLog.initA k) = P.initA k := by
  have h := initializeInitiatorSession_withLog P.C P.spqr P.idA P.idB
    (KeyPair.generate P.C k.bobSpkCoins).publicKey k.rootKey k.chainKey k.pqrKey
    k.aliceRatchetCoins
  simp only [Params.initA, Params.withSpqrLog]
  rw [← h]
  cases initializeInitiatorSession P.C P.spqr.withLog P.idA P.idB
    (KeyPair.generate P.C k.bobSpkCoins).publicKey k.rootKey k.chainKey k.pqrKey
    k.aliceRatchetCoins <;> rfl

theorem libSessionR_withSpqrLog_initA [Inhabited PQ] (P : Params PQ PQC) (ℓ : ℕ)
    (encPt : Pt → List (BitVec 8)) (lam : Pt) (k : RootKey × BitVec 256 × BitVec 256 × BitVec 256) :
    GhostState.mapPQ Prod.fst ((libsignalSessionScheme P.withSpqrLog ℓ encPt lam).initA k) =
      (libsignalSessionScheme P ℓ encPt lam).initA k :=
  initA_withSpqrLog P _

theorem libSessionR_withSpqrLog_initB [Inhabited PQ] (P : Params PQ PQC) (ℓ : ℕ)
    (encPt : Pt → List (BitVec 8)) (lam : Pt) (k : RootKey × BitVec 256 × BitVec 256 × BitVec 256) :
    GhostState.mapPQ Prod.fst ((libsignalSessionScheme P.withSpqrLog ℓ encPt lam).initB k) =
      (libsignalSessionScheme P ℓ encPt lam).initB k := rfl

def OutgoingTripleRatchet.mapPQ {PQ PQ' : Type} (f : PQ → PQ') (o : OutgoingTripleRatchet PQ) :
    OutgoingTripleRatchet PQ' :=
  ⟨o.senderRatchetKey, o.senderChainKey, o.previousCounter, f o.pqrState, o.sessionVersion,
    o.localIdentityKey, o.remoteIdentityKey⟩

private theorem exec_bind {σ α β : Type} (m : Mut σ α) (f : α → Mut σ β) (s : σ) :
    Mut.exec (m >>= f) s =
      match Mut.exec m s with
      | (.ok a, s') => Mut.exec (f a) s'
      | (.error e, s') => (.error e, s') := by
  unfold Mut.exec
  simp only [ExceptT.run_bind, StateT.run_bind]
  rcases (m.run).run s with ⟨r, s'⟩
  cases r <;> rfl

private theorem exec_pure {σ α : Type} (a : α) (s : σ) :
    Mut.exec (pure a : Mut σ α) s = (.ok a, s) := rfl

private theorem exec_throw {σ α : Type} (e : SignalProtocolError) (s : σ) :
    Mut.exec (throw e : Mut σ α) s = (.error e, s) := rfl

private theorem exec_liftE {σ α : Type} (r : Except SignalProtocolError α) (s : σ) :
    Mut.exec (liftE r : Mut σ α) s = (r, s) := by
  cases r <;> rfl

private theorem exec_get {σ : Type} (s : σ) : Mut.exec (get : Mut σ σ) s = (.ok s, s) := rfl

private theorem exec_set {σ : Type} (s' s : σ) : Mut.exec (set s' : Mut σ Unit) s = (.ok (), s') :=
  rfl

private theorem exec_take {PQ : Type} [Inhabited PQ] (s : SessionState PQ) :
    Mut.exec SessionState.takePqRatchetState s =
      (.ok s.pqRatchetState, { s with pqRatchetState := default }) := rfl

theorem fromSessionState_mapPQ [Inhabited PQ] (s : SessionState (PQ × SpqrLog)) :
    Mut.exec OutgoingTripleRatchet.fromSessionState (SessionState.mapPQ Prod.fst s) =
      ((Mut.exec OutgoingTripleRatchet.fromSessionState s).1.map
          (OutgoingTripleRatchet.mapPQ Prod.fst),
        SessionState.mapPQ Prod.fst (Mut.exec OutgoingTripleRatchet.fromSessionState s).2) := by
  unfold OutgoingTripleRatchet.fromSessionState SessionState.version
  simp only [exec_bind, exec_get]
  cases hsc : s.senderChain with
  | none => simp [SessionState.mapPQ, hsc, exec_throw, Except.map]
  | some sc =>
    simp only [SessionState.mapPQ, hsc, exec_bind, exec_get, exec_take]
    by_cases hv : 256 ≤ (if s.sessionVersion = 0 then (2 : BitVec 32) else s.sessionVersion).toNat
    · simp only [hv, ↓reduceIte]; rfl
    · simp only [hv, ↓reduceIte]
      cases s.remoteIdentity <;> rfl

theorem encrypt_mapPQ (C : Crypto) (codec : SignalMessageProtoCodec) (S : Spqr PQ PQC)
    (ptext : List (BitVec 8)) (addresses : Option (List (BitVec 8))) (coins : PQC)
    (o : OutgoingTripleRatchet (PQ × SpqrLog)) :
    Mut.exec (OutgoingTripleRatchet.encrypt C codec S ptext addresses coins)
        (OutgoingTripleRatchet.mapPQ Prod.fst o) =
      ((Mut.exec (OutgoingTripleRatchet.encrypt C codec S.withLog ptext addresses coins) o).1,
        OutgoingTripleRatchet.mapPQ Prod.fst
          (Mut.exec (OutgoingTripleRatchet.encrypt C codec S.withLog ptext addresses coins) o).2) := by
  unfold OutgoingTripleRatchet.encrypt
  simp only [exec_bind, exec_get]
  simp only [OutgoingTripleRatchet.mapPQ, Spqr.withLog]
  by_cases hp : S.sendPanics o.pqrState.1 coins = true
  · simp only [hp, ↓reduceIte]
    rfl
  simp only [hp]
  cases h : S.send o.pqrState.1 coins with
  | none => simp [exec_throw]
  | some x =>
    obtain ⟨st', salt, msg⟩ := x
    simp only [Option.map_some]
    cases o.senderChainKey.nextChainKey C.F <;> rfl

theorem messageEncrypt_mapPQ [Inhabited PQ] (C : Crypto) (codec : SignalMessageProtoCodec) (S : Spqr PQ PQC)
    (addresses : Option (List (BitVec 8))) (ptext : List (BitVec 8)) (coins : PQC)
    (s : SessionState (PQ × SpqrLog)) :
    SessionState.messageEncrypt C codec S addresses ptext coins (SessionState.mapPQ Prod.fst s) =
      ((SessionState.messageEncrypt C codec S.withLog addresses ptext coins s).1,
        SessionState.mapPQ Prod.fst
          (SessionState.messageEncrypt C codec S.withLog addresses ptext coins s).2) := by
  unfold SessionState.messageEncrypt
  rw [fromSessionState_mapPQ]
  rcases Mut.exec OutgoingTripleRatchet.fromSessionState s with ⟨r_out, s_out⟩
  cases r_out with
  | error e => rfl
  | ok o =>
    have ha : (SessionState.mapPQ Prod.fst s).encryptAddresses addresses =
        s.encryptAddresses addresses := rfl
    simp only [Except.map, ha]
    rw [encrypt_mapPQ]
    rcases Mut.exec (OutgoingTripleRatchet.encrypt C codec S.withLog ptext
      (s.encryptAddresses addresses) coins) o with ⟨r_enc, s_enc⟩
    cases r_enc <;> rfl

/-- `libsignalSessionScheme.send` under `P.withSpqrLog` projects via `GhostState.mapPQ Prod.fst` to
the unlogged `send` with identical wire output. -/
theorem libSessionR_withSpqrLog_send [Inhabited PQ] (P : Params PQ PQC) (ℓ : ℕ)
    (encPt : Pt → List (BitVec 8)) (lam : Pt) (g : GhostState (PQ × SpqrLog)) (m : Plain ℓ)
    (r : PQC) :
    (GhostState.mapPQ Prod.fst ((libsignalSessionScheme P.withSpqrLog ℓ encPt lam).send g m r).1,
        ((libsignalSessionScheme P.withSpqrLog ℓ encPt lam).send g m r).2) =
      (libsignalSessionScheme P ℓ encPt lam).send (GhostState.mapPQ Prod.fst g) m r := by
  simp only [libsignalSessionScheme, Params.send]
  have key : SessionState.messageEncrypt P.withSpqrLog.C P.withSpqrLog.codec P.withSpqrLog.spqr
      (P.withSpqrLog.sendAddrs g.party) m.toList r g.session =
      SessionState.messageEncrypt P.C P.codec P.spqr.withLog (P.sendAddrs g.party) m.toList r
        g.session := rfl
  have hs : (GhostState.mapPQ Prod.fst g).session = SessionState.mapPQ Prod.fst g.session := rfl
  have hp : (GhostState.mapPQ Prod.fst g).party = g.party := rfl
  rw [key, hs, hp, messageEncrypt_mapPQ]
  rcases SessionState.messageEncrypt P.C P.codec P.spqr.withLog (P.sendAddrs g.party) m.toList r
    g.session with ⟨r_enc, s_enc⟩
  cases r_enc <;> rfl

private def recv_TripleRatchet_mapPQ {PQ PQ' : Type} (f : PQ → PQ') (t : TripleRatchet PQ) :
    TripleRatchet PQ' :=
  ⟨t.ratchet, f t.pqrState, t.localIdentityKey, t.remoteIdentityKey⟩

private theorem recv_fromSessionState_withLog [Inhabited PQ] (s : SessionState (PQ × SpqrLog)) :
    Mut.exec TripleRatchet.fromSessionState (SessionState.mapPQ Prod.fst s) =
      ((Mut.exec TripleRatchet.fromSessionState s).1.map (recv_TripleRatchet_mapPQ Prod.fst),
        SessionState.mapPQ Prod.fst (Mut.exec TripleRatchet.fromSessionState s).2) := by
  cases s with
  | mk sv li ri rk pc sc rcs ppk pq =>
    cases ri <;> rfl

private theorem recv_exec_bind {σ α β : Type} (m : Mut σ α) (f : α → Mut σ β) (s : σ) :
    Mut.exec (m >>= f) s =
      match Mut.exec m s with
      | (.ok a, s') => Mut.exec (f a) s'
      | (.error e, s') => (.error e, s') := by
  unfold Mut.exec
  simp only [ExceptT.run_bind, StateT.run_bind]
  rcases (m.run).run s with ⟨r, s'⟩
  cases r <;> rfl

private theorem recv_exec_liftE {σ α : Type} (r : Except SignalProtocolError α) (s : σ) :
    Mut.exec (liftE r : Mut σ α) s = (r, s) := by
  cases r <;> rfl

private theorem recv_exec_get {σ : Type} (s : σ) : Mut.exec (get : Mut σ σ) s = (.ok s, s) := rfl

private theorem recv_exec_set {σ : Type} (s' s : σ) :
    Mut.exec (set s' : Mut σ Unit) s = (.ok (), s') := rfl

private theorem recv_exec_onRatchet {PQ' α : Type} (m : Mut RatchetState α) (t : TripleRatchet PQ') :
    Mut.exec (TripleRatchet.onRatchet m) t =
      ((Mut.exec m t.ratchet).1, { t with ratchet := (Mut.exec m t.ratchet).2 }) := by
  unfold TripleRatchet.onRatchet zoom
  simp only [recv_exec_bind, recv_exec_get]
  rcases Mut.exec m t.ratchet with ⟨r, rat'⟩
  simp only [recv_exec_set, recv_exec_liftE]

private theorem recv_decrypt_withLog (C : Crypto) (S : Spqr PQ PQC)
    (expected : Option (List (BitVec 8))) (ciphertext : SignalMessage) (msgType : MessageType)
    (coins : BitVec 256) (t : TripleRatchet (PQ × SpqrLog)) :
    Mut.exec (TripleRatchet.decrypt C S expected ciphertext msgType coins)
        (recv_TripleRatchet_mapPQ Prod.fst t) =
      ((Mut.exec (TripleRatchet.decrypt C S.withLog expected ciphertext msgType coins) t).1,
        recv_TripleRatchet_mapPQ Prod.fst
          (Mut.exec (TripleRatchet.decrypt C S.withLog expected ciphertext msgType coins) t).2) := by
  unfold TripleRatchet.decrypt
  have hrat : (recv_TripleRatchet_mapPQ Prod.fst t).ratchet = t.ratchet := rfl
  simp only [recv_exec_bind, recv_exec_onRatchet, hrat]
  rcases Mut.exec (RatchetState.ensureReceiverChain C ciphertext.senderRatchetKey coins) t.ratchet with ⟨r1, rat1⟩
  cases r1 with
  | error e => rfl
  | ok chainKey =>
    dsimp only
    rcases Mut.exec (RatchetState.consumeMessageKey C.F ciphertext.senderRatchetKey chainKey ciphertext.counter msgType) rat1 with ⟨r2, rat2⟩
    cases r2 with
    | error e => rfl
    | ok messageKeyGen =>
      dsimp only
      simp only [recv_exec_get, recv_TripleRatchet_mapPQ, Spqr.withLog]
      by_cases hp : S.recvPanics t.pqrState.1 ciphertext.pqRatchet = true
      · simp only [hp, ↓reduceIte]
        rfl
      simp only [hp]
      cases hrecv : S.recv t.pqrState.1 ciphertext.pqRatchet with
      | error b =>
        cases b <;> rfl
      | ok rp =>
        obtain ⟨newPqr1, pqrKey⟩ := rp
        simp only [Except.map, pure_bind]
        cases ciphertext.verifyMacWithAddresses C.F expected t.remoteIdentityKey t.localIdentityKey
          ((messageKeyGen.generateKeys C.F pqrKey).macKey)
        · rfl
        · cases aesCbcDecrypt C.D (messageKeyGen.generateKeys C.F pqrKey).cipherKey
            (messageKeyGen.generateKeys C.F pqrKey).iv ciphertext.ciphertext with
          | none => rfl
          | some ptext => rfl

private theorem recv_tryDecryptWithState_withLog [Inhabited PQ] (C : Crypto) (S : Spqr PQ PQC)
    (expected : Option (List (BitVec 8))) (ciphertext : SignalMessage) (msgType : MessageType)
    (coins : BitVec 256) (record : SessionState (PQ × SpqrLog)) :
    Mut.exec (SessionState.tryDecryptWithState C S expected ciphertext msgType coins)
        (SessionState.mapPQ Prod.fst record) =
      ((Mut.exec (SessionState.tryDecryptWithState C S.withLog expected ciphertext msgType coins) record).1,
        SessionState.mapPQ Prod.fst
          (Mut.exec (SessionState.tryDecryptWithState C S.withLog expected ciphertext msgType coins) record).2) := by
  unfold SessionState.tryDecryptWithState
  simp only [recv_exec_bind, recv_fromSessionState_withLog]
  rcases Mut.exec TripleRatchet.fromSessionState record with ⟨rfrom, s1⟩
  cases rfrom with
  | error e => rfl
  | ok session =>
    simp only [Except.map, recv_decrypt_withLog, recv_exec_liftE]
    rcases Mut.exec (TripleRatchet.decrypt C S.withLog expected ciphertext msgType coins) session with ⟨rdec, session'⟩
    cases rdec <;> rfl

private theorem recv_tryDecryptFromRecord_withLog [Inhabited PQ] (C : Crypto) (S : Spqr PQ PQC)
    (expected : Option (List (BitVec 8))) (ciphertext : SignalMessage) (msgType : MessageType)
    (coins : BitVec 256) (record : SessionState (PQ × SpqrLog)) :
    SessionState.tryDecryptFromRecord C S expected ciphertext msgType coins
        (SessionState.mapPQ Prod.fst record) =
      ((SessionState.tryDecryptFromRecord C S.withLog expected ciphertext msgType coins record).1,
        SessionState.mapPQ Prod.fst
          (SessionState.tryDecryptFromRecord C S.withLog expected ciphertext msgType coins record).2) := by
  unfold SessionState.tryDecryptFromRecord
  have hver : (SessionState.mapPQ Prod.fst record).version = record.version := rfl
  rw [hver]
  split
  · rfl
  · rw [recv_tryDecryptWithState_withLog C S expected ciphertext msgType coins record]
    cases Mut.exec (SessionState.tryDecryptWithState C S.withLog expected ciphertext msgType coins) record with
    | mk r updated =>
      cases r <;> rfl

private theorem recv_params_receive_withSpqrLog [Inhabited PQ] (P : Params PQ PQC)
    (g : GhostState (PQ × SpqrLog)) (c : List (BitVec 8)) (rc : BitVec 256) :
    (P.withSpqrLog.receive g c rc).map (fun x => (GhostState.mapPQ Prod.fst x.1, x.2)) =
      P.receive (GhostState.mapPQ Prod.fst g) c rc := by
  unfold Params.receive
  have hcodec : P.withSpqrLog.codec = P.codec := rfl
  rw [hcodec]
  cases SignalMessage.tryFrom P.codec c with
  | error _ => rfl
  | ok msg =>
    dsimp only
    have key : SessionState.tryDecryptFromRecord P.withSpqrLog.C P.withSpqrLog.spqr
        (P.withSpqrLog.expectedAddrs g.party) msg .whisper rc g.session =
        SessionState.tryDecryptFromRecord P.C P.spqr.withLog
          (P.expectedAddrs g.party) msg .whisper rc g.session := rfl
    have hparty : (GhostState.mapPQ Prod.fst g).party = g.party := rfl
    have hsess : (GhostState.mapPQ Prod.fst g).session = SessionState.mapPQ Prod.fst g.session := rfl
    rw [key, hparty, hsess,
      recv_tryDecryptFromRecord_withLog P.C P.spqr (P.expectedAddrs g.party) msg .whisper rc g.session]
    rcases SessionState.tryDecryptFromRecord P.C P.spqr.withLog (P.expectedAddrs g.party) msg .whisper rc g.session with ⟨r, s⟩
    cases r <;> rfl

/-- `libsignalSessionScheme.receive` under `P.withSpqrLog` projects via `GhostState.mapPQ Prod.fst`
to the unlogged `receive` with identical acceptance, epoch, index, and plaintext. -/
theorem libSessionR_withSpqrLog_receive [Inhabited PQ] (P : Params PQ PQC) (ℓ : ℕ)
    (encPt : Pt → List (BitVec 8)) (lam : Pt) (g : GhostState (PQ × SpqrLog))
    (c : List (BitVec 8)) (rc : BitVec 256) :
    ((libsignalSessionScheme P.withSpqrLog ℓ encPt lam).receive g c rc).map
        (fun x => (GhostState.mapPQ Prod.fst x.1, x.2)) =
      (libsignalSessionScheme P ℓ encPt lam).receive (GhostState.mapPQ Prod.fst g) c rc := by
  simp only [libsignalSessionScheme, ← recv_params_receive_withSpqrLog P g c rc, Option.map_map]
  rfl

end LibsignalSpqrLogProjection
end CryptoGames
