/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.PqStep
public import LibsignalBinary.Specifications.AsmConstants
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDecDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EffSalt
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EtMDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HKDFDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HMACDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.LibsignalAead
public import LibsignalBinary.Specifications.CryptoGames.AEAD.MacPrecompDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.WireAeadDefs
public import LibsignalBinary.Specifications.CryptoGames.CKA.DDHDefs
public import LibsignalBinary.Specifications.CryptoGames.CKA.Defs
public import LibsignalBinary.Specifications.CryptoGames.CKA.LibsignalCKA
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Construction
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Defs
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Hybrid
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.HybridWith
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.PubDefs
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Security
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.SecurityWith
public import LibsignalBinary.Specifications.CryptoGames.PRNG.Defs
public import LibsignalBinary.Specifications.CryptoGames.Party
public import LibsignalBinary.Specifications.CryptoGames.Primitives
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.ChainDefs
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.CreateChainDefs
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSMInstance
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSession
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApi
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionSM
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.RootKdfDefs
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.WireRatchetDefs
public import LibsignalBinary.Specifications.CryptoGames.SM.Construction
public import LibsignalBinary.Specifications.CryptoGames.SM.Game
public import LibsignalBinary.Specifications.CryptoGames.SM.LibsignalGame
public import LibsignalBinary.Specifications.HkdfSalt
public import LibsignalBinary.Specifications.LibsignalAesCbc
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhCorrectModel
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhInputs
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhModelLink
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhSessionModel
public import LibsignalBinary.Specifications.LibsignalE2E.SchemeModel
public import LibsignalBinary.Specifications.LibsignalE2E.State
public import LibsignalBinary.Specifications.LibsignalE2E.StateXModel
public import LibsignalBinary.Specifications.LibsignalHmac
public import LibsignalBinary.Specifications.LibsignalProtoCodec
public import LibsignalBinary.Specifications.LibsignalSession
public import LibsignalBinary.Specifications.LibsignalSessionRepr
public import LibsignalBinary.Specifications.LibsignalSignalMessage
public import LibsignalBinary.Specifications.LibsignalSpqr
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Assemble
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Auth
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Chain
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Core
public import LibsignalBinary.Specifications.LibsignalSpqrV1.GF16
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Init
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Interface
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Kdf
public import LibsignalBinary.Specifications.LibsignalSpqrV1.MlKem
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Model
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Poly
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Proto
public import LibsignalBinary.Specifications.LibsignalSpqrV1.ProtoPB
public import LibsignalBinary.Specifications.LibsignalSpqrV1.States
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Top
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire
public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import LibsignalBinary.Specifications.LibsignalTripleRatchetProst
public import LibsignalBinary.Specifications.LibsignalTripleRatchetRepr
public import LibsignalBinary.Specifications.RecordCodecs.Proto
public import LibsignalBinary.Specifications.RustHeap.Alloc
public import LibsignalBinary.Specifications.RustHeap.Vec
public import LibsignalBinary.Specifications.SignalPqxdh.Model
public import LibsignalBinary.Specifications.SignalSession.PqDir
public import LibsignalBinary.Specifications.SignalSession.Run
public import LibsignalBinary.Specifications.SignalSession.SmDir

/-!
# Pre-Key Promotion Closure (`reachPq_promote_proof`)

Proves that a successful `.preKey`-typed decryption (`tryDecryptFromRecord … .preKey`) on a
reachable PQXDH session (`ReachablePqxdhSession`) of encoded length `< 2^31` produces a session state
reachable via `ReachablePqxdhSession`: `MessageType` only tags `.invalidMessage` errors, so `.whisper`
decryption produces the same state and `ReachablePqxdhSession.recv` applies.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Closure.Promote

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec

private theorem exec_pure {σ α : Type} (a : α) (s : σ) :
    Mut.exec (pure a : Mut σ α) s = (.ok a, s) := rfl

private theorem exec_throw {σ α : Type} (e : SignalProtocolError) (s : σ) :
    Mut.exec (throw e : Mut σ α) s = (.error e, s) := rfl

private theorem exec_get {σ : Type} (s : σ) :
    Mut.exec (get : Mut σ σ) s = (.ok s, s) := rfl

private theorem exec_set {σ : Type} (s' s : σ) :
    Mut.exec (set s' : Mut σ Unit) s = (.ok (), s') := rfl

private theorem exec_modify {σ : Type} (f : σ → σ) (s : σ) :
    Mut.exec (modify f : Mut σ Unit) s = (.ok (), f s) := rfl

private theorem exec_modifyGet {σ α : Type} (f : σ → α × σ) (s : σ) :
    Mut.exec (modifyGet f : Mut σ α) s = (.ok (f s).1, (f s).2) := rfl

private theorem exec_liftE {σ α : Type} (r : Except SignalProtocolError α) (s : σ) :
    Mut.exec (liftE r : Mut σ α) s = (r, s) := by
  cases r <;> rfl

private theorem exec_bind {σ α β : Type} (m : Mut σ α) (k : α → Mut σ β) (s : σ) :
    Mut.exec (m >>= k) s =
      match Mut.exec m s with
      | (.ok a, s') => Mut.exec (k a) s'
      | (.error e, s') => (.error e, s') := by
  unfold Mut.exec
  simp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.run, ExceptT.bindCont, StateT.bind, StateT.run]
  rcases m s with ⟨r, s'⟩
  cases r <;> rfl

private theorem exec_onRatchet {PQ α : Type} (m : Mut RatchetState α) (t : TripleRatchet PQ) :
    Mut.exec (TripleRatchet.onRatchet m) t =
      let (r, s') := Mut.exec m t.ratchet
      (r, { t with ratchet := s' }) := by
  unfold TripleRatchet.onRatchet zoom
  simp only [exec_bind, exec_get, exec_set, exec_liftE]

private theorem consumeMessageKey_ok_msgType (F : ShaCompress) (their : PublicKey)
    (chainKey : ChainKey) (counter : BitVec 32) (msgType₁ msgType₂ : MessageType)
    (st st' : RatchetState) (mkg : MessageKeyGenerator)
    (h : Mut.exec (RatchetState.consumeMessageKey F their chainKey counter msgType₁) st =
      (.ok mkg, st')) :
    Mut.exec (RatchetState.consumeMessageKey F their chainKey counter msgType₂) st =
      (.ok mkg, st') := by
  unfold RatchetState.consumeMessageKey at h ⊢
  by_cases hlt : counter < chainKey.index
  · simp only [hlt, ↓reduceIte] at h ⊢
    exact h
  · simp only [hlt, ↓reduceIte, exec_bind, exec_get] at h ⊢
    by_cases hj : st.maxForwardJumps < (counter - chainKey.index).toNat
    · simp only [hj, ↓reduceIte, exec_bind, exec_throw] at h
      cases h
    · simp only [hj, ↓reduceIte, exec_bind, exec_pure] at h ⊢
      exact h

private theorem decrypt_ok_msgType {PQ PQC : Type} (C : Crypto) (spqr : Spqr PQ PQC)
    (expected : Option (List (BitVec 8))) (ciphertext : SignalMessage)
    (msgType₁ msgType₂ : MessageType) (coins : BitVec 256)
    (session session' : TripleRatchet PQ) (pt : List (BitVec 8))
    (h : Mut.exec (TripleRatchet.decrypt C spqr expected ciphertext msgType₁ coins) session =
      (.ok pt, session')) :
    Mut.exec (TripleRatchet.decrypt C spqr expected ciphertext msgType₂ coins) session =
      (.ok pt, session') := by
  unfold TripleRatchet.decrypt at h ⊢
  simp only [exec_bind, exec_onRatchet] at h ⊢
  rcases hens : Mut.exec (RatchetState.ensureReceiverChain C ciphertext.senderRatchetKey coins)
      session.ratchet with ⟨r1, rat1⟩
  rw [hens] at h
  cases r1 with
  | error e => cases h
  | ok chainKey =>
    dsimp only at h ⊢
    rcases hcmk : Mut.exec
        (RatchetState.consumeMessageKey C.F ciphertext.senderRatchetKey chainKey ciphertext.counter msgType₁)
        rat1 with ⟨r2, rat2⟩
    rw [hcmk] at h
    cases r2 with
    | error e => cases h
    | ok messageKeyGen =>
      have hcmk₂ := consumeMessageKey_ok_msgType C.F ciphertext.senderRatchetKey chainKey
        ciphertext.counter msgType₁ msgType₂ rat1 rat2 messageKeyGen hcmk
      rw [hcmk₂]
      dsimp only at h ⊢
      simp only [exec_get] at h ⊢
      cases hpan : spqr.recvPanics session.pqrState ciphertext.pqRatchet with
      | true =>
        rw [hpan] at h
        simp only [↓reduceIte, exec_bind, exec_throw] at h
        cases h
      | false =>
        rw [hpan] at h
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        cases hspqr : spqr.recv session.pqrState ciphertext.pqRatchet with
        | error b =>
          rw [hspqr] at h
          cases b <;> simp only [exec_bind, exec_throw] at h <;> cases h
        | ok rp =>
          rw [hspqr] at h
          rcases rp with ⟨newPqrState, pqrKey⟩
          simp only [exec_bind, exec_pure] at h ⊢
          cases hmac : ciphertext.verifyMacWithAddresses C.F expected session.remoteIdentityKey
              session.localIdentityKey (messageKeyGen.generateKeys C.F pqrKey).macKey with
          | false =>
            rw [hmac] at h
            simp only [Bool.not_false, ↓reduceIte, exec_bind, exec_throw] at h
            cases h
          | true =>
            rw [hmac] at h
            simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
            cases haes : aesCbcDecrypt C.D (messageKeyGen.generateKeys C.F pqrKey).cipherKey
                (messageKeyGen.generateKeys C.F pqrKey).iv ciphertext.ciphertext with
            | none =>
              rw [haes] at h
              simp only [exec_throw] at h
              cases h
            | some ptext =>
              rw [haes] at h
              exact h

private theorem tryDecryptWithState_ok_msgType {PQ PQC : Type} [Inhabited PQ]
    (C : Crypto) (spqr : Spqr PQ PQC) (expected : Option (List (BitVec 8)))
    (ciphertext : SignalMessage) (msgType₁ msgType₂ : MessageType) (coins : BitVec 256)
    (record updated : SessionState PQ) (pt : List (BitVec 8))
    (h : Mut.exec (SessionState.tryDecryptWithState C spqr expected ciphertext msgType₁ coins) record =
      (.ok pt, updated)) :
    Mut.exec (SessionState.tryDecryptWithState C spqr expected ciphertext msgType₂ coins) record =
      (.ok pt, updated) := by
  unfold SessionState.tryDecryptWithState at h ⊢
  simp only [exec_bind, exec_liftE] at h ⊢
  rcases hfrom : Mut.exec TripleRatchet.fromSessionState record with ⟨rf, session⟩
  rw [hfrom] at h
  cases rf with
  | error e => cases h
  | ok tr =>
    dsimp only at h ⊢
    rcases hdec : Mut.exec (TripleRatchet.decrypt C spqr expected ciphertext msgType₁ coins) tr
      with ⟨rd, tr'⟩
    rw [hdec] at h
    cases rd with
    | error e => cases h
    | ok ptext =>
      have hdec₂ := decrypt_ok_msgType C spqr expected ciphertext msgType₁ msgType₂ coins tr tr' ptext hdec
      rw [hdec₂]
      exact h

private theorem tryDecryptFromRecord_ok_msgType {PQ PQC : Type} [Inhabited PQ]
    (C : Crypto) (spqr : Spqr PQ PQC) (expected : Option (List (BitVec 8)))
    (ciphertext : SignalMessage) (msgType₁ msgType₂ : MessageType) (coins : BitVec 256)
    (record updated : SessionState PQ) (pt : List (BitVec 8))
    (h : SessionState.tryDecryptFromRecord C spqr expected ciphertext msgType₁ coins record =
      (.ok pt, updated)) :
    SessionState.tryDecryptFromRecord C spqr expected ciphertext msgType₂ coins record =
      (.ok pt, updated) := by
  unfold SessionState.tryDecryptFromRecord at h ⊢
  split at h
  · cases h
  · rename_i hver
    simp only [hver, ↓reduceIte]
    rcases hst : Mut.exec (SessionState.tryDecryptWithState C spqr expected ciphertext msgType₁ coins)
        record with ⟨r, upd⟩
    rw [hst] at h
    cases r with
    | error e => cases h
    | ok ptext =>
      cases h
      have hst₂ := tryDecryptWithState_ok_msgType C spqr expected ciphertext msgType₁ msgType₂
        coins record updated pt hst
      rw [hst₂]

theorem reachPq_promote_proof (W : PEParams) (me : LocalIdentity) (x : RecordExtras) (g : GhostState Bytes)
    (c : List (BitVec 8)) (msg : SignalMessage) (rc : BitVec 256) (pt : List (BitVec 8))
    (s : SessionState Bytes)
    (hR : ReachablePqxdhSession W me x g) (hlen : (encodeRecordUnderExtras (fun _ => x) g).length < 2 ^ 31)
    (hc : SignalMessage.tryFrom protoSignalCodec c = .ok msg)
    (hd : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W) ((pqxdhSessionParams W).expectedAddrs g.party)
      msg .preKey rc g.session = (.ok pt, s)) :
    ∃ g₁ : GhostState Bytes, ReachablePqxdhSession W me x g₁ ∧ g₁.party = g.party ∧ g₁.session = s := by
  have hd_whisper : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
      ((pqxdhSessionParams W).expectedAddrs g.party) msg .whisper rc g.session = (.ok pt, s) :=
    tryDecryptFromRecord_ok_msgType W.C (pqxdhSpqrSession W)
      ((pqxdhSessionParams W).expectedAddrs g.party) msg .preKey .whisper rc g.session s pt hd
  let idx := g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey)
  let trip := match idx with
    | some i => (g.chainEpochs.getD i 0, g.chainEpochs, g.epoch)
    | none => (g.epoch + 1, g.chainEpochs ++ [g.epoch + 1], g.epoch + 1)
  let epochs := trip.2.1.drop (trip.2.1.length - s.receiverChains.length)
  let g₁ : GhostState Bytes := { g with session := s, epoch := trip.2.2, chainEpochs := epochs }
  have hcodec : (pqxdhSessionParams W).codec = protoSignalCodec := rfl
  have hC : (pqxdhSessionParams W).C = W.C := rfl
  have hspqr : (pqxdhSessionParams W).spqr = pqxdhSpqrSession W := rfl
  have hrecv : (pqxdhSessionParams W).receive g c rc =
      some (g₁, trip.1, msg.counter.toNat + 1, pt) := by
    unfold Params.receive
    rw [hcodec, hc]
    dsimp only
    rw [hC, hspqr, hd_whisper]
    rfl
  exact ⟨g₁, ReachablePqxdhSession.recv hR hlen hrecv, rfl, rfl⟩

end CryptoVerification.SignalSession.Closure.Promote
