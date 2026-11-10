/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.LibsignalCli.Entry.CliPqReachSize
public import Computational.Proofs.SpqrV1Sync.TopStateTight
import LibsignalBinary.Proofs.SignalSession.PqClosure

/-!
# Session-record size cap and budget-free `PqStep` closure

Threads `TopStateTight` (`pqRatchetState.length ≤ 286,196`) through `ReachablePqxdhSession` to
bound every encoded session record by `1,209,331 < sessionCapBytes` (`2 ^ 21` bytes). Deduces
`PqxdhPartyInSpecDomain` closure across arbitrarily many `PqStep` transitions without a linear
state-growth budget.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalCli.Entry

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoGames.HKDF (Salt)
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec CryptoVerification.SignalSession
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1 spqrV1Init spqrV1Session)
open CryptoVerification.SpqrV1Sync.SendTotal (TopStateTight topStateTight_init
  topStateTight_send topStateTight_recv topStateTight_length_le)

/-- Session-record byte-size cap (`2 ^ 21` bytes), equal to `SignalSession.fileCapBytes`. -/
def sessionCapBytes : ℕ := fileCapBytes

private theorem r3_Mut_exec_bind {σ α β : Type} (m : Mut σ α) (f : α → Mut σ β) (s : σ) :
    Mut.exec (m >>= f) s =
      match Mut.exec m s with
      | (.ok a, s') => Mut.exec (f a) s'
      | (.error e, s') => (.error e, s') := by
  cases h : m s with
  | mk r s' =>
    cases r <;> (simp [Mut.exec, h, bind, ExceptT.bind, ExceptT.mk, StateT.bind, ExceptT.bindCont,
      StateT.run, ExceptT.run]; try rfl)

private theorem r3_Mut_exec_pure {σ α : Type} (a : α) (s : σ) :
    Mut.exec (pure a : Mut σ α) s = (.ok a, s) := rfl
private theorem r3_Mut_exec_throw {σ α : Type} (e : SignalProtocolError) (s : σ) :
    Mut.exec (throw e : Mut σ α) s = (.error e, s) := rfl
private theorem r3_Mut_exec_get {σ : Type} (s : σ) : Mut.exec (get : Mut σ σ) s = (.ok s, s) := rfl
private theorem r3_Mut_exec_set {σ : Type} (s' s : σ) :
    Mut.exec (set s' : Mut σ Unit) s = (.ok (), s') := rfl
private theorem r3_Mut_exec_modify {σ : Type} (f : σ → σ) (s : σ) :
    Mut.exec (modify f : Mut σ Unit) s = (.ok (), f s) := rfl
private theorem r3_Mut_exec_modifyGet {σ α : Type} (f : σ → α × σ) (s : σ) :
    Mut.exec (modifyGet f : Mut σ α) s = (.ok (f s).1, (f s).2) := rfl
private theorem r3_Mut_exec_liftE {σ α : Type} (r : Except SignalProtocolError α) (s : σ) :
    Mut.exec (liftE r : Mut σ α) s = (r, s) := by cases r <;> rfl

private theorem r3_onRatchet_pq {PQ α : Type} (m : Mut RatchetState α) (t t' : TripleRatchet PQ)
    (a : α) (h : Mut.exec (TripleRatchet.onRatchet m) t = (.ok a, t')) :
    t'.pqrState = t.pqrState := by
  unfold TripleRatchet.onRatchet zoom at h
  simp only [r3_Mut_exec_bind, r3_Mut_exec_get] at h
  rcases hm : Mut.exec m t.ratchet with ⟨_ | _, _⟩
  · simp [hm, r3_Mut_exec_set, r3_Mut_exec_liftE] at h
  · simp only [hm, r3_Mut_exec_set, r3_Mut_exec_liftE, Prod.mk.injEq, Except.ok.injEq] at h
    rcases h with ⟨rfl, rfl⟩; rfl

private theorem r3_messageEncrypt_spqr {PQ PQC : Type} [Inhabited PQ]
    (C : Crypto) (codec : SignalMessageProtoCodec) (spqr : Spqr PQ PQC) (addrs : Option Bytes)
    (ptext : Bytes) (coins : PQC) (record s : SessionState PQ) (msg : SignalMessage)
    (h : SessionState.messageEncrypt C codec spqr addrs ptext coins record = (.ok msg, s)) :
    ∃ salt pm, spqr.send record.pqRatchetState coins = some (s.pqRatchetState, salt, pm) := by
  unfold SessionState.messageEncrypt at h
  rcases hfrom : Mut.exec OutgoingTripleRatchet.fromSessionState record with ⟨_ | o, _⟩
  · rw [hfrom] at h; cases h
  · rw [hfrom] at h; dsimp only at h
    have hpq : o.pqrState = record.pqRatchetState := by
      revert hfrom; unfold OutgoingTripleRatchet.fromSessionState SessionState.takePqRatchetState
      rcases hsc : record.senderChain with _ | _
      · simp [r3_Mut_exec_bind, r3_Mut_exec_get, hsc, r3_Mut_exec_throw]
      · simp only [r3_Mut_exec_bind, r3_Mut_exec_get, hsc, r3_Mut_exec_modifyGet]
        split
        · simp [r3_Mut_exec_throw]
        · rcases record.remoteIdentity with _ | _
          · simp [r3_Mut_exec_throw]
          · simp only [r3_Mut_exec_pure, Prod.mk.injEq, Except.ok.injEq]
            rintro ⟨rfl, rfl⟩; rfl
    rcases henc : Mut.exec (OutgoingTripleRatchet.encrypt C codec spqr ptext
        (record.encryptAddresses addrs) coins) o with ⟨_ | _, _⟩
    · rw [henc] at h; cases h
    · rw [henc] at h; simp only [Prod.mk.injEq, Except.ok.injEq] at h; rcases h with ⟨rfl, rfl⟩
      unfold OutgoingTripleRatchet.encrypt at henc
      simp only [r3_Mut_exec_bind, r3_Mut_exec_get] at henc
      cases hpan : spqr.sendPanics o.pqrState coins
      · simp only [hpan, Bool.false_eq_true, ↓reduceIte] at henc
        rcases hspqr : spqr.send o.pqrState coins with _ | ⟨_, salt, pm⟩
        · simp [hspqr, r3_Mut_exec_throw] at henc
        · simp only [hspqr, r3_Mut_exec_bind] at henc
          rcases hn : o.senderChainKey.nextChainKey C.F with _ | _
          · simp [hn, r3_Mut_exec_liftE] at henc
          · simp only [hn, r3_Mut_exec_liftE, r3_Mut_exec_set, r3_Mut_exec_pure,
              Prod.mk.injEq] at henc
            rcases henc with ⟨-, rfl⟩
            exact ⟨salt, pm, by simpa [OutgoingTripleRatchet.applyToSessionState, hpq] using hspqr⟩
      · simp [hpan, r3_Mut_exec_throw] at henc

private theorem r3_tryDecryptFromRecord_spqr {PQ PQC : Type} [Inhabited PQ]
    (C : Crypto) (spqr : Spqr PQ PQC) (expected : Option Bytes) (m : SignalMessage)
    (msgType : MessageType) (coins : BitVec 256) (record s : SessionState PQ) (pt : Bytes)
    (h : SessionState.tryDecryptFromRecord C spqr expected m msgType coins record = (.ok pt, s)) :
    ∃ salt, spqr.recv record.pqRatchetState m.pqRatchet = .ok (s.pqRatchetState, salt) := by
  unfold SessionState.tryDecryptFromRecord at h; split_ifs at h
  · cases h
  · rcases hd : Mut.exec (SessionState.tryDecryptWithState C spqr expected m msgType coins) record with
      ⟨_ | _, _⟩
    · rw [hd] at h; cases h
    · rw [hd] at h; simp only [Prod.mk.injEq, Except.ok.injEq] at h; rcases h with ⟨rfl, rfl⟩
      unfold SessionState.tryDecryptWithState TripleRatchet.fromSessionState
        SessionState.takeRatchetState SessionState.takePqRatchetState at hd
      simp only [r3_Mut_exec_bind, r3_Mut_exec_get, r3_Mut_exec_modifyGet] at hd
      rcases hrem : record.remoteIdentity with _ | rem
      · simp [hrem, r3_Mut_exec_throw] at hd
      · simp only [hrem, r3_Mut_exec_pure] at hd
        set tr0 : TripleRatchet PQ := ⟨⟨record.rootKey, record.senderChain, record.receiverChains,
          record.previousCounter, maxForwardJumps⟩, record.pqRatchetState, record.localIdentity, rem⟩
        rcases hdec : Mut.exec (TripleRatchet.decrypt C spqr expected m msgType coins) tr0 with
          ⟨_ | _, _⟩
        · simp [hdec, r3_Mut_exec_liftE] at hd
        · simp only [hdec, r3_Mut_exec_liftE, r3_Mut_exec_modify, Prod.mk.injEq] at hd
          rcases hd with ⟨-, rfl⟩; unfold TripleRatchet.decrypt at hdec
          simp only [r3_Mut_exec_bind] at hdec
          rcases hens : Mut.exec (TripleRatchet.onRatchet
              (RatchetState.ensureReceiverChain C m.senderRatchetKey coins)) tr0 with ⟨_ | ck, tr1⟩
          · rw [hens] at hdec; cases hdec
          · rw [hens] at hdec; dsimp only at hdec
            have hpq1 := r3_onRatchet_pq _ tr0 tr1 ck hens
            rcases hcons : Mut.exec (TripleRatchet.onRatchet
                (RatchetState.consumeMessageKey C.F m.senderRatchetKey ck m.counter msgType)) tr1 with
              ⟨_ | mkg, tr2⟩
            · rw [hcons] at hdec; cases hdec
            · rw [hcons] at hdec; dsimp only at hdec
              have hpq2 := r3_onRatchet_pq _ tr1 tr2 mkg hcons
              simp only [r3_Mut_exec_get] at hdec
              cases hpan : spqr.recvPanics tr2.pqrState m.pqRatchet
              · simp only [hpan, Bool.false_eq_true, ↓reduceIte] at hdec
                rcases hspqr : spqr.recv tr2.pqrState m.pqRatchet with err | ⟨_, salt⟩
                · cases err <;> simp [hspqr, r3_Mut_exec_throw] at hdec
                · simp only [hspqr, r3_Mut_exec_bind, r3_Mut_exec_pure] at hdec; split_ifs at hdec
                  · simp [r3_Mut_exec_throw] at hdec
                  · rcases haes : aesCbcDecrypt C.D (mkg.generateKeys C.F salt).cipherKey
                        (mkg.generateKeys C.F salt).iv m.ciphertext with _ | _
                    · simp [haes, r3_Mut_exec_throw] at hdec
                    · simp only [haes, r3_Mut_exec_bind, r3_Mut_exec_modify, r3_Mut_exec_pure,
                        Prod.mk.injEq] at hdec
                      rcases hdec with ⟨-, rfl⟩
                      exact ⟨salt, by simpa [TripleRatchet.applyToSessionState,
                        SessionState.clearUnacknowledgedPreKeyMessage, hpq2, hpq1, tr0] using hspqr⟩
              · simp [hpan, r3_Mut_exec_throw] at hdec

/-! ## Tight state and record-size bounds -/

/-- Every reachable PQXDH session has a `TopStateTight` SPQR-V1 state. -/
theorem reachPq_topStateTight {W : PEParams} {me : LocalIdentity} {x : RecordExtras}
    {g : GhostState Bytes} (hR : ReachablePqxdhSession W me x g) :
    TopStateTight W.C.F W.Q.K g.session.pqRatchetState := by
  induction hR with
  | initiate X' _ me' b t _ _ hi =>
    unfold initiateState at hi
    rcases hinit : SignalPqxdh.Model.initiateKeys (modelPrims X' W) (initiateInput W me' b t) with
      _ | ⟨dk, _⟩
    · simp [hinit] at hi
    · rw [hinit] at hi; dsimp only at hi; unfold initializeInitiatorSession at hi
      dsimp only [bind, Except.bind, pure, Except.pure] at hi
      rcases hrc : rootCreateChain W.C (HKDF.bytesToKey32 (ofU8 dk.rootKey)) ⟨b.spkPub⟩
          (KeyPair.generate W.C (HKDF.bytesToKey32 ((t.toList.drop 160).take 32))).privateKey with
        _ | ⟨_, _⟩
      · simp [hrc] at hi
      · rw [hrc] at hi; simp only [Option.some.injEq, Prod.mk.injEq] at hi
        rcases hi with ⟨rfl, rfl⟩
        exact topStateTight_init W.C.F W.Q.K .a2b _
  | recvPrekey X' P me' k m rc _ _ _ hr =>
    unfold recvPrekeyState at hr
    rcases htf : SignalMessage.tryFrom protoSignalCodec m.inner with _ | inner
    · simp [htf] at hr
    · rw [htf] at hr; dsimp only at hr
      by_cases hids : m.spkId ≠ k.spkId ∨ m.kpkId ≠ k.kpkId
      · simp only [hids, ↓reduceIte] at hr; cases hr
      · simp only [hids, ↓reduceIte] at hr
        rcases hacc : SignalPqxdh.Model.acceptKeys (modelPrims X' W) (acceptInput W me' k m) with
          _ | dk
        · simp [hacc] at hr
        · rw [hacc] at hr; dsimp only at hr
          set st0 : SessionState Bytes :=
            initializeRecipientSession (pqxdhSpqrSession W) ⟨(keyPairOf W.C me'.idPriv).publicKey⟩
              ⟨⟨m.idPub⟩⟩ (keyPairOf W.C k.spkPriv) (HKDF.bytesToKey32 (ofU8 dk.rootKey))
              (HKDF.bytesToKey32 (ofU8 dk.chainKey)) (HKDF.bytesToKey32 (ofU8 dk.pqrKey))
          rcases hd : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
              ((pqxdhSessionParams W).expectedAddrs P) inner .preKey rc st0 with ⟨err | pt', st⟩
          · rw [hd] at hr; cases err <;> cases hr
          · rw [hd] at hr; simp only [Option.some.injEq, Prod.mk.injEq] at hr
            rcases hr with ⟨rfl, rfl, rfl⟩
            obtain ⟨salt, hspqr⟩ := r3_tryDecryptFromRecord_spqr W.C (pqxdhSpqrSession W)
              ((pqxdhSessionParams W).expectedAddrs P) inner .preKey rc st0 st pt' hd
            have h0 : TopStateTight W.C.F W.Q.K st0.pqRatchetState :=
              topStateTight_init W.C.F W.Q.K .b2a _
            exact topStateTight_recv W.C.F W.Q.K h0 hspqr
  | @send _ _ g_s m r _ _ ih =>
    unfold Params.send
    rcases hm : SessionState.messageEncrypt (pqxdhSessionParams W).C (pqxdhSessionParams W).codec
        (pqxdhSessionParams W).spqr ((pqxdhSessionParams W).sendAddrs g_s.party) m r g_s.session with
      ⟨_ | msg, s⟩
    · exact ih
    · dsimp only
      obtain ⟨salt, pm, hspqr⟩ := r3_messageEncrypt_spqr (pqxdhSessionParams W).C
        (pqxdhSessionParams W).codec (pqxdhSessionParams W).spqr
        ((pqxdhSessionParams W).sendAddrs g_s.party) m r g_s.session s msg hm
      exact topStateTight_send W.C.F W.Q.K ih hspqr
  | @recv _ _ g_r _ c rc _ _ _ hrec ih =>
    unfold Params.receive at hrec
    rcases htf : SignalMessage.tryFrom (pqxdhSessionParams W).codec c with _ | msg
    · simp [htf] at hrec
    · rw [htf] at hrec; dsimp only at hrec
      rcases hd : SessionState.tryDecryptFromRecord (pqxdhSessionParams W).C
          (pqxdhSessionParams W).spqr ((pqxdhSessionParams W).expectedAddrs g_r.party) msg .whisper
          rc g_r.session with ⟨_ | pt, s⟩
      · simp [hd] at hrec
      · rw [hd] at hrec; simp only [Option.some.injEq, Prod.mk.injEq] at hrec
        rcases hrec with ⟨rfl, -⟩
        obtain ⟨salt, hspqr⟩ := r3_tryDecryptFromRecord_spqr (pqxdhSessionParams W).C
          (pqxdhSessionParams W).spqr ((pqxdhSessionParams W).expectedAddrs g_r.party) msg .whisper
          rc g_r.session s pt hd
        exact topStateTight_recv W.C.F W.Q.K ih hspqr

theorem reachPq_pqLength_le_286196 {W : PEParams} {me : LocalIdentity} {x : RecordExtras}
    {g : GhostState Bytes} (hR : ReachablePqxdhSession W me x g) :
    g.session.pqRatchetState.length ≤ 286196 :=
  topStateTight_length_le W.C.F W.Q.K (reachPq_topStateTight hR)

theorem pqLength_le_286196_of_wfPq {W : PEParams} {d0 : PqParty} {x : RecordExtras}
    {g : GhostState Bytes} (hwf : PqxdhPartyInSpecDomain W { d0 with session := some (x, g) }) :
    g.session.pqRatchetState.length ≤ 286196 := by
  obtain ⟨⟨g₀, hR₀, -, hs₀⟩, -, -⟩ := hwf.1 x g rfl
  rw [← hs₀]
  exact reachPq_pqLength_le_286196 hR₀

/-- Every reachable PQXDH session record encodes to at most `1,209,331` bytes. -/
theorem encodeRecordX_length_le_1209331_cli {W : PEParams} {me : LocalIdentity}
    {x : RecordExtras} {g : GhostState Bytes} (hR : ReachablePqxdhSession W me x g) :
    (encodeRecordUnderExtras (fun _ => x) g).length ≤ 1209331 := by
  have hdr := encodeRecordX_length_le_pq_add_923135_cli hR
  have hpq := reachPq_pqLength_le_286196 hR
  omega

/-- Every reachable PQXDH session record encodes to strictly fewer than `sessionCapBytes`. -/
theorem encodeRecordX_length_lt_sessionCap_cli {W : PEParams} {me : LocalIdentity}
    {x : RecordExtras} {g : GhostState Bytes} (hR : ReachablePqxdhSession W me x g) :
    (encodeRecordUnderExtras (fun _ => x) g).length < sessionCapBytes := by
  have h := encodeRecordX_length_le_1209331_cli hR
  unfold sessionCapBytes fileCapBytes
  omega

/-! ## Spec-domain closure across `PqStep` -/

private theorem r3_removeOpk_me (st : PqParty) (m : PreKeyMessageFields) :
    (removeOpk st m).me = st.me := by
  unfold removeOpk; cases m.opkId <;> rfl

private theorem r3_markKyberUsed_me {st st1 : PqParty} {m : PreKeyMessageFields}
    (h : markKyberUsed st m = some st1) : st1.me = st.me := by
  unfold markKyberUsed at h
  split at h
  · injection h with h'; subst h'; rfl
  · split at h <;> [cases h; (split at h <;> [cases h; (injection h with h'; subst h'; rfl)])]

private theorem r3_encodeRecordX_eq_of_session_eq (x : RecordExtras) (g₁ g₂ : GhostState Bytes)
    (hs : g₁.session = g₂.session) :
    encodeRecordUnderExtras (fun _ => x) g₁ = encodeRecordUnderExtras (fun _ => x) g₂ := by
  unfold encodeRecordUnderExtras; rw [hs]

private theorem pqStep_session_reach {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {st st' : PqParty} {x' : RecordExtras} {g' : GhostState Bytes}
    (hwf : PqxdhPartyInSpecDomain W st) (hstep : PqStep X W st st')
    (hs' : st'.session = some (x', g')) :
    ∃ g₀' : GhostState Bytes,
      ReachablePqxdhSession W st'.me x' g₀' ∧ g₀'.party = g'.party ∧ g₀'.session = g'.session := by
  cases hstep with
  | init b t _ out _ hinit =>
    unfold pqInitModel at hinit
    cases ht : st.trusts ⟨⟨b.idPub⟩⟩
    · rw [ht] at hinit; cases hinit
    · rw [ht] at hinit; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hinit
      rcases hi : initiateState X W st.party st.me b t with _ | ⟨x, g⟩
      · rw [hi] at hinit; cases hinit
      · rw [hi] at hinit; simp only [Option.some.injEq, Prod.mk.injEq] at hinit
        rcases hinit with ⟨rfl, -⟩; simp only [Option.some.injEq, Prod.mk.injEq] at hs'
        rcases hs' with ⟨hx', hg'⟩; rw [← hx', ← hg']
        exact ⟨g, ReachablePqxdhSession.initiate X st.party st.me b t x g hi, rfl, rfl⟩
  | send m r _ out _ hsend =>
    unfold pqSendModel at hsend
    rcases hsess : st.session with _ | ⟨x, g⟩
    · rw [hsess] at hsend; cases hsend
    · rw [hsess] at hsend; dsimp only at hsend
      rcases henc : SessionState.messageEncrypt W.C protoSignalCodec (pqxdhSpqrSession W)
          ((pqxdhSessionParams W).sendAddrs g.party) m r.toList g.session with ⟨err | _, s⟩
      · rw [henc] at hsend; cases err <;> cases hsend
      · rw [henc] at hsend; dsimp only at hsend
        rcases hk : g.session.remoteIdentity with _ | k
        · rw [hk] at hsend; cases hsend
        · rw [hk] at hsend; dsimp only at hsend
          cases ht : st.trusts k
          · rw [ht] at hsend; cases hsend
          · rw [ht] at hsend
            simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
              Option.some.injEq, Prod.mk.injEq] at hsend
            rcases hsend with ⟨rfl, -⟩; simp only [Option.some.injEq, Prod.mk.injEq] at hs'
            rcases hs' with ⟨hx', hg'⟩; rw [← hx', ← hg']
            obtain ⟨⟨g₀, hR₀, hp₀, hs₀⟩, -, hlen⟩ := hwf.1 x g hsess
            have hlen₀ : (encodeRecordUnderExtras (fun _ => x) g₀).length < 2 ^ 31 := by
              rw [r3_encodeRecordX_eq_of_session_eq x g₀ g hs₀]; exact hlen
            refine ⟨((pqxdhSessionParams W).send g₀ m r.toList).1,
              ReachablePqxdhSession.send m r.toList hR₀ hlen₀, ?_⟩
            unfold Params.send
            have hC : (pqxdhSessionParams W).C = W.C := rfl
            have hcodec : (pqxdhSessionParams W).codec = protoSignalCodec := rfl
            have hspqr' : (pqxdhSessionParams W).spqr = pqxdhSpqrSession W := rfl
            rw [hC, hcodec, hspqr', hp₀, hs₀, henc]; exact ⟨rfl, rfl⟩
  | recvWhisper c rc _ out _ hrecv =>
    unfold pqRecvWhisperModel at hrecv
    rcases hsess : st.session with _ | ⟨x, g⟩
    · rw [hsess] at hrecv; cases hrecv
    · rw [hsess] at hrecv; dsimp only at hrecv
      rcases htry : SignalMessage.tryFrom protoSignalCodec c with _ | msg
      · rw [htry] at hrecv; cases hrecv
      · rw [htry] at hrecv; dsimp only [pqxdhSessionDecryptModel] at hrecv
        rcases hdec : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
            ((pqxdhSessionParams W).expectedAddrs g.party) msg .whisper rc g.session with ⟨err | _, s⟩
        · rw [hdec] at hrecv; cases err <;> cases hrecv
        · rw [hdec] at hrecv; dsimp only at hrecv
          rcases hk : s.remoteIdentity with _ | k
          · rw [hk] at hrecv; cases hrecv
          · rw [hk] at hrecv; dsimp only at hrecv
            cases ht : st.trusts k
            · rw [ht] at hrecv; cases hrecv
            · rw [ht] at hrecv
              simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                Option.some.injEq, Prod.mk.injEq] at hrecv
              rcases hrecv with ⟨rfl, -⟩; simp only [Option.some.injEq, Prod.mk.injEq] at hs'
              rcases hs' with ⟨hx', hg'⟩; rw [← hx', ← hg']
              obtain ⟨⟨g₀, hR₀, hp₀, hs₀⟩, -, hlen⟩ := hwf.1 x g hsess
              have hlen₀ : (encodeRecordUnderExtras (fun _ => x) g₀).length < 2 ^ 31 := by
                rw [r3_encodeRecordX_eq_of_session_eq x g₀ g hs₀]; exact hlen
              have hrec₀ : ∃ g₁ res, (pqxdhSessionParams W).receive g₀ c rc = some (g₁, res) ∧
                  g₁.party = g.party ∧ g₁.session = s := by
                unfold Params.receive
                have hC : (pqxdhSessionParams W).C = W.C := rfl
                have hcodec : (pqxdhSessionParams W).codec = protoSignalCodec := rfl
                have hspqr' : (pqxdhSessionParams W).spqr = pqxdhSpqrSession W := rfl
                rw [hcodec, htry, hC, hspqr', hp₀, hs₀]; dsimp only; rw [hdec]
                exact ⟨_, _, rfl, rfl, rfl⟩
              rcases hrec₀ with ⟨g₁, res, hrec₁, hp₁, hs₁⟩
              exact ⟨g₁, ReachablePqxdhSession.recv hR₀ hlen₀ hrec₁, hp₁, hs₁⟩
  | recvPrekey m rc _ out _ _ hrecv =>
    unfold pqRecvPrekeyModel at hrecv
    rcases htry : SignalMessage.tryFrom protoSignalCodec m.inner with _ | inner
    · rw [htry] at hrecv; cases hrecv
    · rw [htry] at hrecv; dsimp only at hrecv
      cases ht : st.trusts ⟨⟨m.idPub⟩⟩
      · rw [ht] at hrecv; cases hrecv
      · rw [ht] at hrecv; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hrecv
        rcases hsess : st.session with _ | ⟨x, g⟩
        · rw [hsess] at hrecv; dsimp only at hrecv
          rcases hk : preKeysNamedBy st m with _ | k
          · rw [hk] at hrecv; cases hrecv
          · rw [hk] at hrecv; dsimp only at hrecv
            rcases hrp : recvPrekeyState X W st.party st.me k m rc with _ | _ | ⟨x1, g1, pt⟩
            · rw [hrp] at hrecv; cases hrecv
            · rw [hrp] at hrecv; cases hrecv
            · rw [hrp] at hrecv; dsimp only at hrecv
              rcases hmk : markKyberUsed st m with _ | st1
              · rw [hmk] at hrecv; cases hrecv
              · rw [hmk] at hrecv; simp only [Option.some.injEq, Prod.mk.injEq] at hrecv
                rcases hrecv with ⟨rfl, -⟩; simp only [Option.some.injEq, Prod.mk.injEq] at hs'
                rcases hs' with ⟨hx', hg'⟩; rw [← hx', ← hg']
                have hme : (removeOpk st1 m).me = st.me :=
                  (r3_removeOpk_me st1 m).trans (r3_markKyberUsed_me hmk)
                dsimp only; rw [hme]
                exact ⟨g1, ReachablePqxdhSession.recvPrekey X st.party st.me k m rc x1 g1 pt hrp,
                  rfl, rfl⟩
        · rw [hsess] at hrecv; dsimp only at hrecv
          by_cases hm_match : PqSessionMatches x g m
          · simp only [hm_match, ↓reduceIte] at hrecv
            split_ifs at hrecv
            · cases hrecv
            · rcases hdec : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
                  ((pqxdhSessionParams W).expectedAddrs g.party) inner .preKey rc g.session with
                ⟨err | pt, s⟩
              · rw [hdec] at hrecv; cases err <;> cases hrecv
              · rw [hdec] at hrecv; simp only [Option.some.injEq, Prod.mk.injEq] at hrecv
                rcases hrecv with ⟨rfl, -⟩; simp only [Option.some.injEq, Prod.mk.injEq] at hs'
                rcases hs' with ⟨hx', hg'⟩; rw [← hx', ← hg']
                obtain ⟨⟨g₀, hR₀, hp₀, hs₀⟩, -, hlen⟩ := hwf.1 x g hsess
                have hlen₀ : (encodeRecordUnderExtras (fun _ => x) g₀).length < 2 ^ 31 := by
                  rw [r3_encodeRecordX_eq_of_session_eq x g₀ g hs₀]; exact hlen
                have hdec₀ : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
                    ((pqxdhSessionParams W).expectedAddrs g₀.party) inner .preKey rc g₀.session =
                    (.ok pt, s) := by rw [hp₀, hs₀]; exact hdec
                obtain ⟨g₁, hR₁, hp₁, hs₁⟩ :=
                  reachPq_promote W st.me x g₀ m.inner inner rc pt s hR₀ hlen₀ htry hdec₀
                exact ⟨g₁, hR₁, hp₁.trans hp₀, hs₁⟩
          · simp only [hm_match, ↓reduceIte] at hrecv; cases hrecv

/-- One-step `PqxdhPartyInSpecDomain` and `< sessionCapBytes` record-size closure across any
accepted `PqStep`. -/
theorem wfPq_step_r3 {X : UnreachedPqxdhPrimitives} {W : PEParams} {st st' : PqParty}
    (hwf : PqxdhPartyInSpecDomain W st) (hstep : PqStep X W st st')
    (hlr : lastResortUses st' < 2 ^ 25) :
    PqxdhPartyInSpecDomain W st' ∧
      ∀ x' g', st'.session = some (x', g') →
        (encodeRecordUnderExtras (fun _ => x') g').length < sessionCapBytes := by
  have hcap : ∀ x' g', st'.session = some (x', g') →
      (encodeRecordUnderExtras (fun _ => x') g').length < sessionCapBytes := by
    intro x' g' hs'
    obtain ⟨g₀', hR₀', -, hsess₀'⟩ := pqStep_session_reach hwf hstep hs'
    rw [← r3_encodeRecordX_eq_of_session_eq x' g₀' g' hsess₀']
    exact encodeRecordX_length_lt_sessionCap_cli hR₀'
  have hle_cap : ∀ x' g', st'.session = some (x', g') →
      (encodeRecordUnderExtras (fun _ => x') g').length ≤ fileCapBytes := by
    intro x' g' hs'
    have h := hcap x' g' hs'
    unfold sessionCapBytes at h
    omega
  exact ⟨wfPq_step X W st st' hwf hstep hlr hle_cap, hcap⟩

/-- Multi-step `PqxdhPartyInSpecDomain` and `< sessionCapBytes` record-size closure across `n`
accepted CLI calls from a sessionless initial party state with `n < 2 ^ 25`. -/
theorem wfPq_of_pqSteps_r3 {X : UnreachedPqxdhPrimitives} {W : PEParams} {n : ℕ}
    {st₀ stₙ : PqParty}
    (hwf₀ : PqxdhPartyInSpecDomain W st₀) (hnone₀ : st₀.session = none)
    (hlr₀ : lastResortUses st₀ = 0) (hsteps : PqSteps X W n st₀ stₙ) (hn : n < 2 ^ 25) :
    PqxdhPartyInSpecDomain W stₙ ∧ lastResortUses stₙ ≤ n ∧
      ∀ x g, stₙ.session = some (x, g) →
        (encodeRecordUnderExtras (fun _ => x) g).length < sessionCapBytes := by
  induction hsteps with
  | refl =>
    refine ⟨hwf₀, by omega, ?_⟩
    intro _ _ hs; rw [hnone₀] at hs; cases hs
  | @step m _ st₁ st₂ _ hlast ih =>
    obtain ⟨hwf₁, hlr₁, -⟩ := ih hwf₀ hnone₀ hlr₀ (by omega)
    have hlr_step := pqStep_lastResortUses_le X W st₁ st₂ hwf₁.2.2.2.2.2 hlast
    obtain ⟨hwf₂, hcap₂⟩ := wfPq_step_r3 hwf₁ hlast (by omega)
    exact ⟨hwf₂, by omega, hcap₂⟩

end CryptoVerification.LibsignalCli.Entry
