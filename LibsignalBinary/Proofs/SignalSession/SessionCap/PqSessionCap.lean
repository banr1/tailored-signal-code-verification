/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.SessionCap.TopStateTight
public import LibsignalBinary.Proofs.SignalSession.SessionCap.PqReachInv

/-!
# `ReachablePqxdhSession` Session-Record Byte Bound (`≤ 1,209,331 < fileCapBytes`)

Combines `ReachPqInvCli` (`≤ 923,135` B non-PQ overhead) with `TopStateTight` (`≤ 286,196` B SPQR V1
state) to bound every `ReachablePqxdhSession` encoding by `1,209,331` bytes (`< fileCapBytes = 2^21`),
and extends the bound to all non-`.base-keys` files in `encodeDir W st`.
-/

@[expose] public section

set_option autoImplicit false

open CryptoGames.LibsignalSession (Crypto GhostState MessageType Mut RatchetState SessionState SignalMessage SignalMessageProtoCodec SignalProtocolError Spqr TripleRatchet aesCbcDecrypt initializeInitiatorSession initializeRecipientSession liftE maxForwardJumps rootCreateChain zoom)
open CryptoVerification.E2E (Bytes LocalIdentity PEParams ReachablePqxdhSession RecordExtras acceptInput encodeRecordUnderExtras initiateInput initiateState keyPairOf modelPrims ofU8 pqxdhSessionParams pqxdhSpqrSession recvPrekeyState)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.SignalSession (fileCapBytes)

namespace LibsignalBinary.Proofs.SignalSession.SessionCap.PqSessionCap

open CryptoGames.HKDF (Salt)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1 spqrV1Init spqrV1Session)
open LibsignalBinary.Proofs.SignalSession.SessionCap.TopStateTight
  (TopStateTight topStateTight_init topStateTight_send topStateTight_recv topStateTight_length_le)
open LibsignalBinary.Proofs.SignalSession.SessionCap.PqReachInv
  (encodeRecordX_length_le_pq_add_923135)

private theorem Mut_exec_bind {σ α β : Type} (m : Mut σ α) (f : α → Mut σ β) (s : σ) :
    CryptoGames.LibsignalSession.Mut.exec (m >>= f) s =
      match CryptoGames.LibsignalSession.Mut.exec m s with
      | (.ok a, s') => CryptoGames.LibsignalSession.Mut.exec (f a) s'
      | (.error e, s') => (.error e, s') := by
  cases h : m s with
  | mk r s' =>
    cases r <;> (simp [CryptoGames.LibsignalSession.Mut.exec, h, bind, ExceptT.bind, ExceptT.mk, StateT.bind, ExceptT.bindCont,
      StateT.run, ExceptT.run]; try rfl)

private theorem Mut_exec_pure {σ α : Type} (a : α) (s : σ) :
    CryptoGames.LibsignalSession.Mut.exec (pure a : Mut σ α) s = (.ok a, s) := rfl
private theorem Mut_exec_throw {σ α : Type} (e : SignalProtocolError) (s : σ) :
    CryptoGames.LibsignalSession.Mut.exec (throw e : Mut σ α) s = (.error e, s) := rfl
private theorem Mut_exec_get {σ : Type} (s : σ) : CryptoGames.LibsignalSession.Mut.exec (get : Mut σ σ) s = (.ok s, s) := rfl
private theorem Mut_exec_set {σ : Type} (s' s : σ) :
    CryptoGames.LibsignalSession.Mut.exec (set s' : Mut σ Unit) s = (.ok (), s') := rfl
private theorem Mut_exec_modify {σ : Type} (f : σ → σ) (s : σ) :
    CryptoGames.LibsignalSession.Mut.exec (modify f : Mut σ Unit) s = (.ok (), f s) := rfl
private theorem Mut_exec_modifyGet {σ α : Type} (f : σ → α × σ) (s : σ) :
    CryptoGames.LibsignalSession.Mut.exec (modifyGet f : Mut σ α) s = (.ok (f s).1, (f s).2) := rfl
private theorem Mut_exec_liftE {σ α : Type} (r : Except SignalProtocolError α) (s : σ) :
    CryptoGames.LibsignalSession.Mut.exec (liftE r : Mut σ α) s = (r, s) := by cases r <;> rfl

private theorem onRatchet_pq {PQ α : Type} (m : Mut RatchetState α) (t t' : TripleRatchet PQ)
    (a : α) (h : CryptoGames.LibsignalSession.Mut.exec (CryptoGames.LibsignalSession.TripleRatchet.onRatchet m) t = (.ok a, t')) :
    t'.pqrState = t.pqrState := by
  unfold CryptoGames.LibsignalSession.TripleRatchet.onRatchet zoom at h
  simp only [Mut_exec_bind, Mut_exec_get] at h
  rcases hm : CryptoGames.LibsignalSession.Mut.exec m t.ratchet with ⟨_ | _, _⟩
  · simp [hm, Mut_exec_set, Mut_exec_liftE] at h
  · simp only [hm, Mut_exec_set, Mut_exec_liftE, Prod.mk.injEq, Except.ok.injEq] at h
    rcases h with ⟨rfl, rfl⟩; rfl

private theorem messageEncrypt_spqr {PQ PQC : Type} [Inhabited PQ]
    (C : Crypto) (codec : SignalMessageProtoCodec) (spqr : Spqr PQ PQC) (addrs : Option Bytes)
    (ptext : Bytes) (coins : PQC) (record s : SessionState PQ) (msg : SignalMessage)
    (h : CryptoGames.LibsignalSession.SessionState.messageEncrypt C codec spqr addrs ptext coins record = (.ok msg, s)) :
    ∃ salt pm, spqr.send record.pqRatchetState coins = some (s.pqRatchetState, salt, pm) := by
  unfold CryptoGames.LibsignalSession.SessionState.messageEncrypt at h
  rcases hfrom : CryptoGames.LibsignalSession.Mut.exec CryptoGames.LibsignalSession.OutgoingTripleRatchet.fromSessionState record with ⟨_ | o, _⟩
  · rw [hfrom] at h; cases h
  · rw [hfrom] at h; dsimp only at h
    have hpq : o.pqrState = record.pqRatchetState := by
      revert hfrom; unfold CryptoGames.LibsignalSession.OutgoingTripleRatchet.fromSessionState CryptoGames.LibsignalSession.SessionState.takePqRatchetState
      rcases hsc : record.senderChain with _ | _
      · simp [Mut_exec_bind, Mut_exec_get, hsc, Mut_exec_throw]
      · simp only [Mut_exec_bind, Mut_exec_get, hsc, Mut_exec_modifyGet]
        split
        · simp [Mut_exec_throw]
        · rcases record.remoteIdentity with _ | _
          · simp [Mut_exec_throw]
          · simp only [Mut_exec_pure, Prod.mk.injEq, Except.ok.injEq]
            rintro ⟨rfl, rfl⟩; rfl
    rcases henc : CryptoGames.LibsignalSession.Mut.exec (CryptoGames.LibsignalSession.OutgoingTripleRatchet.encrypt C codec spqr ptext
        (record.encryptAddresses addrs) coins) o with ⟨_ | _, _⟩
    · rw [henc] at h; cases h
    · rw [henc] at h; simp only [Prod.mk.injEq, Except.ok.injEq] at h; rcases h with ⟨rfl, rfl⟩
      unfold CryptoGames.LibsignalSession.OutgoingTripleRatchet.encrypt at henc
      simp only [Mut_exec_bind, Mut_exec_get] at henc
      cases hpan : spqr.sendPanics o.pqrState coins
      · simp only [hpan, Bool.false_eq_true, ↓reduceIte] at henc
        rcases hspqr : spqr.send o.pqrState coins with _ | ⟨_, salt, pm⟩
        · simp [hspqr, Mut_exec_throw] at henc
        · simp only [hspqr, Mut_exec_bind] at henc
          rcases hn : o.senderChainKey.nextChainKey C.F with _ | _
          · simp [hn, Mut_exec_liftE] at henc
          · simp only [hn, Mut_exec_liftE, Mut_exec_set, Mut_exec_pure,
              Prod.mk.injEq] at henc
            rcases henc with ⟨-, rfl⟩
            exact ⟨salt, pm, by simpa [CryptoGames.LibsignalSession.OutgoingTripleRatchet.applyToSessionState, hpq] using hspqr⟩
      · simp [hpan, Mut_exec_throw] at henc

private theorem tryDecryptFromRecord_spqr {PQ PQC : Type} [Inhabited PQ]
    (C : Crypto) (spqr : Spqr PQ PQC) (expected : Option Bytes) (m : SignalMessage)
    (msgType : MessageType) (coins : BitVec 256) (record s : SessionState PQ) (pt : Bytes)
    (h : CryptoGames.LibsignalSession.SessionState.tryDecryptFromRecord C spqr expected m msgType coins record = (.ok pt, s)) :
    ∃ salt, spqr.recv record.pqRatchetState m.pqRatchet = .ok (s.pqRatchetState, salt) := by
  unfold CryptoGames.LibsignalSession.SessionState.tryDecryptFromRecord at h; split_ifs at h
  · cases h
  · rcases hd : CryptoGames.LibsignalSession.Mut.exec (CryptoGames.LibsignalSession.SessionState.tryDecryptWithState C spqr expected m msgType coins) record with
      ⟨_ | _, _⟩
    · rw [hd] at h; cases h
    · rw [hd] at h; simp only [Prod.mk.injEq, Except.ok.injEq] at h; rcases h with ⟨rfl, rfl⟩
      unfold CryptoGames.LibsignalSession.SessionState.tryDecryptWithState CryptoGames.LibsignalSession.TripleRatchet.fromSessionState
        CryptoGames.LibsignalSession.SessionState.takeRatchetState CryptoGames.LibsignalSession.SessionState.takePqRatchetState at hd
      simp only [Mut_exec_bind, Mut_exec_get, Mut_exec_modifyGet] at hd
      rcases hrem : record.remoteIdentity with _ | rem
      · simp [hrem, Mut_exec_throw] at hd
      · simp only [hrem, Mut_exec_pure] at hd
        set tr0 : TripleRatchet PQ := ⟨⟨record.rootKey, record.senderChain, record.receiverChains,
          record.previousCounter, maxForwardJumps⟩, record.pqRatchetState, record.localIdentity, rem⟩
        rcases hdec : CryptoGames.LibsignalSession.Mut.exec (CryptoGames.LibsignalSession.TripleRatchet.decrypt C spqr expected m msgType coins) tr0 with
          ⟨_ | _, _⟩
        · simp [hdec, Mut_exec_liftE] at hd
        · simp only [hdec, Mut_exec_liftE, Mut_exec_modify, Prod.mk.injEq] at hd
          rcases hd with ⟨-, rfl⟩; unfold CryptoGames.LibsignalSession.TripleRatchet.decrypt at hdec
          simp only [Mut_exec_bind] at hdec
          rcases hens : CryptoGames.LibsignalSession.Mut.exec (CryptoGames.LibsignalSession.TripleRatchet.onRatchet
              (CryptoGames.LibsignalSession.RatchetState.ensureReceiverChain C m.senderRatchetKey coins)) tr0 with ⟨_ | ck, tr1⟩
          · rw [hens] at hdec; cases hdec
          · rw [hens] at hdec; dsimp only at hdec
            have hpq1 := onRatchet_pq _ tr0 tr1 ck hens
            rcases hcons : CryptoGames.LibsignalSession.Mut.exec (CryptoGames.LibsignalSession.TripleRatchet.onRatchet
                (CryptoGames.LibsignalSession.RatchetState.consumeMessageKey C.F m.senderRatchetKey ck m.counter msgType)) tr1 with
              ⟨_ | mkg, tr2⟩
            · rw [hcons] at hdec; cases hdec
            · rw [hcons] at hdec; dsimp only at hdec
              have hpq2 := onRatchet_pq _ tr1 tr2 mkg hcons
              simp only [Mut_exec_get] at hdec
              cases hpan : spqr.recvPanics tr2.pqrState m.pqRatchet
              · simp only [hpan, Bool.false_eq_true, ↓reduceIte] at hdec
                rcases hspqr : spqr.recv tr2.pqrState m.pqRatchet with err | ⟨_, salt⟩
                · cases err <;> simp [hspqr, Mut_exec_throw] at hdec
                · simp only [hspqr, Mut_exec_bind, Mut_exec_pure] at hdec; split_ifs at hdec
                  · simp [Mut_exec_throw] at hdec
                  · rcases haes : aesCbcDecrypt C.D (mkg.generateKeys C.F salt).cipherKey
                        (mkg.generateKeys C.F salt).iv m.ciphertext with _ | _
                    · simp [haes, Mut_exec_throw] at hdec
                    · simp only [haes, Mut_exec_bind, Mut_exec_modify, Mut_exec_pure,
                        Prod.mk.injEq] at hdec
                      rcases hdec with ⟨-, rfl⟩
                      exact ⟨salt, by simpa [CryptoGames.LibsignalSession.TripleRatchet.applyToSessionState,
                        CryptoGames.LibsignalSession.SessionState.clearUnacknowledgedPreKeyMessage, hpq2, hpq1, tr0] using hspqr⟩
              · simp [hpan, Mut_exec_throw] at hdec

/-- Every reachable PQXDH session (`ReachablePqxdhSession W me x g`) has a `TopStateTight`
SPQR V1 state. -/
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
      rcases hrc : rootCreateChain W.C (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.rootKey)) ⟨b.spkPub⟩
          (CryptoGames.LibsignalSession.KeyPair.generate W.C (CryptoGames.HKDF.bytesToKey32 ((t.toList.drop 160).take 32))).privateKey with
        _ | ⟨_, _⟩
      · simp [hrc] at hi
      · rw [hrc] at hi; simp only [Option.some.injEq, Prod.mk.injEq] at hi
        rcases hi with ⟨rfl, rfl⟩
        exact topStateTight_init W.C.F W.Q.K .a2b _
  | recvPrekey X' P me' k m rc _ _ _ hr =>
    unfold recvPrekeyState at hr
    rcases htf : CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec m.inner with _ | inner
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
              ⟨⟨m.idPub⟩⟩ (keyPairOf W.C k.spkPriv) (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.rootKey))
              (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.chainKey)) (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.pqrKey))
          rcases hd : CryptoGames.LibsignalSession.SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
              ((pqxdhSessionParams W).expectedAddrs P) inner .preKey rc st0 with ⟨err | pt', st⟩
          · rw [hd] at hr; cases err <;> cases hr
          · rw [hd] at hr; simp only [Option.some.injEq, Prod.mk.injEq] at hr
            rcases hr with ⟨rfl, rfl, rfl⟩
            obtain ⟨salt, hspqr⟩ := tryDecryptFromRecord_spqr W.C (pqxdhSpqrSession W)
              ((pqxdhSessionParams W).expectedAddrs P) inner .preKey rc st0 st pt' hd
            have h0 : TopStateTight W.C.F W.Q.K st0.pqRatchetState :=
              topStateTight_init W.C.F W.Q.K .b2a _
            exact topStateTight_recv W.C.F W.Q.K h0 hspqr
  | @send _ _ g_s m r _ _ ih =>
    unfold CryptoGames.LibsignalSession.Params.send
    rcases hm : CryptoGames.LibsignalSession.SessionState.messageEncrypt (pqxdhSessionParams W).C (pqxdhSessionParams W).codec
        (pqxdhSessionParams W).spqr ((pqxdhSessionParams W).sendAddrs g_s.party) m r g_s.session with
      ⟨_ | msg, s⟩
    · exact ih
    · dsimp only
      obtain ⟨salt, pm, hspqr⟩ := messageEncrypt_spqr (pqxdhSessionParams W).C
        (pqxdhSessionParams W).codec (pqxdhSessionParams W).spqr
        ((pqxdhSessionParams W).sendAddrs g_s.party) m r g_s.session s msg hm
      exact topStateTight_send W.C.F W.Q.K ih hspqr
  | @recv _ _ g_r _ c rc _ _ _ hrec ih =>
    unfold CryptoGames.LibsignalSession.Params.receive at hrec
    rcases htf : CryptoGames.LibsignalSession.SignalMessage.tryFrom (pqxdhSessionParams W).codec c with _ | msg
    · simp [htf] at hrec
    · rw [htf] at hrec; dsimp only at hrec
      rcases hd : CryptoGames.LibsignalSession.SessionState.tryDecryptFromRecord (pqxdhSessionParams W).C
          (pqxdhSessionParams W).spqr ((pqxdhSessionParams W).expectedAddrs g_r.party) msg .whisper
          rc g_r.session with ⟨_ | pt, s⟩
      · simp [hd] at hrec
      · rw [hd] at hrec; simp only [Option.some.injEq, Prod.mk.injEq] at hrec
        rcases hrec with ⟨rfl, -⟩
        obtain ⟨salt, hspqr⟩ := tryDecryptFromRecord_spqr (pqxdhSessionParams W).C
          (pqxdhSessionParams W).spqr ((pqxdhSessionParams W).expectedAddrs g_r.party) msg .whisper
          rc g_r.session s pt hd
        exact topStateTight_recv W.C.F W.Q.K ih hspqr

/-- Every reachable PQXDH session's SPQR V1 state is at most `286,196` bytes. -/
theorem reachPq_pqLength_le_286196 {W : PEParams} {me : LocalIdentity} {x : RecordExtras}
    {g : GhostState Bytes} (hR : ReachablePqxdhSession W me x g) :
    g.session.pqRatchetState.length ≤ 286196 :=
  topStateTight_length_le W.C.F W.Q.K (reachPq_topStateTight hR)

/-- Tight honest `SessionRecord` encoding bound: every `ReachablePqxdhSession` record encodes to
at most `923,135 + 286,196 = 1,209,331` bytes. -/
theorem reachPq_encodeRecordX_length_le_1209331 {W : PEParams} {me : LocalIdentity}
    {x : RecordExtras} {g : GhostState Bytes} (hR : ReachablePqxdhSession W me x g) :
    (encodeRecordUnderExtras (fun _ => x) g).length ≤ 1209331 := by
  have hdr := encodeRecordX_length_le_pq_add_923135 hR
  have hpq := reachPq_pqLength_le_286196 hR
  omega

/-- Every `ReachablePqxdhSession` record encodes to strictly fewer than `fileCapBytes`
(`2 ^ 21 = 2,097,152` bytes, `2 MiB`). -/
theorem reachPq_encodeRecordX_length_lt_fileCapBytes {W : PEParams} {me : LocalIdentity}
    {x : RecordExtras} {g : GhostState Bytes} (hR : ReachablePqxdhSession W me x g) :
    (encodeRecordUnderExtras (fun _ => x) g).length < fileCapBytes := by
  have h := reachPq_encodeRecordX_length_le_1209331 hR
  unfold fileCapBytes
  omega

/-- `≤ fileCapBytes` form of `reachPq_encodeRecordX_length_lt_fileCapBytes`. -/
theorem reachPq_encodeRecordX_length_le_fileCapBytes {W : PEParams} {me : LocalIdentity}
    {x : RecordExtras} {g : GhostState Bytes} (hR : ReachablePqxdhSession W me x g) :
    (encodeRecordUnderExtras (fun _ => x) g).length ≤ fileCapBytes :=
  Nat.le_of_lt (reachPq_encodeRecordX_length_lt_fileCapBytes hR)

private theorem byteArray_loop_len (bs : ByteArray) (i : Nat) (acc : List UInt8) (hi : i ≤ bs.size) :
    (ByteArray.toList.loop bs i acc).length = acc.length + (bs.size - i) := by
  unfold ByteArray.toList.loop
  split
  · rw [byteArray_loop_len bs (i + 1) _ (by omega)]; simp; omega
  · simp; omega
termination_by bs.size - i
decreasing_by
  have : i < bs.size := ‹_›; omega

theorem textBytes_partyAddress_length_le_fileCapBytes
    (P : CryptoGames.Party) :
    (CryptoVerification.SignalSession.textBytes
      (CryptoVerification.SignalSession.partyAddress P).text).length ≤ fileCapBytes := by
  have h1 : ∀ s : String, (CryptoVerification.SignalSession.textBytes s).length = s.utf8ByteSize := by
    intro s
    unfold CryptoVerification.SignalSession.textBytes
      CryptoVerification.LibsignalTripleRatchetRepr.utf8 ByteArray.toList
    rw [List.length_map, byteArray_loop_len _ 0 [] (Nat.zero_le _), String.toUTF8_eq_toByteArray]
    have hsz : s.toByteArray.size = s.utf8ByteSize := String.size_toByteArray
    simp [hsz]
  rw [h1]
  have hn : (CryptoVerification.E2E.partyAddressName P).utf8ByteSize ≤ 64 := by cases P <;> decide
  have hd : ".".utf8ByteSize = 1 := by decide
  have ht1 : toString (1 : Nat) = String.singleton (Nat.digitChar 1) := Nat.repr_of_lt (by omega)
  have hc := Char.utf8Size_le_four (Nat.digitChar 1)
  simp only [CryptoVerification.SignalSession.Address.text,
    CryptoVerification.SignalSession.partyAddress, ht1,
    String.utf8ByteSize_append, String.utf8ByteSize_singleton, fileCapBytes]
  omega

theorem le32_length_le_fileCapBytes (v : BitVec 32) :
    (CryptoVerification.SignalSession.le32 v).length ≤ fileCapBytes := by
  simp [CryptoVerification.SignalSession.le32, fileCapBytes]

theorem identityKey_serialize_length_le_fileCapBytes
    (k : CryptoGames.LibsignalSession.IdentityKey) :
    k.serialize.length ≤ fileCapBytes := by
  simp [CryptoGames.LibsignalSession.IdentityKey.serialize,
    CryptoGames.LibsignalSession.PublicKey.serialize, fileCapBytes]

private theorem encodeVarintAux_len_le : ∀ (k : Nat) (v : BitVec 64),
    (CryptoVerification.LibsignalProtoCodec.encodeVarintAux k v).length ≤ k
  | 0, _ => by simp [CryptoVerification.LibsignalProtoCodec.encodeVarintAux]
  | k + 1, v => by
    unfold CryptoVerification.LibsignalProtoCodec.encodeVarintAux; split_ifs
    · simp
    · simp only [List.length_cons]
      exact Nat.add_le_add_right (encodeVarintAux_len_le k (v >>> 7)) 1

private theorem encodeVarint_len_le (v : BitVec 64) :
    (CryptoVerification.LibsignalProtoCodec.encodeVarint v).length ≤ 10 :=
  encodeVarintAux_len_le 10 v

private theorem encodeKey_len_le (tag : Nat)
    (wt : CryptoVerification.LibsignalProtoCodec.WireType) :
    (CryptoVerification.LibsignalProtoCodec.encodeKey tag wt).length ≤ 10 :=
  encodeVarintAux_len_le 10 _

private theorem encodeBytes3_length_le (tag : Nat) (v : List (BitVec 8)) :
    (CryptoVerification.RecordCodecs.encodeProto3BytesField tag v).length ≤ 20 + v.length := by
  unfold CryptoVerification.RecordCodecs.encodeProto3BytesField
  split_ifs
  · simp
  · unfold CryptoVerification.LibsignalProtoCodec.encodeBytesField
    have h1 := encodeKey_len_le tag .lengthDelimited
    have h2 := encodeVarint_len_le (BitVec.ofNat 64 v.length)
    simp only [List.length_append]
    omega

private theorem encodeUint32_3_length_le (tag : Nat) (v : BitVec 32) :
    (CryptoVerification.RecordCodecs.encodeProto3Uint32Field tag v).length ≤ 20 := by
  unfold CryptoVerification.RecordCodecs.encodeProto3Uint32Field
  split_ifs
  · simp
  · change (CryptoVerification.LibsignalProtoCodec.encodeKey tag .varint ++
      CryptoVerification.LibsignalProtoCodec.encodeVarint (v.setWidth 64)).length ≤ 20
    have h1 := encodeKey_len_le tag .varint
    have h2 := encodeVarint_len_le (v.setWidth 64)
    simp only [List.length_append]
    omega

private theorem encodeFixed64_3_length_le (tag : Nat) (v : BitVec 64) :
    (CryptoVerification.RecordCodecs.encodeProto3Fixed64Field tag v).length ≤ 18 := by
  unfold CryptoVerification.RecordCodecs.encodeProto3Fixed64Field
  split_ifs
  · simp
  · have h1 := encodeKey_len_le tag .sixtyFourBit
    unfold CryptoVerification.RecordCodecs.le64Bytes
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem idKeyPair_encode_length_le_fileCapBytes (C : Crypto)
    (idPriv : List.Vector (BitVec 8) 32) :
    (CryptoVerification.RecordCodecs.IdentityKeyPairStructure.encode
      ⟨CryptoVerification.E2E.djbKey (keyPairOf C idPriv).publicKey.bytes, idPriv.toList⟩).length ≤
        fileCapBytes := by
  unfold CryptoVerification.RecordCodecs.IdentityKeyPairStructure.encode
  simp only [List.length_append]
  have h1 := encodeBytes3_length_le 1 (CryptoVerification.E2E.djbKey (keyPairOf C idPriv).publicKey.bytes)
  have h2 := encodeBytes3_length_le 2 idPriv.toList
  have hd : (CryptoVerification.E2E.djbKey (keyPairOf C idPriv).publicKey.bytes).length = 33 := by
    simp [CryptoVerification.E2E.djbKey]
  have hp : idPriv.toList.length = 32 := idPriv.2
  unfold fileCapBytes
  omega

theorem signedRecordBytes_length_le_fileCapBytes (C : Crypto) (id : BitVec 32)
    (k : CryptoVerification.SignalSession.PqSignedKey) :
    (CryptoVerification.SignalSession.signedRecordBytes C id k).length ≤ fileCapBytes := by
  unfold CryptoVerification.SignalSession.signedRecordBytes
    CryptoVerification.RecordCodecs.SignedPreKeyRecordStructure.encode
  simp only [List.length_append]
  have h1 := encodeUint32_3_length_le 1 id
  have h2 := encodeBytes3_length_le 2 (CryptoVerification.E2E.djbKey (keyPairOf C k.priv).publicKey.bytes)
  have h3 := encodeBytes3_length_le 3 k.priv.toList
  have h4 := encodeBytes3_length_le 4 k.sig.toList
  have h5 := encodeFixed64_3_length_le 5 k.timestamp
  have hd : (CryptoVerification.E2E.djbKey (keyPairOf C k.priv).publicKey.bytes).length = 33 := by
    simp [CryptoVerification.E2E.djbKey]
  have hp : k.priv.toList.length = 32 := k.priv.2
  have hs : k.sig.toList.length = 64 := k.sig.2
  unfold fileCapBytes
  omega

theorem kyberRecordBytes_length_le_fileCapBytes (id : BitVec 32)
    (k : CryptoVerification.SignalSession.PqKyberKey) :
    (CryptoVerification.SignalSession.kyberRecordBytes id k).length ≤ fileCapBytes := by
  unfold CryptoVerification.SignalSession.kyberRecordBytes
    CryptoVerification.RecordCodecs.SignedPreKeyRecordStructure.encode
  simp only [List.length_append]
  have h1 := encodeUint32_3_length_le 1 id
  have h2 := encodeBytes3_length_le 2 (CryptoVerification.E2E.kyberKey k.pub)
  have h3 := encodeBytes3_length_le 3 (0x08#8 :: k.sec.toList)
  have h4 := encodeBytes3_length_le 4 k.sig.toList
  have h5 := encodeFixed64_3_length_le 5 k.timestamp
  have hpub : (CryptoVerification.E2E.kyberKey k.pub).length = 1569 := by
    simp [CryptoVerification.E2E.kyberKey]
  have hsec : (0x08#8 :: k.sec.toList).length = 3169 := by simp
  have hsig : k.sig.toList.length = 64 := k.sig.2
  unfold fileCapBytes
  omega

theorem oneTimeRecordBytes_length_le_fileCapBytes (C : Crypto) (id : BitVec 32)
    (sk : List.Vector (BitVec 8) 32) :
    (CryptoVerification.SignalSession.oneTimeRecordBytes C id sk).length ≤ fileCapBytes := by
  unfold CryptoVerification.SignalSession.oneTimeRecordBytes
    CryptoVerification.RecordCodecs.PreKeyRecordStructure.encode
  simp only [List.length_append]
  have h1 := encodeUint32_3_length_le 1 id
  have h2 := encodeBytes3_length_le 2 (CryptoVerification.E2E.djbKey (keyPairOf C sk).publicKey.bytes)
  have h3 := encodeBytes3_length_le 3 sk.toList
  have hd : (CryptoVerification.E2E.djbKey (keyPairOf C sk).publicKey.bytes).length = 33 := by
    simp [CryptoVerification.E2E.djbKey]
  have hp : sk.toList.length = 32 := sk.2
  unfold fileCapBytes
  omega

/-- Every non-`.base-keys` file in `encodeDir W st` has length `≤ fileCapBytes`, provided any
stored session in `st` agrees on `.session` with a `ReachablePqxdhSession`. -/
theorem encodeDir_nonBaseKeys_length_le_fileCapBytes (W : PEParams)
    (st : CryptoVerification.SignalSession.PqParty)
    (hsess : ∀ x g, st.session = some (x, g) →
      ∃ g₀, ReachablePqxdhSession W st.me x g₀ ∧ g₀.session = g.session) :
    ∀ f ∈ CryptoVerification.SignalSession.encodeDir W st,
      (∀ i, f.1 ≠ CryptoVerification.SignalSession.baseKeysFile i) → f.2.length ≤ fileCapBytes := by
  intro f hf hne
  unfold CryptoVerification.SignalSession.encodeDir at hf
  simp only [List.mem_append] at hf
  rcases hf with ((((((hf_hdr | hf_peer) | hf_sess) | hf_sig) | hf_ot) | hf_kot) | hf_klr)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf_hdr
    rcases hf_hdr with rfl | rfl | rfl
    · exact textBytes_partyAddress_length_le_fileCapBytes st.party
    · exact idKeyPair_encode_length_le_fileCapBytes W.C st.me.idPriv
    · exact le32_length_le_fileCapBytes st.me.regId
  · cases hp : st.peerId with
    | none => simp [hp] at hf_peer
    | some k =>
      simp only [hp, List.mem_singleton] at hf_peer
      subst hf_peer
      exact identityKey_serialize_length_le_fileCapBytes k
  · cases hs : st.session with
    | none => simp [hs] at hf_sess
    | some xg =>
      rcases xg with ⟨x, g⟩
      simp only [hs, List.mem_singleton] at hf_sess
      subst hf_sess
      obtain ⟨g₀, hR₀, hs₀⟩ := hsess x g hs
      have heq : encodeRecordUnderExtras (fun _ => x) g₀ = encodeRecordUnderExtras (fun _ => x) g := by
        unfold encodeRecordUnderExtras; rw [hs₀]
      rw [← heq]
      exact reachPq_encodeRecordX_length_le_fileCapBytes hR₀
  · rw [List.mem_map] at hf_sig
    rcases hf_sig with ⟨⟨i, k⟩, -, rfl⟩
    exact signedRecordBytes_length_le_fileCapBytes W.C i k
  · rw [List.mem_map] at hf_ot
    rcases hf_ot with ⟨⟨i, optSk⟩, -, rfl⟩
    cases optSk with
    | none => simp [fileCapBytes]
    | some sk => exact oneTimeRecordBytes_length_le_fileCapBytes W.C i sk
  · rw [List.mem_map] at hf_kot
    rcases hf_kot with ⟨⟨i, optK⟩, -, rfl⟩
    cases optK with
    | none => simp [fileCapBytes]
    | some k => exact kyberRecordBytes_length_le_fileCapBytes i k
  · rw [List.mem_flatten] at hf_klr
    rcases hf_klr with ⟨sub, hsub, hf_in⟩
    rw [List.mem_map] at hsub
    rcases hsub with ⟨⟨i, k, _⟩, -, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf_in
    rcases hf_in with rfl | rfl
    · exact kyberRecordBytes_length_le_fileCapBytes i k
    · exact absurd rfl (hne i)

end LibsignalBinary.Proofs.SignalSession.SessionCap.PqSessionCap
