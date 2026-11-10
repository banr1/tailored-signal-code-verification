/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApi

/-!
# Facts about the libsignal session API model

**Checked by Lean.** No theorem of `Computational/Theorems/` unfolds a definition of this file, and
Lean's kernel checks every proof in it: you do not need to read it to trust those theorems.

Flattened characterizations (`decryptFlat`, `encryptFlat`) and properties of `messageEncrypt` and
`messageDecryptSignal`: store-call trace prefixes (`fullTrace`), atomic store-on-success (`Stored`),
well-formedness preservation (`Session.Wf`), panic characterization (`ApiError.panic`), and
non-vacuity witnesses.
-/

@[expose] public section

namespace CryptoGames.LibsignalSessionApi
open LibsignalSession

variable {Addr PQ PQC E : Type} [Inhabited PQ]

/-! ### `ApiError.ofProtocol` -/

/-- `ApiError.ofProtocol` sends exactly the session model's panic to `ApiError.panic`. -/
@[simp] theorem ApiError.ofProtocol_eq_panic {e : SignalProtocolError} :
    (ApiError.ofProtocol e : ApiError Addr E) = .panic ↔ e = .panic := by
  cases e <;> simp [ApiError.ofProtocol]

/-- `ApiError.protocol` never carries the session model's panic. -/
@[simp] theorem ApiError.ofProtocol_ne_protocol_panic {e : SignalProtocolError} :
    (ApiError.ofProtocol e : ApiError Addr E) ≠ .protocol .panic := by
  cases e <;> simp [ApiError.ofProtocol]

/-! ### Flattened forms -/

/-- `api_simp [h, …]`: `simp` with the `Api` monad (`ExceptT` over `StateM`) unfolded to plain
functions, plus the given lemmas. -/
local macro "api_simp" " [" xs:Lean.Parser.Tactic.simpLemma,* "]"
    loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp [Api.run, storeCall, liftProtocol, modify, modifyGet,
      MonadStateOf.modifyGet, ExceptT.run, StateT.run, bind, ExceptT.bind, ExceptT.mk,
      ExceptT.lift, ExceptT.bindCont, StateT.bind, pure, ExceptT.pure, StateT.pure,
      StateT.modifyGet, throw, throwThe, MonadExceptOf.throw, Id.run, liftM, monadLift,
      MonadLift.monadLift, MonadLiftT.monadLift, StateT.lift, StateT.map, Functor.map, get, getThe,
      MonadStateOf.get, StateT.get, set, MonadStateOf.set, StateT.set, $xs,*] $(loc)?)

/-- `message_decrypt_signal` flattened: the result and the trace by cases on the store answers and
the decryption. -/
def decryptFlat (C : Crypto) (spqr : Spqr PQ PQC)
    (ser : Addr → Addr → Option (List (BitVec 8))) (answers : StoreAnswers PQ E)
    (ciphertext : SignalMessage) (remote loc : Addr) (coins : BitVec 256) :
    Except (ApiError Addr E) (List (BitVec 8)) × List (StoreCall Addr PQ) :=
  let load := StoreCall.loadSession remote
  match answers.loadSession with
  | .error e => (.error (.store e), [load])
  | .ok none => (.error (.sessionNotFound remote "message_decrypt_signal"), [load])
  | .ok (some record) =>
    match record.tryDecryptFromRecord C spqr (ser remote loc) ciphertext coins with
    | .error e => (.error (ApiError.ofProtocol e), [load])
    | .ok (ptext, record') =>
      match record'.currentSession.bind (·.state.remoteIdentity) with
      | none => (.error .panic, [load])
      | some k =>
        let trust := StoreCall.isTrustedIdentity remote k .receiving
        match answers.isTrustedIdentity with
        | .error e => (.error (.store e), [load, trust])
        | .ok false => (.error (.untrustedIdentity remote), [load, trust])
        | .ok true =>
          let save := StoreCall.saveIdentity remote k
          match answers.saveIdentity with
          | .error e => (.error (.store e), [load, trust, save])
          | .ok _ =>
            let store := StoreCall.storeSession remote record'
            match answers.storeSession with
            | .error e => (.error (.store e), [load, trust, save, store])
            | .ok () => (.ok ptext, [load, trust, save, store])

theorem messageDecryptSignal_eq_flat (C : Crypto) (spqr : Spqr PQ PQC)
    (ser : Addr → Addr → Option (List (BitVec 8))) (answers : StoreAnswers PQ E)
    (ciphertext : SignalMessage) (remote loc : Addr) (coins : BitVec 256) :
    messageDecryptSignal C spqr ser answers ciphertext remote loc coins =
      decryptFlat C spqr ser answers ciphertext remote loc coins := by
  rcases answers with ⟨l, t, s, st⟩
  simp only [messageDecryptSignal, decryptFlat]
  rcases l with el | _ | record
  · api_simp []
  · api_simp []
  · rcases hd : record.tryDecryptFromRecord C spqr (ser remote loc) ciphertext coins with
      ed | ⟨ptext, record'⟩
    · api_simp [hd]
    · rcases record' with ⟨_ | session⟩
      · api_simp [hd]
      · rcases hk : session.state.remoteIdentity with _ | k
        · api_simp [hd, hk]
        · rcases t with et | _ | _ <;> rcases s with es | _ <;> rcases st with est | _ <;>
            api_simp [hd, hk]

/-- The `PreKeySignalMessage` wrapping and the `encrypt` call of `message_encrypt`
(`session_management.rs:76–119`), flattened. -/
def wrapFlat (C : Crypto) (codec : SignalMessageProtoCodec) (spqr : Spqr PQ PQC)
    (ser : Addr → Addr → Option (List (BitVec 8))) (ptext : List (BitVec 8)) (remote loc : Addr)
    (now : SystemTime) (coins : PQC) (session : Session PQ) (otr : OutgoingTripleRatchet PQ) :
    Except (ApiError Addr E) (CiphertextMessage × OutgoingTripleRatchet PQ) :=
  match session.pendingPreKey with
  | some items =>
    match SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat with
    | none => .error .panic
    | some timestamp =>
      match timestamp.checkedAddSecs maxUnacknowledgedSessionAge with
      | none => .error .panic
      | some expiry =>
        if expiry.lt now then .error (.sessionNotFound remote "message_encrypt")
        else
          match execOk (OutgoingTripleRatchet.encrypt C codec spqr ptext (ser loc remote) coins) otr with
          | .error e => .error (ApiError.ofProtocol e)
          | .ok (signalMessage, otr') =>
            .ok (.preKeySignalMessage (PreKeySignalMessage.new otr'.sessionVersion
              session.localRegistrationId items.preKeyId items.signedPreKeyId
              (session.pendingKyberPreKey.map fun k => ⟨k.preKeyId, k.ciphertext⟩) items.baseKey
              otr'.localIdentityKey signalMessage), otr')
  | none =>
    match execOk (OutgoingTripleRatchet.encrypt C codec spqr ptext none coins) otr with
    | .error e => .error (ApiError.ofProtocol e)
    | .ok (signalMessage, otr') => .ok (.signalMessage signalMessage, otr')

/-- `message_encrypt` flattened. -/
def encryptFlat (C : Crypto) (codec : SignalMessageProtoCodec)
    (spqr : Spqr PQ PQC) (ser : Addr → Addr → Option (List (BitVec 8)))
    (answers : StoreAnswers PQ E) (ptext : List (BitVec 8)) (remote loc : Addr)
    (now : SystemTime) (coins : PQC) :
    Except (ApiError Addr E) CiphertextMessage × List (StoreCall Addr PQ) :=
  let load := StoreCall.loadSession remote
  match answers.loadSession with
  | .error e => (.error (.store e), [load])
  | .ok none => (.error (.sessionNotFound remote "message_encrypt"), [load])
  | .ok (some record) =>
    match record.currentSession with
    | none => (.error (.sessionNotFound remote "message_encrypt"), [load])
    | some session =>
      match execOk OutgoingTripleRatchet.fromSessionState session.state with
      | .error e => (.error (ApiError.ofProtocol e), [load])
      | .ok (otr, taken) =>
        match taken.remoteIdentity with
        | none => (.error .panic, [load])
        | some k =>
          match wrapFlat C codec spqr ser ptext remote loc now coins session otr with
          | .error e => (.error e, [load])
          | .ok (message, otr') =>
            let trust := StoreCall.isTrustedIdentity remote k .sending
            match answers.isTrustedIdentity with
            | .error e => (.error (.store e), [load, trust])
            | .ok false => (.error (.untrustedIdentity remote), [load, trust])
            | .ok true =>
              let save := StoreCall.saveIdentity remote k
              match answers.saveIdentity with
              | .error e => (.error (.store e), [load, trust, save])
              | .ok _ =>
                let store := StoreCall.storeSession remote
                  ⟨some { session with state := otr'.applyToSessionState taken }⟩
                match answers.storeSession with
                | .error e => (.error (.store e), [load, trust, save, store])
                | .ok () => (.ok message, [load, trust, save, store])

theorem messageEncrypt_eq_flat (C : Crypto) (codec : SignalMessageProtoCodec)
    (spqr : Spqr PQ PQC) (ser : Addr → Addr → Option (List (BitVec 8)))
    (answers : StoreAnswers PQ E) (ptext : List (BitVec 8)) (remote loc : Addr)
    (now : SystemTime) (coins : PQC) :
    messageEncrypt C codec spqr ser answers ptext remote loc now coins =
      encryptFlat C codec spqr ser answers ptext remote loc now coins := by
  rcases answers with ⟨l, t, s, st⟩
  simp only [messageEncrypt, encryptFlat]
  rcases l with el | _ | ⟨_ | session⟩
  · api_simp []
  · api_simp []
  · api_simp []
  · rcases hf : execOk OutgoingTripleRatchet.fromSessionState session.state with ef | ⟨otr, taken⟩
    · api_simp [hf]
    · rcases hk : taken.remoteIdentity with _ | k
      · api_simp [hf, hk]
      · rcases hp : session.pendingPreKey with _ | items
        · rcases he : execOk (OutgoingTripleRatchet.encrypt C codec spqr ptext none coins) otr with
            ee | ⟨sm, otr'⟩
          · api_simp [hf, hk, hp, he, wrapFlat]
          · rcases t with et | _ | _ <;> rcases s with es | _ <;> rcases st with est | _ <;>
              api_simp [hf, hk, hp, he, wrapFlat]
        · rcases h1 : SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat with _ | ts
          · api_simp [hf, hk, hp, h1, wrapFlat]
          · rcases h2 : ts.checkedAddSecs maxUnacknowledgedSessionAge with _ | expiry
            · api_simp [hf, hk, hp, h1, h2, wrapFlat]
            · by_cases h3 : expiry.lt now = true
              · api_simp [hf, hk, hp, h1, h2, h3, wrapFlat]
              · rcases he : execOk (OutgoingTripleRatchet.encrypt C codec spqr ptext
                    (ser loc remote) coins) otr with ee | ⟨sm, otr'⟩
                · api_simp [hf, hk, hp, h1, h2, h3, he, wrapFlat]
                · rcases t with et | _ | _ <;> rcases s with es | _ <;> rcases st with est | _ <;>
                    api_simp [hf, hk, hp, h1, h2, h3, he, wrapFlat]

/-! ### Traces and storage on the flattened forms

`fullTrace` and `Stored` are the vocabulary of the main results; the `*Flat_*` lemmas are those
results for `decryptFlat` / `encryptFlat`, transported below by `*_eq_flat`. -/

local instance : Inhabited IdentityKey := ⟨⟨⟨List.Vector.replicate 32 0⟩⟩⟩
local instance : Inhabited (SessionRecord PQ) := ⟨⟨none⟩⟩

/-- The four store calls of a run that gets to the end: load, trust check, save identity, store
the record `r`, all for the remote address. -/
def fullTrace (remote : Addr) (k : IdentityKey) (dir : Direction) (r : SessionRecord PQ) :
    List (StoreCall Addr PQ) :=
  [.loadSession remote, .isTrustedIdentity remote k dir, .saveIdentity remote k,
    .storeSession remote r]

/-- **The record was stored**: a `store_session` call was made and the store accepted it. -/
def Stored (answers : StoreAnswers PQ E) (trace : List (StoreCall Addr PQ)) : Prop :=
  answers.storeSession = .ok () ∧ ∃ a r, StoreCall.storeSession a r ∈ trace

theorem decryptFlat_prefix (C : Crypto) (spqr : Spqr PQ PQC)
    (ser : Addr → Addr → Option (List (BitVec 8))) (answers : StoreAnswers PQ E)
    (ciphertext : SignalMessage) (remote loc : Addr) (coins : BitVec 256) :
    ∃ k r, (decryptFlat C spqr ser answers ciphertext remote loc coins).2 ≠ [] ∧
      (decryptFlat C spqr ser answers ciphertext remote loc coins).2 <+:
        fullTrace remote k .receiving r := by
  unfold decryptFlat
  repeat' split
  all_goals first
    | exact ⟨_, _, List.cons_ne_nil _ _, List.prefix_iff_eq_take.mpr rfl⟩
    | exact ⟨_, default, List.cons_ne_nil _ _, List.prefix_iff_eq_take.mpr rfl⟩
    | exact ⟨default, default, List.cons_ne_nil _ _, List.prefix_iff_eq_take.mpr rfl⟩

theorem decryptFlat_ok_iff_stored (C : Crypto) (spqr : Spqr PQ PQC)
    (ser : Addr → Addr → Option (List (BitVec 8))) (answers : StoreAnswers PQ E)
    (ciphertext : SignalMessage) (remote loc : Addr) (coins : BitVec 256) :
    (∃ p, (decryptFlat C spqr ser answers ciphertext remote loc coins).1 = .ok p) ↔
      Stored answers (decryptFlat C spqr ser answers ciphertext remote loc coins).2 := by
  unfold decryptFlat
  repeat' split
  all_goals simp_all [Stored]

theorem decryptFlat_ok (C : Crypto) (spqr : Spqr PQ PQC)
    (ser : Addr → Addr → Option (List (BitVec 8))) (answers : StoreAnswers PQ E)
    (ciphertext : SignalMessage) (remote loc : Addr) (coins : BitVec 256) (p : List (BitVec 8))
    (h : (decryptFlat C spqr ser answers ciphertext remote loc coins).1 = .ok p) :
    ∃ k r, (decryptFlat C spqr ser answers ciphertext remote loc coins).2 =
      fullTrace remote k .receiving r ∧ answers.isTrustedIdentity = .ok true ∧
      answers.storeSession = .ok () := by
  unfold decryptFlat at h ⊢
  repeat' split at h
  all_goals simp at h
  all_goals simp_all
  exact ⟨_, _, rfl⟩

theorem decryptFlat_stored (C : Crypto) (spqr : Spqr PQ PQC)
    (ser : Addr → Addr → Option (List (BitVec 8))) (answers : StoreAnswers PQ E)
    (ciphertext : SignalMessage) (remote loc : Addr) (coins : BitVec 256) (a : Addr)
    (r : SessionRecord PQ)
    (h : StoreCall.storeSession a r ∈ (decryptFlat C spqr ser answers ciphertext remote loc coins).2) :
    a = remote ∧ ∃ record ptext, answers.loadSession = .ok (some record) ∧
      record.tryDecryptFromRecord C spqr (ser remote loc) ciphertext coins = .ok (ptext, r) := by
  unfold decryptFlat at h
  repeat' split at h
  all_goals simp at h
  all_goals simp_all

section encrypt
variable (C : Crypto) (codec : SignalMessageProtoCodec) (spqr : Spqr PQ PQC)
  (ser : Addr → Addr → Option (List (BitVec 8))) (answers : StoreAnswers PQ E)
  (ptext : List (BitVec 8)) (remote loc : Addr) (now : SystemTime) (coins : PQC)

theorem encryptFlat_prefix :
    ∃ k r, (encryptFlat C codec spqr ser answers ptext remote loc now coins).2 ≠ [] ∧
      (encryptFlat C codec spqr ser answers ptext remote loc now coins).2 <+:
        fullTrace remote k .sending r := by
  unfold encryptFlat
  repeat' split
  all_goals first
    | exact ⟨_, _, List.cons_ne_nil _ _, List.prefix_iff_eq_take.mpr rfl⟩
    | exact ⟨_, default, List.cons_ne_nil _ _, List.prefix_iff_eq_take.mpr rfl⟩
    | exact ⟨default, default, List.cons_ne_nil _ _, List.prefix_iff_eq_take.mpr rfl⟩

theorem encryptFlat_ok_iff_stored :
    (∃ m, (encryptFlat C codec spqr ser answers ptext remote loc now coins).1 = .ok m) ↔
      Stored answers (encryptFlat C codec spqr ser answers ptext remote loc now coins).2 := by
  unfold encryptFlat
  repeat' split
  all_goals simp_all [Stored]

theorem encryptFlat_ok (m : CiphertextMessage)
    (h : (encryptFlat C codec spqr ser answers ptext remote loc now coins).1 = .ok m) :
    ∃ k r, (encryptFlat C codec spqr ser answers ptext remote loc now coins).2 =
      fullTrace remote k .sending r ∧ answers.isTrustedIdentity = .ok true ∧
      answers.storeSession = .ok () := by
  unfold encryptFlat at h ⊢
  repeat' split at h
  all_goals simp at h
  all_goals simp_all
  exact ⟨_, _, rfl⟩

theorem encryptFlat_stored (a : Addr) (r : SessionRecord PQ)
    (h : StoreCall.storeSession a r ∈
      (encryptFlat C codec spqr ser answers ptext remote loc now coins).2) :
    a = remote ∧ ∃ record session otr taken m otr', answers.loadSession = .ok (some record) ∧
      record.currentSession = some session ∧
      execOk OutgoingTripleRatchet.fromSessionState session.state = .ok (otr, taken) ∧
      wrapFlat (E := E) C codec spqr ser ptext remote loc now coins session otr =
        .ok (m, otr') ∧
      r = ⟨some { session with state := otr'.applyToSessionState taken }⟩ := by
  unfold encryptFlat at h
  repeat' split at h
  all_goals simp at h
  all_goals simp_all

end encrypt

/-! ### Facts about the session model -/

/-- `OutgoingTripleRatchet::from_session_state` only moves the SPQR state out. -/
theorem execOk_fromSessionState {s t : SessionState PQ} {o : OutgoingTripleRatchet PQ}
    (h : execOk OutgoingTripleRatchet.fromSessionState s = .ok (o, t)) :
    t = { s with pqRatchetState := default } ∧ s.remoteIdentity.isSome := by
  unfold execOk Mut.exec OutgoingTripleRatchet.fromSessionState
    SessionState.takePqRatchetState at h
  rcases hs : s.senderChain with _ | sc <;> rcases hr : s.remoteIdentity with _ | k <;>
    api_simp [hs, hr] at h
  all_goals split_ifs at h <;> api_simp [] at h
  exact ⟨h.2.symm, rfl⟩

/-- `OutgoingTripleRatchet::from_session_state` does not panic. -/
theorem execOk_fromSessionState_ne_panic {s : SessionState PQ} :
    execOk (OutgoingTripleRatchet.fromSessionState (PQ := PQ)) s ≠ .error .panic := by
  intro h
  unfold execOk Mut.exec OutgoingTripleRatchet.fromSessionState
    SessionState.takePqRatchetState at h
  rcases hs : s.senderChain with _ | sc <;> rcases hr : s.remoteIdentity with _ | k <;>
    api_simp [hs, hr] at h
  all_goals split_ifs at h <;> api_simp [] at h

/-- `OutgoingTripleRatchet::from_session_state` succeeds on a state with a sender chain, a
version below 256 and a remote identity key. -/
theorem execOk_fromSessionState_of {s : SessionState PQ} {sc : SenderChain} {k : IdentityKey}
    (hs : s.senderChain = some sc) (hv : s.version.toNat < 256) (hr : s.remoteIdentity = some k) :
    execOk OutgoingTripleRatchet.fromSessionState s =
      .ok (⟨sc.ratchetKey, sc.chainKey, s.previousCounter, s.pqRatchetState,
        BitVec.ofNat 8 s.version.toNat, s.localIdentity, k⟩, { s with pqRatchetState := default }) := by
  unfold execOk Mut.exec OutgoingTripleRatchet.fromSessionState
    SessionState.takePqRatchetState
  api_simp [hs, hr]
  split_ifs with hc
  · simp only [SessionState.version] at hc hv
    omega
  · api_simp [SessionState.version]

/-- A successful `try_decrypt_with_state` clears the pending pre-key flag and keeps the remote
identity key, which was present (`TripleRatchet::from_session_state` requires it). -/
theorem tryDecryptWithState_ok {PQC : Type} (C : Crypto) (spqr : Spqr PQ PQC)
    (expected : Option (List (BitVec 8))) (ciphertext : SignalMessage) (msgType : MessageType)
    (coins : BitVec 256) {s s' : SessionState PQ} {p : List (BitVec 8)}
    (h : Mut.exec (SessionState.tryDecryptWithState C spqr expected ciphertext msgType coins) s =
      (.ok p, s')) :
    s'.pendingPreKey = false ∧ s'.remoteIdentity = s.remoteIdentity ∧ s.remoteIdentity.isSome := by
  unfold SessionState.tryDecryptWithState at h
  generalize Mut.exec (TripleRatchet.decrypt C spqr expected ciphertext msgType coins) = D at h
  unfold Mut.exec TripleRatchet.fromSessionState SessionState.takeRatchetState
    SessionState.takePqRatchetState at h
  rcases hr : s.remoteIdentity with _ | k <;> api_simp [hr] at h
  generalize D _ = R at h
  rcases R with ⟨_ | a, t⟩ <;> api_simp [liftE] at h
  obtain ⟨-, rfl⟩ := h
  simp [SessionState.clearUnacknowledgedPreKeyMessage, TripleRatchet.applyToSessionState]

theorem SessionState.tryDecryptFromRecord_ok {PQC : Type} (C : Crypto) (spqr : Spqr PQ PQC)
    (expected : Option (List (BitVec 8))) (ciphertext : SignalMessage) (msgType : MessageType)
    (coins : BitVec 256) {s s' : SessionState PQ} {p : List (BitVec 8)}
    (h : SessionState.tryDecryptFromRecord C spqr expected ciphertext msgType coins s =
      (.ok p, s')) :
    s'.pendingPreKey = false ∧ s'.remoteIdentity = s.remoteIdentity ∧ s.remoteIdentity.isSome := by
  unfold SessionState.tryDecryptFromRecord at h
  split_ifs at h
  · simp at h
  · split at h
    · simp only [Prod.mk.injEq, Except.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      apply tryDecryptWithState_ok C spqr expected ciphertext msgType coins
      assumption
    · simp at h

/-- **A successful record decryption leaves an acknowledged, well-formed current session** with
the same remote identity key as before (which is present). -/
theorem SessionRecord.tryDecryptFromRecord_ok {PQC : Type} (C : Crypto) (spqr : Spqr PQ PQC)
    (expected : Option (List (BitVec 8))) (ciphertext : SignalMessage) (coins : BitVec 256)
    {record record' : SessionRecord PQ} {p : List (BitVec 8)}
    (h : record.tryDecryptFromRecord C spqr expected ciphertext coins = .ok (p, record')) :
    ∃ s₀ s, record.currentSession = some s₀ ∧ record'.currentSession = some s ∧
      s.pendingPreKey = none ∧ s.pendingKyberPreKey = none ∧ s.state.pendingPreKey = false ∧
      s.state.remoteIdentity = s₀.state.remoteIdentity ∧ s₀.state.remoteIdentity.isSome := by
  unfold SessionRecord.tryDecryptFromRecord at h
  split at h
  · simp at h
  · rename_i s₀ _
    split at h
    · rename_i st hst
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have := SessionState.tryDecryptFromRecord_ok C spqr expected ciphertext .whisper coins hst
      exact ⟨s₀, _, ‹_›, rfl, rfl, rfl, this⟩
    · simp at h

omit [Inhabited PQ] in
/-- `OutgoingTripleRatchet::encrypt` succeeds when `spqr::send` does not panic and succeeds, and the
sender chain index is below `u32::MAX`. -/
theorem execOk_encrypt_of {PQC : Type} (C : Crypto) (codec : SignalMessageProtoCodec) (spqr : Spqr PQ PQC)
    (ptext : List (BitVec 8)) (addresses : Option (List (BitVec 8))) (coins : PQC)
    {o : OutgoingTripleRatchet PQ} {pq' : PQ} {salt : HKDF.Salt} {pqMsg : List (BitVec 8)}
    (hnp : spqr.sendPanics o.pqrState coins = false)
    (hsend : spqr.send o.pqrState coins = some (pq', salt, pqMsg))
    (hidx : o.senderChainKey.index ≠ BitVec.allOnes 32) :
    ∃ m o', execOk (OutgoingTripleRatchet.encrypt C codec spqr ptext addresses coins) o =
      .ok (m, o') := by
  have hidx' : o.senderChainKey.index ≠ 4294967295#32 := hidx
  unfold execOk Mut.exec OutgoingTripleRatchet.encrypt
  api_simp [hnp, hsend, liftE, ChainKey.nextChainKey, hidx']

/-! ### `message_decrypt_signal` -/

section decrypt
variable (C : Crypto) (spqr : Spqr PQ PQC) (ser : Addr → Addr → Option (List (BitVec 8)))
  (answers : StoreAnswers PQ E) (ciphertext : SignalMessage) (remote loc : Addr)
  (coins : BitVec 256)

/-- **Call order**: the store calls are always a non-empty prefix of load, trust check
(`Receiving`), save identity, store, all for the remote address. -/
theorem messageDecryptSignal_trace_prefix :
    ∃ k r, (messageDecryptSignal C spqr ser answers ciphertext remote loc coins).2 ≠ [] ∧
      (messageDecryptSignal C spqr ser answers ciphertext remote loc coins).2 <+:
        fullTrace remote k .receiving r := by
  rw [messageDecryptSignal_eq_flat]; exact decryptFlat_prefix ..

/-- **All or nothing**: the call succeeds iff the record was stored. -/
theorem messageDecryptSignal_ok_iff_stored :
    (∃ p, (messageDecryptSignal C spqr ser answers ciphertext remote loc coins).1 = .ok p) ↔
      Stored answers (messageDecryptSignal C spqr ser answers ciphertext remote loc coins).2 := by
  rw [messageDecryptSignal_eq_flat]; exact decryptFlat_ok_iff_stored ..

/-- **On any error, nothing is stored**: no `store_session` call was made, or the store rejected
it. -/
theorem messageDecryptSignal_error_not_stored (e : ApiError Addr E)
    (h : (messageDecryptSignal C spqr ser answers ciphertext remote loc coins).1 = .error e) :
    ¬ Stored answers (messageDecryptSignal C spqr ser answers ciphertext remote loc coins).2 := by
  rw [← messageDecryptSignal_ok_iff_stored, h]; simp

/-- **A successful call** made all four store calls, the trust check said yes and the store
accepted the record. -/
theorem messageDecryptSignal_ok (p : List (BitVec 8))
    (h : (messageDecryptSignal C spqr ser answers ciphertext remote loc coins).1 = .ok p) :
    ∃ k r, (messageDecryptSignal C spqr ser answers ciphertext remote loc coins).2 =
      fullTrace remote k .receiving r ∧ answers.isTrustedIdentity = .ok true ∧
      answers.storeSession = .ok () := by
  rw [messageDecryptSignal_eq_flat] at h ⊢; exact decryptFlat_ok _ _ _ _ _ _ _ _ _ h

/-- **What is stored**: the record a successful `try_decrypt_from_record` produced from the loaded
one, under the remote address. -/
theorem messageDecryptSignal_stored (a : Addr) (r : SessionRecord PQ)
    (h : StoreCall.storeSession a r ∈
      (messageDecryptSignal C spqr ser answers ciphertext remote loc coins).2) :
    a = remote ∧ ∃ record ptext, answers.loadSession = .ok (some record) ∧
      record.tryDecryptFromRecord C spqr (ser remote loc) ciphertext coins = .ok (ptext, r) := by
  rw [messageDecryptSignal_eq_flat] at h; exact decryptFlat_stored _ _ _ _ _ _ _ _ _ _ h

/-- **The stored session is acknowledged and well formed** (`Session.Wf`), whatever was loaded. -/
theorem messageDecryptSignal_stored_wf (a : Addr) (r : SessionRecord PQ)
    (h : StoreCall.storeSession a r ∈
      (messageDecryptSignal C spqr ser answers ciphertext remote loc coins).2) :
    ∃ s, r.currentSession = some s ∧ s.pendingPreKey = none ∧ s.Wf := by
  obtain ⟨-, record, ptext, -, hd⟩ := messageDecryptSignal_stored C spqr ser answers ciphertext remote loc coins a r h
  obtain ⟨s₀, s, -, hs, hp, -, hst, -⟩ := SessionRecord.tryDecryptFromRecord_ok C spqr _ _ _ hd
  exact ⟨s, hs, hp, by simp [Session.Wf, hp, hst]⟩

/-- **The API's own `expect`s never panic**: a panic comes from `try_decrypt_from_record`. -/
theorem messageDecryptSignal_panic
    (h : (messageDecryptSignal C spqr ser answers ciphertext remote loc coins).1 =
      .error .panic) :
    ∃ record, answers.loadSession = .ok (some record) ∧
      record.tryDecryptFromRecord C spqr (ser remote loc) ciphertext coins = .error .panic := by
  rw [messageDecryptSignal_eq_flat] at h
  unfold decryptFlat at h
  repeat' split at h
  all_goals simp at h
  · subst h; exact ⟨_, ‹_›, ‹_›⟩
  · rename_i hd _ hnone
    obtain ⟨s₀, s, -, hs, -, -, -, hk, hsome⟩ := SessionRecord.tryDecryptFromRecord_ok C spqr _ _ _ hd
    simp [hs, hk] at hnone
    simp [hnone] at hsome

/-- **A panic is always `ApiError.panic`**: the result is never `ApiError.protocol` of the session
model's panic. -/
theorem messageDecryptSignal_ne_protocol_panic :
    (messageDecryptSignal C spqr ser answers ciphertext remote loc coins).1 ≠
      .error (.protocol .panic) := by
  rw [messageDecryptSignal_eq_flat]
  unfold decryptFlat
  repeat' split
  all_goals simp

/-- **Success conditions**: a loaded record that decrypts, a trusted identity and a store that
accepts give the plaintext, with the full trace. -/
theorem messageDecryptSignal_ok_of {record record' : SessionRecord PQ} {p : List (BitVec 8)}
    {c : IdentityChange}
    (hl : answers.loadSession = .ok (some record))
    (hd : record.tryDecryptFromRecord C spqr (ser remote loc) ciphertext coins = .ok (p, record'))
    (ht : answers.isTrustedIdentity = .ok true) (hsv : answers.saveIdentity = .ok c)
    (hst : answers.storeSession = .ok ()) :
    ∃ k, messageDecryptSignal C spqr ser answers ciphertext remote loc coins =
      (.ok p, fullTrace remote k .receiving record') := by
  obtain ⟨s₀, s, -, hs, -, -, -, hk, hsome⟩ := SessionRecord.tryDecryptFromRecord_ok C spqr _ _ _ hd
  obtain ⟨k, hk'⟩ := Option.isSome_iff_exists.mp hsome
  refine ⟨k, ?_⟩
  rw [messageDecryptSignal_eq_flat]
  simp [decryptFlat, hl, hd, hs, hk, hk', ht, hsv, hst, fullTrace]

end decrypt

/-! ### `message_encrypt` -/

section encryptApi
variable (C : Crypto) (codec : SignalMessageProtoCodec) (spqr : Spqr PQ PQC)
  (ser : Addr → Addr → Option (List (BitVec 8))) (answers : StoreAnswers PQ E)
  (ptext : List (BitVec 8)) (remote loc : Addr) (now : SystemTime) (coins : PQC)

/-- **Call order**: the store calls are always a non-empty prefix of load, trust check
(`Sending`), save identity, store, all for the remote address. -/
theorem messageEncrypt_trace_prefix :
    ∃ k r, (messageEncrypt C codec spqr ser answers ptext remote loc now coins).2 ≠ [] ∧
      (messageEncrypt C codec spqr ser answers ptext remote loc now coins).2 <+:
        fullTrace remote k .sending r := by
  rw [messageEncrypt_eq_flat]; exact encryptFlat_prefix ..

/-- **All or nothing**: the call succeeds iff the record was stored. -/
theorem messageEncrypt_ok_iff_stored :
    (∃ m, (messageEncrypt C codec spqr ser answers ptext remote loc now coins).1 =
      .ok m) ↔
      Stored answers (messageEncrypt C codec spqr ser answers ptext remote loc now coins).2 := by
  rw [messageEncrypt_eq_flat]; exact encryptFlat_ok_iff_stored ..

/-- **On any error, nothing is stored**: no `store_session` call was made, or the store rejected
it. -/
theorem messageEncrypt_error_not_stored (e : ApiError Addr E)
    (h : (messageEncrypt C codec spqr ser answers ptext remote loc now coins).1 =
      .error e) :
    ¬ Stored answers (messageEncrypt C codec spqr ser answers ptext remote loc now coins).2 := by
  rw [← messageEncrypt_ok_iff_stored, h]; simp

/-- **A successful call** made all four store calls, the trust check said yes and the store
accepted the record. -/
theorem messageEncrypt_ok (m : CiphertextMessage)
    (h : (messageEncrypt C codec spqr ser answers ptext remote loc now coins).1 = .ok m) :
    ∃ k r, (messageEncrypt C codec spqr ser answers ptext remote loc now coins).2 =
      fullTrace remote k .sending r ∧ answers.isTrustedIdentity = .ok true ∧
      answers.storeSession = .ok () := by
  rw [messageEncrypt_eq_flat] at h ⊢; exact encryptFlat_ok _ _ _ _ _ _ _ _ _ _ m h

/-- **What is stored**: the loaded session with only its session state replaced, by the state left
by `from_session_state` (SPQR state moved out) with the ratchet's new sender chain key and SPQR
state written back (`apply_to_session_state`). The other `SessionStructure` fields, in particular
the pending pre-key, are unchanged. -/
theorem messageEncrypt_stored (a : Addr) (r : SessionRecord PQ)
    (h : StoreCall.storeSession a r ∈
      (messageEncrypt C codec spqr ser answers ptext remote loc now coins).2) :
    a = remote ∧ ∃ (record : SessionRecord PQ) (session : Session PQ)
      (otr' : OutgoingTripleRatchet PQ), answers.loadSession = .ok (some record) ∧
      record.currentSession = some session ∧
      r = ⟨some { session with
        state := otr'.applyToSessionState { session.state with pqRatchetState := default } }⟩ := by
  rw [messageEncrypt_eq_flat] at h
  obtain ⟨ha, record, session, otr, taken, m, otr', hl, hc, hf, -, rfl⟩ :=
    encryptFlat_stored _ _ _ _ _ _ _ _ _ _ a r h
  obtain ⟨rfl, -⟩ := execOk_fromSessionState hf
  exact ⟨ha, record, session, otr', hl, hc, rfl⟩

/-- **Well-formedness is preserved**: if the loaded session is well formed, so is the stored one. -/
theorem messageEncrypt_stored_wf (a : Addr) (r : SessionRecord PQ) (record : SessionRecord PQ)
    (hl : answers.loadSession = .ok (some record))
    (hwf : ∀ s, record.currentSession = some s → s.Wf)
    (h : StoreCall.storeSession a r ∈
      (messageEncrypt C codec spqr ser answers ptext remote loc now coins).2) :
    ∃ s, r.currentSession = some s ∧ s.Wf := by
  obtain ⟨-, record', session, otr', hl', hc, rfl⟩ :=
    messageEncrypt_stored C codec spqr ser answers ptext remote loc now coins a r h
  rw [hl] at hl'
  cases hl'
  have := hwf session hc
  exact ⟨_, rfl, by simpa [Session.Wf, OutgoingTripleRatchet.applyToSessionState] using this⟩

/-- **Where a panic comes from**: the `SystemTime` overflow of an unacknowledged session's
timestamp (`state/session.rs:559`) or expiry (`session_management.rs:82`), or the session model's
`encrypt` (the sender chain index at `u32::MAX`). The API's own `expect` (`:71–73`) never panics. -/
theorem messageEncrypt_panic
    (h : (messageEncrypt C codec spqr ser answers ptext remote loc now coins).1 =
      .error .panic) :
    ∃ record session, answers.loadSession = .ok (some record) ∧
      record.currentSession = some session ∧
      ((∃ items, session.pendingPreKey = some items ∧
          ((SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat).bind
            (·.checkedAddSecs maxUnacknowledgedSessionAge)) = none) ∨
        ∃ otr addresses,
          execOk (OutgoingTripleRatchet.encrypt C codec spqr ptext addresses coins) otr =
            .error .panic) := by
  rw [messageEncrypt_eq_flat] at h
  unfold encryptFlat at h
  repeat' split at h
  all_goals simp at h
  · subst h; exact absurd ‹_› execOk_fromSessionState_ne_panic
  · rename_i hf _ hnone
    obtain ⟨rfl, hsome⟩ := execOk_fromSessionState hf
    simp only at hnone
    simp [hnone] at hsome
  · rename_i _ record hl _ session hc _ otr taken hf _ k hk _ e hw
    subst h
    refine ⟨record, session, hl, hc, ?_⟩
    unfold wrapFlat at hw
    repeat' split at hw
    all_goals simp at hw
    all_goals first
      | (subst hw; exact .inr ⟨_, _, ‹_›⟩)
      | exact .inl ⟨_, ‹_›, by simp [*]⟩

/-- **A panic is always `ApiError.panic`**: the result is never `ApiError.protocol` of the session
model's panic. -/
theorem messageEncrypt_ne_protocol_panic :
    (messageEncrypt C codec spqr ser answers ptext remote loc now coins).1 ≠
      .error (.protocol .panic) := by
  rw [messageEncrypt_eq_flat]
  unfold encryptFlat
  repeat' split
  all_goals simp
  rename_i hw
  unfold wrapFlat at hw
  repeat' split at hw
  all_goals simp at hw
  all_goals (subst hw; simp)

/-- **Success conditions**: a loaded session that `from_session_state` accepts (sender chain,
version below 256, remote identity key), whose pending pre-key (if any) has a representable,
unexpired timestamp, an `spqr::send` that does not panic and succeeds, a sender chain index below
`u32::MAX`, a trusted identity and a store that accepts give a message, with the full trace. -/
theorem messageEncrypt_ok_of {session : Session PQ} {sc : SenderChain} {k : IdentityKey}
    {pq' : PQ} {salt : HKDF.Salt} {pqMsg : List (BitVec 8)} {c : IdentityChange}
    (hl : answers.loadSession = .ok (some ⟨some session⟩))
    (hs : session.state.senderChain = some sc) (hv : session.state.version.toNat < 256)
    (hr : session.state.remoteIdentity = some k)
    (hpk : ∀ items, session.pendingPreKey = some items → ∃ expiry,
      (SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat).bind
        (·.checkedAddSecs maxUnacknowledgedSessionAge) = some expiry ∧ expiry.lt now = false)
    (hnp : spqr.sendPanics session.state.pqRatchetState coins = false)
    (hsend : spqr.send session.state.pqRatchetState coins = some (pq', salt, pqMsg))
    (hidx : sc.chainKey.index ≠ BitVec.allOnes 32)
    (ht : answers.isTrustedIdentity = .ok true) (hsv : answers.saveIdentity = .ok c)
    (hst : answers.storeSession = .ok ()) :
    ∃ m r, messageEncrypt C codec spqr ser answers ptext remote loc now coins =
      (.ok m, fullTrace remote k .sending r) := by
  rw [messageEncrypt_eq_flat]
  simp only [encryptFlat, hl, execOk_fromSessionState_of hs hv hr, hr]
  rcases hp : session.pendingPreKey with _ | items
  · obtain ⟨m, o', he⟩ := execOk_encrypt_of C codec spqr ptext none coins
      (o := ⟨sc.ratchetKey, sc.chainKey, session.state.previousCounter, session.state.pqRatchetState,
        BitVec.setWidth 8 session.state.version, session.state.localIdentity, k⟩) hnp hsend hidx
    simp [wrapFlat, hp, he, ht, hsv, hst, fullTrace]
  · obtain ⟨expiry, hexp, hlt⟩ := hpk items hp
    obtain ⟨m, o', he⟩ := execOk_encrypt_of C codec spqr ptext (ser loc remote) coins
      (o := ⟨sc.ratchetKey, sc.chainKey, session.state.previousCounter, session.state.pqRatchetState,
        BitVec.setWidth 8 session.state.version, session.state.localIdentity, k⟩) hnp hsend hidx
    rcases h1 : SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat with _ | ts
    · simp [h1] at hexp
    · simp only [h1, Option.bind_some] at hexp
      simp [wrapFlat, hp, h1, hexp, hlt, he, ht, hsv, hst, fullTrace]

end encryptApi

/-! ### Non-vacuity -/

/-- An all-zero 32-byte public key (the model is generic in key bytes; any value would do). -/
def zeroKey : PublicKey := ⟨List.Vector.replicate 32 0⟩

/-- A version-4 session with a sender chain at index 0 and a remote identity key, with the given
pending pre-key (`none`: acknowledged), well formed (`exampleSession_wf`). `PQ = Unit`. -/
def exampleSession (pending : Option PendingPreKey) : Session Unit :=
  { state :=
      { sessionVersion := 4, localIdentity := ⟨zeroKey⟩, remoteIdentity := some ⟨zeroKey⟩,
        rootKey := 0, previousCounter := 0,
        senderChain := some ⟨⟨zeroKey, ⟨zeroKey.bytes⟩⟩, ⟨0, 0⟩⟩, receiverChains := [],
        pendingPreKey := pending.isSome, pqRatchetState := () }
    pendingPreKey := pending, pendingKyberPreKey := none, localRegistrationId := 1,
    remoteRegistrationId := 2, aliceBaseKey := [] }

theorem exampleSession_wf (pending : Option PendingPreKey) : (exampleSession pending).Wf := rfl

/-- An `Spqr` whose `send` always succeeds (`PQ = PQC = Unit`, no salt, empty message). -/
def exampleSpqr : Spqr Unit Unit :=
  ⟨fun _ _ => (), fun _ _ => some ((), none, []), fun _ _ => .ok ((), none), fun _ _ => false,
    fun _ _ => false⟩

/-- Store answers: `exampleSession pending` is loaded, the identity is trusted, every call
succeeds. -/
def exampleAnswers (E : Type) (pending : Option PendingPreKey) : StoreAnswers Unit E :=
  ⟨.ok (some ⟨some (exampleSession pending)⟩), .ok true, .ok .newOrUnchanged, .ok ()⟩

/-- **Non-vacuity, acknowledged session**: for all primitives, codecs, addresses, plaintexts and
times, `message_encrypt` succeeds with the full trace (a bare `SignalMessage`). -/
theorem messageEncrypt_nonvacuous (C : Crypto) (codec : SignalMessageProtoCodec)
    (ser : Addr → Addr → Option (List (BitVec 8)))
    (ptext : List (BitVec 8)) (remote loc : Addr) (now : SystemTime) :
    ∃ m k r, messageEncrypt C codec exampleSpqr ser (exampleAnswers E none) ptext
      remote loc now () = (.ok m, fullTrace remote k .sending r) := by
  obtain ⟨m, r, h⟩ := messageEncrypt_ok_of C codec exampleSpqr ser
    (exampleAnswers E none) ptext remote loc now () (session := exampleSession none) (k := ⟨zeroKey⟩)
    (sc := ⟨⟨zeroKey, ⟨zeroKey.bytes⟩⟩, ⟨0, 0⟩⟩) (pq' := ()) (salt := none) (pqMsg := [])
    (c := .newOrUnchanged) rfl rfl (by decide) rfl (by simp [exampleSession]) rfl rfl (by decide) rfl rfl
    rfl
  exact ⟨m, _, r, h⟩

/-- **Non-vacuity, unacknowledged session** (the `PreKeySignalMessage` branch): a pending pre-key
with timestamp 0 is not stale at the Unix epoch, and `message_encrypt` succeeds with the full
trace. -/
theorem messageEncrypt_nonvacuous_preKey (C : Crypto) (codec : SignalMessageProtoCodec)
    (ser : Addr → Addr → Option (List (BitVec 8)))
    (ptext : List (BitVec 8)) (remote loc : Addr) :
    ∃ m k r, messageEncrypt C codec exampleSpqr ser
      (exampleAnswers E (some ⟨none, 0, zeroKey, 0⟩)) ptext remote loc SystemTime.unixEpoch () =
        (.ok m, fullTrace remote k .sending r) := by
  obtain ⟨m, r, h⟩ := messageEncrypt_ok_of C codec exampleSpqr ser
    (exampleAnswers E (some ⟨none, 0, zeroKey, 0⟩)) ptext remote loc SystemTime.unixEpoch ()
    (session := exampleSession (some ⟨none, 0, zeroKey, 0⟩)) (k := ⟨zeroKey⟩)
    (sc := ⟨⟨zeroKey, ⟨zeroKey.bytes⟩⟩, ⟨0, 0⟩⟩) (pq' := ()) (salt := none) (pqMsg := [])
    (c := .newOrUnchanged) rfl rfl (by decide) rfl
    (by
      intro items h
      simp only [exampleSession, Option.some.injEq] at h
      subst h
      exact ⟨⟨2592000, 0⟩, by decide, by decide⟩)
    rfl rfl (by decide) rfl rfl rfl
  exact ⟨m, _, r, h⟩

end CryptoGames.LibsignalSessionApi
