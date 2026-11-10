/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Refinement.Composed.Cli.SDet.Defs
public import Symbolic.Proofs.Refinement.Composed.Cli.SDet.FilesOfAlg
import Symbolic.Proofs.Refinement.Composed.Cli.ParD3OverlapGates
import Symbolic.Proofs.Refinement.Composed.Cli.ParD7PureGates
import Symbolic.Proofs.Refinement.Composed.Cli.SDet.ModelCongrD3
import Symbolic.Proofs.Refinement.Composed.Cli.SDet.ModelCongrD7
import Symbolic.Proofs.Refinement.Composed.Cli.SDet.XIndep
import Symbolic.Proofs.Refinement.Composed.Cli.Transfer

/-!
# Model Congruence and Determinism Assembly

Defines `SDetBridges`, proves congruence of the PQXDH CLI models under `PqPartyEquiv`, and
derives `PqModelPost` from `Draft.PqModelRel` (`sdet_of_bridges`).
-/

@[expose] public section

set_option autoImplicit false

namespace DY.Libsignal.Composed.Refinement.Cli.SDet

open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open CryptoGames.LibsignalSession (GhostState SessionState OutgoingTripleRatchet TripleRatchet
  SignalMessage MessageType IdentityKey)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.E2E (PreKeyBundleFields PreKeyMessageFields UnreachedPqxdhPrimitives PEParams RecordExtras initiateTapeLen
  wireWhisper wirePrekey initiateState recvPrekeyState pqxdhSpqrSession pqxdhSessionParams firstMessageBody)
open CryptoVerification.SignalSession

structure SDetBridges : Prop where
  init_send_false : ∀ {P : PEParams} {st₀ st₁ : PqParty} {b₀ : PreKeyBundleFields}
      {t₀ : List.Vector (BitVec 8) initiateTapeLen} {m₁ : HwBytes} {r₁ : List.Vector (BitVec 8) 64},
    InputsEquiv (pqInitInputs P st₀ b₀ t₀) (pqSendInputs P st₁ m₁ r₁) → False
  init_recv_false : ∀ {P : PEParams} {st₀ st₁ : PqParty} {b₀ : PreKeyBundleFields}
      {t₀ : List.Vector (BitVec 8) initiateTapeLen} {c₁ : HwBytes} {rc₁ : BitVec 256},
    InputsEquiv (pqInitInputs P st₀ b₀ t₀) (pqRecvInputs P st₁ c₁ rc₁) → False
  send_recv_false : ∀ {P : PEParams} {st₀ st₁ : PqParty} {m₀ : HwBytes}
      {r₀ : List.Vector (BitVec 8) 64} {c₁ : HwBytes} {rc₁ : BitVec 256},
    InputsEquiv (pqSendInputs P st₀ m₀ r₀) (pqRecvInputs P st₁ c₁ rc₁) → False
  whisper_prekey_false : ∀ {P : PEParams} {st₀ st₁ : PqParty} {body₀ : HwBytes}
      {rc₀ : BitVec 256} {m₁ : PreKeyMessageFields} {rc₁ : BitVec 256},
    InputsEquiv (pqRecvInputs P st₀ (wireWhisper :: body₀) rc₀)
                (pqRecvInputs P st₁ (wirePrekey :: m₁.bytes) rc₁) → False
  whisper_other_false : ∀ {P : PEParams} {st₀ st₁ : PqParty} {body₀ : HwBytes}
      {rc₀ : BitVec 256} {c₁ : HwBytes} {rc₁ : BitVec 256},
    c₁.head? ≠ some wireWhisper →
    InputsEquiv (pqRecvInputs P st₀ (wireWhisper :: body₀) rc₀)
                (pqRecvInputs P st₁ c₁ rc₁) → False
  prekey_other_false : ∀ {P : PEParams} {st₀ st₁ : PqParty} {m₀ : PreKeyMessageFields}
      {rc₀ : BitVec 256} {c₁ : HwBytes} {rc₁ : BitVec 256},
    c₁.head? ≠ some wirePrekey →
    InputsEquiv (pqRecvInputs P st₀ (wirePrekey :: m₀.bytes) rc₀)
                (pqRecvInputs P st₁ c₁ rc₁) → False
  init_extract : ∀ {P : PEParams} {st₀ st₁ : PqParty} {b₀ b₁ : PreKeyBundleFields}
      {t₀ t₁ : List.Vector (BitVec 8) initiateTapeLen},
    InputsEquiv (pqInitInputs P st₀ b₀ t₀) (pqInitInputs P st₁ b₁ t₁) →
    b₀ = b₁ ∧ t₀ = t₁ ∧ ∀ p, filesOf (encodeDir P st₀) p = filesOf (encodeDir P st₁) p
  send_extract : ∀ {P : PEParams} {st₀ st₁ : PqParty} {m₀ m₁ : HwBytes}
      {r₀ r₁ : List.Vector (BitVec 8) 64},
    InputsEquiv (pqSendInputs P st₀ m₀ r₀) (pqSendInputs P st₁ m₁ r₁) →
    m₀ = m₁ ∧ r₀ = r₁ ∧ ∀ p, filesOf (encodeDir P st₀) p = filesOf (encodeDir P st₁) p
  whisper_extract : ∀ {P : PEParams} {st₀ st₁ : PqParty} {body₀ body₁ : HwBytes}
      {rc₀ rc₁ : BitVec 256},
    InputsEquiv (pqRecvInputs P st₀ (wireWhisper :: body₀) rc₀)
                (pqRecvInputs P st₁ (wireWhisper :: body₁) rc₁) →
    body₀ = body₁ ∧ rc₀ = rc₁ ∧ ∀ p, filesOf (encodeDir P st₀) p = filesOf (encodeDir P st₁) p
  prekey_extract : ∀ {P : PEParams} {st₀ st₁ : PqParty} {m₀ m₁ : PreKeyMessageFields}
      {rc₀ rc₁ : BitVec 256},
    m₀.inner.length + 2048 < 2 ^ 32 →
    m₁.inner.length + 2048 < 2 ^ 32 →
    InputsEquiv (pqRecvInputs P st₀ (wirePrekey :: m₀.bytes) rc₀)
                (pqRecvInputs P st₁ (wirePrekey :: m₁.bytes) rc₁) →
    m₀ = m₁ ∧ rc₀ = rc₁ ∧ ∀ p, filesOf (encodeDir P st₀) p = filesOf (encodeDir P st₁) p
  party_equiv_of_files : ∀ {P : PEParams} {st st' : PqParty},
    PqxdhPartyInSpecDomain P st → PqxdhPartyInSpecDomain P st' →
    (∀ p, filesOf (encodeDir P st) p = filesOf (encodeDir P st') p) →
    PqPartyEquiv st st'
  files_of_party_equiv : ∀ (P : PEParams) {st st' : PqParty},
    PqPartyEquiv st st' → ∀ p, filesOf (encodeDir P st) p = filesOf (encodeDir P st') p

/-! ## Basic congruence for `trusts`, `PqSessionMatches`, and store maps -/

theorem PqPartyEquiv.trusts_eq {st st' : PqParty} (h : PqPartyEquiv st st') (k : IdentityKey) :
    st.trusts k = st'.trusts k := by
  unfold PqParty.trusts
  rw [h.peerId_eq]

theorem PqSessionEquiv.matches_iff {x x' : RecordExtras} {g g' : GhostState HwBytes}
    (h : PqSessionEquiv x g x' g') (m : PreKeyMessageFields) :
    PqSessionMatches x g m ↔ PqSessionMatches x' g' m := by
  unfold PqSessionMatches
  rw [h.aliceBase_eq, h.session_eq]

private theorem map_fst_assoc_update {α : Type} (l : List (BitVec 32 × α))
    (j : BitVec 32) (f : α → α) :
    ((l.map fun (i, v) => if i = j then (i, f v) else (i, v)).map (·.1)) = l.map (·.1) := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨i, v⟩
    simp only [List.map_cons]
    by_cases hij : i = j <;> simp [hij, ih]

private theorem lookup_assoc_update {α : Type} (l : List (BitVec 32 × α))
    (j : BitVec 32) (f : α → α) (id : BitVec 32) :
    List.lookup id (l.map fun (i, v) => if i = j then (i, f v) else (i, v)) =
      if id = j then (List.lookup id l).map f else List.lookup id l := by
  induction l with
  | nil => simp
  | cons p ps ih =>
    rcases p with ⟨i, v⟩
    by_cases hid : id = i
    · subst hid
      by_cases hij : id = j <;> simp [List.lookup, hij]
    · have hbeq : (id == i) = false := beq_false_of_ne hid
      cases hij : decide (i = j)
      · have hne : i ≠ j := of_decide_eq_false hij
        simp [List.lookup, hne, hbeq, ih]
      · have heq : i = j := of_decide_eq_true hij
        subst heq
        simp [List.lookup, hid, hbeq, ih]

theorem keysFor_eq_of_pqPartyEquiv {st st' : PqParty} (h : PqPartyEquiv st st') (m : PreKeyMessageFields) :
    preKeysNamedBy st m = preKeysNamedBy st' m := by
  simp only [preKeysNamedBy, h.signed_lookup, h.kyberOneTime_lookup, h.kyberLastResort_lookup,
    h.oneTime_lookup]

private theorem markKyberUsed_lastResort_equiv {st st' : PqParty}
    (h : PqPartyEquiv st st') (m : PreKeyMessageFields) :
    PqPartyEquiv
      { st with kyberLastResort := st.kyberLastResort.map fun (i, k, s) =>
          if i = m.kpkId then (i, k, s ++ [(m.spkId, m.baseKey)]) else (i, k, s) }
      { st' with kyberLastResort := st'.kyberLastResort.map fun (i, k, s) =>
          if i = m.kpkId then (i, k, s ++ [(m.spkId, m.baseKey)]) else (i, k, s) } := by
  let f : PqKyberKey × List (BitVec 32 × List.Vector (BitVec 8) 32) →
      PqKyberKey × List (BitVec 32 × List.Vector (BitVec 8) 32) :=
    fun v => (v.1, v.2 ++ [(m.spkId, m.baseKey)])
  have hfn : (fun (x : BitVec 32 × PqKyberKey × List (BitVec 32 × List.Vector (BitVec 8) 32)) =>
      match x with | (i, k, s) => if i = m.kpkId then (i, k, s ++ [(m.spkId, m.baseKey)]) else (i, k, s)) =
      (fun (i, v) => if i = m.kpkId then (i, f v) else (i, v)) := by
    funext ⟨i, k0, s0⟩; rfl
  exact
    { party_eq := h.party_eq
      me_eq := h.me_eq
      peerId_eq := h.peerId_eq
      session_rel := h.session_rel
      signed_lookup := h.signed_lookup
      oneTime_lookup := h.oneTime_lookup
      kyberOneTime_lookup := h.kyberOneTime_lookup
      kyberLastResort_lookup := fun id => by
        dsimp only
        rw [hfn, lookup_assoc_update, lookup_assoc_update, h.kyberLastResort_lookup id]
      signed_nodup := h.signed_nodup
      oneTime_nodup := h.oneTime_nodup
      kyberOneTime_nodup := h.kyberOneTime_nodup
      kyberLastResort_nodup := by
        dsimp only
        rw [hfn, map_fst_assoc_update, map_fst_assoc_update]
        exact h.kyberLastResort_nodup }

theorem markKyberUsed_congr {st st' : PqParty} (h : PqPartyEquiv st st') (m : PreKeyMessageFields) :
    Option.Rel PqPartyEquiv (markKyberUsed st m) (markKyberUsed st' m) := by
  unfold markKyberUsed
  have hkot := h.kyberOneTime_lookup m.kpkId
  cases h1 : List.lookup m.kpkId st.kyberOneTime with
  | none =>
    rw [h1] at hkot
    rw [← hkot]
    have hklr := h.kyberLastResort_lookup m.kpkId
    cases h2 : List.lookup m.kpkId st.kyberLastResort with
    | none =>
      rw [h2] at hklr
      rw [← hklr]
      exact Option.Rel.none
    | some ks =>
      rcases ks with ⟨k, seen⟩
      rw [h2] at hklr
      rw [← hklr]
      dsimp only
      by_cases hmem : 37 * seen.length > fileCapBytes ∨ (m.spkId, m.baseKey) ∈ seen
      · simp only [hmem, ↓reduceIte]
        exact Option.Rel.none
      · simp only [hmem, ↓reduceIte]
        exact Option.Rel.some (markKyberUsed_lastResort_equiv h m)
  | some ok =>
    rw [h1] at hkot
    rw [← hkot]
    cases ok with
    | none =>
      have hklr := h.kyberLastResort_lookup m.kpkId
      cases h2 : List.lookup m.kpkId st.kyberLastResort with
      | none =>
        rw [h2] at hklr
        rw [← hklr]
        exact Option.Rel.none
      | some ks =>
        rcases ks with ⟨k, seen⟩
        rw [h2] at hklr
        rw [← hklr]
        dsimp only
        by_cases hmem : 37 * seen.length > fileCapBytes ∨ (m.spkId, m.baseKey) ∈ seen
        · simp only [hmem, ↓reduceIte]
          exact Option.Rel.none
        · simp only [hmem, ↓reduceIte]
          exact Option.Rel.some (markKyberUsed_lastResort_equiv h m)
    | some _ =>
      let f : Option PqKyberKey → Option PqKyberKey := fun _ => none
      have hfn : (fun (x : BitVec 32 × Option PqKyberKey) =>
          match x with | (i, k) => if i = m.kpkId then (i, none) else (i, k)) =
          (fun (i, v) => if i = m.kpkId then (i, f v) else (i, v)) := by
        funext ⟨i, k0⟩; rfl
      refine Option.Rel.some ?_
      exact
        { party_eq := h.party_eq
          me_eq := h.me_eq
          peerId_eq := h.peerId_eq
          session_rel := h.session_rel
          signed_lookup := h.signed_lookup
          oneTime_lookup := h.oneTime_lookup
          kyberOneTime_lookup := fun id => by
            dsimp only
            rw [hfn, lookup_assoc_update, lookup_assoc_update, h.kyberOneTime_lookup id]
          kyberLastResort_lookup := h.kyberLastResort_lookup
          signed_nodup := h.signed_nodup
          oneTime_nodup := h.oneTime_nodup
          kyberOneTime_nodup := by
            dsimp only
            rw [hfn, map_fst_assoc_update, map_fst_assoc_update]
            exact h.kyberOneTime_nodup
          kyberLastResort_nodup := h.kyberLastResort_nodup }

theorem removeOpk_congr {st st' : PqParty} (h : PqPartyEquiv st st') (m : PreKeyMessageFields) :
    PqPartyEquiv (removeOpk st m) (removeOpk st' m) := by
  unfold removeOpk
  cases m.opkId with
  | none => exact h
  | some j =>
    let f : Option (List.Vector (BitVec 8) 32) → Option (List.Vector (BitVec 8) 32) := fun _ => none
    have hfn : (fun (x : BitVec 32 × Option (List.Vector (BitVec 8) 32)) =>
        match x with | (i, k) => if i = j then (i, none) else (i, k)) =
        (fun (i, v) => if i = j then (i, f v) else (i, v)) := by
      funext ⟨i, k0⟩; rfl
    exact
      { party_eq := h.party_eq
        me_eq := h.me_eq
        peerId_eq := h.peerId_eq
        session_rel := h.session_rel
        signed_lookup := h.signed_lookup
        oneTime_lookup := fun id => by
          dsimp only
          rw [hfn, lookup_assoc_update, lookup_assoc_update, h.oneTime_lookup id]
        kyberOneTime_lookup := h.kyberOneTime_lookup
        kyberLastResort_lookup := h.kyberLastResort_lookup
        signed_nodup := h.signed_nodup
        oneTime_nodup := by
          dsimp only
          rw [hfn, map_fst_assoc_update, map_fst_assoc_update]
          exact h.oneTime_nodup
        kyberOneTime_nodup := h.kyberOneTime_nodup
        kyberLastResort_nodup := h.kyberLastResort_nodup }

private theorem pqPartyEquiv_with_peer_session {st₀ st₁ : PqParty}
    (hst : PqPartyEquiv st₀ st₁) (k : IdentityKey)
    {x₀ x₁ : RecordExtras} {g₀ g₁ : GhostState HwBytes}
    (hse : PqSessionEquiv x₀ g₀ x₁ g₁) :
    PqPartyEquiv { st₀ with peerId := some k, session := some (x₀, g₀) }
                 { st₁ with peerId := some k, session := some (x₁, g₁) } where
  party_eq := hst.party_eq
  me_eq := hst.me_eq
  peerId_eq := rfl
  session_rel := Option.Rel.some hse
  signed_lookup := hst.signed_lookup
  oneTime_lookup := hst.oneTime_lookup
  kyberOneTime_lookup := hst.kyberOneTime_lookup
  kyberLastResort_lookup := hst.kyberLastResort_lookup
  signed_nodup := hst.signed_nodup
  oneTime_nodup := hst.oneTime_nodup
  kyberOneTime_nodup := hst.kyberOneTime_nodup
  kyberLastResort_nodup := hst.kyberLastResort_nodup

/-! ## `pendingPreKey` invariants across `messageEncrypt` and `tryDecryptFromRecord` -/

private theorem fromSessionState_pendingPreKey {PQ : Type} [Inhabited PQ]
    (record taken : SessionState PQ) (o : OutgoingTripleRatchet PQ)
    (h : CryptoGames.LibsignalSession.Mut.exec OutgoingTripleRatchet.fromSessionState record =
      (.ok o, taken)) :
    taken.pendingPreKey = record.pendingPreKey := by
  unfold OutgoingTripleRatchet.fromSessionState SessionState.takePqRatchetState
    CryptoGames.LibsignalSession.Mut.exec at h
  dsimp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.run, ExceptT.bindCont,
    get, getThe, MonadStateOf.get, StateT.get,
    modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    StateT.bind, StateT.pure, StateT.run, pure, ExceptT.pure,
    throw, throwThe, MonadExceptOf.throw,
    liftM, monadLift, MonadLift.monadLift, ExceptT.lift, Functor.map, StateT.map] at h
  cases hsc : record.senderChain with
  | none =>
    rw [hsc] at h
    dsimp only [StateT.pure, pure] at h
    cases h
  | some sc =>
    rw [hsc] at h
    dsimp only [StateT.bind, StateT.map, StateT.modifyGet, StateT.get, StateT.pure,
      ExceptT.bindCont, bind, pure] at h
    split at h
    · dsimp only [StateT.bind, StateT.pure, ExceptT.bindCont, bind, pure] at h
      cases h
    · cases hrm : record.remoteIdentity with
      | none =>
        rw [hrm] at h
        dsimp only [StateT.pure, pure] at h
        cases h
      | some remote =>
        rw [hrm] at h
        dsimp only [StateT.pure, pure] at h
        cases h
        rfl

private theorem messageEncrypt_pendingPreKey {PQ PQC : Type} [Inhabited PQ]
    (C : CryptoGames.LibsignalSession.Crypto) (codec : CryptoGames.LibsignalSession.SignalMessageProtoCodec)
    (spqr : CryptoGames.LibsignalSession.Spqr PQ PQC)
    (addresses : Option (List (BitVec 8))) (ptext : List (BitVec 8)) (coins : PQC)
    (record s : SessionState PQ) (msg : SignalMessage)
    (h : SessionState.messageEncrypt C codec spqr addresses ptext coins record = (.ok msg, s)) :
    s.pendingPreKey = record.pendingPreKey := by
  unfold SessionState.messageEncrypt at h
  cases hf : CryptoGames.LibsignalSession.Mut.exec OutgoingTripleRatchet.fromSessionState record with
  | mk r taken =>
    rw [hf] at h
    cases r with
    | error _ => cases h
    | ok session =>
      dsimp only at h
      cases he : CryptoGames.LibsignalSession.Mut.exec
          (OutgoingTripleRatchet.encrypt C codec spqr ptext
            (record.encryptAddresses addresses) coins) session with
      | mk r2 session2 =>
        rw [he] at h
        cases r2 with
        | error _ => cases h
        | ok message =>
          cases h
          exact fromSessionState_pendingPreKey record taken session hf

private theorem tryDecryptFromRecord_pendingPreKey {PQ PQC : Type} [Inhabited PQ]
    (C : CryptoGames.LibsignalSession.Crypto) (spqr : CryptoGames.LibsignalSession.Spqr PQ PQC)
    (expected : Option (List (BitVec 8))) (ciphertext : SignalMessage) (msgType : MessageType)
    (coins : BitVec 256) (record s : SessionState PQ) (pt : List (BitVec 8))
    (h : SessionState.tryDecryptFromRecord C spqr expected ciphertext msgType coins record =
      (.ok pt, s)) :
    s.pendingPreKey = false := by
  unfold SessionState.tryDecryptFromRecord at h
  split at h
  · cases h
  · cases hd : CryptoGames.LibsignalSession.Mut.exec
        (SessionState.tryDecryptWithState C spqr expected ciphertext msgType coins) record with
    | mk r updated =>
      rw [hd] at h
      cases r with
      | error _ => cases h
      | ok ptext =>
        cases h
        unfold SessionState.tryDecryptWithState CryptoGames.LibsignalSession.Mut.exec at hd
        dsimp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.run, StateT.run, StateT.bind] at hd
        cases hf : TripleRatchet.fromSessionState record with
        | mk rf st1 =>
          rw [hf] at hd
          cases rf with
          | error _ => cases hd
          | ok tr0 =>
            dsimp only [ExceptT.bindCont] at hd
            cases hdec : TripleRatchet.decrypt C spqr expected ciphertext msgType coins tr0 with
            | mk rdec tr1 =>
              rw [hdec] at hd
              cases rdec with
              | error _ =>
                dsimp only [CryptoGames.LibsignalSession.liftE] at hd
                cases hd
              | ok pt0 =>
                dsimp only [CryptoGames.LibsignalSession.liftE, pure, ExceptT.pure, StateT.pure,
                  ExceptT.bindCont, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
                  StateT.bind] at hd
                cases hd
                rfl

/-! ## Congruence of the four `pq*Model`s and `pqxdhExpectedOutcome` -/

inductive PqModelResultEquiv :
    Option (Option (PqParty × HwBytes)) → Option (Option (PqParty × HwBytes)) → Prop
  | panic : PqModelResultEquiv none none
  | reject : PqModelResultEquiv (some none) (some none)
  | accept {st₀ st₁ : PqParty} {out : HwBytes} :
      PqPartyEquiv st₀ st₁ →
      PqModelResultEquiv (some (some (st₀, out))) (some (some (st₁, out)))

theorem pqInitModel_congr (X : UnreachedPqxdhPrimitives) (P : PEParams) {st₀ st₁ : PqParty}
    (hst : PqPartyEquiv st₀ st₁) (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen) :
    PqModelResultEquiv (pqInitModel X P st₀ b t) (pqInitModel X P st₁ b t) := by
  unfold pqInitModel
  have hinit : initiateState X P st₀.party st₀.me b t = initiateState X P st₁.party st₁.me b t := by
    rw [hst.party_eq, hst.me_eq]
  rw [hst.trusts_eq, hinit]
  cases st₁.trusts ⟨⟨b.idPub⟩⟩
  · simp only [Bool.not_false, ↓reduceIte]
    exact .reject
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases initiateState X P st₁.party st₁.me b t with
    | none => exact .reject
    | some xg =>
      rcases xg with ⟨x, g⟩
      exact .accept (pqPartyEquiv_with_peer_session hst _ (PqSessionEquiv.refl x g))

theorem pqSendModel_congr (P : PEParams) {st₀ st₁ : PqParty}
    (hst : PqPartyEquiv st₀ st₁) (m r : HwBytes) :
    PqModelResultEquiv (pqSendModel P st₀ m r) (pqSendModel P st₁ m r) := by
  unfold pqSendModel
  cases hs₀ : st₀.session <;> cases hs₁ : st₁.session
  · exact .reject
  · have hr := hst.session_rel; rw [hs₀, hs₁] at hr; cases hr
  · have hr := hst.session_rel; rw [hs₀, hs₁] at hr; cases hr
  · rename_i xg₀ xg₁
    rcases xg₀ with ⟨x₀, g₀⟩
    rcases xg₁ with ⟨x₁, g₁⟩
    have hr := hst.session_rel; rw [hs₀, hs₁] at hr
    cases hr with
    | some hse =>
      dsimp only at hse ⊢
      have henc : SessionState.messageEncrypt P.C protoSignalCodec (pqxdhSpqrSession P)
          ((pqxdhSessionParams P).sendAddrs g₀.party) m r g₀.session =
          SessionState.messageEncrypt P.C protoSignalCodec (pqxdhSpqrSession P)
          ((pqxdhSessionParams P).sendAddrs g₁.party) m r g₁.session := by
        rw [hse.party_eq, hse.session_eq]
      rw [← henc]
      cases hm : SessionState.messageEncrypt P.C protoSignalCodec (pqxdhSpqrSession P)
          ((pqxdhSessionParams P).sendAddrs g₀.party) m r g₀.session with
      | mk res s =>
        cases res with
        | error err =>
          cases err <;> first | exact .panic | exact .reject
        | ok msg =>
          dsimp only
          have hrem : g₁.session.remoteIdentity = g₀.session.remoteIdentity := by
            rw [hse.session_eq]
          rw [hrem]
          cases g₀.session.remoteIdentity with
          | none => exact .reject
          | some k =>
            dsimp only
            rw [hst.trusts_eq k]
            cases st₁.trusts k
            · simp only [Bool.not_false, ↓reduceIte]
              exact .reject
            · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              have hwire : (if g₀.session.pendingPreKey then wirePrekey :: firstMessageBody x₀ g₀.session msg
                  else wireWhisper :: msg.serialized) =
                  (if g₁.session.pendingPreKey then wirePrekey :: firstMessageBody x₁ g₁.session msg
                  else wireWhisper :: msg.serialized) := by
                cases hppk : g₀.session.pendingPreKey
                · have hppk₁ : g₁.session.pendingPreKey = false := hse.session_eq ▸ hppk
                  simp [hppk₁]
                · have hppk₁ : g₁.session.pendingPreKey = true := hse.session_eq ▸ hppk
                  have hx := hse.pending_eq hppk
                  simp [hppk₁, hx, hse.session_eq]
              rw [hwire]
              have hppk_pres := messageEncrypt_pendingPreKey P.C protoSignalCodec (pqxdhSpqrSession P)
                ((pqxdhSessionParams P).sendAddrs g₀.party) m r g₀.session s msg hm
              have hse' : PqSessionEquiv x₀ { g₀ with session := s } x₁ { g₁ with session := s } :=
                { party_eq := hse.party_eq
                  session_eq := rfl
                  remoteReg_eq := hse.remoteReg_eq
                  localReg_eq := hse.localReg_eq
                  aliceBase_eq := hse.aliceBase_eq
                  pending_eq := fun hp => hse.pending_eq (hppk_pres ▸ hp) }
              exact .accept (pqPartyEquiv_with_peer_session hst k hse')

theorem pqDecryptWith_congr (P : PEParams) {st₀ st₁ : PqParty}
    (hst : PqPartyEquiv st₀ st₁) {x₀ x₁ : RecordExtras} {g₀ g₁ : GhostState HwBytes}
    (hse : PqSessionEquiv x₀ g₀ x₁ g₁) (msg : SignalMessage) (ty : MessageType) (rc : BitVec 256) :
    PqModelResultEquiv (pqxdhSessionDecryptModel P st₀ x₀ g₀ msg ty rc)
                       (pqxdhSessionDecryptModel P st₁ x₁ g₁ msg ty rc) := by
  unfold pqxdhSessionDecryptModel
  have hdec_eq : SessionState.tryDecryptFromRecord P.C (pqxdhSpqrSession P) ((pqxdhSessionParams P).expectedAddrs g₀.party)
      msg ty rc g₀.session =
      SessionState.tryDecryptFromRecord P.C (pqxdhSpqrSession P) ((pqxdhSessionParams P).expectedAddrs g₁.party)
      msg ty rc g₁.session := by
    rw [hse.party_eq, hse.session_eq]
  rw [← hdec_eq]
  cases hd : SessionState.tryDecryptFromRecord P.C (pqxdhSpqrSession P) ((pqxdhSessionParams P).expectedAddrs g₀.party)
      msg ty rc g₀.session with
  | mk res s =>
    cases res with
    | error err =>
      cases err <;> first | exact .panic | exact .reject
    | ok pt =>
      dsimp only
      cases s.remoteIdentity with
      | none => exact .reject
      | some k =>
        dsimp only
        rw [hst.trusts_eq k]
        split_ifs
        · exact .reject
        · have hppk_false := tryDecryptFromRecord_pendingPreKey P.C (pqxdhSpqrSession P)
            ((pqxdhSessionParams P).expectedAddrs g₀.party) msg ty rc g₀.session s pt hd
          have hse' : PqSessionEquiv x₀ { g₀ with session := s } x₁ { g₁ with session := s } :=
            { party_eq := hse.party_eq
              session_eq := rfl
              remoteReg_eq := hse.remoteReg_eq
              localReg_eq := hse.localReg_eq
              aliceBase_eq := hse.aliceBase_eq
              pending_eq := fun hp => by rw [hppk_false] at hp; cases hp }
          exact .accept (pqPartyEquiv_with_peer_session hst k hse')

theorem pqRecvWhisperModel_congr (P : PEParams) {st₀ st₁ : PqParty}
    (hst : PqPartyEquiv st₀ st₁) (c : HwBytes) (rc : BitVec 256) :
    PqModelResultEquiv (pqRecvWhisperModel P st₀ c rc) (pqRecvWhisperModel P st₁ c rc) := by
  unfold pqRecvWhisperModel
  cases hs₀ : st₀.session <;> cases hs₁ : st₁.session
  · exact .reject
  · have hr := hst.session_rel; rw [hs₀, hs₁] at hr; cases hr
  · have hr := hst.session_rel; rw [hs₀, hs₁] at hr; cases hr
  · rename_i xg₀ xg₁
    rcases xg₀ with ⟨x₀, g₀⟩
    rcases xg₁ with ⟨x₁, g₁⟩
    have hr := hst.session_rel; rw [hs₀, hs₁] at hr
    cases hr with
    | some hse =>
      dsimp only at hse ⊢
      cases SignalMessage.tryFrom protoSignalCodec c with
      | error _ => exact .reject
      | ok msg => exact pqDecryptWith_congr P hst hse msg .whisper rc

theorem pqRecvPrekeyModel_congr (X : UnreachedPqxdhPrimitives) (P : PEParams) {st₀ st₁ : PqParty}
    (hst : PqPartyEquiv st₀ st₁) (m : PreKeyMessageFields) (rc : BitVec 256) :
    PqModelResultEquiv (pqRecvPrekeyModel X P st₀ m rc) (pqRecvPrekeyModel X P st₁ m rc) := by
  unfold pqRecvPrekeyModel
  cases SignalMessage.tryFrom protoSignalCodec m.inner with
  | error _ => exact .reject
  | ok inner =>
    dsimp only
    rw [hst.trusts_eq]
    split_ifs
    · exact .reject
    · cases hs₀ : st₀.session <;> cases hs₁ : st₁.session
      · dsimp only
        rw [keysFor_eq_of_pqPartyEquiv hst m]
        cases preKeysNamedBy st₁ m with
        | none => exact .reject
        | some k =>
          dsimp only
          rw [hst.party_eq, hst.me_eq]
          cases recvPrekeyState X P st₁.party st₁.me k m rc with
          | none => exact .panic
          | some opt =>
            cases opt with
            | none => exact .reject
            | some xgpt =>
              rcases xgpt with ⟨x, g, pt⟩
              dsimp only
              have hmku := markKyberUsed_congr hst m
              cases hm₀ : markKyberUsed st₀ m <;> cases hm₁ : markKyberUsed st₁ m
              · exact .reject
              · rw [hm₀, hm₁] at hmku; cases hmku
              · rw [hm₀, hm₁] at hmku; cases hmku
              · rw [hm₀, hm₁] at hmku
                cases hmku with
                | some hst1 =>
                  dsimp only
                  exact .accept (pqPartyEquiv_with_peer_session (removeOpk_congr hst1 m) _
                    (PqSessionEquiv.refl x g))
      · have hr := hst.session_rel; rw [hs₀, hs₁] at hr; cases hr
      · have hr := hst.session_rel; rw [hs₀, hs₁] at hr; cases hr
      · rename_i xg₀ xg₁
        rcases xg₀ with ⟨x₀, g₀⟩
        rcases xg₁ with ⟨x₁, g₁⟩
        have hr := hst.session_rel; rw [hs₀, hs₁] at hr
        cases hr with
        | some hse =>
          dsimp only at hse ⊢
          have hm_iff := hse.matches_iff m
          by_cases hmat₀ : PqSessionMatches x₀ g₀ m
          · have hmat₁ : PqSessionMatches x₁ g₁ m := hm_iff.mp hmat₀
            simp only [hmat₀, hmat₁, ↓reduceIte]
            have hrem : g₁.session.remoteIdentity = g₀.session.remoteIdentity := by
              rw [hse.session_eq]
            rw [hrem]
            split_ifs
            · exact .reject
            · have hdec_eq : SessionState.tryDecryptFromRecord P.C (pqxdhSpqrSession P)
                  ((pqxdhSessionParams P).expectedAddrs g₀.party) inner .preKey rc g₀.session =
                  SessionState.tryDecryptFromRecord P.C (pqxdhSpqrSession P)
                  ((pqxdhSessionParams P).expectedAddrs g₁.party) inner .preKey rc g₁.session := by
                rw [hse.party_eq, hse.session_eq]
              rw [← hdec_eq]
              cases hd : SessionState.tryDecryptFromRecord P.C (pqxdhSpqrSession P)
                  ((pqxdhSessionParams P).expectedAddrs g₀.party) inner .preKey rc g₀.session with
              | mk res s =>
                cases res with
                | error err =>
                  cases err <;> first | exact .panic | exact .reject
                | ok pt =>
                  dsimp only
                  have hppk_false := tryDecryptFromRecord_pendingPreKey P.C (pqxdhSpqrSession P)
                    ((pqxdhSessionParams P).expectedAddrs g₀.party) inner .preKey rc g₀.session s pt hd
                  have hse' : PqSessionEquiv x₀ { g₀ with session := s } x₁ { g₁ with session := s } :=
                    { party_eq := hse.party_eq
                      session_eq := rfl
                      remoteReg_eq := hse.remoteReg_eq
                      localReg_eq := hse.localReg_eq
                      aliceBase_eq := hse.aliceBase_eq
                      pending_eq := fun hp => by rw [hppk_false] at hp; cases hp }
                  exact .accept (pqPartyEquiv_with_peer_session hst _ hse')
          · have hmat₁ : ¬ PqSessionMatches x₁ g₁ m := fun h1 => hmat₀ (hm_iff.mpr h1)
            simp only [hmat₀, hmat₁, ↓reduceIte]
            exact .reject

theorem pqObserve_congr (B : SDetBridges) (P : PEParams) {i₀ i₁ : Inputs}
    {r₀ r₁ : Option (Option (PqParty × HwBytes))}
    (hreg₀ : RegularFileList i₀.files) (hreg₁ : RegularFileList i₁.files)
    (heq : InputsEquiv i₀ i₁) (hr : PqModelResultEquiv r₀ r₁) :
    pqxdhExpectedOutcome P i₀ r₀ = pqxdhExpectedOutcome P i₁ r₁ := by
  cases hr with
  | panic => rfl
  | reject =>
    simp only [pqxdhExpectedOutcome, Option.map, observe, Outcome.exited.injEq, true_and]
    funext p
    exact heq.2.2.2 p
  | accept hst =>
    simp only [pqxdhExpectedOutcome, Option.map, observe, Outcome.exited.injEq, true_and]
    funext p
    rw [filesOf_append_of_regular hreg₀ (regularFileList_encodeDir P _),
        filesOf_append_of_regular hreg₁ (regularFileList_encodeDir P _),
        B.files_of_party_equiv P hst p, heq.2.2.2 p]

/-! ## Assembling `PqModelPost` from `Draft.PqModelRel` and `SDetBridges` -/

theorem sdet_of_bridges (B : SDetBridges)
    (Xof : ExternInterpretation → UnreachedPqxdhPrimitives) (Wof : ExternInterpretation → PEParams)
    (interp : ExternInterpretation) (i : Inputs) (o : Outcome)
    (h : Draft.PqModelRel Xof Wof interp i o) : PqModelPost interp (Wof interp) i o := by
  obtain ⟨st₀, i₀, hwf₀, heq₀_d, hcall⟩ := h
  have heq₀ : InputsEquiv i i₀ := heq₀_d
  set P := Wof interp
  set X₀ := Xof interp
  refine
    { init := ?_
      send := ?_
      recvWhisper := ?_
      recvPrekey := ?_
      recvPrekeyNoMatch := ?_
      recvOther := ?_
      recvPrekeyNoMatchSession := ?_
      recvPrekeyReject := ?_
      recvPrekeyUntyped := ?_
      recvPrekeyMatching := ?_
      recvPrekeyParsed := ?_
      recvPrekeyParsedNoMatch := ?_
      initFiles := ?_
      initReject := ?_ }
  · intro X₁ st₁ b₁ t₁ hwf₁ _hs₁ heq₁
    have heq : InputsEquiv i₀ (pqInitInputs P st₁ b₁ t₁) := heq₀.symm.trans heq₁
    rcases hcall with ⟨b₀, t₀, _hs₀, rfl, rfl⟩ | ⟨m₀, r₀, _, rfl, _⟩ |
        ⟨c₀, rc₀, _, rfl, _⟩ | ⟨m₀, rc₀, _, _, rfl, _⟩
    · obtain ⟨rfl, rfl, hfiles⟩ := B.init_extract heq
      have hst := B.party_equiv_of_files hwf₀ hwf₁ hfiles
      rw [pqInitModel_xindep X₀ X₁ P st₀ b₀ t₀]
      exact pqObserve_congr B P (regularFileList_pqInitInputs P st₀ b₀ t₀)
        (regularFileList_pqInitInputs P st₁ b₀ t₀) heq (pqInitModel_congr X₁ P hst b₀ t₀)
    · exact False.elim (B.init_send_false heq.symm)
    · exact False.elim (B.init_recv_false heq.symm)
    · exact False.elim (B.init_recv_false heq.symm)
  · intro st₁ m₁ r₁ hwf₁ _hm₁ heq₁
    have heq : InputsEquiv i₀ (pqSendInputs P st₁ m₁ r₁) := heq₀.symm.trans heq₁
    rcases hcall with ⟨b₀, t₀, _, rfl, _⟩ | ⟨m₀, r₀, _hm₀, rfl, rfl⟩ |
        ⟨c₀, rc₀, _, rfl, _⟩ | ⟨m₀, rc₀, _, _, rfl, _⟩
    · exact False.elim (B.init_send_false heq)
    · obtain ⟨rfl, rfl, hfiles⟩ := B.send_extract heq
      have hst := B.party_equiv_of_files hwf₀ hwf₁ hfiles
      exact pqObserve_congr B P (regularFileList_pqSendInputs P st₀ m₀ r₀)
        (regularFileList_pqSendInputs P st₁ m₀ r₀) heq (pqSendModel_congr P hst m₀ r₀.toList)
    · exact False.elim (B.send_recv_false heq.symm)
    · exact False.elim (B.send_recv_false heq.symm)
  · intro st₁ body₁ rc₁ hwf₁ _hb₁ heq₁
    have heq : InputsEquiv i₀ (pqRecvInputs P st₁ (wireWhisper :: body₁) rc₁) := heq₀.symm.trans heq₁
    rcases hcall with ⟨b₀, t₀, _, rfl, _⟩ | ⟨m₀, r₀, _, rfl, _⟩ |
        ⟨body₀, rc₀, _hc₀, rfl, rfl⟩ | ⟨m₀, rc₀, _, _, rfl, _⟩
    · exact False.elim (B.init_recv_false heq)
    · exact False.elim (B.send_recv_false heq)
    · obtain ⟨rfl, rfl, hfiles⟩ := B.whisper_extract heq
      have hst := B.party_equiv_of_files hwf₀ hwf₁ hfiles
      exact pqObserve_congr B P (regularFileList_pqRecvInputs P st₀ (wireWhisper :: body₀) rc₀)
        (regularFileList_pqRecvInputs P st₁ (wireWhisper :: body₀) rc₀) heq
        (pqRecvWhisperModel_congr P hst body₀ rc₀)
    · exact False.elim (B.whisper_prekey_false heq.symm)
  · intro X₁ st₁ m₁ rc₁ hwf₁ hm₁ _hmatch₁ heq₁
    have heq : InputsEquiv i₀ (pqRecvInputs P st₁ (wirePrekey :: m₁.bytes) rc₁) := heq₀.symm.trans heq₁
    rcases hcall with ⟨b₀, t₀, _, rfl, _⟩ | ⟨m₀, r₀, _, rfl, _⟩ |
        ⟨body₀, rc₀, _, rfl, _⟩ | ⟨m₀, rc₀, hm₀, _hmatch₀, rfl, rfl⟩
    · exact False.elim (B.init_recv_false heq)
    · exact False.elim (B.send_recv_false heq)
    · exact False.elim (B.whisper_prekey_false heq)
    · obtain ⟨rfl, rfl, hfiles⟩ := B.prekey_extract hm₀ hm₁ heq
      have hst := B.party_equiv_of_files hwf₀ hwf₁ hfiles
      rw [pqRecvPrekeyModel_xindep X₀ X₁ P st₀ m₀ rc₀]
      exact pqObserve_congr B P (regularFileList_pqRecvInputs P st₀ (wirePrekey :: m₀.bytes) rc₀)
        (regularFileList_pqRecvInputs P st₁ (wirePrekey :: m₀.bytes) rc₀) heq
        (pqRecvPrekeyModel_congr X₁ P hst m₀ rc₀)
  · intro _X₁ st₁ x₁ g₁ m₁ rc₁ hwf₁ hs₁ hm₁ hnomatch₁ heq₁
    have heq : InputsEquiv i₀ (pqRecvInputs P st₁ (wirePrekey :: m₁.bytes) rc₁) := heq₀.symm.trans heq₁
    rcases hcall with ⟨b₀, t₀, _, rfl, _⟩ | ⟨m₀, r₀, _, rfl, _⟩ |
        ⟨body₀, rc₀, _, rfl, _⟩ | ⟨m₀, rc₀, hm₀, hmatch₀, rfl, _⟩
    · exact False.elim (B.init_recv_false heq)
    · exact False.elim (B.send_recv_false heq)
    · exact False.elim (B.whisper_prekey_false heq)
    · obtain ⟨rfl, _, hfiles⟩ := B.prekey_extract hm₀ hm₁ heq
      have hst := B.party_equiv_of_files hwf₀ hwf₁ hfiles
      have hrel := hst.session_rel
      rw [hs₁] at hrel
      cases hs₀ : st₀.session with
      | none =>
        rw [hs₀] at hrel
        cases hrel
      | some xg₀ =>
        rcases xg₀ with ⟨x₀, g₀⟩
        rw [hs₀] at hrel
        cases hrel with
        | some hse =>
          exact False.elim (hnomatch₁ ((hse.matches_iff m₀).mp (hmatch₀ x₀ g₀ hs₀)))
  · intro st₁ c₁ rc₁ _hwf₁ _hc₁ hnw hnp heq₁
    have heq : InputsEquiv i₀ (pqRecvInputs P st₁ c₁ rc₁) := heq₀.symm.trans heq₁
    rcases hcall with ⟨b₀, t₀, _, rfl, _⟩ | ⟨m₀, r₀, _, rfl, _⟩ |
        ⟨body₀, rc₀, _, rfl, _⟩ | ⟨m₀, rc₀, _, _, rfl, _⟩
    · exact False.elim (B.init_recv_false heq)
    · exact False.elim (B.send_recv_false heq)
    · exact False.elim (B.whisper_other_false hnw heq)
    · exact False.elim (B.prekey_other_false hnp heq)
  · intro _X₁ st₁ x₁ g₁ m₁ rc₁ hwf₁ hs₁ hm₁ hnomatch₁ heq₁
    have heq : InputsEquiv i₀ (pqRecvInputs P st₁ (wirePrekey :: m₁.bytes) rc₁) := heq₀.symm.trans heq₁
    rcases hcall with ⟨b₀, t₀, _, rfl, _⟩ | ⟨m₀, r₀, _, rfl, _⟩ |
        ⟨body₀, rc₀, _, rfl, _⟩ | ⟨m₀, rc₀, hm₀, hmatch₀, rfl, _⟩
    · exact False.elim (B.init_recv_false heq)
    · exact False.elim (B.send_recv_false heq)
    · exact False.elim (B.whisper_prekey_false heq)
    · obtain ⟨rfl, _, hfiles⟩ := B.prekey_extract hm₀ hm₁ heq
      have hst := B.party_equiv_of_files hwf₀ hwf₁ hfiles
      have hrel := hst.session_rel
      rw [hs₁] at hrel
      cases hs₀ : st₀.session with
      | none => rw [hs₀] at hrel; cases hrel
      | some xg₀ =>
        rcases xg₀ with ⟨x₀, g₀⟩
        rw [hs₀] at hrel
        cases hrel with
        | some hse =>
          exact False.elim (hnomatch₁ ((hse.matches_iff m₀).mp (hmatch₀ x₀ g₀ hs₀)))
  · intro st₁ body₁ rc₁ _hwf₁ _hlen₁ hparse₁ heq₁
    have heq : InputsEquiv i₀ (pqRecvInputs P st₁ (wirePrekey :: body₁) rc₁) := heq₀.symm.trans heq₁
    rcases hcall with ⟨b₀, t₀, _, rfl, _⟩ | ⟨m₀, r₀, _, rfl, _⟩ |
        ⟨body₀, rc₀, _, rfl, _⟩ | ⟨m₀, rc₀, hm₀, _, rfl, rfl⟩
    · exact False.elim (B.init_recv_false heq)
    · exact False.elim (B.send_recv_false heq)
    · exact False.elim (pqRecvWhisper_wirePrekey_false heq)
    · have hbody : body₁ = m₀.bytes := ((List.cons.inj heq.2.2.1).2).symm
      subst hbody
      rw [DY.Libsignal.Composed.Refinement.Cli.pqRecvPrekeyModel_eq_some_none_of_parsePreKey_bytes_none
        X₀ P st₀ m₀ rc₀ hm₀ hparse₁]
      exact congrArg (Outcome.exited 1 []) (funext heq.2.2.2)
  · intro st₁ body₁ q₁ rc₁ _hwf₁ _hlen₁ hq₁ hpk₁ _hnfm₁ heq₁
    have heq : InputsEquiv i₀ (pqRecvInputs P st₁ (wirePrekey :: body₁) rc₁) := heq₀.symm.trans heq₁
    rcases hcall with ⟨b₀, t₀, _, rfl, _⟩ | ⟨m₀, r₀, _, rfl, _⟩ |
        ⟨body₀, rc₀, _, rfl, _⟩ | ⟨m₀, rc₀, hm₀, _, rfl, _⟩
    · exact False.elim (B.init_recv_false heq)
    · exact False.elim (B.send_recv_false heq)
    · exact False.elim (pqRecvWhisper_wirePrekey_false heq)
    · have hbody : body₁ = m₀.bytes := ((List.cons.inj heq.2.2.1).2).symm
      subst hbody
      exact False.elim (DY.Libsignal.Composed.Refinement.Cli.a2_untyped_vacuous_on_bytes m₀ q₁ hm₀ hq₁ hpk₁)
  · intro st₁ x₁ g₁ body₁ q₁ rc₁ hwf₁ hs₁ _hlen₁ hq₁ hfm₁ heq₁
    have heq : InputsEquiv i₀ (pqRecvInputs P st₁ (wirePrekey :: body₁) rc₁) := heq₀.symm.trans heq₁
    rcases hcall with ⟨b₀, t₀, _, rfl, _⟩ | ⟨m₀, r₀, _, rfl, _⟩ |
        ⟨body₀, rc₀, _, rfl, _⟩ | ⟨m₀, rc₀, hm₀, _, rfl, rfl⟩
    · exact False.elim (B.init_recv_false heq)
    · exact False.elim (B.send_recv_false heq)
    · exact False.elim (pqRecvWhisper_wirePrekey_false heq)
    · have hbody : body₁ = m₀.bytes := ((List.cons.inj heq.2.2.1).2).symm
      subst hbody
      obtain ⟨_, hrc, hfiles⟩ := B.prekey_extract hm₀ hm₀ heq
      have hrc' : rc₁ = rc₀ := hrc.symm; subst hrc'
      have hst := B.party_equiv_of_files hwf₀ hwf₁ hfiles
      have hm_some := DY.Libsignal.Composed.Refinement.Cli.preKeyOfBody?_bytes_of_parsePreKey_some hm₀ hq₁
      rw [DY.Libsignal.Composed.Refinement.Cli.pqRecvMatchingFieldsModel_eq_pqRecvPrekeyModel
        X₀ P st₁ x₁ g₁ rc₁ hwf₁ hs₁ hq₁ hm_some hfm₁]
      exact pqObserve_congr B P (regularFileList_pqRecvInputs P st₀ (wirePrekey :: m₀.bytes) rc₁)
        (regularFileList_pqRecvInputs P st₁ (wirePrekey :: m₀.bytes) rc₁) heq
        (pqRecvPrekeyModel_congr X₀ P hst m₀ rc₁)
  · intro X₁ st₁ body₁ m₁ rc₁ hwf₁ _hlen₁ hpk₁ _hin₁ _hsm₁ heq₁
    have heq : InputsEquiv i₀ (pqRecvInputs P st₁ (wirePrekey :: body₁) rc₁) := heq₀.symm.trans heq₁
    rcases hcall with ⟨b₀, t₀, _, rfl, _⟩ | ⟨m₀, r₀, _, rfl, _⟩ |
        ⟨body₀, rc₀, _, rfl, _⟩ | ⟨m₀, rc₀, hm₀, _, rfl, rfl⟩
    · exact False.elim (B.init_recv_false heq)
    · exact False.elim (B.send_recv_false heq)
    · exact False.elim (pqRecvWhisper_wirePrekey_false heq)
    · have hbody : body₁ = m₀.bytes := ((List.cons.inj heq.2.2.1).2).symm
      subst hbody
      have hm_eq : m₁ = m₀ := DY.Libsignal.Composed.Refinement.Cli.eq_of_preKeyOfBody?_bytes_some hm₀ hpk₁
      subst hm_eq
      obtain ⟨_, hrc, hfiles⟩ := B.prekey_extract hm₀ hm₀ heq
      have hrc' : rc₁ = rc₀ := hrc.symm; subst hrc'
      have hst := B.party_equiv_of_files hwf₀ hwf₁ hfiles
      rw [pqRecvPrekeyModel_xindep X₀ X₁ P st₀ m₁ rc₁]
      exact pqObserve_congr B P (regularFileList_pqRecvInputs P st₀ (wirePrekey :: m₁.bytes) rc₁)
        (regularFileList_pqRecvInputs P st₁ (wirePrekey :: m₁.bytes) rc₁) heq
        (pqRecvPrekeyModel_congr X₁ P hst m₁ rc₁)
  · intro _X₁ st₁ x₁ g₁ body₁ m₁ rc₁ hwf₁ hs₁ _hlen₁ hpk₁ _hin₁ hnomatch₁ heq₁
    have heq : InputsEquiv i₀ (pqRecvInputs P st₁ (wirePrekey :: body₁) rc₁) := heq₀.symm.trans heq₁
    rcases hcall with ⟨b₀, t₀, _, rfl, _⟩ | ⟨m₀, r₀, _, rfl, _⟩ |
        ⟨body₀, rc₀, _, rfl, _⟩ | ⟨m₀, rc₀, hm₀, hmatch₀, rfl, _⟩
    · exact False.elim (B.init_recv_false heq)
    · exact False.elim (B.send_recv_false heq)
    · exact False.elim (pqRecvWhisper_wirePrekey_false heq)
    · have hbody : body₁ = m₀.bytes := ((List.cons.inj heq.2.2.1).2).symm
      subst hbody
      have hm_eq : m₁ = m₀ := DY.Libsignal.Composed.Refinement.Cli.eq_of_preKeyOfBody?_bytes_some hm₀ hpk₁
      subst hm_eq
      obtain ⟨_, _, hfiles⟩ := B.prekey_extract hm₀ hm₀ heq
      have hst := B.party_equiv_of_files hwf₀ hwf₁ hfiles
      have hrel := hst.session_rel
      rw [hs₁] at hrel
      cases hs₀ : st₀.session with
      | none => rw [hs₀] at hrel; cases hrel
      | some xg₀ =>
        rcases xg₀ with ⟨x₀, g₀⟩
        rw [hs₀] at hrel
        cases hrel with
        | some hse =>
          exact False.elim (hnomatch₁ ((hse.matches_iff m₁).mp (hmatch₀ x₀ g₀ hs₀)))
  · intro X₁ st₁ files₁ b₁ t₁ hwf₁ _hs₁ hflat₁ hparse₁ heq₁
    have heq : InputsEquiv i₀ (pqInitInputsF P st₁ files₁ t₁) := heq₀.symm.trans heq₁
    rcases hcall with ⟨b₀, t₀, _hs₀, rfl, rfl⟩ | ⟨m₀, r₀, _, rfl, _⟩ |
        ⟨c₀, rc₀, _, rfl, _⟩ | ⟨m₀, rc₀, _, _, rfl, _⟩
    · obtain ⟨hpb, rfl, hfiles⟩ := pqInitInputs_pqInitInputsF_extract hflat₁ heq
      rw [hparse₁, Option.some.injEq] at hpb
      obtain rfl := (DY.Libsignal.Composed.Refinement.Cli.publicBundleOf_injective hpb).symm
      have hst := B.party_equiv_of_files hwf₀ hwf₁ hfiles
      rw [pqInitModel_xindep X₀ X₁ P st₀ b₀ t₀,
        pqObserve_congr B P (regularFileList_pqInitInputs P st₀ b₀ t₀)
          (regularFileList_pqInitInputsF P st₁ hflat₁ t₀) heq (pqInitModel_congr X₁ P hst b₀ t₀)]
      exact DY.Libsignal.Composed.Refinement.Cli.ScrubAgree.refl _
    · exact False.elim (pqSendInputs_pqInitInputsF_false heq)
    · exact False.elim (pqRecvInputs_pqInitInputsF_false heq)
    · exact False.elim (pqRecvInputs_pqInitInputsF_false heq)
  · intro st₁ files₁ t₁ _hwf₁ _hs₁ hflat₁ hparse₁ heq₁
    have heq : InputsEquiv i₀ (pqInitInputsF P st₁ files₁ t₁) := heq₀.symm.trans heq₁
    rcases hcall with ⟨b₀, t₀, _, rfl, _⟩ | ⟨m₀, r₀, _, rfl, _⟩ |
        ⟨c₀, rc₀, _, rfl, _⟩ | ⟨m₀, rc₀, _, _, rfl, _⟩
    · obtain ⟨hpb, _, _⟩ := pqInitInputs_pqInitInputsF_extract hflat₁ heq
      rw [hparse₁] at hpb; cases hpb
    · exact False.elim (pqSendInputs_pqInitInputsF_false heq)
    · exact False.elim (pqRecvInputs_pqInitInputsF_false heq)
    · exact False.elim (pqRecvInputs_pqInitInputsF_false heq)

end DY.Libsignal.Composed.Refinement.Cli.SDet
