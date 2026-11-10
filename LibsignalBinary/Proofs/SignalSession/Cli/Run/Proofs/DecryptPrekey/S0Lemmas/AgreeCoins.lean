/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.LoadRec
import LibsignalBinary.Proofs.E2E.Run.RecvPure
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.S0Lemmas.Agree

/-!
# Coin Round-Trip, Wire Inversion, and Session-Record Helpers for `decPkDef`

Proves helper lemmas for `pqDecryptPrekeyAgrees_decPkDef`, including the 32-byte coin round-trip
`pkRecvCoins_keyToBytes32`, wire inversion `pkToE?_pmOfE`, scalar-clamping idempotence across
`recvPrekeyState`, and matched-session record encoding.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.DecPkS0

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes

/-! ## Mirrored `S₀` definitions -/

def pmOfE (m : PreKeyMessageFields) (i : SignalMessage) : PreKeySignalMessage :=
  E2E.Pqxdh.ResponderWire.PreKeyTryFromArgs.toModel
    { ptr := 0, sret := 0, regId := m.regId, opkId := m.opkId, spkId := m.spkId, kpkId := m.kpkId,
      kyberCt := m.kyberCt, baseKey := m.baseKey, idPub := m.idPub, inner := m.inner } i

def PksmTyped (S : RunSem) : Prop :=
  ∀ (m : PreKeyMessageFields) (pm : PreKeySignalMessage), m.inner.length + 2048 < 2 ^ 32 →
    S.pksmParse m.bytes = some pm →
    ∃ i : SignalMessage, SignalMessage.tryFrom protoSignalCodec m.inner = .ok i ∧ pm = pmOfE m i

def pkVecTag? (tag : BitVec 8) (n : Nat) (l : List (BitVec 8)) :
    Option (List.Vector (BitVec 8) n) :=
  match l with
  | t :: rest => if h : t = tag ∧ rest.length = n then some ⟨rest, h.2⟩ else none
  | [] => none

def pkVec? (n : Nat) (l : List (BitVec 8)) : Option (List.Vector (BitVec 8) n) :=
  if h : l.length = n then some ⟨l, h⟩ else none

def pkToE? (pm : PreKeySignalMessage) : Option PreKeyMessageFields :=
  if pm.messageVersion ≠ 4 then none
  else
    match pm.kyberPayload with
    | none => none
    | some kp =>
      match pkVecTag? 8 1568 kp.ciphertext with
      | none => none
      | some ct =>
        some { regId := pm.registrationId, opkId := pm.preKeyId, spkId := pm.signedPreKeyId,
               kpkId := kp.preKeyId, kyberCt := ct, baseKey := pm.baseKey.bytes,
               idPub := pm.identityKey.publicKey.bytes, inner := pm.message.serialized }

def SessMatchesPm (s : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8)))
    (pm : PreKeySignalMessage) : Prop :=
  s.state.version = pm.messageVersion.zeroExtend 32 ∧ s.aliceBaseKey = pm.baseKey.serialize

instance (s : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8)))
    (pm : PreKeySignalMessage) : Decidable (SessMatchesPm s pm) := by
  unfold SessMatchesPm; infer_instance

def pkStoreKeys (F : FsFiles) (m : PreKeyMessageFields) : Option ResponderPreKeySecrets :=
  let g := StoresGhost.opened
  match getSignedPreKey cliIo.rd F g.signed m.spkId, g.kyber.get cliIo.rd F m.kpkId with
  | .ok sr, .ok kr =>
    match pkVec? 32 sr.signedPreKey.privateKey, pkVecTag? 8 1568 kr.signedPreKey.publicKey,
        pkVecTag? 8 3168 kr.signedPreKey.privateKey with
    | some spk, some kpub, some ksec =>
      let opk : Option (Option (BitVec 32 × List.Vector (BitVec 8) 32)) :=
        match m.opkId with
        | none => some none
        | some j =>
          match getPreKey cliIo.rd F g.oneTime j with
          | .ok r => (pkVec? 32 r.preKey.privateKey).map fun sk => some (j, sk)
          | .error _ => none
      opk.map fun o =>
        { spkId := m.spkId, spkPriv := spk, kpkId := m.kpkId, kpkPub := kpub, kpkSec := ksec,
          opk := o }
    | _, _, _ => none
  | _, _ => none

def pkRecvCoins (c : List (BitVec 8)) : BitVec 256 :=
  HKDF.bytesToKey32 (c.take 32 ++ List.replicate (32 - c.length) 0#8)

noncomputable def decPkDef (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (F : FsFiles) (peer _me : AddrVal)
    (pm : PreKeySignalMessage) (coins : List (BitVec 8)) : SlotAns (List (BitVec 8)) :=
  let g := StoresGhost.opened
  let P := initParty peer
  match Slots.loadRec Scope F peer with
  | .error _ => some none
  | .ok r =>
    match g.identity.trusted cliIo.rd F peer pm.identityKey with
    | .error _ => some none
    | .ok false => some none
    | .ok true =>
      let saved := g.identity.saveUpd cliIo.rd F peer pm.identityKey
      match r.bind (·.currentSession) with
      | some s =>
        if SessMatchesPm s pm then
          if s.state.remoteIdentity ≠ some pm.identityKey then some none
          else
            match SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W) ((pqxdhSessionParams W).expectedAddrs P)
                pm.message .preKey (pkRecvCoins coins) s.state with
            | (.ok pt, st) =>
              some (some ({ g with
                identity := saved
                sessions := g.sessions.put (addressText peer)
                  (E2E.Record.encodeRecord
                    { currentSession := some { s with state := st, pendingPreKey := none,
                                                      pendingKyberPreKey := none } }) }, pt))
            | (.error .panic, _) => none
            | (.error _, _) => some none
        else some none
      | none =>
        match pkToE? pm with
        | none => some none
        | some m =>
          match pkStoreKeys F m, g.identity.keyPair cliIo.rd F, g.identity.regId cliIo.rd F with
          | some k, .ok kp, .ok reg =>
            match recvPrekeyState X W P ⟨kp.privateKey.bytes, reg⟩ k m (pkRecvCoins coins) with
            | none => none
            | some none => some none
            | some (some (x, gs, pt)) =>
              match g.kyber.mark cliIo.rd F m.kpkId pm.signedPreKeyId pm.baseKey with
              | (.error _, _) => some none
              | (.ok (), kyber') =>
                let oneTime' := match pm.preKeyId with
                  | none => g.oneTime
                  | some j => (removePreKey cliIo.rd F g.oneTime j).2
                some (some ({ g with
                  identity := saved
                  kyber := kyber'
                  oneTime := oneTime'
                  sessions := g.sessions.put (addressText peer) (encodeRecordUnderExtras (fun _ => x) gs) },
                  pt))
          | _, _, _ => some none

def ScopeCoversPq (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  ∀ (st : PqParty) x g, PqxdhPartyInSpecDomain W st → st.session = some (x, g) →
    Scope (E2E.Record.toRecord (E2E.RecordX.extrasOf fun _ => x) g)

/-! ## Coin round-trip -/

theorem pkRecvCoins_keyToBytes32 (rc : BitVec 256) :
    pkRecvCoins (HMAC.keyToBytes32 rc) = rc := by
  unfold pkRecvCoins
  have hlen : (HMAC.keyToBytes32 rc).length = 32 := by simp [HMAC.keyToBytes32]
  rw [hlen, Nat.sub_self, List.replicate_zero, List.append_nil,
    List.take_of_length_le (Nat.le_of_eq hlen), E2E.Run.bytesToKey32_keyToBytes32]

/-! ## Wire inversion (`pkToE?_pmOfE`) -/

theorem serialized_of_tryFrom {codec : SignalMessageProtoCodec} {value : List (BitVec 8)} {i : SignalMessage}
    (h : SignalMessage.tryFrom codec value = .ok i) :
    i.serialized = value := by
  unfold SignalMessage.tryFrom at h
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure, MonadExcept.throw,
    MonadExceptOf.throw] at h
  split at h
  · nomatch h
  · split at h
    · nomatch h
    · split at h
      · nomatch h
      · split at h
        · split at h
          · split at h
            · nomatch h
            · split at h
              · split at h
                · injection h with h; rw [← h]
                · nomatch h
              · nomatch h
          · nomatch h
        · nomatch h

theorem pkVecTag?_cons_self (tag : BitVec 8) {n : Nat} (v : List.Vector (BitVec 8) n) :
    pkVecTag? tag n (tag :: v.toList) = some v := by
  simp only [pkVecTag?, true_and, v.toList_length, ↓reduceDIte, InitS0.vec_eta]

theorem pkVec?_toList {n : Nat} (v : List.Vector (BitVec 8) n) :
    pkVec? n v.toList = some v := by
  simp only [pkVec?, v.toList_length, ↓reduceDIte, InitS0.vec_eta]

theorem pkToE?_pmOfE (m : PreKeyMessageFields) (i : SignalMessage)
    (hi : SignalMessage.tryFrom protoSignalCodec m.inner = .ok i) :
    pkToE? (pmOfE m i) = some m := by
  rcases m with ⟨regId, opkId, spkId, kpkId, kyberCt, baseKey, idPub, inner⟩
  have hser := serialized_of_tryFrom hi
  unfold pkToE? pmOfE E2E.Pqxdh.ResponderWire.PreKeyTryFromArgs.toModel
    E2E.Pqxdh.ResponderWire.PreKeyTryFromArgs.kyberBytes
  dsimp only
  have htag : pkVecTag? 8 1568 (8#8 :: kyberCt.toList) = some kyberCt :=
    pkVecTag?_cons_self 8#8 kyberCt
  have h4 : ¬ (4#8 ≠ 4) := by decide
  simp only [h4, ↓reduceIte, htag, hser]

/-! ## Scalar clamping and matched-session helpers -/

theorem recvPrekeyState_clampScalar (X : UnreachedPqxdhPrimitives) (W : PEParams) (P : Party) (me : LocalIdentity)
    (k : ResponderPreKeySecrets) (m : PreKeyMessageFields) (rc : BitVec 256) :
    recvPrekeyState X W P ⟨Ratchet.clampScalar me.idPriv, me.regId⟩ k m rc =
      recvPrekeyState X W P me k m rc := by
  have hai : acceptInput W ⟨Ratchet.clampScalar me.idPriv, me.regId⟩ k m =
      acceptInput W me k m := by
    unfold acceptInput
    dsimp only
    rw [InitS0.keyPairOf_clampScalar]
  have hrx : responderRecordExtras ⟨Ratchet.clampScalar me.idPriv, me.regId⟩ m = responderRecordExtras me m := rfl
  unfold recvPrekeyState
  cases SignalMessage.tryFrom protoSignalCodec m.inner with
  | error _ => rfl
  | ok inner =>
    dsimp only
    split
    · rfl
    · rw [hai]
      cases SignalPqxdh.Model.acceptKeys (modelPrims X W) (acceptInput W me k m) with
      | none => rfl
      | some dk =>
        dsimp only
        rw [InitS0.keyPairOf_clampScalar, hrx]

theorem sessMatchesPm_toRecord (x : RecordExtras) (g : GhostState E2E.Bytes) (m : PreKeyMessageFields)
    (i : SignalMessage) (hm : PqSessionMatches x g m) :
    SessMatchesPm
      { state := g.session
        pendingPreKey := if g.session.pendingPreKey then some x.pending else none
        pendingKyberPreKey := if g.session.pendingPreKey then x.kyber else none
        localRegistrationId := x.localRegistrationId
        remoteRegistrationId := x.remoteRegistrationId
        aliceBaseKey := x.aliceBaseKey }
      (pmOfE m i) := by
  rcases hm with ⟨hbase, hver⟩
  refine ⟨?_, ?_⟩
  · unfold SessionState.version pmOfE E2E.Pqxdh.ResponderWire.PreKeyTryFromArgs.toModel
    dsimp only
    rw [hver]
    decide
  · dsimp only
    rw [hbase]
    rfl

theorem encodeRecord_cleared_eq_encodeRecordX (x : RecordExtras) (g : GhostState E2E.Bytes)
    (st' : SessionState E2E.Bytes) (hpend : st'.pendingPreKey = false) :
    E2E.Record.encodeRecord
      { currentSession := some
          { ({ state := g.session
               pendingPreKey := if g.session.pendingPreKey then some x.pending else none
               pendingKyberPreKey := if g.session.pendingPreKey then x.kyber else none
               localRegistrationId := x.localRegistrationId
               remoteRegistrationId := x.remoteRegistrationId
               aliceBaseKey := x.aliceBaseKey } : Session E2E.Bytes) with
            state := st', pendingPreKey := none, pendingKyberPreKey := none } } =
      encodeRecordUnderExtras (fun _ => x) { g with session := st' } := by
  rw [E2E.RecordX.encodeRecordX_eq_toRecord]
  unfold E2E.Record.toRecord E2E.RecordX.extrasOf E2E.RecordX.toSessionExtras
  dsimp only
  rw [hpend]
  rfl

end CryptoVerification.SignalSession.Cli.RunProofs.DecPkS0
