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
# Session Version and Remote Identity Preservation (`tryDecryptFromRecord`)

Proves `tryDecryptFromRecord_sessionVersion_remoteIdentity` and `tryDecryptFromRecord_remoteIdentity`:
`SessionState.tryDecryptFromRecord` preserves both `sessionVersion` and `remoteIdentity` across
success and error outcomes.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Closure.Version

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec

private theorem exec_pure {σ α : Type} (a : α) (s : σ) :
    Mut.exec (pure a : Mut σ α) s = (.ok a, s) := rfl

private theorem exec_throw {σ α : Type} (e : SignalProtocolError) (s : σ) :
    Mut.exec (throw e : Mut σ α) s = (.error e, s) := rfl

private theorem exec_get {σ : Type} (s : σ) :
    Mut.exec (get : Mut σ σ) s = (.ok s, s) := rfl

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

private theorem tryDecryptWithState_ok_sessionVersion_remoteIdentity {PQ PQC : Type} [Inhabited PQ]
    (C : Crypto) (spqr : Spqr PQ PQC) (expected : Option Bytes) (m : SignalMessage)
    (msgType : MessageType) (coins : BitVec 256) (record updated : SessionState PQ)
    (ptext : List (BitVec 8))
    (h : Mut.exec (SessionState.tryDecryptWithState C spqr expected m msgType coins) record =
      (.ok ptext, updated)) :
    updated.sessionVersion = record.sessionVersion ∧
    updated.remoteIdentity = record.remoteIdentity := by
  unfold SessionState.tryDecryptWithState TripleRatchet.fromSessionState
    SessionState.takeRatchetState SessionState.takePqRatchetState
    TripleRatchet.applyToSessionState SessionState.clearUnacknowledgedPreKeyMessage at h
  simp only [exec_bind, exec_modifyGet, exec_get, exec_pure, exec_liftE, exec_modify] at h
  cases hrem : record.remoteIdentity with
  | none =>
    simp only [hrem, exec_throw] at h
    cases h
  | some remote =>
    simp only [hrem, exec_pure] at h
    rcases hdec : Mut.exec (TripleRatchet.decrypt C spqr expected m msgType coins)
      { ratchet :=
          { rootKey := record.rootKey
            senderChain := record.senderChain
            receiverChains := record.receiverChains
            previousCounter := record.previousCounter
            maxForwardJumps := maxForwardJumps }
        pqrState := record.pqRatchetState
        localIdentityKey := record.localIdentity
        remoteIdentityKey := remote } with ⟨r, session⟩
    rw [hdec] at h
    cases r with
    | error e =>
      cases h
    | ok pt =>
      injection h with _ hupd
      subst hupd
      exact ⟨rfl, rfl⟩

theorem tryDecryptFromRecord_sessionVersion_remoteIdentity {PQ PQC : Type} [Inhabited PQ]
    (C : Crypto) (spqr : Spqr PQ PQC) (expected : Option Bytes) (m : SignalMessage)
    (msgType : MessageType) (coins : BitVec 256) (record : SessionState PQ) :
    (SessionState.tryDecryptFromRecord C spqr expected m msgType coins record).2.sessionVersion =
      record.sessionVersion ∧
    (SessionState.tryDecryptFromRecord C spqr expected m msgType coins record).2.remoteIdentity =
      record.remoteIdentity := by
  unfold SessionState.tryDecryptFromRecord
  split
  · exact ⟨rfl, rfl⟩
  · rcases h : Mut.exec (SessionState.tryDecryptWithState C spqr expected m msgType coins) record
      with ⟨r, updated⟩
    cases r with
    | ok ptext =>
      exact tryDecryptWithState_ok_sessionVersion_remoteIdentity
        C spqr expected m msgType coins record updated ptext h
    | error e =>
      exact ⟨rfl, rfl⟩

theorem tryDecryptFromRecord_remoteIdentity {PQ PQC : Type} [Inhabited PQ]
    (C : Crypto) (spqr : Spqr PQ PQC) (expected : Option Bytes) (m : SignalMessage)
    (msgType : MessageType) (coins : BitVec 256) (record : SessionState PQ) :
    (SessionState.tryDecryptFromRecord C spqr expected m msgType coins record).2.remoteIdentity =
      record.remoteIdentity :=
  (tryDecryptFromRecord_sessionVersion_remoteIdentity C spqr expected m msgType coins record).2

end CryptoVerification.SignalSession.Closure.Version
