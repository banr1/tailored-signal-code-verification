/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.LibsignalCli.Entry.CliPqDirRoundtrip
public import Computational.Specifications.Session.StatementSpkModel
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Lazy
public import Computational.Specifications.Pqxdh.Game
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Correctness.Crypto
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.RecvCoins
import Computational.Proofs.GameHop.Rnd
import LibsignalBinary.Proofs.SignalSession.Closure.Version
import VCVio.EvalDist.Monad.Basic
public import LibsignalBinary.Proofs.CryptoGames.Ratchet.LibsignalSessionSMProofDefs

/-!
# CLI entry runners, `EpochGhost` alignment, and receive bridges

Couples file-level `signal-session` CLI receive calls on PQXDH directories (`CliDirState`) with the
SPQR-V1 session model (`paramsPqIds` and `paramsPqBIds`), proving `GhostState.Aligned` preservation,
`EpochGhost` commutation, and `CliSpecPqxdh` commutation for whisper and pre-key messages.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession

open CryptoGames CryptoGames.CKA CryptoGames.Ratchet CryptoGames.SM CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoGames.Ratchet.LibsignalInst CryptoGames.Ratchet.LibsignalSim
open CryptoGames.LibsignalSM.Proofs.Refinement CryptoGames.LibsignalSM.Proofs.Correctness
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSpqrV1 (spqrV1SessionUniformCoins coinBytes coinBytes_length)
open OracleComp OracleSpec MeasureTheory ENNReal

local notation "RawBytes" => List (BitVec 8)

/-! ## SPQR-V1 `Params` at arbitrary identity keys -/

/-- `pqxdhSessionParams W` generalized to caller-chosen identity keys `idA`, `idB`. -/
def paramsPqIds (W : PEParams) (idA idB : IdentityKey) :
    Params RawBytes RawBytes :=
  ⟨W.C, protoSignalCodec, pqxdhSpqrSession W, idA, idB,
    serializedPartyAddresses LibsignalTripleRatchetRepr.uuidTryParse .A .B,
    serializedPartyAddresses LibsignalTripleRatchetRepr.uuidTryParse .B .A⟩

/-- `pqxdhSessionParams W` with 512-bit uniform `send` coins and caller-chosen identity keys. -/
def paramsPqBIds (W : PEParams) (idA idB : IdentityKey) :
    Params RawBytes (BitVec 512) :=
  ⟨W.C, protoSignalCodec, spqrV1SessionUniformCoins W.C.F W.Q.K, idA, idB,
    serializedPartyAddresses LibsignalTripleRatchetRepr.uuidTryParse .A .B,
    serializedPartyAddresses LibsignalTripleRatchetRepr.uuidTryParse .B .A⟩

def coinBytesVec64 (r : BitVec 512) : List.Vector (BitVec 8) 64 :=
  ⟨coinBytes r, coinBytes_length r⟩

@[simp]
theorem coinBytesVec64_toList (r : BitVec 512) :
    (coinBytesVec64 r).toList = coinBytes r :=
  rfl

theorem paramsPqIds_idOfE (W : PEParams) :
    paramsPqIds W (partyIdentityKey .A) (partyIdentityKey .B) = pqxdhSessionParams W :=
  rfl

@[simp]
theorem paramsPqBIds_send_eq (W : PEParams) (idA idB : IdentityKey)
    (g : GhostState RawBytes) (m : RawBytes) (r : BitVec 512) :
    (paramsPqBIds W idA idB).send g m r =
      (paramsPqIds W idA idB).send g m (coinBytesVec64 r).toList :=
  rfl

@[simp]
theorem paramsPqBIds_receive_eq (W : PEParams) (idA idB : IdentityKey)
    (g : GhostState RawBytes) (c : RawBytes) (rc : BitVec 256) :
    (paramsPqBIds W idA idB).receive g c rc =
      (paramsPqIds W idA idB).receive g c rc :=
  rfl

/-! ## Directory-backed party state and receive runners -/

/-- Directory-backed party state holding the party tag, candidate file paths, current on-disk
files, and `EpochGhost` bookkeeping (`DEV-M2`). -/
structure CliDirState where
  party : Party
  candidatePaths : List String
  dirFiles : List (String × List (BitVec 8))
  epochs : EpochGhost

def cliDirStateOf (W : PEParams) (st : PqParty) : CliDirState :=
  { party := st.party
    candidatePaths := pqPartyCandidatePathsOf st
    dirFiles := encodeDir W st
    epochs := match st.session with
      | some (_, g) => EpochGhost.ofGhost g
      | none => ⟨0, []⟩ }

/-- Run `recv <peer>` on whisper wire `2 ‖ c` and update `EpochGhost` (`DEV-M2`). -/
def cliPqRecvWhisperDir (run : CliRun) (s : CliDirState) (c : RawBytes)
    (rc : BitVec 256) : Option (CliDirState × ℕ × ℕ × RawBytes) :=
  match run (cliPqRecvInputsFromFiles s.party s.dirFiles (wireWhisper :: c) rc),
      SignalMessage.tryFrom protoSignalCodec c with
  | some (.exited 0 pt fs), .ok msg =>
    let (t, e) := s.epochs.recv msg.senderRatchetKey
    some ({ s with dirFiles := readBackDir s.candidatePaths fs, epochs := e },
      t, msg.counter.toNat + 1, pt)
  | some (.exited 0 pt fs), .error _ =>
    some ({ s with dirFiles := readBackDir s.candidatePaths fs }, s.epochs.epoch, 0, pt)
  | _, _ => none

/-- Run `recv <peer>` on pre-key message `3 ‖ m.bytes` when no session exists yet. -/
def cliPqRecvPrekeyInitDir (run : CliRun) (s : CliDirState) (m : PreKeyMessageFields)
    (rc : BitVec 256) : Option (CliDirState × ℕ × ℕ × RawBytes) :=
  match run (cliPqRecvInputsFromFiles s.party s.dirFiles (wirePrekey :: m.bytes) rc),
      SignalMessage.tryFrom protoSignalCodec m.inner with
  | some (.exited 0 pt fs), .ok msg =>
    some ({ s with
      dirFiles := readBackDir s.candidatePaths fs
      epochs := ⟨1, [(msg.senderRatchetKey, 1)]⟩ },
      1, msg.counter.toNat + 1, pt)
  | some (.exited 0 pt fs), .error _ =>
    some ({ s with dirFiles := readBackDir s.candidatePaths fs }, 1, 0, pt)
  | _, _ => none

/-- Run `recv <peer>` on pre-key message `3 ‖ m.bytes` when a matching session already exists. -/
def cliPqRecvPrekeyMatchingDir (run : CliRun) (s : CliDirState) (m : PreKeyMessageFields)
    (rc : BitVec 256) : Option (CliDirState × ℕ × ℕ × RawBytes) :=
  match run (cliPqRecvInputsFromFiles s.party s.dirFiles (wirePrekey :: m.bytes) rc),
      SignalMessage.tryFrom protoSignalCodec m.inner with
  | some (.exited 0 pt fs), .ok msg =>
    let (t, e) := s.epochs.recv msg.senderRatchetKey
    some ({ s with dirFiles := readBackDir s.candidatePaths fs, epochs := e },
      t, msg.counter.toNat + 1, pt)
  | some (.exited 0 pt fs), .error _ =>
    some ({ s with dirFiles := readBackDir s.candidatePaths fs }, s.epochs.epoch, 0, pt)
  | _, _ => none

/-! ## `GhostState.Aligned` and `EpochGhost` commutation -/

@[local simp] private theorem exec_pure {σ α : Type} (a : α) (s : σ) :
    Mut.exec (pure a : Mut σ α) s = (.ok a, s) := rfl

@[local simp] private theorem exec_throw {σ α : Type} (e : SignalProtocolError) (s : σ) :
    Mut.exec (throw e : Mut σ α) s = (.error e, s) := rfl

@[local simp] private theorem exec_get {σ : Type} (s : σ) :
    Mut.exec (get : Mut σ σ) s = (.ok s, s) := rfl

@[local simp] private theorem exec_set {σ : Type} (s' s : σ) :
    Mut.exec (set s' : Mut σ PUnit) s = (.ok (), s') := rfl

@[local simp] private theorem exec_modify {σ : Type} (f : σ → σ) (s : σ) :
    Mut.exec (modify f : Mut σ PUnit) s = (.ok (), f s) := rfl

@[local simp] private theorem exec_modifyGet {σ α : Type} (f : σ → α × σ) (s : σ) :
    Mut.exec (modifyGet f : Mut σ α) s = (.ok (f s).1, (f s).2) := rfl

@[local simp] private theorem exec_liftE {σ α : Type} (r : Except SignalProtocolError α) (s : σ) :
    Mut.exec (liftE r : Mut σ α) s = (r, s) := by
  cases r <;> rfl

@[local simp] private theorem exec_bind {σ α β : Type} (m : Mut σ α) (f : α → Mut σ β) (s : σ) :
    Mut.exec (m >>= f) s =
      match Mut.exec m s with
      | (.ok a, s') => Mut.exec (f a) s'
      | (.error e, s') => (.error e, s') := by
  unfold Mut.exec
  change (ExceptT.run (m >>= f)).run s = _
  rw [ExceptT.run_bind]
  simp only [StateT.run_bind]
  rcases (m.run).run s with ⟨r, s'⟩
  cases r <;> rfl

@[local simp] private theorem exec_onRatchet {PQ α : Type} (m : Mut RatchetState α)
    (t : TripleRatchet PQ) :
    Mut.exec (TripleRatchet.onRatchet m) t =
      ((Mut.exec m t.ratchet).1, { t with ratchet := (Mut.exec m t.ratchet).2 }) := by
  unfold TripleRatchet.onRatchet zoom
  simp

private theorem consumeMessageKey_toOption_eq (F : ShaCompress) (their : PublicKey)
    (ck : LibsignalSession.ChainKey)
    (counter : BitVec 32) (msgType₁ msgType₂ : MessageType) (r : RatchetState) :
    ((Mut.exec (RatchetState.consumeMessageKey F their ck counter msgType₁) r).1.toOption,
      (Mut.exec (RatchetState.consumeMessageKey F their ck counter msgType₁) r).2) =
    ((Mut.exec (RatchetState.consumeMessageKey F their ck counter msgType₂) r).1.toOption,
      (Mut.exec (RatchetState.consumeMessageKey F their ck counter msgType₂) r).2) := by
  unfold RatchetState.consumeMessageKey
  by_cases hlt : counter < ck.index
  · simp only [hlt, ↓reduceIte, exec_bind]
    rcases Mut.exec (RatchetState.takeSkippedKey their counter) r with ⟨e | opt, r1⟩
    · rfl
    · cases opt <;> rfl
  · simp only [hlt, ↓reduceIte, exec_bind, exec_get]
    by_cases hgt : r.maxForwardJumps < (counter - ck.index).toNat
    · simp only [hgt, ↓reduceIte]; rfl
    · simp only [hgt, ↓reduceIte]

private theorem tripleRatchet_decrypt_toOption_eq {PQ PQC : Type} (C : Crypto) (spqr : Spqr PQ PQC)
    (expected : Option RawBytes) (msg : SignalMessage)
    (msgType₁ msgType₂ : MessageType) (coins : BitVec 256) (tr : TripleRatchet PQ) :
    ((Mut.exec (TripleRatchet.decrypt C spqr expected msg msgType₁ coins) tr).1.toOption,
      (Mut.exec (TripleRatchet.decrypt C spqr expected msg msgType₁ coins) tr).2) =
    ((Mut.exec (TripleRatchet.decrypt C spqr expected msg msgType₂ coins) tr).1.toOption,
      (Mut.exec (TripleRatchet.decrypt C spqr expected msg msgType₂ coins) tr).2) := by
  unfold TripleRatchet.decrypt
  rw [exec_bind, exec_bind, exec_onRatchet]
  rcases Mut.exec (RatchetState.ensureReceiverChain C msg.senderRatchetKey coins) tr.ratchet with
    ⟨e | ck, r1⟩
  · rfl
  · dsimp only
    rw [exec_bind, exec_bind, exec_onRatchet, exec_onRatchet]
    have hcmk := consumeMessageKey_toOption_eq C.F msg.senderRatchetKey ck msg.counter
      msgType₁ msgType₂ r1
    rcases h1 : Mut.exec (RatchetState.consumeMessageKey C.F msg.senderRatchetKey ck msg.counter
        msgType₁) r1 with ⟨res1, r2_1⟩
    rcases h2 : Mut.exec (RatchetState.consumeMessageKey C.F msg.senderRatchetKey ck msg.counter
        msgType₂) r1 with ⟨res2, r2_2⟩
    rw [h1, h2] at hcmk; dsimp only at hcmk ⊢
    have hres : res1.toOption = res2.toOption := (Prod.mk.inj hcmk).1
    have hr2 : r2_1 = r2_2 := (Prod.mk.inj hcmk).2
    subst hr2
    cases res1 with
    | error e1 =>
      cases res2 with
      | error e2 => rfl
      | ok mkg2 => injection hres
    | ok mkg1 =>
      cases res2 with
      | error e2 => injection hres
      | ok mkg2 =>
        have hmkg : mkg1 = mkg2 := Option.some.inj hres
        subst hmkg
        dsimp only
        simp only [exec_get, exec_bind]
        cases hpan : spqr.recvPanics tr.pqrState msg.pqRatchet
        case true =>
          simp only [↓reduceIte, exec_throw, exec_bind]
        simp only [Bool.false_eq_true, ↓reduceIte]
        cases spqr.recv tr.pqrState msg.pqRatchet with
        | error b =>
          cases b
          · simp only [exec_throw, exec_bind]; rfl
          · simp only [exec_throw, exec_bind]
        | ok pqrOut =>
          rcases pqrOut with ⟨newPqrState, pqrKey'⟩
          simp only [exec_pure, exec_bind]
          by_cases hmac : (!msg.verifyMacWithAddresses C.F expected tr.remoteIdentityKey
              tr.localIdentityKey (mkg1.generateKeys C.F pqrKey').macKey) = true
          · simp only [hmac, ↓reduceIte, exec_throw, exec_bind]; rfl
          · simp only [hmac, Bool.false_eq_true, ↓reduceIte]
            cases aesCbcDecrypt C.D (mkg1.generateKeys C.F pqrKey').cipherKey
                (mkg1.generateKeys C.F pqrKey').iv msg.ciphertext with
            | none => simp only [exec_throw]; rfl
            | some ptext =>
              simp only [exec_modify, exec_pure, exec_bind]

/-- `SessionState.tryDecryptFromRecord` mapped through `Except.toOption` is independent of
`msgType`. -/
theorem tryDecryptFromRecord_toOption_eq {PQ PQC : Type} [Inhabited PQ] (C : Crypto)
    (spqr : Spqr PQ PQC) (expected : Option RawBytes) (msg : SignalMessage)
    (msgType₁ msgType₂ : MessageType) (coins : BitVec 256) (st : SessionState PQ) :
    ((SessionState.tryDecryptFromRecord C spqr expected msg msgType₁ coins st).1.toOption,
      (SessionState.tryDecryptFromRecord C spqr expected msg msgType₁ coins st).2) =
    ((SessionState.tryDecryptFromRecord C spqr expected msg msgType₂ coins st).1.toOption,
      (SessionState.tryDecryptFromRecord C spqr expected msg msgType₂ coins st).2) := by
  unfold SessionState.tryDecryptFromRecord
  by_cases hver : st.version.toNat ≠ msg.messageVersion.toNat
  · simp [hver, Except.toOption]
  · simp only [hver, ↓reduceIte]
    unfold SessionState.tryDecryptWithState
    simp only [exec_bind]
    rcases Mut.exec TripleRatchet.fromSessionState st with ⟨e | session, st1⟩
    · rfl
    · dsimp only
      have htr := tripleRatchet_decrypt_toOption_eq C spqr expected msg msgType₁ msgType₂ coins
        session
      rcases h1 : Mut.exec (TripleRatchet.decrypt C spqr expected msg msgType₁ coins) session with
        ⟨e1 | pt1, session1⟩ <;>
        rcases h2 : Mut.exec (TripleRatchet.decrypt C spqr expected msg msgType₂ coins) session with
          ⟨e2 | pt2, session2⟩
      · rfl
      · rw [h1, h2] at htr; injection (Prod.mk.inj htr).1
      · rw [h1, h2] at htr; injection (Prod.mk.inj htr).1
      · rw [h1, h2] at htr
        have hpt : pt1 = pt2 := Option.some.inj (Prod.mk.inj htr).1
        have hsess : session1 = session2 := (Prod.mk.inj htr).2
        subst hpt hsess; rfl

private theorem fromSessionState_outgoing_receiverChains {PQ : Type} [Inhabited PQ]
    (record : SessionState PQ) :
    (Mut.exec OutgoingTripleRatchet.fromSessionState record).2.receiverChains =
      record.receiverChains := by
  unfold OutgoingTripleRatchet.fromSessionState SessionState.takePqRatchetState
  rcases hsc : record.senderChain with _ | sc
  · simp [hsc]
  · simp only [hsc, exec_bind, exec_get, exec_modifyGet]
    split_ifs
    · rfl
    · rcases hrem : record.remoteIdentity with _ | remote <;> simp

private theorem messageEncrypt_receiverChains {PQ PQC : Type} [Inhabited PQ]
    (C : Crypto) (codec : SignalMessageProtoCodec) (spqr : Spqr PQ PQC)
    (addresses : Option RawBytes) (ptext : RawBytes) (coins : PQC)
    (record : SessionState PQ) :
    (SessionState.messageEncrypt C codec spqr addresses ptext coins record).2.receiverChains =
      record.receiverChains := by
  unfold SessionState.messageEncrypt
  have hf := fromSessionState_outgoing_receiverChains record
  rcases h1 : Mut.exec OutgoingTripleRatchet.fromSessionState record with ⟨e | session, taken⟩
  · simp
  · rw [h1] at hf
    dsimp only
    rcases h2 : Mut.exec (OutgoingTripleRatchet.encrypt C codec spqr ptext
        (record.encryptAddresses addresses) coins) session with ⟨e | message, session'⟩
    · simp
    · simpa [OutgoingTripleRatchet.applyToSessionState] using hf

/-- `Params.send` preserves `GhostState.Aligned` and updates `EpochGhost.ofGhost`. -/
theorem aligned_send_gen {PQC : Type} (P : Params RawBytes PQC)
    (g : GhostState RawBytes) (m : RawBytes) (r : PQC) (hal : g.Aligned) :
    (P.send g m r).1.Aligned ∧
    EpochGhost.ofGhost (P.send g m r).1 =
      if (SessionState.messageEncrypt P.C P.codec P.spqr (P.sendAddrs g.party) m r g.session).1.isOk
      then (EpochGhost.ofGhost g).send g.party
      else EpochGhost.ofGhost g := by
  unfold Params.send
  rcases hm : SessionState.messageEncrypt P.C P.codec P.spqr (P.sendAddrs g.party) m r g.session
    with ⟨e | msg, s⟩
  · exact ⟨hal, rfl⟩
  · have hs : s.receiverChains = g.session.receiverChains := by
      have hrc := messageEncrypt_receiverChains P.C P.codec P.spqr (P.sendAddrs g.party) m r g.session
      simpa [hm] using hrc
    simp only [Except.isOk, Except.toBool, ↓reduceIte]
    refine ⟨?_, ?_⟩
    · unfold GhostState.Aligned at hal ⊢
      dsimp only
      rw [hs]
      exact hal
    · dsimp only [EpochGhost.ofGhost, EpochGhost.send]
      rw [hs]

private theorem map_set_eq_self {α β : Type} (f : α → β) (l : List α) (idx : ℕ) {c c' : α}
    (hget : l[idx]? = some c) (hf : f c' = f c) :
    (l.set idx c').map f = l.map f := by
  induction l generalizing idx with
  | nil => simp at hget
  | cons a as ih =>
    cases idx with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      subst hget
      simp [List.set, hf]
    | succ idx =>
      simp only [List.getElem?_cons_succ] at hget
      simp [List.set, ih idx hget]

private theorem takeSkippedKey_map_senderRatchetKey (their : PublicKey) (counter : BitVec 32)
    (r : RatchetState) :
    (Mut.exec (RatchetState.takeSkippedKey their counter) r).2.receiverChains.map
      (·.senderRatchetKey) =
    r.receiverChains.map (·.senderRatchetKey) := by
  unfold RatchetState.takeSkippedKey
  rcases h1 : r.findReceiverChainIndex their with _ | chainIdx
  · simp [h1]
  · rcases h2 : r.receiverChains[chainIdx]? with _ | c
    · simp [h1, h2]
    · rcases h3 : c.messageKeys.findIdx? (fun mk => mk.counter == counter) with _ | pos
      · simp [h1, h2, h3]
      · rcases h4 : c.messageKeys[pos]? with _ | key
        · simp [h1, h2, h3, h4]
        · simp only [h1, h2, h3, h4, exec_bind, exec_get, exec_set, exec_pure]
          apply map_set_eq_self (·.senderRatchetKey) r.receiverChains chainIdx h2
          rfl

private theorem storeSkippedKey_map_senderRatchetKey (their : PublicKey) (key : MessageKeyGenerator)
    (r : RatchetState) :
    (Mut.exec (RatchetState.storeSkippedKey their key) r).2.receiverChains.map
      (·.senderRatchetKey) =
    r.receiverChains.map (·.senderRatchetKey) := by
  unfold RatchetState.storeSkippedKey
  rcases h1 : r.findReceiverChainIndex their with _ | chainIdx
  · simp [h1]
  · rcases h2 : r.receiverChains[chainIdx]? with _ | c
    · simp [h1, h2]
    · simp only [h1, h2, exec_bind, exec_get, exec_set]
      apply map_set_eq_self (·.senderRatchetKey) r.receiverChains chainIdx h2
      rfl

private theorem setReceiverChainKey_map_senderRatchetKey (their : PublicKey)
    (ck : LibsignalSession.ChainKey) (r : RatchetState) :
    (Mut.exec (RatchetState.setReceiverChainKey their ck) r).2.receiverChains.map
      (·.senderRatchetKey) =
    r.receiverChains.map (·.senderRatchetKey) := by
  unfold RatchetState.setReceiverChainKey
  rcases h1 : r.findReceiverChainIndex their with _ | chainIdx
  · simp [h1]
  · rcases h2 : r.receiverChains[chainIdx]? with _ | c
    · simp [h1, h2]
    · simp only [h1, h2, exec_bind, exec_get, exec_set]
      apply map_set_eq_self (·.senderRatchetKey) r.receiverChains chainIdx h2
      rfl

private theorem advanceChain_map_senderRatchetKey (F : ShaCompress) (their : PublicKey)
    (counter : BitVec 32) (fuel : ℕ) (ck : LibsignalSession.ChainKey) (r : RatchetState) :
    (Mut.exec (RatchetState.advanceChain F their counter fuel ck) r).2.receiverChains.map
      (·.senderRatchetKey) =
    r.receiverChains.map (·.senderRatchetKey) := by
  induction fuel generalizing ck r with
  | zero => rfl
  | succ fuel ih =>
    unfold RatchetState.advanceChain
    split
    · rw [exec_bind]
      have h1 := storeSkippedKey_map_senderRatchetKey their (ck.messageKeys F) r
      rcases hs : Mut.exec (RatchetState.storeSkippedKey their (ck.messageKeys F)) r with
        ⟨e | _, r1⟩
      · rw [hs] at h1; exact h1
      · rw [hs] at h1
        simp only [exec_bind, exec_liftE]
        rcases hn : ck.nextChainKey F with _ | ck'
        · exact h1
        · exact (ih ck' r1).trans h1
    · rfl

private theorem consumeMessageKey_map_senderRatchetKey (F : ShaCompress) (their : PublicKey)
    (ck : LibsignalSession.ChainKey) (counter : BitVec 32) (msgType : MessageType) (r : RatchetState) :
    (Mut.exec (RatchetState.consumeMessageKey F their ck counter msgType) r).2.receiverChains.map
      (·.senderRatchetKey) =
    r.receiverChains.map (·.senderRatchetKey) := by
  unfold RatchetState.consumeMessageKey
  by_cases hlt : counter < ck.index
  · simp only [hlt, ↓reduceIte, exec_bind]
    have h1 := takeSkippedKey_map_senderRatchetKey their counter r
    rcases ht : Mut.exec (RatchetState.takeSkippedKey their counter) r with ⟨e | opt, r1⟩
    · rw [ht] at h1; exact h1
    · rw [ht] at h1
      cases opt <;> simpa using h1
  · simp only [hlt, ↓reduceIte, exec_bind, exec_get]
    split
    · rfl
    · rw [exec_bind]
      have h1 := advanceChain_map_senderRatchetKey F their counter (counter - ck.index).toNat ck r
      rcases ha : Mut.exec (RatchetState.advanceChain F their counter (counter - ck.index).toNat ck) r
        with ⟨e | ck1, r1⟩
      · rw [ha] at h1; exact h1
      · rw [ha] at h1
        simp only [exec_bind, exec_liftE]
        rcases hn : ck1.nextChainKey F with _ | ck2
        · exact h1
        · simp only [exec_pure]
          have h2 := setReceiverChainKey_map_senderRatchetKey their ck2 r1
          rcases hs : Mut.exec (RatchetState.setReceiverChainKey their ck2) r1 with ⟨e | _, r2⟩ <;>
            · rw [hs] at h2
              exact h2.trans h1

private theorem dhRatchetStep_ok_map_senderRatchetKey (C : Crypto) (their : PublicKey)
    (coins : BitVec 256) (r r1 : RatchetState) (ck : LibsignalSession.ChainKey)
    (h : Mut.exec (RatchetState.dhRatchetStep C their coins) r = (.ok ck, r1)) :
    r1.receiverChains.map (·.senderRatchetKey) =
      (r.receiverChains.map (·.senderRatchetKey) ++ [their]).drop
        ((r.receiverChains.length + 1) - maxReceiverChains) := by
  unfold RatchetState.dhRatchetStep RatchetState.takeRootKey at h
  simp only [exec_bind, exec_get] at h
  rcases hsc : r.senderChain with _ | sc
  · simp [hsc] at h
  · simp only [hsc, exec_bind, exec_modifyGet, exec_liftE] at h
    rcases hrc1 : rootCreateChain C r.rootKey their sc.ratchetKey.privateKey with
      _ | ⟨newRootKey, receiverChainKey⟩
    · simp [hrc1] at h
    · simp only [hrc1, exec_modify, exec_pure] at h
      rcases hrc2 : rootCreateChain C newRootKey their (KeyPair.generate C coins).privateKey with
        _ | ⟨finalRootKey, senderChainKey⟩
      · simp [hrc2] at h
      · simp only [hrc2, Prod.mk.injEq, Except.ok.injEq] at h
        rcases h with ⟨_, rfl⟩
        simp [RatchetState.evictReceiverChains, List.map_drop, List.map_append]

private theorem ensureReceiverChain_ok_some_map_senderRatchetKey (C : Crypto) (their : PublicKey)
    (coins : BitVec 256) (r r1 : RatchetState) (ck : LibsignalSession.ChainKey) (i : ℕ)
    (hidx : r.receiverChains.findIdx? (·.senderRatchetKey == their) = some i)
    (h : Mut.exec (RatchetState.ensureReceiverChain C their coins) r = (.ok ck, r1)) :
    r1.receiverChains.map (·.senderRatchetKey) = r.receiverChains.map (·.senderRatchetKey) := by
  unfold RatchetState.ensureReceiverChain RatchetState.findReceiverChainKey
    RatchetState.findReceiverChainIndex at h
  simp only [exec_bind, exec_get, hidx, exec_liftE] at h
  rcases hget : r.receiverChains[i]? with _ | c
  · simp [hget] at h
  · rcases hck : c.chainKey with _ | ck'
    · simp [hget, hck] at h
    · simp only [hget, hck, exec_pure, Prod.mk.injEq, Except.ok.injEq] at h
      rcases h with ⟨_, rfl⟩
      rfl

private theorem ensureReceiverChain_ok_none_map_senderRatchetKey (C : Crypto) (their : PublicKey)
    (coins : BitVec 256) (r r1 : RatchetState) (ck : LibsignalSession.ChainKey)
    (hidx : r.receiverChains.findIdx? (·.senderRatchetKey == their) = none)
    (h : Mut.exec (RatchetState.ensureReceiverChain C their coins) r = (.ok ck, r1)) :
    r1.receiverChains.map (·.senderRatchetKey) =
      (r.receiverChains.map (·.senderRatchetKey) ++ [their]).drop
        ((r.receiverChains.length + 1) - maxReceiverChains) := by
  unfold RatchetState.ensureReceiverChain RatchetState.findReceiverChainKey
    RatchetState.findReceiverChainIndex at h
  simp only [exec_bind, exec_get, hidx, exec_liftE] at h
  exact dhRatchetStep_ok_map_senderRatchetKey C their coins r r1 ck h

private theorem tryDecryptFromRecord_ok_ratchet {PQ PQC : Type} [Inhabited PQ] (C : Crypto)
    (spqr : Spqr PQ PQC) (expected : Option RawBytes) (msg : SignalMessage)
    (msgType : MessageType) (coins : BitVec 256) (st st' : SessionState PQ) (pt : RawBytes)
    (h : SessionState.tryDecryptFromRecord C spqr expected msg msgType coins st = (.ok pt, st')) :
    ∃ ck r1 mkg r2,
      Mut.exec (RatchetState.ensureReceiverChain C msg.senderRatchetKey coins)
        ⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, maxForwardJumps⟩ =
        (.ok ck, r1) ∧
      Mut.exec (RatchetState.consumeMessageKey C.F msg.senderRatchetKey ck msg.counter msgType) r1 =
        (.ok mkg, r2) ∧
      st'.receiverChains = r2.receiverChains := by
  unfold SessionState.tryDecryptFromRecord at h
  split_ifs at h
  · simp at h
  · rcases hd : Mut.exec (SessionState.tryDecryptWithState C spqr expected msg msgType coins) st with
      ⟨e | ptext, updated⟩
    · simp [hd] at h
    · rw [hd] at h
      simp only [Prod.mk.injEq, Except.ok.injEq] at h
      rcases h with ⟨_, hst'⟩
      unfold SessionState.tryDecryptWithState TripleRatchet.fromSessionState
        SessionState.takeRatchetState SessionState.takePqRatchetState at hd
      rcases hrem : st.remoteIdentity with _ | remote
      · simp [hrem] at hd
      · simp only [hrem, exec_bind, exec_modifyGet, exec_get, exec_pure] at hd
        unfold TripleRatchet.decrypt at hd
        rw [exec_bind, exec_onRatchet] at hd
        rcases he : Mut.exec (RatchetState.ensureReceiverChain C msg.senderRatchetKey coins)
            ⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, maxForwardJumps⟩ with
          ⟨e | ck, r1⟩
        · simp [he] at hd
        · simp only [he, exec_bind, exec_onRatchet] at hd
          rcases hc : Mut.exec (RatchetState.consumeMessageKey C.F msg.senderRatchetKey ck
              msg.counter msgType) r1 with ⟨e | mkg, r2⟩
          · simp [hc] at hd
          · simp only [hc, exec_get] at hd
            cases hpan : spqr.recvPanics st.pqRatchetState msg.pqRatchet
            case true => simp [hpan] at hd
            simp only [hpan, Bool.false_eq_true, ↓reduceIte] at hd
            rcases hspqr : spqr.recv st.pqRatchetState msg.pqRatchet with ⟨_ | _⟩ | ⟨newPqrState, pqrKey⟩
            · simp [hspqr] at hd
            · simp [hspqr] at hd
            · simp only [hspqr, exec_pure, exec_bind] at hd
              split_ifs at hd
              · simp at hd
              · rcases haes : aesCbcDecrypt C.D (mkg.generateKeys C.F pqrKey).cipherKey
                    (mkg.generateKeys C.F pqrKey).iv msg.ciphertext with _ | pt'
                · simp [haes] at hd
                · have hupd : updated.receiverChains = r2.receiverChains := by
                    simpa [haes, map_eq_bind_pure_comp, TripleRatchet.applyToSessionState,
                      SessionState.clearUnacknowledgedPreKeyMessage] using
                      congrArg (fun x => x.2.receiverChains) hd.symm
                  refine ⟨ck, r1, mkg, r2, rfl, hc, ?_⟩
                  rw [← hst']
                  exact hupd

private theorem findIdx?_map {α β : Type} (f : α → β) (p : β → Bool) (l : List α) :
    (l.map f).findIdx? p = l.findIdx? (fun x => p (f x)) := by
  induction l with
  | nil => rfl
  | cons a as ih => simp [List.findIdx?_cons, ih]

private theorem find?_zip_of_findIdx?_none {α β : Type} (p : α → Bool)
    (ks : List α) (es : List β) (hnone : ks.findIdx? p = none) :
    (ks.zip es).find? (fun x => p x.1) = none := by
  induction ks generalizing es with
  | nil => rfl
  | cons k ks ih =>
    cases es with
    | nil => rfl
    | cons e es =>
      simp only [List.findIdx?_cons] at hnone
      cases hk : p k with
      | true => simp [hk] at hnone
      | false =>
        simp only [hk, Bool.false_eq_true, ↓reduceIte, Option.map_eq_none_iff] at hnone
        simp [List.zip_cons_cons, hk, ih es hnone]

private theorem find?_zip_of_findIdx?_some {α : Type} (p : α → Bool)
    (ks : List α) (es : List ℕ) (i : ℕ)
    (hlen : ks.length = es.length)
    (hsome : ks.findIdx? p = some i) :
    ∃ k, (ks.zip es).find? (fun x => p x.1) = some (k, es.getD i 0) := by
  induction ks generalizing es i with
  | nil => simp at hsome
  | cons k ks ih =>
    cases es with
    | nil => simp at hlen
    | cons e es =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [List.findIdx?_cons] at hsome
      cases hk : p k with
      | true =>
        simp only [hk, ↓reduceIte, Option.some.injEq] at hsome
        subst hsome
        exact ⟨k, by simp [List.zip_cons_cons, hk, List.getD]⟩
      | false =>
        simp only [hk, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at hsome
        rcases hsome with ⟨j, hj, rfl⟩
        rcases ih es j hlen hj with ⟨k', hk'⟩
        refine ⟨k', ?_⟩
        simpa [List.zip_cons_cons, List.find?_cons, hk, List.getD] using hk'

private theorem zip_drop {α β : Type} (as : List α) (bs : List β) (k : ℕ) :
    (as.drop k).zip (bs.drop k) = (as.zip bs).drop k := by
  induction k generalizing as bs with
  | zero => rfl
  | succ k ih =>
    cases as with
    | nil => simp
    | cons a as =>
      cases bs with
      | nil => simp
      | cons b bs => simp [List.drop_succ_cons, List.zip_cons_cons, ih]

private theorem zip_append_singleton {α β : Type} (as : List α) (bs : List β) (a : α) (b : β)
    (hlen : as.length = bs.length) :
    (as ++ [a]).zip (bs ++ [b]) = (as.zip bs) ++ [(a, b)] := by
  induction as generalizing bs with
  | nil =>
    cases bs with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons x xs ih =>
    cases bs with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp [List.zip_cons_cons, ih ys hlen]

/-- Successful `Params.receive` preserves `GhostState.Aligned` and receiver-chain length, and
commutes with `EpochGhost.recv`. -/
theorem recv_aligned_and_epochs_gen {PQC : Type}
    (P : Params RawBytes PQC)
    (g : GhostState RawBytes) (c : RawBytes) (rc : BitVec 256)
    (hal : g.Aligned)
    (hlen : g.session.receiverChains.length ≤ maxReceiverChains)
    (msg : SignalMessage)
    (hmsg : SignalMessage.tryFrom P.codec c = .ok msg)
    (x : GhostState RawBytes × ℕ × ℕ × RawBytes) (hx : P.receive g c rc = some x) :
    x.1.Aligned ∧
      x.1.session.receiverChains.length ≤ maxReceiverChains ∧
      (EpochGhost.ofGhost g).recv msg.senderRatchetKey = (x.2.1, EpochGhost.ofGhost x.1) ∧
      x.2.2.1 = msg.counter.toNat + 1 ∧ x.1.party = g.party := by
  unfold Params.receive at hx
  rw [hmsg] at hx
  dsimp only at hx
  rcases hdec : SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper
      rc g.session with ⟨e | pt, s⟩
  · simp [hdec] at hx
  · rw [hdec] at hx
    simp only [Option.some.injEq] at hx
    subst hx
    rcases tryDecryptFromRecord_ok_ratchet P.C P.spqr (P.expectedAddrs g.party) msg .whisper
        rc g.session s pt hdec with ⟨ck, r1, mkg, r2, he, hc, hsrc⟩
    have hc_map := consumeMessageKey_map_senderRatchetKey P.C.F msg.senderRatchetKey ck
      msg.counter .whisper r1
    rw [hc] at hc_map
    have hmap2 : s.receiverChains.map (·.senderRatchetKey) =
        r1.receiverChains.map (·.senderRatchetKey) := by
      rw [hsrc, hc_map]
    have hlen_ks : (g.session.receiverChains.map (·.senderRatchetKey)).length =
        g.chainEpochs.length := by
      rw [List.length_map, hal.symm]
    rcases hidx : g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey) with
      _ | i
    · have hidx_ks : (g.session.receiverChains.map (·.senderRatchetKey)).findIdx?
          (· == msg.senderRatchetKey) = none := by
        rw [findIdx?_map]; exact hidx
      have hfind_none : ((g.session.receiverChains.map (·.senderRatchetKey)).zip g.chainEpochs).find?
          (·.1 == msg.senderRatchetKey) = none :=
        find?_zip_of_findIdx?_none (· == msg.senderRatchetKey) _ _ hidx_ks
      have he_map := ensureReceiverChain_ok_none_map_senderRatchetKey P.C msg.senderRatchetKey
        rc _ r1 ck hidx he
      have hs_map : s.receiverChains.map (·.senderRatchetKey) =
          (g.session.receiverChains.map (·.senderRatchetKey) ++ [msg.senderRatchetKey]).drop
            ((g.session.receiverChains.length + 1) - maxReceiverChains) :=
        hmap2.trans he_map
      have hs_len : s.receiverChains.length =
          (g.session.receiverChains.length + 1) -
            ((g.session.receiverChains.length + 1) - maxReceiverChains) := by
        have := congrArg List.length hs_map
        simpa [List.length_drop, List.length_append, List.length_map] using this
      have hce : g.chainEpochs.length = g.session.receiverChains.length := hal
      have hmax : maxReceiverChains = 5 := rfl
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · unfold GhostState.Aligned
        simp only [hidx]
        rw [List.length_drop, List.length_append, List.length_singleton, hce, hs_len]
        omega
      · dsimp only
        omega
      · unfold EpochGhost.recv EpochGhost.ofGhost
        dsimp only
        have hdrop_eq : (g.chainEpochs ++ [g.epoch + 1]).length - s.receiverChains.length =
            (g.session.receiverChains.length + 1) - maxReceiverChains := by
          rw [List.length_append, List.length_singleton, hce, hs_len]
          omega
        have hcs_len : (((g.session.receiverChains.map (·.senderRatchetKey)).zip g.chainEpochs) ++
            [(msg.senderRatchetKey, g.epoch + 1)]).length - maxReceiverChains =
            (g.session.receiverChains.length + 1) - maxReceiverChains := by
          simp [List.length_append, List.length_zip, List.length_map, hce]
        simp only [hidx, hfind_none, hs_map, hdrop_eq, hcs_len, zip_drop,
          zip_append_singleton _ _ _ _ hlen_ks]
      · rfl
      · rfl
    · have hidx_ks : (g.session.receiverChains.map (·.senderRatchetKey)).findIdx?
          (· == msg.senderRatchetKey) = some i := by
        rw [findIdx?_map]; exact hidx
      rcases find?_zip_of_findIdx?_some (· == msg.senderRatchetKey) _ _ i hlen_ks hidx_ks with
        ⟨k', hfind_some⟩
      have he_map := ensureReceiverChain_ok_some_map_senderRatchetKey P.C msg.senderRatchetKey
        rc _ r1 ck i hidx he
      have hs_map : s.receiverChains.map (·.senderRatchetKey) =
          g.session.receiverChains.map (·.senderRatchetKey) :=
        hmap2.trans he_map
      have hs_len : s.receiverChains.length = g.session.receiverChains.length := by
        have := congrArg List.length hs_map
        simpa [List.length_map] using this
      have hce : g.chainEpochs.length = g.session.receiverChains.length := hal
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · unfold GhostState.Aligned
        simp only [hidx]
        rw [List.length_drop, hce, hs_len]
        omega
      · dsimp only
        omega
      · unfold EpochGhost.recv EpochGhost.ofGhost
        dsimp only
        have hdrop_zero : g.chainEpochs.length - s.receiverChains.length = 0 := by omega
        simp only [hidx, hfind_some, hs_map, hdrop_zero, List.drop_zero]
      · rfl
      · rfl

/-- `initiateState` produces an aligned `GhostState` at initial `EpochGhost` `⟨0, [(⟨b.spkPub⟩, 0)]⟩`. -/
theorem initiateState_aligned_and_epochs {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {P : Party} {me : LocalIdentity} {b : PreKeyBundleFields} {t : List.Vector (BitVec 8) initiateTapeLen}
    {x : RecordExtras} {g : GhostState RawBytes}
    (h : initiateState X W P me b t = some (x, g)) :
    g.Aligned ∧
      g.session.receiverChains.length ≤ maxReceiverChains ∧
      g.party = P ∧
      EpochGhost.ofGhost g = ⟨0, [(⟨b.spkPub⟩, 0)]⟩ := by
  unfold initiateState at h
  rcases hinit : SignalPqxdh.Model.initiateKeys (modelPrims X W) (initiateInput W me b t) with
    _ | ⟨dk, hdr⟩
  · simp [hinit] at h
  · rw [hinit] at h; dsimp only at h
    unfold initializeInitiatorSession at h
    dsimp only [bind, Except.bind, pure, Except.pure] at h
    rcases hrc : rootCreateChain W.C (HKDF.bytesToKey32 (ofU8 dk.rootKey)) ⟨b.spkPub⟩
        (KeyPair.generate W.C (HKDF.bytesToKey32 ((t.toList.drop 160).take 32))).privateKey with
      _ | ⟨rk', ck'⟩
    · simp [hrc] at h
    · rw [hrc] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      refine ⟨?_, ?_, rfl, ?_⟩
      · simp [GhostState.Aligned, SessionState.new, SessionState.addReceiverChain,
          SessionState.setSenderChain, SessionState.setUnacknowledgedPreKeyMessage,
          maxReceiverChains]
      · simp [SessionState.new, SessionState.addReceiverChain,
          SessionState.setSenderChain, SessionState.setUnacknowledgedPreKeyMessage,
          maxReceiverChains]
      · simp [EpochGhost.ofGhost, SessionState.new, SessionState.addReceiverChain,
          SessionState.setSenderChain, SessionState.setUnacknowledgedPreKeyMessage,
          maxReceiverChains]

/-- `recvPrekeyState` produces an aligned `GhostState` at initial `EpochGhost`
`⟨1, [(msg.senderRatchetKey, 1)]⟩`. -/
theorem recvPrekeyState_aligned_and_epochs {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {P : Party} {me : LocalIdentity} {k : ResponderPreKeySecrets} {m : PreKeyMessageFields} {rc : BitVec 256}
    {x : RecordExtras} {g : GhostState RawBytes} {pt : RawBytes}
    (h : recvPrekeyState X W P me k m rc = some (some (x, g, pt))) :
    g.Aligned ∧
      g.session.receiverChains.length ≤ maxReceiverChains ∧
      g.party = P ∧
      ∃ msg, SignalMessage.tryFrom protoSignalCodec m.inner = .ok msg ∧
        EpochGhost.ofGhost g = ⟨1, [(msg.senderRatchetKey, 1)]⟩ := by
  unfold recvPrekeyState at h
  rcases htf : SignalMessage.tryFrom protoSignalCodec m.inner with _ | inner
  · simp [htf] at h
  · rw [htf] at h; dsimp only at h
    split_ifs at h with hids
    · simp at h
    · rcases hacc : SignalPqxdh.Model.acceptKeys (modelPrims X W) (acceptInput W me k m) with
        _ | dk
      · simp [hacc] at h
      · rw [hacc] at h; dsimp only at h
        let st0 : SessionState RawBytes :=
          initializeRecipientSession (pqxdhSpqrSession W)
            ⟨(keyPairOf W.C me.idPriv).publicKey⟩
            ⟨⟨m.idPub⟩⟩ (keyPairOf W.C k.spkPriv) (HKDF.bytesToKey32 (ofU8 dk.rootKey))
            (HKDF.bytesToKey32 (ofU8 dk.chainKey)) (HKDF.bytesToKey32 (ofU8 dk.pqrKey))
        change (match SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
            ((pqxdhSessionParams W).expectedAddrs P) inner .preKey rc st0 with
          | (.ok pt, st) => some (some (responderRecordExtras me m, ⟨P, st, 1, [1]⟩, pt))
          | (.error .panic, _) => none
          | (.error _, _) => some none) = some (some (x, g, pt)) at h
        rcases hdec : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
            ((pqxdhSessionParams W).expectedAddrs P) inner .preKey rc st0 with ⟨e | pt', st⟩
        · rw [hdec] at h; cases e <;> simp at h
        · rw [hdec] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl, rfl⟩
          rcases tryDecryptFromRecord_ok_ratchet W.C (pqxdhSpqrSession W)
              ((pqxdhSessionParams W).expectedAddrs P) inner .preKey rc st0 st pt' hdec with
            ⟨ck, r1, mkg, r2, he, hc, hsrc⟩
          have hc_map := consumeMessageKey_map_senderRatchetKey W.C.F inner.senderRatchetKey ck
            inner.counter .preKey r1
          rw [hc] at hc_map
          have hmap2 : st.receiverChains.map (·.senderRatchetKey) =
              r1.receiverChains.map (·.senderRatchetKey) := by
            rw [hsrc, hc_map]
          have hidx0 :
              st0.receiverChains.findIdx? (·.senderRatchetKey == inner.senderRatchetKey) = none :=
            rfl
          have he_map := ensureReceiverChain_ok_none_map_senderRatchetKey W.C
            inner.senderRatchetKey rc _ r1 ck hidx0 he
          have hst_map : st.receiverChains.map (·.senderRatchetKey) = [inner.senderRatchetKey] := by
            have h0 : st0.receiverChains = [] := rfl
            simpa [h0, maxReceiverChains] using hmap2.trans he_map
          have hst_len : st.receiverChains.length = 1 := by
            have := congrArg List.length hst_map
            simpa [List.length_map] using this
          refine ⟨?_, ?_, rfl, inner, rfl, ?_⟩
          · unfold GhostState.Aligned
            dsimp only
            exact hst_len.symm
          · dsimp only
            have hmax : maxReceiverChains = 5 := rfl
            omega
          · dsimp only [EpochGhost.ofGhost]
            rw [hst_map]
            rfl

private theorem extractLsb'_zero_bytesToKey32_cons (b : BitVec 8) (acc : BitVec 256) :
    ((acc <<< 8) ||| b.zeroExtend 256).extractLsb' 0 8 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', Nat.zero_add, hi, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have h256 : i < 256 := by omega
  simp [hi, h256]

private theorem extractLsb'_succ_bytesToKey32_cons (b : BitVec 8) (acc : BitVec 256) (j : ℕ)
    (hj : j + 1 < 32) :
    ((acc <<< 8) ||| b.zeroExtend 256).extractLsb' (8 * (j + 1)) 8 =
      acc.extractLsb' (8 * j) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have h1 : ¬ (8 * (j + 1) + i < 8) := by omega
  have h2 : 8 * (j + 1) + i < 256 := by omega
  have h3 : 8 * (j + 1) + i - 8 = 8 * j + i := by omega
  have hb : b.getLsbD (8 * (j + 1) + i) = false := by
    unfold BitVec.getLsbD
    exact Nat.testBit_lt_two_pow
      (lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by decide) (by omega)))
  simp [h1, h2, h3, hb]

private theorem extractLsb'_bytesToKey32 (bs : List (BitVec 8)) (j : ℕ)
    (hj : j < bs.length) (h32 : j < 32) :
    (HKDF.bytesToKey32 bs).extractLsb' (8 * j) 8 = bs[j] := by
  induction bs generalizing j with
  | nil => simp at hj
  | cons b rest ih =>
    cases j with
    | zero =>
      simpa [HKDF.bytesToKey32] using extractLsb'_zero_bytesToKey32_cons b (HKDF.bytesToKey32 rest)
    | succ j =>
      have hcons : HKDF.bytesToKey32 (b :: rest) =
          (HKDF.bytesToKey32 rest <<< 8) ||| b.zeroExtend 256 := rfl
      rw [hcons, extractLsb'_succ_bytesToKey32_cons b (HKDF.bytesToKey32 rest) j h32,
        List.getElem_cons_succ]
      exact ih j (by simpa using hj) (by omega)

private theorem keyToBytes32_bytesToKey32 (bs : List (BitVec 8)) (h : bs.length = 32) :
    HMAC.keyToBytes32 (HKDF.bytesToKey32 bs) = bs := by
  refine List.ext_getElem (by simp [HMAC.keyToBytes32, h]) fun j h1 h2 => ?_
  simp only [HMAC.keyToBytes32, List.getElem_ofFn]
  exact extractLsb'_bytesToKey32 bs j h2 (by omega)

theorem keyPairOf_eq_keyPair_generate (C : Crypto) (sk : List.Vector (BitVec 8) 32) :
    keyPairOf C sk = KeyPair.generate C (HKDF.bytesToKey32 sk.toList) := by
  unfold keyPairOf KeyPair.generate
  have hvec : Ratchet.keyToBytesVec32 (HKDF.bytesToKey32 sk.toList) = sk := by
    apply Subtype.ext
    exact keyToBytes32_bytesToKey32 sk.toList sk.2
  rw [hvec]

private theorem tryDecryptFromRecord_ok_receiverChains_length_one_of_nil {PQ PQC : Type}
    [Inhabited PQ] (C : Crypto) (spqr : Spqr PQ PQC) (expected : Option RawBytes)
    (msg : SignalMessage) (msgType : MessageType) (coins : BitVec 256)
    (st st' : SessionState PQ) (pt : RawBytes)
    (hnil : st.receiverChains = [])
    (h : SessionState.tryDecryptFromRecord C spqr expected msg msgType coins st = (.ok pt, st')) :
    st'.receiverChains.length = 1 := by
  obtain ⟨ck, r1, mkg, r2, he, hc, hrc⟩ :=
    tryDecryptFromRecord_ok_ratchet C spqr expected msg msgType coins st st' pt h
  let r0 : RatchetState :=
    ⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, maxForwardJumps⟩
  have hidx : r0.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey) = none := by
    simp [r0, hnil]
  have hr1 := ensureReceiverChain_ok_none_map_senderRatchetKey C msg.senderRatchetKey coins
    r0 r1 ck hidx he
  have hr2 := consumeMessageKey_map_senderRatchetKey C.F msg.senderRatchetKey ck msg.counter
    msgType r1
  rw [hc] at hr2
  have hmap : st'.receiverChains.map (·.senderRatchetKey) = [msg.senderRatchetKey] := by
    rw [hrc, hr2, hr1]; simp [r0, hnil, maxReceiverChains]
  have hlen := congrArg List.length hmap
  simpa using hlen

private theorem params_receive_initB_eq {PQ PQC : Type} [Inhabited PQ] (P : Params PQ PQC)
    (k : InitKeys) (innerBytes : RawBytes) (rc : BitVec 256) :
    P.receive (P.initB k) innerBytes rc =
      match SignalMessage.tryFrom P.codec innerBytes with
      | .error _ => none
      | .ok inner =>
        match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs .B) inner .whisper rc
            (P.initB k).session with
        | (.ok pt, st) => some (⟨.B, st, 1, [1]⟩, 1, inner.counter.toNat + 1, pt)
        | (.error _, _) => none := by
  unfold Params.receive
  rcases SignalMessage.tryFrom P.codec innerBytes with _ | inner
  · rfl
  · dsimp only
    have hparty : (P.initB k).party = .B := rfl
    rw [hparty]
    rcases hdec : SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs .B)
        inner .whisper rc (P.initB k).session with ⟨e | pt, st⟩
    · rfl
    · have hnil : (P.initB k).session.receiverChains = [] := rfl
      have hlen : st.receiverChains.length = 1 :=
        tryDecryptFromRecord_ok_receiverChains_length_one_of_nil P.C P.spqr
          (P.expectedAddrs .B) inner .whisper rc (P.initB k).session st pt hnil hdec
      have hidx : (P.initB k).session.receiverChains.findIdx?
          (fun c : ReceiverChain => c.senderRatchetKey == inner.senderRatchetKey) = none := rfl
      have hep : (P.initB k).epoch = 0 := rfl
      have hce : (P.initB k).chainEpochs = [] := rfl
      dsimp only; rw [hidx, hep, hce, hlen]; rfl

private theorem tryDecryptFromRecord_spqr_eq_of_recv_eq {PQ PQC₁ PQC₂ : Type} [Inhabited PQ]
    (C : Crypto) (spqr₁ : Spqr PQ PQC₁) (spqr₂ : Spqr PQ PQC₂)
    (hrecv : spqr₁.recv = spqr₂.recv) (hpan : spqr₁.recvPanics = spqr₂.recvPanics)
    (expected : Option RawBytes) (msg : SignalMessage) (ty : MessageType)
    (coins : BitVec 256) (st : SessionState PQ) :
    SessionState.tryDecryptFromRecord C spqr₁ expected msg ty coins st =
      SessionState.tryDecryptFromRecord C spqr₂ expected msg ty coins st := by
  have hd : TripleRatchet.decrypt C spqr₁ expected msg ty coins =
      TripleRatchet.decrypt C spqr₂ expected msg ty coins := by
    unfold TripleRatchet.decrypt; rw [hrecv, hpan]
  unfold SessionState.tryDecryptFromRecord SessionState.tryDecryptWithState
  rw [hd]

/-- When `acceptKeys` succeeds with `dk`, `(recvPrekeyState X W .B meB k m rc).join` agrees with
`(paramsPqBIds W ...).receive` on `.initB`. -/
theorem recvPrekeyState_join_eq_initB_receive (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (meB : LocalIdentity) (k : ResponderPreKeySecrets) (m : PreKeyMessageFields) (rc aliceCoins : BitVec 256)
    (dk : SignalPqxdh.DRKey)
    (hids : m.spkId = k.spkId ∧ m.kpkId = k.kpkId)
    (hacc : SignalPqxdh.Model.acceptKeys (modelPrims X W) (acceptInput W meB k m) = some dk) :
    let P := paramsPqBIds W ⟨⟨m.idPub⟩⟩ ⟨(keyPairOf W.C meB.idPriv).publicKey⟩
    let kInit := initKeysOfSampled (HKDF.bytesToKey32 k.spkPriv.toList)
      ((HKDF.bytesToKey32 (ofU8 dk.rootKey), HKDF.bytesToKey32 (ofU8 dk.chainKey)),
       aliceCoins, HKDF.bytesToKey32 (ofU8 dk.pqrKey))
    (recvPrekeyState X W .B meB k m rc).join =
      (P.receive (P.initB kInit) m.inner rc).map
        (fun (gB, _, _, pt) => (responderRecordExtras meB m, gB, pt)) := by
  dsimp only
  set idA : IdentityKey := ⟨⟨m.idPub⟩⟩
  set idB : IdentityKey := ⟨(keyPairOf W.C meB.idPriv).publicKey⟩
  set P := paramsPqBIds W idA idB
  set kInit := initKeysOfSampled (HKDF.bytesToKey32 k.spkPriv.toList)
    ((HKDF.bytesToKey32 (ofU8 dk.rootKey), HKDF.bytesToKey32 (ofU8 dk.chainKey)),
     aliceCoins, HKDF.bytesToKey32 (ofU8 dk.pqrKey))
  set g0 := P.initB kInit
  unfold recvPrekeyState
  rw [params_receive_initB_eq P kInit m.inner rc]
  rcases htf : SignalMessage.tryFrom protoSignalCodec m.inner with _ | inner
  · have htf' : SignalMessage.tryFrom P.codec m.inner = .error ‹_› := htf
    rw [htf']; rfl
  · have htf' : SignalMessage.tryFrom P.codec m.inner = .ok inner := htf
    rw [htf']; dsimp only
    have hids' : ¬ (m.spkId ≠ k.spkId ∨ m.kpkId ≠ k.kpkId) := by simp [hids.1, hids.2]
    simp only [hids', ↓reduceIte, hacc]
    have hkp : keyPairOf W.C k.spkPriv = KeyPair.generate W.C (HKDF.bytesToKey32 k.spkPriv.toList) :=
      keyPairOf_eq_keyPair_generate W.C k.spkPriv
    have hst0 : initializeRecipientSession (pqxdhSpqrSession W)
        idB idA (keyPairOf W.C k.spkPriv)
        (HKDF.bytesToKey32 (ofU8 dk.rootKey))
        (HKDF.bytesToKey32 (ofU8 dk.chainKey))
        (HKDF.bytesToKey32 (ofU8 dk.pqrKey)) = g0.session := by
      rw [hkp]; rfl
    have haddr : (pqxdhSessionParams W).expectedAddrs .B = P.expectedAddrs .B := rfl
    have hP_C : P.C = W.C := rfl
    have hP_spqr : P.spqr = spqrV1SessionUniformCoins W.C.F W.Q.K := rfl
    have hg0_sess : (P.initB kInit).session = g0.session := rfl
    rw [hst0, haddr, hP_C, hP_spqr, hg0_sess,
        tryDecryptFromRecord_spqr_eq_of_recv_eq W.C (pqxdhSpqrSession W) (spqrV1SessionUniformCoins W.C.F W.Q.K) rfl rfl]
    have hopt := tryDecryptFromRecord_toOption_eq W.C (spqrV1SessionUniformCoins W.C.F W.Q.K)
      (P.expectedAddrs .B) inner .preKey .whisper rc g0.session
    rcases hd1 : SessionState.tryDecryptFromRecord W.C (spqrV1SessionUniformCoins W.C.F W.Q.K)
        (P.expectedAddrs .B) inner .preKey rc g0.session with ⟨e1 | pt1, st1⟩ <;>
      rcases hd2 : SessionState.tryDecryptFromRecord W.C (spqrV1SessionUniformCoins W.C.F W.Q.K)
          (P.expectedAddrs .B) inner .whisper rc g0.session with ⟨e2 | pt2, st2⟩
    · cases e1 <;> rfl
    · rw [hd1, hd2] at hopt; injection (Prod.mk.inj hopt).1
    · rw [hd1, hd2] at hopt; injection (Prod.mk.inj hopt).1
    · rw [hd1, hd2] at hopt
      have hpt : pt1 = pt2 := Option.some.inj (Prod.mk.inj hopt).1
      have hst : st1 = st2 := (Prod.mk.inj hopt).2
      subst hpt hst; rfl

/-! ## Per-entry `CliSpecPqxdh` commutation on `CliDirState` -/

private theorem encodeDir_eq_of_session_eq (W : PEParams) (st : PqParty) (x : RecordExtras)
    (g₁ g₂ : GhostState RawBytes) (hs : g₁.session = g₂.session) :
    encodeDir W { st with session := some (x, g₁) } =
      encodeDir W { st with session := some (x, g₂) } := by
  unfold encodeDir encodeRecordUnderExtras
  dsimp only
  rw [hs]

private theorem paramsPqIds_receive_eq_paramsPq (W : PEParams) (idA idB : IdentityKey)
    (g : GhostState RawBytes) (c : RawBytes) (rc : BitVec 256) :
    (paramsPqIds W idA idB).receive g c rc = (pqxdhSessionParams W).receive g c rc := by
  unfold Params.receive paramsPqIds pqxdhSessionParams Params.expectedAddrs
  cases g.party <;> rfl

/-- `cliPqRecvWhisperDir` commutes with `(paramsPqBIds W idA idB).receive` through `cliDirStateOf`. -/
theorem cliPqRecvWhisperDir_eq_paramsPqBIds_receive
    {run : CliRun} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (hspec : CliSpecPqxdh run X W) (st : PqParty) (hwf : PqxdhPartyInSpecDomain W st)
    (idA idB : IdentityKey) (x : RecordExtras) (g : GhostState RawBytes) (k : IdentityKey)
    (hsess : st.session = some (x, g)) (hal : g.Aligned)
    (hlen : g.session.receiverChains.length ≤ maxReceiverChains)
    (hp_party : g.party = st.party)
    (hrem : g.session.remoteIdentity = some k) (htrust : st.trusts k = true)
    (c : RawBytes) (rc : BitVec 256) (hc : (wireWhisper :: c).length < 2 ^ 32)
    (hcap : (wireWhisper :: c).length ≤ stdinCapBytes) :
    cliPqRecvWhisperDir run (cliDirStateOf W st) c rc =
      ((paramsPqBIds W idA idB).receive g c rc).map (fun (g', t, idx, pt) =>
        (cliDirStateOf W { st with peerId := some k, session := some (x, g') }, t, idx, pt)) := by
  let _ := hp_party
  have hc' : c.length < 2 ^ 32 := by simp at hc; omega
  have hnc : ¬ (wireWhisper :: c).length > stdinCapBytes := Nat.not_lt.mpr hcap
  have hnd : PqDirIdsNodup st := pqDirIdsNodup_of_wfPq hwf
  have hrun := (hspec st hwf).2.2.1 c rc hc'
  simp only [hnc, ↓reduceIte] at hrun
  rw [paramsPqBIds_receive_eq, paramsPqIds_receive_eq_paramsPq]
  unfold cliPqRecvWhisperDir
  have hp : (cliDirStateOf W st).party = st.party := rfl
  have hdf : (cliDirStateOf W st).dirFiles = encodeDir W st := rfl
  have hcp : (cliDirStateOf W st).candidatePaths = pqPartyCandidatePathsOf st := rfl
  have hep : (cliDirStateOf W st).epochs = EpochGhost.ofGhost g := by
    simp [cliDirStateOf, hsess]
  rw [hp, hdf, cliPqRecvInputsFromFiles_encodeDir_eq, hrun]
  have hP_C : (pqxdhSessionParams W).C = W.C := rfl
  have hP_codec : (pqxdhSessionParams W).codec = protoSignalCodec := rfl
  have hP_spqr : (pqxdhSessionParams W).spqr = pqxdhSpqrSession W := rfl
  rcases htry : SignalMessage.tryFrom protoSignalCodec c with _ | msg
  · have hmod : pqRecvWhisperModel W st c rc = some none := by
      simp [pqRecvWhisperModel, hsess, htry]
    have hrec_none : (pqxdhSessionParams W).receive g c rc = none := by
      unfold Params.receive; rw [hP_codec, htry]
    rw [hmod, hrec_none]; rfl
  · rcases hdec : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
        ((pqxdhSessionParams W).expectedAddrs g.party) msg .whisper rc g.session with ⟨err | pt, s⟩
    · have hrec_none : (pqxdhSessionParams W).receive g c rc = none := by
        unfold Params.receive; rw [hP_codec, htry]; dsimp only; rw [hP_C, hP_spqr, hdec]
      rw [hrec_none]
      cases err with
      | panic =>
        have hmod : pqRecvWhisperModel W st c rc = none := by
          simp [pqRecvWhisperModel, pqxdhSessionDecryptModel, hsess, htry, hdec]
        rw [hmod]; rfl
      | _ =>
        have hmod : pqRecvWhisperModel W st c rc = some none := by
          simp [pqRecvWhisperModel, pqxdhSessionDecryptModel, hsess, htry, hdec]
        rw [hmod]; rfl
    · have hs_rem : s.remoteIdentity = some k := by
        have hvr := (Closure.Version.tryDecryptFromRecord_sessionVersion_remoteIdentity
          W.C (pqxdhSpqrSession W) ((pqxdhSessionParams W).expectedAddrs g.party) msg .whisper rc g.session).2
        rw [hdec, hrem] at hvr
        exact hvr
      have hnt : (!st.trusts k) = false := by simp [htrust]
      let st_raw : PqParty :=
        { st with peerId := some k, session := some (x, { g with session := s }) }
      have hmod : pqRecvWhisperModel W st c rc = some (some (st_raw, pt)) := by
        simp [pqRecvWhisperModel, pqxdhSessionDecryptModel, hsess, htry, hdec, hs_rem, hnt, st_raw]
      have hstep : PqStep X W st st_raw := PqStep.recvWhisper c rc st_raw pt hc' hmod
      have hrb := readBackDir_pqObserve_ok_eq (pqRecvInputs W st (wireWhisper :: c) rc).files hnd hstep
      rcases hrec : (pqxdhSessionParams W).receive g c rc with _ | ⟨g', t', idx, pt'⟩
      · exfalso
        unfold Params.receive at hrec
        rw [hP_codec, htry] at hrec; dsimp only at hrec; rw [hP_C, hP_spqr, hdec] at hrec
        simp at hrec
      · have hrae := recv_aligned_and_epochs_gen (pqxdhSessionParams W) g c rc hal hlen msg
          (by rw [hP_codec]; exact htry) (g', t', idx, pt') hrec
        have hg'_sess_pt : g'.session = s ∧ pt' = pt := by
          unfold Params.receive at hrec
          rw [hP_codec, htry] at hrec; dsimp only at hrec; rw [hP_C, hP_spqr, hdec] at hrec
          simp only [Option.some.injEq, Prod.mk.injEq] at hrec
          exact ⟨hrec.1.symm ▸ rfl, hrec.2.2.2.symm⟩
        have hdir : encodeDir W st_raw =
            encodeDir W { st with peerId := some k, session := some (x, g') } :=
          encodeDir_eq_of_session_eq W { st with peerId := some k } x
            { g with session := s } g' hg'_sess_pt.1.symm
        have hidx_eq : idx = msg.counter.toNat + 1 := hrae.2.2.2.1
        rw [hmod]
        simp only [pqxdhExpectedOutcome, observe, Option.map]
        rw [hcp, hrb, hep, hrae.2.2.1, hdir, hidx_eq, hg'_sess_pt.2]
        rfl

/-- On a party without a session, `cliPqRecvPrekeyInitDir` commutes with `(pqRecvPrekeyModel X W st m rc).join`
through `cliDirStateOf`. -/
theorem cliPqRecvPrekeyInitDir_eq_pqRecvPrekeyModel
    {run : CliRun} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (hspec : CliSpecPqxdh run X W) (st : PqParty) (hwf : PqxdhPartyInSpecDomain W st) (hnone : st.session = none)
    (m : PreKeyMessageFields) (rc : BitVec 256) (hm : m.inner.length + 2048 < 2 ^ 32)
    (hcap : (wirePrekey :: m.bytes).length ≤ stdinCapBytes) :
    (cliPqRecvPrekeyInitDir run (cliDirStateOf W st) m rc).map (fun (s', _, _, pt) => (s', pt)) =
      ((pqRecvPrekeyModel X W st m rc).join).map (fun (st', pt) => (cliDirStateOf W st', pt)) := by
  have hnd : PqDirIdsNodup st := pqDirIdsNodup_of_wfPq hwf
  have hnc : ¬ (wirePrekey :: m.bytes).length > stdinCapBytes := Nat.not_lt.mpr hcap
  have hvac : ∀ x g, st.session = some (x, g) → PqSessionMatches x g m := by
    intro _ _ h; rw [hnone] at h; cases h
  have hrun := (hspec st hwf).2.2.2.1 m rc hm hvac
  simp only [hnc, ↓reduceIte] at hrun
  unfold cliPqRecvPrekeyInitDir
  have hp : (cliDirStateOf W st).party = st.party := rfl
  have hdf : (cliDirStateOf W st).dirFiles = encodeDir W st := rfl
  have hcp : (cliDirStateOf W st).candidatePaths = pqPartyCandidatePathsOf st := rfl
  rw [hp, hdf, cliPqRecvInputsFromFiles_encodeDir_eq, hrun]
  rcases hmod : pqRecvPrekeyModel X W st m rc with _ | (_ | ⟨st', pt⟩)
  · rfl
  · rfl
  · have hstep : PqStep X W st st' := PqStep.recvPrekey m rc st' pt hm hvac hmod
    have hrb := readBackDir_pqObserve_ok_eq (pqRecvInputs W st (wirePrekey :: m.bytes) rc).files hnd hstep
    have hshape := pqStep_preserves_shape hstep
    have hmod' := hmod
    unfold pqRecvPrekeyModel at hmod'
    rcases htry : SignalMessage.tryFrom protoSignalCodec m.inner with _ | inner
    · simp [htry] at hmod'
    · rw [htry, hnone] at hmod'
      dsimp only at hmod'
      split_ifs at hmod' with hnt
      · simp at hmod'
      · rcases hk : preKeysNamedBy st m with _ | k
        · simp [hk] at hmod'
        · rw [hk] at hmod'
          dsimp only at hmod'
          rcases hrps : recvPrekeyState X W st.party st.me k m rc with _ | (_ | ⟨x, g, pt'⟩)
          · simp [hrps] at hmod'
          · simp [hrps] at hmod'
          · rw [hrps] at hmod'
            dsimp only at hmod'
            rcases hmk : markKyberUsed st m with _ | st1
            · simp [hmk] at hmod'
            · rw [hmk] at hmod'
              dsimp only at hmod'
              simp only [Option.some.injEq, Prod.mk.injEq] at hmod'
              rcases hmod' with ⟨hst', rfl⟩
              rcases (recvPrekeyState_aligned_and_epochs hrps).2.2.2 with ⟨msg', htry', hep⟩
              rw [htry] at htry'
              injection htry' with hmsg_eq
              subst hmsg_eq
              simp only [pqxdhExpectedOutcome, observe, Option.join, Option.bind, Option.map]
              dsimp only [id]
              rw [hcp, hrb]
              unfold cliDirStateOf
              rw [hshape.1, hshape.2.2.2.2.2.2.1]
              have hsess' : st'.session = some (x, g) := by rw [← hst']
              rw [hsess']
              dsimp only
              rw [hep]

/-- On a matching session, `cliPqRecvPrekeyMatchingDir` commutes with
`(paramsPqBIds W idA idB).receive` through `cliDirStateOf`. -/
theorem cliPqRecvPrekeyMatchingDir_eq_paramsPqBIds_receive
    {run : CliRun} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (hspec : CliSpecPqxdh run X W) (st : PqParty) (hwf : PqxdhPartyInSpecDomain W st)
    (idA idB : IdentityKey) (x : RecordExtras) (g : GhostState RawBytes) (m : PreKeyMessageFields)
    (hsess : st.session = some (x, g)) (hal : g.Aligned)
    (hlen : g.session.receiverChains.length ≤ maxReceiverChains)
    (hp_party : g.party = st.party)
    (hmatch : PqSessionMatches x g m)
    (hrem : g.session.remoteIdentity = some ⟨⟨m.idPub⟩⟩)
    (htrust : st.trusts ⟨⟨m.idPub⟩⟩ = true)
    (rc : BitVec 256) (hm : m.inner.length + 2048 < 2 ^ 32)
    (hcap : (wirePrekey :: m.bytes).length ≤ stdinCapBytes) :
    cliPqRecvPrekeyMatchingDir run (cliDirStateOf W st) m rc =
      ((paramsPqBIds W idA idB).receive g m.inner rc).map (fun (g', t, idx, pt) =>
        (cliDirStateOf W { st with peerId := some ⟨⟨m.idPub⟩⟩, session := some (x, g') },
          t, idx, pt)) := by
  let _ := hp_party
  have hnd : PqDirIdsNodup st := pqDirIdsNodup_of_wfPq hwf
  have hnc : ¬ (wirePrekey :: m.bytes).length > stdinCapBytes := Nat.not_lt.mpr hcap
  have hmatch_all : ∀ x' g', st.session = some (x', g') → PqSessionMatches x' g' m := by
    intro x' g' h; rw [hsess] at h; cases h; exact hmatch
  have hrun := (hspec st hwf).2.2.2.1 m rc hm hmatch_all
  simp only [hnc, ↓reduceIte] at hrun
  rw [paramsPqBIds_receive_eq, paramsPqIds_receive_eq_paramsPq]
  unfold cliPqRecvPrekeyMatchingDir
  have hp : (cliDirStateOf W st).party = st.party := rfl
  have hdf : (cliDirStateOf W st).dirFiles = encodeDir W st := rfl
  have hcp : (cliDirStateOf W st).candidatePaths = pqPartyCandidatePathsOf st := rfl
  have hep : (cliDirStateOf W st).epochs = EpochGhost.ofGhost g := by
    simp [cliDirStateOf, hsess]
  rw [hp, hdf, cliPqRecvInputsFromFiles_encodeDir_eq, hrun]
  have hP_C : (pqxdhSessionParams W).C = W.C := rfl
  have hP_codec : (pqxdhSessionParams W).codec = protoSignalCodec := rfl
  have hP_spqr : (pqxdhSessionParams W).spqr = pqxdhSpqrSession W := rfl
  rcases htry : SignalMessage.tryFrom protoSignalCodec m.inner with _ | inner
  · have hmod : pqRecvPrekeyModel X W st m rc = some none := by
      simp [pqRecvPrekeyModel, htry]
    have hrec_none : (pqxdhSessionParams W).receive g m.inner rc = none := by
      unfold Params.receive; rw [hP_codec, htry]
    rw [hmod, hrec_none]; rfl
  · have hnt : (!st.trusts ⟨⟨m.idPub⟩⟩) = false := by simp [htrust]
    have hopt := tryDecryptFromRecord_toOption_eq W.C (pqxdhSpqrSession W)
      ((pqxdhSessionParams W).expectedAddrs g.party) inner .preKey .whisper rc g.session
    rcases hd1 : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
        ((pqxdhSessionParams W).expectedAddrs g.party) inner .preKey rc g.session with ⟨e1 | pt1, s1⟩ <;>
      rcases hd2 : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
          ((pqxdhSessionParams W).expectedAddrs g.party) inner .whisper rc g.session with ⟨e2 | pt2, s2⟩
    · have hrec_none : (pqxdhSessionParams W).receive g m.inner rc = none := by
        unfold Params.receive; rw [hP_codec, htry]; dsimp only; rw [hP_C, hP_spqr, hd2]
      rw [hrec_none]
      cases e1 with
      | panic =>
        have hmod : pqRecvPrekeyModel X W st m rc = none := by
          simp [pqRecvPrekeyModel, htry, hnt, hsess, hmatch, hrem, hd1]
        rw [hmod]; rfl
      | _ =>
        have hmod : pqRecvPrekeyModel X W st m rc = some none := by
          simp [pqRecvPrekeyModel, htry, hnt, hsess, hmatch, hrem, hd1]
        rw [hmod]; rfl
    · rw [hd1, hd2] at hopt; injection (Prod.mk.inj hopt).1
    · rw [hd1, hd2] at hopt; injection (Prod.mk.inj hopt).1
    · rw [hd1, hd2] at hopt
      have hpt : pt1 = pt2 := Option.some.inj (Prod.mk.inj hopt).1
      have hs_eq : s1 = s2 := (Prod.mk.inj hopt).2
      subst hpt hs_eq
      let st_raw : PqParty :=
        { st with peerId := some ⟨⟨m.idPub⟩⟩, session := some (x, { g with session := s1 }) }
      have hmod : pqRecvPrekeyModel X W st m rc = some (some (st_raw, pt1)) := by
        simp [pqRecvPrekeyModel, htry, hnt, hsess, hmatch, hrem, hd1, st_raw]
      have hstep : PqStep X W st st_raw := PqStep.recvPrekey m rc st_raw pt1 hm hmatch_all hmod
      have hrb := readBackDir_pqObserve_ok_eq (pqRecvInputs W st (wirePrekey :: m.bytes) rc).files
        hnd hstep
      rcases hrec : (pqxdhSessionParams W).receive g m.inner rc with _ | ⟨g', t', idx, pt'⟩
      · exfalso
        unfold Params.receive at hrec
        rw [hP_codec, htry] at hrec; dsimp only at hrec; rw [hP_C, hP_spqr, hd2] at hrec
        simp at hrec
      · have hrae := recv_aligned_and_epochs_gen (pqxdhSessionParams W) g m.inner rc hal hlen inner
          (by rw [hP_codec]; exact htry) (g', t', idx, pt') hrec
        have hg'_sess_pt : g'.session = s1 ∧ pt' = pt1 := by
          unfold Params.receive at hrec
          rw [hP_codec, htry] at hrec; dsimp only at hrec; rw [hP_C, hP_spqr, hd2] at hrec
          simp only [Option.some.injEq, Prod.mk.injEq] at hrec
          exact ⟨hrec.1.symm ▸ rfl, hrec.2.2.2.symm⟩
        have hdir : encodeDir W st_raw =
            encodeDir W { st with peerId := some ⟨⟨m.idPub⟩⟩, session := some (x, g') } :=
          encodeDir_eq_of_session_eq W { st with peerId := some ⟨⟨m.idPub⟩⟩ } x
            { g with session := s1 } g' hg'_sess_pt.1.symm
        have hidx_eq : idx = inner.counter.toNat + 1 := hrae.2.2.2.1
        rw [hmod]
        simp only [pqxdhExpectedOutcome, observe, Option.map]
        rw [hcp, hrb, hep, hrae.2.2.1, hdir, hidx_eq, hg'_sess_pt.2]
        rfl

/-- Extract the 256-bit `aliceCoins` word from bytes `160..192` of a 192-byte `init` tape (`DEV-PQ6`). -/
def tapeAliceCoins (t : List.Vector (BitVec 8) initiateTapeLen) : BitVec 256 :=
  HKDF.bytesToKey32 ((t.toList.drop 160).take 32)

end CryptoVerification.SignalSession
