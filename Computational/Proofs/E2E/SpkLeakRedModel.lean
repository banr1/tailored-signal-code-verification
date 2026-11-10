/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Session.StatementIdsModel
public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalBound
public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalSim
public import Computational.Proofs.CryptoGames.Ratchet.LibsignalSMInstanceProofDefs
public import Computational.Proofs.CryptoGames.SM.LibsignalGameProofDefs

/-!
# Shallow PRF Reduction `spkLeakRed` for Leaked Signed Pre-Keys

Defines the shallow `OracleComp` PRF reduction `spkLeakRed` against `extractPRF` (Hop 1) and its
uniform-scalar wrapper `spkLeakRedU` (Hop 3) for the leaked signed pre-key session game.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.SM CryptoGames.Ratchet CryptoGames.Ratchet.LibsignalInst
  CryptoGames.LibsignalSession CryptoGames.CKA CryptoGames.MACScheme CryptoGames.HKDF
  CryptoGames.HMAC CBC CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession

/-- Type of the shallow session-model PRF reduction against `extractPRF` for Hops 1 and 3. -/
abbrev SpkLeakRed (Pt : Type) (ℓ : ℕ) (PQC : Type := Unit) : Type :=
  Params Bytes PQC → DHFun (BitVec 256) Pt → (Pt → Bytes) → (Pt → PublicKey) →
    (PublicKey → Option Pt) → ℕ → BitVec 256 →
    SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes →
    MACScheme.PRFAdversary Pt (BitVec 256)

/-- Hop 3 wrapper running a `SpkLeakRed` reduction on a freshly sampled uniform scalar. -/
def spkLeakRedU {Pt : Type} {ℓ : ℕ} {PQC : Type} (D : SpkLeakRed Pt ℓ PQC) (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) :
    MACScheme.PRFAdversary Pt (BitVec 256) :=
  show OracleComp (unifSpec + prfSpec Pt (BitVec 256)) Bool from do
  let x ← (liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256)) :
    OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 256))
  D P Dh encPt encT decT qep x A

section SpkLeakRedDef

variable {Pt : Type} [Zero Pt] [DecidableEq Pt] {ℓ : ℕ} {PQC : Type} [SampleableType PQC]

def liftSpkGameM {α : Type}
    (m : StateT (SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) ProbComp α) :
    StateT (SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes)
      (OracleComp (unifSpec + prfSpec Pt (BitVec 256))) α :=
  StateT.mk fun s =>
    (liftM (m.run s) :
      OracleComp (unifSpec + prfSpec Pt (BitVec 256))
        (α × SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes))

/-- Initializes Alice's session state by querying the `extractPRF` oracle for the epoch-0 root key. -/
def initAOracle (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (ck0 s alice pqr : BitVec 256) :
    OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (GhostState Bytes) := do
  let prk ← evalQuery (Input := Pt) (Tag := BitVec 256) (Dh.dh s (Dh.dh alice Dh.base))
  let (rk1, ck1) := (expandPRG P.C.F).gen prk
  let spk := (KeyPair.generate P.C s).publicKey
  let sendingRatchetKey := KeyPair.generate P.C alice
  let sess := ((SessionState.new currentVersion P.idA P.idB rk1
    (P.spqr.init .a2b pqr)).addReceiverChain spk ⟨ck0, 0⟩).setSenderChain
    sendingRatchetKey ⟨ck1, 0⟩
  return ⟨.A, sess.setUnacknowledgedPreKeyMessage, 0, [0]⟩

/-- Handles Bob's epoch-0 receive by querying the `extractPRF` oracle at `Dh.dh s T` for admissible sender keys. -/
def receiveB0 (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (s : BitVec 256)
    (g : GhostState Bytes) (c : Bytes) (rc : BitVec 256) :
    OracleComp (unifSpec + prfSpec Pt (BitVec 256))
      (Option (GhostState Bytes × ℕ × ℕ × CBC.Plain ℓ)) := do
  match SignalMessage.tryFrom P.codec c with
  | .error _ => return none
  | .ok msg =>
    match decT msg.senderRatchetKey with
    | none => return none
    | some T =>
      if T = 0 ∨ encT T ≠ msg.senderRatchetKey then
        return none
      else
        let prk ← evalQuery (Input := Pt) (Tag := BitVec 256) (Dh.dh s T)
        let (rk1, ck1) := (expandPRG P.C.F).gen prk
        match rootCreateChain P.C rk1 msg.senderRatchetKey (KeyPair.generate P.C rc).privateKey with
        | .error _ => return none
        | .ok (rk2, ck2) =>
          let sess' : SessionState Bytes :=
            { g.session with
              previousCounter := 0
              rootKey := rk2
              receiverChains := [⟨msg.senderRatchetKey, some ⟨ck1, 0⟩, []⟩]
              senderChain := some ⟨KeyPair.generate P.C rc, ck2⟩ }
          match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs .B)
              msg .whisper rc sess' with
          | (.error _, _) => return none
          | (.ok m, s_out) =>
            let epochs := ([1] : List ℕ).drop (1 - s_out.receiverChains.length)
            return some ({ g with session := s_out, epoch := 1, chainEpochs := epochs },
              1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m)

def receiveSpk (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (s : BitVec 256)
    (g : GhostState Bytes) (c : Bytes) (rc : BitVec 256) :
    OracleComp (unifSpec + prfSpec Pt (BitVec 256))
      (Option (GhostState Bytes × ℕ × ℕ × CBC.Plain ℓ)) :=
  if g.party == .B && g.epoch == 0 then
    receiveB0 P ℓ Dh encT decT s g c rc
  else
    pure ((sessionSchemeU P ℓ).receive g c rc)

def deliverSpk (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (s : BitVec 256) :
    QueryImpl ((Party × Bytes) →ₒ Option (SM.RecvResult (CBC.Plain ℓ)))
      (StateT (SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes)
        (OracleComp (unifSpec + prfSpec Pt (BitVec 256)))) :=
  fun ⟨Q, c⟩ => do
    let st ← get
    if st.win then return none
    match st.inTransit Q.other c with
    | none => return none
    | some r =>
      let rc ← StateT.lift (liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256)))
      match ← StateT.lift (receiveSpk P ℓ Dh encT decT s (st.st Q) c rc) with
      | none => return some .rejected
      | some (st', t', i', m') =>
        set (st.accept Q st' r.pos)
        return some (.accepted t' i' (if st.chall.contains r.pos then none else some m'))

def injectSpk (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256) :
    QueryImpl ((Party × Bytes) →ₒ Option (SM.RecvResult (CBC.Plain ℓ)))
      (StateT (SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes)
        (OracleComp (unifSpec + prfSpec Pt (BitVec 256)))) :=
  fun ⟨Q, c⟩ => do
    let st ← get
    if st.win || (st.inTransit Q.other c).isSome || !(st.safeInj 3) ||
        !(ratchetKeyAdmissible protoSignalCodec decT encT c) then
      return none
    let rc ← StateT.lift (liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256)))
    match ← StateT.lift (receiveSpk P ℓ Dh encT decT s (st.st Q) c rc) with
    | none => return some .rejected
    | some (st', t', i', m') =>
      if qep + 1 < t' then return some .rejected
      let pos : SM.Pos := ⟨Q.other, t', i'⟩
      if st.trivial 3 pos then
        set (st.accept Q st' pos)
        return some (.accepted t' i' (some m'))
      else
        set { st with win := true }
        return some .rejected

def spkOracleImpl (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256) :
    QueryImpl (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes)
      (StateT (SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes)
        (OracleComp (unifSpec + prfSpec Pt (BitVec 256))))
  | .inl u => StateT.lift (query (spec := unifSpec + prfSpec Pt (BitVec 256)) (.inl u))
  | .inr (.inl (.inl (.inl (.inl x)))) =>
    liftSpkGameM (SM.transmitR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) x)
  | .inr (.inl (.inl (.inl (.inr x)))) =>
    liftSpkGameM (SM.challR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) x)
  | .inr (.inl (.inl (.inr x))) =>
    deliverSpk P ℓ Dh encT decT s x
  | .inr (.inl (.inr x)) =>
    injectSpk P ℓ Dh encT decT qep s x
  | .inr (.inr x) =>
    liftSpkGameM (SM.corrR (configRefuseEarlyBobCorr decT encT) x)

/-- Shallow PRF reduction simulating `configRefuseEarlyBobCorr` with epoch-0 root-key derivations answered by `extractPRF`. -/
def spkLeakRed : SpkLeakRed Pt ℓ PQC :=
  fun P Dh _encPt encT decT qep s A =>
    show OracleComp (unifSpec + prfSpec Pt (BitVec 256)) Bool from do
    let b ← (liftM ($ᵗ Bool : ProbComp Bool) :
      OracleComp (unifSpec + prfSpec Pt (BitVec 256)) Bool)
    let ck0 ← (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
      OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 256))
    let rest ← (liftM ($ᵗ (BitVec 256 × BitVec 256) : ProbComp (BitVec 256 × BitVec 256)) :
      OracleComp (unifSpec + prfSpec Pt (BitVec 256)) (BitVec 256 × BitVec 256))
    let stA ← initAOracle (Pt := Pt) P Dh ck0 s rest.1 rest.2
    let stB := P.initB ⟨0, ck0, s, rest.1, rest.2⟩
    let initSt : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes :=
      { st := fun Q => match Q with | .A => stA | .B => stB, b := b }
    let (b', finalSt) ← (simulateQ (spkOracleImpl P ℓ Dh encT decT qep s) A).run initSt
    return (b == b' || finalSt.win)

end SpkLeakRedDef

end CryptoVerification.E2E
