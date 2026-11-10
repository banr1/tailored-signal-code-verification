/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.SpuriousBounds
public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalSim
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RoundTrip
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma11Aux
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.RecvCoins
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.GhostStep

/-!
# Ideal Epoch-0 Signed-Pre-Key Injection Bound

**Checked by Lean.** No theorem of `Computational/Theorems/` unfolds a definition of this file, and
Lean's kernel checks every proof in it: you do not need to read it to trust those theorems.

Bounds the ideal `epoch0Distinguisher` experiment by `q * eps0IdealUnit P.C.F` (`eps0_ideal_le`)
and deduces `eps0Event_le_eps0` (DEV-LS26).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.LibsignalSM.Proofs.Refinement

open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst CryptoGames.Ratchet.LibsignalSim
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ]
  [SampleableType PQC]

def spurPred (F : ShaState → List (BitVec 8) → ShaState) (c : ℕ) (salt : Salt) (ids : SerializedIdentityKeys)
    (ser : List (BitVec 8)) (tag : BitVec 64) (ck0 : BitVec 256) : Bool :=
  let ck := (List.range c).foldl (fun k _ => (hmacPRF F).tag k chainKeySeed) ck0
  let mk := deriveMessageKeys F salt (chainHmac F ck messageKeySeed)
  (hmacScheme F).tag mk.2 (ids.toList ++ ser) == tag

@[local simp]
theorem spurDist_apply (F : ShaState → List (BitVec 8) → ShaState) (c : ℕ) (salt : Salt)
    (ids : SerializedIdentityKeys) (ser : List (BitVec 8)) (tag : BitVec 64) (rk0 : Ratchet.RootKey)
    (ck0 : BitVec 256) :
    wireMacVerifiesTest F c salt ids ser tag (rk0, ck0) =
      (pure (spurPred F c salt ids ser tag ck0) : ProbComp Bool) :=
  rfl

theorem evalDist_spurPred_eq_prgIdeal (F : ShaState → List (BitVec 8) → ShaState)
    (c : ℕ) (salt : Salt) (ids : SerializedIdentityKeys) (ser : List (BitVec 8)) (tag : BitVec 64) :
    𝒟[(do let ck0 ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
          pure (spurPred F c salt ids ser tag ck0) : ProbComp Bool)] =
      𝒟[PRGScheme.prgIdealExperiment (wireMacVerifiesTest F c salt ids ser tag)] := by
  symm
  unfold PRGScheme.prgIdealExperiment
  rw [sample_prod_bind]
  simp only [spurDist_apply]
  exact OracleComp.evalDist_bind_const ($ᵗ Ratchet.RootKey) _

theorem spurPred_le_unit (F : ShaState → List (BitVec 8) → ShaState)
    (c : ℕ) (hc : c < 2 ^ 32) (salt : Salt) (ids : SerializedIdentityKeys) (ser : List (BitVec 8))
    (hser : ser.length < 2 ^ 32) (tag : BitVec 64) :
    𝒟[(do let ck0 ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
          pure (spurPred F c salt ids ser tag ck0) : ProbComp Bool)] {true} ≤
      eps0IdealUnit F := by
  rw [evalDist_spurPred_eq_prgIdeal]
  exact spurDist_ideal_le_unit F c hc salt ids ser hser tag

theorem verifyMacWithAddresses_implies_spurPred (F : ShaState → List (BitVec 8) → ShaState)
    (c : ℕ) (salt : Salt) (expected : Option (List (BitVec 8)))
    (sender receiver : IdentityKey) (m : SignalMessage) (ck : LibsignalSession.ChainKey)
    (ck0 : BitVec 256)
    (hck : ck.key = (List.range c).foldl (fun k _ => (hmacPRF F).tag k chainKeySeed) ck0)
    (hv : m.verifyMacWithAddresses F expected sender receiver
      ((ck.messageKeys F).generateKeys F salt).macKey = true) :
    spurPred F c salt (macIds sender receiver)
      (m.serialized.take (m.serialized.length - macLength))
      (bytesToWord64LE (m.serialized.drop (m.serialized.length - macLength))) ck0 = true := by
  unfold SignalMessage.verifyMacWithAddresses SignalMessage.verifyMac computeMac
    ChainKey.messageKeys MessageKeyGenerator.generateKeys at hv
  rw [Bool.and_eq_true, beq_iff_eq] at hv
  unfold spurPred hmacScheme
  simp only [← hck, ← hv.1, beq_self_eq_true]

theorem foldl_range_succ {α : Type} (f : α → α) (n : ℕ) (a : α) :
    (List.range (n + 1)).foldl (fun k _ => f k) a =
      (List.range n).foldl (fun k _ => f k) (f a) := by
  rw [List.range_succ_eq_map, List.foldl_cons, List.foldl_map]

theorem Mut_exec_bind {σ α β : Type} (m : Mut σ α) (f : α → Mut σ β) (s : σ) :
    Mut.exec (m >>= f) s =
      match Mut.exec m s with
      | (.ok a, s') => Mut.exec (f a) s'
      | (.error e, s') => (.error e, s') := by
  unfold Mut.exec
  simp only [ExceptT.run_bind, StateT.run_bind]
  rcases (m.run).run s with ⟨r, s'⟩
  cases r <;> rfl

theorem Mut_exec_pure {σ α : Type} (a : α) (s : σ) :
    Mut.exec (pure a : Mut σ α) s = (.ok a, s) := rfl

theorem Mut_exec_throw {σ α : Type} (e : SignalProtocolError) (s : σ) :
    Mut.exec (throw e : Mut σ α) s = (.error e, s) := rfl

theorem Mut_exec_liftE {σ α : Type} (r : Except SignalProtocolError α) (s : σ) :
    Mut.exec (liftE r : Mut σ α) s = (r, s) := by
  cases r <;> rfl

theorem advanceChain_key (F : ShaState → List (BitVec 8) → ShaState) (their : PublicKey)
    (counter : BitVec 32) :
    ∀ (fuel : ℕ) (ck ckOut : LibsignalSession.ChainKey) (s s' : RatchetState),
      ck.index.toNat + fuel ≤ counter.toNat →
      Mut.exec (RatchetState.advanceChain F their counter fuel ck) s = (.ok ckOut, s') →
      ckOut.key = (List.range fuel).foldl (fun k _ => (hmacPRF F).tag k chainKeySeed) ck.key := by
  intro fuel
  induction fuel with
  | zero =>
    intro ck ckOut s s' _ hexec
    unfold RatchetState.advanceChain at hexec
    rw [Mut_exec_pure] at hexec
    injection hexec with h1 _
    injection h1 with h2
    subst h2
    rfl
  | succ n ih =>
    intro ck ckOut s s' hle hexec
    have hlt : ck.index < counter := by
      rw [BitVec.lt_def]
      omega
    unfold RatchetState.advanceChain at hexec
    simp only [hlt, ↓reduceIte, Mut_exec_bind, Mut_exec_liftE] at hexec
    rcases hst : Mut.exec (RatchetState.storeSkippedKey their (ck.messageKeys F)) s with ⟨r1, s1⟩
    rw [hst] at hexec
    cases r1 with
    | error e => simp at hexec
    | ok _ =>
      cases hnext : ck.nextChainKey F with
      | error e =>
        rw [hnext] at hexec
        simp at hexec
      | ok ck' =>
        rw [hnext] at hexec
        unfold ChainKey.nextChainKey at hnext
        split at hnext
        · simp at hnext
        · injection hnext with hck'
          subst hck'
          have h1nat : ((1 : BitVec 32).toNat) = 1 := rfl
          have hidx : (ck.index + 1).toNat = ck.index.toNat + 1 := by
            have hlt32 : counter.toNat < 2 ^ 32 := counter.isLt
            rw [BitVec.toNat_add, h1nat, Nat.mod_eq_of_lt]; omega
          rw [foldl_range_succ]
          refine ih _ ckOut s1 s' ?_ hexec
          dsimp only []
          omega

theorem consumeMessageKey_zero_key (F : ShaState → List (BitVec 8) → ShaState) (their : PublicKey)
    (ck0 : BitVec 256) (counter : BitVec 32) (msgType : MessageType)
    (s s' : RatchetState) (gen : MessageKeyGenerator)
    (hexec : Mut.exec (RatchetState.consumeMessageKey F their ⟨ck0, 0⟩ counter msgType) s =
      (.ok gen, s')) :
    ∃ ckOut : LibsignalSession.ChainKey,
      gen = ckOut.messageKeys F ∧
      ckOut.key = (List.range counter.toNat).foldl
        (fun k _ => (hmacPRF F).tag k chainKeySeed) ck0 := by
  have h0nat : ((0 : BitVec 32).toNat) = 0 := rfl
  have hlt : ¬ (counter < (0 : BitVec 32)) := by
    rw [BitVec.lt_def, h0nat]
    omega
  have hsub : counter - (0 : BitVec 32) = counter := by simp
  unfold RatchetState.consumeMessageKey at hexec
  simp only [hlt, ↓reduceIte, hsub, Mut_exec_bind, Mut_exec_liftE, Mut_exec_pure,
    Mut_exec_throw] at hexec
  have hget : Mut.exec (get : Mut RatchetState RatchetState) s = (.ok s, s) := rfl
  rw [hget] at hexec
  dsimp only [] at hexec
  split at hexec
  · simp only [Mut_exec_bind, Mut_exec_throw] at hexec
    simp at hexec
  · simp only [Mut_exec_bind, Mut_exec_pure, Mut_exec_liftE] at hexec
    rcases hadv : Mut.exec (RatchetState.advanceChain F their counter counter.toNat ⟨ck0, 0⟩) s
      with ⟨r1, s1⟩
    rw [hadv] at hexec
    cases r1 with
    | error e => simp at hexec
    | ok ckOut =>
      dsimp only [] at hexec
      cases hnext : ckOut.nextChainKey F with
      | error e =>
        rw [hnext] at hexec
        simp at hexec
      | ok ckNext =>
        rw [hnext] at hexec
        dsimp only [] at hexec
        rcases hset : Mut.exec (RatchetState.setReceiverChainKey their ckNext) s1 with ⟨r2, s2⟩
        rw [hset] at hexec
        cases r2 with
        | error e => simp at hexec
        | ok _ =>
          injection hexec with h1 _
          injection h1 with hgen
          refine ⟨ckOut, hgen.symm, ?_⟩
          exact advanceChain_key F their counter counter.toNat ⟨ck0, 0⟩ ckOut s s1
            (by dsimp; omega) hadv

def testSpk (P : Params PQ PQC) (pqrState : PQ) (c : List (BitVec 8)) (ck0 : BitVec 256) : Bool :=
  match SignalMessage.tryFrom P.codec c with
  | .error _ => false
  | .ok msg =>
    match P.spqr.recv pqrState msg.pqRatchet with
    | .error _ => false
    | .ok (_, salt) =>
      spurPred P.C.F msg.counter.toNat salt (macIds P.idB P.idA)
        (msg.serialized.take (msg.serialized.length - macLength))
        (bytesToWord64LE (msg.serialized.drop (msg.serialized.length - macLength))) ck0

theorem tryFrom_serialized_eq (codec : SignalMessageProtoCodec) (c : List (BitVec 8))
    (msg : SignalMessage) (htry : SignalMessage.tryFrom codec c = .ok msg) :
    msg.serialized = c := by
  obtain ⟨hl, hp⟩ := tryFrom_parse_eq codec c msg htry
  have h := tryFrom_of_parse codec c _ _ hl hp
  rw [htry] at h
  injection h with h
  rw [h]

theorem testSpk_le_unit (P : Params PQ PQC) (pqrState : PQ) (c : List (BitVec 8))
    (hc : c.length < 2 ^ 32) :
    𝒟[(do let ck0 ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
          pure (testSpk P pqrState c ck0) : ProbComp Bool)] {true} ≤
      eps0IdealUnit P.C.F := by
  unfold testSpk
  cases htry : SignalMessage.tryFrom P.codec c with
  | error _ =>
    dsimp only []
    rw [OracleComp.evalDist_bind_const ($ᵗ BitVec 256)]
    simp
  | ok msg =>
    dsimp only []
    cases P.spqr.recv pqrState msg.pqRatchet with
    | error _ =>
      dsimp only []
      rw [OracleComp.evalDist_bind_const ($ᵗ BitVec 256)]
      simp
    | ok ps =>
      have hser := tryFrom_serialized_eq P.codec c msg htry
      refine spurPred_le_unit P.C.F msg.counter.toNat msg.counter.isLt ps.2 (macIds P.idB P.idA) _
        ?_ _
      rw [hser, List.length_take]
      exact lt_of_le_of_lt (Nat.min_le_right _ _) hc

def setBobSenderKey (ck0 : BitVec 256) (g : GhostState PQ) : GhostState PQ :=
  { g with session := { g.session with
      senderChain := g.session.senderChain.map fun sc => { sc with chainKey := ⟨ck0, 0⟩ } } }

theorem Mut_exec_get {σ : Type} (s : σ) :
    Mut.exec (get : Mut σ σ) s = (.ok s, s) := rfl

theorem Mut_exec_set {σ : Type} (s' s : σ) :
    Mut.exec (set s' : Mut σ Unit) s = (.ok (), s') := rfl

theorem Mut_exec_modify {σ : Type} (f : σ → σ) (s : σ) :
    Mut.exec (modify f : Mut σ Unit) s = (.ok (), f s) := rfl

theorem Mut_exec_takeRootKey (r : RatchetState) :
    Mut.exec RatchetState.takeRootKey r = (.ok r.rootKey, { r with rootKey := 0 }) := rfl

theorem Mut_exec_takeRatchetState (s : SessionState PQ) :
    Mut.exec SessionState.takeRatchetState s =
      (.ok ⟨s.rootKey, s.senderChain, s.receiverChains, s.previousCounter, maxForwardJumps⟩,
        { s with receiverChains := [] }) := rfl

theorem Mut_exec_takePqRatchetState (s : SessionState PQ) :
    Mut.exec SessionState.takePqRatchetState s =
      (.ok s.pqRatchetState, { s with pqRatchetState := default }) := rfl

theorem Mut_exec_fromSessionState (s : SessionState PQ) :
    Mut.exec TripleRatchet.fromSessionState s =
      match s.remoteIdentity with
      | none =>
        (.error (.invalidSessionStructure .missingRemoteIdentity),
          { s with receiverChains := [], pqRatchetState := default })
      | some remote =>
        (.ok ⟨⟨s.rootKey, s.senderChain, s.receiverChains, s.previousCounter, maxForwardJumps⟩,
            s.pqRatchetState, s.localIdentity, remote⟩,
          { s with receiverChains := [], pqRatchetState := default }) := by
  unfold TripleRatchet.fromSessionState
  simp only [Mut_exec_bind, Mut_exec_takeRatchetState, Mut_exec_takePqRatchetState,
    Mut_exec_get, Mut_exec_pure, Mut_exec_throw]
  cases s.remoteIdentity <;> rfl

theorem Mut_exec_onRatchet {α : Type} (m : Mut RatchetState α) (t : TripleRatchet PQ) :
    Mut.exec (TripleRatchet.onRatchet m) t =
      match Mut.exec m t.ratchet with
      | (.ok a, r') => (.ok a, { t with ratchet := r' })
      | (.error e, r') => (.error e, { t with ratchet := r' }) := by
  unfold TripleRatchet.onRatchet zoom
  simp only [Mut_exec_bind, Mut_exec_get, Mut_exec_set, Mut_exec_liftE]
  rcases Mut.exec m t.ratchet with ⟨res, r'⟩
  cases res <;> rfl

theorem decrypt_setSenderKey (P : Params PQ PQC) (ck0 : BitVec 256)
    (expected : Option (List (BitVec 8))) (msg : SignalMessage) (rc : BitVec 256)
    (t : TripleRatchet PQ)
    (hrc : t.ratchet.receiverChains = [])
    (hidx : ∀ sc ∈ t.ratchet.senderChain, sc.chainKey.index = 0) :
    ∃ tErr,
      Mut.exec (TripleRatchet.decrypt P.C P.spqr expected msg .whisper rc)
        { t with ratchet := { t.ratchet with
            senderChain := t.ratchet.senderChain.map fun sc => { sc with chainKey := ⟨ck0, 0⟩ } } } =
      match Mut.exec (TripleRatchet.decrypt P.C P.spqr expected msg .whisper rc) t with
      | (.ok ptext, t') => (.ok ptext, t')
      | (.error e, _) => (.error e, tErr) := by
  have hens : ∃ rErr,
      Mut.exec (RatchetState.ensureReceiverChain P.C msg.senderRatchetKey rc)
        { t.ratchet with
          senderChain := t.ratchet.senderChain.map fun sc => { sc with chainKey := ⟨ck0, 0⟩ } } =
      match Mut.exec (RatchetState.ensureReceiverChain P.C msg.senderRatchetKey rc) t.ratchet with
      | (.ok ck, r') => (.ok ck, r')
      | (.error e, _) => (.error e, rErr) := by
    unfold RatchetState.ensureReceiverChain RatchetState.findReceiverChainKey
      RatchetState.findReceiverChainIndex RatchetState.dhRatchetStep
    simp only [hrc, List.findIdx?_nil, Mut_exec_bind, Mut_exec_get, Mut_exec_liftE,
      Mut_exec_pure, Mut_exec_throw, Mut_exec_takeRootKey, Mut_exec_modify]
    cases hsc : t.ratchet.senderChain with
    | none =>
      exact ⟨_, rfl⟩
    | some sc =>
      have hsc0 : sc.chainKey.index = 0 := hidx sc (by simp [hsc])
      simp only [Option.map_some, Mut_exec_bind, Mut_exec_pure, Mut_exec_takeRootKey,
        Mut_exec_liftE, Mut_exec_modify, hsc0, ↓reduceIte]
      rcases hrc1 : rootCreateChain P.C t.ratchet.rootKey msg.senderRatchetKey sc.ratchetKey.privateKey with _ | ⟨rk1, rck⟩
      · exact ⟨_, rfl⟩
      · dsimp only []
        rcases hrc2 : rootCreateChain P.C rk1 msg.senderRatchetKey (KeyPair.generate P.C rc).privateKey with _ | ⟨rk2, sck⟩
        · exact ⟨_, rfl⟩
        · exact ⟨t.ratchet, by simp [hrc]⟩
  rcases hens with ⟨rErr, hens⟩
  unfold TripleRatchet.decrypt
  rw [Mut_exec_bind, Mut_exec_bind, Mut_exec_onRatchet, Mut_exec_onRatchet]
  dsimp only []
  rw [hens]
  rcases Mut.exec (RatchetState.ensureReceiverChain P.C msg.senderRatchetKey rc) t.ratchet
    with ⟨r_ens, s_ens⟩
  cases r_ens with
  | error e => exact ⟨_, rfl⟩
  | ok ck =>
    dsimp only []
    rcases Mut.exec (_ : Mut (TripleRatchet PQ) (List (BitVec 8))) { t with ratchet := s_ens }
      with ⟨r_rest, s_rest⟩
    cases r_rest <;> exact ⟨s_rest, rfl⟩

theorem receive_setBobSenderKey_eq (P : Params PQ PQC) (ck0 : BitVec 256) (g : GhostState PQ)
    (c : List (BitVec 8)) (rc : BitVec 256)
    (hrc : g.session.receiverChains = [])
    (hidx : ∀ sc ∈ g.session.senderChain, sc.chainKey.index = 0) :
    P.receive (setBobSenderKey ck0 g) c rc = P.receive g c rc := by
  unfold Params.receive
  cases SignalMessage.tryFrom P.codec c with
  | error _ => rfl
  | ok msg =>
    dsimp only [setBobSenderKey]
    have htry : (SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper rc
        { g.session with
          senderChain := g.session.senderChain.map fun sc => { sc with chainKey := ⟨ck0, 0⟩ } }) =
      match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper rc
          g.session with
      | (.ok m, s) => (.ok m, s)
      | (.error e, _) =>
        (.error e, { g.session with
          senderChain := g.session.senderChain.map fun sc => { sc with chainKey := ⟨ck0, 0⟩ } }) := by
      unfold SessionState.tryDecryptFromRecord
      have hver : SessionState.version
          { g.session with
            senderChain := g.session.senderChain.map fun sc => { sc with chainKey := ⟨ck0, 0⟩ } } =
          g.session.version := rfl
      rw [hver]
      split
      · rfl
      · unfold SessionState.tryDecryptWithState
        rw [Mut_exec_bind, Mut_exec_bind, Mut_exec_fromSessionState, Mut_exec_fromSessionState]
        dsimp only []
        cases hrem : g.session.remoteIdentity with
        | none => rfl
        | some remote =>
          dsimp only []
          rcases decrypt_setSenderKey P ck0 (P.expectedAddrs g.party) msg rc
            ⟨⟨g.session.rootKey, g.session.senderChain, g.session.receiverChains,
              g.session.previousCounter, maxForwardJumps⟩,
              g.session.pqRatchetState, g.session.localIdentity, remote⟩ hrc hidx with ⟨tErr, hdec⟩
          dsimp only [] at hdec
          rw [hdec]
          rcases Mut.exec (TripleRatchet.decrypt P.C P.spqr (P.expectedAddrs g.party) msg .whisper rc)
            ⟨⟨g.session.rootKey, g.session.senderChain, g.session.receiverChains,
              g.session.previousCounter, maxForwardJumps⟩,
              g.session.pqRatchetState, g.session.localIdentity, remote⟩ with ⟨r_dec, t_dec⟩
          cases r_dec with
          | error e =>
            simp only [Mut_exec_bind, Mut_exec_liftE, Mut_exec_throw]
          | ok ptext =>
            simp only [Mut_exec_bind, Mut_exec_liftE, Mut_exec_modify, Mut_exec_pure]
            rfl
    rw [htry]
    rcases SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper rc g.session with ⟨r, s⟩
    cases r <;> rfl

def setHeadChainKey (ck0 : BitVec 256) (cs : List ReceiverChain) : List ReceiverChain :=
  match cs with
  | [] => []
  | rc :: rest => { rc with chainKey := some ⟨ck0, 0⟩ } :: rest

def setAliceSpkKey (ck0 : BitVec 256) (g : GhostState PQ) : GhostState PQ :=
  { g with session := { g.session with receiverChains := setHeadChainKey ck0 g.session.receiverChains } }

theorem findIdx?_setHeadChainKey (ck0 : BitVec 256) (cs : List ReceiverChain) (their : PublicKey) :
    (setHeadChainKey ck0 cs).findIdx? (fun c => c.senderRatchetKey == their) =
      cs.findIdx? (fun c => c.senderRatchetKey == their) := by
  cases cs <;> rfl

theorem length_setHeadChainKey (ck0 : BitVec 256) (cs : List ReceiverChain) :
    (setHeadChainKey ck0 cs).length = cs.length := by
  cases cs <;> rfl

theorem takeSkippedKey_setHeadChainKey (ck0 : BitVec 256) (their : PublicKey)
    (counter : BitVec 32) (r : RatchetState) (rc0 : ReceiverChain) (rest : List ReceiverChain)
    (hrc : r.receiverChains = rc0 :: rest) (hne : (rc0.senderRatchetKey == their) = false) :
    Mut.exec (RatchetState.takeSkippedKey their counter)
      { r with receiverChains := setHeadChainKey ck0 r.receiverChains } =
      ( (Mut.exec (RatchetState.takeSkippedKey their counter) r).1,
        { (Mut.exec (RatchetState.takeSkippedKey their counter) r).2 with
          receiverChains := setHeadChainKey ck0
            (Mut.exec (RatchetState.takeSkippedKey their counter) r).2.receiverChains } ) ∧
    ∃ rest', (Mut.exec (RatchetState.takeSkippedKey their counter) r).2.receiverChains =
      rc0 :: rest' := by
  cases r with
  | mk rootKey senderChain receiverChains previousCounter maxForwardJumps =>
    dsimp only [] at hrc
    subst hrc
    unfold RatchetState.takeSkippedKey RatchetState.findReceiverChainIndex
    simp only [Mut_exec_bind, Mut_exec_get, findIdx?_setHeadChainKey, List.findIdx?_cons, hne,
      Bool.false_eq_true, ↓reduceIte]
    cases rest.findIdx? (fun c => c.senderRatchetKey == their) with
    | none => exact ⟨rfl, rest, rfl⟩
    | some j =>
      dsimp only [Option.map, setHeadChainKey, List.getElem?_cons_succ]
      cases rest[j]? with
      | none => exact ⟨rfl, rest, rfl⟩
      | some c =>
        dsimp only []
        cases c.messageKeys.findIdx? (fun mk => mk.counter == counter) with
        | none => exact ⟨rfl, rest, rfl⟩
        | some pos =>
          dsimp only []
          cases c.messageKeys[pos]? with
          | none => exact ⟨rfl, rest, rfl⟩
          | some key => exact ⟨rfl, rest.set j _, rfl⟩

theorem storeSkippedKey_setHeadChainKey (ck0 : BitVec 256) (their : PublicKey)
    (key : MessageKeyGenerator) (r : RatchetState) (rc0 : ReceiverChain) (rest : List ReceiverChain)
    (hrc : r.receiverChains = rc0 :: rest) (hne : (rc0.senderRatchetKey == their) = false) :
    Mut.exec (RatchetState.storeSkippedKey their key)
      { r with receiverChains := setHeadChainKey ck0 r.receiverChains } =
      ( (Mut.exec (RatchetState.storeSkippedKey their key) r).1,
        { (Mut.exec (RatchetState.storeSkippedKey their key) r).2 with
          receiverChains := setHeadChainKey ck0
            (Mut.exec (RatchetState.storeSkippedKey their key) r).2.receiverChains } ) ∧
    ∃ rest', (Mut.exec (RatchetState.storeSkippedKey their key) r).2.receiverChains =
      rc0 :: rest' := by
  cases r with
  | mk rootKey senderChain receiverChains previousCounter maxForwardJumps =>
    dsimp only [] at hrc
    subst hrc
    unfold RatchetState.storeSkippedKey RatchetState.findReceiverChainIndex
    simp only [Mut_exec_bind, Mut_exec_get, findIdx?_setHeadChainKey, List.findIdx?_cons, hne,
      Bool.false_eq_true, ↓reduceIte]
    cases rest.findIdx? (fun c => c.senderRatchetKey == their) with
    | none => exact ⟨rfl, rest, rfl⟩
    | some j =>
      dsimp only [Option.map, setHeadChainKey, List.getElem?_cons_succ]
      cases rest[j]? with
      | none => exact ⟨rfl, rest, rfl⟩
      | some c => exact ⟨rfl, rest.set j _, rfl⟩

theorem setReceiverChainKey_setHeadChainKey (ck0 : BitVec 256) (their : PublicKey)
    (ck : LibsignalSession.ChainKey) (r : RatchetState) (rc0 : ReceiverChain) (rest : List ReceiverChain)
    (hrc : r.receiverChains = rc0 :: rest) (hne : (rc0.senderRatchetKey == their) = false) :
    Mut.exec (RatchetState.setReceiverChainKey their ck)
      { r with receiverChains := setHeadChainKey ck0 r.receiverChains } =
      ( (Mut.exec (RatchetState.setReceiverChainKey their ck) r).1,
        { (Mut.exec (RatchetState.setReceiverChainKey their ck) r).2 with
          receiverChains := setHeadChainKey ck0
            (Mut.exec (RatchetState.setReceiverChainKey their ck) r).2.receiverChains } ) ∧
    ∃ rest', (Mut.exec (RatchetState.setReceiverChainKey their ck) r).2.receiverChains =
      rc0 :: rest' := by
  cases r with
  | mk rootKey senderChain receiverChains previousCounter maxForwardJumps =>
    dsimp only [] at hrc
    subst hrc
    unfold RatchetState.setReceiverChainKey RatchetState.findReceiverChainIndex
    simp only [Mut_exec_bind, Mut_exec_get, findIdx?_setHeadChainKey, List.findIdx?_cons, hne,
      Bool.false_eq_true, ↓reduceIte]
    cases rest.findIdx? (fun c => c.senderRatchetKey == their) with
    | none => exact ⟨rfl, rest, rfl⟩
    | some j =>
      dsimp only [Option.map, setHeadChainKey, List.getElem?_cons_succ]
      cases rest[j]? with
      | none => exact ⟨rfl, rest, rfl⟩
      | some c => exact ⟨rfl, rest.set j _, rfl⟩

theorem advanceChain_setHeadChainKey (F : ShaState → List (BitVec 8) → ShaState)
    (ck0 : BitVec 256) (their : PublicKey) (counter : BitVec 32) :
    ∀ (fuel : ℕ) (ck : LibsignalSession.ChainKey) (r : RatchetState) (rc0 : ReceiverChain) (rest : List ReceiverChain),
      r.receiverChains = rc0 :: rest → (rc0.senderRatchetKey == their) = false →
      Mut.exec (RatchetState.advanceChain F their counter fuel ck)
        { r with receiverChains := setHeadChainKey ck0 r.receiverChains } =
        ( (Mut.exec (RatchetState.advanceChain F their counter fuel ck) r).1,
          { (Mut.exec (RatchetState.advanceChain F their counter fuel ck) r).2 with
            receiverChains := setHeadChainKey ck0
              (Mut.exec (RatchetState.advanceChain F their counter fuel ck) r).2.receiverChains } ) ∧
      ∃ rest', (Mut.exec (RatchetState.advanceChain F their counter fuel ck) r).2.receiverChains =
        rc0 :: rest'
  | 0, ck, r, rc0, rest, hrc, _ => ⟨rfl, rest, hrc⟩
  | fuel + 1, ck, r, rc0, rest, hrc, hne => by
    unfold RatchetState.advanceChain
    by_cases hlt : ck.index < counter
    · simp only [hlt, ↓reduceIte, Mut_exec_bind]
      rcases storeSkippedKey_setHeadChainKey ck0 their (ck.messageKeys F) r rc0 rest hrc hne
        with ⟨hstore, rest1, hrc1⟩
      rw [hstore]
      rcases h_st : Mut.exec (RatchetState.storeSkippedKey their (ck.messageKeys F)) r with ⟨r_st, s_st⟩
      rw [h_st] at hrc1
      cases r_st with
      | error e => exact ⟨rfl, rest1, hrc1⟩
      | ok _ =>
        dsimp only []
        cases ck.nextChainKey F with
        | error e => exact ⟨rfl, rest1, hrc1⟩
        | ok ck' =>
          simp only [Mut_exec_liftE, Mut_exec_pure, Mut_exec_bind]
          exact advanceChain_setHeadChainKey F ck0 their counter fuel ck' s_st rc0 rest1 hrc1 hne
    · simp only [hlt, ↓reduceIte]
      exact ⟨rfl, rest, hrc⟩

theorem consumeMessageKey_setHeadChainKey (F : ShaState → List (BitVec 8) → ShaState)
    (ck0 : BitVec 256) (their : PublicKey) (ck : LibsignalSession.ChainKey) (counter : BitVec 32)
    (msgType : MessageType) (r : RatchetState) (rc0 : ReceiverChain) (rest : List ReceiverChain)
    (hrc : r.receiverChains = rc0 :: rest) (hne : (rc0.senderRatchetKey == their) = false) :
    Mut.exec (RatchetState.consumeMessageKey F their ck counter msgType)
      { r with receiverChains := setHeadChainKey ck0 r.receiverChains } =
      ( (Mut.exec (RatchetState.consumeMessageKey F their ck counter msgType) r).1,
        { (Mut.exec (RatchetState.consumeMessageKey F their ck counter msgType) r).2 with
          receiverChains := setHeadChainKey ck0
            (Mut.exec (RatchetState.consumeMessageKey F their ck counter msgType) r).2.receiverChains } ) ∧
    ∃ rest', (Mut.exec (RatchetState.consumeMessageKey F their ck counter msgType) r).2.receiverChains =
      rc0 :: rest' := by
  unfold RatchetState.consumeMessageKey
  by_cases hlt : counter < ck.index
  · simp only [hlt, ↓reduceIte, Mut_exec_bind]
    rcases takeSkippedKey_setHeadChainKey ck0 their counter r rc0 rest hrc hne with ⟨htake, rest1, hrc1⟩
    rw [htake]
    rcases h_tk : Mut.exec (RatchetState.takeSkippedKey their counter) r with ⟨r_tk, s_tk⟩
    rw [h_tk] at hrc1
    cases r_tk with
    | error e => exact ⟨rfl, rest1, hrc1⟩
    | ok optK =>
      cases optK <;> exact ⟨rfl, rest1, hrc1⟩
  · simp only [hlt, ↓reduceIte, Mut_exec_bind, Mut_exec_get]
    by_cases hj : r.maxForwardJumps < (counter - ck.index).toNat
    · simp only [hj, ↓reduceIte]
      exact ⟨rfl, rest, hrc⟩
    · simp only [hj, ↓reduceIte, Mut_exec_pure, Mut_exec_bind]
      rcases advanceChain_setHeadChainKey F ck0 their counter (counter - ck.index).toNat ck r rc0 rest hrc hne
        with ⟨hadv, rest1, hrc1⟩
      rw [hadv]
      rcases h_adv : Mut.exec (RatchetState.advanceChain F their counter (counter - ck.index).toNat ck) r
        with ⟨r_adv, s_adv⟩
      rw [h_adv] at hrc1
      cases r_adv with
      | error e => exact ⟨rfl, rest1, hrc1⟩
      | ok ckOut =>
        dsimp only []
        cases ckOut.nextChainKey F with
        | error e => exact ⟨rfl, rest1, hrc1⟩
        | ok ckNext =>
          simp only [Mut_exec_liftE, Mut_exec_pure, Mut_exec_bind]
          rcases setReceiverChainKey_setHeadChainKey ck0 their ckNext s_adv rc0 rest1 hrc1 hne
            with ⟨hset, rest2, hrc2⟩
          rw [hset]
          rcases h_set : Mut.exec (RatchetState.setReceiverChainKey their ckNext) s_adv with ⟨r_set, s_set⟩
          rw [h_set] at hrc2
          cases r_set <;> exact ⟨rfl, rest2, hrc2⟩

theorem Mut_exec_outgoingFromSessionState (ck0 : BitVec 256) (s : SessionState PQ) :
    Mut.exec OutgoingTripleRatchet.fromSessionState
      { s with receiverChains := setHeadChainKey ck0 s.receiverChains } =
      ( (Mut.exec OutgoingTripleRatchet.fromSessionState s).1,
        { (Mut.exec OutgoingTripleRatchet.fromSessionState s).2 with
          receiverChains := setHeadChainKey ck0
            (Mut.exec OutgoingTripleRatchet.fromSessionState s).2.receiverChains } ) := by
  unfold OutgoingTripleRatchet.fromSessionState SessionState.version
  simp only [Mut_exec_bind, Mut_exec_get]
  cases hsc : s.senderChain with
  | none => simp [hsc, Mut_exec_throw]
  | some sc =>
    simp only [hsc, Mut_exec_bind, Mut_exec_get, Mut_exec_takePqRatchetState, Mut_exec_set,
      Mut_exec_throw, Mut_exec_pure]
    by_cases hv : 256 ≤ (if s.sessionVersion = 0 then (2 : BitVec 32) else s.sessionVersion).toNat
    · simp only [hv, ↓reduceIte, Mut_exec_throw, Mut_exec_bind]
    · simp only [hv, ↓reduceIte, Mut_exec_pure, Mut_exec_bind]
      cases s.remoteIdentity <;> rfl

theorem messageEncrypt_setHeadChainKey (P : Params PQ PQC) (ck0 : BitVec 256)
    (addr : Option (List (BitVec 8))) (m : List (BitVec 8)) (r : PQC) (s : SessionState PQ) :
    SessionState.messageEncrypt P.C P.codec P.spqr addr m r
      { s with receiverChains := setHeadChainKey ck0 s.receiverChains } =
      ( (SessionState.messageEncrypt P.C P.codec P.spqr addr m r s).1,
        { (SessionState.messageEncrypt P.C P.codec P.spqr addr m r s).2 with
          receiverChains := setHeadChainKey ck0
            (SessionState.messageEncrypt P.C P.codec P.spqr addr m r s).2.receiverChains } ) := by
  unfold SessionState.messageEncrypt SessionState.encryptAddresses
    OutgoingTripleRatchet.applyToSessionState
  simp only [Mut_exec_outgoingFromSessionState]
  rcases Mut.exec OutgoingTripleRatchet.fromSessionState s with ⟨r_out, s_out⟩
  cases r_out with
  | error e => rfl
  | ok o =>
    simp only []
    rcases Mut.exec (OutgoingTripleRatchet.encrypt P.C P.codec P.spqr m
      (if s.pendingPreKey then addr else none) r) o with ⟨r_enc, s_enc⟩
    cases r_enc <;> rfl

theorem send_setAliceSpkKey_eq (P : Params PQ PQC) (ck0 : BitVec 256) (g : GhostState PQ)
    (m : List (BitVec 8)) (r : PQC) :
    P.send (setAliceSpkKey ck0 g) m r =
      (setAliceSpkKey ck0 (P.send g m r).1, (P.send g m r).2) := by
  unfold Params.send setAliceSpkKey
  simp only [messageEncrypt_setHeadChainKey]
  rcases SessionState.messageEncrypt P.C P.codec P.spqr (P.sendAddrs g.party) m r g.session
    with ⟨r_enc, s_enc⟩
  cases r_enc <;> rfl

theorem dhRatchetStep_setHeadChainKey (C : Crypto) (ck0 : BitVec 256) (their : PublicKey)
    (coins : BitVec 256) (r : RatchetState) (rc0 : ReceiverChain) (rest : List ReceiverChain)
    (hrc : r.receiverChains = rc0 :: rest) :
    (Mut.exec (RatchetState.dhRatchetStep C their coins)
      { r with receiverChains := setHeadChainKey ck0 r.receiverChains }).1 =
      (Mut.exec (RatchetState.dhRatchetStep C their coins) r).1 ∧
    (∀ rck r_ens, Mut.exec (RatchetState.dhRatchetStep C their coins) r = (.ok rck, r_ens) →
      if (rest.length + 1 + 1) - maxReceiverChains = 0 then
        Mut.exec (RatchetState.dhRatchetStep C their coins)
          { r with receiverChains := setHeadChainKey ck0 r.receiverChains } =
          (.ok rck, { r_ens with receiverChains := setHeadChainKey ck0 r_ens.receiverChains }) ∧
        r_ens.receiverChains = rc0 :: (rest ++ [⟨their, some rck, []⟩]) ∧
        r_ens.receiverChains.length = r.receiverChains.length + 1
      else
        Mut.exec (RatchetState.dhRatchetStep C their coins)
          { r with receiverChains := setHeadChainKey ck0 r.receiverChains } =
          (.ok rck, r_ens) ∧
        r_ens.receiverChains.length < r.receiverChains.length + 1) := by
  unfold RatchetState.dhRatchetStep RatchetState.evictReceiverChains
  cases hsc : r.senderChain with
  | none =>
    simp [hsc, Mut_exec_bind, Mut_exec_get, Mut_exec_throw]
  | some sc =>
    simp only [hsc, Mut_exec_bind, Mut_exec_get, Mut_exec_throw, Mut_exec_takeRootKey,
      Mut_exec_liftE, Mut_exec_modify, Mut_exec_pure]
    cases rootCreateChain C r.rootKey their sc.ratchetKey.privateKey with
    | error e => simp
    | ok p1 =>
      dsimp only []
      cases rootCreateChain C p1.1 their (KeyPair.generate C coins).privateKey with
      | error e => simp
      | ok p2 =>
        dsimp only []
        refine ⟨rfl, ?_⟩
        intro rck r_ens hok
        injection hok with h1 h2
        injection h1 with hrck
        subst hrck
        subst h2
        simp only [hrc, setHeadChainKey, List.cons_append, List.length_cons, List.length_append,
          List.length_singleton]
        cases hd : (rest.length + 1 + 1) - maxReceiverChains with
        | zero =>
          simp [setHeadChainKey]
        | succ k =>
          simp only [Nat.succ_ne_zero, ↓reduceIte, List.drop_succ_cons, List.length_drop,
            List.length_append, List.length_singleton]
          exact ⟨ trivial, by omega ⟩

theorem takeSkippedKey_length (their : PublicKey) (counter : BitVec 32) (r : RatchetState) :
    (Mut.exec (RatchetState.takeSkippedKey their counter) r).2.receiverChains.length =
      r.receiverChains.length := by
  unfold RatchetState.takeSkippedKey
  rw [Mut_exec_bind, Mut_exec_get]
  dsimp only []
  cases r.findReceiverChainIndex their with
  | none => rfl
  | some idx =>
    dsimp only []
    cases r.receiverChains[idx]? with
    | none => rfl
    | some c =>
      dsimp only []
      cases c.messageKeys.findIdx? (fun mk => mk.counter == counter) with
      | none => rfl
      | some pos =>
        dsimp only []
        cases c.messageKeys[pos]? with
        | none => rfl
        | some key =>
          rw [Mut_exec_bind, Mut_exec_set]
          exact List.length_set

theorem storeSkippedKey_length (their : PublicKey) (key : MessageKeyGenerator) (r : RatchetState) :
    (Mut.exec (RatchetState.storeSkippedKey their key) r).2.receiverChains.length =
      r.receiverChains.length := by
  unfold RatchetState.storeSkippedKey
  rw [Mut_exec_bind, Mut_exec_get]
  dsimp only []
  cases r.findReceiverChainIndex their with
  | none => rfl
  | some idx =>
    dsimp only []
    cases r.receiverChains[idx]? with
    | none => rfl
    | some c =>
      rw [Mut_exec_set]
      exact List.length_set

theorem setReceiverChainKey_length (their : PublicKey) (ck : LibsignalSession.ChainKey) (r : RatchetState) :
    (Mut.exec (RatchetState.setReceiverChainKey their ck) r).2.receiverChains.length =
      r.receiverChains.length := by
  unfold RatchetState.setReceiverChainKey
  rw [Mut_exec_bind, Mut_exec_get]
  dsimp only []
  cases r.findReceiverChainIndex their with
  | none => rfl
  | some idx =>
    dsimp only []
    cases r.receiverChains[idx]? with
    | none => rfl
    | some c =>
      rw [Mut_exec_set]
      exact List.length_set

theorem advanceChain_length (F : ShaState → List (BitVec 8) → ShaState)
    (their : PublicKey) (counter : BitVec 32) :
    ∀ (fuel : ℕ) (ck : LibsignalSession.ChainKey) (r : RatchetState),
      (Mut.exec (RatchetState.advanceChain F their counter fuel ck) r).2.receiverChains.length =
        r.receiverChains.length
  | 0, ck, r => rfl
  | fuel + 1, ck, r => by
    unfold RatchetState.advanceChain
    by_cases hlt : ck.index < counter
    · simp only [hlt, ↓reduceIte, Mut_exec_bind]
      have hst := storeSkippedKey_length their (ck.messageKeys F) r
      rcases h_st : Mut.exec (RatchetState.storeSkippedKey their (ck.messageKeys F)) r with ⟨r_st, s_st⟩
      rw [h_st] at hst
      cases r_st with
      | error e => exact hst
      | ok _ =>
        dsimp only []
        cases ck.nextChainKey F with
        | error e =>
          simp only [Mut_exec_liftE, Mut_exec_throw, Mut_exec_bind]
          exact hst
        | ok ck' =>
          simp only [Mut_exec_liftE, Mut_exec_pure, Mut_exec_bind]
          exact (advanceChain_length F their counter fuel ck' s_st).trans hst
    · simp only [hlt, ↓reduceIte, Mut_exec_pure]

theorem consumeMessageKey_length (F : ShaState → List (BitVec 8) → ShaState)
    (their : PublicKey) (ck : LibsignalSession.ChainKey) (counter : BitVec 32) (msgType : MessageType)
    (r : RatchetState) :
    (Mut.exec (RatchetState.consumeMessageKey F their ck counter msgType) r).2.receiverChains.length =
      r.receiverChains.length := by
  unfold RatchetState.consumeMessageKey
  by_cases hlt : counter < ck.index
  · simp only [hlt, ↓reduceIte, Mut_exec_bind]
    have htk := takeSkippedKey_length their counter r
    rcases h_tk : Mut.exec (RatchetState.takeSkippedKey their counter) r with ⟨r_tk, s_tk⟩
    rw [h_tk] at htk
    cases r_tk with
    | error e => exact htk
    | ok optK =>
      cases optK <;> simp only [Mut_exec_pure, Mut_exec_throw] <;> exact htk
  · simp only [hlt, ↓reduceIte, Mut_exec_bind, Mut_exec_get]
    by_cases hj : r.maxForwardJumps < (counter - ck.index).toNat
    · simp only [hj, ↓reduceIte, Mut_exec_throw, Mut_exec_bind]
    · simp only [hj, ↓reduceIte, Mut_exec_pure, Mut_exec_bind]
      have hadv := advanceChain_length F their counter (counter - ck.index).toNat ck r
      rcases h_adv : Mut.exec (RatchetState.advanceChain F their counter (counter - ck.index).toNat ck) r
        with ⟨r_adv, s_adv⟩
      rw [h_adv] at hadv
      cases r_adv with
      | error e => exact hadv
      | ok ckOut =>
        dsimp only []
        cases ckOut.nextChainKey F with
        | error e =>
          simp only [Mut_exec_liftE, Mut_exec_throw, Mut_exec_bind]
          exact hadv
        | ok ckNext =>
          simp only [Mut_exec_liftE, Mut_exec_pure, Mut_exec_bind]
          have hset := setReceiverChainKey_length their ckNext s_adv
          rcases h_set : Mut.exec (RatchetState.setReceiverChainKey their ckNext) s_adv with ⟨r_set, s_set⟩
          rw [h_set] at hset
          cases r_set <;> exact hset.trans hadv

def ratchetDecryptStep (C : Crypto) (their : PublicKey) (counter : BitVec 32)
    (msgType : MessageType) (coins : BitVec 256) : Mut RatchetState MessageKeyGenerator := do
  let chainKey ← RatchetState.ensureReceiverChain C their coins
  RatchetState.consumeMessageKey C.F their chainKey counter msgType

def postRatchetDecrypt (C : Crypto) (spqr : Spqr PQ PQC) (expected : Option (List (BitVec 8)))
    (msg : SignalMessage) (msgType : MessageType) (s : SessionState PQ)
    (rem : IdentityKey) (gen : MessageKeyGenerator) (r' : RatchetState) :
    Except SignalProtocolError (List (BitVec 8)) × SessionState PQ :=
  if spqr.recvPanics s.pqRatchetState msg.pqRatchet then
    (.error (SessionState.recordError msgType .panic), s)
  else
  match spqr.recv s.pqRatchetState msg.pqRatchet with
  | .error true => (.error (SessionState.recordError msgType .invalidState), s)
  | .error false => (.error (SessionState.recordError msgType (.invalidMessage msgType .pqRatchet)), s)
  | .ok (newPqrState, pqrKey) =>
    let messageKeys := gen.generateKeys C.F pqrKey
    if !(msg.verifyMacWithAddresses C.F expected rem s.localIdentity messageKeys.macKey) then
      (.error (SessionState.recordError msgType (.invalidMessage msgType .macFailed)), s)
    else
      match aesCbcDecrypt C.D messageKeys.cipherKey messageKeys.iv msg.ciphertext with
      | none => (.error (SessionState.recordError msgType (.invalidMessage msgType .badCiphertext)), s)
      | some ptext =>
        (.ok ptext,
          { s with rootKey := r'.rootKey, previousCounter := r'.previousCounter,
                   senderChain := r'.senderChain, receiverChains := r'.receiverChains,
                   pqRatchetState := newPqrState, pendingPreKey := false })

theorem tryDecryptFromRecord_eq (C : Crypto) (spqr : Spqr PQ PQC)
    (expected : Option (List (BitVec 8))) (msg : SignalMessage) (msgType : MessageType)
    (coins : BitVec 256) (s : SessionState PQ) :
    SessionState.tryDecryptFromRecord C spqr expected msg msgType coins s =
      if s.version.toNat ≠ msg.messageVersion.toNat then
        (.error (.invalidMessage msgType .decryptionFailed), s)
      else
        match s.remoteIdentity with
        | none => (.error (SessionState.recordError msgType (.invalidSessionStructure .missingRemoteIdentity)), s)
        | some rem =>
          match Mut.exec (ratchetDecryptStep C msg.senderRatchetKey msg.counter msgType coins)
              ⟨s.rootKey, s.senderChain, s.receiverChains, s.previousCounter, maxForwardJumps⟩ with
          | (.error e, _) => (.error (SessionState.recordError msgType e), s)
          | (.ok gen, r') => postRatchetDecrypt C spqr expected msg msgType s rem gen r' := by
  unfold SessionState.tryDecryptFromRecord SessionState.tryDecryptWithState
    TripleRatchet.decrypt ratchetDecryptStep postRatchetDecrypt
    TripleRatchet.applyToSessionState SessionState.clearUnacknowledgedPreKeyMessage
  split
  · rfl
  · simp only [Mut_exec_bind, Mut_exec_fromSessionState, Mut_exec_onRatchet, Mut_exec_liftE,
      Mut_exec_get, Mut_exec_modify, Mut_exec_pure, Mut_exec_throw]
    cases s.remoteIdentity with
    | none => rfl
    | some rem =>
      dsimp only []
      rcases Mut.exec (RatchetState.ensureReceiverChain C msg.senderRatchetKey coins)
        ⟨s.rootKey, s.senderChain, s.receiverChains, s.previousCounter, maxForwardJumps⟩
        with ⟨r_ens, s_ens⟩
      cases r_ens with
      | error e => rfl
      | ok ck =>
        dsimp only []
        rcases Mut.exec (RatchetState.consumeMessageKey C.F msg.senderRatchetKey ck msg.counter msgType)
          s_ens with ⟨r_cmk, s_cmk⟩
        cases r_cmk with
        | error e => rfl
        | ok gen =>
          dsimp only []
          cases hpan : spqr.recvPanics s.pqRatchetState msg.pqRatchet
          case true => simp [Mut_exec_throw, Mut_exec_bind]
          simp only [Bool.false_eq_true, ↓reduceIte, Mut_exec_pure, Mut_exec_bind]
          cases spqr.recv s.pqRatchetState msg.pqRatchet with
          | error b =>
            cases b <;> simp [Mut_exec_throw, Mut_exec_bind]
          | ok ps =>
            simp only [Mut_exec_pure, Mut_exec_bind]
            cases hmac : msg.verifyMacWithAddresses C.F expected rem s.localIdentity
              ((gen.generateKeys C.F ps.2).macKey) with
            | false =>
              simp only [hmac, Bool.not_false, ↓reduceIte, Mut_exec_throw, Mut_exec_bind]
            | true =>
              simp only [hmac, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              cases aesCbcDecrypt C.D ((gen.generateKeys C.F ps.2).cipherKey)
                  ((gen.generateKeys C.F ps.2).iv) msg.ciphertext <;> rfl

theorem ensureReceiverChain_length (C : Crypto) (their : PublicKey) (coins : BitVec 256)
    (r r' : RatchetState) (ck : LibsignalSession.ChainKey)
    (hok : Mut.exec (RatchetState.ensureReceiverChain C their coins) r = (.ok ck, r')) :
    (∀ idx, r.findReceiverChainIndex their = some idx →
      r'.receiverChains.length = r.receiverChains.length ∧ idx < r.receiverChains.length) ∧
    (r.findReceiverChainIndex their = none →
      r'.receiverChains.length ≤ r.receiverChains.length + 1) := by
  unfold RatchetState.ensureReceiverChain RatchetState.findReceiverChainKey at hok
  simp only [Mut_exec_bind, Mut_exec_get, Mut_exec_liftE] at hok
  refine ⟨?_, ?_⟩
  · intro idx hidx
    rw [hidx] at hok
    dsimp only [] at hok
    cases hget : r.receiverChains[idx]? with
    | none => rw [hget] at hok; simp [Mut_exec_throw] at hok
    | some c =>
      rw [hget] at hok
      dsimp only [] at hok
      cases hck : c.chainKey with
      | none => rw [hck] at hok; simp [Mut_exec_throw] at hok
      | some ck0 =>
        rw [hck] at hok
        simp only [Mut_exec_pure] at hok
        injection hok with _ hr'
        subst hr'
        exact ⟨rfl, (List.getElem?_eq_some_iff.mp hget).1⟩
  · intro hnone
    rw [hnone] at hok
    dsimp only [] at hok
    unfold RatchetState.dhRatchetStep RatchetState.evictReceiverChains at hok
    simp only [Mut_exec_bind, Mut_exec_get] at hok
    cases hsc : r.senderChain with
    | none => rw [hsc] at hok; simp [Mut_exec_throw] at hok
    | some sc =>
      rw [hsc] at hok
      simp only [Mut_exec_bind, Mut_exec_get, Mut_exec_takeRootKey, Mut_exec_liftE,
        Mut_exec_modify, Mut_exec_pure] at hok
      cases hrc1 : rootCreateChain C r.rootKey their sc.ratchetKey.privateKey with
      | error e => rw [hrc1] at hok; simp [Mut_exec_throw] at hok
      | ok p1 =>
        rw [hrc1] at hok
        dsimp only [] at hok
        cases hrc2 : rootCreateChain C p1.1 their (KeyPair.generate C coins).privateKey with
        | error e => rw [hrc2] at hok; simp [Mut_exec_throw] at hok
        | ok p2 =>
          rw [hrc2] at hok
          dsimp only [] at hok
          injection hok with _ hr'
          subst hr'
          simp only [List.length_drop, List.length_append, List.length_singleton]
          omega

theorem ratchetDecryptStep_length (C : Crypto) (their : PublicKey) (counter : BitVec 32)
    (msgType : MessageType) (coins : BitVec 256) (r r' : RatchetState) (gen : MessageKeyGenerator)
    (hok : Mut.exec (ratchetDecryptStep C their counter msgType coins) r = (.ok gen, r')) :
    (∀ idx, r.findReceiverChainIndex their = some idx →
      r'.receiverChains.length = r.receiverChains.length ∧ idx < r.receiverChains.length) ∧
    (r.findReceiverChainIndex their = none →
      r'.receiverChains.length ≤ r.receiverChains.length + 1) := by
  unfold ratchetDecryptStep at hok
  rw [Mut_exec_bind] at hok
  rcases hens : Mut.exec (RatchetState.ensureReceiverChain C their coins) r with ⟨r_ens, s_ens⟩
  rw [hens] at hok
  cases r_ens with
  | error e => simp at hok
  | ok ck =>
    dsimp only [] at hok
    have hcmk := consumeMessageKey_length C.F their ck counter msgType s_ens
    rw [hok] at hcmk
    dsimp only [] at hcmk
    have hens_len := ensureReceiverChain_length C their coins r s_ens ck hens
    exact ⟨fun idx hidx => ⟨hcmk.trans (hens_len.1 idx hidx).1, (hens_len.1 idx hidx).2⟩,
      fun hnone => hcmk ▸ hens_len.2 hnone⟩

theorem ratchetDecryptStep_setHeadChainKey (C : Crypto) (ck0 : BitVec 256) (their : PublicKey)
    (counter : BitVec 32) (msgType : MessageType) (coins : BitVec 256)
    (r : RatchetState) (rc0 : ReceiverChain) (rest : List ReceiverChain)
    (hrc : r.receiverChains = rc0 :: rest) (hne : (rc0.senderRatchetKey == their) = false) :
    (Mut.exec (ratchetDecryptStep C their counter msgType coins)
      { r with receiverChains := setHeadChainKey ck0 r.receiverChains }).1 =
      (Mut.exec (ratchetDecryptStep C their counter msgType coins) r).1 ∧
    (∀ gen r', Mut.exec (ratchetDecryptStep C their counter msgType coins) r = (.ok gen, r') →
      (∀ idx, r.findReceiverChainIndex their = some idx →
        Mut.exec (ratchetDecryptStep C their counter msgType coins)
          { r with receiverChains := setHeadChainKey ck0 r.receiverChains } =
          (.ok gen, { r' with receiverChains := setHeadChainKey ck0 r'.receiverChains }) ∧
        r'.receiverChains.length = r.receiverChains.length ∧
        (∃ j, idx = j + 1 ∧ j < rest.length) ∧
        ∃ rest', r'.receiverChains = rc0 :: rest') ∧
      (r.findReceiverChainIndex their = none →
        if (rest.length + 1 + 1) - maxReceiverChains = 0 then
          Mut.exec (ratchetDecryptStep C their counter msgType coins)
            { r with receiverChains := setHeadChainKey ck0 r.receiverChains } =
            (.ok gen, { r' with receiverChains := setHeadChainKey ck0 r'.receiverChains }) ∧
          r'.receiverChains.length = r.receiverChains.length + 1 ∧
          ∃ rest', r'.receiverChains = rc0 :: rest'
        else
          Mut.exec (ratchetDecryptStep C their counter msgType coins)
            { r with receiverChains := setHeadChainKey ck0 r.receiverChains } =
            (.ok gen, r') ∧
          r'.receiverChains.length < r.receiverChains.length + 1)) := by
  unfold ratchetDecryptStep RatchetState.ensureReceiverChain RatchetState.findReceiverChainKey
  have hidx_eq : ({ r with receiverChains := setHeadChainKey ck0 r.receiverChains }).findReceiverChainIndex their =
      r.findReceiverChainIndex their := findIdx?_setHeadChainKey ck0 r.receiverChains their
  have hidx_val : r.findReceiverChainIndex their =
      Option.map Nat.succ (rest.findIdx? (fun c => c.senderRatchetKey == their)) := by
    unfold RatchetState.findReceiverChainIndex
    simp [hrc, List.findIdx?_cons, hne]
  simp only [Mut_exec_bind, Mut_exec_liftE, Mut_exec_get, hidx_eq, hidx_val]
  cases hfind : rest.findIdx? (fun c => c.senderRatchetKey == their) with
  | some j =>
    have hget_succ : (setHeadChainKey ck0 r.receiverChains)[j + 1]? = rest[j]? := by
      simp [hrc, setHeadChainKey]
    have hget_r : r.receiverChains[j + 1]? = rest[j]? := by
      simp [hrc]
    simp only [Option.map_some, hget_succ, hget_r]
    cases hc : rest[j]? with
    | none => simp [hc, Mut_exec_throw, Mut_exec_bind]
    | some c =>
      cases hck : c.chainKey with
      | none => simp [hc, hck, Mut_exec_throw, Mut_exec_bind]
      | some ck =>
        simp only [hc, hck, Mut_exec_pure, Mut_exec_bind]
        have hcmk := consumeMessageKey_setHeadChainKey C.F ck0 their ck counter msgType r rc0 rest hrc hne
        have hlen := consumeMessageKey_length C.F their ck counter msgType r
        refine ⟨by rw [hcmk.1], ?_⟩
        intro gen r' hok
        refine ⟨fun idx hidx => ⟨by rw [hcmk.1, hok], ?_, ?_, ?_⟩, by simp⟩
        · rw [hok] at hlen; exact hlen
        · exact ⟨j, (Option.some.inj hidx).symm, (List.getElem?_eq_some_iff.mp hc).1⟩
        · rcases hcmk.2 with ⟨rest', hrest'⟩
          rw [hok] at hrest'
          exact ⟨rest', hrest'⟩
  | none =>
    simp only [Option.map_none, Mut_exec_pure, Mut_exec_bind]
    have hdh := dhRatchetStep_setHeadChainKey C ck0 their coins r rc0 rest hrc
    rcases h_dh : Mut.exec (RatchetState.dhRatchetStep C their coins) r with ⟨r_dh, s_dh⟩
    rw [h_dh] at hdh
    cases r_dh with
    | error e =>
      rcases h_dh1 : Mut.exec (RatchetState.dhRatchetStep C their coins)
        { r with receiverChains := setHeadChainKey ck0 r.receiverChains } with ⟨r_dh1, s_dh1⟩
      have herr : r_dh1 = .error e := by
        have h1 := hdh.1
        rw [h_dh1] at h1
        exact h1
      subst herr
      simp
    | ok rck =>
      have h2 := hdh.2 rck s_dh rfl
      by_cases hd : (rest.length + 1 + 1) - maxReceiverChains = 0
      · simp only [hd, ↓reduceIte] at h2
        rcases h2 with ⟨hdh1, hrc_dh, hlen_dh⟩
        rw [hdh1]
        dsimp only []
        have hcmk := consumeMessageKey_setHeadChainKey C.F ck0 their rck counter msgType
          s_dh rc0 (rest ++ [⟨their, some rck, []⟩]) hrc_dh hne
        have hlen := consumeMessageKey_length C.F their rck counter msgType s_dh
        refine ⟨by rw [hcmk.1], ?_⟩
        intro gen r' hok
        refine ⟨by simp, fun _ => ?_⟩
        simp only [hd, ↓reduceIte]
        refine ⟨by rw [hcmk.1, hok], ?_, ?_⟩
        · rw [hok] at hlen; exact hlen.trans hlen_dh
        · rcases hcmk.2 with ⟨rest', hrest'⟩
          rw [hok] at hrest'
          exact ⟨rest', hrest'⟩
      · simp only [hd, ↓reduceIte] at h2
        rcases h2 with ⟨hdh1, hlen_dh⟩
        rw [hdh1]
        dsimp only []
        have hlen := consumeMessageKey_length C.F their rck counter msgType s_dh
        refine ⟨rfl, ?_⟩
        intro gen r' hok
        refine ⟨by simp, fun _ => ?_⟩
        simp only [hd, ↓reduceIte]
        rw [hok] at hlen ⊢
        exact ⟨rfl, hlen.symm ▸ hlen_dh⟩

theorem postRatchetDecrypt_receiverChains (C : Crypto) (spqr : Spqr PQ PQC)
    (expected : Option (List (BitVec 8))) (msg : SignalMessage) (msgType : MessageType)
    (s : SessionState PQ) (rem : IdentityKey) (gen : MessageKeyGenerator) (r' : RatchetState)
    (rc_in rc_out : List ReceiverChain) :
    (postRatchetDecrypt C spqr expected msg msgType { s with receiverChains := rc_in } rem gen
      { r' with receiverChains := rc_out }).1 =
      (postRatchetDecrypt C spqr expected msg msgType s rem gen r').1 ∧
    (∀ ptext s', postRatchetDecrypt C spqr expected msg msgType s rem gen r' = (.ok ptext, s') →
      postRatchetDecrypt C spqr expected msg msgType { s with receiverChains := rc_in } rem gen
        { r' with receiverChains := rc_out } = (.ok ptext, { s' with receiverChains := rc_out }) ∧
      s'.remoteIdentity = s.remoteIdentity ∧
      s'.localIdentity = s.localIdentity ∧
      s'.receiverChains = r'.receiverChains) := by
  unfold postRatchetDecrypt
  dsimp only []
  cases hpan : spqr.recvPanics s.pqRatchetState msg.pqRatchet
  case true => simp
  simp only [Bool.false_eq_true, ↓reduceIte]
  cases spqr.recv s.pqRatchetState msg.pqRatchet with
  | error b => cases b <;> simp
  | ok ps =>
    dsimp only []
    split
    · simp
    · cases hdec : aesCbcDecrypt C.D ((gen.generateKeys C.F ps.2).cipherKey)
        ((gen.generateKeys C.F ps.2).iv) msg.ciphertext with
      | none => simp [hdec]
      | some ptext =>
        dsimp only [hdec]
        refine ⟨rfl, ?_⟩
        intro ptext' s' hok
        injection hok with hp hs
        injection hp with hp'
        subst hp' hs
        exact ⟨rfl, rfl, rfl, rfl⟩

theorem getD_mem_of_lt : ∀ (l : List ℕ) (i d : ℕ), i < l.length → l.getD i d ∈ l
  | [], _, _, h => by simp at h
  | a :: l, 0, _, _ => by simp [List.getD]
  | a :: l, i + 1, d, h => by
    simp only [List.length_cons, Nat.add_lt_add_iff_right] at h
    simp only [List.getD, List.getElem?_cons_succ]
    exact List.mem_cons_of_mem a (getD_mem_of_lt l i d h)

theorem mem_of_mem_drop {α : Type} : ∀ (k : ℕ) (l : List α) (x : α), x ∈ l.drop k → x ∈ l
  | 0, l, _, h => h
  | k + 1, [], _, h => by simp at h
  | k + 1, a :: l, x, h => List.mem_cons_of_mem a (mem_of_mem_drop k l x h)

def patchAlice (ck0 : BitVec 256) (g : GhostState PQ) : GhostState PQ :=
  if 0 ∈ g.chainEpochs then setAliceSpkKey ck0 g else g

/-- Invariant on Alice's reference ghost state before any epoch-0 acceptance. -/
def AliceInv (P : Params PQ PQC) (spk : PublicKey) (g : GhostState PQ) : Prop :=
  g.party = .A ∧
  g.session.remoteIdentity = some P.idB ∧
  g.session.localIdentity = P.idA ∧
  g.chainEpochs.length = g.session.receiverChains.length ∧
  ((0 ∉ g.chainEpochs ∧ ∀ e ∈ g.chainEpochs, 0 < e) ∨
   (∃ rest epochsTail,
      g.session.receiverChains = ⟨spk, some ⟨0, 0⟩, []⟩ :: rest ∧
      g.chainEpochs = 0 :: epochsTail ∧
      ∀ e ∈ epochsTail, 0 < e))

theorem fromSessionState_preserve_fields (s : SessionState PQ) :
    (Mut.exec OutgoingTripleRatchet.fromSessionState s).2.remoteIdentity = s.remoteIdentity ∧
    (Mut.exec OutgoingTripleRatchet.fromSessionState s).2.localIdentity = s.localIdentity ∧
    (Mut.exec OutgoingTripleRatchet.fromSessionState s).2.receiverChains = s.receiverChains := by
  unfold OutgoingTripleRatchet.fromSessionState SessionState.version
  simp only [Mut_exec_bind, Mut_exec_get]
  cases hsc : s.senderChain with
  | none =>
    simp [hsc, Mut_exec_throw]
  | some sc =>
    simp only [hsc, Mut_exec_bind, Mut_exec_get, Mut_exec_takePqRatchetState, Mut_exec_set,
      Mut_exec_throw, Mut_exec_pure]
    by_cases hv : 256 ≤ (if s.sessionVersion = 0 then (2 : BitVec 32) else s.sessionVersion).toNat
    · simp only [hv, ↓reduceIte, Mut_exec_throw, Mut_exec_bind]
      simp [Mut_exec_throw]
    · simp only [hv, ↓reduceIte, Mut_exec_pure, Mut_exec_bind]
      cases s.remoteIdentity <;> simp [Mut_exec_pure, Mut_exec_throw]

theorem send_preserve_fields (P : Params PQ PQC) (g : GhostState PQ) (m : List (BitVec 8)) (r : PQC) :
    (P.send g m r).1.party = g.party ∧
    (P.send g m r).1.chainEpochs = g.chainEpochs ∧
    (P.send g m r).1.session.remoteIdentity = g.session.remoteIdentity ∧
    (P.send g m r).1.session.localIdentity = g.session.localIdentity ∧
    (P.send g m r).1.session.receiverChains = g.session.receiverChains := by
  have hf := fromSessionState_preserve_fields g.session
  unfold Params.send SessionState.messageEncrypt SessionState.encryptAddresses
    OutgoingTripleRatchet.applyToSessionState
  rcases h_out : Mut.exec OutgoingTripleRatchet.fromSessionState g.session with ⟨r_out, s_out⟩
  rw [h_out] at hf
  cases r_out with
  | error e => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | ok o =>
    dsimp only []
    rcases Mut.exec (OutgoingTripleRatchet.encrypt P.C P.codec P.spqr m
      (if g.session.pendingPreKey then P.sendAddrs g.party else none) r) o with ⟨r_enc, s_enc⟩
    cases r_enc with
    | error e => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    | ok msg => exact ⟨rfl, rfl, hf.1, hf.2.1, hf.2.2⟩

theorem send_patchAlice (P : Params PQ PQC) (ck0 : BitVec 256) (spk : PublicKey)
    (g : GhostState PQ) (m : List (BitVec 8)) (r : PQC) (hinv : AliceInv P spk g) :
    P.send (patchAlice ck0 g) m r =
      (patchAlice ck0 (P.send g m r).1, (P.send g m r).2) ∧
    AliceInv P spk (P.send g m r).1 := by
  have hp := send_preserve_fields P g m r
  refine ⟨?_, ?_⟩
  · unfold patchAlice
    rw [hp.2.1]
    split
    · exact send_setAliceSpkKey_eq P ck0 g m r
    · rfl
  · rcases hinv with ⟨hp1, hp2, hp3, hp4, hp5⟩
    refine ⟨hp.1.trans hp1, hp.2.2.1.trans hp2, hp.2.2.2.1.trans hp3, ?_, ?_⟩
    · rw [hp.2.1, hp.2.2.2.2]; exact hp4
    · rw [hp.2.1, hp.2.2.2.2]; exact hp5

theorem receive_noZero_props (P : Params PQ PQC) (rid : IdentityKey)
    (g : GhostState PQ) (c : List (BitVec 8)) (rc : BitVec 256)
    (hrem : g.session.remoteIdentity = some rid)
    (hlen : g.chainEpochs.length = g.session.receiverChains.length)
    (hpos : ∀ e ∈ g.chainEpochs, 0 < e) :
    ∀ g' t i m, P.receive g c rc = some (g', t, i, m) →
      g'.party = g.party ∧
      g'.session.remoteIdentity = some rid ∧
      g'.session.localIdentity = g.session.localIdentity ∧
      g'.chainEpochs.length = g'.session.receiverChains.length ∧
      0 ∉ g'.chainEpochs ∧
      (∀ e ∈ g'.chainEpochs, 0 < e) ∧
      0 < t ∧
      ((g'.epoch = g.epoch ∧ g.session.receiverChains ≠ []) ∨ g'.epoch = g.epoch + 1) := by
  intro g' t i m hrecv
  unfold Params.receive at hrecv
  cases htry : SignalMessage.tryFrom P.codec c with
  | error _ => rw [htry] at hrecv; simp at hrecv
  | ok msg =>
    rw [htry] at hrecv
    dsimp only [] at hrecv
    have hdec := tryDecryptFromRecord_eq P.C P.spqr (P.expectedAddrs g.party) msg .whisper rc g.session
    rw [hrem] at hdec
    by_cases hv : g.session.version.toNat = msg.messageVersion.toNat
    · simp only [ne_eq, hv, not_true_eq_false, ↓reduceIte] at hdec
      rcases hrat : Mut.exec (ratchetDecryptStep P.C msg.senderRatchetKey msg.counter .whisper rc)
        ⟨g.session.rootKey, g.session.senderChain, g.session.receiverChains,
         g.session.previousCounter, maxForwardJumps⟩ with ⟨r_rat, r'⟩
      rw [hrat] at hdec
      cases r_rat with
      | error _ => rw [hdec] at hrecv; simp at hrecv
      | ok gen =>
        dsimp only [] at hdec
        have hpost := (postRatchetDecrypt_receiverChains P.C P.spqr (P.expectedAddrs g.party)
          msg .whisper g.session rid gen r' g.session.receiverChains r'.receiverChains).2
        rcases hp : postRatchetDecrypt P.C P.spqr (P.expectedAddrs g.party) msg .whisper
          g.session rid gen r' with ⟨r_post, s⟩
        rw [hp] at hdec
        rw [hdec] at hrecv
        cases r_post with
        | error _ => simp at hrecv
        | ok ptext =>
          dsimp only [] at hrecv
          have hfields := (hpost ptext s hp).2
          have hrat_len := ratchetDecryptStep_length P.C msg.senderRatchetKey msg.counter
            .whisper rc _ r' gen hrat
          cases hidx : g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey) with
          | some idx =>
            rw [hidx] at hrecv
            dsimp only [] at hrecv
            injection hrecv with htuple
            rcases Prod.mk.inj htuple with ⟨hg', hrest⟩
            rcases Prod.mk.inj hrest with ⟨ht, _⟩
            subst hg' ht
            have hidx_len := hrat_len.1 idx hidx
            dsimp only [] at hidx_len
            have hdrop : g.chainEpochs.length - s.receiverChains.length = 0 := by
              rw [hfields.2.2, hidx_len.1, hlen]; omega
            simp only [hdrop, List.drop_zero]
            have hlt : idx < g.chainEpochs.length := hlen.symm ▸ hidx_len.2
            have ht_pos : 0 < g.chainEpochs.getD idx 0 :=
              hpos _ (getD_mem_of_lt g.chainEpochs idx 0 hlt)
            have hno0 : 0 ∉ g.chainEpochs := fun h0 => by have := hpos 0 h0; omega
            refine ⟨trivial, hfields.1.trans hrem, hfields.2.1, ?_, hno0, hpos, ht_pos,
              Or.inl ⟨trivial, fun hnil => by simp [hnil] at hidx⟩⟩
            rw [hfields.2.2, hidx_len.1, hlen]
          | none =>
            rw [hidx] at hrecv
            dsimp only [] at hrecv
            injection hrecv with htuple
            rcases Prod.mk.inj htuple with ⟨hg', hrest⟩
            rcases Prod.mk.inj hrest with ⟨ht, _⟩
            subst hg' ht
            have hnone_len := hrat_len.2 hidx
            have hpos' : ∀ e ∈ (g.chainEpochs ++ [g.epoch + 1]).drop
                ((g.chainEpochs ++ [g.epoch + 1]).length - s.receiverChains.length), 0 < e := by
              intro e he
              have hmem := mem_of_mem_drop _ _ _ he
              rw [List.mem_append, List.mem_singleton] at hmem
              rcases hmem with hmem | rfl
              · exact hpos e hmem
              · omega
            have hno0' : 0 ∉ (g.chainEpochs ++ [g.epoch + 1]).drop
                ((g.chainEpochs ++ [g.epoch + 1]).length - s.receiverChains.length) := by
              intro h0
              have := hpos' 0 h0
              omega
            refine ⟨rfl, hfields.1.trans hrem, hfields.2.1, ?_, hno0', hpos', by omega, Or.inr rfl⟩
            simp only [List.length_drop, List.length_append, List.length_singleton]
            dsimp only [] at hnone_len
            rw [← hlen, ← hfields.2.2] at hnone_len
            omega
    · simp only [ne_eq, hv, not_false_eq_true, ↓reduceIte] at hdec
      rw [hdec] at hrecv; simp at hrecv

theorem AliceInv_receive_noZero (P : Params PQ PQC) (ck0 : BitVec 256) (spk : PublicKey)
    (g : GhostState PQ) (c : List (BitVec 8)) (rc : BitVec 256)
    (hparty : g.party = .A) (hrem : g.session.remoteIdentity = some P.idB)
    (hloc : g.session.localIdentity = P.idA)
    (hlen : g.chainEpochs.length = g.session.receiverChains.length)
    (hno0 : 0 ∉ g.chainEpochs) (hpos : ∀ e ∈ g.chainEpochs, 0 < e) :
    P.receive (patchAlice ck0 g) c rc =
      (P.receive g c rc).map (fun x => (patchAlice ck0 x.1, x.2)) ∧
    ∀ g' t i m, P.receive g c rc = some (g', t, i, m) → AliceInv P spk g' ∧ 0 < t := by
  have hpatch_g : patchAlice ck0 g = g := by unfold patchAlice; simp [hno0]
  have hmain : ∀ g' t i m, P.receive g c rc = some (g', t, i, m) →
      0 ∉ g'.chainEpochs ∧ AliceInv P spk g' ∧ 0 < t := by
    intro g' t i m hrecv
    obtain ⟨hp, hrem', hloc', hlen', hno0', hpos', ht_pos, _⟩ :=
      receive_noZero_props P P.idB g c rc hrem hlen hpos g' t i m hrecv
    exact ⟨hno0', ⟨hp.trans hparty, hrem', hloc'.trans hloc, hlen', Or.inl ⟨hno0', hpos'⟩⟩, ht_pos⟩
  refine ⟨?_, fun g' t i m h => ⟨(hmain g' t i m h).2.1, (hmain g' t i m h).2.2⟩⟩
  rw [hpatch_g]
  cases h : P.receive g c rc with
  | none => rfl
  | some val =>
    rcases val with ⟨g', t, i, m⟩
    have h0 := (hmain g' t i m h).1
    simp only [Option.map_some, patchAlice, h0, ↓reduceIte]

theorem AliceInv_receive_hasZero (P : Params PQ PQC) (ck0 : BitVec 256) (spk : PublicKey)
    (g : GhostState PQ) (rest : List ReceiverChain) (epochsTail : List ℕ)
    (c : List (BitVec 8)) (rc : BitVec 256)
    (hparty : g.party = .A) (hrem : g.session.remoteIdentity = some P.idB)
    (hloc : g.session.localIdentity = P.idA)
    (hlen : g.chainEpochs.length = g.session.receiverChains.length)
    (hrc : g.session.receiverChains = ⟨spk, some ⟨0, 0⟩, []⟩ :: rest)
    (hep : g.chainEpochs = 0 :: epochsTail) (hpos : ∀ e ∈ epochsTail, 0 < e)
    (hmsg : ∀ msg, SignalMessage.tryFrom P.codec c = .ok msg → (spk == msg.senderRatchetKey) = false) :
    P.receive (patchAlice ck0 g) c rc =
      (P.receive g c rc).map (fun x => (patchAlice ck0 x.1, x.2)) ∧
    ∀ g' t i m, P.receive g c rc = some (g', t, i, m) → AliceInv P spk g' ∧ 0 < t := by
  have hpatch_g : patchAlice ck0 g = setAliceSpkKey ck0 g := by
    unfold patchAlice; simp [hep]
  rw [hpatch_g]
  unfold Params.receive
  cases htry : SignalMessage.tryFrom P.codec c with
  | error _ => simp
  | ok msg =>
    dsimp only [setAliceSpkKey]
    have hne : ((⟨spk, some ⟨0, 0⟩, []⟩ : ReceiverChain).senderRatchetKey == msg.senderRatchetKey) = false :=
      hmsg msg htry
    have hdec1 := tryDecryptFromRecord_eq P.C P.spqr (P.expectedAddrs g.party) msg .whisper rc
      { g.session with receiverChains := setHeadChainKey ck0 g.session.receiverChains }
    have hdec2 := tryDecryptFromRecord_eq P.C P.spqr (P.expectedAddrs g.party) msg .whisper rc g.session
    have hver : ({ g.session with receiverChains := setHeadChainKey ck0 g.session.receiverChains } : SessionState PQ).version =
        g.session.version := rfl
    have hrem1 : ({ g.session with receiverChains := setHeadChainKey ck0 g.session.receiverChains } : SessionState PQ).remoteIdentity =
        some P.idB := hrem
    rw [hver, hrem1] at hdec1
    rw [hrem] at hdec2
    by_cases hv : g.session.version.toNat = msg.messageVersion.toNat
    · simp only [ne_eq, hv, not_true_eq_false, ↓reduceIte] at hdec1 hdec2
      have hrat_step := ratchetDecryptStep_setHeadChainKey P.C ck0 msg.senderRatchetKey
        msg.counter .whisper rc
        ⟨g.session.rootKey, g.session.senderChain, g.session.receiverChains,
         g.session.previousCounter, maxForwardJumps⟩
        ⟨spk, some ⟨0, 0⟩, []⟩ rest hrc hne
      rcases hrat : Mut.exec (ratchetDecryptStep P.C msg.senderRatchetKey msg.counter .whisper rc)
        ⟨g.session.rootKey, g.session.senderChain, g.session.receiverChains,
         g.session.previousCounter, maxForwardJumps⟩ with ⟨r_rat, r'⟩
      rw [hrat] at hdec2
      cases r_rat with
      | error e =>
        rcases hrat1 : Mut.exec (ratchetDecryptStep P.C msg.senderRatchetKey msg.counter .whisper rc)
          ⟨g.session.rootKey, g.session.senderChain, setHeadChainKey ck0 g.session.receiverChains,
           g.session.previousCounter, maxForwardJumps⟩ with ⟨r_rat1, r1'⟩
        have herr : r_rat1 = .error e := by
          have h1 := hrat_step.1
          rw [hrat, hrat1] at h1
          exact h1
        subst herr
        rw [hrat1] at hdec1
        rw [hdec1, hdec2]; simp
      | ok gen =>
        dsimp only [] at hdec2
        have hstep := hrat_step.2 gen r' hrat
        have hidx_eq : (setHeadChainKey ck0 g.session.receiverChains).findIdx? (·.senderRatchetKey == msg.senderRatchetKey) =
            g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey) :=
          findIdx?_setHeadChainKey ck0 g.session.receiverChains msg.senderRatchetKey
        cases hidx : g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey) with
        | some idx =>
          rcases hstep.1 idx hidx with ⟨hrat1, hlen_r', ⟨j, rfl, hj⟩, rest', hrc_r'⟩
          dsimp only [] at hrat1
          rw [hrat1] at hdec1
          dsimp only [] at hdec1
          have hpost := postRatchetDecrypt_receiverChains P.C P.spqr (P.expectedAddrs g.party)
            msg .whisper g.session P.idB gen r'
            (setHeadChainKey ck0 g.session.receiverChains) (setHeadChainKey ck0 r'.receiverChains)
          rcases hp : postRatchetDecrypt P.C P.spqr (P.expectedAddrs g.party) msg .whisper
            g.session P.idB gen r' with ⟨r_post, s⟩
          rw [hp] at hdec2 hpost
          cases r_post with
          | error e =>
            rcases hp1 : postRatchetDecrypt P.C P.spqr (P.expectedAddrs g.party) msg .whisper
              { g.session with receiverChains := setHeadChainKey ck0 g.session.receiverChains }
              P.idB gen { r' with receiverChains := setHeadChainKey ck0 r'.receiverChains }
              with ⟨r_post1, s1⟩
            rw [hp1] at hpost hdec1
            have herr : r_post1 = .error e := hpost.1
            subst herr
            rw [hdec1, hdec2]; simp
          | ok ptext =>
            rcases hpost.2 ptext s rfl with ⟨hp1, hs_rem, hs_loc, hs_rc⟩
            rw [hp1] at hdec1
            rw [hdec1, hdec2]
            dsimp only []
            rw [hidx_eq, hidx]
            dsimp only []
            have hlen_s1 : (setHeadChainKey ck0 r'.receiverChains).length = g.chainEpochs.length := by
              rw [length_setHeadChainKey, hlen_r', hlen]
            have hlen_s2 : s.receiverChains.length = g.chainEpochs.length := by
              rw [hs_rc, hlen_r', hlen]
            have hdrop1 : g.chainEpochs.length - (setHeadChainKey ck0 r'.receiverChains).length = 0 := by omega
            have hdrop2 : g.chainEpochs.length - s.receiverChains.length = 0 := by omega
            simp only [hdrop1, hdrop2, List.drop_zero]
            have h0_mem : 0 ∈ g.chainEpochs := by simp [hep]
            refine ⟨?_, ?_⟩
            · simp only [Option.map_some, patchAlice, h0_mem, ↓reduceIte, setAliceSpkKey, hs_rc]
            · intro g' t i m hsome
              injection hsome with htuple
              rcases Prod.mk.inj htuple with ⟨hg', hrest⟩
              rcases Prod.mk.inj hrest with ⟨ht, _⟩
              subst hg' ht
              have hlen_ep : epochsTail.length = rest.length := by
                have := hlen; rw [hep, hrc] at this; simp at this; exact this
              have hj_ep : j < epochsTail.length := hlen_ep ▸ hj
              have ht_pos : 0 < g.chainEpochs.getD (j + 1) 0 := by
                rw [hep]
                simp only [List.getD, List.getElem?_cons_succ]
                exact hpos _ (getD_mem_of_lt epochsTail j 0 hj_ep)
              refine ⟨⟨hparty, hs_rem.trans hrem, hs_loc.trans hloc, hlen_s2.symm,
                Or.inr ⟨rest', epochsTail, hs_rc.trans hrc_r', hep, hpos⟩⟩, ht_pos⟩
        | none =>
          have hstep_none := hstep.2 hidx
          by_cases hd : (rest.length + 1 + 1) - maxReceiverChains = 0
          · simp only [hd, ↓reduceIte] at hstep_none
            rcases hstep_none with ⟨hrat1, hlen_r', rest', hrc_r'⟩
            rw [hrat1] at hdec1
            dsimp only [] at hdec1
            have hpost := postRatchetDecrypt_receiverChains P.C P.spqr (P.expectedAddrs g.party)
              msg .whisper g.session P.idB gen r'
              (setHeadChainKey ck0 g.session.receiverChains) (setHeadChainKey ck0 r'.receiverChains)
            rcases hp : postRatchetDecrypt P.C P.spqr (P.expectedAddrs g.party) msg .whisper
              g.session P.idB gen r' with ⟨r_post, s⟩
            rw [hp] at hdec2 hpost
            cases r_post with
            | error e =>
              rcases hp1 : postRatchetDecrypt P.C P.spqr (P.expectedAddrs g.party) msg .whisper
                { g.session with receiverChains := setHeadChainKey ck0 g.session.receiverChains }
                P.idB gen { r' with receiverChains := setHeadChainKey ck0 r'.receiverChains }
                with ⟨r_post1, s1⟩
              rw [hp1] at hpost hdec1
              have herr : r_post1 = .error e := hpost.1
              subst herr
              rw [hdec1, hdec2]; simp
            | ok ptext =>
              rcases hpost.2 ptext s rfl with ⟨hp1, hs_rem, hs_loc, hs_rc⟩
              rw [hp1] at hdec1
              rw [hdec1, hdec2]
              dsimp only []
              rw [hidx_eq, hidx]
              dsimp only []
              have hlen_s1 : (setHeadChainKey ck0 r'.receiverChains).length =
                  (g.chainEpochs ++ [g.epoch + 1]).length := by
                rw [length_setHeadChainKey, List.length_append, List.length_singleton, hlen_r', hlen]
              have hlen_s2 : s.receiverChains.length = (g.chainEpochs ++ [g.epoch + 1]).length := by
                rw [hs_rc, List.length_append, List.length_singleton, hlen_r', hlen]
              have hdrop1 : (g.chainEpochs ++ [g.epoch + 1]).length -
                  (setHeadChainKey ck0 r'.receiverChains).length = 0 := by omega
              have hdrop2 : (g.chainEpochs ++ [g.epoch + 1]).length - s.receiverChains.length = 0 := by omega
              simp only [hdrop1, hdrop2, List.drop_zero]
              have h0_mem : 0 ∈ g.chainEpochs ++ [g.epoch + 1] := by simp [hep]
              refine ⟨?_, ?_⟩
              · simp only [Option.map_some, patchAlice, h0_mem, ↓reduceIte, setAliceSpkKey, hs_rc]
              · intro g' t i m hsome
                injection hsome with htuple
                rcases Prod.mk.inj htuple with ⟨hg', hrest⟩
                rcases Prod.mk.inj hrest with ⟨ht, _⟩
                subst hg' ht
                refine ⟨⟨hparty, hs_rem.trans hrem, hs_loc.trans hloc, hlen_s2.symm,
                  Or.inr ⟨rest', epochsTail ++ [g.epoch + 1], hs_rc.trans hrc_r', ?_, ?_⟩⟩, by omega⟩
                · simp [hep]
                · intro e he
                  rw [List.mem_append, List.mem_singleton] at he
                  rcases he with he | rfl
                  · exact hpos e he
                  · omega
          · simp only [hd, ↓reduceIte] at hstep_none
            rcases hstep_none with ⟨hrat1, hlen_r'⟩
            rw [hrat1] at hdec1
            dsimp only [] at hdec1
            have hpost := postRatchetDecrypt_receiverChains P.C P.spqr (P.expectedAddrs g.party)
              msg .whisper g.session P.idB gen r'
              (setHeadChainKey ck0 g.session.receiverChains) r'.receiverChains
            rcases hp : postRatchetDecrypt P.C P.spqr (P.expectedAddrs g.party) msg .whisper
              g.session P.idB gen r' with ⟨r_post, s⟩
            rw [hp] at hdec2 hpost
            cases r_post with
            | error e =>
              rcases hp1 : postRatchetDecrypt P.C P.spqr (P.expectedAddrs g.party) msg .whisper
                { g.session with receiverChains := setHeadChainKey ck0 g.session.receiverChains }
                P.idB gen r' with ⟨r_post1, s1⟩
              rw [hp1] at hpost hdec1
              have herr : r_post1 = .error e := hpost.1
              subst herr
              rw [hdec1, hdec2]; simp
            | ok ptext =>
              rcases hpost.2 ptext s rfl with ⟨hp1, hs_rem, hs_loc, hs_rc⟩
              have hs_eq : { s with receiverChains := r'.receiverChains } = s := by
                cases s; congr 1; exact hs_rc.symm
              rw [hs_eq] at hp1
              rw [hp1] at hdec1
              rw [hdec1, hdec2]
              dsimp only []
              rw [hidx_eq, hidx]
              dsimp only []
              have hdrop_pos : (g.chainEpochs ++ [g.epoch + 1]).length - s.receiverChains.length =
                  ((epochsTail ++ [g.epoch + 1]).length - s.receiverChains.length) + 1 := by
                rw [hep, hs_rc]
                simp only [List.cons_append, List.length_cons, List.length_append, List.length_singleton] at hlen_r' ⊢
                have hlen_eq : epochsTail.length + 1 = g.session.receiverChains.length := by
                  rw [← List.length_cons (a := 0), ← hep, hlen]
                omega
              have hpos_drop : ∀ e ∈ (g.chainEpochs ++ [g.epoch + 1]).drop
                  ((g.chainEpochs ++ [g.epoch + 1]).length - s.receiverChains.length), 0 < e := by
                rw [hdrop_pos, hep, List.cons_append, List.drop_succ_cons]
                intro e he
                have hmem := mem_of_mem_drop _ _ _ he
                rw [List.mem_append, List.mem_singleton] at hmem
                rcases hmem with hmem | rfl
                · exact hpos e hmem
                · omega
              have hno0_drop : 0 ∉ (g.chainEpochs ++ [g.epoch + 1]).drop
                  ((g.chainEpochs ++ [g.epoch + 1]).length - s.receiverChains.length) := by
                intro h0; have := hpos_drop 0 h0; omega
              refine ⟨?_, ?_⟩
              · simp only [Option.map_some, patchAlice, hno0_drop, ↓reduceIte]
              · intro g' t i m hsome
                injection hsome with htuple
                rcases Prod.mk.inj htuple with ⟨hg', hrest⟩
                rcases Prod.mk.inj hrest with ⟨ht, _⟩
                subst hg' ht
                refine ⟨⟨hparty, hs_rem.trans hrem, hs_loc.trans hloc, ?_, Or.inl ⟨hno0_drop, hpos_drop⟩⟩, by omega⟩
                simp only [List.length_drop, List.length_append, List.length_singleton]
                rw [← hlen, ← hs_rc] at hlen_r'
                omega
    · simp only [ne_eq, hv, not_false_eq_true, ↓reduceIte] at hdec1 hdec2
      rw [hdec1, hdec2]; simp

theorem receive_patchAlice_nonSpk (P : Params PQ PQC) (ck0 : BitVec 256) (spk : PublicKey)
    (g : GhostState PQ) (c : List (BitVec 8)) (rc : BitVec 256)
    (hinv : AliceInv P spk g)
    (hnonSpk : 0 ∉ g.chainEpochs ∨
      ∀ msg, SignalMessage.tryFrom P.codec c = .ok msg → (spk == msg.senderRatchetKey) = false) :
    P.receive (patchAlice ck0 g) c rc =
      (P.receive g c rc).map (fun x => (patchAlice ck0 x.1, x.2)) ∧
    ∀ g' t i m, P.receive g c rc = some (g', t, i, m) → AliceInv P spk g' ∧ 0 < t := by
  rcases hinv with ⟨hparty, hrem, hloc, hlen, hcases⟩
  rcases hcases with ⟨hno0, hpos⟩ | ⟨rest, epochsTail, hrc, hep, hpos⟩
  · exact AliceInv_receive_noZero P ck0 spk g c rc hparty hrem hloc hlen hno0 hpos
  · rcases hnonSpk with hno0 | hmsg
    · exfalso; apply hno0; simp [hep]
    · exact AliceInv_receive_hasZero P ck0 spk g rest epochsTail c rc hparty hrem hloc hlen hrc hep hpos hmsg

def patchBob (ck0 : BitVec 256) (g : GhostState PQ) : GhostState PQ :=
  if g.epoch = 0 then setBobSenderKey ck0 g else g

/-- Invariant on Bob's reference ghost state. -/
def BobInv (P : Params PQ PQC) (s_epoch_B : ℕ) (g : GhostState PQ) : Prop :=
  g.session.remoteIdentity = some P.idA ∧
  g.chainEpochs.length = g.session.receiverChains.length ∧
  (∀ e ∈ g.chainEpochs, 0 < e) ∧
  (g.epoch = 0 →
    s_epoch_B = 0 ∧
    g.session.receiverChains = [] ∧
    ∀ sc ∈ g.session.senderChain, sc.chainKey.index = 0)

theorem send_patchBob (P : Params PQ PQC) (ck0 : BitVec 256) (g : GhostState PQ)
    (m : List (BitVec 8)) (r : PQC) (hne : g.epoch ≠ 0) :
    P.send (patchBob ck0 g) m r = (patchBob ck0 (P.send g m r).1, (P.send g m r).2) ∧
    (P.send g m r).1.epoch ≠ 0 := by
  have h1 : patchBob ck0 g = g := by unfold patchBob; simp [hne]
  have h2 : (P.send g m r).1.epoch ≠ 0 := by
    unfold Params.send
    rcases SessionState.messageEncrypt P.C P.codec P.spqr (P.sendAddrs g.party) m r g.session with ⟨res, s'⟩
    cases res with
    | error _ => exact hne
    | ok msg =>
      dsimp only []
      split <;> omega
  have h3 : patchBob ck0 (P.send g m r).1 = (P.send g m r).1 := by
    unfold patchBob; simp [h2]
  rw [h1, h3]
  exact ⟨rfl, h2⟩

theorem receive_patchBob (P : Params PQ PQC) (ck0 : BitVec 256) (s_ep : ℕ) (g : GhostState PQ)
    (c : List (BitVec 8)) (rc : BitVec 256) (hinv : BobInv P s_ep g) :
    P.receive (patchBob ck0 g) c rc = P.receive g c rc ∧
    ∀ g' t i m, P.receive g c rc = some (g', t, i, m) →
      (∀ s_ep', BobInv P s_ep' g') ∧ 0 < t ∧ patchBob ck0 g' = g' := by
  have hmain : ∀ g' t i m, P.receive g c rc = some (g', t, i, m) →
      (∀ s_ep', BobInv P s_ep' g') ∧ 0 < t ∧ g'.epoch ≠ 0 := by
    intro g' t i m hrecv
    obtain ⟨_, hrem', _, hlen', _, hpos', ht_pos, hep_cases⟩ :=
      receive_noZero_props P P.idA g c rc hinv.1 hinv.2.1 hinv.2.2.1 g' t i m hrecv
    have hep' : g'.epoch ≠ 0 := by
      rcases hep_cases with ⟨heq, hne⟩ | heq
      · intro h0; exact hne (hinv.2.2.2 (heq.symm.trans h0)).2.1
      · omega
    exact ⟨fun _ => ⟨hrem', hlen', hpos', fun h0 => False.elim (hep' h0)⟩, ht_pos, hep'⟩
  refine ⟨?_, fun g' t i m h =>
    ⟨(hmain g' t i m h).1, (hmain g' t i m h).2.1, by unfold patchBob; simp [(hmain g' t i m h).2.2]⟩⟩
  by_cases hep : g.epoch = 0
  · unfold patchBob
    simp only [hep, ↓reduceIte]
    exact receive_setBobSenderKey_eq P ck0 g c rc (hinv.2.2.2 hep).2.1 (hinv.2.2.2 hep).2.2
  · unfold patchBob
    simp only [hep, ↓reduceIte]

abbrev GameSt (PQ : Type) (ℓ : ℕ) := GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))

def patchParty (ck0 : BitVec 256) : Party → GhostState PQ → GhostState PQ
  | .A => patchAlice ck0
  | .B => patchBob ck0

def patchGameState {ℓ : ℕ} (ck0 : BitVec 256) (s : GameSt PQ ℓ) : GameSt PQ ℓ :=
  { s with st := fun p => match p with
      | .A => patchAlice ck0 (s.st .A)
      | .B => patchBob ck0 (s.st .B) }

/-- Reference game-state invariant maintained while `0 = s.maxAcc .A 0`, `s.win = false`, and `(.B, 0) ∉ s.corrs`. -/
def GameInv {ℓ : ℕ} (P : Params PQ PQC) (spk : PublicKey) (s : GameSt PQ ℓ) : Prop :=
  AliceInv P spk (s.st .A) ∧
  BobInv P (s.epoch .B) (s.st .B) ∧
  s.maxAcc .A 0 = 0 ∧
  s.win = false ∧
  ∀ r ∈ s.trans, 0 < r.pos.epoch

theorem patchAlice_chainEpochs (ck0 : BitVec 256) (g : GhostState PQ) :
    (patchAlice ck0 g).chainEpochs = g.chainEpochs := by
  unfold patchAlice setAliceSpkKey
  split <;> rfl

theorem patchGameState_epMgmt {ℓ : ℕ} (ck0 : BitVec 256)
    (s : GameSt PQ ℓ) (Δ qep : ℕ) (Q : Party) (bad : Bool) :
    (patchGameState ck0 s).epMgmt Δ qep Q bad =
      (s.epMgmt Δ qep Q bad).map (patchGameState ck0) := by
  unfold GameState.epMgmt GameState.safeCh GameState.leak patchGameState
  dsimp only []
  split
  · split
    · rfl
    · split <;> rfl
  · split <;> rfl

theorem patchGameState_record {ℓ : ℕ} (ck0 : BitVec 256)
    (s : GameSt PQ ℓ) (Δ : ℕ) (Q : Party)
    (st' : GhostState PQ) (r : Record (Plain ℓ) (List (BitVec 8))) (isChall : Bool) :
    (patchGameState ck0 s).record Δ Q (patchParty ck0 Q st') r isChall =
      patchGameState ck0 (s.record Δ Q st' r isChall) := by
  unfold GameState.record GameState.safeCh patchGameState patchParty
  dsimp only []
  congr 1
  funext p
  cases Q <;> cases p <;> rfl

theorem patchGameState_accept {ℓ : ℕ} (ck0 : BitVec 256)
    (s : GameSt PQ ℓ) (Q : Party) (st' : GhostState PQ) (pos : Pos) :
    (patchGameState ck0 s).accept Q (patchParty ck0 Q st') pos =
      patchGameState ck0 (s.accept Q st' pos) := by
  unfold GameState.accept GameState.delete patchGameState patchParty
  dsimp only []
  congr 1
  funext p
  cases Q <;> cases p <;> rfl

theorem epMgmt_epoch_pos {ℓ : ℕ} (s : GameSt PQ ℓ)
    (Δ qep : ℕ) (Q : Party) (bad : Bool) (s₁ : GameSt PQ ℓ)
    (hsend : noBobSendInEpoch0 s Q = true) (hep : s.epMgmt Δ qep Q bad = some s₁) :
    0 < s₁.epoch Q ∧ (Q = .B → s.epoch .B ≠ 0 ∧ s₁.epoch .B ≠ 0) ∧
    s₁.st = s.st ∧ s₁.trans = s.trans ∧ s₁.maxAcc = s.maxAcc ∧ s₁.win = s.win ∧
    (Q = .A → s₁.epoch .B = s.epoch .B) := by
  have hB : Q = .B → s.epoch .B ≠ 0 := by
    intro hQ; subst hQ
    unfold noBobSendInEpoch0 at hsend
    simp at hsend
    exact hsend
  unfold GameState.epMgmt at hep
  split at hep
  · split at hep
    · simp at hep
    · injection hep with hs₁
      subst hs₁
      have hst : (if bad && !s.safeCh Δ Q then s.leak (s.epoch Q + 1) else s).st = s.st := by
        split <;> rfl
      have htr : (if bad && !s.safeCh Δ Q then s.leak (s.epoch Q + 1) else s).trans = s.trans := by
        split <;> rfl
      have hma : (if bad && !s.safeCh Δ Q then s.leak (s.epoch Q + 1) else s).maxAcc = s.maxAcc := by
        split <;> rfl
      have hwin : (if bad && !s.safeCh Δ Q then s.leak (s.epoch Q + 1) else s).win = s.win := by
        split <;> rfl
      have hep_eq : (if bad && !s.safeCh Δ Q then s.leak (s.epoch Q + 1) else s).epoch = s.epoch := by
        split <;> rfl
      dsimp only []
      rw [hst, htr, hma, hwin, hep_eq, Function.update_self]
      exact ⟨by omega, fun hQ => ⟨hB hQ, by subst hQ; simp⟩, rfl, rfl, rfl, rfl, fun hQ => by subst hQ; simp⟩
  · split at hep
    · simp at hep
    · injection hep with hs₁
      subst hs₁
      rename_i hnsend _
      have hpos : 0 < s.epoch Q := by
        cases Q with
        | A =>
          by_cases h0 : s.epoch .A = 0
          · exfalso; apply hnsend; rw [h0]; rfl
          · omega
        | B =>
          have := hB rfl; omega
      exact ⟨hpos, fun hQ => ⟨hB hQ, hB hQ⟩, rfl, rfl, rfl, rfl, fun _ => rfl⟩

theorem evalDist_bind_le_const {α : Type} (p : ProbComp α) (F : α → ProbComp Bool) (B : ℝ≥0∞)
    (h : ∀ a, 𝒟[F a] {true} ≤ B) :
    𝒟[p >>= F] {true} ≤ B := by
  induction p using OracleComp.inductionOn with
  | pure a =>
    simpa only [pure_bind] using h a
  | query_bind t r ih =>
    simp only [bind_assoc, evalDist_bind_of_discrete,
      Measure.bind_apply (MeasurableSet.singleton true) Measurable.of_discrete.aemeasurable]
    calc ∫⁻ u, 𝒟[r u >>= F] {true} ∂𝒟[query t]
        ≤ ∫⁻ _, B ∂𝒟[query t] := lintegral_mono ih
      _ = B := by simp

theorem evalDist_bind_le_add {α : Type} (p : ProbComp α) (F G₁ G₂ : α → ProbComp Bool)
    (h : ∀ a, 𝒟[F a] {true} ≤ 𝒟[G₁ a] {true} + 𝒟[G₂ a] {true}) :
    𝒟[p >>= F] {true} ≤ 𝒟[p >>= G₁] {true} + 𝒟[p >>= G₂] {true} := by
  induction p using OracleComp.inductionOn with
  | pure a =>
    simpa only [pure_bind] using h a
  | query_bind t r ih =>
    simp only [bind_assoc, evalDist_bind_of_discrete,
      Measure.bind_apply (MeasurableSet.singleton true) Measurable.of_discrete.aemeasurable]
    rw [← lintegral_add_left Measurable.of_discrete]
    exact lintegral_mono ih

theorem evalDist_sample_split (test : BitVec 256 → Bool) (F_bad F_good : BitVec 256 → ProbComp Bool)
    (hle : ∀ ck0, test ck0 = false → 𝒟[F_bad ck0] {true} ≤ 𝒟[F_good ck0] {true}) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= F_bad] {true} ≤
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ck0 => pure (test ck0)] {true} +
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= F_good] {true} := by
  refine evalDist_bind_le_add ($ᵗ BitVec 256) F_bad (fun ck0 => pure (test ck0)) F_good fun ck0 => ?_
  cases h : test ck0
  · exact (hle ck0 h).trans le_add_self
  · calc 𝒟[F_bad ck0] {true} ≤ 1 := Construction.AuthL11.evalDist_le_one _
      _ = 𝒟[(pure true : ProbComp Bool)] {true} := by simp
      _ ≤ 𝒟[(pure true : ProbComp Bool)] {true} + 𝒟[F_good ck0] {true} := le_self_add

theorem receive_alice_spk_implies_testSpk (P : Params PQ PQC) (ck0 : BitVec 256)
    (g : GhostState PQ) (spk : PublicKey) (rest : List ReceiverChain)
    (c : List (BitVec 8)) (rc : BitVec 256) (msg : SignalMessage)
    (hrem : g.session.remoteIdentity = some P.idB)
    (hloc : g.session.localIdentity = P.idA)
    (hcs : g.session.receiverChains = ⟨spk, some ⟨0, 0⟩, []⟩ :: rest)
    (htry : SignalMessage.tryFrom P.codec c = .ok msg)
    (hspk : msg.senderRatchetKey = spk)
    (hrecv : (P.receive (setAliceSpkKey ck0 g) c rc).isSome) :
    testSpk P g.session.pqRatchetState c ck0 = true := by
  unfold Params.receive at hrecv
  rw [htry] at hrecv
  dsimp only [setAliceSpkKey] at hrecv
  rcases hdec : SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper rc
    { g.session with receiverChains := setHeadChainKey ck0 g.session.receiverChains } with ⟨r_dec, s_dec⟩
  rw [hdec] at hrecv
  cases r_dec with
  | error _ => simp at hrecv
  | ok m =>
    clear hrecv
    unfold SessionState.tryDecryptFromRecord at hdec
    split at hdec
    · simp at hdec
    · unfold SessionState.tryDecryptWithState at hdec
      simp only [Mut_exec_bind, Mut_exec_fromSessionState, hrem, hloc, hcs, setHeadChainKey,
        Mut_exec_liftE] at hdec
      unfold TripleRatchet.decrypt at hdec
      have hens : Mut.exec (RatchetState.ensureReceiverChain P.C msg.senderRatchetKey rc)
          { rootKey := g.session.rootKey, senderChain := g.session.senderChain,
            receiverChains := ⟨spk, some ⟨ck0, 0⟩, []⟩ :: rest,
            previousCounter := g.session.previousCounter, maxForwardJumps := maxForwardJumps } =
          (.ok ⟨ck0, 0⟩,
            { rootKey := g.session.rootKey, senderChain := g.session.senderChain,
              receiverChains := ⟨spk, some ⟨ck0, 0⟩, []⟩ :: rest,
              previousCounter := g.session.previousCounter, maxForwardJumps := maxForwardJumps }) := by
        unfold RatchetState.ensureReceiverChain RatchetState.findReceiverChainKey
          RatchetState.findReceiverChainIndex
        simp only [Mut_exec_bind, Mut_exec_get, Mut_exec_liftE, Mut_exec_pure,
          hspk, List.findIdx?_cons, beq_self_eq_true, ↓reduceIte, List.getElem?_cons_zero]
      simp only [Mut_exec_bind, Mut_exec_onRatchet, hens] at hdec
      rcases hcmk : Mut.exec (RatchetState.consumeMessageKey P.C.F msg.senderRatchetKey ⟨ck0, 0⟩ msg.counter .whisper)
        { rootKey := g.session.rootKey, senderChain := g.session.senderChain,
          receiverChains := ⟨spk, some ⟨ck0, 0⟩, []⟩ :: rest,
          previousCounter := g.session.previousCounter, maxForwardJumps := maxForwardJumps }
        with ⟨r_cmk, s_cmk⟩
      rw [hcmk] at hdec
      cases r_cmk with
      | error _ => simp at hdec
      | ok gen =>
        simp only [Mut_exec_bind, Mut_exec_get] at hdec
        cases hpan : P.spqr.recvPanics g.session.pqRatchetState msg.pqRatchet
        case true => simp [hpan, Mut_exec_throw] at hdec
        simp only [hpan, Bool.false_eq_true, ↓reduceIte, Mut_exec_pure, Mut_exec_bind] at hdec
        unfold testSpk
        rw [htry]
        dsimp only []
        cases hpqr_recv : P.spqr.recv g.session.pqRatchetState msg.pqRatchet with
        | error b =>
          rw [hpqr_recv] at hdec
          cases b <;> simp [Mut_exec_throw] at hdec
        | ok ps =>
          rw [hpqr_recv] at hdec
          simp only [Mut_exec_pure, Mut_exec_bind] at hdec
          rw [hspk] at hcmk
          rcases consumeMessageKey_zero_key P.C.F spk ck0 msg.counter .whisper _ _ gen hcmk
            with ⟨ckOut, rfl, hckOut⟩
          by_cases hmac : msg.verifyMacWithAddresses P.C.F (P.expectedAddrs g.party) P.idB P.idA
            ((ckOut.messageKeys P.C.F).generateKeys P.C.F ps.2).macKey = true
          · exact verifyMacWithAddresses_implies_spurPred P.C.F msg.counter.toNat ps.2
              (P.expectedAddrs g.party) P.idB P.idA msg ckOut ck0 hckOut hmac
          · have hmacF : msg.verifyMacWithAddresses P.C.F (P.expectedAddrs g.party) P.idB P.idA
                ((ckOut.messageKeys P.C.F).generateKeys P.C.F ps.2).macKey = false :=
              Bool.eq_false_iff.mpr hmac
            simp [hmacF, Mut_exec_throw] at hdec

def winPred {ℓ : ℕ} (s : GameSt PQ ℓ) : Bool :=
  (decide (0 < s.maxAcc .A 0) || s.win) && !(s.corrs.contains (.B, 0))

def d0Impl (P : Params PQ PQC) (ℓ : ℕ) (onImage : List (BitVec 8) → Bool) (qep : ℕ) :
    QueryImpl (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
      (StateT (GameSt PQ ℓ) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (GameSt PQ ℓ) ProbComp) +
    SM.oracleImplR (libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0) 3 qep (configEpoch0Distinguisher onImage)

theorem oracleImplR_libSessionR0_eq (P : Params PQ PQC) (ℓ : ℕ) (rk0 ck0 : BitVec 256)
    (onImage : List (BitVec 8) → Bool) (qep : ℕ) :
    (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (GameSt PQ ℓ) ProbComp) +
      SM.oracleImplR (libsignalSessionSchemeFromEpoch0Keys P ℓ rk0 ck0) 3 qep (configEpoch0Distinguisher onImage) =
      d0Impl P ℓ onImage qep := by
  unfold d0Impl SM.oracleImplR SM.transmitR SM.challR SM.deliverR SM.injectR SM.corrR
    SM.transmitImpl SM.challImpl SMSchemeR.sendPart libsignalSessionSchemeFromEpoch0Keys
  rfl

@[local simp] theorem d0Impl_inl_run (P : Params PQ PQC) (ℓ : ℕ) (onImage : List (BitVec 8) → Bool)
    (qep : ℕ) (q_u : unifSpec.Domain) (s : GameSt PQ ℓ) :
    (d0Impl P ℓ onImage qep (.inl q_u)).run s =
      ((query (spec := unifSpec) q_u : ProbComp _) >>= fun u => pure (u, s)) := rfl

theorem epMgmt_corrs {ℓ : ℕ} (s s₁ : GameSt PQ ℓ) (Δ qep : ℕ) (Q : Party) (bad : Bool)
    (h : s.epMgmt Δ qep Q bad = some s₁) : s₁.corrs = s.corrs := by
  unfold GameState.epMgmt GameState.leak at h
  split at h
  · split at h
    · simp at h
    · injection h with hs₁; subst hs₁; split <;> rfl
  · split at h
    · simp at h
    · injection h with hs₁; subst hs₁; rfl

theorem record_corrs {ℓ : ℕ} (s : GameSt PQ ℓ) (Δ : ℕ) (Q : Party)
    (st' : GhostState PQ) (r : Record (Plain ℓ) (List (BitVec 8))) (isChall : Bool) :
    (s.record Δ Q st' r isChall).corrs = s.corrs := rfl

theorem afterCorr_contains {ℓ : ℕ} (s : GameSt PQ ℓ) (Q : Party) (pe : Party × ℕ)
    (h : s.corrs.contains pe = true) :
    (s.afterCorr Q).corrs.contains pe = true := by
  unfold GameState.afterCorr GameState.leak
  simp only [List.contains_eq_mem, decide_eq_true_eq, List.mem_cons] at h ⊢
  exact Or.inr h

theorem d0Oracle_preserves_corrs (P : Params PQ PQC) (ℓ : ℕ) (onImage : List (BitVec 8) → Bool)
    (qep : ℕ)
    (t : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (s : GameSt PQ ℓ) (h : s.corrs.contains (.B, 0) = true)
    (F : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range t ×
      GameSt PQ ℓ → ProbComp Bool)
    (hF : ∀ u s', s'.corrs.contains (.B, 0) = true → 𝒟[F (u, s')] {true} ≤ 0) :
    𝒟[((d0Impl P ℓ onImage qep t).run s) >>= F] {true} ≤ 0 := by
  rcases t with q_u | q_sm
  · simp only [d0Impl_inl_run, bind_assoc, pure_bind]
    exact evalDist_bind_le_const _ _ 0 fun u => hF u s h
  · rcases q_sm with (((q_tr | q_ch) | q_del) | q_inj) | q_corr
    ·
      rcases q_tr with ⟨Q, m, r⟩
      change 𝒟[((SM.transmitR (libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0) 3 qep (configEpoch0Distinguisher onImage) (Q, m, r)).run s) >>= F] {true} ≤ 0
      unfold SM.transmitR SM.transmitImpl
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      split
      · simp only [StateT.run_pure, pure_bind]; exact hF none s h
      · simp only [StateT.run_bind, StateT.run_get, pure_bind]
        split
        · simp only [StateT.run_pure, pure_bind]; exact hF none s h
        · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
          refine evalDist_bind_le_const _ _ 0 fun cb => ?_
          cases hep : s.epMgmt 3 qep Q cb.2 with
          | none => simp only [StateT.run_pure, pure_bind]; exact hF none s h
          | some s₁ =>
            simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
            exact hF _ _ (by rw [record_corrs, epMgmt_corrs s s₁ 3 qep Q cb.2 hep]; exact h)
    ·
      rcases q_ch with ⟨Q, m₀, m₁, r⟩
      change 𝒟[((SM.challR (libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0) 3 qep (configEpoch0Distinguisher onImage) (Q, m₀, m₁, r)).run s) >>= F] {true} ≤ 0
      unfold SM.challR SM.challImpl
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      split
      · simp only [StateT.run_pure, pure_bind]; exact hF none s h
      · simp only [StateT.run_bind, StateT.run_get, pure_bind]
        split
        · simp only [StateT.run_pure, pure_bind]; exact hF none s h
        · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
          refine evalDist_bind_le_const _ _ 0 fun cb => ?_
          cases hep : s.epMgmt 3 qep Q cb.2 with
          | none => simp only [StateT.run_pure, pure_bind]; exact hF none s h
          | some s₁ =>
            dsimp only []
            split
            · simp only [StateT.run_pure, pure_bind]; exact hF none s h
            · exact hF _ _ (by rw [record_corrs, epMgmt_corrs s s₁ 3 qep Q cb.2 hep]; exact h)
    ·
      rcases q_del with ⟨Q, c⟩
      change 𝒟[((SM.deliverR (libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0) (configEpoch0Distinguisher onImage) (Q, c)).run s) >>= F] {true} ≤ 0
      unfold SM.deliverR
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      split
      · simp only [StateT.run_pure, pure_bind]; exact hF none s h
      · cases s.inTransit Q.other c with
        | none => simp only [StateT.run_pure, pure_bind]; exact hF none s h
        | some r =>
          simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
          refine evalDist_bind_le_const _ _ 0 fun rc => ?_
          cases (libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).receive (s.st Q) c rc with
          | none =>
            split <;> exact hF _ _ h
          | some res =>
            rcases res with ⟨st', t', i', m'⟩
            split <;> exact hF _ _ h
    ·
      rcases q_inj with ⟨Q, c⟩
      change 𝒟[((SM.injectR (libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0) 3 qep (configEpoch0Distinguisher onImage) (Q, c)).run s) >>= F] {true} ≤ 0
      unfold SM.injectR
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      split
      · simp only [StateT.run_pure, pure_bind]; exact hF none s h
      · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
        refine evalDist_bind_le_const _ _ 0 fun rc => ?_
        cases (libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).receive (s.st Q) c rc with
        | none => simp only [StateT.run_pure, pure_bind]; exact hF _ _ h
        | some res =>
          rcases res with ⟨st', t', i', m'⟩
          split
          · simp only [StateT.run_pure, pure_bind]; exact hF _ _ h
          · split
            · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]; exact hF _ _ h
            · split
              · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]; exact hF _ _ h
              · split <;> exact hF _ _ h
    ·
      change 𝒟[((SM.corrR (configEpoch0Distinguisher onImage) q_corr).run s) >>= F] {true} ≤ 0
      unfold SM.corrR
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      split
      · simp only [StateT.run_pure, pure_bind]; exact hF none s h
      · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
        exact hF _ _ (afterCorr_contains s q_corr (.B, 0) h)

theorem evalDist_winPred_of_corrs {α : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (onImage : List (BitVec 8) → Bool) (qep : ℕ)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s : GameSt PQ ℓ) (h : s.corrs.contains (.B, 0) = true) :
    𝒟[do let (_, s') ← (simulateQ (d0Impl P ℓ onImage qep) oa).run s; pure (winPred s')] {true} ≤ 0 := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a =>
    have hw : winPred s = false := by unfold winPred; simp only [h, Bool.not_true, Bool.and_false]
    simp [hw]
  | query_bind t r ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_eq, map_eq_bind_pure_comp, Function.comp_apply, pure_bind, StateT.run_bind, bind_assoc]
    exact d0Oracle_preserves_corrs P ℓ onImage qep t s h
      (fun x => (simulateQ (d0Impl P ℓ onImage qep) (r x.1)).run x.2 >>= fun z => pure (winPred z.2))
      fun u s' hs' => ih u s' hs'

theorem initState_patchGameState (P : Params PQ PQC) (ℓ : ℕ) (rk0 ck0 : BitVec 256)
    (k : Ratchet.RootKey × BitVec 256 × BitVec 256 × BitVec 256) (b : Bool) :
    let sRef := SM.initState (libsignalSessionSchemeFromEpoch0Keys P ℓ rk0 0).sendPart k b
    let spk := (KeyPair.generate P.C k.2.1).publicKey
    SM.initState (libsignalSessionSchemeFromEpoch0Keys P ℓ rk0 ck0).sendPart k b = patchGameState ck0 sRef ∧
    GameInv P spk sRef := by
  intro sRef spk
  refine ⟨?_, ?_, ?_, rfl, rfl, by simp [sRef, SM.initState]⟩
  · dsimp only [sRef]
    unfold SM.initState SMSchemeR.sendPart libsignalSessionSchemeFromEpoch0Keys patchGameState
    dsimp only []
    congr 1
    funext p
    cases p with
    | A =>
      dsimp only [patchAlice, Params.initA, initializeInitiatorSession]
      cases rootCreateChain P.C rk0 (KeyPair.generate P.C k.2.1).publicKey
        (KeyPair.generate P.C k.2.2.1).privateKey <;>
        simp [Bind.bind, Except.bind, Pure.pure, Except.pure, patchAlice, setAliceSpkKey,
          setHeadChainKey, SessionState.new, SessionState.addReceiverChain,
          SessionState.setSenderChain, SessionState.setUnacknowledgedPreKeyMessage,
          maxReceiverChains]
    | B =>
      dsimp only [patchBob, Params.initB, initializeRecipientSession]
      rfl
  · refine ⟨?_, ?_, ?_, ?_, Or.inr ⟨[], [], ?_, ?_, by simp⟩⟩
    · dsimp only [sRef, SM.initState, SMSchemeR.sendPart, libsignalSessionSchemeFromEpoch0Keys, Params.initA,
        initializeInitiatorSession]
      cases rootCreateChain P.C rk0 (KeyPair.generate P.C k.2.1).publicKey
        (KeyPair.generate P.C k.2.2.1).privateKey <;>
        simp [Bind.bind, Except.bind, Pure.pure, Except.pure, SessionState.new,
          SessionState.addReceiverChain, SessionState.setSenderChain,
          SessionState.setUnacknowledgedPreKeyMessage, maxReceiverChains]
    · dsimp only [sRef, SM.initState, SMSchemeR.sendPart, libsignalSessionSchemeFromEpoch0Keys, Params.initA,
        initializeInitiatorSession]
      cases rootCreateChain P.C rk0 (KeyPair.generate P.C k.2.1).publicKey
        (KeyPair.generate P.C k.2.2.1).privateKey <;>
        simp [Bind.bind, Except.bind, Pure.pure, Except.pure, SessionState.new,
          SessionState.addReceiverChain, SessionState.setSenderChain,
          SessionState.setUnacknowledgedPreKeyMessage, maxReceiverChains]
    · dsimp only [sRef, SM.initState, SMSchemeR.sendPart, libsignalSessionSchemeFromEpoch0Keys, Params.initA,
        initializeInitiatorSession]
      cases rootCreateChain P.C rk0 (KeyPair.generate P.C k.2.1).publicKey
        (KeyPair.generate P.C k.2.2.1).privateKey <;>
        simp [Bind.bind, Except.bind, Pure.pure, Except.pure, SessionState.new,
          SessionState.addReceiverChain, SessionState.setSenderChain,
          SessionState.setUnacknowledgedPreKeyMessage, maxReceiverChains]
    · dsimp only [sRef, SM.initState, SMSchemeR.sendPart, libsignalSessionSchemeFromEpoch0Keys, Params.initA,
        initializeInitiatorSession]
      cases rootCreateChain P.C rk0 (KeyPair.generate P.C k.2.1).publicKey
        (KeyPair.generate P.C k.2.2.1).privateKey <;>
        simp [Bind.bind, Except.bind, Pure.pure, Except.pure, SessionState.new,
          SessionState.addReceiverChain, SessionState.setSenderChain,
          SessionState.setUnacknowledgedPreKeyMessage, maxReceiverChains]
    · dsimp only [sRef, SM.initState, SMSchemeR.sendPart, libsignalSessionSchemeFromEpoch0Keys, Params.initA,
        initializeInitiatorSession]
      cases rootCreateChain P.C rk0 (KeyPair.generate P.C k.2.1).publicKey
        (KeyPair.generate P.C k.2.2.1).privateKey <;>
        simp [Bind.bind, Except.bind, Pure.pure, Except.pure, SessionState.new,
          SessionState.addReceiverChain, SessionState.setSenderChain,
          SessionState.setUnacknowledgedPreKeyMessage, maxReceiverChains, spk]
    · dsimp only [sRef, SM.initState, SMSchemeR.sendPart, libsignalSessionSchemeFromEpoch0Keys, Params.initA,
        initializeInitiatorSession]
      cases rootCreateChain P.C rk0 (KeyPair.generate P.C k.2.1).publicKey
        (KeyPair.generate P.C k.2.2.1).privateKey <;>
        simp [Bind.bind, Except.bind, Pure.pure, Except.pure]
  · refine ⟨rfl, rfl, by simp [sRef, SM.initState, SMSchemeR.sendPart, libsignalSessionSchemeFromEpoch0Keys, Params.initB], ?_⟩
    intro _
    refine ⟨rfl, rfl, ?_⟩
    intro sc hsc
    dsimp only [sRef, SM.initState, SMSchemeR.sendPart, libsignalSessionSchemeFromEpoch0Keys, Params.initB,
      initializeRecipientSession, SessionState.new, SessionState.setSenderChain] at hsc
    injection hsc with hsc
    subst hsc
    rfl

theorem patchGameState_afterCorr {ℓ : ℕ} (ck0 : BitVec 256) (sRef : GameSt PQ ℓ) (Q : Party) :
    (patchGameState ck0 sRef).afterCorr Q = patchGameState ck0 (sRef.afterCorr Q) :=
  rfl

theorem gameInv_afterCorr {ℓ : ℕ} {P : Params PQ PQC} {spk : PublicKey} {sRef : GameSt PQ ℓ}
    (Q : Party) (hinv : GameInv P spk sRef) : GameInv P spk (sRef.afterCorr Q) :=
  hinv

theorem send_record_patchGameState (P : Params PQ PQC) (ℓ : ℕ) (ck0 : BitVec 256)
    (spk : PublicKey) (sRef s₁ : GameSt PQ ℓ) (qep : ℕ) (Q : Party) (m : Plain ℓ)
    (coins : PQC) (bad isChall : Bool)
    (hinv : GameInv P spk sRef)
    (hsend : noBobSendInEpoch0 sRef Q = true)
    (hep : sRef.epMgmt 3 qep Q bad = some s₁) :
    let out := (libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).send (s₁.st Q) m coins
    let rec' : Record (Plain ℓ) (List (BitVec 8)) := ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m, out.2⟩
    ((libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).send ((patchGameState ck0 s₁).st Q) m coins).2 = out.2 ∧
    (patchGameState ck0 s₁).record 3 Q
      ((libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).send ((patchGameState ck0 s₁).st Q) m coins).1
      ⟨⟨Q, (patchGameState ck0 s₁).epoch Q, (patchGameState ck0 s₁).idx Q + 1⟩, m,
        ((libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).send ((patchGameState ck0 s₁).st Q) m coins).2⟩ isChall =
      patchGameState ck0 (s₁.record 3 Q out.1 rec' isChall) ∧
    GameInv P spk (s₁.record 3 Q out.1 rec' isChall) := by
  intro out rec'
  obtain ⟨hep_pos, hB_ne, hst, htr, hma, hwin, hA_ep⟩ := epMgmt_epoch_pos sRef 3 qep Q bad s₁ hsend hep
  cases Q with
  | A =>
    have hsendA := send_patchAlice P ck0 spk (sRef.st .A) m.toList coins hinv.1
    have h1 : (libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).send ((patchGameState ck0 s₁).st .A) m coins =
        (patchAlice ck0 out.1, out.2) := by
      change P.send (patchAlice ck0 (s₁.st .A)) m.toList coins =
        (patchAlice ck0 (P.send (s₁.st .A) m.toList coins).1, (P.send (s₁.st .A) m.toList coins).2)
      rw [hst]
      exact hsendA.1
    refine ⟨by rw [h1], ?_, ?_⟩
    · rw [h1]
      exact patchGameState_record ck0 s₁ 3 .A out.1 rec' isChall
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · dsimp only [GameState.record]
        rw [Function.update_self]
        change AliceInv P spk (P.send (s₁.st .A) m.toList coins).1
        rw [hst]
        exact hsendA.2
      · dsimp only [GameState.record]; rw [hA_ep rfl, Function.update_of_ne (by decide), hst]
        exact hinv.2.1
      · dsimp only [GameState.record]; rw [hma]; exact hinv.2.2.1
      · dsimp only [GameState.record]; rw [hwin]; exact hinv.2.2.2.1
      · intro r hr
        simp only [GameState.record, List.mem_cons] at hr
        rcases hr with rfl | hr
        · exact hep_pos
        · rw [htr] at hr; exact hinv.2.2.2.2 r hr
  | B =>
    have hne_ep : (sRef.st .B).epoch ≠ 0 := fun h0 => (hB_ne rfl).1 (hinv.2.1.2.2.2 h0).1
    have hsendB := send_patchBob P ck0 (sRef.st .B) m.toList coins hne_ep
    have hpB := send_preserve_fields P (sRef.st .B) m.toList coins
    have h1 : (libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).send ((patchGameState ck0 s₁).st .B) m coins =
        (patchBob ck0 out.1, out.2) := by
      change P.send (patchBob ck0 (s₁.st .B)) m.toList coins =
        (patchBob ck0 (P.send (s₁.st .B) m.toList coins).1, (P.send (s₁.st .B) m.toList coins).2)
      rw [hst]
      exact hsendB.1
    refine ⟨by rw [h1], ?_, ?_⟩
    · rw [h1]
      exact patchGameState_record ck0 s₁ 3 .B out.1 rec' isChall
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · dsimp only [GameState.record]; rw [Function.update_of_ne (by decide), hst]; exact hinv.1
      · dsimp only [GameState.record]; rw [Function.update_self]
        change BobInv P (s₁.epoch .B) (P.send (s₁.st .B) m.toList coins).1
        rw [hst]
        refine ⟨hpB.2.2.1.trans hinv.2.1.1, ?_, ?_, fun h0 => False.elim (hsendB.2 h0)⟩
        · rw [hpB.2.1, hpB.2.2.2.2]; exact hinv.2.1.2.1
        · rw [hpB.2.1]; exact hinv.2.1.2.2.1
      · dsimp only [GameState.record]; rw [hma]; exact hinv.2.2.1
      · dsimp only [GameState.record]; rw [hwin]; exact hinv.2.2.2.1
      · intro r hr
        simp only [GameState.record, List.mem_cons] at hr
        rcases hr with rfl | hr
        · exact hep_pos
        · rw [htr] at hr; exact hinv.2.2.2.2 r hr

def isAliceSpkQuery (P : Params PQ PQC) (spk : PublicKey) (Q : Party) (gA : GhostState PQ)
    (c : List (BitVec 8)) : Bool :=
  (Q == .A) && decide (0 ∈ gA.chainEpochs) &&
  match SignalMessage.tryFrom P.codec c with
  | .ok msg => spk == msg.senderRatchetKey
  | .error _ => false

theorem receive_patchGameState_of_not_spk (P : Params PQ PQC) (ℓ : ℕ) (ck0 : BitVec 256)
    (spk : PublicKey) (sRef : GameSt PQ ℓ) (Q : Party) (c : List (BitVec 8)) (rc : BitVec 256)
    (hinv : GameInv P spk sRef) (hnspk : isAliceSpkQuery P spk Q (sRef.st .A) c = false) :
    ((libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).receive ((patchGameState ck0 sRef).st Q) c rc =
      ((libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).receive (sRef.st Q) c rc).map fun x =>
        (patchParty ck0 Q x.1, x.2.1, x.2.2.1, x.2.2.2)) ∧
    ∀ st' t' i' m', (libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).receive (sRef.st Q) c rc = some (st', t', i', m') →
      0 < t' ∧
      (∀ pos : Pos, (Q = .A → 0 < pos.epoch) → GameInv P spk (sRef.accept Q st' pos)) := by
  cases Q with
  | A =>
    have hnonSpk : 0 ∉ (sRef.st .A).chainEpochs ∨
        ∀ msg, SignalMessage.tryFrom P.codec c = .ok msg → (spk == msg.senderRatchetKey) = false := by
      unfold isAliceSpkQuery at hnspk
      simp only [beq_self_eq_true, Bool.true_and, Bool.and_eq_false_iff,
        decide_eq_false_iff_not] at hnspk
      rcases hnspk with hnot0 | hmsg
      · exact Or.inl hnot0
      · right
        intro msg htry
        rw [htry] at hmsg
        exact hmsg
    have hA := receive_patchAlice_nonSpk P ck0 spk (sRef.st .A) c rc hinv.1 hnonSpk
    refine ⟨?_, ?_⟩
    · change (P.receive (patchAlice ck0 (sRef.st .A)) c rc).map
          (fun x => (x.1, x.2.1, x.2.2.1, padOrTruncatePlain ℓ x.2.2.2)) =
        ((P.receive (sRef.st .A) c rc).map
          (fun x => (x.1, x.2.1, x.2.2.1, padOrTruncatePlain ℓ x.2.2.2))).map
          (fun x => (patchAlice ck0 x.1, x.2.1, x.2.2.1, x.2.2.2))
      rw [hA.1]
      cases P.receive (sRef.st .A) c rc <;> rfl
    · intro st' t' i' m' hrecv
      change (P.receive (sRef.st .A) c rc).map
        (fun x => (x.1, x.2.1, x.2.2.1, padOrTruncatePlain ℓ x.2.2.2)) = some (st', t', i', m') at hrecv
      simp only [Option.map_eq_some_iff] at hrecv
      rcases hrecv with ⟨⟨g', t₀, i₀, m_raw⟩, hrecv_raw, htuple⟩
      rcases Prod.mk.inj htuple with ⟨hst', htuple2⟩
      rcases Prod.mk.inj htuple2 with ⟨ht', htuple3⟩
      rcases Prod.mk.inj htuple3 with ⟨hi', hm'⟩
      subst hst' ht' hi' hm'
      obtain ⟨hinvA', ht_pos⟩ := hA.2 g' t₀ i₀ m_raw hrecv_raw
      refine ⟨ht_pos, fun pos hpos => ?_⟩
      refine ⟨?_, ?_, ?_, hinv.2.2.2.1, ?_⟩
      · dsimp only [GameState.accept, GameState.delete]; rw [Function.update_self]; exact hinvA'
      · dsimp only [GameState.accept, GameState.delete]
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
        exact hinv.2.1
      · dsimp only [GameState.accept, GameState.delete]
        have hne : (0 : ℕ) ≠ pos.epoch := by
          have := hpos rfl; omega
        simp only [hne, and_false, ↓reduceIte]
        exact hinv.2.2.1
      · intro r hr
        simp only [GameState.accept, GameState.delete, List.mem_filter] at hr
        exact hinv.2.2.2.2 r hr.1
  | B =>
    have hB := receive_patchBob P ck0 (sRef.epoch .B) (sRef.st .B) c rc hinv.2.1
    refine ⟨?_, ?_⟩
    · change (P.receive (patchBob ck0 (sRef.st .B)) c rc).map
          (fun x => (x.1, x.2.1, x.2.2.1, padOrTruncatePlain ℓ x.2.2.2)) =
        ((P.receive (sRef.st .B) c rc).map
          (fun x => (x.1, x.2.1, x.2.2.1, padOrTruncatePlain ℓ x.2.2.2))).map
          (fun x => (patchBob ck0 x.1, x.2.1, x.2.2.1, x.2.2.2))
      rw [hB.1]
      cases hrecv : P.receive (sRef.st .B) c rc with
      | none => rfl
      | some val =>
        rcases val with ⟨g', t', i', m_raw⟩
        simp only [Option.map_some, (hB.2 g' t' i' m_raw hrecv).2.2]
    · intro st' t' i' m' hrecv
      change (P.receive (sRef.st .B) c rc).map
        (fun x => (x.1, x.2.1, x.2.2.1, padOrTruncatePlain ℓ x.2.2.2)) = some (st', t', i', m') at hrecv
      simp only [Option.map_eq_some_iff] at hrecv
      rcases hrecv with ⟨⟨g', t₀, i₀, m_raw⟩, hrecv_raw, htuple⟩
      rcases Prod.mk.inj htuple with ⟨hst', htuple2⟩
      rcases Prod.mk.inj htuple2 with ⟨ht', htuple3⟩
      rcases Prod.mk.inj htuple3 with ⟨hi', hm'⟩
      subst hst' ht' hi' hm'
      obtain ⟨hinvB', ht_pos, _⟩ := hB.2 g' t₀ i₀ m_raw hrecv_raw
      refine ⟨ht_pos, fun pos _ => ?_⟩
      refine ⟨?_, ?_, ?_, hinv.2.2.2.1, ?_⟩
      · dsimp only [GameState.accept, GameState.delete]
        rw [Function.update_of_ne (by decide)]
        exact hinv.1
      · dsimp only [GameState.accept, GameState.delete]
        rw [Function.update_self]
        exact hinvB' _
      · dsimp only [GameState.accept, GameState.delete]
        have hne : Party.A ≠ Party.B := by decide
        simp only [hne, false_and, ↓reduceIte]
        exact hinv.2.2.1
      · intro r hr
        simp only [GameState.accept, GameState.delete, List.mem_filter] at hr
        exact hinv.2.2.2.2 r hr.1

theorem receive_patchGameState_of_spk_test_false (P : Params PQ PQC) (ℓ : ℕ) (ck0 : BitVec 256)
    (spk : PublicKey) (sRef : GameSt PQ ℓ) (Q : Party) (c : List (BitVec 8)) (rc : BitVec 256)
    (hinv : GameInv P spk sRef) (hspk : isAliceSpkQuery P spk Q (sRef.st .A) c = true)
    (htest : testSpk P (sRef.st .A).session.pqRatchetState c ck0 = false) :
    Q = .A ∧ (libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).receive ((patchGameState ck0 sRef).st Q) c rc = none := by
  unfold isAliceSpkQuery at hspk
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hspk
  rcases hspk with ⟨⟨rfl, h0_in⟩, hmsg⟩
  refine ⟨rfl, ?_⟩
  cases htry : SignalMessage.tryFrom P.codec c with
  | error _ => rw [htry] at hmsg; cases hmsg
  | ok msg =>
    rw [htry] at hmsg
    simp only [beq_iff_eq] at hmsg
    rcases hinv.1 with ⟨_, hrem, hloc, _, ⟨h0_notin, _⟩ | ⟨rest, epochsTail, hcs, _, _⟩⟩
    · exact False.elim (h0_notin h0_in)
    · change (P.receive (patchAlice ck0 (sRef.st .A)) c rc).map _ = none
      have hpatch : patchAlice ck0 (sRef.st .A) = setAliceSpkKey ck0 (sRef.st .A) := by
        unfold patchAlice; simp [h0_in]
      rw [hpatch]
      cases hrecv : P.receive (setAliceSpkKey ck0 (sRef.st .A)) c rc with
      | none => rfl
      | some val =>
        exfalso
        have htrue := receive_alice_spk_implies_testSpk P ck0 (sRef.st .A) spk rest c rc msg
          hrem hloc hcs htry hmsg.symm (by simp [hrecv])
        rw [htrue] at htest
        cases htest

def TransShort {St Msg : Type} (s : GameState St Msg (List (BitVec 8))) : Prop :=
  ∀ r ∈ s.trans, r.ct.length < 2 ^ 32

theorem transShort_accept {St Msg : Type} {s : GameState St Msg (List (BitVec 8))}
    (h : TransShort s) (Q : Party) (st' : St) (pos : Pos) : TransShort (s.accept Q st' pos) := by
  intro r hr
  simp only [GameState.accept, GameState.delete, List.mem_filter] at hr
  exact h r hr.1

theorem transShort_afterCorr {St Msg : Type} {s : GameState St Msg (List (BitVec 8))}
    (h : TransShort s) (Q : Party) : TransShort (s.afterCorr Q) := h

theorem transShort_record {St Msg : Type} {s : GameState St Msg (List (BitVec 8))}
    (h : TransShort s) (Δ : ℕ) (Q : Party) (st' : St) (r : Record Msg (List (BitVec 8)))
    (b : Bool) (hr : r.ct.length < 2 ^ 32) : TransShort (s.record Δ Q st' r b) := by
  intro r' hr'
  simp only [GameState.record, List.mem_cons] at hr'
  rcases hr' with rfl | hr'
  · exact hr
  · exact h r' hr'

theorem transShort_epMgmt {St Msg : Type} {s s₁ : GameState St Msg (List (BitVec 8))}
    {Δ qep : ℕ} {Q : Party} {bad : Bool} (h : s.epMgmt Δ qep Q bad = some s₁)
    (hs : TransShort s) : TransShort s₁ := by
  have htr : s₁.trans = s.trans := by
    unfold GameState.epMgmt at h
    split at h
    · split at h
      · cases h
      · cases h
        dsimp only
        split <;> rfl
    · split at h
      · cases h
      · cases h; rfl
  intro r hr
  exact hs r (by rw [← htr]; exact hr)

theorem ct_length_lt_of_inTransit {St Msg : Type} {s : GameState St Msg (List (BitVec 8))}
    (h : TransShort s) (Q : Party) (c : List (BitVec 8)) (r : Record Msg (List (BitVec 8)))
    (hin : s.inTransit Q c = some r) : c.length < 2 ^ 32 := by
  unfold GameState.inTransit at hin
  have hp := List.find?_some hin
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  rw [← hp.2]
  exact h r (List.mem_of_find?_eq_some hin)

theorem ratchetKeyAdmissible_length_lt_of_tryFrom {Pt' : Type} [DecidableEq PublicKey]
    (codec : SignalMessageProtoCodec) (decT : PublicKey → Option Pt') (encT : Pt' → PublicKey)
    (c : List (BitVec 8)) (msg : SignalMessage)
    (hadm : ratchetKeyAdmissible codec decT encT c = true)
    (htry : SignalMessage.tryFrom codec c = .ok msg) : c.length < 2 ^ 32 := by
  obtain ⟨hl, hp⟩ := tryFrom_parse_eq codec c msg htry
  unfold ratchetKeyAdmissible at hadm
  simp only [hl, ↓reduceIte, hp, Bool.and_eq_true, decide_eq_true_eq] at hadm
  exact hadm.1

theorem send_ct_length_lt (P : Params PQ PQC) (ℓ : ℕ) (hrt : RoundTrip.RtHyp P ℓ)
    (g : GhostState PQ) (m : Plain ℓ) (r : PQC) :
    ((libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).send g m r).2.length < 2 ^ 32 := by
  change (P.send g m.toList r).2.length < 2 ^ 32
  exact hrt.send_length_lt g m.toList (by simp) r

theorem d0Oracle_transmit_le (P : Params PQ PQC) (ℓ : ℕ) (onImage : List (BitVec 8) → Bool)
    (qep : ℕ) (spk : PublicKey) (sRef : GameSt PQ ℓ) (hinv : GameInv P spk sRef) (hts : TransShort sRef)
    (hrt : RoundTrip.RtHyp P ℓ) (Q : Party) (m : Plain ℓ) (r : Option PQC)
    (B : ℝ≥0∞) (F : Option (List (BitVec 8)) → GameSt PQ ℓ → ProbComp Bool)
    (hF : ∀ u sRef', GameInv P spk sRef' → TransShort sRef' →
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ck0 => F u (patchGameState ck0 sRef')] {true} ≤ B) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ck0 =>
      ((SM.transmitR (libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0) 3 qep (configEpoch0Distinguisher onImage) (Q, m, r)).run
        (patchGameState ck0 sRef)) >>= fun us => F us.1 us.2] {true} ≤ B := by
  unfold SM.transmitR SM.transmitImpl
  have hts_ep : ∀ (s₁ : GameSt PQ ℓ) (bad : Bool), sRef.epMgmt 3 qep Q bad = some s₁ → TransShort s₁ :=
    fun _ _ h => transShort_epMgmt h hts
  have hsendOK : ∀ ck0, (configEpoch0Distinguisher onImage).sendOK (patchGameState ck0 sRef) Q = noBobSendInEpoch0 sRef Q :=
    fun _ => rfl
  have hwin : ∀ ck0, (patchGameState ck0 sRef).win = sRef.win := fun _ => rfl
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hsendOK, hwin]
  by_cases hs : (!noBobSendInEpoch0 sRef Q) = true
  · simp only [hs, ↓reduceIte, StateT.run_pure, pure_bind]
    exact hF none sRef hinv hts
  · simp only [hs, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind, hwin]
    have hsend : noBobSendInEpoch0 sRef Q = true := by simpa using hs
    by_cases hw : sRef.win = true
    · simp only [hw, ↓reduceIte, StateT.run_pure, pure_bind]
      exact hF none sRef hinv hts
    · simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, bind_assoc, pure_bind, patchGameState_epMgmt]
      rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) (SM.samIfNec r)]
      refine evalDist_bind_le_const (SM.samIfNec r) _ B fun cb => ?_
      cases hep : sRef.epMgmt 3 qep Q cb.2 with
      | none =>
        simp only [Option.map_none, StateT.run_pure, pure_bind]
        exact hF none sRef hinv hts
      | some s₁ =>
        dsimp only [Option.map]
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
        obtain ⟨_, _, h3⟩ :=
          send_record_patchGameState P ℓ 0 spk sRef s₁ qep Q m cb.1 cb.2 false hinv hsend hep
        refine le_trans (le_of_eq ?_)
          (hF (some ((libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).send (s₁.st Q) m cb.1).2) _ h3
            (transShort_record (hts_ep s₁ _ hep) 3 Q _ _ _ (send_ct_length_lt P ℓ hrt _ _ _)))
        congr 1; congr 1; congr 1; funext ck0
        obtain ⟨hc1, hc2, _⟩ :=
          send_record_patchGameState P ℓ ck0 spk sRef s₁ qep Q m cb.1 cb.2 false hinv hsend hep
        change F (some ((libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).send ((patchGameState ck0 s₁).st Q) m cb.1).2)
            ((patchGameState ck0 s₁).record 3 Q
              ((libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).send ((patchGameState ck0 s₁).st Q) m cb.1).1
              ⟨⟨Q, (patchGameState ck0 s₁).epoch Q, (patchGameState ck0 s₁).idx Q + 1⟩, m,
                ((libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).send ((patchGameState ck0 s₁).st Q) m cb.1).2⟩ false) =
          F (some ((libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).send (s₁.st Q) m cb.1).2)
            (patchGameState ck0 (s₁.record 3 Q ((libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).send (s₁.st Q) m cb.1).1
              ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m,
                ((libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).send (s₁.st Q) m cb.1).2⟩ false))
        rw [hc2, hc1]

theorem d0Oracle_chall_le (P : Params PQ PQC) (ℓ : ℕ) (onImage : List (BitVec 8) → Bool)
    (qep : ℕ) (spk : PublicKey) (sRef : GameSt PQ ℓ) (hinv : GameInv P spk sRef) (hts : TransShort sRef)
    (hrt : RoundTrip.RtHyp P ℓ) (Q : Party) (m₀ m₁ : Plain ℓ) (r : Option PQC)
    (B : ℝ≥0∞) (F : Option (List (BitVec 8)) → GameSt PQ ℓ → ProbComp Bool)
    (hF : ∀ u sRef', GameInv P spk sRef' → TransShort sRef' →
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ck0 => F u (patchGameState ck0 sRef')] {true} ≤ B) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ck0 =>
      ((SM.challR (libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0) 3 qep (configEpoch0Distinguisher onImage) (Q, m₀, m₁, r)).run
        (patchGameState ck0 sRef)) >>= fun us => F us.1 us.2] {true} ≤ B := by
  unfold SM.challR SM.challImpl
  have hts_ep : ∀ (s₁ : GameSt PQ ℓ) (bad : Bool), sRef.epMgmt 3 qep Q bad = some s₁ → TransShort s₁ :=
    fun _ _ h => transShort_epMgmt h hts
  have hsendOK : ∀ ck0, (configEpoch0Distinguisher onImage).sendOK (patchGameState ck0 sRef) Q = noBobSendInEpoch0 sRef Q :=
    fun _ => rfl
  have hwin : ∀ ck0, (patchGameState ck0 sRef).win = sRef.win := fun _ => rfl
  have hb : ∀ ck0, (patchGameState ck0 sRef).b = sRef.b := fun _ => rfl
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hsendOK, hwin, hb]
  by_cases hs : (!noBobSendInEpoch0 sRef Q) = true
  · simp only [hs, ↓reduceIte, StateT.run_pure, pure_bind]
    exact hF none sRef hinv hts
  · simp only [hs, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind, hwin, hb]
    have hsend : noBobSendInEpoch0 sRef Q = true := by simpa using hs
    by_cases hw : sRef.win = true
    · simp only [hw, ↓reduceIte, StateT.run_pure, pure_bind]
      exact hF none sRef hinv hts
    · simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, bind_assoc, pure_bind, patchGameState_epMgmt]
      rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) (SM.samIfNec r)]
      refine evalDist_bind_le_const (SM.samIfNec r) _ B fun cb => ?_
      cases hep : sRef.epMgmt 3 qep Q cb.2 with
      | none =>
        simp only [Option.map_none, StateT.run_pure, pure_bind]
        exact hF none sRef hinv hts
      | some s₁ =>
        have hsafe : ∀ ck0, (patchGameState ck0 s₁).safeCh 3 Q = s₁.safeCh 3 Q := fun _ => rfl
        have hep1 : ∀ ck0, (patchGameState ck0 s₁).epoch Q = s₁.epoch Q := fun _ => rfl
        dsimp only [Option.map]
        simp only [hsafe, hep1]
        by_cases hch : (!s₁.safeCh 3 Q || !(configEpoch0Distinguisher (PQ := PQ) (ℓ := ℓ) onImage).base.challAllowedIn (s₁.epoch Q)) = true
        · simp only [hch, ↓reduceIte, StateT.run_pure, pure_bind]
          exact hF none sRef hinv hts
        · simp only [hch, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
          let m := ((configEpoch0Distinguisher (PQ := PQ) (ℓ := ℓ) onImage).base.challMsg (s₁.epoch Q)).getD (if sRef.b then m₁ else m₀)
          obtain ⟨_, _, h3⟩ :=
            send_record_patchGameState P ℓ 0 spk sRef s₁ qep Q m cb.1 cb.2 true hinv hsend hep
          refine le_trans (le_of_eq ?_)
            (hF (some ((libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).send (s₁.st Q) m cb.1).2) _ h3
            (transShort_record (hts_ep s₁ _ hep) 3 Q _ _ _ (send_ct_length_lt P ℓ hrt _ _ _)))
          congr 1; congr 1; congr 1; funext ck0
          obtain ⟨hc1, hc2, _⟩ :=
            send_record_patchGameState P ℓ ck0 spk sRef s₁ qep Q m cb.1 cb.2 true hinv hsend hep
          change F (some ((libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).send ((patchGameState ck0 s₁).st Q) m cb.1).2)
              ((patchGameState ck0 s₁).record 3 Q
                ((libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).send ((patchGameState ck0 s₁).st Q) m cb.1).1
                ⟨⟨Q, s₁.epoch Q, (patchGameState ck0 s₁).idx Q + 1⟩, m,
                  ((libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).send ((patchGameState ck0 s₁).st Q) m cb.1).2⟩ true) =
            F (some ((libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).send (s₁.st Q) m cb.1).2)
              (patchGameState ck0 (s₁.record 3 Q ((libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).send (s₁.st Q) m cb.1).1
                ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m,
                  ((libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).send (s₁.st Q) m cb.1).2⟩ true))
          rw [hep1] at hc2
          rw [hc2, hc1]

theorem corrGuard_patchGameState {PQ : Type} [Inhabited PQ] {ℓ : ℕ} (onImage : List (BitVec 8) → Bool)
    (ck0 : BitVec 256) (sRef : GameSt PQ ℓ) (Q : Party) :
    ((patchGameState ck0 sRef).win || !(patchGameState ck0 sRef).corrAllowed Q ||
      ((configEpoch0Distinguisher (PQ := PQ) (ℓ := ℓ) onImage).r1 && inWindow (patchGameState ck0 sRef) Q) ||
      !(configEpoch0Distinguisher (PQ := PQ) (ℓ := ℓ) onImage).corrOK (patchGameState ck0 sRef) Q) =
    (sRef.win || !sRef.corrAllowed Q ||
      ((configEpoch0Distinguisher (PQ := PQ) (ℓ := ℓ) onImage).r1 && inWindow sRef Q) ||
      !(configEpoch0Distinguisher (PQ := PQ) (ℓ := ℓ) onImage).corrOK sRef Q) := by
  unfold configEpoch0Distinguisher patchGameState GameState.corrAllowed inWindow noAliceCorrWhileAliceBelowEpoch10
  dsimp only []
  rw [patchAlice_chainEpochs]

theorem d0Oracle_corr_le (P : Params PQ PQC) (ℓ : ℕ) (onImage : List (BitVec 8) → Bool)
    (spk : PublicKey) (sRef : GameSt PQ ℓ) (hinv : GameInv P spk sRef) (hts : TransShort sRef) (Q : Party)
    (B : ℝ≥0∞) (F : Option (GhostState PQ) → GameSt PQ ℓ → ProbComp Bool)
    (hF : ∀ u sRef', GameInv P spk sRef' → TransShort sRef' →
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ck0 => F u (patchGameState ck0 sRef')] {true} ≤ B)
    (hF_corrs : ∀ u s', s'.corrs.contains (.B, 0) = true → 𝒟[F u s'] {true} ≤ 0) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ck0 =>
      ((SM.corrR (configEpoch0Distinguisher onImage) Q).run (patchGameState ck0 sRef)) >>= fun us => F us.1 us.2] {true} ≤ B := by
  unfold SM.corrR
  simp only [StateT.run_bind, StateT.run_get, pure_bind, corrGuard_patchGameState]
  by_cases hg : (sRef.win || !sRef.corrAllowed Q ||
      ((configEpoch0Distinguisher (PQ := PQ) (ℓ := ℓ) onImage).r1 && inWindow sRef Q) ||
      !(configEpoch0Distinguisher (PQ := PQ) (ℓ := ℓ) onImage).corrOK sRef Q) = true
  · simp only [hg, ↓reduceIte, StateT.run_pure, pure_bind]
    exact hF none sRef hinv hts
  · simp only [hg, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, patchGameState_afterCorr]
    cases Q with
    | A =>
      have hcorrOK : (configEpoch0Distinguisher (PQ := PQ) (ℓ := ℓ) onImage).corrOK sRef .A = true := by
        simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false] at hg
        exact hg.2
      have h0_notin : 0 ∉ (sRef.st .A).chainEpochs := by
        unfold configEpoch0Distinguisher noAliceCorrWhileAliceBelowEpoch10 at hcorrOK
        simp only [Bool.and_eq_true, beq_self_eq_true, Bool.true_and, Bool.not_eq_true',
          List.contains_eq_mem, decide_eq_false_iff_not] at hcorrOK
        exact hcorrOK.2
      have hstA : ∀ ck0, (patchGameState ck0 sRef).st .A = sRef.st .A := by
        intro ck0
        unfold patchGameState patchAlice
        simp [h0_notin]
      simp only [hstA]
      exact hF (some (sRef.st .A)) (sRef.afterCorr .A) (gameInv_afterCorr .A hinv) (transShort_afterCorr hts .A)
    | B =>
      by_cases heb : sRef.epoch .B = 0
      · refine (evalDist_bind_le_const ($ᵗ BitVec 256) _ 0 fun ck0 => ?_).trans (zero_le : 0 ≤ B)
        refine hF_corrs _ _ ?_
        unfold GameState.afterCorr GameState.leak patchGameState
        simp [heb]
      · have hne : (sRef.st .B).epoch ≠ 0 := fun h0 => heb (hinv.2.1.2.2.2 h0).1
        have hstB : ∀ ck0, (patchGameState ck0 sRef).st .B = sRef.st .B := by
          intro ck0
          unfold patchGameState patchBob
          simp [hne]
        simp only [hstB]
        exact hF (some (sRef.st .B)) (sRef.afterCorr .B) (gameInv_afterCorr .B hinv) (transShort_afterCorr hts .B)

theorem d0Oracle_deliver_le (P : Params PQ PQC) (ℓ : ℕ) (onImage : List (BitVec 8) → Bool)
    (spk : PublicKey) (sRef : GameSt PQ ℓ) (hinv : GameInv P spk sRef) (hts : TransShort sRef)
    (Q : Party) (c : List (BitVec 8))
    (B : ℝ≥0∞) (F : Option (RecvResult (Plain ℓ)) → GameSt PQ ℓ → ProbComp Bool)
    (hF : ∀ u sRef', GameInv P spk sRef' → TransShort sRef' →
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ck0 => F u (patchGameState ck0 sRef')] {true} ≤ B) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ck0 =>
      ((SM.deliverR (libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0) (configEpoch0Distinguisher onImage) (Q, c)).run
        (patchGameState ck0 sRef)) >>= fun us => F us.1 us.2] {true} ≤
      eps0IdealUnit P.C.F + B := by
  unfold SM.deliverR
  have hwin : ∀ ck0, (patchGameState ck0 sRef).win = sRef.win := fun _ => rfl
  have htr : ∀ ck0, (patchGameState ck0 sRef).inTransit Q.other c = sRef.inTransit Q.other c :=
    fun _ => rfl
  have hch : ∀ ck0, (patchGameState ck0 sRef).chall = sRef.chall := fun _ => rfl
  have hmust : ∀ ck0 r,
      ((configEpoch0Distinguisher (PQ := PQ) (ℓ := ℓ) onImage).base.deliverWin &&
        (configEpoch0Distinguisher (PQ := PQ) (ℓ := ℓ) onImage).must (patchGameState ck0 sRef) Q r) =
        false := fun _ _ => rfl
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hwin, htr, hch, hmust, Bool.false_and]
  by_cases hw : sRef.win = true
  · simp only [hw, ↓reduceIte, StateT.run_pure, pure_bind]
    exact (hF none sRef hinv hts).trans le_add_self
  · simp only [hw, Bool.false_eq_true, ↓reduceIte]
    cases h_in : sRef.inTransit Q.other c with
    | none =>
      simp only [StateT.run_pure, pure_bind]
      exact (hF none sRef hinv hts).trans le_add_self
    | some r =>
      have hr_pos : 0 < r.pos.epoch := by
        unfold GameState.inTransit at h_in
        exact hinv.2.2.2.2 r (List.mem_of_find?_eq_some h_in)
      simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
      by_cases hspk : isAliceSpkQuery P spk Q (sRef.st .A) c = true
      · have hc32 : c.length < 2 ^ 32 := ct_length_lt_of_inTransit hts Q.other c r h_in
        refine (evalDist_sample_split (testSpk P (sRef.st .A).session.pqRatchetState c)
          _ (fun ck0 => F (some .rejected) (patchGameState ck0 sRef)) ?_).trans ?_
        · intro ck0 htest
          have hnone : ∀ rc,
              (libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).receive ((patchGameState ck0 sRef).st Q) c rc = none :=
            fun rc => (receive_patchGameState_of_spk_test_false P ℓ ck0 spk sRef Q c rc hinv hspk htest).2
          simp only [hnone, ↓reduceIte, StateT.run_pure, pure_bind,
            OracleComp.evalDist_bind_const ($ᵗ BitVec 256)]
          exact le_rfl
        · exact add_le_add (testSpk_le_unit P (sRef.st .A).session.pqRatchetState c hc32)
            (hF (some .rejected) sRef hinv hts)
      · have hnspk : isAliceSpkQuery P spk Q (sRef.st .A) c = false :=
          Bool.eq_false_iff.mpr hspk
        rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]
        refine evalDist_bind_le_const ($ᵗ BitVec 256) _ (eps0IdealUnit P.C.F + B) fun rc => ?_
        cases hrecv : (libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).receive (sRef.st Q) c rc with
        | none =>
          have hnone : ∀ ck0,
              (libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).receive ((patchGameState ck0 sRef).st Q) c rc = none := by
            intro ck0
            rw [(receive_patchGameState_of_not_spk P ℓ ck0 spk sRef Q c rc hinv hnspk).1, hrecv]
            rfl
          simp only [hnone, ↓reduceIte, StateT.run_pure, pure_bind]
          exact (hF (some .rejected) sRef hinv hts).trans le_add_self
        | some val =>
          rcases val with ⟨st', t', i', m'⟩
          have hsome : ∀ ck0,
              (libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).receive ((patchGameState ck0 sRef).st Q) c rc =
                some (patchParty ck0 Q st', t', i', m') := by
            intro ck0
            rw [(receive_patchGameState_of_not_spk P ℓ ck0 spk sRef Q c rc hinv hnspk).1, hrecv]
            rfl
          have hinv' : GameInv P spk (sRef.accept Q st' r.pos) :=
            ((receive_patchGameState_of_not_spk P ℓ 0 spk sRef Q c rc hinv hnspk).2
              st' t' i' m' hrecv).2 r.pos (fun _ => hr_pos)
          simp only [hsome, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure,
            pure_bind, patchGameState_accept]
          exact (hF _ (sRef.accept Q st' r.pos) hinv' (transShort_accept hts Q st' r.pos)).trans le_add_self

theorem d0Oracle_inject_le (P : Params PQ PQC) (ℓ : ℕ) (onImage : List (BitVec 8) → Bool)
    (honImg : ∀ c msg, onImage c = true → SignalMessage.tryFrom P.codec c = .ok msg →
      c.length < 2 ^ 32)
    (qep : ℕ) (spk : PublicKey) (sRef : GameSt PQ ℓ) (hinv : GameInv P spk sRef) (hts : TransShort sRef)
    (Q : Party) (c : List (BitVec 8))
    (B : ℝ≥0∞) (F : Option (RecvResult (Plain ℓ)) → GameSt PQ ℓ → ProbComp Bool)
    (hF : ∀ u sRef', GameInv P spk sRef' → TransShort sRef' →
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ck0 => F u (patchGameState ck0 sRef')] {true} ≤ B) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ck0 =>
      ((SM.injectR (libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0) 3 qep (configEpoch0Distinguisher onImage) (Q, c)).run
        (patchGameState ck0 sRef)) >>= fun us => F us.1 us.2] {true} ≤
      eps0IdealUnit P.C.F + B := by
  unfold SM.injectR
  have hguard : ∀ ck0,
      ((patchGameState ck0 sRef).win || ((patchGameState ck0 sRef).inTransit Q.other c).isSome ||
        !(patchGameState ck0 sRef).safeInj 3 || !(configEpoch0Distinguisher (PQ := PQ) (ℓ := ℓ) onImage).injOK c) =
      (sRef.win || (sRef.inTransit Q.other c).isSome ||
        !sRef.safeInj 3 || !(configEpoch0Distinguisher (PQ := PQ) (ℓ := ℓ) onImage).injOK c) := fun _ => rfl
  have htriv : ∀ ck0 pos, (patchGameState ck0 sRef).trivial 3 pos = sRef.trivial 3 pos :=
    fun _ _ => rfl
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hguard, htriv]
  by_cases hg : (sRef.win || (sRef.inTransit Q.other c).isSome ||
      !sRef.safeInj 3 || !(configEpoch0Distinguisher (PQ := PQ) (ℓ := ℓ) onImage).injOK c) = true
  · simp only [hg, ↓reduceIte, StateT.run_pure, pure_bind]
    exact (hF none sRef hinv hts).trans le_add_self
  · simp only [hg, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
       monadLift_self, bind_assoc, pure_bind]
    by_cases hspk : isAliceSpkQuery P spk Q (sRef.st .A) c = true
    · have hc32 : c.length < 2 ^ 32 := by
        cases htry : SignalMessage.tryFrom P.codec c with
        | error _ =>
          unfold isAliceSpkQuery at hspk; rw [htry] at hspk; simp at hspk
        | ok msg =>
          refine honImg c msg ?_ htry
          simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false] at hg
          exact hg.2
      refine (evalDist_sample_split (testSpk P (sRef.st .A).session.pqRatchetState c)
        _ (fun ck0 => F (some .rejected) (patchGameState ck0 sRef)) ?_).trans ?_
      · intro ck0 htest
        have hnone : ∀ rc,
            (libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).receive ((patchGameState ck0 sRef).st Q) c rc = none :=
          fun rc => (receive_patchGameState_of_spk_test_false P ℓ ck0 spk sRef Q c rc hinv hspk htest).2
        simp only [hnone, StateT.run_pure, pure_bind,
          OracleComp.evalDist_bind_const ($ᵗ BitVec 256)]
        exact le_rfl
      · exact add_le_add (testSpk_le_unit P (sRef.st .A).session.pqRatchetState c hc32)
          (hF (some .rejected) sRef hinv hts)
    · have hnspk : isAliceSpkQuery P spk Q (sRef.st .A) c = false :=
        Bool.eq_false_iff.mpr hspk
      rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]
      refine evalDist_bind_le_const ($ᵗ BitVec 256) _ (eps0IdealUnit P.C.F + B) fun rc => ?_
      cases hrecv : (libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).receive (sRef.st Q) c rc with
      | none =>
        have hnone : ∀ ck0,
            (libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).receive ((patchGameState ck0 sRef).st Q) c rc = none := by
          intro ck0
          rw [(receive_patchGameState_of_not_spk P ℓ ck0 spk sRef Q c rc hinv hnspk).1, hrecv]
          rfl
        simp only [hnone, StateT.run_pure, pure_bind]
        exact (hF (some .rejected) sRef hinv hts).trans le_add_self
      | some val =>
        rcases val with ⟨st', t', i', m'⟩
        have hsome : ∀ ck0,
            (libsignalSessionSchemeFromEpoch0Keys P ℓ 0 0).receive ((patchGameState ck0 sRef).st Q) c rc =
              some (patchParty ck0 Q st', t', i', m') := by
          intro ck0
          rw [(receive_patchGameState_of_not_spk P ℓ ck0 spk sRef Q c rc hinv hnspk).1, hrecv]
          rfl
        obtain ⟨ht_pos, hinv_acc⟩ :=
          (receive_patchGameState_of_not_spk P ℓ 0 spk sRef Q c rc hinv hnspk).2 st' t' i' m' hrecv
        simp only [hsome]
        by_cases hcap : qep + 1 < t'
        · simp only [hcap, ↓reduceIte, StateT.run_pure, pure_bind]
          exact (hF (some .rejected) sRef hinv hts).trans le_add_self
        · simp only [hcap, ↓reduceIte]
          by_cases htr : sRef.trivial 3 ⟨Q.other, t', i'⟩ = true
          · simp only [htr, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure,
              pure_bind, patchGameState_accept]
            exact (hF _ (sRef.accept Q st' ⟨Q.other, t', i'⟩)
              (hinv_acc ⟨Q.other, t', i'⟩ (fun _ => ht_pos))
              (transShort_accept hts Q st' ⟨Q.other, t', i'⟩)).trans le_add_self
          · have hinj0 : (configEpoch0Distinguisher (PQ := PQ) (ℓ := ℓ) onImage).base.injectFull t' = false := by
              change (t' == 0) = false
              simp [Nat.ne_of_gt ht_pos]
            simp only [htr, Bool.false_eq_true, ↓reduceIte, hinj0, StateT.run_pure, pure_bind]
            exact (hF (some .rejected) sRef hinv hts).trans le_add_self

theorem evalDist_d0Exp_le {α : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (onImage : List (BitVec 8) → Bool) (qep : ℕ) (spk : PublicKey)
    (hrt : RoundTrip.RtHyp P ℓ)
    (honImg : ∀ c msg, onImage c = true → SignalMessage.tryFrom P.codec c = .ok msg →
      c.length < 2 ^ 32)
    {p : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain → Prop}
    [DecidablePred p]
    (hp_inl : ∀ t, ¬ p (.inl t)) (hp_inr : ∀ t, p (.inr t))
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    {rem : ℕ} (hq : oa.IsQueryBoundP p rem)
    (sRef : GameSt PQ ℓ) (hinv : GameInv P spk sRef) (hts : TransShort sRef) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ck0 => do
      let (_, s') ← (simulateQ (d0Impl P ℓ onImage qep) oa).run (patchGameState ck0 sRef)
      pure (winPred s')] {true} ≤ (rem : ℕ) * eps0IdealUnit P.C.F := by
  induction oa using OracleComp.inductionOn generalizing rem sRef with
  | pure a =>
    have hw : ∀ ck0, winPred (patchGameState ck0 sRef) = false := by
      intro ck0
      unfold winPred patchGameState
      simp [hinv.2.2.1, hinv.2.2.2.1]
    simp [hw]
  | query_bind t r ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at hq
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_eq, map_eq_bind_pure_comp, Function.comp_apply, pure_bind, StateT.run_bind, bind_assoc]
    rcases t with q_u | q_sm
    · have hq' : ∀ u, (r u).IsQueryBoundP p rem := fun u => by simpa [hp_inl q_u] using hq.2 u
      simp only [d0Impl_inl_run, bind_assoc, pure_bind]
      rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) (query q_u)]
      exact evalDist_bind_le_const (query q_u) _ _ fun u => ih u (hq' u) sRef hinv hts
    · have hpos : 0 < rem := hq.1.resolve_left (not_not.mpr (hp_inr q_sm))
      have hq' : ∀ u, (r u).IsQueryBoundP p (rem - 1) := fun u => by
        simpa [hp_inr q_sm] using hq.2 u
      have hrem_eq : eps0IdealUnit P.C.F + (rem - 1 : ℕ) * eps0IdealUnit P.C.F =
          (rem : ℕ) * eps0IdealUnit P.C.F := by
        have h1 : (rem : ℝ≥0∞) = (1 : ℕ) + (rem - 1 : ℕ) := by norm_cast; omega
        rw [h1, add_mul, Nat.cast_one, one_mul]
      let F := fun u (s' : GameSt PQ ℓ) => do
        let (_, s'') ← (simulateQ (d0Impl P ℓ onImage qep) (r u)).run s'
        pure (winPred s'')
      have hF : ∀ u sRef', GameInv P spk sRef' → TransShort sRef' →
          𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ck0 =>
            F u (patchGameState ck0 sRef')] {true} ≤ (rem - 1 : ℕ) * eps0IdealUnit P.C.F :=
        fun u sRef' hinv' hts' => ih u (hq' u) sRef' hinv' hts'
      rcases q_sm with (((q_tr | q_ch) | q_del) | q_inj) | q_corr
      · rcases q_tr with ⟨Q, m, rc⟩
        exact (d0Oracle_transmit_le P ℓ onImage qep spk sRef hinv hts hrt Q m rc _ F hF).trans
          (le_add_self.trans_eq hrem_eq)
      · rcases q_ch with ⟨Q, m₀, m₁, rc⟩
        exact (d0Oracle_chall_le P ℓ onImage qep spk sRef hinv hts hrt Q m₀ m₁ rc _ F hF).trans
          (le_add_self.trans_eq hrem_eq)
      · rcases q_del with ⟨Q, c⟩
        exact (d0Oracle_deliver_le P ℓ onImage spk sRef hinv hts Q c _ F hF).trans_eq hrem_eq
      · rcases q_inj with ⟨Q, c⟩
        exact (d0Oracle_inject_le P ℓ onImage honImg qep spk sRef hinv hts Q c _ F hF).trans_eq hrem_eq
      · refine (d0Oracle_corr_le P ℓ onImage spk sRef hinv hts q_corr _ F hF ?_).trans
          (le_add_self.trans_eq hrem_eq)
        intro u s' hs'
        exact evalDist_winPred_of_corrs P ℓ onImage qep (r u) s' hs'

set_option linter.unusedVariables false in
/-- Bounds the ideal `epoch0Distinguisher` win probability for a `q`-query adversary by `q * eps0IdealUnit P.C.F`. -/
theorem eps0_ideal_le (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (hrt : RoundTrip.RtHyp P ℓ)
    (qep q : ℕ) (A : LibAdv PQ PQC ℓ) (hq : SM.MakesAtMostQueries A q) :
    𝒟[PRGScheme.prgIdealExperiment (epoch0Distinguisher P ℓ (ratchetKeyAdmissible P.codec decT encT) qep A)] {true} ≤
      q * eps0IdealUnit P.C.F := by
  let onImage := ratchetKeyAdmissible P.codec decT encT
  unfold PRGScheme.prgIdealExperiment epoch0Distinguisher SM.runR
  rw [sample_prod_bind]
  refine evalDist_bind_le_const ($ᵗ Ratchet.RootKey) _ _ fun rk0 => ?_
  have himpl : ∀ ck0,
      (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (GameSt PQ ℓ) ProbComp) +
        SM.oracleImplR (libsignalSessionSchemeFromEpoch0Keys P ℓ rk0 ck0) 3 qep (configEpoch0Distinguisher onImage) =
        d0Impl P ℓ onImage qep :=
    fun ck0 => oracleImplR_libSessionR0_eq P ℓ rk0 ck0 onImage qep
  simp only [bind_assoc]
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ Bool)]
  refine evalDist_bind_le_const ($ᵗ Bool) _ _ fun b => ?_
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256)
    ($ᵗ (Ratchet.RootKey × BitVec 256 × BitVec 256 × BitVec 256))]
  refine evalDist_bind_le_const
    ($ᵗ (Ratchet.RootKey × BitVec 256 × BitVec 256 × BitVec 256)) _ _ fun k => ?_
  have hinit : ∀ ck0,
      SM.initState (libsignalSessionSchemeFromEpoch0Keys P ℓ rk0 ck0).sendPart k b =
        patchGameState ck0 (SM.initState (libsignalSessionSchemeFromEpoch0Keys P ℓ rk0 0).sendPart k b) :=
    fun ck0 => (initState_patchGameState P ℓ rk0 ck0 k b).1
  have hinv : GameInv P (KeyPair.generate P.C k.2.1).publicKey
      (SM.initState (libsignalSessionSchemeFromEpoch0Keys P ℓ rk0 0).sendPart k b) :=
    (initState_patchGameState P ℓ rk0 0 k b).2
  refine le_trans (le_of_eq ?_)
    (evalDist_d0Exp_le P ℓ onImage qep (KeyPair.generate P.C k.2.1).publicKey hrt
      (fun c msg h1 h2 => ratchetKeyAdmissible_length_lt_of_tryFrom P.codec decT encT c msg h1 h2)
      (fun _ => by rintro ⟨⟩) (fun _ => rfl) A hq
      (SM.initState (libsignalSessionSchemeFromEpoch0Keys P ℓ rk0 0).sendPart k b) hinv
      (fun r hr => by simp [SM.initState] at hr))
  refine congrArg (fun m : ProbComp Bool => 𝒟[m] {true})
    (congrArg (Bind.bind ($ᵗ BitVec 256)) (funext fun ck0 => ?_))
  rw [himpl ck0, hinit ck0]
  rfl

/-- Bounds the probability of `eps0Event` in `libsignalSessionScheme` by `LibsignalSim.epoch0Term`. -/
theorem eps0Event_le_eps0 (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (hrt : RoundTrip.RtHyp P ℓ)
    (lam : Pt) (qep q : ℕ) (A : LibAdv PQ PQC ℓ) (hq : SM.MakesAtMostQueries A q) :
    𝒟[eps0Event P ℓ encPt lam (ratchetKeyAdmissible P.codec decT encT) qep A] {true} ≤
      LibsignalSim.epoch0Term P ℓ encPt lam (ratchetKeyAdmissible P.codec decT encT) qep q A := by
  refine (eps0Event_le_prgAdv_add_ideal P ℓ encPt lam (ratchetKeyAdmissible P.codec decT encT) qep A).trans ?_
  unfold LibsignalSim.epoch0Term
  gcongr
  exact eps0_ideal_le P ℓ Dh encPt encT decT hX hdec hinj hdum hrt qep q A hq

end CryptoGames.LibsignalSM.Proofs.Refinement
