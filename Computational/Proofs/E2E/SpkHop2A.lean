/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.SpkLeakRedModel
public import Computational.Proofs.E2E.Relabel.GameEq
public import Computational.Proofs.CryptoGames.Ratchet.LibsignalWireRoundTrip
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.Epoch0Events
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.GhostStep
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.RecvCoins
import Computational.Proofs.SignalWireRoundTrip

/-!
# Proof Obligations for `spkLeakRed` in Hops 1 and 3

**Checked by Lean.**

Proves pure-PRF simulation of `initAOracle` and `receiveB0`, wire-header agreement with
`ratchetKeyAdmissible`, and preservation of the state invariant `SpkStateInv` for `spkLeakRed`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.SM CryptoGames.Ratchet CryptoGames.Ratchet.LibsignalInst
  CryptoGames.LibsignalSession CryptoGames.CKA CryptoGames.MACScheme CryptoGames.HKDF
  CryptoGames.HMAC CBC CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.E2E.Relabel CryptoVerification.E2E.Relabel.GameEq

namespace SpkHop2

open CryptoGames.LibsignalSM.Proofs
open CryptoVerification.E2E.Relabel


set_option linter.unusedSectionVars false

variable {Pt : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt]
variable {PQC : Type} [SampleableType PQC] {ℓ : ℕ}

/-! ## Pure PRF simulation -/

/-- Stateless query implementation for the real (`b = false`) branch of `extractPRF F encPt`. -/
def purePrfImpl (F : ShaCompress) (encPt : Pt → Bytes) (rk0 : BitVec 256) :
    QueryImpl (unifSpec + prfSpec Pt (BitVec 256)) ProbComp
  | .inl u => QueryImpl.ofLift unifSpec ProbComp u
  | .inr T => pure ((extractPRF F encPt).tag rk0 T)

omit [Zero Pt] [SampleableType Pt] in
theorem simulateQ_prf_false_run {α : Type} (F : ShaCompress) (encPt : Pt → Bytes)
    (rk0 : BitVec 256) (oa : OracleComp (unifSpec + prfSpec Pt (BitVec 256)) α) :
    (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (PRFState (BitVec 256) Pt (BitVec 256)) ProbComp) +
        prfEval (extractPRF F encPt)) oa).run { key := rk0, b := false } =
      (simulateQ (purePrfImpl F encPt rk0) oa >>=
        fun a => pure (a, { key := rk0, b := false })) := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    rcases t with u | T
    · change ((liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _) >>=
          fun x => (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
            (StateT (PRFState (BitVec 256) Pt (BitVec 256)) ProbComp) +
            prfEval (extractPRF F encPt)) (k x)).run { key := rk0, b := false }) =
        ((liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _) >>=
          fun x => simulateQ (purePrfImpl F encPt rk0) (k x) >>=
            fun a => pure (a, { key := rk0, b := false }))
      congr 1
      funext x
      exact ih x
    · exact ih ((extractPRF F encPt).tag rk0 T)

omit [Zero Pt] [SampleableType Pt] in
theorem simulateQ_prf_false_run' {α : Type} (F : ShaCompress) (encPt : Pt → Bytes)
    (rk0 : BitVec 256) (oa : OracleComp (unifSpec + prfSpec Pt (BitVec 256)) α) :
    (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (PRFState (BitVec 256) Pt (BitVec 256)) ProbComp) +
        prfEval (extractPRF F encPt)) oa).run' { key := rk0, b := false } =
      simulateQ (purePrfImpl F encPt rk0) oa := by
  rw [StateT.run'_eq, simulateQ_prf_false_run F encPt rk0 oa, map_eq_bind_pure_comp]
  simp

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
@[simp] theorem simulateQ_purePrfImpl_liftM {α : Type} (F : ShaCompress) (encPt : Pt → Bytes)
    (rk0 : BitVec 256) (oa : ProbComp α) :
    simulateQ (purePrfImpl F encPt rk0)
      (liftM oa : OracleComp (unifSpec + prfSpec Pt (BitVec 256)) α) = oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    change (liftM (OracleSpec.query (spec := unifSpec) t) : ProbComp _) >>=
        (fun u => simulateQ (purePrfImpl F encPt rk0) (liftM (k u))) = _
    congr 1
    funext u
    exact ih u

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
@[simp] theorem simulateQ_purePrfImpl_liftSpkGameM {α : Type}
    (F : ShaCompress) (encPt : Pt → Bytes) (rk0 : BitVec 256)
    (m : StateT (SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) ProbComp α)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) :
    simulateQ (purePrfImpl F encPt rk0) ((liftSpkGameM (Pt := Pt) (ℓ := ℓ) m).run st) = m.run st :=
  simulateQ_purePrfImpl_liftM F encPt rk0 (m.run st)

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
@[simp] theorem simulateQ_purePrfImpl_evalQuery (F : ShaCompress) (encPt : Pt → Bytes)
    (rk0 : BitVec 256) (T : Pt) :
    simulateQ (purePrfImpl F encPt rk0) (evalQuery (Input := Pt) (Tag := BitVec 256) T) =
      pure ((extractPRF F encPt).tag rk0 T) := by
  unfold evalQuery
  rw [GameEq.simulateQ_oracleSpec_query]
  rfl

theorem simulateQ_run_stateT {ι₁ ι₂ : Type}
    {ospec₁ : OracleSpec.{0, 0} ι₁} {ospec₂ : OracleSpec.{0, 0} ι₂} {S α : Type}
    (impl : QueryImpl ospec₂ ProbComp)
    (oimpl : QueryImpl ospec₁ (StateT S (OracleComp ospec₂)))
    (oa : OracleComp ospec₁ α) (s : S) :
    simulateQ impl ((simulateQ oimpl oa).run s) =
      (simulateQ (fun t => StateT.mk fun st => simulateQ impl ((oimpl t).run st)) oa).run s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => rfl
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind]
    congr 1
    funext z
    exact ih z.1 z.2

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem expand_extract_eq_rootPRNG (F : ShaCompress) (encPt : Pt → Bytes)
    (rk : BitVec 256) (T : Pt) :
    (expandPRG F).gen ((extractPRF F encPt).tag rk T) = (rootPRNG F encPt).up rk T := by
  unfold expandPRG extractPRF rootPRNG rootKdf rootExpand hkdf hkdfExtract
  dsimp only
  rw [Refinement.keyToBytes32_bytesToKey32 _ (Refinement.length_hmacWith F _ _)]

/-- Under `purePrfImpl`, `initAOracle` evaluates to `P.initA ⟨rk0, ck0, s, alice, pqr⟩`. -/
theorem simulateQ_purePrfImpl_initAOracle (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (rk0 ck0 s alice pqr : BitVec 256) :
    simulateQ (purePrfImpl P.C.F encPt rk0) (initAOracle P Dh ck0 s alice pqr) =
      pure (P.initA ⟨rk0, ck0, s, alice, pqr⟩) := by
  have hM := Refinement.libX25519Rel_model hX
  have hspk : (KeyPair.generate P.C s).publicKey = encT (Dh.dh s Dh.base) :=
    Refinement.keyPair_generate_publicKey hX s
  have hT0 : Dh.dh s Dh.base ≠ 0 := hM.dh_ne_zero s Dh.base hM.base_ne_zero
  have hpub : (encT (Dh.dh s Dh.base)).bytes.toList = encPt (Dh.dh s Dh.base) :=
    Refinement.encT_bytes_toList hX (Dh.dh s Dh.base)
  have hrc := Refinement.rootCreateChain_generate_honest P.C hM rk0 alice hT0 hpub
  unfold initAOracle Params.initA initializeInitiatorSession
  simp only [simulateQ_bind, simulateQ_purePrfImpl_evalQuery, simulateQ_pure, pure_bind,
    expand_extract_eq_rootPRNG, hDh s alice]
  rw [hspk, hrc]
  rfl

/-! ## Wire admissibility -/

theorem parse_tryFrom_senderRatchetKey_eq
    (codec : SignalMessageProtoCodec) (w : Bytes) (msg : SignalMessage)
    (htry : SignalMessage.tryFrom codec w = .ok msg) :
    ¬ w.length < 9 ∧
      ((signalWireCodec codec).parse (w.take (w.length - 8))).map (fun p => p.1.senderRatchetKey) =
        some msg.senderRatchetKey := by
  rcases Refinement.tryFrom_parse_eq codec w msg htry with ⟨hlen, hparse⟩
  exact ⟨hlen, by rw [hparse]; rfl⟩

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem ratchetKeyOnCurve_of_tryFrom
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (c : Bytes) (msg : SignalMessage)
    (horc : ratchetKeyAdmissible protoSignalCodec decT encT c = true)
    (htry : SignalMessage.tryFrom protoSignalCodec c = .ok msg) :
    ∃ T, decT msg.senderRatchetKey = some T ∧ encT T = msg.senderRatchetKey := by
  obtain ⟨hlen, hparse⟩ := parse_tryFrom_senderRatchetKey_eq protoSignalCodec c msg htry
  unfold ratchetKeyAdmissible at horc
  simp only [hlen, ↓reduceIte] at horc
  rcases hp : (signalWireCodec protoSignalCodec).parse (c.take (c.length - 8)) with _ | ⟨hdr, ct⟩
  · simp [hp] at hparse
  · rw [hp] at hparse horc
    simp only [Option.map_some, Option.some.injEq] at hparse
    dsimp only at horc
    rw [hparse] at horc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at horc
    rcases hd : decT msg.senderRatchetKey with _ | T
    · simp [hd] at horc
    · rw [hd] at horc
      simp only [decide_eq_true_eq] at horc
      exact ⟨T, rfl, horc.2⟩

theorem Mut_exec_outgoingFromSessionState (s : SessionState Bytes) :
    ∀ o taken, Mut.exec OutgoingTripleRatchet.fromSessionState s = (.ok o, taken) →
      ∃ sc rem, s.senderChain = some sc ∧ s.remoteIdentity = some rem ∧
        o = ⟨sc.ratchetKey, sc.chainKey, s.previousCounter, s.pqRatchetState,
          BitVec.ofNat 8 s.version.toNat, s.localIdentity, rem⟩ ∧
        taken.sessionVersion = s.sessionVersion ∧
        taken.senderChain = s.senderChain := by
  unfold OutgoingTripleRatchet.fromSessionState
  rw [Refinement.Mut_exec_bind, Refinement.Mut_exec_get]
  dsimp only
  cases hsc : s.senderChain with
  | none =>
    intro o taken h
    cases h
  | some sc =>
    rw [Refinement.Mut_exec_bind, Refinement.Mut_exec_takePqRatchetState]
    dsimp only
    rw [Refinement.Mut_exec_bind, Refinement.Mut_exec_get]
    dsimp only
    split_ifs with hv
    · intro o taken h
      cases h
    · cases hrem : s.remoteIdentity with
      | none =>
        intro o taken h
        cases h
      | some rem =>
        dsimp only
        rw [Refinement.Mut_exec_pure]
        intro o taken h
        injection h with h1 h2
        injection h1 with h1'
        subst h1' h2
        exact ⟨sc, rem, rfl, rfl, rfl, rfl, hsc⟩

theorem Mut_exec_outgoingEncrypt
    (C : Crypto) (codec : SignalMessageProtoCodec) (spqr : Spqr Bytes PQC)
    (ptext : Bytes) (addrs : Option Bytes) (coins : PQC) (o : OutgoingTripleRatchet Bytes) :
    ∀ msg o', Mut.exec (OutgoingTripleRatchet.encrypt C codec spqr ptext addrs coins) o =
        (.ok msg, o') →
      ∃ newPqrState pqrKey pqrMsg,
        spqr.send o.pqrState coins = some (newPqrState, pqrKey, pqrMsg) ∧
        let messageKeys := (o.senderChainKey.messageKeys C.F).generateKeys C.F pqrKey
        let ctext := aesCbcEncrypt C.E messageKeys.cipherKey messageKeys.iv ptext
        msg = SignalMessage.new C.F codec o.sessionVersion messageKeys.macKey addrs
          o.senderRatchetKey.publicKey o.senderChainKey.index o.previousCounter ctext
          o.localIdentityKey o.remoteIdentityKey pqrMsg := by
  unfold OutgoingTripleRatchet.encrypt
  simp only [Refinement.Mut_exec_bind, Refinement.Mut_exec_get]
  cases hpan : spqr.sendPanics o.pqrState coins
  case true =>
    intro msg o' h
    simp only [↓reduceIte, Refinement.Mut_exec_bind, Refinement.Mut_exec_throw] at h
    cases h
  simp only [Bool.false_eq_true, ↓reduceIte]
  cases hspqr : spqr.send o.pqrState coins with
  | none =>
    intro msg o' h
    cases h
  | some val =>
    rcases val with ⟨newPqrState, pqrKey, pqrMsg⟩
    simp only [Refinement.Mut_exec_bind, Refinement.Mut_exec_liftE]
    cases (o.senderChainKey.nextChainKey C.F) with
    | error _ =>
      intro msg o' h
      cases h
    | ok next =>
      simp only [Refinement.Mut_exec_pure, Refinement.Mut_exec_set]
      intro msg o' h
      injection h with h1 _
      injection h1 with h1'
      subst h1'
      exact ⟨newPqrState, pqrKey, pqrMsg, rfl, rfl⟩

theorem version_of_sessionVersion_current {s : SessionState Bytes}
    (hv : s.sessionVersion = BitVec.ofNat 32 currentVersion.toNat) :
    BitVec.ofNat 8 s.version.toNat = currentVersion := by
  unfold SessionState.version
  rw [hv]
  decide

theorem ratchetKeyOnCurve_send
    (P : Params Bytes PQC) (hcodec : P.codec = protoSignalCodec) (hL : LengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (g : GhostState Bytes)
    (hver : g.session.sessionVersion = BitVec.ofNat 32 currentVersion.toNat)
    (hsc : ∀ sc ∈ g.session.senderChain, ∃ x, sc.ratchetKey = KeyPair.generate P.C x)
    (m : CBC.Plain ℓ) (r : PQC) :
    ratchetKeyAdmissible protoSignalCodec decT encT ((sessionSchemeU P ℓ).send g m r).2 = true := by
  have hrt : RoundTrip.RtHyp P ℓ := ⟨hcodec ▸ signalRoundTripShort_proto, hL, hcodec ▸ signalEncodeFits32_proto⟩
  unfold sessionSchemeU Params.send SessionState.messageEncrypt
  dsimp only
  rcases hfrom : Mut.exec OutgoingTripleRatchet.fromSessionState g.session with ⟨r_from, taken⟩
  cases r_from with
  | error _ => rfl
  | ok session =>
    dsimp only
    rcases henc : Mut.exec (OutgoingTripleRatchet.encrypt P.C P.codec P.spqr m.toList
      (g.session.encryptAddresses (P.sendAddrs g.party)) r) session with ⟨r_enc, session'⟩
    cases r_enc with
    | error _ => rfl
    | ok msg =>
      dsimp only
      obtain ⟨sc, rem, hsc_some, _, rfl, _, _⟩ :=
        Mut_exec_outgoingFromSessionState g.session session taken hfrom
      obtain ⟨newPqr, pqrKey, pqrMsg, hspqr, hmsg⟩ :=
        Mut_exec_outgoingEncrypt P.C P.codec P.spqr m.toList
          (g.session.encryptAddresses (P.sendAddrs g.party)) r _ msg session' henc
      obtain ⟨x, hx⟩ := hsc sc (by simp [hsc_some])
      have hv : BitVec.ofNat 8 g.session.version.toNat = currentVersion :=
        version_of_sessionVersion_current hver
      dsimp only at hmsg
      rw [hv, hx] at hmsg
      subst hmsg
      set messageKeys := (sc.chainKey.messageKeys P.C.F).generateKeys P.C.F pqrKey
      set ctext := aesCbcEncrypt P.C.E messageKeys.cipherKey messageKeys.iv m.toList
      set addrs := g.session.encryptAddresses (P.sendAddrs g.party)
      set hdr : SignalHeader := ⟨currentVersion, (KeyPair.generate P.C x).publicKey,
        sc.chainKey.index, g.session.previousCounter, pqrMsg, addrs⟩
      set ser := (signalWireCodec P.codec).encode hdr ctext
      set mac := computeMac P.C.F g.session.localIdentity rem messageKeys.macKey ser
      have hser_eq : (SignalMessage.new P.C.F P.codec currentVersion messageKeys.macKey addrs
          (KeyPair.generate P.C x).publicKey sc.chainKey.index g.session.previousCounter ctext
          g.session.localIdentity rem pqrMsg).serialized = ser ++ mac := rfl
      have hmac_len : mac.length = 8 := Refinement.length_computeMac _ _ _ _ _
      have htake : (ser ++ mac).take ((ser ++ mac).length - 8) = ser := by
        rw [List.length_append, hmac_len, Nat.add_sub_cancel,
          List.take_append_of_le_length (Nat.le_refl _), List.take_length]
      have hparse : (signalWireCodec protoSignalCodec).parse ser = some (hdr, ctext) := by
        rw [← hcodec]
        exact RoundTrip.RtHyp.parse hrt hdr ctext rfl (Or.inr ⟨_, _, _, _, hspqr⟩)
          (RoundTrip.sentAddrs_send P g.session.pendingPreKey g.party)
          (by rw [RoundTrip.length_aesCbcEncrypt, m.toList_length])
      have hpk : hdr.senderRatchetKey = encT (Dh.dh x Dh.base) :=
        Refinement.keyPair_generate_publicKey hX x
      have hfit32 : (ser ++ mac).length < 2 ^ 32 := by
        rw [List.length_append, hmac_len]
        have hser_p : ser = (signalWireCodec protoSignalCodec).encode hdr ctext := by
          rw [← hcodec]
        rw [hser_p]
        refine signalEncodeFits32_proto hdr ctext (hL.2.1 _ _ _ _ _ hspqr)
          (fun a ha => RoundTrip.LengthsOk.addrs_lt29 hL
            (RoundTrip.sentAddrs_send P g.session.pendingPreKey g.party) a ha) ?_
        rw [RoundTrip.length_aesCbcEncrypt, m.toList_length]
        exact RoundTrip.LengthsOk.body_lt32 hL
      rw [hser_eq]
      unfold ratchetKeyAdmissible
      split_ifs with hlen
      · rfl
      · rw [htake, hparse]
        dsimp only
        rw [hpk, hdec (Dh.dh x Dh.base)]
        simpa using hfit32

/-! ## `receiveB0` simulation and `SpkStateInv` -/

theorem ensureReceiverChain_preStep_cc1_err (C : Crypto) (their : PublicKey) (rc : BitVec 256)
    (rk0 ck0 : BitVec 256) (kp : KeyPair) (e : SignalProtocolError)
    (hcc1 : rootCreateChain C rk0 their kp.privateKey = .error e) :
    (Mut.exec (RatchetState.ensureReceiverChain C their rc)
      ⟨rk0, some ⟨kp, ⟨ck0, 0⟩⟩, [], 0, maxForwardJumps⟩).1 = .error e := by
  unfold RatchetState.ensureReceiverChain RatchetState.findReceiverChainKey
    RatchetState.findReceiverChainIndex RatchetState.dhRatchetStep
  simp only [List.findIdx?_nil, Refinement.Mut_exec_bind, Refinement.Mut_exec_get,
    Refinement.Mut_exec_liftE, Refinement.Mut_exec_takeRootKey, hcc1]

theorem ensureReceiverChain_preStep_err (C : Crypto) (their : PublicKey) (rc : BitVec 256)
    (rk0 ck0 : BitVec 256) (kp : KeyPair) (rk1 ck1 : BitVec 256) (e : SignalProtocolError)
    (hcc1 : rootCreateChain C rk0 their kp.privateKey = .ok (rk1, ⟨ck1, 0⟩))
    (hcc2 : rootCreateChain C rk1 their (KeyPair.generate C rc).privateKey = .error e) :
    (Mut.exec (RatchetState.ensureReceiverChain C their rc)
      ⟨rk0, some ⟨kp, ⟨ck0, 0⟩⟩, [], 0, maxForwardJumps⟩).1 = .error e := by
  unfold RatchetState.ensureReceiverChain RatchetState.findReceiverChainKey
    RatchetState.findReceiverChainIndex RatchetState.dhRatchetStep
  simp only [List.findIdx?_nil, Refinement.Mut_exec_bind, Refinement.Mut_exec_get,
    Refinement.Mut_exec_liftE, Refinement.Mut_exec_takeRootKey, hcc1, hcc2]

theorem ensureReceiverChain_preStep_eq (C : Crypto) (their : PublicKey) (rc : BitVec 256)
    (rk0 ck0 : BitVec 256) (kp : KeyPair) (rk1 ck1 rk2 : BitVec 256)
    (ck2 : LibsignalSession.ChainKey)
    (hcc1 : rootCreateChain C rk0 their kp.privateKey = .ok (rk1, ⟨ck1, 0⟩))
    (hcc2 : rootCreateChain C rk1 their (KeyPair.generate C rc).privateKey = .ok (rk2, ck2)) :
    Mut.exec (RatchetState.ensureReceiverChain C their rc)
      ⟨rk2, some ⟨KeyPair.generate C rc, ck2⟩, [⟨their, some ⟨ck1, 0⟩, []⟩], 0, maxForwardJumps⟩ =
    Mut.exec (RatchetState.ensureReceiverChain C their rc)
      ⟨rk0, some ⟨kp, ⟨ck0, 0⟩⟩, [], 0, maxForwardJumps⟩ := by
  unfold RatchetState.ensureReceiverChain RatchetState.findReceiverChainKey
    RatchetState.findReceiverChainIndex RatchetState.dhRatchetStep
  simp only [List.findIdx?_cons, beq_self_eq_true, List.findIdx?_nil,
    Refinement.Mut_exec_bind, Refinement.Mut_exec_get, Refinement.Mut_exec_liftE,
    Refinement.Mut_exec_pure, Refinement.Mut_exec_takeRootKey, Refinement.Mut_exec_modify,
    hcc1, hcc2, ↓reduceIte]
  rfl

theorem decrypt_preStep_cc1_err (P : Params Bytes PQC)
    (expected : Option Bytes) (msg : SignalMessage) (rc : BitVec 256)
    (rk0 ck0 : BitVec 256) (kp : KeyPair) (pqr : Bytes) (localId remoteId : IdentityKey)
    (e : SignalProtocolError)
    (hcc1 : rootCreateChain P.C rk0 msg.senderRatchetKey kp.privateKey = .error e) :
    (Mut.exec (TripleRatchet.decrypt P.C P.spqr expected msg .whisper rc)
      ⟨⟨rk0, some ⟨kp, ⟨ck0, 0⟩⟩, [], 0, maxForwardJumps⟩, pqr, localId, remoteId⟩).1 =
      .error e := by
  unfold TripleRatchet.decrypt
  rw [Refinement.Mut_exec_bind, Refinement.Mut_exec_onRatchet]
  dsimp only
  rcases hens : Mut.exec (RatchetState.ensureReceiverChain P.C msg.senderRatchetKey rc)
    ⟨rk0, some ⟨kp, ⟨ck0, 0⟩⟩, [], 0, maxForwardJumps⟩ with ⟨r_ens, s_ens⟩
  have herr : r_ens = .error e := by
    have h1 := ensureReceiverChain_preStep_cc1_err P.C msg.senderRatchetKey rc rk0 ck0 kp e hcc1
    rw [hens] at h1
    exact h1
  subst herr
  rfl

theorem decrypt_preStep_err (P : Params Bytes PQC)
    (expected : Option Bytes) (msg : SignalMessage) (rc : BitVec 256)
    (rk0 ck0 : BitVec 256) (kp : KeyPair) (pqr : Bytes) (localId remoteId : IdentityKey)
    (rk1 ck1 : BitVec 256) (e : SignalProtocolError)
    (hcc1 : rootCreateChain P.C rk0 msg.senderRatchetKey kp.privateKey = .ok (rk1, ⟨ck1, 0⟩))
    (hcc2 : rootCreateChain P.C rk1 msg.senderRatchetKey
      (KeyPair.generate P.C rc).privateKey = .error e) :
    (Mut.exec (TripleRatchet.decrypt P.C P.spqr expected msg .whisper rc)
      ⟨⟨rk0, some ⟨kp, ⟨ck0, 0⟩⟩, [], 0, maxForwardJumps⟩, pqr, localId, remoteId⟩).1 =
      .error e := by
  unfold TripleRatchet.decrypt
  rw [Refinement.Mut_exec_bind, Refinement.Mut_exec_onRatchet]
  dsimp only
  rcases hens : Mut.exec (RatchetState.ensureReceiverChain P.C msg.senderRatchetKey rc)
    ⟨rk0, some ⟨kp, ⟨ck0, 0⟩⟩, [], 0, maxForwardJumps⟩ with ⟨r_ens, s_ens⟩
  have herr : r_ens = .error e := by
    have h1 := ensureReceiverChain_preStep_err P.C msg.senderRatchetKey rc rk0 ck0 kp rk1 ck1 e
      hcc1 hcc2
    rw [hens] at h1
    exact h1
  subst herr
  rfl

theorem decrypt_preStep_eq (P : Params Bytes PQC)
    (expected : Option Bytes) (msg : SignalMessage) (rc : BitVec 256)
    (rk0 ck0 : BitVec 256) (kp : KeyPair) (pqr : Bytes) (localId remoteId : IdentityKey)
    (rk1 ck1 rk2 : BitVec 256) (ck2 : LibsignalSession.ChainKey)
    (hcc1 : rootCreateChain P.C rk0 msg.senderRatchetKey kp.privateKey = .ok (rk1, ⟨ck1, 0⟩))
    (hcc2 : rootCreateChain P.C rk1 msg.senderRatchetKey
      (KeyPair.generate P.C rc).privateKey = .ok (rk2, ck2)) :
    Mut.exec (TripleRatchet.decrypt P.C P.spqr expected msg .whisper rc)
      ⟨⟨rk2, some ⟨KeyPair.generate P.C rc, ck2⟩,
        [⟨msg.senderRatchetKey, some ⟨ck1, 0⟩, []⟩], 0, maxForwardJumps⟩,
        pqr, localId, remoteId⟩ =
    Mut.exec (TripleRatchet.decrypt P.C P.spqr expected msg .whisper rc)
      ⟨⟨rk0, some ⟨kp, ⟨ck0, 0⟩⟩, [], 0, maxForwardJumps⟩, pqr, localId, remoteId⟩ := by
  unfold TripleRatchet.decrypt
  rw [Refinement.Mut_exec_bind, Refinement.Mut_exec_bind,
    Refinement.Mut_exec_onRatchet, Refinement.Mut_exec_onRatchet]
  dsimp only
  rw [ensureReceiverChain_preStep_eq P.C msg.senderRatchetKey rc rk0 ck0 kp rk1 ck1 rk2 ck2
    hcc1 hcc2]

theorem tryDecryptFromRecord_preStep_cc1_err (P : Params Bytes PQC)
    (expected : Option Bytes) (msg : SignalMessage) (rc : BitVec 256)
    (rk0 ck0 s alice pqr : BitVec 256) (e : SignalProtocolError)
    (hcc1 : rootCreateChain P.C rk0 msg.senderRatchetKey
      (KeyPair.generate P.C s).privateKey = .error e) :
    ∃ e', (SessionState.tryDecryptFromRecord P.C P.spqr expected msg .whisper rc
      (P.initB ⟨rk0, ck0, s, alice, pqr⟩).session).1 = .error e' := by
  unfold SessionState.tryDecryptFromRecord
  split_ifs with hver
  · exact ⟨_, rfl⟩
  · unfold SessionState.tryDecryptWithState
    rw [Refinement.Mut_exec_bind, Refinement.Mut_exec_fromSessionState]
    dsimp only [Params.initB, initializeRecipientSession, SessionState.setSenderChain,
      SessionState.new]
    have hdec := decrypt_preStep_cc1_err P expected msg rc rk0 ck0 (KeyPair.generate P.C s)
      (P.spqr.init .b2a pqr) P.idB P.idA e hcc1
    rcases htr : Mut.exec (TripleRatchet.decrypt P.C P.spqr expected msg .whisper rc)
      ⟨⟨rk0, some ⟨KeyPair.generate P.C s, ⟨ck0, 0⟩⟩, [], 0, maxForwardJumps⟩,
        P.spqr.init .b2a pqr, P.idB, P.idA⟩ with ⟨r_dec, t_dec⟩
    rw [htr] at hdec
    dsimp only at hdec
    subst hdec
    simp [Refinement.Mut_exec_bind, Refinement.Mut_exec_liftE]

theorem tryDecryptFromRecord_preStep_err (P : Params Bytes PQC)
    (expected : Option Bytes) (msg : SignalMessage) (rc : BitVec 256)
    (rk0 ck0 s alice pqr rk1 ck1 : BitVec 256) (e : SignalProtocolError)
    (hcc1 : rootCreateChain P.C rk0 msg.senderRatchetKey
      (KeyPair.generate P.C s).privateKey = .ok (rk1, ⟨ck1, 0⟩))
    (hcc2 : rootCreateChain P.C rk1 msg.senderRatchetKey
      (KeyPair.generate P.C rc).privateKey = .error e) :
    ∃ e', (SessionState.tryDecryptFromRecord P.C P.spqr expected msg .whisper rc
      (P.initB ⟨rk0, ck0, s, alice, pqr⟩).session).1 = .error e' := by
  unfold SessionState.tryDecryptFromRecord
  split_ifs with hver
  · exact ⟨_, rfl⟩
  · unfold SessionState.tryDecryptWithState
    rw [Refinement.Mut_exec_bind, Refinement.Mut_exec_fromSessionState]
    dsimp only [Params.initB, initializeRecipientSession, SessionState.setSenderChain,
      SessionState.new]
    have hdec := decrypt_preStep_err P expected msg rc rk0 ck0 (KeyPair.generate P.C s)
      (P.spqr.init .b2a pqr) P.idB P.idA rk1 ck1 e hcc1 hcc2
    rcases htr : Mut.exec (TripleRatchet.decrypt P.C P.spqr expected msg .whisper rc)
      ⟨⟨rk0, some ⟨KeyPair.generate P.C s, ⟨ck0, 0⟩⟩, [], 0, maxForwardJumps⟩,
        P.spqr.init .b2a pqr, P.idB, P.idA⟩ with ⟨r_dec, t_dec⟩
    rw [htr] at hdec
    dsimp only at hdec
    subst hdec
    simp [Refinement.Mut_exec_bind, Refinement.Mut_exec_liftE]

theorem tryDecryptFromRecord_preStep_ok (P : Params Bytes PQC)
    (expected : Option Bytes) (msg : SignalMessage) (rc : BitVec 256)
    (rk0 ck0 s alice pqr rk1 ck1 rk2 : BitVec 256) (ck2 : LibsignalSession.ChainKey)
    (hcc1 : rootCreateChain P.C rk0 msg.senderRatchetKey
      (KeyPair.generate P.C s).privateKey = .ok (rk1, ⟨ck1, 0⟩))
    (hcc2 : rootCreateChain P.C rk1 msg.senderRatchetKey
      (KeyPair.generate P.C rc).privateKey = .ok (rk2, ck2)) :
    let g0 := P.initB ⟨0, ck0, s, alice, pqr⟩
    let g1 := P.initB ⟨rk0, ck0, s, alice, pqr⟩
    let sess' : SessionState Bytes :=
      { g0.session with
        previousCounter := 0
        rootKey := rk2
        receiverChains := [⟨msg.senderRatchetKey, some ⟨ck1, 0⟩, []⟩]
        senderChain := some ⟨KeyPair.generate P.C rc, ck2⟩ }
    SessionState.tryDecryptFromRecord P.C P.spqr expected msg .whisper rc sess' =
      match SessionState.tryDecryptFromRecord P.C P.spqr expected msg .whisper rc g1.session with
      | (.ok m, s_out) => (.ok m, s_out)
      | (.error err, _) => (.error err, sess') := by
  dsimp only
  unfold SessionState.tryDecryptFromRecord
  change (if (P.initB ⟨rk0, ck0, s, alice, pqr⟩).session.version.toNat ≠ msg.messageVersion.toNat
      then _ else _) = _
  split_ifs with hver
  · rfl
  · unfold SessionState.tryDecryptWithState
    simp only [Refinement.Mut_exec_bind, Refinement.Mut_exec_fromSessionState]
    dsimp only [Params.initB, initializeRecipientSession, SessionState.setSenderChain,
      SessionState.new]
    rw [decrypt_preStep_eq P expected msg rc rk0 ck0 (KeyPair.generate P.C s)
      (P.spqr.init .b2a pqr) P.idB P.idA rk1 ck1 rk2 ck2 hcc1 hcc2]
    rcases Mut.exec (TripleRatchet.decrypt P.C P.spqr expected msg .whisper rc)
      ⟨⟨rk0, some ⟨KeyPair.generate P.C s, ⟨ck0, 0⟩⟩, [], 0, maxForwardJumps⟩,
        P.spqr.init .b2a pqr, P.idB, P.idA⟩ with ⟨r_dec, t_dec⟩
    cases r_dec with
    | error err =>
      simp [Refinement.Mut_exec_liftE]
    | ok ptext =>
      simp only [Refinement.Mut_exec_liftE,
        Refinement.Mut_exec_modify, Refinement.Mut_exec_pure]
      rfl

/-- Under `purePrfImpl`, `receiveB0` on `P.initB ⟨0, ck0, s, alice, pqr⟩` agrees with `(sessionSchemeU P ℓ).receive` at root key `rk0` on admissible ciphertexts. -/
theorem receiveB0_purePrfImpl_eq (P : Params Bytes PQC) (hcodec : P.codec = protoSignalCodec)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hz : ∀ x, Dh.dh x 0 = 0)
    (rk0 ck0 s alice pqr : BitVec 256) (c : Bytes)
    (horc : ratchetKeyAdmissible protoSignalCodec decT encT c = true) (rc : BitVec 256) :
    simulateQ (purePrfImpl P.C.F encPt rk0)
      (receiveB0 P ℓ Dh encT decT s (P.initB ⟨0, ck0, s, alice, pqr⟩) c rc) =
      pure ((sessionSchemeU P ℓ).receive (P.initB ⟨rk0, ck0, s, alice, pqr⟩) c rc) := by
  have hM := Refinement.libX25519Rel_model hX
  have hparty : (P.initB ⟨rk0, ck0, s, alice, pqr⟩).party = .B := rfl
  unfold receiveB0 sessionSchemeU Params.receive
  dsimp only
  rw [hparty]
  cases htry : SignalMessage.tryFrom P.codec c with
  | error _ => rfl
  | ok msg =>
    dsimp only
    obtain ⟨T, hdecT, hencT⟩ :=
      ratchetKeyOnCurve_of_tryFrom decT encT c msg horc (hcodec ▸ htry)
    have hpub : msg.senderRatchetKey.bytes.toList = encPt T := by
      rw [← hencT]
      exact Refinement.encT_bytes_toList hX T
    by_cases hT0 : T = 0
    · subst hT0
      simp only [hdecT]
      have hcc1 : rootCreateChain P.C rk0 msg.senderRatchetKey
          (KeyPair.generate P.C s).privateKey = .error .invalidKeyAgreement :=
        Refinement.rootCreateChain_generate_zero P.C hM hz rk0 s hpub
      obtain ⟨e', herr⟩ := tryDecryptFromRecord_preStep_cc1_err P (P.expectedAddrs .B) msg rc
        rk0 ck0 s alice pqr .invalidKeyAgreement hcc1
      rcases htr : SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs .B) msg .whisper rc
        (P.initB ⟨rk0, ck0, s, alice, pqr⟩).session with ⟨r_tr, s_tr⟩
      rw [htr] at herr
      dsimp only at herr
      subst herr
      rfl
    · have hnot : ¬ (T = 0 ∨ encT T ≠ msg.senderRatchetKey) := by
        rintro (rfl | hne)
        · exact hT0 rfl
        · exact hne hencT
      have hcc1 : rootCreateChain P.C rk0 msg.senderRatchetKey
          (KeyPair.generate P.C s).privateKey =
          .ok (((rootPRNG P.C.F encPt).up rk0 (Dh.dh s T)).1,
            ⟨((rootPRNG P.C.F encPt).up rk0 (Dh.dh s T)).2, 0⟩) :=
        Refinement.rootCreateChain_generate_honest P.C hM rk0 s hT0 hpub
      simp only [hdecT, hnot, ↓reduceIte, simulateQ_bind, simulateQ_purePrfImpl_evalQuery,
        pure_bind, expand_extract_eq_rootPRNG]
      set rk1 := ((rootPRNG P.C.F encPt).up rk0 (Dh.dh s T)).1
      set ck1 := ((rootPRNG P.C.F encPt).up rk0 (Dh.dh s T)).2
      cases hcc2 :
          rootCreateChain P.C rk1 msg.senderRatchetKey (KeyPair.generate P.C rc).privateKey with
      | error err =>
        dsimp only
        rw [simulateQ_pure]
        obtain ⟨e', herr⟩ := tryDecryptFromRecord_preStep_err P (P.expectedAddrs .B) msg rc
          rk0 ck0 s alice pqr rk1 ck1 err hcc1 hcc2
        rcases htr :
            SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs .B) msg .whisper rc
          (P.initB ⟨rk0, ck0, s, alice, pqr⟩).session with ⟨r_tr, s_tr⟩
        rw [htr] at herr
        dsimp only at herr
        subst herr
        rfl
      | ok pair2 =>
        rcases pair2 with ⟨rk2, ck2⟩
        dsimp only
        have hok := tryDecryptFromRecord_preStep_ok P (P.expectedAddrs .B) msg rc
          rk0 ck0 s alice pqr rk1 ck1 rk2 ck2 hcc1 hcc2
        dsimp only at hok
        rw [hok]
        rcases htr :
            SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs .B) msg .whisper rc
          (P.initB ⟨rk0, ck0, s, alice, pqr⟩).session with ⟨r_tr, s_out⟩
        cases r_tr <;> { dsimp only; rw [simulateQ_pure]; rfl }

/-- Sender-side session invariant: current session version and generated sender ratchet key. -/
def SessionSenderInv (P : Params Bytes PQC) (s : SessionState Bytes) : Prop :=
  s.sessionVersion = BitVec.ofNat 32 currentVersion.toNat ∧
  ∀ sc ∈ s.senderChain, ∃ x, sc.ratchetKey = KeyPair.generate P.C x

theorem sessionSenderInv_initA (P : Params Bytes PQC) (k : InitKeys) :
    SessionSenderInv P (P.initA k).session := by
  unfold Params.initA initializeInitiatorSession
  dsimp only
  cases rootCreateChain P.C k.rootKey (KeyPair.generate P.C k.bobSpkCoins).publicKey
    (KeyPair.generate P.C k.aliceRatchetCoins).privateKey with
  | error _ =>
    refine ⟨rfl, ?_⟩
    intro sc hsc
    cases hsc
  | ok pair =>
    refine ⟨rfl, ?_⟩
    intro sc hsc
    cases hsc
    exact ⟨k.aliceRatchetCoins, rfl⟩

theorem sessionSenderInv_initB (P : Params Bytes PQC) (k : InitKeys) :
    SessionSenderInv P (P.initB k).session := by
  refine ⟨rfl, ?_⟩
  intro sc hsc
  simp only [Params.initB, initializeRecipientSession, SessionState.setSenderChain,
    SessionState.new, Option.mem_def, Option.some.injEq] at hsc
  subst hsc
  exact ⟨k.bobSpkCoins, rfl⟩

theorem sessionSenderInv_send (P : Params Bytes PQC) (g : GhostState Bytes)
    (m : CBC.Plain ℓ) (r : PQC) (hs : SessionSenderInv P g.session) :
    SessionSenderInv P ((sessionSchemeU P ℓ).send g m r).1.session ∧
      ((sessionSchemeU P ℓ).send g m r).1.party = g.party ∧
      (((sessionSchemeU P ℓ).send g m r).1.epoch = g.epoch ∨
        ((sessionSchemeU P ℓ).send g m r).1.epoch = g.epoch + 1) := by
  unfold sessionSchemeU Params.send SessionState.messageEncrypt
  dsimp only
  rcases hfrom : Mut.exec OutgoingTripleRatchet.fromSessionState g.session with ⟨r_from, taken⟩
  cases r_from with
  | error _ => exact ⟨hs, rfl, Or.inl rfl⟩
  | ok session =>
    dsimp only
    rcases henc : Mut.exec (OutgoingTripleRatchet.encrypt P.C P.codec P.spqr m.toList
      (g.session.encryptAddresses (P.sendAddrs g.party)) r) session with ⟨r_enc, session'⟩
    cases r_enc with
    | error _ => exact ⟨hs, rfl, Or.inl rfl⟩
    | ok msg =>
      obtain ⟨_, _, _, _, _, hver, hsc⟩ :=
        Mut_exec_outgoingFromSessionState g.session session taken hfrom
      refine ⟨⟨by simp [OutgoingTripleRatchet.applyToSessionState, hver, hs.1], ?_⟩, rfl, ?_⟩
      · intro sc' hsc'
        simp only [OutgoingTripleRatchet.applyToSessionState, hsc, Option.mem_def,
          Option.map_eq_some_iff] at hsc'
        obtain ⟨sc, hsc_mem, rfl⟩ := hsc'
        exact hs.2 sc hsc_mem
      · split_ifs
        · exact Or.inl rfl
        · exact Or.inr rfl

theorem takeSkippedKey_senderChain (their : PublicKey) (counter : BitVec 32) (r : RatchetState) :
    (Mut.exec (RatchetState.takeSkippedKey their counter) r).2.senderChain = r.senderChain := by
  unfold RatchetState.takeSkippedKey
  rw [Refinement.Mut_exec_bind, Refinement.Mut_exec_get]
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
          rw [Refinement.Mut_exec_bind, Refinement.Mut_exec_set]
          rfl

theorem storeSkippedKey_senderChain (their : PublicKey) (key : MessageKeyGenerator)
    (r : RatchetState) :
    (Mut.exec (RatchetState.storeSkippedKey their key) r).2.senderChain = r.senderChain := by
  unfold RatchetState.storeSkippedKey
  rw [Refinement.Mut_exec_bind, Refinement.Mut_exec_get]
  dsimp only []
  cases r.findReceiverChainIndex their with
  | none => rfl
  | some idx =>
    dsimp only []
    cases r.receiverChains[idx]? with
    | none => rfl
    | some c =>
      rw [Refinement.Mut_exec_set]

theorem setReceiverChainKey_senderChain (their : PublicKey) (ck : LibsignalSession.ChainKey)
    (r : RatchetState) :
    (Mut.exec (RatchetState.setReceiverChainKey their ck) r).2.senderChain = r.senderChain := by
  unfold RatchetState.setReceiverChainKey
  rw [Refinement.Mut_exec_bind, Refinement.Mut_exec_get]
  dsimp only []
  cases r.findReceiverChainIndex their with
  | none => rfl
  | some idx =>
    dsimp only []
    cases r.receiverChains[idx]? with
    | none => rfl
    | some c =>
      rw [Refinement.Mut_exec_set]

theorem advanceChain_senderChain (F : ShaCompress) (their : PublicKey) (counter : BitVec 32) :
    ∀ (fuel : ℕ) (ck : LibsignalSession.ChainKey) (r : RatchetState),
      (Mut.exec (RatchetState.advanceChain F their counter fuel ck) r).2.senderChain =
        r.senderChain
  | 0, ck, r => rfl
  | fuel + 1, ck, r => by
    unfold RatchetState.advanceChain
    by_cases hlt : ck.index < counter
    · simp only [hlt, ↓reduceIte, Refinement.Mut_exec_bind]
      have hst := storeSkippedKey_senderChain their (ck.messageKeys F) r
      rcases h_st : Mut.exec (RatchetState.storeSkippedKey their (ck.messageKeys F)) r with
        ⟨r_st, s_st⟩
      rw [h_st] at hst
      cases r_st with
      | error e => exact hst
      | ok _ =>
        dsimp only []
        cases ck.nextChainKey F with
        | error e =>
          simp only [Refinement.Mut_exec_liftE]
          exact hst
        | ok ck' =>
          simp only [Refinement.Mut_exec_liftE]
          exact (advanceChain_senderChain F their counter fuel ck' s_st).trans hst
    · simp only [hlt, ↓reduceIte, Refinement.Mut_exec_pure]

theorem consumeMessageKey_senderChain (F : ShaCompress) (their : PublicKey)
    (ck : LibsignalSession.ChainKey) (counter : BitVec 32) (msgType : MessageType)
    (r : RatchetState) :
    (Mut.exec (RatchetState.consumeMessageKey F their ck counter msgType) r).2.senderChain =
      r.senderChain := by
  unfold RatchetState.consumeMessageKey
  by_cases hlt : counter < ck.index
  · simp only [hlt, ↓reduceIte, Refinement.Mut_exec_bind]
    have htk := takeSkippedKey_senderChain their counter r
    rcases h_tk : Mut.exec (RatchetState.takeSkippedKey their counter) r with ⟨r_tk, s_tk⟩
    rw [h_tk] at htk
    cases r_tk with
    | error e => exact htk
    | ok optK =>
      cases optK <;> simp only [Refinement.Mut_exec_pure] <;> exact htk
  · simp only [hlt, ↓reduceIte, Refinement.Mut_exec_bind, Refinement.Mut_exec_get]
    by_cases hj : r.maxForwardJumps < (counter - ck.index).toNat
    · simp only [hj, ↓reduceIte, Refinement.Mut_exec_throw, Refinement.Mut_exec_bind]
    · simp only [hj, ↓reduceIte, Refinement.Mut_exec_pure, Refinement.Mut_exec_bind]
      have hadv := advanceChain_senderChain F their counter (counter - ck.index).toNat ck r
      rcases h_adv :
          Mut.exec (RatchetState.advanceChain F their counter (counter - ck.index).toNat ck) r
        with ⟨r_adv, s_adv⟩
      rw [h_adv] at hadv
      cases r_adv with
      | error e => exact hadv
      | ok ckOut =>
        dsimp only []
        cases ckOut.nextChainKey F with
        | error e =>
          simp only [Refinement.Mut_exec_liftE]
          exact hadv
        | ok ckNext =>
          simp only [Refinement.Mut_exec_liftE]
          have hset := setReceiverChainKey_senderChain their ckNext s_adv
          rcases h_set : Mut.exec (RatchetState.setReceiverChainKey their ckNext) s_adv with
            ⟨r_set, s_set⟩
          rw [h_set] at hset
          cases r_set <;> exact hset.trans hadv

theorem ensureReceiverChain_senderChain (C : Crypto) (their : PublicKey) (rc : BitVec 256)
    (ck : LibsignalSession.ChainKey) (r r' : RatchetState)
    (h : Mut.exec (RatchetState.ensureReceiverChain C their rc) r = (.ok ck, r')) :
    r'.senderChain = r.senderChain ∨
      ∃ sck, r'.senderChain = some ⟨KeyPair.generate C rc, sck⟩ := by
  unfold RatchetState.ensureReceiverChain RatchetState.dhRatchetStep at h
  simp only [Refinement.Mut_exec_bind, Refinement.Mut_exec_get, Refinement.Mut_exec_liftE] at h
  cases hfind : r.findReceiverChainKey their with
  | error _ => simp [hfind] at h
  | ok opt =>
    rw [hfind] at h
    cases opt with
    | some ck0 =>
      dsimp only at h
      injection h with _ h2
      exact Or.inl (congrArg RatchetState.senderChain h2.symm)
    | none =>
      dsimp only at h
      rw [Refinement.Mut_exec_bind, Refinement.Mut_exec_get] at h
      dsimp only at h
      cases hsc : r.senderChain with
      | none =>
        rw [hsc] at h
        cases h
      | some sc =>
        rw [hsc] at h
        dsimp only at h
        simp only [Refinement.Mut_exec_bind, Refinement.Mut_exec_takeRootKey,
          Refinement.Mut_exec_liftE, Refinement.Mut_exec_modify, Refinement.Mut_exec_pure] at h
        cases hcc1 : rootCreateChain C r.rootKey their sc.ratchetKey.privateKey with
        | error _ =>
          rw [hcc1] at h
          cases h
        | ok p1 =>
          rw [hcc1] at h
          dsimp only at h
          cases hcc2 : rootCreateChain C p1.1 their (KeyPair.generate C rc).privateKey with
          | error _ =>
            rw [hcc2] at h
            cases h
          | ok p2 =>
            rw [hcc2] at h
            dsimp only at h
            injection h with _ h2
            exact Or.inr ⟨p2.2, by rw [← h2]⟩

theorem tryDecryptFromRecord_preserve_sender (P : Params Bytes PQC)
    (expected : Option Bytes) (msg : SignalMessage) (rc : BitVec 256)
    (s s_out : SessionState Bytes) (m : Bytes)
    (hs : SessionSenderInv P s)
    (htr : SessionState.tryDecryptFromRecord P.C P.spqr expected msg .whisper rc s =
      (.ok m, s_out)) :
    SessionSenderInv P s_out := by
  rw [Refinement.tryDecryptFromRecord_eq] at htr
  split_ifs at htr with hver
  · cases htr
  · cases hrem : s.remoteIdentity with
    | none =>
      rw [hrem] at htr
      cases htr
    | some rem =>
      rw [hrem] at htr
      dsimp only at htr
      rcases hstep :
          Mut.exec (Refinement.ratchetDecryptStep P.C msg.senderRatchetKey msg.counter .whisper rc)
        ⟨s.rootKey, s.senderChain, s.receiverChains, s.previousCounter, maxForwardJumps⟩
        with ⟨r_step, s_step⟩
      rw [hstep] at htr
      cases r_step with
      | error _ => cases htr
      | ok gen =>
        dsimp only [Refinement.postRatchetDecrypt] at htr
        cases hpan : P.spqr.recvPanics s.pqRatchetState msg.pqRatchet
        case true => simp [hpan] at htr
        simp only [hpan, Bool.false_eq_true, ↓reduceIte] at htr
        cases hspqr : P.spqr.recv s.pqRatchetState msg.pqRatchet with
        | error b =>
          rw [hspqr] at htr
          cases b <;> cases htr
        | ok pqr_pair =>
          rw [hspqr] at htr
          rcases pqr_pair with ⟨newPqr, pqrKey⟩
          dsimp only at htr
          split_ifs at htr with hmac
          · cases htr
          · cases haes : aesCbcDecrypt P.C.D
              ((gen.generateKeys P.C.F pqrKey).cipherKey)
              ((gen.generateKeys P.C.F pqrKey).iv) msg.ciphertext with
            | none =>
              rw [haes] at htr
              cases htr
            | some ptext =>
              rw [haes] at htr
              injection htr with _ hs_out
              subst hs_out
              unfold Refinement.ratchetDecryptStep at hstep
              rw [Refinement.Mut_exec_bind] at hstep
              rcases hens : Mut.exec (RatchetState.ensureReceiverChain P.C msg.senderRatchetKey rc)
                ⟨s.rootKey, s.senderChain, s.receiverChains, s.previousCounter, maxForwardJumps⟩
                with ⟨r_ens, s_ens⟩
              rw [hens] at hstep
              cases r_ens with
              | error _ => cases hstep
              | ok ck =>
                dsimp only at hstep
                have hcon_sc := consumeMessageKey_senderChain P.C.F msg.senderRatchetKey ck
                  msg.counter .whisper s_ens
                rw [hstep] at hcon_sc
                dsimp only at hcon_sc
                have hens_sc := ensureReceiverChain_senderChain P.C msg.senderRatchetKey rc ck
                  ⟨s.rootKey, s.senderChain, s.receiverChains, s.previousCounter, maxForwardJumps⟩
                  s_ens hens
                refine ⟨hs.1, ?_⟩
                intro sc' hsc'
                dsimp only at hsc'
                rw [hcon_sc] at hsc'
                rcases hens_sc with h_eq | ⟨sck, h_new⟩
                · rw [h_eq] at hsc'
                  exact hs.2 sc' hsc'
                · rw [h_new, Option.mem_def, Option.some.injEq] at hsc'
                  subst hsc'
                  exact ⟨rc, rfl⟩

theorem sessionSenderInv_receive (P : Params Bytes PQC) (g : GhostState Bytes)
    (c : Bytes) (rc : BitVec 256) (x : GhostState Bytes × ℕ × ℕ × CBC.Plain ℓ)
    (hs : SessionSenderInv P g.session)
    (hrec : (sessionSchemeU P ℓ).receive g c rc = some x) :
    SessionSenderInv P x.1.session ∧ x.1.party = g.party ∧
      (x.1.epoch = g.epoch ∨ x.1.epoch = g.epoch + 1) ∧
      (g.session.receiverChains = [] → x.1.epoch = g.epoch + 1 ∧ x.2.1 = g.epoch + 1) := by
  unfold sessionSchemeU Params.receive at hrec
  simp only [Option.map_eq_some_iff] at hrec
  obtain ⟨y, hy, rfl⟩ := hrec
  cases htry : SignalMessage.tryFrom P.codec c with
  | error _ =>
    rw [htry] at hy
    cases hy
  | ok msg =>
    rw [htry] at hy
    dsimp only at hy
    rcases htr : SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg
      .whisper rc g.session with ⟨r_tr, s_out⟩
    rw [htr] at hy
    cases r_tr with
    | error _ => cases hy
    | ok m =>
      dsimp only at hy
      injection hy with hy'
      subst hy'
      refine ⟨tryDecryptFromRecord_preserve_sender P (P.expectedAddrs g.party) msg rc
        g.session s_out m hs htr, rfl, ?_, ?_⟩
      · cases g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey) with
        | some i => exact Or.inl rfl
        | none => exact Or.inr rfl
      · intro hrc
        simp [hrc]

/-- Patch Bob's root key at epoch 0 to `rk0`, leaving all other party states unchanged. -/
def patchPartySpk (rk0 : BitVec 256) (g : GhostState Bytes) : GhostState Bytes :=
  if g.party == .B && g.epoch == 0 then
    { g with session := { g.session with rootKey := rk0 } }
  else
    g

theorem patchPartySpk_of_not_B0 (rk0 : BitVec 256) (g : GhostState Bytes)
    (h : ¬ (g.party = .B ∧ g.epoch = 0)) :
    patchPartySpk rk0 g = g := by
  unfold patchPartySpk
  have hcond : (g.party == .B && g.epoch == 0) = false := by
    rw [Bool.and_eq_false_iff, beq_eq_false_iff_ne, beq_eq_false_iff_ne]
    by_cases hp : g.party = .B
    · exact Or.inr fun he => h ⟨hp, he⟩
    · exact Or.inl hp
  rw [hcond]
  rfl

@[simp] theorem patchPartySpk_party (rk0 : BitVec 256) (g : GhostState Bytes) :
    (patchPartySpk rk0 g).party = g.party := by
  unfold patchPartySpk
  split_ifs <;> rfl

@[simp] theorem patchPartySpk_epoch (rk0 : BitVec 256) (g : GhostState Bytes) :
    (patchPartySpk rk0 g).epoch = g.epoch := by
  unfold patchPartySpk
  split_ifs <;> rfl

@[simp] theorem patchPartySpk_sessionSenderInv (P : Params Bytes PQC) (rk0 : BitVec 256)
    (g : GhostState Bytes) :
    SessionSenderInv P (patchPartySpk rk0 g).session ↔ SessionSenderInv P g.session := by
  unfold patchPartySpk SessionSenderInv
  split_ifs <;> rfl

theorem patchPartySpk_initA (P : Params Bytes PQC) (rk0 ck0 s alice pqr : BitVec 256) :
    patchPartySpk rk0 (P.initA ⟨rk0, ck0, s, alice, pqr⟩) =
      P.initA ⟨rk0, ck0, s, alice, pqr⟩ := by
  apply patchPartySpk_of_not_B0
  rintro ⟨hp, _⟩
  have hA : (P.initA ⟨rk0, ck0, s, alice, pqr⟩).party = .A := by
    unfold Params.initA
    dsimp only
    split <;> rfl
  rw [hA] at hp
  cases hp

theorem patchPartySpk_initB (P : Params Bytes PQC) (rk0 ck0 s alice pqr : BitVec 256) :
    patchPartySpk rk0 (P.initB ⟨0, ck0, s, alice, pqr⟩) =
      P.initB ⟨rk0, ck0, s, alice, pqr⟩ := rfl

/-- Game-state invariant for `spkLeakRed`. -/
structure SpkStateInv (P : Params Bytes PQC)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ck0 s alice pqr : BitVec 256)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) : Prop where
  b_epoch_zero_iff : (st.st .B).epoch = 0 ↔ st.epoch .B = 0
  b_eq_initB : (st.st .B).epoch = 0 → st.st .B = P.initB ⟨0, ck0, s, alice, pqr⟩
  party_eq : ∀ Q, (st.st Q).party = Q
  sender_inv : ∀ Q, SessionSenderInv P (st.st Q).session
  trans_inv : ∀ r ∈ st.trans,
    0 < r.pos.epoch ∧ ratchetKeyAdmissible protoSignalCodec decT encT r.ct = true

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem spkStateInv_init (P : Params Bytes PQC)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (rk0 ck0 s alice pqr : BitVec 256) (b : Bool) :
    let stA := P.initA ⟨rk0, ck0, s, alice, pqr⟩
    let stB := P.initB ⟨0, ck0, s, alice, pqr⟩
    let initSt : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes :=
      { st := fun Q => match Q with | .A => stA | .B => stB, b := b }
    SpkStateInv P decT encT ck0 s alice pqr initSt := by
  refine ⟨Iff.rfl, fun _ => rfl, ?_, ?_, ?_⟩
  · intro Q
    cases Q
    · unfold Params.initA
      dsimp only
      split <;> rfl
    · rfl
  · intro Q
    cases Q
    · exact sessionSenderInv_initA P _
    · exact sessionSenderInv_initB P _
  · intro r hr
    cases hr

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem patchPartySpk_st_of_noBobEpoch0
    {P : Params Bytes PQC} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ck0 s alice pqr : BitVec 256}
    {st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes}
    (hs : SpkStateInv P decT encT ck0 s alice pqr st)
    (rk0 : BitVec 256) (Q : Party) (hok : noBobSendInEpoch0 st Q = true) :
    patchPartySpk rk0 (st.st Q) = st.st Q ∧ ¬ (Q = .B ∧ (st.st .B).epoch = 0) := by
  have hne : ¬ (Q = .B ∧ (st.st .B).epoch = 0) := by
    rintro ⟨rfl, hb0⟩
    have he0 : st.epoch .B = 0 := hs.b_epoch_zero_iff.mp hb0
    unfold noBobSendInEpoch0 at hok
    simp [he0] at hok
  refine ⟨patchPartySpk_of_not_B0 rk0 (st.st Q) ?_, hne⟩
  rintro ⟨hp, he0⟩
  rw [hs.party_eq Q] at hp
  subst hp
  exact hne ⟨rfl, he0⟩

theorem epMgmt_epoch
    {st st1 : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes}
    {qep : ℕ} {Q : Party} {bad : Bool}
    (hep : st.epMgmt 3 qep Q bad = some st1) (R : Party) :
    st1.epoch R = (if Q.sendsIn (st.epoch Q + 1) then
      Function.update st.epoch Q (st.epoch Q + 1) else st.epoch) R := by
  unfold SM.GameState.epMgmt SM.GameState.leak at hep
  split_ifs at hep <;> injection hep with hep <;> subst hep <;>
    simp only [*, ↓reduceIte, Bool.false_eq_true]

theorem epMgmt_epoch_pos_of_noBobEpoch0
    {st st1 : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes}
    {qep : ℕ} {Q : Party} {bad : Bool}
    (hok : noBobSendInEpoch0 st Q = true)
    (hep : st.epMgmt 3 qep Q bad = some st1) :
    0 < st1.epoch Q ∧ (st1.epoch .B = 0 ↔ st.epoch .B = 0) := by
  cases Q with
  | A =>
    rw [epMgmt_epoch hep .A, epMgmt_epoch hep .B]
    by_cases hsend : Party.A.sendsIn (st.epoch .A + 1) = true
    · simp only [hsend, ↓reduceIte, Function.update_self]
      rw [Function.update_of_ne (by decide)]
      exact ⟨by omega, Iff.rfl⟩
    · simp only [hsend, Bool.false_eq_true, ↓reduceIte]
      refine ⟨?_, trivial⟩
      by_cases he0 : st.epoch .A = 0
      · have hA1 : Party.A.sendsIn (0 + 1) = true := by decide
        exact absurd (he0 ▸ hsend) (by simp [hA1])
      · omega
  | B =>
    rw [epMgmt_epoch hep .B]
    have hb_ne0 : st.epoch .B ≠ 0 := by
      unfold noBobSendInEpoch0 at hok
      simp only [beq_self_eq_true, Bool.true_and, Bool.not_eq_true',
        beq_eq_false_iff_ne] at hok
      exact hok
    by_cases hsend : Party.B.sendsIn (st.epoch .B + 1) = true
    · simp only [hsend, ↓reduceIte, Function.update_self]
      omega
    · simp only [hsend, Bool.false_eq_true, ↓reduceIte]
      exact ⟨by omega, trivial⟩

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem spkStateInv_epMgmt
    {P : Params Bytes PQC} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ck0 s alice pqr : BitVec 256}
    {st st1 : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes}
    {qep : ℕ} {Q : Party} {bad : Bool}
    (hs : SpkStateInv P decT encT ck0 s alice pqr st)
    (hok : noBobSendInEpoch0 st Q = true)
    (hep : st.epMgmt 3 qep Q bad = some st1) :
    SpkStateInv P decT encT ck0 s alice pqr st1 ∧ 0 < st1.epoch Q := by
  obtain ⟨hst, htr⟩ := GameEq.epMgmt_st_trans hep
  obtain ⟨hpos, heB⟩ := epMgmt_epoch_pos_of_noBobEpoch0 hok hep
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hpos⟩
  · rw [hst, heB]
    exact hs.b_epoch_zero_iff
  · rw [hst]
    exact hs.b_eq_initB
  · intro R
    rw [hst]
    exact hs.party_eq R
  · intro R
    rw [hst]
    exact hs.sender_inv R
  · intro r hr
    rw [htr] at hr
    exact hs.trans_inv r hr

theorem spkStateInv_record_send
    {P : Params Bytes PQC} (hcodec : P.codec = protoSignalCodec) (hL : LengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    {ck0 s alice pqr : BitVec 256} (rk0 : BitVec 256)
    {st1 : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes}
    (hs1 : SpkStateInv P decT encT ck0 s alice pqr st1)
    (Q : Party) (hneB0 : ¬ (Q = .B ∧ (st1.st .B).epoch = 0))
    (hpos : 0 < st1.epoch Q) (m : CBC.Plain ℓ) (coins : PQC)
    (rec : SM.Record (CBC.Plain ℓ) Bytes)
    (hrec_ep : rec.pos.epoch = st1.epoch Q)
    (hrec_ct : rec.ct = ((sessionSchemeU P ℓ).send (st1.st Q) m coins).2)
    (isChall : Bool) :
    let st' := ((sessionSchemeU P ℓ).send (st1.st Q) m coins).1
    patchPartySpk rk0 st' = st' ∧
      SpkStateInv P decT encT ck0 s alice pqr (st1.record 3 Q st' rec isChall) := by
  set st' := ((sessionSchemeU P ℓ).send (st1.st Q) m coins).1
  obtain ⟨hsend_inv, hsend_party, hsend_ep⟩ :=
    sessionSenderInv_send P (st1.st Q) m coins (hs1.sender_inv Q)
  change SessionSenderInv P st'.session at hsend_inv
  change st'.party = (st1.st Q).party at hsend_party
  change st'.epoch = (st1.st Q).epoch ∨ st'.epoch = (st1.st Q).epoch + 1 at hsend_ep
  have hst'_party : st'.party = Q := hsend_party.trans (hs1.party_eq Q)
  have hnot_B0 : ¬ (st'.party = .B ∧ st'.epoch = 0) := by
    rintro ⟨hp, he0⟩
    rw [hst'_party] at hp
    subst hp
    have hb_ne0 : (st1.st .B).epoch ≠ 0 := fun h0 => hneB0 ⟨rfl, h0⟩
    rcases hsend_ep with h1 | h2 <;> omega
  have hpatch : patchPartySpk rk0 st' = st' := patchPartySpk_of_not_B0 rk0 st' hnot_B0
  have horc : ratchetKeyAdmissible protoSignalCodec decT encT rec.ct = true := by
    rw [hrec_ct]
    exact ratchetKeyOnCurve_send P hcodec hL Dh encPt encT decT hX hdec (st1.st Q)
      (hs1.sender_inv Q).1 (hs1.sender_inv Q).2 m coins
  refine ⟨hpatch, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · unfold SM.GameState.record
    dsimp only
    cases Q with
    | A =>
      rw [Function.update_of_ne (by decide)]
      exact hs1.b_epoch_zero_iff
    | B =>
      rw [Function.update_self]
      have hb_ne0 : (st1.st .B).epoch ≠ 0 := fun h0 => hneB0 ⟨rfl, h0⟩
      have he_ne0 : st1.epoch .B ≠ 0 := fun h0 => hb_ne0 (hs1.b_epoch_zero_iff.mpr h0)
      have hst'_ne0 : st'.epoch ≠ 0 := fun h0 => hnot_B0 ⟨hst'_party, h0⟩
      exact ⟨fun h => False.elim (hst'_ne0 h), fun h => False.elim (he_ne0 h)⟩
  · unfold SM.GameState.record
    dsimp only
    cases Q with
    | A =>
      rw [Function.update_of_ne (by decide)]
      exact hs1.b_eq_initB
    | B =>
      rw [Function.update_self]
      intro h0
      exact False.elim (hnot_B0 ⟨hst'_party, h0⟩)
  · intro R
    unfold SM.GameState.record
    dsimp only
    by_cases hR : R = Q
    · subst hR
      simp [hst'_party]
    · simp [Function.update_of_ne hR, hs1.party_eq R]
  · intro R
    unfold SM.GameState.record
    dsimp only
    by_cases hR : R = Q
    · subst hR
      simp [hsend_inv]
    · simp [Function.update_of_ne hR, hs1.sender_inv R]
  · intro r hr
    unfold SM.GameState.record at hr
    dsimp only at hr
    rcases List.mem_cons.mp hr with rfl | hr_old
    · exact ⟨hrec_ep ▸ hpos, horc⟩
    · exact hs1.trans_inv r hr_old

theorem simulateQ_purePrfImpl_receiveSpk
    (P : Params Bytes PQC) (hcodec : P.codec = protoSignalCodec)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hz : ∀ x, Dh.dh x 0 = 0)
    (rk0 ck0 s alice pqr : BitVec 256)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes)
    (hs : SpkStateInv P decT encT ck0 s alice pqr st)
    (Q : Party) (c : Bytes) (horc : ratchetKeyAdmissible protoSignalCodec decT encT c = true)
    (rc : BitVec 256) :
    simulateQ (purePrfImpl P.C.F encPt rk0)
      (receiveSpk P ℓ Dh encT decT s (st.st Q) c rc) =
      pure ((sessionSchemeU P ℓ).receive (patchPartySpk rk0 (st.st Q)) c rc) := by
  unfold receiveSpk patchPartySpk
  by_cases hcond : ((st.st Q).party == .B && (st.st Q).epoch == 0) = true
  · simp only [hcond, ↓reduceIte]
    have hcond' := hcond
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hcond'
    have hQ : Q = .B := (hs.party_eq Q).symm.trans hcond'.1
    subst hQ
    have hinitB := hs.b_eq_initB hcond'.2
    rw [hinitB]
    exact receiveB0_purePrfImpl_eq P hcodec Dh encPt encT decT hX hz rk0 ck0 s alice pqr c horc rc
  · simp only [hcond, Bool.false_eq_true, ↓reduceIte, simulateQ_pure]

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem spkStateInv_accept_receive
    (P : Params Bytes PQC)
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ck0 s alice pqr : BitVec 256} (rk0 : BitVec 256)
    {st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes}
    (hs : SpkStateInv P decT encT ck0 s alice pqr st)
    (Q : Party) (c : Bytes) (rc : BitVec 256)
    (st' : GhostState Bytes) (t' i' : ℕ) (m' : CBC.Plain ℓ)
    (hrec : (sessionSchemeU P ℓ).receive (patchPartySpk rk0 (st.st Q)) c rc =
      some (st', t', i', m'))
    (pos : SM.Pos) (hpos : Q = .B → (st.st .B).epoch = 0 → t' = 1 → 0 < pos.epoch) :
    patchPartySpk rk0 st' = st' ∧
      (Q = .B → (st.st .B).epoch = 0 → 0 < t') ∧
      SpkStateInv P decT encT ck0 s alice pqr (st.accept Q st' pos) := by
  have hsinv : SessionSenderInv P (patchPartySpk rk0 (st.st Q)).session :=
    (patchPartySpk_sessionSenderInv P rk0 (st.st Q)).mpr (hs.sender_inv Q)
  obtain ⟨hst'_inv, hst'_party, hst'_ep, hst'_init⟩ :=
    sessionSenderInv_receive P (patchPartySpk rk0 (st.st Q)) c rc (st', t', i', m') hsinv hrec
  dsimp only at hst'_inv hst'_party hst'_ep hst'_init
  rw [patchPartySpk_party, hs.party_eq Q] at hst'_party
  rw [patchPartySpk_epoch] at hst'_ep hst'_init
  have hB_t' : Q = .B → (st.st .B).epoch = 0 → st'.epoch = 1 ∧ t' = 1 := by
    intro hQ hb0
    subst hQ
    have hinitB := hs.b_eq_initB hb0
    have hrc_nil : (patchPartySpk rk0 (st.st .B)).session.receiverChains = [] := by
      rw [hinitB, patchPartySpk_initB]
      rfl
    have h1 := hst'_init hrc_nil
    omega
  have hnot_B0 : ¬ (st'.party = .B ∧ st'.epoch = 0) := by
    rintro ⟨hp, he0⟩
    rw [hst'_party] at hp
    subst hp
    by_cases hb0 : (st.st .B).epoch = 0
    · have h1 := (hB_t' rfl hb0).1
      omega
    · rcases hst'_ep with h1 | h2 <;> omega
  have hpatch : patchPartySpk rk0 st' = st' := patchPartySpk_of_not_B0 rk0 st' hnot_B0
  refine ⟨hpatch, fun hQ hb0 => by have := (hB_t' hQ hb0).2; omega, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · unfold SM.GameState.accept SM.GameState.delete
    dsimp only
    cases Q with
    | A =>
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
      exact hs.b_epoch_zero_iff
    | B =>
      rw [Function.update_self, Function.update_self]
      have hst'_ne0 : st'.epoch ≠ 0 := fun h0 => hnot_B0 ⟨hst'_party, h0⟩
      have hmax_ne0 : max (st.epoch .B) pos.epoch ≠ 0 := by
        by_cases hb0 : (st.st .B).epoch = 0
        · have hp_pos := hpos rfl hb0 (hB_t' rfl hb0).2
          omega
        · have he_ne0 : st.epoch .B ≠ 0 := fun h0 => hb0 (hs.b_epoch_zero_iff.mpr h0)
          omega
      exact ⟨fun h => False.elim (hst'_ne0 h), fun h => False.elim (hmax_ne0 h)⟩
  · unfold SM.GameState.accept SM.GameState.delete
    dsimp only
    cases Q with
    | A =>
      rw [Function.update_of_ne (by decide)]
      exact hs.b_eq_initB
    | B =>
      rw [Function.update_self]
      intro h0
      exact False.elim (hnot_B0 ⟨hst'_party, h0⟩)
  · intro R
    unfold SM.GameState.accept SM.GameState.delete
    dsimp only
    by_cases hR : R = Q
    · subst hR
      simp [hst'_party]
    · simp [Function.update_of_ne hR, hs.party_eq R]
  · intro R
    unfold SM.GameState.accept SM.GameState.delete
    dsimp only
    by_cases hR : R = Q
    · subst hR
      simp [hst'_inv]
    · simp [Function.update_of_ne hR, hs.sender_inv R]
  · intro r hr
    unfold SM.GameState.accept SM.GameState.delete at hr
    dsimp only at hr
    exact hs.trans_inv r (List.mem_of_mem_filter hr)

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem spkStateInv_afterCorr
    {P : Params Bytes PQC} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ck0 s alice pqr : BitVec 256}
    {st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes}
    (hs : SpkStateInv P decT encT ck0 s alice pqr st) (Q : Party) :
    SpkStateInv P decT encT ck0 s alice pqr (st.afterCorr Q) :=
  ⟨hs.b_epoch_zero_iff, hs.b_eq_initB, hs.party_eq, hs.sender_inv, hs.trans_inv⟩

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem spkStateInv_with_win
    {P : Params Bytes PQC} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ck0 s alice pqr : BitVec 256}
    {st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes}
    (hs : SpkStateInv P decT encT ck0 s alice pqr st) (w : Bool) :
    SpkStateInv P decT encT ck0 s alice pqr { st with win := w } :=
  ⟨hs.b_epoch_zero_iff, hs.b_eq_initB, hs.party_eq, hs.sender_inv, hs.trans_inv⟩


omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem inTransit_spkStateInv
    {P : Params Bytes PQC} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ck0 s alice pqr : BitVec 256}
    {st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes}
    (hs : SpkStateInv P decT encT ck0 s alice pqr st)
    {Q : Party} {c : Bytes} {r : SM.Record (CBC.Plain ℓ) Bytes}
    (htr : st.inTransit Q c = some r) :
    0 < r.pos.epoch ∧ ratchetKeyAdmissible protoSignalCodec decT encT c = true := by
  unfold SM.GameState.inTransit at htr
  have hmem : r ∈ st.trans := List.mem_of_find?_eq_some htr
  have hpred := List.find?_some htr
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hpred
  rw [← hpred.2]
  exact hs.trans_inv r hmem

@[simp] theorem mapSt_noCorrB0 {St₁ St₂ Msg C : Type} (φ : St₁ → St₂)
    (s : SM.GameState St₁ Msg C) (P : Party) :
    noBobCorrInEpoch0 (GameEq.mapSt φ s) P = noBobCorrInEpoch0 s P := rfl

@[simp] theorem mapSt_noCorrBWin {St₁ St₂ Msg C : Type} (φ : St₁ → St₂)
    (s : SM.GameState St₁ Msg C) (P : Party) :
    noBobCorrWhileAliceBelowEpoch10 (GameEq.mapSt φ s) P = noBobCorrWhileAliceBelowEpoch10 s P := rfl

@[simp] theorem stateT_lift_run {m : Type → Type} [Monad m] {σ α : Type} (x : m α) (s : σ) :
    (StateT.lift x : StateT σ m α).run s = (x >>= fun a => pure (a, s)) := rfl

theorem send_patchPartySpk_eq
    {P : Params Bytes PQC} (hcodec : P.codec = protoSignalCodec) (hL : LengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    {ck0 s alice pqr : BitVec 256} (rk0 : BitVec 256)
    {st1 : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes}
    (hs1 : SpkStateInv P decT encT ck0 s alice pqr st1)
    (Q : Party) (hneB0 : ¬ (Q = .B ∧ (st1.st .B).epoch = 0))
    (hpos : 0 < st1.epoch Q) (m : CBC.Plain ℓ) (coins : PQC) :
    ((sessionSchemeU P ℓ).send (patchPartySpk rk0 (st1.st Q)) m coins) =
      Prod.map (patchPartySpk rk0) id ((sessionSchemeU P ℓ).send (st1.st Q) m coins) := by
  have hpatch_in : patchPartySpk rk0 (st1.st Q) = st1.st Q := by
    apply patchPartySpk_of_not_B0
    rintro ⟨hp, he0⟩
    rw [hs1.party_eq Q] at hp
    subst hp
    exact hneB0 ⟨rfl, he0⟩
  obtain ⟨hpatch_out, _⟩ := spkStateInv_record_send hcodec hL Dh encPt hX hdec rk0 hs1
    Q hneB0 hpos m coins
    ⟨⟨Q, st1.epoch Q, st1.idx Q + 1⟩, m, ((sessionSchemeU P ℓ).send (st1.st Q) m coins).2⟩
    rfl rfl false
  rw [hpatch_in]
  exact Prod.ext hpatch_out.symm rfl

theorem transmitR_spk_eq
    (P : Params Bytes PQC) (hcodec : P.codec = protoSignalCodec) (hL : LengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (qep : ℕ) (rk0 ck0 s alice pqr : BitVec 256)
    (x : Party × CBC.Plain ℓ × Option PQC)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes)
    (hs : SpkStateInv P decT encT ck0 s alice pqr st) :
    (SM.transmitR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) x).run
        (GameEq.mapSt (patchPartySpk rk0) st) =
      Prod.map id (GameEq.mapSt (patchPartySpk rk0)) <$>
        (SM.transmitR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) x).run st := by
  rcases x with ⟨Q, m, r⟩
  unfold SM.transmitR SM.transmitImpl SMSchemeR.sendPart configRefuseEarlyBobCorr configR1OnCurve configR1
  simp only [StateT.run_bind, StateT.run_get, pure_bind, GameEq.mapSt_noBobEpoch0]
  by_cases hok : noBobSendInEpoch0 st Q = true
  · by_cases hwin : st.win = true
    · simp [hok, hwin]
    · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
        StateT.run_get, pure_bind, GameEq.mapSt_win, hwin, StateT.run_monadLift, bind_assoc,
        map_eq_bind_pure_comp, GameEq.mapSt_epMgmt]
      congr 1
      funext cb
      cases hep : st.epMgmt 3 qep Q cb.2 with
      | none => simp
      | some st1 =>
        obtain ⟨hs1, hpos⟩ := spkStateInv_epMgmt hs hok hep
        obtain ⟨hst, _⟩ := GameEq.epMgmt_st_trans hep
        obtain ⟨_, hneB0⟩ := patchPartySpk_st_of_noBobEpoch0 hs rk0 Q hok
        have hneB01 : ¬ (Q = .B ∧ (st1.st .B).epoch = 0) := hst ▸ hneB0
        simp only [Option.map_some, StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
          GameEq.mapSt_st,
          send_patchPartySpk_eq hcodec hL Dh encPt hX hdec rk0 hs1 Q hneB01 hpos m cb.1,
          Prod.map_fst, Prod.map_snd, id_eq, GameEq.mapSt_epoch, GameEq.mapSt_idx,
          GameEq.mapSt_record]
        rfl
  · simp [hok]

theorem transmitR_spk_preserve
    (P : Params Bytes PQC) (hcodec : P.codec = protoSignalCodec) (hL : LengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (qep : ℕ) (rk0 ck0 s alice pqr : BitVec 256)
    (x : Party × CBC.Plain ℓ × Option PQC)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes)
    (hs : SpkStateInv P decT encT ck0 s alice pqr st) :
    ∀ z ∈ support ((SM.transmitR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) x).run st),
      SpkStateInv P decT encT ck0 s alice pqr z.2 := by
  rcases x with ⟨Q, m, r⟩
  intro z hz
  unfold SM.transmitR configRefuseEarlyBobCorr configR1OnCurve configR1 at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  by_cases hok : noBobSendInEpoch0 st Q = true
  · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hz
    simp only [SM.transmitImpl, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact hs
    · rw [StateT.run_bind] at hz
      simp only [StateT.run_monadLift, bind_assoc, pure_bind, MonadAttach.mem_support_bind] at hz
      rcases hz with ⟨cb, _, hz⟩
      cases hep : st.epMgmt 3 qep Q cb.2 with
      | none =>
        simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hs
      | some st1 =>
        simp only [hep, StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
          support_pure, Set.mem_singleton_iff] at hz
        subst hz
        obtain ⟨hs1, hpos⟩ := spkStateInv_epMgmt hs hok hep
        obtain ⟨hst, _⟩ := GameEq.epMgmt_st_trans hep
        obtain ⟨_, hneB0⟩ := patchPartySpk_st_of_noBobEpoch0 hs rk0 Q hok
        have hneB01 : ¬ (Q = .B ∧ (st1.st .B).epoch = 0) := hst ▸ hneB0
        exact (spkStateInv_record_send hcodec hL Dh encPt hX hdec rk0 hs1 Q hneB01 hpos m cb.1
          ⟨⟨Q, st1.epoch Q, st1.idx Q + 1⟩, m, ((sessionSchemeU P ℓ).send (st1.st Q) m cb.1).2⟩
          rfl rfl false).2
  · simp only [hok, Bool.not_false, ↓reduceIte, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz; exact hs

theorem challR_spk_eq
    (P : Params Bytes PQC) (hcodec : P.codec = protoSignalCodec) (hL : LengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (qep : ℕ) (rk0 ck0 s alice pqr : BitVec 256)
    (x : Party × CBC.Plain ℓ × CBC.Plain ℓ × Option PQC)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes)
    (hs : SpkStateInv P decT encT ck0 s alice pqr st) :
    (SM.challR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) x).run
        (GameEq.mapSt (patchPartySpk rk0) st) =
      Prod.map id (GameEq.mapSt (patchPartySpk rk0)) <$>
        (SM.challR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) x).run st := by
  rcases x with ⟨Q, m₀, m₁, r⟩
  unfold SM.challR SM.challImpl SMSchemeR.sendPart configRefuseEarlyBobCorr configR1OnCurve configR1 SM.Config.h1
  simp only [StateT.run_bind, StateT.run_get, pure_bind, GameEq.mapSt_noBobEpoch0]
  by_cases hok : noBobSendInEpoch0 st Q = true
  · by_cases hwin : st.win = true
    · simp [hok, hwin]
    · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
        StateT.run_get, pure_bind, GameEq.mapSt_win, hwin, StateT.run_monadLift, bind_assoc,
        map_eq_bind_pure_comp, GameEq.mapSt_epMgmt]
      congr 1
      funext cb
      cases hep : st.epMgmt 3 qep Q cb.2 with
      | none => simp
      | some st1 =>
        obtain ⟨hs1, hpos⟩ := spkStateInv_epMgmt hs hok hep
        obtain ⟨hst, _⟩ := GameEq.epMgmt_st_trans hep
        obtain ⟨_, hneB0⟩ := patchPartySpk_st_of_noBobEpoch0 hs rk0 Q hok
        have hneB01 : ¬ (Q = .B ∧ (st1.st .B).epoch = 0) := hst ▸ hneB0
        simp only [Option.map_some, GameEq.mapSt_safeCh, GameEq.mapSt_epoch, GameEq.mapSt_b,
          Bool.or_false]
        by_cases hsc : st1.safeCh 3 Q = true
        · simp only [hsc, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
            StateT.run_set, pure_bind, StateT.run_pure, GameEq.mapSt_st,
            send_patchPartySpk_eq hcodec hL Dh encPt hX hdec rk0 hs1 Q hneB01 hpos _ cb.1,
            Prod.map_fst, Prod.map_snd, id_eq, GameEq.mapSt_idx, GameEq.mapSt_record]
          rfl
        · simp [hsc]
  · simp [hok]

theorem challR_spk_preserve
    (P : Params Bytes PQC) (hcodec : P.codec = protoSignalCodec) (hL : LengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (qep : ℕ) (rk0 ck0 s alice pqr : BitVec 256)
    (x : Party × CBC.Plain ℓ × CBC.Plain ℓ × Option PQC)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes)
    (hs : SpkStateInv P decT encT ck0 s alice pqr st) :
    ∀ z ∈ support ((SM.challR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) x).run st),
      SpkStateInv P decT encT ck0 s alice pqr z.2 := by
  rcases x with ⟨Q, m₀, m₁, r⟩
  intro z hz
  unfold SM.challR configRefuseEarlyBobCorr configR1OnCurve configR1 at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  by_cases hok : noBobSendInEpoch0 st Q = true
  · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hz
    simp only [SM.challImpl, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact hs
    · rw [StateT.run_bind] at hz
      simp only [StateT.run_monadLift, bind_assoc, pure_bind, MonadAttach.mem_support_bind] at hz
      rcases hz with ⟨cb, _, hz⟩
      cases hep : st.epMgmt 3 qep Q cb.2 with
      | none =>
        simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hs
      | some st1 =>
        simp only [hep] at hz
        split at hz
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact hs
        · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
            support_pure, Set.mem_singleton_iff] at hz
          subst hz
          obtain ⟨hs1, hpos⟩ := spkStateInv_epMgmt hs hok hep
          obtain ⟨hst, _⟩ := GameEq.epMgmt_st_trans hep
          obtain ⟨_, hneB0⟩ := patchPartySpk_st_of_noBobEpoch0 hs rk0 Q hok
          have hneB01 : ¬ (Q = .B ∧ (st1.st .B).epoch = 0) := hst ▸ hneB0
          exact (spkStateInv_record_send hcodec hL Dh encPt hX hdec rk0 hs1 Q hneB01 hpos _ cb.1
            ⟨⟨Q, st1.epoch Q, st1.idx Q + 1⟩, _, ((sessionSchemeU P ℓ).send (st1.st Q) _ cb.1).2⟩
            rfl rfl true).2
  · simp only [hok, Bool.not_false, ↓reduceIte, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz; exact hs


end SpkHop2

end CryptoVerification.E2E
