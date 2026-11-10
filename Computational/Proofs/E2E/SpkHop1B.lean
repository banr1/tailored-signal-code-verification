/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.SpkHop1A
public import Computational.Proofs.E2E.SpkHop2Red
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.GhostStep
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.RecvCoins
import Computational.Proofs.E2E.SpkHop2A

/-!
# Hop 2 Unit Bounds, Root-Key Patching, and Lazy-Table Helpers

Establishes single-query unit bounds (`hop2GuessUnit`, `hop2CollUnit`, `hop2FreshUnit`,
`hop2CreateCollUnit`), root-key patching under the `DEV-LS34` window corruption refusal, and
lazy-table simulation helpers (`lazyImpl`, `LookupEq`) for Hop 2 coupling.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoVerification.E2E.SpkHop1

open CryptoGames CryptoGames.SM CryptoGames.Ratchet CryptoGames.Ratchet.LibsignalInst
  CryptoGames.LibsignalSession CBC
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.E2E CryptoVerification.E2E.Relabel CryptoVerification.E2E.Relabel.GameEq

set_option linter.unusedSectionVars false

section Hop2Coupling

open CryptoGames.CKA CryptoGames.LibsignalSM.Proofs.Refinement
open HMAC HKDF MACScheme

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
variable {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC] {ℓ : ℕ}

/-! ## Key-conversion and KDF identities -/

private theorem extractLsb'_zero_bytesToKey32_cons (b : BitVec 8) (acc : BitVec 256) :
    ((acc <<< 8) ||| b.zeroExtend 256).extractLsb' 0 8 = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', Nat.zero_add, hi, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have h256 : i < 256 := by omega
  simp [hi, h256]

private theorem extractLsb'_succ_bytesToKey32_cons (b : BitVec 8) (acc : BitVec 256) (j : Nat)
    (hj : j + 1 < 32) :
    ((acc <<< 8) ||| b.zeroExtend 256).extractLsb' (8 * (j + 1)) 8 =
      acc.extractLsb' (8 * j) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
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

private theorem extractLsb'_bytesToKey32 (bs : List (BitVec 8)) (j : Nat)
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

theorem keyToBytes32_bytesToKey32_std (bs : List (BitVec 8)) (h : bs.length = 32) :
    keyToBytes32 (HKDF.bytesToKey32 bs) = bs := by
  refine List.ext_getElem (by simp [keyToBytes32, h]) fun j h1 h2 => ?_
  simp only [keyToBytes32, List.getElem_ofFn]
  exact extractLsb'_bytesToKey32 bs j h2 (by omega)

theorem length_hkdfExtract_std (F : ShaState → List (BitVec 8) → ShaState) (salt : Salt)
    (ikm : List (BitVec 8)) :
    (HKDF.hkdfExtract F salt ikm).length = 32 := by
  unfold HKDF.hkdfExtract HMAC.hmacWith HMAC.sha256With
  generalize (HMAC.chunks64 _).foldl F HMAC.sha256IV = st
  rcases st with ⟨l, hl⟩
  simp [HMAC.toBEBytes, List.length_flatMap]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem rootExpand_extractPRF_eq_rootKdf (F : ShaState → List (BitVec 8) → ShaState)
    (encPt : Pt → Bytes) (rk : Ratchet.RootKey) (I : Pt) :
    Ratchet.rootExpand F (keyToBytes32 ((extractPRF F encPt).tag rk I)) =
      rootKdf F rk (encPt I) := by
  dsimp only [extractPRF, rootKdf, HKDF.hkdf, Ratchet.rootExpand]
  rw [keyToBytes32_bytesToKey32_std (HKDF.hkdfExtract F (rootSalt rk) (encPt I))
    (length_hkdfExtract_std F _ _)]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem rootExpand_extractPRF_eq_rootPRNG_up (F : ShaState → List (BitVec 8) → ShaState)
    (encPt : Pt → Bytes) (rk : Ratchet.RootKey) (I : Pt) :
    Ratchet.rootExpand F (keyToBytes32 ((extractPRF F encPt).tag rk I)) =
      (rootPRNG F encPt).up rk I :=
  rootExpand_extractPRF_eq_rootKdf F encPt rk I

/-! ## Single-query unit bounds -/

/-- Single-point supremum unit of `spkSwapHiddenScalarGuessTerm`. -/
noncomputable def hop2GuessUnit (Dh : DHFun (BitVec 256) Pt) : ℝ≥0∞ :=
  ⨆ P_pt : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = P_pt}

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem hop2GuessTerm_eq_mul_unit (Dh : DHFun (BitVec 256) Pt) (q : ℕ) :
    spkSwapHiddenScalarGuessTerm Dh q = ((6 * q : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh := rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem dh_base_eq_le_hop2GuessUnit (Dh : DHFun (BitVec 256) Pt) (P_pt : Pt) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = P_pt} ≤ hop2GuessUnit Dh :=
  le_iSup (fun Q : Pt => 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q}) P_pt

omit [Zero Pt] [SampleableType Pt] in
theorem dh_base_eq_prob_le_hop2GuessUnit (Dh : DHFun (BitVec 256) Pt) (P_pt : Pt) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x => pure (decide (Dh.dh x Dh.base =
        P_pt))] {true} ≤
      hop2GuessUnit Dh := by
  rw [evalDist_bind_of_discrete,
    MeasureTheory.Measure.bind_apply (MeasurableSet.singleton true)
        Measurable.of_discrete.aemeasurable]
  calc ∫⁻ x, 𝒟[pure (decide (Dh.dh x Dh.base = P_pt))] {true}
          ∂𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))]
      = ∫⁻ x, Set.indicator {x | Dh.dh x Dh.base = P_pt} 1 x
          ∂𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] := by
        refine MeasureTheory.lintegral_congr fun x => ?_
        by_cases h : Dh.dh x Dh.base = P_pt <;> simp [h]
    _ = 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = P_pt} :=
        MeasureTheory.lintegral_indicator_one MeasurableSet.of_discrete
    _ ≤ hop2GuessUnit Dh := dh_base_eq_le_hop2GuessUnit Dh P_pt

/-- Single-query supremum unit of `spkSwapCreationPointHitTerm`. -/
noncomputable def hop2CollUnit (Dh : DHFun (BitVec 256) Pt) : ℝ≥0∞ :=
  ⨆ (a : BitVec 256) (T : Pt),
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {r | Dh.dh a (Dh.dh r Dh.base) = Dh.dh a T}

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem hop2CollTerm_eq_mul_unit (Dh : DHFun (BitVec 256) Pt) (q : ℕ) :
    spkSwapCreationPointHitTerm Dh q = ((q + 1 : ℕ) : ℝ≥0∞) * hop2CollUnit Dh := by
  simp [spkSwapCreationPointHitTerm, hop2CollUnit]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem dh_coll_single_le_hop2CollUnit (Dh : DHFun (BitVec 256) Pt) (a : BitVec 256) (T : Pt) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {r | Dh.dh a (Dh.dh r Dh.base) = Dh.dh a T} ≤
      hop2CollUnit Dh := by
  unfold hop2CollUnit
  exact le_iSup_of_le a (le_iSup_of_le T le_rfl)

omit [Zero Pt] [SampleableType Pt] in
theorem dh_coll_prob_le_hop2CollUnit (Dh : DHFun (BitVec 256) Pt) (a : BitVec 256) (T : Pt) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>=
        fun r => pure (decide (Dh.dh a (Dh.dh r Dh.base) = Dh.dh a T))] {true} ≤
      hop2CollUnit Dh := by
  rw [evalDist_bind_of_discrete,
    MeasureTheory.Measure.bind_apply (MeasurableSet.singleton true)
        Measurable.of_discrete.aemeasurable]
  calc ∫⁻ r, 𝒟[pure (decide (Dh.dh a (Dh.dh r Dh.base) = Dh.dh a T))] {true}
          ∂𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))]
      = ∫⁻ r, Set.indicator {r | Dh.dh a (Dh.dh r Dh.base) = Dh.dh a T} 1 r
          ∂𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] := by
        refine MeasureTheory.lintegral_congr fun r => ?_
        by_cases h : Dh.dh a (Dh.dh r Dh.base) = Dh.dh a T <;> simp [h]
    _ = 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {r | Dh.dh a (Dh.dh r Dh.base) = Dh.dh a T} :=
        MeasureTheory.lintegral_indicator_one MeasurableSet.of_discrete
    _ ≤ hop2CollUnit Dh := dh_coll_single_le_hop2CollUnit Dh a T

/-- Single-query supremum unit of `spkSwapSpuriousStepTerm`. -/
noncomputable def hop2FreshUnit (F : ShaState → List (BitVec 8) → ShaState) : ℝ≥0∞ :=
  ⨆ (c : ℕ) (_ : c < 2 ^ 32) (salt : Salt) (ids : LibsignalAead.SerializedIdentityKeys) (ser : List (BitVec 8))
    (_ : ser.length < 2 ^ 32) (tag : BitVec 64),
    ((Ratchet.expandPRG F).prgAdvantage (LibsignalSim.wireMacVerifiesTest F c salt ids ser tag) +
      𝒟[PRGScheme.prgIdealExperiment (LibsignalSim.wireMacVerifiesTest F c salt ids ser tag)] {true})

theorem hop2FreshTerm_eq_mul_unit (F : ShaState → List (BitVec 8) → ShaState) (q : ℕ) :
    spkSwapSpuriousStepTerm F q = (q : ℝ≥0∞) * hop2FreshUnit F := rfl

theorem expandPRG_spurDist_real_le_hop2FreshUnit (F : ShaState → List (BitVec 8) → ShaState)
    (c : ℕ) (hc : c < 2 ^ 32) (salt : Salt) (ids : LibsignalAead.SerializedIdentityKeys)
    (ser : List (BitVec 8)) (hser : ser.length < 2 ^ 32) (tag : BitVec 64) :
    𝒟[(Ratchet.expandPRG F).prgRealExperiment (LibsignalSim.wireMacVerifiesTest F c salt ids ser tag)] {true} ≤
      hop2FreshUnit F := by
  refine (prgReal_true_le (Ratchet.expandPRG F) (LibsignalSim.wireMacVerifiesTest F c salt ids ser tag)).trans
      ?_
  unfold hop2FreshUnit
  exact le_iSup₂_of_le c hc (le_iSup_of_le salt (le_iSup_of_le ids
    (le_iSup₂_of_le ser hser (le_iSup_of_le tag le_rfl))))

omit [Inhabited PQ] [SampleableType PQC] in
theorem testSpk_expandPRG_le_hop2FreshUnit (P : Params PQ PQC) (pqrState : PQ) (c :
    List (BitVec 8)) (hc : ∀ msg, SignalMessage.tryFrom P.codec c = .ok msg → c.length < 2 ^ 32) :
    𝒟[(do let prk ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
          pure (testSpk P pqrState c ((Ratchet.expandPRG P.C.F).gen prk).2) :
              ProbComp Bool)] {true} ≤
      hop2FreshUnit P.C.F := by
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
      dsimp only []
      change 𝒟[(Ratchet.expandPRG P.C.F).prgRealExperiment
        (LibsignalSim.wireMacVerifiesTest P.C.F msg.counter.toNat ps.2 (macIds P.idB P.idA)
          (msg.serialized.take (msg.serialized.length - macLength))
          (bytesToWord64LE (msg.serialized.drop (msg.serialized.length - macLength))))] {true} ≤
        hop2FreshUnit P.C.F
      have hser := tryFrom_serialized_eq P.codec c msg htry
      refine expandPRG_spurDist_real_le_hop2FreshUnit P.C.F msg.counter.toNat msg.counter.isLt ps.2
        (macIds P.idB P.idA) (msg.serialized.take (msg.serialized.length - macLength)) ?_
        (bytesToWord64LE (msg.serialized.drop (msg.serialized.length - macLength)))
      rw [hser, List.length_take]
      exact lt_of_le_of_lt (Nat.min_le_right _ _) (hc msg htry)

/-- Single-query supremum unit of `hop2CreateCollTerm`. -/
noncomputable def hop2CreateCollUnit (Dh : DHFun (BitVec 256) Pt) : ℝ≥0∞ :=
  ⨆ (T : Pt) (Q : Pt),
    if Q = 0 then 0 else 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {r | Dh.dh r T = Q}

omit [SampleableType Pt] in
theorem dh_createColl_single_le_hop2CreateCollUnit (Dh : DHFun (BitVec 256) Pt) (T Q : Pt)
    (hQ : Q ≠ 0) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {r | Dh.dh r T = Q} ≤
      hop2CreateCollUnit Dh := by
  unfold hop2CreateCollUnit
  refine le_iSup_of_le T (le_iSup_of_le Q ?_)
  simp [hQ]

omit [SampleableType Pt] in
theorem dh_createColl_prob_le_hop2CreateCollUnit (Dh : DHFun (BitVec 256) Pt) (T Q : Pt)
    (hQ : Q ≠ 0) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>=
        fun r => pure (decide (Dh.dh r T = Q))] {true} ≤
      hop2CreateCollUnit Dh := by
  rw [evalDist_bind_of_discrete,
    MeasureTheory.Measure.bind_apply (MeasurableSet.singleton true)
        Measurable.of_discrete.aemeasurable]
  calc ∫⁻ r, 𝒟[pure (decide (Dh.dh r T = Q))] {true}
          ∂𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))]
      = ∫⁻ r, Set.indicator {r | Dh.dh r T = Q} 1 r
          ∂𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] := by
        refine MeasureTheory.lintegral_congr fun r => ?_
        by_cases h : Dh.dh r T = Q <;> simp [h]
    _ = 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {r | Dh.dh r T = Q} :=
        MeasureTheory.lintegral_indicator_one MeasurableSet.of_discrete
    _ ≤ hop2CreateCollUnit Dh := dh_createColl_single_le_hop2CreateCollUnit Dh T Q hQ

/-! ## Root-key patching and `DEV-LS34` window corruption refusal -/

def setRootKey (rk : Ratchet.RootKey) (g : GhostState PQ) : GhostState PQ :=
  { g with session := { g.session with rootKey := rk } }

theorem Mut_exec_outgoingFromSessionState_rootKey (rk : Ratchet.RootKey) (s : SessionState PQ) :
    Mut.exec OutgoingTripleRatchet.fromSessionState { s with rootKey := rk } =
      ( (Mut.exec OutgoingTripleRatchet.fromSessionState s).1,
        { (Mut.exec OutgoingTripleRatchet.fromSessionState s).2 with rootKey := rk } ) := by
  unfold OutgoingTripleRatchet.fromSessionState SessionState.version
  simp only [Mut_exec_bind, Mut_exec_get]
  cases hsc : s.senderChain with
  | none => simp [hsc, Mut_exec_throw]
  | some sc =>
    simp only [hsc, Mut_exec_bind, Mut_exec_get, Mut_exec_takePqRatchetState
      ]
    by_cases hv : 256 ≤ (if s.sessionVersion = 0 then (2 : BitVec 32) else s.sessionVersion).toNat
    · simp only [hv, ↓reduceIte, Mut_exec_throw, Mut_exec_bind]
    · simp only [hv, ↓reduceIte]
      cases s.remoteIdentity <;> rfl

omit [SampleableType PQC] in
theorem messageEncrypt_setRootKey (P : Params PQ PQC) (rk : Ratchet.RootKey)
    (addr : Option (List (BitVec 8))) (m : List (BitVec 8)) (r : PQC) (s : SessionState PQ) :
    SessionState.messageEncrypt P.C P.codec P.spqr addr m r { s with rootKey := rk } =
      ( (SessionState.messageEncrypt P.C P.codec P.spqr addr m r s).1,
        { (SessionState.messageEncrypt P.C P.codec P.spqr addr m r s).2 with rootKey := rk } ) := by
  unfold SessionState.messageEncrypt SessionState.encryptAddresses
    OutgoingTripleRatchet.applyToSessionState
  simp only [Mut_exec_outgoingFromSessionState_rootKey]
  rcases Mut.exec OutgoingTripleRatchet.fromSessionState s with ⟨r_out, s_out⟩
  cases r_out with
  | error e => rfl
  | ok o =>
    simp only []
    rcases Mut.exec (OutgoingTripleRatchet.encrypt P.C P.codec P.spqr m
      (if s.pendingPreKey then addr else none) r) o with ⟨r_enc, s_enc⟩
    cases r_enc <;> rfl

omit [SampleableType PQC] in
theorem send_setRootKey_eq (P : Params PQ PQC) (rk : Ratchet.RootKey) (g : GhostState PQ)
    (m : List (BitVec 8)) (r : PQC) :
    P.send (setRootKey rk g) m r =
      (setRootKey rk (P.send g m r).1, (P.send g m r).2) := by
  unfold Params.send setRootKey
  simp only [messageEncrypt_setRootKey]
  rcases SessionState.messageEncrypt P.C P.codec P.spqr (P.sendAddrs g.party) m r g.session
    with ⟨r_enc, s_enc⟩
  cases r_enc <;> rfl

omit [SampleableType PQC] in
theorem send_preserves_senderChain_ratchetKey (P : Params PQ PQC) (g : GhostState PQ)
    (kp : KeyPair) (ck : LibsignalSession.ChainKey) (m : List (BitVec 8)) (r : PQC)
    (hsc : g.session.senderChain = some ⟨kp, ck⟩) :
    ∃ ck', (P.send g m r).1.session.senderChain = some ⟨kp, ck'⟩ := by
  have hf : (Mut.exec OutgoingTripleRatchet.fromSessionState g.session).2.senderChain =
      g.session.senderChain := by
    unfold OutgoingTripleRatchet.fromSessionState SessionState.version
    simp only [Mut_exec_bind, Mut_exec_get, hsc, Mut_exec_takePqRatchetState
      ]
    by_cases hv : 256 ≤ (if g.session.sessionVersion = 0 then (2 :
        BitVec 32) else g.session.sessionVersion).toNat
    · simp only [hv, ↓reduceIte, Mut_exec_throw, Mut_exec_bind]
    · simp only [hv, ↓reduceIte]
      cases g.session.remoteIdentity <;> rfl
  unfold Params.send SessionState.messageEncrypt SessionState.encryptAddresses
    OutgoingTripleRatchet.applyToSessionState
  rcases h_out : Mut.exec OutgoingTripleRatchet.fromSessionState g.session with ⟨r_out, s_out⟩
  rw [h_out] at hf
  cases r_out with
  | error _ => exact ⟨ck, hsc⟩
  | ok o =>
    dsimp only []
    rcases Mut.exec (OutgoingTripleRatchet.encrypt P.C P.codec P.spqr m
      (if g.session.pendingPreKey then P.sendAddrs g.party else none) r) o with ⟨r_enc, s_enc⟩
    cases r_enc with
    | error _ => exact ⟨ck, hsc⟩
    | ok msg =>
      dsimp only []
      rw [hf, hsc]
      exact ⟨s_enc.senderChainKey, rfl⟩

theorem receive_setRootKey_of_findIdx_some (P : Params PQ PQC) (rk : Ratchet.RootKey)
    (g : GhostState PQ) (c : List (BitVec 8)) (rc : BitVec 256) (msg : SignalMessage) (idx : ℕ)
    (htry : SignalMessage.tryFrom P.codec c = .ok msg)
    (hidx : g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey) =
        some idx) :
    P.receive (setRootKey rk g) c rc =
      (P.receive g c rc).map (fun x => (setRootKey rk x.1, x.2)) ∧
    ∀ g' t' i' m', P.receive g c rc = some (g', t', i', m') →
      g'.session.senderChain = g.session.senderChain ∧
      g'.epoch = g.epoch ∧
      t' = g.chainEpochs.getD idx 0 := by
  set sess_rk : SessionState PQ := { g.session with rootKey := rk }
  have hset_sess : (setRootKey rk g).session = sess_rk := rfl
  have hset_party : (setRootKey rk g).party = g.party := rfl
  have hset_ep : (setRootKey rk g).epoch = g.epoch := rfl
  have hset_ce : (setRootKey rk g).chainEpochs = g.chainEpochs := rfl
  unfold Params.receive
  rw [htry, hset_party, hset_sess, hset_ep, hset_ce]
  dsimp only []
  have hdec1 := tryDecryptFromRecord_eq P.C P.spqr (P.expectedAddrs g.party) msg .whisper rc sess_rk
  have hdec2 :=
      tryDecryptFromRecord_eq P.C P.spqr (P.expectedAddrs g.party) msg .whisper rc g.session
  have hver : sess_rk.version = g.session.version := rfl
  have hrem : sess_rk.remoteIdentity = g.session.remoteIdentity := rfl
  rw [hver, hrem] at hdec1
  by_cases hv : g.session.version.toNat = msg.messageVersion.toNat
  · simp only [ne_eq, hv, not_true_eq_false, ↓reduceIte] at hdec1 hdec2
    cases hrem_opt : g.session.remoteIdentity with
    | none =>
      rw [hrem_opt] at hdec1 hdec2
      rw [hdec1, hdec2]; simp
    | some rem =>
      rw [hrem_opt] at hdec1 hdec2
      dsimp only [] at hdec1 hdec2
      set r0 : RatchetState :=
        ⟨g.session.rootKey, g.session.senderChain, g.session.receiverChains,
         g.session.previousCounter, maxForwardJumps⟩
      have hr1 : (⟨sess_rk.rootKey, sess_rk.senderChain, sess_rk.receiverChains,
          sess_rk.previousCounter, maxForwardJumps⟩ : RatchetState) =
        { r0 with rootKey := rk } := rfl
      rw [hr1] at hdec1
      have hrat : Mut.exec (ratchetDecryptStep P.C msg.senderRatchetKey msg.counter .whisper rc)
          { r0 with rootKey := rk } =
          ( (Mut.exec (ratchetDecryptStep P.C msg.senderRatchetKey msg.counter .whisper rc) r0).1,
            { (Mut.exec (ratchetDecryptStep P.C msg.senderRatchetKey msg.counter .whisper rc) r0).2
              with rootKey := rk } ) ∧
          (Mut.exec (ratchetDecryptStep P.C msg.senderRatchetKey msg.counter .whisper rc)
              r0).2.senderChain =
            g.session.senderChain := by
        unfold ratchetDecryptStep RatchetState.ensureReceiverChain RatchetState.findReceiverChainKey
          RatchetState.findReceiverChainIndex
        dsimp only [r0]
        simp only [Mut_exec_bind, Mut_exec_get, Mut_exec_liftE, hidx]
        cases g.session.receiverChains[idx]? with
        | none => simp []
        | some ch =>
          dsimp only []
          cases ch.chainKey with
          | none => simp []
          | some ck =>
            simp only [Mut_exec_pure]
            have hws : { r0 with rootKey := rk } =
                CryptoGames.LibsignalSM.Proofs.Refinement.withSender r0 rk r0.senderChain := rfl
            rw [hws, CryptoGames.LibsignalSM.Proofs.Refinement.exec_consumeMessageKey_withSender]
            have hsc_cmk : (Mut.exec (RatchetState.consumeMessageKey P.C.F msg.senderRatchetKey ck
                msg.counter .whisper) r0).2.senderChain = r0.senderChain := by
              have hself :=
                  CryptoGames.LibsignalSM.Proofs.Refinement.exec_consumeMessageKey_withSender
                P.C.F msg.senderRatchetKey ck msg.counter .whisper r0 r0.rootKey r0.senderChain
              have hr0 :
                  CryptoGames.LibsignalSM.Proofs.Refinement.withSender r0 r0.rootKey r0.senderChain
                  = r0 :=
                CryptoGames.LibsignalSM.Proofs.Refinement.withSender_self r0
              rw [hr0] at hself
              have h2 := congrArg Prod.snd hself
              dsimp only [CryptoGames.LibsignalSM.Proofs.Refinement.withSender] at h2
              rw [h2]
            rcases hcmk : Mut.exec (RatchetState.consumeMessageKey P.C.F msg.senderRatchetKey ck
              msg.counter .whisper) r0 with ⟨r_cmk, s_cmk⟩
            rw [hcmk] at hsc_cmk
            dsimp only [] at hsc_cmk
            refine ⟨?_, hsc_cmk⟩
            dsimp only [CryptoGames.LibsignalSM.Proofs.Refinement.withSender]
            rw [hsc_cmk]
      rcases h_r0 :
          Mut.exec (ratchetDecryptStep P.C msg.senderRatchetKey msg.counter .whisper rc) r0
        with ⟨r_res, r_out⟩
      have hrat1 := hrat.1
      have hrat2 := hrat.2
      rw [h_r0] at hrat1 hrat2 hdec2
      dsimp only [] at hrat1 hrat2
      rw [hrat1] at hdec1
      cases r_res with
      | error _ =>
        rw [hdec1, hdec2]; simp
      | ok gen =>
        dsimp only [] at hdec1 hdec2
        have hpost : postRatchetDecrypt P.C P.spqr (P.expectedAddrs g.party) msg .whisper
            sess_rk rem gen { r_out with rootKey := rk } =
          ( (postRatchetDecrypt P.C P.spqr (P.expectedAddrs g.party) msg .whisper
              g.session rem gen r_out).1,
            { (postRatchetDecrypt P.C P.spqr (P.expectedAddrs g.party) msg .whisper
                g.session rem gen r_out).2 with rootKey := rk } ) ∧
          ∀ m s_p, postRatchetDecrypt P.C P.spqr (P.expectedAddrs g.party) msg .whisper
              g.session rem gen r_out = (.ok m, s_p) →
            s_p.senderChain = r_out.senderChain := by
          unfold postRatchetDecrypt
          dsimp only [sess_rk]
          cases hpan : P.spqr.recvPanics g.session.pqRatchetState msg.pqRatchet
          case true => exact ⟨rfl, fun _ _ h => by simp at h⟩
          simp only [Bool.false_eq_true, ↓reduceIte]
          cases P.spqr.recv g.session.pqRatchetState msg.pqRatchet with
          | error b => cases b <;> exact ⟨rfl, fun _ _ h => by simp at h⟩
          | ok ps =>
            dsimp only []
            split
            · exact ⟨rfl, fun _ _ h => by simp at h⟩
            · cases aesCbcDecrypt P.C.D ((gen.generateKeys P.C.F ps.2).cipherKey)
                ((gen.generateKeys P.C.F ps.2).iv) msg.ciphertext with
              | none => exact ⟨rfl, fun _ _ h => by simp at h⟩
              | some ptext =>
                refine ⟨rfl, fun m s_p h => ?_⟩
                injection h with _ hs
                subst hs
                rfl
        rcases h_post : postRatchetDecrypt P.C P.spqr (P.expectedAddrs g.party) msg .whisper
          g.session rem gen r_out with ⟨res_p, s_p⟩
        have hpost1 := hpost.1
        rw [h_post] at hpost1 hdec2
        dsimp only [] at hpost1
        rw [hpost1] at hdec1
        cases res_p with
        | error _ =>
          rw [hdec1, hdec2]; simp
        | ok m =>
          have hsc_p : s_p.senderChain = g.session.senderChain :=
            (hpost.2 m s_p h_post).trans hrat2
          rw [hdec1, hdec2, hidx]
          dsimp only [setRootKey]
          refine ⟨rfl, ?_⟩
          intro g' t' i' m' hsome
          injection hsome with htuple
          rcases Prod.mk.inj htuple with ⟨hg', hrest⟩
          rcases Prod.mk.inj hrest with ⟨ht', _⟩
          subst hg' ht'
          exact ⟨hsc_p, rfl, rfl⟩
  · simp only [ne_eq, hv, not_false_eq_true, ↓reduceIte] at hdec1 hdec2
    rw [hdec1, hdec2]; simp

theorem exec_ensureReceiverChain_evict_append (C : Crypto) (r : RatchetState)
    (their : PublicKey) (ck : LibsignalSession.ChainKey) (coins : BitVec 256)
    (hnone : r.receiverChains.findIdx? (fun c => c.senderRatchetKey == their) = none) :
    let r' : RatchetState :=
      { r with receiverChains :=
          RatchetState.evictReceiverChains (r.receiverChains ++ [⟨their, some ck, []⟩]) }
    Mut.exec (RatchetState.ensureReceiverChain C their coins) r' = (.ok ck, r') := by
  intro r'
  set L := List.drop ((r.receiverChains.length + 1) - 5) r.receiverChains
  have hevict : r'.receiverChains = L ++ [⟨their, some ck, []⟩] :=
    CryptoGames.LibsignalSM.Proofs.Refinement.evictReceiverChains_append_singleton
      r.receiverChains ⟨their, some ck, []⟩
  have hL_none : L.findIdx? (fun (c : ReceiverChain) => c.senderRatchetKey == their) = none :=
    CryptoGames.LibsignalSM.Proofs.Refinement.findIdx_drop_none_of_none
      r.receiverChains (fun (c : ReceiverChain) => c.senderRatchetKey == their) _ hnone
  have hfind : r'.findReceiverChainIndex their = some L.length := by
    unfold RatchetState.findReceiverChainIndex
    rw [hevict]
    exact CryptoGames.LibsignalSM.Proofs.Refinement.findIdx_append_singleton_of_none
      L ⟨their, some ck, []⟩ (fun (c : ReceiverChain) => c.senderRatchetKey == their)
      hL_none (beq_self_eq_true their)
  have hget : r'.receiverChains[L.length]? = some ⟨their, some ck, []⟩ := by
    rw [hevict, List.getElem?_append_right (Nat.le_refl L.length), Nat.sub_self]
    rfl
  unfold RatchetState.ensureReceiverChain RatchetState.findReceiverChainKey
  simp [Mut_exec_bind, Mut_exec_get, hfind, hget, Mut_exec_liftE, Mut_exec_pure]

theorem tryDecryptFromRecord_stepped_error_of_testSpk_false (P : Params Bytes PQC)
    (g : GhostState Bytes) (c : Bytes) (msg : SignalMessage) (rc : BitVec 256)
    (prev : BitVec 32) (rk2 : Ratchet.RootKey) (ckR : BitVec 256) (sc' : Option SenderChain)
    (hparty : g.party = .A)
    (hrem : g.session.remoteIdentity = some P.idB)
    (hloc : g.session.localIdentity = P.idA)
    (htry : SignalMessage.tryFrom P.codec c = .ok msg)
    (hnone : g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey) = none)
    (htest : testSpk P g.session.pqRatchetState c ckR = false) :
    let sess' : SessionState Bytes :=
      { g.session with
        previousCounter := prev
        rootKey := rk2
        receiverChains := RatchetState.evictReceiverChains
          (g.session.receiverChains ++ [⟨msg.senderRatchetKey, some ⟨ckR, 0⟩, []⟩])
        senderChain := sc' }
    ∃ e s_out,
      SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper rc sess' =
        (.error e, s_out) := by
  intro sess'
  rw [hparty]
  rcases hdec : SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs .A)
    msg .whisper rc sess' with ⟨r_dec, s_out⟩
  cases r_dec with
  | error e => exact ⟨e, s_out, rfl⟩
  | ok m =>
    exfalso
    unfold SessionState.tryDecryptFromRecord at hdec
    split at hdec
    · simp at hdec
    · unfold SessionState.tryDecryptWithState at hdec
      have hrem' : sess'.remoteIdentity = some P.idB := hrem
      have hloc' : sess'.localIdentity = P.idA := hloc
      simp only [Mut_exec_bind, Mut_exec_fromSessionState, hrem', hloc',
        Mut_exec_liftE] at hdec
      unfold TripleRatchet.decrypt at hdec
      set r_stepped : RatchetState :=
        ⟨rk2, sc',
         RatchetState.evictReceiverChains
           (g.session.receiverChains ++ [⟨msg.senderRatchetKey, some ⟨ckR, 0⟩, []⟩]),
         prev, maxForwardJumps⟩
      have hens : Mut.exec (RatchetState.ensureReceiverChain P.C msg.senderRatchetKey rc)
          r_stepped = (.ok ⟨ckR, 0⟩, r_stepped) :=
        exec_ensureReceiverChain_evict_append P.C
          ⟨rk2, sc', g.session.receiverChains, prev, maxForwardJumps⟩
          msg.senderRatchetKey ⟨ckR, 0⟩ rc hnone
      have hr_eq : (⟨sess'.rootKey, sess'.senderChain, sess'.receiverChains,
          sess'.previousCounter, maxForwardJumps⟩ : RatchetState) = r_stepped := rfl
      simp only [Mut_exec_bind, Mut_exec_onRatchet, hens] at hdec
      rcases hcmk : Mut.exec (RatchetState.consumeMessageKey P.C.F
        msg.senderRatchetKey ⟨ckR, 0⟩ msg.counter .whisper) r_stepped with ⟨r_cmk, s_cmk⟩
      rw [hcmk] at hdec
      cases r_cmk with
      | error _ => simp at hdec
      | ok gen =>
        simp only [Mut_exec_get] at hdec
        unfold testSpk at htest
        rw [htry] at htest
        dsimp only [] at htest
        cases hpan : P.spqr.recvPanics sess'.pqRatchetState msg.pqRatchet
        case true => simp [hpan, Mut_exec_throw] at hdec
        simp only [hpan, Bool.false_eq_true, ↓reduceIte] at hdec
        cases hpqr : P.spqr.recv g.session.pqRatchetState msg.pqRatchet with
        | error b =>
          rw [hpqr] at hdec
          cases b <;> simp [Mut_exec_throw] at hdec
        | ok ps =>
          rw [hpqr] at hdec htest
          dsimp only [] at htest
          simp only [Mut_exec_pure, Mut_exec_bind] at hdec
          rcases consumeMessageKey_zero_key P.C.F msg.senderRatchetKey ckR
            msg.counter .whisper _ _ gen hcmk with ⟨ckOut, rfl, hckOut⟩
          by_cases hmac : msg.verifyMacWithAddresses P.C.F (P.expectedAddrs .A)
            P.idB P.idA ((ckOut.messageKeys P.C.F).generateKeys P.C.F ps.2).macKey = true
          · have hsp := verifyMacWithAddresses_implies_spurPred P.C.F
              msg.counter.toNat ps.2 (P.expectedAddrs .A) P.idB P.idA msg ckOut ckR
              hckOut hmac
            change spurPred P.C.F msg.counter.toNat ps.2 (macIds P.idB P.idA)
              (msg.serialized.take (msg.serialized.length - macLength))
              (bytesToWord64LE (msg.serialized.drop (msg.serialized.length - macLength))) ckR = false at htest
            rw [hsp] at htest
            cases htest
          · have hmacF : msg.verifyMacWithAddresses P.C.F (P.expectedAddrs .A)
              P.idB P.idA ((ckOut.messageKeys P.C.F).generateKeys P.C.F ps.2).macKey = false :=
              Bool.eq_false_iff.mpr hmac
            simp [hmacF, Mut_exec_throw] at hdec

/-! ## Lazy-table simulation and `hop2DH` equivalence -/

def lazyStep : QueryImpl (prfSpec Pt (BitVec 256)) (StateT (List (Pt × BitVec 256)) ProbComp) :=
  fun x => do
    let tbl ← get
    match tbl.lookup x with
    | some v => return v
    | none =>
      let v ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      set ((x, v) :: tbl)
      return v

/-- Query implementation for `Hop2Comp Pt` backed by a lazy random-oracle table. -/
def lazyImpl : QueryImpl (unifSpec + prfSpec Pt (BitVec 256))
    (StateT (List (Pt × BitVec 256)) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (List (Pt × BitVec 256)) ProbComp) +
    lazyStep (Pt := Pt)

omit [Zero Pt] [SampleableType Pt] in
@[local simp]
theorem simulateQ_lazyImpl_evalQuery (x : Pt) :
    simulateQ (lazyImpl (Pt := Pt)) (evalQuery (Input := Pt) (Tag := BitVec 256) x) =
        lazyStep x := by
  simp [evalQuery, lazyImpl]

omit [Zero Pt] [SampleableType Pt] in
@[local simp]
theorem simulateQ_lazyImpl_hop2Unif :
    simulateQ (lazyImpl (Pt := Pt)) (hop2Unif (Pt := Pt)) =
      (StateT.lift ($ᵗ BitVec 256 : ProbComp (BitVec 256)) :
        StateT (List (Pt × BitVec 256)) ProbComp (BitVec 256)) := by
  simp [hop2Unif, lazyImpl, QueryImpl.simulateQ_add_liftM_left]
  rfl

omit [Zero Pt] [SampleableType Pt] in
theorem simulateQ_prfOracleImpl_true_run {Key α : Type}
    (mac : MACScheme Key Pt (BitVec 256)) (key : Key)
    (comp : Hop2Comp Pt α) (tbl : List (Pt × BitVec 256)) :
    (simulateQ (prfOracleImpl mac) comp).run ⟨key, true, tbl⟩ =
      (fun r => (r.1, ⟨key, true, r.2⟩)) <$> (simulateQ lazyImpl comp).run tbl := by
  induction comp using OracleComp.inductionOn generalizing tbl with
  | pure a =>
    simp [StateT.run_pure]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, map_bind]
    cases t with
    | inl u =>
      simp only [prfOracleImpl, lazyImpl, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
        QueryImpl.ofLift_apply, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
      refine bind_congr fun a => ih a tbl
    | inr x =>
      simp only [prfOracleImpl, lazyImpl, QueryImpl.add_apply_inr,
        MACScheme.prfEval, lazyStep, StateT.run_bind, StateT.run_get, pure_bind, ↓reduceIte]
      cases tbl.lookup x with
      | some v =>
        simp only [StateT.run_pure, pure_bind]
        exact ih v tbl
      | none =>
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
          StateT.run_pure, bind_assoc, pure_bind]
        refine bind_congr fun v => ih v ((x, v) :: tbl)

omit [Zero Pt] [SampleableType Pt] in
theorem simulateQ_prfOracleImpl_true_run' {Key α : Type}
    (mac : MACScheme Key Pt (BitVec 256)) (key : Key)
    (comp : Hop2Comp Pt α) (tbl : List (Pt × BitVec 256)) :
    (simulateQ (prfOracleImpl mac) comp).run' ⟨key, true, tbl⟩ =
      (simulateQ lazyImpl comp).run' tbl := by
  rw [StateT.run'_eq, StateT.run'_eq, simulateQ_prfOracleImpl_true_run, Functor.map_map]

omit [Zero Pt] [SampleableType Pt] in
theorem evalDist_branch_true_eq_lazyImpl {Key : Type} [SampleableType Key]
    (mac : MACScheme Key Pt (BitVec 256)) (comp : Hop2Comp Pt Bool) :
    𝒟[mac.branch true comp] = 𝒟[(simulateQ lazyImpl comp).run' []] := by
  unfold MACScheme.branch
  have h : ∀ k : Key,
      (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (PRFState Key Pt (BitVec 256)) ProbComp) + mac.prfEval) comp).run'
        { key := k, b := true } =
      (simulateQ lazyImpl comp).run' [] :=
    fun k => simulateQ_prfOracleImpl_true_run' mac k comp []
  simp only [h, OracleComp.evalDist_bind_const]

/-- Two association lists are lookup-equivalent if they agree on `List.lookup` at every key. -/
def LookupEq {κ ν : Type} [BEq κ] (l₁ l₂ : List (κ × ν)) : Prop :=
  ∀ x, l₁.lookup x = l₂.lookup x

theorem LookupEq.cons {κ ν : Type} [BEq κ] {l₁ l₂ : List (κ × ν)}
    (h : LookupEq l₁ l₂) (k : κ) (v : ν) :
    LookupEq ((k, v) :: l₁) ((k, v) :: l₂) := by
  intro x
  simp only [List.lookup]
  rw [h x]

theorem LookupEq.swap_cons {κ ν : Type} [BEq κ] [LawfulBEq κ] (k₁ k₂ : κ) (v₁ v₂ : ν)
    (l : List (κ × ν)) (hne : k₁ ≠ k₂) :
    LookupEq ((k₁, v₁) :: (k₂, v₂) :: l) ((k₂, v₂) :: (k₁, v₁) :: l) := by
  intro x
  simp only [List.lookup]
  by_cases h1 : (x == k₁) = true
  · have h1' : x = k₁ := eq_of_beq h1
    subst h1'
    have h2 : (x == k₂) = false := beq_eq_false_iff_ne.mpr hne
    simp [h2]
  · simp [h1]

omit [Zero Pt] [SampleableType Pt] in
theorem simulateQ_lazyImpl_run'_congr {α : Type}
    (comp : Hop2Comp Pt α) {tbl₁ tbl₂ : List (Pt × BitVec 256)}
    (hlook : LookupEq tbl₁ tbl₂) :
    (simulateQ lazyImpl comp).run' tbl₁ = (simulateQ lazyImpl comp).run' tbl₂ := by
  simp only [StateT.run'_eq, map_eq_bind_pure_comp]
  induction comp using OracleComp.inductionOn generalizing tbl₁ tbl₂ with
  | pure a =>
    simp [StateT.run_pure]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, bind_assoc]
    cases t with
    | inl u =>
      simp only [lazyImpl, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
        QueryImpl.ofLift_apply, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
      refine bind_congr fun a => ih a hlook
    | inr x =>
      simp only [lazyImpl, QueryImpl.add_apply_inr, lazyStep,
        StateT.run_bind, StateT.run_get, pure_bind, hlook x]
      cases tbl₂.lookup x with
      | some v =>
        simp only [StateT.run_pure, pure_bind]
        exact ih v hlook
      | none =>
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
          StateT.run_pure, bind_assoc, pure_bind]
        refine bind_congr fun v => ih v (hlook.cons x v)

omit [Zero Pt] [SampleableType Pt] in
theorem evalDist_lazyImpl_cons_fresh
    (comp : Hop2Comp Pt Bool) (x₀ : Pt) (tbl : List (Pt × BitVec 256))
    (hnone : tbl.lookup x₀ = none) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u =>
      (simulateQ lazyImpl comp).run' ((x₀, u) :: tbl)] =
      𝒟[(simulateQ lazyImpl comp).run' tbl] := by
  induction comp using OracleComp.inductionOn generalizing tbl with
  | pure a =>
    simp [StateT.run'_eq, StateT.run_pure]
  | query_bind t k ih =>
    cases t with
    | inl q_u =>
      have hstep : ∀ t0,
          (simulateQ lazyImpl
            (liftM (OracleSpec.query (spec := unifSpec +
                prfSpec Pt (BitVec 256)) (Sum.inl q_u)) >>= k)).run' t0 =
          ((liftM (OracleSpec.query (spec := unifSpec) q_u) : ProbComp _) >>= fun a =>
            (simulateQ lazyImpl (k a)).run' t0) := by
        intro t0
        simp [StateT.run'_eq, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, lazyImpl, QueryImpl.add_apply_inl,
          StateT.run_bind,
          StateT.run_monadLift, monadLift_self, map_eq_bind_pure_comp, bind_assoc]
      simp only [hstep]
      rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256)
        (liftM (OracleSpec.query (spec := unifSpec) q_u))]
      refine evalDist_bind_congr (liftM (OracleSpec.query (spec := unifSpec) q_u)) _ _ fun a =>
        ih a tbl hnone
    | inr x =>
      by_cases hx : x = x₀
      · subst hx
        have h1 : ∀ u,
            (simulateQ lazyImpl
              (liftM (OracleSpec.query (spec := unifSpec +
                  prfSpec Pt (BitVec 256)) (Sum.inr x)) >>= k)).run'
              ((x, u) :: tbl) =
            (simulateQ lazyImpl (k u)).run' ((x, u) :: tbl) := by
          intro u
          simp [StateT.run'_eq, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
            OracleQuery.cont_query, id_map, lazyImpl, QueryImpl.add_apply_inr,
            lazyStep, StateT.run_bind, StateT.run_get, StateT.run_pure]
        have h2 :
            (simulateQ lazyImpl
              (liftM (OracleSpec.query (spec := unifSpec +
                  prfSpec Pt (BitVec 256)) (Sum.inr x)) >>= k)).run' tbl =
            (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u =>
              (simulateQ lazyImpl (k u)).run' ((x, u) :: tbl)) := by
          simp [StateT.run'_eq, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
            OracleQuery.cont_query, lazyImpl, QueryImpl.add_apply_inr,
            lazyStep, StateT.run_bind, StateT.run_get, hnone, StateT.run_monadLift, monadLift_self,
            StateT.run_set, StateT.run_pure, map_eq_bind_pure_comp, bind_assoc]
        simp only [h1, h2]
      · have hbeq : (x == x₀) = false := beq_eq_false_iff_ne.mpr hx
        have hbeq' : (x₀ == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm hx)
        cases hlook : tbl.lookup x with
        | some v =>
          have h1 : ∀ u,
              (simulateQ lazyImpl
                (liftM (OracleSpec.query (spec := unifSpec +
                    prfSpec Pt (BitVec 256)) (Sum.inr x)) >>= k)).run'
                ((x₀, u) :: tbl) =
              (simulateQ lazyImpl (k v)).run' ((x₀, u) :: tbl) := by
            intro u
            simp [StateT.run'_eq, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
              OracleQuery.cont_query, id_map, lazyImpl, QueryImpl.add_apply_inr,
              lazyStep, StateT.run_bind, StateT.run_get, List.lookup, hbeq, hlook, StateT.run_pure]
          have h2 :
              (simulateQ lazyImpl
                (liftM (OracleSpec.query (spec := unifSpec +
                    prfSpec Pt (BitVec 256)) (Sum.inr x)) >>= k)).run' tbl =
              (simulateQ lazyImpl (k v)).run' tbl := by
            simp [StateT.run'_eq, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
              OracleQuery.cont_query, id_map, lazyImpl, QueryImpl.add_apply_inr,
              lazyStep, StateT.run_bind, StateT.run_get, hlook, StateT.run_pure]
          simp only [h1, h2]
          exact ih v tbl hnone
        | none =>
          have h1 : ∀ u,
              (simulateQ lazyImpl
                (liftM (OracleSpec.query (spec := unifSpec +
                    prfSpec Pt (BitVec 256)) (Sum.inr x)) >>= k)).run'
                ((x₀, u) :: tbl) =
              (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun v =>
                (simulateQ lazyImpl (k v)).run' ((x₀, u) :: (x, v) :: tbl)) := by
            intro u
            simp only [StateT.run'_eq, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
              OracleQuery.cont_query, lazyImpl, QueryImpl.add_apply_inr,
              lazyStep, StateT.run_bind, StateT.run_get, List.lookup, hbeq, hlook, pure_bind,
              StateT.run_monadLift, monadLift_self, StateT.run_set, StateT.run_pure,
              Function.comp_apply, id_eq, map_eq_bind_pure_comp, bind_assoc]
            refine bind_congr fun v => ?_
            have hc := simulateQ_lazyImpl_run'_congr (k v) (LookupEq.swap_cons x x₀ v u tbl hx)
            simpa only [StateT.run'_eq, map_eq_bind_pure_comp, lazyImpl] using hc
          have h2 :
              (simulateQ lazyImpl
                (liftM (OracleSpec.query (spec := unifSpec +
                    prfSpec Pt (BitVec 256)) (Sum.inr x)) >>= k)).run' tbl =
              (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun v =>
                (simulateQ lazyImpl (k v)).run' ((x, v) :: tbl)) := by
            simp [StateT.run'_eq, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
              OracleQuery.cont_query, lazyImpl, QueryImpl.add_apply_inr,
              lazyStep, StateT.run_bind, StateT.run_get, hlook, StateT.run_monadLift,
                  monadLift_self,
              StateT.run_set, StateT.run_pure, map_eq_bind_pure_comp, bind_assoc]
          simp only [h1, h2]
          rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]
          refine evalDist_bind_congr ($ᵗ BitVec 256) _ _ fun v => ?_
          exact ih v ((x, v) :: tbl) (by simp [List.lookup, hbeq', hnone])

omit [Zero Pt] [SampleableType Pt] in
theorem evalDist_lazyStep_discard
    (x₀ : Pt) (comp : Hop2Comp Pt Bool) (tbl : List (Pt × BitVec 256)) :
    𝒟[(do let _ ← lazyStep x₀; simulateQ lazyImpl comp).run' tbl] =
      𝒟[(simulateQ lazyImpl comp).run' tbl] := by
  have hrun : (do let _ ← lazyStep x₀; simulateQ lazyImpl comp).run' tbl =
      match tbl.lookup x₀ with
      | some _ => (simulateQ lazyImpl comp).run' tbl
      | none => ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u =>
          (simulateQ lazyImpl comp).run' ((x₀, u) :: tbl) := by
    unfold lazyStep
    simp only [StateT.run'_eq, StateT.run_bind, StateT.run_get, pure_bind, map_eq_bind_pure_comp]
    cases tbl.lookup x₀ <;>
      simp [StateT.run_pure, StateT.run_monadLift, monadLift_self, StateT.run_set, bind_assoc]
  rw [hrun]
  cases hlook : tbl.lookup x₀ with
  | some _ => rfl
  | none => exact evalDist_lazyImpl_cons_fresh comp x₀ tbl hlook

/-- Base session state after the receiving half of `hop2DH`. -/
def steppedSessBase (g : GhostState PQ) (msg : SignalMessage) (prev : BitVec 32)
    (ckR : BitVec 256) : SessionState PQ :=
  { g.session with
    previousCounter := prev
    rootKey := 0
    receiverChains := RatchetState.evictReceiverChains
      (g.session.receiverChains ++ [⟨msg.senderRatchetKey, some ⟨ckR, 0⟩, []⟩])
    senderChain := none }

theorem tryDecryptFromRecord_steppedSess (P : Params PQ PQC)
    (g : GhostState PQ) (msg : SignalMessage) (rc : BitVec 256)
    (prev : BitVec 32) (rk2 : Ratchet.RootKey) (ckR : BitVec 256) (sc' : Option SenderChain)
    (hnone : g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey) =
        none) :
    let base := steppedSessBase g msg prev ckR
    SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper rc
      { base with rootKey := rk2, senderChain := sc' } =
    ( (SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper rc
        base).1,
      { (SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper rc
          base).2
        with rootKey := rk2, senderChain := sc' } ) := by
  intro base
  set sess1 : SessionState PQ := { base with rootKey := rk2, senderChain := sc' }
  have hdec1 := tryDecryptFromRecord_eq P.C P.spqr (P.expectedAddrs g.party) msg .whisper rc sess1
  have hdec2 := tryDecryptFromRecord_eq P.C P.spqr (P.expectedAddrs g.party) msg .whisper rc base
  have hver : sess1.version = base.version := rfl
  have hrem : sess1.remoteIdentity = base.remoteIdentity := rfl
  rw [hver, hrem] at hdec1
  by_cases hv : base.version.toNat = msg.messageVersion.toNat
  · simp only [ne_eq, hv, not_true_eq_false, ↓reduceIte] at hdec1 hdec2
    cases hrem_opt : base.remoteIdentity with
    | none =>
      rw [hrem_opt] at hdec1 hdec2
      rw [hdec1, hdec2]
    | some rem =>
      rw [hrem_opt] at hdec1 hdec2
      dsimp only [] at hdec1 hdec2
      set r0 : RatchetState :=
        ⟨0, none, base.receiverChains, prev, maxForwardJumps⟩
      have hr1 : (⟨sess1.rootKey, sess1.senderChain, sess1.receiverChains,
          sess1.previousCounter, maxForwardJumps⟩ : RatchetState) =
        CryptoGames.LibsignalSM.Proofs.Refinement.withSender r0 rk2 sc' := rfl
      have hr0 : (⟨base.rootKey, base.senderChain, base.receiverChains,
          base.previousCounter, maxForwardJumps⟩ : RatchetState) = r0 := rfl
      rw [hr1] at hdec1
      rw [hr0] at hdec2
      have hens1 : Mut.exec (RatchetState.ensureReceiverChain P.C msg.senderRatchetKey rc)
          (CryptoGames.LibsignalSM.Proofs.Refinement.withSender r0 rk2 sc') =
          (.ok ⟨ckR, 0⟩, CryptoGames.LibsignalSM.Proofs.Refinement.withSender r0 rk2 sc') :=
        exec_ensureReceiverChain_evict_append P.C
          ⟨rk2, sc', g.session.receiverChains, prev, maxForwardJumps⟩
          msg.senderRatchetKey ⟨ckR, 0⟩ rc hnone
      have hens0 : Mut.exec (RatchetState.ensureReceiverChain P.C msg.senderRatchetKey rc) r0 =
          (.ok ⟨ckR, 0⟩, r0) :=
        exec_ensureReceiverChain_evict_append P.C
          ⟨0, none, g.session.receiverChains, prev, maxForwardJumps⟩
          msg.senderRatchetKey ⟨ckR, 0⟩ rc hnone
      have hrat : Mut.exec (ratchetDecryptStep P.C msg.senderRatchetKey msg.counter .whisper rc)
          (CryptoGames.LibsignalSM.Proofs.Refinement.withSender r0 rk2 sc') =
          ( (Mut.exec (ratchetDecryptStep P.C msg.senderRatchetKey msg.counter .whisper rc) r0).1,
            CryptoGames.LibsignalSM.Proofs.Refinement.withSender
              (Mut.exec (ratchetDecryptStep P.C msg.senderRatchetKey msg.counter .whisper rc) r0).2
              rk2 sc' ) := by
        unfold ratchetDecryptStep
        rw [Mut_exec_bind, Mut_exec_bind, hens1, hens0]
        dsimp only []
        exact CryptoGames.LibsignalSM.Proofs.Refinement.exec_consumeMessageKey_withSender
          P.C.F msg.senderRatchetKey ⟨ckR, 0⟩ msg.counter .whisper r0 rk2 sc'
      rcases h_r0 :
          Mut.exec (ratchetDecryptStep P.C msg.senderRatchetKey msg.counter .whisper rc) r0
        with ⟨r_res, r_out⟩
      rw [h_r0] at hrat hdec2
      dsimp only [] at hrat
      rw [hrat] at hdec1
      cases r_res with
      | error _ =>
        rw [hdec1, hdec2]
      | ok gen =>
        dsimp only [] at hdec1 hdec2
        rw [hdec1, hdec2]
        unfold postRatchetDecrypt
        dsimp only [sess1, base, steppedSessBase,
          CryptoGames.LibsignalSM.Proofs.Refinement.withSender]
        by_cases hpan : P.spqr.recvPanics g.session.pqRatchetState msg.pqRatchet = true
        · simp only [hpan, ite_true]
        simp only [hpan, Bool.false_eq_true, ↓reduceIte]
        cases P.spqr.recv g.session.pqRatchetState msg.pqRatchet with
        | error b => cases b <;> rfl
        | ok ps =>
          rcases ps with ⟨newPqr, pqrKey⟩
          dsimp only []
          by_cases hmac : (!SignalMessage.verifyMacWithAddresses P.C.F msg
            (P.expectedAddrs g.party) rem g.session.localIdentity
            (gen.generateKeys P.C.F pqrKey).macKey) = true
          · simp only [hmac, ↓reduceIte]
          · simp only [hmac, Bool.false_eq_true, ↓reduceIte]
            cases haes : aesCbcDecrypt P.C.D ((gen.generateKeys P.C.F pqrKey).cipherKey)
              ((gen.generateKeys P.C.F pqrKey).iv) msg.ciphertext <;> simp only []
  · simp only [ne_eq, hv, not_false_eq_true, ↓reduceIte] at hdec1 hdec2
    rw [hdec1, hdec2]

def patchPartyIdx (m : ℕ) (rk : Ratchet.RootKey) (idx : Option ℕ) (g : GhostState PQ) :
    GhostState PQ :=
  if idx = some m then setRootKey rk g else g

omit [Inhabited PQ] in
@[simp]
theorem patchPartyIdx_some_self (m : ℕ) (rk : Ratchet.RootKey) (g : GhostState PQ) :
    patchPartyIdx m rk (some m) g = setRootKey rk g := by
  simp [patchPartyIdx]

omit [Inhabited PQ] in
@[simp]
theorem patchPartyIdx_none (m : ℕ) (rk : Ratchet.RootKey) (g : GhostState PQ) :
    patchPartyIdx m rk none g = g := by
  simp [patchPartyIdx]

omit [Inhabited PQ] in
theorem patchPartyIdx_of_ne (m : ℕ) (rk : Ratchet.RootKey) (idx : Option ℕ) (g : GhostState PQ)
    (hne : idx ≠ some m) :
    patchPartyIdx m rk idx g = g := by
  simp [patchPartyIdx, hne]

omit [SampleableType PQC] in
@[simp]
theorem send_patchPartyIdx_eq (P : Params PQ PQC) (m : ℕ) (rk : Ratchet.RootKey)
    (idx : Option ℕ) (g : GhostState PQ) (msg : List (BitVec 8)) (r : PQC) :
    P.send (patchPartyIdx m rk idx g) msg r =
      (patchPartyIdx m rk idx (P.send g msg r).1, (P.send g msg r).2) := by
  unfold patchPartyIdx
  split
  · exact send_setRootKey_eq P rk g msg r
  · rfl

theorem tryDecryptFromRecord_setRootKey_cc1_err (P : Params Bytes PQC)
    (g : GhostState Bytes) (msg : SignalMessage) (rc : BitVec 256)
    (rk : Ratchet.RootKey) (sc : SenderChain) (e : SignalProtocolError)
    (hnone : g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey) = none)
    (hsc : g.session.senderChain = some sc)
    (hcc1 : rootCreateChain P.C rk msg.senderRatchetKey sc.ratchetKey.privateKey = .error e) :
    ∃ e', (SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
      msg .whisper rc (setRootKey rk g).session).1 = .error e' := by
  have hdec := tryDecryptFromRecord_eq P.C P.spqr (P.expectedAddrs g.party)
    msg .whisper rc (setRootKey rk g).session
  split_ifs at hdec with hv
  · exact ⟨_, congrArg Prod.fst hdec⟩
  · cases hrem : (setRootKey rk g).session.remoteIdentity with
    | none => rw [hrem] at hdec; exact ⟨_, congrArg Prod.fst hdec⟩
    | some rem =>
      rw [hrem] at hdec
      dsimp only [] at hdec
      have hrat : (Mut.exec (ratchetDecryptStep P.C msg.senderRatchetKey msg.counter .whisper rc)
          ⟨(setRootKey rk g).session.rootKey, (setRootKey rk g).session.senderChain,
           (setRootKey rk g).session.receiverChains,
           (setRootKey rk g).session.previousCounter, maxForwardJumps⟩).1 = .error e := by
        unfold setRootKey ratchetDecryptStep RatchetState.ensureReceiverChain
          RatchetState.findReceiverChainKey RatchetState.findReceiverChainIndex
          RatchetState.dhRatchetStep
        simp [Mut_exec_bind, Mut_exec_get, Mut_exec_liftE, Mut_exec_takeRootKey,
          hnone, hsc, hcc1]
      rcases h_r : Mut.exec (ratchetDecryptStep P.C msg.senderRatchetKey msg.counter .whisper rc)
        ⟨(setRootKey rk g).session.rootKey, (setRootKey rk g).session.senderChain,
         (setRootKey rk g).session.receiverChains,
         (setRootKey rk g).session.previousCounter, maxForwardJumps⟩ with ⟨r_res, r_out⟩
      rw [h_r] at hrat hdec
      dsimp only [] at hrat
      subst hrat
      exact ⟨_, congrArg Prod.fst hdec⟩

theorem tryDecryptFromRecord_setRootKey_cc2_err (P : Params Bytes PQC)
    (g : GhostState Bytes) (msg : SignalMessage) (rc : BitVec 256)
    (rk rk1 ck1 : BitVec 256) (sc : SenderChain) (e : SignalProtocolError)
    (hnone : g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey) = none)
    (hsc : g.session.senderChain = some sc)
    (hcc1 : rootCreateChain P.C rk msg.senderRatchetKey sc.ratchetKey.privateKey = .ok (rk1, ⟨ck1,
        0⟩))
    (hcc2 : rootCreateChain P.C rk1 msg.senderRatchetKey (KeyPair.generate P.C rc).privateKey =
        .error e) :
    ∃ e', (SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
      msg .whisper rc (setRootKey rk g).session).1 = .error e' := by
  have hdec := tryDecryptFromRecord_eq P.C P.spqr (P.expectedAddrs g.party)
    msg .whisper rc (setRootKey rk g).session
  split_ifs at hdec with hv
  · exact ⟨_, congrArg Prod.fst hdec⟩
  · cases hrem : (setRootKey rk g).session.remoteIdentity with
    | none => rw [hrem] at hdec; exact ⟨_, congrArg Prod.fst hdec⟩
    | some rem =>
      rw [hrem] at hdec
      dsimp only [] at hdec
      have hrat : (Mut.exec (ratchetDecryptStep P.C msg.senderRatchetKey msg.counter .whisper rc)
          ⟨(setRootKey rk g).session.rootKey, (setRootKey rk g).session.senderChain,
           (setRootKey rk g).session.receiverChains,
           (setRootKey rk g).session.previousCounter, maxForwardJumps⟩).1 = .error e := by
        unfold setRootKey ratchetDecryptStep RatchetState.ensureReceiverChain
          RatchetState.findReceiverChainKey RatchetState.findReceiverChainIndex
          RatchetState.dhRatchetStep
        simp [Mut_exec_bind, Mut_exec_get, Mut_exec_liftE, Mut_exec_takeRootKey,
          hnone, hsc, hcc1, hcc2]
      rcases h_r : Mut.exec (ratchetDecryptStep P.C msg.senderRatchetKey msg.counter .whisper rc)
        ⟨(setRootKey rk g).session.rootKey, (setRootKey rk g).session.senderChain,
         (setRootKey rk g).session.receiverChains,
         (setRootKey rk g).session.previousCounter, maxForwardJumps⟩ with ⟨r_res, r_out⟩
      rw [h_r] at hrat hdec
      dsimp only [] at hrat
      subst hrat
      exact ⟨_, congrArg Prod.fst hdec⟩

theorem tryDecryptFromRecord_setRootKey_ok (P : Params Bytes PQC)
    (g : GhostState Bytes) (msg : SignalMessage) (rc : BitVec 256)
    (rk rk1 ck1 rk2 : BitVec 256) (ck2 : LibsignalSession.ChainKey) (sc : SenderChain)
    (hnone : g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey) = none)
    (hsc : g.session.senderChain = some sc)
    (hcc1 : rootCreateChain P.C rk msg.senderRatchetKey sc.ratchetKey.privateKey = .ok (rk1, ⟨ck1,
        0⟩))
    (hcc2 : rootCreateChain P.C rk1 msg.senderRatchetKey (KeyPair.generate P.C rc).privateKey =
        .ok (rk2, ck2)) :
    let cur := sc.chainKey.index
    let sess' : SessionState Bytes :=
      { g.session with
        previousCounter := if cur = 0 then 0 else cur - 1
        rootKey := rk2
        receiverChains := RatchetState.evictReceiverChains
          (g.session.receiverChains ++ [⟨msg.senderRatchetKey, some ⟨ck1, 0⟩, []⟩])
        senderChain := some ⟨KeyPair.generate P.C rc, ck2⟩ }
    SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper rc sess' =
      match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
          msg .whisper rc (setRootKey rk g).session with
      | (.ok m, s_out) => (.ok m, s_out)
      | (.error err, _) => (.error err, sess') := by
  intro cur sess'
  have hdec1 := tryDecryptFromRecord_eq P.C P.spqr (P.expectedAddrs g.party) msg .whisper rc sess'
  have hdec2 := tryDecryptFromRecord_eq P.C P.spqr (P.expectedAddrs g.party)
    msg .whisper rc (setRootKey rk g).session
  have hver : sess'.version = (setRootKey rk g).session.version := rfl
  have hrem : sess'.remoteIdentity = (setRootKey rk g).session.remoteIdentity := rfl
  rw [hver, hrem] at hdec1
  by_cases hv : (setRootKey rk g).session.version.toNat = msg.messageVersion.toNat
  · simp only [ne_eq, hv, not_true_eq_false, ↓reduceIte] at hdec1 hdec2
    cases hrem_opt : (setRootKey rk g).session.remoteIdentity with
    | none =>
      rw [hrem_opt] at hdec1 hdec2
      rw [hdec1, hdec2]
    | some rem =>
      rw [hrem_opt] at hdec1 hdec2
      dsimp only [] at hdec1 hdec2
      set r_stepped : RatchetState :=
        ⟨sess'.rootKey, sess'.senderChain, sess'.receiverChains,
         sess'.previousCounter, maxForwardJumps⟩
      have hens1 :
          Mut.exec (RatchetState.ensureReceiverChain P.C msg.senderRatchetKey rc) r_stepped =
          (.ok ⟨ck1, 0⟩, r_stepped) :=
        exec_ensureReceiverChain_evict_append P.C
          ⟨rk2, some ⟨KeyPair.generate P.C rc, ck2⟩, g.session.receiverChains,
           sess'.previousCounter, maxForwardJumps⟩
          msg.senderRatchetKey ⟨ck1, 0⟩ rc hnone
      have hens2 : Mut.exec (RatchetState.ensureReceiverChain P.C msg.senderRatchetKey rc)
          ⟨(setRootKey rk g).session.rootKey, (setRootKey rk g).session.senderChain,
           (setRootKey rk g).session.receiverChains,
           (setRootKey rk g).session.previousCounter, maxForwardJumps⟩ =
          (.ok ⟨ck1, 0⟩, r_stepped) := by
        change Mut.exec (RatchetState.ensureReceiverChain P.C msg.senderRatchetKey rc)
          ⟨rk, g.session.senderChain, g.session.receiverChains,
           g.session.previousCounter, maxForwardJumps⟩ = (.ok ⟨ck1, 0⟩, r_stepped)
        unfold RatchetState.ensureReceiverChain RatchetState.findReceiverChainKey
          RatchetState.findReceiverChainIndex RatchetState.dhRatchetStep
        simp only [Mut_exec_bind, Mut_exec_get, Mut_exec_liftE, Mut_exec_takeRootKey,
          Mut_exec_modify, Mut_exec_pure, hnone, hsc, hcc1, hcc2]
        rfl
      have hrat :
          Mut.exec (ratchetDecryptStep P.C msg.senderRatchetKey msg.counter .whisper rc) r_stepped =
          Mut.exec (ratchetDecryptStep P.C msg.senderRatchetKey msg.counter .whisper rc)
            ⟨(setRootKey rk g).session.rootKey, (setRootKey rk g).session.senderChain,
             (setRootKey rk g).session.receiverChains,
             (setRootKey rk g).session.previousCounter, maxForwardJumps⟩ := by
        unfold ratchetDecryptStep
        rw [Mut_exec_bind, Mut_exec_bind, hens1, hens2]
      rw [hrat] at hdec1
      rcases h_r : Mut.exec (ratchetDecryptStep P.C msg.senderRatchetKey msg.counter .whisper rc)
        ⟨(setRootKey rk g).session.rootKey, (setRootKey rk g).session.senderChain,
         (setRootKey rk g).session.receiverChains,
         (setRootKey rk g).session.previousCounter, maxForwardJumps⟩ with ⟨r_res, r_out⟩
      rw [h_r] at hdec1 hdec2
      cases r_res with
      | error _ =>
        rw [hdec1, hdec2]
      | ok gen =>
        dsimp only [] at hdec1 hdec2
        have hpost : postRatchetDecrypt P.C P.spqr (P.expectedAddrs g.party) msg .whisper
            sess' rem gen r_out =
          match postRatchetDecrypt P.C P.spqr (P.expectedAddrs g.party) msg .whisper
              (setRootKey rk g).session rem gen r_out with
          | (.ok m, s_out) => (.ok m, s_out)
          | (.error err, _) => (.error err, sess') := by
          unfold postRatchetDecrypt
          dsimp only [sess', setRootKey]
          by_cases hpan : P.spqr.recvPanics g.session.pqRatchetState msg.pqRatchet = true
          · simp only [hpan, ite_true]
          simp only [hpan, Bool.false_eq_true, ↓reduceIte]
          cases P.spqr.recv g.session.pqRatchetState msg.pqRatchet with
          | error b => cases b <;> rfl
          | ok ps =>
            rcases ps with ⟨newPqr, pqrKey⟩
            dsimp only []
            by_cases hmac : (!SignalMessage.verifyMacWithAddresses P.C.F msg
              (P.expectedAddrs g.party) rem g.session.localIdentity
              (gen.generateKeys P.C.F pqrKey).macKey) = true
            · simp only [hmac, ↓reduceIte]
            · simp only [hmac]
              cases aesCbcDecrypt P.C.D ((gen.generateKeys P.C.F pqrKey).cipherKey)
                ((gen.generateKeys P.C.F pqrKey).iv) msg.ciphertext <;> rfl
        rw [hdec1, hdec2, hpost]
  · simp only [ne_eq, hv, not_false_eq_true, ↓reduceIte] at hdec1 hdec2
    rw [hdec1, hdec2]

/-- Shows `hop2Recv` steps identically to `(sessionSchemeU P ℓ).receive` on `patchPartyIdx m rk`
when the party's index is `none` or strictly above `k`. -/
theorem hop2Recv_patchPartyIdx_eq
    (P : Params Bytes PQC) (hcodec : P.codec = protoSignalCodec)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hz : ∀ x, Dh.dh x 0 = 0)
    (k m : ℕ) (hkm : k < m) (rk : Ratchet.RootKey) (c_chall : BitVec 256)
    (g : GhostState Bytes) (c : Bytes) (rc : BitVec 256)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes × Hop2Aux Pt)
    (horc : ratchetKeyAdmissible protoSignalCodec decT encT c = true)
    (hidx_cases : st.2.idx g.party = none ∨
      (st.2.idx g.party = some m ∧
        ∃ ckS0, g.session.senderChain =
          some ⟨KeyPair.generate P.C (st.2.coins g.party), ckS0⟩)) :
    let h : Hop2Hyb Pt := ⟨k, (rk, c_chall), fun I => pure ((extractPRF P.C.F encPt).tag rk I)⟩
    ∃ opt : Hop2Out Pt ℓ,
      (hop2Recv (ℓ := ℓ) P Dh encT decT h g c rc).run st = pure (opt, st) ∧
      opt.map (fun r =>
        (patchPartyIdx m rk ((hop2Commit st.2 g.party r.2).idx g.party) r.1.1, r.1.2)) =
        (sessionSchemeU P ℓ).receive (patchPartyIdx m rk (st.2.idx g.party) g) c rc ∧
      ∀ r ∈ opt,
        ((hop2Commit st.2 g.party r.2).idx g.party = none ∨
          ((hop2Commit st.2 g.party r.2).idx g.party = some m ∧
            ∃ ckS0, r.1.1.session.senderChain =
              some ⟨KeyPair.generate P.C ((hop2Commit st.2 g.party r.2).coins g.party), ckS0⟩)) ∧
        (∀ Q ≠ g.party, (hop2Commit st.2 g.party r.2).idx Q = st.2.idx Q ∧
          (hop2Commit st.2 g.party r.2).coins Q = st.2.coins Q) ∧
        (hop2Commit st.2 g.party r.2).made = st.2.made ∧
        (hop2Commit st.2 g.party r.2).lazy = st.2.lazy ∧
        (hop2Commit st.2 g.party r.2).bad = st.2.bad := by
  intro h
  rcases hidx_cases with hnone_idx | ⟨hsome_idx, ckS0, hsc⟩
  · refine ⟨((sessionSchemeU P ℓ).receive g c rc).map (fun r => (r, none)), ?_, ?_, ?_⟩
    · unfold hop2Recv
      cases htry : SignalMessage.tryFrom P.codec c with
      | error _ =>
        simp [StateT.run_pure, sessionSchemeU, Params.receive, htry]
      | ok msg =>
        simp [StateT.run_bind, StateT.run_get, hnone_idx, StateT.run_pure]
    · rw [hnone_idx, patchPartyIdx_none]
      cases (sessionSchemeU P ℓ).receive g c rc with
      | none => simp
      | some val =>
        rcases val with ⟨g', t', i', m'⟩
        simp [hop2Commit, hnone_idx]
    · intro r hr
      simp only [Option.mem_def, Option.map_eq_some_iff] at hr
      rcases hr with ⟨x, _, rfl⟩
      simp [hop2Commit, hnone_idx]
  · unfold hop2Recv
    cases htry : SignalMessage.tryFrom P.codec c with
    | error _ =>
      refine ⟨none, by simp [StateT.run_pure], ?_, by simp⟩
      simp [sessionSchemeU, Params.receive, hsome_idx, setRootKey, htry]
    | ok msg =>
      dsimp only []
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hsome_idx]
      cases hfind :
          g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey) with
      | some i =>
        simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
        have hrecv_eq := receive_setRootKey_of_findIdx_some P rk g c rc msg i htry hfind
        refine ⟨((sessionSchemeU P ℓ).receive g c rc).map (fun r => (r, none)), rfl, ?_, ?_⟩
        · simp only [hop2Commit, patchPartyIdx_some_self,
            sessionSchemeU, hrecv_eq.1]
          cases P.receive g c rc with
          | none => simp
          | some val =>
            rcases val with ⟨g', t', i', m'⟩
            simp [hsome_idx, patchPartyIdx_some_self]
        · intro r hr
          simp only [Option.mem_def, Option.map_eq_some_iff, sessionSchemeU] at hr
          rcases hr with ⟨⟨g', t', i', m'⟩, ⟨⟨g0, t0, i0, m0⟩, hrec0, htuple⟩, rfl⟩
          rcases Prod.mk.inj htuple with ⟨rfl, htuple2⟩
          rcases Prod.mk.inj htuple2 with ⟨rfl, htuple3⟩
          rcases Prod.mk.inj htuple3 with ⟨rfl, rfl⟩
          have hsc' := (hrecv_eq.2 g0 t0 i0 m0 hrec0).1
          dsimp only [hop2Commit]
          exact ⟨Or.inr ⟨hsome_idx, ckS0, hsc'.trans hsc⟩,
            fun _ _ => ⟨rfl, rfl⟩, rfl, rfl, rfl⟩
      | none =>
        simp only [Option.isNone_none, ↓reduceIte]
        have hM := CryptoGames.LibsignalSM.Proofs.Refinement.libX25519Rel_model hX
        obtain ⟨T, hdecT, hencT⟩ :=
          CryptoVerification.E2E.SpkHop2.ratchetKeyOnCurve_of_tryFrom decT encT c msg horc (hcodec ▸
              htry)
        have hpub : msg.senderRatchetKey.bytes.toList = encPt T := by
          rw [← hencT]
          exact CryptoGames.LibsignalSM.Proofs.Refinement.encT_bytes_toList hX T
        unfold hop2DH
        rw [hdecT]
        dsimp only []
        by_cases hT0 : T = 0
        · subst hT0
          simp only [true_or, ↓reduceIte, StateT.run_pure]
          have hcc1 : rootCreateChain P.C rk msg.senderRatchetKey
              (KeyPair.generate P.C (st.2.coins g.party)).privateKey =
              .error .invalidKeyAgreement :=
            CryptoGames.LibsignalSM.Proofs.Refinement.rootCreateChain_generate_zero
              P.C hM hz rk (st.2.coins g.party) hpub
          have hcc1' : rootCreateChain P.C rk msg.senderRatchetKey
              ({ ratchetKey := KeyPair.generate P.C (st.2.coins g.party),
                 chainKey := ckS0 } : SenderChain).ratchetKey.privateKey =
              .error .invalidKeyAgreement := hcc1
          obtain ⟨e', herr⟩ := tryDecryptFromRecord_setRootKey_cc1_err P g msg rc rk
            ⟨KeyPair.generate P.C (st.2.coins g.party), ckS0⟩ .invalidKeyAgreement
            hfind hsc hcc1'
          refine ⟨none, rfl, ?_, by simp⟩
          simp only [Option.map_none, patchPartyIdx_some_self,
            sessionSchemeU, Params.receive]
          have hparty_set : (setRootKey rk g).party = g.party := rfl
          rw [htry, hparty_set]
          dsimp only []
          rcases htr : SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
            msg .whisper rc (setRootKey rk g).session with ⟨r_tr, s_tr⟩
          rw [htr] at herr
          change r_tr = .error e' at herr
          subst herr
          rfl
        · have hnot : ¬ (T = 0 ∨ encT T ≠ msg.senderRatchetKey) := by
            rintro (rfl | hne)
            · exact hT0 rfl
            · exact hne hencT
          have hQ0 : Dh.dh (st.2.coins g.party) T ≠ 0 :=
            hM.dh_ne_zero (st.2.coins g.party) T hT0
          have hnot_le : ¬ (m ≤ k) := Nat.not_le.mpr hkm
          have hrecvHalf : (hop2RecvHalf (ℓ := ℓ) P h (some m) g.session.rootKey
              msg.senderRatchetKey
              (KeyPair.generate P.C (st.2.coins g.party)).privateKey
              (Dh.dh (st.2.coins g.party) T)).run st =
              pure (some (none,
                ((rootPRNG P.C.F encPt).up rk (Dh.dh (st.2.coins g.party) T)).1,
                ((rootPRNG P.C.F encPt).up rk (Dh.dh (st.2.coins g.party) T)).2), st) := by
            unfold hop2RecvHalf
            simp [h, hQ0, hnot_le,
              rootExpand_extractPRF_eq_rootPRNG_up]
          have hcc1 : rootCreateChain P.C rk msg.senderRatchetKey
              (KeyPair.generate P.C (st.2.coins g.party)).privateKey =
              .ok (((rootPRNG P.C.F encPt).up rk (Dh.dh (st.2.coins g.party) T)).1,
                ⟨((rootPRNG P.C.F encPt).up rk (Dh.dh (st.2.coins g.party) T)).2, 0⟩) :=
            CryptoGames.LibsignalSM.Proofs.Refinement.rootCreateChain_generate_honest
              P.C hM rk (st.2.coins g.party) hT0 hpub
          simp only [hnot, ↓reduceIte, hsc, StateT.run_bind, hrecvHalf, pure_bind]
          set rk1 := ((rootPRNG P.C.F encPt).up rk (Dh.dh (st.2.coins g.party) T)).1
          set ck1 := ((rootPRNG P.C.F encPt).up rk (Dh.dh (st.2.coins g.party) T)).2
          unfold hop2SendHalf
          dsimp only []
          cases hcc2 : rootCreateChain P.C rk1 msg.senderRatchetKey
            (KeyPair.generate P.C rc).privateKey with
          | error e =>
            simp only [StateT.lift, StateT.run, pure_bind]
            obtain ⟨e', herr⟩ := tryDecryptFromRecord_setRootKey_cc2_err P g msg rc rk rk1 ck1
              ⟨KeyPair.generate P.C (st.2.coins g.party), ckS0⟩ e hfind hsc hcc1 hcc2
            refine ⟨none, rfl, ?_, by simp⟩
            simp only [Option.map_none, patchPartyIdx_some_self,
              sessionSchemeU, Params.receive]
            have hparty_set : (setRootKey rk g).party = g.party := rfl
            rw [htry, hparty_set]
            dsimp only []
            rcases htr : SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
              msg .whisper rc (setRootKey rk g).session with ⟨r_tr, s_tr⟩
            rw [htr] at herr
            change r_tr = .error e' at herr
            subst herr
            rfl
          | ok pair2 =>
            rcases pair2 with ⟨rk2, ck2⟩
            have hck2 : (⟨ck2.key, 0⟩ : LibsignalSession.ChainKey) = ck2 := by
              have hrc2 := CryptoGames.LibsignalSM.Proofs.Refinement.rootCreateChain_generate_honest
                P.C hM rk1 rc hT0 hpub
              rw [hcc2] at hrc2
              injection hrc2 with hpair
              rcases Prod.mk.inj hpair with ⟨_, rfl⟩
              rfl
            simp only [StateT.lift, StateT.run, pure_bind, hck2]
            have hok := tryDecryptFromRecord_setRootKey_ok P g msg rc rk rk1 ck1 rk2 ck2
              ⟨KeyPair.generate P.C (st.2.coins g.party), ckS0⟩ hfind hsc hcc1 hcc2
            dsimp only [] at hok
            rw [hok]
            rcases htr : SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
              msg .whisper rc (setRootKey rk g).session with ⟨r_tr, s_out⟩
            cases r_tr with
            | error err =>
              simp only []
              refine ⟨none, rfl, ?_, by simp⟩
              simp only [Option.map_none, patchPartyIdx_some_self,
                sessionSchemeU, Params.receive]
              have hparty_set : (setRootKey rk g).party = g.party := rfl
              rw [htry]
              dsimp only []
              rw [hparty_set, htr]
              rfl
            | ok m_plain =>
              simp only []
              refine ⟨_, rfl, ?_, ?_⟩
              · simp only [Option.map_some, hop2Commit, Function.update_self, patchPartyIdx_none,
                  patchPartyIdx_some_self, sessionSchemeU, Params.receive]
                have hparty_set : (setRootKey rk g).party = g.party := rfl
                have hrc_set : (setRootKey rk g).session.receiverChains =
                    g.session.receiverChains := rfl
                have hep_set : (setRootKey rk g).epoch = g.epoch := rfl
                have hce_set : (setRootKey rk g).chainEpochs = g.chainEpochs := rfl
                rw [htry]
                dsimp only []
                rw [hparty_set, htr, hrc_set, hfind, hep_set, hce_set]
                simp [Option.map_some, List.length_append]
              · intro r hr
                simp only [Option.mem_def, Option.some.injEq] at hr
                subst hr
                dsimp only [hop2Commit]
                exact ⟨Or.inl (Function.update_self _ _ _),
                  fun Q hQ => ⟨Function.update_of_ne hQ _ _, Function.update_of_ne hQ _ _⟩,
                  rfl, rfl, rfl⟩

end Hop2Coupling
end CryptoVerification.E2E.SpkHop1
