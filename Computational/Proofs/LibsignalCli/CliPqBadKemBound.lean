/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SpecLemmas.Game.StatementPq
public import Computational.Proofs.SignalPqxdh.Security.CollisionsB
public import Computational.Specifications.Pqxdh.Security.HeadlineDelta
import Computational.Proofs.E2E.ComposedKeyIndHop
import Computational.Proofs.GameHop.Rnd
import Computational.Proofs.SignalPqxdh.Security.CollisionsC
import VCVio.EvalDist.Monad.Basic

/-!
# Bad-KEM event and ML-KEM correctness bound for `cliDrvImpl`

Defines the bad-KEM indicator `cliClause2BadKemBool` over initiator handshake tapes and responder
SPK bundles, proves its stickiness across `simulateQ (cliDrvImpl ...)`, and bounds its probability
by ML-KEM correctness (`cliBadKemProb_le_bound`, `two_mul_cliBadKemProb_modelPrims_le_kemCorrTerm`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.constructorNameAsVariable false

open OracleComp OracleSpec MeasureTheory ENNReal BigOperators

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  CryptoGames.LibsignalSessionApi HMAC HKDF CBC SM
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.LibsignalSpqrV1 CryptoVerification.SignalSession

/-! ## Monad, expectation, and handshake tape helpers -/

@[local simp]
private theorem stateT_run_lift_cli {M : Type → Type} [Monad M] {σ α : Type}
    (mx : M α) (s : σ) :
    (StateT.lift mx : StateT σ M α).run s = (mx >>= fun x => pure (x, s)) := rfl

@[local simp]
private theorem stateT_run_monadLift_cli {M : Type → Type} [Monad M] {σ α : Type}
    (mx : M α) (s : σ) :
    (liftM mx : StateT σ M α).run s = (mx >>= fun x => pure (x, s)) := rfl

private theorem simulateQ_query_bind_run_cli {ι : Type} {spec : OracleSpec ι} {M : Type → Type}
    [Monad M] [LawfulMonad M] {σ₁ σ₂ α : Type}
    (impl : QueryImpl spec (StateT σ₁ (StateT σ₂ M)))
    (q : ι) (oa : spec.Range q → OracleComp spec α)
    (ds : σ₁) (st : σ₂) :
    (((simulateQ impl (liftM (OracleSpec.query q) >>= oa)).run ds).run st) =
      (((impl q).run ds).run st >>= fun z => ((simulateQ impl (oa z.1.1)).run z.1.2).run z.2) := by
  simp [simulateQ_bind, StateT.run_bind]

private theorem evalDist_bind_true_eq_probExpect_comp {α : Type}
    (mx : ProbComp α) (k : α → ProbComp Bool) :
    𝒟[mx >>= k] {true} =
      SignalPqxdh.Security.probExpect mx (fun a => 𝒟[k a] {true}) := by
  let _ : MeasurableSpace α := ⊤
  have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  unfold SignalPqxdh.Security.probExpect
  rw [evalDist_bind_of_discrete,
      Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]

private def wordToVec32Cli (w : BitVec 256) : List.Vector (BitVec 8) 32 :=
  ⟨HMAC.keyToBytes32 w, by simp [HMAC.keyToBytes32]⟩

private theorem bijective_wordToVec32Cli : Function.Bijective wordToVec32Cli :=
  Function.bijective_iff_has_inverse.mpr
    ⟨fun v => HKDF.bytesToKey32 v.toList, bytesToKey32_keyToBytes32,
     fun v => Subtype.ext (keyToBytes32_bytesToKey32 v.toList v.2)⟩

private def joinTape160Cli
    (p : List.Vector (BitVec 8) 32 ×
      (List.Vector (BitVec 8) 32 × List.Vector (BitVec 8) 96)) : List.Vector (BitVec 8) 160 :=
  List.Vector.ofFn (fun k : Fin 160 =>
    if h : k.val < 32 then
      p.2.1.get ⟨k.val, h⟩
    else if (k.val - 32) % 4 = 0 then
      p.1.get ⟨(k.val - 32) / 4, by omega⟩
    else
      p.2.2.get ⟨3 * ((k.val - 32) / 4) + ((k.val - 32) % 4 - 1), by omega⟩)

private def splitTape160Cli (t : List.Vector (BitVec 8) 160) :
    List.Vector (BitVec 8) 32 ×
      (List.Vector (BitVec 8) 32 × List.Vector (BitVec 8) 96) :=
  (List.Vector.ofFn (fun i : Fin 32 => t.get ⟨32 + 4 * i.val, by omega⟩),
   (List.Vector.ofFn (fun i : Fin 32 => t.get ⟨i.val, by omega⟩),
    List.Vector.ofFn (fun j : Fin 96 =>
      t.get ⟨32 + 4 * (j.val / 3) + (j.val % 3 + 1), by omega⟩)))

private theorem splitTape160Cli_joinTape160Cli
    (p : List.Vector (BitVec 8) 32 ×
      (List.Vector (BitVec 8) 32 × List.Vector (BitVec 8) 96)) :
    splitTape160Cli (joinTape160Cli p) = p := by
  rcases p with ⟨kem, ek, pad⟩
  ext : 1
  · apply List.Vector.ext; intro i
    simp only [splitTape160Cli, joinTape160Cli, List.Vector.get_ofFn]
    have h1 : ¬ (32 + 4 * i.val < 32) := by omega
    simp [h1]
  · ext : 1
    · apply List.Vector.ext; intro i
      simp only [splitTape160Cli, joinTape160Cli, List.Vector.get_ofFn]
      have hi : i.val < 32 := i.2
      simp [hi]
    · apply List.Vector.ext; intro j
      simp only [splitTape160Cli, joinTape160Cli, List.Vector.get_ofFn]
      have h1 : ¬ (32 + 4 * (j.val / 3) + (j.val % 3 + 1) < 32) := by omega
      have h2 : (32 + 4 * (j.val / 3) + (j.val % 3 + 1) - 32) % 4 ≠ 0 := by omega
      have h3 : 3 * ((32 + 4 * (j.val / 3) + (j.val % 3 + 1) - 32) / 4) +
          ((32 + 4 * (j.val / 3) + (j.val % 3 + 1) - 32) % 4 - 1) = j.val := by omega
      simp [h1, h2, h3]

private theorem joinTape160Cli_splitTape160Cli (t : List.Vector (BitVec 8) 160) :
    joinTape160Cli (splitTape160Cli t) = t := by
  apply List.Vector.ext; intro k
  simp only [joinTape160Cli, splitTape160Cli, List.Vector.get_ofFn]
  split_ifs with h1 h2
  · rfl
  · congr 1; ext; dsimp only; omega
  · congr 1; ext; dsimp only; omega

private theorem bijective_splitTape160Cli : Function.Bijective splitTape160Cli :=
  Function.bijective_iff_has_inverse.mpr
    ⟨joinTape160Cli, joinTape160Cli_splitTape160Cli, splitTape160Cli_joinTape160Cli⟩

private theorem probExpect_tapeKemCoins_eq_sampleCoins32
    (k : SignalPqxdh.Bytes → ProbComp Bool) :
    SignalPqxdh.Security.probExpect ($ᵗ List.Vector (BitVec 8) 160)
      (fun t_init => 𝒟[k (tapeKemCoins t_init)] {true}) =
    SignalPqxdh.Security.probExpect SignalPqxdh.sampleCoins32
      (fun r => 𝒟[k r] {true}) := by
  rw [← evalDist_bind_true_eq_probExpect_comp, ← evalDist_bind_true_eq_probExpect_comp]
  have heq : (SignalPqxdh.sampleCoins32 : ProbComp SignalPqxdh.Bytes) =
      (fun w => vecU8 (wordToVec32Cli w)) <$> ($ᵗ BitVec 256 : ProbComp (BitVec 256)) := by
    unfold SignalPqxdh.sampleCoins32 SignalPqxdh.sampleBytes32
    congr 1; funext w
    exact word256ToBytes_eq_toU8_keyToBytes32 w
  rw [heq, bind_map_left]
  exact congrArg (· {true})
    (((Computational.Proofs.GameHop.Rnd.evalDistEq_marginal_fst_bind_of_bijective
        bijective_splitTape160Cli (fun v => k (vecU8 v))).trans
      (Computational.Proofs.GameHop.Rnd.evalDistEq_uniformSample_bind_of_bijective
        bijective_wordToVec32Cli (fun v => k (vecU8 v))).symm).evalDist_eq)

/-! ## Bad-KEM predicate and monotonicity -/

/-- Whether ML-KEM decapsulation on responder pre-key bundle entry `b` disagrees with
`P.kemEncaps bnd.pqspkB (tapeKemCoins t_init)` when `bnd.pqspkB = b.pqspkPk`. -/
def cliClause2BadKemPair (P : SignalPqxdh.Primitives)
    (bnd : SignalPqxdh.PreKeyBundleInput) (t_init : List.Vector (BitVec 8) 160)
    (b : SignalPqxdh.SpkBundleEntry) : Bool :=
  decide (bnd.pqspkB = b.pqspkPk) &&
  match P.kemEncaps bnd.pqspkB (tapeKemCoins t_init) with
  | none => false
  | some (ss, kemCt) => decide (P.kemDecaps b.pqspkSk kemCt ≠ some ss)

/-- Bad-KEM event indicator over all initiator handshake tapes in `ds.initTapes` and all
honest responder SPK bundles in `st.spkBundles`. -/
def cliClause2BadKemBool (S : SignalPqxdh.Setup) {ℓ : ℕ} (P : SignalPqxdh.Primitives)
    (st : SignalPqxdh.KeyIndState S) (ds : ModelDriverState S ℓ) : Bool :=
  ds.initTapes.any fun (_, _, bnd, t_init) =>
    st.spkBundles.any fun (_, b) => cliClause2BadKemPair P bnd t_init b

/-- Outside `cliClause2BadKemBool`, honest responder decapsulation recovers the encapsulated shared
secret. -/
theorem not_cliClause2BadKemBool_decaps_eq {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {st : SignalPqxdh.KeyIndState S} {ds : ModelDriverState S ℓ}
    {sid : SignalPqxdh.SessionId S} {u : Fin S.N_id}
    {bnd : SignalPqxdh.PreKeyBundleInput} {t_init : List.Vector (BitVec 8) 160}
    {idx : ℕ × ℕ} {b : SignalPqxdh.SpkBundleEntry}
    {ss ct : SignalPqxdh.Bytes}
    (hNoBad : cliClause2BadKemBool S P st ds = false)
    (hTape : (sid, u, bnd, t_init) ∈ ds.initTapes)
    (hSpk : (idx, b) ∈ st.spkBundles)
    (hPk : b.pqspkPk = bnd.pqspkB)
    (hEnc : P.kemEncaps bnd.pqspkB (tapeKemCoins t_init) = some (ss, ct)) :
    P.kemDecaps b.pqspkSk ct = some ss := by
  apply Decidable.byContradiction
  intro hNe
  have hPair : cliClause2BadKemPair P bnd t_init b = true := by
    unfold cliClause2BadKemPair
    rw [hPk, hEnc]
    simp [hNe]
  have hBad : cliClause2BadKemBool S P st ds = true := by
    unfold cliClause2BadKemBool
    rw [List.any_eq_true]
    refine ⟨(sid, u, bnd, t_init), hTape, ?_⟩
    rw [List.any_eq_true]
    exact ⟨(idx, b), hSpk, hPair⟩
  rw [hNoBad] at hBad
  cases hBad

/-- Monotonicity relation on `ds.initTapes` and the Kyber keypairs in `st.spkBundles`. -/
def CliSpkAndTapesMono {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (st st' : SignalPqxdh.KeyIndState S) (ds ds' : ModelDriverState S ℓ) : Prop :=
  (∀ e ∈ ds.initTapes, e ∈ ds'.initTapes) ∧
  (∀ idx b, (idx, b) ∈ st.spkBundles →
    ∃ b', (idx, b') ∈ st'.spkBundles ∧ b'.pqspkPk = b.pqspkPk ∧ b'.pqspkSk = b.pqspkSk)

theorem CliSpkAndTapesMono.refl {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (st : SignalPqxdh.KeyIndState S) (ds : ModelDriverState S ℓ) :
    CliSpkAndTapesMono st st ds ds :=
  ⟨fun _ h => h, fun _ b h => ⟨b, h, rfl, rfl⟩⟩

theorem CliSpkAndTapesMono.trans {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {st₀ st₁ st₂ : SignalPqxdh.KeyIndState S} {ds₀ ds₁ ds₂ : ModelDriverState S ℓ}
    (h₀₁ : CliSpkAndTapesMono st₀ st₁ ds₀ ds₁) (h₁₂ : CliSpkAndTapesMono st₁ st₂ ds₁ ds₂) :
    CliSpkAndTapesMono st₀ st₂ ds₀ ds₂ := by
  refine ⟨fun e he => h₁₂.1 e (h₀₁.1 e he), fun idx b hb => ?_⟩
  obtain ⟨b₁, hb₁, hpk₁, hsk₁⟩ := h₀₁.2 idx b hb
  obtain ⟨b₂, hb₂, hpk₂, hsk₂⟩ := h₁₂.2 idx b₁ hb₁
  exact ⟨b₂, hb₂, hpk₂.trans hpk₁, hsk₂.trans hsk₁⟩

theorem cliClause2BadKemBool_mono {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (P : SignalPqxdh.Primitives)
    {st st' : SignalPqxdh.KeyIndState S} {ds ds' : ModelDriverState S ℓ}
    (hMono : CliSpkAndTapesMono st st' ds ds')
    (hBad : cliClause2BadKemBool S P st ds = true) :
    cliClause2BadKemBool S P st' ds' = true := by
  unfold cliClause2BadKemBool at hBad ⊢
  simp only [List.any_eq_true] at hBad ⊢
  rcases hBad with ⟨⟨sid, u, bnd, t_init⟩, ht, ⟨idx, b⟩, hb, hpair⟩
  obtain ⟨b', hb', hpk, hsk⟩ := hMono.2 idx b hb
  refine ⟨(sid, u, bnd, t_init), hMono.1 _ ht, (idx, b'), hb', ?_⟩
  unfold cliClause2BadKemPair at hpair ⊢
  rw [hpk, hsk]
  exact hpair

private def PreservesKemState {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (st st' : SignalPqxdh.KeyIndState S) (ds ds' : ModelDriverState S ℓ) : Prop :=
  ds'.initTapes = ds.initTapes ∧
  (st'.spkBundles = st.spkBundles ∨
    ∃ key, st'.spkBundles = st.spkBundles.map (fun (idx, e) =>
      if idx == key then (idx, { e with revealed := true }) else (idx, e))) ∧
  (∀ sEntry ∈ st.sessions, ∃ sEntry' ∈ st'.sessions, sEntry'.sid = sEntry.sid)

private theorem PreservesKemState.refl {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (st : SignalPqxdh.KeyIndState S) (ds : ModelDriverState S ℓ) :
    PreservesKemState st st ds ds :=
  ⟨rfl, Or.inl rfl, fun sEntry hs => ⟨sEntry, hs, rfl⟩⟩

private theorem PreservesKemState.bhDrvMirror {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (st : SignalPqxdh.KeyIndState S) (ds : ModelDriverState S ℓ)
    (q : SignalPqxdh.KeyIndQuery S) (r : SignalPqxdh.KeyIndResponse) :
    PreservesKemState st st ds (CryptoVerification.E2E.bhDrvMirror ds q r) :=
  ⟨rfl, Or.inl rfl, fun sEntry hs => ⟨sEntry, hs, rfl⟩⟩

private theorem PreservesKemState.toSpkAndTapesMono {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {st st' : SignalPqxdh.KeyIndState S} {ds ds' : ModelDriverState S ℓ}
    (h : PreservesKemState st st' ds ds') :
    CliSpkAndTapesMono st st' ds ds' := by
  refine ⟨fun e he => h.1 ▸ he, fun idx bEntry hb => ?_⟩
  rcases h.2.1 with hEq | ⟨key, hMap⟩
  · exact ⟨bEntry, hEq ▸ hb, rfl, rfl⟩
  · refine ⟨if idx == key then { bEntry with revealed := true } else bEntry, ?_, ?_, ?_⟩
    · rw [hMap, List.mem_map]
      refine ⟨(idx, bEntry), hb, ?_⟩
      dsimp only; split_ifs <;> rfl
    · split_ifs <;> rfl
    · split_ifs <;> rfl

private theorem cliRunStdSM_preservesKemState (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (run : CliRun) (W : PEParams) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ds : ModelDriverState S ℓ) (i : ℕ) (bi : ModelDriverInstance S ℓ) (im : ModelDriverInstanceMeta S)
    (gs : SM.GameState BinState (Plain ℓ) Bytes)
    (q : (cliGameSmSpec ℓ (BitVec 512)).Domain)
    (st : SignalPqxdh.KeyIndState S) :
    ∀ y ∈ support (((cliRunStdSM S ℓ run W qep decT encT ds i bi im gs q).run ds).run st),
      PreservesKemState st y.2 ds y.1.2 := by
  intro y hy
  unfold cliRunStdSM at hy
  simp only [StateT.run_bind, stateT_run_lift_cli, stateT_run_monadLift_cli,
    StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind, bind_assoc,
    MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
  rcases hy with ⟨⟨r, gsOut⟩, _, rfl⟩
  exact ⟨rfl, Or.inl rfl, fun sEntry hs => ⟨sEntry, hs, rfl⟩⟩

private theorem cliStepLocalSM_preservesKemState (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (run : CliRun) (W : PEParams) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ds : ModelDriverState S ℓ) (i : ℕ) (bi : ModelDriverInstance S ℓ) (im : ModelDriverInstanceMeta S)
    (gs : SM.GameState BinState (Plain ℓ) Bytes)
    (q : (cliGameSmSpec ℓ (BitVec 512)).Domain)
    (st : SignalPqxdh.KeyIndState S) :
    ∀ y ∈ support (((cliStepLocalSM S ℓ run W qep decT encT ds i bi im gs q).run ds).run st),
      PreservesKemState st y.2 ds y.1.2 := by
  intro y hy
  rcases q with ⟨⟨⟨p⟩ | ⟨⟨p, c⟩⟩⟩ | ⟨⟨p, c⟩⟩⟩ | ⟨p⟩
  · exact cliRunStdSM_preservesKemState S ℓ run W qep decT encT ds i bi im gs _ st y hy
  · cases p <;> unfold cliStepLocalSM at hy <;> dsimp only at hy <;> split_ifs at hy
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy; exact PreservesKemState.refl st ds
    · exact cliRunStdSM_preservesKemState S ℓ run W qep decT encT ds i bi im gs _ st y hy
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy; exact PreservesKemState.refl st ds
    · exact cliRunStdSM_preservesKemState S ℓ run W qep decT encT ds i bi im gs _ st y hy
  · cases p <;> unfold cliStepLocalSM at hy <;> dsimp only at hy <;> split_ifs at hy
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy; exact PreservesKemState.refl st ds
    · exact cliRunStdSM_preservesKemState S ℓ run W qep decT encT ds i bi im gs _ st y hy
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy; exact PreservesKemState.refl st ds
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy; exact PreservesKemState.refl st ds
    · exact cliRunStdSM_preservesKemState S ℓ run W qep decT encT ds i bi im gs _ st y hy
  · exact cliRunStdSM_preservesKemState S ℓ run W qep decT encT ds i bi im gs _ st y hy

private theorem cliDrvSM_preservesKemState (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (run : CliRun) (W : PEParams) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (iq : (cliGameDrSpec ℓ (BitVec 512)).Domain)
    (st : SignalPqxdh.KeyIndState S) (ds : ModelDriverState S ℓ) :
    ∀ y ∈ support (((cliDrvSM S ℓ run W qep decT encT bhNoExtWithSpqr iq).run ds).run st),
      PreservesKemState st y.2 ds y.1.2 := by
  intro y hy
  rcases iq with ⟨i, q⟩
  unfold cliDrvSM at hy
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hy
  split_ifs at hy
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
    subst hy; exact PreservesKemState.refl st ds
  · rcases hbi : ds.bhInsts[i]? with _ | bi
    · rw [hbi] at hy
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy; exact PreservesKemState.refl st ds
    · rw [hbi] at hy
      rcases him : ds.instMeta[i]? with _ | im
      · rw [him] at hy
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
        subst hy; exact PreservesKemState.refl st ds
      · rw [him] at hy; dsimp only at hy
        split_ifs at hy
        · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff] at hy
          subst hy; exact ⟨rfl, Or.inl rfl, fun sEntry hs => ⟨sEntry, hs, rfl⟩⟩
        · rcases hgs : bi.gs with _ | gs
          · rw [hgs] at hy
            simp only [bhNoExtWithSpqr, StateT.run_bind, StateT.run_set, StateT.run_pure,
              pure_bind, support_pure, Set.mem_singleton_iff] at hy
            subst hy; exact ⟨rfl, Or.inl rfl, fun sEntry hs => ⟨sEntry, hs, rfl⟩⟩
          · rw [hgs] at hy
            exact cliStepLocalSM_preservesKemState S ℓ run W qep decT encT ds i bi im gs q st y hy

private theorem pqxdhKeyIndImpl_testSession_preserves (S : SignalPqxdh.Setup)
    (P : SignalPqxdh.Primitives) (sid : SignalPqxdh.SessionId S) (st : SignalPqxdh.KeyIndState S) :
    ∀ x ∈ support ((SignalPqxdh.pqxdhKeyIndImpl false S P (.testSession sid)).run st),
      x.2.spkBundles = st.spkBundles ∧
      ∀ sEntry ∈ st.sessions, ∃ sEntry' ∈ x.2.sessions, sEntry'.sid = sEntry.sid := by
  intro x hx
  unfold SignalPqxdh.pqxdhKeyIndImpl at hx; dsimp only at hx
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hx
  by_cases hFresh : (!SignalPqxdh.isKeyIndSessionTestable st sid) = true
  · simp only [hFresh, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
    subst hx; exact ⟨rfl, fun sEntry hs => ⟨sEntry, hs, rfl⟩⟩
  · simp only [Bool.not_eq_true] at hFresh
    simp only [hFresh, Bool.false_eq_true, ↓reduceIte] at hx
    cases hSecb : st.secb <;> simp only [hSecb, ↓reduceIte, Bool.false_eq_true] at hx <;> (
      rcases h1 : st.sessions.find? (fun e => e.sid == sid) with _ | sFound
      · rw [h1] at hx; dsimp only at hx
        rcases h2 : st.respSessions.find? (fun r => r.sid == sid) with _ | rFound
        · rw [h2] at hx; dsimp only at hx
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
          subst hx; exact ⟨rfl, fun sEntry hs => ⟨sEntry, hs, rfl⟩⟩
        · rw [h2] at hx; dsimp only at hx
          simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff] at hx
          subst hx; exact ⟨rfl, fun sEntry hs => ⟨sEntry, hs, rfl⟩⟩
      · rw [h1] at hx; dsimp only at hx
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] at hx
        subst hx
        refine ⟨rfl, fun sEntry hs => ⟨if sEntry.sid == sid then { sEntry with tested := true } else sEntry,
          List.mem_map.mpr ⟨sEntry, hs, rfl⟩, ?_⟩⟩
        split_ifs <;> rfl)

private theorem pqxdhKeyIndImpl_revealSpkSk_preserves (useRo : Bool) (S : SignalPqxdh.Setup)
    (P : SignalPqxdh.Primitives) (u : Fin S.N_id) (j : Fin S.N_recv)
    (st : SignalPqxdh.KeyIndState S) :
    ∀ x ∈ support ((SignalPqxdh.pqxdhKeyIndImpl useRo S P (.revealSpkSk u j)).run st),
      (x.2.spkBundles = st.spkBundles ∨
       ∃ key, x.2.spkBundles = st.spkBundles.map (fun (idx, bEntry) =>
         if idx == key then (idx, { bEntry with revealed := true }) else (idx, bEntry))) ∧
      x.2.sessions = st.sessions := by
  intro x hx
  unfold SignalPqxdh.pqxdhKeyIndImpl at hx; dsimp only at hx
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hx
  rcases hFind : st.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val)) with _ | ⟨_, bEntry⟩
  · rw [hFind] at hx
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
    subst hx; exact ⟨Or.inl rfl, rfl⟩
  · rw [hFind] at hx; dsimp only at hx
    simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff] at hx
    subst hx; exact ⟨Or.inr ⟨(u.val, j.val), rfl⟩, rfl⟩

set_option linter.unusedTactic false in
private theorem cliDrvStart_preservesKemState (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (run : CliRun) (W : PEParams)
    (mode : BHDrvMode S) (sid : SignalPqxdh.SessionId S)
    (st : SignalPqxdh.KeyIndState S) (ds : ModelDriverState S ℓ) :
    ∀ y ∈ support (((cliDrvStart S ℓ P run W mode sid).run ds).run st),
      PreservesKemState st y.2 ds y.1.2 := by
  intro y hy
  unfold cliDrvStart at hy
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hy
  rcases hG : bhDrvGuard ds sid with _ | ⟨hdr, bnd, u_resp, j_resp⟩
  · rw [hG] at hy
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
    subst hy; exact PreservesKemState.refl st ds
  · rw [hG] at hy; dsimp only at hy
    simp only [StateT.run_bind, stateT_run_lift_cli, stateT_run_monadLift_cli,
      StateT.run_get, pure_bind, bind_assoc, MonadAttach.mem_support_bind] at hy
    rcases hy with ⟨⟨r_test, st_test⟩, hTest, hy⟩
    obtain ⟨hSpk1, hSess1⟩ :=
      pqxdhKeyIndImpl_testSession_preserves S P sid st (r_test, st_test) hTest
    cases r_test with
    | drKeyResp dk =>
      dsimp only at hy
      simp only [StateT.run_bind, stateT_run_lift_cli, stateT_run_monadLift_cli,
        pure_bind, bind_assoc, MonadAttach.mem_support_bind] at hy
      rcases hy with ⟨⟨r_rev, st_rev⟩, hRev, hy⟩
      obtain ⟨hSpk2, hSess2⟩ :=
        pqxdhKeyIndImpl_revealSpkSk_preserves false S P u_resp j_resp st_test (r_rev, st_rev) hRev
      have hSpk_rev : st_rev.spkBundles = st.spkBundles ∨
          ∃ key, st_rev.spkBundles = st.spkBundles.map (fun (idx, bEntry) =>
            if idx == key then (idx, { bEntry with revealed := true }) else (idx, bEntry)) := by
        rw [← hSpk1]; exact hSpk2
      have hSess_rev : ∀ sEntry ∈ st.sessions, ∃ sEntry' ∈ st_rev.sessions, sEntry'.sid = sEntry.sid := by
        rw [hSess2]; exact hSess1
      have hPres_rev : ∀ ds' : ModelDriverState S ℓ,
          ds'.initTapes = ds.initTapes → PreservesKemState st st_rev ds ds' :=
        fun ds' hT => ⟨hT, hSpk_rev, hSess_rev⟩
      cases r_rev with
      | spkSkResp spkSk =>
        dsimp only at hy
        simp only [StateT.run_bind, stateT_run_lift_cli, stateT_run_monadLift_cli,
          pure_bind, bind_assoc, MonadAttach.mem_support_bind] at hy
        rcases hy with ⟨t_dr, _, hy⟩
        repeat (first
          | (try simp only [StateT.run_pure] at hy;
             simp only [support_pure, Set.mem_singleton_iff] at hy;
             subst hy; exact PreservesKemState.refl st ds)
          | (simp only [StateT.run_bind, stateT_run_lift_cli, StateT.run_set, StateT.run_pure,
               pure_bind, support_pure, Set.mem_singleton_iff] at hy;
             subst hy; exact hPres_rev _ rfl)
          | (split at hy;
             try simp only [StateT.run_bind] at hy;
             try simp only [StateT.run_pure] at hy;
             try simp only [pure_bind] at hy;
             try simp only [bind_assoc] at hy))
      | _ =>
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
        subst hy; exact PreservesKemState.refl st ds
    | _ =>
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy; exact PreservesKemState.refl st ds

private theorem pqxdhKeyIndImpl_preserves_spk_and_sess (useRo : Bool)
    (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives)
    (q : SignalPqxdh.KeyIndQuery S) (st : SignalPqxdh.KeyIndState S)
    (hNot : (∀ u j, q ≠ .genSPK u j) ∧ (∀ u j, q ≠ .revealSpkSk u j) ∧
            (∀ sid, q ≠ .testSession sid) ∧ (∀ sid, q ≠ .revealSessionKey sid) ∧
            (∀ u i bnd, q ≠ .initiateOPK u i bnd) ∧ (∀ u i bnd, q ≠ .initiateNoOPK u i bnd)) :
    SignalPqxdh.Security.PreservesAt
      (fun s : SignalPqxdh.KeyIndState S => (s.spkBundles, s.sessions))
      st (SignalPqxdh.pqxdhKeyIndImpl useRo S P q) := by
  rcases hNot with ⟨h1, h2, h3, h4, h5, h6⟩
  cases q with
  | genSPK u j => exact False.elim (h1 u j rfl)
  | revealSpkSk u j => exact False.elim (h2 u j rfl)
  | testSession sid => exact False.elim (h3 sid rfl)
  | revealSessionKey sid => exact False.elim (h4 sid rfl)
  | initiateOPK u i bnd => exact False.elim (h5 u i bnd rfl)
  | initiateNoOPK u i bnd => exact False.elim (h6 u i bnd rfl)
  | _ =>
    unfold SignalPqxdh.pqxdhKeyIndImpl
    dsimp only
    repeat (first
      | with_reducible apply SignalPqxdh.Security.PreservesAt.pure
      | with_reducible apply SignalPqxdh.Security.PreservesAt.get_bind
      | (with_reducible apply SignalPqxdh.Security.PreservesAt.liftM_bind; intro _)
      | ((with_reducible apply SignalPqxdh.Security.PreservesAt.recordKeyIndResp_pure);
         intro _; rfl)
      | ((with_reducible apply SignalPqxdh.Security.PreservesAt.set_bind); rfl)
      | (split; try dsimp only))

private theorem bhDrvMirror_lift_preservesKemState (S : SignalPqxdh.Setup) {ℓ : ℕ}
    (m_st : StateT (SignalPqxdh.KeyIndState S) ProbComp SignalPqxdh.KeyIndResponse)
    (q : SignalPqxdh.KeyIndQuery S)
    (st : SignalPqxdh.KeyIndState S) (ds : ModelDriverState S ℓ)
    (h : ∀ x ∈ support (m_st.run st), PreservesKemState st x.2 ds ds) :
    ∀ y ∈ support (((do
        let r ← StateT.lift m_st
        modify (fun ds => bhDrvMirror ds q r); return r :
        BHDrvM S ℓ SignalPqxdh.KeyIndResponse).run ds).run st),
      PreservesKemState st y.2 ds y.1.2 := by
  intro y hy
  simp only [StateT.run_bind, stateT_run_lift_cli, StateT.run_modify, StateT.run_pure,
    pure_bind, bind_assoc, MonadAttach.mem_support_bind, support_pure,
    Set.mem_singleton_iff] at hy
  rcases hy with ⟨⟨r, st'⟩, hmem, rfl⟩
  exact h (r, st') hmem

private theorem preservesKemState_of_preserves_spk_and_sess {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (m_st : StateT (SignalPqxdh.KeyIndState S) ProbComp SignalPqxdh.KeyIndResponse)
    (q : SignalPqxdh.KeyIndQuery S)
    (st : SignalPqxdh.KeyIndState S) (ds : ModelDriverState S ℓ)
    (hPres : SignalPqxdh.Security.PreservesAt
      (fun s : SignalPqxdh.KeyIndState S => (s.spkBundles, s.sessions)) st m_st) :
    ∀ y ∈ support (((do
        let r ← StateT.lift m_st
        modify (fun ds => bhDrvMirror ds q r); return r :
        BHDrvM S ℓ SignalPqxdh.KeyIndResponse).run ds).run st),
      PreservesKemState st y.2 ds y.1.2 := by
  refine bhDrvMirror_lift_preservesKemState S m_st q st ds (fun x hx => ?_)
  have hEq := Prod.mk.inj (hPres x hx)
  exact ⟨rfl, Or.inl hEq.1, fun sEntry hs => ⟨sEntry, hEq.2 ▸ hs, rfl⟩⟩

private theorem bhDrvKeyInd_preservesKemState_or_gen_or_init (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (useRo : Bool) (q : SignalPqxdh.KeyIndQuery S)
    (st : SignalPqxdh.KeyIndState S) (ds : ModelDriverState S ℓ) :
    (∀ y ∈ support (((bhDrvKeyInd S ℓ P useRo q).run ds).run st),
      PreservesKemState st y.2 ds y.1.2) ∨
    (∃ u j, q = .genSPK u j) ∨
    (∃ u i bnd, q = .initiateOPK u i bnd) ∨
    (∃ u i bnd, q = .initiateNoOPK u i bnd) := by
  cases q with
  | genSPK u j => right; left; exact ⟨u, j, rfl⟩
  | initiateOPK u i bnd => right; right; left; exact ⟨u, i, bnd, rfl⟩
  | initiateNoOPK u i bnd => right; right; right; exact ⟨u, i, bnd, rfl⟩
  | testSession sid =>
    left; intro y hy
    simp only [bhDrvKeyInd, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
    subst hy; exact PreservesKemState.refl st ds
  | revealDhSecrets =>
    left; intro y hy
    simp only [bhDrvKeyInd, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
    subst hy; exact PreservesKemState.refl st ds
  | roQuery secrets =>
    left; intro y hy
    simp only [bhDrvKeyInd, StateT.run_bind, stateT_run_lift_cli, stateT_run_monadLift_cli,
      StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind, bind_assoc,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨dk, roCache'⟩, _, rfl⟩
    exact PreservesKemState.refl st ds
  | initPrin u =>
    left
    unfold bhDrvKeyInd; dsimp only
    cases useRo with
    | false =>
      simp only [Bool.not_false, ↓reduceIte]
      refine bhDrvMirror_lift_preservesKemState S _ (.initPrin u) st ds (fun x hx => ?_)
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at hx
      split_ifs at hx
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
        subst hx; exact PreservesKemState.refl st ds
      · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
          StateT.run_pure, pure_bind, bind_assoc, MonadAttach.mem_support_bind,
          support_pure, Set.mem_singleton_iff] at hx
        rcases hx with ⟨secIKA0, _, rfl⟩
        exact PreservesKemState.refl st ds
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      exact preservesKemState_of_preserves_spk_and_sess _ (.initPrin u) st ds
        (pqxdhKeyIndImpl_preserves_spk_and_sess true S P (.initPrin u) st
          ⟨(fun _ _ h => nomatch h), (fun _ _ h => nomatch h), (fun _ h => nomatch h),
           (fun _ h => nomatch h), (fun _ _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩)
  | corruptIK u =>
    left; intro y hy
    unfold bhDrvKeyInd at hy; dsimp only at hy
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hy
    split_ifs at hy
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy; exact PreservesKemState.refl st ds
    · exact preservesKemState_of_preserves_spk_and_sess _ (.corruptIK u) st ds
        (pqxdhKeyIndImpl_preserves_spk_and_sess useRo S P (.corruptIK u) st
          ⟨(fun _ _ h => nomatch h), (fun _ _ h => nomatch h), (fun _ h => nomatch h),
           (fun _ h => nomatch h), (fun _ _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩) y hy
  | genOPK u j o =>
    left; unfold bhDrvKeyInd; dsimp only
    exact preservesKemState_of_preserves_spk_and_sess _ (.genOPK u j o) st ds
      (pqxdhKeyIndImpl_preserves_spk_and_sess useRo S P (.genOPK u j o) st
        ⟨(fun _ _ h => nomatch h), (fun _ _ h => nomatch h), (fun _ h => nomatch h),
         (fun _ h => nomatch h), (fun _ _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩)
  | registerKey sk =>
    left; unfold bhDrvKeyInd; dsimp only
    exact preservesKemState_of_preserves_spk_and_sess _ (.registerKey sk) st ds
      (pqxdhKeyIndImpl_preserves_spk_and_sess useRo S P (.registerKey sk) st
        ⟨(fun _ _ h => nomatch h), (fun _ _ h => nomatch h), (fun _ h => nomatch h),
         (fun _ h => nomatch h), (fun _ _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩)
  | acceptOPK k j o hdr =>
    left; intro y hy
    unfold bhDrvKeyInd at hy; dsimp only at hy
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hy
    split_ifs at hy
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy; exact PreservesKemState.refl st ds
    · exact preservesKemState_of_preserves_spk_and_sess _ (.acceptOPK k j o hdr) st ds
        (pqxdhKeyIndImpl_preserves_spk_and_sess useRo S P (.acceptOPK k j o hdr) st
          ⟨(fun _ _ h => nomatch h), (fun _ _ h => nomatch h), (fun _ h => nomatch h),
           (fun _ h => nomatch h), (fun _ _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩) y hy
  | acceptNoOPK k j l hdr =>
    left; intro y hy
    unfold bhDrvKeyInd at hy; dsimp only at hy
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hy
    split_ifs at hy
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy; exact PreservesKemState.refl st ds
    · exact preservesKemState_of_preserves_spk_and_sess _ (.acceptNoOPK k j l hdr) st ds
        (pqxdhKeyIndImpl_preserves_spk_and_sess useRo S P (.acceptNoOPK k j l hdr) st
          ⟨(fun _ _ h => nomatch h), (fun _ _ h => nomatch h), (fun _ h => nomatch h),
           (fun _ h => nomatch h), (fun _ _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩) y hy
  | revealSpkSk u j =>
    left; unfold bhDrvKeyInd; dsimp only
    refine bhDrvMirror_lift_preservesKemState S _ (.revealSpkSk u j) st ds (fun x hx => ?_)
    obtain ⟨hSpk, hSess⟩ := pqxdhKeyIndImpl_revealSpkSk_preserves useRo S P u j st x hx
    exact ⟨rfl, hSpk, fun sEntry hs => ⟨sEntry, hSess ▸ hs, rfl⟩⟩
  | revealSessionKey sid =>
    left; unfold bhDrvKeyInd; dsimp only
    refine bhDrvMirror_lift_preservesKemState S _ (.revealSessionKey sid) st ds (fun x hx => ?_)
    unfold SignalPqxdh.pqxdhKeyIndImpl at hx; dsimp only at hx
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hx
    rcases hFind1 : st.sessions.find? (fun e => e.sid == sid) with _ | eFound
    · rw [hFind1] at hx; dsimp only at hx
      rcases hFind2 : st.respSessions.find? (fun r => r.sid == sid) with _ | reFound
      · rw [hFind2] at hx; dsimp only at hx
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
        subst hx; exact PreservesKemState.refl st ds
      · rw [hFind2] at hx; dsimp only at hx
        split_ifs at hx
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
          subst hx; exact PreservesKemState.refl st ds
        · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff] at hx
          subst hx; exact PreservesKemState.refl st ds
    · rw [hFind1] at hx; dsimp only at hx
      split_ifs at hx
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
        subst hx; exact PreservesKemState.refl st ds
      · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] at hx
        subst hx
        refine ⟨rfl, Or.inl rfl, fun sEntry hs => ?_⟩
        refine ⟨if sEntry.sid == sid then { sEntry with revealed := true } else sEntry,
          List.mem_map.mpr ⟨sEntry, hs, rfl⟩, ?_⟩
        split_ifs <;> rfl

private theorem bhDrvMirror_wrapper_spkAndTapesMono (S : SignalPqxdh.Setup) {ℓ : ℕ}
    (m : BHDrvM S ℓ SignalPqxdh.KeyIndResponse) (q : SignalPqxdh.KeyIndQuery S)
    (st : SignalPqxdh.KeyIndState S) (ds : ModelDriverState S ℓ)
    (h : ∀ y ∈ support ((m.run ds).run st), CliSpkAndTapesMono st y.2 ds y.1.2) :
    ∀ y ∈ support (((do let r ← m; modify (fun ds => bhDrvMirror ds q r); return r :
      BHDrvM S ℓ SignalPqxdh.KeyIndResponse).run ds).run st),
      CliSpkAndTapesMono st y.2 ds y.1.2 := by
  intro y hy
  simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
    MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
  rcases hy with ⟨z, hz, rfl⟩
  exact h z hz

private theorem bhRunInitiate_spkAndTapesMono (S : SignalPqxdh.Setup) {ℓ : ℕ}
    (P : SignalPqxdh.Primitives)
    (sid : SignalPqxdh.SessionId S) (u : Fin S.N_id) (bundle : SignalPqxdh.PreKeyBundleInput)
    (useRo : Bool)
    (st : SignalPqxdh.KeyIndState S) (ds : ModelDriverState S ℓ) :
    ∀ y ∈ support (((bhRunInitiate S P sid u bundle useRo :
        BHDrvM S ℓ SignalPqxdh.KeyIndResponse).run ds).run st),
      CliSpkAndTapesMono st y.2 ds y.1.2 := by
  intro y hy
  unfold bhRunInitiate at hy
  simp only [StateT.run_bind, stateT_run_lift_cli, StateT.run_get, pure_bind, bind_assoc] at hy
  cases hFresh : st.sessions.any (fun e => e.sid == sid)
  · rw [hFresh] at hy
    simp only [Bool.false_eq_true, ↓reduceIte] at hy
    rcases hFindU : st.principals.find? (fun (idx, _) => idx == u.val) with _ | ⟨_, uEntry⟩
    · rw [hFindU] at hy
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy; exact CliSpkAndTapesMono.refl st ds
    · rw [hFindU] at hy; dsimp only at hy
      split_ifs at hy
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
        subst hy; exact CliSpkAndTapesMono.refl st ds
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
        subst hy; exact CliSpkAndTapesMono.refl st ds
      · simp only [StateT.run_bind, stateT_run_lift_cli, stateT_run_monadLift_cli,
          StateT.run_pure, pure_bind, bind_assoc, MonadAttach.mem_support_bind, support_pure,
          Set.mem_singleton_iff] at hy
        rcases hy with ⟨_, _, rfl⟩
        exact CliSpkAndTapesMono.refl st ds
      · simp only [StateT.run_bind, stateT_run_lift_cli, stateT_run_monadLift_cli,
          pure_bind, bind_assoc, MonadAttach.mem_support_bind] at hy
        rcases hy with ⟨t_init, _, hy⟩
        rcases hEnc : P.kemEncaps bundle.pqspkB (tapeKemCoins t_init) with _ | ⟨ss, kemCt⟩
        · rw [hEnc] at hy
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
          subst hy; exact CliSpkAndTapesMono.refl st ds
        · rw [hEnc] at hy; dsimp only at hy
          simp only [StateT.run_bind, stateT_run_lift_cli, stateT_run_monadLift_cli,
            pure_bind, bind_assoc, MonadAttach.mem_support_bind] at hy
          rcases hy with ⟨⟨drKeyReal, roCache'⟩, _, hy⟩
          rcases hKPR : SignalPqxdh.keyIndPartnerRandKey? P st.respSessions _ with _ | dk
          · rw [hKPR] at hy; dsimp only at hy
            simp only [StateT.run_bind, stateT_run_lift_cli, stateT_run_monadLift_cli,
              StateT.run_set, StateT.run_modify, pure_bind, bind_assoc,
              MonadAttach.mem_support_bind] at hy
            rcases hy with ⟨drKeyRand, _, hy⟩
            rcases hFHP : SignalPqxdh.findHonestPrincipal P st.principals bundle.ikB with _ | _ <;>
              rw [hFHP] at hy <;>
              simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy <;>
              subst hy <;>
              exact ⟨fun e he => List.mem_cons_of_mem _ he, fun _ bEntry hb => ⟨bEntry, hb, rfl, rfl⟩⟩
          · rw [hKPR] at hy; dsimp only at hy
            rcases hFHP : SignalPqxdh.findHonestPrincipal P st.principals bundle.ikB with _ | _ <;>
              rw [hFHP] at hy <;>
              simp only [StateT.run_bind, stateT_run_lift_cli, StateT.run_set, StateT.run_modify,
                StateT.run_pure, pure_bind, bind_assoc, support_pure, Set.mem_singleton_iff] at hy <;>
              subst hy <;>
              exact ⟨fun e he => List.mem_cons_of_mem _ he, fun _ bEntry hb => ⟨bEntry, hb, rfl, rfl⟩⟩
  · rw [hFresh] at hy
    simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
    subst hy; exact CliSpkAndTapesMono.refl st ds

private theorem bhDrvKeyInd_spkAndTapesMono (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (useRo : Bool) (q : SignalPqxdh.KeyIndQuery S)
    (st : SignalPqxdh.KeyIndState S) (ds : ModelDriverState S ℓ) :
    ∀ y ∈ support (((bhDrvKeyInd S ℓ P useRo q).run ds).run st),
      CliSpkAndTapesMono st y.2 ds y.1.2 := by
  rcases bhDrvKeyInd_preservesKemState_or_gen_or_init S ℓ P useRo q st ds with
    hPres | ⟨u, j, rfl⟩ | ⟨u, i, bnd, rfl⟩ | ⟨u, i, bnd, rfl⟩
  · exact fun y hy => (hPres y hy).toSpkAndTapesMono
  · unfold bhDrvKeyInd; dsimp only
    refine bhDrvMirror_wrapper_spkAndTapesMono S _ (.genSPK u j) st ds (fun y hy => ?_)
    simp only [stateT_run_lift_cli, StateT.run_bind, StateT.run_pure,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨r, st'⟩, hmem, rfl⟩
    unfold SignalPqxdh.pqxdhKeyIndImpl at hmem; dsimp only at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    split_ifs at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩; exact CliSpkAndTapesMono.refl _ ds
    · rcases hFindU : st.principals.find? (fun (idx, _) => idx == u.val) with _ | ⟨_, uEntry⟩
      · rw [hFindU] at hmem
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩; exact CliSpkAndTapesMono.refl _ ds
      · rw [hFindU] at hmem; dsimp only at hmem
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
          StateT.run_pure, bind_assoc, pure_bind, MonadAttach.mem_support_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨spkSk, _, rSpk, _, ⟨pqspkPk, pqspkSk⟩, _, rPq, _, rfl, rfl⟩
        exact ⟨fun e he => he, fun _ bEntry hb => ⟨bEntry, List.mem_cons_of_mem _ hb, rfl, rfl⟩⟩
  · intro y hy
    unfold bhDrvKeyInd at hy; dsimp only at hy
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hy
    split_ifs at hy
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy; exact CliSpkAndTapesMono.refl st ds
    · exact bhDrvMirror_wrapper_spkAndTapesMono S _ (.initiateOPK u i bnd) st ds
        (bhRunInitiate_spkAndTapesMono S P (.sendOPK u i) u bnd useRo st ds) y hy
  · intro y hy
    unfold bhDrvKeyInd at hy; dsimp only at hy
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hy
    split_ifs at hy
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy; exact CliSpkAndTapesMono.refl st ds
    · exact bhDrvMirror_wrapper_spkAndTapesMono S _ (.initiateNoOPK u i bnd) st ds
        (bhRunInitiate_spkAndTapesMono S P (.sendNoOPK u i) u bnd useRo st ds) y hy

@[local simp]
private theorem cliDrvImpl_inl_inl_inl (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (P : SignalPqxdh.Primitives) (run : CliRun) (W : PEParams)
    (qep : ℕ) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ext : QueryImpl (cliGameSmSpec ℓ (BitVec 512)) (BHDrvM S ℓ))
    (mode : BHDrvMode S) (uq : unifSpec.Domain)
    (ds : ModelDriverState S ℓ) (st : SignalPqxdh.KeyIndState S) :
    ((cliDrvImpl S ℓ P run W qep decT encT ext mode (.inl (.inl (.inl uq)))).run ds).run st =
    (fun u => ((u, ds), st)) <$> (liftM (unifSpec.query uq) : ProbComp (unifSpec.Range uq)) := by
  simp [cliDrvImpl, QueryImpl.liftTarget, StateT.run_monadLift, Functor.map_map]

@[local simp]
private theorem cliDrvImpl_inl_inl_inr (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (P : SignalPqxdh.Primitives) (run : CliRun) (W : PEParams)
    (qep : ℕ) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ext : QueryImpl (cliGameSmSpec ℓ (BitVec 512)) (BHDrvM S ℓ))
    (mode : BHDrvMode S) (kq : SignalPqxdh.KeyIndQuery S) :
    cliDrvImpl S ℓ P run W qep decT encT ext mode (.inl (.inl (.inr kq))) =
    bhDrvKeyInd S ℓ P false kq := rfl

@[local simp]
private theorem cliDrvImpl_inl_inr (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (P : SignalPqxdh.Primitives) (run : CliRun) (W : PEParams)
    (qep : ℕ) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ext : QueryImpl (cliGameSmSpec ℓ (BitVec 512)) (BHDrvM S ℓ))
    (mode : BHDrvMode S) (sid : SignalPqxdh.SessionId S) :
    cliDrvImpl S ℓ P run W qep decT encT ext mode (.inl (.inr (.startDR sid))) =
    cliDrvStart S ℓ P run W mode sid := rfl

@[local simp]
private theorem cliDrvImpl_inr (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (P : SignalPqxdh.Primitives) (run : CliRun) (W : PEParams)
    (qep : ℕ) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ext : QueryImpl (cliGameSmSpec ℓ (BitVec 512)) (BHDrvM S ℓ))
    (mode : BHDrvMode S)
    (iq : (cliGameDrSpec ℓ (BitVec 512)).Domain) :
    cliDrvImpl S ℓ P run W qep decT encT ext mode (.inr iq) =
    cliDrvSM S ℓ run W qep decT encT ext iq := rfl

theorem cliDrvImpl_spkAndTapesMono (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (P : SignalPqxdh.Primitives) (run : CliRun) (W : PEParams)
    (qep : ℕ) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (mode : BHDrvMode S)
    (q : (cliGameSpec S ℓ (BitVec 512)).Domain)
    (st : SignalPqxdh.KeyIndState S) (ds : ModelDriverState S ℓ) :
    ∀ y ∈ support (((cliDrvImpl S ℓ P run W qep decT encT bhNoExtWithSpqr mode q).run ds).run st),
      CliSpkAndTapesMono st y.2 ds y.1.2 := by
  intro y hy
  rcases q with ((uq | kq) | ctlq) | iq
  · rw [cliDrvImpl_inl_inl_inl] at hy
    simp only [support_map, Set.mem_image] at hy
    rcases hy with ⟨u, _, rfl⟩
    exact CliSpkAndTapesMono.refl st ds
  · rw [cliDrvImpl_inl_inl_inr] at hy
    exact bhDrvKeyInd_spkAndTapesMono S ℓ P false kq st ds y hy
  · cases ctlq with
    | startDR sid =>
      rw [cliDrvImpl_inl_inr] at hy
      exact PreservesKemState.toSpkAndTapesMono
        (cliDrvStart_preservesKemState S ℓ P run W mode sid st ds y hy)
  · rw [cliDrvImpl_inr] at hy
    exact PreservesKemState.toSpkAndTapesMono
      (cliDrvSM_preservesKemState S ℓ run W qep decT encT iq st ds y hy)

theorem simulateQ_cliDrvImpl_spkAndTapesMono (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt α : Type}
    (P : SignalPqxdh.Primitives) (run : CliRun) (W : PEParams)
    (qep : ℕ) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (mode : BHDrvMode S)
    (oa : OracleComp (cliGameSpec S ℓ (BitVec 512)) α)
    (st : SignalPqxdh.KeyIndState S) (ds : ModelDriverState S ℓ) :
    ∀ y ∈ support (((simulateQ (cliDrvImpl S ℓ P run W qep decT encT bhNoExtWithSpqr
      mode) oa).run ds).run st),
      CliSpkAndTapesMono st y.2 ds y.1.2 := by
  let impl := cliDrvImpl S ℓ P run W qep decT encT bhNoExtWithSpqr mode
  induction oa using OracleComp.inductionOn generalizing st ds with
  | pure a =>
    intro y hy
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
    subst hy; exact CliSpkAndTapesMono.refl st ds
  | query_bind q oa ih =>
    intro y hy
    rw [simulateQ_query_bind_run_cli, MonadAttach.mem_support_bind] at hy
    rcases hy with ⟨z, hz, hy⟩
    have h1 := cliDrvImpl_spkAndTapesMono S ℓ P run W qep decT encT mode q st ds z hz
    have h2 := ih z.1.1 z.2 z.1.2 y hy
    exact CliSpkAndTapesMono.trans h1 h2

/-- Once `cliClause2BadKemBool` holds, it remains `true` across `simulateQ (cliDrvImpl ...)`. -/
theorem probExpect_simulateQ_cliBadKem_eq_one_of_bad (S : SignalPqxdh.Setup) (ℓ : ℕ)
    {Pt α : Type}
    (P : SignalPqxdh.Primitives) (run : CliRun) (W : PEParams)
    (qep : ℕ) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (mode : BHDrvMode S)
    (oa : OracleComp (cliGameSpec S ℓ (BitVec 512)) α)
    (st : SignalPqxdh.KeyIndState S) (ds : ModelDriverState S ℓ)
    (hBad : cliClause2BadKemBool S P st ds = true) :
    SignalPqxdh.Security.probExpect
      (((simulateQ (cliDrvImpl S ℓ P run W qep decT encT bhNoExtWithSpqr mode) oa).run ds).run st)
      (fun y => 𝒟[(pure (cliClause2BadKemBool S P y.2 y.1.2) : ProbComp Bool)] {true}) = 1 := by
  calc SignalPqxdh.Security.probExpect
        (((simulateQ (cliDrvImpl S ℓ P run W qep decT encT bhNoExtWithSpqr mode) oa).run ds).run st)
        (fun y => 𝒟[(pure (cliClause2BadKemBool S P y.2 y.1.2) : ProbComp Bool)] {true})
      = SignalPqxdh.Security.probExpect
          (((simulateQ (cliDrvImpl S ℓ P run W qep decT encT bhNoExtWithSpqr mode) oa).run ds).run st)
          (fun _ => 1) := by
        refine le_antisymm
          (SignalPqxdh.Security.probExpect_mono_of_support _ _ _ (fun _ _ => measure_le_one _ _))
          (SignalPqxdh.Security.probExpect_mono_of_support _ _ _ (fun y hy => ?_))
        have hBad' := cliClause2BadKemBool_mono P
          (simulateQ_cliDrvImpl_spkAndTapesMono S ℓ P run W qep decT encT mode oa st ds y hy) hBad
        simp [hBad']
    _ = 1 := SignalPqxdh.Security.probExpect_const _ 1

/-- Bad-KEM experiment running `runCliDriver` from the empty `KeyIndState` and `{}`. -/
noncomputable def cliRunBadKemExp (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives)
    (run : CliRun) (W : PEParams) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : CliGameAdversary S ℓ (BitVec 512)) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let ((_, ds), st) ←
    (runCliDriver S ℓ P run W qep decT encT bhNoExtWithSpqr
      (fun _ _ _ _ _ => some b) A).run (SignalPqxdh.KeyIndState.empty S true)
  return cliClause2BadKemBool S P st ds

/-! ## ML-KEM correctness bound -/

private def ValidCliBadKemState (S : SignalPqxdh.Setup) {ℓ : ℕ}
    (st : SignalPqxdh.KeyIndState S) (ds : ModelDriverState S ℓ) : Prop :=
  SignalPqxdh.Security.ValidSpkBundlesKem S st.spkBundles ∧
  (∀ e ∈ ds.initTapes,
    SignalPqxdh.Security.IsSendSessionId S e.1 ∧ ∃ sEntry ∈ st.sessions, sEntry.sid = e.1) ∧
  (ds.initTapes.map (fun e => SignalPqxdh.Security.sessSlotFlatIdx S e.1)).Nodup

private theorem validCliBadKemState_empty (S : SignalPqxdh.Setup) (ℓ : ℕ) (secb : Bool) :
    ValidCliBadKemState S (SignalPqxdh.KeyIndState.empty S secb) ({} : ModelDriverState S ℓ) :=
  ⟨SignalPqxdh.Security.validSpkBundlesKem_nil S,
   fun _ h => False.elim (List.not_mem_nil h),
   List.nodup_nil⟩

private theorem PreservesKemState.validCliBadKemState {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {st st' : SignalPqxdh.KeyIndState S} {ds ds' : ModelDriverState S ℓ}
    (hP : PreservesKemState st st' ds ds') (hV : ValidCliBadKemState S st ds) :
    ValidCliBadKemState S st' ds' := by
  refine ⟨?_, ?_, ?_⟩
  · rcases hP.2.1 with hEq | ⟨key, hMap⟩
    · exact hEq ▸ hV.1
    · rw [hMap]
      exact (SignalPqxdh.Security.validSpkBundlesKem_map_revealed S key st.spkBundles hV.1).1
  · intro e he
    rw [hP.1] at he
    obtain ⟨hSend, sEntry, hs, hsid⟩ := hV.2.1 e he
    obtain ⟨sEntry', hs', hsid'⟩ := hP.2.2 sEntry hs
    exact ⟨hSend, sEntry', hs', hsid'.trans hsid⟩
  · rw [hP.1]; exact hV.2.2

private def cliClause2BadKemAt (S : SignalPqxdh.Setup) {ℓ : ℕ} (P : SignalPqxdh.Primitives)
    (bIdx sIdx : ℕ) (st : SignalPqxdh.KeyIndState S) (ds : ModelDriverState S ℓ) : Bool :=
  match st.spkBundles.find? (fun e => SignalPqxdh.Security.spkSlotFlatIdx S e.1 == bIdx),
        ds.initTapes.find? (fun e => SignalPqxdh.Security.sessSlotFlatIdx S e.1 == sIdx) with
  | some (_, bEntry), some (_, _, bnd, t_init) => cliClause2BadKemPair P bnd t_init bEntry
  | _, _ => false

private noncomputable def cliKemCorrPotential (S : SignalPqxdh.Setup) {ℓ : ℕ}
    (P : SignalPqxdh.Primitives) (bIdx sIdx : ℕ)
    (st : SignalPqxdh.KeyIndState S) (ds : ModelDriverState S ℓ) : ℝ≥0∞ :=
  match st.spkBundles.find? (fun e => SignalPqxdh.Security.spkSlotFlatIdx S e.1 == bIdx),
        ds.initTapes.find? (fun e => SignalPqxdh.Security.sessSlotFlatIdx S e.1 == sIdx) with
  | none, none =>
      𝒟[do
        let seed ← SignalPqxdh.sampleRandom64
        let r ← SignalPqxdh.sampleCoins32
        pure (SignalPqxdh.kemHonestExchangeFails P seed r)] {true}
  | some (_, bEntry), none =>
      𝒟[do
        let r ← SignalPqxdh.sampleCoins32
        pure (match P.kemEncaps bEntry.pqspkPk r with
          | none => false
          | some (ss, ct) => decide (P.kemDecaps bEntry.pqspkSk ct ≠ some ss))] {true}
  | none, some (_, _, _, t_init) =>
      𝒟[do
        let seed ← SignalPqxdh.sampleRandom64
        pure (SignalPqxdh.kemHonestExchangeFails P seed (tapeKemCoins t_init))] {true}
  | some (_, bEntry), some (_, _, bnd, t_init) =>
      𝒟[(pure (cliClause2BadKemPair P bnd t_init bEntry) : ProbComp Bool)] {true}

private theorem evalDist_cliClause2BadKemAt_le_potential (S : SignalPqxdh.Setup) {ℓ : ℕ}
    (P : SignalPqxdh.Primitives) (bIdx sIdx : ℕ)
    (st : SignalPqxdh.KeyIndState S) (ds : ModelDriverState S ℓ) :
    𝒟[(pure (cliClause2BadKemAt S P bIdx sIdx st ds) : ProbComp Bool)] {true} ≤
      cliKemCorrPotential S P bIdx sIdx st ds := by
  unfold cliClause2BadKemAt cliKemCorrPotential
  cases st.spkBundles.find? (fun e => SignalPqxdh.Security.spkSlotFlatIdx S e.1 == bIdx) with
  | none => simp
  | some p =>
    rcases p with ⟨_, bEntry⟩
    cases ds.initTapes.find? (fun e => SignalPqxdh.Security.sessSlotFlatIdx S e.1 == sIdx) with
    | none => simp
    | some t =>
      rcases t with ⟨_, _, bnd, t_init⟩
      exact le_rfl

private theorem PreservesKemState.cliKemCorrPotential_eq {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (P : SignalPqxdh.Primitives) (bIdx sIdx : ℕ)
    {st st' : SignalPqxdh.KeyIndState S} {ds ds' : ModelDriverState S ℓ}
    (hP : PreservesKemState st st' ds ds') :
    cliKemCorrPotential S P bIdx sIdx st' ds' = cliKemCorrPotential S P bIdx sIdx st ds := by
  unfold cliKemCorrPotential
  rw [hP.1]
  rcases hP.2.1 with hEq | ⟨key, hMap⟩
  · rw [hEq]
  · rw [hMap, SignalPqxdh.Security.find?_spkSlotFlatIdx_map_revealed]
    cases st.spkBundles.find? (fun e => SignalPqxdh.Security.spkSlotFlatIdx S e.1 == bIdx) with
    | none => rfl
    | some p =>
      rcases p with ⟨idx, bEntry⟩
      dsimp only [Option.map]
      cases ds.initTapes.find? (fun e => SignalPqxdh.Security.sessSlotFlatIdx S e.1 == sIdx) with
      | none => split_ifs <;> rfl
      | some t =>
        rcases t with ⟨sid, u, bnd, t_init⟩
        split_ifs <;> rfl

private theorem probExpect_cliKemCorrPotential_genSPK_le (S : SignalPqxdh.Setup) {ℓ : ℕ}
    (P : SignalPqxdh.Primitives) (u : Fin S.N_id) (j : Fin S.N_recv)
    (st : SignalPqxdh.KeyIndState S) (ds : ModelDriverState S ℓ)
    (hV : SignalPqxdh.Security.ValidSpkBundlesKem S st.spkBundles)
    (hFresh : st.spkBundles.any (fun (k, _) => k == (u.val, j.val)) = false)
    (mkEntry : SignalPqxdh.Bytes × SignalPqxdh.Bytes → SignalPqxdh.Bytes →
      SignalPqxdh.SpkBundleEntry)
    (hpk : ∀ pair rPq, (mkEntry pair rPq).pqspkPk = pair.1)
    (hsk : ∀ pair rPq, (mkEntry pair rPq).pqspkSk = pair.2)
    (bIdx sIdx : ℕ) :
    SignalPqxdh.Security.probExpect (SignalPqxdh.sampleKemKeyGen P)
      (fun pair => SignalPqxdh.Security.probExpect SignalPqxdh.sampleRandom64
        (fun rPq => cliKemCorrPotential S P bIdx sIdx
          { st with spkBundles := ((u.val, j.val), mkEntry pair rPq) :: st.spkBundles } ds)) ≤
      cliKemCorrPotential S P bIdx sIdx st ds := by
  have hnone := SignalPqxdh.Security.find?_spkSlotFlatIdx_none_of_fresh S u j st.spkBundles hV hFresh
  unfold cliKemCorrPotential cliClause2BadKemPair
  simp only [List.find?_cons]
  by_cases hb : (SignalPqxdh.Security.spkSlotFlatIdx S (u.val, j.val) == bIdx) = true
  · have heq : SignalPqxdh.Security.spkSlotFlatIdx S (u.val, j.val) = bIdx := beq_iff_eq.mp hb
    have hnone' : st.spkBundles.find? (fun e => SignalPqxdh.Security.spkSlotFlatIdx S e.1 == bIdx) =
        none := by rwa [← heq]
    simp only [hb, hnone']
    cases ds.initTapes.find? (fun e => SignalPqxdh.Security.sessSlotFlatIdx S e.1 == sIdx) with
    | none =>
      dsimp only
      simp only [hpk, hsk, SignalPqxdh.Security.probExpect_const]
      unfold SignalPqxdh.sampleKemKeyGen SignalPqxdh.kemHonestExchangeFails
      rw [evalDist_bind_true_eq_probExpect_comp, SignalPqxdh.Security.probExpect_bind]
      simp only [SignalPqxdh.Security.probExpect_pure]
      exact le_rfl
    | some t =>
      rcases t with ⟨sid, u₀, bnd, t_init⟩
      dsimp only
      simp only [hpk, hsk, SignalPqxdh.Security.probExpect_const]
      unfold SignalPqxdh.sampleKemKeyGen
      rw [SignalPqxdh.Security.evalDist_bind_true_eq_probExpect,
          SignalPqxdh.Security.probExpect_bind]
      simp only [SignalPqxdh.Security.probExpect_pure]
      refine SignalPqxdh.Security.probExpect_mono_of_support _ _ _ (fun seed _ => ?_)
      by_cases hpq : bnd.pqspkB = (P.kemKeyGen seed).1
      · simp [SignalPqxdh.kemHonestExchangeFails, hpq]; exact le_rfl
      · simp [hpq]
  · simp only [Bool.not_eq_true] at hb
    simp [hb, SignalPqxdh.Security.probExpect_const]

private theorem find?_sessSlotFlatIdx_none_of_fresh (S : SignalPqxdh.Setup) {ℓ : ℕ}
    (sid : SignalPqxdh.SessionId S)
    (st : SignalPqxdh.KeyIndState S) (ds : ModelDriverState S ℓ)
    (hV : ValidCliBadKemState S st ds)
    (hSend : SignalPqxdh.Security.IsSendSessionId S sid)
    (hFresh : st.sessions.any (fun e => e.sid == sid) = false) :
    ds.initTapes.find? (fun e =>
      SignalPqxdh.Security.sessSlotFlatIdx S e.1 ==
        SignalPqxdh.Security.sessSlotFlatIdx S sid) = none := by
  rw [List.find?_eq_none]
  intro e hmem hbeq
  obtain ⟨hSend_e, sEntry, hs, hsid_s⟩ := hV.2.1 e hmem
  have heq : e.1 = sid :=
    SignalPqxdh.Security.sessSlotFlatIdx_inj S hSend_e hSend (beq_iff_eq.mp hbeq)
  have hany : st.sessions.any (fun x => x.sid == sid) = true := by
    rw [List.any_eq_true]
    exact ⟨sEntry, hs, by simp [hsid_s, heq]⟩
  rw [hFresh] at hany
  cases hany

private theorem validCliBadKemState_cons_initiate (S : SignalPqxdh.Setup) {ℓ : ℕ}
    (sid : SignalPqxdh.SessionId S) (u : Fin S.N_id)
    (bundle : SignalPqxdh.PreKeyBundleInput) (t_init : List.Vector (BitVec 8) 160)
    (entry : SignalPqxdh.KeyIndInitiatorEntry S)
    (roCache' : List (SignalPqxdh.Bytes × SignalPqxdh.DRKey))
    (ds : ModelDriverState S ℓ) (ds' : ModelDriverState S ℓ)
    (st : SignalPqxdh.KeyIndState S)
    (hV : ValidCliBadKemState S st ds)
    (hSend : SignalPqxdh.Security.IsSendSessionId S sid)
    (hFresh : st.sessions.any (fun e => e.sid == sid) = false)
    (hSid : entry.sid = sid)
    (hTapes : ds'.initTapes = (sid, u, bundle, t_init) :: ds.initTapes) :
    ValidCliBadKemState S
      { st with sessions := entry :: st.sessions, roCache := roCache' } ds' := by
  refine ⟨hV.1, ?_, ?_⟩
  · intro e he
    rw [hTapes] at he
    rcases List.mem_cons.mp he with rfl | hmem
    · exact ⟨hSend, entry, List.mem_cons_self, hSid⟩
    · obtain ⟨hSend_e, sEntry, hs, hsid_s⟩ := hV.2.1 e hmem
      exact ⟨hSend_e, sEntry, List.mem_cons_of_mem entry hs, hsid_s⟩
  · rw [hTapes, List.map_cons, List.nodup_cons]
    refine ⟨?_, hV.2.2⟩
    rw [List.mem_map]
    rintro ⟨e, hmem, heq⟩
    have hnone := find?_sessSlotFlatIdx_none_of_fresh S sid st ds hV hSend hFresh
    rw [List.find?_eq_none] at hnone
    exact hnone e hmem (beq_iff_eq.mpr heq)

private theorem probExpect_cliKemCorrPotential_initiate_le (S : SignalPqxdh.Setup) {ℓ : ℕ}
    (P : SignalPqxdh.Primitives)
    (sid : SignalPqxdh.SessionId S) (u : Fin S.N_id)
    (bundle : SignalPqxdh.PreKeyBundleInput)
    (st : SignalPqxdh.KeyIndState S) (ds : ModelDriverState S ℓ)
    (hV : ValidCliBadKemState S st ds)
    (hSend : SignalPqxdh.Security.IsSendSessionId S sid)
    (hFresh : st.sessions.any (fun e => e.sid == sid) = false)
    (bIdx sIdx : ℕ) :
    SignalPqxdh.Security.probExpect ($ᵗ List.Vector (BitVec 8) 160)
      (fun t_init => cliKemCorrPotential S P bIdx sIdx st
        { ds with initTapes := (sid, u, bundle, t_init) :: ds.initTapes }) ≤
      cliKemCorrPotential S P bIdx sIdx st ds := by
  have hnone := find?_sessSlotFlatIdx_none_of_fresh S sid st ds hV hSend hFresh
  unfold cliKemCorrPotential cliClause2BadKemPair
  simp only [List.find?_cons]
  by_cases hs : (SignalPqxdh.Security.sessSlotFlatIdx S sid == sIdx) = true
  · have heq : SignalPqxdh.Security.sessSlotFlatIdx S sid = sIdx := beq_iff_eq.mp hs
    have hnone' : ds.initTapes.find? (fun e => SignalPqxdh.Security.sessSlotFlatIdx S e.1 == sIdx) =
        none := by rwa [← heq]
    simp only [hs, hnone']
    cases st.spkBundles.find? (fun e => SignalPqxdh.Security.spkSlotFlatIdx S e.1 == bIdx) with
    | none =>
      dsimp only
      rw [probExpect_tapeKemCoins_eq_sampleCoins32
            (fun r => do
              let seed ← SignalPqxdh.sampleRandom64
              pure (SignalPqxdh.kemHonestExchangeFails P seed r))]
      simp only [evalDist_bind_true_eq_probExpect_comp]
      exact le_of_eq (SignalPqxdh.Security.probExpect_swap _ _ _)
    | some p =>
      rcases p with ⟨idx, bEntry⟩
      dsimp only
      refine le_trans
        (b := SignalPqxdh.Security.probExpect ($ᵗ List.Vector (BitVec 8) 160)
          (fun t_init => 𝒟[(pure (match P.kemEncaps bEntry.pqspkPk (tapeKemCoins t_init) with
            | none => false
            | some (ss, ct) => decide (P.kemDecaps bEntry.pqspkSk ct ≠ some ss)) :
              ProbComp Bool)] {true})) ?_ (le_of_eq ?_)
      · refine SignalPqxdh.Security.probExpect_mono_of_support _ _ _ (fun t_init _ => ?_)
        by_cases hpq : bundle.pqspkB = bEntry.pqspkPk
        · simp [hpq]
        · simp [hpq]
      · rw [probExpect_tapeKemCoins_eq_sampleCoins32
              (fun r => (pure (match P.kemEncaps bEntry.pqspkPk r with
                | none => false
                | some (ss, ct) => decide (P.kemDecaps bEntry.pqspkSk ct ≠ some ss)) :
                  ProbComp Bool)),
            SignalPqxdh.Security.evalDist_bind_true_eq_probExpect]
  · simp only [Bool.not_eq_true] at hs
    simp [hs, SignalPqxdh.Security.probExpect_const]

private theorem bhDrvMirror_wrapper_valid_and_potential_le (S : SignalPqxdh.Setup) {ℓ : ℕ}
    (P : SignalPqxdh.Primitives) (bIdx sIdx : ℕ)
    (m : BHDrvM S ℓ SignalPqxdh.KeyIndResponse)
    (q : SignalPqxdh.KeyIndQuery S)
    (st : SignalPqxdh.KeyIndState S) (ds : ModelDriverState S ℓ)
    (hm :
      (∀ y ∈ support ((m.run ds).run st), ValidCliBadKemState S y.2 y.1.2) ∧
      SignalPqxdh.Security.probExpect ((m.run ds).run st)
        (fun y => cliKemCorrPotential S P bIdx sIdx y.2 y.1.2) ≤
        cliKemCorrPotential S P bIdx sIdx st ds) :
    let m' := (((do
        let r ← m
        modify (fun ds => bhDrvMirror ds q r); return r :
        BHDrvM S ℓ SignalPqxdh.KeyIndResponse).run ds).run st)
    (∀ y ∈ support m', ValidCliBadKemState S y.2 y.1.2) ∧
    SignalPqxdh.Security.probExpect m'
      (fun y => cliKemCorrPotential S P bIdx sIdx y.2 y.1.2) ≤
      cliKemCorrPotential S P bIdx sIdx st ds := by
  intro m'
  have hRunEq :
      m' = ((m.run ds).run st >>= fun y =>
        pure ((y.1.1, bhDrvMirror y.1.2 q y.1.1), y.2)) := by
    dsimp only [m']
    simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
  rw [hRunEq]
  refine ⟨?_, ?_⟩
  · intro y hy
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨z, hz, rfl⟩
    exact (PreservesKemState.bhDrvMirror z.2 z.1.2 q z.1.1).validCliBadKemState (hm.1 z hz)
  · simp only [SignalPqxdh.Security.probExpect_bind, SignalPqxdh.Security.probExpect_pure]
    have hEq : (fun z : (SignalPqxdh.KeyIndResponse × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S =>
        cliKemCorrPotential S P bIdx sIdx z.2 (bhDrvMirror z.1.2 q z.1.1)) =
      (fun z => cliKemCorrPotential S P bIdx sIdx z.2 z.1.2) := by
      ext z
      exact (PreservesKemState.bhDrvMirror z.2 z.1.2 q z.1.1).cliKemCorrPotential_eq P bIdx sIdx
    rw [hEq]
    exact hm.2

private theorem bhRunInitiate_valid_and_potential_le (S : SignalPqxdh.Setup) {ℓ : ℕ}
    (P : SignalPqxdh.Primitives)
    (enc : SignalPqxdh.Bytes → SignalPqxdh.Bytes → SignalPqxdh.Bytes × SignalPqxdh.Bytes)
    (hEnc : ∀ pk, (∀ r, P.kemEncaps pk r = none) ∨ (∀ r, P.kemEncaps pk r = some (enc pk r)))
    (sid : SignalPqxdh.SessionId S) (u : Fin S.N_id) (bundle : SignalPqxdh.PreKeyBundleInput)
    (hSend : SignalPqxdh.Security.IsSendSessionId S sid)
    (bIdx sIdx : ℕ)
    (st : SignalPqxdh.KeyIndState S) (ds : ModelDriverState S ℓ)
    (hV : ValidCliBadKemState S st ds) :
    let m := (((bhRunInitiate S P sid u bundle false).run ds).run st)
    (∀ y ∈ support m, ValidCliBadKemState S y.2 y.1.2) ∧
    SignalPqxdh.Security.probExpect m
      (fun y => cliKemCorrPotential S P bIdx sIdx y.2 y.1.2) ≤
      cliKemCorrPotential S P bIdx sIdx st ds := by
  intro m
  dsimp only [m]
  unfold bhRunInitiate
  simp only [StateT.run_bind, stateT_run_lift_cli, StateT.run_get,
    pure_bind, bind_assoc]
  cases hFresh : st.sessions.any (fun e => e.sid == sid)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases st.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      simp [StateT.run_pure, SignalPqxdh.Security.probExpect_pure, hV]
    | some uPair =>
      rcases uPair with ⟨_, uEntry⟩
      dsimp only
      split_ifs
      · simp [StateT.run_pure, SignalPqxdh.Security.probExpect_pure, hV]
      · simp [StateT.run_pure, SignalPqxdh.Security.probExpect_pure, hV]
      · simp only [StateT.run_bind, stateT_run_lift_cli, stateT_run_monadLift_cli,
          StateT.run_pure, pure_bind, bind_assoc,
          SignalPqxdh.Security.probExpect_bind, SignalPqxdh.Security.probExpect_pure,
          SignalPqxdh.Security.probExpect_const]
        refine ⟨?_, le_rfl⟩
        intro y hy
        simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
        rcases hy with ⟨_, _, rfl⟩
        exact hV
      · rcases hEnc bundle.pqspkB with hNone | hSome
        · simp only [hNone,
            StateT.run_bind, stateT_run_lift_cli, stateT_run_monadLift_cli,
            StateT.run_pure, pure_bind, bind_assoc,
            SignalPqxdh.Security.probExpect_bind, SignalPqxdh.Security.probExpect_pure,
            SignalPqxdh.Security.probExpect_const]
          refine ⟨?_, le_rfl⟩
          intro y hy
          simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
          rcases hy with ⟨_, _, rfl⟩
          exact hV
        · simp only [hSome,
            SignalPqxdh.evalHkdfOrRo, Bool.not_false, ↓reduceIte,
            StateT.run_bind, stateT_run_lift_cli, stateT_run_monadLift_cli,
            pure_bind, bind_assoc]
          refine ⟨?_, ?_⟩
          · intro y hy
            simp only [MonadAttach.mem_support_bind] at hy
            rcases hy with ⟨t_init, _, hy⟩
            rcases hKPR : SignalPqxdh.keyIndPartnerRandKey? P st.respSessions _ with _ | dk
            · rw [hKPR] at hy; dsimp only at hy
              simp only [StateT.run_bind, stateT_run_lift_cli, stateT_run_monadLift_cli,
                StateT.run_set, StateT.run_modify, pure_bind, bind_assoc,
                MonadAttach.mem_support_bind] at hy
              rcases hy with ⟨drKeyRand, _, hy⟩
              rcases hFHP : SignalPqxdh.findHonestPrincipal P st.principals bundle.ikB with _ | _ <;>
                rw [hFHP] at hy <;>
                simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy <;>
                subst hy <;>
                exact validCliBadKemState_cons_initiate S sid u bundle t_init _ _ ds _ st
                  hV hSend hFresh rfl rfl
            · rw [hKPR] at hy; dsimp only at hy
              rcases hFHP : SignalPqxdh.findHonestPrincipal P st.principals bundle.ikB with _ | _ <;>
                rw [hFHP] at hy <;>
                simp only [StateT.run_bind, stateT_run_lift_cli, StateT.run_set, StateT.run_modify,
                  StateT.run_pure, pure_bind, bind_assoc, support_pure, Set.mem_singleton_iff] at hy <;>
                subst hy <;>
                exact validCliBadKemState_cons_initiate S sid u bundle t_init _ _ ds _ st
                  hV hSend hFresh rfl rfl
          · rw [SignalPqxdh.Security.probExpect_bind]
            calc SignalPqxdh.Security.probExpect ($ᵗ List.Vector (BitVec 8) 160) _
                ≤ SignalPqxdh.Security.probExpect ($ᵗ List.Vector (BitVec 8) 160)
                    (fun t_init => cliKemCorrPotential S P bIdx sIdx st
                      { ds with initTapes := (sid, u, bundle, t_init) :: ds.initTapes }) := by
                  refine SignalPqxdh.Security.probExpect_mono_of_support _ _ _ (fun t_init _ => ?_)
                  rcases hKPR : SignalPqxdh.keyIndPartnerRandKey? P st.respSessions _ with _ | dk
                  · dsimp only
                    rcases hFHP : SignalPqxdh.findHonestPrincipal P st.principals bundle.ikB with _ | _ <;>
                      simp only [StateT.run_bind, stateT_run_lift_cli, stateT_run_monadLift_cli,
                        StateT.run_set, StateT.run_modify, StateT.run_pure, pure_bind, bind_assoc,
                        SignalPqxdh.Security.probExpect_bind, SignalPqxdh.Security.probExpect_pure] <;>
                      exact SignalPqxdh.Security.probExpect_const_le_of_support _ _ _ (fun _ _ => le_rfl)
                  · dsimp only
                    rcases hFHP : SignalPqxdh.findHonestPrincipal P st.principals bundle.ikB with _ | _ <;>
                      simp only [StateT.run_bind, stateT_run_lift_cli,
                        StateT.run_set, StateT.run_modify, StateT.run_pure, pure_bind, bind_assoc,
                        SignalPqxdh.Security.probExpect_pure] <;>
                      exact le_rfl
              _ ≤ cliKemCorrPotential S P bIdx sIdx st ds :=
                probExpect_cliKemCorrPotential_initiate_le S P sid u bundle st ds hV hSend hFresh
                  bIdx sIdx
  · simp [StateT.run_pure, SignalPqxdh.Security.probExpect_pure, hV]

private theorem bhDrvKeyInd_valid_and_potential_le (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives)
    (enc : SignalPqxdh.Bytes → SignalPqxdh.Bytes → SignalPqxdh.Bytes × SignalPqxdh.Bytes)
    (hEnc : ∀ pk, (∀ r, P.kemEncaps pk r = none) ∨ (∀ r, P.kemEncaps pk r = some (enc pk r)))
    (bIdx sIdx : ℕ) (q : SignalPqxdh.KeyIndQuery S)
    (st : SignalPqxdh.KeyIndState S) (ds : ModelDriverState S ℓ)
    (hV : ValidCliBadKemState S st ds) :
    (∀ y ∈ support (((bhDrvKeyInd S ℓ P false q).run ds).run st),
      ValidCliBadKemState S y.2 y.1.2) ∧
    SignalPqxdh.Security.probExpect (((bhDrvKeyInd S ℓ P false q).run ds).run st)
      (fun y => cliKemCorrPotential S P bIdx sIdx y.2 y.1.2) ≤
      cliKemCorrPotential S P bIdx sIdx st ds := by
  rcases bhDrvKeyInd_preservesKemState_or_gen_or_init S ℓ P false q st ds with
    hPres | ⟨u, j, rfl⟩ | ⟨u, i, bnd, rfl⟩ | ⟨u, i, bnd, rfl⟩
  · refine ⟨fun y hy => (hPres y hy).validCliBadKemState hV, ?_⟩
    exact SignalPqxdh.Security.probExpect_const_le_of_support _ _ _ (fun y hy =>
      le_of_eq ((hPres y hy).cliKemCorrPotential_eq P bIdx sIdx))
  · unfold bhDrvKeyInd; dsimp only
    apply bhDrvMirror_wrapper_valid_and_potential_le
    unfold SignalPqxdh.pqxdhKeyIndImpl; dsimp only
    simp only [StateT.run_bind, stateT_run_lift_cli, StateT.run_get,
      StateT.run_pure, pure_bind, bind_assoc]
    cases hFresh : st.spkBundles.any (fun (k, _) => k == (u.val, j.val))
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases st.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        simp [StateT.run_pure, SignalPqxdh.Security.probExpect_pure, hV]
      | some uPair =>
        rcases uPair with ⟨_, uEntry⟩
        dsimp only
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
          StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
        refine ⟨?_, ?_⟩
        · intro y hy
          simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
          rcases hy with ⟨spkSk, _, rSpk, _, ⟨pqspkPk, pqspkSk⟩, _, rPq, _, rfl⟩
          exact ⟨SignalPqxdh.Security.validSpkBundlesKem_cons S u j _ st.spkBundles hV.1 hFresh,
                 hV.2.1, hV.2.2⟩
        · simp only [SignalPqxdh.Security.probExpect_bind, SignalPqxdh.Security.probExpect_pure]
          apply SignalPqxdh.Security.probExpect_const_le_of_support; intro spkSk _
          apply SignalPqxdh.Security.probExpect_const_le_of_support; intro rSpk _
          exact probExpect_cliKemCorrPotential_genSPK_le S P u j st ds hV.1 hFresh
            (fun pair rPq => {
              spkSk := spkSk
              spkPk := P.x25519Base spkSk
              spkSig := P.sigSign uEntry.secIKAsign (SignalPqxdh.encodeEC (P.x25519Base spkSk)) rSpk
              pqspkSk := pair.2
              pqspkPk := pair.1
              pqspkSig := P.sigSign uEntry.secIKAsign (SignalPqxdh.encodeKEM pair.1) rPq
            })
            (fun _ _ => rfl) (fun _ _ => rfl) bIdx sIdx
    · simp [StateT.run_pure, SignalPqxdh.Security.probExpect_pure, hV]
  · unfold bhDrvKeyInd; dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · simp [StateT.run_pure, SignalPqxdh.Security.probExpect_pure, hV]
    · exact bhDrvMirror_wrapper_valid_and_potential_le S P bIdx sIdx _ _ st ds
        (bhRunInitiate_valid_and_potential_le S P enc hEnc (.sendOPK u i) u bnd
          trivial bIdx sIdx st ds hV)
  · unfold bhDrvKeyInd; dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · simp [StateT.run_pure, SignalPqxdh.Security.probExpect_pure, hV]
    · exact bhDrvMirror_wrapper_valid_and_potential_le S P bIdx sIdx _ _ st ds
        (bhRunInitiate_valid_and_potential_le S P enc hEnc (.sendNoOPK u i) u bnd
          trivial bIdx sIdx st ds hV)

private theorem cliDrvImpl_valid_and_potential_le (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (enc : SignalPqxdh.Bytes → SignalPqxdh.Bytes → SignalPqxdh.Bytes × SignalPqxdh.Bytes)
    (hEnc : ∀ pk, (∀ r, P.kemEncaps pk r = none) ∨ (∀ r, P.kemEncaps pk r = some (enc pk r)))
    (run : CliRun) (W : PEParams)
    (qep : ℕ) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (mode : BHDrvMode S) (bIdx sIdx : ℕ)
    (q : (cliGameSpec S ℓ (BitVec 512)).Domain)
    (st : SignalPqxdh.KeyIndState S) (ds : ModelDriverState S ℓ)
    (hV : ValidCliBadKemState S st ds) :
    let m := (((cliDrvImpl S ℓ P run W qep decT encT bhNoExtWithSpqr mode q).run ds).run st)
    (∀ y ∈ support m, ValidCliBadKemState S y.2 y.1.2) ∧
    SignalPqxdh.Security.probExpect m
      (fun y => cliKemCorrPotential S P bIdx sIdx y.2 y.1.2) ≤
      cliKemCorrPotential S P bIdx sIdx st ds := by
  intro m
  dsimp only [m]
  rcases q with ((uq | kq) | ctlq) | iq
  · rw [cliDrvImpl_inl_inl_inl]
    refine ⟨?_, ?_⟩
    · intro y hy
      simp only [support_map, Set.mem_image] at hy
      rcases hy with ⟨u, _, rfl⟩
      exact hV
    · refine SignalPqxdh.Security.probExpect_const_le_of_support _ _ _ (fun y hy => ?_)
      simp only [support_map, Set.mem_image] at hy
      rcases hy with ⟨u, _, rfl⟩
      exact le_rfl
  · rw [cliDrvImpl_inl_inl_inr]
    exact bhDrvKeyInd_valid_and_potential_le S ℓ P enc hEnc bIdx sIdx kq st ds hV
  · cases ctlq with
    | startDR sid =>
      rw [cliDrvImpl_inl_inr]
      have hP := cliDrvStart_preservesKemState S ℓ P run W mode sid st ds
      exact ⟨fun y hy => (hP y hy).validCliBadKemState hV,
             SignalPqxdh.Security.probExpect_const_le_of_support _ _ _ (fun y hy =>
               le_of_eq ((hP y hy).cliKemCorrPotential_eq P bIdx sIdx))⟩
  · rw [cliDrvImpl_inr]
    have hP := cliDrvSM_preservesKemState S ℓ run W qep decT encT iq st ds
    exact ⟨fun y hy => (hP y hy).validCliBadKemState hV,
           SignalPqxdh.Security.probExpect_const_le_of_support _ _ _ (fun y hy =>
             le_of_eq ((hP y hy).cliKemCorrPotential_eq P bIdx sIdx))⟩

private theorem simulateQ_cliDrvImpl_valid_and_potential_le (S : SignalPqxdh.Setup) (ℓ : ℕ)
    {Pt α : Type}
    (P : SignalPqxdh.Primitives)
    (enc : SignalPqxdh.Bytes → SignalPqxdh.Bytes → SignalPqxdh.Bytes × SignalPqxdh.Bytes)
    (hEnc : ∀ pk, (∀ r, P.kemEncaps pk r = none) ∨ (∀ r, P.kemEncaps pk r = some (enc pk r)))
    (run : CliRun) (W : PEParams)
    (qep : ℕ) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (mode : BHDrvMode S) (bIdx sIdx : ℕ)
    (oa : OracleComp (cliGameSpec S ℓ (BitVec 512)) α)
    (st : SignalPqxdh.KeyIndState S) (ds : ModelDriverState S ℓ)
    (hV : ValidCliBadKemState S st ds) :
    let m := (((simulateQ (cliDrvImpl S ℓ P run W qep decT encT bhNoExtWithSpqr
      mode) oa).run ds).run st)
    (∀ y ∈ support m, ValidCliBadKemState S y.2 y.1.2) ∧
    SignalPqxdh.Security.probExpect m
      (fun y => cliKemCorrPotential S P bIdx sIdx y.2 y.1.2) ≤
      cliKemCorrPotential S P bIdx sIdx st ds := by
  intro m
  let impl := cliDrvImpl S ℓ P run W qep decT encT bhNoExtWithSpqr mode
  induction oa using OracleComp.inductionOn generalizing st ds with
  | pure a =>
    refine ⟨?_, ?_⟩
    · intro y hy
      simp only [m, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy; exact hV
    · simp [m, simulateQ_pure, StateT.run_pure, SignalPqxdh.Security.probExpect_pure]
  | query_bind q oa ih =>
    dsimp only [m]
    rw [simulateQ_query_bind_run_cli]
    have hStep := cliDrvImpl_valid_and_potential_le S ℓ P enc hEnc run W qep decT encT
      mode bIdx sIdx q st ds hV
    refine ⟨?_, ?_⟩
    · intro y hy
      rw [MonadAttach.mem_support_bind] at hy
      rcases hy with ⟨z, hz, hy⟩
      exact (ih z.1.1 z.2 z.1.2 (hStep.1 z hz)).1 y hy
    · rw [SignalPqxdh.Security.probExpect_bind]
      calc SignalPqxdh.Security.probExpect (((impl q).run ds).run st)
            (fun z => SignalPqxdh.Security.probExpect
              (((simulateQ impl (oa z.1.1)).run z.1.2).run z.2)
              (fun y => cliKemCorrPotential S P bIdx sIdx y.2 y.1.2))
          ≤ SignalPqxdh.Security.probExpect (((impl q).run ds).run st)
              (fun z => cliKemCorrPotential S P bIdx sIdx z.2 z.1.2) :=
            SignalPqxdh.Security.probExpect_mono_of_support _ _ _
              (fun z hz => (ih z.1.1 z.2 z.1.2 (hStep.1 z hz)).2)
        _ ≤ cliKemCorrPotential S P bIdx sIdx st ds := hStep.2

private theorem find?_map_nodup_eq_some {α : Type} (f : α → ℕ) :
    ∀ (xs : List α), (xs.map f).Nodup → ∀ e ∈ xs, xs.find? (fun x => f x == f e) = some e
  | [], _, _, hmem => False.elim (List.not_mem_nil hmem)
  | x :: xs, hnodup, e, hmem => by
    rw [List.map_cons, List.nodup_cons] at hnodup
    rcases List.mem_cons.mp hmem with rfl | hxs
    · simp only [List.find?, beq_self_eq_true]
    · have hne : (f x == f e) = false := by
        rw [beq_eq_false_iff_ne]
        intro heq
        apply hnodup.1
        rw [heq, List.mem_map]
        exact ⟨e, hxs, rfl⟩
      simp only [List.find?, hne]
      exact find?_map_nodup_eq_some f xs hnodup.2 e hxs

private theorem cliClause2BadKemBool_imp_any_double_range (S : SignalPqxdh.Setup) {ℓ : ℕ}
    (P : SignalPqxdh.Primitives)
    (st : SignalPqxdh.KeyIndState S) (ds : ModelDriverState S ℓ)
    (hV : ValidCliBadKemState S st ds)
    (hBad : cliClause2BadKemBool S P st ds = true) :
    ((List.range S.N_spk_tot).any (fun bIdx =>
      (List.range S.N_send_tot).any (fun sIdx =>
        cliClause2BadKemAt S P bIdx sIdx st ds))) = true := by
  unfold cliClause2BadKemBool at hBad
  simp only [List.any_eq_true] at hBad
  rcases hBad with ⟨⟨sid, u, bnd, t_init⟩, ht, ⟨idx, bEntry⟩, hb, hpair⟩
  have hb_lt : SignalPqxdh.Security.spkSlotFlatIdx S idx < S.N_spk_tot :=
    SignalPqxdh.Security.spkSlotFlatIdx_lt S
      (hV.1.1 (idx, bEntry) hb).1 (hV.1.1 (idx, bEntry) hb).2
  have hs_lt : SignalPqxdh.Security.sessSlotFlatIdx S sid < S.N_send_tot :=
    SignalPqxdh.Security.sessSlotFlatIdx_lt S sid (hV.2.1 (sid, u, bnd, t_init) ht).1
  have hfb := SignalPqxdh.Security.find?_spkSlotFlatIdx_eq_some S st.spkBundles hV.1.2
    (idx, bEntry) hb
  have hfs := find?_map_nodup_eq_some (fun e => SignalPqxdh.Security.sessSlotFlatIdx S e.1)
    ds.initTapes hV.2.2 (sid, u, bnd, t_init) ht
  simp only [List.any_eq_true, List.mem_range]
  refine ⟨SignalPqxdh.Security.spkSlotFlatIdx S idx, hb_lt,
          SignalPqxdh.Security.sessSlotFlatIdx S sid, hs_lt, ?_⟩
  unfold cliClause2BadKemAt
  rw [hfb, hfs]
  exact hpair

/-- Bounds the bad-KEM probability of `cliRunBadKemExp` by `N_spk_tot * N_send_tot * δ_kem`. -/
theorem cliBadKemProb_le_bound (S : SignalPqxdh.Setup) (ℓ qep : ℕ) {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (enc : SignalPqxdh.Bytes → SignalPqxdh.Bytes → SignalPqxdh.Bytes × SignalPqxdh.Bytes)
    (hEnc : ∀ pk, (∀ r, P.kemEncaps pk r = none) ∨ (∀ r, P.kemEncaps pk r = some (enc pk r)))
    (run : CliRun) (W : PEParams)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (δ_kem : ℝ) (hKem : SignalPqxdh.KemDeltaCorrectReal P δ_kem)
    (A : CliGameAdversary S ℓ (BitVec 512)) :
    (𝒟[cliRunBadKemExp S P run W ℓ qep decT encT A] {true}).toReal ≤
      (S.N_spk_tot : ℝ) * (S.N_send_tot : ℝ) * δ_kem := by
  let runSim : ProbComp (Bool × (Bool × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S) := do
    let bBit ← $ᵗ Bool
    let y ←
      (runCliDriver S ℓ P run W qep decT encT bhNoExtWithSpqr
        (fun _ _ _ _ _ => some bBit) A).run (SignalPqxdh.KeyIndState.empty S true)
    return (bBit, y)
  have hExpEq :
      cliRunBadKemExp S P run W ℓ qep decT encT A =
        (runSim >>= fun (_, y) => pure (cliClause2BadKemBool S P y.2 y.1.2)) := by
    unfold cliRunBadKemExp runSim
    simp only [bind_assoc, pure_bind]
  rw [hExpEq]
  have hSim := fun bIdx sIdx (bBit : Bool) =>
    simulateQ_cliDrvImpl_valid_and_potential_le S ℓ P enc hEnc run W qep decT encT
      (fun _ _ _ _ _ => some bBit) bIdx sIdx A.run (SignalPqxdh.KeyIndState.empty S true) {}
      (validCliBadKemState_empty S ℓ true)
  have hV_runSim : ∀ x ∈ support runSim, ValidCliBadKemState S x.2.2 x.2.1.2 := by
    intro x hx
    simp only [runSim, runCliDriver, MonadAttach.mem_support_bind,
      support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨bBit, _, y, hy, rfl⟩
    exact (hSim 0 0 bBit).1 y hy
  have hPair_le : ∀ bIdx sIdx : ℕ,
      (𝒟[runSim >>= fun (_, y) => pure (cliClause2BadKemAt S P bIdx sIdx y.2 y.1.2)] {true}).toReal ≤
        δ_kem := by
    intro bIdx sIdx
    have h_enn :
        𝒟[runSim >>= fun (_, y) => pure (cliClause2BadKemAt S P bIdx sIdx y.2 y.1.2)] {true} ≤
          cliKemCorrPotential S P bIdx sIdx (SignalPqxdh.KeyIndState.empty S true)
            ({} : ModelDriverState S ℓ) := by
      rw [SignalPqxdh.Security.evalDist_bind_true_eq_probExpect]
      simp only [runSim, runCliDriver, SignalPqxdh.Security.probExpect_bind,
        SignalPqxdh.Security.probExpect_pure]
      apply SignalPqxdh.Security.probExpect_const_le_of_support; intro bBit _
      calc SignalPqxdh.Security.probExpect
            (((simulateQ (cliDrvImpl S ℓ P run W qep decT encT bhNoExtWithSpqr
              (fun _ _ _ _ _ => some bBit)) A.run).run {}).run
                (SignalPqxdh.KeyIndState.empty S true))
            (fun y => 𝒟[(pure (cliClause2BadKemAt S P bIdx sIdx y.2 y.1.2) : ProbComp Bool)] {true})
          ≤ SignalPqxdh.Security.probExpect
              (((simulateQ (cliDrvImpl S ℓ P run W qep decT encT bhNoExtWithSpqr
                (fun _ _ _ _ _ => some bBit)) A.run).run {}).run
                  (SignalPqxdh.KeyIndState.empty S true))
              (fun y => cliKemCorrPotential S P bIdx sIdx y.2 y.1.2) :=
            SignalPqxdh.Security.probExpect_mono_of_support _ _ _
              (fun y _ => evalDist_cliClause2BadKemAt_le_potential S P bIdx sIdx y.2 y.1.2)
        _ ≤ cliKemCorrPotential S P bIdx sIdx (SignalPqxdh.KeyIndState.empty S true) {} :=
            (hSim bIdx sIdx bBit).2
    have hInitEq :
        cliKemCorrPotential S P bIdx sIdx (SignalPqxdh.KeyIndState.empty S true)
          ({} : ModelDriverState S ℓ) =
        𝒟[do
          let seed ← SignalPqxdh.sampleRandom64
          let r ← SignalPqxdh.sampleCoins32
          pure (SignalPqxdh.kemHonestExchangeFails P seed r)] {true} := rfl
    rw [hInitEq] at h_enn
    exact le_trans
      ((ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr h_enn)
      hKem
  calc (𝒟[runSim >>= fun (_, y) => pure (cliClause2BadKemBool S P y.2 y.1.2)] {true}).toReal
      ≤ (𝒟[runSim >>= fun (_, y) =>
          pure ((List.range S.N_spk_tot).any (fun bIdx =>
            (List.range S.N_send_tot).any (fun sIdx =>
              cliClause2BadKemAt S P bIdx sIdx y.2 y.1.2)))] {true}).toReal :=
        SignalPqxdh.Security.toReal_bind_bool_mono_of_support runSim _ _
          (fun x hx hBad => cliClause2BadKemBool_imp_any_double_range S P x.2.2 x.2.1.2
            (hV_runSim x hx) hBad)
    _ ≤ ∑ bIdx ∈ Finset.range S.N_spk_tot,
          (𝒟[runSim >>= fun (_, y) =>
            pure ((List.range S.N_send_tot).any (fun sIdx =>
              cliClause2BadKemAt S P bIdx sIdx y.2 y.1.2))] {true}).toReal :=
        SignalPqxdh.Security.toReal_any_range_le_sum runSim S.N_spk_tot
          (fun bIdx x => (List.range S.N_send_tot).any (fun sIdx =>
            cliClause2BadKemAt S P bIdx sIdx x.2.2 x.2.1.2))
    _ ≤ ∑ bIdx ∈ Finset.range S.N_spk_tot,
          ∑ sIdx ∈ Finset.range S.N_send_tot,
            (𝒟[runSim >>= fun (_, y) =>
              pure (cliClause2BadKemAt S P bIdx sIdx y.2 y.1.2)] {true}).toReal :=
        Finset.sum_le_sum (fun bIdx _ =>
          SignalPqxdh.Security.toReal_any_range_le_sum runSim S.N_send_tot
            (fun sIdx x => cliClause2BadKemAt S P bIdx sIdx x.2.2 x.2.1.2))
    _ ≤ ∑ _bIdx ∈ Finset.range S.N_spk_tot,
          ∑ _sIdx ∈ Finset.range S.N_send_tot, δ_kem :=
        Finset.sum_le_sum (fun bIdx _ => Finset.sum_le_sum (fun sIdx _ => hPair_le bIdx sIdx))
    _ = (S.N_spk_tot : ℝ) * (S.N_send_tot : ℝ) * δ_kem := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

theorem two_mul_cliBadKemProb_le_kemCorrTerm (S : SignalPqxdh.Setup) (ℓ qep : ℕ) {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (enc : SignalPqxdh.Bytes → SignalPqxdh.Bytes → SignalPqxdh.Bytes × SignalPqxdh.Bytes)
    (hEnc : ∀ pk, (∀ r, P.kemEncaps pk r = none) ∨ (∀ r, P.kemEncaps pk r = some (enc pk r)))
    (run : CliRun) (W : PEParams)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (δ_kem : ℝ≥0∞) (hKem : SignalPqxdh.KemDeltaCorrect P δ_kem)
    (A : CliGameAdversary S ℓ (BitVec 512)) :
    2 * 𝒟[cliRunBadKemExp S P run W ℓ qep decT encT A] {true} ≤
      SignalPqxdh.Security.kemDecapsFailureTerm S δ_kem := by
  set δ' : ℝ≥0∞ := min δ_kem 1
  have hδ'_ne_top : δ' ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  set p := 𝒟[cliRunBadKemExp S P run W ℓ qep decT encT A] {true}
  have hp_ne_top : p ≠ ⊤ := measure_ne_top _ _
  have h2p_ne_top : 2 * p ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofNat_ne_top hp_ne_top
  have hReal : 2 * p ≤ ENNReal.ofReal (SignalPqxdh.Security.kemDecapsFailureTermReal S δ'.toReal) := by
    rw [← ENNReal.ofReal_toReal h2p_ne_top]
    apply ENNReal.ofReal_le_ofReal
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat]
    have hBound := cliBadKemProb_le_bound S ℓ qep P enc hEnc run W decT encT
      δ'.toReal hKem.min_one_real A
    unfold SignalPqxdh.Security.kemDecapsFailureTermReal
    linarith
  rw [SignalPqxdh.Security.ofReal_kemDecapsFailureTermReal S hδ'_ne_top] at hReal
  exact hReal.trans (SignalPqxdh.Security.kemDecapsFailureTerm_mono (min_le_left δ_kem 1))

/-- Bounds `2 * 𝒟[cliRunBadKemExp ...] {true}` at `modelPrims X W` by `kemDecapsFailureTerm S δ_kem`. -/
theorem two_mul_cliBadKemProb_modelPrims_le_kemCorrTerm
    (S : SignalPqxdh.Setup) (ℓ qep : ℕ) {Pt : Type}
    (X : UnreachedPqxdhPrimitives) (run : CliRun) (W : PEParams)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (δ_kem : ℝ≥0∞) (hKem : SignalPqxdh.KemDeltaCorrect (modelPrims X W) δ_kem)
    (A : CliGameAdversary S ℓ (BitVec 512)) :
    2 * 𝒟[cliRunBadKemExp S (modelPrims X W) run W ℓ qep decT encT A] {true} ≤
      SignalPqxdh.Security.kemDecapsFailureTerm S δ_kem :=
  two_mul_cliBadKemProb_le_kemCorrTerm S ℓ qep (modelPrims X W)
    (fun pk r =>
      let (ct, ss) := W.Q.encaps (u8Vec SignalPqxdh.kyberPkLen pk) (u8Vec 32 r)
      (vecU8 ss, vecU8 ct))
    (fun pk => by
      dsimp only [modelPrims, blockLevelPrims]
      by_cases hpk : (pk.length == SignalPqxdh.kyberPkLen) = true
      · exact Or.inr (fun r => by simp [hpk])
      · exact Or.inl (fun r => by simp [hpk]))
    run W decT encT δ_kem hKem A

end CryptoVerification.E2E
