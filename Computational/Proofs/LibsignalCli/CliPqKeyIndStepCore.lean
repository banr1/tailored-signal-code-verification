/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.LibsignalCli.CliPqAdapterDefs
public import Computational.Specifications.Assumptions.KeyInd1KeyReal
import Computational.Proofs.E2E.BhKindCouplingV1
import Computational.Proofs.GameHop.Rnd
import Computational.Proofs.ReductionDsl.SM.GameCosted
import ProofLib.SepLogic.WP.StateNorm
import VCVio.EvalDist.Monad.Basic

/-!
# Helpers for 1-key `KeyInd`, `Unif`, and `startDR` adapter step coupling

**Checked by Lean.** Proves tape-marginal `DEq` equivalences, `spkBundles` replacement commutation
for `pqxdhKeyIndImpl` and `pqxdhKeyIndImpl1KeyReal`, projection `DEq` for `bhDrvKeyInd`, and
monotonicity of `CliAdapterInstRel`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.constructorNameAsVariable false
set_option linter.unusedSimpArgs false

open scoped ENNReal BigOperators
open ReductionDsl OracleComp OracleSpec MeasureTheory

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  CryptoGames.LibsignalSessionApi HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme
  MACScheme WireAEAD FSAEAD CryptoGames.Ratchet.LibsignalSim CryptoGames.FSAEAD.Thm5
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.LibsignalSpqrV1 CryptoVerification.SignalSession

/-! ## Monad, `DEq`, and tape-marginal helpers -/

@[simp]
theorem stateT_lift_run_cli {m : Type → Type} [Monad m] {σ α : Type}
    (x : m α) (s : σ) :
    (StateT.lift x : StateT σ m α).run s = (x >>= fun a => pure (a, s)) := rfl

@[simp]
theorem stateT_monadLift_run_cli {m : Type → Type} [Monad m] {σ α : Type}
    (x : m α) (s : σ) :
    (liftM x : StateT σ m α).run s = (x >>= fun a => pure (a, s)) := rfl

theorem stateT_run_get_bind_cli {m : Type → Type} [Monad m] [LawfulMonad m] {σ α : Type}
    (k : σ → StateT σ m α) (s : σ) :
    ((get >>= k : StateT σ m α).run s) = (k s).run s := by
  simp [StateT.run_bind, StateT.run_get]

/-- Extract Alice's 256-bit initial ratchet coins from the 32-byte DR initiate tape `t_dr`. -/
def cliTape32AliceCoins (t_dr : List.Vector (BitVec 8) 32) : BitVec 256 :=
  HKDF.bytesToKey32 t_dr.toList

private def wordToVec32Step (w : BitVec 256) : List.Vector (BitVec 8) 32 :=
  ⟨HMAC.keyToBytes32 w, by simp [HMAC.keyToBytes32]⟩

private theorem bijective_wordToVec32Step : Function.Bijective wordToVec32Step :=
  Function.bijective_iff_has_inverse.mpr
    ⟨cliTape32AliceCoins, bytesToKey32_keyToBytes32,
     fun v => Subtype.ext (keyToBytes32_bytesToKey32 v.toList v.2)⟩

private theorem bijective_cliTape32AliceCoins : Function.Bijective cliTape32AliceCoins :=
  Function.bijective_iff_has_inverse.mpr
    ⟨wordToVec32Step, fun v => Subtype.ext (keyToBytes32_bytesToKey32 v.toList v.2),
     bytesToKey32_keyToBytes32⟩

theorem deq_cliTape32_aliceCoins :
    CryptoGames.Lazy.DEq
      (do
        let t_dr ← ($ᵗ List.Vector (BitVec 8) 32 : ProbComp (List.Vector (BitVec 8) 32))
        return cliTape32AliceCoins t_dr)
      ($ᵗ BitVec 256 : ProbComp (BitVec 256)) :=
  fun F => ((Computational.Proofs.GameHop.Rnd.evalDistEq_uniformSample_return_of_bijective
    bijective_cliTape32AliceCoins).bind_left F).evalDist_eq

private theorem evalDistEq_vec32_sampleBytes32 {α : Type}
    (k : SignalPqxdh.Bytes → ProbComp α) :
    (do let v ← ($ᵗ List.Vector (BitVec 8) 32 : ProbComp _); k (vecU8 v)) =ᵈ
      (do let bs ← SignalPqxdh.sampleBytes32; k bs) := by
  have heq : (SignalPqxdh.sampleBytes32 : ProbComp SignalPqxdh.Bytes) =
      (fun w => vecU8 (wordToVec32Step w)) <$> ($ᵗ BitVec 256 : ProbComp (BitVec 256)) := by
    unfold SignalPqxdh.sampleBytes32
    congr 1; funext w
    exact word256ToBytes_eq_toU8_keyToBytes32 w
  rw [heq, bind_map_left]
  exact (Computational.Proofs.GameHop.Rnd.evalDistEq_uniformSample_bind_of_bijective
    bijective_wordToVec32Step (fun v => k (vecU8 v))).symm

private def joinTape160Step
    (p : (List.Vector (BitVec 8) 32 × List.Vector (BitVec 8) 32) ×
      List.Vector (BitVec 8) 96) : List.Vector (BitVec 8) 160 :=
  List.Vector.ofFn (fun k : Fin 160 =>
    if h : k.val < 32 then
      p.1.1.get ⟨k.val, h⟩
    else if (k.val - 32) % 4 = 0 then
      p.1.2.get ⟨(k.val - 32) / 4, by omega⟩
    else
      p.2.get ⟨3 * ((k.val - 32) / 4) + ((k.val - 32) % 4 - 1), by omega⟩)

private def splitTape160Step (t : List.Vector (BitVec 8) 160) :
    (List.Vector (BitVec 8) 32 × List.Vector (BitVec 8) 32) ×
      List.Vector (BitVec 8) 96 :=
  ((List.Vector.ofFn (fun i : Fin 32 => t.get ⟨i.val, by omega⟩),
    List.Vector.ofFn (fun i : Fin 32 => t.get ⟨32 + 4 * i.val, by omega⟩)),
   List.Vector.ofFn (fun j : Fin 96 =>
    t.get ⟨32 + 4 * (j.val / 3) + (j.val % 3 + 1), by omega⟩))

private theorem splitTape160Step_joinTape160Step
    (p : (List.Vector (BitVec 8) 32 × List.Vector (BitVec 8) 32) ×
      List.Vector (BitVec 8) 96) :
    splitTape160Step (joinTape160Step p) = p := by
  rcases p with ⟨⟨ek, kem⟩, pad⟩
  ext : 1
  · ext : 1
    · apply List.Vector.ext; intro i
      simp only [splitTape160Step, joinTape160Step, List.Vector.get_ofFn]
      have hi : i.val < 32 := i.2
      simp [hi]
    · apply List.Vector.ext; intro i
      simp only [splitTape160Step, joinTape160Step, List.Vector.get_ofFn]
      have h1 : ¬ (32 + 4 * i.val < 32) := by omega
      simp [h1]
  · apply List.Vector.ext; intro j
    simp only [splitTape160Step, joinTape160Step, List.Vector.get_ofFn]
    have h1 : ¬ (32 + 4 * (j.val / 3) + (j.val % 3 + 1) < 32) := by omega
    have h2 : (32 + 4 * (j.val / 3) + (j.val % 3 + 1) - 32) % 4 ≠ 0 := by omega
    have h3 : 3 * ((32 + 4 * (j.val / 3) + (j.val % 3 + 1) - 32) / 4) +
        ((32 + 4 * (j.val / 3) + (j.val % 3 + 1) - 32) % 4 - 1) = j.val := by omega
    simp [h1, h2, h3]

private theorem joinTape160Step_splitTape160Step (t : List.Vector (BitVec 8) 160) :
    joinTape160Step (splitTape160Step t) = t := by
  apply List.Vector.ext; intro k
  simp only [joinTape160Step, splitTape160Step, List.Vector.get_ofFn]
  split_ifs with h1 h2
  · rfl
  · congr 1; ext; dsimp only; omega
  · congr 1; ext; dsimp only; omega

private theorem bijective_splitTape160Step : Function.Bijective splitTape160Step :=
  Function.bijective_iff_has_inverse.mpr
    ⟨joinTape160Step, joinTape160Step_splitTape160Step, splitTape160Step_joinTape160Step⟩

private theorem vector_toList_getElem_step {α : Type} {n : ℕ}
    (v : List.Vector α n) (i : ℕ) (hi : i < v.toList.length) :
    v.toList[i] = v.get ⟨i, by simpa [List.Vector.toList_length] using hi⟩ := by
  rcases v with ⟨l, rfl⟩
  rfl

private theorem tapeEkASk_eq_splitTape160Step (t : List.Vector (BitVec 8) 160) :
    CryptoVerification.E2E.tapeEkASk t = vecU8 (splitTape160Step t).1.1 := by
  unfold CryptoVerification.E2E.tapeEkASk vecU8
  apply congrArg toU8
  apply List.ext_getElem
  · simp [List.Vector.toList_length]
  · intro i hi1 hi2
    have hi32 : i < 32 := by simpa [List.Vector.toList_length] using hi2
    rw [List.getElem_take,
        vector_toList_getElem_step t i (by simp [List.Vector.toList_length]; omega),
        vector_toList_getElem_step _ i hi2]
    simp only [splitTape160Step, List.Vector.get_ofFn]

theorem deq_tape160_ekASk_kemCoins :
    CryptoGames.Lazy.DEq
      (do
        let t_init ← ($ᵗ List.Vector (BitVec 8) 160 : ProbComp (List.Vector (BitVec 8) 160))
        return (CryptoVerification.E2E.tapeEkASk t_init,
                CryptoVerification.E2E.tapeKemCoins t_init))
      (do
        let ekASk ← SignalPqxdh.sampleScalar32
        let kemCoins ← SignalPqxdh.sampleCoins32
        return (ekASk, kemCoins)) := by
  have hEq :
      (do
        let t_init ← ($ᵗ List.Vector (BitVec 8) 160 : ProbComp (List.Vector (BitVec 8) 160))
        return (CryptoVerification.E2E.tapeEkASk t_init,
                CryptoVerification.E2E.tapeKemCoins t_init)) =ᵈ
      (do
        let ekASk ← SignalPqxdh.sampleScalar32
        let kemCoins ← SignalPqxdh.sampleCoins32
        return (ekASk, kemCoins)) := by
    have hlhs :
        (do
          let t_init ← ($ᵗ List.Vector (BitVec 8) 160 : ProbComp (List.Vector (BitVec 8) 160))
          return (CryptoVerification.E2E.tapeEkASk t_init,
                  CryptoVerification.E2E.tapeKemCoins t_init)) =
        (fun p => (vecU8 p.1, vecU8 p.2)) <$>
          ((fun t => (splitTape160Step t).1) <$>
            ($ᵗ List.Vector (BitVec 8) 160 : ProbComp (List.Vector (BitVec 8) 160))) := by
      rw [Functor.map_map]
      simp only [map_eq_bind_pure_comp, Function.comp_def, tapeEkASk_eq_splitTape160Step]
      rfl
    rw [hlhs]
    refine (((Computational.Proofs.GameHop.Rnd.evalDistEq_marginal_fst_of_bijective
        bijective_splitTape160Step).trans
      Computational.Proofs.GameHop.Rnd.evalDistEq_uniformSample_prod).map
      (fun p => (vecU8 p.1, vecU8 p.2))).trans ?_
    unfold SignalPqxdh.sampleScalar32 SignalPqxdh.sampleCoins32
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    exact (evalDistEq_vec32_sampleBytes32 fun ekASk =>
        do let v ← ($ᵗ List.Vector (BitVec 8) 32 : ProbComp _); pure (ekASk, vecU8 v)).trans
      (EvalDistEq.bind_right _ fun ekASk =>
        evalDistEq_vec32_sampleBytes32 fun kemCoins => pure (ekASk, kemCoins))
  exact fun F => (hEq.bind_left F).evalDist_eq

@[simp]
theorem simulateQ_cliE2EDrvImplWith_liftM_query {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (q : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain) :
    simulateQ (cliE2EDrvImplWith P ki C K qep decT encT)
      (liftM ((unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).query q) :
        OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) _) =
    cliE2EDrvImplWith P ki C K qep decT encT q := by
  simp [simulateQ_query, OracleSpec.query_def]

/-! ## `spkBundles` replacement and `KeyInd` projection `DEq` -/

/-- Coupling when `c_ad` is a deterministic function `g_ad (r, st_cli')` of a computation `c₂`
that is `DEq` to the `(r, st_cli')`-projection of `c_cli`. -/
theorem cliAdapterStepCoupled_of_proj {S : SignalPqxdh.Setup} {ℓ : ℕ} {α : Type}
    {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {b : Bool} {qStart' : ℕ} {qs_rem' : ℕ → ℕ}
    (c_cli : ProbComp ((α × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S))
    (c₂ : ProbComp (α × SignalPqxdh.KeyIndState S))
    (g_ad : α × SignalPqxdh.KeyIndState S → (α × CliAdapterState S) × BHE2EDrvState S ℓ)
    (c_ad : ProbComp ((α × CliAdapterState S) × BHE2EDrvState S ℓ))
    (hProj : CryptoGames.Lazy.DEq (c_cli >>= fun x => pure (x.1.1, x.2)) c₂)
    (hAd : CryptoGames.Lazy.DEq c_ad (c₂ >>= fun p => pure (g_ad p)))
    (hInv : ∀ x ∈ support c_cli,
      x.1.1 = (g_ad (x.1.1, x.2)).1.1 ∧
      CliAdapterDrvRel S ℓ X W b qStart' qs_rem'
        x.2 x.1.2 (g_ad (x.1.1, x.2)).1.2 (g_ad (x.1.1, x.2)).2) :
    cliAdapterStepCoupled X W b qStart' qs_rem' c_cli c_ad := by
  refine ⟨c_cli >>= fun x => pure (x, g_ad (x.1.1, x.2)), ?_, ?_, ?_⟩
  · simp [CryptoGames.Lazy.DEq, map_eq_bind_pure_comp, bind_assoc]
  · have hMap : (Prod.snd <$> (c_cli >>= fun x => pure (x, g_ad (x.1.1, x.2)))) =
        ((c_cli >>= fun x => pure (x.1.1, x.2)) >>= fun p => pure (g_ad p)) := by
      simp [map_eq_bind_pure_comp, bind_assoc]
    rw [hMap]
    exact (hProj.bind_left (fun p => pure (g_ad p))).trans hAd.symm
  · intro x y hmem
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hmem
    rcases hmem with ⟨x', hx', hxy⟩
    rcases Prod.mk.inj hxy with ⟨rfl, rfl⟩
    exact hInv x hx'

/-- True when `kq` is `.corruptIK u` and `u` is a promoted no-OPK responder in `instMeta`. -/
def cliKiNoOpkCorrupt {S : SignalPqxdh.Setup}
    (instMeta : List (ModelDriverInstanceMeta S)) (kq : SignalPqxdh.KeyIndQuery S) : Bool :=
  match kq with
  | .corruptIK u => bhNoOpkRespPromoted instMeta u
  | _ => false

theorem cliComposedAdapterImplWith_keyInd_run {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (kq : SignalPqxdh.KeyIndQuery S) (σ_ad : CliAdapterState S) (σ_e2e : BHE2EDrvState S ℓ) :
    (((cliComposedAdapterImplWith P ki C K qep decT encT (.inl (.inl (.inr kq)))).run σ_ad).run σ_e2e) =
      if !bhDrvKiQueryOk P σ_e2e.toModelDriverBase kq then
        pure ((.noneResp, (σ_ad.1, σ_ad.2.1, bhBaseMirror σ_ad.2.2 kq .noneResp)), σ_e2e)
      else if cliKiNoOpkCorrupt σ_e2e.instMeta kq then
        pure ((.noneResp, (σ_ad.1, σ_ad.2.1, bhBaseMirror σ_ad.2.2 kq .noneResp)), σ_e2e)
      else
        do
          let (kr, st') ← (ki kq).run σ_e2e.st
          return ((kr, (σ_ad.1, σ_ad.2.1, bhBaseMirror σ_ad.2.2 kq kr)),
            bhE2EMirror { σ_e2e with st := st' } kq kr) := by
  dsimp [cliComposedAdapterImplWith, cliAdapterStepImplWith, bhShallowAdapterImpl,
    bhShallowAdapterGameStep, bhShallowQueryTarget, bhShallowStepMirrorGuard]
  simp only [simulateQ_bind, simulateQ_cliE2EDrvImplWith_liftM_query, simulateQ_pure,
    id_map, pure_bind, bind_assoc, StateT.run_bind, StateT.run_pure,
    map_eq_bind_pure_comp, Function.comp_def]
  unfold cliE2EDrvImplWith
  cases kq <;>
    cases h : bhDrvKiQueryOk P σ_e2e.toModelDriverBase _ <;>
    simp [cliKiNoOpkCorrupt, h, StateT.run_bind, StateT.run_get, StateT.run_pure, StateT.run_set,
      StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc];
  cases hProm : bhNoOpkRespPromoted σ_e2e.instMeta _ <;>
    simp [hProm, StateT.run_bind, StateT.run_pure, StateT.run_set,
      StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc]

abbrev cliReplaceSpkBundles {S : SignalPqxdh.Setup} (st : SignalPqxdh.KeyIndState S)
    (spks : List ((ℕ × ℕ) × SignalPqxdh.SpkBundleEntry)) : SignalPqxdh.KeyIndState S :=
  { st with spkBundles := spks }

@[simp] theorem isFreshKeyIndSession_cliReplaceSpkBundles {S : SignalPqxdh.Setup}
    (st₁ : SignalPqxdh.KeyIndState S)
    (spks₂ : List ((ℕ × ℕ) × SignalPqxdh.SpkBundleEntry))
    (sid : SignalPqxdh.SessionId S) :
    SignalPqxdh.isKeyIndSessionTestable (cliReplaceSpkBundles st₁ spks₂) sid =
      SignalPqxdh.isKeyIndSessionTestable st₁ sid := rfl

theorem eq_cliReplaceSpkBundles_of_cliKeyIndStateRel {S : SignalPqxdh.Setup}
    {P : SignalPqxdh.Primitives} {st₁ st₂ : SignalPqxdh.KeyIndState S}
    (hRel : CliKeyIndStateRel P st₁ st₂) :
    st₂ = cliReplaceSpkBundles st₁ st₂.spkBundles := by
  cases st₁; cases st₂
  dsimp [cliReplaceSpkBundles]
  congr 1
  · exact hRel.secb_e2e.trans hRel.secb_cli.symm
  · exact hRel.principals_eq.symm
  · exact hRel.opkEntries_eq.symm
  · exact hRel.sessions_eq.symm
  · exact hRel.respSessions_eq.symm
  · exact hRel.usedRecvOPK_eq.symm
  · exact hRel.usedRecvNoOPK_eq.symm
  · exact hRel.usedKyberTriples_eq.symm
  · exact hRel.roCache_eq.symm
  · exact hRel.advKeys_eq.symm

theorem forall2_cliSpkBundles_any {spks₁ spks₂ : List ((ℕ × ℕ) × SignalPqxdh.SpkBundleEntry)}
    (h : List.Forall₂ CliSpkBundleRel spks₁ spks₂)
    (f : (ℕ × ℕ) × SignalPqxdh.SpkBundleEntry → Bool)
    (hf : ∀ x₁ x₂, CliSpkBundleRel x₁ x₂ → f x₁ = f x₂) :
    spks₁.any f = spks₂.any f := by
  induction h with
  | nil => rfl
  | cons hhead _ ih => simp [List.any_cons, hf _ _ hhead, ih]

private theorem forall2_cliSpkBundles_koskBundleOk (P : SignalPqxdh.Primitives)
    (principals : List (ℕ × SignalPqxdh.PrincipalEntry))
    {spks₁ spks₂ : List ((ℕ × ℕ) × SignalPqxdh.SpkBundleEntry)}
    (h : List.Forall₂ CliSpkBundleRel spks₁ spks₂)
    (opkEntries : List ((ℕ × ℕ × ℕ) × SignalPqxdh.OpkEntry))
    (advKeys : List (SignalPqxdh.Bytes × SignalPqxdh.Bytes))
    (bundle : SignalPqxdh.PreKeyBundleInput) :
    SignalPqxdh.koskBundleOk P principals spks₁ opkEntries advKeys bundle =
      SignalPqxdh.koskBundleOk P principals spks₂ opkEntries advKeys bundle := by
  unfold SignalPqxdh.koskBundleOk SignalPqxdh.isGameSpk
  have hg :
      (spks₁.any fun (_, b) => P.pow8 b.spkPk == P.pow8 bundle.spkB) =
      (spks₂.any fun (_, b) => P.pow8 b.spkPk == P.pow8 bundle.spkB) := by
    refine forall2_cliSpkBundles_any h _ fun ⟨_, _⟩ ⟨_, _⟩ hx => ?_
    dsimp only; rw [hx.2.2.1]
  rw [hg]

private theorem forall2_cliSpkBundles_checkBundleProvenance (P : SignalPqxdh.Primitives)
    (principals : List (ℕ × SignalPqxdh.PrincipalEntry))
    {spks₁ spks₂ : List ((ℕ × ℕ) × SignalPqxdh.SpkBundleEntry)}
    (h : List.Forall₂ CliSpkBundleRel spks₁ spks₂)
    (opkEntries : List ((ℕ × ℕ × ℕ) × SignalPqxdh.OpkEntry))
    (bundle : SignalPqxdh.PreKeyBundleInput) :
    SignalPqxdh.checkBundleProvenance P principals spks₁ opkEntries bundle =
      SignalPqxdh.checkBundleProvenance P principals spks₂ opkEntries bundle := by
  unfold SignalPqxdh.checkBundleProvenance
  rcases SignalPqxdh.findHonestPrincipal P principals bundle.ikB with _ | ⟨k, _⟩
  · rfl
  · dsimp only
    have h1 : (spks₁.any fun ((u, _), b) => u == k && P.pow8 b.spkPk == P.pow8 bundle.spkB) =
        (spks₂.any fun ((u, _), b) => u == k && P.pow8 b.spkPk == P.pow8 bundle.spkB) := by
      refine forall2_cliSpkBundles_any h _ fun ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩ hx => ?_
      rcases hx with ⟨hidx, _, hspk, _⟩; cases hidx; dsimp only; rw [hspk]
    have h2 : (spks₁.any fun ((u, _), b) => u == k && b.pqspkPk == bundle.pqspkB) =
        (spks₂.any fun ((u, _), b) => u == k && b.pqspkPk == bundle.pqspkB) := by
      refine forall2_cliSpkBundles_any h _ fun ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩ hx => ?_
      rcases hx with ⟨hidx, _, _, _, _, hpq, _⟩; cases hidx; dsimp only; rw [hpq]
    rw [h1, h2]

theorem find_cliSpkBundles_rel_of_forall2
    {spks₁ spks₂ : List ((ℕ × ℕ) × SignalPqxdh.SpkBundleEntry)}
    (h : List.Forall₂ CliSpkBundleRel spks₁ spks₂) (target : ℕ × ℕ) :
    (spks₁.find? (fun x => x.1 == target) = none ∧
     spks₂.find? (fun x => x.1 == target) = none) ∨
    ∃ x₁ x₂,
      spks₁.find? (fun x => x.1 == target) = some x₁ ∧
      spks₂.find? (fun x => x.1 == target) = some x₂ ∧
      CliSpkBundleRel x₁ x₂ := by
  have hf :
      match spks₁.find? (fun (idx, _) => idx == target),
            spks₂.find? (fun (idx, _) => idx == target) with
      | none, none => True
      | some x₁, some x₂ => CliSpkBundleRel x₁ x₂
      | _, _ => False := by
    induction h with
    | nil => trivial
    | cons hhead _ ih =>
      rcases hhead with ⟨hidx, hrest⟩
      simp only [List.find?_cons]
      rw [hidx]
      cases (_ == target)
      · exact ih
      · exact ⟨hidx, hrest⟩
  generalize h1 : spks₁.find? (fun (idx, _) => idx == target) = o1 at hf
  generalize h2 : spks₂.find? (fun (idx, _) => idx == target) = o2 at hf
  cases o1 with
  | none =>
    cases o2 with
    | none => exact Or.inl ⟨rfl, rfl⟩
    | some _ => exact False.elim hf
  | some x₁ =>
    cases o2 with
    | none => exact False.elim hf
    | some x₂ => exact Or.inr ⟨x₁, x₂, rfl, rfl, hf⟩

def cliUpdateSpkBundlesForQuery {S : SignalPqxdh.Setup} (kq : SignalPqxdh.KeyIndQuery S)
    (spks₂ : List ((ℕ × ℕ) × SignalPqxdh.SpkBundleEntry))
    (r : SignalPqxdh.KeyIndResponse)
    (st₁' : SignalPqxdh.KeyIndState S) : List ((ℕ × ℕ) × SignalPqxdh.SpkBundleEntry) :=
  match kq, r with
  | .genSPK _ _, .bundleResp _ =>
    match st₁'.spkBundles with
    | head :: _ => head :: spks₂
    | [] => spks₂
  | .revealSpkSk u j, .spkSkResp _ =>
    spks₂.map (fun (idx, b) =>
      if idx == (u.val, j.val) then (idx, { b with revealed := true }) else (idx, b))
  | _, _ => spks₂

@[simp]
theorem cliUpdateSpkBundlesForQuery_noneResp {S : SignalPqxdh.Setup}
    (kq : SignalPqxdh.KeyIndQuery S)
    (spks₂ : List ((ℕ × ℕ) × SignalPqxdh.SpkBundleEntry))
    (st₁' : SignalPqxdh.KeyIndState S) :
    cliUpdateSpkBundlesForQuery kq spks₂ .noneResp st₁' = spks₂ := by
  cases kq <;> rfl

theorem forall2_cliSpkBundles_map_reveal
    {spks₁ spks₂ : List ((ℕ × ℕ) × SignalPqxdh.SpkBundleEntry)}
    (h : List.Forall₂ CliSpkBundleRel spks₁ spks₂) (target : ℕ × ℕ) :
    List.Forall₂ CliSpkBundleRel
      (spks₁.map (fun (idx, b) => if idx == target then (idx, { b with revealed := true }) else (idx, b)))
      (spks₂.map (fun (idx, b) => if idx == target then (idx, { b with revealed := true }) else (idx, b))) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hhead _ ih =>
    refine List.Forall₂.cons ?_ ih
    rcases hhead with ⟨hidx, h1, h2, h3, h4, h5, h6⟩
    dsimp only; rw [hidx]
    split_ifs <;> exact ⟨rfl, h1, h2, h3, h4, h5, h6⟩

theorem isSpkRevealed_cons_of_true_cli (P : SignalPqxdh.Primitives)
    (head : (ℕ × ℕ) × SignalPqxdh.SpkBundleEntry)
    (spks : List ((ℕ × ℕ) × SignalPqxdh.SpkBundleEntry)) (pk : SignalPqxdh.Bytes)
    (h : SignalPqxdh.isSpkRevealed P spks pk = true) :
    SignalPqxdh.isSpkRevealed P (head :: spks) pk = true := by
  unfold SignalPqxdh.isSpkRevealed at h ⊢
  simp [List.any_cons, h]

theorem isSpkRevealed_map_reveal_of_true_cli (P : SignalPqxdh.Primitives)
    (spks : List ((ℕ × ℕ) × SignalPqxdh.SpkBundleEntry)) (target : ℕ × ℕ) (pk : SignalPqxdh.Bytes)
    (h : SignalPqxdh.isSpkRevealed P spks pk = true) :
    SignalPqxdh.isSpkRevealed P
      (spks.map (fun (idx, b) => if idx == target then (idx, { b with revealed := true }) else (idx, b)))
      pk = true := by
  unfold SignalPqxdh.isSpkRevealed at h ⊢
  rw [List.any_eq_true] at h ⊢
  rcases h with ⟨⟨idx, b⟩, hmem, hpred⟩
  refine ⟨if idx == target then (idx, { b with revealed := true }) else (idx, b),
    List.mem_map_of_mem hmem, ?_⟩
  simp only [Bool.and_eq_true, beq_iff_eq] at hpred
  split_ifs <;> simp [hpred.1, hpred.2]

private theorem recordKeyIndResp_run_cliReplaceSpkBundles {S : SignalPqxdh.Setup}
    (P : SignalPqxdh.Primitives) (rEntry : SignalPqxdh.KeyIndRespEntry S)
    (st₁ : SignalPqxdh.KeyIndState S)
    (spks₂ : List ((ℕ × ℕ) × SignalPqxdh.SpkBundleEntry)) :
    (SignalPqxdh.recordKeyIndResp S P rEntry).run (cliReplaceSpkBundles st₁ spks₂) =
      ((SignalPqxdh.recordKeyIndResp S P rEntry).run st₁ >>= fun (u, st₁') =>
        pure (u, cliReplaceSpkBundles st₁' spks₂)) := by
  unfold SignalPqxdh.recordKeyIndResp
  rw [stateT_run_get_bind_cli, stateT_run_get_bind_cli]
  rcases st₁.sessions.find? (fun s => SignalPqxdh.keyIndPartner P s rEntry) with _ | s <;>
    simp [StateT.run_bind, StateT.run_get, StateT.run_pure, StateT.run_set,
      StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc]

private theorem runKeyIndInitiate_run_cliReplaceSpkBundles {S : SignalPqxdh.Setup}
    (useRo : Bool) (P : SignalPqxdh.Primitives) (sid : SignalPqxdh.SessionId S)
    (u : Fin S.N_id) (bundle : SignalPqxdh.PreKeyBundleInput)
    (st₁ : SignalPqxdh.KeyIndState S)
    (spks₂ : List ((ℕ × ℕ) × SignalPqxdh.SpkBundleEntry))
    (hForall : List.Forall₂ CliSpkBundleRel st₁.spkBundles spks₂) :
    (SignalPqxdh.runKeyIndInitiate useRo S P sid u bundle).run (cliReplaceSpkBundles st₁ spks₂) =
      ((SignalPqxdh.runKeyIndInitiate useRo S P sid u bundle).run st₁ >>= fun (r, st₁') =>
        pure (r, cliReplaceSpkBundles st₁' spks₂)) := by
  unfold SignalPqxdh.runKeyIndInitiate
  rw [stateT_run_get_bind_cli, stateT_run_get_bind_cli]
  dsimp only [cliReplaceSpkBundles]
  rw [← forall2_cliSpkBundles_koskBundleOk P st₁.principals hForall,
      ← forall2_cliSpkBundles_checkBundleProvenance P st₁.principals hForall]
  rcases h1 : st₁.sessions.any (fun e => e.sid == sid) with _ | _
  · rcases h2 : st₁.principals.find? (fun x => x.1 == u.val) with _ | ⟨_, uEntry⟩
    · simp only [h1, h2]; simp
    · rcases h3 : SignalPqxdh.koskBundleOk P st₁.principals st₁.spkBundles st₁.opkEntries st₁.advKeys bundle with _ | _
      · simp only [h1, h2, h3]; simp
      · simp only [h1, h2, h3, Bool.false_eq_true, Bool.not_true, ↓reduceIte,
          StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
        congr 1; funext ekASk; congr 1; funext kemCoins
        rcases h4 : (P.sigVerify (SignalPqxdh.resolveSigPk P st₁.principals bundle.ikB)
            (SignalPqxdh.encodeEC bundle.spkB) bundle.spkSig &&
          P.sigVerify (SignalPqxdh.resolveSigPk P st₁.principals bundle.ikB)
            (SignalPqxdh.encodeKEM bundle.pqspkB) bundle.pqspkSig) with _ | _
        · simp [h4]
        · rcases h5 : P.kemEncaps bundle.pqspkB kemCoins with _ | ⟨ss, kemCt⟩
          · simp [h4, h5]
          · simp only [h4, h5, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
              StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
            congr 1; funext ⟨drKeyReal, roCache'⟩
            rcases h6 : SignalPqxdh.keyIndPartnerRandKey? P st₁.respSessions _ with _ | dk <;>
              rcases h7 : SignalPqxdh.findHonestPrincipal P st₁.principals bundle.ikB with _ | _ <;>
              simp [h6, h7, StateT.run_bind, StateT.run_pure, StateT.run_set,
                StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc]
  · simp [h1]

theorem pqxdhKeyIndImpl_false_run_cliReplaceSpkBundles {S : SignalPqxdh.Setup}
    (P : SignalPqxdh.Primitives) (kq : SignalPqxdh.KeyIndQuery S)
    (st₁ : SignalPqxdh.KeyIndState S)
    (spks₂ : List ((ℕ × ℕ) × SignalPqxdh.SpkBundleEntry))
    (hForall : List.Forall₂ CliSpkBundleRel st₁.spkBundles spks₂) :
    (SignalPqxdh.pqxdhKeyIndImpl false S P kq).run (cliReplaceSpkBundles st₁ spks₂) =
      ((SignalPqxdh.pqxdhKeyIndImpl false S P kq).run st₁ >>= fun (r, st₁') =>
        pure (r, cliReplaceSpkBundles st₁' (cliUpdateSpkBundlesForQuery kq spks₂ r st₁'))) := by
  unfold SignalPqxdh.pqxdhKeyIndImpl
  rw [stateT_run_get_bind_cli, stateT_run_get_bind_cli]
  cases kq <;> dsimp only [cliUpdateSpkBundlesForQuery, cliReplaceSpkBundles]
  case initPrin u =>
    rcases st₁.principals.any (fun x => x.1 == u.val) with _ | _ <;>
      simp [StateT.run_bind, StateT.run_get, StateT.run_pure, StateT.run_set,
        StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc]
  case corruptIK u =>
    rcases h1 : st₁.principals.find? (fun x => x.1 == u.val) with _ | ⟨_, entry⟩ <;>
      (simp only [h1]; simp [StateT.run_bind, StateT.run_get, StateT.run_pure, StateT.run_set,
        pure_bind, bind_assoc])
  case genSPK u j =>
    have hany : (spks₂.any fun x => x.1 == (u.val, j.val)) =
        (st₁.spkBundles.any fun x => x.1 == (u.val, j.val)) :=
      (forall2_cliSpkBundles_any hForall _ fun _ _ hx => by rw [hx.1]).symm
    rcases h1 : st₁.spkBundles.any (fun x => x.1 == (u.val, j.val)) with _ | _
    · rcases h2 : st₁.principals.find? (fun x => x.1 == u.val) with _ | ⟨_, uEntry⟩ <;>
        (simp only [hany, h1, h2]; simp [cliUpdateSpkBundlesForQuery, StateT.run_bind,
          StateT.run_pure, StateT.run_set, StateT.run_monadLift, monadLift_self,
          pure_bind, bind_assoc])
    · simp only [hany, h1]; simp [cliUpdateSpkBundlesForQuery]
  case genOPK u j o =>
    rcases st₁.opkEntries.any (fun x => x.1 == (u.val, j.val, o.val)) with _ | _ <;>
      simp [StateT.run_bind, StateT.run_get, StateT.run_pure, StateT.run_set,
        StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc]
  case initiateOPK u i bundle =>
    rcases h1 : bundle.opkB?.isNone with _ | _
    · simp only [h1, Bool.false_eq_true, ↓reduceIte]
      exact runKeyIndInitiate_run_cliReplaceSpkBundles false P (.sendOPK u i) u bundle st₁ spks₂ hForall
    · simp [h1]
  case initiateNoOPK u i bundle =>
    rcases h1 : bundle.opkB?.isSome with _ | _
    · simp only [h1, Bool.false_eq_true, ↓reduceIte]
      exact runKeyIndInitiate_run_cliReplaceSpkBundles false P (.sendNoOPK u i) u bundle st₁ spks₂ hForall
    · simp [h1]
  case acceptOPK k j o hdr =>
    split_ifs
    · simp
    · simp
    · simp
    · rcases hkp : st₁.principals.find? (fun x => x.1 == k.val) with _ | ⟨_, kEntry⟩
      · simp only [hkp]; simp
      · rcases find_cliSpkBundles_rel_of_forall2 hForall (k.val, j.val) with
          ⟨hnone1, hnone2⟩ | ⟨⟨idx₁, b₁⟩, ⟨idx₂, b₂⟩, hsome1, hsome2, ⟨_, h1, h2, _, h4, h5, _⟩⟩
        · simp only [hkp, hnone1, hnone2]; simp
        · dsimp only at h1 h2 h4 h5
          rcases hopk : st₁.opkEntries.find? (fun x => x.1 == (k.val, j.val, o.val)) with _ | ⟨_, oEntry⟩
          · simp only [hkp, hsome1, hsome2, hopk]; simp
          · rcases hcons : oEntry.consumed with _ | _
            · simp only [hkp, hsome1, hsome2, hopk, hcons, Bool.false_eq_true, ↓reduceIte]
              rw [← h1, ← h2, ← h4, ← h5]
              rcases SignalPqxdh.Model.acceptKeys P _ with _ | _
              · simp
              · rcases P.kemDecaps b₁.pqspkSk hdr.kemCt with _ | ss
                · simp
                · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
                    StateT.run_set, bind_assoc, pure_bind]
                  congr 1; funext ⟨drKey, roCache'⟩
                  have hrec := recordKeyIndResp_run_cliReplaceSpkBundles P
                    { sid := .recvOPK k j o, respIkPk := kEntry.ikAPk, spkPk := b₁.spkPk,
                      opkPk? := some oEntry.opkPk, pqspkPk := b₁.pqspkPk, hdr := hdr,
                      senderHonest := (SignalPqxdh.findHonestPrincipal P st₁.principals hdr.ikAPk).isSome,
                      drKeyReal := drKey, drKeyRand := drKey }
                    { st₁ with
                      opkEntries := st₁.opkEntries.map (fun (idx, e) =>
                        if idx == (k.val, j.val, o.val) then (idx, { e with consumed := true }) else (idx, e))
                      usedRecvOPK := (k.val, j.val, o.val) :: st₁.usedRecvOPK
                      seenKyberBaseKeys := (SignalPqxdh.checkAndMarkKyberBaseKeySeen st₁.seenKyberBaseKeys k.val hdr.pqspkId hdr.spkId hdr.ekAPk).2
                      roCache := roCache' } spks₂
                  rw [hrec]
                  rcases SignalPqxdh.findHonestPrincipal P st₁.principals hdr.ikAPk with _ | _ <;>
                    simp [bind_assoc, pure_bind]
            · simp only [hkp, hsome1, hsome2, hopk, hcons]; simp
  case acceptNoOPK k j l hdr =>
    split_ifs
    · simp
    · simp
    · simp
    · rcases hkp : st₁.principals.find? (fun x => x.1 == k.val) with _ | ⟨_, kEntry⟩
      · simp only [hkp]; simp
      · rcases find_cliSpkBundles_rel_of_forall2 hForall (k.val, j.val) with
          ⟨hnone1, hnone2⟩ | ⟨⟨idx₁, b₁⟩, ⟨idx₂, b₂⟩, hsome1, hsome2, ⟨_, h1, h2, _, h4, h5, _⟩⟩
        · simp only [hkp, hnone1, hnone2]; simp
        · dsimp only at h1 h2 h4 h5
          simp only [hkp, hsome1, hsome2]
          rw [← h1, ← h2, ← h4, ← h5]
          rcases SignalPqxdh.Model.acceptKeys P _ with _ | _
          · simp
          · rcases P.kemDecaps b₁.pqspkSk hdr.kemCt with _ | ss
            · simp
            · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
                StateT.run_set, bind_assoc, pure_bind]
              congr 1; funext ⟨drKey, roCache'⟩
              have hrec := recordKeyIndResp_run_cliReplaceSpkBundles P
                { sid := .recvNoOPK k j l, respIkPk := kEntry.ikAPk, spkPk := b₁.spkPk,
                  opkPk? := none, pqspkPk := b₁.pqspkPk, hdr := hdr,
                  senderHonest := (SignalPqxdh.findHonestPrincipal P st₁.principals hdr.ikAPk).isSome,
                  drKeyReal := drKey, drKeyRand := drKey }
                { st₁ with
                  usedRecvNoOPK := (k.val, j.val, l.val) :: st₁.usedRecvNoOPK
                  seenKyberBaseKeys := (SignalPqxdh.checkAndMarkKyberBaseKeySeen st₁.seenKyberBaseKeys k.val hdr.pqspkId hdr.spkId hdr.ekAPk).2
                  roCache := roCache' } spks₂
              rw [hrec]
              rcases SignalPqxdh.findHonestPrincipal P st₁.principals hdr.ikAPk with _ | _ <;>
                simp [bind_assoc, pure_bind]
  case testSession sid =>
    rw [isFreshKeyIndSession_cliReplaceSpkBundles]
    rcases hfresh : SignalPqxdh.isKeyIndSessionTestable st₁ sid with _ | _
    · simp [hfresh]
    · rcases h1 : st₁.sessions.find? (fun e => e.sid == sid) with _ | e
      · rcases h2 : st₁.respSessions.find? (fun r => r.sid == sid) with _ | r <;>
          simp [hfresh, h1, h2, StateT.run_bind, StateT.run_pure, StateT.run_set, pure_bind, bind_assoc]
      · simp [hfresh, h1, StateT.run_bind, StateT.run_pure, StateT.run_set, pure_bind, bind_assoc]
  case revealSessionKey sid =>
    rcases h1 : st₁.sessions.find? (fun e => e.sid == sid) with _ | e
    · rcases h2 : st₁.respSessions.find? (fun r => r.sid == sid) with _ | r
      · simp [h1, h2]
      · rcases h3 : r.tested with _ | _ <;>
          simp [h1, h2, h3, StateT.run_bind, StateT.run_pure, StateT.run_set, pure_bind, bind_assoc]
    · rcases h3 : e.tested with _ | _ <;>
        simp [h1, h3, StateT.run_bind, StateT.run_pure, StateT.run_set, pure_bind, bind_assoc]
  case revealSpkSk u j =>
    rcases find_cliSpkBundles_rel_of_forall2 hForall (u.val, j.val) with
      ⟨hnone1, hnone2⟩ | ⟨⟨idx₁, b₁⟩, ⟨idx₂, b₂⟩, hsome1, hsome2, ⟨_, h1, _⟩⟩
    · simp [hnone1, hnone2]
    · dsimp only at h1
      simp [hsome1, hsome2, h1, StateT.run_bind, StateT.run_pure, StateT.run_set, pure_bind, bind_assoc]
  case registerKey sk =>
    rcases h1 : SignalPqxdh.registerAdvKey P st₁.advKeys sk with _ | ⟨pk, advKeys'⟩ <;>
      simp [h1, StateT.run_bind, StateT.run_pure, StateT.run_set, pure_bind, bind_assoc]
  case roQuery secrets =>
    simp [StateT.run_bind, StateT.run_get, StateT.run_pure, StateT.run_set,
      StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc]
  case revealDhSecrets =>
    have hmap : (spks₂.map fun x => x.2.spkSk) = (st₁.spkBundles.map fun x => x.2.spkSk) := by
      generalize st₁.spkBundles = spks₁ at hForall ⊢
      induction hForall with
      | nil => rfl
      | cons hhead _ ih => rcases hhead with ⟨_, h1, _⟩; simp [h1, ih]
    simp [hmap]

theorem pqxdhKeyIndImpl1KeyReal_run_cliReplaceSpkBundles {S : SignalPqxdh.Setup}
    (P : SignalPqxdh.Primitives) (kq : SignalPqxdh.KeyIndQuery S)
    (st₁ : SignalPqxdh.KeyIndState S)
    (spks₂ : List ((ℕ × ℕ) × SignalPqxdh.SpkBundleEntry))
    (hForall : List.Forall₂ CliSpkBundleRel st₁.spkBundles spks₂) :
    (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P kq).run (cliReplaceSpkBundles st₁ spks₂) =
      ((SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P kq).run st₁ >>= fun (r, st₁') =>
        pure (r, cliReplaceSpkBundles st₁' (cliUpdateSpkBundlesForQuery kq spks₂ r st₁'))) := by
  have hOther (q : SignalPqxdh.KeyIndQuery S)
      (h_eq : SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P q = SignalPqxdh.pqxdhKeyIndImpl false S P q) :
      (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P q).run (cliReplaceSpkBundles st₁ spks₂) =
        ((SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P q).run st₁ >>= fun (r, st₁') =>
          pure (r, cliReplaceSpkBundles st₁' (cliUpdateSpkBundlesForQuery q spks₂ r st₁'))) := by
    rw [h_eq]
    exact pqxdhKeyIndImpl_false_run_cliReplaceSpkBundles P q st₁ spks₂ hForall
  cases kq with
  | initPrin u =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal
    rw [stateT_run_get_bind_cli, stateT_run_get_bind_cli]
    rcases st₁.principals.any (fun (idx, _) => idx == u.val) with _ | _ <;>
      simp [cliUpdateSpkBundlesForQuery, StateT.run_bind, StateT.run_get, StateT.run_pure,
        StateT.run_set, StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc]
  | roQuery secrets =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal
    rw [stateT_run_get_bind_cli, stateT_run_get_bind_cli]
    simp [cliUpdateSpkBundlesForQuery, StateT.run_bind, StateT.run_get, StateT.run_pure,
      StateT.run_set, StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc]
  | revealDhSecrets =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal
    simp [cliUpdateSpkBundlesForQuery]
  | corruptIK _ | genSPK _ _ | genOPK _ _ _ | initiateOPK _ _ _ | initiateNoOPK _ _ _
  | acceptOPK _ _ _ _ | acceptNoOPK _ _ _ _ | testSession _ | revealSessionKey _
  | registerKey _ | revealSpkSk _ _ =>
    exact hOther _ rfl

private theorem deq_of_eq_cli {α : Type} {c₁ c₂ : ProbComp α} (h : c₁ = c₂) :
    CryptoGames.Lazy.DEq c₁ c₂ := by
  subst h; intro _; rfl

private theorem bhDrvM_lift_prob_bind_run {S : SignalPqxdh.Setup} {ℓ : ℕ} {α β : Type}
    (c : ProbComp α) (f : α → BHDrvM S ℓ β)
    (ds : ModelDriverState S ℓ) (st : SignalPqxdh.KeyIndState S) :
    (((StateT.lift (liftM c : StateT (SignalPqxdh.KeyIndState S) ProbComp α) >>= f).run ds).run st) =
      (c >>= fun a => (((f a).run ds).run st)) := by
  simp [StateT.run_bind, StateT.run_pure, StateT.run_monadLift, monadLift_self,
    stateT_lift_run_cli, stateT_monadLift_run_cli, bind_assoc, pure_bind]

private theorem keyIndM_lift_prob_bind_run {S : SignalPqxdh.Setup} {α β : Type}
    (c : ProbComp α) (f : α → StateT (SignalPqxdh.KeyIndState S) ProbComp β)
    (st : SignalPqxdh.KeyIndState S) :
    ((liftM c >>= f).run st) = (c >>= fun a => (f a).run st) := by
  simp [StateT.run_bind, StateT.run_pure, StateT.run_monadLift, monadLift_self,
    stateT_monadLift_run_cli, bind_assoc, pure_bind]

private theorem bind_congr_prob {α β : Type} (c : ProbComp α) {f g : α → ProbComp β}
    (h : ∀ a, f a = g a) : (c >>= f) = (c >>= g) :=
  congrArg (c >>= ·) (funext h)

private theorem stateT_run_if_neg_cli {S : SignalPqxdh.Setup} {ℓ : ℕ} {α : Type}
    {P : Prop} [Decidable P] (hP : ¬ P) (t e : BHDrvM S ℓ α)
    (ds : ModelDriverState S ℓ) (st : SignalPqxdh.KeyIndState S) :
    ((StateT.run (if P then t else e) ds).run st) = ((StateT.run e ds).run st) := by
  simp [hP]

private theorem bhRunInitiate_deq_runKeyIndInitiate_false {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (P : SignalPqxdh.Primitives) (sid : SignalPqxdh.SessionId S)
    (u : Fin S.N_id) (bundle : SignalPqxdh.PreKeyBundleInput)
    (ds : ModelDriverState S ℓ) (st : SignalPqxdh.KeyIndState S)
    (hHonIk : (match SignalPqxdh.findHonestPrincipal P st.principals bundle.ikB with
               | some (_, e) => e.ikAPk == bundle.ikB
               | none => true) = true) :
    CryptoGames.Lazy.DEq
      ((((bhRunInitiate S P sid u bundle false).run ds).run st) >>= fun x => pure (x.1.1, x.2))
      ((SignalPqxdh.runKeyIndInitiate false S P sid u bundle).run st) := by
  unfold bhRunInitiate SignalPqxdh.runKeyIndInitiate
  rw [stateT_run_get_bind_cli]
  rw [StateT.run_bind, StateT.run_bind, stateT_lift_run_cli, StateT.run_bind, StateT.run_get]
  simp only [StateT.run_pure, bind_assoc, pure_bind]
  rcases h1 : st.sessions.any (fun e => e.sid == sid) with _ | _
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    rcases h2 : st.principals.find? (fun (idx, _) => idx == u.val) with _ | ⟨_, uEntry⟩
    · simp only [h2, StateT.run_pure, pure_bind]; exact CryptoGames.Lazy.DEq.refl _
    · simp only [h2]
      rw [stateT_run_if_neg_cli (by
        intro hbad
        rcases hf : SignalPqxdh.findHonestPrincipal P st.principals bundle.ikB with _ | ⟨_, e⟩ <;>
          simp_all)]
      rcases h3 : SignalPqxdh.koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bundle with _ | _
      · simp only [h3, Bool.not_false, ↓reduceIte, StateT.run_pure, pure_bind]
        exact CryptoGames.Lazy.DEq.refl _
      · simp only [h3, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        rw [bhDrvM_lift_prob_bind_run, bind_assoc, keyIndM_lift_prob_bind_run]
        let k (p : SignalPqxdh.Bytes × SignalPqxdh.Bytes) :
            ProbComp (SignalPqxdh.KeyIndResponse × SignalPqxdh.KeyIndState S) :=
          let ekASk := p.1
          let kemCoins := p.2
          let sigPkB := SignalPqxdh.resolveSigPk P st.principals bundle.ikB
          if !(P.sigVerify sigPkB (SignalPqxdh.encodeEC bundle.spkB) bundle.spkSig &&
               P.sigVerify sigPkB (SignalPqxdh.encodeKEM bundle.pqspkB) bundle.pqspkSig) then
            pure (.noneResp, st)
          else
            match P.kemEncaps bundle.pqspkB kemCoins with
            | none => pure (.noneResp, st)
            | some (ss, kemCt) =>
              let ekAPk := P.x25519Base ekASk
              let secrets := SignalPqxdh.buildSecrets
                (P.x25519 uEntry.secIKA0 bundle.spkB) (P.x25519 ekASk bundle.ikB)
                (P.x25519 ekASk bundle.spkB)
                (bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)) ss
              SignalPqxdh.evalHkdfOrRo false P st.roCache secrets >>= fun (drKeyReal, roCache') =>
                let hdr : SignalPqxdh.HandshakeHdr :=
                  { ikAPk := uEntry.ikAPk, ekAPk := ekAPk, spkId := bundle.spkId,
                    opkId? := bundle.opkB?.map Prod.fst, pqspkId := bundle.pqspkId, kemCt := kemCt }
                let honestPeer := SignalPqxdh.isHonestUncorruptedPeer P st.principals bundle.ikB
                let (spkHon, opkHon, pqspkHon) :=
                  SignalPqxdh.checkBundleProvenance P st.principals st.spkBundles st.opkEntries bundle
                let sessEntry : SignalPqxdh.KeyIndInitiatorEntry S :=
                  { sid := sid, honestPeer := honestPeer, peerIkPk := bundle.ikB,
                    peerSpkPk := bundle.spkB, peerOpkPk? := bundle.opkB?.map Prod.snd,
                    peerPqspkPk := bundle.pqspkB, spkHonest := spkHon, opkHonest := opkHon,
                    pqspkHonest := pqspkHon, ekASk := ekASk, fresh := honestPeer.isSome,
                    drKeyReal := drKeyReal, drKeyRand := drKeyReal, hdr := hdr, tested := false }
                (match SignalPqxdh.keyIndPartnerRandKey? P st.respSessions sessEntry with
                 | some dk => pure dk
                 | none => SignalPqxdh.sampleDRKey96) >>= fun drKeyRand =>
                  let st' := { st with sessions := { sessEntry with drKeyRand := drKeyRand } :: st.sessions,
                                       roCache := roCache' }
                  match SignalPqxdh.findHonestPrincipal P st.principals bundle.ikB with
                  | some _ => pure (.hdrResp hdr, st')
                  | none => pure (.initUnfreshResp drKeyReal hdr, st')
        refine CryptoGames.Lazy.DEq.trans
          (y := ($ᵗ List.Vector (BitVec 8) 160 : ProbComp _) >>= fun t_init =>
            k (tapeEkASk t_init, tapeKemCoins t_init)) ?_
          (CryptoGames.Lazy.DEq.trans
            (y := SignalPqxdh.sampleScalar32 >>= fun ekASk =>
              SignalPqxdh.sampleCoins32 >>= fun kemCoins => k (ekASk, kemCoins)) ?_ ?_)
        · apply deq_of_eq_cli
          apply bind_congr_prob ($ᵗ List.Vector (BitVec 8) 160)
          intro t_init; dsimp only [k]
          rcases hsig : (P.sigVerify (SignalPqxdh.resolveSigPk P st.principals bundle.ikB)
              (SignalPqxdh.encodeEC bundle.spkB) bundle.spkSig &&
            P.sigVerify (SignalPqxdh.resolveSigPk P st.principals bundle.ikB)
              (SignalPqxdh.encodeKEM bundle.pqspkB) bundle.pqspkSig) with _ | _
          · simp [hsig]
          · simp only [hsig, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            rcases henc : P.kemEncaps bundle.pqspkB (tapeKemCoins t_init) with _ | ⟨ss, kemCt⟩
            · simp [henc]
            · dsimp only
              rw [bhDrvM_lift_prob_bind_run, bind_assoc]
              apply bind_congr_prob
              intro ⟨drKeyReal, roCache'⟩
              rcases hkp : SignalPqxdh.keyIndPartnerRandKey? P st.respSessions _ with _ | dk <;>
                rcases hfhp : SignalPqxdh.findHonestPrincipal P st.principals bundle.ikB with _ | _ <;>
                simp [hkp, hfhp, StateT.run_bind, StateT.run_pure, StateT.run_set, StateT.run_modify,
                  StateT.run_monadLift, monadLift_self, stateT_lift_run_cli,
                  stateT_monadLift_run_cli, bind_assoc, pure_bind]
        · simpa only [bind_assoc, pure_bind] using deq_tape160_ekASk_kemCoins.bind_left k
        · apply deq_of_eq_cli
          apply bind_congr_prob SignalPqxdh.sampleScalar32
          intro ekASk
          rw [keyIndM_lift_prob_bind_run]
          apply bind_congr_prob SignalPqxdh.sampleCoins32
          intro kemCoins; dsimp only [k]
          rcases hsig : (P.sigVerify (SignalPqxdh.resolveSigPk P st.principals bundle.ikB)
              (SignalPqxdh.encodeEC bundle.spkB) bundle.spkSig &&
            P.sigVerify (SignalPqxdh.resolveSigPk P st.principals bundle.ikB)
              (SignalPqxdh.encodeKEM bundle.pqspkB) bundle.pqspkSig) with _ | _
          · simp [hsig]
          · simp only [hsig, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            rcases henc : P.kemEncaps bundle.pqspkB kemCoins with _ | ⟨ss, kemCt⟩
            · simp [henc]
            · dsimp only
              rw [keyIndM_lift_prob_bind_run]
              apply bind_congr_prob
              intro ⟨drKeyReal, roCache'⟩
              rcases hkp : SignalPqxdh.keyIndPartnerRandKey? P st.respSessions _ with _ | dk <;>
                rcases hfhp : SignalPqxdh.findHonestPrincipal P st.principals bundle.ikB with _ | _ <;>
                simp [hkp, hfhp, StateT.run_bind, StateT.run_pure, StateT.run_set,
                  StateT.run_monadLift, monadLift_self, stateT_monadLift_run_cli,
                  bind_assoc, pure_bind]
  · simp only [h1, ↓reduceIte, StateT.run_pure, pure_bind]; exact CryptoGames.Lazy.DEq.refl _

private theorem bhDrvM_bind_modify_proj {S : SignalPqxdh.Setup} {ℓ : ℕ} {α : Type}
    (m : BHDrvM S ℓ α) (f : α → ModelDriverState S ℓ → ModelDriverState S ℓ)
    (ds : ModelDriverState S ℓ) (st : SignalPqxdh.KeyIndState S) :
    ((((do let r ← m; modify (f r); return r : BHDrvM S ℓ α).run ds).run st) >>=
      fun x => pure (x.1.1, x.2)) =
    (((m.run ds).run st) >>= fun x => pure (x.1.1, x.2)) := by
  simp [StateT.run_bind, StateT.run_pure, StateT.run_modify, bind_assoc, pure_bind]

theorem honIk_of_bhDrvInitiateIkOk_cli {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {W : PEParams}
    {st : SignalPqxdh.KeyIndState S} {ds : ModelDriverState S ℓ}
    (hInv : CliAdapterKeyIndInv S P W st ds)
    (bnd : SignalPqxdh.PreKeyBundleInput)
    (hOk : bhDrvInitiateIkOk P ds.toModelDriverBase bnd = true) :
    (match SignalPqxdh.findHonestPrincipal P st.principals bnd.ikB with
     | some (_, e) => e.ikAPk == bnd.ikB
     | none => true) = true := by
  unfold SignalPqxdh.findHonestPrincipal
  rcases hfind : st.principals.find? (fun x => P.pow8 bnd.ikB == P.pow8 x.2.ikAPk) with
    _ | ⟨idx, e⟩
  · rw [hfind]
  · rw [hfind]
    have hmem := List.mem_of_find?_eq_some hfind
    have hpow0 := List.find?_some hfind
    dsimp only at hpow0
    have hpow : (P.pow8 e.ikAPk == P.pow8 bnd.ikB) = true :=
      beq_iff_eq.mpr (beq_iff_eq.mp hpow0).symm
    obtain ⟨u, hu⟩ := hInv.prins_ds idx e hmem
    unfold bhDrvInitiateIkOk at hOk
    simp only [Bool.not_eq_true', List.any_eq_false] at hOk
    have hnot := hOk (u, e.ikAPk) hu
    simp [hpow] at hnot
    exact beq_iff_eq.mpr hnot

theorem cliDrvKeyInd_proj_deq {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {W : PEParams}
    {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
    (hInv : CliAdapterKeyIndInv S P W st_cli ds_cli)
    (kq : SignalPqxdh.KeyIndQuery S)
    (hOk : bhDrvKiQueryOk P ds_cli.toModelDriverBase kq = true)
    (hNoProm : cliKiNoOpkCorrupt ds_cli.instMeta kq = false) :
    CryptoGames.Lazy.DEq
      ((((bhDrvKeyInd S ℓ P false kq).run ds_cli).run st_cli) >>= fun x => pure (x.1.1, x.2))
      ((SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P kq).run st_cli) := by
  have hOther (q : SignalPqxdh.KeyIndQuery S)
      (h_cli : bhDrvKeyInd S ℓ P false q = do
        let r ← StateT.lift (SignalPqxdh.pqxdhKeyIndImpl false S P q)
        modify (fun ds => bhDrvMirror ds q r); return r)
      (h_ki : SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P q = SignalPqxdh.pqxdhKeyIndImpl false S P q) :
      CryptoGames.Lazy.DEq
        ((((bhDrvKeyInd S ℓ P false q).run ds_cli).run st_cli) >>= fun x => pure (x.1.1, x.2))
        ((SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P q).run st_cli) := by
    rw [h_cli, h_ki, bhDrvM_bind_modify_proj]
    simp [stateT_lift_run_cli, bind_assoc, pure_bind, CryptoGames.Lazy.DEq]
  cases kq with
  | testSession _ | revealDhSecrets =>
    simp [bhDrvKiQueryOk] at hOk
  | initPrin u =>
    unfold bhDrvKeyInd SignalPqxdh.pqxdhKeyIndImpl1KeyReal
    simp [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
      StateT.run_modify, StateT.run_monadLift, monadLift_self, stateT_lift_run_cli,
      bind_assoc, pure_bind]
    rcases st_cli.principals.any (fun (idx, _) => idx == u.val) with _ | _ <;>
      simp [CryptoGames.Lazy.DEq, bind_assoc, pure_bind]
  | initiateOPK u i bnd =>
    simp only [bhDrvKiQueryOk, Bool.and_eq_true] at hOk
    rcases hOk with ⟨hopk, hik⟩
    have hnone : bnd.opkB?.isNone = false := by
      rcases hopk' : bnd.opkB? with _ | _
      · simp [hopk'] at hopk
      · rfl
    have h_cli : bhDrvKeyInd S ℓ P false (.initiateOPK u i bnd) = (do
        let ds ← get
        if bnd.opkB?.isNone || !bhDrvInitiateIkOk P ds.toModelDriverBase bnd then return .noneResp
        let r ← bhRunInitiate S P (.sendOPK u i) u bnd false
        modify (fun ds => bhDrvMirror ds (.initiateOPK u i bnd) r); return r) := rfl
    have h_ki : SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P (.initiateOPK u i bnd) = (do
        let st ← get
        if bnd.opkB?.isNone then return .noneResp
        SignalPqxdh.runKeyIndInitiate false S P (.sendOPK u i) u bnd) := rfl
    rw [h_cli, h_ki, stateT_run_get_bind_cli, stateT_run_get_bind_cli]
    simp only [hnone, hik, Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
    rw [bhDrvM_bind_modify_proj]
    exact bhRunInitiate_deq_runKeyIndInitiate_false P (.sendOPK u i) u bnd ds_cli st_cli
      (honIk_of_bhDrvInitiateIkOk_cli hInv bnd hik)
  | initiateNoOPK u i bnd =>
    simp only [bhDrvKiQueryOk, Bool.and_eq_true] at hOk
    rcases hOk with ⟨hopk, hik⟩
    have hsome : bnd.opkB?.isSome = false := by
      rcases hopk' : bnd.opkB? with _ | _
      · rfl
      · simp [hopk'] at hopk
    have h_cli : bhDrvKeyInd S ℓ P false (.initiateNoOPK u i bnd) = (do
        let ds ← get
        if bnd.opkB?.isSome || !bhDrvInitiateIkOk P ds.toModelDriverBase bnd then return .noneResp
        let r ← bhRunInitiate S P (.sendNoOPK u i) u bnd false
        modify (fun ds => bhDrvMirror ds (.initiateNoOPK u i bnd) r); return r) := rfl
    have h_ki : SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P (.initiateNoOPK u i bnd) = (do
        let st ← get
        if bnd.opkB?.isSome then return .noneResp
        SignalPqxdh.runKeyIndInitiate false S P (.sendNoOPK u i) u bnd) := rfl
    rw [h_cli, h_ki, stateT_run_get_bind_cli, stateT_run_get_bind_cli]
    simp only [hsome, hik, Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
    rw [bhDrvM_bind_modify_proj]
    exact bhRunInitiate_deq_runKeyIndInitiate_false P (.sendNoOPK u i) u bnd ds_cli st_cli
      (honIk_of_bhDrvInitiateIkOk_cli hInv bnd hik)
  | acceptOPK k j o hdr =>
    simp only [bhDrvKiQueryOk] at hOk
    have hk : SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P (.acceptOPK k j o hdr) =
        SignalPqxdh.pqxdhKeyIndImpl false S P (.acceptOPK k j o hdr) := rfl
    have h_cli : bhDrvKeyInd S ℓ P false (.acceptOPK k j o hdr) = (do
        let ds ← get
        if !bhDrvAcceptIkOk ds.toModelDriverBase hdr then return .noneResp
        let r ← StateT.lift (SignalPqxdh.pqxdhKeyIndImpl false S P (.acceptOPK k j o hdr))
        modify (fun ds => bhDrvMirror ds (.acceptOPK k j o hdr) r); return r) := rfl
    rw [hk, h_cli, stateT_run_get_bind_cli]
    simp only [hOk, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [bhDrvM_bind_modify_proj]
    simp [stateT_lift_run_cli, bind_assoc, pure_bind, CryptoGames.Lazy.DEq]
  | acceptNoOPK k j l hdr =>
    simp only [bhDrvKiQueryOk] at hOk
    have hk : SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P (.acceptNoOPK k j l hdr) =
        SignalPqxdh.pqxdhKeyIndImpl false S P (.acceptNoOPK k j l hdr) := rfl
    have h_cli : bhDrvKeyInd S ℓ P false (.acceptNoOPK k j l hdr) = (do
        let ds ← get
        if !bhDrvAcceptIkOk ds.toModelDriverBase hdr then return .noneResp
        let r ← StateT.lift (SignalPqxdh.pqxdhKeyIndImpl false S P (.acceptNoOPK k j l hdr))
        modify (fun ds => bhDrvMirror ds (.acceptNoOPK k j l hdr) r); return r) := rfl
    rw [hk, h_cli, stateT_run_get_bind_cli]
    simp only [hOk, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [bhDrvM_bind_modify_proj]
    simp [stateT_lift_run_cli, bind_assoc, pure_bind, CryptoGames.Lazy.DEq]
  | roQuery secrets =>
    unfold bhDrvKeyInd SignalPqxdh.pqxdhKeyIndImpl1KeyReal
    rw [stateT_run_get_bind_cli]
    simp [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
      StateT.run_monadLift, monadLift_self, stateT_lift_run_cli, bind_assoc, pure_bind,
      CryptoGames.Lazy.DEq]
  | corruptIK u =>
    dsimp only [cliKiNoOpkCorrupt] at hNoProm
    have hk : SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P (.corruptIK u) =
        SignalPqxdh.pqxdhKeyIndImpl false S P (.corruptIK u) := rfl
    have h_cli : bhDrvKeyInd S ℓ P false (.corruptIK u) = (do
        let ds ← get
        if bhNoOpkRespPromoted ds.instMeta u then return .noneResp
        let r ← StateT.lift (SignalPqxdh.pqxdhKeyIndImpl false S P (.corruptIK u))
        modify (fun ds => bhDrvMirror ds (.corruptIK u) r); return r) := rfl
    rw [hk, h_cli, stateT_run_get_bind_cli]
    simp only [hNoProm, Bool.false_eq_true, ↓reduceIte]
    rw [bhDrvM_bind_modify_proj]
    simp [stateT_lift_run_cli, bind_assoc, pure_bind, CryptoGames.Lazy.DEq]
  | genSPK _ _ | genOPK _ _ _ | revealSessionKey _ | registerKey _
  | revealSpkSk _ _ =>
    exact hOther _ rfl rfl

/-! ## `cliPqSigsOf` preservation and `CliAdapterInstRel` monotonicity -/

theorem find?_map_fst_eq_cli {α β : Type}
    (l : List (α × β)) (f : α × β → α × β) (hf : ∀ x, (f x).1 = x.1)
    (p : α × β → Bool) (hp : ∀ x y, x.1 = y.1 → p x = p y) :
    (l.map f).find? p = (l.find? p).map f := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, List.find?_cons, hp (f hd) hd (hf hd)]
    cases p hd <;> simp [ih]

theorem cliPqSigsOf_eq_of_spkBundles_eq {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {st st' : SignalPqxdh.KeyIndState S} (h : st'.spkBundles = st.spkBundles)
    (bi : ModelDriverInstance S ℓ) :
    cliPqSigsOf st' bi = cliPqSigsOf st bi := by
  unfold cliPqSigsOf; rw [h]

theorem cliPqSigsOf_cons_ne {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {st st' : SignalPqxdh.KeyIndState S} {idx₀ : ℕ × ℕ} {b₀ : SignalPqxdh.SpkBundleEntry}
    (h : st'.spkBundles = (idx₀, b₀) :: st.spkBundles)
    (bi : ModelDriverInstance S ℓ) (hne : idx₀ ≠ (bi.respSlot.1.val, bi.respSlot.2.val)) :
    cliPqSigsOf st' bi = cliPqSigsOf st bi := by
  unfold cliPqSigsOf
  rw [h, List.find?_cons]
  have hbeq : (idx₀ == (bi.respSlot.1.val, bi.respSlot.2.val)) = false :=
    beq_false_of_ne hne
  simp [hbeq]

theorem cliPqSigsOf_map_reveal {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {st st' : SignalPqxdh.KeyIndState S} (target : ℕ × ℕ)
    {f : (ℕ × ℕ) × SignalPqxdh.SpkBundleEntry → (ℕ × ℕ) × SignalPqxdh.SpkBundleEntry}
    (hf : ∀ idx b,
      f (idx, b) = if idx == target then (idx, { b with revealed := true }) else (idx, b))
    (h : st'.spkBundles = st.spkBundles.map f)
    (bi : ModelDriverInstance S ℓ) :
    cliPqSigsOf st' bi = cliPqSigsOf st bi := by
  unfold cliPqSigsOf
  rw [h, find?_map_fst_eq_cli st.spkBundles f
    (fun ⟨idx, b⟩ => by rw [hf]; split_ifs <;> rfl) _
    (fun ⟨i₁, _⟩ ⟨i₂, _⟩ hi => by dsimp only at hi ⊢; rw [hi])]
  cases List.find? _ st.spkBundles with
  | none => rfl
  | some p =>
    rcases p with ⟨idx, e⟩
    dsimp only [Option.map]
    rw [hf]
    split_ifs <;> rfl

/-- Monotonicity of `CliAdapterInstRel` when `(st_cli, ds_cli)` advances to `(st_cli', ds_cli')`
preserving existing `initTapes`, responder bundle secrets/public keys, and `cliPqSigsOf`. -/
theorem cliAdapterInstRel_mono {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {X : UnreachedPqxdhPrimitives} {W : PEParams} {q_rem : ℕ}
    {st_cli st_cli' : SignalPqxdh.KeyIndState S} {ds_cli ds_cli' : ModelDriverState S ℓ}
    {bi : ModelDriverInstance S ℓ} {d : BHModelInst S ℓ} {im im_e2e : ModelDriverInstanceMeta S}
    {inst : BHAdapterInstMeta S} {ack : Bool}
    (hInst : CliAdapterInstRel X W q_rem st_cli ds_cli bi d im im_e2e inst ack)
    (hTapes : ∀ x ∈ ds_cli.initTapes, x ∈ ds_cli'.initTapes)
    (hSpkFwd : ∀ b, ((bi.respSlot.1.val, bi.respSlot.2.val), b) ∈ st_cli.spkBundles →
      ∃ b', ((bi.respSlot.1.val, bi.respSlot.2.val), b') ∈ st_cli'.spkBundles ∧
        b'.spkSk = b.spkSk ∧ b'.spkSig = b.spkSig ∧
        b'.pqspkSk = b.pqspkSk ∧ b'.pqspkSig = b.pqspkSig)
    (hSpkBwd : ∀ b', ((bi.respSlot.1.val, bi.respSlot.2.val), b') ∈ st_cli'.spkBundles →
      ∃ b, ((bi.respSlot.1.val, bi.respSlot.2.val), b) ∈ st_cli.spkBundles ∧
        b'.pqspkPk = b.pqspkPk ∧ b'.pqspkSk = b.pqspkSk)
    (hSigs : cliPqSigsOf st_cli' bi = cliPqSigsOf st_cli bi) :
    CliAdapterInstRel X W q_rem st_cli' ds_cli' bi d im im_e2e inst ack where
  im_eq := hInst.im_eq
  sid_eq := hInst.sid_eq
  hdr_eq := hInst.hdr_eq
  idB_eq := hInst.idB_eq
  respSlot_eq := hInst.respSlot_eq
  respMeta_eq := hInst.respMeta_eq
  regIdA_eq := hInst.regIdA_eq
  regIdB_eq := hInst.regIdB_eq
  aliceAcked_false := hInst.aliceAcked_false
  idA_pub_eq := hInst.idA_pub_eq
  idB_pub_eq := hInst.idB_pub_eq
  extrasB_eq := hInst.extrasB_eq
  stB0_empty := hInst.stB0_empty
  resp_bundle_rel := by
    obtain ⟨bEntry, hb_mem, h1, h2, h3, h4⟩ := hInst.resp_bundle_rel
    obtain ⟨bEntry', hb'_mem, heq1, heq2, heq3, heq4⟩ := hSpkFwd bEntry hb_mem
    exact ⟨bEntry', hb'_mem, heq1 ▸ h1, heq1 ▸ h2, heq3 ▸ h3,
      by rw [hSigs, h4, heq2, heq4]⟩
  handshake_rel := by
    obtain ⟨bundleE, dk, aliceCoins, u_init, bnd, t_init, ss, hexA, htape, hbnd_all, hinitB⟩ :=
      hInst.handshake_rel
    refine ⟨bundleE, dk, aliceCoins, u_init, bnd, t_init, ss, hexA, hTapes _ htape, ?_, hinitB⟩
    intro bEntry' hb'_mem
    obtain ⟨bEntry, hb_mem, hpqPk, hpqSk⟩ := hSpkBwd bEntry' hb'_mem
    obtain ⟨h_eq1, h_enc, h_dec⟩ := hbnd_all bEntry hb_mem
    rw [hpqPk, hpqSk]
    exact ⟨h_eq1, h_enc, h_dec⟩
  gs_rel := by
    have hgs := hInst.gs_rel
    cases h1 : bi.gs with
    | none => simp only [h1] at hgs
    | some gs_cli =>
      cases h2 : d.gs with
      | none => simp only [h1, h2] at hgs
      | some gs_m =>
        simp only [h1, h2] at hgs ⊢
        rw [hSigs]
        exact hgs

theorem cliAdapterInstRel_of_st_ds_unchanged {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {X : UnreachedPqxdhPrimitives} {W : PEParams} {q_rem : ℕ}
    {st_cli st_cli' : SignalPqxdh.KeyIndState S} {ds_cli ds_cli' : ModelDriverState S ℓ}
    {bi : ModelDriverInstance S ℓ} {d : BHModelInst S ℓ} {im im_e2e : ModelDriverInstanceMeta S}
    {inst : BHAdapterInstMeta S} {ack : Bool}
    (hInst : CliAdapterInstRel X W q_rem st_cli ds_cli bi d im im_e2e inst ack)
    (hTapes : ∀ x ∈ ds_cli.initTapes, x ∈ ds_cli'.initTapes)
    (hSpks : st_cli'.spkBundles = st_cli.spkBundles) :
    CliAdapterInstRel X W q_rem st_cli' ds_cli' bi d im im_e2e inst ack :=
  cliAdapterInstRel_mono hInst hTapes
    (fun b hb => ⟨b, hSpks ▸ hb, rfl, rfl, rfl, rfl⟩)
    (fun b' hb' => ⟨b', hSpks.symm ▸ hb', rfl, rfl⟩)
    (cliPqSigsOf_eq_of_spkBundles_eq hSpks bi)

theorem cliAdapterInstRel_of_cons_spk {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {X : UnreachedPqxdhPrimitives} {W : PEParams} {q_rem : ℕ}
    {st_cli st_cli' : SignalPqxdh.KeyIndState S} {ds_cli ds_cli' : ModelDriverState S ℓ}
    {idx₀ : ℕ × ℕ} {b₀ : SignalPqxdh.SpkBundleEntry}
    {bi : ModelDriverInstance S ℓ} {d : BHModelInst S ℓ} {im im_e2e : ModelDriverInstanceMeta S}
    {inst : BHAdapterInstMeta S} {ack : Bool}
    (hInst : CliAdapterInstRel X W q_rem st_cli ds_cli bi d im im_e2e inst ack)
    (hTapes : ∀ x ∈ ds_cli.initTapes, x ∈ ds_cli'.initTapes)
    (hSpks : st_cli'.spkBundles = (idx₀, b₀) :: st_cli.spkBundles)
    (hFresh : st_cli.spkBundles.any (fun (k, _) => k == idx₀) = false) :
    CliAdapterInstRel X W q_rem st_cli' ds_cli' bi d im im_e2e inst ack := by
  obtain ⟨b_wit, hb_wit, _⟩ := hInst.resp_bundle_rel
  have hne : idx₀ ≠ (bi.respSlot.1.val, bi.respSlot.2.val) := by
    intro heq; subst heq
    rw [List.any_eq_false] at hFresh
    have hf := hFresh _ hb_wit
    simp at hf
  exact cliAdapterInstRel_mono hInst hTapes
    (fun b hb => ⟨b, hSpks ▸ List.mem_cons_of_mem _ hb, rfl, rfl, rfl, rfl⟩)
    (fun b' hb' => by
      rw [hSpks] at hb'
      rcases List.mem_cons.mp hb' with heq | htl
      · exact False.elim (hne (Prod.mk.inj heq).1.symm)
      · exact ⟨b', htl, rfl, rfl⟩)
    (cliPqSigsOf_cons_ne hSpks bi hne)

theorem cliAdapterInstRel_of_map_reveal_spk {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {X : UnreachedPqxdhPrimitives} {W : PEParams} {q_rem : ℕ}
    {st_cli st_cli' : SignalPqxdh.KeyIndState S} {ds_cli ds_cli' : ModelDriverState S ℓ}
    {target : ℕ × ℕ}
    {f : (ℕ × ℕ) × SignalPqxdh.SpkBundleEntry → (ℕ × ℕ) × SignalPqxdh.SpkBundleEntry}
    {bi : ModelDriverInstance S ℓ} {d : BHModelInst S ℓ} {im im_e2e : ModelDriverInstanceMeta S}
    {inst : BHAdapterInstMeta S} {ack : Bool}
    (hInst : CliAdapterInstRel X W q_rem st_cli ds_cli bi d im im_e2e inst ack)
    (hTapes : ∀ x ∈ ds_cli.initTapes, x ∈ ds_cli'.initTapes)
    (hf : ∀ idx b,
      f (idx, b) = if idx == target then (idx, { b with revealed := true }) else (idx, b))
    (hSpks : st_cli'.spkBundles = st_cli.spkBundles.map f) :
    CliAdapterInstRel X W q_rem st_cli' ds_cli' bi d im im_e2e inst ack :=
  cliAdapterInstRel_mono hInst hTapes
    (fun b hb => by
      refine ⟨if (bi.respSlot.1.val, bi.respSlot.2.val) == target
        then { b with revealed := true } else b, ?_, ?_⟩
      · rw [hSpks]
        have hm := List.mem_map_of_mem (f := f) hb
        rw [hf] at hm
        split_ifs at hm ⊢ <;> exact hm
      · split_ifs <;> exact ⟨rfl, rfl, rfl, rfl⟩)
    (fun b' hb' => by
      rw [hSpks, List.mem_map] at hb'
      rcases hb' with ⟨⟨idx, b⟩, hb_mem, heq⟩
      rw [hf] at heq
      split_ifs at heq
      · rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
        exact ⟨b, hb_mem, rfl, rfl⟩
      · rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
        exact ⟨b, hb_mem, rfl, rfl⟩)
    (cliPqSigsOf_map_reveal target hf hSpks bi)

end CryptoVerification.E2E
