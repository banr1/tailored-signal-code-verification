/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.LibsignalCli.MainHaltedPrefixEndpoints
public import Computational.Proofs.ReductionDsl.Soundness
import Computational.Proofs.CryptoGames.FSAEAD.CellForgery
import Computational.Proofs.GameHop.GlobalHybrid
import VCVio.EvalDist.Monad.Basic

/-!
# Session-Tracked Stage-1 Prefix Factorization

**Checked by Lean.** Defines `bhPlugExtSessionTracked` and factors
`bhPrefixLazyFullExpWithSessionTracked` through Stage 1 (`eval1`) of
`bhPrefixRedWithSessionTracked` and `bhPrefixExtExpWithSessionTracked`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

open scoped ENNReal BigOperators
open OracleComp OracleSpec

namespace Computational.Proofs.LibsignalCli.MainHaltedPrefixFactor

open CryptoGames (Party SMSchemeR)
open CryptoGames.CBC (Plain)
open CryptoGames.CellForgery (run_simulateQ_query_bind)
open CryptoGames.LibsignalSession (Crypto GhostState PublicKey)
open CryptoGames.SM (GameState initState)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open ReductionDsl (Mid isGameQuery)
open CryptoVerification.E2E (BHE2EDrvState BHE2ESmResp BHModelInst BHPrefixCtx BHTargetQuery
  BHTargetResp BhShallowTwoStageRed Bytes ModelDriverInstanceMeta
  SampledSessionKey bhBytesWord bhDrvKiQueryOk bhE2EDrvInstClean bhE2EDrvWon
  bhE2EFinishStartSpk bhE2EGuard bhE2EInstIkACorr bhE2EMirror bhFwdU bhIdKeyOf
  bhIsBobAcceptSMResp bhIsBobRecvSMQuery bhKeySOf bhLiftP bhNoOpkRespPromoted bhPackSmResp
  bhShallowCheckExtSm bhShallowRunFuel bhShallowRunFuel_query_inr_succ bhTargetGameSpec
  bhTargetQenc bhTargetRdec bhUnpackSmResp configRefuseEarlyBobCorr paramsIdsWithSpqr
  prob_bind_congr_of_support sessionSchemeFixedSpk stageOneAsProbComp)
open Computational.Proofs.LibsignalCli.MainHaltedPrefixCore (ModelDriverKeyBitGen
  SessionHaltTracker
  bhClassifyTarget bhClassifyTargetOnly bhComposedPostObs bhComposedPostObsSessionTracked
  bhE2EDrvImplGenWithSessionTracked bhE2EDrvImplPrefixWithSessionTracked
  bhE2EDrvImplPrefixWithSessionTracked_run_eq_gen bhE2ELocalStartGenWithSessionTracked
  bhE2ELocalStartSessionTracked bhE2EStepLocalSmSessionTracked
  bhE2EStepLocalSmSessionTracked_eq_filter bhFilterSmQuery bhFinishStartSpkGen bhMkKeyBitConst
  bhMkPrefixLazy bhPrefixHandlePostWithSessionTracked bhPrefixHandlePreWithSessionTracked
  bhPrefixLazyFullExpWithSessionTracked bhPrefixRedWithSessionTracked
  bhShallowStepPreCtlSessionTracked bhShallowStepPreNonCtlSessionTracked
  oracleImplRSessionTracked stateT_run_lift stateT_run_liftM)
open Computational.Proofs.LibsignalCli.MainHaltedPrefixEndpoints (
  bhE2EDrvImplGenWithSessionTracked_step_length bhE2EDrvImplGenWithSessionTracked_with_b
  bhE2ELocalStartGenWithSessionTracked_const_eq bhE2EStepLocalSmSessionTracked_insts_length_eq)

/-! ## External session-state plugging -/

abbrev bhDefaultPrefixCtx : BHPrefixCtx :=
  { idA := bhIdKeyOf [], idB := bhIdKeyOf [], spkCoins := 0 }

abbrev ExtState (ℓ : ℕ) := GameState (GhostState Bytes) (Plain ℓ) Bytes

def bhPlugExtInst {S : SignalPqxdh.Setup} {ℓ : ℕ} (gs_ext : ExtState ℓ)
    (d : BHModelInst S ℓ) : BHModelInst S ℓ :=
  match d.gs with | some _ => d | none => { d with gs := some gs_ext }

def bhPlugExt {S : SignalPqxdh.Setup} {ℓ : ℕ} (gs_ext : ExtState ℓ)
    (σ : BHE2EDrvState S ℓ) : BHE2EDrvState S ℓ :=
  { σ with insts := σ.insts.map (bhPlugExtInst gs_ext) }

/-- Plug `(gs_ext, tr_ext)` into `σH` at session slot `k`. -/
def bhPlugExtSessionTracked {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (k : ℕ) (gs_ext : ExtState ℓ) (tr_ext : τ)
    (σH : BHE2EDrvState S ℓ × List τ) : BHE2EDrvState S ℓ × List τ :=
  (bhPlugExt gs_ext σH.1, σH.2.set k tr_ext)

theorem bhPlugExtInst_of_some {S : SignalPqxdh.Setup} {ℓ : ℕ} (gs_ext : ExtState ℓ)
    (d : BHModelInst S ℓ) (gs : ExtState ℓ) (h : d.gs = some gs) :
    bhPlugExtInst gs_ext d = d := by simp [bhPlugExtInst, h]

/-- Every instance in `σ.insts` has `d.gs ≠ none`. -/
def BHAllInstsSome {S : SignalPqxdh.Setup} {ℓ : ℕ} (σ : BHE2EDrvState S ℓ) : Prop :=
  ∀ d ∈ σ.insts, d.gs ≠ none

theorem bhAllInstsSome_empty {S : SignalPqxdh.Setup} {ℓ : ℕ} :
    BHAllInstsSome ({} : BHE2EDrvState S ℓ) := by
  rintro _ ⟨⟩

/-! ## Stage-1 factorization through `bhPrefixRedWithSessionTracked` -/

theorem bhE2EStepLocalSmSessionTracked_preserves_allInstsSome {τ : Type}
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (σH : BHE2EDrvState S ℓ × List τ) (hσ : BHAllInstsSome σH.1)
    (i : ℕ) (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    {p : BHE2ESmResp ℓ × (BHE2EDrvState S ℓ × List τ)}
    (hp : p ∈ support (bhE2EStepLocalSmSessionTracked T C K qep decT encT σH i sq)) :
    BHAllInstsSome p.2.1 ∧ p.2.1.paused = σH.1.paused := by
  rw [bhE2EStepLocalSmSessionTracked_eq_filter] at hp
  by_cases hClean : (!bhE2EDrvInstClean σH.1 i) = true
  · simp only [hClean, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hp
    subst hp; exact ⟨hσ, rfl⟩
  · simp only [hClean, Bool.false_eq_true, ↓reduceIte] at hp
    cases hi : σH.1.insts[i]? with
    | none =>
      rw [hi] at hp; simp only [support_pure, Set.mem_singleton_iff] at hp
      subst hp; exact ⟨hσ, rfl⟩
    | some d =>
      rw [hi] at hp
      cases him : σH.1.instMeta[i]? with
      | none =>
        rw [him] at hp; simp only [support_pure, Set.mem_singleton_iff] at hp
        subst hp; exact ⟨hσ, rfl⟩
      | some im =>
        rw [him] at hp; dsimp only at hp
        by_cases hCorr : (!im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σH.1 d) = true
        · simp only [hCorr, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hp
          subst hp; exact ⟨hσ, rfl⟩
        · simp only [hCorr, Bool.false_eq_true, ↓reduceIte] at hp
          cases hd : d.gs with
          | none =>
            rw [hd] at hp; simp only [support_pure, Set.mem_singleton_iff] at hp
            subst hp; exact ⟨hσ, rfl⟩
          | some gs =>
            rw [hd] at hp
            cases hf : bhFilterSmQuery d im sq with
            | none =>
              rw [hf] at hp; simp only [support_pure, Set.mem_singleton_iff] at hp
              subst hp; exact ⟨hσ, rfl⟩
            | some q' =>
              rw [hf] at hp
              simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hp
              rcases hp with ⟨⟨⟨r, gs'⟩, tr'⟩, _, rfl⟩
              refine ⟨fun d' hd' => ?_, rfl⟩
              rcases List.mem_or_eq_of_mem_set hd' with hd'_old | rfl
              · exact hσ d' hd'_old
              · simp

theorem bhE2EStepLocalSmSessionTracked_with_paused {τ : Type}
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (σH : BHE2EDrvState S ℓ × List τ) (paused' : Bool) (i : ℕ)
    (q : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    bhE2EStepLocalSmSessionTracked T C K qep decT encT ({ σH.1 with paused := paused' }, σH.2) i q =
      (fun p => (p.1, ({ p.2.1 with paused := paused' }, p.2.2))) <$>
        bhE2EStepLocalSmSessionTracked T C K qep decT encT σH i q := by
  rw [bhE2EStepLocalSmSessionTracked_eq_filter, bhE2EStepLocalSmSessionTracked_eq_filter]
  dsimp only
  have hCleanEq : bhE2EDrvInstClean { σH.1 with paused := paused' } i = bhE2EDrvInstClean σH.1 i := rfl
  rw [hCleanEq]
  by_cases hClean : (!bhE2EDrvInstClean σH.1 i) = true
  · simp [hClean]
  · simp only [hClean, Bool.false_eq_true, ↓reduceIte]
    have hInsts : ({ σH.1 with paused := paused' } : BHE2EDrvState S ℓ).insts = σH.1.insts := rfl
    have hMeta : ({ σH.1 with paused := paused' } : BHE2EDrvState S ℓ).instMeta = σH.1.instMeta := rfl
    rw [hInsts, hMeta]
    cases σH.1.insts[i]? with
    | none => simp
    | some d =>
      cases σH.1.instMeta[i]? with
      | none => simp
      | some im =>
        dsimp only
        have hCorrEq : bhE2EInstIkACorr { σH.1 with paused := paused' } d = bhE2EInstIkACorr σH.1 d := rfl
        rw [hCorrEq]
        by_cases hCorr : (!im.bobAccepted && bhIsBobRecvSMQuery q && bhE2EInstIkACorr σH.1 d) = true
        · simp [hCorr]
        · simp only [hCorr, Bool.false_eq_true, ↓reduceIte]
          cases d.gs with
          | none => simp
          | some gs =>
            cases bhFilterSmQuery d im q with
            | none => simp
            | some q' =>
              simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]

private theorem bhFinishStartSpkGen_with_paused {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (C : Crypto) (K : MlKem) (σ : BHE2EDrvState S ℓ) (paused' : Bool)
    (sid : SignalPqxdh.SessionId S) (kr1 kr2 : SignalPqxdh.KeyIndResponse)
    (kb : SampledSessionKey × Bool) :
    bhFinishStartSpkGen C K { σ with paused := paused' } sid kr1 kr2 kb =
      let (idx?, σ') := bhFinishStartSpkGen C K σ sid kr1 kr2 kb
      (idx?, { σ' with paused := paused' }) := by
  unfold bhFinishStartSpkGen
  have hG : bhE2EGuard { σ with paused := paused' } sid = bhE2EGuard σ sid := rfl
  rw [hG]
  cases bhE2EGuard σ sid with
  | none => rfl
  | some val =>
    rcases val with ⟨hdr, bnd, ⟨u, j⟩⟩
    cases kr1 <;> cases kr2 <;> try rfl
    dsimp only
    split_ifs <;> rfl

set_option maxHeartbeats 800000 in
theorem bhE2EDrvImplGenWithSessionTracked_with_paused {τ : Type}
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (mkKeyBit : ModelDriverKeyBitGen)
    (q : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain)
    (σH : BHE2EDrvState S ℓ × List τ) (paused' : Bool) :
    (bhE2EDrvImplGenWithSessionTracked T ki P C K qep decT encT mkKeyBit q).run
        ({ σH.1 with paused := paused' }, σH.2) =
      (fun (r, σH') => (r, ({ σH'.1 with paused := paused' }, σH'.2))) <$>
        (bhE2EDrvImplGenWithSessionTracked T ki P C K qep decT encT mkKeyBit q).run σH := by
  rcases q with n | ((kq | ⟨⟨sid⟩⟩) | ⟨i, sq⟩)
  · change ((query (spec := unifSpec) n : ProbComp (Fin (n + 1))) >>=
        fun u => pure (u, ({ σH.1 with paused := paused' }, σH.2))) =
      ((fun (r, σH') => (r, ({ σH'.1 with paused := paused' }, σH'.2))) <$>
        ((query (spec := unifSpec) n : ProbComp (Fin (n + 1))) >>= fun u => pure (u, σH)))
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  · dsimp only [bhE2EDrvImplGenWithSessionTracked]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    have hBase : ({ σH.1 with paused := paused' } : BHE2EDrvState S ℓ).toModelDriverBase =
        σH.1.toModelDriverBase := rfl
    have hMeta : ({ σH.1 with paused := paused' } : BHE2EDrvState S ℓ).instMeta = σH.1.instMeta := rfl
    rw [hBase, hMeta]
    split_ifs
    · simp [StateT.run_pure]
    · simp [StateT.run_pure]
    · simp only [stateT_run_liftM, StateT.run_bind, StateT.run_set, StateT.run_pure,
        bind_assoc, pure_bind, map_eq_bind_pure_comp, Function.comp_def]
      refine bind_congr fun ⟨kr, st'⟩ => ?_
      have hMir : bhE2EMirror { σH.1 with paused := paused', st := st' } kq kr =
          { bhE2EMirror { σH.1 with st := st' } kq kr with paused := paused' } := by
        cases kq <;> cases kr <;> rfl
      rw [hMir]
  · dsimp only [bhE2EDrvImplGenWithSessionTracked]
    simp only [StateT.run_bind, StateT.run_get, stateT_run_liftM, StateT.run_set,
      StateT.run_pure, bind_assoc, pure_bind, Prod.mk.eta, bind_pure]
    unfold bhE2ELocalStartGenWithSessionTracked
    have hG : bhE2EGuard { σH.1 with paused := paused' } sid = bhE2EGuard σH.1 sid := rfl
    rw [hG]
    cases bhE2EGuard σH.1 sid with
    | none => simp
    | some val =>
      rcases val with ⟨hdr, bnd, ⟨u, j⟩⟩
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      refine bind_congr fun ⟨kr1, st1⟩ => bind_congr fun ⟨kr2, st2⟩ => bind_congr fun kb => ?_
      have hFin := bhFinishStartSpkGen_with_paused C K { σH.1 with st := st2 } paused' sid kr1 kr2 kb
      have hSt : ({ σH.1 with paused := paused', st := st2 } : BHE2EDrvState S ℓ) =
          { ({ σH.1 with st := st2 } : BHE2EDrvState S ℓ) with paused := paused' } := rfl
      rw [hSt, hFin]
  · dsimp only [bhE2EDrvImplGenWithSessionTracked]
    simp only [StateT.run_bind, StateT.run_get, stateT_run_liftM, StateT.run_set,
      StateT.run_pure, bind_assoc, pure_bind, bhE2EStepLocalSmSessionTracked_with_paused,
      map_eq_bind_pure_comp, Function.comp_def]

theorem simulateQ_bhE2EDrvImplGenWithSessionTracked_with_paused {τ : Type}
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type} {α : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (mkKeyBit : ModelDriverKeyBitGen)
    (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
    (σH : BHE2EDrvState S ℓ × List τ) (paused' : Bool) :
    (simulateQ (bhE2EDrvImplGenWithSessionTracked T ki P C K qep decT encT mkKeyBit) oa).run
        ({ σH.1 with paused := paused' }, σH.2) =
      (fun (r, σH') => (r, ({ σH'.1 with paused := paused' }, σH'.2))) <$>
        (simulateQ (bhE2EDrvImplGenWithSessionTracked T ki P C K qep decT encT mkKeyBit) oa).run σH := by
  induction oa using OracleComp.inductionOn generalizing σH with
  | pure x => rfl
  | query_bind q mx ih =>
    rw [run_simulateQ_query_bind, run_simulateQ_query_bind,
      bhE2EDrvImplGenWithSessionTracked_with_paused]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    exact bind_congr fun ⟨r, σH'⟩ => by
      simpa only [map_eq_bind_pure_comp, Function.comp_def] using ih r σH'

theorem simulateQ_bhE2EDrvImplGenWithSessionTracked_preserves_paused {τ : Type}
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type} {α : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (mkKeyBit : ModelDriverKeyBitGen)
    (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
    (σH : BHE2EDrvState S ℓ × List τ) :
    (fun (r, σH') => (r, ({ σH'.1 with paused := σH.1.paused }, σH'.2))) <$>
        (simulateQ (bhE2EDrvImplGenWithSessionTracked T ki P C K qep decT encT mkKeyBit) oa).run σH =
      (simulateQ (bhE2EDrvImplGenWithSessionTracked T ki P C K qep decT encT mkKeyBit) oa).run σH := by
  have h := simulateQ_bhE2EDrvImplGenWithSessionTracked_with_paused T ki P C K qep decT encT
    mkKeyBit oa σH σH.1.paused
  have hσH : ({ σH.1 with paused := σH.1.paused }, σH.2) = σH := by
    rcases σH with ⟨σ, tracks⟩; rfl
  rw [hσH] at h
  exact h.symm

theorem simulateQ_bhE2EDrvImplGenWithSessionTracked_with_b {τ : Type}
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type} {α : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (mkKeyBit : ModelDriverKeyBitGen)
    (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
    (σH : BHE2EDrvState S ℓ × List τ) (b0 : Bool) :
    (simulateQ (bhE2EDrvImplGenWithSessionTracked T ki P C K qep decT encT mkKeyBit) oa).run
        ({ σH.1 with b := b0 }, σH.2) =
      (fun (r, σH') => (r, ({ σH'.1 with b := b0 }, σH'.2))) <$>
        (simulateQ (bhE2EDrvImplGenWithSessionTracked T ki P C K qep decT encT mkKeyBit) oa).run σH := by
  induction oa using OracleComp.inductionOn generalizing σH with
  | pure x => rfl
  | query_bind q mx ih =>
    rw [run_simulateQ_query_bind, run_simulateQ_query_bind,
      bhE2EDrvImplGenWithSessionTracked_with_b]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    exact bind_congr fun ⟨r, σH'⟩ => by
      simpa only [map_eq_bind_pure_comp, Function.comp_def] using ih r σH'

theorem bhMkPrefixLazy_eq_const_false_of_gt (k len : ℕ) (b_k : Bool) (hgt : k < len) :
    bhMkPrefixLazy k b_k len = bhMkKeyBitConst false := by
  funext kr1 kr2
  have hne : (len == k) = false := beq_eq_false_iff_ne.mpr (by omega)
  have hlt : decide (len < k) = false := decide_eq_false (by omega)
  unfold bhMkPrefixLazy bhMkKeyBitConst
  simp only [hne, hlt, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  refine bind_congr fun ac => ?_
  cases kr1 <;> cases kr2 <;> rfl

theorem simulateQ_bhE2EDrvImplPrefixWithSessionTracked_mkPrefixLazy_of_gt {τ : Type}
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type} {α : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (k : ℕ) (b_k : Bool)
    (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
    (σH : BHE2EDrvState S ℓ × List τ) (hgt : k < σH.1.insts.length) :
    (simulateQ (bhE2EDrvImplPrefixWithSessionTracked T ki P C K qep decT encT (bhMkPrefixLazy k b_k))
        oa).run σH =
      (simulateQ (bhE2EDrvImplGenWithSessionTracked T ki P C K qep decT encT (bhMkKeyBitConst false))
        oa).run σH := by
  induction oa using OracleComp.inductionOn generalizing σH with
  | pure x => rfl
  | query_bind q mx ih =>
    rw [run_simulateQ_query_bind, run_simulateQ_query_bind,
      bhE2EDrvImplPrefixWithSessionTracked_run_eq_gen,
      bhMkPrefixLazy_eq_const_false_of_gt k σH.1.insts.length b_k hgt]
    refine prob_bind_congr_of_support _ _ _ (fun ⟨r, σH'⟩ hp => ?_)
    have hle :=
      (bhE2EDrvImplGenWithSessionTracked_step_length T ki P C K qep decT encT (bhMkKeyBitConst false)
        q σH hp).2.1
    exact ih r σH' (lt_of_lt_of_le hgt hle)

set_option maxHeartbeats 800000 in
theorem bhE2EDrvImplGenWithSessionTracked_const_true_step_props {τ : Type}
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (q : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain)
    (σH : BHE2EDrvState S ℓ × List τ) (hAll : BHAllInstsSome σH.1)
    (hTrackLen : σH.2.length = σH.1.insts.length)
    {p : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Range q × (BHE2EDrvState S ℓ × List τ)}
    (hp : p ∈ support
      ((bhE2EDrvImplGenWithSessionTracked T ki P C K qep decT encT (bhMkKeyBitConst true) q).run σH)) :
    BHAllInstsSome p.2.1 ∧ p.2.1.paused = σH.1.paused ∧ p.2.2.length = p.2.1.insts.length := by
  rcases q with n | ((kq | ⟨⟨sid⟩⟩) | ⟨i, sq⟩)
  · change p ∈ support ((query (spec := unifSpec) n : ProbComp _) >>= fun u => pure (u, σH)) at hp
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hp
    rcases hp with ⟨_, _, rfl⟩
    exact ⟨hAll, rfl, hTrackLen⟩
  · dsimp only [bhE2EDrvImplGenWithSessionTracked] at hp
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hp
    split_ifs at hp
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
      subst hp; exact ⟨hAll, rfl, hTrackLen⟩
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
      subst hp; exact ⟨hAll, rfl, hTrackLen⟩
    · simp only [stateT_run_liftM, StateT.run_bind, StateT.run_set, StateT.run_pure,
        bind_assoc, pure_bind, support_bind, support_pure, Set.mem_iUnion,
        Set.mem_singleton_iff] at hp
      rcases hp with ⟨⟨kr, st'⟩, _, rfl⟩
      have hMirInsts : (bhE2EMirror { σH.1 with st := st' } kq kr).insts = σH.1.insts := by
        cases kq <;> cases kr <;> rfl
      have hMirPaused : (bhE2EMirror { σH.1 with st := st' } kq kr).paused = σH.1.paused := by
        cases kq <;> cases kr <;> rfl
      refine ⟨fun d hd => hAll d (hMirInsts ▸ hd), hMirPaused, ?_⟩
      dsimp only
      rw [hMirInsts, hTrackLen]
  · rcases σH with ⟨σ, tracks⟩
    dsimp only [bhE2EDrvImplGenWithSessionTracked] at hp
    simp only [StateT.run_bind, StateT.run_get, stateT_run_liftM, StateT.run_set,
      StateT.run_pure, bind_assoc, pure_bind, Prod.mk.eta, bind_pure,
      bhE2ELocalStartGenWithSessionTracked_const_eq] at hp
    dsimp only [bhE2ELocalStartSessionTracked] at hp
    cases hG : bhE2EGuard σ sid with
    | none =>
      rw [hG] at hp
      simp only [support_pure, Set.mem_singleton_iff] at hp
      subst hp; exact ⟨hAll, rfl, hTrackLen⟩
    | some val =>
      rcases val with ⟨hdr, bnd, ⟨u, j⟩⟩
      rw [hG] at hp; dsimp only at hp
      simp only [bind_assoc, pure_bind, support_bind, support_pure, Set.mem_iUnion,
        Set.mem_singleton_iff] at hp
      rcases hp with ⟨⟨kr1, st1⟩, _, ⟨kr2, st2⟩, _, ac, _, rfl⟩
      unfold bhE2EFinishStartSpk
      have hG2 : bhE2EGuard { σ with st := st2 } sid = bhE2EGuard σ sid := rfl
      rw [hG2, hG]
      cases kr1 <;> cases kr2 <;> try exact ⟨hAll, rfl, hTrackLen⟩
      dsimp only at hAll hTrackLen ⊢
      split_ifs
      · refine ⟨fun d' hd' => ?_, rfl, ?_⟩
        · rcases List.mem_append.mp hd' with hd' | hd'
          · exact hAll d' hd'
          · rw [List.mem_singleton.mp hd']
            simp
        · simp [hTrackLen]
      · exact ⟨hAll, rfl, hTrackLen⟩
  · dsimp only [bhE2EDrvImplGenWithSessionTracked] at hp
    simp only [StateT.run_bind, StateT.run_get, stateT_run_liftM, StateT.run_set,
      StateT.run_pure, bind_assoc, pure_bind, support_bind, support_pure,
      Set.mem_iUnion, Set.mem_singleton_iff] at hp
    rcases hp with ⟨⟨sr, σH'⟩, hsm, rfl⟩
    obtain ⟨hAll', hpaused'⟩ :=
      bhE2EStepLocalSmSessionTracked_preserves_allInstsSome T C K qep decT encT σH hAll i sq hsm
    obtain ⟨hInstsLen, hTrLen⟩ :=
      bhE2EStepLocalSmSessionTracked_insts_length_eq T C K qep decT encT σH i sq hsm
    dsimp only at hAll' hpaused' hInstsLen hTrLen ⊢
    exact ⟨hAll', hpaused', by omega⟩

theorem bhStage1ToProb_pure {ℓ : ℕ} {α : Type} (x : α) :
    stageOneAsProbComp (ℓ := ℓ) (PQC := BitVec 512) (pure x) = pure x := rfl

theorem bhStage1ToProb_bind {ℓ : ℕ} {α β : Type}
    (oa : OracleComp (unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) α)
    (f : α → OracleComp (unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) β) :
    stageOneAsProbComp (ℓ := ℓ) (oa >>= f) =
      (stageOneAsProbComp (ℓ := ℓ) oa >>= fun x => stageOneAsProbComp (ℓ := ℓ) (f x)) := by
  unfold stageOneAsProbComp
  exact simulateQ_bind _ oa f

theorem bhStage1ToProb_bhLiftP {ℓ : ℕ} {α : Type} (mx : ProbComp α) :
    stageOneAsProbComp (bhLiftP (G := CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) mx) =
      mx := by
  unfold stageOneAsProbComp bhLiftP
  induction mx using OracleComp.inductionOn with
  | pure a => simp [simulateQ_pure]
  | query_bind n k ih =>
    simp only [simulateQ_query_bind, bhFwdU, simulateQ_bind, QueryImpl.add_apply_inl,
      QueryImpl.ofLift_apply, monadLift_self, bind_assoc]
    exact bind_congr ih

theorem bhStage1ToProb_bhFwdU {ℓ : ℕ} (n : ℕ) :
    stageOneAsProbComp (bhFwdU (G := CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) n) =
      (query (spec := unifSpec) n : ProbComp (Fin (n + 1))) := by
  unfold stageOneAsProbComp bhFwdU
  simp

theorem bhPrefixRedWithSessionTracked_run1_pure {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (k : ℕ) (dflt x : Bool) (fuel : ℕ) (σH : BHE2EDrvState S ℓ × List τ) :
    (bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).run1 dflt (pure x) fuel σH =
      pure (.done x σH) := rfl

theorem bhPrefixRedWithSessionTracked_run1_query_bind_inl {τ : Type}
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (k : ℕ) (dflt : Bool) (n : ℕ)
    (mx : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Range (Sum.inl n) →
      OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (fuel : ℕ) (σH : BHE2EDrvState S ℓ × List τ) :
    (bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).run1 dflt
      (liftM (OracleSpec.query (spec := unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
        (Sum.inl n)) >>= mx) fuel σH =
    (bhFwdU (G := CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) n >>= fun u =>
      (bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).run1 dflt (mx u) fuel σH) := rfl

theorem bhPrefixRedWithSessionTracked_run1_query_bind_inr_zero {τ : Type}
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (k : ℕ) (dflt : Bool) (t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain)
    (mx : (bhTargetGameSpec S ℓ (BitVec 512)).Range t →
      OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (σH : BHE2EDrvState S ℓ × List τ) :
    (bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).run1 dflt
      (liftM (OracleSpec.query (spec := unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
        (Sum.inr t)) >>= mx) 0 σH =
    pure (.done dflt σH) := rfl

theorem bhPrefixRedWithSessionTracked_run1_query_bind_inr_succ {τ : Type}
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (k : ℕ) (dflt : Bool) (t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain)
    (mx : (bhTargetGameSpec S ℓ (BitVec 512)).Range t →
      OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (f : ℕ) (σH : BHE2EDrvState S ℓ × List τ) :
    (bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).run1 dflt
      (liftM (OracleSpec.query (spec := unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
        (Sum.inr t)) >>= mx) (f + 1) σH =
    (bhPrefixHandlePreWithSessionTracked T P ki C K qep decT encT k σH (bhTargetQenc t) >>= fun step =>
      match step with
      | .inl (r, σH') =>
        (bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).run1 dflt
          (mx (bhTargetRdec t r)) f σH'
      | .inr (c, p, σH') =>
        pure (.paused t c p σH' mx)) := by
  conv_lhs => unfold BhShallowTwoStageRed.run1
  rw [construct_query_bind]
  refine bind_congr fun step => ?_
  rcases step with ⟨r, σH'⟩ | ⟨c, p, σH'⟩ <;> rfl

def bhPrefixPlugContWithSessionTracked {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (k : ℕ) (b_k : Bool)
    (o : BHPrefixCtx × Mid (bhTargetGameSpec S ℓ (BitVec 512)) Bool (Option ℕ)
      (BHE2EDrvState S ℓ × List τ) BHPrefixCtx) :
    ProbComp (Bool × (BHE2EDrvState S ℓ × List τ)) :=
  match o.2 with
  | .done a σH' => pure (a, σH')
  | .paused t _ p σH_p cont => do
    let k_fresh ← ($ᵗ SampledSessionKey : ProbComp SampledSessionKey)
    let spqr := spqrV1SessionUniformCoins C.F K
    let gs0 := initState
      (sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr o.1.idA o.1.idB) ℓ o.1.spkCoins).sendPart
      k_fresh b_k
    let tr0 := T.init k_fresh
    let v := bhTargetRdec t (.inl (.inr p))
    (simulateQ (bhE2EDrvImplGenWithSessionTracked T ki P C K qep decT encT (bhMkKeyBitConst false))
      (cont v)).run (bhPlugExtSessionTracked k gs0 tr0 σH_p)

def bhPrefixExtPairExpWithSessionTracked {τ : Type} {ℓ : ℕ}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (S : SignalPqxdh.Setup)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (k : ℕ) (b_k : Bool)
    (o : BHPrefixCtx × Mid (bhTargetGameSpec S ℓ (BitVec 512)) Bool (Option ℕ)
      (BHE2EDrvState S ℓ × List τ) BHPrefixCtx) :
    ProbComp (Bool × Bool) := do
  let (b', σH') ← bhPrefixPlugContWithSessionTracked T ki P C K qep decT encT k b_k o
  let y ← bhComposedPostObsSessionTracked P (b', σH')
  return (match o.2 with | .paused _ _ _ _ _ => true | .done _ _ => false, y)

/-- Scalar experiment at `o` in the plugged session-tracked world over `ki`. -/
def bhPrefixExtExpWithSessionTracked {τ : Type} {ℓ : ℕ}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (S : SignalPqxdh.Setup)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (k : ℕ) (b_k : Bool)
    (o : BHPrefixCtx × Mid (bhTargetGameSpec S ℓ (BitVec 512)) Bool (Option ℕ)
      (BHE2EDrvState S ℓ × List τ) BHPrefixCtx) :
    ProbComp Bool :=
  Prod.snd <$> bhPrefixExtPairExpWithSessionTracked T S ki P C K qep decT encT k b_k o

private theorem bhFinishStartSpkGen_of_not_succ' {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (C : Crypto) (K : MlKem)
    (σ : BHE2EDrvState S ℓ) (sid : SignalPqxdh.SessionId S) (kr1 kr2 : SignalPqxdh.KeyIndResponse)
    (kb : SampledSessionKey × Bool)
    (hNotSucc : ¬ ∃ (dk : SignalPqxdh.DRKey) (spkSk : SignalPqxdh.Bytes),
      kr1 = .drKeyResp dk ∧ kr2 = .spkSkResp spkSk ∧
      (dk.rootKey.length == 32 && dk.chainKey.length == 32 &&
        dk.pqrKey.length == 32 && spkSk.length == 32) = true) :
    bhFinishStartSpkGen C K σ sid kr1 kr2 kb = (none, σ) := by
  unfold bhFinishStartSpkGen
  cases bhE2EGuard σ sid with
  | none => rfl
  | some val =>
    rcases val with ⟨hdr, bnd, ⟨u, j⟩⟩
    cases kr1 <;> cases kr2 <;> try rfl
    rename_i dk spkSk
    have hLenFalse :
        (dk.rootKey.length == 32 && dk.chainKey.length == 32 &&
          dk.pqrKey.length == 32 && spkSk.length == 32) = false :=
      Bool.eq_false_iff.mpr fun h => hNotSucc ⟨dk, spkSk, rfl, rfl, h⟩
    simp [hLenFalse]

private theorem bhE2EFinishStartSpk_of_not_succ' {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (C : Crypto) (K : MlKem) (b? : Option Bool)
    (σ : BHE2EDrvState S ℓ) (sid : SignalPqxdh.SessionId S) (kr1 kr2 : SignalPqxdh.KeyIndResponse)
    (ac : BitVec 256)
    (hNotSucc : ¬ ∃ (dk : SignalPqxdh.DRKey) (spkSk : SignalPqxdh.Bytes),
      kr1 = .drKeyResp dk ∧ kr2 = .spkSkResp spkSk ∧
      (dk.rootKey.length == 32 && dk.chainKey.length == 32 &&
        dk.pqrKey.length == 32 && spkSk.length == 32) = true) :
    bhE2EFinishStartSpk C K b? σ sid kr1 kr2 ac = (none, σ) := by
  unfold bhE2EFinishStartSpk
  cases bhE2EGuard σ sid with
  | none => rfl
  | some val =>
    rcases val with ⟨hdr, bnd, ⟨u, j⟩⟩
    cases kr1 <;> cases kr2 <;> try rfl
    rename_i dk spkSk
    have hLenFalse :
        (dk.rootKey.length == 32 && dk.chainKey.length == 32 &&
          dk.pqrKey.length == 32 && spkSk.length == 32) = false :=
      Bool.eq_false_iff.mpr fun h => hNotSucc ⟨dk, spkSk, rfl, rfl, h⟩
    simp [hLenFalse]

private theorem bhMkPrefixLazy_bind_of_not_succ' {α : Type}
    (k : ℕ) (b_k : Bool) (kr1 kr2 : SignalPqxdh.KeyIndResponse)
    (m : ProbComp α)
    (hNotSucc : ¬ ∃ (dk : SignalPqxdh.DRKey) (spkSk : SignalPqxdh.Bytes),
      kr1 = .drKeyResp dk ∧ kr2 = .spkSkResp spkSk ∧
      (dk.rootKey.length == 32 && dk.chainKey.length == 32 &&
        dk.pqrKey.length == 32 && spkSk.length == 32) = true) :
    (bhMkPrefixLazy k b_k k kr1 kr2 >>= fun _ => m) =
      (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ => m) := by
  unfold bhMkPrefixLazy
  simp only [beq_self_eq_true, Bool.and_true, bind_assoc, pure_bind]
  refine bind_congr fun _ => ?_
  split
  · rename_i dk spkSk
    have hLenFalse :
        (dk.rootKey.length == 32 && dk.chainKey.length == 32 &&
          dk.pqrKey.length == 32 && spkSk.length == 32) = false :=
      Bool.eq_false_iff.mpr fun h => hNotSucc ⟨dk, spkSk, rfl, rfl, h⟩
    simp [hLenFalse]
  · simp
  · simp

theorem bhPlugExt_mapIdx_bhFinishStartSpkGen_eq {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (C : Crypto) (K : MlKem) (σ : BHE2EDrvState S ℓ) (hAll : BHAllInstsSome σ)
    (st2 : SignalPqxdh.KeyIndState S) (sid : SignalPqxdh.SessionId S)
    {hdr : SignalPqxdh.HandshakeHdr} {bnd : SignalPqxdh.PreKeyBundleInput}
    {u : Fin S.N_id} {j : Fin S.N_recv}
    (hG : bhE2EGuard σ sid = some (hdr, bnd, (u, j)))
    (dk : SignalPqxdh.DRKey) (spkSk : SignalPqxdh.Bytes)
    (hLen : (dk.rootKey.length == 32 && dk.chainKey.length == 32 &&
      dk.pqrKey.length == 32 && spkSk.length == 32) = true)
    (ac : BitVec 256) (k_fresh : SampledSessionKey) (b_k : Bool) :
    let σ_true := (bhE2EFinishStartSpk C K (some true) { σ with st := st2 } sid
      (.drKeyResp dk) (.spkSkResp spkSk) ac).2
    let k := σ.insts.length
    let spqr := spqrV1SessionUniformCoins C.F K
    let gs0 := initState
      (sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr (bhIdKeyOf hdr.ikAPk) (bhIdKeyOf bnd.ikB))
        ℓ (bhBytesWord spkSk)).sendPart k_fresh b_k
    let σ_p : BHE2EDrvState S ℓ :=
      { σ_true with
        insts := σ_true.insts.mapIdx (fun i d => if i = k then { d with gs := none } else d),
        paused := true }
    let σ_lazy := (bhFinishStartSpkGen C K { σ with st := st2 } sid
      (.drKeyResp dk) (.spkSkResp spkSk) (k_fresh, b_k)).2
    bhPlugExt gs0 σ_p = { σ_lazy with paused := true } := by
  intro σ_true k spqr gs0 σ_p σ_lazy
  have hG2 : bhE2EGuard { σ with st := st2 } sid = bhE2EGuard σ sid := rfl
  have hTrue : σ_true =
      { σ with st := st2,
               insts := σ.insts ++ [{
                 sid := sid, hdr := hdr,
                 idA := bhIdKeyOf hdr.ikAPk, idB := bhIdKeyOf bnd.ikB,
                 spkCoins := bhBytesWord spkSk,
                 gs := some (initState (sessionSchemeFixedSpk
                   (paramsIdsWithSpqr C spqr (bhIdKeyOf hdr.ikAPk) (bhIdKeyOf bnd.ikB))
                   ℓ (bhBytesWord spkSk)).sendPart (bhKeySOf dk ac) true) }],
               instMeta := σ.instMeta ++
                 [{ respPrin := some u, respSpkIdx := some j, instOpkId? := hdr.opkId? }] } := by
    dsimp only [σ_true, bhE2EFinishStartSpk, spqr]
    rw [hG2, hG]
    simp [hLen]
  have hLazy : σ_lazy =
      { σ with st := st2,
               insts := σ.insts ++ [{
                 sid := sid, hdr := hdr,
                 idA := bhIdKeyOf hdr.ikAPk, idB := bhIdKeyOf bnd.ikB,
                 spkCoins := bhBytesWord spkSk,
                 gs := some gs0 }],
               instMeta := σ.instMeta ++
                 [{ respPrin := some u, respSpkIdx := some j, instOpkId? := hdr.opkId? }] } := by
    dsimp only [σ_lazy, bhFinishStartSpkGen, spqr, gs0]
    rw [hG2, hG]
    simp [hLen]
  dsimp only [bhPlugExt, σ_p]
  rw [hTrue, hLazy]
  congr 1
  refine List.ext_getElem (by simp) fun i hi1 hi2 => ?_
  simp only [List.getElem_map, List.getElem_mapIdx]
  by_cases hlt : i < σ.insts.length
  · have hik : i ≠ k := Nat.ne_of_lt hlt
    simp only [List.getElem_append_left hlt, hik, ↓reduceIte]
    cases hgs : σ.insts[i].gs with
    | none => exact False.elim (hAll σ.insts[i] (List.getElem_mem hlt) hgs)
    | some gs => exact bhPlugExtInst_of_some gs0 σ.insts[i] gs hgs
  · have hi_eq : i = σ.insts.length := by
      simp only [List.length_append, List.length_singleton] at hi2
      omega
    subst hi_eq
    have hk_eq : σ.insts.length = k := rfl
    simp [List.getElem_append_right (le_refl _), hk_eq, bhPlugExtInst]

set_option maxHeartbeats 1200000 in
theorem simulateQ_bhE2EDrvImplPrefixWithSessionTracked_mkPrefixLazy_eq_run1_bind {τ : Type}
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (k : ℕ) (b_k : Bool)
    (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    {qB fuel : ℕ}
    (hQ : oa.IsQueryBoundP (isGameQuery (G := bhTargetGameSpec S ℓ (BitVec 512))) qB)
    (hfuel : qB ≤ fuel)
    (σH : BHE2EDrvState S ℓ × List τ) (hAll : BHAllInstsSome σH.1)
    (hle : σH.1.insts.length ≤ k) (hpaused : σH.1.paused = false)
    (hTrackLen : σH.2.length = σH.1.insts.length) :
    (simulateQ (bhE2EDrvImplPrefixWithSessionTracked T ki P C K qep decT encT (bhMkPrefixLazy k b_k))
        oa).run σH =
      ((fun (a, σH') => (a, ({ σH'.1 with paused := false }, σH'.2))) <$>
        (stageOneAsProbComp
            ((bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).run1 false oa fuel σH) >>=
          fun m => bhPrefixPlugContWithSessionTracked T ki P C K qep decT encT k b_k
            (match m with
             | .done _ _ => bhDefaultPrefixCtx
             | .paused _ c _ _ _ => c, m))) := by
  induction oa using OracleComp.inductionOn generalizing qB fuel σH with
  | pure x =>
    have hσH : ({ σH.1 with paused := false }, σH.2) = σH := by
      rcases σH with ⟨σ, tracks⟩; cases σ; simp_all
    simp [bhPrefixRedWithSessionTracked_run1_pure, bhStage1ToProb_pure,
      bhPrefixPlugContWithSessionTracked, hσH]
  | query_bind q mx ih =>
    rw [isQueryBoundP_query_bind_iff] at hQ
    cases q with
    | inl n =>
      rw [run_simulateQ_query_bind]
      have hRun1 :
          stageOneAsProbComp ((bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).run1 false
            (liftM (OracleSpec.query (Sum.inl n)) >>= mx) fuel σH) =
          ((query (spec := unifSpec) n : ProbComp (Fin (n + 1))) >>= fun u =>
            stageOneAsProbComp
              ((bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).run1 false (mx u) fuel σH)) := by
        rw [bhPrefixRedWithSessionTracked_run1_query_bind_inl, bhStage1ToProb_bind,
          bhStage1ToProb_bhFwdU]
      rw [hRun1]
      simp only [bhE2EDrvImplPrefixWithSessionTracked_run_eq_gen, map_eq_bind_pure_comp,
        Function.comp_def, bind_assoc, pure_bind]
      change ((query (spec := unifSpec) n : ProbComp (Fin (n + 1))) >>= fun u =>
          (simulateQ (bhE2EDrvImplPrefixWithSessionTracked T ki P C K qep decT encT (bhMkPrefixLazy k b_k))
            (mx u)).run σH) = _
      refine bind_congr fun u => ?_
      simpa only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind] using
        ih u (hQ.2 u) hfuel σH hAll hle hpaused hTrackLen
    | inr t =>
      have hpos : 0 < qB := hQ.1.resolve_left (by simp [isGameQuery])
      obtain ⟨m, rfl⟩ : ∃ m, qB = m + 1 := ⟨qB - 1, by omega⟩
      have hqm : ∀ v, (mx v).IsQueryBoundP
          (isGameQuery (G := bhTargetGameSpec S ℓ (BitVec 512))) m := by
        intro v; simpa [isGameQuery] using hQ.2 v
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hle_f : m ≤ f := by omega
      rw [run_simulateQ_query_bind, bhE2EDrvImplPrefixWithSessionTracked_run_eq_gen]
      rcases t with (kq | ctl) | ⟨i, sq⟩
      ·
        have hRun1 :
            stageOneAsProbComp ((bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).run1 false
              (liftM (OracleSpec.query (spec := unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
                (Sum.inr (.inl (.inl kq)))) >>= mx) (f + 1) σH) =
            ((bhE2EDrvImplGenWithSessionTracked T ki P C K qep decT encT (bhMkKeyBitConst true)
                (.inr (.inl (.inl kq)))).run σH >>= fun ⟨r, σH'⟩ =>
              stageOneAsProbComp
                ((bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).run1 false (mx r) f σH')) := by
          rw [bhPrefixRedWithSessionTracked_run1_query_bind_inr_succ]
          simp only [bhPrefixHandlePreWithSessionTracked, bhTargetQenc, bhTargetRdec,
            bhShallowStepPreNonCtlSessionTracked, bhStage1ToProb_bind, bhStage1ToProb_bhLiftP,
            bhStage1ToProb_pure, bind_assoc, pure_bind]
          dsimp only [bhE2EDrvImplGenWithSessionTracked]
          simp only [StateT.run_bind, StateT.run_get, pure_bind]
          by_cases hOk : (!bhDrvKiQueryOk P σH.1.toModelDriverBase kq) = true
          · simp only [hOk, ↓reduceIte, StateT.run_pure, pure_bind]
          · simp only [hOk, Bool.false_eq_true, ↓reduceIte]
            split_ifs
            · simp only [StateT.run_pure, pure_bind]
            · simp only [stateT_run_liftM, StateT.run_bind, StateT.run_map, StateT.run_set,
                StateT.run_pure, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
        have hLHS_step :
            (bhE2EDrvImplGenWithSessionTracked T ki P C K qep decT encT
              (bhMkPrefixLazy k b_k σH.1.insts.length) (.inr (.inl (.inl kq)))).run σH =
            (bhE2EDrvImplGenWithSessionTracked T ki P C K qep decT encT (bhMkKeyBitConst true)
              (.inr (.inl (.inl kq)))).run σH := rfl
        rw [hLHS_step, hRun1]
        simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
        refine prob_bind_congr_of_support _ _ _ (fun ⟨r, σH'⟩ hp => ?_)
        obtain ⟨hAll', hpaused', hTrackLen'⟩ :=
          bhE2EDrvImplGenWithSessionTracked_const_true_step_props T ki P C K qep decT encT
            (.inr (.inl (.inl kq))) σH hAll hTrackLen hp
        have hlen' :=
          (bhE2EDrvImplGenWithSessionTracked_step_length T ki P C K qep decT encT (bhMkKeyBitConst true)
            (.inr (.inl (.inl kq))) σH hp).1 rfl
        dsimp only at hlen'
        simpa only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind] using
          ih r (hqm r) hle_f σH' hAll' (by omega) (hpaused'.trans hpaused) hTrackLen'
      ·
        rcases ctl with ⟨sid⟩
        have hRun1 :
            stageOneAsProbComp ((bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).run1 false
              (liftM (OracleSpec.query (spec := unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
                (Sum.inr (.inl (.inr (.startDR sid))))) >>= mx) (f + 1) σH) =
            (bhE2ELocalStartSessionTracked T.init ki C K (some true) σH sid >>= fun ⟨idx?, (σ', tracks')⟩ =>
              if k < σ'.insts.length then
                let ctx : BHPrefixCtx := match σ'.insts[k]? with
                  | some d => { idA := d.idA, idB := d.idB, spkCoins := d.spkCoins }
                  | none => { idA := bhIdKeyOf [], idB := bhIdKeyOf [], spkCoins := 0 }
                let insts' := σ'.insts.mapIdx (fun i d => if i = k then { d with gs := none } else d)
                pure (.paused (.inl (.inr (.startDR sid))) ctx idx?
                  ({ σ' with insts := insts', paused := true }, tracks') mx)
              else
                stageOneAsProbComp
                  ((bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).run1 false (mx idx?) f
                    (σ', tracks'))) := by
          rw [bhPrefixRedWithSessionTracked_run1_query_bind_inr_succ]
          simp only [bhPrefixHandlePreWithSessionTracked, bhTargetQenc, bhTargetRdec,
            bhShallowStepPreCtlSessionTracked, bhStage1ToProb_bind, bhStage1ToProb_bhLiftP,
            bhStage1ToProb_pure, bind_assoc, pure_bind]
          refine bind_congr fun p => ?_
          rcases p with ⟨idx?, ⟨σ', tracks'⟩⟩
          dsimp only
          split_ifs
          · rfl
          · simp [bhStage1ToProb_pure]
        rw [hRun1]
        by_cases hlt : σH.1.insts.length < k
        ·
          have hmk : bhMkPrefixLazy k b_k σH.1.insts.length = bhMkKeyBitConst true := by
            funext kr1 kr2
            have hne : (σH.1.insts.length == k) = false := beq_eq_false_iff_ne.mpr (by omega)
            have hlt_dec : decide (σH.1.insts.length < k) = true := decide_eq_true hlt
            unfold bhMkPrefixLazy bhMkKeyBitConst
            simp only [hne, hlt_dec, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
            refine bind_congr fun ac => ?_
            cases kr1 <;> cases kr2 <;> rfl
          have hLHS_step :
              (bhE2EDrvImplGenWithSessionTracked T ki P C K qep decT encT
                (bhMkPrefixLazy k b_k σH.1.insts.length) (.inr (.inl (.inr (.startDR sid))))).run σH =
              bhE2ELocalStartSessionTracked T.init ki C K (some true) σH sid := by
            rw [hmk]
            dsimp only [bhE2EDrvImplGenWithSessionTracked]
            simp [StateT.run_bind, StateT.run_get, stateT_run_liftM, StateT.run_set,
              StateT.run_pure, bind_assoc, pure_bind, Prod.mk.eta, bind_pure,
              bhE2ELocalStartGenWithSessionTracked_const_eq]
          rw [hLHS_step]
          simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
          refine prob_bind_congr_of_support _ _ _ (fun ⟨idx?, σH'⟩ hp => ?_)
          have hp' : (idx?, σH') ∈ support ((bhE2EDrvImplGenWithSessionTracked T ki P C K qep decT encT
              (bhMkKeyBitConst true) (.inr (.inl (.inr (.startDR sid))))).run σH) := by
            dsimp only [bhE2EDrvImplGenWithSessionTracked]
            simpa [StateT.run_bind, StateT.run_get, stateT_run_liftM, StateT.run_set,
              StateT.run_pure, bind_assoc, pure_bind, Prod.mk.eta, bind_pure,
              bhE2ELocalStartGenWithSessionTracked_const_eq] using hp
          obtain ⟨hAll', hpaused', hTrackLen'⟩ :=
            bhE2EDrvImplGenWithSessionTracked_const_true_step_props T ki P C K qep decT encT
              (.inr (.inl (.inr (.startDR sid)))) σH hAll hTrackLen hp'
          have hlen_le :=
            (bhE2EDrvImplGenWithSessionTracked_step_length T ki P C K qep decT encT (bhMkKeyBitConst true)
              (.inr (.inl (.inr (.startDR sid)))) σH hp').2.2
          dsimp only at hlen_le
          have hNotGt : ¬ (k < σH'.1.insts.length) := by omega
          rcases σH' with ⟨σ', tracks'⟩
          dsimp only at hNotGt hAll' hpaused' hTrackLen' hlen_le ⊢
          simp only [hNotGt, ↓reduceIte]
          simpa only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind] using
            ih idx? (hqm idx?) hle_f (σ', tracks') hAll' (by dsimp only; omega)
              (hpaused'.trans hpaused) hTrackLen'
        ·
          rcases σH with ⟨σ, tracks⟩
          dsimp only at hAll hle hpaused hTrackLen hlt ⊢
          have hlen_eq : σ.insts.length = k := by omega
          subst hlen_eq
          dsimp only [bhE2EDrvImplGenWithSessionTracked]
          simp only [StateT.run_bind, StateT.run_get, stateT_run_liftM, StateT.run_set,
            StateT.run_pure, bind_assoc, pure_bind, Prod.mk.eta, bind_pure]
          unfold bhE2ELocalStartGenWithSessionTracked bhE2ELocalStartSessionTracked
          dsimp only
          cases hG : bhE2EGuard σ sid with
          | none =>
            simp only [pure_bind, lt_irrefl, ↓reduceIte]
            exact ih none (hqm none) hle_f (σ, tracks) hAll le_rfl hpaused hTrackLen
          | some val =>
            rcases val with ⟨hdr, bnd, ⟨u, j⟩⟩
            simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
            refine bind_congr fun p1 => bind_congr fun p2 => ?_
            rcases p1 with ⟨kr1, st1⟩
            rcases p2 with ⟨kr2, st2⟩
            dsimp only
            by_cases hSucc :
                ∃ (dk : SignalPqxdh.DRKey) (spkSk : SignalPqxdh.Bytes),
                  kr1 = .drKeyResp dk ∧ kr2 = .spkSkResp spkSk ∧
                  (dk.rootKey.length == 32 && dk.chainKey.length == 32 &&
                    dk.pqrKey.length == 32 && spkSk.length == 32) = true
            · rcases hSucc with ⟨dk, spkSk, rfl, rfl, hLen⟩
              have hMkSucc :
                  bhMkPrefixLazy σ.insts.length b_k σ.insts.length
                    (.drKeyResp dk) (.spkSkResp spkSk) =
                  (do
                    let _ ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
                    let k_fresh ← ($ᵗ SampledSessionKey : ProbComp SampledSessionKey)
                    return (k_fresh, b_k)) := by
                unfold bhMkPrefixLazy
                simp [hLen]
              rw [hMkSucc]
              simp only [bind_assoc, pure_bind]
              refine bind_congr fun ac => ?_
              let σ_true := (bhE2EFinishStartSpk C K (some true) { σ with st := st2 } sid
                (.drKeyResp dk) (.spkSkResp spkSk) ac).2
              have hG2 : bhE2EGuard { σ with st := st2 } sid = bhE2EGuard σ sid := rfl
              have hIdxTrue :
                  (bhE2EFinishStartSpk C K (some true) { σ with st := st2 } sid
                    (.drKeyResp dk) (.spkSkResp spkSk) ac).1 = some σ.insts.length := by
                unfold bhE2EFinishStartSpk
                rw [hG2, hG]
                simp [hLen]
              have hFinishTrue :
                  bhE2EFinishStartSpk C K (some true) { σ with st := st2 } sid
                    (.drKeyResp dk) (.spkSkResp spkSk) ac = (some σ.insts.length, σ_true) :=
                Prod.ext hIdxTrue rfl
              have hLenTrue : σ.insts.length < σ_true.insts.length := by
                dsimp only [σ_true, bhE2EFinishStartSpk]
                rw [hG2, hG]
                simp [hLen]
              have hGetK : σ_true.insts[σ.insts.length]? =
                  some { sid := sid, hdr := hdr,
                         idA := bhIdKeyOf hdr.ikAPk, idB := bhIdKeyOf bnd.ikB,
                         spkCoins := bhBytesWord spkSk,
                         gs := some (initState (sessionSchemeFixedSpk
                           (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K)
                             (bhIdKeyOf hdr.ikAPk) (bhIdKeyOf bnd.ikB))
                           ℓ (bhBytesWord spkSk)).sendPart (bhKeySOf dk ac) true) } := by
                dsimp only [σ_true, bhE2EFinishStartSpk]
                rw [hG2, hG]
                simp only [hLen, ↓reduceIte]
                rw [List.getElem?_append_right (le_refl _), Nat.sub_self]
                rfl
              simp only [hFinishTrue, hLenTrue, ↓reduceIte, hGetK, bhStage1ToProb_pure, pure_bind]
              unfold bhPrefixPlugContWithSessionTracked
              dsimp only [bhTargetRdec]
              simp only [bind_assoc, pure_bind]
              refine bind_congr fun k_fresh => ?_
              let σ_lazy := (bhFinishStartSpkGen C K { σ with st := st2 } sid
                (.drKeyResp dk) (.spkSkResp spkSk) (k_fresh, b_k)).2
              have hIdxLazy :
                  (bhFinishStartSpkGen C K { σ with st := st2 } sid
                    (.drKeyResp dk) (.spkSkResp spkSk) (k_fresh, b_k)).1 =
                    some σ.insts.length := by
                unfold bhFinishStartSpkGen
                rw [hG2, hG]
                simp [hLen]
              have hLenLazy : σ.insts.length < σ_lazy.insts.length := by
                dsimp only [σ_lazy, bhFinishStartSpkGen]
                rw [hG2, hG]
                simp [hLen]
              have hLazyPaused : σ_lazy.paused = false := by
                dsimp only [σ_lazy, bhFinishStartSpkGen]
                rw [hG2, hG]
                simp [hLen, hpaused]
              have hTracksSet :
                  (tracks ++ [T.init (bhKeySOf dk ac)]).set σ.insts.length (T.init k_fresh) =
                    tracks ++ [T.init k_fresh] := by
                simp [List.set_append, hTrackLen]
              have hPlugTracked :
                  bhPlugExtSessionTracked σ.insts.length
                    (initState (sessionSchemeFixedSpk
                      (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K)
                        (bhIdKeyOf hdr.ikAPk) (bhIdKeyOf bnd.ikB))
                      ℓ (bhBytesWord spkSk)).sendPart k_fresh b_k)
                    (T.init k_fresh)
                    ({ σ_true with
                       insts := σ_true.insts.mapIdx
                         (fun i d => if i = σ.insts.length then { d with gs := none } else d),
                       paused := true },
                     tracks ++ [T.init (bhKeySOf dk ac)]) =
                  ({ σ_lazy with paused := true }, tracks ++ [T.init k_fresh]) := by
                unfold bhPlugExtSessionTracked
                exact Prod.ext
                  (bhPlugExt_mapIdx_bhFinishStartSpkGen_eq C K σ hAll st2 sid hG dk spkSk
                    hLen ac k_fresh b_k)
                  hTracksSet
              simp only [hIdxLazy, Option.isSome_some, ↓reduceIte]
              rw [simulateQ_bhE2EDrvImplPrefixWithSessionTracked_mkPrefixLazy_of_gt T ki P C K qep
                  decT encT σ.insts.length b_k (mx (some σ.insts.length))
                  (σ_lazy, tracks ++ [T.init k_fresh]) hLenLazy,
                hPlugTracked,
                simulateQ_bhE2EDrvImplGenWithSessionTracked_with_paused T ki P C K qep decT encT
                  (bhMkKeyBitConst false) (mx (some σ.insts.length))
                  (σ_lazy, tracks ++ [T.init k_fresh]) true]
              have hPres := simulateQ_bhE2EDrvImplGenWithSessionTracked_preserves_paused T ki P C K
                qep decT encT (bhMkKeyBitConst false) (mx (some σ.insts.length))
                (σ_lazy, tracks ++ [T.init k_fresh])
              dsimp only at hPres
              rw [hLazyPaused] at hPres
              simpa only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind] using
                hPres.symm
            · simp only [bhFinishStartSpkGen_of_not_succ' C K { σ with st := st2 } sid kr1 kr2 _ hSucc,
                bhE2EFinishStartSpk_of_not_succ' C K (some true) { σ with st := st2 } sid kr1 kr2 _ hSucc,
                bhMkPrefixLazy_bind_of_not_succ' σ.insts.length b_k kr1 kr2 _ hSucc,
                Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
              refine bind_congr fun _ => ?_
              have hlt_false :
                  ¬ (σ.insts.length < ({ σ with st := st2 } : BHE2EDrvState S ℓ).insts.length) :=
                Nat.lt_irrefl _
              simp only [hlt_false, ↓reduceIte]
              simpa only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind] using
                ih none (hqm none) hle_f ({ σ with st := st2 }, tracks) hAll le_rfl hpaused hTrackLen
      ·
        have hRun1 :
            stageOneAsProbComp ((bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).run1 false
              (liftM (OracleSpec.query (spec := unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
                (Sum.inr (.inr ⟨i, sq⟩))) >>= mx) (f + 1) σH) =
            (bhE2EStepLocalSmSessionTracked T C K qep decT encT σH i sq >>= fun ⟨sr, σH'⟩ =>
              stageOneAsProbComp ((bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).run1 false
                (mx (bhUnpackSmResp sq sr)) f σH')) := by
          rw [bhPrefixRedWithSessionTracked_run1_query_bind_inr_succ]
          simp only [bhPrefixHandlePreWithSessionTracked, bhTargetQenc, bhTargetRdec,
            bhShallowStepPreNonCtlSessionTracked, bhStage1ToProb_bind, bhStage1ToProb_bhLiftP,
            bhStage1ToProb_pure, bind_assoc, pure_bind]
        have hLHS_step :
            (bhE2EDrvImplGenWithSessionTracked T ki P C K qep decT encT
              (bhMkPrefixLazy k b_k σH.1.insts.length) (.inr (.inr ⟨i, sq⟩))).run σH =
            (bhE2EStepLocalSmSessionTracked T C K qep decT encT σH i sq >>= fun ⟨sr, σH'⟩ =>
              pure (bhUnpackSmResp sq sr, σH')) := by
          dsimp only [bhE2EDrvImplGenWithSessionTracked]
          simp [StateT.run_bind, StateT.run_get, stateT_run_liftM, StateT.run_set,
            StateT.run_pure, bind_assoc, pure_bind]
        rw [hLHS_step, hRun1]
        simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
        refine prob_bind_congr_of_support _ _ _ (fun ⟨sr, σH'⟩ hsm => ?_)
        obtain ⟨hAll', hpaused'⟩ :=
          bhE2EStepLocalSmSessionTracked_preserves_allInstsSome T C K qep decT encT σH hAll i sq hsm
        obtain ⟨hInstsLen, hTrLen⟩ :=
          bhE2EStepLocalSmSessionTracked_insts_length_eq T C K qep decT encT σH i sq hsm
        dsimp only at hInstsLen hTrLen
        simpa only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind] using
          ih (bhUnpackSmResp sq sr) (hqm _) hle_f σH' hAll' (by omega) (hpaused'.trans hpaused)
            (by omega)

theorem bhStage1ToProb_eval1_withSessionTracked_eq_run1_bind {τ : Type}
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (k qTot : ℕ) (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) :
    stageOneAsProbComp
        ((bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).eval1 (fun _ => B) () qTot false) =
      (stageOneAsProbComp
          ((bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).run1 false B qTot ({}, [])) >>=
        fun m =>
          pure (match m with
            | .done _ _ => bhDefaultPrefixCtx
            | .paused _ c _ _ _ => c, m)) := by
  unfold BhShallowTwoStageRed.eval1
  dsimp only [bhPrefixRedWithSessionTracked, bhDefaultPrefixCtx]
  simp only [bhStage1ToProb_bind, bhStage1ToProb_pure, bind_assoc, pure_bind]
  refine bind_congr fun m => ?_
  cases m <;> rfl

theorem bhPrefixLazyFullExpWithSessionTracked_eq_bind_bhPrefixExtExpWithSessionTracked {τ : Type}
    {ℓ : ℕ}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (S : SignalPqxdh.Setup)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (k qTot : ℕ) (b_k : Bool)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hQ : B.IsQueryBoundP (isGameQuery (G := bhTargetGameSpec S ℓ (BitVec 512))) qTot) :
    bhPrefixLazyFullExpWithSessionTracked T S ki P C K qep decT encT k b_k B =
      (stageOneAsProbComp
          ((bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).eval1 (fun _ => B) () qTot false) >>=
        bhPrefixExtExpWithSessionTracked T S ki P C K qep decT encT k b_k) := by
  unfold bhPrefixLazyFullExpWithSessionTracked
  rw [simulateQ_bhE2EDrvImplPrefixWithSessionTracked_mkPrefixLazy_eq_run1_bind T ki P C K qep
      decT encT k b_k B hQ le_rfl ({}, []) bhAllInstsSome_empty (Nat.zero_le k) rfl rfl,
    bhStage1ToProb_eval1_withSessionTracked_eq_run1_bind]
  simp only [bhPrefixExtExpWithSessionTracked, bhPrefixExtPairExpWithSessionTracked,
    map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  congr 1; funext m
  cases m <;>
  · congr 1; funext p; rcases p with ⟨_, _⟩
    simp only [bhComposedPostObsSessionTracked, bhComposedPostObs, bind_pure]
    rfl

end Computational.Proofs.LibsignalCli.MainHaltedPrefixFactor
