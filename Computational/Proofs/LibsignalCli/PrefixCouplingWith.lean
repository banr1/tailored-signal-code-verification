/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.LibsignalCli.PrefixCouplingWithCore
import Computational.Proofs.ReductionDsl.Bridge
import VCVio.EvalDist.Monad.Basic

/-!
# Polymorphic `bhPrefixRedWith` Prefix-Hybrid Telescope

**Checked by Lean.** Generalizes the Stage-1/Stage-2 prefix factorization and `qStart`-step
prefix-hybrid telescope of `BhPrefixCouplingV1` to an arbitrary key-indistinguishability oracle
`ki` under an explicit lazy-replacement hypothesis `hLazyEq`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

open scoped ENNReal BigOperators
open OracleComp OracleSpec MeasureTheory
open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme MACScheme WireAEAD FSAEAD
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.E2E CryptoVerification.E2E.Prefix CryptoVerification.E2E.Signed
  ReductionDsl

namespace CryptoVerification.E2E.Prefix1Key

open CryptoVerification.E2E

variable {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}

@[simp]
private theorem stateT_run_lift {M : Type → Type} [Monad M] {σ α : Type}
    (mx : M α) (s : σ) :
    (StateT.lift mx : StateT σ M α).run s = (mx >>= fun x => pure (x, s)) := rfl

@[simp]
private theorem stateT_run_liftM {M : Type → Type} [Monad M] {σ α : Type}
    (mx : M α) (s : σ) :
    (liftM mx : StateT σ M α).run s = (mx >>= fun x => pure (x, s)) := rfl

/-! ## Stage-1 factorization through `bhPrefixRedWith` -/

section PrefixFactorizationWith

set_option maxHeartbeats 800000 in
theorem bhE2EDrvImplGenWith_with_paused
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (mkKeyBit : ModelDriverKeyBitGen)
    (q : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain)
    (σ : BHE2EDrvState S ℓ) (paused' : Bool) :
    (bhE2EDrvImplGenWith ki P C K qep decT encT mkKeyBit q).run { σ with paused := paused' } =
      (fun (r, σ') => (r, { σ' with paused := paused' })) <$>
        (bhE2EDrvImplGenWith ki P C K qep decT encT mkKeyBit q).run σ := by
  rcases q with n | ((kq | ⟨⟨sid⟩⟩) | ⟨i, sq⟩)
  · change ((query (spec := unifSpec) n : ProbComp (Fin (n + 1))) >>=
        fun u => pure (u, { σ with paused := paused' })) =
      ((fun (r, σ') => (r, { σ' with paused := paused' })) <$>
        ((query (spec := unifSpec) n : ProbComp (Fin (n + 1))) >>= fun u => pure (u, σ)))
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  · dsimp only [bhE2EDrvImplGenWith]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    have hBase : ({ σ with paused := paused' } : BHE2EDrvState S ℓ).toModelDriverBase =
        σ.toModelDriverBase := rfl
    have hMeta : ({ σ with paused := paused' } : BHE2EDrvState S ℓ).instMeta = σ.instMeta := rfl
    rw [hBase, hMeta]
    split_ifs
    · simp [StateT.run_pure]
    · simp [StateT.run_pure]
    · simp only [stateT_run_liftM, StateT.run_bind, StateT.run_set, StateT.run_pure,
        bind_assoc, pure_bind, map_eq_bind_pure_comp, Function.comp_def]
      rfl
  · dsimp only [bhE2EDrvImplGenWith]
    simp only [StateT.run_bind, StateT.run_get, stateT_run_liftM, StateT.run_set,
      StateT.run_pure, bind_assoc, pure_bind, Prod.mk.eta, bind_pure]
    unfold bhE2ELocalStartGenWith
    have hG : bhE2EGuard { σ with paused := paused' } sid = bhE2EGuard σ sid := rfl
    rw [hG]
    cases bhE2EGuard σ sid with
    | none => simp
    | some val =>
      rcases val with ⟨hdr, bnd, ⟨u, j⟩⟩
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      refine bind_congr fun ⟨kr1, st1⟩ => bind_congr fun ⟨kr2, st2⟩ => bind_congr fun kb => ?_
      unfold bhFinishStartSpkGen
      have hG2 : bhE2EGuard { σ with paused := paused', st := st2 } sid =
          bhE2EGuard { σ with st := st2 } sid := rfl
      rw [hG2]
      cases bhE2EGuard { σ with st := st2 } sid with
      | none => rfl
      | some val2 =>
        rcases val2 with ⟨hdr2, bnd2, ⟨u2, j2⟩⟩
        cases kr1 <;> cases kr2 <;> try rfl
        dsimp only
        split_ifs <;> rfl
  · dsimp only [bhE2EDrvImplGenWith]
    simp only [StateT.run_bind, StateT.run_get, stateT_run_liftM, StateT.run_set,
      StateT.run_pure, bind_assoc, pure_bind, bhE2EStepLocalSm_with_paused,
      map_eq_bind_pure_comp, Function.comp_def]

theorem simulateQ_bhE2EDrvImplGenWith_with_paused {α : Type}
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (mkKeyBit : ModelDriverKeyBitGen)
    (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
    (σ : BHE2EDrvState S ℓ) (paused' : Bool) :
    (simulateQ (bhE2EDrvImplGenWith ki P C K qep decT encT mkKeyBit) oa).run
        { σ with paused := paused' } =
      (fun (r, σ') => (r, { σ' with paused := paused' })) <$>
        (simulateQ (bhE2EDrvImplGenWith ki P C K qep decT encT mkKeyBit) oa).run σ := by
  induction oa using OracleComp.inductionOn generalizing σ with
  | pure x => rfl
  | query_bind q mx ih =>
    rw [run_simulateQ_query_bind, run_simulateQ_query_bind, bhE2EDrvImplGenWith_with_paused]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    exact bind_congr fun ⟨r, σ'⟩ => by
      simpa only [map_eq_bind_pure_comp, Function.comp_def] using ih r σ'

theorem simulateQ_bhE2EDrvImplGenWith_preserves_paused {α : Type}
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (mkKeyBit : ModelDriverKeyBitGen)
    (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
    (σ : BHE2EDrvState S ℓ) :
    (fun (r, σ') => (r, { σ' with paused := σ.paused })) <$>
        (simulateQ (bhE2EDrvImplGenWith ki P C K qep decT encT mkKeyBit) oa).run σ =
      (simulateQ (bhE2EDrvImplGenWith ki P C K qep decT encT mkKeyBit) oa).run σ := by
  have h := simulateQ_bhE2EDrvImplGenWith_with_paused ki P C K qep decT encT mkKeyBit oa σ σ.paused
  have hσ : { σ with paused := σ.paused } = σ := rfl
  rw [hσ] at h
  exact h.symm

theorem simulateQ_bhE2EDrvImplGenWith_with_b {α : Type}
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (mkKeyBit : ModelDriverKeyBitGen)
    (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
    (σ : BHE2EDrvState S ℓ) (b0 : Bool) :
    (simulateQ (bhE2EDrvImplGenWith ki P C K qep decT encT mkKeyBit) oa).run { σ with b := b0 } =
      (fun (r, σ') => (r, { σ' with b := b0 })) <$>
        (simulateQ (bhE2EDrvImplGenWith ki P C K qep decT encT mkKeyBit) oa).run σ := by
  induction oa using OracleComp.inductionOn generalizing σ with
  | pure x => rfl
  | query_bind q mx ih =>
    rw [run_simulateQ_query_bind, run_simulateQ_query_bind, bhE2EDrvImplGenWith_with_b]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    exact bind_congr fun ⟨r, σ'⟩ => by
      simpa only [map_eq_bind_pure_comp, Function.comp_def] using ih r σ'

theorem simulateQ_bhE2EDrvImplPrefixWith_mkPrefixLazy_of_gt {α : Type}
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (k : ℕ) (b_k : Bool)
    (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
    (σ : BHE2EDrvState S ℓ) (hgt : k < σ.insts.length) :
    (simulateQ (bhE2EDrvImplPrefixWith ki P C K qep decT encT (bhMkPrefixLazy k b_k)) oa).run σ =
      (simulateQ (bhE2EDrvImplGenWith ki P C K qep decT encT (bhMkKeyBitConst false)) oa).run σ := by
  induction oa using OracleComp.inductionOn generalizing σ with
  | pure x => rfl
  | query_bind q mx ih =>
    rw [run_simulateQ_query_bind, run_simulateQ_query_bind,
      bhE2EDrvImplPrefixWith_run_eq_gen,
      bhMkPrefixLazy_eq_const_false_of_gt k σ.insts.length b_k hgt]
    refine prob_bind_congr_of_support _ _ _ (fun ⟨r, σ'⟩ hp => ?_)
    have hle :=
      (bhE2EDrvImplGenWith_step_length ki P C K qep decT encT (bhMkKeyBitConst false) q σ hp).2.1
    exact ih r σ' (lt_of_lt_of_le hgt hle)

set_option maxHeartbeats 800000 in
theorem bhE2EDrvImplGenWith_const_true_step_props
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (q : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain)
    (σ : BHE2EDrvState S ℓ) (hAll : BHAllInstsSome σ)
    {p : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Range q × BHE2EDrvState S ℓ}
    (hp : p ∈ support
      ((bhE2EDrvImplGenWith ki P C K qep decT encT (bhMkKeyBitConst true) q).run σ)) :
    BHAllInstsSome p.2 ∧ p.2.paused = σ.paused := by
  rcases q with n | ((kq | ⟨⟨sid⟩⟩) | ⟨i, sq⟩)
  · change p ∈ support ((query (spec := unifSpec) n : ProbComp _) >>= fun u => pure (u, σ)) at hp
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hp
    rcases hp with ⟨_, _, rfl⟩
    exact ⟨hAll, rfl⟩
  · dsimp only [bhE2EDrvImplGenWith] at hp
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hp
    split_ifs at hp
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
      subst hp; exact ⟨hAll, rfl⟩
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
      subst hp; exact ⟨hAll, rfl⟩
    · simp only [stateT_run_liftM, StateT.run_bind, StateT.run_set, StateT.run_pure,
        bind_assoc, pure_bind, support_bind, support_pure, Set.mem_iUnion,
        Set.mem_singleton_iff] at hp
      rcases hp with ⟨⟨kr, st'⟩, _, rfl⟩
      exact ⟨hAll, rfl⟩
  · dsimp only [bhE2EDrvImplGenWith] at hp
    simp only [StateT.run_bind, StateT.run_get, stateT_run_liftM, StateT.run_set,
      StateT.run_pure, bind_assoc, pure_bind, Prod.mk.eta, bind_pure,
      bhE2ELocalStartGenWith_const_eq] at hp
    unfold compositionLocalStart at hp
    cases hG : bhE2EGuard σ sid with
    | none =>
      rw [hG] at hp
      simp only [support_pure, Set.mem_singleton_iff] at hp
      subst hp; exact ⟨hAll, rfl⟩
    | some val =>
      rcases val with ⟨hdr, bnd, ⟨u, j⟩⟩
      rw [hG] at hp; dsimp only at hp
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hp
      rcases hp with ⟨⟨kr1, st1⟩, _, ⟨kr2, st2⟩, _, ac, _, rfl⟩
      unfold bhE2EFinishStartSpk
      simp only [bhE2EGuard_with_st, hG]
      cases kr1 <;> cases kr2 <;> try exact ⟨hAll, rfl⟩
      dsimp only
      split_ifs
      · refine ⟨fun d' hd' => ?_, rfl⟩
        rcases List.mem_append.mp hd' with hd' | hd'
        · exact hAll d' hd'
        · rw [List.mem_singleton.mp hd']
          simp
      · exact ⟨hAll, rfl⟩
  · dsimp only [bhE2EDrvImplGenWith] at hp
    simp only [StateT.run_bind, StateT.run_get, stateT_run_liftM, StateT.run_set,
      StateT.run_pure, bind_assoc, pure_bind, support_bind, support_pure,
      Set.mem_iUnion, Set.mem_singleton_iff] at hp
    rcases hp with ⟨⟨sr, σ'⟩, hsm, rfl⟩
    exact bhE2EStepLocalSm_preserves_allInstsSome C K qep decT encT σ hAll i sq hsm

@[simp]
theorem bhStage1ToProb_bhLiftP {α : Type} (mx : ProbComp α) :
    stageOneAsProbComp (bhLiftP (G := SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) mx) = mx := by
  unfold stageOneAsProbComp bhLiftP
  induction mx using OracleComp.inductionOn with
  | pure a => simp [simulateQ_pure]
  | query_bind n k ih =>
    simp only [simulateQ_query_bind, bhFwdU, simulateQ_bind, QueryImpl.add_apply_inl,
      QueryImpl.ofLift_apply, monadLift_self, bind_assoc]
    exact bind_congr ih

@[simp]
theorem bhStage1ToProb_bhFwdU (n : ℕ) :
    stageOneAsProbComp (bhFwdU (G := SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) n) =
      (query (spec := unifSpec) n : ProbComp (Fin (n + 1))) := by
  unfold stageOneAsProbComp bhFwdU
  simp

@[simp]
theorem bhPrefixRedWith_run1_pure
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (k : ℕ) (default : Bool) (x : Bool) (fuel : ℕ) (σ : BHE2EDrvState S ℓ) :
    (bhPrefixRedWith S ℓ P ki C K qep decT encT k).run1 default (pure x) fuel σ =
      pure (.done x σ) := rfl

@[simp]
theorem bhPrefixRedWith_run1_query_bind_inl
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (k : ℕ) (default : Bool) (n : ℕ)
    (mx : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Range (Sum.inl n) →
      OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (fuel : ℕ) (σ : BHE2EDrvState S ℓ) :
    (bhPrefixRedWith S ℓ P ki C K qep decT encT k).run1 default
      (liftM (OracleSpec.query (spec := unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
        (Sum.inl n)) >>= mx) fuel σ =
    (bhFwdU (G := SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) n >>= fun u =>
      (bhPrefixRedWith S ℓ P ki C K qep decT encT k).run1 default (mx u) fuel σ) := rfl

@[simp]
theorem bhPrefixRedWith_run1_query_bind_inr_zero
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (k : ℕ) (default : Bool) (t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain)
    (mx : (bhTargetGameSpec S ℓ (BitVec 512)).Range t →
      OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (σ : BHE2EDrvState S ℓ) :
    (bhPrefixRedWith S ℓ P ki C K qep decT encT k).run1 default
      (liftM (OracleSpec.query (spec := unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
        (Sum.inr t)) >>= mx) 0 σ =
    pure (.done default σ) := rfl

theorem bhPrefixRedWith_run1_query_bind_inr_succ
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (k : ℕ) (default : Bool) (t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain)
    (mx : (bhTargetGameSpec S ℓ (BitVec 512)).Range t →
      OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (f : ℕ) (σ : BHE2EDrvState S ℓ) :
    (bhPrefixRedWith S ℓ P ki C K qep decT encT k).run1 default
      (liftM (OracleSpec.query (spec := unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
        (Sum.inr t)) >>= mx) (f + 1) σ =
    (bhPrefixHandlePreWith S ℓ P ki C K qep decT encT k σ (bhTargetQenc t) >>= fun step =>
      match step with
      | .inl (r, σ') =>
        (bhPrefixRedWith S ℓ P ki C K qep decT encT k).run1 default
          (mx (bhTargetRdec t r)) f σ'
      | .inr (c, p, σ') =>
        pure (.paused t c p σ' mx)) := by
  conv_lhs => unfold BhShallowTwoStageRed.run1
  rw [construct_query_bind]
  refine bind_congr fun step => ?_
  rcases step with ⟨r, σ'⟩ | ⟨c, p, σ'⟩ <;> rfl

def bhPrefixPlugContWith
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b_k : Bool)
    (o : BHPrefixCtx × Mid (bhTargetGameSpec S ℓ (BitVec 512)) Bool (Option ℕ)
      (BHE2EDrvState S ℓ) BHPrefixCtx) :
    ProbComp (Bool × BHE2EDrvState S ℓ) :=
  match o.2 with
  | .done a σ' => pure (a, σ')
  | .paused t _ p σ_p cont => do
    let k_fresh ← ($ᵗ SampledSessionKey : ProbComp SampledSessionKey)
    let spqr := LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K
    let gs0 := SM.initState
      (sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr o.1.idA o.1.idB) ℓ o.1.spkCoins).sendPart
      k_fresh b_k
    let v := bhTargetRdec t (.inl (.inr p))
    (simulateQ (bhE2EDrvImplGenWith ki P C K qep decT encT (bhMkKeyBitConst false)) (cont v)).run
      (bhPlugExt gs0 σ_p)

def bhPrefixExtPairExpWith
    (S : SignalPqxdh.Setup)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b_k : Bool)
    (o : BHPrefixCtx × Mid (bhTargetGameSpec S ℓ (BitVec 512)) Bool (Option ℕ)
      (BHE2EDrvState S ℓ) BHPrefixCtx) :
    ProbComp (Bool × Bool) := do
  let (b', σ') ← bhPrefixPlugContWith ki P C K qep decT encT b_k o
  let y ← bhComposedPostObs P (b', σ')
  return (match o.2 with | .paused _ _ _ _ _ => true | .done _ _ => false, y)

/-- Scalar experiment at `o` in the plugged world over `ki`. -/
def bhPrefixExtExpWith
    (S : SignalPqxdh.Setup)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b_k : Bool)
    (o : BHPrefixCtx × Mid (bhTargetGameSpec S ℓ (BitVec 512)) Bool (Option ℕ)
      (BHE2EDrvState S ℓ) BHPrefixCtx) :
    ProbComp Bool :=
  Prod.snd <$> bhPrefixExtPairExpWith S ki P C K ℓ qep decT encT b_k o

private theorem bhFinishStartSpkGen_of_not_succ'
    (C : Crypto) (K : LibsignalSpqrV1.MlKem)
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

private theorem bhE2EFinishStartSpk_of_not_succ'
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (b? : Option Bool)
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

set_option maxHeartbeats 1200000 in
theorem simulateQ_bhE2EDrvImplPrefixWith_mkPrefixLazy_eq_run1_bind
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (k : ℕ) (b_k : Bool)
    (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    {qB fuel : ℕ}
    (hQ : oa.IsQueryBoundP (isGameQuery (G := bhTargetGameSpec S ℓ (BitVec 512))) qB)
    (hfuel : qB ≤ fuel)
    (σ : BHE2EDrvState S ℓ) (hAll : BHAllInstsSome σ) (hle : σ.insts.length ≤ k)
    (hpaused : σ.paused = false) :
    (simulateQ (bhE2EDrvImplPrefixWith ki P C K qep decT encT (bhMkPrefixLazy k b_k)) oa).run σ =
      ((fun (a, σ') => (a, { σ' with paused := false })) <$>
        (stageOneAsProbComp ((bhPrefixRedWith S ℓ P ki C K qep decT encT k).run1 false oa fuel σ) >>=
          fun m => bhPrefixPlugContWith ki P C K qep decT encT b_k
            (match m with
             | .done _ _ => bhDefaultPrefixCtx
             | .paused _ c _ _ _ => c, m))) := by
  induction oa using OracleComp.inductionOn generalizing qB fuel σ with
  | pure x =>
    have hσ : { σ with paused := false } = σ := by
      cases σ; simp_all
    simp [bhPrefixPlugContWith, hσ]
  | query_bind q mx ih =>
    rw [isQueryBoundP_query_bind_iff] at hQ
    cases q with
    | inl n =>
      rw [run_simulateQ_query_bind]
      have hRun1 :
          stageOneAsProbComp ((bhPrefixRedWith S ℓ P ki C K qep decT encT k).run1 false
            (liftM (OracleSpec.query (Sum.inl n)) >>= mx) fuel σ) =
          ((query (spec := unifSpec) n : ProbComp (Fin (n + 1))) >>= fun u =>
            stageOneAsProbComp
              ((bhPrefixRedWith S ℓ P ki C K qep decT encT k).run1 false (mx u) fuel σ)) := by
        rw [bhPrefixRedWith_run1_query_bind_inl, bhStage1ToProb_bind,
          bhStage1ToProb_bhFwdU]
      rw [hRun1]
      simp only [bhE2EDrvImplPrefixWith_run_eq_gen, map_eq_bind_pure_comp, Function.comp_def,
        bind_assoc, pure_bind]
      change ((query (spec := unifSpec) n : ProbComp (Fin (n + 1))) >>= fun u =>
          (simulateQ (bhE2EDrvImplPrefixWith ki P C K qep decT encT (bhMkPrefixLazy k b_k))
            (mx u)).run σ) = _
      refine bind_congr fun u => ?_
      simpa only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind] using
        ih u (hQ.2 u) hfuel σ hAll hle hpaused
    | inr t =>
      have hpos : 0 < qB := hQ.1.resolve_left (by simp [isGameQuery])
      obtain ⟨m, rfl⟩ : ∃ m, qB = m + 1 := ⟨qB - 1, by omega⟩
      have hqm : ∀ v, (mx v).IsQueryBoundP
          (isGameQuery (G := bhTargetGameSpec S ℓ (BitVec 512))) m := by
        intro v; simpa [isGameQuery] using hQ.2 v
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hle_f : m ≤ f := by omega
      rw [run_simulateQ_query_bind, bhE2EDrvImplPrefixWith_run_eq_gen]
      rcases t with (kq | ctl) | ⟨i, sq⟩
      ·
        have hRun1 :
            stageOneAsProbComp ((bhPrefixRedWith S ℓ P ki C K qep decT encT k).run1 false
              (liftM (OracleSpec.query (spec := unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
                (Sum.inr (.inl (.inl kq)))) >>= mx) (f + 1) σ) =
            ((bhE2EDrvImplGenWith ki P C K qep decT encT (bhMkKeyBitConst true)
                (.inr (.inl (.inl kq)))).run σ >>= fun ⟨r, σ'⟩ =>
              stageOneAsProbComp
                ((bhPrefixRedWith S ℓ P ki C K qep decT encT k).run1 false (mx r) f σ')) := by
          rw [bhPrefixRedWith_run1_query_bind_inr_succ]
          simp only [bhPrefixHandlePreWith, bhTargetQenc, bhTargetRdec, bhShallowStepPreNonCtl,
            bhStage1ToProb_bind, bhStage1ToProb_bhLiftP, bhStage1ToProb_pure,
            bind_assoc, pure_bind]
          dsimp only [bhE2EDrvImplGenWith]
          simp only [StateT.run_bind, StateT.run_get, pure_bind]
          cases kq <;>
            (dsimp only
             split_ifs <;>
               simp [stateT_run_liftM, StateT.run_bind, StateT.run_set, StateT.run_pure,
                 bind_assoc, pure_bind])
        have hLHS_step :
            (bhE2EDrvImplGenWith ki P C K qep decT encT (bhMkPrefixLazy k b_k σ.insts.length)
              (.inr (.inl (.inl kq)))).run σ =
            (bhE2EDrvImplGenWith ki P C K qep decT encT (bhMkKeyBitConst true)
              (.inr (.inl (.inl kq)))).run σ := rfl
        rw [hLHS_step, hRun1]
        simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
        refine prob_bind_congr_of_support _ _ _ (fun ⟨r, σ'⟩ hp => ?_)
        obtain ⟨hAll', hpaused'⟩ :=
          bhE2EDrvImplGenWith_const_true_step_props ki P C K qep decT encT
            (.inr (.inl (.inl kq))) σ hAll hp
        have hlen' :=
          (bhE2EDrvImplGenWith_step_length ki P C K qep decT encT (bhMkKeyBitConst true)
            (.inr (.inl (.inl kq))) σ hp).1 rfl
        dsimp only at hlen'
        simpa only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind] using
          ih r (hqm r) hle_f σ' hAll' (by omega) (hpaused'.trans hpaused)
      ·
        rcases ctl with ⟨sid⟩
        have hRun1 :
            stageOneAsProbComp ((bhPrefixRedWith S ℓ P ki C K qep decT encT k).run1 false
              (liftM (OracleSpec.query (spec := unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
                (Sum.inr (.inl (.inr (.startDR sid))))) >>= mx) (f + 1) σ) =
            (compositionLocalStart ki C K (some true) σ sid >>= fun ⟨idx?, σ'⟩ =>
              if k < σ'.insts.length then
                let ctx : BHPrefixCtx := match σ'.insts[k]? with
                  | some d => { idA := d.idA, idB := d.idB, spkCoins := d.spkCoins }
                  | none => bhDefaultPrefixCtx
                let insts' := σ'.insts.mapIdx (fun i d => if i = k then { d with gs := none } else d)
                pure (.paused (.inl (.inr (.startDR sid))) ctx idx?
                  { σ' with insts := insts', paused := true } mx)
              else
                stageOneAsProbComp
                  ((bhPrefixRedWith S ℓ P ki C K qep decT encT k).run1 false (mx idx?) f σ')) := by
          rw [bhPrefixRedWith_run1_query_bind_inr_succ]
          simp only [bhPrefixHandlePreWith, bhTargetQenc, bhTargetRdec, bhShallowStepPreCtl,
            bhStage1ToProb_bind, bhStage1ToProb_bhLiftP, bhStage1ToProb_pure,
            bind_assoc, pure_bind]
          refine bind_congr fun p => ?_
          rcases p with ⟨idx?, σ'⟩
          dsimp only
          split_ifs
          · rfl
          · simp
        rw [hRun1]
        by_cases hlt : σ.insts.length < k
        ·
          have hmk : bhMkPrefixLazy k b_k σ.insts.length = bhMkKeyBitConst true := by
            funext kr1 kr2
            have hne : (σ.insts.length == k) = false := beq_eq_false_iff_ne.mpr (by omega)
            have hlt_dec : decide (σ.insts.length < k) = true := decide_eq_true hlt
            unfold bhMkPrefixLazy bhMkKeyBitConst
            simp only [hne, hlt_dec, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
            refine bind_congr fun ac => ?_
            cases kr1 <;> cases kr2 <;> rfl
          have hLHS_step :
              (bhE2EDrvImplGenWith ki P C K qep decT encT (bhMkPrefixLazy k b_k σ.insts.length)
                (.inr (.inl (.inr (.startDR sid))))).run σ =
              compositionLocalStart ki C K (some true) σ sid := by
            rw [hmk]
            dsimp only [bhE2EDrvImplGenWith]
            simp [StateT.run_bind, StateT.run_get, stateT_run_liftM, StateT.run_set,
              StateT.run_pure, bind_assoc, pure_bind, Prod.mk.eta, bind_pure,
              bhE2ELocalStartGenWith_const_eq]
          rw [hLHS_step]
          simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
          refine prob_bind_congr_of_support _ _ _ (fun ⟨idx?, σ'⟩ hp => ?_)
          have hp' : (idx?, σ') ∈ support ((bhE2EDrvImplGenWith ki P C K qep decT encT
              (bhMkKeyBitConst true) (.inr (.inl (.inr (.startDR sid))))).run σ) := by
            dsimp only [bhE2EDrvImplGenWith]
            simpa [StateT.run_bind, StateT.run_get, stateT_run_liftM, StateT.run_set,
              StateT.run_pure, bind_assoc, pure_bind, Prod.mk.eta, bind_pure,
              bhE2ELocalStartGenWith_const_eq] using hp
          obtain ⟨hAll', hpaused'⟩ :=
            bhE2EDrvImplGenWith_const_true_step_props ki P C K qep decT encT
              (.inr (.inl (.inr (.startDR sid)))) σ hAll hp'
          have hlen_le :=
            (bhE2EDrvImplGenWith_step_length ki P C K qep decT encT (bhMkKeyBitConst true)
              (.inr (.inl (.inr (.startDR sid)))) σ hp').2.2
          dsimp only at hlen_le
          have hNotGt : ¬ (k < σ'.insts.length) := by omega
          simp only [hNotGt, ↓reduceIte]
          simpa only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind] using
            ih idx? (hqm idx?) hle_f σ' hAll' (by omega) (hpaused'.trans hpaused)
        ·
          have hlen_eq : σ.insts.length = k := by omega
          subst hlen_eq
          dsimp only [bhE2EDrvImplGenWith]
          simp only [StateT.run_bind, StateT.run_get, stateT_run_liftM, StateT.run_set,
            StateT.run_pure, bind_assoc, pure_bind, Prod.mk.eta, bind_pure]
          unfold bhE2ELocalStartGenWith compositionLocalStart
          cases hG : bhE2EGuard σ sid with
          | none =>
            simp only [pure_bind, lt_irrefl, ↓reduceIte]
            exact ih none (hqm none) hle_f σ hAll le_rfl hpaused
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
              have hIdxTrue :
                  (bhE2EFinishStartSpk C K (some true) { σ with st := st2 } sid
                    (.drKeyResp dk) (.spkSkResp spkSk) ac).1 = some σ.insts.length := by
                unfold bhE2EFinishStartSpk
                simp [bhE2EGuard_with_st, hG, hLen]
              have hFinishTrue :
                  bhE2EFinishStartSpk C K (some true) { σ with st := st2 } sid
                    (.drKeyResp dk) (.spkSkResp spkSk) ac = (some σ.insts.length, σ_true) :=
                Prod.ext hIdxTrue rfl
              have hLenTrue : σ.insts.length < σ_true.insts.length := by
                dsimp only [σ_true, bhE2EFinishStartSpk]
                simp [bhE2EGuard_with_st, hG, hLen]
              have hGetK : σ_true.insts[σ.insts.length]? =
                  some { sid := sid, hdr := hdr,
                         idA := bhIdKeyOf hdr.ikAPk, idB := bhIdKeyOf bnd.ikB,
                         spkCoins := bhBytesWord spkSk,
                         gs := some (SM.initState (sessionSchemeFixedSpk
                           (paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K)
                             (bhIdKeyOf hdr.ikAPk) (bhIdKeyOf bnd.ikB))
                           ℓ (bhBytesWord spkSk)).sendPart (bhKeySOf dk ac) true) } := by
                dsimp only [σ_true, bhE2EFinishStartSpk]
                simp only [bhE2EGuard_with_st, hG, hLen, ↓reduceIte]
                rw [List.getElem?_append_right (le_refl _), Nat.sub_self]
                rfl
              simp only [hFinishTrue, hLenTrue, ↓reduceIte, hGetK, pure_bind]
              unfold bhPrefixPlugContWith
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
                simp [bhE2EGuard_with_st, hG, hLen]
              have hLenLazy : σ.insts.length < σ_lazy.insts.length := by
                dsimp only [σ_lazy, bhFinishStartSpkGen]
                simp [bhE2EGuard_with_st, hG, hLen]
              have hLazyPaused : σ_lazy.paused = false := by
                dsimp only [σ_lazy, bhFinishStartSpkGen]
                rw [bhE2EGuard_with_st, hG]
                simp [hLen, hpaused]
              rw [hIdxLazy,
                simulateQ_bhE2EDrvImplPrefixWith_mkPrefixLazy_of_gt ki P C K qep decT encT
                  σ.insts.length b_k (mx (some σ.insts.length)) σ_lazy hLenLazy,
                bhPlugExt_mapIdx_bhFinishStartSpkGen_eq C K σ hAll st2 sid hG dk spkSk
                  hLen ac k_fresh b_k,
                simulateQ_bhE2EDrvImplGenWith_with_paused ki P C K qep decT encT
                  (bhMkKeyBitConst false) (mx (some σ.insts.length)) σ_lazy true]
              have hPres := simulateQ_bhE2EDrvImplGenWith_preserves_paused ki P C K qep decT encT
                (bhMkKeyBitConst false) (mx (some σ.insts.length)) σ_lazy
              rw [hLazyPaused] at hPres
              simpa only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind] using
                hPres.symm
            · simp only [bhFinishStartSpkGen_of_not_succ' C K { σ with st := st2 } sid kr1 kr2 _ hSucc,
                bhE2EFinishStartSpk_of_not_succ' C K (some true) { σ with st := st2 } sid kr1 kr2 _ hSucc,
                bhMkPrefixLazy_bind_of_not_succ' σ.insts.length b_k kr1 kr2 _ hSucc]
              refine bind_congr fun _ => ?_
              have hlt_false :
                  ¬ (σ.insts.length < ({ σ with st := st2 } : BHE2EDrvState S ℓ).insts.length) :=
                Nat.lt_irrefl _
              simp only [hlt_false, ↓reduceIte]
              simpa only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind] using
                ih none (hqm none) hle_f { σ with st := st2 } hAll le_rfl hpaused
      ·
        have hRun1 :
            stageOneAsProbComp ((bhPrefixRedWith S ℓ P ki C K qep decT encT k).run1 false
              (liftM (OracleSpec.query (spec := unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
                (Sum.inr (.inr ⟨i, sq⟩))) >>= mx) (f + 1) σ) =
            (bhE2EStepLocalSm C K qep decT encT σ i sq >>= fun ⟨sr, σ'⟩ =>
              stageOneAsProbComp ((bhPrefixRedWith S ℓ P ki C K qep decT encT k).run1 false
                (mx (bhUnpackSmResp sq sr)) f σ')) := by
          rw [bhPrefixRedWith_run1_query_bind_inr_succ]
          simp only [bhPrefixHandlePreWith, bhTargetQenc, bhTargetRdec, bhShallowStepPreNonCtl,
            bhStage1ToProb_bind, bhStage1ToProb_bhLiftP, bhStage1ToProb_pure,
            bind_assoc, pure_bind]
        have hLHS_step :
            (bhE2EDrvImplGenWith ki P C K qep decT encT (bhMkPrefixLazy k b_k σ.insts.length)
              (.inr (.inr ⟨i, sq⟩))).run σ =
            (bhE2EStepLocalSm C K qep decT encT σ i sq >>= fun ⟨sr, σ'⟩ =>
              pure (bhUnpackSmResp sq sr, σ')) := by
          dsimp only [bhE2EDrvImplGenWith]
          simp [StateT.run_bind, StateT.run_get, stateT_run_liftM, StateT.run_set,
            StateT.run_pure, bind_assoc, pure_bind]
        rw [hLHS_step, hRun1]
        simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
        refine prob_bind_congr_of_support _ _ _ (fun ⟨sr, σ'⟩ hsm => ?_)
        obtain ⟨hAll', hpaused'⟩ :=
          bhE2EStepLocalSm_preserves_allInstsSome C K qep decT encT σ hAll i sq hsm
        have hp' : (bhUnpackSmResp sq sr, σ') ∈ support
            ((bhE2EDrvImplGenWith ki P C K qep decT encT (bhMkKeyBitConst true)
              (.inr (.inr ⟨i, sq⟩))).run σ) := by
          dsimp only [bhE2EDrvImplGenWith]
          simp only [StateT.run_bind, StateT.run_get, stateT_run_liftM, StateT.run_set,
            StateT.run_pure, bind_assoc, pure_bind, support_bind, support_pure,
            Set.mem_iUnion, Set.mem_singleton_iff]
          exact ⟨(sr, σ'), hsm, rfl⟩
        have hlen' :=
          (bhE2EDrvImplGenWith_step_length ki P C K qep decT encT (bhMkKeyBitConst true)
            (.inr (.inr ⟨i, sq⟩)) σ hp').1 rfl
        dsimp only at hlen'
        simpa only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind] using
          ih (bhUnpackSmResp sq sr) (hqm _) hle_f σ' hAll' (by omega) (hpaused'.trans hpaused)

theorem bhStage1ToProb_eval1_with_eq_run1_bind
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (k qTot : ℕ) (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) :
    stageOneAsProbComp ((bhPrefixRedWith S ℓ P ki C K qep decT encT k).eval1 (fun _ => B) () qTot false) =
      (stageOneAsProbComp ((bhPrefixRedWith S ℓ P ki C K qep decT encT k).run1 false B qTot {}) >>=
        fun m =>
          pure (match m with
            | .done _ _ => bhDefaultPrefixCtx
            | .paused _ c _ _ _ => c, m)) := by
  unfold BhShallowTwoStageRed.eval1
  dsimp only [bhPrefixRedWith, bhDefaultPrefixCtx]
  simp only [bhStage1ToProb_bind, bhStage1ToProb_pure, bind_assoc, pure_bind]
  refine bind_congr fun m => ?_
  cases m <;> rfl

theorem bhPrefixLazyFullExpWith_eq_bind_bhPrefixExtExpWith
    (S : SignalPqxdh.Setup)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (k qTot : ℕ) (b_k : Bool)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hQ : B.IsQueryBoundP (isGameQuery (G := bhTargetGameSpec S ℓ (BitVec 512))) qTot) :
    bhPrefixLazyFullExpWith S ki P C K ℓ qep decT encT k b_k B =
      (stageOneAsProbComp
          ((bhPrefixRedWith S ℓ P ki C K qep decT encT k).eval1 (fun _ => B) () qTot false) >>=
        bhPrefixExtExpWith S ki P C K ℓ qep decT encT b_k) := by
  unfold bhPrefixLazyFullExpWith
  rw [simulateQ_bhE2EDrvImplPrefixWith_mkPrefixLazy_eq_run1_bind ki P C K qep decT encT k b_k B
    hQ le_rfl {} bhAllInstsSome_empty (Nat.zero_le k) rfl,
    bhStage1ToProb_eval1_with_eq_run1_bind]
  simp only [bhPrefixExtExpWith, bhPrefixExtPairExpWith, map_eq_bind_pure_comp, Function.comp_def,
    bind_assoc, pure_bind]
  congr 1; funext m
  cases m <;>
  · congr 1; funext p; rcases p with ⟨_, _⟩
    simp only [bhComposedPostObs_with_paused, bind_pure]

/-! ## Stage-1 support invariants and Stage-2 commutation -/

theorem bhE2ELocalStartWith_preserves_allInstsSome
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (b : Bool)
    (σ : BHE2EDrvState S ℓ) (hAll : BHAllInstsSome σ) (sid : SignalPqxdh.SessionId S)
    {p : Option ℕ × BHE2EDrvState S ℓ}
    (hp : p ∈ support (compositionLocalStart ki C K (some b) σ sid)) :
    BHAllInstsSome p.2 ∧ p.2.paused = σ.paused := by
  unfold compositionLocalStart at hp
  cases hG : bhE2EGuard σ sid with
  | none =>
    rw [hG] at hp; simp only [support_pure, Set.mem_singleton_iff] at hp
    subst hp; exact ⟨hAll, rfl⟩
  | some val =>
    rcases val with ⟨hdr, bnd, ⟨u, j⟩⟩
    rw [hG] at hp; dsimp only at hp
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hp
    rcases hp with ⟨⟨kr1, st1⟩, _, ⟨kr2, st2⟩, _, ac, _, rfl⟩
    unfold bhE2EFinishStartSpk
    simp only [bhE2EGuard_with_st, hG]
    cases kr1 <;> cases kr2 <;> try exact ⟨hAll, rfl⟩
    dsimp only
    split_ifs
    · refine ⟨fun d' hd' => ?_, rfl⟩
      rcases List.mem_append.mp hd' with hd' | hd'
      · exact hAll d' hd'
      · rw [List.mem_singleton.mp hd']; simp
    · exact ⟨hAll, rfl⟩

set_option maxHeartbeats 800000 in
theorem mem_support_bhStage1ToProb_run1_with_props
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (k : ℕ) {oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool} {q f : ℕ}
    (hQ : oa.IsQueryBoundP (isGameQuery (G := bhTargetGameSpec S ℓ (BitVec 512))) q)
    (σ : BHE2EDrvState S ℓ) (hAll : BHAllInstsSome σ) (hpaused : σ.paused = false)
    {m}
    (hm : m ∈ support
      (stageOneAsProbComp ((bhPrefixRedWith S ℓ P ki C K qep decT encT k).run1 false oa f σ))) :
    BHMidStage1Props k q m := by
  induction oa using OracleComp.inductionOn generalizing q f σ m with
  | pure a =>
    rw [bhPrefixRedWith_run1_pure, bhStage1ToProb_pure, support_pure, Set.mem_singleton_iff] at hm
    subst hm
    exact hpaused
  | query_bind q_step mx ih =>
    rw [isQueryBoundP_query_bind_iff] at hQ
    rcases q_step with n | ((kq | ⟨⟨sid⟩⟩) | ⟨i, sq⟩)
    · rw [bhPrefixRedWith_run1_query_bind_inl, bhStage1ToProb_bind,
        bhStage1ToProb_bhFwdU] at hm
      simp only [support_bind, Set.mem_iUnion, exists_prop] at hm
      rcases hm with ⟨u, _, hm⟩
      exact ih u (hQ.2 u) σ hAll hpaused hm
    · have hqm : ∀ v, (mx v).IsQueryBoundP
          (isGameQuery (G := bhTargetGameSpec S ℓ (BitVec 512))) q := by
        intro v
        exact (hQ.2 v).mono (by simp [isGameQuery])
      cases f with
      | zero =>
        rw [bhPrefixRedWith_run1_query_bind_inr_zero, bhStage1ToProb_pure,
          support_pure, Set.mem_singleton_iff] at hm
        subst hm
        exact hpaused
      | succ f' =>
        rw [bhPrefixRedWith_run1_query_bind_inr_succ] at hm
        simp only [bhPrefixHandlePreWith, bhTargetQenc, bhTargetRdec, bhShallowStepPreNonCtl,
          bhStage1ToProb_bind, bhStage1ToProb_bhLiftP, bhStage1ToProb_pure,
          bind_assoc, pure_bind] at hm
        have hstep : ∃ r σ', BHAllInstsSome σ' ∧ σ'.paused = false ∧
            m ∈ support (stageOneAsProbComp
              ((bhPrefixRedWith S ℓ P ki C K qep decT encT k).run1 false (mx r) f' σ')) := by
          have hMir : ∀ kq' st' kr,
              BHAllInstsSome (bhE2EMirror { σ with st := st' } kq' kr) ∧
                (bhE2EMirror { σ with st := st' } kq' kr).paused = false := fun kq' st' kr => by
            refine ⟨?_, ?_⟩
            · have hi : (bhE2EMirror { σ with st := st' } kq' kr).insts = σ.insts := by
                cases kq' <;> cases kr <;> rfl
              intro d hd; rw [hi] at hd; exact hAll d hd
            · have hp : (bhE2EMirror { σ with st := st' } kq' kr).paused = σ.paused := by
                cases kq' <;> cases kr <;> rfl
              exact hp.trans hpaused
          cases kq <;>
            (dsimp only at hm
             split_ifs at hm <;>
               (simp only [bind_assoc, pure_bind, bhStage1ToProb_bind, bhStage1ToProb_pure,
                  support_bind, Set.mem_iUnion, exists_prop] at hm
                first
                | exact ⟨.noneResp, σ, hAll, hpaused, hm⟩
                | (rcases hm with ⟨⟨kr, st'⟩, _, hm⟩
                   exact ⟨kr, _, (hMir _ st' kr).1, (hMir _ st' kr).2, hm⟩)))
        rcases hstep with ⟨r, σ', hAll', hpaused', hm'⟩
        exact ih r (hqm r) σ' hAll' hpaused' hm'
    · have hqm : ∀ v, (mx v).IsQueryBoundP
          (isGameQuery (G := bhTargetGameSpec S ℓ (BitVec 512))) q := by
        intro v
        exact (hQ.2 v).mono (by simp [isGameQuery])
      cases f with
      | zero =>
        rw [bhPrefixRedWith_run1_query_bind_inr_zero, bhStage1ToProb_pure,
          support_pure, Set.mem_singleton_iff] at hm
        subst hm
        exact hpaused
      | succ f' =>
        rw [bhPrefixRedWith_run1_query_bind_inr_succ] at hm
        simp only [bhPrefixHandlePreWith, bhTargetQenc, bhTargetRdec, bhShallowStepPreCtl,
          bhStage1ToProb_bind, bhStage1ToProb_bhLiftP,
          bhStage1ToProb_pure, bind_assoc, pure_bind] at hm
        rw [support_bind, Set.mem_iUnion] at hm
        rcases hm with ⟨⟨idx?, σ'⟩, hm⟩
        rw [Set.mem_iUnion] at hm
        rcases hm with ⟨hstart, hm⟩
        dsimp only at hm
        obtain ⟨hAll', hpaused'⟩ :=
          bhE2ELocalStartWith_preserves_allInstsSome ki C K true σ hAll sid hstart
        by_cases hlt : k < σ'.insts.length
        · simp only [hlt, ↓reduceIte, pure_bind, bhStage1ToProb_pure, support_pure,
            Set.mem_singleton_iff] at hm
          subst hm
          exact ⟨bhPrefixPlugInv_init k σ' hAll' hlt, hqm⟩
        · simp only [hlt, Bool.false_eq_true, ↓reduceIte, pure_bind,
            bhStage1ToProb_bind, bhStage1ToProb_pure] at hm
          exact ih idx? (hqm _) σ' hAll' (hpaused'.trans hpaused) hm
    · have hqm : ∀ v, (mx v).IsQueryBoundP
          (isGameQuery (G := bhTargetGameSpec S ℓ (BitVec 512))) q := by
        intro v
        exact (hQ.2 v).mono (by simp [isGameQuery])
      cases f with
      | zero =>
        rw [bhPrefixRedWith_run1_query_bind_inr_zero, bhStage1ToProb_pure,
          support_pure, Set.mem_singleton_iff] at hm
        subst hm
        exact hpaused
      | succ f' =>
        rw [bhPrefixRedWith_run1_query_bind_inr_succ] at hm
        simp only [bhPrefixHandlePreWith, bhTargetQenc, bhTargetRdec, bhShallowStepPreNonCtl,
          bhStage1ToProb_bind, bhStage1ToProb_bhLiftP, bhStage1ToProb_pure,
          bind_assoc, pure_bind, support_bind, Set.mem_iUnion, exists_prop] at hm
        rcases hm with ⟨⟨sr, σ'⟩, hsm, hm⟩
        obtain ⟨hAll', hpaused'⟩ :=
          bhE2EStepLocalSm_preserves_allInstsSome C K qep decT encT σ hAll i sq hsm
        exact ih (bhUnpackSmResp sq sr) (hqm _) σ' hAll' (hpaused'.trans hpaused) hm

theorem mem_support_bhStage1ToProb_eval1_with_props
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (k qTot : ℕ) (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hQ : B.IsQueryBoundP (isGameQuery (G := bhTargetGameSpec S ℓ (BitVec 512))) qTot)
    {o}
    (ho : o ∈ support (stageOneAsProbComp ((bhPrefixRedWith S ℓ P ki C K qep decT encT k).eval1
      (fun _ => B) () qTot false))) :
    BHMidEval1Props k qTot o := by
  rw [bhStage1ToProb_eval1_with_eq_run1_bind] at ho
  simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at ho
  rcases ho with ⟨m, hm, rfl⟩
  have hprops := mem_support_bhStage1ToProb_run1_with_props P ki C K qep decT encT k hQ {}
    bhAllInstsSome_empty rfl hm
  cases m with
  | done b' σ' => exact hprops
  | paused t c p σ_p cont =>
    exact ⟨rfl, hprops.1, hprops.2⟩

@[simp]
theorem simulateQ_implExt_bhFwdU_run
    (C : Crypto) (spqr : Spqr Bytes (BitVec 512)) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (idA idB : IdentityKey) (s : BitVec 256)
    (n : ℕ) (gs_ext : ExtState ℓ) :
    (simulateQ (implExt C spqr ℓ qep decT encT idA idB s)
      (bhFwdU (G := SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) n)).run gs_ext =
    ((query (spec := unifSpec) n : ProbComp (Fin (n + 1))) >>= fun u => pure (u, gs_ext)) :=
  simulateQ_implExt_query_inl_run C spqr qep decT encT idA idB s n gs_ext

@[simp]
theorem simulateQ_implExt_bhLiftP_run {α : Type}
    (C : Crypto) (spqr : Spqr Bytes (BitVec 512)) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (idA idB : IdentityKey) (s : BitVec 256)
    (mx : ProbComp α) (gs_ext : ExtState ℓ) :
    (simulateQ (implExt C spqr ℓ qep decT encT idA idB s)
      (bhLiftP (G := SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) mx)).run gs_ext =
    (mx >>= fun x => pure (x, gs_ext)) := by
  unfold bhLiftP
  induction mx using OracleComp.inductionOn generalizing gs_ext with
  | pure a => rfl
  | query_bind n k ih =>
    rw [simulateQ_query_bind, simulateQ_bind, StateT.run_bind]
    have hq :
        (simulateQ (implExt C spqr ℓ qep decT encT idA idB s)
          (bhFwdU (G := SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) n)).run gs_ext =
        ((liftM (OracleSpec.query n) : ProbComp (Fin (n + 1))) >>= fun u => pure (u, gs_ext)) :=
      simulateQ_implExt_query_inl_run C spqr qep decT encT idA idB s n gs_ext
    dsimp only [OracleSpec.query_def, liftM, monadLift] at hq ⊢
    change (do
      let p ← (simulateQ (implExt C spqr ℓ qep decT encT idA idB s)
        (bhFwdU (G := SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) n)).run gs_ext
      (simulateQ (implExt C spqr ℓ qep decT encT idA idB s)
        (simulateQ (bhFwdU (G := SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes))
          (k p.1))).run p.2) = _
    rw [hq]
    simp only [bind_assoc, pure_bind]
    exact bind_congr fun u => ih u gs_ext

theorem bhE2ELocalStartWith_false_bhPlugExt
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (σ : BHE2EDrvState S ℓ) (gs_ext : ExtState ℓ) (sid : SignalPqxdh.SessionId S) :
    compositionLocalStart ki C K (some false) (bhPlugExt gs_ext σ) sid =
      (fun (idx?, σ1) => (idx?, bhPlugExt gs_ext σ1)) <$>
        compositionLocalStart ki C K (some false) σ sid ∧
    ∀ p ∈ support (compositionLocalStart ki C K (some false) σ sid),
      ∀ {k idA idB s}, BHPrefixPlugInv k idA idB s σ → BHPrefixPlugInv k idA idB s p.2 := by
  unfold compositionLocalStart
  rw [bhE2EGuard_bhPlugExt]
  cases hG : bhE2EGuard σ sid with
  | none =>
    simp only [map_pure, support_pure, Set.mem_singleton_iff, true_and]
    rintro p rfl _ _ _ _ h
    exact h
  | some val =>
    rcases val with ⟨hdr, bnd, ⟨u, j⟩⟩
    have hst : (bhPlugExt gs_ext σ).st = σ.st := rfl
    rw [hst]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    have hFin : ∀ st2 kr1 kr2 ac,
        bhE2EFinishStartSpk C K (some false) { bhPlugExt gs_ext σ with st := st2 } sid kr1 kr2 ac =
          (let (idx?, σ1) := bhE2EFinishStartSpk C K (some false) { σ with st := st2 } sid kr1 kr2 ac
           (idx?, bhPlugExt gs_ext σ1)) ∧
        ∀ {k idA idB s}, BHPrefixPlugInv k idA idB s σ →
          BHPrefixPlugInv k idA idB s
            (bhE2EFinishStartSpk C K (some false) { σ with st := st2 } sid kr1 kr2 ac).2 := by
      intro st2 kr1 kr2 ac
      unfold bhE2EFinishStartSpk
      have hPlugSt : { bhPlugExt gs_ext σ with st := st2 } = bhPlugExt gs_ext { σ with st := st2 } := by
        cases σ; rfl
      rw [hPlugSt, bhE2EGuard_bhPlugExt, bhE2EGuard_with_st, hG]
      cases kr1 <;> cases kr2 <;> try exact ⟨rfl, fun h => bhPrefixPlugInv_with_st h st2⟩
      dsimp only
      split_ifs with hLen
      · refine ⟨?_, fun h => bhPrefixPlugInv_append_some h _ _ st2 (by simp)⟩
        simp [bhPlugExt, bhPlugExtInst]
      · exact ⟨rfl, fun h => bhPrefixPlugInv_with_st h st2⟩
    refine ⟨?_, ?_⟩
    · refine bind_congr fun ⟨kr1, st1⟩ => bind_congr fun ⟨kr2, st2⟩ => bind_congr fun ac => ?_
      rw [(hFin st2 kr1 kr2 ac).1]
    · intro p hp k idA idB s hInv
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at hp
      rcases hp with ⟨⟨kr1, st1⟩, _, ⟨kr2, st2⟩, _, ac, _, rfl⟩
      exact (hFin st2 kr1 kr2 ac).2 hInv

set_option maxHeartbeats 1200000 in
private theorem bhPrefixHandlePostWith_plugExt_sm_bind_eq {α : Type}
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (k : ℕ) (idA idB : IdentityKey) (s : BitVec 256)
    (i : ℕ) (sq : (SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (σ : BHE2EDrvState S ℓ) (gs_ext : ExtState ℓ)
    (h : BHPrefixPlugInv k idA idB s σ)
    (k1 : ((unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Range (.inr (.inr ⟨i, sq⟩)) ×
        BHE2EDrvState S ℓ) × ExtState ℓ → ProbComp α)
    (k2 : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Range (.inr (.inr ⟨i, sq⟩)) ×
        BHE2EDrvState S ℓ → ProbComp α)
    (hk : ∀ r σ' gs_ext', BHPrefixPlugInv k idA idB s σ' → gs_ext'.b = gs_ext.b →
      k1 ((r, σ'), gs_ext') = k2 (r, bhPlugExt gs_ext' σ')) :
    ((simulateQ (implExt C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) ℓ qep decT encT idA idB s)
        ((bhShallowImplOfHandle bhTargetQenc bhTargetRdec
          (bhPrefixHandlePostWith S ℓ P ki C K qep decT encT k)
          (.inr (.inr ⟨i, sq⟩))).run σ)).run gs_ext >>= k1) =
    ((bhE2EDrvImplGenWith ki P C K qep decT encT (bhMkKeyBitConst false)
        (.inr (.inr ⟨i, sq⟩))).run (bhPlugExt gs_ext σ) >>= k2) := by
  have hL :
      (simulateQ (implExt C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) ℓ qep decT encT idA idB s)
        ((bhShallowImplOfHandle bhTargetQenc bhTargetRdec
          (bhPrefixHandlePostWith S ℓ P ki C K qep decT encT k)
          (.inr (.inr ⟨i, sq⟩))).run σ)).run gs_ext =
      match bhShallowCheckExtSm k σ i sq with
      | .inl _ =>
        (bhE2EStepLocalSm C K qep decT encT σ i sq >>= fun (sr, σ') =>
          pure ((bhUnpackSmResp sq sr, σ'), gs_ext))
      | .inr sq' =>
        ((SM.oracleImplR (sessionSchemeFixedSpk
            (paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) idA idB) ℓ s)
            (2 + 1) qep (configRefuseEarlyBobCorr decT encT) sq').run gs_ext >>= fun (r, gs_ext') =>
          let p := bhShallowCommitExtSm k σ sq' (bhPackSmResp sq' r)
          pure ((bhUnpackSmResp sq (bhPackSmResp sq' r), p.2), gs_ext')) := by
    change
      (simulateQ (implExt C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) ℓ qep decT encT idA idB s)
        (bhPrefixHandlePostWith S ℓ P ki C K qep decT encT k σ (bhTargetQenc (.inr ⟨i, sq⟩)) >>=
          fun p => pure (bhTargetRdec (.inr ⟨i, sq⟩) p.1, p.2))).run gs_ext = _
    dsimp only [bhPrefixHandlePostWith, bhTargetQenc]
    cases bhShallowCheckExtSm k σ i sq
    · simp only [bhShallowStepPostLocal, bhTargetRdec,
        simulateQ_bind, StateT.run_bind, simulateQ_implExt_bhLiftP_run,
        simulateQ_pure, StateT.run_pure, bind_assoc, pure_bind]
    · simp only [bhTargetRdec, simulateQ_bind, StateT.run_bind,
        simulateQ_pure, StateT.run_pure, bind_assoc, pure_bind]
      erw [simulateQ_implExt_query_inr_run]
      rfl
  have hR :
      (bhE2EDrvImplGenWith ki P C K qep decT encT (bhMkKeyBitConst false)
        (.inr (.inr ⟨i, sq⟩))).run (bhPlugExt gs_ext σ) =
      (bhE2EStepLocalSm C K qep decT encT (bhPlugExt gs_ext σ) i sq >>= fun (sr, σ') =>
        pure (bhUnpackSmResp sq sr, σ')) := by
    dsimp only [bhE2EDrvImplGenWith]
    simp only [StateT.run_bind, StateT.run_get, stateT_run_liftM, StateT.run_set, StateT.run_pure,
      bind_assoc, pure_bind]
  rw [hL, hR, checkExtSm_eval_eq_filter]
  by_cases hClean : (!bhE2EDrvInstClean σ i) = true
  · have hOr : (i != k || !bhE2EDrvInstClean σ k) = true := by
      rcases Decidable.em (i = k) with rfl | hik
      · simp [hClean]
      · simp [hik]
    rw [hOr]
    simp only [↓reduceIte, bhE2EStepLocalSm_eq_filter, bhE2EDrvInstClean_bhPlugExt,
      hClean, pure_bind]
    exact hk (bhUnpackSmResp sq (none, none, none)) σ gs_ext h rfl
  · by_cases hik : i = k
    · subst hik
      have hOr : (i != i || !bhE2EDrvInstClean σ i) = false := by simp [hClean]
      rw [hOr]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rcases h.inst_k_none with ⟨d, hi_d, hd_none⟩
      rw [hi_d]
      cases him : σ.instMeta[i]? with
      | none =>
        have him_plug : (bhPlugExt gs_ext σ).instMeta[i]? = none := him
        simp only [bhE2EStepLocalSm_eq_filter, bhE2EDrvInstClean_bhPlugExt, hClean,
          Bool.false_eq_true, ↓reduceIte, getElem?_insts_bhPlugExt, hi_d, Option.map_some,
          him, him_plug, pure_bind]
        exact hk (bhUnpackSmResp sq (none, none, none)) σ gs_ext h rfl
      | some im =>
        have him_plug : (bhPlugExt gs_ext σ).instMeta[i]? = some im := him
        by_cases hCorr : (!im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d) = true
        · simp only [hCorr, ↓reduceIte, bhE2EStepLocalSm_eq_filter,
            bhE2EDrvInstClean_bhPlugExt, hClean, Bool.false_eq_true, getElem?_insts_bhPlugExt,
            hi_d, Option.map_some, him, him_plug, bhE2EInstIkACorr_bhPlugExt,
            bhE2EInstIkACorr_bhPlugExtInst, pure_bind]
          have hPlugMeta :
              { bhPlugExt gs_ext σ with
                instMeta := (bhPlugExt gs_ext σ).instMeta.set i
                  { im with bobAccepted := true, ikACorrAtAccept := true } } =
              bhPlugExt gs_ext
                { σ with
                  instMeta := σ.instMeta.set i
                    { im with bobAccepted := true, ikACorrAtAccept := true } } :=
            rfl
          rw [hPlugMeta]
          exact hk (bhUnpackSmResp sq (none, none, none)) _ gs_ext
            (bhPrefixPlugInv_set_instMeta h i _) rfl
        · simp only [hCorr, Bool.false_eq_true, ↓reduceIte]
          cases hfilt : bhFilterSmQuery d im sq with
          | none =>
            simp only [bhE2EStepLocalSm_eq_filter, bhE2EDrvInstClean_bhPlugExt, hClean,
              Bool.false_eq_true, ↓reduceIte, getElem?_insts_bhPlugExt, hi_d, Option.map_some,
              him, him_plug, bhE2EInstIkACorr_bhPlugExt, bhE2EInstIkACorr_bhPlugExtInst,
              bhE2EInstIkACorr_with_gs, hCorr, hd_none, bhPlugExtInst_of_none gs_ext d hd_none,
              bhFilterSmQuery_with_gs, hfilt, pure_bind]
            exact hk (bhUnpackSmResp sq (none, none, none)) σ gs_ext h rfl
          | some sq' =>
            rcases h.params_none d (List.mem_of_getElem? hi_d) hd_none with ⟨hidA, hidB, hspk⟩
            have hRecvEq : bhIsBobRecvSMQuery sq' = bhIsBobRecvSMQuery sq :=
              bhIsBobRecvSMQuery_of_bhFilterSmQuery hfilt
            have hCorr' : (!im.bobAccepted && bhIsBobRecvSMQuery sq' && bhE2EInstIkACorr σ d) = false := by
              rw [hRecvEq]; exact Bool.eq_false_iff.mpr hCorr
            simp only [bhE2EStepLocalSm_eq_filter, bhE2EDrvInstClean_bhPlugExt, hClean,
              Bool.false_eq_true, ↓reduceIte, getElem?_insts_bhPlugExt, hi_d, Option.map_some,
              him_plug, bhE2EInstIkACorr_bhPlugExt, bhE2EInstIkACorr_bhPlugExtInst,
              bhE2EInstIkACorr_with_gs, hCorr, hd_none, bhPlugExtInst_of_none gs_ext d hd_none,
              bhFilterSmQuery_with_gs, hfilt, bind_assoc, pure_bind]
            have hSchEq :
                sessionSchemeFixedSpk
                  (paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) d.idA d.idB) ℓ d.spkCoins =
                sessionSchemeFixedSpk
                  (paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) idA idB) ℓ s := by
              rw [hidA, hidB, hspk]
            rw [hSchEq]
            refine prob_bind_congr_of_support _ _ _ (fun p hsm => ?_)
            rcases p with ⟨r, gs_ext'⟩
            have hb' : gs_ext'.b = gs_ext.b := oracleImplR_preserves_b _ _ _ _ sq' gs_ext hsm
            dsimp only [bhShallowCommitExtSm, bhTargetRdec]
            simp only [hClean, Bool.false_eq_true, ↓reduceIte, hi_d, him, hCorr',
              bhUnpackSmResp_bhPackSmResp, pure_bind]
            let im' := if !im.bobAccepted && bhIsBobAcceptSMResp sq' r then
                { im with bobAccepted := true, ikACorrAtAccept := bhE2EInstIkACorr σ d }
              else im
            erw [bhPlugExt_set_none_of_onlyInstKNone h.only_k gs_ext gs_ext' hi_d hd_none im']
            exact hk (bhUnpackSmResp sq (bhPackSmResp sq' r))
              { σ with instMeta := σ.instMeta.set i im' } gs_ext'
              (bhPrefixPlugInv_set_instMeta h i im') hb'
    · have hne : (i != k) = true := bne_iff_ne.mpr hik
      have hOr : (i != k || !bhE2EDrvInstClean σ k) = true := by simp [hne]
      rw [hOr]
      simp only [↓reduceIte, bhE2EStepLocalSm_eq_filter, bhE2EDrvInstClean_bhPlugExt,
        hClean, Bool.false_eq_true, getElem?_insts_bhPlugExt]
      cases hi : σ.insts[i]? with
      | none =>
        simp only [Option.map_none, pure_bind]
        exact hk (bhUnpackSmResp sq (none, none, none)) σ gs_ext h rfl
      | some d =>
        have hd_some : d.gs ≠ none := fun hnone => hik (h.only_k i d hi hnone)
        cases hd : d.gs with
        | none => exact False.elim (hd_some hd)
        | some gs =>
          have him_eq : (bhPlugExt gs_ext σ).instMeta[i]? = σ.instMeta[i]? := rfl
          simp only [Option.map_some, bhPlugExtInst_of_some gs_ext d gs hd, him_eq]
          cases him : σ.instMeta[i]? with
          | none =>
            simp only [pure_bind]
            exact hk (bhUnpackSmResp sq (none, none, none)) σ gs_ext h rfl
          | some im =>
            simp only [bhE2EInstIkACorr_bhPlugExt, bhE2EInstIkACorr_with_gs]
            by_cases hCorr : (!im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d) = true
            · simp only [hCorr, ↓reduceIte, pure_bind]
              exact hk (bhUnpackSmResp sq (none, none, none)) _ gs_ext
                (bhPrefixPlugInv_set_instMeta h i _) rfl
            · simp only [hCorr, Bool.false_eq_true, ↓reduceIte, hd, bhFilterSmQuery_with_gs]
              cases hfilt : bhFilterSmQuery d im sq with
              | none =>
                simp only [pure_bind]
                exact hk (bhUnpackSmResp sq (none, none, none)) σ gs_ext h rfl
              | some sq' =>
                simp only [bind_assoc, pure_bind]
                refine bind_congr fun p => ?_
                rcases p with ⟨r, gs'⟩
                let im' := if !im.bobAccepted && bhIsBobAcceptSMResp sq' r then
                    { im with bobAccepted := true, ikACorrAtAccept := bhE2EInstIkACorr σ d }
                  else im
                have hSetPlug :
                    { bhPlugExt gs_ext σ with
                      insts := (bhPlugExt gs_ext σ).insts.set i { d with gs := some gs' },
                      instMeta := (bhPlugExt gs_ext σ).instMeta.set i im' } =
                    bhPlugExt gs_ext
                      { σ with
                        insts := σ.insts.set i { d with gs := some gs' },
                        instMeta := σ.instMeta.set i im' } := by
                  cases σ
                  simp [bhPlugExt, List.map_set, bhPlugExtInst]
                rw [hSetPlug]
                exact hk (bhUnpackSmResp sq (bhPackSmResp sq' r)) _ gs_ext
                  (bhPrefixPlugInv_set_some h i _ im' (by simp)
                    (fun d' hd' => by rw [hi] at hd'; injection hd' with hEq; rw [← hEq, hd]; simp))
                  rfl

set_option maxHeartbeats 800000 in
theorem bhPrefixHandlePostWith_plugExt_step_bind_eq {α : Type}
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (k : ℕ) (idA idB : IdentityKey) (s : BitVec 256)
    (q : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain)
    (σ : BHE2EDrvState S ℓ) (gs_ext : ExtState ℓ)
    (h : BHPrefixPlugInv k idA idB s σ)
    (k1 : ((unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Range q × BHE2EDrvState S ℓ) ×
      ExtState ℓ → ProbComp α)
    (k2 : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Range q × BHE2EDrvState S ℓ →
      ProbComp α)
    (hk : ∀ r σ' gs_ext', BHPrefixPlugInv k idA idB s σ' → gs_ext'.b = gs_ext.b →
      k1 ((r, σ'), gs_ext') = k2 (r, bhPlugExt gs_ext' σ')) :
    ((simulateQ (implExt C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) ℓ qep decT encT idA idB s)
        ((bhShallowImplOfHandle bhTargetQenc bhTargetRdec
          (bhPrefixHandlePostWith S ℓ P ki C K qep decT encT k) q).run σ)).run gs_ext >>=
          k1) =
    ((bhE2EDrvImplGenWith ki P C K qep decT encT (bhMkKeyBitConst false) q).run
        (bhPlugExt gs_ext σ) >>=
      k2) := by
  rcases q with n | ((kq | ⟨⟨sid⟩⟩) | ⟨i, sq⟩)
  · change ((simulateQ (implExt C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) ℓ qep decT encT idA idB s)
        (bhFwdU (G := SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) n >>=
          fun u => pure (u, σ))).run gs_ext >>= k1) =
      (((query (spec := unifSpec) n : ProbComp (Fin (n + 1))) >>=
        fun u => pure (u, bhPlugExt gs_ext σ)) >>= k2)
    rw [simulateQ_bind, StateT.run_bind, simulateQ_implExt_bhFwdU_run]
    simp only [simulateQ_pure, StateT.run_pure, bind_assoc, pure_bind]
    exact bind_congr fun u => hk u σ gs_ext h rfl
  · let isRef (kq' : SignalPqxdh.KeyIndQuery S) : Bool :=
      match kq' with | .corruptIK u => bhNoOpkRespPromoted σ.instMeta u | _ => false
    have hL :
        (simulateQ (implExt C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) ℓ qep decT encT idA idB s)
          ((bhShallowImplOfHandle bhTargetQenc bhTargetRdec
            (bhPrefixHandlePostWith S ℓ P ki C K qep decT encT k)
            (.inr (.inl (.inl kq)))).run σ)).run gs_ext =
        (if !bhDrvKiQueryOk P σ.toModelDriverBase kq then
          pure ((.noneResp, σ), gs_ext)
        else if isRef kq then
          pure ((.noneResp, σ), gs_ext)
        else
          (ki kq).run σ.st >>= fun (kr, st') =>
            pure ((kr, bhE2EMirror { σ with st := st' } kq kr), gs_ext)) := by
      simp only [bhShallowImplOfHandle, bhPrefixHandlePostWith, bhTargetQenc, bhTargetRdec,
        bhShallowStepPostLocal, StateT.run_mk, simulateQ_bind, StateT.run_bind,
        simulateQ_implExt_bhLiftP_run, simulateQ_pure, StateT.run_pure, bind_assoc, pure_bind, isRef]
      cases kq <;> (dsimp only; split_ifs <;> simp only [bhTargetRdec, bind_assoc, pure_bind])
    have hR :
        (bhE2EDrvImplGenWith ki P C K qep decT encT (bhMkKeyBitConst false)
          (.inr (.inl (.inl kq)))).run (bhPlugExt gs_ext σ) =
        (if !bhDrvKiQueryOk P σ.toModelDriverBase kq then
          pure (.noneResp, bhPlugExt gs_ext σ)
        else if isRef kq then
          pure (.noneResp, bhPlugExt gs_ext σ)
        else
          (ki kq).run σ.st >>= fun (kr, st') =>
            pure (kr, bhPlugExt gs_ext (bhE2EMirror { σ with st := st' } kq kr))) := by
      dsimp only [bhE2EDrvImplGenWith, isRef]
      rw [StateT.run_bind, StateT.run_get, pure_bind]
      have hBase : (bhPlugExt gs_ext σ).toModelDriverBase = σ.toModelDriverBase := rfl
      have hMeta : (bhPlugExt gs_ext σ).instMeta = σ.instMeta := rfl
      have hSt : (bhPlugExt gs_ext σ).st = σ.st := rfl
      cases kq <;>
        (dsimp only
         try rw [hBase]
         try rw [hMeta]
         split_ifs <;> first
           | rfl
           | (try rw [hSt]
              simp only [stateT_run_liftM, StateT.run_bind, StateT.run_set, StateT.run_pure,
                bind_assoc, pure_bind]
              refine bind_congr fun ⟨kr, st'⟩ => ?_
              exact congrArg (fun x => pure (kr, x))
                (bhE2EMirror_bhPlugExt gs_ext { σ with st := st' } _ kr)))
    rw [hL, hR]
    split_ifs
    · simp only [pure_bind]
      exact hk .noneResp σ gs_ext h rfl
    · simp only [pure_bind]
      exact hk .noneResp σ gs_ext h rfl
    · simp only [bind_assoc, pure_bind]
      exact bind_congr fun ⟨kr, st'⟩ =>
        hk kr (bhE2EMirror { σ with st := st' } kq kr) gs_ext
          (bhPrefixPlugInv_bhE2EMirror h st' kq kr) rfl
  · have hL :
        (simulateQ (implExt C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) ℓ qep decT encT idA idB s)
          ((bhShallowImplOfHandle bhTargetQenc bhTargetRdec
            (bhPrefixHandlePostWith S ℓ P ki C K qep decT encT k)
            (.inr (.inl (.inr ⟨sid⟩)))).run σ)).run gs_ext =
        (compositionLocalStart ki C K (some false) σ sid >>= fun (idx?, σ1) =>
          pure ((idx?, σ1), gs_ext)) := by
      simp only [bhShallowImplOfHandle, bhPrefixHandlePostWith, bhTargetQenc, bhTargetRdec,
        bhShallowStepPostLocal, StateT.run_mk, simulateQ_bind, StateT.run_bind,
        simulateQ_implExt_bhLiftP_run, simulateQ_pure, StateT.run_pure, bind_assoc, pure_bind]
    have hR :
        (bhE2EDrvImplGenWith ki P C K qep decT encT (bhMkKeyBitConst false)
          (.inr (.inl (.inr ⟨sid⟩)))).run (bhPlugExt gs_ext σ) =
        compositionLocalStart ki C K (some false) (bhPlugExt gs_ext σ) sid := by
      dsimp only [bhE2EDrvImplGenWith]
      simp only [StateT.run_bind, StateT.run_get, stateT_run_liftM, StateT.run_set, StateT.run_pure,
        bind_assoc, pure_bind, Prod.mk.eta, bind_pure, bhE2ELocalStartGenWith_const_eq]
    obtain ⟨hStartEq, hStartInv⟩ := bhE2ELocalStartWith_false_bhPlugExt ki C K σ gs_ext sid
    rw [hL, hR, hStartEq]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    refine prob_bind_congr_of_support _ _ _ (fun ⟨idx?, σ1⟩ hp => ?_)
    exact hk idx? σ1 gs_ext (hStartInv (idx?, σ1) hp h) rfl
  · exact bhPrefixHandlePostWith_plugExt_sm_bind_eq ki P C K qep decT encT k idA idB s i sq
      σ gs_ext h k1 k2 hk

theorem bhShallowRunFuel_eq_simulateQ_with
    {κ ι Q R St : Type} {G : OracleSpec κ} {T : OracleSpec ι}
    (qenc : G.Domain → Q) (rdec : (t : G.Domain) → R → G.Range t)
    (h : St → Q → OracleComp (unifSpec + T) (R × St))
    {α : Type} (dflt : α) :
    ∀ {oa : OracleComp (unifSpec + G) α} {q : ℕ},
      oa.IsQueryBoundP (isGameQuery (G := G)) q →
      ∀ {fuel : ℕ}, q ≤ fuel → ∀ (s : St),
        bhShallowRunFuel qenc rdec h dflt oa fuel s =
          (simulateQ (bhShallowImplOfHandle qenc rdec h) oa).run s := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro q _ fuel _ s
    simp [bhShallowRunFuel, simulateQ_pure]
  | query_bind q mx ih =>
    intro qB hq fuel hfuel s
    rw [isQueryBoundP_query_bind_iff] at hq
    cases q with
    | inl n =>
      rw [run_simulateQ_query_bind]
      simp only [bhShallowRunFuel_query_inl, bhShallowImplOfHandle, StateT.run_mk, bind_assoc, pure_bind]
      refine bind_congr fun u => ih u (hq.2 u) hfuel s
    | inr t =>
      have hpos : 0 < qB := hq.1.resolve_left (by simp [isGameQuery])
      obtain ⟨m, rfl⟩ : ∃ m, qB = m + 1 := ⟨qB - 1, by omega⟩
      have hqm : ∀ u, (mx u).IsQueryBoundP (isGameQuery (G := G)) m := by
        intro u; simpa [isGameQuery] using hq.2 u
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hle : m ≤ f := by omega
      rw [run_simulateQ_query_bind]
      simp only [bhShallowRunFuel_query_inr_succ, bhShallowImplOfHandle, StateT.run_mk, bind_assoc, pure_bind]
      refine bind_congr fun p => ih (rdec t p.1) (hqm _) hle p.2

theorem bhPrefixHandlePostWith_plugExt_simulateQ_bind_eq {α β : Type}
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (k : ℕ) (idA idB : IdentityKey) (s : BitVec 256)
    (mx : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
    (σ : BHE2EDrvState S ℓ) (gs_ext : ExtState ℓ)
    (h : BHPrefixPlugInv k idA idB s σ)
    (k1 : (α × BHE2EDrvState S ℓ) × ExtState ℓ → ProbComp β)
    (k2 : α × BHE2EDrvState S ℓ → ProbComp β)
    (hk : ∀ r σ' gs_ext', BHPrefixPlugInv k idA idB s σ' → gs_ext'.b = gs_ext.b →
      k1 ((r, σ'), gs_ext') = k2 (r, bhPlugExt gs_ext' σ')) :
    ((simulateQ (implExt C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) ℓ qep decT encT idA idB s)
        ((simulateQ (bhShallowImplOfHandle bhTargetQenc bhTargetRdec
          (bhPrefixHandlePostWith S ℓ P ki C K qep decT encT k)) mx).run
          σ)).run gs_ext >>= k1) =
    ((simulateQ (bhE2EDrvImplGenWith ki P C K qep decT encT (bhMkKeyBitConst false)) mx).run
      (bhPlugExt gs_ext σ) >>= k2) := by
  induction mx using OracleComp.inductionOn generalizing σ gs_ext with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    exact hk x σ gs_ext h rfl
  | query_bind q m ih =>
    rw [run_simulateQ_query_bind, run_simulateQ_query_bind]
    simp only [simulateQ_bind, StateT.run_bind, bind_assoc]
    exact bhPrefixHandlePostWith_plugExt_step_bind_eq ki P C K qep decT encT k idA idB s q σ
      gs_ext h _ _ (fun u σ' gs_ext' h' hb' =>
        ih u σ' gs_ext' h' (fun r σ'' gs_ext'' h'' hb'' =>
          hk r σ'' gs_ext'' h'' (hb''.trans hb')))

theorem bhPrefixHandlePostWith_plugExt_simulateQ_postObs_bind_eq {β : Type}
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (k : ℕ) (idA idB : IdentityKey) (s : BitVec 256)
    (mx : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (σ : BHE2EDrvState S ℓ) (gs_ext : ExtState ℓ)
    (h : BHPrefixPlugInv k idA idB s σ)
    (f : Bool → ProbComp β) :
    ((simulateQ (implExt C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) ℓ qep decT encT idA idB s)
        ((simulateQ (bhShallowImplOfHandle bhTargetQenc bhTargetRdec
          (bhPrefixHandlePostWith S ℓ P ki C K qep decT encT k)) mx).run
          σ)).run gs_ext >>= fun x => bhComposedPostObsPlug P gs_ext.b x >>= f) =
    ((simulateQ (bhE2EDrvImplGenWith ki P C K qep decT encT (bhMkKeyBitConst false)) mx).run
      (bhPlugExt gs_ext σ) >>= fun x => bhComposedPostObs P x >>= f) :=
  bhPrefixHandlePostWith_plugExt_simulateQ_bind_eq ki P C K qep decT encT k idA idB s mx σ gs_ext h
    (fun x => bhComposedPostObsPlug P gs_ext.b x >>= f)
    (fun x => bhComposedPostObs P x >>= f)
    (fun b' σ' gs_ext' h' hb' => by
      rw [bhComposedPostObs_bhPlugExt_eq P gs_ext.b b' σ' gs_ext' h' hb'])

theorem simulateQ_implExt_bhPrefixRedWith_eval2_paused
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (idA idB : IdentityKey) (s : BitVec 256) (k qTot : ℕ)
    (t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain) (c : BHPrefixCtx) (p : Option ℕ)
    (σ_p : BHE2EDrvState S ℓ)
    (cont : (bhTargetGameSpec S ℓ (BitVec 512)).Range t →
      OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hInv : BHPrefixPlugInv k idA idB s σ_p)
    (hQ : ∀ v, (cont v).IsQueryBoundP (isGameQuery (G := bhTargetGameSpec S ℓ (BitVec 512))) qTot)
    (flip : Bool) (gs0 : ExtState ℓ) :
    let v := bhTargetRdec t (.inl (.inr p))
    (simulateQ (implExt C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) ℓ qep decT encT idA idB s)
      ((bhPrefixRedWith S ℓ P ki C K qep decT encT k).eval2
        (.paused t c p σ_p cont) flip qTot false)).run gs0 =
    (do
      let ((b', σ'), gs_ext) ←
        ((simulateQ (implExt C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) ℓ qep decT encT idA idB s)
          ((simulateQ (bhShallowImplOfHandle bhTargetQenc bhTargetRdec
            (bhPrefixHandlePostWith S ℓ P ki C K qep decT encT k))
            (cont v)).run { σ_p with b := flip })).run gs0)
      let w ← bhPrefixRedPost P flip b' σ'
      return (w, gs_ext)) := by
  intro v
  change (simulateQ (implExt C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) ℓ qep decT encT idA idB s)
      (bhShallowRunFuel bhTargetQenc bhTargetRdec
        (bhPrefixHandlePostWith S ℓ P ki C K qep decT encT k) false (cont v) qTot
        { σ_p with b := flip } >>= fun (b', σ') =>
        (bhPrefixRedWith S ℓ P ki C K qep decT encT k).finish σ' b' flip)).run gs0 = _
  rw [bhShallowRunFuel_eq_simulateQ_with bhTargetQenc bhTargetRdec
      (bhPrefixHandlePostWith S ℓ P ki C K qep decT encT k) false (hQ v) le_rfl
      { σ_p with b := flip }]
  simp only [simulateQ_bind, StateT.run_bind]
  refine prob_bind_congr_of_support _ _ _ (fun x hmem => ?_)
  rcases x with ⟨⟨b', σ'⟩, gs_ext⟩
  have hInv_flip : BHPrefixPlugInv k idA idB s { σ_p with b := flip } :=
    bhPrefixPlugInv_with_b hInv flip
  have hpaused' : σ'.paused = true := by
    have hPres : ∀ {α : Type} (mx : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
        (σ0 : BHE2EDrvState S ℓ) (gs_0 : ExtState ℓ),
        BHPrefixPlugInv k idA idB s σ0 →
        ∀ x ∈ support ((simulateQ (implExt C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) ℓ qep
            decT encT idA idB s)
          ((simulateQ (bhShallowImplOfHandle bhTargetQenc bhTargetRdec
            (bhPrefixHandlePostWith S ℓ P ki C K qep decT encT k)) mx).run
            σ0)).run gs_0),
        x.1.2.paused = true := by
      intro α mx σ0 gs_0 hInv0
      have h0 := bhPrefixHandlePostWith_plugExt_simulateQ_bind_eq ki P C K qep decT encT k
        idA idB s mx σ0 gs_0 hInv0
        (fun x => pure x.1.2.paused)
        (fun _ => pure true)
        (fun _ σ'' _ h'' _ => by rw [h''.paused_true])
      intro x hx
      have h1 : ∀ y ∈ support ((simulateQ (bhE2EDrvImplGenWith ki P C K qep decT encT
          (bhMkKeyBitConst false)) mx).run (bhPlugExt gs_0 σ0) >>= fun _ => pure true),
          y = true := by
        intro y hy
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hy
        rcases hy with ⟨_, _, rfl⟩; rfl
      have h2 : x.1.2.paused ∈ support
          (((simulateQ (implExt C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) ℓ qep decT encT idA idB s)
            ((simulateQ (bhShallowImplOfHandle bhTargetQenc bhTargetRdec
              (bhPrefixHandlePostWith S ℓ P ki C K qep decT encT k)) mx).run
              σ0)).run gs_0) >>= fun z => pure z.1.2.paused) := by
        rw [support_bind]
        exact Set.mem_iUnion₂.mpr ⟨x, hx, by simp⟩
      rw [h0] at h2
      exact h1 _ h2
    exact hPres (cont v) { σ_p with b := flip } gs0 hInv_flip ((b', σ'), gs_ext) hmem
  dsimp only [bhPrefixRedWith, bhShallowFinishPrefix]
  rw [simulateQ_implExt_bhLiftP_run]
  unfold bhPrefixRedPost
  simp only [hpaused', Bool.not_true, Bool.false_eq_true, ↓reduceIte]

end PrefixFactorizationWith

/-! ## Prefix telescope under `hLazyEq` -/

section PrefixSandwichWith

private theorem evalDist_bind_pure_false_apply_true {α : Type} (c : ProbComp α) :
    𝒟[c >>= fun _ => (pure false : ProbComp Bool)] {true} = 0 := by
  let _ : MeasurableSpace α := ⊤
  have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  rw [evalDist_bind_of_discrete,
    Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
  simp

theorem evalDist_bhPrefixExtPairExpWith_not_fst_eq
    (S : SignalPqxdh.Setup)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (flip : Bool)
    (o : BHPrefixCtx × Mid (bhTargetGameSpec S ℓ (BitVec 512)) Bool (Option ℕ)
      (BHE2EDrvState S ℓ) BHPrefixCtx) :
    𝒟[(fun p : Bool × Bool => !p.1 && (p.2 == !flip)) <$>
        bhPrefixExtPairExpWith S ki P C K ℓ qep decT encT true o] {true} =
    𝒟[(fun p : Bool × Bool => !p.1 && (p.2 == !flip)) <$>
        bhPrefixExtPairExpWith S ki P C K ℓ qep decT encT false o] {true} := by
  rcases o with ⟨ctx, m⟩
  cases m with
  | done b' σ' => rfl
  | paused t c p σ_p cont =>
    unfold bhPrefixExtPairExpWith
    have h (b_k : Bool) :
        ((fun p0 : Bool × Bool => !p0.1 && (p0.2 == !flip)) <$>
          (bhPrefixPlugContWith ki P C K qep decT encT b_k (ctx, .paused t c p σ_p cont) >>=
            fun x => bhComposedPostObs P x >>= fun y => pure (true, y))) =
        ((bhPrefixPlugContWith ki P C K qep decT encT b_k (ctx, .paused t c p σ_p cont) >>=
            bhComposedPostObs P) >>= fun _ => pure false) := by
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind,
        Bool.not_true, Bool.false_and]
    dsimp only
    rw [h true, h false, evalDist_bind_pure_false_apply_true, evalDist_bind_pure_false_apply_true]

set_option maxHeartbeats 800000 in
theorem evalDist_bhPrefixExtPairExpWith_fst_true_le_runR
    (S : SignalPqxdh.Setup)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (k qTot : ℕ) (flip : Bool)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hQ : B.IsQueryBoundP (isGameQuery (G := bhTargetGameSpec S ℓ (BitVec 512))) qTot)
    (o : BHPrefixCtx × Mid (bhTargetGameSpec S ℓ (BitVec 512)) Bool (Option ℕ)
      (BHE2EDrvState S ℓ) BHPrefixCtx)
    (ho : o ∈ support (stageOneAsProbComp ((bhPrefixRedWith S ℓ P ki C K qep decT encT k).eval1
      (fun _ => B) () qTot false))) :
    𝒟[(fun p : Bool × Bool => p.1 && (p.2 == !flip)) <$>
        bhPrefixExtPairExpWith S ki P C K ℓ qep decT encT true o] {true} ≤
    𝒟[SM.runR
        (sessionSchemeFixedSpk
          (paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) o.1.idA o.1.idB)
          ℓ o.1.spkCoins)
        (2 + 1) qep (configRefuseEarlyBobCorr decT encT) true
        ((bhPrefixRedWith S ℓ P ki C K qep decT encT k).eval2 o.2 flip qTot false) >>=
        fun p => pure (p.1 || p.2.win)] {true} := by
  have hprops := mem_support_bhStage1ToProb_eval1_with_props P ki C K qep decT encT k qTot B hQ ho
  rcases o with ⟨ctx, m⟩
  cases m with
  | done b' σ' =>
    unfold bhPrefixExtPairExpWith
    have h :
        ((fun p : Bool × Bool => p.1 && (p.2 == !flip)) <$>
          (bhPrefixPlugContWith ki P C K qep decT encT true (ctx, .done b' σ') >>= fun x =>
            bhComposedPostObs P x >>= fun y => pure (false, y))) =
        ((bhPrefixPlugContWith ki P C K qep decT encT true (ctx, .done b' σ') >>=
            bhComposedPostObs P) >>= fun _ => pure false) := by
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind,
        Bool.false_and]
    dsimp only
    rw [h, evalDist_bind_pure_false_apply_true]
    exact zero_le
  | paused t c p σ_p cont =>
    change ctx = c ∧ BHPrefixPlugInv k ctx.idA ctx.idB ctx.spkCoins σ_p ∧ _ at hprops
    rcases hprops with ⟨rfl, hInv, hQ_cont⟩
    unfold SM.runR bhPrefixExtPairExpWith bhPrefixPlugContWith
    dsimp only
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    refine evalDist_bind_mono_prob ($ᵗ SampledSessionKey) _ _ (fun k_fresh => ?_)
    let spqr := LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K
    let gs0 := SM.initState
      (sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr ctx.idA ctx.idB) ℓ ctx.spkCoins).sendPart
      k_fresh true
    let v := bhTargetRdec t (.inl (.inr p))
    have hPlugB : bhPlugExt gs0 { σ_p with b := flip } = { bhPlugExt gs0 σ_p with b := flip } := rfl
    have hWithB :
        ((simulateQ (bhE2EDrvImplGenWith ki P C K qep decT encT (bhMkKeyBitConst false))
          (cont v)).run (bhPlugExt gs0 σ_p) >>= fun x => bhComposedPostObs P x >>=
            fun y => pure (true && (y == !flip))) =
        ((simulateQ (bhE2EDrvImplGenWith ki P C K qep decT encT (bhMkKeyBitConst false))
          (cont v)).run (bhPlugExt gs0 { σ_p with b := flip }) >>=
            fun x => bhComposedPostObs P x >>= fun y => pure (true && (y == !flip))) := by
      symm
      rw [hPlugB, simulateQ_bhE2EDrvImplGenWith_with_b]
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind,
        bhComposedPostObs_with_b, Prod.mk.eta]
    change 𝒟[((simulateQ (bhE2EDrvImplGenWith ki P C K qep decT encT (bhMkKeyBitConst false))
          (cont v)).run (bhPlugExt gs0 σ_p) >>= fun x => bhComposedPostObs P x >>=
            fun y => pure (true && (y == !flip)))] {true} ≤
      𝒟[(simulateQ (implExt C spqr ℓ qep decT encT ctx.idA ctx.idB ctx.spkCoins)
          ((bhPrefixRedWith S ℓ P ki C K qep decT encT k).eval2
            (.paused t ctx p σ_p cont) flip qTot false)).run
            gs0 >>= fun p0 => pure (p0.1 || p0.2.win)] {true}
    rw [hWithB,
      simulateQ_implExt_bhPrefixRedWith_eval2_paused ki P C K qep decT encT ctx.idA ctx.idB
        ctx.spkCoins k qTot t ctx p σ_p cont hInv hQ_cont flip gs0,
      ← bhPrefixHandlePostWith_plugExt_simulateQ_postObs_bind_eq ki P C K qep decT encT k
        ctx.idA ctx.idB ctx.spkCoins (cont v) { σ_p with b := flip } gs0
        (bhPrefixPlugInv_with_b hInv flip)]
    simp only [bind_assoc, pure_bind]
    refine evalDist_bind_mono_prob_of_support _ _ _ (fun x _ => ?_)
    rcases x with ⟨⟨b', σ'⟩, gs_ext⟩
    have hb0 : gs0.b = true := rfl
    unfold bhComposedPostObsPlug bhPrefixRedPost
    simp only [hb0, beq_self_eq_true, Bool.true_and]
    have hbf : (true == false) = false := rfl
    simp only [hbf, Bool.false_and, Bool.or_false]
    by_cases hC : allTestedSessionsFresh P σ'.st = true
    · simp only [hC, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind]
      have hle := slotStep_bool_le_true true true false (bhE2EDrvWon σ' true) (bhE2EDrvWon σ' false)
        gs_ext.win b' flip
      unfold slotStepY1 slotStepWRed slotStepOut at hle
      simpa using evalDist_bind_mono_of_imp (pure ()) (fun _ => _) (fun _ => _) (fun _ => hle)
    · have hNC : (!allTestedSessionsFresh P σ'.st) = true := by
        cases hc : allTestedSessionsFresh P σ'.st <;> simp_all
      simp only [hNC, ↓reduceIte, bind_assoc, pure_bind]
      refine evalDist_bind_mono_of_imp ($ᵗ Bool) _ _ (fun coin => ?_)
      have hle := slotStep_bool_le_true true false coin (bhE2EDrvWon σ' true) (bhE2EDrvWon σ' false)
        gs_ext.win b' flip
      unfold slotStepY1 slotStepWRed at hle
      simpa using hle

set_option maxHeartbeats 800000 in
theorem evalDist_runR_le_bhPrefixExtPairExpWith_fst_false
    (S : SignalPqxdh.Setup)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (k qTot : ℕ) (flip : Bool)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hQ : B.IsQueryBoundP (isGameQuery (G := bhTargetGameSpec S ℓ (BitVec 512))) qTot)
    (o : BHPrefixCtx × Mid (bhTargetGameSpec S ℓ (BitVec 512)) Bool (Option ℕ)
      (BHE2EDrvState S ℓ) BHPrefixCtx)
    (ho : o ∈ support (stageOneAsProbComp ((bhPrefixRedWith S ℓ P ki C K qep decT encT k).eval1
      (fun _ => B) () qTot false))) :
    𝒟[SM.runR
        (sessionSchemeFixedSpk
          (paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) o.1.idA o.1.idB)
          ℓ o.1.spkCoins)
        (2 + 1) qep (configRefuseEarlyBobCorr decT encT) false
        ((bhPrefixRedWith S ℓ P ki C K qep decT encT k).eval2 o.2 flip qTot false) >>=
        fun p => pure (p.1 && !p.2.win)] {true} ≤
    𝒟[(fun p : Bool × Bool => p.1 && (p.2 == !flip)) <$>
        bhPrefixExtPairExpWith S ki P C K ℓ qep decT encT false o] {true} := by
  have hprops := mem_support_bhStage1ToProb_eval1_with_props P ki C K qep decT encT k qTot B hQ ho
  rcases o with ⟨ctx, m⟩
  cases m with
  | done b' σ' =>
    have hpaused : σ'.paused = false := hprops
    unfold SM.runR
    change 𝒟[($ᵗ SampledSessionKey : ProbComp SampledSessionKey) >>= fun k_fresh =>
        let gs0 := SM.initState
          (sessionSchemeFixedSpk
            (paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) ctx.idA ctx.idB)
            ℓ ctx.spkCoins).sendPart k_fresh false
        (simulateQ (implExt C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) ℓ qep decT encT
            ctx.idA ctx.idB ctx.spkCoins)
          (bhLiftP (G := SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
            (bhShallowFinishPrefix P σ' b' flip))).run gs0 >>= fun p => pure (p.1 && !p.2.win)] {true} ≤ _
    have hDone : ∀ k_fresh : SampledSessionKey,
        (let gs0 := SM.initState
          (sessionSchemeFixedSpk
            (paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) ctx.idA ctx.idB)
            ℓ ctx.spkCoins).sendPart k_fresh false
         (simulateQ (implExt C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) ℓ qep decT encT
            ctx.idA ctx.idB ctx.spkCoins)
          (bhLiftP (G := SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
            (bhShallowFinishPrefix P σ' b' flip))).run gs0 >>= fun p => pure (p.1 && !p.2.win)) =
        pure false := by
      intro k_fresh
      dsimp only [bhShallowFinishPrefix]
      rw [simulateQ_implExt_bhLiftP_run]
      simp [hpaused]
    simp only [hDone, evalDist_bind_pure_false_apply_true]
    exact zero_le
  | paused t c p σ_p cont =>
    change ctx = c ∧ BHPrefixPlugInv k ctx.idA ctx.idB ctx.spkCoins σ_p ∧ _ at hprops
    rcases hprops with ⟨rfl, hInv, hQ_cont⟩
    unfold SM.runR bhPrefixExtPairExpWith bhPrefixPlugContWith
    dsimp only
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    refine evalDist_bind_mono_prob ($ᵗ SampledSessionKey) _ _ (fun k_fresh => ?_)
    let spqr := LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K
    let gs0 := SM.initState
      (sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr ctx.idA ctx.idB) ℓ ctx.spkCoins).sendPart
      k_fresh false
    let v := bhTargetRdec t (.inl (.inr p))
    have hPlugB : bhPlugExt gs0 { σ_p with b := flip } = { bhPlugExt gs0 σ_p with b := flip } := rfl
    have hWithB :
        ((simulateQ (bhE2EDrvImplGenWith ki P C K qep decT encT (bhMkKeyBitConst false))
          (cont v)).run (bhPlugExt gs0 σ_p) >>= fun x => bhComposedPostObs P x >>=
            fun y => pure (true && (y == !flip))) =
        ((simulateQ (bhE2EDrvImplGenWith ki P C K qep decT encT (bhMkKeyBitConst false))
          (cont v)).run (bhPlugExt gs0 { σ_p with b := flip }) >>=
            fun x => bhComposedPostObs P x >>= fun y => pure (true && (y == !flip))) := by
      symm
      rw [hPlugB, simulateQ_bhE2EDrvImplGenWith_with_b]
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind,
        bhComposedPostObs_with_b, Prod.mk.eta]
    change 𝒟[(simulateQ (implExt C spqr ℓ qep decT encT ctx.idA ctx.idB ctx.spkCoins)
          ((bhPrefixRedWith S ℓ P ki C K qep decT encT k).eval2
            (.paused t ctx p σ_p cont) flip qTot false)).run
            gs0 >>= fun p0 => pure (p0.1 && !p0.2.win)] {true} ≤
      𝒟[((simulateQ (bhE2EDrvImplGenWith ki P C K qep decT encT (bhMkKeyBitConst false))
          (cont v)).run (bhPlugExt gs0 σ_p) >>= fun x => bhComposedPostObs P x >>=
            fun y => pure (true && (y == !flip)))] {true}
    rw [hWithB,
      simulateQ_implExt_bhPrefixRedWith_eval2_paused ki P C K qep decT encT ctx.idA ctx.idB
        ctx.spkCoins k qTot t ctx p σ_p cont hInv hQ_cont flip gs0,
      ← bhPrefixHandlePostWith_plugExt_simulateQ_postObs_bind_eq ki P C K qep decT encT k
        ctx.idA ctx.idB ctx.spkCoins (cont v) { σ_p with b := flip } gs0
        (bhPrefixPlugInv_with_b hInv flip)]
    simp only [bind_assoc, pure_bind]
    refine evalDist_bind_mono_prob_of_support _ _ _ (fun x _ => ?_)
    rcases x with ⟨⟨b', σ'⟩, gs_ext⟩
    have hb0 : gs0.b = false := rfl
    unfold bhComposedPostObsPlug bhPrefixRedPost
    simp only [hb0, beq_self_eq_true, Bool.true_and]
    have hbf : (false == true) = false := rfl
    simp only [hbf, Bool.false_and, Bool.or_false]
    by_cases hC : allTestedSessionsFresh P σ'.st = true
    · simp only [hC, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind]
      have hle := slotStep_bool_le_false true true false (bhE2EDrvWon σ' true) (bhE2EDrvWon σ' false)
        gs_ext.win b' flip
      unfold slotStepY0 slotStepWRed slotStepOut at hle
      simpa using evalDist_bind_mono_of_imp (pure ()) (fun _ => _) (fun _ => _) (fun _ => hle)
    · have hNC : (!allTestedSessionsFresh P σ'.st) = true := by
        cases hc : allTestedSessionsFresh P σ'.st <;> simp_all
      simp only [hNC, ↓reduceIte, bind_assoc, pure_bind]
      refine evalDist_bind_mono_of_imp ($ᵗ Bool) _ _ (fun coin => ?_)
      have hle := slotStep_bool_le_false true false coin (bhE2EDrvWon σ' true) (bhE2EDrvWon σ' false)
        gs_ext.win b' flip
      unfold slotStepY0 slotStepWRed at hle
      simpa using hle

/-- Under `hLazyEq`, bounds the `k`-th prefix-creation hybrid step over `ki` by the supremum
over `flip` of the mixture bias of `SM.gameR` on `bhPrefixRedWith`. -/
theorem boolDist_bhPrefixHybExpWith_step_le_of_lazyEq
    (S : SignalPqxdh.Setup)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (k qTot : ℕ)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hLazyEq : ∀ b_k,
      𝒟[bhPrefixLazyFullExpWith S ki P C K ℓ qep decT encT k b_k B] =
        𝒟[bhPrefixExactFullExpWith S ki P C K ℓ qep decT encT k b_k B])
    (hQTot : B.IsQueryBoundP (isGameQuery (G := bhTargetGameSpec S ℓ (BitVec 512))) qTot) :
    𝒟[bhPrefixHybExpWith S ki P C K ℓ qep decT encT (k + 1) B].boolDist
        𝒟[bhPrefixHybExpWith S ki P C K ℓ qep decT encT k B] ≤
      ⨆ flip : Bool,
        𝒟[stageOneAsProbComp
            ((bhPrefixRedWith S ℓ P ki C K qep decT encT k).eval1 (fun _ => B) () qTot false) >>=
          fun o =>
            SM.gameR
              (sessionSchemeFixedSpk
                (paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) o.1.idA o.1.idB)
                ℓ o.1.spkCoins)
              (2 + 1) qep (configRefuseEarlyBobCorr decT encT)
              ((bhPrefixRedWith S ℓ P ki C K qep decT encT k).eval2 o.2 flip qTot false)].boolBias := by
  rw [← bhPrefixExactFullExpWith_true_eq, ← bhPrefixExactFullExpWith_false_eq,
    ← hLazyEq true, ← hLazyEq false,
    bhPrefixLazyFullExpWith_eq_bind_bhPrefixExtExpWith S ki P C K ℓ qep decT encT k qTot true B hQTot,
    bhPrefixLazyFullExpWith_eq_bind_bhPrefixExtExpWith S ki P C K ℓ qep decT encT k qTot false B hQTot]
  refine boolDist_le_iSup_flip_of_beq_not_le _ _ _ (fun flip => ?_)
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  let oa :=
    stageOneAsProbComp ((bhPrefixRedWith S ℓ P ki C K qep decT encT k).eval1 (fun _ => B) () qTot false)
  have hdec : ∀ b : Bool,
      𝒟[oa >>= fun o => bhPrefixExtExpWith S ki P C K ℓ qep decT encT b o >>=
          fun x => pure (x == !flip)] {true} =
        𝒟[oa >>= fun o =>
          (fun p : Bool × Bool => p.1 && (p.2 == !flip)) <$>
            bhPrefixExtPairExpWith S ki P C K ℓ qep decT encT b o] {true} +
        𝒟[oa >>= fun o =>
          (fun p : Bool × Bool => !p.1 && (p.2 == !flip)) <$>
            bhPrefixExtPairExpWith S ki P C K ℓ qep decT encT b o] {true} := fun b =>
    Signed.evalDist_bind_apply_eq_add _ _ _ _ true fun o => by
      unfold bhPrefixExtExpWith
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
      exact evalDist_bind_fst_or_not_fst _ flip
  have h0 :
      𝒟[oa >>= fun o =>
          (fun p : Bool × Bool => !p.1 && (p.2 == !flip)) <$>
            bhPrefixExtPairExpWith S ki P C K ℓ qep decT encT true o] {true} =
        𝒟[oa >>= fun o =>
          (fun p : Bool × Bool => !p.1 && (p.2 == !flip)) <$>
            bhPrefixExtPairExpWith S ki P C K ℓ qep decT encT false o] {true} :=
    evalDist_bind_congr_prob_of_support _ _ _ fun o _ =>
      evalDist_bhPrefixExtPairExpWith_not_fst_eq S ki P C K ℓ qep decT encT flip o
  have h1 :
      𝒟[oa >>= fun o =>
          (fun p : Bool × Bool => p.1 && (p.2 == !flip)) <$>
            bhPrefixExtPairExpWith S ki P C K ℓ qep decT encT true o] {true} ≤
        𝒟[oa >>= fun o =>
          SM.runR
            (sessionSchemeFixedSpk
              (paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) o.1.idA o.1.idB)
              ℓ o.1.spkCoins)
            (2 + 1) qep (configRefuseEarlyBobCorr decT encT) true
            ((bhPrefixRedWith S ℓ P ki C K qep decT encT k).eval2 o.2 flip qTot false) >>=
            fun p => pure (p.1 || p.2.win)] {true} :=
    evalDist_bind_mono_prob_of_support _ _ _ fun o ho =>
      evalDist_bhPrefixExtPairExpWith_fst_true_le_runR S ki P C K ℓ qep decT encT k qTot flip B
        hQTot o ho
  have h2 :
      𝒟[oa >>= fun o =>
          SM.runR
            (sessionSchemeFixedSpk
              (paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) o.1.idA o.1.idB)
              ℓ o.1.spkCoins)
            (2 + 1) qep (configRefuseEarlyBobCorr decT encT) false
            ((bhPrefixRedWith S ℓ P ki C K qep decT encT k).eval2 o.2 flip qTot false) >>=
            fun p => pure (p.1 && !p.2.win)] {true} ≤
        𝒟[oa >>= fun o =>
          (fun p : Bool × Bool => p.1 && (p.2 == !flip)) <$>
            bhPrefixExtPairExpWith S ki P C K ℓ qep decT encT false o] {true} :=
    evalDist_bind_mono_prob_of_support _ _ _ fun o ho =>
      evalDist_runR_le_bhPrefixExtPairExpWith_fst_false S ki P C K ℓ qep decT encT k qTot flip B
        hQTot o ho
  have h3 := Measure.apply_true_le_add_boolDist
    𝒟[oa >>= fun o =>
      SM.runR
        (sessionSchemeFixedSpk
          (paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) o.1.idA o.1.idB)
          ℓ o.1.spkCoins)
        (2 + 1) qep (configRefuseEarlyBobCorr decT encT) true
        ((bhPrefixRedWith S ℓ P ki C K qep decT encT k).eval2 o.2 flip qTot false) >>=
        fun p => pure (p.1 || p.2.win)]
    𝒟[oa >>= fun o =>
      SM.runR
        (sessionSchemeFixedSpk
          (paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) o.1.idA o.1.idB)
          ℓ o.1.spkCoins)
        (2 + 1) qep (configRefuseEarlyBobCorr decT encT) false
        ((bhPrefixRedWith S ℓ P ki C K qep decT encT k).eval2 o.2 flip qTot false) >>=
        fun p => pure (p.1 && !p.2.win)]
  have hb := Signed.boolBias_mix_gameR_eq oa
    (fun o =>
      sessionSchemeFixedSpk
        (paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) o.1.idA o.1.idB)
        ℓ o.1.spkCoins)
    (2 + 1) qep (configRefuseEarlyBobCorr decT encT)
    (fun o => (bhPrefixRedWith S ℓ P ki C K qep decT encT k).eval2 o.2 flip qTot false)
  beta_reduce at hb
  change 𝒟[oa >>= fun o => bhPrefixExtExpWith S ki P C K ℓ qep decT encT true o >>=
      fun x => pure (x == !flip)] {true} ≤
    𝒟[oa >>= fun o => bhPrefixExtExpWith S ki P C K ℓ qep decT encT false o >>=
      fun x => pure (x == !flip)] {true} + _
  rw [hb, hdec true, hdec false, h0]
  exact (add_le_add (h1.trans (h3.trans (add_le_add h2 le_rfl))) le_rfl).trans_eq (by ac_rfl)

/-- Under `hLazyEq`, bounds
`𝒟[bhE2EExpWithKi S ki false P C K ℓ qep decT encT B].boolBias` by the sum over
`k ∈ Finset.range qStart` of the mixture session biases of `bhPrefixRedWith`. -/
theorem boolBias_bhE2EExpWithKi_false_le_sum_prefix_steps_of_lazyEq
    (S : SignalPqxdh.Setup)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (qStart qTot : ℕ)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hLazyEq : ∀ k < qStart, ∀ b_k,
      𝒟[bhPrefixLazyFullExpWith S ki P C K ℓ qep decT encT k b_k B] =
        𝒟[bhPrefixExactFullExpWith S ki P C K ℓ qep decT encT k b_k B])
    (hQStart : B.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
      qStart)
    (hQTot : B.IsQueryBoundP (isGameQuery (G := bhTargetGameSpec S ℓ (BitVec 512))) qTot) :
    𝒟[bhE2EExpWithKi S ki false P C K ℓ qep decT encT B].boolBias ≤
      ∑ k ∈ Finset.range qStart,
        ⨆ flip : Bool,
          𝒟[stageOneAsProbComp
              ((bhPrefixRedWith S ℓ P ki C K qep decT encT k).eval1 (fun _ => B) () qTot false) >>=
            fun o =>
              SM.gameR
                (sessionSchemeFixedSpk
                  (paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) o.1.idA o.1.idB)
                  ℓ o.1.spkCoins)
                (2 + 1) qep (configRefuseEarlyBobCorr decT encT)
                ((bhPrefixRedWith S ℓ P ki C K qep decT encT k).eval2 o.2 flip qTot false)].boolBias := by
  rw [boolBias_bhE2EExpWithKi_false_eq_boolDist_prefixHyb_endpoints S ki P C K ℓ qep decT encT
      qStart B hQStart,
    Measure.boolDist_comm]
  refine (Measure.boolDist_le_sum_range
    (fun k => 𝒟[bhPrefixHybExpWith S ki P C K ℓ qep decT encT k B]) qStart).trans ?_
  refine Finset.sum_le_sum fun k hk => ?_
  rw [Measure.boolDist_comm]
  exact boolDist_bhPrefixHybExpWith_step_le_of_lazyEq S ki P C K ℓ qep decT encT k qTot B
    (hLazyEq k (Finset.mem_range.mp hk)) hQTot

end PrefixSandwichWith

end CryptoVerification.E2E.Prefix1Key
