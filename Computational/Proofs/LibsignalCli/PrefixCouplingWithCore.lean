/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Reductions.Pqxdh.StatementPqReds
public import Computational.Proofs.E2E.BhPrefixCouplingV1
import Computational.Proofs.ReductionDsl.Notation
import VCVio.EvalDist.Monad.Basic

/-!
# Polymorphic `bhPrefixRedWith` Definitions and Endpoint Identities

**Checked by Lean.** Defines the model-state E2E driver and prefix-hybrid experiments parameterized
over an arbitrary key-indistinguishability oracle `ki`, and proves the `k = 0` and `k = qStart`
endpoint identities.
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
open scoped Computational.Proofs.ReductionDsl.Notation

@[simp]
private theorem stateT_run_lift {M : Type → Type} [Monad M] {σ α : Type}
    (mx : M α) (s : σ) :
    (StateT.lift mx : StateT σ M α).run s = (mx >>= fun x => pure (x, s)) := rfl

@[simp]
private theorem stateT_run_liftM {M : Type → Type} [Monad M] {σ α : Type}
    (mx : M α) (s : σ) :
    (liftM mx : StateT σ M α).run s = (mx >>= fun x => pure (x, s)) := rfl

/-! ## Polymorphic model-state prefix experiments -/

section PrefixDefsWith

@[simp]
theorem bhE2ELocalStartWith_pqxdhKeyIndImpl {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (bMode? : Option Bool) (σ : BHE2EDrvState S ℓ) (sid : SignalPqxdh.SessionId S) :
    compositionLocalStart (SignalPqxdh.pqxdhKeyIndImpl true S P) C K bMode? σ sid =
      bhE2ELocalStart P C K bMode? σ sid := rfl

/-- Model-state E2E driver oracle implementation over `BHE2EDrvState S ℓ` parameterized by `ki`. -/
def bhE2EDrvImplWith {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    QueryImpl (unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
      (StateT (BHE2EDrvState S ℓ) ProbComp) := fun q =>
  match q with
  | .inl n => liftM (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))
  | .inr (.inl (.inl kq)) => do
    let σ ← get
    if !bhDrvKiQueryOk P σ.toModelDriverBase kq then
      return .noneResp
    else if (match kq with | .corruptIK u => bhNoOpkRespPromoted σ.instMeta u | _ => false) then
      return .noneResp
    else
      let (kr, st') ← liftM ((ki kq).run σ.st)
      set (bhE2EMirror { σ with st := st' } kq kr)
      return kr
  | .inr (.inl (.inr (.startDR sid))) => do
    let σ ← get
    let (idx?, σ') ← liftM (compositionLocalStart ki C K (some σ.b) σ sid)
    set σ'
    return idx?
  | .inr (.inr ⟨i, sq⟩) => do
    let σ ← get
    let (sr, σ') ← liftM (bhE2EStepLocalSm C K qep decT encT σ i sq)
    set σ'
    return bhUnpackSmResp sq sr

/-- Model-state E2E experiment parameterized by `ki` and the `KeyInd` challenge bit `secb : Bool`
(`true` = real `DRKey`s, `false` = uniform `DRKey`s). -/
def bhE2EExpWithKi (S : SignalPqxdh.Setup)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (secb : Bool)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let (b', σ) ← (simulateQ (bhE2EDrvImplWith ki P C K qep decT encT) B).run
    { b := b, st := SignalPqxdh.KeyIndState.empty S secb }
  if !allTestedSessionsFresh P σ.st then $ᵗ Bool
  else return (b' == b || bhE2EDrvWon σ b)

theorem bhE2ELocalStartGenWith_const_eq {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (b : Bool)
    (σ : BHE2EDrvState S ℓ) (sid : SignalPqxdh.SessionId S) :
    bhE2ELocalStartGenWith ki C K (bhMkKeyBitConst b) σ sid =
      compositionLocalStart ki C K (some b) σ sid := by
  unfold bhE2ELocalStartGenWith compositionLocalStart
  cases bhE2EGuard σ sid with
  | none => rfl
  | some val =>
    rcases val with ⟨hdr, bnd, ⟨u, j⟩⟩
    simp only [bind_assoc]
    refine bind_congr fun ⟨kr1, st1⟩ => bind_congr fun ⟨kr2, st2⟩ => ?_
    exact bhFinishStartSpkGen_bhMkKeyBitConst_eq C K b { σ with st := st2 } sid kr1 kr2

@[simp]
theorem bhE2EDrvImplPrefixWith_run_eq_gen {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (mkP : BHDrvPrefixKeyBitGen)
    (q : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain) (σ : BHE2EDrvState S ℓ) :
    (bhE2EDrvImplPrefixWith ki P C K qep decT encT mkP q).run σ =
      (bhE2EDrvImplGenWith ki P C K qep decT encT (mkP σ.insts.length) q).run σ := rfl

def bhModeExpWith (S : SignalPqxdh.Setup)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (b : Bool)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) : ProbComp Bool :=
  (simulateQ (bhE2EDrvImplGenWith ki P C K qep decT encT (bhMkKeyBitConst b)) B).run {} >>=
    bhComposedPostObs P

/-- The `k`-th prefix-creation hybrid experiment over `ki`: instances `< k` get bit `true`, and
instances `≥ k` get bit `false`. -/
def bhPrefixHybExpWith (S : SignalPqxdh.Setup)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (k : ℕ)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) : ProbComp Bool :=
  (simulateQ (bhE2EDrvImplPrefixWith ki P C K qep decT encT (bhMkPrefixHyb k)) B).run {} >>=
    bhComposedPostObs P

theorem bhPrefixExactFullExpWith_true_eq (S : SignalPqxdh.Setup)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (k : ℕ)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) :
    bhPrefixExactFullExpWith S ki P C K ℓ qep decT encT k true B =
      bhPrefixHybExpWith S ki P C K ℓ qep decT encT (k + 1) B := by
  unfold bhPrefixExactFullExpWith bhPrefixHybExpWith
  rw [bhMkPrefixExact_true_eq_bhMkPrefixHyb_succ]

theorem bhPrefixExactFullExpWith_false_eq (S : SignalPqxdh.Setup)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (k : ℕ)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) :
    bhPrefixExactFullExpWith S ki P C K ℓ qep decT encT k false B =
      bhPrefixHybExpWith S ki P C K ℓ qep decT encT k B := by
  unfold bhPrefixExactFullExpWith bhPrefixHybExpWith
  rw [bhMkPrefixExact_false_eq_bhMkPrefixHyb]

end PrefixDefsWith

/-! ## Endpoint identities -/

section PrefixEndpointsWith

variable {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}

private theorem bhWin_cond_eq_of_drvWon_not (b b' : Bool) (σ : BHE2EDrvState S ℓ)
    (h : bhE2EDrvWon σ (!b) = false) :
    (b' == b || bhE2EDrvWon σ b) =
      (b == (if bhE2EDrvWon σ true then true else if bhE2EDrvWon σ false then false else b')) := by
  cases b <;> cases b' <;>
    cases h1 : bhE2EDrvWon σ true <;> cases h2 : bhE2EDrvWon σ false <;> simp_all

set_option maxHeartbeats 800000 in
theorem bhE2EDrvImplGenWith_const_preserves_allInstsBit
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : Bool) (q : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain)
    (σ : BHE2EDrvState S ℓ) (hσ : BHAllInstsBit b σ)
    {p : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Range q × BHE2EDrvState S ℓ}
    (hp : p ∈ support ((bhE2EDrvImplGenWith ki P C K qep decT encT (bhMkKeyBitConst b) q).run σ)) :
    BHAllInstsBit b p.2 := by
  rcases q with n | ((kq | ⟨⟨sid⟩⟩) | ⟨i, sq⟩)
  · change p ∈ support ((query (spec := unifSpec) n : ProbComp _) >>= fun u => pure (u, σ)) at hp
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hp
    rcases hp with ⟨_, _, rfl⟩; exact hσ
  · dsimp only [bhE2EDrvImplGenWith] at hp
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hp
    split_ifs at hp
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
      subst hp; exact hσ
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
      subst hp; exact hσ
    · simp only [stateT_run_liftM, StateT.run_bind, StateT.run_set, StateT.run_pure,
        bind_assoc, pure_bind, support_bind, support_pure, Set.mem_iUnion,
        Set.mem_singleton_iff] at hp
      rcases hp with ⟨⟨kr, st'⟩, _, rfl⟩
      exact hσ
  · dsimp only [bhE2EDrvImplGenWith] at hp
    simp only [StateT.run_bind, StateT.run_get, stateT_run_liftM, StateT.run_set,
      StateT.run_pure, bind_assoc, pure_bind, Prod.mk.eta, bind_pure,
      bhE2ELocalStartGenWith_const_eq] at hp
    unfold compositionLocalStart at hp
    cases hG : bhE2EGuard σ sid with
    | none =>
      rw [hG] at hp
      simp only [support_pure, Set.mem_singleton_iff] at hp
      subst hp; exact hσ
    | some val =>
      rcases val with ⟨hdr, bnd, ⟨u, j⟩⟩
      rw [hG] at hp; dsimp only at hp
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hp
      rcases hp with ⟨⟨kr1, st1⟩, _, ⟨kr2, st2⟩, _, ac, _, rfl⟩
      unfold bhE2EFinishStartSpk
      simp only [bhE2EGuard_with_st, hG]
      cases kr1 <;> cases kr2 <;> try exact hσ
      dsimp only
      split_ifs
      · intro d' hd' gs hgs
        rcases List.mem_append.mp hd' with hd' | hd'
        · exact hσ d' hd' gs hgs
        · rw [List.mem_singleton.mp hd'] at hgs
          simp only [Option.map_some, Option.some.injEq] at hgs
          subst hgs; rfl
      · exact hσ
  · dsimp only [bhE2EDrvImplGenWith] at hp
    simp only [StateT.run_bind, StateT.run_get, stateT_run_liftM, StateT.run_set,
      StateT.run_pure, bind_assoc, pure_bind, support_bind, support_pure,
      Set.mem_iUnion, Set.mem_singleton_iff] at hp
    rcases hp with ⟨⟨sr, σ'⟩, hsm, rfl⟩
    exact bhE2EStepLocalSm_preserves_allInstsBit C K qep decT encT b σ hσ i sq hsm

theorem simulateQ_bhE2EDrvImplGenWith_const_preserves_allInstsBit
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : Bool) {α : Type}
    (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
    (σ : BHE2EDrvState S ℓ) (hσ : BHAllInstsBit b σ)
    {p : α × BHE2EDrvState S ℓ}
    (hp : p ∈ support
      ((simulateQ (bhE2EDrvImplGenWith ki P C K qep decT encT (bhMkKeyBitConst b)) oa).run σ)) :
    BHAllInstsBit b p.2 := by
  induction oa using OracleComp.inductionOn generalizing σ p with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp; exact hσ
  | query_bind q mx ih =>
    rw [run_simulateQ_query_bind, support_bind] at hp
    rcases Set.mem_iUnion₂.mp hp with ⟨⟨u, σ'⟩, hstep, hp⟩
    exact ih u σ'
      (bhE2EDrvImplGenWith_const_preserves_allInstsBit ki P C K qep decT encT b q σ hσ hstep) hp

set_option maxHeartbeats 800000 in
theorem bhE2EDrvImplGenWith_with_b
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (mkKeyBit : ModelDriverKeyBitGen)
    (q : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain)
    (σ : BHE2EDrvState S ℓ) (b' : Bool) :
    (bhE2EDrvImplGenWith ki P C K qep decT encT mkKeyBit q).run { σ with b := b' } =
      (fun (r, σ') => (r, { σ' with b := b' })) <$>
        (bhE2EDrvImplGenWith ki P C K qep decT encT mkKeyBit q).run σ := by
  rcases q with n | ((kq | ⟨⟨sid⟩⟩) | ⟨i, sq⟩)
  · change ((query (spec := unifSpec) n : ProbComp (Fin (n + 1))) >>=
        fun u => pure (u, { σ with b := b' })) =
      ((fun (r, σ') => (r, { σ' with b := b' })) <$>
        ((query (spec := unifSpec) n : ProbComp (Fin (n + 1))) >>= fun u => pure (u, σ)))
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  · dsimp only [bhE2EDrvImplGenWith]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    have hBase : ({ σ with b := b' } : BHE2EDrvState S ℓ).toModelDriverBase =
        σ.toModelDriverBase := rfl
    have hMeta : ({ σ with b := b' } : BHE2EDrvState S ℓ).instMeta = σ.instMeta := rfl
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
    have hG : bhE2EGuard { σ with b := b' } sid = bhE2EGuard σ sid := rfl
    rw [hG]
    cases bhE2EGuard σ sid with
    | none => simp
    | some val =>
      rcases val with ⟨hdr, bnd, ⟨u, j⟩⟩
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      refine bind_congr fun ⟨kr1, st1⟩ => bind_congr fun ⟨kr2, st2⟩ => bind_congr fun kb => ?_
      unfold bhFinishStartSpkGen
      have hG2 : bhE2EGuard { σ with b := b', st := st2 } sid =
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
      StateT.run_pure, bind_assoc, pure_bind, bhE2EStepLocalSm_with_b,
      map_eq_bind_pure_comp, Function.comp_def]

theorem simulateQ_bhE2EDrvImplWith_eq_gen_const {α : Type}
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : Bool) (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
    (σ : BHE2EDrvState S ℓ) :
    (simulateQ (bhE2EDrvImplWith ki P C K qep decT encT) oa).run { σ with b := b } =
      (fun (r, σ') => (r, { σ' with b := b })) <$>
        (simulateQ (bhE2EDrvImplGenWith ki P C K qep decT encT (bhMkKeyBitConst b)) oa).run σ := by
  induction oa using OracleComp.inductionOn generalizing σ with
  | pure x => rfl
  | query_bind q mx ih =>
    rw [run_simulateQ_query_bind, run_simulateQ_query_bind]
    have hStep :
        (bhE2EDrvImplWith ki P C K qep decT encT q).run { σ with b := b } =
          (bhE2EDrvImplGenWith ki P C K qep decT encT (bhMkKeyBitConst b) q).run
            { σ with b := b } := by
      rcases q with n | ((kq | ⟨⟨sid⟩⟩) | ⟨i, sq⟩)
      · rfl
      · rfl
      · dsimp only [bhE2EDrvImplWith, bhE2EDrvImplGenWith]
        simp only [StateT.run_bind, StateT.run_get, stateT_run_liftM, StateT.run_set,
          StateT.run_pure, bind_assoc, pure_bind, Prod.mk.eta, bind_pure,
          bhE2ELocalStartGenWith_const_eq]
      · rfl
    rw [hStep, bhE2EDrvImplGenWith_with_b ki P C K qep decT encT (bhMkKeyBitConst b) q σ b]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    exact bind_congr fun ⟨r, σ'⟩ => by
      simpa only [map_eq_bind_pure_comp, Function.comp_def] using ih r σ'

theorem bhPrefixHybExpWith_zero_eq
    (S : SignalPqxdh.Setup)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) :
    bhPrefixHybExpWith S ki P C K ℓ qep decT encT 0 B =
      bhModeExpWith S ki P C K ℓ qep decT encT false B := by
  unfold bhPrefixHybExpWith bhModeExpWith
  have hmk : ∀ len : ℕ, bhMkPrefixHyb 0 len = bhMkKeyBitConst false := by
    intro len; funext kr1 kr2; simp [bhMkPrefixHyb, bhMkKeyBitConst]
  have hsim : ∀ (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
      (σ : BHE2EDrvState S ℓ),
      (simulateQ (bhE2EDrvImplPrefixWith ki P C K qep decT encT (bhMkPrefixHyb 0)) oa).run σ =
        (simulateQ (bhE2EDrvImplGenWith ki P C K qep decT encT (bhMkKeyBitConst false)) oa).run σ := by
    intro oa σ
    induction oa using OracleComp.inductionOn generalizing σ with
    | pure x => rfl
    | query_bind q mx ih =>
      rw [run_simulateQ_query_bind, run_simulateQ_query_bind,
        bhE2EDrvImplPrefixWith_run_eq_gen, hmk]
      exact bind_congr fun ⟨r, σ'⟩ => ih r σ'
  rw [hsim]

private theorem bhE2EStepLocalSm_insts_length_eq
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (σ : BHE2EDrvState S ℓ) (i : ℕ)
    (sq : (SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    {p : BHE2ESmResp ℓ × BHE2EDrvState S ℓ}
    (hp : p ∈ support (bhE2EStepLocalSm C K qep decT encT σ i sq)) :
    p.2.insts.length = σ.insts.length := by
  rw [bhE2EStepLocalSm_eq_filter] at hp
  by_cases hC : (!bhE2EDrvInstClean σ i) = true
  · simp only [hC, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hp
    subst hp; rfl
  · simp only [hC, Bool.false_eq_true, ↓reduceIte] at hp
    cases hi : σ.insts[i]? with
    | none =>
      rw [hi] at hp; simp only [support_pure, Set.mem_singleton_iff] at hp
      subst hp; rfl
    | some d =>
      rw [hi] at hp
      cases him : σ.instMeta[i]? with
      | none =>
        rw [him] at hp; simp only [support_pure, Set.mem_singleton_iff] at hp
        subst hp; rfl
      | some im =>
        rw [him] at hp; dsimp only at hp
        split_ifs at hp
        · simp only [support_pure, Set.mem_singleton_iff] at hp
          subst hp; rfl
        · cases hd : d.gs with
          | none =>
            rw [hd] at hp; simp only [support_pure, Set.mem_singleton_iff] at hp
            subst hp; rfl
          | some gs =>
            rw [hd] at hp
            cases hf : bhFilterSmQuery d im sq with
            | none =>
              rw [hf] at hp; simp only [support_pure, Set.mem_singleton_iff] at hp
              subst hp; rfl
            | some q' =>
              rw [hf] at hp
              simp only [support_bind, support_pure, Set.mem_iUnion,
                Set.mem_singleton_iff] at hp
              rcases hp with ⟨⟨_, _⟩, _, rfl⟩
              simp

theorem bhE2EDrvImplGenWith_step_length
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (mkKeyBit : ModelDriverKeyBitGen)
    (q : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain)
    (σ : BHE2EDrvState S ℓ)
    {p : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Range q × BHE2EDrvState S ℓ}
    (hp : p ∈ support ((bhE2EDrvImplGenWith ki P C K qep decT encT mkKeyBit q).run σ)) :
    (bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = false →
      p.2.insts.length = σ.insts.length) ∧
    σ.insts.length ≤ p.2.insts.length ∧
    p.2.insts.length ≤ σ.insts.length + 1 := by
  rcases q with n | ((kq | ⟨⟨sid⟩⟩) | ⟨i, sq⟩)
  · change p ∈ support ((query (spec := unifSpec) n : ProbComp _) >>= fun u => pure (u, σ)) at hp
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hp
    rcases hp with ⟨_, _, rfl⟩
    exact ⟨fun _ => rfl, le_rfl, Nat.le_succ _⟩
  · dsimp only [bhE2EDrvImplGenWith] at hp
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hp
    split_ifs at hp
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
      subst hp; exact ⟨fun _ => rfl, le_rfl, Nat.le_succ _⟩
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
      subst hp; exact ⟨fun _ => rfl, le_rfl, Nat.le_succ _⟩
    · simp only [stateT_run_liftM, StateT.run_bind, StateT.run_set, StateT.run_pure,
        bind_assoc, pure_bind, support_bind, support_pure, Set.mem_iUnion,
        Set.mem_singleton_iff] at hp
      rcases hp with ⟨⟨kr, st'⟩, _, rfl⟩
      exact ⟨fun _ => rfl, le_rfl, Nat.le_succ _⟩
  · simp only [bhClassifyTarget, bhClassifyTargetOnly, Bool.true_eq_false, IsEmpty.forall_iff,
      true_and]
    dsimp only [bhE2EDrvImplGenWith] at hp
    simp only [StateT.run_bind, StateT.run_get, stateT_run_liftM, StateT.run_set,
      StateT.run_pure, bind_assoc, pure_bind, Prod.mk.eta, bind_pure] at hp
    unfold bhE2ELocalStartGenWith at hp
    cases hG : bhE2EGuard σ sid with
    | none =>
      rw [hG] at hp
      simp only [support_pure, Set.mem_singleton_iff] at hp
      subst hp; exact ⟨le_rfl, Nat.le_succ _⟩
    | some val =>
      rcases val with ⟨hdr, bnd, ⟨u, j⟩⟩
      rw [hG] at hp; dsimp only at hp
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hp
      rcases hp with ⟨⟨kr1, st1⟩, _, ⟨kr2, st2⟩, _, kb, _, rfl⟩
      unfold bhFinishStartSpkGen
      simp only [bhE2EGuard_with_st, hG]
      cases kr1 <;> cases kr2 <;> try exact ⟨le_rfl, Nat.le_succ _⟩
      dsimp only
      split_ifs
      · simp
      · exact ⟨le_rfl, Nat.le_succ _⟩
  · dsimp only [bhE2EDrvImplGenWith] at hp
    simp only [StateT.run_bind, StateT.run_get, stateT_run_liftM, StateT.run_set,
      StateT.run_pure, bind_assoc, pure_bind, support_bind, support_pure,
      Set.mem_iUnion, Set.mem_singleton_iff] at hp
    rcases hp with ⟨⟨sr, σ'⟩, hsm, rfl⟩
    have hlen := bhE2EStepLocalSm_insts_length_eq C K qep decT encT σ i sq hsm
    dsimp only at hlen ⊢
    exact ⟨fun _ => hlen, by omega, by omega⟩

theorem simulateQ_bhE2EDrvImplPrefixWith_hyb_eq_const_true {α : Type}
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (qStart n : ℕ)
    (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
    (σ : BHE2EDrvState S ℓ)
    (hQ : oa.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true) n)
    (hlen : σ.insts.length + n ≤ qStart) :
    (simulateQ (bhE2EDrvImplPrefixWith ki P C K qep decT encT (bhMkPrefixHyb qStart)) oa).run σ =
      (simulateQ (bhE2EDrvImplGenWith ki P C K qep decT encT (bhMkKeyBitConst true)) oa).run σ := by
  induction oa using OracleComp.inductionOn generalizing n σ with
  | pure x => rfl
  | query_bind q mx ih =>
    rw [isQueryBoundP_query_bind_iff] at hQ
    rw [run_simulateQ_query_bind, run_simulateQ_query_bind, bhE2EDrvImplPrefixWith_run_eq_gen]
    by_cases hCtl : bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true
    · have hn : 0 < n := hQ.1.resolve_left (by simp [hCtl])
      have hlt : σ.insts.length < qStart := by omega
      have hmk : bhMkPrefixHyb qStart σ.insts.length = bhMkKeyBitConst true := by
        funext kr1 kr2
        simp [bhMkPrefixHyb, bhMkKeyBitConst, hlt]
      rw [hmk]
      refine prob_bind_congr_of_support _ _ _ (fun ⟨r, σ'⟩ hp => ?_)
      have hStep :=
        (bhE2EDrvImplGenWith_step_length ki P C K qep decT encT (bhMkKeyBitConst true) q σ hp).2.2
      dsimp only at hStep
      have hQr : (mx r).IsQueryBoundP
          (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
          (n - 1) := by
        simpa [hCtl] using hQ.2 r
      exact ih r (n - 1) σ' hQr (by omega)
    · have hCtlF : bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = false :=
        Bool.eq_false_iff.mpr hCtl
      have hNonCtlEq :
          (bhE2EDrvImplGenWith ki P C K qep decT encT (bhMkPrefixHyb qStart σ.insts.length) q).run σ =
            (bhE2EDrvImplGenWith ki P C K qep decT encT (bhMkKeyBitConst true) q).run σ := by
        rcases q with m | ((kq | ⟨⟨sid⟩⟩) | ⟨i, sq⟩)
        · rfl
        · rfl
        · simp [bhClassifyTarget, bhClassifyTargetOnly] at hCtlF
        · rfl
      rw [hNonCtlEq]
      refine prob_bind_congr_of_support _ _ _ (fun ⟨r, σ'⟩ hp => ?_)
      have hLenEq :=
        (bhE2EDrvImplGenWith_step_length ki P C K qep decT encT (bhMkKeyBitConst true) q σ hp).1
          hCtlF
      dsimp only at hLenEq
      have hQr : (mx r).IsQueryBoundP
          (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
          n := by
        simpa [hCtl] using hQ.2 r
      exact ih r n σ' hQr (by omega)

theorem bhPrefixHybExpWith_qStart_eq
    (S : SignalPqxdh.Setup)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (qStart : ℕ)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hStart : B.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
      qStart) :
    bhPrefixHybExpWith S ki P C K ℓ qep decT encT qStart B =
      bhModeExpWith S ki P C K ℓ qep decT encT true B := by
  unfold bhPrefixHybExpWith bhModeExpWith
  rw [simulateQ_bhE2EDrvImplPrefixWith_hyb_eq_const_true ki P C K qep decT encT qStart qStart B {}
    hStart (by simp)]

private theorem evalDist_uniformBool_beq_left (b : Bool) :
    𝒟[($ᵗ Bool : ProbComp Bool) >>= fun z => pure (b == z)] = 𝒟[($ᵗ Bool : ProbComp Bool)] := by
  cases b
  · simpa using ProbComp.evalDist_bind_not_uniformBool (fun z => (pure z : ProbComp Bool))
  · simp

theorem evalDist_bhE2EExpWithKi_false_branch
    (S : SignalPqxdh.Setup)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : Bool)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) :
    𝒟[do
      let (b', σ) ← (simulateQ (bhE2EDrvImplWith ki P C K qep decT encT) B).run
        { b := b, st := SignalPqxdh.KeyIndState.empty S false }
      if !allTestedSessionsFresh P σ.st then $ᵗ Bool
      else return (b' == b || bhE2EDrvWon σ b)] =
    𝒟[do
      let g ← bhModeExpWith S ki P C K ℓ qep decT encT b B
      return (b == g)] := by
  have hInit : ({ b := b, st := SignalPqxdh.KeyIndState.empty S false } : BHE2EDrvState S ℓ) =
      { ({} : BHE2EDrvState S ℓ) with b := b } := rfl
  rw [hInit, simulateQ_bhE2EDrvImplWith_eq_gen_const]
  unfold bhModeExpWith bhComposedPostObs
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  refine evalDist_bind_congr_of_support _ _ _ fun ⟨b', σ⟩ hp => ?_
  have hbit : BHAllInstsBit b σ :=
    simulateQ_bhE2EDrvImplGenWith_const_preserves_allInstsBit ki P C K qep decT encT b B {}
      (bhAllInstsBit_empty b) hp
  have hnot : bhE2EDrvWon σ (!b) = false := bhE2EDrvWon_not_of_allInstsBit hbit
  have hWonEq : ∀ z, bhE2EDrvWon { σ with b := b } z = bhE2EDrvWon σ z := fun _ => rfl
  simp only [hWonEq]
  cases allTestedSessionsFresh P σ.st
  · simp only [Bool.not_false, ↓reduceIte]
    exact (evalDist_uniformBool_beq_left b).symm
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind]
    rw [bhWin_cond_eq_of_drvWon_not b b' σ hnot]

theorem evalDist_bhE2EExpWithKi_false_eq_bind_modeExp
    (S : SignalPqxdh.Setup)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) :
    𝒟[bhE2EExpWithKi S ki false P C K ℓ qep decT encT B] =
      𝒟[do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let g ← if b then bhModeExpWith S ki P C K ℓ qep decT encT true B
                else bhModeExpWith S ki P C K ℓ qep decT encT false B
        return (b == g)] := by
  unfold bhE2EExpWithKi
  refine evalDist_bind_congr ($ᵗ Bool) _ _ fun b => ?_
  cases b
  · exact evalDist_bhE2EExpWithKi_false_branch S ki P C K ℓ qep decT encT false B
  · exact evalDist_bhE2EExpWithKi_false_branch S ki P C K ℓ qep decT encT true B

theorem boolBias_bhE2EExpWithKi_false_eq_boolDist_prefixHyb_endpoints
    (S : SignalPqxdh.Setup)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (qStart : ℕ)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hStart : B.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
      qStart) :
    𝒟[bhE2EExpWithKi S ki false P C K ℓ qep decT encT B].boolBias =
      𝒟[bhPrefixHybExpWith S ki P C K ℓ qep decT encT qStart B].boolDist
        𝒟[bhPrefixHybExpWith S ki P C K ℓ qep decT encT 0 B] := by
  rw [evalDist_bhE2EExpWithKi_false_eq_bind_modeExp,
    evalDist_boolBias_bind_uniformBool,
    bhPrefixHybExpWith_zero_eq,
    bhPrefixHybExpWith_qStart_eq S ki P C K ℓ qep decT encT qStart B hStart]

end PrefixEndpointsWith

end CryptoVerification.E2E.Prefix1Key
