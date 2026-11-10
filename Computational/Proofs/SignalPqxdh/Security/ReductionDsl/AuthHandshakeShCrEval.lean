/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeShCrLoop
public import Computational.Proofs.SpecLemmas.Pqxdh.Security.BoundProofDefs
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeShCrStep
import Computational.Proofs.SignalPqxdh.Security.SigHopA
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure

/-!
# `shcrReductionAuthProg` Experiment Equality

Defines the `ReductionDsl` `KemShCr` adversary `shcrAuthDslAdv` from `shcrReductionAuthProg` and
proves that its `KemShCr` advantage matches the shallow reduction `shcrReductionAuth` via an
intermediate `RedProg2` runner `shcrAuthMidAdv`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthHs

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl
open OracleSpec OracleComp RoKem
open scoped ENNReal

set_option allowUnsafeReducibility true in
attribute [implicit_reducible] authCodec shcrReductionAuthProg

/-- The `KemShCr` adversary obtained by running `shcrReductionAuthProg` with capacity and fuel
    `b.q_total`. -/
def shcrAuthDslAdv (S : Setup) (b : QueryBudget) (A : AuthAdversary S) : KemShCrAdv where
  State := Mid (authSpec S) Bool
    (shcrReductionAuthProg S b.q_total b.q_total).π.denote
    (shcrReductionAuthProg S b.q_total b.q_total).σ.denote
    (B 1568).denote
  choosePk pk sk :=
    (shcrReductionAuthProg S b.q_total b.q_total).eval1 (fun _ => A.run) (pk, sk) b.q_total false
  findCollision st ss ct :=
    (shcrReductionAuthProg S b.q_total b.q_total).eval2 st (ss, ct) b.q_total false
  q_prim := primQueryBudget S b

abbrev MidSt (S : Setup) :=
  Bytes × Bytes × Nat × RedProg2State (authSpec S) Bool (PauseMid S) (AuthShCrState S)

def chOf {S : Setup} (pk : Bytes) :
    RedProg2State (authSpec S) Bool (PauseMid S) (AuthShCrState S) → Bytes
  | .done _ _ => pk
  | .paused _ d _ _ => d.2.1.pqspkB

abbrev postImpl (S : Setup) (q : AuthQuery S) (s : AuthShCrState S) :
    OracleComp PrimBaseSpec ((authSpec S).Range q × AuthShCrState S) :=
  (pqxdhAuthShCrPrimImpl true S q).run s

/-- Intermediate `KemShCr` adversary running the shallow reduction under generic `RedProg2`
    runners. -/
def shcrAuthMidAdv (S : Setup) (b : QueryBudget) (A : AuthAdversary S) : KemShCrAdv where
  State := MidSt S
  choosePk pk sk :=
    if S.N_spk_tot * S.N_send_tot = 0 then (do
      let secb ← embedUnif ($ᵗ Bool)
      let r ← stepUntilPauseFuel false (stepMid S 0) A.run b.q_total
        (initSh S secb 0 pk sk)
      pure (chOf pk r.2, (pk, sk, 0, r.2)))
    else (do
      let uIdx ← embedUnif (sampleIndexRange S.N_id)
      let jIdx ← embedUnif (sampleIndexRange S.N_recv)
      let sIdx ← embedUnif (sampleIndexRange S.N_send_tot)
      let secb ← embedUnif ($ᵗ Bool)
      let r ← stepUntilPauseFuel false (stepMid S sIdx) A.run b.q_total
        (initSh S secb (uIdx * S.N_recv + jIdx) pk sk)
      pure (chOf pk r.2, (pk, sk, sIdx, r.2)))
  findCollision st ss ct :=
    match st with
    | (pk, sk, _, .done _ h) =>
      extractCollidingKemCtPrim b.q_total pk sk pk ct ss h.recvKemRecs
    | (pk, sk, _, .paused _ d h c) => do
      let x ← postKemAuthPrim S d.1 d.2.1 d.2.2.1 d.2.2.2.1 d.2.2.2.2 h ss ct
      let y ← runWithFuelPrim false (postImpl S) (c x.1) b.q_total x.2
      extractCollidingKemCtPrim b.q_total pk sk d.2.1.pqspkB ct ss y.2.recvKemRecs
  q_prim := primQueryBudget S b

def Fcore {S : Setup} : MidSt S → AuthShCrFinishState S
  | (pk, sk, _, r) => (pk, sk, chOf pk r, Gsh S (none, r))

private theorem evalDist_sampleIndexRange_bind_true {N : ℕ} (hN : 0 < N) (g : ℕ → ProbComp Bool) :
    𝒟[sampleIndexRange N >>= g] {true} =
      ∑ k ∈ Finset.range N, 𝒟[g k] {true} * (N : ℝ≥0∞)⁻¹ := by
  let : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let : MeasurableSpace (Fin N) := ⊤
  simp only [sampleIndexRange, hN, ↓reduceDIte, bind_assoc, pure_bind]
  rw [evalDist_bind_of_discrete,
    MeasureTheory.Measure.bind_apply (MeasurableSet.singleton true)
      (Measurable.of_discrete).aemeasurable,
    MeasureTheory.lintegral_fintype]
  simp_rw [SampleableType.evalDist_uniformSample_singleton, Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range (fun k => 𝒟[g k] {true} * (N : ℝ≥0∞)⁻¹) N

private theorem sum_range_mul_div_mod_ennreal (M N : ℕ) (g : ℕ → ℕ → ℝ≥0∞) :
    ∑ k ∈ Finset.range (M * N), g (k / N) (k % N) =
      ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range N, g i j := by
  induction M with
  | zero => simp
  | succ m ih =>
    rw [Nat.add_one_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    have hPos : 0 < N := by omega
    rw [Nat.add_comm (m * N) j, Nat.add_mul_div_right j m hPos, Nat.div_eq_of_lt hj,
      Nat.zero_add, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

private theorem evalDist_sampleIndexRange_mul_true {M N : ℕ} (hMN : 0 < M * N)
    (g : ℕ → ℕ → ProbComp Bool) :
    𝒟[sampleIndexRange (M * N) >>= fun k => g (k / N) (k % N)] {true} =
      𝒟[sampleIndexRange M >>= fun i => sampleIndexRange N >>= fun j => g i j] {true} := by
  have hM : 0 < M := Nat.pos_of_mul_pos_right hMN
  have hN : 0 < N := Nat.pos_of_mul_pos_left hMN
  rw [evalDist_sampleIndexRange_bind_true hMN,
    sum_range_mul_div_mod_ennreal M N (fun i j => 𝒟[g i j] {true} * ((M * N : ℕ) : ℝ≥0∞)⁻¹),
    evalDist_sampleIndexRange_bind_true hM]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [evalDist_sampleIndexRange_bind_true hN, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Nat.cast_mul, ENNReal.mul_inv (.inl (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hM)))
    (.inl (ENNReal.natCast_ne_top M)), mul_assoc, mul_comm (M : ℝ≥0∞)⁻¹]

/-- Equivalence of `KemShCr` advantage between a 1-draw `(S.N_spk_tot * S.N_send_tot)` reduction
    and a meta-guarded 3-draw `(S.N_id, S.N_recv, S.N_send_tot)` reduction. -/
theorem kemShCr_eq_of_choosePk_spk_send (P : Primitives) (S : Setup)
    (B₁ B₂ : KemShCrAdv) (F : B₂.State → B₁.State)
    (h1 : ℕ → ℕ → Bytes → Bytes → OracleComp PrimBaseSpec (Bytes × B₂.State))
    (hc1 : ∀ pk sk, B₁.choosePk pk sk = (do
      let idx ← embedUnif (sampleIndexRange (S.N_spk_tot * S.N_send_tot))
      Prod.map id F <$> h1 (idx / S.N_send_tot) (idx % S.N_send_tot) pk sk))
    (hc2 : ∀ pk sk, B₂.choosePk pk sk =
      if S.N_spk_tot * S.N_send_tot = 0 then
        h1 0 0 pk sk
      else (do
        let uIdx ← embedUnif (sampleIndexRange S.N_id)
        let jIdx ← embedUnif (sampleIndexRange S.N_recv)
        let sIdx ← embedUnif (sampleIndexRange S.N_send_tot)
        h1 (uIdx * S.N_recv + jIdx) sIdx pk sk))
    (hf : ∀ st ss ct, B₁.findCollision (F st) ss ct = B₂.findCollision st ss ct) :
    KemShCr P B₁ = KemShCr P B₂ := by
  let body (bIdx sIdx : ℕ) (x : Bytes × Bytes) : ProbComp Bool := do
    let (pk', st) ← simulateQ (primBaseImpl P) (h1 bIdx sIdx x.1 x.2)
    let r ← sampleCoins32
    let some (ss, ct) := P.kemEncaps pk' r | return false
    let ct' ← simulateQ (primBaseImpl P) (B₂.findCollision st ss ct)
    return (decide (P.kemDecaps x.2 ct' = some ss) && decide (ct' ≠ ct ∨ pk' ≠ x.1) &&
            decide (ct'.length = kyberCtLen ∧ pk'.length = kyberPkLen))
  have hExp1 : kemShCrExp P B₁ = (do
      let x ← sampleKemKeyGen P
      let idx ← sampleIndexRange (S.N_spk_tot * S.N_send_tot)
      body (idx / S.N_send_tot) (idx % S.N_send_tot) x) := by
    unfold kemShCrExp
    refine bind_congr fun ⟨pk, sk⟩ => ?_
    dsimp only [body]
    rw [hc1 pk sk]
    simp only [map_eq_bind_pure_comp, Function.comp_def, Prod.map, id,
      simulateQ_bind, simulateQ_embedUnif, simulateQ_pure, bind_assoc, pure_bind]
    refine bind_congr fun idx => bind_congr fun x => ?_
    rcases x with ⟨pk', st⟩
    dsimp only
    refine bind_congr fun r => ?_
    cases P.kemEncaps pk' r with
    | none => rfl
    | some p =>
      rcases p with ⟨ss, ct⟩
      dsimp only
      rw [hf st ss ct]
  unfold KemShCr
  by_cases h0 : S.N_spk_tot * S.N_send_tot = 0
  · have hExp2 : kemShCrExp P B₂ = (sampleKemKeyGen P >>= body 0 0) := by
      unfold kemShCrExp
      refine bind_congr fun ⟨pk, sk⟩ => ?_
      dsimp only [body]
      rw [hc2 pk sk]
      simp only [h0, ↓reduceIte]
      rfl
    have hEq0 : (do
        let x ← sampleKemKeyGen P
        let idx ← sampleIndexRange (S.N_spk_tot * S.N_send_tot)
        body (idx / S.N_send_tot) (idx % S.N_send_tot) x) =
      (sampleKemKeyGen P >>= body 0 0) := by
      refine bind_congr fun x => ?_
      simp [h0, sampleIndexRange]
    rw [hExp1, hExp2, hEq0]
  · let sample3 : ProbComp (ℕ × ℕ) := do
      let uIdx ← sampleIndexRange S.N_id
      let jIdx ← sampleIndexRange S.N_recv
      let sIdx ← sampleIndexRange S.N_send_tot
      pure (uIdx * S.N_recv + jIdx, sIdx)
    have hExp2 : kemShCrExp P B₂ = (do
        let x ← sampleKemKeyGen P
        let q ← sample3
        body q.1 q.2 x) := by
      unfold kemShCrExp
      refine bind_congr fun ⟨pk, sk⟩ => ?_
      dsimp only [body]
      rw [hc2 pk sk]
      simp only [h0, ↓reduceIte, sample3, simulateQ_bind, simulateQ_embedUnif,
        bind_assoc, pure_bind]
      rfl
    have hD1 : 𝒟[kemShCrExp P B₁] =
        𝒟[sampleIndexRange (S.N_spk_tot * S.N_send_tot) >>= fun idx =>
          sampleKemKeyGen P >>= body (idx / S.N_send_tot) (idx % S.N_send_tot)] := by
      rw [hExp1, OracleComp.evalDist_bind_bind_swap]
    have hD2 : 𝒟[kemShCrExp P B₂] =
        𝒟[sample3 >>= fun q => sampleKemKeyGen P >>= body q.1 q.2] := by
      rw [hExp2, OracleComp.evalDist_bind_bind_swap]
    rw [hD1, hD2]
    let f (bIdx sIdx : ℕ) : ProbComp Bool := sampleKemKeyGen P >>= body bIdx sIdx
    change 𝒟[sampleIndexRange (S.N_spk_tot * S.N_send_tot) >>= fun idx =>
        f (idx / S.N_send_tot) (idx % S.N_send_tot)] {true} =
      𝒟[sample3 >>= fun q => f q.1 q.2] {true}
    simp only [sample3, bind_assoc, pure_bind]
    have hPos : 0 < S.N_spk_tot * S.N_send_tot := Nat.pos_of_ne_zero h0
    have hPosSpk : 0 < S.N_id * S.N_recv := Nat.pos_of_mul_pos_right hPos
    rw [evalDist_sampleIndexRange_mul_true hPos f]
    have hRew : (fun bIdx => sampleIndexRange S.N_send_tot >>= fun sIdx => f bIdx sIdx) =
        (fun bIdx => sampleIndexRange S.N_send_tot >>= fun sIdx =>
          f ((bIdx / S.N_recv) * S.N_recv + bIdx % S.N_recv) sIdx) := by
      funext bIdx
      rw [Nat.div_add_mod']
    rw [hRew]
    exact evalDist_sampleIndexRange_mul_true hPosSpk
      (fun uIdx jIdx => sampleIndexRange S.N_send_tot >>= fun sIdx => f (uIdx * S.N_recv + jIdx) sIdx)

theorem midAdv_kemShCrExp_eq_core (P : Primitives) (S : Setup) (b : QueryBudget)
    (A : AuthAdversary S) :
    KemShCr P (shcrReductionAuthCore S b A) = KemShCr P (shcrAuthMidAdv S b A) := by
  refine kemShCr_eq_of_choosePk_spk_send P S (shcrReductionAuthCore S b A) (shcrAuthMidAdv S b A)
    Fcore (fun bIdx sIdx pk sk => do
      let secb ← embedUnif ($ᵗ Bool)
      let r ← stepUntilPauseFuel false (stepMid S sIdx) A.run b.q_total
        (initSh S secb bIdx pk sk)
      pure (chOf pk r.2, (pk, sk, sIdx, r.2))) ?_ ?_ ?_
  · intro pk sk
    simp only [shcrReductionAuthCore, choosePkAuthPrimAt, map_eq_bind_pure_comp,
      bind_assoc, Function.comp_def, pure_bind]
    refine bind_congr fun idx => bind_congr fun secb => ?_
    rw [stepUntilShCr_eq]
    simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
    refine bind_congr fun r => ?_
    rcases r with ⟨c, _ | _⟩ <;> rfl
  · intro pk sk
    rfl
  · rintro ⟨pk, sk, sIdx, r⟩ ss ct
    rcases r with ⟨a, h⟩ | ⟨q, d, h, c⟩
    · simp [shcrReductionAuthCore, shcrAuthMidAdv, Fcore, Gsh, findCollisionAuthPrim, chOf]
    · simp only [shcrReductionAuthCore, shcrAuthMidAdv, Fcore, Gsh, findCollisionAuthPrim,
        resumePausedAuthPrim, toPaused, chOf, bind_assoc]
      refine bind_congr fun x => ?_
      rw [runWithFuelShCr_eq]

theorem stepMid_inv (S : Setup) (pk sk : Bytes) (n sIdx : Nat) (q : AuthQuery S)
    (h : AuthShCrState S) (hI : ShInv pk sk n h) :
    HoldsOnLeaves (PreStepInvC (ShInv pk sk) (fun d : PauseMid S => d.2.1.pqspkB) n)
      (stepMid S sIdx q h) := by
  unfold stepMid
  refine HoldsOnLeaves.bind_const _ fun o => ?_
  rcases o with _ | d
  · exact HoldsOnLeaves.map _ (pqxdhAuthShCrPrimImpl_inv S pk sk n q h hI) fun x hx => hx
  · exact HoldsOnLeaves.pure ⟨rfl, hI⟩

theorem postKemAuthPrim_inv (S : Setup) (pk sk : Bytes) (n : Nat) (d : PauseMid S)
    (h : AuthShCrState S) (ss ct : Bytes) (hI : ShInv pk sk n h) :
    HoldsOnLeaves (fun x : AuthResponse × AuthShCrState S => ShInv pk sk (n + 1) x.2)
      (postKemAuthPrim S d.1 d.2.1 d.2.2.1 d.2.2.2.1 d.2.2.2.2 h ss ct) := by
  have hI1 : ShInv pk sk (n + 1) h := hI.mono (Nat.le_succ n)
  simp only [postKemAuthPrim]
  refine HoldsOnLeaves.bind_const _ fun _ => HoldsOnLeaves.bind_const _ fun _ =>
    HoldsOnLeaves.bind_const _ fun _ => ?_
  refine HoldsOnLeaves.bind (finishAuthSimBasePrim_bnd S n _ _ _ _ _ _ _ _ _ _ h.base hI.bnd)
    fun p hp => HoldsOnLeaves.pure ?_
  obtain ⟨r, _ | b'⟩ := p
  · exact ⟨hI1.bnd, hI.tpk, hI.tsk⟩
  · exact ⟨hp b' rfl, hI.tpk, hI.tsk⟩

theorem preStep_eq (S : Setup) (K n : Nat) (q : AuthQuery S) (h : AuthShCrState S) (sIdx : Nat)
    (chosen : Bytes) (hB : AuthBaseListsBounded n h.base) (hn : n + 1 ≤ K) :
    (do
      match ← (shcrReductionAuthProg S K K).handlePre.eval
          (.cons (shcrStToVal sIdx chosen h) (.cons ((authCodec S).qenc q) .nil)) with
      | .inl (rVal, st') => pure (.inl ((authCodec S).rdec q rVal, st'))
      | .inr (ch1Val, (pVal, st')) => pure (.inr (ch1Val, (pVal, st')))) =
      Sum.map (Prod.map id (shcrStToVal sIdx chosen))
        (Prod.map id (Prod.map pauseToVal (shcrStToVal sIdx chosen))) <$> stepMid S sIdx q h := by
  have hr : ∀ x, valToAuthResp (authRespToVal x) = x := valToAuthResp_authRespToVal
  change (do
      match ← (shcrReductionAuthProg S K K).handlePre.eval
          (.cons (shcrStToVal sIdx chosen h) (.cons (authQueryToVal q) .nil)) with
      | .inl (rVal, st') => pure (.inl (valToAuthResp rVal, st'))
      | .inr (ch1Val, (pVal, st')) => pure (.inr (ch1Val, (pVal, st'))) :
      OracleComp PrimBaseSpec (((authSpec S).Range q × shcrStTy.denote) ⊕
        (Bytes × (pauseTy.denote × shcrStTy.denote)))) = _
  rw [shcrPreC_eval S K K n q h sIdx chosen hB hn]
  refine (bind_map_left _ _ _).trans ?_
  rw [map_eq_bind_pure_comp]
  refine bind_congr fun x => ?_
  rcases x with ⟨r, h'⟩ | ⟨c, d, h'⟩
  · show (pure (Sum.inl (valToAuthResp (authRespToVal r), shcrStToVal sIdx chosen h')) :
        OracleComp PrimBaseSpec (((authSpec S).Range q × shcrStTy.denote) ⊕
          (Bytes × (pauseTy.denote × shcrStTy.denote)))) =
      pure (Sum.inl (r, shcrStToVal sIdx chosen h'))
    rw [hr]
  · rfl

theorem postStep_eq (S : Setup) (K n : Nat) (q : AuthQuery S) (h : AuthShCrState S) (sIdx : Nat)
    (chosen : Bytes) (hB : AuthBaseListsBounded n h.base) (hn : n + 1 ≤ K) :
    (do
      let p ← (shcrReductionAuthProg S K K).handlePost.eval
          (.cons (shcrStToVal sIdx chosen h) (.cons ((authCodec S).qenc q) .nil))
      return ((authCodec S).rdec q p.1, p.2)) =
      Prod.map id (shcrStToVal sIdx chosen) <$> postImpl S q h := by
  have hr : ∀ x, valToAuthResp (authRespToVal x) = x := valToAuthResp_authRespToVal
  change (do
      let p ← (shcrReductionAuthProg S K K).handlePost.eval
          (.cons (shcrStToVal sIdx chosen h) (.cons (authQueryToVal q) .nil))
      return (valToAuthResp p.1, p.2) :
      OracleComp PrimBaseSpec ((authSpec S).Range q × shcrStTy.denote)) = _
  dsimp only [shcrReductionAuthProg, authCodec]
  rw [shcrPostC_eval S K n _ _ _ q h sIdx chosen (by simp) (by simp) hB hn]
  refine (bind_map_left _ _ _).trans ?_
  rw [map_eq_bind_pure_comp]
  refine bind_congr fun x => ?_
  show (pure (valToAuthResp (authRespToVal x.1), shcrStToVal sIdx chosen x.2) :
      OracleComp PrimBaseSpec ((authSpec S).Range q × shcrStTy.denote)) =
    pure (x.1, shcrStToVal sIdx chosen x.2)
  rw [hr]

/-- Mid-level invariant on reduction states. -/
def MidInv {S : Setup} (K : Nat) : MidSt S → Prop
  | (pk, sk, _, .done _ h) => ShInv pk sk K h
  | (pk, sk, _, .paused _ _ h c) => ∃ n r, ShInv pk sk n h ∧ n + 1 + r ≤ K ∧
      ∀ x, IsQueryBoundP (c x) (fun q : ℕ ⊕ AuthQuery S => q.isRight = true) r

def Fdsl (S : Setup) (b : QueryBudget) (A : AuthAdversary S) :
    MidSt S → (shcrAuthDslAdv S b A).State
  | (pk, _, sIdx, .done a h) => .done a (shcrStToVal sIdx pk h)
  | (pk, _, sIdx, .paused q d h k) =>
    .paused q d.2.1.pqspkB (pauseToVal d) (shcrStToVal sIdx pk h) k

theorem dslAdv_kemShCrExp_eq_mid (P : Primitives) (S : Setup) (b : QueryBudget)
    (A : AuthAdversary S)
    (hA : IsQueryBoundP A.run (fun q : ℕ ⊕ AuthQuery S => q.isRight = true) b.q_total) :
    kemShCrExp P (shcrAuthDslAdv S b A) = kemShCrExp P (shcrAuthMidAdv S b A) := by
  have hr : ∀ x, valToAuthResp (authRespToVal x) = x := valToAuthResp_authRespToVal
  have hMono : ∀ {pk sk : Bytes} {n m : Nat} {st : AuthShCrState S}, n ≤ m →
      ShInv pk sk n st → ShInv pk sk m st := fun hnm hI => hI.mono hnm
  have hL : ∀ (pk sk : Bytes) (sIdx bIdx : Nat) (secb : Bool),
      HoldsOnLeaves (Stage1InvC (ShInv pk sk) (fun d : PauseMid S => d.2.1.pqspkB) b.q_total)
        (stepUntilPauseFuel false (stepMid S sIdx) A.run b.q_total (initSh S secb bIdx pk sk)) :=
    fun pk sk sIdx bIdx secb =>
      (stepUntilPauseFuel_map_boundedC false id id (ShInv pk sk)
        (fun d : PauseMid S => d.2.1.pqspkB)
        hMono (stepMid S sIdx) (stepMid S sIdx) b.q_total (fun _ _ _ _ _ => by simp)
        (fun n q st hI => stepMid_inv S pk sk n sIdx q st hI) A.run b.q_total hA b.q_total 0
        (initSh S secb bIdx pk sk) ⟨authBaseListsBounded_empty S secb, rfl, rfl⟩ (by omega)).1
  refine kemShCrExp_congr P (shcrAuthMidAdv S b A) (shcrAuthDslAdv S b A) (MidInv b.q_total)
    (Fdsl S b A) ?_ ?_ ?_
  · intro pk sk
    simp only [shcrAuthDslAdv, shcrAuthMidAdv, TwoStageCostedReduction.eval1]
    rw [shcrInit_eval]
    split_ifs with h0
    · simp only [bind_assoc, pure_bind, map_bind]
      refine bind_congr fun secb => ?_
      rw [GRed2_run1_eq_stepUntilPauseFuel (shcrReductionAuthProg S b.q_total b.q_total) false []]
      simp only [bind_map_left]
      refine (congrArg (fun x => x >>= _)
        (stepUntilPauseFuel_map_boundedC false pauseToVal (shcrStToVal 0 pk)
        (ShInv pk sk) (fun d : PauseMid S => d.2.1.pqspkB) hMono (stepMid S 0) _
        b.q_total ?hstep0 (fun n q st hI => stepMid_inv S pk sk n _ q st hI) A.run b.q_total hA
        b.q_total 0 (initSh S secb 0 pk sk)
        ⟨authBaseListsBounded_empty S secb, rfl, rfl⟩ (by omega)).2).trans ?_
      case hstep0 =>
        intro n q st hn hI
        refine (bind_congr fun x => ?_).trans
          (preStep_eq S b.q_total n q st 0 pk hI.bnd hn)
        rcases x with ⟨v, s'⟩ | ⟨c, p, s'⟩ <;> rfl
      · refine (bind_map_left _ _ _).trans ?_
        refine (hL pk sk _ _ secb).bind_congr _ _ fun x hx => ?_
        rcases x with ⟨c, ⟨a, h⟩ | ⟨q, d, h, k⟩⟩
        · obtain ⟨rfl, hI⟩ := hx
          simp [RedProg2State.mapSt, midOfStepUntilPause, Fdsl, chOf, shcrReductionAuthProg,
            Comp.eval, Expr.eval, scTPk, shcrStToVal, hI.tpk]
        · obtain ⟨rfl, -⟩ := hx
          simp only [RedProg2State.mapSt, midOfStepUntilPause, Option.getD_some, Fdsl, chOf,
            Prod.map, id, map_pure]
    · simp only [bind_assoc, pure_bind, map_bind]
      refine bind_congr fun uIdx => bind_congr fun jIdx => bind_congr fun sIdx =>
        bind_congr fun secb => ?_
      rw [GRed2_run1_eq_stepUntilPauseFuel (shcrReductionAuthProg S b.q_total b.q_total) false []]
      simp only [bind_map_left]
      refine (congrArg (fun x => x >>= _)
        (stepUntilPauseFuel_map_boundedC false pauseToVal (shcrStToVal sIdx pk)
        (ShInv pk sk) (fun d : PauseMid S => d.2.1.pqspkB) hMono (stepMid S sIdx) _
        b.q_total ?hstep1 (fun n q st hI => stepMid_inv S pk sk n _ q st hI) A.run b.q_total hA
        b.q_total 0 (initSh S secb (uIdx * S.N_recv + jIdx) pk sk)
        ⟨authBaseListsBounded_empty S secb, rfl, rfl⟩ (by omega)).2).trans ?_
      case hstep1 =>
        intro n q st hn hI
        refine (bind_congr fun x => ?_).trans
          (preStep_eq S b.q_total n q st sIdx pk hI.bnd hn)
        rcases x with ⟨v, s'⟩ | ⟨c, p, s'⟩ <;> rfl
      · refine (bind_map_left _ _ _).trans ?_
        refine (hL pk sk _ _ secb).bind_congr _ _ fun x hx => ?_
        rcases x with ⟨c, ⟨a, h⟩ | ⟨q, d, h, k⟩⟩
        · obtain ⟨rfl, hI⟩ := hx
          simp [RedProg2State.mapSt, midOfStepUntilPause, Fdsl, chOf, shcrReductionAuthProg,
            Comp.eval, Expr.eval, scTPk, shcrStToVal, hI.tpk]
        · obtain ⟨rfl, -⟩ := hx
          simp only [RedProg2State.mapSt, midOfStepUntilPause, Option.getD_some, Fdsl, chOf,
            Prod.map, id, map_pure]
  · intro pk sk
    simp only [shcrAuthMidAdv]
    split_ifs with h0
    · refine HoldsOnLeaves.bind_const _ fun secb => ?_
      refine HoldsOnLeaves.bind (hL pk sk _ _ secb) fun x hx => HoldsOnLeaves.pure ?_
      rcases x with ⟨c, ⟨a, h⟩ | ⟨q, d, h, k⟩⟩ <;> exact hx.2
    · refine HoldsOnLeaves.bind_const _ fun uIdx => HoldsOnLeaves.bind_const _ fun jIdx =>
        HoldsOnLeaves.bind_const _ fun sIdx => HoldsOnLeaves.bind_const _ fun secb => ?_
      refine HoldsOnLeaves.bind (hL pk sk _ _ secb) fun x hx => HoldsOnLeaves.pure ?_
      rcases x with ⟨c, ⟨a, h⟩ | ⟨q, d, h, k⟩⟩ <;> exact hx.2
  · rintro ⟨pk, sk, sIdx, r⟩ hI ss ct
    rcases r with ⟨a, h⟩ | ⟨q, d, h, c⟩
    · simp only [shcrAuthDslAdv, shcrAuthMidAdv, TwoStageCostedReduction.eval2, Fdsl, pure_bind]
      rw [shcrFinish_eval]
      simp only [MidInv] at hI
      rw [hI.tpk, hI.tsk]
    · obtain ⟨n, rr, hI, hb, hc⟩ := hI
      simp only [shcrAuthDslAdv, shcrAuthMidAdv, TwoStageCostedReduction.eval2, Fdsl]
      refine (congrArg (fun x => x >>= _)
        (shcrResume_eval S b.q_total b.q_total d h sIdx pk ss ct (hI.bnd.mono (by omega)))).trans ?_
      refine (bind_map_left _ _ _).trans ?_
      refine (postKemAuthPrim_inv S pk sk n d h ss ct hI).bind_congr _ _ fun x hx => ?_
      simp only [encSCS]
      have hDec : (authCodec S).rdec q (authRespToVal x.1) = x.1 := hr x.1
      rw [hDec, runFuel_pqPrimIface_eq_runWithFuelPrim]
      refine (congrArg (fun x => x >>= _)
        (runWithFuelPrim_map_boundedC false (shcrStToVal sIdx d.2.1.pqspkB) (ShInv pk sk) hMono
        (postImpl S) _ b.q_total ?hstep
        (fun n q st hI => pqxdhAuthShCrPrimImpl_inv S pk sk n q st hI)
        (c x.1) rr (hc x.1) b.q_total (n + 1) x.2 hx (by omega)).2).trans ?_
      case hstep =>
        intro n q st hn hI
        exact postStep_eq S b.q_total n q st _ _ hI.bnd hn
      · refine (bind_map_left _ _ _).trans ?_
        refine (runWithFuelPrim_map_boundedC false id (ShInv pk sk) hMono (postImpl S) (postImpl S)
          b.q_total (fun _ _ _ _ _ => by simp)
          (fun n q st hI => pqxdhAuthShCrPrimImpl_inv S pk sk n q st hI)
          (c x.1) rr (hc x.1) b.q_total (n + 1) x.2 hx (by omega)).1.bind_congr _ _ fun y hy => ?_
        dsimp only [Prod.map, id]
        rw [shcrFinish_eval S b.q_total b.q_total _ y.2 sIdx d.2.1.pqspkB ss ct, hy.tpk, hy.tsk]

/-- `shcrAuthDslAdv` and the shallow `shcrReductionAuth` have equal `KemShCr` advantage. -/
theorem shcrAuthDslAdv_kemShCr_eq (P : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    KemShCr P (shcrAuthDslAdv S b A.1) = KemShCr P (shcrReductionAuth S b A) := by
  have hA : IsQueryBoundP A.1.run (fun q : ℕ ⊕ AuthQuery S => q.isRight = true) b.q_total := by
    have h := SignalPqxdh.QueryBounded.auth_total A.2
    convert h using 1; funext q; cases q <;> rfl
  have hDslMid : KemShCr P (shcrAuthDslAdv S b A.1) = KemShCr P (shcrAuthMidAdv S b A.1) := by
    unfold KemShCr
    rw [dslAdv_kemShCrExp_eq_mid P S b A.1 hA]
  rw [hDslMid, ← midAdv_kemShCrExp_eq_core]
  rfl

theorem shcrAuthDslAdv_kemShCrExp_eq (P : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    𝒟[kemShCrExp P (shcrAuthDslAdv S b A.1)] {true} =
      𝒟[kemShCrExp P (shcrReductionAuth S b A)] {true} :=
  shcrAuthDslAdv_kemShCr_eq P S b A

theorem shcrAuthDslAdv_kemShCrReal_eq (P : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    KemShCrReal P (shcrAuthDslAdv S b A.1) = KemShCrReal P (shcrReductionAuth S b A) :=
  congrArg ENNReal.toReal (shcrAuthDslAdv_kemShCr_eq P S b A)

end SignalPqxdh.Security.ReductionDsl.AuthHs
