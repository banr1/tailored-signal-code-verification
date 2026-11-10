/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyShCr
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeShCrEval
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeShCrStep
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthCoreSimSend
import Computational.Proofs.SpecLemmas.SignalPqxdh.Game
import VCVio.EvalDist.Monad.Basic

/-!
# One-Key `KemShCr` Experiment Equality

**Checked by Lean.** Proves that the `KemShCr` adversary `shcrAuth1KeyDslAdv` executing the one-key
`ReductionDsl` program `shcrReductionAuthProg1Key` has the same `KemShCr` advantage as the shallow
reduction `shcrReductionAuth1Key`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthHs

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl
open OracleSpec OracleComp RoKem

set_option allowUnsafeReducibility true in
attribute [implicit_reducible] authCodec shcrReductionAuthProg shcrReductionAuthProg1Key

/-- One-key pre-pause step: pause (outputting `bundle.pqspkB`) or run the simulator handler. -/
def stepMid1Key (S : Setup) (sIdx : Nat) (q : AuthQuery S) (h : AuthShCrState S) :
    OracleComp PrimBaseSpec
      ((AuthResponse × AuthShCrState S) ⊕ (Bytes × (PauseMid S × AuthShCrState S))) := do
  match ← tryPauseMid S sIdx q h with
  | some d => pure (.inr (d.2.1.pqspkB, (d, h)))
  | none => Sum.inl <$> (pqxdhAuthShCrPrimImpl1Key true S q).run h

theorem shcrPre1KeyC_eval (S : Setup) (Q K n : Nat) (q : AuthQuery S) (h : AuthShCrState S)
    (sIdx : Nat) (chosen : Bytes) (hB : AuthBaseListsBounded n h.base) (hn : n + 1 ≤ K) :
    (shcrReductionAuthProg1Key S Q K).handlePre.eval
        (.cons (shcrStToVal sIdx chosen h) (.cons (authQueryToVal q) .nil)) =
      Sum.map (encSCS sIdx chosen) (Prod.map id (Prod.map pauseToVal (shcrStToVal sIdx chosen))) <$>
        stepMid1Key S sIdx q h := by
  have hK : AuthBaseListsBounded K h.base := hB.mono (by omega)
  dsimp only [shcrReductionAuthProg1Key, authCodec]
  simp only [shcrPre1KeyC, bindV, caseOptV, Comp.eval]
  rw [pauseCheckC_eval S K _ _ h sIdx chosen rfl hK _ q rfl]
  simp only [stepMid1Key, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  refine bind_congr fun o => ?_
  rcases o with _ | d
  · simp only [Option.map_none, Expr.eval]
    rw [shcrPost1KeyC_eval S K n _ _ _ q h sIdx chosen (by simp) (by simp) hB hn]
    simp [map_eq_bind_pure_comp, Expr.eval, v]
  · obtain ⟨sid, bu, m0, m1, ui⟩ := d
    simp [Expr.eval, v, pauseToVal, shcrStToVal, preKeyBundleToVal]

theorem stepUntilShCr1Key_eq (S : Setup) (sIdx : Nat)
    (mx : OracleComp (unifSpec + authSpec S) Bool) (h : AuthShCrState S) (fuel : Nat) :
    stepUntilShCrFuelAuthPrim1Key S sIdx mx h fuel =
      Gsh S <$> stepUntilPauseFuel false (stepMid1Key S sIdx) mx fuel h := by
  refine stepUntilPauseFuel_char false (stepMid1Key S sIdx) (Gsh S)
    (fun mx fuel h => stepUntilShCrFuelAuthPrim1Key S sIdx mx h fuel) ?_ ?_ ?_ ?_ mx fuel h
  · intro a fuel s; rfl
  · intro uq k fuel s
    simp only [stepUntilShCrFuelAuthPrim1Key]
    rw [OracleComp.construct_query_bind]
  · intro gq k s
    simp only [stepUntilShCrFuelAuthPrim1Key]
    rw [OracleComp.construct_query_bind]
    rfl
  · intro gq k fuel s
    simp only [stepUntilShCrFuelAuthPrim1Key]
    rw [OracleComp.construct_query_bind]
    dsimp only
    rw [tryPauseMid_shallow, bind_map_left]
    simp only [stepMid1Key, bind_assoc]
    refine bind_congr fun o => ?_
    rcases o with _ | d
    · simp only [Option.map_none, map_eq_bind_pure_comp, bind_assoc]
      rfl
    · simp only [Option.map_some, pure_bind]
      rfl

theorem runWithFuelShCr1Key_eq (S : Setup) (mx : OracleComp (unifSpec + authSpec S) Bool)
    (h : AuthShCrState S) (fuel : Nat) :
    runWithFuelAuthShCrPrim1Key S mx h fuel =
      runWithFuelPrim false (fun q s => (pqxdhAuthShCrPrimImpl1Key true S q).run s) mx fuel h := by
  have := runWithFuelPrim_char false (fun q s => (pqxdhAuthShCrPrimImpl1Key true S q).run s) id
    (fun mx fuel h => runWithFuelAuthShCrPrim1Key S mx h fuel) (fun _ _ _ => rfl)
    (fun uq k fuel s => by
      simp only [runWithFuelAuthShCrPrim1Key]; rw [OracleComp.construct_query_bind])
    (fun gq k s => by
      simp only [runWithFuelAuthShCrPrim1Key]; rw [OracleComp.construct_query_bind]; rfl)
    (fun gq k fuel s => by
      simp only [runWithFuelAuthShCrPrim1Key]; rw [OracleComp.construct_query_bind]) mx fuel h
  rw [this, id_map]

/-- The `KemShCr` adversary obtained by running the one-key `ReductionDsl` program
    `shcrReductionAuthProg1Key` (`Q = K = b.q_total`, fuel `b.q_total`). -/
def shcrAuth1KeyDslAdv (S : Setup) (b : QueryBudget) (A : AuthAdversary S) : KemShCrAdv where
  State := Mid (authSpec S) Bool
    (shcrReductionAuthProg1Key S b.q_total b.q_total).π.denote
    (shcrReductionAuthProg1Key S b.q_total b.q_total).σ.denote
    (B 1568).denote
  choosePk pk sk :=
    (shcrReductionAuthProg1Key S b.q_total b.q_total).eval1 (fun _ => A.run) (pk, sk) b.q_total false
  findCollision st ss ct :=
    (shcrReductionAuthProg1Key S b.q_total b.q_total).eval2 st (ss, ct) b.q_total false
  q_prim := primQueryBudget S b

abbrev postImpl1Key (S : Setup) (q : AuthQuery S) (s : AuthShCrState S) :
    OracleComp PrimBaseSpec ((authSpec S).Range q × AuthShCrState S) :=
  (pqxdhAuthShCrPrimImpl1Key true S q).run s

/-- Mid-level one-key adversary: the shallow reduction run by the generic `RedProg2` runners. -/
def shcrAuth1KeyMidAdv (S : Setup) (b : QueryBudget) (A : AuthAdversary S) : KemShCrAdv where
  State := MidSt S
  choosePk pk sk :=
    if S.N_spk_tot * S.N_send_tot = 0 then
      (do
        let secb ← embedUnif ($ᵗ Bool)
        let r ← stepUntilPauseFuel false (stepMid1Key S 0) A.run b.q_total
          (initSh S secb 0 pk sk)
        pure (chOf pk r.2, (pk, sk, 0, r.2)))
    else
      (do
        let uIdx ← embedUnif (sampleIndexRange S.N_id)
        let jIdx ← embedUnif (sampleIndexRange S.N_recv)
        let sIdx ← embedUnif (sampleIndexRange S.N_send_tot)
        let secb ← embedUnif ($ᵗ Bool)
        let r ← stepUntilPauseFuel false (stepMid1Key S sIdx) A.run b.q_total
          (initSh S secb (uIdx * S.N_recv + jIdx) pk sk)
        pure (chOf pk r.2, (pk, sk, sIdx, r.2)))
  findCollision st ss ct :=
    match st with
    | (pk, sk, _, .done _ h) =>
      extractCollidingKemCtPrim b.q_total pk sk pk ct ss h.recvKemRecs
    | (pk, sk, _, .paused _ d h c) => do
      let x ← postKemAuthPrim S d.1 d.2.1 d.2.2.1 d.2.2.2.1 d.2.2.2.2 h ss ct
      let y ← runWithFuelPrim false (postImpl1Key S) (c x.1) b.q_total x.2
      extractCollidingKemCtPrim b.q_total pk sk d.2.1.pqspkB ct ss y.2.recvKemRecs
  q_prim := primQueryBudget S b

theorem midAdv1Key_kemShCrExp_eq_core (P : Primitives) (S : Setup) (b : QueryBudget)
    (A : AuthAdversary S) :
    KemShCr P (shcrReductionAuthCore1Key S b A) = KemShCr P (shcrAuth1KeyMidAdv S b A) := by
  refine kemShCr_eq_of_choosePk_spk_send P S
    (shcrReductionAuthCore1Key S b A) (shcrAuth1KeyMidAdv S b A)
    Fcore (fun bIdx sIdx pk sk => do
      let secb ← embedUnif ($ᵗ Bool)
      let r ← stepUntilPauseFuel false (stepMid1Key S sIdx) A.run b.q_total
        (initSh S secb bIdx pk sk)
      pure (chOf pk r.2, (pk, sk, sIdx, r.2))) ?_ ?_ ?_
  · intro pk sk
    simp only [shcrReductionAuthCore1Key, choosePkAuthPrimAt1Key, map_eq_bind_pure_comp,
      bind_assoc, Function.comp_def, pure_bind]
    refine bind_congr fun idx => bind_congr fun secb => ?_
    rw [stepUntilShCr1Key_eq]
    simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
    refine bind_congr fun r => ?_
    rcases r with ⟨c, _ | _⟩ <;> rfl
  · intro pk sk
    rfl
  · rintro ⟨pk, sk, sIdx, r⟩ ss ct
    rcases r with ⟨a, h⟩ | ⟨q, d, h, c⟩
    · simp [shcrReductionAuthCore1Key, shcrAuth1KeyMidAdv, Fcore, Gsh, findCollisionAuthPrim1Key,
        chOf]
    · simp only [shcrReductionAuthCore1Key, shcrAuth1KeyMidAdv, Fcore, Gsh,
        findCollisionAuthPrim1Key, resumePausedAuthPrim1Key, toPaused, chOf, bind_assoc]
      refine bind_congr fun x => ?_
      rw [runWithFuelShCr1Key_eq]

theorem stepMid1Key_inv (S : Setup) (pk sk : Bytes) (n sIdx : Nat) (q : AuthQuery S)
    (h : AuthShCrState S) (hI : ShInv pk sk n h) :
    HoldsOnLeaves (PreStepInvC (ShInv pk sk) (fun d : PauseMid S => d.2.1.pqspkB) n)
      (stepMid1Key S sIdx q h) := by
  unfold stepMid1Key
  refine HoldsOnLeaves.bind_const _ fun o => ?_
  rcases o with _ | d
  · exact HoldsOnLeaves.map _ (pqxdhAuthShCrPrimImpl1Key_inv S pk sk n q h hI) fun x hx => hx
  · exact HoldsOnLeaves.pure ⟨rfl, hI⟩

theorem preStep1Key_eq (S : Setup) (K n : Nat) (q : AuthQuery S) (h : AuthShCrState S)
    (sIdx : Nat) (chosen : Bytes) (hB : AuthBaseListsBounded n h.base) (hn : n + 1 ≤ K) :
    (do
      match ← (shcrReductionAuthProg1Key S K K).handlePre.eval
          (.cons (shcrStToVal sIdx chosen h) (.cons ((authCodec S).qenc q) .nil)) with
      | .inl (rVal, st') => pure (.inl ((authCodec S).rdec q rVal, st'))
      | .inr (ch1Val, (pVal, st')) => pure (.inr (ch1Val, (pVal, st')))) =
      Sum.map (Prod.map id (shcrStToVal sIdx chosen))
        (Prod.map id (Prod.map pauseToVal (shcrStToVal sIdx chosen))) <$>
          stepMid1Key S sIdx q h := by
  have hr : ∀ x, valToAuthResp (authRespToVal x) = x := valToAuthResp_authRespToVal
  change (do
      match ← (shcrReductionAuthProg1Key S K K).handlePre.eval
          (.cons (shcrStToVal sIdx chosen h) (.cons (authQueryToVal q) .nil)) with
      | .inl (rVal, st') => pure (.inl (valToAuthResp rVal, st'))
      | .inr (ch1Val, (pVal, st')) => pure (.inr (ch1Val, (pVal, st'))) :
      OracleComp PrimBaseSpec (((authSpec S).Range q × shcrStTy.denote) ⊕
        (Bytes × (pauseTy.denote × shcrStTy.denote)))) = _
  rw [shcrPre1KeyC_eval S K K n q h sIdx chosen hB hn]
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

theorem postStep1Key_eq (S : Setup) (K n : Nat) (q : AuthQuery S) (h : AuthShCrState S)
    (sIdx : Nat) (chosen : Bytes) (hB : AuthBaseListsBounded n h.base) (hn : n + 1 ≤ K) :
    (do
      let p ← (shcrReductionAuthProg1Key S K K).handlePost.eval
          (.cons (shcrStToVal sIdx chosen h) (.cons ((authCodec S).qenc q) .nil))
      return ((authCodec S).rdec q p.1, p.2)) =
      Prod.map id (shcrStToVal sIdx chosen) <$> postImpl1Key S q h := by
  have hr : ∀ x, valToAuthResp (authRespToVal x) = x := valToAuthResp_authRespToVal
  change (do
      let p ← (shcrReductionAuthProg1Key S K K).handlePost.eval
          (.cons (shcrStToVal sIdx chosen h) (.cons (authQueryToVal q) .nil))
      return (valToAuthResp p.1, p.2) :
      OracleComp PrimBaseSpec ((authSpec S).Range q × shcrStTy.denote)) = _
  dsimp only [shcrReductionAuthProg1Key, authCodec]
  rw [shcrPost1KeyC_eval S K n _ _ _ q h sIdx chosen (by simp) (by simp) hB hn]
  refine (bind_map_left _ _ _).trans ?_
  rw [map_eq_bind_pure_comp]
  refine bind_congr fun x => ?_
  show (pure (valToAuthResp (authRespToVal x.1), shcrStToVal sIdx chosen x.2) :
      OracleComp PrimBaseSpec ((authSpec S).Range q × shcrStTy.denote)) =
    pure (x.1, shcrStToVal sIdx chosen x.2)
  rw [hr]

/-- Maps a mid-level `MidSt` state to the corresponding `shcrAuth1KeyDslAdv` state. -/
def Fdsl1Key (S : Setup) (b : QueryBudget) (A : AuthAdversary S) :
    MidSt S → (shcrAuth1KeyDslAdv S b A).State
  | (pk, _, sIdx, .done a h) => .done a (shcrStToVal sIdx pk h)
  | (pk, _, sIdx, .paused q d h k) =>
    .paused q d.2.1.pqspkB (pauseToVal d) (shcrStToVal sIdx pk h) k

theorem dslAdv1Key_kemShCrExp_eq_mid (P : Primitives) (S : Setup) (b : QueryBudget)
    (A : AuthAdversary S)
    (hA : IsQueryBoundP A.run (fun q : ℕ ⊕ AuthQuery S => q.isRight = true) b.q_total) :
    kemShCrExp P (shcrAuth1KeyDslAdv S b A) = kemShCrExp P (shcrAuth1KeyMidAdv S b A) := by
  have hr : ∀ x, valToAuthResp (authRespToVal x) = x := valToAuthResp_authRespToVal
  have hMono : ∀ {pk sk : Bytes} {n m : Nat} {st : AuthShCrState S}, n ≤ m →
      ShInv pk sk n st → ShInv pk sk m st := fun hnm hI => hI.mono hnm
  have hL : ∀ (pk sk : Bytes) (sIdx bIdx : Nat) (secb : Bool),
      HoldsOnLeaves (Stage1InvC (ShInv pk sk) (fun d : PauseMid S => d.2.1.pqspkB) b.q_total)
        (stepUntilPauseFuel false (stepMid1Key S sIdx) A.run b.q_total (initSh S secb bIdx pk sk)) :=
    fun pk sk sIdx bIdx secb =>
      (stepUntilPauseFuel_map_boundedC false id id (ShInv pk sk)
        (fun d : PauseMid S => d.2.1.pqspkB)
        hMono (stepMid1Key S sIdx) (stepMid1Key S sIdx) b.q_total (fun _ _ _ _ _ => by simp)
        (fun n q st hI => stepMid1Key_inv S pk sk n sIdx q st hI) A.run b.q_total hA b.q_total 0
        (initSh S secb bIdx pk sk) ⟨authBaseListsBounded_empty S secb, rfl, rfl⟩ (by omega)).1
  refine kemShCrExp_congr P (shcrAuth1KeyMidAdv S b A) (shcrAuth1KeyDslAdv S b A) (MidInv b.q_total)
    (Fdsl1Key S b A) ?_ ?_ ?_
  · intro pk sk
    simp only [shcrAuth1KeyDslAdv, shcrAuth1KeyMidAdv, TwoStageCostedReduction.eval1]
    rw [show (shcrReductionAuthProg1Key S b.q_total b.q_total).init =
      (shcrReductionAuthProg S b.q_total b.q_total).init from rfl, shcrInit_eval]
    split_ifs with h0
    · simp only [bind_assoc, pure_bind, map_bind]
      refine bind_congr fun secb => ?_
      rw [GRed2_run1_eq_stepUntilPauseFuel (shcrReductionAuthProg1Key S b.q_total b.q_total) false []]
      simp only [bind_map_left]
      refine (congrArg (fun x => x >>= _)
        (stepUntilPauseFuel_map_boundedC false pauseToVal (shcrStToVal 0 pk)
        (ShInv pk sk) (fun d : PauseMid S => d.2.1.pqspkB) hMono (stepMid1Key S 0) _
        b.q_total ?hstep0 (fun n q st hI => stepMid1Key_inv S pk sk n _ q st hI) A.run b.q_total hA
        b.q_total 0 (initSh S secb 0 pk sk)
        ⟨authBaseListsBounded_empty S secb, rfl, rfl⟩ (by omega)).2).trans ?_
      case hstep0 =>
        intro n q st hn hI
        refine (bind_congr fun x => ?_).trans
          (preStep1Key_eq S b.q_total n q st 0 pk hI.bnd hn)
        rcases x with ⟨v, s'⟩ | ⟨c, p, s'⟩ <;> rfl
      · refine (bind_map_left _ _ _).trans ?_
        refine (hL pk sk _ _ secb).bind_congr _ _ fun x hx => ?_
        rcases x with ⟨c, ⟨a, h⟩ | ⟨q, d, h, k⟩⟩
        · obtain ⟨rfl, hI⟩ := hx
          simp [RedProg2State.mapSt, midOfStepUntilPause, Fdsl1Key, chOf,
            shcrReductionAuthProg1Key, shcrReductionAuthProg,
            Comp.eval, Expr.eval, scTPk, shcrStToVal, hI.tpk]
        · obtain ⟨rfl, -⟩ := hx
          simp only [RedProg2State.mapSt, midOfStepUntilPause, Option.getD_some, Fdsl1Key, chOf,
            Prod.map, id, map_pure]
    · simp only [bind_assoc, pure_bind, map_bind]
      refine bind_congr fun uIdx => bind_congr fun jIdx => bind_congr fun sIdx =>
        bind_congr fun secb => ?_
      rw [GRed2_run1_eq_stepUntilPauseFuel (shcrReductionAuthProg1Key S b.q_total b.q_total) false []]
      simp only [bind_map_left]
      refine (congrArg (fun x => x >>= _)
        (stepUntilPauseFuel_map_boundedC false pauseToVal (shcrStToVal sIdx pk)
        (ShInv pk sk) (fun d : PauseMid S => d.2.1.pqspkB) hMono (stepMid1Key S sIdx) _
        b.q_total ?hstep1 (fun n q st hI => stepMid1Key_inv S pk sk n _ q st hI) A.run b.q_total hA
        b.q_total 0 (initSh S secb (uIdx * S.N_recv + jIdx) pk sk)
        ⟨authBaseListsBounded_empty S secb, rfl, rfl⟩ (by omega)).2).trans ?_
      case hstep1 =>
        intro n q st hn hI
        refine (bind_congr fun x => ?_).trans
          (preStep1Key_eq S b.q_total n q st sIdx pk hI.bnd hn)
        rcases x with ⟨v, s'⟩ | ⟨c, p, s'⟩ <;> rfl
      · refine (bind_map_left _ _ _).trans ?_
        refine (hL pk sk _ _ secb).bind_congr _ _ fun x hx => ?_
        rcases x with ⟨c, ⟨a, h⟩ | ⟨q, d, h, k⟩⟩
        · obtain ⟨rfl, hI⟩ := hx
          simp [RedProg2State.mapSt, midOfStepUntilPause, Fdsl1Key, chOf,
            shcrReductionAuthProg1Key, shcrReductionAuthProg,
            Comp.eval, Expr.eval, scTPk, shcrStToVal, hI.tpk]
        · obtain ⟨rfl, -⟩ := hx
          simp only [RedProg2State.mapSt, midOfStepUntilPause, Option.getD_some, Fdsl1Key, chOf,
            Prod.map, id, map_pure]
  · intro pk sk
    simp only [shcrAuth1KeyMidAdv]
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
    · simp only [shcrAuth1KeyDslAdv, shcrAuth1KeyMidAdv, TwoStageCostedReduction.eval2,
        Fdsl1Key, pure_bind]
      rw [show (shcrReductionAuthProg1Key S b.q_total b.q_total).finish =
        (shcrReductionAuthProg S b.q_total b.q_total).finish from rfl, shcrFinish_eval]
      simp only [MidInv] at hI
      rw [hI.tpk, hI.tsk]
    · obtain ⟨n, rr, hI, hb, hc⟩ := hI
      simp only [shcrAuth1KeyDslAdv, shcrAuth1KeyMidAdv, TwoStageCostedReduction.eval2, Fdsl1Key]
      refine (congrArg (fun x => x >>= _)
        (shcrResume_eval S b.q_total b.q_total d h sIdx pk ss ct (hI.bnd.mono (by omega)))).trans ?_
      refine (bind_map_left _ _ _).trans ?_
      refine (postKemAuthPrim_inv S pk sk n d h ss ct hI).bind_congr _ _ fun x hx => ?_
      simp only [encSCS]
      have hDec : (authCodec S).rdec q (authRespToVal x.1) = x.1 := hr x.1
      rw [hDec, runFuel_pqPrimIface_eq_runWithFuelPrim]
      refine (congrArg (fun x => x >>= _)
        (runWithFuelPrim_map_boundedC false (shcrStToVal sIdx d.2.1.pqspkB) (ShInv pk sk) hMono
        (postImpl1Key S) _ b.q_total ?hstep
        (fun n q st hI => pqxdhAuthShCrPrimImpl1Key_inv S pk sk n q st hI)
        (c x.1) rr (hc x.1) b.q_total (n + 1) x.2 hx (by omega)).2).trans ?_
      case hstep =>
        intro n q st hn hI
        exact postStep1Key_eq S b.q_total n q st _ _ hI.bnd hn
      · refine (bind_map_left _ _ _).trans ?_
        refine (runWithFuelPrim_map_boundedC false id (ShInv pk sk) hMono
          (postImpl1Key S) (postImpl1Key S)
          b.q_total (fun _ _ _ _ _ => by simp)
          (fun n q st hI => pqxdhAuthShCrPrimImpl1Key_inv S pk sk n q st hI)
          (c x.1) rr (hc x.1) b.q_total (n + 1) x.2 hx (by omega)).1.bind_congr _ _ fun y hy => ?_
        dsimp only [Prod.map, id]
        rw [show (shcrReductionAuthProg1Key S b.q_total b.q_total).finish =
          (shcrReductionAuthProg S b.q_total b.q_total).finish from rfl,
          shcrFinish_eval S b.q_total b.q_total _ y.2 sIdx d.2.1.pqspkB ss ct, hy.tpk, hy.tsk]

/-- The one-key `ReductionDsl` adversary `shcrAuth1KeyDslAdv` and the shallow
    `shcrReductionAuth1Key` have equal `KemShCr` advantage. -/
theorem shcrAuth1KeyDslAdv_kemShCr_eq (P : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    KemShCr P (shcrAuth1KeyDslAdv S b A.1) = KemShCr P (shcrReductionAuth1Key S b A) := by
  have hA : IsQueryBoundP A.1.run (fun q : ℕ ⊕ AuthQuery S => q.isRight = true) b.q_total := by
    have h := SignalPqxdh.QueryBounded.auth_total A.2
    convert h using 1; funext q; cases q <;> rfl
  have hDslMid : KemShCr P (shcrAuth1KeyDslAdv S b A.1) =
      KemShCr P (shcrAuth1KeyMidAdv S b A.1) := by
    unfold KemShCr
    rw [dslAdv1Key_kemShCrExp_eq_mid P S b A.1 hA]
  rw [hDslMid, ← midAdv1Key_kemShCrExp_eq_core]
  rfl

theorem shcrAuth1KeyDslAdv_kemShCrExp_eq (P : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    𝒟[kemShCrExp P (shcrAuth1KeyDslAdv S b A.1)] {true} =
      𝒟[kemShCrExp P (shcrReductionAuth1Key S b A)] {true} :=
  shcrAuth1KeyDslAdv_kemShCr_eq P S b A

end SignalPqxdh.Security.ReductionDsl.AuthHs
