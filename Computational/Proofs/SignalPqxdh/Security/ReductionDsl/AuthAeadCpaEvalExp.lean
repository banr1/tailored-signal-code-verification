/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthAeadCpaMid
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthAeadCpaEval
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthAeadCpaLeaves
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthAeadCpaSend
import VCVio.EvalDist.Monad.Basic

/-!
# `aeadCpaRedProg` Experiment Equality

Evaluates the outer components of `aeadCpaRedProg`, defines the `ReductionDsl` adversary
`aeadCpaDslAdv`, and proves that its `aeadIndCpaExp` experiment and `AeadIndCpa` advantage match
the shallow reduction `aeadCpaReductionAuthFixed`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthAead

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl SignalPqxdh.Security.ReductionDsl.AuthPrf
open OracleSpec OracleComp RoKem

theorem cpaFinish_eval (S : Setup) (K idx : Nat) (c? : Option Bytes) (b' : Bool)
    (hst : AuthHybridStateFixed S) (hB : AuthListsBounded K hst) :
    (aeadCpaRedProg S K).finish.eval (.cons (cpaStToVal idx hst) (.cons b' (.cons c? .nil))) =
      AuthSubHops1to3.finalizeAuthFixedPrim S true b' hst.toAuthHybridState := by
  dsimp only [aeadCpaRedProg, authCodec]
  simp only [cpaFinishC, letV_eval]
  exact finalizeAuthFixedDsl_eval S K true b' hst.toAuthHybridState _ hB.toAuthHybridListsBounded

theorem cpaInit_slot_eval (S : Setup) (K : Nat) :
    (aeadCpaRedProg S K).init.eval (.cons () .nil) =
      (do
        let idx ← embedUnif (sampleIndexRange (min K S.N_send_tot))
        pure ((), cpaSlotStToVal idx (0, AuthHybridStateFixed.empty S true))) := by
  simp only [aeadCpaRedProg, cpaInitC, bindV, Comp.eval, samplePrim_index_eval]
  rfl

theorem cpaPostStep_slot_eq (S : Setup) (K n idx : Nat) (q : AuthQuery S)
    (shst : CpaSlotSt S) (hI : CpaSlotInv n shst) (hn : n + 1 ≤ K) :
    (do
      let p ← (aeadCpaRedProg S K).handlePost.eval
          (.cons (cpaSlotStToVal idx shst) (.cons ((authCodec S).qenc q) .nil))
      return ((authCodec S).rdec q p.1, p.2) :
      OracleComp PrimBaseSpec ((authSpec S).Range q × cpaStTy.denote)) =
      Prod.map id (cpaSlotStToVal idx) <$> cpaStepCutoffSlotPrim idx S q shst := by
  have hr : ∀ x, valToAuthResp (authRespToVal x) = x := valToAuthResp_authRespToVal
  dsimp only [aeadCpaRedProg, authCodec, cpaPostC]
  rw [bindV_eval]
  erw [cpaStepC_slot_eval S K false idx n q shst hI hn, stepCpaSlotGen_false]
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
  refine bind_congr fun x => ?_
  show (pure (valToAuthResp (authRespToVal x.1), cpaSlotStToVal idx x.2) :
      OracleComp PrimBaseSpec ((authSpec S).Range q × cpaStTy.denote)) =
    pure (x.1, cpaSlotStToVal idx x.2)
  rw [hr]

theorem cpaResume_slot_eval (S : Setup) (K idx : Nat) (c? : Option Bytes)
    (p : AuthCpaPausePayload S) (shst : CpaSlotSt S) :
    (aeadCpaRedProg S K).resume.eval
        (.cons (cpaSlotStToVal idx shst) (.cons (cpaPayloadToVal p) (.cons c? .nil))) =
      pure (authRespToVal (finishAuthCpaSendFixedPure true true p (c?.getD []) shst.2).1,
        cpaSlotStToVal idx
          (idx + 1, (finishAuthCpaSendFixedPure true true p (c?.getD []) shst.2).2)) := by
  dsimp only [aeadCpaRedProg, authCodec]
  simp only [cpaResumeC, letV_eval, bindV_eval]
  rw [finishCpaC_eval S _ _ _ _ _ _ shst.2 p rfl rfl]
  rcases c? with _ | c <;> rfl

theorem cpaFinish_slot_eval (S : Setup) (K idx : Nat) (c? : Option Bytes) (b' : Bool)
    (shst : CpaSlotSt S) (hB : AuthListsBounded K shst.2) :
    (aeadCpaRedProg S K).finish.eval
        (.cons (cpaSlotStToVal idx shst) (.cons b' (.cons c? .nil))) =
      AuthSubHops1to3.finalizeAuthFixedPrim S true b' shst.2.toAuthHybridState := by
  dsimp only [aeadCpaRedProg, authCodec]
  simp only [cpaFinishC, letV_eval]
  exact finalizeAuthFixedDsl_eval S K true b' shst.2.toAuthHybridState _
    hB.toAuthHybridListsBounded

/-- The `AeadIndCpa` adversary obtained by running `aeadCpaRedProg` with capacity and fuel
    `b.q_total`. -/
def aeadCpaDslAdv (S : Setup) (b : QueryBudget) (A : AuthAdversary S) : AeadIndCpaAdv where
  State := Mid (authSpec S) Bool (aeadCpaRedProg S b.q_total).π.denote
    (aeadCpaRedProg S b.q_total).σ.denote cpaChOutTy.denote
  choose := do
    let r ← (aeadCpaRedProg S b.q_total).eval1 (fun _ => A.run) () b.q_total false
    pure (r.1.1, r.1.2.1, r.1.2.2, r.2)
  dist st c? := (aeadCpaRedProg S b.q_total).eval2 st c? b.q_total false
  q_prim := primQueryBudget S b

abbrev CpaMid (S : Setup) :=
  Nat × (Option (Bytes × Bytes × Bytes) ×
    RedProg2State (authSpec S) Bool (AuthCpaPausePayload S) (AuthHybridStateFixed S))

def cpaOutA {S : Setup} : AuthCpaPauseResult S Bool → Bytes × Bytes × Bytes
  | .paused ad m0 m1 _ _ _ => if m0.length == m1.length then (ad, m0, m1) else ([], [0], [0])
  | .done _ _ => ([], [0], [0])

def FcpaA {S : Setup} (x : CpaMid S) : Bytes × Bytes × Bytes × (Nat × AuthCpaPauseResult S Bool) :=
  ((cpaOutA (Gcpa x.2)).1, (cpaOutA (Gcpa x.2)).2.1, (cpaOutA (Gcpa x.2)).2.2, (x.1, Gcpa x.2))

def FcpaB (S : Setup) (b : QueryBudget) (A : AuthAdversary S) (x : CpaMid S) :
    Bytes × Bytes × Bytes × (aeadCpaDslAdv S b A).State :=
  ((x.2.1.getD ([], [0], [0])).1, (x.2.1.getD ([], [0], [0])).2.1,
    (x.2.1.getD ([], [0], [0])).2.2,
    midOfStepUntilPause ([], ([0], [0]))
      (x.2.1, x.2.2.mapSt cpaPayloadToVal (cpaStToVal x.1)))

abbrev CpaSlotMid (S : Setup) :=
  Nat × (Option (Bytes × Bytes × Bytes) ×
    RedProg2State (authSpec S) Bool (AuthCpaPausePayload S) (CpaSlotSt S))

def cpaSlotOutA {S : Setup} : CpaSlotPauseRes S Bool → Bytes × Bytes × Bytes
  | .paused ad m0 m1 _ _ _ => if m0.length == m1.length then (ad, m0, m1) else ([], [0], [0])
  | .done _ _ => ([], [0], [0])

def FcpaSlotA {S : Setup} (x : CpaSlotMid S) :
    Bytes × Bytes × Bytes × (Nat × CpaSlotPauseRes S Bool) :=
  ((cpaSlotOutA (GcpaSlot x.2)).1, (cpaSlotOutA (GcpaSlot x.2)).2.1,
    (cpaSlotOutA (GcpaSlot x.2)).2.2, (x.1, GcpaSlot x.2))

def FcpaSlotB (S : Setup) (b : QueryBudget) (A : AuthAdversary S) (x : CpaSlotMid S) :
    Bytes × Bytes × Bytes × (aeadCpaDslAdv S b A).State :=
  ((x.2.1.getD ([], [0], [0])).1, (x.2.1.getD ([], [0], [0])).2.1,
    (x.2.1.getD ([], [0], [0])).2.2,
    midOfStepUntilPause ([], ([0], [0]))
      (x.2.1, x.2.2.mapSt cpaPayloadToVal (cpaSlotStToVal x.1)))

theorem aeadCpaDslAdv_aeadIndCpaExp_slot_eq_core (P : Primitives) (S : Setup) (b : QueryBudget)
    (A : AuthAdversary S)
    (hA : IsQueryBoundP A.run (fun q : ℕ ⊕ AuthQuery S => q.isRight = true) b.q_total) :
    aeadIndCpaExp P (aeadCpaDslAdv S b A) =
      aeadIndCpaExp P (cpaReductionAuthSlot S b A) := by
  have hr : ∀ x, valToAuthResp (authRespToVal x) = x := valToAuthResp_authRespToVal
  have hMono : ∀ {n m : Nat} {st : CpaSlotSt S}, n ≤ m → CpaSlotInv n st → CpaSlotInv m st :=
    fun hnm hI => hI.mono hnm
  have hL : ∀ idx : Nat,
      HoldsOnLeaves (Stage1InvP (fun n sh => CpaSlotInv n sh) (CpaSlotPI S idx) b.q_total)
        (stepUntilPauseFuel false (stepMidCpaSlot S idx) A.run b.q_total
          (0, AuthHybridStateFixed.empty S true)) :=
    fun idx =>
      (stepUntilPauseFuel_map_boundedP false id id (fun n sh => CpaSlotInv n sh) (CpaSlotPI S idx)
        hMono (stepMidCpaSlot S idx) (stepMidCpaSlot S idx) b.q_total (fun _ _ _ _ _ => by simp)
        (fun n q st hI => stepMidCpaSlot_leaves S idx n q st hI) A.run b.q_total hA b.q_total 0
        (0, AuthHybridStateFixed.empty S true) (cpaSlotInv_empty S) (by omega)).1
  let m : OracleComp PrimBaseSpec (CpaSlotMid S) := do
    let idx ← embedUnif (sampleIndexRange (min b.q_total S.N_send_tot))
    let r ← stepUntilPauseFuel false (stepMidCpaSlot S idx) A.run b.q_total
      (0, AuthHybridStateFixed.empty S true)
    pure (idx, r)
  refine aeadIndCpaExp_congr P (cpaReductionAuthSlot S b A) (aeadCpaDslAdv S b A) m
    (fun x => Stage1InvP (fun n sh => CpaSlotInv n sh) (CpaSlotPI S x.1) b.q_total x.2) ?_ FcpaSlotA
    (FcpaSlotB S b A) ?_ ?_ ?_ ?_
  · refine HoldsOnLeaves.bind_const _ fun idx => ?_
    exact HoldsOnLeaves.bind (hL idx) fun x hx => HoldsOnLeaves.pure hx
  · dsimp only [cpaReductionAuthSlot, cpaReductionAuthSlotChoose, cpaReductionAuthSlotAtChoose, m]
    simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
    refine bind_congr fun idx => ?_
    rw [stepUntilCpaSlot_eq]
    simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
    refine bind_congr fun r => ?_
    rcases r with ⟨_ | c, ⟨a, sh⟩ | ⟨q, p, sh, k⟩⟩ <;>
      simp only [GcpaSlot, FcpaSlotA, cpaSlotOutA] <;> (try split) <;> rfl
  · show (do
        let r ← (aeadCpaRedProg S b.q_total).eval1 (fun _ => A.run) () b.q_total false
        pure (r.1.1, r.1.2.1, r.1.2.2, r.2)) = _
    simp only [TwoStageCostedReduction.eval1, m]
    erw [cpaInit_slot_eval]
    simp only [bind_assoc, pure_bind, map_bind]
    refine bind_congr fun idx => ?_
    erw [GRed2_run1_eq_stepUntilPauseFuel (aeadCpaRedProg S b.q_total) false ([], ([0], [0]))]
    simp only [bind_map_left]
    refine (congrArg (fun x => x >>= _)
      (stepUntilPauseFuel_map_boundedP false cpaPayloadToVal (cpaSlotStToVal idx)
        (fun n sh => CpaSlotInv n sh) (CpaSlotPI S idx) hMono (stepMidCpaSlot S idx) _ b.q_total
        ?hstep (fun n q st hI => stepMidCpaSlot_leaves S idx n q st hI) A.run b.q_total hA
        b.q_total 0 (0, AuthHybridStateFixed.empty S true) (cpaSlotInv_empty S)
        (by omega)).2).trans ?_
    case hstep =>
      intro n q st hn hI
      dsimp only [aeadCpaRedProg, authCodec, cpaPreC]
      erw [cpaStepC_slot_eval S _ true idx n q st hI hn, stepCpaSlotGen_true]
      refine (bind_map_left _ _ _).trans ?_
      rw [map_eq_bind_pure_comp]
      refine bind_congr fun x => ?_
      rcases x with ⟨r, sh'⟩ | ⟨c, p, sh'⟩
      · show (pure (Sum.inl (valToAuthResp (authRespToVal r), cpaSlotStToVal idx sh')) :
            OracleComp PrimBaseSpec (((authSpec S).Range q × cpaStTy.denote) ⊕
              ((Bytes × Bytes × Bytes) × (cpaPayloadTy.denote × cpaStTy.denote)))) =
          pure (Sum.inl (r, cpaSlotStToVal idx sh'))
        rw [hr]
      · rfl
    · refine (bind_map_left _ _ _).trans ?_
      refine (hL idx).bind_congr _ _ fun x hx => ?_
      rcases x with ⟨c, ⟨a, sh⟩ | ⟨q, p, sh, k⟩⟩
      · obtain ⟨rfl, -⟩ := hx
        rfl
      · obtain ⟨c', n, rr, rfl, -⟩ := hx
        rfl
  · rintro ⟨idx, c, r⟩ hx
    rcases r with ⟨a, sh⟩ | ⟨q, p, sh, k⟩
    · obtain ⟨rfl, -⟩ := hx
      exact ⟨rfl, rfl, rfl⟩
    · obtain ⟨⟨c1, c2, c3⟩, n, rr, rfl, hP, -, -⟩ := hx
      have h1 : c1 = p.ad := hP.pause.ad_eq
      have h2 : c2 = p.m0 := hP.pause.m0_eq
      have h3 : c3 = p.m1 := hP.pause.m1_eq
      have hl : (c2.length == c3.length) = true := by
        rw [h2, h3, hP.pause.len_eq]; exact beq_self_eq_true _
      simp only [FcpaSlotB, FcpaSlotA, GcpaSlot, cpaSlotOutA, hl, ite_true, Option.getD_some]
      exact ⟨trivial, trivial, trivial⟩
  · rintro ⟨idx, c, r⟩ hx c?
    rcases r with ⟨a, sh⟩ | ⟨q, p, sh, k⟩
    · obtain ⟨rfl, hI⟩ := hx
      simp only [aeadCpaDslAdv, cpaReductionAuthSlot, FcpaSlotA, FcpaSlotB, GcpaSlot,
        cpaReductionAuthSlotDist]
      simp only [TwoStageCostedReduction.eval2, midOfStepUntilPause, RedProg2State.mapSt,
        cpaResumeAfterChallengeSlotPrim, pure_bind]
      erw [cpaFinish_slot_eval S _ idx c? a sh hI.inv.bnd,
        finalizeAuthFixedPrim_true_eq S a _ hI.inv.won]
    · obtain ⟨⟨c1, c2, c3⟩, n, rr, rfl, hP, hb, hc⟩ := hx
      simp only [aeadCpaDslAdv, cpaReductionAuthSlot, FcpaSlotA, FcpaSlotB, GcpaSlot,
        cpaReductionAuthSlotDist]
      simp only [TwoStageCostedReduction.eval2, midOfStepUntilPause, RedProg2State.mapSt,
        cpaResumeAfterChallengeSlotPrim]
      erw [cpaResume_slot_eval]
      have hIdxLe : idx + 1 ≤ n + 1 := by
        have hEq : sh.1 = idx := hP.slot_eq
        have hLe : sh.1 ≤ n := hP.slot_le
        omega
      have hI' := finishAuthCpaSendFixedPure_slot_inv S n (idx + 1) true true p (c?.getD []) sh.2
        hP.pause.inv hP.ideal_le hIdxLe hP.pause.ro_le hP.pause.root_le
      rcases hfin : finishAuthCpaSendFixedPure true true p (c?.getD []) sh.2 with ⟨resp, h'⟩
      rw [hfin] at hI'
      refine (pure_bind _ _).trans ?_
      erw [runFuel_pqPrimIface_eq_runWithFuelPrim,
        show (authCodec S).rdec q (authRespToVal resp) = resp from hr resp]
      rw [runWithPrimStepFuelSlot_eq]
      refine (congrArg (fun x => x >>= _)
        (runWithFuelPrim_map_boundedP false (cpaSlotStToVal idx) (fun n sh => CpaSlotInv n sh)
          hMono (cpaStepCutoffSlotPrim idx S) _ b.q_total ?hstep
          (fun n q st hI => (cpaStepCutoffSlotPrim_leaves S idx n q st hI).toHoldsOnLeaves)
          (k resp) rr (hc resp) b.q_total (n + 1) (idx + 1, h') hI' (by omega)).2).trans ?_
      case hstep =>
        intro n q st hn hI
        exact cpaPostStep_slot_eq S b.q_total n idx q st hI hn
      · refine (bind_map_left _ _ _).trans ?_
        refine (runWithFuelPrim_map_boundedP false id (fun n sh => CpaSlotInv n sh) hMono
          (cpaStepCutoffSlotPrim idx S) (cpaStepCutoffSlotPrim idx S) b.q_total
          (fun _ _ _ _ _ => by simp)
          (fun n q st hI => (cpaStepCutoffSlotPrim_leaves S idx n q st hI).toHoldsOnLeaves)
          (k resp) rr (hc resp) b.q_total (n + 1) (idx + 1, h') hI' (by omega)).1.bind_congr _ _
          fun y hy => ?_
        obtain ⟨b', fs⟩ := y
        erw [cpaFinish_slot_eval S _ idx c? b' fs hy.inv.bnd,
          finalizeAuthFixedPrim_true_eq S b' _ hy.inv.won]

private def GcpaSlotExt {S : Setup} :
    Option (Bytes × Bytes × Bytes) ×
      RedProg2State (authSpec S) Bool (AuthCpaPausePayload S) (CpaSlotSt S) →
    AuthCpaSlotPauseResult S Bool
  | (_, .done a sh) => .done a sh
  | (some c, .paused _ p sh k) => .paused c.1 c.2.1 c.2.2 p sh k
  | (none, .paused _ p sh k) => .paused p.ad p.m0 p.m1 p sh k

private theorem stepUntilAuthCpaChallengeSlotPrim_eq (S : Setup) (idx : Nat)
    (mx : OracleComp (unifSpec + authSpec S) Bool) (fuel : Nat) (shst : CpaSlotSt S) :
    stepUntilAuthCpaChallengeSlotPrim idx S false mx fuel shst =
      GcpaSlotExt <$> stepUntilPauseFuel false (stepMidCpaSlot S idx) mx fuel shst := by
  refine stepUntilPauseFuel_char false (stepMidCpaSlot S idx) GcpaSlotExt
    (fun mx fuel sh => stepUntilAuthCpaChallengeSlotPrim idx S false mx fuel sh) ?_ ?_ ?_ ?_
    mx fuel shst
  · intro a fuel s; rfl
  · intro uq k fuel s
    simp only [stepUntilAuthCpaChallengeSlotPrim]
    rw [OracleComp.construct_query_bind]
    rfl
  · intro gq k s
    simp only [stepUntilAuthCpaChallengeSlotPrim]
    rw [OracleComp.construct_query_bind]
    rfl
  · intro gq k fuel s
    simp only [stepUntilAuthCpaChallengeSlotPrim]
    rw [OracleComp.construct_query_bind]
    cases gq
    case sendOPK u i b m0 m1 =>
      simp only [stepMidCpaSlot, cpaSendSlotShOpk]
      split
      · simp only [map_pure, pure_bind]; rfl
      · rw [bind_map_left]
        change (tryPauseAuthCpaSendSlotPrim true idx S (.sendOPK u i) u b m0 m1 s >>= _) =
          (tryPauseAuthCpaSendSlotPrim true idx S (.sendOPK u i) u b m0 m1 s >>= _)
        refine bind_congr fun x => ?_
        rcases x with ⟨r, sh⟩ | ⟨ad, m0', m1', p, sh⟩ <;> rfl
    case sendNoOPK u i b m0 m1 =>
      simp only [stepMidCpaSlot, cpaSendSlotShNoOpk]
      split
      · simp only [map_pure, pure_bind]; rfl
      · rw [bind_map_left]
        change (tryPauseAuthCpaSendSlotPrim true idx S (.sendNoOPK u i) u b m0 m1 s >>= _) =
          (tryPauseAuthCpaSendSlotPrim true idx S (.sendNoOPK u i) u b m0 m1 s >>= _)
        refine bind_congr fun x => ?_
        rcases x with ⟨r, sh⟩ | ⟨ad, m0', m1', p, sh⟩ <;> rfl
    all_goals
      simp only [stepMidCpaSlot]
      rw [bind_map_left]

/-- The `ReductionDsl` `AeadIndCpa` reduction `aeadCpaRedProg` (run as `aeadCpaDslAdv`) and
    the shallow `aeadCpaReductionAuthFixed` have the same `AeadIndCpa` experiment. -/
theorem aeadCpaDslAdv_aeadIndCpaExp_eq (P : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    aeadIndCpaExp P (aeadCpaDslAdv S b A.1) =
      aeadIndCpaExp P (aeadCpaReductionAuthFixed S b A) := by
  have hA : IsQueryBoundP A.1.run (fun q : ℕ ⊕ AuthQuery S => q.isRight = true) b.q_total := by
    have h := SignalPqxdh.QueryBounded.auth_total A.2
    convert h using 1; funext q; cases q <;> rfl
  rw [aeadCpaDslAdv_aeadIndCpaExp_slot_eq_core P S b A.1 hA]
  let m : OracleComp PrimBaseSpec (CpaSlotMid S) := do
    let idx ← embedUnif (sampleIndexRange (min b.q_total S.N_send_tot))
    let r ← stepUntilPauseFuel false (stepMidCpaSlot S idx) A.1.run b.q_total
      (0, AuthHybridStateFixed.empty S true)
    pure (idx, r)
  let outExt : AuthCpaSlotPauseResult S Bool → Bytes × Bytes × Bytes
    | .paused ad m0 m1 _ _ _ => if m0.length == m1.length then (ad, m0, m1) else ([], [0], [0])
    | .done _ _ => ([], [0], [0])
  let FExt : CpaSlotMid S → Bytes × Bytes × Bytes × (Nat × AuthCpaSlotPauseResult S Bool) :=
    fun x => ((outExt (GcpaSlotExt x.2)).1, (outExt (GcpaSlotExt x.2)).2.1,
      (outExt (GcpaSlotExt x.2)).2.2, (x.1, GcpaSlotExt x.2))
  refine aeadIndCpaExp_congr P (aeadCpaReductionAuthFixed S b A) (cpaReductionAuthSlot S b A.1) m
    (fun _ => True) ?_ FExt FcpaSlotA ?_ ?_ ?_ ?_
  · refine HoldsOnLeaves.bind_const _ fun _ => ?_
    exact HoldsOnLeaves.bind_const _ fun _ => HoldsOnLeaves.pure trivial
  · dsimp only [aeadCpaReductionAuthFixed, aeadCpaReductionAuthSlotChoose,
      aeadCpaReductionAuthSlotAtChoose, m, outExt, FExt]
    simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
    refine bind_congr fun idx => ?_
    rw [stepUntilAuthCpaChallengeSlotPrim_eq]
    simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
    refine bind_congr fun r => ?_
    rcases r with ⟨_ | c, ⟨a, sh⟩ | ⟨q, p, sh, k⟩⟩ <;>
      simp only [GcpaSlotExt] <;> (try split) <;> rfl
  · dsimp only [cpaReductionAuthSlot, cpaReductionAuthSlotChoose, cpaReductionAuthSlotAtChoose, m]
    simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
    refine bind_congr fun idx => ?_
    rw [stepUntilCpaSlot_eq]
    simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
    refine bind_congr fun r => ?_
    rcases r with ⟨_ | c, ⟨a, sh⟩ | ⟨q, p, sh, k⟩⟩ <;>
      simp only [GcpaSlot, FcpaSlotA, cpaSlotOutA] <;> (try split) <;> rfl
  · rintro ⟨idx, _ | c, ⟨a, sh⟩ | ⟨q, p, sh, k⟩⟩ _ <;>
      simp only [FcpaSlotA, FExt, GcpaSlot, GcpaSlotExt, cpaSlotOutA, outExt] <;>
      exact ⟨trivial, trivial, trivial⟩
  · rintro ⟨idx, _ | c, ⟨a, sh⟩ | ⟨q, p, sh, k⟩⟩ _ c? <;> rfl

theorem aeadCpaDslAdv_aeadIndCpa_eq (P : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    AeadIndCpa P (aeadCpaDslAdv S b A.1) = AeadIndCpa P (aeadCpaReductionAuthFixed S b A) := by
  unfold AeadIndCpa; rw [aeadCpaDslAdv_aeadIndCpaExp_eq]

end SignalPqxdh.Security.ReductionDsl.AuthAead
