/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfHmacRun
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfHmacEnc
import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5M1
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthAeadCpaLeaves
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthAeadCpaSend
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfHmacLeaves
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfHmacMu
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfHmacRecv
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfHmacSend
import VCVio.EvalDist.Monad.Basic

/-!
# Evaluation Equivalence and Wiring for `prfHmacRedProg`

Proves that the `ReductionDsl` program `prfHmacRedProg S b.q_total` evaluates to the shallow
reduction `prfHmacReductionAuth S b A`. Packages the DSL reduction as `prfHmacDslAdv` and
establishes experiment equivalence and query-budget compliance.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthPrfHmac

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security
open SignalPqxdh.Security.ReductionDsl SignalPqxdh.Security.ReductionDsl.AuthPrf SignalPqxdh.Security.ReductionDsl.AuthAead
open FgGapDh
open OracleSpec OracleComp

@[simp] theorem sampleChal_prfHmac_bool_eval {Γ : List PT} (env : Env Γ) :
    (sampleChal (C := hmacPrfOracle) .bool).eval env = prfHmacUnif ($ᵗ Bool) := by
  simp only [sampleChal, Comp.eval, prfHmacUnif]; rfl

@[simp] theorem sampleChal_prfHmac_index_eval {Γ : List PT} (N : ℕ) (env : Env Γ) :
    (sampleChal (C := hmacPrfOracle) (.index N)).eval env =
      prfHmacUnif (RoKem.sampleIndexRange N) :=
  pqChalIface_liftP_eq (C := hmacPrfOracle) (RoKem.sampleIndexRange N)

section Dispatch

variable (S : Setup) (K : Nat)

theorem hmOther_eval_v2 {Γ₁ Δ : List PT} (mst : Var Γ₁ muStTy) [h₁ : Ext Γ₁ Δ] (env : Env Δ)
    (ms : PrfHmacMuState) (hm : Env.get env (h₁.wk mst) = muStToValS S ms)
    (m : Comp pqxdhOps pqPrimIface Δ RSF)
    (mx : OracleComp PrimBaseSpec (AuthResponse × AuthHybridStateFixed S))
    (hmx : m.eval env = Prod.map authRespToVal authHybridStateFixedToVal <$> mx) :
    (hmOther mst m).eval env =
      hmPreToVal <$> ((fun r => .inl (r, ms)) <$> mx :
        OracleComp PrimBaseSpec (HmRes S ⊕ HmSendCont S)) := by
  simp only [hmOther, bindV, v, Comp.eval, Expr.eval, Ext.step_wk, Env.get_succ, hm,
    hmx, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
  refine bind_congr fun x => ?_
  rcases x with ⟨r, h⟩
  rfl

set_option maxHeartbeats 4000000 in
theorem hmPreC_eval (jt : Nat) (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (ms : PrfHmacMuState) (hB : AuthListsBounded K hst)
    (hw : hst.toAuthHybridState.base.hasWonAuth = false) (hM : MuBounded K ms) :
    (hmPreC S K).eval (.cons (hmStToVal jt hst ms) (.cons (authQueryToVal q) .nil)) =
      hmPreToVal <$> hmPre S jt q hst ms := by
  cases q <;>
    simp only [hmPreC, hmDispatchC, letV_eval, caseSumV, v, Comp.eval, Expr.eval,
      Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero, authQueryToVal, authQenc, hmStToVal]
  case initPrin u =>
    refine (hmOther_eval_v2 S _ _ ms rfl _ _ (initPrinFixedB_eval S K _ _ _ hst u rfl rfl hB)).trans ?_
    rw [← stepAuthOtherPrim_cpa_eq S (.initPrin u) hst hw rfl]; rfl
  case corruptIK u =>
    refine (hmOther_eval_v2 S _ _ ms rfl _ _ (corruptFixedB_eval S K _ _ _ hst u rfl rfl hB)).trans ?_
    rw [← stepAuthOtherPrim_cpa_eq S (.corruptIK u) hst hw rfl]; rfl
  case genSPK u j =>
    refine (hmOther_eval_v2 S _ _ ms rfl _ _
      (genSpkFixedB_eval S K _ _ _ hst u j rfl rfl hB)).trans ?_
    rw [← stepAuthOtherPrim_cpa_eq S (.genSPK u j) hst hw rfl]; rfl
  case genOPK u j o =>
    refine (hmOther_eval_v2 S _ _ ms rfl _ _
      (genOpkFixedB_eval S K _ _ _ hst u j o rfl rfl hB)).trans ?_
    rw [← stepAuthOtherPrim_cpa_eq S (.genOPK u j o) hst hw rfl]; rfl
  case roQuery sec =>
    refine (hmOther_eval_v2 S _ _ ms rfl _ _ (roFixedB_eval S K _ _ _ hst sec rfl rfl hB)).trans ?_
    rw [← stepAuthOtherPrim_cpa_eq S (.roQuery sec) hst hw rfl]; rfl
  case roRootQuery rk dh =>
    refine (hmOther_eval_v2 S _ _ ms rfl _ _
      (roRootFixedB_eval S K _ _ _ hst rk dh rfl rfl hB)).trans ?_
    rw [← stepAuthOtherPrim_cpa_eq S (.roRootQuery rk dh) hst hw rfl]; rfl
  case registerKey sk =>
    refine (hmOther_eval_v2 S _ _ ms rfl _ _ (registerFixedB_eval S _ _ _ hst sk rfl rfl)).trans ?_
    rw [← stepAuthOtherPrim_cpa_eq S (.registerKey sk) hst hw rfl]; rfl
  case revealDhSecrets =>
    simp [hmPre, stepAuthOtherPrim, hmPreToVal, hmResToVal, aNone, authRespToVal, authRenc,
      Expr.eval]
  case sendOPK u i b m0 m1 =>
    exact hmSendC_eval_opk_v2 S K _ _ _ _ _ jt hst ms u i b m0 m1 rfl rfl rfl rfl hB hM
  case sendNoOPK u i b m0 m1 =>
    exact hmSendC_eval_noopk_v2 S K _ _ _ _ _ jt hst ms u i b m0 m1 rfl rfl rfl rfl hB hM
  case recvOPK k j o msg =>
    exact hmRecvC_eval_opk_v2 S K _ _ _ _ _ jt hst ms k j o msg rfl rfl rfl rfl hB hM
  case recvNoOPK k j l msg =>
    exact hmRecvC_eval_noopk_v2 S K _ _ _ _ _ jt hst ms k j l msg rfl rfl rfl rfl hB hM

end Dispatch

section Handle

variable (S : Setup) (K : Nat)

theorem hmPostC_eval {Δ : List PT} (a : Expr pqxdhOps Δ (.prod hmSendContTy (B 32))) (env : Env Δ)
    (c : HmSendCont S) (t : Bytes) (ha : a.eval env = (hmSendContToVal c, t))
    (hP : c.enc.st.pending.length ≤ K) :
    (hmPostC K a).eval env = pure (hmResToVal (c.post t)) := by
  simp only [hmPostC, letV_eval, bindV_eval, v, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk,
    Env.get_succ, Env.get_zero, ha, hmSendContToVal]
  rw [encPostIdC_eval S K _ _ c.enc t rfl hP, pure_bind]
  rw [finishIntC_eval S _ _ c.hst c.sid c.bundle c.m0 c.m1 c.p default ((c.enc.post t).1.getD [])
    (by
      rcases h : (c.enc.post t).1 with _ | ct <;>
        simp [Expr.eval, h, defaultMsgKeysE, msgKeysToVal, msgKeysV, getDBytes_eval])]
  simp only [pure_bind]
  rfl

/-- Encoding of a handled query's result as a `(resp, state)` value. -/
def hmOutToVal {S : Setup} (jt : Nat) (r : HmRes S) : (Ty.prod authRespTy hmStTy).denote :=
  (authRespToVal r.1.1, hmStToVal jt r.1.2 r.2)

set_option maxHeartbeats 4000000 in
theorem hmHandleC_eval (n jt : Nat) (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (ms : PrfHmacMuState) (hI : HmInv n hst ms) (hn : n ≤ K) :
    (hmHandleC S K).eval (.cons (hmStToVal jt hst ms) (.cons (authQueryToVal q) .nil)) =
      hmOutToVal jt <$> (embedPrim (spec := prfHmacSpec) (hmPre S jt q hst ms) >>= hmResume) := by
  have hI' := hI.mono hn
  simp only [hmHandleC, bindV_eval, letV_eval, caseSumV, v, liftPrimComp_prfHmac_eval,
    Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero]
  rw [hmPreC_eval S K jt q hst ms hI'.bnd hI'.won hI'.mu, embedPrim_map]
  erw [bind_map_left]
  rw [map_eq_bind_pure_comp, bind_assoc]
  refine hm_bind_congr_leaves (AllLeaves.embedPrim (hmPre_leaves S n jt q hst ms hI))
    fun p hp => ?_
  rcases p with r | c
  · rfl
  · simp only [hmPreToVal, hmResume, queryHmacEval_eval]
    have hcB : c.Bounded n := hp
    rw [hmContX0E_eval _ _ c rfl]
    simp only [prfHmacEvalQ, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
    refine bind_congr fun t => ?_
    rw [hmPostC_eval S K _ _ c t rfl (Nat.le_trans hcB.pending_le hn)]
    simp only [embedPrim_pure]
    erw [pure_bind]
    rfl

end Handle

section Finish

variable (K : Nat)

theorem foldr_dedup_eq (xs : List (ℕ × Bytes)) (hK : xs.length ≤ K) :
    xs.foldr (fun x acc =>
      if (acc.take K).any (fun y => (x.1 == y.1) && (x.2 == y.2)) then acc else x :: acc) [] =
      xs.dedup := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hl : xs.length ≤ K := by simp only [List.length_cons] at hK; omega
    rw [List.foldr_cons, ih hl,
      List.take_of_length_le ((List.dedup_sublist xs).length_le.trans hl)]
    by_cases hm : x ∈ xs
    · have h : (xs.dedup.any fun y => (x.1 == y.1) && (x.2 == y.2)) = true :=
        List.any_eq_true.mpr ⟨x, List.mem_dedup.mpr hm, by simp⟩
      rw [List.dedup_cons_of_mem hm]
      simp only [h, ↓reduceIte]
    · have h : (xs.dedup.any fun y => (x.1 == y.1) && (x.2 == y.2)) = false := by
        rw [← Bool.not_eq_true]
        intro h
        obtain ⟨y, hy, hxy⟩ := List.any_eq_true.mp h
        simp only [Bool.and_eq_true, beq_iff_eq] at hxy
        have hxy' : x = y := Prod.ext hxy.1 hxy.2
        subst hxy'
        exact hm (List.mem_dedup.mp hy)
      rw [List.dedup_cons_of_notMem hm]
      simp only [h, Bool.false_eq_true, ↓reduceIte]

theorem mapML_finish (jt : Nat) (pending : List (ℕ × Bytes × Bytes))
    (f : ℕ × Bytes → OracleComp PrfHmacSimSpec Bool)
    (hf : ∀ p, f p = (fun t => prfHmacPendingHit pending p.1 p.2 t) <$> prfHmacTagQ jt p.1 p.2)
    (pts : List (ℕ × Bytes)) {β : Type} (g : Bool → OracleComp PrfHmacSimSpec β) (K' : Nat)
    (hK : pts.length ≤ K') :
    (_root_.ReductionDsl.mapML f pts >>= fun hits => g ((hits.take K').any fun h => h)) =
      (prfHmacFinish jt pending pts >>= g) := by
  induction pts generalizing K' g with
  | nil => simp [_root_.ReductionDsl.mapML, prfHmacFinish]
  | cons x xs ih =>
    obtain ⟨K'', rfl⟩ : ∃ K'', K' = K'' + 1 := ⟨K' - 1, by simp at hK; omega⟩
    simp only [_root_.ReductionDsl.mapML, prfHmacFinish, hf, map_eq_bind_pure_comp, bind_assoc,
      pure_bind, Function.comp_apply, List.take_succ_cons, List.any_cons]
    refine bind_congr fun t => ?_
    have := ih (fun b => g (prfHmacPendingHit pending x.1 x.2 t || b)) K'' (by simp at hK; omega)
    exact this

theorem hmFinishC_eval {S : Setup} (jt : Nat) (hst : AuthHybridStateFixed S) (ms : PrfHmacMuState)
    (b' : Bool) (hP : ms.pending.length ≤ K) :
    (hmFinishC K).eval (.cons (hmStToVal jt hst ms) (.cons b' .nil)) =
      (prfHmacFinish jt ms.pending (ms.pending.map (fun e => (e.1, e.2.1))).dedup >>= fun hit =>
        pure (ms.bad || hit)) := by
  have hT : ms.pending.take K = ms.pending := List.take_of_length_le hP
  have hL : (ms.pending.map fun e => (e.1, e.2.1)).length ≤ K := by simpa using hP
  have hT2 :
      (ms.pending.map fun e => (e.1, e.2.1)).take K = ms.pending.map fun e => (e.1, e.2.1) :=
    List.take_of_length_le hL
  have hDL : (ms.pending.map fun e => (e.1, e.2.1)).dedup.length ≤ K :=
    (List.dedup_sublist _).length_le.trans hL
  simp only [hmFinishC, letV_eval, bindV_eval, mapMV, dedupE, eMap, eAny, muPend, muBad, v,
    natEq_eval, natLt_expr_eval, bytesBeq_eval, boolOr_eval, Comp.eval, Expr.eval,
    Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
    hmStToVal, muStToValS, hT, hT2]
  rw [foldr_dedup_eq K _ hL, List.take_of_length_le hDL]
  refine mapML_finish jt ms.pending _ (fun p => ?_) _ (fun hit => pure (ms.bad || hit)) K hDL
  by_cases hlt : p.1 < jt
  · simp [hlt, prfHmacTagQ, prfHmacUnif, prfHmacPendingHit, pendHitE, eAny, natEq_eval,
      bytesBeq_eval, bytesTake_eval, hT, v, Expr.eval]
    rfl
  · simp [hlt, prfHmacTagQ, prfHmacEvalQ, prfHmacPendingHit, pendHitE, eAny, natEq_eval,
      bytesBeq_eval, bytesTake_eval, queryHmacEval_eval, hT, v, Expr.eval]
    rw [map_eq_bind_pure_comp]; rfl

end Finish

section Run

variable (S : Setup) (K : Nat)

theorem hmStep_leaves (n jt : Nat) (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (ms : PrfHmacMuState) (hI : HmInv n hst ms) :
    AllLeaves (fun r : HmRes S => HmInv (n + 1) r.1.2 r.2)
      (embedPrim (spec := prfHmacSpec) (hmPre S jt q hst ms) >>= hmResume) := by
  refine AllLeaves.bind (AllLeaves.embedPrim (hmPre_leaves S n jt q hst ms hI)) fun p hp => ?_
  rcases p with r | c
  · exact AllLeaves.pure hp
  · have hcB : c.Bounded n := hp
    simp only [hmResume, map_eq_bind_pure_comp]
    exact AllLeaves.bind_const _ fun t => AllLeaves.pure (hcB.post_inv t)

/-- The DSL step function of `CostedReduction.eval` for `prfHmacRedProg`. -/
def hmDslStep :
    (q : AuthQuery S) → hmStTy.denote →
      OracleComp PrfHmacSimSpec ((authSpec S).Range q × hmStTy.denote) :=
  fun q st => do
    let p ← (hmHandleC S K).eval (.cons st (.cons (authQueryToVal q) .nil))
    return (valToAuthResp p.1, p.2)

theorem simulateQ_prfHmacRedProg_impl_eq {α : Type}
    (mx : OracleComp (unifSpec + authSpec S) α) (st : (prfHmacRedProg S K).σ.denote) :
    (simulateQ (prfHmacRedProg S K).impl mx).run st =
      runWithPrfHmacStep (hmDslStep S K) mx st := by
  induction mx using OracleComp.inductionOn generalizing st with
  | pure a => rfl
  | query_bind q k ih =>
    rw [simulateQ_query_bind, StateT.run_bind]
    rcases q with uq | gq
    · change ((do let u ← pqPrfHmacIface.fwdU uq; return (u, st)) >>=
          fun x => (simulateQ (prfHmacRedProg S K).impl (k x.1)).run x.2) =
        (liftM (OracleSpec.query (spec := PrfHmacSimSpec) (Sum.inl (Sum.inl uq))) >>=
          fun u => runWithPrfHmacStep (hmDslStep S K) (k u) st)
      rw [bind_assoc]
      congr 1; funext u
      rw [pure_bind, ih u st]
    · change (hmDslStep S K gq st >>=
          fun x => (simulateQ (prfHmacRedProg S K).impl (k x.1)).run x.2) =
        (hmDslStep S K gq st >>=
          fun x => runWithPrfHmacStep (hmDslStep S K) (k x.1) x.2)
      congr 1; funext x
      exact ih x.1 x.2

/-- Running `hmDslStep` and the fused shallow step agree for any computation making at most `n`
    game queries from an `HmInv m` state with `m + n ≤ K`. -/
theorem hm_runBridge (jt : Nat) {α β : Type}
    (f : α × hmStTy.denote → OracleComp PrfHmacSimSpec β)
    (g : α × (AuthHybridStateFixed S × PrfHmacMuState) → OracleComp PrfHmacSimSpec β)
    (hfg : ∀ a hst ms, HmInv K hst ms → f (a, hmStToVal jt hst ms) = g (a, (hst, ms)))
    (mx : OracleComp (unifSpec + authSpec S) α) :
    ∀ (n m : Nat) (hst : AuthHybridStateFixed S) (ms : PrfHmacMuState),
      IsQueryBoundP mx (fun q => isGameQuery q = true) n →
      HmInv m hst ms → m + n ≤ K →
      (runWithPrfHmacStep (hmDslStep S K) mx (hmStToVal jt hst ms) >>= f) =
        (runWithPrfHmacStep (fuseStep jt (stepAuthMuPrim S)) mx (hst, ms) >>= g) := by
  induction mx using OracleComp.inductionOn with
  | pure a =>
    intro n m hst ms _ hI hmK
    change (pure (a, hmStToVal jt hst ms) >>= f) = (pure (a, (hst, ms)) >>= g)
    simp only [pure_bind]
    exact hfg a hst ms (hI.mono (by omega))
  | query_bind q k ih =>
    intro n m hst ms hG hI hmK
    rw [isQueryBoundP_query_bind_iff] at hG
    rcases q with uq | gq
    · obtain ⟨_, hG⟩ := hG
      simp only [SignalPqxdh.isGameQuery, Bool.false_eq_true, ↓reduceIte] at hG
      rw [runWithPrfHmacStep_query_inl, runWithPrfHmacStep_query_inl, bind_assoc, bind_assoc]
      refine bind_congr fun u => ?_
      exact ih u n m hst ms (hG u) hI hmK
    · obtain ⟨hG0, hG⟩ := hG
      simp only [SignalPqxdh.isGameQuery, ↓reduceIte] at hG hG0
      have hn : 0 < n := by
        rcases hG0 with h | h
        · exact absurd trivial h
        · exact h
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at hG
      rw [runWithPrfHmacStep_query_inr, runWithPrfHmacStep_query_inr, bind_assoc, bind_assoc]
      simp only [hmDslStep, fuseStep]
      rw [hmHandleC_eval S K m jt gq hst ms hI (by omega), prfMuRun_stepAuthMuPrim]
      have hL := hmStep_leaves S m jt gq hst ms hI
      generalize (embedPrim (spec := prfHmacSpec) (hmPre S jt gq hst ms) >>= hmResume) = X at hL ⊢
      simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
      refine hm_bind_congr_leaves hL fun x hx => ?_
      simp only [hmOutToVal, valToAuthResp_authRespToVal]
      exact ih x.1.1 n' (m + 1) x.1.2 x.2 (hG x.1.1) hx (by omega)

theorem hmInitC_eval (u : (Ty.unit : PT).denote) :
    (hmInitC S).eval (.cons u .nil) =
      (prfHmacUnif (RoKem.sampleIndexRange (S.N_send_tot + S.N_recv_tot)) >>= fun jt =>
        prfHmacUnif ($ᵗ Bool) >>= fun secb =>
          pure ((), hmStToVal jt (AuthHybridStateFixed.empty S secb) {})) := by
  simp only [hmInitC, bindV_eval, sampleChal_prfHmac_index_eval, sampleChal_prfHmac_bool_eval,
    Comp.eval, Expr.eval]
  rfl

theorem hmInv_empty (secb : Bool) : HmInv 0 (AuthHybridStateFixed.empty S secb) {} :=
  ⟨authListsBounded_empty S secb, rfl, ⟨le_refl _, le_refl _, le_refl _⟩⟩

/-- Shallow `prfHmacReductionAuth` computation parameterized directly by an arbitrary adversary
    computation `runA`. -/
def prfHmacReductionAuthRun (runA : OracleComp (unifSpec + authSpec S) Bool) :
    OracleComp PrfHmacSimSpec Bool := do
  let j ← prfHmacUnif (RoKem.sampleIndexRange (S.N_send_tot + S.N_recv_tot))
  let (_, st) ← prfMuRun j (aeadMuIntReductionAuthRun S ⟨runA⟩) {}
  let hit ← prfHmacFinish j st.pending (st.pending.map (fun e => (e.1, e.2.1))).dedup
  return (st.bad || hit)

/-- Evaluation equivalence for `prfHmacRedProg S K` on any adversary computation making at most `K`
    game queries. -/
theorem prfHmacRedProg_eval_eq_of_isQueryBoundP
    (A : Unit → OracleComp (unifSpec + authSpec S) Bool)
    (hG : IsQueryBoundP (A ()) (fun q => isGameQuery q = true) K) :
    (prfHmacRedProg S K).eval A () = prfHmacReductionAuthRun S (A ()) := by
  unfold CostedReduction.eval prfHmacReductionAuthRun aeadMuIntReductionAuthRun
  change (do
      let as ← (hmInitC S).eval (.cons () .nil)
      let bs ← (simulateQ (prfHmacRedProg S K).impl (A as.1)).run as.2
      (hmFinishC K).eval (.cons bs.2 (.cons bs.1 .nil)) :
      OracleComp PrfHmacSimSpec Bool) = _
  rw [hmInitC_eval]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun jt => ?_
  rw [prfMuRun_bind, unifMu, prfMuRun_embedPrimMu]
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
  refine bind_congr fun secb => ?_
  erw [simulateQ_prfHmacRedProg_impl_eq]
  rw [prfMuRun_bind, prfMuRun_runWithMuStep]
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind, prfMuRun_pure]
  exact hm_runBridge S K jt
    (fun x => (hmFinishC K).eval (.cons x.2 (.cons x.1 .nil)))
    (fun x => prfHmacFinish jt x.2.2.pending (x.2.2.pending.map (fun e => (e.1, e.2.1))).dedup >>=
      fun hit => pure (x.2.2.bad || hit))
    (fun a hst ms hI => hmFinishC_eval K jt hst ms a hI.mu.pending_le)
    (A ()) K 0 _ _ hG (hmInv_empty S secb) (by omega)

/-- Evaluating `prfHmacRedProg S b.q_total` agrees with `(prfHmacReductionAuth S b A).run`. -/
theorem prfHmacRedProg_eval_eq (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    (prfHmacRedProg S b.q_total).eval (fun _ => A.1.run) () =
      (prfHmacReductionAuth S b A).run := by
  rw [prfHmacRedProg_eval_eq_of_isQueryBoundP S b.q_total (fun _ => A.1.run)
    (SignalPqxdh.QueryBounded.auth_total A.2)]
  simp only [prfHmacReductionAuthRun, prfHmacReductionAuth, prfHmacOfMu, prfHmacOfMuRun,
    prfHmacOfMuRunAt_eq, aeadMuIntReductionAuth]
  rfl

end Run

section Adv

variable (S : Setup)

/-- The `ReductionDsl` `PrfHmac` adversary with primitive-query budget `primQueryBudget S b`. -/
def prfHmacDslAdv (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    PrfHmacAdv where
  run := (prfHmacRedProg S b.q_total).eval (fun _ => A.1.run) ()
  q_prf := (prfHmacReductionAuth S b A).q_prf
  q_prim := primQueryBudget S b

theorem prfHmacDslAdv_run (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    (prfHmacDslAdv S b A).run = (prfHmacReductionAuth S b A).run :=
  prfHmacRedProg_eval_eq S b A

theorem prfHmacRedProg_evalDist_eq (P : Primitives) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    𝒟[prfHmacExp P (prfHmacDslAdv S b A)] = 𝒟[prfHmacExp P (prfHmacReductionAuth S b A)] := by
  have h : prfHmacDslAdv S b A =
      { prfHmacReductionAuth S b A with q_prim := primQueryBudget S b } := by
    unfold prfHmacDslAdv
    rw [prfHmacRedProg_eval_eq]
  rw [h]
  rfl

theorem prfHmacRedProg_prfHmac_eq (P : Primitives) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    PrfHmac P (prfHmacDslAdv S b A) = PrfHmac P (prfHmacReductionAuth S b A) := by
  simp only [PrfHmac, prfHmacRedProg_evalDist_eq]

/-- `prfHmacDslAdv` satisfies its declared query budgets. -/
theorem prfHmacDslAdv_bounded (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    (prfHmacDslAdv S b A).Bounded := by
  obtain ⟨h1, h2⟩ := prfHmacOfMu_bounded _ (aeadMuIntReductionAuth_bounded S b A)
  have hq : (prfHmacReductionAuth S b A).q_prim ≤ primQueryBudget S b := by
    unfold prfHmacReductionAuth prfHmacOfMu aeadMuIntReductionAuth perQueryAuthPrimBudget
      primQueryBudget Setup.N_sess_tot
    dsimp only
    nlinarith
  refine ⟨?_, ?_⟩
  · rw [prfHmacDslAdv_run]; exact h1
  · rw [prfHmacDslAdv_run]; exact h2.mono hq

end Adv

end SignalPqxdh.Security.ReductionDsl.AuthPrfHmac
