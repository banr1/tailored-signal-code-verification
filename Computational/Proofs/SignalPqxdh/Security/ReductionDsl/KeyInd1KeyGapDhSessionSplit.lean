/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDhProofs
public import Computational.Proofs.ReductionDsl.SoundnessTwoClass
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDhEvalEq

/-!
# Session-Split Primitive-Query Bound for `fgKeyInd1KeyGapDhProg`

**Checked by Lean.** Proves the `gdhPrimQueryBudget S b` primitive-query bound for
`fgKeyInd1KeyGapDhProg` via `CostedReduction.queryBound_eval₂`, separating the four
list-scanning session arms from non-session arms that make at most `32` primitive queries.
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh SignalPqxdh.Security SignalPqxdh.Security.FgGapDh SignalPqxdh.Security.FgGapDh1Key
open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh.LegacyCosted
open OracleSpec OracleComp

namespace SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh

open SignalPqxdh.Security.ReductionDsl.KeyInd
open SignalPqxdh.Security.ReductionDsl.KeyIndGapDh

/-- Predicate identifying session-creating `KeyInd` queries (`initiate*` and `accept*`). -/
def isSessionQ {S : Setup} : KeyIndQuery S → Bool
  | .initiateOPK _ _ _   => true
  | .initiateNoOPK _ _ _ => true
  | .acceptOPK _ _ _ _   => true
  | .acceptNoOPK _ _ _ _ => true
  | _                    => false

theorem keyIndAdv_sessionBound (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    A.1.run.IsQueryBoundP
      (onGame (G := keyIndSpec S) (fun t => isSessionQ t = true)) S.N_sess_tot := by
  obtain ⟨_, hS, hR, _⟩ := A.2
  refine isQueryBoundP_or_add (p₁ := isKeyIndSendQuery) (p₂ := isKeyIndRecvQuery) ?_ hS hR
  intro t ht
  rcases t with _ | t
  · exact ht.elim
  · cases t <;> simp_all [onGame, isSessionQ, isKeyIndSendQuery, isKeyIndRecvQuery]

/-- A `b`-bounded `KeyInd` adversary makes at most `min b.q_on S.N_sess_tot` session queries. -/
theorem keyIndAdv_sessionBound_on (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    A.1.run.IsQueryBoundP
      (onGame (G := keyIndSpec S) (fun t => isSessionQ t = true)) (min b.q_on S.N_sess_tot) := by
  by_cases h : b.q_on ≤ S.N_sess_tot
  · obtain ⟨_, _, _, _, hOn⟩ := A.2
    have hSessQOn : A.1.run.IsQueryBoundP
        (onGame (G := keyIndSpec S) (fun t => isSessionQ t = true)) b.q_on := by
      refine isQueryBoundP_of_imp (fun t ht => ?_) hOn
      rcases t with _ | t
      · exact ht.elim
      · cases t <;> simp_all [onGame, isSessionQ, isKeyIndOnlineQuery]
    simpa [Nat.min_eq_left h] using hSessQOn
  · simpa [Nat.min_eq_right (Nat.le_of_not_le h)] using keyIndAdv_sessionBound S b A

/-- Variant of `gdhHandle` with the four session arms replaced by no-ops, used to bound
    non-session primitive queries. -/
def gdhHandleNS (S : Setup) (K : Nat) :
    Comp pqxdhOps pqGapDhIface [gdhStateTy, keyIndQueryTy] (.prod keyIndRespTy gdhStateTy) :=
  let st : Var [gdhStateTy, keyIndQueryTy] gdhStateTy := .zero
  let q : Var [gdhStateTy, keyIndQueryTy] keyIndQueryTy := .succ .zero
  letV (.fst (v st)) fun pa =>
  letV (.snd (v st)) fun sm =>
  letV (smBase (v sm)) fun bSt =>
  caseSumV (v q) (fun u => wrapSim pa (initPrinGdhB K pa sm bSt u)) fun r1 =>
  caseSumV (v r1) (fun u => wrapBase pa sm (corruptB K bSt u)) fun r2 =>
  caseSumV (v r2) (fun x => wrapSim pa (genSpkGdhB S K pa sm bSt x)) fun r3 =>
  caseSumV (v r3) (fun x => wrapSim pa (genOpkGdhB S K pa sm bSt x)) fun r4 =>
  caseSumV (v r4) (fun _ => .ret (.pair rNone (v st))) fun r5 =>
  caseSumV (v r5) (fun _ => .ret (.pair rNone (v st))) fun r6 =>
  caseSumV (v r6) (fun _ => .ret (.pair rNone (v st))) fun r7 =>
  caseSumV (v r7) (fun _ => .ret (.pair rNone (v st))) fun r8 =>
  caseSumV (v r8) (fun sid => wrapBase pa sm (testB K bSt sid)) fun r9 =>
  caseSumV (v r9) (fun sec => wrapSim pa (roParsedC K sm sec)) fun r10 =>
  caseSumV (v r10) (fun _ => .ret (.pair rNone (v st))) fun r11 =>
  caseSumV (v r11) (fun sid => wrapBase pa sm (revealB K bSt sid)) fun r12 =>
  caseSumV (v r12) (fun sk => wrapSim pa (registerGdhB sm bSt sk))
                   (fun x => wrapBase pa sm (revealSpkB K bSt x))

theorem gdhHandleNS_primUB (S : Setup) (K : Nat) :
    (gdhHandleNS S K).queriesUB wPrimGdh wsZero ≤ 32 := by
  simp only [gdhHandleNS, initPrinGdhB, corruptB, genSpkGdhB, genOpkGdhB,
    testB, roParsedC, roRawFallbackC, revealB, registerGdhB, revealSpkB,
    wrapBase_primUB, wrapSim_primUB,
    letV_queriesUB, bindV_queriesUB, caseOptV_queriesUB, caseSumV_queriesUB,
    gPrim_queriesUB_wPrimGdh, mkSecretPosC_primUB, fgPatchC_primUB,
    sBytes32_queriesUB, sRandom64_queriesUB, sDrKey96_queriesUB,
    qX25519Base_queriesUB, qPow8_queriesUB, qSigPkGen_queriesUB, qSigSign_queriesUB,
    qKemKeyGen_queriesUB, Comp.queriesUB]
  omega

theorem gdhHandleNS_primQueries_le (S : Setup) (K : Nat) :
    (gdhHandleNS S K).queries wPrimGdh wsZero ≤ 32 :=
  (Comp.queries_le_queriesUB _ _ _).trans (gdhHandleNS_primUB S K)

/-- `callGdhHandle` with `gdhHandleNS` in place of `gdhHandle`. -/
def callGdhHandleNS (S : Setup) (K : Nat) {Δ : List PT}
    (st1 : Var Δ gdh1KeyStateTy) (q : Var Δ keyIndQueryTy) :
    Comp pqxdhOps pqSigAndDdhIface Δ (.prod keyIndRespTy gdh1KeyStateTy) :=
  letV (.fst (v st1)) fun gst =>
  bindV (renameComp (twoVarRen gst (.succ q)) (liftGdhComp (gdhHandleNS S K))) fun res =>
  .ret (.pair (.fst (v res)) (.pair (.snd (v res)) (.snd (v st1))))

theorem callGdhHandleNS_queries_prim_le (S : Setup) (K : Nat) {Δ : List PT}
    (st1 : Var Δ gdh1KeyStateTy) (q : Var Δ keyIndQueryTy) :
    (callGdhHandleNS S K st1 q).queries wPrim1Key wsZero1Key ≤ 32 := by
  simpa [callGdhHandleNS, Comp.queries] using gdhHandleNS_primQueries_le S K

section
set_option allowUnsafeReducibility true
attribute [local implicit_reducible] Env.get Ext.wk

theorem gdhHandle_eval_NS (S : Setup) (K : Nat) (q : KeyIndQuery S)
    (hq : isSessionQ q = false) (st : gdhStateTy.denote) :
    (gdhHandle S K).eval (.cons st (.cons (keyIndQenc q) .nil)) =
      (gdhHandleNS S K).eval (.cons st (.cons (keyIndQenc q) .nil)) := by
  cases q <;> simp only [isSessionQ, Bool.true_eq_false] at hq <;> rfl

theorem callGdhHandle_eval_NS (S : Setup) (K : Nat) {Δ : List PT}
    (st1 : Var Δ gdh1KeyStateTy) (qV : Var Δ keyIndQueryTy) (env : Env Δ) (q : KeyIndQuery S)
    (hq : env.get qV = keyIndQenc q) (hns : isSessionQ q = false) :
    (callGdhHandle S K st1 qV).eval env = (callGdhHandleNS S K st1 qV).eval env := by
  unfold callGdhHandle callGdhHandleNS
  simp only [letV_eval, bindV, Comp.eval, v, Expr.eval, Ext.step_wk', Ext.refl_wk',
    Env.get_zero', Env.get_succ', renameComp_eval, pullEnv_twoVarRen, liftGdhComp_eval, hq,
    gdhHandle_eval_NS S K q hns]

/-- Primitive-query soundness for one `Comp` evaluation over `pqSigAndDdhIface`. -/
theorem comp_primBound {Γ : List PT} {t : PT} (c : Comp pqxdhOps pqSigAndDdhIface Γ t)
    (ρ : Env Γ) {n : ℕ} (h : c.queries wPrim1Key wsZero1Key ≤ n) :
    (c.eval ρ).IsQueryBoundP (fun q => isPrimQuery q = true) n := by
  refine (Comp.queryBound_eval (fun q => isPrimQuery q = true)
    SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight
    SignalPqxdh.LegacyCosted.samplerZeroQueryWeight ?_ ?_ c ρ).mono h
  · intro g x hx
    cases g with
    | inl t => simp [SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight]
    | inr t => simp [pqSigAndDdhIface, pqChalIface, isPrimQuery] at hx
  · intro k
    change IsQueryBoundP
      (liftM (OracleSpec.query (spec := PrimBaseSpec + sigAndDdhOracle.spec) (Sum.inl (Sum.inl k))))
      (fun q => isPrimQuery q = true) 0
    rw [isQueryBoundP_query_iff]
    simp [isPrimQuery]

theorem ite_eval_queryBound {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T} {Γ : List PT}
    {t : PT} (b : Expr pqxdhOps Γ .bool) (c d : Comp pqxdhOps I Γ t) (ρ : Env Γ)
    {P : ι → Prop} [DecidablePred P] {n : ℕ}
    (hc : b.eval ρ = true → (c.eval ρ).IsQueryBoundP P n)
    (hd : b.eval ρ = false → (d.eval ρ).IsQueryBoundP P n) :
    ((Comp.ite b c d).eval ρ).IsQueryBoundP P n := by
  simp only [Comp.eval]
  split
  · rename_i h; exact hc h
  · rename_i h; exact hd (by simpa using h)

theorem callGdhHandle_primBound_NS (S : Setup) (K : Nat) {Δ : List PT}
    (st1 : Var Δ gdh1KeyStateTy) (qV : Var Δ keyIndQueryTy) (env : Env Δ) (q : KeyIndQuery S)
    (hq : env.get qV = keyIndQenc q) (hns : isSessionQ q = false) :
    ((callGdhHandle S K st1 qV).eval env).IsQueryBoundP (fun q => isPrimQuery q = true) 32 := by
  rw [callGdhHandle_eval_NS S K st1 qV env q hq hns]
  exact comp_primBound _ env (callGdhHandleNS_queries_prim_le S K st1 qV)

theorem gdh1KeyHandle_primBound_heavy (S : Setup) (K : Nat) (s : gdh1KeyStateTy.denote)
    (t : KeyIndQuery S) :
    ((gdh1KeyHandle S K).eval (.cons s (.cons (keyIndQenc t) .nil))).IsQueryBoundP
      (fun q => isPrimQuery q = true) (16 * (5 * S.N_dh + S.N_sess_tot + 12)) :=
  comp_primBound _ _ ((gdh1KeyHandle_queries_prim_le S K).trans (by omega))

theorem gdh1KeyHandle_primBound_light (S : Setup) (K : Nat) (s : gdh1KeyStateTy.denote)
    (t : KeyIndQuery S) (ht : isSessionQ t = false) :
    ((gdh1KeyHandle S K).eval (.cons s (.cons (keyIndQenc t) .nil))).IsQueryBoundP
      (fun q => isPrimQuery q = true) 32 := by
  cases t with
  | initPrin u =>
    simp only [gdh1KeyHandle, keyIndQenc, caseSumV,
      Comp.eval, v, Expr.eval, Env.get_zero', Env.get_succ', Ext.refl_wk']
    exact comp_primBound _ _ ((initPrin1KeyB_queries_prim_le _ _ _).trans (by omega))
  | corruptIK u =>
    simp only [gdh1KeyHandle, keyIndQenc, caseSumV,
      Comp.eval, v, Expr.eval, Env.get_zero', Env.get_succ', Ext.refl_wk']
    exact callGdhHandle_primBound_NS S K _ _ _ (.corruptIK u) rfl rfl
  | genSPK u j =>
    simp only [gdh1KeyHandle, keyIndQenc, caseSumV,
      Comp.eval, v, Expr.eval, Env.get_zero', Env.get_succ', Ext.refl_wk']
    unfold genSpk1KeyB
    refine ite_eval_queryBound _ _ _ _ (fun _ => comp_primBound _ _ ?_)
      (fun _ => callGdhHandle_primBound_NS S K _ _ _ (.genSPK u j) rfl rfl)
    simp only [letV_queries, bindV_queries, caseOptV_queries, Comp.queries,
      liftGdhComp_queries_prim, gPrim_queries_wPrimGdh, sigChalQ_dsl_queries_prim,
      sBytes32_queries, sRandom64_queries, qX25519Base_queries, qKemKeyGen_queries]
    omega
  | genOPK u j o =>
    simp only [gdh1KeyHandle, keyIndQenc, caseSumV,
      Comp.eval, v, Expr.eval, Env.get_zero', Env.get_succ', Ext.refl_wk']
    exact callGdhHandle_primBound_NS S K _ _ _ (.genOPK u j o) rfl rfl
  | initiateOPK u i b => simp [isSessionQ] at ht
  | initiateNoOPK u i b => simp [isSessionQ] at ht
  | acceptOPK k j o h => simp [isSessionQ] at ht
  | acceptNoOPK k j l h => simp [isSessionQ] at ht
  | testSession sid =>
    simp only [gdh1KeyHandle, keyIndQenc, caseSumV,
      Comp.eval, v, Expr.eval, Env.get_zero', Env.get_succ', Ext.refl_wk']
    exact callGdhHandle_primBound_NS S K _ _ _ (.testSession sid) rfl rfl
  | roQuery sec =>
    simp only [gdh1KeyHandle, keyIndQenc, caseSumV,
      Comp.eval, v, Expr.eval, Env.get_zero', Env.get_succ', Ext.refl_wk']
    exact callGdhHandle_primBound_NS S K _ _ _ (.roQuery sec) rfl rfl
  | revealDhSecrets =>
    simp only [gdh1KeyHandle, keyIndQenc, caseSumV,
      Comp.eval, v, Expr.eval, Env.get_zero', Env.get_succ', Ext.refl_wk']
    exact callGdhHandle_primBound_NS S K _ _ _ .revealDhSecrets rfl rfl
  | revealSessionKey sid =>
    simp only [gdh1KeyHandle, keyIndQenc, caseSumV,
      Comp.eval, v, Expr.eval, Env.get_zero', Env.get_succ', Ext.refl_wk']
    exact callGdhHandle_primBound_NS S K _ _ _ (.revealSessionKey sid) rfl rfl
  | registerKey sk =>
    simp only [gdh1KeyHandle, keyIndQenc, caseSumV,
      Comp.eval, v, Expr.eval, Env.get_zero', Env.get_succ', Ext.refl_wk']
    exact callGdhHandle_primBound_NS S K _ _ _ (.registerKey sk) rfl rfl
  | revealSpkSk u j =>
    simp only [gdh1KeyHandle, keyIndQenc, caseSumV,
      Comp.eval, v, Expr.eval, Env.get_zero', Env.get_succ', Ext.refl_wk']
    exact callGdhHandle_primBound_NS S K _ _ _ (.revealSpkSk u j) rfl rfl

set_option allowUnsafeReducibility true in
attribute [local semireducible] Env.get Ext.wk
end

private theorem split_arith (q k X F : ℕ) (hk : k ≤ q) (hX : 2 ≤ X) (hF : F ≤ 16 * X) :
    0 + (q * 32 + k * (16 * X - 32)) + F ≤ 32 * (q - k) + 16 * (k + 1) * X := by
  obtain ⟨r, rfl⟩ : ∃ r, q = k + r := ⟨q - k, by omega⟩
  obtain ⟨d, hd⟩ : ∃ d, 16 * X = 32 + d := ⟨16 * X - 32, by omega⟩
  have h1 : 16 * X - 32 = d := by omega
  have h2 : k + r - k = r := by omega
  have h3 : 16 * (k + 1) * X = (k + 1) * (32 + d) := by rw [← hd]; ring
  rw [h1, h2, h3]
  nlinarith

/-- Two-class primitive-query bound for `fgKeyInd1KeyGapDhProg` given `q` total game queries and
    `m` session queries. -/
theorem fgKeyInd1KeyGapDhProg_primBounded_split (S : Setup) (K q m : Nat)
    (A : Unit → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hA : ∀ a, (A a).IsQueryBoundP (ReductionDsl.isGameQuery (G := keyIndSpec S)) q)
    (hAH : ∀ a, (A a).IsQueryBoundP
      (onGame (G := keyIndSpec S) (fun t => isSessionQ t = true)) m)
    (U V : Bytes) :
    ((fgKeyInd1KeyGapDhProg S K).eval A (U, V)).IsQueryBoundP
      (fun q => isPrimQuery q = true)
      (32 * (q - min q m) + 16 * (min q m + 1) * (5 * S.N_dh + S.N_sess_tot + 12)) := by
  refine (CostedReduction.queryBound_eval₂ (fgKeyInd1KeyGapDhProg S K)
    (fun q => isPrimQuery q = true)
    SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight
    SignalPqxdh.LegacyCosted.samplerZeroQueryWeight ?_ ?_
    (fun t => isSessionQ t = true) (kL := 32) (kH := 16 * (5 * S.N_dh + S.N_sess_tot + 12))
    (by omega) (fun t s _ => gdh1KeyHandle_primBound_heavy S K s t)
    (fun t s ht => gdh1KeyHandle_primBound_light S K s t (by simpa using ht))
    A q m hA hAH (U, V)).mono ?_
  · intro g x hx
    cases g with
    | inl t => simp [SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight]
    | inr t => simp [pqSigAndDdhIface, pqChalIface, isPrimQuery] at hx
  · intro k
    change IsQueryBoundP
      (liftM (OracleSpec.query (spec := PrimBaseSpec + sigAndDdhOracle.spec) (Sum.inl (Sum.inl k))))
      (fun q => isPrimQuery q = true) 0
    rw [isQueryBoundP_query_iff]
    simp [isPrimQuery]
  · have h0 : (fgKeyInd1KeyGapDhProg S K).init.queries
        SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight
        SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = 0 :=
      fgKeyInd1KeyGapDhProg_init_queries_prim S K
    have hF : (fgKeyInd1KeyGapDhProg S K).finish.queries
        SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight
        SignalPqxdh.LegacyCosted.samplerZeroQueryWeight ≤ 3 * S.N_dh + S.N_sess_tot :=
      gdh1KeyFinish_queries_prim_le S K
    rw [h0]
    exact split_arith q (min q m) _ _ (min_le_left _ _) (by omega) (hF.trans (by omega))

theorem gdhPrimQueryBudget_le_primQueryBudget (S : Setup) (b : QueryBudget) :
    gdhPrimQueryBudget S b ≤ primQueryBudget S b := by
  unfold gdhPrimQueryBudget primQueryBudget
  dsimp only
  have hX : 12 ≤ 5 * S.N_dh + S.N_sess_tot + 12 := by omega
  obtain ⟨r, hr⟩ : ∃ r, b.q_total = min (min b.q_on b.q_total) S.N_sess_tot + r :=
    ⟨b.q_total - min (min b.q_on b.q_total) S.N_sess_tot, by omega⟩
  generalize min (min b.q_on b.q_total) S.N_sess_tot = k at hr ⊢
  generalize 5 * S.N_dh + S.N_sess_tot + 12 = X at hX ⊢
  rw [hr, Nat.add_sub_cancel_left]
  have h2 : r * 12 ≤ r * X := Nat.mul_le_mul le_rfl hX
  nlinarith [h2]

theorem split_prim_eq_gdhPrimQueryBudget (S : Setup) (b : QueryBudget) :
    32 * (b.q_total - min b.q_total (min b.q_on S.N_sess_tot)) +
      16 * (min b.q_total (min b.q_on S.N_sess_tot) + 1) * (5 * S.N_dh + S.N_sess_tot + 12) =
    gdhPrimQueryBudget S b := by
  unfold gdhPrimQueryBudget
  dsimp only
  have hm : min b.q_total (min b.q_on S.N_sess_tot) = min (min b.q_on b.q_total) S.N_sess_tot := by
    omega
  rw [hm]

theorem keyIndAdv_gameBound (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    ∀ _ : Unit, (A.1.run).IsQueryBoundP
      (_root_.ReductionDsl.isGameQuery (G := keyIndSpec S)) b.q_total := by
  intro _
  obtain ⟨_, _, _, h, _⟩ := A.2
  convert h using 1
  funext q
  cases q
  · exact propext ⟨False.elim, Bool.noConfusion⟩
  · exact propext ⟨fun _ => rfl, fun _ => trivial⟩

/-- Evaluating `fgKeyInd1KeyGapDhProg S K` on a `b`-bounded `KeyInd` adversary makes at most
    `gdhPrimQueryBudget S b` primitive queries. -/
theorem fgKeyInd1KeyGapDhProg_primBounded_gdhPrimQueryBudget (S : Setup) (K : Nat)
    (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) (U V : Bytes) :
    ((fgKeyInd1KeyGapDhProg S K).eval (fun _ => A.1.run) (U, V)).IsQueryBoundP
      (fun q => isPrimQuery q = true) (gdhPrimQueryBudget S b) :=
  (fgKeyInd1KeyGapDhProg_primBounded_split S K b.q_total (min b.q_on S.N_sess_tot) (fun _ => A.1.run)
    (keyIndAdv_gameBound S b A) (fun _ => keyIndAdv_sessionBound_on S b A) U V).mono
    (le_of_eq (split_prim_eq_gdhPrimQueryBudget S b))

end SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh
