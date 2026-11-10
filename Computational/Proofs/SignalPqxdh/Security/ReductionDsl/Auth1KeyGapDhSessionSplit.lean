/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyGapDhBounds
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDhSessionSplit
public import Computational.Proofs.SpecLemmas.SignalPqxdh.Game

/-!
# Session-Split Primitive and Bilinear DDH Query Bounds for `fgAuth1KeyGapDhProg`

**Checked by Lean.** Proves the `gdhPrimQueryBudget S b` primitive-query bound for
`fgAuth1KeyGapDhProg` via a session/non-session handler split
(`fgAuth1KeyGapDhProg_primBounded_gdhPrimQueryBudget`), together with the shallow `GdhSimSpec`
bilinear potential and per-branch DDH query bounds.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthHs

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl
open OracleSpec OracleComp

/-- Whether an `Auth` query creates a session (`sendOPK`, `sendNoOPK`, `recvOPK`, `recvNoOPK`). -/
def isAuthSessionQ {S : Setup} : AuthQuery S → Bool
  | .sendOPK _ _ _ _ _   => true
  | .sendNoOPK _ _ _ _ _ => true
  | .recvOPK _ _ _ _     => true
  | .recvNoOPK _ _ _ _   => true
  | _                    => false

theorem authAdv_sessionBound (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    A.1.run.IsQueryBoundP
      (onGame (G := authSpec S) (fun t => isAuthSessionQ t = true)) S.N_sess_tot := by
  have hS := SignalPqxdh.QueryBounded.auth_send A.2
  have hR := SignalPqxdh.QueryBounded.auth_recv A.2
  refine isQueryBoundP_or_add (p₁ := isAuthSendQuery) (p₂ := isAuthRecvQuery) ?_ hS hR
  intro t ht
  rcases t with _ | t
  · exact ht.elim
  · cases t <;> simp_all [onGame, isAuthSessionQ, isAuthSendQuery, isAuthRecvQuery]

/-- A query-bounded `Auth` adversary makes at most `min b.q_on S.N_sess_tot` session queries. -/
theorem authAdv_sessionBound_on (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    A.1.run.IsQueryBoundP
      (onGame (G := authSpec S) (fun t => isAuthSessionQ t = true)) (min b.q_on S.N_sess_tot) := by
  by_cases h : b.q_on ≤ S.N_sess_tot
  · rw [Nat.min_eq_left h]
    refine isQueryBoundP_of_imp (fun t ht => ?_) (SignalPqxdh.QueryBounded.auth_on A.2)
    rcases t with _ | t
    · exact ht.elim
    · cases t <;> simp_all [onGame, isAuthSessionQ, isAuthOnlineQuery]
  · rw [Nat.min_eq_right (Nat.le_of_not_le h)]
    exact authAdv_sessionBound S b A

theorem authAdv_gameBound (S : Setup) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    ∀ _ : Unit, (A.1.run).IsQueryBoundP
      (_root_.ReductionDsl.isGameQuery (G := authSpec S)) b.q_total := by
  intro _
  have h := SignalPqxdh.QueryBounded.auth_total A.2
  convert h using 1
  funext q
  cases q
  · exact propext ⟨False.elim, Bool.noConfusion⟩
  · exact propext ⟨fun _ => rfl, fun _ => trivial⟩

section Branches

variable {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}

def fgStepNSC (S : Setup) (K : Nat) (pa : Var Γ₁ paramsTy) (sim : Var Γ₂ fgSimTy)
    (q : Var Γ₃ authQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] : CG Δ RSF :=
  caseSumV (v q) (fun u => fgInitPrinC K pa sim u) fun q =>
  caseSumV (v q) (fun u => onBaseF sim fun g => corruptB K g u) fun q =>
  caseSumV (v q) (fun x => fgGenSpkC S K pa sim x) fun q =>
  caseSumV (v q) (fun x => onBaseF sim fun g => genOpkB K g x) fun q =>
  caseSumV (v q) (fun _ => .ret (.pair aNone (v sim))) fun q =>
  caseSumV (v q) (fun _ => .ret (.pair aNone (v sim))) fun q =>
  caseSumV (v q) (fun _ => .ret (.pair aNone (v sim))) fun q =>
  caseSumV (v q) (fun _ => .ret (.pair aNone (v sim))) fun q =>
  caseSumV (v q) (fun sec => fgRoC K sim sec) fun q =>
  caseSumV (v q) (fun x => fgRoRootC K sim x) fun q =>
  caseSumV (v q) (fun _ => .ret (.pair aNone (v sim))) fun sk =>
  fgRegisterC sim sk

def a1gStepNSC (S : Setup) (K : Nat) (st : Var Γ₁ a1gStTy) (q : Var Γ₂ authQueryTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : CS Δ (.prod authRespTy a1gStTy) :=
  letV (.fst (.fst (v st))) fun pa =>
  letV (.snd (.fst (v st))) fun sim =>
  letV (.snd (v st)) fun sigB =>
  .iteC (.boolAnd (paDh1 (v pa))
      (eCaseOpt (eFind K (stPrin (fsBase (v sim))) fun e => natEq (.fst (v e)) (paTI (v pa)))
        (.litBool false) fun e => peCorrupted (.snd (v e))))
    (.ret (.pair aNone (v st))) <|
  bindV (a1gPreC S K pa sim sigB q) fun pre =>
  caseSumV (v pre)
    (fun r => .ret (.pair (.fst (v r))
      (.pair (.pair (v pa) (.fst (.snd (v r)))) (.snd (.snd (v r)))))) fun _ =>
  bindV (KeyInd1KeyGapDh.liftGdhComp (fgStepNSC S K pa sim q)) fun r =>
  .ret (.pair (.fst (v r)) (.pair (.pair (v pa) (.snd (v r))) (v sigB)))

def fgStep2NSC (K : Nat) (pa : Var Γ₁ a1gParams2Ty) (sim : Var Γ₂ fgSimTy)
    (q : Var Γ₃ authQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] : CG Δ RSF :=
  caseSumV (v q) (fun u => fgInitPrin2C K pa sim u) fun q =>
  caseSumV (v q) (fun u => onBaseF sim fun g => corruptB K g u) fun q =>
  caseSumV (v q) (fun x => fgGenSpk2C K pa sim x) fun q =>
  caseSumV (v q) (fun x => onBaseF sim fun g => genOpkB K g x) fun q =>
  caseSumV (v q) (fun _ => .ret (.pair aNone (v sim))) fun q =>
  caseSumV (v q) (fun _ => .ret (.pair aNone (v sim))) fun q =>
  caseSumV (v q) (fun _ => .ret (.pair aNone (v sim))) fun q =>
  caseSumV (v q) (fun _ => .ret (.pair aNone (v sim))) fun q =>
  caseSumV (v q) (fun sec => fgRoC K sim sec) fun q =>
  caseSumV (v q) (fun x => fgRoRootC K sim x) fun q =>
  caseSumV (v q) (fun _ => .ret (.pair aNone (v sim))) fun sk =>
  fgRegisterC sim sk

def a1gStep2NSC (K : Nat) (st : Var Γ₁ a1g2StTy) (q : Var Γ₂ authQueryTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : CS Δ (.prod authRespTy a1g2StTy) :=
  letV (.fst (.fst (v st))) fun pa =>
  letV (.snd (.fst (v st))) fun sim =>
  letV (.snd (v st)) fun sigB =>
  .iteC (eCaseSum (pa2Role (v pa))
      (fun uT =>
        eCaseOpt (eFind K (stPrin (fsBase (v sim))) fun e => natEq (.fst (v e)) (v uT))
          (.litBool false) fun e => peCorrupted (.snd (v e)))
      (fun _ => .litBool false))
    (.ret (.pair aNone (v st))) <|
  bindV (a1gPre2C K pa sim sigB q) fun pre =>
  caseSumV (v pre)
    (fun r => .ret (.pair (.fst (v r))
      (.pair (.pair (v pa) (.fst (.snd (v r)))) (.snd (.snd (v r)))))) fun _ =>
  bindV (KeyInd1KeyGapDh.liftGdhComp (fgStep2NSC K pa sim q)) fun r =>
  .ret (.pair (.fst (v r)) (.pair (.pair (v pa) (.snd (v r))) (v sigB)))

end Branches

/-- `a1gHandleDsl` with the four session arms replaced by a no-op. -/
def a1gHandleNS (S : Setup) (K : Nat) :
    CS [a1gStTy, authQueryTy] (.prod authRespTy a1gStTy) :=
  a1gStepNSC S K (.vz : Var [a1gStTy, authQueryTy] a1gStTy)
    (.vs .vz : Var [a1gStTy, authQueryTy] authQueryTy)

def a1g2HandleNS (K : Nat) :
    CS [a1g2StTy, authQueryTy] (.prod authRespTy a1g2StTy) :=
  a1gStep2NSC K (.vz : Var [a1g2StTy, authQueryTy] a1g2StTy)
    (.vs .vz : Var [a1g2StTy, authQueryTy] authQueryTy)

theorem a1gHandleNS_queries_prim_le (S : Setup) (K : Nat) :
    (a1gHandleNS S K).queries KeyInd1KeyGapDh.wPrim1Key KeyInd1KeyGapDh.wsZero1Key ≤ 32 := by
  simp only [
    a1gHandleNS, a1gStepNSC, Comp.letC, a1gPreC, a1gInitPrinC, a1gGenSpkC,
    a1g_liftGdhComp_queries_prim, KeyInd1KeyGapDh.sigChalQ_dsl_queries_prim,
    queries_liftChal_gdhPrimW, queries_queryDdh_prim,
    fgStepNSC,
    fgInitPrinC, fgGenSpkC, fgRoC, fgRoRootC, fgRegisterC,
    onBaseF, corruptB, genOpkB,
    mkSecretPosC, ddhEqC, ddhEqOptC,
    entryMatchesC, patchC, rootPatchC,
    findMV, Comp.sampleBytes32, Comp.sampleDrKey96C, Comp.queryPrim,
    primW, primWS, gdhPrimW, gdhWS,
    bindV, letV, caseOptV, caseSumV,
    Comp.sampleBytes32C, Comp.sampleRandom64C, Comp.queryPrimC,
    a1g_wPrim_inl, a1g_wsZero1Key, Comp.queries,
    Nat.zero_max, Nat.max_zero, max_self, Nat.add_zero, Nat.zero_add, Nat.mul_zero]
  omega

theorem a1g2HandleNS_queries_prim_le (K : Nat) :
    (a1g2HandleNS K).queries KeyInd1KeyGapDh.wPrim1Key KeyInd1KeyGapDh.wsZero1Key ≤ 32 := by
  simp only [
    a1g2HandleNS, a1gStep2NSC, Comp.letC, a1gPre2C, a1gInitPrin2C, a1gGenSpk2C,
    a1g_liftGdhComp_queries_prim, KeyInd1KeyGapDh.sigChalQ_dsl_queries_prim,
    queries_liftChal_gdhPrimW, queries_queryDdh_prim,
    fgStep2NSC,
    fgInitPrin2C, fgGenSpk2C, fgRoC, fgRoRootC, fgRegisterC,
    onBaseF, corruptB, genOpkB,
    mkSecretPosC, ddhEqC, ddhEqOptC,
    entryMatchesC, patchC, rootPatchC,
    findMV, Comp.sampleBytes32, Comp.sampleDrKey96C, Comp.queryPrim,
    primW, primWS, gdhPrimW, gdhWS,
    bindV, letV, caseOptV, caseSumV,
    Comp.sampleBytes32C, Comp.sampleRandom64C, Comp.queryPrimC,
    a1g_wPrim_inl, a1g_wsZero1Key, Comp.queries,
    Nat.zero_max, Nat.max_zero, max_self, Nat.add_zero, Nat.zero_add, Nat.mul_zero]
  omega

section
set_option allowUnsafeReducibility true
attribute [local implicit_reducible] Env.get Ext.wk

theorem a1gHandleDsl_eval_NS (S : Setup) (K : Nat) (t : AuthQuery S)
    (ht : isAuthSessionQ t = false) (s : a1gStTy.denote) :
    (a1gHandleDsl S K).eval (.cons s (.cons (authQenc t) .nil)) =
      (a1gHandleNS S K).eval (.cons s (.cons (authQenc t) .nil)) := by
  cases t <;> simp only [isAuthSessionQ, Bool.true_eq_false] at ht <;> rfl

theorem a1g2HandleDsl_eval_NS (S : Setup) (K : Nat) (t : AuthQuery S)
    (ht : isAuthSessionQ t = false) (s : a1g2StTy.denote) :
    (a1g2HandleDsl S K).eval (.cons s (.cons (authQenc t) .nil)) =
      (a1g2HandleNS K).eval (.cons s (.cons (authQenc t) .nil)) := by
  cases t <;> simp only [isAuthSessionQ, Bool.true_eq_false] at ht <;> rfl

end

theorem a1gHandle_primBound_heavy (S : Setup) (K : Nat) (s : a1g2StTy.denote)
    (t : AuthQuery S) :
    ((fgAuth1KeyGapDhProg S K).handle.eval (.cons s (.cons (authQenc t) .nil))).IsQueryBoundP
      (fun q => isPrimQuery q = true) (16 * (5 * S.N_dh + S.N_sess_tot + 12)) :=
  KeyInd1KeyGapDh.comp_primBound _ _ ((a1g_handle_prim_le S K).trans (by omega))

theorem a1gHandle_primBound_light (S : Setup) (K : Nat) (s : a1g2StTy.denote)
    (t : AuthQuery S) (ht : isAuthSessionQ t = false) :
    ((fgAuth1KeyGapDhProg S K).handle.eval (.cons s (.cons (authQenc t) .nil))).IsQueryBoundP
      (fun q => isPrimQuery q = true) 32 := by
  change ((a1g2HandleDsl S K).eval (.cons s (.cons (authQenc t) .nil))).IsQueryBoundP _ _
  rw [a1g2HandleDsl_eval_NS S K t ht s]
  exact KeyInd1KeyGapDh.comp_primBound _ _ (a1g2HandleNS_queries_prim_le K)

private theorem a1g_split_arith (q k X F : ℕ) (hk : k ≤ q) (hX : 2 ≤ X) (hF : F ≤ 16 * X) :
    0 + (q * 32 + k * (16 * X - 32)) + F ≤ 32 * (q - k) + 16 * (k + 1) * X := by
  obtain ⟨r, rfl⟩ : ∃ r, q = k + r := ⟨q - k, by omega⟩
  obtain ⟨d, hd⟩ : ∃ d, 16 * X = 32 + d := ⟨16 * X - 32, by omega⟩
  have h1 : 16 * X - 32 = d := by omega
  have h2 : k + r - k = r := by omega
  have h3 : 16 * (k + 1) * X = (k + 1) * (32 + d) := by rw [← hd]; ring
  rw [h1, h2, h3]
  nlinarith

/-- Two-class primitive-query bound for `fgAuth1KeyGapDhProg` separating session and non-session
    queries. -/
theorem fgAuth1KeyGapDhProg_primBounded_split (S : Setup) (K q m : Nat)
    (A : Unit → OracleComp (unifSpec + authSpec S) Bool)
    (hA : ∀ a, (A a).IsQueryBoundP (ReductionDsl.isGameQuery (G := authSpec S)) q)
    (hAH : ∀ a, (A a).IsQueryBoundP
      (onGame (G := authSpec S) (fun t => isAuthSessionQ t = true)) m)
    (U V : Bytes) :
    ((fgAuth1KeyGapDhProg S K).eval A (U, V)).IsQueryBoundP
      (fun q => isPrimQuery q = true)
      (32 * (q - min q m) + 16 * (min q m + 1) * (5 * S.N_dh + S.N_sess_tot + 12)) := by
  refine (CostedReduction.queryBound_eval₂ (fgAuth1KeyGapDhProg S K)
    (fun q => isPrimQuery q = true)
    SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight
    SignalPqxdh.LegacyCosted.samplerZeroQueryWeight ?_ ?_
    (fun t => isAuthSessionQ t = true) (kL := 32) (kH := 16 * (5 * S.N_dh + S.N_sess_tot + 12))
    (by omega) (fun t s _ => a1gHandle_primBound_heavy S K s t)
    (fun t s ht => a1gHandle_primBound_light S K s t (by simpa using ht))
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
  · have h0 : (fgAuth1KeyGapDhProg S K).init.queries
        SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight
        SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = 0 :=
      a1g_init_prim S K
    have hF : (fgAuth1KeyGapDhProg S K).finish.queries
        SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight
        SignalPqxdh.LegacyCosted.samplerZeroQueryWeight ≤ S.N_dh * 4 + S.N_sess_tot * 2 :=
      a1g_finish_prim_le S K
    rw [h0]
    exact a1g_split_arith q (min q m) _ _ (min_le_left _ _) (by omega) (hF.trans (by omega))

theorem a1g_split_prim_eq_gdhPrimQueryBudget (S : Setup) (b : QueryBudget) :
    32 * (b.q_total - min b.q_total (min b.q_on S.N_sess_tot)) +
      16 * (min b.q_total (min b.q_on S.N_sess_tot) + 1) * (5 * S.N_dh + S.N_sess_tot + 12) =
    gdhPrimQueryBudget S b := by
  unfold gdhPrimQueryBudget
  dsimp only
  have hm : min b.q_total (min b.q_on S.N_sess_tot) = min (min b.q_on b.q_total) S.N_sess_tot := by
    omega
  rw [hm]

/-- Evaluating `fgAuth1KeyGapDhProg` against a `b`-bounded `Auth` adversary makes at most
    `gdhPrimQueryBudget S b` primitive queries. -/
theorem fgAuth1KeyGapDhProg_primBounded_gdhPrimQueryBudget (S : Setup) (K : Nat)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) (U V : Bytes) :
    ((fgAuth1KeyGapDhProg S K).eval (fun _ => A.1.run) (U, V)).IsQueryBoundP
      (fun q => isPrimQuery q = true) (gdhPrimQueryBudget S b) :=
  (fgAuth1KeyGapDhProg_primBounded_split S K b.q_total (min b.q_on S.N_sess_tot) (fun _ => A.1.run)
    (authAdv_gameBound S b A) (fun _ => authAdv_sessionBound_on S b A) U V).mono
    (le_of_eq (a1g_split_prim_eq_gdhPrimQueryBudget S b))

section BilinearGdh
open Proofs.SignalPqxdh.Security Proofs.SignalPqxdh.Security.FgGapDh

abbrev a1g_isDdhGdh (q : FgGapDh.GdhSimSpec.Domain) : Prop := q.isRight = true
theorem ddhGdh_pure {α : Type} (x : α) (n : ℕ) :
    IsQueryBoundP (pure x : OracleComp FgGapDh.GdhSimSpec α) a1g_isDdhGdh n :=
  isQueryBoundP_pure _ x n

theorem ddhGdh_bind0 {α β : Type} {n : ℕ}
    {mx : OracleComp FgGapDh.GdhSimSpec α} {f : α → OracleComp FgGapDh.GdhSimSpec β}
    (h1 : IsQueryBoundP mx a1g_isDdhGdh 0)
    (h2 : ∀ x ∈ support mx, IsQueryBoundP (f x) a1g_isDdhGdh n) :
    IsQueryBoundP (mx >>= f) a1g_isDdhGdh n := by
  simpa using isQueryBoundP_bind h1 h2

theorem ddhGdh_primQ (t : PrimQuery) :
    IsQueryBoundP (FgGapDh.primGdhQ t) a1g_isDdhGdh 0 :=
  (isQueryBoundP_query_iff (spec := FgGapDh.GdhSimSpec) a1g_isDdhGdh
    (Sum.inl (Sum.inr t)) 0).2 (fun h => by cases h)

theorem ddhGdh_embedPrim {α : Type} (mx : OracleComp (unifSpec + primSpec) α) :
    IsQueryBoundP (FgGapDh.embedPrim (spec := gapDhOracleSpec) mx) a1g_isDdhGdh 0 := by
  induction mx using OracleComp.inductionOn with
  | pure a => exact ddhGdh_pure a 0
  | query_bind t r ih =>
    change IsQueryBoundP
      (liftM (OracleSpec.query (spec := FgGapDh.GdhSimSpec) (Sum.inl t)) >>=
        fun u => FgGapDh.embedPrim (spec := gapDhOracleSpec) (r u))
      a1g_isDdhGdh 0
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (fun h => by cases h), ih⟩

theorem ddhGdh_unif {α : Type} (mx : OracleComp unifSpec α) :
    IsQueryBoundP (FgGapDh.unifGdh mx) a1g_isDdhGdh 0 :=
  ddhGdh_embedPrim (FgGapDh.embedUnif mx)

theorem ddhGdh_ddhQ (X Y Z : Bytes) :
    IsQueryBoundP (FgGapDh.ddhGdhQ X Y Z) a1g_isDdhGdh 1 :=
  (isQueryBoundP_query_iff (spec := FgGapDh.GdhSimSpec) a1g_isDdhGdh
    (Sum.inr (X, Y, Z)) 1).2 (fun _ => Nat.zero_lt_one)

def a1g_isSecPoS : FgGapDh.FgPoS → Bool
  | .secret _ _ => true
  | .pair _ _ _ _ => false

def a1g_isSecOpt : Option FgGapDh.FgPoS → Bool
  | none => true
  | some p => a1g_isSecPoS p

def a1g_isSecPatch (e : FgGapDh.FgPatchEntry) : Bool :=
  a1g_isSecPoS e.pos1 && a1g_isSecPoS e.pos2 && a1g_isSecPoS e.pos3 && a1g_isSecOpt e.pos4?

def a1g_isSecRoot (e : FgRootEntry) : Bool :=
  a1g_isSecPoS e.dhPos

theorem ddhGdh_mkSecretPos (z : Bytes) :
    IsQueryBoundP (FgGapDh.mkSecretPos z) a1g_isDdhGdh 0 ∧
      ∀ p ∈ support (FgGapDh.mkSecretPos z), a1g_isSecPoS p = true := by
  unfold FgGapDh.mkSecretPos
  refine ⟨ddhGdh_bind0 (ddhGdh_primQ _) (fun _ _ => ddhGdh_pure _ 0), ?_⟩
  intro p hp
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hp
  rcases hp with ⟨_, _, rfl⟩
  rfl

theorem ddhGdh_mkPairPos (pk1 pk2 : Bytes) :
    IsQueryBoundP (FgGapDh.mkPairPos pk1 pk2) a1g_isDdhGdh 0 := by
  unfold FgGapDh.mkPairPos
  exact ddhGdh_bind0 (ddhGdh_primQ _) fun _ _ =>
    ddhGdh_bind0 (ddhGdh_primQ _) fun _ _ => ddhGdh_pure _ 0

theorem ddhGdh_twoSide (sk1 sk2 pk1 pk2 : Bytes) :
    IsQueryBoundP (FgGapDh.computeTwoSideOrPairPos sk1 sk2 pk1 pk2) a1g_isDdhGdh 0 := by
  unfold FgGapDh.computeTwoSideOrPairPos
  split_ifs
  · exact ddhGdh_bind0 (ddhGdh_primQ _) fun z _ => (ddhGdh_mkSecretPos z).1
  · exact ddhGdh_bind0 (ddhGdh_primQ _) fun z _ => (ddhGdh_mkSecretPos z).1
  · exact ddhGdh_mkPairPos pk1 pk2

theorem ddhGdh_optPos (sk1 pk1 : Bytes) (o : Option (Bytes × Bytes)) :
    IsQueryBoundP (FgGapDh.computeOptPos sk1 pk1 o) a1g_isDdhGdh 0 := by
  rcases o with _ | ⟨sk2, pk2⟩
  · exact ddhGdh_pure _ 0
  · dsimp only [FgGapDh.computeOptPos]
    rw [map_eq_bind_pure_comp]
    exact ddhGdh_bind0 (ddhGdh_twoSide _ _ _ _) fun _ _ => ddhGdh_pure _ 0

theorem ddhGdh_ddhEq_le (p1 p2 : FgGapDh.FgPoS) :
    IsQueryBoundP (FgGapDh.ddhEqGdh p1 p2) a1g_isDdhGdh 1 := by
  cases p1 <;> cases p2 <;> simp only [FgGapDh.ddhEqGdh]
  · exact ddhGdh_pure _ 1
  · split_ifs; exacts [ddhGdh_ddhQ _ _ _, ddhGdh_pure _ 1]
  · split_ifs; exacts [ddhGdh_ddhQ _ _ _, ddhGdh_pure _ 1]
  · exact ddhGdh_pure _ 1

theorem ddhGdh_ddhEq_sec (p1 p2 : FgGapDh.FgPoS)
    (h1 : a1g_isSecPoS p1 = true) (h2 : a1g_isSecPoS p2 = true) :
    IsQueryBoundP (FgGapDh.ddhEqGdh p1 p2) a1g_isDdhGdh 0 := by
  cases p1 with
  | secret z1 c1 =>
    cases p2 with
    | secret z2 c2 => exact ddhGdh_pure _ 0
    | pair _ _ _ _ => cases h2
  | pair _ _ _ _ => cases h1

theorem ddhGdh_ddhEqOpt_le (o1 o2 : Option FgGapDh.FgPoS) :
    IsQueryBoundP (FgGapDh.ddhEqOptGdh o1 o2) a1g_isDdhGdh 1 := by
  cases o1 <;> cases o2 <;> simp only [FgGapDh.ddhEqOptGdh]
  · exact ddhGdh_pure _ 1
  · exact ddhGdh_pure _ 1
  · exact ddhGdh_pure _ 1
  · exact ddhGdh_ddhEq_le _ _

theorem ddhGdh_ddhEqOpt_sec (o1 o2 : Option FgGapDh.FgPoS)
    (h1 : a1g_isSecOpt o1 = true) (h2 : a1g_isSecOpt o2 = true) :
    IsQueryBoundP (FgGapDh.ddhEqOptGdh o1 o2) a1g_isDdhGdh 0 := by
  cases o1 with
  | none =>
    cases o2 with
    | none => exact ddhGdh_pure _ 0
    | some _ => exact ddhGdh_pure _ 0
  | some p1 =>
    cases o2 with
    | none => exact ddhGdh_pure _ 0
    | some p2 => exact ddhGdh_ddhEq_sec p1 p2 h1 h2

theorem ddhGdh_entryMatches_le (p1 p2 p3 : FgGapDh.FgPoS) (p4 : Option FgGapDh.FgPoS)
    (ss : Bytes) (e : FgGapDh.FgPatchEntry) :
    IsQueryBoundP (FgGapDh.fgEntryMatches p1 p2 p3 p4 ss e) a1g_isDdhGdh 4 := by
  unfold FgGapDh.fgEntryMatches
  split_ifs
  · exact ddhGdh_pure _ 4
  · refine (isQueryBoundP_bind (n := 1) (m := 3) (ddhGdh_ddhEq_le p1 e.pos1) fun _ _ => ?_).mono (by omega)
    refine (isQueryBoundP_bind (n := 1) (m := 2) (ddhGdh_ddhEq_le p2 e.pos2) fun _ _ => ?_).mono (by omega)
    refine (isQueryBoundP_bind (n := 1) (m := 1) (ddhGdh_ddhEq_le p3 e.pos3) fun _ _ => ?_).mono (by omega)
    exact (isQueryBoundP_bind (n := 1) (m := 0) (ddhGdh_ddhEqOpt_le p4 e.pos4?) fun _ _ =>
      ddhGdh_pure _ 0).mono (by omega)

theorem ddhGdh_entryMatches_sec (p1 p2 p3 : FgGapDh.FgPoS) (p4 : Option FgGapDh.FgPoS)
    (ss : Bytes) (e : FgGapDh.FgPatchEntry)
    (h1 : a1g_isSecPoS p1 = true) (h2 : a1g_isSecPoS p2 = true) (h3 : a1g_isSecPoS p3 = true)
    (h4 : a1g_isSecOpt p4 = true) (he : a1g_isSecPatch e = true) :
    IsQueryBoundP (FgGapDh.fgEntryMatches p1 p2 p3 p4 ss e) a1g_isDdhGdh 0 := by
  unfold FgGapDh.fgEntryMatches
  split_ifs
  · exact ddhGdh_pure _ 0
  · simp only [a1g_isSecPatch, Bool.and_eq_true] at he
    rcases he with ⟨⟨⟨he1, he2⟩, he3⟩, he4⟩
    exact ddhGdh_bind0 (ddhGdh_ddhEq_sec p1 e.pos1 h1 he1) fun _ _ =>
      ddhGdh_bind0 (ddhGdh_ddhEq_sec p2 e.pos2 h2 he2) fun _ _ =>
        ddhGdh_bind0 (ddhGdh_ddhEq_sec p3 e.pos3 h3 he3) fun _ _ =>
          ddhGdh_bind0 (ddhGdh_ddhEqOpt_sec p4 e.pos4? h4 he4) fun _ _ => ddhGdh_pure _ 0

theorem ddhGdh_rootMatches_le (rk : Bytes) (p : FgGapDh.FgPoS) (e : FgRootEntry) :
    IsQueryBoundP (fgRootEntryMatches rk p e) a1g_isDdhGdh 1 := by
  unfold fgRootEntryMatches
  split_ifs
  · exact ddhGdh_pure _ 1
  · exact ddhGdh_ddhEq_le p e.dhPos

theorem ddhGdh_rootMatches_sec (rk : Bytes) (p : FgGapDh.FgPoS) (e : FgRootEntry)
    (hp : a1g_isSecPoS p = true) (he : a1g_isSecRoot e = true) :
    IsQueryBoundP (fgRootEntryMatches rk p e) a1g_isDdhGdh 0 := by
  unfold fgRootEntryMatches
  split_ifs
  · exact ddhGdh_pure _ 0
  · exact ddhGdh_ddhEq_sec p e.dhPos hp he

theorem ddhGdh_findM_weight {α : Type} (p : α → OracleComp FgGapDh.GdhSimSpec Bool)
    (w : α → ℕ) (hw : ∀ x, IsQueryBoundP (p x) a1g_isDdhGdh (w x)) :
    ∀ L : List α, IsQueryBoundP (FgGapDh.findMGdh p L) a1g_isDdhGdh ((L.map w).sum)
  | [] => ddhGdh_pure _ 0
  | x :: xs => by
    unfold FgGapDh.findMGdh
    refine (isQueryBoundP_bind (n := w x) (m := (xs.map w).sum) (hw x) fun b _ => ?_).mono
      (by simp)
    cases b
    · exact ddhGdh_findM_weight p w hw xs
    · exact ddhGdh_pure _ ((xs.map w).sum)

theorem ddhGdh_findMapM_len {α : Type} (f : α → OracleComp FgGapDh.GdhSimSpec Bytes)
    (hf : ∀ x, IsQueryBoundP (f x) a1g_isDdhGdh 0) (U V : Bytes) :
    ∀ L : List α, IsQueryBoundP (FgGapDh.findMapMGdh f U V L) a1g_isDdhGdh L.length
  | [] => ddhGdh_pure _ 0
  | x :: xs => by
    unfold FgGapDh.findMapMGdh
    refine ddhGdh_bind0 (hf x) fun z _ => ?_
    refine (isQueryBoundP_bind (n := 1) (m := xs.length) (ddhGdh_ddhQ U V z) fun b _ => ?_).mono
      (by simp; omega)
    cases b
    · exact ddhGdh_findMapM_len f hf U V xs
    · exact ddhGdh_pure _ xs.length

theorem ddhGdh_spkPows :
    ∀ L : List ((Nat × Nat) × SpkBundleEntry), IsQueryBoundP (FgGapDh.spkPowsGdh L) a1g_isDdhGdh 0
  | [] => ddhGdh_pure _ 0
  | (_, b) :: xs => by
    unfold FgGapDh.spkPowsGdh
    exact ddhGdh_bind0 (ddhGdh_primQ _) fun _ _ =>
      ddhGdh_bind0 (ddhGdh_spkPows xs) fun _ _ => ddhGdh_pure _ 0

theorem a1g_sum_map_const_eq {α : Type} (c : ℕ) :
    ∀ L : List α, (L.map (fun _ => c)).sum = c * L.length
  | [] => by simp
  | _ :: xs => by
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [a1g_sum_map_const_eq c xs]
    ring

theorem a1g_sum_map_ite_not_countP {α : Type} (c : ℕ) (q : α → Bool) :
    ∀ L : List α, (L.map (fun x => if q x then 0 else c)).sum = c * L.countP (fun x => !q x)
  | [] => by simp
  | x :: xs => by
    cases hq : q x
    · simp only [List.map_cons, List.sum_cons, List.countP_cons, hq, Bool.false_eq_true,
        ↓reduceIte, Bool.not_false]
      rw [a1g_sum_map_ite_not_countP c q xs]; ring
    · simp only [List.map_cons, List.sum_cons, List.countP_cons, hq, ↓reduceIte,
        Bool.not_true, Bool.false_eq_true, Nat.zero_add]
      exact a1g_sum_map_ite_not_countP c q xs

theorem a1g_take_countP_le {α : Type} (q : α → Bool) :
    ∀ (k : ℕ) (L : List α), (L.take k).countP q ≤ L.countP q
  | 0, _ => by simp
  | _ + 1, [] => by simp
  | k + 1, x :: xs => by
    simp only [List.take_succ_cons, List.countP_cons]
    have := a1g_take_countP_le q k xs
    omega

theorem a1g_countP_add_countP_not {α : Type} (q : α → Bool) :
    ∀ L : List α, L.countP q + L.countP (fun x => !q x) = L.length
  | [] => by simp
  | x :: xs => by
    have ih := a1g_countP_add_countP_not q xs
    cases hq : q x
    · simp only [List.countP_cons, List.length_cons, hq, Bool.false_eq_true, ↓reduceIte,
        Bool.not_false]
      omega
    · simp only [List.countP_cons, List.length_cons, hq, ↓reduceIte, Bool.not_true,
        Bool.false_eq_true]
      omega

theorem ddhGdh_fgPatch_ro (maxLen : ℕ) (p1 p2 p3 : FgGapDh.FgPoS)
    (p4 : Option FgGapDh.FgPoS) (ss : Bytes) (L : List FgGapDh.FgPatchEntry)
    (h1 : a1g_isSecPoS p1 = true) (h2 : a1g_isSecPoS p2 = true) (h3 : a1g_isSecPoS p3 = true)
    (h4 : a1g_isSecOpt p4 = true) :
    IsQueryBoundP (FgGapDh.fgPatch maxLen p1 p2 p3 p4 ss L) a1g_isDdhGdh
      (4 * L.countP (fun e => !a1g_isSecPatch e)) ∧
    ∀ out ∈ support (FgGapDh.fgPatch maxLen p1 p2 p3 p4 ss L),
      out.2.countP a1g_isSecPatch ≤ L.countP a1g_isSecPatch + 1 ∧
      out.2.countP (fun e => !a1g_isSecPatch e) = L.countP (fun e => !a1g_isSecPatch e) := by
  unfold FgGapDh.fgPatch
  have hFind : IsQueryBoundP
      (FgGapDh.findMGdh (FgGapDh.fgEntryMatches p1 p2 p3 p4 ss) (L.take maxLen)) a1g_isDdhGdh
      (4 * L.countP (fun e => !a1g_isSecPatch e)) := by
    refine (ddhGdh_findM_weight _ (fun e => if a1g_isSecPatch e then 0 else 4) (fun e => ?_)
      (L.take maxLen)).mono ?_
    · split_ifs with he
      · exact ddhGdh_entryMatches_sec p1 p2 p3 p4 ss e h1 h2 h3 h4 he
      · exact ddhGdh_entryMatches_le p1 p2 p3 p4 ss e
    · rw [a1g_sum_map_ite_not_countP]
      exact Nat.mul_le_mul_left 4 (a1g_take_countP_le _ maxLen L)
  refine ⟨(isQueryBoundP_bind (n := 4 * L.countP (fun e => !a1g_isSecPatch e)) (m := 0)
      hFind fun m _ => ?_).mono (by omega), ?_⟩
  · cases m with
    | some _ => exact ddhGdh_pure _ 0
    | none => exact ddhGdh_bind0 (ddhGdh_unif _) fun _ _ => ddhGdh_pure _ 0
  · intro out hout
    simp only [mem_support_bind_iff] at hout
    rcases hout with ⟨m, _, hm⟩
    cases m with
    | some _ =>
      simp only [support_pure, Set.mem_singleton_iff] at hm
      subst hm; exact ⟨Nat.le_succ _, rfl⟩
    | none =>
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hm
      rcases hm with ⟨dk, _, rfl⟩
      have hSec : a1g_isSecPatch { pos1 := p1, pos2 := p2, pos3 := p3, pos4? := p4, ss := ss, dk := dk } = true := by
        simp [a1g_isSecPatch, h1, h2, h3, h4]
      simp [hSec]

theorem ddhGdh_fgPatch_sess (maxLen : ℕ) (p1 p2 p3 : FgGapDh.FgPoS)
    (p4 : Option FgGapDh.FgPoS) (ss : Bytes) (L : List FgGapDh.FgPatchEntry) :
    IsQueryBoundP (FgGapDh.fgPatch maxLen p1 p2 p3 p4 ss L) a1g_isDdhGdh
      (4 * (L.countP a1g_isSecPatch + L.countP (fun e => !a1g_isSecPatch e))) ∧
    ∀ out ∈ support (FgGapDh.fgPatch maxLen p1 p2 p3 p4 ss L),
      (out.2.countP a1g_isSecPatch = L.countP a1g_isSecPatch ∧
        out.2.countP (fun e => !a1g_isSecPatch e) = L.countP (fun e => !a1g_isSecPatch e)) ∨
      (out.2.countP a1g_isSecPatch = L.countP a1g_isSecPatch + 1 ∧
        out.2.countP (fun e => !a1g_isSecPatch e) = L.countP (fun e => !a1g_isSecPatch e)) ∨
      (out.2.countP a1g_isSecPatch = L.countP a1g_isSecPatch ∧
        out.2.countP (fun e => !a1g_isSecPatch e) = L.countP (fun e => !a1g_isSecPatch e) + 1) := by
  unfold FgGapDh.fgPatch
  have hFind : IsQueryBoundP
      (FgGapDh.findMGdh (FgGapDh.fgEntryMatches p1 p2 p3 p4 ss) (L.take maxLen)) a1g_isDdhGdh
      (4 * (L.countP a1g_isSecPatch + L.countP (fun e => !a1g_isSecPatch e))) := by
    refine (ddhGdh_findM_weight _ (fun _ => 4) (fun e => ddhGdh_entryMatches_le p1 p2 p3 p4 ss e)
      (L.take maxLen)).mono ?_
    rw [a1g_sum_map_const_eq, a1g_countP_add_countP_not]
    exact Nat.mul_le_mul_left 4 (List.length_take_le' maxLen L)
  refine ⟨(isQueryBoundP_bind (n := 4 * (L.countP a1g_isSecPatch + L.countP (fun e => !a1g_isSecPatch e)))
      (m := 0) hFind fun m _ => ?_).mono (by omega), ?_⟩
  · cases m with
    | some _ => exact ddhGdh_pure _ 0
    | none => exact ddhGdh_bind0 (ddhGdh_unif _) fun _ _ => ddhGdh_pure _ 0
  · intro out hout
    simp only [mem_support_bind_iff] at hout
    rcases hout with ⟨m, _, hm⟩
    cases m with
    | some _ =>
      simp only [support_pure, Set.mem_singleton_iff] at hm
      subst hm; exact Or.inl ⟨rfl, rfl⟩
    | none =>
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hm
      rcases hm with ⟨dk, _, rfl⟩
      cases hSec : a1g_isSecPatch { pos1 := p1, pos2 := p2, pos3 := p3, pos4? := p4, ss := ss, dk := dk }
      · exact Or.inr (Or.inr (by simp [hSec]))
      · exact Or.inr (Or.inl (by simp [hSec]))

theorem ddhGdh_fgRootPatch_ro (maxLen : ℕ) (rk : Bytes) (p : FgGapDh.FgPoS)
    (L : List FgRootEntry) (hp : a1g_isSecPoS p = true) :
    IsQueryBoundP (fgRootPatch maxLen rk p L) a1g_isDdhGdh
      (L.countP (fun e => !a1g_isSecRoot e)) ∧
    ∀ out ∈ support (fgRootPatch maxLen rk p L),
      out.2.countP a1g_isSecRoot ≤ L.countP a1g_isSecRoot + 1 ∧
      out.2.countP (fun e => !a1g_isSecRoot e) = L.countP (fun e => !a1g_isSecRoot e) := by
  unfold fgRootPatch
  have hFind : IsQueryBoundP
      (FgGapDh.findMGdh (fgRootEntryMatches rk p) (L.take maxLen)) a1g_isDdhGdh
      (L.countP (fun e => !a1g_isSecRoot e)) := by
    refine (ddhGdh_findM_weight _ (fun e => if a1g_isSecRoot e then 0 else 1) (fun e => ?_)
      (L.take maxLen)).mono ?_
    · split_ifs with he
      · exact ddhGdh_rootMatches_sec rk p e hp he
      · exact ddhGdh_rootMatches_le rk p e
    · rw [a1g_sum_map_ite_not_countP, Nat.one_mul]
      exact a1g_take_countP_le _ maxLen L
  refine ⟨(isQueryBoundP_bind (n := L.countP (fun e => !a1g_isSecRoot e)) (m := 0)
      hFind fun m _ => ?_).mono (by omega), ?_⟩
  · cases m with
    | some _ => exact ddhGdh_pure _ 0
    | none =>
      exact ddhGdh_bind0 (ddhGdh_unif _) fun _ _ =>
        ddhGdh_bind0 (ddhGdh_unif _) fun _ _ => ddhGdh_pure _ 0
  · intro out hout
    simp only [mem_support_bind_iff] at hout
    rcases hout with ⟨m, _, hm⟩
    cases m with
    | some _ =>
      simp only [support_pure, Set.mem_singleton_iff] at hm
      subst hm; exact ⟨Nat.le_succ _, rfl⟩
    | none =>
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hm
      rcases hm with ⟨rk1, _, ck1, _, rfl⟩
      have hSec : a1g_isSecRoot { rk := rk, dhPos := p, rk1 := rk1, ck1_0 := ck1 } = true := hp
      simp [hSec]

theorem ddhGdh_fgRootPatch_sess (maxLen : ℕ) (rk : Bytes) (p : FgGapDh.FgPoS)
    (L : List FgRootEntry) :
    IsQueryBoundP (fgRootPatch maxLen rk p L) a1g_isDdhGdh
      (L.countP a1g_isSecRoot + L.countP (fun e => !a1g_isSecRoot e)) ∧
    ∀ out ∈ support (fgRootPatch maxLen rk p L),
      (out.2.countP a1g_isSecRoot = L.countP a1g_isSecRoot ∧
        out.2.countP (fun e => !a1g_isSecRoot e) = L.countP (fun e => !a1g_isSecRoot e)) ∨
      (out.2.countP a1g_isSecRoot = L.countP a1g_isSecRoot + 1 ∧
        out.2.countP (fun e => !a1g_isSecRoot e) = L.countP (fun e => !a1g_isSecRoot e)) ∨
      (out.2.countP a1g_isSecRoot = L.countP a1g_isSecRoot ∧
        out.2.countP (fun e => !a1g_isSecRoot e) = L.countP (fun e => !a1g_isSecRoot e) + 1) := by
  unfold fgRootPatch
  have hFind : IsQueryBoundP
      (FgGapDh.findMGdh (fgRootEntryMatches rk p) (L.take maxLen)) a1g_isDdhGdh
      (L.countP a1g_isSecRoot + L.countP (fun e => !a1g_isSecRoot e)) := by
    refine (ddhGdh_findM_weight _ (fun _ => 1) (fun e => ddhGdh_rootMatches_le rk p e)
      (L.take maxLen)).mono ?_
    rw [a1g_sum_map_const_eq, Nat.one_mul, a1g_countP_add_countP_not]
    exact List.length_take_le' maxLen L
  refine ⟨(isQueryBoundP_bind (n := L.countP a1g_isSecRoot + L.countP (fun e => !a1g_isSecRoot e))
      (m := 0) hFind fun m _ => ?_).mono (by omega), ?_⟩
  · cases m with
    | some _ => exact ddhGdh_pure _ 0
    | none =>
      exact ddhGdh_bind0 (ddhGdh_unif _) fun _ _ =>
        ddhGdh_bind0 (ddhGdh_unif _) fun _ _ => ddhGdh_pure _ 0
  · intro out hout
    simp only [mem_support_bind_iff] at hout
    rcases hout with ⟨m, _, hm⟩
    cases m with
    | some _ =>
      simp only [support_pure, Set.mem_singleton_iff] at hm
      subst hm; exact Or.inl ⟨rfl, rfl⟩
    | none =>
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hm
      rcases hm with ⟨rk1, _, ck1, _, rfl⟩
      cases hSec : a1g_isSecRoot { rk := rk, dhPos := p, rk1 := rk1, ck1_0 := ck1 }
      · exact Or.inr (Or.inr (by simp [hSec]))
      · exact Or.inr (Or.inl (by simp [hSec]))

def a1g_rDone {S : Setup} (st : FgAuthSimState S) : ℕ := st.fgL.countP a1g_isSecPatch
def a1g_sDone {S : Setup} (st : FgAuthSimState S) : ℕ := st.fgL.countP (fun e => !a1g_isSecPatch e)
def a1g_rtRDone {S : Setup} (st : FgAuthSimState S) : ℕ := st.fgRootL.countP a1g_isSecRoot
def a1g_rtSDone {S : Setup} (st : FgAuthSimState S) : ℕ := st.fgRootL.countP (fun e => !a1g_isSecRoot e)

def a1g_phiMain (rD sD rR sR : ℕ) : ℕ :=
  4 * rD * sR + 4 * rR * (sD + sR) + 4 * sD * sR + 2 * sR * (sR - 1)

def a1g_phiRoot (rtRD rtSD rtRR sR : ℕ) : ℕ :=
  rtRD * sR + rtRR * (rtSD + sR) + rtSD * sR + sR * (sR - 1)

def a1g_authPhi {S : Setup} (st : FgAuthSimState S) (rR rtRR sR : ℕ) : ℕ :=
  a1g_phiMain (a1g_rDone st) (a1g_sDone st) rR sR + a1g_phiRoot (a1g_rtRDone st) (a1g_rtSDone st) rtRR sR

theorem a1g_phiMain_ro (rD sD r' sR rD' : ℕ) (h : rD' ≤ rD + 1) :
    4 * sD + a1g_phiMain rD' sD r' sR ≤ a1g_phiMain rD sD (r' + 1) sR := by
  unfold a1g_phiMain
  have h1 : 4 * rD' * sR ≤ 4 * (rD + 1) * sR := Nat.mul_le_mul_right sR (by omega)
  nlinarith

theorem a1g_phiRoot_ro (rtRD rtSD rt' sR rtRD' : ℕ) (h : rtRD' ≤ rtRD + 1) :
    rtSD + a1g_phiRoot rtRD' rtSD rt' sR ≤ a1g_phiRoot rtRD rtSD (rt' + 1) sR := by
  unfold a1g_phiRoot
  have h1 : rtRD' * sR ≤ (rtRD + 1) * sR := Nat.mul_le_mul_right sR h
  nlinarith

theorem a1g_mul_pred_succ (s' : ℕ) : (s' + 1) * s' = s' * (s' - 1) + 2 * s' := by
  cases s' with
  | zero => rfl
  | succ k => simp; ring

theorem a1g_phiMain_sess (rD sD rR s' rD' sD' : ℕ)
    (h : (rD' = rD ∧ sD' = sD) ∨ (rD' = rD + 1 ∧ sD' = sD) ∨ (rD' = rD ∧ sD' = sD + 1)) :
    4 * (rD + sD) + a1g_phiMain rD' sD' rR s' ≤ a1g_phiMain rD sD rR (s' + 1) := by
  unfold a1g_phiMain
  have hm := a1g_mul_pred_succ s'
  have hs : s' + 1 - 1 = s' := Nat.add_sub_cancel s' 1
  rw [hs]
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> nlinarith

theorem a1g_phiRoot_sess (rtRD rtSD rtRR s' rtRD' rtSD' : ℕ)
    (h : (rtRD' = rtRD ∧ rtSD' = rtSD) ∨
         (rtRD' = rtRD + 1 ∧ rtSD' = rtSD) ∨
         (rtRD' = rtRD ∧ rtSD' = rtSD + 1)) :
    (rtRD + rtSD) + a1g_phiRoot rtRD' rtSD' rtRR s' ≤ a1g_phiRoot rtRD rtSD rtRR (s' + 1) := by
  unfold a1g_phiRoot
  have hm := a1g_mul_pred_succ s'
  have hs : s' + 1 - 1 = s' := Nat.add_sub_cancel s' 1
  rw [hs, hm]
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> nlinarith

theorem ddhGdh_step_bind0 {S : Setup} {α : Type} {n : ℕ}
    {mx : OracleComp FgGapDh.GdhSimSpec α}
    {k : α → OracleComp FgGapDh.GdhSimSpec (AuthResponse × FgAuthSimState S)}
    {P : FgAuthSimState S → Prop}
    (h1 : IsQueryBoundP mx a1g_isDdhGdh 0)
    (h2 : ∀ x ∈ support mx, IsQueryBoundP (k x) a1g_isDdhGdh n ∧ ∀ p ∈ support (k x), P p.2) :
    IsQueryBoundP (mx >>= k) a1g_isDdhGdh n ∧ ∀ p ∈ support (mx >>= k), P p.2 := by
  refine ⟨ddhGdh_bind0 h1 (fun x hx => (h2 x hx).1), ?_⟩
  intro p hp
  rw [mem_support_bind_iff] at hp
  rcases hp with ⟨x, hx, hp⟩
  exact (h2 x hx).2 p hp

theorem ddhGdh_step_pure {S : Setup} (r : AuthResponse) (st : FgAuthSimState S)
    (n : ℕ) {P : FgAuthSimState S → Prop} (hP : P st) :
    IsQueryBoundP (pure (r, st) : OracleComp FgGapDh.GdhSimSpec (AuthResponse × FgAuthSimState S))
      a1g_isDdhGdh n ∧
    ∀ p ∈ support (pure (r, st) : OracleComp FgGapDh.GdhSimSpec (AuthResponse × FgAuthSimState S)),
      P p.2 := by
  refine ⟨ddhGdh_pure _ n, fun p hp => ?_⟩
  simp only [support_pure, Set.mem_singleton_iff] at hp
  subst hp; exact hP

def a1g_RoStepPost {S : Setup} (st st' : FgAuthSimState S) : Prop :=
  a1g_rDone st' ≤ a1g_rDone st + 1 ∧ a1g_sDone st' = a1g_sDone st ∧ st'.fgRootL = st.fgRootL

theorem ddhGdh_fgRoQueryAuthGdh {S : Setup} (maxLen : ℕ) (secrets : Bytes)
    (st : FgAuthSimState S) :
    IsQueryBoundP (fgRoQueryAuthGdh maxLen secrets st) a1g_isDdhGdh (4 * a1g_sDone st) ∧
    ∀ p ∈ support (fgRoQueryAuthGdh maxLen secrets st), a1g_RoStepPost st p.2 := by
  dsimp only [fgRoQueryAuthGdh]
  cases parseRoSecrets secrets with
  | none =>
    cases st.rawRoCache.find? (fun (s, _) => s == secrets) with
    | some kv =>
      rcases kv with ⟨_, dk⟩
      exact ddhGdh_step_pure _ _ _ ⟨Nat.le_succ _, rfl, rfl⟩
    | none =>
      exact ddhGdh_step_bind0 (ddhGdh_unif _) fun _ _ =>
        ddhGdh_step_pure _ _ _ ⟨Nat.le_succ _, rfl, rfl⟩
  | some tup =>
    rcases tup with ⟨dh1, dh2, dh3, dh4?, ss⟩
    dsimp only
    refine ddhGdh_step_bind0 (ddhGdh_mkSecretPos dh1).1 fun p1 hp1 => ?_
    refine ddhGdh_step_bind0 (ddhGdh_mkSecretPos dh2).1 fun p2 hp2 => ?_
    refine ddhGdh_step_bind0 (ddhGdh_mkSecretPos dh3).1 fun p3 hp3 => ?_
    have h1 := (ddhGdh_mkSecretPos dh1).2 p1 hp1
    have h2 := (ddhGdh_mkSecretPos dh2).2 p2 hp2
    have h3 := (ddhGdh_mkSecretPos dh3).2 p3 hp3
    cases dh4? with
    | none =>
      dsimp only
      rw [pure_bind]
      have hP := ddhGdh_fgPatch_ro maxLen p1 p2 p3 none ss st.fgL h1 h2 h3 rfl
      refine ⟨(isQueryBoundP_bind (n := 4 * a1g_sDone st) (m := 0) hP.1
        fun _ _ => ddhGdh_pure _ 0).mono (by omega), ?_⟩
      intro p hp
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hp
      rcases hp with ⟨⟨dk, fgL'⟩, hout, rfl⟩
      exact ⟨(hP.2 _ hout).1, (hP.2 _ hout).2, rfl⟩
    | some dh4 =>
      dsimp only
      rw [map_eq_bind_pure_comp, bind_assoc]
      refine ddhGdh_step_bind0 (ddhGdh_mkSecretPos dh4).1 fun q4 hq4 => ?_
      simp only [Function.comp_apply, pure_bind]
      have h4 : a1g_isSecOpt (some q4) = true := (ddhGdh_mkSecretPos dh4).2 q4 hq4
      have hP := ddhGdh_fgPatch_ro maxLen p1 p2 p3 (some q4) ss st.fgL h1 h2 h3 h4
      refine ⟨(isQueryBoundP_bind (n := 4 * a1g_sDone st) (m := 0) hP.1
        fun _ _ => ddhGdh_pure _ 0).mono (by omega), ?_⟩
      intro p hp
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hp
      rcases hp with ⟨⟨dk, fgL'⟩, hout, rfl⟩
      exact ⟨(hP.2 _ hout).1, (hP.2 _ hout).2, rfl⟩

theorem ddhGdh_fgRoRootQueryAuthGdh {S : Setup} (maxLen : ℕ) (rk dh : Bytes)
    (st : FgAuthSimState S) :
    IsQueryBoundP (fgRoRootQueryAuthGdh maxLen rk dh st) a1g_isDdhGdh (a1g_rtSDone st) ∧
    ∀ p ∈ support (fgRoRootQueryAuthGdh maxLen rk dh st),
      a1g_rtRDone p.2 ≤ a1g_rtRDone st + 1 ∧ a1g_rtSDone p.2 = a1g_rtSDone st ∧ p.2.fgL = st.fgL := by
  unfold fgRoRootQueryAuthGdh
  refine ⟨ddhGdh_bind0 (ddhGdh_mkSecretPos dh).1 fun pos hpos =>
    (isQueryBoundP_bind (n := a1g_rtSDone st) (m := 0)
      (ddhGdh_fgRootPatch_ro maxLen rk pos st.fgRootL ((ddhGdh_mkSecretPos dh).2 pos hpos)).1
      fun _ _ => ddhGdh_pure _ 0).mono (by omega), ?_⟩
  intro p hp
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hp
  rcases hp with ⟨pos, hpos, out, hout, rfl⟩
  have hP := (ddhGdh_fgRootPatch_ro maxLen rk pos st.fgRootL
    ((ddhGdh_mkSecretPos dh).2 pos hpos)).2 out hout
  exact ⟨hP.1, hP.2, rfl⟩

def a1g_SessStepPost {S : Setup} (st st' : FgAuthSimState S) : Prop :=
  ((a1g_rDone st' = a1g_rDone st ∧ a1g_sDone st' = a1g_sDone st) ∨
   (a1g_rDone st' = a1g_rDone st + 1 ∧ a1g_sDone st' = a1g_sDone st) ∨
   (a1g_rDone st' = a1g_rDone st ∧ a1g_sDone st' = a1g_sDone st + 1)) ∧
  ((a1g_rtRDone st' = a1g_rtRDone st ∧ a1g_rtSDone st' = a1g_rtSDone st) ∨
   (a1g_rtRDone st' = a1g_rtRDone st + 1 ∧ a1g_rtSDone st' = a1g_rtSDone st) ∨
   (a1g_rtRDone st' = a1g_rtRDone st ∧ a1g_rtSDone st' = a1g_rtSDone st + 1))

theorem a1g_sessStepPost_refl {S : Setup} (st : FgAuthSimState S) : a1g_SessStepPost st st :=
  ⟨Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩

theorem ddhGdh_fgRunSendAuthGdh (useDh1 : Bool) (targetIdx : ℕ) (S : Setup) (maxLen : ℕ)
    (U : Bytes) (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (st : FgAuthSimState S) :
    IsQueryBoundP (fgRunSendAuthGdh useDh1 targetIdx S maxLen U sid u bundle m0 m1 st) a1g_isDdhGdh
      (4 * (a1g_rDone st + a1g_sDone st) + (a1g_rtRDone st + a1g_rtSDone st)) ∧
    ∀ p ∈ support (fgRunSendAuthGdh useDh1 targetIdx S maxLen U sid u bundle m0 m1 st),
      a1g_SessStepPost st p.2 := by
  dsimp only [fgRunSendAuthGdh]
  by_cases h1 : (m0.length != m1.length) = true
  · simp only [h1, ↓reduceIte]; exact ddhGdh_step_pure _ _ _ (a1g_sessStepPost_refl st)
  simp only [h1, Bool.false_eq_true, ↓reduceIte]
  by_cases h2 : st.base.usedSendSessions.contains sid = true
  · simp only [h2, ↓reduceIte]; exact ddhGdh_step_pure _ _ _ (a1g_sessStepPost_refl st)
  simp only [h2, Bool.false_eq_true, ↓reduceIte]
  cases st.base.principals.find? (fun (idx, _) => idx == u.val) with
  | none => exact ddhGdh_step_pure _ _ _ (a1g_sessStepPost_refl st)
  | some uPair =>
    rcases uPair with ⟨_, uEntry⟩
    dsimp only
    have stepIte : ∀ {c : Bool} {t e : OracleComp FgGapDh.GdhSimSpec (AuthResponse × FgAuthSimState S)},
        (IsQueryBoundP t a1g_isDdhGdh (4 * (a1g_rDone st + a1g_sDone st) + (a1g_rtRDone st + a1g_rtSDone st)) ∧
          ∀ p ∈ support t, a1g_SessStepPost st p.2) →
        (IsQueryBoundP e a1g_isDdhGdh (4 * (a1g_rDone st + a1g_sDone st) + (a1g_rtRDone st + a1g_rtSDone st)) ∧
          ∀ p ∈ support e, a1g_SessStepPost st p.2) →
        (IsQueryBoundP (if c = true then t else e) a1g_isDdhGdh
          (4 * (a1g_rDone st + a1g_sDone st) + (a1g_rtRDone st + a1g_rtSDone st)) ∧
          ∀ p ∈ support (if c = true then t else e), a1g_SessStepPost st p.2) := by
      rintro (_ | _) _ _ ht he
      · exact he
      · exact ht
    refine ddhGdh_step_bind0 (ddhGdh_embedPrim _) fun peerPrincipal? _ => ?_
    refine stepIte (ddhGdh_step_pure _ _ _ (a1g_sessStepPost_refl st)) ?_
    refine ddhGdh_step_bind0 (ddhGdh_embedPrim _) fun koskOk _ => ?_
    by_cases h4 : (!koskOk) = true
    · simp only [h4, ↓reduceIte]; exact ddhGdh_step_pure _ _ _ (a1g_sessStepPost_refl st)
    simp only [h4, Bool.false_eq_true, ↓reduceIte]
    refine ddhGdh_step_bind0 (ddhGdh_unif _) fun ekASkRaw _ => ?_
    refine ddhGdh_step_bind0 (ddhGdh_unif _) fun kemCoins _ => ?_
    refine ddhGdh_step_bind0 (ddhGdh_unif _) fun ephASk _ => ?_
    refine ddhGdh_step_bind0 (ddhGdh_unif _) fun spqrCoins _ => ?_
    refine ddhGdh_step_bind0 (ddhGdh_embedPrim _) fun sigPkB _ => ?_
    refine ddhGdh_step_bind0 (ddhGdh_primQ _) fun v1 _ => ?_
    refine ddhGdh_step_bind0 (ddhGdh_primQ _) fun v2 _ => ?_
    by_cases h5 : (!(v1 && v2)) = true
    · simp only [h5, ↓reduceIte]; exact ddhGdh_step_pure _ _ _ (a1g_sessStepPost_refl st)
    simp only [h5, Bool.false_eq_true, ↓reduceIte]
    refine ddhGdh_step_bind0 (ddhGdh_primQ _) fun kemOut _ => ?_
    rcases kemOut with _ | ⟨ss, kemCt⟩
    · exact ddhGdh_step_pure _ _ _ (a1g_sessStepPost_refl st)
    dsimp only
    refine ddhGdh_step_bind0 (ddhGdh_primQ _) fun ekAPkRaw _ => ?_
    refine ddhGdh_step_bind0 (ddhGdh_embedPrim _) fun spkSk _ => ?_
    refine ddhGdh_step_bind0 (ddhGdh_twoSide _ _ _ _) fun pos1 _ => ?_
    refine ddhGdh_step_bind0 (ddhGdh_twoSide _ _ _ _) fun pos2 _ => ?_
    refine ddhGdh_step_bind0 (ddhGdh_twoSide _ _ _ _) fun pos3 _ => ?_
    refine ddhGdh_step_bind0 (ddhGdh_optPos _ _ _) fun pos4? _ => ?_
    have hPatch := ddhGdh_fgPatch_sess maxLen pos1 pos2 pos3 pos4? ss st.fgL
    refine ⟨(isQueryBoundP_bind (n := 4 * (a1g_rDone st + a1g_sDone st))
      (m := a1g_rtRDone st + a1g_rtSDone st) hPatch.1 fun dkOut _ => ?_).mono (by omega), ?_⟩
    · rcases dkOut with ⟨drKey, fgL'⟩
      refine ddhGdh_bind0 (ddhGdh_primQ _) fun ephAPk _ => ?_
      refine ddhGdh_bind0 (ddhGdh_primQ _) fun dhRatchet _ => ?_
      refine ddhGdh_bind0 (ddhGdh_mkSecretPos dhRatchet).1 fun posRatchet _ => ?_
      have hRoot := ddhGdh_fgRootPatch_sess maxLen drKey.rootKey posRatchet st.fgRootL
      refine (isQueryBoundP_bind (n := a1g_rtRDone st + a1g_rtSDone st) (m := 0) hRoot.1
        fun rkOut _ => ?_).mono (by omega)
      rcases rkOut with ⟨⟨rk1, ck1_0⟩, fgRootL'⟩
      refine ddhGdh_bind0 (ddhGdh_primQ _) fun mkSeed _ => ?_
      refine ddhGdh_bind0 (ddhGdh_primQ _) fun ck1_1 _ => ?_
      refine ddhGdh_bind0 (ddhGdh_primQ _) fun spqrOut _ => ?_
      rcases spqrOut with _ | ⟨_, spqrSalt?, pqRatchetMsg⟩
      · exact ddhGdh_pure _ 0
      · refine ddhGdh_bind0 (ddhGdh_primQ _) fun _ _ => ?_
        refine ddhGdh_bind0 (ddhGdh_primQ _) fun _ _ => ?_
        split_ifs <;> exact ddhGdh_pure _ 0
    · intro p hp
      rw [mem_support_bind_iff] at hp
      rcases hp with ⟨⟨drKey, fgL'⟩, hdk, hp⟩
      simp only [mem_support_bind_iff] at hp
      rcases hp with ⟨ephAPk, _, dhRatchet, _, posRatchet, _, ⟨⟨rk1, ck1_0⟩, fgRootL'⟩, hrk,
        mkSeed, _, ck1_1, _, spqrOut, _, hp⟩
      rcases spqrOut with _ | ⟨_, spqrSalt?, pqRatchetMsg⟩
      · simp only [support_pure, Set.mem_singleton_iff] at hp
        subst hp; exact a1g_sessStepPost_refl st
      · simp only [mem_support_bind_iff] at hp
        rcases hp with ⟨_, _, _, _, hp⟩
        have hM := hPatch.2 (drKey, fgL') hdk
        have hR := (ddhGdh_fgRootPatch_sess maxLen drKey.rootKey posRatchet st.fgRootL).2
          ((rk1, ck1_0), fgRootL') hrk
        split_ifs at hp <;> {
          simp only [support_pure, Set.mem_singleton_iff] at hp
          subst hp
          exact ⟨hM, hR⟩
        }

theorem ddhGdh_fgFinishRecvStep2AuthGdh_qb (S : Setup) (k : Fin S.N_id) (j : Fin S.N_recv)
    (msg : PreKeyMsg) (kEntry : PrincipalEntry)
    (drKey : DRKey) (fgL' : List FgGapDh.FgPatchEntry)
    (rk1 : Bytes) (ck1_1 : Bytes) (fgRootL' : List FgRootEntry)
    (mkSeed : Bytes) (spqrSalt? : Option Bytes)
    (updBase : AuthState S → AuthState S)
    (st : FgAuthSimState S) :
    IsQueryBoundP (fgFinishRecvStep2AuthGdh S k j msg kEntry drKey fgL' rk1 ck1_1 fgRootL'
      mkSeed spqrSalt? updBase st) a1g_isDdhGdh 0 := by
  unfold fgFinishRecvStep2AuthGdh
  refine ddhGdh_bind0 (ddhGdh_primQ _) fun _ _ => ?_
  refine ddhGdh_bind0 (ddhGdh_primQ _) fun pt? _ => ?_
  cases pt? with
  | none => exact ddhGdh_pure _ 0
  | some _ =>
    refine ddhGdh_bind0 (ddhGdh_embedPrim _) fun sender? _ => ?_
    cases sender? <;> exact ddhGdh_pure _ 0

theorem ddhGdh_fgFinishRecvStep2AuthGdh_supp (S : Setup) (k : Fin S.N_id) (j : Fin S.N_recv)
    (msg : PreKeyMsg) (kEntry : PrincipalEntry)
    (drKey : DRKey) (fgL' : List FgGapDh.FgPatchEntry)
    (rk1 : Bytes) (ck1_1 : Bytes) (fgRootL' : List FgRootEntry)
    (mkSeed : Bytes) (spqrSalt? : Option Bytes)
    (updBase : AuthState S → AuthState S)
    (st st0 : FgAuthSimState S)
    (hInv : a1g_SessStepPost st0 st)
    (hUpd : a1g_SessStepPost st0 { st with base := updBase st.base, fgL := fgL', fgRootL := fgRootL' }) :
    ∀ p ∈ support (fgFinishRecvStep2AuthGdh S k j msg kEntry drKey fgL' rk1 ck1_1 fgRootL'
      mkSeed spqrSalt? updBase st), a1g_SessStepPost st0 p.2 := by
  intro p hp
  unfold fgFinishRecvStep2AuthGdh at hp
  simp only [mem_support_bind_iff] at hp
  rcases hp with ⟨_, _, pt?, _, hp⟩
  cases pt? with
  | none =>
    simp only [support_pure, Set.mem_singleton_iff] at hp
    subst hp; exact hInv
  | some _ =>
    simp only [mem_support_bind_iff] at hp
    rcases hp with ⟨sender?, _, hp⟩
    cases sender? <;> {
      simp only [support_pure, Set.mem_singleton_iff] at hp
      subst hp; exact hUpd
    }

theorem ddhGdh_fgFinishRecvAuthGdh (S : Setup) (maxLen : ℕ) (k : Fin S.N_id) (j : Fin S.N_recv)
    (msg : PreKeyMsg) (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (ss : Bytes) (pos4? : Option FgGapDh.FgPoS)
    (updBase : AuthState S → AuthState S)
    (st st0 : FgAuthSimState S)
    (hFgEq : st.fgL = st0.fgL) (hRtEq : st.fgRootL = st0.fgRootL) :
    IsQueryBoundP (fgFinishRecvAuthGdh S maxLen k j msg kEntry bEntry ss pos4? updBase st) a1g_isDdhGdh
      (4 * (a1g_rDone st0 + a1g_sDone st0) + (a1g_rtRDone st0 + a1g_rtSDone st0)) ∧
    ∀ p ∈ support (fgFinishRecvAuthGdh S maxLen k j msg kEntry bEntry ss pos4? updBase st),
      a1g_SessStepPost st0 p.2 := by
  have hSt0 : a1g_SessStepPost st0 st := by
    unfold a1g_SessStepPost a1g_rDone a1g_sDone a1g_rtRDone a1g_rtSDone
    rw [hFgEq, hRtEq]
    exact ⟨Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩
  unfold fgFinishRecvAuthGdh
  refine ddhGdh_step_bind0 (ddhGdh_twoSide _ _ _ _) fun pos1 _ => ?_
  refine ddhGdh_step_bind0 (ddhGdh_twoSide _ _ _ _) fun pos2 _ => ?_
  refine ddhGdh_step_bind0 (ddhGdh_twoSide _ _ _ _) fun pos3 _ => ?_
  have hPatch := ddhGdh_fgPatch_sess maxLen pos1 pos2 pos3 pos4? ss st.fgL
  have hPatch1 : IsQueryBoundP (FgGapDh.fgPatch maxLen pos1 pos2 pos3 pos4? ss st.fgL) a1g_isDdhGdh
      (4 * (a1g_rDone st0 + a1g_sDone st0)) := by
    unfold a1g_rDone a1g_sDone; rw [← hFgEq]; exact hPatch.1
  refine ⟨(isQueryBoundP_bind (n := 4 * (a1g_rDone st0 + a1g_sDone st0))
    (m := a1g_rtRDone st0 + a1g_rtSDone st0) hPatch1 fun dkL _ => ?_).mono (by omega), ?_⟩
  · refine ddhGdh_bind0 (ddhGdh_twoSide _ _ _ _) fun posRatchet _ => ?_
    have hRoot1 : IsQueryBoundP (fgRootPatch maxLen dkL.1.rootKey posRatchet st.fgRootL) a1g_isDdhGdh
        (a1g_rtRDone st0 + a1g_rtSDone st0) := by
      unfold a1g_rtRDone a1g_rtSDone; rw [← hRtEq]
      exact (ddhGdh_fgRootPatch_sess maxLen dkL.1.rootKey posRatchet st.fgRootL).1
    refine (isQueryBoundP_bind (n := a1g_rtRDone st0 + a1g_rtSDone st0) (m := 0) hRoot1 fun rkOut _ => ?_).mono
      (by omega)
    refine ddhGdh_bind0 (ddhGdh_primQ _) fun mkSeed _ => ?_
    refine ddhGdh_bind0 (ddhGdh_primQ _) fun ck1_1 _ => ?_
    refine ddhGdh_bind0 (ddhGdh_primQ _) fun spqr? _ => ?_
    cases spqr? with
    | none => exact ddhGdh_pure _ 0
    | some spqr =>
      exact ddhGdh_fgFinishRecvStep2AuthGdh_qb S k j msg kEntry dkL.1 dkL.2 rkOut.1.1 ck1_1
        rkOut.2 mkSeed spqr.2 updBase st
  · intro p hp
    rw [mem_support_bind_iff] at hp
    rcases hp with ⟨dkL, hdk, hp⟩
    simp only [mem_support_bind_iff] at hp
    rcases hp with ⟨posRatchet, _, rkOut, hrk, mkSeed, _, ck1_1, _, spqr?, _, hp⟩
    cases spqr? with
    | none =>
      simp only [support_pure, Set.mem_singleton_iff] at hp
      subst hp; exact hSt0
    | some spqr =>
      have hM := hPatch.2 dkL hdk
      have hR := (ddhGdh_fgRootPatch_sess maxLen dkL.1.rootKey posRatchet st.fgRootL).2 rkOut hrk
      have hUpd : a1g_SessStepPost st0
          { st with base := updBase st.base, fgL := dkL.2, fgRootL := rkOut.2 } := by
        unfold a1g_SessStepPost a1g_rDone a1g_sDone a1g_rtRDone a1g_rtSDone
        dsimp only
        rw [← hFgEq, ← hRtEq]
        exact ⟨hM, hR⟩
      exact ddhGdh_fgFinishRecvStep2AuthGdh_supp S k j msg kEntry dkL.1 dkL.2 rkOut.1.1 ck1_1
        rkOut.2 mkSeed spqr.2 updBase st st0 hSt0 hUpd p hp

end BilinearGdh

end SignalPqxdh.Security.ReductionDsl.AuthHs
