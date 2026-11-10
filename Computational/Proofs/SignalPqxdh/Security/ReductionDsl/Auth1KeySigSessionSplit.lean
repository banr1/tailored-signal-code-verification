/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyGapDhSessionSplit
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeySigStepBounds
import Computational.Proofs.SignalPqxdh.Security.Auth1KeySigSigBound

/-!
# Session-Split Primitive and Bilinear DDH Query Bounds for `sigAuth1KeyProg`

**Checked by Lean.** Separates session and non-session handler arms of `sigAuth1KeyProg` so
non-session queries incur at most `32` primitive queries, yielding `gdhPrimQueryBudget S b` for any
`QueryBounded` adversary. Also proves the bilinear DDH-query bound for the shallow reduction
`sigReductionAuth1Key`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthHs

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl
open OracleSpec OracleComp

section Branches

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}

/-- `a1sPreC` with the two `send*` forgery-check arms replaced by `.inr ()` (delegate). -/
def a1sPreNSC (_s : Var Γ₁ a1sStTy) (q : Var Γ₂ authQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    CS Δ (.sum a1sRS .unit) :=
  caseSumV (v q) (fun _ => .ret (.inr .litUnit)) fun q =>
  caseSumV (v q) (fun _ => .ret (.inr .litUnit)) fun q =>
  caseSumV (v q) (fun _ => .ret (.inr .litUnit)) fun q =>
  caseSumV (v q) (fun _ => .ret (.inr .litUnit)) fun q =>
  caseSumV (v q) (fun _ => .ret (.inr .litUnit)) fun q =>
  caseSumV (v q) (fun _ => .ret (.inr .litUnit)) fun _ =>
  .ret (.inr .litUnit)

def a1sDelegateNSC (s : Var Γ₁ a1sStTy) (q : Var Γ₂ authQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    CS Δ a1sRS :=
  letV (a1sG (v s)) fun g =>
  bindV (a1gStepNSC S K g q) fun r =>
  .ret (.pair (.fst (v r)) (a1sMk (.snd (v r)) (a1sTp (v s)) (a1sTpk (v s)) (a1sFg (v s))))

def a1sStepNSC (s : Var Γ₁ a1sStTy) (q : Var Γ₂ authQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    CS Δ a1sRS :=
  .iteC (isSomeE (a1sFg (v s))) (.ret (.pair aNone (v s))) <|
  bindV (a1sPreNSC s q) fun pre =>
  caseSumV (v pre) (fun r => .ret (v r)) fun _ =>
  a1sDelegateNSC S K s q

end Branches

/-- `a1sHandleDsl` with the session arms replaced by no-ops. -/
def a1sHandleNS (S : Setup) (K : Nat) : CS [a1sStTy, authQueryTy] a1sRS :=
  a1sStepNSC S K (.vz : Var [a1sStTy, authQueryTy] a1sStTy)
    (.vs .vz : Var [a1sStTy, authQueryTy] authQueryTy)

private def a1sDelegate2NSC (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ a1sStTy) (q : Var Γ₂ authQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    CS Δ a1sRS :=
  letV (.pair (.pair (a1sCaseAPa2 (a1sTpk (v s)) (a1sTp (v s))) (.snd (.fst (a1sG (v s)))))
      (.snd (a1sG (v s)))) fun g2 =>
  bindV (a1gStep2NSC K g2 q) fun r =>
  .ret (.pair (.fst (v r))
    (a1sMk (.pair (.pair (.fst (.fst (a1sG (v s)))) (.snd (.fst (.snd (v r)))))
        (.snd (.snd (v r))))
      (a1sTp (v s)) (a1sTpk (v s)) (a1sFg (v s))))

private def a1sStep2NSC (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ a1sStTy) (q : Var Γ₂ authQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    CS Δ a1sRS :=
  .iteC (isSomeE (a1sFg (v s))) (.ret (.pair aNone (v s))) <|
  bindV (a1sPreNSC s q) fun pre =>
  caseSumV (v pre) (fun r => .ret (v r)) fun _ =>
  a1sDelegate2NSC K s q

private def a1sHandle2NS (K : Nat) : CS [a1sStTy, authQueryTy] a1sRS :=
  a1sStep2NSC K (.vz : Var [a1sStTy, authQueryTy] a1sStTy)
    (.vs .vz : Var [a1sStTy, authQueryTy] authQueryTy)

theorem a1gStepNSC_queries_prim_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (st : Var Γ₁ a1gStTy) (q : Var Γ₂ authQueryTy) :
    (a1gStepNSC S K (Δ := Δ) st q).queries
      KeyInd1KeyGapDh.wPrim1Key KeyInd1KeyGapDh.wsZero1Key ≤ 32 := by
  simp only [
    a1gStepNSC, Comp.letC, a1gPreC, a1gInitPrinC, a1gGenSpkC,
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

private theorem a1gStep2NSC_queries_prim_le (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (st : Var Γ₁ a1g2StTy) (q : Var Γ₂ authQueryTy) :
    (a1gStep2NSC K (Δ := Δ) st q).queries
      KeyInd1KeyGapDh.wPrim1Key KeyInd1KeyGapDh.wsZero1Key ≤ 32 := by
  simp only [
    a1gStep2NSC, Comp.letC, a1gPre2C, a1gInitPrin2C, a1gGenSpk2C,
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

theorem a1sHandleNS_queries_prim_le (S : Setup) (K : Nat) :
    (a1sHandleNS S K).queries
      SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight ≤ 32 := by
  have hD := a1gStepNSC_queries_prim_le S K
    (Γ₁ := a1gStTy :: .unit :: (.sum a1sRS .unit) :: [a1sStTy, authQueryTy])
    (Δ := a1gStTy :: .unit :: (.sum a1sRS .unit) :: [a1sStTy, authQueryTy])
    Var.vz (.vs .vz : Var [a1sStTy, authQueryTy] authQueryTy)
  simp only [a1sHandleNS, a1sStepNSC, a1sPreNSC, a1sDelegateNSC, bindV, letV, caseSumV,
    Comp.letC, Comp.queries, Nat.zero_max, max_self, Nat.add_zero, Nat.zero_add] at hD ⊢
  exact hD

private theorem a1sHandle2NS_queries_prim_le (K : Nat) :
    (a1sHandle2NS K).queries
      SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight ≤ 32 := by
  have hD := a1gStep2NSC_queries_prim_le K
    (Γ₁ := a1g2StTy :: .unit :: (.sum a1sRS .unit) :: [a1sStTy, authQueryTy])
    (Δ := a1g2StTy :: .unit :: (.sum a1sRS .unit) :: [a1sStTy, authQueryTy])
    Var.vz (.vs .vz : Var [a1sStTy, authQueryTy] authQueryTy)
  simp only [a1sHandle2NS, a1sStep2NSC, a1sPreNSC, a1sDelegate2NSC, bindV, letV, caseSumV,
    Comp.letC, Comp.queries, Nat.zero_max, max_self, Nat.add_zero, Nat.zero_add] at hD ⊢
  exact hD

section
set_option allowUnsafeReducibility true
attribute [local implicit_reducible] Env.get Ext.wk

theorem a1sHandleDsl_eval_NS (S : Setup) (K : Nat) (t : AuthQuery S)
    (ht : isAuthSessionQ t = false) (s : a1sStTy.denote) :
    (a1sHandleDsl S K).eval (.cons s (.cons (authQenc t) .nil)) =
      (a1sHandleNS S K).eval (.cons s (.cons (authQenc t) .nil)) := by
  cases t <;> simp only [isAuthSessionQ, Bool.true_eq_false] at ht <;> rfl

private theorem a1sHandle2Dsl_eval_NS (S : Setup) (K : Nat) (t : AuthQuery S)
    (ht : isAuthSessionQ t = false) (s : a1sStTy.denote) :
    (a1sHandle2Dsl S K).eval (.cons s (.cons (authQenc t) .nil)) =
      (a1sHandle2NS K).eval (.cons s (.cons (authQenc t) .nil)) := by
  cases t <;> simp only [isAuthSessionQ, Bool.true_eq_false] at ht <;> rfl

end

theorem a1sHandle_primBound_heavy (S : Setup) (K : Nat) (s : a1sStTy.denote)
    (t : AuthQuery S) :
    ((sigAuth1KeyProg S K).handle.eval (.cons s (.cons (authQenc t) .nil))).IsQueryBoundP
      (fun q => isPrimQuery q = true) (16 * (5 * S.N_dh + S.N_sess_tot + 12)) :=
  KeyInd1KeyGapDh.comp_primBound _ _
    ((a1s_handle_prim_le S K (fun st q => a1gStepC_queries_prim_le S K st q)).trans
      (by omega))

theorem a1sHandle_primBound_light (S : Setup) (K : Nat) (s : a1sStTy.denote)
    (t : AuthQuery S) (ht : isAuthSessionQ t = false) :
    ((sigAuth1KeyProg S K).handle.eval (.cons s (.cons (authQenc t) .nil))).IsQueryBoundP
      (fun q => isPrimQuery q = true) 32 := by
  change ((a1sHandle2Dsl S K).eval (.cons s (.cons (authQenc t) .nil))).IsQueryBoundP _ _
  rw [a1sHandle2Dsl_eval_NS S K t ht s]
  exact KeyInd1KeyGapDh.comp_primBound _ _ (a1sHandle2NS_queries_prim_le K)

private theorem a1s_split_arith (q k X : ℕ) (hk : k ≤ q) (hX : 2 ≤ X) :
    0 + (q * 32 + k * (16 * X - 32)) + 0 ≤ 32 * (q - k) + 16 * (k + 1) * X := by
  obtain ⟨r, rfl⟩ : ∃ r, q = k + r := ⟨q - k, by omega⟩
  obtain ⟨d, hd⟩ : ∃ d, 16 * X = 32 + d := ⟨16 * X - 32, by omega⟩
  have h1 : 16 * X - 32 = d := by omega
  have h2 : k + r - k = r := by omega
  have h3 : 16 * (k + 1) * X = (k + 1) * (32 + d) := by rw [← hd]; ring
  rw [h1, h2, h3]
  nlinarith

/-- Session-split primitive-query bound for `(sigAuth1KeyProg S K).eval` in terms of total and
    session query counts. -/
theorem sigAuth1KeyProg_primBounded_split (S : Setup) (K q m : Nat)
    (A : Unit → OracleComp (unifSpec + authSpec S) Bool)
    (hA : ∀ a, (A a).IsQueryBoundP (ReductionDsl.isGameQuery (G := authSpec S)) q)
    (hAH : ∀ a, (A a).IsQueryBoundP
      (onGame (G := authSpec S) (fun t => isAuthSessionQ t = true)) m)
    (pk : Bytes) :
    ((sigAuth1KeyProg S K).eval A pk).IsQueryBoundP
      (fun q => isPrimQuery q = true)
      (32 * (q - min q m) + 16 * (min q m + 1) * (5 * S.N_dh + S.N_sess_tot + 12)) := by
  refine (CostedReduction.queryBound_eval₂ (sigAuth1KeyProg S K)
    (fun q => isPrimQuery q = true)
    SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight
    SignalPqxdh.LegacyCosted.samplerZeroQueryWeight ?_ ?_
    (fun t => isAuthSessionQ t = true) (kL := 32) (kH := 16 * (5 * S.N_dh + S.N_sess_tot + 12))
    (by omega) (fun t s _ => a1sHandle_primBound_heavy S K s t)
    (fun t s ht => a1sHandle_primBound_light S K s t (by simpa using ht))
    A q m hA hAH pk).mono ?_
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
  · have hI0 : (sigAuth1KeyProg S K).init.queries
        SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight
        SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = 0 :=
      a1s_init_queries S K _
    have hF0 : (sigAuth1KeyProg S K).finish.queries
        SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight
        SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = 0 :=
      a1s_finish_queries S K _
    rw [hI0, hF0]
    exact a1s_split_arith q (min q m) _ (min_le_left _ _) (by omega)

/-- For a `b`-bounded `Auth` adversary, `(sigAuth1KeyProg S K).eval` makes at most
    `gdhPrimQueryBudget S b` primitive queries. -/
theorem sigAuth1KeyProg_primBounded_gdhPrimQueryBudget (S : Setup) (K : Nat)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) (pk : Bytes) :
    ((sigAuth1KeyProg S K).eval (fun _ => A.1.run) pk).IsQueryBoundP
      (fun q => isPrimQuery q = true) (gdhPrimQueryBudget S b) :=
  (sigAuth1KeyProg_primBounded_split S K b.q_total (min b.q_on S.N_sess_tot) (fun _ => A.1.run)
    (authAdv_gameBound S b A) (fun _ => authAdv_sessionBound_on S b A) pk).mono
    (le_of_eq (a1g_split_prim_eq_gdhPrimQueryBudget S b))

section Auth1KeySigBilinearDdh

open Proofs.SignalPqxdh.Security
open SignalPqxdh.Security.FgGapDh SignalPqxdh.Security.FgGapDh1Key
open Proofs.SignalPqxdh.Security.FgGapDh Proofs.SignalPqxdh.Security.FgGapDh1Key

private def posIsSecret : FgPoS → Bool
  | .secret _ _ => true | .pair _ _ _ _ => false

private def optPosIsSecret : Option FgPoS → Bool
  | none => true | some p => posIsSecret p

private def entryAllSecret (e : FgPatchEntry) : Bool :=
  posIsSecret e.pos1 && posIsSecret e.pos2 && posIsSecret e.pos3 && optPosIsSecret e.pos4?

private def fgSDone : List FgPatchEntry → ℕ
  | [] => 0 | e :: L => (if entryAllSecret e then 0 else 1) + fgSDone L

private def rootSDone : List FgRootEntry → ℕ
  | [] => 0 | e :: L => (if posIsSecret e.dhPos then 0 else 1) + rootSDone L

private def isGdhDdh : GdhSimSpec.Domain → Bool
  | Sum.inl _ => false | Sum.inr _ => true

private def DdhStep {ι : Type} {spec : OracleSpec ι} (p : spec.Domain → Bool)
    {α : Type} (m : ℕ) (Q : α → Prop) (oa : OracleComp spec α) : Prop :=
  oa.IsQueryBoundP (fun q => p q = true) m ∧ ∀ x ∈ support oa, Q x

private abbrev GdhDdhStep {α : Type} := DdhStep (spec := GdhSimSpec) isGdhDdh (α := α)
private abbrev SignDdhStep {α : Type} := DdhStep (spec := GdhSignSimSpec) isDdhChalQuery (α := α)

private theorem ddhStep_pure {ι : Type} {spec : OracleSpec ι} {p : spec.Domain → Bool}
    {α : Type} (a : α) {Q : α → Prop} (ha : Q a) : DdhStep p 0 Q (pure a) :=
  ⟨isQueryBoundP_pure _ a 0, fun x hx => by
    simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx; exact ha⟩

private theorem ddhStep_mono {ι : Type} {spec : OracleSpec ι} {p : spec.Domain → Bool}
    {α : Type} {m1 m2 : ℕ} {Q1 Q2 : α → Prop} {oa : OracleComp spec α}
    (hm : m1 ≤ m2) (hQ : ∀ x, Q1 x → Q2 x) (h : DdhStep p m1 Q1 oa) : DdhStep p m2 Q2 oa :=
  ⟨h.1.mono hm, fun x hx => hQ x (h.2 x hx)⟩

private theorem ddhStep_bind {ι : Type} {spec : OracleSpec ι} {p : spec.Domain → Bool}
    {α β : Type} {m1 m2 : ℕ} {P : α → Prop} {Q : β → Prop}
    {oa : OracleComp spec α} {k : α → OracleComp spec β}
    (h1 : DdhStep p m1 P oa) (h2 : ∀ x, P x → DdhStep p m2 Q (k x)) :
    DdhStep p (m1 + m2) Q (oa >>= k) :=
  ⟨isQueryBoundP_bind h1.1 (fun x hx => (h2 x (h1.2 x hx)).1), fun y hy => by
    rw [mem_support_bind_iff] at hy; rcases hy with ⟨x, hx, hy⟩; exact (h2 x (h1.2 x hx)).2 y hy⟩

private theorem ddhStep_bind0 {ι : Type} {spec : OracleSpec ι} {p : spec.Domain → Bool}
    {α β : Type} {m : ℕ} {P : α → Prop} {Q : β → Prop}
    {oa : OracleComp spec α} {k : α → OracleComp spec β}
    (h1 : DdhStep p 0 P oa) (h2 : ∀ x, P x → DdhStep p m Q (k x)) : DdhStep p m Q (oa >>= k) := by
  simpa using ddhStep_bind h1 h2

private theorem ddhStep_bindR0 {ι : Type} {spec : OracleSpec ι} {p : spec.Domain → Bool}
    {α β : Type} {m : ℕ} {P : α → Prop} {Q : β → Prop}
    {oa : OracleComp spec α} {k : α → OracleComp spec β}
    (h1 : DdhStep p m P oa) (h2 : ∀ x, P x → DdhStep p 0 Q (k x)) : DdhStep p m Q (oa >>= k) := by
  simpa using ddhStep_bind h1 h2

private theorem isQueryBoundP_embedPrim_gdhDdh {α : Type} (mx : OracleComp PrimBaseSpec α) :
    (FgGapDh.embedPrim (spec := gapDhOracleSpec) mx).IsQueryBoundP (fun q => isGdhDdh q = true) 0 := by
  induction mx using OracleComp.inductionOn with
  | pure a => exact isQueryBoundP_pure _ a 0
  | query_bind q k ih =>
    change IsQueryBoundP (liftM (OracleSpec.query (spec := PrimBaseSpec + gapDhOracleSpec) (Sum.inl q)) >>=
      fun u => FgGapDh.embedPrim (spec := gapDhOracleSpec) (k u)) (fun q => isGdhDdh q = true) 0
    rw [isQueryBoundP_query_bind_iff]; exact ⟨Or.inl (fun h => by cases h), fun u => ih u⟩

private theorem isQueryBoundP_embedPrim_sigDdh {α : Type} (mx : OracleComp PrimBaseSpec α) :
    (SignalPqxdh.Security.embedPrim (spec := sigAndDdhSpec) mx).IsQueryBoundP
      (fun q => isDdhChalQuery q = true) 0 := by
  induction mx using OracleComp.inductionOn with
  | pure a => exact isQueryBoundP_pure _ a 0
  | query_bind q k ih =>
    change IsQueryBoundP (liftM (OracleSpec.query (spec := PrimBaseSpec + sigAndDdhSpec) (Sum.inl q)) >>=
      fun u => SignalPqxdh.Security.embedPrim (spec := sigAndDdhSpec) (k u))
      (fun q => isDdhChalQuery q = true) 0
    rw [isQueryBoundP_query_bind_iff]; exact ⟨Or.inl (fun h => by cases h), fun u => ih u⟩

private theorem gdhDdhStep_embedPrim {α : Type} (mx : OracleComp PrimBaseSpec α) :
    GdhDdhStep 0 (fun _ => True) (FgGapDh.embedPrim (spec := gapDhOracleSpec) mx) :=
  ⟨isQueryBoundP_embedPrim_gdhDdh mx, fun _ _ => trivial⟩

private theorem gdhDdhStep_unif {α : Type} (mx : ProbComp α) :
    GdhDdhStep 0 (fun _ => True) (unifGdh mx) := gdhDdhStep_embedPrim (FgGapDh.embedUnif mx)

private theorem gdhDdhStep_primQ (op : PrimQuery) : GdhDdhStep 0 (fun _ => True) (primGdhQ op) :=
  ⟨by unfold primGdhQ; change IsQueryBoundP (liftM (OracleSpec.query (spec := GdhSimSpec) _)) _ _
      rw [isQueryBoundP_query_iff]; simp [isGdhDdh], fun _ _ => trivial⟩

private theorem isQueryBoundP_ddhGdhQ (X Y Z : Bytes) :
    (ddhGdhQ X Y Z).IsQueryBoundP (fun q => isGdhDdh q = true) 1 := by
  unfold ddhGdhQ; change IsQueryBoundP (liftM (OracleSpec.query (spec := GdhSimSpec) _)) _ _
  rw [isQueryBoundP_query_iff]; simp [isGdhDdh]

private theorem mem_support_liftGdhToSign {α : Type} (oa : OracleComp GdhSimSpec α) (y : α) :
    y ∈ support (liftGdhToSign oa) ↔ y ∈ support oa := by
  induction oa using OracleComp.inductionOn with
  | pure _ => rfl
  | query_bind q r ih =>
    rcases q with bq | dq
    · change y ∈ support (liftM (OracleSpec.query (spec := GdhSignSimSpec) (Sum.inl bq)) >>=
          fun u => liftGdhToSign (r u)) ↔ _
      simp only [mem_support_bind_iff, support_query, Set.mem_univ, true_and]
      exact exists_congr fun u => ih u
    · change y ∈ support (liftM (OracleSpec.query (spec := GdhSignSimSpec) (Sum.inr (Sum.inr dq))) >>=
          fun u => liftGdhToSign (r u)) ↔ _
      simp only [mem_support_bind_iff, support_query, Set.mem_univ, true_and]
      exact exists_congr fun u => ih u

private theorem isQueryBoundP_liftGdhToSign_ddh {α : Type} (oa : OracleComp GdhSimSpec α) :
    ∀ {m : ℕ}, oa.IsQueryBoundP (fun q => isGdhDdh q = true) m →
      (liftGdhToSign oa).IsQueryBoundP (fun q => isDdhChalQuery q = true) m := by
  induction oa using OracleComp.inductionOn with
  | pure _ => intro _ _; simp [liftGdhToSign]
  | query_bind q r ih =>
    intro m h; rw [isQueryBoundP_query_bind_iff] at h; rcases q with bq | dq
    · change IsQueryBoundP (liftM (OracleSpec.query (spec := GdhSignSimSpec) (Sum.inl bq)) >>=
          fun u => liftGdhToSign (r u)) (fun q => isDdhChalQuery q = true) m
      rw [isQueryBoundP_query_bind_iff]; exact ⟨Or.inl (fun hc => by cases hc), fun u => ih u (h.2 u)⟩
    · change IsQueryBoundP (liftM (OracleSpec.query (spec := GdhSignSimSpec) (Sum.inr (Sum.inr dq))) >>=
          fun u => liftGdhToSign (r u)) (fun q => isDdhChalQuery q = true) m
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨Or.inr (h.1.resolve_left (fun hc => hc rfl)), fun u => ih u (h.2 u)⟩

private theorem liftGdhToSign_ddhStep {α : Type} {m : ℕ} {Q : α → Prop}
    {oa : OracleComp GdhSimSpec α} (h : GdhDdhStep m Q oa) : SignDdhStep m Q (liftGdhToSign oa) :=
  ⟨isQueryBoundP_liftGdhToSign_ddh oa h.1, fun x hx => h.2 x ((mem_support_liftGdhToSign oa x).mp hx)⟩

private theorem signDdhStep_unif {α : Type} (mx : ProbComp α) :
    SignDdhStep 0 (fun _ => True) (unifGdhSign mx) := liftGdhToSign_ddhStep (gdhDdhStep_unif mx)

private theorem signDdhStep_primQ (op : PrimQuery) : SignDdhStep 0 (fun _ => True) (primGdhSignQ op) :=
  ⟨by unfold primGdhSignQ; change IsQueryBoundP (liftM (OracleSpec.query (spec := GdhSignSimSpec) _)) _ _
      rw [isQueryBoundP_query_iff]; simp [isDdhChalQuery], fun _ _ => trivial⟩

private theorem signDdhStep_sigChalQ (msg : Bytes) :
    SignDdhStep 0 (fun _ => True) (FgGapDh1Key.sigChalQ msg) :=
  ⟨by unfold FgGapDh1Key.sigChalQ; change IsQueryBoundP (liftM (OracleSpec.query (spec := GdhSignSimSpec) _)) _ _
      rw [isQueryBoundP_query_iff]; simp [isDdhChalQuery], fun _ _ => trivial⟩

private theorem mkSecretPos_step (z : Bytes) :
    GdhDdhStep 0 (fun p => posIsSecret p = true) (mkSecretPos z) := by
  unfold mkSecretPos; exact ddhStep_bind0 (gdhDdhStep_primQ _) fun _ _ => ddhStep_pure _ rfl

private theorem computeTwoSideOrPairPos_step (sk1 sk2 pk1 pk2 : Bytes) :
    GdhDdhStep 0 (fun _ => True) (computeTwoSideOrPairPos sk1 sk2 pk1 pk2) := by
  unfold computeTwoSideOrPairPos; split_ifs
  · exact ddhStep_bind0 (gdhDdhStep_primQ _) fun z _ =>
      ddhStep_mono le_rfl (fun _ _ => trivial) (mkSecretPos_step z)
  · exact ddhStep_bind0 (gdhDdhStep_primQ _) fun z _ =>
      ddhStep_mono le_rfl (fun _ _ => trivial) (mkSecretPos_step z)
  · unfold mkPairPos; exact ddhStep_bind0 (gdhDdhStep_primQ _) fun _ _ =>
      ddhStep_bind0 (gdhDdhStep_primQ _) fun _ _ => ddhStep_pure _ trivial

private theorem computeOptPos_step (sk1 pk1 : Bytes) (opt : Option (Bytes × Bytes)) :
    GdhDdhStep 0 (fun _ => True) (computeOptPos sk1 pk1 opt) := by
  cases opt with
  | none => exact ddhStep_pure none trivial
  | some p =>
    simp only [computeOptPos, map_eq_bind_pure_comp, Function.comp_def]
    exact ddhStep_bind0 (computeTwoSideOrPairPos_step sk1 p.1 pk1 p.2) fun x _ => ddhStep_pure (some x) trivial

private theorem ddhEqGdh_any (p1 p2 : FgPoS) :
    (ddhEqGdh p1 p2).IsQueryBoundP (fun q => isGdhDdh q = true) 1 := by
  cases p1 <;> cases p2 <;> simp only [ddhEqGdh]
  all_goals try exact (isQueryBoundP_pure _ _ 0).mono (Nat.zero_le 1)
  all_goals split_ifs <;> [exact isQueryBoundP_ddhGdhQ _ _ _;
    exact (isQueryBoundP_pure _ _ 0).mono (Nat.zero_le 1)]

private theorem ddhEqGdh_sec (p1 p2 : FgPoS) (h1 : posIsSecret p1 = true) (h2 : posIsSecret p2 = true) :
    (ddhEqGdh p1 p2).IsQueryBoundP (fun q => isGdhDdh q = true) 0 := by
  cases p1 <;> cases p2 <;> simp_all [posIsSecret, ddhEqGdh]

private theorem fgEntryMatches_any (pos1 pos2 pos3 : FgPoS) (pos4? : Option FgPoS)
    (ss : Bytes) (e : FgPatchEntry) :
    (fgEntryMatches pos1 pos2 pos3 pos4? ss e).IsQueryBoundP (fun q => isGdhDdh q = true) 4 := by
  have hOpt (o1 o2 : Option FgPoS) : (ddhEqOptGdh o1 o2).IsQueryBoundP (fun q => isGdhDdh q = true) 1 := by
    cases o1 <;> cases o2 <;> simp only [ddhEqOptGdh]
    all_goals try exact (isQueryBoundP_pure _ _ 0).mono (Nat.zero_le 1)
    exact ddhEqGdh_any _ _
  unfold fgEntryMatches; split_ifs
  · exact (isQueryBoundP_pure _ _ 0).mono (Nat.zero_le 4)
  · refine (isQueryBoundP_bind (ddhEqGdh_any pos1 e.pos1) fun _ _ =>
      isQueryBoundP_bind (ddhEqGdh_any pos2 e.pos2) fun _ _ =>
      isQueryBoundP_bind (ddhEqGdh_any pos3 e.pos3) fun _ _ =>
      isQueryBoundP_bind (hOpt pos4? e.pos4?) fun _ _ => isQueryBoundP_pure _ _ 0).mono (by omega)

private theorem fgEntryMatches_sec (pos1 pos2 pos3 : FgPoS) (pos4? : Option FgPoS) (ss : Bytes)
    (e : FgPatchEntry) (h1 : posIsSecret pos1 = true) (h2 : posIsSecret pos2 = true)
    (h3 : posIsSecret pos3 = true) (h4 : optPosIsSecret pos4? = true) (he : entryAllSecret e = true) :
    (fgEntryMatches pos1 pos2 pos3 pos4? ss e).IsQueryBoundP (fun q => isGdhDdh q = true) 0 := by
  rcases e with ⟨ep1, ep2, ep3, ep4, ess, edk⟩
  simp only [entryAllSecret, Bool.and_eq_true] at he; rcases he with ⟨⟨⟨he1, he2⟩, he3⟩, he4⟩
  have hOpt : (ddhEqOptGdh pos4? ep4).IsQueryBoundP (fun q => isGdhDdh q = true) 0 := by
    cases pos4? <;> cases ep4 <;> simp_all [optPosIsSecret, ddhEqOptGdh]
    exact ddhEqGdh_sec _ _ h4 he4
  unfold fgEntryMatches; split_ifs
  · exact isQueryBoundP_pure _ _ 0
  · refine (isQueryBoundP_bind (ddhEqGdh_sec pos1 ep1 h1 he1) fun _ _ =>
      isQueryBoundP_bind (ddhEqGdh_sec pos2 ep2 h2 he2) fun _ _ =>
      isQueryBoundP_bind (ddhEqGdh_sec pos3 ep3 h3 he3) fun _ _ =>
      isQueryBoundP_bind hOpt fun _ _ => isQueryBoundP_pure _ _ 0).mono (by omega)

private theorem findMGdh_take_queryBound {α : Type} (p : α → OracleComp GdhSimSpec Bool)
    (cost : α → ℕ) (hp : ∀ x, (p x).IsQueryBoundP (fun q => isGdhDdh q = true) (cost x)) :
    ∀ (n : ℕ) (xs : List α),
      (findMGdh p (xs.take n)).IsQueryBoundP (fun q => isGdhDdh q = true) ((xs.map cost).sum)
  | 0, _ => by simp only [List.take_zero, findMGdh]; exact (isQueryBoundP_pure _ _ 0).mono (Nat.zero_le _)
  | _ + 1, [] => by simp only [List.take_nil, findMGdh, List.map_nil, List.sum_nil]; exact isQueryBoundP_pure _ _ 0
  | n + 1, x :: xs => by
    simp only [List.take_succ_cons, findMGdh, List.map_cons, List.sum_cons]
    refine isQueryBoundP_bind (hp x) fun _ _ => ?_
    split_ifs; · exact (isQueryBoundP_pure _ _ 0).mono (Nat.zero_le _)
    · exact findMGdh_take_queryBound p cost hp n xs

private theorem sum_const_cost {α : Type} (c : ℕ) : ∀ L : List α, (L.map (fun _ => c)).sum = c * L.length
  | [] => by simp
  | _ :: L => by simp only [List.map_cons, List.sum_cons, List.length_cons, sum_const_cost c L]; ring

private theorem fgPatch_any_step (maxLen : ℕ) (pos1 pos2 pos3 : FgPoS) (pos4? : Option FgPoS)
    (ss : Bytes) (L : List FgPatchEntry) :
    GdhDdhStep (4 * L.length) (fun r => fgSDone r.2 ≤ fgSDone L + 1 ∧ r.2.length ≤ L.length + 1)
      (fgPatch maxLen pos1 pos2 pos3 pos4? ss L) := by
  unfold fgPatch
  have hFind := findMGdh_take_queryBound (fgEntryMatches pos1 pos2 pos3 pos4? ss)
    (fun _ => 4) (fun e => fgEntryMatches_any _ _ _ _ _ e) maxLen L
  rw [sum_const_cost] at hFind
  refine ddhStep_bindR0 ⟨hFind, fun _ _ => trivial⟩ fun opt _ => ?_
  cases opt with
  | some e => exact ddhStep_pure (e.dk, L) ⟨Nat.le_succ _, Nat.le_succ _⟩
  | none =>
    refine ddhStep_bind0 (gdhDdhStep_unif _) fun _ _ => ddhStep_pure _ ?_
    simp only [fgSDone, List.length_cons]; split_ifs <;> omega

private theorem fgRootPatch_any_step (maxLen : ℕ) (rk : Bytes) (dhPos : FgPoS) (L : List FgRootEntry) :
    GdhDdhStep L.length (fun r => rootSDone r.2 ≤ rootSDone L + 1 ∧ r.2.length ≤ L.length + 1)
      (fgRootPatch maxLen rk dhPos L) := by
  unfold fgRootPatch
  have hFind := findMGdh_take_queryBound (fgRootEntryMatches rk dhPos) (fun _ => 1)
    (fun e => by unfold fgRootEntryMatches; split_ifs
                 · exact (isQueryBoundP_pure _ _ 0).mono (Nat.zero_le 1)
                 · exact ddhEqGdh_any dhPos e.dhPos) maxLen L
  rw [sum_const_cost, one_mul] at hFind
  refine ddhStep_bindR0 ⟨hFind, fun _ _ => trivial⟩ fun opt _ => ?_
  cases opt with
  | some e => exact ddhStep_pure ((e.rk1, e.ck1_0), L) ⟨Nat.le_succ _, Nat.le_succ _⟩
  | none =>
    refine ddhStep_bind0 (gdhDdhStep_unif _) fun _ _ =>
      ddhStep_bind0 (gdhDdhStep_unif _) fun _ _ => ddhStep_pure _ ?_
    simp only [rootSDone, List.length_cons]; split_ifs <;> omega

private theorem sum_fgPatch_sec_cost : ∀ L : List FgPatchEntry,
    (L.map (fun e => if entryAllSecret e then 0 else 4)).sum = 4 * fgSDone L
  | [] => by simp [fgSDone]
  | e :: L => by
    simp only [List.map_cons, List.sum_cons, fgSDone, sum_fgPatch_sec_cost L]
    cases entryAllSecret e
    · simp; omega
    · simp

private theorem sum_fgRoot_sec_cost : ∀ L : List FgRootEntry,
    (L.map (fun e => if posIsSecret e.dhPos then 0 else 1)).sum = rootSDone L
  | [] => by simp [rootSDone]
  | e :: L => by simp only [List.map_cons, List.sum_cons, rootSDone, sum_fgRoot_sec_cost L]

private theorem fgPatch_sec_step (maxLen : ℕ) (pos1 pos2 pos3 : FgPoS) (pos4? : Option FgPoS)
    (ss : Bytes) (L : List FgPatchEntry)
    (h1 : posIsSecret pos1 = true) (h2 : posIsSecret pos2 = true)
    (h3 : posIsSecret pos3 = true) (h4 : optPosIsSecret pos4? = true) :
    GdhDdhStep (4 * fgSDone L) (fun r => fgSDone r.2 = fgSDone L ∧ r.2.length ≤ L.length + 1)
      (fgPatch maxLen pos1 pos2 pos3 pos4? ss L) := by
  unfold fgPatch
  have hFind := findMGdh_take_queryBound (fgEntryMatches pos1 pos2 pos3 pos4? ss)
    (fun e => if entryAllSecret e then 0 else 4)
    (fun e => by
      by_cases he : entryAllSecret e = true
      · simp only [he, ↓reduceIte]; exact fgEntryMatches_sec _ _ _ _ _ e h1 h2 h3 h4 he
      · simp only [he, Bool.false_eq_true, ↓reduceIte]; exact fgEntryMatches_any _ _ _ _ _ e)
    maxLen L
  rw [sum_fgPatch_sec_cost] at hFind
  refine ddhStep_bindR0 ⟨hFind, fun _ _ => trivial⟩ fun opt _ => ?_
  cases opt with
  | some e => exact ddhStep_pure (e.dk, L) ⟨rfl, Nat.le_succ _⟩
  | none =>
    refine ddhStep_bind0 (gdhDdhStep_unif _) fun _ _ => ddhStep_pure _ ?_
    simp [fgSDone, entryAllSecret, h1, h2, h3, h4]

private theorem fgRootPatch_sec_step (maxLen : ℕ) (rk : Bytes) (dhPos : FgPoS)
    (L : List FgRootEntry) (hpos : posIsSecret dhPos = true) :
    GdhDdhStep (rootSDone L) (fun r => rootSDone r.2 = rootSDone L ∧ r.2.length ≤ L.length + 1)
      (fgRootPatch maxLen rk dhPos L) := by
  unfold fgRootPatch
  have hFind := findMGdh_take_queryBound (fgRootEntryMatches rk dhPos)
    (fun e => if posIsSecret e.dhPos then 0 else 1)
    (fun e => by
      by_cases he : posIsSecret e.dhPos = true
      · simp only [he, ↓reduceIte]; unfold fgRootEntryMatches; split_ifs
        · exact isQueryBoundP_pure _ _ 0
        · exact ddhEqGdh_sec dhPos e.dhPos hpos he
      · simp only [he, Bool.false_eq_true, ↓reduceIte]; unfold fgRootEntryMatches; split_ifs
        · exact (isQueryBoundP_pure _ _ 0).mono (Nat.zero_le 1)
        · exact ddhEqGdh_any dhPos e.dhPos)
    maxLen L
  rw [sum_fgRoot_sec_cost] at hFind
  refine ddhStep_bindR0 ⟨hFind, fun _ _ => trivial⟩ fun opt _ => ?_
  cases opt with
  | some e => exact ddhStep_pure ((e.rk1, e.ck1_0), L) ⟨rfl, Nat.le_succ _⟩
  | none =>
    refine ddhStep_bind0 (gdhDdhStep_unif _) fun _ _ =>
      ddhStep_bind0 (gdhDdhStep_unif _) fun _ _ => ddhStep_pure _ ?_
    simp [rootSDone, hpos]

private theorem fgRoQueryAuthGdh_step {S : Setup} (maxLen : ℕ) (secrets : Bytes) (st : FgAuthSimState S) :
    GdhDdhStep (4 * fgSDone st.fgL)
      (fun r => fgSDone r.2.fgL = fgSDone st.fgL ∧ r.2.fgL.length ≤ st.fgL.length + 1 ∧ r.2.fgRootL = st.fgRootL)
      (fgRoQueryAuthGdh maxLen secrets st) := by
  unfold fgRoQueryAuthGdh; cases parseRoSecrets secrets with
  | none =>
    cases st.rawRoCache.find? (fun (s, _) => s == secrets) with
    | some _ => exact ddhStep_mono (Nat.zero_le _) (fun r hr => hr) (ddhStep_pure _ ⟨rfl, Nat.le_succ _, rfl⟩)
    | none =>
      exact ddhStep_mono (Nat.zero_le _) (fun r hr => hr)
        (ddhStep_bind0 (gdhDdhStep_unif _) fun _ _ => ddhStep_pure _ ⟨rfl, Nat.le_succ _, rfl⟩)
  | some tup =>
    rcases tup with ⟨dh1, dh2, dh3, dh4?, ss⟩; dsimp only
    refine ddhStep_bind0 (mkSecretPos_step dh1) fun pos1 h1 =>
      ddhStep_bind0 (mkSecretPos_step dh2) fun pos2 h2 =>
      ddhStep_bind0 (mkSecretPos_step dh3) fun pos3 h3 => ?_
    cases dh4? with
    | none =>
      dsimp only; simp only [pure_bind]
      exact ddhStep_bindR0 (fgPatch_sec_step maxLen pos1 pos2 pos3 none ss st.fgL h1 h2 h3 rfl)
        fun _ hp => ddhStep_pure _ ⟨hp.1, hp.2, rfl⟩
    | some dh4 =>
      dsimp only; simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      refine ddhStep_bind0 (mkSecretPos_step dh4) fun p4 hp4 => ?_
      exact ddhStep_bindR0 (fgPatch_sec_step maxLen pos1 pos2 pos3 (some p4) ss st.fgL h1 h2 h3 hp4)
        fun _ hp => ddhStep_pure _ ⟨hp.1, hp.2, rfl⟩

private theorem fgRoRootQueryAuthGdh_step {S : Setup} (maxLen : ℕ) (rk dh : Bytes) (st : FgAuthSimState S) :
    GdhDdhStep (rootSDone st.fgRootL)
      (fun r => r.2.fgL = st.fgL ∧ rootSDone r.2.fgRootL = rootSDone st.fgRootL ∧
        r.2.fgRootL.length ≤ st.fgRootL.length + 1)
      (fgRoRootQueryAuthGdh maxLen rk dh st) := by
  unfold fgRoRootQueryAuthGdh
  refine ddhStep_bind0 (mkSecretPos_step dh) fun pos hpos => ?_
  exact ddhStep_bindR0 (fgRootPatch_sec_step maxLen rk pos st.fgRootL hpos)
    fun _ hp => ddhStep_pure _ ⟨rfl, hp.1, hp.2⟩

private def SessListsPost {S : Setup} (st st' : FgAuthSimState S) : Prop :=
  fgSDone st'.fgL ≤ fgSDone st.fgL + 1 ∧ st'.fgL.length ≤ st.fgL.length + 1 ∧
    rootSDone st'.fgRootL ≤ rootSDone st.fgRootL + 1 ∧ st'.fgRootL.length ≤ st.fgRootL.length + 1

private theorem sessListsPost_refl {S : Setup} (st : FgAuthSimState S) : SessListsPost st st :=
  ⟨Nat.le_succ _, Nat.le_succ _, Nat.le_succ _, Nat.le_succ _⟩

local macro "gdh_step1" : tactic => `(tactic|
  first
    | refine ddhStep_bind0 (gdhDdhStep_primQ _) fun _ _ => ?_
    | refine ddhStep_bind0 (gdhDdhStep_unif _) fun _ _ => ?_
    | refine ddhStep_bind0 (gdhDdhStep_embedPrim _) fun _ _ => ?_
    | refine ddhStep_bind0 (computeTwoSideOrPairPos_step _ _ _ _) fun _ _ => ?_
    | refine ddhStep_bind0 (computeOptPos_step _ _ _) fun _ _ => ?_
    | refine ddhStep_bind0 (ddhStep_mono le_rfl (fun _ _ => trivial) (mkSecretPos_step _)) fun _ _ => ?_)

local macro "gdh_step0" : tactic => `(tactic| repeat gdh_step1)

private theorem fgRunSendAuthGdh_step (useDh1 : Bool) (targetIdx : ℕ) (S : Setup) (maxLen : ℕ)
    (U : Bytes) (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput)
    (m0 m1 : Bytes) (st : FgAuthSimState S) :
    GdhDdhStep (4 * st.fgL.length + st.fgRootL.length)
      (fun r => SessListsPost st r.2) (fgRunSendAuthGdh useDh1 targetIdx S maxLen U sid u bundle m0 m1 st) := by
  have hNone : GdhDdhStep (4 * st.fgL.length + st.fgRootL.length)
      (fun r => SessListsPost st r.2) (pure (AuthResponse.noneResp, st)) :=
    ddhStep_mono (Nat.zero_le _) (fun r hr => hr) (ddhStep_pure _ (sessListsPost_refl st))
  have hIte : ∀ {c : Prop} [Decidable c] {e : OracleComp GdhSimSpec (AuthResponse × FgAuthSimState S)},
      GdhDdhStep (4 * st.fgL.length + st.fgRootL.length) (fun r => SessListsPost st r.2) e →
      GdhDdhStep (4 * st.fgL.length + st.fgRootL.length) (fun r => SessListsPost st r.2)
        (if c then pure (AuthResponse.noneResp, st) else e) := by
    intro c _ e he; by_cases hc : c <;> simp [hc, hNone, he]
  unfold fgRunSendAuthGdh
  refine hIte (hIte ?_)
  cases st.base.principals.find? (fun (idx, _) => idx == u.val) with
  | none => exact hNone
  | some pU =>
    rcases pU with ⟨_, _⟩; dsimp only
    gdh_step1; refine hIte ?_
    gdh_step1; refine hIte ?_
    gdh_step1; gdh_step1; gdh_step1; gdh_step1; gdh_step1; gdh_step1; gdh_step1
    refine hIte ?_
    refine ddhStep_bind0 (gdhDdhStep_primQ _) fun kemOpt _ => ?_
    cases kemOpt with
    | none => exact hNone
    | some kemP =>
      rcases kemP with ⟨_, _⟩; dsimp only
      gdh_step1; gdh_step1; gdh_step1; gdh_step1; gdh_step1; gdh_step1
      refine ddhStep_bind (fgPatch_any_step maxLen _ _ _ _ _ st.fgL) fun pFg hpFg => ?_
      rcases pFg with ⟨_, _⟩; dsimp only at hpFg ⊢
      gdh_step1; gdh_step1; gdh_step1
      refine ddhStep_bindR0 (fgRootPatch_any_step maxLen _ _ st.fgRootL) fun pRt hpRt => ?_
      rcases pRt with ⟨⟨_, _⟩, _⟩; dsimp only at hpRt ⊢
      gdh_step1; gdh_step1
      refine ddhStep_bind0 (gdhDdhStep_primQ _) fun spqrOpt _ => ?_
      cases spqrOpt with
      | none => exact ddhStep_pure _ (sessListsPost_refl st)
      | some spqrT =>
        rcases spqrT with ⟨_, _, _⟩; dsimp only
        gdh_step1; gdh_step1
        split <;> exact ddhStep_pure _ ⟨hpFg.1, hpFg.2, hpRt.1, hpRt.2⟩

private theorem fgFinishRecvAuthGdh_step (S : Setup) (maxLen : ℕ) (k : Fin S.N_id)
    (j : Fin S.N_recv) (msg : PreKeyMsg) (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (ss : Bytes) (pos4? : Option FgPoS) (updBase : AuthState S → AuthState S) (st : FgAuthSimState S) :
    GdhDdhStep (4 * st.fgL.length + st.fgRootL.length)
      (fun r => SessListsPost st r.2)
      (fgFinishRecvAuthGdh S maxLen k j msg kEntry bEntry ss pos4? updBase st) := by
  unfold fgFinishRecvAuthGdh; gdh_step1; gdh_step1; gdh_step1
  refine ddhStep_bind (fgPatch_any_step maxLen _ _ _ _ _ st.fgL) fun dkL hpFg => ?_
  rcases dkL with ⟨_, _⟩; dsimp only at hpFg ⊢; gdh_step1
  refine ddhStep_bindR0 (fgRootPatch_any_step maxLen _ _ st.fgRootL) fun rkOut hpRt => ?_
  rcases rkOut with ⟨⟨_, _⟩, _⟩; dsimp only at hpRt ⊢
  gdh_step1; gdh_step1
  refine ddhStep_bind0 (gdhDdhStep_primQ _) fun spqr? _ => ?_
  cases spqr? with
  | none => exact ddhStep_pure _ (sessListsPost_refl st)
  | some spqr =>
    rcases spqr with ⟨_, _⟩; dsimp only; unfold fgFinishRecvStep2AuthGdh
    gdh_step1
    refine ddhStep_bind0 (gdhDdhStep_primQ _) fun pt? _ => ?_
    cases pt? with
    | none => exact ddhStep_pure _ (sessListsPost_refl st)
    | some _ =>
      dsimp only
      refine ddhStep_bind0 (gdhDdhStep_embedPrim _) fun senderPrincipal? _ => ?_
      cases senderPrincipal? <;> exact ddhStep_pure _ ⟨hpFg.1, hpFg.2, hpRt.1, hpRt.2⟩

private theorem fgRunRecvOPKAuthGdh_step (S : Setup) (maxLen : ℕ) (k : Fin S.N_id)
    (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg) (stR : FgAuthSimState S) :
    GdhDdhStep (4 * stR.fgL.length + stR.fgRootL.length)
      (fun r => SessListsPost stR r.2) (fgRunRecvOPKAuthGdh S maxLen k j o msg stR) := by
  have hNone : GdhDdhStep (4 * stR.fgL.length + stR.fgRootL.length)
      (fun r => SessListsPost stR r.2) (pure (AuthResponse.noneResp, stR)) :=
    ddhStep_mono (Nat.zero_le _) (fun r hr => hr) (ddhStep_pure _ (sessListsPost_refl stR))
  unfold fgRunRecvOPKAuthGdh
  split; · exact hNone
  split; · exact hNone
  gdh_step1; split; · exact hNone
  cases stR.base.principals.find? (fun (idx, _) => idx == k.val) with
  | none => exact hNone
  | some pK =>
    rcases pK with ⟨_, kEntry⟩; dsimp only
    cases stR.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
    | none => exact hNone
    | some pB =>
      rcases pB with ⟨_, bEntry⟩; dsimp only
      cases stR.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
      | none => exact hNone
      | some pO =>
        rcases pO with ⟨_, _⟩; dsimp only; split; · exact hNone
        gdh_step1; gdh_step1; split; · exact hNone
        refine ddhStep_bind0 (gdhDdhStep_primQ _) fun ss? _ => ?_
        cases ss? with
        | none => exact hNone
        | some ss =>
          dsimp only; gdh_step1
          exact fgFinishRecvAuthGdh_step S maxLen k j msg kEntry bEntry ss _ _ stR

private theorem fgRunRecvNoOPKAuthGdh_step (S : Setup) (maxLen : ℕ) (k : Fin S.N_id)
    (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg) (stR : FgAuthSimState S) :
    GdhDdhStep (4 * stR.fgL.length + stR.fgRootL.length)
      (fun r => SessListsPost stR r.2) (fgRunRecvNoOPKAuthGdh S maxLen k j l msg stR) := by
  have hNone : GdhDdhStep (4 * stR.fgL.length + stR.fgRootL.length)
      (fun r => SessListsPost stR r.2) (pure (AuthResponse.noneResp, stR)) :=
    ddhStep_mono (Nat.zero_le _) (fun r hr => hr) (ddhStep_pure _ (sessListsPost_refl stR))
  unfold fgRunRecvNoOPKAuthGdh
  split; · exact hNone
  split; · exact hNone
  gdh_step1; split; · exact hNone
  cases stR.base.principals.find? (fun (idx, _) => idx == k.val) with
  | none => exact hNone
  | some pK =>
    rcases pK with ⟨_, kEntry⟩; dsimp only
    cases stR.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
    | none => exact hNone
    | some pB =>
      rcases pB with ⟨_, bEntry⟩; dsimp only
      gdh_step1; gdh_step1; split; · exact hNone
      refine ddhStep_bind0 (gdhDdhStep_primQ _) fun ss? _ => ?_
      cases ss? with
      | none => exact hNone
      | some ss =>
        dsimp only
        exact fgFinishRecvAuthGdh_step S maxLen k j msg kEntry bEntry ss none _ stR

private theorem liftAuthSimStep1Key_ddhStep {S : Setup} {m : ℕ} {Q : FgAuthSimState S → Prop}
    {f : FgAuthSimState S → OracleComp GdhSimSpec (AuthResponse × FgAuthSimState S)}
    (st : FgAuth1KeySimState S) (hf : GdhDdhStep m (fun r => Q r.2) (f st.sim)) :
    SignDdhStep m (fun r => Q r.2.sim) (liftAuthSimStep1Key f st) := by
  unfold liftAuthSimStep1Key
  exact ddhStep_bindR0 (liftGdhToSign_ddhStep hf) fun _ hp => ddhStep_pure _ hp

private theorem sigAuth1KeyDelegate_ddhStep {S : Setup} {maxLen m : ℕ} {q : AuthQuery S}
    {st : SigAuth1KeySimState S} {Q : FgAuthSimState S → Prop} (hRefl : Q st.fg.sim)
    (hStep : GdhDdhStep m (fun r => Q r.2)
      (fgAuthStep true st.targetParty S.N_spk_tot S maxLen st.targetPk st.targetPk q st.fg.sim))
    (hNotInitSpk : match q with | .initPrin _ => False | .genSPK _ _ => False | _ => True) :
    SignDdhStep m (fun r => Q r.2.fg.sim) (sigAuth1KeyDelegate S maxLen q st) := by
  unfold sigAuth1KeyDelegate fgAuth1KeyStepHalt; split
  · exact ddhStep_mono (Nat.zero_le m) (fun r hr => hr)
      (ddhStep_bind0 (ddhStep_pure _ hRefl) fun _ hp => ddhStep_pure _ hp)
  · have h1 : SignDdhStep m (fun r => Q r.2.sim)
        (fgAuth1KeyStep true st.targetParty S.N_spk_tot S maxLen st.targetPk st.targetPk q st.fg) := by
      cases q <;> try exact False.elim hNotInitSpk
      all_goals exact liftAuthSimStep1Key_ddhStep st.fg hStep
    exact ddhStep_bindR0 h1 fun _ hp => ddhStep_pure _ hp

private theorem sigAuth1KeyStep_sess (S : Setup) (maxLen : ℕ) (q : AuthQuery S)
    (hq : isAuthSessionQ q = true) (st : SigAuth1KeySimState S) :
    SignDdhStep (4 * st.fg.sim.fgL.length + st.fg.sim.fgRootL.length)
      (fun r => SessListsPost st.fg.sim r.2.fg.sim) (sigAuth1KeyStep S maxLen q st) := by
  have hRefl := sessListsPost_refl st.fg.sim
  unfold sigAuth1KeyStep; split
  · exact ddhStep_mono (Nat.zero_le _) (fun r hr => hr) (ddhStep_pure _ hRefl)
  · cases q with
    | sendOPK u i bundle m0 m1 =>
      dsimp only; unfold sigAuth1KeySend
      refine ddhStep_bind0 ⟨isQueryBoundP_embedPrim_sigDdh _, fun _ _ => trivial⟩ fun _ _ => ?_
      split
      · exact ddhStep_mono (Nat.zero_le _) (fun r hr => hr) (ddhStep_pure _ hRefl)
      · refine sigAuth1KeyDelegate_ddhStep (q := .sendOPK u i bundle m0 m1) (Q := SessListsPost st.fg.sim) hRefl ?_ trivial
        dsimp only [fgAuthStep]; split
        · exact ddhStep_mono (Nat.zero_le _) (fun r hr => hr) (ddhStep_pure _ hRefl)
        · exact fgRunSendAuthGdh_step _ _ S maxLen _ _ u bundle m0 m1 st.fg.sim
    | sendNoOPK u i bundle m0 m1 =>
      dsimp only; unfold sigAuth1KeySend
      refine ddhStep_bind0 ⟨isQueryBoundP_embedPrim_sigDdh _, fun _ _ => trivial⟩ fun _ _ => ?_
      split
      · exact ddhStep_mono (Nat.zero_le _) (fun r hr => hr) (ddhStep_pure _ hRefl)
      · refine sigAuth1KeyDelegate_ddhStep (q := .sendNoOPK u i bundle m0 m1) (Q := SessListsPost st.fg.sim) hRefl ?_ trivial
        dsimp only [fgAuthStep]; split
        · exact ddhStep_mono (Nat.zero_le _) (fun r hr => hr) (ddhStep_pure _ hRefl)
        · exact fgRunSendAuthGdh_step _ _ S maxLen _ _ u bundle m0 m1 st.fg.sim
    | recvOPK k j o msg =>
      dsimp only
      refine sigAuth1KeyDelegate_ddhStep (q := .recvOPK k j o msg) (Q := SessListsPost st.fg.sim) hRefl ?_ trivial
      exact fgRunRecvOPKAuthGdh_step S maxLen k j o msg
        { st.fg.sim with respRecs := { bKey := (k.val, j.val), ikAPk := msg.hdr.ikAPk, ekAPk := msg.hdr.ekAPk } :: st.fg.sim.respRecs }
    | recvNoOPK k j l msg =>
      dsimp only
      refine sigAuth1KeyDelegate_ddhStep (q := .recvNoOPK k j l msg) (Q := SessListsPost st.fg.sim) hRefl ?_ trivial
      exact fgRunRecvNoOPKAuthGdh_step S maxLen k j l msg
        { st.fg.sim with respRecs := { bKey := (k.val, j.val), ikAPk := msg.hdr.ikAPk, ekAPk := msg.hdr.ekAPk } :: st.fg.sim.respRecs }
    | _ => simp [isAuthSessionQ] at hq

private theorem sigAuth1KeyStep_other (S : Setup) (maxLen : ℕ) (q : AuthQuery S)
    (hNotRo : ∀ s, q ≠ .roQuery s) (hNotRoot : ∀ rk dh, q ≠ .roRootQuery rk dh)
    (hNotSess : isAuthSessionQ q = false) (st : SigAuth1KeySimState S) :
    SignDdhStep 0 (fun r => r.2.fg.sim.fgL = st.fg.sim.fgL ∧ r.2.fg.sim.fgRootL = st.fg.sim.fgRootL)
      (sigAuth1KeyStep S maxLen q st) := by
  let QEq : FgAuthSimState S → Prop := fun s => s.fgL = st.fg.sim.fgL ∧ s.fgRootL = st.fg.sim.fgRootL
  have hQRefl : QEq st.fg.sim := ⟨rfl, rfl⟩
  unfold sigAuth1KeyStep; split
  · exact ddhStep_pure _ hQRefl
  · cases q with
    | initPrin u =>
      dsimp only; unfold sigAuth1KeyDelegate
      refine ddhStep_bindR0 (P := fun r => QEq r.2.sim) ?_ fun _ hp => ddhStep_pure _ hp
      unfold fgAuth1KeyStepHalt; split
      · exact ddhStep_pure _ hQRefl
      · dsimp only [fgAuth1KeyStep]; unfold fgAuthInitPrin1KeyGdh; split
        · exact ddhStep_pure _ hQRefl
        · dsimp only
          exact ddhStep_bind0 (signDdhStep_unif _) fun _ _ =>
            ddhStep_bind0 (signDdhStep_primQ _) fun _ _ => ddhStep_pure _ hQRefl
    | genSPK u j =>
      dsimp only; unfold sigAuth1KeyDelegate
      refine ddhStep_bindR0 (P := fun r => QEq r.2.sim) ?_ fun _ hp => ddhStep_pure _ hp
      unfold fgAuth1KeyStepHalt; split
      · exact ddhStep_pure _ hQRefl
      · dsimp only [fgAuth1KeyStep]; unfold fgAuthGenSPK1KeyGdh; split
        · split; · exact ddhStep_pure _ hQRefl
          cases st.fg.sim.base.principals.find? (fun (idx, _) => idx == u.val) with
          | none => exact ddhStep_pure _ hQRefl
          | some p =>
            rcases p with ⟨_, _⟩; dsimp only; split; · exact ddhStep_pure _ hQRefl
            exact ddhStep_bind0 (signDdhStep_unif _) fun _ _ =>
              ddhStep_bind0 (signDdhStep_primQ _) fun _ _ =>
              ddhStep_bind0 (signDdhStep_sigChalQ _) fun _ _ =>
              ddhStep_bind0 (signDdhStep_unif _) fun _ _ =>
              ddhStep_bind0 (signDdhStep_primQ _) fun pqPair _ => by
                rcases pqPair with ⟨_, _⟩; dsimp only
                exact ddhStep_bind0 (signDdhStep_sigChalQ _) fun _ _ => ddhStep_pure _ hQRefl
        · refine liftAuthSimStep1Key_ddhStep (Q := QEq) st.fg ?_; dsimp only [fgAuthStep]; split
          · exact ddhStep_pure _ hQRefl
          · cases st.fg.sim.base.principals.find? (fun (idx, _) => idx == u.val) with
            | none => exact ddhStep_pure _ hQRefl
            | some p =>
              rcases p with ⟨_, _⟩; dsimp only
              gdh_step1; gdh_step1; gdh_step1; gdh_step1; gdh_step1
              refine ddhStep_bind0 (gdhDdhStep_primQ _) fun pqPair _ => ?_
              rcases pqPair with ⟨_, _⟩; dsimp only
              gdh_step1; gdh_step1; exact ddhStep_pure _ hQRefl
    | corruptIK u =>
      refine sigAuth1KeyDelegate_ddhStep (Q := QEq) hQRefl ?_ trivial; dsimp only [fgAuthStep]
      cases st.fg.sim.base.principals.find? (fun (idx, _) => idx == u.val) <;> exact ddhStep_pure _ hQRefl
    | genOPK _ _ _ | registerKey _ =>
      refine sigAuth1KeyDelegate_ddhStep (Q := QEq) hQRefl ?_ trivial; dsimp only [fgAuthStep]; split
      · exact ddhStep_pure _ hQRefl
      · gdh_step0; exact ddhStep_pure _ hQRefl
    | revealDhSecrets =>
      exact sigAuth1KeyDelegate_ddhStep (Q := QEq) hQRefl (ddhStep_pure _ hQRefl) trivial
    | roQuery s => exact False.elim (hNotRo s rfl)
    | roRootQuery rk dh => exact False.elim (hNotRoot rk dh rfl)
    | sendOPK _ _ _ _ _ | sendNoOPK _ _ _ _ _ | recvOPK _ _ _ _ | recvNoOPK _ _ _ _ =>
      simp [isAuthSessionQ] at hNotSess

private def authDdhPhi (r_done root_done s_done r_rem root_rem s_rem : ℕ) : ℕ :=
  4 * r_rem * (s_done + s_rem) + root_rem * (s_done + s_rem) +
    (4 * r_done + root_done) * s_rem + 6 * s_done * s_rem + 3 * s_rem * (s_rem - 1)

private structure AuthDdhInv {S : Setup} (r_done root_done s_done : ℕ) (sim : FgAuthSimState S) : Prop where
  fgS_le   : fgSDone sim.fgL ≤ s_done
  fgLen_le : sim.fgL.length ≤ r_done + s_done
  rtS_le   : rootSDone sim.fgRootL ≤ s_done
  rtLen_le : sim.fgRootL.length ≤ root_done + s_done

private def isAuthRoDom {S : Setup} : (unifSpec + authSpec S).Domain → Bool
  | Sum.inr (.roQuery _) => true | _ => false

private def isAuthRoRootDom {S : Setup} : (unifSpec + authSpec S).Domain → Bool
  | Sum.inr (.roRootQuery _ _) => true | _ => false

private def isAuthSessDom {S : Setup} : (unifSpec + authSpec S).Domain → Bool
  | Sum.inr q => isAuthSessionQ q | Sum.inl _ => false

private theorem qb_step_false {ι : Type} {spec : OracleSpec ι} {α : Type}
    {p : spec.Domain → Bool} {q : spec.Domain} {k : spec.Range q → OracleComp spec α}
    {m : ℕ} (hq : p q = false)
    (h : ∀ u, (k u).IsQueryBoundP (fun x => p x = true) (if p q = true then m - 1 else m))
    (u : spec.Range q) : (k u).IsQueryBoundP (fun x => p x = true) m := by
  have hu := h u; rw [hq] at hu; exact hu

private theorem qb_step_true {ι : Type} {spec : OracleSpec ι} {α : Type}
    {p : spec.Domain → Bool} {q : spec.Domain} {k : spec.Range q → OracleComp spec α}
    {m' : ℕ} (hq : p q = true)
    (h : ∀ u, (k u).IsQueryBoundP (fun x => p x = true) (if p q = true then (m' + 1) - 1 else m' + 1))
    (u : spec.Range q) : (k u).IsQueryBoundP (fun x => p x = true) m' := by
  have hu := h u; rw [hq] at hu; exact hu

private theorem qb_bind_le {ι : Type} {spec : OracleSpec ι} {α β : Type}
    {p : spec.Domain → Bool} {oa : OracleComp spec α} {k : α → OracleComp spec β} {n1 n : ℕ}
    (n2 : ℕ) (h1 : oa.IsQueryBoundP (fun q => p q = true) n1)
    (h2 : ∀ x ∈ support oa, (k x).IsQueryBoundP (fun q => p q = true) n2) (hle : n1 + n2 ≤ n) :
    (oa >>= k).IsQueryBoundP (fun q => p q = true) n :=
  (isQueryBoundP_bind h1 h2).mono hle

private theorem isQueryBoundP_runWithGdhSignStep_authDdhPhi {S : Setup} {α : Type}
    (maxLen : ℕ) (mx : OracleComp (unifSpec + authSpec S) α) :
    ∀ (r_done root_done s_done r_rem root_rem s_rem : ℕ) (st : SigAuth1KeySimState S),
      AuthDdhInv r_done root_done s_done st.fg.sim →
      mx.IsQueryBoundP (fun q => isAuthRoDom q = true) r_rem →
      mx.IsQueryBoundP (fun q => isAuthRoRootDom q = true) root_rem →
      mx.IsQueryBoundP (fun q => isAuthSessDom q = true) s_rem →
      (runWithGdhSignStep (sigAuth1KeyStep S maxLen) mx st).IsQueryBoundP
        (fun q => isDdhChalQuery q = true)
        (authDdhPhi r_done root_done s_done r_rem root_rem s_rem) := by
  induction mx using OracleComp.inductionOn with
  | pure _ =>
    intro _ _ _ _ _ _ _ _ _ _ _
    simp only [runWithGdhSignStep_pure]
    exact (isQueryBoundP_pure (fun q => isDdhChalQuery q = true) _ 0).mono (Nat.zero_le _)
  | query_bind q k ih =>
    intro r_done root_done s_done r_rem root_rem s_rem st hInv hRo hRoot hSess
    rw [isQueryBoundP_query_bind_iff] at hRo hRoot hSess
    cases q with
    | inl _ =>
      rw [runWithGdhSignStep_query_inl, isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (fun h => by cases h), fun u =>
        ih u r_done root_done s_done r_rem root_rem s_rem st hInv (hRo.2 u) (hRoot.2 u) (hSess.2 u)⟩
    | inr gq =>
      rw [runWithGdhSignStep_query_inr]
      by_cases hR : ∃ s, gq = .roQuery s
      · rcases hR with ⟨secrets, rfl⟩
        have hPos : 0 < r_rem := hRo.1.resolve_left (fun hc => hc rfl)
        obtain ⟨r', rfl⟩ : ∃ r', r_rem = r' + 1 := ⟨r_rem - 1, by omega⟩
        let QRo : FgAuthSimState S → Prop := fun sim =>
          fgSDone sim.fgL = fgSDone st.fg.sim.fgL ∧
            sim.fgL.length ≤ st.fg.sim.fgL.length + 1 ∧ sim.fgRootL = st.fg.sim.fgRootL
        have hs : SignDdhStep (4 * fgSDone st.fg.sim.fgL)
            (fun r => QRo r.2.fg.sim)
            (sigAuth1KeyStep S maxLen (.roQuery secrets) st) := by
          unfold sigAuth1KeyStep; split
          · exact ddhStep_mono (Nat.zero_le _) (fun r hr => hr) (ddhStep_pure _ ⟨rfl, Nat.le_succ _, rfl⟩)
          · exact sigAuth1KeyDelegate_ddhStep (Q := QRo) ⟨rfl, Nat.le_succ _, rfl⟩
              (fgRoQueryAuthGdh_step maxLen secrets st.fg.sim) trivial
        refine qb_bind_le (authDdhPhi (r_done + 1) root_done s_done r' root_rem s_rem)
          (hs.1.mono (Nat.mul_le_mul_left 4 hInv.fgS_le)) (fun p hp => ?_)
          (by unfold authDdhPhi; nlinarith)
        rcases hs.2 p hp with ⟨hS, hL, hRt⟩
        exact ih p.1 (r_done + 1) root_done s_done r' root_rem s_rem p.2
          ⟨by rw [hS]; exact hInv.fgS_le, by have := hInv.fgLen_le; omega,
           by rw [hRt]; exact hInv.rtS_le, by rw [hRt]; exact hInv.rtLen_le⟩
          (qb_step_true (p := isAuthRoDom) rfl hRo.2 p.1)
          (qb_step_false (p := isAuthRoRootDom) rfl hRoot.2 p.1)
          (qb_step_false (p := isAuthSessDom) rfl hSess.2 p.1)
      · have hNRo : isAuthRoDom (Sum.inr gq) = false := by cases gq <;> simp_all [isAuthRoDom]
        by_cases hRt : ∃ rk dh, gq = .roRootQuery rk dh
        · rcases hRt with ⟨rk, dh, rfl⟩
          have hPos : 0 < root_rem := hRoot.1.resolve_left (fun hc => hc rfl)
          obtain ⟨root', rfl⟩ : ∃ root', root_rem = root' + 1 := ⟨root_rem - 1, by omega⟩
          let QRt : FgAuthSimState S → Prop := fun sim =>
            sim.fgL = st.fg.sim.fgL ∧
              rootSDone sim.fgRootL = rootSDone st.fg.sim.fgRootL ∧
              sim.fgRootL.length ≤ st.fg.sim.fgRootL.length + 1
          have hs : SignDdhStep (rootSDone st.fg.sim.fgRootL)
              (fun r => QRt r.2.fg.sim)
              (sigAuth1KeyStep S maxLen (.roRootQuery rk dh) st) := by
            unfold sigAuth1KeyStep; split
            · exact ddhStep_mono (Nat.zero_le _) (fun r hr => hr) (ddhStep_pure _ ⟨rfl, rfl, Nat.le_succ _⟩)
            · exact sigAuth1KeyDelegate_ddhStep (Q := QRt) ⟨rfl, rfl, Nat.le_succ _⟩
                (fgRoRootQueryAuthGdh_step maxLen rk dh st.fg.sim) trivial
          refine qb_bind_le (authDdhPhi r_done (root_done + 1) s_done r_rem root' s_rem)
            (hs.1.mono hInv.rtS_le) (fun p hp => ?_)
            (by unfold authDdhPhi; nlinarith)
          rcases hs.2 p hp with ⟨hFg, hRtS, hRtL⟩
          exact ih p.1 r_done (root_done + 1) s_done r_rem root' s_rem p.2
            ⟨by rw [hFg]; exact hInv.fgS_le, by rw [hFg]; exact hInv.fgLen_le,
             by rw [hRtS]; exact hInv.rtS_le, by have := hInv.rtLen_le; omega⟩
            (qb_step_false (p := isAuthRoDom) rfl hRo.2 p.1)
            (qb_step_true (p := isAuthRoRootDom) rfl hRoot.2 p.1)
            (qb_step_false (p := isAuthSessDom) rfl hSess.2 p.1)
        · have hNRt : isAuthRoRootDom (Sum.inr gq) = false := by cases gq <;> simp_all [isAuthRoRootDom]
          by_cases hS : isAuthSessionQ gq = true
          · have hSDom : isAuthSessDom (Sum.inr gq) = true := hS
            have hPos : 0 < s_rem := hSess.1.resolve_left (by simp [isAuthSessDom, hS])
            obtain ⟨s', rfl⟩ : ∃ s', s_rem = s' + 1 := ⟨s_rem - 1, by omega⟩
            have hs := sigAuth1KeyStep_sess S maxLen gq hS st
            have hStepLe : 4 * st.fg.sim.fgL.length + st.fg.sim.fgRootL.length ≤
                4 * r_done + root_done + 5 * s_done := by
              have := hInv.fgLen_le; have := hInv.rtLen_le; omega
            have hPhi : (4 * r_done + root_done + 5 * s_done) +
                authDdhPhi r_done root_done (s_done + 1) r_rem root_rem s' ≤
                authDdhPhi r_done root_done s_done r_rem root_rem (s' + 1) := by
              unfold authDdhPhi; rcases s' with _ | _
              · simp; omega
              · simp only [Nat.add_sub_cancel]; nlinarith
            refine qb_bind_le (authDdhPhi r_done root_done (s_done + 1) r_rem root_rem s')
              (hs.1.mono hStepLe) (fun p hp => ?_) hPhi
            rcases hs.2 p hp with ⟨hFgS, hFgL, hRtS, hRtL⟩
            exact ih p.1 r_done root_done (s_done + 1) r_rem root_rem s' p.2
              ⟨by have := hInv.fgS_le; omega, by have := hInv.fgLen_le; omega,
               by have := hInv.rtS_le; omega, by have := hInv.rtLen_le; omega⟩
              (qb_step_false (p := isAuthRoDom) hNRo hRo.2 p.1)
              (qb_step_false (p := isAuthRoRootDom) hNRt hRoot.2 p.1)
              (qb_step_true (p := isAuthSessDom) hSDom hSess.2 p.1)
          · have hNS : isAuthSessionQ gq = false := Bool.eq_false_iff.mpr hS
            have hNSDom : isAuthSessDom (Sum.inr gq) = false := hNS
            have hs := sigAuth1KeyStep_other S maxLen gq
              (fun s hs => hR ⟨s, hs⟩) (fun rk dh hr => hRt ⟨rk, dh, hr⟩) hNS st
            refine qb_bind_le (authDdhPhi r_done root_done s_done r_rem root_rem s_rem)
              hs.1 (fun p hp => ?_) (by omega)
            rcases hs.2 p hp with ⟨hFg, hRtE⟩
            exact ih p.1 r_done root_done s_done r_rem root_rem s_rem p.2
              ⟨by rw [hFg]; exact hInv.fgS_le, by rw [hFg]; exact hInv.fgLen_le,
               by rw [hRtE]; exact hInv.rtS_le, by rw [hRtE]; exact hInv.rtLen_le⟩
              (qb_step_false (p := isAuthRoDom) hNRo hRo.2 p.1)
              (qb_step_false (p := isAuthRoRootDom) hNRt hRoot.2 p.1)
              (qb_step_false (p := isAuthSessDom) hNSDom hSess.2 p.1)

private theorem isQueryBoundP_min_tot {S : Setup} {α : Type}
    {mx : OracleComp (unifSpec + authSpec S) α} (p : (unifSpec + authSpec S).Domain → Bool)
    {m q_tot : ℕ} (hp : ∀ n, p (Sum.inl n) = false)
    (hm : mx.IsQueryBoundP (fun q => p q = true) m)
    (ht : mx.IsQueryBoundP (fun q => SignalPqxdh.isGameQuery q = true) q_tot) :
    mx.IsQueryBoundP (fun q => p q = true) (min m q_tot) := by
  by_cases h : m ≤ q_tot
  · simpa [Nat.min_eq_left h] using hm
  · simpa [Nat.min_eq_right (Nat.le_of_not_le h)] using isQueryBoundP_of_imp
      (fun t ht' => by rcases t with n | _ <;> [simp [hp] at ht'; simp [SignalPqxdh.isGameQuery]]) ht

/-- Bilinear DDH-query bound for the shallow reduction `sigReductionAuth1Key`. -/
theorem isQueryBoundP_sigReductionAuth1Key_ddh_shallow (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) (pk : Bytes) :
    ((sigReductionAuth1Key S b A).run pk).IsQueryBoundP
      (fun q => isDdhChalQuery q = true)
      ((4 * min b.q_ro b.q_total + min b.q_roRoot b.q_total) *
          min (min b.q_on b.q_total) S.N_sess_tot +
        3 * min (min b.q_on b.q_total) S.N_sess_tot *
          (min (min b.q_on b.q_total) S.N_sess_tot - 1)) := by
  let M_ro := min b.q_ro b.q_total
  let M_root := min b.q_roRoot b.q_total
  let M_sess := min (min b.q_on b.q_total) S.N_sess_tot
  obtain ⟨hRoRaw, _, _, hRootRaw, hTotRaw, _⟩ := A.2
  have hSessB := authAdv_sessionBound_on S b A
  have hRoM := isQueryBoundP_min_tot isAuthRoDom (fun _ => rfl)
    (isQueryBoundP_of_imp (fun t ht => by
      rcases t with _ | gq <;> [cases ht; cases gq <;> simp_all [isAuthRoDom, isAuthRoQuery]])
      hRoRaw) hTotRaw
  have hRootM := isQueryBoundP_min_tot isAuthRoRootDom (fun _ => rfl)
    (isQueryBoundP_of_imp (fun t ht => by
      rcases t with _ | gq <;> [cases ht; cases gq <;> simp_all [isAuthRoRootDom, isAuthRoRootQuery]])
      hRootRaw) hTotRaw
  have hSessM : A.1.run.IsQueryBoundP (fun q => isAuthSessDom q = true) M_sess := by
    have hEq : M_sess = min (min b.q_on S.N_sess_tot) b.q_total := by dsimp only [M_sess]; omega
    rw [hEq]
    exact isQueryBoundP_min_tot isAuthSessDom (fun _ => rfl)
      (isQueryBoundP_of_imp (fun t ht => by rcases t with _ | _ <;> [cases ht; exact ht]) hSessB)
      hTotRaw
  dsimp only [sigReductionAuth1Key]
  refine qb_bind_le ((4 * M_ro + M_root) * M_sess + 3 * M_sess * (M_sess - 1))
    (signDdhStep_unif _).1 (fun targetParty _ => ?_)
    (by dsimp only [M_ro, M_root, M_sess]; rw [Nat.zero_add])
  unfold sigReductionAuth1KeyRunAt
  refine qb_bind_le (authDdhPhi 0 0 0 M_ro M_root M_sess + 0)
    (signDdhStep_unif ($ᵗ Bool)).1 (fun secb _ => ?_)
    (by unfold authDdhPhi; nlinarith)
  exact isQueryBoundP_bind
    (isQueryBoundP_runWithGdhSignStep_authDdhPhi b.q_total A.1.run
      0 0 0 M_ro M_root M_sess (SigAuth1KeySimState.empty S secb targetParty pk)
      ⟨by simp [SigAuth1KeySimState.empty, FgAuth1KeySimState.empty, FgAuthSimState.empty, fgSDone],
       by simp [SigAuth1KeySimState.empty, FgAuth1KeySimState.empty, FgAuthSimState.empty],
       by simp [SigAuth1KeySimState.empty, FgAuth1KeySimState.empty, FgAuthSimState.empty, rootSDone],
       by simp [SigAuth1KeySimState.empty, FgAuth1KeySimState.empty, FgAuthSimState.empty]⟩
      hRoM hRootM hSessM)
    fun _ _ => isQueryBoundP_pure _ _ 0

end Auth1KeySigBilinearDdh
end SignalPqxdh.Security.ReductionDsl.AuthHs
