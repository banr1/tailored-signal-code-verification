/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.AtomicOpsHonest
public import Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge
public import Computational.Proofs.ReductionDsl.Bridge
public import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds
public import Computational.Proofs.E2E.UniformStartHop
public import Computational.Proofs.E2E.Dsl.StartAndExtSmAux
public import Computational.Specifications.Session.StatementComposed

/-!
# Shared Infrastructure for Single-Session Costed Reductions

Provides the forward-encoding simulation bridge (`eval_eq_simulateQ_of_enc`), `e2eSessionCodec`
transport lemmas, the initial-state sampler (`initEpoch0GsC`), polynomial `ratchetCostBudget`
arithmetic, and dummy fallback reductions for single-session `CostedReduction` witnesses.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon

open OracleSpec OracleComp
open ReductionDsl (Sig Ty Var Env Ops Samplers Iface Expr Comp GameCodec CostedReduction
  UniformSamplerTag bits bits_mono bits_le_of_lt lt_two_pow_bits reductionSizeBudget
  isGameQuery handlerImpl bind_congr_of_mem_support'
  simulateQ_run_abs_of_bound atomicSig atomicSamplers atomicSessionOps coinOnlyIface
  e2eSessionCodec BV256 BV512 GhostStT PlainT B)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.Ratchet (RootKey)
open CryptoGames.Ratchet.LibsignalInst (libsignalSessionSchemeFromEpoch0Keys)
open CryptoGames.SM (GameState initState oracleImplR MakesAtMostQueries)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey GhostState maxForwardJumps)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.LibsignalSession (ratchetCostBudget GRedBounded)
open CryptoVerification.E2E (Bytes SampledSessionKey paramsIdsWithSpqr paramsV1
  sessionSchemeFixedSpk toU8 ofU8 fitVec u8Vec)
open CryptoVerification.E2E.HeadlineU (sample_prod_bindU)
open CryptoVerification.E2E.Costed (e2eSig e2eOps E2EPureOp e2ePureOps E2ECurveCheckOp
  e2eCurveCheckOps E2ECryptoOp)
open Computational.Proofs.E2E.Dsl.TablesHonest (e2ePureOp eval_e2ePureOp cost_e2ePureOp
  e2eCryptoOp)
open Computational.Proofs.E2E.Dsl.PqxdhSimTypes (v eLet eCaseOpt)
open Computational.Proofs.E2E.Dsl.SmReachInv (SmReachBounded smReachBounded_initState)
open Computational.Proofs.E2E.Dsl.M2Interfaces (smRenc smRdec_smRenc_id e2eGsTy e2eGsEnc)
open Computational.Proofs.E2E.Dsl.StartAndExtSmAux (initFixedSpkBobE initFixedSpkAliceE
  initFixedSpkGsE eval_initFixedSpkGsE cost_initFixedSpkGsE)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge (sessPureOp sessCurveOp
  sessSymOp sessSpqrKemOp zeroPqxdhPrims
  liftTy liftCtx liftVal liftEnv liftPureOpExpr liftCurveOpExpr liftCryptoOpExpr liftOpExpr
  liftExpr liftExpr_cost liftExpr_eval emptyE2EIface liftCompEmpty
  coinE2EIface liftSampComp liftCompCoins liftCompCoins_queries_zero liftCompCoins_cost
  liftCompCoins_eval renExpr renComp wk1Expr wk1Comp)

/-! ## Structural stepping lemmas -/

theorem letE_eval {S : Sig} {O : Ops S} {Γ : List (Ty S)} {a b : Ty S}
    (e₁ : Expr O Γ a) (e₂ : Expr O (a :: Γ) b) (ρ : Env Γ) :
    (Expr.letE e₁ e₂).eval ρ = e₂.eval (.cons (e₁.eval ρ) ρ) := rfl

theorem comp_eval_ret {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {a : Ty S} (e : Expr O Γ a) (ρ : Env Γ) :
    (Comp.ret (I := I) e).eval ρ = pure (e.eval ρ) := rfl

theorem comp_eval_bind {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {a b : Ty S} (c₁ : Comp O I Γ a) (c₂ : Comp O I (a :: Γ) b) (ρ : Env Γ) :
    (Comp.bind c₁ c₂).eval ρ = (c₁.eval ρ >>= fun v => c₂.eval (.cons v ρ)) := rfl

theorem comp_eval_bind_ret {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {a b : Ty S} (e : Expr O Γ a) (c₂ : Comp O I (a :: Γ) b) (ρ : Env Γ) :
    (Comp.bind (.ret e) c₂).eval ρ = c₂.eval (.cons (e.eval ρ) ρ) := by
  change (pure (e.eval ρ) >>= fun v => c₂.eval (.cons v ρ)) = _
  exact pure_bind (e.eval ρ) (fun v => c₂.eval (.cons v ρ))

theorem comp_eval_ite {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {a : Ty S} (cond : Expr O Γ .bool) (t e : Comp O I Γ a) (ρ : Env Γ) :
    (Comp.ite cond t e).eval ρ = (if cond.eval ρ then t.eval ρ else e.eval ρ) := rfl

theorem comp_eval_caseOpt {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {a b : Ty S}
    (scrut : Expr O Γ (.opt a)) (noneArm : Comp O I Γ b) (someArm : Comp O I (a :: Γ) b)
    (ρ : Env Γ) :
    (Comp.caseOpt scrut noneArm someArm).eval ρ =
      match scrut.eval ρ with
      | none => noneArm.eval ρ
      | some v => someArm.eval (.cons v ρ) := rfl

theorem comp_eval_caseSum {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {a b c : Ty S}
    (scrut : Expr O Γ (.sum a b)) (inlArm : Comp O I (a :: Γ) c) (inrArm : Comp O I (b :: Γ) c)
    (ρ : Env Γ) :
    (Comp.caseSum scrut inlArm inrArm).eval ρ =
      match scrut.eval ρ with
      | .inl va => inlArm.eval (.cons va ρ)
      | .inr vb => inrArm.eval (.cons vb ρ) := rfl

/-! ## Forward-encoding simulation bridge -/

/-- Connects `R.eval` to `simulateQ so` when `R` maintains the forward encoding `enc s` of a game
state satisfying a remaining-query invariant `Inv`. -/
theorem eval_eq_simulateQ_of_enc {S : Sig} {O : Ops S} {ι κ : Type} {T : OracleSpec ι}
    {I : Iface S T} {G : OracleSpec κ} {GC : GameCodec S G}
    {rIn aIn aOut out : Ty S} (R : CostedReduction O I G GC rIn aIn aOut out) {σ₁ : Type}
    (enc : σ₁ → R.σ.denote) (Inv : ℕ → σ₁ → Prop)
    (initImpl : rIn.denote → OracleComp T (aIn.denote × σ₁))
    (so : QueryImpl (unifSpec + G) (StateT σ₁ (OracleComp T)))
    (finishImpl : σ₁ → aOut.denote → OracleComp T out.denote)
    (qAdv : ℕ) (x : rIn.denote)
    (hinit : R.init.eval (.cons x .nil) = Prod.map id enc <$> initImpl x)
    (hinitInv : ∀ r ∈ support (initImpl x), Inv qAdv r.2)
    (hU : ∀ n s, (so (.inl n)).run s = (StateT.lift (I.fwdU n)).run s)
    (hstep : ∀ m t s, Inv (m + 1) s →
      (R.impl (.inr t)).run (enc s) = Prod.map id enc <$> (so (.inr t)).run s ∧
      ∀ r ∈ support ((so (.inr t)).run s), Inv m r.2)
    (hfin : ∀ s b, Inv 0 s → R.finish.eval (.cons (enc s) (.cons b .nil)) = finishImpl s b)
    (hmono : ∀ {m n} (s), m ≤ n → Inv n s → Inv m s)
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote)
    (hb : ∀ a, (A a).IsQueryBoundP (isGameQuery (G := G)) qAdv) :
    R.eval A x = (do
      let (a, s₀) ← initImpl x
      let (b, s₁) ← (simulateQ so (A a)).run s₀
      finishImpl s₁ b) := by
  let Inv' : ℕ → σ₁ → Prop := fun q s => Inv q s ∧ Inv 0 s
  have hU' : ∀ q n s, Inv' q s →
      (Prod.map id enc <$> (so (.inl n)).run s) = (R.impl (.inl n)).run (enc s) ∧
      ∀ r ∈ support ((so (.inl n)).run s), Inv' q r.2 := by
    intro q n s hs
    refine ⟨?_, ?_⟩
    · simp [CostedReduction.impl, handlerImpl, hU, StateT.run_lift, Prod.map,
        map_eq_bind_pure_comp]
    · intro r hr
      rw [hU] at hr
      simp only [StateT.run_lift, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
      obtain ⟨u, -, rfl⟩ := hr
      exact hs
  have hstep' : ∀ m t s, Inv' (m + 1) s →
      (Prod.map id enc <$> (so (.inr t)).run s) = (R.impl (.inr t)).run (enc s) ∧
      ∀ r ∈ support ((so (.inr t)).run s), Inv' m r.2 := by
    intro m t s hs
    obtain ⟨heq, hinv⟩ := hstep m t s hs.1
    exact ⟨heq.symm, fun r hr => ⟨hinv r hr, hmono r.2 (Nat.zero_le m) (hinv r hr)⟩⟩
  simp only [CostedReduction.eval, hinit, bind_map_left]
  refine bind_congr_of_mem_support' (initImpl x) (fun ⟨a, s₀⟩ hr₀ => ?_)
  have hs₀ : Inv' qAdv s₀ :=
    ⟨hinitInv (a, s₀) hr₀, hmono s₀ (Nat.zero_le qAdv) (hinitInv (a, s₀) hr₀)⟩
  have hsim := (simulateQ_run_abs_of_bound so R.impl enc Inv' hU' hstep' (hb a) s₀ hs₀).symm
  have hinvEnd : ∀ r ∈ support ((simulateQ so (A a)).run s₀), Inv 0 r.2 := by
    have hpreserve : ∀ {α : Type} {oa : OracleComp (unifSpec + G) α} {q : ℕ},
        oa.IsQueryBoundP (isGameQuery (G := G)) q →
        ∀ s, Inv' q s → ∀ r ∈ support ((simulateQ so oa).run s), Inv 0 r.2 := by
      intro α oa
      induction oa using OracleComp.inductionOn with
      | pure b =>
        intro q _ s hs r hr
        simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact hs.2
      | query_bind q mx ih =>
        intro qB hq s hs r hr
        rw [isQueryBoundP_query_bind_iff] at hq
        rw [run_simulateQ_query_bind, mem_support_bind_iff] at hr
        obtain ⟨⟨u, s'⟩, hst, hr⟩ := hr
        cases q with
        | inl n =>
          exact ih u (hq.2 u) s' ((hU' qB n s hs).2 (u, s') hst) r hr
        | inr t =>
          have hpos : 0 < qB := hq.1.resolve_left (by simp [isGameQuery])
          obtain ⟨m, rfl⟩ : ∃ m, qB = m + 1 := ⟨qB - 1, by omega⟩
          have hqm : ∀ v, (mx v).IsQueryBoundP (isGameQuery (G := G)) m := by
            intro v; simpa [isGameQuery] using hq.2 v
          exact ih u (hqm u) s' ((hstep' m t s hs).2 (u, s') hst) r hr
    exact hpreserve (hb a) s₀ hs₀
  dsimp only [Prod.map, id_eq] at hsim ⊢
  rw [hsim, bind_map_left]
  refine bind_congr_of_mem_support' ((simulateQ so (A a)).run s₀) (fun ⟨b, s₁⟩ hr₁ => ?_)
  exact hfin s₁ b (hinvEnd (b, s₁) hr₁)

theorem isQueryBoundP_of_makesAtMostQueries {St Msg Coins C : Type}
    {A : CryptoGames.SM.Adversary St Msg Coins C} {q : ℕ}
    (hA : MakesAtMostQueries A q) :
    A.IsQueryBoundP (isGameQuery (G := CryptoGames.SM.spec St Msg Coins C)) q :=
  hA.of_imp (fun t ht => by cases t <;> simp_all [isGameQuery])

theorem liftP_unif_eq_self {S0 : Sig} (I0 : Iface S0 unifSpec)
    (hfwd : ∀ n, I0.fwdU n = query (spec := unifSpec) n)
    {α : Type} (p : ProbComp α) : I0.liftP p = p := by
  induction p using OracleComp.inductionOn with
  | pure a => simp [Iface.liftP]
  | query_bind n mx ih =>
    dsimp only [Iface.liftP] at ih ⊢
    rw [simulateQ_bind, simulateQ_query, hfwd]
    exact bind_congr ih

/-! ## Codec transport -/

section CodecTransport

variable {ℓ : ℕ} (Pt : Type)

@[simp] theorem liftVal_smQenc
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    liftVal (Pt := Pt) (CryptoVerification.E2E.Costed.smQenc (ℓ := ℓ) sq) =
      (e2eSessionCodec ℓ Pt).qenc sq := by
  rcases sq with (((⟨p, m, r⟩ | ⟨p, m0, m1, r⟩) | ⟨p, c⟩) | ⟨p, c⟩) | p <;>
    cases p <;> (try cases r) <;> rfl

@[simp] theorem e2eSessionCodec_rdec_liftVal
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (r : (CryptoVerification.E2E.Costed.smRT (ℓ := ℓ)
      CryptoVerification.E2E.Costed.GhostStT).denote) :
    (e2eSessionCodec ℓ Pt).rdec sq (liftVal (Pt := Pt) r) =
      CryptoVerification.E2E.Costed.smRdec (stT := CryptoVerification.E2E.Costed.GhostStT) id sq r := by
  rcases sq with (((_ | _) | _) | _) | _ <;>
    rcases r with ⟨_ | _, _ | (_ | ⟨_, _, _ | _⟩), _ | _⟩ <;> rfl

@[simp] theorem e2eSessionCodec_rdec_liftVal_smRenc
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (ans : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range sq) :
    (e2eSessionCodec ℓ Pt).rdec sq
      (liftVal (Pt := Pt)
        (smRenc (ℓ := ℓ) (stT := CryptoVerification.E2E.Costed.GhostStT) id sq ans)) = ans := by
  rw [e2eSessionCodec_rdec_liftVal, smRdec_smRenc_id]

end CodecTransport

/-! ## Epoch-0 state initialization -/

section Epoch0Init

private theorem ofU8_toU8 (bs : Bytes) : ofU8 (toU8 bs) = bs := by
  simp [ofU8, toU8, List.map_map, Function.comp_def]

private theorem u8Vec_toU8_vec {n : ℕ} (v : List.Vector (BitVec 8) n) :
    u8Vec n (toU8 v.toList) = v := by
  rcases v with ⟨xs, hxs⟩
  apply List.Vector.eq
  dsimp only [u8Vec, fitVec]
  change List.take n (ofU8 (toU8 xs) ++ List.replicate n 0#8) = xs
  rw [ofU8_toU8, List.take_append_of_le_length (Nat.le_of_eq hxs.symm)]
  exact List.take_of_length_le (Nat.le_of_eq hxs)

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  {C : Crypto} {K : MlKem}
  {Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
  {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
local notation "ESig" => e2eSig ℓ
local notation "EOps" => e2eOps ℓ zeroPqxdhPrims C K decT encT

omit [SampleableType Pt] in
private theorem liftPureOpExpr_size {Γ : List (Ty ASig)} (o : E2EPureOp)
    (a : Expr AOps Γ (liftTy (Pt := Pt) (o.dom ℓ))) :
    (liftPureOpExpr (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).size = a.size + o.opSize + 1 := by
  cases o <;> rfl

omit [SampleableType Pt] in
private theorem liftCurveOpExpr_size {Γ : List (Ty ASig)} (cc : E2ECurveCheckOp)
    (a : Expr AOps Γ (liftTy (Pt := Pt) ((e2eCurveCheckOps ℓ decT encT).dom cc))) :
    (liftCurveOpExpr (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) cc a).size = a.size + 1 := by
  cases cc <;> rfl

omit [SampleableType Pt] in
set_option linter.unusedSimpArgs false in
private theorem liftCryptoOpExpr_size {Γ : List (Ty ASig)} (c : E2ECryptoOp)
    (a : Expr AOps Γ (liftTy (Pt := Pt) (c.dom ℓ))) :
    (liftCryptoOpExpr (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) c a).size ≤ a.size + 9 := by
  have hop : ∀ o : _root_.ReductionDsl.AtomicPureOp,
      (AOps).opSize (Sum.inl (Sum.inl (Sum.inl (Sum.inl o)))) = o.opSize := fun _ => rfl
  have hsym : ∀ o : _root_.ReductionDsl.AtomicSymOp,
      (AOps).opSize (Sum.inl (Sum.inl (Sum.inl (Sum.inr (Sum.inr o))))) = 0 := fun _ => rfl
  have hspqr : ∀ o : _root_.ReductionDsl.AtomicSpqrKemOp,
      (AOps).opSize (Sum.inr o) = 0 := fun _ => rfl
  cases c <;>
    (simp only [liftCryptoOpExpr, sessPureOp, sessSymOp, sessSpqrKemOp, Expr.size,
      hop, hsym, hspqr, _root_.ReductionDsl.AtomicPureOp.opSize, List.length_nil, Nat.add_assoc]
     exact Nat.add_le_add_left (by decide) _)

omit [SampleableType Pt] in
private theorem liftOpExpr_size {Γ : List (Ty ASig)}
    (o : (e2eOps ℓ zeroPqxdhPrims C K decT encT).Op)
    (a : Expr AOps Γ (liftTy (Pt := Pt) ((e2eOps ℓ zeroPqxdhPrims C K decT encT).dom o))) :
    (liftOpExpr (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).size ≤
      a.size + 9 * (e2eOps ℓ zeroPqxdhPrims C K decT encT).opSize o + 9 := by
  rcases o with o | (cc | c)
  · dsimp only [liftOpExpr, e2eOps, _root_.ReductionDsl.Ops.sum, _root_.ReductionDsl.Ops.dom,
      _root_.ReductionDsl.Ops.opSize, e2ePureOps, Sum.elim] at a ⊢
    have h := liftPureOpExpr_size (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) o a
    omega
  · exact (liftCurveOpExpr_size cc a).le.trans
      (Nat.add_le_add_left (by change 1 ≤ 9 * 0 + 9; decide) _)
  · exact (liftCryptoOpExpr_size c a).trans
      (Nat.add_le_add_left (by change 9 ≤ 9 * 0 + 9; decide) _)

omit [SampleableType Pt] in
theorem liftExpr_size_le {Γ : List (Ty ESig)} {t : Ty ESig} (e : Expr EOps Γ t) :
    (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) e).size ≤ 9 * e.size := by
  induction e with
  | var _ | unit | bool _ | none | nil => simp [liftExpr, Expr.size]
  | nat _ => simp only [liftExpr, Expr.size]; omega
  | add _ _ ha hb | sub _ _ ha hb | lt _ _ ha hb | eqN _ _ ha hb | and _ _ ha hb
  | pair _ _ ha hb | cons _ _ ha hb | take _ _ ha hb | appendL _ _ _ ha hb
  | letE _ _ ha hb | tget _ _ ha hb | findB _ _ _ ha hb | anyB _ _ _ ha hb
  | mapB _ _ _ ha hb =>
    simp only [liftExpr, Expr.size]; omega
  | mulK _ _ ha | divK _ _ ha | modK _ _ ha | not _ ha | fst _ ha | snd _ ha
  | inl _ ha | inr _ ha | some _ ha | len _ ha | tconst _ ha =>
    simp only [liftExpr, Expr.size]; omega
  | ite _ _ _ hc ha hb | caseOpt _ _ _ hc ha hb | caseSum _ _ _ hc ha hb
  | tset _ _ _ hc ha hb | foldrB _ _ _ _ hc ha hb =>
    simp only [liftExpr, Expr.size]; omega
  | op o a ha =>
    have ho := liftOpExpr_size (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o (liftExpr a)
    simp only [liftExpr, Expr.size] at ho ⊢
    omega

omit [SampleableType Pt] in
theorem liftCompEmpty_size_le {ι : Type} {T : OracleSpec ι} {I' : Iface ASig T}
    {Γ : List (Ty ESig)} {t : Ty ESig} (c : Comp EOps (emptyE2EIface I') Γ t) :
    (liftCompEmpty (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) c).size ≤ 9 * c.size := by
  induction c with
  | ret e =>
    have he := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) e
    simp only [liftCompEmpty, Comp.size]; omega
  | bind _ _ hc hk =>
    simp only [liftCompEmpty, Comp.size]; omega
  | ite b _ _ hc hd | caseOpt b _ _ hc hd | caseSum b _ _ hc hd =>
    have hb := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) b
    simp only [liftCompEmpty, Comp.size]; omega
  | sample s _ => exact s.elim
  | query g _ => exact g.elim
  | iter _ e _ ih | findM _ e _ ih | anyM _ e _ ih | mapM _ e _ ih =>
    have he := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) e
    simp only [liftCompEmpty, Comp.size]; omega
  | consumeFirstM _ l _ mk ih =>
    have hl := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) l
    have hmk := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) mk
    simp only [liftCompEmpty, Comp.size]; omega
  | foldM _ l z _ ih =>
    have hl := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) l
    have hz := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) z
    simp only [liftCompEmpty, Comp.size]; omega

private theorem liftSampComp_size {ι : Type} {T : OracleSpec ι}
    {I' : Iface ASig T} (hsmp : I'.smp = atomicSamplers ℓ Pt) {Γ : List (Ty ASig)}
    (s : UniformSamplerTag CryptoVerification.E2E.Costed.E2EUnifBase) (a : Expr AOps Γ .unit) :
    (liftSampComp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' hsmp s a).size = a.size + 1 := by
  rcases I' with ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, smp⟩
  dsimp only at hsmp; subst hsmp
  rcases s with _ | N | (_ | _) <;> rfl

theorem liftCompCoins_size_le {ι : Type} {T : OracleSpec ι}
    {I' : Iface ASig T} (hsmp : I'.smp = atomicSamplers ℓ Pt)
    {Γ : List (Ty ESig)} {t : Ty ESig} (c : Comp EOps (coinE2EIface I') Γ t) :
    (liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) hsmp c).size ≤ 9 * c.size := by
  induction c with
  | ret e =>
    have he := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) e
    simp only [liftCompCoins, Comp.size]; omega
  | bind _ _ hc hk =>
    simp only [liftCompCoins, Comp.size]; omega
  | ite b _ _ hc hd | caseOpt b _ _ hc hd | caseSum b _ _ hc hd =>
    have hb := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) b
    simp only [liftCompCoins, Comp.size]; omega
  | sample s a =>
    have ha := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) a
    have hs := liftSampComp_size (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) hsmp s (liftExpr a)
    dsimp only [liftCompCoins, Comp.size] at hs ⊢
    omega
  | query g _ => exact g.elim
  | iter _ e _ ih | findM _ e _ ih | anyM _ e _ ih | mapM _ e _ ih =>
    have he := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) e
    simp only [liftCompCoins, Comp.size]; omega
  | consumeFirstM _ l _ mk ih =>
    have hl := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) l
    have hmk := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) mk
    simp only [liftCompCoins, Comp.size]; omega
  | foldM _ l z _ ih =>
    have hl := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) l
    have hz := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) z
    simp only [liftCompCoins, Comp.size]; omega

def idKeyLitE {Γ : List (Ty ESig)} (ik : IdentityKey) :
    Expr EOps Γ CryptoVerification.E2E.Costed.IdKey :=
  e2ePureOp .idKeyOfPbytes (e2ePureOp (.pbytesLit 32 (toU8 ik.publicKey.bytes.toList)) .unit)

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
@[simp] theorem eval_idKeyLitE {Γ : List (Ty ESig)} (ik : IdentityKey) (ρ : Env Γ) :
    (idKeyLitE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) ik).eval ρ = ik := by
  rcases ik with ⟨⟨v⟩⟩
  simp only [idKeyLitE, eval_e2ePureOp, E2EPureOp.eval, u8Vec_toU8_vec]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem cost_idKeyLitE {Γ : List (Ty ESig)} (ik : IdentityKey) :
    (idKeyLitE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) (Γ := Γ) ik).cost ≤ 100 := by
  have h32 : ((32 : ℕ+) : ℕ) = 32 := rfl
  have hlen : (toU8 ik.publicKey.bytes.toList).length = 32 := by simp [toU8]
  simp only [idKeyLitE, cost_e2ePureOp, E2EPureOp.cost, Expr.cost, h32, hlen]
  omega

def idKeyPairLitE {Γ : List (Ty ESig)} (idA idB : IdentityKey) :
    Expr EOps Γ (.prod CryptoVerification.E2E.Costed.IdKey CryptoVerification.E2E.Costed.IdKey) :=
  .pair (idKeyLitE idA) (idKeyLitE idB)

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
@[simp] theorem eval_idKeyPairLitE {Γ : List (Ty ESig)} (idA idB : IdentityKey) (ρ : Env Γ) :
    (idKeyPairLitE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB).eval ρ =
      (idA, idB) := by
  simp [idKeyPairLitE, Expr.eval]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem cost_idKeyPairLitE {Γ : List (Ty ESig)} (idA idB : IdentityKey) :
    (idKeyPairLitE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
      (Γ := Γ) idA idB).cost ≤ 201 := by
  have ha := cost_idKeyLitE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) (Γ := Γ) idA
  have hb := cost_idKeyLitE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) (Γ := Γ) idB
  simp only [idKeyPairLitE, Expr.cost]
  omega

/-- Samples `(b, k0, spk, ac, pqr)` and builds the encoded initial `SM.GameState` of
`libsignalSessionSchemeFromEpoch0Keys`. -/
def initEpoch0GsE2EC (idA idB : IdentityKey) :
    Comp EOps (coinE2EIface (coinOnlyIface ℓ Pt))
      [.prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256]
      (.prod .unit (e2eGsTy ℓ)) :=
  .bind (Comp.sample (I := coinE2EIface (coinOnlyIface ℓ Pt)) UniformSamplerTag.bool .unit)
    (.bind (Comp.sample (I := coinE2EIface (coinOnlyIface ℓ Pt)) (UniformSamplerTag.base .bv256) .unit)
      (.bind (Comp.sample (I := coinE2EIface (coinOnlyIface ℓ Pt)) (UniformSamplerTag.base .bv256) .unit)
        (.bind (Comp.sample (I := coinE2EIface (coinOnlyIface ℓ Pt)) (UniformSamplerTag.base .bv256) .unit)
          (.bind (Comp.sample (I := coinE2EIface (coinOnlyIface ℓ Pt)) (UniformSamplerTag.base .bv256) .unit)
            (.ret (.pair .unit
              (initFixedSpkGsE (idKeyPairLitE idA idB)
                (.pair (.var (.succ (.succ .zero)))
                  (.pair
                    (.pair (.var (.succ (.succ (.succ (.succ (.succ .zero))))))
                      (.pair (.var (.succ .zero)) (.var .zero)))
                    (.var (.succ (.succ (.succ (.succ .zero))))))))))))))

def initEpoch0GsC (idA idB : IdentityKey) :
    Comp AOps (coinOnlyIface ℓ Pt)
      [.prod BV256 BV256]
      (.prod .unit (liftTy (Pt := Pt) (e2eGsTy ℓ))) :=
  liftCompCoins (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) rfl
    (initEpoch0GsE2EC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT) idA idB)

theorem initEpoch0GsC_queries_zero (idA idB : IdentityKey) (w : Empty → ℕ) :
    (initEpoch0GsC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB).queries
      w (fun _ => 0) = 0 :=
  liftCompCoins_queries_zero (I' := coinOnlyIface ℓ Pt) rfl _ w

theorem initEpoch0GsC_cost (idA idB : IdentityKey) :
    (initEpoch0GsC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB).cost ≤ 32 * 94200 := by
  have h1 := liftCompCoins_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl
    (initEpoch0GsE2EC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT) idA idB)
  let Γ5 : List (Ty ESig) :=
    [Ty.base CryptoVerification.E2E.Costed.E2EUnifBase.bv256.sort,
     Ty.base CryptoVerification.E2E.Costed.E2EUnifBase.bv256.sort,
     Ty.base CryptoVerification.E2E.Costed.E2EUnifBase.bv256.sort,
     Ty.base CryptoVerification.E2E.Costed.E2EUnifBase.bv256.sort,
     .bool,
     .prod CryptoVerification.E2E.Costed.BV256 CryptoVerification.E2E.Costed.BV256]
  have hids := cost_idKeyPairLitE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
    (Γ := Γ5) idA idB
  have hgs := cost_initFixedSpkGsE (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Γ5)
    (idKeyPairLitE idA idB)
    (.pair (.var (.succ (.succ .zero)))
      (.pair
        (.pair (.var (.succ (.succ (.succ (.succ (.succ .zero))))))
          (.pair (.var (.succ .zero)) (.var .zero)))
        (.var (.succ (.succ (.succ (.succ .zero)))))))
  dsimp only [initEpoch0GsC, initEpoch0GsE2EC] at h1 ⊢
  simp only [Comp.cost, Expr.cost, coinE2EIface, CryptoVerification.E2E.Costed.e2eSamplers,
    ReductionDsl.unifSamplers, CryptoVerification.E2E.Costed.E2EUnifBase.cost] at hgs h1 ⊢
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem size_e2ePureOp {Γ : List (Ty ESig)} (o : E2EPureOp)
    (e : Expr EOps Γ (o.dom ℓ)) :
    (e2ePureOp (P := zeroPqxdhPrims) (C := C) (K := K) (decT := decT) (encT := encT) o e).size =
      e.size + o.opSize + 1 := rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem size_e2eCryptoOp {Γ : List (Ty ESig)} (c : E2ECryptoOp)
    (e : Expr EOps Γ (c.dom ℓ)) :
    (e2eCryptoOp (P := zeroPqxdhPrims) (C := C) (K := K) (decT := decT) (encT := encT) c e).size =
      e.size + 1 := rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
@[simp] theorem size_idKeyLitE {Γ : List (Ty ESig)} (ik : IdentityKey) :
    (idKeyLitE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) (Γ := Γ) ik).size = 35 := by
  have hlen : (toU8 ik.publicKey.bytes.toList).length = 32 := by simp [toU8]
  simp only [idKeyLitE, size_e2ePureOp, E2EPureOp.opSize, Expr.size, hlen]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
@[simp] theorem size_idKeyPairLitE {Γ : List (Ty ESig)} (idA idB : IdentityKey) :
    (idKeyPairLitE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT)
      (Γ := Γ) idA idB).size = 71 := by
  simp only [idKeyPairLitE, Expr.size, size_idKeyLitE]

theorem initEpoch0GsC_size_le (idA idB : IdentityKey) :
    (initEpoch0GsC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB).size ≤ 5000 := by
  have h1 := liftCompCoins_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl
    (initEpoch0GsE2EC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT) idA idB)
  have h2 : (initEpoch0GsE2EC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
      (decT := decT) (encT := encT) idA idB).size ≤ 550 := by
    simp only [initEpoch0GsE2EC, initFixedSpkGsE, initFixedSpkAliceE, initFixedSpkBobE,
      eLet, eCaseOpt, v, size_e2ePureOp, size_e2eCryptoOp, E2EPureOp.opSize,
      size_idKeyPairLitE, Comp.size, Expr.size, show bits 0 = 1 from rfl]
    omega
  dsimp only [initEpoch0GsC]
  omega

def epoch0InitImpl (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (ℓ : ℕ)
    (rc : RootKey × BitVec 256) :
    ProbComp (Unit × GameState (GhostState Bytes) (Plain ℓ) Bytes) := do
  let b ← ($ᵗ Bool : ProbComp Bool)
  let k ← ($ᵗ (RootKey × BitVec 256 × BitVec 256 × BitVec 256) : ProbComp _)
  return ((), initState
    (libsignalSessionSchemeFromEpoch0Keys (paramsV1 C K idA idB) ℓ rc.1 rc.2).sendPart k b)

theorem initEpoch0GsC_eval (idA idB : IdentityKey) (rc : RootKey × BitVec 256) :
    (initEpoch0GsC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB).eval (.cons rc .nil) =
      Prod.map id (fun st => liftVal (Pt := Pt) (e2eGsEnc st)) <$>
        epoch0InitImpl C K idA idB ℓ rc := by
  have hev := liftCompCoins_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl
    (initEpoch0GsE2EC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT) idA idB)
    (.cons rc .nil)
  change (initEpoch0GsC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB).eval (.cons rc .nil) =
    liftVal (Pt := Pt) <$>
      (initEpoch0GsE2EC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT)
        idA idB).eval (.cons rc .nil) at hev
  rw [hev]
  have hlift : ∀ {α : Type} (p : ProbComp α),
      (coinE2EIface (coinOnlyIface ℓ Pt)).liftP p = p :=
    fun p => liftP_unif_eq_self _ (fun _ => rfl) p
  unfold initEpoch0GsE2EC epoch0InitImpl
  simp only [Comp.eval, hlift, CryptoVerification.E2E.Costed.e2eSamplers,
    ReductionDsl.unifSamplers, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  refine bind_congr fun b => ?_
  rw [sample_prod_bindU]
  refine bind_congr fun k0 => ?_
  rw [sample_prod_bindU]
  refine bind_congr fun spk => ?_
  rw [sample_prod_bindU]
  refine bind_congr fun ac => ?_
  refine bind_congr fun pqr => ?_
  have hgs := eval_initFixedSpkGsE (ℓ := ℓ) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT)
    (idKeyPairLitE idA idB)
    (.pair (.var (.succ (.succ .zero)))
      (.pair
        (.pair (.var (.succ (.succ (.succ (.succ (.succ .zero))))))
          (.pair (.var (.succ .zero)) (.var .zero)))
        (.var (.succ (.succ (.succ (.succ .zero)))))))
    (.cons pqr (.cons ac (.cons spk (.cons k0 (.cons b (.cons rc .nil))))))
  simp only [Expr.eval, eval_idKeyPairLitE] at hgs
  exact congrArg (fun x => pure ((), liftVal (Pt := Pt) x)) hgs

theorem smReachBounded_epoch0InitImpl (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (ℓ : ℕ)
    (rc : RootKey × BitVec 256)
    {r : Unit × GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (hr : r ∈ support (epoch0InitImpl C K idA idB ℓ rc)) :
    SmReachBounded C K 0 r.2 := by
  unfold epoch0InitImpl at hr
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨b, -, ⟨k0, ⟨spk, ac, pqr⟩⟩, -, rfl⟩ := hr
  exact smReachBounded_initState C K idA idB ℓ spk ((rc.1, rc.2), (ac, pqr)) b

theorem oracleImplR_epoch0Keys_eq_fixedSpk (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (ℓ Δ qep : ℕ) (rc : RootKey × BitVec 256) (spk : BitVec 256)
    (cfg : CryptoGames.SM.ConfigR (GhostState Bytes) (Plain ℓ) Bytes) :
    oracleImplR (libsignalSessionSchemeFromEpoch0Keys (paramsV1 C K idA idB) ℓ rc.1 rc.2) Δ qep cfg =
      oracleImplR
        (sessionSchemeFixedSpk
          (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spk)
        Δ qep cfg := by
  rfl

end Epoch0Init

/-! ## Step-cost budget and fallback reductions -/

theorem bits_le_succ (n : ℕ) : bits n ≤ n + 1 := by
  dsimp only [bits]
  exact Nat.succ_le_succ (Nat.log_le_self 2 n)

theorem bits_succ_le (n : ℕ) : bits (n + 1) ≤ bits n + 1 :=
  bits_le_of_lt (by have h := lt_two_pow_bits n; rw [pow_succ]; omega) (by omega)

def ratchetCostBudgetTight (q qep : ℕ) : ℕ :=
  2 ^ 12 * (q + 1) ^ 2 * (maxForwardJumps + bits qep)

theorem ratchetCostBudgetTight_le_ratchetCostBudget (q qep : ℕ) :
    ratchetCostBudgetTight q qep ≤ ratchetCostBudget q qep :=
  le_rfl

theorem session_cost_le_ratchetCostBudgetTight (q qep cInit cFin cStepBase cStepQ cStepQep : ℕ)
    (hInit : cInit ≤ 50000000)
    (hFin : cFin ≤ 50000000 + 2048 * q)
    (hBase : cStepBase ≤ 200000000)
    (hQ : cStepQ ≤ 100000000)
    (hQep : cStepQep ≤ 4096) :
    cInit + q * (cStepBase + cStepQ * q + cStepQep * bits qep) + cFin ≤
      ratchetCostBudgetTight q qep := by
  unfold ratchetCostBudgetTight maxForwardJumps
  have h12 : (2 : ℕ) ^ 12 = 4096 := by decide
  rw [h12]
  have h1 : q * cStepBase ≤ q * 200000000 := Nat.mul_le_mul_left q hBase
  have h2 : q * (cStepQ * q) ≤ q * (100000000 * q) :=
    Nat.mul_le_mul_left q (Nat.mul_le_mul_right q hQ)
  have h3 : q * (cStepQep * bits qep) ≤ q * (4096 * bits qep) :=
    Nat.mul_le_mul_left q (Nat.mul_le_mul_right (bits qep) hQep)
  have hlhs : q * (cStepBase + cStepQ * q + cStepQep * bits qep) =
      q * cStepBase + q * (cStepQ * q) + q * (cStepQep * bits qep) := by ring
  have hrhs : 4096 * (q + 1) ^ 2 * (25000 + bits qep) =
      102400000 + 204800000 * q + 102400000 * (q * q) +
        4096 * bits qep + 8192 * (q * bits qep) + 4096 * (q * q * bits qep) := by ring
  have hm2 : q * (100000000 * q) = 100000000 * (q * q) := by ring
  have hm3 : q * (4096 * bits qep) = 4096 * (q * bits qep) := by ring
  rw [hlhs, hrhs]
  rw [hm2] at h2
  rw [hm3] at h3
  omega

theorem session_cost_le_ratchetCostBudget (q qep cInit cFin cStepBase cStepQ cStepQep : ℕ)
    (hInit : cInit ≤ 50000000)
    (hFin : cFin ≤ 50000000 + 2048 * q)
    (hBase : cStepBase ≤ 200000000)
    (hQ : cStepQ ≤ 100000000)
    (hQep : cStepQep ≤ 4096) :
    cInit + q * (cStepBase + cStepQ * q + cStepQep * bits qep) + cFin ≤
      ratchetCostBudget q qep :=
  (session_cost_le_ratchetCostBudgetTight q qep cInit cFin cStepBase cStepQ cStepQep
    hInit hFin hBase hQ hQep).trans (ratchetCostBudgetTight_le_ratchetCostBudget q qep)

theorem session_cost_cubic_le_ratchetCostBudgetTight
    (q qep cInit cFin cStepBase cStepQ cStepQ2 cStepQep : ℕ)
    (hInit : cInit ≤ 50000000)
    (hFin : cFin ≤ 50000000 + 2048 * q)
    (hBase : cStepBase ≤ 200000000)
    (hQ : cStepQ ≤ 100000000)
    (hQ2 : cStepQ2 = 0)
    (hQep : cStepQep ≤ 4096) :
    cInit + q * (cStepBase + cStepQ * q + cStepQ2 * (q * q) + cStepQep * bits qep) + cFin ≤
      ratchetCostBudgetTight q qep := by
  subst hQ2
  simpa using session_cost_le_ratchetCostBudgetTight q qep cInit cFin cStepBase cStepQ cStepQep
    hInit hFin hBase hQ hQep

theorem session_cost_cubic_le_ratchetCostBudget
    (q qep cInit cFin cStepBase cStepQ cStepQ2 cStepQep : ℕ)
    (hInit : cInit ≤ 50000000)
    (hFin : cFin ≤ 50000000 + 2048 * q)
    (hBase : cStepBase ≤ 200000000)
    (hQ : cStepQ ≤ 100000000)
    (hQ2 : cStepQ2 = 0)
    (hQep : cStepQep ≤ 4096) :
    cInit + q * (cStepBase + cStepQ * q + cStepQ2 * (q * q) + cStepQep * bits qep) + cFin ≤
      ratchetCostBudget q qep :=
  (session_cost_cubic_le_ratchetCostBudgetTight q qep cInit cFin cStepBase cStepQ cStepQ2 cStepQep
    hInit hFin hBase hQ hQ2 hQep).trans (ratchetCostBudgetTight_le_ratchetCostBudget q qep)

def dummyBoolSessionRed {ℓ : ℕ} {Pt : Type}
    {O : Ops (atomicSig ℓ Pt)} {ι : Type} {T : OracleSpec ι}
    (I : Iface (atomicSig ℓ Pt) T) (rIn : Ty (atomicSig ℓ Pt)) :
    CostedReduction O I
      (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (e2eSessionCodec ℓ Pt) rIn .unit .bool .bool where
  σ := .unit
  init := .ret (.pair .unit .unit)
  handle := .ret (.pair (.pair .none (.pair .none .none)) .unit)
  finish := .ret (.bool false)

theorem dummyBoolSessionRed_totalQueries {ℓ : ℕ} {Pt : Type}
    {O : Ops (atomicSig ℓ Pt)} {ι : Type} {T : OracleSpec ι}
    (I : Iface (atomicSig ℓ Pt) T) (rIn : Ty (atomicSig ℓ Pt))
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) (q : ℕ) :
    (dummyBoolSessionRed (O := O) I rIn).totalQueries w ws q = 0 := by
  simp [dummyBoolSessionRed, CostedReduction.totalQueries, Comp.queries]

theorem dummyBoolSessionRed_totalCost_le {ℓ : ℕ} {Pt : Type}
    {O : Ops (atomicSig ℓ Pt)} {ι : Type} {T : OracleSpec ι}
    (I : Iface (atomicSig ℓ Pt) T) (hU : I.uCost = 1) (rIn : Ty (atomicSig ℓ Pt)) (q qep : ℕ) :
    (dummyBoolSessionRed (O := O) I rIn).totalCost q ≤ ratchetCostBudget q qep := by
  have hcost : (dummyBoolSessionRed (O := O) I rIn).totalCost q = 6 + q * 24 := by
    simp [dummyBoolSessionRed, CostedReduction.totalCost, e2eSessionCodec, hU, Comp.cost, Expr.cost]
    omega
  rw [hcost]
  simpa using session_cost_le_ratchetCostBudget q qep 6 0 24 0 0
    (by omega) (by omega) (by omega) (by omega) (by omega)

def dummyPairSessionRed {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {C : Crypto} {K : MlKem}
    {Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {ι : Type} {T : OracleSpec ι}
    (I : Iface (atomicSig ℓ Pt) T) (rIn : Ty (atomicSig ℓ Pt)) :
    CostedReduction (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) I
      (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (e2eSessionCodec ℓ Pt) rIn .unit .bool (.prod BV512 BV256) where
  σ := .unit
  init := .ret (.pair .unit .unit)
  handle := .ret (.pair (.pair .none (.pair .none .none)) .unit)
  finish := .ret (.pair (sessPureOp (.bv512Lit 0) .unit) (sessPureOp (.bv256Lit 0) .unit))

theorem dummyPairSessionRed_totalQueries {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {C : Crypto} {K : MlKem}
    {Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {ι : Type} {T : OracleSpec ι}
    (I : Iface (atomicSig ℓ Pt) T) (rIn : Ty (atomicSig ℓ Pt))
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) (q : ℕ) :
    (dummyPairSessionRed (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) I rIn).totalQueries w ws q = 0 := by
  simp [dummyPairSessionRed, CostedReduction.totalQueries, Comp.queries]

theorem dummyPairSessionRed_totalCost_le {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {C : Crypto} {K : MlKem}
    {Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {ι : Type} {T : OracleSpec ι}
    (I : Iface (atomicSig ℓ Pt) T) (hU : I.uCost = 1) (rIn : Ty (atomicSig ℓ Pt)) (q qep : ℕ) :
    (dummyPairSessionRed (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) I rIn).totalCost q ≤
      ratchetCostBudget q qep := by
  have hb :
      (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam).cost
        (Sum.inl (Sum.inl (Sum.inl (Sum.inl (ReductionDsl.AtomicPureOp.bv512Lit 0#512))))) = 3 :=
    rfl
  have hc :
      (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam).cost
        (Sum.inl (Sum.inl (Sum.inl (Sum.inl (ReductionDsl.AtomicPureOp.bv256Lit 0#256))))) = 2 :=
    rfl
  have hcost : (dummyPairSessionRed (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) I rIn).totalCost q ≤ 32 + q * 24 := by
    simp [dummyPairSessionRed, CostedReduction.totalCost, e2eSessionCodec, hU, Comp.cost,
      Expr.cost, hb, hc]
    omega
  refine hcost.trans ?_
  simpa using session_cost_le_ratchetCostBudget q qep 32 0 24 0 0
    (by omega) (by omega) (by omega) (by omega) (by omega)

@[simp] theorem renExpr_size {S0 : Sig} {O0 : Ops S0} {Γ₁ Γ₂ : List (Ty S0)} {t : Ty S0}
    (f : ∀ {u}, Var Γ₁ u → Var Γ₂ u) (e : Expr O0 Γ₁ t) :
    (renExpr f e).size = e.size := by
  induction e generalizing Γ₂ <;> simp [renExpr, Expr.size, *]

@[simp] theorem renComp_size {S0 : Sig} {O0 : Ops S0} {ι : Type} {T : OracleSpec ι}
    {I0 : Iface S0 T} {Γ₁ Γ₂ : List (Ty S0)} {t : Ty S0}
    (f : ∀ {u}, Var Γ₁ u → Var Γ₂ u) (c : Comp O0 I0 Γ₁ t) :
    (renComp f c).size = c.size := by
  induction c generalizing Γ₂ <;> simp [renComp, Comp.size, renExpr_size, *]

@[simp] theorem wk1Expr_size {S0 : Sig} {O0 : Ops S0} {a b : Ty S0} {Γ : List (Ty S0)}
    (e : Expr O0 [a] b) :
    (wk1Expr (Γ := Γ) e).size = e.size :=
  renExpr_size _ e

@[simp] theorem wk1Comp_size {S0 : Sig} {O0 : Ops S0} {ι : Type} {T : OracleSpec ι}
    {I0 : Iface S0 T} {a b : Ty S0} {Γ : List (Ty S0)} (c : Comp O0 I0 [a] b) :
    (wk1Comp (Γ := Γ) c).size = c.size :=
  renComp_size _ c

@[simp] theorem dummyBoolSessionRed_size {ℓ : ℕ} {Pt : Type}
    {O : Ops (atomicSig ℓ Pt)} {ι : Type} {T : OracleSpec ι}
    (I : Iface (atomicSig ℓ Pt) T) (rIn : Ty (atomicSig ℓ Pt)) :
    (dummyBoolSessionRed (O := O) I rIn).size = 14 :=
  rfl

theorem dummyBoolSessionRed_size_le {ℓ : ℕ} {Pt : Type}
    {O : Ops (atomicSig ℓ Pt)} {ι : Type} {T : OracleSpec ι}
    (I : Iface (atomicSig ℓ Pt) T) (rIn : Ty (atomicSig ℓ Pt)) :
    (dummyBoolSessionRed (O := O) I rIn).size ≤ reductionSizeBudget := by
  rw [dummyBoolSessionRed_size]
  decide

@[simp] theorem dummyPairSessionRed_size {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {C : Crypto} {K : MlKem}
    {Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {ι : Type} {T : OracleSpec ι}
    (I : Iface (atomicSig ℓ Pt) T) (rIn : Ty (atomicSig ℓ Pt)) :
    (dummyPairSessionRed (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) I rIn).size = 114 :=
  rfl

theorem dummyPairSessionRed_size_le {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {C : Crypto} {K : MlKem}
    {Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {ι : Type} {T : OracleSpec ι}
    (I : Iface (atomicSig ℓ Pt) T) (rIn : Ty (atomicSig ℓ Pt)) :
    (dummyPairSessionRed (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) I rIn).size ≤ reductionSizeBudget := by
  rw [dummyPairSessionRed_size]
  decide

end Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon
