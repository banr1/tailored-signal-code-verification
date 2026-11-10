/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.SM.DeliverForge
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperDefs
import Computational.Proofs.ReductionDsl.Bridge
import Computational.Proofs.ReductionDsl.Notation

/-!
# Costed Challenge Simulators for `DeliverForgePaper`

Defines the `CostedReduction` programs `challSimDFPaperProg` and coin-stripping
`challSimDF'PaperProg` for `SM.specDF` under `corrAllowedPaper`, with evaluation agreement, query,
and cost bounds.
-/

@[expose] public section

open ReductionDsl OracleSpec OracleComp
open scoped Computational.Proofs.ReductionDsl.Notation

namespace CryptoGames.SM

open CryptoGames.SM.Construction

local macro_rules
  | `(rdsl_pat| .transmit $p:term)     => `(rdsl_pat| .inl (.inl (.inl (.inl (.inl $p)))))
  | `(rdsl_pat| .challenge $p:term)    => `(rdsl_pat| .inl (.inl (.inl (.inl (.inr $p)))))
  | `(rdsl_pat| .deliver $p:term)      => `(rdsl_pat| .inl (.inl (.inl (.inr $p))))
  | `(rdsl_pat| .inject $p:term)       => `(rdsl_pat| .inl (.inl (.inr $p)))
  | `(rdsl_pat| .corrupt $p:term)      => `(rdsl_pat| .inl (.inr $p))
  | `(rdsl_pat| .deliverForge $p:term) => `(rdsl_pat| .inr $p)

section ChallSimDFPaperProg

variable {Key St St₂ Msg Coins RCoins C : Type}
  {init : Party → Key → Option St}
  {send : St → Msg → Coins → Option (St × C)}
  {receive : St → C → RCoins → Option (St × ℕ × ℕ × Msg)}
  {eqMsg : Msg → Msg → Bool}
  {eqCt : C → C → Bool}
  {blank : Msg → Msg}
  {injOK : C → Bool}
  {stOK : Party → St → Bool}
  {φ : St → Option St₂}
  {stSort : SMSort}
  {sampKey : ProbComp (Option Key)}
  {sampCoins : ProbComp (Option Coins)}
  {sampRCoins : ProbComp (Option RCoins)}

local notation "S" => smSig Key St St₂ Msg Coins RCoins C
local notation "OO" => smOps init send receive eqMsg eqCt blank injOK stOK φ
local notation "SIfaceDF" =>
  smIfaceDF Key St St₂ Msg Coins RCoins C stSort sampKey sampCoins sampRCoins
local notation "SCodecDF" => smCodecDF Key St St₂ Msg Coins RCoins C stSort
local notation "SQ" => smQ Key St St₂ Msg Coins RCoins C
local notation "SR" => smR Key St St₂ Msg Coins RCoins C stSort
local notation "SQDF" => smQDF Key St St₂ Msg Coins RCoins C
local notation "SRDF" => smRDF Key St St₂ Msg Coins RCoins C stSort

def mCorrAllowedPaperE
    {O' : Ops S} {Γ} (K : ℕ) (s : Expr O' Γ mirrorTy) (p : Expr O' Γ .bool) :
    Expr O' Γ .bool :=
  rdslExpr =>
    letE (s, p) fun (s0, p0) =>
      !(anyB K (mChall s0) fun pos => boolEq (posSender pos) (otherE p0))

theorem mCorrAllowedPaperE_eval {O' : Ops S} {Γ} (K : ℕ) (s : Expr O' Γ mirrorTy)
    (p : Expr O' Γ .bool) (ρ : Env Γ) (st : Thm1.Mirror Msg C) (P : Party)
    (hChall : st.chall.length ≤ K)
    (hs : s.eval ρ = mirrorEnc st) (hp : p.eval ρ = partyEnc P) :
    (mCorrAllowedPaperE (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins) K s p).eval ρ =
      st.corrAllowedPaper P := by
  unfold mCorrAllowedPaperE GameState.corrAllowedPaper
  rw [letE_eval]
  have h0 : (Expr.pair s p).eval ρ =
      (mirrorEnc (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins) st, partyEnc P) := by
    simp [Expr.eval, hs, hp]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod mirrorTy .bool)
    (mirrorEnc (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins) st, partyEnc P) ρ
  have htCh : (st.chall.map posEnc).take K = st.chall.map posEnc :=
    List.take_of_length_le (by simpa using hChall)
  have hCh0 : (mChall (.fst (Expr.v0 (O := O')))).eval ρ₁ = st.chall.map posEnc := rfl
  simp only [Expr.eval, hCh0, htCh]
  congr 1
  rw [any_map_eq]
  congr 1; funext pos
  simp [ρ₁, posSender, otherE, posEnc, ← partyEnc_other, partyEnc_beq, Expr.eval, Expr.v0, Expr.v1]

def simCorrCDFPaper (K : ℕ) {Γ}
    (s : Expr OO Γ mirrorTy)
    (p : Expr OO Γ .bool) :
    Comp OO SIfaceDF Γ (.prod (.opt (.base stSort)) mirrorTy) :=
  rdsl do
    (s0, p0) ← return (s, p)
    if !(mCorrAllowedPaperE K s0 p0) then
      return (none, s0)
    else
      res ← query (I := SIfaceDF) SMTagDF.cr p0
      if isSomeE res then
        return (res, mAfterCorrE K s0 p0)
      else
        return (res, s0)

def simHandleCDFPaper (K Δ qep : ℕ) :
    Comp OO SIfaceDF [mirrorTy, SQDF] (.prod SRDF mirrorTy) :=
  rdsl [s, q] do
    match q with
    | .transmit arg =>
      (r, s') ← simTransmitCDF Δ qep s arg
      return (.inl (.inl (.inl (.inl (.inl r)))), s')
    | .challenge arg =>
      (r, s') ← simChallCDF Δ qep s arg
      return (.inl (.inl (.inl (.inl (.inr r)))), s')
    | .deliver arg =>
      (r, s') ← simDeliverCDF K s arg
      return (.inl (.inl (.inl (.inr r))), s')
    | .inject arg =>
      (r, s') ← simInjectCDF K s arg
      return (.inl (.inl (.inr r)), s')
    | .corrupt arg =>
      (r, s') ← simCorrCDFPaper K s arg
      return (.inl (.inr r), s')
    | .deliverForge arg =>
      (r, s') ← simDeliverForgeCDF K s arg
      return (.inr r, s')

/-- Costed `DeliverForge.challSimDFPaper` challenge simulator over `SM.specDF`. -/
@[reducible] def challSimDFPaperProg (K Δ qep : ℕ) :
    CostedReduction OO SIfaceDF
      (SM.specDF (SMSort.den Key St St₂ Msg Coins RCoins C stSort) Msg Coins C)
      SCodecDF .unit .unit .bool .bool where
  σ := mirrorTy
  init := simInitCDF
  handle := simHandleCDFPaper K Δ qep
  finish := rdsl [_, guess] do return guess

@[simp] theorem simImplDFPaper_inl [DecidableEq C] (Δ qep : ℕ) (n : ℕ) :
    DeliverForge.simImplDFPaper (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
      (Msg := Msg) (Coins := Coins) (C := C) Δ qep (.inl n) =
      StateT.lift (query (spec := unifSpec +
        SM.specDF (SMSort.den Key St St₂ Msg Coins RCoins C stSort) Msg Coins C) (.inl n)) := rfl

@[simp] theorem simImplDFPaper_tr [DecidableEq C] (Δ qep : ℕ) (q : Party × Msg × Option Coins) :
    DeliverForge.simImplDFPaper (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
      (Msg := Msg) (Coins := Coins) (C := C) Δ qep
      (.inr (.inl (.inl (.inl (.inl (.inl q)))))) =
      DeliverForge.simTransmitDF Δ qep q := rfl

@[simp] theorem simImplDFPaper_ch [DecidableEq C] (Δ qep : ℕ)
    (q : Party × Msg × Msg × Option Coins) :
    DeliverForge.simImplDFPaper (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
      (Msg := Msg) (Coins := Coins) (C := C) Δ qep
      (.inr (.inl (.inl (.inl (.inl (.inr q)))))) =
      DeliverForge.simChallDF Δ qep q := rfl

@[simp] theorem simImplDFPaper_dl [DecidableEq C] (Δ qep : ℕ) (q : Party × C) :
    DeliverForge.simImplDFPaper (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
      (Msg := Msg) (Coins := Coins) (C := C) Δ qep
      (.inr (.inl (.inl (.inl (.inr q))))) =
      DeliverForge.simDeliverDF q := rfl

@[simp] theorem simImplDFPaper_ij [DecidableEq C] (Δ qep : ℕ) (q : Party × C) :
    DeliverForge.simImplDFPaper (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
      (Msg := Msg) (Coins := Coins) (C := C) Δ qep
      (.inr (.inl (.inl (.inr q)))) =
      DeliverForge.simInjectDF q := rfl

@[simp] theorem simImplDFPaper_cr [DecidableEq C] (Δ qep : ℕ) (P : Party) :
    DeliverForge.simImplDFPaper (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
      (Msg := Msg) (Coins := Coins) (C := C) Δ qep
      (.inr (.inl (.inr P))) =
      DeliverForge.simCorrDFPaper P := rfl

@[simp] theorem simImplDFPaper_df [DecidableEq C] (Δ qep : ℕ) (q : Party × C × C) :
    DeliverForge.simImplDFPaper (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
      (Msg := Msg) (Coins := Coins) (C := C) Δ qep
      (.inr (.inr q)) =
      DeliverForge.simDeliverForgeDF q := rfl

theorem simCorrCDFPaper_eval (K : ℕ) {Γ}
    (s : Expr OO Γ mirrorTy) (p : Expr OO Γ .bool)
    (ρ : Env Γ) (st : Thm1.Mirror Msg C) (P : Party)
    (hTrans : st.trans.length ≤ K) (hChall : st.chall.length ≤ K)
    (hs : s.eval ρ = mirrorEnc st) (hp : p.eval ρ = partyEnc P) :
    (simCorrCDFPaper (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
      (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
      K s p).eval ρ =
      Prod.map id mirrorEnc <$>
        ((DeliverForge.simCorrDFPaper (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          (Msg := Msg) (Coins := Coins) (C := C) P).run st) := by
  unfold simCorrCDFPaper DeliverForge.simCorrDFPaper
  rw [Comp.eval_bind_ret]
  have h0 : (Expr.pair s p).eval ρ = (mirrorEnc st, partyEnc P) := by
    simp [Expr.eval, hs, hp]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := (.prod mirrorTy .bool : Ty S)) (mirrorEnc st, partyEnc P) ρ
  rw [Comp.eval_ite]
  have hAllow : (Expr.not (mCorrAllowedPaperE K (.fst (Expr.v0 (O := OO))) (.snd .v0))).eval ρ₁ =
      !(st.corrAllowedPaper P) := by
    simp only [Expr.eval]
    rw [mCorrAllowedPaperE_eval K (.fst .v0) (.snd .v0) ρ₁ st P hChall rfl rfl]
  rw [hAllow]
  cases hca : st.corrAllowedPaper P
  · simp [ρ₁, hca, Comp.eval, Expr.eval, Expr.v0, StateT.run_bind, StateT.run_get]
  · simp only [hca, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
      pure_bind]
    have hcr : (Comp.query (I := SIfaceDF) SMTagDF.cr (.snd (Expr.v0 (O := OO)))).eval ρ₁ =
        DeliverForge.corrQueryDF (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          (Msg := Msg) (Coins := Coins) (C := C) P := by
      rw [query_crDF_eval]
      simp [ρ₁, partyDec_partyEnc, Expr.eval, Expr.v0]
    simp only [Comp.eval_bind, hcr, stateT_lift_run, bind_assoc, pure_bind, map_bind]
    refine bind_congr fun res => ?_
    rcases res with _ | stP
    · simp [ρ₁, Comp.eval, isSomeE, Expr.eval, Expr.v0, Expr.v1, StateT.run_pure]
    · simp only [Comp.eval_ite, isSomeE_eval, Expr.eval, Expr.v0, Env.get_cons_zero,
        Option.isSome_some, ↓reduceIte, Comp.eval_ret, StateT.run_bind, StateT.run_set,
        StateT.run_pure, pure_bind, map_pure, Prod.map]
      congr 2
      exact mAfterCorrE_eval K (.fst (Expr.v1 (O := OO))) (.snd .v1)
        (Env.cons (t := (.opt (.base stSort) : Ty S)) (some stP) ρ₁) st P hTrans rfl rfl

theorem handlerImpl_simHandleCDFPaper_cr (K Δ qep : ℕ)
    (st : Thm1.Mirror Msg C) (P : Party)
    (hTrans : st.trans.length ≤ K) (hChall : st.chall.length ≤ K) :
    ((handlerImpl (C := SCodecDF)
      (simHandleCDFPaper (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
        (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
        (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
        (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
        K Δ qep)
      (.inr (.inl (.inr P)))).run (mirrorEnc st)) =
      Prod.map id mirrorEnc <$>
        ((DeliverForge.simCorrDFPaper (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          (Msg := Msg) (Coins := Coins) (C := C) P).run st) := by
  unfold handlerImpl simHandleCDFPaper smCodecDF smCodec
  simp only [StateT.run_mk, Comp.eval, Expr.eval, Expr.v0, Expr.v1,
    Env.get_cons_zero, Env.get_cons_succ, bind_assoc, pure_bind]
  rw [simCorrCDFPaper_eval K .v2 (.var .zero) _ st P hTrans hChall rfl rfl]
  simp

theorem challSimDFPaperProg_impl_run_eq_of_ne_cr (K Δ qep : ℕ)
    (t : (SM.specDF (SMSort.den Key St St₂ Msg Coins RCoins C stSort) Msg Coins C).Domain)
    (hne : ∀ P, t ≠ .inl (.inr P))
    (v : (@mirrorTy Key St St₂ Msg Coins RCoins C).denote) :
    (((challSimDFPaperProg (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
      (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
      K Δ qep).impl (.inr t)).run v) =
    (((challSimDFProg (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
      (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
      K Δ qep).impl (.inr t)).run v) := by
  rcases t with (((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩)
  · unfold challSimDFPaperProg challSimDFProg CostedReduction.impl
      handlerImpl simHandleCDFPaper simHandleCDF smCodecDF smCodec
    simp only [StateT.run_mk, Comp.eval, Expr.eval, Expr.v0, Expr.v1,
      Env.get_cons_zero, Env.get_cons_succ]
  · unfold challSimDFPaperProg challSimDFProg CostedReduction.impl
      handlerImpl simHandleCDFPaper simHandleCDF smCodecDF smCodec
    simp only [StateT.run_mk, Comp.eval, Expr.eval, Expr.v0, Expr.v1,
      Env.get_cons_zero, Env.get_cons_succ]
  · unfold challSimDFPaperProg challSimDFProg CostedReduction.impl
      handlerImpl simHandleCDFPaper simHandleCDF smCodecDF smCodec
    simp only [StateT.run_mk, Comp.eval, Expr.eval, Expr.v0, Expr.v1,
      Env.get_cons_zero, Env.get_cons_succ]
  · unfold challSimDFPaperProg challSimDFProg CostedReduction.impl
      handlerImpl simHandleCDFPaper simHandleCDF smCodecDF smCodec
    simp only [StateT.run_mk, Comp.eval, Expr.eval, Expr.v0, Expr.v1,
      Env.get_cons_zero, Env.get_cons_succ]
  · exact absurd rfl (hne P)
  · unfold challSimDFPaperProg challSimDFProg CostedReduction.impl
      handlerImpl simHandleCDFPaper simHandleCDF smCodecDF
    simp only [StateT.run_mk, Comp.eval, Expr.eval, Expr.v0, Expr.v1,
      Env.get_cons_zero, Env.get_cons_succ]

@[simp] theorem mirrorClearComp_corrAllowedPaper (s : Thm1.Mirror Msg C) (P : Party) :
    (mirrorClearComp s).corrAllowedPaper P = s.corrAllowedPaper P := rfl

theorem simImplDFPaper_clearComp [DecidableEq C] (Δ qep : ℕ)
    (t : (SM.specDF (SMSort.den Key St St₂ Msg Coins RCoins C stSort) Msg Coins C).Domain)
    (st : Thm1.Mirror Msg C) :
    Prod.map id mirrorClearComp <$>
      ((DeliverForge.simImplDFPaper (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
        (Msg := Msg) (Coins := Coins) (C := C) Δ qep (.inr t)).run st) =
    Prod.map id mirrorClearComp <$>
      ((DeliverForge.simImplDFPaper (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
        (Msg := Msg) (Coins := Coins) (C := C) Δ qep (.inr t)).run (mirrorClearComp st)) := by
  rcases t with (((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩)
  · exact simImplDF_clearComp (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (stSort := stSort) Δ qep (.inl (.inl (.inl (.inl (.inl (P, m, r)))))) st
  · exact simImplDF_clearComp (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (stSort := stSort) Δ qep (.inl (.inl (.inl (.inl (.inr (P, m₀, m₁, r)))))) st
  · exact simImplDF_clearComp (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (stSort := stSort) Δ qep (.inl (.inl (.inl (.inr (P, c))))) st
  · exact simImplDF_clearComp (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (stSort := stSort) Δ qep (.inl (.inl (.inr (P, c)))) st
  · simp only [simImplDFPaper_cr, DeliverForge.simCorrDFPaper,
      StateT.run_bind, StateT.run_get, pure_bind, mirrorClearComp_corrAllowedPaper]
    by_cases hnot : !(st.corrAllowedPaper P)
    · simp [hnot, StateT.run_pure, Prod.map]
    · simp only [hnot, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, stateT_lift_run,
        bind_assoc, pure_bind, map_bind]
      refine bind_congr fun res => ?_
      rcases res with _ | stP <;>
      simp [StateT.run_pure, StateT.run_set, Prod.map]
  · exact simImplDF_clearComp (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (stSort := stSort) Δ qep (.inr (P, c, c')) st

theorem challSimDFPaperProg_step_clearComp [DecidableEq C] (K Δ qep m : ℕ)
    (heqCt : eqCt = (· == ·))
    (t : (SM.specDF (SMSort.den Key St St₂ Msg Coins RCoins C stSort) Msg Coins C).Domain)
    (v : (@mirrorTy Key St St₂ Msg Coins RCoins C).denote)
    (hInv : MirrorBoundInv K (m + 1) v) :
    (Prod.map id (mirrorClearComp ∘ mirrorDec) <$>
      (((challSimDFPaperProg (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
           (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
           (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
           (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
           K Δ qep).impl (.inr t)).run v)) =
      ((clearCompImpl (DeliverForge.simImplDFPaper
          (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          (Msg := Msg) (Coins := Coins) (C := C) Δ qep) (.inr t)).run
            (mirrorClearComp (mirrorDec v))) ∧
    ∀ r ∈ support (((challSimDFPaperProg (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
        (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
        (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
        (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
        K Δ qep).impl (.inr t)).run v), MirrorBoundInv K m r.2 := by
  rcases t with (((((⟨P, msg, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩)
  · rw [challSimDFPaperProg_impl_run_eq_of_ne_cr K Δ qep _ (by intro _ h; cases h) v]
    exact challSimDFProg_step_clearComp K Δ qep m heqCt
      (.inl (.inl (.inl (.inl (.inl (P, msg, r)))))) v hInv
  · rw [challSimDFPaperProg_impl_run_eq_of_ne_cr K Δ qep _ (by intro _ h; cases h) v]
    exact challSimDFProg_step_clearComp K Δ qep m heqCt
      (.inl (.inl (.inl (.inl (.inr (P, m₀, m₁, r)))))) v hInv
  · rw [challSimDFPaperProg_impl_run_eq_of_ne_cr K Δ qep _ (by intro _ h; cases h) v]
    exact challSimDFProg_step_clearComp K Δ qep m heqCt
      (.inl (.inl (.inl (.inr (P, c))))) v hInv
  · rw [challSimDFPaperProg_impl_run_eq_of_ne_cr K Δ qep _ (by intro _ h; cases h) v]
    exact challSimDFProg_step_clearComp K Δ qep m heqCt
      (.inl (.inl (.inr (P, c)))) v hInv
  · set st := mirrorDec v
    have hv : v = mirrorEnc st := (mirrorEnc_mirrorDec v).symm
    have hTrans : st.trans.length ≤ K := by
      have : st.trans.length + (m + 1) ≤ K := hInv.1; omega
    have hChall : st.chall.length ≤ K := by
      have : st.chall.length + (m + 1) ≤ K := hInv.2; omega
    have hInv0 : MirrorBoundInv (Key := Key) (St := St) (St₂ := St₂)
        (Coins := Coins) (RCoins := RCoins) K m (mirrorEnc st) := by
      rw [← hv]; exact hInv.mono (Nat.le_succ m)
    rw [hv, clearCompImpl, StateT.run_mk, ← simImplDFPaper_clearComp Δ qep (.inl (.inr P)) st]
    have hrun : (((challSimDFPaperProg (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
          (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
          (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
          (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
          K Δ qep).impl (.inr (.inl (.inr P)))).run (mirrorEnc st)) =
        Prod.map id mirrorEnc <$>
          ((DeliverForge.simCorrDFPaper (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
            (Msg := Msg) (Coins := Coins) (C := C) P).run st) :=
      handlerImpl_simHandleCDFPaper_cr K Δ qep st P hTrans hChall
    rw [hrun]
    refine ⟨by rw [Functor.map_map]; congr 1; funext ⟨a, s⟩; simp [Prod.map], ?_⟩
    intro x hx
    simp only [DeliverForge.simCorrDFPaper, StateT.run_bind, StateT.run_get, pure_bind] at hx
    by_cases hnot : !(st.corrAllowedPaper P)
    · simp only [hnot, ↓reduceIte, StateT.run_pure, map_pure, Prod.map, support_pure,
        Set.mem_singleton_iff] at hx
      subst hx; exact hInv0
    · simp only [hnot, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, stateT_lift_run,
        bind_assoc, pure_bind, map_bind, mem_support_bind_iff] at hx
      obtain ⟨res, -, hx⟩ := hx
      rcases res with _ | stP
      · simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, map_pure,
          Prod.map, support_pure, Set.mem_singleton_iff] at hx
        subst hx; exact hInv0
      · simp only [Option.isSome_some, ↓reduceIte] at hx
        subst hx; exact mirrorBoundInv_afterCorr P hInv
  · rw [challSimDFPaperProg_impl_run_eq_of_ne_cr K Δ qep _ (by intro _ h; cases h) v]
    exact challSimDFProg_step_clearComp K Δ qep m heqCt (.inr (P, c, c')) v hInv

def simTransmitC'DFPaper (Δ qep : ℕ) {Γ}
    (s : Expr OO Γ mirrorTy)
    (arg : Expr OO Γ (.prod .bool (.prod (.base .msg) (.opt (.base .coins))))) :
    Comp OO SIfaceDF Γ (.prod (.opt (.base .ct)) mirrorTy) :=
  rdsl do
    (s0, p, m, _) ← return (s, arg)
    optC ← query (I := SIfaceDF) SMTagDF.tr (p, m, none)
    match optC with
    | none => return (none, s0)
    | some ct =>
      match mEpMgmtE Δ qep s0 p false with
      | none => return (some ct, s0)
      | some s₁ =>
        let pos := (p, pGet (mEpoch s₁) p, pGet (mIdx s₁) p + 1)
        let rec_ := (pos, m, ct)
        return (some ct, mRecordE Δ s₁ p rec_ false)

def simChallC'DFPaper (Δ qep : ℕ) {Γ}
    (s : Expr OO Γ mirrorTy)
    (arg : Expr OO Γ
      (.prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .coins)))))) :
    Comp OO SIfaceDF Γ (.prod (.opt (.base .ct)) mirrorTy) :=
  rdsl do
    (s0, p, m₀, m₁, _) ← return (s, arg)
    match mEpMgmtE Δ qep s0 p false with
    | none => return (none, s0)
    | some s1 =>
      if !(mSafeChE Δ s1 p) then
        return (none, s0)
      else
        let mb := if mB s0 then m₁ else m₀
        optC ← query (I := SIfaceDF) SMTagDF.tr (p, mb, none)
        match optC with
        | none => return (none, s0)
        | some ct =>
          let pos := (p, pGet (mEpoch s1) p, pGet (mIdx s1) p + 1)
          let rec_ := (pos, mb, ct)
          return (some ct, mRecordE Δ s1 p rec_ true)

def simHandleC'DFPaper (K Δ qep : ℕ) :
    Comp OO SIfaceDF [mirrorTy, SQDF] (.prod SRDF mirrorTy) :=
  rdsl [s, q] do
    match q with
    | .transmit arg =>
      (r, s') ← simTransmitC'DFPaper Δ qep s arg
      return (.inl (.inl (.inl (.inl (.inl r)))), s')
    | .challenge arg =>
      (r, s') ← simChallC'DFPaper Δ qep s arg
      return (.inl (.inl (.inl (.inl (.inr r)))), s')
    | .deliver arg =>
      (r, s') ← simDeliverCDF K s arg
      return (.inl (.inl (.inl (.inr r))), s')
    | .inject arg =>
      (r, s') ← simInjectCDF K s arg
      return (.inl (.inl (.inr r)), s')
    | .corrupt arg =>
      (r, s') ← simCorrCDFPaper K s arg
      return (.inl (.inr r), s')
    | .deliverForge arg =>
      (r, s') ← simDeliverForgeCDF K s arg
      return (.inr r, s')

/-- Costed coin-stripping `DeliverForge.challSimDF'Paper` challenge simulator over `SM.specDF`. -/
@[reducible] def challSimDF'PaperProg (K Δ qep : ℕ) :
    CostedReduction OO SIfaceDF
      (SM.specDF (SMSort.den Key St St₂ Msg Coins RCoins C stSort) Msg Coins C)
      SCodecDF .unit .unit .bool .bool where
  σ := mirrorTy
  init := simInitCDF
  handle := simHandleC'DFPaper K Δ qep
  finish := rdsl [_, guess] do return guess

@[simp] theorem simImplDF'Paper_inl [DecidableEq Msg] [DecidableEq C] (Δ qep : ℕ) (n : ℕ) :
    DeliverForge.simImplDF'Paper (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
      (Msg := Msg) (Coins := Coins) (C := C) Δ qep (.inl n) =
      StateT.lift (query (spec := unifSpec +
        SM.specDF (SMSort.den Key St St₂ Msg Coins RCoins C stSort) Msg Coins C) (.inl n)) := rfl

@[simp] theorem simImplDF'Paper_tr [DecidableEq Msg] [DecidableEq C] (Δ qep : ℕ)
    (q : Party × Msg × Option Coins) :
    DeliverForge.simImplDF'Paper (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
      (Msg := Msg) (Coins := Coins) (C := C) Δ qep
      (.inr (.inl (.inl (.inl (.inl (.inl q)))))) =
      DeliverForge.simTransmitDF'Paper Δ qep q := rfl

@[simp] theorem simImplDF'Paper_ch [DecidableEq Msg] [DecidableEq C] (Δ qep : ℕ)
    (q : Party × Msg × Msg × Option Coins) :
    DeliverForge.simImplDF'Paper (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
      (Msg := Msg) (Coins := Coins) (C := C) Δ qep
      (.inr (.inl (.inl (.inl (.inl (.inr q)))))) =
      DeliverForge.simChallDF'Paper Δ qep q := rfl

@[simp] theorem simImplDF'Paper_dl [DecidableEq Msg] [DecidableEq C] (Δ qep : ℕ) (q : Party × C) :
    DeliverForge.simImplDF'Paper (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
      (Msg := Msg) (Coins := Coins) (C := C) Δ qep
      (.inr (.inl (.inl (.inl (.inr q))))) =
      DeliverForge.simDeliverDF q := rfl

@[simp] theorem simImplDF'Paper_ij [DecidableEq Msg] [DecidableEq C] (Δ qep : ℕ) (q : Party × C) :
    DeliverForge.simImplDF'Paper (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
      (Msg := Msg) (Coins := Coins) (C := C) Δ qep
      (.inr (.inl (.inl (.inr q)))) =
      DeliverForge.simInjectDF q := rfl

@[simp] theorem simImplDF'Paper_cr [DecidableEq Msg] [DecidableEq C] (Δ qep : ℕ) (P : Party) :
    DeliverForge.simImplDF'Paper (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
      (Msg := Msg) (Coins := Coins) (C := C) Δ qep
      (.inr (.inl (.inr P))) =
      DeliverForge.simCorrDFPaper P := rfl

@[simp] theorem simImplDF'Paper_df [DecidableEq Msg] [DecidableEq C] (Δ qep : ℕ)
    (q : Party × C × C) :
    DeliverForge.simImplDF'Paper (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
      (Msg := Msg) (Coins := Coins) (C := C) Δ qep
      (.inr (.inr q)) =
      DeliverForge.simDeliverForgeDF q := rfl

theorem simTransmitC'DFPaper_eval (Δ qep : ℕ) {Γ}
    (s : Expr OO Γ mirrorTy)
    (arg : Expr OO Γ (.prod .bool (.prod (.base .msg) (.opt (.base .coins)))))
    (ρ : Env Γ) (st : Thm1.Mirror Msg C) (P : Party) (m : Msg) (r : Option Coins)
    (hs : s.eval ρ = mirrorEnc st) (harg : arg.eval ρ = (partyEnc P, m, r)) :
    (simTransmitC'DFPaper (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
      (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
      Δ qep s arg).eval ρ =
      Prod.map id mirrorEnc <$>
        ((DeliverForge.simTransmitDF'Paper (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          Δ qep (P, m, r)).run st) := by
  unfold simTransmitC'DFPaper DeliverForge.simTransmitDF'Paper
  rw [Comp.eval_bind_ret]
  have h0 : (Expr.pair s arg).eval ρ = (mirrorEnc st, partyEnc P, m, r) := by
    simp [Expr.eval, hs, harg]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := (.prod mirrorTy (.prod .bool (.prod (.base .msg) (.opt (.base .coins)))) : Ty S))
    (mirrorEnc st, partyEnc P, m, r) ρ
  have htr : (Comp.query (I := SIfaceDF) SMTagDF.tr
      (.pair (.fst (.snd (Expr.v0 (O := OO)))) (.pair (.fst (.snd (.snd .v0))) .none))).eval ρ₁ =
      DeliverForge.transmitQueryDF (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
        P m none := by
    rw [query_trDF_eval]
    simp [ρ₁, partyDec_partyEnc, Expr.eval, Expr.v0]
  simp only [Comp.eval_bind, htr, StateT.run_bind, StateT.run_get, stateT_lift_run,
    bind_assoc, pure_bind, map_bind]
  refine bind_congr fun res => ?_
  rcases res with _ | c
  · simp [ρ₁, Comp.eval, Expr.eval, Expr.v0, Expr.v1, StateT.run_pure]
  · rw [Comp.eval_caseOpt_v0_some]
    set ρ₂ := Env.cons (t := (.base .ct : Ty S)) c
      (Env.cons (t := (.opt (.base .ct) : Ty S)) (some c) ρ₁)
    rw [Comp.eval_caseOpt]
    have hep : (mEpMgmtE Δ qep (.fst (Expr.v2 (O := OO))) (.fst (.snd .v2))
        (.bool false)).eval ρ₂ =
        (st.epMgmt Δ qep P false).map mirrorEnc := by
      rw [mEpMgmtE_eval Δ qep (.fst .v2) (.fst (.snd .v2)) (.bool false) ρ₂ st P rfl rfl]
      simp [Expr.eval]
    rw [hep]
    rcases st.epMgmt Δ qep P false with _ | s₁
    · simp [ρ₂, ρ₁, Expr.eval, Expr.v0, Expr.v2, StateT.run_pure]
    · simp only [Option.map_some, Comp.eval_ret, pair_eval, some_eval,
        StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, map_pure, Prod.map]
      set ρ₃ := Env.cons (t := mirrorTy) (mirrorEnc s₁) ρ₂
      congr 2
      refine mRecordE_eval Δ (Expr.v0 (O := OO)) (.fst (.snd .v3))
        (.pair (.pair (.fst (.snd .v3))
          (.pair (pGet (mEpoch .v0) (.fst (.snd .v3)))
            (.add (pGet (mIdx .v0) (.fst (.snd .v3))) (.nat 1))))
          (.pair (.fst (.snd (.snd .v3))) .v1))
        (.bool false) ρ₃ s₁ P ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, c⟩ rfl rfl ?_
      cases P <;> simp [ρ₃, ρ₂, ρ₁, mEpoch, mIdx, pGet, mirrorEnc, gsEnc, recEnc, posEnc,
        partyEnc, Expr.eval, Expr.v0, Expr.v1, Expr.v3]

theorem simChallC'DFPaper_eval (Δ qep : ℕ) {Γ}
    (s : Expr OO Γ mirrorTy)
    (arg : Expr OO Γ
      (.prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .coins))))))
    (ρ : Env Γ) (st : Thm1.Mirror Msg C) (P : Party) (m₀ m₁ : Msg) (r : Option Coins)
    (hs : s.eval ρ = mirrorEnc st) (harg : arg.eval ρ = (partyEnc P, m₀, m₁, r)) :
    (simChallC'DFPaper (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
      (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
      Δ qep s arg).eval ρ =
      Prod.map id mirrorEnc <$>
        ((DeliverForge.simChallDF'Paper (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          Δ qep (P, m₀, m₁, r)).run st) := by
  unfold simChallC'DFPaper DeliverForge.simChallDF'Paper
  rw [Comp.eval_bind_ret]
  have h0 : (Expr.pair s arg).eval ρ = (mirrorEnc st, partyEnc P, m₀, m₁, r) := by
    simp [Expr.eval, hs, harg]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := (.prod mirrorTy
      (.prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .coins))))) : Ty S))
    (mirrorEnc st, partyEnc P, m₀, m₁, r) ρ
  rw [Comp.eval_caseOpt]
  have hep : (mEpMgmtE Δ qep (.fst (Expr.v0 (O := OO))) (.fst (.snd .v0))
      (.bool false)).eval ρ₁ =
      (st.epMgmt Δ qep P false).map mirrorEnc := by
    rw [mEpMgmtE_eval Δ qep (.fst .v0) (.fst (.snd .v0)) (.bool false) ρ₁ st P rfl rfl]
    simp [Expr.eval]
  rw [hep]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rcases st.epMgmt Δ qep P false with _ | s₁
  · simp [ρ₁, Expr.eval, Expr.v0, StateT.run_pure]
  · simp only [Option.map_some]
    set ρ₂ := Env.cons (t := mirrorTy) (mirrorEnc s₁) ρ₁
    rw [Comp.eval_ite]
    have hsafe : (Expr.not (mSafeChE Δ (Expr.v0 (O := OO)) (.fst (.snd .v1)))).eval ρ₂ =
        !(s₁.safeCh Δ P) := by
      simp only [Expr.eval]
      rw [mSafeChE_eval Δ .v0 (.fst (.snd .v1)) ρ₂ s₁ P rfl rfl]
    rw [hsafe]
    by_cases hsc : !(s₁.safeCh Δ P)
    · simp [ρ₂, ρ₁, hsc, Expr.eval, Expr.v1, StateT.run_pure]
    · simp only [hsc, Bool.false_eq_true, ↓reduceIte, Comp.eval_bind,
        StateT.run_bind, stateT_lift_run, bind_assoc, pure_bind, map_bind]
      have hsend : (Comp.query (I := SIfaceDF) SMTagDF.tr
          (.pair (.fst (.snd (Expr.v1 (O := OO))))
            (.pair (.ite (mB (.fst .v1)) (.fst (.snd (.snd (.snd .v1)))) (.fst (.snd (.snd .v1))))
              .none))).eval ρ₂ =
          DeliverForge.transmitQueryDF (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
            P (if st.b then m₁ else m₀) none := by
        rw [query_trDF_eval]
        simp [ρ₂, ρ₁, mB, mirrorEnc, gsEnc, partyDec_partyEnc, Expr.eval, Expr.v1]
      rw [hsend]
      refine bind_congr fun res => ?_
      rcases res with _ | c
      · simp [ρ₂, ρ₁, Comp.eval, Expr.eval, Expr.v0, Expr.v2, StateT.run_pure]
      · rw [Comp.eval_caseOpt_v0_some]
        set ρ₃ := Env.cons (t := (.base .ct : Ty S)) c
          (Env.cons (t := (.opt (.base .ct) : Ty S)) (some c) ρ₂)
        simp only [Comp.eval_ret, pair_eval, some_eval,
          StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, map_pure, Prod.map]
        congr 2
        refine mRecordE_eval Δ (Expr.v2 (O := OO)) (.fst (.snd .v3))
          (.pair (.pair (.fst (.snd .v3))
            (.pair (pGet (mEpoch .v2) (.fst (.snd .v3)))
              (.add (pGet (mIdx .v2) (.fst (.snd .v3))) (.nat 1))))
            (.pair (.ite (mB (.fst .v3))
              (.fst (.snd (.snd (.snd .v3)))) (.fst (.snd (.snd .v3)))) .v0))
          (.bool true) ρ₃ s₁ P
          ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, if st.b then m₁ else m₀, c⟩ rfl rfl ?_
        cases P <;> simp [ρ₃, ρ₂, ρ₁, mEpoch, mIdx, mB, pGet, mirrorEnc, gsEnc, recEnc, posEnc,
          partyEnc, Expr.eval, Expr.v0, Expr.v2, Expr.v3]

theorem handlerImpl_simHandleC'DFPaper_tr (K Δ qep : ℕ)
    (st : Thm1.Mirror Msg C) (P : Party) (m : Msg) (r : Option Coins) :
    ((handlerImpl (C := SCodecDF)
      (simHandleC'DFPaper (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
        (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
        (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
        (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
        K Δ qep)
      (.inr (.inl (.inl (.inl (.inl (.inl (P, m, r)))))))).run (mirrorEnc st)) =
      Prod.map id mirrorEnc <$>
        ((DeliverForge.simTransmitDF'Paper (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          Δ qep (P, m, r)).run st) := by
  unfold handlerImpl simHandleC'DFPaper smCodecDF smCodec
  simp only [StateT.run_mk, Comp.eval, Expr.eval, Expr.v0, Expr.v1,
    Env.get_cons_zero, Env.get_cons_succ, bind_assoc, pure_bind]
  rw [simTransmitC'DFPaper_eval Δ qep .v5 (.var .zero) _ st P m r rfl rfl]
  simp

theorem handlerImpl_simHandleC'DFPaper_ch (K Δ qep : ℕ)
    (st : Thm1.Mirror Msg C) (P : Party) (m₀ m₁ : Msg) (r : Option Coins) :
    ((handlerImpl (C := SCodecDF)
      (simHandleC'DFPaper (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
        (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
        (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
        (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
        K Δ qep)
      (.inr (.inl (.inl (.inl (.inl (.inr (P, m₀, m₁, r)))))))).run (mirrorEnc st)) =
      Prod.map id mirrorEnc <$>
        ((DeliverForge.simChallDF'Paper (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          Δ qep (P, m₀, m₁, r)).run st) := by
  unfold handlerImpl simHandleC'DFPaper smCodecDF smCodec
  simp only [StateT.run_mk, Comp.eval, Expr.eval, Expr.v0, Expr.v1,
    Env.get_cons_zero, Env.get_cons_succ, bind_assoc, pure_bind]
  rw [simChallC'DFPaper_eval Δ qep .v5 (.var .zero) _ st P m₀ m₁ r rfl rfl]
  simp

theorem simImplDF'Paper_clearComp [DecidableEq C] (Δ qep : ℕ)
    (t : (SM.specDF (SMSort.den Key St St₂ Msg Coins RCoins C stSort) Msg Coins C).Domain)
    (st : Thm1.Mirror Msg C) :
    Prod.map id mirrorClearComp <$>
      ((DeliverForge.simImplDF'Paper (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
        (Msg := Msg) (Coins := Coins) (C := C) Δ qep (.inr t)).run st) =
    Prod.map id mirrorClearComp <$>
      ((DeliverForge.simImplDF'Paper (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
        (Msg := Msg) (Coins := Coins) (C := C) Δ qep (.inr t)).run (mirrorClearComp st)) := by
  rcases t with (((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩)
  · simp only [simImplDF'Paper_tr, DeliverForge.simTransmitDF'Paper,
      StateT.run_bind, StateT.run_get, stateT_lift_run, bind_assoc, pure_bind, map_bind,
      mirrorClearComp_epMgmt]
    refine bind_congr fun res => ?_
    rcases res with _ | c <;> rcases st.epMgmt Δ qep P false with _ | s₁ <;>
    simp [StateT.run_pure, StateT.run_set, Prod.map]
  · simp only [simImplDF'Paper_ch, DeliverForge.simChallDF'Paper,
      StateT.run_bind, StateT.run_get, pure_bind, mirrorClearComp_epMgmt]
    rcases st.epMgmt Δ qep P false with _ | s₁
    · simp [StateT.run_pure, Prod.map]
    · simp only [Option.map_some, mirrorClearComp_safeCh, mirrorClearComp_b, mirrorClearComp_epoch,
        mirrorClearComp_idx]
      by_cases hsc : !(s₁.safeCh Δ P)
      · simp [hsc, StateT.run_pure, Prod.map]
      · simp only [hsc, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, stateT_lift_run,
          bind_assoc, pure_bind, map_bind]
        refine bind_congr fun res => ?_
        rcases res with _ | c <;>
        (simp [StateT.run_pure, StateT.run_set, Prod.map]; try rfl)
  · exact simImplDFPaper_clearComp Δ qep (.inl (.inl (.inl (.inr (P, c))))) st
  · exact simImplDFPaper_clearComp Δ qep (.inl (.inl (.inr (P, c)))) st
  · exact simImplDFPaper_clearComp Δ qep (.inl (.inr P)) st
  · exact simImplDFPaper_clearComp Δ qep (.inr (P, c, c')) st

theorem challSimDF'PaperProg_impl_run_eq_of_ne_tr_ch (K Δ qep : ℕ)
    (t : (SM.specDF (SMSort.den Key St St₂ Msg Coins RCoins C stSort) Msg Coins C).Domain)
    (hne_tr : ∀ q, t ≠ .inl (.inl (.inl (.inl (.inl q)))))
    (hne_ch : ∀ q, t ≠ .inl (.inl (.inl (.inl (.inr q)))))
    (v : (@mirrorTy Key St St₂ Msg Coins RCoins C).denote) :
    (((challSimDF'PaperProg (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
      (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
      K Δ qep).impl (.inr t)).run v) =
    (((challSimDFPaperProg (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
      (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
      K Δ qep).impl (.inr t)).run v) := by
  rcases t with (((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩)
  · exact absurd rfl (hne_tr (P, m, r))
  · exact absurd rfl (hne_ch (P, m₀, m₁, r))
  · unfold challSimDF'PaperProg challSimDFPaperProg CostedReduction.impl
      handlerImpl simHandleC'DFPaper simHandleCDFPaper smCodecDF smCodec
    simp only [StateT.run_mk, Comp.eval, Expr.eval, Expr.v0, Expr.v1,
      Env.get_cons_zero, Env.get_cons_succ]
  · unfold challSimDF'PaperProg challSimDFPaperProg CostedReduction.impl
      handlerImpl simHandleC'DFPaper simHandleCDFPaper smCodecDF smCodec
    simp only [StateT.run_mk, Comp.eval, Expr.eval, Expr.v0, Expr.v1,
      Env.get_cons_zero, Env.get_cons_succ]
  · unfold challSimDF'PaperProg challSimDFPaperProg CostedReduction.impl
      handlerImpl simHandleC'DFPaper simHandleCDFPaper smCodecDF smCodec
    simp only [StateT.run_mk, Comp.eval, Expr.eval, Expr.v0, Expr.v1,
      Env.get_cons_zero, Env.get_cons_succ]
  · unfold challSimDF'PaperProg challSimDFPaperProg CostedReduction.impl
      handlerImpl simHandleC'DFPaper simHandleCDFPaper smCodecDF
    simp only [StateT.run_mk, Comp.eval, Expr.eval, Expr.v0, Expr.v1,
      Env.get_cons_zero, Env.get_cons_succ]

theorem challSimDF'PaperProg_step_clearComp [DecidableEq C] (K Δ qep m : ℕ)
    (heqCt : eqCt = (· == ·))
    (t : (SM.specDF (SMSort.den Key St St₂ Msg Coins RCoins C stSort) Msg Coins C).Domain)
    (v : (@mirrorTy Key St St₂ Msg Coins RCoins C).denote)
    (hInv : MirrorBoundInv K (m + 1) v) :
    (Prod.map id (mirrorClearComp ∘ mirrorDec) <$>
      (((challSimDF'PaperProg (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
           (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
           (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
           (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
           K Δ qep).impl (.inr t)).run v)) =
      ((clearCompImpl (DeliverForge.simImplDF'Paper
          (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          (Msg := Msg) (Coins := Coins) (C := C) Δ qep) (.inr t)).run
            (mirrorClearComp (mirrorDec v))) ∧
    ∀ r ∈ support (((challSimDF'PaperProg (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
        (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
        (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
        (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
        K Δ qep).impl (.inr t)).run v), MirrorBoundInv K m r.2 := by
  rcases t with (((((⟨P, msg, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩)
  · set st := mirrorDec v
    have hv : v = mirrorEnc st := (mirrorEnc_mirrorDec v).symm
    have hInv0 : MirrorBoundInv (Key := Key) (St := St) (St₂ := St₂)
        (Coins := Coins) (RCoins := RCoins) K m (mirrorEnc st) := by
      rw [← hv]; exact hInv.mono (Nat.le_succ m)
    rw [hv, clearCompImpl, StateT.run_mk,
      ← simImplDF'Paper_clearComp Δ qep (.inl (.inl (.inl (.inl (.inl (P, msg, r)))))) st]
    have hrun : (((challSimDF'PaperProg (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
        (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
        (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
        (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
        K Δ qep).impl (.inr (.inl (.inl (.inl (.inl (.inl (P, msg, r)))))))).run (mirrorEnc st)) =
      Prod.map id mirrorEnc <$>
        ((DeliverForge.simTransmitDF'Paper (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          Δ qep (P, msg, r)).run st) :=
      handlerImpl_simHandleC'DFPaper_tr K Δ qep st P msg r
    rw [hrun]
    refine ⟨by rw [Functor.map_map]; congr 1; funext ⟨a, s⟩; simp [Prod.map], ?_⟩
    intro x hx
    simp only [DeliverForge.simTransmitDF'Paper, StateT.run_bind, StateT.run_get, stateT_lift_run,
      bind_assoc, pure_bind, map_bind, mem_support_bind_iff] at hx
    obtain ⟨res, -, hx⟩ := hx
    rcases res with _ | c
    · simp only [StateT.run_pure, map_pure, Prod.map, support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact hInv0
    · rcases hep : st.epMgmt Δ qep P false with _ | s₁
      · simp only [hep, StateT.run_pure, map_pure, Prod.map, support_pure,
          Set.mem_singleton_iff] at hx
        subst hx; exact hInv0
      · simp only [hep] at hx
        subst hx; exact mirrorBoundInv_record _ hInv hep
  · set st := mirrorDec v
    have hv : v = mirrorEnc st := (mirrorEnc_mirrorDec v).symm
    have hInv0 : MirrorBoundInv (Key := Key) (St := St) (St₂ := St₂)
        (Coins := Coins) (RCoins := RCoins) K m (mirrorEnc st) := by
      rw [← hv]; exact hInv.mono (Nat.le_succ m)
    rw [hv, clearCompImpl, StateT.run_mk,
      ← simImplDF'Paper_clearComp Δ qep (.inl (.inl (.inl (.inl (.inr (P, m₀, m₁, r)))))) st]
    have hrun : (((challSimDF'PaperProg (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
        (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
        (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
        (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
        K Δ qep).impl
          (.inr (.inl (.inl (.inl (.inl (.inr (P, m₀, m₁, r)))))))).run (mirrorEnc st)) =
      Prod.map id mirrorEnc <$>
        ((DeliverForge.simChallDF'Paper (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          Δ qep (P, m₀, m₁, r)).run st) :=
      handlerImpl_simHandleC'DFPaper_ch K Δ qep st P m₀ m₁ r
    rw [hrun]
    refine ⟨by rw [Functor.map_map]; congr 1; funext ⟨a, s⟩; simp [Prod.map], ?_⟩
    intro x hx
    simp only [DeliverForge.simChallDF'Paper, StateT.run_bind, StateT.run_get, pure_bind] at hx
    rcases hep : st.epMgmt Δ qep P false with _ | s₁
    · simp only [hep, StateT.run_pure, map_pure, Prod.map, support_pure,
        Set.mem_singleton_iff] at hx
      subst hx; exact hInv0
    · simp only [hep] at hx
      by_cases hsc : !(s₁.safeCh Δ P)
      · simp only [hsc, ↓reduceIte, StateT.run_pure, map_pure, Prod.map, support_pure,
          Set.mem_singleton_iff] at hx
        subst hx; exact hInv0
      · simp only [hsc, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, stateT_lift_run,
          bind_assoc, pure_bind, map_bind, mem_support_bind_iff] at hx
        obtain ⟨res, -, hx⟩ := hx
        rcases res with _ | c
        · simp only [StateT.run_pure, map_pure, Prod.map, support_pure,
            Set.mem_singleton_iff] at hx
          subst hx; exact hInv0
        · subst hx; exact mirrorBoundInv_record _ hInv hep
  · rw [challSimDF'PaperProg_impl_run_eq_of_ne_tr_ch K Δ qep _
      (by intro _ h; cases h) (by intro _ h; cases h) v]
    exact challSimDFPaperProg_step_clearComp K Δ qep m heqCt
      (.inl (.inl (.inl (.inr (P, c))))) v hInv
  · rw [challSimDF'PaperProg_impl_run_eq_of_ne_tr_ch K Δ qep _
      (by intro _ h; cases h) (by intro _ h; cases h) v]
    exact challSimDFPaperProg_step_clearComp K Δ qep m heqCt
      (.inl (.inl (.inr (P, c)))) v hInv
  · rw [challSimDF'PaperProg_impl_run_eq_of_ne_tr_ch K Δ qep _
      (by intro _ h; cases h) (by intro _ h; cases h) v]
    exact challSimDFPaperProg_step_clearComp K Δ qep m heqCt
      (.inl (.inr P)) v hInv
  · rw [challSimDF'PaperProg_impl_run_eq_of_ne_tr_ch K Δ qep _
      (by intro _ h; cases h) (by intro _ h; cases h) v]
    exact challSimDFPaperProg_step_clearComp K Δ qep m heqCt
      (.inr (P, c, c')) v hInv

/-- Evaluation agreement between `challSimDF'PaperProg` and `DeliverForge.challSimDF'Paper` for
`q ≤ K` game queries. -/
theorem challSimDF'PaperProg_eval [DecidableEq Msg] [DecidableEq C] (K Δ qep : ℕ)
    (heqCt : eqCt = (· == ·))
    (A : DeliverForge.AdversaryDF (SMSort.den Key St St₂ Msg Coins RCoins C stSort) Msg Coins C)
    (q : ℕ) (hq : DeliverForge.MakesAtMostQueriesDF A q) (hqK : q ≤ K) :
    (challSimDF'PaperProg (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
      (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
      K Δ qep).eval (fun _ => A) () =
      DeliverForge.challSimDF'Paper Δ qep A := by
  let so := DeliverForge.simImplDF'Paper (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
    (Msg := Msg) (Coins := Coins) (C := C) Δ qep
  have hq' := (makesAtMostQueriesDF_iff_isGameQuery A q).mp hq
  have h1 := (challSimDF'PaperProg (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
      (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
      K Δ qep).eval_eq_simulateQ_of_abs
    (mirrorClearComp ∘ mirrorDec) (MirrorBoundInv K)
    (fun _ => do
      let b ← (liftM ($ᵗ Bool : ProbComp Bool) :
        DeliverForge.AdversaryCompDF (SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          Msg Coins C Bool)
      return ((), ({ st := fun _ => (), b } : Thm1.Mirror Msg C)))
    (clearCompImpl so)
    (fun _ b' => pure b')
    q ()
    (by simp [challSimDF'PaperProg, simInitCDF_eval, map_eq_bind_pure_comp]; rfl)
    (by
      intro r hr
      change r ∈ support ((simInitCDF (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
        (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
        (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
        (sampKey := sampKey) (sampCoins := sampCoins)
        (sampRCoins := sampRCoins)).eval (Env.cons (t := .unit) () Env.nil)) at hr
      rw [simInitCDF_eval, mem_support_bind_iff] at hr
      obtain ⟨b, -, hr⟩ := hr
      rw [support_pure, Set.mem_singleton_iff] at hr
      subst hr
      exact ⟨by simp [hqK], by simp [hqK]⟩)
    (fun n s => rfl)
    (fun m t v hv => challSimDF'PaperProg_step_clearComp K Δ qep m heqCt t v hv)
    (fun _ _ _ => rfl)
    (fun _ hle hv => hv.mono hle)
    (fun _ => A) (fun _ => hq')
  rw [h1]
  have h2 : ∀ (b : Bool),
      (simulateQ (clearCompImpl so) A).run ({ st := fun _ => (), b } : Thm1.Mirror Msg C) =
        Prod.map id mirrorClearComp <$>
          (simulateQ so A).run ({ st := fun _ => (), b } : Thm1.Mirror Msg C) := by
    intro b
    refine (simulateQ_run_abs_of_bound so (clearCompImpl so) mirrorClearComp (fun _ _ => True)
      (fun _ n s _ => ⟨?_, fun _ _ => trivial⟩)
      (fun _ t s _ => ⟨simImplDF'Paper_clearComp Δ qep t s, fun _ _ => trivial⟩)
      hq' ({ st := fun _ => (), b } : Thm1.Mirror Msg C) trivial).symm
    dsimp [clearCompImpl, so]
    simp [Prod.map, map_eq_bind_pure_comp]
  unfold DeliverForge.challSimDF'Paper
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun b => ?_
  rw [h2 b, StateT.run', bind_map_left, map_eq_bind_pure_comp]
  rfl

@[simp] theorem simHandleC'DFPaper_queries (K Δ qep : ℕ) :
    (simHandleC'DFPaper (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
      (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
      K Δ qep).queries (fun _ => 1) (fun _ => 0) = 1 := by
  simp [simHandleC'DFPaper, simTransmitC'DFPaper, simChallC'DFPaper, simDeliverCDF, simInjectCDF,
    simCorrCDFPaper, simDeliverForgeCDF, Comp.queries]

@[simp] theorem challSimDF'PaperProg_totalQueries (K Δ qep q : ℕ) :
    (challSimDF'PaperProg (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
      (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
      K Δ qep).totalQueries (fun _ => 1) (fun _ => 0) q = q := by
  simp [CostedReduction.totalQueries, challSimDF'PaperProg, Comp.queries]

theorem challSimDF'PaperProg_totalCost (K Δ qep q : ℕ) :
    (challSimDF'PaperProg (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
      (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
      K Δ qep).totalCost q =
      41 + q * ((simHandleC'DFPaper (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
        (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
        (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
        (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
        K Δ qep).cost + 7) := by
  simp only [CostedReduction.totalCost, challSimDF'PaperProg, simInitCDF_cost, smCodecDF, smIfaceDF, Comp.cost,
    Expr.cost, Expr.v1]
  rw [max_eq_right (by omega)]
  omega

end ChallSimDFPaperProg

end CryptoGames.SM
