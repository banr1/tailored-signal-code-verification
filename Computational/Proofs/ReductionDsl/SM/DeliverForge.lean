/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.SM.Theorem1
public import Computational.Proofs.ReductionDsl.SM.RedCKA
public import Computational.Proofs.ReductionDsl.SM.RedPRNG
public import Computational.Proofs.ReductionDsl.SM.RedFS
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForge
import Computational.Proofs.ReductionDsl.Bridge
import Computational.Proofs.ReductionDsl.Notation
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePRNG -- shake: keep

/-!
# Costed Reductions for `DeliverForge`

Defines the deep-embedded `CostedReduction` simulator `challSimDFProg`, the six-oracle engine
dispatcher `implECDF`, and the reductions `redCKAAuthDFProg`, `redPRNGAuthDFProg`, and
`redFSAuthDFProg` over `SM.specDF`.
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

/-! ## Challenge simulator -/

section ChallSimDFProg

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

def simTransmitCDF (Δ qep : ℕ) {Γ}
    (s : Expr OO Γ mirrorTy)
    (arg : Expr OO Γ (.prod .bool (.prod (.base .msg) (.opt (.base .coins))))) :
    Comp OO SIfaceDF Γ (.prod (.opt (.base .ct)) mirrorTy) :=
  rdsl do
    (s0, q@(p, m, r)) ← return (s, arg)
    optC ← query (I := SIfaceDF) SMTagDF.tr q
    match optC with
    | none => return (none, s0)
    | some ct =>
      match mEpMgmtE Δ qep s0 p (isSomeE r) with
      | none => return (some ct, s0)
      | some s₁ =>
        let pos := (p, pGet (mEpoch s₁) p, pGet (mIdx s₁) p + 1)
        let rec_ := (pos, m, ct)
        return (some ct, mRecordE Δ s₁ p rec_ false)

def simChallCDF (Δ qep : ℕ) {Γ}
    (s : Expr OO Γ mirrorTy)
    (arg : Expr OO Γ
      (.prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .coins)))))) :
    Comp OO SIfaceDF Γ (.prod (.opt (.base .ct)) mirrorTy) :=
  rdsl do
    (s0, p, m₀, m₁, r) ← return (s, arg)
    match mEpMgmtE Δ qep s0 p (isSomeE r) with
    | none => return (none, s0)
    | some s1 =>
      if !(mSafeChE Δ s1 p) then
        return (none, s0)
      else
        let mb := if mB s0 then m₁ else m₀
        optC ← query (I := SIfaceDF) SMTagDF.tr (p, mb, r)
        match optC with
        | none => return (none, s0)
        | some ct =>
          let pos := (p, pGet (mEpoch s1) p, pGet (mIdx s1) p + 1)
          let rec_ := (pos, mb, ct)
          return (some ct, mRecordE Δ s1 p rec_ true)

def simDeliverCDF (K : ℕ) {Γ}
    (s : Expr OO Γ mirrorTy)
    (arg : Expr OO Γ (.prod .bool (.base .ct))) :
    Comp OO SIfaceDF Γ (.prod (.opt (smRrTy Key St St₂ Msg Coins RCoins C)) mirrorTy) :=
  rdsl do
    (s0, q@(p0, ct)) ← return (s, arg)
    optRr ← query (I := SIfaceDF) SMTagDF.dl q
    match optRr with
    | none => return (none, s0)
    | some rr =>
      match rr with
      | .inl _ => return (some (.inl ()), s0)
      | .inr tim@(t', i', m) =>
        match mInTransitE K s0 (otherE p0) ct with
        | none => return (some (.inr tim), s0)
        | some r =>
          let rPos := recPos r
          let mOut := if mChallContainsE K s0 rPos then none else m
          return (some (.inr (t', i', mOut)), mAcceptE K s0 p0 rPos)

def simInjectCDF (K : ℕ) {Γ}
    (s : Expr OO Γ mirrorTy)
    (arg : Expr OO Γ (.prod .bool (.base .ct))) :
    Comp OO SIfaceDF Γ (.prod (.opt (smRrTy Key St St₂ Msg Coins RCoins C)) mirrorTy) :=
  rdsl do
    (s0, q@(p0, _)) ← return (s, arg)
    optRr ← query (I := SIfaceDF) SMTagDF.ij q
    match optRr with
    | none => return (none, s0)
    | some rr =>
      match rr with
      | .inl _ => return (some (.inl ()), s0)
      | .inr tim@(t', i', _) =>
        let pos := (otherE p0, t', i')
        return (some (.inr tim), mAcceptE K s0 p0 pos)

def simCorrCDF (K : ℕ) {Γ}
    (s : Expr OO Γ mirrorTy)
    (p : Expr OO Γ .bool) :
    Comp OO SIfaceDF Γ (.prod (.opt (.base stSort)) mirrorTy) :=
  rdsl do
    (s0, p0) ← return (s, p)
    res ← query (I := SIfaceDF) SMTagDF.cr p0
    if isSomeE res then
      return (res, mAfterCorrE K s0 p0)
    else
      return (res, s0)

def simDeliverForgeCDF (K : ℕ) {Γ}
    (s : Expr OO Γ mirrorTy)
    (arg : Expr OO Γ (.prod .bool (.prod (.base .ct) (.base .ct)))) :
    Comp OO SIfaceDF Γ (.prod (.opt (smRrTy Key St St₂ Msg Coins RCoins C)) mirrorTy) :=
  rdsl do
    (s0, q@(p0, _)) ← return (s, arg)
    optRr ← query (I := SIfaceDF) SMTagDF.df q
    match optRr with
    | none => return (none, s0)
    | some rr =>
      match rr with
      | .inl _ => return (some (.inl ()), s0)
      | .inr tim@(t', i', _) =>
        let pos := (otherE p0, t', i')
        return (some (.inr tim), mAcceptE K s0 p0 pos)

def simHandleCDF (K Δ qep : ℕ) :
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
      (r, s') ← simCorrCDF K s arg
      return (.inl (.inr r), s')
    | .deliverForge arg =>
      (r, s') ← simDeliverForgeCDF K s arg
      return (.inr r, s')

def simInitCDF : Comp OO SIfaceDF [.unit] (.prod .unit mirrorTy) :=
  rdsl [_] do
    b ← sample (I := SIfaceDF) SMSamp.bit ()
    return ((), mMk ((), ()) b false (0, 0) (0, 0) none [] [] [] (tconst 0, tconst 0) [] [])

/-- Costed `DeliverForge.challSimDF` challenge simulator over `SM.specDF`. -/
@[reducible] def challSimDFProg (K Δ qep : ℕ) :
    CostedReduction OO SIfaceDF
      (SM.specDF (SMSort.den Key St St₂ Msg Coins RCoins C stSort) Msg Coins C)
      SCodecDF .unit .unit .bool .bool where
  σ := mirrorTy
  init := simInitCDF
  handle := simHandleCDF K Δ qep
  finish := rdsl [_, guess] do return guess

@[simp] theorem query_trDF_eval {Γ}
    (e : Expr OO Γ (.prod .bool (.prod (.base .msg) (.opt (.base .coins))))) (ρ : Env Γ) :
    (Comp.query (I := SIfaceDF) SMTagDF.tr e).eval ρ =
      DeliverForge.transmitQueryDF (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
        (partyDec (e.eval ρ).1) (e.eval ρ).2.1 (e.eval ρ).2.2 := by
  simp [Comp.eval, smIfaceDF, DeliverForge.transmitQueryDF]

@[simp] theorem query_dlDF_eval {Γ}
    (e : Expr OO Γ (.prod .bool (.base .ct))) (ρ : Env Γ) :
    (Comp.query (I := SIfaceDF) SMTagDF.dl e).eval ρ =
      Option.map smRrEnc <$>
        DeliverForge.deliverQueryDF (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          (Coins := Coins) (partyDec (e.eval ρ).1) (e.eval ρ).2 := by
  simp [Comp.eval, smIfaceDF, DeliverForge.deliverQueryDF]

@[simp] theorem query_ijDF_eval {Γ}
    (e : Expr OO Γ (.prod .bool (.base .ct))) (ρ : Env Γ) :
    (Comp.query (I := SIfaceDF) SMTagDF.ij e).eval ρ =
      Option.map smRrEnc <$>
        DeliverForge.injectQueryDF (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          (Coins := Coins) (partyDec (e.eval ρ).1) (e.eval ρ).2 := by
  simp [Comp.eval, smIfaceDF, DeliverForge.injectQueryDF]

@[simp] theorem query_crDF_eval {Γ}
    (e : Expr OO Γ .bool) (ρ : Env Γ) :
    (Comp.query (I := SIfaceDF) SMTagDF.cr e).eval ρ =
      DeliverForge.corrQueryDF (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
        (Msg := Msg) (Coins := Coins) (C := C) (partyDec (e.eval ρ)) := by
  simp [Comp.eval, smIfaceDF, DeliverForge.corrQueryDF]

@[simp] theorem query_dfDF_eval {Γ}
    (e : Expr OO Γ (.prod .bool (.prod (.base .ct) (.base .ct)))) (ρ : Env Γ) :
    (Comp.query (I := SIfaceDF) SMTagDF.df e).eval ρ =
      Option.map smRrEnc <$>
        DeliverForge.deliverForgeQuery (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          (Coins := Coins) (partyDec (e.eval ρ).1) (e.eval ρ).2.1 (e.eval ρ).2.2 := by
  simp [Comp.eval, smIfaceDF, DeliverForge.deliverForgeQuery]

@[simp] theorem simImplDF_inl [DecidableEq C] (Δ qep : ℕ) (n : ℕ) :
    DeliverForge.simImplDF (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
      (Msg := Msg) (Coins := Coins) (C := C) Δ qep (.inl n) =
      StateT.lift (query (spec := unifSpec +
        SM.specDF (SMSort.den Key St St₂ Msg Coins RCoins C stSort) Msg Coins C) (.inl n)) := rfl

@[simp] theorem simImplDF_tr [DecidableEq C] (Δ qep : ℕ) (q : Party × Msg × Option Coins) :
    DeliverForge.simImplDF (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
      (Msg := Msg) (Coins := Coins) (C := C) Δ qep
      (.inr (.inl (.inl (.inl (.inl (.inl q)))))) =
      DeliverForge.simTransmitDF Δ qep q := rfl

@[simp] theorem simImplDF_ch [DecidableEq C] (Δ qep : ℕ)
    (q : Party × Msg × Msg × Option Coins) :
    DeliverForge.simImplDF (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
      (Msg := Msg) (Coins := Coins) (C := C) Δ qep
      (.inr (.inl (.inl (.inl (.inl (.inr q)))))) =
      DeliverForge.simChallDF Δ qep q := rfl

@[simp] theorem simImplDF_dl [DecidableEq C] (Δ qep : ℕ) (q : Party × C) :
    DeliverForge.simImplDF (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
      (Msg := Msg) (Coins := Coins) (C := C) Δ qep
      (.inr (.inl (.inl (.inl (.inr q))))) =
      DeliverForge.simDeliverDF q := rfl

@[simp] theorem simImplDF_ij [DecidableEq C] (Δ qep : ℕ) (q : Party × C) :
    DeliverForge.simImplDF (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
      (Msg := Msg) (Coins := Coins) (C := C) Δ qep
      (.inr (.inl (.inl (.inr q)))) =
      DeliverForge.simInjectDF q := rfl

@[simp] theorem simImplDF_cr [DecidableEq C] (Δ qep : ℕ) (P : Party) :
    DeliverForge.simImplDF (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
      (Msg := Msg) (Coins := Coins) (C := C) Δ qep
      (.inr (.inl (.inr P))) =
      DeliverForge.simCorrDF P := rfl

@[simp] theorem simImplDF_df [DecidableEq C] (Δ qep : ℕ) (q : Party × C × C) :
    DeliverForge.simImplDF (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
      (Msg := Msg) (Coins := Coins) (C := C) Δ qep
      (.inr (.inr q)) =
      DeliverForge.simDeliverForgeDF q := rfl

theorem simTransmitCDF_eval (Δ qep : ℕ) {Γ}
    (s : Expr OO Γ mirrorTy)
    (arg : Expr OO Γ (.prod .bool (.prod (.base .msg) (.opt (.base .coins)))))
    (ρ : Env Γ) (st : Thm1.Mirror Msg C) (P : Party) (m : Msg) (r : Option Coins)
    (hs : s.eval ρ = mirrorEnc st) (harg : arg.eval ρ = (partyEnc P, m, r)) :
    (simTransmitCDF (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
      (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
      Δ qep s arg).eval ρ =
      Prod.map id mirrorEnc <$>
        ((DeliverForge.simTransmitDF (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          Δ qep (P, m, r)).run st) := by
  unfold simTransmitCDF DeliverForge.simTransmitDF
  rw [Comp.eval_bind_ret]
  have h0 : (Expr.pair s arg).eval ρ = (mirrorEnc st, partyEnc P, m, r) := by
    simp [Expr.eval, hs, harg]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := (.prod mirrorTy (.prod .bool (.prod (.base .msg) (.opt (.base .coins)))) : Ty S))
    (mirrorEnc st, partyEnc P, m, r) ρ
  have htr : (Comp.query (I := SIfaceDF) SMTagDF.tr (.snd (Expr.v0 (O := OO)))).eval ρ₁ =
      DeliverForge.transmitQueryDF (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
        P m r := by
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
        (isSomeE (.snd (.snd (.snd .v2))))).eval ρ₂ =
        (st.epMgmt Δ qep P r.isSome).map mirrorEnc := by
      rw [mEpMgmtE_eval Δ qep (.fst .v2) (.fst (.snd .v2)) (isSomeE (.snd (.snd (.snd .v2))))
        ρ₂ st P rfl rfl]
      simp [ρ₂, ρ₁, isSomeE_eval, Expr.eval, Expr.v2]
    rw [hep]
    rcases st.epMgmt Δ qep P r.isSome with _ | s₁
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

theorem simChallCDF_eval (Δ qep : ℕ) {Γ}
    (s : Expr OO Γ mirrorTy)
    (arg : Expr OO Γ
      (.prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .coins))))))
    (ρ : Env Γ) (st : Thm1.Mirror Msg C) (P : Party) (m₀ m₁ : Msg) (r : Option Coins)
    (hs : s.eval ρ = mirrorEnc st) (harg : arg.eval ρ = (partyEnc P, m₀, m₁, r)) :
    (simChallCDF (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
      (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
      Δ qep s arg).eval ρ =
      Prod.map id mirrorEnc <$>
        ((DeliverForge.simChallDF (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          Δ qep (P, m₀, m₁, r)).run st) := by
  unfold simChallCDF DeliverForge.simChallDF
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
      (isSomeE (.snd (.snd (.snd (.snd .v0)))))).eval ρ₁ =
      (st.epMgmt Δ qep P r.isSome).map mirrorEnc := by
    rw [mEpMgmtE_eval Δ qep (.fst .v0) (.fst (.snd .v0)) (isSomeE (.snd (.snd (.snd (.snd .v0)))))
      ρ₁ st P rfl rfl]
    simp [ρ₁, isSomeE_eval, Expr.eval, Expr.v0]
  rw [hep]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rcases st.epMgmt Δ qep P r.isSome with _ | s₁
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
              (.snd (.snd (.snd (.snd .v1))))))).eval ρ₂ =
          DeliverForge.transmitQueryDF (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
            P (if st.b then m₁ else m₀) r := by
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

theorem simDeliverCDF_eval_trunc [DecidableEq C] (K : ℕ) {Γ}
    (s : Expr OO Γ mirrorTy) (arg : Expr OO Γ (.prod .bool (.base .ct)))
    (ρ : Env Γ) (st : Thm1.Mirror Msg C) (P : Party) (c : C)
    (heqCt : eqCt = (· == ·))
    (hTrans : st.trans.length ≤ K) (hChall : st.chall.length ≤ K)
    (hs : s.eval ρ = mirrorEnc st) (harg : arg.eval ρ = (partyEnc P, c)) :
    (simDeliverCDF (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
      (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
      K s arg).eval ρ =
      (do
        let res ← DeliverForge.deliverQueryDF
          (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort) (Coins := Coins) P c
        match res, st.inTransit P.other c with
        | some (.accepted t' i' m), some r =>
          pure (some (.inr (t', i', if st.chall.contains r.pos then none else m)),
            mirrorEnc ({ st with comp := st.comp.take K }.accept P () r.pos))
        | _, _ => pure (res.map smRrEnc, mirrorEnc st)) := by
  unfold simDeliverCDF
  rw [Comp.eval_bind_ret]
  have h0 : (Expr.pair s arg).eval ρ = (mirrorEnc st, partyEnc P, c) := by
    simp [Expr.eval, hs, harg]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := (.prod mirrorTy (.prod .bool (.base .ct)) : Ty S))
    (mirrorEnc st, partyEnc P, c) ρ
  have hdl : (Comp.query (I := SIfaceDF) SMTagDF.dl (.snd (Expr.v0 (O := OO)))).eval ρ₁ =
      Option.map smRrEnc <$>
        DeliverForge.deliverQueryDF (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          (Coins := Coins) P c := by
    rw [query_dlDF_eval]
    simp [ρ₁, partyDec_partyEnc, Expr.eval, Expr.v0]
  simp only [Comp.eval_bind, hdl, bind_map_left]
  refine bind_congr fun res => ?_
  rcases res with _ | rr
  · simp [ρ₁, Comp.eval, Expr.eval, Expr.v0, Expr.v1]
  · simp only [Option.map_some]
    rw [Comp.eval_caseOpt_v0_some]
    rcases rr with _ | ⟨t', i', m⟩
    · simp [ρ₁, smRrEnc, Comp.eval, Expr.eval, Expr.v0, Expr.v3]
    · simp only [smRrEnc]
      rw [Comp.eval_caseSum_v0_inr]
      set ρ₂ := Env.cons
        (t := (.prod .nat (.prod .nat (.opt (.base .msg))) : Ty S)) (t', i', m)
        (Env.cons (t := smRrTy Key St St₂ Msg Coins RCoins C) (.inr (t', i', m))
          (Env.cons (t := (.opt (smRrTy Key St St₂ Msg Coins RCoins C) : Ty S))
            (some (.inr (t', i', m))) ρ₁))
      rw [Comp.eval_caseOpt]
      have htr : (mInTransitE K (.fst (Expr.v3 (O := OO)))
          (otherE (.fst (.snd .v3))) (.snd (.snd .v3))).eval ρ₂ =
          (st.inTransit P.other c).map recEnc := by
        refine mInTransitE_eval K (.fst .v3) (otherE (.fst (.snd .v3))) (.snd (.snd .v3))
          ρ₂ st P.other heqCt hTrans rfl ?_
        simp [ρ₂, ρ₁, otherE, partyEnc_other, Expr.eval, Expr.v3]
      rw [htr]
      rcases st.inTransit P.other c with _ | r
      · simp [ρ₂, ρ₁, Expr.eval, Expr.v0, Expr.v3]
      · simp only [Option.map_some, Comp.eval_ret]
        set ρ₃ := Env.cons (t := recTy) (recEnc r) ρ₂
        have hch : (mChallContainsE K (.fst (Expr.v4 (O := OO))) (recPos .v0)).eval ρ₃ =
            st.chall.contains r.pos :=
          mChallContainsE_eval K (.fst .v4) (recPos .v0) ρ₃ st r.pos hChall rfl rfl
        have hacc : (mAcceptE K (.fst (Expr.v4 (O := OO))) (.fst (.snd .v4))
            (recPos .v0)).eval ρ₃ =
            mirrorEnc ({ st with comp := st.comp.take K }.accept P () r.pos) :=
          mAcceptE_eval_trunc K (.fst .v4) (.fst (.snd .v4)) (recPos .v0) ρ₃ st P r.pos
            hTrans hChall rfl rfl rfl
        simp only [Expr.eval, hch, hacc]
        rfl

theorem simInjectCDF_eval_trunc (K : ℕ) {Γ}
    (s : Expr OO Γ mirrorTy) (arg : Expr OO Γ (.prod .bool (.base .ct)))
    (ρ : Env Γ) (st : Thm1.Mirror Msg C) (P : Party) (c : C)
    (hTrans : st.trans.length ≤ K) (hChall : st.chall.length ≤ K)
    (hs : s.eval ρ = mirrorEnc st) (harg : arg.eval ρ = (partyEnc P, c)) :
    (simInjectCDF (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
      (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
      K s arg).eval ρ =
      (do
        let res ← DeliverForge.injectQueryDF
          (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort) (Coins := Coins) P c
        match res with
        | some (.accepted t' i' m) =>
          pure (some (.inr (t', i', m)),
            mirrorEnc ({ st with comp := st.comp.take K }.accept P () ⟨P.other, t', i'⟩))
        | _ => pure (res.map smRrEnc, mirrorEnc st)) := by
  unfold simInjectCDF
  rw [Comp.eval_bind_ret]
  have h0 : (Expr.pair s arg).eval ρ = (mirrorEnc st, partyEnc P, c) := by
    simp [Expr.eval, hs, harg]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := (.prod mirrorTy (.prod .bool (.base .ct)) : Ty S))
    (mirrorEnc st, partyEnc P, c) ρ
  have hij : (Comp.query (I := SIfaceDF) SMTagDF.ij (.snd (Expr.v0 (O := OO)))).eval ρ₁ =
      Option.map smRrEnc <$>
        DeliverForge.injectQueryDF (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          (Coins := Coins) P c := by
    rw [query_ijDF_eval]
    simp [ρ₁, partyDec_partyEnc, Expr.eval, Expr.v0]
  simp only [Comp.eval_bind, hij, bind_map_left]
  refine bind_congr fun res => ?_
  rcases res with _ | rr
  · simp [ρ₁, Comp.eval, Expr.eval, Expr.v0, Expr.v1]
  · simp only [Option.map_some]
    rw [Comp.eval_caseOpt_v0_some]
    rcases rr with _ | ⟨t', i', m⟩
    · simp [ρ₁, smRrEnc, Comp.eval, Expr.eval, Expr.v0, Expr.v3]
    · simp only [smRrEnc]
      rw [Comp.eval_caseSum_v0_inr, Comp.eval_ret]
      set ρ₂ := Env.cons
        (t := (.prod .nat (.prod .nat (.opt (.base .msg))) : Ty S)) (t', i', m)
        (Env.cons (t := smRrTy Key St St₂ Msg Coins RCoins C) (.inr (t', i', m))
          (Env.cons (t := (.opt (smRrTy Key St St₂ Msg Coins RCoins C) : Ty S))
            (some (.inr (t', i', m))) ρ₁))
      have hpos : (Expr.pair (otherE (.fst (.snd (Expr.v3 (O := OO)))))
          (.pair (.fst .v0) (.fst (.snd .v0)))).eval ρ₂ =
          posEnc ⟨P.other, t', i'⟩ := by
        simp [ρ₂, ρ₁, otherE, posEnc, partyEnc_other, Expr.eval, Expr.v0, Expr.v3]
      have hacc : (mAcceptE K (.fst (Expr.v3 (O := OO))) (.fst (.snd .v3))
          (.pair (otherE (.fst (.snd .v3))) (.pair (.fst .v0) (.fst (.snd .v0))))).eval ρ₂ =
          mirrorEnc ({ st with comp := st.comp.take K }.accept P () ⟨P.other, t', i'⟩) :=
        mAcceptE_eval_trunc K (.fst .v3) (.fst (.snd .v3)) _ ρ₂ st P ⟨P.other, t', i'⟩
          hTrans hChall rfl rfl hpos
      simp only [Expr.eval, hacc]
      rfl

theorem simCorrCDF_eval (K : ℕ) {Γ}
    (s : Expr OO Γ mirrorTy) (p : Expr OO Γ .bool)
    (ρ : Env Γ) (st : Thm1.Mirror Msg C) (P : Party)
    (hTrans : st.trans.length ≤ K)
    (hs : s.eval ρ = mirrorEnc st) (hp : p.eval ρ = partyEnc P) :
    (simCorrCDF (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
      (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
      K s p).eval ρ =
      Prod.map id mirrorEnc <$>
        ((DeliverForge.simCorrDF (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          (Msg := Msg) (Coins := Coins) (C := C) P).run st) := by
  unfold simCorrCDF DeliverForge.simCorrDF
  rw [Comp.eval_bind_ret]
  have h0 : (Expr.pair s p).eval ρ = (mirrorEnc st, partyEnc P) := by
    simp [Expr.eval, hs, hp]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := (.prod mirrorTy .bool : Ty S)) (mirrorEnc st, partyEnc P) ρ
  have hcr : (Comp.query (I := SIfaceDF) SMTagDF.cr (.snd (Expr.v0 (O := OO)))).eval ρ₁ =
      DeliverForge.corrQueryDF (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
        (Msg := Msg) (Coins := Coins) (C := C) P := by
    rw [query_crDF_eval]
    simp [ρ₁, partyDec_partyEnc, Expr.eval, Expr.v0]
  simp only [Comp.eval_bind, hcr, StateT.run_bind, StateT.run_get, stateT_lift_run,
    bind_assoc, pure_bind, map_bind]
  refine bind_congr fun res => ?_
  rcases res with _ | stP
  · simp [ρ₁, Comp.eval, isSomeE, Expr.eval, Expr.v0, Expr.v1, StateT.run_pure]
  · simp only [Comp.eval_ite, isSomeE_eval, Expr.eval, Expr.v0, Env.get_cons_zero,
      Option.isSome_some, ↓reduceIte, Comp.eval_ret, StateT.run_bind, StateT.run_set,
      StateT.run_pure, pure_bind, map_pure, Prod.map]
    congr 2
    exact mAfterCorrE_eval K (.fst (Expr.v1 (O := OO))) (.snd .v1)
      (Env.cons (t := (.opt (.base stSort) : Ty S)) (some stP) ρ₁) st P hTrans rfl rfl

theorem simDeliverForgeCDF_eval_trunc (K : ℕ) {Γ}
    (s : Expr OO Γ mirrorTy)
    (arg : Expr OO Γ (.prod .bool (.prod (.base .ct) (.base .ct))))
    (ρ : Env Γ) (st : Thm1.Mirror Msg C) (P : Party) (c c' : C)
    (hTrans : st.trans.length ≤ K) (hChall : st.chall.length ≤ K)
    (hs : s.eval ρ = mirrorEnc st) (harg : arg.eval ρ = (partyEnc P, c, c')) :
    (simDeliverForgeCDF (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
      (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
      K s arg).eval ρ =
      (do
        let res ← DeliverForge.deliverForgeQuery
          (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort) (Coins := Coins) P c c'
        match res with
        | some (.accepted t' i' m) =>
          pure (some (.inr (t', i', m)),
            mirrorEnc ({ st with comp := st.comp.take K }.accept P () ⟨P.other, t', i'⟩))
        | _ => pure (res.map smRrEnc, mirrorEnc st)) := by
  unfold simDeliverForgeCDF
  rw [Comp.eval_bind_ret]
  have h0 : (Expr.pair s arg).eval ρ = (mirrorEnc st, partyEnc P, c, c') := by
    simp [Expr.eval, hs, harg]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := (.prod mirrorTy (.prod .bool (.prod (.base .ct) (.base .ct))) : Ty S))
    (mirrorEnc st, partyEnc P, c, c') ρ
  have hdf : (Comp.query (I := SIfaceDF) SMTagDF.df (.snd (Expr.v0 (O := OO)))).eval ρ₁ =
      Option.map smRrEnc <$>
        DeliverForge.deliverForgeQuery (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          (Coins := Coins) P c c' := by
    rw [query_dfDF_eval]
    simp [ρ₁, partyDec_partyEnc, Expr.eval, Expr.v0]
  simp only [Comp.eval_bind, hdf, bind_map_left]
  refine bind_congr fun res => ?_
  rcases res with _ | rr
  · simp [ρ₁, Comp.eval, Expr.eval, Expr.v0, Expr.v1]
  · simp only [Option.map_some]
    rw [Comp.eval_caseOpt_v0_some]
    rcases rr with _ | ⟨t', i', m⟩
    · simp [ρ₁, smRrEnc, Comp.eval, Expr.eval, Expr.v0, Expr.v3]
    · simp only [smRrEnc]
      rw [Comp.eval_caseSum_v0_inr, Comp.eval_ret]
      set ρ₂ := Env.cons
        (t := (.prod .nat (.prod .nat (.opt (.base .msg))) : Ty S)) (t', i', m)
        (Env.cons (t := smRrTy Key St St₂ Msg Coins RCoins C) (.inr (t', i', m))
          (Env.cons (t := (.opt (smRrTy Key St St₂ Msg Coins RCoins C) : Ty S))
            (some (.inr (t', i', m))) ρ₁))
      have hpos : (Expr.pair (otherE (.fst (.snd (Expr.v3 (O := OO)))))
          (.pair (.fst .v0) (.fst (.snd .v0)))).eval ρ₂ =
          posEnc ⟨P.other, t', i'⟩ := by
        simp [ρ₂, ρ₁, otherE, posEnc, partyEnc_other, Expr.eval, Expr.v0, Expr.v3]
      have hacc : (mAcceptE K (.fst (Expr.v3 (O := OO))) (.fst (.snd .v3))
          (.pair (otherE (.fst (.snd .v3))) (.pair (.fst .v0) (.fst (.snd .v0))))).eval ρ₂ =
          mirrorEnc ({ st with comp := st.comp.take K }.accept P () ⟨P.other, t', i'⟩) :=
        mAcceptE_eval_trunc K (.fst .v3) (.fst (.snd .v3)) _ ρ₂ st P ⟨P.other, t', i'⟩
          hTrans hChall rfl rfl hpos
      simp only [Expr.eval, hacc]
      rfl

theorem handlerImpl_simHandleCDF_tr (K Δ qep : ℕ)
    (st : Thm1.Mirror Msg C) (P : Party) (m : Msg) (r : Option Coins) :
    ((handlerImpl (C := SCodecDF)
      (simHandleCDF (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
        (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
        (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
        (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
        K Δ qep)
      (.inr (.inl (.inl (.inl (.inl (.inl (P, m, r)))))))).run (mirrorEnc st)) =
      Prod.map id mirrorEnc <$>
        ((DeliverForge.simTransmitDF (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          Δ qep (P, m, r)).run st) := by
  unfold handlerImpl simHandleCDF smCodecDF smCodec
  simp only [StateT.run_mk, Comp.eval, Expr.eval, Expr.v0, Expr.v1,
    Env.get_cons_zero, Env.get_cons_succ, bind_assoc, pure_bind]
  rw [simTransmitCDF_eval Δ qep .v5 (.var .zero) _ st P m r rfl rfl]
  simp

theorem handlerImpl_simHandleCDF_ch (K Δ qep : ℕ)
    (st : Thm1.Mirror Msg C) (P : Party) (m₀ m₁ : Msg) (r : Option Coins) :
    ((handlerImpl (C := SCodecDF)
      (simHandleCDF (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
        (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
        (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
        (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
        K Δ qep)
      (.inr (.inl (.inl (.inl (.inl (.inr (P, m₀, m₁, r)))))))).run (mirrorEnc st)) =
      Prod.map id mirrorEnc <$>
        ((DeliverForge.simChallDF (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          Δ qep (P, m₀, m₁, r)).run st) := by
  unfold handlerImpl simHandleCDF smCodecDF smCodec
  simp only [StateT.run_mk, Comp.eval, Expr.eval, Expr.v0, Expr.v1,
    Env.get_cons_zero, Env.get_cons_succ, bind_assoc, pure_bind]
  rw [simChallCDF_eval Δ qep .v5 (.var .zero) _ st P m₀ m₁ r rfl rfl]
  simp

theorem handlerImpl_simHandleCDF_dl_trunc [DecidableEq C] (K Δ qep : ℕ)
    (heqCt : eqCt = (· == ·))
    (st : Thm1.Mirror Msg C) (P : Party) (c : C)
    (hTrans : st.trans.length ≤ K) (hChall : st.chall.length ≤ K) :
    ((handlerImpl (C := SCodecDF)
      (simHandleCDF (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
        (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
        (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
        (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
        K Δ qep)
      (.inr (.inl (.inl (.inl (.inr (P, c))))))).run (mirrorEnc st)) =
      (do
        let res ← DeliverForge.deliverQueryDF
          (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort) (Coins := Coins) P c
        match res, st.inTransit P.other c with
        | some (.accepted t' i' m'), some r =>
          pure (some (.accepted t' i' (if st.chall.contains r.pos then none else m')),
            mirrorEnc ({ st with comp := st.comp.take K }.accept P () r.pos))
        | _, _ => pure (res, mirrorEnc st)) := by
  unfold handlerImpl simHandleCDF smCodecDF smCodec
  simp only [StateT.run_mk, Comp.eval, Expr.eval, Expr.v0, Expr.v1,
    Env.get_cons_zero, Env.get_cons_succ, bind_assoc, pure_bind]
  rw [simDeliverCDF_eval_trunc K .v4 (.var .zero) _ st P c heqCt hTrans hChall rfl rfl]
  simp only [bind_assoc]
  refine bind_congr fun res => ?_
  rcases res with _ | (_ | ⟨t', i', m'⟩) <;>
  rcases st.inTransit P.other c with _ | r <;>
  simp [smRrEnc, smRrDec]

theorem handlerImpl_simHandleCDF_ij_trunc (K Δ qep : ℕ)
    (st : Thm1.Mirror Msg C) (P : Party) (c : C)
    (hTrans : st.trans.length ≤ K) (hChall : st.chall.length ≤ K) :
    ((handlerImpl (C := SCodecDF)
      (simHandleCDF (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
        (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
        (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
        (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
        K Δ qep)
      (.inr (.inl (.inl (.inr (P, c)))))).run (mirrorEnc st)) =
      (do
        let res ← DeliverForge.injectQueryDF
          (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort) (Coins := Coins) P c
        match res with
        | some (.accepted t' i' m') =>
          pure (some (.accepted t' i' m'),
            mirrorEnc ({ st with comp := st.comp.take K }.accept P () ⟨P.other, t', i'⟩))
        | _ => pure (res, mirrorEnc st)) := by
  unfold handlerImpl simHandleCDF smCodecDF smCodec
  simp only [StateT.run_mk, Comp.eval, Expr.eval, Expr.v0, Expr.v1,
    Env.get_cons_zero, Env.get_cons_succ, bind_assoc, pure_bind]
  rw [simInjectCDF_eval_trunc K .v3 (.var .zero) _ st P c hTrans hChall rfl rfl]
  simp only [bind_assoc]
  refine bind_congr fun res => ?_
  rcases res with _ | (_ | ⟨t', i', m'⟩) <;>
  simp [smRrEnc, smRrDec]

theorem handlerImpl_simHandleCDF_cr (K Δ qep : ℕ)
    (st : Thm1.Mirror Msg C) (P : Party)
    (hTrans : st.trans.length ≤ K) :
    ((handlerImpl (C := SCodecDF)
      (simHandleCDF (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
        (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
        (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
        (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
        K Δ qep)
      (.inr (.inl (.inr P)))).run (mirrorEnc st)) =
      Prod.map id mirrorEnc <$>
        ((DeliverForge.simCorrDF (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          (Msg := Msg) (Coins := Coins) (C := C) P).run st) := by
  unfold handlerImpl simHandleCDF smCodecDF smCodec
  simp only [StateT.run_mk, Comp.eval, Expr.eval, Expr.v0, Expr.v1,
    Env.get_cons_zero, Env.get_cons_succ, bind_assoc, pure_bind]
  rw [simCorrCDF_eval K .v2 (.var .zero) _ st P hTrans rfl rfl]
  simp

theorem handlerImpl_simHandleCDF_df_trunc (K Δ qep : ℕ)
    (st : Thm1.Mirror Msg C) (P : Party) (c c' : C)
    (hTrans : st.trans.length ≤ K) (hChall : st.chall.length ≤ K) :
    ((handlerImpl (C := SCodecDF)
      (simHandleCDF (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
        (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
        (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
        (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
        K Δ qep)
      (.inr (.inr (P, c, c')))).run (mirrorEnc st)) =
      (do
        let res ← DeliverForge.deliverForgeQuery
          (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort) (Coins := Coins) P c c'
        match res with
        | some (.accepted t' i' m') =>
          pure (some (.accepted t' i' m'),
            mirrorEnc ({ st with comp := st.comp.take K }.accept P () ⟨P.other, t', i'⟩))
        | _ => pure (res, mirrorEnc st)) := by
  unfold handlerImpl simHandleCDF smCodecDF
  simp only [StateT.run_mk, Comp.eval, Expr.eval, Expr.v0, Expr.v1,
    Env.get_cons_zero, Env.get_cons_succ, bind_assoc, pure_bind]
  rw [simDeliverForgeCDF_eval_trunc K (.var (.succ .zero)) (.var .zero)
    _ st P c c' hTrans hChall rfl rfl]
  simp only [bind_assoc]
  refine bind_congr fun res => ?_
  rcases res with _ | (_ | ⟨t', i', m'⟩) <;>
  simp [smRrEnc, smRrDec]

theorem simImplDF_clearComp [DecidableEq C] (Δ qep : ℕ)
    (t : (SM.specDF (SMSort.den Key St St₂ Msg Coins RCoins C stSort) Msg Coins C).Domain)
    (st : Thm1.Mirror Msg C) :
    Prod.map id mirrorClearComp <$>
      ((DeliverForge.simImplDF (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
        (Msg := Msg) (Coins := Coins) (C := C) Δ qep (.inr t)).run st) =
    Prod.map id mirrorClearComp <$>
      ((DeliverForge.simImplDF (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
        (Msg := Msg) (Coins := Coins) (C := C) Δ qep (.inr t)).run (mirrorClearComp st)) := by
  rcases t with (((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩)
  · simp only [simImplDF_tr, DeliverForge.simTransmitDF,
      StateT.run_bind, StateT.run_get, stateT_lift_run, bind_assoc, pure_bind, map_bind,
      mirrorClearComp_epMgmt]
    refine bind_congr fun res => ?_
    rcases res with _ | c <;> rcases st.epMgmt Δ qep P r.isSome with _ | s₁ <;>
    simp [StateT.run_pure, StateT.run_set, Prod.map]
  · simp only [simImplDF_ch, DeliverForge.simChallDF,
      StateT.run_bind, StateT.run_get, pure_bind, mirrorClearComp_epMgmt]
    rcases st.epMgmt Δ qep P r.isSome with _ | s₁
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
  · simp only [simImplDF_dl, DeliverForge.simDeliverDF,
      StateT.run_bind, StateT.run_get, stateT_lift_run, bind_assoc, pure_bind, map_bind,
      mirrorClearComp_inTransit, mirrorClearComp_chall]
    refine bind_congr fun res => ?_
    rcases res with _ | (_ | ⟨t', i', m⟩) <;> rcases st.inTransit P.other c with _ | r <;>
    simp [StateT.run_pure, StateT.run_set, Prod.map]
  · simp only [simImplDF_ij, DeliverForge.simInjectDF,
      StateT.run_bind, StateT.run_get, stateT_lift_run, bind_assoc, pure_bind, map_bind]
    refine bind_congr fun res => ?_
    rcases res with _ | (_ | ⟨t', i', m⟩) <;>
    simp [StateT.run_pure, StateT.run_set, Prod.map]
  · simp only [simImplDF_cr, DeliverForge.simCorrDF,
      StateT.run_bind, StateT.run_get, stateT_lift_run, bind_assoc, pure_bind, map_bind]
    refine bind_congr fun res => ?_
    rcases res with _ | stP <;>
    simp [StateT.run_pure, StateT.run_set, Prod.map]
  · simp only [simImplDF_df, DeliverForge.simDeliverForgeDF,
      StateT.run_bind, StateT.run_get, stateT_lift_run, bind_assoc, pure_bind, map_bind]
    refine bind_congr fun res => ?_
    rcases res with _ | (_ | ⟨t', i', m⟩) <;>
    simp [StateT.run_pure, StateT.run_set, Prod.map]

theorem challSimDFProg_step_clearComp [DecidableEq C] (K Δ qep m : ℕ)
    (heqCt : eqCt = (· == ·))
    (t : (SM.specDF (SMSort.den Key St St₂ Msg Coins RCoins C stSort) Msg Coins C).Domain)
    (v : (@mirrorTy Key St St₂ Msg Coins RCoins C).denote)
    (hInv : MirrorBoundInv K (m + 1) v) :
    (Prod.map id (mirrorClearComp ∘ mirrorDec) <$>
      (((challSimDFProg (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
           (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
           (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
           (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
           K Δ qep).impl (.inr t)).run v)) =
      ((clearCompImpl (DeliverForge.simImplDF
          (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          (Msg := Msg) (Coins := Coins) (C := C) Δ qep) (.inr t)).run
            (mirrorClearComp (mirrorDec v))) ∧
    ∀ r ∈ support (((challSimDFProg (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
        (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
        (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
        (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
        K Δ qep).impl (.inr t)).run v), MirrorBoundInv K m r.2 := by
  set st := mirrorDec v
  have hv : v = mirrorEnc st := (mirrorEnc_mirrorDec v).symm
  have hTrans : st.trans.length ≤ K := by
    have : st.trans.length + (m + 1) ≤ K := hInv.1; omega
  have hChall : st.chall.length ≤ K := by
    have : st.chall.length + (m + 1) ≤ K := hInv.2; omega
  have hInv0 : MirrorBoundInv (Key := Key) (St := St) (St₂ := St₂)
      (Coins := Coins) (RCoins := RCoins) K m (mirrorEnc st) := by
    rw [← hv]; exact hInv.mono (Nat.le_succ m)
  rw [hv, clearCompImpl, StateT.run_mk, ← simImplDF_clearComp Δ qep t st]
  rcases t with (((((⟨P, msg, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩)
  · have hrun : (((challSimDFProg (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
        (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
        (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
        (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
        K Δ qep).impl (.inr (.inl (.inl (.inl (.inl (.inl (P, msg, r)))))))).run (mirrorEnc st)) =
      Prod.map id mirrorEnc <$>
        ((DeliverForge.simTransmitDF (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          Δ qep (P, msg, r)).run st) :=
      handlerImpl_simHandleCDF_tr K Δ qep st P msg r
    rw [hrun]
    refine ⟨by rw [Functor.map_map]; congr 1; funext ⟨a, s⟩; simp [Prod.map], ?_⟩
    intro x hx
    simp only [DeliverForge.simTransmitDF, StateT.run_bind, StateT.run_get, stateT_lift_run,
      bind_assoc, pure_bind, map_bind, mem_support_bind_iff] at hx
    obtain ⟨res, -, hx⟩ := hx
    rcases res with _ | c
    · simp only [StateT.run_pure, map_pure, Prod.map, support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact hInv0
    · rcases hep : st.epMgmt Δ qep P r.isSome with _ | s₁
      · simp only [hep, StateT.run_pure, map_pure, Prod.map, support_pure,
          Set.mem_singleton_iff] at hx
        subst hx; exact hInv0
      · simp only [hep] at hx
        subst hx; exact mirrorBoundInv_record _ hInv hep
  · have hrun : (((challSimDFProg (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
        (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
        (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
        (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
        K Δ qep).impl (.inr (.inl (.inl (.inl (.inl (.inr (P, m₀, m₁, r)))))))).run
          (mirrorEnc st)) =
      Prod.map id mirrorEnc <$>
        ((DeliverForge.simChallDF (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          Δ qep (P, m₀, m₁, r)).run st) :=
      handlerImpl_simHandleCDF_ch K Δ qep st P m₀ m₁ r
    rw [hrun]
    refine ⟨by rw [Functor.map_map]; congr 1; funext ⟨a, s⟩; simp [Prod.map], ?_⟩
    intro x hx
    simp only [DeliverForge.simChallDF, StateT.run_bind, StateT.run_get, pure_bind] at hx
    rcases hep : st.epMgmt Δ qep P r.isSome with _ | s₁
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
  · have hrun : (((challSimDFProg (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
        (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
        (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
        (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
        K Δ qep).impl (.inr (.inl (.inl (.inl (.inr (P, c))))))).run (mirrorEnc st)) =
      (do
        let res ← DeliverForge.deliverQueryDF
          (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort) (Coins := Coins) P c
        match res, st.inTransit P.other c with
        | some (.accepted t' i' m'), some r =>
          pure (some (.accepted t' i' (if st.chall.contains r.pos then none else m')),
            mirrorEnc ({ st with comp := st.comp.take K }.accept P () r.pos))
        | _, _ => pure (res, mirrorEnc st)) :=
      handlerImpl_simHandleCDF_dl_trunc K Δ qep heqCt st P c hTrans hChall
    rw [hrun]
    refine ⟨?_, ?_⟩
    · simp only [simImplDF_dl, DeliverForge.simDeliverDF,
        StateT.run_bind, StateT.run_get, stateT_lift_run, bind_assoc, pure_bind, map_bind]
      refine bind_congr fun res => ?_
      rcases res with _ | (_ | ⟨t', i', m'⟩) <;>
      rcases st.inTransit P.other c with _ | r <;>
      simp [StateT.run_pure, StateT.run_set, Prod.map]
    · intro x hx
      rw [mem_support_bind_iff] at hx
      obtain ⟨res, -, hx⟩ := hx
      rcases res with _ | (_ | ⟨t', i', m'⟩)
      · simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx; exact hInv0
      · simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx; exact hInv0
      · rcases htr : st.inTransit P.other c with _ | r
        · simp only [htr, support_pure, Set.mem_singleton_iff] at hx; subst hx; exact hInv0
        · simp only [htr, support_pure, Set.mem_singleton_iff] at hx
          subst hx; exact mirrorBoundInv_accept_take P r.pos hInv
  · have hrun : (((challSimDFProg (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
        (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
        (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
        (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
        K Δ qep).impl (.inr (.inl (.inl (.inr (P, c)))))).run (mirrorEnc st)) =
      (do
        let res ← DeliverForge.injectQueryDF
          (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort) (Coins := Coins) P c
        match res with
        | some (.accepted t' i' m') =>
          pure (some (.accepted t' i' m'),
            mirrorEnc ({ st with comp := st.comp.take K }.accept P () ⟨P.other, t', i'⟩))
        | _ => pure (res, mirrorEnc st)) :=
      handlerImpl_simHandleCDF_ij_trunc K Δ qep st P c hTrans hChall
    rw [hrun]
    refine ⟨?_, ?_⟩
    · simp only [simImplDF_ij, DeliverForge.simInjectDF,
        StateT.run_bind, StateT.run_get, stateT_lift_run, bind_assoc, pure_bind, map_bind]
      refine bind_congr fun res => ?_
      rcases res with _ | (_ | ⟨t', i', m'⟩) <;>
      simp [StateT.run_pure, StateT.run_set, Prod.map]
    · intro x hx
      rw [mem_support_bind_iff] at hx
      obtain ⟨res, -, hx⟩ := hx
      rcases res with _ | (_ | ⟨t', i', m'⟩)
      all_goals
        simp only [support_pure, Set.mem_singleton_iff] at hx
        subst hx
        first | exact hInv0 | exact mirrorBoundInv_accept_take P ⟨P.other, t', i'⟩ hInv
  · have hrun : (((challSimDFProg (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
        (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
        (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
        (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
        K Δ qep).impl (.inr (.inl (.inr P)))).run (mirrorEnc st)) =
      Prod.map id mirrorEnc <$>
        ((DeliverForge.simCorrDF (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          (Msg := Msg) (Coins := Coins) (C := C) P).run st) :=
      handlerImpl_simHandleCDF_cr K Δ qep st P hTrans
    rw [hrun]
    refine ⟨by rw [Functor.map_map]; congr 1; funext ⟨a, s⟩; simp [Prod.map], ?_⟩
    intro x hx
    simp only [DeliverForge.simCorrDF, StateT.run_bind, StateT.run_get, stateT_lift_run,
      bind_assoc, pure_bind, map_bind, mem_support_bind_iff] at hx
    obtain ⟨res, -, hx⟩ := hx
    rcases res with _ | stP
    · simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, map_pure,
        Prod.map, support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact hInv0
    · simp only [Option.isSome_some, ↓reduceIte] at hx
      subst hx; exact mirrorBoundInv_afterCorr P hInv
  · have hrun : (((challSimDFProg (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
        (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
        (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
        (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
        K Δ qep).impl (.inr (.inr (P, c, c')))).run (mirrorEnc st)) =
      (do
        let res ← DeliverForge.deliverForgeQuery
          (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort) (Coins := Coins) P c c'
        match res with
        | some (.accepted t' i' m') =>
          pure (some (.accepted t' i' m'),
            mirrorEnc ({ st with comp := st.comp.take K }.accept P () ⟨P.other, t', i'⟩))
        | _ => pure (res, mirrorEnc st)) :=
      handlerImpl_simHandleCDF_df_trunc K Δ qep st P c c' hTrans hChall
    rw [hrun]
    refine ⟨?_, ?_⟩
    · simp only [simImplDF_df, DeliverForge.simDeliverForgeDF,
        StateT.run_bind, StateT.run_get, stateT_lift_run, bind_assoc, pure_bind, map_bind]
      refine bind_congr fun res => ?_
      rcases res with _ | (_ | ⟨t', i', m'⟩) <;>
      simp [StateT.run_pure, StateT.run_set, Prod.map]
    · intro x hx
      rw [mem_support_bind_iff] at hx
      obtain ⟨res, -, hx⟩ := hx
      rcases res with _ | (_ | ⟨t', i', m'⟩)
      all_goals
        simp only [support_pure, Set.mem_singleton_iff] at hx
        subst hx
        first | exact hInv0 | exact mirrorBoundInv_accept_take P ⟨P.other, t', i'⟩ hInv

theorem simInitCDF_eval (ρ : Env [.unit]) :
    (simInitCDF (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
      (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)).eval ρ =
      (do
        let b ← (liftM ($ᵗ Bool : ProbComp Bool) :
          DeliverForge.AdversaryCompDF (SMSort.den Key St St₂ Msg Coins RCoins C stSort)
            Msg Coins C Bool)
        return ((), mirrorEnc ({ st := fun _ => (), b } : Thm1.Mirror Msg C))) := rfl

theorem makesAtMostQueriesDF_iff_isGameQuery
    (oa : DeliverForge.AdversaryDF (SMSort.den Key St St₂ Msg Coins RCoins C stSort) Msg Coins C)
    (q : ℕ) :
    DeliverForge.MakesAtMostQueriesDF oa q ↔
      oa.IsQueryBoundP
        (isGameQuery
          (G := SM.specDF (SMSort.den Key St St₂ Msg Coins RCoins C stSort) Msg Coins C))
        q :=
  isQueryBoundP_congr oa (by funext x; cases x <;> simp [isGameQuery]) q

@[simp] theorem simHandleCDF_queries (K Δ qep : ℕ) :
    (simHandleCDF (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
      (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
      K Δ qep).queries (fun _ => 1) (fun _ => 0) = 1 := by
  simp [simHandleCDF, simTransmitCDF, simChallCDF, simDeliverCDF, simInjectCDF, simCorrCDF,
    simDeliverForgeCDF, Comp.queries]

@[simp] theorem simInitCDF_queries :
    (simInitCDF (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
      (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)).queries
      (fun _ => 1) (fun _ => 0) = 0 := by
  simp [simInitCDF, Comp.queries]

@[simp] theorem challSimDFProg_totalQueries (K Δ qep q : ℕ) :
    (challSimDFProg (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
      (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
      K Δ qep).totalQueries (fun _ => 1) (fun _ => 0) q = q := by
  simp [CostedReduction.totalQueries, challSimDFProg, Comp.queries]

theorem simInitCDF_cost :
    (simInitCDF (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
      (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)).cost = 39 := by
  simp [simInitCDF, mMk, smIfaceDF, smSamplers, Comp.cost, Expr.cost, Expr.v0, bits]

theorem challSimDFProg_totalCost (K Δ qep q : ℕ) :
    (challSimDFProg (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
      (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
      K Δ qep).totalCost q =
      41 + q * ((simHandleCDF (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
        (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
        (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
        (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
        K Δ qep).cost + 7) := by
  simp only [CostedReduction.totalCost, challSimDFProg, simInitCDF_cost, smCodecDF, smIfaceDF, Comp.cost,
    Expr.cost, Expr.v1]
  rw [max_eq_right (by omega)]
  omega

end ChallSimDFProg

end CryptoGames.SM

/-! ## Engine dispatch -/

namespace CryptoGames.SM.Engine

open Construction CKA DeliverForge

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}
  {ckaInitA : KC → Γ}
  {ckaInitB : KC → Γ}
  {ckaSend : Γ → CCoins → Γ × T × I}
  {ckaReceive : Γ → T → Γ × I}
  {prngInit : KR → RSt}
  {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS}
  {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E}
  {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool}
  {eqI : I → I → Bool}
  {eqM : M → M → Bool}
  {eqE : E → E → Bool}
  {lam : I}
  {defaultE : E}

local notation "S" => ckaSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "OO" =>
  ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE
local notation "hdrTy" => ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrCtTy" => ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "psTy" => ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "rrTy" => ckaRrTy KC Γ CCoins T I KR RSt K SS RS M E

def hdrEqE {Γ'} (c₁ c₂ : Expr OO Γ' hdrCtTy) : Expr OO Γ' .bool :=
  rdslExpr =>
    letE (c₁, c₂) fun (a, b) =>
      (a.1.1 == b.1.1) && optTEqE a.1.2 b.1.2

theorem hdrEqE_eval [DecidableEq T] {Γ'}
    (c₁ c₂ : Expr OO Γ' hdrCtTy) (ρ : Env Γ')
    (heqT : eqT = (· == ·)) :
    (hdrEqE c₁ c₂).eval ρ = ((c₁.eval ρ).1 == (c₂.eval ρ).1) := by
  rcases h1 : c₁.eval ρ with ⟨⟨t₁, o₁⟩, e₁⟩
  rcases h2 : c₂.eval ρ with ⟨⟨t₂, o₂⟩, e₂⟩
  simp only [hdrEqE, Expr.eval, Expr.v0, Env.get_cons_zero, h1, h2]
  rw [optTEqE_eval _ _ _ heqT]
  simp only [Expr.eval, Env.get_cons_zero]
  by_cases ht : t₁ = t₂ <;> cases o₁ <;> cases o₂ <;> simp [ht, BEq.beq]

/-- Costed `DeliverForge.deliverForgeE` handler with list-scan bound `L`. -/
def deliverForgeEC
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : Ty S}
    (hk : HooksC OO I' γvT svT ssvT rsvT hsT)
    (L Δ qep : ℕ) (cfg : ConfigEC OO)
    {Γ'} (es : Expr OO Γ'
      (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO Γ' (.prod .bool (.prod hdrCtTy hdrCtTy))) :
    Comp OO I' Γ'
      (.prod (.opt rrTy)
        (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT)) :=
  rdsl do
    (es0, p0, c0, c'0) ← return (es, arg)
    let s0 := esG es0
    if orE (esAbort es0) (cGsWin s0) then
      return (none, es0)
    else
      match cInTransitE L s0 (otherE p0) c0 with
      | none => return (none, es0)
      | some r1 =>
        let bad1 :=
          orE (isSomeE (cInTransitE L s0 (otherE p0) c'0))
            (orE (cCompContainsE L s0 (cRecPos r1))
              (!(hdrEqE c0 c'0)))
        if bad1 then
          return (none, es0)
        else
          (vrRes, h') ← vRecvC hk (esH es0) s0 p0 (pGet (cGsSt s0) p0) c'0 none
          match vrRes with
          | none => return (none, esMk s0 h' true)
          | some optTup =>
            match optTup with
            | none => return (some (.inl ()), esSetH es0 h')
            | some (st', t', i', m') =>
              let es4' := esSetH es0 h'
              if orE (nat (qep + 1) < t') (!(t' == posEpoch (cRecPos r1))) then
                return (some (.inl ()), es4')
              else
                let pos := (otherE p0, t', i')
                if cTrivialE L Δ s0 pos then
                  (optAcc, es_acc) ← commitEC hk L es4' s0 p0 (pGet (cGsSt s0) p0) st' pos
                  match optAcc with
                  | none => return (none, es_acc)
                  | some s_acc =>
                    return (some (.inr (t', i', some m')), esSetG es_acc s_acc)
                else
                  let g4 := if cfg.injectFullE t' then cGsSetWin s0 true else s0
                  return (some (.inl ()), esSetG es4' g4)

/-- Six-oracle costed engine dispatcher for `DeliverForge.implEDF`. -/
def implECDF
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : Ty S}
    (hk : HooksC OO I' γvT svT ssvT rsvT hsT)
    (L Δ qep maxSkip : ℕ) (cfg : ConfigEC OO) (π : Policy)
    {Γ'} (es : Expr OO Γ'
      (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (q : Expr OO Γ' (ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E)) :
    Comp OO I' Γ'
      (.prod (ckaSMRDF KC Γ CCoins T I KR RSt K SS RS M E)
        (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT)) :=
  rdsl do
    (es0, q0) ← return (es, q)
    match q0 with
    | .inl qBase =>
      (r, es') ← implEC hk L Δ qep maxSkip cfg π es0 qBase
      return (.inl r, es')
    | .inr qDf =>
      (r, es') ← deliverForgeEC hk L Δ qep cfg es0 qDf
      return (.inr r, es')

theorem deliverForgeEC_eval {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S} {HS : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hsEncFn : HS → hsT.denote) (HBounded : HS → Prop) {HBoundedPost : HS → Prop}
    {VROk : rsvT.denote → Prop}
    (hkC : HooksC OO I' γvT svT ssvT rsvT hsT)
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins
      γvT.denote svT.denote ssvT.denote rsvT.denote)
    (hHk : HooksCAgrees hsEncFn HBounded (HBoundedPost := HBoundedPost) (VROk := VROk) hkC hk)
    (L Δ qep : ℕ) (cfgC : ConfigEC OO) (cfg : Config M)
    (hCfg : ConfigECAgrees cfgC cfg)
    (heqT : eqT = (· == ·))
    (heqE : eqE = (· == ·))
    {Γ'} (esE : Expr OO Γ'
      (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (argE : Expr OO Γ' (.prod .bool (.prod hdrCtTy hdrCtTy)))
    (ρ : Env Γ')
    (es : EState (VP γvT.denote T svT.denote ssvT.denote rsvT.denote) M (Header T × E) HS)
    (P : Party) (c c' : Header T × E)
    (hHB : HBounded es.h) (hBound : SMStateBoundedEngine L es.g)
    (hVR : ∀ t v, (es.g.st P).vR t = some v → VROk v)
    (hes : esE.eval ρ = esEnc vpTblEnc hsEncFn es)
    (harg : argE.eval ρ = (partyEnc P, c, c')) :
    (deliverForgeEC hkC L Δ qep cfgC esE argE).eval ρ =
      Prod.map (Option.map smRrEnc) (esEnc vpTblEnc hsEncFn) <$>
        (deliverForgeE hk Δ qep cfg (P, c, c')).run es := by
  unfold deliverForgeEC deliverForgeE abortE
  rw [eval_bind_ret]
  have h0 : (Expr.pair esE argE).eval ρ =
      (esEnc vpTblEnc hsEncFn es, partyEnc P, c, c') := by
    simp [Expr.eval, hes, harg]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := .prod (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT)
      (.prod .bool (.prod hdrCtTy hdrCtTy)))
    (esEnc vpTblEnc hsEncFn es, partyEnc P, c, c') ρ
  rw [eval_ite]
  have hab : (orE (esAbort (.fst (Expr.v0 (O := OO)))) (cGsWin (esG (.fst .v0)))).eval ρ₁ =
      (es.abort || es.g.win) := by
    simp [ρ₁, orE_eval, esAbort, cGsWin, esG, esEnc, cGsEnc, Expr.eval, Expr.v0]
  rw [hab]
  by_cases h1 : (es.abort || es.g.win)
  · simp only [StateT.run_bind, StateT.run_get, pure_bind, h1, ↓reduceIte,
      eval_ret, StateT.run_pure, map_pure, Prod.map]
    simp [ρ₁, Expr.eval, Expr.v0]
  · rw [StateT.run_bind, StateT.run_get, pure_bind]
    simp only [h1, Bool.false_eq_true, ↓reduceIte, eval_caseOpt]
    have hOther : (otherE (.fst (.snd (Expr.v0 (O := OO))))).eval ρ₁ = partyEnc P.other := by
      simp [ρ₁, otherE, partyEnc_other, Expr.eval, Expr.v0]
    have hInTr : (cInTransitE L (esG (.fst (Expr.v0 (O := OO))))
        (otherE (.fst (.snd .v0))) (.fst (.snd (.snd .v0)))).eval ρ₁ =
        (es.g.inTransit P.other c).map cRecEnc :=
      cInTransitE_eval vpTblEnc L (esG (.fst .v0)) (otherE (.fst (.snd .v0)))
        (.fst (.snd (.snd .v0))) ρ₁ es.g P.other heqT heqE hBound.trans_le rfl hOther
    rw [hInTr]
    rcases htr : es.g.inTransit P.other c with _ | r
    · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
    · simp only [Option.map_some]
      set ρ₂ := Env.cons (t := cRecTy) (cRecEnc r) ρ₁
      rw [eval_ite]
      have hOther2 : (otherE (.fst (.snd (Expr.v1 (O := OO))))).eval ρ₂ = partyEnc P.other := by
        simp [ρ₂, ρ₁, otherE, partyEnc_other, Expr.eval, Expr.v1]
      have hInTr' : (cInTransitE L (esG (.fst (Expr.v1 (O := OO))))
          (otherE (.fst (.snd .v1))) (.snd (.snd (.snd .v1)))).eval ρ₂ =
          (es.g.inTransit P.other c').map cRecEnc :=
        cInTransitE_eval vpTblEnc L (esG (.fst .v1)) (otherE (.fst (.snd .v1)))
          (.snd (.snd (.snd .v1))) ρ₂ es.g P.other heqT heqE hBound.trans_le rfl hOther2
      have hComp : (cCompContainsE L (esG (.fst (Expr.v1 (O := OO))))
          (cRecPos .v0)).eval ρ₂ = es.g.comp.contains r.pos :=
        cCompContainsE_eval vpTblEnc (O' := OO) L (esG (.fst .v1)) (cRecPos .v0)
          ρ₂ es.g r.pos hBound.comp_le rfl rfl
      have hHdr : (hdrEqE (.fst (.snd (.snd (Expr.v1 (O := OO)))))
          (.snd (.snd (.snd .v1)))).eval ρ₂ = (c.1 == c'.1) := by
        rw [hdrEqE_eval _ _ _ heqT]
        rfl
      have hBad1 : (orE (isSomeE (cInTransitE L (esG (.fst (Expr.v1 (O := OO))))
            (otherE (.fst (.snd .v1))) (.snd (.snd (.snd .v1)))))
          (orE (cCompContainsE L (esG (.fst .v1)) (cRecPos .v0))
            (.not (hdrEqE (.fst (.snd (.snd .v1))) (.snd (.snd (.snd .v1))))))).eval ρ₂ =
          ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos || c.1 != c'.1) := by
        simp only [orE_eval, isSomeE_eval, not_eval, hInTr', Option.isSome_map, hComp, hHdr, bne,
          Bool.or_assoc]
      rw [hBad1]
      by_cases hbad :
          ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos || c.1 != c'.1)
      · simp only [hbad, ↓reduceIte, eval_ret, StateT.run_pure, map_pure, Prod.map]
        simp [ρ₂, ρ₁, Expr.eval, Expr.v1]
      · simp only [hbad, Bool.false_eq_true, ↓reduceIte, eval_bind]
        have hStP : (pGet (cGsSt (esG (.fst (Expr.v1 (O := OO)))))
            (.fst (.snd .v1))).eval ρ₂ = vpTblEnc (es.g.st P) :=
          pGet_eval (cGsSt (esG (.fst .v1))) (.fst (.snd .v1)) ρ₂
            (fun Q => vpTblEnc (es.g.st Q)) P rfl rfl
        have hVRecv := vRecvC_eval hsEncFn HBounded hkC hk hHk
          (esH (.fst .v1)) (esG (.fst .v1)) (.fst (.snd .v1))
          (pGet (cGsSt (esG (.fst .v1))) (.fst (.snd .v1))) (.snd (.snd (.snd .v1))) .none
          ρ₂ es.h es.g P (es.g.st P) c' none hHB hVR rfl rfl rfl hStP rfl rfl
        rw [hVRecv, bind_map_left, run_liftH_bind, map_bind]
        refine OracleComp.bind_congr_of_forall_mem_support
          ((vRecv hk es.g P (es.g.st P) c' none).run es.h)
          fun ⟨vrRes, h'⟩ hvrMem => ?_
        have hHB' : HBoundedPost h' :=
          vRecv_bounded hsEncFn HBounded hkC hk hHk es.g P (es.g.st P) c' none es.h hHB
            (vrRes, h') hvrMem
        rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
        · simp [ρ₂, ρ₁, Comp.eval, StateT.run_modify,
            Prod.map, esMk, esG, esEnc, Expr.eval, Expr.v0, Expr.v2]
        · simp only [Prod.map, Option.map_some, Option.map_none,
            StateT.run_pure, map_pure]
          set ρ₃ := Env.cons
            (t := .opt (.prod (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)
              (.prod .nat (.prod .nat (.base .msg)))))
            none
            (Env.cons
              (t := .prod
                (.opt (.opt (.prod (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)
                  (.prod .nat (.prod .nat (.base .msg)))))) hsT)
              (some none, hsEncFn h') ρ₂)
          change (Comp.ret _).eval ρ₃ = _
          have hSetH := esSetH_eval vpTblEnc hsEncFn (O' := OO) (.fst .v3) (.snd .v1)
            ρ₃ es h' rfl rfl
          simp only [eval_ret, pair_eval, some_eval, inl_eval, hSetH]
          rfl
        · simp only [Prod.map, Option.map_some, id_eq]
          set ρ₄ := Env.cons
            (t := .prod (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)
              (.prod .nat (.prod .nat (.base .msg))))
            (vpTblEnc st', t', i', m')
            (Env.cons
              (t := .opt (.prod (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)
                (.prod .nat (.prod .nat (.base .msg)))))
              (some (vpTblEnc st', t', i', m'))
              (Env.cons
                (t := .prod
                  (.opt (.opt (.prod (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E
                    γvT svT ssvT rsvT)
                    (.prod .nat (.prod .nat (.base .msg)))))) hsT)
                (some (some (vpTblEnc st', t', i', m')), hsEncFn h') ρ₂))
          change (Comp.ite
            (orE (.lt (.nat (qep + 1)) (.fst (.snd .v0)))
              (.not (.eqN (.fst (.snd .v0)) (posEpoch (cRecPos .v3))))) _ _).eval ρ₄ = _
          have hes4' : (esSetH (.fst (Expr.v4 (O := OO))) (.snd .v2)).eval ρ₄ =
              esEnc vpTblEnc hsEncFn { es with h := h' } :=
            esSetH_eval vpTblEnc hsEncFn (O' := OO) (.fst .v4) (.snd .v2) ρ₄ es h' rfl rfl
          rw [eval_ite]
          have hEpochChk : (orE (.lt (.nat (qep + 1)) (.fst (.snd (Expr.v0 (O := OO)))))
              (.not (.eqN (.fst (.snd .v0)) (posEpoch (cRecPos .v3))))).eval ρ₄ =
              (decide (qep + 1 < t') || (t' != r.pos.epoch)) := by
            simp only [orE_eval, ρ₄, ρ₂, cRecPos, posEpoch, cRecEnc, posEnc,
              Expr.eval, Expr.v0, Expr.v3, Env.get_cons_zero, Env.get_cons_succ, bne, BEq.beq]
            by_cases ht : t' = r.pos.epoch <;> simp [ht]
          rw [hEpochChk]
          by_cases hqep : (decide (qep + 1 < t') || (t' != r.pos.epoch))
          · simp [hqep, hes4', smRrEnc, Expr.eval]
          · have hqep1 : ¬ (qep + 1 < t') := by
              intro hlt
              exact hqep (Bool.or_eq_true_iff.mpr (Or.inl (decide_eq_true hlt)))
            have hqep2 : (t' != r.pos.epoch) = false := by
              cases hb : (t' != r.pos.epoch)
              · rfl
              · exact False.elim (hqep (Bool.or_eq_true_iff.mpr (Or.inr hb)))
            simp only [hqep1, hqep2, Bool.or_false, decide_false, Bool.false_eq_true,
              ↓reduceIte, eval_ite]
            have hPos : (Expr.pair (otherE (.fst (.snd (Expr.v4 (O := OO)))))
                (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0))))).eval ρ₄ =
                posEnc ⟨P.other, t', i'⟩ := by
              simp [ρ₄, ρ₂, ρ₁, otherE, posEnc, partyEnc_other, Expr.eval, Expr.v0, Expr.v4]
            have hTriv : (cTrivialE L Δ (esG (.fst (Expr.v4 (O := OO))))
                (.pair (otherE (.fst (.snd .v4)))
                  (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))).eval ρ₄ =
                es.g.trivial Δ ⟨P.other, t', i'⟩ :=
              cTrivialE_eval vpTblEnc (O' := OO) L Δ (esG (.fst .v4)) _
                ρ₄ es.g ⟨P.other, t', i'⟩ hBound.trans_le hBound.comp_le rfl hPos
            rw [hTriv]
            by_cases htriv : es.g.trivial Δ ⟨P.other, t', i'⟩
            · simp only [htriv, ↓reduceIte, eval_bind]
              have hSt4 : (pGet (cGsSt (esG (.fst (Expr.v4 (O := OO)))))
                  (.fst (.snd .v4))).eval ρ₄ = vpTblEnc (es.g.st P) :=
                pGet_eval (cGsSt (esG (.fst .v4))) (.fst (.snd .v4)) ρ₄
                  (fun Q => vpTblEnc (es.g.st Q)) P rfl rfl
              have hCom := commitEC_eval hsEncFn HBounded hkC hk hHk L
                (esSetH (.fst .v4) (.snd .v2)) (esG (.fst .v4)) (.fst (.snd .v4))
                (pGet (cGsSt (esG (.fst .v4))) (.fst (.snd .v4))) (.fst .v0)
                (.pair (otherE (.fst (.snd .v4)))
                  (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
                ρ₄ { es with h := h' } es.g P (es.g.st P) st' ⟨P.other, t', i'⟩ hHB' hBound
                hes4' rfl rfl hSt4 rfl hPos
              rw [hCom, StateT.run_bind, bind_map_left, map_bind]
              refine bind_congr fun ⟨cmRes, es''⟩ => ?_
              rcases cmRes with _ | s_acc
              · simp [ρ₄, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
              · simp only [Prod.map, Option.map_some,
                  StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, map_pure]
                set ρ₅ := Env.cons
                  (t := cGsTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
                  (cGsEnc vpTblEnc s_acc)
                  (Env.cons
                    (t := .prod
                      (.opt (cGsTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E
                        γvT svT ssvT rsvT)))
                      (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
                    (some (cGsEnc vpTblEnc s_acc), esEnc vpTblEnc hsEncFn es'') ρ₄)
                change (Comp.ret _).eval ρ₅ = _
                have hSetG := esSetG_eval vpTblEnc hsEncFn (O' := OO) (.snd .v1) .v0
                  ρ₅ es'' s_acc rfl rfl
                simp only [eval_ret, pair_eval, some_eval, inr_eval, hSetG]
                rfl
            · simp only [htriv, Bool.false_eq_true, ↓reduceIte, eval_ret, pair_eval, some_eval]
              have hInjFull : (cfgC.injectFullE (.fst (.snd .v0))).eval ρ₄ = cfg.injectFull t' :=
                hCfg.injectFull_eq (.fst (.snd .v0)) ρ₄
              have hSetWin := cGsSetWin_eval vpTblEnc (O' := OO)
                (esG (.fst .v4)) (.bool true) ρ₄ es.g rfl
              have hg4 : (Expr.ite (cfgC.injectFullE (.fst (.snd .v0)))
                  (cGsSetWin (esG (.fst .v4)) (.bool true)) (esG (.fst .v4))).eval ρ₄ =
                  cGsEnc vpTblEnc
                    (if cfg.injectFull t' then { es.g with win := true } else es.g) := by
                rw [ite_eval, hInjFull, hSetWin]
                by_cases hf : cfg.injectFull t' <;>
                  simp [hf, ρ₄, ρ₂, ρ₁, esG, esEnc, Expr.eval, Expr.v4]
              have hSetG := esSetG_eval vpTblEnc hsEncFn (O' := OO)
                (esSetH (.fst .v4) (.snd .v2))
                (.ite (cfgC.injectFullE (.fst (.snd .v0)))
                  (cGsSetWin (esG (.fst .v4)) (.bool true)) (esG (.fst .v4)))
                ρ₄ { es with h := h' }
                (if cfg.injectFull t' then { es.g with win := true } else es.g) hes4' hg4
              rw [hSetG]
              by_cases hf : cfg.injectFull t' <;>
                simp [hf, StateT.run_modify, StateT.run_pure, smRrEnc, Expr.eval]

theorem deliverForgeE_inv [DecidableEq T] [DecidableEq E]
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    {L B q Δ qep : ℕ} (cfg : Config M)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (arg : Party × (Header T × E) × (Header T × E))
    (hInv : SMEngineInv L B (q + 1) es.g) :
    ∀ res ∈ support ((deliverForgeE hk Δ qep cfg arg).run es), SMEngineInv L B q res.2.g := by
  rcases arg with ⟨P, c, c'⟩
  intro ⟨out, es'⟩ hmem
  have hInvQ : SMEngineInv L B q es.g := hInv.mono (Nat.le_succ q)
  unfold deliverForgeE abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases hab : (es.abort || es.g.win)
  · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hInvQ
  · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
    rcases htr : es.g.inTransit P.other c with _ | r
    · simp only [htr, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInvQ
    · simp only [htr] at hmem
      by_cases hbad :
          ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos || c.1 != c'.1)
      · simp only [hbad, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hInvQ
      · simp only [hbad, Bool.false_eq_true, ↓reduceIte,
          run_liftH_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨vrRes, h'⟩, _, hmem⟩ := hmem
        rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hInvQ
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hInvQ
        · by_cases hqep : (decide (qep + 1 < t') || (t' != r.pos.epoch))
          · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
              Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hInvQ
          · simp only [hqep, Bool.false_eq_true, ↓reduceIte] at hmem
            by_cases htriv : es.g.trivial Δ ⟨P.other, t', i'⟩
            · simp only [htriv, ↓reduceIte, StateT.run_bind, mem_support_bind_iff] at hmem
              obtain ⟨⟨cmRes, es''⟩, hcm, hmem⟩ := hmem
              have ⟨hEs'', hAcc⟩ := commitE_inv hk { es with h := h' } es.g P (es.g.st P) st'
                ⟨P.other, t', i'⟩ hInvQ hInvQ (cmRes, es'') hcm
              rcases cmRes with _ | s₁
              · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
                  Prod.mk.injEq] at hmem
                rcases hmem with ⟨_, rfl⟩; exact hEs''
              · have hs₁ : SMEngineInv L B q s₁ := hAcc s₁ rfl
                simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                  support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                rcases hmem with ⟨_, rfl⟩; exact hs₁
            · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem
              by_cases hf : cfg.injectFull t'
              · simp only [hf, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
                  pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                rcases hmem with ⟨_, rfl⟩; exact hInvQ.of_lists_eq rfl rfl rfl rfl rfl
              · simp only [hf, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
                  support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                rcases hmem with ⟨_, rfl⟩; exact hInvQ

theorem deliverForgeE_vrInv [DecidableEq T] [DecidableEq E]
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    {VROkStep : ℕ → rsV → Prop}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    (hVRHk : HooksVRInv VROkStep hk)
    {L B q Δ qep : ℕ} (cfg : Config M)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (arg : Party × (Header T × E) × (Header T × E))
    (hInv : SMEngineInv L B (q + 1) es.g)
    (hVR : SMVRInv VROkStep B (q + 1) es.g) :
    ∀ res ∈ support ((deliverForgeE hk Δ qep cfg arg).run es),
      SMVRInv VROkStep B q res.2.g := by
  rcases arg with ⟨P, c, c'⟩
  have hVRQ : SMVRInv VROkStep B q es.g :=
    SMVRInv.mono (VROkStep := VROkStep) hVRHk.mono (Nat.le_succ q) hVR
  have hBq : B - (q + 1) + 1 = B - q := by
    have := hInv.trans_le; omega
  intro ⟨out, es'⟩ hmem
  unfold deliverForgeE abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases hab : (es.abort || es.g.win)
  · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hVRQ
  · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
    rcases htr : es.g.inTransit P.other c with _ | r
    · simp only [htr, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hVRQ
    · simp only [htr] at hmem
      by_cases hbad :
          ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos || c.1 != c'.1)
      · simp only [hbad, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hVRQ
      · simp only [hbad, Bool.false_eq_true, ↓reduceIte,
          run_liftH_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨vrRes, h'⟩, hvr, hmem⟩ := hmem
        rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hVRQ
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hVRQ
        · by_cases hqep : (decide (qep + 1 < t') || (t' != r.pos.epoch))
          · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
              Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hVRQ
          · simp only [hqep, Bool.false_eq_true, ↓reduceIte] at hmem
            by_cases htriv : es.g.trivial Δ ⟨P.other, t', i'⟩
            · simp only [htriv, ↓reduceIte, StateT.run_bind, mem_support_bind_iff] at hmem
              obtain ⟨⟨cmRes, es''⟩, hcm, hmem⟩ := hmem
              have hSt'VR : ∀ t₀ v₀, st'.vR t₀ = some v₀ → VROkStep (B - q) v₀ := by
                rw [← hBq]
                exact vRecv_vrInv hk hVRHk es.g P (es.g.st P) c' none es.h (hVR P)
                  (some (some (st', t', i', m')), h') hvr st' t' i' m' rfl
              have ⟨hEs'', hAcc⟩ := commitE_vrInv hk hVRHk { es with h := h' } es.g P (es.g.st P)
                st' ⟨P.other, t', i'⟩ hVRQ hVRQ hSt'VR (cmRes, es'') hcm
              rcases cmRes with _ | s₁
              · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
                  Prod.mk.injEq] at hmem
                rcases hmem with ⟨_, rfl⟩; exact hEs''
              · have hs₁ : SMVRInv VROkStep B q s₁ := hAcc s₁ rfl
                simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                  support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                rcases hmem with ⟨_, rfl⟩; exact hs₁
            · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem
              by_cases hf : cfg.injectFull t'
              · simp only [hf, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
                  pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                rcases hmem with ⟨_, rfl⟩; exact hVRQ
              · simp only [hf, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
                  support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                rcases hmem with ⟨_, rfl⟩; exact hVRQ

theorem deliverForgeE_b_eq [DecidableEq T] [DecidableEq E]
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    {Δ qep : ℕ} (cfg : Config M)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (arg : Party × (Header T × E) × (Header T × E)) :
    ∀ res ∈ support ((deliverForgeE hk Δ qep cfg arg).run es), res.2.g.b = es.g.b := by
  rcases arg with ⟨P, c, c'⟩
  intro ⟨out, es'⟩ hmem
  unfold deliverForgeE abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases hab : (es.abort || es.g.win)
  · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; rfl
  · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
    rcases htr : es.g.inTransit P.other c with _ | r
    · simp only [htr, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; rfl
    · simp only [htr] at hmem
      by_cases hbad :
          ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos || c.1 != c'.1)
      · simp only [hbad, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; rfl
      · simp only [hbad, Bool.false_eq_true, ↓reduceIte,
          run_liftH_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨vrRes, h'⟩, _, hmem⟩ := hmem
        rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; rfl
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; rfl
        · by_cases hqep : (decide (qep + 1 < t') || (t' != r.pos.epoch))
          · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
              Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; rfl
          · simp only [hqep, Bool.false_eq_true, ↓reduceIte] at hmem
            by_cases htriv : es.g.trivial Δ ⟨P.other, t', i'⟩
            · simp only [htriv, ↓reduceIte, StateT.run_bind, mem_support_bind_iff] at hmem
              obtain ⟨⟨cmRes, es''⟩, hcm, hmem⟩ := hmem
              have ⟨hEs'', hAcc⟩ := commitE_b_eq hk { es with h := h' } es.g P (es.g.st P) st'
                ⟨P.other, t', i'⟩ (cmRes, es'') hcm
              rcases cmRes with _ | s₁
              · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
                  Prod.mk.injEq] at hmem
                rcases hmem with ⟨_, rfl⟩; exact hEs''
              · have hs₁ : s₁.b = es.g.b := hAcc s₁ rfl
                simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                  support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                rcases hmem with ⟨_, rfl⟩; exact hs₁
            · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem
              by_cases hf : cfg.injectFull t'
              · simp only [hf, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
                  pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                rcases hmem with ⟨_, rfl⟩; rfl
              · simp only [hf, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
                  support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                rcases hmem with ⟨_, rfl⟩; rfl

end CryptoGames.SM.Engine

namespace CryptoGames.SM.Construction

open Engine Engine.RedPRNG CKA PRFPRNG

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}

local notation "S" => ckaSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrTy" => ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrCtTy" => ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "psTy" => ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "rrTy" => ckaRrTy KC Γ CCoins T I KR RSt K SS RS M E

/-! ## Authenticity reductions -/

section HooksCKACDF

variable
  {ckaInitA : KC → Γ}
  {ckaInitB : KC → Γ}
  {ckaSend : Γ → CCoins → Γ × T × I}
  {ckaReceive : Γ → T → Γ × I}
  {prngInit : KR → RSt}
  {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS}
  {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E}
  {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool}
  {eqI : I → I → Bool}
  {eqM : M → M → Bool}
  {eqE : E → E → Bool}
  {lam : I}
  {defaultE : E}
  {sampKR : ProbComp KR}
  {sampKC : ProbComp KC}
  {sampCCoins : ProbComp CCoins}
  {sampI : ProbComp I}
  {sampK : ProbComp K}

local notation "OO" =>
  ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE

local notation "II" =>
  ckaIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK

/-- Costed `DeliverForge.redCKAAuthDF` reduction over `SM.specDF`. -/
def redCKAAuthDFProg (L B Δcka qep maxSkip : ℕ) (tL : Option ℕ) (t : ℕ) :
    CostedReduction OO II
      (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E)
      .unit .unit .bool .bool where
  σ := ckaEsTy
  init := rdsl [_] do
    es ← initCKAEStateC (raw ⟨true, tL, t⟩) false
    return ((), es)
  handle := rdsl [st, q] do
    implECDF (raw (hooksCKAC B Δcka ⟨true, tL, t⟩)) L (raw (2 + Δcka)) qep maxSkip
      (raw (modeCfgEC OO ⟨true, tL, t⟩)) (raw (⟨true, tL, t⟩ : Mode).policy) st q
  finish := rdsl [st, _] do
    return authOutE L (raw (2 + Δcka)) (raw (⟨true, tL, t⟩ : Mode).policy) st

@[simp] theorem deliverForgeEC_hooksCKAC_queries (L B Δcka qep : ℕ) (mo : Mode) {Γ'}
    (es : Expr OO Γ' ckaEsTy)
    (arg : Expr OO Γ' (.prod .bool (.prod hdrCtTy hdrCtTy))) :
    (deliverForgeEC (hooksCKAC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B Δcka mo)
      L (2 + Δcka) qep (modeCfgEC OO mo) es arg).queries
      (fun _ => 1) (fun _ => 0) = 2 := by
  simp [deliverForgeEC, vRecvC, vRecvStep1C, commitEC, hooksCKAC, Comp.queries]

@[simp] theorem implECDF_hooksCKAC_queries (L B Δcka qep maxSkip : ℕ) (mo : Mode) {Γ'}
    (es : Expr OO Γ' ckaEsTy)
    (q : Expr OO Γ' (ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E)) :
    (implECDF (hooksCKAC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B Δcka mo)
      L (2 + Δcka) qep maxSkip (modeCfgEC OO mo) mo.policy es q).queries
      (fun _ => 1) (fun _ => 0) = 2 := by
  simp [implECDF, implEC_hooksCKAC_queries, deliverForgeEC_hooksCKAC_queries, Comp.queries]

@[simp] theorem redCKAAuthDFProg_totalQueries (L B Δcka qep maxSkip : ℕ)
    (tL : Option ℕ) (t q : ℕ) :
    (redCKAAuthDFProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L B Δcka qep maxSkip tL t).totalQueries (fun _ => 1) (fun _ => 0) q = q * 2 := by
  simp [CostedReduction.totalQueries, redCKAAuthDFProg, Comp.queries]

theorem redCKAAuthDFProg_totalCost (L B Δcka qep maxSkip : ℕ) (tL : Option ℕ) (t q : ℕ) :
    (redCKAAuthDFProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L B Δcka qep maxSkip tL t).totalCost q =
      491 +
        q * ((implECDF (Γ' := [ckaEsTy, ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E])
          (hooksCKAC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
            (sampI := sampI) (sampK := sampK) B Δcka ⟨true, tL, t⟩)
          L (2 + Δcka) qep maxSkip (modeCfgEC OO ⟨true, tL, t⟩)
          (⟨true, tL, t⟩ : Mode).policy .v0 .v1).cost + 13) +
        (authOutE (O' := OO) L (2 + Δcka) (⟨true, tL, t⟩ : Mode).policy
          (Expr.v0 : Expr OO [ckaEsTy, .bool] ckaEsTy)).cost := by
  simp only [CostedReduction.totalCost, redCKAAuthDFProg, ckaSMCodecDF, ckaSMCodec, ckaIface, Comp.cost,
    initCKAEStateC_cost, Expr.cost, Expr.v0]
  rw [max_eq_right (by omega)]
  omega

end HooksCKACDF

section HooksPRNGCDF

variable
  {ckaInitA : KC → Γ}
  {ckaInitB : KC → Γ}
  {ckaSend : Γ → CCoins → Γ × T × I}
  {ckaReceive : Γ → T → Γ × I}
  {prngInit : KR → RSt}
  {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS}
  {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E}
  {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool}
  {eqI : I → I → Bool}
  {eqM : M → M → Bool}
  {eqE : E → E → Bool}
  {lam : I}
  {defaultE : E}
  {sampKR : ProbComp KR}
  {sampKC : ProbComp KC}
  {sampCCoins : ProbComp CCoins}
  {sampI : ProbComp I}
  {sampK : ProbComp K}

local notation "OO" =>
  prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE

local notation "II" =>
  prngIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK

/-- Costed `DeliverForge.redPRNGAuthDF` reduction over `SM.specDF`. -/
def redPRNGAuthDFProg (L B Δcka qep maxSkip : ℕ) (tL : Option ℕ) (t : ℕ) :
    CostedReduction OO II
      (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E)
      .unit .unit .bool .bool where
  σ := prngEsTy
  init := rdsl [_] do
    es ← initPRNGEStateC (raw ⟨true, tL, t⟩) false
    return ((), es)
  handle := rdsl [st, q] do
    implECDF (raw (hooksPRNGC B ⟨true, tL, t⟩)) L (raw (2 + Δcka)) qep maxSkip
      (raw (modeCfgEC OO ⟨true, tL, t⟩)) (raw (⟨true, tL, t⟩ : Mode).policy) st q
  finish := rdsl [st, _] do
    return authOutE L (raw (2 + Δcka)) (raw (⟨true, tL, t⟩ : Mode).policy) st

@[simp] theorem deliverForgeEC_hooksPRNGC_queries (L B Δcka qep : ℕ) (mo : Mode) {Γ'}
    (es : Expr OO Γ' prngEsTy)
    (arg : Expr OO Γ' (.prod .bool (.prod hdrCtTy hdrCtTy))) :
    (deliverForgeEC (hooksPRNGC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B mo)
      L (2 + Δcka) qep (modeCfgEC OO mo) es arg).queries
      (fun _ => 1) (fun _ => 0) = 1 := by
  simp [deliverForgeEC, vRecvC, vRecvStep1C, commitEC, hooksPRNGC, Comp.queries]

@[simp] theorem implECDF_hooksPRNGC_queries (L B Δcka qep maxSkip : ℕ) (mo : Mode) {Γ'}
    (es : Expr OO Γ' prngEsTy)
    (q : Expr OO Γ' (ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E)) :
    (implECDF (hooksPRNGC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B mo)
      L (2 + Δcka) qep maxSkip (modeCfgEC OO mo) mo.policy es q).queries
      (fun _ => 1) (fun _ => 0) = 2 := by
  simp [implECDF, implEC_hooksPRNGC_queries, deliverForgeEC_hooksPRNGC_queries, Comp.queries]

@[simp] theorem redPRNGAuthDFProg_totalQueries (L B Δcka qep maxSkip : ℕ)
    (tL : Option ℕ) (t q : ℕ) :
    (redPRNGAuthDFProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L B Δcka qep maxSkip tL t).totalQueries (fun _ => 1) (fun _ => 0) q = 2 + q * 2 := by
  simp [CostedReduction.totalQueries, redPRNGAuthDFProg, Comp.queries]

theorem redPRNGAuthDFProg_totalCost (L B Δcka qep maxSkip : ℕ) (tL : Option ℕ) (t q : ℕ) :
    (redPRNGAuthDFProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L B Δcka qep maxSkip tL t).totalCost q =
      (initPRNGEStateC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        ⟨true, tL, t⟩ (.bool false : Expr OO [.unit] .bool)).cost + 6 +
        q * ((implECDF (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
          (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (I' := II)
          (Γ' := [prngEsTy, ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E])
          (hooksPRNGC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
            (sampI := sampI) (sampK := sampK) B ⟨true, tL, t⟩)
          L (2 + Δcka) qep maxSkip (modeCfgEC OO ⟨true, tL, t⟩)
          (⟨true, tL, t⟩ : Mode).policy .v0 .v1).cost + 13) +
        (authOutE (O' := OO) L (2 + Δcka) (⟨true, tL, t⟩ : Mode).policy
          (Expr.v0 : Expr OO [prngEsTy, .bool] prngEsTy)).cost := by
  simp only [CostedReduction.totalCost, redPRNGAuthDFProg, prngSMCodecDF, ckaSMCodecDF, prngIface, Comp.cost,
    Expr.cost]
  have hV0 : (Expr.v0 : Expr OO [prngEsTy, .unit] prngEsTy).cost = 1 := rfl
  rw [hV0, max_eq_right (by omega)]
  omega

end HooksPRNGCDF

section HooksFSCDF

variable
  {ckaInitA : KC → Γ}
  {ckaInitB : KC → Γ}
  {ckaSend : Γ → CCoins → Γ × T × I}
  {ckaReceive : Γ → T → Γ × I}
  {prngInit : KR → RSt}
  {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS}
  {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E}
  {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool}
  {eqI : I → I → Bool}
  {eqM : M → M → Bool}
  {eqE : E → E → Bool}
  {lam : I}
  {defaultE : E}
  {sampKR : ProbComp KR}
  {sampKC : ProbComp KC}
  {sampCCoins : ProbComp CCoins}
  {sampI : ProbComp I}
  {sampK : ProbComp K}

local notation "OO" =>
  prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE

local notation "II" =>
  fsaeadHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK

local notation "hsTy" => fsHsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hsEnc" => fsHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M)
local notation "hsDec" => fsHsDec (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M)
local notation "vpTyFS" => fsVpTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "vpEnc" =>
  fsVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (K := K) (M := M) (E := E)
local notation "esTyFS" => fsEsTy KC Γ CCoins T I KR RSt K SS RS M E

theorem deliverForgeE_hooksFSL_eq [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L Δ qep : ℕ) (cfg : Config M) (Δcka : ℕ) (mo : Mode) (j : ℕ) :
    DeliverForge.deliverForgeE (hooksFSL cka prng fs L Δcka mo j) Δ qep cfg =
      DeliverForge.deliverForgeE (hooksFS cka prng fs Δcka mo j) Δ qep cfg := by
  funext q; unfold DeliverForge.deliverForgeE; rw [vRecv_hooksFSL_eq, commitE_hooksFSL_eq]

theorem deliverForgeE_fs_inv [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    {L B q Δ qep : ℕ} (cfg : Config M) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (es : EState (VP Γ T RSt (Option SS) (Option RS)) M (Header T × E)
      (FSState T RSt K I SS RS E))
    (arg : Party × (Header T × E) × (Header T × E))
    (hInv : FSEngineInv L B (q + 1) es) :
    ∀ res ∈ support
      ((DeliverForge.deliverForgeE (hooksFS cka prng fs Δcka mo j) Δ qep cfg arg).run es),
      FSEngineInv L B q res.2 := by
  rcases arg with ⟨P, c, c'⟩
  intro ⟨out, es'⟩ hmem
  have hInvQ : FSEngineInv L B q es := hInv.mono (Nat.le_succ q)
  have hSm := deliverForgeE_inv (hooksFS cka prng fs Δcka mo j) cfg es (P, c, c') hInv.sm
    (out, es') hmem
  unfold DeliverForge.deliverForgeE abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases hab : (es.abort || es.g.win)
  · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hInvQ
  · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
    rcases htr : es.g.inTransit P.other c with _ | r
    · simp only [htr, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInvQ
    · simp only [htr] at hmem
      by_cases hbad :
          ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos || c.1 != c'.1)
      · simp only [hbad, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hInvQ
      · simp only [hbad, Bool.false_eq_true, ↓reduceIte,
          run_liftH_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨vrRes, h'⟩, hvr, hmem⟩ := hmem
        have hPres := vRecv_fs_preserve cka prng fs Δcka mo j es.g P (es.g.st P) c' none es.h
          (hInv.vR_none_of_gt P) (vrRes, h') hvr
        dsimp only at hPres
        rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩
          exact ⟨hSm,
            by dsimp only; have := hInv.table_le; have := hPres.1; omega,
            by dsimp only; have := hInv.sessions_le; have := hPres.2.1; omega,
            by dsimp only; have := hInv.fsTrans_le; have := hPres.2.2.1; omega,
            hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩
          exact ⟨hSm,
            by dsimp only; have := hInv.table_le; have := hPres.1; omega,
            by dsimp only; have := hInv.sessions_le; have := hPres.2.1; omega,
            by dsimp only; have := hInv.fsTrans_le; have := hPres.2.2.1; omega,
            hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
        · by_cases hqep : (decide (qep + 1 < t') || (t' != r.pos.epoch))
          · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
              Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩
            exact ⟨hSm,
              by dsimp only; have := hInv.table_le; have := hPres.1; omega,
              by dsimp only; have := hInv.sessions_le; have := hPres.2.1; omega,
              by dsimp only; have := hInv.fsTrans_le; have := hPres.2.2.1; omega,
              hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
          · simp only [hqep, Bool.false_eq_true, ↓reduceIte] at hmem
            by_cases htriv : es.g.trivial Δ ⟨P.other, t', i'⟩
            · simp only [htriv, ↓reduceIte, StateT.run_bind, commitE_fs_eq, pure_bind,
                StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff,
                Prod.mk.injEq] at hmem
              rcases hmem with ⟨_, rfl⟩
              have hst' := hPres.2.2.2 st' t' i' m' rfl
              refine ⟨hSm,
                by dsimp only; have := hInv.table_le; have := hPres.1; omega,
                by dsimp only; have := hInv.sessions_le; have := hPres.2.1; omega,
                by dsimp only; have := hInv.fsTrans_le; have := hPres.2.2.1; omega,
                fun Q => ?_, fun Q t ht => ?_⟩
              · dsimp only [SM.GameState.accept]
                by_cases hQ : Q = P
                · subst hQ; simp only [Function.update_self]
                  have := hInv.tcur_le Q; have := hst'.1; omega
                · simp only [Function.update_of_ne hQ]; exact hInvQ.tcur_le Q
              · dsimp only [SM.GameState.accept] at ht ⊢
                by_cases hQ : Q = P
                · subst hQ; simp only [Function.update_self] at ht ⊢; exact hst'.2 t ht
                · simp only [Function.update_of_ne hQ] at ht ⊢; exact hInv.vR_none_of_gt Q t ht
            · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem
              by_cases hf : cfg.injectFull t'
              · simp only [hf, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
                  pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                rcases hmem with ⟨_, rfl⟩
                exact ⟨hSm,
                  by dsimp only; have := hInv.table_le; have := hPres.1; omega,
                  by dsimp only; have := hInv.sessions_le; have := hPres.2.1; omega,
                  by dsimp only; have := hInv.fsTrans_le; have := hPres.2.2.1; omega,
                  hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
              · simp only [hf, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
                  support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                rcases hmem with ⟨_, rfl⟩
                exact ⟨hSm,
                  by dsimp only; have := hInv.table_le; have := hPres.1; omega,
                  by dsimp only; have := hInv.sessions_le; have := hPres.2.1; omega,
                  by dsimp only; have := hInv.fsTrans_le; have := hPres.2.2.1; omega,
                  hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩

/-- Costed `DeliverForge.redFSAuthDF` reduction over `SM.specDF`. -/
def redFSAuthDFProg (L B Δcka qep maxSkip : ℕ) (j : ℕ) (tL : Option ℕ) (t : ℕ) :
    CostedReduction OO II
      (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E)
      .unit .unit .bool .bool where
  σ := esTyFS
  init := rdsl [_] do
    es ← initFSEStateC L (raw ⟨true, tL, t⟩) j false
    return ((), es)
  handle := rdsl [st, q] do
    implECDF (raw (hooksFSC L B Δcka ⟨true, tL, t⟩ j)) L (raw (2 + Δcka)) qep maxSkip
      (raw (modeCfgEC OO ⟨true, tL, t⟩)) (raw (⟨true, tL, t⟩ : Mode).policy) st q
  finish := rdsl [_, _] do
    sample (O := OO) (I := II) CKASamp.bit ()

@[simp] theorem deliverForgeEC_hooksFSC_queries (L B Δcka qep : ℕ) (mo : Mode) (j : ℕ) {Γ'}
    (es : Expr OO Γ' esTyFS)
    (arg : Expr OO Γ' (.prod .bool (.prod hdrCtTy hdrCtTy))) :
    (deliverForgeEC (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δcka mo j)
      L (2 + Δcka) qep (modeCfgEC OO mo) es arg).queries
      (fun _ => 1) (fun _ => 0) = 1 := by
  simp [deliverForgeEC, vRecvC, vRecvStep1C, commitEC, hooksFSC, Comp.queries]

@[simp] theorem deliverForgeEC_hooksFSC_decQueries (L B Δcka qep : ℕ) (mo : Mode) (j : ℕ) {Γ'}
    (es : Expr OO Γ' esTyFS)
    (arg : Expr OO Γ' (.prod .bool (.prod hdrCtTy hdrCtTy))) :
    (deliverForgeEC (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δcka mo j)
      L (2 + Δcka) qep (modeCfgEC OO mo) es arg).queries
      fsHdrDecWt (fun _ => 0) = 1 := by
  simp [deliverForgeEC, vRecvC, vRecvStep1C, commitEC, hooksFSC, Comp.queries]

@[simp] theorem implECDF_hooksFSC_queries (L B Δcka qep maxSkip : ℕ) (mo : Mode) (j : ℕ) {Γ'}
    (es : Expr OO Γ' esTyFS)
    (q : Expr OO Γ' (ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E)) :
    (implECDF (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δcka mo j)
      L (2 + Δcka) qep maxSkip (modeCfgEC OO mo) mo.policy es q).queries
      (fun _ => 1) (fun _ => 0) = 2 := by
  simp [implECDF, implEC_hooksFSC_queries, deliverForgeEC_hooksFSC_queries, Comp.queries]

@[simp] theorem implECDF_hooksFSC_decQueries (L B Δcka qep maxSkip : ℕ) (mo : Mode) (j : ℕ) {Γ'}
    (es : Expr OO Γ' esTyFS)
    (q : Expr OO Γ' (ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E)) :
    (implECDF (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δcka mo j)
      L (2 + Δcka) qep maxSkip (modeCfgEC OO mo) mo.policy es q).queries
      fsHdrDecWt (fun _ => 0) = 1 := by
  simp [implECDF, implEC_hooksFSC_decQueries, deliverForgeEC_hooksFSC_decQueries, Comp.queries]

@[simp] theorem redFSAuthDFProg_totalQueries (L B Δcka qep maxSkip : ℕ) (j : ℕ)
    (tL : Option ℕ) (t q : ℕ) :
    (redFSAuthDFProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L B Δcka qep maxSkip j tL t).totalQueries (fun _ => 1) (fun _ => 0) q = q * 2 := by
  simp [CostedReduction.totalQueries, redFSAuthDFProg, Comp.queries]

theorem redFSAuthDFProg_totalCost (L B Δcka qep maxSkip : ℕ) (j : ℕ) (tL : Option ℕ) (t q : ℕ) :
    (redFSAuthDFProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L B Δcka qep maxSkip j tL t).totalCost q =
      (initFSEStateC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L ⟨true, tL, t⟩ j (.bool false : Expr OO [.unit] .bool)).cost + 7 +
        q * ((implECDF (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
          (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (I' := II)
          (Γ' := [esTyFS, ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E])
          (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
            (sampI := sampI) (sampK := sampK) L B Δcka ⟨true, tL, t⟩ j)
          L (2 + Δcka) qep maxSkip (modeCfgEC OO ⟨true, tL, t⟩)
          (⟨true, tL, t⟩ : Mode).policy .v0 .v1).cost + 13) := by
  simp only [CostedReduction.totalCost, redFSAuthDFProg, prngSMCodecDF, ckaSMCodecDF, fsaeadHeaderAdIface, prngSamplers,
    ckaSamplers, Comp.cost, Expr.cost]
  have hV0 : (Expr.v0 : Expr OO [esTyFS, .unit] esTyFS).cost = 1 := rfl
  rw [hV0, max_eq_right (by omega)]
  omega

end HooksFSCDF

section FromAEADPRGDF

variable {MK C : Type}

theorem deliverForgeE_fsClamp_eq [DecidableEq T] [DecidableEq I] [DecidableEq C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip B B_q q Δcka qep : ℕ) (mo : Mode) (j : ℕ)
    (hB : (B_q + 1) * (maxSkip + 1) ≤ B)
    (es : EState (VP Γ T RSt (Option (FSAEAD.RatchetSenderState K))
      (Option (FSAEAD.RatchetReceiverState K MK))) M (Header T × (ℕ × C))
      (FSState T RSt K I (FSAEAD.RatchetSenderState K)
        (FSAEAD.RatchetReceiverState K MK) (ℕ × C)))
    (arg : Party × (Header T × (ℕ × C)) × (Header T × (ℕ × C)))
    (hVR : SMVRInv (FSVROkStep maxSkip) B_q (q + 1) es.g)
    (hExt : FSVROkStep maxSkip (B_q - (q + 1)) (es.h.ext.map Prod.snd)) :
    (DeliverForge.deliverForgeE
        (hooksFS cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip)) Δcka mo j)
        (2 + Δcka) qep mo.cfg arg).run es =
      (DeliverForge.deliverForgeE
        (hooksFS cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j)
        (2 + Δcka) qep mo.cfg arg).run es := by
  have hkB : (B_q - (q + 1) + 1) * (maxSkip + 1) ≤ B :=
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.sub_le _ _) 1)).trans hB
  rcases arg with ⟨P, c, c'⟩
  unfold DeliverForge.deliverForgeE
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hab : (es.abort || es.g.win)
  · simp only [hab, ↓reduceIte]
  · simp only [hab, Bool.false_eq_true, ↓reduceIte]
    rcases htr : es.g.inTransit P.other c with _ | r
    · rfl
    · dsimp only
      by_cases hbad :
          ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos || c.1 != c'.1)
      · simp only [hbad, ↓reduceIte]
      · simp only [hbad, Bool.false_eq_true, ↓reduceIte, run_liftH_bind]
        rw [vRecv_fsClamp_eq cka prng ae G maxSkip B (B_q - (q + 1)) Δcka mo j hkB
          es.g P (es.g.st P) c' none es.h (hVR P) hExt]
        rfl

theorem deliverForgeE_ext_snd [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C]
    [Inhabited C] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip k Δcka qep : ℕ) (mo : Mode) (j : ℕ)
    (es : EState (VP Γ T RSt (Option (FSAEAD.RatchetSenderState K))
      (Option (FSAEAD.RatchetReceiverState K MK))) M (Header T × (ℕ × C))
      (FSState T RSt K I (FSAEAD.RatchetSenderState K)
        (FSAEAD.RatchetReceiverState K MK) (ℕ × C)))
    (arg : Party × (Header T × (ℕ × C)) × (Header T × (ℕ × C)))
    (hVR : ∀ P t₀ v, (es.g.st P).vR t₀ = some v → FSVROkStep maxSkip k v)
    (hExt : FSVROkStep maxSkip k (es.h.ext.map Prod.snd)) :
    ∀ res ∈ support
      ((DeliverForge.deliverForgeE
        (hooksFS cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j)
        (2 + Δcka) qep mo.cfg arg).run es),
      FSVROkStep maxSkip (k + 1) (res.2.h.ext.map Prod.snd) := by
  have hExt1 : FSVROkStep maxSkip (k + 1) (es.h.ext.map Prod.snd) := hExt.mono (Nat.le_succ k)
  rcases arg with ⟨P, c, c'⟩
  intro ⟨out, es'⟩ hmem
  unfold DeliverForge.deliverForgeE abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases hab : (es.abort || es.g.win)
  · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hExt1
  · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
    rcases htr : es.g.inTransit P.other c with _ | r
    · simp only [htr, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hExt1
    · simp only [htr] at hmem
      by_cases hbad :
          ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos || c.1 != c'.1)
      · simp only [hbad, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hExt1
      · simp only [hbad, Bool.false_eq_true, ↓reduceIte, run_liftH_bind,
          mem_support_bind_iff] at hmem
        obtain ⟨⟨vrRes, h'⟩, hvr, hmem⟩ := hmem
        have hExt' := vRecv_ext_snd cka prng ae G maxSkip k Δcka mo j
          es.g P (es.g.st P) c' none es.h (hVR P) hExt (vrRes, h') hvr
        rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hExt'
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hExt'
        · by_cases hqep : (decide (qep + 1 < t') || (t' != r.pos.epoch))
          · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
              Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hExt'
          · simp only [hqep, Bool.false_eq_true, ↓reduceIte] at hmem
            by_cases htriv : es.g.trivial (2 + Δcka) ⟨P.other, t', i'⟩
            · simp only [htriv, ↓reduceIte, StateT.run_bind, commitE_fs_eq, pure_bind,
                StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff,
                Prod.mk.injEq] at hmem
              rcases hmem with ⟨_, rfl⟩; exact hExt'
            · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem
              split_ifs at hmem <;>
                (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                   support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
                 rcases hmem with ⟨_, rfl⟩; exact hExt')

theorem qb_deliverForgeE_one
    {Q : (ReductionsQueries.RSpec SS RS T M E).Domain → Prop} [DecidablePred Q]
    (hQu : ∀ u, ¬ Q (.inl u))
    [DecidableEq M] [DecidableEq T] [DecidableEq E] [DecidableEq I] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (mo : Mode) (j : ℕ)
    (q : Party × (Header T × E) × (Header T × E)) :
    ReductionsQueries.QB Q
      (DeliverForge.deliverForgeE (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep mo.cfg q) 1 := by
  rcases q with ⟨P, c, c'⟩
  unfold DeliverForge.deliverForgeE
  refine ReductionsQueries.qb_bind0 ReductionsQueries.qb_get fun es => ?_
  dsimp only
  by_cases hab : (es.abort || es.g.win) = true
  · simp only [hab, ↓reduceIte]
    exact ReductionsQueries.qb_pure none 1
  · simp only [hab, Bool.false_eq_true, ↓reduceIte]
    rcases htr : es.g.inTransit P.other c with _ | r
    · exact ReductionsQueries.qb_pure none 1
    · dsimp only
      by_cases hbad :
          ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos || c.1 != c'.1) = true
      · simp only [hbad, ↓reduceIte]
        exact ReductionsQueries.qb_pure none 1
      · simp only [hbad, Bool.false_eq_true, ↓reduceIte]
        refine ReductionsQueries.qb_bind_r
          (ReductionsQueries.qb_liftH
            (ReductionsQueries.qb_vRecv_one hQu cka prng fs Δcka mo j es.g P (es.g.st P) c' none))
          fun res => ?_
        cases res with
        | none => exact ReductionsQueries.qb_bind0 ReductionsQueries.qb_abortE fun _ =>
            ReductionsQueries.qb_pure none 0
        | some inner =>
          cases inner with
          | none => exact ReductionsQueries.qb_pure (some RecvResult.rejected) 0
          | some stim =>
            rcases stim with ⟨st', t', i', m'⟩
            dsimp only
            by_cases h2 : (decide (qep + 1 < t') || (t' != r.pos.epoch)) = true
            · simp only [h2, ↓reduceIte]
              exact ReductionsQueries.qb_pure (some RecvResult.rejected) 0
            · simp only [h2, Bool.false_eq_true, ↓reduceIte]
              by_cases h3 : es.g.trivial (2 + Δcka) ⟨P.other, t', i'⟩ = true
              · simp only [h3, ↓reduceIte]
                refine ReductionsQueries.qb_bind0
                  (ReductionsQueries.qb_commitE cka prng fs Δcka mo j es.g P (es.g.st P) st'
                    ⟨P.other, t', i'⟩)
                  fun s₁? => ?_
                cases s₁? with
                | none => exact ReductionsQueries.qb_pure none 0
                | some s₁ =>
                  exact ReductionsQueries.qb_bind0 (ReductionsQueries.qb_modify _) fun _ =>
                    ReductionsQueries.qb_pure _ 0
              · simp only [h3, Bool.false_eq_true, ↓reduceIte]
                split_ifs
                · exact ReductionsQueries.qb_bind0 (ReductionsQueries.qb_modify _) fun _ =>
                    ReductionsQueries.qb_pure (some RecvResult.rejected) 0
                · exact ReductionsQueries.qb_pure (some RecvResult.rejected) 0

end FromAEADPRGDF

end CryptoGames.SM.Construction
