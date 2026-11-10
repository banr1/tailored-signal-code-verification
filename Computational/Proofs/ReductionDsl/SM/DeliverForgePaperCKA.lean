/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperDefs
public import Computational.Proofs.ReductionDsl.SM.DeliverForge
import Computational.Proofs.ReductionDsl.Notation

/-!
# Costed `implECDFPaper` Engine Dispatch and `redCKAAuthDFPaperProg` Reduction

Deep-embedded `ReductionDsl` engine dispatcher `implECDFPaper` and `CostedReduction` formulation
`redCKAAuthDFPaperProg` of `DeliverForge.redCKAAuthDFPaper`.
-/

@[expose] public section

open ReductionDsl OracleSpec OracleComp
open scoped Computational.Proofs.ReductionDsl.Notation

/-! ## Engine dispatch -/

namespace CryptoGames.SM.Engine

open Construction CKA DeliverForge

local macro_rules
  | `(rdsl_pat| .transmit $p:term)  => `(rdsl_pat| .inl (.inl (.inl (.inl $p))))
  | `(rdsl_pat| .challenge $p:term) => `(rdsl_pat| .inl (.inl (.inl (.inr $p))))
  | `(rdsl_pat| .deliver $p:term)   => `(rdsl_pat| .inl (.inl (.inr $p)))
  | `(rdsl_pat| .inject $p:term)    => `(rdsl_pat| .inl (.inr $p))
  | `(rdsl_pat| .corrupt $p:term)   => `(rdsl_pat| .inr $p)

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

/-- Costed `SM.GameState.corrAllowedPaper` expression with list-scan bound `L`. -/
def cCorrAllowedPaperE
    {O' : Ops S} {vpT : Ty S} {Γ'} (L : ℕ) (s : Expr O' Γ' (cGsTy vpT))
    (p : Expr O' Γ' .bool) : Expr O' Γ' .bool :=
  rdslExpr =>
    letE (s, p) fun (s0, p0) =>
      !(anyB L (cGsChall s0) fun pos => boolEq (posSender pos) (otherE p0))

theorem cCorrAllowedPaperE_eval {O' : Ops S} {vpT : Ty S} {VPt : Type}
    (vpEncFn : VPt → vpT.denote) {Γ'} (L : ℕ) (s : Expr O' Γ' (cGsTy vpT))
    (p : Expr O' Γ' .bool) (ρ : Env Γ') (st : GameState VPt M (Header T × E)) (P : Party)
    (hChall : st.chall.length ≤ L)
    (hs : s.eval ρ = cGsEnc (vpT := vpT) vpEncFn st) (hp : p.eval ρ = partyEnc P) :
    (cCorrAllowedPaperE L s p).eval ρ = st.corrAllowedPaper P := by
  unfold cCorrAllowedPaperE GameState.corrAllowedPaper
  rw [letE_eval]
  have h0 : (Expr.pair s p).eval ρ = (cGsEnc (vpT := vpT) vpEncFn st, partyEnc P) := by
    simp [Expr.eval, hs, hp]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod (cGsTy vpT) .bool) (cGsEnc (vpT := vpT) vpEncFn st, partyEnc P) ρ
  have htCh : (st.chall.map posEnc).take L = st.chall.map posEnc :=
    List.take_of_length_le (by simpa using hChall)
  have hCh0 : (cGsChall (.fst (Expr.v0 (O := O')))).eval ρ₁ = st.chall.map posEnc := rfl
  simp only [Expr.eval, hCh0, htCh]
  congr 1
  rw [any_map_eq]
  congr 1; funext pos
  simp [ρ₁, posSender, otherE, posEnc, ← partyEnc_other, partyEnc_beq, Expr.eval,
    Expr.v0, Expr.v1]

def corrECPaper
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : Ty S}
    (hk : HooksC OO I' γvT svT ssvT rsvT hsT)
    (L : ℕ) (π : Policy)
    {Γ'} (es : Expr OO Γ'
      (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (p : Expr OO Γ' .bool) :
    Comp OO I' Γ'
      (.prod (.opt psTy)
        (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT)) :=
  rdsl do
    (es0, p0) ← return (es, p)
    let s0 := esG es0
    let refuse := orE (esAbort es0) (orE (cGsWin s0) (!(cCorrAllowedPaperE L s0 p0)))
    if refuse then
      return (none, es0)
    else
      let s1 := cAfterCorrE L s0 p0
      if orE (leakDoomE L π s0 s1) (corrDoomE π s0 p0) then
        return (none, esSetAbort es0 true)
      else
        (optSt, h') ← hk.reveal (esH es0) s0 p0 (pGet (cGsSt s0) p0)
        match optSt with
        | none => return (none, esMk s0 h' true)
        | some st => return (some st, esMk s1 h' (esAbort es0))

def implECPaper
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : Ty S}
    (hk : HooksC OO I' γvT svT ssvT rsvT hsT)
    (L Δ qep maxSkip : ℕ) (cfg : ConfigEC OO) (π : Policy)
    {Γ'} (es : Expr OO Γ'
      (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (q : Expr OO Γ' (ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E)) :
    Comp OO I' Γ'
      (.prod (ckaSMR KC Γ CCoins T I KR RSt K SS RS M E)
        (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT)) :=
  rdsl do
    (es0, q0) ← return (es, q)
    match q0 with
    | .transmit arg =>
      (r, es') ← transmitEC hk L Δ qep π es0 arg
      return (.inl (.inl (.inl (.inl r))), es')
    | .challenge arg =>
      (r, es') ← challEC hk L Δ qep cfg π es0 arg
      return (.inl (.inl (.inl (.inr r))), es')
    | .deliver arg =>
      (r, es') ← deliverEC hk L maxSkip cfg es0 arg
      return (.inl (.inl (.inr r)), es')
    | .inject arg =>
      (r, es') ← injectEC hk L Δ qep cfg es0 arg
      return (.inl (.inr r), es')
    | .corrupt arg =>
      (r, es') ← corrECPaper hk L π es0 arg
      return (.inr r, es')

/-- Six-oracle costed engine dispatcher for `DeliverForge.implEDFPaper`. -/
def implECDFPaper
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
      (r, es') ← implECPaper hk L Δ qep maxSkip cfg π es0 qBase
      return (.inl r, es')
    | .inr qDf =>
      (r, es') ← deliverForgeEC hk L Δ qep cfg es0 qDf
      return (.inr r, es')

theorem corrECPaper_eval {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S} {HS : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hsEncFn : HS → hsT.denote) (HBounded : HS → Prop) {HBoundedPost : HS → Prop}
    {VROk : rsvT.denote → Prop}
    (hkC : HooksC OO I' γvT svT ssvT rsvT hsT)
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins
      γvT.denote svT.denote ssvT.denote rsvT.denote)
    (hHk : HooksCAgrees hsEncFn HBounded (HBoundedPost := HBoundedPost) (VROk := VROk) hkC hk)
    (L : ℕ) (π : Policy)
    {Γ'} (esE : Expr OO Γ'
      (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (pE : Expr OO Γ' .bool)
    (ρ : Env Γ')
    (es : EState (VP γvT.denote T svT.denote ssvT.denote rsvT.denote) M (Header T × E) HS)
    (P : Party)
    (hHB : HBounded es.h) (hBound : SMStateBoundedEngine L es.g)
    (hes : esE.eval ρ = esEnc vpTblEnc hsEncFn es)
    (hp : pE.eval ρ = partyEnc P) :
    (corrECPaper hkC L π esE pE).eval ρ =
      Prod.map (Option.map ckaPsEnc) (esEnc vpTblEnc hsEncFn) <$>
        (corrEPaper hk π P).run es := by
  unfold corrECPaper corrEPaper abortE
  rw [eval_bind_ret]
  have h0 : (Expr.pair esE pE).eval ρ = (esEnc vpTblEnc hsEncFn es, partyEnc P) := by
    simp [Expr.eval, hes, hp]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := .prod (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT) .bool)
    (esEnc vpTblEnc hsEncFn es, partyEnc P) ρ
  rw [eval_ite]
  have hCorrOk : (cCorrAllowedPaperE L (esG (.fst (Expr.v0 (O := OO)))) (.snd .v0)).eval ρ₁ =
      es.g.corrAllowedPaper P :=
    cCorrAllowedPaperE_eval vpTblEnc (O' := OO) L (esG (.fst .v0)) (.snd .v0) ρ₁ es.g P
      hBound.chall_le rfl rfl
  have hRefuse : (orE (esAbort (.fst (Expr.v0 (O := OO))))
      (orE (cGsWin (esG (.fst .v0)))
        (.not (cCorrAllowedPaperE L (esG (.fst .v0)) (.snd .v0))))).eval ρ₁ =
      (es.abort || es.g.win || !(es.g.corrAllowedPaper P)) := by
    simp only [orE_eval, not_eval, hCorrOk]
    simp [ρ₁, esAbort, cGsWin, esG, esEnc, cGsEnc, Expr.eval, Expr.v0, Bool.or_assoc]
  rw [hRefuse]
  by_cases href : (es.abort || es.g.win || !(es.g.corrAllowedPaper P))
  · simp only [StateT.run_bind, StateT.run_get, pure_bind, href, ↓reduceIte,
      eval_ret, StateT.run_pure, map_pure, Prod.map]
    simp [ρ₁, Expr.eval, Expr.v0]
  · simp only [href, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, StateT.run_get, pure_bind]
    rw [eval_ite]
    have hAfter : (cAfterCorrE L (esG (.fst (Expr.v0 (O := OO)))) (.snd .v0)).eval ρ₁ =
        cGsEnc vpTblEnc (es.g.afterCorr P) :=
      cAfterCorrE_eval vpTblEnc (O' := OO) L (esG (.fst .v0)) (.snd .v0) ρ₁ es.g P
        hBound.trans_le hBound.comp_u rfl rfl
    have hAfterLeaks : (es.g.afterCorr P).leaks.length ≤ L := afterCorr_leaks_le hBound P
    have hLeakDoom : (leakDoomE L π (esG (.fst (Expr.v0 (O := OO))))
        (cAfterCorrE L (esG (.fst .v0)) (.snd .v0))).eval ρ₁ =
        π.leakDoom es.g (es.g.afterCorr P) :=
      leakDoomE_eval vpTblEnc (O' := OO) L π (esG (.fst .v0))
        (cAfterCorrE L (esG (.fst .v0)) (.snd .v0)) ρ₁ es.g (es.g.afterCorr P)
        hAfterLeaks rfl hAfter
    have hCorrDoom : (corrDoomE π (esG (.fst (Expr.v0 (O := OO)))) (.snd .v0)).eval ρ₁ =
        π.corrDoom es.g P :=
      corrDoomE_eval vpTblEnc (O' := OO) π (esG (.fst .v0)) (.snd .v0) ρ₁ es.g P rfl rfl
    have hDoom : (orE (leakDoomE L π (esG (.fst (Expr.v0 (O := OO))))
        (cAfterCorrE L (esG (.fst .v0)) (.snd .v0)))
        (corrDoomE π (esG (.fst (Expr.v0 (O := OO)))) (.snd .v0))).eval ρ₁ =
        (π.leakDoom es.g (es.g.afterCorr P) || π.corrDoom es.g P) := by
      rw [orE_eval, hLeakDoom, hCorrDoom]
    rw [hDoom]
    by_cases hdoom : (π.leakDoom es.g (es.g.afterCorr P) || π.corrDoom es.g P)
    · simp only [hdoom, ↓reduceIte, eval_ret, pair_eval,
        StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, map_pure, Prod.map]
      have hSetAb := esSetAbort_eval vpTblEnc hsEncFn (O' := OO) (.fst .v0) (.bool true) ρ₁ es rfl
      simp only [Expr.eval] at hSetAb ⊢
      rw [hSetAb]; rfl
    · simp only [hdoom, Bool.false_eq_true, ↓reduceIte, eval_bind]
      have hStP : (pGet (cGsSt (esG (.fst (Expr.v0 (O := OO))))) (.snd .v0)).eval ρ₁ =
          vpTblEnc (es.g.st P) :=
        pGet_eval (cGsSt (esG (.fst .v0))) (.snd .v0) ρ₁
          (fun Q => vpTblEnc (es.g.st Q)) P rfl rfl
      have hRev := hHk.reveal_eval (esH (.fst .v0)) (esG (.fst .v0)) (.snd .v0)
        (pGet (cGsSt (esG (.fst .v0))) (.snd .v0)) ρ₁ es.h es.g P (es.g.st P) hHB
        rfl rfl rfl hStP
      rw [hRev, bind_map_left, run_liftH_bind, map_bind]
      refine bind_congr fun ⟨revRes, h'⟩ => ?_
      rcases revRes with _ | st
      · simp [ρ₁, Comp.eval, StateT.run_modify,
          Prod.map, esMk, esG, esEnc, Expr.eval, Expr.v0, Expr.v1]
      · simp only [Prod.map, Option.map_some]
        set ρ₂ := Env.cons (t := psTy) (ckaPsEnc st)
          (Env.cons (t := .prod (.opt psTy) hsT) (some (ckaPsEnc st), hsEncFn h') ρ₁)
        change (Comp.ret _).eval ρ₂ = _
        have hAfter2 : (cAfterCorrE L (esG (.fst (Expr.v2 (O := OO)))) (.snd .v2)).eval ρ₂ =
            cGsEnc vpTblEnc (es.g.afterCorr P) :=
          cAfterCorrE_eval vpTblEnc (O' := OO) L (esG (.fst .v2)) (.snd .v2) ρ₂ es.g P
            hBound.trans_le hBound.comp_u rfl rfl
        simp only [eval_ret, esMk, pair_eval, some_eval, hAfter2]
        rfl

theorem rdec_implECPaper_eval {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S} {HS : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hDefaultE : defaultE = default)
    (hsEncFn : HS → hsT.denote) (HBounded : HS → Prop) {HBoundedPost : HS → Prop}
    {VROk : rsvT.denote → Prop}
    (hkC : HooksC OO I' γvT svT ssvT rsvT hsT)
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins
      γvT.denote svT.denote ssvT.denote rsvT.denote)
    (hHk : HooksCAgrees hsEncFn HBounded (HBoundedPost := HBoundedPost) (VROk := VROk) hkC hk)
    (L Δ qep maxSkip : ℕ) (cfgC : ConfigEC OO) (cfg : Config M)
    (hCfg : ConfigECAgrees cfgC cfg)
    (heqT : eqT = (· == ·))
    (heqM : eqM = (· == ·))
    (heqE : eqE = (· == ·))
    (π : Policy)
    {Γ'} (esE : Expr OO Γ'
      (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (qE : Expr OO Γ' (ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E))
    (ρ : Env Γ')
    (es : EState (VP γvT.denote T svT.denote ssvT.denote rsvT.denote) M (Header T × E) HS)
    (q : (SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hHB : HBounded es.h) (hBound : SMStateBoundedEngine L es.g)
    (hVR : ∀ P t v, (es.g.st P).vR t = some v → VROk v)
    (hes : esE.eval ρ = esEnc vpTblEnc hsEncFn es)
    (hq : qE.eval ρ = (ckaSMCodec KC Γ CCoins T I KR RSt K SS RS M E).qenc q) :
    ((fun p => ((ckaSMCodec KC Γ CCoins T I KR RSt K SS RS M E).rdec q p.1, p.2)) <$>
      (implECPaper hkC L Δ qep maxSkip cfgC π esE qE).eval ρ) =
      Prod.map id (esEnc vpTblEnc hsEncFn) <$>
        (implEDFPaper hk Δ qep maxSkip cfg π (.inr (.inl q))).run es := by
  unfold implECPaper implEDFPaper
  rw [eval_bind_ret]
  have h0 : (Expr.pair esE qE).eval ρ =
      (esEnc vpTblEnc hsEncFn es,
       (ckaSMCodec KC Γ CCoins T I KR RSt K SS RS M E).qenc q) := by
    simp [Expr.eval, hes, hq]
  rw [h0]; clear h0
  rcases q with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
  · simp only [ckaSMCodec, Comp.eval, Expr.eval, Expr.v0, Env.get_cons_zero]
    rw [transmitEC_eval hDefaultE hsEncFn HBounded hkC hk hHk L Δ qep π
          _ _ _ es P m r hHB hBound rfl rfl]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
    refine bind_congr fun ⟨res, es'⟩ => ?_
    rfl
  · simp only [ckaSMCodec, Comp.eval, Expr.eval, Expr.v0, Env.get_cons_zero]
    rw [challEC_eval hDefaultE hsEncFn HBounded hkC hk hHk L Δ qep cfgC cfg hCfg π
          _ _ _ es P m₀ m₁ r hHB hBound rfl rfl]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
    refine bind_congr fun ⟨res, es'⟩ => ?_
    rfl
  · simp only [ckaSMCodec, Comp.eval, Expr.eval, Expr.v0, Env.get_cons_zero]
    rw [deliverEC_eval hsEncFn HBounded hkC hk hHk L maxSkip cfgC cfg hCfg heqT heqM heqE
          _ _ _ es P c hHB hBound (hVR P) rfl rfl]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
    refine bind_congr fun ⟨res, es'⟩ => ?_
    rcases res with _ | (_ | m') <;> rfl
  · simp only [ckaSMCodec, Comp.eval, Expr.eval, Expr.v0, Env.get_cons_zero]
    rw [injectEC_eval hsEncFn HBounded hkC hk hHk L Δ qep cfgC cfg hCfg heqT heqE
          _ _ _ es P c hHB hBound (hVR P) rfl rfl]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
    refine bind_congr fun ⟨res, es'⟩ => ?_
    rcases res with _ | (_ | m') <;> rfl
  · simp only [ckaSMCodec, Comp.eval, Expr.eval, Expr.v0, Env.get_cons_zero]
    rw [corrECPaper_eval hsEncFn HBounded hkC hk hHk L π
          _ _ _ es P hHB hBound rfl rfl]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
    refine bind_congr fun ⟨res, es'⟩ => ?_
    rcases res with _ | st
    · rfl
    · simp [Prod.map]

theorem rdecDF_implECDFPaper_eval {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S} {HS : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hDefaultE : defaultE = default)
    (hsEncFn : HS → hsT.denote) (HBounded : HS → Prop) {HBoundedPost : HS → Prop}
    {VROk : rsvT.denote → Prop}
    (hkC : HooksC OO I' γvT svT ssvT rsvT hsT)
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins
      γvT.denote svT.denote ssvT.denote rsvT.denote)
    (hHk : HooksCAgrees hsEncFn HBounded (HBoundedPost := HBoundedPost) (VROk := VROk) hkC hk)
    (L Δ qep maxSkip : ℕ) (cfgC : ConfigEC OO) (cfg : Config M)
    (hCfg : ConfigECAgrees cfgC cfg)
    (heqT : eqT = (· == ·))
    (heqM : eqM = (· == ·))
    (heqE : eqE = (· == ·))
    (π : Policy)
    {Γ'} (esE : Expr OO Γ'
      (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (qE : Expr OO Γ' (ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E))
    (ρ : Env Γ')
    (es : EState (VP γvT.denote T svT.denote ssvT.denote rsvT.denote) M (Header T × E) HS)
    (q : (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hHB : HBounded es.h) (hBound : SMStateBoundedEngine L es.g)
    (hVR : ∀ P t v, (es.g.st P).vR t = some v → VROk v)
    (hes : esE.eval ρ = esEnc vpTblEnc hsEncFn es)
    (hq : qE.eval ρ = (ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).qenc q) :
    ((fun p => ((ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).rdec q p.1, p.2)) <$>
      (implECDFPaper hkC L Δ qep maxSkip cfgC π esE qE).eval ρ) =
      Prod.map id (esEnc vpTblEnc hsEncFn) <$>
        (implEDFPaper hk Δ qep maxSkip cfg π (.inr q)).run es := by
  unfold implECDFPaper
  rw [eval_bind_ret]
  have h0 : (Expr.pair esE qE).eval ρ =
      (esEnc vpTblEnc hsEncFn es,
       (ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).qenc q) := by
    simp [Expr.eval, hes, hq]
  rw [h0]; clear h0
  rcases q with q | ⟨P, c, c'⟩
  · simp only [ckaSMCodecDF, Comp.eval, Expr.eval, Expr.v0, Expr.v1,
      Env.get_cons_zero, map_eq_bind_pure_comp, bind_assoc, pure_bind]
    have hSub := rdec_implECPaper_eval hDefaultE hsEncFn HBounded hkC hk hHk L Δ qep maxSkip
      cfgC cfg hCfg heqT heqM heqE π (.fst .v1) .v0
      (Env.cons (t := ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E)
        ((ckaSMCodec KC Γ CCoins T I KR RSt K SS RS M E).qenc q)
        (Env.cons (t := .prod (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)
          hsT) (ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E))
          (esEnc vpTblEnc hsEncFn es,
           .inl ((ckaSMCodec KC Γ CCoins T I KR RSt K SS RS M E).qenc q)) ρ))
      es q hHB hBound hVR rfl rfl
    simp only [map_eq_bind_pure_comp] at hSub
    exact hSub
  · simp only [ckaSMCodecDF, implEDFPaper, Comp.eval, Expr.eval, Expr.v0, Expr.v1,
      Env.get_cons_zero]
    rw [deliverForgeEC_eval hsEncFn HBounded hkC hk hHk L Δ qep cfgC cfg hCfg heqT heqE
          _ _ _ es P c c' hHB hBound (hVR P) rfl rfl]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
    refine bind_congr fun ⟨res, es'⟩ => ?_
    rcases res with _ | (_ | m') <;> rfl

theorem corrEPaper_inv {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    {L B q : ℕ} (π : Policy)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (P : Party)
    (hInv : SMEngineInv L B (q + 1) es.g) :
    ∀ res ∈ support ((corrEPaper hk π P).run es), SMEngineInv L B q res.2.g := by
  intro ⟨out, es'⟩ hmem
  have hInvQ : SMEngineInv L B q es.g := hInv.mono (Nat.le_succ q)
  unfold corrEPaper abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases href : (es.abort || es.g.win || !(es.g.corrAllowedPaper P))
  · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hInvQ
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hmem
    by_cases hdoom : (π.leakDoom es.g (es.g.afterCorr P) || π.corrDoom es.g P)
    · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
        pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInvQ
    · simp only [hdoom, Bool.false_eq_true, ↓reduceIte] at hmem
      rw [run_liftH_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨revRes, h'⟩, _, hmem⟩ := hmem
      rcases revRes with _ | st
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hInvQ
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩
        exact hInv.afterCorr P

theorem implEDFPaper_inv [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    {L B q Δ qep maxSkip : ℕ} (cfg : Config M) (π : Policy)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (t : (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hInv : SMEngineInv L B (q + 1) es.g) :
    ∀ res ∈ support ((implEDFPaper hk Δ qep maxSkip cfg π (.inr t)).run es),
      SMEngineInv L B q res.2.g := by
  rcases t with (t4 | P) | arg
  · exact implE_inv hk cfg π es (.inl t4) hInv
  · exact corrEPaper_inv hk π es P hInv
  · exact deliverForgeE_inv hk cfg es arg hInv

theorem implEDFPaper_vrInv [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    {VROkStep : ℕ → rsV → Prop}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    (hVRHk : HooksVRInv VROkStep hk)
    {L B q Δ qep maxSkip : ℕ} (cfg : Config M) (π : Policy)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (t : (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hInv : SMEngineInv L B (q + 1) es.g)
    (hVR : SMVRInv VROkStep B (q + 1) es.g) :
    ∀ res ∈ support ((implEDFPaper hk Δ qep maxSkip cfg π (.inr t)).run es),
      SMVRInv VROkStep B q res.2.g := by
  have hVRQ : SMVRInv VROkStep B q es.g :=
    SMVRInv.mono (VROkStep := VROkStep) hVRHk.mono (Nat.le_succ q) hVR
  rcases t with (t4 | P) | arg
  · exact implE_vrInv hk hVRHk cfg π es (.inl t4) hInv hVR
  · intro ⟨out, es'⟩ hmem
    change (out, es') ∈ support ((corrEPaper hk π P).run es) at hmem
    unfold corrEPaper abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases href : (es.abort || es.g.win || !(es.g.corrAllowedPaper P))
    · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hVRQ
    · simp only [href, Bool.false_eq_true, ↓reduceIte] at hmem
      by_cases hdoom : (π.leakDoom es.g (es.g.afterCorr P) || π.corrDoom es.g P)
      · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
          pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hVRQ
      · simp only [hdoom, Bool.false_eq_true, ↓reduceIte,
          run_liftH_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨revRes, h'⟩, _, hmem⟩ := hmem
        rcases revRes with _ | st
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hVRQ
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hVRQ
  · exact deliverForgeE_vrInv hk hVRHk cfg es arg hInv hVR

theorem corrEPaper_b_eq {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    (π : Policy)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (P : Party) :
    ∀ res ∈ support ((corrEPaper hk π P).run es), res.2.g.b = es.g.b := by
  intro ⟨out, es'⟩ hmem
  unfold corrEPaper abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases href : (es.abort || es.g.win || !(es.g.corrAllowedPaper P))
  · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; rfl
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hmem
    by_cases hdoom : (π.leakDoom es.g (es.g.afterCorr P) || π.corrDoom es.g P)
    · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
        pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; rfl
    · simp only [hdoom, Bool.false_eq_true, ↓reduceIte] at hmem
      rw [run_liftH_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨revRes, h'⟩, _, hmem⟩ := hmem
      rcases revRes with _ | st
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; rfl
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; rfl

theorem implEDFPaper_b_eq [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    {Δ qep maxSkip : ℕ} (cfg : Config M) (π : Policy)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (t : (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain) :
    ∀ res ∈ support ((implEDFPaper hk Δ qep maxSkip cfg π (.inr t)).run es),
      res.2.g.b = es.g.b := by
  rcases t with (t4 | P) | arg
  · exact implE_b_eq hk cfg π es (.inl t4)
  · exact corrEPaper_b_eq hk π es P
  · exact deliverForgeE_b_eq hk cfg es arg

theorem simulateQ_implECDFPaper_vr_eq {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S} {HS : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hDefaultE : defaultE = default)
    (hU : ∀ n, I'.fwdU n = query (spec := unifSpec + TSpec) (.inl n))
    (hsEncFn : HS → hsT.denote) (HBounded : HS → Prop) {HBoundedPost : HS → Prop}
    {VROkStep : ℕ → rsvT.denote → Prop}
    (hkC : HooksC OO I' γvT svT ssvT rsvT hsT)
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins
      γvT.denote svT.denote ssvT.denote rsvT.denote)
    (L B Δ qep maxSkip : ℕ)
    (hHk : HooksCAgrees hsEncFn HBounded (HBoundedPost := HBoundedPost)
      (VROk := VROkStep B) hkC hk)
    (hVRHk : HooksVRInv VROkStep hk)
    (cfgC : ConfigEC OO) (cfg : Config M)
    (hCfg : ConfigECAgrees cfgC cfg)
    (heqT : eqT = (· == ·))
    (heqM : eqM = (· == ·))
    (heqE : eqE = (· == ·))
    (π : Policy)
    (hHbStep : ∀ (t : (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
      (es : EState (VP γvT.denote T svT.denote ssvT.denote rsvT.denote) M (Header T × E) HS),
      HBounded es.h → SMStateBoundedEngine L es.g →
      ∀ res ∈ support ((implEDFPaper hk Δ qep maxSkip cfg π (.inr t)).run es), HBounded res.2.h) :
    ∀ {α : Type}
      {oa : OracleComp (unifSpec + SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) α}
      {qAdv : ℕ},
      oa.IsQueryBoundP
        (isGameQuery (G := SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) qAdv →
      ∀ (es : EState (VP γvT.denote T svT.denote ssvT.denote rsvT.denote) M (Header T × E) HS),
        HBounded es.h → SMEngineInv L B qAdv es.g → SMVRInv VROkStep B qAdv es.g →
        (simulateQ
          (handlerImpl (C := ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E)
            (implECDFPaper hkC L Δ qep maxSkip cfgC π .v0 .v1)) oa).run
          (esEnc vpTblEnc hsEncFn es) =
          (Prod.map id (esEnc vpTblEnc hsEncFn) <$>
            (simulateQ (implEDFPaper hk Δ qep maxSkip cfg π) oa).run es) ∧
        ∀ res ∈ support ((simulateQ (implEDFPaper hk Δ qep maxSkip cfg π) oa).run es),
          HBounded res.2.h ∧ SMEngineInv L B 0 res.2.g ∧ res.2.g.b = es.g.b := by
  intro α oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro qAdv _ es hHB hInv _
    refine ⟨by simp [simulateQ_pure, Prod.map], ?_⟩
    intro res hmem
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    exact ⟨hHB, hInv.mono (Nat.zero_le qAdv), rfl⟩
  | query_bind q mx ih =>
    intro qAdv hq es hHB hInv hVR
    rw [isQueryBoundP_query_bind_iff] at hq
    rw [run_simulateQ_query_bind, run_simulateQ_query_bind]
    cases q with
    | inl n =>
      have hCoinL :
          ((handlerImpl (C := ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E)
            (implECDFPaper hkC L Δ qep maxSkip cfgC π .v0 .v1)) (.inl n)).run
            (esEnc vpTblEnc hsEncFn es) =
          (fun u => (u, esEnc vpTblEnc hsEncFn es)) <$>
            query (spec := unifSpec + TSpec) (.inl n) := by
        simp [handlerImpl, hU, StateT.run_lift, map_eq_bind_pure_comp]
      have hCoinR :
          (implEDFPaper hk Δ qep maxSkip cfg π (.inl n)).run es =
          (fun u => (u, es)) <$> query (spec := unifSpec + TSpec) (.inl n) := by
        simp [implEDFPaper, coinsE, StateT.run_lift, map_eq_bind_pure_comp]
      rw [hCoinL, hCoinR, bind_map_left, bind_map_left, map_bind]
      refine ⟨bind_congr fun u => (ih u (hq.2 u) es hHB hInv hVR).1, ?_⟩
      intro res hmem
      rw [mem_support_bind_iff] at hmem
      obtain ⟨u, _, hmem⟩ := hmem
      exact (ih u (hq.2 u) es hHB hInv hVR).2 res hmem
    | inr t =>
      have hpos : 0 < qAdv := hq.1.resolve_left (by simp [isGameQuery])
      obtain ⟨m, rfl⟩ : ∃ m, qAdv = m + 1 := ⟨qAdv - 1, by omega⟩
      have hqm : ∀ u, (mx u).IsQueryBoundP
          (isGameQuery (G := SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) m := by
        intro u; simpa [isGameQuery] using hq.2 u
      have hVRB : ∀ P t₀ v, (es.g.st P).vR t₀ = some v → VROkStep B v :=
        fun P t₀ v hv => hVRHk.mono (Nat.sub_le B (m + 1)) (hVR P t₀ v hv)
      have hStep :
          ((handlerImpl (C := ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E)
            (implECDFPaper hkC L Δ qep maxSkip cfgC π .v0 .v1)) (.inr t)).run
            (esEnc vpTblEnc hsEncFn es) =
          Prod.map id (esEnc vpTblEnc hsEncFn) <$>
            (implEDFPaper hk Δ qep maxSkip cfg π (.inr t)).run es := by
        simp only [handlerImpl, StateT.run_mk,
          ← rdecDF_implECDFPaper_eval hDefaultE hsEncFn HBounded hkC hk hHk L Δ qep maxSkip
            cfgC cfg hCfg heqT heqM heqE π .v0 .v1
            (.cons (esEnc vpTblEnc hsEncFn es)
              (.cons ((ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).qenc t) .nil))
            es t hHB hInv.toBoundedEngine hVRB rfl rfl,
          map_eq_bind_pure_comp, Function.comp_def]
      rw [hStep, bind_map_left, map_bind]
      refine ⟨OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es₁⟩ hmem => ?_, ?_⟩
      · have hHB₁ := hHbStep t es hHB hInv.toBoundedEngine (u, es₁) hmem
        have hInv₁ := implEDFPaper_inv hk cfg π es t hInv (u, es₁) hmem
        have hVR₁ := implEDFPaper_vrInv hk hVRHk cfg π es t hInv hVR (u, es₁) hmem
        exact (ih u (hqm u) es₁ hHB₁ hInv₁ hVR₁).1
      · intro res hmem
        rw [mem_support_bind_iff] at hmem
        obtain ⟨⟨u, es₁⟩, hmem₁, hmem₂⟩ := hmem
        have hHB₁ := hHbStep t es hHB hInv.toBoundedEngine (u, es₁) hmem₁
        have hInv₁ := implEDFPaper_inv hk cfg π es t hInv (u, es₁) hmem₁
        have hVR₁ := implEDFPaper_vrInv hk hVRHk cfg π es t hInv hVR (u, es₁) hmem₁
        have hb₁ := implEDFPaper_b_eq hk cfg π es t (u, es₁) hmem₁
        obtain ⟨hHB₂, hInv₂, hb₂⟩ := (ih u (hqm u) es₁ hHB₁ hInv₁ hVR₁).2 res hmem₂
        exact ⟨hHB₂, hInv₂, hb₂.trans hb₁⟩

@[simp] theorem corrECPaper_queries_eq
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : Ty S}
    (hk : HooksC OO I' γvT svT ssvT rsvT hsT) (L : ℕ) (π : Policy) {Γ'}
    (es : Expr OO Γ'
      (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (p : Expr OO Γ' .bool) (fQ : I'.Tag → ℕ) (fS : I'.smp.Samp → ℕ) :
    (corrECPaper hk L π es p).queries fQ fS = (corrEC hk L π es p).queries fQ fS := rfl

@[simp] theorem implECPaper_queries_eq
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : Ty S}
    (hk : HooksC OO I' γvT svT ssvT rsvT hsT) (L Δ qep maxSkip : ℕ) (cfg : ConfigEC OO)
    (π : Policy) {Γ'}
    (es : Expr OO Γ'
      (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (q : Expr OO Γ' (ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E))
    (fQ : I'.Tag → ℕ) (fS : I'.smp.Samp → ℕ) :
    (implECPaper hk L Δ qep maxSkip cfg π es q).queries fQ fS =
      (implEC hk L Δ qep maxSkip cfg π es q).queries fQ fS := rfl

@[simp] theorem implECDFPaper_queries_eq
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : Ty S}
    (hk : HooksC OO I' γvT svT ssvT rsvT hsT) (L Δ qep maxSkip : ℕ) (cfg : ConfigEC OO)
    (π : Policy) {Γ'}
    (es : Expr OO Γ'
      (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (q : Expr OO Γ' (ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E))
    (fQ : I'.Tag → ℕ) (fS : I'.smp.Samp → ℕ) :
    (implECDFPaper hk L Δ qep maxSkip cfg π es q).queries fQ fS =
      (implECDF hk L Δ qep maxSkip cfg π es q).queries fQ fS := rfl

end CryptoGames.SM.Engine

namespace CryptoGames.SM.Construction

open Engine Engine.RedPRNG CKA PRFPRNG

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}

local notation "S" => ckaSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrTy" => ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrCtTy" => ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "psTy" => ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "rrTy" => ckaRrTy KC Γ CCoins T I KR RSt K SS RS M E

/-! ## `redCKAAuthDFPaperProg` reduction -/

section HooksCKACDFPaper

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

theorem runCKADFPaper_eq_bind_initCKARaw
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (Δcka qep : ℕ) (mo : Mode) (cfg : Config M) (π : Policy) (b : Bool)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) :
    DeliverForge.engRunDFPaper (hooksCKA cka prng fs Δcka mo) (2 + Δcka) qep fs.maxSkip
      cfg π (initCKA cka prng fs lam mo) {} b A =
      (do
        let es₀ ← initCKARaw cka prng fs lam mo b
        let res ←
          (simulateQ
            (DeliverForge.implEDFPaper (hooksCKA cka prng fs Δcka mo)
              (2 + Δcka) qep fs.maxSkip cfg π)
            A).run es₀
        return some res) := by
  unfold DeliverForge.engRunDFPaper initCKA initCKARaw
  simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  refine bind_congr fun kr => ?_
  rcases mo.tL with _ | l
  · simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind,
      bind_map_left]; rfl
  · simp only [StateT.run_pure, pure_bind]; rfl

/-- Costed `DeliverForge.redCKAAuthDFPaper` reduction over `SM.specDF`. -/
def redCKAAuthDFPaperProg (L B Δcka qep maxSkip : ℕ) (tL : Option ℕ) (t : ℕ) :
    CostedReduction OO II
      (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E)
      .unit .unit .bool .bool where
  σ := ckaEsTy
  init := rdsl [_] do
    es ← initCKAEStateC (raw ⟨true, tL, t⟩) false
    return ((), es)
  handle := rdsl [st, q] do
    implECDFPaper (raw (hooksCKAC B Δcka ⟨true, tL, t⟩)) L (raw (2 + Δcka)) qep maxSkip
      (raw (modeCfgEC OO ⟨true, tL, t⟩)) (raw (⟨true, tL, t⟩ : Mode).policy) st q
  finish := rdsl [st, _] do
    return authOutE L (raw (2 + Δcka)) (raw (⟨true, tL, t⟩ : Mode).policy) st

private theorem ckaVpEnc_eq_vpTblEnc :
    @ckaVpEnc KC Γ CCoins T I KR RSt K SS RS M E =
      vpTblEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (RSt := RSt)
        (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
        (γvT := .opt (.base .γ)) (svT := .base .sig) (ssvT := .base .ss) (rsvT := .base .rs) := rfl

@[simp] private theorem eval_v0_cons {Γ' : List (Ty S)} {t : Ty S} (x : t.denote) (ρ : Env Γ') :
    (Expr.v0 (O := OO)).eval (Env.cons x ρ) = x := rfl

@[simp] private theorem eval_bool_env {Γ' : List (Ty S)} (b : Bool) (ρ : Env Γ') :
    (Expr.bool (O := OO) b).eval ρ = b := rfl

@[simp] private theorem eval_ret_pair_unit_v0 {Γ' : List (Ty S)} {t : Ty S}
    (x : t.denote) (ρ : Env Γ') :
    (Comp.ret (O := OO) (I := II) (.pair .unit .v0)).eval (Env.cons x ρ) = pure ((), x) := rfl

/-- Step-indexed `vR`-invariant evaluation bridge for `redCKAAuthDFPaperProg`. -/
theorem redCKAAuthDFPaperProg_eval_vr
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B B_q Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    {VROkStep : ℕ → RS → Prop}
    (hInitA : ckaInitA = cka.initA)
    (hInitB : ckaInitB = cka.initB)
    (hSend : ckaSend = cka.send)
    (hRecv : ckaReceive = cka.receive)
    (hPrngInit : prngInit = prng.init)
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send)
    (hFsRecv : fsReceive = fs.receive)
    (heqT : eqT = (· == ·))
    (heqM : eqM = (· == ·))
    (heqE : eqE = (· == ·))
    (hDefaultE : defaultE = default)
    (hSampKR : sampKR = ($ᵗ KR : ProbComp KR))
    (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hVRHk : HooksVRInv VROkStep (hooksCKA cka prng fs Δcka ⟨true, tL, t⟩))
    (hInitR : ∀ k, VROkStep 0 (fs.initReceiver k))
    (hFsB : ∀ rs hdr e rs' i m, VROkStep B_q rs → fs.receive rs hdr e = some (rs', i, m) → i ≤ B)
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) (qAdv : ℕ)
    (hA : DeliverForge.MakesAtMostQueriesDF A qAdv) (hqB : qAdv ≤ B_q) :
    (redCKAAuthDFPaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L B Δcka qep fs.maxSkip tL t).eval (fun _ => A) () =
      DeliverForge.redCKAAuthDFPaper cka prng fs lam Δcka qep tL t A := by
  have hA' : A.IsQueryBoundP
      (isGameQuery (G := SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) qAdv := by
    refine hA.of_imp (fun x hx => ?_)
    rcases x with _ | _ <;> simp_all [isGameQuery]
  have hHk := hooksCKAC_agrees_vr (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (prngInit := prngInit) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    cka prng fs B Δcka ⟨true, tL, t⟩ hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend hFsRecv
    heqT hSampCCoins (fun k => hVRHk.mono (Nat.zero_le B_q) (hInitR k)) hFsB
  have hInit := initCKAEStateC_eval
    (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    cka prng fs hInitA hInitB hPrngInit hPrngUp hFsInitS hFsInitR hSampKR hSampKC
    ⟨true, tL, t⟩ (Expr.bool (O := OO) false) (Env.cons (t := .unit) () .nil)
  unfold redCKAAuthDFPaperProg CostedReduction.eval CostedReduction.impl
    DeliverForge.redCKAAuthDFPaper DeliverForge.authSimDFPaper
  dsimp only
  rw [eval_bind, hInit, ckaVpEnc_eq_vpTblEnc, runCKADFPaper_eq_bind_initCKARaw]
  simp only [bind_map_left, eval_bool_env, eval_ret_pair_unit_v0, bind_assoc, pure_bind]
  refine OracleComp.bind_congr_of_forall_mem_support
    (initCKARaw cka prng fs lam ⟨true, tL, t⟩ false) fun es₀ hes₀ => ?_
  have ⟨hInv₀, _⟩ := initCKARaw_inv cka prng fs lam ⟨true, tL, t⟩ false hqB hB1 hBB es₀ hes₀
  have hVR₀ := initCKARaw_vrInv (B := B_q) (qAdv := qAdv) cka prng fs lam ⟨true, tL, t⟩ false
    (fun k => hVRHk.mono (Nat.zero_le _) (hInitR k)) es₀ hes₀
  have ⟨hSim, hSimInv⟩ := Engine.simulateQ_implECDFPaper_vr_eq hDefaultE (fun _ => rfl) ckaHsEnc
    (fun _ => True)
    (hooksCKAC B Δcka ⟨true, tL, t⟩) (hooksCKA cka prng fs Δcka ⟨true, tL, t⟩)
    L B_q (2 + Δcka) qep fs.maxSkip hHk hVRHk
    (modeCfgEC OO ⟨true, tL, t⟩) (⟨true, tL, t⟩ : Mode).cfg
    (modeCfgEC_agrees ⟨true, tL, t⟩) heqT heqM heqE (⟨true, tL, t⟩ : Mode).policy
    (fun _ _ _ _ _ _ => trivial) hA' es₀ trivial hInv₀ hVR₀
  rw [hSim, bind_map_left]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨b', es'⟩ hes' => ?_
  obtain ⟨_, hInv', _⟩ := hSimInv (b', es') hes'
  have hBnd' := hInv'.toBoundedEngine
  have hOut := authOutE_eval vpTblEnc ckaHsEnc (O' := OO) L (2 + Δcka)
    (⟨true, tL, t⟩ : Mode).policy .v0
    (Env.cons (esEnc vpTblEnc ckaHsEnc es') (Env.cons (t := .bool) b' .nil))
    es' hBnd'.leaks_le hBnd'.corrs_le rfl
  simp only [eval_ret, Prod.map_apply, id_eq, hOut]
  rfl

@[simp] theorem redCKAAuthDFPaperProg_totalQueries (L B Δcka qep maxSkip : ℕ)
    (tL : Option ℕ) (t q : ℕ) :
    (redCKAAuthDFPaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L B Δcka qep maxSkip tL t).totalQueries (fun _ => 1) (fun _ => 0) q = q * 2 := by
  simp [CostedReduction.totalQueries, redCKAAuthDFPaperProg, Comp.queries]

end HooksCKACDFPaper

end CryptoGames.SM.Construction
