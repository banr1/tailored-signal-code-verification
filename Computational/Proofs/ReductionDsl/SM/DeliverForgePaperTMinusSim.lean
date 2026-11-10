/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperShiftedFS
public import Computational.Proofs.ReductionDsl.SM.DeliverForge
import ProofLib.SepLogic.WP.StateNorm
import Computational.Proofs.ReductionDsl.Notation

/-!
# Costed Off-Target Dead-Cell Triviality Handlers

Deep-embedded `ReductionDsl` expressions and handlers `cTrivialB1E`, `injectECB1`, and
`deliverForgeECB1` for `DeliverForge.trivB1`, `DeliverForge.injectEB1`, and
`DeliverForge.deliverForgeEB1`, with evaluation and engine-invariant preservation lemmas.
-/

@[expose] public section

set_option autoImplicit false

open ReductionDsl OracleSpec OracleComp
open scoped Computational.Proofs.ReductionDsl.Notation
open CryptoGames CryptoGames.CKA CryptoGames.PRFPRNG CryptoGames.FSAEAD CryptoGames.SM
open CryptoGames.SM.Engine CryptoGames.SM.Engine.RedPRNG CryptoGames.SM.Construction
open CryptoGames.SM.Construction.DeliverForge

namespace CryptoGames.SM.Engine

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}

local notation "S" => ckaSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrTy" => ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrCtTy" => ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "psTy" => ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "rrTy" => ckaRrTy KC Γ CCoins T I KR RSt K SS RS M E

/-- `DeliverForge.trivB1 tStar s pos` over `cGsTy vpT` with list-scan bound `L`. -/
def cTrivialB1E
    {O' : Ops S} {vpT : Ty S} {Γ'} (L tStar : ℕ) (s : Expr O' Γ' (cGsTy vpT))
    (pos : Expr O' Γ' posTy) : Expr O' Γ' .bool :=
  rdslExpr =>
    let ep0 := posEpoch pos
    let minEp :=
      if leN (cGsEpoch s).1 (cGsEpoch s).2 then (cGsEpoch s).1 else (cGsEpoch s).2
    orE (cTrivialE L (raw 2) s pos)
      ((!(ep0 == nat tStar)) && (ep0 < minEp))

theorem cTrivialB1E_eval {O' : Ops S} {vpT : Ty S} {VPt : Type}
    (vpEncFn : VPt → vpT.denote) {Γ'} (L tStar : ℕ) (s : Expr O' Γ' (cGsTy vpT))
    (pos : Expr O' Γ' posTy) (ρ : Env Γ') (st : GameState VPt M (Header T × E)) (pos₀ : Pos)
    (hTrans : st.trans.length ≤ L) (hComp : st.comp.dedup.length ≤ L)
    (hs : s.eval ρ = cGsEnc (vpT := vpT) vpEncFn st) (hpos : pos.eval ρ = posEnc pos₀) :
    (cTrivialB1E L tStar s pos).eval ρ = DeliverForge.trivB1 tStar st pos₀ := by
  unfold cTrivialB1E DeliverForge.trivB1
  rw [orE_eval, cTrivialE_eval vpEncFn L 2 s pos ρ st pos₀ hTrans hComp hs hpos]
  congr 1
  have hep0 : (posEpoch pos).eval ρ = pos₀.epoch := by
    simp [posEpoch, Expr.eval, hpos, posEnc]
  have hmin : (Expr.ite (leN (.fst (cGsEpoch s)) (.snd (cGsEpoch s)))
      (.fst (cGsEpoch s)) (.snd (cGsEpoch s))).eval ρ =
      min (st.epoch .A) (st.epoch .B) := by
    rw [ite_eval, leN_eval]
    have hA : (Expr.fst (cGsEpoch s)).eval ρ = st.epoch .A := by
      simp [cGsEpoch, Expr.eval, hs, cGsEnc]
    have hB : (Expr.snd (cGsEpoch s)).eval ρ = st.epoch .B := by
      simp [cGsEpoch, Expr.eval, hs, cGsEnc]
    rw [hA, hB]
    by_cases hle : st.epoch .A ≤ st.epoch .B <;> simp [hle, Nat.min_def]
  have hlt : (Expr.lt (posEpoch pos)
      (.ite (leN (.fst (cGsEpoch s)) (.snd (cGsEpoch s)))
        (.fst (cGsEpoch s)) (.snd (cGsEpoch s)))).eval ρ =
      decide (pos₀.epoch < min (st.epoch .A) (st.epoch .B)) := by
    change decide ((posEpoch pos).eval ρ <
      (Expr.ite (leN (.fst (cGsEpoch s)) (.snd (cGsEpoch s)))
        (.fst (cGsEpoch s)) (.snd (cGsEpoch s))).eval ρ) = _
    rw [hep0, hmin]
  have hne : (Expr.not (.eqN (posEpoch pos) (.nat tStar))).eval ρ =
      (pos₀.epoch != tStar) := by
    change (!decide ((posEpoch pos).eval ρ = tStar)) = (pos₀.epoch != tStar)
    rw [hep0]
    by_cases heq : pos₀.epoch = tStar <;> simp [heq, bne, BEq.beq]
  change ((Expr.not (.eqN (posEpoch pos) (.nat tStar))).eval ρ &&
    (Expr.lt (posEpoch pos)
      (.ite (leN (.fst (cGsEpoch s)) (.snd (cGsEpoch s)))
        (.fst (cGsEpoch s)) (.snd (cGsEpoch s)))).eval ρ) = _
  rw [hne, hlt]

theorem cTrivialB1E_cost_le_cTrivialE {O' : Ops S} {vpT : Ty S} {Γ'}
    (L tStar : ℕ) (s : Expr O' Γ' (cGsTy vpT)) (pos : Expr O' Γ' posTy) :
    (cTrivialB1E L tStar s pos).cost ≤
      (cTrivialE L 3 s pos).cost + 4 * s.cost + 2 * pos.cost + ReductionDsl.bits tStar + 41 := by
  have htriv : (cTrivialE L 2 s pos).cost = (cTrivialE L 3 s pos).cost := rfl
  simp only [cTrivialB1E, orE, posEpoch, leN, cGsEpoch, Expr.cost, htriv]
  omega

section Dir2OffTargetHandlers

variable
  {ckaInitA : KC → Γ} {ckaInitB : KC → Γ} {ckaSend : Γ → CCoins → Γ × T × I}
  {ckaReceive : Γ → T → Γ × I} {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS} {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E} {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
  {lam : I} {defaultE : E}

local notation "OO" =>
  ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE

/-- Costed `DeliverForge.injectEB1` handler with list-scan bound `L`. -/
def injectECB1
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : Ty S}
    (hk : HooksC OO I' γvT svT ssvT rsvT hsT)
    (L qep tStar : ℕ) (cfg : ConfigEC OO)
    {Γ'} (es : Expr OO Γ'
      (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO Γ' (.prod .bool hdrCtTy)) :
    Comp OO I' Γ'
      (.prod (.opt rrTy)
        (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT)) :=
  rdsl do
    (es0, p0, c0) ← return (es, arg)
    let s0 := esG es0
    let refuse :=
      orE (esAbort es0)
        (orE (cGsWin s0)
          (orE (isSomeE (cInTransitE L s0 (otherE p0) c0))
            (!(cSafeInjE (raw 2) s0))))
    if refuse then
      return (none, es0)
    else
      (vrRes, h') ← vRecvC hk (esH es0) s0 p0 (pGet (cGsSt s0) p0) c0 none
      match vrRes with
      | none => return (none, esMk s0 h' true)
      | some optTup =>
        match optTup with
        | none => return (some (.inl ()), esSetH es0 h')
        | some (st', t', i', m') =>
          let es3' := esSetH es0 h'
          if nat (qep + 1) < t' then
            return (some (.inl ()), es3')
          else
            let pos := (otherE p0, t', i')
            if cTrivialB1E L tStar s0 pos then
              (optAcc, es_acc) ← commitEC hk L es3' s0 p0 (pGet (cGsSt s0) p0) st' pos
              match optAcc with
              | none => return (none, es_acc)
              | some s_acc =>
                return (some (.inr (t', i', some m')), esSetG es_acc s_acc)
            else
              let g3 := if cfg.injectFullE t' then cGsSetWin s0 true else s0
              return (some (.inl ()), esSetG es3' g3)

/-- Costed `DeliverForge.deliverForgeEB1` handler with list-scan bound `L`. -/
def deliverForgeECB1
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : Ty S}
    (hk : HooksC OO I' γvT svT ssvT rsvT hsT)
    (L qep tStar : ℕ) (cfg : ConfigEC OO)
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
                if cTrivialB1E L tStar s0 pos then
                  (optAcc, es_acc) ← commitEC hk L es4' s0 p0 (pGet (cGsSt s0) p0) st' pos
                  match optAcc with
                  | none => return (none, es_acc)
                  | some s_acc =>
                    return (some (.inr (t', i', some m')), esSetG es_acc s_acc)
                else
                  let g4 := if cfg.injectFullE t' then cGsSetWin s0 true else s0
                  return (some (.inl ()), esSetG es4' g4)

private theorem add_slack_left {a b c d : ℕ} (h : b ≤ c + d) :
    a + b + 1 ≤ a + c + 1 + d := by omega

private theorem max_slack_right {a b c d e : ℕ} (h : c ≤ d + e) :
    a + max b c + 1 ≤ a + max b d + 1 + e := by omega

private theorem max_slack_right_eq {a1 a2 b c d e : ℕ} (ha : a1 = a2) (h : c ≤ d + e) :
    a1 + max b c + 1 ≤ a2 + max b d + 1 + e := by omega

private theorem add_slack_first {t1 t2 c d : ℕ} (h : t1 ≤ t2 + d) :
    t1 + c + 1 ≤ t2 + c + 1 + d := by omega

theorem injectECB1_cost_le_injectEC
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : Ty S}
    (hk : HooksC OO I' γvT svT ssvT rsvT hsT)
    (L qep tStar : ℕ) (cfg : ConfigEC OO)
    {Γ'} (es : Expr OO Γ'
      (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO Γ' (.prod .bool hdrCtTy)) :
    (injectECB1 hk L qep tStar cfg es arg).cost ≤
      (injectEC hk L 3 qep cfg es arg).cost + (ReductionDsl.bits tStar + 81) := by
  let vpT := @vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let decT : Ty S := .prod vpT (.prod .nat (.prod .nat (.base .msg)))
  let Γ0 : List (Ty S) := .prod (esTy vpT hsT) (.prod .bool hdrCtTy) :: Γ'
  let Γ1 : List (Ty S) :=
    decT :: .opt decT :: .prod (.opt (.opt decT)) hsT :: Γ0
  let s0 : Expr OO Γ0 (cGsTy vpT) := esG (.fst .v0)
  let p0 : Expr OO Γ0 .bool := .fst (.snd .v0)
  let c0 : Expr OO Γ0 hdrCtTy := .snd (.snd .v0)
  have href :
      (orE (esAbort (.fst .v0))
        (orE (cGsWin s0)
          (orE (isSomeE (cInTransitE L s0 (otherE p0) c0))
            (.not (cSafeInjE 2 s0))))).cost =
      (orE (esAbort (.fst .v0))
        (orE (cGsWin s0)
          (orE (isSomeE (cInTransitE L s0 (otherE p0) c0))
            (.not (cSafeInjE 3 s0))))).cost := rfl
  have htr := cTrivialB1E_cost_le_cTrivialE (O' := OO) (vpT := vpT) L tStar (Γ' := Γ1)
    (esG (.fst .v3))
    (.pair (otherE (.fst (.snd .v3))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hs3 : (esG (O' := OO) (vpT := vpT) (hsT := hsT) (Γ' := Γ1) (.fst .v3)).cost = 3 := rfl
  have hpos : (Expr.pair (O := OO) (Γ := Γ1) (otherE (.fst (.snd .v3)))
      (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0))))).cost = 13 := rfl
  rw [hs3, hpos] at htr
  have htr' :
      (cTrivialB1E (O' := OO) (vpT := vpT) L tStar (Γ' := Γ1) (esG (.fst .v3))
        (.pair (otherE (.fst (.snd .v3)))
          (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))).cost ≤
      (cTrivialE (O' := OO) (vpT := vpT) L 3 (Γ' := Γ1) (esG (.fst .v3))
        (.pair (otherE (.fst (.snd .v3)))
          (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))).cost +
        (ReductionDsl.bits tStar + 81) :=
    Nat.le_trans htr (by omega)
  dsimp only [injectECB1, injectEC, Comp.cost]
  with_reducible apply add_slack_left
  with_reducible apply max_slack_right_eq href
  with_reducible apply add_slack_left
  with_reducible apply max_slack_right
  with_reducible apply max_slack_right
  with_reducible apply max_slack_right
  with_reducible apply add_slack_first
  exact htr'

theorem deliverForgeECB1_cost_le_deliverForgeEC
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S (unifSpec + TSpec)}
    {γvT svT ssvT rsvT hsT : Ty S}
    (hk : HooksC OO I' γvT svT ssvT rsvT hsT)
    (L qep tStar : ℕ) (cfg : ConfigEC OO)
    {Γ'} (es : Expr OO Γ'
      (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO Γ' (.prod .bool (.prod hdrCtTy hdrCtTy))) :
    (deliverForgeECB1 hk L qep tStar cfg es arg).cost ≤
      (deliverForgeEC hk L 3 qep cfg es arg).cost + (ReductionDsl.bits tStar + 81) := by
  let vpT := @vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let decT : Ty S := .prod vpT (.prod .nat (.prod .nat (.base .msg)))
  let Γ0 : List (Ty S) :=
    .prod (esTy vpT hsT) (.prod .bool (.prod hdrCtTy hdrCtTy)) :: Γ'
  let Γ1 : List (Ty S) := cRecTy :: Γ0
  let Γ2 : List (Ty S) :=
    decT :: .opt decT :: .prod (.opt (.opt decT)) hsT :: Γ1
  have htr := cTrivialB1E_cost_le_cTrivialE (O' := OO) (vpT := vpT) L tStar (Γ' := Γ2)
    (esG (.fst .v4))
    (.pair (otherE (.fst (.snd .v4))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hs4 : (esG (O' := OO) (vpT := vpT) (hsT := hsT) (Γ' := Γ2) (.fst .v4)).cost = 3 := rfl
  have hpos : (Expr.pair (O := OO) (Γ := Γ2) (otherE (.fst (.snd .v4)))
      (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0))))).cost = 13 := rfl
  rw [hs4, hpos] at htr
  have htr' :
      (cTrivialB1E (O' := OO) (vpT := vpT) L tStar (Γ' := Γ2) (esG (.fst .v4))
        (.pair (otherE (.fst (.snd .v4)))
          (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))).cost ≤
      (cTrivialE (O' := OO) (vpT := vpT) L 3 (Γ' := Γ2) (esG (.fst .v4))
        (.pair (otherE (.fst (.snd .v4)))
          (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))).cost +
        (ReductionDsl.bits tStar + 81) :=
    Nat.le_trans htr (by omega)
  dsimp only [deliverForgeECB1, deliverForgeEC, Comp.cost]
  with_reducible apply add_slack_left
  with_reducible apply max_slack_right
  with_reducible apply max_slack_right
  with_reducible apply max_slack_right
  with_reducible apply add_slack_left
  with_reducible apply max_slack_right
  with_reducible apply max_slack_right
  with_reducible apply max_slack_right
  with_reducible apply add_slack_first
  exact htr'

theorem injectECB1_eval {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S} {HS : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hsEncFn : HS → hsT.denote) (HBounded : HS → Prop) {HBoundedPost : HS → Prop}
    {VROk : rsvT.denote → Prop}
    (hkC : HooksC OO I' γvT svT ssvT rsvT hsT)
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins
      γvT.denote svT.denote ssvT.denote rsvT.denote)
    (hHk : HooksCAgrees hsEncFn HBounded (HBoundedPost := HBoundedPost) (VROk := VROk) hkC hk)
    (L qep tStar : ℕ) (cfgC : ConfigEC OO) (cfg : Config M)
    (hCfg : ConfigECAgrees cfgC cfg)
    (heqT : eqT = (· == ·))
    (heqE : eqE = (· == ·))
    {Γ'} (esE : Expr OO Γ'
      (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (argE : Expr OO Γ' (.prod .bool hdrCtTy))
    (ρ : Env Γ')
    (es : EState (VP γvT.denote T svT.denote ssvT.denote rsvT.denote) M (Header T × E) HS)
    (P : Party) (c : Header T × E)
    (hHB : HBounded es.h) (hBound : SMStateBoundedEngine L es.g)
    (hVR : ∀ t v, (es.g.st P).vR t = some v → VROk v)
    (hes : esE.eval ρ = esEnc vpTblEnc hsEncFn es)
    (harg : argE.eval ρ = (partyEnc P, c)) :
    (injectECB1 hkC L qep tStar cfgC esE argE).eval ρ =
      Prod.map (Option.map smRrEnc) (esEnc vpTblEnc hsEncFn) <$>
        (DeliverForge.injectEB1 hk qep tStar cfg (P, c)).run es := by
  unfold injectECB1 DeliverForge.injectEB1 abortE
  rw [eval_bind_ret]
  have h0 : (Expr.pair esE argE).eval ρ =
      (esEnc vpTblEnc hsEncFn es, partyEnc P, c) := by
    simp [Expr.eval, hes, harg]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := .prod (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT)
      (.prod .bool hdrCtTy))
    (esEnc vpTblEnc hsEncFn es, partyEnc P, c) ρ
  rw [eval_ite]
  have hOther : (otherE (.fst (.snd (Expr.v0 (O := OO))))).eval ρ₁ = partyEnc P.other := by
    simp [ρ₁, otherE, partyEnc_other, Expr.eval, Expr.v0]
  have hInTr : (cInTransitE L (esG (.fst (Expr.v0 (O := OO))))
      (otherE (.fst (.snd .v0))) (.snd (.snd .v0))).eval ρ₁ =
      (es.g.inTransit P.other c).map cRecEnc :=
    cInTransitE_eval vpTblEnc L (esG (.fst .v0)) (otherE (.fst (.snd .v0))) (.snd (.snd .v0))
      ρ₁ es.g P.other heqT heqE hBound.trans_le rfl hOther
  have hSafeInj : (cSafeInjE 2 (esG (.fst (Expr.v0 (O := OO))))).eval ρ₁ = es.g.safeInj 2 :=
    cSafeInjE_eval vpTblEnc (O' := OO) 2 (esG (.fst .v0)) ρ₁ es.g rfl
  have hRefuse : (orE (esAbort (.fst (Expr.v0 (O := OO))))
      (orE (cGsWin (esG (.fst .v0)))
        (orE (isSomeE (cInTransitE L (esG (.fst .v0))
            (otherE (.fst (.snd .v0))) (.snd (.snd .v0))))
          (.not (cSafeInjE 2 (esG (.fst .v0))))))).eval ρ₁ =
      (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj 2)) := by
    simp only [orE_eval, isSomeE_eval, not_eval, hInTr, Option.isSome_map, hSafeInj]
    simp [ρ₁, esAbort, cGsWin, esG, esEnc, cGsEnc, Expr.eval, Expr.v0, Bool.or_assoc]
  rw [hRefuse]
  by_cases href : (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj 2))
  · simp only [StateT.run_bind, StateT.run_get, pure_bind, href, ↓reduceIte,
      eval_ret, StateT.run_pure, map_pure, Prod.map]
    simp [ρ₁, Expr.eval, Expr.v0]
  · rw [StateT.run_bind, StateT.run_get, pure_bind]
    simp only [href, Bool.false_eq_true, ↓reduceIte, eval_bind]
    have hStP : (pGet (cGsSt (esG (.fst (Expr.v0 (O := OO)))))
        (.fst (.snd .v0))).eval ρ₁ = vpTblEnc (es.g.st P) :=
      pGet_eval (cGsSt (esG (.fst .v0))) (.fst (.snd .v0)) ρ₁
        (fun Q => vpTblEnc (es.g.st Q)) P rfl rfl
    have hVRecv := vRecvC_eval hsEncFn HBounded hkC hk hHk
      (esH (.fst .v0)) (esG (.fst .v0)) (.fst (.snd .v0))
      (pGet (cGsSt (esG (.fst .v0))) (.fst (.snd .v0))) (.snd (.snd .v0)) .none
      ρ₁ es.h es.g P (es.g.st P) c none hHB hVR rfl rfl rfl hStP rfl rfl
    rw [hVRecv, bind_map_left, run_liftH_bind, map_bind]
    refine OracleComp.bind_congr_of_forall_mem_support
      ((vRecv hk es.g P (es.g.st P) c none).run es.h)
      fun ⟨vrRes, h'⟩ hvrMem => ?_
    have hHB' : HBoundedPost h' :=
      vRecv_bounded hsEncFn HBounded hkC hk hHk es.g P (es.g.st P) c none es.h hHB
        (vrRes, h') hvrMem
    rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
    · simp [ρ₁, Comp.eval, StateT.run_modify,
        Prod.map, esMk, esG, esEnc, Expr.eval, Expr.v0, Expr.v1]
    · simp only [Prod.map, Option.map_some, Option.map_none,
        StateT.run_pure, map_pure]
      set ρ₂ := Env.cons
        (t := .opt (.prod (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)
          (.prod .nat (.prod .nat (.base .msg)))))
        none
        (Env.cons
          (t := .prod
            (.opt (.opt (.prod (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)
              (.prod .nat (.prod .nat (.base .msg)))))) hsT)
          (some none, hsEncFn h') ρ₁)
      change (Comp.ret _).eval ρ₂ = _
      have hSetH := esSetH_eval vpTblEnc hsEncFn (O' := OO) (.fst .v2) (.snd .v1) ρ₂ es h' rfl rfl
      simp only [eval_ret, pair_eval, some_eval, inl_eval, hSetH]
      rfl
    · simp only [Prod.map, Option.map_some, id_eq]
      set ρ₃ := Env.cons
        (t := .prod (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)
          (.prod .nat (.prod .nat (.base .msg))))
        (vpTblEnc st', t', i', m')
        (Env.cons
          (t := .opt (.prod (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)
            (.prod .nat (.prod .nat (.base .msg)))))
          (some (vpTblEnc st', t', i', m'))
          (Env.cons
            (t := .prod
              (.opt (.opt (.prod (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)
                (.prod .nat (.prod .nat (.base .msg)))))) hsT)
            (some (some (vpTblEnc st', t', i', m')), hsEncFn h') ρ₁))
      change (Comp.ite (.lt (.nat (qep + 1)) (.fst (.snd .v0))) _ _).eval ρ₃ = _
      have hes3' : (esSetH (.fst (Expr.v3 (O := OO))) (.snd .v2)).eval ρ₃ =
          esEnc vpTblEnc hsEncFn { es with h := h' } :=
        esSetH_eval vpTblEnc hsEncFn (O' := OO) (.fst .v3) (.snd .v2) ρ₃ es h' rfl rfl
      rw [eval_ite]
      have hlt : (Expr.lt (.nat (qep + 1)) (.fst (.snd (Expr.v0 (O := OO))))).eval ρ₃ =
          decide (qep + 1 < t') := rfl
      rw [hlt]
      by_cases hqep : qep + 1 < t'
      · simp only [hqep, decide_true, ↓reduceIte, eval_ret, pair_eval, some_eval, inl_eval, hes3',
          StateT.run_pure, map_pure]
        rfl
      · simp only [hqep, decide_false, Bool.false_eq_true, ↓reduceIte, eval_ite]
        have hPos : (Expr.pair (otherE (.fst (.snd (Expr.v3 (O := OO)))))
            (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0))))).eval ρ₃ =
            posEnc ⟨P.other, t', i'⟩ := by
          simp [ρ₃, ρ₁, otherE, posEnc, partyEnc_other, Expr.eval, Expr.v0, Expr.v3]
        have hTriv : (cTrivialB1E L tStar (esG (.fst (Expr.v3 (O := OO))))
            (.pair (otherE (.fst (.snd .v3)))
              (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))).eval ρ₃ =
            DeliverForge.trivB1 tStar es.g ⟨P.other, t', i'⟩ :=
          cTrivialB1E_eval vpTblEnc (O' := OO) L tStar (esG (.fst .v3)) _
            ρ₃ es.g ⟨P.other, t', i'⟩ hBound.trans_le hBound.comp_le rfl hPos
        rw [hTriv]
        by_cases htriv : DeliverForge.trivB1 tStar es.g ⟨P.other, t', i'⟩
        · simp only [htriv, ↓reduceIte, eval_bind]
          have hSt3 : (pGet (cGsSt (esG (.fst (Expr.v3 (O := OO)))))
              (.fst (.snd .v3))).eval ρ₃ = vpTblEnc (es.g.st P) :=
            pGet_eval (cGsSt (esG (.fst .v3))) (.fst (.snd .v3)) ρ₃
              (fun Q => vpTblEnc (es.g.st Q)) P rfl rfl
          have hCom := commitEC_eval hsEncFn HBounded hkC hk hHk L
            (esSetH (.fst .v3) (.snd .v2)) (esG (.fst .v3)) (.fst (.snd .v3))
            (pGet (cGsSt (esG (.fst .v3))) (.fst (.snd .v3))) (.fst .v0)
            (.pair (otherE (.fst (.snd .v3)))
              (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
            ρ₃ { es with h := h' } es.g P (es.g.st P) st' ⟨P.other, t', i'⟩ hHB' hBound
            hes3' rfl rfl hSt3 rfl hPos
          rw [hCom, StateT.run_bind, bind_map_left, map_bind]
          refine bind_congr fun ⟨cmRes, es''⟩ => ?_
          rcases cmRes with _ | s_acc
          · simp [ρ₃, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
          · simp only [Prod.map, Option.map_some,
              StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, map_pure]
            set ρ₄ := Env.cons
              (t := cGsTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
              (cGsEnc vpTblEnc s_acc)
              (Env.cons
                (t := .prod
                   (.opt (cGsTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
                   (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
                (some (cGsEnc vpTblEnc s_acc), esEnc vpTblEnc hsEncFn es'') ρ₃)
            change (Comp.ret _).eval ρ₄ = _
            have hSetG := esSetG_eval vpTblEnc hsEncFn (O' := OO) (.snd .v1) .v0
              ρ₄ es'' s_acc rfl rfl
            simp only [eval_ret, pair_eval, some_eval, inr_eval, hSetG]
            rfl
        · simp only [htriv, Bool.false_eq_true, ↓reduceIte, eval_ret, pair_eval, some_eval]
          have hInjFull : (cfgC.injectFullE (.fst (.snd .v0))).eval ρ₃ = cfg.injectFull t' :=
            hCfg.injectFull_eq (.fst (.snd .v0)) ρ₃
          have hSetWin := cGsSetWin_eval vpTblEnc (O' := OO)
            (esG (.fst .v3)) (.bool true) ρ₃ es.g rfl
          have hg3 : (Expr.ite (cfgC.injectFullE (.fst (.snd .v0)))
              (cGsSetWin (esG (.fst .v3)) (.bool true)) (esG (.fst .v3))).eval ρ₃ =
              cGsEnc vpTblEnc (if cfg.injectFull t' then { es.g with win := true } else es.g) := by
            rw [ite_eval, hInjFull, hSetWin]
            by_cases hf : cfg.injectFull t' <;> simp [hf, ρ₃, ρ₁, esG, esEnc, Expr.eval, Expr.v3]
          have hSetG := esSetG_eval vpTblEnc hsEncFn (O' := OO)
            (esSetH (.fst .v3) (.snd .v2))
            (.ite (cfgC.injectFullE (.fst (.snd .v0)))
              (cGsSetWin (esG (.fst .v3)) (.bool true)) (esG (.fst .v3)))
            ρ₃ { es with h := h' }
            (if cfg.injectFull t' then { es.g with win := true } else es.g) hes3' hg3
          rw [hSetG]
          by_cases hf : cfg.injectFull t' <;>
            simp [hf, StateT.run_modify, StateT.run_pure, smRrEnc, Expr.eval]

theorem deliverForgeECB1_eval {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S} {HS : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hsEncFn : HS → hsT.denote) (HBounded : HS → Prop) {HBoundedPost : HS → Prop}
    {VROk : rsvT.denote → Prop}
    (hkC : HooksC OO I' γvT svT ssvT rsvT hsT)
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins
      γvT.denote svT.denote ssvT.denote rsvT.denote)
    (hHk : HooksCAgrees hsEncFn HBounded (HBoundedPost := HBoundedPost) (VROk := VROk) hkC hk)
    (L qep tStar : ℕ) (cfgC : ConfigEC OO) (cfg : Config M)
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
    (deliverForgeECB1 hkC L qep tStar cfgC esE argE).eval ρ =
      Prod.map (Option.map smRrEnc) (esEnc vpTblEnc hsEncFn) <$>
        (DeliverForge.deliverForgeEB1 hk qep tStar cfg (P, c, c')).run es := by
  unfold deliverForgeECB1 DeliverForge.deliverForgeEB1 abortE
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
            have hTriv : (cTrivialB1E L tStar (esG (.fst (Expr.v4 (O := OO))))
                (.pair (otherE (.fst (.snd .v4)))
                  (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))).eval ρ₄ =
                DeliverForge.trivB1 tStar es.g ⟨P.other, t', i'⟩ :=
              cTrivialB1E_eval vpTblEnc (O' := OO) L tStar (esG (.fst .v4)) _
                ρ₄ es.g ⟨P.other, t', i'⟩ hBound.trans_le hBound.comp_le rfl hPos
            rw [hTriv]
            by_cases htriv : DeliverForge.trivB1 tStar es.g ⟨P.other, t', i'⟩
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

end Dir2OffTargetHandlers

theorem injectEB1_inv [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    {L B q qep tStar : ℕ} (cfg : Config M)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (arg : Party × (Header T × E))
    (hInv : SMEngineInv L B (q + 1) es.g) :
    ∀ res ∈ support ((DeliverForge.injectEB1 hk qep tStar cfg arg).run es),
      SMEngineInv L B q res.2.g := by
  rcases arg with ⟨P, c⟩
  intro ⟨out, es'⟩ hmem
  have hInvQ : SMEngineInv L B q es.g := hInv.mono (Nat.le_succ q)
  unfold DeliverForge.injectEB1 abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases href : (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj 2))
  · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hInvQ
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hmem
    rw [run_liftH_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨vrRes, h'⟩, _, hmem⟩ := hmem
    rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
    · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInvQ
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInvQ
    · by_cases hqep : qep + 1 < t'
      · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hInvQ
      · simp only [hqep, ↓reduceIte] at hmem
        by_cases htriv : DeliverForge.trivB1 tStar es.g ⟨P.other, t', i'⟩
        · simp only [htriv, ↓reduceIte, StateT.run_bind, mem_support_bind_iff] at hmem
          obtain ⟨⟨cmRes, es''⟩, hcm, hmem⟩ := hmem
          have ⟨hEs'', hAcc⟩ := commitE_inv hk { es with h := h' } es.g P (es.g.st P) st'
            ⟨P.other, t', i'⟩ hInvQ hInvQ (cmRes, es'') hcm
          rcases cmRes with _ | s₁
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
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

theorem deliverForgeEB1_inv [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {γV σV ssV rsV HS : Type}
    (hk : Hooks TSpec HS Γ T RSt SS RS M E CCoins γV σV ssV rsV)
    {L B q qep tStar : ℕ} (cfg : Config M)
    (es : EState (VP γV T σV ssV rsV) M (Header T × E) HS)
    (arg : Party × (Header T × E) × (Header T × E))
    (hInv : SMEngineInv L B (q + 1) es.g) :
    ∀ res ∈ support ((DeliverForge.deliverForgeEB1 hk qep tStar cfg arg).run es),
      SMEngineInv L B q res.2.g := by
  rcases arg with ⟨P, c, c'⟩
  intro ⟨out, es'⟩ hmem
  have hInvQ : SMEngineInv L B q es.g := hInv.mono (Nat.le_succ q)
  unfold DeliverForge.deliverForgeEB1 abortE at hmem
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
            by_cases htriv : DeliverForge.trivB1 tStar es.g ⟨P.other, t', i'⟩
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

end CryptoGames.SM.Engine
