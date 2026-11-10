/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SpecLemmas.Session.ACD19.SM.CostedTables
import Computational.Proofs.ReductionDsl.Size
public import Computational.Proofs.CryptoGames.SM.GameProofDefs
public import Computational.Proofs.GameHop.CompDedup
import Computational.Proofs.ReductionDsl.Notation

/-!
# Costed SM game state, bookkeeping, and oracle handlers

Encodes `SM.Record` and `SM.GameState`, pure bookkeeping predicates, and the `SM` oracle handlers
(`transmitRC`, `challRC`, `corrRC`) in `ReductionDsl` over `smSig`, and proves size-honesty,
evaluation agreement, and static query bounds.
-/

@[expose] public section

namespace CryptoGames.SM

open ReductionDsl OracleSpec OracleComp
open Computational.Proofs.GameHop.CompDedup
  (CountLe countLe_length_le dedupPrepend foldr_dedup_map_eq afterCorrDedup corrRDedup)
open scoped Computational.Proofs.ReductionDsl.Notation

@[simp] theorem _root_.ReductionDsl.Env.get_cons_zero {S : Sig} {Γ : List (Ty S)} {t : Ty S}
    (x : t.denote) (ρ : Env Γ) : (Env.cons x ρ).get Var.zero = x := rfl

@[simp] theorem _root_.ReductionDsl.Env.get_cons_succ {S : Sig} {Γ : List (Ty S)} {t u : Ty S}
    (x : u.denote) (ρ : Env Γ) (v : Var Γ t) : (Env.cons x ρ).get (Var.succ v) = ρ.get v := rfl

/-! ## State representations -/

section StateRepr

variable {Key St St₂ Msg Coins RCoins C : Type}

local notation "S" => smSig Key St St₂ Msg Coins RCoins C

/-- `SM.Record Msg C` as a `ReductionDsl` type: `(pos, (msg, ct))`. -/
@[reducible] def recTy : Ty S := .prod posTy (.prod (.base .msg) (.base .ct))

def recEnc (r : Record Msg C) : (Bool × ℕ × ℕ) × Msg × C :=
  (posEnc r.pos, r.msg, r.ct)

def recDec (v : (Bool × ℕ × ℕ) × Msg × C) : Record Msg C :=
  ⟨posDec v.1, v.2.1, v.2.2⟩

@[simp] theorem recDec_recEnc (r : Record Msg C) : recDec (recEnc r) = r := by
  cases r; simp [recEnc, recDec]

@[simp] theorem recEnc_recDec (v : (Bool × ℕ × ℕ) × Msg × C) : recEnc (recDec v) = v := by
  rcases v with ⟨p, m, c⟩; simp [recEnc, recDec]

/-- `SM.GameState St Msg C` encoded in `smSig` as `(st, b, win, epoch, idx, tL, trans, chall, comp, maxAcc, leaks, corrs)`. -/
@[reducible] def gsTy : Ty S :=
  .prod (.prod (.base .st) (.base .st))
    (.prod .bool
      (.prod .bool
        (.prod (.prod .nat .nat)
          (.prod (.prod .nat .nat)
            (.prod (.opt .nat)
               (.prod (.list recTy)
                (.prod (.list posTy)
                  (.prod (.list posTy)
                    (.prod (.prod (.tbl .nat) (.tbl .nat))
                      (.prod (.list .nat)
                        (.list (.prod .bool .nat))))))))))))

def gsEnc (s : GameState St Msg C) : (@gsTy Key St St₂ Msg Coins RCoins C).denote :=
  ((s.st .A, s.st .B),
   (s.b,
    (s.win,
     ((s.epoch .A, s.epoch .B),
      ((s.idx .A, s.idx .B),
       (s.tL,
        (s.trans.map recEnc,
         (s.chall.map posEnc,
          (s.comp.map posEnc,
           ((s.maxAcc .A, s.maxAcc .B),
            (s.leaks,
             s.corrs.map (fun pe => (partyEnc pe.1, pe.2)))))))))))))

def gsDec (v : (@gsTy Key St St₂ Msg Coins RCoins C).denote) : GameState St Msg C :=
  let (stAB, (b, (win, (epAB, (idxAB, (tL, (trs, (chall, (comp, (maAB, (leaks, corrs))))))))))) := v
  { st := fun | .A => stAB.1 | .B => stAB.2
    epoch := fun | .A => epAB.1 | .B => epAB.2
    idx := fun | .A => idxAB.1 | .B => idxAB.2
    tL := tL
    trans := trs.map recDec
    chall := chall.map posDec
    comp := comp.map posDec
    maxAcc := fun | .A => maAB.1 | .B => maAB.2
    b := b
    win := win
    leaks := leaks
    corrs := corrs.map (fun pe => (partyDec pe.1, pe.2)) }

end StateRepr

section ExprHelpers

variable {Key St St₂ Msg Coins RCoins C : Type}

local notation "S" => smSig Key St St₂ Msg Coins RCoins C

def recPos
    {O' : Ops S} {Γ} (r : Expr O' Γ recTy) : Expr O' Γ posTy := .fst r
def recCt
    {O' : Ops S} {Γ} (r : Expr O' Γ recTy) : Expr O' Γ (.base .ct) := .snd (.snd r)

def gsSt
    {O' : Ops S} {Γ} (s : Expr O' Γ gsTy) :
    Expr O' Γ (.prod (.base .st) (.base .st)) := .fst s
def gsB
    {O' : Ops S} {Γ} (s : Expr O' Γ gsTy) : Expr O' Γ .bool :=
  .fst (.snd s)
def gsWin
    {O' : Ops S} {Γ} (s : Expr O' Γ gsTy) : Expr O' Γ .bool :=
  .fst (.snd (.snd s))
def gsEpoch
    {O' : Ops S} {Γ} (s : Expr O' Γ gsTy) : Expr O' Γ (.prod .nat .nat) :=
  .fst (.snd (.snd (.snd s)))
def gsIdx
    {O' : Ops S} {Γ} (s : Expr O' Γ gsTy) : Expr O' Γ (.prod .nat .nat) :=
  .fst (.snd (.snd (.snd (.snd s))))
def gsTL
    {O' : Ops S} {Γ} (s : Expr O' Γ gsTy) : Expr O' Γ (.opt .nat) :=
  .fst (.snd (.snd (.snd (.snd (.snd s)))))
def gsTrans
    {O' : Ops S} {Γ} (s : Expr O' Γ gsTy) : Expr O' Γ (.list recTy) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd s))))))
def gsChall
    {O' : Ops S} {Γ} (s : Expr O' Γ gsTy) : Expr O' Γ (.list posTy) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd s)))))))
def gsComp
    {O' : Ops S} {Γ} (s : Expr O' Γ gsTy) : Expr O' Γ (.list posTy) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd s))))))))
def gsMaxAcc
    {O' : Ops S} {Γ} (s : Expr O' Γ gsTy) :
    Expr O' Γ (.prod (.tbl .nat) (.tbl .nat)) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd s)))))))))
def gsLeaks
    {O' : Ops S} {Γ} (s : Expr O' Γ gsTy) : Expr O' Γ (.list .nat) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd s))))))))))
def gsCorrs
    {O' : Ops S} {Γ} (s : Expr O' Γ gsTy) : Expr O' Γ (.list (.prod .bool .nat)) :=
  .snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd s))))))))))

def gsMk
    {O' : Ops S} {Γ}
    (st : Expr O' Γ (.prod (.base .st) (.base .st)))
    (b win : Expr O' Γ .bool)
    (epoch idx : Expr O' Γ (.prod .nat .nat))
    (tL : Expr O' Γ (.opt .nat))
    (trans : Expr O' Γ (.list recTy))
    (chall comp : Expr O' Γ (.list posTy))
    (maxAcc : Expr O' Γ (.prod (.tbl .nat) (.tbl .nat)))
    (leaks : Expr O' Γ (.list .nat))
    (corrs : Expr O' Γ (.list (.prod .bool .nat))) : Expr O' Γ gsTy :=
  .pair st
    (.pair b
      (.pair win
        (.pair epoch
          (.pair idx
            (.pair tL
               (.pair trans
                (.pair chall
                  (.pair comp
                    (.pair maxAcc
                      (.pair leaks corrs))))))))))

def gsSetWin
    {O' : Ops S} {Γ} (s : Expr O' Γ gsTy) (w : Expr O' Γ .bool) : Expr O' Γ gsTy :=
  .letE (.pair s w)
    (let s0 : Expr O' _ gsTy := .fst .v0
     let w0 : Expr O' _ .bool := .snd .v0
     gsMk (gsSt s0) (gsB s0) w0 (gsEpoch s0) (gsIdx s0) (gsTL s0)
       (gsTrans s0) (gsChall s0) (gsComp s0) (gsMaxAcc s0) (gsLeaks s0) (gsCorrs s0))

end ExprHelpers

/-! ## Pure bookkeeping expressions -/

section Bookkeeping

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

local notation "S" => smSig Key St St₂ Msg Coins RCoins C
local notation "OO" => smOps init send receive eqMsg eqCt blank injOK stOK φ

def safeChE
    {O' : Ops S} {Γ} (Δ : ℕ) (s : Expr O' Γ gsTy) (p : Expr O' Γ .bool) :
    Expr O' Γ .bool :=
  rdslExpr =>
    letE (s, p) fun (s0, p0) =>
      healedByE (gsTL s0) Δ (pGet (gsEpoch s0) p0)

def safeInjE
    {O' : Ops S} {Γ} (Δ : ℕ) (s : Expr O' Γ gsTy) : Expr O' Γ .bool :=
  rdslExpr =>
    letE s fun s0 =>
      healedByE (gsTL s0) Δ (minN (gsEpoch s0).1 (gsEpoch s0).2)

def leakE
    {O' : Ops S} {Γ} (s : Expr O' Γ gsTy) (l : Expr O' Γ .nat) : Expr O' Γ gsTy :=
  rdslExpr =>
    letE (s, l) fun (s0, l0) =>
      let m := maxOptE (gsTL s0) l0
      gsMk (gsSt s0) (gsB s0) (gsWin s0) (gsEpoch s0) (gsIdx s0)
        (some m) (gsTrans s0) (gsChall s0) (gsComp s0) (gsMaxAcc s0)
        (cons m (gsLeaks s0)) (gsCorrs s0)

def epMgmtE
    {O' : Ops S} {Γ} (Δ qep : ℕ) (s : Expr O' Γ gsTy) (p : Expr O' Γ .bool)
    (bad : Expr O' Γ .bool) : Expr O' Γ (.opt gsTy) :=
  rdslExpr =>
    letE (s, (p, bad)) fun (s0, (p0, bad0)) =>
      let epP := pGet (gsEpoch s0) p0
      let epNext := epP + 1
      if sendsInE p0 epNext then
        if nat qep < epNext then
          none
        else
          letE (if bad0 && !(safeChE Δ s0 p0) then leakE s0 epNext else s0) fun s1 =>
            let ep1 := pGet (gsEpoch s1) p0 + 1
            some (gsMk (gsSt s1) (gsB s1) (gsWin s1)
              (pSet (gsEpoch s1) p0 ep1)
              (pSet (gsIdx s1) p0 0)
              (gsTL s1) (gsTrans s1) (gsChall s1) (gsComp s1)
              (gsMaxAcc s1) (gsLeaks s1) (gsCorrs s1))
      else if nat qep < epP then
        none
      else
        some s0

def recordE
    {O' : Ops S} {Γ} (Δ : ℕ) (s : Expr O' Γ gsTy) (p : Expr O' Γ .bool)
    (st' : Expr O' Γ (.base .st)) (r : Expr O' Γ recTy) (isChall : Expr O' Γ .bool) :
    Expr O' Γ gsTy :=
  rdslExpr =>
    letE (s, (p, (st', (r, isChall)))) fun (s0, (p0, (st0, (r0, ch0)))) =>
      let pos := recPos r0
      gsMk
        (pSet (gsSt s0) p0 st0)
        (gsB s0) (gsWin s0) (gsEpoch s0)
        (pSet (gsIdx s0) p0 (posIdx pos))
        (gsTL s0)
        (cons r0 (gsTrans s0))
        (if ch0 then cons pos (gsChall s0) else gsChall s0)
        (if safeChE Δ s0 p0 then gsComp s0 else cons pos (gsComp s0))
        (gsMaxAcc s0) (gsLeaks s0) (gsCorrs s0)

def inTransitE {Γ} (K : ℕ) (s : Expr OO Γ gsTy) (qParty : Expr OO Γ .bool)
    (c : Expr OO Γ (.base .ct)) : Expr OO Γ (.opt recTy) :=
  rdslExpr =>
    letE (s, (qParty, c)) fun (s0, (qp0, c0)) =>
      findB K (gsTrans s0) fun recElem =>
        boolEq (posSender (recPos recElem)) qp0 &&
          Expr.op (O := OO) SMOp.eqCt (recCt recElem, c0)

def deleteE
    {O' : Ops S} {Γ} (K : ℕ) (s : Expr O' Γ gsTy) (pos : Expr O' Γ posTy) :
    Expr O' Γ gsTy :=
  rdslExpr =>
    letE (s, pos) fun (s0, pos0) =>
      let trans' := foldrB K (gsTrans s0) [] fun recElem acc =>
        if !(posEq (recPos recElem) pos0) then cons recElem acc else acc
      let chall' := foldrB K (gsChall s0) [] fun posElem acc =>
        if !(posEq posElem pos0) then cons posElem acc else acc
      let comp' := foldrB K (gsComp s0) [] fun posElem acc =>
        if !(posEq posElem pos0) then cons posElem acc else acc
      gsMk (gsSt s0) (gsB s0) (gsWin s0) (gsEpoch s0) (gsIdx s0) (gsTL s0)
        trans' chall' comp' (gsMaxAcc s0) (gsLeaks s0) (gsCorrs s0)

def acceptE
    {O' : Ops S} {Γ} (K : ℕ) (s : Expr O' Γ gsTy) (p : Expr O' Γ .bool)
    (st' : Expr O' Γ (.base .st)) (pos : Expr O' Γ posTy) : Expr O' Γ gsTy :=
  rdslExpr =>
    letE (deleteE K s pos, (p, (st', pos))) fun (s1, (p0, (st0, pos0))) =>
      let pEpoch := posEpoch pos0
      let pIdx := posIdx pos0
      gsMk
        (pSet (gsSt s1) p0 st0)
        (gsB s1) (gsWin s1)
        (pSet (gsEpoch s1) p0 (maxN (pGet (gsEpoch s1) p0) pEpoch))
        (gsIdx s1) (gsTL s1) (gsTrans s1) (gsChall s1) (gsComp s1)
        (maxAccSet (gsMaxAcc s1) p0 pEpoch
          (maxN (maxAccGet (gsMaxAcc s1) p0 pEpoch) pIdx))
        (gsLeaks s1) (gsCorrs s1)

def compContainsE
    {O' : Ops S} {Γ} (K : ℕ) (s : Expr O' Γ gsTy) (pos : Expr O' Γ posTy) :
    Expr O' Γ .bool :=
  rdslExpr =>
    letE (s, pos) fun (s0, pos0) =>
      anyB K (gsComp s0) fun posElem => posEq posElem pos0

def challContainsE
    {O' : Ops S} {Γ} (K : ℕ) (s : Expr O' Γ gsTy) (pos : Expr O' Γ posTy) :
    Expr O' Γ .bool :=
  rdslExpr =>
    letE (s, pos) fun (s0, pos0) =>
      anyB K (gsChall s0) fun posElem => posEq posElem pos0

def trivialE
    {O' : Ops S} {Γ} (K Δ : ℕ) (s : Expr O' Γ gsTy) (pos : Expr O' Γ posTy) :
    Expr O' Γ .bool :=
  rdslExpr =>
    letE (s, pos) fun (s0, pos0) =>
      orE (compContainsE K s0 pos0)
        ((!(anyB K (gsTrans s0) fun recElem => posEq (recPos recElem) pos0)) &&
          !(healedByE (gsTL s0) Δ (posEpoch pos0)))

def corrAllowedE
    {O' : Ops S} {Γ} (K : ℕ) (s : Expr O' Γ gsTy) (p : Expr O' Γ .bool) :
    Expr O' Γ .bool :=
  rdslExpr =>
    letE (s, p) fun (s0, p0) =>
      (!(anyB K (gsChall s0) fun posElem => boolEq (posSender posElem) (otherE p0))) &&
        !(anyB K (gsTrans s0) fun recElem =>
          boolEq (posSender (recPos recElem)) (otherE p0) &&
            !(compContainsE K s0 (recPos recElem)))

def afterCorrE
    {O' : Ops S} {Γ} (K : ℕ) (s : Expr O' Γ gsTy) (p : Expr O' Γ .bool) :
    Expr O' Γ gsTy :=
  rdslExpr =>
    letE (s, p) fun (s0, p0) =>
      let comp' := foldrB K (gsTrans s0) (gsComp s0) fun recElem acc =>
        if boolEq (posSender (recPos recElem)) (otherE p0) &&
            !(anyB K acc fun posElem => posEq posElem (recPos recElem)) then
          cons (recPos recElem) acc
        else
          acc
      let s1 := gsMk (gsSt s0) (gsB s0) (gsWin s0) (gsEpoch s0) (gsIdx s0) (gsTL s0)
        (gsTrans s0) (gsChall s0) comp' (gsMaxAcc s0) (gsLeaks s0) (gsCorrs s0)
      let s2 := leakE s1 (maxN (gsEpoch s0).1 (gsEpoch s0).2)
      gsMk (gsSt s2) (gsB s2) (gsWin s2) (gsEpoch s2) (gsIdx s2) (gsTL s2)
        (gsTrans s2) (gsChall s2) (gsComp s2) (gsMaxAcc s2) (gsLeaks s2)
        (cons (p0, pGet (gsEpoch s0) p0) (gsCorrs s2))

def inWindowE
    {O' : Ops S} {Γ} (s : Expr O' Γ gsTy) (p : Expr O' Γ .bool) : Expr O' Γ .bool :=
  rdslExpr =>
    letE (s, p) fun (s0, p0) =>
      !(sendsInE p0 (pGet (gsEpoch s0) p0))

def noBobEpoch0E
    {O' : Ops S} {Γ} (s : Expr O' Γ gsTy) (p : Expr O' Γ .bool) :
    Expr O' Γ .bool :=
  rdslExpr =>
    letE (s, p) fun (s0, p0) =>
      !(p0 && (gsEpoch s0).2 == 0)

def noSpkCorrE
    {O' : Ops S} {Γ} (s : Expr O' Γ gsTy) (p : Expr O' Γ .bool) :
    Expr O' Γ .bool :=
  rdslExpr =>
    letE (s, p) fun (s0, p0) =>
      !((!p0) && (gsEpoch s0).1 < 10)

def noCorrB0E
    {O' : Ops S} {Γ} (s : Expr O' Γ gsTy) (p : Expr O' Γ .bool) :
    Expr O' Γ .bool :=
  noBobEpoch0E s p

def noCorrBWinE
    {O' : Ops S} {Γ} (s : Expr O' Γ gsTy) (p : Expr O' Γ .bool) :
    Expr O' Γ .bool :=
  rdslExpr =>
    letE (s, p) fun (s0, p0) =>
      !(p0 && (gsEpoch s0).1 < 10)

def validGuessE
    {S' : Sig} {O' : Ops S'} {Γ} (Δ : ℕ) (tLStar : Expr O' Γ (.opt .nat))
    (tStar : Expr O' Γ .nat) : Expr O' Γ .bool :=
  healedByE tLStar Δ tStar

def optNatEqE
    {S' : Sig} {O' : Ops S'} {Γ} (a b : Expr O' Γ (.opt .nat)) : Expr O' Γ .bool :=
  rdslExpr =>
    letE (a, b) fun (a0, b0) =>
      match a0 with
      | none =>
        match b0 with
        | none => true
        | some _ => false
      | some va =>
        match b0 with
        | none => false
        | some vb => va == vb

end Bookkeeping

/-! ## Configuration and oracle handlers -/

section Oracles

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

local notation "S" => smSig Key St St₂ Msg Coins RCoins C
local notation "OO" => smOps init send receive eqMsg eqCt blank injOK stOK φ

/-- Configuration expressions for SM oracle handlers (`ConfigR`) in `ReductionDsl`. -/
structure ConfigRC (O' : Ops S) where
  deliverWin : Bool := true
  injectFullE : ∀ {Γ}, Expr O' Γ .nat → Expr O' Γ .bool := fun _ => .bool true
  challOKE : ∀ {Γ}, Expr O' Γ .nat → Expr O' Γ .bool := fun _ => .bool true
  challBlankBefore : Option ℕ := none
  r1 : Bool := false
  mustE : ∀ {Γ}, Expr O' Γ gsTy → Expr O' Γ .bool → Expr O' Γ recTy → Expr O' Γ .bool :=
    fun _ _ _ => .bool false
  sendOKE : ∀ {Γ}, Expr O' Γ gsTy → Expr O' Γ .bool → Expr O' Γ .bool := fun _ _ => .bool true
  corrOKE : ∀ {Γ}, Expr O' Γ gsTy → Expr O' Γ .bool → Expr O' Γ .bool := fun _ _ => .bool true
  useInjOK : Bool := false

/-- `ConfigRC` instance corresponding to `E2E.configRefuseEarlyBobCorr`. -/
def ConfigRC.spkS
    (O' : Ops S) : ConfigRC O' :=
  { deliverWin := false
    r1 := true
    useInjOK := true
    sendOKE := noBobEpoch0E
    corrOKE := fun s p =>
      .and (.and (noSpkCorrE s p) (noCorrB0E s p)) (noCorrBWinE s p) }

def ConfigRC.injOKE (cfg : ConfigRC OO) {Γ} (c : Expr OO Γ (.base .ct)) : Expr OO Γ .bool :=
  if cfg.useInjOK then Expr.op (O := OO) SMOp.injOK c else .bool true

def ConfigRC.challMsgE (cfg : ConfigRC OO) {Γ} (ep : Expr OO Γ .nat) (b : Expr OO Γ .bool)
    (m₀ m₁ : Expr OO Γ (.base .msg)) : Expr OO Γ (.base .msg) :=
  let mb : Expr OO Γ (.base .msg) := .ite b m₁ m₀
  match cfg.challBlankBefore with
  | none => mb
  | some i => .ite (.lt ep (.nat i)) (Expr.op (O := OO) SMOp.blank mb) mb

def samIfNecC
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (drawCoins : ∀ {Γ}, Comp OO I Γ (.opt (.base .coins)))
    {Γ} (optR : Expr OO Γ (.opt (.base .coins))) :
    Comp OO I Γ (.opt (.prod (.base .coins) .bool)) :=
  rdsl do
    match optR with
    | none =>
      drawn ← drawCoins
      match drawn with
      | none => return none
      | some r => return (some (r, false))
    | some r =>
      return (some (r, true))

def transmitRC
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (Δ qep : ℕ) (cfg : ConfigRC OO)
    (drawCoins : ∀ {Γ}, Comp OO I Γ (.opt (.base .coins)))
    {Γ} (s : Expr OO Γ gsTy)
    (arg : Expr OO Γ (.prod .bool (.prod (.base .msg) (.opt (.base .coins))))) :
    Comp OO I Γ (.prod (.opt (.base .ct)) gsTy) :=
  rdsl do
    (s0, (p0, (m0, optR0))) ← return (s, arg)
    if orE (!(cfg.sendOKE s0 p0)) (gsWin s0) then
      return (none, s0)
    else
      coinOpt ← samIfNecC drawCoins optR0
      match coinOpt with
      | none => return (none, s0)
      | some (coins1, bad) =>
        match epMgmtE Δ qep s0 p0 bad with
        | none => return (none, s0)
        | some s1 =>
          match Expr.op (O := OO) SMOp.send (pGet (gsSt s1) p0, (m0, coins1)) with
          | none => return (none, s0)
          | some (st', c) =>
            let pos := (p0, (pGet (gsEpoch s1) p0, pGet (gsIdx s1) p0 + 1))
            let rec_ := (pos, (m0, c))
            return (some c, recordE Δ s1 p0 st' rec_ false)

def challRC
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (Δ qep : ℕ) (cfg : ConfigRC OO)
    (drawCoins : ∀ {Γ}, Comp OO I Γ (.opt (.base .coins)))
    {Γ} (s : Expr OO Γ gsTy)
    (arg : Expr OO Γ
      (.prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .coins)))))) :
    Comp OO I Γ (.prod (.opt (.base .ct)) gsTy) :=
  rdsl do
    (s0, (p0, (m₀, (m₁, optR0)))) ← return (s, arg)
    if orE (!(cfg.sendOKE s0 p0)) (gsWin s0) then
      return (none, s0)
    else
      coinOpt ← samIfNecC drawCoins optR0
      match coinOpt with
      | none => return (none, s0)
      | some (coins1, bad) =>
        match epMgmtE Δ qep s0 p0 bad with
        | none => return (none, s0)
        | some s1 =>
          let ep1 := pGet (gsEpoch s1) p0
          if orE (!(safeChE Δ s1 p0)) (!(cfg.challOKE ep1)) then
            return (none, s0)
          else
            let m := cfg.challMsgE ep1 (gsB s0) m₀ m₁
            match Expr.op (O := OO) SMOp.send (pGet (gsSt s1) p0, (m, coins1)) with
            | none => return (none, s0)
            | some (st', c) =>
              let pos := (p0, (ep1, pGet (gsIdx s1) p0 + 1))
              let rec_ := (pos, (m, c))
              return (some c, recordE Δ s1 p0 st' rec_ true)

def corrRC
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (K : ℕ) (cfg : ConfigRC OO)
    {Γ} (s : Expr OO Γ gsTy) (p : Expr OO Γ .bool) :
    Comp OO I Γ (.prod (.opt (.base .st)) gsTy) :=
  rdsl do
    (s0, p0) ← return (s, p)
    let refuse :=
      orE (gsWin s0)
        (orE (!(corrAllowedE K s0 p0))
          (orE (bool cfg.r1 && inWindowE s0 p0)
            (!(cfg.corrOKE s0 p0))))
    if refuse then
      return (none, s0)
    else
      return (some (pGet (gsSt s0) p0), afterCorrE K s0 p0)

end Oracles

/-! ## Size-honesty -/

section SizeHonest

variable {Key St St₂ Msg Coins RCoins C : Type}

theorem smOps_sizeHonest
    (init : Party → Key → Option St := fun _ _ => none)
    (send : St → Msg → Coins → Option (St × C) := fun _ _ _ => none)
    (receive : St → C → RCoins → Option (St × ℕ × ℕ × Msg) := fun _ _ _ => none)
    (eqMsg : Msg → Msg → Bool := fun _ _ => false)
    (eqCt : C → C → Bool := fun _ _ => false)
    (blank : Msg → Msg := id)
    (injOK : C → Bool := fun _ => true)
    (stOK : Party → St → Bool := fun _ _ => true)
    (φ : St → Option St₂ := fun _ => none) :
    OpsSizeHonest (smOps init send receive eqMsg eqCt blank injOK stOK φ) := by
  intro o x B hx
  cases o with
  | init =>
    rcases x with ⟨p, k⟩
    simp only [smOps, Ty.Fits, smSig] at hx ⊢
    rcases init (partyDec p) k with _ | st
    · trivial
    · simp only [Ty.Fits]; omega
  | send =>
    rcases x with ⟨st, m, r⟩
    simp only [smOps, Ty.Fits, smSig] at hx ⊢
    rcases send st m r with _ | ⟨st', c⟩
    · trivial
    · simp only [Ty.Fits]; exact ⟨by omega, by omega⟩
  | receive B_idx =>
    rcases x with ⟨st, c, rc⟩
    simp only [smOps, Ty.Fits, smSig] at hx ⊢
    rcases receive st c rc with _ | ⟨st', t', i', m'⟩
    · trivial
    · simp only [Option.map_some, Ty.Fits]
      have hb1 : 1 ≤ bits B_idx := one_le_bits B_idx
      have ht : bits (min t' B_idx) ≤ bits B_idx := bits_mono (Nat.min_le_right _ _)
      have hi : bits (min i' B_idx) ≤ bits B_idx := bits_mono (Nat.min_le_right _ _)
      exact ⟨by omega, ⟨by omega, ⟨by omega, by omega⟩⟩⟩
  | eqMsg => trivial
  | eqCt => trivial
  | blank => simp only [Ty.Fits] at hx ⊢; omega
  | injOK => trivial
  | stOK => trivial
  | relabelSt =>
    simp only [smOps, Ty.Fits, smSig] at hx ⊢
    rcases φ x with _ | st₂
    · trivial
    · simp only [Ty.Fits]; omega

theorem smSamplers_sizeHonest
    (sampKey : ProbComp (Option Key) := pure none)
    (sampCoins : ProbComp (Option Coins) := pure none)
    (sampRCoins : ProbComp (Option RCoins) := pure none) :
    SampSizeHonest (smSamplers (St := St) (St₂ := St₂) (Msg := Msg) (C := C)
      sampKey sampCoins sampRCoins) := by
  intro s x B _ y _
  cases s with
  | bit => trivial
  | key => rcases y with _ | k <;> simp [Ty.Fits]
  | coins => rcases y with _ | r <;> simp [Ty.Fits]
  | rcoins => rcases y with _ | rc <;> simp [Ty.Fits]

end SizeHonest

section EncDec

variable {Key St St₂ Msg Coins RCoins C : Type}

@[simp] theorem partyEnc_beq (P Q : Party) : (partyEnc P == partyEnc Q) = (P == Q) := by
  cases P <;> cases Q <;> rfl

theorem partyEnc_sendsIn (P : Party) (t : ℕ) :
    (if partyEnc P then decide (t % 2 = 0) else decide (t % 2 = 1)) = P.sendsIn t := by
  cases P <;> rfl

theorem partyEnc_senderOf (t : ℕ) : (!decide (t % 2 = 1)) = partyEnc (Party.senderOf t) := by
  simp only [Party.senderOf]
  split <;> simp_all [partyEnc]

theorem partyEnc_receiverOf (t : ℕ) : decide (t % 2 = 1) = partyEnc (Party.receiverOf t) := by
  simp only [Party.receiverOf, Party.senderOf]
  split <;> simp_all [partyEnc, Party.other]

@[simp] theorem gsDec_gsEnc (s : GameState St Msg C) :
    gsDec (Key := Key) (St₂ := St₂) (Coins := Coins) (RCoins := RCoins) (gsEnc s) = s := by
  cases s
  simp only [gsEnc, gsDec, List.map_map]
  congr 1
  · funext p; cases p <;> rfl
  · funext p; cases p <;> rfl
  · funext p; cases p <;> rfl
  · rw [show (recDec ∘ recEnc : Record Msg C → Record Msg C) = id by funext r; simp, List.map_id]
  · rw [show (posDec ∘ posEnc : Pos → Pos) = id by funext p; simp, List.map_id]
  · rw [show (posDec ∘ posEnc : Pos → Pos) = id by funext p; simp, List.map_id]
  · funext p; cases p <;> rfl
  · rw [show ((fun pe : Bool × ℕ => (partyDec pe.1, pe.2)) ∘
        (fun pe : Party × ℕ => (partyEnc pe.1, pe.2))) = id by
      funext ⟨p, e⟩; simp, List.map_id]

@[simp] theorem gsEnc_gsDec (v : (@gsTy Key St St₂ Msg Coins RCoins C).denote) :
    gsEnc (Key := Key) (St₂ := St₂) (Coins := Coins) (RCoins := RCoins) (gsDec v) = v := by
  rcases v with ⟨⟨stA, stB⟩, b, win, ⟨epA, epB⟩, ⟨idxA, idxB⟩, tL, trs, chall, comp,
    ⟨maA, maB⟩, leaks, corrs⟩
  simp [gsEnc, gsDec, List.map_map, Function.comp_def]

end EncDec

/-! ## Bookkeeping evaluation agreement -/

section BookkeepingEval

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

local notation "S" => smSig Key St St₂ Msg Coins RCoins C
local notation "OO" => smOps init send receive eqMsg eqCt blank injOK stOK φ

theorem letE_eval {S' : Sig} {O' : Ops S'} {Γ} {t₁ t₂ : Ty S'}
    (e₁ : Expr O' Γ t₁) (e₂ : Expr O' (t₁ :: Γ) t₂) (ρ : Env Γ) :
    (Expr.letE e₁ e₂).eval ρ = e₂.eval (Env.cons (e₁.eval ρ) ρ) := rfl

theorem ite_eval {S' : Sig} {O' : Ops S'} {Γ} {t : Ty S'}
    (c : Expr O' Γ .bool) (e₁ e₂ : Expr O' Γ t) (ρ : Env Γ) :
    (Expr.ite c e₁ e₂).eval ρ = if c.eval ρ then e₁.eval ρ else e₂.eval ρ := rfl

theorem pair_eval {S' : Sig} {O' : Ops S'} {Γ} {t₁ t₂ : Ty S'}
    (e₁ : Expr O' Γ t₁) (e₂ : Expr O' Γ t₂) (ρ : Env Γ) :
    (Expr.pair e₁ e₂).eval ρ = (e₁.eval ρ, e₂.eval ρ) := rfl

theorem some_eval {S' : Sig} {O' : Ops S'} {Γ} {t : Ty S'}
    (e : Expr O' Γ t) (ρ : Env Γ) :
    (Expr.some e).eval ρ = some (e.eval ρ) := rfl

theorem inr_eval {S' : Sig} {O' : Ops S'} {Γ} {t u : Ty S'}
    (e : Expr O' Γ u) (ρ : Env Γ) :
    (Expr.inr (t := t) e).eval ρ = Sum.inr (e.eval ρ) := rfl

@[simp] theorem orE_eval {S' : Sig} {O' : Ops S'} {Γ} (a b : Expr O' Γ .bool) (ρ : Env Γ) :
    (orE a b).eval ρ = (a.eval ρ || b.eval ρ) := by
  simp [orE, Expr.eval]

@[simp] theorem boolEq_eval {S' : Sig} {O' : Ops S'} {Γ} (a b : Expr O' Γ .bool) (ρ : Env Γ) :
    (boolEq a b).eval ρ = (a.eval ρ == b.eval ρ) := by
  simp [boolEq, Expr.eval]
  cases a.eval ρ <;> cases b.eval ρ <;> rfl

@[simp] theorem leN_eval {S' : Sig} {O' : Ops S'} {Γ} (a b : Expr O' Γ .nat) (ρ : Env Γ) :
    (leN a b).eval ρ = decide (a.eval ρ ≤ b.eval ρ) := by
  simp only [leN, Expr.eval]
  by_cases h : a.eval ρ ≤ b.eval ρ
  · have hlt : ¬b.eval ρ < a.eval ρ := Nat.not_lt.mpr h
    simp [h, hlt]
  · have hlt : b.eval ρ < a.eval ρ := Nat.lt_of_not_le h
    simp [h, hlt]

@[simp] theorem maxN_eval {S' : Sig} {O' : Ops S'} {Γ} (a b : Expr O' Γ .nat) (ρ : Env Γ) :
    (maxN a b).eval ρ = max (a.eval ρ) (b.eval ρ) := by
  simp only [maxN, Expr.eval, Expr.v0, leN_eval]
  change (if decide (a.eval ρ ≤ b.eval ρ) = true then b.eval ρ else a.eval ρ) =
    max (a.eval ρ) (b.eval ρ)
  by_cases h : a.eval ρ ≤ b.eval ρ
  · simp [h]
  · simp [h, Nat.le_of_not_le h]

@[simp] theorem minN_eval {S' : Sig} {O' : Ops S'} {Γ} (a b : Expr O' Γ .nat) (ρ : Env Γ) :
    (minN a b).eval ρ = min (a.eval ρ) (b.eval ρ) := by
  simp only [minN, Expr.eval, Expr.v0, leN_eval]
  change (if decide (a.eval ρ ≤ b.eval ρ) = true then a.eval ρ else b.eval ρ) =
    min (a.eval ρ) (b.eval ρ)
  by_cases h : a.eval ρ ≤ b.eval ρ
  · simp [h]
  · simp [h, Nat.le_of_not_le h]

@[simp] theorem isSomeE_eval {S' : Sig} {O' : Ops S'} {Γ t} (e : Expr O' Γ (.opt t)) (ρ : Env Γ) :
    (isSomeE e).eval ρ = (e.eval ρ).isSome := by
  simp only [isSomeE, Expr.eval]
  cases e.eval ρ <;> rfl

@[simp] theorem otherE_eval {S' : Sig} {O' : Ops S'} {Γ} (p : Expr O' Γ .bool) (ρ : Env Γ) :
    (otherE p).eval ρ = !(p.eval ρ) := rfl

@[simp] theorem sendsInE_eval {S' : Sig} {O' : Ops S'} {Γ} (p : Expr O' Γ .bool)
    (t : Expr O' Γ .nat) (ρ : Env Γ) (P : Party) (hp : p.eval ρ = partyEnc P) :
    (sendsInE p t).eval ρ = P.sendsIn (t.eval ρ) := by
  simp [sendsInE, Expr.eval, Expr.v0, hp, partyEnc_sendsIn]

@[simp] theorem senderOfE_eval {S' : Sig} {O' : Ops S'} {Γ} (t : Expr O' Γ .nat) (ρ : Env Γ) :
    (senderOfE t).eval ρ = partyEnc (Party.senderOf (t.eval ρ)) := by
  simp only [senderOfE, Expr.eval]
  exact partyEnc_senderOf (t.eval ρ)

@[simp] theorem receiverOfE_eval {S' : Sig} {O' : Ops S'} {Γ} (t : Expr O' Γ .nat) (ρ : Env Γ) :
    (receiverOfE t).eval ρ = partyEnc (Party.receiverOf (t.eval ρ)) := by
  simp only [receiverOfE, Expr.eval]
  exact partyEnc_receiverOf (t.eval ρ)

@[simp] theorem pGet_eval {S' : Sig} {O' : Ops S'} {Γ t} (m : Expr O' Γ (.prod t t))
    (p : Expr O' Γ .bool) (ρ : Env Γ) (f : Party → t.denote) (P : Party)
    (hm : m.eval ρ = (f .A, f .B)) (hp : p.eval ρ = partyEnc P) :
    (pGet m p).eval ρ = f P := by
  cases P <;> simp [pGet, Expr.eval, Expr.v0, hm, hp, partyEnc]

@[simp] theorem pSet_eval {S' : Sig} {O' : Ops S'} {Γ t} (m : Expr O' Γ (.prod t t))
    (p : Expr O' Γ .bool) (v : Expr O' Γ t) (ρ : Env Γ) (f : Party → t.denote) (P : Party)
    (hm : m.eval ρ = (f .A, f .B)) (hp : p.eval ρ = partyEnc P) :
    (pSet m p v).eval ρ =
      (Function.update f P (v.eval ρ) .A, Function.update f P (v.eval ρ) .B) := by
  cases P <;> simp [pSet, Expr.eval, Expr.v0, hm, hp, partyEnc, Function.update]

@[simp] theorem posEq_eval {S' : Sig} {O' : Ops S'} {Γ} (p₁ p₂ : Expr O' Γ posTy) (ρ : Env Γ) :
    (posEq p₁ p₂).eval ρ = (posDec (p₁.eval ρ) == posDec (p₂.eval ρ)) := by
  rcases h1 : p₁.eval ρ with ⟨b₁, t₁, i₁⟩
  rcases h2 : p₂.eval ρ with ⟨b₂, t₂, i₂⟩
  simp only [posEq, posSender, posEpoch, posIdx, Expr.eval, Expr.v0, boolEq_eval,
    Env.get_cons_zero, h1, h2, posDec]
  cases b₁ <;> cases b₂ <;> by_cases ht : t₁ = t₂ <;> by_cases hi : i₁ = i₂ <;>
    simp [partyDec, ht, hi, BEq.beq, Pos.mk.injEq]

@[simp] theorem healedByE_eval {S' : Sig} {O' : Ops S'} {Γ} (tL : Expr O' Γ (.opt .nat)) (Δ : ℕ)
    (t : Expr O' Γ .nat) (ρ : Env Γ) :
    (healedByE tL Δ t).eval ρ = healedBy (tL.eval ρ) Δ (t.eval ρ) := by
  simp only [healedByE, Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero]
  cases tL.eval ρ
  · rfl
  · simp only [healedBy, leN_eval]; rfl

@[simp] theorem ltOptE_eval {S' : Sig} {O' : Ops S'} {Γ} (tL : Expr O' Γ (.opt .nat))
    (t : Expr O' Γ .nat) (ρ : Env Γ) :
    (ltOptE tL t).eval ρ = ltOpt (tL.eval ρ) (t.eval ρ) := by
  simp only [ltOptE, Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero]
  cases tL.eval ρ
  · rfl
  · simp only [ltOpt]; rfl

@[simp] theorem maxOptE_eval {S' : Sig} {O' : Ops S'} {Γ} (tL : Expr O' Γ (.opt .nat))
    (t : Expr O' Γ .nat) (ρ : Env Γ) :
    (maxOptE tL t).eval ρ = maxOpt (tL.eval ρ) (t.eval ρ) := by
  simp only [maxOptE, Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero]
  cases tL.eval ρ <;> simp [maxOpt, Expr.eval, maxN_eval]

@[simp] theorem safeChE_eval {O' : Ops S} {Γ} (Δ : ℕ) (s : Expr O' Γ gsTy) (p : Expr O' Γ .bool)
    (ρ : Env Γ) (st : GameState St Msg C) (P : Party)
    (hs : s.eval ρ = gsEnc st) (hp : p.eval ρ = partyEnc P) :
    (safeChE Δ s p).eval ρ = st.safeCh Δ P := by
  simp only [safeChE, Expr.eval, hs, hp, healedByE_eval]
  cases P <;> simp [GameState.safeCh, gsTL, gsEpoch, pGet, Expr.eval, Expr.v0, gsEnc, partyEnc]

@[simp] theorem safeInjE_eval {O' : Ops S} {Γ} (Δ : ℕ) (s : Expr O' Γ gsTy)
    (ρ : Env Γ) (st : GameState St Msg C) (hs : s.eval ρ = gsEnc st) :
    (safeInjE Δ s).eval ρ = st.safeInj Δ := by
  simp only [safeInjE, Expr.eval, hs, healedByE_eval, minN_eval]
  simp [GameState.safeInj, gsTL, gsEpoch, Expr.eval, Expr.v0, gsEnc]

@[simp] theorem leakE_eval {O' : Ops S} {Γ} (s : Expr O' Γ gsTy) (l : Expr O' Γ .nat)
    (ρ : Env Γ) (st : GameState St Msg C) (hs : s.eval ρ = gsEnc st) :
    (leakE s l).eval ρ = gsEnc (st.leak (l.eval ρ)) := by
  simp only [leakE, gsMk, Expr.eval, hs, maxOptE_eval]
  simp [GameState.leak, gsSt, gsB, gsWin, gsEpoch, gsIdx, gsTL, gsTrans, gsChall,
    gsComp, gsMaxAcc, gsLeaks, gsCorrs, Expr.eval, Expr.v0, gsEnc]

@[simp] theorem epMgmtE_eval {O' : Ops S} {Γ} (Δ qep : ℕ) (s : Expr O' Γ gsTy)
    (p : Expr O' Γ .bool) (bad : Expr O' Γ .bool) (ρ : Env Γ)
    (st : GameState St Msg C) (P : Party)
    (hs : s.eval ρ = gsEnc st) (hp : p.eval ρ = partyEnc P) :
    (epMgmtE Δ qep s p bad).eval ρ = (st.epMgmt Δ qep P (bad.eval ρ)).map gsEnc := by
  unfold epMgmtE GameState.epMgmt
  rw [letE_eval]
  have h0 : (Expr.pair s (.pair p bad)).eval ρ = (gsEnc st, partyEnc P, bad.eval ρ) := by
    simp [Expr.eval, hs, hp]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod gsTy (.prod .bool .bool)) (gsEnc st, partyEnc P, bad.eval ρ) ρ
  rw [ite_eval]
  have hSends : (sendsInE (.fst (.snd (Expr.v0 (O := O'))))
      (.add (pGet (gsEpoch (.fst (Expr.v0 (O := O')))) (.fst (.snd (Expr.v0 (O := O')))))
        (.nat 1))).eval ρ₁ = P.sendsIn (st.epoch P + 1) := by
    rw [sendsInE_eval _ _ ρ₁ P rfl]
    congr 1
    cases P <;> simp [ρ₁, pGet, gsEpoch, gsEnc, partyEnc, Expr.eval, Expr.v0]
  rw [hSends]
  by_cases h1 : P.sendsIn (st.epoch P + 1)
  · simp only [h1, ↓reduceIte]
    rw [ite_eval]
    have hlt1 : (Expr.lt (.nat qep) (.add (pGet (gsEpoch (.fst (Expr.v0 (O := O'))))
        (.fst (.snd (Expr.v0 (O := O'))))) (.nat 1))).eval ρ₁ =
        decide (qep < st.epoch P + 1) := by
      cases P <;> simp [ρ₁, pGet, gsEpoch, gsEnc, partyEnc, Expr.eval, Expr.v0]
    rw [hlt1]
    by_cases h2 : qep < st.epoch P + 1
    · simp [h2, Expr.eval]
    · simp only [h2, decide_false, Bool.false_eq_true, ↓reduceIte, Option.map_some]
      rw [letE_eval, ite_eval]
      have hCond : (Expr.and (.snd (.snd (Expr.v0 (O := O'))))
          (.not (safeChE Δ (.fst (Expr.v0 (O := O'))) (.fst (.snd (Expr.v0 (O := O'))))))).eval ρ₁ =
          (bad.eval ρ && !(st.safeCh Δ P)) := by
        have hsafe := safeChE_eval Δ (.fst (Expr.v0 (O := O'))) (.fst (.snd (Expr.v0 (O := O'))))
          ρ₁ st P rfl rfl
        simp only [Expr.eval, hsafe]
        rfl
      have hLeak : (leakE (.fst (Expr.v0 (O := O')))
          (.add (pGet (gsEpoch (.fst (Expr.v0 (O := O')))) (.fst (.snd (Expr.v0 (O := O')))))
            (.nat 1))).eval ρ₁ = gsEnc (st.leak (st.epoch P + 1)) := by
        rw [leakE_eval (.fst (Expr.v0 (O := O'))) _ ρ₁ st rfl]
        congr 2
        cases P <;> simp [ρ₁, pGet, gsEpoch, gsEnc, partyEnc, Expr.eval, Expr.v0]
      have hBase : (Expr.fst (Expr.v0 (O := O'))).eval ρ₁ = gsEnc st := rfl
      rw [hCond, hLeak, hBase]
      set st₁ := if (bad.eval ρ && !(st.safeCh Δ P)) = true then st.leak (st.epoch P + 1) else st
      have hst₁ : (if (bad.eval ρ && !(st.safeCh Δ P)) = true
          then (gsEnc (st.leak (st.epoch P + 1)) : (@gsTy Key St St₂ Msg Coins RCoins C).denote)
          else gsEnc st) = gsEnc st₁ := by
        dsimp only [st₁]; split_ifs <;> rfl
      rw [hst₁]
      cases P <;>
        simp [ρ₁, gsMk, gsSt, gsB, gsWin, gsEpoch, gsIdx, gsTL, gsTrans, gsChall, gsComp,
          gsMaxAcc, gsLeaks, gsCorrs, pGet, pSet, gsEnc, partyEnc, Function.update,
          Expr.eval, Expr.v0, Expr.v1]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    rw [ite_eval]
    have hlt2 : (Expr.lt (.nat qep) (pGet (gsEpoch (.fst (Expr.v0 (O := O'))))
        (.fst (.snd (Expr.v0 (O := O')))))).eval ρ₁ = decide (qep < st.epoch P) := by
      cases P <;> simp [ρ₁, pGet, gsEpoch, gsEnc, partyEnc, Expr.eval, Expr.v0]
    rw [hlt2]
    by_cases h2 : qep < st.epoch P <;> simp [ρ₁, h2, Expr.eval, Expr.v0]

@[simp] theorem recordE_eval {O' : Ops S} {Γ} (Δ : ℕ) (s : Expr O' Γ gsTy) (p : Expr O' Γ .bool)
    (st' : Expr O' Γ (.base .st)) (r : Expr O' Γ recTy) (isChall : Expr O' Γ .bool) (ρ : Env Γ)
    (st : GameState St Msg C) (P : Party) (rec_ : Record Msg C)
    (hs : s.eval ρ = gsEnc st) (hp : p.eval ρ = partyEnc P) (hr : r.eval ρ = recEnc rec_) :
    (recordE Δ s p st' r isChall).eval ρ =
      gsEnc (st.record Δ P (st'.eval ρ) rec_ (isChall.eval ρ)) := by
  unfold recordE
  rw [letE_eval]
  have h0 : (Expr.pair s (.pair p (.pair st' (.pair r isChall)))).eval ρ =
      (gsEnc st, partyEnc P, st'.eval ρ, recEnc rec_, isChall.eval ρ) := by
    simp [Expr.eval, hs, hp, hr]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod gsTy (.prod .bool (.prod (.base .st) (.prod recTy .bool))))
    (gsEnc st, partyEnc P, st'.eval ρ, recEnc rec_, isChall.eval ρ) ρ
  have hSafe : (safeChE Δ (.fst (Expr.v0 (O := O'))) (.fst (.snd (Expr.v0 (O := O'))))).eval ρ₁ =
      st.safeCh Δ P :=
    safeChE_eval Δ (.fst .v0) (.fst (.snd .v0)) ρ₁ st P rfl rfl
  simp only [gsMk, Expr.eval, hSafe]
  cases P <;> cases hch : isChall.eval ρ <;>
  by_cases hsafeA : st.safeCh Δ .A <;> by_cases hsafeB : st.safeCh Δ .B <;>
  simp [ρ₁, GameState.record, gsSt, gsB, gsWin, gsEpoch, gsIdx, gsTL, gsTrans,
    gsChall, gsComp, gsMaxAcc, gsLeaks, gsCorrs, recPos, posIdx, pSet,
    hch, hsafeA, hsafeB, gsEnc, recEnc, posEnc, partyEnc, Function.update,
    Expr.eval, Expr.v0]

@[simp] theorem gsSetWin_eval {O' : Ops S} {Γ} (s : Expr O' Γ gsTy) (w : Expr O' Γ .bool)
    (ρ : Env Γ) (st : GameState St Msg C) (hs : s.eval ρ = gsEnc st) :
    (gsSetWin s w).eval ρ = gsEnc { st with win := w.eval ρ } := by
  simp [gsSetWin, gsMk, gsSt, gsB, gsEpoch, gsIdx, gsTL, gsTrans, gsChall, gsComp,
    gsMaxAcc, gsLeaks, gsCorrs, hs, gsEnc, Expr.eval, Expr.v0]

/-- List-length invariant bounding `trans`, `chall`, `leaks`, `corrs`, and deduplicated `comp` by `K`. -/
structure SMStateBounded (K : ℕ) (s : GameState St Msg C) : Prop where
  trans_le : s.trans.length ≤ K
  chall_le : s.chall.length ≤ K
  comp_u : ∃ U : List Pos, U.length ≤ K ∧ CountLe s.comp U ∧ ∀ r ∈ s.trans, r.pos ∈ U
  leaks_le : s.leaks.length ≤ K
  corrs_le : s.corrs.length ≤ K

theorem SMStateBounded.comp_le {K : ℕ} {s : GameState St Msg C}
    (h : SMStateBounded K s) : s.comp.length ≤ K := by
  rcases h.comp_u with ⟨U, hUK, hCU, _⟩
  exact le_trans (countLe_length_le hCU) hUK

theorem find?_map_eq {α β : Type} (f : α → β) (p : β → Bool) :
    ∀ (xs : List α), (xs.map f).find? p = (xs.find? (fun x => p (f x))).map f
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, List.find?_cons, find?_map_eq f p xs]
    split <;> rfl

theorem any_map_eq {α β : Type} (f : α → β) (p : β → Bool) :
    ∀ (xs : List α), (xs.map f).any p = xs.any (fun x => p (f x))
  | [] => rfl
  | x :: xs => by simp [List.any_cons, any_map_eq f p xs]

theorem foldr_filter_map_proj {α β γ : Type} (f : α → β) (proj : β → γ) (p : β → Bool) :
    ∀ (xs : List α) (z : List γ),
      (xs.map f).foldr (fun y acc => if p y then proj y :: acc else acc) z =
        ((xs.filter (fun x => p (f x))).map (fun x => proj (f x))) ++ z
  | [], z => rfl
  | x :: xs, z => by
    simp only [List.map_cons, List.foldr_cons, List.filter_cons,
      foldr_filter_map_proj f proj p xs z]
    split <;> rfl

theorem foldr_filter_map {α β : Type} (f : α → β) (p : β → Bool) (xs : List α) :
    (xs.map f).foldr (fun y acc => if p y then y :: acc else acc) [] =
      (xs.filter (fun x => p (f x))).map f := by
  have := foldr_filter_map_proj f id p xs []
  simpa using this

theorem Pos.beq_comm (p q : Pos) : (p == q) = (q == p) := by
  rcases p with ⟨s₁, e₁, i₁⟩; rcases q with ⟨s₂, e₂, i₂⟩
  cases s₁ <;> cases s₂ <;> simp [BEq.beq, eq_comm]

theorem any_beq_eq_contains (a : Pos) :
    ∀ (xs : List Pos), xs.any (fun x => x == a) = xs.contains a
  | [] => rfl
  | x :: xs => by
    simp only [List.any_cons, List.contains, List.elem, Pos.beq_comm x a]
    cases (a == x)
    · exact any_beq_eq_contains a xs
    · rfl

@[simp] theorem inTransitE_eval [DecidableEq C] {Γ} (K : ℕ) (s : Expr OO Γ gsTy)
    (qParty : Expr OO Γ .bool) (c : Expr OO Γ (.base .ct)) (ρ : Env Γ)
    (st : GameState St Msg C) (Q : Party)
    (heqCt : eqCt = (· == ·))
    (hK : st.trans.length ≤ K)
    (hs : s.eval ρ = gsEnc st) (hq : qParty.eval ρ = partyEnc Q) :
    (inTransitE K s qParty c).eval ρ = (st.inTransit Q (c.eval ρ)).map recEnc := by
  have htake : ((st.trans.map recEnc).take K) = st.trans.map recEnc :=
    List.take_of_length_le (by simpa using hK)
  simp only [inTransitE, GameState.inTransit, gsTrans, recPos, posSender, recCt,
    Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ,
    boolEq_eval, smOps, hs, hq, heqCt, gsEnc, htake]
  rw [find?_map_eq]
  congr 2
  funext ⟨⟨sender, ep, idx⟩, msg, ct⟩
  cases sender <;> cases Q <;> rfl

@[simp] theorem deleteE_eval {O' : Ops S} {Γ} (K : ℕ) (s : Expr O' Γ gsTy)
    (pos : Expr O' Γ posTy) (ρ : Env Γ) (st : GameState St Msg C) (p : Pos)
    (hTrans : st.trans.length ≤ K) (hChall : st.chall.length ≤ K) (hComp : st.comp.length ≤ K)
    (hs : s.eval ρ = gsEnc st) (hp : pos.eval ρ = posEnc p) :
    (deleteE K s pos).eval ρ = gsEnc (st.delete p) := by
  have ht1 : (st.trans.map recEnc).take K = st.trans.map recEnc :=
    List.take_of_length_le (by simpa using hTrans)
  have ht2 : (st.chall.map posEnc).take K = st.chall.map posEnc :=
    List.take_of_length_le (by simpa using hChall)
  have ht3 : (st.comp.map posEnc).take K = st.comp.map posEnc :=
    List.take_of_length_le (by simpa using hComp)
  simp only [deleteE, GameState.delete, gsMk, gsSt, gsB, gsWin, gsEpoch, gsIdx, gsTL, gsTrans,
    gsChall, gsComp, gsMaxAcc, gsLeaks, gsCorrs, recPos, Expr.eval, Expr.v0, Expr.v1, Expr.v2,
    Env.get_cons_zero, Env.get_cons_succ, posEq_eval, hs, hp, gsEnc, ht1, ht2, ht3]
  rw [foldr_filter_map, foldr_filter_map, foldr_filter_map]
  simp [recEnc, posDec_posEnc, bne]

@[simp] theorem acceptE_eval {O' : Ops S} {Γ} (K : ℕ) (s : Expr O' Γ gsTy) (p : Expr O' Γ .bool)
    (st' : Expr O' Γ (.base .st)) (pos : Expr O' Γ posTy) (ρ : Env Γ)
    (st : GameState St Msg C) (P : Party) (pos₀ : Pos)
    (hTrans : st.trans.length ≤ K) (hChall : st.chall.length ≤ K) (hComp : st.comp.length ≤ K)
    (hs : s.eval ρ = gsEnc st) (hp : p.eval ρ = partyEnc P) (hpos : pos.eval ρ = posEnc pos₀) :
    (acceptE K s p st' pos).eval ρ = gsEnc (st.accept P (st'.eval ρ) pos₀) := by
  have hdel := deleteE_eval K s pos ρ st pos₀ hTrans hChall hComp hs hpos
  simp only [acceptE, gsMk, Expr.eval, hdel, hp, hpos]
  cases P <;>
  · simp [GameState.accept, gsSt, gsB, gsWin, gsEpoch, gsIdx, gsTL, gsTrans,
      gsChall, gsComp, gsMaxAcc, gsLeaks, gsCorrs, posEpoch, posIdx, pGet, pSet,
      maxAccGet, maxAccSet, maxN_eval, gsEnc, posEnc, partyEnc,
      Function.update, Expr.eval, Expr.v0]
    funext j; split_ifs with hj <;> simp [hj]

@[simp] theorem compContainsE_eval {O' : Ops S} {Γ} (K : ℕ) (s : Expr O' Γ gsTy)
    (pos : Expr O' Γ posTy) (ρ : Env Γ) (st : GameState St Msg C) (pos₀ : Pos)
    (hComp : st.comp.length ≤ K) (hs : s.eval ρ = gsEnc st) (hpos : pos.eval ρ = posEnc pos₀) :
    (compContainsE K s pos).eval ρ = st.comp.contains pos₀ := by
  have ht : (st.comp.map posEnc).take K = st.comp.map posEnc :=
    List.take_of_length_le (by simpa using hComp)
  simp only [compContainsE, gsComp, Expr.eval, Expr.v0, Expr.v1,
    Env.get_cons_zero, Env.get_cons_succ, posEq_eval, hs, hpos, gsEnc, ht]
  rw [any_map_eq]
  simp only [posDec_posEnc]
  exact any_beq_eq_contains pos₀ st.comp

@[simp] theorem challContainsE_eval {O' : Ops S} {Γ} (K : ℕ) (s : Expr O' Γ gsTy)
    (pos : Expr O' Γ posTy) (ρ : Env Γ) (st : GameState St Msg C) (pos₀ : Pos)
    (hChall : st.chall.length ≤ K) (hs : s.eval ρ = gsEnc st) (hpos : pos.eval ρ = posEnc pos₀) :
    (challContainsE K s pos).eval ρ = st.chall.contains pos₀ := by
  have ht : (st.chall.map posEnc).take K = st.chall.map posEnc :=
    List.take_of_length_le (by simpa using hChall)
  simp only [challContainsE, gsChall, Expr.eval, Expr.v0, Expr.v1,
    Env.get_cons_zero, Env.get_cons_succ, posEq_eval, hs, hpos, gsEnc, ht]
  rw [any_map_eq]
  simp only [posDec_posEnc]
  exact any_beq_eq_contains pos₀ st.chall

@[simp] theorem trivialE_eval {O' : Ops S} {Γ} (K Δ : ℕ) (s : Expr O' Γ gsTy)
    (pos : Expr O' Γ posTy) (ρ : Env Γ) (st : GameState St Msg C) (pos₀ : Pos)
    (hTrans : st.trans.length ≤ K) (hComp : st.comp.length ≤ K)
    (hs : s.eval ρ = gsEnc st) (hpos : pos.eval ρ = posEnc pos₀) :
    (trivialE K Δ s pos).eval ρ = st.trivial Δ pos₀ := by
  have ht : (st.trans.map recEnc).take K = st.trans.map recEnc :=
    List.take_of_length_le (by simpa using hTrans)
  simp only [trivialE, Expr.eval, hs, hpos, orE_eval, healedByE_eval]
  rw [compContainsE_eval K _ _ _ st pos₀ hComp rfl rfl]
  simp only [GameState.trivial, gsTrans, gsTL, recPos, posEpoch,
    Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ,
    posEq_eval, gsEnc, ht]
  rw [any_map_eq]
  simp [recEnc, posEnc, posDec]

@[simp] theorem corrAllowedE_eval {O' : Ops S} {Γ} (K : ℕ) (s : Expr O' Γ gsTy)
    (p : Expr O' Γ .bool) (ρ : Env Γ) (st : GameState St Msg C) (P : Party)
    (hTrans : st.trans.length ≤ K) (hChall : st.chall.length ≤ K) (hComp : st.comp.length ≤ K)
    (hs : s.eval ρ = gsEnc st) (hp : p.eval ρ = partyEnc P) :
    (corrAllowedE K s p).eval ρ = st.corrAllowed P := by
  unfold corrAllowedE GameState.corrAllowed
  rw [letE_eval]
  have h0 : (Expr.pair s p).eval ρ = (gsEnc st, partyEnc P) := by simp [Expr.eval, hs, hp]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod gsTy .bool) (gsEnc st, partyEnc P) ρ
  have htCh : (st.chall.map posEnc).take K = st.chall.map posEnc :=
    List.take_of_length_le (by simpa using hChall)
  have htTr : (st.trans.map recEnc).take K = st.trans.map recEnc :=
    List.take_of_length_le (by simpa using hTrans)
  have hCh0 : (gsChall (.fst (Expr.v0 (O := O')))).eval ρ₁ = st.chall.map posEnc := rfl
  have hTr0 : (gsTrans (.fst (Expr.v0 (O := O')))).eval ρ₁ = st.trans.map recEnc := rfl
  simp only [Expr.eval, hCh0, hTr0, htCh, htTr]
  congr 1
  · congr 1
    rw [any_map_eq]
    congr 1; funext pos
    simp [ρ₁, posSender, otherE, posEnc, ← partyEnc_other, partyEnc_beq, Expr.eval,
      Expr.v0, Expr.v1]
  · congr 1
    rw [any_map_eq]
    congr 1; funext r
    have hcomp := compContainsE_eval (O' := O') K (.fst .v1) (recPos .v0)
      (Env.cons (t := recTy) (recEnc r) ρ₁) st r.pos hComp rfl rfl
    simp only [hcomp]
    simp [ρ₁, recPos, posSender, otherE, recEnc, posEnc, ← partyEnc_other, partyEnc_beq,
      Expr.eval, Expr.v0, Expr.v1]

@[simp] theorem afterCorrE_eval {O' : Ops S} {Γ} (K : ℕ) (s : Expr O' Γ gsTy)
    (p : Expr O' Γ .bool) (ρ : Env Γ) (st : GameState St Msg C) (P : Party)
    (hBound : SMStateBounded K st)
    (hs : s.eval ρ = gsEnc st) (hp : p.eval ρ = partyEnc P) :
    (afterCorrE K s p).eval ρ = gsEnc (afterCorrDedup st P) := by
  rcases hBound.comp_u with ⟨U, hUK, haccU, htransU⟩
  simp only [afterCorrE, leakE, maxOptE, gsMk, gsSt, gsB, gsWin, gsEpoch, gsIdx, gsTL,
    gsTrans, gsChall, gsComp, gsMaxAcc, gsLeaks, gsCorrs, recPos, posSender, otherE,
    Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get_cons_zero, Env.get_cons_succ,
    boolEq_eval, posEq_eval, maxN_eval, hs, hp, gsEnc]
  have hfold := foldr_dedup_map_eq (K := K) (encR := recEnc) (encP := posEnc)
    (posOf := Record.pos) (keep := fun r : Record Msg C => r.pos.sender == P.other)
    (keepE := fun rE => rE.1.1 == !partyEnc P)
    (posE := fun rE => rE.1)
    (eqP := fun p₁ p₂ => posDec p₁ == posDec p₂)
    (rs := st.trans) (acc := st.comp) (U := U)
    (by intro r; simp [recEnc, posEnc, ← partyEnc_other, partyEnc_beq])
    (by intro r; rfl)
    (by intro p₁ p₂; simp [posDec_posEnc])
    hBound.trans_le hUK haccU (fun r hr _ => htransU r hr)
  rw [hfold]
  cases P <;>
  · simp only [afterCorrDedup, GameState.leak, maxOpt, pGet, partyEnc,
      Expr.eval, Expr.v0, Env.get_cons_zero]
    cases st.tL <;> rfl

@[simp] theorem inWindowE_eval {O' : Ops S} {Γ} (s : Expr O' Γ gsTy) (p : Expr O' Γ .bool)
    (ρ : Env Γ) (st : GameState St Msg C) (P : Party)
    (hs : s.eval ρ = gsEnc st) (hp : p.eval ρ = partyEnc P) :
    (inWindowE s p).eval ρ = inWindow st P := by
  cases P <;> simp [inWindowE, inWindow, sendsInE, pGet, gsEpoch, hs, hp, gsEnc, partyEnc,
    Party.sendsIn, BEq.beq, Expr.eval, Expr.v0]

@[simp] theorem noBobEpoch0E_eval {O' : Ops S} {Γ} (s : Expr O' Γ gsTy) (p : Expr O' Γ .bool)
    (ρ : Env Γ) (st : GameState St Msg C) (P : Party)
    (hs : s.eval ρ = gsEnc st) (hp : p.eval ρ = partyEnc P) :
    (noBobEpoch0E s p).eval ρ = !((P == .B) && (st.epoch .B == 0)) := by
  cases P <;> simp [noBobEpoch0E, gsEpoch, hs, hp, gsEnc, partyEnc, Expr.eval, Expr.v0]
  rfl

@[simp] theorem noCorrB0E_eval {O' : Ops S} {Γ} (s : Expr O' Γ gsTy) (p : Expr O' Γ .bool)
    (ρ : Env Γ) (st : GameState St Msg C) (P : Party)
    (hs : s.eval ρ = gsEnc st) (hp : p.eval ρ = partyEnc P) :
    (noCorrB0E s p).eval ρ = !((P == .B) && (st.epoch .B == 0)) :=
  noBobEpoch0E_eval s p ρ st P hs hp

@[simp] theorem noSpkCorrE_eval {O' : Ops S} {Γ} (s : Expr O' Γ gsTy) (p : Expr O' Γ .bool)
    (ρ : Env Γ) (st : GameState St Msg C) (P : Party)
    (hs : s.eval ρ = gsEnc st) (hp : p.eval ρ = partyEnc P) :
    (noSpkCorrE s p).eval ρ = !((P == .A) && decide (st.epoch .A < 10)) := by
  cases P <;> simp [noSpkCorrE, gsEpoch, hs, hp, gsEnc, partyEnc, Expr.eval, Expr.v0]

@[simp] theorem noCorrBWinE_eval {O' : Ops S} {Γ} (s : Expr O' Γ gsTy) (p : Expr O' Γ .bool)
    (ρ : Env Γ) (st : GameState St Msg C) (P : Party)
    (hs : s.eval ρ = gsEnc st) (hp : p.eval ρ = partyEnc P) :
    (noCorrBWinE s p).eval ρ = !((P == .B) && decide (st.epoch .A < 10)) := by
  cases P <;> simp [noCorrBWinE, gsEpoch, hs, hp, gsEnc, partyEnc, Expr.eval, Expr.v0]

@[simp] theorem validGuessE_eval {S' : Sig} {O' : Ops S'} {Γ} (Δ : ℕ)
    (tLStar : Expr O' Γ (.opt .nat)) (tStar : Expr O' Γ .nat) (ρ : Env Γ) :
    (validGuessE Δ tLStar tStar).eval ρ = lastLeakGuessAdmissible Δ (tLStar.eval ρ) (tStar.eval ρ) :=
  healedByE_eval tLStar Δ tStar ρ

theorem foldr_filter_max? (tStar : ℕ) :
    ∀ (xs : List ℕ),
      xs.foldr (fun x (acc : Option ℕ) =>
        if decide (x < tStar) = true then
          match acc with
          | none => some x
          | some m => some (max x m)
        else acc) none = (xs.filter (· < tStar)).max?
  | [] => rfl
  | x :: xs => by
    simp only [List.foldr_cons, List.filter_cons, foldr_filter_max? tStar xs]
    by_cases h : x < tStar
    · simp only [h, decide_true, ↓reduceIte, List.max?_cons]
      cases (List.filter (· < tStar) xs).max? <;> rfl
    · simp [h]

@[simp] theorem optNatEqE_eval {S' : Sig} {O' : Ops S'} {Γ}
    (a b : Expr O' Γ (.opt .nat)) (ρ : Env Γ) :
    (optNatEqE a b).eval ρ = (a.eval ρ == b.eval ρ) := by
  simp only [optNatEqE, Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ]
  rcases a.eval ρ with _ | x <;> rcases b.eval ρ with _ | y <;> rfl

theorem anyB_eval {S' : Sig} {O' : Ops S'} {Γ} {t : Ty S'}
    (K : ℕ) (xs : Expr O' Γ (.list t)) (p : Expr O' (t :: Γ) .bool) (ρ : Env Γ) :
    (Expr.anyB K xs p).eval ρ = ((xs.eval ρ).take K).any (fun x => p.eval (Env.cons x ρ)) := rfl

theorem and_eval {S' : Sig} {O' : Ops S'} {Γ} (a b : Expr O' Γ .bool) (ρ : Env Γ) :
    (Expr.and a b).eval ρ = (a.eval ρ && b.eval ρ) := rfl

theorem not_eval {S' : Sig} {O' : Ops S'} {Γ} (a : Expr O' Γ .bool) (ρ : Env Γ) :
    (Expr.not a).eval ρ = !a.eval ρ := rfl

theorem not_any_eq_all_not {α : Type} (xs : List α) (p q : α → Bool) (h : ∀ x, p x = q x) :
    (!xs.any p) = xs.all (fun x => !q x) := by
  rw [List.all_eq_not_any_not]
  congr 2; funext x; rw [h x, Bool.not_not]

theorem not_any_map_eq_all_not {α β : Type} (f : α → β) (xs : List α) (p : β → Bool)
    (q : α → Bool) (h : ∀ x, p (f x) = q x) :
    (!(xs.map f).any p) = xs.all (fun x => !q x) := by
  rw [any_map_eq]
  exact not_any_eq_all_not xs (fun x => p (f x)) q h

end BookkeepingEval

/-! ## Oracle evaluation agreement -/

section OracleEval

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

local notation "S" => smSig Key St St₂ Msg Coins RCoins C
local notation "OO" => smOps init send receive eqMsg eqCt blank injOK stOK φ

@[simp] theorem liftP_pure {ι : Type} {T : OracleSpec ι} (I : Iface S T) {α : Type} (x : α) :
    I.liftP (pure x) = pure x := by
  simp [Iface.liftP]

@[simp] theorem liftP_bind {ι : Type} {T : OracleSpec ι} (I : Iface S T) {α β : Type}
    (m : ProbComp α) (k : α → ProbComp β) :
    I.liftP (m >>= k) = I.liftP m >>= fun x => I.liftP (k x) := by
  simp [Iface.liftP]

/-- Agreement predicate linking a `ConfigRC` expression bundle to a shallow `SM.ConfigR`. -/
structure ConfigRCAgrees (K : ℕ) (blankFn : Msg → Msg) (injOKFn : C → Bool)
    (cfg : ConfigRC OO) (cfgR : ConfigR St Msg C) : Prop where
  deliverWin_eq : cfg.deliverWin = cfgR.base.deliverWin
  r1_eq : cfg.r1 = cfgR.r1
  injectFull_eq : ∀ {Γ} (e : Expr OO Γ .nat) (ρ : Env Γ),
    (cfg.injectFullE e).eval ρ = cfgR.base.injectFull (e.eval ρ)
  challOK_eq : ∀ {Γ} (e : Expr OO Γ .nat) (ρ : Env Γ),
    (cfg.challOKE e).eval ρ = cfgR.base.challAllowedIn (e.eval ρ)
  challMsg_eq : ∀ {Γ} (ep : Expr OO Γ .nat) (b : Expr OO Γ .bool)
    (m₀ m₁ : Expr OO Γ (.base .msg)) (ρ : Env Γ),
    (cfg.challMsgE ep b m₀ m₁).eval ρ =
      (cfgR.base.challMsg (ep.eval ρ)).getD (if b.eval ρ then m₁.eval ρ else m₀.eval ρ)
  must_eq : ∀ {Γ} (s : Expr OO Γ gsTy) (p : Expr OO Γ .bool) (r : Expr OO Γ recTy) (ρ : Env Γ)
    (st : GameState St Msg C) (P : Party) (rec_ : Record Msg C),
    SMStateBounded K st → s.eval ρ = gsEnc st → p.eval ρ = partyEnc P → r.eval ρ = recEnc rec_ →
    (cfg.mustE s p r).eval ρ = cfgR.must st P rec_
  sendOK_eq : ∀ {Γ} (s : Expr OO Γ gsTy) (p : Expr OO Γ .bool) (ρ : Env Γ)
    (st : GameState St Msg C) (P : Party),
    SMStateBounded K st → s.eval ρ = gsEnc st → p.eval ρ = partyEnc P →
    (cfg.sendOKE s p).eval ρ = cfgR.sendOK st P
  corrOK_eq : ∀ {Γ} (s : Expr OO Γ gsTy) (p : Expr OO Γ .bool) (ρ : Env Γ)
    (st : GameState St Msg C) (P : Party),
    SMStateBounded K st → s.eval ρ = gsEnc st → p.eval ρ = partyEnc P →
    (cfg.corrOKE s p).eval ρ = cfgR.corrOK st P
  injOK_eq : ∀ {Γ} (c : Expr OO Γ (.base .ct)) (ρ : Env Γ),
    (cfg.injOKE c).eval ρ = cfgR.injOK (c.eval ρ)

theorem samIfNecC_eval [SampleableType Coins] {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (drawCoins : ∀ {Γ}, Comp OO I Γ (.opt (.base .coins)))
    (hCoins : ∀ {Γ} (ρ' : Env Γ), (drawCoins (Γ := Γ)).eval ρ' =
      some <$> I.liftP ($ᵗ Coins : ProbComp Coins))
    {Γ} (optR : Expr OO Γ (.opt (.base .coins))) (ρ : Env Γ) :
    (samIfNecC (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) drawCoins optR).eval ρ =
      some <$> I.liftP (samIfNec (optR.eval ρ)) := by
  simp only [samIfNecC, Comp.eval]
  rcases optR.eval ρ with _ | r
  · simp [samIfNec, hCoins, Expr.eval, Expr.v0, map_eq_bind_pure_comp]
  · simp [samIfNec, Expr.eval, Expr.v0]

theorem Comp.eval_bind_ret {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ} {t u : Ty S} (e : Expr OO Γ t) (k : Comp OO I (t :: Γ) u) (ρ : Env Γ) :
    (Comp.bind (.ret e) k).eval ρ = k.eval (Env.cons (e.eval ρ) ρ) :=
  pure_bind (e.eval ρ) (fun x => k.eval (Env.cons x ρ))

theorem Comp.eval_ite {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ} {t : Ty S} (c : Expr OO Γ .bool) (th el : Comp OO I Γ t) (ρ : Env Γ) :
    (Comp.ite c th el).eval ρ = if c.eval ρ then th.eval ρ else el.eval ρ := rfl

theorem Comp.eval_bind {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ} {t u : Ty S} (m : Comp OO I Γ t) (k : Comp OO I (t :: Γ) u) (ρ : Env Γ) :
    (Comp.bind m k).eval ρ = (m.eval ρ >>= fun x => k.eval (Env.cons x ρ)) := rfl

theorem Comp.eval_caseOpt {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ} {t u : Ty S} (e : Expr OO Γ (.opt t))
    (noneB : Comp OO I Γ u) (someB : Comp OO I (t :: Γ) u) (ρ : Env Γ) :
    (Comp.caseOpt e noneB someB).eval ρ =
      match e.eval ρ with
      | none => noneB.eval ρ
      | some x => someB.eval (Env.cons x ρ) := by
  rcases h : e.eval ρ with _ | x <;> simp [Comp.eval, h]

theorem Comp.eval_caseOpt_v0_some {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ} {t u : Ty S} (x : t.denote)
    (noneB : Comp OO I (.opt t :: Γ) u) (someB : Comp OO I (t :: .opt t :: Γ) u) (ρ : Env Γ) :
    (Comp.caseOpt .v0 noneB someB).eval (Env.cons (t := .opt t) (some x) ρ) =
      someB.eval (Env.cons (t := t) x (Env.cons (t := .opt t) (some x) ρ)) := rfl

theorem Comp.eval_ret {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ} {t : Ty S} (e : Expr OO Γ t) (ρ : Env Γ) :
    (Comp.ret (I := I) e).eval ρ = pure (e.eval ρ) := rfl

@[simp] theorem op_send_eval {Γ}
    (stE : Expr OO Γ (.base .st)) (mE : Expr OO Γ (.base .msg))
    (cE : Expr OO Γ (.base .coins)) (ρ : Env Γ) :
    (Expr.op (O := OO) SMOp.send (.pair stE (.pair mE cE))).eval ρ =
      send (stE.eval ρ) (mE.eval ρ) (cE.eval ρ) := rfl

@[simp] theorem op_receive_eval (B : ℕ) {Γ}
    (stE : Expr OO Γ (.base .st)) (ctE : Expr OO Γ (.base .ct))
    (rcE : Expr OO Γ (.base .rcoins)) (ρ : Env Γ) :
    (Expr.op (O := OO) (SMOp.receive B) (.pair stE (.pair ctE rcE))).eval ρ =
      (receive (stE.eval ρ) (ctE.eval ρ) (rcE.eval ρ)).map
        (fun x => (x.1, min x.2.1 B, min x.2.2.1 B, x.2.2.2)) := rfl

theorem corrRC_eval {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (K : ℕ) (cfg : ConfigRC OO) (cfgR : ConfigR St Msg C)
    (hCfg : ConfigRCAgrees K blank injOK cfg cfgR)
    {Γ} (s : Expr OO Γ gsTy) (p : Expr OO Γ .bool) (ρ : Env Γ)
    (st : GameState St Msg C) (P : Party)
    (hBound : SMStateBounded K st)
    (hs : s.eval ρ = gsEnc st) (hp : p.eval ρ = partyEnc P) :
    (corrRC (I := I) K cfg s p).eval ρ =
      Prod.map id gsEnc <$> I.liftP ((corrRDedup cfgR P).run st) := by
  unfold corrRC corrRDedup
  simp only [Comp.eval, Expr.eval, hs, hp, pure_bind]
  set ρ₁ := Env.cons (t := (.prod gsTy .bool : Ty S)) (gsEnc st, partyEnc P) ρ
  have hRefuse : (orE (gsWin (.fst (Expr.v0 (O := OO))))
      (orE (.not (corrAllowedE K (.fst .v0) (.snd .v0)))
        (orE (.and (.bool cfg.r1) (inWindowE (.fst .v0) (.snd .v0)))
          (.not (cfg.corrOKE (.fst .v0) (.snd .v0)))))).eval ρ₁ =
      (st.win || !st.corrAllowed P || (cfgR.r1 && inWindow st P) || !cfgR.corrOK st P) := by
    simp only [orE_eval, Expr.eval]
    rw [corrAllowedE_eval K (.fst .v0) (.snd .v0) ρ₁ st P
          hBound.trans_le hBound.chall_le hBound.comp_le rfl rfl,
        inWindowE_eval (.fst .v0) (.snd .v0) ρ₁ st P rfl rfl,
        hCfg.corrOK_eq (.fst .v0) (.snd .v0) ρ₁ st P hBound rfl rfl,
        hCfg.r1_eq]
    simp [ρ₁, gsWin, gsEnc, Expr.eval, Expr.v0, Bool.or_assoc]
  rw [hRefuse]
  by_cases h : (st.win || !st.corrAllowed P || (cfgR.r1 && inWindow st P) || !cfgR.corrOK st P)
  · simp only [StateT.run_bind, StateT.run_get, pure_bind, h, ↓reduceIte,
      StateT.run_pure, liftP_pure, map_pure, Prod.map]
    simp [ρ₁, Expr.eval, Expr.v0]
  · simp only [h, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind,
      liftP_pure, map_pure, Prod.map]
    rw [pGet_eval (gsSt (.fst .v0)) (.snd .v0) ρ₁ st.st P rfl rfl,
        afterCorrE_eval K (.fst .v0) (.snd .v0) ρ₁ st P hBound rfl rfl]
    rfl

theorem transmitRC_eval [SampleableType Coins] {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (sm : SMSchemeR Key St Msg Coins RCoins C)
    (Δ qep K : ℕ) (cfg : ConfigRC OO) (cfgR : ConfigR St Msg C)
    (hCfg : ConfigRCAgrees K blank injOK cfg cfgR)
    (hSend : send = fun st m r => some (sm.send st m r))
    (drawCoins : ∀ {Γ}, Comp OO I Γ (.opt (.base .coins)))
    (hCoins : ∀ {Γ} (ρ' : Env Γ), (drawCoins (Γ := Γ)).eval ρ' =
      some <$> I.liftP ($ᵗ Coins : ProbComp Coins))
    {Γ} (s : Expr OO Γ gsTy)
    (arg : Expr OO Γ (.prod .bool (.prod (.base .msg) (.opt (.base .coins)))))
    (ρ : Env Γ) (st : GameState St Msg C) (P : Party) (m : Msg) (optR : Option Coins)
    (hBound : SMStateBounded K st)
    (hs : s.eval ρ = gsEnc st) (harg : arg.eval ρ = (partyEnc P, m, optR)) :
    (transmitRC Δ qep cfg drawCoins s arg).eval ρ =
      Prod.map id gsEnc <$> I.liftP ((transmitR sm Δ qep cfgR (P, m, optR)).run st) := by
  unfold transmitRC transmitR transmitImpl
  rw [Comp.eval_bind_ret]
  have h0 : (Expr.pair s arg).eval ρ = (gsEnc st, partyEnc P, m, optR) := by
    simp [Expr.eval, hs, harg]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := (.prod gsTy (.prod .bool (.prod (.base .msg) (.opt (.base .coins)))) : Ty S))
    (gsEnc st, partyEnc P, m, optR) ρ
  rw [Comp.eval_ite]
  have hSendOK : (cfg.sendOKE (.fst .v0) (.fst (.snd .v0))).eval ρ₁ = cfgR.sendOK st P :=
    hCfg.sendOK_eq (.fst .v0) (.fst (.snd .v0)) ρ₁ st P hBound rfl rfl
  have hWin : (gsWin (.fst (Expr.v0 (O := OO)))).eval ρ₁ = st.win := rfl
  simp only [orE_eval, Expr.eval, hSendOK, hWin]
  by_cases hok : cfgR.sendOK st P
  · by_cases hwin : st.win
    · simp [ρ₁, hok, hwin, Comp.eval_ret, StateT.run_bind, StateT.run_get, StateT.run_pure,
        Expr.eval, Expr.v0]
    · have hOptR : (Expr.snd (.snd (.snd (Expr.v0 (O := OO))))).eval ρ₁ = optR := rfl
      simp only [hok, hwin, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
        Comp.eval_bind, samIfNecC_eval drawCoins hCoins, hOptR,
        StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
        pure_bind, bind_assoc, liftP_bind, map_bind, bind_map_left]
      refine bind_congr fun ⟨coins, bad⟩ => ?_
      rw [Comp.eval_caseOpt_v0_some]
      set ρ₂ := Env.cons (t := (.prod (.base .coins) .bool : Ty S)) (coins, bad)
        (Env.cons (t := (.opt (.prod (.base .coins) .bool) : Ty S)) (some (coins, bad)) ρ₁)
      rw [Comp.eval_caseOpt]
      have hep : (epMgmtE Δ qep (.fst (Expr.v2 (O := OO))) (.fst (.snd .v2)) (.snd .v0)).eval ρ₂ =
          (st.epMgmt Δ qep P bad).map gsEnc := by
        rw [epMgmtE_eval Δ qep (.fst .v2) (.fst (.snd .v2)) (.snd .v0) ρ₂ st P rfl rfl]
        rfl
      rw [hep]
      rcases st.epMgmt Δ qep P bad with _ | s₁
      · simp [ρ₂, ρ₁, Comp.eval_ret, StateT.run_pure, Expr.eval, Expr.v2]
      · simp only [Option.map_some]
        set ρ₃ := Env.cons (t := gsTy) (gsEnc s₁) ρ₂
        rw [Comp.eval_caseOpt]
        have hsend_eval : (Expr.op (O := OO) SMOp.send
            (.pair (pGet (gsSt .v0) (.fst (.snd .v3)))
              (.pair (.fst (.snd (.snd .v3))) (.fst .v1)))).eval ρ₃ =
            some (sm.send (s₁.st P) m coins) := by
          rw [op_send_eval, hSend]
          cases P <;> rfl
        rw [hsend_eval]
        simp only [Comp.eval_ret, pair_eval, StateT.run_bind, StateT.run_set, StateT.run_pure,
          pure_bind, liftP_pure, map_pure, Prod.map]
        set ρ₄ := Env.cons (t := (.prod (.base .st) (.base .ct) : Ty S))
          (sm.send (s₁.st P) m coins) ρ₃
        have hrec : (recordE Δ (Expr.v1 (O := OO)) (.fst (.snd .v4)) (.fst .v0)
            (.pair (.pair (.fst (.snd .v4))
              (.pair (pGet (gsEpoch .v1) (.fst (.snd .v4)))
                (.add (pGet (gsIdx .v1) (.fst (.snd .v4))) (.nat 1))))
              (.pair (.fst (.snd (.snd .v4))) (.snd .v0))) (.bool false)).eval ρ₄ =
            gsEnc (s₁.record Δ P (sm.send (s₁.st P) m coins).1
              ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, (sm.send (s₁.st P) m coins).2⟩ false) := by
          refine recordE_eval Δ (Expr.v1 (O := OO)) (.fst (.snd .v4)) (.fst .v0) _ (.bool false)
            ρ₄ s₁ P _ rfl rfl ?_
          have hEp4 : (pGet (gsEpoch (Expr.v1 (O := OO))) (.fst (.snd .v4))).eval ρ₄ =
              s₁.epoch P := by
            cases P <;> rfl
          have hIdx4 : (pGet (gsIdx (Expr.v1 (O := OO))) (.fst (.snd .v4))).eval ρ₄ =
              s₁.idx P := by
            cases P <;> rfl
          simp only [Expr.eval, recEnc, posEnc, hEp4, hIdx4]
          rfl
        rw [hrec]
        rfl
  · simp [ρ₁, hok, Comp.eval_ret, StateT.run_bind, StateT.run_get, StateT.run_pure,
      Expr.eval, Expr.v0]

theorem challRC_eval [SampleableType Coins] {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (sm : SMSchemeR Key St Msg Coins RCoins C)
    (Δ qep K : ℕ) (cfg : ConfigRC OO) (cfgR : ConfigR St Msg C)
    (hCfg : ConfigRCAgrees K blank injOK cfg cfgR)
    (hSend : send = fun st m r => some (sm.send st m r))
    (drawCoins : ∀ {Γ}, Comp OO I Γ (.opt (.base .coins)))
    (hCoins : ∀ {Γ} (ρ' : Env Γ), (drawCoins (Γ := Γ)).eval ρ' =
      some <$> I.liftP ($ᵗ Coins : ProbComp Coins))
    {Γ} (s : Expr OO Γ gsTy)
    (arg : Expr OO Γ (.prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .coins))))))
    (ρ : Env Γ) (st : GameState St Msg C) (P : Party) (m₀ m₁ : Msg) (optR : Option Coins)
    (hBound : SMStateBounded K st)
    (hs : s.eval ρ = gsEnc st) (harg : arg.eval ρ = (partyEnc P, m₀, m₁, optR)) :
    (challRC Δ qep cfg drawCoins s arg).eval ρ =
      Prod.map id gsEnc <$> I.liftP ((challR sm Δ qep cfgR (P, m₀, m₁, optR)).run st) := by
  unfold challRC challR challImpl
  rw [Comp.eval_bind_ret]
  have h0 : (Expr.pair s arg).eval ρ = (gsEnc st, partyEnc P, m₀, m₁, optR) := by
    simp [Expr.eval, hs, harg]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := (.prod gsTy
      (.prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .coins))))) : Ty S))
    (gsEnc st, partyEnc P, m₀, m₁, optR) ρ
  rw [Comp.eval_ite]
  have hSendOK : (cfg.sendOKE (.fst .v0) (.fst (.snd .v0))).eval ρ₁ = cfgR.sendOK st P :=
    hCfg.sendOK_eq (.fst .v0) (.fst (.snd .v0)) ρ₁ st P hBound rfl rfl
  have hWin : (gsWin (.fst (Expr.v0 (O := OO)))).eval ρ₁ = st.win := rfl
  simp only [orE_eval, Expr.eval, hSendOK, hWin]
  by_cases hok : cfgR.sendOK st P
  · by_cases hwin : st.win
    · simp [ρ₁, hok, hwin, Comp.eval_ret, StateT.run_bind, StateT.run_get, StateT.run_pure,
        Expr.eval, Expr.v0]
    · have hOptR : (Expr.snd (.snd (.snd (.snd (Expr.v0 (O := OO)))))).eval ρ₁ = optR := rfl
      simp only [hok, hwin, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
        Comp.eval_bind, samIfNecC_eval drawCoins hCoins, hOptR,
        StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
        pure_bind, bind_assoc, liftP_bind, map_bind, bind_map_left]
      refine bind_congr fun ⟨coins, bad⟩ => ?_
      rw [Comp.eval_caseOpt_v0_some]
      set ρ₂ := Env.cons (t := (.prod (.base .coins) .bool : Ty S)) (coins, bad)
        (Env.cons (t := (.opt (.prod (.base .coins) .bool) : Ty S)) (some (coins, bad)) ρ₁)
      rw [Comp.eval_caseOpt]
      have hep : (epMgmtE Δ qep (.fst (Expr.v2 (O := OO))) (.fst (.snd .v2)) (.snd .v0)).eval ρ₂ =
          (st.epMgmt Δ qep P bad).map gsEnc := by
        rw [epMgmtE_eval Δ qep (.fst .v2) (.fst (.snd .v2)) (.snd .v0) ρ₂ st P rfl rfl]
        rfl
      rw [hep]
      rcases st.epMgmt Δ qep P bad with _ | s₁
      · simp [ρ₂, ρ₁, Comp.eval_ret, StateT.run_pure, Expr.eval, Expr.v2]
      · simp only [Option.map_some]
        set ρ₃ := Env.cons (t := gsTy) (gsEnc s₁) ρ₂
        rw [Comp.eval_ite]
        simp only [orE_eval, Expr.eval]
        have hSafe : (safeChE Δ (Expr.v0 (O := OO)) (.fst (.snd .v3))).eval ρ₃ = s₁.safeCh Δ P :=
          safeChE_eval Δ (Expr.v0 (O := OO)) (.fst (.snd .v3)) ρ₃ s₁ P rfl rfl
        have hEp : (pGet (gsEpoch (Expr.v0 (O := OO))) (.fst (.snd .v3))).eval ρ₃ = s₁.epoch P := by
          cases P <;> rfl
        have hChallOK : (cfg.challOKE (pGet (gsEpoch .v0) (.fst (.snd .v3)))).eval ρ₃ =
            cfgR.base.challAllowedIn (s₁.epoch P) := by
          rw [hCfg.challOK_eq, hEp]
        rw [hSafe, hChallOK]
        by_cases hch : (!s₁.safeCh Δ P || !cfgR.base.challAllowedIn (s₁.epoch P))
        · simp [ρ₃, ρ₂, ρ₁, hch, Comp.eval_ret, StateT.run_pure, Expr.eval, Expr.v3]
        · simp only [hch, Bool.false_eq_true, ↓reduceIte, Comp.eval_caseOpt]
          have hm3 : (cfg.challMsgE (pGet (gsEpoch .v0) (.fst (.snd .v3))) (gsB (.fst .v3))
              (.fst (.snd (.snd .v3))) (.fst (.snd (.snd (.snd .v3))))).eval ρ₃ =
              (cfgR.base.challMsg (s₁.epoch P)).getD (if st.b then m₁ else m₀) := by
            rw [hCfg.challMsg_eq, hEp]
            rfl
          have hsend_eval : (Expr.op (O := OO) SMOp.send
              (.pair (pGet (gsSt .v0) (.fst (.snd .v3)))
                (.pair (cfg.challMsgE (pGet (gsEpoch .v0) (.fst (.snd .v3))) (gsB (.fst .v3))
                  (.fst (.snd (.snd .v3))) (.fst (.snd (.snd (.snd .v3))))) (.fst .v1)))).eval ρ₃ =
              some (sm.send (s₁.st P)
                ((cfgR.base.challMsg (s₁.epoch P)).getD (if st.b then m₁ else m₀)) coins) := by
            rw [op_send_eval, hm3, hSend]
            cases P <;> rfl
          rw [hsend_eval]
          simp only [Comp.eval_ret, pair_eval, StateT.run_bind, StateT.run_set, StateT.run_pure,
            pure_bind, liftP_pure, map_pure, Prod.map]
          set mChall := (cfgR.base.challMsg (s₁.epoch P)).getD (if st.b then m₁ else m₀)
          set ρ₄ := Env.cons (t := (.prod (.base .st) (.base .ct) : Ty S))
            (sm.send (s₁.st P) mChall coins) ρ₃
          have hrec : (recordE Δ (Expr.v1 (O := OO)) (.fst (.snd .v4)) (.fst .v0)
              (.pair (.pair (.fst (.snd .v4))
                (.pair (pGet (gsEpoch .v1) (.fst (.snd .v4)))
                  (.add (pGet (gsIdx .v1) (.fst (.snd .v4))) (.nat 1))))
                (.pair (cfg.challMsgE (pGet (gsEpoch .v1) (.fst (.snd .v4))) (gsB (.fst .v4))
                  (.fst (.snd (.snd .v4))) (.fst (.snd (.snd (.snd .v4))))) (.snd .v0)))
              (.bool true)).eval ρ₄ =
              gsEnc (s₁.record Δ P (sm.send (s₁.st P) mChall coins).1
                ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, mChall, (sm.send (s₁.st P) mChall coins).2⟩
                true) := by
            refine recordE_eval Δ (Expr.v1 (O := OO)) (.fst (.snd .v4)) (.fst .v0) _ (.bool true)
              ρ₄ s₁ P _ rfl rfl ?_
            have hEp4 : (pGet (gsEpoch (Expr.v1 (O := OO))) (.fst (.snd .v4))).eval ρ₄ =
                s₁.epoch P := by
              cases P <;> rfl
            have hIdx4 : (pGet (gsIdx (Expr.v1 (O := OO))) (.fst (.snd .v4))).eval ρ₄ =
                s₁.idx P := by
              cases P <;> rfl
            have hm4 : (cfg.challMsgE (pGet (gsEpoch .v1) (.fst (.snd .v4))) (gsB (.fst .v4))
                (.fst (.snd (.snd .v4))) (.fst (.snd (.snd (.snd .v4))))).eval ρ₄ = mChall := by
              rw [hCfg.challMsg_eq, hEp4]
              rfl
            simp only [Expr.eval, recEnc, posEnc, hEp4, hIdx4, hm4]
            rfl
          rw [hrec]
          rfl
  · simp [ρ₁, hok, Comp.eval_ret, StateT.run_bind, StateT.run_get, StateT.run_pure,
      Expr.eval, Expr.v0]

/-! ## Static query bounds -/

@[simp] theorem corrRC_queries {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (K : ℕ) (cfg : ConfigRC OO) {Γ} (s : Expr OO Γ gsTy) (p : Expr OO Γ .bool) :
    (corrRC (I := I) K cfg s p).queries w ws = 0 := by
  simp [corrRC, Comp.queries]

@[simp] theorem samIfNecC_queries {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (drawCoins : ∀ {Γ}, Comp OO I Γ (.opt (.base .coins)))
    {Γ} (optR : Expr OO Γ (.opt (.base .coins))) :
    (samIfNecC (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) drawCoins optR).queries w ws =
      (drawCoins (Γ := Γ)).queries w ws := by
  simp [samIfNecC, Comp.queries]

@[simp] theorem transmitRC_queries {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (Δ qep : ℕ) (cfg : ConfigRC OO)
    (drawCoins : ∀ {Γ}, Comp OO I Γ (.opt (.base .coins)))
    {Γ} (s : Expr OO Γ gsTy)
    (arg : Expr OO Γ (.prod .bool (.prod (.base .msg) (.opt (.base .coins))))) :
    (transmitRC Δ qep cfg drawCoins s arg).queries w ws =
      (drawCoins (Γ := .prod gsTy
        (.prod .bool (.prod (.base .msg) (.opt (.base .coins)))) :: Γ)).queries w ws := by
  simp [transmitRC, Comp.queries]

@[simp] theorem challRC_queries {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (Δ qep : ℕ) (cfg : ConfigRC OO)
    (drawCoins : ∀ {Γ}, Comp OO I Γ (.opt (.base .coins)))
    {Γ} (s : Expr OO Γ gsTy)
    (arg : Expr OO Γ
      (.prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .coins)))))) :
    (challRC Δ qep cfg drawCoins s arg).queries w ws =
      (drawCoins (Γ := .prod gsTy
        (.prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .coins))))) :: Γ)).queries
        w ws := by
  simp [challRC, Comp.queries]

end OracleEval

end CryptoGames.SM
