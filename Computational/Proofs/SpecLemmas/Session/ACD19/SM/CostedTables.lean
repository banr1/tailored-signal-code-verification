/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Session.ACD19.SM.Theorem8And12Statements
public import Computational.Specifications.Reductions.ReductionDsl.Core
public import LibsignalBinary.Specifications.CryptoGames.SM.Game
public import LibsignalBinary.Specifications.CryptoGames.SM.LibsignalGame

/-!
# Shared `ReductionDsl` tables, interfaces, and codecs for Secure Messaging

**Checked by Lean.**

Defines the `ReductionDsl` signature (`smSig`), operation and sampler tables (`smOps`,
`smSamplers`), oracle interfaces (`smIface`, `smIfaceDF`), game codecs (`smCodec`, `smCodecDF`),
and expression helpers for the two-party secure-messaging game (`SM.spec` and `SM.specDF`), with
unit abstract sort sizes matching ACD19's black-box cost model.
-/

@[expose] public section

namespace CryptoGames.SM

open ReductionDsl OracleSpec OracleComp

def partyEnc : Party → Bool
  | .A => false
  | .B => true

def partyDec : Bool → Party
  | false => .A
  | true => .B

/-- Abstract value sorts of an SM scheme and its state relabellings. -/
inductive SMSort
  | key | st | st2 | msg | coins | rcoins | ct
  deriving DecidableEq

@[reducible] def SMSort.den (Key St St₂ Msg Coins RCoins C : Type) : SMSort → Type
  | .key => Key
  | .st => St
  | .st2 => St₂
  | .msg => Msg
  | .coins => Coins
  | .rcoins => RCoins
  | .ct => C

/-- `ReductionDsl` signature for SM schemes, assigning size 1 to each abstract sort. -/
@[reducible] def smSig (Key St St₂ Msg Coins RCoins C : Type) : Sig where
  Base := SMSort
  den := SMSort.den Key St St₂ Msg Coins RCoins C
  sz := fun _ _ => 1

/-- Primitive SM operations, configuration predicates, and state relabelling. -/
inductive SMOp
  | init
  | send
  | receive (B : ℕ)
  | eqMsg
  | eqCt
  | blank
  | injOK
  | stOK
  | relabelSt
  deriving DecidableEq

/-- Operation table for `SMOp`, with unit cost except `bits B` for `receive B`. -/
@[reducible] def smOps {Key St St₂ Msg Coins RCoins C : Type}
    (init : Party → Key → Option St := fun _ _ => none)
    (send : St → Msg → Coins → Option (St × C) := fun _ _ _ => none)
    (receive : St → C → RCoins → Option (St × ℕ × ℕ × Msg) := fun _ _ _ => none)
    (eqMsg : Msg → Msg → Bool := fun _ _ => false)
    (eqCt : C → C → Bool := fun _ _ => false)
    (blank : Msg → Msg := id)
    (injOK : C → Bool := fun _ => true)
    (stOK : Party → St → Bool := fun _ _ => true)
    (φ : St → Option St₂ := fun _ => none) :
    Ops (smSig Key St St₂ Msg Coins RCoins C) where
  Op := SMOp
  dom := fun
    | .init => .prod .bool (.base .key)
    | .send => .prod (.base .st) (.prod (.base .msg) (.base .coins))
    | .receive _ => .prod (.base .st) (.prod (.base .ct) (.base .rcoins))
    | .eqMsg => .prod (.base .msg) (.base .msg)
    | .eqCt => .prod (.base .ct) (.base .ct)
    | .blank => .base .msg
    | .injOK => .base .ct
    | .stOK => .prod .bool (.base .st)
    | .relabelSt => .base .st
  cod := fun
    | .init => .opt (.base .st)
    | .send => .opt (.prod (.base .st) (.base .ct))
    | .receive _ => .opt (.prod (.base .st) (.prod .nat (.prod .nat (.base .msg))))
    | .eqMsg => .bool
    | .eqCt => .bool
    | .blank => .base .msg
    | .injOK => .bool
    | .stOK => .bool
    | .relabelSt => .opt (.base .st2)
  eval := fun
    | .init, (p, k) => init (partyDec p) k
    | .send, (st, m, r) => send st m r
    | .receive B, (st, c, rc) =>
      (receive st c rc).map fun (st', t', i', m') => (st', min t' B, min i' B, m')
    | .eqMsg, (m₁, m₂) => eqMsg m₁ m₂
    | .eqCt, (c₁, c₂) => eqCt c₁ c₂
    | .blank, m => blank m
    | .injOK, c => injOK c
    | .stOK, (p, st) => stOK (partyDec p) st
    | .relabelSt, st => φ st
  cost := fun
    | .receive B => bits B
    | _ => 1

inductive SMSamp
  | bit | key | coins | rcoins
  deriving DecidableEq

/-- Coin sampler table for SM reductions and games at unit cost. -/
@[reducible] def smSamplers {Key St St₂ Msg Coins RCoins C : Type}
    (sampKey : ProbComp (Option Key) := pure none)
    (sampCoins : ProbComp (Option Coins) := pure none)
    (sampRCoins : ProbComp (Option RCoins) := pure none) :
    Samplers (smSig Key St St₂ Msg Coins RCoins C) where
  Samp := SMSamp
  sDom := fun _ => .unit
  sTy := fun
    | .bit => .bool
    | .key => .opt (.base .key)
    | .coins => .opt (.base .coins)
    | .rcoins => .opt (.base .rcoins)
  samp := fun
    | .bit, _ => ($ᵗ Bool : ProbComp Bool)
    | .key, _ => sampKey
    | .coins, _ => sampCoins
    | .rcoins, _ => sampRCoins
  sCost := fun _ => 1

/-- `ReductionDsl` representation of `SM.RecvResult Msg`. -/
@[reducible] def smRrTy (Key St St₂ Msg Coins RCoins C : Type) :
    Ty (smSig Key St St₂ Msg Coins RCoins C) :=
  .sum .unit (.prod .nat (.prod .nat (.opt (.base .msg))))

def smRrEnc {Msg : Type} : RecvResult Msg → Unit ⊕ (ℕ × ℕ × Option Msg)
  | .rejected => .inl ()
  | .accepted t i m => .inr (t, i, m)

def smRrDec {Msg : Type} : Unit ⊕ (ℕ × ℕ × Option Msg) → RecvResult Msg
  | .inl () => .rejected
  | .inr (t, i, m) => .accepted t i m

inductive SMTag
  | tr | ch | dl | ij | cr
  deriving DecidableEq

/-- Target interface into `unifSpec + SM.spec` with unit query and coin-forwarding costs. -/
@[reducible] def smIface (Key St St₂ Msg Coins RCoins C : Type)
    (stSort : SMSort := .st)
    (sampKey : ProbComp (Option Key) := pure none)
    (sampCoins : ProbComp (Option Coins) := pure none)
    (sampRCoins : ProbComp (Option RCoins) := pure none) :
    Iface (smSig Key St St₂ Msg Coins RCoins C)
      (unifSpec + SM.spec (SMSort.den Key St St₂ Msg Coins RCoins C stSort) Msg Coins C) where
  fwdU n :=
    query (spec := unifSpec + SM.spec (SMSort.den Key St St₂ Msg Coins RCoins C stSort) Msg Coins C)
      (.inl n)
  uCost := 1
  Tag := SMTag
  dom := fun
    | .tr => .prod .bool (.prod (.base .msg) (.opt (.base .coins)))
    | .ch => .prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .coins))))
    | .dl => .prod .bool (.base .ct)
    | .ij => .prod .bool (.base .ct)
    | .cr => .bool
  cod := fun
    | .tr => .opt (.base .ct)
    | .ch => .opt (.base .ct)
    | .dl => .opt (smRrTy Key St St₂ Msg Coins RCoins C)
    | .ij => .opt (smRrTy Key St St₂ Msg Coins RCoins C)
    | .cr => .opt (.base stSort)
  enc := fun
    | .tr, (p, m, r) => .inr (.inl (.inl (.inl (.inl (partyDec p, m, r)))))
    | .ch, (p, m₀, m₁, r) => .inr (.inl (.inl (.inl (.inr (partyDec p, m₀, m₁, r)))))
    | .dl, (q, c) => .inr (.inl (.inl (.inr (partyDec q, c))))
    | .ij, (q, c) => .inr (.inl (.inr (partyDec q, c)))
    | .cr, p => .inr (.inr (partyDec p))
  dec := fun
    | .tr, _, r => r
    | .ch, _, r => r
    | .dl, _, r => r.map smRrEnc
    | .ij, _, r => r.map smRrEnc
    | .cr, _, r => r
  qCost := fun _ => 1
  smp := smSamplers sampKey sampCoins sampRCoins

@[reducible] def smQ (Key St St₂ Msg Coins RCoins C : Type) :
    Ty (smSig Key St St₂ Msg Coins RCoins C) :=
  .sum
    (.sum
      (.sum
        (.sum
          (.prod .bool (.prod (.base .msg) (.opt (.base .coins))))
          (.prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .coins))))))
        (.prod .bool (.base .ct)))
      (.prod .bool (.base .ct)))
    .bool

@[reducible] def smR (Key St St₂ Msg Coins RCoins C : Type)
    (stSort : SMSort := .st) :
    Ty (smSig Key St St₂ Msg Coins RCoins C) :=
  .sum
    (.sum
      (.sum
        (.sum
          (.opt (.base .ct))
          (.opt (.base .ct)))
        (.opt (smRrTy Key St St₂ Msg Coins RCoins C)))
      (.opt (smRrTy Key St St₂ Msg Coins RCoins C)))
    (.opt (.base stSort))

/-- Source game codec for `SM.spec` at `codecCost = 6`. -/
@[reducible] def smCodec (Key St St₂ Msg Coins RCoins C : Type)
    (stSort : SMSort := .st) :
    GameCodec (smSig Key St St₂ Msg Coins RCoins C)
      (SM.spec (SMSort.den Key St St₂ Msg Coins RCoins C stSort) Msg Coins C) where
  Q := smQ Key St St₂ Msg Coins RCoins C
  R := smR Key St St₂ Msg Coins RCoins C stSort
  qenc := fun
    | .inl (.inl (.inl (.inl (P, m, r)))) =>
      .inl (.inl (.inl (.inl (partyEnc P, m, r))))
    | .inl (.inl (.inl (.inr (P, m₀, m₁, r)))) =>
      .inl (.inl (.inl (.inr (partyEnc P, m₀, m₁, r))))
    | .inl (.inl (.inr (Q, c))) =>
      .inl (.inl (.inr (partyEnc Q, c)))
    | .inl (.inr (Q, c)) =>
      .inl (.inr (partyEnc Q, c))
    | .inr P =>
      .inr (partyEnc P)
  rdec := fun
    | .inl (.inl (.inl (.inl _))), .inl (.inl (.inl (.inl r))) => r
    | .inl (.inl (.inl (.inl _))), _ => none
    | .inl (.inl (.inl (.inr _))), .inl (.inl (.inl (.inr r))) => r
    | .inl (.inl (.inl (.inr _))), _ => none
    | .inl (.inl (.inr _)), .inl (.inl (.inr r)) => r.map smRrDec
    | .inl (.inl (.inr _)), _ => none
    | .inl (.inr _), .inl (.inr r) => r.map smRrDec
    | .inl (.inr _), _ => none
    | .inr _, .inr r => r
    | .inr _, _ => none
  codecCost := 6

inductive SMTagDF where
  | tr | ch | dl | ij | cr | df
  deriving DecidableEq, Repr

/-- Target interface into `unifSpec + SM.specDF` extending `smIface` with `deliverForge`. -/
@[reducible] def smIfaceDF (Key St St₂ Msg Coins RCoins C : Type)
    (stSort : SMSort := .st)
    (sampKey : ProbComp (Option Key) := pure none)
    (sampCoins : ProbComp (Option Coins) := pure none)
    (sampRCoins : ProbComp (Option RCoins) := pure none) :
    Iface (smSig Key St St₂ Msg Coins RCoins C)
      (unifSpec + SM.specDF (SMSort.den Key St St₂ Msg Coins RCoins C stSort) Msg Coins C) where
  fwdU n :=
    query
      (spec := unifSpec + SM.specDF (SMSort.den Key St St₂ Msg Coins RCoins C stSort) Msg Coins C)
      (.inl n)
  uCost := 1
  Tag := SMTagDF
  dom := fun
    | .tr => .prod .bool (.prod (.base .msg) (.opt (.base .coins)))
    | .ch => .prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .coins))))
    | .dl => .prod .bool (.base .ct)
    | .ij => .prod .bool (.base .ct)
    | .cr => .bool
    | .df => .prod .bool (.prod (.base .ct) (.base .ct))
  cod := fun
    | .tr => .opt (.base .ct)
    | .ch => .opt (.base .ct)
    | .dl => .opt (smRrTy Key St St₂ Msg Coins RCoins C)
    | .ij => .opt (smRrTy Key St St₂ Msg Coins RCoins C)
    | .cr => .opt (.base stSort)
    | .df => .opt (smRrTy Key St St₂ Msg Coins RCoins C)
  enc := fun
    | .tr, (p, m, r) => .inr (.inl (.inl (.inl (.inl (.inl (partyDec p, m, r))))))
    | .ch, (p, m₀, m₁, r) => .inr (.inl (.inl (.inl (.inl (.inr (partyDec p, m₀, m₁, r))))))
    | .dl, (q, c) => .inr (.inl (.inl (.inl (.inr (partyDec q, c)))))
    | .ij, (q, c) => .inr (.inl (.inl (.inr (partyDec q, c))))
    | .cr, p => .inr (.inl (.inr (partyDec p)))
    | .df, (q, c, c') => .inr (.inr (partyDec q, c, c'))
  dec := fun
    | .tr, _, r => r
    | .ch, _, r => r
    | .dl, _, r => r.map smRrEnc
    | .ij, _, r => r.map smRrEnc
    | .cr, _, r => r
    | .df, _, r => r.map smRrEnc
  qCost := fun _ => 1
  smp := smSamplers sampKey sampCoins sampRCoins

@[reducible] def smQDF (Key St St₂ Msg Coins RCoins C : Type) :
    Ty (smSig Key St St₂ Msg Coins RCoins C) :=
  .sum (smQ Key St St₂ Msg Coins RCoins C) (.prod .bool (.prod (.base .ct) (.base .ct)))

@[reducible] def smRDF (Key St St₂ Msg Coins RCoins C : Type)
    (stSort : SMSort := .st) :
    Ty (smSig Key St St₂ Msg Coins RCoins C) :=
  .sum (smR Key St St₂ Msg Coins RCoins C stSort) (.opt (smRrTy Key St St₂ Msg Coins RCoins C))

/-- Source game codec for `SM.specDF` at `codecCost = 7`. -/
@[reducible] def smCodecDF (Key St St₂ Msg Coins RCoins C : Type)
    (stSort : SMSort := .st) :
    GameCodec (smSig Key St St₂ Msg Coins RCoins C)
      (SM.specDF (SMSort.den Key St St₂ Msg Coins RCoins C stSort) Msg Coins C) where
  Q := smQDF Key St St₂ Msg Coins RCoins C
  R := smRDF Key St St₂ Msg Coins RCoins C stSort
  qenc := fun
    | .inl q => .inl ((smCodec Key St St₂ Msg Coins RCoins C stSort).qenc q)
    | .inr (Q, c, c') => .inr (partyEnc Q, c, c')
  rdec := fun
    | .inl q, .inl r => (smCodec Key St St₂ Msg Coins RCoins C stSort).rdec q r
    | .inl (.inl (.inl (.inl (.inl _)))), .inr _ => none
    | .inl (.inl (.inl (.inl (.inr _)))), .inr _ => none
    | .inl (.inl (.inl (.inr _))), .inr _ => none
    | .inl (.inl (.inr _)), .inr _ => none
    | .inl (.inr _), .inr _ => none
    | .inr _, .inr r => r.map smRrDec
    | .inr _, .inl _ => none
  codecCost := 7

/-! ## `Pos` representation and `Expr` helpers -/

/-- `SM.Pos` encoded as `(sender, (epoch, idx))`. -/
@[reducible] def posTy {S' : Sig} : Ty S' := .prod .bool (.prod .nat .nat)

def orE
    {S' : Sig} {O' : Ops S'} {Γ} (a b : Expr O' Γ .bool) : Expr O' Γ .bool :=
  .ite a (.bool true) b

def boolEq
    {S' : Sig} {O' : Ops S'} {Γ} (a b : Expr O' Γ .bool) : Expr O' Γ .bool :=
  .ite a b (.not b)

def leN
    {S' : Sig} {O' : Ops S'} {Γ} (a b : Expr O' Γ .nat) : Expr O' Γ .bool :=
  .not (.lt b a)

def maxN
    {S' : Sig} {O' : Ops S'} {Γ} (a b : Expr O' Γ .nat) : Expr O' Γ .nat :=
  .letE (.pair a b)
    (.ite (leN (.fst .v0) (.snd .v0)) (.snd .v0) (.fst .v0))

def minN
    {S' : Sig} {O' : Ops S'} {Γ} (a b : Expr O' Γ .nat) : Expr O' Γ .nat :=
  .letE (.pair a b)
    (.ite (leN (.fst .v0) (.snd .v0)) (.fst .v0) (.snd .v0))

def isSomeE
    {S' : Sig} {O' : Ops S'} {Γ t} (e : Expr O' Γ (.opt t)) : Expr O' Γ .bool :=
  .caseOpt e (.bool false) (.bool true)

def otherE
    {S' : Sig} {O' : Ops S'} {Γ} (p : Expr O' Γ .bool) : Expr O' Γ .bool :=
  .not p

def sendsInE
    {S' : Sig} {O' : Ops S'} {Γ} (p : Expr O' Γ .bool) (t : Expr O' Γ .nat) :
    Expr O' Γ .bool :=
  .letE (.pair p t)
    (.ite (.fst .v0)
      (.eqN (.modK 2 (.snd .v0)) (.nat 0))
      (.eqN (.modK 2 (.snd .v0)) (.nat 1)))

def senderOfE
    {S' : Sig} {O' : Ops S'} {Γ} (t : Expr O' Γ .nat) : Expr O' Γ .bool :=
  .not (.eqN (.modK 2 t) (.nat 1))

def pGet
    {S' : Sig} {O' : Ops S'} {Γ t} (m : Expr O' Γ (.prod t t)) (p : Expr O' Γ .bool) :
    Expr O' Γ t :=
  .letE (.pair m p) (.ite (.snd .v0) (.snd (.fst .v0)) (.fst (.fst .v0)))

def pSet
    {S' : Sig} {O' : Ops S'} {Γ t} (m : Expr O' Γ (.prod t t)) (p : Expr O' Γ .bool)
    (v : Expr O' Γ t) : Expr O' Γ (.prod t t) :=
  .letE (.pair m (.pair p v))
    (.ite (.fst (.snd .v0))
      (.pair (.fst (.fst .v0)) (.snd (.snd .v0)))
      (.pair (.snd (.snd .v0)) (.snd (.fst .v0))))

def maxAccGet
    {S' : Sig} {O' : Ops S'} {Γ} (ma : Expr O' Γ (.prod (.tbl .nat) (.tbl .nat)))
    (p : Expr O' Γ .bool) (ep : Expr O' Γ .nat) : Expr O' Γ .nat :=
  .tget (pGet ma p) ep

def maxAccSet
    {S' : Sig} {O' : Ops S'} {Γ} (ma : Expr O' Γ (.prod (.tbl .nat) (.tbl .nat)))
    (p : Expr O' Γ .bool) (ep : Expr O' Γ .nat) (val : Expr O' Γ .nat) :
    Expr O' Γ (.prod (.tbl .nat) (.tbl .nat)) :=
  .letE (.pair ma (.pair p (.pair ep val)))
    (let ma0 : Expr O' _ (.prod (.tbl .nat) (.tbl .nat)) := .fst .v0
     let p0 : Expr O' _ .bool := .fst (.snd .v0)
     let ep0 : Expr O' _ .nat := .fst (.snd (.snd .v0))
     let val0 : Expr O' _ .nat := .snd (.snd (.snd .v0))
     pSet ma0 p0 (.tset (pGet ma0 p0) ep0 val0))

def posSender
    {S' : Sig} {O' : Ops S'} {Γ} (p : Expr O' Γ posTy) : Expr O' Γ .bool := .fst p
def posEpoch
    {S' : Sig} {O' : Ops S'} {Γ} (p : Expr O' Γ posTy) : Expr O' Γ .nat := .fst (.snd p)
def posIdx
    {S' : Sig} {O' : Ops S'} {Γ} (p : Expr O' Γ posTy) : Expr O' Γ .nat := .snd (.snd p)

def posEq
    {S' : Sig} {O' : Ops S'} {Γ} (p₁ p₂ : Expr O' Γ posTy) : Expr O' Γ .bool :=
  .letE (.pair p₁ p₂)
    (let a : Expr O' _ posTy := .fst .v0
     let b : Expr O' _ posTy := .snd .v0
     .and (boolEq (posSender a) (posSender b))
       (.and (.eqN (posEpoch a) (posEpoch b)) (.eqN (posIdx a) (posIdx b))))

def healedByE
    {S' : Sig} {O' : Ops S'} {Γ} (tL : Expr O' Γ (.opt .nat)) (Δ : ℕ)
    (t : Expr O' Γ .nat) : Expr O' Γ .bool :=
  .letE (.pair tL t)
    (.caseOpt (.fst .v0)
      (.bool true)
      (leN (.add .v0 (.nat Δ)) (.snd .v1)))

def maxOptE
    {S' : Sig} {O' : Ops S'} {Γ} (tL : Expr O' Γ (.opt .nat)) (t : Expr O' Γ .nat) :
    Expr O' Γ .nat :=
  .letE (.pair tL t)
    (.caseOpt (.fst .v0)
      (.snd .v0)
      (maxN .v0 (.snd .v1)))

end CryptoGames.SM

set_option autoImplicit false

namespace CryptoGames.SM

open ReductionDsl OracleSpec OracleComp

@[simp] theorem partyDec_partyEnc (P : Party) : partyDec (partyEnc P) = P := by
  cases P <;> rfl

@[simp] theorem partyEnc_partyDec (b : Bool) : partyEnc (partyDec b) = b := by
  cases b <;> rfl

@[simp] theorem partyEnc_other (P : Party) : partyEnc P.other = !partyEnc P := by
  cases P <;> rfl

@[simp] theorem smRrDec_smRrEnc {Msg : Type} (r : RecvResult Msg) :
    smRrDec (smRrEnc r) = r := by
  cases r <;> rfl

def posEnc (p : Pos) : Bool × ℕ × ℕ := (partyEnc p.sender, p.epoch, p.idx)

def posDec (v : Bool × ℕ × ℕ) : Pos := ⟨partyDec v.1, v.2.1, v.2.2⟩

@[simp] theorem posDec_posEnc (p : Pos) : posDec (posEnc p) = p := by
  cases p; simp [posEnc, posDec]

@[simp] theorem posEnc_posDec (v : Bool × ℕ × ℕ) : posEnc (posDec v) = v := by
  rcases v with ⟨b, t, i⟩; simp [posEnc, posDec]

def receiverOfE
    {S' : Sig} {O' : Ops S'} {Γ} (t : Expr O' Γ .nat) : Expr O' Γ .bool :=
  .eqN (.modK 2 t) (.nat 1)

def ltOptE
    {S' : Sig} {O' : Ops S'} {Γ} (tL : Expr O' Γ (.opt .nat)) (t : Expr O' Γ .nat) :
    Expr O' Γ .bool :=
  .letE (.pair tL t)
    (.caseOpt (.fst .v0)
      (.bool true)
      (.lt .v0 (.snd .v1)))

end CryptoGames.SM
