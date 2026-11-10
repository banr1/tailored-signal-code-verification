/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost
public import Computational.Proofs.ReductionDsl.Fig8Atomic
public import Computational.Proofs.SpqrV1Sync.TopStateTight

/-!
# Base Combinators, Mirror Bookkeeping, and `GhostChain` Helpers for `simFig8`

Defines `ReductionDsl` operator wrappers, game-mirror bookkeeping expressions, bounded
`GhostChain` and `toGhost` combinators, and the zero-overhead lift from `atomicFig8Ops` to
`atomicSessionOps`, with evaluation, cost, and description-bit bounds.
-/

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp
open ReductionDsl (Sig Ty Var Env Ops Iface Expr Comp bits bits_mono
  atomicSig atomicFig8Ops atomicSessionOps B U32 BV256 PK IdKey PlainT PtT GhostStT
  AtomicPureOp AtomicSymOp AtomicGroupOp AtomicPtEncOp AtomicPtDecOp
  AtomicCurveCheckOp AtomicSpqrKemOp atomicPtEncOps atomicPtDecOps atomicCurveCheckOps
  partyToBool boolToParty
  fig8CtT fig8CtV fig8CtOfV fig8StT fig8StV fig8StOfV
  fsSendStT fsSendStV fsSendStOfV fsRecvStT fsRecvStV fsRecvStOfV ckaStV ckaStOfV
  drSenderChainT drRecvChainT ghostJoinEval)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.Ratchet (RootKey keyToBytesVec32)
open CryptoGames.Ratchet.LibsignalInst (dummyKey)
open CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C GhostChain SimState pushChain
  inReceiveOnlyEpoch toGhost)
open CryptoGames.Ratchet.LibsignalSimC (Kept LibsignalToModularSchemeSimState)
open CryptoGames.SM (Pos Record GameState maxOpt noBobSendInEpoch0 noAliceCorrWhileAliceBelowEpoch10
  partyEnc partyDec partyEnc_other partyEnc_beq posTy posEnc posDec posDec_posEnc
  posSender posEpoch posIdx posEq
  orE boolEq maxN minN isSomeE otherE sendsInE pGet pSet maxAccGet maxAccSet
  healedByE maxOptE ite_eval orE_eval boolEq_eval maxN_eval minN_eval isSomeE_eval
  otherE_eval sendsInE_eval pGet_eval pSet_eval posEq_eval healedByE_eval maxOptE_eval
  find?_map_eq any_map_eq foldr_filter_map any_beq_eq_contains)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey KeyPair
  GhostState currentVersion)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.E2E (Bytes toU8 ofU8 u8Vec paramsV1)
open Computational.Proofs.GameHop.CompDedup
  (CountLe countLe_length_le dedupPrepend dedupPrepend_cons foldr_dedup_map_eq afterCorrDedup)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge (sessPureOp sessSymOp
  sessGroupOp sessPtEncOp sessPtDecOp sessCurveOp sessSpqrKemOp)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost
  (atomicSortDescBits atomicTyDescBits varIdx atomicPureOpDescBits atomicSymOpDescBits
   atomicSessionOpDescBits atomicExprDescBits atomicCompDescBits)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost
  (simRecT simMirT ghostChainT simBaseT keptT snapT sentEntryT simFullT
   simRecEnc simRecDec simMirEnc simMirDec ghostChainEnc ghostChainDec
   honestPairEnc honestPairDec simBaseEnc simBaseDec keptEnc keptDec
   snapEnc snapDec sentEntryEnc sentEntryDec simFullEnc simFullDec
   fig8StTruncSk)

namespace Computational.Proofs.Game.PromotedCostedReds.SimFig8State

theorem bits_zero : bits 0 = 1 := by unfold bits; simp

theorem bits_eq_of_bounds {n k : ℕ} (hk : 1 ≤ k) (h0 : n ≠ 0)
    (hlo : 2 ^ (k - 1) ≤ n) (hhi : n < 2 ^ k) : bits n = k := by
  unfold bits
  have h1 : k - 1 ≤ Nat.log 2 n := (Nat.le_log_iff_pow_le (by omega) h0).mpr hlo
  have h2 : Nat.log 2 n < k := Nat.log_lt_of_lt_pow h0 hhi
  omega

theorem bits_le_of_lt_pow {n k : ℕ} (hk : 1 ≤ k) (hhi : n < 2 ^ k) : bits n ≤ k := by
  by_cases h0 : n = 0
  · subst h0
    have hb0 : bits 0 = 1 := bits_zero
    omega
  · unfold bits
    have h2 : Nat.log 2 n < k := Nat.log_lt_of_lt_pow h0 hhi
    omega

section SessionIrreducibleOps

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
  {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
  {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

/-- Wrapper around `sessPureOp` keeping `Ops.sum` structure opaque to `simp`. -/
def sOpPure {Γ : List (Ty ASig)} (o : AtomicPureOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) : Expr AOps Γ (o.cod ℓ Pt) :=
  sessPureOp o a

def sOpPtEnc {Γ : List (Ty ASig)} (o : AtomicPtEncOp)
    (a : Expr AOps Γ ((atomicPtEncOps ℓ encT).dom o)) :
    Expr AOps Γ ((atomicPtEncOps ℓ encT).cod o) :=
  sessPtEncOp o a

def sOpSym {Γ : List (Ty ASig)} (o : AtomicSymOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) : Expr AOps Γ (o.cod ℓ Pt) :=
  sessSymOp o a

def sOpGrp {Γ : List (Ty ASig)} (o : AtomicGroupOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) : Expr AOps Γ (o.cod ℓ Pt) :=
  sessGroupOp o a

def sOpPtDec {Γ : List (Ty ASig)} (o : AtomicPtDecOp)
    (a : Expr AOps Γ ((atomicPtDecOps ℓ decT).dom o)) :
    Expr AOps Γ ((atomicPtDecOps ℓ decT).cod o) :=
  sessPtDecOp o a

def sOpCurve {Γ : List (Ty ASig)} (o : AtomicCurveCheckOp)
    (a : Expr AOps Γ ((atomicCurveCheckOps ℓ decT encT).dom o)) :
    Expr AOps Γ ((atomicCurveCheckOps ℓ decT encT).cod o) :=
  sessCurveOp o a

def sOpSpqr {Γ : List (Ty ASig)} (o : AtomicSpqrKemOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) : Expr AOps Γ (o.cod ℓ Pt) :=
  sessSpqrKemOp o a

@[simp] theorem eval_sOpPure {Γ : List (Ty ASig)} (o : AtomicPureOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) (ρ : Env Γ) :
    (sOpPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).eval ρ = o.eval ℓ Pt (a.eval ρ) := rfl

@[simp] theorem cost_sOpPure {Γ : List (Ty ASig)} (o : AtomicPureOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) :
    (sOpPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).cost = a.cost + o.cost ℓ := rfl

@[simp] theorem descBits_sOpPure {Γ : List (Ty ASig)} (o : AtomicPureOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) :
    atomicExprDescBits atomicSessionOpDescBits
      (sOpPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) o a) =
      atomicPureOpDescBits o + 4 + atomicExprDescBits atomicSessionOpDescBits a + 6 := rfl

@[simp] theorem eval_sOpPtEnc {Γ : List (Ty ASig)}
    (a : Expr AOps Γ (PtT (ℓ := ℓ) (Pt := Pt))) (ρ : Env Γ) :
    (sOpPtEnc (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) .ptEncPk a).eval ρ = encT (a.eval ρ) := rfl

@[simp] theorem cost_sOpPtEnc {Γ : List (Ty ASig)}
    (a : Expr AOps Γ (PtT (ℓ := ℓ) (Pt := Pt))) :
    (sOpPtEnc (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) .ptEncPk a).cost = a.cost + 4 := rfl

@[simp] theorem descBits_sOpPtEnc {Γ : List (Ty ASig)} (o : AtomicPtEncOp)
    (a : Expr AOps Γ ((atomicPtEncOps ℓ encT).dom o)) :
    atomicExprDescBits atomicSessionOpDescBits
      (sOpPtEnc (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) o a) =
      13 + atomicExprDescBits atomicSessionOpDescBits a + 6 := rfl

@[simp] theorem eval_sOpSym {Γ : List (Ty ASig)} (o : AtomicSymOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) (ρ : Env Γ) :
    (sOpSym (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).eval ρ = o.eval ℓ Pt C (a.eval ρ) := rfl

@[simp] theorem cost_sOpSym {Γ : List (Ty ASig)} (o : AtomicSymOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) :
    (sOpSym (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).cost = a.cost + o.cost ℓ := rfl

@[simp] theorem descBits_sOpSym {Γ : List (Ty ASig)} (o : AtomicSymOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) :
    atomicExprDescBits atomicSessionOpDescBits
      (sOpSym (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) o a) =
      atomicSymOpDescBits o + 5 + atomicExprDescBits atomicSessionOpDescBits a + 6 := rfl

@[simp] theorem eval_sOpGrp {Γ : List (Ty ASig)} (o : AtomicGroupOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) (ρ : Env Γ) :
    (sOpGrp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).eval ρ = o.eval ℓ Pt C Dh encPt lam (a.eval ρ) := rfl

@[simp] theorem cost_sOpGrp {Γ : List (Ty ASig)} (o : AtomicGroupOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) :
    (sOpGrp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).cost = a.cost + o.cost := rfl

@[simp] theorem descBits_sOpGrp {Γ : List (Ty ASig)} (o : AtomicGroupOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) :
    atomicExprDescBits atomicSessionOpDescBits
      (sOpGrp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) o a) =
      11 + atomicExprDescBits atomicSessionOpDescBits a + 6 := rfl

@[simp] theorem eval_sOpPtDec {Γ : List (Ty ASig)}
    (a : Expr AOps Γ (PK (ℓ := ℓ) (Pt := Pt))) (ρ : Env Γ) :
    (sOpPtDec (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) .ptDecPk a).eval ρ = decT (a.eval ρ) := rfl

@[simp] theorem cost_sOpPtDec {Γ : List (Ty ASig)}
    (a : Expr AOps Γ (PK (ℓ := ℓ) (Pt := Pt))) :
    (sOpPtDec (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) .ptDecPk a).cost = a.cost + 8 := rfl

@[simp] theorem descBits_sOpPtDec {Γ : List (Ty ASig)} (o : AtomicPtDecOp)
    (a : Expr AOps Γ ((atomicPtDecOps ℓ decT).dom o)) :
    atomicExprDescBits atomicSessionOpDescBits
      (sOpPtDec (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) o a) =
      11 + atomicExprDescBits atomicSessionOpDescBits a + 6 := rfl

@[simp] theorem eval_sOpCurve {Γ : List (Ty ASig)} (o : AtomicCurveCheckOp)
    (a : Expr AOps Γ ((atomicCurveCheckOps ℓ decT encT).dom o)) (ρ : Env Γ) :
    (sOpCurve (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).eval ρ =
      (atomicCurveCheckOps ℓ decT encT).eval o (a.eval ρ) := rfl

@[simp] theorem cost_sOpCurve {Γ : List (Ty ASig)} (o : AtomicCurveCheckOp)
    (a : Expr AOps Γ ((atomicCurveCheckOps ℓ decT encT).dom o)) :
    (sOpCurve (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).cost = a.cost + (atomicCurveCheckOps ℓ decT encT).cost o := rfl

@[simp] theorem descBits_sOpCurve {Γ : List (Ty ASig)} (o : AtomicCurveCheckOp)
    (a : Expr AOps Γ ((atomicCurveCheckOps ℓ decT encT).dom o)) :
    atomicExprDescBits atomicSessionOpDescBits
      (sOpCurve (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) o a) =
      11 + atomicExprDescBits atomicSessionOpDescBits a + 6 := rfl

@[simp] theorem eval_sOpSpqr {Γ : List (Ty ASig)} (o : AtomicSpqrKemOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) (ρ : Env Γ) :
    (sOpSpqr (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).eval ρ = o.eval ℓ Pt C K (a.eval ρ) := rfl

@[simp] theorem cost_sOpSpqr {Γ : List (Ty ASig)} (o : AtomicSpqrKemOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) :
    (sOpSpqr (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).cost = a.cost + o.cost := rfl

@[simp] theorem descBits_sOpSpqr {Γ : List (Ty ASig)} (o : AtomicSpqrKemOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) :
    atomicExprDescBits atomicSessionOpDescBits
      (sOpSpqr (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) o a) =
      9 + atomicExprDescBits atomicSessionOpDescBits a + 6 := rfl

end SessionIrreducibleOps

/-! ## Mirror bookkeeping -/

section MirrorBookkeeping

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
  {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
  {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

def eLet {O' : Ops ASig} {Γ : List (Ty ASig)} {a b : Ty ASig}
    (e : Expr O' Γ a) (body : Expr O' (a :: Γ) b) : Expr O' Γ b :=
  .letE e body

omit [DecidableEq Pt] [Zero Pt] in
@[simp] theorem eval_eLet {O' : Ops ASig} {Γ : List (Ty ASig)} {a b : Ty ASig}
    (e : Expr O' Γ a) (body : Expr O' (a :: Γ) b) (ρ : Env Γ) :
    (eLet e body).eval ρ = body.eval (.cons (e.eval ρ) ρ) := rfl

omit [DecidableEq Pt] [Zero Pt] in
@[simp] theorem cost_eLet {O' : Ops ASig} {Γ : List (Ty ASig)} {a b : Ty ASig}
    (e : Expr O' Γ a) (body : Expr O' (a :: Γ) b) :
    (eLet e body).cost = e.cost + body.cost + 1 := rfl

omit [DecidableEq Pt] [Zero Pt] in
@[simp] theorem descBits_eLet {O' : Ops ASig} (opB : O'.Op → ℕ)
    {Γ : List (Ty ASig)} {a b : Ty ASig}
    (e : Expr O' Γ a) (body : Expr O' (a :: Γ) b) :
    atomicExprDescBits opB (eLet e body) =
      atomicExprDescBits opB e + atomicExprDescBits opB body + 6 := rfl

def eMapOpt {O' : Ops ASig} {Γ : List (Ty ASig)} {a b : Ty ASig}
    (e : Expr O' Γ (.opt a)) (f : Expr O' (a :: Γ) b) : Expr O' Γ (.opt b) :=
  .caseOpt e .none (.some f)

omit [DecidableEq Pt] [Zero Pt] in
@[simp] theorem eval_eMapOpt {O' : Ops ASig} {Γ : List (Ty ASig)} {a b : Ty ASig}
    (e : Expr O' Γ (.opt a)) (f : Expr O' (a :: Γ) b) (ρ : Env Γ) :
    (eMapOpt e f).eval ρ = (e.eval ρ).map (fun x => f.eval (.cons x ρ)) := by
  simp only [eMapOpt, Expr.eval]
  cases e.eval ρ <;> rfl

omit [DecidableEq Pt] [Zero Pt] in
@[simp] theorem cost_eMapOpt {O' : Ops ASig} {Γ : List (Ty ASig)} {a b : Ty ASig}
    (e : Expr O' Γ (.opt a)) (f : Expr O' (a :: Γ) b) :
    (eMapOpt e f).cost = e.cost + (f.cost + 1) + 1 := by
  simp [eMapOpt, Expr.cost]

omit [DecidableEq Pt] [Zero Pt] in
@[simp] theorem descBits_eMapOpt {O' : Ops ASig} (opB : O'.Op → ℕ)
    {Γ : List (Ty ASig)} {a b : Ty ASig}
    (e : Expr O' Γ (.opt a)) (f : Expr O' (a :: Γ) b) :
    atomicExprDescBits opB (eMapOpt e f) =
      atomicExprDescBits opB e + (atomicTyDescBits b + 6) +
        (atomicExprDescBits opB f + 6) + 6 := rfl

def srecPos {O' : Ops ASig} {Γ} (r : Expr O' Γ (simRecT ℓ Pt)) : Expr O' Γ posTy := .fst r
def srecMsg {O' : Ops ASig} {Γ} (r : Expr O' Γ (simRecT ℓ Pt)) : Expr O' Γ PlainT := .fst (.snd r)
def srecCt {O' : Ops ASig} {Γ} (r : Expr O' Γ (simRecT ℓ Pt)) : Expr O' Γ (B 32) := .snd (.snd r)

def mB {O' : Ops ASig} {Γ} (s : Expr O' Γ (simMirT ℓ Pt)) : Expr O' Γ .bool := .fst s
def mWin {O' : Ops ASig} {Γ} (s : Expr O' Γ (simMirT ℓ Pt)) : Expr O' Γ .bool := .fst (.snd s)
def mEpoch {O' : Ops ASig} {Γ} (s : Expr O' Γ (simMirT ℓ Pt)) : Expr O' Γ (.prod .nat .nat) :=
  .fst (.snd (.snd s))
def mIdx {O' : Ops ASig} {Γ} (s : Expr O' Γ (simMirT ℓ Pt)) : Expr O' Γ (.prod .nat .nat) :=
  .fst (.snd (.snd (.snd s)))
def mTL {O' : Ops ASig} {Γ} (s : Expr O' Γ (simMirT ℓ Pt)) : Expr O' Γ (.opt .nat) :=
  .fst (.snd (.snd (.snd (.snd s))))
def mTrans {O' : Ops ASig} {Γ} (s : Expr O' Γ (simMirT ℓ Pt)) :
    Expr O' Γ (.list (simRecT ℓ Pt)) :=
  .fst (.snd (.snd (.snd (.snd (.snd s)))))
def mChall {O' : Ops ASig} {Γ} (s : Expr O' Γ (simMirT ℓ Pt)) : Expr O' Γ (.list posTy) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd s))))))
def mComp {O' : Ops ASig} {Γ} (s : Expr O' Γ (simMirT ℓ Pt)) : Expr O' Γ (.list posTy) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd s)))))))
def mMaxAcc {O' : Ops ASig} {Γ} (s : Expr O' Γ (simMirT ℓ Pt)) :
    Expr O' Γ (.prod (.tbl .nat) (.tbl .nat)) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd s))))))))
def mLeaks {O' : Ops ASig} {Γ} (s : Expr O' Γ (simMirT ℓ Pt)) : Expr O' Γ (.list .nat) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd s)))))))))
def mCorrs {O' : Ops ASig} {Γ} (s : Expr O' Γ (simMirT ℓ Pt)) :
    Expr O' Γ (.list (.prod .bool .nat)) :=
  .snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd s)))))))))

def mMk {O' : Ops ASig} {Γ}
    (b win : Expr O' Γ .bool)
    (ep idx : Expr O' Γ (.prod .nat .nat))
    (tL : Expr O' Γ (.opt .nat))
    (trs : Expr O' Γ (.list (simRecT ℓ Pt)))
    (chall comp : Expr O' Γ (.list posTy))
    (ma : Expr O' Γ (.prod (.tbl .nat) (.tbl .nat)))
    (leaks : Expr O' Γ (.list .nat))
    (corrs : Expr O' Γ (.list (.prod .bool .nat))) : Expr O' Γ (simMirT ℓ Pt) :=
  .pair b (.pair win (.pair ep (.pair idx (.pair tL (.pair trs
    (.pair chall (.pair comp (.pair ma (.pair leaks corrs)))))))))

def mSetWin {O' : Ops ASig} {Γ} (s : Expr O' Γ (simMirT ℓ Pt)) (w : Expr O' Γ .bool) :
    Expr O' Γ (simMirT ℓ Pt) :=
  eLet (.pair s w)
    (mMk (mB (.fst .v0)) (.snd .v0) (mEpoch (.fst .v0)) (mIdx (.fst .v0))
      (mTL (.fst .v0)) (mTrans (.fst .v0)) (mChall (.fst .v0)) (mComp (.fst .v0))
      (mMaxAcc (.fst .v0)) (mLeaks (.fst .v0)) (mCorrs (.fst .v0)))

def mSafeChE {O' : Ops ASig} {Γ} (s : Expr O' Γ (simMirT ℓ Pt)) (p : Expr O' Γ .bool) :
    Expr O' Γ .bool :=
  healedByE (mTL s) 3 (pGet (mEpoch s) p)

def mSafeInjE {O' : Ops ASig} {Γ} (s : Expr O' Γ (simMirT ℓ Pt)) : Expr O' Γ .bool :=
  eLet s (healedByE (mTL .v0) 3 (minN (.fst (mEpoch .v0)) (.snd (mEpoch .v0))))

def mLeakE {O' : Ops ASig} {Γ} (s : Expr O' Γ (simMirT ℓ Pt)) (l : Expr O' Γ .nat) :
    Expr O' Γ (simMirT ℓ Pt) :=
  eLet (.pair s l)
    (eLet (maxOptE (mTL (.fst .v0)) (.snd .v0))
      (mMk (mB (.fst .v1)) (mWin (.fst .v1)) (mEpoch (.fst .v1)) (mIdx (.fst .v1))
        (.some .v0) (mTrans (.fst .v1)) (mChall (.fst .v1))
        (mComp (.fst .v1)) (mMaxAcc (.fst .v1)) (.cons .v0 (mLeaks (.fst .v1)))
        (mCorrs (.fst .v1))))

def mEpMgmtE {O' : Ops ASig} {Γ} (qep : ℕ) (s : Expr O' Γ (simMirT ℓ Pt))
    (p bad : Expr O' Γ .bool) : Expr O' Γ (.opt (simMirT ℓ Pt)) :=
  eLet (.pair s (.pair p bad))
    (let s0 : Expr O' _ (simMirT ℓ Pt) := .fst .v0
     let p0 : Expr O' _ .bool := .fst (.snd .v0)
     let bad0 : Expr O' _ .bool := .snd (.snd .v0)
     let epNext : Expr O' _ .nat := .add (pGet (mEpoch s0) p0) (.nat 1)
     .ite (sendsInE p0 epNext)
       (.ite (.lt (.nat qep) epNext)
         .none
         (eLet (.ite (.and bad0 (.not (mSafeChE s0 p0))) (mLeakE s0 epNext) s0)
           (.some (mMk (mB .v0) (mWin .v0)
             (pSet (mEpoch .v0) (.fst (.snd .v1))
               (.add (pGet (mEpoch .v0) (.fst (.snd .v1))) (.nat 1)))
             (pSet (mIdx .v0) (.fst (.snd .v1)) (.nat 0))
             (mTL .v0) (mTrans .v0) (mChall .v0) (mComp .v0)
             (mMaxAcc .v0) (mLeaks .v0) (mCorrs .v0)))))
       (.ite (.lt (.nat qep) (pGet (mEpoch s0) p0)) .none (.some s0)))

def mRecordE {O' : Ops ASig} {Γ} (s : Expr O' Γ (simMirT ℓ Pt)) (p : Expr O' Γ .bool)
    (r : Expr O' Γ (simRecT ℓ Pt)) (isChall : Expr O' Γ .bool) : Expr O' Γ (simMirT ℓ Pt) :=
  eLet (.pair s (.pair p (.pair r isChall)))
    (let s0 : Expr O' _ (simMirT ℓ Pt) := .fst .v0
     let p0 : Expr O' _ .bool := .fst (.snd .v0)
     let r0 : Expr O' _ (simRecT ℓ Pt) := .fst (.snd (.snd .v0))
     let ch0 : Expr O' _ .bool := .snd (.snd (.snd .v0))
     mMk (mB s0) (mWin s0) (mEpoch s0)
       (pSet (mIdx s0) p0 (posIdx (srecPos r0)))
       (mTL s0)
       (.cons r0 (mTrans s0))
       (.ite ch0 (.cons (srecPos r0) (mChall s0)) (mChall s0))
       (.ite (mSafeChE s0 p0) (mComp s0) (.cons (srecPos r0) (mComp s0)))
       (mMaxAcc s0) (mLeaks s0) (mCorrs s0))

def mInTransitE {Γ} (Lq : ℕ) (s : Expr AOps Γ (simMirT ℓ Pt))
    (qParty : Expr AOps Γ .bool) (w : Expr AOps Γ (B 32)) : Expr AOps Γ (.opt (simRecT ℓ Pt)) :=
  eLet (.pair s (.pair qParty w))
    (.findB Lq (mTrans (.fst .v0))
      (.and (boolEq (posSender (srecPos .v0)) (.fst (.snd .v1)))
        (sOpPure (.bytesEq 32 32) (.pair (srecCt .v0) (.snd (.snd .v1))))))

def mDeleteE {O' : Ops ASig} {Γ} (Lq : ℕ) (s : Expr O' Γ (simMirT ℓ Pt))
    (pos : Expr O' Γ posTy) : Expr O' Γ (simMirT ℓ Pt) :=
  eLet (.pair s pos)
    (let s0 : Expr O' _ (simMirT ℓ Pt) := .fst .v0
     let trs' := Expr.foldrB Lq (mTrans s0) .nil
       (.ite (posEq (srecPos .v0) (.snd .v2)) .v1 (.cons .v0 .v1))
     let ch' := Expr.foldrB Lq (mChall s0) .nil
       (.ite (posEq .v0 (.snd .v2)) .v1 (.cons .v0 .v1))
     let cp' := Expr.foldrB Lq (mComp s0) .nil
       (.ite (posEq .v0 (.snd .v2)) .v1 (.cons .v0 .v1))
     mMk (mB s0) (mWin s0) (mEpoch s0) (mIdx s0) (mTL s0) trs' ch' cp'
       (mMaxAcc s0) (mLeaks s0) (mCorrs s0))

def mAcceptE {O' : Ops ASig} {Γ} (Lq : ℕ) (s : Expr O' Γ (simMirT ℓ Pt))
    (p : Expr O' Γ .bool) (pos : Expr O' Γ posTy) : Expr O' Γ (simMirT ℓ Pt) :=
  eLet (.pair (mDeleteE Lq s pos) (.pair p pos))
    (let s0 : Expr O' _ (simMirT ℓ Pt) := .fst .v0
     let p0 : Expr O' _ .bool := .fst (.snd .v0)
     let pos0 : Expr O' _ posTy := .snd (.snd .v0)
     let ep := posEpoch pos0
     let idx := posIdx pos0
     mMk (mB s0) (mWin s0)
       (pSet (mEpoch s0) p0 (maxN (pGet (mEpoch s0) p0) ep))
       (mIdx s0) (mTL s0) (mTrans s0) (mChall s0) (mComp s0)
       (maxAccSet (mMaxAcc s0) p0 ep (maxN (maxAccGet (mMaxAcc s0) p0 ep) idx))
       (mLeaks s0) (mCorrs s0))

def mCompContainsE {O' : Ops ASig} {Γ} (Lq : ℕ) (s : Expr O' Γ (simMirT ℓ Pt))
    (pos : Expr O' Γ posTy) : Expr O' Γ .bool :=
  eLet (.pair s pos) (.anyB Lq (mComp (.fst .v0)) (posEq .v0 (.snd .v1)))

def mChallContainsE {O' : Ops ASig} {Γ} (Lq : ℕ) (s : Expr O' Γ (simMirT ℓ Pt))
    (pos : Expr O' Γ posTy) : Expr O' Γ .bool :=
  eLet (.pair s pos) (.anyB Lq (mChall (.fst .v0)) (posEq .v0 (.snd .v1)))

def mTrivialE {O' : Ops ASig} {Γ} (Lq : ℕ) (s : Expr O' Γ (simMirT ℓ Pt))
    (pos : Expr O' Γ posTy) : Expr O' Γ .bool :=
  eLet (.pair s pos)
    (let s0 : Expr O' _ (simMirT ℓ Pt) := .fst .v0
     let p0 : Expr O' _ posTy := .snd .v0
     orE (mCompContainsE Lq s0 p0)
       (.and (.not (.anyB Lq (mTrans s0) (posEq (srecPos .v0) (.snd .v1))))
         (.not (healedByE (mTL s0) 3 (posEpoch p0)))))

def mCorrAllowedE {O' : Ops ASig} {Γ} (Lq : ℕ) (s : Expr O' Γ (simMirT ℓ Pt))
    (p : Expr O' Γ .bool) : Expr O' Γ .bool :=
  eLet (.pair s p)
    (let s0 : Expr O' _ (simMirT ℓ Pt) := .fst .v0
     .and
       (.not (.anyB Lq (mChall s0) (boolEq (posSender .v0) (otherE (.snd .v1)))))
       (.not (.anyB Lq (mTrans s0)
         (.and (boolEq (posSender (srecPos .v0)) (otherE (.snd .v1)))
           (.not (mCompContainsE Lq (.fst .v1) (srecPos .v0)))))))

def mAfterCorrE {O' : Ops ASig} {Γ} (Lq : ℕ) (s : Expr O' Γ (simMirT ℓ Pt))
    (p : Expr O' Γ .bool) : Expr O' Γ (simMirT ℓ Pt) :=
  eLet (.pair s p)
    (let s0 : Expr O' _ (simMirT ℓ Pt) := .fst .v0
     let p0 : Expr O' _ .bool := .snd .v0
     let comp' := Expr.foldrB Lq (mTrans s0) (mComp s0)
       (.ite
         (.and (boolEq (posSender (srecPos .v0)) (otherE (.snd .v2)))
           (.not (.anyB Lq .v1 (posEq .v0 (srecPos .v1)))))
         (.cons (srecPos .v0) .v1)
         .v1)
     let s1 := mMk (mB s0) (mWin s0) (mEpoch s0) (mIdx s0) (mTL s0)
       (mTrans s0) (mChall s0) comp' (mMaxAcc s0) (mLeaks s0) (mCorrs s0)
     let s2 := mLeakE s1 (maxN (.fst (mEpoch s0)) (.snd (mEpoch s0)))
     mMk (mB s2) (mWin s2) (mEpoch s2) (mIdx s2) (mTL s2)
       (mTrans s2) (mChall s2) (mComp s2) (mMaxAcc s2) (mLeaks s2)
       (.cons (.pair p0 (pGet (mEpoch s0) p0)) (mCorrs s2)))

/-- Pair of `(epoch → idx → Bool)` lookup tables indexing `Pos` membership in `O(1)` DSL cost. -/
abbrev compTblTy : Ty ASig :=
  .prod (.tbl (.tbl .bool)) (.tbl (.tbl .bool))

def compTblEmptyE {O' : Ops ASig} {Γ} : Expr O' Γ (compTblTy (ℓ := ℓ) (Pt := Pt)) :=
  .pair (.tconst (.tconst (.bool false))) (.tconst (.tconst (.bool false)))

def compTblInsertE {O' : Ops ASig} {Γ}
    (m : Expr O' Γ (compTblTy (ℓ := ℓ) (Pt := Pt))) (pos : Expr O' Γ posTy) :
    Expr O' Γ (compTblTy (ℓ := ℓ) (Pt := Pt)) :=
  eLet (.pair m pos)
    (let m0 : Expr O' _ (compTblTy (ℓ := ℓ) (Pt := Pt)) := .fst .v0
     let pos0 : Expr O' _ posTy := .snd .v0
     let sub := pGet m0 (posSender pos0)
     let row := Expr.tget sub (posEpoch pos0)
     pSet m0 (posSender pos0)
       (.tset sub (posEpoch pos0) (.tset row (posIdx pos0) (.bool true))))

def compTblGetE {O' : Ops ASig} {Γ}
    (m : Expr O' Γ (compTblTy (ℓ := ℓ) (Pt := Pt))) (pos : Expr O' Γ posTy) :
    Expr O' Γ .bool :=
  eLet (.pair m pos)
    (let m0 : Expr O' _ (compTblTy (ℓ := ℓ) (Pt := Pt)) := .fst .v0
     let pos0 : Expr O' _ posTy := .snd .v0
     .tget (.tget (pGet m0 (posSender pos0)) (posEpoch pos0)) (posIdx pos0))

def compTblOfListE {O' : Ops ASig} {Γ} (Lq : ℕ) (xs : Expr O' Γ (.list posTy)) :
    Expr O' Γ (compTblTy (ℓ := ℓ) (Pt := Pt)) :=
  .foldrB Lq xs compTblEmptyE (compTblInsertE .v1 .v0)

/-- `O(Lq)`-cost table-backed equivalent of `mCorrAllowedE`. -/
def mCorrAllowedFastE {O' : Ops ASig} {Γ} (Lq : ℕ) (s : Expr O' Γ (simMirT ℓ Pt))
    (p : Expr O' Γ .bool) : Expr O' Γ .bool :=
  eLet (.pair s p)
    (let s0 : Expr O' _ (simMirT ℓ Pt) := .fst .v0
     eLet (compTblOfListE Lq (mComp s0))
       (.and
         (.not (.anyB Lq (mChall (.fst .v1))
           (boolEq (posSender .v0) (otherE (.snd .v2)))))
         (.not (.anyB Lq (mTrans (.fst .v1))
           (.and (boolEq (posSender (srecPos .v0)) (otherE (.snd .v2)))
             (.not (compTblGetE .v1 (srecPos .v0))))))))

/-- `O(Lq)`-cost table-backed equivalent of `mAfterCorrE`. -/
def mAfterCorrFastE {O' : Ops ASig} {Γ} (Lq : ℕ) (s : Expr O' Γ (simMirT ℓ Pt))
    (p : Expr O' Γ .bool) : Expr O' Γ (simMirT ℓ Pt) :=
  eLet (.pair s p)
    (let s0 : Expr O' _ (simMirT ℓ Pt) := .fst .v0
     let initAcc : Expr O' _ (.prod (.list posTy) (compTblTy (ℓ := ℓ) (Pt := Pt))) :=
       .pair (mComp s0) (compTblOfListE Lq (mComp s0))
     eLet
       (.fst (.foldrB Lq (mTrans s0) initAcc
         (.ite
           (.and (boolEq (posSender (srecPos .v0)) (otherE (.snd .v2)))
             (.not (compTblGetE (.snd .v1) (srecPos .v0))))
           (.pair (.cons (srecPos .v0) (.fst .v1)) (compTblInsertE (.snd .v1) (srecPos .v0)))
           .v1)))
       (let s0' : Expr O' _ (simMirT ℓ Pt) := .fst .v1
        let p0' : Expr O' _ .bool := .snd .v1
        let s1 : Expr O' _ (simMirT ℓ Pt) :=
          mMk (mB s0') (mWin s0') (mEpoch s0') (mIdx s0') (mTL s0')
            (mTrans s0') (mChall s0') .v0 (mMaxAcc s0') (mLeaks s0') (mCorrs s0')
        let s2 : Expr O' _ (simMirT ℓ Pt) :=
          mLeakE s1 (maxN (.fst (mEpoch s0')) (.snd (mEpoch s0')))
        mMk (mB s2) (mWin s2) (mEpoch s2) (mIdx s2) (mTL s2)
          (mTrans s2) (mChall s2) (mComp s2) (mMaxAcc s2) (mLeaks s2)
          (.cons (.pair p0' (pGet (mEpoch s0') p0')) (mCorrs s2))))

def mInWinE {O' : Ops ASig} {Γ} (s : Expr O' Γ (simMirT ℓ Pt)) (p : Expr O' Γ .bool) :
    Expr O' Γ .bool :=
  eLet (.pair s p) (.not (sendsInE (.snd .v0) (pGet (mEpoch (.fst .v0)) (.snd .v0))))

def mNoBobEpoch0E {O' : Ops ASig} {Γ} (s : Expr O' Γ (simMirT ℓ Pt)) (p : Expr O' Γ .bool) :
    Expr O' Γ .bool :=
  eLet (.pair s p) (.not (.and (.snd .v0) (.eqN (.snd (mEpoch (.fst .v0))) (.nat 0))))

def mNoSpkCorrE {O' : Ops ASig} {Γ} (s : Expr O' Γ (simMirT ℓ Pt)) (p : Expr O' Γ .bool) :
    Expr O' Γ .bool :=
  eLet (.pair s p) (.not (.and (.not (.snd .v0)) (.lt (.fst (mEpoch (.fst .v0))) (.nat 10))))

omit [DecidableEq Pt] [Zero Pt] in
@[simp] theorem mSetWin_eval {O' : Ops ASig} {Γ} (s : Expr O' Γ (simMirT ℓ Pt))
    (w : Expr O' Γ .bool) (ρ : Env Γ) (st : GameState Unit (Plain ℓ) Bytes)
    (hs : s.eval ρ = simMirEnc st) :
    (mSetWin s w).eval ρ = simMirEnc { st with win := w.eval ρ } := by
  simp [mSetWin, mMk, mB, mEpoch, mIdx, mTL, mTrans, mChall, mComp, mMaxAcc, mLeaks, mCorrs,
    hs, simMirEnc, Expr.eval, Expr.v0]

omit [DecidableEq Pt] [Zero Pt] in
@[simp] theorem mSafeChE_eval {O' : Ops ASig} {Γ} (s : Expr O' Γ (simMirT ℓ Pt))
    (p : Expr O' Γ .bool) (ρ : Env Γ) (st : GameState Unit (Plain ℓ) Bytes) (Q : Party)
    (hs : s.eval ρ = simMirEnc st) (hp : p.eval ρ = partyEnc Q) :
    (mSafeChE s p).eval ρ = st.safeCh 3 Q := by
  rw [mSafeChE, healedByE_eval]
  cases Q <;> simp [GameState.safeCh, mTL, mEpoch, pGet, hs, hp, Expr.eval, Expr.v0,
    simMirEnc, partyEnc]

omit [DecidableEq Pt] [Zero Pt] in
@[simp] theorem mSafeInjE_eval {O' : Ops ASig} {Γ} (s : Expr O' Γ (simMirT ℓ Pt))
    (ρ : Env Γ) (st : GameState Unit (Plain ℓ) Bytes) (hs : s.eval ρ = simMirEnc st) :
    (mSafeInjE s).eval ρ = st.safeInj 3 := by
  simp only [mSafeInjE, eval_eLet, Expr.eval, hs, healedByE_eval, minN_eval]
  simp [GameState.safeInj, mTL, mEpoch, Expr.eval, Expr.v0, simMirEnc]

omit [DecidableEq Pt] [Zero Pt] in
@[simp] theorem mLeakE_eval {O' : Ops ASig} {Γ} (s : Expr O' Γ (simMirT ℓ Pt))
    (l : Expr O' Γ .nat) (ρ : Env Γ) (st : GameState Unit (Plain ℓ) Bytes)
    (hs : s.eval ρ = simMirEnc st) :
    (mLeakE s l).eval ρ = simMirEnc (st.leak (l.eval ρ)) := by
  simp only [mLeakE, eval_eLet, mMk, Expr.eval, hs, maxOptE_eval]
  simp [GameState.leak, mB, mWin, mEpoch, mIdx, mTL, mTrans, mChall, mComp, mMaxAcc, mLeaks,
    mCorrs, Expr.eval, Expr.v0, Expr.v1, simMirEnc]

omit [DecidableEq Pt] [Zero Pt] in
@[simp] theorem mEpMgmtE_eval {O' : Ops ASig} {Γ} (qep : ℕ) (s : Expr O' Γ (simMirT ℓ Pt))
    (p bad : Expr O' Γ .bool) (ρ : Env Γ) (st : GameState Unit (Plain ℓ) Bytes) (Q : Party)
    (hs : s.eval ρ = simMirEnc st) (hp : p.eval ρ = partyEnc Q) :
    (mEpMgmtE qep s p bad).eval ρ = (st.epMgmt 3 qep Q (bad.eval ρ)).map simMirEnc := by
  unfold mEpMgmtE GameState.epMgmt
  rw [eval_eLet]
  have h0 : (Expr.pair s (.pair p bad)).eval ρ = (simMirEnc st, partyEnc Q, bad.eval ρ) := by
    simp [Expr.eval, hs, hp]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod (simMirT ℓ Pt) (.prod .bool .bool))
    (simMirEnc st, partyEnc Q, bad.eval ρ) ρ
  rw [ite_eval]
  have hSends : (sendsInE (.fst (.snd (Expr.v0 (O := O'))))
      (.add (pGet (mEpoch (.fst (Expr.v0 (O := O')))) (.fst (.snd (Expr.v0 (O := O')))))
        (.nat 1))).eval ρ₁ = Q.sendsIn (st.epoch Q + 1) := by
    rw [sendsInE_eval _ _ ρ₁ Q rfl]
    congr 1
    cases Q <;> simp [ρ₁, pGet, mEpoch, simMirEnc, partyEnc, Expr.eval, Expr.v0]
  rw [hSends]
  by_cases h1 : Q.sendsIn (st.epoch Q + 1)
  · simp only [h1, ↓reduceIte]
    rw [ite_eval]
    have hlt1 : (Expr.lt (.nat qep) (.add (pGet (mEpoch (.fst (Expr.v0 (O := O'))))
        (.fst (.snd (Expr.v0 (O := O'))))) (.nat 1))).eval ρ₁ =
        decide (qep < st.epoch Q + 1) := by
      cases Q <;> simp [ρ₁, pGet, mEpoch, simMirEnc, partyEnc, Expr.eval, Expr.v0]
    rw [hlt1]
    by_cases h2 : qep < st.epoch Q + 1
    · simp [h2, Expr.eval]
    · simp only [h2, decide_false, Bool.false_eq_true, ↓reduceIte, Option.map_some]
      rw [eval_eLet, ite_eval]
      have hCond : (Expr.and (.snd (.snd (Expr.v0 (O := O'))))
          (.not (mSafeChE (.fst (Expr.v0 (O := O')))
            (.fst (.snd (Expr.v0 (O := O'))))))).eval ρ₁ =
          (bad.eval ρ && !(st.safeCh 3 Q)) := by
        have hsafe := mSafeChE_eval (.fst (Expr.v0 (O := O')))
          (.fst (.snd (Expr.v0 (O := O')))) ρ₁ st Q rfl rfl
        simp only [Expr.eval, hsafe]; rfl
      have hLeak : (mLeakE (.fst (Expr.v0 (O := O')))
          (.add (pGet (mEpoch (.fst (Expr.v0 (O := O')))) (.fst (.snd (Expr.v0 (O := O')))))
            (.nat 1))).eval ρ₁ = simMirEnc (st.leak (st.epoch Q + 1)) := by
        rw [mLeakE_eval (.fst (Expr.v0 (O := O'))) _ ρ₁ st rfl]
        congr 2
        cases Q <;> simp [ρ₁, pGet, mEpoch, simMirEnc, partyEnc, Expr.eval, Expr.v0]
      have hBase : (Expr.fst (Expr.v0 (O := O'))).eval ρ₁ = simMirEnc st := rfl
      rw [hCond, hLeak, hBase]
      set st₁ := if (bad.eval ρ && !(st.safeCh 3 Q)) = true then st.leak (st.epoch Q + 1) else st
      have hst₁ : (if (bad.eval ρ && !(st.safeCh 3 Q)) = true
          then (simMirEnc (st.leak (st.epoch Q + 1)) : (simMirT ℓ Pt).denote)
          else simMirEnc st) = simMirEnc st₁ := by
        dsimp only [st₁]; split_ifs <;> rfl
      rw [hst₁]
      cases Q <;>
        simp [ρ₁, mMk, mB, mWin, mEpoch, mIdx, mTL, mTrans, mChall, mComp,
          mMaxAcc, mLeaks, mCorrs, pGet, pSet, simMirEnc, partyEnc, Function.update,
          Expr.eval, Expr.v0, Expr.v1]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    rw [ite_eval]
    have hlt2 : (Expr.lt (.nat qep) (pGet (mEpoch (.fst (Expr.v0 (O := O'))))
        (.fst (.snd (Expr.v0 (O := O')))))).eval ρ₁ = decide (qep < st.epoch Q) := by
      cases Q <;> simp [ρ₁, pGet, mEpoch, simMirEnc, partyEnc, Expr.eval, Expr.v0]
    rw [hlt2]
    by_cases h2 : qep < st.epoch Q <;> simp [ρ₁, h2, Expr.eval, Expr.v0]

omit [DecidableEq Pt] [Zero Pt] in
@[simp] theorem mRecordE_eval {O' : Ops ASig} {Γ} (s : Expr O' Γ (simMirT ℓ Pt))
    (p : Expr O' Γ .bool) (r : Expr O' Γ (simRecT ℓ Pt)) (isChall : Expr O' Γ .bool) (ρ : Env Γ)
    (st : GameState Unit (Plain ℓ) Bytes) (Q : Party) (rec_ : Record (Plain ℓ) Bytes)
    (hs : s.eval ρ = simMirEnc st) (hp : p.eval ρ = partyEnc Q) (hr : r.eval ρ = simRecEnc rec_) :
    (mRecordE s p r isChall).eval ρ = simMirEnc (st.record 3 Q () rec_ (isChall.eval ρ)) := by
  unfold mRecordE
  rw [eval_eLet]
  have h0 : (Expr.pair s (.pair p (.pair r isChall))).eval ρ =
      (simMirEnc st, partyEnc Q, simRecEnc rec_, isChall.eval ρ) := by
    simp [Expr.eval, hs, hp, hr]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod (simMirT ℓ Pt) (.prod .bool (.prod (simRecT ℓ Pt) .bool)))
    (simMirEnc st, partyEnc Q, simRecEnc rec_, isChall.eval ρ) ρ
  have hSafe : (mSafeChE (.fst (Expr.v0 (O := O'))) (.fst (.snd (Expr.v0 (O := O'))))).eval ρ₁ =
      st.safeCh 3 Q :=
    mSafeChE_eval (.fst .v0) (.fst (.snd .v0)) ρ₁ st Q rfl rfl
  simp only [mMk, Expr.eval, hSafe]
  cases Q <;> cases hch : isChall.eval ρ <;>
    by_cases hsafeA : st.safeCh 3 .A <;> by_cases hsafeB : st.safeCh 3 .B <;>
    simp [ρ₁, GameState.record, mB, mWin, mEpoch, mIdx, mTL, mTrans,
      mChall, mComp, mMaxAcc, mLeaks, mCorrs, posIdx, srecPos, pSet,
      hch, hsafeA, hsafeB, simMirEnc, simRecEnc, posEnc, partyEnc, Function.update,
      Expr.eval, Expr.v0]

@[simp] theorem mInTransitE_eval {Γ} (Lq : ℕ) (s : Expr AOps Γ (simMirT ℓ Pt))
    (qParty : Expr AOps Γ .bool) (w : Expr AOps Γ (B 32)) (ρ : Env Γ)
    (st : GameState Unit (Plain ℓ) Bytes) (Q : Party)
    (hLq : st.trans.length ≤ Lq)
    (hs : s.eval ρ = simMirEnc st) (hq : qParty.eval ρ = partyEnc Q) :
    (mInTransitE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) Lq s qParty w).eval ρ =
      (st.inTransit Q (w.eval ρ)).map simRecEnc := by
  have htake : (st.trans.map (simRecEnc (ℓ := ℓ) (Pt := Pt))).take Lq =
      st.trans.map (simRecEnc (ℓ := ℓ) (Pt := Pt)) :=
    List.take_of_length_le (by simpa using hLq)
  simp only [mInTransitE, eval_eLet, GameState.inTransit, mTrans, srecPos, posSender, srecCt,
    Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ,
    boolEq_eval, eval_sOpPure, AtomicPureOp.eval, hs, hq, simMirEnc, htake]
  rw [find?_map_eq]
  congr 2
  funext ⟨⟨sender, ep, idx⟩, msg, ct⟩
  cases sender <;> cases Q <;> by_cases h : ct = w.eval ρ <;>
    simp [simRecEnc, posEnc, partyEnc, h]

omit [DecidableEq Pt] [Zero Pt] in
@[simp] theorem mDeleteE_eval {O' : Ops ASig} {Γ} (Lq : ℕ) (s : Expr O' Γ (simMirT ℓ Pt))
    (pos : Expr O' Γ posTy) (ρ : Env Γ) (st : GameState Unit (Plain ℓ) Bytes) (p : Pos)
    (hTrans : st.trans.length ≤ Lq) (hChall : st.chall.length ≤ Lq) (hComp : st.comp.length ≤ Lq)
    (hs : s.eval ρ = simMirEnc st) (hp : pos.eval ρ = posEnc p) :
    (mDeleteE Lq s pos).eval ρ = simMirEnc (st.delete p) := by
  have ht1 : (st.trans.map (simRecEnc (ℓ := ℓ) (Pt := Pt))).take Lq =
      st.trans.map (simRecEnc (ℓ := ℓ) (Pt := Pt)) :=
    List.take_of_length_le (by simpa using hTrans)
  have ht2 : (st.chall.map posEnc).take Lq = st.chall.map posEnc :=
    List.take_of_length_le (by simpa using hChall)
  have ht3 : (st.comp.map posEnc).take Lq = st.comp.map posEnc :=
    List.take_of_length_le (by simpa using hComp)
  simp only [mDeleteE, eval_eLet, GameState.delete, mMk, mB, mWin, mEpoch, mIdx, mTL, mTrans,
    mChall, mComp, mMaxAcc, mLeaks, mCorrs, srecPos, Expr.eval, Expr.v0, Expr.v1, Expr.v2,
    Env.get_cons_zero, Env.get_cons_succ, posEq_eval, hs, hp, simMirEnc, ht1, ht2, ht3,
    posDec_posEnc]
  have hstep1 :
      (fun (x : (simRecT ℓ Pt).denote) (acc : List (simRecT ℓ Pt).denote) =>
        if (posDec x.1 == p) = true then acc else x :: acc) =
      (fun x acc => if (!(posDec x.1 == p)) = true then x :: acc else acc) := by
    funext x acc; cases (posDec x.1 == p) <;> rfl
  have hstep2 :
      (fun (x : Bool × (ℕ × ℕ)) (acc : List (Bool × (ℕ × ℕ))) =>
        if (posDec x == p) = true then acc else x :: acc) =
      (fun x acc => if (!(posDec x == p)) = true then x :: acc else acc) := by
    funext x acc; cases (posDec x == p) <;> rfl
  rw [hstep1, hstep2, foldr_filter_map, foldr_filter_map, foldr_filter_map]
  simp [simRecEnc, posDec_posEnc, bne]

omit [DecidableEq Pt] [Zero Pt] in
@[simp] theorem mAcceptE_eval {O' : Ops ASig} {Γ} (Lq : ℕ) (s : Expr O' Γ (simMirT ℓ Pt))
    (p : Expr O' Γ .bool) (pos : Expr O' Γ posTy) (ρ : Env Γ)
    (st : GameState Unit (Plain ℓ) Bytes) (Q : Party) (pos₀ : Pos)
    (hTrans : st.trans.length ≤ Lq) (hChall : st.chall.length ≤ Lq) (hComp : st.comp.length ≤ Lq)
    (hs : s.eval ρ = simMirEnc st) (hp : p.eval ρ = partyEnc Q) (hpos : pos.eval ρ = posEnc pos₀) :
    (mAcceptE Lq s p pos).eval ρ = simMirEnc (st.accept Q () pos₀) := by
  have hdel := mDeleteE_eval Lq s pos ρ st pos₀ hTrans hChall hComp hs hpos
  simp only [mAcceptE, eval_eLet, mMk, Expr.eval, hdel, hp, hpos]
  cases Q <;>
  · simp [GameState.accept, mB, mWin, mEpoch, mIdx, mTL, mTrans,
      mChall, mComp, mMaxAcc, mLeaks, mCorrs, posEpoch, posIdx, pGet, pSet,
      maxAccGet, maxAccSet, maxN_eval, simMirEnc, posEnc, partyEnc,
      Function.update, Expr.eval, Expr.v0]
    funext j; split_ifs with hj <;> simp [hj]

omit [DecidableEq Pt] [Zero Pt] in
@[simp] theorem mCompContainsE_eval {O' : Ops ASig} {Γ} (Lq : ℕ) (s : Expr O' Γ (simMirT ℓ Pt))
    (pos : Expr O' Γ posTy) (ρ : Env Γ) (st : GameState Unit (Plain ℓ) Bytes) (pos₀ : Pos)
    (hComp : st.comp.length ≤ Lq) (hs : s.eval ρ = simMirEnc st)
    (hpos : pos.eval ρ = posEnc pos₀) :
    (mCompContainsE Lq s pos).eval ρ = st.comp.contains pos₀ := by
  have ht : (st.comp.map posEnc).take Lq = st.comp.map posEnc :=
    List.take_of_length_le (by simpa using hComp)
  simp only [mCompContainsE, eval_eLet, mComp, Expr.eval, Expr.v0, Expr.v1,
    Env.get_cons_zero, Env.get_cons_succ, posEq_eval, hs, hpos, simMirEnc, ht]
  rw [any_map_eq]
  simp only [posDec_posEnc]
  exact any_beq_eq_contains pos₀ st.comp

omit [DecidableEq Pt] [Zero Pt] in
@[simp] theorem mChallContainsE_eval {O' : Ops ASig} {Γ} (Lq : ℕ) (s : Expr O' Γ (simMirT ℓ Pt))
    (pos : Expr O' Γ posTy) (ρ : Env Γ) (st : GameState Unit (Plain ℓ) Bytes) (pos₀ : Pos)
    (hChall : st.chall.length ≤ Lq) (hs : s.eval ρ = simMirEnc st)
    (hpos : pos.eval ρ = posEnc pos₀) :
    (mChallContainsE Lq s pos).eval ρ = st.chall.contains pos₀ := by
  have ht : (st.chall.map posEnc).take Lq = st.chall.map posEnc :=
    List.take_of_length_le (by simpa using hChall)
  simp only [mChallContainsE, eval_eLet, mChall, Expr.eval, Expr.v0, Expr.v1,
    Env.get_cons_zero, Env.get_cons_succ, posEq_eval, hs, hpos, simMirEnc, ht]
  rw [any_map_eq]
  simp only [posDec_posEnc]
  exact any_beq_eq_contains pos₀ st.chall

omit [DecidableEq Pt] [Zero Pt] in
@[simp] theorem mTrivialE_eval {O' : Ops ASig} {Γ} (Lq : ℕ) (s : Expr O' Γ (simMirT ℓ Pt))
    (pos : Expr O' Γ posTy) (ρ : Env Γ) (st : GameState Unit (Plain ℓ) Bytes) (pos₀ : Pos)
    (hTrans : st.trans.length ≤ Lq) (hComp : st.comp.length ≤ Lq)
    (hs : s.eval ρ = simMirEnc st) (hpos : pos.eval ρ = posEnc pos₀) :
    (mTrivialE Lq s pos).eval ρ = st.trivial 3 pos₀ := by
  have ht : (st.trans.map (simRecEnc (ℓ := ℓ) (Pt := Pt))).take Lq =
      st.trans.map (simRecEnc (ℓ := ℓ) (Pt := Pt)) :=
    List.take_of_length_le (by simpa using hTrans)
  simp only [mTrivialE, eval_eLet, Expr.eval, hs, hpos, orE_eval, healedByE_eval]
  rw [mCompContainsE_eval Lq _ _ _ st pos₀ hComp rfl rfl]
  simp only [GameState.trivial, mTrans, mTL, posEpoch, srecPos,
    Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ,
    posEq_eval, simMirEnc, ht]
  rw [any_map_eq]
  simp [simRecEnc, posEnc, posDec]

omit [DecidableEq Pt] [Zero Pt] in
@[simp] theorem mCorrAllowedE_eval {O' : Ops ASig} {Γ} (Lq : ℕ) (s : Expr O' Γ (simMirT ℓ Pt))
    (p : Expr O' Γ .bool) (ρ : Env Γ) (st : GameState Unit (Plain ℓ) Bytes) (Q : Party)
    (hTrans : st.trans.length ≤ Lq) (hChall : st.chall.length ≤ Lq) (hComp : st.comp.length ≤ Lq)
    (hs : s.eval ρ = simMirEnc st) (hp : p.eval ρ = partyEnc Q) :
    (mCorrAllowedE Lq s p).eval ρ = st.corrAllowed Q := by
  unfold mCorrAllowedE GameState.corrAllowed
  rw [eval_eLet]
  have h0 : (Expr.pair s p).eval ρ = (simMirEnc st, partyEnc Q) := by simp [Expr.eval, hs, hp]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod (simMirT ℓ Pt) .bool) (simMirEnc st, partyEnc Q) ρ
  have htCh : (st.chall.map posEnc).take Lq = st.chall.map posEnc :=
    List.take_of_length_le (by simpa using hChall)
  have htTr : (st.trans.map (simRecEnc (ℓ := ℓ) (Pt := Pt))).take Lq =
      st.trans.map (simRecEnc (ℓ := ℓ) (Pt := Pt)) :=
    List.take_of_length_le (by simpa using hTrans)
  have hCh0 : (mChall (.fst (Expr.v0 (O := O')))).eval ρ₁ = st.chall.map posEnc := rfl
  have hTr0 : (mTrans (.fst (Expr.v0 (O := O')))).eval ρ₁ =
      st.trans.map (simRecEnc (ℓ := ℓ) (Pt := Pt)) := rfl
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
    have hcomp := mCompContainsE_eval (O' := O') Lq (.fst .v1) (srecPos .v0)
      (Env.cons (t := simRecT ℓ Pt) (simRecEnc r) ρ₁) st r.pos hComp rfl rfl
    rw [hcomp]
    simp [ρ₁, srecPos, posSender, otherE, simRecEnc, posEnc, ← partyEnc_other, partyEnc_beq,
      Expr.eval, Expr.v0, Expr.v1]

omit [DecidableEq Pt] [Zero Pt] in
@[simp] theorem mAfterCorrE_eval {O' : Ops ASig} {Γ} (Lq : ℕ) (s : Expr O' Γ (simMirT ℓ Pt))
    (p : Expr O' Γ .bool) (ρ : Env Γ) (st : GameState Unit (Plain ℓ) Bytes) (Q : Party)
    (hTrans : st.trans.length ≤ Lq)
    (hCompU : ∃ U : List Pos, U.length ≤ Lq ∧ CountLe st.comp U ∧ ∀ r ∈ st.trans, r.pos ∈ U)
    (hs : s.eval ρ = simMirEnc st) (hp : p.eval ρ = partyEnc Q) :
    (mAfterCorrE Lq s p).eval ρ = simMirEnc (afterCorrDedup st Q) := by
  rcases hCompU with ⟨U, hULq, haccU, htransU⟩
  simp only [mAfterCorrE, eval_eLet, mLeakE, maxOptE, mMk, mB, mWin, mEpoch, mIdx, mTL,
    mTrans, mChall, mComp, mMaxAcc, mLeaks, mCorrs, posSender, srecPos, otherE,
    Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get_cons_zero, Env.get_cons_succ,
    boolEq_eval, posEq_eval, maxN_eval, hs, hp, simMirEnc]
  have hfold := foldr_dedup_map_eq (K := Lq) (encR := simRecEnc (ℓ := ℓ) (Pt := Pt))
    (encP := posEnc) (posOf := Record.pos)
    (keep := fun r : Record (Plain ℓ) Bytes => r.pos.sender == Q.other)
    (keepE := fun rE => rE.1.1 == !partyEnc Q)
    (posE := fun rE => rE.1)
    (eqP := fun p₁ p₂ => posDec p₁ == posDec p₂)
    (rs := st.trans) (acc := st.comp) (U := U)
    (by intro r; simp [simRecEnc, posEnc, ← partyEnc_other, partyEnc_beq])
    (by intro r; rfl)
    (by intro p₁ p₂; simp [posDec_posEnc])
    hTrans hULq haccU (fun r hr _ => htransU r hr)
  rw [hfold]
  cases Q <;>
  · simp only [afterCorrDedup, GameState.leak, maxOpt, pGet, partyEnc,
      Expr.eval, Expr.v0, Env.get_cons_zero]
    cases st.tL <;> rfl

private def compTblEnc (l : List Pos) : (ℕ → ℕ → Bool) × (ℕ → ℕ → Bool) :=
  ((fun ep idx => l.contains ⟨.A, ep, idx⟩),
   (fun ep idx => l.contains ⟨.B, ep, idx⟩))

omit [DecidableEq Pt] [Zero Pt] in
private theorem compTblInsertE_eval {O' : Ops ASig} {Γ}
    (m : Expr O' Γ (compTblTy (ℓ := ℓ) (Pt := Pt))) (pos : Expr O' Γ posTy)
    (ρ : Env Γ) (l : List Pos) (p₀ : Pos)
    (hm : m.eval ρ = compTblEnc l) (hpos : pos.eval ρ = posEnc p₀) :
    (compTblInsertE m pos).eval ρ = compTblEnc (p₀ :: l) := by
  rcases p₀ with ⟨sender, ep₀, idx₀⟩
  cases sender
  · simp only [compTblInsertE, eval_eLet, compTblEnc, posSender, posEpoch, posIdx, pGet, pSet,
      hm, hpos, posEnc, partyEnc, Expr.eval, Expr.v0, Env.get, ↓reduceIte, Bool.false_eq_true,
      Prod.mk.injEq]
    constructor
    · funext ep idx
      by_cases hep : ep = ep₀
      · subst hep
        by_cases hidx : idx = idx₀
        · subst hidx; rw [Bool.eq_iff_iff]; simp
        · rw [Bool.eq_iff_iff]; simp [hidx]
      · rw [Bool.eq_iff_iff]; simp [hep]
    · funext ep idx; rw [Bool.eq_iff_iff]; simp
  · simp only [compTblInsertE, eval_eLet, compTblEnc, posSender, posEpoch, posIdx, pGet, pSet,
      hm, hpos, posEnc, partyEnc, Expr.eval, Expr.v0, Env.get, ↓reduceIte, Prod.mk.injEq]
    constructor
    · funext ep idx; rw [Bool.eq_iff_iff]; simp
    · funext ep idx
      by_cases hep : ep = ep₀
      · subst hep
        by_cases hidx : idx = idx₀
        · subst hidx; rw [Bool.eq_iff_iff]; simp
        · rw [Bool.eq_iff_iff]; simp [hidx]
      · rw [Bool.eq_iff_iff]; simp [hep]

omit [DecidableEq Pt] [Zero Pt] in
private theorem compTblGetE_eval {O' : Ops ASig} {Γ}
    (m : Expr O' Γ (compTblTy (ℓ := ℓ) (Pt := Pt))) (pos : Expr O' Γ posTy)
    (ρ : Env Γ) (l : List Pos) (p₀ : Pos)
    (hm : m.eval ρ = compTblEnc l) (hpos : pos.eval ρ = posEnc p₀) :
    (compTblGetE m pos).eval ρ = l.contains p₀ := by
  rcases p₀ with ⟨sender, ep, idx⟩
  cases sender <;>
    simp [compTblGetE, eval_eLet, compTblEnc, posSender, posEpoch, posIdx, pGet,
      hm, hpos, posEnc, partyEnc, Expr.eval, Expr.v0]

omit [DecidableEq Pt] [Zero Pt] in
private theorem compTblOfListE_eval {O' : Ops ASig} {Γ}
    (Lq : ℕ) (xs : Expr O' Γ (.list posTy))
    (ρ : Env Γ) (l : List Pos)
    (hlen : l.length ≤ Lq) (hxs : xs.eval ρ = l.map posEnc) :
    (compTblOfListE Lq xs).eval ρ = compTblEnc l := by
  have htake : (l.map posEnc).take Lq = l.map posEnc :=
    List.take_of_length_le (by simpa using hlen)
  simp only [compTblOfListE, Expr.eval, hxs, htake]
  have hemp : (compTblEmptyE (ℓ := ℓ) (Pt := Pt) (O' := O')).eval ρ = compTblEnc [] := by
    ext <;> simp [compTblEmptyE, compTblEnc, Expr.eval]
  rw [hemp]
  clear hlen hxs htake
  induction l with
  | nil => rfl
  | cons p ps ih =>
    rw [List.map_cons, List.foldr_cons, ih]
    exact compTblInsertE_eval .v1 .v0 _ ps p rfl rfl

omit [DecidableEq Pt] [Zero Pt] in
@[simp] theorem mCorrAllowedFastE_eval {O' : Ops ASig} {Γ} (Lq : ℕ) (s : Expr O' Γ (simMirT ℓ Pt))
    (p : Expr O' Γ .bool) (ρ : Env Γ) (st : GameState Unit (Plain ℓ) Bytes) (Q : Party)
    (hTrans : st.trans.length ≤ Lq) (hChall : st.chall.length ≤ Lq) (hComp : st.comp.length ≤ Lq)
    (hs : s.eval ρ = simMirEnc st) (hp : p.eval ρ = partyEnc Q) :
    (mCorrAllowedFastE Lq s p).eval ρ = st.corrAllowed Q := by
  unfold mCorrAllowedFastE GameState.corrAllowed
  rw [eval_eLet]
  have h0 : (Expr.pair s p).eval ρ = (simMirEnc st, partyEnc Q) := by simp [Expr.eval, hs, hp]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod (simMirT ℓ Pt) .bool) (simMirEnc st, partyEnc Q) ρ
  rw [eval_eLet]
  have htbl : (compTblOfListE Lq (mComp (.fst (Expr.v0 (O := O'))))).eval ρ₁ = compTblEnc st.comp :=
    compTblOfListE_eval Lq _ ρ₁ st.comp hComp rfl
  rw [htbl]; clear htbl
  set ρ₂ := Env.cons (t := compTblTy (ℓ := ℓ) (Pt := Pt)) (compTblEnc st.comp) ρ₁
  have htCh : (st.chall.map posEnc).take Lq = st.chall.map posEnc :=
    List.take_of_length_le (by simpa using hChall)
  have htTr : (st.trans.map (simRecEnc (ℓ := ℓ) (Pt := Pt))).take Lq =
      st.trans.map (simRecEnc (ℓ := ℓ) (Pt := Pt)) :=
    List.take_of_length_le (by simpa using hTrans)
  have hCh0 : (mChall (.fst (Expr.v1 (O := O')))).eval ρ₂ = st.chall.map posEnc := rfl
  have hTr0 : (mTrans (.fst (Expr.v1 (O := O')))).eval ρ₂ =
      st.trans.map (simRecEnc (ℓ := ℓ) (Pt := Pt)) := rfl
  simp only [Expr.eval, hCh0, hTr0, htCh, htTr]
  congr 1
  · congr 1
    rw [any_map_eq]
    congr 1; funext pos
    simp [ρ₂, ρ₁, posSender, otherE, posEnc, ← partyEnc_other, partyEnc_beq, Expr.eval,
      Expr.v0, Expr.v2, Env.get_cons_zero, Env.get_cons_succ]
  · congr 1
    rw [any_map_eq]
    congr 1; funext r
    have hcomp := compTblGetE_eval (O' := O') .v1 (srecPos .v0)
      (Env.cons (t := simRecT ℓ Pt) (simRecEnc r) ρ₂) st.comp r.pos rfl rfl
    rw [hcomp]
    simp [ρ₂, ρ₁, srecPos, posSender, otherE, simRecEnc, posEnc, ← partyEnc_other, partyEnc_beq,
      Expr.eval, Expr.v0, Expr.v2, Env.get_cons_zero, Env.get_cons_succ]

omit [DecidableEq Pt] [Zero Pt] in
theorem mAfterCorrFastE_eval_of_le {O' : Ops ASig} {Γ} (Lq : ℕ) (s : Expr O' Γ (simMirT ℓ Pt))
    (p : Expr O' Γ .bool) (ρ : Env Γ) (st : GameState Unit (Plain ℓ) Bytes) (Q : Party)
    (hTrans : st.trans.length ≤ Lq) (hComp : st.comp.length ≤ Lq)
    (hs : s.eval ρ = simMirEnc st) (hp : p.eval ρ = partyEnc Q) :
    (mAfterCorrFastE Lq s p).eval ρ = simMirEnc (afterCorrDedup st Q) := by
  unfold mAfterCorrFastE
  rw [eval_eLet]
  have h0 : (Expr.pair s p).eval ρ = (simMirEnc st, partyEnc Q) := by simp [Expr.eval, hs, hp]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod (simMirT ℓ Pt) .bool) (simMirEnc st, partyEnc Q) ρ
  rw [eval_eLet]
  have htbl : (compTblOfListE Lq (mComp (.fst (Expr.v0 (O := O'))))).eval ρ₁ = compTblEnc st.comp :=
    compTblOfListE_eval Lq _ ρ₁ st.comp hComp rfl
  have htr : (st.trans.map (simRecEnc (ℓ := ℓ) (Pt := Pt))).take Lq =
      st.trans.map (simRecEnc (ℓ := ℓ) (Pt := Pt)) :=
    List.take_of_length_le (by simpa using hTrans)
  let compOut (rs : List (Record (Plain ℓ) Bytes)) : List Pos :=
    dedupPrepend ((rs.filter (fun r => r.pos.sender == Q.other)).map (·.pos)) st.comp
  let stepE : Expr O'
      (simRecT ℓ Pt :: .prod (.list posTy) (compTblTy (ℓ := ℓ) (Pt := Pt)) ::
        .prod (simMirT ℓ Pt) .bool :: Γ)
      (.prod (.list posTy) (compTblTy (ℓ := ℓ) (Pt := Pt))) :=
    .ite
      (.and (boolEq (posSender (srecPos .v0)) (otherE (.snd .v2)))
        (.not (compTblGetE (.snd .v1) (srecPos .v0))))
      (.pair (.cons (srecPos .v0) (.fst .v1)) (compTblInsertE (.snd .v1) (srecPos .v0)))
      .v1
  have hfold : ∀ rs : List (Record (Plain ℓ) Bytes),
      (rs.map (simRecEnc (ℓ := ℓ) (Pt := Pt))).foldr
        (fun x acc => stepE.eval (Env.cons x (Env.cons acc ρ₁)))
        (st.comp.map posEnc, compTblEnc st.comp) =
      ((compOut rs).map posEnc, compTblEnc (compOut rs)) := by
    intro rs; induction rs with
    | nil => rfl
    | cons r rs ih =>
      rw [List.map_cons, List.foldr_cons, ih]
      set c := compOut rs
      let ρ_acc := Env.cons (t := .prod (.list posTy) (compTblTy (ℓ := ℓ) (Pt := Pt)))
        (c.map posEnc, compTblEnc c) ρ₁
      let ρ_step := Env.cons (t := simRecT ℓ Pt) (simRecEnc (ℓ := ℓ) (Pt := Pt) r) ρ_acc
      have hsend_eq : (boolEq (posSender (srecPos (Expr.v0 (O := O')))) (otherE (.snd .v2))).eval ρ_step =
          (r.pos.sender == Q.other) := by
        simp [ρ_step, ρ_acc, ρ₁, posSender, srecPos, otherE, simRecEnc, posEnc, ← partyEnc_other,
          partyEnc_beq, Expr.eval, Expr.v0, Expr.v2, Env.get_cons_zero, Env.get_cons_succ]
      have hget := compTblGetE_eval (O' := O') (.snd .v1) (srecPos .v0) ρ_step c r.pos rfl rfl
      have hins := compTblInsertE_eval (O' := O') (.snd .v1) (srecPos .v0) ρ_step c r.pos rfl rfl
      have hspos : (srecPos (Expr.v0 (O := O'))).eval ρ_step = posEnc r.pos := rfl
      have hv1 : (Expr.v1 (O := O')).eval ρ_step = (c.map posEnc, compTblEnc c) := rfl
      change stepE.eval ρ_step = _
      dsimp only [stepE]
      simp only [Expr.eval, hsend_eq, hget, hins, hspos, hv1]
      dsimp only [compOut, c]
      rw [List.filter_cons]
      by_cases hsnd : (r.pos.sender == Q.other) = true
      · simp only [hsnd, Bool.true_and, ↓reduceIte, List.map_cons, dedupPrepend_cons]
        cases hc : (dedupPrepend ((rs.filter (fun r => r.pos.sender == Q.other)).map (·.pos)) st.comp).contains r.pos <;>
          simp
      · have hsndF : (r.pos.sender == Q.other) = false := Bool.eq_false_iff.mpr hsnd
        simp [hsndF]
  have hTr0 : (mTrans (.fst (Expr.v0 (O := O')))).eval ρ₁ =
      st.trans.map (simRecEnc (ℓ := ℓ) (Pt := Pt)) := rfl
  have hCp0 : (mComp (.fst (Expr.v0 (O := O')))).eval ρ₁ = st.comp.map posEnc := rfl
  have hfsts :
      (Expr.fst (Expr.foldrB Lq (mTrans (.fst .v0))
        (.pair (mComp (.fst .v0)) (compTblOfListE Lq (mComp (.fst .v0)))) stepE)).eval ρ₁ =
      (compOut st.trans).map posEnc := by
    simp only [Expr.eval, hTr0, hCp0, htbl, htr]
    exact congrArg Prod.fst (hfold st.trans)
  change _ = _
  rw [hfsts]
  simp only [ρ₁, compOut, eval_eLet, mLeakE, maxOptE, mMk, mB, mWin, mEpoch, mIdx, mTL,
    mTrans, mChall, mComp, mMaxAcc, mLeaks, mCorrs,
    Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ, maxN_eval, simMirEnc]
  cases Q <;>
  · simp only [afterCorrDedup, GameState.leak, maxOpt, pGet, partyEnc,
      Expr.eval, Expr.v0, Env.get_cons_zero]
    cases st.tL <;> rfl

omit [DecidableEq Pt] [Zero Pt] in
@[simp] theorem mAfterCorrFastE_eval {O' : Ops ASig} {Γ} (Lq : ℕ) (s : Expr O' Γ (simMirT ℓ Pt))
    (p : Expr O' Γ .bool) (ρ : Env Γ) (st : GameState Unit (Plain ℓ) Bytes) (Q : Party)
    (hTrans : st.trans.length ≤ Lq)
    (hCompU : ∃ U : List Pos, U.length ≤ Lq ∧ CountLe st.comp U ∧ ∀ r ∈ st.trans, r.pos ∈ U)
    (hs : s.eval ρ = simMirEnc st) (hp : p.eval ρ = partyEnc Q) :
    (mAfterCorrFastE Lq s p).eval ρ = simMirEnc (afterCorrDedup st Q) := by
  rcases hCompU with ⟨U, hULq, haccU, _⟩
  exact mAfterCorrFastE_eval_of_le Lq s p ρ st Q hTrans ((countLe_length_le haccU).trans hULq) hs hp

omit [DecidableEq Pt] [Zero Pt] in
@[simp] theorem mInWinE_eval {O' : Ops ASig} {Γ} (s : Expr O' Γ (simMirT ℓ Pt))
    (p : Expr O' Γ .bool) (ρ : Env Γ) (st : GameState Unit (Plain ℓ) Bytes) (Q : Party)
    (hs : s.eval ρ = simMirEnc st) (hp : p.eval ρ = partyEnc Q) :
    (mInWinE s p).eval ρ = inReceiveOnlyEpoch st Q := by
  cases Q <;> simp [mInWinE, eval_eLet, inReceiveOnlyEpoch, sendsInE, pGet, mEpoch,
    hs, hp, simMirEnc, partyEnc, Party.sendsIn, BEq.beq, Expr.eval, Expr.v0]

omit [DecidableEq Pt] [Zero Pt] in
@[simp] theorem mNoBobEpoch0E_eval {O' : Ops ASig} {Γ} (s : Expr O' Γ (simMirT ℓ Pt))
    (p : Expr O' Γ .bool) (ρ : Env Γ) (st : GameState Unit (Plain ℓ) Bytes) (Q : Party)
    (hs : s.eval ρ = simMirEnc st) (hp : p.eval ρ = partyEnc Q) :
    (mNoBobEpoch0E s p).eval ρ = noBobSendInEpoch0 st Q := by
  cases Q <;> simp [mNoBobEpoch0E, eval_eLet, noBobSendInEpoch0, mEpoch,
    hs, hp, simMirEnc, partyEnc, BEq.beq, Expr.eval, Expr.v0]

omit [DecidableEq Pt] [Zero Pt] in
@[simp] theorem mNoSpkCorrE_eval {O' : Ops ASig} {Γ} (s : Expr O' Γ (simMirT ℓ Pt))
    (p : Expr O' Γ .bool) (ρ : Env Γ) (st : GameState Unit (Plain ℓ) Bytes) (Q : Party)
    (hs : s.eval ρ = simMirEnc st) (hp : p.eval ρ = partyEnc Q) :
    (mNoSpkCorrE s p).eval ρ = noAliceCorrWhileAliceBelowEpoch10 st Q := by
  cases Q <;> simp [mNoSpkCorrE, eval_eLet, noAliceCorrWhileAliceBelowEpoch10, mEpoch,
    hs, hp, simMirEnc, partyEnc, BEq.beq, Expr.eval, Expr.v0]

omit [DecidableEq Pt] [Zero Pt] in
theorem cost_mSetWin {O' : Ops ASig} {Γ} (s : Expr O' Γ (simMirT ℓ Pt)) (w : Expr O' Γ .bool) :
    (mSetWin s w).cost ≤ s.cost + w.cost + 200 := by
  simp only [mSetWin, cost_eLet, mMk, mB, mEpoch, mIdx, mTL, mTrans, mChall, mComp,
    mMaxAcc, mLeaks, mCorrs, Expr.cost, Expr.v0]
  omega

omit [DecidableEq Pt] [Zero Pt] in
theorem cost_mSafeChE {O' : Ops ASig} {Γ} (s : Expr O' Γ (simMirT ℓ Pt)) (p : Expr O' Γ .bool) :
    (mSafeChE s p).cost ≤ 3 * s.cost + p.cost + 40 := by
  have hb3 : bits 3 = 2 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  simp only [mSafeChE, healedByE, CryptoGames.SM.leN, mTL, mEpoch, pGet,
    Expr.cost, Expr.v0, Expr.v1, hb3]
  omega

omit [DecidableEq Pt] [Zero Pt] in
theorem cost_mSafeInjE {O' : Ops ASig} {Γ} (s : Expr O' Γ (simMirT ℓ Pt)) :
    (mSafeInjE s).cost ≤ s.cost + 50 := by
  have hb3 : bits 3 = 2 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  simp only [mSafeInjE, cost_eLet, healedByE, CryptoGames.SM.leN, minN, mTL, mEpoch,
    Expr.cost, Expr.v0, Expr.v1, hb3]
  omega

omit [DecidableEq Pt] [Zero Pt] in
theorem cost_mLeakE {O' : Ops ASig} {Γ} (s : Expr O' Γ (simMirT ℓ Pt)) (l : Expr O' Γ .nat) :
    (mLeakE s l).cost ≤ s.cost + l.cost + 400 := by
  simp only [mLeakE, cost_eLet, mMk, maxOptE, maxN, CryptoGames.SM.leN, mB, mWin, mEpoch, mIdx,
    mTL, mTrans, mChall, mComp, mMaxAcc, mLeaks, mCorrs, Expr.cost, Expr.v0, Expr.v1]
  omega

omit [DecidableEq Pt] [Zero Pt] in
theorem cost_mEpMgmtE {O' : Ops ASig} {Γ} (qep : ℕ) (s : Expr O' Γ (simMirT ℓ Pt))
    (p bad : Expr O' Γ .bool) :
    (mEpMgmtE qep s p bad).cost ≤ s.cost + p.cost + bad.cost + 2 * bits qep + 900 := by
  have hb0 : bits 0 = 1 := bits_zero
  have hb1 : bits 1 = 1 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  have hb2 : bits 2 = 2 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  have hb3 : bits 3 = 2 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  simp only [mEpMgmtE, cost_eLet, mSafeChE, mLeakE, mMk, maxOptE, maxN, healedByE,
    CryptoGames.SM.leN, sendsInE, pGet, pSet, mB, mWin, mEpoch, mIdx, mTL, mTrans,
    mChall, mComp, mMaxAcc, mLeaks, mCorrs, Expr.cost, Expr.v0, Expr.v1,
    hb0, hb1, hb2, hb3]
  omega

omit [DecidableEq Pt] [Zero Pt] in
theorem cost_mRecordE {O' : Ops ASig} {Γ} (s : Expr O' Γ (simMirT ℓ Pt)) (p : Expr O' Γ .bool)
    (r : Expr O' Γ (simRecT ℓ Pt)) (isChall : Expr O' Γ .bool) :
    (mRecordE s p r isChall).cost ≤ s.cost + p.cost + r.cost + isChall.cost + 260 := by
  have hb3 : bits 3 = 2 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  simp only [mRecordE, cost_eLet, mSafeChE, healedByE, CryptoGames.SM.leN, mMk, pGet, pSet,
    posIdx, srecPos, mB, mWin, mEpoch, mIdx, mTL, mTrans, mChall, mComp, mMaxAcc, mLeaks,
    mCorrs, Expr.cost, Expr.v0, Expr.v1, hb3]
  omega

theorem cost_mInTransitE {Γ} (Lq : ℕ) (s : Expr AOps Γ (simMirT ℓ Pt))
    (qParty : Expr AOps Γ .bool) (w : Expr AOps Γ (B 32)) :
    (mInTransitE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) Lq s qParty w).cost ≤
      s.cost + qParty.cost + w.cost + 200 * Lq + 100 := by
  have h32 : ((32 : ℕ+) : ℕ) = 32 := rfl
  simp only [mInTransitE, cost_eLet, mTrans, boolEq, posSender, srecPos, srecCt,
    Expr.cost, cost_sOpPure, AtomicPureOp.cost,
    Expr.v0, Expr.v1, h32, Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
  omega

omit [DecidableEq Pt] [Zero Pt] in
theorem cost_mAcceptE {O' : Ops ASig} {Γ} (Lq : ℕ) (s : Expr O' Γ (simMirT ℓ Pt))
    (p : Expr O' Γ .bool) (pos : Expr O' Γ posTy) :
    (mAcceptE Lq s p pos).cost ≤ s.cost + p.cost + 2 * pos.cost + 350 * Lq + 1500 := by
  simp only [mAcceptE, mDeleteE, cost_eLet, mMk, posEq, boolEq, posSender, posEpoch, posIdx,
    srecPos, pGet, pSet, maxAccGet, maxAccSet, maxN, CryptoGames.SM.leN, mB, mWin, mEpoch, mIdx,
    mTL, mTrans, mChall, mComp, mMaxAcc, mLeaks, mCorrs, Expr.cost, Expr.v0, Expr.v1, Expr.v2,
    Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
  omega

omit [DecidableEq Pt] [Zero Pt] in
theorem cost_mCompContainsE {O' : Ops ASig} {Γ} (Lq : ℕ) (s : Expr O' Γ (simMirT ℓ Pt))
    (pos : Expr O' Γ posTy) :
    (mCompContainsE Lq s pos).cost ≤ s.cost + pos.cost + 100 * Lq + 80 := by
  simp only [mCompContainsE, cost_eLet, mComp, posEq, boolEq, posSender, posEpoch, posIdx,
    Expr.cost, Expr.v0, Expr.v1, Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
  omega

omit [DecidableEq Pt] [Zero Pt] in
theorem cost_mChallContainsE {O' : Ops ASig} {Γ} (Lq : ℕ) (s : Expr O' Γ (simMirT ℓ Pt))
    (pos : Expr O' Γ posTy) :
    (mChallContainsE Lq s pos).cost ≤ s.cost + pos.cost + 100 * Lq + 80 := by
  simp only [mChallContainsE, cost_eLet, mChall, posEq, boolEq, posSender, posEpoch, posIdx,
    Expr.cost, Expr.v0, Expr.v1, Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
  omega

omit [DecidableEq Pt] [Zero Pt] in
theorem cost_mTrivialE {O' : Ops ASig} {Γ} (Lq : ℕ) (s : Expr O' Γ (simMirT ℓ Pt))
    (pos : Expr O' Γ posTy) :
    (mTrivialE Lq s pos).cost ≤ s.cost + pos.cost + 200 * Lq + 200 := by
  have hb3 : bits 3 = 2 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  simp only [mTrivialE, mCompContainsE, cost_eLet, orE, healedByE, CryptoGames.SM.leN,
    posEq, boolEq, posSender, posEpoch, posIdx, srecPos, mComp, mTrans, mTL,
    Expr.cost, Expr.v0, Expr.v1, hb3, Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
  omega

omit [DecidableEq Pt] [Zero Pt] in
theorem cost_mCorrAllowedE {O' : Ops ASig} {Γ} (Lq : ℕ) (s : Expr O' Γ (simMirT ℓ Pt))
    (p : Expr O' Γ .bool) :
    (mCorrAllowedE Lq s p).cost ≤ s.cost + p.cost + 300 * Lq + 150 * (Lq * Lq) + 300 := by
  simp only [mCorrAllowedE, mCompContainsE, cost_eLet, boolEq, otherE, posEq, posSender,
    posEpoch, posIdx, srecPos, mChall, mTrans, mComp, Expr.cost, Expr.v0, Expr.v1,
    Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd, Nat.mul_add]
  nlinarith

omit [DecidableEq Pt] [Zero Pt] in
theorem cost_mAfterCorrE {O' : Ops ASig} {Γ} (Lq : ℕ) (s : Expr O' Γ (simMirT ℓ Pt))
    (p : Expr O' Γ .bool) :
    (mAfterCorrE Lq s p).cost ≤ s.cost + p.cost + 1500 * Lq + 1000 * (Lq * Lq) + 10000 := by
  simp only [mAfterCorrE, mLeakE, cost_eLet, mMk, maxOptE, maxN, CryptoGames.SM.leN, boolEq,
    otherE, posEq, posSender, posEpoch, posIdx, srecPos, pGet, mB, mWin, mEpoch, mIdx, mTL,
    mTrans, mChall, mComp, mMaxAcc, mLeaks, mCorrs, Expr.cost, Expr.v0, Expr.v1, Expr.v2,
    Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd, Nat.mul_add]
  nlinarith

omit [DecidableEq Pt] [Zero Pt] in
theorem cost_mCorrAllowedFastE {O' : Ops ASig} {Γ} (Lq : ℕ) (s : Expr O' Γ (simMirT ℓ Pt))
    (p : Expr O' Γ .bool) :
    (mCorrAllowedFastE Lq s p).cost ≤ s.cost + p.cost + 600 * Lq + 300 := by
  simp only [mCorrAllowedFastE, compTblOfListE, compTblEmptyE, compTblInsertE, compTblGetE,
    cost_eLet, boolEq, otherE, posSender, posEpoch, posIdx, srecPos, pGet, pSet,
    mChall, mTrans, mComp, Expr.cost, Expr.v0, Expr.v1, Expr.v2,
    Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
  omega

omit [DecidableEq Pt] [Zero Pt] in
theorem cost_mAfterCorrFastE {O' : Ops ASig} {Γ} (Lq : ℕ) (s : Expr O' Γ (simMirT ℓ Pt))
    (p : Expr O' Γ .bool) :
    (mAfterCorrFastE Lq s p).cost ≤ s.cost + p.cost + 1500 * Lq + 10000 := by
  simp only [mAfterCorrFastE, compTblOfListE, compTblEmptyE, compTblInsertE, compTblGetE,
    mLeakE, cost_eLet, mMk, maxOptE, maxN, CryptoGames.SM.leN, boolEq, otherE,
    posSender, posEpoch, posIdx, srecPos, pGet, pSet, mB, mWin, mEpoch, mIdx, mTL,
    mTrans, mChall, mComp, mMaxAcc, mLeaks, mCorrs, Expr.cost, Expr.v0, Expr.v1, Expr.v2,
    Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
  omega

omit [DecidableEq Pt] [Zero Pt] in
theorem cost_mInWinE {O' : Ops ASig} {Γ} (s : Expr O' Γ (simMirT ℓ Pt)) (p : Expr O' Γ .bool) :
    (mInWinE s p).cost ≤ s.cost + p.cost + 50 := by
  have hb0 : bits 0 = 1 := bits_zero
  have hb1 : bits 1 = 1 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  have hb2 : bits 2 = 2 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  simp only [mInWinE, cost_eLet, sendsInE, pGet, mEpoch, Expr.cost, Expr.v0, hb0, hb1, hb2]
  omega

omit [DecidableEq Pt] [Zero Pt] in
theorem cost_mNoBobEpoch0E {O' : Ops ASig} {Γ} (s : Expr O' Γ (simMirT ℓ Pt))
    (p : Expr O' Γ .bool) :
    (mNoBobEpoch0E s p).cost ≤ s.cost + p.cost + 20 := by
  have hb0 : bits 0 = 1 := bits_zero
  simp only [mNoBobEpoch0E, cost_eLet, mEpoch, Expr.cost, Expr.v0, hb0]
  omega

omit [DecidableEq Pt] [Zero Pt] in
theorem cost_mNoSpkCorrE {O' : Ops ASig} {Γ} (s : Expr O' Γ (simMirT ℓ Pt))
    (p : Expr O' Γ .bool) :
    (mNoSpkCorrE s p).cost ≤ s.cost + p.cost + 25 := by
  have hb10 : bits 10 = 4 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  simp only [mNoSpkCorrE, cost_eLet, mEpoch, Expr.cost, Expr.v0, hb10]
  omega

end MirrorBookkeeping

/-! ## `GhostChain` operations and `toGhostE` -/

section GhostAndToGhost

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
  {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
  {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

private theorem ofU8_toU8_local (bs : Bytes) : ofU8 (toU8 bs) = bs := by
  simp [ofU8, toU8, List.map_map, Function.comp_def]

private theorem u8Vec_toU8_vec_local {n : ℕ} (v : List.Vector (BitVec 8) n) :
    u8Vec n (toU8 v.toList) = v := by
  rcases v with ⟨xs, hxs⟩
  apply List.Vector.eq
  dsimp only [u8Vec, CryptoVerification.E2E.fitVec]
  change List.take n (ofU8 (toU8 xs) ++ List.replicate n 0#8) = xs
  rw [ofU8_toU8_local, List.take_append_of_le_length (Nat.le_of_eq hxs.symm)]
  exact List.take_of_length_le (Nat.le_of_eq hxs)

def pkLitE {Γ : List (Ty ASig)} (pk : PublicKey) : Expr AOps Γ PK :=
  sOpPure .pkOfPbytes (sOpPure (.pbytesLit 32 (toU8 pk.bytes.toList)) .unit)

@[simp] theorem eval_pkLitE {Γ : List (Ty ASig)} (pk : PublicKey) (ρ : Env Γ) :
    (pkLitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) pk).eval ρ = pk := by
  rcases pk with ⟨v⟩
  simp [pkLitE, eval_sOpPure, AtomicPureOp.eval, u8Vec_toU8_vec_local]

@[simp] theorem cost_pkLitE {Γ : List (Ty ASig)} (pk : PublicKey) :
    (pkLitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (Γ := Γ) pk).cost = 98 := by
  have h32 : ((32 : ℕ+) : ℕ) = 32 := rfl
  have hlen : (toU8 pk.bytes.toList).length = 32 := by simp [toU8]
  simp only [pkLitE, Expr.cost, cost_sOpPure, AtomicPureOp.cost, h32, hlen]

def idKeyAtomLitE {Γ : List (Ty ASig)} (ik : IdentityKey) : Expr AOps Γ IdKey :=
  sOpPure .idKeyOfPbytes (sOpPure (.pbytesLit 32 (toU8 ik.publicKey.bytes.toList)) .unit)

@[simp] theorem eval_idKeyAtomLitE {Γ : List (Ty ASig)} (ik : IdentityKey) (ρ : Env Γ) :
    (idKeyAtomLitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) ik).eval ρ = ik := by
  rcases ik with ⟨⟨v⟩⟩
  simp [idKeyAtomLitE, eval_sOpPure, AtomicPureOp.eval, u8Vec_toU8_vec_local]

@[simp] theorem cost_idKeyAtomLitE {Γ : List (Ty ASig)} (ik : IdentityKey) :
    (idKeyAtomLitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (Γ := Γ) ik).cost = 98 := by
  have h32 : ((32 : ℕ+) : ℕ) = 32 := rfl
  have hlen : (toU8 ik.publicKey.bytes.toList).length = 32 := by simp [toU8]
  simp only [idKeyAtomLitE, Expr.cost, cost_sOpPure, AtomicPureOp.cost, h32, hlen]

def takeListE {O' : Ops ASig} {Γ : List (Ty ASig)} {t : Ty ASig} (B : ℕ)
    (xs : Expr O' Γ (.list t)) : Expr O' Γ (.list t) :=
  .mapB B xs .v0

omit [DecidableEq Pt] [Zero Pt] in
@[simp] theorem eval_takeListE {O' : Ops ASig} {Γ : List (Ty ASig)} {t : Ty ASig} (B : ℕ)
    (xs : Expr O' Γ (.list t)) (ρ : Env Γ) :
    (takeListE B xs).eval ρ = (xs.eval ρ).take B := by
  simp [takeListE, Expr.eval, Expr.v0]

omit [DecidableEq Pt] [Zero Pt] in
theorem cost_takeListE {O' : Ops ASig} {Γ : List (Ty ASig)} {t : Ty ASig} (B : ℕ)
    (xs : Expr O' Γ (.list t)) :
    (takeListE B xs).cost = xs.cost + 2 * B + 1 := by
  simp [takeListE, Expr.cost, Expr.v0]
  omega

def eraseFoldStep {α : Type} (p : α → Bool) (x : α) (acc : List α × Bool) : List α × Bool :=
  if acc.2 then (x :: acc.1, true)
  else if p x then (acc.1, true)
  else (x :: acc.1, false)

private theorem foldML_pure {ι : Type} {T : OracleSpec ι} {α β : Type} (f : α → β → β) :
    ∀ (b : β) (xs : List α),
      (ReductionDsl.foldML (m := OracleComp T) (fun x acc => pure (f x acc)) b xs) =
        pure (xs.foldl (fun acc x => f x acc) b)
  | b, [] => rfl
  | b, x :: xs => by
    simp only [ReductionDsl.foldML, pure_bind, List.foldl_cons]
    exact foldML_pure f (f x b) xs

private theorem foldl_eraseFoldStep_true {α : Type} (p : α → Bool) :
    ∀ (xs : List α) (revPfx : List α),
      (xs.foldl (fun acc x => eraseFoldStep p x acc) (revPfx, true)).1 =
        xs.reverse ++ revPfx
  | [], revPfx => rfl
  | x :: xs, revPfx => by
    rw [List.foldl_cons]
    have h0 : eraseFoldStep p x (revPfx, true) = (x :: revPfx, true) := rfl
    rw [h0, foldl_eraseFoldStep_true p xs (x :: revPfx)]
    simp [List.append_assoc]

private theorem foldl_eraseFoldStep_false {α : Type} (p : α → Bool) :
    ∀ (xs : List α) (revPfx : List α),
      (xs.foldl (fun acc x => eraseFoldStep p x acc) (revPfx, false)).1 =
        (xs.eraseP p).reverse ++ revPfx
  | [], revPfx => rfl
  | x :: xs, revPfx => by
    rw [List.foldl_cons]
    cases hp : p x with
    | true =>
      have h0 : eraseFoldStep p x (revPfx, false) = (revPfx, true) := by simp [eraseFoldStep, hp]
      rw [h0, foldl_eraseFoldStep_true p xs revPfx]
      simp [hp]
    | false =>
      have h0 : eraseFoldStep p x (revPfx, false) = (x :: revPfx, false) := by
        simp [eraseFoldStep, hp]
      rw [h0, foldl_eraseFoldStep_false p xs (x :: revPfx)]
      simp [hp, List.append_assoc]

private theorem foldl_cons_eq_rev_append {α : Type} :
    ∀ (xs acc : List α), xs.foldl (fun a x => x :: a) acc = xs.reverse ++ acc
  | [], acc => rfl
  | x :: xs, acc => by simp [foldl_cons_eq_rev_append xs (x :: acc), List.append_assoc]

private theorem foldl_cons_nil {α : Type} (xs : List α) :
    xs.foldl (fun acc x => x :: acc) [] = xs.reverse := by
  rw [foldl_cons_eq_rev_append]; simp

def eraseFirstNatC {O' : Ops ASig} {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    (B : ℕ) {Γ : List (Ty ASig)}
    (xs : Expr O' Γ (.list .nat)) (target : Expr O' Γ .nat) :
    Comp O' I' Γ (.list .nat) :=
  .bind (.ret (.pair xs target))
    (.bind
      (.foldM B (.fst .v0) (.pair .nil (.bool false))
        (.ret
          (.ite (.snd .v1)
            (.pair (.cons .v0 (.fst .v1)) (.bool true))
            (.ite (.eqN .v0 (.snd .v2))
              (.pair (.fst .v1) (.bool true))
              (.pair (.cons .v0 (.fst .v1)) (.bool false))))))
      (.foldM B (.fst .v0) .nil (.ret (.cons .v0 .v1))))

omit [DecidableEq Pt] [Zero Pt] in
theorem eraseFirstNatC_queries {O' : Ops ASig} {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    (B : ℕ) {Γ : List (Ty ASig)} (xs : Expr O' Γ (.list .nat)) (target : Expr O' Γ .nat)
    (w : I'.Tag → ℕ) (ws : I'.smp.Samp → ℕ) :
    (eraseFirstNatC I' B xs target).queries w ws = 0 := by
  simp [eraseFirstNatC, Comp.queries]

omit [DecidableEq Pt] [Zero Pt] in
theorem eraseFirstNatC_cost {O' : Ops ASig} {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    (B : ℕ) {Γ : List (Ty ASig)} (xs : Expr O' Γ (.list .nat)) (target : Expr O' Γ .nat) :
    (eraseFirstNatC I' B xs target).cost ≤ xs.cost + target.cost + 80 * B + 60 := by
  simp only [eraseFirstNatC, Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2,
    Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
  omega

omit [DecidableEq Pt] [Zero Pt] in
theorem eraseFirstNatC_eval {O' : Ops ASig} {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    (B : ℕ) {Γ : List (Ty ASig)} (xs : Expr O' Γ (.list .nat)) (target : Expr O' Γ .nat)
    (ρ : Env Γ) (hB : (xs.eval ρ).length ≤ B) :
    (eraseFirstNatC I' B xs target).eval ρ = pure ((xs.eval ρ).erase (target.eval ρ)) := by
  have ht0 : (xs.eval ρ).take B = xs.eval ρ := List.take_of_length_le hB
  let stepE : Expr O' (.nat :: .prod (.list .nat) .bool :: .prod (.list .nat) .nat :: Γ)
      (.prod (.list .nat) .bool) :=
    .ite (.snd .v1)
      (.pair (.cons .v0 (.fst .v1)) (.bool true))
      (.ite (.eqN .v0 (.snd .v2))
        (.pair (.fst .v1) (.bool true))
        (.pair (.cons .v0 (.fst .v1)) (.bool false)))
  have hbody : ∀ (x : ℕ) (acc : List ℕ × Bool),
      stepE.eval (.cons x (.cons acc (.cons (xs.eval ρ, target.eval ρ) ρ))) =
        eraseFoldStep (fun y => decide (y = target.eval ρ)) x acc := by
    intro x ⟨ac, d⟩
    cases d <;> by_cases h : x = target.eval ρ <;>
      simp [stepE, eraseFoldStep, Expr.eval, Expr.v0, Expr.v1, Expr.v2, h]
  change (do
    let p0 ← (pure (xs.eval ρ, target.eval ρ) : OracleComp T (List ℕ × ℕ))
    let r1 ← ReductionDsl.foldML (m := OracleComp T)
      (fun x acc => pure (stepE.eval (.cons x (.cons acc (.cons p0 ρ)))))
      ([], false) (p0.1.take B)
    ReductionDsl.foldML (m := OracleComp T) (fun x acc => pure (x :: acc)) [] (r1.1.take B)) = _
  simp only [pure_bind, ht0, hbody]
  rw [foldML_pure, pure_bind]
  set l0 : List ℕ := xs.eval ρ
  set tgt : ℕ := target.eval ρ
  set r1 := l0.foldl (fun acc x => eraseFoldStep (fun y => decide (y = tgt)) x acc) ([], false)
  have hr1 : r1.1 = (l0.eraseP (fun y => decide (y = tgt))).reverse := by
    simpa [r1] using foldl_eraseFoldStep_false (fun y => decide (y = tgt)) l0 []
  have hr1Len : r1.1.length ≤ B := by
    rw [hr1, List.length_reverse]
    exact List.length_eraseP_le.trans hB
  rw [List.take_of_length_le hr1Len, foldML_pure, foldl_cons_nil, hr1, List.reverse_reverse]
  congr 1
  rw [List.erase_eq_eraseP]
  congr 1; funext x; simp [BEq.beq, eq_comm]

def descRangeStep : ℕ × (ℕ × List ℕ) → ℕ × (ℕ × List ℕ)
  | (cnt, (cur, acc)) =>
    if cnt = 0 then (0, (cur, acc))
    else (cnt - 1, (cur + 1, cur :: acc))

private theorem iterate_descRangeStep_zero :
    ∀ (k cur : ℕ) (acc : List ℕ), (descRangeStep)^[k] (0, (cur, acc)) = (0, (cur, acc))
  | 0, _, _ => rfl
  | k + 1, cur, acc => by
    rw [Function.iterate_succ_apply]
    have h0 : descRangeStep (0, (cur, acc)) = (0, (cur, acc)) := rfl
    rw [h0]
    exact iterate_descRangeStep_zero k cur acc

private theorem iterate_descRangeStep :
    ∀ (cnt k cur : ℕ) (acc : List ℕ),
      cnt ≤ k →
      ((descRangeStep)^[k] (cnt, (cur, acc))).2.2 =
        (List.range cnt).map (fun d => cur + cnt - 1 - d) ++ acc
  | 0, k, cur, acc, _ => by simp [iterate_descRangeStep_zero]
  | _ + 1, 0, _, _, hle => by omega
  | cnt + 1, k + 1, cur, acc, hle => by
    have hk : cnt ≤ k := by omega
    rw [Function.iterate_succ_apply]
    have hstep : descRangeStep (cnt + 1, (cur, acc)) = (cnt, (cur + 1, cur :: acc)) := by
      simp [descRangeStep]
    rw [hstep, iterate_descRangeStep cnt k (cur + 1) (cur :: acc) hk]
    rw [List.range_succ, List.map_append, List.map_singleton, List.append_assoc]
    have hlast : cur + (cnt + 1) - 1 - cnt = cur := by omega
    rw [hlast, List.singleton_append]
    congr 1
    apply List.map_congr_left
    intro d hd
    have hdlt : d < cnt := List.mem_range.mp hd
    omega

private theorem range_desc_take_2000 (N hi : ℕ) (sk : List ℕ) :
    ((List.range (min N 2000)).map (fun d => hi - d) ++ sk).take 2000 =
      ((List.range N).map (fun d => hi - d) ++ sk).take 2000 := by
  by_cases hle : N ≤ 2000
  · rw [Nat.min_eq_left hle]
  · have hge : 2000 ≤ N := by omega
    rw [Nat.min_eq_right hge]
    refine List.ext_getElem (by simp; omega) fun j hj1 hj2 => ?_
    have hj : j < 2000 := by simp at hj1; omega
    have hjN : j < N := lt_of_lt_of_le hj hge
    simp [List.getElem_take, List.getElem_append_left, hjN]

/-- `GhostChain.accept g i` in `Comp` (exact for all `i : ℕ` whenever `g.skipped.length ≤ 2000`). -/
def ghostAcceptC {O' : Ops ASig} {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    {Γ : List (Ty ASig)} (gE : Expr O' Γ (ghostChainT ℓ Pt)) (iE : Expr O' Γ .nat) :
    Comp O' I' Γ (ghostChainT ℓ Pt) :=
  .bind (.ret (.pair gE iE))
    (.ite (.lt (.fst (.snd (.snd (.fst .v0)))) (.snd .v0))
      (let g0 : Expr O' _ (ghostChainT ℓ Pt) := .fst .v0
       let i0 : Expr O' _ .nat := .snd .v0
       let last0 : Expr O' _ .nat := .fst (.snd (.snd g0))
       let sk0 : Expr O' _ (.list .nat) := .snd (.snd (.snd g0))
       let mE : Expr O' _ .nat := minN (.sub (.sub i0 (.nat 1)) last0) (.nat 2000)
       .bind
         (.iter 2000 (.pair mE (.pair (.sub i0 mE) sk0))
           (.ret
             (.ite (.eqN (.fst .v0) (.nat 0))
               .v0
               (.pair (.sub (.fst .v0) (.nat 1))
                 (.pair (.add (.fst (.snd .v0)) (.nat 1))
                   (.cons (.fst (.snd .v0)) (.snd (.snd .v0))))))))
         (.ret
           (.pair (.fst (.fst .v1))
             (.pair (.fst (.snd (.fst .v1)))
               (.pair (.snd .v1) (takeListE 2000 (.snd (.snd .v0))))))))
      (.bind (eraseFirstNatC I' 2000 (.snd (.snd (.snd (.fst .v0)))) (.snd .v0))
        (.ret
          (.pair (.fst (.fst .v1))
            (.pair (.fst (.snd (.fst .v1)))
              (.pair (.fst (.snd (.snd (.fst .v1)))) .v0))))))

omit [DecidableEq Pt] [Zero Pt] in
theorem ghostAcceptC_queries {O' : Ops ASig} {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    {Γ : List (Ty ASig)} (gE : Expr O' Γ (ghostChainT ℓ Pt)) (iE : Expr O' Γ .nat)
    (w : I'.Tag → ℕ) (ws : I'.smp.Samp → ℕ) :
    (ghostAcceptC I' gE iE).queries w ws = 0 := by
  simp [ghostAcceptC, Comp.queries, eraseFirstNatC_queries]

omit [DecidableEq Pt] [Zero Pt] in
theorem ghostAcceptC_cost {O' : Ops ASig} {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    {Γ : List (Ty ASig)} (gE : Expr O' Γ (ghostChainT ℓ Pt)) (iE : Expr O' Γ .nat) :
    (ghostAcceptC I' gE iE).cost ≤ gE.cost + iE.cost + 250000 := by
  have hb0 : bits 0 = 1 := bits_zero
  have hb1 : bits 1 = 1 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  have hb2k : bits 2000 = 11 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  have he := eraseFirstNatC_cost (O' := O')
    (Γ := .prod (ghostChainT ℓ Pt) .nat :: Γ) I' 2000
    (.snd (.snd (.snd (.fst .v0)))) (.snd .v0)
  simp only [Expr.cost, Expr.v0] at he
  simp only [ghostAcceptC, minN, CryptoGames.SM.leN, cost_takeListE, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, hb0, hb1, hb2k, Nat.reduceAdd, Nat.reduceMul,
    Nat.max_def, Nat.reduceLeDiff, ↓reduceIte]
  split_ifs <;> omega

omit [DecidableEq Pt] [Zero Pt] in
theorem ghostAcceptC_eval {O' : Ops ASig} {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    {Γ : List (Ty ASig)} (gE : Expr O' Γ (ghostChainT ℓ Pt)) (iE : Expr O' Γ .nat)
    (ρ : Env Γ) (g : GhostChain)
    (hg : gE.eval ρ = ghostChainEnc g) (hsk : g.skipped.length ≤ 2000) :
    (ghostAcceptC I' gE iE).eval ρ = pure (ghostChainEnc (g.accept (iE.eval ρ))) := by
  have hiter : ∀ (k : ℕ) (st : ℕ × (ℕ × List ℕ)),
      (ReductionDsl.iterM (m := OracleComp T) (fun v => pure (descRangeStep v)) k st) =
        pure ((descRangeStep)^[k] st) := by
    intro k st
    induction k generalizing st with
    | zero => rfl
    | succ k ih =>
      simp only [ReductionDsl.iterM, pure_bind, Function.iterate_succ_apply]
      exact ih (descRangeStep st)
  set i : ℕ := iE.eval ρ
  set ρ0 := Env.cons (t := .prod (ghostChainT ℓ Pt) .nat) (ghostChainEnc g, i) ρ
  unfold ghostAcceptC
  simp only [Comp.eval, Expr.eval, hg, pure_bind]
  have hcondE : (Expr.lt (.fst (.snd (.snd (.fst (Expr.v0 (O := O')))))) (.snd .v0)).eval ρ0 =
      decide (g.last < i) := rfl
  change (if (Expr.lt (.fst (.snd (.snd (.fst (Expr.v0 (O := O')))))) (.snd .v0)).eval ρ0 = true
    then _ else _) = _
  rw [hcondE]
  by_cases hlt : g.last < i
  · simp only [hlt, decide_true, ↓reduceIte, Expr.eval, minN_eval, eval_takeListE,
      ghostChainEnc, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ]
    have hbody :
        (fun v : ℕ × (ℕ × List ℕ) =>
          (pure (if decide (v.1 = 0) = true then v
           else (v.1 - 1, (v.2.1 + 1, v.2.1 :: v.2.2))) : OracleComp T (ℕ × (ℕ × List ℕ)))) =
        fun v => pure (descRangeStep v) := by
      funext ⟨c, cu, ac⟩
      by_cases hc : c = 0 <;> simp [descRangeStep, hc]
    simp only [hbody, hiter, pure_bind]
    set N : ℕ := i - 1 - g.last with hN_def
    set m : ℕ := min N 2000 with hm_def
    have hm2k : m ≤ 2000 := Nat.min_le_right _ _
    rw [iterate_descRangeStep m 2000 (i - m) g.skipped hm2k]
    unfold GhostChain.accept
    simp only [hlt, ↓reduceIte]
    congr 1
    simp only [Prod.mk.injEq, true_and]
    refine ⟨rfl, ?_⟩
    rcases Nat.eq_zero_or_pos m with hm0 | hmp
    · have hN0 : N = 0 := by omega
      rw [← hN_def, hN0]
      simp [hm0]
    · have hmN : m ≤ N := Nat.min_le_left _ _
      have hNi : N + g.last + 1 ≤ i := by omega
      have hmi : m < i := by omega
      have hmap : (List.range m).map (fun d => i - m + m - 1 - d) =
          (List.range m).map (fun d => i - 1 - d) := by
        apply List.map_congr_left
        intro d _; omega
      rw [hmap, ← hN_def]
      exact range_desc_take_2000 N (i - 1) g.skipped
  · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
    have her := eraseFirstNatC_eval (O' := O') I' 2000
      (.snd (.snd (.snd (.fst .v0)))) (.snd .v0) ρ0
      (by simpa [ρ0, ghostChainEnc, Expr.eval, Expr.v0] using hsk)
    rw [her]
    simp [ρ0, GhostChain.accept, hlt, ghostChainEnc, Expr.eval, Expr.v0, Expr.v1]

/-- `GhostChain.rejects g i` in `Expr` (exact whenever `g.skipped.length ≤ 2000`). -/
def ghostRejectsE {O' : Ops ASig} {Γ : List (Ty ASig)}
    (gE : Expr O' Γ (ghostChainT ℓ Pt)) (iE : Expr O' Γ .nat) : Expr O' Γ .bool :=
  eLet (.pair gE iE)
    (let last0 : Expr O' _ .nat := .fst (.snd (.snd (.fst .v0)))
     let sk0 : Expr O' _ (.list .nat) := .snd (.snd (.snd (.fst .v0)))
     let i0 : Expr O' _ .nat := .snd .v0
     .ite (.not (.lt last0 i0))
       (.not (.anyB 2000 sk0 (.eqN .v0 (.snd .v1))))
       (orE (.lt (.nat 25000) (.sub (.sub i0 (.nat 1)) last0))
         (.not (.lt i0 (.nat (2 ^ 32))))))

omit [DecidableEq Pt] [Zero Pt] in
theorem eval_ghostRejectsE {O' : Ops ASig} {Γ : List (Ty ASig)}
    (gE : Expr O' Γ (ghostChainT ℓ Pt)) (iE : Expr O' Γ .nat) (ρ : Env Γ) (g : GhostChain)
    (hg : gE.eval ρ = ghostChainEnc g) (hsk : g.skipped.length ≤ 2000) :
    (ghostRejectsE gE iE).eval ρ = g.rejects (iE.eval ρ) := by
  have ht : g.skipped.take 2000 = g.skipped := List.take_of_length_le hsk
  unfold ghostRejectsE GhostChain.rejects
  rw [eval_eLet]
  have h0 : (Expr.pair gE iE).eval ρ = (ghostChainEnc g, iE.eval ρ) := by simp [Expr.eval, hg]
  rw [h0]; clear h0
  set i : ℕ := iE.eval ρ
  set ρ0 := Env.cons (t := .prod (ghostChainT ℓ Pt) .nat) (ghostChainEnc g, i) ρ
  rw [ite_eval]
  have hcond : (Expr.not (.lt (.fst (.snd (.snd (.fst (Expr.v0 (O := O')))))) (.snd .v0))).eval ρ0 =
      !decide (g.last < i) := rfl
  rw [hcond]
  by_cases hle : i ≤ g.last
  · have hnotlt : ¬ (g.last < i) := by omega
    simp only [ρ0, ghostChainEnc, hle, hnotlt, decide_false, Bool.not_false, ↓reduceIte,
      Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ, ht]
    congr 1
    have hany : ∀ (xs : List ℕ), (xs.any fun x => decide (x = i)) = xs.contains i := by
      intro xs
      induction xs with
      | nil => rfl
      | cons x xs ih =>
        simp only [List.any_cons, List.contains_cons, ih]
        by_cases h : x = i
        · subst h; simp
        · have hne : (i == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
          simp [h, hne]
    exact hany g.skipped
  · have hlt : g.last < i := by omega
    simp only [ρ0, ghostChainEnc, hle, hlt, decide_true, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, orE_eval, Expr.eval, Expr.v0, Env.get_cons_zero]
    congr 1
    by_cases h : i < 4294967296
    · have h2 : ¬ (4294967296 ≤ i) := by omega
      simp [h, h2]
    · have h2 : 4294967296 ≤ i := by omega
      simp [h, h2]

omit [DecidableEq Pt] [Zero Pt] in
theorem cost_ghostRejectsE {O' : Ops ASig} {Γ : List (Ty ASig)}
    (gE : Expr O' Γ (ghostChainT ℓ Pt)) (iE : Expr O' Γ .nat) :
    (ghostRejectsE gE iE).cost ≤ gE.cost + iE.cost + 12500 := by
  have hb1 : bits 1 = 1 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  have hb25k : bits 25000 = 15 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  have hb232 : bits (2 ^ 32) = 33 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  simp only [ghostRejectsE, cost_eLet, orE, Expr.cost, Expr.v0, Expr.v1, hb1, hb25k, hb232]
  omega

def unconsList {α : Type} : List α → Option (α × List α)
  | [] => none
  | h :: tl => some (h, tl)

def unconsB {O' : Ops ASig} {Γ : List (Ty ASig)} {t : Ty ASig} (K : ℕ)
    (xs : Expr O' Γ (.list t)) : Expr O' Γ (.opt (.prod t (.list t))) :=
  .foldrB K xs .none
    (.caseOpt .v1
      (.some (.pair .v0 .nil))
      (.some (.pair .v1 (.cons (.fst .v0) (.snd .v0)))))

omit [DecidableEq Pt] [Zero Pt] in
private theorem foldr_uncons_aux {α : Type} :
    ∀ (l : List α),
      l.foldr
        (fun x (acc : Option (α × List α)) =>
          match acc with
          | none => some (x, [])
          | some p => some (x, p.1 :: p.2))
        none = unconsList l
  | [] => rfl
  | [_] => rfl
  | h :: y :: ys => by
    have ih := foldr_uncons_aux (y :: ys)
    simp only [List.foldr_cons] at ih ⊢
    rw [ih]; rfl

omit [DecidableEq Pt] [Zero Pt] in
private theorem eval_caseOpt_local {O' : Ops ASig} {Γ : List (Ty ASig)} {a b : Ty ASig}
    (e : Expr O' Γ (.opt a)) (n : Expr O' Γ b) (s : Expr O' (a :: Γ) b) (ρ : Env Γ) :
    (Expr.caseOpt e n s).eval ρ =
      match e.eval ρ with
      | none => n.eval ρ
      | some x => s.eval (.cons x ρ) := by
  simp only [Expr.eval]
  cases e.eval ρ <;> rfl

omit [DecidableEq Pt] [Zero Pt] in
@[simp] theorem eval_unconsB {O' : Ops ASig} {Γ : List (Ty ASig)} {t : Ty ASig} (K : ℕ)
    (xs : Expr O' Γ (.list t)) (ρ : Env Γ) (l : List t.denote)
    (hxs : xs.eval ρ = l) (hlen : l.length ≤ K) :
    (unconsB K xs).eval ρ = unconsList l := by
  have ht : l.take K = l := List.take_of_length_le hlen
  simp only [unconsB, Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ, hxs, ht]
  rw [← foldr_uncons_aux l]
  congr 1; funext x acc; cases acc <;> rfl

omit [DecidableEq Pt] [Zero Pt] in
@[simp] theorem cost_unconsB {O' : Ops ASig} {Γ : List (Ty ASig)} {t : Ty ASig} (K : ℕ)
    (xs : Expr O' Γ (.list t)) :
    (unconsB K xs).cost = xs.cost + 11 * K + 2 := by
  simp only [unconsB, Expr.cost, Expr.v0, Expr.v1,
    Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
  omega

/-- `pushChain cs g` in `Expr` (exact whenever `cs.length ≤ 5`). -/
def pushChainE {O' : Ops ASig} {Γ : List (Ty ASig)}
    (csE : Expr O' Γ (.list (ghostChainT ℓ Pt))) (gE : Expr O' Γ (ghostChainT ℓ Pt)) :
    Expr O' Γ (.list (ghostChainT ℓ Pt)) :=
  eLet (.pair csE gE)
    (let cs0 : Expr O' _ (.list (ghostChainT ℓ Pt)) := .fst .v0
     let g0 : Expr O' _ (ghostChainT ℓ Pt) := .snd .v0
     let cs1 := Expr.foldrB 5 cs0 (.cons g0 .nil) (.cons .v0 .v1)
     .ite (.lt (.nat 4) (.len cs0)) (.caseOpt (unconsB 6 cs1) .nil (.snd .v0)) cs1)

omit [DecidableEq Pt] [Zero Pt] in
theorem eval_pushChainE {O' : Ops ASig} {Γ : List (Ty ASig)}
    (csE : Expr O' Γ (.list (ghostChainT ℓ Pt))) (gE : Expr O' Γ (ghostChainT ℓ Pt))
    (ρ : Env Γ) (cs : List GhostChain) (g : GhostChain)
    (hcs : csE.eval ρ = cs.map ghostChainEnc) (hlen : cs.length ≤ 5)
    (hg : gE.eval ρ = ghostChainEnc g) :
    (pushChainE csE gE).eval ρ = (pushChain cs g).map ghostChainEnc := by
  have ht : (cs.map (ghostChainEnc (ℓ := ℓ) (Pt := Pt))).take 5 = cs.map ghostChainEnc :=
    List.take_of_length_le (by simpa using hlen)
  have hconsFold : ∀ (xs : List (ghostChainT ℓ Pt).denote) (y : (ghostChainT ℓ Pt).denote),
      xs.foldr (fun x acc => x :: acc) [y] = xs ++ [y] := by
    intro xs y; induction xs with | nil => rfl | cons _ xs ih => simp [ih]
  dsimp only [pushChainE]
  rw [eval_eLet]
  have hp : (Expr.pair csE gE).eval ρ = (cs.map ghostChainEnc, ghostChainEnc g) := by
    simp [Expr.eval, hcs, hg]
  rw [hp]; clear hp
  set ρ1 := Env.cons (t := .prod (.list (ghostChainT ℓ Pt)) (ghostChainT ℓ Pt))
    (cs.map (ghostChainEnc (ℓ := ℓ) (Pt := Pt)), ghostChainEnc (ℓ := ℓ) (Pt := Pt) g) ρ
  have hcs1Eval :
      (Expr.foldrB (O := O') 5 (.fst .v0) (.cons (.snd .v0) .nil) (.cons .v0 .v1)).eval ρ1 =
        cs.map ghostChainEnc ++ [ghostChainEnc g] := by
    simp [ρ1, Expr.eval, Expr.v0, Expr.v1, ht, hconsFold]
  have hunc := eval_unconsB (O' := O') 6
    (Expr.foldrB 5 (.fst .v0) (.cons (.snd .v0) .nil) (.cons .v0 .v1)) ρ1
    (cs.map ghostChainEnc ++ [ghostChainEnc g]) hcs1Eval (by simp; omega)
  rw [ite_eval]
  have hcond : (Expr.lt (.nat 4) (.len (.fst (Expr.v0 (O := O'))))).eval ρ1 =
      decide (4 < cs.length) := by
    simp [ρ1, Expr.eval, Expr.v0]
  rw [hcond]
  unfold pushChain
  by_cases h4 : 4 < cs.length
  · have h5 : cs.length = 5 := by omega
    simp only [h4, decide_true, ↓reduceIte]
    rw [eval_caseOpt_local, hunc]
    rcases cs with _ | ⟨c0, csTail⟩
    · simp at h5
    · have hcs4 : csTail.length = 4 := by simp at h5; omega
      simp [unconsList, hcs4, Expr.eval, Expr.v0, List.map_append]
  · have hsub : (cs ++ [g]).length - 5 = 0 := by simp; omega
    simp only [h4, decide_false, Bool.false_eq_true, ↓reduceIte, hcs1Eval, hsub, List.drop,
      List.map_append, List.map_cons, List.map_nil]

omit [DecidableEq Pt] [Zero Pt] in
theorem cost_pushChainE {O' : Ops ASig} {Γ : List (Ty ASig)}
    (csE : Expr O' Γ (.list (ghostChainT ℓ Pt))) (gE : Expr O' Γ (ghostChainT ℓ Pt)) :
    (pushChainE csE gE).cost ≤ csE.cost + gE.cost + 150 := by
  have hb4 : bits 4 = 3 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  simp only [pushChainE, cost_eLet, cost_unconsB, Expr.cost, Expr.v0, Expr.v1, hb4]
  omega

/-- `(s.chains Q).findIdx? (fun g => g.key == some rk)` in `Expr` for `cs.length ≤ 5`. -/
def findChainIdxE {Γ : List (Ty ASig)}
    (csE : Expr AOps Γ (.list (ghostChainT ℓ Pt))) (rkE : Expr AOps Γ PK) :
    Expr AOps Γ (.opt .nat) :=
  eLet (.pair csE rkE)
    (.fst
      (Expr.foldrB 5 (.fst .v0) (.pair .none (.nat 0))
        (.pair
          (.caseOpt (.fst .v0)
            (eMapOpt (.fst .v1) (.add .v0 (.nat 1)))
            (.ite (sOpPure .pkEq (.pair .v0 (.snd .v3)))
              (.some (.nat 0))
              (eMapOpt (.fst .v2) (.add .v0 (.nat 1)))))
          (.add (.snd .v1) (.nat 1)))))

omit [DecidableEq Pt] [Zero Pt] in
private theorem foldr_findIdx_aux {α : Type} (p : α → Bool) :
    ∀ (xs : List α),
      (xs.foldr
        (fun x (acc : Option ℕ × ℕ) =>
          (if p x then some 0 else acc.1.map (· + 1), acc.2 + 1))
        (none, 0)).1 = xs.findIdx? p
  | [] => rfl
  | x :: xs => by
    have ih := foldr_findIdx_aux p xs
    rw [List.findIdx?_cons]
    dsimp only [List.foldr]
    rw [ih]

theorem eval_findChainIdxE {Γ : List (Ty ASig)}
    (csE : Expr AOps Γ (.list (ghostChainT ℓ Pt))) (rkE : Expr AOps Γ PK)
    (ρ : Env Γ) (cs : List GhostChain)
    (hcs : csE.eval ρ = cs.map ghostChainEnc) (hlen : cs.length ≤ 5) :
    (findChainIdxE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) csE rkE).eval ρ =
      cs.findIdx? (fun g => g.key == some (rkE.eval ρ)) := by
  have hstep : ∀ (xs : List GhostChain),
      (xs.map (ghostChainEnc (ℓ := ℓ) (Pt := Pt))).foldr
        (fun g (acc : Option ℕ × ℕ) =>
          (match g.1 with
           | none => acc.1.map (· + 1)
           | some pk => if (pk == rkE.eval ρ) = true then some 0 else acc.1.map (· + 1),
           acc.2 + 1))
        (none, 0) =
      xs.foldr
        (fun g (acc : Option ℕ × ℕ) =>
          (if g.key == some (rkE.eval ρ) then some 0 else acc.1.map (· + 1), acc.2 + 1))
        (none, 0) := by
    intro xs
    induction xs with
    | nil => rfl
    | cons g rest ih =>
      simp only [List.map_cons, List.foldr_cons]
      rw [ih]
      rcases g with ⟨_ | pk, ep, last, sk⟩
      · simp [ghostChainEnc]
      · by_cases h : pk = rkE.eval ρ <;> simp [ghostChainEnc, h]
  have ht : (cs.map (ghostChainEnc (ℓ := ℓ) (Pt := Pt))).take 5 = cs.map ghostChainEnc :=
    List.take_of_length_le (by simpa using hlen)
  simp only [findChainIdxE, eval_eLet, eval_eMapOpt, Expr.eval, hcs,
    eval_sOpPure, AtomicPureOp.eval,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Env.get_cons_zero, Env.get_cons_succ, ht]
  rw [← foldr_findIdx_aux (fun g => g.key == some (rkE.eval ρ)) cs, ← hstep cs]
  congr 2; funext g acc; cases g.1 <;> rfl

theorem cost_findChainIdxE {Γ : List (Ty ASig)}
    (csE : Expr AOps Γ (.list (ghostChainT ℓ Pt))) (rkE : Expr AOps Γ PK) :
    (findChainIdxE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) csE rkE).cost ≤ csE.cost + rkE.cost + 500 := by
  have hb0 : bits 0 = 1 := bits_zero
  have hb1 : bits 1 = 1 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  simp only [findChainIdxE, cost_eLet, cost_eMapOpt,
    Expr.cost, cost_sOpPure, AtomicPureOp.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, hb0, hb1,
    Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
  omega

def listGetDConstE {O' : Ops ASig} {t : Ty ASig} :
    (fuel : ℕ) → {Γ : List (Ty ASig)} →
      Expr O' Γ (.list t) → Expr O' Γ .nat → Expr O' Γ t → Expr O' Γ t
  | 0, _, _, _, defVal => defVal
  | fuel + 1, _, xs, idx, defVal =>
    eLet (.pair xs (.pair idx defVal))
      (.caseOpt (unconsB (fuel + 1) (.fst .v0))
        (.snd (.snd .v0))
        (.ite (.eqN (.fst (.snd .v1)) (.nat 0))
          (.fst .v0)
          (listGetDConstE fuel (.snd .v0) (.sub (.fst (.snd .v1)) (.nat 1)) (.snd (.snd .v1)))))

omit [DecidableEq Pt] [Zero Pt] in
theorem eval_listGetDConstE {O' : Ops ASig} {t : Ty ASig} :
    ∀ (fuel : ℕ) {Γ : List (Ty ASig)} (xs : Expr O' Γ (.list t)) (idx : Expr O' Γ .nat)
      (defVal : Expr O' Γ t) (ρ : Env Γ),
      (xs.eval ρ).length ≤ fuel →
      (listGetDConstE fuel xs idx defVal).eval ρ = (xs.eval ρ).getD (idx.eval ρ) (defVal.eval ρ)
  | 0, _, xs, idx, defVal, ρ, hlen => by
    cases hxs : (xs.eval ρ : List t.denote) with
    | nil =>
      rw [listGetDConstE]
      cases idx.eval ρ <;> rfl
    | cons _ _ => rw [hxs] at hlen; simp at hlen
  | fuel + 1, _, xs, idx, defVal, ρ, hlen => by
    rw [listGetDConstE, eval_eLet]
    have hp : (Expr.pair xs (.pair idx defVal)).eval ρ =
        (xs.eval ρ, (idx.eval ρ, defVal.eval ρ)) := rfl
    rw [hp, eval_caseOpt_local]; clear hp
    cases hxs : (xs.eval ρ : List t.denote) with
    | nil =>
      have hunc := eval_unconsB (O' := O') (fuel + 1) (.fst .v0)
        (Env.cons (t := .prod (.list t) (.prod .nat t)) ([], (idx.eval ρ, defVal.eval ρ)) ρ)
        [] rfl (by simp)
      rw [hunc]
      cases idx.eval ρ <;> rfl
    | cons hd tl =>
      have htl : tl.length ≤ fuel := by rw [hxs] at hlen; simp at hlen; omega
      have hunc := eval_unconsB (O' := O') (fuel + 1) (.fst .v0)
        (Env.cons (t := .prod (.list t) (.prod .nat t)) (hd :: tl, (idx.eval ρ, defVal.eval ρ)) ρ)
        (hd :: tl) rfl (by rw [hxs] at hlen; exact hlen)
      rw [hunc]
      dsimp only [unconsList]
      rw [ite_eval]
      cases hidx : (idx.eval ρ : ℕ) with
      | zero =>
        have hc :
            (Expr.eqN (.fst (.snd (Expr.v1 (O := O')))) (.nat 0)).eval
              (Env.cons (t := .prod t (.list t)) (hd, tl)
                (Env.cons (t := .prod (.list t) (.prod .nat t)) (hd :: tl, (0, defVal.eval ρ)) ρ)) =
              true := rfl
        rw [hc]; rfl
      | succ k =>
        have hc :
            (Expr.eqN (.fst (.snd (Expr.v1 (O := O')))) (.nat 0)).eval
              (Env.cons (t := .prod t (.list t)) (hd, tl)
                (Env.cons (t := .prod (.list t) (.prod .nat t)) (hd :: tl, (k + 1, defVal.eval ρ)) ρ)) =
              false := rfl
        rw [hc]
        simp only [Bool.false_eq_true, ↓reduceIte]
        have ih := eval_listGetDConstE (O' := O') fuel (.snd .v0) (.sub (.fst (.snd .v1)) (.nat 1))
          (.snd (.snd .v1))
          (Env.cons (t := .prod t (.list t)) (hd, tl)
            (Env.cons (t := .prod (.list t) (.prod .nat t)) (hd :: tl, (k + 1, defVal.eval ρ)) ρ))
          (by simpa [Expr.eval, Expr.v0] using htl)
        rw [ih]; rfl

def getChainDE {O' : Ops ASig} {Γ : List (Ty ASig)}
    (csE : Expr O' Γ (.list (ghostChainT ℓ Pt))) (ciE : Expr O' Γ .nat) :
    Expr O' Γ (ghostChainT ℓ Pt) :=
  listGetDConstE 5 csE ciE (.pair .none (.pair (.nat 0) (.pair (.nat 0) .nil)))

omit [DecidableEq Pt] [Zero Pt] in
theorem eval_getChainDE {O' : Ops ASig} {Γ : List (Ty ASig)}
    (csE : Expr O' Γ (.list (ghostChainT ℓ Pt))) (ciE : Expr O' Γ .nat)
    (ρ : Env Γ) (cs : List GhostChain)
    (hcs : csE.eval ρ = cs.map ghostChainEnc) (hlen : cs.length ≤ 5) :
    (getChainDE csE ciE).eval ρ = ghostChainEnc (cs.getD (ciE.eval ρ) ⟨none, 0, 0, []⟩) := by
  have h1 := eval_listGetDConstE (O' := O') 5 csE ciE
    (.pair .none (.pair (.nat 0) (.pair (.nat 0) .nil))) ρ (by simpa [hcs] using hlen)
  rw [getChainDE, h1, hcs]
  have hgetD_map : ∀ (xs : List GhostChain) (k : ℕ),
      (xs.map (ghostChainEnc (ℓ := ℓ) (Pt := Pt))).getD k (none, (0, (0, []))) =
        ghostChainEnc (xs.getD k ⟨none, 0, 0, []⟩) := by
    intro xs k
    induction xs generalizing k with
    | nil => rfl
    | cons x xs ih =>
      cases k with
      | zero => rfl
      | succ k => exact ih k
  exact hgetD_map cs (ciE.eval ρ)

omit [DecidableEq Pt] [Zero Pt] in
theorem cost_getChainDE {O' : Ops ASig} {Γ : List (Ty ASig)}
    (csE : Expr O' Γ (.list (ghostChainT ℓ Pt))) (ciE : Expr O' Γ .nat) :
    (getChainDE csE ciE).cost ≤ csE.cost + ciE.cost + 400 := by
  have hb0 : bits 0 = 1 := bits_zero
  have hb1 : bits 1 = 1 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  simp only [getChainDE, listGetDConstE, cost_eLet, cost_unconsB, Expr.cost,
    Expr.v0, Expr.v1, hb0, hb1]
  omega

def listSetAtConstE {O' : Ops ASig} {t : Ty ASig} :
    (fuel : ℕ) → {Γ : List (Ty ASig)} →
      Expr O' Γ (.list t) → Expr O' Γ .nat → Expr O' Γ t → Expr O' Γ (.list t)
  | 0, _, xs, _, _ => xs
  | fuel + 1, _, xs, idx, val =>
    eLet (.pair xs (.pair idx val))
      (.caseOpt (unconsB (fuel + 1) (.fst .v0))
        .nil
        (.ite (.eqN (.fst (.snd .v1)) (.nat 0))
          (.cons (.snd (.snd .v1)) (.snd .v0))
          (.cons (.fst .v0) (listSetAtConstE fuel (.snd .v0) (.sub (.fst (.snd .v1)) (.nat 1))
            (.snd (.snd .v1))))))

omit [DecidableEq Pt] [Zero Pt] in
theorem eval_listSetAtConstE {O' : Ops ASig} {t : Ty ASig} :
    ∀ (fuel : ℕ) {Γ : List (Ty ASig)} (xs : Expr O' Γ (.list t)) (idx : Expr O' Γ .nat)
      (val : Expr O' Γ t) (ρ : Env Γ),
      (xs.eval ρ).length ≤ fuel →
      (listSetAtConstE fuel xs idx val).eval ρ = (xs.eval ρ).set (idx.eval ρ) (val.eval ρ)
  | 0, _, xs, idx, val, ρ, hlen => by
    cases hxs : (xs.eval ρ : List t.denote) with
    | nil =>
      rw [listSetAtConstE, hxs]
      cases idx.eval ρ <;> rfl
    | cons _ _ => rw [hxs] at hlen; simp at hlen
  | fuel + 1, _, xs, idx, val, ρ, hlen => by
    rw [listSetAtConstE, eval_eLet]
    have hp : (Expr.pair xs (.pair idx val)).eval ρ =
        (xs.eval ρ, (idx.eval ρ, val.eval ρ)) := rfl
    rw [hp, eval_caseOpt_local]; clear hp
    cases hxs : (xs.eval ρ : List t.denote) with
    | nil =>
      have hunc := eval_unconsB (O' := O') (fuel + 1) (.fst .v0)
        (Env.cons (t := .prod (.list t) (.prod .nat t)) ([], (idx.eval ρ, val.eval ρ)) ρ)
        [] rfl (by simp)
      rw [hunc]
      cases idx.eval ρ <;> rfl
    | cons hd tl =>
      have htl : tl.length ≤ fuel := by rw [hxs] at hlen; simp at hlen; omega
      have hunc := eval_unconsB (O' := O') (fuel + 1) (.fst .v0)
        (Env.cons (t := .prod (.list t) (.prod .nat t)) (hd :: tl, (idx.eval ρ, val.eval ρ)) ρ)
        (hd :: tl) rfl (by rw [hxs] at hlen; exact hlen)
      rw [hunc]
      dsimp only [unconsList]
      rw [ite_eval]
      cases hidx : (idx.eval ρ : ℕ) with
      | zero =>
        have hc :
            (Expr.eqN (.fst (.snd (Expr.v1 (O := O')))) (.nat 0)).eval
              (Env.cons (t := .prod t (.list t)) (hd, tl)
                (Env.cons (t := .prod (.list t) (.prod .nat t)) (hd :: tl, (0, val.eval ρ)) ρ)) =
              true := rfl
        rw [hc]; rfl
      | succ k =>
        have hc :
            (Expr.eqN (.fst (.snd (Expr.v1 (O := O')))) (.nat 0)).eval
              (Env.cons (t := .prod t (.list t)) (hd, tl)
                (Env.cons (t := .prod (.list t) (.prod .nat t)) (hd :: tl, (k + 1, val.eval ρ)) ρ)) =
              false := rfl
        rw [hc]
        simp only [Bool.false_eq_true, ↓reduceIte]
        have ih := eval_listSetAtConstE (O' := O') fuel (.snd .v0) (.sub (.fst (.snd .v1)) (.nat 1))
          (.snd (.snd .v1))
          (Env.cons (t := .prod t (.list t)) (hd, tl)
            (Env.cons (t := .prod (.list t) (.prod .nat t)) (hd :: tl, (k + 1, val.eval ρ)) ρ))
          (by simpa [Expr.eval, Expr.v0] using htl)
        change hd :: (listSetAtConstE fuel (.snd .v0) (.sub (.fst (.snd .v1)) (.nat 1))
          (.snd (.snd .v1))).eval _ = hd :: tl.set k (val.eval ρ)
        rw [ih]; rfl

/-- `cs.modify ci (·.accept i)` in `Comp` for `cs.length ≤ 5` and `skipped.length ≤ 2000`. -/
def modifyChainAcceptC {O' : Ops ASig} {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    {Γ : List (Ty ASig)} (csE : Expr O' Γ (.list (ghostChainT ℓ Pt)))
    (ciE : Expr O' Γ .nat) (iE : Expr O' Γ .nat) :
    Comp O' I' Γ (.list (ghostChainT ℓ Pt)) :=
  .bind (.ret (.pair csE (.pair ciE iE)))
    (.bind (ghostAcceptC I' (getChainDE (.fst .v0) (.fst (.snd .v0))) (.snd (.snd .v0)))
      (.ret (listSetAtConstE 5 (.fst .v1) (.fst (.snd .v1)) .v0)))

omit [DecidableEq Pt] [Zero Pt] in
theorem modifyChainAcceptC_queries {O' : Ops ASig} {ι : Type} {T : OracleSpec ι}
    (I' : Iface ASig T) {Γ : List (Ty ASig)}
    (csE : Expr O' Γ (.list (ghostChainT ℓ Pt))) (ciE iE : Expr O' Γ .nat)
    (w : I'.Tag → ℕ) (ws : I'.smp.Samp → ℕ) :
    (modifyChainAcceptC I' csE ciE iE).queries w ws = 0 := by
  simp [modifyChainAcceptC, Comp.queries, ghostAcceptC_queries]

omit [DecidableEq Pt] [Zero Pt] in
theorem modifyChainAcceptC_cost {O' : Ops ASig} {ι : Type} {T : OracleSpec ι}
    (I' : Iface ASig T) {Γ : List (Ty ASig)}
    (csE : Expr O' Γ (.list (ghostChainT ℓ Pt))) (ciE iE : Expr O' Γ .nat) :
    (modifyChainAcceptC I' csE ciE iE).cost ≤ csE.cost + ciE.cost + iE.cost + 252000 := by
  let Γ1 := .prod (.list (ghostChainT ℓ Pt)) (.prod .nat .nat) :: Γ
  have hg := cost_getChainDE (O' := O')
    (.fst (.v0 : Expr O' Γ1 (.prod (.list (ghostChainT ℓ Pt)) (.prod .nat .nat))))
    (.fst (.snd (.v0 : Expr O' Γ1 (.prod (.list (ghostChainT ℓ Pt)) (.prod .nat .nat)))))
  have ha := ghostAcceptC_cost (O' := O') I'
    (getChainDE (.fst (.v0 : Expr O' Γ1 (.prod (.list (ghostChainT ℓ Pt)) (.prod .nat .nat))))
      (.fst (.snd (.v0 : Expr O' Γ1 (.prod (.list (ghostChainT ℓ Pt)) (.prod .nat .nat))))))
    (.snd (.snd (.v0 : Expr O' Γ1 (.prod (.list (ghostChainT ℓ Pt)) (.prod .nat .nat)))))
  have hb0 : bits 0 = 1 := bits_zero
  have hb1 : bits 1 = 1 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  simp only [Expr.cost, Expr.v0] at hg ha
  simp only [modifyChainAcceptC, listSetAtConstE, cost_eLet, cost_unconsB, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, hb0, hb1, Nat.reduceMul, Nat.max_def, Nat.reduceLeDiff, ↓reduceIte,
    Nat.reduceAdd]
  omega

omit [DecidableEq Pt] [Zero Pt] in
private theorem set_getD_eq_modify {α : Type} (f : α → α) (d : α) :
    ∀ (xs : List α) (k : ℕ), xs.set k (f (xs.getD k d)) = xs.modify k f
  | [], 0 => rfl
  | [], _ + 1 => rfl
  | _ :: _, 0 => rfl
  | x :: xs, k + 1 => congrArg (x :: ·) (set_getD_eq_modify f d xs k)

omit [DecidableEq Pt] [Zero Pt] in
theorem modifyChainAcceptC_eval {O' : Ops ASig} {ι : Type} {T : OracleSpec ι}
    (I' : Iface ASig T) {Γ : List (Ty ASig)}
    (csE : Expr O' Γ (.list (ghostChainT ℓ Pt))) (ciE iE : Expr O' Γ .nat)
    (ρ : Env Γ) (cs : List GhostChain)
    (hcs : csE.eval ρ = cs.map ghostChainEnc) (hlen : cs.length ≤ 5)
    (hsk : ∀ g ∈ cs, g.skipped.length ≤ 2000) :
    (modifyChainAcceptC I' csE ciE iE).eval ρ =
      pure ((cs.modify (ciE.eval ρ) (·.accept (iE.eval ρ))).map ghostChainEnc) := by
  set ci : ℕ := ciE.eval ρ
  set i : ℕ := iE.eval ρ
  have hgetD_sk : (cs.getD ci ⟨none, 0, 0, []⟩).skipped.length ≤ 2000 := by
    have hmem_or : ∀ (xs : List GhostChain) (k : ℕ),
        xs.getD k ⟨none, 0, 0, []⟩ ∈ xs ∨ xs.getD k ⟨none, 0, 0, []⟩ = ⟨none, 0, 0, []⟩ := by
      intro xs k
      induction xs generalizing k with
      | nil => exact Or.inr rfl
      | cons x xs ih =>
        cases k with
        | zero => exact Or.inl List.mem_cons_self
        | succ k =>
          rcases ih k with hm | hd
          · exact Or.inl (List.mem_cons_of_mem _ hm)
          · exact Or.inr hd
    rcases hmem_or cs ci with hm | hd
    · exact hsk _ hm
    · rw [hd]; simp
  simp only [modifyChainAcceptC, Comp.eval, Expr.eval, hcs, pure_bind]
  set ρ1 := Env.cons (t := .prod (.list (ghostChainT ℓ Pt)) (.prod .nat .nat))
    (cs.map (ghostChainEnc (ℓ := ℓ) (Pt := Pt)), (ci, i)) ρ
  have hgd := eval_getChainDE (O' := O') (.fst .v0) (.fst (.snd .v0)) ρ1 cs rfl hlen
  have hac := ghostAcceptC_eval (O' := O') I'
    (getChainDE (.fst .v0) (.fst (.snd .v0))) (.snd (.snd .v0)) ρ1
    (cs.getD ci ⟨none, 0, 0, []⟩) hgd hgetD_sk
  rw [hac, pure_bind]
  set g' := (cs.getD ci ⟨none, 0, 0, []⟩).accept i
  have hset := eval_listSetAtConstE (O' := O') 5 (.fst .v1) (.fst (.snd .v1)) .v0
    (.cons (ghostChainEnc g') ρ1) (by simpa [ρ1, Expr.eval, Expr.v1] using hlen)
  change pure ((listSetAtConstE 5 (.fst .v1) (.fst (.snd .v1)) .v0).eval (.cons (ghostChainEnc g') ρ1)) = _
  rw [hset]
  dsimp only [ρ1, Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ]
  rw [← List.map_set, set_getD_eq_modify (·.accept i) ⟨none, 0, 0, []⟩ cs ci]

def anyChainKeyNoneE {O' : Ops ASig} {Γ : List (Ty ASig)}
    (csE : Expr O' Γ (.list (ghostChainT ℓ Pt))) : Expr O' Γ .bool :=
  .anyB 5 csE (.caseOpt (.fst .v0) (.bool true) (.bool false))

omit [DecidableEq Pt] [Zero Pt] in
theorem eval_anyChainKeyNoneE {O' : Ops ASig} {Γ : List (Ty ASig)}
    (csE : Expr O' Γ (.list (ghostChainT ℓ Pt))) (ρ : Env Γ) (cs : List GhostChain)
    (hcs : csE.eval ρ = cs.map ghostChainEnc) (hlen : cs.length ≤ 5) :
    (anyChainKeyNoneE csE).eval ρ = cs.any (·.key.isNone) := by
  have ht : (cs.map (ghostChainEnc (ℓ := ℓ) (Pt := Pt))).take 5 = cs.map ghostChainEnc :=
    List.take_of_length_le (by simpa using hlen)
  simp only [anyChainKeyNoneE, Expr.eval, hcs, ht, any_map_eq]
  congr 1; funext g; rcases g with ⟨_ | _, _, _, _⟩ <;> rfl

omit [DecidableEq Pt] [Zero Pt] in
theorem cost_anyChainKeyNoneE {O' : Ops ASig} {Γ : List (Ty ASig)}
    (csE : Expr O' Γ (.list (ghostChainT ℓ Pt))) :
    (anyChainKeyNoneE csE).cost ≤ csE.cost + 40 := by
  simp only [anyChainKeyNoneE, Expr.cost, Expr.v0,
    Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
  omega

def revealSpkChainsE {O' : Ops ASig} {Γ : List (Ty ASig)}
    (csE : Expr O' Γ (.list (ghostChainT ℓ Pt))) (pkE : Expr O' Γ PK) :
    Expr O' Γ (.list (ghostChainT ℓ Pt)) :=
  eLet (.pair csE pkE)
    (.mapB 5 (.fst .v0)
      (.caseOpt (.fst .v0)
        (.pair (.some (.snd .v1)) (.snd .v0))
        .v1))

omit [DecidableEq Pt] [Zero Pt] in
theorem eval_revealSpkChainsE {O' : Ops ASig} {Γ : List (Ty ASig)}
    (csE : Expr O' Γ (.list (ghostChainT ℓ Pt))) (pkE : Expr O' Γ PK)
    (ρ : Env Γ) (cs : List GhostChain)
    (hcs : csE.eval ρ = cs.map ghostChainEnc) (hlen : cs.length ≤ 5) :
    (revealSpkChainsE csE pkE).eval ρ =
      (cs.map fun g => if g.key.isNone then { g with key := some (pkE.eval ρ) } else g).map
        ghostChainEnc := by
  have ht : (cs.map (ghostChainEnc (ℓ := ℓ) (Pt := Pt))).take 5 = cs.map ghostChainEnc :=
    List.take_of_length_le (by simpa using hlen)
  simp only [revealSpkChainsE, eval_eLet, Expr.eval, Expr.v0, Expr.v1,
    Env.get_cons_zero, Env.get_cons_succ, hcs, ht, List.map_map]
  congr 1; funext g; rcases g with ⟨_ | _, _, _, _⟩ <;> rfl

omit [DecidableEq Pt] [Zero Pt] in
theorem cost_revealSpkChainsE {O' : Ops ASig} {Γ : List (Ty ASig)}
    (csE : Expr O' Γ (.list (ghostChainT ℓ Pt))) (pkE : Expr O' Γ PK) :
    (revealSpkChainsE csE pkE).cost ≤ csE.cost + pkE.cost + 60 := by
  simp only [revealSpkChainsE, cost_eLet, Expr.cost, Expr.v0, Expr.v1,
    Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
  omega

omit [DecidableEq Pt] [Zero Pt] in
theorem fig8StTruncSk_eq_self (B_skip : ℕ) (st : Fig8St Pt)
    (hsk : ∀ t v, st.vR t = some v → v.skippedKeys.length ≤ B_skip) :
    fig8StTruncSk B_skip st = st := by
  rcases st with ⟨idP, rk, vs?, vr, γ, cur?, tc⟩
  simp only [fig8StTruncSk]
  congr 1
  funext t
  cases ht : vr t with
  | none => rfl
  | some v =>
    rcases v with ⟨ck, li, sk⟩
    simp [List.take_of_length_le (hsk t _ ht)]


private theorem foldr_tset_lookup (xs : List (ℕ × BitVec 256)) (j : ℕ) :
    (xs.foldr (fun kv (tbl : ℕ → Option (BitVec 256)) k =>
      if k = kv.1 then some kv.2 else tbl k) (fun _ => none)) j = xs.lookup j := by
  induction xs with
  | nil => rfl
  | cons kv xs ih =>
    rcases kv with ⟨k, v⟩
    simp only [List.foldr_cons, List.lookup_cons]
    by_cases hjk : j = k
    · subst hjk; simp
    · have hbeq : (j == k) = false := beq_eq_false_iff_ne.mpr hjk
      simp [hjk, hbeq, ih]

def toGhostScE {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt))) :
    Expr AOps Γ (.opt drSenderChainT) :=
  eLet stE
    (.caseSum (.fst (.snd (.snd (.snd (.snd .v0)))))
      .none
      (.caseOpt
        (.fst (.snd (.snd .v1)))
        .none
        (.some
          (.pair
            (sOpSym .sessionKeyPairGen .v1)
            (.pair (.fst .v0) (sOpPure .u32OfNat (.snd .v0)))))))

theorem cost_toGhostScE {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt))) :
    (toGhostScE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) stE).cost ≤ stE.cost + 400 := by
  simp only [toGhostScE, cost_eLet, Expr.cost, cost_sOpPure, cost_sOpSym,
    AtomicPureOp.cost, AtomicSymOp.cost, Expr.v0, Expr.v1,
    Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
  omega

def toGhostRcSomeE (B_skip : ℕ) {Γ : List (Ty ASig)}
    (gE : Expr AOps Γ (ghostChainT ℓ Pt))
    (vrE : Expr AOps Γ (fsRecvStT (ℓ := ℓ) (Pt := Pt))) :
    Expr AOps Γ drRecvChainT :=
  eLet (.pair gE vrE)
    (eLet
      (Expr.foldrB B_skip (.snd (.snd (.snd .v0))) (.tconst .none)
        (.tset .v1 (.fst .v0) (.some (.snd .v0))))
      (.pair
        (.caseOpt (.fst (.fst .v1)) (pkLitE dummyKey) .v0)
        (.pair
          (.some (.pair (.fst (.snd .v1)) (sOpPure .u32OfNat (.fst (.snd (.snd .v1))))))
          (Expr.foldrB 2000 (.snd (.snd (.snd (.fst .v1)))) .nil
            (.caseOpt (.tget .v2 .v0)
              .v1
              (.cons
                (.pair .v0 (sOpPure .u32OfNat (.sub .v1 (.nat 1))))
                .v2))))))

theorem cost_toGhostRcSomeE (B_skip : ℕ) {Γ : List (Ty ASig)}
    (gE : Expr AOps Γ (ghostChainT ℓ Pt))
    (vrE : Expr AOps Γ (fsRecvStT (ℓ := ℓ) (Pt := Pt))) :
    (toGhostRcSomeE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) B_skip gE vrE).cost ≤
      gE.cost + vrE.cost + 160 * B_skip + 200000 := by
  have hb1 : bits 1 = 1 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  simp only [toGhostRcSomeE, cost_eLet, Expr.cost, cost_sOpPure, cost_pkLitE,
    AtomicPureOp.cost, Expr.v0, Expr.v1, Expr.v2, hb1,
    Nat.reduceMul, Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
  omega

theorem eval_toGhostRcSomeE (B_skip : ℕ) {Γ : List (Ty ASig)}
    (gE : Expr AOps Γ (ghostChainT ℓ Pt))
    (vrE : Expr AOps Γ (fsRecvStT (ℓ := ℓ) (Pt := Pt)))
    {ρ : Env Γ} (g : GhostChain)
    (vr : CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
    (hg : gE.eval ρ = ghostChainEnc g) (hvr : vrE.eval ρ = fsRecvStV vr)
    (hsk : g.skipped.length ≤ 2000) :
    (toGhostRcSomeE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) B_skip gE vrE).eval ρ =
      (g.key.getD dummyKey,
        (some (vr.chainKey, BitVec.ofNat 32 vr.lastIndex),
          g.skipped.filterMap fun j =>
            ((vr.skippedKeys.take B_skip).lookup j).map fun mk =>
              (mk, BitVec.ofNat 32 (j - 1)))) := by
  rcases g with ⟨pk?, ep, last, sk⟩
  dsimp only at hsk
  rcases vr with ⟨vck, vli, vsk⟩
  have htSk : sk.take 2000 = sk := List.take_of_length_le hsk
  rw [toGhostRcSomeE, eval_eLet]
  have hp : (Expr.pair gE vrE).eval ρ = (ghostChainEnc ⟨pk?, ep, last, sk⟩, fsRecvStV ⟨vck, vli, vsk⟩) := by
    simp [Expr.eval, hg, hvr]
  rw [hp]; clear hp hg hvr
  rw [eval_eLet]
  simp only [ghostChainEnc, fsRecvStV, Expr.eval, eval_sOpPure, eval_pkLitE,
    AtomicPureOp.eval, Expr.v0, Expr.v1, Expr.v2,
    Env.get_cons_zero, Env.get_cons_succ, htSk]
  cases pk? <;> dsimp only [Option.getD]
  all_goals
    congr 1; congr 1
    have htbl :
        ((vsk.take B_skip).foldr
          (fun kv (tbl : ℕ → Option (BitVec 256)) k =>
            if k = kv.1 then some kv.2 else tbl k)
          (fun _ => none)) =
        fun j => (vsk.take B_skip).lookup j := by
      funext j; exact foldr_tset_lookup (vsk.take B_skip) j
    clear hsk htSk
    rw [htbl]
    dsimp only []
    induction sk with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.foldr_cons, List.filterMap_cons, ih]
      cases List.lookup x (List.take B_skip vsk) <;> rfl

def toGhostRcsE (B_skip : ℕ) {Γ : List (Ty ASig)}
    (csE : Expr AOps Γ (.list (ghostChainT ℓ Pt)))
    (stE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt))) :
    Expr AOps Γ (.list drRecvChainT) :=
  eLet (.pair csE stE)
    (.mapB 5 (.fst .v0)
      (let g0 : Expr AOps _ (ghostChainT ℓ Pt) := .v0
       let srkE : Expr AOps _ PK := .caseOpt (.fst g0) (pkLitE dummyKey) .v0
       let vrAtEp := Expr.tget (.fst (.snd (.snd (.snd (.snd .v1))))) (.fst (.snd g0))
       .caseOpt vrAtEp
         (.pair srkE (.pair .none .nil))
         (toGhostRcSomeE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
           (decT := decT) (lam := lam) B_skip .v1 .v0)))

theorem cost_toGhostRcsE (B_skip : ℕ) {Γ : List (Ty ASig)}
    (csE : Expr AOps Γ (.list (ghostChainT ℓ Pt)))
    (stE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt))) :
    (toGhostRcsE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) B_skip csE stE).cost ≤
      csE.cost + stE.cost + 1000 * B_skip + 1500000 := by
  have hsome := cost_toGhostRcSomeE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) B_skip
    (Γ := fsRecvStT (ℓ := ℓ) (Pt := Pt) :: ghostChainT ℓ Pt ::
      .prod (.list (ghostChainT ℓ Pt)) (fig8StT (ℓ := ℓ) (Pt := Pt)) :: Γ) .v1 .v0
  simp only [Expr.cost, Expr.v0, Expr.v1] at hsome
  simp only [toGhostRcsE, cost_eLet, Expr.cost, cost_pkLitE, Expr.v0, Expr.v1,
    Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
  split_ifs <;> omega

def toGhostTailE (B_skip : ℕ) {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ (simBaseT ℓ Pt)) (qE : Expr AOps Γ .bool)
    (stE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt))) :
    Expr AOps Γ (.prod .bool (.prod .nat (.prod (.list .nat)
      (.prod (.opt drSenderChainT)
        (.prod (.list drRecvChainT) (B 32)))))) :=
  eLet (.pair sE (.pair qE stE))
    (let s0 : Expr AOps _ (simBaseT ℓ Pt) := .fst .v0
     let q0 : Expr AOps _ .bool := .fst (.snd .v0)
     let st0 : Expr AOps _ (fig8StT (ℓ := ℓ) (Pt := Pt)) := .snd (.snd .v0)
     let pq0 := pGet (.fst (.snd s0)) q0
     let unackA0 := Expr.fst (.snd (.snd (.snd s0)))
     let cs0 := pGet (.fst (.snd (.snd (.snd (.snd (.snd s0)))))) q0
     let ep0 := pGet (mEpoch (.fst s0)) q0
     let pendE := Expr.and (.not q0) unackA0
     let cEpsE := Expr.mapB 5 cs0 (.fst (.snd .v0))
     let scE := toGhostScE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
       (decT := decT) (lam := lam) st0
     let rcsE := toGhostRcsE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
       (decT := decT) (lam := lam) B_skip cs0 st0
     .pair pendE (.pair ep0 (.pair cEpsE (.pair scE (.pair rcsE pq0)))))

theorem cost_toGhostTailE (B_skip : ℕ) {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ (simBaseT ℓ Pt)) (qE : Expr AOps Γ .bool)
    (stE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt))) :
    (toGhostTailE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) B_skip sE qE stE).cost ≤
      sE.cost + qE.cost + stE.cost + 1000 * B_skip + 1550000 := by
  have hsc := cost_toGhostScE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam)
    (Γ := .prod (simBaseT ℓ Pt) (.prod .bool (fig8StT (ℓ := ℓ) (Pt := Pt))) :: Γ)
    (.snd (.snd .v0))
  have hrcs := cost_toGhostRcsE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) B_skip
    (Γ := .prod (simBaseT ℓ Pt) (.prod .bool (fig8StT (ℓ := ℓ) (Pt := Pt))) :: Γ)
    (pGet (.fst (.snd (.snd (.snd (.snd (.snd (.fst .v0))))))) (.fst (.snd .v0)))
    (.snd (.snd .v0))
  simp only [pGet, Expr.cost, Expr.v0, Nat.reduceAdd] at hsc hrcs
  simp only [toGhostTailE, pGet, mEpoch, cost_eLet, Expr.cost, Expr.v0,
    Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
  omega

/-- `toGhost s Q st` in `Expr` over `AOps` using `.tbl`-accelerated `skippedKeys` lookup. -/
def toGhostE (idA idB : IdentityKey) (B_skip : ℕ) {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ (simBaseT ℓ Pt)) (qE : Expr AOps Γ .bool)
    (stE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt))) :
    Expr AOps Γ GhostStT :=
  eLet (.pair sE (.pair qE stE))
    (let s0 : Expr AOps _ (simBaseT ℓ Pt) := .fst .v0
     let q0 : Expr AOps _ .bool := .fst (.snd .v0)
     let st0 : Expr AOps _ (fig8StT (ℓ := ℓ) (Pt := Pt)) := .snd (.snd .v0)
     let pn0 := pGet (.fst (.snd (.snd s0))) q0
     let rk0 := Expr.fst (.snd st0)
     let idLoc := Expr.ite q0 (idKeyAtomLitE idB) (idKeyAtomLitE idA)
     let idRem := Expr.some (.ite q0 (idKeyAtomLitE idA) (idKeyAtomLitE idB))
     let verE := sOpPure (.u32Lit (BitVec.ofNat 32 currentVersion.toNat)) .unit
     let tailE := toGhostTailE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
       (decT := decT) (lam := lam) B_skip s0 q0 st0
     sOpPure .ghostStateJoin
       (.pair q0 (.pair verE (.pair idLoc (.pair idRem (.pair rk0 (.pair pn0 tailE)))))))

theorem cost_toGhostE (idA idB : IdentityKey) (B_skip : ℕ) {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ (simBaseT ℓ Pt)) (qE : Expr AOps Γ .bool)
    (stE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt))) :
    (toGhostE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB B_skip sE qE stE).cost ≤
      sE.cost + qE.cost + stE.cost + 1000 * B_skip + 1600000 := by
  have htail := cost_toGhostTailE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) B_skip
    (Γ := .prod (simBaseT ℓ Pt) (.prod .bool (fig8StT (ℓ := ℓ) (Pt := Pt))) :: Γ)
    (.fst .v0) (.fst (.snd .v0)) (.snd (.snd .v0))
  simp only [Expr.cost, Expr.v0] at htail
  simp only [toGhostE, pGet, cost_eLet, Expr.cost, cost_sOpPure, cost_idKeyAtomLitE,
    AtomicPureOp.cost, Expr.v0, Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
  omega

theorem eval_toGhostE (idA idB : IdentityKey) (B_skip : ℕ) {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ (simBaseT ℓ Pt)) (qE : Expr AOps Γ .bool)
    (stE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt)))
    (ρ : Env Γ) (s : SimState Bytes Pt ℓ) (Q : Party) (st : Fig8St Pt)
    (hs : sE.eval ρ = simBaseEnc s) (hq : qE.eval ρ = partyEnc Q)
    (hst : stE.eval ρ = fig8StV st)
    (hcs : (s.chains Q).length ≤ 5)
    (hsk : ∀ g ∈ s.chains Q, g.skipped.length ≤ 2000) :
    (toGhostE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB B_skip sE qE stE).eval ρ =
      toGhost (P := paramsV1 C K idA idB) s Q (fig8StTruncSk B_skip st) := by
  have htCs : ((s.chains Q).map (ghostChainEnc (ℓ := ℓ) (Pt := Pt))).take 5 =
      (s.chains Q).map ghostChainEnc :=
    List.take_of_length_le (by simpa using hcs)
  have hpriv : ∀ (x : BitVec 256),
      keyToBytesVec32 (bytesToKey32 (KeyPair.generate C x).privateKey.bytes.toList) =
        (KeyPair.generate C x).privateKey.bytes := by
    intro x
    rcases (KeyPair.generate C x).privateKey.bytes with ⟨xs, hxs⟩
    apply List.Vector.eq
    simp [keyToBytesVec32,
      Computational.Proofs.ReductionDsl.Fig8Atomic.keyToBytes32_bytesToKey32 xs hxs]
  have hAA : (Party.A == Party.A) = true := rfl
  have hBA : (Party.B == Party.A) = false := rfl
  rw [toGhostE, eval_eLet]
  have hp : (Expr.pair sE (.pair qE stE)).eval ρ =
      (simBaseEnc s, (partyEnc Q, fig8StV st)) := by
    simp [Expr.eval, hs, hq, hst]
  rw [hp]; clear hp hs hq hst
  rw [eval_sOpPure]
  dsimp only [AtomicPureOp.eval, ghostJoinEval]
  unfold toGhost fig8StTruncSk
  cases Q <;>
  · simp only [toGhostTailE, toGhostScE, toGhostRcsE, eval_eLet,
      partyEnc, boolToParty, Party.other, hAA, hBA, simBaseEnc, simMirEnc, fig8StV, pGet, mEpoch,
      Expr.eval, eval_sOpPure, eval_sOpSym, AtomicPureOp.eval, AtomicSymOp.eval,
      eval_idKeyAtomLitE, eval_pkLitE,
      Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ,
      Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true,
      Bool.true_and, Bool.false_and,
      paramsV1, CryptoVerification.E2E.paramsIdsWithSpqr]
    congr 1
    · congr 1
      · rcases st.γ with h | x <;> rcases st.vS with _ | ⟨ck, li⟩
        · rfl
        · rfl
        · rfl
        · simp only [ckaStV, fsSendStV, Option.map_some, hpriv]
      · rw [htCs, List.map_map, List.take_of_length_le (by simp [hcs]), List.map_map]
        apply List.map_congr_left
        intro g hgMem
        dsimp only [Function.comp_def]
        have hgSk : g.skipped.length ≤ 2000 := hsk g hgMem
        cases hvr : st.vR g.epoch with
        | none =>
          have h1 : (ghostChainEnc (ℓ := ℓ) (Pt := Pt) g).2.1 = g.epoch := rfl
          rw [h1, hvr]
          rcases g with ⟨_ | pk, ep, last, sk⟩ <;> simp [ghostChainEnc, Option.getD]
        | some vr =>
          have h1 : (ghostChainEnc (ℓ := ℓ) (Pt := Pt) g).2.1 = g.epoch := rfl
          rw [h1, hvr]
          dsimp only [Option.map]
          rw [eval_toGhostRcSomeE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam) B_skip
            (Expr.var Var.zero.succ) (Expr.var Var.zero) g vr rfl rfl hgSk]
          dsimp only []
          congr 1
          rw [List.map_filterMap]
          apply List.filterMap_congr
          intro j _
          cases (vr.skippedKeys.take B_skip).lookup j <;> rfl
    · rw [List.take_of_length_le (by simp [hcs]), List.map_map]
      rfl

end GhostAndToGhost

/-! ## Operator lift from `atomicFig8Ops` -/

section LiftFig8Ops

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
  {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
  {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "FOps" => atomicFig8Ops ℓ Pt C Dh encPt encT lam
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

/-- Operator description-bit cost induced on `atomicFig8Ops` by `atomicSessionOpDescBits`. -/
def atomicFig8OpDescBits : (atomicFig8Ops ℓ Pt C Dh encPt encT lam).Op → ℕ
  | .inl (.inl o) => atomicPureOpDescBits o + 4
  | .inl (.inr (.inl _)) => 8 + 5
  | .inl (.inr (.inr o)) => atomicSymOpDescBits o + 5
  | .inr _ => 8 + 3

/-- Embed any `atomicFig8Ops` expression into `atomicSessionOps` with identical `.cost` and `.eval`. -/
def liftFig8Expr : {Γ : List (Ty ASig)} → {a : Ty ASig} → Expr FOps Γ a → Expr AOps Γ a
  | _, _, .var v => .var v
  | _, _, .letE e body => .letE (liftFig8Expr e) (liftFig8Expr body)
  | _, _, .unit => .unit
  | _, _, .bool b => .bool b
  | _, _, .not e => .not (liftFig8Expr e)
  | _, _, .and e₁ e₂ => .and (liftFig8Expr e₁) (liftFig8Expr e₂)
  | _, _, .ite c t e => .ite (liftFig8Expr c) (liftFig8Expr t) (liftFig8Expr e)
  | _, _, .nat n => .nat n
  | _, _, .add e₁ e₂ => .add (liftFig8Expr e₁) (liftFig8Expr e₂)
  | _, _, .sub e₁ e₂ => .sub (liftFig8Expr e₁) (liftFig8Expr e₂)
  | _, _, .mulK k e => .mulK k (liftFig8Expr e)
  | _, _, .divK k e => .divK k (liftFig8Expr e)
  | _, _, .modK k e => .modK k (liftFig8Expr e)
  | _, _, .eqN e₁ e₂ => .eqN (liftFig8Expr e₁) (liftFig8Expr e₂)
  | _, _, .lt e₁ e₂ => .lt (liftFig8Expr e₁) (liftFig8Expr e₂)
  | _, _, .pair e₁ e₂ => .pair (liftFig8Expr e₁) (liftFig8Expr e₂)
  | _, _, .fst e => .fst (liftFig8Expr e)
  | _, _, .snd e => .snd (liftFig8Expr e)
  | _, _, .inl e => .inl (liftFig8Expr e)
  | _, _, .inr e => .inr (liftFig8Expr e)
  | _, _, .caseSum s l r => .caseSum (liftFig8Expr s) (liftFig8Expr l) (liftFig8Expr r)
  | _, _, .none => .none
  | _, _, .some e => .some (liftFig8Expr e)
  | _, _, .caseOpt o n s => .caseOpt (liftFig8Expr o) (liftFig8Expr n) (liftFig8Expr s)
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons (liftFig8Expr h) (liftFig8Expr t)
  | _, _, .len xs => .len (liftFig8Expr xs)
  | _, _, .appendL B xs ys => .appendL B (liftFig8Expr xs) (liftFig8Expr ys)
  | _, _, .take n xs => .take (liftFig8Expr n) (liftFig8Expr xs)
  | _, _, .mapB B xs f => .mapB B (liftFig8Expr xs) (liftFig8Expr f)
  | _, _, .findB B xs p => .findB B (liftFig8Expr xs) (liftFig8Expr p)
  | _, _, .anyB B xs p => .anyB B (liftFig8Expr xs) (liftFig8Expr p)
  | _, _, .foldrB B xs init step =>
      .foldrB B (liftFig8Expr xs) (liftFig8Expr init) (liftFig8Expr step)
  | _, _, .tconst d => .tconst (liftFig8Expr d)
  | _, _, .tget tbl k => .tget (liftFig8Expr tbl) (liftFig8Expr k)
  | _, _, .tset tbl k v => .tset (liftFig8Expr tbl) (liftFig8Expr k) (liftFig8Expr v)
  | _, _, .op o a => .op (Sum.inl (Sum.inl o)) (liftFig8Expr a)

@[simp] theorem liftFig8Expr_cost :
    ∀ {Γ : List (Ty ASig)} {a : Ty ASig} (e : Expr FOps Γ a),
      (liftFig8Expr (K := K) (decT := decT) e).cost = e.cost
  | _, _, .var _ => rfl
  | _, _, .letE e body => by
      dsimp only [liftFig8Expr, Expr.cost]
      rw [liftFig8Expr_cost e, liftFig8Expr_cost body]
  | _, _, .unit => rfl
  | _, _, .bool _ => rfl
  | _, _, .not e => by dsimp only [liftFig8Expr, Expr.cost]; rw [liftFig8Expr_cost e]
  | _, _, .and e₁ e₂ => by
      dsimp only [liftFig8Expr, Expr.cost]; rw [liftFig8Expr_cost e₁, liftFig8Expr_cost e₂]
  | _, _, .ite c t e => by
      dsimp only [liftFig8Expr, Expr.cost]
      rw [liftFig8Expr_cost c, liftFig8Expr_cost t, liftFig8Expr_cost e]
  | _, _, .nat _ => rfl
  | _, _, .add e₁ e₂ => by
      dsimp only [liftFig8Expr, Expr.cost]; rw [liftFig8Expr_cost e₁, liftFig8Expr_cost e₂]
  | _, _, .sub e₁ e₂ => by
      dsimp only [liftFig8Expr, Expr.cost]; rw [liftFig8Expr_cost e₁, liftFig8Expr_cost e₂]
  | _, _, .mulK _ e => by dsimp only [liftFig8Expr, Expr.cost]; rw [liftFig8Expr_cost e]
  | _, _, .divK _ e => by dsimp only [liftFig8Expr, Expr.cost]; rw [liftFig8Expr_cost e]
  | _, _, .modK _ e => by dsimp only [liftFig8Expr, Expr.cost]; rw [liftFig8Expr_cost e]
  | _, _, .eqN e₁ e₂ => by
      dsimp only [liftFig8Expr, Expr.cost]; rw [liftFig8Expr_cost e₁, liftFig8Expr_cost e₂]
  | _, _, .lt e₁ e₂ => by
      dsimp only [liftFig8Expr, Expr.cost]; rw [liftFig8Expr_cost e₁, liftFig8Expr_cost e₂]
  | _, _, .pair e₁ e₂ => by
      dsimp only [liftFig8Expr, Expr.cost]; rw [liftFig8Expr_cost e₁, liftFig8Expr_cost e₂]
  | _, _, .fst e => by dsimp only [liftFig8Expr, Expr.cost]; rw [liftFig8Expr_cost e]
  | _, _, .snd e => by dsimp only [liftFig8Expr, Expr.cost]; rw [liftFig8Expr_cost e]
  | _, _, .inl e => by dsimp only [liftFig8Expr, Expr.cost]; rw [liftFig8Expr_cost e]
  | _, _, .inr e => by dsimp only [liftFig8Expr, Expr.cost]; rw [liftFig8Expr_cost e]
  | _, _, .caseSum s l r => by
      dsimp only [liftFig8Expr, Expr.cost]
      rw [liftFig8Expr_cost s, liftFig8Expr_cost l, liftFig8Expr_cost r]
  | _, _, .none => by dsimp only [liftFig8Expr, Expr.cost]
  | _, _, .some e => by dsimp only [liftFig8Expr, Expr.cost]; rw [liftFig8Expr_cost e]
  | _, _, .caseOpt o n s => by
      dsimp only [liftFig8Expr, Expr.cost]
      rw [liftFig8Expr_cost o, liftFig8Expr_cost n, liftFig8Expr_cost s]
  | _, _, .nil => by dsimp only [liftFig8Expr, Expr.cost]
  | _, _, .cons h t => by
      dsimp only [liftFig8Expr, Expr.cost]; rw [liftFig8Expr_cost h, liftFig8Expr_cost t]
  | _, _, .len xs => by dsimp only [liftFig8Expr, Expr.cost]; rw [liftFig8Expr_cost xs]
  | _, _, .appendL _ xs ys => by
      dsimp only [liftFig8Expr, Expr.cost]; rw [liftFig8Expr_cost xs, liftFig8Expr_cost ys]
  | _, _, .take n xs => by
      dsimp only [liftFig8Expr, Expr.cost]; rw [liftFig8Expr_cost n, liftFig8Expr_cost xs]
  | _, _, .mapB _ xs f => by
      dsimp only [liftFig8Expr, Expr.cost]; rw [liftFig8Expr_cost xs, liftFig8Expr_cost f]
  | _, _, .findB _ xs p => by
      dsimp only [liftFig8Expr, Expr.cost]; rw [liftFig8Expr_cost xs, liftFig8Expr_cost p]
  | _, _, .anyB _ xs p => by
      dsimp only [liftFig8Expr, Expr.cost]; rw [liftFig8Expr_cost xs, liftFig8Expr_cost p]
  | _, _, .foldrB _ xs init step => by
      dsimp only [liftFig8Expr, Expr.cost]
      rw [liftFig8Expr_cost xs, liftFig8Expr_cost init, liftFig8Expr_cost step]
  | _, _, .tconst d => by dsimp only [liftFig8Expr, Expr.cost]; rw [liftFig8Expr_cost d]
  | _, _, .tget tbl k => by
      dsimp only [liftFig8Expr, Expr.cost]; rw [liftFig8Expr_cost tbl, liftFig8Expr_cost k]
  | _, _, .tset tbl k v => by
      dsimp only [liftFig8Expr, Expr.cost]
      rw [liftFig8Expr_cost tbl, liftFig8Expr_cost k, liftFig8Expr_cost v]
  | _, _, .op o a => by
      change (liftFig8Expr a).cost +
          (atomicFig8Ops ℓ Pt C Dh encPt encT lam).cost o =
        a.cost + (atomicFig8Ops ℓ Pt C Dh encPt encT lam).cost o
      rw [liftFig8Expr_cost a]

@[simp] theorem liftFig8Expr_eval :
    ∀ {Γ : List (Ty ASig)} {a : Ty ASig} (e : Expr FOps Γ a) (ρ : Env Γ),
      (liftFig8Expr (K := K) (decT := decT) e).eval ρ = e.eval ρ
  | _, _, .var _, _ => rfl
  | _, _, .letE e body, ρ => by
      dsimp only [liftFig8Expr, Expr.eval]
      rw [liftFig8Expr_eval e ρ, liftFig8Expr_eval body]
  | _, _, .unit, _ => rfl
  | _, _, .bool _, _ => rfl
  | _, _, .not e, ρ => by dsimp only [liftFig8Expr, Expr.eval]; rw [liftFig8Expr_eval e ρ]
  | _, _, .and e₁ e₂, ρ => by
      dsimp only [liftFig8Expr, Expr.eval]
      rw [liftFig8Expr_eval e₁ ρ, liftFig8Expr_eval e₂ ρ]
  | _, _, .ite c t e, ρ => by
      dsimp only [liftFig8Expr, Expr.eval]
      rw [liftFig8Expr_eval c ρ, liftFig8Expr_eval t ρ, liftFig8Expr_eval e ρ]
  | _, _, .nat _, _ => rfl
  | _, _, .add e₁ e₂, ρ => by
      dsimp only [liftFig8Expr, Expr.eval]
      rw [liftFig8Expr_eval e₁ ρ, liftFig8Expr_eval e₂ ρ]
  | _, _, .sub e₁ e₂, ρ => by
      dsimp only [liftFig8Expr, Expr.eval]
      rw [liftFig8Expr_eval e₁ ρ, liftFig8Expr_eval e₂ ρ]
  | _, _, .mulK _ e, ρ => by dsimp only [liftFig8Expr, Expr.eval]; rw [liftFig8Expr_eval e ρ]
  | _, _, .divK _ e, ρ => by dsimp only [liftFig8Expr, Expr.eval]; rw [liftFig8Expr_eval e ρ]
  | _, _, .modK _ e, ρ => by dsimp only [liftFig8Expr, Expr.eval]; rw [liftFig8Expr_eval e ρ]
  | _, _, .eqN e₁ e₂, ρ => by
      dsimp only [liftFig8Expr, Expr.eval]
      rw [liftFig8Expr_eval e₁ ρ, liftFig8Expr_eval e₂ ρ]
  | _, _, .lt e₁ e₂, ρ => by
      dsimp only [liftFig8Expr, Expr.eval]
      rw [liftFig8Expr_eval e₁ ρ, liftFig8Expr_eval e₂ ρ]
  | _, _, .pair e₁ e₂, ρ => by
      dsimp only [liftFig8Expr, Expr.eval]
      rw [liftFig8Expr_eval e₁ ρ, liftFig8Expr_eval e₂ ρ]
  | _, _, .fst e, ρ => by dsimp only [liftFig8Expr, Expr.eval]; rw [liftFig8Expr_eval e ρ]
  | _, _, .snd e, ρ => by dsimp only [liftFig8Expr, Expr.eval]; rw [liftFig8Expr_eval e ρ]
  | _, _, .inl e, ρ => by dsimp only [liftFig8Expr, Expr.eval]; rw [liftFig8Expr_eval e ρ]
  | _, _, .inr e, ρ => by dsimp only [liftFig8Expr, Expr.eval]; rw [liftFig8Expr_eval e ρ]
  | _, _, .caseSum s l r, ρ => by
      dsimp only [liftFig8Expr, Expr.eval]
      rw [liftFig8Expr_eval s ρ]
      cases s.eval ρ with
      | inl x => exact liftFig8Expr_eval l (.cons x ρ)
      | inr y => exact liftFig8Expr_eval r (.cons y ρ)
  | _, _, .none, _ => by dsimp only [liftFig8Expr, Expr.eval]
  | _, _, .some e, ρ => by dsimp only [liftFig8Expr, Expr.eval]; rw [liftFig8Expr_eval e ρ]
  | _, _, .caseOpt o n s, ρ => by
      dsimp only [liftFig8Expr, Expr.eval]
      rw [liftFig8Expr_eval o ρ]
      cases o.eval ρ with
      | none => exact liftFig8Expr_eval n ρ
      | some x => exact liftFig8Expr_eval s (.cons x ρ)
  | _, _, .nil, _ => by dsimp only [liftFig8Expr, Expr.eval]
  | _, _, .cons h t, ρ => by
      dsimp only [liftFig8Expr, Expr.eval]
      rw [liftFig8Expr_eval h ρ, liftFig8Expr_eval t ρ]
  | _, _, .len xs, ρ => by dsimp only [liftFig8Expr, Expr.eval]; rw [liftFig8Expr_eval xs ρ]
  | _, _, .appendL _ xs ys, ρ => by
      dsimp only [liftFig8Expr, Expr.eval]
      rw [liftFig8Expr_eval xs ρ, liftFig8Expr_eval ys ρ]
  | _, _, .take n xs, ρ => by
      dsimp only [liftFig8Expr, Expr.eval]
      rw [liftFig8Expr_eval n ρ, liftFig8Expr_eval xs ρ]
  | _, _, .mapB _ xs f, ρ => by
      dsimp only [liftFig8Expr, Expr.eval]
      rw [liftFig8Expr_eval xs ρ]
      congr 1; funext x; exact liftFig8Expr_eval f (.cons x ρ)
  | _, _, .findB _ xs p, ρ => by
      dsimp only [liftFig8Expr, Expr.eval]
      rw [liftFig8Expr_eval xs ρ]
      congr 1; funext x; exact liftFig8Expr_eval p (.cons x ρ)
  | _, _, .anyB _ xs p, ρ => by
      dsimp only [liftFig8Expr, Expr.eval]
      rw [liftFig8Expr_eval xs ρ]
      congr 1; funext x; exact liftFig8Expr_eval p (.cons x ρ)
  | _, _, .foldrB _ xs init step, ρ => by
      dsimp only [liftFig8Expr, Expr.eval]
      rw [liftFig8Expr_eval xs ρ, liftFig8Expr_eval init ρ]
      congr 1; funext x acc; exact liftFig8Expr_eval step (.cons x (.cons acc ρ))
  | _, _, .tconst d, ρ => by
      dsimp only [liftFig8Expr, Expr.eval]
      funext k; exact liftFig8Expr_eval d ρ
  | _, _, .tget tbl k, ρ => by
      dsimp only [liftFig8Expr, Expr.eval]
      rw [liftFig8Expr_eval tbl ρ, liftFig8Expr_eval k ρ]
  | _, _, .tset tbl k v, ρ => by
      dsimp only [liftFig8Expr, Expr.eval]
      rw [liftFig8Expr_eval tbl ρ, liftFig8Expr_eval k ρ, liftFig8Expr_eval v ρ]
  | _, _, .op o a, ρ => by
      change (atomicFig8Ops ℓ Pt C Dh encPt encT lam).eval o
          ((liftFig8Expr a).eval ρ) =
        (atomicFig8Ops ℓ Pt C Dh encPt encT lam).eval o (a.eval ρ)
      rw [liftFig8Expr_eval a ρ]

@[simp] theorem liftFig8Expr_descBits :
    ∀ {Γ : List (Ty ASig)} {a : Ty ASig} (e : Expr FOps Γ a),
      atomicExprDescBits atomicSessionOpDescBits (liftFig8Expr (K := K) (decT := decT) e) =
        atomicExprDescBits atomicFig8OpDescBits e
  | _, _, .var _ => rfl
  | _, _, .letE e body => by
      dsimp only [liftFig8Expr, atomicExprDescBits]
      rw [liftFig8Expr_descBits e, liftFig8Expr_descBits body]
  | _, _, .unit => rfl
  | _, _, .bool _ => rfl
  | _, _, .not e => by
      dsimp only [liftFig8Expr, atomicExprDescBits]; rw [liftFig8Expr_descBits e]
  | _, _, .and e₁ e₂ => by
      dsimp only [liftFig8Expr, atomicExprDescBits]
      rw [liftFig8Expr_descBits e₁, liftFig8Expr_descBits e₂]
  | _, _, .ite c t e => by
      dsimp only [liftFig8Expr, atomicExprDescBits]
      rw [liftFig8Expr_descBits c, liftFig8Expr_descBits t, liftFig8Expr_descBits e]
  | _, _, .nat _ => rfl
  | _, _, .add e₁ e₂ => by
      dsimp only [liftFig8Expr, atomicExprDescBits]
      rw [liftFig8Expr_descBits e₁, liftFig8Expr_descBits e₂]
  | _, _, .sub e₁ e₂ => by
      dsimp only [liftFig8Expr, atomicExprDescBits]
      rw [liftFig8Expr_descBits e₁, liftFig8Expr_descBits e₂]
  | _, _, .mulK _ e => by
      dsimp only [liftFig8Expr, atomicExprDescBits]; rw [liftFig8Expr_descBits e]
  | _, _, .divK _ e => by
      dsimp only [liftFig8Expr, atomicExprDescBits]; rw [liftFig8Expr_descBits e]
  | _, _, .modK _ e => by
      dsimp only [liftFig8Expr, atomicExprDescBits]; rw [liftFig8Expr_descBits e]
  | _, _, .eqN e₁ e₂ => by
      dsimp only [liftFig8Expr, atomicExprDescBits]
      rw [liftFig8Expr_descBits e₁, liftFig8Expr_descBits e₂]
  | _, _, .lt e₁ e₂ => by
      dsimp only [liftFig8Expr, atomicExprDescBits]
      rw [liftFig8Expr_descBits e₁, liftFig8Expr_descBits e₂]
  | _, _, .pair e₁ e₂ => by
      dsimp only [liftFig8Expr, atomicExprDescBits]
      rw [liftFig8Expr_descBits e₁, liftFig8Expr_descBits e₂]
  | _, _, .fst e => by
      dsimp only [liftFig8Expr, atomicExprDescBits]; rw [liftFig8Expr_descBits e]
  | _, _, .snd e => by
      dsimp only [liftFig8Expr, atomicExprDescBits]; rw [liftFig8Expr_descBits e]
  | _, .sum _ _, .inl e => by
      dsimp only [liftFig8Expr, atomicExprDescBits]; rw [liftFig8Expr_descBits e]
  | _, .sum _ _, .inr e => by
      dsimp only [liftFig8Expr, atomicExprDescBits]; rw [liftFig8Expr_descBits e]
  | _, _, .caseSum s l r => by
      dsimp only [liftFig8Expr, atomicExprDescBits]
      rw [liftFig8Expr_descBits s, liftFig8Expr_descBits l, liftFig8Expr_descBits r]
  | _, .opt _, .none => rfl
  | _, _, .some e => by
      dsimp only [liftFig8Expr, atomicExprDescBits]; rw [liftFig8Expr_descBits e]
  | _, _, .caseOpt o n s => by
      dsimp only [liftFig8Expr, atomicExprDescBits]
      rw [liftFig8Expr_descBits o, liftFig8Expr_descBits n, liftFig8Expr_descBits s]
  | _, .list _, .nil => rfl
  | _, _, .cons h t => by
      dsimp only [liftFig8Expr, atomicExprDescBits]
      rw [liftFig8Expr_descBits h, liftFig8Expr_descBits t]
  | _, _, .len xs => by
      dsimp only [liftFig8Expr, atomicExprDescBits]; rw [liftFig8Expr_descBits xs]
  | _, _, .appendL _ xs ys => by
      dsimp only [liftFig8Expr, atomicExprDescBits]
      rw [liftFig8Expr_descBits xs, liftFig8Expr_descBits ys]
  | _, _, .take n xs => by
      dsimp only [liftFig8Expr, atomicExprDescBits]
      rw [liftFig8Expr_descBits n, liftFig8Expr_descBits xs]
  | _, _, .mapB _ xs f => by
      dsimp only [liftFig8Expr, atomicExprDescBits]
      rw [liftFig8Expr_descBits xs, liftFig8Expr_descBits f]
  | _, _, .findB _ xs p => by
      dsimp only [liftFig8Expr, atomicExprDescBits]
      rw [liftFig8Expr_descBits xs, liftFig8Expr_descBits p]
  | _, _, .anyB _ xs p => by
      dsimp only [liftFig8Expr, atomicExprDescBits]
      rw [liftFig8Expr_descBits xs, liftFig8Expr_descBits p]
  | _, _, .foldrB _ xs init step => by
      dsimp only [liftFig8Expr, atomicExprDescBits]
      rw [liftFig8Expr_descBits xs, liftFig8Expr_descBits init, liftFig8Expr_descBits step]
  | _, _, .tconst d => by
      dsimp only [liftFig8Expr, atomicExprDescBits]; rw [liftFig8Expr_descBits d]
  | _, _, .tget tbl k => by
      dsimp only [liftFig8Expr, atomicExprDescBits]
      rw [liftFig8Expr_descBits tbl, liftFig8Expr_descBits k]
  | _, _, .tset tbl k v => by
      dsimp only [liftFig8Expr, atomicExprDescBits]
      rw [liftFig8Expr_descBits tbl, liftFig8Expr_descBits k, liftFig8Expr_descBits v]
  | _, _, .op o a => by
      have ih := liftFig8Expr_descBits a
      have hop : atomicSessionOpDescBits (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
          (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
          (show (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam).Op from Sum.inl (Sum.inl o)) =
          atomicFig8OpDescBits o := by
        rcases o with ((o | (o | o)) | o) <;> rfl
      change atomicSessionOpDescBits
          (show (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam).Op from Sum.inl (Sum.inl o)) +
          atomicExprDescBits atomicSessionOpDescBits (liftFig8Expr a) + 6 =
        atomicFig8OpDescBits o + atomicExprDescBits atomicFig8OpDescBits a + 6
      omega

omit [DecidableEq Pt] [Zero Pt] in
theorem rename_descBits_eq {O' : Ops ASig} (opB : O'.Op → ℕ) :
    ∀ {Γ₁ Γ₂ : List (Ty ASig)} {a : Ty ASig}
      (ren : ∀ ⦃u⦄, Var Γ₁ u → Var Γ₂ u) (e : Expr O' Γ₁ a),
      (∀ u (v : Var Γ₁ u), varIdx (ren v) = varIdx v) →
      atomicExprDescBits opB (Expr.renameM ren e) = atomicExprDescBits opB e
  | _, _, _, ren, .var v, hren => by
      dsimp only [Expr.renameM, atomicExprDescBits]; rw [hren _ v]
  | _, _, _, ren, .letE e body, hren => by
      dsimp only [Expr.renameM, atomicExprDescBits]
      rw [rename_descBits_eq opB ren e hren, rename_descBits_eq opB _ body]
      intro u v; cases v with
      | zero => rfl
      | succ w => change varIdx (ren w) + 1 = varIdx w + 1; rw [hren _ w]
  | _, _, _, _, .unit, _ => rfl
  | _, _, _, _, .bool _, _ => rfl
  | _, _, _, ren, .not e, hren => by
      dsimp only [Expr.renameM, atomicExprDescBits]; rw [rename_descBits_eq opB ren e hren]
  | _, _, _, ren, .and e₁ e₂, hren => by
      dsimp only [Expr.renameM, atomicExprDescBits]
      rw [rename_descBits_eq opB ren e₁ hren, rename_descBits_eq opB ren e₂ hren]
  | _, _, _, ren, .ite c t e, hren => by
      dsimp only [Expr.renameM, atomicExprDescBits]
      rw [rename_descBits_eq opB ren c hren, rename_descBits_eq opB ren t hren,
        rename_descBits_eq opB ren e hren]
  | _, _, _, _, .nat _, _ => rfl
  | _, _, _, ren, .add e₁ e₂, hren => by
      dsimp only [Expr.renameM, atomicExprDescBits]
      rw [rename_descBits_eq opB ren e₁ hren, rename_descBits_eq opB ren e₂ hren]
  | _, _, _, ren, .sub e₁ e₂, hren => by
      dsimp only [Expr.renameM, atomicExprDescBits]
      rw [rename_descBits_eq opB ren e₁ hren, rename_descBits_eq opB ren e₂ hren]
  | _, _, _, ren, .mulK _ e, hren => by
      dsimp only [Expr.renameM, atomicExprDescBits]; rw [rename_descBits_eq opB ren e hren]
  | _, _, _, ren, .divK _ e, hren => by
      dsimp only [Expr.renameM, atomicExprDescBits]; rw [rename_descBits_eq opB ren e hren]
  | _, _, _, ren, .modK _ e, hren => by
      dsimp only [Expr.renameM, atomicExprDescBits]; rw [rename_descBits_eq opB ren e hren]
  | _, _, _, ren, .eqN e₁ e₂, hren => by
      dsimp only [Expr.renameM, atomicExprDescBits]
      rw [rename_descBits_eq opB ren e₁ hren, rename_descBits_eq opB ren e₂ hren]
  | _, _, _, ren, .lt e₁ e₂, hren => by
      dsimp only [Expr.renameM, atomicExprDescBits]
      rw [rename_descBits_eq opB ren e₁ hren, rename_descBits_eq opB ren e₂ hren]
  | _, _, _, ren, .pair e₁ e₂, hren => by
      dsimp only [Expr.renameM, atomicExprDescBits]
      rw [rename_descBits_eq opB ren e₁ hren, rename_descBits_eq opB ren e₂ hren]
  | _, _, _, ren, .fst e, hren => by
      dsimp only [Expr.renameM, atomicExprDescBits]; rw [rename_descBits_eq opB ren e hren]
  | _, _, _, ren, .snd e, hren => by
      dsimp only [Expr.renameM, atomicExprDescBits]; rw [rename_descBits_eq opB ren e hren]
  | _, _, .sum _ _, ren, .inl e, hren => by
      dsimp only [Expr.renameM, atomicExprDescBits]; rw [rename_descBits_eq opB ren e hren]
  | _, _, .sum _ _, ren, .inr e, hren => by
      dsimp only [Expr.renameM, atomicExprDescBits]; rw [rename_descBits_eq opB ren e hren]
  | _, _, _, ren, .caseSum s l r, hren => by
      dsimp only [Expr.renameM, atomicExprDescBits]
      rw [rename_descBits_eq opB ren s hren, rename_descBits_eq opB _ l, rename_descBits_eq opB _ r]
      · intro u v; cases v with
        | zero => rfl
        | succ w => change varIdx (ren w) + 1 = varIdx w + 1; rw [hren _ w]
      · intro u v; cases v with
        | zero => rfl
        | succ w => change varIdx (ren w) + 1 = varIdx w + 1; rw [hren _ w]
  | _, _, .opt _, _, .none, _ => rfl
  | _, _, _, ren, .some e, hren => by
      dsimp only [Expr.renameM, atomicExprDescBits]; rw [rename_descBits_eq opB ren e hren]
  | _, _, _, ren, .caseOpt o n s, hren => by
      dsimp only [Expr.renameM, atomicExprDescBits]
      rw [rename_descBits_eq opB ren o hren, rename_descBits_eq opB ren n hren,
        rename_descBits_eq opB _ s]
      intro u v; cases v with
      | zero => rfl
      | succ w => change varIdx (ren w) + 1 = varIdx w + 1; rw [hren _ w]
  | _, _, .list _, _, .nil, _ => rfl
  | _, _, _, ren, .cons h t, hren => by
      dsimp only [Expr.renameM, atomicExprDescBits]
      rw [rename_descBits_eq opB ren h hren, rename_descBits_eq opB ren t hren]
  | _, _, _, ren, .len xs, hren => by
      dsimp only [Expr.renameM, atomicExprDescBits]; rw [rename_descBits_eq opB ren xs hren]
  | _, _, _, ren, .appendL _ xs ys, hren => by
      dsimp only [Expr.renameM, atomicExprDescBits]
      rw [rename_descBits_eq opB ren xs hren, rename_descBits_eq opB ren ys hren]
  | _, _, _, ren, .take n xs, hren => by
      dsimp only [Expr.renameM, atomicExprDescBits]
      rw [rename_descBits_eq opB ren n hren, rename_descBits_eq opB ren xs hren]
  | _, _, _, ren, .mapB _ xs f, hren => by
      dsimp only [Expr.renameM, atomicExprDescBits]
      rw [rename_descBits_eq opB ren xs hren, rename_descBits_eq opB _ f]
      intro u v; cases v with
      | zero => rfl
      | succ w => change varIdx (ren w) + 1 = varIdx w + 1; rw [hren _ w]
  | _, _, _, ren, .findB _ xs p, hren => by
      dsimp only [Expr.renameM, atomicExprDescBits]
      rw [rename_descBits_eq opB ren xs hren, rename_descBits_eq opB _ p]
      intro u v; cases v with
      | zero => rfl
      | succ w => change varIdx (ren w) + 1 = varIdx w + 1; rw [hren _ w]
  | _, _, _, ren, .anyB _ xs p, hren => by
      dsimp only [Expr.renameM, atomicExprDescBits]
      rw [rename_descBits_eq opB ren xs hren, rename_descBits_eq opB _ p]
      intro u v; cases v with
      | zero => rfl
      | succ w => change varIdx (ren w) + 1 = varIdx w + 1; rw [hren _ w]
  | _, _, _, ren, .foldrB _ xs init step, hren => by
      dsimp only [Expr.renameM, atomicExprDescBits]
      rw [rename_descBits_eq opB ren xs hren, rename_descBits_eq opB ren init hren,
        rename_descBits_eq opB _ step]
      intro u v; cases v with
      | zero => rfl
      | succ w =>
        cases w with
        | zero => rfl
        | succ z => change varIdx (ren z) + 1 + 1 = varIdx z + 1 + 1; rw [hren _ z]
  | _, _, _, ren, .tconst d, hren => by
      dsimp only [Expr.renameM, atomicExprDescBits]; rw [rename_descBits_eq opB ren d hren]
  | _, _, _, ren, .tget tbl k, hren => by
      dsimp only [Expr.renameM, atomicExprDescBits]
      rw [rename_descBits_eq opB ren tbl hren, rename_descBits_eq opB ren k hren]
  | _, _, _, ren, .tset tbl k v, hren => by
      dsimp only [Expr.renameM, atomicExprDescBits]
      rw [rename_descBits_eq opB ren tbl hren, rename_descBits_eq opB ren k hren,
        rename_descBits_eq opB ren v hren]
  | _, _, _, ren, .op _ a, hren => by
      dsimp only [Expr.renameM, atomicExprDescBits]; rw [rename_descBits_eq opB ren a hren]

/-- Run a `Fig8Atomic` combinator `f : Expr FOps [a, .prod IdKey IdKey] b` on `arg : Expr AOps Γ a`
and literal identity keys `(idA, idB)` inside `AOps`. -/
def runFig8WithIds (idA idB : IdentityKey) {Γ : List (Ty ASig)} {a b : Ty ASig}
    (f : Expr FOps [a, .prod IdKey IdKey] b) (arg : Expr AOps Γ a) : Expr AOps Γ b :=
  eLet (.pair arg (.pair (idKeyAtomLitE idA) (idKeyAtomLitE idB)))
    (eLet (.snd .v0)
      (eLet (.fst .v1)
        (liftFig8Expr
          (Expr.renameM
            (fun ⦃_⦄ v => match v with
              | .zero => .zero
              | .succ .zero => .succ .zero)
            f))))

theorem cost_runFig8WithIds (idA idB : IdentityKey) {Γ : List (Ty ASig)} {a b : Ty ASig}
    (f : Expr FOps [a, .prod IdKey IdKey] b) (arg : Expr AOps Γ a) :
    (runFig8WithIds (K := K) (decT := decT) idA idB f arg).cost ≤ arg.cost + f.cost + 225 := by
  have hidA := cost_idKeyAtomLitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ) idA
  have hidB := cost_idKeyAtomLitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ) idB
  simp only [runFig8WithIds, cost_eLet, liftFig8Expr_cost, Expr.renameM_cost,
    Expr.cost, Expr.v0, Expr.v1]
  omega

@[simp] theorem eval_runFig8WithIds (idA idB : IdentityKey) {Γ : List (Ty ASig)} {a b : Ty ASig}
    (f : Expr FOps [a, .prod IdKey IdKey] b) (arg : Expr AOps Γ a) (ρ : Env Γ) :
    (runFig8WithIds (K := K) (decT := decT) idA idB f arg).eval ρ =
      f.eval (Env.cons (arg.eval ρ) (Env.cons (idA, idB) Env.nil)) := by
  simp only [runFig8WithIds, eval_eLet, Expr.eval, eval_idKeyAtomLitE, Expr.v0, Expr.v1,
    Env.get_cons_zero, Env.get_cons_succ, liftFig8Expr_eval]
  refine Expr.renameM_eval f ?_
  intro u v
  cases v with
  | zero => rfl
  | succ v =>
    cases v with
    | zero => rfl
    | succ v => nomatch v

theorem pkLitE_descBits_le {Γ : List (Ty ASig)} (pk : PublicKey) :
    atomicExprDescBits atomicSessionOpDescBits
      (pkLitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) (Γ := Γ) pk) ≤ 350 := by
  have h32 : ((32 : ℕ+) : ℕ) = 32 := rfl
  have hb32 : bits 32 = 6 :=
    bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  have hlen : (toU8 pk.bytes.toList).length = 32 := by simp [toU8]
  change atomicPureOpDescBits .pkOfPbytes + 4 +
      (atomicPureOpDescBits (.pbytesLit 32 (toU8 pk.bytes.toList)) + 4 + 6 + 6) + 6 ≤ 350
  dsimp only [atomicPureOpDescBits]
  rw [h32, hlen, hb32]
  omega

theorem idKeyAtomLitE_descBits_le {Γ : List (Ty ASig)} (ik : IdentityKey) :
    atomicExprDescBits atomicSessionOpDescBits
      (idKeyAtomLitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) (Γ := Γ) ik) ≤ 350 := by
  have h32 : ((32 : ℕ+) : ℕ) = 32 := rfl
  have hb32 : bits 32 = 6 :=
    bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  have hlen : (toU8 ik.publicKey.bytes.toList).length = 32 := by simp [toU8]
  change atomicPureOpDescBits .idKeyOfPbytes + 4 +
      (atomicPureOpDescBits (.pbytesLit 32 (toU8 ik.publicKey.bytes.toList)) + 4 + 6 + 6) + 6 ≤ 350
  dsimp only [atomicPureOpDescBits]
  rw [h32, hlen, hb32]
  omega

theorem descBits_runFig8WithIds (idA idB : IdentityKey) {Γ : List (Ty ASig)} {a b : Ty ASig}
    (f : Expr FOps [a, .prod IdKey IdKey] b) (arg : Expr AOps Γ a) :
    atomicExprDescBits atomicSessionOpDescBits
      (runFig8WithIds (K := K) (decT := decT) idA idB f arg) ≤
      atomicExprDescBits atomicSessionOpDescBits arg +
        atomicExprDescBits atomicFig8OpDescBits f + 1000 := by
  have hb0 : bits 0 = 1 := bits_zero
  have hb1 : bits 1 = 1 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  have hidA := idKeyAtomLitE_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ) idA
  have hidB := idKeyAtomLitE_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ) idB
  let ren0 : ∀ ⦃u : Ty ASig⦄, Var [a, .prod IdKey IdKey] u →
      Var (a :: .prod IdKey IdKey :: .prod a (.prod IdKey IdKey) :: Γ) u :=
    fun ⦃_⦄ v => match v with
      | .zero => .zero
      | .succ .zero => .succ .zero
  have hren := rename_descBits_eq atomicFig8OpDescBits ren0 f
    (by
      intro u v
      cases v with
      | zero => rfl
      | succ w => cases w with | zero => rfl | succ z => nomatch z)
  simp only [runFig8WithIds, descBits_eLet, liftFig8Expr_descBits,
    Expr.v0, Expr.v1, varIdx, atomicExprDescBits, Nat.reduceAdd, hb0, hb1]
  rw [hren]
  omega

end LiftFig8Ops


/-! ## State accessors and `descBits` bounds -/

section StateAccessorsAndDescBits

variable {ℓ : ℕ} {Pt : Type}

local notation "ASig" => atomicSig ℓ Pt

def ssMir {O' : Ops ASig} {Γ} (s : Expr O' Γ (simBaseT ℓ Pt)) : Expr O' Γ (simMirT ℓ Pt) := .fst s
def ssPq {O' : Ops ASig} {Γ} (s : Expr O' Γ (simBaseT ℓ Pt)) :
    Expr O' Γ (.prod (B 32) (B 32)) := .fst (.snd s)
def ssPn {O' : Ops ASig} {Γ} (s : Expr O' Γ (simBaseT ℓ Pt)) :
    Expr O' Γ (.prod U32 U32) := .fst (.snd (.snd s))
def ssUnackA {O' : Ops ASig} {Γ} (s : Expr O' Γ (simBaseT ℓ Pt)) : Expr O' Γ .bool :=
  .fst (.snd (.snd (.snd s)))
def ssHonest {O' : Ops ASig} {Γ} (s : Expr O' Γ (simBaseT ℓ Pt)) :
    Expr O' Γ (.list (.prod (B 32) fig8CtT)) :=
  .fst (.snd (.snd (.snd (.snd s))))
def ssChains {O' : Ops ASig} {Γ} (s : Expr O' Γ (simBaseT ℓ Pt)) :
    Expr O' Γ (.prod (.list (ghostChainT ℓ Pt)) (.list (ghostChainT ℓ Pt))) :=
  .fst (.snd (.snd (.snd (.snd (.snd s)))))
def ssAmb {O' : Ops ASig} {Γ} (s : Expr O' Γ (simBaseT ℓ Pt)) : Expr O' Γ .nat :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd s))))))
def ssStopped {O' : Ops ASig} {Γ} (s : Expr O' Γ (simBaseT ℓ Pt)) : Expr O' Γ .bool :=
  .snd (.snd (.snd (.snd (.snd (.snd (.snd s))))))

def ssMk {O' : Ops ASig} {Γ}
    (mir : Expr O' Γ (simMirT ℓ Pt))
    (pq : Expr O' Γ (.prod (B 32) (B 32)))
    (pn : Expr O' Γ (.prod U32 U32))
    (unackA : Expr O' Γ .bool)
    (honest : Expr O' Γ (.list (.prod (B 32) fig8CtT)))
    (chains : Expr O' Γ (.prod (.list (ghostChainT ℓ Pt)) (.list (ghostChainT ℓ Pt))))
    (amb : Expr O' Γ .nat)
    (stopped : Expr O' Γ .bool) : Expr O' Γ (simBaseT ℓ Pt) :=
  .pair mir (.pair pq (.pair pn (.pair unackA (.pair honest (.pair chains (.pair amb stopped))))))

def ssSetAmb {O' : Ops ASig} {Γ} (s : Expr O' Γ (simBaseT ℓ Pt)) (a : Expr O' Γ .nat) :
    Expr O' Γ (simBaseT ℓ Pt) :=
  eLet (.pair s a)
    (let s0 : Expr O' _ (simBaseT ℓ Pt) := .fst .v0
     ssMk (ssMir s0) (ssPq s0) (ssPn s0) (ssUnackA s0) (ssHonest s0) (ssChains s0)
       (.snd .v0) (ssStopped s0))

def ssSetMirWin {O' : Ops ASig} {Γ} (s : Expr O' Γ (simBaseT ℓ Pt)) : Expr O' Γ (simBaseT ℓ Pt) :=
  eLet s
    (let s0 : Expr O' _ (simBaseT ℓ Pt) := .v0
     ssMk (mSetWin (ssMir s0) (.bool true)) (ssPq s0) (ssPn s0) (ssUnackA s0)
       (ssHonest s0) (ssChains s0) (ssAmb s0) (ssStopped s0))

def ssSetMir {O' : Ops ASig} {Γ} (s : Expr O' Γ (simBaseT ℓ Pt)) (m : Expr O' Γ (simMirT ℓ Pt)) :
    Expr O' Γ (simBaseT ℓ Pt) :=
  eLet (.pair s m)
    (let s0 : Expr O' _ (simBaseT ℓ Pt) := .fst .v0
     ssMk (.snd .v0) (ssPq s0) (ssPn s0) (ssUnackA s0) (ssHonest s0) (ssChains s0)
       (ssAmb s0) (ssStopped s0))

def scBase {O' : Ops ASig} {Γ} (sC : Expr O' Γ (simFullT ℓ Pt)) : Expr O' Γ (simBaseT ℓ Pt) :=
  .fst sC
def scKept {O' : Ops ASig} {Γ} (sC : Expr O' Γ (simFullT ℓ Pt)) :
    Expr O' Γ (.prod (keptT ℓ Pt) (keptT ℓ Pt)) := .fst (.snd sC)
def scSent {O' : Ops ASig} {Γ} (sC : Expr O' Γ (simFullT ℓ Pt)) :
    Expr O' Γ (.list (sentEntryT ℓ Pt)) := .fst (.snd (.snd sC))
def scSnaps {O' : Ops ASig} {Γ} (sC : Expr O' Γ (simFullT ℓ Pt)) :
    Expr O' Γ (.list (snapT ℓ Pt)) := .snd (.snd (.snd sC))

def scMk {O' : Ops ASig} {Γ}
    (base : Expr O' Γ (simBaseT ℓ Pt))
    (kept : Expr O' Γ (.prod (keptT ℓ Pt) (keptT ℓ Pt)))
    (sent : Expr O' Γ (.list (sentEntryT ℓ Pt)))
    (snaps : Expr O' Γ (.list (snapT ℓ Pt))) : Expr O' Γ (simFullT ℓ Pt) :=
  .pair base (.pair kept (.pair sent snaps))

def scSetBase {O' : Ops ASig} {Γ} (sC : Expr O' Γ (simFullT ℓ Pt))
    (b : Expr O' Γ (simBaseT ℓ Pt)) : Expr O' Γ (simFullT ℓ Pt) :=
  eLet (.pair sC b)
    (let s0 : Expr O' _ (simFullT ℓ Pt) := .fst .v0
     scMk (.snd .v0) (scKept s0) (scSent s0) (scSnaps s0))

@[simp] theorem eval_ssSetAmb {O' : Ops ASig} {Γ} (s : Expr O' Γ (simBaseT ℓ Pt))
    (a : Expr O' Γ .nat) (ρ : Env Γ) (st : SimState Bytes Pt ℓ)
    (hs : s.eval ρ = simBaseEnc st) :
    (ssSetAmb s a).eval ρ = simBaseEnc { st with amb := a.eval ρ } := by
  simp [ssSetAmb, ssMk, ssMir, ssPq, ssPn, ssUnackA, ssHonest, ssChains, ssStopped,
    hs, simBaseEnc, Expr.eval, Expr.v0]

@[simp] theorem eval_ssSetMirWin {O' : Ops ASig} {Γ} (s : Expr O' Γ (simBaseT ℓ Pt))
    (ρ : Env Γ) (st : SimState Bytes Pt ℓ) (hs : s.eval ρ = simBaseEnc st) :
    (ssSetMirWin s).eval ρ = simBaseEnc { st with mir := { st.mir with win := true } } := by
  dsimp only [ssSetMirWin]
  rw [eval_eLet, hs]
  have hw := mSetWin_eval (O' := O') (ssMir (.v0 : Expr O' (simBaseT ℓ Pt :: Γ) _))
    (.bool true) (.cons (simBaseEnc st) ρ) st.mir rfl
  dsimp only [Expr.eval, Expr.v0] at hw
  dsimp only [ssMk, Expr.eval, Expr.v0]
  rw [hw]
  simp [ssPq, ssPn, ssUnackA, ssHonest, ssChains, ssAmb, ssStopped, simBaseEnc, Expr.eval]

@[simp] theorem eval_ssSetMir {O' : Ops ASig} {Γ} (s : Expr O' Γ (simBaseT ℓ Pt))
    (m : Expr O' Γ (simMirT ℓ Pt)) (ρ : Env Γ) (st : SimState Bytes Pt ℓ)
    (mir' : GameState Unit (Plain ℓ) Bytes)
    (hs : s.eval ρ = simBaseEnc st) (hm : m.eval ρ = simMirEnc mir') :
    (ssSetMir s m).eval ρ = simBaseEnc { st with mir := mir' } := by
  simp [ssSetMir, ssMk, ssPq, ssPn, ssUnackA, ssHonest, ssChains, ssAmb, ssStopped,
    hs, hm, simBaseEnc, Expr.eval, Expr.v0]

@[simp] theorem eval_scSetBase {O' : Ops ASig} {Γ} (sC : Expr O' Γ (simFullT ℓ Pt))
    (b : Expr O' Γ (simBaseT ℓ Pt)) (ρ : Env Γ)
    (st : LibsignalToModularSchemeSimState Bytes Pt ℓ) (b' : SimState Bytes Pt ℓ)
    (hs : sC.eval ρ = simFullEnc st) (hb : b.eval ρ = simBaseEnc b') :
    (scSetBase sC b).eval ρ = simFullEnc { st with base := b' } := by
  simp [scSetBase, scMk, scKept, scSent, scSnaps, hs, hb, simFullEnc, Expr.eval, Expr.v0]

theorem cost_ssSetAmb {O' : Ops ASig} {Γ} (s : Expr O' Γ (simBaseT ℓ Pt)) (a : Expr O' Γ .nat) :
    (ssSetAmb s a).cost ≤ s.cost + a.cost + 60 := by
  simp only [ssSetAmb, cost_eLet, ssMk, ssMir, ssPq, ssPn, ssUnackA, ssHonest, ssChains, ssStopped,
    Expr.cost, Expr.v0]
  omega

theorem cost_ssSetMirWin {O' : Ops ASig} {Γ} (s : Expr O' Γ (simBaseT ℓ Pt)) :
    (ssSetMirWin s).cost ≤ s.cost + 300 := by
  have hw := cost_mSetWin (O' := O') (ssMir (.v0 : Expr O' (simBaseT ℓ Pt :: Γ) _)) (.bool true)
  simp only [ssMir, Expr.cost, Expr.v0] at hw
  simp only [ssSetMirWin, cost_eLet, ssMk, ssMir, ssPq, ssPn, ssUnackA, ssHonest, ssChains, ssAmb,
    ssStopped, Expr.cost, Expr.v0]
  omega

theorem cost_ssSetMir {O' : Ops ASig} {Γ} (s : Expr O' Γ (simBaseT ℓ Pt))
    (m : Expr O' Γ (simMirT ℓ Pt)) :
    (ssSetMir s m).cost ≤ s.cost + m.cost + 60 := by
  simp only [ssSetMir, cost_eLet, ssMk, ssPq, ssPn, ssUnackA, ssHonest, ssChains, ssAmb, ssStopped,
    Expr.cost, Expr.v0]
  omega

theorem cost_scSetBase {O' : Ops ASig} {Γ} (sC : Expr O' Γ (simFullT ℓ Pt))
    (b : Expr O' Γ (simBaseT ℓ Pt)) :
    (scSetBase sC b).cost ≤ sC.cost + b.cost + 30 := by
  simp only [scSetBase, cost_eLet, scMk, scKept, scSent, scSnaps, Expr.cost, Expr.v0]
  omega

private theorem hb32_nat : bits 32 = 6 :=
  bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)

private theorem hb32_pnat : bits ((32 : ℕ+) : ℕ) = 6 := hb32_nat

private theorem hb0_bits : bits 0 = 1 := bits_zero
private theorem hb1_bits : bits 1 = 1 :=
  bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
private theorem hb2_bits : bits 2 ≤ 2 := bits_le_of_lt_pow (by omega) (by omega)
private theorem hb3_bits : bits 3 ≤ 2 := bits_le_of_lt_pow (by omega) (by omega)
private theorem hb4_bits : bits 4 ≤ 3 := bits_le_of_lt_pow (by omega) (by omega)
private theorem hb5_bits : bits 5 ≤ 3 := bits_le_of_lt_pow (by omega) (by omega)
private theorem hb6_bits : bits 6 ≤ 3 := bits_le_of_lt_pow (by omega) (by omega)
private theorem hb10_bits : bits 10 ≤ 4 := bits_le_of_lt_pow (by omega) (by omega)
private theorem hb2000_bits : bits 2000 ≤ 11 := bits_le_of_lt_pow (by omega) (by omega)
private theorem hb25000_bits : bits 25000 ≤ 15 := bits_le_of_lt_pow (by omega) (by omega)
private theorem hb2pow32_bits : bits (2 ^ 32) ≤ 33 := bits_le_of_lt_pow (by omega) (by omega)

theorem atomicTyDescBits_posTy :
    atomicTyDescBits (posTy : Ty ASig) ≤ 20 := by
  dsimp only [posTy, atomicTyDescBits]
  omega

theorem atomicTyDescBits_simRecT :
    atomicTyDescBits (simRecT ℓ Pt) ≤ 80 := by
  dsimp only [simRecT, posTy, B, ReductionDsl.PB, PlainT, atomicTyDescBits, atomicSortDescBits]
  rw [hb32_pnat]
  omega

theorem atomicTyDescBits_simMirT :
    atomicTyDescBits (simMirT ℓ Pt) ≤ 300 := by
  dsimp only [simMirT, simRecT, posTy, B, ReductionDsl.PB, PlainT,
    atomicTyDescBits, atomicSortDescBits]
  simp only [hb32_pnat]
  omega

theorem atomicTyDescBits_fig8CtT :
    atomicTyDescBits (fig8CtT (ℓ := ℓ) (Pt := Pt)) ≤ 110 := by
  dsimp only [fig8CtT, ReductionDsl.fig8HdrT, ReductionDsl.lctT, ReductionDsl.wireSaltCtT,
    B, ReductionDsl.PB, ReductionDsl.U64, BV256, PtT, atomicTyDescBits, atomicSortDescBits]
  rw [hb32_pnat]
  omega

theorem atomicTyDescBits_fsSendStT :
    atomicTyDescBits (fsSendStT (ℓ := ℓ) (Pt := Pt)) ≤ 20 := by
  dsimp only [fsSendStT, BV256, atomicTyDescBits, atomicSortDescBits]
  omega

theorem atomicTyDescBits_fsRecvStT :
    atomicTyDescBits (fsRecvStT (ℓ := ℓ) (Pt := Pt)) ≤ 50 := by
  dsimp only [fsRecvStT, BV256, atomicTyDescBits, atomicSortDescBits]
  omega

theorem atomicTyDescBits_fig8StT :
    atomicTyDescBits (fig8StT (ℓ := ℓ) (Pt := Pt)) ≤ 140 := by
  dsimp only [fig8StT, fsSendStT, fsRecvStT, ReductionDsl.ckaStT, BV256, PtT,
    atomicTyDescBits, atomicSortDescBits]
  omega

theorem atomicTyDescBits_ghostChainT :
    atomicTyDescBits (ghostChainT ℓ Pt) ≤ 40 := by
  dsimp only [ghostChainT, PK, atomicTyDescBits, atomicSortDescBits]
  omega

theorem atomicTyDescBits_simBaseT :
    atomicTyDescBits (simBaseT ℓ Pt) ≤ 700 := by
  dsimp only [simBaseT, simMirT, simRecT, posTy, fig8CtT, ReductionDsl.fig8HdrT,
    ReductionDsl.lctT, ReductionDsl.wireSaltCtT, ghostChainT,
    B, ReductionDsl.PB, ReductionDsl.U64, PlainT, BV256, PtT, PK, U32,
    atomicTyDescBits, atomicSortDescBits]
  simp only [hb32_pnat]
  omega

theorem atomicTyDescBits_keptT :
    atomicTyDescBits (keptT ℓ Pt) ≤ 400 := by
  dsimp only [keptT, fig8StT, fsSendStT, fsRecvStT, ReductionDsl.ckaStT,
    ReductionDsl.U64, BV256, PtT, atomicTyDescBits, atomicSortDescBits]
  omega

theorem atomicTyDescBits_snapT :
    atomicTyDescBits (snapT ℓ Pt) ≤ 30 := by
  dsimp only [snapT, GhostStT, atomicTyDescBits, atomicSortDescBits]
  omega

theorem atomicTyDescBits_sentEntryT :
    atomicTyDescBits (sentEntryT ℓ Pt) ≤ 160 := by
  dsimp only [sentEntryT, fig8CtT, ReductionDsl.fig8HdrT, ReductionDsl.lctT,
    ReductionDsl.wireSaltCtT, fsSendStT, B, ReductionDsl.PB, ReductionDsl.U64, BV256, PtT,
    atomicTyDescBits, atomicSortDescBits]
  simp only [hb32_pnat]
  omega

theorem atomicTyDescBits_simFullT :
    atomicTyDescBits (simFullT ℓ Pt) ≤ 1800 := by
  dsimp only [simFullT, simBaseT, simMirT, simRecT, posTy, keptT, fig8StT, fsSendStT, fsRecvStT,
    ReductionDsl.ckaStT, sentEntryT, fig8CtT, ReductionDsl.fig8HdrT, ReductionDsl.lctT,
    ReductionDsl.wireSaltCtT, ghostChainT, snapT,
    B, ReductionDsl.PB, ReductionDsl.U64, PlainT, BV256, PtT, PK, U32, GhostStT,
    atomicTyDescBits, atomicSortDescBits]
  simp only [hb32_pnat]
  omega

theorem mSetWin_descBits_le {O' : Ops ASig} (opB : O'.Op → ℕ)
    {Γ : List (Ty ASig)} (s : Expr O' Γ (simMirT ℓ Pt)) (w : Expr O' Γ .bool) :
    atomicExprDescBits opB (mSetWin s w) ≤
      atomicExprDescBits opB s + atomicExprDescBits opB w + 900 := by
  dsimp only [mSetWin, eLet, mMk, mB, mEpoch, mIdx, mTL, mTrans, mChall, mComp,
    mMaxAcc, mLeaks, mCorrs, Expr.v0, atomicExprDescBits, varIdx]
  simp only [hb0_bits]
  omega

theorem mSafeChE_descBits_le {O' : Ops ASig} (opB : O'.Op → ℕ)
    {Γ : List (Ty ASig)} (s : Expr O' Γ (simMirT ℓ Pt)) (p : Expr O' Γ .bool) :
    atomicExprDescBits opB (mSafeChE s p) ≤
      2 * atomicExprDescBits opB s + atomicExprDescBits opB p + 350 := by
  have hb3 := hb3_bits
  dsimp only [mSafeChE, eLet, healedByE, CryptoGames.SM.leN, mTL, mEpoch, pGet,
    Expr.v0, Expr.v1, atomicExprDescBits, varIdx]
  simp only [Nat.reduceAdd, hb0_bits, hb1_bits]
  omega

theorem mSafeInjE_descBits_le {O' : Ops ASig} (opB : O'.Op → ℕ)
    {Γ : List (Ty ASig)} (s : Expr O' Γ (simMirT ℓ Pt)) :
    atomicExprDescBits opB (mSafeInjE s) ≤ atomicExprDescBits opB s + 350 := by
  have hb3 := hb3_bits
  dsimp only [mSafeInjE, eLet, healedByE, CryptoGames.SM.leN, minN, mTL, mEpoch,
    Expr.v0, Expr.v1, atomicExprDescBits, varIdx]
  simp only [Nat.reduceAdd, hb0_bits, hb1_bits]
  omega

theorem mLeakE_descBits_le {O' : Ops ASig} (opB : O'.Op → ℕ)
    {Γ : List (Ty ASig)} (s : Expr O' Γ (simMirT ℓ Pt)) (l : Expr O' Γ .nat) :
    atomicExprDescBits opB (mLeakE s l) ≤
      atomicExprDescBits opB s + atomicExprDescBits opB l + 1300 := by
  dsimp only [mLeakE, eLet, mMk, maxOptE, maxN, CryptoGames.SM.leN, mB, mWin, mEpoch, mIdx,
    mTL, mTrans, mChall, mComp, mMaxAcc, mLeaks, mCorrs, Expr.v0, Expr.v1,
    atomicExprDescBits, varIdx]
  simp only [Nat.reduceAdd, hb0_bits, hb1_bits]
  omega

theorem mEpMgmtE_descBits_le {O' : Ops ASig} (opB : O'.Op → ℕ) (qep : ℕ)
    {Γ : List (Ty ASig)} (s : Expr O' Γ (simMirT ℓ Pt)) (p bad : Expr O' Γ .bool) :
    atomicExprDescBits opB (mEpMgmtE qep s p bad) ≤
      atomicExprDescBits opB s + atomicExprDescBits opB p + atomicExprDescBits opB bad +
      4 * bits qep + 4500 := by
  have hb2 := hb2_bits
  have hb3 := hb3_bits
  dsimp only [mEpMgmtE, eLet, mSafeChE, mLeakE, mMk, maxOptE, maxN, healedByE,
    CryptoGames.SM.leN, sendsInE, pGet, pSet, mB, mWin, mEpoch, mIdx, mTL, mTrans,
    mChall, mComp, mMaxAcc, mLeaks, mCorrs, simMirT, simRecT, posTy, B, ReductionDsl.PB, PlainT,
    Expr.v0, Expr.v1, atomicExprDescBits, atomicTyDescBits, atomicSortDescBits, varIdx]
  simp only [Nat.reduceAdd, hb0_bits, hb1_bits, hb32_pnat]
  omega

theorem mRecordE_descBits_le {O' : Ops ASig} (opB : O'.Op → ℕ)
    {Γ : List (Ty ASig)} (s : Expr O' Γ (simMirT ℓ Pt)) (p : Expr O' Γ .bool)
    (r : Expr O' Γ (simRecT ℓ Pt)) (isChall : Expr O' Γ .bool) :
    atomicExprDescBits opB (mRecordE s p r isChall) ≤
      atomicExprDescBits opB s + atomicExprDescBits opB p +
      atomicExprDescBits opB r + atomicExprDescBits opB isChall + 1600 := by
  have hb3 := hb3_bits
  dsimp only [mRecordE, eLet, mSafeChE, healedByE, CryptoGames.SM.leN, mMk, pGet, pSet,
    posIdx, srecPos, mB, mWin, mEpoch, mIdx, mTL, mTrans, mChall, mComp, mMaxAcc, mLeaks,
    mCorrs, Expr.v0, Expr.v1, atomicExprDescBits, varIdx]
  simp only [Nat.reduceAdd, hb0_bits, hb1_bits]
  omega

theorem mDeleteE_descBits_le {O' : Ops ASig} (opB : O'.Op → ℕ) (Lq : ℕ)
    {Γ : List (Ty ASig)} (s : Expr O' Γ (simMirT ℓ Pt)) (pos : Expr O' Γ posTy) :
    atomicExprDescBits opB (mDeleteE Lq s pos) ≤
      atomicExprDescBits opB s + atomicExprDescBits opB pos + 6 * bits Lq + 2000 := by
  have hb2 := hb2_bits
  dsimp only [mDeleteE, eLet, mMk, posEq, boolEq, posSender, posEpoch, posIdx, srecPos,
    mB, mWin, mEpoch, mIdx, mTL, mTrans, mChall, mComp, mMaxAcc, mLeaks, mCorrs,
    simRecT, posTy, B, ReductionDsl.PB, PlainT,
    Expr.v0, Expr.v1, Expr.v2, atomicExprDescBits, atomicTyDescBits, atomicSortDescBits, varIdx]
  simp only [Nat.reduceAdd, hb0_bits, hb1_bits, hb32_pnat]
  omega

theorem mAcceptE_descBits_le {O' : Ops ASig} (opB : O'.Op → ℕ) (Lq : ℕ)
    {Γ : List (Ty ASig)} (s : Expr O' Γ (simMirT ℓ Pt))
    (p : Expr O' Γ .bool) (pos : Expr O' Γ posTy) :
    atomicExprDescBits opB (mAcceptE Lq s p pos) ≤
      atomicExprDescBits opB s + atomicExprDescBits opB p +
      2 * atomicExprDescBits opB pos + 8 * bits Lq + 4500 := by
  have hb2 := hb2_bits
  dsimp only [mAcceptE, mDeleteE, eLet, mMk, posEq, boolEq, posSender, pGet, pSet, maxAccGet,
    maxAccSet, maxN, CryptoGames.SM.leN, posEpoch, posIdx, srecPos,
    mB, mWin, mEpoch, mIdx, mTL, mTrans, mChall, mComp, mMaxAcc, mLeaks, mCorrs,
    simRecT, posTy, B, ReductionDsl.PB, PlainT,
    Expr.v0, Expr.v1, Expr.v2, atomicExprDescBits, atomicTyDescBits, atomicSortDescBits, varIdx]
  simp only [Nat.reduceAdd, hb0_bits, hb1_bits, hb32_pnat]
  omega

theorem mCompContainsE_descBits_le {O' : Ops ASig} (opB : O'.Op → ℕ) (Lq : ℕ)
    {Γ : List (Ty ASig)} (s : Expr O' Γ (simMirT ℓ Pt)) (pos : Expr O' Γ posTy) :
    atomicExprDescBits opB (mCompContainsE Lq s pos) ≤
      atomicExprDescBits opB s + atomicExprDescBits opB pos + 2 * bits Lq + 350 := by
  dsimp only [mCompContainsE, eLet, mComp, posEq, boolEq, posSender, posEpoch, posIdx,
    Expr.v0, Expr.v1, atomicExprDescBits, varIdx]
  simp only [Nat.reduceAdd, hb0_bits, hb1_bits]
  omega

theorem mChallContainsE_descBits_le {O' : Ops ASig} (opB : O'.Op → ℕ) (Lq : ℕ)
    {Γ : List (Ty ASig)} (s : Expr O' Γ (simMirT ℓ Pt)) (pos : Expr O' Γ posTy) :
    atomicExprDescBits opB (mChallContainsE Lq s pos) ≤
      atomicExprDescBits opB s + atomicExprDescBits opB pos + 2 * bits Lq + 350 := by
  dsimp only [mChallContainsE, eLet, mChall, posEq, boolEq, posSender, posEpoch, posIdx,
    Expr.v0, Expr.v1, atomicExprDescBits, varIdx]
  simp only [Nat.reduceAdd, hb0_bits, hb1_bits]
  omega

theorem mTrivialE_descBits_le {O' : Ops ASig} (opB : O'.Op → ℕ) (Lq : ℕ)
    {Γ : List (Ty ASig)} (s : Expr O' Γ (simMirT ℓ Pt)) (pos : Expr O' Γ posTy) :
    atomicExprDescBits opB (mTrivialE Lq s pos) ≤
      atomicExprDescBits opB s + atomicExprDescBits opB pos + 4 * bits Lq + 900 := by
  have hb3 := hb3_bits
  dsimp only [mTrivialE, mCompContainsE, eLet, orE, healedByE, CryptoGames.SM.leN,
    posEq, boolEq, posSender, posEpoch, posIdx, srecPos, mComp, mTrans, mTL, Expr.v0, Expr.v1,
    atomicExprDescBits, varIdx]
  simp only [Nat.reduceAdd, hb0_bits, hb1_bits]
  omega

theorem mCorrAllowedE_descBits_le {O' : Ops ASig} (opB : O'.Op → ℕ) (Lq : ℕ)
    {Γ : List (Ty ASig)} (s : Expr O' Γ (simMirT ℓ Pt)) (p : Expr O' Γ .bool) :
    atomicExprDescBits opB (mCorrAllowedE Lq s p) ≤
      atomicExprDescBits opB s + atomicExprDescBits opB p + 6 * bits Lq + 800 := by
  dsimp only [mCorrAllowedE, mCompContainsE, eLet, boolEq, otherE, posEq, posSender,
    posEpoch, posIdx, srecPos, mChall, mTrans, mComp, Expr.v0, Expr.v1,
    atomicExprDescBits, varIdx]
  simp only [Nat.reduceAdd, hb0_bits, hb1_bits]
  omega

theorem mAfterCorrE_descBits_le {O' : Ops ASig} (opB : O'.Op → ℕ) (Lq : ℕ)
    {Γ : List (Ty ASig)} (s : Expr O' Γ (simMirT ℓ Pt)) (p : Expr O' Γ .bool) :
    atomicExprDescBits opB (mAfterCorrE Lq s p) ≤
      atomicExprDescBits opB s + atomicExprDescBits opB p + 48 * bits Lq + 60000 := by
  have hb2 := hb2_bits
  dsimp only [mAfterCorrE, mLeakE, eLet, mMk, maxOptE, maxN, CryptoGames.SM.leN, boolEq,
    otherE, posEq, posSender, posEpoch, posIdx, srecPos, pGet, mB, mWin, mEpoch, mIdx, mTL, mTrans,
    mChall, mComp, mMaxAcc, mLeaks, mCorrs, Expr.v0, Expr.v1, Expr.v2,
    atomicExprDescBits, varIdx]
  simp only [Nat.reduceAdd, hb0_bits, hb1_bits]
  omega

theorem mCorrAllowedFastE_descBits_le {O' : Ops ASig} (opB : O'.Op → ℕ) (Lq : ℕ)
    {Γ : List (Ty ASig)} (s : Expr O' Γ (simMirT ℓ Pt)) (p : Expr O' Γ .bool) :
    atomicExprDescBits opB (mCorrAllowedFastE Lq s p) ≤
      atomicExprDescBits opB s + atomicExprDescBits opB p + 8 * bits Lq + 2000 := by
  have hb2 := hb2_bits
  dsimp only [mCorrAllowedFastE, compTblOfListE, compTblEmptyE, compTblInsertE, compTblGetE,
    eLet, boolEq, otherE, posSender, posEpoch, posIdx, srecPos, pGet, pSet,
    mChall, mTrans, mComp, compTblTy, simRecT, posTy, B, ReductionDsl.PB, PlainT,
    Expr.v0, Expr.v1, Expr.v2, atomicExprDescBits, atomicTyDescBits, atomicSortDescBits, varIdx]
  simp only [Nat.reduceAdd, hb0_bits, hb1_bits]
  omega

theorem mAfterCorrFastE_descBits_le {O' : Ops ASig} (opB : O'.Op → ℕ) (Lq : ℕ)
    {Γ : List (Ty ASig)} (s : Expr O' Γ (simMirT ℓ Pt)) (p : Expr O' Γ .bool) :
    atomicExprDescBits opB (mAfterCorrFastE Lq s p) ≤
      atomicExprDescBits opB s + atomicExprDescBits opB p + 48 * bits Lq + 60000 := by
  have hb2 := hb2_bits
  dsimp only [mAfterCorrFastE, compTblOfListE, compTblEmptyE, compTblInsertE, compTblGetE,
    mLeakE, eLet, mMk, maxOptE, maxN, CryptoGames.SM.leN, boolEq, otherE,
    posSender, posEpoch, posIdx, srecPos, pGet, pSet, mB, mWin, mEpoch, mIdx, mTL, mTrans,
    mChall, mComp, mMaxAcc, mLeaks, mCorrs, compTblTy, simRecT, posTy, B, ReductionDsl.PB, PlainT,
    Expr.v0, Expr.v1, Expr.v2, atomicExprDescBits, atomicTyDescBits, atomicSortDescBits, varIdx]
  simp only [Nat.reduceAdd, hb0_bits, hb1_bits]
  omega

theorem mInWinE_descBits_le {O' : Ops ASig} (opB : O'.Op → ℕ)
    {Γ : List (Ty ASig)} (s : Expr O' Γ (simMirT ℓ Pt)) (p : Expr O' Γ .bool) :
    atomicExprDescBits opB (mInWinE s p) ≤
      atomicExprDescBits opB s + atomicExprDescBits opB p + 500 := by
  have hb2 := hb2_bits
  dsimp only [mInWinE, eLet, sendsInE, pGet, mEpoch, Expr.v0, atomicExprDescBits, varIdx]
  simp only [hb0_bits, hb1_bits]
  omega

theorem mNoBobEpoch0E_descBits_le {O' : Ops ASig} (opB : O'.Op → ℕ)
    {Γ : List (Ty ASig)} (s : Expr O' Γ (simMirT ℓ Pt)) (p : Expr O' Γ .bool) :
    atomicExprDescBits opB (mNoBobEpoch0E s p) ≤
      atomicExprDescBits opB s + atomicExprDescBits opB p + 150 := by
  dsimp only [mNoBobEpoch0E, eLet, mEpoch, Expr.v0, atomicExprDescBits, varIdx]
  simp only [hb0_bits]
  omega

theorem mNoSpkCorrE_descBits_le {O' : Ops ASig} (opB : O'.Op → ℕ)
    {Γ : List (Ty ASig)} (s : Expr O' Γ (simMirT ℓ Pt)) (p : Expr O' Γ .bool) :
    atomicExprDescBits opB (mNoSpkCorrE s p) ≤
      atomicExprDescBits opB s + atomicExprDescBits opB p + 150 := by
  have hb10 := hb10_bits
  dsimp only [mNoSpkCorrE, eLet, mEpoch, Expr.v0, atomicExprDescBits, varIdx]
  simp only [hb0_bits]
  omega

theorem ssSetAmb_descBits_le {O' : Ops ASig} (opB : O'.Op → ℕ) {Γ : List (Ty ASig)}
    (s : Expr O' Γ (simBaseT ℓ Pt)) (a : Expr O' Γ .nat) :
    atomicExprDescBits opB (ssSetAmb s a) ≤
      atomicExprDescBits opB s + atomicExprDescBits opB a + 450 := by
  dsimp only [ssSetAmb, eLet, ssMk, ssMir, ssPq, ssPn, ssUnackA, ssHonest, ssChains, ssStopped,
    Expr.v0, atomicExprDescBits, varIdx]
  simp only [hb0_bits]
  omega

theorem ssSetMirWin_descBits_le {O' : Ops ASig} (opB : O'.Op → ℕ) {Γ : List (Ty ASig)}
    (s : Expr O' Γ (simBaseT ℓ Pt)) :
    atomicExprDescBits opB (ssSetMirWin s) ≤ atomicExprDescBits opB s + 1500 := by
  have hw := mSetWin_descBits_le opB (ssMir (O' := O') (.v0 : Expr O' (simBaseT ℓ Pt :: Γ) _))
    (.bool true)
  dsimp only [ssMir, Expr.v0, atomicExprDescBits, varIdx] at hw
  simp only [hb0_bits] at hw
  dsimp only [ssSetMirWin, eLet, ssMk, ssMir, ssPq, ssPn, ssUnackA, ssHonest, ssChains, ssAmb,
    ssStopped, Expr.v0, atomicExprDescBits, varIdx]
  simp only [hb0_bits]
  omega

theorem ssSetMir_descBits_le {O' : Ops ASig} (opB : O'.Op → ℕ) {Γ : List (Ty ASig)}
    (s : Expr O' Γ (simBaseT ℓ Pt)) (m : Expr O' Γ (simMirT ℓ Pt)) :
    atomicExprDescBits opB (ssSetMir s m) ≤
      atomicExprDescBits opB s + atomicExprDescBits opB m + 450 := by
  dsimp only [ssSetMir, eLet, ssMk, ssPq, ssPn, ssUnackA, ssHonest, ssChains, ssAmb,
    ssStopped, Expr.v0, atomicExprDescBits, varIdx]
  simp only [hb0_bits]
  omega

theorem scSetBase_descBits_le {O' : Ops ASig} (opB : O'.Op → ℕ) {Γ : List (Ty ASig)}
    (sC : Expr O' Γ (simFullT ℓ Pt)) (b : Expr O' Γ (simBaseT ℓ Pt)) :
    atomicExprDescBits opB (scSetBase sC b) ≤
      atomicExprDescBits opB sC + atomicExprDescBits opB b + 150 := by
  dsimp only [scSetBase, eLet, scMk, scKept, scSent, scSnaps, Expr.v0, atomicExprDescBits, varIdx]
  simp only [hb0_bits]
  omega

theorem takeListE_descBits_le {O' : Ops ASig} (opB : O'.Op → ℕ)
    {Γ : List (Ty ASig)} {t : Ty ASig} (B_cap : ℕ) (xs : Expr O' Γ (.list t)) :
    atomicExprDescBits opB (takeListE B_cap xs) ≤
      atomicExprDescBits opB xs + 2 * bits B_cap + 20 := by
  dsimp only [takeListE, Expr.v0, atomicExprDescBits, varIdx]
  simp only [hb0_bits]
  omega

theorem eraseFirstNatC_descBits_le {O' : Ops ASig} (opB : O'.Op → ℕ)
    {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    (sB : I'.smp.Samp → ℕ) (qB : I'.Tag → ℕ)
    (B_cap : ℕ) {Γ : List (Ty ASig)}
    (xs : Expr O' Γ (.list .nat)) (target : Expr O' Γ .nat) :
    atomicCompDescBits opB sB qB (eraseFirstNatC I' B_cap xs target) ≤
      atomicExprDescBits opB xs + atomicExprDescBits opB target + 8 * bits B_cap + 500 := by
  have hb2 := hb2_bits
  dsimp only [eraseFirstNatC, Expr.v0, Expr.v1, Expr.v2,
    atomicCompDescBits, atomicExprDescBits, atomicTyDescBits, varIdx]
  simp only [Nat.reduceAdd, hb0_bits, hb1_bits]
  omega

theorem ghostAcceptC_descBits_le {O' : Ops ASig} (opB : O'.Op → ℕ)
    {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    (sB : I'.smp.Samp → ℕ) (qB : I'.Tag → ℕ)
    {Γ : List (Ty ASig)} (gE : Expr O' Γ (ghostChainT ℓ Pt)) (iE : Expr O' Γ .nat) :
    atomicCompDescBits opB sB qB (ghostAcceptC I' gE iE) ≤
      atomicExprDescBits opB gE + atomicExprDescBits opB iE + 2500 := by
  have hb2k := hb2000_bits
  let Γ1 := Ty.prod (ghostChainT ℓ Pt) .nat :: Γ
  have her := eraseFirstNatC_descBits_le opB I' sB qB 2000
    (.snd (.snd (.snd (.fst (.v0 : Expr O' Γ1 _)))))
    (.snd (.v0 : Expr O' Γ1 _))
  have htk := takeListE_descBits_le opB 2000
    (.snd (.snd (.v0 : Expr O' (.prod .nat (.prod .nat (.list .nat)) :: Γ1) _)))
  dsimp only [Expr.v0, atomicExprDescBits, varIdx] at her htk
  simp only [hb0_bits] at her htk
  dsimp only [ghostAcceptC, minN, CryptoGames.SM.leN, Expr.v0, Expr.v1,
    atomicCompDescBits, atomicExprDescBits, varIdx]
  simp only [Nat.reduceAdd, hb0_bits, hb1_bits]
  omega

theorem ghostRejectsE_descBits_le {O' : Ops ASig} (opB : O'.Op → ℕ)
    {Γ : List (Ty ASig)} (gE : Expr O' Γ (ghostChainT ℓ Pt)) (iE : Expr O' Γ .nat) :
    atomicExprDescBits opB (ghostRejectsE gE iE) ≤
      atomicExprDescBits opB gE + atomicExprDescBits opB iE + 500 := by
  have hb2k := hb2000_bits
  have hb25k := hb25000_bits
  have hb232 := hb2pow32_bits
  dsimp only [ghostRejectsE, eLet, orE, Expr.v0, Expr.v1, atomicExprDescBits, varIdx]
  simp only [Nat.reduceAdd, hb0_bits, hb1_bits]
  omega

theorem pushChainE_descBits_le {O' : Ops ASig} (opB : O'.Op → ℕ)
    {Γ : List (Ty ASig)}
    (csE : Expr O' Γ (.list (ghostChainT ℓ Pt))) (gE : Expr O' Γ (ghostChainT ℓ Pt)) :
    atomicExprDescBits opB (pushChainE csE gE) ≤
      atomicExprDescBits opB csE + atomicExprDescBits opB gE + 800 := by
  have hb4 := hb4_bits
  have hb5 := hb5_bits
  have hb6 := hb6_bits
  dsimp only [pushChainE, eLet, unconsB, ghostChainT, PK, Expr.v0, Expr.v1,
    atomicExprDescBits, atomicTyDescBits, atomicSortDescBits, varIdx]
  simp only [Nat.reduceAdd, hb0_bits, hb1_bits]
  omega

theorem getChainDE_descBits_le {O' : Ops ASig} (opB : O'.Op → ℕ)
    {Γ : List (Ty ASig)}
    (csE : Expr O' Γ (.list (ghostChainT ℓ Pt))) (ciE : Expr O' Γ .nat) :
    atomicExprDescBits opB (getChainDE csE ciE) ≤
      atomicExprDescBits opB csE + atomicExprDescBits opB ciE + 3000 := by
  have hb2 := hb2_bits
  have hb3 := hb3_bits
  have hb4 := hb4_bits
  have hb5 := hb5_bits
  dsimp only [getChainDE, listGetDConstE, eLet, unconsB, ghostChainT, PK, Expr.v0, Expr.v1,
    atomicExprDescBits, atomicTyDescBits, atomicSortDescBits, varIdx]
  simp only [Nat.reduceAdd, hb0_bits, hb1_bits]
  omega

theorem modifyChainAcceptC_descBits_le {O' : Ops ASig} (opB : O'.Op → ℕ)
    {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    (sB : I'.smp.Samp → ℕ) (qB : I'.Tag → ℕ)
    {Γ : List (Ty ASig)}
    (csE : Expr O' Γ (.list (ghostChainT ℓ Pt))) (ciE iE : Expr O' Γ .nat) :
    atomicCompDescBits opB sB qB (modifyChainAcceptC I' csE ciE iE) ≤
      atomicExprDescBits opB csE + atomicExprDescBits opB ciE +
      atomicExprDescBits opB iE + 9500 := by
  have hb2 := hb2_bits
  have hb3 := hb3_bits
  have hb4 := hb4_bits
  have hb5 := hb5_bits
  let Γ1 := Ty.prod (.list (ghostChainT ℓ Pt)) (.prod .nat .nat) :: Γ
  have hgd := getChainDE_descBits_le opB
    (.fst (.v0 : Expr O' Γ1 _)) (.fst (.snd (.v0 : Expr O' Γ1 _)))
  have hac := ghostAcceptC_descBits_le opB I' sB qB
    (getChainDE (.fst (.v0 : Expr O' Γ1 _)) (.fst (.snd (.v0 : Expr O' Γ1 _))))
    (.snd (.snd (.v0 : Expr O' Γ1 _)))
  dsimp only [Expr.v0, atomicExprDescBits, varIdx] at hgd hac
  simp only [hb0_bits] at hgd hac
  dsimp only [modifyChainAcceptC, listSetAtConstE, eLet, unconsB, ghostChainT, PK, Expr.v0, Expr.v1,
    atomicCompDescBits, atomicExprDescBits, atomicTyDescBits, atomicSortDescBits, varIdx]
  simp only [Nat.reduceAdd, hb0_bits, hb1_bits]
  omega

theorem anyChainKeyNoneE_descBits_le {O' : Ops ASig} (opB : O'.Op → ℕ)
    {Γ : List (Ty ASig)} (csE : Expr O' Γ (.list (ghostChainT ℓ Pt))) :
    atomicExprDescBits opB (anyChainKeyNoneE csE) ≤
      atomicExprDescBits opB csE + 100 := by
  have hb5 := hb5_bits
  dsimp only [anyChainKeyNoneE, Expr.v0, atomicExprDescBits, varIdx]
  simp only [hb0_bits]
  omega

theorem revealSpkChainsE_descBits_le {O' : Ops ASig} (opB : O'.Op → ℕ)
    {Γ : List (Ty ASig)}
    (csE : Expr O' Γ (.list (ghostChainT ℓ Pt))) (pkE : Expr O' Γ PK) :
    atomicExprDescBits opB (revealSpkChainsE csE pkE) ≤
      atomicExprDescBits opB csE + atomicExprDescBits opB pkE + 250 := by
  have hb5 := hb5_bits
  dsimp only [revealSpkChainsE, eLet, ghostChainT, PK, Expr.v0, Expr.v1,
    atomicExprDescBits, atomicTyDescBits, atomicSortDescBits, varIdx]
  simp only [Nat.reduceAdd, hb0_bits, hb1_bits]
  omega

end StateAccessorsAndDescBits
section AtomicBaseDescBits

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
  {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
  {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

theorem mInTransitE_descBits_le (Lq : ℕ) {Γ : List (Ty ASig)}
    (s : Expr AOps Γ (simMirT ℓ Pt)) (qParty : Expr AOps Γ .bool) (w : Expr AOps Γ (B 32)) :
    atomicExprDescBits atomicSessionOpDescBits
      (mInTransitE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) Lq s qParty w) ≤
      atomicExprDescBits atomicSessionOpDescBits s +
      atomicExprDescBits atomicSessionOpDescBits qParty +
      atomicExprDescBits atomicSessionOpDescBits w + 2 * bits Lq + 450 := by
  dsimp only [mInTransitE, eLet, mTrans, boolEq, posSender, srecPos, srecCt,
    Expr.v0, Expr.v1, atomicExprDescBits, varIdx]
  simp only [descBits_sOpPure]
  dsimp only [atomicPureOpDescBits, atomicExprDescBits, varIdx]
  simp only [Nat.reduceAdd, hb0_bits, hb1_bits, hb32_pnat]
  omega

theorem findChainIdxE_descBits_le {Γ : List (Ty ASig)}
    (csE : Expr AOps Γ (.list (ghostChainT ℓ Pt))) (rkE : Expr AOps Γ PK) :
    atomicExprDescBits atomicSessionOpDescBits
      (findChainIdxE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) csE rkE) ≤
      atomicExprDescBits atomicSessionOpDescBits csE +
      atomicExprDescBits atomicSessionOpDescBits rkE + 800 := by
  have hb2 := hb2_bits
  have hb3 := hb3_bits
  have hb5 := hb5_bits
  dsimp only [findChainIdxE, eLet, eMapOpt, Expr.v0, Expr.v1, Expr.v2, Expr.v3,
    PK, atomicExprDescBits, atomicTyDescBits, atomicSortDescBits, varIdx]
  simp only [descBits_sOpPure]
  dsimp only [atomicPureOpDescBits, atomicExprDescBits, varIdx]
  simp only [Nat.reduceAdd, hb0_bits, hb1_bits]
  omega

theorem toGhostScE_descBits_le {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt))) :
    atomicExprDescBits atomicSessionOpDescBits
      (toGhostScE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) stE) ≤
      atomicExprDescBits atomicSessionOpDescBits stE + 400 := by
  have hb2 := hb2_bits
  dsimp only [toGhostScE, eLet, drSenderChainT, PK, BV256, U32,
    Expr.v0, Expr.v1, atomicExprDescBits, atomicTyDescBits, atomicSortDescBits, varIdx]
  simp only [descBits_sOpPure, descBits_sOpSym]
  dsimp only [atomicPureOpDescBits, atomicSymOpDescBits, atomicExprDescBits, varIdx]
  simp only [Nat.reduceAdd, hb0_bits, hb1_bits]
  omega

theorem toGhostRcSomeE_descBits_le (B_skip : ℕ) {Γ : List (Ty ASig)}
    (gE : Expr AOps Γ (ghostChainT ℓ Pt))
    (vrE : Expr AOps Γ (fsRecvStT (ℓ := ℓ) (Pt := Pt))) :
    atomicExprDescBits atomicSessionOpDescBits
      (toGhostRcSomeE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) B_skip gE vrE) ≤
      atomicExprDescBits atomicSessionOpDescBits gE +
      atomicExprDescBits atomicSessionOpDescBits vrE +
      2 * bits B_skip + 1200 := by
  have hb2 := hb2_bits
  have hb2k := hb2000_bits
  let Γ1 := Ty.prod (ghostChainT ℓ Pt) (fsRecvStT (ℓ := ℓ) (Pt := Pt)) :: Γ
  let Γ2 := Ty.tbl (.opt BV256) :: Γ1
  have hpk := pkLitE_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ2) dummyKey
  dsimp only [Γ2, Γ1] at hpk
  dsimp only [toGhostRcSomeE, eLet, drRecvChainT, PK, BV256, U32, Expr.v0, Expr.v1, Expr.v2,
    atomicExprDescBits, atomicTyDescBits, atomicSortDescBits, varIdx]
  simp only [descBits_sOpPure]
  dsimp only [atomicPureOpDescBits, atomicExprDescBits, varIdx]
  simp only [Nat.reduceAdd, hb0_bits, hb1_bits]
  omega

theorem toGhostRcsE_descBits_le (B_skip : ℕ) {Γ : List (Ty ASig)}
    (csE : Expr AOps Γ (.list (ghostChainT ℓ Pt)))
    (stE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt))) :
    atomicExprDescBits atomicSessionOpDescBits
      (toGhostRcsE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) B_skip csE stE) ≤
      atomicExprDescBits atomicSessionOpDescBits csE +
      atomicExprDescBits atomicSessionOpDescBits stE +
      2 * bits B_skip + 2200 := by
  have hb5 := hb5_bits
  let Γ0 := Ty.prod (.list (ghostChainT ℓ Pt)) (fig8StT (ℓ := ℓ) (Pt := Pt)) :: Γ
  let Γg := ghostChainT ℓ Pt :: Γ0
  let Γv := fsRecvStT (ℓ := ℓ) (Pt := Pt) :: Γg
  have hpk := pkLitE_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γg) dummyKey
  have hrc := toGhostRcSomeE_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) B_skip
    (.v1 : Expr AOps Γv _) (.v0 : Expr AOps Γv _)
  dsimp only [Γv, Γg, Γ0, Expr.v0, Expr.v1, atomicExprDescBits, varIdx] at hpk hrc
  simp only [Nat.reduceAdd, hb0_bits, hb1_bits] at hrc
  dsimp only [toGhostRcsE, eLet, drRecvChainT, PK, BV256, U32, Expr.v0, Expr.v1,
    atomicExprDescBits, atomicTyDescBits, atomicSortDescBits, varIdx]
  simp only [Nat.reduceAdd, hb0_bits, hb1_bits]
  omega

theorem toGhostE_descBits_le (idA idB : IdentityKey) (B_skip : ℕ) {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ (simBaseT ℓ Pt)) (qE : Expr AOps Γ .bool)
    (stE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt))) :
    atomicExprDescBits atomicSessionOpDescBits
      (toGhostE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB B_skip sE qE stE) ≤
      atomicExprDescBits atomicSessionOpDescBits sE +
      atomicExprDescBits atomicSessionOpDescBits qE +
      atomicExprDescBits atomicSessionOpDescBits stE +
      2 * bits B_skip + 8000 := by
  have hb5 := hb5_bits
  let Γ0 := Ty.prod (simBaseT ℓ Pt) (.prod .bool (fig8StT (ℓ := ℓ) (Pt := Pt))) :: Γ
  let Γt := Ty.prod (simBaseT ℓ Pt) (.prod .bool (fig8StT (ℓ := ℓ) (Pt := Pt))) :: Γ0
  have hidA1 := idKeyAtomLitE_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ0) idA
  have hidB1 := idKeyAtomLitE_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ0) idB
  have hsc := toGhostScE_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    (.snd (.snd (.v0 : Expr AOps Γt _)))
  have hrcs := toGhostRcsE_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) B_skip
    (pGet (.fst (.snd (.snd (.snd (.snd (.snd (.fst (.v0 : Expr AOps Γt _))))))))
      (.fst (.snd (.v0 : Expr AOps Γt _))))
    (.snd (.snd (.v0 : Expr AOps Γt _)))
  have hver : bits (BitVec.ofNat 32 currentVersion.toNat).toNat ≤ 33 := by
    apply bits_le_of_lt_pow (by omega)
    exact lt_of_lt_of_le (BitVec.isLt _) (by omega)
  dsimp only [Γ0, Γt, pGet, Expr.v0, atomicExprDescBits, varIdx] at hidA1 hidB1 hsc hrcs
  simp only [hb0_bits] at hsc hrcs
  dsimp only [toGhostE, toGhostTailE, eLet, pGet, mEpoch, drSenderChainT, drRecvChainT,
    PK, BV256, U32, IdKey, Expr.v0, atomicExprDescBits, atomicTyDescBits, atomicSortDescBits,
    varIdx]
  simp only [descBits_sOpPure, atomicExprDescBits]
  dsimp only [atomicPureOpDescBits, atomicExprDescBits, varIdx]
  simp only [Nat.reduceAdd, hb0_bits]
  omega

end AtomicBaseDescBits

end Computational.Proofs.Game.PromotedCostedReds.SimFig8State
