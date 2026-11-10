/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.BlankedPrivRed
public import Computational.Proofs.ReductionDsl.SM.GameCosted
public import Computational.Proofs.ReductionDsl.Soundness
import Computational.Proofs.ReductionDsl.Bridge
import Computational.Proofs.ReductionDsl.Notation

/-!
# Costed Theorem 1 SM Reductions

Defines `challSimProg` and `privRedBProg` as `ReductionDsl.CostedReduction` programs for the
ACD19 Theorem 1 SM simulators (`Thm1.challSim` and `ThmB.privRedB`), with evaluation agreement,
1:1 target-query bounds, and cost bounds.
-/

@[expose] public section

namespace CryptoGames.SM

open ReductionDsl OracleSpec OracleComp
open scoped Computational.Proofs.ReductionDsl.Notation

local macro_rules
  | `(rdsl_pat| .transmit $p:term)  => `(rdsl_pat| .inl (.inl (.inl (.inl $p))))
  | `(rdsl_pat| .challenge $p:term) => `(rdsl_pat| .inl (.inl (.inl (.inr $p))))
  | `(rdsl_pat| .deliver $p:term)   => `(rdsl_pat| .inl (.inl (.inr $p)))
  | `(rdsl_pat| .inject $p:term)    => `(rdsl_pat| .inl (.inr $p))
  | `(rdsl_pat| .corrupt $p:term)   => `(rdsl_pat| .inr $p)

/-! ## `Mirror` state representation and bookkeeping -/

section MirrorBookkeeping

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

/-- `Thm1.Mirror Msg C` (`GameState Unit Msg C`) as a `ReductionDsl` type in `smSig`:
identical to `gsTy` with `.unit` in place of `.base .st` for the two party-state slots. -/
@[reducible] def mirrorTy : Ty S :=
  .prod (.prod .unit .unit)
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

abbrev mirrorEnc (s : Thm1.Mirror Msg C) :
    (@mirrorTy Key St St₂ Msg Coins RCoins C).denote :=
  gsEnc (Key := Key) (St := Unit) (St₂ := St₂) (Coins := Coins) (RCoins := RCoins) s

abbrev mirrorDec (v : (@mirrorTy Key St St₂ Msg Coins RCoins C).denote) :
    Thm1.Mirror Msg C :=
  gsDec (Key := Key) (St := Unit) (St₂ := St₂) (Coins := Coins) (RCoins := RCoins) v

@[simp] theorem mirrorDec_mirrorEnc (s : Thm1.Mirror Msg C) :
    mirrorDec (Key := Key) (St := St) (St₂ := St₂) (Coins := Coins) (RCoins := RCoins)
      (mirrorEnc s) = s :=
  gsDec_gsEnc (Key := Key) (St := Unit) (St₂ := St₂) (Coins := Coins) (RCoins := RCoins) s

@[simp] theorem mirrorEnc_mirrorDec
    (v : (@mirrorTy Key St St₂ Msg Coins RCoins C).denote) :
    mirrorEnc (Key := Key) (St := St) (St₂ := St₂) (Coins := Coins) (RCoins := RCoins)
      (mirrorDec v) = v :=
  gsEnc_gsDec (Key := Key) (St := Unit) (St₂ := St₂) (Coins := Coins) (RCoins := RCoins) v

def mSt
    {O' : Ops S} {Γ} (s : Expr O' Γ mirrorTy) :
    Expr O' Γ (.prod .unit .unit) := .fst s
def mB
    {O' : Ops S} {Γ} (s : Expr O' Γ mirrorTy) : Expr O' Γ .bool :=
  .fst (.snd s)
def mWin
    {O' : Ops S} {Γ} (s : Expr O' Γ mirrorTy) : Expr O' Γ .bool :=
  .fst (.snd (.snd s))
def mEpoch
    {O' : Ops S} {Γ} (s : Expr O' Γ mirrorTy) : Expr O' Γ (.prod .nat .nat) :=
  .fst (.snd (.snd (.snd s)))
def mIdx
    {O' : Ops S} {Γ} (s : Expr O' Γ mirrorTy) : Expr O' Γ (.prod .nat .nat) :=
  .fst (.snd (.snd (.snd (.snd s))))
def mTL
    {O' : Ops S} {Γ} (s : Expr O' Γ mirrorTy) : Expr O' Γ (.opt .nat) :=
  .fst (.snd (.snd (.snd (.snd (.snd s)))))
def mTrans
    {O' : Ops S} {Γ} (s : Expr O' Γ mirrorTy) : Expr O' Γ (.list recTy) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd s))))))
def mChall
    {O' : Ops S} {Γ} (s : Expr O' Γ mirrorTy) : Expr O' Γ (.list posTy) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd s)))))))
def mComp
    {O' : Ops S} {Γ} (s : Expr O' Γ mirrorTy) : Expr O' Γ (.list posTy) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd s))))))))
def mMaxAcc
    {O' : Ops S} {Γ} (s : Expr O' Γ mirrorTy) :
    Expr O' Γ (.prod (.tbl .nat) (.tbl .nat)) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd s)))))))))
def mLeaks
    {O' : Ops S} {Γ} (s : Expr O' Γ mirrorTy) : Expr O' Γ (.list .nat) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd s))))))))))
def mCorrs
    {O' : Ops S} {Γ} (s : Expr O' Γ mirrorTy) : Expr O' Γ (.list (.prod .bool .nat)) :=
  .snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd s))))))))))

def mMk
    {O' : Ops S} {Γ}
    (st : Expr O' Γ (.prod .unit .unit))
    (b win : Expr O' Γ .bool)
    (epoch idx : Expr O' Γ (.prod .nat .nat))
    (tL : Expr O' Γ (.opt .nat))
    (trans : Expr O' Γ (.list recTy))
    (chall comp : Expr O' Γ (.list posTy))
    (maxAcc : Expr O' Γ (.prod (.tbl .nat) (.tbl .nat)))
    (leaks : Expr O' Γ (.list .nat))
    (corrs : Expr O' Γ (.list (.prod .bool .nat))) : Expr O' Γ mirrorTy :=
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

def mSafeChE
    {O' : Ops S} {Γ} (Δ : ℕ) (s : Expr O' Γ mirrorTy) (p : Expr O' Γ .bool) :
    Expr O' Γ .bool :=
  .letE (.pair s p)
    (healedByE (mTL (.fst .v0)) Δ (pGet (mEpoch (.fst .v0)) (.snd .v0)))

def mLeakE
    {O' : Ops S} {Γ} (s : Expr O' Γ mirrorTy) (l : Expr O' Γ .nat) : Expr O' Γ mirrorTy :=
  .letE (.pair s l)
    (let s0 : Expr O' _ mirrorTy := .fst .v0
     let m : Expr O' _ .nat := maxOptE (mTL s0) (.snd .v0)
     mMk (mSt s0) (mB s0) (mWin s0) (mEpoch s0) (mIdx s0)
       (.some m) (mTrans s0) (mChall s0) (mComp s0) (mMaxAcc s0)
       (.cons m (mLeaks s0)) (mCorrs s0))

def mEpMgmtE
    {O' : Ops S} {Γ} (Δ qep : ℕ) (s : Expr O' Γ mirrorTy) (p : Expr O' Γ .bool)
    (bad : Expr O' Γ .bool) : Expr O' Γ (.opt mirrorTy) :=
  .letE (.pair s (.pair p bad))
    (let s0 : Expr O' _ mirrorTy := .fst .v0
     let p0 : Expr O' _ .bool := .fst (.snd .v0)
     let bad0 : Expr O' _ .bool := .snd (.snd .v0)
     let epP : Expr O' _ .nat := pGet (mEpoch s0) p0
     let epNext : Expr O' _ .nat := .add epP (.nat 1)
     .ite (sendsInE p0 epNext)
       (.ite (.lt (.nat qep) epNext)
         .none
         (.letE (.ite (.and bad0 (.not (mSafeChE Δ s0 p0))) (mLeakE s0 epNext) s0)
           (let s1 : Expr O' _ mirrorTy := .v0
            let p1 : Expr O' _ .bool := .fst (.snd .v1)
            let ep1 : Expr O' _ .nat := .add (pGet (mEpoch s1) p1) (.nat 1)
            .some (mMk (mSt s1) (mB s1) (mWin s1)
              (pSet (mEpoch s1) p1 ep1)
              (pSet (mIdx s1) p1 (.nat 0))
              (mTL s1) (mTrans s1) (mChall s1) (mComp s1)
              (mMaxAcc s1) (mLeaks s1) (mCorrs s1)))))
       (.ite (.lt (.nat qep) epP)
         .none
         (.some s0)))

def mRecordE
    {O' : Ops S} {Γ} (Δ : ℕ) (s : Expr O' Γ mirrorTy) (p : Expr O' Γ .bool)
    (r : Expr O' Γ recTy) (isChall : Expr O' Γ .bool) :
    Expr O' Γ mirrorTy :=
  .letE (.pair s (.pair p (.pair r isChall)))
    (let s0 : Expr O' _ mirrorTy := .fst .v0
     let p0 : Expr O' _ .bool := .fst (.snd .v0)
     let r0 : Expr O' _ recTy := .fst (.snd (.snd .v0))
     let ch0 : Expr O' _ .bool := .snd (.snd (.snd .v0))
     let pos : Expr O' _ posTy := recPos r0
     mMk
       (pSet (mSt s0) p0 .unit)
       (mB s0) (mWin s0) (mEpoch s0)
       (pSet (mIdx s0) p0 (posIdx pos))
       (mTL s0)
       (.cons r0 (mTrans s0))
       (.ite ch0 (.cons pos (mChall s0)) (mChall s0))
       (.ite (mSafeChE Δ s0 p0) (mComp s0) (.cons pos (mComp s0)))
       (mMaxAcc s0) (mLeaks s0) (mCorrs s0))

def mInTransitE {Γ} (K : ℕ) (s : Expr OO Γ mirrorTy) (qParty : Expr OO Γ .bool)
    (c : Expr OO Γ (.base .ct)) : Expr OO Γ (.opt recTy) :=
  .letE (.pair s (.pair qParty c))
    (.findB K (mTrans (.fst .v0))
      (.and (boolEq (posSender (recPos .v0)) (.fst (.snd .v1)))
        (Expr.op (O := OO) SMOp.eqCt (.pair (recCt .v0) (.snd (.snd .v1))))))

def mDeleteE
    {O' : Ops S} {Γ} (K : ℕ) (s : Expr O' Γ mirrorTy) (pos : Expr O' Γ posTy) :
    Expr O' Γ mirrorTy :=
  .letE (.pair s pos)
    (let s0 : Expr O' _ mirrorTy := .fst .v0
     let trans' : Expr O' _ (.list recTy) :=
       .foldrB K (mTrans s0) .nil
         (.ite (.not (posEq (recPos .v0) (.snd .v2))) (.cons .v0 .v1) .v1)
     let chall' : Expr O' _ (.list posTy) :=
       .foldrB K (mChall s0) .nil
         (.ite (.not (posEq .v0 (.snd .v2))) (.cons .v0 .v1) .v1)
     let comp' : Expr O' _ (.list posTy) :=
       .foldrB K (mComp s0) .nil
         (.ite (.not (posEq .v0 (.snd .v2))) (.cons .v0 .v1) .v1)
     mMk (mSt s0) (mB s0) (mWin s0) (mEpoch s0) (mIdx s0) (mTL s0)
       trans' chall' comp' (mMaxAcc s0) (mLeaks s0) (mCorrs s0))

def mAcceptE
    {O' : Ops S} {Γ} (K : ℕ) (s : Expr O' Γ mirrorTy) (p : Expr O' Γ .bool)
    (pos : Expr O' Γ posTy) : Expr O' Γ mirrorTy :=
  .letE (.pair (mDeleteE K s pos) (.pair p pos))
    (let s1 : Expr O' _ mirrorTy := .fst .v0
     let p0 : Expr O' _ .bool := .fst (.snd .v0)
     let pos0 : Expr O' _ posTy := .snd (.snd .v0)
     let pEpoch : Expr O' _ .nat := posEpoch pos0
     let pIdx : Expr O' _ .nat := posIdx pos0
     mMk
       (pSet (mSt s1) p0 .unit)
       (mB s1) (mWin s1)
       (pSet (mEpoch s1) p0 (maxN (pGet (mEpoch s1) p0) pEpoch))
       (mIdx s1) (mTL s1) (mTrans s1) (mChall s1) (mComp s1)
       (maxAccSet (mMaxAcc s1) p0 pEpoch
         (maxN (maxAccGet (mMaxAcc s1) p0 pEpoch) pIdx))
       (mLeaks s1) (mCorrs s1))

def mChallContainsE
    {O' : Ops S} {Γ} (K : ℕ) (s : Expr O' Γ mirrorTy) (pos : Expr O' Γ posTy) :
    Expr O' Γ .bool :=
  .letE (.pair s pos)
    (.anyB K (mChall (.fst .v0)) (posEq .v0 (.snd .v1)))

def mAfterCorrE
    {O' : Ops S} {Γ} (K : ℕ) (s : Expr O' Γ mirrorTy) (p : Expr O' Γ .bool) :
    Expr O' Γ mirrorTy :=
  .letE (.pair s p)
    (let s0 : Expr O' _ mirrorTy := .fst .v0
     let p0 : Expr O' _ .bool := .snd .v0
     let comp' : Expr O' _ (.list posTy) :=
       .foldrB K (mTrans s0) (mComp s0)
         (.ite (boolEq (posSender (recPos .v0)) (otherE (.snd .v2)))
           (.cons (recPos .v0) .v1)
           .v1)
     let s1 : Expr O' _ mirrorTy :=
       mMk (mSt s0) (mB s0) (mWin s0) (mEpoch s0) (mIdx s0) (mTL s0)
         (mTrans s0) (mChall s0) comp' (mMaxAcc s0) (mLeaks s0) (mCorrs s0)
     let s2 : Expr O' _ mirrorTy :=
       mLeakE s1 (maxN (.fst (mEpoch s0)) (.snd (mEpoch s0)))
     mMk (mSt s2) (mB s2) (mWin s2) (mEpoch s2) (mIdx s2) (mTL s2)
       (mTrans s2) (mChall s2) (mComp s2) (mMaxAcc s2) (mLeaks s2)
       (.cons (.pair p0 (pGet (mEpoch s0) p0)) (mCorrs s2)))

@[simp] theorem mSafeChE_eval {O' : Ops S} {Γ} (Δ : ℕ) (s : Expr O' Γ mirrorTy)
    (p : Expr O' Γ .bool) (ρ : Env Γ) (st : Thm1.Mirror Msg C) (P : Party)
    (hs : s.eval ρ = mirrorEnc st) (hp : p.eval ρ = partyEnc P) :
    (mSafeChE Δ s p).eval ρ = st.safeCh Δ P := by
  simp only [mSafeChE, Expr.eval, hs, hp, healedByE_eval]
  cases P <;> simp [GameState.safeCh, mTL, mEpoch, pGet, Expr.eval, Expr.v0,
    mirrorEnc, gsEnc, partyEnc]

@[simp] theorem mLeakE_eval {O' : Ops S} {Γ} (s : Expr O' Γ mirrorTy) (l : Expr O' Γ .nat)
    (ρ : Env Γ) (st : Thm1.Mirror Msg C) (hs : s.eval ρ = mirrorEnc st) :
    (mLeakE s l).eval ρ = mirrorEnc (st.leak (l.eval ρ)) := by
  simp only [mLeakE, mMk, Expr.eval, hs, maxOptE_eval]
  simp [GameState.leak, mSt, mB, mWin, mEpoch, mIdx, mTL, mTrans, mChall,
    mComp, mMaxAcc, mLeaks, mCorrs, Expr.eval, Expr.v0, mirrorEnc, gsEnc]

@[simp] theorem mEpMgmtE_eval {O' : Ops S} {Γ} (Δ qep : ℕ) (s : Expr O' Γ mirrorTy)
    (p : Expr O' Γ .bool) (bad : Expr O' Γ .bool) (ρ : Env Γ)
    (st : Thm1.Mirror Msg C) (P : Party)
    (hs : s.eval ρ = mirrorEnc st) (hp : p.eval ρ = partyEnc P) :
    (mEpMgmtE Δ qep s p bad).eval ρ = (st.epMgmt Δ qep P (bad.eval ρ)).map mirrorEnc := by
  unfold mEpMgmtE GameState.epMgmt
  rw [letE_eval]
  have h0 : (Expr.pair s (.pair p bad)).eval ρ = (mirrorEnc st, partyEnc P, bad.eval ρ) := by
    simp [Expr.eval, hs, hp]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod mirrorTy (.prod .bool .bool))
    (mirrorEnc st, partyEnc P, bad.eval ρ) ρ
  rw [ite_eval]
  have hSends : (sendsInE (.fst (.snd (Expr.v0 (O := O'))))
      (.add (pGet (mEpoch (.fst (Expr.v0 (O := O')))) (.fst (.snd (Expr.v0 (O := O')))))
        (.nat 1))).eval ρ₁ = P.sendsIn (st.epoch P + 1) := by
    rw [sendsInE_eval _ _ ρ₁ P rfl]
    congr 1
    cases P <;> simp [ρ₁, pGet, mEpoch, mirrorEnc, gsEnc, partyEnc, Expr.eval, Expr.v0]
  rw [hSends]
  by_cases h1 : P.sendsIn (st.epoch P + 1)
  · simp only [h1, ↓reduceIte]
    rw [ite_eval]
    have hlt1 : (Expr.lt (.nat qep) (.add (pGet (mEpoch (.fst (Expr.v0 (O := O'))))
        (.fst (.snd (Expr.v0 (O := O'))))) (.nat 1))).eval ρ₁ =
        decide (qep < st.epoch P + 1) := by
      cases P <;> simp [ρ₁, pGet, mEpoch, mirrorEnc, gsEnc, partyEnc, Expr.eval, Expr.v0]
    rw [hlt1]
    by_cases h2 : qep < st.epoch P + 1
    · simp [h2, Expr.eval]
    · simp only [h2, decide_false, Bool.false_eq_true, ↓reduceIte, Option.map_some]
      rw [letE_eval, ite_eval]
      have hCond : (Expr.and (.snd (.snd (Expr.v0 (O := O'))))
          (.not (mSafeChE Δ (.fst (Expr.v0 (O := O')))
            (.fst (.snd (Expr.v0 (O := O'))))))).eval ρ₁ =
          (bad.eval ρ && !(st.safeCh Δ P)) := by
        have hsafe := mSafeChE_eval Δ (.fst (Expr.v0 (O := O'))) (.fst (.snd (Expr.v0 (O := O'))))
          ρ₁ st P rfl rfl
        simp only [Expr.eval, hsafe]
        rfl
      have hLeak : (mLeakE (.fst (Expr.v0 (O := O')))
          (.add (pGet (mEpoch (.fst (Expr.v0 (O := O')))) (.fst (.snd (Expr.v0 (O := O')))))
            (.nat 1))).eval ρ₁ = mirrorEnc (st.leak (st.epoch P + 1)) := by
        rw [mLeakE_eval (.fst (Expr.v0 (O := O'))) _ ρ₁ st rfl]
        congr 2
        cases P <;> simp [ρ₁, pGet, mEpoch, mirrorEnc, gsEnc, partyEnc, Expr.eval, Expr.v0]
      have hBase : (Expr.fst (Expr.v0 (O := O'))).eval ρ₁ = mirrorEnc st := rfl
      rw [hCond, hLeak, hBase]
      set st₁ := if (bad.eval ρ && !(st.safeCh Δ P)) = true then st.leak (st.epoch P + 1) else st
      have hst₁ : (if (bad.eval ρ && !(st.safeCh Δ P)) = true
          then (mirrorEnc (st.leak (st.epoch P + 1)) :
            (@mirrorTy Key St St₂ Msg Coins RCoins C).denote)
          else mirrorEnc st) = mirrorEnc st₁ := by
        dsimp only [st₁]; split_ifs <;> rfl
      rw [hst₁]
      cases P <;>
        simp [ρ₁, mMk, mSt, mB, mWin, mEpoch, mIdx, mTL, mTrans, mChall, mComp,
          mMaxAcc, mLeaks, mCorrs, pGet, pSet, mirrorEnc, gsEnc, partyEnc, Function.update,
          Expr.eval, Expr.v0, Expr.v1]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    rw [ite_eval]
    have hlt2 : (Expr.lt (.nat qep) (pGet (mEpoch (.fst (Expr.v0 (O := O'))))
        (.fst (.snd (Expr.v0 (O := O')))))).eval ρ₁ = decide (qep < st.epoch P) := by
      cases P <;> simp [ρ₁, pGet, mEpoch, mirrorEnc, gsEnc, partyEnc, Expr.eval, Expr.v0]
    rw [hlt2]
    by_cases h2 : qep < st.epoch P <;> simp [ρ₁, h2, Expr.eval, Expr.v0]

@[simp] theorem mRecordE_eval {O' : Ops S} {Γ} (Δ : ℕ) (s : Expr O' Γ mirrorTy)
    (p : Expr O' Γ .bool) (r : Expr O' Γ recTy) (isChall : Expr O' Γ .bool) (ρ : Env Γ)
    (st : Thm1.Mirror Msg C) (P : Party) (rec_ : Record Msg C)
    (hs : s.eval ρ = mirrorEnc st) (hp : p.eval ρ = partyEnc P) (hr : r.eval ρ = recEnc rec_) :
    (mRecordE Δ s p r isChall).eval ρ =
      mirrorEnc (st.record Δ P () rec_ (isChall.eval ρ)) := by
  unfold mRecordE
  rw [letE_eval]
  have h0 : (Expr.pair s (.pair p (.pair r isChall))).eval ρ =
      (mirrorEnc st, partyEnc P, recEnc rec_, isChall.eval ρ) := by
    simp [Expr.eval, hs, hp, hr]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod mirrorTy (.prod .bool (.prod recTy .bool)))
    (mirrorEnc st, partyEnc P, recEnc rec_, isChall.eval ρ) ρ
  have hSafe : (mSafeChE Δ (.fst (Expr.v0 (O := O'))) (.fst (.snd (Expr.v0 (O := O'))))).eval ρ₁ =
      st.safeCh Δ P :=
    mSafeChE_eval Δ (.fst .v0) (.fst (.snd .v0)) ρ₁ st P rfl rfl
  simp only [mMk, Expr.eval, hSafe]
  cases P <;> cases hch : isChall.eval ρ <;>
  by_cases hsafeA : st.safeCh Δ .A <;> by_cases hsafeB : st.safeCh Δ .B <;>
  simp [ρ₁, GameState.record, mSt, mB, mWin, mEpoch, mIdx, mTL, mTrans,
    mChall, mComp, mMaxAcc, mLeaks, mCorrs, recPos, posIdx, pSet,
    hch, hsafeA, hsafeB, mirrorEnc, gsEnc, recEnc, posEnc, partyEnc, Function.update,
    Expr.eval, Expr.v0]

@[simp] theorem mInTransitE_eval [DecidableEq C] {Γ} (K : ℕ) (s : Expr OO Γ mirrorTy)
    (qParty : Expr OO Γ .bool) (c : Expr OO Γ (.base .ct)) (ρ : Env Γ)
    (st : Thm1.Mirror Msg C) (Q : Party)
    (heqCt : eqCt = (· == ·))
    (hK : st.trans.length ≤ K)
    (hs : s.eval ρ = mirrorEnc st) (hq : qParty.eval ρ = partyEnc Q) :
    (mInTransitE K s qParty c).eval ρ = (st.inTransit Q (c.eval ρ)).map recEnc := by
  have htake : ((st.trans.map recEnc).take K) = st.trans.map recEnc :=
    List.take_of_length_le (by simpa using hK)
  simp only [mInTransitE, GameState.inTransit, mTrans, recPos, posSender, recCt,
    Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ,
    boolEq_eval, smOps, hs, hq, heqCt, mirrorEnc, gsEnc, htake]
  rw [find?_map_eq]
  congr 2
  funext ⟨⟨sender, ep, idx⟩, msg, ct⟩
  cases sender <;> cases Q <;> rfl

theorem mDeleteE_eval_trunc {O' : Ops S} {Γ} (K : ℕ) (s : Expr O' Γ mirrorTy)
    (pos : Expr O' Γ posTy) (ρ : Env Γ) (st : Thm1.Mirror Msg C) (p : Pos)
    (hTrans : st.trans.length ≤ K) (hChall : st.chall.length ≤ K)
    (hs : s.eval ρ = mirrorEnc st) (hp : pos.eval ρ = posEnc p) :
    (mDeleteE K s pos).eval ρ =
      mirrorEnc ({ st with comp := st.comp.take K }.delete p) := by
  have ht1 : (st.trans.map recEnc).take K = st.trans.map recEnc :=
    List.take_of_length_le (by simpa using hTrans)
  have ht2 : (st.chall.map posEnc).take K = st.chall.map posEnc :=
    List.take_of_length_le (by simpa using hChall)
  have ht3 : (st.comp.map posEnc).take K = (st.comp.take K).map posEnc := by
    rw [List.map_take]
  simp only [mDeleteE, GameState.delete, mMk, mSt, mB, mWin, mEpoch, mIdx, mTL, mTrans,
    mChall, mComp, mMaxAcc, mLeaks, mCorrs, recPos, Expr.eval, Expr.v0, Expr.v1, Expr.v2,
    Env.get_cons_zero, Env.get_cons_succ, posEq_eval, hs, hp, mirrorEnc, gsEnc, ht1, ht2, ht3]
  rw [foldr_filter_map, foldr_filter_map, foldr_filter_map]
  simp [recEnc, posDec_posEnc, bne]

theorem mAcceptE_eval_trunc {O' : Ops S} {Γ} (K : ℕ) (s : Expr O' Γ mirrorTy)
    (p : Expr O' Γ .bool) (pos : Expr O' Γ posTy) (ρ : Env Γ)
    (st : Thm1.Mirror Msg C) (P : Party) (pos₀ : Pos)
    (hTrans : st.trans.length ≤ K) (hChall : st.chall.length ≤ K)
    (hs : s.eval ρ = mirrorEnc st) (hp : p.eval ρ = partyEnc P) (hpos : pos.eval ρ = posEnc pos₀) :
    (mAcceptE K s p pos).eval ρ =
      mirrorEnc ({ st with comp := st.comp.take K }.accept P () pos₀) := by
  have hdel := mDeleteE_eval_trunc K s pos ρ st pos₀ hTrans hChall hs hpos
  simp only [mAcceptE, mMk, Expr.eval, hdel, hp, hpos]
  cases P <;>
  · simp [GameState.accept, mSt, mB, mWin, mEpoch, mIdx, mTL, mTrans,
      mChall, mComp, mMaxAcc, mLeaks, mCorrs, posEpoch, posIdx, pGet, pSet,
      maxAccGet, maxAccSet, maxN_eval, mirrorEnc, gsEnc, posEnc, partyEnc,
      Function.update, Expr.eval, Expr.v0]
    funext j; split_ifs with hj <;> simp [hj]

@[simp] theorem mChallContainsE_eval {O' : Ops S} {Γ} (K : ℕ) (s : Expr O' Γ mirrorTy)
    (pos : Expr O' Γ posTy) (ρ : Env Γ) (st : Thm1.Mirror Msg C) (pos₀ : Pos)
    (hChall : st.chall.length ≤ K) (hs : s.eval ρ = mirrorEnc st)
    (hpos : pos.eval ρ = posEnc pos₀) :
    (mChallContainsE K s pos).eval ρ = st.chall.contains pos₀ := by
  have ht : (st.chall.map posEnc).take K = st.chall.map posEnc :=
    List.take_of_length_le (by simpa using hChall)
  simp only [mChallContainsE, mChall, Expr.eval, Expr.v0, Expr.v1,
    Env.get_cons_zero, Env.get_cons_succ, posEq_eval, hs, hpos, mirrorEnc, gsEnc, ht]
  rw [any_map_eq]
  simp only [posDec_posEnc]
  exact any_beq_eq_contains pos₀ st.chall

@[simp] theorem mAfterCorrE_eval {O' : Ops S} {Γ} (K : ℕ) (s : Expr O' Γ mirrorTy)
    (p : Expr O' Γ .bool) (ρ : Env Γ) (st : Thm1.Mirror Msg C) (P : Party)
    (hTrans : st.trans.length ≤ K)
    (hs : s.eval ρ = mirrorEnc st) (hp : p.eval ρ = partyEnc P) :
    (mAfterCorrE K s p).eval ρ = mirrorEnc (st.afterCorr P) := by
  have htTrans : (st.trans.map recEnc).take K = st.trans.map recEnc :=
    List.take_of_length_le (by simpa using hTrans)
  simp only [mAfterCorrE, mLeakE, maxOptE, mMk, mSt, mB, mWin, mEpoch, mIdx, mTL,
    mTrans, mChall, mComp, mMaxAcc, mLeaks, mCorrs, recPos, posSender, otherE,
    Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get_cons_zero, Env.get_cons_succ,
    boolEq_eval, maxN_eval, hs, hp, mirrorEnc, gsEnc, htTrans]
  rw [foldr_filter_map_proj]
  have hflt : (st.trans.filter fun x => (recEnc x).1.1 == !partyEnc P) =
      (st.trans.filter fun r => r.pos.sender == P.other) := by
    congr 1; funext r; simp [recEnc, posEnc, ← partyEnc_other, partyEnc_beq]
  rw [hflt]
  cases P <;>
  · simp only [GameState.afterCorr, GameState.leak, maxOpt, pGet, recEnc, posEnc, partyEnc,
      List.map_append, List.map_map, Function.comp_def, Expr.eval, Expr.v0, Env.get_cons_zero]
    cases st.tL <;> rfl

end MirrorBookkeeping

/-! ## Costed simulator handlers and reduction programs -/

section SimProg

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
local notation "SIface" =>
  smIface Key St St₂ Msg Coins RCoins C stSort sampKey sampCoins sampRCoins
local notation "SCodec" => smCodec Key St St₂ Msg Coins RCoins C stSort
local notation "SQ" => smQ Key St St₂ Msg Coins RCoins C
local notation "SR" => smR Key St St₂ Msg Coins RCoins C stSort

def simSendC (realEpoch : Option ℕ) {Γ}
    (p : Expr OO Γ .bool) (ep : Expr OO Γ .nat)
    (mb : Expr OO Γ (.base .msg)) (r : Expr OO Γ (.opt (.base .coins))) :
    Comp OO SIface Γ (.opt (.base .ct)) :=
  match realEpoch with
  | none =>
    rdsl do
      query (I := SIface) SMTag.tr (p, mb, r)
  | some i =>
    rdsl do
      if ep == nat i then
        query (I := SIface) SMTag.ch (p, Expr.op (O := OO) SMOp.blank mb, mb, r)
      else
        let mb' := if ep < nat i then Expr.op (O := OO) SMOp.blank mb else mb
        query (I := SIface) SMTag.tr (p, mb', r)

def simTransmitC (Δ qep : ℕ) {Γ}
    (s : Expr OO Γ mirrorTy)
    (arg : Expr OO Γ (.prod .bool (.prod (.base .msg) (.opt (.base .coins))))) :
    Comp OO SIface Γ (.prod (.opt (.base .ct)) mirrorTy) :=
  rdsl do
    (s0, q@(p, m, rCoins)) ← return (s, arg)
    res ← query (I := SIface) SMTag.tr q
    match res with
    | none => return (none, s0)
    | some c =>
      match mEpMgmtE Δ qep s0 p (isSomeE rCoins) with
      | none => return (some c, s0)
      | some s₁ =>
        let pos := (p, pGet (mEpoch s₁) p, pGet (mIdx s₁) p + 1)
        let rec_ := (pos, m, c)
        return (some c, mRecordE Δ s₁ p rec_ false)

def simChallC (Δ qep : ℕ) (realEpoch : Option ℕ) {Γ}
    (s : Expr OO Γ mirrorTy)
    (arg : Expr OO Γ
      (.prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .coins)))))) :
    Comp OO SIface Γ (.prod (.opt (.base .ct)) mirrorTy) :=
  rdsl do
    (s0, (p, m₀, m₁, rCoins)) ← return (s, arg)
    match mEpMgmtE Δ qep s0 p (isSomeE rCoins) with
    | none => return (none, s0)
    | some s₁ =>
      if !(mSafeChE Δ s₁ p) then
        return (none, s0)
      else
        let mb := if mB s0 then m₁ else m₀
        cOpt ← simSendC realEpoch p (pGet (mEpoch s₁) p) mb rCoins
        match cOpt with
        | none => return (none, s0)
        | some c =>
          let pos := (p, pGet (mEpoch s₁) p, pGet (mIdx s₁) p + 1)
          let rec_ := (pos, mb, c)
          return (some c, mRecordE Δ s₁ p rec_ true)

def simDeliverC (K : ℕ) {Γ}
    (s : Expr OO Γ mirrorTy)
    (arg : Expr OO Γ (.prod .bool (.base .ct))) :
    Comp OO SIface Γ (.prod (.opt (smRrTy Key St St₂ Msg Coins RCoins C)) mirrorTy) :=
  rdsl do
    (s0, q@(p, c)) ← return (s, arg)
    res ← query (I := SIface) SMTag.dl q
    match res with
    | none => return (none, s0)
    | some rr =>
      match rr with
      | .inl _ => return (some (.inl ()), s0)
      | .inr tim@(t', i', m) =>
        match mInTransitE K s0 (otherE p) c with
        | none => return (some (.inr tim), s0)
        | some r =>
          let rPos := recPos r
          let mOut := if mChallContainsE K s0 rPos then none else m
          return (some (.inr (t', i', mOut)), mAcceptE K s0 p rPos)

def simInjectC (K : ℕ) {Γ}
    (s : Expr OO Γ mirrorTy)
    (arg : Expr OO Γ (.prod .bool (.base .ct))) :
    Comp OO SIface Γ (.prod (.opt (smRrTy Key St St₂ Msg Coins RCoins C)) mirrorTy) :=
  rdsl do
    (s0, q@(p, _)) ← return (s, arg)
    res ← query (I := SIface) SMTag.ij q
    match res with
    | none => return (none, s0)
    | some rr =>
      match rr with
      | .inl _ => return (some (.inl ()), s0)
      | .inr tim@(t', i', _) =>
        let pos := (otherE p, t', i')
        return (some (.inr tim), mAcceptE K s0 p pos)

def simCorrC (K : ℕ) {Γ}
    (s : Expr OO Γ mirrorTy)
    (p : Expr OO Γ .bool) :
    Comp OO SIface Γ (.prod (.opt (.base stSort)) mirrorTy) :=
  rdsl do
    (s0, p0) ← return (s, p)
    res ← query (I := SIface) SMTag.cr p0
    if isSomeE res then
      return (res, mAfterCorrE K s0 p0)
    else
      return (res, s0)

def simHandleC (K Δ qep : ℕ) (realEpoch : Option ℕ) :
    Comp OO SIface [mirrorTy, SQ] (.prod SR mirrorTy) :=
  rdsl [st, qry] do
    match qry with
    | .transmit qTr =>
      res ← simTransmitC Δ qep st qTr
      return (.inl (.inl (.inl (.inl res.1))), res.2)
    | .challenge qCh =>
      res ← simChallC Δ qep realEpoch st qCh
      return (.inl (.inl (.inl (.inr res.1))), res.2)
    | .deliver qDl =>
      res ← simDeliverC K st qDl
      return (.inl (.inl (.inr res.1)), res.2)
    | .inject qIj =>
      res ← simInjectC K st qIj
      return (.inl (.inr res.1), res.2)
    | .corrupt p =>
      res ← simCorrC K st p
      return (.inr res.1, res.2)

def simInitC : Comp OO SIface [.unit] (.prod .unit mirrorTy) :=
  rdsl [_] do
    b ← sample (I := SIface) SMSamp.bit ()
    return ((),
      mMk ((), ()) b false
        (0, 0) (0, 0)
        none [] [] []
        (tconst 0, tconst 0)
        [] [])

/-- Costed `Thm1.challSim` simulator (`B1` / `B2` of ACD19 Lemmas 16 and 17). -/
@[reducible] def challSimProg (K Δ qep : ℕ) :
    CostedReduction OO SIface
      (SM.spec (SMSort.den Key St St₂ Msg Coins RCoins C stSort) Msg Coins C)
      SCodec .unit .unit .bool .bool where
  σ := mirrorTy
  init := simInitC
  handle := simHandleC K Δ qep none
  finish := rdsl [_, b'] do return b'

/-- Costed `ThmB.privRedB` simulator (`B3,i` of ACD19 Lemma 18 with blanking map `SMOp.blank`). -/
@[reducible] def privRedBProg (K Δ qep i : ℕ) :
    CostedReduction OO SIface
      (SM.spec (SMSort.den Key St St₂ Msg Coins RCoins C stSort) Msg Coins C)
      SCodec .unit .unit .bool .bool where
  σ := mirrorTy
  init := simInitC
  handle := simHandleC K Δ qep (some i)
  finish := rdsl [st, b'] do return boolEq (mB st) b'

/-! ## Step-level evaluation agreement -/

@[simp] theorem query_tr_eval {Γ}
    (e : Expr OO Γ (.prod .bool (.prod (.base .msg) (.opt (.base .coins))))) (ρ : Env Γ) :
    (Comp.query (I := SIface) SMTag.tr e).eval ρ =
      transmitQuery (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
        (partyDec (e.eval ρ).1) (e.eval ρ).2.1 (e.eval ρ).2.2 := by
  simp [Comp.eval, smIface, transmitQuery]

@[simp] theorem query_ch_eval {Γ}
    (e : Expr OO Γ (.prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .coins))))))
    (ρ : Env Γ) :
    (Comp.query (I := SIface) SMTag.ch e).eval ρ =
      challQuery (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
        (partyDec (e.eval ρ).1) (e.eval ρ).2.1 (e.eval ρ).2.2.1 (e.eval ρ).2.2.2 := by
  simp [Comp.eval, smIface, challQuery]

@[simp] theorem query_dl_eval {Γ}
    (e : Expr OO Γ (.prod .bool (.base .ct))) (ρ : Env Γ) :
    (Comp.query (I := SIface) SMTag.dl e).eval ρ =
      Option.map smRrEnc <$>
        deliverQuery (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort) (Coins := Coins)
          (partyDec (e.eval ρ).1) (e.eval ρ).2 := by
  simp [Comp.eval, smIface, deliverQuery]

@[simp] theorem query_ij_eval {Γ}
    (e : Expr OO Γ (.prod .bool (.base .ct))) (ρ : Env Γ) :
    (Comp.query (I := SIface) SMTag.ij e).eval ρ =
      Option.map smRrEnc <$>
        injectQuery (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort) (Coins := Coins)
          (partyDec (e.eval ρ).1) (e.eval ρ).2 := by
  simp [Comp.eval, smIface, injectQuery]

@[simp] theorem query_cr_eval {Γ}
    (e : Expr OO Γ .bool) (ρ : Env Γ) :
    (Comp.query (I := SIface) SMTag.cr e).eval ρ =
      corrQuery (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
        (Msg := Msg) (Coins := Coins) (C := C) (partyDec (e.eval ρ)) := by
  simp [Comp.eval, smIface, corrQuery]

theorem simSendC_eval_none {Γ}
    (p : Expr OO Γ .bool) (ep : Expr OO Γ .nat)
    (mb : Expr OO Γ (.base .msg)) (r : Expr OO Γ (.opt (.base .coins)))
    (ρ : Env Γ) (P : Party) (hp : p.eval ρ = partyEnc P) :
    (simSendC (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
      (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
      none p ep mb r).eval ρ =
      Thm1.simSend (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
        (fun _ => none) none P (ep.eval ρ) (mb.eval ρ) (r.eval ρ) := by
  simp [simSendC, Thm1.simSend, Expr.eval, hp, partyDec_partyEnc]

theorem simSendC_eval_some (i : ℕ) {Γ}
    (p : Expr OO Γ .bool) (ep : Expr OO Γ .nat)
    (mb : Expr OO Γ (.base .msg)) (r : Expr OO Γ (.opt (.base .coins)))
    (ρ : Env Γ) (P : Party) (hp : p.eval ρ = partyEnc P) :
    (simSendC (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
      (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
      (some i) p ep mb r).eval ρ =
      ThmB.simSend (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
        (fun t => if t < i then some blank else none) (some (i, blank))
        P (ep.eval ρ) (mb.eval ρ) (r.eval ρ) := by
  simp only [simSendC, ThmB.simSend, Comp.eval_ite, Expr.eval]
  by_cases hti : ep.eval ρ = i
  · simp [hti, query_ch_eval, Expr.eval, smOps, hp, partyDec_partyEnc]
  · by_cases hlt : ep.eval ρ < i <;>
    simp [hti, hlt, query_tr_eval, Expr.eval, smOps, hp, partyDec_partyEnc]

@[simp] theorem stateT_lift_run {m : Type → Type} [Monad m] {σ α : Type}
    (x : m α) (s : σ) :
    (StateT.lift x : StateT σ m α).run s = (x >>= fun a => pure (a, s)) := rfl

theorem Comp.eval_caseSum_v0_inr {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ} {t₁ t₂ u : Ty S} (x : t₂.denote)
    (lB : Comp OO I (t₁ :: .sum t₁ t₂ :: Γ) u)
    (rB : Comp OO I (t₂ :: .sum t₁ t₂ :: Γ) u) (ρ : Env Γ) :
    (Comp.caseSum .v0 lB rB).eval (Env.cons (t := .sum t₁ t₂) (.inr x) ρ) =
      rB.eval (Env.cons (t := t₂) x (Env.cons (t := .sum t₁ t₂) (.inr x) ρ)) := rfl

@[simp] theorem simImpl_inl [DecidableEq C] (Δ qep : ℕ) (challMsg : ℕ → Option Msg)
    (challEpoch : Option (ℕ × Msg)) (n : ℕ) :
    Thm1.simImpl (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
      (Coins := Coins) (C := C) Δ qep challMsg challEpoch (.inl n) =
      StateT.lift (query (spec := unifSpec +
        SM.spec (SMSort.den Key St St₂ Msg Coins RCoins C stSort) Msg Coins C) (.inl n)) := rfl

@[simp] theorem simImpl_tr [DecidableEq C] (Δ qep : ℕ) (challMsg : ℕ → Option Msg)
    (challEpoch : Option (ℕ × Msg)) (q : Party × Msg × Option Coins) :
    Thm1.simImpl (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
      (Coins := Coins) (C := C) Δ qep challMsg challEpoch
      (.inr (.inl (.inl (.inl (.inl q))))) =
      Thm1.simTransmit Δ qep q := rfl

@[simp] theorem simImpl_ch [DecidableEq C] (Δ qep : ℕ) (challMsg : ℕ → Option Msg)
    (challEpoch : Option (ℕ × Msg)) (q : Party × Msg × Msg × Option Coins) :
    Thm1.simImpl (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
      (Coins := Coins) (C := C) Δ qep challMsg challEpoch
      (.inr (.inl (.inl (.inl (.inr q))))) =
      Thm1.simChall Δ qep challMsg challEpoch q := rfl

@[simp] theorem simImpl_dl [DecidableEq C] (Δ qep : ℕ) (challMsg : ℕ → Option Msg)
    (challEpoch : Option (ℕ × Msg)) (q : Party × C) :
    Thm1.simImpl (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
      (Coins := Coins) (C := C) Δ qep challMsg challEpoch
      (.inr (.inl (.inl (.inr q)))) =
      Thm1.simDeliver q := rfl

@[simp] theorem simImpl_ij [DecidableEq C] (Δ qep : ℕ) (challMsg : ℕ → Option Msg)
    (challEpoch : Option (ℕ × Msg)) (q : Party × C) :
    Thm1.simImpl (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
      (Coins := Coins) (C := C) Δ qep challMsg challEpoch
      (.inr (.inl (.inr q))) =
      Thm1.simInject q := rfl

@[simp] theorem simImpl_cr [DecidableEq C] (Δ qep : ℕ) (challMsg : ℕ → Option Msg)
    (challEpoch : Option (ℕ × Msg)) (P : Party) :
    Thm1.simImpl (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
      (Coins := Coins) (C := C) Δ qep challMsg challEpoch
      (.inr (.inr P)) =
      Thm1.simCorr P := rfl

@[simp] theorem simImplB_inl [DecidableEq C] (Δ qep : ℕ) (challMsg : ℕ → Option (Msg → Msg))
    (challEpoch : Option (ℕ × (Msg → Msg))) (n : ℕ) :
    ThmB.simImpl (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
      (Coins := Coins) (C := C) Δ qep challMsg challEpoch (.inl n) =
      StateT.lift (query (spec := unifSpec +
        SM.spec (SMSort.den Key St St₂ Msg Coins RCoins C stSort) Msg Coins C) (.inl n)) := rfl

@[simp] theorem simImplB_tr [DecidableEq C] (Δ qep : ℕ) (challMsg : ℕ → Option (Msg → Msg))
    (challEpoch : Option (ℕ × (Msg → Msg))) (q : Party × Msg × Option Coins) :
    ThmB.simImpl (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
      (Coins := Coins) (C := C) Δ qep challMsg challEpoch
      (.inr (.inl (.inl (.inl (.inl q))))) =
      Thm1.simTransmit Δ qep q := rfl

@[simp] theorem simImplB_ch [DecidableEq C] (Δ qep : ℕ) (challMsg : ℕ → Option (Msg → Msg))
    (challEpoch : Option (ℕ × (Msg → Msg))) (q : Party × Msg × Msg × Option Coins) :
    ThmB.simImpl (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
      (Coins := Coins) (C := C) Δ qep challMsg challEpoch
      (.inr (.inl (.inl (.inl (.inr q))))) =
      ThmB.simChall Δ qep challMsg challEpoch q := rfl

@[simp] theorem simImplB_dl [DecidableEq C] (Δ qep : ℕ) (challMsg : ℕ → Option (Msg → Msg))
    (challEpoch : Option (ℕ × (Msg → Msg))) (q : Party × C) :
    ThmB.simImpl (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
      (Coins := Coins) (C := C) Δ qep challMsg challEpoch
      (.inr (.inl (.inl (.inr q)))) =
      Thm1.simDeliver q := rfl

@[simp] theorem simImplB_ij [DecidableEq C] (Δ qep : ℕ) (challMsg : ℕ → Option (Msg → Msg))
    (challEpoch : Option (ℕ × (Msg → Msg))) (q : Party × C) :
    ThmB.simImpl (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
      (Coins := Coins) (C := C) Δ qep challMsg challEpoch
      (.inr (.inl (.inr q))) =
      Thm1.simInject q := rfl

@[simp] theorem simImplB_cr [DecidableEq C] (Δ qep : ℕ) (challMsg : ℕ → Option (Msg → Msg))
    (challEpoch : Option (ℕ × (Msg → Msg))) (P : Party) :
    ThmB.simImpl (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
      (Coins := Coins) (C := C) Δ qep challMsg challEpoch
      (.inr (.inr P)) =
      Thm1.simCorr P := rfl

theorem simTransmitC_eval (Δ qep : ℕ) {Γ}
    (s : Expr OO Γ mirrorTy)
    (arg : Expr OO Γ (.prod .bool (.prod (.base .msg) (.opt (.base .coins)))))
    (ρ : Env Γ) (st : Thm1.Mirror Msg C) (P : Party) (m : Msg) (r : Option Coins)
    (hs : s.eval ρ = mirrorEnc st) (harg : arg.eval ρ = (partyEnc P, m, r)) :
    (simTransmitC (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
      (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
      Δ qep s arg).eval ρ =
      Prod.map id mirrorEnc <$>
        ((Thm1.simTransmit (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          Δ qep (P, m, r)).run st) := by
  unfold simTransmitC Thm1.simTransmit
  rw [Comp.eval_bind_ret]
  have h0 : (Expr.pair s arg).eval ρ = (mirrorEnc st, partyEnc P, m, r) := by
    simp [Expr.eval, hs, harg]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := (.prod mirrorTy (.prod .bool (.prod (.base .msg) (.opt (.base .coins)))) : Ty S))
    (mirrorEnc st, partyEnc P, m, r) ρ
  have htr : (Comp.query (I := SIface) SMTag.tr (.snd (Expr.v0 (O := OO)))).eval ρ₁ =
      transmitQuery (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort) P m r := by
    rw [query_tr_eval]
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
    · simp [ρ₂, ρ₁, Comp.eval_ret, Expr.eval, Expr.v0, Expr.v2, StateT.run_pure]
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

theorem simChallC_eval_aux (Δ qep : ℕ) (realEpoch : Option ℕ)
    (sendFn : Party → ℕ → Msg → Option Coins →
      AdversaryComp (SMSort.den Key St St₂ Msg Coins RCoins C stSort) Msg Coins C (Option C))
    (hSend : ∀ {Γ'} (p : Expr OO Γ' .bool) (ep : Expr OO Γ' .nat)
      (mb : Expr OO Γ' (.base .msg)) (r : Expr OO Γ' (.opt (.base .coins)))
      (ρ' : Env Γ') (P : Party), p.eval ρ' = partyEnc P →
      (simSendC (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
        (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
        (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
        (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
        realEpoch p ep mb r).eval ρ' =
        sendFn P (ep.eval ρ') (mb.eval ρ') (r.eval ρ'))
    {Γ} (s : Expr OO Γ mirrorTy)
    (arg : Expr OO Γ
      (.prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .coins))))))
    (ρ : Env Γ) (st : Thm1.Mirror Msg C) (P : Party) (m₀ m₁ : Msg) (r : Option Coins)
    (hs : s.eval ρ = mirrorEnc st) (harg : arg.eval ρ = (partyEnc P, m₀, m₁, r)) :
    (simChallC (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
      (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
      Δ qep realEpoch s arg).eval ρ =
      Prod.map id mirrorEnc <$>
        (match st.epMgmt Δ qep P r.isSome with
         | none => pure (none, st)
         | some s₁ =>
           if !(s₁.safeCh Δ P) then pure (none, st)
           else do
             let mb := if st.b then m₁ else m₀
             let res ← sendFn P (s₁.epoch P) mb r
             match res with
             | none => pure (none, st)
             | some c =>
               pure (some c,
                 s₁.record Δ P () ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, mb, c⟩ true)) := by
  unfold simChallC
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
  rcases st.epMgmt Δ qep P r.isSome with _ | s₁
  · simp [ρ₁, Comp.eval_ret, Expr.eval, Expr.v0]
  · simp only [Option.map_some]
    set ρ₂ := Env.cons (t := mirrorTy) (mirrorEnc s₁) ρ₁
    rw [Comp.eval_ite]
    have hsafe : (Expr.not (mSafeChE Δ (Expr.v0 (O := OO)) (.fst (.snd .v1)))).eval ρ₂ =
        !(s₁.safeCh Δ P) := by
      simp only [Expr.eval]
      rw [mSafeChE_eval Δ .v0 (.fst (.snd .v1)) ρ₂ s₁ P rfl rfl]
    rw [hsafe]
    by_cases hsc : !(s₁.safeCh Δ P)
    · simp [ρ₂, ρ₁, hsc, Comp.eval_ret, Expr.eval, Expr.v1]
    · simp only [hsc, Bool.false_eq_true, ↓reduceIte, Comp.eval_bind, map_bind]
      have hsend : (simSendC (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
          (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
          (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
          (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
          realEpoch (.fst (.snd .v1)) (pGet (mEpoch .v0) (.fst (.snd .v1)))
          (.ite (mB (.fst .v1)) (.fst (.snd (.snd (.snd .v1)))) (.fst (.snd (.snd .v1))))
          (.snd (.snd (.snd (.snd .v1))))).eval ρ₂ =
          sendFn P (s₁.epoch P) (if st.b then m₁ else m₀) r := by
        rw [hSend _ _ _ _ ρ₂ P rfl]
        cases P <;> rfl
      rw [hsend]
      refine bind_congr fun res => ?_
      rcases res with _ | c
      · simp [ρ₂, ρ₁, Comp.eval, Expr.eval, Expr.v0, Expr.v2]
      · rw [Comp.eval_caseOpt_v0_some]
        set ρ₃ := Env.cons (t := (.base .ct : Ty S)) c
          (Env.cons (t := (.opt (.base .ct) : Ty S)) (some c) ρ₂)
        simp only [Comp.eval_ret, pair_eval, some_eval, map_pure, Prod.map]
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

theorem simChallC_eval_none (Δ qep : ℕ) {Γ}
    (s : Expr OO Γ mirrorTy)
    (arg : Expr OO Γ
      (.prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .coins))))))
    (ρ : Env Γ) (st : Thm1.Mirror Msg C) (P : Party) (m₀ m₁ : Msg) (r : Option Coins)
    (hs : s.eval ρ = mirrorEnc st) (harg : arg.eval ρ = (partyEnc P, m₀, m₁, r)) :
    (simChallC (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
      (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
      Δ qep none s arg).eval ρ =
      Prod.map id mirrorEnc <$>
        ((Thm1.simChall (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          Δ qep (fun _ => none) none (P, m₀, m₁, r)).run st) := by
  rw [simChallC_eval_aux Δ qep none _ (fun p ep mb r' ρ' P' hp' =>
    simSendC_eval_none p ep mb r' ρ' P' hp') s arg ρ st P m₀ m₁ r hs harg]
  unfold Thm1.simChall
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rcases st.epMgmt Δ qep P r.isSome with _ | s₁
  · simp [StateT.run_pure]
  · by_cases hsc : !(s₁.safeCh Δ P)
    · simp [hsc, StateT.run_pure]
    · simp only [hsc, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, stateT_lift_run,
        bind_assoc, pure_bind]
      congr 1; refine bind_congr fun res => ?_
      rcases res with _ | c <;> simp [StateT.run_pure, StateT.run_set]

theorem simChallC_eval_some (Δ qep i : ℕ) {Γ}
    (s : Expr OO Γ mirrorTy)
    (arg : Expr OO Γ
      (.prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .coins))))))
    (ρ : Env Γ) (st : Thm1.Mirror Msg C) (P : Party) (m₀ m₁ : Msg) (r : Option Coins)
    (hs : s.eval ρ = mirrorEnc st) (harg : arg.eval ρ = (partyEnc P, m₀, m₁, r)) :
    (simChallC (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
      (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
      Δ qep (some i) s arg).eval ρ =
      Prod.map id mirrorEnc <$>
        ((ThmB.simChall (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          Δ qep (fun t => if t < i then some blank else none) (some (i, blank))
          (P, m₀, m₁, r)).run st) := by
  rw [simChallC_eval_aux Δ qep (some i) _ (fun p ep mb r' ρ' P' hp' =>
    simSendC_eval_some i p ep mb r' ρ' P' hp') s arg ρ st P m₀ m₁ r hs harg]
  unfold ThmB.simChall
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rcases st.epMgmt Δ qep P r.isSome with _ | s₁
  · simp [StateT.run_pure]
  · by_cases hsc : !(s₁.safeCh Δ P)
    · simp [hsc, StateT.run_pure]
    · simp only [hsc, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, stateT_lift_run,
        bind_assoc, pure_bind]
      congr 1; refine bind_congr fun res => ?_
      rcases res with _ | c <;> simp [StateT.run_pure, StateT.run_set]

theorem simDeliverC_eval_trunc [DecidableEq C] (K : ℕ) {Γ}
    (s : Expr OO Γ mirrorTy) (arg : Expr OO Γ (.prod .bool (.base .ct)))
    (ρ : Env Γ) (st : Thm1.Mirror Msg C) (P : Party) (c : C)
    (heqCt : eqCt = (· == ·))
    (hTrans : st.trans.length ≤ K) (hChall : st.chall.length ≤ K)
    (hs : s.eval ρ = mirrorEnc st) (harg : arg.eval ρ = (partyEnc P, c)) :
    (simDeliverC (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
      (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
      K s arg).eval ρ =
      (do
        let res ← deliverQuery (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          (Coins := Coins) P c
        match res, st.inTransit P.other c with
        | some (.accepted t' i' m), some r =>
          pure (some (.inr (t', i', if st.chall.contains r.pos then none else m)),
            mirrorEnc ({ st with comp := st.comp.take K }.accept P () r.pos))
        | _, _ => pure (res.map smRrEnc, mirrorEnc st)) := by
  unfold simDeliverC
  rw [Comp.eval_bind_ret]
  have h0 : (Expr.pair s arg).eval ρ = (mirrorEnc st, partyEnc P, c) := by
    simp [Expr.eval, hs, harg]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := (.prod mirrorTy (.prod .bool (.base .ct)) : Ty S))
    (mirrorEnc st, partyEnc P, c) ρ
  have hdl : (Comp.query (I := SIface) SMTag.dl (.snd (Expr.v0 (O := OO)))).eval ρ₁ =
      Option.map smRrEnc <$>
        deliverQuery (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort) (Coins := Coins)
          P c := by
    rw [query_dl_eval]
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
      · simp [ρ₂, ρ₁, Comp.eval_ret, Expr.eval, Expr.v0, Expr.v3]
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

theorem simInjectC_eval_trunc (K : ℕ) {Γ}
    (s : Expr OO Γ mirrorTy) (arg : Expr OO Γ (.prod .bool (.base .ct)))
    (ρ : Env Γ) (st : Thm1.Mirror Msg C) (P : Party) (c : C)
    (hTrans : st.trans.length ≤ K) (hChall : st.chall.length ≤ K)
    (hs : s.eval ρ = mirrorEnc st) (harg : arg.eval ρ = (partyEnc P, c)) :
    (simInjectC (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
      (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
      K s arg).eval ρ =
      (do
        let res ← injectQuery (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          (Coins := Coins) P c
        match res with
        | some (.accepted t' i' m) =>
          pure (some (.inr (t', i', m)),
            mirrorEnc ({ st with comp := st.comp.take K }.accept P () ⟨P.other, t', i'⟩))
        | _ => pure (res.map smRrEnc, mirrorEnc st)) := by
  unfold simInjectC
  rw [Comp.eval_bind_ret]
  have h0 : (Expr.pair s arg).eval ρ = (mirrorEnc st, partyEnc P, c) := by
    simp [Expr.eval, hs, harg]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := (.prod mirrorTy (.prod .bool (.base .ct)) : Ty S))
    (mirrorEnc st, partyEnc P, c) ρ
  have hij : (Comp.query (I := SIface) SMTag.ij (.snd (Expr.v0 (O := OO)))).eval ρ₁ =
      Option.map smRrEnc <$>
        injectQuery (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort) (Coins := Coins)
          P c := by
    rw [query_ij_eval]
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

theorem simCorrC_eval (K : ℕ) {Γ}
    (s : Expr OO Γ mirrorTy) (p : Expr OO Γ .bool)
    (ρ : Env Γ) (st : Thm1.Mirror Msg C) (P : Party)
    (hTrans : st.trans.length ≤ K)
    (hs : s.eval ρ = mirrorEnc st) (hp : p.eval ρ = partyEnc P) :
    (simCorrC (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
      (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
      K s p).eval ρ =
      Prod.map id mirrorEnc <$>
        ((Thm1.simCorr (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          (Msg := Msg) (Coins := Coins) (C := C) P).run st) := by
  unfold simCorrC Thm1.simCorr
  rw [Comp.eval_bind_ret]
  have h0 : (Expr.pair s p).eval ρ = (mirrorEnc st, partyEnc P) := by
    simp [Expr.eval, hs, hp]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := (.prod mirrorTy .bool : Ty S)) (mirrorEnc st, partyEnc P) ρ
  have hcr : (Comp.query (I := SIface) SMTag.cr (.snd (Expr.v0 (O := OO)))).eval ρ₁ =
      corrQuery (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
        (Msg := Msg) (Coins := Coins) (C := C) P := by
    rw [query_cr_eval]
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

theorem handlerImpl_simHandleC_tr (K Δ qep : ℕ) (realEpoch : Option ℕ)
    (st : Thm1.Mirror Msg C) (P : Party) (m : Msg) (r : Option Coins) :
    ((handlerImpl (C := smCodec Key St St₂ Msg Coins RCoins C stSort)
      (simHandleC (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
        (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
        (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
        (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
        K Δ qep realEpoch)
      (.inr (.inl (.inl (.inl (.inl (P, m, r))))))).run (mirrorEnc st)) =
      Prod.map id mirrorEnc <$>
        ((Thm1.simTransmit (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          Δ qep (P, m, r)).run st) := by
  unfold handlerImpl simHandleC smCodec
  simp only [StateT.run_mk, Comp.eval, Expr.eval, Expr.v0, Expr.v1,
    Env.get_cons_zero, Env.get_cons_succ, bind_assoc, pure_bind]
  rw [simTransmitC_eval Δ qep .v4 (.var .zero) _ st P m r rfl rfl]
  simp

theorem handlerImpl_simHandleC_ch_none (K Δ qep : ℕ)
    (st : Thm1.Mirror Msg C) (P : Party) (m₀ m₁ : Msg) (r : Option Coins) :
    ((handlerImpl (C := smCodec Key St St₂ Msg Coins RCoins C stSort)
      (simHandleC (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
        (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
        (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
        (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
        K Δ qep none)
      (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))))).run (mirrorEnc st)) =
      Prod.map id mirrorEnc <$>
        ((Thm1.simChall (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          Δ qep (fun _ => none) none (P, m₀, m₁, r)).run st) := by
  unfold handlerImpl simHandleC smCodec
  simp only [StateT.run_mk, Comp.eval, Expr.eval, Expr.v0, Expr.v1,
    Env.get_cons_zero, Env.get_cons_succ, bind_assoc, pure_bind]
  rw [simChallC_eval_none Δ qep .v4 (.var .zero) _ st P m₀ m₁ r rfl rfl]
  simp

theorem handlerImpl_simHandleC_ch_some (K Δ qep i : ℕ)
    (st : Thm1.Mirror Msg C) (P : Party) (m₀ m₁ : Msg) (r : Option Coins) :
    ((handlerImpl (C := smCodec Key St St₂ Msg Coins RCoins C stSort)
      (simHandleC (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
        (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
        (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
        (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
        K Δ qep (some i))
      (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))))).run (mirrorEnc st)) =
      Prod.map id mirrorEnc <$>
        ((ThmB.simChall (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          Δ qep (fun t => if t < i then some blank else none) (some (i, blank))
          (P, m₀, m₁, r)).run st) := by
  unfold handlerImpl simHandleC smCodec
  simp only [StateT.run_mk, Comp.eval, Expr.eval, Expr.v0, Expr.v1,
    Env.get_cons_zero, Env.get_cons_succ, bind_assoc, pure_bind]
  rw [simChallC_eval_some Δ qep i .v4 (.var .zero) _ st P m₀ m₁ r rfl rfl]
  simp

theorem handlerImpl_simHandleC_dl_trunc [DecidableEq C] (K Δ qep : ℕ) (realEpoch : Option ℕ)
    (heqCt : eqCt = (· == ·))
    (st : Thm1.Mirror Msg C) (P : Party) (c : C)
    (hTrans : st.trans.length ≤ K) (hChall : st.chall.length ≤ K) :
    ((handlerImpl (C := smCodec Key St St₂ Msg Coins RCoins C stSort)
      (simHandleC (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
        (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
        (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
        (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
        K Δ qep realEpoch)
      (.inr (.inl (.inl (.inr (P, c)))))).run (mirrorEnc st)) =
      (do
        let res ← deliverQuery (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          (Coins := Coins) P c
        match res, st.inTransit P.other c with
        | some (.accepted t' i' m'), some r =>
          pure (some (.accepted t' i' (if st.chall.contains r.pos then none else m')),
            mirrorEnc ({ st with comp := st.comp.take K }.accept P () r.pos))
        | _, _ => pure (res, mirrorEnc st)) := by
  unfold handlerImpl simHandleC smCodec
  simp only [StateT.run_mk, Comp.eval, Expr.eval, Expr.v0, Expr.v1,
    Env.get_cons_zero, Env.get_cons_succ, bind_assoc, pure_bind]
  rw [simDeliverC_eval_trunc K .v3 (.var .zero) _ st P c heqCt hTrans hChall rfl rfl]
  simp only [bind_assoc]
  refine bind_congr fun res => ?_
  rcases res with _ | (_ | ⟨t', i', m'⟩) <;>
  rcases st.inTransit P.other c with _ | r <;>
  simp [smRrEnc, smRrDec]

theorem handlerImpl_simHandleC_ij_trunc (K Δ qep : ℕ) (realEpoch : Option ℕ)
    (st : Thm1.Mirror Msg C) (P : Party) (c : C)
    (hTrans : st.trans.length ≤ K) (hChall : st.chall.length ≤ K) :
    ((handlerImpl (C := smCodec Key St St₂ Msg Coins RCoins C stSort)
      (simHandleC (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
        (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
        (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
        (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
        K Δ qep realEpoch)
      (.inr (.inl (.inr (P, c))))).run (mirrorEnc st)) =
      (do
        let res ← injectQuery (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          (Coins := Coins) P c
        match res with
        | some (.accepted t' i' m') =>
          pure (some (.accepted t' i' m'),
            mirrorEnc ({ st with comp := st.comp.take K }.accept P () ⟨P.other, t', i'⟩))
        | _ => pure (res, mirrorEnc st)) := by
  unfold handlerImpl simHandleC smCodec
  simp only [StateT.run_mk, Comp.eval, Expr.eval, Expr.v0, Expr.v1,
    Env.get_cons_zero, Env.get_cons_succ, bind_assoc, pure_bind]
  rw [simInjectC_eval_trunc K .v2 (.var .zero) _ st P c hTrans hChall rfl rfl]
  simp only [bind_assoc]
  refine bind_congr fun res => ?_
  rcases res with _ | (_ | ⟨t', i', m'⟩) <;>
  simp [smRrEnc, smRrDec]

theorem handlerImpl_simHandleC_cr (K Δ qep : ℕ) (realEpoch : Option ℕ)
    (st : Thm1.Mirror Msg C) (P : Party)
    (hTrans : st.trans.length ≤ K) :
    ((handlerImpl (C := smCodec Key St St₂ Msg Coins RCoins C stSort)
      (simHandleC (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
        (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
        (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
        (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
        K Δ qep realEpoch)
      (.inr (.inr P))).run (mirrorEnc st)) =
      Prod.map id mirrorEnc <$>
        ((Thm1.simCorr (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          (Msg := Msg) (Coins := Coins) (C := C) P).run st) := by
  unfold handlerImpl simHandleC smCodec
  simp only [StateT.run_mk, Comp.eval, Expr.eval, Expr.v0, Expr.v1,
    Env.get_cons_zero, Env.get_cons_succ, bind_assoc, pure_bind]
  rw [simCorrC_eval K (.var (.succ .zero)) (.var .zero) _ st P hTrans rfl rfl]
  simp

/-! ## Full reduction evaluation agreement -/

def mirrorClearComp (s : Thm1.Mirror Msg C) : Thm1.Mirror Msg C :=
  { s with comp := [] }

@[simp] theorem mirrorClearComp_idem (s : Thm1.Mirror Msg C) :
    mirrorClearComp (mirrorClearComp s) = mirrorClearComp s := rfl

@[simp] theorem mirrorClearComp_b (s : Thm1.Mirror Msg C) :
    (mirrorClearComp s).b = s.b := rfl

@[simp] theorem mirrorClearComp_trans (s : Thm1.Mirror Msg C) :
    (mirrorClearComp s).trans = s.trans := rfl

@[simp] theorem mirrorClearComp_chall (s : Thm1.Mirror Msg C) :
    (mirrorClearComp s).chall = s.chall := rfl

@[simp] theorem mirrorClearComp_epoch (s : Thm1.Mirror Msg C) :
    (mirrorClearComp s).epoch = s.epoch := rfl

@[simp] theorem mirrorClearComp_idx (s : Thm1.Mirror Msg C) :
    (mirrorClearComp s).idx = s.idx := rfl

@[simp] theorem mirrorClearComp_safeCh (s : Thm1.Mirror Msg C) (Δ : ℕ) (P : Party) :
    (mirrorClearComp s).safeCh Δ P = s.safeCh Δ P := rfl

@[simp] theorem mirrorClearComp_inTransit [DecidableEq C] (s : Thm1.Mirror Msg C) (Q : Party)
    (c : C) : (mirrorClearComp s).inTransit Q c = s.inTransit Q c := rfl

@[simp] theorem mirrorClearComp_record (s : Thm1.Mirror Msg C) (Δ : ℕ) (P : Party)
    (rec_ : Record Msg C) (isChall : Bool) :
    mirrorClearComp ((mirrorClearComp s).record Δ P () rec_ isChall) =
      mirrorClearComp (s.record Δ P () rec_ isChall) := rfl

@[simp] theorem mirrorClearComp_accept (s : Thm1.Mirror Msg C) (P : Party) (pos : Pos) :
    mirrorClearComp ((mirrorClearComp s).accept P () pos) =
      mirrorClearComp (s.accept P () pos) := rfl

@[simp] theorem mirrorClearComp_accept_take (s : Thm1.Mirror Msg C) (K : ℕ) (P : Party)
    (pos : Pos) :
    mirrorClearComp ({ s with comp := s.comp.take K }.accept P () pos) =
      mirrorClearComp (s.accept P () pos) := rfl

@[simp] theorem mirrorClearComp_afterCorr (s : Thm1.Mirror Msg C) (P : Party) :
    mirrorClearComp ((mirrorClearComp s).afterCorr P) =
      mirrorClearComp (s.afterCorr P) := rfl

theorem mirrorClearComp_epMgmt (s : Thm1.Mirror Msg C) (Δ qep : ℕ) (P : Party) (bad : Bool) :
    (mirrorClearComp s).epMgmt Δ qep P bad = (s.epMgmt Δ qep P bad).map mirrorClearComp := by
  unfold GameState.epMgmt
  simp only [mirrorClearComp_epoch, mirrorClearComp_safeCh]
  by_cases h1 : P.sendsIn (s.epoch P + 1) <;>
  by_cases h2 : qep < s.epoch P + 1 <;>
  by_cases h3 : qep < s.epoch P <;>
  by_cases h4 : (bad && !s.safeCh Δ P) <;>
  simp [h1, h2, h3, h4, GameState.leak, mirrorClearComp]

theorem epMgmt_fields {St' : Type} (st s₁ : GameState St' Msg C) (Δ qep : ℕ) (P : Party)
    (bad : Bool) (h : st.epMgmt Δ qep P bad = some s₁) :
    s₁.trans = st.trans ∧ s₁.chall = st.chall ∧ s₁.b = st.b := by
  unfold GameState.epMgmt at h
  split_ifs at h
  all_goals
    simp only [Option.some.injEq] at h
    subst h
    simp [GameState.leak]

def clearCompImpl {κ : Type} {G : OracleSpec κ} {ι : Type} {T : OracleSpec ι}
    (so : QueryImpl (unifSpec + G) (StateT (Thm1.Mirror Msg C) (OracleComp T))) :
    QueryImpl (unifSpec + G) (StateT (Thm1.Mirror Msg C) (OracleComp T))
  | .inl n => so (.inl n)
  | .inr t => StateT.mk fun s => Prod.map id mirrorClearComp <$> (so (.inr t)).run s

theorem simImpl_clearComp [DecidableEq C] (Δ qep : ℕ)
    (t : (SM.spec (SMSort.den Key St St₂ Msg Coins RCoins C stSort) Msg Coins C).Domain)
    (st : Thm1.Mirror Msg C) :
    Prod.map id mirrorClearComp <$>
      ((Thm1.simImpl (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
        Δ qep (fun _ => none) none (.inr t)).run st) =
    Prod.map id mirrorClearComp <$>
      ((Thm1.simImpl (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
        Δ qep (fun _ => none) none (.inr t)).run (mirrorClearComp st)) := by
  rcases t with ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
  · simp only [simImpl_tr, Thm1.simTransmit,
      StateT.run_bind, StateT.run_get, stateT_lift_run, bind_assoc, pure_bind, map_bind,
      mirrorClearComp_epMgmt]
    refine bind_congr fun res => ?_
    rcases res with _ | c <;> rcases st.epMgmt Δ qep P r.isSome with _ | s₁ <;>
    simp [StateT.run_pure, StateT.run_set, Prod.map]
  · simp only [simImpl_ch, Thm1.simChall,
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
  · simp only [simImpl_dl, Thm1.simDeliver,
      StateT.run_bind, StateT.run_get, stateT_lift_run, bind_assoc, pure_bind, map_bind,
      mirrorClearComp_inTransit, mirrorClearComp_chall]
    refine bind_congr fun res => ?_
    rcases res with _ | (_ | ⟨t', i', m⟩) <;> rcases st.inTransit P.other c with _ | r <;>
    simp [StateT.run_pure, StateT.run_set, Prod.map]
  · simp only [simImpl_ij, Thm1.simInject,
      StateT.run_bind, StateT.run_get, stateT_lift_run, bind_assoc, pure_bind, map_bind]
    refine bind_congr fun res => ?_
    rcases res with _ | (_ | ⟨t', i', m⟩) <;>
    simp [StateT.run_pure, StateT.run_set, Prod.map]
  · simp only [simImpl_cr, Thm1.simCorr,
      StateT.run_bind, StateT.run_get, stateT_lift_run, bind_assoc, pure_bind, map_bind]
    refine bind_congr fun res => ?_
    rcases res with _ | stP <;>
    simp [StateT.run_pure, StateT.run_set, Prod.map]

theorem simImplB_clearComp [DecidableEq C] (Δ qep i : ℕ)
    (t : (SM.spec (SMSort.den Key St St₂ Msg Coins RCoins C stSort) Msg Coins C).Domain)
    (st : Thm1.Mirror Msg C) :
    Prod.map id mirrorClearComp <$>
      ((ThmB.simImpl (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
        Δ qep (fun t => if t < i then some blank else none) (some (i, blank)) (.inr t)).run st) =
    Prod.map id mirrorClearComp <$>
      ((ThmB.simImpl (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
        Δ qep (fun t => if t < i then some blank else none) (some (i, blank)) (.inr t)).run
          (mirrorClearComp st)) := by
  rcases t with ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
  · exact simImpl_clearComp Δ qep (.inl (.inl (.inl (.inl (P, m, r))))) st
  · simp only [simImplB_ch, ThmB.simChall,
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
  · exact simImpl_clearComp Δ qep (.inl (.inl (.inr (P, c)))) st
  · exact simImpl_clearComp Δ qep (.inl (.inr (P, c))) st
  · exact simImpl_clearComp Δ qep (.inr P) st

/-- Query-budget invariant on `mirrorTy.denote` for `K`-bounded Theorem 1 simulation:
with `m` adversary game queries remaining, `trans` and `chall` have length at most `K - m`. -/
def MirrorBoundInv (K m : ℕ) (v : (@mirrorTy Key St St₂ Msg Coins RCoins C).denote) : Prop :=
  (mirrorDec v).trans.length + m ≤ K ∧ (mirrorDec v).chall.length + m ≤ K

theorem MirrorBoundInv.mono {K m₁ m₂ : ℕ} {v : (@mirrorTy Key St St₂ Msg Coins RCoins C).denote}
    (hle : m₁ ≤ m₂) (h : MirrorBoundInv K m₂ v) : MirrorBoundInv K m₁ v :=
  ⟨by have := h.1; omega, by have := h.2; omega⟩

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
theorem mirrorBoundInv_record {K m Δ : ℕ} {st s₁ : Thm1.Mirror Msg C} {P : Party}
    {bad isChall : Bool} (rec_ : Record Msg C)
    (hInv : st.trans.length + (m + 1) ≤ K ∧ st.chall.length + (m + 1) ≤ K)
    (hep : st.epMgmt Δ qep P bad = some s₁) :
    MirrorBoundInv (Key := Key) (St := St) (St₂ := St₂) (Coins := Coins) (RCoins := RCoins) K m
      (mirrorEnc (s₁.record Δ P () rec_ isChall)) := by
  obtain ⟨htr, hch, -⟩ := epMgmt_fields st s₁ Δ qep P bad hep
  refine ⟨?_, ?_⟩
  · simp only [mirrorDec_mirrorEnc, GameState.record, List.length_cons, htr]
    omega
  · simp only [mirrorDec_mirrorEnc, GameState.record]
    cases isChall <;> simp only [↓reduceIte, Bool.false_eq_true, List.length_cons, hch] <;> omega

theorem mirrorBoundInv_accept_take {K m : ℕ} {st : Thm1.Mirror Msg C} (P : Party) (pos : Pos)
    (hInv : st.trans.length + (m + 1) ≤ K ∧ st.chall.length + (m + 1) ≤ K) :
    MirrorBoundInv (Key := Key) (St := St) (St₂ := St₂) (Coins := Coins) (RCoins := RCoins) K m
      (mirrorEnc ({ st with comp := st.comp.take K }.accept P () pos)) := by
  refine ⟨?_, ?_⟩
  · simp only [mirrorDec_mirrorEnc, GameState.accept, GameState.delete]
    have hle := List.length_filter_le (fun r : Record Msg C => r.pos != pos) st.trans
    omega
  · simp only [mirrorDec_mirrorEnc, GameState.accept, GameState.delete]
    have hle := List.length_filter_le (fun p : Pos => p != pos) st.chall
    omega

theorem mirrorBoundInv_afterCorr {K m : ℕ} {st : Thm1.Mirror Msg C} (P : Party)
    (hInv : st.trans.length + (m + 1) ≤ K ∧ st.chall.length + (m + 1) ≤ K) :
    MirrorBoundInv (Key := Key) (St := St) (St₂ := St₂) (Coins := Coins) (RCoins := RCoins) K m
      (mirrorEnc (st.afterCorr P)) := by
  refine ⟨?_, ?_⟩
  · simp only [mirrorDec_mirrorEnc, GameState.afterCorr, GameState.leak]
    omega
  · simp only [mirrorDec_mirrorEnc, GameState.afterCorr, GameState.leak]
    omega

theorem challSimProg_step_clearComp [DecidableEq C] (K Δ qep m : ℕ)
    (heqCt : eqCt = (· == ·))
    (t : (SM.spec (SMSort.den Key St St₂ Msg Coins RCoins C stSort) Msg Coins C).Domain)
    (v : (@mirrorTy Key St St₂ Msg Coins RCoins C).denote)
    (hInv : MirrorBoundInv K (m + 1) v) :
    (Prod.map id (mirrorClearComp ∘ mirrorDec) <$>
      (((challSimProg (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
           (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
           (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
           (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
           K Δ qep).impl (.inr t)).run v)) =
      ((clearCompImpl (Thm1.simImpl (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          Δ qep (fun _ => none) none) (.inr t)).run (mirrorClearComp (mirrorDec v))) ∧
    ∀ r ∈ support (((challSimProg (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
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
  rw [hv, clearCompImpl, StateT.run_mk, ← simImpl_clearComp Δ qep t st]
  rcases t with ((((⟨P, msg, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
  · have hrun : (((challSimProg (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
        (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
        (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
        (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
        K Δ qep).impl (.inr (.inl (.inl (.inl (.inl (P, msg, r))))))).run (mirrorEnc st)) =
      Prod.map id mirrorEnc <$>
        ((Thm1.simTransmit (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          Δ qep (P, msg, r)).run st) :=
      handlerImpl_simHandleC_tr K Δ qep none st P msg r
    rw [hrun]
    refine ⟨by rw [Functor.map_map]; congr 1; funext ⟨a, s⟩; simp [Prod.map], ?_⟩
    intro x hx
    simp only [Thm1.simTransmit, StateT.run_bind, StateT.run_get, stateT_lift_run,
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
  · have hrun : (((challSimProg (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
        (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
        (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
        (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
        K Δ qep).impl (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))))).run (mirrorEnc st)) =
      Prod.map id mirrorEnc <$>
        ((Thm1.simChall (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          Δ qep (fun _ => none) none (P, m₀, m₁, r)).run st) :=
      handlerImpl_simHandleC_ch_none K Δ qep st P m₀ m₁ r
    rw [hrun]
    refine ⟨by rw [Functor.map_map]; congr 1; funext ⟨a, s⟩; simp [Prod.map], ?_⟩
    intro x hx
    simp only [Thm1.simChall, StateT.run_bind, StateT.run_get, pure_bind] at hx
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
  · have hrun : (((challSimProg (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
        (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
        (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
        (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
        K Δ qep).impl (.inr (.inl (.inl (.inr (P, c)))))).run (mirrorEnc st)) =
      (do
        let res ← deliverQuery (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          (Coins := Coins) P c
        match res, st.inTransit P.other c with
        | some (.accepted t' i' m'), some r =>
          pure (some (.accepted t' i' (if st.chall.contains r.pos then none else m')),
            mirrorEnc ({ st with comp := st.comp.take K }.accept P () r.pos))
        | _, _ => pure (res, mirrorEnc st)) :=
      handlerImpl_simHandleC_dl_trunc K Δ qep none heqCt st P c hTrans hChall
    rw [hrun]
    refine ⟨?_, ?_⟩
    · simp only [simImpl_dl, Thm1.simDeliver,
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
  · have hrun : (((challSimProg (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
        (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
        (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
        (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
        K Δ qep).impl (.inr (.inl (.inr (P, c))))).run (mirrorEnc st)) =
      (do
        let res ← injectQuery (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          (Coins := Coins) P c
        match res with
        | some (.accepted t' i' m') =>
          pure (some (.accepted t' i' m'),
            mirrorEnc ({ st with comp := st.comp.take K }.accept P () ⟨P.other, t', i'⟩))
        | _ => pure (res, mirrorEnc st)) :=
      handlerImpl_simHandleC_ij_trunc K Δ qep none st P c hTrans hChall
    rw [hrun]
    refine ⟨?_, ?_⟩
    · simp only [simImpl_ij, Thm1.simInject,
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
  · have hrun : (((challSimProg (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
        (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
        (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
        (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
        K Δ qep).impl (.inr (.inr P))).run (mirrorEnc st)) =
      Prod.map id mirrorEnc <$>
        ((Thm1.simCorr (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          (Msg := Msg) (Coins := Coins) (C := C) P).run st) :=
      handlerImpl_simHandleC_cr K Δ qep none st P hTrans
    rw [hrun]
    refine ⟨by rw [Functor.map_map]; congr 1; funext ⟨a, s⟩; simp [Prod.map], ?_⟩
    intro x hx
    simp only [Thm1.simCorr, StateT.run_bind, StateT.run_get, stateT_lift_run,
      bind_assoc, pure_bind, map_bind, mem_support_bind_iff] at hx
    obtain ⟨res, -, hx⟩ := hx
    rcases res with _ | stP
    · simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, map_pure,
        Prod.map, support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact hInv0
    · simp only [Option.isSome_some, ↓reduceIte] at hx
      subst hx; exact mirrorBoundInv_afterCorr P hInv

theorem privRedBProg_step_clearComp [DecidableEq C] (K Δ qep i m : ℕ)
    (heqCt : eqCt = (· == ·))
    (t : (SM.spec (SMSort.den Key St St₂ Msg Coins RCoins C stSort) Msg Coins C).Domain)
    (v : (@mirrorTy Key St St₂ Msg Coins RCoins C).denote)
    (hInv : MirrorBoundInv K (m + 1) v) :
    (Prod.map id (mirrorClearComp ∘ mirrorDec) <$>
      (((privRedBProg (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
          (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
          (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
          (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
          K Δ qep i).impl (.inr t)).run v)) =
      ((clearCompImpl (ThmB.simImpl (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          Δ qep (fun t => if t < i then some blank else none) (some (i, blank)))
        (.inr t)).run (mirrorClearComp (mirrorDec v))) ∧
    ∀ r ∈ support (((privRedBProg (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
        (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
        (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
        (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
        K Δ qep i).impl (.inr t)).run v), MirrorBoundInv K m r.2 := by
  set st := mirrorDec v
  have hv : v = mirrorEnc st := (mirrorEnc_mirrorDec v).symm
  have hTrans : st.trans.length ≤ K := by
    have : st.trans.length + (m + 1) ≤ K := hInv.1; omega
  have hChall : st.chall.length ≤ K := by
    have : st.chall.length + (m + 1) ≤ K := hInv.2; omega
  have hInv0 : MirrorBoundInv (Key := Key) (St := St) (St₂ := St₂)
      (Coins := Coins) (RCoins := RCoins) K m (mirrorEnc st) := by
    rw [← hv]; exact hInv.mono (Nat.le_succ m)
  rw [hv, clearCompImpl, StateT.run_mk, ← simImplB_clearComp (blank := blank) Δ qep i t st]
  rcases t with ((((⟨P, msg, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
  · have hrun : (((privRedBProg (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
        (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
        (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
        (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
        K Δ qep i).impl (.inr (.inl (.inl (.inl (.inl (P, msg, r))))))).run (mirrorEnc st)) =
      Prod.map id mirrorEnc <$>
        ((Thm1.simTransmit (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          Δ qep (P, msg, r)).run st) :=
      handlerImpl_simHandleC_tr K Δ qep (some i) st P msg r
    rw [hrun]
    refine ⟨by rw [Functor.map_map]; congr 1; funext ⟨a, s⟩; simp [Prod.map], ?_⟩
    intro x hx
    simp only [Thm1.simTransmit, StateT.run_bind, StateT.run_get, stateT_lift_run,
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
  · have hrun : (((privRedBProg (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
        (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
        (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
        (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
        K Δ qep i).impl (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))))).run (mirrorEnc st)) =
      Prod.map id mirrorEnc <$>
        ((ThmB.simChall (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          Δ qep (fun t => if t < i then some blank else none) (some (i, blank))
          (P, m₀, m₁, r)).run st) :=
      handlerImpl_simHandleC_ch_some K Δ qep i st P m₀ m₁ r
    rw [hrun]
    refine ⟨by rw [Functor.map_map]; congr 1; funext ⟨a, s⟩; simp [Prod.map], ?_⟩
    intro x hx
    simp only [ThmB.simChall, StateT.run_bind, StateT.run_get, pure_bind] at hx
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
  · have hrun : (((privRedBProg (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
        (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
        (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
        (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
        K Δ qep i).impl (.inr (.inl (.inl (.inr (P, c)))))).run (mirrorEnc st)) =
      (do
        let res ← deliverQuery (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          (Coins := Coins) P c
        match res, st.inTransit P.other c with
        | some (.accepted t' i' m'), some r =>
          pure (some (.accepted t' i' (if st.chall.contains r.pos then none else m')),
            mirrorEnc ({ st with comp := st.comp.take K }.accept P () r.pos))
        | _, _ => pure (res, mirrorEnc st)) :=
      handlerImpl_simHandleC_dl_trunc K Δ qep (some i) heqCt st P c hTrans hChall
    rw [hrun]
    refine ⟨?_, ?_⟩
    · simp only [simImplB_dl, Thm1.simDeliver,
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
  · have hrun : (((privRedBProg (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
        (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
        (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
        (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
        K Δ qep i).impl (.inr (.inl (.inr (P, c))))).run (mirrorEnc st)) =
      (do
        let res ← injectQuery (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          (Coins := Coins) P c
        match res with
        | some (.accepted t' i' m') =>
          pure (some (.accepted t' i' m'),
            mirrorEnc ({ st with comp := st.comp.take K }.accept P () ⟨P.other, t', i'⟩))
        | _ => pure (res, mirrorEnc st)) :=
      handlerImpl_simHandleC_ij_trunc K Δ qep (some i) st P c hTrans hChall
    rw [hrun]
    refine ⟨?_, ?_⟩
    · simp only [simImplB_ij, Thm1.simInject,
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
  · have hrun : (((privRedBProg (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
        (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
        (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
        (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
        K Δ qep i).impl (.inr (.inr P))).run (mirrorEnc st)) =
      Prod.map id mirrorEnc <$>
        ((Thm1.simCorr (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
          (Msg := Msg) (Coins := Coins) (C := C) P).run st) :=
      handlerImpl_simHandleC_cr K Δ qep (some i) st P hTrans
    rw [hrun]
    refine ⟨by rw [Functor.map_map]; congr 1; funext ⟨a, s⟩; simp [Prod.map], ?_⟩
    intro x hx
    simp only [Thm1.simCorr, StateT.run_bind, StateT.run_get, stateT_lift_run,
      bind_assoc, pure_bind, map_bind, mem_support_bind_iff] at hx
    obtain ⟨res, -, hx⟩ := hx
    rcases res with _ | stP
    · simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, map_pure,
        Prod.map, support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact hInv0
    · simp only [Option.isSome_some, ↓reduceIte] at hx
      subst hx; exact mirrorBoundInv_afterCorr P hInv

theorem simImplB_step_b [DecidableEq C] (Δ qep i : ℕ)
    (q : (unifSpec +
      SM.spec (SMSort.den Key St St₂ Msg Coins RCoins C stSort) Msg Coins C).Domain)
    (st : Thm1.Mirror Msg C) :
    ∀ r ∈ support ((ThmB.simImpl (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
      Δ qep (fun t => if t < i then some blank else none) (some (i, blank)) q).run st),
      r.2.b = st.b := by
  intro r hr
  rcases q with n | ((((⟨P, msg, rCoins⟩ | ⟨P, m₀, m₁, rCoins⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
  · simp only [simImplB_inl, stateT_lift_run,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨u, -, rfl⟩ := hr; rfl
  · simp only [simImplB_tr, Thm1.simTransmit,
      StateT.run_bind, StateT.run_get, stateT_lift_run, bind_assoc, pure_bind,
      mem_support_bind_iff] at hr
    obtain ⟨res, -, hr⟩ := hr
    rcases res with _ | c
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr; subst hr; rfl
    · rcases hep : st.epMgmt Δ qep P rCoins.isSome with _ | s₁
      · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr; subst hr; rfl
      · simp only [hep] at hr
        subst hr; exact (epMgmt_fields st s₁ Δ qep P rCoins.isSome hep).2.2
  · simp only [simImplB_ch, ThmB.simChall,
      StateT.run_bind, StateT.run_get, pure_bind] at hr
    rcases hep : st.epMgmt Δ qep P rCoins.isSome with _ | s₁
    · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr; subst hr; rfl
    · simp only [hep] at hr
      by_cases hsc : !(s₁.safeCh Δ P)
      · simp only [hsc, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; rfl
      · simp only [hsc, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, stateT_lift_run,
          bind_assoc, pure_bind, mem_support_bind_iff] at hr
        obtain ⟨res, -, hr⟩ := hr
        rcases res with _ | c
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr; subst hr; rfl
        · subst hr; exact (epMgmt_fields st s₁ Δ qep P rCoins.isSome hep).2.2
  · simp only [simImplB_dl, Thm1.simDeliver,
      StateT.run_bind, StateT.run_get, stateT_lift_run, bind_assoc, pure_bind,
      mem_support_bind_iff] at hr
    obtain ⟨res, -, hr⟩ := hr
    rcases res with _ | (_ | ⟨t', i', m'⟩) <;> rcases htr : st.inTransit P.other c with _ | rec_ <;>
    simp [htr, StateT.run_pure, StateT.run_set] at hr <;> subst hr <;> rfl
  · simp only [simImplB_ij, Thm1.simInject,
      StateT.run_bind, StateT.run_get, stateT_lift_run, bind_assoc, pure_bind,
      mem_support_bind_iff] at hr
    obtain ⟨res, -, hr⟩ := hr
    rcases res with _ | (_ | ⟨t', i', m'⟩) <;>
    simp [StateT.run_pure, StateT.run_set] at hr <;> subst hr <;> rfl
  · simp only [simImplB_cr, Thm1.simCorr,
      StateT.run_bind, StateT.run_get, stateT_lift_run, bind_assoc, pure_bind,
      mem_support_bind_iff] at hr
    obtain ⟨res, -, hr⟩ := hr
    rcases res with _ | stP <;>
    simp [StateT.run_pure, StateT.run_set] at hr <;> subst hr <;> rfl

theorem simulateQ_simImplB_b [DecidableEq C] (Δ qep i : ℕ) {α : Type}
    (oa : AdversaryComp (SMSort.den Key St St₂ Msg Coins RCoins C stSort) Msg Coins C α)
    (st : Thm1.Mirror Msg C) :
    ∀ r ∈ support ((simulateQ (ThmB.simImpl
      (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
      Δ qep (fun t => if t < i then some blank else none) (some (i, blank))) oa).run st),
      r.2.b = st.b := by
  induction oa using OracleComp.inductionOn generalizing st with
  | pure a =>
    intro r hr
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr; rfl
  | query_bind q mx ih =>
    intro r hr
    rw [run_simulateQ_query_bind, mem_support_bind_iff] at hr
    obtain ⟨⟨u, s'⟩, hst, hr⟩ := hr
    exact (ih u s' r hr).trans (simImplB_step_b Δ qep i q st (u, s') hst)

theorem simInitC_eval (ρ : Env [.unit]) :
    (simInitC (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
      (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)).eval ρ =
      (do
        let b ← (liftM ($ᵗ Bool : ProbComp Bool) :
          AdversaryComp (SMSort.den Key St St₂ Msg Coins RCoins C stSort) Msg Coins C Bool)
        return ((), mirrorEnc ({ st := fun _ => (), b } : Thm1.Mirror Msg C))) := rfl

theorem isQueryBoundP_congr {ι : Type} {G : OracleSpec ι} {α : Type}
    (oa : OracleComp G α) {P₁ P₂ : ι → Prop} [d₁ : DecidablePred P₁] [d₂ : DecidablePred P₂]
    (h : P₁ = P₂) (q : ℕ) :
    oa.IsQueryBoundP P₁ q ↔ oa.IsQueryBoundP P₂ q := by
  subst h
  rw [Subsingleton.elim d₁ d₂]

theorem makesAtMostQueries_iff_isGameQuery
    (oa : Adversary (SMSort.den Key St St₂ Msg Coins RCoins C stSort) Msg Coins C)
    (q : ℕ) :
    MakesAtMostQueries oa q ↔
      oa.IsQueryBoundP
        (isGameQuery
          (G := SM.spec (SMSort.den Key St St₂ Msg Coins RCoins C stSort) Msg Coins C))
        q :=
  isQueryBoundP_congr oa (by funext x; cases x <;> simp [isGameQuery]) q

/-- When `A` makes at most `q ≤ K` game queries, `(challSimProg K Δ qep).eval (fun _ => A) ()` equals `Thm1.challSim Δ qep A`. -/
theorem challSimProg_eval [DecidableEq Msg] [DecidableEq C] (K Δ qep : ℕ)
    (heqCt : eqCt = (· == ·))
    (A : Adversary (SMSort.den Key St St₂ Msg Coins RCoins C stSort) Msg Coins C)
    (q : ℕ) (hq : MakesAtMostQueries A q) (hqK : q ≤ K) :
    (challSimProg (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
      (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
      K Δ qep).eval (fun _ => A) () =
      Thm1.challSim Δ qep A := by
  let so := Thm1.simImpl (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
    (Msg := Msg) (Coins := Coins) (C := C) Δ qep (fun _ => none) none
  have hq' := (makesAtMostQueries_iff_isGameQuery A q).mp hq
  have h1 := (challSimProg (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
      (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
      K Δ qep).eval_eq_simulateQ_of_abs
    (mirrorClearComp ∘ mirrorDec) (MirrorBoundInv K)
    (fun _ => do
      let b ← (liftM ($ᵗ Bool : ProbComp Bool) :
        AdversaryComp (SMSort.den Key St St₂ Msg Coins RCoins C stSort) Msg Coins C Bool)
      return ((), ({ st := fun _ => (), b } : Thm1.Mirror Msg C)))
    (clearCompImpl so)
    (fun _ b' => pure b')
    q ()
    (by simp [challSimProg, simInitC_eval, map_eq_bind_pure_comp]; rfl)
    (by
      intro r hr
      change r ∈ support ((simInitC (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
        (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
        (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
        (sampKey := sampKey) (sampCoins := sampCoins)
        (sampRCoins := sampRCoins)).eval (Env.cons (t := .unit) () Env.nil)) at hr
      rw [simInitC_eval, mem_support_bind_iff] at hr
      obtain ⟨b, -, hr⟩ := hr
      rw [support_pure, Set.mem_singleton_iff] at hr
      subst hr
      exact ⟨by simp [hqK], by simp [hqK]⟩)
    (fun n s => rfl)
    (fun m t v hv => challSimProg_step_clearComp K Δ qep m heqCt t v hv)
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
      (fun _ t s _ => ⟨simImpl_clearComp Δ qep t s, fun _ _ => trivial⟩)
      hq' ({ st := fun _ => (), b } : Thm1.Mirror Msg C) trivial).symm
    dsimp [clearCompImpl, so]
    simp [Prod.map, map_eq_bind_pure_comp]
  unfold Thm1.challSim Thm1.simRun
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun b => ?_
  rw [h2 b, StateT.run', bind_map_left, map_eq_bind_pure_comp, bind_assoc]
  simp [so, Prod.map]
  rfl

/-- When `A` makes at most `q ≤ K` game queries, `(privRedBProg K Δ qep i).eval (fun _ => A) ()` equals `ThmB.privRedB Δ qep i blank A`. -/
theorem privRedBProg_eval [DecidableEq Msg] [DecidableEq C] (K Δ qep i : ℕ)
    (heqCt : eqCt = (· == ·))
    (A : Adversary (SMSort.den Key St St₂ Msg Coins RCoins C stSort) Msg Coins C)
    (q : ℕ) (hq : MakesAtMostQueries A q) (hqK : q ≤ K) :
    (privRedBProg (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
      (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
      K Δ qep i).eval (fun _ => A) () =
      ThmB.privRedB Δ qep i blank A := by
  let so := ThmB.simImpl (St := SMSort.den Key St St₂ Msg Coins RCoins C stSort)
    (Coins := Coins) (C := C)
    Δ qep (fun t => if t < i then some blank else none) (some (i, blank))
  have hq' := (makesAtMostQueries_iff_isGameQuery A q).mp hq
  have h1 := (privRedBProg (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
      (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
      K Δ qep i).eval_eq_simulateQ_of_abs
    (mirrorClearComp ∘ mirrorDec) (MirrorBoundInv K)
    (fun _ => do
      let b ← (liftM ($ᵗ Bool : ProbComp Bool) :
        AdversaryComp (SMSort.den Key St St₂ Msg Coins RCoins C stSort) Msg Coins C Bool)
      return ((), ({ st := fun _ => (), b } : Thm1.Mirror Msg C)))
    (clearCompImpl so)
    (fun s₁ b' => pure (s₁.b == b'))
    q ()
    (by simp [privRedBProg, simInitC_eval, map_eq_bind_pure_comp]; rfl)
    (by
      intro r hr
      change r ∈ support ((simInitC (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
        (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
        (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
        (sampKey := sampKey) (sampCoins := sampCoins)
        (sampRCoins := sampRCoins)).eval (Env.cons (t := .unit) () Env.nil)) at hr
      rw [simInitC_eval, mem_support_bind_iff] at hr
      obtain ⟨b, -, hr⟩ := hr
      rw [support_pure, Set.mem_singleton_iff] at hr
      subst hr
      exact ⟨by simp [hqK], by simp [hqK]⟩)
    (fun n s => rfl)
    (fun m t v hv => privRedBProg_step_clearComp K Δ qep i m heqCt t v hv)
    (fun s b' _ => by
      simp [privRedBProg, Comp.eval, boolEq_eval, mB, Function.comp, mirrorDec, gsDec,
        Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ])
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
      (fun _ t s _ => ⟨simImplB_clearComp Δ qep i t s, fun _ _ => trivial⟩)
      hq' ({ st := fun _ => (), b } : Thm1.Mirror Msg C) trivial).symm
    dsimp [clearCompImpl, so]
    simp [Prod.map, map_eq_bind_pure_comp]
  unfold ThmB.privRedB ThmB.simRun
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun b => ?_
  rw [h2 b, StateT.run', bind_map_left, map_eq_bind_pure_comp, bind_assoc]
  refine bind_congr_of_mem_support'
    ((simulateQ so A).run ({ st := fun _ => (), b } : Thm1.Mirror Msg C)) (fun ⟨b', s₁⟩ hr => ?_)
  have hb : s₁.b = b := simulateQ_simImplB_b (blank := blank) Δ qep i A
    ({ st := fun _ => (), b } : Thm1.Mirror Msg C) (b', s₁) hr
  simp [Prod.map, hb]

/-! ## Query and cost bounds -/

@[simp] theorem simSendC_queries (realEpoch : Option ℕ) {Γ}
    (p : Expr OO Γ .bool) (ep : Expr OO Γ .nat)
    (mb : Expr OO Γ (.base .msg)) (r : Expr OO Γ (.opt (.base .coins))) :
    (simSendC (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
      (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
      realEpoch p ep mb r).queries (fun _ => 1) (fun _ => 0) = 1 := by
  cases realEpoch <;> simp [simSendC, Comp.queries]

@[simp] theorem simHandleC_queries (K Δ qep : ℕ) (realEpoch : Option ℕ) :
    (simHandleC (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
      (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
      K Δ qep realEpoch).queries (fun _ => 1) (fun _ => 0) = 1 := by
  simp [simHandleC, simTransmitC, simChallC, simDeliverC, simInjectC, simCorrC, Comp.queries]

@[simp] theorem simInitC_queries :
    (simInitC (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
      (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)).queries
      (fun _ => 1) (fun _ => 0) = 0 := by
  simp [simInitC, Comp.queries]

@[simp] theorem challSimProg_totalQueries (K Δ qep q : ℕ) :
    (challSimProg (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
      (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
      K Δ qep).totalQueries (fun _ => 1) (fun _ => 0) q = q := by
  simp [CostedReduction.totalQueries, challSimProg, Comp.queries]

@[simp] theorem privRedBProg_totalQueries (K Δ qep i q : ℕ) :
    (privRedBProg (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
      (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
      K Δ qep i).totalQueries (fun _ => 1) (fun _ => 0) q = q := by
  simp [CostedReduction.totalQueries, privRedBProg, Comp.queries]

theorem simInitC_cost :
    (simInitC (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
      (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)).cost = 39 := by
  simp [simInitC, mMk, smIface, smSamplers, Comp.cost, Expr.cost, Expr.v0, bits]

theorem challSimProg_totalCost (K Δ qep q : ℕ) :
    (challSimProg (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
      (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
      K Δ qep).totalCost q =
      41 + q * ((simHandleC (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
        (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
        (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
        (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
        K Δ qep none).cost + 6) := by
  simp only [CostedReduction.totalCost, challSimProg, simInitC_cost, smCodec, smIface, Comp.cost, Expr.cost,
    Expr.v1]
  rw [max_eq_right (by omega)]
  omega

theorem privRedBProg_totalCost (K Δ qep i q : ℕ) :
    (privRedBProg (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
      (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
      (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
      (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
      K Δ qep i).totalCost q =
      46 + q * ((simHandleC (Key := Key) (St := St) (St₂ := St₂) (RCoins := RCoins)
        (init := init) (send := send) (receive := receive) (eqMsg := eqMsg) (eqCt := eqCt)
        (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ) (stSort := stSort)
        (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
        K Δ qep (some i)).cost + 6) := by
  have hfin : (Comp.ret (I := SIface) (boolEq (mB (Expr.v0 (O := OO))) .v1) :
      Comp OO SIface [mirrorTy, .bool] .bool).cost = 7 := by
    simp [boolEq, mB, Comp.cost, Expr.cost, Expr.v0, Expr.v1]
  simp only [CostedReduction.totalCost, privRedBProg, simInitC_cost, hfin, smCodec, smIface]
  rw [max_eq_right (by omega)]
  omega

end SimProg

end CryptoGames.SM

