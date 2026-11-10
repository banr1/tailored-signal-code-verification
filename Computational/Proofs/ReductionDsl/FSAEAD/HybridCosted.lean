/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SpecLemmas.Reductions.Primitives.FSAEAD.CostedTables
public import Computational.Proofs.SpecLemmas.Reductions.Primitives.PRG.CostedTables
public import Computational.Proofs.SpecLemmas.Reductions.Primitives.OTCCA.CostedTables
public import Computational.Specifications.Reductions.ReductionDsl.Samplers
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Hybrid
import Computational.Proofs.ReductionDsl.Notation

/-!
# Two-stage `ReductionDsl` programs for ACD19 Theorem 5

Two-stage costed `ReductionDsl` witness programs (`prgRedZeroProg`, `multiRedProg`,
`prgRedAuthProg`, and `multiRedAuthProg`) for `cumulativeChainPrgReduction`,
`multiSlotOtccaReduction`, and their direct-output `Auth` variants, pausing at the first valid
`corruptReceiver` query so receiver-state materialization runs once in Stage 2.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoGames.FSAEAD.Thm5.Costed

open ReductionDsl CryptoGames.FSAEAD.Costed CryptoGames.PRG.Costed CryptoGames.OTCCA.Costed
open OracleComp OracleSpec
open scoped Computational.Proofs.ReductionDsl.Notation

local macro_rules
  | `(rdsl_pat| .transmit $p:term)        => `(rdsl_pat| .inl $p)
  | `(rdsl_pat| .challenge $p:term)       => `(rdsl_pat| .inr (.inl $p))
  | `(rdsl_pat| .corruptSender $p:term)   => `(rdsl_pat| .inr (.inr (.inl $p)))
  | `(rdsl_pat| .corruptReceiver $p:term) => `(rdsl_pat| .inr (.inr (.inr (.inl $p))))
  | `(rdsl_pat| .deliver $p:term)         => `(rdsl_pat| .inr (.inr (.inr (.inr (.inl $p)))))
  | `(rdsl_pat| .inject $p:term)          => `(rdsl_pat| .inr (.inr (.inr (.inr (.inr $p)))))
  | `(rdsl_pat| .unknown $p:term)         => `(rdsl_pat| .inl $p)
  | `(rdsl_pat| .seed $p:term)            => `(rdsl_pat| .inr (.inl $p))
  | `(rdsl_pat| .mat $p:term)             => `(rdsl_pat| .inr (.inr $p))

export CryptoGames.FSAEAD.Costed (fsStateSampleSort instSampleableHybKey)

local notation "HSig" CK:arg MK:arg AD:arg M:arg C:arg => fsSig CK MK AD Unit M C

local notation "HSamp" CK:arg MK:arg AD:arg M:arg C:arg =>
  unifSamplers (S := fsSig CK MK AD Unit M C) fsStateSampleSort (fun _ => 1)

local notation "hybOps" CK:arg MK:arg AD:arg M:arg C:arg ae:arg G:arg kPRG:arg kAEAD:arg =>
  Ops.sum
    (prgOps (S := fsSig CK MK AD Unit M C)
      (Ty.prod Ty.nat (bt FSort.ss)) (Ty.prod (bt FSort.ss) (bt FSort.rs))
      (fun pw => PRGScheme.gen (G (Prod.fst pw)) (Prod.snd pw)) kPRG)
    (otccaOps (S := fsSig CK MK AD Unit M C)
      (bt FSort.rs) (Ty.prod Ty.nat (bt FSort.ad)) (bt FSort.ad)
      (bt FSort.msg) (bt FSort.ct) ae kAEAD Ty.unit (fun _ => ()))

local notation "prgRedZeroIface" CK:arg MK:arg AD:arg M:arg C:arg ideal:arg kIdeal:arg =>
  Iface.withSamp
    (Iface.withSamp (prgIface (fsSig CK MK AD Unit M C))
      (idealSamplers (S := fsSig CK MK AD Unit M C)
        (Ty.prod Ty.nat (bt FSort.ad)) (bt FSort.ct) ideal kIdeal))
    (unifSamplers (S := fsSig CK MK AD Unit M C) fsStateSampleSort (fun _ => 1))

local notation "multiRedIface" CK:arg MK:arg AD:arg M:arg C:arg ideal:arg kIdeal:arg =>
  Iface.withSamp
    (otccaIface (S := fsSig CK MK AD Unit M C)
      (Ty.prod Ty.nat (bt FSort.ad)) (bt FSort.msg) (bt FSort.ct) ideal kIdeal)
    (unifSamplers (S := fsSig CK MK AD Unit M C) fsStateSampleSort (fun _ => 1))

section Programs

variable {CK MK AD M C : Type}
  [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK)) (kPRG kAEAD : ℕ)
  [SampleableType MK] [SampleableType CK]
  (ideal : ℕ × AD → ProbComp C) (kIdeal : ℕ)

local notation "HT" => Ty (fsSig CK MK AD Unit M C)

/-! ## State representation and pure helpers -/

@[reducible] def recTy : HT :=
  .prod .nat (.prod (bt .ad) (.prod (bt .msg) (.prod .nat (bt .ct))))

/-- Encoded frontier slot (`unknown`, `seed w`, or `mat pos (w', K)`). -/
@[reducible] def slotTy : HT :=
  .sum .unit (.sum (bt .ss) (.prod .nat (.prod (bt .ss) (bt .rs))))

@[reducible] def metaTy : HT :=
  .prod (.prod .bool .nat) (.prod (.opt .nat) .nat)

@[reducible] def flagsTy : HT :=
  .prod .bool (.prod .bool .bool)

@[reducible] def transTy : HT :=
  .prod (.list recTy) (.list .nat)

@[reducible] def kcTy : HT :=
  .prod .nat (.tbl (.opt (bt .rs)))

@[reducible] def chainTy : HT :=
  .prod kcTy (.prod (.opt (bt .ss)) (.tbl .bool))

@[reducible] def hsTy : HT :=
  .prod (.prod metaTy flagsTy) (.prod transTy chainTy)

@[reducible] def stTy : HT :=
  .prod hsTy slotTy

@[reducible] def callE
    {O : Ops (HSig CK MK AD M C)} {Γ : List HT} {a b : HT}
    (arg : Expr O Γ a) (body : Expr O (a :: Γ) b) : Expr O Γ b :=
  .letE arg body

@[reducible] def callC
    {O : Ops (HSig CK MK AD M C)} {ι : Type} {T : OracleSpec ι} {I : Iface (HSig CK MK AD M C) T}
    {Γ : List HT} {a b : HT} (arg : Expr O Γ a) (body : Comp O I (a :: Γ) b) : Comp O I Γ b :=
  .bind (.ret arg) body

@[reducible] def orE
    {O : Ops (HSig CK MK AD M C)} {Γ : List HT} (a b : Expr O Γ .bool) : Expr O Γ .bool :=
  .ite a (.bool true) b

@[reducible] def beqBoolE
    {O : Ops (HSig CK MK AD M C)} {Γ : List HT} (a b : Expr O Γ .bool) : Expr O Γ .bool :=
  .ite a b (.not b)

@[reducible] def isSomeE
    {O : Ops (HSig CK MK AD M C)} {Γ : List HT} {t : HT} (e : Expr O Γ (.opt t)) :
    Expr O Γ .bool :=
  .caseOpt e (.bool false) (.bool true)

@[reducible] def maxNatE
    {O : Ops (HSig CK MK AD M C)} {Γ : List HT} (a b : Expr O Γ .nat) : Expr O Γ .nat :=
  .ite (.lt a (.add b (.nat 1))) b a

@[reducible] def recIdx
    {O : Ops (HSig CK MK AD M C)} {Γ : List HT} (r : Expr O Γ recTy) : Expr O Γ .nat :=
  .fst r
@[reducible] def recAd
    {O : Ops (HSig CK MK AD M C)} {Γ : List HT} (r : Expr O Γ recTy) : Expr O Γ (bt .ad) :=
  .fst (.snd r)
@[reducible] def recMsg
    {O : Ops (HSig CK MK AD M C)} {Γ : List HT} (r : Expr O Γ recTy) : Expr O Γ (bt .msg) :=
  .fst (.snd (.snd r))
@[reducible] def recCt
    {O : Ops (HSig CK MK AD M C)} {Γ : List HT} (r : Expr O Γ recTy) :
    Expr O Γ (.prod .nat (bt .ct)) :=
  .snd (.snd (.snd r))

@[reducible] def hsB
    {O : Ops (HSig CK MK AD M C)} {Γ : List HT} (hs : Expr O Γ hsTy) : Expr O Γ .bool :=
  .fst (.fst (.fst (.fst hs)))
@[reducible] def hsLastSent
    {O : Ops (HSig CK MK AD M C)} {Γ : List HT} (hs : Expr O Γ hsTy) : Expr O Γ .nat :=
  .snd (.fst (.fst (.fst hs)))
@[reducible] def hsCorrAt
    {O : Ops (HSig CK MK AD M C)} {Γ : List HT} (hs : Expr O Γ hsTy) :
    Expr O Γ (.opt .nat) :=
  .fst (.snd (.fst (.fst hs)))
@[reducible] def hsRecvIdx
    {O : Ops (HSig CK MK AD M C)} {Γ : List HT} (hs : Expr O Γ hsTy) : Expr O Γ .nat :=
  .snd (.snd (.fst (.fst hs)))
@[reducible] def hsEnded
    {O : Ops (HSig CK MK AD M C)} {Γ : List HT} (hs : Expr O Γ hsTy) : Expr O Γ .bool :=
  .fst (.snd (.fst hs))
@[reducible] def hsWin
    {O : Ops (HSig CK MK AD M C)} {Γ : List HT} (hs : Expr O Γ hsTy) : Expr O Γ .bool :=
  .fst (.snd (.snd (.fst hs)))
@[reducible] def hsLf
    {O : Ops (HSig CK MK AD M C)} {Γ : List HT} (hs : Expr O Γ hsTy) : Expr O Γ .bool :=
  .snd (.snd (.snd (.fst hs)))
@[reducible] def hsInTransit
    {O : Ops (HSig CK MK AD M C)} {Γ : List HT} (hs : Expr O Γ hsTy) :
    Expr O Γ (.list recTy) :=
  .fst (.fst (.snd hs))
@[reducible] def hsChalls
    {O : Ops (HSig CK MK AD M C)} {Γ : List HT} (hs : Expr O Γ hsTy) :
    Expr O Γ (.list .nat) :=
  .snd (.fst (.snd hs))
@[reducible] def hsNKeys
    {O : Ops (HSig CK MK AD M C)} {Γ : List HT} (hs : Expr O Γ hsTy) : Expr O Γ .nat :=
  .fst (.fst (.snd (.snd hs)))
@[reducible] def hsKeysT
    {O : Ops (HSig CK MK AD M C)} {Γ : List HT} (hs : Expr O Γ hsTy) :
    Expr O Γ (.tbl (.opt (bt .rs))) :=
  .snd (.fst (.snd (.snd hs)))
@[reducible] def hsCorrKey
    {O : Ops (HSig CK MK AD M C)} {Γ : List HT} (hs : Expr O Γ hsTy) :
    Expr O Γ (.opt (bt .ss)) :=
  .fst (.snd (.snd (.snd hs)))
@[reducible] def hsSkipped
    {O : Ops (HSig CK MK AD M C)} {Γ : List HT} (hs : Expr O Γ hsTy) :
    Expr O Γ (.tbl .bool) :=
  .snd (.snd (.snd (.snd hs)))

@[reducible] def mkHS
    {O : Ops (HSig CK MK AD M C)} {Γ : List HT}
    (b : Expr O Γ .bool) (lastSentIdx : Expr O Γ .nat)
    (senderCorruptedAt : Expr O Γ (.opt .nat)) (receiverIdx : Expr O Γ .nat)
    (ended : Expr O Γ .bool) (win : Expr O Γ .bool) (lf : Expr O Γ .bool)
    (inTransit : Expr O Γ (.list recTy)) (challs : Expr O Γ (.list .nat))
    (nKeys : Expr O Γ .nat) (keysT : Expr O Γ (.tbl (.opt (bt .rs))))
    (corrKey : Expr O Γ (.opt (bt .ss))) (skipped : Expr O Γ (.tbl .bool)) :
    Expr O Γ hsTy :=
  .pair (.pair (.pair (.pair b lastSentIdx) (.pair senderCorruptedAt receiverIdx))
               (.pair ended (.pair win lf)))
        (.pair (.pair inTransit challs)
               (.pair (.pair nKeys keysT) (.pair corrKey skipped)))

@[reducible] def withKcE
    {O : Ops (HSig CK MK AD M C)} {Γ : List HT}
    (hs : Expr O Γ hsTy) (kc : Expr O Γ kcTy) : Expr O Γ hsTy :=
  .pair (.fst hs) (.pair (.fst (.snd hs)) (.pair kc (.snd (.snd (.snd hs)))))

@[reducible] def withSkippedE
    {O : Ops (HSig CK MK AD M C)} {Γ : List HT}
    (hs : Expr O Γ hsTy) (sk : Expr O Γ (.tbl .bool)) : Expr O Γ hsTy :=
  .pair (.fst hs)
    (.pair (.fst (.snd hs))
      (.pair (.fst (.snd (.snd hs)))
        (.pair (.fst (.snd (.snd (.snd hs)))) sk)))

@[reducible] def initHSE
    {O : Ops (HSig CK MK AD M C)} {Γ : List HT} (b : Expr O Γ .bool) : Expr O Γ hsTy :=
  mkHS b (.nat 0) .none (.nat 0) (.bool false) (.bool false) (.bool false)
    .nil .nil (.nat 0) (.tconst .none) .none (.tconst (.bool false))

def isCompromisedBody
    {O : Ops (HSig CK MK AD M C)} {Γ : List HT} :
    Expr O (.prod hsTy .nat :: Γ) .bool :=
  .caseOpt (hsCorrAt (.fst .v0)) (.bool false) (.lt .v0 (.snd .v1))

def isCompromisedE
    {O : Ops (HSig CK MK AD M C)} {Γ : List HT}
    (st : Expr O Γ hsTy) (i : Expr O Γ .nat) : Expr O Γ .bool :=
  callE (.pair st i) isCompromisedBody

@[reducible] def appendKcE
    {O : Ops (HSig CK MK AD M C)} {Γ : List HT}
    (kc : Expr O Γ kcTy) (K : Expr O Γ (bt .rs)) : Expr O Γ kcTy :=
  .pair (.add (.fst kc) (.nat 1))
        (.tset (.snd kc) (.fst kc) (.some K))

def removeFromTransitBody
    {O : Ops (HSig CK MK AD M C)} {Γ : List HT} (q : ℕ) :
    Expr O (.prod hsTy .nat :: Γ) hsTy :=
  let st := Expr.fst .v0
  mkHS (hsB st) (hsLastSent st) (hsCorrAt st) (hsRecvIdx st)
    (hsEnded st) (hsWin st) (hsLf st)
    (.foldrB q (hsInTransit st) .nil
      (.ite (.not (.eqN (recIdx .v0) (.snd .v2))) (.cons .v0 .v1) .v1))
    (.foldrB q (hsChalls st) .nil
      (.ite (.not (.eqN .v0 (.snd .v2))) (.cons .v0 .v1) .v1))
    (hsNKeys st) (hsKeysT st) (hsCorrKey st) (hsSkipped st)

def removeFromTransitE
    {O : Ops (HSig CK MK AD M C)} {Γ : List HT} (q : ℕ)
    (st : Expr O Γ hsTy) (i : Expr O Γ .nat) : Expr O Γ hsTy :=
  callE (.pair st i) (removeFromTransitBody q)

@[reducible] def skippedContainsE
    {O : Ops (HSig CK MK AD M C)} {Γ : List HT}
    (st : Expr O Γ hsTy) (i : Expr O Γ .nat) : Expr O Γ .bool :=
  .tget (hsSkipped st) i

def skippedRemoveBody
    {O : Ops (HSig CK MK AD M C)} {Γ : List HT} :
    Expr O (.prod hsTy .nat :: Γ) hsTy :=
  let st := Expr.fst .v0
  withSkippedE st (.tset (hsSkipped st) (.snd .v0) (.bool false))

def skippedRemoveE
    {O : Ops (HSig CK MK AD M C)} {Γ : List HT}
    (st : Expr O Γ hsTy) (i : Expr O Γ .nat) : Expr O Γ hsTy :=
  callE (.pair st i) skippedRemoveBody

@[reducible] def prgGenE {Γ : List HT}
    (pw : Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Γ (.prod .nat (bt .ss))) :
    Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Γ (.prod (bt .ss) (bt .rs)) :=
  Expr.op (O := hybOps CK MK AD M C ae G kPRG kAEAD) (Sum.inl () : Unit ⊕ OtccaOp) pw

@[reducible] def aeadEncE {Γ : List HT}
    (x : Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Γ
      (.prod (bt .rs) (.prod (.prod .nat (bt .ad)) (bt .msg)))) :
    Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Γ (bt .ct) :=
  Expr.op (O := hybOps CK MK AD M C ae G kPRG kAEAD) (Sum.inr OtccaOp.enc : Unit ⊕ OtccaOp) x

@[reducible] def aeadDecE {Γ : List HT}
    (x : Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Γ
      (.prod (bt .rs) (.prod (.prod .nat (bt .ad)) (bt .ct)))) :
    Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Γ (.opt (bt .msg)) :=
  Expr.op (O := hybOps CK MK AD M C ae G kPRG kAEAD) (Sum.inr OtccaOp.dec : Unit ⊕ OtccaOp) x

@[reducible] def eqAdE {Γ : List HT}
    (x : Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Γ (.prod (bt .ad) (bt .ad))) :
    Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Γ .bool :=
  Expr.op (O := hybOps CK MK AD M C ae G kPRG kAEAD) (Sum.inr OtccaOp.eqAD : Unit ⊕ OtccaOp) x

@[reducible] def eqME {Γ : List HT}
    (x : Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Γ (.prod (bt .msg) (bt .msg))) :
    Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Γ .bool :=
  Expr.op (O := hybOps CK MK AD M C ae G kPRG kAEAD) (Sum.inr OtccaOp.eqM : Unit ⊕ OtccaOp) x

@[reducible] def eqCE {Γ : List HT}
    (x : Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Γ (.prod (bt .ct) (bt .ct))) :
    Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Γ .bool :=
  Expr.op (O := hybOps CK MK AD M C ae G kPRG kAEAD) (Sum.inr OtccaOp.eqC : Unit ⊕ OtccaOp) x

def recMatchesE {Γ : List HT} :
    Expr (hybOps CK MK AD M C ae G kPRG kAEAD)
      (recTy :: .prod (bt .ad) (.prod .nat (bt .ct)) :: Γ) .bool :=
  .and (eqAdE ae G kPRG kAEAD (.pair (recAd .v0) (.fst .v1)))
    (.and (.eqN (.fst (recCt .v0)) (.fst (.snd .v1)))
          (eqCE ae G kPRG kAEAD (.pair (.snd (recCt .v0)) (.snd (.snd .v1)))))

def findInTransitBody {Γ : List HT} (q : ℕ) :
    Expr (hybOps CK MK AD M C ae G kPRG kAEAD)
      (.prod hsTy (.prod (bt .ad) (.prod .nat (bt .ct))) :: Γ) (.opt recTy) :=
  .letE (.snd .v0) (.findB q (hsInTransit (.fst .v1)) (recMatchesE ae G kPRG kAEAD))

def findInTransitE {Γ : List HT} (q : ℕ)
    (st : Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Γ hsTy)
    (qry : Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Γ (.prod (bt .ad) (.prod .nat (bt .ct)))) :
    Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Γ (.opt recTy) :=
  callE (.pair st qry) (findInTransitBody ae G kPRG kAEAD q)

def anyInTransitBody {Γ : List HT} (q : ℕ) :
    Expr (hybOps CK MK AD M C ae G kPRG kAEAD)
      (.prod hsTy (.prod (bt .ad) (.prod .nat (bt .ct))) :: Γ) .bool :=
  .letE (.snd .v0) (.anyB q (hsInTransit (.fst .v1)) (recMatchesE ae G kPRG kAEAD))

def anyInTransitE {Γ : List HT} (q : ℕ)
    (st : Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Γ hsTy)
    (qry : Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Γ (.prod (bt .ad) (.prod .nat (bt .ct)))) :
    Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Γ .bool :=
  callE (.pair st qry) (anyInTransitBody ae G kPRG kAEAD q)

def anyUncompInTransitBody
    {O : Ops (HSig CK MK AD M C)} {Γ : List HT} (q : ℕ) :
    Expr O (hsTy :: Γ) .bool :=
  .anyB q (hsInTransit .v0) (.not (isCompromisedE .v1 (recIdx .v0)))

def anyUncompInTransitE
    {O : Ops (HSig CK MK AD M C)} {Γ : List HT} (q : ℕ)
    (st : Expr O Γ hsTy) : Expr O Γ .bool :=
  callE st (anyUncompInTransitBody q)

def challsContainsBody
    {O : Ops (HSig CK MK AD M C)} {Γ : List HT} (q : ℕ) :
    Expr O (.prod hsTy .nat :: Γ) .bool :=
  .anyB q (hsChalls (.fst .v0)) (.eqN .v0 (.snd .v1))

def challsContainsE
    {O : Ops (HSig CK MK AD M C)} {Γ : List HT} (q : ℕ)
    (st : Expr O Γ hsTy) (i : Expr O Γ .nat) : Expr O Γ .bool :=
  callE (.pair st i) (challsContainsBody q)

/-! ## Monadic hybrid subroutines -/

def genStepKcBody
    {ι : Type} {T : OracleSpec ι} {I₀ : Iface (HSig CK MK AD M C) T} {Γ : List HT} :
    Comp (hybOps CK MK AD M C ae G kPRG kAEAD) (I₀.withSamp (HSamp CK MK AD M C))
      (.prod kcTy slotTy :: .prod .nat .nat :: Γ) (.prod kcTy slotTy) :=
  rdsl [(kc, slot), (_, jV)] do
    match slot with
    | .unknown _ =>
      if kc.1 < jV then
        K ← sample (Sum.inr (.base false)) ()
        return (appendKcE kc K, .inl ())
      else
        w ← sample (Sum.inr (.base true)) ()
        return (letE (prgGenE ae G kPRG kAEAD (kc.1, w)) fun (w', K) =>
          (appendKcE kc K, .inr (.inl w')))
    | .seed w =>
      return (letE (prgGenE ae G kPRG kAEAD (kc.1, w)) fun (w', K) =>
        (appendKcE kc K, .inr (.inl w')))
    | .mat pm@(pos, (w', K)) =>
      if kc.1 < pos then
        K₀ ← sample (Sum.inr (.base false)) ()
        return (appendKcE kc K₀, .inr (.inr pm))
      else
        return (appendKcE kc K, .inr (.inl w'))

def genUpToBody
    {ι : Type} {T : OracleSpec ι} {I₀ : Iface (HSig CK MK AD M C) T} {Γ : List HT}
    (maxSkip jPos : ℕ) :
    Comp (hybOps CK MK AD M C ae G kPRG kAEAD) (I₀.withSamp (HSamp CK MK AD M C))
      (.prod .nat stTy :: Γ) stTy :=
  rdsl [(targetIdx, (st, slot))] do
    (tIdx, _) ← return (targetIdx, nat jPos)
    (kc', slot') ← iter (maxSkip + 1) ((hsNKeys st, hsKeysT st), slot) fun acc@(kc, _) => do
      if kc.1 < tIdx then
        genStepKcBody ae G kPRG kAEAD
      else
        return acc
    return (withKcE st kc', slot')

def genUpToC
    {ι : Type} {T : OracleSpec ι} {I₀ : Iface (HSig CK MK AD M C) T} {Γ : List HT}
    (maxSkip jPos : ℕ)
    (i : Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Γ .nat)
    (s : Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Γ stTy) :
    Comp (hybOps CK MK AD M C ae G kPRG kAEAD) (I₀.withSamp (HSamp CK MK AD M C)) Γ stTy :=
  callC (.pair i s) (genUpToBody ae G kPRG kAEAD maxSkip jPos)

def revealBody
    {ι : Type} {T : OracleSpec ι} {I₀ : Iface (HSig CK MK AD M C) T} {Γ : List HT} :
    Comp (hybOps CK MK AD M C ae G kPRG kAEAD) (I₀.withSamp (HSamp CK MK AD M C))
      (stTy :: Γ) (.prod (bt .ss) stTy) :=
  rdsl [s@(st, slot)] do
    match slot with
    | .unknown _ =>
      w ← sample (Sum.inr (.base true)) ()
      return (w, (st, .inr (.inl w)))
    | .seed w =>
      return (w, s)
    | .mat _ =>
      w ← sample (Sum.inr (.base true)) ()
      return (w, (st, .inr (.inl w)))

def chainFromBody
    {ι : Type} {T : OracleSpec ι} {I : Iface (HSig CK MK AD M C) T} {Γ : List HT}
    (fuel : ℕ) :
    Comp (hybOps CK MK AD M C ae G kPRG kAEAD) I
      (.prod .nat (.prod (bt .ss) .nat) :: Γ) (bt .ss) :=
  rdsl [(c, (w, m))] do
    (_, wOut) ← iter fuel (0, w) fun step@(idx, curW) => do
      return (if idx < m then
        (idx + 1, (prgGenE ae G kPRG kAEAD (c + idx, curW)).1)
      else
        step)
    return wOut

def chainFromC
    {ι : Type} {T : OracleSpec ι} {I : Iface (HSig CK MK AD M C) T} {Γ : List HT}
    (fuel : ℕ)
    (c : Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Γ .nat)
    (w : Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Γ (bt .ss))
    (m : Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Γ .nat) :
    Comp (hybOps CK MK AD M C ae G kPRG kAEAD) I Γ (bt .ss) :=
  callC (.pair c (.pair w m)) (chainFromBody ae G kPRG kAEAD fuel)

def senderKeyBody
    {ι : Type} {T : OracleSpec ι} {I₀ : Iface (HSig CK MK AD M C) T} {Γ : List HT}
    (q : ℕ) :
    Comp (hybOps CK MK AD M C ae G kPRG kAEAD) (I₀.withSamp (HSamp CK MK AD M C))
      (stTy :: Γ) (.prod (bt .ss) stTy) :=
  rdsl [s@(st, _)] do
    match hsCorrAt st with
    | none => revealBody ae G kPRG kAEAD
    | some c =>
      match hsCorrKey st with
      | none => callC s (revealBody ae G kPRG kAEAD)
      | some w =>
        w' ← chainFromC ae G kPRG kAEAD q c w (hsLastSent st - c)
        return (w', s)

def prependNewSkippedBody
    {ι : Type} {T : OracleSpec ι} {I : Iface (HSig CK MK AD M C) T} {Γ : List HT}
    (maxSkip : ℕ) :
    Comp (hybOps CK MK AD M C ae G kPRG kAEAD) I
      (.prod .nat (.prod .nat (.tbl .bool)) :: Γ) (.tbl .bool) :=
  rdsl [(iB, (i, skipped))] do
    iV ← return i
    (_, out) ← iter maxSkip (iB + 1, skipped) fun step@(idx, acc) => do
      return (if idx < iV then
        (idx + 1, tset acc idx true)
      else
        step)
    return out

/-- Scans `1 .. (maxSkip + 1) * q` upward to materialize `st.skipped` in strictly decreasing order. -/
def corruptReceiverDBody
    {ι : Type} {T : OracleSpec ι} {I : Iface (HSig CK MK AD M C) T} {Γ : List HT}
    (maxSkip q : ℕ) :
    Comp (hybOps CK MK AD M C ae G kPRG kAEAD) I
      (hsTy :: Γ) (.list (.prod .nat (bt .rs))) :=
  let fuelD : ℕ := (maxSkip + 1) * q
  rdsl [st] do
    match hsCorrAt st with
    | none => return Expr.nil
    | some c =>
      (cV, (skV, ktV)) ← return (c, (hsSkipped st, hsKeysT st))
      (_, out) ← iter fuelD (0, Expr.nil) fun (step, acc) => do
        return (letE (step + 1) fun idx =>
          (idx,
            if cV < idx then
              if tget skV idx then
                match tget ktV step with
                | none => acc
                | some K => cons (idx, K) acc
              else
                acc
            else
              acc))
      return out

def decIdxBody
    {ι : Type} {T : OracleSpec ι} {I : Iface (HSig CK MK AD M C) T} {Γ : List HT}
    (mSlot : ℕ)
    (specialDec : Option (∀ {Δ},
      Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Δ (.prod (.prod .nat (bt .ad)) (bt .ct)) →
        Comp (hybOps CK MK AD M C ae G kPRG kAEAD) I Δ (.opt (bt .msg)))) :
    Comp (hybOps CK MK AD M C ae G kPRG kAEAD) I
      (.prod (.prod (.opt (bt .msg)) (.prod .nat (.prod (bt .ad) (bt .ct)))) hsTy :: Γ)
      (.opt (bt .msg)) :=
  let realArm : Comp (hybOps CK MK AD M C ae G kPRG kAEAD) I _ (.opt (bt .msg)) :=
    rdsl [((_, (i, (a, e))), st)] do
      return (match tget (hsKeysT st) (i - 1) with
        | none => none
        | some K => aeadDecE ae G kPRG kAEAD (K, ((i, a), e)))
  let fallbackArm : Comp (hybOps CK MK AD M C ae G kPRG kAEAD) I _ (.opt (bt .msg)) :=
    match specialDec with
    | none => realArm
    | some sDec =>
      rdsl [((_, (i, (a, e))), st)] do
        if (i < nat mSlot + 1) && !(isCompromisedE st i) then
          sDec ((i, a), e)
        else
          raw realArm
  rdsl [((hint, (i, _)), st)] do
    match hint with
    | none =>
      if (i == 0) && !(isCompromisedE st i) then
        return none
      else
        raw fallbackArm
    | some msg =>
      return (some msg)

def encIdxBody
    {ι : Type} {T : OracleSpec ι} {I : Iface (HSig CK MK AD M C) T} {Γ : List HT}
    (mSlot : ℕ)
    (sampleIdeal : ∀ {Δ},
      Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Δ (.prod .nat (bt .ad)) →
        Comp (hybOps CK MK AD M C ae G kPRG kAEAD) I Δ (bt .ct))
    (specialEnc : Option (∀ {Δ},
      Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Δ (.prod (.prod .nat (bt .ad)) (bt .msg)) →
        Comp (hybOps CK MK AD M C ae G kPRG kAEAD) I Δ (bt .ct))) :
    Comp (hybOps CK MK AD M C ae G kPRG kAEAD) I
      (.prod (.prod .nat (.prod (bt .ad) (bt .msg))) hsTy :: Γ) (bt .ct) :=
  let realArm : Comp (hybOps CK MK AD M C ae G kPRG kAEAD) I _ (bt .ct) :=
    rdsl [((i, (a, msg)), st)] do
      match tget (hsKeysT st) (i - 1) with
      | none => sampleIdeal (i, a)
      | some K => return (aeadEncE ae G kPRG kAEAD (K, ((i, a), msg)))
  let fallbackArm : Comp (hybOps CK MK AD M C ae G kPRG kAEAD) I _ (bt .ct) :=
    match specialEnc with
    | none => realArm
    | some sEnc =>
      rdsl [((i, (a, msg)), st)] do
        if (i < nat mSlot + 1) && !(isCompromisedE st i) then
          sEnc ((i, a), msg)
        else
          raw realArm
  rdsl [((i, (a, _)), st)] do
    if (i == 0) && !(isCompromisedE st i) then
      sampleIdeal (i, a)
    else
      raw fallbackArm

def receiveBody
    {ι : Type} {T : OracleSpec ι} {I₀ : Iface (HSig CK MK AD M C) T} {Γ : List HT}
    (maxSkip jPos mSlot : ℕ) (la : Bool)
    (specialDec : Option (∀ {Δ},
      Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Δ (.prod (.prod .nat (bt .ad)) (bt .ct)) →
        Comp (hybOps CK MK AD M C ae G kPRG kAEAD)
          (I₀.withSamp (HSamp CK MK AD M C)) Δ (.opt (bt .msg)))) :
    Comp (hybOps CK MK AD M C ae G kPRG kAEAD) (I₀.withSamp (HSamp CK MK AD M C))
      (.prod (.prod (.opt (bt .msg)) (.prod (bt .ad) (.prod .nat (bt .ct)))) stTy :: Γ)
      (.prod (.opt (.prod .nat (bt .msg))) stTy) :=
  rdsl [((hint, (a, (i, e))), s@(st, sl))] do
    if skippedContainsE st i then
      optMsg ← callC ((hint, (i, (a, e))), st) (decIdxBody ae G kPRG kAEAD mSlot specialDec)
      match optMsg with
      | none => return (none, s)
      | some msg =>
        return (some (i, msg), (skippedRemoveE st i, sl))
    else if orE (i < hsRecvIdx st + 1) (nat maxSkip < i - hsRecvIdx st - 1) then
      return (none, s)
    else if !(bool la) && ((hsLastSent st < i) && !(isCompromisedE st i)) then
      return (none, s)
    else
      s'@(st', sl') ← genUpToC ae G kPRG kAEAD maxSkip jPos i s
      optMsg ← callC ((hint, (i, (a, e))), st') (decIdxBody ae G kPRG kAEAD mSlot specialDec)
      match optMsg with
      | none => return (none, s')
      | some msg =>
        skipped' ← callC (hsRecvIdx st, (i, hsSkipped st'))
          (prependNewSkippedBody ae G kPRG kAEAD maxSkip)
        return (some (i, msg), (withSkippedE st' skipped', sl'))

/-! ## Oracle handlers and two-stage components -/

def corruptSenderBody
    {ι : Type} {T : OracleSpec ι} {I₀ : Iface (HSig CK MK AD M C) T} {Γ : List HT}
    (q : ℕ) (la : Bool) :
    Comp (hybOps CK MK AD M C ae G kPRG kAEAD) (I₀.withSamp (HSamp CK MK AD M C))
      (stTy :: Γ) (.prod (.opt rssTy) stTy) :=
  rdsl [s@(st, sl)] do
    if hsEnded st then
      return (none, s)
    else if bool la then
      return (none,
        (mkHS (hsB st) (hsLastSent st) (hsCorrAt st) (hsRecvIdx st)
          true (hsWin st) (hsLf st) (hsInTransit st) (hsChalls st)
          (hsNKeys st) (hsKeysT st) (hsCorrKey st) (hsSkipped st), sl))
    else
      (w, (st', sl')) ← senderKeyBody ae G kPRG kAEAD q
      let corrAt' := match hsCorrAt st with | none => hsLastSent st | some c => c
      let corrKey' := match hsCorrKey st with | none => w | some ck => ck
      return (some (w, hsLastSent st),
        (mkHS (hsB st') (hsLastSent st') (some corrAt') (hsRecvIdx st')
          (hsEnded st') (hsWin st') (hsLf st') (hsInTransit st') (hsChalls st')
          (hsNKeys st') (hsKeysT st') (some corrKey') (hsSkipped st'), sl'))

def corruptReceiverResumeBody
    {ι : Type} {T : OracleSpec ι} {I₀ : Iface (HSig CK MK AD M C) T} {Γ : List HT}
    (maxSkip q : ℕ) (la : Bool) :
    Comp (hybOps CK MK AD M C ae G kPRG kAEAD) (I₀.withSamp (HSamp CK MK AD M C))
      (stTy :: Γ) (.prod ratchetR stTy) :=
  let fuelB : ℕ := (maxSkip + 1) * q
  rdsl [(st, sl)] do
    if bool la then
      return (.inr (.inr (.inl none)),
        (mkHS (hsB st) (hsLastSent st) (hsCorrAt st) (hsRecvIdx st)
          true (hsWin st) (hsLf st) (hsInTransit st) (hsChalls st)
          (hsNKeys st) (hsKeysT st) (hsCorrKey st) (hsSkipped st), sl))
    else
      (wA, (st', sl')) ← senderKeyBody ae G kPRG kAEAD q
      wB ← match hsCorrAt st' with
        | none => return wA
        | some c =>
          match hsCorrKey st' with
          | none => return wA
          | some ck => chainFromC ae G kPRG kAEAD fuelB c ck (hsRecvIdx st' - c)
      D ← callC st' (corruptReceiverDBody ae G kPRG kAEAD maxSkip q)
      return (.inr (.inr (.inl (some ((wA, hsLastSent st'), (wB, (hsRecvIdx st', D)))))),
        (mkHS (hsB st') (hsLastSent st') (hsCorrAt st') (hsRecvIdx st')
          true (hsWin st') (hsLf st') (hsInTransit st') (hsChalls st')
          (hsNKeys st') (hsKeysT st') (hsCorrKey st') (hsSkipped st'), sl'))

def transmitBody
    {ι : Type} {T : OracleSpec ι} {I₀ : Iface (HSig CK MK AD M C) T} {Γ : List HT}
    (maxSkip jPos mSlot : ℕ)
    (sampleIdeal : ∀ {Δ},
      Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Δ (.prod .nat (bt .ad)) →
        Comp (hybOps CK MK AD M C ae G kPRG kAEAD)
          (I₀.withSamp (HSamp CK MK AD M C)) Δ (bt .ct))
    (specialEnc : Option (∀ {Δ},
      Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Δ (.prod (.prod .nat (bt .ad)) (bt .msg)) →
        Comp (hybOps CK MK AD M C ae G kPRG kAEAD)
          (I₀.withSamp (HSamp CK MK AD M C)) Δ (bt .ct))) :
    Comp (hybOps CK MK AD M C ae G kPRG kAEAD) (I₀.withSamp (HSamp CK MK AD M C))
      (.prod (.prod (bt .ad) (bt .msg)) stTy :: Γ)
      (.prod (.opt (.prod .nat (bt .ct))) stTy) :=
  rdsl [(am@(a, m), s@(st, _))] do
    if hsEnded st then
      return (none, s)
    else
      let nextIdx := hsLastSent st + 1
      (st', sl') ← genUpToC ae G kPRG kAEAD maxSkip jPos nextIdx s
      ct ← callC ((nextIdx, am), st') (encIdxBody ae G kPRG kAEAD mSlot sampleIdeal specialEnc)
      let recE := (nextIdx, (a, (m, (nextIdx, ct))))
      return (some (nextIdx, ct),
        (mkHS (hsB st') nextIdx (hsCorrAt st') (hsRecvIdx st')
          (hsEnded st') (hsWin st') (hsLf st')
          (cons recE (hsInTransit st')) (hsChalls st')
          (hsNKeys st') (hsKeysT st') (hsCorrKey st') (hsSkipped st'), sl'))

def challengeBody
    {ι : Type} {T : OracleSpec ι} {I₀ : Iface (HSig CK MK AD M C) T} {Γ : List HT}
    (maxSkip jPos mSlot : ℕ)
    (sampleIdeal : ∀ {Δ},
      Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Δ (.prod .nat (bt .ad)) →
        Comp (hybOps CK MK AD M C ae G kPRG kAEAD)
          (I₀.withSamp (HSamp CK MK AD M C)) Δ (bt .ct))
    (specialEnc : Option (∀ {Δ},
      Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Δ (.prod (.prod .nat (bt .ad)) (bt .msg)) →
        Comp (hybOps CK MK AD M C ae G kPRG kAEAD)
          (I₀.withSamp (HSamp CK MK AD M C)) Δ (bt .ct))) :
    Comp (hybOps CK MK AD M C ae G kPRG kAEAD) (I₀.withSamp (HSamp CK MK AD M C))
      (.prod (.prod (bt .ad) (.prod (bt .msg) (bt .msg))) stTy :: Γ)
      (.prod (.opt (.prod .nat (bt .ct))) stTy) :=
  rdsl [((a, (m₀, m₁)), s@(st, _))] do
    if orE (hsEnded st) (isSomeE (hsCorrAt st)) then
      return (none, s)
    else
      let nextIdx := hsLastSent st + 1
      let msg := if hsB st then m₁ else m₀
      (st', sl') ← genUpToC ae G kPRG kAEAD maxSkip jPos nextIdx s
      ct ← callC ((nextIdx, (a, msg)), st')
        (encIdxBody ae G kPRG kAEAD mSlot sampleIdeal specialEnc)
      let recE := (nextIdx, (a, (msg, (nextIdx, ct))))
      return (some (nextIdx, ct),
        (mkHS (hsB st') nextIdx (hsCorrAt st') (hsRecvIdx st')
          (hsEnded st') (hsWin st') (hsLf st')
          (cons recE (hsInTransit st')) (cons nextIdx (hsChalls st'))
          (hsNKeys st') (hsKeysT st') (hsCorrKey st') (hsSkipped st'), sl'))

def deliverBody
    {ι : Type} {T : OracleSpec ι} {I₀ : Iface (HSig CK MK AD M C) T} {Γ : List HT}
    (maxSkip q jPos mSlot : ℕ) (la : Bool)
    (specialDec : Option (∀ {Δ},
      Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Δ (.prod (.prod .nat (bt .ad)) (bt .ct)) →
        Comp (hybOps CK MK AD M C ae G kPRG kAEAD)
          (I₀.withSamp (HSamp CK MK AD M C)) Δ (.opt (bt .msg)))) :
    Comp (hybOps CK MK AD M C ae G kPRG kAEAD) (I₀.withSamp (HSamp CK MK AD M C))
      (.prod (.prod (bt .ad) (.prod .nat (bt .ct))) stTy :: Γ)
      (.prod (.opt (rrTy (bt .msg))) stTy) :=
  rdsl [(qry, s@(st, _))] do
    if hsEnded st then
      return (none, s)
    else
      match findInTransitE ae G kPRG kAEAD q st qry with
      | none => return (none, s)
      | some r =>
        (optRes, (st', sl')) ← callC ((some (recMsg r), qry), s)
          (receiveBody ae G kPRG kAEAD maxSkip jPos mSlot la specialDec)
        let rIdx := recIdx r
        let inReceiveOnlyEpoch := rIdx < hsRecvIdx st + nat maxSkip + 2
        let mustBe := !(isCompromisedE st rIdx) && inReceiveOnlyEpoch
        match optRes with
        | none =>
          return (some (.inl ()),
            (mkHS (hsB st') (hsLastSent st') (hsCorrAt st') (hsRecvIdx st')
              (hsEnded st') (orE (hsWin st') mustBe) (hsLf st')
              (hsInTransit st') (hsChalls st') (hsNKeys st') (hsKeysT st')
              (hsCorrKey st') (hsSkipped st'), sl'))
        | some (i', m') =>
          let incorr := mustBe && orE (!(i' == rIdx)) (!(eqME ae G kPRG kAEAD (m', recMsg r)))
          let outOpt := if callE (.pair st rIdx) (challsContainsBody q) then none else some m'
          let stUpd := mkHS (hsB st') (hsLastSent st') (hsCorrAt st')
            (maxNatE (hsRecvIdx st') i') (hsEnded st') (orE (hsWin st') incorr) (hsLf st')
            (hsInTransit st') (hsChalls st') (hsNKeys st') (hsKeysT st')
            (hsCorrKey st') (hsSkipped st')
          return (some (.inr (i', outOpt)),
            (removeFromTransitE q stUpd rIdx, sl'))

def injectBody
    {ι : Type} {T : OracleSpec ι} {I₀ : Iface (HSig CK MK AD M C) T} {Γ : List HT}
    (maxSkip q jPos mSlot : ℕ) (la : Bool)
    (specialDec : Option (∀ {Δ},
      Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Δ (.prod (.prod .nat (bt .ad)) (bt .ct)) →
        Comp (hybOps CK MK AD M C ae G kPRG kAEAD)
          (I₀.withSamp (HSamp CK MK AD M C)) Δ (.opt (bt .msg)))) :
    Comp (hybOps CK MK AD M C ae G kPRG kAEAD) (I₀.withSamp (HSamp CK MK AD M C))
      (.prod (.prod (bt .ad) (.prod .nat (bt .ct))) stTy :: Γ)
      (.prod (.opt (rrTy (bt .msg))) stTy) :=
  rdsl [(qry, s@(st, _))] do
    if orE (hsEnded st) (anyInTransitE ae G kPRG kAEAD q st qry) then
      return (none, s)
    else
      (optRes, s'@(st', sl')) ← callC ((none, qry), s)
        (receiveBody ae G kPRG kAEAD maxSkip jPos mSlot la specialDec)
      match optRes with
      | none => return (some (.inl ()), s')
      | some (i', m') =>
        let forged := !(isCompromisedE st i')
        let lfNow := forged && (hsLastSent st < i')
        let stUpd := mkHS (hsB st') (hsLastSent st') (hsCorrAt st')
          (maxNatE (hsRecvIdx st') i')
          (orE (hsEnded st') (bool la && lfNow))
          (orE (hsWin st') forged)
          (orE (hsLf st') lfNow)
          (hsInTransit st') (hsChalls st') (hsNKeys st') (hsKeysT st')
          (hsCorrKey st') (hsSkipped st')
        return (some (.inr (i', some m')),
          (removeFromTransitE q stUpd i', sl'))

/-- Stage-1 hybrid oracle handler that pauses on the first valid `corruptReceiver` query. -/
def hybHandlePreC
    {ι : Type} {T : OracleSpec ι} {I₀ : Iface (HSig CK MK AD M C) T}
    (maxSkip q jPos mSlot : ℕ) (la : Bool)
    (sampleIdeal : ∀ {Δ},
      Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Δ (.prod .nat (bt .ad)) →
        Comp (hybOps CK MK AD M C ae G kPRG kAEAD)
          (I₀.withSamp (HSamp CK MK AD M C)) Δ (bt .ct))
    (specialEnc : Option (∀ {Δ},
      Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Δ (.prod (.prod .nat (bt .ad)) (bt .msg)) →
        Comp (hybOps CK MK AD M C ae G kPRG kAEAD)
          (I₀.withSamp (HSamp CK MK AD M C)) Δ (bt .ct)))
    (specialDec : Option (∀ {Δ},
      Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Δ (.prod (.prod .nat (bt .ad)) (bt .ct)) →
        Comp (hybOps CK MK AD M C ae G kPRG kAEAD)
          (I₀.withSamp (HSamp CK MK AD M C)) Δ (.opt (bt .msg)))) :
    Comp (hybOps CK MK AD M C ae G kPRG kAEAD) (I₀.withSamp (HSamp CK MK AD M C))
      [stTy, ratchetQ] (.sum (.prod ratchetR stTy) (.prod .unit (.prod .unit stTy))) :=
  rdsl [s@(st, _), qry] do
    match qry with
    | .transmit qTr =>
      (r, s') ← callC (qTr, s)
        (transmitBody ae G kPRG kAEAD maxSkip jPos mSlot sampleIdeal specialEnc)
      return (.inl (.inl r, s'))
    | .challenge qCh =>
      (r, s') ← callC (qCh, s)
        (challengeBody ae G kPRG kAEAD maxSkip jPos mSlot sampleIdeal specialEnc)
      return (.inl (.inl r, s'))
    | .corruptSender _ =>
      (r, s') ← callC s (corruptSenderBody ae G kPRG kAEAD q la)
      return (.inl (.inr (.inl r), s'))
    | .corruptReceiver _ =>
      let bad := orE (hsEnded st) (orE (0 < len (hsChalls st)) (anyUncompInTransitE q st))
      if bad then
        return (.inl (.inl none, s))
      else
        return (.inr ((), ((), s)))
    | .deliver qDl =>
      (r, s') ← callC (qDl, s)
        (deliverBody ae G kPRG kAEAD maxSkip q jPos mSlot la specialDec)
      return (.inl (.inr (.inr (.inr r)), s'))
    | .inject qIj =>
      (r, s') ← callC (qIj, s)
        (injectBody ae G kPRG kAEAD maxSkip q jPos mSlot la specialDec)
      return (.inl (.inr (.inr (.inr r)), s'))

def hybChDoneC
    {ι : Type} {T : OracleSpec ι} {I : Iface (HSig CK MK AD M C) T} :
    Comp (hybOps CK MK AD M C ae G kPRG kAEAD) I [stTy, .bool] .unit :=
  .ret .unit

def hybResumeC
    {ι : Type} {T : OracleSpec ι} {I₀ : Iface (HSig CK MK AD M C) T}
    (maxSkip q : ℕ) (la : Bool) :
    Comp (hybOps CK MK AD M C ae G kPRG kAEAD) (I₀.withSamp (HSamp CK MK AD M C))
      [stTy, .unit, .unit] (.prod ratchetR stTy) :=
  corruptReceiverResumeBody ae G kPRG kAEAD maxSkip q la

def hybHandlePostC
    {ι : Type} {T : OracleSpec ι} {I : Iface (HSig CK MK AD M C) T} :
    Comp (hybOps CK MK AD M C ae G kPRG kAEAD) I [stTy, ratchetQ] (.prod ratchetR stTy) :=
  .ret (.pair (.inl .none) .v0)

def hybFinishC
    {ι : Type} {T : OracleSpec ι} {I : Iface (HSig CK MK AD M C) T} (la : Bool) :
    Comp (hybOps CK MK AD M C ae G kPRG kAEAD) I [stTy, .bool, .unit] .bool :=
  rdsl [(st, _), b', _] do
    return (if bool la then hsLf st else orE (beqBoolE (hsB st) b') (hsWin st))

def hybFinishAuthC
    {ι : Type} {T : OracleSpec ι} {I : Iface (HSig CK MK AD M C) T} :
    Comp (hybOps CK MK AD M C ae G kPRG kAEAD) I [stTy, .bool, .unit] .bool :=
  .ret (.var (.succ .zero))

/-! ## Top-level two-stage costed reductions -/

/-- Two-stage costed program for `cumulativeChainPrgReduction ideal ae G maxSkip j`. -/
def prgRedZeroProg (q maxSkip j : ℕ) :
    TwoStageCostedReduction (hybOps CK MK AD M C ae G kPRG kAEAD)
      (prgRedZeroIface CK MK AD M C ideal kIdeal)
      (spec (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M (ℕ × C))
      ratchetCodec (.prod (bt .ss) (bt .rs)) .unit .bool .unit .unit .bool where
  σ := stTy
  π := .unit
  init := rdsl [mt] do
    b ← sample (Sum.inr .bool) ()
    return ((), (initHSE b, .inr (.inr (nat (j / 2), mt))))
  handlePre :=
    hybHandlePreC ae G kPRG kAEAD maxSkip q (j / 2) 0 (isLookaheadHop j)
      (fun ia =>
        Comp.sample (O := hybOps CK MK AD M C ae G kPRG kAEAD)
          (I := prgRedZeroIface CK MK AD M C ideal kIdeal)
          (Sum.inl (Sum.inr ()) : (Empty ⊕ Unit) ⊕ UniformSamplerTag Bool) ia)
      none none
  chDone := hybChDoneC ae G kPRG kAEAD
  resume := hybResumeC ae G kPRG kAEAD maxSkip q (isLookaheadHop j)
  handlePost := hybHandlePostC ae G kPRG kAEAD
  finish := hybFinishC ae G kPRG kAEAD (isLookaheadHop j)

/-- Direct-output (`Auth`-mode) two-stage costed program for `cumulativeChainPrgReductionOut`. -/
def prgRedAuthProg (q maxSkip j : ℕ) :
    TwoStageCostedReduction (hybOps CK MK AD M C ae G kPRG kAEAD)
      (prgRedZeroIface CK MK AD M C ideal kIdeal)
      (spec (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M (ℕ × C))
      ratchetCodec (.prod (bt .ss) (bt .rs)) .unit .bool .unit .unit .bool where
  σ := stTy
  π := .unit
  init := rdsl [mt] do
    b ← sample (Sum.inr .bool) ()
    return ((), (initHSE b, .inr (.inr (nat (j / 2), mt))))
  handlePre :=
    hybHandlePreC ae G kPRG kAEAD maxSkip q (j / 2) 0 (isLookaheadHop j)
      (fun ia =>
        Comp.sample (O := hybOps CK MK AD M C ae G kPRG kAEAD)
          (I := prgRedZeroIface CK MK AD M C ideal kIdeal)
          (Sum.inl (Sum.inr ()) : (Empty ⊕ Unit) ⊕ UniformSamplerTag Bool) ia)
      none none
  chDone := hybChDoneC ae G kPRG kAEAD
  resume := hybResumeC ae G kPRG kAEAD maxSkip q (isLookaheadHop j)
  handlePost := hybHandlePostC ae G kPRG kAEAD
  finish := hybFinishAuthC ae G kPRG kAEAD

def otSpecialEncC {Γ : List HT}
    (iam : Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Γ (.prod (.prod .nat (bt .ad)) (bt .msg))) :
    Comp (hybOps CK MK AD M C ae G kPRG kAEAD) (multiRedIface CK MK AD M C ideal kIdeal)
      Γ (bt .ct) :=
  callC iam <| rdsl [req@(ia, _msg)] do
    r ← query (O := hybOps CK MK AD M C ae G kPRG kAEAD)
      (I := multiRedIface CK MK AD M C ideal kIdeal) OtccaTag.enc req
    match r with
    | none =>
      sample (O := hybOps CK MK AD M C ae G kPRG kAEAD)
        (I := multiRedIface CK MK AD M C ideal kIdeal)
        (Sum.inl () : Unit ⊕ UniformSamplerTag Bool) ia
    | some ct =>
      return ct

def otSpecialDecC {Γ : List HT}
    (iae : Expr (hybOps CK MK AD M C ae G kPRG kAEAD) Γ (.prod (.prod .nat (bt .ad)) (bt .ct))) :
    Comp (hybOps CK MK AD M C ae G kPRG kAEAD) (multiRedIface CK MK AD M C ideal kIdeal)
      Γ (.opt (bt .msg)) :=
  Comp.query (O := hybOps CK MK AD M C ae G kPRG kAEAD)
    (I := multiRedIface CK MK AD M C ideal kIdeal) OtccaTag.dec iae

/-- Two-stage costed program for `multiSlotOtccaReduction ideal ae G maxSkip N la`. -/
def multiRedProg (q maxSkip N : ℕ) (la : Bool) :
    TwoStageCostedReduction (hybOps CK MK AD M C ae G kPRG kAEAD)
      (multiRedIface CK MK AD M C ideal kIdeal)
      (spec (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M (ℕ × C))
      ratchetCodec .unit .unit .bool .unit .unit .bool where
  σ := stTy
  π := .unit
  init := rdsl [_] do
    b ← sample (Sum.inr .bool) ()
    return ((), (initHSE b, .inl ()))
  handlePre :=
    hybHandlePreC ae G kPRG kAEAD maxSkip q N N la
      (fun ia =>
        Comp.sample (O := hybOps CK MK AD M C ae G kPRG kAEAD)
          (I := multiRedIface CK MK AD M C ideal kIdeal)
          (Sum.inl () : Unit ⊕ UniformSamplerTag Bool) ia)
      (some (otSpecialEncC ae G kPRG kAEAD ideal kIdeal))
      (some (otSpecialDecC ae G kPRG kAEAD ideal kIdeal))
  chDone := hybChDoneC ae G kPRG kAEAD
  resume := hybResumeC ae G kPRG kAEAD maxSkip q la
  handlePost := hybHandlePostC ae G kPRG kAEAD
  finish := hybFinishC ae G kPRG kAEAD la

/-- Direct-output (`Auth`-mode) two-stage costed program for `multiSlotOtccaReductionOut`. -/
def multiRedAuthProg (q maxSkip N : ℕ) (la : Bool) :
    TwoStageCostedReduction (hybOps CK MK AD M C ae G kPRG kAEAD)
      (multiRedIface CK MK AD M C ideal kIdeal)
      (spec (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M (ℕ × C))
      ratchetCodec .unit .unit .bool .unit .unit .bool where
  σ := stTy
  π := .unit
  init := rdsl [_] do
    b ← sample (Sum.inr .bool) ()
    return ((), (initHSE b, .inl ()))
  handlePre :=
    hybHandlePreC ae G kPRG kAEAD maxSkip q N N la
      (fun ia =>
        Comp.sample (O := hybOps CK MK AD M C ae G kPRG kAEAD)
          (I := multiRedIface CK MK AD M C ideal kIdeal)
          (Sum.inl () : Unit ⊕ UniformSamplerTag Bool) ia)
      (some (otSpecialEncC ae G kPRG kAEAD ideal kIdeal))
      (some (otSpecialDecC ae G kPRG kAEAD ideal kIdeal))
  chDone := hybChDoneC ae G kPRG kAEAD
  resume := hybResumeC ae G kPRG kAEAD maxSkip q la
  handlePost := hybHandlePostC ae G kPRG kAEAD
  finish := hybFinishAuthC ae G kPRG kAEAD

end Programs

end CryptoGames.FSAEAD.Thm5.Costed
