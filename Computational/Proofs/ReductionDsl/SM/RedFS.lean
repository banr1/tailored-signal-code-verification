/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.ReductionsQueries
public import Computational.Proofs.ReductionDsl.SM.Engine
public import Computational.Proofs.ReductionDsl.Size
import Computational.Proofs.ReductionDsl.SM.RedPRNG
import Computational.Proofs.ReductionDsl.Notation

/-!
# Costed FS-AEAD reductions for SM authenticity and privacy

Implements the single-session and multi-session `ReductionDsl.CostedReduction` FS-AEAD reductions
for SM authenticity and privacy (`redFSAuthProg`, `redFSPrivProg`, `redFSPrivCoinProg`,
`redFSPrivUniProg`, `redFSPrivUniCoinProg`, `redFSAuthMultiStage2Prog`), and proves simulation
evaluation agreement, `FSAEAD.fromAEADPRG` bridges, static query bounds, and static cost
characterizations.
-/

@[expose] public section

open ReductionDsl OracleSpec OracleComp

namespace CryptoGames.SM.Construction

open Engine Engine.RedPRNG CKA PRFPRNG
open scoped Computational.Proofs.ReductionDsl.Notation

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}

local notation "S" => prngSig KC Γ CCoins T I KR RSt K SS RS M E

/-! ## `FSState` and `VP` representations -/

@[reducible] def fsCacheEntryTy (KC Γ CCoins T I KR RSt K SS RS M E : Type) :
    Ty (prngSig KC Γ CCoins T I KR RSt K SS RS M E) :=
  .prod (.base .t) (.prod (.base .sig) (.prod (.base .k) .bool))

@[reducible] def fsTableEntryTy (KC Γ CCoins T I KR RSt K SS RS M E : Type) :
    Ty (prngSig KC Γ CCoins T I KR RSt K SS RS M E) :=
  .prod (.base .i) (.base .k)

@[reducible] def fsTransEntryTy (KC Γ CCoins T I KR RSt K SS RS M E : Type) :
    Ty (prngSig KC Γ CCoins T I KR RSt K SS RS M E) :=
  .prod .nat (ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)

@[reducible] def fsExtTy (KC Γ CCoins T I KR RSt K SS RS M E : Type) :
    Ty (prngSig KC Γ CCoins T I KR RSt K SS RS M E) :=
  .opt (.prod (.base .ss) (.base .rs))

/-- Encoding of `FSState` in `prngSig`: `(cache, table, sessions, fsTrans, fsCount, fsSCorr, ext)`. -/
@[reducible] def fsHsTy (KC Γ CCoins T I KR RSt K SS RS M E : Type) :
    Ty (prngSig KC Γ CCoins T I KR RSt K SS RS M E) :=
  .prod (.tbl (.opt (fsCacheEntryTy KC Γ CCoins T I KR RSt K SS RS M E)))
    (.prod (.list (fsTableEntryTy KC Γ CCoins T I KR RSt K SS RS M E))
      (.prod (.list (.base .i))
        (.prod (.list (fsTransEntryTy KC Γ CCoins T I KR RSt K SS RS M E))
          (.prod .nat
            (.prod .bool (fsExtTy KC Γ CCoins T I KR RSt K SS RS M E))))))

local notation "cacheEntryTy" => fsCacheEntryTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "tableEntryTy" => fsTableEntryTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "transEntryTy" => fsTransEntryTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "extTy" => fsExtTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hsTy" => fsHsTy KC Γ CCoins T I KR RSt K SS RS M E

def fsHsEnc (h : FSState T RSt K I SS RS E) : (hsTy).denote :=
  (h.cache, h.table, h.sessions, h.fsTrans, h.fsCount, h.fsSCorr, h.ext)

def fsHsDec (v : (hsTy).denote) :
    FSState T RSt K I SS RS E :=
  { cache := v.1
    table := v.2.1
    sessions := v.2.2.1
    fsTrans := v.2.2.2.1
    fsCount := v.2.2.2.2.1
    fsSCorr := v.2.2.2.2.2.1
    ext := v.2.2.2.2.2.2 }

@[simp] theorem fsHsDec_fsHsEnc (h : FSState T RSt K I SS RS E) :
    fsHsDec (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (fsHsEnc h) = h := by
  cases h; rfl

@[simp] theorem fsHsEnc_fsHsDec (v : (hsTy).denote) :
    fsHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M) (fsHsDec v) = v := by
  rcases v with ⟨c, tbl, ses, tr, cnt, sc, ex⟩; rfl

section FSStateExpr

def fsHsCache
    {O' : Ops S} {Γ'} (h : Expr O' Γ' hsTy) :
    Expr O' Γ' (.tbl (.opt cacheEntryTy)) := .fst h
def fsHsTable
    {O' : Ops S} {Γ'} (h : Expr O' Γ' hsTy) :
    Expr O' Γ' (.list tableEntryTy) := .fst (.snd h)
def fsHsSessions
    {O' : Ops S} {Γ'} (h : Expr O' Γ' hsTy) :
    Expr O' Γ' (.list (.base .i)) := .fst (.snd (.snd h))
def fsHsTrans
    {O' : Ops S} {Γ'} (h : Expr O' Γ' hsTy) :
    Expr O' Γ' (.list transEntryTy) := .fst (.snd (.snd (.snd h)))
def fsHsCount
    {O' : Ops S} {Γ'} (h : Expr O' Γ' hsTy) :
    Expr O' Γ' .nat := .fst (.snd (.snd (.snd (.snd h))))
def fsHsSCorr
    {O' : Ops S} {Γ'} (h : Expr O' Γ' hsTy) :
    Expr O' Γ' .bool := .fst (.snd (.snd (.snd (.snd (.snd h)))))
def fsHsExt
    {O' : Ops S} {Γ'} (h : Expr O' Γ' hsTy) :
    Expr O' Γ' extTy := .snd (.snd (.snd (.snd (.snd (.snd h)))))

def fsHsMk
    {O' : Ops S} {Γ'}
    (cache : Expr O' Γ' (.tbl (.opt cacheEntryTy)))
    (table : Expr O' Γ' (.list tableEntryTy))
    (sessions : Expr O' Γ' (.list (.base .i)))
    (trans : Expr O' Γ' (.list transEntryTy))
    (count : Expr O' Γ' .nat)
    (scorr : Expr O' Γ' .bool)
    (ext : Expr O' Γ' extTy) : Expr O' Γ' hsTy :=
  .pair cache (.pair table (.pair sessions (.pair trans (.pair count (.pair scorr ext)))))

def fsHsSetCache
    {O' : Ops S} {Γ'} (h : Expr O' Γ' hsTy)
    (c : Expr O' Γ' (.tbl (.opt cacheEntryTy))) : Expr O' Γ' hsTy :=
  fsHsMk c (fsHsTable h) (fsHsSessions h) (fsHsTrans h) (fsHsCount h) (fsHsSCorr h) (fsHsExt h)

def fsHsSetTable
    {O' : Ops S} {Γ'} (h : Expr O' Γ' hsTy)
    (tbl : Expr O' Γ' (.list tableEntryTy)) : Expr O' Γ' hsTy :=
  fsHsMk (fsHsCache h) tbl (fsHsSessions h) (fsHsTrans h) (fsHsCount h) (fsHsSCorr h) (fsHsExt h)

def fsHsSetSessions
    {O' : Ops S} {Γ'} (h : Expr O' Γ' hsTy)
    (ses : Expr O' Γ' (.list (.base .i))) : Expr O' Γ' hsTy :=
  fsHsMk (fsHsCache h) (fsHsTable h) ses (fsHsTrans h) (fsHsCount h) (fsHsSCorr h) (fsHsExt h)

def fsHsSetTrans
    {O' : Ops S} {Γ'} (h : Expr O' Γ' hsTy)
    (tr : Expr O' Γ' (.list transEntryTy)) : Expr O' Γ' hsTy :=
  fsHsMk (fsHsCache h) (fsHsTable h) (fsHsSessions h) tr (fsHsCount h) (fsHsSCorr h) (fsHsExt h)

def fsHsSetCountTrans
    {O' : Ops S} {Γ'} (h : Expr O' Γ' hsTy) (cnt : Expr O' Γ' .nat)
    (tr : Expr O' Γ' (.list transEntryTy)) : Expr O' Γ' hsTy :=
  fsHsMk (fsHsCache h) (fsHsTable h) (fsHsSessions h) tr cnt (fsHsSCorr h) (fsHsExt h)

def fsHsSetSCorr
    {O' : Ops S} {Γ'} (h : Expr O' Γ' hsTy)
    (sc : Expr O' Γ' .bool) : Expr O' Γ' hsTy :=
  fsHsMk (fsHsCache h) (fsHsTable h) (fsHsSessions h) (fsHsTrans h) (fsHsCount h) sc (fsHsExt h)

def fsHsSetExt
    {O' : Ops S} {Γ'} (h : Expr O' Γ' hsTy)
    (ex : Expr O' Γ' extTy) : Expr O' Γ' hsTy :=
  fsHsMk (fsHsCache h) (fsHsTable h) (fsHsSessions h) (fsHsTrans h) (fsHsCount h) (fsHsSCorr h) ex

def fsHsEmptyE
    {O' : Ops S} {Γ'} : Expr O' Γ' hsTy :=
  fsHsMk (.tconst .none) .nil .nil .nil (.nat 0) (.bool false) .none

@[simp] theorem fsHsEmptyE_eval {O' : Ops S} {Γ'} (ρ : Env Γ') :
    (fsHsEmptyE (O' := O')).eval ρ =
      fsHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M)
        ({} : FSState T RSt K I SS RS E) := rfl

end FSStateExpr

@[reducible] def fsVpTy (KC Γ CCoins T I KR RSt K SS RS M E : Type) :
    Ty (prngSig KC Γ CCoins T I KR RSt K SS RS M E) :=
  @vpTblTy KC Γ CCoins T I KR RSt K SS RS M E
    (.base .γ) (.base .sig) (.opt (.base .ss)) (.opt (.base .rs))

local notation "vpTyFS" => fsVpTy KC Γ CCoins T I KR RSt K SS RS M E

@[reducible] def fsVpEnc (vp : VP Γ T RSt (Option SS) (Option RS)) : (vpTyFS).denote :=
  vpTblEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (RSt := RSt)
    (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
    (γvT := .base .γ) (svT := .base .sig) (ssvT := .opt (.base .ss)) (rsvT := .opt (.base .rs)) vp

@[reducible] def fsEsTy (KC Γ CCoins T I KR RSt K SS RS M E : Type) :
    Ty (prngSig KC Γ CCoins T I KR RSt K SS RS M E) :=
  esTy (fsVpTy KC Γ CCoins T I KR RSt K SS RS M E) (fsHsTy KC Γ CCoins T I KR RSt K SS RS M E)

local notation "esTyFS" => fsEsTy KC Γ CCoins T I KR RSt K SS RS M E

def FSHBounded (L : ℕ) (h : FSState T RSt K I SS RS E) : Prop :=
  h.table.length ≤ L ∧ h.sessions.length ≤ L ∧ h.fsTrans.length ≤ L

def FSHBoundedPost (L : ℕ) (h : FSState T RSt K I SS RS E) : Prop :=
  h.fsTrans.length ≤ L

/-! ## Costed helpers and `hooksFSC` -/

section HooksFSC

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

local notation "hdrTy" => ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrCtTy" => ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "psTy" => ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E

def tableLookupE (L : ℕ) {Γ'}
    (tblE : Expr OO Γ' (.list tableEntryTy))
    (ikE : Expr OO Γ' (.base .i)) :
    Expr OO Γ' (.opt (.base .k)) :=
  rdslExpr =>
    letE (tblE, ikE) fun (tbl0, ik0) =>
      foldrB L tbl0 none fun (ikEntry, kEntry) acc =>
        if Expr.op (O := OO) CKAOp.eqI (ik0, ikEntry) then some kEntry else acc

def lookupFC (L : ℕ) {Γ'}
    (hE : Expr OO Γ' hsTy)
    (ikE : Expr OO Γ' (.base .i)) :
    Comp OO II Γ' (.prod (.base .k) hsTy) :=
  rdsl do
    (h0, ik0) ← return (hE, ikE)
    match tableLookupE L (fsHsTable h0) ik0 with
    | none =>
      kNew ← sample (O := OO) (I := II) CKASamp.k ()
      return (kNew, fsHsSetTable h0 ((ik0, kNew) :: fsHsTable h0))
    | some kFound =>
      return (kFound, h0)

def sessionsMemE (L : ℕ) {Γ'}
    (sesE : Expr OO Γ' (.list (.base .i)))
    (ikE : Expr OO Γ' (.base .i)) :
    Expr OO Γ' .bool :=
  rdslExpr =>
    letE (sesE, ikE) fun (ses0, ik0) =>
      foldrB L ses0 false fun x acc =>
        orE (Expr.op (O := OO) CKAOp.eqI (x, ik0)) acc

def sessionsIdxOfE (L : ℕ) {Γ'}
    (sesE : Expr OO Γ' (.list (.base .i)))
    (ikE : Expr OO Γ' (.base .i)) :
    Expr OO Γ' .nat :=
  rdslExpr =>
    letE (sesE, ikE) fun (ses0, ik0) =>
      foldrB L ses0 0 fun x acc =>
        if Expr.op (O := OO) CKAOp.eqI (x, ik0) then 0 else acc + 1

def sessionsLenE (L : ℕ) {Γ'}
    (sesE : Expr OO Γ' (.list (.base .i))) :
    Expr OO Γ' .nat :=
  rdslExpr =>
    foldrB L sesE 0 fun _ acc => acc + 1

def sessionsAppendOneE (L : ℕ) {Γ'}
    (sesE : Expr OO Γ' (.list (.base .i)))
    (ikE : Expr OO Γ' (.base .i)) :
    Expr OO Γ' (.list (.base .i)) :=
  rdslExpr =>
    foldrB L sesE [ikE] fun x acc => x :: acc

def isExtE (L j : ℕ) {Γ'}
    (hE : Expr OO Γ' hsTy)
    (ikE : Expr OO Γ' (.base .i)) :
    Expr OO Γ' (.prod .bool hsTy) :=
  rdslExpr =>
    letE (hE, ikE) fun (h0, ik0) =>
      let ses0 := fsHsSessions h0
      if sessionsMemE L ses0 ik0 then
        (sessionsIdxOfE L ses0 ik0 == nat j, h0)
      else
        (sessionsLenE L ses0 == nat j, fsHsSetSessions h0 (sessionsAppendOneE L ses0 ik0))

def extOfE (L j : ℕ) {Γ'}
    (hE : Expr OO Γ' hsTy)
    (sidE : Expr OO Γ' (.opt (.base .i))) :
    Expr OO Γ' (.prod .bool hsTy) :=
  rdslExpr =>
    letE (hE, sidE) fun (h0, sid0) =>
      match sid0 with
      | none => (false, h0)
      | some ik => isExtE L j h0 ik

def rootFSC (L : ℕ) (mo : Mode) {Γ'}
    (hE : Expr OO Γ' hsTy)
    (tE : Expr OO Γ' .nat)
    (ikE : Expr OO Γ' (.base .i))
    (σE : Expr OO Γ' (.base .sig)) :
    Comp OO II Γ'
      (.prod (.prod (.base .sig) (.prod (.base .k) (.opt (.base .i)))) hsTy) :=
  rdsl do
    (h0, t0, ik0, σ0) ← return (hE, tE, ikE, σE)
    let pIk := Expr.op (O := OO) CKAOp.prngUp (σ0, ik0)
    if nat mo.tStar < t0 then
      return ((pIk.1, pIk.2, none), h0)
    else if t0 == nat mo.tStar then
      if bool mo.tL.isSome && (t0 == nat mo.tH) then
        ir ← sample (O := OO) (I := II) CKASamp.i ()
        kSample ← sample (O := OO) (I := II) CKASamp.k ()
        let pIr := Expr.op (O := OO) CKAOp.prngUp (σ0, ir)
        return ((pIr.1, kSample, some ir), h0)
      else
        (kLookup, h1) ← lookupFC L h0 ik0
        return ((pIk.1, kLookup, some ik0), h1)
    else if bool mo.tL.isSome && (t0 == nat mo.tH) then
      ir ← sample (O := OO) (I := II) CKASamp.i ()
      let pIr := Expr.op (O := OO) CKAOp.prngUp (σ0, ir)
      return ((pIr.1, pIr.2, none), h0)
    else
      return ((pIk.1, pIk.2, none), h0)

def fsStartSendC (L : ℕ) (mo : Mode) (j : ℕ) {Γ'}
    (hE : Expr OO Γ' hsTy)
    (_ctxE : Expr OO Γ' (cGsTy vpTyFS))
    (_pE : Expr OO Γ' .bool)
    (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' (.base .γ))
    (σE : Expr OO Γ' (.base .sig))
    (rE : Expr OO Γ' (.opt (.base .ccoins))) :
    Comp OO II Γ'
      (.prod (.opt (.prod (.base .γ)
        (.prod (.base .t) (.prod (.base .sig) (.opt (.base .ss))))))
        hsTy) :=
  rdsl do
    (h0, t0, γ0, σ0, r0) ← return (hE, tE, γE, σE, rE)
    coins ←
      match r0 with
      | none => sample (O := OO) (I := II) CKASamp.ccoins ()
      | some c => return c
    let cOut := Expr.op (O := OO) CKAOp.ckaSend (γ0, coins)
    ((σ', kVal, sid), h1) ← rootFSC L mo h0 t0 cOut.2.2 σ0
    let extPair := extOfE L j h1 sid
    let ext := extPair.1
    let h2 := extPair.2
    let tMsg := cOut.2.1
    let cache' := tset (fsHsCache h2) t0 (some (tMsg, σ', kVal, ext))
    let h3 := fsHsSetCache h2 cache'
    let ssv := if ext then none else some (Expr.op (O := OO) CKAOp.fsInitSender kVal)
    return (some (cOut.1, tMsg, σ', ssv), h3)

def fsStartRecvC (L : ℕ) (mo : Mode) (j : ℕ) {Γ'}
    (hE : Expr OO Γ' hsTy)
    (_ctxE : Expr OO Γ' (cGsTy vpTyFS))
    (_pE : Expr OO Γ' .bool)
    (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' (.base .γ))
    (σE : Expr OO Γ' (.base .sig))
    (tnE : Expr OO Γ' (.base .t)) :
    Comp OO II Γ'
      (.prod (.opt (.opt (.prod (.base .γ) (.prod (.base .sig) (.opt (.base .rs))))))
        hsTy) :=
  rdsl do
    (h0, t0, γ0, σ0, tn0) ← return (hE, tE, γE, σE, tnE)
    let honest :=
      match tget (fsHsCache h0) t0 with
      | none => none
      | some (tCached, entry) =>
        if Expr.op (O := OO) CKAOp.eqT (tCached, tn0) then some entry else none
    match honest with
    | none =>
      if bool mo.auth && (t0 == nat mo.tStar) then
        if bool (mo.tL.isSome && decide (mo.tStar = mo.tH)) then
          return (none, h0)
        else
          let kk := Expr.op (O := OO) CKAOp.ckaReceive (γ0, tn0)
          (k', h1) ← lookupFC L h0 kk.2
          let extPair := isExtE L j h1 kk.2
          let ext := extPair.1
          let h2 := extPair.2
          let σ' := (Expr.op (O := OO) CKAOp.prngUp (σ0, kk.2)).1
          let rsv := if ext then none else some (Expr.op (O := OO) CKAOp.fsInitReceiver k')
          return (some (some (kk.1, σ', rsv)), h2)
      else
        return (some none, h0)
    | some (σc, kVal, ext) =>
      let γ' := (Expr.op (O := OO) CKAOp.ckaReceive (γ0, tn0)).1
      let rsv := if ext then none else some (Expr.op (O := OO) CKAOp.fsInitReceiver kVal)
      return (some (some (γ', σc, rsv)), h0)

def fsFsSendC (Δcka : ℕ) {Γ'}
    (hE : Expr OO Γ' hsTy)
    (ctxE : Expr OO Γ' (cGsTy vpTyFS))
    (pE : Expr OO Γ' .bool)
    (_tE : Expr OO Γ' .nat)
    (ssvE : Expr OO Γ' (.opt (.base .ss)))
    (hdrE : Expr OO Γ' hdrTy)
    (mE : Expr OO Γ' (.base .msg))
    (pairE : Expr OO Γ' (.opt (.prod (.base .msg) (.base .msg)))) :
    Comp OO II Γ' (.prod (.opt (.prod (.opt (.base .ss)) (.base .ct))) hsTy) :=
  rdsl do
    (h0, ctx0, p0, ssv0, hdr0, m0, pair0) ← return (hE, ctxE, pE, ssvE, hdrE, mE, pairE)
    match ssv0 with
    | none =>
      match fsHsExt h0 with
      | none =>
        (ok, h1) ←
          if !(cSafeChE (raw (2 + Δcka)) ctx0 p0) && !(fsHsSCorr h0) then
            csOpt ← query (O := OO) (I := II) FSHdrTag.cs ()
            match csOpt with
            | none => return (false, h0)
            | some _ => return (true, fsHsSetSCorr h0 true)
          else
            return (true, h0)
        if !ok then
          return (none, h1)
        else
          ctOpt ←
            match pair0 with
            | none => query (O := OO) (I := II) FSHdrTag.tr (hdr0, m0)
            | some mPair => query (O := OO) (I := II) FSHdrTag.ch (hdr0, mPair)
          match ctOpt with
          | none => return (none, h1)
          | some ct =>
            let cnt' := fsHsCount h1 + 1
            let tr' := (cnt', hdr0, ct) :: fsHsTrans h1
            return (some (none, ct), fsHsSetCountTrans h1 cnt' tr')
      | some (ss, rs) =>
        let o := Expr.op (O := OO) CKAOp.fsSend (ss, hdr0, m0)
        let h1 := fsHsSetExt h0 (some (o.1, rs))
        return (some (none, o.2), h1)
    | some ss =>
      let o := Expr.op (O := OO) CKAOp.fsSend (ss, hdr0, m0)
      return (some (some o.1, o.2), h0)

def fsTransFindE (L : ℕ) {Γ'}
    (trE : Expr OO Γ' (.list transEntryTy))
    (hcE : Expr OO Γ' hdrCtTy) :
    Expr OO Γ' (.opt transEntryTy) :=
  rdslExpr =>
    letE (trE, hcE) fun (tr0, hc0) =>
      findB L tr0 fun x => hdrCtEqE x.2 hc0

def fsTransFilterE (L : ℕ) {Γ'}
    (trE : Expr OO Γ' (.list transEntryTy))
    (dropE : Expr OO Γ' .nat) :
    Expr OO Γ' (.list transEntryTy) :=
  rdslExpr =>
    letE (trE, dropE) fun (tr0, drop0) =>
      foldrB L tr0 [] fun x acc =>
        if !(x.1 == drop0) then x :: acc else acc

def fsFsRecvC (L B : ℕ) {Γ'}
    (hE : Expr OO Γ' hsTy)
    (_ctxE : Expr OO Γ' (cGsTy vpTyFS))
    (_pE : Expr OO Γ' .bool)
    (_tE : Expr OO Γ' .nat)
    (rsvE : Expr OO Γ' (.opt (.base .rs)))
    (hdrE : Expr OO Γ' hdrTy)
    (eE : Expr OO Γ' (.base .ct))
    (recE : Expr OO Γ' (.opt cRecTy)) :
    Comp OO II Γ'
      (.prod (.opt (.opt (.prod (.opt (.base .rs)) (.prod .nat (.base .msg))))) hsTy) :=
  rdsl do
    (h0, rsv0, hdr0, e0, rec0) ← return (hE, rsvE, hdrE, eE, recE)
    match rsv0 with
    | none =>
      match fsHsExt h0 with
      | none =>
        let matched := fsTransFindE L (fsHsTrans h0) (hdr0, e0)
        resOpt ←
          match matched with
          | none => query (O := OO) (I := II) FSHdrTag.ij (hdr0, e0)
          | some _ => query (O := OO) (I := II) FSHdrTag.dl (hdr0, e0)
        match resOpt with
        | none => return (none, h0)
        | some resSum =>
          match resSum with
          | .inl _ => return (some none, h0)
          | .inr (msgIdx, mo') =>
            let drop :=
              match matched with
              | none => msgIdx
              | some entry => entry.1
            let h4 := fsHsSetTrans h0 (fsTransFilterE L (fsHsTrans h0) drop)
            let outE :=
              match mo' with
              | none =>
                match rec0 with
                | none => none
                | some r => some (some (none, msgIdx, cRecMsg r))
              | some msg => some (some (none, msgIdx, msg))
            return (outE, h4)
      | some (ss, rs) =>
        match Expr.op (O := OO) (CKAOp.fsReceive B) (rs, hdr0, e0) with
        | none => return (some none, h0)
        | some (rs', idxMsg) =>
          return (some (some (none, idxMsg)), fsHsSetExt h0 (some (ss, rs')))
    | some rs =>
      match Expr.op (O := OO) (CKAOp.fsReceive B) (rs, hdr0, e0) with
      | none => return (some none, h0)
      | some (rs', idxMsg) =>
        return (some (some (some rs', idxMsg)), h0)

def fsCommitC {Γ'}
    (hE : Expr OO Γ' hsTy)
    (_ctxE : Expr OO Γ' (cGsTy vpTyFS))
    (_pE : Expr OO Γ' .bool)
    (_oldE newE : Expr OO Γ' vpTyFS) :
    Comp OO II Γ' (.prod (.opt vpTyFS) hsTy) :=
  rdsl do
    return (some newE, hE)

/-- Builds `[L - 1, ..., 0]` via `Comp.iter` so AST size scales with `bits L`. -/
def rangeListC {S' : Sig} {O' : Ops S'} {ι : Type} {spec : OracleSpec ι}
    {I' : Iface S' spec} (L : ℕ) {Γ' : List (Ty S')} : Comp O' I' Γ' (.list .nat) :=
  .bind
    (.iter L (.pair (.nat 0) .nil)
      (.ret (.pair (.add (.fst .v0) (.nat 1)) (.cons (.fst .v0) (.snd .v0)))))
    (.ret (.snd .v0))

def unliftEntryE {Γ'}
    (entryE : Expr OO Γ' (.opt (.opt (.base .rs))))
    (rsExtE : Expr OO Γ' (.opt (.base .rs))) :
    Expr OO Γ' (.opt (.base .rs)) :=
  rdslExpr =>
    letE (entryE, rsExtE) fun (entry0, rsExt0) =>
      match entry0 with
      | none => none
      | some innerOpt =>
        match innerOpt with
        | none => rsExt0
        | some rs => some rs

def unliftVRE (L : ℕ) {Γ'}
    (vRE : Expr OO Γ' (.tbl (.opt (.opt (.base .rs)))))
    (rsExtE : Expr OO Γ' (.opt (.base .rs)))
    (rngE : Expr OO Γ' (.list .nat)) :
    Expr OO Γ' (.tbl (.opt (.base .rs))) :=
  rdslExpr =>
    letE ((vRE, rsExtE), rngE) fun ((vR0, rsExt0), rng0) =>
      foldrB L rng0 (tconst none) fun idx acc =>
        tset acc idx (unliftEntryE (tget vR0 idx) rsExt0)

def fsRevealC (L : ℕ) (mo : Mode) {Γ'}
    (hE : Expr OO Γ' hsTy)
    (_ctxE : Expr OO Γ' (cGsTy vpTyFS))
    (_pE : Expr OO Γ' .bool)
    (vpE : Expr OO Γ' vpTyFS) :
    Comp OO II Γ' (.prod (.opt psTy) hsTy) :=
  rdsl do
    (h0, vp0) ← return (hE, vpE)
    (ssOptOpt, h1) ←
      match vpVS vp0 with
      | none => return (some none, h0)
      | some ssv =>
        match ssv with
        | none =>
          match fsHsExt h0 with
          | none =>
            csOpt ← query (O := OO) (I := II) FSHdrTag.cs ()
            match csOpt with
            | none => return (none, h0)
            | some ss => return (some (some ss), fsHsSetSCorr h0 true)
          | some (ss, _) =>
            return (some (some ss), h0)
        | some ss =>
          return (some (some ss), h0)
    match ssOptOpt with
    | none => return (none, h1)
    | some ssReal =>
      (rsExtOpt, h2) ←
        match tget (vpVR vp0) (nat mo.tStar) with
        | none => return (some none, h1)
        | some rsv =>
          match rsv with
          | none =>
            match fsHsExt h1 with
            | none =>
              if bool mo.auth then
                return (none, h1)
              else
                crOpt ← query (O := OO) (I := II) FSHdrTag.cr ()
                match crOpt with
                | none => return (none, h1)
                | some extPair@(_, rs) =>
                  return (some (some rs), fsHsSetExt h1 (some extPair))
            | some (_, rs) =>
              return (some (some rs), h1)
          | some _ =>
            return (some none, h1)
      match rsExtOpt with
      | none => return (none, h2)
      | some rsExt =>
        rng ← rangeListC (O' := OO) (I' := II) L
        let vR' := unliftVRE L (vpVR vp0) rsExt rng
        return (some (realPartyE vp0 (vpΓ vp0) (vpRoot vp0) ssReal vR'), h2)

/-- Costed `HooksC` bundle for single-session `redFS`. -/
def hooksFSC (L B Δcka : ℕ) (mo : Mode) (j : ℕ) :
    HooksC OO II (.base .γ) (.base .sig) (.opt (.base .ss)) (.opt (.base .rs)) hsTy where
  startSend := fsStartSendC L mo j
  startRecv := fsStartRecvC L mo j
  fsSend := fsFsSendC Δcka
  fsRecv := fsFsRecvC L B
  commit := fsCommitC
  reveal := fsRevealC L mo

end HooksFSC

/-! ## Hook evaluation agreement -/

section HooksFSEval

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

local notation "hdrTy" => ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrCtTy" => ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "psTy" => ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hsEnc" => fsHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M)
local notation "hsDec" => fsHsDec (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (M := M)
local notation "vpEnc" =>
  fsVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (K := K) (M := M) (E := E)

theorem foldr_lookup_eq [DecidableEq I] (ik : I) (tbl : List (I × K)) :
    tbl.foldr (fun x (acc : Option K) => if (ik == x.1) = true then some x.2 else acc) none =
      tbl.lookup ik := by
  induction tbl with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    simp only [List.foldr_cons, List.lookup_cons, ih]
    cases ik == k <;> rfl

theorem tableLookupE_eval [DecidableEq I] (heqI : eqI = (· == ·))
    (L : ℕ) {Γ'} (tblE : Expr OO Γ' (.list tableEntryTy)) (ikE : Expr OO Γ' (.base .i))
    (ρ : Env Γ') (hL : (tblE.eval ρ).length ≤ L) :
    (tableLookupE L tblE ikE).eval ρ = (tblE.eval ρ).lookup (ikE.eval ρ) := by
  have htake : (tblE.eval ρ).take L = tblE.eval ρ := List.take_of_length_le hL
  simp only [tableLookupE, prngOps, ckaOps, heqI, Expr.eval, Expr.v0, Expr.v1, Expr.v2,
    Env.get_cons_zero, Env.get_cons_succ, htake]
  exact foldr_lookup_eq (ikE.eval ρ) (tblE.eval ρ)

theorem lookupFC_eval [DecidableEq I] [SampleableType K]
    (heqI : eqI = (· == ·))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (L : ℕ) {Γ'} (hE : Expr OO Γ' hsTy) (ikE : Expr OO Γ' (.base .i))
    (ρ : Env Γ') (h : FSState T RSt K I SS RS E)
    (hh : hE.eval ρ = hsEnc h) (hL : h.table.length ≤ L) :
    (lookupFC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L hE ikE).eval ρ =
      Prod.map id hsEnc <$>
        (lookupF (T := T) (Sig := RSt) (K := K) (I := I) (SS := SS) (RS := RS) (M := M) (E := E)
          (ikE.eval ρ)).run h ∧
    ∀ res ∈ support ((lookupF (T := T) (Sig := RSt) (K := K) (I := I) (SS := SS) (RS := RS)
        (M := M) (E := E) (ikE.eval ρ)).run h),
      res.2.table.length ≤ h.table.length + 1 ∧
      res.2.sessions = h.sessions ∧
      res.2.fsTrans = h.fsTrans := by
  unfold lookupFC lookupF
  rw [eval_bind_ret]
  set Ik : I := ikE.eval ρ
  have h0 : (Expr.pair hE ikE).eval ρ = (hsEnc h, Ik) := by simp [Expr.eval, hh, Ik]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod hsTy (.base CKASort.i)) (hsEnc h, Ik) ρ
  have hTbl : (tableLookupE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      L (fsHsTable (.fst .v0)) (.snd .v0)).eval ρ₁ = h.table.lookup Ik := by
    rw [tableLookupE_eval heqI L (fsHsTable (.fst .v0)) (.snd .v0) ρ₁
      (by simpa [ρ₁, fsHsTable, fsHsEnc, Expr.eval, Expr.v0] using hL)]
    rfl
  rw [eval_caseOpt, hTbl]
  rcases hlk : h.table.lookup Ik with _ | k
  · refine ⟨?_, ?_⟩
    · simp only [hlk, eval_bind, StateT.run_bind, StateT.run_get,
        StateT.run_lift, StateT.run_modify, StateT.run_pure, pure_bind, bind_assoc, map_bind]
      have hSamp : (@Comp.sample _ _ _ OO II _ CKASamp.k .unit).eval ρ₁ =
          (sampleT K : TComp (FSAEAD.spec SS RS (Header T) M E) K) := by
        simp only [Comp.eval, fsaeadHeaderAdIface, prngSamplers, ckaSamplers, hSampK, sampleT]
        exact liftP_eq_liftM II (fun _ => rfl) ($ᵗ K)
      rw [hSamp]
      refine bind_congr fun k' => ?_
      simp [ρ₁, Comp.eval, fsHsSetTable, fsHsMk, fsHsCache, fsHsTable, fsHsSessions,
        fsHsTrans, fsHsCount, fsHsSCorr, fsHsExt, fsHsEnc, Prod.map,
        Expr.eval, Expr.v0, Expr.v1]
    · intro res hmem
      simp only [hlk, StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_modify,
        StateT.run_pure, pure_bind, bind_assoc, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hmem
      obtain ⟨k', _, rfl⟩ := hmem
      exact ⟨by simp, rfl, rfl⟩
  · refine ⟨?_, ?_⟩
    · simp [ρ₁, hlk, Comp.eval, StateT.run_bind, StateT.run_get,
        StateT.run_pure, pure_bind, Prod.map, Expr.eval, Expr.v0, Expr.v1]
    · intro res hmem
      simp only [hlk, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff] at hmem
      subst hmem
      exact ⟨Nat.le_add_right _ _, rfl, rfl⟩

theorem foldr_mem_eq [DecidableEq I] (ik : I) (ses : List I) :
    ses.foldr (fun x (acc : Bool) => if (x == ik) = true then true else acc) false =
      decide (ik ∈ ses) := by
  induction ses with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldr_cons, ih, List.mem_cons]
    by_cases h : hd = ik
    · subst h; simp
    · have hne : ik ≠ hd := Ne.symm h
      simp [h, hne]

theorem sessionsMemE_eval [DecidableEq I] (heqI : eqI = (· == ·))
    (L : ℕ) {Γ'} (sesE : Expr OO Γ' (.list (.base .i))) (ikE : Expr OO Γ' (.base .i))
    (ρ : Env Γ') (hL : (sesE.eval ρ).length ≤ L) :
    (sessionsMemE L sesE ikE).eval ρ = decide (ikE.eval ρ ∈ sesE.eval ρ) := by
  have htake : (sesE.eval ρ).take L = sesE.eval ρ := List.take_of_length_le hL
  simp only [sessionsMemE, orE, prngOps, ckaOps, heqI, Expr.eval, Expr.v0, Expr.v1, Expr.v2,
    Env.get_cons_zero, Env.get_cons_succ, htake]
  exact foldr_mem_eq (ikE.eval ρ) (sesE.eval ρ)

theorem foldr_idxOf_eq [DecidableEq I] (ik : I) (ses : List I) :
    ses.foldr (fun x (acc : ℕ) => if (x == ik) = true then 0 else acc + 1) 0 =
      ses.idxOf ik := by
  induction ses with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldr_cons, ih, List.idxOf_cons]

theorem sessionsIdxOfE_eval [DecidableEq I] (heqI : eqI = (· == ·))
    (L : ℕ) {Γ'} (sesE : Expr OO Γ' (.list (.base .i))) (ikE : Expr OO Γ' (.base .i))
    (ρ : Env Γ') (hL : (sesE.eval ρ).length ≤ L) :
    (sessionsIdxOfE L sesE ikE).eval ρ = (sesE.eval ρ).idxOf (ikE.eval ρ) := by
  have htake : (sesE.eval ρ).take L = sesE.eval ρ := List.take_of_length_le hL
  simp only [sessionsIdxOfE, prngOps, ckaOps, heqI, Expr.eval, Expr.v0, Expr.v1, Expr.v2,
    Env.get_cons_zero, Env.get_cons_succ, htake]
  exact foldr_idxOf_eq (ikE.eval ρ) (sesE.eval ρ)

theorem foldr_len_eq {α : Type} (l : List α) :
    l.foldr (fun _ (acc : ℕ) => acc + 1) 0 = l.length := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem sessionsLenE_eval (L : ℕ) {Γ'} (sesE : Expr OO Γ' (.list (.base .i)))
    (ρ : Env Γ') (hL : (sesE.eval ρ).length ≤ L) :
    (sessionsLenE L sesE).eval ρ = (sesE.eval ρ).length := by
  have htake : (sesE.eval ρ).take L = sesE.eval ρ := List.take_of_length_le hL
  simp only [sessionsLenE, Expr.eval, Expr.v1, Env.get_cons_zero, Env.get_cons_succ, htake]
  exact foldr_len_eq (sesE.eval ρ)

theorem foldr_append_one_eq {α : Type} (a : α) (l : List α) :
    l.foldr (fun x acc => x :: acc) [a] = l ++ [a] := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem sessionsAppendOneE_eval (L : ℕ) {Γ'} (sesE : Expr OO Γ' (.list (.base .i)))
    (ikE : Expr OO Γ' (.base .i)) (ρ : Env Γ') (hL : (sesE.eval ρ).length ≤ L) :
    (sessionsAppendOneE L sesE ikE).eval ρ = sesE.eval ρ ++ [ikE.eval ρ] := by
  have htake : (sesE.eval ρ).take L = sesE.eval ρ := List.take_of_length_le hL
  simp only [sessionsAppendOneE, Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero,
    Env.get_cons_succ, htake]
  exact foldr_append_one_eq (ikE.eval ρ) (sesE.eval ρ)

@[simp] theorem fst_eval {S' : Sig} {O' : Ops S'} {Γ' : List (Ty S')} {a b : Ty S'}
    (e : Expr O' Γ' (.prod a b)) (ρ : Env Γ') :
    (Expr.fst e).eval ρ = (e.eval ρ).1 := rfl

@[simp] theorem snd_eval {S' : Sig} {O' : Ops S'} {Γ' : List (Ty S')} {a b : Ty S'}
    (e : Expr O' Γ' (.prod a b)) (ρ : Env Γ') :
    (Expr.snd e).eval ρ = (e.eval ρ).2 := rfl

@[simp] theorem eqN_eval {S' : Sig} {O' : Ops S'} {Γ' : List (Ty S')}
    (a b : Expr O' Γ' .nat) (ρ : Env Γ') :
    (Expr.eqN a b).eval ρ = decide (a.eval ρ = b.eval ρ) := rfl

theorem isExtE_eval_pair [DecidableEq I] (heqI : eqI = (· == ·))
    (L j : ℕ) {Γ'} (hE : Expr OO Γ' hsTy) (ikE : Expr OO Γ' (.base .i))
    (ρ : Env Γ') (h : FSState T RSt K I SS RS E)
    (hh : hE.eval ρ = hsEnc h) (hL : h.sessions.length ≤ L) :
    ((isExt (T := T) (Sig := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
        j (ikE.eval ρ)).run h) =
      pure (let p := (isExtE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        L j hE ikE).eval ρ; (p.1, hsDec p.2)) ∧
    let p := (isExtE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        L j hE ikE).eval ρ
    p.2 = hsEnc (hsDec p.2) ∧
    (hsDec p.2).table = h.table ∧
    (hsDec p.2).sessions.length ≤ h.sessions.length + 1 ∧
    (hsDec p.2).fsTrans = h.fsTrans := by
  unfold isExt isExtE
  rw [letE_eval]
  set Ik : I := ikE.eval ρ
  have h0 : (Expr.pair hE ikE).eval ρ = (hsEnc h, Ik) := by simp [Expr.eval, hh, Ik]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod hsTy (.base CKASort.i)) (hsEnc h, Ik) ρ
  have hMem : (sessionsMemE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM)
      (eqE := eqE) (lam := lam) (defaultE := defaultE)
      L (fsHsSessions (.fst .v0)) (.snd .v0)).eval ρ₁ = decide (Ik ∈ h.sessions) :=
    sessionsMemE_eval heqI L (fsHsSessions (.fst .v0)) (.snd .v0) ρ₁
      (by simpa [ρ₁, fsHsSessions, fsHsEnc, Expr.eval, Expr.v0] using hL)
  have hIdx : (sessionsIdxOfE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM)
      (eqE := eqE) (lam := lam) (defaultE := defaultE)
      L (fsHsSessions (.fst .v0)) (.snd .v0)).eval ρ₁ = List.idxOf Ik h.sessions :=
    sessionsIdxOfE_eval heqI L (fsHsSessions (.fst .v0)) (.snd .v0) ρ₁
      (by simpa [ρ₁, fsHsSessions, fsHsEnc, Expr.eval, Expr.v0] using hL)
  have hLen : (sessionsLenE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM)
      (eqE := eqE) (lam := lam) (defaultE := defaultE)
      L (fsHsSessions (.fst .v0))).eval ρ₁ = h.sessions.length :=
    sessionsLenE_eval L (fsHsSessions (.fst .v0)) ρ₁
      (by simpa [ρ₁, fsHsSessions, fsHsEnc, Expr.eval, Expr.v0] using hL)
  have hApp : (sessionsAppendOneE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM)
      (eqE := eqE) (lam := lam) (defaultE := defaultE)
      L (fsHsSessions (.fst .v0)) (.snd .v0)).eval ρ₁ = h.sessions ++ [Ik] :=
    sessionsAppendOneE_eval L (fsHsSessions (.fst .v0)) (.snd .v0) ρ₁
      (by simpa [ρ₁, fsHsSessions, fsHsEnc, Expr.eval, Expr.v0] using hL)
  rw [ite_eval, hMem]
  by_cases hm : Ik ∈ h.sessions
  · simp only [hm, decide_true, ↓reduceIte, pair_eval, eqN_eval, hIdx]
    simp [ρ₁, hm, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
      BEq.beq, Expr.eval, Expr.v0]
    exact decide_eq_decide.mpr Iff.rfl
  · simp only [hm, decide_false, Bool.false_eq_true, ↓reduceIte, pair_eval, eqN_eval,
      fsHsSetSessions, fsHsMk, hLen, hApp]
    simp [ρ₁, hm, fsHsCache, fsHsTable, fsHsTrans, fsHsCount, fsHsSCorr, fsHsExt,
      fsHsEnc, fsHsDec, StateT.run_bind, StateT.run_get, StateT.run_set,
      pure_bind, BEq.beq, Expr.eval, Expr.v0]
    exact decide_eq_decide.mpr Iff.rfl

theorem extOfE_eval_pair [DecidableEq I] (heqI : eqI = (· == ·))
    (L j : ℕ) {Γ'} (hE : Expr OO Γ' hsTy) (sidE : Expr OO Γ' (.opt (.base .i)))
    (ρ : Env Γ') (h : FSState T RSt K I SS RS E)
    (hh : hE.eval ρ = hsEnc h) (hL : h.sessions.length ≤ L) :
    ((extOf (T := T) (Sig := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
        j (sidE.eval ρ)).run h) =
      pure (let p := (extOfE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        L j hE sidE).eval ρ; (p.1, hsDec p.2)) ∧
    let p := (extOfE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        L j hE sidE).eval ρ
    p.2 = hsEnc (hsDec p.2) ∧
    (hsDec p.2).table = h.table ∧
    (hsDec p.2).sessions.length ≤ h.sessions.length + 1 ∧
    (hsDec p.2).fsTrans = h.fsTrans := by
  unfold extOf extOfE
  rw [letE_eval]
  rcases hsid : sidE.eval ρ with _ | Ik
  · simp [hsid, hh, StateT.run_pure, Expr.eval, Expr.v0]
  · simp only [hsid, Expr.eval, hh]
    exact isExtE_eval_pair (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) heqI L j (.fst .v1) .v0
      (Env.cons (t := .base CKASort.i) Ik
        (Env.cons (t := .prod hsTy (.opt (.base CKASort.i))) (hsEnc h, some Ik) ρ)) h rfl hL

theorem rootFSC_eval [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR RSt I K)
    (hPrngUp : prngUp = prng.up)
    (heqI : eqI = (· == ·))
    (hSampI : sampI = ($ᵗ I : ProbComp I))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (L : ℕ) (mo : Mode) {Γ'}
    (hE : Expr OO Γ' hsTy) (tE : Expr OO Γ' .nat)
    (ikE : Expr OO Γ' (.base .i)) (σE : Expr OO Γ' (.base .sig))
    (ρ : Env Γ') (h : FSState T RSt K I SS RS E)
    (hh : hE.eval ρ = hsEnc h) (hL : h.table.length ≤ L) :
    (rootFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L mo hE tE ikE σE).eval ρ =
      Prod.map id hsEnc <$>
        (rootFS (T := T) (SS := SS) (RS := RS) (M := M) (E := E)
          prng mo (tE.eval ρ) (ikE.eval ρ) (σE.eval ρ)).run h ∧
    ∀ res ∈ support ((rootFS (T := T) (SS := SS) (RS := RS) (M := M) (E := E)
        prng mo (tE.eval ρ) (ikE.eval ρ) (σE.eval ρ)).run h),
      res.2.table.length ≤ h.table.length + 1 ∧
      res.2.sessions = h.sessions ∧
      res.2.fsTrans = h.fsTrans := by
  unfold rootFSC rootFS
  rw [eval_bind_ret]
  set t : ℕ := tE.eval ρ
  set Ik : I := ikE.eval ρ
  set σ : RSt := σE.eval ρ
  have h0 : (Expr.pair hE (.pair tE (.pair ikE σE))).eval ρ = (hsEnc h, t, Ik, σ) := by
    simp [Expr.eval, hh, t, Ik, σ]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod hsTy (.prod .nat (.prod (.base CKASort.i) (.base CKASort.sig))))
    (hsEnc h, t, Ik, σ) ρ
  have hSampIComp : ∀ {Γ''} (ρ' : Env Γ''),
      (@Comp.sample _ _ _ OO II Γ'' CKASamp.i .unit).eval ρ' =
        (sampleT I : TComp (FSAEAD.spec SS RS (Header T) M E) I) := by
    intro Γ'' ρ'
    simp only [Comp.eval, fsaeadHeaderAdIface, prngSamplers, ckaSamplers, hSampI, sampleT]
    exact liftP_eq_liftM II (fun _ => rfl) ($ᵗ I)
  have hSampKComp : ∀ {Γ''} (ρ' : Env Γ''),
      (@Comp.sample _ _ _ OO II Γ'' CKASamp.k .unit).eval ρ' =
        (sampleT K : TComp (FSAEAD.spec SS RS (Header T) M E) K) := by
    intro Γ'' ρ'
    simp only [Comp.eval, fsaeadHeaderAdIface, prngSamplers, ckaSamplers, hSampK, sampleT]
    exact liftP_eq_liftM II (fun _ => rfl) ($ᵗ K)
  rw [eval_ite]
  have hlt1 : (Expr.lt (.nat mo.tStar) (.fst (.snd (Expr.v0 (O := OO))))).eval ρ₁ =
      decide (mo.tStar < t) := rfl
  rw [hlt1]
  by_cases hgt : mo.tStar < t
  · refine ⟨?_, ?_⟩
    · simp [ρ₁, hgt, Comp.eval, StateT.run_pure, hPrngUp, Prod.map, Expr.eval, Expr.v0]
    · intro res hmem
      simp only [hgt, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem
      exact ⟨Nat.le_add_right _ _, rfl, rfl⟩
  · simp only [hgt, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [eval_ite]
    have heq1 : (Expr.eqN (.fst (.snd (Expr.v0 (O := OO)))) (.nat mo.tStar)).eval ρ₁ =
        decide (t = mo.tStar) := rfl
    rw [heq1]
    by_cases hts : t = mo.tStar
    · have htsIf : (t = mo.tStar) ↔ True := by simp [hts]
      simp only [htsIf, decide_true, ↓reduceIte]
      rw [eval_ite]
      have hcond2 : (Expr.and (.bool mo.tL.isSome)
          (.eqN (.fst (.snd (Expr.v0 (O := OO)))) (.nat mo.tH))).eval ρ₁ =
          (mo.tL.isSome && decide (t = mo.tH)) := rfl
      rw [hcond2]
      by_cases htH : (mo.tL.isSome && decide (t = mo.tH)) = true
      · refine ⟨?_, ?_⟩
        · simp only [htH, ↓reduceIte, eval_bind, hSampIComp, StateT.run_bind,
            StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind, map_bind]
          refine bind_congr fun Ir => ?_
          simp only [hSampKComp]
          refine bind_congr fun k => ?_
          simp [ρ₁, Comp.eval, hPrngUp, Prod.map, Expr.eval, Expr.v0, Expr.v1, Expr.v2]
        · intro res hmem
          simp only [htH, ↓reduceIte, StateT.run_bind, StateT.run_lift, StateT.run_pure,
            bind_assoc, pure_bind, mem_support_bind_iff, support_pure,
            Set.mem_singleton_iff] at hmem
          obtain ⟨Ir, _, k, _, rfl⟩ := hmem
          exact ⟨Nat.le_add_right _ _, rfl, rfl⟩
      · simp only [htH, Bool.false_eq_true, ↓reduceIte]
        have hLk := lookupFC_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
          (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
          (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
          (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
          (sampCCoins := sampCCoins) (sampI := sampI)
          heqI hSampK L (.fst .v0) (.fst (.snd (.snd .v0))) ρ₁ h rfl hL
        have hIk1 : (Expr.fst (.snd (.snd (Expr.v0 (O := OO))))).eval ρ₁ = Ik := rfl
        rw [hIk1] at hLk
        refine ⟨?_, ?_⟩
        · rw [eval_bind, hLk.1, StateT.run_bind, bind_map_left, map_bind]
          refine bind_congr fun ⟨k, h'⟩ => ?_
          simp [ρ₁, Comp.eval, StateT.run_pure, hPrngUp, Prod.map, Expr.eval, Expr.v0, Expr.v1]
        · intro res hmem
          simp only [StateT.run_bind, StateT.run_pure, mem_support_bind_iff, support_pure,
            Set.mem_singleton_iff] at hmem
          obtain ⟨⟨k, h'⟩, hmemLk, rfl⟩ := hmem
          exact hLk.2 (k, h') hmemLk
    · simp only [hts, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [eval_ite]
      have hcond3 : (Expr.and (.bool mo.tL.isSome)
          (.eqN (.fst (.snd (Expr.v0 (O := OO)))) (.nat mo.tH))).eval ρ₁ =
          (mo.tL.isSome && decide (t = mo.tH)) := rfl
      rw [hcond3]
      by_cases htH : (mo.tL.isSome && decide (t = mo.tH)) = true
      · refine ⟨?_, ?_⟩
        · simp only [htH, ↓reduceIte, eval_bind, hSampIComp, StateT.run_bind,
            StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind, map_bind]
          refine bind_congr fun Ir => ?_
          simp [ρ₁, Comp.eval, hPrngUp, Prod.map, Expr.eval, Expr.v0, Expr.v1]
        · intro res hmem
          simp only [htH, ↓reduceIte, StateT.run_bind, StateT.run_lift, StateT.run_pure,
            bind_assoc, pure_bind, mem_support_bind_iff, support_pure,
            Set.mem_singleton_iff] at hmem
          obtain ⟨Ir, _, rfl⟩ := hmem
          exact ⟨Nat.le_add_right _ _, rfl, rfl⟩
      · refine ⟨?_, ?_⟩
        · simp [ρ₁, htH, Comp.eval, StateT.run_pure, hPrngUp, Prod.map, Expr.eval, Expr.v0]
        · intro res hmem
          simp only [htH, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, support_pure,
            Set.mem_singleton_iff] at hmem
          subst hmem
          exact ⟨Nat.le_add_right _ _, rfl, rfl⟩

theorem fsStartSendC_eval [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (hSend : ckaSend = cka.send)
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (heqI : eqI = (· == ·))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hSampI : sampI = ($ᵗ I : ProbComp I))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (L Δcka : ℕ) (mo : Mode) (j : ℕ)
    {Γ'} (hE : Expr OO Γ' hsTy) (ctxE : Expr OO Γ' (cGsTy vpTyFS))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' (.base .γ)) (σE : Expr OO Γ' (.base .sig))
    (rE : Expr OO Γ' (.opt (.base .ccoins))) (ρ : Env Γ')
    (h : FSState T RSt K I SS RS E) (ctx : Ctx Γ T RSt (Option SS) (Option RS) M E) (P : Party)
    (hHB : FSHBounded L h) (hh : hE.eval ρ = hsEnc h) :
    (fsStartSendC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L mo j hE ctxE pE tE γE σE rE).eval ρ =
      Prod.map id hsEnc <$>
        ((hooksFS cka prng fs Δcka mo j).startSend ctx P
          (tE.eval ρ) (γE.eval ρ) (σE.eval ρ) (rE.eval ρ)).run h ∧
    ∀ res ∈ support (((hooksFS cka prng fs Δcka mo j).startSend ctx P
        (tE.eval ρ) (γE.eval ρ) (σE.eval ρ) (rE.eval ρ)).run h),
      res.2.table.length ≤ h.table.length + 1 ∧
      res.2.sessions.length ≤ h.sessions.length + 1 ∧
      res.2.fsTrans = h.fsTrans := by
  unfold fsStartSendC
  rw [eval_bind_ret]
  set t : ℕ := tE.eval ρ
  set γ : Γ := γE.eval ρ
  set σ : RSt := σE.eval ρ
  set r : Option CCoins := rE.eval ρ
  have h0 : (Expr.pair hE (.pair tE (.pair γE (.pair σE rE)))).eval ρ =
      (hsEnc h, t, γ, σ, r) := by
    simp [Expr.eval, hh, t, γ, σ, r]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := .prod hsTy (.prod .nat (.prod (.base CKASort.γ)
      (.prod (.base CKASort.sig) (.opt (.base CKASort.ccoins))))))
    (hsEnc h, t, γ, σ, r) ρ
  have hStep1 :
      (Comp.caseOpt (O := OO) (I := II) (.snd (.snd (.snd (.snd .v0))))
        (@Comp.sample _ _ _ OO II _ CKASamp.ccoins .unit)
        (.ret .v0)).eval ρ₁ =
      (match r with
        | some c => pure c
        | none => (sampleT CCoins : TComp (FSAEAD.spec SS RS (Header T) M E) CCoins)) := by
    rcases r with _ | c
    · simp only [ρ₁, Comp.eval, Expr.eval, Expr.v0, Env.get_cons_zero,
        fsaeadHeaderAdIface, prngSamplers, ckaSamplers, hSampCCoins, sampleT]
      exact liftP_eq_liftM II (fun _ => rfl) ($ᵗ CCoins)
    · rfl
  have hRHS :
      ((hooksFS cka prng fs Δcka mo j).startSend ctx P t γ σ r).run h =
      ((match r with
          | some c => pure c
          | none => (sampleT CCoins : TComp (FSAEAD.spec SS RS (Header T) M E) CCoins)) >>=
        fun coins =>
          (do
            let c := cka.send γ coins
            let (σ', k, sid) ← rootFS prng mo t c.2.2 σ
            let ext ← extOf j sid
            modify fun (s : FSState T RSt K I SS RS E) =>
              { s with cache := Function.update s.cache t (some (c.2.1, σ', k, ext)) }
            return some (c.1, c.2.1, σ', if ext then none else some (fs.initSender k))).run h) := by
    unfold hooksFS; dsimp only
    rcases r with _ | c
    · simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
    · simp only [StateT.run_bind, pure_bind]
  rw [eval_bind, hStep1, hRHS, map_bind]
  refine ⟨bind_congr fun coins => ?_, ?_⟩
  · set ρ₂ := Env.cons (t := .base CKASort.ccoins) coins ρ₁
    rw [eval_bind]
    have hRoot := rootFSC_eval (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      prng hPrngUp heqI hSampI hSampK L mo (.fst .v1) (.fst (.snd .v1))
      (.snd (.snd (Expr.op (O := OO) CKAOp.ckaSend (.pair (.fst (.snd (.snd .v1))) .v0))))
      (.fst (.snd (.snd (.snd .v1)))) ρ₂ h rfl hHB.1
    have hRootArgs :
        ((Expr.fst (.snd (Expr.v1 (O := OO)))).eval ρ₂ = t) ∧
        ((Expr.snd (.snd (Expr.op (O := OO) CKAOp.ckaSend
          (.pair (.fst (.snd (.snd .v1))) .v0)))).eval ρ₂ = (cka.send γ coins).2.2) ∧
        ((Expr.fst (.snd (.snd (.snd (Expr.v1 (O := OO)))))).eval ρ₂ = σ) := by
      refine ⟨rfl, ?_, rfl⟩
      simp [ρ₂, ρ₁, hSend, Expr.eval, Expr.v0, Expr.v1]
    rw [hRootArgs.1, hRootArgs.2.1, hRootArgs.2.2] at hRoot
    rw [StateT.run_bind, hRoot.1, bind_map_left, map_bind]
    refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨σ', k, sid⟩, h₁⟩ hmemRoot => ?_
    have ⟨_, hSes₁, _⟩ := hRoot.2 ((σ', k, sid), h₁) hmemRoot
    have hSesL₁ : h₁.sessions.length ≤ L := hSes₁ ▸ hHB.2.1
    set ρ₃ := Env.cons
      (t := .prod
        (.prod (.base CKASort.sig) (.prod (.base CKASort.k) (.opt (.base CKASort.i)))) hsTy)
      ((σ', k, sid), hsEnc h₁) ρ₂
    have hExt := extOfE_eval_pair (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) heqI L j (.snd .v0) (.snd (.snd (.fst .v0))) ρ₃ h₁
      rfl hSesL₁
    have hSid : (Expr.snd (.snd (.fst (Expr.v0 (O := OO))))).eval ρ₃ = sid := rfl
    rw [hSid] at hExt
    rcases hExtPair : (extOfE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      L j (.snd .v0) (.snd (.snd (.fst .v0)))).eval ρ₃ with ⟨ext, h₂_enc⟩
    rw [hExtPair] at hExt
    rw [StateT.run_bind, hExt.1]
    simp only [pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure, map_pure,
      Prod.map, id_eq]
    change (Comp.ret _).eval ρ₃ = _
    simp only [eval_ret, pair_eval, some_eval, fst_eval, snd_eval, ite_eval,
      tset_eval_eq_update, fsHsSetCache, fsHsMk, fsHsCache, fsHsTable, fsHsSessions,
      fsHsTrans, fsHsCount, fsHsSCorr, fsHsExt, hExtPair, hExt.2.1]
    cases ext <;>
      simp [ρ₃, ρ₂, ρ₁, hSend, hFsInitS, fsHsEnc, Expr.eval, Expr.v0, Expr.v1, Expr.v2]
  · intro res hmem
    rw [mem_support_bind_iff] at hmem
    obtain ⟨coins, _, hmem⟩ := hmem
    simp only [StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨⟨σ', k, sid⟩, h₁⟩, hmemRoot, hmem⟩ := hmem
    have hRoot := (rootFSC_eval (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      prng hPrngUp heqI hSampI hSampK L mo (.fst .v1) (.fst (.snd .v1))
      (.snd (.snd (Expr.op (O := OO) CKAOp.ckaSend (.pair (.fst (.snd (.snd .v1))) .v0))))
      (.fst (.snd (.snd (.snd .v1)))) (Env.cons (t := .base CKASort.ccoins) coins ρ₁) h rfl hHB.1).2
      ((σ', k, sid), h₁) (by simpa [ρ₁, hSend, Expr.eval, Expr.v0, Expr.v1] using hmemRoot)
    have hSesL₁ : h₁.sessions.length ≤ L := hRoot.2.1 ▸ hHB.2.1
    set ρ₃ := Env.cons
      (t := .prod
        (.prod (.base CKASort.sig) (.prod (.base CKASort.k) (.opt (.base CKASort.i)))) hsTy)
      ((σ', k, sid), hsEnc h₁) (Env.cons (t := .base CKASort.ccoins) coins ρ₁)
    have hExt := extOfE_eval_pair (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) heqI L j (.snd .v0) (.snd (.snd (.fst .v0))) ρ₃ h₁
      rfl hSesL₁
    have hSid : (Expr.snd (.snd (.fst (Expr.v0 (O := OO))))).eval ρ₃ = sid := rfl
    rw [hSid] at hExt
    rw [hExt.1] at hmem
    simp only [support_pure, Set.mem_singleton_iff, exists_eq_left, StateT.run_modify,
      StateT.run_pure] at hmem
    subst hmem
    dsimp only
    exact ⟨by rw [hExt.2.2.1]; exact hRoot.1,
      by rw [← hRoot.2.1]; exact hExt.2.2.2.1,
      by rw [hExt.2.2.2.2, hRoot.2.2]⟩

theorem eval_caseOpt_none {S' : Sig} {O' : Ops S'} {ι : Type} {spec : OracleSpec ι}
    {I' : Iface S' spec} {Γ' : List (Ty S')} {a b : Ty S'}
    {e : Expr O' Γ' (.opt a)} {nb : Comp O' I' Γ' b} {sb : Comp O' I' (a :: Γ') b}
    {ρ : Env Γ'} (h : e.eval ρ = none) :
    (Comp.caseOpt e nb sb).eval ρ = nb.eval ρ := by
  rw [eval_caseOpt, h]

theorem eval_caseOpt_some {S' : Sig} {O' : Ops S'} {ι : Type} {spec : OracleSpec ι}
    {I' : Iface S' spec} {Γ' : List (Ty S')} {a b : Ty S'}
    {e : Expr O' Γ' (.opt a)} {nb : Comp O' I' Γ' b} {sb : Comp O' I' (a :: Γ') b}
    {ρ : Env Γ'} {v : a.denote} (h : e.eval ρ = some v) :
    (Comp.caseOpt e nb sb).eval ρ = sb.eval (.cons v ρ) := by
  rw [eval_caseOpt, h]

theorem eval_caseSum_inl {S' : Sig} {O' : Ops S'} {ι : Type} {spec : OracleSpec ι}
    {I' : Iface S' spec} {Γ' : List (Ty S')} {a b c : Ty S'}
    {e : Expr O' Γ' (.sum a b)} {lb : Comp O' I' (a :: Γ') c} {rb : Comp O' I' (b :: Γ') c}
    {ρ : Env Γ'} {v : a.denote} (h : e.eval ρ = .inl v) :
    (Comp.caseSum e lb rb).eval ρ = lb.eval (.cons v ρ) := by
  simp [Comp.eval, h]

theorem eval_caseSum_inr {S' : Sig} {O' : Ops S'} {ι : Type} {spec : OracleSpec ι}
    {I' : Iface S' spec} {Γ' : List (Ty S')} {a b c : Ty S'}
    {e : Expr O' Γ' (.sum a b)} {lb : Comp O' I' (a :: Γ') c} {rb : Comp O' I' (b :: Γ') c}
    {ρ : Env Γ'} {v : b.denote} (h : e.eval ρ = .inr v) :
    (Comp.caseSum e lb rb).eval ρ = rb.eval (.cons v ρ) := by
  simp [Comp.eval, h]

theorem fsStartRecvC_eval [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (hRecv : ckaReceive = cka.receive)
    (hPrngUp : prngUp = prng.up)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (heqT : eqT = (· == ·))
    (heqI : eqI = (· == ·))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (L Δcka : ℕ) (mo : Mode) (j : ℕ)
    {Γ'} (hE : Expr OO Γ' hsTy) (ctxE : Expr OO Γ' (cGsTy vpTyFS))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' (.base .γ)) (σE : Expr OO Γ' (.base .sig))
    (tnE : Expr OO Γ' (.base .t)) (ρ : Env Γ')
    (h : FSState T RSt K I SS RS E) (ctx : Ctx Γ T RSt (Option SS) (Option RS) M E) (P : Party)
    (hHB : FSHBounded L h) (hh : hE.eval ρ = hsEnc h) :
    (fsStartRecvC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L mo j hE ctxE pE tE γE σE tnE).eval ρ =
      Prod.map id hsEnc <$>
        ((hooksFS cka prng fs Δcka mo j).startRecv ctx P
          (tE.eval ρ) (γE.eval ρ) (σE.eval ρ) (tnE.eval ρ)).run h ∧
    ∀ res ∈ support (((hooksFS cka prng fs Δcka mo j).startRecv ctx P
        (tE.eval ρ) (γE.eval ρ) (σE.eval ρ) (tnE.eval ρ)).run h),
      res.2.table.length ≤ h.table.length + 1 ∧
      res.2.sessions.length ≤ h.sessions.length + 1 ∧
      res.2.fsTrans = h.fsTrans := by
  unfold fsStartRecvC hooksFS
  dsimp only
  rw [eval_bind_ret]
  set t : ℕ := tE.eval ρ
  set γ : Γ := γE.eval ρ
  set σ : RSt := σE.eval ρ
  set Tn : T := tnE.eval ρ
  have h0 : (Expr.pair hE (.pair tE (.pair γE (.pair σE tnE)))).eval ρ =
      (hsEnc h, t, γ, σ, Tn) := by
    simp [Expr.eval, hh, t, γ, σ, Tn]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := .prod hsTy (.prod .nat (.prod (.base CKASort.γ)
      (.prod (.base CKASort.sig) (.base CKASort.t)))))
    (hsEnc h, t, γ, σ, Tn) ρ
  have hNoneBranch :
      (Comp.ite (O := OO) (I := II) (.and (.bool mo.auth) (.eqN (.fst (.snd .v0)) (.nat mo.tStar)))
        (.ite (.bool (mo.tL.isSome && decide (mo.tStar = mo.tH)))
          (.ret (.pair .none (.fst .v0)))
          (.bind
            (lookupFC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
              (sampI := sampI) (sampK := sampK) L (.fst .v0)
              (.snd (Expr.op (O := OO) CKAOp.ckaReceive
                (.pair (.fst (.snd (.snd .v0))) (.snd (.snd (.snd (.snd .v0))))))))
            (.ret (.pair
              (.some (.some (.pair
                (.fst (Expr.op (O := OO) CKAOp.ckaReceive
                  (.pair (.fst (.snd (.snd .v1))) (.snd (.snd (.snd (.snd .v1)))))))
                (.pair
                  (.fst (Expr.op (O := OO) CKAOp.prngUp
                    (.pair (.fst (.snd (.snd (.snd .v1))))
                      (.snd (Expr.op (O := OO) CKAOp.ckaReceive
                        (.pair (.fst (.snd (.snd .v1))) (.snd (.snd (.snd (.snd .v1))))))))))
                  (.ite (.fst (isExtE L j (.snd .v0)
                      (.snd (Expr.op (O := OO) CKAOp.ckaReceive
                        (.pair (.fst (.snd (.snd .v1))) (.snd (.snd (.snd (.snd .v1)))))))))
                    .none
                    (.some (Expr.op (O := OO) CKAOp.fsInitReceiver (.fst .v0))))))))
              (.snd (isExtE L j (.snd .v0)
                (.snd (Expr.op (O := OO) CKAOp.ckaReceive
                  (.pair (.fst (.snd (.snd .v1))) (.snd (.snd (.snd (.snd .v1)))))))))))))
        (.ret (.pair (.some .none) (.fst .v0)))).eval ρ₁ =
      Prod.map id hsEnc <$>
        ((if (mo.auth && decide (t = mo.tStar)) = true then
            if (mo.tL.isSome && decide (mo.tStar = mo.tH)) = true then pure none
            else do
              let k' ← lookupF (cka.receive γ Tn).2
              let ext ← isExt j (cka.receive γ Tn).2
              pure (some (some ((cka.receive γ Tn).1, (prng.up σ (cka.receive γ Tn).2).1,
                if ext = true then none else some (fs.initReceiver k'))))
          else pure (some none) :
          HM (FSAEAD.spec SS RS (Header T) M E) (FSState T RSt K I SS RS E) _).run h) ∧
      ∀ res ∈ support
        ((if (mo.auth && decide (t = mo.tStar)) = true then
            if (mo.tL.isSome && decide (mo.tStar = mo.tH)) = true then pure none
            else do
              let k' ← lookupF (cka.receive γ Tn).2
              let ext ← isExt j (cka.receive γ Tn).2
              pure (some (some ((cka.receive γ Tn).1, (prng.up σ (cka.receive γ Tn).2).1,
                if ext = true then none else some (fs.initReceiver k'))))
          else pure (some none) :
          HM (FSAEAD.spec SS RS (Header T) M E) (FSState T RSt K I SS RS E) _).run h),
        res.2.table.length ≤ h.table.length + 1 ∧
        res.2.sessions.length ≤ h.sessions.length + 1 ∧
        res.2.fsTrans = h.fsTrans := by
    rw [eval_ite]
    have hCond1 : (Expr.and (.bool mo.auth)
        (.eqN (.fst (.snd (Expr.v0 (O := OO)))) (.nat mo.tStar))).eval ρ₁ =
        (mo.auth && decide (t = mo.tStar)) := rfl
    rw [hCond1]
    by_cases hc1 : (mo.auth && decide (t = mo.tStar)) = true
    · simp only [hc1, ↓reduceIte]
      rw [eval_ite]
      have hCond2 : (Expr.bool (O := OO) (mo.tL.isSome && decide (mo.tStar = mo.tH))).eval ρ₁ =
          (mo.tL.isSome && decide (mo.tStar = mo.tH)) := rfl
      rw [hCond2]
      by_cases hc2 : (mo.tL.isSome && decide (mo.tStar = mo.tH)) = true
      · simp only [hc2, ↓reduceIte]
        refine ⟨?_, ?_⟩
        · simp [ρ₁, StateT.run_pure, Comp.eval, Prod.map, Expr.eval, Expr.v0]
        · intro res hmem
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
          subst hmem
          exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, rfl⟩
      · simp only [hc2, Bool.false_eq_true, ↓reduceIte]
        have hLk := lookupFC_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
          (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
          (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
          (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
          (sampCCoins := sampCCoins) (sampI := sampI)
          heqI hSampK L (.fst .v0)
          (.snd (Expr.op (O := OO) CKAOp.ckaReceive
            (.pair (.fst (.snd (.snd .v0))) (.snd (.snd (.snd (.snd .v0))))))) ρ₁ h rfl hHB.1
        have hKk2 : (Expr.snd (Expr.op (O := OO) CKAOp.ckaReceive
            (.pair (.fst (.snd (.snd .v0))) (.snd (.snd (.snd (.snd .v0))))))).eval ρ₁ =
            (cka.receive γ Tn).2 := by
          simp [ρ₁, hRecv, Expr.eval, Expr.v0]
        rw [hKk2] at hLk
        refine ⟨?_, ?_⟩
        · rw [eval_bind, hLk.1, StateT.run_bind, bind_map_left, map_bind]
          refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨k', h₁⟩ hmemLk => ?_
          have ⟨_, hSes₁, _⟩ := hLk.2 (k', h₁) hmemLk
          have hSesL₁ : h₁.sessions.length ≤ L := hSes₁ ▸ hHB.2.1
          set ρ₂ := Env.cons (t := .prod (.base CKASort.k) hsTy) (k', hsEnc h₁) ρ₁
          have hExt := isExtE_eval_pair (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
            (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
            (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
            (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
            (lam := lam) (defaultE := defaultE) heqI L j (.snd .v0)
            (.snd (Expr.op (O := OO) CKAOp.ckaReceive
              (.pair (.fst (.snd (.snd .v1))) (.snd (.snd (.snd (.snd .v1))))))) ρ₂ h₁ rfl hSesL₁
          have hKk2' : (Expr.snd (Expr.op (O := OO) CKAOp.ckaReceive
              (.pair (.fst (.snd (.snd .v1))) (.snd (.snd (.snd (.snd .v1))))))).eval ρ₂ =
              (cka.receive γ Tn).2 := by
            simp [ρ₂, ρ₁, hRecv, Expr.eval, Expr.v1]
          rw [hKk2'] at hExt
          rcases hExtPair : (isExtE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
            (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
            (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
            (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
            (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
            L j (.snd .v0)
            (.snd (Expr.op (O := OO) CKAOp.ckaReceive
              (.pair (.fst (.snd (.snd .v1))) (.snd (.snd (.snd (.snd .v1)))))))).eval ρ₂ with
            ⟨ext, h₂_enc⟩
          rw [hExtPair] at hExt
          rw [StateT.run_bind, hExt.1]
          simp only [pure_bind, StateT.run_pure, map_pure, Prod.map, id_eq]
          change (Comp.ret _).eval ρ₂ = _
          simp only [eval_ret, pair_eval, some_eval, fst_eval, snd_eval, ite_eval,
            hExtPair, hExt.2.1]
          cases ext <;>
            simp [ρ₂, ρ₁, hRecv, hPrngUp, hFsInitR, Expr.eval, Expr.v0, Expr.v1]
        · intro res hmem
          simp only [StateT.run_bind, mem_support_bind_iff] at hmem
          obtain ⟨⟨k', h₁⟩, hmemLk, hmem⟩ := hmem
          have ⟨hTbl₁, hSes₁, hTr₁⟩ := hLk.2 (k', h₁) hmemLk
          have hSesL₁ : h₁.sessions.length ≤ L := hSes₁ ▸ hHB.2.1
          set ρ₂ := Env.cons (t := .prod (.base CKASort.k) hsTy) (k', hsEnc h₁) ρ₁
          have hExt := isExtE_eval_pair (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
            (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
            (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
            (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
            (lam := lam) (defaultE := defaultE) heqI L j (.snd .v0)
            (.snd (Expr.op (O := OO) CKAOp.ckaReceive
              (.pair (.fst (.snd (.snd .v1))) (.snd (.snd (.snd (.snd .v1))))))) ρ₂ h₁ rfl hSesL₁
          have hKk2' : (Expr.snd (Expr.op (O := OO) CKAOp.ckaReceive
              (.pair (.fst (.snd (.snd .v1))) (.snd (.snd (.snd (.snd .v1))))))).eval ρ₂ =
              (cka.receive γ Tn).2 := by
            simp [ρ₂, ρ₁, hRecv, Expr.eval, Expr.v1]
          rw [hKk2'] at hExt
          rw [hExt.1] at hmem
          simp only [support_pure, Set.mem_singleton_iff, exists_eq_left, StateT.run_pure] at hmem
          subst hmem
          dsimp only
          exact ⟨by rw [hExt.2.2.1]; exact hTbl₁,
            by rw [← hSes₁]; exact hExt.2.2.2.1,
            by rw [hExt.2.2.2.2, hTr₁]⟩
    · simp only [hc1, Bool.false_eq_true, ↓reduceIte]
      refine ⟨?_, ?_⟩
      · simp [ρ₁, StateT.run_pure, Comp.eval, Prod.map, Expr.eval, Expr.v0]
      · intro res hmem
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem
        exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, rfl⟩
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rcases hcache : h.cache t with _ | ⟨Tc, σc, k, ext⟩
  · have hHonNone :
        (Expr.caseOpt (O := OO) (.tget (fsHsCache (.fst .v0)) (.fst (.snd .v0))) .none
          (.ite (Expr.op (O := OO) CKAOp.eqT (.pair (.fst .v0) (.snd (.snd (.snd (.snd .v1))))))
            (.some (.snd .v0))
            .none)).eval ρ₁ = none := by
      simp [ρ₁, hcache, fsHsCache, fsHsEnc, Expr.eval, Expr.v0]
    rw [eval_caseOpt_none hHonNone]
    exact hNoneBranch
  · by_cases hEq : Tc = Tn
    · have hHonSome :
          (Expr.caseOpt (O := OO) (.tget (fsHsCache (.fst .v0)) (.fst (.snd .v0))) .none
            (.ite (Expr.op (O := OO) CKAOp.eqT (.pair (.fst .v0) (.snd (.snd (.snd (.snd .v1))))))
              (.some (.snd .v0))
              .none)).eval ρ₁ = some (σc, k, ext) := by
        simp [ρ₁, hcache, hEq, heqT, fsHsCache, fsHsEnc, Expr.eval, Expr.v0, Expr.v1]
      rw [eval_caseOpt_some hHonSome, eval_ret]
      simp only [hEq, ↓reduceIte, StateT.run_pure]
      refine ⟨?_, ?_⟩
      · cases ext <;>
          simp [ρ₁, hRecv, hFsInitR, Prod.map, Expr.eval, Expr.v0, Expr.v1]
      · intro res hmem
        simp only [support_pure, Set.mem_singleton_iff] at hmem
        subst hmem
        exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, rfl⟩
    · have hHonNone :
          (Expr.caseOpt (O := OO) (.tget (fsHsCache (.fst .v0)) (.fst (.snd .v0))) .none
            (.ite (Expr.op (O := OO) CKAOp.eqT (.pair (.fst .v0) (.snd (.snd (.snd (.snd .v1))))))
              (.some (.snd .v0))
              .none)).eval ρ₁ = none := by
        simp [ρ₁, hcache, hEq, heqT, fsHsCache, fsHsEnc, Expr.eval, Expr.v0, Expr.v1]
      rw [eval_caseOpt_none hHonNone]
      simp only [hEq, ↓reduceIte]
      exact hNoneBranch

@[simp] theorem query_fs_tr_eval {Γ'} (arg : Expr OO Γ' (.prod hdrTy (.base .msg))) (ρ : Env Γ') :
    (@Comp.query _ _ _ OO II Γ' FSHdrTag.tr arg).eval ρ =
      FSAEAD.transmitQuery (SenderState := SS) (ReceiverState := RS)
        (arg.eval ρ).1 (arg.eval ρ).2 := by
  simp [Comp.eval, fsaeadHeaderAdIface, FSAEAD.transmitQuery]

@[simp] theorem query_fs_ch_eval {Γ'}
    (arg : Expr OO Γ' (.prod hdrTy (.prod (.base .msg) (.base .msg)))) (ρ : Env Γ') :
    (@Comp.query _ _ _ OO II Γ' FSHdrTag.ch arg).eval ρ =
      FSAEAD.challengeQuery (SenderState := SS) (ReceiverState := RS)
        (arg.eval ρ).1 (arg.eval ρ).2.1 (arg.eval ρ).2.2 := by
  simp [Comp.eval, fsaeadHeaderAdIface, FSAEAD.challengeQuery]

@[simp] theorem query_fs_cs_eval {Γ'} (arg : Expr OO Γ' .unit) (ρ : Env Γ') :
    (@Comp.query _ _ _ OO II Γ' FSHdrTag.cs arg).eval ρ =
      FSAEAD.corruptSenderQuery (SenderState := SS) (ReceiverState := RS)
        (AssocData := Header T) (Message := M) (Ciphertext := E) := by
  simp [Comp.eval, fsaeadHeaderAdIface, FSAEAD.corruptSenderQuery]

@[simp] theorem query_fs_cr_eval {Γ'} (arg : Expr OO Γ' .unit) (ρ : Env Γ') :
    (@Comp.query _ _ _ OO II Γ' FSHdrTag.cr arg).eval ρ =
      FSAEAD.corruptReceiverQuery (SenderState := SS) (ReceiverState := RS)
        (AssocData := Header T) (Message := M) (Ciphertext := E) := by
  simp [Comp.eval, fsaeadHeaderAdIface, FSAEAD.corruptReceiverQuery]

@[simp] theorem query_fs_dl_eval {Γ'} (arg : Expr OO Γ' hdrCtTy) (ρ : Env Γ') :
    (@Comp.query _ _ _ OO II Γ' FSHdrTag.dl arg).eval ρ =
      Option.map fsHdrRrEnc <$>
        FSAEAD.deliverQuery (SenderState := SS) (ReceiverState := RS)
          (arg.eval ρ).1 (arg.eval ρ).2 := by
  simp [Comp.eval, fsaeadHeaderAdIface, FSAEAD.deliverQuery]

@[simp] theorem query_fs_ij_eval {Γ'} (arg : Expr OO Γ' hdrCtTy) (ρ : Env Γ') :
    (@Comp.query _ _ _ OO II Γ' FSHdrTag.ij arg).eval ρ =
      Option.map fsHdrRrEnc <$>
        FSAEAD.injectQuery (SenderState := SS) (ReceiverState := RS)
          (arg.eval ρ).1 (arg.eval ρ).2 := by
  simp [Comp.eval, fsaeadHeaderAdIface, FSAEAD.injectQuery]

theorem fsFsSendC_eval [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (hFsSend : fsSend = fs.send)
    (Δcka : ℕ) (mo : Mode) (j : ℕ)
    {Γ'} (hE : Expr OO Γ' hsTy) (ctxE : Expr OO Γ' (cGsTy vpTyFS))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (ssvE : Expr OO Γ' (.opt (.base .ss))) (hdrE : Expr OO Γ' hdrTy)
    (mE : Expr OO Γ' (.base .msg))
    (pairE : Expr OO Γ' (.opt (.prod (.base .msg) (.base .msg)))) (ρ : Env Γ')
    (h : FSState T RSt K I SS RS E) (ctx : Ctx Γ T RSt (Option SS) (Option RS) M E) (P : Party)
    (hh : hE.eval ρ = hsEnc h)
    (hctx : ctxE.eval ρ = cGsEnc vpEnc ctx) (hp : pE.eval ρ = partyEnc P) :
    (fsFsSendC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) Δcka hE ctxE pE tE ssvE hdrE mE pairE).eval ρ =
      Prod.map id hsEnc <$>
        ((hooksFS cka prng fs Δcka mo j).fsSend ctx P (tE.eval ρ)
          (ssvE.eval ρ) (hdrE.eval ρ) (mE.eval ρ) (pairE.eval ρ)).run h := by
  unfold fsFsSendC hooksFS
  dsimp only
  rw [eval_bind_ret]
  set ssv : Option SS := ssvE.eval ρ
  set hdr : Header T := hdrE.eval ρ
  set m : M := mE.eval ρ
  set pair : Option (M × M) := pairE.eval ρ
  have h0 : (Expr.pair hE (.pair ctxE (.pair pE (.pair ssvE (.pair hdrE (.pair mE pairE)))))).eval
      ρ = (hsEnc h, cGsEnc vpEnc ctx, partyEnc P, ssv, hdr, m, pair) := by
    simp [Expr.eval, hh, hctx, hp, ssv, hdr, m, pair]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := .prod hsTy (.prod (cGsTy vpTyFS) (.prod .bool (.prod (.opt (.base CKASort.ss))
      (.prod hdrTy (.prod (.base CKASort.msg)
        (.opt (.prod (.base CKASort.msg) (.base CKASort.msg)))))))))
    (hsEnc h, cGsEnc vpEnc ctx, partyEnc P, ssv, hdr, m, pair) ρ
  rcases ssv with _ | ss
  · rw [eval_caseOpt_none rfl]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    have hExt0 : (fsHsExt (.fst (Expr.v0 (O := OO)))).eval ρ₁ = h.ext := rfl
    rcases hext : h.ext with _ | ⟨ss, rs⟩
    · rw [eval_caseOpt_none (hExt0.trans hext)]
      dsimp only
      rw [eval_bind, eval_ite]
      have hSafe : (cSafeChE (2 + Δcka) (.fst (.snd (Expr.v0 (O := OO))))
          (.fst (.snd (.snd .v0)))).eval ρ₁ = ctx.safeCh (2 + Δcka) P :=
        cSafeChE_eval vpEnc (O' := OO) (2 + Δcka)
          (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) ρ₁ ctx P rfl rfl
      have hCond : (Expr.and (.not (cSafeChE (2 + Δcka) (.fst (.snd (Expr.v0 (O := OO))))
          (.fst (.snd (.snd .v0))))) (.not (fsHsSCorr (.fst .v0)))).eval ρ₁ =
          (!(ctx.safeCh (2 + Δcka) P) && !h.fsSCorr) := by
        rw [and_eval, not_eval, hSafe]
        rfl
      rw [hCond]
      have hSendTrue : ∀ (h₁ : FSState T RSt K I SS RS E),
          (Comp.ite (O := OO) (I := II) (.not (.fst .v0))
            (.ret (.pair .none (.snd .v0)))
            (.bind
              (.caseOpt (.snd (.snd (.snd (.snd (.snd (.snd .v1))))))
                (@Comp.query _ _ _ OO II _ FSHdrTag.tr
                  (.pair (.fst (.snd (.snd (.snd (.snd .v1)))))
                         (.fst (.snd (.snd (.snd (.snd (.snd .v1))))))))
                (@Comp.query _ _ _ OO II _ FSHdrTag.ch
                  (.pair (.fst (.snd (.snd (.snd (.snd .v2))))) .v0)))
              (.caseOpt .v0
                (.ret (.pair .none (.snd .v1)))
                (.ret (.pair (.some (.pair (.none (t := .base CKASort.ss)) .v0))
                  (fsHsSetCountTrans (.snd .v2)
                    (.add (fsHsCount (.snd .v2)) (.nat 1))
                    (.cons (.pair (.add (fsHsCount (.snd .v2)) (.nat 1))
                      (.pair (.fst (.snd (.snd (.snd (.snd .v3))))) .v0))
                      (fsHsTrans (.snd .v2))))))))).eval
            (Env.cons (t := .prod .bool hsTy) (true, hsEnc h₁) ρ₁) =
          Prod.map id hsEnc <$>
            ((do
                let e? ← match pair with
                  | some (m₀, m₁) =>
                    liftF (FSAEAD.challengeQuery (SenderState := SS) (ReceiverState := RS)
                      hdr m₀ m₁)
                  | none =>
                    liftF (FSAEAD.transmitQuery (SenderState := SS) (ReceiverState := RS) hdr m)
                match e? with
                | none => return none
                | some e =>
                  modify fun (s : FSState T RSt K I SS RS E) => { s with
                    fsCount := s.fsCount + 1
                    fsTrans := (s.fsCount + 1, (hdr, e)) :: s.fsTrans }
                  return some (none, e) :
              HM (FSAEAD.spec SS RS (Header T) M E) (FSState T RSt K I SS RS E)
                (Option (Option SS × E))).run h₁) := by
        intro h₁
        set ρ₂ := Env.cons (t := .prod .bool hsTy) (true, hsEnc h₁) ρ₁
        rw [eval_ite]
        have hNotOk : (Expr.not (.fst (Expr.v0 (O := OO)))).eval ρ₂ = false := rfl
        rw [hNotOk]
        simp only [Bool.false_eq_true, ↓reduceIte, eval_bind]
        rcases pair with _ | ⟨m₀, m₁⟩
        · rw [eval_caseOpt_none rfl, query_fs_tr_eval]
          simp only [ρ₂, ρ₁, liftF, StateT.run_bind, StateT.run_lift,
            bind_assoc, pure_bind, map_bind, Expr.eval, Expr.v1]
          refine bind_congr fun e? => ?_
          rcases e? with _ | e
          · rw [eval_caseOpt_none rfl, eval_ret]
            simp [StateT.run_pure, Prod.map, Expr.eval]
          · rw [eval_caseOpt_some rfl, eval_ret, pair_eval]
            simp [StateT.run_modify, fsHsSetCountTrans, fsHsMk, fsHsCache, fsHsTable,
              fsHsSessions, fsHsTrans, fsHsCount, fsHsSCorr, fsHsExt, fsHsEnc,
              Prod.map, Expr.eval, Expr.v0, Expr.v2, Expr.v3]
        · rw [eval_caseOpt_some rfl, query_fs_ch_eval]
          simp only [ρ₂, ρ₁, liftF, StateT.run_bind, StateT.run_lift,
            bind_assoc, pure_bind, map_bind, Expr.eval, Expr.v0, Expr.v2]
          refine bind_congr fun e? => ?_
          rcases e? with _ | e
          · rw [eval_caseOpt_none rfl, eval_ret]
            simp [StateT.run_pure, Prod.map, Expr.eval, Expr.v1]
          · rw [eval_caseOpt_some rfl, eval_ret, pair_eval]
            simp [StateT.run_modify, fsHsSetCountTrans, fsHsMk, fsHsCache, fsHsTable,
              fsHsSessions, fsHsTrans, fsHsCount, fsHsSCorr, fsHsExt, fsHsEnc,
              Prod.map, Expr.eval, Expr.v3]
      by_cases hc : (!(ctx.safeCh (2 + Δcka) P) && !h.fsSCorr) = true
      · simp only [hc, ↓reduceIte, eval_bind, query_fs_cs_eval, liftF,
          StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind]
        refine bind_congr fun cs? => ?_
        rcases cs? with _ | ss'
        · rw [eval_caseOpt_none rfl, eval_ret, pure_bind]
          simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v1]
        · rw [eval_caseOpt_some rfl, eval_ret, pure_bind]
          simp only [StateT.run_bind, StateT.run_modify, pure_bind, Bool.not_true,
            Bool.false_eq_true, ↓reduceIte]
          have hEncSCorr : (Expr.pair (O := OO) (.bool true)
              (fsHsSetSCorr (.fst .v2) (.bool true))).eval
              (Env.cons (t := .base CKASort.ss) ss'
                (Env.cons (t := .opt (.base CKASort.ss)) (some ss') ρ₁)) =
              (true, hsEnc { h with fsSCorr := true }) := by
            simp [ρ₁, fsHsSetSCorr, fsHsMk, fsHsCache, fsHsTable, fsHsSessions,
              fsHsTrans, fsHsCount, fsHsExt, fsHsEnc, Expr.eval, Expr.v2]
          rw [hEncSCorr]
          exact hSendTrue { h with fsSCorr := true }
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, eval_ret, pure_bind]
        have hEncH : (Expr.pair (O := OO) (.bool true) (.fst .v0)).eval ρ₁ = (true, hsEnc h) := rfl
        rw [hEncH]
        exact hSendTrue h
    · rw [eval_caseOpt_some (hExt0.trans hext), eval_ret]
      simp [ρ₁, hext, StateT.run_set, hFsSend, fsHsSetExt, fsHsMk, fsHsCache, fsHsTable,
        fsHsSessions, fsHsTrans, fsHsCount, fsHsSCorr, fsHsEnc, Prod.map,
        Expr.eval, Expr.v0, Expr.v1]
  · rw [eval_caseOpt_some rfl, eval_ret]
    simp [ρ₁, StateT.run_pure, hFsSend, Prod.map, Expr.eval, Expr.v0, Expr.v1]

theorem fsTransFindE_eval [DecidableEq T] [DecidableEq E]
    (heqT : eqT = (· == ·)) (heqE : eqE = (· == ·))
    (L : ℕ) {Γ'} (trE : Expr OO Γ' (.list transEntryTy)) (hcE : Expr OO Γ' hdrCtTy)
    (ρ : Env Γ') (hL : (trE.eval ρ).length ≤ L) :
    (fsTransFindE L trE hcE).eval ρ =
      (trE.eval ρ).find? (fun x => x.2 == hcE.eval ρ) := by
  have htake : (trE.eval ρ).take L = trE.eval ρ := List.take_of_length_le hL
  simp only [fsTransFindE, Expr.eval, Expr.v0, Env.get_cons_zero, htake]
  congr 1; funext x
  rw [hdrCtEqE_eval _ _ _ heqT heqE]
  rfl

theorem foldr_filter_fst_bne {β : Type} (drop : ℕ) (l : List (ℕ × β)) :
    l.foldr (fun x acc => if (!decide (x.1 = drop)) = true then x :: acc else acc) [] =
      l.filter (·.1 != drop) := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldr_cons, List.filter_cons, ih]
    by_cases h : hd.1 = drop <;> simp [bne, h]

theorem fsTransFilterE_eval (L : ℕ) {Γ'}
    (trE : Expr OO Γ' (.list transEntryTy)) (dropE : Expr OO Γ' .nat)
    (ρ : Env Γ') (hL : (trE.eval ρ).length ≤ L) :
    (fsTransFilterE L trE dropE).eval ρ =
      (trE.eval ρ).filter (·.1 != dropE.eval ρ) := by
  have htake : (trE.eval ρ).take L = trE.eval ρ := List.take_of_length_le hL
  simp only [fsTransFilterE, Expr.eval, Expr.v0, Expr.v1, Expr.v2,
    Env.get_cons_zero, Env.get_cons_succ, htake]
  exact foldr_filter_fst_bne (dropE.eval ρ) (trE.eval ρ)

theorem fsFsRecvC_eval [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (heqT : eqT = (· == ·))
    (heqE : eqE = (· == ·))
    (L B Δcka : ℕ) (mo : Mode) (j : ℕ)
    (hFsRecvB : ∀ rs hdr e,
      (fsReceive rs hdr e).map (fun (rs', i, m) => (rs', min i B, m)) =
        fs.receive rs hdr e)
    {Γ'} (hE : Expr OO Γ' hsTy) (ctxE : Expr OO Γ' (cGsTy vpTyFS))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (rsvE : Expr OO Γ' (.opt (.base .rs))) (hdrE : Expr OO Γ' hdrTy)
    (eE : Expr OO Γ' (.base .ct)) (recE : Expr OO Γ' (.opt cRecTy)) (ρ : Env Γ')
    (h : FSState T RSt K I SS RS E) (ctx : Ctx Γ T RSt (Option SS) (Option RS) M E)
    (P : Party) (rec_ : Option (Record M (Header T × E)))
    (hHB : FSHBoundedPost L h) (hh : hE.eval ρ = hsEnc h)
    (hrec : recE.eval ρ = rec_.map cRecEnc) :
    (fsFsRecvC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B hE ctxE pE tE rsvE hdrE eE recE).eval ρ =
      Prod.map id hsEnc <$>
        ((hooksFS cka prng fs Δcka mo j).fsRecv ctx P (tE.eval ρ)
          (rsvE.eval ρ) (hdrE.eval ρ) (eE.eval ρ) rec_).run h ∧
    ∀ res ∈ support (((hooksFS cka prng fs Δcka mo j).fsRecv ctx P (tE.eval ρ)
        (rsvE.eval ρ) (hdrE.eval ρ) (eE.eval ρ) rec_).run h),
      FSHBoundedPost L res.2 := by
  unfold fsFsRecvC hooksFS
  dsimp only
  rw [eval_bind_ret]
  set rsv : Option RS := rsvE.eval ρ
  set hdr : Header T := hdrE.eval ρ
  set e : E := eE.eval ρ
  have h0 : (Expr.pair hE (.pair rsvE (.pair hdrE (.pair eE recE)))).eval ρ =
      (hsEnc h, rsv, hdr, e, rec_.map cRecEnc) := by
    simp [Expr.eval, hh, hrec, rsv, hdr, e]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := .prod hsTy (.prod (.opt (.base CKASort.rs))
      (.prod hdrTy (.prod (.base CKASort.ct) (.opt cRecTy)))))
    (hsEnc h, rsv, hdr, e, rec_.map cRecEnc) ρ
  rcases rsv with _ | rs
  · rw [eval_caseOpt_none rfl]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    have hExt0 : (fsHsExt (.fst (Expr.v0 (O := OO)))).eval ρ₁ = h.ext := rfl
    rcases hext : h.ext with _ | ⟨ss, rs⟩
    · rw [eval_caseOpt_none (hExt0.trans hext)]
      dsimp only
      set matched := h.fsTrans.find? (fun x => x.2 == (hdr, e))
      have hFind1 : (fsTransFindE L (fsHsTrans (.fst (Expr.v0 (O := OO))))
          (.pair (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0)))))).eval ρ₁ =
          matched :=
        fsTransFindE_eval heqT heqE L (fsHsTrans (.fst .v0))
          (.pair (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0))))) ρ₁ hHB
      have hContEval : ∀ (m? : Option (ℕ × Header T × E))
          (_hM : matched = m?)
          (res : Option (FSAEAD.ReceiveResult M)),
          (Comp.caseOpt (O := OO) (I := II) .v0
            (.ret (.pair .none (.fst .v1)))
            (.caseSum .v0
              (.ret (.pair (.some .none) (.fst .v3)))
              (.ret (.pair
                (.caseOpt (.snd .v0)
                  (.caseOpt (.snd (.snd (.snd (.snd .v3))))
                    .none
                    (.some (.some (.pair (Expr.none (O := OO) (t := .base .rs))
                      (.pair (.fst .v1) (cRecMsg .v0))))))
                  (.some (.some (.pair (Expr.none (O := OO) (t := .base .rs))
                    (.pair (.fst .v1) .v0)))))
                (fsHsSetTrans (.fst .v3)
                  (fsTransFilterE L (fsHsTrans (.fst .v3))
                    (.caseOpt
                      (fsTransFindE L (fsHsTrans (.fst .v3))
                        (.pair (.fst (.snd (.snd .v3))) (.fst (.snd (.snd (.snd .v3))))))
                      (.fst .v0) (.fst .v0)))))))).eval
            (Env.cons (t := .opt (fsHdrRrTy KC Γ CCoins T I KR RSt K SS RS M E))
              (Option.map fsHdrRrEnc res) ρ₁) =
          Prod.map id hsEnc <$>
            ((match res with
              | none => pure none
              | some .rejected => pure (some none)
              | some (.accepted i mo') => do
                modify fun (s : FSState T RSt K I SS RS E) =>
                  { s with fsTrans := s.fsTrans.filter (·.1 != (m?.map (·.1)).getD i) }
                match mo', rec_ with
                | some m, _ => pure (some (some ((none : Option RS), i, m)))
                | none, some r => pure (some (some ((none : Option RS), i, r.msg)))
                | none, none => pure none :
              HM (FSAEAD.spec SS RS (Header T) M E) (FSState T RSt K I SS RS E)
                (Option (Option (Option RS × ℕ × M)))).run h) := by
        intro m? hM res
        rcases res with _ | (_ | ⟨i, mo'⟩)
        · dsimp only [Option.map]
          rw [eval_caseOpt_none rfl, eval_ret]
          simp [ρ₁, StateT.run_pure, Prod.map, Expr.eval, Expr.v1]
        · dsimp only [Option.map, fsHdrRrEnc]
          rw [eval_caseOpt_some rfl, eval_caseSum_inl rfl, eval_ret]
          simp [ρ₁, StateT.run_pure, Prod.map, Expr.eval, Expr.v3]
        · dsimp only [Option.map, fsHdrRrEnc]
          rw [eval_caseOpt_some rfl, eval_caseSum_inr rfl, eval_ret, pair_eval]
          simp only [StateT.run_bind, StateT.run_modify, pure_bind]
          set ρ₂ := Env.cons (t := .prod .nat (.opt (.base CKASort.msg))) (i, mo')
            (Env.cons (t := fsHdrRrTy KC Γ CCoins T I KR RSt K SS RS M E) (.inr (i, mo'))
              (Env.cons (t := .opt (fsHdrRrTy KC Γ CCoins T I KR RSt K SS RS M E))
                (some (.inr (i, mo'))) ρ₁))
          have hFind3 : (fsTransFindE L (fsHsTrans (.fst (Expr.v3 (O := OO))))
              (.pair (.fst (.snd (.snd .v3))) (.fst (.snd (.snd (.snd .v3)))))).eval ρ₂ =
              m? :=
            Eq.trans (fsTransFindE_eval heqT heqE L (fsHsTrans (.fst (Expr.v3 (O := OO))))
              (.pair (.fst (.snd (.snd .v3))) (.fst (.snd (.snd (.snd .v3))))) ρ₂ hHB) hM
          have hDrop : (Expr.caseOpt (O := OO)
              (fsTransFindE L (fsHsTrans (.fst .v3))
                (.pair (.fst (.snd (.snd .v3))) (.fst (.snd (.snd (.snd .v3))))))
              (.fst .v0) (.fst .v0)).eval ρ₂ =
              (m?.map (·.1)).getD i := by
            simp only [Expr.eval, hFind3]
            rcases m? with _ | mrec <;> rfl
          have hFlt := fsTransFilterE_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
            (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
            (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
            (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
            (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
            L (fsHsTrans (.fst .v3))
            (.caseOpt (fsTransFindE L (fsHsTrans (.fst .v3))
                (.pair (.fst (.snd (.snd .v3))) (.fst (.snd (.snd (.snd .v3))))))
              (.fst .v0) (.fst .v0)) ρ₂ hHB
          rw [hDrop] at hFlt
          have hH4 : (fsHsSetTrans (.fst (Expr.v3 (O := OO)))
              (fsTransFilterE L (fsHsTrans (.fst .v3))
                (.caseOpt (fsTransFindE L (fsHsTrans (.fst .v3))
                    (.pair (.fst (.snd (.snd .v3))) (.fst (.snd (.snd (.snd .v3))))))
                  (.fst .v0) (.fst .v0)))).eval ρ₂ =
              hsEnc { h with fsTrans := h.fsTrans.filter (·.1 != (m?.map (·.1)).getD i) } := by
            unfold fsHsSetTrans fsHsMk
            simp only [pair_eval, hFlt]
            rfl
          have hOut :
              (Expr.caseOpt (O := OO) (.snd .v0)
                (Expr.caseOpt (.snd (.snd (.snd (.snd .v3))))
                  .none
                  (.some (.some (.pair (Expr.none (O := OO) (t := .base .rs))
                    (.pair (.fst .v1) (cRecMsg .v0))))))
                (.some (.some (.pair (Expr.none (O := OO) (t := .base .rs))
                  (.pair (.fst .v1) .v0))))).eval ρ₂ =
              (match mo', rec_ with
                | some m, _ => some (some ((none : Option RS), i, m))
                | none, some r => some (some ((none : Option RS), i, r.msg))
                | none, none => none) := by
            rcases mo' with _ | m
            · rcases rec_ with _ | r <;>
                simp [ρ₂, ρ₁, cRecMsg, cRecEnc, Expr.eval, Expr.v0, Expr.v1, Expr.v3]
            · simp [ρ₂, Expr.eval, Expr.v0, Expr.v1]
          rw [hOut, hH4]
          rcases mo' with _ | m
          · rcases rec_ with _ | r <;> rfl
          · rfl
      have hContHB : ∀ (m? : Option (ℕ × Header T × E))
          (res : Option (FSAEAD.ReceiveResult M)) (res' : _),
          res' ∈ support
            ((match res with
              | none => pure none
              | some .rejected => pure (some none)
              | some (.accepted i mo') => do
                modify fun (s : FSState T RSt K I SS RS E) =>
                  { s with fsTrans := s.fsTrans.filter (·.1 != (m?.map (·.1)).getD i) }
                match mo', rec_ with
                | some m, _ => pure (some (some ((none : Option RS), i, m)))
                | none, some r => pure (some (some ((none : Option RS), i, r.msg)))
                | none, none => pure none :
              HM (FSAEAD.spec SS RS (Header T) M E) (FSState T RSt K I SS RS E)
                (Option (Option (Option RS × ℕ × M)))).run h) →
          FSHBoundedPost L res'.2 := by
        intro m? res res' hmem
        rcases res with _ | (_ | ⟨i, mo'⟩)
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
          subst hmem; exact hHB
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
          subst hmem; exact hHB
        · simp only [StateT.run_bind, StateT.run_modify, pure_bind] at hmem
          have hHB' : FSHBoundedPost L
              { h with fsTrans := h.fsTrans.filter (·.1 != (m?.map (·.1)).getD i) } :=
            (List.length_filter_le _ _).trans hHB
          rcases mo' with _ | m
          · rcases rec_ with _ | r <;>
              (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem;
               subst hmem; exact hHB')
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
            subst hmem; exact hHB'
      rcases hM : matched with _ | mrec
      · refine ⟨?_, ?_⟩
        · rw [eval_bind, eval_caseOpt_none (hFind1.trans hM), query_fs_ij_eval]
          simp only [ρ₁, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
            liftF, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
            bind_map_left, map_bind, Expr.eval, Expr.v0]
          exact bind_congr fun res => hContEval none hM res
        · intro res' hmem
          simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
            liftF, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
            mem_support_bind_iff] at hmem
          obtain ⟨res, _, hmem⟩ := hmem
          exact hContHB none res res' hmem
      · refine ⟨?_, ?_⟩
        · rw [eval_bind, eval_caseOpt_some (hFind1.trans hM), query_fs_dl_eval]
          simp only [ρ₁, Option.isSome_some, ↓reduceIte,
            liftF, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
            bind_map_left, map_bind, Expr.eval, Expr.v1]
          exact bind_congr fun res => hContEval (some mrec) hM res
        · intro res' hmem
          simp only [Option.isSome_some, ↓reduceIte,
            liftF, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
            mem_support_bind_iff] at hmem
          obtain ⟨res, _, hmem⟩ := hmem
          exact hContHB (some mrec) res res' hmem
    · rw [eval_caseOpt_some (hExt0.trans hext)]
      dsimp only
      refine ⟨?_, ?_⟩
      · have hOp : (Expr.op (O := OO) (CKAOp.fsReceive B)
            (.pair (.snd .v0)
              (.pair (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1))))))).eval
            (Env.cons (t := .prod (.base CKASort.ss) (.base CKASort.rs)) (ss, rs) ρ₁) =
            fs.receive rs hdr e := by
          simp only [ρ₁, prngOps, ckaOps, Expr.eval, Expr.v0, Expr.v1,
            Env.get_cons_zero, Env.get_cons_succ]
          exact hFsRecvB rs hdr e
        rcases hrc : fs.receive rs hdr e with _ | ⟨rs', i, m⟩
        · rw [eval_caseOpt_none (hOp.trans hrc), eval_ret]
          simp [ρ₁, StateT.run_pure, Prod.map, Expr.eval, Expr.v1]
        · rw [eval_caseOpt_some (hOp.trans hrc), eval_ret]
          simp [ρ₁, StateT.run_set, fsHsSetExt, fsHsMk, fsHsCache, fsHsTable,
            fsHsSessions, fsHsTrans, fsHsCount, fsHsSCorr, fsHsEnc, Prod.map,
            Expr.eval, Expr.v0, Expr.v1, Expr.v2]
      · intro res' hmem
        rcases hrc : fs.receive rs hdr e with _ | ⟨rs', i, m⟩
        · simp only [hrc, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
          subst hmem; exact hHB
        · simp only [hrc, StateT.run_bind, StateT.run_set, StateT.run_pure,
            pure_bind, support_pure, Set.mem_singleton_iff] at hmem
          subst hmem; exact hHB
  · rw [eval_caseOpt_some rfl]
    dsimp only
    refine ⟨?_, ?_⟩
    · have hOp : (Expr.op (O := OO) (CKAOp.fsReceive B)
          (.pair .v0
            (.pair (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1))))))).eval
          (Env.cons (t := .base CKASort.rs) rs ρ₁) =
          fs.receive rs hdr e := by
        simp only [ρ₁, prngOps, ckaOps, Expr.eval, Expr.v0, Expr.v1,
          Env.get_cons_zero, Env.get_cons_succ]
        exact hFsRecvB rs hdr e
      rcases hrc : fs.receive rs hdr e with _ | ⟨rs', i, m⟩
      · rw [eval_caseOpt_none (hOp.trans hrc), eval_ret]
        simp [ρ₁, StateT.run_pure, Prod.map, Expr.eval, Expr.v1]
      · rw [eval_caseOpt_some (hOp.trans hrc), eval_ret]
        simp [ρ₁, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v2]
    · intro res' hmem
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact hHB

def unliftEntry (entry : Option (Option RS)) (rsExt : Option RS) : Option RS :=
  match entry with
  | some (some rs) => some rs
  | some none => rsExt
  | none => none

theorem unliftEntryE_eval {Γ'}
    (entryE : Expr OO Γ' (.opt (.opt (.base .rs))))
    (rsExtE : Expr OO Γ' (.opt (.base .rs))) (ρ : Env Γ') :
    (unliftEntryE entryE rsExtE).eval ρ = unliftEntry (entryE.eval ρ) (rsExtE.eval ρ) := by
  unfold unliftEntryE unliftEntry
  rw [letE_eval]
  rcases h1 : entryE.eval ρ with _ | (_ | rs) <;>
    simp [h1, Expr.eval, Expr.v0, Expr.v1]

private theorem iterM_rangeListStep {ι : Type} {spec : OracleSpec ι} :
    ∀ (n k : ℕ) (acc : List ℕ),
      (iterM (fun p : ℕ × List ℕ => (pure (p.1 + 1, p.1 :: p.2) : OracleComp spec _))
        n (k, acc)) =
      pure (k + n, (List.range' k n).reverse ++ acc)
  | 0, k, acc => by simp [iterM]
  | n + 1, k, acc => by
    simp only [iterM, pure_bind]
    rw [iterM_rangeListStep n (k + 1) (k :: acc)]
    congr 1
    exact Prod.ext (by omega) (by simp [List.range'_succ, List.append_assoc])

theorem rangeListC_eval {S' : Sig} {O' : Ops S'} {ι : Type} {spec : OracleSpec ι}
    {I' : Iface S' spec} (L : ℕ) {Γ' : List (Ty S')} (ρ : Env Γ') :
    (rangeListC (O' := O') (I' := I') L (Γ' := Γ')).eval ρ =
      pure (List.range L).reverse := by
  unfold rangeListC
  change (iterM (fun p : ℕ × List ℕ => pure (p.1 + 1, p.1 :: p.2)) L (0, []) >>=
      fun p => pure p.2) = pure (List.range L).reverse
  rw [iterM_rangeListStep L 0 []]
  simp [List.range_eq_range']

@[simp] theorem rangeListC_queries {S' : Sig} {O' : Ops S'} {ι : Type} {spec : OracleSpec ι}
    {I' : Iface S' spec} (L : ℕ) {Γ' : List (Ty S')}
    (w : I'.Tag → ℕ) (ws : I'.smp.Samp → ℕ) :
    (rangeListC (O' := O') (I' := I') L (Γ' := Γ')).queries w ws = 0 := by
  simp [rangeListC, Comp.queries]

theorem foldr_update_apply {α : Type} (f : ℕ → α) (init : ℕ → α) (l : List ℕ) (t : ℕ) :
    (l.foldr (fun k acc => Function.update acc k (f k)) init) t =
      if t ∈ l then f t else init t := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldr_cons, List.mem_cons]
    by_cases h : t = hd
    · subst h; simp [Function.update]
    · simp [Function.update, h, ih]

theorem unliftVRE_eval (L : ℕ) {Γ'}
    (vRE : Expr OO Γ' (.tbl (.opt (.opt (.base .rs)))))
    (rsExtE : Expr OO Γ' (.opt (.base .rs)))
    (rngE : Expr OO Γ' (.list .nat)) (ρ : Env Γ')
    (hRng : rngE.eval ρ = (List.range L).reverse) :
    (unliftVRE L vRE rsExtE rngE).eval ρ =
      fun t => if t < L then unliftEntry ((vRE.eval ρ) t) (rsExtE.eval ρ) else none := by
  unfold unliftVRE
  rw [letE_eval]
  set vR := vRE.eval ρ
  set rsExt := rsExtE.eval ρ
  have h0 : (Expr.pair (.pair vRE rsExtE) rngE).eval ρ =
      ((vR, rsExt), (List.range L).reverse) := by
    simp [Expr.eval, vR, rsExt, hRng]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := .prod (.prod (.tbl (.opt (.opt (.base CKASort.rs)))) (.opt (.base CKASort.rs)))
      (.list .nat))
    ((vR, rsExt), (List.range L).reverse) ρ
  have hTake : (((Expr.snd (O := OO) .v0).eval ρ₁).take L) = (List.range L).reverse := by
    change ((List.range L).reverse).take L = (List.range L).reverse
    simp
  change List.foldr _ (fun _ => none) (((Expr.snd (O := OO) .v0).eval ρ₁).take L) = _
  rw [hTake]
  have hStep :
      (fun (x : ℕ) (acc : ℕ → Option RS) =>
        (Expr.tset (O := OO) .v1 .v0
          (unliftEntryE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
            (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
            (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
            (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
            (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
            (.tget (.fst (.fst .v2)) .v0) (.snd (.fst .v2)))).eval
          (Env.cons (t := .nat) x
            (Env.cons (t := .tbl (.opt (.base CKASort.rs))) acc ρ₁))) =
      (fun (x : ℕ) (acc : ℕ → Option RS) =>
        Function.update acc x (unliftEntry (vR x) rsExt)) := by
    funext x acc
    rw [tset_eval_eq_update, unliftEntryE_eval]
    rfl
  rw [hStep]
  funext t
  rw [foldr_update_apply]
  simp [List.mem_reverse, List.mem_range]

def hooksFSL [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L Δcka : ℕ) (mo : Mode) (j : ℕ) :
    Hooks (FSAEAD.spec SS RS (Header T) M E) (FSState T RSt K I SS RS E)
      Γ T RSt SS RS M E CCoins Γ RSt (Option SS) (Option RS) :=
  { hooksFS cka prng fs Δcka mo j with
    reveal := fun _ _ vp => do
      let vS? : Option (Option SS) ← match vp.vS with
        | none => pure (some none)
        | some (some ss) => pure (some (some ss))
        | some none => do
          match (← get).ext with
          | some (ss, _) => pure (some (some ss))
          | none =>
            match ← liftF (FSAEAD.corruptSenderQuery (ReceiverState := RS)
                (AssocData := Header T) (Message := M) (Ciphertext := E)) with
            | none => pure none
            | some ss =>
              modify fun s => { s with fsSCorr := true }
              pure (some (some ss))
      match vS? with
      | none => return none
      | some vS =>
        let rsExt? : Option (Option RS) ← match vp.vR mo.tStar with
          | some none => do
            match (← get).ext with
            | some (_, rs) => pure (some (some rs))
            | none =>
              if mo.auth then pure none
              else
                match ← liftF (FSAEAD.corruptReceiverQuery (SenderState := SS) (ReceiverState := RS)
                    (AssocData := Header T) (Message := M) (Ciphertext := E)) with
                | none => pure none
                | some (ss, rs) =>
                  modify fun s => { s with ext := some (ss, rs) }
                  pure (some (some rs))
          | _ => pure (some none)
        match rsExt? with
        | none => return none
        | some rsExt =>
          let vR : ℕ → Option RS := fun t =>
            if t < L then unliftEntry (vp.vR t) rsExt else none
          return some (realParty vp vp.γ vp.root vS vR) }

theorem fsRevealC_eval [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L Δcka : ℕ) (mo : Mode) (j : ℕ)
    {Γ'} (hE : Expr OO Γ' hsTy) (ctxE : Expr OO Γ' (cGsTy vpTyFS))
    (pE : Expr OO Γ' .bool) (vpE : Expr OO Γ' vpTyFS) (ρ : Env Γ')
    (h : FSState T RSt K I SS RS E) (ctx : Ctx Γ T RSt (Option SS) (Option RS) M E)
    (P : Party) (vp : VP Γ T RSt (Option SS) (Option RS))
    (hh : hE.eval ρ = hsEnc h) (hvp : vpE.eval ρ = vpEnc vp) :
    (fsRevealC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L mo hE ctxE pE vpE).eval ρ =
      Prod.map (Option.map ckaPsEnc) hsEnc <$>
        ((hooksFSL cka prng fs L Δcka mo j).reveal ctx P vp).run h := by
  unfold fsRevealC hooksFSL
  dsimp only
  rw [eval_bind_ret]
  have h0 : (Expr.pair hE vpE).eval ρ = (hsEnc h, vpEnc vp) := by
    simp [Expr.eval, hh, hvp]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod hsTy vpTyFS) (hsEnc h, vpEnc vp) ρ
  have hStep2 : ∀ (vS : Option SS) (h₁ : FSState T RSt K I SS RS E),
      (Comp.caseOpt (O := OO) (I := II) (.fst .v0)
        (.ret (.pair .none (.snd .v0)))
        (.bind
          (.caseOpt (.tget (vpVR (.snd .v2)) (.nat mo.tStar))
            (.ret (.pair (.some .none) (.snd .v1)))
            (.caseOpt .v0
              (.caseOpt (fsHsExt (.snd .v2))
                (.ite (.bool mo.auth)
                  (.ret (.pair .none (.snd .v2)))
                  (.bind (@Comp.query _ _ _ OO II _ FSHdrTag.cr .unit)
                    (.caseOpt .v0
                      (.ret (.pair .none (.snd .v3)))
                      (.ret (.pair (.some (.some (.snd .v0)))
                        (fsHsSetExt (.snd .v4) (.some .v0)))))))
                (.ret (.pair (.some (.some (.snd .v0))) (.snd .v3))))
              (.ret (.pair (.some .none) (.snd .v3)))))
          (.caseOpt (.fst .v0)
            (.ret (.pair .none (.snd .v0)))
            (.bind (rangeListC (O' := OO) (I' := II) L)
              (.ret (.pair
                (.some (realPartyE (.snd .v5) (vpΓ (.snd .v5)) (vpRoot (.snd .v5)) .v3
                  (unliftVRE L (vpVR (.snd .v5)) .v1 .v0)))
                (.snd .v2))))))).eval
        (Env.cons (t := .prod (.opt (.opt (.base CKASort.ss))) hsTy) (some vS, hsEnc h₁) ρ₁) =
      Prod.map (Option.map ckaPsEnc) hsEnc <$>
        ((do
            let rsExt? : Option (Option RS) ← match vp.vR mo.tStar with
              | some none => do
                match (← get).ext with
                | some (_, rs) => pure (some (some rs))
                | none =>
                  if mo.auth then pure none
                  else
                    match ← liftF (FSAEAD.corruptReceiverQuery (SenderState := SS)
                        (ReceiverState := RS) (AssocData := Header T) (Message := M)
                        (Ciphertext := E)) with
                    | none => pure none
                    | some (ss, rs) =>
                      modify fun (s : FSState T RSt K I SS RS E) =>
                        { s with ext := some (ss, rs) }
                      pure (some (some rs))
              | _ => pure (some none)
            match rsExt? with
            | none => return none
            | some rsExt =>
              let vR : ℕ → Option RS := fun t =>
                if t < L then unliftEntry (vp.vR t) rsExt else none
              return some (realParty vp vp.γ vp.root vS vR) :
          HM (FSAEAD.spec SS RS (Header T) M E) (FSState T RSt K I SS RS E) _).run h₁) := by
    intro vS h₁
    rw [eval_caseOpt_some rfl, eval_bind]
    set ρ₂ := Env.cons (t := .opt (.base CKASort.ss)) vS
      (Env.cons (t := .prod (.opt (.opt (.base CKASort.ss))) hsTy) (some vS, hsEnc h₁) ρ₁)
    have hFinal : ∀ (rsExt : Option RS) (h₂ : FSState T RSt K I SS RS E),
        (Comp.caseOpt (O := OO) (I := II) (.fst .v0)
          (.ret (.pair .none (.snd .v0)))
          (.bind (rangeListC (O' := OO) (I' := II) L)
            (.ret (.pair
              (.some (realPartyE (.snd .v5) (vpΓ (.snd .v5)) (vpRoot (.snd .v5)) .v3
                (unliftVRE L (vpVR (.snd .v5)) .v1 .v0)))
              (.snd .v2))))).eval
          (Env.cons (t := .prod (.opt (.opt (.base CKASort.rs))) hsTy) (some rsExt, hsEnc h₂) ρ₂) =
        pure (some (ckaPsEnc (realParty vp vp.γ vp.root vS
          (fun t => if t < L then unliftEntry (vp.vR t) rsExt else none))), hsEnc h₂) := by
      intro rsExt h₂
      rw [eval_caseOpt_some rfl, eval_bind, rangeListC_eval, pure_bind, eval_ret, pair_eval,
        some_eval]
      set ρ₃ := Env.cons (t := .list .nat) (List.range L).reverse
        (Env.cons (t := .opt (.base CKASort.rs)) rsExt
          (Env.cons (t := .prod (.opt (.opt (.base CKASort.rs))) hsTy) (some rsExt, hsEnc h₂) ρ₂))
      have hUnlift := unliftVRE_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        L (vpVR (.snd .v5)) .v1 .v0 ρ₃ rfl
      have hReal := realPartyE_eval (O' := OO)
        (.snd .v5) (vpΓ (.snd .v5)) (vpRoot (.snd .v5)) .v3
        (unliftVRE L (vpVR (.snd .v5)) .v1 .v0) ρ₃ vp rfl
      rw [hReal, hUnlift]
      rfl
    have hvR : (Expr.tget (vpVR (.snd (Expr.v2 (O := OO)))) (.nat mo.tStar)).eval ρ₂ =
        vp.vR mo.tStar := rfl
    rcases hvR' : vp.vR mo.tStar with _ | (_ | rs)
    · rw [eval_caseOpt_none (hvR.trans hvR'), eval_ret, pure_bind]
      exact hFinal none h₁
    · rw [eval_caseOpt_some (hvR.trans hvR'), eval_caseOpt_none rfl]
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      have hExt2 : (fsHsExt (.snd (Expr.v2 (O := OO)))).eval
          (Env.cons (t := .opt (.base CKASort.rs)) none ρ₂) = h₁.ext := rfl
      rcases hext2 : h₁.ext with _ | ⟨ss, rs⟩
      · rw [eval_caseOpt_none (hExt2.trans hext2), eval_ite]
        cases hauth : mo.auth
        · simp only [Bool.false_eq_true, ↓reduceIte, eval_bind, query_fs_cr_eval, liftF,
            StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind, Expr.eval]
          refine bind_congr fun cr? => ?_
          rcases cr? with _ | ⟨ss', rs'⟩
          · rw [eval_caseOpt_none rfl, eval_ret, pure_bind, eval_caseOpt_none rfl, eval_ret]
            simp [ρ₂, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v3]
          · rw [eval_caseOpt_some rfl, eval_ret, pure_bind]
            simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              map_pure, Prod.map, Option.map_some]
            have hEncExt : (Expr.pair (O := OO) (.some (.some (.snd .v0)))
                (fsHsSetExt (.snd .v4) (.some .v0))).eval
                (Env.cons (t := .prod (.base CKASort.ss) (.base CKASort.rs)) (ss', rs')
                  (Env.cons (t := .opt (.prod (.base CKASort.ss) (.base CKASort.rs)))
                    (some (ss', rs'))
                    (Env.cons (t := .opt (.base CKASort.rs)) none ρ₂))) =
                (some (some rs'), hsEnc { h₁ with ext := some (ss', rs') }) := by
              simp [ρ₂, fsHsSetExt, fsHsMk, fsHsCache, fsHsTable, fsHsSessions,
                fsHsTrans, fsHsCount, fsHsSCorr, fsHsEnc, Expr.eval, Expr.v0, Expr.v4]
            rw [hEncExt]
            exact hFinal (some rs') { h₁ with ext := some (ss', rs') }
        · simp only [↓reduceIte, eval_ret, pure_bind, Expr.eval]
          rw [eval_caseOpt_none rfl, eval_ret]
          simp [ρ₂, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v2]
      · rw [eval_caseOpt_some (hExt2.trans hext2), eval_ret, pure_bind]
        have hEncExt2 : (Expr.pair (O := OO) (.some (.some (.snd .v0))) (.snd .v3)).eval
            (Env.cons (t := .prod (.base CKASort.ss) (.base CKASort.rs)) (ss, rs)
              (Env.cons (t := .opt (.base CKASort.rs)) none ρ₂)) =
            (some (some rs), hsEnc h₁) := rfl
        rw [hEncExt2]
        exact hFinal (some rs) h₁
    · rw [eval_caseOpt_some (hvR.trans hvR'), eval_caseOpt_some rfl, eval_ret, pure_bind]
      exact hFinal none h₁
  rw [eval_bind]
  have hvS : (vpVS (.snd (Expr.v0 (O := OO)))).eval ρ₁ = vp.vS := rfl
  rcases hvS' : vp.vS with _ | (_ | ss)
  · rw [eval_caseOpt_none (hvS.trans hvS'), eval_ret, pure_bind]
    exact hStep2 none h
  · rw [eval_caseOpt_some (hvS.trans hvS'), eval_caseOpt_none rfl]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    have hExt1 : (fsHsExt (.fst (Expr.v1 (O := OO)))).eval
        (Env.cons (t := .opt (.base CKASort.ss)) none ρ₁) = h.ext := rfl
    rcases hext1 : h.ext with _ | ⟨ss, rs⟩
    · rw [eval_caseOpt_none (hExt1.trans hext1)]
      simp only [eval_bind, query_fs_cs_eval, liftF, StateT.run_bind, StateT.run_lift,
        bind_assoc, pure_bind, map_bind]
      refine bind_congr fun cs? => ?_
      rcases cs? with _ | ss'
      · rw [eval_caseOpt_none rfl, eval_ret, pure_bind, eval_caseOpt_none rfl, eval_ret]
        simp [ρ₁, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v2]
      · rw [eval_caseOpt_some rfl, eval_ret, pure_bind]
        simp only [StateT.run_bind, StateT.run_modify, pure_bind]
        have hEncSCorr : (Expr.pair (O := OO) (.some (.some .v0))
            (fsHsSetSCorr (.fst .v3) (.bool true))).eval
            (Env.cons (t := .base CKASort.ss) ss'
              (Env.cons (t := .opt (.base CKASort.ss)) (some ss')
                (Env.cons (t := .opt (.base CKASort.ss)) none ρ₁))) =
            (some (some ss'), hsEnc { h with fsSCorr := true }) := by
          simp [ρ₁, fsHsSetSCorr, fsHsMk, fsHsCache, fsHsTable, fsHsSessions,
            fsHsTrans, fsHsCount, fsHsExt, fsHsEnc, Expr.eval, Expr.v0, Expr.v3]
        rw [hEncSCorr]
        exact hStep2 (some ss') { h with fsSCorr := true }
    · rw [eval_caseOpt_some (hExt1.trans hext1), eval_ret, pure_bind]
      have hEncExt1 : (Expr.pair (O := OO) (.some (.some (.fst .v0))) (.fst .v2)).eval
          (Env.cons (t := .prod (.base CKASort.ss) (.base CKASort.rs)) (ss, rs)
            (Env.cons (t := .opt (.base CKASort.ss)) none ρ₁)) =
          (some (some ss), hsEnc h) := rfl
      rw [hEncExt1]
      exact hStep2 (some ss) h
  · rw [eval_caseOpt_some (hvS.trans hvS'), eval_caseOpt_some rfl, eval_ret, pure_bind]
    exact hStep2 (some ss) h

theorem lookupF_preserve [DecidableEq I] [SampleableType K] (ik : I)
    (h : FSState T RSt K I SS RS E) :
    ∀ res ∈ support
      ((lookupF (T := T) (Sig := RSt) (SS := SS) (RS := RS) (M := M) (E := E) ik).run h),
      res.2.table.length ≤ h.table.length + 1 ∧
      res.2.sessions = h.sessions ∧
      res.2.fsTrans = h.fsTrans := by
  intro res hmem
  unfold lookupF at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  rcases hlk : h.table.lookup ik with _ | k
  · simp only [hlk, StateT.run_bind, StateT.run_lift, StateT.run_modify, StateT.run_pure,
      bind_assoc, pure_bind, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hmem
    obtain ⟨k, _, rfl⟩ := hmem
    exact ⟨by simp, rfl, rfl⟩
  · simp only [hlk, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    exact ⟨Nat.le_add_right _ _, rfl, rfl⟩

theorem isExt_preserve [DecidableEq I] (j : ℕ) (Ik : I)
    (h : FSState T RSt K I SS RS E) :
    ∀ res ∈ support
      ((isExt (T := T) (Sig := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
          j Ik).run h),
      res.2.table = h.table ∧
      res.2.sessions.length ≤ h.sessions.length + 1 ∧
      res.2.fsTrans = h.fsTrans := by
  intro res hmem
  unfold isExt at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases hm : Ik ∈ h.sessions
  · simp only [hm, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    exact ⟨rfl, Nat.le_add_right _ _, rfl⟩
  · simp only [hm, ↓reduceIte, StateT.run_bind, StateT.run_set, pure_bind] at hmem
    subst hmem
    simp

theorem extOf_preserve [DecidableEq I] (j : ℕ) (sid : Option I)
    (h : FSState T RSt K I SS RS E) :
    ∀ res ∈ support
      ((extOf (T := T) (Sig := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
          j sid).run h),
      res.2.table = h.table ∧
      res.2.sessions.length ≤ h.sessions.length + 1 ∧
      res.2.fsTrans = h.fsTrans := by
  rcases sid with _ | Ik
  · intro res hmem
    simp only [extOf, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    exact ⟨rfl, Nat.le_add_right _ _, rfl⟩
  · exact isExt_preserve j Ik h

theorem rootFS_preserve [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR RSt I K) (mo : Mode) (t : ℕ) (ik : I) (σ : RSt)
    (h : FSState T RSt K I SS RS E) :
    ∀ res ∈ support
      ((rootFS (T := T) (SS := SS) (RS := RS) (M := M) (E := E) prng mo t ik σ).run h),
      res.2.table.length ≤ h.table.length + 1 ∧
      res.2.sessions = h.sessions ∧
      res.2.fsTrans = h.fsTrans := by
  intro res hmem
  unfold rootFS at hmem
  by_cases hlt : mo.tStar < t
  · simp only [hlt, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    exact ⟨Nat.le_add_right _ _, rfl, rfl⟩
  · simp only [hlt, ↓reduceIte] at hmem
    by_cases heq : t = mo.tStar
    · have heqIf : (t = mo.tStar) ↔ True := by simp [heq]
      simp only [heqIf, ↓reduceIte] at hmem
      by_cases hc : (mo.tL.isSome && decide (t = mo.tH)) = true
      · simp only [hc, ↓reduceIte, StateT.run_bind, StateT.run_lift,
          StateT.run_pure, bind_assoc, pure_bind, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at hmem
        obtain ⟨_, _, _, _, rfl⟩ := hmem
        exact ⟨Nat.le_add_right _ _, rfl, rfl⟩
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_pure,
          mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hmem
        obtain ⟨⟨k, h₁⟩, hLk, rfl⟩ := hmem
        exact lookupF_preserve ik h (k, h₁) hLk
    · simp only [heq, ↓reduceIte] at hmem
      by_cases hc : (mo.tL.isSome && decide (t = mo.tH)) = true
      · simp only [hc, ↓reduceIte, StateT.run_bind, StateT.run_lift,
          StateT.run_pure, bind_assoc, pure_bind, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at hmem
        obtain ⟨_, _, rfl⟩ := hmem
        exact ⟨Nat.le_add_right _ _, rfl, rfl⟩
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at hmem
        subst hmem
        exact ⟨Nat.le_add_right _ _, rfl, rfl⟩

theorem fsStartSend_preserve [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (ctx : Ctx Γ T RSt (Option SS) (Option RS) M E) (P : Party)
    (t : ℕ) (γ : Γ) (σ : RSt) (r : Option CCoins)
    (h : FSState T RSt K I SS RS E) :
    ∀ res ∈ support (((hooksFS cka prng fs Δcka mo j).startSend ctx P t γ σ r).run h),
      res.2.table.length ≤ h.table.length + 1 ∧
      res.2.sessions.length ≤ h.sessions.length + 1 ∧
      res.2.fsTrans = h.fsTrans := by
  intro res hmem
  unfold hooksFS at hmem; dsimp only at hmem
  rcases r with _ | coins <;>
    simp only [StateT.run_bind, StateT.run_lift, StateT.run_modify, StateT.run_pure,
      bind_assoc, pure_bind, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hmem
  · obtain ⟨coins, _, ⟨⟨σ', k, sid⟩, h₁⟩, hRoot, ⟨ext, h₂⟩, hExt, rfl⟩ := hmem
    obtain ⟨hT1, hS1, hTr1⟩ := rootFS_preserve prng mo t (cka.send γ coins).2.2 σ h
      ((σ', k, sid), h₁) hRoot
    obtain ⟨hT2, hS2, hTr2⟩ := extOf_preserve j sid h₁ (ext, h₂) hExt
    exact ⟨hT2 ▸ hT1, hS1 ▸ hS2, hTr2.trans hTr1⟩
  · obtain ⟨⟨⟨σ', k, sid⟩, h₁⟩, hRoot, ⟨ext, h₂⟩, hExt, rfl⟩ := hmem
    obtain ⟨hT1, hS1, hTr1⟩ := rootFS_preserve prng mo t (cka.send γ coins).2.2 σ h
      ((σ', k, sid), h₁) hRoot
    obtain ⟨hT2, hS2, hTr2⟩ := extOf_preserve j sid h₁ (ext, h₂) hExt
    exact ⟨hT2 ▸ hT1, hS1 ▸ hS2, hTr2.trans hTr1⟩

theorem fsStartRecv_preserve [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (ctx : Ctx Γ T RSt (Option SS) (Option RS) M E) (P : Party)
    (t : ℕ) (γ : Γ) (σ : RSt) (Tn : T)
    (h : FSState T RSt K I SS RS E) :
    ∀ res ∈ support (((hooksFS cka prng fs Δcka mo j).startRecv ctx P t γ σ Tn).run h),
      res.2.table.length ≤ h.table.length + 1 ∧
      res.2.sessions.length ≤ h.sessions.length + 1 ∧
      res.2.fsTrans = h.fsTrans := by
  intro res hmem
  unfold hooksFS at hmem; dsimp only at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  have hNonHon :
      (res ∈ support ((if (mo.auth && decide (t = mo.tStar)) = true then
          if (mo.tL.isSome && decide (mo.tStar = mo.tH)) = true then pure none
          else do
            let k' ← lookupF (cka.receive γ Tn).2
            let ext ← isExt j (cka.receive γ Tn).2
            pure (some (some ((cka.receive γ Tn).1, (prng.up σ (cka.receive γ Tn).2).1,
              if ext = true then none else some (fs.initReceiver k'))))
        else pure (some none) :
        HM (FSAEAD.spec SS RS (Header T) M E) (FSState T RSt K I SS RS E) _).run h)) →
      res.2.table.length ≤ h.table.length + 1 ∧
      res.2.sessions.length ≤ h.sessions.length + 1 ∧
      res.2.fsTrans = h.fsTrans := by
    intro hmem'
    by_cases hc1 : (mo.auth && decide (t = mo.tStar)) = true
    · simp only [hc1, ↓reduceIte] at hmem'
      by_cases hc2 : (mo.tL.isSome && decide (mo.tStar = mo.tH)) = true
      · simp only [hc2, ↓reduceIte, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at hmem'
        subst hmem'
        exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, rfl⟩
      · simp only [hc2, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_pure,
          mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hmem'
        obtain ⟨⟨k', h₁⟩, hLk, ⟨ext, h₂⟩, hExt, rfl⟩ := hmem'
        obtain ⟨hT1, hS1, hTr1⟩ := lookupF_preserve (cka.receive γ Tn).2 h (k', h₁) hLk
        obtain ⟨hT2, hS2, hTr2⟩ := isExt_preserve j (cka.receive γ Tn).2 h₁ (ext, h₂) hExt
        exact ⟨hT2 ▸ hT1, hS1 ▸ hS2, hTr2.trans hTr1⟩
    · simp only [hc1, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hmem'
      subst hmem'
      exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, rfl⟩
  rcases hcache : h.cache t with _ | ⟨Tc, σc, k, ext⟩
  · simp only [hcache] at hmem
    exact hNonHon hmem
  · by_cases hTc : Tc = Tn
    · simp only [hcache, hTc, ↓reduceIte, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hmem
      subst hmem
      exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, rfl⟩
    · simp only [hcache, hTc, ↓reduceIte] at hmem
      exact hNonHon hmem

theorem fsFsRecv_preserve [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (ctx : Ctx Γ T RSt (Option SS) (Option RS) M E) (P : Party)
    (t : ℕ) (rsv : Option RS) (hdr : Header T) (e : E)
    (rec_ : Option (Record M (Header T × E)))
    (h : FSState T RSt K I SS RS E) :
    ∀ res ∈ support (((hooksFS cka prng fs Δcka mo j).fsRecv ctx P t rsv hdr e rec_).run h),
      res.2.table = h.table ∧
      res.2.sessions = h.sessions ∧
      res.2.fsTrans.length ≤ h.fsTrans.length := by
  intro res hmem
  unfold hooksFS at hmem; dsimp only at hmem
  rcases rsv with _ | rs
  · simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    rcases hext : h.ext with _ | ⟨ss, rs⟩
    · simp only [hext] at hmem
      set matched := h.fsTrans.find? (fun x => x.2 == (hdr, e))
      have hCont : ∀ (m? : Option (ℕ × Header T × E))
          (qres : Option (FSAEAD.ReceiveResult M)),
          res ∈ support
            ((match qres with
              | none => pure none
              | some .rejected => pure (some none)
              | some (.accepted i mo') => do
                modify fun (s : FSState T RSt K I SS RS E) =>
                  { s with fsTrans := s.fsTrans.filter (·.1 != (m?.map (·.1)).getD i) }
                match mo', rec_ with
                | some m, _ => pure (some (some ((none : Option RS), i, m)))
                | none, some r => pure (some (some ((none : Option RS), i, r.msg)))
                | none, none => pure none :
              HM (FSAEAD.spec SS RS (Header T) M E) (FSState T RSt K I SS RS E)
                (Option (Option (Option RS × ℕ × M)))).run h) →
          res.2.table = h.table ∧
          res.2.sessions = h.sessions ∧
          res.2.fsTrans.length ≤ h.fsTrans.length := by
        intro m? qres hmem
        rcases qres with _ | (_ | ⟨i, mo'⟩)
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
          subst hmem; exact ⟨rfl, rfl, le_rfl⟩
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
          subst hmem; exact ⟨rfl, rfl, le_rfl⟩
        · simp only [StateT.run_bind, StateT.run_modify, pure_bind] at hmem
          rcases mo' with _ | m
          · rcases rec_ with _ | r <;>
              (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem;
               subst hmem; exact ⟨rfl, rfl, List.length_filter_le _ _⟩)
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
            subst hmem; exact ⟨rfl, rfl, List.length_filter_le _ _⟩
      rcases matched with _ | mrec
      · simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
          liftF, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
          mem_support_bind_iff] at hmem
        obtain ⟨qres, _, hmem⟩ := hmem
        exact hCont none qres hmem
      · simp only [Option.isSome_some, ↓reduceIte,
          liftF, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
          mem_support_bind_iff] at hmem
        obtain ⟨qres, _, hmem⟩ := hmem
        exact hCont (some mrec) qres hmem
    · simp only [hext] at hmem
      rcases hrc : fs.receive rs hdr e with _ | ⟨rs', i, m⟩
      · simp only [hrc, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; exact ⟨rfl, rfl, le_rfl⟩
      · simp only [hrc, StateT.run_bind, StateT.run_set, StateT.run_pure,
          pure_bind, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; exact ⟨rfl, rfl, le_rfl⟩
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; exact ⟨rfl, rfl, le_rfl⟩

theorem hooksFSC_agrees [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B Δcka : ℕ) (mo : Mode) (j : ℕ)
    (hSend : ckaSend = cka.send)
    (hRecv : ckaReceive = cka.receive)
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send)
    (heqT : eqT = (· == ·))
    (heqI : eqI = (· == ·))
    (heqE : eqE = (· == ·))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hSampI : sampI = ($ᵗ I : ProbComp I))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (hFsRecvB : ∀ rs hdr e,
      (fsReceive rs hdr e).map (fun (rs', i, m) => (rs', min i B, m)) =
        fs.receive rs hdr e) :
    HooksCAgrees (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      hsEnc (FSHBounded L) (HBoundedPost := FSHBoundedPost L) (VROk := fun _ => True)
      (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δcka mo j)
      (hooksFSL cka prng fs L Δcka mo j) where
  hBounded_post _ h := h.2.2
  startSend_eval hE ctxE pE tE γE σE rE ρ h ctx P hHB hh _ _ :=
    (fsStartSendC_eval cka prng fs hSend hPrngUp hFsInitS heqI
      hSampCCoins hSampI hSampK L Δcka mo j hE ctxE pE tE γE σE rE ρ h ctx P hHB hh).1
  startSend_bounded ctx P t γ σ r h hHB res hmem := by
    have hB := fsStartSend_preserve cka prng fs Δcka mo j ctx P t γ σ r h res hmem
    unfold FSHBoundedPost; rw [hB.2.2]; exact hHB.2.2
  startRecv_eval hE ctxE pE tE γE σE tnE ρ h ctx P hHB hh _ _ :=
    (fsStartRecvC_eval cka prng fs hRecv hPrngUp hFsInitR heqT heqI
      hSampK L Δcka mo j hE ctxE pE tE γE σE tnE ρ h ctx P hHB hh).1
  startRecv_bounded ctx P t γ σ Tn h hHB res hmem := by
    have hB := fsStartRecv_preserve cka prng fs Δcka mo j ctx P t γ σ Tn h res hmem
    unfold FSHBoundedPost; rw [hB.2.2]; exact hHB.2.2
  startRecv_vrOk _ _ _ _ _ _ _ _ _ _ _ _ _ _ := trivial
  fsSend_eval hE ctxE pE tE ssE hdrE mE pairE ρ h ctx P _ hh hctx hp :=
    fsFsSendC_eval cka prng fs hFsSend Δcka mo j hE ctxE pE tE ssE hdrE mE pairE ρ
      h ctx P hh hctx hp
  fsRecv_eval hE ctxE pE tE rsE hdrE eE recE ρ h ctx P rec_ hHB _ hh _ _ hrec :=
    (fsFsRecvC_eval cka prng fs heqT heqE L B Δcka mo j hFsRecvB
      hE ctxE pE tE rsE hdrE eE recE ρ h ctx P rec_ hHB hh hrec).1
  fsRecv_bounded ctx P t rs hdr e rec_ h hHB res hmem := by
    have hB := fsFsRecv_preserve cka prng fs Δcka mo j ctx P t rs hdr e rec_ h res hmem
    exact hB.2.2.trans hHB
  commit_eval hE _ _ _ newE ρ h _ _ _ new _ hh _ _ _ hnew := by
    simp [hooksFSC, fsCommitC, hooksFSL, hooksFS, hh, hnew, StateT.run_pure, Prod.map, Expr.eval]
  reveal_eval hE ctxE pE vpE ρ h ctx P vp _ hh _ _ hvp :=
    fsRevealC_eval cka prng fs L Δcka mo j hE ctxE pE vpE ρ h ctx P vp hh hvp

theorem hooksFSL_reveal_eq [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L Δcka : ℕ) (mo : Mode) (j : ℕ)
    (ctx : Ctx Γ T RSt (Option SS) (Option RS) M E) (P : Party)
    (vp : VP Γ T RSt (Option SS) (Option RS))
    (hvR : ∀ t, L ≤ t → vp.vR t = none) :
    (hooksFSL cka prng fs L Δcka mo j).reveal ctx P vp =
      (hooksFS cka prng fs Δcka mo j).reveal ctx P vp := by
  have hvR_eq : ∀ (rsExt : Option RS),
      (fun (t : ℕ) => if t < L then unliftEntry (vp.vR t) rsExt else none) =
      (fun (t : ℕ) =>
        match vp.vR t with
        | some (some rs) => some rs
        | some none => rsExt
        | none => none) := by
    intro rsExt; funext t
    by_cases ht : t < L
    · simp [ht, unliftEntry]
    · simp [ht, hvR t (Nat.le_of_not_lt ht)]
  unfold hooksFSL hooksFS
  dsimp only
  simp only [hvR_eq]
  rfl

@[simp] theorem vSend_hooksFSL_eq [DecidableEq T] [DecidableEq I] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L Δcka : ℕ) (mo : Mode) (j : ℕ) :
    vSend (hooksFSL cka prng fs L Δcka mo j) = vSend (hooksFS cka prng fs Δcka mo j) := by
  funext s P st m pair r
  unfold vSend hooksFSL
  rfl

@[simp] theorem vRecv_hooksFSL_eq [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L Δcka : ℕ) (mo : Mode) (j : ℕ) :
    vRecv (hooksFSL cka prng fs L Δcka mo j) = vRecv (hooksFS cka prng fs Δcka mo j) := by
  funext s P st c rec_
  unfold vRecv hooksFSL
  rfl

@[simp] theorem commitE_hooksFSL_eq [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L Δcka : ℕ) (mo : Mode) (j : ℕ) :
    commitE (hooksFSL cka prng fs L Δcka mo j) = commitE (hooksFS cka prng fs Δcka mo j) := by
  funext s P old new pos
  unfold commitE hooksFSL
  rfl

@[simp] theorem transmitE_hooksFSL_eq [DecidableEq T] [DecidableEq I] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L Δ qep : ℕ) (π : Policy) (Δcka : ℕ) (mo : Mode) (j : ℕ) :
    transmitE (hooksFSL cka prng fs L Δcka mo j) Δ qep π =
      transmitE (hooksFS cka prng fs Δcka mo j) Δ qep π := by
  funext q; unfold transmitE; rw [vSend_hooksFSL_eq]

@[simp] theorem challE_hooksFSL_eq [DecidableEq T] [DecidableEq I] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L Δ qep : ℕ) (cfg : Config M) (π : Policy) (Δcka : ℕ) (mo : Mode) (j : ℕ) :
    challE (hooksFSL cka prng fs L Δcka mo j) Δ qep cfg π =
      challE (hooksFS cka prng fs Δcka mo j) Δ qep cfg π := by
  funext q; unfold challE; rw [vSend_hooksFSL_eq]

@[simp] theorem deliverE_hooksFSL_eq [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L maxSkip : ℕ) (cfg : Config M) (Δcka : ℕ) (mo : Mode) (j : ℕ) :
    deliverE (hooksFSL cka prng fs L Δcka mo j) maxSkip cfg =
      deliverE (hooksFS cka prng fs Δcka mo j) maxSkip cfg := by
  funext q; unfold deliverE; rw [vRecv_hooksFSL_eq, commitE_hooksFSL_eq]

@[simp] theorem injectE_hooksFSL_eq [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L Δ qep : ℕ) (cfg : Config M) (Δcka : ℕ) (mo : Mode) (j : ℕ) :
    injectE (hooksFSL cka prng fs L Δcka mo j) Δ qep cfg =
      injectE (hooksFS cka prng fs Δcka mo j) Δ qep cfg := by
  funext q; unfold injectE; rw [vRecv_hooksFSL_eq, commitE_hooksFSL_eq]

theorem corrE_hooksFSL_eq [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L : ℕ) (π : Policy) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (es : EState (VP Γ T RSt (Option SS) (Option RS)) M (Header T × E)
      (FSState T RSt K I SS RS E))
    (P : Party)
    (hvR : ∀ t, L ≤ t → (es.g.st P).vR t = none) :
    (corrE (hooksFSL cka prng fs L Δcka mo j) π P).run es =
      (corrE (hooksFS cka prng fs Δcka mo j) π P).run es := by
  unfold corrE
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases href : (es.abort || es.g.win || !es.g.corrAllowed P)
  · simp [href]
  · simp only [href, Bool.false_eq_true, ↓reduceIte]
    by_cases hdoom : (π.leakDoom es.g (es.g.afterCorr P) || π.corrDoom es.g P)
    · simp [hdoom]
    · simp only [hdoom, Bool.false_eq_true, ↓reduceIte, run_liftH_bind,
        hooksFSL_reveal_eq cka prng fs L Δcka mo j es.g P (es.g.st P) hvR]

theorem implE_hooksFSL_eq [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [Inhabited E] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L Δ qep maxSkip : ℕ) (cfg : Config M) (π : Policy)
    (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (es : EState (VP Γ T RSt (Option SS) (Option RS)) M (Header T × E)
      (FSState T RSt K I SS RS E))
    (q : (SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hvR : ∀ P t, L ≤ t → (es.g.st P).vR t = none) :
    (implE (hooksFSL cka prng fs L Δcka mo j) Δ qep maxSkip cfg π (.inr q)).run es =
      (implE (hooksFS cka prng fs Δcka mo j) Δ qep maxSkip cfg π (.inr q)).run es := by
  rcases q with (((arg | arg) | arg) | arg) | P
  · change (transmitE (hooksFSL cka prng fs L Δcka mo j) Δ qep π arg).run es =
      (transmitE (hooksFS cka prng fs Δcka mo j) Δ qep π arg).run es
    rw [transmitE_hooksFSL_eq]
  · change (challE (hooksFSL cka prng fs L Δcka mo j) Δ qep cfg π arg).run es =
      (challE (hooksFS cka prng fs Δcka mo j) Δ qep cfg π arg).run es
    rw [challE_hooksFSL_eq]
  · change (deliverE (hooksFSL cka prng fs L Δcka mo j) maxSkip cfg arg).run es =
      (deliverE (hooksFS cka prng fs Δcka mo j) maxSkip cfg arg).run es
    rw [deliverE_hooksFSL_eq]
  · change (injectE (hooksFSL cka prng fs L Δcka mo j) Δ qep cfg arg).run es =
      (injectE (hooksFS cka prng fs Δcka mo j) Δ qep cfg arg).run es
    rw [injectE_hooksFSL_eq]
  · exact corrE_hooksFSL_eq cka prng fs L π Δcka mo j es P (hvR P)

/-! ## Engine invariant and simulation agreement -/

/-- Combined engine and hook-state invariant for `redFS` across `q` remaining queries. -/
structure FSEngineInv (L B q : ℕ)
    (es : EState (VP Γ T RSt (Option SS) (Option RS)) M (Header T × E)
      (FSState T RSt K I SS RS E)) : Prop where
  sm : SMEngineInv L B q es.g
  table_le : es.h.table.length + q ≤ B + 1
  sessions_le : es.h.sessions.length + q ≤ B + 1
  fsTrans_le : es.h.fsTrans.length + q ≤ B
  tcur_le : ∀ P : Party, (es.g.st P).tcur + q ≤ B
  vR_none_of_gt : ∀ (P : Party) (t : ℕ), (es.g.st P).tcur < t → (es.g.st P).vR t = none

theorem FSEngineInv.mono {L B q q' : ℕ}
    {es : EState (VP Γ T RSt (Option SS) (Option RS)) M (Header T × E)
      (FSState T RSt K I SS RS E)}
    (hq : q' ≤ q) (h : FSEngineInv L B q es) : FSEngineInv L B q' es where
  sm := h.sm.mono hq
  table_le := by have := h.table_le; omega
  sessions_le := by have := h.sessions_le; omega
  fsTrans_le := by have := h.fsTrans_le; omega
  tcur_le P := by have := h.tcur_le P; omega
  vR_none_of_gt := h.vR_none_of_gt

theorem FSEngineInv.toFSHBounded {L B q : ℕ}
    {es : EState (VP Γ T RSt (Option SS) (Option RS)) M (Header T × E)
      (FSState T RSt K I SS RS E)}
    (h : FSEngineInv L B (q + 1) es) : FSHBounded L es.h :=
  ⟨by have := h.table_le; have := h.sm.b_succ_le; omega,
   by have := h.sessions_le; have := h.sm.b_succ_le; omega,
   by have := h.fsTrans_le; have := h.sm.b_succ_le; omega⟩

theorem FSEngineInv.vR_none_of_le_L {L B q : ℕ}
    {es : EState (VP Γ T RSt (Option SS) (Option RS)) M (Header T × E)
      (FSState T RSt K I SS RS E)}
    (h : FSEngineInv L B q es) (P : Party) (t : ℕ) (ht : L ≤ t) :
    (es.g.st P).vR t = none :=
  h.vR_none_of_gt P t (by have := h.tcur_le P; have := h.sm.b_succ_le; omega)

theorem fsFsSend_preserve [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (h : FSState T RSt K I SS RS E) (ctx : Ctx Γ T RSt (Option SS) (Option RS) M E)
    (P : Party) (t : ℕ) (ssv : Option SS) (hdr : Header T) (m : M) (pair : Option (M × M)) :
    ∀ res ∈ support (((hooksFS cka prng fs Δcka mo j).fsSend ctx P t ssv hdr m pair).run h),
      res.2.table = h.table ∧
      res.2.sessions = h.sessions ∧
      res.2.fsTrans.length ≤ h.fsTrans.length + 1 := by
  intro res hmem
  dsimp only [hooksFS] at hmem
  rcases ssv with _ | ss
  · simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    rcases hext : h.ext with _ | ⟨ss, rs⟩
    · simp only [hext] at hmem
      have hStep2 : ∀ (h₁ : FSState T RSt K I SS RS E),
          h₁.table = h.table → h₁.sessions = h.sessions → h₁.fsTrans = h.fsTrans →
          ∀ res ∈ support (((match pair with
            | some (m₀, m₁) => do
              let e? ←
                liftF (FSAEAD.challengeQuery (SenderState := SS) (ReceiverState := RS) hdr m₀ m₁)
              match e? with
              | none => pure none
              | some e => do
                modify fun s =>
                  { s with fsCount := s.fsCount + 1,
                           fsTrans := (s.fsCount + 1, hdr, e) :: s.fsTrans }
                pure (some (none, e))
            | none => do
              let e? ←
                liftF (FSAEAD.transmitQuery (SenderState := SS) (ReceiverState := RS) hdr m)
              match e? with
              | none => pure none
              | some e => do
                modify fun s =>
                  { s with fsCount := s.fsCount + 1,
                           fsTrans := (s.fsCount + 1, hdr, e) :: s.fsTrans }
                pure (some (none, e)) :
            HM (FSAEAD.spec SS RS (Header T) M E) (FSState T RSt K I SS RS E)
              (Option (Option SS × E))).run h₁)),
            res.2.table = h.table ∧
            res.2.sessions = h.sessions ∧
            res.2.fsTrans.length ≤ h.fsTrans.length + 1 := by
        intro h₁ htb hse htr res hmem2
        rcases pair with _ | ⟨m₀, m₁⟩ <;>
        · simp only [liftF, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
            mem_support_bind_iff] at hmem2
          obtain ⟨e?, _, hmem2⟩ := hmem2
          rcases e? with _ | e
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem2
            subst hmem2; exact ⟨htb, hse, by simp [htr]⟩
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff] at hmem2
            subst hmem2; exact ⟨htb, hse, by simp [htr]⟩
      by_cases hc : (!ctx.safeCh (2 + Δcka) P && !h.fsSCorr) = true
      · simp only [hc, ↓reduceIte, liftF, StateT.run_bind, StateT.run_lift,
          bind_assoc] at hmem
        rw [mem_support_bind_iff] at hmem
        obtain ⟨ans, _, hmem⟩ := hmem
        rcases ans with _ | ss'
        · simp only [StateT.run_pure, pure_bind, Bool.not_false, ↓reduceIte,
            support_pure, Set.mem_singleton_iff] at hmem
          subst hmem
          exact ⟨rfl, rfl, Nat.le_add_right _ _⟩
        · simp only [StateT.run_bind, StateT.run_modify, pure_bind,
            Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hmem
          exact hStep2 { h with fsSCorr := true } rfl rfl rfl res hmem
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, Bool.not_true] at hmem
        exact hStep2 h rfl rfl rfl res hmem
    · simp only [hext, StateT.run_bind, StateT.run_set, pure_bind] at hmem
      subst hmem
      exact ⟨rfl, rfl, Nat.le_add_right _ _⟩
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    exact ⟨rfl, rfl, Nat.le_add_right _ _⟩

theorem fsReveal_preserve [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (h : FSState T RSt K I SS RS E) (ctx : Ctx Γ T RSt (Option SS) (Option RS) M E)
    (P : Party) (vp : VP Γ T RSt (Option SS) (Option RS)) :
    ∀ res ∈ support (((hooksFS cka prng fs Δcka mo j).reveal ctx P vp).run h),
      res.2.table = h.table ∧
      res.2.sessions = h.sessions ∧
      res.2.fsTrans = h.fsTrans := by
  intro res hmem
  simp only [hooksFS, pure_bind] at hmem
  have hStep2 : ∀ (vS : Option SS) (h₁ : FSState T RSt K I SS RS E),
      h₁.table = h.table → h₁.sessions = h.sessions → h₁.fsTrans = h.fsTrans →
      res ∈ support (((match vp.vR mo.tStar with
        | some none => do
          let s ← get
          match s.ext with
          | some (_, rs) =>
            pure (some (realParty vp vp.γ vp.root vS fun t =>
              match vp.vR t with
              | some (some rs) => some rs
              | some none => some rs
              | none => none))
          | none =>
            if mo.auth = true then pure none
            else do
              let ans ← liftF (FSAEAD.corruptReceiverQuery (SenderState := SS) (ReceiverState := RS)
                  (AssocData := Header T) (Message := M) (Ciphertext := E))
              match ans with
              | none => pure none
              | some (ss, rs) => do
                modify fun s => { s with ext := some (ss, rs) }
                pure (some (realParty vp vp.γ vp.root vS fun t =>
                  match vp.vR t with
                  | some (some rs) => some rs
                  | some none => some rs
                  | none => none))
        | _ =>
          pure (some (realParty vp vp.γ vp.root vS fun t =>
            match vp.vR t with
            | some (some rs) => some rs
            | some none => none
            | none => none)) :
        HM (FSAEAD.spec SS RS (Header T) M E) (FSState T RSt K I SS RS E)
          (Option (PartyState Γ T RSt SS RS))).run h₁)) →
      res.2.table = h.table ∧
      res.2.sessions = h.sessions ∧
      res.2.fsTrans = h.fsTrans := by
    intro vS h₁ htb hse htr hmem2
    rcases hvR : vp.vR mo.tStar with _ | (_ | rs)
    · simp only [hvR, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem2
      subst hmem2; exact ⟨htb, hse, htr⟩
    · simp only [hvR, StateT.run_bind, StateT.run_get, pure_bind] at hmem2
      rcases hext : h₁.ext with _ | ⟨ss, rs⟩
      · simp only [hext] at hmem2
        by_cases hauth : mo.auth = true
        · simp only [hauth, ↓reduceIte, StateT.run_pure,
            support_pure, Set.mem_singleton_iff] at hmem2
          subst hmem2; exact ⟨htb, hse, htr⟩
        · simp only [hauth, Bool.false_eq_true, ↓reduceIte, liftF,
            StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind] at hmem2
          rw [mem_support_bind_iff] at hmem2
          obtain ⟨ans, _, hmem2⟩ := hmem2
          rcases ans with _ | ⟨ss', rs'⟩
          · simp only [StateT.run_pure,
              support_pure, Set.mem_singleton_iff] at hmem2
            subst hmem2; exact ⟨htb, hse, htr⟩
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff] at hmem2
            subst hmem2; exact ⟨htb, hse, htr⟩
      · simp only [hext, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at hmem2
        subst hmem2; exact ⟨htb, hse, htr⟩
    · simp only [hvR, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem2
      subst hmem2; exact ⟨htb, hse, htr⟩
  rcases hvS : vp.vS with _ | (_ | ss)
  · simp only [hvS] at hmem
    exact hStep2 none h rfl rfl rfl hmem
  · simp only [hvS, StateT.run_bind, StateT.run_get, pure_bind] at hmem
    rcases hext : h.ext with _ | ⟨ss, rs⟩
    · simp only [hext, liftF, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind] at hmem
      rw [mem_support_bind_iff] at hmem
      obtain ⟨ans, _, hmem⟩ := hmem
      rcases ans with _ | ss'
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; exact ⟨rfl, rfl, rfl⟩
      · simp only [StateT.run_bind, StateT.run_modify, pure_bind] at hmem
        exact hStep2 (some ss') { h with fsSCorr := true } rfl rfl rfl hmem
    · simp only [hext] at hmem
      exact hStep2 (some ss) h rfl rfl rfl hmem
  · simp only [hvS] at hmem
    exact hStep2 (some ss) h rfl rfl rfl hmem

theorem vSend_fs_preserve [DecidableEq T] [DecidableEq I] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (ctx : Ctx Γ T RSt (Option SS) (Option RS) M E) (P : Party)
    (s : VP Γ T RSt (Option SS) (Option RS)) (m : M)
    (pair : Option (M × M)) (r : Option CCoins)
    (h : FSState T RSt K I SS RS E) :
    ∀ res ∈ support ((vSend (hooksFS cka prng fs Δcka mo j) ctx P s m pair r).run h),
      res.2.table.length ≤ h.table.length + 1 ∧
      res.2.sessions.length ≤ h.sessions.length + 1 ∧
      res.2.fsTrans.length ≤ h.fsTrans.length + 1 ∧
      (∀ st' c, res.1 = some (st', c) →
        s.tcur ≤ st'.tcur ∧ st'.tcur ≤ s.tcur + 1 ∧ st'.vR = s.vR) := by
  intro ⟨vsRes, h'⟩ hmem
  rw [vSend_eq_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨s₁?, h₁⟩, hmem1, hmem2⟩ := hmem
  have hStep1 :
      h₁.table.length ≤ h.table.length + 1 ∧
      h₁.sessions.length ≤ h.sessions.length + 1 ∧
      h₁.fsTrans = h.fsTrans ∧
      (∀ s₁, s₁? = some s₁ →
        s.tcur ≤ s₁.tcur ∧ s₁.tcur ≤ s.tcur + 1 ∧ s₁.vR = s.vR) := by
    unfold vSendStep1 at hmem1
    split_ifs at hmem1
    · rw [StateT.run_bind, mem_support_bind_iff] at hmem1
      obtain ⟨⟨ssRes, h₁'⟩, hss, hmem1⟩ := hmem1
      have hPres := fsStartSend_preserve cka prng fs Δcka mo j ctx P
        (s.tcur + 1) s.γ s.root r h (ssRes, h₁') hss
      rcases ssRes with _ | ⟨γ', T', σ', ss⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem1
        rcases hmem1 with ⟨rfl, rfl⟩
        exact ⟨hPres.1, hPres.2.1, hPres.2.2, fun _ h => by cases h⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem1
        rcases hmem1 with ⟨rfl, rfl⟩
        refine ⟨hPres.1, hPres.2.1, hPres.2.2, fun s₁ hs₁ => ?_⟩
        cases hs₁
        exact ⟨Nat.le_succ _, le_rfl, rfl⟩
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem1
      rcases hmem1 with ⟨rfl, rfl⟩
      exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, rfl,
        fun s₁ hs₁ => by cases hs₁; exact ⟨le_rfl, Nat.le_succ _, rfl⟩⟩
  rcases s₁? with _ | s₁
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2
    rcases hmem2 with ⟨rfl, rfl⟩
    exact ⟨hStep1.1, hStep1.2.1, by rw [hStep1.2.2.1]; exact Nat.le_add_right _ _,
      fun _ _ h => by cases h⟩
  · have hs₁ := hStep1.2.2.2 s₁ rfl
    rcases hvS : s₁.vS with _ | v
    · simp only [hvS, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem2
      rcases hmem2 with ⟨rfl, rfl⟩
      refine ⟨hStep1.1, hStep1.2.1, by rw [hStep1.2.2.1]; exact Nat.le_add_right _ _,
        fun st' c hEq => ?_⟩
      cases hEq; exact hs₁
    · simp only [hvS] at hmem2
      rw [StateT.run_bind, mem_support_bind_iff] at hmem2
      obtain ⟨⟨fsRes, h₂⟩, hfs, hmem2⟩ := hmem2
      have hPres2 := fsFsSend_preserve cka prng fs Δcka mo j h₁ ctx P s₁.tcur v
        (s₁.tcur, s₁.curCkaMsg) m pair (fsRes, h₂) hfs
      rcases fsRes with _ | ⟨v', e⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2
        rcases hmem2 with ⟨rfl, rfl⟩
        exact ⟨by rw [hPres2.1]; exact hStep1.1,
          by rw [hPres2.2.1]; exact hStep1.2.1,
          by rw [← hStep1.2.2.1]; exact hPres2.2.2,
          fun _ _ h => by cases h⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2
        rcases hmem2 with ⟨rfl, rfl⟩
        refine ⟨by rw [hPres2.1]; exact hStep1.1,
          by rw [hPres2.2.1]; exact hStep1.2.1,
          by rw [← hStep1.2.2.1]; exact hPres2.2.2,
          fun st' c hEq => ?_⟩
        cases hEq; exact hs₁

theorem vRecv_fs_preserve [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (ctx : Ctx Γ T RSt (Option SS) (Option RS) M E) (P : Party)
    (s : VP Γ T RSt (Option SS) (Option RS))
    (c : Header T × E) (rec : Option (Record M (Header T × E)))
    (h : FSState T RSt K I SS RS E)
    (hvR : ∀ t, s.tcur < t → s.vR t = none) :
    ∀ res ∈ support ((vRecv (hooksFS cka prng fs Δcka mo j) ctx P s c rec).run h),
      res.2.table.length ≤ h.table.length + 1 ∧
      res.2.sessions.length ≤ h.sessions.length + 1 ∧
      res.2.fsTrans.length ≤ h.fsTrans.length ∧
      (∀ st' t' i' m', res.1 = some (some (st', t', i', m')) →
        st'.tcur ≤ s.tcur + 1 ∧ (∀ t, st'.tcur < t → st'.vR t = none)) := by
  intro ⟨vrRes, h'⟩ hmem
  rw [vRecv_eq_bind] at hmem
  by_cases h1 : (s.id.sendsIn c.1.1 || decide (s.tcur + 1 < c.1.1)) = true
  · simp only [h1, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, le_rfl, fun _ _ _ _ h => by cases h⟩
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hmem
    have htle : c.1.1 ≤ s.tcur + 1 := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at h1
      omega
    rw [StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨s₁?, h₁⟩, hmem1, hmem2⟩ := hmem
    have hStep1 :
        h₁.table.length ≤ h.table.length + 1 ∧
        h₁.sessions.length ≤ h.sessions.length + 1 ∧
        h₁.fsTrans = h.fsTrans ∧
        (∀ s₁, s₁? = some (some s₁) →
          c.1.1 ≤ s₁.tcur ∧ s₁.tcur ≤ s.tcur + 1 ∧
          (∀ t, s₁.tcur < t → s₁.vR t = none)) := by
      unfold vRecvStep1 at hmem1
      by_cases h2 : c.1.1 = s.tcur + 1
      · simp only [h2, ↓reduceIte] at hmem1
        rcases hTn : c.1.2 with _ | Tn
        · simp only [hTn, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem1
          rcases hmem1 with ⟨rfl, rfl⟩
          exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, rfl, fun _ h => by cases h⟩
        · simp only [hTn] at hmem1
          rw [StateT.run_bind, mem_support_bind_iff] at hmem1
          obtain ⟨⟨srRes, h₁'⟩, hsr, hmem1⟩ := hmem1
          have hPres := fsStartRecv_preserve cka prng fs Δcka mo j ctx P
            (s.tcur + 1) s.γ s.root Tn h (srRes, h₁') hsr
          rcases srRes with _ | _ | ⟨γ', σ', rs⟩
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem1
            rcases hmem1 with ⟨rfl, rfl⟩
            exact ⟨hPres.1, hPres.2.1, hPres.2.2, fun _ h => by cases h⟩
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem1
            rcases hmem1 with ⟨rfl, rfl⟩
            exact ⟨hPres.1, hPres.2.1, hPres.2.2, fun _ h => by cases h⟩
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem1
            rcases hmem1 with ⟨rfl, rfl⟩
            refine ⟨hPres.1, hPres.2.1, hPres.2.2, fun s₁ hs₁ => ?_⟩
            cases hs₁
            refine ⟨by omega, le_rfl, fun t ht => ?_⟩
            dsimp only at ht ⊢
            rw [Function.update_of_ne (by omega)]
            exact hvR t (by omega)
      · simp only [h2, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem1
        rcases hmem1 with ⟨rfl, rfl⟩
        refine ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, rfl, fun s₁ hs₁ => ?_⟩
        cases hs₁
        exact ⟨by omega, Nat.le_succ _, hvR⟩
    rcases s₁? with _ | _ | s₁
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2
      rcases hmem2 with ⟨rfl, rfl⟩
      exact ⟨hStep1.1, hStep1.2.1, by rw [hStep1.2.2.1], fun _ _ _ _ h => by cases h⟩
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2
      rcases hmem2 with ⟨rfl, rfl⟩
      exact ⟨hStep1.1, hStep1.2.1, by rw [hStep1.2.2.1], fun _ _ _ _ h => by cases h⟩
    · have hs₁ := hStep1.2.2.2 s₁ rfl
      rcases hvR1 : s₁.vR c.1.1 with _ | v
      · simp only [hvR1, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem2
        rcases hmem2 with ⟨rfl, rfl⟩
        exact ⟨hStep1.1, hStep1.2.1, by rw [hStep1.2.2.1], fun _ _ _ _ h => by cases h⟩
      · simp only [hvR1] at hmem2
        rw [StateT.run_bind, mem_support_bind_iff] at hmem2
        obtain ⟨⟨frRes, h₂⟩, hfr, hmem2⟩ := hmem2
        have hPres2 := fsFsRecv_preserve cka prng fs Δcka mo j ctx P c.1.1 v
          c.1 c.2 rec h₁ (frRes, h₂) hfr
        rcases frRes with _ | _ | ⟨v', i, m⟩
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2
          rcases hmem2 with ⟨rfl, rfl⟩
          exact ⟨by rw [hPres2.1]; exact hStep1.1,
            by rw [hPres2.2.1]; exact hStep1.2.1,
            by rw [← hStep1.2.2.1]; exact hPres2.2.2,
            fun _ _ _ _ h => by cases h⟩
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2
          rcases hmem2 with ⟨rfl, rfl⟩
          exact ⟨by rw [hPres2.1]; exact hStep1.1,
            by rw [hPres2.2.1]; exact hStep1.2.1,
            by rw [← hStep1.2.2.1]; exact hPres2.2.2,
            fun _ _ _ _ h => by cases h⟩
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2
          rcases hmem2 with ⟨rfl, rfl⟩
          refine ⟨by rw [hPres2.1]; exact hStep1.1,
            by rw [hPres2.2.1]; exact hStep1.2.1,
            by rw [← hStep1.2.2.1]; exact hPres2.2.2,
            fun st' t' i' m' hEq => ?_⟩
          cases hEq
          refine ⟨hs₁.2.1, fun t ht => ?_⟩
          dsimp only at ht ⊢
          rw [Function.update_of_ne (by omega)]
          exact hs₁.2.2 t ht

theorem epMgmt_st_eq {St Msg C : Type} {Δ qep : ℕ} {s s₁ : SM.GameState St Msg C}
    {P : Party} {bad : Bool} (h : s.epMgmt Δ qep P bad = some s₁) :
    s₁.st = s.st := by
  unfold SM.GameState.epMgmt at h
  by_cases h1 : P.sendsIn (s.epoch P + 1)
  · by_cases h2 : qep < s.epoch P + 1
    · simp [h1, h2] at h
    · simp only [h1, h2, ↓reduceIte, Option.some.injEq] at h
      subst h
      by_cases h3 : (bad && !(s.safeCh Δ P)) = true <;> simp [h3, SM.GameState.leak]
  · by_cases h2 : qep < s.epoch P
    · simp [h1, h2] at h
    · simp only [h1, Bool.false_eq_true, h2, ↓reduceIte, Option.some.injEq] at h
      subst h; rfl

theorem commitE_fs_eq [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (es : EState (VP Γ T RSt (Option SS) (Option RS)) M (Header T × E)
      (FSState T RSt K I SS RS E))
    (s : Ctx Γ T RSt (Option SS) (Option RS) M E) (P : Party)
    (old new : VP Γ T RSt (Option SS) (Option RS)) (pos : Pos) :
    (commitE (hooksFS cka prng fs Δcka mo j) s P old new pos).run es =
      pure (some { s.accept P new pos with st := Function.update (s.accept P new pos).st P new },
        es) := by
  unfold commitE
  simp only [pure_bind, run_liftH_bind, hooksFS, StateT.run_pure]

theorem transmitE_fs_inv [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [Inhabited E] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    {L B q Δ qep : ℕ} (π : Policy) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (es : EState (VP Γ T RSt (Option SS) (Option RS)) M (Header T × E)
      (FSState T RSt K I SS RS E))
    (arg : Party × M × Option CCoins)
    (hInv : FSEngineInv L B (q + 1) es) :
    ∀ res ∈ support ((transmitE (hooksFS cka prng fs Δcka mo j) Δ qep π arg).run es),
      FSEngineInv L B q res.2 := by
  rcases arg with ⟨P, m, r⟩
  intro ⟨out, es'⟩ hmem
  have hInvQ : FSEngineInv L B q es := hInv.mono (Nat.le_succ q)
  have hSm := transmitE_inv (hooksFS cka prng fs Δcka mo j) π es (P, m, r) hInv.sm
    (out, es') hmem
  unfold transmitE abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases hab : (es.abort || es.g.win)
  · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hInvQ
  · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
    rcases hep : es.g.epMgmt Δ qep P r.isSome with _ | s₁
    · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInvQ
    · simp only [hep] at hmem
      by_cases hdoom : π.leakDoom es.g s₁
      · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
          pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩
        exact ⟨hSm, hInvQ.table_le, hInvQ.sessions_le, hInvQ.fsTrans_le,
          hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
      · simp only [hdoom, Bool.false_eq_true, ↓reduceIte] at hmem
        rw [run_liftH_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨vsRes, h'⟩, hvs, hmem⟩ := hmem
        have hPres := vSend_fs_preserve cka prng fs Δcka mo j s₁ P (s₁.st P) m none r es.h
          (vsRes, h') hvs
        dsimp only at hPres
        have hSt₁ : s₁.st = es.g.st := epMgmt_st_eq hep
        rcases vsRes with _ | ⟨st', c⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩
          exact ⟨hSm,
            by dsimp only; have := hInv.table_le; have := hPres.1; omega,
            by dsimp only; have := hInv.sessions_le; have := hPres.2.1; omega,
            by dsimp only; have := hInv.fsTrans_le; have := hPres.2.2.1; omega,
            hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩
          have hst' := hPres.2.2.2 st' c rfl
          rw [hSt₁] at hst'
          refine ⟨hSm,
            by dsimp only; have := hInv.table_le; have := hPres.1; omega,
            by dsimp only; have := hInv.sessions_le; have := hPres.2.1; omega,
            by dsimp only; have := hInv.fsTrans_le; have := hPres.2.2.1; omega,
            fun Q => ?_, fun Q t ht => ?_⟩
          · dsimp only [SM.GameState.record]
            rw [hSt₁]
            by_cases hQ : Q = P
            · subst hQ; rw [Function.update_self]
              have := hInv.tcur_le Q; have := hst'.2.1; omega
            · rw [Function.update_of_ne hQ]; exact hInvQ.tcur_le Q
          · dsimp only [SM.GameState.record] at ht ⊢
            rw [hSt₁] at ht ⊢
            by_cases hQ : Q = P
            · subst hQ; rw [Function.update_self] at ht ⊢
              rw [hst'.2.2]
              exact hInv.vR_none_of_gt Q t (by have := hst'.1; omega)
            · rw [Function.update_of_ne hQ] at ht ⊢
              exact hInv.vR_none_of_gt Q t ht

theorem challE_fs_inv [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [Inhabited E] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    {L B q Δ qep : ℕ} (cfg : Config M) (π : Policy) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (es : EState (VP Γ T RSt (Option SS) (Option RS)) M (Header T × E)
      (FSState T RSt K I SS RS E))
    (arg : Party × M × M × Option CCoins)
    (hInv : FSEngineInv L B (q + 1) es) :
    ∀ res ∈ support ((challE (hooksFS cka prng fs Δcka mo j) Δ qep cfg π arg).run es),
      FSEngineInv L B q res.2 := by
  rcases arg with ⟨P, m₀, m₁, r⟩
  intro ⟨out, es'⟩ hmem
  have hInvQ : FSEngineInv L B q es := hInv.mono (Nat.le_succ q)
  have hSm := challE_inv (hooksFS cka prng fs Δcka mo j) cfg π es (P, m₀, m₁, r) hInv.sm
    (out, es') hmem
  unfold challE abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases hab : (es.abort || es.g.win)
  · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hInvQ
  · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
    rcases hep : es.g.epMgmt Δ qep P r.isSome with _ | s₁
    · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInvQ
    · simp only [hep] at hmem
      by_cases hch : (!(s₁.safeCh Δ P) || !(cfg.challAllowedIn (s₁.epoch P)))
      · simp only [hch, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hInvQ
      · simp only [hch, Bool.false_eq_true, ↓reduceIte] at hmem
        by_cases hdoom : π.leakDoom es.g s₁
        · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
            pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩
          exact ⟨hSm, hInvQ.table_le, hInvQ.sessions_le, hInvQ.fsTrans_le,
            hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
        · simp only [hdoom, Bool.false_eq_true, ↓reduceIte] at hmem
          rw [run_liftH_bind, mem_support_bind_iff] at hmem
          obtain ⟨⟨vsRes, h'⟩, hvs, hmem⟩ := hmem
          have hPres := vSend_fs_preserve cka prng fs Δcka mo j s₁ P (s₁.st P) _
            (some (m₀, m₁)) r es.h (vsRes, h') hvs
          dsimp only at hPres
          have hSt₁ : s₁.st = es.g.st := epMgmt_st_eq hep
          rcases vsRes with _ | ⟨st', c⟩
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩
            exact ⟨hSm,
              by dsimp only; have := hInv.table_le; have := hPres.1; omega,
              by dsimp only; have := hInv.sessions_le; have := hPres.2.1; omega,
              by dsimp only; have := hInv.fsTrans_le; have := hPres.2.2.1; omega,
              hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩
            have hst' := hPres.2.2.2 st' c rfl
            rw [hSt₁] at hst'
            refine ⟨hSm,
              by dsimp only; have := hInv.table_le; have := hPres.1; omega,
              by dsimp only; have := hInv.sessions_le; have := hPres.2.1; omega,
              by dsimp only; have := hInv.fsTrans_le; have := hPres.2.2.1; omega,
              fun Q => ?_, fun Q t ht => ?_⟩
            · dsimp only [SM.GameState.record]
              rw [hSt₁]
              by_cases hQ : Q = P
              · subst hQ; rw [Function.update_self]
                have := hInv.tcur_le Q; have := hst'.2.1; omega
              · rw [Function.update_of_ne hQ]; exact hInvQ.tcur_le Q
            · dsimp only [SM.GameState.record] at ht ⊢
              rw [hSt₁] at ht ⊢
              by_cases hQ : Q = P
              · subst hQ; rw [Function.update_self] at ht ⊢
                rw [hst'.2.2]
                exact hInv.vR_none_of_gt Q t (by have := hst'.1; omega)
              · rw [Function.update_of_ne hQ] at ht ⊢
                exact hInv.vR_none_of_gt Q t ht

theorem deliverE_fs_inv [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    {L B q maxSkip : ℕ} (cfg : Config M) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (es : EState (VP Γ T RSt (Option SS) (Option RS)) M (Header T × E)
      (FSState T RSt K I SS RS E))
    (arg : Party × (Header T × E))
    (hInv : FSEngineInv L B (q + 1) es) :
    ∀ res ∈ support ((deliverE (hooksFS cka prng fs Δcka mo j) maxSkip cfg arg).run es),
      FSEngineInv L B q res.2 := by
  rcases arg with ⟨P, c⟩
  intro ⟨out, es'⟩ hmem
  have hInvQ : FSEngineInv L B q es := hInv.mono (Nat.le_succ q)
  have hSm := deliverE_inv (hooksFS cka prng fs Δcka mo j) cfg es (P, c) hInv.sm
    (out, es') hmem
  unfold deliverE abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases hab : (es.abort || es.g.win)
  · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hInvQ
  · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
    rcases htr : es.g.inTransit P.other c with _ | r
    · simp only [htr, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInvQ
    · simp only [htr] at hmem
      rw [run_liftH_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨vrRes, h'⟩, hvr, hmem⟩ := hmem
      have hPres := vRecv_fs_preserve cka prng fs Δcka mo j es.g P (es.g.st P) c (some r) es.h
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
      · by_cases hmust : (cfg.deliverWin && es.g.mustBeCorrect maxSkip P r)
        · simp only [hmust, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
            pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩
          exact ⟨hSm,
            by dsimp only; have := hInv.table_le; have := hPres.1; omega,
            by dsimp only; have := hInv.sessions_le; have := hPres.2.1; omega,
            by dsimp only; have := hInv.fsTrans_le; have := hPres.2.2.1; omega,
            hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
        · simp only [hmust, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩
          exact ⟨hSm,
            by dsimp only; have := hInv.table_le; have := hPres.1; omega,
            by dsimp only; have := hInv.sessions_le; have := hPres.2.1; omega,
            by dsimp only; have := hInv.fsTrans_le; have := hPres.2.2.1; omega,
            hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
      · simp only [StateT.run_bind, commitE_fs_eq, pure_bind, StateT.run_modify,
          StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩
        have hst' := hPres.2.2.2 st' t' i' m' rfl
        refine ⟨hSm,
          by dsimp only; have := hInv.table_le; have := hPres.1; omega,
          by dsimp only; have := hInv.sessions_le; have := hPres.2.1; omega,
          by dsimp only; have := hInv.fsTrans_le; have := hPres.2.2.1; omega,
          fun Q => ?_, fun Q t ht => ?_⟩
        · split_ifs <;> dsimp only [SM.GameState.accept]
          · by_cases hQ : Q = P
            · subst hQ; simp only [Function.update_self]
              have := hInv.tcur_le Q; have := hst'.1; omega
            · simp only [Function.update_of_ne hQ]; exact hInvQ.tcur_le Q
          · by_cases hQ : Q = P
            · subst hQ; simp only [Function.update_self]
              have := hInv.tcur_le Q; have := hst'.1; omega
            · simp only [Function.update_of_ne hQ]; exact hInvQ.tcur_le Q
        · split_ifs at ht ⊢ <;> dsimp only [SM.GameState.accept] at ht ⊢
          · by_cases hQ : Q = P
            · subst hQ; simp only [Function.update_self] at ht ⊢; exact hst'.2 t ht
            · simp only [Function.update_of_ne hQ] at ht ⊢; exact hInv.vR_none_of_gt Q t ht
          · by_cases hQ : Q = P
            · subst hQ; simp only [Function.update_self] at ht ⊢; exact hst'.2 t ht
            · simp only [Function.update_of_ne hQ] at ht ⊢; exact hInv.vR_none_of_gt Q t ht

theorem injectE_fs_inv [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    {L B q Δ qep : ℕ} (cfg : Config M) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (es : EState (VP Γ T RSt (Option SS) (Option RS)) M (Header T × E)
      (FSState T RSt K I SS RS E))
    (arg : Party × (Header T × E))
    (hInv : FSEngineInv L B (q + 1) es) :
    ∀ res ∈ support ((injectE (hooksFS cka prng fs Δcka mo j) Δ qep cfg arg).run es),
      FSEngineInv L B q res.2 := by
  rcases arg with ⟨P, c⟩
  intro ⟨out, es'⟩ hmem
  have hInvQ : FSEngineInv L B q es := hInv.mono (Nat.le_succ q)
  have hSm := injectE_inv (hooksFS cka prng fs Δcka mo j) cfg es (P, c) hInv.sm
    (out, es') hmem
  unfold injectE abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases href : (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj Δ))
  · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hInvQ
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hmem
    rw [run_liftH_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨vrRes, h'⟩, hvr, hmem⟩ := hmem
    have hPres := vRecv_fs_preserve cka prng fs Δcka mo j es.g P (es.g.st P) c none es.h
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
    · by_cases hqep : qep + 1 < t'
      · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩
        exact ⟨hSm,
          by dsimp only; have := hInv.table_le; have := hPres.1; omega,
          by dsimp only; have := hInv.sessions_le; have := hPres.2.1; omega,
          by dsimp only; have := hInv.fsTrans_le; have := hPres.2.2.1; omega,
          hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
      · simp only [hqep, ↓reduceIte] at hmem
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

theorem corrE_fs_inv [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    {L B q : ℕ} (π : Policy) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (es : EState (VP Γ T RSt (Option SS) (Option RS)) M (Header T × E)
      (FSState T RSt K I SS RS E))
    (P : Party)
    (hInv : FSEngineInv L B (q + 1) es) :
    ∀ res ∈ support ((corrE (hooksFS cka prng fs Δcka mo j) π P).run es),
      FSEngineInv L B q res.2 := by
  intro ⟨out, es'⟩ hmem
  have hInvQ : FSEngineInv L B q es := hInv.mono (Nat.le_succ q)
  have hSm := corrE_inv (hooksFS cka prng fs Δcka mo j) π es P hInv.sm
    (out, es') hmem
  unfold corrE abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases href : (es.abort || es.g.win || !(es.g.corrAllowed P))
  · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hInvQ
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hmem
    by_cases hdoom : (π.leakDoom es.g (es.g.afterCorr P) || π.corrDoom es.g P)
    · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
        pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩
      exact ⟨hSm, hInvQ.table_le, hInvQ.sessions_le, hInvQ.fsTrans_le,
        hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
    · simp only [hdoom, Bool.false_eq_true, ↓reduceIte] at hmem
      rw [run_liftH_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨revRes, h'⟩, hrev, hmem⟩ := hmem
      have hPres := fsReveal_preserve cka prng fs Δcka mo j es.h es.g P (es.g.st P)
        (revRes, h') hrev
      rcases revRes with _ | st
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩
        exact ⟨hSm,
          by dsimp only; rw [hPres.1]; exact hInvQ.table_le,
          by dsimp only; rw [hPres.2.1]; exact hInvQ.sessions_le,
          by dsimp only; rw [hPres.2.2]; exact hInvQ.fsTrans_le,
          hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩
        exact ⟨hSm,
          by dsimp only; rw [hPres.1]; exact hInvQ.table_le,
          by dsimp only; rw [hPres.2.1]; exact hInvQ.sessions_le,
          by dsimp only; rw [hPres.2.2]; exact hInvQ.fsTrans_le,
          hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩

theorem implE_fs_inv [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [Inhabited E] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    {L B q Δ qep maxSkip : ℕ} (cfg : Config M) (π : Policy)
    (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (es : EState (VP Γ T RSt (Option SS) (Option RS)) M (Header T × E)
      (FSState T RSt K I SS RS E))
    (t : (SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hInv : FSEngineInv L B (q + 1) es) :
    ∀ res ∈ support ((implE (hooksFS cka prng fs Δcka mo j) Δ qep maxSkip cfg π (.inr t)).run es),
      FSEngineInv L B q res.2 := by
  rcases t with (((arg | arg) | arg) | arg) | P
  · exact transmitE_fs_inv cka prng fs π Δcka mo j es arg hInv
  · exact challE_fs_inv cka prng fs cfg π Δcka mo j es arg hInv
  · exact deliverE_fs_inv cka prng fs cfg Δcka mo j es arg hInv
  · exact injectE_fs_inv cka prng fs cfg Δcka mo j es arg hInv
  · exact corrE_fs_inv cka prng fs π Δcka mo j es P hInv

/-- Multi-step simulation agreement between `handlerImpl (implEC (hooksFSC ...))` and `Engine.implE (hooksFS ...)`. -/
theorem simulateQ_implEC_fs_eq
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B B_q Δcka qep : ℕ) (mo : Mode) (j : ℕ)
    (hSend : ckaSend = cka.send)
    (hRecv : ckaReceive = cka.receive)
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send)
    (heqT : eqT = (· == ·))
    (heqI : eqI = (· == ·))
    (heqM : eqM = (· == ·))
    (heqE : eqE = (· == ·))
    (hDefaultE : defaultE = default)
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hSampI : sampI = ($ᵗ I : ProbComp I))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (hFsRecvB : ∀ rs hdr e,
      (fsReceive rs hdr e).map (fun (rs', i, m) => (rs', min i B, m)) =
        fs.receive rs hdr e) :
    ∀ {α : Type}
      {oa : OracleComp (unifSpec + SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) α}
      {qAdv : ℕ},
      oa.IsQueryBoundP
        (isGameQuery (G := SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) qAdv →
      ∀ (es : EState (VP Γ T RSt (Option SS) (Option RS)) M (Header T × E)
          (FSState T RSt K I SS RS E)),
        FSEngineInv L B_q qAdv es →
        (simulateQ
          (handlerImpl (C := prngSMCodec KC Γ CCoins T I KR RSt K SS RS M E)
            (implEC (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
                (sampI := sampI) (sampK := sampK) L B Δcka mo j)
              L (2 + Δcka) qep fs.maxSkip (modeCfgEC OO mo) mo.policy .v0 .v1)) oa).run
          (esEnc vpEnc hsEnc es) =
          (Prod.map id (esEnc vpEnc hsEnc) <$>
            (simulateQ (implE (hooksFS cka prng fs Δcka mo j)
              (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy) oa).run es) ∧
        ∀ res ∈ support ((simulateQ (implE (hooksFS cka prng fs Δcka mo j)
            (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy) oa).run es),
          FSEngineInv L B_q 0 res.2 ∧ res.2.g.b = es.g.b := by
  have hHk := hooksFSC_agrees (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (prngInit := prngInit) (eqM := eqM) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC)
    cka prng fs L B Δcka mo j hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend
    heqT heqI heqE hSampCCoins hSampI hSampK hFsRecvB
  let vpE := vpTblEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
    (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
    (γvT := .base .γ) (svT := .base .sig)
    (ssvT := .opt (.base .ss)) (rsvT := .opt (.base .rs))
  have hVp : vpEnc = vpE := rfl
  intro α oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro qAdv _ es hInv
    refine ⟨by simp [simulateQ_pure, Prod.map], ?_⟩
    intro res hmem
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    exact ⟨hInv.mono (Nat.zero_le qAdv), rfl⟩
  | query_bind q mx ih =>
    intro qAdv hq es hInv
    rw [isQueryBoundP_query_bind_iff] at hq
    rw [run_simulateQ_query_bind, run_simulateQ_query_bind]
    cases q with
    | inl n =>
      have hCoinL :
          ((handlerImpl (C := prngSMCodec KC Γ CCoins T I KR RSt K SS RS M E)
            (implEC (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
                (sampI := sampI) (sampK := sampK) L B Δcka mo j) L (2 + Δcka) qep fs.maxSkip
              (modeCfgEC OO mo) mo.policy .v0 .v1)) (.inl n)).run
            (esEnc vpEnc hsEnc es) =
          (fun u => (u, esEnc vpEnc hsEnc es)) <$>
            query (spec := unifSpec + FSAEAD.spec SS RS (Header T) M E) (.inl n) := by
        simp [handlerImpl, StateT.run_lift, map_eq_bind_pure_comp]
      have hCoinR :
          (implE (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep fs.maxSkip
            mo.cfg mo.policy (.inl n)).run es =
          (fun u => (u, es)) <$>
            query (spec := unifSpec + FSAEAD.spec SS RS (Header T) M E) (.inl n) := by
        simp [implE, coinsE, StateT.run_lift, map_eq_bind_pure_comp]
      rw [hCoinL, hCoinR, bind_map_left, bind_map_left, map_bind]
      refine ⟨bind_congr fun u => (ih u (hq.2 u) es hInv).1, ?_⟩
      intro res hmem
      rw [mem_support_bind_iff] at hmem
      obtain ⟨u, _, hmem⟩ := hmem
      exact (ih u (hq.2 u) es hInv).2 res hmem
    | inr t =>
      have hpos : 0 < qAdv := hq.1.resolve_left (by simp [isGameQuery])
      obtain ⟨m, rfl⟩ : ∃ m, qAdv = m + 1 := ⟨qAdv - 1, by omega⟩
      have hqm : ∀ u, (mx u).IsQueryBoundP
          (isGameQuery (G := SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) m := by
        intro u; simpa [isGameQuery] using hq.2 u
      have hHB : FSHBounded L es.h := hInv.toFSHBounded
      have hStepL := rdec_implEC_eval hDefaultE hsEnc (FSHBounded L)
        (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L B Δcka mo j)
        (hooksFSL cka prng fs L Δcka mo j) hHk
        L (2 + Δcka) qep fs.maxSkip (modeCfgEC OO mo) mo.cfg (modeCfgEC_agrees mo)
        heqT heqM heqE mo.policy .v0 .v1
        (.cons (esEnc vpE hsEnc es)
          (.cons ((ckaSMCodec KC Γ CCoins T I KR RSt K SS RS M E).qenc t) .nil))
        es t hHB hInv.sm.toBoundedEngine (fun _ _ _ _ => trivial) rfl rfl
      rw [implE_hooksFSL_eq cka prng fs L (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy
        Δcka mo j es t hInv.vR_none_of_le_L] at hStepL
      have hStep :
          ((handlerImpl (C := prngSMCodec KC Γ CCoins T I KR RSt K SS RS M E)
            (implEC (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
                (sampI := sampI) (sampK := sampK) L B Δcka mo j) L (2 + Δcka) qep fs.maxSkip
              (modeCfgEC OO mo) mo.policy .v0 .v1)) (.inr t)).run
            (esEnc vpEnc hsEnc es) =
          Prod.map id (esEnc vpEnc hsEnc) <$>
            (implE (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep fs.maxSkip
              mo.cfg mo.policy (.inr t)).run es := by
        rw [hVp]
        dsimp only [vpE] at hStepL ⊢
        simp only [handlerImpl, StateT.run_mk, prngSMCodec, ← hStepL,
          map_eq_bind_pure_comp, Function.comp_def]
      rw [hStep, bind_map_left, map_bind]
      refine ⟨OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es₁⟩ hmem => ?_, ?_⟩
      · have hInv₁ := implE_fs_inv cka prng fs mo.cfg mo.policy Δcka mo j es t hInv (u, es₁) hmem
        exact (ih u (hqm u) es₁ hInv₁).1
      · intro res hmem
        rw [mem_support_bind_iff] at hmem
        obtain ⟨⟨u, es₁⟩, hmem₁, hmem₂⟩ := hmem
        have hInv₁ := implE_fs_inv cka prng fs mo.cfg mo.policy Δcka mo j es t hInv (u, es₁) hmem₁
        have hb₁ := implE_b_eq (hooksFS cka prng fs Δcka mo j) mo.cfg mo.policy es t (u, es₁) hmem₁
        obtain ⟨hInv₂, hb₂⟩ := (ih u (hqm u) es₁ hInv₁).2 res hmem₂
        exact ⟨hInv₂, hb₂.trans hb₁⟩

/-! ## Costed single-session FS-AEAD reductions -/

def initFSRaw [DecidableEq I]
    [SampleableType KR] [SampleableType KC] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (mo : Mode) (j : ℕ) (b : Bool) :
    TComp (FSAEAD.spec SS RS (Header T) M E)
      (EState (VP Γ T RSt (Option SS) (Option RS)) M (Header T × E)
        (FSState T RSt K I SS RS E)) := do
  let kr ← sampleT KR
  let kc ← sampleT KC
  let ((σ, k, sid), h₁) ←
    (rootFS (T := T) (SS := SS) (RS := RS) (M := M) (E := E)
      prng mo 0 lam (prng.init kr)).run {}
  let (ext, h₂) ←
    (extOf (T := T) (Sig := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E) j sid).run h₁
  let pAB := mkParties (T := T) (cka.initA kc) (cka.initB kc) σ
    (if ext then none else some (fs.initSender k))
    (if ext then none else some (fs.initReceiver k))
  return {
    g := { st := fun | .A => pAB.1 | .B => pAB.2, b := b }
    h := h₂ }

def initFSEStateC (L : ℕ) (mo : Mode) (j : ℕ) {Γ'} (bE : Expr OO Γ' .bool) :
    Comp OO II Γ' esTyFS :=
  rdsl do
    b0 ← return bE
    kr ← sample (O := OO) (I := II) CKASamp.kr ()
    kc ← sample (O := OO) (I := II) CKASamp.kc ()
    ((σ, kVal, sid), h1) ←
      rootFSC L mo fsHsEmptyE 0
        (Expr.op (O := OO) CKAOp.lamI ())
        (Expr.op (O := OO) CKAOp.prngInit kr)
    let extP := extOfE L j h1 sid
    let ext := extP.1
    let h2 := extP.2
    let pAB := mkPartiesE
      (Expr.op (O := OO) CKAOp.ckaInitA kc)
      (Expr.op (O := OO) CKAOp.ckaInitB kc)
      σ
      (if ext then none else some (Expr.op (O := OO) CKAOp.fsInitSender kVal))
      (if ext then none else some (Expr.op (O := OO) CKAOp.fsInitReceiver kVal))
    return (esMk (cGsInitE (vpT := vpTyFS) pAB.1 pAB.2 b0) h2 false)

theorem initFSEStateC_eval [DecidableEq I]
    [SampleableType KR] [SampleableType KC] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (hInitA : ckaInitA = cka.initA)
    (hInitB : ckaInitB = cka.initB)
    (hPrngInit : prngInit = prng.init)
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (heqI : eqI = (· == ·))
    (hSampKR : sampKR = ($ᵗ KR : ProbComp KR))
    (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampI : sampI = ($ᵗ I : ProbComp I))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (L : ℕ) (mo : Mode) (j : ℕ) {Γ'} (bE : Expr OO Γ' .bool) (ρ : Env Γ') :
    (initFSEStateC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L mo j bE).eval ρ =
      esEnc vpEnc hsEnc <$> initFSRaw cka prng fs lam mo j (bE.eval ρ) := by
  unfold initFSEStateC initFSRaw
  rw [eval_bind_ret]
  set b : Bool := bE.eval ρ
  set ρ₁ := Env.cons (t := (.bool : Ty S)) b ρ
  have hKR : (@Comp.sample _ _ _ OO II _ CKASamp.kr .unit).eval ρ₁ =
      (sampleT KR : TComp (FSAEAD.spec SS RS (Header T) M E) KR) := by
    simp only [Comp.eval, fsaeadHeaderAdIface, prngSamplers, ckaSamplers, hSampKR, sampleT]
    exact liftP_eq_liftM II (fun _ => rfl) ($ᵗ KR)
  rw [eval_bind, hKR, map_bind]
  refine bind_congr fun kr => ?_
  set ρ₂ := Env.cons (t := (.base .kr : Ty S)) kr ρ₁
  have hKC : (@Comp.sample _ _ _ OO II _ CKASamp.kc .unit).eval ρ₂ =
      (sampleT KC : TComp (FSAEAD.spec SS RS (Header T) M E) KC) := by
    simp only [Comp.eval, fsaeadHeaderAdIface, prngSamplers, ckaSamplers, hSampKC, sampleT]
    exact liftP_eq_liftM II (fun _ => rfl) ($ᵗ KC)
  rw [eval_bind, hKC, map_bind]
  refine bind_congr fun kc => ?_
  set ρ₃ := Env.cons (t := (.base .kc : Ty S)) kc ρ₂
  have hRoot := rootFSC_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins)
    prng hPrngUp heqI hSampI hSampK L mo fsHsEmptyE (.nat 0)
    (Expr.op (O := OO) CKAOp.lamI .unit) (Expr.op (O := OO) CKAOp.prngInit .v1)
    ρ₃ ({} : FSState T RSt K I SS RS E) rfl (Nat.zero_le L)
  have hT0 : (Expr.nat (O := OO) 0).eval ρ₃ = 0 := rfl
  have hLam : (Expr.op (O := OO) CKAOp.lamI .unit).eval ρ₃ = lam := rfl
  have hSig0 : (Expr.op (O := OO) CKAOp.prngInit .v1).eval ρ₃ = prng.init kr := by
    simp [ρ₃, ρ₂, hPrngInit, Expr.eval, Expr.v1]
  rw [hT0, hLam, hSig0] at hRoot
  rw [eval_bind, hRoot.1, bind_map_left, map_bind]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨σ, k, sid⟩, h₁⟩ hmemR => ?_
  dsimp only
  have ⟨_, hSes₁, _⟩ := hRoot.2 ((σ, k, sid), h₁) hmemR
  have hSesL₁ : h₁.sessions.length ≤ L := by
    dsimp only at hSes₁
    rw [hSes₁]
    exact Nat.zero_le L
  set ρ₄ := Env.cons
    (t := .prod (.prod (.base CKASort.sig) (.prod (.base CKASort.k) (.opt (.base CKASort.i)))) hsTy)
    ((σ, (k, sid)), hsEnc h₁) ρ₃
  have hExt := extOfE_eval_pair (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) heqI L j (.snd .v0) (.snd (.snd (.fst .v0)))
    ρ₄ h₁ rfl hSesL₁
  have hSid : (Expr.snd (.snd (.fst (Expr.v0 (O := OO))))).eval ρ₄ = sid := rfl
  rw [hSid] at hExt
  rcases hExtPair : (extOfE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    L j (.snd .v0) (.snd (.snd (.fst .v0)))).eval ρ₄ with ⟨ext, h₂_enc⟩
  rw [hExtPair] at hExt
  rw [hExt.1]
  simp only [pure_bind, map_pure]
  change (Comp.ret _).eval ρ₄ = _
  rw [eval_ret]
  set extE : Expr OO _ .bool :=
    .fst (extOfE L j (.snd .v0) (.snd (.snd (.fst .v0))))
  set h2E : Expr OO _ hsTy :=
    .snd (extOfE L j (.snd .v0) (.snd (.snd (.fst .v0))))
  set ssBE : Expr OO _ (.opt (.base .ss)) :=
    .ite extE .none (.some (Expr.op (O := OO) CKAOp.fsInitSender (.fst (.snd (.fst .v0)))))
  set rsAE : Expr OO _ (.opt (.base .rs)) :=
    .ite extE .none (.some (Expr.op (O := OO) CKAOp.fsInitReceiver (.fst (.snd (.fst .v0)))))
  set pAB := mkParties (T := T) (cka.initA kc) (cka.initB kc) σ
    (if ext then none else some (fs.initSender k))
    (if ext then none else some (fs.initReceiver k))
  have hMkP := mkPartiesE_eval (O' := OO)
    (γvT := .base .γ) (svT := .base .sig)
    (ssvT := .opt (.base .ss)) (rsvT := .opt (.base .rs))
    (Expr.op (O := OO) CKAOp.ckaInitA .v1)
    (Expr.op (O := OO) CKAOp.ckaInitB .v1)
    (.fst (.fst .v0)) ssBE rsAE ρ₄
  have hMkP' :
      (mkPartiesE (O' := OO)
        (γvT := .base .γ) (svT := .base .sig)
        (ssvT := .opt (.base .ss)) (rsvT := .opt (.base .rs))
        (Expr.op (O := OO) CKAOp.ckaInitA .v1)
        (Expr.op (O := OO) CKAOp.ckaInitB .v1)
        (.fst (.fst .v0)) ssBE rsAE).eval ρ₄ =
        (vpEnc pAB.1, vpEnc pAB.2) := by
    rw [hMkP]
    have hExtE : extE.eval ρ₄ = ext := by simp [extE, hExtPair, Expr.eval]
    simp [hExtE, ρ₄, ρ₃, ρ₂, ρ₁, hInitA, hInitB, hFsInitS, hFsInitR, ssBE, rsAE,
      pAB, fsVpEnc, Prod.map, Expr.eval, Expr.v0, Expr.v1]
  have hGs := cGsInitE_eval vpEnc (O' := OO)
    (.fst (mkPartiesE
      (Expr.op (O := OO) CKAOp.ckaInitA .v1)
      (Expr.op (O := OO) CKAOp.ckaInitB .v1)
      (.fst (.fst .v0)) ssBE rsAE))
    (.snd (mkPartiesE
      (Expr.op (O := OO) CKAOp.ckaInitA .v1)
      (Expr.op (O := OO) CKAOp.ckaInitB .v1)
      (.fst (.fst .v0)) ssBE rsAE))
    .v3 ρ₄ pAB.1 pAB.2
    (by simp [Expr.eval, hMkP']) (by simp [Expr.eval, hMkP'])
  have hh2 : h2E.eval ρ₄ = hsEnc (hsDec h₂_enc) := by
    simp [h2E, hExtPair, hExt.2.1, Expr.eval]
  simp only [esMk, pair_eval, hGs, hh2]
  rfl

theorem initFSRaw_inv [DecidableEq I]
    [SampleableType KR] [SampleableType KC] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (mo : Mode) (j : ℕ) (b : Bool)
    {L B qAdv : ℕ} (hqB : qAdv ≤ B) (hB1 : B + 1 ≤ L) (hBB : B * B ≤ L * L) :
    ∀ es₀ ∈ support (initFSRaw cka prng fs lam mo j b),
      FSEngineInv L B qAdv es₀ ∧ es₀.g.b = b := by
  intro es₀ hmem
  unfold initFSRaw at hmem
  rw [mem_support_bind_iff] at hmem; obtain ⟨kr, _, hmem⟩ := hmem
  rw [mem_support_bind_iff] at hmem; obtain ⟨kc, _, hmem⟩ := hmem
  rw [mem_support_bind_iff] at hmem; obtain ⟨⟨⟨σ, k, sid⟩, h₁⟩, hRoot, hmem⟩ := hmem
  rw [mem_support_bind_iff] at hmem; obtain ⟨⟨ext, h₂⟩, hExt, hmem⟩ := hmem
  simp only [support_pure, Set.mem_singleton_iff] at hmem
  subst hmem
  obtain ⟨hT1, hS1, hTr1⟩ := rootFS_preserve prng mo 0 lam (prng.init kr) {}
    ((σ, k, sid), h₁) hRoot
  obtain ⟨hT2, hS2, hTr2⟩ := extOf_preserve j sid h₁ (ext, h₂) hExt
  have hT_zero : ({} : FSState T RSt K I SS RS E).table.length = 0 := rfl
  have hS_zero : h₁.sessions.length = 0 := by
    dsimp only at hS1
    rw [hS1]
    rfl
  have hTr_zero : ({} : FSState T RSt K I SS RS E).fsTrans.length = 0 := rfl
  refine ⟨⟨(SMEngineInv.init _ b hB1 hBB).mono hqB,
    by dsimp only at hT1 hT2 ⊢; rw [hT2]; rw [hT_zero] at hT1; omega,
    by dsimp only at hS2 ⊢; rw [hS_zero] at hS2; omega,
    by dsimp only at hTr1 hTr2 ⊢; rw [hTr2, hTr1, hTr_zero]; omega,
    fun P => by cases P <;> simp [mkParties, hqB],
    fun P t ht => ?_⟩, rfl⟩
  cases P
  · dsimp only [mkParties] at ht ⊢
    simp [Nat.ne_of_gt ht]
  · rfl

theorem runFS_eq_bind_initFSRaw
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (Δcka qep : ℕ) (mo : Mode) (j : ℕ) (b : Bool)
    (A : SchemeAdversary Γ T RSt SS RS M CCoins E) :
    runFS cka prng fs lam Δcka qep mo j b A =
      (do
        let es₀ ← initFSRaw cka prng fs lam mo j b
        let res ←
          (simulateQ (implE (hooksFS cka prng fs Δcka mo j)
            (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy) A).run es₀
        pure (some res)) := by
  unfold runFS engRun initFS initFSRaw
  simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind]
  refine bind_congr fun _ => bind_congr fun _ =>
    bind_congr fun ⟨⟨_, _, _⟩, _⟩ => bind_congr fun ⟨_, _⟩ => rfl

/-- Costed `redFSAuth` reduction (ACD19 Lemma 11) over `prngOps`, `fsaeadHeaderAdIface`, and `prngSMCodec`. -/
def redFSAuthProg (L B Δcka qep maxSkip : ℕ) (j : ℕ) (tL : Option ℕ) (t : ℕ) :
    CostedReduction OO II
      (SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (prngSMCodec KC Γ CCoins T I KR RSt K SS RS M E)
      .unit .unit .bool .bool where
  σ := esTyFS
  init := rdsl [_] do
    es ← initFSEStateC L (raw ⟨true, tL, t⟩) j false
    return ((), es)
  handle := rdsl [es, q] do
    implEC (raw (hooksFSC L B Δcka ⟨true, tL, t⟩ j)) L (raw (2 + Δcka)) qep maxSkip
      (raw (modeCfgEC OO ⟨true, tL, t⟩)) (raw (⟨true, tL, t⟩ : Mode).policy) es q
  finish := rdsl [_, _] do
    sample (O := OO) (I := II) CKASamp.bit ()

/-- Costed `redFSPriv` reduction (ACD19 Lemma 15) over `prngOps`, `fsaeadHeaderAdIface`, and `prngSMCodec`. -/
def redFSPrivProg (L B Δcka qep maxSkip : ℕ) (tL : Option ℕ) (t : ℕ) :
    CostedReduction OO II
      (SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (prngSMCodec KC Γ CCoins T I KR RSt K SS RS M E)
      .unit .unit .bool .bool where
  σ := esTyFS
  init := rdsl [_] do
    es ← initFSEStateC L (raw ⟨false, tL, t⟩) (raw 0) false
    return ((), es)
  handle := rdsl [es, q] do
    implEC (raw (hooksFSC L B Δcka ⟨false, tL, t⟩ 0)) L (raw (2 + Δcka)) qep maxSkip
      (raw (modeCfgEC OO ⟨false, tL, t⟩)) (raw (⟨false, tL, t⟩ : Mode).policy) es q
  finish := rdsl [es, guess] do
    if privValidE L (raw (2 + Δcka)) (raw (⟨false, tL, t⟩ : Mode).policy) es then
      return guess
    else
      sample (O := OO) (I := II) CKASamp.bit ()

/-- Coin-guessing variant of `redFSPrivProg`. -/
def redFSPrivCoinProg (L B Δcka qep maxSkip : ℕ) (tL : Option ℕ) (t : ℕ) :
    CostedReduction OO II
      (SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (prngSMCodec KC Γ CCoins T I KR RSt K SS RS M E)
      .unit .unit .bool .bool where
  σ := esTyFS
  init := rdsl [_] do
    es ← initFSEStateC L (raw ⟨false, tL, t⟩) (raw 0) false
    return ((), es)
  handle := rdsl [es, q] do
    implEC (raw (hooksFSC L B Δcka ⟨false, tL, t⟩ 0)) L (raw (2 + Δcka)) qep maxSkip
      (raw (modeCfgEC OO ⟨false, tL, t⟩)) (raw (⟨false, tL, t⟩ : Mode).policy) es q
  finish := rdsl [_, _] do
    sample (O := OO) (I := II) CKASamp.bit ()

def leakDoomUniE (L Δcka t : ℕ) {Γ'}
    (g0 g1 : Expr OO Γ' (cGsTy vpTyFS)) : Expr OO Γ' .bool :=
  rdslExpr =>
    letE (raw g0, raw g1) fun (s0, s1) =>
      let ev2 :=
        anyB L (cGsLeaks s1) (fun lk => leN (nat t) lk) &&
          (pGet (cGsEpoch s0) (bool (partyEnc (Party.senderOf t))) < nat t)
      let badPre :=
        anyB L (cGsLeaks s1) (fun lk => (lk < nat t) && (nat t < lk + nat (2 + Δcka)))
      orE ev2 badPre

def corrUniEC (L Δcka t : ℕ) {Γ'}
    (es : Expr OO Γ' esTyFS) (p : Expr OO Γ' .bool) :
    Comp OO II Γ' (.prod (.opt psTy) esTyFS) :=
  rdsl do
    (es0, p0) ← return (raw es, raw p)
    let s0 := esG es0
    let refuse := orE (esAbort es0) (orE (cGsWin s0) (!(cCorrAllowedE (raw L) s0 p0)))
    if refuse then
      return (none, es0)
    else
      let s1 := cAfterCorrE (raw L) s0 p0
      if orE (leakDoomUniE (raw L) (raw Δcka) (raw t) s0 s1)
          (corrDoomE (raw (⟨false, none, t⟩ : Mode).policy) s0 p0) then
        return (none, esSetAbort es0 true)
      else
        (res, h') ← fsRevealC L (raw ⟨false, none, t⟩)
          (esH es0) s0 p0 (pGet (cGsSt s0) p0)
        match res with
        | none => return (none, esMk s0 h' true)
        | some st => return (some st, esMk s1 h' (esAbort es0))

/-- Unified `tL`-free privacy policy at challenge epoch `t`. -/
def redFsPolUni (Δcka t : ℕ) : Policy :=
  ⟨false, if 2 + Δcka ≤ t then some (t - (2 + Δcka)) else none, t⟩

def implUniEC (L B Δcka qep maxSkip t : ℕ) {Γ'}
    (es : Expr OO Γ' esTyFS)
    (q : Expr OO Γ' (ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E)) :
    Comp OO II Γ' (.prod (ckaSMR KC Γ CCoins T I KR RSt K SS RS M E) esTyFS) :=
  implEC (hooksFSC L B Δcka ⟨false, none, t⟩ 0) L (2 + Δcka) qep maxSkip
    (modeCfgEC OO ⟨false, none, t⟩) (redFsPolUni Δcka t) es q

def privValidUniE (L Δ t : ℕ) {Γ'} (esE : Expr OO Γ' esTyFS) : Expr OO Γ' .bool :=
  rdslExpr =>
    letE (raw esE) fun es0 =>
      !(esAbort es0) && validGuessE (raw Δ) (cCanonE (raw L) (nat t) (esG es0)) (nat t)

/-- Stage-2 `tL`-free `redFSPriv` reduction at challenge epoch `t`. -/
def redFSPrivUniProg (L B Δcka qep maxSkip : ℕ) (t : ℕ) :
    CostedReduction OO II
      (SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (prngSMCodec KC Γ CCoins T I KR RSt K SS RS M E)
      .unit .unit .bool .bool where
  σ := esTyFS
  init := rdsl [_] do
    es ← initFSEStateC L (raw ⟨false, none, t⟩) (raw 0) false
    return ((), es)
  handle := rdsl [es, q] do
    implUniEC L B Δcka qep maxSkip t es q
  finish := rdsl [es, guess] do
    if privValidUniE (raw L) (raw (2 + Δcka)) (raw t) es then
      return guess
    else
      sample (O := OO) (I := II) CKASamp.bit ()

/-- Coin-guessing variant of `redFSPrivUniProg`. -/
def redFSPrivUniCoinProg (L B Δcka qep maxSkip : ℕ) (t : ℕ) :
    CostedReduction OO II
      (SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (prngSMCodec KC Γ CCoins T I KR RSt K SS RS M E)
      .unit .unit .bool .bool where
  σ := esTyFS
  init := rdsl [_] do
    es ← initFSEStateC L (raw ⟨false, none, t⟩) (raw 0) false
    return ((), es)
  handle := rdsl [es, q] do
    implUniEC L B Δcka qep maxSkip t es q
  finish := rdsl [_, _] do
    sample (O := OO) (I := II) CKASamp.bit ()

/-- Wraps an `FSAEADScheme` by clamping `receive`'s output message index to `B`. -/
def fsClamp (B : ℕ) (fs : FSAEADScheme K SS RS (Header T) M E) :
    FSAEADScheme K SS RS (Header T) M E :=
  { fs with
    receive := fun rs hdr e =>
      (fs.receive rs hdr e).map fun (rs', i, m) => (rs', min i B, m) }

theorem redFSAuthProg_eval_clamp
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B B_q Δcka qep : ℕ) (j : ℕ) (tL : Option ℕ) (t : ℕ)
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
    (heqI : eqI = (· == ·))
    (heqM : eqM = (· == ·))
    (heqE : eqE = (· == ·))
    (hDefaultE : defaultE = default)
    (hSampKR : sampKR = ($ᵗ KR : ProbComp KR))
    (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hSampI : sampI = ($ᵗ I : ProbComp I))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : SchemeAdversary Γ T RSt SS RS M CCoins E) (qAdv : ℕ)
    (hA : MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q) :
    (redFSAuthProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L B Δcka qep fs.maxSkip j tL t).eval (fun _ => A) () =
      redFSAuth cka prng (fsClamp B fs) lam Δcka qep j tL t A := by
  have hA' : A.IsQueryBoundP
      (isGameQuery (G := SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) qAdv := by
    refine hA.of_imp (fun x hx => ?_)
    rcases x with _ | _ <;> simp_all [isGameQuery]
  have hBit : ∀ {Γ'} (ρ' : Env Γ'),
      (@Comp.sample _ _ _ OO II _ CKASamp.bit .unit).eval ρ' =
        (sampleT Bool : TComp (FSAEAD.spec SS RS (Header T) M E) Bool) := by
    intro Γ' ρ'
    simp only [Comp.eval, fsaeadHeaderAdIface, prngSamplers, ckaSamplers, sampleT]
    exact liftP_eq_liftM II (fun _ => rfl) ($ᵗ Bool)
  have hInit := initFSEStateC_eval (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (sampCCoins := sampCCoins)
    cka prng (fsClamp B fs) hInitA hInitB hPrngInit hPrngUp hFsInitS hFsInitR heqI
    hSampKR hSampKC hSampI hSampK L ⟨true, tL, t⟩ j (.bool false)
    (Env.cons (t := (.unit : Ty S)) () .nil)
  unfold CostedReduction.eval redFSAuthProg CostedReduction.impl redFSAuth
  dsimp only
  rw [runFS_eq_bind_initFSRaw, eval_bind, hInit]
  simp only [bind_map_left, eval_ret, Expr.eval, Expr.v0, Env.get_cons_zero,
    bind_assoc, pure_bind]
  refine OracleComp.bind_congr_of_forall_mem_support
    (initFSRaw cka prng (fsClamp B fs) lam ⟨true, tL, t⟩ j false) fun es₀ hes₀ => ?_
  have ⟨hInv₀, _⟩ := initFSRaw_inv cka prng (fsClamp B fs) lam ⟨true, tL, t⟩ j false
    hqB hB1 hBB es₀ hes₀
  have ⟨hSim, _⟩ := simulateQ_implEC_fs_eq (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (prngInit := prngInit) (fsReceive := fsReceive) (lam := lam)
    (sampKR := sampKR) (sampKC := sampKC)
    cka prng (fsClamp B fs) L B B_q Δcka qep ⟨true, tL, t⟩ j
    hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend
    heqT heqI heqM heqE hDefaultE hSampCCoins hSampI hSampK
    (fun rs hdr e => by simp [fsClamp, hFsRecv]) hA' es₀ hInv₀
  have hms : (fsClamp B fs).maxSkip = fs.maxSkip := rfl
  dsimp only [Expr.v0] at hSim
  rw [hms] at hSim
  rw [hSim, bind_map_left]
  refine bind_congr fun ⟨b', es'⟩ => ?_
  exact hBit _

theorem redFSPrivProg_eval_clamp
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B B_q Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
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
    (heqI : eqI = (· == ·))
    (heqM : eqM = (· == ·))
    (heqE : eqE = (· == ·))
    (hDefaultE : defaultE = default)
    (hSampKR : sampKR = ($ᵗ KR : ProbComp KR))
    (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hSampI : sampI = ($ᵗ I : ProbComp I))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : SchemeAdversary Γ T RSt SS RS M CCoins E) (qAdv : ℕ)
    (hA : MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q) :
    (redFSPrivProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L B Δcka qep fs.maxSkip tL t).eval (fun _ => A) () =
      redFSPriv cka prng (fsClamp B fs) lam Δcka qep tL t A := by
  have hA' : A.IsQueryBoundP
      (isGameQuery (G := SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) qAdv := by
    refine hA.of_imp (fun x hx => ?_)
    rcases x with _ | _ <;> simp_all [isGameQuery]
  have hBit : ∀ {Γ'} (ρ' : Env Γ'),
      (@Comp.sample _ _ _ OO II _ CKASamp.bit .unit).eval ρ' =
        (sampleT Bool : TComp (FSAEAD.spec SS RS (Header T) M E) Bool) := by
    intro Γ' ρ'
    simp only [Comp.eval, fsaeadHeaderAdIface, prngSamplers, ckaSamplers, sampleT]
    exact liftP_eq_liftM II (fun _ => rfl) ($ᵗ Bool)
  have hInit := initFSEStateC_eval (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (sampCCoins := sampCCoins)
    cka prng (fsClamp B fs) hInitA hInitB hPrngInit hPrngUp hFsInitS hFsInitR heqI
    hSampKR hSampKC hSampI hSampK L ⟨false, tL, t⟩ 0 (.bool false)
    (Env.cons (t := (.unit : Ty S)) () .nil)
  unfold CostedReduction.eval redFSPrivProg CostedReduction.impl redFSPriv
  dsimp only
  rw [runFS_eq_bind_initFSRaw, eval_bind, hInit]
  let vpE := vpTblEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
    (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
    (γvT := .base .γ) (svT := .base .sig)
    (ssvT := .opt (.base .ss)) (rsvT := .opt (.base .rs))
  let esT := @fsEsTy KC Γ CCoins T I KR RSt K SS RS M E
  have hVp : vpEnc = vpE := rfl
  simp only [bind_map_left, eval_ret, Expr.eval, Expr.v0, Env.get_cons_zero,
    bind_assoc, pure_bind]
  refine OracleComp.bind_congr_of_forall_mem_support
    (initFSRaw cka prng (fsClamp B fs) lam ⟨false, tL, t⟩ 0 false) fun es₀ hes₀ => ?_
  have ⟨hInv₀, _⟩ := initFSRaw_inv cka prng (fsClamp B fs) lam ⟨false, tL, t⟩ 0 false
    hqB hB1 hBB es₀ hes₀
  have ⟨hSim, hSimInv⟩ := simulateQ_implEC_fs_eq (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (prngInit := prngInit) (fsReceive := fsReceive) (lam := lam)
    (sampKR := sampKR) (sampKC := sampKC)
    cka prng (fsClamp B fs) L B B_q Δcka qep ⟨false, tL, t⟩ 0
    hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend
    heqT heqI heqM heqE hDefaultE hSampCCoins hSampI hSampK
    (fun rs hdr e => by simp [fsClamp, hFsRecv]) hA' es₀ hInv₀
  have hms : (fsClamp B fs).maxSkip = fs.maxSkip := rfl
  dsimp only [Expr.v0] at hSim
  rw [hms] at hSim
  rw [hSim, bind_map_left]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨b', es'⟩ hes' => ?_
  obtain ⟨hInv', _⟩ := hSimInv (b', es') hes'
  have hBnd' := hInv'.sm.toBoundedEngine
  rw [hVp]
  have hPV := privValidE_eval vpE hsEnc (O' := OO) L (2 + Δcka)
    (⟨false, tL, t⟩ : Mode).policy .v0
    (Env.cons (t := esT) (esEnc vpE hsEnc es')
      (Env.cons (t := (.bool : Ty S)) b' .nil))
    es' hBnd'.leaks_le rfl
  dsimp only [Prod.map, id, Expr.v0, vpE, Mode.policy] at hPV ⊢
  rw [eval_ite, hPV]
  split_ifs
  · rfl
  · exact hBit _

theorem redFSPrivCoinProg_eval_clamp
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B B_q Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
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
    (heqI : eqI = (· == ·))
    (heqM : eqM = (· == ·))
    (heqE : eqE = (· == ·))
    (hDefaultE : defaultE = default)
    (hSampKR : sampKR = ($ᵗ KR : ProbComp KR))
    (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hSampI : sampI = ($ᵗ I : ProbComp I))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : SchemeAdversary Γ T RSt SS RS M CCoins E) (qAdv : ℕ)
    (hA : MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q) :
    (redFSPrivCoinProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L B Δcka qep fs.maxSkip tL t).eval (fun _ => A) () =
      redFSPrivCoin cka prng (fsClamp B fs) lam Δcka qep tL t A := by
  have hA' : A.IsQueryBoundP
      (isGameQuery (G := SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) qAdv := by
    refine hA.of_imp (fun x hx => ?_)
    rcases x with _ | _ <;> simp_all [isGameQuery]
  have hBit : ∀ {Γ'} (ρ' : Env Γ'),
      (@Comp.sample _ _ _ OO II _ CKASamp.bit .unit).eval ρ' =
        (sampleT Bool : TComp (FSAEAD.spec SS RS (Header T) M E) Bool) := by
    intro Γ' ρ'
    simp only [Comp.eval, fsaeadHeaderAdIface, prngSamplers, ckaSamplers, sampleT]
    exact liftP_eq_liftM II (fun _ => rfl) ($ᵗ Bool)
  have hInit := initFSEStateC_eval (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (sampCCoins := sampCCoins)
    cka prng (fsClamp B fs) hInitA hInitB hPrngInit hPrngUp hFsInitS hFsInitR heqI
    hSampKR hSampKC hSampI hSampK L ⟨false, tL, t⟩ 0 (.bool false)
    (Env.cons (t := (.unit : Ty S)) () .nil)
  unfold CostedReduction.eval redFSPrivCoinProg CostedReduction.impl redFSPrivCoin
  dsimp only
  rw [runFS_eq_bind_initFSRaw, eval_bind, hInit]
  simp only [bind_map_left, eval_ret, Expr.eval, Expr.v0, Env.get_cons_zero,
    bind_assoc, pure_bind]
  refine OracleComp.bind_congr_of_forall_mem_support
    (initFSRaw cka prng (fsClamp B fs) lam ⟨false, tL, t⟩ 0 false) fun es₀ hes₀ => ?_
  have ⟨hInv₀, _⟩ := initFSRaw_inv cka prng (fsClamp B fs) lam ⟨false, tL, t⟩ 0 false
    hqB hB1 hBB es₀ hes₀
  have ⟨hSim, _⟩ := simulateQ_implEC_fs_eq (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (prngInit := prngInit) (fsReceive := fsReceive) (lam := lam)
    (sampKR := sampKR) (sampKC := sampKC)
    cka prng (fsClamp B fs) L B B_q Δcka qep ⟨false, tL, t⟩ 0
    hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend
    heqT heqI heqM heqE hDefaultE hSampCCoins hSampI hSampK
    (fun rs hdr e => by simp [fsClamp, hFsRecv]) hA' es₀ hInv₀
  have hms : (fsClamp B fs).maxSkip = fs.maxSkip := rfl
  dsimp only [Expr.v0] at hSim
  rw [hms] at hSim
  rw [hSim, bind_map_left]
  refine bind_congr fun ⟨b', es'⟩ => ?_
  exact hBit _

/-! ## Static query bounds -/

/-- Decryption query weight on `FSHdrTag`: `1` on `.dl` and `.ij`, `0` on all other tags. -/
def fsHdrDecWt : FSHdrTag → ℕ
  | .dl | .ij => 1
  | .tr | .ch | .cs | .cr => 0

@[simp] theorem lookupFC_queries (L : ℕ) (w : FSHdrTag → ℕ) {Γ'}
    (hE : Expr OO Γ' hsTy) (ikE : Expr OO Γ' (.base .i)) :
    (lookupFC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L hE ikE).queries w (fun _ => 0) = 0 := by
  simp [lookupFC, Comp.queries]

@[simp] theorem rootFSC_queries (L : ℕ) (mo : Mode) (w : FSHdrTag → ℕ) {Γ'}
    (hE : Expr OO Γ' hsTy) (tE : Expr OO Γ' .nat)
    (ikE : Expr OO Γ' (.base .i)) (σE : Expr OO Γ' (.base .sig)) :
    (rootFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L mo hE tE ikE σE).queries w (fun _ => 0) = 0 := by
  simp [rootFSC, Comp.queries]

@[simp] theorem fsStartSendC_queries (L : ℕ) (mo : Mode) (j : ℕ) (w : FSHdrTag → ℕ) {Γ'}
    (hE : Expr OO Γ' hsTy) (ctxE : Expr OO Γ' (cGsTy vpTyFS))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' (.base .γ)) (σE : Expr OO Γ' (.base .sig))
    (rE : Expr OO Γ' (.opt (.base .ccoins))) :
    (fsStartSendC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L mo j hE ctxE pE tE γE σE rE).queries
      w (fun _ => 0) = 0 := by
  simp [fsStartSendC, Comp.queries]

@[simp] theorem fsStartRecvC_queries (L : ℕ) (mo : Mode) (j : ℕ) (w : FSHdrTag → ℕ) {Γ'}
    (hE : Expr OO Γ' hsTy) (ctxE : Expr OO Γ' (cGsTy vpTyFS))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' (.base .γ)) (σE : Expr OO Γ' (.base .sig))
    (tnE : Expr OO Γ' (.base .t)) :
    (fsStartRecvC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L mo j hE ctxE pE tE γE σE tnE).queries
      w (fun _ => 0) = 0 := by
  simp [fsStartRecvC, Comp.queries]

@[simp] theorem fsFsSendC_queries (Δcka : ℕ) {Γ'}
    (hE : Expr OO Γ' hsTy) (ctxE : Expr OO Γ' (cGsTy vpTyFS))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (ssvE : Expr OO Γ' (.opt (.base .ss))) (hdrE : Expr OO Γ' hdrTy)
    (mE : Expr OO Γ' (.base .msg)) (pairE : Expr OO Γ' (.opt (.prod (.base .msg) (.base .msg)))) :
    (fsFsSendC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) Δcka hE ctxE pE tE ssvE hdrE mE pairE).queries
      (fun _ => 1) (fun _ => 0) = 2 := by
  simp [fsFsSendC, Comp.queries]

@[simp] theorem fsFsSendC_decQueries (Δcka : ℕ) {Γ'}
    (hE : Expr OO Γ' hsTy) (ctxE : Expr OO Γ' (cGsTy vpTyFS))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (ssvE : Expr OO Γ' (.opt (.base .ss))) (hdrE : Expr OO Γ' hdrTy)
    (mE : Expr OO Γ' (.base .msg)) (pairE : Expr OO Γ' (.opt (.prod (.base .msg) (.base .msg)))) :
    (fsFsSendC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) Δcka hE ctxE pE tE ssvE hdrE mE pairE).queries
      fsHdrDecWt (fun _ => 0) = 0 := by
  simp [fsFsSendC, fsHdrDecWt, Comp.queries]

@[simp] theorem fsFsRecvC_queries (L B : ℕ) {Γ'}
    (hE : Expr OO Γ' hsTy) (ctxE : Expr OO Γ' (cGsTy vpTyFS))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (rsvE : Expr OO Γ' (.opt (.base .rs))) (hdrE : Expr OO Γ' hdrTy)
    (eE : Expr OO Γ' (.base .ct)) (recE : Expr OO Γ' (.opt cRecTy)) :
    (fsFsRecvC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B hE ctxE pE tE rsvE hdrE eE recE).queries
      (fun _ => 1) (fun _ => 0) = 1 := by
  simp [fsFsRecvC, Comp.queries]

@[simp] theorem fsFsRecvC_decQueries (L B : ℕ) {Γ'}
    (hE : Expr OO Γ' hsTy) (ctxE : Expr OO Γ' (cGsTy vpTyFS))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (rsvE : Expr OO Γ' (.opt (.base .rs))) (hdrE : Expr OO Γ' hdrTy)
    (eE : Expr OO Γ' (.base .ct)) (recE : Expr OO Γ' (.opt cRecTy)) :
    (fsFsRecvC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B hE ctxE pE tE rsvE hdrE eE recE).queries
      fsHdrDecWt (fun _ => 0) = 1 := by
  simp [fsFsRecvC, fsHdrDecWt, Comp.queries]

@[simp] theorem fsCommitC_queries (w : FSHdrTag → ℕ) {Γ'}
    (hE : Expr OO Γ' hsTy) (ctxE : Expr OO Γ' (cGsTy vpTyFS))
    (pE : Expr OO Γ' .bool) (oldE newE : Expr OO Γ' vpTyFS) :
    (fsCommitC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) hE ctxE pE oldE newE).queries w (fun _ => 0) = 0 := by
  simp [fsCommitC, Comp.queries]

@[simp] theorem fsRevealC_queries (L : ℕ) (mo : Mode) {Γ'}
    (hE : Expr OO Γ' hsTy) (ctxE : Expr OO Γ' (cGsTy vpTyFS))
    (pE : Expr OO Γ' .bool) (vpE : Expr OO Γ' vpTyFS) :
    (fsRevealC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L mo hE ctxE pE vpE).queries
      (fun _ => 1) (fun _ => 0) = 2 := by
  simp [fsRevealC, Comp.queries]

@[simp] theorem fsRevealC_decQueries (L : ℕ) (mo : Mode) {Γ'}
    (hE : Expr OO Γ' hsTy) (ctxE : Expr OO Γ' (cGsTy vpTyFS))
    (pE : Expr OO Γ' .bool) (vpE : Expr OO Γ' vpTyFS) :
    (fsRevealC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L mo hE ctxE pE vpE).queries
      fsHdrDecWt (fun _ => 0) = 0 := by
  simp [fsRevealC, fsHdrDecWt, Comp.queries]

@[simp] theorem implEC_hooksFSC_queries (L B Δcka qep maxSkip : ℕ) (mo : Mode) (j : ℕ) {Γ'}
    (es : Expr OO Γ' esTyFS)
    (q : Expr OO Γ' (ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E)) :
    (implEC (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δcka mo j)
      L (2 + Δcka) qep maxSkip (modeCfgEC OO mo) mo.policy es q).queries
      (fun _ => 1) (fun _ => 0) = 2 := by
  simp [implEC, transmitEC, challEC, deliverEC, injectEC, corrEC,
    vSendC, vSendStep1C, vRecvC, vRecvStep1C, commitEC, hooksFSC, Comp.queries]

@[simp] theorem implEC_hooksFSC_decQueries (L B Δcka qep maxSkip : ℕ) (mo : Mode) (j : ℕ) {Γ'}
    (es : Expr OO Γ' esTyFS)
    (q : Expr OO Γ' (ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E)) :
    (implEC (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δcka mo j)
      L (2 + Δcka) qep maxSkip (modeCfgEC OO mo) mo.policy es q).queries
      fsHdrDecWt (fun _ => 0) = 1 := by
  simp [implEC, transmitEC, challEC, deliverEC, injectEC, corrEC,
    vSendC, vSendStep1C, vRecvC, vRecvStep1C, commitEC, hooksFSC, Comp.queries]

@[simp] theorem initFSEStateC_queries (L : ℕ) (mo : Mode) (j : ℕ) (w : FSHdrTag → ℕ)
    {Γ'} (bE : Expr OO Γ' .bool) :
    (initFSEStateC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L mo j bE).queries w (fun _ => 0) = 0 := by
  simp [initFSEStateC, Comp.queries]

@[simp] theorem redFSAuthProg_totalQueries (L B Δcka qep maxSkip : ℕ) (j : ℕ)
    (tL : Option ℕ) (t q : ℕ) :
    (redFSAuthProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L B Δcka qep maxSkip j tL t).totalQueries (fun _ => 1) (fun _ => 0) q = q * 2 := by
  simp [CostedReduction.totalQueries, redFSAuthProg, Comp.queries]

@[simp] theorem redFSPrivProg_totalQueries (L B Δcka qep maxSkip : ℕ)
    (tL : Option ℕ) (t q : ℕ) :
    (redFSPrivProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L B Δcka qep maxSkip tL t).totalQueries (fun _ => 1) (fun _ => 0) q = q * 2 := by
  simp [CostedReduction.totalQueries, redFSPrivProg, Comp.queries]

@[simp] theorem redFSPrivCoinProg_totalQueries (L B Δcka qep maxSkip : ℕ)
    (tL : Option ℕ) (t q : ℕ) :
    (redFSPrivCoinProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L B Δcka qep maxSkip tL t).totalQueries (fun _ => 1) (fun _ => 0) q = q * 2 := by
  simp [CostedReduction.totalQueries, redFSPrivCoinProg, Comp.queries]

/-! ## Static cost characterizations -/

theorem redFSAuthProg_totalCost (L B Δcka qep maxSkip : ℕ) (j : ℕ) (tL : Option ℕ) (t q : ℕ) :
    (redFSAuthProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
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
        q * ((implEC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
          (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (I' := II)
          (Γ' := [esTyFS, ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E])
          (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
            (sampI := sampI) (sampK := sampK) L B Δcka ⟨true, tL, t⟩ j)
          L (2 + Δcka) qep maxSkip (modeCfgEC OO ⟨true, tL, t⟩)
          (⟨true, tL, t⟩ : Mode).policy .v0 .v1).cost + 12) := by
  simp only [CostedReduction.totalCost, redFSAuthProg, prngSMCodec, ckaSMCodec, fsaeadHeaderAdIface, prngSamplers,
    ckaSamplers, Comp.cost, Expr.cost]
  have hV0 : (Expr.v0 : Expr OO [esTyFS, .unit] esTyFS).cost = 1 := rfl
  rw [hV0, max_eq_right (by omega)]
  omega

theorem redFSPrivProg_totalCost (L B Δcka qep maxSkip : ℕ) (tL : Option ℕ) (t q : ℕ) :
    (redFSPrivProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L B Δcka qep maxSkip tL t).totalCost q =
      (initFSEStateC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L ⟨false, tL, t⟩ 0 (.bool false : Expr OO [.unit] .bool)).cost + 8 +
        q * ((implEC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
          (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (I' := II)
          (Γ' := [esTyFS, ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E])
          (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
            (sampI := sampI) (sampK := sampK) L B Δcka ⟨false, tL, t⟩ 0)
          L (2 + Δcka) qep maxSkip (modeCfgEC OO ⟨false, tL, t⟩)
          (⟨false, tL, t⟩ : Mode).policy .v0 .v1).cost + 12) +
        (privValidE (O' := OO) L (2 + Δcka) (⟨false, tL, t⟩ : Mode).policy
          (Expr.v0 : Expr OO [esTyFS, .bool] esTyFS)).cost := by
  simp only [CostedReduction.totalCost, redFSPrivProg, prngSMCodec, ckaSMCodec, fsaeadHeaderAdIface, prngSamplers,
    ckaSamplers, Comp.cost, Expr.cost]
  have hV0 : (Expr.v0 : Expr OO [esTyFS, .unit] esTyFS).cost = 1 := rfl
  have hV1 : (Expr.v1 : Expr OO [esTyFS, .bool] .bool).cost = 1 := rfl
  rw [hV0, hV1, max_eq_right (by omega), max_eq_right (by omega)]
  omega

theorem redFSPrivCoinProg_totalCost (L B Δcka qep maxSkip : ℕ) (tL : Option ℕ) (t q : ℕ) :
    (redFSPrivCoinProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L B Δcka qep maxSkip tL t).totalCost q =
      (initFSEStateC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L ⟨false, tL, t⟩ 0 (.bool false : Expr OO [.unit] .bool)).cost + 7 +
        q * ((implEC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
          (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (I' := II)
          (Γ' := [esTyFS, ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E])
          (hooksFSC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
            (sampI := sampI) (sampK := sampK) L B Δcka ⟨false, tL, t⟩ 0)
          L (2 + Δcka) qep maxSkip (modeCfgEC OO ⟨false, tL, t⟩)
          (⟨false, tL, t⟩ : Mode).policy .v0 .v1).cost + 12) := by
  simp only [CostedReduction.totalCost, redFSPrivCoinProg, prngSMCodec, ckaSMCodec, fsaeadHeaderAdIface, prngSamplers,
    ckaSamplers, Comp.cost, Expr.cost]
  have hV0 : (Expr.v0 : Expr OO [esTyFS, .unit] esTyFS).cost = 1 := rfl
  rw [hV0, max_eq_right (by omega)]
  omega

end HooksFSEval

section FromAEADPRG

variable {MK C : Type}

def FSVROkStep (maxSkip k : ℕ) :
    Option (FSAEAD.RatchetReceiverState K MK) → Prop
  | none => True
  | some rs => RSReach maxSkip k rs

theorem FSVROkStep.mono {maxSkip k k' : ℕ}
    {v : Option (FSAEAD.RatchetReceiverState K MK)}
    (hle : k ≤ k') (hv : FSVROkStep maxSkip k v) : FSVROkStep maxSkip k' v := by
  cases v with
  | none => trivial
  | some rs => exact RSReach.mono hle hv

theorem fsClamp_receive_fromAEADPRG
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip B k : ℕ)
    (hB : (k + 1) * (maxSkip + 1) ≤ B)
    {rs : FSAEAD.RatchetReceiverState K MK} (hrs : RSReach maxSkip k rs)
    (hdr : Header T) (e : ℕ × C) :
    (fsClamp (T := T) B (FSAEAD.fromAEADPRG ae G maxSkip)).receive rs hdr e =
      (FSAEAD.fromAEADPRG ae G maxSkip).receive rs hdr e := by
  dsimp only [fsClamp]
  rcases hrec : (FSAEAD.fromAEADPRG ae G maxSkip).receive rs hdr e with _ | ⟨rs', i, m⟩
  · rfl
  · have hi := (RSReach.receive ae G maxSkip k hrs hrec).1
    simp [Nat.min_eq_left (hi.trans hB)]

theorem lookupF_ext [DecidableEq I] [SampleableType K] (ik : I)
    (h : FSState T RSt K I SS RS E) :
    ∀ res ∈ support
      ((lookupF (T := T) (Sig := RSt) (SS := SS) (RS := RS) (M := M) (E := E) ik).run h),
      res.2.ext = h.ext := by
  intro res hmem
  unfold lookupF at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  rcases hlk : h.table.lookup ik with _ | k
  · simp only [hlk, StateT.run_bind, StateT.run_lift, StateT.run_modify, StateT.run_pure,
      bind_assoc, pure_bind, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hmem
    obtain ⟨_, _, rfl⟩ := hmem; rfl
  · simp only [hlk, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; rfl

theorem isExt_ext [DecidableEq I] (j : ℕ) (ik : I)
    (h : FSState T RSt K I SS RS E) :
    ∀ res ∈ support
      ((isExt (T := T) (Sig := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
          j ik).run h),
      res.2.ext = h.ext := by
  intro res hmem
  unfold isExt at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases hm : ik ∈ h.sessions
  · simp only [hm, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; rfl
  · simp only [hm, ↓reduceIte, StateT.run_bind, StateT.run_set, pure_bind] at hmem
    subst hmem; rfl

theorem extOf_ext [DecidableEq I] (j : ℕ) (sid : Option I)
    (h : FSState T RSt K I SS RS E) :
    ∀ res ∈ support
      ((extOf (T := T) (Sig := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
          j sid).run h),
      res.2.ext = h.ext := by
  rcases sid with _ | ik
  · intro res hmem
    simp only [extOf, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; rfl
  · exact isExt_ext j ik h

theorem rootFS_ext [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR RSt I K) (mo : Mode) (t : ℕ) (ik : I) (σ : RSt)
    (h : FSState T RSt K I SS RS E) :
    ∀ res ∈ support
      ((rootFS (T := T) (SS := SS) (RS := RS) (M := M) (E := E) prng mo t ik σ).run h),
      res.2.ext = h.ext := by
  intro res hmem
  unfold rootFS at hmem
  by_cases hlt : mo.tStar < t
  · simp only [hlt, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; rfl
  · simp only [hlt, ↓reduceIte] at hmem
    by_cases heq : t = mo.tStar
    · have heqIf : (t = mo.tStar) ↔ True := by simp [heq]
      simp only [heqIf, ↓reduceIte] at hmem
      by_cases hc : (mo.tL.isSome && decide (t = mo.tH)) = true
      · simp only [hc, ↓reduceIte, StateT.run_bind, StateT.run_lift,
          StateT.run_pure, bind_assoc, pure_bind, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at hmem
        obtain ⟨_, _, _, _, rfl⟩ := hmem; rfl
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_pure,
          mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hmem
        obtain ⟨⟨k, h₁⟩, hLk, rfl⟩ := hmem
        exact lookupF_ext ik h (k, h₁) hLk
    · simp only [heq, ↓reduceIte] at hmem
      by_cases hc : (mo.tL.isSome && decide (t = mo.tH)) = true
      · simp only [hc, ↓reduceIte, StateT.run_bind, StateT.run_lift,
          StateT.run_pure, bind_assoc, pure_bind, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at hmem
        obtain ⟨_, _, rfl⟩ := hmem; rfl
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at hmem
        subst hmem; rfl

theorem fsStartSend_ext [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (ctx : Ctx Γ T RSt (Option SS) (Option RS) M E) (P : Party)
    (t : ℕ) (γ : Γ) (σ : RSt) (r : Option CCoins)
    (h : FSState T RSt K I SS RS E) :
    ∀ res ∈ support (((hooksFS cka prng fs Δcka mo j).startSend ctx P t γ σ r).run h),
      res.2.ext = h.ext := by
  intro res hmem
  unfold hooksFS at hmem; dsimp only at hmem
  rcases r with _ | coins <;>
    simp only [StateT.run_bind, StateT.run_lift, StateT.run_modify, StateT.run_pure,
      bind_assoc, pure_bind, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hmem
  · obtain ⟨coins, _, ⟨⟨σ', k, sid⟩, h₁⟩, hRoot, ⟨ext, h₂⟩, hExt, rfl⟩ := hmem
    exact (extOf_ext j sid h₁ (ext, h₂) hExt).trans
      (rootFS_ext prng mo t (cka.send γ coins).2.2 σ h ((σ', k, sid), h₁) hRoot)
  · obtain ⟨⟨⟨σ', k, sid⟩, h₁⟩, hRoot, ⟨ext, h₂⟩, hExt, rfl⟩ := hmem
    exact (extOf_ext j sid h₁ (ext, h₂) hExt).trans
      (rootFS_ext prng mo t (cka.send γ coins).2.2 σ h ((σ', k, sid), h₁) hRoot)

theorem fsStartRecv_ext [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (ctx : Ctx Γ T RSt (Option SS) (Option RS) M E) (P : Party)
    (t : ℕ) (γ : Γ) (σ : RSt) (Tn : T)
    (h : FSState T RSt K I SS RS E) :
    ∀ res ∈ support (((hooksFS cka prng fs Δcka mo j).startRecv ctx P t γ σ Tn).run h),
      res.2.ext = h.ext := by
  intro res hmem
  unfold hooksFS at hmem; dsimp only at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  have hNonHon :
      (res ∈ support ((if (mo.auth && decide (t = mo.tStar)) = true then
          if (mo.tL.isSome && decide (mo.tStar = mo.tH)) = true then pure none
          else do
            let k' ← lookupF (cka.receive γ Tn).2
            let ext ← isExt j (cka.receive γ Tn).2
            pure (some (some ((cka.receive γ Tn).1, (prng.up σ (cka.receive γ Tn).2).1,
              if ext = true then none else some (fs.initReceiver k'))))
        else pure (some none) :
        HM (FSAEAD.spec SS RS (Header T) M E) (FSState T RSt K I SS RS E) _).run h)) →
      res.2.ext = h.ext := by
    intro hmem'
    by_cases hc1 : (mo.auth && decide (t = mo.tStar)) = true
    · simp only [hc1, ↓reduceIte] at hmem'
      by_cases hc2 : (mo.tL.isSome && decide (mo.tStar = mo.tH)) = true
      · simp only [hc2, ↓reduceIte, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at hmem'
        subst hmem'; rfl
      · simp only [hc2, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_pure,
          mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hmem'
        obtain ⟨⟨k', h₁⟩, hLk, ⟨ext, h₂⟩, hExt, rfl⟩ := hmem'
        exact (isExt_ext j (cka.receive γ Tn).2 h₁ (ext, h₂) hExt).trans
          (lookupF_ext (cka.receive γ Tn).2 h (k', h₁) hLk)
    · simp only [hc1, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hmem'
      subst hmem'; rfl
  rcases hcache : h.cache t with _ | ⟨Tc, σc, k, ext⟩
  · simp only [hcache] at hmem; exact hNonHon hmem
  · by_cases hTc : Tc = Tn
    · simp only [hcache, hTc, ↓reduceIte, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hmem
      subst hmem; rfl
    · simp only [hcache, hTc, ↓reduceIte] at hmem; exact hNonHon hmem

theorem fsFsSend_ext_snd [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (ctx : Ctx Γ T RSt (Option SS) (Option RS) M E) (P : Party)
    (t : ℕ) (ssv : Option SS) (hdr : Header T) (m : M) (pair : Option (M × M))
    (h : FSState T RSt K I SS RS E) :
    ∀ res ∈ support (((hooksFS cka prng fs Δcka mo j).fsSend ctx P t ssv hdr m pair).run h),
      res.2.ext.map Prod.snd = h.ext.map Prod.snd := by
  intro res hmem
  unfold hooksFS at hmem; dsimp only at hmem
  rcases ssv with _ | ss
  · simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    rcases hext : h.ext with _ | ⟨ss, rs⟩
    · simp only [hext] at hmem
      have hTail : ∀ (h₁ : FSState T RSt K I SS RS E), h₁.ext = none →
          res ∈ support
            ((do
              let e? ← match pair with
                | some (m₀, m₁) =>
                  liftF (FSAEAD.challengeQuery (SenderState := SS) (ReceiverState := RS)
                    hdr m₀ m₁)
                | none =>
                  liftF (FSAEAD.transmitQuery (SenderState := SS) (ReceiverState := RS)
                    hdr m)
              match e? with
              | none => pure none
              | some e =>
                modify fun s => { s with fsCount := s.fsCount + 1,
                                         fsTrans := (s.fsCount + 1, hdr, e) :: s.fsTrans }
                pure (some (none, e)) :
              HM (FSAEAD.spec SS RS (Header T) M E) (FSState T RSt K I SS RS E) _).run h₁) →
          res.2.ext.map Prod.snd = none := by
        intro h₁ hh₁ hmem'
        rcases pair with _ | ⟨m₀, m₁⟩ <;>
          (simp only [liftF, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
             mem_support_bind_iff] at hmem';
           obtain ⟨e?, _, hmem'⟩ := hmem';
           rcases e? with _ | e <;>
             (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                support_pure, Set.mem_singleton_iff] at hmem';
              subst hmem'; simp [hh₁]))
      by_cases hc : (!ctx.safeCh (2 + Δcka) P && !h.fsSCorr) = true
      · simp only [hc, ↓reduceIte, liftF, StateT.run_bind, StateT.run_lift,
          bind_assoc, pure_bind, mem_support_bind_iff] at hmem
        obtain ⟨cs?, _, hmem⟩ := hmem
        rcases cs? with _ | ss'
        · simp only [Bool.not_false, ↓reduceIte, StateT.run_pure,
            support_pure, Set.mem_singleton_iff] at hmem
          subst hmem; simp [hext]
        · simp only [StateT.run_bind, StateT.run_modify, pure_bind,
            Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hmem
          exact hTail { h with fsSCorr := true } hext hmem
      · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hmem
        exact hTail h hext hmem
    · simp only [hext, StateT.run_bind, StateT.run_set, pure_bind] at hmem
      subst hmem; rfl
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; rfl

theorem fsFsRecv_ext_snd [DecidableEq T] [DecidableEq I] [DecidableEq C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip k Δcka : ℕ) (mo : Mode) (j : ℕ)
    (ctx : Ctx Γ T RSt (Option (FSAEAD.RatchetSenderState K))
      (Option (FSAEAD.RatchetReceiverState K MK)) M (ℕ × C))
    (P : Party) (t : ℕ) (rsv : Option (FSAEAD.RatchetReceiverState K MK))
    (hdr : Header T) (e : ℕ × C) (rec_ : Option (Record M (Header T × (ℕ × C))))
    (h : FSState T RSt K I (FSAEAD.RatchetSenderState K)
      (FSAEAD.RatchetReceiverState K MK) (ℕ × C))
    (hExt : FSVROkStep maxSkip k (h.ext.map Prod.snd)) :
    ∀ res ∈ support (((hooksFS cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j).fsRecv
        ctx P t rsv hdr e rec_).run h),
      FSVROkStep maxSkip (k + 1) (res.2.ext.map Prod.snd) := by
  intro res hmem
  unfold hooksFS at hmem; dsimp only at hmem
  rcases rsv with _ | rs
  · simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    rcases hext : h.ext with _ | ⟨ss, rs⟩
    · simp only [hext] at hmem
      split_ifs at hmem <;>
        (simp only [liftF, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
           mem_support_bind_iff] at hmem;
         obtain ⟨qres, _, hmem⟩ := hmem;
         rcases qres with _ | (_ | ⟨i, mo'⟩);
         · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem;
           subst hmem; simp [hext, FSVROkStep];
         · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem;
           subst hmem; simp [hext, FSVROkStep];
         · simp only [StateT.run_bind, StateT.run_modify, pure_bind] at hmem;
           rcases mo' with _ | m;
           · rcases rec_ with _ | r <;>
               (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem;
                subst hmem; simp [hext, FSVROkStep]);
           · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem;
             subst hmem; simp [hext, FSVROkStep])
    · simp only [hext] at hmem hExt
      rcases hrc : (FSAEAD.fromAEADPRG ae G maxSkip).receive rs hdr e with _ | ⟨rs', i, m⟩
      · simp only [hrc, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; simp [hext, FSVROkStep]; exact hExt.mono (Nat.le_succ k)
      · simp only [hrc, StateT.run_bind, StateT.run_set, StateT.run_pure,
          pure_bind, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem
        exact (RSReach.receive ae G maxSkip k hExt hrc).2
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    exact hExt.mono (Nat.le_succ k)

theorem hooksFS_vrInv_fromAEADPRG [DecidableEq T] [DecidableEq I] [DecidableEq C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip Δcka : ℕ) (mo : Mode) (j : ℕ) :
    HooksVRInv (FSVROkStep (K := K) (MK := MK) maxSkip)
      (hooksFS cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j) where
  mono hle hv := hv.mono hle
  startRecv_step ctx P t γ σ Tn h res hmem γ' σ' rsv hEq := by
    rcases res with ⟨ans, h'⟩
    dsimp only at hEq
    subst hEq
    unfold hooksFS at hmem; dsimp only at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    have hNonHon :
        (some (some (γ', σ', rsv)), h') ∈ support
          ((if (mo.auth && decide (t = mo.tStar)) = true then
              if (mo.tL.isSome && decide (mo.tStar = mo.tH)) = true then pure none
              else do
                let k' ← lookupF (cka.receive γ Tn).2
                let ext ← isExt j (cka.receive γ Tn).2
                pure (some (some ((cka.receive γ Tn).1, (prng.up σ (cka.receive γ Tn).2).1,
                  if ext = true then none
                  else some ((FSAEAD.fromAEADPRG ae G maxSkip).initReceiver k'))))
            else pure (some none) :
            HM (FSAEAD.spec _ _ (Header T) M (ℕ × C)) _ _).run h) →
        FSVROkStep maxSkip 0 rsv := by
      intro hmem'
      by_cases hc1 : (mo.auth && decide (t = mo.tStar)) = true
      · simp only [hc1, ↓reduceIte] at hmem'
        by_cases hc2 : (mo.tL.isSome && decide (mo.tStar = mo.tH)) = true
        · simp [hc2] at hmem'
        · simp only [hc2, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_pure,
            mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
            Option.some.injEq] at hmem'
          obtain ⟨⟨k', h₁⟩, _, ⟨ext, h₂⟩, _, ⟨_, _, hrsv⟩, _⟩ := hmem'
          subst hrsv
          cases ext <;> [exact RSReach.init ae G maxSkip k'; trivial]
      · simp [hc1] at hmem'
    rcases hcache : h.cache t with _ | ⟨Tc, σc, k, ext⟩
    · simp only [hcache] at hmem; exact hNonHon hmem
    · by_cases hTc : Tc = Tn
      · simp only [hcache, hTc, ↓reduceIte, StateT.run_pure, support_pure,
          Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at hmem
        rcases hmem with ⟨⟨_, _, hrsv⟩, _⟩
        subst hrsv
        cases ext <;> [exact RSReach.init ae G maxSkip k; trivial]
      · simp only [hcache, hTc, ↓reduceIte] at hmem; exact hNonHon hmem
  fsRecv_step ctx P t rsv hdr e rec_ h res hVR hmem v' i' m' hEq := by
    rcases res with ⟨ans, h'⟩
    dsimp only at hEq
    subst hEq
    unfold hooksFS at hmem; dsimp only at hmem
    rcases rsv with _ | rs
    · simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
      rcases hext : h.ext with _ | ⟨ss, rs⟩
      · simp only [hext] at hmem
        split_ifs at hmem <;>
          (simp only [liftF, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
             mem_support_bind_iff] at hmem;
           obtain ⟨qres, _, hmem⟩ := hmem;
           rcases qres with _ | (_ | ⟨i, mo'⟩);
           · simp at hmem;
           · simp at hmem;
           · simp only [StateT.run_bind, StateT.run_modify, pure_bind] at hmem;
             rcases mo' with _ | m;
             · rcases rec_ with _ | r;
               · simp at hmem;
               · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
                   Prod.mk.injEq, Option.some.injEq] at hmem;
                 rcases hmem with ⟨⟨rfl, _, _⟩, _⟩; trivial;
             · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
                 Prod.mk.injEq, Option.some.injEq] at hmem;
               rcases hmem with ⟨⟨rfl, _, _⟩, _⟩; trivial)
      · simp only [hext] at hmem
        rcases hrc : (FSAEAD.fromAEADPRG ae G maxSkip).receive rs hdr e with _ | ⟨rs', i, m⟩
        · simp [hrc] at hmem
        · simp only [hrc, StateT.run_bind, StateT.run_set, pure_bind] at hmem
          rcases hmem with ⟨⟨rfl, _, _⟩, _⟩; trivial
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq, Option.some.injEq] at hmem
      rcases hmem with ⟨hmap, _⟩
      rcases hrc : (FSAEAD.fromAEADPRG ae G maxSkip).receive rs hdr e with _ | ⟨rs', i, m⟩
      · simp [hrc] at hmap
      · simp only [hrc, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hmap
        rcases hmap with ⟨rfl, rfl, rfl⟩
        exact (RSReach.receive ae G maxSkip _ hVR hrc).2
  commit_vR _ _ _ _ _ _ hmem _ hEq := by
    simp only [hooksFS, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; cases hEq; rfl

theorem initFSRaw_vrInv_fromAEADPRG [DecidableEq I]
    [SampleableType KR] [SampleableType KC] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip : ℕ)
    (lam : I) (mo : Mode) (j : ℕ) (b : Bool) (B_q qAdv : ℕ) :
    ∀ es₀ ∈ support (initFSRaw cka prng (FSAEAD.fromAEADPRG ae G maxSkip) lam mo j b),
      SMVRInv (FSVROkStep maxSkip) B_q qAdv es₀.g ∧ es₀.h.ext = none := by
  intro es₀ hmem
  unfold initFSRaw at hmem
  rw [mem_support_bind_iff] at hmem; obtain ⟨kr, _, hmem⟩ := hmem
  rw [mem_support_bind_iff] at hmem; obtain ⟨kc, _, hmem⟩ := hmem
  rw [mem_support_bind_iff] at hmem; obtain ⟨⟨⟨σ, k, sid⟩, h₁⟩, hRoot, hmem⟩ := hmem
  rw [mem_support_bind_iff] at hmem; obtain ⟨⟨ext, h₂⟩, hExt, hmem⟩ := hmem
  simp only [support_pure, Set.mem_singleton_iff] at hmem
  subst hmem
  have hext₁ := rootFS_ext prng mo 0 lam (prng.init kr) {} ((σ, k, sid), h₁) hRoot
  have hext₂ := extOf_ext j sid h₁ (ext, h₂) hExt
  refine ⟨fun P t v hv => ?_, hext₂.trans hext₁⟩
  cases P <;> simp only [mkParties] at hv
  · by_cases ht0 : t = 0
    · simp only [ht0, ↓reduceIte, Option.some.injEq] at hv
      subst hv
      cases ext <;> [exact (RSReach.init ae G maxSkip k).mono (Nat.zero_le _); trivial]
    · simp [ht0] at hv
  · cases hv

theorem hooksFS_fsRecv_fsClamp_eq [DecidableEq T] [DecidableEq I] [DecidableEq C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip B k Δcka : ℕ) (mo : Mode) (j : ℕ)
    (hB : (k + 1) * (maxSkip + 1) ≤ B)
    (ctx : Ctx Γ T RSt (Option (FSAEAD.RatchetSenderState K))
      (Option (FSAEAD.RatchetReceiverState K MK)) M (ℕ × C))
    (P : Party) (t : ℕ) (rsv : Option (FSAEAD.RatchetReceiverState K MK))
    (hdr : Header T) (e : ℕ × C) (rec_ : Option (Record M (Header T × (ℕ × C))))
    (h : FSState T RSt K I (FSAEAD.RatchetSenderState K)
      (FSAEAD.RatchetReceiverState K MK) (ℕ × C))
    (hVR : FSVROkStep maxSkip k rsv)
    (hExt : FSVROkStep maxSkip k (h.ext.map Prod.snd)) :
    ((hooksFS cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip)) Δcka mo j).fsRecv
        ctx P t rsv hdr e rec_).run h =
      ((hooksFS cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j).fsRecv
        ctx P t rsv hdr e rec_).run h := by
  dsimp only [hooksFS]
  rcases rsv with _ | rs
  · simp only [StateT.run_bind, StateT.run_get, pure_bind]
    rcases hext : h.ext with _ | ⟨ss, rs⟩
    · rfl
    · rw [hext] at hExt
      dsimp only [Option.map] at hExt ⊢
      rw [fsClamp_receive_fromAEADPRG ae G maxSkip B k hB hExt hdr e]
  · dsimp only
    rw [fsClamp_receive_fromAEADPRG ae G maxSkip B k hB hVR hdr e]

theorem vRecvStep1_hooksFS_state [DecidableEq T] [DecidableEq I] [DecidableEq C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip k Δcka : ℕ) (mo : Mode) (j : ℕ)
    (ctx : Ctx Γ T RSt (Option (FSAEAD.RatchetSenderState K))
      (Option (FSAEAD.RatchetReceiverState K MK)) M (ℕ × C))
    (P : Party)
    (s : VP Γ T RSt (Option (FSAEAD.RatchetSenderState K))
      (Option (FSAEAD.RatchetReceiverState K MK)))
    (c : Header T × (ℕ × C))
    (h : FSState T RSt K I (FSAEAD.RatchetSenderState K)
      (FSAEAD.RatchetReceiverState K MK) (ℕ × C))
    (hVR : ∀ t v, s.vR t = some v → FSVROkStep maxSkip k v) :
    ∀ res ∈ support
      ((vRecvStep1 (hooksFS cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j)
          ctx P s c).run h),
      res.2.ext = h.ext ∧
      (∀ s₁, res.1 = some (some s₁) → ∀ t v, s₁.vR t = some v → FSVROkStep maxSkip k v) := by
  intro ⟨s₁?, h₁⟩ hmem
  unfold vRecvStep1 at hmem
  by_cases ht : c.1.1 = s.tcur + 1
  · simp only [ht, ↓reduceIte] at hmem
    rcases hTn : c.1.2 with _ | Tn
    · simp only [hTn, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩
      exact ⟨rfl, fun _ h => by cases h⟩
    · simp only [hTn, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨srRes, h'⟩, hsr, hmem⟩ := hmem
      have hext' := fsStartRecv_ext cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j
        ctx P (s.tcur + 1) s.γ s.root Tn h (srRes, h') hsr
      rcases srRes with _ | _ | ⟨γ', σ', rs⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩; exact ⟨hext', fun _ h => by cases h⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩; exact ⟨hext', fun _ h => by cases h⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩
        refine ⟨hext', fun s₁ hs₁ t₀ v₀ hv₀ => ?_⟩
        cases hs₁
        by_cases ht₀ : t₀ = s.tcur + 1
        · subst ht₀
          simp only [Function.update_self, Option.some.injEq] at hv₀
          subst hv₀
          exact ((hooksFS_vrInv_fromAEADPRG cka prng ae G maxSkip Δcka mo j).startRecv_step
            ctx P (s.tcur + 1) s.γ s.root Tn h
            (some (some (γ', σ', rs)), h₁) hsr γ' σ' rs rfl).mono (Nat.zero_le k)
        · simp only [Function.update_of_ne ht₀] at hv₀
          exact hVR t₀ v₀ hv₀
  · simp only [ht, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact ⟨rfl, fun s₁ hs₁ => by cases hs₁; exact hVR⟩

theorem vRecv_fsClamp_eq [DecidableEq T] [DecidableEq I] [DecidableEq C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip B k Δcka : ℕ) (mo : Mode) (j : ℕ)
    (hB : (k + 1) * (maxSkip + 1) ≤ B)
    (ctx : Ctx Γ T RSt (Option (FSAEAD.RatchetSenderState K))
      (Option (FSAEAD.RatchetReceiverState K MK)) M (ℕ × C))
    (P : Party)
    (s : VP Γ T RSt (Option (FSAEAD.RatchetSenderState K))
      (Option (FSAEAD.RatchetReceiverState K MK)))
    (c : Header T × (ℕ × C)) (rec_ : Option (Record M (Header T × (ℕ × C))))
    (h : FSState T RSt K I (FSAEAD.RatchetSenderState K)
      (FSAEAD.RatchetReceiverState K MK) (ℕ × C))
    (hVR : ∀ t v, s.vR t = some v → FSVROkStep maxSkip k v)
    (hExt : FSVROkStep maxSkip k (h.ext.map Prod.snd)) :
    (vRecv (hooksFS cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip)) Δcka mo j)
        ctx P s c rec_).run h =
      (vRecv (hooksFS cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j)
        ctx P s c rec_).run h := by
  rw [vRecv_eq_bind, vRecv_eq_bind]
  by_cases href : (s.id.sendsIn c.1.1 || decide (s.tcur + 1 < c.1.1))
  · simp [href]
  · simp only [href, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
    have hStep1 :
        vRecvStep1 (hooksFS cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip)) Δcka mo j)
          ctx P s c =
        vRecvStep1 (hooksFS cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j)
          ctx P s c := rfl
    rw [hStep1]
    refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨s₁?, h₁⟩ hmem => ?_
    obtain ⟨hext₁, hVR₁⟩ := vRecvStep1_hooksFS_state cka prng ae G maxSkip k Δcka mo j
      ctx P s c h hVR (s₁?, h₁) hmem
    rcases s₁? with _ | (_ | s₁)
    · rfl
    · rfl
    · rcases hvRc : s₁.vR c.1.1 with _ | v
      · simp only [hvRc]
      · simp only [hvRc, StateT.run_bind]
        have hExt₁ : FSVROkStep maxSkip k (h₁.ext.map Prod.snd) := by rw [hext₁]; exact hExt
        rw [hooksFS_fsRecv_fsClamp_eq cka prng ae G maxSkip B k Δcka mo j hB
          ctx P c.1.1 v c.1 c.2 rec_ h₁ (hVR₁ s₁ rfl c.1.1 v hvRc) hExt₁]

theorem vSend_fsClamp_eq [DecidableEq T] [DecidableEq I] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (B Δcka : ℕ) (mo : Mode) (j : ℕ) :
    vSend (hooksFS cka prng (fsClamp B fs) Δcka mo j) =
      vSend (hooksFS cka prng fs Δcka mo j) := by
  unfold vSend hooksFS fsClamp
  rfl

theorem corrE_fsClamp_eq [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (B Δcka : ℕ) (mo : Mode) (j : ℕ) :
    corrE (hooksFS cka prng (fsClamp B fs) Δcka mo j) =
      corrE (hooksFS cka prng fs Δcka mo j) := by
  unfold corrE hooksFS fsClamp
  rfl

theorem implE_fsClamp_eq [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C]
    [Inhabited C]
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
    (t : (SM.spec (PartyState Γ T RSt (FSAEAD.RatchetSenderState K)
      (FSAEAD.RatchetReceiverState K MK)) M CCoins (Header T × (ℕ × C))).Domain)
    (hVR : SMVRInv (FSVROkStep maxSkip) B_q (q + 1) es.g)
    (hExt : FSVROkStep maxSkip (B_q - (q + 1)) (es.h.ext.map Prod.snd)) :
    (implE (hooksFS cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip)) Δcka mo j)
        (2 + Δcka) qep maxSkip mo.cfg mo.policy (.inr t)).run es =
      (implE (hooksFS cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j)
        (2 + Δcka) qep maxSkip mo.cfg mo.policy (.inr t)).run es := by
  have hkB : (B_q - (q + 1) + 1) * (maxSkip + 1) ≤ B :=
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.sub_le _ _) 1)).trans hB
  rcases t with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
  · change (transmitE _ _ _ _ (P, m, r)).run es = (transmitE _ _ _ _ (P, m, r)).run es
    unfold transmitE
    rw [vSend_fsClamp_eq]
  · change (challE _ _ _ _ _ (P, m₀, m₁, r)).run es =
      (challE _ _ _ _ _ (P, m₀, m₁, r)).run es
    unfold challE
    rw [vSend_fsClamp_eq]
  · change (deliverE _ maxSkip mo.cfg (P, c)).run es = (deliverE _ maxSkip mo.cfg (P, c)).run es
    unfold deliverE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win)
    · simp [hab]
    · simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases htr : es.g.inTransit P.other c with _ | r
      · rfl
      · simp only [run_liftH_bind]
        rw [vRecv_fsClamp_eq cka prng ae G maxSkip B (B_q - (q + 1)) Δcka mo j hkB
          es.g P (es.g.st P) c (some r) es.h (hVR P) hExt]
        rfl
  · change (injectE _ (2 + Δcka) qep mo.cfg (P, c)).run es =
      (injectE _ (2 + Δcka) qep mo.cfg (P, c)).run es
    unfold injectE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases href :
        (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj (2 + Δcka)))
    · simp [href]
    · simp only [href, Bool.false_eq_true, ↓reduceIte, run_liftH_bind]
      rw [vRecv_fsClamp_eq cka prng ae G maxSkip B (B_q - (q + 1)) Δcka mo j hkB
        es.g P (es.g.st P) c none es.h (hVR P) hExt]
      rfl
  · change (corrE _ mo.policy P).run es = (corrE _ mo.policy P).run es
    rw [corrE_fsClamp_eq]

theorem vSend_ext_snd [DecidableEq T] [DecidableEq I] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (ctx : Ctx Γ T RSt (Option SS) (Option RS) M E) (P : Party)
    (s : VP Γ T RSt (Option SS) (Option RS)) (m : M) (pair : Option (M × M))
    (r : Option CCoins) (h : FSState T RSt K I SS RS E) :
    ∀ res ∈ support ((vSend (hooksFS cka prng fs Δcka mo j) ctx P s m pair r).run h),
      res.2.ext.map Prod.snd = h.ext.map Prod.snd := by
  intro ⟨vsRes, h'⟩ hmem
  rw [vSend_eq_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨s₁?, h₁⟩, hmem1, hmem2⟩ := hmem
  have hext₁ : h₁.ext = h.ext := by
    unfold vSendStep1 at hmem1
    split_ifs at hmem1
    · rw [StateT.run_bind, mem_support_bind_iff] at hmem1
      obtain ⟨⟨ssRes, h₁'⟩, hss, hmem1⟩ := hmem1
      have hext' := fsStartSend_ext cka prng fs Δcka mo j ctx P (s.tcur + 1) s.γ s.root r h
        (ssRes, h₁') hss
      rcases ssRes with _ | ⟨γ', T', σ', ss⟩ <;>
        (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem1;
         rcases hmem1 with ⟨_, rfl⟩; exact hext')
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem1
      rcases hmem1 with ⟨_, rfl⟩; rfl
  rcases s₁? with _ | s₁
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2
    rcases hmem2 with ⟨_, rfl⟩; rw [hext₁]
  · rcases hvS : s₁.vS with _ | v
    · simp only [hvS, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2
      rcases hmem2 with ⟨_, rfl⟩; rw [hext₁]
    · simp only [hvS, StateT.run_bind, mem_support_bind_iff] at hmem2
      obtain ⟨⟨fsRes, h₂⟩, hfs, hmem2⟩ := hmem2
      have hext₂ := fsFsSend_ext_snd cka prng fs Δcka mo j ctx P s₁.tcur v
        (s₁.tcur, s₁.curCkaMsg) m pair h₁ (fsRes, h₂) hfs
      rcases fsRes with _ | ⟨v', e⟩ <;>
        (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2;
         rcases hmem2 with ⟨_, rfl⟩; rw [hext₂, hext₁])

theorem vRecv_ext_snd [DecidableEq T] [DecidableEq I] [DecidableEq C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip k Δcka : ℕ) (mo : Mode) (j : ℕ)
    (ctx : Ctx Γ T RSt (Option (FSAEAD.RatchetSenderState K))
      (Option (FSAEAD.RatchetReceiverState K MK)) M (ℕ × C))
    (P : Party)
    (s : VP Γ T RSt (Option (FSAEAD.RatchetSenderState K))
      (Option (FSAEAD.RatchetReceiverState K MK)))
    (c : Header T × (ℕ × C)) (rec_ : Option (Record M (Header T × (ℕ × C))))
    (h : FSState T RSt K I (FSAEAD.RatchetSenderState K)
      (FSAEAD.RatchetReceiverState K MK) (ℕ × C))
    (hVR : ∀ t v, s.vR t = some v → FSVROkStep maxSkip k v)
    (hExt : FSVROkStep maxSkip k (h.ext.map Prod.snd)) :
    ∀ res ∈ support
      ((vRecv (hooksFS cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j)
          ctx P s c rec_).run h),
      FSVROkStep maxSkip (k + 1) (res.2.ext.map Prod.snd) := by
  intro ⟨vrRes, h'⟩ hmem
  rw [vRecv_eq_bind] at hmem
  by_cases href : (s.id.sendsIn c.1.1 || decide (s.tcur + 1 < c.1.1))
  · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hExt.mono (Nat.le_succ k)
  · simp only [href, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
      mem_support_bind_iff] at hmem
    obtain ⟨⟨s₁?, h₁⟩, hmem1, hmem2⟩ := hmem
    obtain ⟨hext₁, _⟩ := vRecvStep1_hooksFS_state cka prng ae G maxSkip k Δcka mo j
      ctx P s c h hVR (s₁?, h₁) hmem1
    have hExt₁ : FSVROkStep maxSkip k (h₁.ext.map Prod.snd) := by rw [hext₁]; exact hExt
    rcases s₁? with _ | (_ | s₁)
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2
      rcases hmem2 with ⟨_, rfl⟩; exact hExt₁.mono (Nat.le_succ k)
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2
      rcases hmem2 with ⟨_, rfl⟩; exact hExt₁.mono (Nat.le_succ k)
    · rcases hvRc : s₁.vR c.1.1 with _ | v
      · simp only [hvRc, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem2
        rcases hmem2 with ⟨_, rfl⟩; exact hExt₁.mono (Nat.le_succ k)
      · simp only [hvRc, StateT.run_bind, mem_support_bind_iff] at hmem2
        obtain ⟨⟨fsRes, h₂⟩, hfs, hmem2⟩ := hmem2
        have hExt₂ := fsFsRecv_ext_snd cka prng ae G maxSkip k Δcka mo j
          ctx P c.1.1 v c.1 c.2 rec_ h₁ hExt₁ (fsRes, h₂) hfs
        rcases fsRes with _ | _ | ⟨v', i', m'⟩ <;>
          (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2;
           rcases hmem2 with ⟨_, rfl⟩; exact hExt₂)

abbrev fsFullImpl [DecidableEq T] [DecidableEq M] [DecidableEq E]
    (fs : FSAEADScheme K SS RS (Header T) M E) :
    QueryImpl (unifSpec + FSAEAD.spec SS RS (Header T) M E)
      (StateT (FSAEAD.State SS RS (Header T) M E) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (FSAEAD.State SS RS (Header T) M E) ProbComp) + FSAEAD.oracleImpl fs

theorem fst_mem_support_of_mem_support_simulateQ_run
    {ι : Type} {spec : OracleSpec.{0, 0} ι} {σ α : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) (oa : OracleComp spec α) (st : σ)
    {z : α × σ} (hz : z ∈ support ((simulateQ impl oa).run st)) : z.1 ∈ support oa := by
  induction oa using OracleComp.inductionOn generalizing st with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz ⊢
    subst hz; rfl
  | query_bind q mx ih =>
    simp only [simulateQ_query_bind, OracleQuery.input_query, OracleQuery.cont_query, id_eq,
      StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨⟨u, st'⟩, _, hmx⟩ := hz
    rw [mem_support_bind_iff]
    exact ⟨u, by simp, ih u st' hmx⟩

theorem fsOracleImpl_receiverState_step [DecidableEq T] [DecidableEq M] [DecidableEq C]
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip k : ℕ)
    (q : (FSAEAD.spec (FSAEAD.RatchetSenderState K) (FSAEAD.RatchetReceiverState K MK)
      (Header T) M (ℕ × C)).Domain)
    (st : FSAEAD.State (FSAEAD.RatchetSenderState K) (FSAEAD.RatchetReceiverState K MK)
      (Header T) M (ℕ × C))
    (hSt : RSReach maxSkip k st.receiverState) :
    ∀ r ∈ support ((FSAEAD.oracleImpl (FSAEAD.fromAEADPRG ae G maxSkip) q).run st),
      RSReach maxSkip
        (if ReductionsQueries.QFSDec (FSAEAD.RatchetSenderState K)
          (FSAEAD.RatchetReceiverState K MK) T M (ℕ × C) (.inr q) then k + 1 else k)
        r.2.receiverState := by
  intro r hr
  rcases q with (((((⟨a, m⟩ | ⟨a, m₀, m₁⟩) | ⟨⟩) | ⟨⟩) | ⟨a, e⟩) | ⟨a, e⟩)
  · simp only [FSAEAD.oracleImpl, QueryImpl.add_apply, FSAEAD.transmitImpl, StateT.run_modifyGet,
      FSAEAD.transmit, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    have hQF : ¬ ReductionsQueries.QFSDec (FSAEAD.RatchetSenderState K)
        (FSAEAD.RatchetReceiverState K MK) T M (ℕ × C)
        (.inr (.inl (.inl (.inl (.inl (.inl (a, m))))))) :=
      ReductionsQueries.hQt_QFSDec _ _ T M (ℕ × C) a m
    simp only [hQF, ↓reduceIte]
    split <;> exact hSt
  · simp only [FSAEAD.oracleImpl, QueryImpl.add_apply, FSAEAD.challengeImpl, StateT.run_modifyGet,
      FSAEAD.challenge, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    have hQF : ¬ ReductionsQueries.QFSDec (FSAEAD.RatchetSenderState K)
        (FSAEAD.RatchetReceiverState K MK) T M (ℕ × C)
        (.inr (.inl (.inl (.inl (.inl (.inr (a, m₀, m₁))))))) :=
      ReductionsQueries.hQch_QFSDec _ _ T M (ℕ × C) a m₀ m₁
    simp only [hQF, ↓reduceIte]
    split <;> exact hSt
  · simp only [FSAEAD.oracleImpl, QueryImpl.add_apply, FSAEAD.corruptSenderImpl,
      StateT.run_modifyGet, FSAEAD.corruptSender, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    have hQF : ¬ ReductionsQueries.QFSDec (FSAEAD.RatchetSenderState K)
        (FSAEAD.RatchetReceiverState K MK) T M (ℕ × C)
        (.inr (.inl (.inl (.inl (.inr ()))))) :=
      ReductionsQueries.hQcs_QFSDec _ _ T M (ℕ × C)
    simp only [hQF, ↓reduceIte]
    split <;> exact hSt
  · simp only [FSAEAD.oracleImpl, QueryImpl.add_apply, FSAEAD.corruptReceiverImpl,
      StateT.run_modifyGet, FSAEAD.corruptReceiver, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    have hQF : ¬ ReductionsQueries.QFSDec (FSAEAD.RatchetSenderState K)
        (FSAEAD.RatchetReceiverState K MK) T M (ℕ × C)
        (.inr (.inl (.inl (.inr ())))) :=
      ReductionsQueries.hQcr_QFSDec _ _ T M (ℕ × C)
    simp only [hQF, ↓reduceIte]
    split <;> exact hSt
  · simp only [FSAEAD.oracleImpl, QueryImpl.add_apply, FSAEAD.deliverImpl, StateT.run_modifyGet,
      support_pure, Set.mem_singleton_iff] at hr
    subst hr
    change RSReach maxSkip (k + 1)
      (FSAEAD.deliver (FSAEAD.fromAEADPRG ae G maxSkip) st a e).2.receiverState
    unfold FSAEAD.deliver FSAEAD.State.removeFromTransit
    split
    · exact hSt.mono (Nat.le_succ k)
    · split
      · exact hSt.mono (Nat.le_succ k)
      · dsimp only
        rcases hrec : (FSAEAD.fromAEADPRG ae G maxSkip).receive st.receiverState a e with
          _ | ⟨rs', i', m'⟩
        · exact hSt.mono (Nat.le_succ k)
        · exact (RSReach.receive ae G maxSkip k hSt hrec).2
  · simp only [FSAEAD.oracleImpl, QueryImpl.add_apply, FSAEAD.injectImpl, StateT.run_modifyGet,
      support_pure, Set.mem_singleton_iff] at hr
    subst hr
    change RSReach maxSkip (k + 1)
      (FSAEAD.inject (FSAEAD.fromAEADPRG ae G maxSkip) st a e).2.receiverState
    unfold FSAEAD.inject
    split_ifs
    · exact hSt.mono (Nat.le_succ k)
    · rcases hrec : (FSAEAD.fromAEADPRG ae G maxSkip).receive st.receiverState a e with
        _ | ⟨rs', i', m'⟩
      · exact hSt.mono (Nat.le_succ k)
      · exact (RSReach.receive ae G maxSkip k hSt hrec).2

theorem receiverState_reach_of_isDecQuery_bound [DecidableEq T] [DecidableEq M] [DecidableEq C]
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip : ℕ)
    {α : Type}
    {oa : FSAEAD.AdversaryComp (FSAEAD.RatchetSenderState K)
      (FSAEAD.RatchetReceiverState K MK) (Header T) M (ℕ × C) α}
    {n k : ℕ}
    (hoa : oa.IsQueryBoundP
      (ReductionsQueries.QFSDec (FSAEAD.RatchetSenderState K)
        (FSAEAD.RatchetReceiverState K MK) T M (ℕ × C)) n)
    (st : FSAEAD.State (FSAEAD.RatchetSenderState K) (FSAEAD.RatchetReceiverState K MK)
      (Header T) M (ℕ × C))
    (hSt : RSReach maxSkip k st.receiverState) :
    ∀ r ∈ support ((simulateQ (fsFullImpl (FSAEAD.fromAEADPRG ae G maxSkip)) oa).run st),
      RSReach maxSkip (k + n) r.2.receiverState := by
  induction oa using OracleComp.inductionOn generalizing n k st with
  | pure a =>
    intro r hr
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact hSt.mono (Nat.le_add_right k n)
  | query_bind q mx ih =>
    rw [isQueryBoundP_query_bind_iff] at hoa
    rcases hoa with ⟨hq0, hmx⟩
    intro r hr
    simp only [simulateQ_query_bind, OracleQuery.input_query, OracleQuery.cont_query, id_eq,
      StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨u, hu, hr⟩ := hr
    cases q with
    | inl m =>
      have hQF : ¬ ReductionsQueries.QFSDec (FSAEAD.RatchetSenderState K)
          (FSAEAD.RatchetReceiverState K MK) T M (ℕ × C) (.inl m) :=
        ReductionsQueries.hQu_QFSDec _ _ T M (ℕ × C) m
      simp only [hQF, ↓reduceIte] at hmx
      change u ∈ support
        ((liftM (OracleSpec.query (spec := unifSpec) m) : ProbComp _) >>=
          fun x => pure (x, st)) at hu
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hu
      obtain ⟨x, _, rfl⟩ := hu
      exact ih x (hmx x) st hSt r hr
    | inr oq =>
      change u ∈ support
        ((FSAEAD.oracleImpl (FSAEAD.fromAEADPRG ae G maxSkip) oq).run st) at hu
      have hStep := fsOracleImpl_receiverState_step ae G maxSkip k oq st hSt u hu
      have ihStep := ih u.1 (hmx u.1) u.2 hStep r hr
      refine ihStep.mono ?_
      split_ifs with hq
      · have hn : 0 < n := hq0.resolve_left (fun h => h hq)
        omega
      · omega

theorem simulateQ_fsFullImpl_corruptSenderQuery [DecidableEq T] [DecidableEq M] [DecidableEq E]
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (sF : FSState T RSt K I SS RS E) (st : FSAEAD.State SS RS (Header T) M E) :
    (simulateQ (fsFullImpl fs)
      ((liftF (FSAEAD.corruptSenderQuery (ReceiverState := RS) (AssocData := Header T)
        (Message := M) (Ciphertext := E))).run sF)).run st =
      pure (((FSAEAD.corruptSender st).1, sF), (FSAEAD.corruptSender st).2) := by
  simp [liftF, StateT.run_lift, map_eq_bind_pure_comp, FSAEAD.corruptSenderQuery,
    fsFullImpl, FSAEAD.oracleImpl, FSAEAD.corruptSenderImpl, modifyGet, MonadStateOf.modifyGet]
  rfl

theorem simulateQ_fsFullImpl_corruptReceiverQuery [DecidableEq T] [DecidableEq M] [DecidableEq E]
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (sF : FSState T RSt K I SS RS E) (st : FSAEAD.State SS RS (Header T) M E) :
    (simulateQ (fsFullImpl fs)
      ((liftF (FSAEAD.corruptReceiverQuery (SenderState := SS) (ReceiverState := RS)
        (AssocData := Header T) (Message := M) (Ciphertext := E))).run sF)).run st =
      pure (((FSAEAD.corruptReceiver st).1, sF), (FSAEAD.corruptReceiver st).2) := by
  simp [liftF, StateT.run_lift, map_eq_bind_pure_comp, FSAEAD.corruptReceiverQuery,
    fsFullImpl, FSAEAD.oracleImpl, FSAEAD.corruptReceiverImpl, modifyGet, MonadStateOf.modifyGet]
  rfl

theorem fsReveal_ext_snd_fromAEADPRG [DecidableEq T] [DecidableEq I] [DecidableEq M]
    [DecidableEq C] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip k Δcka : ℕ) (mo : Mode) (j : ℕ)
    (ctx : Ctx Γ T RSt (Option (FSAEAD.RatchetSenderState K))
      (Option (FSAEAD.RatchetReceiverState K MK)) M (ℕ × C)) (P : Party)
    (vp : VP Γ T RSt (Option (FSAEAD.RatchetSenderState K))
      (Option (FSAEAD.RatchetReceiverState K MK)))
    (h : FSState T RSt K I (FSAEAD.RatchetSenderState K)
      (FSAEAD.RatchetReceiverState K MK) (ℕ × C))
    (st : FSAEAD.State (FSAEAD.RatchetSenderState K) (FSAEAD.RatchetReceiverState K MK)
      (Header T) M (ℕ × C))
    (hExt : FSVROkStep maxSkip k (h.ext.map Prod.snd))
    (hSt : RSReach maxSkip k st.receiverState) :
    ∀ z ∈ support
      ((simulateQ (fsFullImpl (FSAEAD.fromAEADPRG ae G maxSkip))
        (((hooksFS cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j).reveal ctx P vp).run
          h)).run st),
      FSVROkStep maxSkip k (z.1.2.ext.map Prod.snd) := by
  have hcs : ∀ (st₀ : FSAEAD.State (FSAEAD.RatchetSenderState K)
      (FSAEAD.RatchetReceiverState K MK) (Header T) M (ℕ × C)),
      (FSAEAD.corruptSender st₀).2.receiverState = st₀.receiverState := by
    intro st₀; unfold FSAEAD.corruptSender; split_ifs <;> rfl
  have hcr : ∀ (st₀ : FSAEAD.State (FSAEAD.RatchetSenderState K)
      (FSAEAD.RatchetReceiverState K MK) (Header T) M (ℕ × C)) ss' rs',
      (FSAEAD.corruptReceiver st₀).1 = some (ss', rs') → rs' = st₀.receiverState := by
    intro st₀ ss' rs'; unfold FSAEAD.corruptReceiver; split_ifs <;> simp_all
  intro z hz
  simp only [hooksFS, pure_bind] at hz
  rcases hvS : vp.vS with _ | (_ | ss)
  · simp only [hvS] at hz
    rcases hvR : vp.vR mo.tStar with _ | (_ | rs')
    · simp only [hvR, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz; exact hExt
    · simp only [hvR, StateT.run_bind, StateT.run_get, pure_bind] at hz
      rcases hext : h.ext with _ | ⟨ss₁, rs₁⟩
      · simp only [hext] at hz
        by_cases hauth : mo.auth = true
        · simp only [hauth, ↓reduceIte, StateT.run_pure, simulateQ_pure,
            support_pure, Set.mem_singleton_iff] at hz
          subst hz; simp [hext, FSVROkStep]
        · simp only [hauth, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, simulateQ_bind,
            simulateQ_fsFullImpl_corruptReceiverQuery, pure_bind] at hz
          rcases hcr_eq : (FSAEAD.corruptReceiver st).1 with _ | ⟨ss', rs'⟩
          · simp only [hcr_eq, StateT.run_pure, simulateQ_pure, support_pure,
              Set.mem_singleton_iff] at hz
            subst hz; simp [hext, FSVROkStep]
          · simp only [hcr_eq, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; dsimp [FSVROkStep]; rw [hcr st ss' rs' hcr_eq]; exact hSt
      · simp only [hext, StateT.run_pure, simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at hz
        subst hz; exact hExt
    · simp only [hvR, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz; exact hExt
  · simp only [hvS, StateT.run_bind, StateT.run_get, pure_bind] at hz
    rcases hext : h.ext with _ | ⟨ss₁, rs₁⟩
    · simp only [hext, StateT.run_bind, simulateQ_bind,
        simulateQ_fsFullImpl_corruptSenderQuery, pure_bind] at hz
      rcases hcs_eq : (FSAEAD.corruptSender st).1 with _ | ss'
      · simp only [hcs_eq, StateT.run_pure, simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at hz
        subst hz; simp [hext, FSVROkStep]
      · simp only [hcs_eq, StateT.run_bind, StateT.run_modify, pure_bind] at hz
        rcases hvR : vp.vR mo.tStar with _ | (_ | rs')
        · simp only [hvR, StateT.run_pure, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at hz
          subst hz; simp [hext, FSVROkStep]
        · simp only [hvR, hext, StateT.run_bind, StateT.run_get, pure_bind] at hz
          by_cases hauth : mo.auth = true
          · simp only [hauth, ↓reduceIte, StateT.run_pure, simulateQ_pure,
              support_pure, Set.mem_singleton_iff] at hz
            subst hz; simp [FSVROkStep]
          · simp only [hauth, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, simulateQ_bind,
              simulateQ_fsFullImpl_corruptReceiverQuery, pure_bind] at hz
            rcases hcr_eq : (FSAEAD.corruptReceiver (FSAEAD.corruptSender st).2).1 with
              _ | ⟨ss'', rs''⟩
            · simp only [hcr_eq, StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hz
              subst hz; simp [FSVROkStep]
            · simp only [hcr_eq, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
              subst hz; dsimp [FSVROkStep]
              rw [hcr (FSAEAD.corruptSender st).2 ss'' rs'' hcr_eq, hcs st]
              exact hSt
        · simp only [hvR, StateT.run_pure, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at hz
          subst hz; simp [hext, FSVROkStep]
    · simp only [hext] at hz
      rcases hvR : vp.vR mo.tStar with _ | (_ | rs')
      · simp only [hvR, StateT.run_pure, simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at hz
        subst hz; exact hExt
      · simp only [hvR, hext, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
          simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hExt
      · simp only [hvR, StateT.run_pure, simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at hz
        subst hz; exact hExt
  · simp only [hvS] at hz
    rcases hvR : vp.vR mo.tStar with _ | (_ | rs')
    · simp only [hvR, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz; exact hExt
    · simp only [hvR, StateT.run_bind, StateT.run_get, pure_bind] at hz
      rcases hext : h.ext with _ | ⟨ss₁, rs₁⟩
      · simp only [hext] at hz
        by_cases hauth : mo.auth = true
        · simp only [hauth, ↓reduceIte, StateT.run_pure, simulateQ_pure,
            support_pure, Set.mem_singleton_iff] at hz
          subst hz; simp [hext, FSVROkStep]
        · simp only [hauth, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, simulateQ_bind,
            simulateQ_fsFullImpl_corruptReceiverQuery, pure_bind] at hz
          rcases hcr_eq : (FSAEAD.corruptReceiver st).1 with _ | ⟨ss', rs'⟩
          · simp only [hcr_eq, StateT.run_pure, simulateQ_pure, support_pure,
              Set.mem_singleton_iff] at hz
            subst hz; simp [hext, FSVROkStep]
          · simp only [hcr_eq, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; dsimp [FSVROkStep]; rw [hcr st ss' rs' hcr_eq]; exact hSt
      · simp only [hext, StateT.run_pure, simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at hz
        subst hz; exact hExt
    · simp only [hvR, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz; exact hExt

theorem corrE_ext_snd_fromAEADPRG [DecidableEq T] [DecidableEq I] [DecidableEq M]
    [DecidableEq C] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip k Δcka : ℕ) (mo : Mode) (j : ℕ)
    (es : EState (VP Γ T RSt (Option (FSAEAD.RatchetSenderState K))
      (Option (FSAEAD.RatchetReceiverState K MK))) M (Header T × (ℕ × C))
      (FSState T RSt K I (FSAEAD.RatchetSenderState K)
        (FSAEAD.RatchetReceiverState K MK) (ℕ × C)))
    (P : Party)
    (st : FSAEAD.State (FSAEAD.RatchetSenderState K) (FSAEAD.RatchetReceiverState K MK)
      (Header T) M (ℕ × C))
    (hExt : FSVROkStep maxSkip k (es.h.ext.map Prod.snd))
    (hSt : RSReach maxSkip k st.receiverState) :
    ∀ z ∈ support
      ((simulateQ (fsFullImpl (FSAEAD.fromAEADPRG ae G maxSkip))
        ((corrE (hooksFS cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j)
          mo.policy P).run es)).run st),
      FSVROkStep maxSkip k (z.1.2.h.ext.map Prod.snd) := by
  intro z hz
  unfold corrE abortE at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  by_cases href : (es.abort || es.g.win || !(es.g.corrAllowed P))
  · simp only [href, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz; exact hExt
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hz
    by_cases hdoom : (mo.policy.leakDoom es.g (es.g.afterCorr P) || mo.policy.corrDoom es.g P)
    · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
        pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact hExt
    · simp only [hdoom, Bool.false_eq_true, ↓reduceIte, run_liftH_bind] at hz
      simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨⟨⟨revRes, h'⟩, st'⟩, hrev, hz⟩ := hz
      have hExt' := fsReveal_ext_snd_fromAEADPRG cka prng ae G maxSkip k Δcka mo j
        es.g P (es.g.st P) es.h st hExt hSt ((revRes, h'), st') hrev
      rcases revRes with _ | stP <;>
        (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
           simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz;
         subst hz; exact hExt')

theorem implE_nonCorr_ext_snd [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C]
    [Inhabited C] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip k Δcka qep : ℕ) (mo : Mode) (j : ℕ)
    (es : EState (VP Γ T RSt (Option (FSAEAD.RatchetSenderState K))
      (Option (FSAEAD.RatchetReceiverState K MK))) M (Header T × (ℕ × C))
      (FSState T RSt K I (FSAEAD.RatchetSenderState K)
        (FSAEAD.RatchetReceiverState K MK) (ℕ × C)))
    (q : (SM.spec (PartyState Γ T RSt (FSAEAD.RatchetSenderState K)
      (FSAEAD.RatchetReceiverState K MK)) M CCoins (Header T × (ℕ × C))).Domain)
    (hNotCorr : ∀ P, q ≠ .inr P)
    (hVR : ∀ P t₀ v, (es.g.st P).vR t₀ = some v → FSVROkStep maxSkip k v)
    (hExt : FSVROkStep maxSkip k (es.h.ext.map Prod.snd)) :
    ∀ res ∈ support
      ((implE (hooksFS cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j)
          (2 + Δcka) qep maxSkip mo.cfg mo.policy (.inr q)).run es),
      FSVROkStep maxSkip (k + 1) (res.2.h.ext.map Prod.snd) := by
  have hExt1 : FSVROkStep maxSkip (k + 1) (es.h.ext.map Prod.snd) := hExt.mono (Nat.le_succ k)
  rcases q with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
  · intro ⟨out, es'⟩ hmem
    change (out, es') ∈ support ((transmitE _ _ _ _ (P, m, r)).run es) at hmem
    unfold transmitE abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases hab : (es.abort || es.g.win)
    · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hExt1
    · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
      rcases hep : es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
      · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hExt1
      · simp only [hep] at hmem
        by_cases hdoom : mo.policy.leakDoom es.g s₁
        · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
            pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hExt1
        · simp only [hdoom, Bool.false_eq_true, ↓reduceIte,
            run_liftH_bind, mem_support_bind_iff] at hmem
          obtain ⟨⟨vsRes, h'⟩, hvs, hmem⟩ := hmem
          have hext' := vSend_ext_snd cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
            Δcka mo j s₁ P (s₁.st P) m none r es.h (vsRes, h') hvs
          rcases vsRes with _ | ⟨st', ct⟩ <;>
            (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
               support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
             rcases hmem with ⟨_, rfl⟩; dsimp only at hext' ⊢; rw [hext']; exact hExt1)
  · intro ⟨out, es'⟩ hmem
    change (out, es') ∈ support ((challE _ _ _ _ _ (P, m₀, m₁, r)).run es) at hmem
    unfold challE abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases hab : (es.abort || es.g.win)
    · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hExt1
    · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
      rcases hep : es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
      · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hExt1
      · simp only [hep] at hmem
        by_cases hch : (!(s₁.safeCh (2 + Δcka) P) || !((Mode.cfg (M := M) mo).challAllowedIn (s₁.epoch P)))
        · simp only [hch, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hExt1
        · simp only [hch, Bool.false_eq_true, ↓reduceIte] at hmem
          by_cases hdoom : mo.policy.leakDoom es.g s₁
          · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hExt1
          · simp only [hdoom, Bool.false_eq_true, ↓reduceIte,
              run_liftH_bind, mem_support_bind_iff] at hmem
            obtain ⟨⟨vsRes, h'⟩, hvs, hmem⟩ := hmem
            have hext' := vSend_ext_snd cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
              Δcka mo j s₁ P (s₁.st P) _ (some (m₀, m₁)) r es.h (vsRes, h') hvs
            rcases vsRes with _ | ⟨st', ct⟩ <;>
              (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                 support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
               rcases hmem with ⟨_, rfl⟩; dsimp only at hext' ⊢; rw [hext']; exact hExt1)
  · intro ⟨out, es'⟩ hmem
    change (out, es') ∈ support ((deliverE _ maxSkip _ (P, c)).run es) at hmem
    unfold deliverE abortE at hmem
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
      · simp only [htr, run_liftH_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨vrRes, h'⟩, hvr, hmem⟩ := hmem
        have hExt' := vRecv_ext_snd cka prng ae G maxSkip k Δcka mo j
          es.g P (es.g.st P) c (some r) es.h (hVR P) hExt (vrRes, h') hvr
        rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hExt'
        · split_ifs at hmem <;>
            (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
               support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
             rcases hmem with ⟨_, rfl⟩; exact hExt')
        · simp only [StateT.run_bind, commitE_fs_eq, pure_bind, StateT.run_modify,
            StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hExt'
  · intro ⟨out, es'⟩ hmem
    change (out, es') ∈ support ((injectE _ (2 + Δcka) qep _ (P, c)).run es) at hmem
    unfold injectE abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases href :
        (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj (2 + Δcka)))
    · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hExt1
    · simp only [href, Bool.false_eq_true, ↓reduceIte, run_liftH_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨⟨vrRes, h'⟩, hvr, hmem⟩ := hmem
      have hExt' := vRecv_ext_snd cka prng ae G maxSkip k Δcka mo j
        es.g P (es.g.st P) c none es.h (hVR P) hExt (vrRes, h') hvr
      rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hExt'
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hExt'
      · by_cases hqep : qep + 1 < t'
        · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hExt'
        · simp only [hqep, ↓reduceIte] at hmem
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
  · exact absurd rfl (hNotCorr P)

theorem implE_ext_snd_fromAEADPRG [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C]
    [Inhabited C] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip k Δcka qep : ℕ) (mo : Mode) (j : ℕ)
    (es : EState (VP Γ T RSt (Option (FSAEAD.RatchetSenderState K))
      (Option (FSAEAD.RatchetReceiverState K MK))) M (Header T × (ℕ × C))
      (FSState T RSt K I (FSAEAD.RatchetSenderState K)
        (FSAEAD.RatchetReceiverState K MK) (ℕ × C)))
    (q : (SM.spec (PartyState Γ T RSt (FSAEAD.RatchetSenderState K)
      (FSAEAD.RatchetReceiverState K MK)) M CCoins (Header T × (ℕ × C))).Domain)
    (st : FSAEAD.State (FSAEAD.RatchetSenderState K) (FSAEAD.RatchetReceiverState K MK)
      (Header T) M (ℕ × C))
    (hVR : ∀ P t₀ v, (es.g.st P).vR t₀ = some v → FSVROkStep maxSkip k v)
    (hExt : FSVROkStep maxSkip k (es.h.ext.map Prod.snd))
    (hSt : RSReach maxSkip k st.receiverState) :
    ∀ z ∈ support
      ((simulateQ (fsFullImpl (FSAEAD.fromAEADPRG ae G maxSkip))
        ((implE (hooksFS cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j)
          (2 + Δcka) qep maxSkip mo.cfg mo.policy (.inr q)).run es)).run st),
      FSVROkStep maxSkip (k + 1) (z.1.2.h.ext.map Prod.snd) := by
  intro z hz
  rcases q with (((q₁ | q₂) | q₃) | q₄) | P
  · exact implE_nonCorr_ext_snd cka prng ae G maxSkip k Δcka qep mo j es _
      (by intro _ h; nomatch h) hVR hExt z.1
      (fst_mem_support_of_mem_support_simulateQ_run _ _ st hz)
  · exact implE_nonCorr_ext_snd cka prng ae G maxSkip k Δcka qep mo j es _
      (by intro _ h; nomatch h) hVR hExt z.1
      (fst_mem_support_of_mem_support_simulateQ_run _ _ st hz)
  · exact implE_nonCorr_ext_snd cka prng ae G maxSkip k Δcka qep mo j es _
      (by intro _ h; nomatch h) hVR hExt z.1
      (fst_mem_support_of_mem_support_simulateQ_run _ _ st hz)
  · exact implE_nonCorr_ext_snd cka prng ae G maxSkip k Δcka qep mo j es _
      (by intro _ h; nomatch h) hVR hExt z.1
      (fst_mem_support_of_mem_support_simulateQ_run _ _ st hz)
  · exact (corrE_ext_snd_fromAEADPRG cka prng ae G maxSkip k Δcka mo j es P st hExt hSt z hz).mono
      (Nat.le_succ k)

theorem simulateQ_implE_fsClamp_fromAEADPRG_eq [DecidableEq T] [DecidableEq I] [DecidableEq M]
    [DecidableEq C] [Inhabited C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK))
    (fs₀ : FSAEADScheme K (FSAEAD.RatchetSenderState K) (FSAEAD.RatchetReceiverState K MK)
      (Header T) M (ℕ × C))
    (L B B_q Δcka qep maxSkip : ℕ)
    (mo : Mode) (j : ℕ)
    (hfs₀ : fs₀ = FSAEAD.fromAEADPRG ae G maxSkip)
    (hB : (B_q + 1) * (maxSkip + 1) ≤ B)
    {α : Type} {oa : OracleComp (unifSpec + SM.spec
      (PartyState Γ T RSt (FSAEAD.RatchetSenderState K) (FSAEAD.RatchetReceiverState K MK))
      M CCoins (Header T × (ℕ × C))) α}
    {q : ℕ}
    (hoa : oa.IsQueryBoundP
      (isGameQuery (G := SM.spec
        (PartyState Γ T RSt (FSAEAD.RatchetSenderState K) (FSAEAD.RatchetReceiverState K MK))
        M CCoins (Header T × (ℕ × C)))) q)
    (es : EState (VP Γ T RSt (Option (FSAEAD.RatchetSenderState K))
      (Option (FSAEAD.RatchetReceiverState K MK))) M (Header T × (ℕ × C))
      (FSState T RSt K I (FSAEAD.RatchetSenderState K)
        (FSAEAD.RatchetReceiverState K MK) (ℕ × C)))
    (st : FSAEAD.State (FSAEAD.RatchetSenderState K) (FSAEAD.RatchetReceiverState K MK)
      (Header T) M (ℕ × C))
    (hInv : SMEngineInv L B_q q es.g)
    (hVR : SMVRInv (FSVROkStep maxSkip) B_q q es.g)
    (hExt : FSVROkStep maxSkip (B_q - q) (es.h.ext.map Prod.snd))
    (hSt : RSReach maxSkip (B_q - q) st.receiverState) :
    (simulateQ (fsFullImpl fs₀)
      ((simulateQ (implE (hooksFS cka prng (fsClamp B fs₀) Δcka mo j)
        (2 + Δcka) qep maxSkip mo.cfg mo.policy) oa).run es)).run st =
    (simulateQ (fsFullImpl fs₀)
      ((simulateQ (implE (hooksFS cka prng fs₀ Δcka mo j)
        (2 + Δcka) qep maxSkip mo.cfg mo.policy) oa).run es)).run st := by
  subst hfs₀
  induction oa using OracleComp.inductionOn generalizing q es st with
  | pure x => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind qy mx ih =>
    rw [isQueryBoundP_query_bind_iff] at hoa
    rcases hoa with ⟨hq0, hmx⟩
    rw [simulateQ_query_bind, simulateQ_query_bind, StateT.run_bind, StateT.run_bind,
      simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind]
    have hLift : ∀ {M' : Type → Type} [Monad M'] {σ' α' : Type} (m : StateT σ' M' α') (s : σ'),
        (liftM m : StateT σ' M' α').run s = m.run s := fun _ _ => rfl
    rw [hLift, hLift]
    simp only [OracleQuery.input_query, OracleQuery.cont_query]
    rcases qy with n | t_sm
    · simp only [isGameQuery, ↓reduceIte] at hmx
      have hInl1 :
          (implE (hooksFS cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip)) Δcka mo j)
              (2 + Δcka) qep maxSkip mo.cfg mo.policy (.inl n)).run es =
            (coinsE n).run es := rfl
      have hInl2 :
          (implE (hooksFS cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j)
              (2 + Δcka) qep maxSkip mo.cfg mo.policy (.inl n)).run es =
            (coinsE n).run es := rfl
      rw [hInl1, hInl2]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨u, es'⟩, st'⟩ hmem => ?_
      have hmem1 : (u, es') ∈ support ((coinsE n).run es) :=
        fst_mem_support_of_mem_support_simulateQ_run _ _ st hmem
      simp only [coinsE, StateT.run_lift, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem1
      obtain ⟨_, _, _, rfl⟩ := hmem1
      have hQbCoins : ((coinsE n).run es').IsQueryBoundP
          (ReductionsQueries.QFSDec (FSAEAD.RatchetSenderState K)
            (FSAEAD.RatchetReceiverState K MK) T M (ℕ × C)) 0 :=
        ReductionsQueries.qb_coinsE (ReductionsQueries.hQu_QFSDec _ _ T M (ℕ × C)) n es'
      have hSt' : RSReach maxSkip (B_q - q) st'.receiverState := by
        simpa using receiverState_reach_of_isDecQuery_bound ae G maxSkip hQbCoins st hSt
          ((u, es'), st') hmem
      exact ih u (hmx u) es' st' hInv hVR hExt hSt'
    · simp only [isGameQuery, ↓reduceIte] at hq0 hmx
      have hqp : 0 < q := hq0.resolve_left (by decide)
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      have hStep :
          (implE (hooksFS cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip)) Δcka mo j)
              (2 + Δcka) qep maxSkip mo.cfg mo.policy (.inr t_sm)).run es =
            (implE (hooksFS cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j)
              (2 + Δcka) qep maxSkip mo.cfg mo.policy (.inr t_sm)).run es :=
        implE_fsClamp_eq cka prng ae G maxSkip B B_q q' Δcka qep mo j hB es t_sm hVR hExt
      rw [hStep]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨u, es'⟩, st'⟩ hmem => ?_
      have hmem1 := fst_mem_support_of_mem_support_simulateQ_run _ _ st hmem
      have hInv' := implE_inv (hooksFS cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j)
        mo.cfg mo.policy es t_sm hInv (u, es') hmem1
      have hVR' : SMVRInv (FSVROkStep maxSkip) B_q q' es'.g :=
        implE_vrInv
          (hooksFS cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j)
          (hooksFS_vrInv_fromAEADPRG cka prng ae G maxSkip Δcka mo j)
          mo.cfg mo.policy es t_sm hInv hVR (u, es') hmem1
      have hBq : B_q - (q' + 1) + 1 ≤ B_q - q' := by have := hInv.1; omega
      have hExt' : FSVROkStep maxSkip (B_q - q') (es'.h.ext.map Prod.snd) :=
        (implE_ext_snd_fromAEADPRG cka prng ae G maxSkip (B_q - (q' + 1)) Δcka qep mo j
          es t_sm st (fun P _ _ hv => hVR P _ _ hv) hExt hSt ((u, es'), st') hmem).mono hBq
      have hSt' : RSReach maxSkip (B_q - q') st'.receiverState := by
        have hQbStep :
            ((implE (hooksFS cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j)
              (2 + Δcka) qep (FSAEAD.fromAEADPRG ae G maxSkip).maxSkip
              mo.cfg mo.policy (.inr t_sm)).run es).IsQueryBoundP
              (ReductionsQueries.QFSDec (FSAEAD.RatchetSenderState K)
                (FSAEAD.RatchetReceiverState K MK) T M (ℕ × C)) 1 :=
          ReductionsQueries.qb_implE_inr_one
            (ReductionsQueries.hQu_QFSDec _ _ T M (ℕ × C))
            (ReductionsQueries.hQt_QFSDec _ _ T M (ℕ × C))
            (ReductionsQueries.hQch_QFSDec _ _ T M (ℕ × C))
            (ReductionsQueries.hQcs_QFSDec _ _ T M (ℕ × C))
            (ReductionsQueries.hQcr_QFSDec _ _ T M (ℕ × C))
            cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka qep mo j t_sm es
        exact (receiverState_reach_of_isDecQuery_bound ae G maxSkip hQbStep st hSt
          ((u, es'), st') hmem).mono hBq
      exact ih u (by simpa using hmx u) es' st' hInv' hVR' hExt' hSt'

theorem isQueryBoundP_initFSRaw_dec [DecidableEq I]
    [SampleableType KR] [SampleableType KC] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (mo : Mode) (j : ℕ) (b : Bool) :
    (initFSRaw cka prng fs lam mo j b).IsQueryBoundP
      (ReductionsQueries.QFSDec SS RS T M E) 0 := by
  have hQu := ReductionsQueries.hQu_QFSDec SS RS T M E
  unfold initFSRaw
  refine isQueryBoundP_bind (n := 0) (m := 0)
    (ReductionsQueries.isQueryBoundP_sampleT hQu KR) fun kr _ => ?_
  refine isQueryBoundP_bind (n := 0) (m := 0)
    (ReductionsQueries.isQueryBoundP_sampleT hQu KC) fun kc _ => ?_
  refine isQueryBoundP_bind (n := 0) (m := 0)
    (ReductionsQueries.qb_rootFS hQu prng mo 0 lam (prng.init kr) {})
    fun ⟨⟨σ, k, sid⟩, h₁⟩ _ => ?_
  exact isQueryBoundP_bind (n := 0) (m := 0)
    (ReductionsQueries.qb_extOf j sid h₁) fun ⟨ext, h₂⟩ _ => isQueryBoundP_pure _ _ 0

theorem simulateQ_runFS_fsClamp_fromAEADPRG [DecidableEq T] [DecidableEq I] [DecidableEq M]
    [DecidableEq C] [Inhabited C]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip L B B_q Δcka qep : ℕ)
    (lam : I) (mo : Mode) (j : ℕ) (b : Bool)
    (hFsB : (B_q + 1) * (maxSkip + 1) ≤ B)
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : SchemeAdversary Γ T RSt (FSAEAD.RatchetSenderState K)
      (FSAEAD.RatchetReceiverState K MK) M CCoins (ℕ × C)) (qAdv : ℕ)
    (hA : MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q)
    (st₀ : FSAEAD.State (FSAEAD.RatchetSenderState K) (FSAEAD.RatchetReceiverState K MK)
      (Header T) M (ℕ × C))
    (hSt₀ : RSReach maxSkip 0 st₀.receiverState) :
    (simulateQ (fsFullImpl (FSAEAD.fromAEADPRG ae G maxSkip))
      (runFS cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip))
        lam Δcka qep mo j b A)).run st₀ =
    (simulateQ (fsFullImpl (FSAEAD.fromAEADPRG ae G maxSkip))
      (runFS cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
        lam Δcka qep mo j b A)).run st₀ := by
  have hA' : A.IsQueryBoundP
      (isGameQuery (G := SM.spec
        (PartyState Γ T RSt (FSAEAD.RatchetSenderState K) (FSAEAD.RatchetReceiverState K MK))
        M CCoins (Header T × (ℕ × C)))) qAdv := by
    refine hA.of_imp (fun x hx => ?_)
    rcases x with _ | _ <;> simp_all [isGameQuery]
  rw [runFS_eq_bind_initFSRaw, runFS_eq_bind_initFSRaw]
  have hInitEq :
      initFSRaw cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip)) lam mo j b =
        initFSRaw cka prng (FSAEAD.fromAEADPRG ae G maxSkip) lam mo j b := rfl
  rw [hInitEq, simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨es₀, st₁⟩ hmem₀ => ?_
  have hes₀ : es₀ ∈ support (initFSRaw cka prng (FSAEAD.fromAEADPRG ae G maxSkip) lam mo j b) :=
    fst_mem_support_of_mem_support_simulateQ_run _ _ st₀ hmem₀
  have ⟨hInv₀, _⟩ := initFSRaw_inv cka prng (FSAEAD.fromAEADPRG ae G maxSkip) lam mo j b
    hqB hB1 hBB es₀ hes₀
  have ⟨hVR₀, hext₀⟩ := initFSRaw_vrInv_fromAEADPRG cka prng ae G maxSkip lam mo j b
    B_q qAdv es₀ hes₀
  have hExt₀ : FSVROkStep maxSkip (B_q - qAdv) (es₀.h.ext.map Prod.snd) := by
    simp [hext₀, FSVROkStep]
  have hSt₁ : RSReach maxSkip (B_q - qAdv) st₁.receiverState :=
    (receiverState_reach_of_isDecQuery_bound ae G maxSkip
      (isQueryBoundP_initFSRaw_dec cka prng (FSAEAD.fromAEADPRG ae G maxSkip) lam mo j b)
      st₀ hSt₀ (es₀, st₁) hmem₀).mono (Nat.zero_le _)
  rw [simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind]
  have hSim := simulateQ_implE_fsClamp_fromAEADPRG_eq cka prng ae G
    (FSAEAD.fromAEADPRG ae G maxSkip) L B B_q Δcka qep maxSkip
    mo j rfl hFsB hA' es₀ st₁ hInv₀.sm hVR₀ hExt₀ hSt₁
  have hms1 : (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip)).maxSkip = maxSkip := rfl
  have hms2 : (FSAEAD.fromAEADPRG ae G maxSkip).maxSkip = maxSkip := rfl
  rw [hms1, hms2, hSim]

end FromAEADPRG

/-! ## Multi-session `redFSAuthMultiStage2` -/

/-- Multi-session target interface into `unifSpec + FSMultiSpec` over `prngSig`. -/
@[reducible] def fsaeadMultiHeaderAdIface (KC Γ CCoins T I KR RSt K SS RS M E : Type)
    (sampKR : ProbComp KR)
    (sampKC : ProbComp KC)
    (sampCCoins : ProbComp CCoins)
    (sampI : ProbComp I)
    (sampK : ProbComp K) :
    Iface (prngSig KC Γ CCoins T I KR RSt K SS RS M E)
      (unifSpec + OracleSpec.sigma (fun _ : ℕ => FSAEAD.spec SS RS (Header T) M E)) where
  fwdU n :=
    query (spec := unifSpec + OracleSpec.sigma (fun _ : ℕ => FSAEAD.spec SS RS (Header T) M E))
      (.inl n)
  uCost := 1
  Tag := FSHdrTag
  dom := fun g =>
    .prod .nat ((fsaeadHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E
      sampKR sampKC sampCCoins sampI sampK).dom g)
  cod := fun g =>
    (fsaeadHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E
      sampKR sampKC sampCCoins sampI sampK).cod g
  enc := fun
    | .tr, (sIdx, x) => .inr ⟨sIdx, .inl (.inl (.inl (.inl (.inl x))))⟩
    | .ch, (sIdx, x) => .inr ⟨sIdx, .inl (.inl (.inl (.inl (.inr x))))⟩
    | .cs, (sIdx, x) => .inr ⟨sIdx, .inl (.inl (.inl (.inr x)))⟩
    | .cr, (sIdx, x) => .inr ⟨sIdx, .inl (.inl (.inr x))⟩
    | .dl, (sIdx, x) => .inr ⟨sIdx, .inl (.inr x)⟩
    | .ij, (sIdx, x) => .inr ⟨sIdx, .inr x⟩
  dec := fun
    | .tr, _, u => u
    | .ch, _, u => u
    | .cs, _, u => u
    | .cr, _, u => u
    | .dl, _, u => Option.map fsHdrRrEnc u
    | .ij, _, u => Option.map fsHdrRrEnc u
  qCost := fun _ => 1
  smp := prngSamplers sampKR sampKC sampCCoins sampI sampK

@[reducible] def fsMultiCacheEntryTy (KC Γ CCoins T I KR RSt K SS RS M E : Type) :
    Ty (prngSig KC Γ CCoins T I KR RSt K SS RS M E) :=
  .prod (.base .t) (.prod (.base .sig) (.prod (.base .k) (.opt .nat)))

@[reducible] def fsMultiSessBookTy (KC Γ CCoins T I KR RSt K SS RS M E : Type) :
    Ty (prngSig KC Γ CCoins T I KR RSt K SS RS M E) :=
  .prod .bool (.prod .nat (.list (fsTransEntryTy KC Γ CCoins T I KR RSt K SS RS M E)))

/-- Hook-state type `(cache, table, sessions, book, lfWin)` for `hooksFSMultiC`. -/
@[reducible] def fsMultiHsTy (KC Γ CCoins T I KR RSt K SS RS M E : Type) :
    Ty (prngSig KC Γ CCoins T I KR RSt K SS RS M E) :=
  .prod (.tbl (.opt (fsMultiCacheEntryTy KC Γ CCoins T I KR RSt K SS RS M E)))
    (.prod (.list (fsTableEntryTy KC Γ CCoins T I KR RSt K SS RS M E))
      (.prod (.list (.base .i))
        (.prod (.tbl (.opt (fsMultiSessBookTy KC Γ CCoins T I KR RSt K SS RS M E))) .bool)))

@[reducible] def fsMultiVpTy (KC Γ CCoins T I KR RSt K SS RS M E : Type) :
    Ty (prngSig KC Γ CCoins T I KR RSt K SS RS M E) :=
  @vpTblTy KC Γ CCoins T I KR RSt K SS RS M E
    (.base .γ) (.base .sig) (.sum (.base .ss) .nat) (.sum (.base .rs) .nat)

@[reducible] def fsMultiEsTy (KC Γ CCoins T I KR RSt K SS RS M E : Type) :
    Ty (prngSig KC Γ CCoins T I KR RSt K SS RS M E) :=
  esTy (fsMultiVpTy KC Γ CCoins T I KR RSt K SS RS M E)
    (fsMultiHsTy KC Γ CCoins T I KR RSt K SS RS M E)

section HooksFSMultiC

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

local notation "IIM" =>
  fsaeadMultiHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK

local notation "hdrTy" => ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrCtTy" => ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "psTy" => ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mHsTy" => fsMultiHsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mVpTy" => fsMultiVpTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mEsTy" => fsMultiEsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mBookTy" => fsMultiSessBookTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "transEntryTy" => fsTransEntryTy KC Γ CCoins T I KR RSt K SS RS M E

def fsMultiHsCache {O : Ops S} {Γ'} (h : Expr O Γ' mHsTy) :
    Expr O Γ' (.tbl (.opt (fsMultiCacheEntryTy KC Γ CCoins T I KR RSt K SS RS M E))) := .fst h
def fsMultiHsTable {O : Ops S} {Γ'} (h : Expr O Γ' mHsTy) :
    Expr O Γ' (.list (fsTableEntryTy KC Γ CCoins T I KR RSt K SS RS M E)) := .fst (.snd h)
def fsMultiHsSessions {O : Ops S} {Γ'} (h : Expr O Γ' mHsTy) :
    Expr O Γ' (.list (.base .i)) := .fst (.snd (.snd h))
def fsMultiHsBook {O : Ops S} {Γ'} (h : Expr O Γ' mHsTy) :
    Expr O Γ' (.tbl (.opt mBookTy)) := .fst (.snd (.snd (.snd h)))
def fsMultiHsLfWin {O : Ops S} {Γ'} (h : Expr O Γ' mHsTy) :
    Expr O Γ' .bool := .snd (.snd (.snd (.snd h)))

def fsMultiHsMk {O : Ops S} {Γ'}
    (ca : Expr O Γ' (.tbl (.opt (fsMultiCacheEntryTy KC Γ CCoins T I KR RSt K SS RS M E))))
    (tb : Expr O Γ' (.list (fsTableEntryTy KC Γ CCoins T I KR RSt K SS RS M E)))
    (se : Expr O Γ' (.list (.base .i)))
    (bk : Expr O Γ' (.tbl (.opt mBookTy)))
    (lw : Expr O Γ' .bool) : Expr O Γ' mHsTy :=
  .pair ca (.pair tb (.pair se (.pair bk lw)))

def fsMultiHsSetCache {O : Ops S} {Γ'} (h : Expr O Γ' mHsTy)
    (ca : Expr O Γ' (.tbl (.opt (fsMultiCacheEntryTy KC Γ CCoins T I KR RSt K SS RS M E)))) :
    Expr O Γ' mHsTy :=
  fsMultiHsMk ca (fsMultiHsTable h) (fsMultiHsSessions h) (fsMultiHsBook h) (fsMultiHsLfWin h)

def fsMultiHsSetTable {O : Ops S} {Γ'} (h : Expr O Γ' mHsTy)
    (tb : Expr O Γ' (.list (fsTableEntryTy KC Γ CCoins T I KR RSt K SS RS M E))) :
    Expr O Γ' mHsTy :=
  fsMultiHsMk (fsMultiHsCache h) tb (fsMultiHsSessions h) (fsMultiHsBook h) (fsMultiHsLfWin h)

def fsMultiHsSetSessions {O : Ops S} {Γ'} (h : Expr O Γ' mHsTy)
    (se : Expr O Γ' (.list (.base .i))) : Expr O Γ' mHsTy :=
  fsMultiHsMk (fsMultiHsCache h) (fsMultiHsTable h) se (fsMultiHsBook h) (fsMultiHsLfWin h)

def fsMultiHsSetBookAt {O : Ops S} {Γ'} (h : Expr O Γ' mHsTy)
    (sIdx : Expr O Γ' .nat) (entry : Expr O Γ' mBookTy) : Expr O Γ' mHsTy :=
  fsMultiHsMk (fsMultiHsCache h) (fsMultiHsTable h) (fsMultiHsSessions h)
    (.tset (fsMultiHsBook h) sIdx (.some entry)) (fsMultiHsLfWin h)

def fsMultiHsGetBookAt {O : Ops S} {Γ'} (h : Expr O Γ' mHsTy)
    (sIdx : Expr O Γ' .nat) : Expr O Γ' mBookTy :=
  rdslExpr =>
    match tget (fsMultiHsBook h) sIdx with
    | none => (false, (0, []))
    | some b => b

def fsMultiHsSetLfWin {O : Ops S} {Γ'} (h : Expr O Γ' mHsTy) (lw : Expr O Γ' .bool) :
    Expr O Γ' mHsTy :=
  fsMultiHsMk (fsMultiHsCache h) (fsMultiHsTable h) (fsMultiHsSessions h) (fsMultiHsBook h) lw

def fsMultiHsEmptyE {O : Ops S} {Γ'} : Expr O Γ' mHsTy :=
  fsMultiHsMk (.tconst .none) .nil .nil (.tconst .none) (.bool false)

def lookupMultiFC (L : ℕ) {Γ'}
    (hE : Expr OO Γ' mHsTy)
    (ikE : Expr OO Γ' (.base .i)) :
    Comp OO IIM Γ' (.prod (.base .k) mHsTy) :=
  rdsl do
    (h0, ik0) ← return (hE, ikE)
    match tableLookupE L (fsMultiHsTable h0) ik0 with
    | none =>
      kNew ← sample (O := OO) (I := IIM) CKASamp.k ()
      return (kNew, fsMultiHsSetTable h0 ((ik0, kNew) :: fsMultiHsTable h0))
    | some kFound =>
      return (kFound, h0)

def regSessMultiE (L : ℕ) {Γ'}
    (hE : Expr OO Γ' mHsTy)
    (ikE : Expr OO Γ' (.base .i)) :
    Expr OO Γ' (.prod .nat mHsTy) :=
  rdslExpr =>
    letE (hE, ikE) fun (h0, ik0) =>
      let ses0 := fsMultiHsSessions h0
      if sessionsMemE L ses0 ik0 then
        (sessionsIdxOfE L ses0 ik0, h0)
      else
        (sessionsLenE L ses0, fsMultiHsSetSessions h0 (sessionsAppendOneE L ses0 ik0))

def regSessOptMultiE (L : ℕ) {Γ'}
    (hE : Expr OO Γ' mHsTy)
    (sidE : Expr OO Γ' (.opt (.base .i))) :
    Expr OO Γ' (.prod (.opt .nat) mHsTy) :=
  rdslExpr =>
    letE (hE, sidE) fun (h0, sid0) =>
      match sid0 with
      | none => (none, h0)
      | some ik =>
        let p := regSessMultiE L h0 ik
        (some p.1, p.2)

def rootFSMultiC (L : ℕ) (mo : Mode) {Γ'}
    (hE : Expr OO Γ' mHsTy)
    (tE : Expr OO Γ' .nat)
    (ikE : Expr OO Γ' (.base .i))
    (σE : Expr OO Γ' (.base .sig)) :
    Comp OO IIM Γ'
      (.prod (.prod (.base .sig) (.prod (.base .k) (.opt (.base .i)))) mHsTy) :=
  rdsl do
    (h0, t0, ik0, σ0) ← return (hE, tE, ikE, σE)
    let pIk := Expr.op (O := OO) CKAOp.prngUp (σ0, ik0)
    if nat mo.tStar < t0 then
      return ((pIk.1, pIk.2, none), h0)
    else if t0 == nat mo.tStar then
      if bool mo.tL.isSome && (t0 == nat mo.tH) then
        ir ← sample (O := OO) (I := IIM) CKASamp.i ()
        kSample ← sample (O := OO) (I := IIM) CKASamp.k ()
        let pIr := Expr.op (O := OO) CKAOp.prngUp (σ0, ir)
        return ((pIr.1, kSample, some ir), h0)
      else
        (kLookup, h1) ← lookupMultiFC L h0 ik0
        return ((pIk.1, kLookup, some ik0), h1)
    else if bool mo.tL.isSome && (t0 == nat mo.tH) then
      ir ← sample (O := OO) (I := IIM) CKASamp.i ()
      let pIr := Expr.op (O := OO) CKAOp.prngUp (σ0, ir)
      return ((pIr.1, pIr.2, none), h0)
    else
      return ((pIk.1, pIk.2, none), h0)

def fsMultiStartSendC (L : ℕ) (mo : Mode) {Γ'}
    (hE : Expr OO Γ' mHsTy)
    (_ctxE : Expr OO Γ' (cGsTy mVpTy))
    (_pE : Expr OO Γ' .bool)
    (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' (.base .γ))
    (σE : Expr OO Γ' (.base .sig))
    (rE : Expr OO Γ' (.opt (.base .ccoins))) :
    Comp OO IIM Γ'
      (.prod (.opt (.prod (.base .γ)
        (.prod (.base .t) (.prod (.base .sig) (.sum (.base .ss) .nat)))))
        mHsTy) :=
  rdsl do
    (h0, t0, γ0, σ0, r0) ← return (hE, tE, γE, σE, rE)
    coins ←
      match r0 with
      | none => sample (O := OO) (I := IIM) CKASamp.ccoins ()
      | some c => return c
    let cOut := Expr.op (O := OO) CKAOp.ckaSend (γ0, coins)
    ((σ', kVal, sid), h1) ← rootFSMultiC L mo h0 t0 cOut.2.2 σ0
    let regP := regSessOptMultiE L h1 sid
    let optIdx := regP.1
    let h2 := regP.2
    let tMsg := cOut.2.1
    let cache' := tset (fsMultiHsCache h2) t0 (some (tMsg, σ', kVal, optIdx))
    let h3 := fsMultiHsSetCache h2 cache'
    let ssv : Expr OO _ (.sum (.base .ss) .nat) :=
      match optIdx with
      | none => .inl (Expr.op (O := OO) CKAOp.fsInitSender kVal)
      | some sIdx => .inr sIdx
    return (some (cOut.1, tMsg, σ', ssv), h3)

def fsMultiStartRecvC (L : ℕ) (mo : Mode) (gMain : Bool) {Γ'}
    (hE : Expr OO Γ' mHsTy)
    (_ctxE : Expr OO Γ' (cGsTy mVpTy))
    (_pE : Expr OO Γ' .bool)
    (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' (.base .γ))
    (σE : Expr OO Γ' (.base .sig))
    (tnE : Expr OO Γ' (.base .t)) :
    Comp OO IIM Γ'
      (.prod (.opt (.opt (.prod (.base .γ) (.prod (.base .sig) (.sum (.base .rs) .nat)))))
        mHsTy) :=
  rdsl do
    (h0, t0, γ0, σ0, tn0) ← return (hE, tE, γE, σE, tnE)
    let honest :=
      match tget (fsMultiHsCache h0) t0 with
      | none => none
      | some (tCached, entry) =>
        if Expr.op (O := OO) CKAOp.eqT (tCached, tn0) then some entry else none
    match honest with
    | none =>
      if bool gMain then
        return (some none, h0)
      else if bool mo.auth && (t0 == nat mo.tStar) then
        if bool (mo.tL.isSome && decide (mo.tStar = mo.tH)) then
          return (none, h0)
        else
          let kk := Expr.op (O := OO) CKAOp.ckaReceive (γ0, tn0)
          (k', h1) ← lookupMultiFC L h0 kk.2
          let regP := regSessMultiE L h1 kk.2
          let sIdx := regP.1
          let h2 := regP.2
          let σ' := (Expr.op (O := OO) CKAOp.prngUp (σ0, kk.2)).1
          return (some (some (kk.1, σ', .inr sIdx)), h2)
      else
        return (some none, h0)
    | some (σc, kVal, optIdx) =>
      let γ' := (Expr.op (O := OO) CKAOp.ckaReceive (γ0, tn0)).1
      let rsv : Expr OO _ (.sum (.base .rs) .nat) :=
        match optIdx with
        | none => .inl (Expr.op (O := OO) CKAOp.fsInitReceiver kVal)
        | some sIdx => .inr sIdx
      return (some (some (γ', σc, rsv)), h0)

def fsMultiFsSendC (Δcka : ℕ) (la : Bool) {Γ'}
    (hE : Expr OO Γ' mHsTy)
    (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (pE : Expr OO Γ' .bool)
    (_tE : Expr OO Γ' .nat)
    (ssvE : Expr OO Γ' (.sum (.base .ss) .nat))
    (hdrE : Expr OO Γ' hdrTy)
    (mE : Expr OO Γ' (.base .msg))
    (pairE : Expr OO Γ' (.opt (.prod (.base .msg) (.base .msg)))) :
    Comp OO IIM Γ' (.prod (.opt (.prod (.sum (.base .ss) .nat) (.base .ct))) mHsTy) :=
  if la then
    rdsl do
      (h0, ctx0, p0, ssv0, hdr0, m0, pair0) ← return (hE, ctxE, pE, ssvE, hdrE, mE, pairE)
      match ssv0 with
      | .inl ss =>
        let o := Expr.op (O := OO) CKAOp.fsSend (ss, hdr0, m0)
        return (some (.inl o.1, o.2), h0)
      | .inr sIdx =>
        let bk := fsMultiHsGetBookAt h0 sIdx
        let sCorr := bk.1
        if !(cSafeChE (raw (2 + Δcka)) ctx0 p0) && !sCorr then
          return (none, h0)
        else
          ctOpt ←
            match pair0 with
            | none => query (O := OO) (I := IIM) FSHdrTag.tr (sIdx, (hdr0, m0))
            | some mPair => query (O := OO) (I := IIM) FSHdrTag.ch (sIdx, (hdr0, mPair))
          match ctOpt with
          | none => return (none, h0)
          | some ct =>
            let cnt' := bk.2.1 + 1
            let tr' := (cnt', hdr0, ct) :: bk.2.2
            return (some (.inr sIdx, ct), fsMultiHsSetBookAt h0 sIdx (sCorr, (cnt', tr')))
  else
    rdsl do
      (h0, ctx0, p0, ssv0, hdr0, m0, pair0) ← return (hE, ctxE, pE, ssvE, hdrE, mE, pairE)
      match ssv0 with
      | .inl ss =>
        let o := Expr.op (O := OO) CKAOp.fsSend (ss, hdr0, m0)
        return (some (.inl o.1, o.2), h0)
      | .inr sIdx =>
        let bk := fsMultiHsGetBookAt h0 sIdx
        let sCorr := bk.1
        let cnt := bk.2.1
        let trs := bk.2.2
        (ok, h1) ←
          if !(cSafeChE (raw (2 + Δcka)) ctx0 p0) && !sCorr then
            csOpt ← query (O := OO) (I := IIM) FSHdrTag.cs (sIdx, ())
            match csOpt with
            | none => return (false, h0)
            | some _ => return (true, fsMultiHsSetBookAt h0 sIdx (true, (cnt, trs)))
          else
            return (true, h0)
        if !ok then
          return (none, h1)
        else
          ctOpt ←
            match pair0 with
            | none => query (O := OO) (I := IIM) FSHdrTag.tr (sIdx, (hdr0, m0))
            | some mPair => query (O := OO) (I := IIM) FSHdrTag.ch (sIdx, (hdr0, mPair))
          match ctOpt with
          | none => return (none, h1)
          | some ct =>
            let bk1 := fsMultiHsGetBookAt h1 sIdx
            let cnt' := bk1.2.1 + 1
            let tr' := (cnt', hdr0, ct) :: bk1.2.2
            return (some (.inr sIdx, ct), fsMultiHsSetBookAt h1 sIdx (bk1.1, (cnt', tr')))

def fsMultiFsRecvC (L B : ℕ) (la : Bool) {Γ'}
    (hE : Expr OO Γ' mHsTy)
    (_ctxE : Expr OO Γ' (cGsTy mVpTy))
    (_pE : Expr OO Γ' .bool)
    (_tE : Expr OO Γ' .nat)
    (rsvE : Expr OO Γ' (.sum (.base .rs) .nat))
    (hdrE : Expr OO Γ' hdrTy)
    (eE : Expr OO Γ' (.base .ct))
    (recE : Expr OO Γ' (.opt cRecTy)) :
    Comp OO IIM Γ'
      (.prod (.opt (.opt (.prod (.sum (.base .rs) .nat) (.prod .nat (.base .msg))))) mHsTy) :=
  rdsl do
    (h0, rsv0, hdr0, e0, rec0) ← return (hE, rsvE, hdrE, eE, recE)
    match rsv0 with
    | .inl rs =>
      match Expr.op (O := OO) (CKAOp.fsReceive B) (rs, hdr0, e0) with
      | none => return (some none, h0)
      | some (rs', idxMsg) =>
        return (some (some (.inl rs', idxMsg)), h0)
    | .inr sIdx =>
      let bk0 := fsMultiHsGetBookAt h0 sIdx
      let sCorr0 := bk0.1
      let cnt0 := bk0.2.1
      let trs0 := bk0.2.2
      let matched := fsTransFindE L trs0 (hdr0, e0)
      resOpt ←
        match matched with
        | none => query (O := OO) (I := IIM) FSHdrTag.ij (sIdx, (hdr0, e0))
        | some _ => query (O := OO) (I := IIM) FSHdrTag.dl (sIdx, (hdr0, e0))
      match resOpt with
      | none => return (none, h0)
      | some resSum =>
        match resSum with
        | .inl _ => return (some none, h0)
        | .inr (msgIdx, mo') =>
          let isLookaheadInj :=
            match matched with
            | none => cnt0 < msgIdx
            | some _ => false
          if bool la && isLookaheadInj then
            return (none, fsMultiHsSetLfWin h0 true)
          else
            let drop :=
              match matched with
              | none => msgIdx
              | some entry => entry.1
            let trs' := fsTransFilterE L trs0 drop
            let h4 := fsMultiHsSetBookAt h0 sIdx (sCorr0, (cnt0, trs'))
            let outE :=
              match mo' with
              | none =>
                match rec0 with
                | none => none
                | some r => some (some (.inr sIdx, msgIdx, cRecMsg r))
              | some msg => some (some (.inr sIdx, msgIdx, msg))
            return (outE, h4)

def fsMultiCommitC {Γ'}
    (hE : Expr OO Γ' mHsTy)
    (_ctxE : Expr OO Γ' (cGsTy mVpTy))
    (_pE : Expr OO Γ' .bool)
    (_oldE newE : Expr OO Γ' mVpTy) :
    Comp OO IIM Γ' (.prod (.opt mVpTy) mHsTy) :=
  rdsl do
    return (some newE, hE)

def unliftMultiEntryE {Γ'}
    (entryE : Expr OO Γ' (.opt (.sum (.base .rs) .nat))) :
    Expr OO Γ' (.opt (.base .rs)) :=
  rdslExpr =>
    match entryE with
    | none => none
    | some sumV =>
      match sumV with
      | .inl rs => some rs
      | .inr _ => none

def unliftMultiVRE (L : ℕ) {Γ'}
    (vRE : Expr OO Γ' (.tbl (.opt (.sum (.base .rs) .nat))))
    (rngE : Expr OO Γ' (.list .nat)) :
    Expr OO Γ' (.tbl (.opt (.base .rs))) :=
  rdslExpr =>
    letE (vRE, rngE) fun (vR0, rng0) =>
      foldrB L rng0 (tconst none) fun t acc =>
        tset acc t (unliftMultiEntryE (tget vR0 t))

def fsMultiRevealC (L : ℕ) (mo : Mode) (la : Bool) {Γ'}
    (hE : Expr OO Γ' mHsTy)
    (_ctxE : Expr OO Γ' (cGsTy mVpTy))
    (_pE : Expr OO Γ' .bool)
    (vpE : Expr OO Γ' mVpTy) :
    Comp OO IIM Γ' (.prod (.opt psTy) mHsTy) :=
  if la then
    rdsl do
      (h0, vp0) ← return (hE, vpE)
      let ssOptOpt :=
        match vpVS vp0 with
        | none => some none
        | some ssv =>
          match ssv with
          | .inl ss => some (some ss)
          | .inr _ => none
      match ssOptOpt with
      | none => return (none, h0)
      | some ssReal =>
        let rStarAbort :=
          match tget (vpVR vp0) (nat mo.tStar) with
          | none => false
          | some rsv =>
            match rsv with
            | .inl _ => false
            | .inr _ => true
        if rStarAbort then
          return (none, h0)
        else
          rng ← rangeListC (O' := OO) (I' := IIM) L
          let vR' := unliftMultiVRE L (vpVR vp0) rng
          return (some (realPartyE vp0 (vpΓ vp0) (vpRoot vp0) ssReal vR'), h0)
  else
    rdsl do
      (h0, vp0) ← return (hE, vpE)
      (ssOptOpt, h1) ←
        match vpVS vp0 with
        | none => return (some none, h0)
        | some ssv =>
          match ssv with
          | .inl ss => return (some (some ss), h0)
          | .inr sIdx =>
            csOpt ← query (O := OO) (I := IIM) FSHdrTag.cs (sIdx, ())
            match csOpt with
            | none => return (none, h0)
            | some ss =>
              let bk0 := fsMultiHsGetBookAt h0 sIdx
              return (some (some ss), fsMultiHsSetBookAt h0 sIdx (true, bk0.2))
      match ssOptOpt with
      | none => return (none, h1)
      | some ssReal =>
        let rStarAbort :=
          match tget (vpVR vp0) (nat mo.tStar) with
          | none => false
          | some rsv =>
            match rsv with
            | .inl _ => false
            | .inr _ => true
        if rStarAbort then
          return (none, h1)
        else
          rng ← rangeListC (O' := OO) (I' := IIM) L
          let vR' := unliftMultiVRE L (vpVR vp0) rng
          return (some (realPartyE vp0 (vpΓ vp0) (vpRoot vp0) ssReal vR'), h1)

/-- Costed multi-session `HooksC` bundle for `redFSAuthMultiStage2Prog`. -/
def hooksFSMultiC (L B Δcka : ℕ) (mo : Mode) (gMain la : Bool) :
    HooksC OO IIM (.base .γ) (.base .sig) (.sum (.base .ss) .nat) (.sum (.base .rs) .nat) mHsTy where
  startSend := fsMultiStartSendC L mo
  startRecv := fsMultiStartRecvC L mo gMain
  fsSend := fsMultiFsSendC Δcka la
  fsRecv := fsMultiFsRecvC L B la
  commit := fsMultiCommitC
  reveal := fsMultiRevealC L mo la

def initFSMultiEStateC (L : ℕ) (mo : Mode) {Γ'} (bE : Expr OO Γ' .bool) :
    Comp OO IIM Γ' mEsTy :=
  rdsl do
    b0 ← return bE
    kr ← sample (O := OO) (I := IIM) CKASamp.kr ()
    kc ← sample (O := OO) (I := IIM) CKASamp.kc ()
    ((σ, kVal, sid), h1) ←
      rootFSMultiC L mo fsMultiHsEmptyE 0
        (Expr.op (O := OO) CKAOp.lamI ())
        (Expr.op (O := OO) CKAOp.prngInit kr)
    let regP := regSessOptMultiE L h1 sid
    let optIdx := regP.1
    let h2 := regP.2
    let ssv0 : Expr OO _ (.sum (.base .ss) .nat) :=
      match optIdx with
      | none => .inl (Expr.op (O := OO) CKAOp.fsInitSender kVal)
      | some sIdx => .inr sIdx
    let rsv0 : Expr OO _ (.sum (.base .rs) .nat) :=
      match optIdx with
      | none => .inl (Expr.op (O := OO) CKAOp.fsInitReceiver kVal)
      | some sIdx => .inr sIdx
    let pAB := mkPartiesE
      (Expr.op (O := OO) CKAOp.ckaInitA kc)
      (Expr.op (O := OO) CKAOp.ckaInitB kc)
      σ ssv0 rsv0
    return (esMk (cGsInitE (vpT := mVpTy) pAB.1 pAB.2 b0) h2 false)

def isHonestHdrFSMultiE {Γ'} (hE : Expr OO Γ' mHsTy) (hdrE : Expr OO Γ' hdrTy) :
    Expr OO Γ' .bool :=
  rdslExpr =>
    letE (hE, hdrE) fun (h0, hdr0) =>
      match tget (fsMultiHsCache h0) hdr0.1 with
      | none => false
      | some (tCached, _) =>
        match hdr0.2 with
        | none => false
        | some tn0 => Expr.op (O := OO) CKAOp.eqT (tCached, tn0)

def finishFSMultiE (L Δ : ℕ) (pol : Policy) (la : Bool) {Γ'}
    (es : Expr OO Γ' mEsTy) : Expr OO Γ' .bool :=
  if la then fsMultiHsLfWin (esH es)
  else authOutE L Δ pol es

/-- Stage-2 multi-session `redFSAuth` reduction (`gMain = true` for honest-header mode, `false` for forged-header mode). -/
def redFSAuthMultiStage2Prog (L B Δcka qep maxSkip : ℕ) (gMain la : Bool)
    (tL : Option ℕ) (t : ℕ) :
    CostedReduction OO IIM
      (SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (prngSMCodec KC Γ CCoins T I KR RSt K SS RS M E)
      .unit .unit .bool .bool where
  σ := mEsTy
  init := rdsl [_] do
    es ← initFSMultiEStateC L (raw ⟨true, tL, t⟩) false
    return ((), es)
  handle :=
    if gMain then
      rdsl [es0, q0] do
        implEC (raw (hooksFSMultiC L B Δcka ⟨true, tL, t⟩ true la)) L (raw (2 + Δcka)) qep maxSkip
          (raw (modeCfgEC OO ⟨true, tL, t⟩)) (raw (⟨true, tL, t⟩ : Mode).policy) es0 q0
    else
      rdsl [es0, q0] do
        let wasWin := cGsWin (esG es0)
        (out, es') ← implEC (raw (hooksFSMultiC L B Δcka ⟨true, tL, t⟩ false la)) L (raw (2 + Δcka))
          qep maxSkip (raw (modeCfgEC OO ⟨true, tL, t⟩)) (raw (⟨true, tL, t⟩ : Mode).policy) es0 q0
        let suppressHonestWin :=
          match q0 with
          | .inl qL =>
            match qL with
            | .inl _ => false
            | .inr x => isHonestHdrFSMultiE (esH es0) x.2.1
          | .inr _ => false
        let esFinal :=
          if !wasWin && cGsWin (esG es') && suppressHonestWin then
            esSetG es' (cGsSetWin (esG es') false)
          else es'
        return (out, esFinal)
  finish := rdsl [es, _] do
    return (finishFSMultiE L (raw (2 + Δcka)) (raw (⟨true, tL, t⟩ : Mode).policy) la es)

@[simp] theorem lookupMultiFC_queries (L : ℕ) (w : FSHdrTag → ℕ) {Γ'}
    (hE : Expr OO Γ' mHsTy) (ikE : Expr OO Γ' (.base .i)) :
    (lookupMultiFC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L hE ikE).queries w (fun _ => 0) = 0 := by
  simp [lookupMultiFC, Comp.queries]

@[simp] theorem rootFSMultiC_queries (L : ℕ) (mo : Mode) (w : FSHdrTag → ℕ) {Γ'}
    (hE : Expr OO Γ' mHsTy) (tE : Expr OO Γ' .nat)
    (ikE : Expr OO Γ' (.base .i)) (σE : Expr OO Γ' (.base .sig)) :
    (rootFSMultiC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L mo hE tE ikE σE).queries w (fun _ => 0) = 0 := by
  simp [rootFSMultiC, Comp.queries]

@[simp] theorem fsMultiStartSendC_queries (L : ℕ) (mo : Mode) (w : FSHdrTag → ℕ) {Γ'}
    (hE : Expr OO Γ' mHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' (.base .γ)) (σE : Expr OO Γ' (.base .sig))
    (rE : Expr OO Γ' (.opt (.base .ccoins))) :
    (fsMultiStartSendC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L mo hE ctxE pE tE γE σE rE).queries w (fun _ => 0) = 0 := by
  simp [fsMultiStartSendC, Comp.queries]

@[simp] theorem fsMultiStartRecvC_queries (L : ℕ) (mo : Mode) (gMain : Bool) (w : FSHdrTag → ℕ) {Γ'}
    (hE : Expr OO Γ' mHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' (.base .γ)) (σE : Expr OO Γ' (.base .sig))
    (tnE : Expr OO Γ' (.base .t)) :
    (fsMultiStartRecvC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L mo gMain hE ctxE pE tE γE σE tnE).queries
      w (fun _ => 0) = 0 := by
  cases gMain <;> simp [fsMultiStartRecvC, Comp.queries]

@[simp] theorem fsMultiFsSendC_queries (Δcka : ℕ) (la : Bool) {Γ'}
    (hE : Expr OO Γ' mHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (ssvE : Expr OO Γ' (.sum (.base .ss) .nat)) (hdrE : Expr OO Γ' hdrTy)
    (mE : Expr OO Γ' (.base .msg))
    (pairE : Expr OO Γ' (.opt (.prod (.base .msg) (.base .msg)))) :
    (fsMultiFsSendC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) Δcka la hE ctxE pE tE ssvE hdrE mE pairE).queries
      (fun _ => 1) (fun _ => 0) = if la then 1 else 2 := by
  cases la <;> simp [fsMultiFsSendC, Comp.queries]

@[simp] theorem fsMultiFsSendC_decQueries (Δcka : ℕ) (la : Bool) {Γ'}
    (hE : Expr OO Γ' mHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (ssvE : Expr OO Γ' (.sum (.base .ss) .nat)) (hdrE : Expr OO Γ' hdrTy)
    (mE : Expr OO Γ' (.base .msg))
    (pairE : Expr OO Γ' (.opt (.prod (.base .msg) (.base .msg)))) :
    (fsMultiFsSendC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) Δcka la hE ctxE pE tE ssvE hdrE mE pairE).queries
      fsHdrDecWt (fun _ => 0) = 0 := by
  cases la <;> simp [fsMultiFsSendC, fsHdrDecWt, Comp.queries]

@[simp] theorem fsMultiFsRecvC_queries (L B : ℕ) (la : Bool) {Γ'}
    (hE : Expr OO Γ' mHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (rsvE : Expr OO Γ' (.sum (.base .rs) .nat)) (hdrE : Expr OO Γ' hdrTy)
    (eE : Expr OO Γ' (.base .ct)) (recE : Expr OO Γ' (.opt cRecTy)) :
    (fsMultiFsRecvC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B la hE ctxE pE tE rsvE hdrE eE recE).queries
      (fun _ => 1) (fun _ => 0) = 1 := by
  cases la <;> simp [fsMultiFsRecvC, Comp.queries]

@[simp] theorem fsMultiFsRecvC_decQueries (L B : ℕ) (la : Bool) {Γ'}
    (hE : Expr OO Γ' mHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (rsvE : Expr OO Γ' (.sum (.base .rs) .nat)) (hdrE : Expr OO Γ' hdrTy)
    (eE : Expr OO Γ' (.base .ct)) (recE : Expr OO Γ' (.opt cRecTy)) :
    (fsMultiFsRecvC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B la hE ctxE pE tE rsvE hdrE eE recE).queries
      fsHdrDecWt (fun _ => 0) = 1 := by
  cases la <;> simp [fsMultiFsRecvC, fsHdrDecWt, Comp.queries]

@[simp] theorem fsMultiCommitC_queries (w : FSHdrTag → ℕ) {Γ'}
    (hE : Expr OO Γ' mHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (pE : Expr OO Γ' .bool) (oldE newE : Expr OO Γ' mVpTy) :
    (fsMultiCommitC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) hE ctxE pE oldE newE).queries w (fun _ => 0) = 0 := by
  simp [fsMultiCommitC, Comp.queries]

@[simp] theorem rangeListC_multi_queries (L : ℕ) (w : FSHdrTag → ℕ) {Γ'} :
    (rangeListC (O' := OO) (I' := IIM) (Γ' := Γ') L).queries w (fun _ => 0) = 0 := by
  induction L <;> simp [rangeListC, Comp.queries, *]

@[simp] theorem fsMultiRevealC_queries (L : ℕ) (mo : Mode) (la : Bool) {Γ'}
    (hE : Expr OO Γ' mHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (pE : Expr OO Γ' .bool) (vpE : Expr OO Γ' mVpTy) :
    (fsMultiRevealC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L mo la hE ctxE pE vpE).queries
      (fun _ => 1) (fun _ => 0) = if la then 0 else 1 := by
  cases la <;> simp [fsMultiRevealC, Comp.queries]

@[simp] theorem fsMultiRevealC_decQueries (L : ℕ) (mo : Mode) (la : Bool) {Γ'}
    (hE : Expr OO Γ' mHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (pE : Expr OO Γ' .bool) (vpE : Expr OO Γ' mVpTy) :
    (fsMultiRevealC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L mo la hE ctxE pE vpE).queries
      fsHdrDecWt (fun _ => 0) = 0 := by
  cases la <;> simp [fsMultiRevealC, fsHdrDecWt, Comp.queries]

@[simp] theorem implEC_hooksFSMultiC_queries (L B Δcka qep maxSkip : ℕ) (mo : Mode)
    (gMain la : Bool) {Γ'}
    (es : Expr OO Γ' mEsTy)
    (q : Expr OO Γ' (ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E)) :
    (implEC (hooksFSMultiC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δcka mo gMain la)
      L (2 + Δcka) qep maxSkip (modeCfgEC OO mo) mo.policy es q).queries
      (fun _ => 1) (fun _ => 0) = if la then 1 else 2 := by
  cases la <;> simp [implEC, transmitEC, challEC, deliverEC, injectEC, corrEC,
    vSendC, vSendStep1C, vRecvC, vRecvStep1C, commitEC, hooksFSMultiC, Comp.queries]

@[simp] theorem implEC_hooksFSMultiC_decQueries (L B Δcka qep maxSkip : ℕ) (mo : Mode)
    (gMain la : Bool) {Γ'}
    (es : Expr OO Γ' mEsTy)
    (q : Expr OO Γ' (ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E)) :
    (implEC (hooksFSMultiC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δcka mo gMain la)
      L (2 + Δcka) qep maxSkip (modeCfgEC OO mo) mo.policy es q).queries
      fsHdrDecWt (fun _ => 0) = 1 := by
  simp [implEC, transmitEC, challEC, deliverEC, injectEC, corrEC,
    vSendC, vSendStep1C, vRecvC, vRecvStep1C, commitEC, hooksFSMultiC, Comp.queries]

@[simp] theorem initFSMultiEStateC_queries (L : ℕ) (mo : Mode) (w : FSHdrTag → ℕ)
    {Γ'} (bE : Expr OO Γ' .bool) :
    (initFSMultiEStateC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L mo bE).queries w (fun _ => 0) = 0 := by
  simp [initFSMultiEStateC, Comp.queries]

@[simp] theorem redFSAuthMultiStage2Prog_totalQueries_eq (L B Δcka qep maxSkip : ℕ)
    (gMain la : Bool) (tL : Option ℕ) (t q : ℕ) :
    (redFSAuthMultiStage2Prog (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L B Δcka qep maxSkip gMain la tL t).totalQueries (fun _ => 1) (fun _ => 0) q =
      q * (if la then 1 else 2) := by
  cases gMain <;>
    simp [CostedReduction.totalQueries, redFSAuthMultiStage2Prog, Comp.queries]

theorem redFSAuthMultiStage2Prog_totalQueries (L B Δcka qep maxSkip : ℕ)
    (gMain la : Bool) (tL : Option ℕ) (t q : ℕ) :
    (redFSAuthMultiStage2Prog (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L B Δcka qep maxSkip gMain la tL t).totalQueries (fun _ => 1) (fun _ => 0) q ≤ q * 2 := by
  rw [redFSAuthMultiStage2Prog_totalQueries_eq]
  (cases la <;> simp); omega

@[simp] theorem redFSAuthMultiStage2Prog_totalDecQueries (L B Δcka qep maxSkip : ℕ)
    (gMain la : Bool) (tL : Option ℕ) (t q : ℕ) :
    (redFSAuthMultiStage2Prog (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L B Δcka qep maxSkip gMain la tL t).totalQueries fsHdrDecWt (fun _ => 0) q = q := by
  cases gMain <;>
    simp [CostedReduction.totalQueries, redFSAuthMultiStage2Prog, Comp.queries]

theorem redFSAuthMultiStage2Prog_totalCost (L B Δcka qep maxSkip : ℕ)
    (gMain la : Bool) (tL : Option ℕ) (t q : ℕ) :
    (redFSAuthMultiStage2Prog (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      L B Δcka qep maxSkip gMain la tL t).totalCost q =
      (initFSMultiEStateC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L ⟨true, tL, t⟩ (.bool false : Expr OO [.unit] .bool)).cost + 6 +
      (finishFSMultiE L (2 + Δcka) (⟨true, tL, t⟩ : Mode).policy la
        (.v0 : Expr OO [mEsTy, .bool] mEsTy)).cost +
      q * (((redFSAuthMultiStage2Prog (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
          (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
          (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK)
          L B Δcka qep maxSkip gMain la tL t).handle).cost + 12) := by
  have hV0 : ∀ {Γ' τ}, (Expr.v0 : Expr OO (τ :: Γ') τ).cost = 1 := rfl
  simp only [CostedReduction.totalCost, redFSAuthMultiStage2Prog, prngSMCodec, ckaSMCodec,
    fsaeadMultiHeaderAdIface, prngSamplers, ckaSamplers, Comp.cost, Expr.cost, hV0]
  rw [max_eq_right (by omega)]
  omega

end HooksFSMultiC

@[reducible] def FSMultiSpec (SS RS T M E : Type) :=
  OracleSpec.sigma (fun _ : ℕ => FSAEAD.spec SS RS (Header T) M E)

structure FSMultiBook (T E : Type) where
  sCorr : Bool := false
  fsCount : ℕ := 0
  fsTrans : List (ℕ × Header T × E) := []

structure FSMultiState (T Sig K I E : Type) where
  cache : ℕ → Option (T × Sig × K × Option ℕ) := fun _ => none
  table : List (I × K) := []
  sessions : List I := []
  book : ℕ → Option (FSMultiBook T E) := fun _ => none
  lfWin : Bool := false

def fsMultiHsEnc (h : FSMultiState T RSt K I E) :
    (fsMultiHsTy KC Γ CCoins T I KR RSt K SS RS M E).denote :=
  (h.cache, h.table, h.sessions,
   (fun sIdx => (h.book sIdx).map fun b => (b.sCorr, b.fsCount, b.fsTrans)),
   h.lfWin)

def fsMultiHsDec (v : (fsMultiHsTy KC Γ CCoins T I KR RSt K SS RS M E).denote) :
    FSMultiState T RSt K I E :=
  { cache := v.1
    table := v.2.1
    sessions := v.2.2.1
    book := fun sIdx => (v.2.2.2.1 sIdx).map fun b => ⟨b.1, b.2.1, b.2.2⟩
    lfWin := v.2.2.2.2 }

@[simp] theorem fsMultiHsDec_fsMultiHsEnc (h : FSMultiState T RSt K I E) :
    fsMultiHsDec (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (SS := SS) (RS := RS) (M := M)
      (fsMultiHsEnc h) = h := by
  cases h with
  | mk ca tb se bk lw =>
    simp only [fsMultiHsEnc, fsMultiHsDec, FSMultiState.mk.injEq, true_and, and_true]
    funext sIdx
    cases bk sIdx <;> rfl

@[simp] theorem fsMultiHsEnc_fsMultiHsDec
    (v : (fsMultiHsTy KC Γ CCoins T I KR RSt K SS RS M E).denote) :
    fsMultiHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (SS := SS) (RS := RS) (M := M)
      (fsMultiHsDec v) = v := by
  rcases v with ⟨ca, tb, se, bk, lw⟩
  simp only [fsMultiHsEnc, fsMultiHsDec, Prod.mk.injEq, true_and, and_true]
  funext sIdx
  rcases bk sIdx with _ | ⟨sc, cnt, tr⟩ <;> rfl

def liftFSMulti {Sig K I : Type} (sIdx : ℕ) {α : Type}
    (x : FSAEAD.AdversaryComp SS RS (Header T) M E α) :
    HM (FSMultiSpec SS RS T M E) (FSMultiState T Sig K I E) α :=
  let liftImpl : QueryImpl (unifSpec + FSAEAD.spec SS RS (Header T) M E)
      (TComp (FSMultiSpec SS RS T M E)) := fun
    | .inl n => query (spec := unifSpec + FSMultiSpec SS RS T M E) (.inl n)
    | .inr q => query (spec := unifSpec + FSMultiSpec SS RS T M E) (.inr ⟨sIdx, q⟩)
  StateT.lift (simulateQ liftImpl x)

def lookupMultiF [DecidableEq I] [SampleableType K] {Sig : Type} (Ik : I) :
    HM (FSMultiSpec SS RS T M E) (FSMultiState T Sig K I E) K := do
  match (← get).table.lookup Ik with
  | some k => return k
  | none =>
    let k ← StateT.lift (sampleT K)
    modify fun s => { s with table := (Ik, k) :: s.table }
    return k

def regSessMulti [DecidableEq I] {Sig : Type} (Ik : I) :
    HM (FSMultiSpec SS RS T M E) (FSMultiState T Sig K I E) ℕ := do
  let s ← get
  if Ik ∈ s.sessions then return s.sessions.idxOf Ik
  else
    set { s with sessions := s.sessions ++ [Ik] }
    return s.sessions.length

def regSessOptMulti [DecidableEq I] {Sig : Type} (sid : Option I) :
    HM (FSMultiSpec SS RS T M E) (FSMultiState T Sig K I E) (Option ℕ) :=
  match sid with
  | none => pure none
  | some Ik => some <$> regSessMulti Ik

def rootFSMulti [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR RSt I K) (mo : Mode) (t : ℕ) (Ik : I) (σ : RSt) :
    HM (FSMultiSpec SS RS T M E) (FSMultiState T RSt K I E) (RSt × K × Option I) := do
  if mo.tStar < t then
    let p := prng.up σ Ik
    return (p.1, p.2, none)
  else if t = mo.tStar then
    if mo.tL.isSome && t = mo.tH then
      let Ir ← StateT.lift (sampleT I)
      let k ← StateT.lift (sampleT K)
      return ((prng.up σ Ir).1, k, some Ir)
    else
      let k ← lookupMultiF Ik
      return ((prng.up σ Ik).1, k, some Ik)
  else if mo.tL.isSome && t = mo.tH then
    let Ir ← StateT.lift (sampleT I)
    let p := prng.up σ Ir
    return (p.1, p.2, none)
  else
    let p := prng.up σ Ik
    return (p.1, p.2, none)

def hooksFSMulti [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (mo : Mode) (gMain la : Bool) :
    Hooks (FSMultiSpec SS RS T M E) (FSMultiState T RSt K I E)
      Γ T RSt SS RS M E CCoins Γ RSt (SS ⊕ ℕ) (RS ⊕ ℕ) where
  startSend _ _ t γ σ r := do
    let coins ← match r with
      | some c => pure c
      | none => StateT.lift (sampleT CCoins)
    let c := cka.send γ coins
    let (σ', k, sid) ← rootFSMulti prng mo t c.2.2 σ
    let optIdx ← regSessOptMulti sid
    modify fun s => { s with cache := Function.update s.cache t (some (c.2.1, σ', k, optIdx)) }
    let ssv : SS ⊕ ℕ := match optIdx with
      | none => .inl (fs.initSender k)
      | some sIdx => .inr sIdx
    return some (c.1, c.2.1, σ', ssv)
  startRecv _ _ t γ σ Tn := do
    let honest := match (← get).cache t with
      | some (Tc, σc, k, optIdx) => if Tc = Tn then some (σc, k, optIdx) else none
      | none => none
    match honest with
    | some (σc, k, optIdx) =>
      let rsv : RS ⊕ ℕ := match optIdx with
        | none => .inl (fs.initReceiver k)
        | some sIdx => .inr sIdx
      return some (some ((cka.receive γ Tn).1, σc, rsv))
    | none =>
      if gMain then return some none
      else if mo.auth && t = mo.tStar then
        if mo.tL.isSome && mo.tStar = mo.tH then return none
        let kk := cka.receive γ Tn
        let _ ← lookupMultiF kk.2
        let sIdx ← regSessMulti kk.2
        return some (some (kk.1, (prng.up σ kk.2).1, .inr sIdx))
      else return some none
  fsSend ctx P _ ssv h m pair := do
    match ssv with
    | .inl ss =>
      let o := fs.send ss h m
      return some (.inl o.1, o.2)
    | .inr sIdx =>
      let s ← get
      let bk := (s.book sIdx).getD {}
      let ok ← if !(ctx.safeCh (2 + Δcka) P) && !bk.sCorr then do
          if la then pure false
          else
            match ← liftFSMulti sIdx (FSAEAD.corruptSenderQuery (ReceiverState := RS)
                (AssocData := Header T) (Message := M) (Ciphertext := E)) with
            | none => pure false
            | some _ =>
              modify fun s =>
                let b := (s.book sIdx).getD {}
                { s with book := Function.update s.book sIdx (some { b with sCorr := true }) }
              pure true
        else pure true
      if !ok then return none
      let e? ← match pair with
        | some (m₀, m₁) =>
          liftFSMulti sIdx (FSAEAD.challengeQuery (SenderState := SS) (ReceiverState := RS)
            h m₀ m₁)
        | none =>
          liftFSMulti sIdx (FSAEAD.transmitQuery (SenderState := SS) (ReceiverState := RS) h m)
      match e? with
      | none => return none
      | some e =>
        modify fun s =>
          let b := (s.book sIdx).getD {}
          let cnt' := b.fsCount + 1
          let b' : FSMultiBook T E := { b with fsCount := cnt', fsTrans := (cnt', h, e) :: b.fsTrans }
          { s with book := Function.update s.book sIdx (some b') }
        return some (.inr sIdx, e)
  fsRecv _ _ _ rsv h e rec := do
    match rsv with
    | .inl rs => return some ((fs.receive rs h e).map fun o => (.inl o.1, o.2.1, o.2.2))
    | .inr sIdx =>
      let s ← get
      let bk := (s.book sIdx).getD {}
      let matched := bk.fsTrans.find? (fun x => x.2 == (h, e))
      let res ← if matched.isSome then
          liftFSMulti sIdx (FSAEAD.deliverQuery (SenderState := SS) (ReceiverState := RS) h e)
        else
          liftFSMulti sIdx (FSAEAD.injectQuery (SenderState := SS) (ReceiverState := RS) h e)
      match res with
      | none => return none
      | some .rejected => return some none
      | some (.accepted i mo') =>
        if la && matched.isNone && bk.fsCount < i then
          modify fun s => { s with lfWin := true }
          return none
        else
          let drop := (matched.map (·.1)).getD i
          modify fun s =>
            let b := (s.book sIdx).getD {}
            let b' : FSMultiBook T E := { b with fsTrans := b.fsTrans.filter (·.1 != drop) }
            { s with book := Function.update s.book sIdx (some b') }
          match mo', rec with
          | some m, _ => return some (some (.inr sIdx, i, m))
          | none, some r => return some (some (.inr sIdx, i, r.msg))
          | none, none => return none
  commit _ _ _ new := pure (some new)
  reveal _ _ vp := do
    let vS? : Option (Option SS) ← match vp.vS with
      | none => pure (some none)
      | some (.inl ss) => pure (some (some ss))
      | some (.inr sIdx) =>
        if la then pure none
        else do
          match ← liftFSMulti sIdx (FSAEAD.corruptSenderQuery (ReceiverState := RS)
              (AssocData := Header T) (Message := M) (Ciphertext := E)) with
          | none => pure none
          | some ss =>
            modify fun s =>
              let b := (s.book sIdx).getD {}
              { s with book := Function.update s.book sIdx (some { b with sCorr := true }) }
            pure (some (some ss))
    match vS? with
    | none => return none
    | some vS =>
      let abortRecv := match vp.vR mo.tStar with
        | some (.inr _) => true
        | _ => false
      if abortRecv then return none
      else
        let vR : ℕ → Option RS := fun t =>
          match vp.vR t with
          | some (.inl rs) => some rs
          | _ => none
        return some (realParty vp vp.γ vp.root vS vR)

def initFSMultiRaw [DecidableEq I]
    [SampleableType KR] [SampleableType KC] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (mo : Mode) (b : Bool) :
    TComp (FSMultiSpec SS RS T M E)
      (EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E)
        (FSMultiState T RSt K I E)) := do
  let kr ← sampleT KR
  let kc ← sampleT KC
  let ((σ, k, sid), h₁) ←
    (rootFSMulti (T := T) (SS := SS) (RS := RS) (M := M) (E := E)
      prng mo 0 lam (prng.init kr)).run {}
  let (optIdx, h₂) ←
    (regSessOptMulti (T := T) (Sig := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E) sid).run h₁
  let ssv0 : SS ⊕ ℕ := match optIdx with
    | none => .inl (fs.initSender k)
    | some sIdx => .inr sIdx
  let rsv0 : RS ⊕ ℕ := match optIdx with
    | none => .inl (fs.initReceiver k)
    | some sIdx => .inr sIdx
  let pAB := mkParties (T := T) (cka.initA kc) (cka.initB kc) σ ssv0 rsv0
  return {
    g := { st := fun | .A => pAB.1 | .B => pAB.2, b := b }
    h := h₂ }

def isHonestHdrFSMulti [DecidableEq T] {Sig K I E : Type}
    (h : FSMultiState T Sig K I E) (hdr : Header T) : Bool :=
  match h.cache hdr.1, hdr.2 with
  | some (Tc, _), some Tn => Tc == Tn
  | _, _ => false

def implEMultiStage2 [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (gMain la : Bool) (tL : Option ℕ) (t : ℕ) :
    QueryImpl (unifSpec + SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (StateT (EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E)
        (FSMultiState T RSt K I E)) (TComp (FSMultiSpec SS RS T M E))) :=
  if gMain then
    implE (hooksFSMulti cka prng fs Δcka ⟨true, tL, t⟩ true la)
      (2 + Δcka) qep fs.maxSkip (⟨true, tL, t⟩ : Mode).cfg (⟨true, tL, t⟩ : Mode).policy
  else
    fun q => do
      let es₀ ← get
      let wasWin := es₀.g.win
      let out ←
        (implE (hooksFSMulti cka prng fs Δcka ⟨true, tL, t⟩ false la)
          (2 + Δcka) qep fs.maxSkip (⟨true, tL, t⟩ : Mode).cfg (⟨true, tL, t⟩ : Mode).policy) q
      let es' ← get
      let suppress := match q with
        | .inr (.inl (.inr (_P, hdr, _e))) => isHonestHdrFSMulti es₀.h hdr
        | _ => false
      if !wasWin && es'.g.win && suppress then
        set { es' with g := { es'.g with win := false } }
      return out

/-- Shallow multi-session Stage-2 FS-AEAD authenticity reduction. -/
def redFSAuthMultiStage2 [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (Δcka qep : ℕ) (gMain la : Bool) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversary Γ T RSt SS RS M CCoins E) :
    TComp (FSMultiSpec SS RS T M E) Bool := do
  let es₀ ← initFSMultiRaw cka prng fs lam ⟨true, tL, t⟩ false
  let (_, es) ←
    (simulateQ (implEMultiStage2 cka prng fs Δcka qep gMain la tL t) A).run es₀
  return (if la then es.h.lfWin else authOut (2 + Δcka) (⟨true, tL, t⟩ : Mode).policy es)

def FSMultiHBounded (L : ℕ) (h : FSMultiState T RSt K I E) : Prop :=
  h.table.length ≤ L ∧ h.sessions.length ≤ L ∧
    ∀ sIdx bk, h.book sIdx = some bk → bk.fsTrans.length ≤ L

def FSMultiHBoundedPost (L : ℕ) (h : FSMultiState T RSt K I E) : Prop :=
  ∀ sIdx bk, h.book sIdx = some bk → bk.fsTrans.length ≤ L

@[reducible] def fsMultiVpEnc (vp : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) :
    (fsMultiVpTy KC Γ CCoins T I KR RSt K SS RS M E).denote :=
  vpTblEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (RSt := RSt)
    (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
    (γvT := .base .γ) (svT := .base .sig)
    (ssvT := .sum (.base .ss) .nat) (rsvT := .sum (.base .rs) .nat) vp

/-- Combined engine and hook-state invariant for `redFSAuthMultiStage2` across `q` remaining queries. -/
structure FSMultiEngineInv (L B q : ℕ)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E)
      (FSMultiState T RSt K I E)) : Prop where
  sm : SMEngineInv L B q es.g
  table_le : es.h.table.length + q ≤ B + 1
  sessions_le : es.h.sessions.length + q ≤ B + 1
  fsTrans_le : ∀ sIdx bk, es.h.book sIdx = some bk → bk.fsTrans.length + q ≤ B
  tcur_le : ∀ P : Party, (es.g.st P).tcur + q ≤ B
  vR_none_of_gt : ∀ (P : Party) (t : ℕ), (es.g.st P).tcur < t → (es.g.st P).vR t = none

theorem FSMultiEngineInv.mono {L B q q' : ℕ}
    {es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E)
      (FSMultiState T RSt K I E)}
    (hq : q' ≤ q) (h : FSMultiEngineInv L B q es) : FSMultiEngineInv L B q' es :=
  ⟨h.sm.mono hq,
    by have := h.table_le; omega,
    by have := h.sessions_le; omega,
    fun sIdx bk hbk => by have := h.fsTrans_le sIdx bk hbk; omega,
    fun P => by have := h.tcur_le P; omega,
    h.vR_none_of_gt⟩

theorem FSMultiEngineInv.toFSMultiHBounded {L B q : ℕ}
    {es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E)
      (FSMultiState T RSt K I E)}
    (h : FSMultiEngineInv L B (q + 1) es) : FSMultiHBounded L es.h := by
  have hBL : B + 1 ≤ L := h.sm.b_succ_le
  exact ⟨by have := h.table_le; omega,
    by have := h.sessions_le; omega,
    fun sIdx bk hbk => by have := h.fsTrans_le sIdx bk hbk; omega⟩

theorem FSMultiEngineInv.vR_none_of_le_L {L B q : ℕ}
    {es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E)
      (FSMultiState T RSt K I E)}
    (h : FSMultiEngineInv L B q es) (P : Party) (t : ℕ) (ht : L ≤ t) :
    (es.g.st P).vR t = none := by
  have hBL : B + 1 ≤ L := h.sm.b_succ_le
  have htcur : (es.g.st P).tcur + q ≤ B := h.tcur_le P
  exact h.vR_none_of_gt P t (by omega)

section MultiInitHelpers

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

local notation "IIM" =>
  fsaeadMultiHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK

local notation "hdrTy" => ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrCtTy" => ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "psTy" => ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mHsTy" => fsMultiHsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mVpTy" => fsMultiVpTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mBookTy" => fsMultiSessBookTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "transEntryTy" => fsTransEntryTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hsMDec" =>
  fsMultiHsDec (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (SS := SS) (RS := RS) (M := M)
local notation "hsMEnc" =>
  fsMultiHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (SS := SS) (RS := RS) (M := M)
local notation "vpMEnc" =>
  fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (K := K) (M := M) (E := E)

private theorem fsMultiHsSetSessions_eval {Γ'}
    (hE : Expr OO Γ' mHsTy) (seE : Expr OO Γ' (.list (.base .i))) (ρ : Env Γ')
    (h : FSMultiState T RSt K I E) (hh : hE.eval ρ = hsMEnc h) :
    (fsMultiHsSetSessions hE seE).eval ρ = hsMEnc { h with sessions := seE.eval ρ } := by
  simp [fsMultiHsSetSessions, fsMultiHsMk, fsMultiHsCache, fsMultiHsTable,
    fsMultiHsBook, fsMultiHsLfWin, fsMultiHsEnc, hh, Expr.eval]

private theorem lookupMultiFC_eval [DecidableEq I] [SampleableType K]
    (heqI : eqI = (· == ·))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (L : ℕ) {Γ'} (hE : Expr OO Γ' mHsTy) (ikE : Expr OO Γ' (.base .i))
    (ρ : Env Γ') (h : FSMultiState T RSt K I E)
    (hh : hE.eval ρ = hsMEnc h) (hL : h.table.length ≤ L) :
    (lookupMultiFC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L hE ikE).eval ρ =
      Prod.map id hsMEnc <$>
        (lookupMultiF (T := T) (Sig := RSt) (K := K) (I := I) (SS := SS) (RS := RS)
          (M := M) (E := E) (ikE.eval ρ)).run h ∧
    ∀ res ∈ support ((lookupMultiF (T := T) (Sig := RSt) (K := K) (I := I) (SS := SS) (RS := RS)
        (M := M) (E := E) (ikE.eval ρ)).run h),
      res.2.table.length ≤ h.table.length + 1 ∧
      res.2.sessions = h.sessions ∧
      res.2.book = h.book := by
  unfold lookupMultiFC lookupMultiF
  rw [eval_bind_ret]
  set Ik : I := ikE.eval ρ
  have h0 : (Expr.pair hE ikE).eval ρ = (hsMEnc h, Ik) := by simp [Expr.eval, hh, Ik]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod mHsTy (.base CKASort.i)) (hsMEnc h, Ik) ρ
  have hTbl : (tableLookupE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      L (fsMultiHsTable (.fst .v0)) (.snd .v0)).eval ρ₁ = h.table.lookup Ik := by
    rw [tableLookupE_eval heqI L (fsMultiHsTable (.fst .v0)) (.snd .v0) ρ₁
      (by simpa [ρ₁, fsMultiHsTable, fsMultiHsEnc, Expr.eval, Expr.v0] using hL)]
    rfl
  rw [eval_caseOpt, hTbl]
  rcases hlk : h.table.lookup Ik with _ | k
  · refine ⟨?_, ?_⟩
    · simp only [hlk, eval_bind, StateT.run_bind, StateT.run_get,
        StateT.run_lift, StateT.run_modify, StateT.run_pure, pure_bind, bind_assoc, map_bind]
      have hSamp : (@Comp.sample _ _ _ OO IIM _ CKASamp.k .unit).eval ρ₁ =
          (sampleT K : TComp (FSMultiSpec SS RS T M E) K) := by
        simp only [Comp.eval, fsaeadMultiHeaderAdIface, prngSamplers, ckaSamplers, hSampK, sampleT]
        exact liftP_eq_liftM IIM (fun _ => rfl) ($ᵗ K)
      rw [hSamp]
      refine bind_congr fun k' => ?_
      simp [ρ₁, Comp.eval, fsMultiHsSetTable, fsMultiHsMk, fsMultiHsCache, fsMultiHsTable,
        fsMultiHsSessions, fsMultiHsBook, fsMultiHsLfWin, fsMultiHsEnc, Prod.map,
        Expr.eval, Expr.v0, Expr.v1]
    · intro res hmem
      simp only [hlk, StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_modify,
        StateT.run_pure, pure_bind, bind_assoc, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hmem
      obtain ⟨k', _, rfl⟩ := hmem
      exact ⟨by simp, rfl, rfl⟩
  · refine ⟨?_, ?_⟩
    · simp [ρ₁, hlk, Comp.eval, StateT.run_bind, StateT.run_get,
        StateT.run_pure, pure_bind, Prod.map, Expr.eval, Expr.v0, Expr.v1]
    · intro res hmem
      simp only [hlk, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff] at hmem
      subst hmem
      exact ⟨Nat.le_add_right _ _, rfl, rfl⟩

private theorem regSessMultiE_eval_pair [DecidableEq I] (heqI : eqI = (· == ·))
    (L : ℕ) {Γ'} (hE : Expr OO Γ' mHsTy) (ikE : Expr OO Γ' (.base .i))
    (ρ : Env Γ') (h : FSMultiState T RSt K I E)
    (hh : hE.eval ρ = hsMEnc h) (hL : h.sessions.length ≤ L) :
    ((regSessMulti (T := T) (Sig := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
        (ikE.eval ρ)).run h) =
      pure (let p := (regSessMultiE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        L hE ikE).eval ρ; (p.1, hsMDec p.2)) ∧
    let p := (regSessMultiE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        L hE ikE).eval ρ
    p.2 = hsMEnc (hsMDec p.2) ∧
    (hsMDec p.2).table = h.table ∧
    (hsMDec p.2).sessions.length ≤ h.sessions.length + 1 ∧
    (hsMDec p.2).book = h.book := by
  unfold regSessMulti regSessMultiE
  rw [letE_eval]
  set Ik : I := ikE.eval ρ
  have h0 : (Expr.pair hE ikE).eval ρ = (hsMEnc h, Ik) := by simp [Expr.eval, hh, Ik]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod mHsTy (.base CKASort.i)) (hsMEnc h, Ik) ρ
  have hMem : (sessionsMemE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM)
      (eqE := eqE) (lam := lam) (defaultE := defaultE)
      L (fsMultiHsSessions (.fst .v0)) (.snd .v0)).eval ρ₁ = decide (Ik ∈ h.sessions) :=
    sessionsMemE_eval heqI L (fsMultiHsSessions (.fst .v0)) (.snd .v0) ρ₁
      (by simpa [ρ₁, fsMultiHsSessions, fsMultiHsEnc, Expr.eval, Expr.v0] using hL)
  have hIdx : (sessionsIdxOfE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM)
      (eqE := eqE) (lam := lam) (defaultE := defaultE)
      L (fsMultiHsSessions (.fst .v0)) (.snd .v0)).eval ρ₁ = List.idxOf Ik h.sessions :=
    sessionsIdxOfE_eval heqI L (fsMultiHsSessions (.fst .v0)) (.snd .v0) ρ₁
      (by simpa [ρ₁, fsMultiHsSessions, fsMultiHsEnc, Expr.eval, Expr.v0] using hL)
  have hLen : (sessionsLenE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM)
      (eqE := eqE) (lam := lam) (defaultE := defaultE)
      L (fsMultiHsSessions (.fst .v0))).eval ρ₁ = h.sessions.length :=
    sessionsLenE_eval L (fsMultiHsSessions (.fst .v0)) ρ₁
      (by simpa [ρ₁, fsMultiHsSessions, fsMultiHsEnc, Expr.eval, Expr.v0] using hL)
  have hApp : (sessionsAppendOneE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM)
      (eqE := eqE) (lam := lam) (defaultE := defaultE)
      L (fsMultiHsSessions (.fst .v0)) (.snd .v0)).eval ρ₁ = h.sessions ++ [Ik] :=
    sessionsAppendOneE_eval L (fsMultiHsSessions (.fst .v0)) (.snd .v0) ρ₁
      (by simpa [ρ₁, fsMultiHsSessions, fsMultiHsEnc, Expr.eval, Expr.v0] using hL)
  rw [ite_eval, hMem]
  by_cases hm : Ik ∈ h.sessions
  · simp only [hm, decide_true, ↓reduceIte, pair_eval, hIdx]
    have hfst : (Expr.fst (Expr.v0 (O := OO))).eval ρ₁ = hsMEnc h := rfl
    rw [hfst, fsMultiHsDec_fsMultiHsEnc]
    simp [hm, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind]
  · simp only [hm, decide_false, Bool.false_eq_true, ↓reduceIte, pair_eval, hLen]
    have hset : (fsMultiHsSetSessions (O := OO) (.fst .v0)
        (sessionsAppendOneE L (fsMultiHsSessions (.fst .v0)) (.snd .v0))).eval ρ₁ =
        hsMEnc { h with sessions := h.sessions ++ [Ik] } := by
      rw [fsMultiHsSetSessions_eval _ _ ρ₁ h rfl, hApp]
    rw [hset, fsMultiHsDec_fsMultiHsEnc]
    simp [hm, StateT.run_bind, StateT.run_get, StateT.run_set, pure_bind]

private theorem regSessOptMultiE_eval_pair [DecidableEq I] (heqI : eqI = (· == ·))
    (L : ℕ) {Γ'} (hE : Expr OO Γ' mHsTy) (sidE : Expr OO Γ' (.opt (.base .i)))
    (ρ : Env Γ') (h : FSMultiState T RSt K I E)
    (hh : hE.eval ρ = hsMEnc h) (hL : h.sessions.length ≤ L) :
    ((regSessOptMulti (T := T) (Sig := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
        (sidE.eval ρ)).run h) =
      pure (let p := (regSessOptMultiE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        L hE sidE).eval ρ; (p.1, hsMDec p.2)) ∧
    let p := (regSessOptMultiE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        L hE sidE).eval ρ
    p.2 = hsMEnc (hsMDec p.2) ∧
    (hsMDec p.2).table = h.table ∧
    (hsMDec p.2).sessions.length ≤ h.sessions.length + 1 ∧
    (hsMDec p.2).book = h.book := by
  unfold regSessOptMulti regSessOptMultiE
  rw [letE_eval]
  rcases hsid : sidE.eval ρ with _ | Ik
  · simp [hsid, hh, StateT.run_pure, Expr.eval, Expr.v0]
  · simp only [hsid, Expr.eval, hh]
    set ρ₁ := Env.cons (t := .base CKASort.i) Ik
      (Env.cons (t := .prod mHsTy (.opt (.base CKASort.i))) (hsMEnc h, some Ik) ρ)
    have hReg := regSessMultiE_eval_pair (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) heqI L (.fst .v1) .v0 ρ₁ h rfl hL
    have hIk : (Expr.v0 (O := OO)).eval ρ₁ = Ik := rfl
    rw [hIk] at hReg
    refine ⟨?_, hReg.2⟩
    rw [StateT.run_map, hReg.1, map_pure]
    rfl

private theorem rootFSMultiC_eval [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR RSt I K)
    (hPrngUp : prngUp = prng.up)
    (heqI : eqI = (· == ·))
    (hSampI : sampI = ($ᵗ I : ProbComp I))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (L : ℕ) (mo : Mode) {Γ'}
    (hE : Expr OO Γ' mHsTy) (tE : Expr OO Γ' .nat)
    (ikE : Expr OO Γ' (.base .i)) (σE : Expr OO Γ' (.base .sig))
    (ρ : Env Γ') (h : FSMultiState T RSt K I E)
    (hh : hE.eval ρ = hsMEnc h) (hL : h.table.length ≤ L) :
    (rootFSMultiC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L mo hE tE ikE σE).eval ρ =
      Prod.map id hsMEnc <$>
        (rootFSMulti (T := T) (SS := SS) (RS := RS) (M := M) (E := E)
          prng mo (tE.eval ρ) (ikE.eval ρ) (σE.eval ρ)).run h ∧
    ∀ res ∈ support ((rootFSMulti (T := T) (SS := SS) (RS := RS) (M := M) (E := E)
        prng mo (tE.eval ρ) (ikE.eval ρ) (σE.eval ρ)).run h),
      res.2.table.length ≤ h.table.length + 1 ∧
      res.2.sessions = h.sessions ∧
      res.2.book = h.book := by
  unfold rootFSMultiC rootFSMulti
  rw [eval_bind_ret]
  set t : ℕ := tE.eval ρ
  set Ik : I := ikE.eval ρ
  set σ : RSt := σE.eval ρ
  have h0 : (Expr.pair hE (.pair tE (.pair ikE σE))).eval ρ = (hsMEnc h, t, Ik, σ) := by
    simp [Expr.eval, hh, t, Ik, σ]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod mHsTy (.prod .nat (.prod (.base CKASort.i) (.base CKASort.sig))))
    (hsMEnc h, t, Ik, σ) ρ
  have hSampIComp : ∀ {Γ''} (ρ' : Env Γ''),
      (@Comp.sample _ _ _ OO IIM Γ'' CKASamp.i .unit).eval ρ' =
        (sampleT I : TComp (FSMultiSpec SS RS T M E) I) := by
    intro Γ'' ρ'
    simp only [Comp.eval, fsaeadMultiHeaderAdIface, prngSamplers, ckaSamplers, hSampI, sampleT]
    exact liftP_eq_liftM IIM (fun _ => rfl) ($ᵗ I)
  have hSampKComp : ∀ {Γ''} (ρ' : Env Γ''),
      (@Comp.sample _ _ _ OO IIM Γ'' CKASamp.k .unit).eval ρ' =
        (sampleT K : TComp (FSMultiSpec SS RS T M E) K) := by
    intro Γ'' ρ'
    simp only [Comp.eval, fsaeadMultiHeaderAdIface, prngSamplers, ckaSamplers, hSampK, sampleT]
    exact liftP_eq_liftM IIM (fun _ => rfl) ($ᵗ K)
  rw [eval_ite]
  have hlt1 : (Expr.lt (.nat mo.tStar) (.fst (.snd (Expr.v0 (O := OO))))).eval ρ₁ =
      decide (mo.tStar < t) := rfl
  rw [hlt1]
  by_cases hgt : mo.tStar < t
  · refine ⟨?_, ?_⟩
    · simp [ρ₁, hgt, Comp.eval, StateT.run_pure, hPrngUp, Prod.map, Expr.eval, Expr.v0]
    · intro res hmem
      simp only [hgt, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem
      exact ⟨Nat.le_add_right _ _, rfl, rfl⟩
  · simp only [hgt, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [eval_ite]
    have heq1 : (Expr.eqN (.fst (.snd (Expr.v0 (O := OO)))) (.nat mo.tStar)).eval ρ₁ =
        decide (t = mo.tStar) := rfl
    rw [heq1]
    by_cases hts : t = mo.tStar
    · have htsIf : (t = mo.tStar) ↔ True := by simp [hts]
      simp only [htsIf, decide_true, ↓reduceIte]
      rw [eval_ite]
      have hcond2 : (Expr.and (.bool mo.tL.isSome)
          (.eqN (.fst (.snd (Expr.v0 (O := OO)))) (.nat mo.tH))).eval ρ₁ =
          (mo.tL.isSome && decide (t = mo.tH)) := rfl
      rw [hcond2]
      by_cases htH : (mo.tL.isSome && decide (t = mo.tH)) = true
      · refine ⟨?_, ?_⟩
        · simp only [htH, ↓reduceIte, eval_bind, hSampIComp, StateT.run_bind,
            StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind, map_bind]
          refine bind_congr fun Ir => ?_
          simp only [hSampKComp]
          refine bind_congr fun k => ?_
          simp [ρ₁, Comp.eval, hPrngUp, Prod.map, Expr.eval, Expr.v0, Expr.v1, Expr.v2]
        · intro res hmem
          simp only [htH, ↓reduceIte, StateT.run_bind, StateT.run_lift, StateT.run_pure,
            bind_assoc, pure_bind, mem_support_bind_iff, support_pure,
            Set.mem_singleton_iff] at hmem
          obtain ⟨Ir, _, k, _, rfl⟩ := hmem
          exact ⟨Nat.le_add_right _ _, rfl, rfl⟩
      · simp only [htH, Bool.false_eq_true, ↓reduceIte]
        have hLk := lookupMultiFC_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
          (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
          (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
          (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
          (sampCCoins := sampCCoins) (sampI := sampI)
          heqI hSampK L (.fst .v0) (.fst (.snd (.snd .v0))) ρ₁ h rfl hL
        have hIk1 : (Expr.fst (.snd (.snd (Expr.v0 (O := OO))))).eval ρ₁ = Ik := rfl
        rw [hIk1] at hLk
        refine ⟨?_, ?_⟩
        · rw [eval_bind, hLk.1, StateT.run_bind, bind_map_left, map_bind]
          refine bind_congr fun ⟨k, h'⟩ => ?_
          simp [ρ₁, Comp.eval, StateT.run_pure, hPrngUp, Prod.map, Expr.eval, Expr.v0, Expr.v1]
        · intro res hmem
          simp only [StateT.run_bind, StateT.run_pure, mem_support_bind_iff, support_pure,
            Set.mem_singleton_iff] at hmem
          obtain ⟨⟨k, h'⟩, hmemLk, rfl⟩ := hmem
          exact hLk.2 (k, h') hmemLk
    · simp only [hts, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [eval_ite]
      have hcond3 : (Expr.and (.bool mo.tL.isSome)
          (.eqN (.fst (.snd (Expr.v0 (O := OO)))) (.nat mo.tH))).eval ρ₁ =
          (mo.tL.isSome && decide (t = mo.tH)) := rfl
      rw [hcond3]
      by_cases htH : (mo.tL.isSome && decide (t = mo.tH)) = true
      · refine ⟨?_, ?_⟩
        · simp only [htH, ↓reduceIte, eval_bind, hSampIComp, StateT.run_bind,
            StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind, map_bind]
          refine bind_congr fun Ir => ?_
          simp [ρ₁, Comp.eval, hPrngUp, Prod.map, Expr.eval, Expr.v0, Expr.v1]
        · intro res hmem
          simp only [htH, ↓reduceIte, StateT.run_bind, StateT.run_lift, StateT.run_pure,
            bind_assoc, pure_bind, mem_support_bind_iff, support_pure,
            Set.mem_singleton_iff] at hmem
          obtain ⟨Ir, _, rfl⟩ := hmem
          exact ⟨Nat.le_add_right _ _, rfl, rfl⟩
      · refine ⟨?_, ?_⟩
        · simp [ρ₁, htH, Comp.eval, StateT.run_pure, hPrngUp, Prod.map, Expr.eval, Expr.v0]
        · intro res hmem
          simp only [htH, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, support_pure,
            Set.mem_singleton_iff] at hmem
          subst hmem
          exact ⟨Nat.le_add_right _ _, rfl, rfl⟩

end MultiInitHelpers

private theorem lookupMultiF_preserve [DecidableEq I] [SampleableType K] (ik : I)
    (h : FSMultiState T RSt K I E) :
    ∀ res ∈ support
      ((lookupMultiF (T := T) (Sig := RSt) (SS := SS) (RS := RS) (M := M) (E := E) ik).run h),
      res.2.table.length ≤ h.table.length + 1 ∧
      res.2.sessions = h.sessions ∧
      res.2.book = h.book := by
  intro res hmem
  unfold lookupMultiF at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  rcases hlk : h.table.lookup ik with _ | k
  · simp only [hlk, StateT.run_bind, StateT.run_lift, StateT.run_modify, StateT.run_pure,
      bind_assoc, pure_bind, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hmem
    obtain ⟨k, _, rfl⟩ := hmem
    exact ⟨by simp, rfl, rfl⟩
  · simp only [hlk, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    exact ⟨Nat.le_add_right _ _, rfl, rfl⟩

private theorem regSessMulti_preserve [DecidableEq I] (Ik : I)
    (h : FSMultiState T RSt K I E) :
    ∀ res ∈ support
      ((regSessMulti (T := T) (Sig := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
          Ik).run h),
      res.2.table = h.table ∧
      res.2.sessions.length ≤ h.sessions.length + 1 ∧
      res.2.book = h.book := by
  intro res hmem
  unfold regSessMulti at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases hm : Ik ∈ h.sessions
  · simp only [hm, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    exact ⟨rfl, Nat.le_add_right _ _, rfl⟩
  · simp only [hm, ↓reduceIte, StateT.run_bind, StateT.run_set, pure_bind] at hmem
    subst hmem
    exact ⟨rfl, by simp, rfl⟩

private theorem regSessOptMulti_preserve [DecidableEq I] (sid : Option I)
    (h : FSMultiState T RSt K I E) :
    ∀ res ∈ support
      ((regSessOptMulti (T := T) (Sig := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
          sid).run h),
      res.2.table = h.table ∧
      res.2.sessions.length ≤ h.sessions.length + 1 ∧
      res.2.book = h.book := by
  rcases sid with _ | Ik
  · intro res hmem
    simp only [regSessOptMulti, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    exact ⟨rfl, Nat.le_add_right _ _, rfl⟩
  · intro ⟨optIdx, h'⟩ hmem
    unfold regSessOptMulti at hmem
    simp only [map_eq_bind_pure_comp, Function.comp_def, StateT.run_bind, StateT.run_pure,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hmem
    obtain ⟨⟨idx, h''⟩, hReg, hEq⟩ := hmem
    cases hEq
    exact regSessMulti_preserve Ik h (idx, h'') hReg

private theorem rootFSMulti_preserve [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR RSt I K) (mo : Mode) (t : ℕ) (ik : I) (σ : RSt)
    (h : FSMultiState T RSt K I E) :
    ∀ res ∈ support
      ((rootFSMulti (T := T) (SS := SS) (RS := RS) (M := M) (E := E) prng mo t ik σ).run h),
      res.2.table.length ≤ h.table.length + 1 ∧
      res.2.sessions = h.sessions ∧
      res.2.book = h.book := by
  intro res hmem
  unfold rootFSMulti at hmem
  by_cases hlt : mo.tStar < t
  · simp only [hlt, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    exact ⟨Nat.le_add_right _ _, rfl, rfl⟩
  · simp only [hlt, ↓reduceIte] at hmem
    by_cases heq : t = mo.tStar
    · have heqIf : (t = mo.tStar) ↔ True := by simp [heq]
      simp only [heqIf, ↓reduceIte] at hmem
      by_cases hc : (mo.tL.isSome && decide (t = mo.tH)) = true
      · simp only [hc, ↓reduceIte, StateT.run_bind, StateT.run_lift,
          StateT.run_pure, bind_assoc, pure_bind, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at hmem
        obtain ⟨_, _, _, _, rfl⟩ := hmem
        exact ⟨Nat.le_add_right _ _, rfl, rfl⟩
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_pure,
          mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hmem
        obtain ⟨⟨k, h₁⟩, hLk, rfl⟩ := hmem
        exact lookupMultiF_preserve ik h (k, h₁) hLk
    · simp only [heq, ↓reduceIte] at hmem
      by_cases hc : (mo.tL.isSome && decide (t = mo.tH)) = true
      · simp only [hc, ↓reduceIte, StateT.run_bind, StateT.run_lift,
          StateT.run_pure, bind_assoc, pure_bind, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at hmem
        obtain ⟨_, _, rfl⟩ := hmem
        exact ⟨Nat.le_add_right _ _, rfl, rfl⟩
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at hmem
        subst hmem
        exact ⟨Nat.le_add_right _ _, rfl, rfl⟩

theorem initFSMultiEStateC_eval
    {ckaInitA : KC → Γ} {ckaInitB : KC → Γ}
    {ckaSend : Γ → CCoins → Γ × T × I} {ckaReceive : Γ → T → Γ × I}
    {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
    {fsInitSender : K → SS} {fsInitReceiver : K → RS}
    {fsSend : SS → Header T → M → SS × E}
    {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
    {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
    {lam : I} {defaultE : E}
    {sampKR : ProbComp KR} {sampKC : ProbComp KC} {sampCCoins : ProbComp CCoins}
    {sampI : ProbComp I} {sampK : ProbComp K}
    [DecidableEq I]
    [SampleableType KR] [SampleableType KC] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (hInitA : ckaInitA = cka.initA)
    (hInitB : ckaInitB = cka.initB)
    (hPrngInit : prngInit = prng.init)
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (heqI : eqI = (· == ·))
    (hSampKR : sampKR = ($ᵗ KR : ProbComp KR))
    (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampI : sampI = ($ᵗ I : ProbComp I))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (L : ℕ) (mo : Mode) {Γ'} (bE : Expr (prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit
      prngUp fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE) Γ' .bool)
    (ρ : Env Γ') :
    (initFSMultiEStateC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L mo bE).eval ρ =
      esEnc
        (fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (K := K)
          (M := M) (E := E))
        (fsMultiHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (SS := SS) (RS := RS)
          (M := M)) <$>
        initFSMultiRaw cka prng fs lam mo (bE.eval ρ) := by
  let OO := prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE
  let IIM := fsaeadMultiHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E
    sampKR sampKC sampCCoins sampI sampK
  let mHsTy := fsMultiHsTy KC Γ CCoins T I KR RSt K SS RS M E
  let vpMEnc := fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
    (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
  let hsMEnc := fsMultiHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
    (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
  let hsMDec := fsMultiHsDec (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
    (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
  unfold initFSMultiEStateC initFSMultiRaw
  rw [eval_bind_ret]
  set b : Bool := bE.eval ρ
  set ρ₁ := Env.cons (t := (.bool : Ty S)) b ρ
  have hKR : (@Comp.sample _ _ _ OO IIM _ CKASamp.kr .unit).eval ρ₁ =
      (sampleT KR : TComp (FSMultiSpec SS RS T M E) KR) := by
    simp only [Comp.eval, IIM, fsaeadMultiHeaderAdIface, prngSamplers, ckaSamplers, hSampKR, sampleT]
    exact liftP_eq_liftM IIM (fun _ => rfl) ($ᵗ KR)
  rw [eval_bind, hKR, map_bind]
  refine bind_congr fun kr => ?_
  set ρ₂ := Env.cons (t := (.base .kr : Ty S)) kr ρ₁
  have hKC : (@Comp.sample _ _ _ OO IIM _ CKASamp.kc .unit).eval ρ₂ =
      (sampleT KC : TComp (FSMultiSpec SS RS T M E) KC) := by
    simp only [Comp.eval, IIM, fsaeadMultiHeaderAdIface, prngSamplers, ckaSamplers, hSampKC, sampleT]
    exact liftP_eq_liftM IIM (fun _ => rfl) ($ᵗ KC)
  rw [eval_bind, hKC, map_bind]
  refine bind_congr fun kc => ?_
  set ρ₃ := Env.cons (t := (.base .kc : Ty S)) kc ρ₂
  have hRoot := rootFSMultiC_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins)
    prng hPrngUp heqI hSampI hSampK L mo fsMultiHsEmptyE (.nat 0)
    (Expr.op (O := OO) CKAOp.lamI .unit) (Expr.op (O := OO) CKAOp.prngInit .v1)
    ρ₃ ({} : FSMultiState T RSt K I E) rfl (Nat.zero_le L)
  have hT0 : (Expr.nat (O := OO) 0).eval ρ₃ = 0 := rfl
  have hLam : (Expr.op (O := OO) CKAOp.lamI .unit).eval ρ₃ = lam := rfl
  have hSig0 : (Expr.op (O := OO) CKAOp.prngInit .v1).eval ρ₃ = prng.init kr := by
    simp [ρ₃, ρ₂, OO, hPrngInit, Expr.eval, Expr.v1]
  rw [hT0, hLam, hSig0] at hRoot
  rw [eval_bind, hRoot.1, bind_map_left, map_bind]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨σ, k, sid⟩, h₁⟩ hmemR => ?_
  dsimp only
  have ⟨_, hSes₁, _⟩ := hRoot.2 ((σ, k, sid), h₁) hmemR
  have hSesL₁ : h₁.sessions.length ≤ L := by
    dsimp only at hSes₁
    rw [hSes₁]
    exact Nat.zero_le L
  set ρ₄ := Env.cons
    (t := .prod (.prod (.base CKASort.sig) (.prod (.base CKASort.k) (.opt (.base CKASort.i)))) mHsTy)
    ((σ, (k, sid)), hsMEnc h₁) ρ₃
  have hReg := regSessOptMultiE_eval_pair (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) heqI L (.snd .v0) (.snd (.snd (.fst .v0)))
    ρ₄ h₁ rfl hSesL₁
  have hSid : (Expr.snd (.snd (.fst (Expr.v0 (O := OO))))).eval ρ₄ = sid := rfl
  rw [hSid] at hReg
  rcases hRegPair : (regSessOptMultiE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    L (.snd .v0) (.snd (.snd (.fst .v0)))).eval ρ₄ with ⟨optIdx, h₂_enc⟩
  rw [hRegPair] at hReg
  rw [hReg.1]
  simp only [pure_bind, map_pure]
  change (Comp.ret _).eval ρ₄ = _
  rw [eval_ret]
  set optIdxE : Expr OO _ (.opt .nat) :=
    .fst (regSessOptMultiE L (.snd .v0) (.snd (.snd (.fst .v0))))
  set h2E : Expr OO _ mHsTy :=
    .snd (regSessOptMultiE L (.snd .v0) (.snd (.snd (.fst .v0))))
  set ssv0E : Expr OO _ (.sum (.base .ss) .nat) :=
    .caseOpt optIdxE (.inl (Expr.op (O := OO) CKAOp.fsInitSender (.fst (.snd (.fst .v0)))))
      (.inr .v0)
  set rsv0E : Expr OO _ (.sum (.base .rs) .nat) :=
    .caseOpt optIdxE (.inl (Expr.op (O := OO) CKAOp.fsInitReceiver (.fst (.snd (.fst .v0)))))
      (.inr .v0)
  set ssv0 : SS ⊕ ℕ := match optIdx with
    | none => .inl (fs.initSender k)
    | some sIdx => .inr sIdx
  set rsv0 : RS ⊕ ℕ := match optIdx with
    | none => .inl (fs.initReceiver k)
    | some sIdx => .inr sIdx
  set pAB := mkParties (T := T) (cka.initA kc) (cka.initB kc) σ ssv0 rsv0
  have hOptIdxE : optIdxE.eval ρ₄ = optIdx := by simp [optIdxE, hRegPair, Expr.eval]
  have hSsv0E : ssv0E.eval ρ₄ = ssv0 := by
    cases optIdx <;> simp [ssv0E, ssv0, hOptIdxE, ρ₄, OO, hFsInitS, Expr.eval, Expr.v0]
  have hRsv0E : rsv0E.eval ρ₄ = rsv0 := by
    cases optIdx <;> simp [rsv0E, rsv0, hOptIdxE, ρ₄, OO, hFsInitR, Expr.eval, Expr.v0]
  have hMkP := mkPartiesE_eval (O' := OO)
    (γvT := .base .γ) (svT := .base .sig)
    (ssvT := .sum (.base .ss) .nat) (rsvT := .sum (.base .rs) .nat)
    (Expr.op (O := OO) CKAOp.ckaInitA .v1)
    (Expr.op (O := OO) CKAOp.ckaInitB .v1)
    (.fst (.fst .v0)) ssv0E rsv0E ρ₄
  have hMkP' :
      (mkPartiesE (O' := OO)
        (γvT := .base .γ) (svT := .base .sig)
        (ssvT := .sum (.base .ss) .nat) (rsvT := .sum (.base .rs) .nat)
        (Expr.op (O := OO) CKAOp.ckaInitA .v1)
        (Expr.op (O := OO) CKAOp.ckaInitB .v1)
        (.fst (.fst .v0)) ssv0E rsv0E).eval ρ₄ =
        (vpMEnc pAB.1, vpMEnc pAB.2) := by
    rw [hMkP]
    simp [hSsv0E, hRsv0E, ρ₄, ρ₃, ρ₂, ρ₁, OO, hInitA, hInitB, pAB, vpMEnc, fsMultiVpEnc,
      Prod.map, Expr.eval, Expr.v0, Expr.v1]
  have hGs := cGsInitE_eval vpMEnc (O' := OO)
    (.fst (mkPartiesE
      (Expr.op (O := OO) CKAOp.ckaInitA .v1)
      (Expr.op (O := OO) CKAOp.ckaInitB .v1)
      (.fst (.fst .v0)) ssv0E rsv0E))
    (.snd (mkPartiesE
      (Expr.op (O := OO) CKAOp.ckaInitA .v1)
      (Expr.op (O := OO) CKAOp.ckaInitB .v1)
      (.fst (.fst .v0)) ssv0E rsv0E))
    .v3 ρ₄ pAB.1 pAB.2
    (by simp [Expr.eval, hMkP']) (by simp [Expr.eval, hMkP'])
  have hh2 : h2E.eval ρ₄ = hsMEnc (hsMDec h₂_enc) := by
    unfold h2E; rw [snd_eval, hRegPair]; exact hReg.2.1
  have hb3 : (Expr.v3 (O := OO)).eval ρ₄ = b := rfl
  simp only [esMk, pair_eval, hGs, hh2, hb3, esEnc, cGsEnc, Expr.eval, pAB, ssv0, rsv0]
  cases optIdx <;> rfl

theorem initFSMultiRaw_inv [DecidableEq I]
    [SampleableType KR] [SampleableType KC] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (mo : Mode) (b : Bool)
    {L B qAdv : ℕ} (hqB : qAdv ≤ B) (hB1 : B + 1 ≤ L) (hBB : B * B ≤ L * L) :
    ∀ es₀ ∈ support (initFSMultiRaw cka prng fs lam mo b),
      FSMultiEngineInv L B qAdv es₀ ∧ es₀.g.b = b := by
  intro es₀ hmem
  unfold initFSMultiRaw at hmem
  rw [mem_support_bind_iff] at hmem; obtain ⟨kr, _, hmem⟩ := hmem
  rw [mem_support_bind_iff] at hmem; obtain ⟨kc, _, hmem⟩ := hmem
  rw [mem_support_bind_iff] at hmem; obtain ⟨⟨⟨σ, k, sid⟩, h₁⟩, hRoot, hmem⟩ := hmem
  rw [mem_support_bind_iff] at hmem; obtain ⟨⟨optIdx, h₂⟩, hReg, hmem⟩ := hmem
  simp only [support_pure, Set.mem_singleton_iff] at hmem
  subst hmem
  obtain ⟨hT1, hS1, hB1'⟩ := rootFSMulti_preserve prng mo 0 lam (prng.init kr) {}
    ((σ, k, sid), h₁) hRoot
  obtain ⟨hT2, hS2, hB2⟩ := regSessOptMulti_preserve sid h₁ (optIdx, h₂) hReg
  have hT_zero : ({} : FSMultiState T RSt K I E).table.length = 0 := rfl
  have hS_zero : h₁.sessions.length = 0 := by
    dsimp only at hS1
    rw [hS1]
    rfl
  refine ⟨⟨(SMEngineInv.init _ b hB1 hBB).mono hqB,
    by dsimp only at hT1 hT2 ⊢; rw [hT2]; rw [hT_zero] at hT1; omega,
    by dsimp only at hS2 ⊢; rw [hS_zero] at hS2; omega,
    (fun sIdx bk hbk => by
      dsimp only at hB1' hB2 hbk
      rw [hB2, hB1'] at hbk
      cases hbk),
    fun P => by cases P <;> simp [mkParties, hqB],
    fun P t ht => ?_⟩, rfl⟩
  cases P
  · dsimp only [mkParties] at ht ⊢
    simp [Nat.ne_of_gt ht]
  · rfl

theorem finishFSMultiE_eval
    {ckaInitA : KC → Γ} {ckaInitB : KC → Γ}
    {ckaSend : Γ → CCoins → Γ × T × I} {ckaReceive : Γ → T → Γ × I}
    {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
    {fsInitSender : K → SS} {fsInitReceiver : K → RS}
    {fsSend : SS → Header T → M → SS × E}
    {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
    {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
    {lam : I} {defaultE : E}
    (L B Δ : ℕ) (pol : Policy) (la : Bool) {Γ'}
    (esE : Expr (prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
      fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE) Γ'
      (fsMultiEsTy KC Γ CCoins T I KR RSt K SS RS M E))
    (ρ : Env Γ')
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E))
    (hInv : SMEngineInv L B 0 es.g)
    (hes : esE.eval ρ = esEnc
      (fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (K := K)
        (M := M) (E := E))
      (fsMultiHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (SS := SS) (RS := RS)
        (M := M)) es) :
    (finishFSMultiE L Δ pol la esE).eval ρ =
      (if la then es.h.lfWin else authOut Δ pol es) := by
  unfold finishFSMultiE
  cases la
  · exact authOutE_eval
      (fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (K := K)
        (M := M) (E := E))
      (fsMultiHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (SS := SS) (RS := RS)
        (M := M))
      L Δ pol esE ρ es hInv.toBoundedEngine.leaks_le hInv.toBoundedEngine.corrs_le hes
  · simp only [↓reduceIte, fsMultiHsLfWin, esH, Expr.eval, hes, esEnc, fsMultiHsEnc]

def hooksFSMultiL [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L Δcka : ℕ) (mo : Mode) (gMain la : Bool) :
    Hooks (FSMultiSpec SS RS T M E) (FSMultiState T RSt K I E)
      Γ T RSt SS RS M E CCoins Γ RSt (SS ⊕ ℕ) (RS ⊕ ℕ) :=
  { hooksFSMulti cka prng fs Δcka mo gMain la with
    reveal := fun _ _ vp => do
      let vS? : Option (Option SS) ← match vp.vS with
        | none => pure (some none)
        | some (.inl ss) => pure (some (some ss))
        | some (.inr sIdx) =>
          if la then pure none
          else do
            match ← liftFSMulti sIdx (FSAEAD.corruptSenderQuery (ReceiverState := RS)
                (AssocData := Header T) (Message := M) (Ciphertext := E)) with
            | none => pure none
            | some ss =>
              modify fun s =>
                let b := (s.book sIdx).getD {}
                { s with book := Function.update s.book sIdx (some { b with sCorr := true }) }
              pure (some (some ss))
      match vS? with
      | none => return none
      | some vS =>
        let abortRecv := match vp.vR mo.tStar with
          | some (.inr _) => true
          | _ => false
        if abortRecv then return none
        else
          let vR : ℕ → Option RS := fun t =>
            if t < L then
              match vp.vR t with
              | some (.inl rs) => some rs
              | _ => none
            else none
          return some (realParty vp vp.γ vp.root vS vR) }

theorem vRecv_hooksFSMultiL_eq [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L Δcka : ℕ) (mo : Mode) (gMain la : Bool) :
    vRecv (hooksFSMultiL cka prng fs L Δcka mo gMain la) =
      vRecv (hooksFSMulti cka prng fs Δcka mo gMain la) :=
  rfl

theorem commitE_hooksFSMultiL_eq [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L Δcka : ℕ) (mo : Mode) (gMain la : Bool) :
    commitE (hooksFSMultiL cka prng fs L Δcka mo gMain la) =
      commitE (hooksFSMulti cka prng fs Δcka mo gMain la) :=
  rfl

section HooksFSMultiEval

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

local notation "IIM" =>
  fsaeadMultiHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK

local notation "hdrTy" => ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrCtTy" => ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "psTy" => ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mHsTy" => fsMultiHsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mVpTy" => fsMultiVpTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mBookTy" => fsMultiSessBookTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "transEntryTy" => fsTransEntryTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hsMDec" =>
  fsMultiHsDec (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (SS := SS) (RS := RS) (M := M)
local notation "hsMEnc" =>
  fsMultiHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (SS := SS) (RS := RS) (M := M)
local notation "vpMEnc" =>
  fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (K := K) (M := M) (E := E)

private theorem fsMultiHsGetBookAt_eval {Γ'}
    (hE : Expr OO Γ' mHsTy) (sIdxE : Expr OO Γ' .nat) (ρ : Env Γ')
    (h : FSMultiState T RSt K I E) (hh : hE.eval ρ = hsMEnc h) :
    (fsMultiHsGetBookAt hE sIdxE).eval ρ =
      let b := (h.book (sIdxE.eval ρ)).getD {}
      (b.sCorr, b.fsCount, b.fsTrans) := by
  unfold fsMultiHsGetBookAt
  simp only [fsMultiHsBook, fsMultiHsEnc, hh, Expr.eval, Expr.v0, Env.get_cons_zero]
  rcases h.book (sIdxE.eval ρ) with _ | ⟨sc, cnt, tr⟩ <;> rfl

private theorem fsMultiHsSetBookAt_eval {Γ'}
    (hE : Expr OO Γ' mHsTy) (sIdxE : Expr OO Γ' .nat) (entryE : Expr OO Γ' mBookTy) (ρ : Env Γ')
    (h : FSMultiState T RSt K I E) (hh : hE.eval ρ = hsMEnc h)
    {sc : Bool} {cnt : ℕ} {tr : List (ℕ × Header T × E)}
    (hentry : entryE.eval ρ = (sc, cnt, tr)) :
    (fsMultiHsSetBookAt hE sIdxE entryE).eval ρ =
      hsMEnc { h with book := Function.update h.book (sIdxE.eval ρ) (some ⟨sc, cnt, tr⟩) } := by
  unfold fsMultiHsSetBookAt fsMultiHsMk
  simp only [pair_eval, tset_eval_eq_update, some_eval, hentry,
    fsMultiHsCache, fsMultiHsTable, fsMultiHsSessions, fsMultiHsBook, fsMultiHsLfWin,
    fst_eval, snd_eval, hh, fsMultiHsEnc, Prod.mk.injEq, true_and, and_true]
  funext i
  by_cases hi : i = sIdxE.eval ρ <;> simp [Function.update, hi]

private theorem fsMultiHsSetCache_eval {Γ'}
    (hE : Expr OO Γ' mHsTy)
    (caE : Expr OO Γ' (.tbl (.opt (fsMultiCacheEntryTy KC Γ CCoins T I KR RSt K SS RS M E))))
    (ρ : Env Γ') (h : FSMultiState T RSt K I E) (hh : hE.eval ρ = hsMEnc h) :
    (fsMultiHsSetCache hE caE).eval ρ = hsMEnc { h with cache := caE.eval ρ } := by
  simp [fsMultiHsSetCache, fsMultiHsMk, fsMultiHsTable, fsMultiHsSessions,
    fsMultiHsBook, fsMultiHsLfWin, fsMultiHsEnc, hh, Expr.eval]

private theorem fsMultiHsSetLfWin_eval {Γ'}
    (hE : Expr OO Γ' mHsTy) (lwE : Expr OO Γ' .bool)
    (ρ : Env Γ') (h : FSMultiState T RSt K I E) (hh : hE.eval ρ = hsMEnc h) :
    (fsMultiHsSetLfWin hE lwE).eval ρ = hsMEnc { h with lfWin := lwE.eval ρ } := by
  simp [fsMultiHsSetLfWin, fsMultiHsMk, fsMultiHsCache, fsMultiHsTable,
    fsMultiHsSessions, fsMultiHsBook, fsMultiHsEnc, hh, Expr.eval]

private theorem fsMultiStartSendC_eval [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (hSend : ckaSend = cka.send)
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (heqI : eqI = (· == ·))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hSampI : sampI = ($ᵗ I : ProbComp I))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (L Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    {Γ'} (hE : Expr OO Γ' mHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' (.base .γ)) (σE : Expr OO Γ' (.base .sig))
    (rE : Expr OO Γ' (.opt (.base .ccoins))) (ρ : Env Γ')
    (h : FSMultiState T RSt K I E) (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (hHB : FSMultiHBounded L h) (hh : hE.eval ρ = hsMEnc h) :
    (fsMultiStartSendC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L mo hE ctxE pE tE γE σE rE).eval ρ =
      Prod.map id hsMEnc <$>
        ((hooksFSMulti cka prng fs Δcka mo gMain la).startSend ctx P
          (tE.eval ρ) (γE.eval ρ) (σE.eval ρ) (rE.eval ρ)).run h ∧
    ∀ res ∈ support (((hooksFSMulti cka prng fs Δcka mo gMain la).startSend ctx P
        (tE.eval ρ) (γE.eval ρ) (σE.eval ρ) (rE.eval ρ)).run h),
      res.2.table.length ≤ h.table.length + 1 ∧
      res.2.sessions.length ≤ h.sessions.length + 1 ∧
      res.2.book = h.book := by
  unfold fsMultiStartSendC
  rw [eval_bind_ret]
  set t : ℕ := tE.eval ρ
  set γ : Γ := γE.eval ρ
  set σ : RSt := σE.eval ρ
  set r : Option CCoins := rE.eval ρ
  have h0 : (Expr.pair hE (.pair tE (.pair γE (.pair σE rE)))).eval ρ =
      (hsMEnc h, t, γ, σ, r) := by
    simp [Expr.eval, hh, t, γ, σ, r]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := .prod mHsTy (.prod .nat (.prod (.base CKASort.γ)
      (.prod (.base CKASort.sig) (.opt (.base CKASort.ccoins))))))
    (hsMEnc h, t, γ, σ, r) ρ
  have hStep1 :
      (Comp.caseOpt (O := OO) (I := IIM) (.snd (.snd (.snd (.snd .v0))))
        (@Comp.sample _ _ _ OO IIM _ CKASamp.ccoins .unit)
        (.ret .v0)).eval ρ₁ =
      (match r with
        | some c => pure c
        | none => (sampleT CCoins : TComp (FSMultiSpec SS RS T M E) CCoins)) := by
    rcases r with _ | c
    · simp only [ρ₁, Comp.eval, Expr.eval, Expr.v0, Env.get_cons_zero,
        fsaeadMultiHeaderAdIface, prngSamplers, ckaSamplers, hSampCCoins, sampleT]
      exact liftP_eq_liftM IIM (fun _ => rfl) ($ᵗ CCoins)
    · rfl
  have hRHS :
      ((hooksFSMulti cka prng fs Δcka mo gMain la).startSend ctx P t γ σ r).run h =
      ((match r with
          | some c => pure c
          | none => (sampleT CCoins : TComp (FSMultiSpec SS RS T M E) CCoins)) >>=
        fun coins =>
          (do
            let c := cka.send γ coins
            let (σ', k, sid) ← rootFSMulti prng mo t c.2.2 σ
            let optIdx ← regSessOptMulti sid
            modify fun (s : FSMultiState T RSt K I E) =>
              { s with cache := Function.update s.cache t (some (c.2.1, σ', k, optIdx)) }
            let ssv : SS ⊕ ℕ := match optIdx with
              | none => .inl (fs.initSender k)
              | some sIdx => .inr sIdx
            return some (c.1, c.2.1, σ', ssv)).run h) := by
    unfold hooksFSMulti; dsimp only
    rcases r with _ | c
    · simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
    · simp only [StateT.run_bind, StateT.run_pure, pure_bind]
  refine ⟨?_, ?_⟩
  · rw [eval_bind, hStep1, hRHS, map_bind]
    refine bind_congr fun coins => ?_
    set ρ₂ := Env.cons (t := .base CKASort.ccoins) coins ρ₁
    have hRoot := rootFSMultiC_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins)
      prng hPrngUp heqI hSampI hSampK L mo (.fst .v1) (.fst (.snd .v1))
      (.snd (.snd (Expr.op (O := OO) CKAOp.ckaSend (.pair (.fst (.snd (.snd .v1))) .v0))))
      (.fst (.snd (.snd (.snd .v1)))) ρ₂ h rfl hHB.1
    have hIkEval : (Expr.snd (.snd (Expr.op (O := OO) CKAOp.ckaSend
        (.pair (.fst (.snd (.snd .v1))) .v0)))).eval ρ₂ = (cka.send γ coins).2.2 := by
      simp [ρ₂, ρ₁, hSend, Expr.eval, Expr.v0, Expr.v1]
    have htEval : (Expr.fst (.snd (Expr.v1 (O := OO)))).eval ρ₂ = t := rfl
    have hσEval : (Expr.fst (.snd (.snd (.snd (Expr.v1 (O := OO)))))).eval ρ₂ = σ := rfl
    rw [hIkEval, htEval, hσEval] at hRoot
    rw [eval_bind, hRoot.1, StateT.run_bind, bind_map_left, map_bind]
    refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨σ', k, sid⟩, h₁⟩ hmemRoot => ?_
    have ⟨_, hSes₁, _⟩ := hRoot.2 ((σ', k, sid), h₁) hmemRoot
    have hSesL₁ : h₁.sessions.length ≤ L := hSes₁ ▸ hHB.2.1
    set ρ₃ := Env.cons
      (t := .prod (.prod (.base CKASort.sig) (.prod (.base CKASort.k) (.opt (.base CKASort.i))))
        mHsTy)
      ((σ', k, sid), hsMEnc h₁) ρ₂
    have hReg := regSessOptMultiE_eval_pair (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) heqI L (.snd .v0) (.snd (.snd (.fst .v0))) ρ₃ h₁ rfl hSesL₁
    have hsidEval : (Expr.snd (.snd (.fst (Expr.v0 (O := OO))))).eval ρ₃ = sid := rfl
    rw [hsidEval] at hReg
    rcases hRegPair : (regSessOptMultiE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      L (.snd .v0) (.snd (.snd (.fst .v0)))).eval ρ₃ with ⟨optIdx, h₂_enc⟩
    rw [hRegPair] at hReg
    rw [StateT.run_bind, hReg.1]
    simp only [pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
      map_pure, Prod.map, id_eq]
    change (Comp.ret _).eval ρ₃ = _
    have hRegFst : (Expr.fst (regSessOptMultiE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        L (.snd .v0) (.snd (.snd (.fst .v0))))).eval ρ₃ = optIdx := by
      rw [fst_eval, hRegPair]
    have hRegSnd : (Expr.snd (regSessOptMultiE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        L (.snd .v0) (.snd (.snd (.fst .v0))))).eval ρ₃ = h₂_enc := by
      rw [snd_eval, hRegPair]
    rw [eval_ret, pair_eval, fsMultiHsSetCache_eval _ _ ρ₃ (hsMDec h₂_enc)
      (hRegSnd.trans hReg.2.1)]
    congr 1
    · congr 1
      · have hCaseOpt : ∀ {α β} (e : Expr OO _ (.opt α)) (n : Expr OO _ β) (s : Expr OO (α :: _) β),
            (Expr.caseOpt e n s).eval ρ₃ =
              match e.eval ρ₃ with | none => n.eval ρ₃ | some x => s.eval (Env.cons x ρ₃) :=
          fun e _ _ => by dsimp only [Expr.eval]; cases e.eval ρ₃ <;> rfl
        rw [some_eval, pair_eval, pair_eval, pair_eval, hCaseOpt, hRegFst]
        cases optIdx <;>
          simp [ρ₃, ρ₂, ρ₁, hSend, hFsInitS, Expr.eval, Expr.v0, Expr.v1, Expr.v2,
            Env.get_cons_zero]
      · congr 1; simp only [tset_eval_eq_update]
        have hca : (fsMultiHsCache (.snd (regSessOptMultiE (ckaInitA := ckaInitA)
            (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
            (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
            (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
            (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
            (defaultE := defaultE) L (.snd .v0) (.snd (.snd (.fst .v0)))))).eval ρ₃ =
            (hsMDec h₂_enc).cache := by
          unfold fsMultiHsCache; rw [fst_eval, hRegSnd]; rfl
        have hkEval : (Expr.fst (.snd (Expr.v2 (O := OO)))).eval ρ₃ = t := rfl
        have hvEval : (Expr.some (.pair
            (.fst (.snd (Expr.op (O := OO) CKAOp.ckaSend (.pair (.fst (.snd (.snd .v2))) .v1))))
            (.pair (.fst (.fst .v0))
              (.pair (.fst (.snd (.fst .v0)))
                (.fst (regSessOptMultiE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
                  (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
                  (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
                  (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
                  (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
                  L (.snd .v0) (.snd (.snd (.fst .v0))))))))).eval ρ₃ =
            some ((cka.send γ coins).2.1, σ', k, optIdx) := by
          rw [some_eval, pair_eval, pair_eval, pair_eval, hRegFst]
          simp [ρ₃, ρ₂, ρ₁, hSend, Expr.eval, Expr.v0, Expr.v1, Expr.v2]
        rw [hca, hkEval, hvEval]
  · intro res hmem
    rw [hRHS, mem_support_bind_iff] at hmem
    obtain ⟨coins, _, hmem⟩ := hmem
    simp only [StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨⟨σ', k, sid⟩, h₁⟩, hmemRoot, hmem⟩ := hmem
    set ρ₂ := Env.cons (t := .base CKASort.ccoins) coins ρ₁
    have hRoot := rootFSMultiC_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins)
      prng hPrngUp heqI hSampI hSampK L mo (.fst .v1) (.fst (.snd .v1))
      (.snd (.snd (Expr.op (O := OO) CKAOp.ckaSend (.pair (.fst (.snd (.snd .v1))) .v0))))
      (.fst (.snd (.snd (.snd .v1)))) ρ₂ h rfl hHB.1
    have hIkEval : (Expr.snd (.snd (Expr.op (O := OO) CKAOp.ckaSend
        (.pair (.fst (.snd (.snd .v1))) .v0)))).eval ρ₂ = (cka.send γ coins).2.2 := by
      simp [ρ₂, ρ₁, hSend, Expr.eval, Expr.v0, Expr.v1]
    have htEval : (Expr.fst (.snd (Expr.v1 (O := OO)))).eval ρ₂ = t := rfl
    have hσEval : (Expr.fst (.snd (.snd (.snd (Expr.v1 (O := OO)))))).eval ρ₂ = σ := rfl
    rw [hIkEval, htEval, hσEval] at hRoot
    have ⟨hTbl₁, hSes₁, hBk₁⟩ := hRoot.2 ((σ', k, sid), h₁) hmemRoot
    have hSesL₁ : h₁.sessions.length ≤ L := hSes₁ ▸ hHB.2.1
    set ρ₃ := Env.cons
      (t := .prod (.prod (.base CKASort.sig) (.prod (.base CKASort.k) (.opt (.base CKASort.i))))
        mHsTy)
      ((σ', k, sid), hsMEnc h₁) ρ₂
    have hReg := regSessOptMultiE_eval_pair (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) heqI L (.snd .v0) (.snd (.snd (.fst .v0))) ρ₃ h₁ rfl hSesL₁
    have hsidEval : (Expr.snd (.snd (.fst (Expr.v0 (O := OO))))).eval ρ₃ = sid := rfl
    rw [hsidEval] at hReg
    rw [hReg.1] at hmem
    simp only [support_pure, Set.mem_singleton_iff, exists_eq_left,
      StateT.run_modify, StateT.run_pure] at hmem
    subst hmem
    exact ⟨by rw [hReg.2.2.1]; exact hTbl₁,
      by rw [← hSes₁]; exact hReg.2.2.2.1,
      by rw [hReg.2.2.2.2, hBk₁]⟩

private theorem fsMultiStartRecvC_eval [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (hRecv : ckaReceive = cka.receive)
    (hPrngUp : prngUp = prng.up)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (heqT : eqT = (· == ·))
    (heqI : eqI = (· == ·))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (L Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    {Γ'} (hE : Expr OO Γ' mHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' (.base .γ)) (σE : Expr OO Γ' (.base .sig))
    (tnE : Expr OO Γ' (.base .t)) (ρ : Env Γ')
    (h : FSMultiState T RSt K I E) (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (hHB : FSMultiHBounded L h) (hh : hE.eval ρ = hsMEnc h) :
    (fsMultiStartRecvC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L mo gMain hE ctxE pE tE γE σE tnE).eval ρ =
      Prod.map id hsMEnc <$>
        ((hooksFSMulti cka prng fs Δcka mo gMain la).startRecv ctx P
          (tE.eval ρ) (γE.eval ρ) (σE.eval ρ) (tnE.eval ρ)).run h ∧
    ∀ res ∈ support (((hooksFSMulti cka prng fs Δcka mo gMain la).startRecv ctx P
        (tE.eval ρ) (γE.eval ρ) (σE.eval ρ) (tnE.eval ρ)).run h),
      res.2.table.length ≤ h.table.length + 1 ∧
      res.2.sessions.length ≤ h.sessions.length + 1 ∧
      res.2.book = h.book := by
  unfold fsMultiStartRecvC hooksFSMulti
  dsimp only
  rw [eval_bind_ret]
  set t : ℕ := tE.eval ρ
  set γ : Γ := γE.eval ρ
  set σ : RSt := σE.eval ρ
  set Tn : T := tnE.eval ρ
  have h0 : (Expr.pair hE (.pair tE (.pair γE (.pair σE tnE)))).eval ρ =
      (hsMEnc h, t, γ, σ, Tn) := by
    simp [Expr.eval, hh, t, γ, σ, Tn]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := .prod mHsTy (.prod .nat (.prod (.base CKASort.γ)
      (.prod (.base CKASort.sig) (.base CKASort.t)))))
    (hsMEnc h, t, γ, σ, Tn) ρ
  have hNoneBranch :
      (Comp.ite (O := OO) (I := IIM) (.bool gMain)
        (.ret (.pair (.some .none) (.fst .v0)))
        (.ite (.and (.bool mo.auth) (.eqN (.fst (.snd .v0)) (.nat mo.tStar)))
          (.ite (.bool (mo.tL.isSome && decide (mo.tStar = mo.tH)))
            (.ret (.pair .none (.fst .v0)))
            (.bind
              (lookupMultiFC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
                (sampI := sampI) (sampK := sampK) L (.fst .v0)
                (.snd (Expr.op (O := OO) CKAOp.ckaReceive
                  (.pair (.fst (.snd (.snd .v0))) (.snd (.snd (.snd (.snd .v0))))))))
              (.ret (.pair
                (.some (.some (.pair
                  (.fst (Expr.op (O := OO) CKAOp.ckaReceive
                    (.pair (.fst (.snd (.snd .v1))) (.snd (.snd (.snd (.snd .v1)))))))
                  (.pair
                    (.fst (Expr.op (O := OO) CKAOp.prngUp
                      (.pair (.fst (.snd (.snd (.snd .v1))))
                        (.snd (Expr.op (O := OO) CKAOp.ckaReceive
                          (.pair (.fst (.snd (.snd .v1))) (.snd (.snd (.snd (.snd .v1))))))))))
                    (Expr.inr (t := .base CKASort.rs) (.fst (regSessMultiE L (.snd .v0)
                      (.snd (Expr.op (O := OO) CKAOp.ckaReceive
                        (.pair (.fst (.snd (.snd .v1))) (.snd (.snd (.snd (.snd .v1))))))))))))))
                (.snd (regSessMultiE L (.snd .v0)
                  (.snd (Expr.op (O := OO) CKAOp.ckaReceive
                    (.pair (.fst (.snd (.snd .v1))) (.snd (.snd (.snd (.snd .v1)))))))))))))
          (.ret (.pair (.some .none) (.fst .v0))))).eval ρ₁ =
      Prod.map id hsMEnc <$>
        ((if gMain = true then pure (some none)
          else if (mo.auth && decide (t = mo.tStar)) = true then
            if (mo.tL.isSome && decide (mo.tStar = mo.tH)) = true then pure none
            else do
              let _ ← lookupMultiF (cka.receive γ Tn).2
              let sIdx ← regSessMulti (cka.receive γ Tn).2
              pure (some (some ((cka.receive γ Tn).1, (prng.up σ (cka.receive γ Tn).2).1,
                (Sum.inr sIdx : RS ⊕ ℕ))))
          else pure (some none) :
          HM (FSMultiSpec SS RS T M E) (FSMultiState T RSt K I E) _).run h) ∧
      ∀ res ∈ support
        ((if gMain = true then pure (some none)
          else if (mo.auth && decide (t = mo.tStar)) = true then
            if (mo.tL.isSome && decide (mo.tStar = mo.tH)) = true then pure none
            else do
              let _ ← lookupMultiF (cka.receive γ Tn).2
              let sIdx ← regSessMulti (cka.receive γ Tn).2
              pure (some (some ((cka.receive γ Tn).1, (prng.up σ (cka.receive γ Tn).2).1,
                (Sum.inr sIdx : RS ⊕ ℕ))))
          else pure (some none) :
          HM (FSMultiSpec SS RS T M E) (FSMultiState T RSt K I E) _).run h),
        res.2.table.length ≤ h.table.length + 1 ∧
        res.2.sessions.length ≤ h.sessions.length + 1 ∧
        res.2.book = h.book := by
    rw [eval_ite]
    cases gMain
    · simp only [Bool.false_eq_true, ↓reduceIte, Expr.eval]
      rw [eval_ite]
      have hCond1 : (Expr.and (.bool mo.auth)
          (.eqN (.fst (.snd (Expr.v0 (O := OO)))) (.nat mo.tStar))).eval ρ₁ =
          (mo.auth && decide (t = mo.tStar)) := rfl
      rw [hCond1]
      by_cases hc1 : (mo.auth && decide (t = mo.tStar)) = true
      · simp only [hc1, ↓reduceIte]
        rw [eval_ite]
        have hCond2 : (Expr.bool (O := OO) (mo.tL.isSome && decide (mo.tStar = mo.tH))).eval ρ₁ =
            (mo.tL.isSome && decide (mo.tStar = mo.tH)) := rfl
        rw [hCond2]
        by_cases hc2 : (mo.tL.isSome && decide (mo.tStar = mo.tH)) = true
        · simp only [hc2, ↓reduceIte]
          refine ⟨?_, ?_⟩
          · simp [ρ₁, StateT.run_pure, Comp.eval, Prod.map, Expr.eval, Expr.v0]
          · intro res hmem
            simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
            subst hmem
            exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, rfl⟩
        · simp only [hc2, Bool.false_eq_true, ↓reduceIte]
          have hLk := lookupMultiFC_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
            (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
            (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
            (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
            (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
            (sampCCoins := sampCCoins) (sampI := sampI)
            heqI hSampK L (.fst .v0)
            (.snd (Expr.op (O := OO) CKAOp.ckaReceive
              (.pair (.fst (.snd (.snd .v0))) (.snd (.snd (.snd (.snd .v0))))))) ρ₁ h rfl hHB.1
          have hKk2 : (Expr.snd (Expr.op (O := OO) CKAOp.ckaReceive
              (.pair (.fst (.snd (.snd .v0))) (.snd (.snd (.snd (.snd .v0))))))).eval ρ₁ =
              (cka.receive γ Tn).2 := by
            simp [ρ₁, hRecv, Expr.eval, Expr.v0]
          rw [hKk2] at hLk
          refine ⟨?_, ?_⟩
          · rw [eval_bind, hLk.1, StateT.run_bind, bind_map_left, map_bind]
            refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨k', h₁⟩ hmemLk => ?_
            have ⟨_, hSes₁, _⟩ := hLk.2 (k', h₁) hmemLk
            have hSesL₁ : h₁.sessions.length ≤ L := hSes₁ ▸ hHB.2.1
            set ρ₂ := Env.cons (t := .prod (.base CKASort.k) mHsTy) (k', hsMEnc h₁) ρ₁
            have hReg := regSessMultiE_eval_pair (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
              (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
              (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
              (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
              (lam := lam) (defaultE := defaultE) heqI L (.snd .v0)
              (.snd (Expr.op (O := OO) CKAOp.ckaReceive
                (.pair (.fst (.snd (.snd .v1))) (.snd (.snd (.snd (.snd .v1))))))) ρ₂ h₁ rfl hSesL₁
            have hKk2' : (Expr.snd (Expr.op (O := OO) CKAOp.ckaReceive
                (.pair (.fst (.snd (.snd .v1))) (.snd (.snd (.snd (.snd .v1))))))).eval ρ₂ =
                (cka.receive γ Tn).2 := by
              simp [ρ₂, ρ₁, hRecv, Expr.eval, Expr.v1]
            rw [hKk2'] at hReg
            rcases hRegPair : (regSessMultiE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
              (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
              (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
              (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
              (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
              L (.snd .v0)
              (.snd (Expr.op (O := OO) CKAOp.ckaReceive
                (.pair (.fst (.snd (.snd .v1))) (.snd (.snd (.snd (.snd .v1)))))))).eval ρ₂ with
              ⟨sIdx, h₂_enc⟩
            rw [hRegPair] at hReg
            rw [StateT.run_bind, hReg.1]
            simp only [pure_bind, StateT.run_pure, map_pure, Prod.map, id_eq]
            change (Comp.ret _).eval ρ₂ = _
            rw [eval_ret]
            dsimp only [Expr.eval]
            erw [hRegPair]
            congr 1
            refine Prod.ext ?_ hReg.2.1
            simp [ρ₂, ρ₁, hRecv, hPrngUp, Expr.eval, Expr.v1]
          · intro res hmem
            simp only [StateT.run_bind, mem_support_bind_iff] at hmem
            obtain ⟨⟨k', h₁⟩, hmemLk, hmem⟩ := hmem
            have ⟨hTbl₁, hSes₁, hBk₁⟩ := hLk.2 (k', h₁) hmemLk
            have hSesL₁ : h₁.sessions.length ≤ L := hSes₁ ▸ hHB.2.1
            set ρ₂ := Env.cons (t := .prod (.base CKASort.k) mHsTy) (k', hsMEnc h₁) ρ₁
            have hReg := regSessMultiE_eval_pair (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
              (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
              (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
              (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
              (lam := lam) (defaultE := defaultE) heqI L (.snd .v0)
              (.snd (Expr.op (O := OO) CKAOp.ckaReceive
                (.pair (.fst (.snd (.snd .v1))) (.snd (.snd (.snd (.snd .v1))))))) ρ₂ h₁ rfl hSesL₁
            have hKk2' : (Expr.snd (Expr.op (O := OO) CKAOp.ckaReceive
                (.pair (.fst (.snd (.snd .v1))) (.snd (.snd (.snd (.snd .v1))))))).eval ρ₂ =
                (cka.receive γ Tn).2 := by
              simp [ρ₂, ρ₁, hRecv, Expr.eval, Expr.v1]
            rw [hKk2'] at hReg
            rw [hReg.1] at hmem
            simp only [support_pure, Set.mem_singleton_iff, exists_eq_left,
              StateT.run_pure] at hmem
            subst hmem
            exact ⟨by rw [hReg.2.2.1]; exact hTbl₁,
              by rw [← hSes₁]; exact hReg.2.2.2.1,
              by rw [hReg.2.2.2.2, hBk₁]⟩
      · simp only [hc1, Bool.false_eq_true, ↓reduceIte]
        refine ⟨?_, ?_⟩
        · simp [ρ₁, StateT.run_pure, Comp.eval, Prod.map, Expr.eval, Expr.v0]
        · intro res hmem
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
          subst hmem
          exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, rfl⟩
    · simp only [↓reduceIte, Expr.eval]
      refine ⟨?_, ?_⟩
      · simp [ρ₁, StateT.run_pure, Comp.eval, Prod.map, Expr.eval, Expr.v0]
      · intro res hmem
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem
        exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, rfl⟩
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rcases hcache : h.cache t with _ | ⟨Tc, σc, k, optIdx⟩
  · have hHonNone :
        (Expr.caseOpt (O := OO) (.tget (fsMultiHsCache (.fst .v0)) (.fst (.snd .v0))) .none
          (.ite (Expr.op (O := OO) CKAOp.eqT (.pair (.fst .v0) (.snd (.snd (.snd (.snd .v1))))))
            (.some (.snd .v0))
            .none)).eval ρ₁ = none := by
      simp [ρ₁, hcache, fsMultiHsCache, fsMultiHsEnc, Expr.eval, Expr.v0]
    rw [eval_caseOpt_none hHonNone]
    exact hNoneBranch
  · by_cases hEq : Tc = Tn
    · have hHonSome :
          (Expr.caseOpt (O := OO) (.tget (fsMultiHsCache (.fst .v0)) (.fst (.snd .v0))) .none
            (.ite (Expr.op (O := OO) CKAOp.eqT (.pair (.fst .v0) (.snd (.snd (.snd (.snd .v1))))))
              (.some (.snd .v0))
              .none)).eval ρ₁ = some (σc, k, optIdx) := by
        simp [ρ₁, hcache, hEq, heqT, fsMultiHsCache, fsMultiHsEnc, Expr.eval, Expr.v0, Expr.v1]
      rw [eval_caseOpt_some hHonSome, eval_ret]
      simp only [hEq, ↓reduceIte, StateT.run_pure]
      refine ⟨?_, ?_⟩
      · cases optIdx <;>
          simp [ρ₁, hRecv, hFsInitR, Prod.map, Expr.eval, Expr.v0, Expr.v1]
      · intro res hmem
        simp only [support_pure, Set.mem_singleton_iff] at hmem
        subst hmem
        exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, rfl⟩
    · have hHonNone :
          (Expr.caseOpt (O := OO) (.tget (fsMultiHsCache (.fst .v0)) (.fst (.snd .v0))) .none
            (.ite (Expr.op (O := OO) CKAOp.eqT (.pair (.fst .v0) (.snd (.snd (.snd (.snd .v1))))))
              (.some (.snd .v0))
              .none)).eval ρ₁ = none := by
        simp [ρ₁, hcache, hEq, heqT, fsMultiHsCache, fsMultiHsEnc, Expr.eval, Expr.v0, Expr.v1]
      rw [eval_caseOpt_none hHonNone]
      simp only [hEq, ↓reduceIte]
      exact hNoneBranch

private def liftFSMultiRaw (sIdx : ℕ) {α : Type}
    (x : FSAEAD.AdversaryComp SS RS (Header T) M E α) :
    TComp (FSMultiSpec SS RS T M E) α :=
  simulateQ (fun
    | .inl n => query (spec := unifSpec + FSMultiSpec SS RS T M E) (.inl n)
    | .inr q => query (spec := unifSpec + FSMultiSpec SS RS T M E) (.inr ⟨sIdx, q⟩)) x

private theorem liftFSMulti_eq (sIdx : ℕ) {α : Type}
    (x : FSAEAD.AdversaryComp SS RS (Header T) M E α) :
    liftFSMulti (T := T) (Sig := RSt) (K := K) (I := I) sIdx x =
      StateT.lift (liftFSMultiRaw sIdx x) := rfl

private theorem query_fsMulti_tr_eval {Γ'}
    (arg : Expr OO Γ' (.prod .nat (.prod hdrTy (.base .msg)))) (ρ : Env Γ') :
    (@Comp.query _ _ _ OO IIM Γ' FSHdrTag.tr arg).eval ρ =
      liftFSMultiRaw (arg.eval ρ).1
        (FSAEAD.transmitQuery (SenderState := SS) (ReceiverState := RS)
          (arg.eval ρ).2.1 (arg.eval ρ).2.2) := by
  simp [Comp.eval, fsaeadMultiHeaderAdIface, liftFSMultiRaw, FSAEAD.transmitQuery]

private theorem query_fsMulti_ch_eval {Γ'}
    (arg : Expr OO Γ' (.prod .nat (.prod hdrTy (.prod (.base .msg) (.base .msg))))) (ρ : Env Γ') :
    (@Comp.query _ _ _ OO IIM Γ' FSHdrTag.ch arg).eval ρ =
      liftFSMultiRaw (arg.eval ρ).1
        (FSAEAD.challengeQuery (SenderState := SS) (ReceiverState := RS)
          (arg.eval ρ).2.1 (arg.eval ρ).2.2.1 (arg.eval ρ).2.2.2) := by
  simp [Comp.eval, fsaeadMultiHeaderAdIface, liftFSMultiRaw, FSAEAD.challengeQuery]

private theorem query_fsMulti_cs_eval {Γ'}
    (arg : Expr OO Γ' (.prod .nat .unit)) (ρ : Env Γ') :
    (@Comp.query _ _ _ OO IIM Γ' FSHdrTag.cs arg).eval ρ =
      liftFSMultiRaw (arg.eval ρ).1
        (FSAEAD.corruptSenderQuery (SenderState := SS) (ReceiverState := RS)
          (AssocData := Header T) (Message := M) (Ciphertext := E)) := by
  simp [Comp.eval, fsaeadMultiHeaderAdIface, liftFSMultiRaw, FSAEAD.corruptSenderQuery]

private theorem query_fsMulti_dl_eval {Γ'}
    (arg : Expr OO Γ' (.prod .nat hdrCtTy)) (ρ : Env Γ') :
    (@Comp.query _ _ _ OO IIM Γ' FSHdrTag.dl arg).eval ρ =
      Option.map fsHdrRrEnc <$>
        liftFSMultiRaw (arg.eval ρ).1
          (FSAEAD.deliverQuery (SenderState := SS) (ReceiverState := RS)
            (arg.eval ρ).2.1 (arg.eval ρ).2.2) := by
  simp [Comp.eval, fsaeadMultiHeaderAdIface, liftFSMultiRaw, FSAEAD.deliverQuery]

private theorem query_fsMulti_ij_eval {Γ'}
    (arg : Expr OO Γ' (.prod .nat hdrCtTy)) (ρ : Env Γ') :
    (@Comp.query _ _ _ OO IIM Γ' FSHdrTag.ij arg).eval ρ =
      Option.map fsHdrRrEnc <$>
        liftFSMultiRaw (arg.eval ρ).1
          (FSAEAD.injectQuery (SenderState := SS) (ReceiverState := RS)
            (arg.eval ρ).2.1 (arg.eval ρ).2.2) := by
  simp [Comp.eval, fsaeadMultiHeaderAdIface, liftFSMultiRaw, FSAEAD.injectQuery]

private theorem fsMultiFsSendC_eval [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (hFsSend : fsSend = fs.send)
    (Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    {Γ'} (hE : Expr OO Γ' mHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (ssvE : Expr OO Γ' (.sum (.base .ss) .nat)) (hdrE : Expr OO Γ' hdrTy)
    (mE : Expr OO Γ' (.base .msg))
    (pairE : Expr OO Γ' (.opt (.prod (.base .msg) (.base .msg)))) (ρ : Env Γ')
    (h : FSMultiState T RSt K I E) (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (hh : hE.eval ρ = hsMEnc h)
    (hctx : ctxE.eval ρ = cGsEnc vpMEnc ctx) (hp : pE.eval ρ = partyEnc P) :
    (fsMultiFsSendC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) Δcka la hE ctxE pE tE ssvE hdrE mE pairE).eval ρ =
      Prod.map id hsMEnc <$>
        ((hooksFSMulti cka prng fs Δcka mo gMain la).fsSend ctx P (tE.eval ρ)
          (ssvE.eval ρ) (hdrE.eval ρ) (mE.eval ρ) (pairE.eval ρ)).run h := by
  unfold fsMultiFsSendC hooksFSMulti
  dsimp only
  set ssv : SS ⊕ ℕ := ssvE.eval ρ
  set hdr : Header T := hdrE.eval ρ
  set m : M := mE.eval ρ
  set pair : Option (M × M) := pairE.eval ρ
  have h0 : (Expr.pair hE (.pair ctxE (.pair pE (.pair ssvE (.pair hdrE (.pair mE pairE)))))).eval
      ρ = (hsMEnc h, cGsEnc vpMEnc ctx, partyEnc P, ssv, hdr, m, pair) := by
    simp [Expr.eval, hh, hctx, hp, ssv, hdr, m, pair]
  set ρ₁ := Env.cons
    (t := .prod mHsTy (.prod (cGsTy mVpTy) (.prod .bool (.prod (.sum (.base CKASort.ss) .nat)
      (.prod hdrTy (.prod (.base CKASort.msg)
        (.opt (.prod (.base CKASort.msg) (.base CKASort.msg)))))))))
    (hsMEnc h, cGsEnc vpMEnc ctx, partyEnc P, ssv, hdr, m, pair) ρ
  cases la
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [eval_bind_ret, h0]
    rcases ssv with ss | sIdx
    · rw [eval_caseSum_inl rfl, eval_ret]
      simp [StateT.run_pure, hFsSend, Prod.map, Expr.eval, Expr.v0, Expr.v1]
    · rw [eval_caseSum_inr rfl]
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      set ρ₂ := Env.cons (t := .nat) sIdx ρ₁
      set bk := (h.book sIdx).getD {}
      have hSafe : (cSafeChE (2 + Δcka) (.fst (.snd (Expr.v1 (O := OO))))
          (.fst (.snd (.snd .v1)))).eval ρ₂ = ctx.safeCh (2 + Δcka) P :=
        cSafeChE_eval vpMEnc (O' := OO) (2 + Δcka)
          (.fst (.snd .v1)) (.fst (.snd (.snd .v1))) ρ₂ ctx P rfl rfl
      have hBk0 : (fsMultiHsGetBookAt (O := OO) (.fst .v1) .v0).eval ρ₂ =
          (bk.sCorr, bk.fsCount, bk.fsTrans) :=
        fsMultiHsGetBookAt_eval (.fst .v1) .v0 ρ₂ h rfl
      have hCond : (Expr.and (.not (cSafeChE (2 + Δcka) (.fst (.snd (Expr.v1 (O := OO))))
          (.fst (.snd (.snd .v1))))) (.not (.fst (fsMultiHsGetBookAt (.fst .v1) .v0)))).eval ρ₂ =
          (!(ctx.safeCh (2 + Δcka) P) && !bk.sCorr) := by
        rw [and_eval, not_eval, not_eval, hSafe, fst_eval, hBk0]
      have hSendTrue : ∀ (h₁ : FSMultiState T RSt K I E),
          (Comp.ite (O := OO) (I := IIM) (.not (.fst .v0))
            (.ret (.pair .none (.snd .v0)))
            (.bind
              (.caseOpt (.snd (.snd (.snd (.snd (.snd (.snd .v2))))))
                (@Comp.query _ _ _ OO IIM _ FSHdrTag.tr
                  (.pair .v1 (.pair (.fst (.snd (.snd (.snd (.snd .v2)))))
                    (.fst (.snd (.snd (.snd (.snd (.snd .v2)))))))))
                (@Comp.query _ _ _ OO IIM _ FSHdrTag.ch
                  (.pair .v2 (.pair (.fst (.snd (.snd (.snd (.snd .v3))))) .v0))))
              (.caseOpt .v0
                (.ret (.pair .none (.snd .v1)))
                (.ret (.pair (.some (.pair (Expr.inr (t := .base CKASort.ss) .v3) .v0))
                  (fsMultiHsSetBookAt (.snd .v2) .v3
                    (.pair (.fst (fsMultiHsGetBookAt (.snd .v2) .v3))
                      (.pair (.add (.fst (.snd (fsMultiHsGetBookAt (.snd .v2) .v3))) (.nat 1))
                        (.cons (.pair (.add (.fst (.snd (fsMultiHsGetBookAt (.snd .v2) .v3))) (.nat 1))
                          (.pair (.fst (.snd (.snd (.snd (.snd .v4))))) .v0))
                          (.snd (.snd (fsMultiHsGetBookAt (.snd .v2) .v3)))))))))))).eval
            (Env.cons (t := .prod .bool mHsTy) (true, hsMEnc h₁) ρ₂) =
          Prod.map id hsMEnc <$>
            ((do
                let e? ← match pair with
                  | some (m₀, m₁) =>
                    liftFSMulti sIdx (FSAEAD.challengeQuery (SenderState := SS) (ReceiverState := RS)
                      hdr m₀ m₁)
                  | none =>
                    liftFSMulti sIdx (FSAEAD.transmitQuery (SenderState := SS) (ReceiverState := RS)
                      hdr m)
                match e? with
                | none => return none
                | some e =>
                  modify fun (s : FSMultiState T RSt K I E) =>
                    let b := (s.book sIdx).getD {}
                    let cnt' := b.fsCount + 1
                    let b' : FSMultiBook T E := { b with fsCount := cnt', fsTrans := (cnt', hdr, e) :: b.fsTrans }
                    { s with book := Function.update s.book sIdx (some b') }
                  return some (.inr sIdx, e) :
              HM (FSMultiSpec SS RS T M E) (FSMultiState T RSt K I E)
                (Option ((SS ⊕ ℕ) × E))).run h₁) := by
        intro h₁
        set ρ₃ := Env.cons (t := .prod .bool mHsTy) (true, hsMEnc h₁) ρ₂
        rw [eval_ite]
        have hNotOk : (Expr.not (.fst (Expr.v0 (O := OO)))).eval ρ₃ = false := rfl
        rw [hNotOk]
        simp only [Bool.false_eq_true, ↓reduceIte, eval_bind]
        rcases pair with _ | ⟨m₀, m₁⟩
        · rw [eval_caseOpt_none rfl, query_fsMulti_tr_eval]
          simp only [ρ₃, ρ₂, ρ₁, liftFSMulti_eq, StateT.run_bind, StateT.run_lift,
            bind_assoc, pure_bind, map_bind, Expr.eval, Expr.v1, Expr.v2]
          refine bind_congr fun e? => ?_
          rcases e? with _ | ct
          · rw [eval_caseOpt_none rfl, eval_ret]
            simp [StateT.run_pure, Prod.map, Expr.eval]
          · rw [eval_caseOpt_some rfl, eval_ret, pair_eval]
            set ρ₄ := Env.cons (t := .base CKASort.ct) ct
              (Env.cons (t := .opt (.base CKASort.ct)) (some ct) ρ₃)
            have hBk1 := fsMultiHsGetBookAt_eval (.snd (Expr.v2 (O := OO))) .v3 ρ₄ h₁ rfl
            have hIdx4 : (Expr.v3 (O := OO)).eval ρ₄ = sIdx := rfl
            rw [hIdx4] at hBk1
            have hSet := fsMultiHsSetBookAt_eval (.snd (Expr.v2 (O := OO))) .v3
              (.pair (.fst (fsMultiHsGetBookAt (.snd .v2) .v3))
                (.pair (.add (.fst (.snd (fsMultiHsGetBookAt (.snd .v2) .v3))) (.nat 1))
                  (.cons (.pair (.add (.fst (.snd (fsMultiHsGetBookAt (.snd .v2) .v3))) (.nat 1))
                    (.pair (.fst (.snd (.snd (.snd (.snd .v4))))) .v0))
                    (.snd (.snd (fsMultiHsGetBookAt (.snd .v2) .v3)))))) ρ₄ h₁ rfl
              (sc := ((h₁.book sIdx).getD {}).sCorr)
              (cnt := ((h₁.book sIdx).getD {}).fsCount + 1)
              (tr := (((h₁.book sIdx).getD {}).fsCount + 1, hdr, ct) :: ((h₁.book sIdx).getD {}).fsTrans)
              (by simp only [Expr.eval, hBk1]; rfl)
            erw [hSet]
            simp [ρ₄, ρ₃, ρ₂, StateT.run_modify, Prod.map, Expr.eval, Expr.v0, Expr.v3]
        · rw [eval_caseOpt_some rfl, query_fsMulti_ch_eval]
          simp only [ρ₃, ρ₂, ρ₁, liftFSMulti_eq, StateT.run_bind, StateT.run_lift,
            bind_assoc, pure_bind, map_bind, Expr.eval, Expr.v0, Expr.v2, Expr.v3]
          refine bind_congr fun e? => ?_
          rcases e? with _ | ct
          · rw [eval_caseOpt_none rfl, eval_ret]
            simp [StateT.run_pure, Prod.map, Expr.eval, Expr.v1]
          · rw [eval_caseOpt_some rfl, eval_ret, pair_eval]
            set ρ₄ := Env.cons (t := .base CKASort.ct) ct
              (Env.cons (t := .opt (.base CKASort.ct)) (some ct) ρ₃)
            have hBk1 := fsMultiHsGetBookAt_eval (.snd (Expr.v2 (O := OO))) .v3 ρ₄ h₁ rfl
            have hIdx4 : (Expr.v3 (O := OO)).eval ρ₄ = sIdx := rfl
            rw [hIdx4] at hBk1
            have hSet := fsMultiHsSetBookAt_eval (.snd (Expr.v2 (O := OO))) .v3
              (.pair (.fst (fsMultiHsGetBookAt (.snd .v2) .v3))
                (.pair (.add (.fst (.snd (fsMultiHsGetBookAt (.snd .v2) .v3))) (.nat 1))
                  (.cons (.pair (.add (.fst (.snd (fsMultiHsGetBookAt (.snd .v2) .v3))) (.nat 1))
                    (.pair (.fst (.snd (.snd (.snd (.snd .v4))))) .v0))
                    (.snd (.snd (fsMultiHsGetBookAt (.snd .v2) .v3)))))) ρ₄ h₁ rfl
              (sc := ((h₁.book sIdx).getD {}).sCorr)
              (cnt := ((h₁.book sIdx).getD {}).fsCount + 1)
              (tr := (((h₁.book sIdx).getD {}).fsCount + 1, hdr, ct) :: ((h₁.book sIdx).getD {}).fsTrans)
              (by simp only [Expr.eval, hBk1]; rfl)
            erw [hSet]
            simp [ρ₄, ρ₃, ρ₂, StateT.run_modify, Prod.map, Expr.eval, Expr.v3]
      rw [eval_bind, eval_ite, hCond]
      by_cases hc : (!(ctx.safeCh (2 + Δcka) P) && !bk.sCorr) = true
      · simp only [hc, ↓reduceIte, eval_bind, query_fsMulti_cs_eval, liftFSMulti_eq,
          StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind,
          Expr.eval, Expr.v0]
        refine bind_congr fun cs? => ?_
        rcases cs? with _ | ss'
        · rw [eval_caseOpt_none rfl, eval_ret, pure_bind]
          simp [ρ₂, ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v2]
        · rw [eval_caseOpt_some rfl, eval_ret, pure_bind]
          simp only [StateT.run_bind, StateT.run_modify, pure_bind,
            Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          set ρ_cs := Env.cons (t := .base CKASort.ss) ss'
            (Env.cons (t := .opt (.base CKASort.ss)) (some ss') ρ₂)
          have hBkCs := fsMultiHsGetBookAt_eval (.fst (Expr.v3 (O := OO))) .v2 ρ_cs h rfl
          have hIdxCs : (Expr.v2 (O := OO)).eval ρ_cs = sIdx := rfl
          rw [hIdxCs] at hBkCs
          have hSetCs := fsMultiHsSetBookAt_eval (.fst (Expr.v3 (O := OO))) .v2
            (.pair (.bool true)
              (.pair (.fst (.snd (fsMultiHsGetBookAt (.fst .v3) .v2)))
                (.snd (.snd (fsMultiHsGetBookAt (.fst .v3) .v2))))) ρ_cs h rfl
            (sc := true) (cnt := bk.fsCount) (tr := bk.fsTrans)
            (by simp only [Expr.eval, hBkCs]; rfl)
          let bk' : FSMultiBook T E := { bk with sCorr := true }
          let h' : FSMultiState T RSt K I E :=
            { h with book := Function.update h.book sIdx (some bk') }
          have hPairCs : (Expr.pair (O := OO) (.bool true)
              (fsMultiHsSetBookAt (.fst .v3) .v2
                (.pair (.bool true)
                  (.pair (.fst (.snd (fsMultiHsGetBookAt (.fst .v3) .v2)))
                    (.snd (.snd (fsMultiHsGetBookAt (.fst .v3) .v2))))))).eval ρ_cs =
              (true, hsMEnc h') := by
            rw [pair_eval, hSetCs]; rfl
          rw [hPairCs]
          exact hSendTrue h'
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, eval_ret, pure_bind]
        have hPair0 : (Expr.pair (O := OO) (.bool true) (.fst .v1)).eval ρ₂ =
            (true, hsMEnc h) := rfl
        rw [hPair0]
        exact hSendTrue h
  · simp only [↓reduceIte]
    rw [eval_bind_ret, h0]
    rcases ssv with ss | sIdx
    · rw [eval_caseSum_inl rfl, eval_ret]
      simp [StateT.run_pure, hFsSend, Prod.map, Expr.eval, Expr.v0, Expr.v1]
    · rw [eval_caseSum_inr rfl, eval_ite]
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      set ρ₂ := Env.cons (t := .nat) sIdx ρ₁
      set bk := (h.book sIdx).getD {}
      have hSafe : (cSafeChE (2 + Δcka) (.fst (.snd (Expr.v1 (O := OO))))
          (.fst (.snd (.snd .v1)))).eval ρ₂ = ctx.safeCh (2 + Δcka) P :=
        cSafeChE_eval vpMEnc (O' := OO) (2 + Δcka)
          (.fst (.snd .v1)) (.fst (.snd (.snd .v1))) ρ₂ ctx P rfl rfl
      have hBk0 : (fsMultiHsGetBookAt (O := OO) (.fst .v1) .v0).eval ρ₂ =
          (bk.sCorr, bk.fsCount, bk.fsTrans) :=
        fsMultiHsGetBookAt_eval (.fst .v1) .v0 ρ₂ h rfl
      have hCond : (Expr.and (.not (cSafeChE (2 + Δcka) (.fst (.snd (Expr.v1 (O := OO))))
          (.fst (.snd (.snd .v1))))) (.not (.fst (fsMultiHsGetBookAt (.fst .v1) .v0)))).eval ρ₂ =
          (!(ctx.safeCh (2 + Δcka) P) && !bk.sCorr) := by
        rw [and_eval, not_eval, not_eval, hSafe, fst_eval, hBk0]
      rw [hCond]
      by_cases hc : (!(ctx.safeCh (2 + Δcka) P) && !bk.sCorr) = true
      · simp only [hc, ↓reduceIte, eval_ret, StateT.run_pure, Bool.not_false,
          Prod.map, map_pure, pair_eval]
        rfl
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, eval_bind,
          Bool.not_true]
        rcases pair with _ | ⟨m₀, m₁⟩
        · rw [eval_caseOpt_none rfl, query_fsMulti_tr_eval]
          simp only [ρ₂, ρ₁, liftFSMulti_eq, StateT.run_bind, StateT.run_lift,
            bind_assoc, pure_bind, map_bind, Expr.eval, Expr.v0, Expr.v1]
          refine bind_congr fun e? => ?_
          rcases e? with _ | ct
          · rw [eval_caseOpt_none rfl, eval_ret]
            simp [StateT.run_pure, Prod.map, Expr.eval, Expr.v2]
          · rw [eval_caseOpt_some rfl, eval_ret, pair_eval]
            set ρ₃ := Env.cons (t := .base CKASort.ct) ct
              (Env.cons (t := .opt (.base CKASort.ct)) (some ct) ρ₂)
            have hBk1 := fsMultiHsGetBookAt_eval (.fst (Expr.v3 (O := OO))) .v2 ρ₃ h rfl
            have hIdx3 : (Expr.v2 (O := OO)).eval ρ₃ = sIdx := rfl
            rw [hIdx3] at hBk1
            have hSet := fsMultiHsSetBookAt_eval (.fst (Expr.v3 (O := OO))) .v2
              (.pair (.fst (fsMultiHsGetBookAt (.fst .v3) .v2))
                (.pair (.add (.fst (.snd (fsMultiHsGetBookAt (.fst .v3) .v2))) (.nat 1))
                  (.cons (.pair (.add (.fst (.snd (fsMultiHsGetBookAt (.fst .v3) .v2))) (.nat 1))
                    (.pair (.fst (.snd (.snd (.snd (.snd .v3))))) .v0))
                    (.snd (.snd (fsMultiHsGetBookAt (.fst .v3) .v2)))))) ρ₃ h rfl
              (sc := bk.sCorr) (cnt := bk.fsCount + 1)
              (tr := (bk.fsCount + 1, hdr, ct) :: bk.fsTrans)
              (by simp only [Expr.eval, hBk1]; rfl)
            erw [hSet]
            simp [ρ₃, ρ₂, bk, StateT.run_modify, Prod.map, Expr.eval, Expr.v2]
        · rw [eval_caseOpt_some rfl, query_fsMulti_ch_eval]
          simp only [ρ₂, ρ₁, liftFSMulti_eq, StateT.run_bind, StateT.run_lift,
            bind_assoc, pure_bind, map_bind, Expr.eval, Expr.v0, Expr.v1, Expr.v2]
          refine bind_congr fun e? => ?_
          rcases e? with _ | ct
          · rw [eval_caseOpt_none rfl, eval_ret]
            simp [StateT.run_pure, Prod.map, Expr.eval]
          · rw [eval_caseOpt_some rfl, eval_ret, pair_eval]
            set ρ₃ := Env.cons (t := .base CKASort.ct) ct
              (Env.cons (t := .opt (.base CKASort.ct)) (some ct) ρ₂)
            have hBk1 := fsMultiHsGetBookAt_eval (.fst (Expr.v3 (O := OO))) .v2 ρ₃ h rfl
            have hIdx3 : (Expr.v2 (O := OO)).eval ρ₃ = sIdx := rfl
            rw [hIdx3] at hBk1
            have hSet := fsMultiHsSetBookAt_eval (.fst (Expr.v3 (O := OO))) .v2
              (.pair (.fst (fsMultiHsGetBookAt (.fst .v3) .v2))
                (.pair (.add (.fst (.snd (fsMultiHsGetBookAt (.fst .v3) .v2))) (.nat 1))
                  (.cons (.pair (.add (.fst (.snd (fsMultiHsGetBookAt (.fst .v3) .v2))) (.nat 1))
                    (.pair (.fst (.snd (.snd (.snd (.snd .v3))))) .v0))
                    (.snd (.snd (fsMultiHsGetBookAt (.fst .v3) .v2)))))) ρ₃ h rfl
              (sc := bk.sCorr) (cnt := bk.fsCount + 1)
              (tr := (bk.fsCount + 1, hdr, ct) :: bk.fsTrans)
              (by simp only [Expr.eval, hBk1]; rfl)
            erw [hSet]
            simp [ρ₃, ρ₂, bk, StateT.run_modify, Prod.map, Expr.eval, Expr.v2]

private theorem fsMultiFsRecvC_eval [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (heqT : eqT = (· == ·))
    (heqE : eqE = (· == ·))
    (L B Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    (hFsRecvB : ∀ rs hdr e,
      (fsReceive rs hdr e).map (fun (rs', i, m) => (rs', min i B, m)) =
        fs.receive rs hdr e)
    {Γ'} (hE : Expr OO Γ' mHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat)
    (rsvE : Expr OO Γ' (.sum (.base .rs) .nat)) (hdrE : Expr OO Γ' hdrTy)
    (eE : Expr OO Γ' (.base .ct)) (recE : Expr OO Γ' (.opt cRecTy)) (ρ : Env Γ')
    (h : FSMultiState T RSt K I E) (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (rec_ : Option (Record M (Header T × E)))
    (hHB : FSMultiHBoundedPost L h)
    (hh : hE.eval ρ = hsMEnc h) (hrec : recE.eval ρ = rec_.map cRecEnc) :
    (fsMultiFsRecvC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B la hE ctxE pE tE rsvE hdrE eE recE).eval ρ =
      Prod.map id hsMEnc <$>
        ((hooksFSMulti cka prng fs Δcka mo gMain la).fsRecv ctx P (tE.eval ρ)
          (rsvE.eval ρ) (hdrE.eval ρ) (eE.eval ρ) rec_).run h ∧
    ∀ res ∈ support (((hooksFSMulti cka prng fs Δcka mo gMain la).fsRecv ctx P (tE.eval ρ)
        (rsvE.eval ρ) (hdrE.eval ρ) (eE.eval ρ) rec_).run h),
      FSMultiHBoundedPost L res.2 := by
  unfold fsMultiFsRecvC hooksFSMulti
  dsimp only
  rw [eval_bind_ret]
  set rsv : RS ⊕ ℕ := rsvE.eval ρ
  set hdr : Header T := hdrE.eval ρ
  set e : E := eE.eval ρ
  have h0 : (Expr.pair hE (.pair rsvE (.pair hdrE (.pair eE recE)))).eval ρ =
      (hsMEnc h, rsv, hdr, e, rec_.map cRecEnc) := by
    simp [Expr.eval, hh, hrec, rsv, hdr, e]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := .prod mHsTy (.prod (.sum (.base CKASort.rs) .nat)
      (.prod hdrTy (.prod (.base CKASort.ct) (.opt cRecTy)))))
    (hsMEnc h, rsv, hdr, e, rec_.map cRecEnc) ρ
  rcases rsv with rs | sIdx
  · rw [eval_caseSum_inl rfl]
    dsimp only
    refine ⟨?_, ?_⟩
    · have hOp : (Expr.op (O := OO) (CKAOp.fsReceive B)
          (.pair .v0
            (.pair (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1))))))).eval
          (Env.cons (t := .base CKASort.rs) rs ρ₁) =
          fs.receive rs hdr e := by
        simp only [ρ₁, prngOps, ckaOps, Expr.eval, Expr.v0, Expr.v1,
          Env.get_cons_zero, Env.get_cons_succ]
        exact hFsRecvB rs hdr e
      rcases hrc : fs.receive rs hdr e with _ | ⟨rs', i, m⟩
      · rw [eval_caseOpt_none (hOp.trans hrc), eval_ret]
        simp [ρ₁, StateT.run_pure, Prod.map, Expr.eval, Expr.v1]
      · rw [eval_caseOpt_some (hOp.trans hrc), eval_ret]
        simp [ρ₁, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v2]
    · intro res' hmem
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact hHB
  · rw [eval_caseSum_inr rfl]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    set ρ₂ := Env.cons (t := .nat) sIdx ρ₁
    set bk := (h.book sIdx).getD {}
    have hBkL : bk.fsTrans.length ≤ L := by
      dsimp only [bk]
      rcases hbk : h.book sIdx with _ | b
      · simp
      · exact hHB sIdx b hbk
    have hBk2 : (fsMultiHsGetBookAt (O := OO) (.fst .v1) .v0).eval ρ₂ =
        (bk.sCorr, bk.fsCount, bk.fsTrans) :=
      fsMultiHsGetBookAt_eval (.fst .v1) .v0 ρ₂ h rfl
    set matched := bk.fsTrans.find? (fun x => x.2 == (hdr, e))
    have hFind1 : (fsTransFindE L (.snd (.snd (fsMultiHsGetBookAt (O := OO) (.fst .v1) .v0)))
        (.pair (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1)))))).eval ρ₂ =
        matched := by
      rw [fsTransFindE_eval heqT heqE L (.snd (.snd (fsMultiHsGetBookAt (.fst .v1) .v0)))
        (.pair (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1))))) ρ₂
        (by simp [snd_eval, hBk2, hBkL])]
      rw [snd_eval, snd_eval, hBk2]
      simp [ρ₂, ρ₁, matched, Expr.eval, Expr.v1]
    have hContEval : ∀ (m? : Option (ℕ × Header T × E))
        (_hM : matched = m?)
        (res : Option (FSAEAD.ReceiveResult M)),
        (Comp.caseOpt (O := OO) (I := IIM) .v0
          (.ret (.pair .none (.fst .v2)))
          (.caseSum .v0
            (.ret (.pair (.some .none) (.fst .v4)))
            (.ite
              (.and (.bool la)
                (.caseOpt
                  (fsTransFindE L (.snd (.snd (fsMultiHsGetBookAt (.fst .v4) .v3)))
                    (.pair (.fst (.snd (.snd .v4))) (.fst (.snd (.snd (.snd .v4))))))
                  (.lt (.fst (.snd (fsMultiHsGetBookAt (.fst .v4) .v3))) (.fst .v0))
                  (.bool false)))
              (.ret (.pair .none (fsMultiHsSetLfWin (.fst .v4) (.bool true))))
              (.ret (.pair
                (.caseOpt (.snd .v0)
                  (.caseOpt (.snd (.snd (.snd (.snd .v4))))
                    .none
                    (.some (.some (.pair (Expr.inr (O := OO) (t := .base CKASort.rs) .v4)
                      (.pair (.fst .v1) (cRecMsg .v0))))))
                  (.some (.some (.pair (Expr.inr (O := OO) (t := .base CKASort.rs) .v4)
                    (.pair (.fst .v1) .v0)))))
                (fsMultiHsSetBookAt (.fst .v4) .v3
                  (.pair (.fst (fsMultiHsGetBookAt (.fst .v4) .v3))
                    (.pair (.fst (.snd (fsMultiHsGetBookAt (.fst .v4) .v3)))
                      (fsTransFilterE L (.snd (.snd (fsMultiHsGetBookAt (.fst .v4) .v3)))
                        (.caseOpt
                          (fsTransFindE L (.snd (.snd (fsMultiHsGetBookAt (.fst .v4) .v3)))
                            (.pair (.fst (.snd (.snd .v4))) (.fst (.snd (.snd (.snd .v4))))))
                          (.fst .v0) (.fst .v0))))))))))).eval
          (Env.cons (t := .opt (fsHdrRrTy KC Γ CCoins T I KR RSt K SS RS M E))
            (Option.map fsHdrRrEnc res) ρ₂) =
        Prod.map id hsMEnc <$>
          ((match res with
            | none => pure none
            | some .rejected => pure (some none)
            | some (.accepted i mo') => do
              if (la && m?.isNone && decide (bk.fsCount < i)) = true then
                modify fun (s : FSMultiState T RSt K I E) => { s with lfWin := true }
                pure none
              else
                let drop := (m?.map (·.1)).getD i
                modify fun (s : FSMultiState T RSt K I E) =>
                  let b := (s.book sIdx).getD {}
                  let b' : FSMultiBook T E := { b with fsTrans := b.fsTrans.filter (·.1 != drop) }
                  { s with book := Function.update s.book sIdx (some b') }
                match mo', rec_ with
                | some m, _ => pure (some (some ((.inr sIdx : RS ⊕ ℕ), i, m)))
                | none, some r => pure (some (some ((.inr sIdx : RS ⊕ ℕ), i, r.msg)))
                | none, none => pure none :
            HM (FSMultiSpec SS RS T M E) (FSMultiState T RSt K I E)
              (Option (Option ((RS ⊕ ℕ) × ℕ × M)))).run h) := by
      intro m? hM res
      rcases res with _ | (_ | ⟨msgIdx, mo'⟩)
      · dsimp only [Option.map]
        rw [eval_caseOpt_none rfl, eval_ret]
        simp [ρ₂, ρ₁, StateT.run_pure, Prod.map, Expr.eval, Expr.v2]
      · dsimp only [Option.map, fsHdrRrEnc]
        rw [eval_caseOpt_some rfl, eval_caseSum_inl rfl, eval_ret]
        simp [ρ₂, ρ₁, StateT.run_pure, Prod.map, Expr.eval, Expr.v4]
      · dsimp only [Option.map, fsHdrRrEnc]
        rw [eval_caseOpt_some rfl, eval_caseSum_inr rfl, eval_ite]
        set ρ₃ := Env.cons (t := .prod .nat (.opt (.base CKASort.msg))) (msgIdx, mo')
          (Env.cons (t := fsHdrRrTy KC Γ CCoins T I KR RSt K SS RS M E) (.inr (msgIdx, mo'))
            (Env.cons (t := .opt (fsHdrRrTy KC Γ CCoins T I KR RSt K SS RS M E))
              (some (.inr (msgIdx, mo'))) ρ₂))
        have hBk3 : (fsMultiHsGetBookAt (O := OO) (.fst .v4) .v3).eval ρ₃ =
            (bk.sCorr, bk.fsCount, bk.fsTrans) :=
          fsMultiHsGetBookAt_eval (.fst .v4) .v3 ρ₃ h rfl
        have hFind3 : (fsTransFindE L (.snd (.snd (fsMultiHsGetBookAt (O := OO) (.fst .v4) .v3)))
            (.pair (.fst (.snd (.snd .v4))) (.fst (.snd (.snd (.snd .v4)))))).eval ρ₃ = m? := by
          rw [fsTransFindE_eval heqT heqE L (.snd (.snd (fsMultiHsGetBookAt (.fst .v4) .v3)))
            (.pair (.fst (.snd (.snd .v4))) (.fst (.snd (.snd (.snd .v4))))) ρ₃
            (by simp [snd_eval, hBk3, hBkL])]
          rw [snd_eval, snd_eval, hBk3]
          refine Eq.trans ?_ hM
          simp [ρ₃, ρ₂, ρ₁, matched, Expr.eval, Expr.v4]
        have hLfCond :
            (Expr.and (.bool la)
              (.caseOpt
                (fsTransFindE L (.snd (.snd (fsMultiHsGetBookAt (O := OO) (.fst .v4) .v3)))
                  (.pair (.fst (.snd (.snd .v4))) (.fst (.snd (.snd (.snd .v4))))))
                (.lt (.fst (.snd (fsMultiHsGetBookAt (.fst .v4) .v3))) (.fst .v0))
                (.bool false))).eval ρ₃ =
            (la && m?.isNone && decide (bk.fsCount < msgIdx)) := by
          rw [and_eval]
          simp only [Expr.eval, hFind3, hBk3]
          rcases m? with _ | mrec
          · simp only [Option.isNone_none, Bool.and_true]; rfl
          · simp
        rw [hLfCond]
        by_cases hLf : (la && m?.isNone && decide (bk.fsCount < msgIdx)) = true
        · simp only [hLf, ↓reduceIte, eval_ret, pair_eval, StateT.run_bind, StateT.run_modify,
            StateT.run_pure, pure_bind, map_pure, Prod.map]
          rw [fsMultiHsSetLfWin_eval (.fst .v4) (.bool true) ρ₃ h rfl]
          rfl
        · simp only [hLf, Bool.false_eq_true, ↓reduceIte, eval_ret, pair_eval,
            StateT.run_bind, StateT.run_modify, pure_bind]
          have hDrop : (Expr.caseOpt (O := OO)
              (fsTransFindE L (.snd (.snd (fsMultiHsGetBookAt (.fst .v4) .v3)))
                (.pair (.fst (.snd (.snd .v4))) (.fst (.snd (.snd (.snd .v4))))))
              (.fst .v0) (.fst .v0)).eval ρ₃ =
              (m?.map (·.1)).getD msgIdx := by
            simp only [Expr.eval, hFind3]
            rcases m? with _ | mrec <;> rfl
          have hFlt := fsTransFilterE_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
            (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
            (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
            (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
            (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
            L (.snd (.snd (fsMultiHsGetBookAt (.fst .v4) .v3)))
            (.caseOpt (fsTransFindE L (.snd (.snd (fsMultiHsGetBookAt (.fst .v4) .v3)))
                (.pair (.fst (.snd (.snd .v4))) (.fst (.snd (.snd (.snd .v4))))))
              (.fst .v0) (.fst .v0)) ρ₃ (by simp [snd_eval, hBk3, hBkL])
          rw [hDrop] at hFlt
          have hTrEq : (Expr.snd (.snd (fsMultiHsGetBookAt (O := OO) (.fst .v4) .v3))).eval ρ₃ =
              bk.fsTrans := by simp [snd_eval, hBk3]
          rw [hTrEq] at hFlt
          have hH4 := fsMultiHsSetBookAt_eval (.fst (Expr.v4 (O := OO))) .v3
            (.pair (.fst (fsMultiHsGetBookAt (.fst .v4) .v3))
              (.pair (.fst (.snd (fsMultiHsGetBookAt (.fst .v4) .v3)))
                (fsTransFilterE L (.snd (.snd (fsMultiHsGetBookAt (.fst .v4) .v3)))
                  (.caseOpt (fsTransFindE L (.snd (.snd (fsMultiHsGetBookAt (.fst .v4) .v3)))
                      (.pair (.fst (.snd (.snd .v4))) (.fst (.snd (.snd (.snd .v4))))))
                    (.fst .v0) (.fst .v0))))) ρ₃ h rfl
            (sc := bk.sCorr) (cnt := bk.fsCount)
            (tr := bk.fsTrans.filter (·.1 != (m?.map (·.1)).getD msgIdx))
            (by simp [pair_eval, fst_eval, snd_eval, hBk3, hFlt])
          have hIdx3 : (Expr.v3 (O := OO)).eval ρ₃ = sIdx := rfl
          rw [hIdx3] at hH4
          have hOut :
              (Expr.caseOpt (O := OO) (.snd .v0)
                (Expr.caseOpt (.snd (.snd (.snd (.snd .v4))))
                  .none
                  (.some (.some (.pair (Expr.inr (O := OO) (t := .base CKASort.rs) .v4) (.pair (.fst .v1) (cRecMsg .v0))))))
                (.some (.some (.pair (Expr.inr (O := OO) (t := .base CKASort.rs) .v4) (.pair (.fst .v1) .v0))))).eval ρ₃ =
              (match mo', rec_ with
                | some m, _ => some (some ((.inr sIdx : RS ⊕ ℕ), msgIdx, m))
                | none, some r => some (some ((.inr sIdx : RS ⊕ ℕ), msgIdx, r.msg))
                | none, none => none) := by
            rcases mo' with _ | m
            · rcases rec_ with _ | r <;>
                simp [ρ₃, ρ₂, ρ₁, cRecMsg, cRecEnc, Expr.eval, Expr.v0, Expr.v1, Expr.v4]
            · simp [ρ₃, ρ₂, Expr.eval, Expr.v0, Expr.v1, Expr.v4]
          rw [hOut, hH4]
          rcases mo' with _ | m
          · rcases rec_ with _ | r <;> rfl
          · rfl
    have hContHB : ∀ (m? : Option (ℕ × Header T × E))
        (res : Option (FSAEAD.ReceiveResult M)) (res' : _),
        res' ∈ support
          ((match res with
            | none => pure none
            | some .rejected => pure (some none)
            | some (.accepted i mo') => do
              if (la && m?.isNone && decide (bk.fsCount < i)) = true then
                modify fun (s : FSMultiState T RSt K I E) => { s with lfWin := true }
                pure none
              else
                let drop := (m?.map (·.1)).getD i
                modify fun (s : FSMultiState T RSt K I E) =>
                  let b := (s.book sIdx).getD {}
                  let b' : FSMultiBook T E := { b with fsTrans := b.fsTrans.filter (·.1 != drop) }
                  { s with book := Function.update s.book sIdx (some b') }
                match mo', rec_ with
                | some m, _ => pure (some (some ((.inr sIdx : RS ⊕ ℕ), i, m)))
                | none, some r => pure (some (some ((.inr sIdx : RS ⊕ ℕ), i, r.msg)))
                | none, none => pure none :
            HM (FSMultiSpec SS RS T M E) (FSMultiState T RSt K I E)
              (Option (Option ((RS ⊕ ℕ) × ℕ × M)))).run h) →
        FSMultiHBoundedPost L res'.2 := by
      intro m? res res' hmem
      rcases res with _ | (_ | ⟨msgIdx, mo'⟩)
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; exact hHB
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; exact hHB
      · by_cases hLf : (la && m?.isNone && decide (bk.fsCount < msgIdx)) = true
        · simp only [hLf, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
            pure_bind, support_pure, Set.mem_singleton_iff] at hmem
          subst hmem; exact hHB
        · simp only [hLf, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_modify,
            pure_bind] at hmem
          let bk' : FSMultiBook T E :=
            { bk with fsTrans := bk.fsTrans.filter (·.1 != (m?.map (·.1)).getD msgIdx) }
          let h' : FSMultiState T RSt K I E :=
            { h with book := Function.update h.book sIdx (some bk') }
          have hHB' : FSMultiHBoundedPost L h' := by
            intro idx b' hb'
            by_cases hidx : idx = sIdx
            · subst hidx
              simp only [h', bk', Function.update_self, Option.some.injEq] at hb'
              subst hb'
              exact (List.length_filter_le _ _).trans hBkL
            · simp only [h', Function.update_of_ne hidx] at hb'
              exact hHB idx b' hb'
          rcases mo' with _ | m
          · rcases rec_ with _ | r <;>
              (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem;
               subst hmem; exact hHB')
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
            subst hmem; exact hHB'
    rcases hM : matched with _ | mrec
    · refine ⟨?_, ?_⟩
      · rw [eval_bind, eval_caseOpt_none (hFind1.trans hM), query_fsMulti_ij_eval]
        simp only [ρ₂, ρ₁, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
          liftFSMulti_eq, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
          bind_map_left, map_bind, Expr.eval, Expr.v0, Expr.v1]
        exact bind_congr fun res => hContEval none hM res
      · intro res' hmem
        simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
          liftFSMulti_eq, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
          mem_support_bind_iff] at hmem
        obtain ⟨res, _, hmem⟩ := hmem
        exact hContHB none res res' hmem
    · refine ⟨?_, ?_⟩
      · rw [eval_bind, eval_caseOpt_some (hFind1.trans hM), query_fsMulti_dl_eval]
        simp only [ρ₂, ρ₁, Option.isSome_some, ↓reduceIte,
          liftFSMulti_eq, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
          bind_map_left, map_bind, Expr.eval, Expr.v1, Expr.v2]
        exact bind_congr fun res => hContEval (some mrec) hM res
      · intro res' hmem
        simp only [Option.isSome_some, ↓reduceIte,
          liftFSMulti_eq, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
          mem_support_bind_iff] at hmem
        obtain ⟨res, _, hmem⟩ := hmem
        exact hContHB (some mrec) res res' hmem

private theorem unliftMultiEntryE_eval {Γ'}
    (entryE : Expr OO Γ' (.opt (.sum (.base .rs) .nat))) (ρ : Env Γ') :
    (unliftMultiEntryE entryE).eval ρ =
      match entryE.eval ρ with
      | some (.inl rs) => some rs
      | _ => none := by
  unfold unliftMultiEntryE
  rcases h1 : entryE.eval ρ with _ | (rs | sIdx) <;>
    simp [h1, Expr.eval, Expr.v0]

private theorem unliftMultiVRE_eval (L : ℕ) {Γ'}
    (vRE : Expr OO Γ' (.tbl (.opt (.sum (.base .rs) .nat))))
    (rngE : Expr OO Γ' (.list .nat)) (ρ : Env Γ')
    (hRng : rngE.eval ρ = (List.range L).reverse) :
    (unliftMultiVRE L vRE rngE).eval ρ =
      fun t =>
        if t < L then
          match (vRE.eval ρ) t with
          | some (.inl rs) => some rs
          | _ => none
        else none := by
  unfold unliftMultiVRE
  rw [letE_eval]
  set vR := vRE.eval ρ
  have h0 : (Expr.pair vRE rngE).eval ρ = (vR, (List.range L).reverse) := by
    simp [Expr.eval, vR, hRng]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := .prod (.tbl (.opt (.sum (.base CKASort.rs) .nat))) (.list .nat))
    (vR, (List.range L).reverse) ρ
  have hTake : (((Expr.snd (O := OO) .v0).eval ρ₁).take L) = (List.range L).reverse := by
    change ((List.range L).reverse).take L = (List.range L).reverse
    simp
  change List.foldr _ (fun _ => none) (((Expr.snd (O := OO) .v0).eval ρ₁).take L) = _
  rw [hTake]
  have hStep :
      (fun (x : ℕ) (acc : ℕ → Option RS) =>
        (Expr.tset (O := OO) .v1 .v0
          (unliftMultiEntryE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
            (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
            (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
            (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
            (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
            (.tget (.fst .v2) .v0))).eval
          (Env.cons (t := .nat) x
            (Env.cons (t := .tbl (.opt (.base CKASort.rs))) acc ρ₁))) =
      (fun (x : ℕ) (acc : ℕ → Option RS) =>
        Function.update acc x
          (match vR x with | some (.inl rs) => some rs | _ => none)) := by
    funext x acc
    rw [tset_eval_eq_update, unliftMultiEntryE_eval]
    rfl
  rw [hStep]
  funext t
  rw [foldr_update_apply]
  simp [List.mem_reverse, List.mem_range]

private theorem fsMultiRevealC_eval [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    {Γ'} (hE : Expr OO Γ' mHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (pE : Expr OO Γ' .bool) (vpE : Expr OO Γ' mVpTy) (ρ : Env Γ')
    (h : FSMultiState T RSt K I E) (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E)
    (P : Party) (vp : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ))
    (hh : hE.eval ρ = hsMEnc h) (hvp : vpE.eval ρ = vpMEnc vp) :
    (fsMultiRevealC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L mo la hE ctxE pE vpE).eval ρ =
      Prod.map (Option.map ckaPsEnc) hsMEnc <$>
        ((hooksFSMultiL cka prng fs L Δcka mo gMain la).reveal ctx P vp).run h := by
  unfold fsMultiRevealC hooksFSMultiL
  dsimp only
  have h0 : (Expr.pair hE vpE).eval ρ = (hsMEnc h, vpMEnc vp) := by
    simp [Expr.eval, hh, hvp]
  set ρ₁ := Env.cons (t := .prod mHsTy mVpTy) (hsMEnc h, vpMEnc vp) ρ
  cases la
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [eval_bind_ret, h0]
    have hStep2 : ∀ (vS : Option SS) (h₁ : FSMultiState T RSt K I E),
        (Comp.caseOpt (O := OO) (I := IIM) (.fst .v0)
          (.ret (.pair .none (.snd .v0)))
          (.ite
            (.caseOpt (.tget (vpVR (.snd .v2)) (.nat mo.tStar))
              (.bool false)
              (.caseSum .v0 (.bool false) (.bool true)))
            (.ret (.pair .none (.snd .v1)))
            (.bind (rangeListC (O' := OO) (I' := IIM) L)
              (.ret (.pair
                (.some (realPartyE (.snd .v3) (vpΓ (.snd .v3)) (vpRoot (.snd .v3)) .v1
                  (unliftMultiVRE L (vpVR (.snd .v3)) .v0)))
                (.snd .v2)))))).eval
          (Env.cons (t := .prod (.opt (.opt (.base CKASort.ss))) mHsTy) (some vS, hsMEnc h₁) ρ₁) =
        Prod.map (Option.map ckaPsEnc) hsMEnc <$>
          ((let abortRecv := match vp.vR mo.tStar with
              | some (.inr _) => true
              | _ => false
            if abortRecv = true then pure none
            else
              let vR : ℕ → Option RS := fun t =>
                if t < L then
                  match vp.vR t with
                  | some (.inl rs) => some rs
                  | _ => none
                else none
              pure (some (realParty vp vp.γ vp.root vS vR)) :
            HM (FSMultiSpec SS RS T M E) (FSMultiState T RSt K I E) _).run h₁) := by
      intro vS h₁
      rw [eval_caseOpt_some rfl, eval_ite]
      set ρ₂ := Env.cons (t := .opt (.base CKASort.ss)) vS
        (Env.cons (t := .prod (.opt (.opt (.base CKASort.ss))) mHsTy) (some vS, hsMEnc h₁) ρ₁)
      have hvR2 : (vpVR (.snd (Expr.v2 (O := OO)))).eval ρ₂ = vp.vR := rfl
      have hFinOk :
          (Comp.bind (rangeListC (O' := OO) (I' := IIM) L)
            (.ret (.pair
              (.some (realPartyE (.snd .v3) (vpΓ (.snd .v3)) (vpRoot (.snd .v3)) .v1
                (unliftMultiVRE L (vpVR (.snd .v3)) .v0)))
              (.snd .v2)))).eval ρ₂ =
          pure (some (ckaPsEnc (realParty vp vp.γ vp.root vS
            (fun t => if t < L then
              match vp.vR t with | some (.inl rs) => some rs | _ => none
             else none))), hsMEnc h₁) := by
        rw [eval_bind, rangeListC_eval, pure_bind, eval_ret, pair_eval, some_eval]
        set ρ₃ := Env.cons (t := .list .nat) (List.range L).reverse ρ₂
        have hUnlift := unliftMultiVRE_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
          (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
          (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          L (vpVR (.snd .v3)) .v0 ρ₃ rfl
        have hReal := realPartyE_eval (O' := OO)
          (.snd .v3) (vpΓ (.snd .v3)) (vpRoot (.snd .v3)) .v1
          (unliftMultiVRE L (vpVR (.snd .v3)) .v0) ρ₃ vp rfl
        rw [hReal, hUnlift]
        refine congrArg (fun f => pure (some (ckaPsEnc (realParty vp vp.γ vp.root vS f)), hsMEnc h₁)) ?_
        funext t
        have hvR3 : (vpVR (.snd (Expr.v3 (O := OO)))).eval ρ₃ = vp.vR := rfl
        erw [hvR3]
        rcases vp.vR t with _ | (_ | _) <;> rfl
      rcases hvR' : vp.vR mo.tStar with _ | (rs0 | sIdx0)
      · have hAb : (Expr.caseOpt (O := OO) (.tget (vpVR (.snd .v2)) (.nat mo.tStar))
            (.bool false) (.caseSum .v0 (.bool false) (.bool true))).eval ρ₂ = false := by
          simp [Expr.eval, hvR2, hvR']
        rw [hAb]
        simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure, map_pure, Prod.map,
          Option.map_some]
        exact hFinOk
      · have hAb : (Expr.caseOpt (O := OO) (.tget (vpVR (.snd .v2)) (.nat mo.tStar))
            (.bool false) (.caseSum .v0 (.bool false) (.bool true))).eval ρ₂ = false := by
          simp [Expr.eval, Expr.v0, hvR2, hvR']
        rw [hAb]
        simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure, map_pure, Prod.map,
          Option.map_some]
        exact hFinOk
      · have hAb : (Expr.caseOpt (O := OO) (.tget (vpVR (.snd .v2)) (.nat mo.tStar))
            (.bool false) (.caseSum .v0 (.bool false) (.bool true))).eval ρ₂ = true := by
          simp [Expr.eval, Expr.v0, hvR2, hvR']
        rw [hAb, eval_ret]
        simp [ρ₂, StateT.run_pure, Prod.map, Expr.eval, Expr.v1]
    rw [eval_bind]
    have hvS : (vpVS (.snd (Expr.v0 (O := OO)))).eval ρ₁ = vp.vS := rfl
    rcases hvS' : vp.vS with _ | (ss | sIdx)
    · rw [eval_caseOpt_none (hvS.trans hvS'), eval_ret, pure_bind]
      simp only [pure_bind]
      exact hStep2 none h
    · rw [eval_caseOpt_some (hvS.trans hvS'), eval_caseSum_inl rfl, eval_ret, pure_bind]
      simp only [pure_bind]
      exact hStep2 (some ss) h
    · rw [eval_caseOpt_some (hvS.trans hvS'), eval_caseSum_inr rfl]
      simp only [eval_bind, query_fsMulti_cs_eval, liftFSMulti_eq, StateT.run_bind,
        StateT.run_lift, bind_assoc, pure_bind, map_bind, Expr.eval, Expr.v0]
      refine bind_congr fun cs? => ?_
      rcases cs? with _ | ss'
      · rw [eval_caseOpt_none rfl, eval_ret, pure_bind, eval_caseOpt_none rfl, eval_ret]
        simp [ρ₁, StateT.run_pure, Prod.map, Expr.eval, Expr.v3]
      · rw [eval_caseOpt_some rfl, eval_ret, pure_bind]
        simp only [StateT.run_bind, StateT.run_modify, pure_bind]
        set ρ_cs := Env.cons (t := .base CKASort.ss) ss'
          (Env.cons (t := .opt (.base CKASort.ss)) (some ss')
            (Env.cons (t := .nat) sIdx
              (Env.cons (t := .sum (.base CKASort.ss) .nat) (.inr sIdx) ρ₁)))
        have hBk := fsMultiHsGetBookAt_eval (.fst (Expr.v4 (O := OO))) .v2 ρ_cs h rfl
        have hIdx : (Expr.v2 (O := OO)).eval ρ_cs = sIdx := rfl
        rw [hIdx] at hBk
        have hSet := fsMultiHsSetBookAt_eval (.fst (Expr.v4 (O := OO))) .v2
          (.pair (.bool true) (.snd (fsMultiHsGetBookAt (.fst .v4) .v2))) ρ_cs h rfl
          (sc := true) (cnt := ((h.book sIdx).getD {}).fsCount)
          (tr := ((h.book sIdx).getD {}).fsTrans)
          (by simp only [Expr.eval, hBk])
        rw [hIdx] at hSet
        let bk0 : FSMultiBook T E := (h.book sIdx).getD {}
        let bk' : FSMultiBook T E := { bk0 with sCorr := true }
        let h' : FSMultiState T RSt K I E :=
          { h with book := Function.update h.book sIdx (some bk') }
        have hPair : (Expr.pair (O := OO) (.some (.some .v0))
            (fsMultiHsSetBookAt (.fst .v4) .v2
              (.pair (.bool true) (.snd (fsMultiHsGetBookAt (.fst .v4) .v2))))).eval ρ_cs =
            (some (some ss'), hsMEnc h') := by
          rw [pair_eval, hSet]; rfl
        erw [hPair]
        exact hStep2 (some ss') h'
  · simp only [↓reduceIte]
    rw [eval_bind_ret, h0]
    have hContLa : ∀ (vS : Option SS),
        (Comp.ite (O := OO) (I := IIM)
          (.caseOpt (.tget (vpVR (.snd .v1)) (.nat mo.tStar))
            (.bool false)
            (.caseSum .v0 (.bool false) (.bool true)))
          (.ret (.pair .none (.fst .v1)))
          (.bind (rangeListC (O' := OO) (I' := IIM) L)
            (.ret (.pair
              (.some (realPartyE (.snd .v2) (vpΓ (.snd .v2)) (vpRoot (.snd .v2)) .v1
                (unliftMultiVRE L (vpVR (.snd .v2)) .v0)))
              (.fst .v2))))).eval
          (Env.cons (t := .opt (.base CKASort.ss)) vS ρ₁) =
        Prod.map (Option.map ckaPsEnc) hsMEnc <$>
          ((let abortRecv := match vp.vR mo.tStar with
              | some (.inr _) => true
              | _ => false
            if abortRecv = true then pure none
            else
              let vR : ℕ → Option RS := fun t =>
                if t < L then
                  match vp.vR t with
                  | some (.inl rs) => some rs
                  | _ => none
                else none
              pure (some (realParty vp vp.γ vp.root vS vR)) :
            HM (FSMultiSpec SS RS T M E) (FSMultiState T RSt K I E) _).run h) := by
      intro vS
      rw [eval_ite]
      set ρ₂ := Env.cons (t := .opt (.base CKASort.ss)) vS ρ₁
      have hvR1 : (vpVR (.snd (Expr.v1 (O := OO)))).eval ρ₂ = vp.vR := rfl
      have hFinOk :
          (Comp.bind (rangeListC (O' := OO) (I' := IIM) L)
            (.ret (.pair
              (.some (realPartyE (.snd .v2) (vpΓ (.snd .v2)) (vpRoot (.snd .v2)) .v1
                (unliftMultiVRE L (vpVR (.snd .v2)) .v0)))
              (.fst .v2)))).eval ρ₂ =
          pure (some (ckaPsEnc (realParty vp vp.γ vp.root vS
            (fun t => if t < L then
              match vp.vR t with | some (.inl rs) => some rs | _ => none
             else none))), hsMEnc h) := by
        rw [eval_bind, rangeListC_eval, pure_bind, eval_ret, pair_eval, some_eval]
        set ρ₃ := Env.cons (t := .list .nat) (List.range L).reverse ρ₂
        have hUnlift := unliftMultiVRE_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
          (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
          (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          L (vpVR (.snd .v2)) .v0 ρ₃ rfl
        have hReal := realPartyE_eval (O' := OO)
          (.snd .v2) (vpΓ (.snd .v2)) (vpRoot (.snd .v2)) .v1
          (unliftMultiVRE L (vpVR (.snd .v2)) .v0) ρ₃ vp rfl
        rw [hReal, hUnlift]
        refine congrArg (fun f => pure (some (ckaPsEnc (realParty vp vp.γ vp.root vS f)), hsMEnc h)) ?_
        funext t
        have hvR2' : (vpVR (.snd (Expr.v2 (O := OO)))).eval ρ₃ = vp.vR := rfl
        erw [hvR2']
        rcases vp.vR t with _ | (_ | _) <;> rfl
      rcases hvR' : vp.vR mo.tStar with _ | (rs0 | sIdx0)
      · have hAb : (Expr.caseOpt (O := OO) (.tget (vpVR (.snd .v1)) (.nat mo.tStar))
            (.bool false) (.caseSum .v0 (.bool false) (.bool true))).eval ρ₂ = false := by
          simp [Expr.eval, hvR1, hvR']
        rw [hAb]
        simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure, map_pure, Prod.map,
          Option.map_some]
        exact hFinOk
      · have hAb : (Expr.caseOpt (O := OO) (.tget (vpVR (.snd .v1)) (.nat mo.tStar))
            (.bool false) (.caseSum .v0 (.bool false) (.bool true))).eval ρ₂ = false := by
          simp [Expr.eval, Expr.v0, hvR1, hvR']
        rw [hAb]
        simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure, map_pure, Prod.map,
          Option.map_some]
        exact hFinOk
      · have hAb : (Expr.caseOpt (O := OO) (.tget (vpVR (.snd .v1)) (.nat mo.tStar))
            (.bool false) (.caseSum .v0 (.bool false) (.bool true))).eval ρ₂ = true := by
          simp [Expr.eval, Expr.v0, hvR1, hvR']
        rw [hAb, eval_ret]
        simp [ρ₂, ρ₁, StateT.run_pure, Prod.map, Expr.eval, Expr.v1]
    have hvS : (vpVS (.snd (Expr.v0 (O := OO)))).eval ρ₁ = vp.vS := rfl
    rcases hvS' : vp.vS with _ | (ss | sIdx)
    · have hOpt : (Expr.caseOpt (O := OO) (vpVS (.snd .v0)) (.some .none)
          (.caseSum .v0 (.some (.some .v0)) .none)).eval ρ₁ = some none := by
        (conv_lhs => unfold Expr.eval); rw [hvS, hvS']; rfl
      rw [eval_caseOpt_some hOpt]
      simp only [pure_bind]
      exact hContLa none
    · have hOpt : (Expr.caseOpt (O := OO) (vpVS (.snd .v0)) (.some .none)
          (.caseSum .v0 (.some (.some .v0)) .none)).eval ρ₁ = some (some ss) := by
        (conv_lhs => unfold Expr.eval); rw [hvS, hvS']; rfl
      rw [eval_caseOpt_some hOpt]
      simp only [pure_bind]
      exact hContLa (some ss)
    · have hOpt : (Expr.caseOpt (O := OO) (vpVS (.snd .v0)) (.some .none)
          (.caseSum .v0 (.some (.some .v0)) .none)).eval ρ₁ = none := by
        (conv_lhs => unfold Expr.eval); rw [hvS, hvS']; rfl
      rw [eval_caseOpt_none hOpt, eval_ret]
      simp [ρ₁, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]

end HooksFSMultiEval

theorem hooksFSMultiC_agrees
    {ckaInitA : KC → Γ} {ckaInitB : KC → Γ}
    {ckaSend : Γ → CCoins → Γ × T × I} {ckaReceive : Γ → T → Γ × I}
    {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
    {fsInitSender : K → SS} {fsInitReceiver : K → RS}
    {fsSend : SS → Header T → M → SS × E}
    {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
    {eqT : T → T → Bool} {eqI : I → I → Bool}
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    {eqM : M → M → Bool} {eqE : E → E → Bool}
    {lam : I} {defaultE : E}
    {sampKR : ProbComp KR} {sampKC : ProbComp KC} {sampCCoins : ProbComp CCoins}
    {sampI : ProbComp I} {sampK : ProbComp K}
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    (hSend : ckaSend = cka.send)
    (hRecv : ckaReceive = cka.receive)
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send)
    (heqT : eqT = (· == ·))
    (heqI : eqI = (· == ·))
    (heqE : eqE = (· == ·))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hSampI : sampI = ($ᵗ I : ProbComp I))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (hFsRecvB : ∀ rs hdr e,
      (fsReceive rs hdr e).map (fun (rs', i, m) => (rs', min i B, m)) =
        fs.receive rs hdr e) :
    HooksCAgrees (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (fsMultiHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (SS := SS) (RS := RS) (M := M))
      (FSMultiHBounded L) (HBoundedPost := FSMultiHBoundedPost L) (VROk := fun _ => True)
      (hooksFSMultiC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δcka mo gMain la)
      (hooksFSMultiL cka prng fs L Δcka mo gMain la) where
  hBounded_post _ h := h.2.2
  startSend_eval hE ctxE pE tE γE σE rE ρ h ctx P hHB hh _ _ :=
    (fsMultiStartSendC_eval cka prng fs hSend hPrngUp hFsInitS heqI
      hSampCCoins hSampI hSampK L Δcka mo gMain la hE ctxE pE tE γE σE rE ρ h ctx P hHB hh).1
  startSend_bounded ctx P t γ σ r h hHB res hmem := by
    let S₀ := ckaSig KC Γ CCoins T I KR RSt K SS RS M E
    let vpE := fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
      (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
    let hsE := fsMultiHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
      (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
    let ρ₀ :=
      Env.cons (t := (Ty.nat : Ty S₀)) t
        (Env.cons (t := (.base CKASort.γ : Ty S₀)) γ
          (Env.cons (t := (.base CKASort.sig : Ty S₀)) σ
            (Env.cons (t := (.opt (.base CKASort.ccoins) : Ty S₀)) r
              (Env.cons (t := fsMultiHsTy KC Γ CCoins T I KR RSt K SS RS M E) (hsE h)
                (Env.cons (t := (Ty.bool : Ty S₀)) (partyEnc P)
                  (Env.cons (t := cGsTy (fsMultiVpTy KC Γ CCoins T I KR RSt K SS RS M E))
                    (cGsEnc vpE ctx) (Env.nil : Env ([] : List (Ty S₀)))))))))
    dsimp only [hooksFSMultiL] at hmem
    have hB := (fsMultiStartSendC_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      cka prng fs hSend hPrngUp hFsInitS heqI hSampCCoins hSampI hSampK
      L Δcka mo gMain la .v4 .v6 .v5 .v0 .v1 .v2 .v3 ρ₀ h ctx P hHB rfl).2 res hmem
    unfold FSMultiHBoundedPost; rw [hB.2.2]; exact hHB.2.2
  startRecv_eval hE ctxE pE tE γE σE tnE ρ h ctx P hHB hh _ _ :=
    (fsMultiStartRecvC_eval cka prng fs hRecv hPrngUp hFsInitR heqT heqI
      hSampK L Δcka mo gMain la hE ctxE pE tE γE σE tnE ρ h ctx P hHB hh).1
  startRecv_bounded ctx P t γ σ Tn h hHB res hmem := by
    let S₀ := ckaSig KC Γ CCoins T I KR RSt K SS RS M E
    let vpE := fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
      (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
    let hsE := fsMultiHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
      (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
    let ρ₀ :=
      Env.cons (t := (Ty.nat : Ty S₀)) t
        (Env.cons (t := (.base CKASort.γ : Ty S₀)) γ
          (Env.cons (t := (.base CKASort.sig : Ty S₀)) σ
            (Env.cons (t := (.base CKASort.t : Ty S₀)) Tn
              (Env.cons (t := fsMultiHsTy KC Γ CCoins T I KR RSt K SS RS M E) (hsE h)
                (Env.cons (t := (Ty.bool : Ty S₀)) (partyEnc P)
                  (Env.cons (t := cGsTy (fsMultiVpTy KC Γ CCoins T I KR RSt K SS RS M E))
                    (cGsEnc vpE ctx) (Env.nil : Env ([] : List (Ty S₀)))))))))
    dsimp only [hooksFSMultiL] at hmem
    have hB := (fsMultiStartRecvC_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (prngInit := prngInit) (fsInitSender := fsInitSender)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI)
      cka prng fs hRecv hPrngUp hFsInitR heqT heqI hSampK
      L Δcka mo gMain la .v4 .v6 .v5 .v0 .v1 .v2 .v3 ρ₀ h ctx P hHB rfl).2 res hmem
    unfold FSMultiHBoundedPost; rw [hB.2.2]; exact hHB.2.2
  startRecv_vrOk _ _ _ _ _ _ _ _ _ _ _ _ _ _ := trivial
  fsSend_eval hE ctxE pE tE ssE hdrE mE pairE ρ h ctx P _ hh hctx hp :=
    fsMultiFsSendC_eval cka prng fs hFsSend Δcka mo gMain la hE ctxE pE tE ssE hdrE mE pairE ρ
      h ctx P hh hctx hp
  fsRecv_eval hE ctxE pE tE rsE hdrE eE recE ρ h ctx P rec_ hHB _ hh _ _ hrec :=
    (fsMultiFsRecvC_eval cka prng fs heqT heqE L B Δcka mo gMain la hFsRecvB
      hE ctxE pE tE rsE hdrE eE recE ρ h ctx P rec_ hHB hh hrec).1
  fsRecv_bounded ctx P t rsv hdr e rec_ h hHB res hmem := by
    let S₀ := ckaSig KC Γ CCoins T I KR RSt K SS RS M E
    let vpE := fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
      (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
    let hsE := fsMultiHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
      (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
    let ρ₀ :=
      Env.cons (t := (Ty.nat : Ty S₀)) t
        (Env.cons (t := (.sum (.base CKASort.rs) .nat : Ty S₀)) rsv
          (Env.cons (t := ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E) hdr
            (Env.cons (t := (.base CKASort.ct : Ty S₀)) e
              (Env.cons (t := (.opt cRecTy : Ty S₀)) (rec_.map cRecEnc)
                (Env.cons (t := fsMultiHsTy KC Γ CCoins T I KR RSt K SS RS M E) (hsE h)
                  (Env.cons (t := (Ty.bool : Ty S₀)) (partyEnc P)
                    (Env.cons (t := cGsTy (fsMultiVpTy KC Γ CCoins T I KR RSt K SS RS M E))
                      (cGsEnc vpE ctx) (Env.nil : Env ([] : List (Ty S₀))))))))))
    dsimp only [hooksFSMultiL] at hmem
    exact (fsMultiFsRecvC_eval (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (eqI := eqI) (eqM := eqM)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      cka prng fs heqT heqE L B Δcka mo gMain la hFsRecvB
      .v5 .v7 .v6 .v0 .v1 .v2 .v3 .v4 ρ₀ h ctx P rec_ hHB rfl rfl).2 res hmem
  commit_eval hE _ _ _ newE ρ h _ _ _ new _ hh _ _ _ hnew := by
    simp [hooksFSMultiC, fsMultiCommitC, hooksFSMultiL, hooksFSMulti, hh, hnew,
      StateT.run_pure, Prod.map, Expr.eval]
  reveal_eval hE ctxE pE vpE ρ h ctx P vp _ hh _ _ hvp :=
    fsMultiRevealC_eval cka prng fs L Δcka mo gMain la hE ctxE pE vpE ρ h ctx P vp hh hvp


private theorem hooksFSMultiL_reveal_eq [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (vp : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ))
    (hvR : ∀ t, L ≤ t → vp.vR t = none) :
    (hooksFSMultiL cka prng fs L Δcka mo gMain la).reveal ctx P vp =
      (hooksFSMulti cka prng fs Δcka mo gMain la).reveal ctx P vp := by
  have hvR_eq :
      (fun (t : ℕ) =>
        if t < L then
          match vp.vR t with
          | some (.inl rs) => some rs
          | _ => none
        else none) =
      (fun (t : ℕ) =>
        match vp.vR t with
        | some (.inl rs) => some rs
        | _ => none) := by
    funext t
    by_cases ht : t < L
    · simp [ht]
    · simp [ht, hvR t (Nat.le_of_not_lt ht)]
  have hTail : ∀ (vS? : Option (Option SS)) (s₁ : FSMultiState T RSt K I E),
      ((match vS? with
        | none => pure none
        | some vS =>
          if (match vp.vR mo.tStar with | some (.inr _) => true | _ => false) = true then
            pure none
          else
            pure (some (realParty vp vp.γ vp.root vS fun t =>
              if t < L then match vp.vR t with | some (.inl rs) => some rs | _ => none
              else none)) :
        HM (FSMultiSpec SS RS T M E) (FSMultiState T RSt K I E)
          (Option (PartyState Γ T RSt SS RS))).run s₁) =
      ((match vS? with
        | none => pure none
        | some vS =>
          if (match vp.vR mo.tStar with | some (.inr _) => true | _ => false) = true then
            pure none
          else
            pure (some (realParty vp vp.γ vp.root vS fun t =>
              match vp.vR t with | some (.inl rs) => some rs | _ => none)) :
        HM (FSMultiSpec SS RS T M E) (FSMultiState T RSt K I E)
          (Option (PartyState Γ T RSt SS RS))).run s₁) := by
    intro vS? s₁
    rcases vS? with _ | vS
    · rfl
    · dsimp only
      split_ifs
      · rfl
      · simp only [StateT.run_pure]
        congr 4
  refine StateT.ext fun s => ?_
  unfold hooksFSMultiL hooksFSMulti
  dsimp only
  rcases vp.vS with _ | (ss | sIdx)
  · simp only [pure_bind]
    exact hTail (some none) s
  · simp only [pure_bind]
    exact hTail (some (some ss)) s
  · by_cases hla : la = true
    · simp only [hla, ↓reduceIte]; rfl
    · simp only [hla, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
      refine bind_congr fun ⟨ans, s₁⟩ => ?_
      rcases ans with _ | ss
      · rfl
      · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
        exact hTail (some (some ss)) _

private theorem implE_hooksFSMultiL_eq [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [Inhabited E] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L Δ qep maxSkip : ℕ) (cfg : Config M) (π : Policy)
    (Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E)
      (FSMultiState T RSt K I E))
    (q : (SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hvR : ∀ P t, L ≤ t → (es.g.st P).vR t = none) :
    (implE (hooksFSMultiL cka prng fs L Δcka mo gMain la) Δ qep maxSkip cfg π (.inr q)).run es =
      (implE (hooksFSMulti cka prng fs Δcka mo gMain la) Δ qep maxSkip cfg π (.inr q)).run es := by
  rcases q with (((arg | arg) | arg) | arg) | P
  · rfl
  · rfl
  · rfl
  · rfl
  · change (corrE (hooksFSMultiL cka prng fs L Δcka mo gMain la) π P).run es =
      (corrE (hooksFSMulti cka prng fs Δcka mo gMain la) π P).run es
    unfold corrE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases href : (es.abort || es.g.win || !es.g.corrAllowed P)
    · simp [href]
    · simp only [href, Bool.false_eq_true, ↓reduceIte]
      by_cases hdoom : (π.leakDoom es.g (es.g.afterCorr P) || π.corrDoom es.g P)
      · simp [hdoom]
      · simp only [hdoom, Bool.false_eq_true, ↓reduceIte, run_liftH_bind,
          hooksFSMultiL_reveal_eq cka prng fs L Δcka mo gMain la es.g P (es.g.st P) (hvR P)]

private def bookTrLen {T E : Type} (book : ℕ → Option (FSMultiBook T E)) (sIdx : ℕ) : ℕ :=
  match book sIdx with
  | some bk => bk.fsTrans.length
  | none => 0

private theorem bookTrLen_getD_eq {T E : Type} (book : ℕ → Option (FSMultiBook T E)) (sIdx : ℕ) :
    ((book sIdx).getD {}).fsTrans.length = bookTrLen book sIdx := by
  unfold bookTrLen
  cases book sIdx <;> rfl

private theorem FSMultiEngineInv.bookTrLen_le {L B q : ℕ}
    {es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E)
      (FSMultiState T RSt K I E)}
    (h : FSMultiEngineInv L B q es) (sIdx : ℕ) :
    bookTrLen es.h.book sIdx + q ≤ B := by
  unfold bookTrLen
  rcases hbk : es.h.book sIdx with _ | bk
  · dsimp only; have := h.sm.trans_le; omega
  · dsimp only; exact h.fsTrans_le sIdx bk hbk

private theorem fsTrans_le_of_step1 {B q : ℕ}
    {book book' : ℕ → Option (FSMultiBook T E)}
    (hOld : ∀ j, bookTrLen book j + (q + 1) ≤ B)
    (hStep : ∀ j, bookTrLen book' j ≤ bookTrLen book j + 1) :
    ∀ sIdx bk, book' sIdx = some bk → bk.fsTrans.length + q ≤ B := by
  intro sIdx bk hbk
  have h1 := hOld sIdx
  have h2 := hStep sIdx
  have hbk' : bookTrLen book' sIdx = bk.fsTrans.length := by simp [bookTrLen, hbk]
  rw [hbk'] at h2
  omega

private theorem lookupMultiF_preserve_sb [DecidableEq I] [SampleableType K]
    (Ik : I) (h : FSMultiState T RSt K I E) :
    ∀ res ∈ support ((lookupMultiF (T := T) (Sig := RSt) (SS := SS) (RS := RS)
        (M := M) (E := E) Ik).run h),
      res.2.table.length ≤ h.table.length + 1 ∧
      res.2.sessions = h.sessions ∧
      res.2.book = h.book := by
  intro res hmem
  unfold lookupMultiF at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  rcases hlk : h.table.lookup Ik with _ | k
  · simp only [hlk, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
      StateT.run_modify, StateT.run_pure, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hmem
    obtain ⟨k', _, rfl⟩ := hmem
    exact ⟨le_rfl, rfl, rfl⟩
  · simp only [hlk, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    exact ⟨Nat.le_add_right _ _, rfl, rfl⟩

private theorem regSessMulti_preserve_sb [DecidableEq I]
    (Ik : I) (h : FSMultiState T RSt K I E) :
    ∀ res ∈ support ((regSessMulti (T := T) (Sig := RSt) (K := K) (SS := SS) (RS := RS)
        (M := M) (E := E) Ik).run h),
      res.2.table = h.table ∧
      res.2.sessions.length ≤ h.sessions.length + 1 ∧
      res.2.book = h.book := by
  intro res hmem
  unfold regSessMulti at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  split_ifs at hmem
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    exact ⟨rfl, Nat.le_add_right _ _, rfl⟩
  · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    exact ⟨rfl, by simp, rfl⟩

private theorem regSessOptMulti_preserve_sb [DecidableEq I]
    (sid : Option I) (h : FSMultiState T RSt K I E) :
    ∀ res ∈ support ((regSessOptMulti (T := T) (Sig := RSt) (K := K) (SS := SS) (RS := RS)
        (M := M) (E := E) sid).run h),
      res.2.table = h.table ∧
      res.2.sessions.length ≤ h.sessions.length + 1 ∧
      res.2.book = h.book := by
  intro res hmem
  rcases sid with _ | Ik
  · simp only [regSessOptMulti, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    exact ⟨rfl, Nat.le_add_right _ _, rfl⟩
  · simp only [regSessOptMulti, StateT.run_map, support_map, Set.mem_image] at hmem
    obtain ⟨⟨idx, h'⟩, hmem', rfl⟩ := hmem
    exact regSessMulti_preserve_sb Ik h (idx, h') hmem'

private theorem rootFSMulti_preserve_sb [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR RSt I K) (mo : Mode) (t : ℕ) (Ik : I) (σ : RSt)
    (h : FSMultiState T RSt K I E) :
    ∀ res ∈ support ((rootFSMulti (T := T) (SS := SS) (RS := RS) (M := M) (E := E)
        prng mo t Ik σ).run h),
      res.2.table.length ≤ h.table.length + 1 ∧
      res.2.sessions = h.sessions ∧
      res.2.book = h.book := by
  intro res hmem
  unfold rootFSMulti at hmem
  split_ifs at hmem
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; exact ⟨Nat.le_add_right _ _, rfl, rfl⟩
  · simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, StateT.run_pure,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hmem
    obtain ⟨Ir, _, k, _, rfl⟩ := hmem
    exact ⟨Nat.le_add_right _ _, rfl, rfl⟩
  · simp only [StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨k, h₁⟩, hlk, hmem⟩ := hmem
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    exact lookupMultiF_preserve_sb Ik h (k, h₁) hlk
  · simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, StateT.run_pure,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hmem
    obtain ⟨Ir, _, rfl⟩ := hmem
    exact ⟨Nat.le_add_right _ _, rfl, rfl⟩
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; exact ⟨Nat.le_add_right _ _, rfl, rfl⟩

private theorem fsMultiStartSend_preserve [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (t : ℕ) (γ : Γ) (σ : RSt) (r : Option CCoins)
    (h : FSMultiState T RSt K I E) :
    ∀ res ∈ support (((hooksFSMulti cka prng fs Δcka mo gMain la).startSend ctx P t γ σ r).run h),
      res.2.table.length ≤ h.table.length + 1 ∧
      res.2.sessions.length ≤ h.sessions.length + 1 ∧
      res.2.book = h.book := by
  intro res hmem
  dsimp only [hooksFSMulti] at hmem
  have hAfterCoins : ∀ coins : CCoins,
      res ∈ support (((do
        let (σ', k, sid) ← rootFSMulti prng mo t (cka.send γ coins).2.2 σ
        let optIdx ← regSessOptMulti sid
        modify fun s : FSMultiState T RSt K I E =>
          { s with cache := Function.update s.cache t (some ((cka.send γ coins).2.1, σ', k, optIdx)) }
        let ssv : SS ⊕ ℕ := match optIdx with
          | none => .inl (fs.initSender k)
          | some sIdx => .inr sIdx
        return some ((cka.send γ coins).1, (cka.send γ coins).2.1, σ', ssv) :
        HM (FSMultiSpec SS RS T M E) (FSMultiState T RSt K I E)
          (Option (Γ × T × RSt × (SS ⊕ ℕ)))).run h)) →
      res.2.table.length ≤ h.table.length + 1 ∧
      res.2.sessions.length ≤ h.sessions.length + 1 ∧
      res.2.book = h.book := by
    intro coins hmemC
    rw [StateT.run_bind, mem_support_bind_iff] at hmemC
    obtain ⟨⟨⟨σ', k, sid⟩, h₁⟩, hRoot, hmemC⟩ := hmemC
    rw [StateT.run_bind, mem_support_bind_iff] at hmemC
    obtain ⟨⟨optIdx, h₂⟩, hReg, hmemC⟩ := hmemC
    simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, support_pure,
      Set.mem_singleton_iff] at hmemC
    subst hmemC
    have hP1 := rootFSMulti_preserve_sb prng mo t (cka.send γ coins).2.2 σ h ((σ', k, sid), h₁) hRoot
    have hP2 := regSessOptMulti_preserve_sb sid h₁ (optIdx, h₂) hReg
    exact ⟨by dsimp only; rw [hP2.1]; exact hP1.1,
      by dsimp only; rw [← hP1.2.1]; exact hP2.2.1,
      by dsimp only; rw [hP2.2.2, hP1.2.2]⟩
  rcases r with _ | c
  · dsimp only at hmem
    rw [StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨coins, h₀⟩, hCoins, hmem⟩ := hmem
    simp only [StateT.run_lift, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at hCoins
    obtain ⟨_, _, _, rfl⟩ := hCoins
    exact hAfterCoins coins hmem
  · dsimp only at hmem
    rw [StateT.run_bind, StateT.run_pure, pure_bind] at hmem
    exact hAfterCoins c hmem

private theorem fsMultiStartRecv_preserve [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (t : ℕ) (γ : Γ) (σ : RSt) (Tn : T)
    (h : FSMultiState T RSt K I E) :
    ∀ res ∈ support (((hooksFSMulti cka prng fs Δcka mo gMain la).startRecv ctx P t γ σ Tn).run h),
      res.2.table.length ≤ h.table.length + 1 ∧
      res.2.sessions.length ≤ h.sessions.length + 1 ∧
      res.2.book = h.book := by
  intro res hmem
  dsimp only [hooksFSMulti] at hmem
  rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  dsimp only at hmem
  have hNoneCase :
      res ∈ support (((if gMain then pure (some none)
        else if mo.auth && decide (t = mo.tStar) then
          if mo.tL.isSome && decide (mo.tStar = mo.tH) then pure none
          else do
            let kk := cka.receive γ Tn
            let _ ← lookupMultiF kk.2
            let sIdx ← regSessMulti kk.2
            pure (some (some (kk.1, (prng.up σ kk.2).1, (.inr sIdx : RS ⊕ ℕ))))
        else pure (some none) :
        HM (FSMultiSpec SS RS T M E) (FSMultiState T RSt K I E)
          (Option (Option (Γ × RSt × (RS ⊕ ℕ))))).run h)) →
      res.2.table.length ≤ h.table.length + 1 ∧
      res.2.sessions.length ≤ h.sessions.length + 1 ∧
      res.2.book = h.book := by
    intro hmemN
    split_ifs at hmemN
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmemN
      subst hmemN; exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, rfl⟩
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmemN
      subst hmemN; exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, rfl⟩
    · rw [StateT.run_bind, mem_support_bind_iff] at hmemN
      obtain ⟨⟨k', h₁⟩, hlk, hmemN⟩ := hmemN
      rw [StateT.run_bind, mem_support_bind_iff] at hmemN
      obtain ⟨⟨sIdx, h₂⟩, hreg, hmemN⟩ := hmemN
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmemN
      subst hmemN
      have hP1 := lookupMultiF_preserve_sb (cka.receive γ Tn).2 h (k', h₁) hlk
      have hP2 := regSessMulti_preserve_sb (cka.receive γ Tn).2 h₁ (sIdx, h₂) hreg
      exact ⟨by dsimp only; rw [hP2.1]; exact hP1.1,
        by dsimp only; rw [← hP1.2.1]; exact hP2.2.1,
        by dsimp only; rw [hP2.2.2, hP1.2.2]⟩
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmemN
      subst hmemN; exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, rfl⟩
  rcases hca : h.cache t with _ | ⟨Tc, σc, k, optIdx⟩
  · rw [hca] at hmem
    exact hNoneCase hmem
  · rw [hca] at hmem
    dsimp only at hmem
    by_cases hEq : Tc = Tn
    · simp only [hEq, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, rfl⟩
    · simp only [hEq, ↓reduceIte] at hmem
      exact hNoneCase hmem

private theorem fsMultiFsSend_preserve [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    (h : FSMultiState T RSt K I E) (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E)
    (P : Party) (t : ℕ) (ssv : SS ⊕ ℕ) (hdr : Header T) (m : M) (pair : Option (M × M)) :
    ∀ res ∈ support (((hooksFSMulti cka prng fs Δcka mo gMain la).fsSend ctx P t ssv hdr m pair).run h),
      res.2.table = h.table ∧
      res.2.sessions = h.sessions ∧
      ∀ j, bookTrLen res.2.book j ≤ bookTrLen h.book j + 1 := by
  intro res hmem
  dsimp only [hooksFSMulti] at hmem
  rcases ssv with ss | sIdx
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    exact ⟨rfl, rfl, fun _ => Nat.le_add_right _ _⟩
  · rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    dsimp only at hmem
    have hRest : ∀ (ok : Bool) (h₁ : FSMultiState T RSt K I E),
        h₁.table = h.table →
        h₁.sessions = h.sessions →
        (∀ j, bookTrLen h₁.book j = bookTrLen h.book j) →
        res ∈ support (((do
          let ok' ← pure ok
          if !ok' then return none
          let e? ← match pair with
            | some (m₀, m₁) =>
              liftFSMulti sIdx (FSAEAD.challengeQuery (SenderState := SS) (ReceiverState := RS)
                hdr m₀ m₁)
            | none =>
              liftFSMulti sIdx (FSAEAD.transmitQuery (SenderState := SS) (ReceiverState := RS)
                hdr m)
          match e? with
          | none => return none
          | some e =>
            modify fun s : FSMultiState T RSt K I E =>
              let b := (s.book sIdx).getD {}
              let cnt' := b.fsCount + 1
              let b' : FSMultiBook T E :=
                { b with fsCount := cnt', fsTrans := (cnt', hdr, e) :: b.fsTrans }
              { s with book := Function.update s.book sIdx (some b') }
            return some ((.inr sIdx : SS ⊕ ℕ), e) :
          HM (FSMultiSpec SS RS T M E) (FSMultiState T RSt K I E)
            (Option ((SS ⊕ ℕ) × E))).run h₁)) →
        res.2.table = h.table ∧
        res.2.sessions = h.sessions ∧
        ∀ j, bookTrLen res.2.book j ≤ bookTrLen h.book j + 1 := by
      intro ok h₁ htb hse hbk hmem2
      rw [StateT.run_bind, StateT.run_pure, pure_bind] at hmem2
      dsimp only at hmem2
      cases ok
      · simp only [Bool.not_false, ↓reduceIte, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at hmem2
        subst hmem2
        exact ⟨htb, hse, fun j => by rw [hbk j]; exact Nat.le_add_right _ _⟩
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hmem2
        rcases pair with _ | ⟨m₀, m₁⟩ <;>
        · simp only [liftFSMulti, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
            mem_support_bind_iff] at hmem2
          obtain ⟨e?, _, hmem2⟩ := hmem2
          rcases e? with _ | e
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem2
            subst hmem2
            exact ⟨htb, hse, fun j => by rw [hbk j]; exact Nat.le_add_right _ _⟩
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff] at hmem2
            subst hmem2
            refine ⟨htb, hse, fun j => ?_⟩
            rw [← hbk j]
            dsimp only [bookTrLen]
            by_cases hj : j = sIdx
            · subst hj
              simp only [Function.update_self, List.length_cons]
              rw [bookTrLen_getD_eq]; unfold bookTrLen; omega
            · simp only [Function.update_of_ne hj]
              exact Nat.le_add_right _ _
    by_cases hc : (!ctx.safeCh (2 + Δcka) P && !((h.book sIdx).getD {}).sCorr) = true
    · simp only [hc, ↓reduceIte] at hmem
      by_cases hla : la = true
      · simp only [hla, ↓reduceIte] at hmem
        exact hRest false h rfl rfl (fun _ => rfl) hmem
      · simp only [hla, Bool.false_eq_true, ↓reduceIte, liftFSMulti, StateT.run_bind,
          StateT.run_lift, bind_assoc, pure_bind, mem_support_bind_iff] at hmem
        obtain ⟨ans, _, hmem⟩ := hmem
        rcases ans with _ | _
        · exact hRest false h rfl rfl (fun _ => rfl) hmem
        · rw [StateT.run_bind, StateT.run_modify, pure_bind] at hmem
          dsimp only at hmem
          let bk0 : FSMultiBook T E := (h.book sIdx).getD {}
          let h₁ : FSMultiState T RSt K I E :=
            { h with book := Function.update h.book sIdx (some { bk0 with sCorr := true }) }
          refine hRest true h₁ rfl rfl (fun j => ?_) hmem
          dsimp only [h₁, bk0, bookTrLen]
          by_cases hj : j = sIdx
          · subst hj; simp [Function.update_self, bookTrLen_getD_eq, bookTrLen]
          · simp [Function.update_of_ne hj]
    · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hmem
      exact hRest true h rfl rfl (fun _ => rfl) hmem

private theorem fsMultiFsRecv_preserve [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party) (t : ℕ)
    (rsv : RS ⊕ ℕ) (hdr : Header T) (e : E) (rec_ : Option (Record M (Header T × E)))
    (h : FSMultiState T RSt K I E) :
    ∀ res ∈ support (((hooksFSMulti cka prng fs Δcka mo gMain la).fsRecv ctx P t rsv hdr e rec_).run h),
      res.2.table = h.table ∧
      res.2.sessions = h.sessions ∧
      ∀ j, bookTrLen res.2.book j ≤ bookTrLen h.book j := by
  intro res hmem
  dsimp only [hooksFSMulti] at hmem
  rcases rsv with rs | sIdx
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    exact ⟨rfl, rfl, fun _ => le_rfl⟩
  · simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    set bk : FSMultiBook T E := (h.book sIdx).getD {}
    set matched : Option (ℕ × Header T × E) := bk.fsTrans.find? (fun x => x.2 == (hdr, e))
    have hAfterQ : ∀ qres : Option (FSAEAD.ReceiveResult M),
        res ∈ support (((match qres with
          | none => pure none
          | some .rejected => pure (some none)
          | some (.accepted i mo') =>
            if la && matched.isNone && decide (bk.fsCount < i) then do
              modify fun s : FSMultiState T RSt K I E => { s with lfWin := true }
              return none
            else do
              let drop := (matched.map (·.1)).getD i
              modify fun s : FSMultiState T RSt K I E =>
                let b := (s.book sIdx).getD {}
                let b' : FSMultiBook T E := { b with fsTrans := b.fsTrans.filter (·.1 != drop) }
                { s with book := Function.update s.book sIdx (some b') }
              match mo', rec_ with
              | some m, _ => return some (some ((.inr sIdx : RS ⊕ ℕ), i, m))
              | none, some r => return some (some ((.inr sIdx : RS ⊕ ℕ), i, r.msg))
              | none, none => return none :
          HM (FSMultiSpec SS RS T M E) (FSMultiState T RSt K I E)
            (Option (Option ((RS ⊕ ℕ) × ℕ × M)))).run h)) →
        res.2.table = h.table ∧ res.2.sessions = h.sessions ∧
        ∀ j, bookTrLen res.2.book j ≤ bookTrLen h.book j := by
      intro qres hmemQ
      rcases qres with _ | (_ | ⟨i, mo'⟩)
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmemQ
        subst hmemQ; exact ⟨rfl, rfl, fun _ => le_rfl⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmemQ
        subst hmemQ; exact ⟨rfl, rfl, fun _ => le_rfl⟩
      · dsimp only at hmemQ
        split_ifs at hmemQ
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff] at hmemQ
          subst hmemQ; exact ⟨rfl, rfl, fun _ => le_rfl⟩
        · simp only [StateT.run_bind, StateT.run_modify, pure_bind] at hmemQ
          have hFlt : ∀ j,
              bookTrLen (Function.update h.book sIdx
                (some { (h.book sIdx).getD {} with
                  fsTrans := ((h.book sIdx).getD {}).fsTrans.filter
                    (·.1 != (matched.map (·.1)).getD i) })) j ≤
              bookTrLen h.book j := by
            intro j
            dsimp only [bookTrLen]
            by_cases hj : j = sIdx
            · subst hj
              simp only [Function.update_self]
              exact (List.length_filter_le _ _).trans (by rw [bookTrLen_getD_eq]; rfl)
            · simp [Function.update_of_ne hj]
          rcases mo' with _ | m
          · rcases rec_ with _ | r <;>
              (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmemQ;
               subst hmemQ; exact ⟨rfl, rfl, hFlt⟩)
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmemQ
            subst hmemQ; exact ⟨rfl, rfl, hFlt⟩
    by_cases hm : matched.isSome = true
    · simp only [hm, ↓reduceIte, liftFSMulti, StateT.run_bind, StateT.run_lift,
        bind_assoc, pure_bind, mem_support_bind_iff] at hmem
      obtain ⟨qres, _, hmem⟩ := hmem
      exact hAfterQ qres hmem
    · simp only [hm, Bool.false_eq_true, ↓reduceIte, liftFSMulti, StateT.run_bind,
        StateT.run_lift, bind_assoc, pure_bind, mem_support_bind_iff] at hmem
      obtain ⟨qres, _, hmem⟩ := hmem
      exact hAfterQ qres hmem

private theorem fsMultiReveal_preserve [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    (h : FSMultiState T RSt K I E) (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E)
    (P : Party) (vp : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) :
    ∀ res ∈ support (((hooksFSMulti cka prng fs Δcka mo gMain la).reveal ctx P vp).run h),
      res.2.table = h.table ∧
      res.2.sessions = h.sessions ∧
      ∀ j, bookTrLen res.2.book j = bookTrLen h.book j := by
  intro res hmem
  simp only [hooksFSMulti, pure_bind] at hmem
  have hStep2 : ∀ (vS : Option SS) (h₁ : FSMultiState T RSt K I E),
      h₁.table = h.table → h₁.sessions = h.sessions →
      (∀ j, bookTrLen h₁.book j = bookTrLen h.book j) →
      res ∈ support (((if (match vp.vR mo.tStar with
          | some (.inr _) => true
          | _ => false) = true then
          pure none
        else
          pure (some (realParty vp vp.γ vp.root vS fun t =>
            match vp.vR t with
            | some (.inl rs) => some rs
            | _ => none)) :
        HM (FSMultiSpec SS RS T M E) (FSMultiState T RSt K I E)
          (Option (PartyState Γ T RSt SS RS))).run h₁)) →
      res.2.table = h.table ∧
      res.2.sessions = h.sessions ∧
      ∀ j, bookTrLen res.2.book j = bookTrLen h.book j := by
    intro vS h₁ htb hse hbk hmem2
    split_ifs at hmem2 <;>
      (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem2;
       subst hmem2; exact ⟨htb, hse, hbk⟩)
  rcases hvS : vp.vS with _ | (ss | sIdx)
  · simp only [hvS] at hmem
    exact hStep2 none h rfl rfl (fun _ => rfl) hmem
  · simp only [hvS] at hmem
    exact hStep2 (some ss) h rfl rfl (fun _ => rfl) hmem
  · simp only [hvS] at hmem
    by_cases hla : la = true
    · simp only [hla, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact ⟨rfl, rfl, fun _ => rfl⟩
    · simp only [hla, Bool.false_eq_true, ↓reduceIte, liftFSMulti, StateT.run_bind,
        StateT.run_lift, bind_assoc, pure_bind, mem_support_bind_iff] at hmem
      obtain ⟨ans, _, hmem⟩ := hmem
      rcases ans with _ | ss
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; exact ⟨rfl, rfl, fun _ => rfl⟩
      · simp only [StateT.run_bind, StateT.run_modify, pure_bind] at hmem
        let bk0 : FSMultiBook T E := (h.book sIdx).getD {}
        let h' : FSMultiState T RSt K I E :=
          { h with book := Function.update h.book sIdx (some { bk0 with sCorr := true }) }
        refine hStep2 (some ss) h' rfl rfl (fun j => ?_) hmem
        dsimp only [h', bk0, bookTrLen]
        by_cases hj : j = sIdx
        · subst hj; simp [Function.update_self, bookTrLen_getD_eq, bookTrLen]
        · simp [Function.update_of_ne hj]

private theorem vSend_fsMulti_preserve [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [Inhabited E] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (s : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) (m : M)
    (pair : Option (M × M)) (r : Option CCoins)
    (h : FSMultiState T RSt K I E) :
    ∀ res ∈ support ((vSend (hooksFSMulti cka prng fs Δcka mo gMain la) ctx P s m pair r).run h),
      res.2.table.length ≤ h.table.length + 1 ∧
      res.2.sessions.length ≤ h.sessions.length + 1 ∧
      (∀ j, bookTrLen res.2.book j ≤ bookTrLen h.book j + 1) ∧
      (∀ st' c, res.1 = some (st', c) →
        s.tcur ≤ st'.tcur ∧ st'.tcur ≤ s.tcur + 1 ∧ st'.vR = s.vR) := by
  intro ⟨vsRes, h'⟩ hmem
  rw [vSend_eq_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨s₁?, h₁⟩, hmem1, hmem2⟩ := hmem
  have hStep1 :
      h₁.table.length ≤ h.table.length + 1 ∧
      h₁.sessions.length ≤ h.sessions.length + 1 ∧
      h₁.book = h.book ∧
      (∀ s₁, s₁? = some s₁ →
        s.tcur ≤ s₁.tcur ∧ s₁.tcur ≤ s.tcur + 1 ∧ s₁.vR = s.vR) := by
    unfold vSendStep1 at hmem1
    split_ifs at hmem1
    · rw [StateT.run_bind, mem_support_bind_iff] at hmem1
      obtain ⟨⟨ssRes, h₁'⟩, hss, hmem1⟩ := hmem1
      have hPres := fsMultiStartSend_preserve cka prng fs Δcka mo gMain la ctx P
        (s.tcur + 1) s.γ s.root r h (ssRes, h₁') hss
      rcases ssRes with _ | ⟨γ', T', σ', ss⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem1
        rcases hmem1 with ⟨rfl, rfl⟩
        exact ⟨hPres.1, hPres.2.1, hPres.2.2, fun _ h => by cases h⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem1
        rcases hmem1 with ⟨rfl, rfl⟩
        refine ⟨hPres.1, hPres.2.1, hPres.2.2, fun s₁ hs₁ => ?_⟩
        cases hs₁
        exact ⟨Nat.le_succ _, le_rfl, rfl⟩
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem1
      rcases hmem1 with ⟨rfl, rfl⟩
      exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, rfl,
        fun s₁ hs₁ => by cases hs₁; exact ⟨le_rfl, Nat.le_succ _, rfl⟩⟩
  rcases s₁? with _ | s₁
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2
    rcases hmem2 with ⟨rfl, rfl⟩
    exact ⟨hStep1.1, hStep1.2.1, fun j => by rw [hStep1.2.2.1]; exact Nat.le_add_right _ _,
      fun _ _ h => by cases h⟩
  · have hs₁ := hStep1.2.2.2 s₁ rfl
    rcases hvS : s₁.vS with _ | v
    · simp only [hvS, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem2
      rcases hmem2 with ⟨rfl, rfl⟩
      refine ⟨hStep1.1, hStep1.2.1, fun j => by rw [hStep1.2.2.1]; exact Nat.le_add_right _ _,
        fun st' c hEq => ?_⟩
      cases hEq; exact hs₁
    · simp only [hvS] at hmem2
      rw [StateT.run_bind, mem_support_bind_iff] at hmem2
      obtain ⟨⟨fsRes, h₂⟩, hfs, hmem2⟩ := hmem2
      have hPres2 := fsMultiFsSend_preserve cka prng fs Δcka mo gMain la h₁ ctx P s₁.tcur v
        (s₁.tcur, s₁.curCkaMsg) m pair (fsRes, h₂) hfs
      rcases fsRes with _ | ⟨v', e⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2
        rcases hmem2 with ⟨rfl, rfl⟩
        exact ⟨by rw [hPres2.1]; exact hStep1.1,
          by rw [hPres2.2.1]; exact hStep1.2.1,
          fun j => by rw [← hStep1.2.2.1]; exact hPres2.2.2 j,
          fun _ _ h => by cases h⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2
        rcases hmem2 with ⟨rfl, rfl⟩
        refine ⟨by rw [hPres2.1]; exact hStep1.1,
          by rw [hPres2.2.1]; exact hStep1.2.1,
          fun j => by rw [← hStep1.2.2.1]; exact hPres2.2.2 j,
          fun st' c hEq => ?_⟩
        cases hEq; exact hs₁

private theorem vRecv_fsMulti_preserve [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (s : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ))
    (c : Header T × E) (rec : Option (Record M (Header T × E)))
    (h : FSMultiState T RSt K I E)
    (hvR : ∀ t, s.tcur < t → s.vR t = none) :
    ∀ res ∈ support ((vRecv (hooksFSMulti cka prng fs Δcka mo gMain la) ctx P s c rec).run h),
      res.2.table.length ≤ h.table.length + 1 ∧
      res.2.sessions.length ≤ h.sessions.length + 1 ∧
      (∀ j, bookTrLen res.2.book j ≤ bookTrLen h.book j) ∧
      (∀ st' t' i' m', res.1 = some (some (st', t', i', m')) →
        st'.tcur ≤ s.tcur + 1 ∧ (∀ t, st'.tcur < t → st'.vR t = none)) := by
  intro ⟨vrRes, h'⟩ hmem
  rw [vRecv_eq_bind] at hmem
  by_cases h1 : (s.id.sendsIn c.1.1 || decide (s.tcur + 1 < c.1.1)) = true
  · simp only [h1, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, fun _ => le_rfl, fun _ _ _ _ h => by cases h⟩
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hmem
    have htle : c.1.1 ≤ s.tcur + 1 := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at h1
      omega
    rw [StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨s₁?, h₁⟩, hmem1, hmem2⟩ := hmem
    have hStep1 :
        h₁.table.length ≤ h.table.length + 1 ∧
        h₁.sessions.length ≤ h.sessions.length + 1 ∧
        h₁.book = h.book ∧
        (∀ s₁, s₁? = some (some s₁) →
          c.1.1 ≤ s₁.tcur ∧ s₁.tcur ≤ s.tcur + 1 ∧
          (∀ t, s₁.tcur < t → s₁.vR t = none)) := by
      unfold vRecvStep1 at hmem1
      by_cases h2 : c.1.1 = s.tcur + 1
      · simp only [h2, ↓reduceIte] at hmem1
        rcases hTn : c.1.2 with _ | Tn
        · simp only [hTn, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem1
          rcases hmem1 with ⟨rfl, rfl⟩
          exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, rfl, fun _ h => by cases h⟩
        · simp only [hTn] at hmem1
          rw [StateT.run_bind, mem_support_bind_iff] at hmem1
          obtain ⟨⟨srRes, h₁'⟩, hsr, hmem1⟩ := hmem1
          have hPres := fsMultiStartRecv_preserve cka prng fs Δcka mo gMain la ctx P
            (s.tcur + 1) s.γ s.root Tn h (srRes, h₁') hsr
          rcases srRes with _ | _ | ⟨γ', σ', rs⟩
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem1
            rcases hmem1 with ⟨rfl, rfl⟩
            exact ⟨hPres.1, hPres.2.1, hPres.2.2, fun _ h => by cases h⟩
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem1
            rcases hmem1 with ⟨rfl, rfl⟩
            exact ⟨hPres.1, hPres.2.1, hPres.2.2, fun _ h => by cases h⟩
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem1
            rcases hmem1 with ⟨rfl, rfl⟩
            refine ⟨hPres.1, hPres.2.1, hPres.2.2, fun s₁ hs₁ => ?_⟩
            cases hs₁
            refine ⟨by omega, le_rfl, fun t ht => ?_⟩
            dsimp only at ht ⊢
            rw [Function.update_of_ne (by omega)]
            exact hvR t (by omega)
      · simp only [h2, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem1
        rcases hmem1 with ⟨rfl, rfl⟩
        refine ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, rfl, fun s₁ hs₁ => ?_⟩
        cases hs₁
        exact ⟨by omega, Nat.le_succ _, hvR⟩
    rcases s₁? with _ | _ | s₁
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2
      rcases hmem2 with ⟨rfl, rfl⟩
      exact ⟨hStep1.1, hStep1.2.1, fun j => by rw [hStep1.2.2.1], fun _ _ _ _ h => by cases h⟩
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2
      rcases hmem2 with ⟨rfl, rfl⟩
      exact ⟨hStep1.1, hStep1.2.1, fun j => by rw [hStep1.2.2.1], fun _ _ _ _ h => by cases h⟩
    · have hs₁ := hStep1.2.2.2 s₁ rfl
      rcases hvR1 : s₁.vR c.1.1 with _ | v
      · simp only [hvR1, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem2
        rcases hmem2 with ⟨rfl, rfl⟩
        exact ⟨hStep1.1, hStep1.2.1, fun j => by rw [hStep1.2.2.1], fun _ _ _ _ h => by cases h⟩
      · simp only [hvR1] at hmem2
        rw [StateT.run_bind, mem_support_bind_iff] at hmem2
        obtain ⟨⟨frRes, h₂⟩, hfr, hmem2⟩ := hmem2
        have hPres2 := fsMultiFsRecv_preserve cka prng fs Δcka mo gMain la ctx P c.1.1 v
          c.1 c.2 rec h₁ (frRes, h₂) hfr
        rcases frRes with _ | _ | ⟨v', i, m⟩
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2
          rcases hmem2 with ⟨rfl, rfl⟩
          exact ⟨by rw [hPres2.1]; exact hStep1.1,
            by rw [hPres2.2.1]; exact hStep1.2.1,
            fun j => by rw [← hStep1.2.2.1]; exact hPres2.2.2 j,
            fun _ _ _ _ h => by cases h⟩
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2
          rcases hmem2 with ⟨rfl, rfl⟩
          exact ⟨by rw [hPres2.1]; exact hStep1.1,
            by rw [hPres2.2.1]; exact hStep1.2.1,
            fun j => by rw [← hStep1.2.2.1]; exact hPres2.2.2 j,
            fun _ _ _ _ h => by cases h⟩
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2
          rcases hmem2 with ⟨rfl, rfl⟩
          refine ⟨by rw [hPres2.1]; exact hStep1.1,
            by rw [hPres2.2.1]; exact hStep1.2.1,
            fun j => by rw [← hStep1.2.2.1]; exact hPres2.2.2 j,
            fun st' t' i' m' hEq => ?_⟩
          cases hEq
          refine ⟨hs₁.2.1, fun t ht => ?_⟩
          dsimp only at ht ⊢
          rw [Function.update_of_ne (by omega)]
          exact hs₁.2.2 t ht

private theorem commitE_fsMulti_eq [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E)
      (FSMultiState T RSt K I E))
    (s : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (old new : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) (pos : Pos) :
    (commitE (hooksFSMulti cka prng fs Δcka mo gMain la) s P old new pos).run es =
      pure (some { s.accept P new pos with st := Function.update (s.accept P new pos).st P new },
        es) := by
  unfold commitE
  simp only [pure_bind, run_liftH_bind, hooksFSMulti, StateT.run_pure]

private theorem transmitE_fsMulti_inv [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [Inhabited E] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    {L B q Δ qep : ℕ} (π : Policy) (Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E)
      (FSMultiState T RSt K I E))
    (arg : Party × M × Option CCoins)
    (hInv : FSMultiEngineInv L B (q + 1) es) :
    ∀ res ∈ support ((transmitE (hooksFSMulti cka prng fs Δcka mo gMain la) Δ qep π arg).run es),
      FSMultiEngineInv L B q res.2 := by
  rcases arg with ⟨P, m, r⟩
  intro ⟨out, es'⟩ hmem
  have hInvQ : FSMultiEngineInv L B q es := hInv.mono (Nat.le_succ q)
  have hSm := transmitE_inv (hooksFSMulti cka prng fs Δcka mo gMain la) π es (P, m, r) hInv.sm
    (out, es') hmem
  unfold transmitE abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases hab : (es.abort || es.g.win)
  · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hInvQ
  · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
    rcases hep : es.g.epMgmt Δ qep P r.isSome with _ | s₁
    · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInvQ
    · simp only [hep] at hmem
      by_cases hdoom : π.leakDoom es.g s₁
      · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
          pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩
        exact ⟨hSm, hInvQ.table_le, hInvQ.sessions_le, hInvQ.fsTrans_le,
          hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
      · simp only [hdoom, Bool.false_eq_true, ↓reduceIte] at hmem
        rw [run_liftH_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨vsRes, h'⟩, hvs, hmem⟩ := hmem
        have hPres := vSend_fsMulti_preserve cka prng fs Δcka mo gMain la s₁ P (s₁.st P) m none r
          es.h (vsRes, h') hvs
        dsimp only at hPres
        have hSt₁ : s₁.st = es.g.st := epMgmt_st_eq hep
        rcases vsRes with _ | ⟨st', c⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩
          exact ⟨hSm,
            by dsimp only; have := hInv.table_le; have := hPres.1; omega,
            by dsimp only; have := hInv.sessions_le; have := hPres.2.1; omega,
            fsTrans_le_of_step1 hInv.bookTrLen_le hPres.2.2.1,
            hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩
          have hst' := hPres.2.2.2 st' c rfl
          rw [hSt₁] at hst'
          refine ⟨hSm,
            by dsimp only; have := hInv.table_le; have := hPres.1; omega,
            by dsimp only; have := hInv.sessions_le; have := hPres.2.1; omega,
            fsTrans_le_of_step1 hInv.bookTrLen_le hPres.2.2.1,
            fun Q => ?_, fun Q t ht => ?_⟩
          · dsimp only [SM.GameState.record]
            rw [hSt₁]
            by_cases hQ : Q = P
            · subst hQ; rw [Function.update_self]
              have := hInv.tcur_le Q; have := hst'.2.1; omega
            · rw [Function.update_of_ne hQ]; exact hInvQ.tcur_le Q
          · dsimp only [SM.GameState.record] at ht ⊢
            rw [hSt₁] at ht ⊢
            by_cases hQ : Q = P
            · subst hQ; rw [Function.update_self] at ht ⊢
              rw [hst'.2.2]
              exact hInv.vR_none_of_gt Q t (by have := hst'.1; omega)
            · rw [Function.update_of_ne hQ] at ht ⊢
              exact hInv.vR_none_of_gt Q t ht

private theorem challE_fsMulti_inv [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [Inhabited E] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    {L B q Δ qep : ℕ} (cfg : Config M) (π : Policy) (Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E)
      (FSMultiState T RSt K I E))
    (arg : Party × M × M × Option CCoins)
    (hInv : FSMultiEngineInv L B (q + 1) es) :
    ∀ res ∈ support ((challE (hooksFSMulti cka prng fs Δcka mo gMain la) Δ qep cfg π arg).run es),
      FSMultiEngineInv L B q res.2 := by
  rcases arg with ⟨P, m₀, m₁, r⟩
  intro ⟨out, es'⟩ hmem
  have hInvQ : FSMultiEngineInv L B q es := hInv.mono (Nat.le_succ q)
  have hSm := challE_inv (hooksFSMulti cka prng fs Δcka mo gMain la) cfg π es (P, m₀, m₁, r) hInv.sm
    (out, es') hmem
  unfold challE abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases hab : (es.abort || es.g.win)
  · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hInvQ
  · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
    rcases hep : es.g.epMgmt Δ qep P r.isSome with _ | s₁
    · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInvQ
    · simp only [hep] at hmem
      by_cases hch : (!(s₁.safeCh Δ P) || !(cfg.challAllowedIn (s₁.epoch P)))
      · simp only [hch, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hInvQ
      · simp only [hch, Bool.false_eq_true, ↓reduceIte] at hmem
        by_cases hdoom : π.leakDoom es.g s₁
        · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
            pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩
          exact ⟨hSm, hInvQ.table_le, hInvQ.sessions_le, hInvQ.fsTrans_le,
            hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
        · simp only [hdoom, Bool.false_eq_true, ↓reduceIte] at hmem
          rw [run_liftH_bind, mem_support_bind_iff] at hmem
          obtain ⟨⟨vsRes, h'⟩, hvs, hmem⟩ := hmem
          have hPres := vSend_fsMulti_preserve cka prng fs Δcka mo gMain la s₁ P (s₁.st P) _
            (some (m₀, m₁)) r es.h (vsRes, h') hvs
          dsimp only at hPres
          have hSt₁ : s₁.st = es.g.st := epMgmt_st_eq hep
          rcases vsRes with _ | ⟨st', c⟩
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩
            exact ⟨hSm,
              by dsimp only; have := hInv.table_le; have := hPres.1; omega,
              by dsimp only; have := hInv.sessions_le; have := hPres.2.1; omega,
              fsTrans_le_of_step1 hInv.bookTrLen_le hPres.2.2.1,
              hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩
            have hst' := hPres.2.2.2 st' c rfl
            rw [hSt₁] at hst'
            refine ⟨hSm,
              by dsimp only; have := hInv.table_le; have := hPres.1; omega,
              by dsimp only; have := hInv.sessions_le; have := hPres.2.1; omega,
              fsTrans_le_of_step1 hInv.bookTrLen_le hPres.2.2.1,
              fun Q => ?_, fun Q t ht => ?_⟩
            · dsimp only [SM.GameState.record]
              rw [hSt₁]
              by_cases hQ : Q = P
              · subst hQ; rw [Function.update_self]
                have := hInv.tcur_le Q; have := hst'.2.1; omega
              · rw [Function.update_of_ne hQ]; exact hInvQ.tcur_le Q
            · dsimp only [SM.GameState.record] at ht ⊢
              rw [hSt₁] at ht ⊢
              by_cases hQ : Q = P
              · subst hQ; rw [Function.update_self] at ht ⊢
                rw [hst'.2.2]
                exact hInv.vR_none_of_gt Q t (by have := hst'.1; omega)
              · rw [Function.update_of_ne hQ] at ht ⊢
                exact hInv.vR_none_of_gt Q t ht

private theorem deliverE_fsMulti_inv [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    {L B q maxSkip : ℕ} (cfg : Config M) (Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E)
      (FSMultiState T RSt K I E))
    (arg : Party × (Header T × E))
    (hInv : FSMultiEngineInv L B (q + 1) es) :
    ∀ res ∈ support ((deliverE (hooksFSMulti cka prng fs Δcka mo gMain la) maxSkip cfg arg).run es),
      FSMultiEngineInv L B q res.2 := by
  rcases arg with ⟨P, c⟩
  intro ⟨out, es'⟩ hmem
  have hInvQ : FSMultiEngineInv L B q es := hInv.mono (Nat.le_succ q)
  have hSm := deliverE_inv (hooksFSMulti cka prng fs Δcka mo gMain la) cfg es (P, c) hInv.sm
    (out, es') hmem
  unfold deliverE abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases hab : (es.abort || es.g.win)
  · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hInvQ
  · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
    rcases htr : es.g.inTransit P.other c with _ | r
    · simp only [htr, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInvQ
    · simp only [htr] at hmem
      rw [run_liftH_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨vrRes, h'⟩, hvr, hmem⟩ := hmem
      have hPres := vRecv_fsMulti_preserve cka prng fs Δcka mo gMain la es.g P (es.g.st P) c
        (some r) es.h (hInv.vR_none_of_gt P) (vrRes, h') hvr
      dsimp only at hPres
      have hBk1 : ∀ j, bookTrLen h'.book j ≤ bookTrLen es.h.book j + 1 :=
        fun j => (hPres.2.2.1 j).trans (Nat.le_succ _)
      rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩
        exact ⟨hSm,
          by dsimp only; have := hInv.table_le; have := hPres.1; omega,
          by dsimp only; have := hInv.sessions_le; have := hPres.2.1; omega,
          fsTrans_le_of_step1 hInv.bookTrLen_le hBk1,
          hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
      · by_cases hmust : (cfg.deliverWin && es.g.mustBeCorrect maxSkip P r)
        · simp only [hmust, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
            pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩
          exact ⟨hSm,
            by dsimp only; have := hInv.table_le; have := hPres.1; omega,
            by dsimp only; have := hInv.sessions_le; have := hPres.2.1; omega,
            fsTrans_le_of_step1 hInv.bookTrLen_le hBk1,
            hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
        · simp only [hmust, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩
          exact ⟨hSm,
            by dsimp only; have := hInv.table_le; have := hPres.1; omega,
            by dsimp only; have := hInv.sessions_le; have := hPres.2.1; omega,
            fsTrans_le_of_step1 hInv.bookTrLen_le hBk1,
            hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
      · simp only [StateT.run_bind, commitE_fsMulti_eq, pure_bind, StateT.run_modify,
          StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩
        have hst' := hPres.2.2.2 st' t' i' m' rfl
        refine ⟨hSm,
          by dsimp only; have := hInv.table_le; have := hPres.1; omega,
          by dsimp only; have := hInv.sessions_le; have := hPres.2.1; omega,
          fsTrans_le_of_step1 hInv.bookTrLen_le hBk1,
          fun Q => ?_, fun Q t ht => ?_⟩
        · split_ifs <;> dsimp only [SM.GameState.accept]
          · by_cases hQ : Q = P
            · subst hQ; simp only [Function.update_self]
              have := hInv.tcur_le Q; have := hst'.1; omega
            · simp only [Function.update_of_ne hQ]; exact hInvQ.tcur_le Q
          · by_cases hQ : Q = P
            · subst hQ; simp only [Function.update_self]
              have := hInv.tcur_le Q; have := hst'.1; omega
            · simp only [Function.update_of_ne hQ]; exact hInvQ.tcur_le Q
        · split_ifs at ht ⊢ <;> dsimp only [SM.GameState.accept] at ht ⊢
          · by_cases hQ : Q = P
            · subst hQ; simp only [Function.update_self] at ht ⊢; exact hst'.2 t ht
            · simp only [Function.update_of_ne hQ] at ht ⊢; exact hInv.vR_none_of_gt Q t ht
          · by_cases hQ : Q = P
            · subst hQ; simp only [Function.update_self] at ht ⊢; exact hst'.2 t ht
            · simp only [Function.update_of_ne hQ] at ht ⊢; exact hInv.vR_none_of_gt Q t ht

private theorem injectE_fsMulti_inv [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    {L B q Δ qep : ℕ} (cfg : Config M) (Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E)
      (FSMultiState T RSt K I E))
    (arg : Party × (Header T × E))
    (hInv : FSMultiEngineInv L B (q + 1) es) :
    ∀ res ∈ support ((injectE (hooksFSMulti cka prng fs Δcka mo gMain la) Δ qep cfg arg).run es),
      FSMultiEngineInv L B q res.2 := by
  rcases arg with ⟨P, c⟩
  intro ⟨out, es'⟩ hmem
  have hInvQ : FSMultiEngineInv L B q es := hInv.mono (Nat.le_succ q)
  have hSm := injectE_inv (hooksFSMulti cka prng fs Δcka mo gMain la) cfg es (P, c) hInv.sm
    (out, es') hmem
  unfold injectE abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases href : (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj Δ))
  · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hInvQ
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hmem
    rw [run_liftH_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨vrRes, h'⟩, hvr, hmem⟩ := hmem
    have hPres := vRecv_fsMulti_preserve cka prng fs Δcka mo gMain la es.g P (es.g.st P) c none
      es.h (hInv.vR_none_of_gt P) (vrRes, h') hvr
    dsimp only at hPres
    have hBk1 : ∀ j, bookTrLen h'.book j ≤ bookTrLen es.h.book j + 1 :=
      fun j => (hPres.2.2.1 j).trans (Nat.le_succ _)
    rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
    · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩
      exact ⟨hSm,
        by dsimp only; have := hInv.table_le; have := hPres.1; omega,
        by dsimp only; have := hInv.sessions_le; have := hPres.2.1; omega,
        fsTrans_le_of_step1 hInv.bookTrLen_le hBk1,
        hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩
      exact ⟨hSm,
        by dsimp only; have := hInv.table_le; have := hPres.1; omega,
        by dsimp only; have := hInv.sessions_le; have := hPres.2.1; omega,
        fsTrans_le_of_step1 hInv.bookTrLen_le hBk1,
        hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
    · by_cases hqep : qep + 1 < t'
      · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩
        exact ⟨hSm,
          by dsimp only; have := hInv.table_le; have := hPres.1; omega,
          by dsimp only; have := hInv.sessions_le; have := hPres.2.1; omega,
          fsTrans_le_of_step1 hInv.bookTrLen_le hBk1,
          hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
      · simp only [hqep, ↓reduceIte] at hmem
        by_cases htriv : es.g.trivial Δ ⟨P.other, t', i'⟩
        · simp only [htriv, ↓reduceIte, StateT.run_bind, commitE_fsMulti_eq, pure_bind,
            StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩
          have hst' := hPres.2.2.2 st' t' i' m' rfl
          refine ⟨hSm,
            by dsimp only; have := hInv.table_le; have := hPres.1; omega,
            by dsimp only; have := hInv.sessions_le; have := hPres.2.1; omega,
            fsTrans_le_of_step1 hInv.bookTrLen_le hBk1,
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
              fsTrans_le_of_step1 hInv.bookTrLen_le hBk1,
              hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
          · simp only [hf, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩
            exact ⟨hSm,
              by dsimp only; have := hInv.table_le; have := hPres.1; omega,
              by dsimp only; have := hInv.sessions_le; have := hPres.2.1; omega,
              fsTrans_le_of_step1 hInv.bookTrLen_le hBk1,
              hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩

private theorem corrE_fsMulti_inv [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    {L B q : ℕ} (π : Policy) (Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E)
      (FSMultiState T RSt K I E))
    (P : Party)
    (hInv : FSMultiEngineInv L B (q + 1) es) :
    ∀ res ∈ support ((corrE (hooksFSMulti cka prng fs Δcka mo gMain la) π P).run es),
      FSMultiEngineInv L B q res.2 := by
  intro ⟨out, es'⟩ hmem
  have hInvQ : FSMultiEngineInv L B q es := hInv.mono (Nat.le_succ q)
  have hSm := corrE_inv (hooksFSMulti cka prng fs Δcka mo gMain la) π es P hInv.sm
    (out, es') hmem
  unfold corrE abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases href : (es.abort || es.g.win || !(es.g.corrAllowed P))
  · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hInvQ
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hmem
    by_cases hdoom : (π.leakDoom es.g (es.g.afterCorr P) || π.corrDoom es.g P)
    · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
        pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩
      exact ⟨hSm, hInvQ.table_le, hInvQ.sessions_le, hInvQ.fsTrans_le,
        hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
    · simp only [hdoom, Bool.false_eq_true, ↓reduceIte] at hmem
      rw [run_liftH_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨revRes, h'⟩, hrev, hmem⟩ := hmem
      have hPres := fsMultiReveal_preserve cka prng fs Δcka mo gMain la es.h es.g P (es.g.st P)
        (revRes, h') hrev
      have hBk1 : ∀ j, bookTrLen h'.book j ≤ bookTrLen es.h.book j + 1 :=
        fun j => by rw [hPres.2.2 j]; exact Nat.le_succ _
      rcases revRes with _ | st
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩
        exact ⟨hSm,
          by dsimp only; rw [hPres.1]; exact hInvQ.table_le,
          by dsimp only; rw [hPres.2.1]; exact hInvQ.sessions_le,
          fsTrans_le_of_step1 hInv.bookTrLen_le hBk1,
          hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩
        exact ⟨hSm,
          by dsimp only; rw [hPres.1]; exact hInvQ.table_le,
          by dsimp only; rw [hPres.2.1]; exact hInvQ.sessions_le,
          fsTrans_le_of_step1 hInv.bookTrLen_le hBk1,
          hInvQ.tcur_le, hInvQ.vR_none_of_gt⟩

private theorem implE_fsMulti_inv [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [Inhabited E] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    {L B q Δ qep maxSkip : ℕ} (cfg : Config M) (π : Policy)
    (Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E)
      (FSMultiState T RSt K I E))
    (t : (SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hInv : FSMultiEngineInv L B (q + 1) es) :
    ∀ res ∈ support ((implE (hooksFSMulti cka prng fs Δcka mo gMain la) Δ qep maxSkip cfg π (.inr t)).run es),
      FSMultiEngineInv L B q res.2 := by
  rcases t with (((arg | arg) | arg) | arg) | P
  · exact transmitE_fsMulti_inv cka prng fs π Δcka mo gMain la es arg hInv
  · exact challE_fsMulti_inv cka prng fs cfg π Δcka mo gMain la es arg hInv
  · exact deliverE_fsMulti_inv cka prng fs cfg Δcka mo gMain la es arg hInv
  · exact injectE_fsMulti_inv cka prng fs cfg Δcka mo gMain la es arg hInv
  · exact corrE_fsMulti_inv cka prng fs π Δcka mo gMain la es P hInv

private theorem isHonestHdrFSMultiE_eval
    {ckaInitA : KC → Γ} {ckaInitB : KC → Γ}
    {ckaSend : Γ → CCoins → Γ × T × I} {ckaReceive : Γ → T → Γ × I}
    {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
    {fsInitSender : K → SS} {fsInitReceiver : K → RS}
    {fsSend : SS → Header T → M → SS × E}
    {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
    {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
    {lam : I} {defaultE : E}
    [DecidableEq T]
    (heqT : eqT = (· == ·))
    {Γ'}
    (hE : Expr (prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
      fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE) Γ'
      (fsMultiHsTy KC Γ CCoins T I KR RSt K SS RS M E))
    (hdrE : Expr (prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
      fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE) Γ'
      (ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E))
    (ρ : Env Γ')
    (h : FSMultiState T RSt K I E) (hdr : Header T)
    (hh : hE.eval ρ = fsMultiHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR)
      (SS := SS) (RS := RS) (M := M) h)
    (hhdr : hdrE.eval ρ = hdr) :
    (isHonestHdrFSMultiE hE hdrE).eval ρ = isHonestHdrFSMulti h hdr := by
  unfold isHonestHdrFSMultiE isHonestHdrFSMulti
  rw [letE_eval]
  have hPair : (Expr.pair hE hdrE).eval ρ =
      (fsMultiHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR)
        (SS := SS) (RS := RS) (M := M) h, hdr) := by
    simp [Expr.eval, hh, hhdr]
  rw [hPair]
  dsimp only [Expr.eval, fsMultiHsCache, fsMultiHsEnc, Expr.v0, Expr.v1, prngOps, ckaOps]
  simp only [Env.get_cons_zero, Env.get_cons_succ]
  rcases hca : h.cache hdr.1 with _ | ⟨Tc, σc, k, optIdx⟩
  · rfl
  · rcases h2 : hdr.2 with _ | Tn
    · rfl
    · dsimp only; rw [heqT]

section MultiStage2EvalHelpers

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

local notation "IIM" =>
  fsaeadMultiHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK

local notation "mHsTy" => fsMultiHsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mVpTy" => fsMultiVpTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mEsTy" => fsMultiEsTy KC Γ CCoins T I KR RSt K SS RS M E

private def postHandleFalseE {Γ'} :
    Expr OO
      (.prod (ckaSMR KC Γ CCoins T I KR RSt K SS RS M E) mEsTy ::
        mEsTy :: ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E :: Γ')
      mEsTy :=
  rdslExpr [(_, es'), es0, q0] =>
    let wasWin := cGsWin (esG es0)
    let suppressHonestWin :=
      match q0 with
      | .inl qL =>
        match qL with
        | .inl _ => false
        | .inr x => isHonestHdrFSMultiE (esH es0) x.2.1
      | .inr _ => false
    if !wasWin && cGsWin (esG es') && suppressHonestWin then
      esSetG es' (cGsSetWin (esG es') false)
    else es'

private def handleMultiStage2EC (L B Δcka qep maxSkip : ℕ) (gMain la : Bool)
    (tL : Option ℕ) (t : ℕ) :
    Comp OO IIM
      (mEsTy :: ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E :: [])
      (.prod (ckaSMR KC Γ CCoins T I KR RSt K SS RS M E) mEsTy) :=
  if gMain then
    rdsl [es0, q0] do
      implEC (raw (hooksFSMultiC L B Δcka ⟨true, tL, t⟩ true la)) L (raw (2 + Δcka)) qep maxSkip
        (raw (modeCfgEC OO ⟨true, tL, t⟩)) (raw (⟨true, tL, t⟩ : Mode).policy) es0 q0
  else
    rdsl [es0, q0] do
      let wasWin := cGsWin (esG es0)
      (out, es') ← implEC (raw (hooksFSMultiC L B Δcka ⟨true, tL, t⟩ false la)) L (raw (2 + Δcka))
        qep maxSkip (raw (modeCfgEC OO ⟨true, tL, t⟩)) (raw (⟨true, tL, t⟩ : Mode).policy) es0 q0
      let suppressHonestWin :=
        match q0 with
        | .inl qL =>
          match qL with
          | .inl _ => false
          | .inr x => isHonestHdrFSMultiE (esH es0) x.2.1
        | .inr _ => false
      let esFinal :=
        if !wasWin && cGsWin (esG es') && suppressHonestWin then
          esSetG es' (cGsSetWin (esG es') false)
        else es'
      return (out, esFinal)

private theorem postHandleFalseE_eval [DecidableEq T]
    (heqT : eqT = (· == ·))
    {Γ'} (rOut : (ckaSMR KC Γ CCoins T I KR RSt K SS RS M E).denote)
    (ρ_tail : Env Γ')
    (es₀ es₁ : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E)
      (FSMultiState T RSt K I E))
    (t_sm : (SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain) :
    (postHandleFalseE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)).eval
      (Env.cons (t := .prod (ckaSMR KC Γ CCoins T I KR RSt K SS RS M E) mEsTy)
        (rOut, esEnc
          (fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (K := K)
            (M := M) (E := E))
          (fsMultiHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (SS := SS) (RS := RS)
            (M := M)) es₁)
        (Env.cons (t := mEsTy)
          (esEnc
            (fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (K := K)
              (M := M) (E := E))
            (fsMultiHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (SS := SS) (RS := RS)
              (M := M)) es₀)
          (Env.cons (t := ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E)
            ((ckaSMCodec KC Γ CCoins T I KR RSt K SS RS M E).qenc t_sm) ρ_tail))) =
      esEnc
        (fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (K := K)
          (M := M) (E := E))
        (fsMultiHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (SS := SS) (RS := RS)
          (M := M))
        (let suppress := match (.inr t_sm :
            (unifSpec + SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain) with
          | .inr (.inl (.inr (_P, hdr, _e))) => isHonestHdrFSMulti es₀.h hdr
          | _ => false
         if !es₀.g.win && es₁.g.win && suppress then
           { es₁ with g := { es₁.g with win := false } }
         else es₁) := by
  set ρ := Env.cons (t := .prod (ckaSMR KC Γ CCoins T I KR RSt K SS RS M E) mEsTy)
    (rOut, esEnc
      (fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (K := K)
        (M := M) (E := E))
      (fsMultiHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (SS := SS) (RS := RS)
        (M := M)) es₁)
    (Env.cons (t := mEsTy)
      (esEnc
        (fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (K := K)
          (M := M) (E := E))
        (fsMultiHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (SS := SS) (RS := RS)
          (M := M)) es₀)
      (Env.cons (t := ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E)
        ((ckaSMCodec KC Γ CCoins T I KR RSt K SS RS M E).qenc t_sm) ρ_tail))
  have hWas : (cGsWin (esG (O' := OO) .v1)).eval ρ = es₀.g.win := rfl
  have hWin1 : (cGsWin (esG (O' := OO) (.snd .v0))).eval ρ = es₁.g.win := rfl
  have hSetWin := cGsSetWin_eval
    (fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (K := K)
      (M := M) (E := E))
    (O' := OO) (esG (.snd .v0)) (.bool false) ρ es₁.g rfl
  have hSetG := esSetG_eval
    (fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (K := K)
      (M := M) (E := E))
    (fsMultiHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (SS := SS) (RS := RS)
      (M := M))
    (O' := OO) (.snd .v0) (cGsSetWin (esG (.snd .v0)) (.bool false)) ρ
    es₁ { es₁.g with win := false } rfl hSetWin
  set supE : Expr OO
      (.prod (ckaSMR KC Γ CCoins T I KR RSt K SS RS M E) mEsTy ::
        mEsTy :: ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E :: Γ') .bool :=
    Expr.caseSum .v2
      (Expr.caseSum .v0 (.bool false)
        (isHonestHdrFSMultiE (esH .v3) (.fst (.snd .v0))))
      (.bool false)
  have hSup : supE.eval ρ =
      (match (.inr t_sm :
          (unifSpec + SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain) with
        | .inr (.inl (.inr (_P, hdr, _e))) => isHonestHdrFSMulti es₀.h hdr
        | _ => false) := by
    rcases t_sm with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, hdr, e⟩) | ⟨P, hdr, e⟩) | P
    · rfl
    · rfl
    · rfl
    · dsimp only [supE, ckaSMCodec, Expr.eval, Expr.v0, Expr.v2]
      exact isHonestHdrFSMultiE_eval heqT (esH .v3) (.fst (.snd .v0)) _ es₀.h hdr rfl rfl
    · rfl
  change (Expr.ite (Expr.and (Expr.and (Expr.not (cGsWin (esG .v1))) (cGsWin (esG (.snd .v0)))) supE)
      (esSetG (.snd .v0) (cGsSetWin (esG (.snd .v0)) (.bool false))) (.snd .v0)).eval ρ = _
  dsimp only [Expr.eval]
  simp only [hWas, hWin1, hSup]
  split_ifs
  · exact hSetG
  · rfl

private def postShallowFSMulti [DecidableEq T]
    (es₀ : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E))
    (t_sm : (SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (es₁ : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E)) :
    EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E) :=
  let suppress := match (.inr t_sm :
      (unifSpec + SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain) with
    | .inr (.inl (.inr (_P, hdr, _e))) => isHonestHdrFSMulti es₀.h hdr
    | _ => false
  if !es₀.g.win && es₁.g.win && suppress then
    { es₁ with g := { es₁.g with win := false } }
  else es₁

private def postEncFSMulti
    (s₀ : (mEsTy).denote)
    (q₀ : (ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E).denote)
    (s₁ : (mEsTy).denote) : (mEsTy).denote :=
  (postHandleFalseE (Γ' := []) (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)).eval
    (Env.cons (t := .prod (ckaSMR KC Γ CCoins T I KR RSt K SS RS M E) mEsTy)
      (.inl (.inl (.inl (.inl none))), s₁)
      (Env.cons (t := mEsTy) s₀
        (Env.cons (t := ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E) q₀ .nil)))

private theorem bind_pure_rdec_eq_map {ι : Type} {spec : OracleSpec ι} {R₀ S₀ R₁ : Type}
    (rdec : R₀ → R₁) (oa : OracleComp spec (R₀ × S₀)) :
    (oa >>= fun q => pure (rdec q.1, q.2)) = (fun q => (rdec q.1, q.2)) <$> oa := by
  rw [map_eq_bind_pure_comp]; rfl

private theorem map_rdec_bind_post {ι : Type} {spec : OracleSpec ι} {R₀ S₀ R₁ : Type}
    (rdec : R₀ → R₁) (f : S₀ → S₀) (oa : OracleComp spec (R₀ × S₀)) :
    (fun q : R₀ × S₀ => (rdec q.1, q.2)) <$> (oa >>= fun p => pure (p.1, f p.2)) =
      Prod.map id f <$> ((fun p => (rdec p.1, p.2)) <$> oa) := by
  simp [map_eq_bind_pure_comp, bind_assoc, Prod.map]

private theorem map_post_map_enc {ι : Type} {spec : OracleSpec ι} {U₀ E₀ S₀ : Type}
    (enc : E₀ → S₀) (f : S₀ → S₀) (g : E₀ → E₀) (oa : OracleComp spec (U₀ × E₀))
    (hf : ∀ e, f (enc e) = enc (g e)) :
    Prod.map id f <$> (Prod.map id enc <$> oa) =
      Prod.map id enc <$> (Prod.map id g <$> oa) := by
  simp only [Functor.map_map, Prod.map, id, hf]

private theorem simulateQ_implEMultiStage2_eq
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B B_q Δcka qep : ℕ) (gMain la : Bool) (tL : Option ℕ) (t : ℕ)
    (hSend : ckaSend = cka.send)
    (hRecv : ckaReceive = cka.receive)
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send)
    (heqT : eqT = (· == ·))
    (heqI : eqI = (· == ·))
    (heqM : eqM = (· == ·))
    (heqE : eqE = (· == ·))
    (hDefaultE : defaultE = default)
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hSampI : sampI = ($ᵗ I : ProbComp I))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (hFsRecvB : ∀ rs hdr e,
      (fsReceive rs hdr e).map (fun (rs', i, m) => (rs', min i B, m)) =
        fs.receive rs hdr e) :
    ∀ {α : Type}
      {oa : OracleComp (unifSpec + SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) α}
      {qAdv : ℕ},
      oa.IsQueryBoundP
        (isGameQuery (G := SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) qAdv →
      ∀ (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E)
          (FSMultiState T RSt K I E)),
        FSMultiEngineInv L B_q qAdv es →
        (simulateQ
          (handlerImpl (C := prngSMCodec KC Γ CCoins T I KR RSt K SS RS M E)
            (handleMultiStage2EC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
              (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
              (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
              (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
              (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
              (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
              (sampI := sampI) (sampK := sampK) L B Δcka qep fs.maxSkip gMain la tL t))
          oa).run
          (esEnc
            (fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (K := K)
              (M := M) (E := E))
            (fsMultiHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (SS := SS) (RS := RS)
              (M := M)) es) =
          (Prod.map id
            (esEnc
              (fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (K := K)
                (M := M) (E := E))
              (fsMultiHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (SS := SS)
                (RS := RS) (M := M))) <$>
            (simulateQ (implEMultiStage2 cka prng fs Δcka qep gMain la tL t) oa).run es) ∧
        ∀ res ∈ support ((simulateQ (implEMultiStage2 cka prng fs Δcka qep gMain la tL t) oa).run es),
          FSMultiEngineInv L B_q 0 res.2 := by
  let mo : Mode := ⟨true, tL, t⟩
  have hHk := hooksFSMultiC_agrees (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (prngInit := prngInit) (eqM := eqM) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC)
    cka prng fs L B Δcka mo gMain la hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend
    heqT heqI heqE hSampCCoins hSampI hSampK hFsRecvB
  let vpE := vpTblEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
    (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
    (γvT := .base .γ) (svT := .base .sig)
    (ssvT := .sum (.base .ss) .nat) (rsvT := .sum (.base .rs) .nat)
  have hVp : fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
      (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E) = vpE := rfl
  intro α oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro qAdv _ es hInv
    refine ⟨by simp [simulateQ_pure, Prod.map], ?_⟩
    intro res hmem
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    exact hInv.mono (Nat.zero_le qAdv)
  | query_bind q mx ih =>
    intro qAdv hq es hInv
    rw [isQueryBoundP_query_bind_iff] at hq
    rw [run_simulateQ_query_bind, run_simulateQ_query_bind]
    cases q with
    | inl n =>
      have hCoinL :
          ((handlerImpl (C := prngSMCodec KC Γ CCoins T I KR RSt K SS RS M E)
            (handleMultiStage2EC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
              (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
              (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
              (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
              (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
              (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
              (sampI := sampI) (sampK := sampK) L B Δcka qep fs.maxSkip gMain la tL t))
            (.inl n)).run
            (esEnc
              (fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (K := K)
                (M := M) (E := E))
              (fsMultiHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (SS := SS)
                (RS := RS) (M := M)) es) =
          (fun u => (u, esEnc
            (fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (K := K)
              (M := M) (E := E))
            (fsMultiHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (SS := SS)
              (RS := RS) (M := M)) es)) <$>
            query (spec := unifSpec + FSMultiSpec SS RS T M E) (.inl n) := by
        simp [handlerImpl, StateT.run_lift, map_eq_bind_pure_comp]
      have hCoinR :
          (implEMultiStage2 cka prng fs Δcka qep gMain la tL t (.inl n)).run es =
          (fun u => (u, es)) <$>
            query (spec := unifSpec + FSMultiSpec SS RS T M E) (.inl n) := by
        unfold implEMultiStage2
        cases gMain <;>
          simp [implE, coinsE, StateT.run_bind, StateT.run_get, StateT.run_lift,
            StateT.run_pure, pure_bind, map_eq_bind_pure_comp]
      rw [hCoinL, hCoinR, bind_map_left, bind_map_left, map_bind]
      refine ⟨bind_congr fun u => (ih u (hq.2 u) es hInv).1, ?_⟩
      intro res hmem
      rw [mem_support_bind_iff] at hmem
      obtain ⟨u, _, hmem⟩ := hmem
      exact (ih u (hq.2 u) es hInv).2 res hmem
    | inr t_sm =>
      have hpos : 0 < qAdv := hq.1.resolve_left (by simp [isGameQuery])
      obtain ⟨m, rfl⟩ : ∃ m, qAdv = m + 1 := ⟨qAdv - 1, by omega⟩
      have hqm : ∀ u, (mx u).IsQueryBoundP
          (isGameQuery (G := SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) m := by
        intro u; simpa [isGameQuery] using hq.2 u
      have hHB : FSMultiHBounded L es.h := hInv.toFSMultiHBounded
      set ρ₀ := Env.cons (t := mEsTy)
        (esEnc vpE
          (fsMultiHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (SS := SS)
            (RS := RS) (M := M)) es)
        (Env.cons (t := ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E)
          ((ckaSMCodec KC Γ CCoins T I KR RSt K SS RS M E).qenc t_sm) .nil)
      have hStepCore := rdec_implEC_eval hDefaultE
        (fsMultiHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (SS := SS)
          (RS := RS) (M := M))
        (FSMultiHBounded L) (HBoundedPost := FSMultiHBoundedPost L) (VROk := fun _ => True)
        (hooksFSMultiC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
          (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L B Δcka mo gMain la)
        (hooksFSMultiL cka prng fs L Δcka mo gMain la) hHk
        L (2 + Δcka) qep fs.maxSkip (modeCfgEC OO mo) mo.cfg (modeCfgEC_agrees mo)
        heqT heqM heqE mo.policy .v0 .v1 ρ₀
        es t_sm hHB hInv.sm.toBoundedEngine (fun _ _ _ _ => trivial) rfl rfl
      rw [implE_hooksFSMultiL_eq cka prng fs L (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy
        Δcka mo gMain la es t_sm hInv.vR_none_of_le_L] at hStepCore
      cases gMain with
      | true =>
        have hStep :
            ((handlerImpl (C := prngSMCodec KC Γ CCoins T I KR RSt K SS RS M E)
              (handleMultiStage2EC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
                (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
                (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
                (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
                (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
                (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
                (sampI := sampI) (sampK := sampK) L B Δcka qep fs.maxSkip true la tL t))
              (.inr t_sm)).run
              (esEnc
                (fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (K := K)
                  (M := M) (E := E))
                (fsMultiHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (SS := SS)
                  (RS := RS) (M := M)) es) =
            Prod.map id
              (esEnc
                (fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (K := K)
                  (M := M) (E := E))
                (fsMultiHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (SS := SS)
                  (RS := RS) (M := M))) <$>
              (implEMultiStage2 cka prng fs Δcka qep true la tL t (.inr t_sm)).run es := by
          have hHdlTrue :
              handleMultiStage2EC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
                (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
                (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
                (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
                (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
                (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
                (sampI := sampI) (sampK := sampK) L B Δcka qep fs.maxSkip true la tL t =
              implEC (hooksFSMultiC L B Δcka mo true la) L (2 + Δcka) qep fs.maxSkip
                (modeCfgEC OO mo) mo.policy .v0 .v1 := rfl
          have hImplTrue :
              implEMultiStage2 cka prng fs Δcka qep true la tL t =
              implE (hooksFSMulti cka prng fs Δcka mo true la)
                (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy := rfl
          rw [hHdlTrue, hImplTrue, hVp]
          dsimp only [vpE, ρ₀] at hStepCore ⊢
          simp only [handlerImpl, StateT.run_mk, prngSMCodec, ← hStepCore,
            map_eq_bind_pure_comp, Function.comp_def]
        rw [hStep, bind_map_left, map_bind]
        refine ⟨OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es₁⟩ hmem => ?_, ?_⟩
        · dsimp only [implEMultiStage2, ↓reduceIte] at hmem
          have hInv₁ := implE_fsMulti_inv cka prng fs mo.cfg mo.policy Δcka mo true la
            es t_sm hInv (u, es₁) hmem
          exact (ih u (hqm u) es₁ hInv₁).1
        · intro res hmem
          rw [mem_support_bind_iff] at hmem
          obtain ⟨⟨u, es₁⟩, hmem₁, hmem₂⟩ := hmem
          dsimp only [implEMultiStage2, ↓reduceIte] at hmem₁
          have hInv₁ := implE_fsMulti_inv cka prng fs mo.cfg mo.policy Δcka mo true la
            es t_sm hInv (u, es₁) hmem₁
          exact (ih u (hqm u) es₁ hInv₁).2 res hmem₂
      | false =>
        have hHdlEq :
            handleMultiStage2EC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
              (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
              (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
              (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
              (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
              (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
              (sampI := sampI) (sampK := sampK) L B Δcka qep fs.maxSkip false la tL t =
            Comp.bind
              (implEC (hooksFSMultiC L B Δcka mo false la) L (2 + Δcka) qep fs.maxSkip
                (modeCfgEC OO mo) mo.policy .v0 .v1)
              (Comp.ret (.pair (.fst .v0)
                (postHandleFalseE (Γ' := []) (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
                  (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
                  (prngUp := prngUp) (fsInitSender := fsInitSender)
                  (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
                  (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
                  (lam := lam) (defaultE := defaultE)))) := rfl
        have hPostEval : ∀ es₁,
            postEncFSMulti (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
              (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
              (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
              (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
              (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
              (esEnc
                (fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (K := K)
                  (M := M) (E := E))
                (fsMultiHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (SS := SS)
                  (RS := RS) (M := M)) es)
              ((ckaSMCodec KC Γ CCoins T I KR RSt K SS RS M E).qenc t_sm)
              (esEnc
                (fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (K := K)
                  (M := M) (E := E))
                (fsMultiHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (SS := SS)
                  (RS := RS) (M := M)) es₁) =
            esEnc
              (fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (K := K)
                (M := M) (E := E))
              (fsMultiHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (SS := SS)
                (RS := RS) (M := M)) (postShallowFSMulti es t_sm es₁) := by
          intro es₁
          unfold postEncFSMulti postShallowFSMulti
          exact postHandleFalseE_eval heqT (.inl (.inl (.inl (.inl none)))) .nil es es₁ t_sm
        have hStepCore' :
            ((fun p => ((ckaSMCodec KC Γ CCoins T I KR RSt K SS RS M E).rdec t_sm p.1, p.2)) <$>
              (implEC (hooksFSMultiC (sampKR := sampKR) (sampKC := sampKC)
                (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
                L B Δcka mo false la) L (2 + Δcka) qep fs.maxSkip
                (modeCfgEC OO mo) mo.policy .v0 .v1).eval ρ₀) =
            Prod.map id
              (esEnc
                (fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (K := K)
                  (M := M) (E := E))
                (fsMultiHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (SS := SS)
                  (RS := RS) (M := M))) <$>
              (implE (hooksFSMulti cka prng fs Δcka mo false la)
                (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy (.inr t_sm)).run es := by
          rw [hVp]
          exact hStepCore
        have hρ₀ : ρ₀ = Env.cons (t := mEsTy)
            (esEnc
              (fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (K := K)
                (M := M) (E := E))
              (fsMultiHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (SS := SS)
                (RS := RS) (M := M)) es)
            (Env.cons (t := ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E)
              ((ckaSMCodec KC Γ CCoins T I KR RSt K SS RS M E).qenc t_sm) .nil) := by
          rw [hVp]
        have hBindEq :
            ((implEC (hooksFSMultiC (sampKR := sampKR) (sampKC := sampKC)
                (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
                L B Δcka mo false la) L (2 + Δcka) qep fs.maxSkip
                (modeCfgEC OO mo) mo.policy .v0 .v1).eval ρ₀ >>=
              fun p =>
                (Comp.ret (I := IIM) (.pair (.fst .v0)
                  (postHandleFalseE (Γ' := []) (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
                    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
                    (prngUp := prngUp) (fsInitSender := fsInitSender)
                    (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
                    (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
                    (lam := lam) (defaultE := defaultE)))).eval (Env.cons p ρ₀)) =
            ((implEC (hooksFSMultiC (sampKR := sampKR) (sampKC := sampKC)
                (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
                L B Δcka mo false la) L (2 + Δcka) qep fs.maxSkip
                (modeCfgEC OO mo) mo.policy .v0 .v1).eval ρ₀ >>=
              fun p =>
                pure (p.1, postEncFSMulti (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
                  (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
                  (prngUp := prngUp) (fsInitSender := fsInitSender)
                  (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
                  (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
                  (lam := lam) (defaultE := defaultE)
                  (esEnc
                    (fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR)
                      (K := K) (M := M) (E := E))
                    (fsMultiHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (SS := SS)
                      (RS := RS) (M := M)) es)
                  ((ckaSMCodec KC Γ CCoins T I KR RSt K SS RS M E).qenc t_sm) p.2)) := by
          refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨rOut, s₁⟩ hp => ?_
          have hImg : ((ckaSMCodec KC Γ CCoins T I KR RSt K SS RS M E).rdec t_sm rOut, s₁) ∈
              support ((fun p => ((ckaSMCodec KC Γ CCoins T I KR RSt K SS RS M E).rdec t_sm p.1, p.2)) <$>
                (implEC (hooksFSMultiC (sampKR := sampKR) (sampKC := sampKC)
                  (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
                  L B Δcka mo false la) L (2 + Δcka) qep fs.maxSkip
                  (modeCfgEC OO mo) mo.policy .v0 .v1).eval ρ₀) := by
            rw [support_map, Set.mem_image]
            exact ⟨(rOut, s₁), hp, rfl⟩
          rw [hStepCore', support_map, Set.mem_image] at hImg
          obtain ⟨⟨u', es₁⟩, _, hEq⟩ := hImg
          have hs₁ : s₁ = esEnc
              (fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (K := K)
                (M := M) (E := E))
              (fsMultiHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (SS := SS)
                (RS := RS) (M := M)) es₁ := (Prod.mk.inj hEq).2.symm
          subst hs₁
          change pure (rOut, (postHandleFalseE (Γ' := []) (ckaInitA := ckaInitA)
              (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
              (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
              (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
              (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
              (lam := lam) (defaultE := defaultE)).eval (Env.cons (rOut, _) ρ₀)) =
            pure (rOut, _)
          refine congrArg (fun x => pure (rOut, x)) ?_
          rw [hPostEval es₁, hρ₀]
          unfold postShallowFSMulti
          exact postHandleFalseE_eval heqT rOut .nil es es₁ t_sm
        have hStepR :
            (implEMultiStage2 cka prng fs Δcka qep false la tL t (.inr t_sm)).run es =
              Prod.map id (postShallowFSMulti es t_sm) <$>
                (implE (hooksFSMulti cka prng fs Δcka mo false la)
                  (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy (.inr t_sm)).run es := by
          unfold implEMultiStage2
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [StateT.run_bind, StateT.run_get, pure_bind]
          dsimp only
          rw [StateT.run_bind, map_eq_bind_pure_comp]
          refine bind_congr fun ⟨u, es₁⟩ => ?_
          rw [StateT.run_bind, StateT.run_get, pure_bind]
          rcases t_sm with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, hdr, e⟩) | ⟨P, hdr, e⟩) | P <;>
            (dsimp only [Function.comp_def, Prod.map, id, postShallowFSMulti]
             split_ifs
             · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
             · simp only [StateT.run_pure])
        have hStep :
            ((handlerImpl (C := prngSMCodec KC Γ CCoins T I KR RSt K SS RS M E)
              (handleMultiStage2EC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
                (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
                (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
                (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
                (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
                (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
                (sampI := sampI) (sampK := sampK) L B Δcka qep fs.maxSkip false la tL t))
              (.inr t_sm)).run
              (esEnc
                (fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (K := K)
                  (M := M) (E := E))
                (fsMultiHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (SS := SS)
                  (RS := RS) (M := M)) es) =
            Prod.map id
              (esEnc
                (fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (K := K)
                  (M := M) (E := E))
                (fsMultiHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (SS := SS)
                  (RS := RS) (M := M))) <$>
              (implEMultiStage2 cka prng fs Δcka qep false la tL t (.inr t_sm)).run es := by
          have hVpEq : esEnc
              (fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (K := K)
                (M := M) (E := E))
              (fsMultiHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (SS := SS)
                (RS := RS) (M := M)) es =
            esEnc vpE
              (fsMultiHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (SS := SS)
                (RS := RS) (M := M)) es := rfl
          rw [hHdlEq, hStepR, hVpEq]
          dsimp only [handlerImpl, StateT.run_mk, prngSMCodec]
          change (((implEC (hooksFSMultiC (sampKR := sampKR) (sampKC := sampKC)
                  (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
                  L B Δcka mo false la) L (2 + Δcka) qep fs.maxSkip
                  (modeCfgEC OO mo) mo.policy .v0 .v1).eval ρ₀ >>=
                fun p => (Comp.ret (I := IIM) (.pair (.fst .v0)
                  (postHandleFalseE (Γ' := []) (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
                    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
                    (prngUp := prngUp) (fsInitSender := fsInitSender)
                    (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
                    (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
                    (lam := lam) (defaultE := defaultE)))).eval
                  (Env.cons p ρ₀)) >>=
              fun q => pure ((ckaSMCodec KC Γ CCoins T I KR RSt K SS RS M E).rdec t_sm q.1, q.2)) = _
          rw [bind_pure_rdec_eq_map, hBindEq, map_rdec_bind_post, hStepCore',
            map_post_map_enc _ _ _ _ hPostEval]
        have hPostInv : ∀ u es₁,
            (u, es₁) ∈ support ((implE (hooksFSMulti cka prng fs Δcka mo false la)
              (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy (.inr t_sm)).run es) →
            FSMultiEngineInv L B_q m (postShallowFSMulti es t_sm es₁) := by
          intro u es₁ hmem₁
          have hInv₁ := implE_fsMulti_inv cka prng fs mo.cfg mo.policy Δcka mo false la
            es t_sm hInv (u, es₁) hmem₁
          dsimp only [postShallowFSMulti]
          split_ifs
          · exact ⟨SMEngineInv.of_lists_eq hInv₁.sm rfl rfl rfl rfl rfl,
              hInv₁.table_le, hInv₁.sessions_le, hInv₁.fsTrans_le,
              hInv₁.tcur_le, hInv₁.vR_none_of_gt⟩
          · exact hInv₁
        rw [hStep, bind_map_left, map_bind]
        refine ⟨OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es₂⟩ hmem => ?_, ?_⟩
        · rw [hStepR, support_map, Set.mem_image] at hmem
          obtain ⟨⟨u', es₁⟩, hmem₁, hEq⟩ := hmem
          simp only [Prod.map, id, Prod.mk.injEq] at hEq
          rcases hEq with ⟨rfl, rfl⟩
          exact (ih u' (hqm u') (postShallowFSMulti es t_sm es₁) (hPostInv u' es₁ hmem₁)).1
        · intro res hmem
          rw [mem_support_bind_iff] at hmem
          obtain ⟨⟨u, es₂⟩, hmem₁, hmem₂⟩ := hmem
          rw [hStepR, support_map, Set.mem_image] at hmem₁
          obtain ⟨⟨u', es₁⟩, hmem₁', hEq⟩ := hmem₁
          simp only [Prod.map, id, Prod.mk.injEq] at hEq
          rcases hEq with ⟨rfl, rfl⟩
          exact (ih u' (hqm u') (postShallowFSMulti es t_sm es₁) (hPostInv u' es₁ hmem₁')).2 res hmem₂

end MultiStage2EvalHelpers

theorem redFSAuthMultiStage2Prog_eval_clamp
    {ckaInitA : KC → Γ} {ckaInitB : KC → Γ}
    {ckaSend : Γ → CCoins → Γ × T × I} {ckaReceive : Γ → T → Γ × I}
    {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
    {fsInitSender : K → SS} {fsInitReceiver : K → RS}
    {fsSend : SS → Header T → M → SS × E}
    {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
    {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
    {lam : I} {defaultE : E}
    {sampKR : ProbComp KR} {sampKC : ProbComp KC} {sampCCoins : ProbComp CCoins}
    {sampI : ProbComp I} {sampK : ProbComp K}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B B_q Δcka qep : ℕ) (gMain la : Bool) (tL : Option ℕ) (t : ℕ)
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
    (heqI : eqI = (· == ·))
    (heqM : eqM = (· == ·))
    (heqE : eqE = (· == ·))
    (hDefaultE : defaultE = default)
    (hSampKR : sampKR = ($ᵗ KR : ProbComp KR))
    (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hSampI : sampI = ($ᵗ I : ProbComp I))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : SchemeAdversary Γ T RSt SS RS M CCoins E) (qAdv : ℕ)
    (hA : MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q) :
    (redFSAuthMultiStage2Prog (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L B Δcka qep fs.maxSkip gMain la tL t).eval (fun _ => A) () =
      redFSAuthMultiStage2 cka prng (fsClamp B fs) lam Δcka qep gMain la tL t A := by
  have hA' : A.IsQueryBoundP
      (isGameQuery (G := SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) qAdv := by
    refine hA.of_imp (fun x hx => ?_)
    rcases x with _ | _ <;> simp_all [isGameQuery]
  have hInit := initFSMultiEStateC_eval (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (sampCCoins := sampCCoins)
    cka prng (fsClamp B fs) hInitA hInitB hPrngInit hPrngUp hFsInitS hFsInitR heqI
    hSampKR hSampKC hSampI hSampK L ⟨true, tL, t⟩ (.bool false)
    (Env.cons (t := (.unit : Ty S)) () .nil)
  unfold CostedReduction.eval redFSAuthMultiStage2Prog CostedReduction.impl redFSAuthMultiStage2
  dsimp only
  rw [eval_bind, hInit]
  simp only [bind_map_left, eval_ret, Expr.eval, Expr.v0, Env.get_cons_zero,
    bind_assoc, pure_bind]
  refine OracleComp.bind_congr_of_forall_mem_support
    (initFSMultiRaw cka prng (fsClamp B fs) lam ⟨true, tL, t⟩ false) fun es₀ hes₀ => ?_
  have ⟨hInv₀, _⟩ := initFSMultiRaw_inv cka prng (fsClamp B fs) lam ⟨true, tL, t⟩ false
    hqB hB1 hBB es₀ hes₀
  have hms : (fsClamp B fs).maxSkip = fs.maxSkip := rfl
  have ⟨hSim, hSimInv⟩ := simulateQ_implEMultiStage2_eq
    (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (prngInit := prngInit)
    (fsReceive := fsReceive) (lam := lam) (sampKR := sampKR) (sampKC := sampKC)
    cka prng (fsClamp B fs) L B B_q Δcka qep gMain la tL t
    hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend
    heqT heqI heqM heqE hDefaultE hSampCCoins hSampI hSampK
    (fun rs hdr e => by simp [fsClamp, hFsRecv]) hA' es₀ hInv₀
  rw [hms] at hSim
  change (do
      let x ←
        (simulateQ (handlerImpl (C := prngSMCodec KC Γ CCoins T I KR RSt K SS RS M E)
          (handleMultiStage2EC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
            (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
            (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
            (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
            (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
            (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
            (sampI := sampI) (sampK := sampK) L B Δcka qep fs.maxSkip gMain la tL t)) A).run _
      _) = _
  rw [hSim, bind_map_left]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨b', es'⟩ hes' => ?_
  have hInv' := hSimInv (b', es') hes'
  let sEnc' := esEnc
    (fsMultiVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (K := K)
      (M := M) (E := E))
    (fsMultiHsEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (KR := KR) (SS := SS) (RS := RS)
      (M := M)) es'
  let ρFin := Env.cons (t := fsMultiEsTy KC Γ CCoins T I KR RSt K SS RS M E) sEnc'
    (Env.cons (t := (.bool : Ty S)) b' .nil)
  have hFin := finishFSMultiE_eval
    (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    L B_q (2 + Δcka) (⟨true, tL, t⟩ : Mode).policy la .v0
    ρFin es' hInv'.sm rfl
  dsimp only [Prod.map, id, Comp.eval]
  exact congrArg pure hFin


def FSVROkMultiStep {K MK : Type} (maxSkip k : ℕ) :
    (FSAEAD.RatchetReceiverState K MK ⊕ ℕ) → Prop
  | .inl rs => RSReach maxSkip k rs
  | .inr _ => True

theorem FSVROkMultiStep.mono {K MK : Type} {maxSkip k k' : ℕ} (hk : k ≤ k')
    {v : FSAEAD.RatchetReceiverState K MK ⊕ ℕ} (hv : FSVROkMultiStep maxSkip k v) :
    FSVROkMultiStep maxSkip k' v := by
  cases v with
  | inl rs => exact RSReach.mono hk hv
  | inr _ => trivial

private theorem hooksFSMulti_startRecv_step {MK C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    (ctx : Ctx Γ T RSt (FSAEAD.RatchetSenderState K ⊕ ℕ)
      (FSAEAD.RatchetReceiverState K MK ⊕ ℕ) M (ℕ × C))
    (P : Party) (t : ℕ) (γ : Γ) (σ : RSt) (Tn : T)
    (h : FSMultiState T RSt K I (ℕ × C)) (res)
    (hmem : res ∈ support
      (((hooksFSMulti cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo gMain la).startRecv
          ctx P t γ σ Tn).run h))
    (γ' : Γ) (σ' : RSt) (rsv : FSAEAD.RatchetReceiverState K MK ⊕ ℕ)
    (hEq : res.1 = some (some (γ', σ', rsv))) :
    FSVROkMultiStep maxSkip 0 rsv := by
  rcases res with ⟨ans, h'⟩
  dsimp only at hEq
  subst hEq
  unfold hooksFSMulti at hmem; dsimp only at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  have hNonHon :
      (some (some (γ', σ', rsv)), h') ∈ support
        ((if gMain = true then pure (some none)
          else if (mo.auth && decide (t = mo.tStar)) = true then
            if (mo.tL.isSome && decide (mo.tStar = mo.tH)) = true then pure none
            else do
              let _ ← lookupMultiF (cka.receive γ Tn).2
              let sIdx ← regSessMulti (cka.receive γ Tn).2
              pure (some (some ((cka.receive γ Tn).1, (prng.up σ (cka.receive γ Tn).2).1,
                Sum.inr sIdx)))
          else pure (some none) :
          HM (FSMultiSpec (FSAEAD.RatchetSenderState K) (FSAEAD.RatchetReceiverState K MK)
            T M (ℕ × C)) _ _).run h) →
      FSVROkMultiStep maxSkip 0 rsv := by
    intro hmem'
    cases gMain
    · simp only [Bool.false_eq_true, ↓reduceIte] at hmem'
      by_cases hc1 : (mo.auth && decide (t = mo.tStar)) = true
      · simp only [hc1, ↓reduceIte] at hmem'
        by_cases hc2 : (mo.tL.isSome && decide (mo.tStar = mo.tH)) = true
        · simp [hc2] at hmem'
        · simp only [hc2, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_pure,
            mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
            Option.some.injEq] at hmem'
          obtain ⟨_, _, ⟨sIdx, _⟩, _, ⟨_, _, hrsv⟩, _⟩ := hmem'
          subst hrsv
          trivial
      · simp [hc1] at hmem'
    · simp at hmem'
  rcases hcache : h.cache t with _ | ⟨Tc, σc, k, optIdx⟩
  · simp only [hcache] at hmem; exact hNonHon hmem
  · by_cases hTc : Tc = Tn
    · simp only [hcache, hTc, ↓reduceIte, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at hmem
      rcases hmem with ⟨⟨_, _, hrsv⟩, _⟩
      subst hrsv
      rcases optIdx with _ | sIdx
      · exact RSReach.init ae G maxSkip k
      · trivial
    · simp only [hcache, hTc, ↓reduceIte] at hmem; exact hNonHon hmem

private theorem vRecvStep1_hooksFSMulti_vrOk {MK C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip k Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    (ctx : Ctx Γ T RSt (FSAEAD.RatchetSenderState K ⊕ ℕ)
      (FSAEAD.RatchetReceiverState K MK ⊕ ℕ) M (ℕ × C))
    (P : Party)
    (s : VP Γ T RSt (FSAEAD.RatchetSenderState K ⊕ ℕ)
      (FSAEAD.RatchetReceiverState K MK ⊕ ℕ))
    (c : Header T × (ℕ × C))
    (h : FSMultiState T RSt K I (ℕ × C))
    (hVR : ∀ t v, s.vR t = some v → FSVROkMultiStep maxSkip k v) :
    ∀ res ∈ support
      ((vRecvStep1 (hooksFSMulti cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo gMain la)
          ctx P s c).run h),
      ∀ s₁, res.1 = some (some s₁) → ∀ t v, s₁.vR t = some v → FSVROkMultiStep maxSkip k v := by
  intro ⟨s₁?, h₁⟩ hmem s₁ hs₁ t₀ v₀ hv₀
  unfold vRecvStep1 at hmem
  by_cases ht : c.1.1 = s.tcur + 1
  · simp only [ht, ↓reduceIte] at hmem
    rcases hTn : c.1.2 with _ | Tn
    · simp only [hTn, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, _⟩; cases hs₁
    · simp only [hTn, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨srRes, h'⟩, hsr, hmem⟩ := hmem
      rcases srRes with _ | _ | ⟨γ', σ', rs⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, _⟩; cases hs₁
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, _⟩; cases hs₁
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩
        cases hs₁
        by_cases ht₀ : t₀ = s.tcur + 1
        · subst ht₀
          simp only [Function.update_self, Option.some.injEq] at hv₀
          subst hv₀
          exact (hooksFSMulti_startRecv_step cka prng ae G maxSkip Δcka mo gMain la
            ctx P (s.tcur + 1) s.γ s.root Tn h
            (some (some (γ', σ', rs)), h₁) hsr γ' σ' rs rfl).mono (Nat.zero_le k)
        · simp only [Function.update_of_ne ht₀] at hv₀
          exact hVR t₀ v₀ hv₀
  · simp only [ht, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, _⟩
    cases hs₁
    exact hVR t₀ v₀ hv₀

private theorem hooksFSMulti_fsRecv_fsClamp_eq {MK C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip B k Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    (hB : (k + 1) * (maxSkip + 1) ≤ B)
    (ctx : Ctx Γ T RSt (FSAEAD.RatchetSenderState K ⊕ ℕ)
      (FSAEAD.RatchetReceiverState K MK ⊕ ℕ) M (ℕ × C))
    (P : Party) (t : ℕ) (rsv : FSAEAD.RatchetReceiverState K MK ⊕ ℕ)
    (hdr : Header T) (e : ℕ × C) (rec_ : Option (Record M (Header T × (ℕ × C))))
    (h : FSMultiState T RSt K I (ℕ × C))
    (hVR : FSVROkMultiStep maxSkip k rsv) :
    ((hooksFSMulti cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip)) Δcka mo gMain la).fsRecv
        ctx P t rsv hdr e rec_).run h =
      ((hooksFSMulti cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo gMain la).fsRecv
        ctx P t rsv hdr e rec_).run h := by
  dsimp only [hooksFSMulti]
  rcases rsv with rs | sIdx
  · dsimp only
    rw [fsClamp_receive_fromAEADPRG ae G maxSkip B k hB hVR hdr e]
  · rfl

theorem vRecv_fsClamp_multi_eq {MK C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip B k Δcka : ℕ) (mo : Mode) (gMain la : Bool)
    (hB : (k + 1) * (maxSkip + 1) ≤ B)
    (ctx : Ctx Γ T RSt (FSAEAD.RatchetSenderState K ⊕ ℕ)
      (FSAEAD.RatchetReceiverState K MK ⊕ ℕ) M (ℕ × C))
    (P : Party)
    (s : VP Γ T RSt (FSAEAD.RatchetSenderState K ⊕ ℕ)
      (FSAEAD.RatchetReceiverState K MK ⊕ ℕ))
    (c : Header T × (ℕ × C)) (rec_ : Option (Record M (Header T × (ℕ × C))))
    (h : FSMultiState T RSt K I (ℕ × C))
    (hVR : ∀ t v, s.vR t = some v → FSVROkMultiStep maxSkip k v) :
    (vRecv (hooksFSMulti cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip)) Δcka mo gMain la)
        ctx P s c rec_).run h =
      (vRecv (hooksFSMulti cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo gMain la)
        ctx P s c rec_).run h := by
  rw [vRecv_eq_bind, vRecv_eq_bind]
  by_cases href : (s.id.sendsIn c.1.1 || decide (s.tcur + 1 < c.1.1))
  · simp [href]
  · simp only [href, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
    have hStep1 :
        vRecvStep1
          (hooksFSMulti cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip)) Δcka mo gMain la)
          ctx P s c =
        vRecvStep1
          (hooksFSMulti cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo gMain la)
          ctx P s c := rfl
    rw [hStep1]
    refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨s₁?, h₁⟩ hmem => ?_
    have hVR₁ := vRecvStep1_hooksFSMulti_vrOk cka prng ae G maxSkip k Δcka mo gMain la
      ctx P s c h hVR (s₁?, h₁) hmem
    rcases s₁? with _ | (_ | s₁)
    · rfl
    · rfl
    · rcases hvRc : s₁.vR c.1.1 with _ | v
      · simp only [hvRc]
      · simp only [hvRc, StateT.run_bind]
        rw [hooksFSMulti_fsRecv_fsClamp_eq cka prng ae G maxSkip B k Δcka mo gMain la hB
          ctx P c.1.1 v c.1 c.2 rec_ h₁ (hVR₁ s₁ rfl c.1.1 v hvRc)]

theorem hooksFSMulti_vrInv_fromAEADPRG {MK C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip Δcka : ℕ) (mo : Mode) (gMain la : Bool) :
    HooksVRInv (FSVROkMultiStep maxSkip)
      (hooksFSMulti cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo gMain la) where
  mono hle hv := hv.mono hle
  startRecv_step := hooksFSMulti_startRecv_step cka prng ae G maxSkip Δcka mo gMain la
  fsRecv_step _ _ _ rsv hdr e rec_ h res hVR hmem v' i' m' hEq := by
    rcases res with ⟨ans, h'⟩
    dsimp only at hEq
    subst hEq
    unfold hooksFSMulti at hmem; dsimp only at hmem
    rcases rsv with rs | sIdx
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq, Option.some.injEq] at hmem
      rcases hmem with ⟨hmap, _⟩
      rcases hrc : (FSAEAD.fromAEADPRG ae G maxSkip).receive rs hdr e with _ | ⟨rs', i, m⟩
      · simp [hrc] at hmap
      · simp only [hrc, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hmap
        rcases hmap with ⟨rfl, rfl, rfl⟩
        exact (RSReach.receive ae G maxSkip _ hVR hrc).2
    · simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
      split_ifs at hmem <;>
        (simp only [StateT.run_bind, mem_support_bind_iff] at hmem;
         obtain ⟨⟨qres, h₁⟩, _, hmem⟩ := hmem;
         rcases qres with _ | (_ | ⟨i, mo'⟩);
         · simp at hmem;
         · simp at hmem;
         · dsimp only at hmem;
           split_ifs at hmem;
           · simp [StateT.run_modify] at hmem;
           · simp only [StateT.run_bind, StateT.run_modify, pure_bind] at hmem;
             rcases mo' with _ | m;
             · rcases rec_ with _ | r;
               · simp at hmem;
               · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
                   Prod.mk.injEq, Option.some.injEq] at hmem;
                 rcases hmem with ⟨⟨rfl, _, _⟩, _⟩; trivial;
             · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
                 Prod.mk.injEq, Option.some.injEq] at hmem;
               rcases hmem with ⟨⟨rfl, _, _⟩, _⟩; trivial)
  commit_vR _ _ _ _ _ _ hmem _ hEq := by
    simp only [hooksFSMulti, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; cases hEq; rfl

private theorem implE_fsClamp_multi_eq {MK C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip B B_q q Δcka qep : ℕ)
    (mo : Mode) (gMain la : Bool)
    (hB : (B_q + 1) * (maxSkip + 1) ≤ B)
    (es : EState (VP Γ T RSt (FSAEAD.RatchetSenderState K ⊕ ℕ)
      (FSAEAD.RatchetReceiverState K MK ⊕ ℕ)) M (Header T × (ℕ × C))
      (FSMultiState T RSt K I (ℕ × C)))
    (t : (SM.spec (PartyState Γ T RSt (FSAEAD.RatchetSenderState K)
      (FSAEAD.RatchetReceiverState K MK)) M CCoins (Header T × (ℕ × C))).Domain)
    (hVR : SMVRInv (FSVROkMultiStep maxSkip) B_q (q + 1) es.g) :
    (implE (hooksFSMulti cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip)) Δcka mo gMain la)
        (2 + Δcka) qep maxSkip mo.cfg mo.policy (.inr t)).run es =
      (implE (hooksFSMulti cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo gMain la)
        (2 + Δcka) qep maxSkip mo.cfg mo.policy (.inr t)).run es := by
  have hkB : (B_q - (q + 1) + 1) * (maxSkip + 1) ≤ B :=
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.sub_le _ _) 1)).trans hB
  rcases t with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
  · change (transmitE _ _ _ _ (P, m, r)).run es = (transmitE _ _ _ _ (P, m, r)).run es
    unfold transmitE vSend hooksFSMulti fsClamp
    rfl
  · change (challE _ _ _ _ _ (P, m₀, m₁, r)).run es =
      (challE _ _ _ _ _ (P, m₀, m₁, r)).run es
    unfold challE vSend hooksFSMulti fsClamp
    rfl
  · change (deliverE _ maxSkip mo.cfg (P, c)).run es = (deliverE _ maxSkip mo.cfg (P, c)).run es
    unfold deliverE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win)
    · simp [hab]
    · simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases htr : es.g.inTransit P.other c with _ | r
      · rfl
      · simp only [run_liftH_bind]
        rw [vRecv_fsClamp_multi_eq cka prng ae G maxSkip B (B_q - (q + 1)) Δcka mo gMain la hkB
          es.g P (es.g.st P) c (some r) es.h (hVR P)]
        rfl
  · change (injectE _ (2 + Δcka) qep mo.cfg (P, c)).run es =
      (injectE _ (2 + Δcka) qep mo.cfg (P, c)).run es
    unfold injectE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases href :
        (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj (2 + Δcka)))
    · simp [href]
    · simp only [href, Bool.false_eq_true, ↓reduceIte, run_liftH_bind]
      rw [vRecv_fsClamp_multi_eq cka prng ae G maxSkip B (B_q - (q + 1)) Δcka mo gMain la hkB
        es.g P (es.g.st P) c none es.h (hVR P)]
      rfl
  · change (corrE _ mo.policy P).run es = (corrE _ mo.policy P).run es
    unfold corrE hooksFSMulti fsClamp
    rfl

private theorem implE_inl_eq {ι : Type} {Spec : OracleSpec.{0, 0} ι}
    {H Γ' T' RSt' VS VR M' E' CCoins' IG IS SS' RS' : Type}
    [DecidableEq T'] [DecidableEq M'] [DecidableEq E'] [Inhabited E']
    (hk : Hooks Spec H Γ' T' RSt' SS' RS' M' E' CCoins' IG IS VS VR)
    (Δ qep maxSkip : ℕ) (cfg : Config M') (π : Policy) (n : ℕ) :
    implE hk Δ qep maxSkip cfg π (.inl n) = coinsE n := rfl

private theorem implEMultiStage2_inl_run_eq
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (gMain la : Bool) (tL : Option ℕ) (t n : ℕ)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E)
      (FSMultiState T RSt K I E)) :
    (implEMultiStage2 cka prng fs Δcka qep gMain la tL t (.inl n)).run es =
      (fun u => (u, es)) <$>
        query (spec := unifSpec + FSMultiSpec SS RS T M E) (.inl n) := by
  cases gMain
  · simp only [implEMultiStage2, Bool.false_eq_true, ↓reduceIte, implE_inl_eq,
      StateT.run_bind, StateT.run_get, pure_bind, coinsE, StateT.run_lift,
      bind_assoc, Bool.and_false, StateT.run_pure, map_eq_bind_pure_comp, Function.comp_def]; rfl
  · simp only [implEMultiStage2, ↓reduceIte, implE_inl_eq, coinsE, StateT.run_lift,
      map_eq_bind_pure_comp, Function.comp_def]; rfl

private theorem simulateQ_implEMultiStage2_fsClamp_eq {MK C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip L B B_q Δcka qep : ℕ)
    (gMain la : Bool) (tL : Option ℕ) (t : ℕ)
    (hB : (B_q + 1) * (maxSkip + 1) ≤ B)
    {α : Type} {oa : OracleComp (unifSpec + SM.spec
      (PartyState Γ T RSt (FSAEAD.RatchetSenderState K) (FSAEAD.RatchetReceiverState K MK))
      M CCoins (Header T × (ℕ × C))) α}
    {q : ℕ}
    (hoa : oa.IsQueryBoundP
      (isGameQuery (G := SM.spec
        (PartyState Γ T RSt (FSAEAD.RatchetSenderState K) (FSAEAD.RatchetReceiverState K MK))
        M CCoins (Header T × (ℕ × C)))) q)
    (es : EState (VP Γ T RSt (FSAEAD.RatchetSenderState K ⊕ ℕ)
      (FSAEAD.RatchetReceiverState K MK ⊕ ℕ)) M (Header T × (ℕ × C))
      (FSMultiState T RSt K I (ℕ × C)))
    (hInv : SMEngineInv L B_q q es.g)
    (hVR : SMVRInv (FSVROkMultiStep maxSkip) B_q q es.g) :
    (simulateQ (implEMultiStage2 cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip))
        Δcka qep gMain la tL t) oa).run es =
      (simulateQ (implEMultiStage2 cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
        Δcka qep gMain la tL t) oa).run es := by
  induction oa using OracleComp.inductionOn generalizing q es with
  | pure x => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind qy mx ih =>
    rw [isQueryBoundP_query_bind_iff] at hoa
    rcases hoa with ⟨hq0, hmx⟩
    rw [simulateQ_query_bind, simulateQ_query_bind, StateT.run_bind, StateT.run_bind]
    have hLift : ∀ {M' : Type → Type} [Monad M'] {σ' α' : Type} (m : StateT σ' M' α') (s : σ'),
        (liftM m : StateT σ' M' α').run s = m.run s := fun _ _ => rfl
    rw [hLift, hLift]
    simp only [OracleQuery.input_query, OracleQuery.cont_query]
    rcases qy with n | t_sm
    · rw [implEMultiStage2_inl_run_eq, implEMultiStage2_inl_run_eq, bind_map_left, bind_map_left]
      exact bind_congr fun u => ih u (hmx u) es hInv hVR
    · have hqp : 0 < q := hq0.resolve_left (by simp [isGameQuery])
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      have hStep :
          (implEMultiStage2 cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip))
              Δcka qep gMain la tL t (.inr t_sm)).run es =
            (implEMultiStage2 cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
              Δcka qep gMain la tL t (.inr t_sm)).run es := by
        cases gMain
        · simp only [implEMultiStage2, Bool.false_eq_true, ↓reduceIte,
            StateT.run_bind, StateT.run_get, pure_bind]
          have h1 := implE_fsClamp_multi_eq cka prng ae G maxSkip B B_q q' Δcka qep
            ⟨true, tL, t⟩ false la hB es t_sm hVR
          change ((implE _ (2 + Δcka) qep maxSkip _ _ (.inr t_sm)).run es >>= _) =
            ((implE _ (2 + Δcka) qep maxSkip _ _ (.inr t_sm)).run es >>= _)
          rw [h1]
        · simp only [implEMultiStage2, ↓reduceIte]
          exact implE_fsClamp_multi_eq cka prng ae G maxSkip B B_q q' Δcka qep
            ⟨true, tL, t⟩ true la hB es t_sm hVR
      rw [hStep]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es'⟩ hmem => ?_
      have ⟨hInv', hVR'⟩ :
          SMEngineInv L B_q q' es'.g ∧ SMVRInv (FSVROkMultiStep maxSkip) B_q q' es'.g := by
        cases gMain
        · simp only [implEMultiStage2, Bool.false_eq_true, ↓reduceIte,
            StateT.run_bind, StateT.run_get, pure_bind, mem_support_bind_iff] at hmem
          obtain ⟨⟨u₁, es₁⟩, hmem₁, hmem₂⟩ := hmem
          have hInv₁ := implE_inv
            (hooksFSMulti cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka ⟨true, tL, t⟩ false la)
            (⟨true, tL, t⟩ : Mode).cfg (⟨true, tL, t⟩ : Mode).policy es t_sm hInv (u₁, es₁) hmem₁
          have hVR₁ := implE_vrInv
            (hooksFSMulti cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka ⟨true, tL, t⟩ false la)
            (hooksFSMulti_vrInv_fromAEADPRG cka prng ae G maxSkip Δcka ⟨true, tL, t⟩ false la)
            (⟨true, tL, t⟩ : Mode).cfg (⟨true, tL, t⟩ : Mode).policy es t_sm hInv hVR (u₁, es₁) hmem₁
          split_ifs at hmem₂
          · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem₂
            rcases hmem₂ with ⟨_, rfl⟩
            exact ⟨⟨hInv₁.trans_le, hInv₁.chall_le, hInv₁.leaks_le, hInv₁.corrs_le,
              hInv₁.comp_u, hInv₁.b_succ_le, hInv₁.bb_le⟩, hVR₁⟩
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem₂
            rcases hmem₂ with ⟨_, rfl⟩
            exact ⟨hInv₁, hVR₁⟩
        · simp only [implEMultiStage2, ↓reduceIte] at hmem
          exact ⟨implE_inv
              (hooksFSMulti cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka ⟨true, tL, t⟩ true la)
              (⟨true, tL, t⟩ : Mode).cfg (⟨true, tL, t⟩ : Mode).policy es t_sm hInv (u, es') hmem,
            implE_vrInv
              (hooksFSMulti cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka ⟨true, tL, t⟩ true la)
              (hooksFSMulti_vrInv_fromAEADPRG cka prng ae G maxSkip Δcka ⟨true, tL, t⟩ true la)
              (⟨true, tL, t⟩ : Mode).cfg (⟨true, tL, t⟩ : Mode).policy es t_sm hInv hVR (u, es') hmem⟩
      exact ih u (hmx u) es' hInv' hVR'

theorem redFSAuthMultiStage2_fsClamp_fromAEADPRG {MK C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip L B B_q Δcka qep : ℕ)
    (lam : I) (gMain la : Bool) (tL : Option ℕ) (t : ℕ)
    (hFsB : (B_q + 1) * (maxSkip + 1) ≤ B)
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : SchemeAdversary Γ T RSt (FSAEAD.RatchetSenderState K)
      (FSAEAD.RatchetReceiverState K MK) M CCoins (ℕ × C)) (qAdv : ℕ)
    (hA : MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q) :
    redFSAuthMultiStage2 cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip))
        lam Δcka qep gMain la tL t A =
      redFSAuthMultiStage2 cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
        lam Δcka qep gMain la tL t A := by
  have hA' : A.IsQueryBoundP
      (isGameQuery (G := SM.spec
        (PartyState Γ T RSt (FSAEAD.RatchetSenderState K) (FSAEAD.RatchetReceiverState K MK))
        M CCoins (Header T × (ℕ × C)))) qAdv := by
    refine hA.of_imp (fun x hx => ?_)
    rcases x with _ | _ <;> simp_all [isGameQuery]
  unfold redFSAuthMultiStage2
  have hInitEq :
      initFSMultiRaw cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip)) lam ⟨true, tL, t⟩ false =
        initFSMultiRaw cka prng (FSAEAD.fromAEADPRG ae G maxSkip) lam ⟨true, tL, t⟩ false := rfl
  rw [hInitEq]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun es₀ hes₀ => ?_
  have ⟨hInv₀, hVR₀⟩ :
      SMEngineInv L B_q qAdv es₀.g ∧ SMVRInv (FSVROkMultiStep maxSkip) B_q qAdv es₀.g := by
    unfold initFSMultiRaw at hes₀
    rw [mem_support_bind_iff] at hes₀; obtain ⟨kr, _, hes₀⟩ := hes₀
    rw [mem_support_bind_iff] at hes₀; obtain ⟨kc, _, hes₀⟩ := hes₀
    rw [mem_support_bind_iff] at hes₀; obtain ⟨⟨⟨σ, k, sid⟩, h₁⟩, _, hes₀⟩ := hes₀
    rw [mem_support_bind_iff] at hes₀; obtain ⟨⟨optIdx, h₂⟩, _, hes₀⟩ := hes₀
    simp only [support_pure, Set.mem_singleton_iff] at hes₀
    subst hes₀
    refine ⟨(SMEngineInv.init _ false hB1 hBB).mono hqB, fun P t₀ v hv => ?_⟩
    cases P <;> simp only [mkParties] at hv
    · by_cases ht0 : t₀ = 0
      · simp only [ht0, ↓reduceIte, Option.some.injEq] at hv
        subst hv
        rcases optIdx with _ | sIdx
        · exact (RSReach.init ae G maxSkip k).mono (Nat.zero_le _)
        · trivial
      · simp [ht0] at hv
    · cases hv
  rw [simulateQ_implEMultiStage2_fsClamp_eq cka prng ae G maxSkip L B B_q Δcka qep
    gMain la tL t hFsB hA' es₀ hInv₀ hVR₀]

/-- Evaluation bridge for `redFSAuthMultiStage2Prog` instantiated with `FSAEAD.fromAEADPRG`. -/
theorem redFSAuthMultiStage2Prog_eval_fromAEADPRG {MK C : Type}
    {ckaInitA : KC → Γ} {ckaInitB : KC → Γ}
    {ckaSend : Γ → CCoins → Γ × T × I} {ckaReceive : Γ → T → Γ × I}
    {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
    {fsInitSender : K → FSAEAD.RatchetSenderState K}
    {fsInitReceiver : K → FSAEAD.RatchetReceiverState K MK}
    {fsSend : FSAEAD.RatchetSenderState K → Header T → M →
      FSAEAD.RatchetSenderState K × (ℕ × C)}
    {fsReceive : FSAEAD.RatchetReceiverState K MK → Header T → (ℕ × C) →
      Option (FSAEAD.RatchetReceiverState K MK × ℕ × M)}
    {eqT : T → T → Bool} {eqI : I → I → Bool}
    {eqM : M → M → Bool} {eqE : (ℕ × C) → (ℕ × C) → Bool}
    {lam : I} {defaultE : ℕ × C}
    {sampKR : ProbComp KR} {sampKC : ProbComp KC} {sampCCoins : ProbComp CCoins}
    {sampI : ProbComp I} {sampK : ProbComp K}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip L B B_q Δcka qep : ℕ)
    (gMain la : Bool) (tL : Option ℕ) (t : ℕ)
    (hInitA : ckaInitA = cka.initA)
    (hInitB : ckaInitB = cka.initB)
    (hSend : ckaSend = cka.send)
    (hRecv : ckaReceive = cka.receive)
    (hPrngInit : prngInit = prng.init)
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = (FSAEAD.fromAEADPRG ae G maxSkip).initSender)
    (hFsInitR : fsInitReceiver = (FSAEAD.fromAEADPRG ae G maxSkip).initReceiver)
    (hFsSend : fsSend = (FSAEAD.fromAEADPRG ae G maxSkip).send)
    (hFsRecv : fsReceive = (FSAEAD.fromAEADPRG ae G maxSkip).receive)
    (heqT : eqT = (· == ·))
    (heqI : eqI = (· == ·))
    (heqM : eqM = (· == ·))
    (heqE : eqE = (· == ·))
    (hDefaultE : defaultE = default)
    (hSampKR : sampKR = ($ᵗ KR : ProbComp KR))
    (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hSampI : sampI = ($ᵗ I : ProbComp I))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (hFsB : (B_q + 1) * (maxSkip + 1) ≤ B)
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : SchemeAdversary Γ T RSt (FSAEAD.RatchetSenderState K)
      (FSAEAD.RatchetReceiverState K MK) M CCoins (ℕ × C)) (qAdv : ℕ)
    (hA : MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q) :
    (redFSAuthMultiStage2Prog (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L B Δcka qep maxSkip gMain la tL t).eval (fun _ => A) () =
      redFSAuthMultiStage2 cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
        lam Δcka qep gMain la tL t A := by
  have heqE' : eqE = fun x1 x2 : ℕ × C => @BEq.beq (ℕ × C) instBEqOfDecidableEq x1 x2 := by
    rw [heqE]
    funext ⟨a1, c1⟩ ⟨a2, c2⟩
    by_cases ha : a1 = a2 <;> by_cases hc : c1 = c2 <;> simp [BEq.beq, ha, hc]
  have h1 := redFSAuthMultiStage2Prog_eval_clamp (lam := lam) cka prng
    (FSAEAD.fromAEADPRG ae G maxSkip) L B B_q Δcka qep gMain la tL t
    hInitA hInitB hSend hRecv hPrngInit hPrngUp hFsInitS hFsInitR hFsSend hFsRecv
    heqT heqI heqM heqE' hDefaultE hSampKR hSampKC hSampCCoins hSampI hSampK
    hB1 hBB A qAdv hA hqB
  have hms : (FSAEAD.fromAEADPRG ae G maxSkip).maxSkip = maxSkip := rfl
  rw [hms] at h1
  exact h1.trans (redFSAuthMultiStage2_fsClamp_fromAEADPRG cka prng ae G maxSkip
    L B B_q Δcka qep lam gMain la tL t hFsB hB1 hBB A qAdv hA hqB)

end CryptoGames.SM.Construction

