/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SpecLemmas.Reductions.Primitives.AEAD.CostedTables
import Computational.Proofs.ReductionDsl.Notation

/-!
# `ReductionDsl` programs for Libsignal salt and wire AEAD reductions

Costed `ReductionDsl` witness programs `lSaltRedProg`, `lWireRedProg`, `slotSaltRedProg`, and
`slotWireRedProg` for the single-slot and multi-slot per-message AEAD salt-PRF and wire-OT-CCA
reductions.
-/

@[expose] public section

namespace CryptoGames.Ratchet.LibsignalInst.Costed

open ReductionDsl OracleComp OracleSpec CryptoGames CryptoGames.AEAD.Costed CryptoGames.OTCCA.Costed
  CryptoGames.PRF.Costed CryptoGames.Ratchet CryptoGames.Ratchet.LibsignalInst
  CryptoGames.LibsignalAead CryptoGames.LibsignalSession CryptoGames.SM.Construction
  CryptoGames.MACScheme CryptoGames.HKDF CBC
open scoped Computational.Proofs.ReductionDsl.Notation

local macro_rules
  | `(rdsl_pat| .enc $p:term) => `(rdsl_pat| .inl $p)
  | `(rdsl_pat| .dec $p:term) => `(rdsl_pat| .inr $p)

variable {Pt : Type} [DecidableEq Pt]
  (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey)
  (idOf : Party → IdentityKey) (kAEAD kIdeal : ℕ)

local notation "SWSig" => saltWireSig Pt ℓ
local notation "SWT" => Ty SWSig
local notation "SWOps" => saltWireOps C codec ℓ encT idOf kAEAD
local notation "SaltIface" => saltRedIface C codec ℓ encT kIdeal
local notation "WireIface" => wireRedIface Pt ℓ
local notation "SlotIface" => slotOtccaIface C codec ℓ encT kIdeal
local notation "SlotCodec" => slotOtccaCodec Pt ℓ

/-! ## Pure expression and oracle helpers -/

def orE {Γ : List SWT} (a b : Expr SWOps Γ .bool) : Expr SWOps Γ .bool :=
  .ite a (.bool true) b

def eqBoolE {Γ : List SWT} (a b : Expr SWOps Γ .bool) : Expr SWOps Γ .bool :=
  .ite a b (.not b)

def leE {Γ : List SWT} (a b : Expr SWOps Γ .nat) : Expr SWOps Γ .bool :=
  .not (.lt b a)

def isSomeE {Γ : List SWT} {t : SWT} (e : Expr SWOps Γ (.opt t)) :
    Expr SWOps Γ .bool :=
  .caseOpt e (.bool false) (.bool true)

def encKE {Γ : List SWT}
    (mk : Expr SWOps Γ (.base .msgKey))
    (a : Expr SWOps Γ (slotAdTy Pt ℓ))
    (m : Expr SWOps Γ (.base .plain)) :
    Expr SWOps Γ (lctTy Pt ℓ) :=
  Expr.op (O := SWOps) (Sum.inl OtccaOp.enc) (.pair mk (.pair a m))

def decKE {Γ : List SWT}
    (mk : Expr SWOps Γ (.base .msgKey))
    (a : Expr SWOps Γ (slotAdTy Pt ℓ))
    (e : Expr SWOps Γ (lctTy Pt ℓ)) :
    Expr SWOps Γ (.opt (.base .plain)) :=
  Expr.op (O := SWOps) (Sum.inl OtccaOp.dec) (.pair mk (.pair a e))

def encRE {Γ : List SWT}
    (seed : Expr SWOps Γ (.base .seed))
    (a : Expr SWOps Γ (slotAdTy Pt ℓ))
    (m : Expr SWOps Γ (.base .plain)) :
    Expr SWOps Γ (lctTy Pt ℓ) :=
  Expr.op (O := SWOps) (Sum.inr (Sum.inl OtccaOp.enc)) (.pair seed (.pair a m))

def decRE {Γ : List SWT}
    (seed : Expr SWOps Γ (.base .seed))
    (a : Expr SWOps Γ (slotAdTy Pt ℓ))
    (e : Expr SWOps Γ (lctTy Pt ℓ)) :
    Expr SWOps Γ (.opt (.base .plain)) :=
  Expr.op (O := SWOps) (Sum.inr (Sum.inl OtccaOp.dec)) (.pair seed (.pair a e))

def saltOfE {Γ : List SWT} (a : Expr SWOps Γ (slotAdTy Pt ℓ)) :
    Expr SWOps Γ (.base .salt) :=
  Expr.op (O := SWOps) (Sum.inl OtccaOp.saltOf) a

def eqADE {Γ : List SWT} (a₁ a₂ : Expr SWOps Γ (slotAdTy Pt ℓ)) :
    Expr SWOps Γ .bool :=
  Expr.op (O := SWOps) (Sum.inl OtccaOp.eqAD) (.pair a₁ a₂)

def eqCE {Γ : List SWT} (e₁ e₂ : Expr SWOps Γ (lctTy Pt ℓ)) : Expr SWOps Γ .bool :=
  Expr.op (O := SWOps) (Sum.inl OtccaOp.eqC) (.pair e₁ e₂)

def eqSaltE {Γ : List SWT} (s₁ s₂ : Expr SWOps Γ (.base .salt)) :
    Expr SWOps Γ .bool :=
  Expr.op (O := SWOps) (Sum.inl OtccaOp.eqSalt) (.pair s₁ s₂)

def idsOfE {Γ : List SWT} (a : Expr SWOps Γ (slotAdTy Pt ℓ)) :
    Expr SWOps Γ (.base .idKeys) :=
  Expr.op (O := SWOps) (Sum.inr (Sum.inr WireOp.idsOf)) a

def hdrOfE {Γ : List SWT} (a : Expr SWOps Γ (slotAdTy Pt ℓ)) :
    Expr SWOps Γ (.base .sigHdr) :=
  Expr.op (O := SWOps) (Sum.inr (Sum.inr WireOp.hdrOf)) a

def eqHdrE {Γ : List SWT} (h₁ h₂ : Expr SWOps Γ (.base .sigHdr)) :
    Expr SWOps Γ .bool :=
  Expr.op (O := SWOps) (Sum.inr (Sum.inr WireOp.eqHdr)) (.pair h₁ h₂)

def fitPlainE {Γ : List SWT} (m : Expr SWOps Γ (.base .rawBytes)) :
    Expr SWOps Γ (.base .plain) :=
  Expr.op (O := SWOps) (Sum.inr (Sum.inr WireOp.fitPlainOp)) m

@[reducible] def chalPairTy : SWT :=
  .prod (slotAdTy Pt ℓ) (lctTy Pt ℓ)

@[reducible] def chalOptTy : SWT :=
  .opt (chalPairTy (Pt := Pt) ℓ)

def eqChalSomeE {Γ : List SWT}
    (chal : Expr SWOps Γ (chalOptTy (Pt := Pt) ℓ))
    (a : Expr SWOps (chalPairTy (Pt := Pt) ℓ :: Γ) (slotAdTy Pt ℓ))
    (e : Expr SWOps (chalPairTy (Pt := Pt) ℓ :: Γ) (lctTy Pt ℓ)) :
    Expr SWOps Γ .bool :=
  rdslExpr =>
    match chal with
    | none => false
    | some (ca, ce) =>
      eqADE C codec ℓ encT idOf kAEAD ca (raw a) &&
      eqCE C codec ℓ encT idOf kAEAD ce (raw e)

def isSlotChalSaltE {Γ : List SWT}
    (chal : Expr SWOps Γ (chalOptTy (Pt := Pt) ℓ))
    (salt : Expr SWOps (chalPairTy (Pt := Pt) ℓ :: Γ) (.base .salt)) :
    Expr SWOps Γ .bool :=
  rdslExpr =>
    match chal with
    | none => false
    | some (ca, _) =>
      eqSaltE C codec ℓ encT idOf kAEAD (raw salt) (saltOfE C codec ℓ encT idOf kAEAD ca)

def sampleSaltBoolC {Γ : List SWT} : Comp SWOps SaltIface Γ .bool :=
  Comp.sample (O := SWOps) (I := SaltIface) (Sum.inr UniformSamplerTag.bool) .unit

def sampleSaltIdealC {Γ : List SWT} (a : Expr SWOps Γ (slotAdTy Pt ℓ)) :
    Comp SWOps SaltIface Γ (lctTy Pt ℓ) :=
  Comp.sample (O := SWOps) (I := SaltIface) (Sum.inl (Sum.inr ())) a

def querySaltPrfC {Γ : List SWT} (s : Expr SWOps Γ (.base .salt)) :
    Comp SWOps SaltIface Γ (.base .msgKey) :=
  Comp.query (O := SWOps) (I := SaltIface) () s

def sampleWireBoolC {Γ : List SWT} : Comp SWOps WireIface Γ .bool :=
  Comp.sample (O := SWOps) (I := WireIface) (Sum.inr UniformSamplerTag.bool) .unit

def queryWireEncC {Γ : List SWT}
    (x : Expr SWOps Γ (.prod (.base .idKeys) (.prod (.base .sigHdr) (.base .plain)))) :
    Comp SWOps WireIface Γ (.opt (wireTagTy Pt ℓ)) :=
  Comp.query (O := SWOps) (I := WireIface) WireTag.enc x

def queryWireDecC {Γ : List SWT}
    (x : Expr SWOps Γ (.prod (.base .idKeys) (wireTagTy Pt ℓ))) :
    Comp SWOps WireIface Γ (.opt (.prod (.base .sigHdr) (.base .rawBytes))) :=
  Comp.query (O := SWOps) (I := WireIface) WireTag.dec x

def sampleSlotIdealC {Γ : List SWT} (a : Expr SWOps Γ (slotAdTy Pt ℓ)) :
    Comp SWOps SlotIface Γ (lctTy Pt ℓ) :=
  Comp.sample (O := SWOps) (I := SlotIface) (Sum.inl ()) a

def sampleSlotSeedC {Γ : List SWT} : Comp SWOps SlotIface Γ (.base .seed) :=
  Comp.sample (O := SWOps) (I := SlotIface) (Sum.inr (UniformSamplerTag.base true)) .unit

def sampleSlotMsgKeyC {Γ : List SWT} : Comp SWOps SlotIface Γ (.base .msgKey) :=
  Comp.sample (O := SWOps) (I := SlotIface) (Sum.inr (UniformSamplerTag.base false)) .unit

def querySlotEncC {Γ : List SWT}
    (x : Expr SWOps Γ (.prod (slotAdTy Pt ℓ) (.base .plain))) :
    Comp SWOps SlotIface Γ (.opt (lctTy Pt ℓ)) :=
  Comp.query (O := SWOps) (I := SlotIface) OtccaTag.enc x

def querySlotDecC {Γ : List SWT}
    (x : Expr SWOps Γ (.prod (slotAdTy Pt ℓ) (lctTy Pt ℓ))) :
    Comp SWOps SlotIface Γ (.opt (.base .plain)) :=
  Comp.query (O := SWOps) (I := SlotIface) OtccaTag.dec x

/-! ## `lSaltRedProg` -/

@[reducible] def saltRedStTy : SWT :=
  .prod .bool (chalOptTy (Pt := Pt) ℓ)

@[reducible] def slotReplyTy : SWT :=
  .sum (.opt (lctTy Pt ℓ)) (.opt (.base .plain))

def lSaltInitC {Γ : List SWT} :
    Comp SWOps SaltIface Γ (.prod .unit (saltRedStTy (Pt := Pt) ℓ)) :=
  rdsl do
    b ← sampleSaltBoolC C codec ℓ encT idOf kAEAD kIdeal
    return ((), (b, none))

def lSaltEncC {Γ : List SWT} :
    Comp SWOps SaltIface
      (.prod (slotAdTy Pt ℓ) (.base .plain) :: saltRedStTy (Pt := Pt) ℓ :: Γ)
      (.prod (slotReplyTy (Pt := Pt) ℓ) (saltRedStTy (Pt := Pt) ℓ)) :=
  rdsl [(a, m), st@(b, chal)] do
    if isSomeE C codec ℓ encT idOf kAEAD chal then
      return (.inl none, st)
    else
      mk ← querySaltPrfC C codec ℓ encT idOf kAEAD kIdeal
        (saltOfE C codec ℓ encT idOf kAEAD a)
      if b then
        ct ← sampleSaltIdealC C codec ℓ encT idOf kAEAD kIdeal a
        return (.inl (some ct), (b, some (a, ct)))
      else
        let ct := encKE C codec ℓ encT idOf kAEAD mk a m
        return (.inl (some ct), (b, some (a, ct)))

def lSaltDecC {Γ : List SWT} :
    Comp SWOps SaltIface
      (.prod (slotAdTy Pt ℓ) (lctTy Pt ℓ) :: saltRedStTy (Pt := Pt) ℓ :: Γ)
      (.prod (slotReplyTy (Pt := Pt) ℓ) (saltRedStTy (Pt := Pt) ℓ)) :=
  rdsl [(a, e@(_, ctSalt)), st@(b, chal)] do
    if orE C codec ℓ encT idOf kAEAD
        (orE C codec ℓ encT idOf kAEAD b
          (eqChalSomeE C codec ℓ encT idOf kAEAD chal
            (rdslExpr [_, (a', _)] => a') (rdslExpr [_, (_, e')] => e')))
        !(eqSaltE C codec ℓ encT idOf kAEAD ctSalt
          (saltOfE C codec ℓ encT idOf kAEAD a)) then
      return (.inr none, st)
    else
      mk ← querySaltPrfC C codec ℓ encT idOf kAEAD kIdeal
        (saltOfE C codec ℓ encT idOf kAEAD a)
      return (.inr (decKE C codec ℓ encT idOf kAEAD mk a e), st)

def lSaltFinishC {Γ : List SWT} :
    Comp SWOps SaltIface (saltRedStTy (Pt := Pt) ℓ :: .bool :: Γ) .bool :=
  rdsl [(b, _chal), b'] do
    return eqBoolE C codec ℓ encT idOf kAEAD b b'

/-- Costed `ReductionDsl` program for the single-slot salt-PRF reduction `lSaltRed`. -/
def lSaltRedProg :
    CostedReduction SWOps SaltIface
      (AEADScheme.otccaSpec (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32) SlotCodec
      .unit .unit .bool .bool where
  σ := saltRedStTy (Pt := Pt) ℓ
  init := lSaltInitC C codec ℓ encT idOf kAEAD kIdeal
  handle := rdsl [_st, qry] do
    match qry with
    | .enc _ => lSaltEncC C codec ℓ encT idOf kAEAD kIdeal
    | .dec _ => lSaltDecC C codec ℓ encT idOf kAEAD kIdeal
  finish := lSaltFinishC C codec ℓ encT idOf kAEAD kIdeal

/-! ## `lWireRedProg` -/

@[reducible] def wireSaltEntryTy : SWT :=
  .prod (.base .salt) .nat

@[reducible] def wireStTy : SWT :=
  .prod (.list (wireSaltEntryTy (Pt := Pt) ℓ)) (.prod .bool .bool)

def wireSlotE (q : ℕ) {Γ : List SWT} :
    Expr SWOps (.base .salt :: .list (wireSaltEntryTy (Pt := Pt) ℓ) :: Γ)
      (.prod .nat (.list (wireSaltEntryTy (Pt := Pt) ℓ))) :=
  rdslExpr [salt, salts] =>
    match findB q salts (fun (s, _) => eqSaltE C codec ℓ encT idOf kAEAD s salt) with
    | none => (len salts, cons (salt, len salts) salts)
    | some (_, idx) => (idx, salts)

def lWireEncC (j q : ℕ) {Γ : List SWT} :
    Comp SWOps WireIface
      (.prod (slotAdTy Pt ℓ) (.base .plain) :: wireStTy (Pt := Pt) ℓ :: Γ)
      (.prod (slotReplyTy (Pt := Pt) ℓ) (wireStTy (Pt := Pt) ℓ)) :=
  rdsl [(a, m), st@(salts, (aborted, didEnc))] do
    if didEnc then
      return (.inl none, st)
    else
      _salts ← return salts
      salt ← return saltOfE C codec ℓ encT idOf kAEAD a
      (n, salts') ← return wireSlotE C codec ℓ encT idOf kAEAD q
      if !(n == nat j) then
        return (.inl none, (salts', (true, true)))
      else
        r ← queryWireEncC C codec ℓ encT idOf kAEAD
          (idsOfE C codec ℓ encT idOf kAEAD a, (hdrOfE C codec ℓ encT idOf kAEAD a, m))
        let ctOpt := match r with | none => none | some tag => some (tag, salt)
        return (.inl ctOpt, (salts', (aborted, true)))

def lWireDecC (j q : ℕ) {Γ : List SWT} :
    Comp SWOps WireIface
      (.prod (slotAdTy Pt ℓ) (lctTy Pt ℓ) :: wireStTy (Pt := Pt) ℓ :: Γ)
      (.prod (slotReplyTy (Pt := Pt) ℓ) (wireStTy (Pt := Pt) ℓ)) :=
  rdsl [(a, (wireCt, ctSalt)), st@(salts, flags@(_aborted, didEnc))] do
    if orE C codec ℓ encT idOf kAEAD
        (!didEnc)
        !(eqSaltE C codec ℓ encT idOf kAEAD ctSalt
          (saltOfE C codec ℓ encT idOf kAEAD a)) then
      return (.inr none, st)
    else
      _salts ← return salts
      _salt ← return saltOfE C codec ℓ encT idOf kAEAD a
      (n, salts') ← return wireSlotE C codec ℓ encT idOf kAEAD q
      if n == nat j then
        r ← queryWireDecC C codec ℓ encT idOf kAEAD
          (idsOfE C codec ℓ encT idOf kAEAD a, wireCt)
        let mOpt :=
          match r with
          | none => none
          | some (hdr, rawBytes) =>
            if eqHdrE C codec ℓ encT idOf kAEAD hdr (hdrOfE C codec ℓ encT idOf kAEAD a) then
              some (fitPlainE C codec ℓ encT idOf kAEAD rawBytes)
            else
              none
        return (.inr mOpt, (salts', flags))
      else
        return (.inr none, (salts', flags))

def lWireFinishC (j : ℕ) {Γ : List SWT} :
    Comp SWOps WireIface (wireStTy (Pt := Pt) ℓ :: .bool :: Γ) .bool :=
  rdsl [(_salts, (aborted, didEnc)), b'] do
    if orE C codec ℓ encT idOf kAEAD aborted ((!didEnc) && !(nat j == 0)) then
      sampleWireBoolC C codec ℓ encT idOf kAEAD
    else
      return b'

/-- Costed `ReductionDsl` program for the single-slot wire-OT-CCA reduction `lWireRed j`. -/
def lWireRedProg (j q : ℕ) :
    CostedReduction SWOps WireIface
      (AEADScheme.otccaSpec (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32) SlotCodec
      .unit .unit .bool .bool where
  σ := wireStTy (Pt := Pt) ℓ
  init := rdsl [_] do return ((), ([], (false, false)))
  handle := rdsl [_st, qry] do
    match qry with
    | .enc _ => lWireEncC C codec ℓ encT idOf kAEAD j q
    | .dec _ => lWireDecC C codec ℓ encT idOf kAEAD j q
  finish := lWireFinishC C codec ℓ encT idOf kAEAD j

/-! ## `slotSaltRedProg` and `slotWireRedProg` -/

@[reducible] def ostTy : SWT :=
  .prod (.base .seed) (.prod .bool (chalOptTy (Pt := Pt) ℓ))

@[reducible] def saltSlotStTy : SWT :=
  .prod (chalOptTy (Pt := Pt) ℓ) (.list (.prod (.base .salt) (.base .msgKey)))

def slotKeyOfC (q : ℕ) {Γ : List SWT} :
    Comp SWOps SlotIface (.base .salt :: saltSlotStTy (Pt := Pt) ℓ :: Γ)
      (.prod (.base .msgKey) (saltSlotStTy (Pt := Pt) ℓ)) :=
  rdsl [salt, st@(chal, table)] do
    match findB q table (fun (s, _) => eqSaltE C codec ℓ encT idOf kAEAD salt s) with
    | none =>
      mk ← sampleSlotMsgKeyC C codec ℓ encT idOf kAEAD kIdeal
      return (mk, (chal, cons (salt, mk) table))
    | some (_, mk) =>
      return (mk, st)

def slotSaltEncC (b : Bool) (q : ℕ) {Γ : List SWT} :
    Comp SWOps SlotIface
      (saltSlotStTy (Pt := Pt) ℓ :: .prod (slotAdTy Pt ℓ) (.base .plain) :: Γ)
      (.prod (.opt (lctTy Pt ℓ)) (saltSlotStTy (Pt := Pt) ℓ)) :=
  rdsl [st@(chal, _table), (a, m)] do
    if isSomeE C codec ℓ encT idOf kAEAD chal then
      return (none, st)
    else
      _salt ← return saltOfE C codec ℓ encT idOf kAEAD a
      (mk, (_chal₁, table₁)) ← slotKeyOfC C codec ℓ encT idOf kAEAD kIdeal q
      if bool b then
        ct ← sampleSlotIdealC C codec ℓ encT idOf kAEAD kIdeal a
        return (some ct, (some (a, ct), table₁))
      else
        let ct := encKE C codec ℓ encT idOf kAEAD mk a m
        return (some ct, (some (a, ct), table₁))

def slotSaltDecC (nf b : Bool) (q : ℕ) {Γ : List SWT} :
    Comp SWOps SlotIface
      (saltSlotStTy (Pt := Pt) ℓ :: .prod (slotAdTy Pt ℓ) (lctTy Pt ℓ) :: Γ)
      (.prod (.opt (.base .plain)) (saltSlotStTy (Pt := Pt) ℓ)) :=
  let rejectCond :
      Expr SWOps (saltSlotStTy (Pt := Pt) ℓ :: .prod (slotAdTy Pt ℓ) (lctTy Pt ℓ) :: Γ) .bool :=
    if nf then
      rdslExpr [(chal, _), _] =>
        orE C codec ℓ encT idOf kAEAD
          (orE C codec ℓ encT idOf kAEAD (bool b)
            !(isSlotChalSaltE C codec ℓ encT idOf kAEAD chal
              (saltOfE C codec ℓ encT idOf kAEAD (rdslExpr [_, _, (a', _)] => a'))))
          (eqChalSomeE C codec ℓ encT idOf kAEAD chal
            (rdslExpr [_, _, (a', _)] => a') (rdslExpr [_, _, (_, e')] => e'))
    else
      rdslExpr [(chal, _), _] =>
        orE C codec ℓ encT idOf kAEAD (bool b)
          (eqChalSomeE C codec ℓ encT idOf kAEAD chal
            (rdslExpr [_, _, (a', _)] => a') (rdslExpr [_, _, (_, e')] => e'))
  rdsl [st, (a, e@(_, ctSalt))] do
    if !(eqSaltE C codec ℓ encT idOf kAEAD ctSalt
        (saltOfE C codec ℓ encT idOf kAEAD a)) then
      return (none, st)
    else if raw rejectCond then
      return (none, st)
    else
      _salt ← return saltOfE C codec ℓ encT idOf kAEAD a
      (mk, st₁) ← slotKeyOfC C codec ℓ encT idOf kAEAD kIdeal q
      return (decKE C codec ℓ encT idOf kAEAD mk a e, st₁)

def otImplEncC {Γ : List SWT} :
    Comp SWOps SlotIface
      (ostTy (Pt := Pt) ℓ :: .prod (slotAdTy Pt ℓ) (.base .plain) :: Γ)
      (.prod (.opt (lctTy Pt ℓ)) (ostTy (Pt := Pt) ℓ)) :=
  rdsl [st@(key, (b, chal)), (a, m)] do
    if isSomeE C codec ℓ encT idOf kAEAD chal then
      return (none, st)
    else if b then
      ct ← sampleSlotIdealC C codec ℓ encT idOf kAEAD kIdeal a
      return (some ct, (key, (b, some (a, ct))))
    else
      let ct := encRE C codec ℓ encT idOf kAEAD key a m
      return (some ct, (key, (b, some (a, ct))))

def otImplDecC {Γ : List SWT} :
    Comp SWOps SlotIface
      (ostTy (Pt := Pt) ℓ :: .prod (slotAdTy Pt ℓ) (lctTy Pt ℓ) :: Γ)
      (.prod (.opt (.base .plain)) (ostTy (Pt := Pt) ℓ)) :=
  rdsl [st@(key, (b, chal)), (a, e)] do
    if orE C codec ℓ encT idOf kAEAD b
        (eqChalSomeE C codec ℓ encT idOf kAEAD chal
          (rdslExpr [_, _, (a', _)] => a') (rdslExpr [_, _, (_, e')] => e')) then
      return (none, st)
    else
      return (decRE C codec ℓ encT idOf kAEAD key a e, st)

def slotRedEncC {slTy srTy : SWT} (k : ℕ)
    (encL : ∀ {Γ},
      Comp SWOps SlotIface (slTy :: .prod (slotAdTy Pt ℓ) (.base .plain) :: Γ)
        (.prod (.opt (lctTy Pt ℓ)) slTy))
    (encR : ∀ {Γ},
      Comp SWOps SlotIface (srTy :: .prod (slotAdTy Pt ℓ) (.base .plain) :: Γ)
        (.prod (.opt (lctTy Pt ℓ)) srTy))
    {Γ : List SWT} :
    Comp SWOps SlotIface
      (.prod (slotAdTy Pt ℓ) (.base .plain) :: .prod (.tbl slTy) (.tbl srTy) :: Γ)
      (.prod (slotReplyTy (Pt := Pt) ℓ) (.prod (.tbl slTy) (.tbl srTy))) :=
  rdsl [hm@((slotIdx, _), _m), tbls@(sL, sR)] do
    if slotIdx == nat (k + 1) then
      r ← querySlotEncC C codec ℓ encT idOf kAEAD kIdeal hm
      return (.inl r, tbls)
    else if leE C codec ℓ encT idOf kAEAD 1 slotIdx &&
        leE C codec ℓ encT idOf kAEAD slotIdx (nat k) then
      _cur ← return tget sR slotIdx
      (r, sR') ← encR
      return (.inl r, (sL, tset sR slotIdx sR'))
    else
      _cur ← return tget sL slotIdx
      (r, sL') ← encL
      return (.inl r, (tset sL slotIdx sL', sR))

def slotRedDecC {slTy srTy : SWT} (k : ℕ)
    (decL : ∀ {Γ},
      Comp SWOps SlotIface (slTy :: .prod (slotAdTy Pt ℓ) (lctTy Pt ℓ) :: Γ)
        (.prod (.opt (.base .plain)) slTy))
    (decR : ∀ {Γ},
      Comp SWOps SlotIface (srTy :: .prod (slotAdTy Pt ℓ) (lctTy Pt ℓ) :: Γ)
        (.prod (.opt (.base .plain)) srTy))
    {Γ : List SWT} :
    Comp SWOps SlotIface
      (.prod (slotAdTy Pt ℓ) (lctTy Pt ℓ) :: .prod (.tbl slTy) (.tbl srTy) :: Γ)
      (.prod (slotReplyTy (Pt := Pt) ℓ) (.prod (.tbl slTy) (.tbl srTy))) :=
  rdsl [he@((slotIdx, _), _e), tbls@(sL, sR)] do
    if slotIdx == nat (k + 1) then
      r ← querySlotDecC C codec ℓ encT idOf kAEAD kIdeal he
      return (.inr r, tbls)
    else if leE C codec ℓ encT idOf kAEAD 1 slotIdx &&
        leE C codec ℓ encT idOf kAEAD slotIdx (nat k) then
      _cur ← return tget sR slotIdx
      (r, sR') ← decR
      return (.inr r, (sL, tset sR slotIdx sR'))
    else
      _cur ← return tget sL slotIdx
      (r, sL') ← decL
      return (.inr r, (tset sL slotIdx sL', sR))

/-- Generic `slotRedImpl` handler routing slot `k + 1` externally, `1 ≤ i ≤ k` right, and others left. -/
def slotRedHandleC {slTy srTy : SWT} (k : ℕ)
    (encL : ∀ {Γ},
      Comp SWOps SlotIface (slTy :: .prod (slotAdTy Pt ℓ) (.base .plain) :: Γ)
        (.prod (.opt (lctTy Pt ℓ)) slTy))
    (decL : ∀ {Γ},
      Comp SWOps SlotIface (slTy :: .prod (slotAdTy Pt ℓ) (lctTy Pt ℓ) :: Γ)
        (.prod (.opt (.base .plain)) slTy))
    (encR : ∀ {Γ},
      Comp SWOps SlotIface (srTy :: .prod (slotAdTy Pt ℓ) (.base .plain) :: Γ)
        (.prod (.opt (lctTy Pt ℓ)) srTy))
    (decR : ∀ {Γ},
      Comp SWOps SlotIface (srTy :: .prod (slotAdTy Pt ℓ) (lctTy Pt ℓ) :: Γ)
        (.prod (.opt (.base .plain)) srTy)) :
    Comp SWOps SlotIface
      [.prod (.tbl slTy) (.tbl srTy), (SlotCodec).Q]
      (.prod (SlotCodec).R (.prod (.tbl slTy) (.tbl srTy))) :=
  rdsl [_tbls, qry] do
    match qry with
    | .enc _ => slotRedEncC C codec ℓ encT idOf kAEAD kIdeal k encL encR
    | .dec _ => slotRedDecC C codec ℓ encT idOf kAEAD kIdeal k decL decR

def emptySaltSlotStE {Γ : List SWT} : Expr SWOps Γ (saltSlotStTy (Pt := Pt) ℓ) :=
  .pair .none .nil

def slotSaltInitC (N : ℕ) {Γ : List SWT} :
    Comp SWOps SlotIface Γ
      (.prod .unit (.prod (.tbl (ostTy (Pt := Pt) ℓ)) (.tbl (saltSlotStTy (Pt := Pt) ℓ)))) :=
  rdsl do
    seed₀ ← sampleSlotSeedC C codec ℓ encT idOf kAEAD kIdeal
    (_, tbl) ← iter N (1, tconst (seed₀, (false, none))) fun (idx, curTbl) => do
      seed ← sampleSlotSeedC C codec ℓ encT idOf kAEAD kIdeal
      return (idx + 1, tset curTbl idx (seed, (false, none)))
    return ((), (tbl, tconst (emptySaltSlotStE C codec ℓ encT idOf kAEAD)))

/-- Costed `ReductionDsl` program for the multi-to-single-slot salt-PRF wrapper `slotSaltRed N k`. -/
def slotSaltRedProg (N k q : ℕ) :
    CostedReduction SWOps SlotIface
      (AEADScheme.otccaSpec (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32) SlotCodec
      .unit .unit .bool .bool where
  σ := .prod (.tbl (ostTy (Pt := Pt) ℓ)) (.tbl (saltSlotStTy (Pt := Pt) ℓ))
  init := slotSaltInitC C codec ℓ encT idOf kAEAD kIdeal N
  handle :=
    slotRedHandleC C codec ℓ encT idOf kAEAD kIdeal k
      (otImplEncC C codec ℓ encT idOf kAEAD kIdeal)
      (otImplDecC C codec ℓ encT idOf kAEAD kIdeal)
      (slotSaltEncC C codec ℓ encT idOf kAEAD kIdeal false q)
      (slotSaltDecC C codec ℓ encT idOf kAEAD kIdeal false false q)
  finish := rdsl [_, guess] do return guess

/-- Costed `ReductionDsl` program for the multi-to-single-slot wire-OT-CCA wrapper `slotWireRed k`. -/
def slotWireRedProg (k q : ℕ) :
    CostedReduction SWOps SlotIface
      (AEADScheme.otccaSpec (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32) SlotCodec
      .unit .unit .bool .bool where
  σ := .prod (.tbl (saltSlotStTy (Pt := Pt) ℓ)) (.tbl (saltSlotStTy (Pt := Pt) ℓ))
  init := rdsl [_] do
    return ((),
      (tconst (emptySaltSlotStE C codec ℓ encT idOf kAEAD),
       tconst (emptySaltSlotStE C codec ℓ encT idOf kAEAD)))
  handle :=
    slotRedHandleC C codec ℓ encT idOf kAEAD kIdeal k
      (slotSaltEncC C codec ℓ encT idOf kAEAD kIdeal false q)
      (slotSaltDecC C codec ℓ encT idOf kAEAD kIdeal true false q)
      (slotSaltEncC C codec ℓ encT idOf kAEAD kIdeal true q)
      (slotSaltDecC C codec ℓ encT idOf kAEAD kIdeal false true q)
  finish := rdsl [_, guess] do return guess

end CryptoGames.Ratchet.LibsignalInst.Costed
