/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.Dsl.M3Interfaces

/-!
# Encoders, Wire Filters, and Session Expressions for Local Session Steps

Proves wire-parser equivalence between `CompositionCostedTables` and the binary harness, factors
`bhE2EStepLocalSm` through the pure filter `bhFilterLocalSmQuery`, and defines bounded-list
indexing and per-session `ReductionDsl` expressions for `LocalSessionStep`.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.Dsl.LocalSessionStepAux

open Classical
open OracleSpec OracleComp

open ReductionDsl (Ty Ops Var Expr Env bits)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.LibsignalSession (Crypto PublicKey IdentityKey GhostState)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.E2E (Bytes PreKeyMessageFields wirePrekey shortCiphertext
  ModelDriverInstanceMeta BHModelInst BHE2EDrvState
  bhIdKeyOf bhReadProstVarint bhParseOptPreKeyId bhParseUint32Field bhParseDjbKeyField
  bhParseInnerMsgFieldWithRest bhParseKyberCtField bhHdrOfPreKeyMsg
  bhDecodePreKeyMsgERaw bhDecodePreKeyMsgE bhExpectedPreKeyMsg
  bhDrvSessionInitPrin? bhInitRegId bhIsBobRecvSMQuery bhIsBobAcceptSMResp
  bhPackSmResp bhE2EDrvInstClean bhE2EInstIkACorr bhE2EStepLocalSm
  paramsIdsWithSpqr sessionSchemeFixedSpk configRefuseEarlyBobCorr)
open CryptoVerification.E2E.Costed (E2EPureOp e2eSig e2ePureOps e2eOps
  PB U32 BV256 FinT IdKey GhostStT hdrT hdrV hdrOfV sidT sidV sidOfV
  recvResultEnc partyToBool boolToParty smQT smQenc smRT
  e2eReadProstVarint e2eParseOptPreKeyId e2eParseUint32Field e2eParseDjbKeyField
  e2eParseInnerMsgField e2eParseKyberCtField e2eDecodePreKeyRaw e2eDecodePreKeyMsg
  e2eHdrOfPreKeyMsg e2eExpectedPreKeyMsg e2ePartneredInnerBytes ghostJoinEval)
open Computational.Proofs.E2E.Dsl.TablesHonest (e2ePureOp eval_e2ePureOp cost_e2ePureOp
  hdrOfV_hdrV hdrV_hdrOfV sidOfV_sidV sidV_sidOfV)
open Computational.Proofs.E2E.Dsl.ClampsLossless (e2ePartneredInnerBytes_lossless
  e2ePureOps_eval_parsePreKeyWire_lossless)
open Computational.Proofs.E2E.Dsl.PqxdhSimTypes (v eval_v_refl eval_v_cons env_get_zero
  env_get_succ exprCostUB_v eLet eCaseOpt eCaseSum exprCostUB_eLet exprCostUB_eCaseOpt
  exprCostUB_eCaseSum isNoneE optEqByE
  hdrIkA hdrEkA hdrSpkId hdrOpkId hdrPqId hdrKemCt)
open Computational.Proofs.E2E.Dsl.M2Interfaces (e2eGsTy e2eGsEnc smQdec smQdec_smQenc
  smQenc_smQdec smRenc)
open Computational.Proofs.E2E.Dsl.M3Interfaces (packSmRespEnc
  e2eInstMetaTy e2eInstMetaEnc e2eInstMetaDec e2eInstMetaDec_e2eInstMetaEnc bhFilterSmQuery)
open Computational.Proofs.GameHop.ReductionDsl.CostUB (exprCostUB exprCost_le_costUB)
open SignalPqxdh (Setup Primitives HandshakeHdr SessionId kyberCtLen)

/-! ## Wire-parser equivalence and query filter -/

theorem e2eReadProstVarint_eq_bhReadProstVarint :
    ∀ (bs : List (BitVec 8)), e2eReadProstVarint bs = bhReadProstVarint bs
  | [] => rfl
  | _ :: rest => by
    simp only [e2eReadProstVarint, bhReadProstVarint, e2eReadProstVarint_eq_bhReadProstVarint rest]

private theorem e2eParseOptPreKeyId_eq (bs : List (BitVec 8)) :
    e2eParseOptPreKeyId bs = bhParseOptPreKeyId bs := by
  cases bs <;> simp [e2eParseOptPreKeyId, bhParseOptPreKeyId, e2eReadProstVarint_eq_bhReadProstVarint]

private theorem e2eParseUint32Field_eq (keyByte : BitVec 8) (bs : List (BitVec 8)) :
    e2eParseUint32Field keyByte bs = bhParseUint32Field keyByte bs := by
  cases bs <;> simp [e2eParseUint32Field, bhParseUint32Field, e2eReadProstVarint_eq_bhReadProstVarint]

private theorem e2eParseDjbKeyField_eq (keyByte : BitVec 8) (bs : List (BitVec 8)) :
    e2eParseDjbKeyField keyByte bs = bhParseDjbKeyField keyByte bs := by
  match bs with
  | [] | [_] | [_, _] => rfl
  | _ :: b1 :: b2 :: _ =>
    by_cases h1 : b1 = 0x21#8 <;> by_cases h2 : b2 = 0x05#8 <;>
      simp [e2eParseDjbKeyField, bhParseDjbKeyField, h1, h2]

private theorem e2eParseInnerMsgField_eq (bs : List (BitVec 8)) :
    e2eParseInnerMsgField bs = bhParseInnerMsgFieldWithRest bs := by
  cases bs with
  | nil => rfl
  | cons b _ =>
    by_cases hb : b = 0x22#8 <;>
      simp [e2eParseInnerMsgField, bhParseInnerMsgFieldWithRest, hb,
        e2eReadProstVarint_eq_bhReadProstVarint]

private theorem e2eParseKyberCtField_eq (bs : List (BitVec 8)) :
    e2eParseKyberCtField bs = bhParseKyberCtField bs := by
  match bs with
  | [] | [_] | [_, _] | [_, _, _] => rfl
  | b0 :: b1 :: b2 :: b3 :: _ =>
    by_cases h0 : b0 = 0x42#8 <;> by_cases h1 : b1 = 0xa1#8 <;>
      by_cases h2 : b2 = 0x0c#8 <;> by_cases h3 : b3 = 0x08#8 <;>
      simp [e2eParseKyberCtField, bhParseKyberCtField, h0, h1, h2, h3]

theorem e2eDecodePreKeyRaw_eq_bhDecodePreKeyMsgERaw (c : Bytes) :
    e2eDecodePreKeyRaw c = bhDecodePreKeyMsgERaw c := by
  match c with
  | [] | [_] => rfl
  | _ :: _ :: _ =>
    simp only [e2eDecodePreKeyRaw, bhDecodePreKeyMsgERaw, e2eParseOptPreKeyId_eq,
      e2eParseDjbKeyField_eq, e2eParseInnerMsgField_eq, e2eParseUint32Field_eq,
      e2eParseKyberCtField_eq]

theorem e2eDecodePreKeyMsg_eq_bhDecodePreKeyMsgE (c : Bytes) :
    e2eDecodePreKeyMsg c = bhDecodePreKeyMsgE c := by
  unfold e2eDecodePreKeyMsg bhDecodePreKeyMsgE
  rw [e2eDecodePreKeyRaw_eq_bhDecodePreKeyMsgERaw]
  cases bhDecodePreKeyMsgERaw c <;> rfl

theorem e2eHdrOfPreKeyMsg_eq_bhHdrOfPreKeyMsg (m : PreKeyMessageFields) :
    e2eHdrOfPreKeyMsg m = bhHdrOfPreKeyMsg m := rfl

theorem e2eExpectedPreKeyMsg_eq_bhExpectedPreKeyMsg (regIdA : BitVec 32)
    (hdr : HandshakeHdr) (inner : Bytes) :
    e2eExpectedPreKeyMsg regIdA hdr inner = bhExpectedPreKeyMsg regIdA hdr inner := by
  unfold e2eExpectedPreKeyMsg bhExpectedPreKeyMsg kyberCtLen; rfl

/-- Pure wire-filtering function factoring the five query-dispatch branches of `bhE2EStepLocalSm`. -/
def bhFilterLocalSmQuery {S : Setup} {ℓ : ℕ} (bobAccepted : Bool) (sid : SessionId S)
    (hdr : HandshakeHdr)
    (q : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    Option ((CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :=
  match q with
  | .inl (.inl (.inr (.A, c))) => if (bhDecodePreKeyMsgE c).isSome then none else some q
  | .inl (.inr (.A, c)) => if (bhDecodePreKeyMsgE c).isSome then none else some q
  | .inl (.inl (.inr (.B, c))) =>
    if !bobAccepted then
      match bhDecodePreKeyMsgE c with
      | some m =>
        if c == wirePrekey :: (bhExpectedPreKeyMsg (bhInitRegId sid) hdr m.inner).bytes then
          some (.inl (.inl (.inr (.B, m.inner))))
        else none
      | none => none
    else
      match bhDecodePreKeyMsgE c with
      | some m =>
        if bhHdrOfPreKeyMsg m == hdr then some (.inl (.inl (.inr (.B, m.inner)))) else none
      | none => some (.inl (.inl (.inr (.B, c))))
  | .inl (.inr (.B, c)) =>
    if !bobAccepted then none
    else
      match bhDecodePreKeyMsgE c with
      | some m =>
        if bhHdrOfPreKeyMsg m == hdr && shortCiphertext c &&
           decide (m.inner.length + 2048 < 2 ^ 32) then
          some (.inl (.inr (.B, m.inner)))
        else none
      | none => some (.inl (.inr (.B, c)))
  | _ => some q

theorem bhFilterLocalSmQuery_eq_bhFilterSmQuery {S : Setup} {ℓ : ℕ}
    (d : BHModelInst S ℓ) (im : ModelDriverInstanceMeta S)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    bhFilterLocalSmQuery im.bobAccepted d.sid d.hdr sq = bhFilterSmQuery d im sq := rfl

/-- Factors wire parsing in `bhE2EStepLocalSm` through `bhFilterLocalSmQuery`. -/
theorem bhE2EStepLocalSm_eq_filtered {S : Setup} {ℓ : ℕ} {Pt : Type}
    (C : Crypto) (K : MlKem) (qep : ℕ) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (σ : BHE2EDrvState S ℓ) (i : ℕ)
    (q : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    bhE2EStepLocalSm C K qep decT encT σ i q =
      if !bhE2EDrvInstClean σ i then pure ((none, none, none), σ)
      else
        match σ.insts[i]?, σ.instMeta[i]? with
        | some d, some im =>
          if !im.bobAccepted && bhIsBobRecvSMQuery q && bhE2EInstIkACorr σ d then
            let imCorr := { im with bobAccepted := true, ikACorrAtAccept := true }
            pure ((none, none, none), { σ with instMeta := σ.instMeta.set i imCorr })
          else
            match d.gs with
            | none => pure ((none, none, none), σ)
            | some gs =>
              match bhFilterLocalSmQuery im.bobAccepted d.sid d.hdr q with
              | none => pure ((none, none, none), σ)
              | some q' => do
                let spqr := spqrV1SessionUniformCoins C.F K
                let sch := sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr d.idA d.idB) ℓ d.spkCoins
                let cfg := configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ)
                  decT encT
                let (r, gs') ← (CryptoGames.SM.oracleImplR sch (2 + 1) qep cfg q').run gs
                let im' := if !im.bobAccepted && bhIsBobAcceptSMResp q' r then
                    { im with bobAccepted := true, ikACorrAtAccept := bhE2EInstIkACorr σ d }
                  else im
                pure (bhPackSmResp q' r,
                  { σ with insts := σ.insts.set i { d with gs := some gs' },
                           instMeta := σ.instMeta.set i im' })
        | _, _ => pure ((none, none, none), σ) := by
  unfold bhE2EStepLocalSm bhFilterLocalSmQuery
  by_cases hcl : !bhE2EDrvInstClean σ i
  · simp only [hcl, ↓reduceIte]
  · simp only [hcl, Bool.false_eq_true, ↓reduceIte]
    cases σ.insts[i]? with
    | none => rfl
    | some d =>
      cases σ.instMeta[i]? with
      | none => rfl
      | some im =>
        dsimp only
        by_cases hcorr : !im.bobAccepted && bhIsBobRecvSMQuery q && bhE2EInstIkACorr σ d
        · simp only [hcorr, ↓reduceIte]
        · simp only [hcorr, Bool.false_eq_true, ↓reduceIte]
          cases d.gs with
          | none => rfl
          | some gs =>
            dsimp only
            rcases q with (((_ | _) | ⟨pDl, cDl⟩) | ⟨pIj, cIj⟩) | _
            · rfl
            · rfl
            · cases pDl
              · by_cases hs : (bhDecodePreKeyMsgE cDl).isSome <;>
                  simp only [hs, Bool.false_eq_true, ↓reduceIte]
              · by_cases hba : !im.bobAccepted
                · simp only [hba, ↓reduceIte]
                  cases bhDecodePreKeyMsgE cDl with
                  | none => rfl
                  | some m =>
                    by_cases hc : cDl == wirePrekey ::
                        (bhExpectedPreKeyMsg (bhInitRegId d.sid) d.hdr m.inner).bytes <;>
                      simp only [hc, Bool.false_eq_true, ↓reduceIte]
                · simp only [hba, Bool.false_eq_true, ↓reduceIte]
                  cases bhDecodePreKeyMsgE cDl with
                  | none => rfl
                  | some m =>
                    by_cases hh : bhHdrOfPreKeyMsg m == d.hdr <;>
                      simp only [hh, Bool.false_eq_true, ↓reduceIte]
            · cases pIj
              · by_cases hs : (bhDecodePreKeyMsgE cIj).isSome <;>
                  simp only [hs, Bool.false_eq_true, ↓reduceIte]
              · by_cases hba : !im.bobAccepted
                · simp only [hba, ↓reduceIte]
                · simp only [hba, Bool.false_eq_true, ↓reduceIte]
                  cases bhDecodePreKeyMsgE cIj with
                  | none => rfl
                  | some m =>
                    by_cases hh : (bhHdrOfPreKeyMsg m == d.hdr && shortCiphertext cIj &&
                        decide (m.inner.length + 2048 < 2 ^ 32)) <;>
                      simp only [hh, Bool.false_eq_true, ↓reduceIte]
            · rfl

def emptySmRespE {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))} :
    Expr O Γ (smRT GhostStT) := .pair .none (.pair .none .none)

@[simp] theorem eval_emptySmRespE {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    (ρ : Env Γ) :
    (emptySmRespE (ℓ := ℓ) (O := O)).eval ρ = packSmRespEnc (ℓ := ℓ) (none, none, none) := rfl

@[simp] theorem cost_emptySmRespE {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))} :
    (emptySmRespE (ℓ := ℓ) (O := O) (Γ := Γ)).cost = 5 := rfl

@[dsl_cost, simp] theorem exprCostUB_emptySmRespE {ℓ : ℕ} {O : Ops (e2eSig ℓ)}
    {Γ : List (Ty (e2eSig ℓ))} :
    exprCostUB (emptySmRespE (ℓ := ℓ) (O := O) (Γ := Γ)) = 5 := rfl

/-! ## Slot encodings and bounded-list indexing -/

/-- Session-slot representation `(idA, (idB, (spkCoins, (promFlag, gsVal))))`, with
`promFlag = false` for unpromoted local sessions and `promFlag = true` otherwise. -/
@[reducible] def instSlotTy (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .prod IdKey (.prod IdKey (.prod BV256 (.prod .bool (e2eGsTy ℓ))))

def defaultGhostState {ℓ : ℕ} : GhostState Bytes :=
  ghostJoinEval (ℓ := ℓ)
    (false, (0#32, (bhIdKeyOf [], (none, (0#256, (0#32,
      (false, (0, ([], (none, ([], E2EPureOp.eval ℓ (.bytesLit 32 []) ())))))))))))

def defaultE2eGsVal {ℓ : ℕ} : (e2eGsTy ℓ).denote :=
  ((defaultGhostState (ℓ := ℓ), defaultGhostState (ℓ := ℓ)),
   (false, (false, ((0, 0), ((0, 0), (none, ([], ([], ([], ((fun _ => 0, fun _ => 0), ([], [])))))))))))

def defaultInstSlotVal {ℓ : ℕ} : (instSlotTy ℓ).denote :=
  (bhIdKeyOf [], (bhIdKeyOf [], (0#256, (true, defaultE2eGsVal))))

def defaultE2eGsE {ℓ : ℕ} {Pt : Type} {P : Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {Γ : List (Ty (e2eSig ℓ))} :
    Expr (e2eOps ℓ P C K decT encT) Γ (e2eGsTy ℓ) :=
  let idKey0 := e2ePureOp .idKeyOfPbytes (e2ePureOp (.pbytesLit 32 []) .unit)
  let gsPart0 := e2ePureOp .ghostStateJoin
    (.pair (.bool false) (.pair (e2ePureOp (.u32Lit 0#32) .unit)
      (.pair idKey0 (.pair .none (.pair (e2ePureOp (.bv256Lit 0#256) .unit)
        (.pair (e2ePureOp (.u32Lit 0#32) .unit) (.pair (.bool false)
          (.pair (.nat 0) (.pair .nil (.pair .none (.pair .nil
            (e2ePureOp (.bytesLit 32 []) .unit))))))))))))
  .pair (.pair gsPart0 gsPart0)
    (.pair (.bool false) (.pair (.bool false) (.pair (.pair (.nat 0) (.nat 0))
      (.pair (.pair (.nat 0) (.nat 0)) (.pair .none (.pair .nil (.pair .nil
        (.pair .nil (.pair (.pair (.tconst (.nat 0)) (.tconst (.nat 0)))
          (.pair .nil .nil))))))))))

@[simp] theorem eval_defaultE2eGsE {ℓ : ℕ} {Pt : Type} {P : Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {Γ : List (Ty (e2eSig ℓ))}
    (ρ : Env Γ) :
    (defaultE2eGsE (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)).eval ρ =
      defaultE2eGsVal (ℓ := ℓ) := by
  simp [defaultE2eGsE, defaultE2eGsVal, defaultGhostState, bhIdKeyOf, Expr.eval, eval_e2ePureOp,
    E2EPureOp.eval]

theorem cost_defaultE2eGsE {ℓ : ℕ} {Pt : Type} {P : Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {Γ : List (Ty (e2eSig ℓ))} :
    (defaultE2eGsE (ℓ := ℓ) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) (Γ := Γ)).cost ≤ 350 := by
  have hb0 : bits 0 = 1 := rfl
  simp only [defaultE2eGsE, Expr.cost, cost_e2ePureOp, E2EPureOp.cost, PNat.val_ofNat,
    List.length_nil, hb0]
  omega

def instSlotOfModelInst {S : Setup} {ℓ : ℕ} (d : BHModelInst S ℓ) : (instSlotTy ℓ).denote :=
  (d.idA, (d.idB, (d.spkCoins,
    match d.gs with | some gs => (false, e2eGsEnc gs) | none => (true, defaultE2eGsVal))))

def encodeInstTbl {S : Setup} {ℓ : ℕ} (insts : List (BHModelInst S ℓ))
    (j : ℕ) : (instSlotTy ℓ).denote :=
  match insts[j]? with | some d => instSlotOfModelInst d | none => defaultInstSlotVal

theorem tset_encodeInstTbl {S : Setup} {ℓ : ℕ} (insts : List (BHModelInst S ℓ))
    (i : ℕ) (d' : BHModelInst S ℓ) (hi : i < insts.length) :
    (fun j => if j = i then instSlotOfModelInst d' else encodeInstTbl insts j) =
      encodeInstTbl (insts.set i d') := by
  funext j; unfold encodeInstTbl; rw [List.getElem?_set]
  by_cases hji : j = i
  · subst hji; simp [hi]
  · simp [hji, Ne.symm hji]

@[reducible] def e2eInstHdrMetaTy (S : Setup) (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .prod (sidT S) (.prod hdrT (e2eInstMetaTy S ℓ))

def e2eInstHdrMetaEnc {S : Setup} {ℓ : ℕ} (d : BHModelInst S ℓ)
    (im : ModelDriverInstanceMeta S) : (e2eInstHdrMetaTy S ℓ).denote :=
  (sidV d.sid, (hdrV d.hdr, e2eInstMetaEnc im))

def encodeHdrMetaList {S : Setup} {ℓ : ℕ} (insts : List (BHModelInst S ℓ))
    (instMeta : List (ModelDriverInstanceMeta S)) : List (e2eInstHdrMetaTy S ℓ).denote :=
  (insts.zip instMeta).map fun p => e2eInstHdrMetaEnc p.1 p.2

theorem zip_getElem_eq {α β : Type} :
    ∀ (as : List α) (bs : List β) (i : ℕ), as.length = bs.length →
      (as.zip bs)[i]? = match as[i]?, bs[i]? with
        | some a, some b => some (a, b)
        | _, _ => none
  | [], [], _, _ => rfl
  | _ :: _, [], _, h => nomatch h
  | [], _ :: _, _, h => nomatch h
  | _ :: _, _ :: _, 0, _ => rfl
  | _ :: as, _ :: bs, i + 1, h => zip_getElem_eq as bs i (Nat.succ.inj h)

theorem zip_set_both {α β : Type} :
    ∀ (as : List α) (bs : List β) (i : ℕ) (a : α) (b : β),
      (as.set i a).zip (bs.set i b) = (as.zip bs).set i (a, b)
  | [], _, _, _, _ => rfl
  | _ :: _, [], _, _, _ => by simp
  | _ :: _, _ :: _, 0, _, _ => rfl
  | x :: as, y :: bs, i + 1, a, b => congrArg ((x, y) :: ·) (zip_set_both as bs i a b)

theorem zip_all_and {α β : Type} (p : α → Bool) (q : β → Bool) :
    ∀ (as : List α) (bs : List β), as.length = bs.length →
      (as.zip bs).all (fun x => p x.1 && q x.2) = (as.all p && bs.all q)
  | [], [], _ => rfl
  | _ :: _, [], h => nomatch h
  | [], _ :: _, h => nomatch h
  | a :: as, b :: bs, h => by
    simp only [List.zip_cons_cons, List.all_cons, zip_all_and p q as bs (Nat.succ.inj h)]
    cases p a <;> cases q b <;> cases as.all p <;> cases bs.all q <;> rfl

theorem not_any_not_eq_all {α : Type} (p : α → Bool) :
    ∀ (l : List α), (!(l.any (fun x => !p x))) = l.all p
  | [] => rfl
  | _ :: xs => by
    simp only [List.any_cons, List.all_cons, Bool.not_or, Bool.not_not, not_any_not_eq_all p xs]

/-- Look up index `iE` in an unindexed list `lE : Expr O Γ (.list t)` of length `≤ K` via
`Expr.foldrB`. -/
def listGetOptE {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))} {t : Ty (e2eSig ℓ)}
    (K : ℕ) (lE : Expr O Γ (.list t)) (iE : Expr O Γ .nat) : Expr O Γ (.opt t) :=
  .letE (.pair lE iE)
    (.letE (.len (.fst .v0))
      (.snd
        (.foldrB K (.fst .v1) (.pair (.nat 0) .none)
          (.pair (.add (.fst .v1) (.nat 1))
            (.ite (.eqN (.add (.add (.fst .v1) (.nat 1)) (.snd .v3)) .v2)
              (.some .v0) (.snd .v1))))))

private def foldGetStep {α : Type} (L i : ℕ) (x : α) (acc : ℕ × Option α) : ℕ × Option α :=
  (acc.1 + 1, if decide (acc.1 + 1 + i = L) = true then some x else acc.2)

private theorem foldGetStep_fst {α : Type} (L i : ℕ) :
    ∀ (xs : List α), (xs.foldr (foldGetStep L i) (0, none)).1 = xs.length
  | [] => rfl
  | _ :: xs => by simp [foldGetStep, foldGetStep_fst L i xs]

private theorem foldGetStep_snd {α : Type} (L i : ℕ) :
    ∀ (xs : List α) (off : ℕ), off + xs.length = L →
      (xs.foldr (foldGetStep L i) (0, none)).2 = if off ≤ i then xs[i - off]? else none
  | [], _, _ => by split_ifs <;> rfl
  | x :: xs, off, hL => by
    simp only [List.length_cons] at hL
    simp only [List.foldr_cons, foldGetStep, foldGetStep_fst L i xs,
      foldGetStep_snd L i xs (off + 1) (by omega)]
    by_cases hi : i = off
    · subst hi; have hcond : xs.length + 1 + i = L := by omega
      simp [hcond]
    · have hcond : ¬(xs.length + 1 + i = L) := by omega
      simp only [decide_eq_false hcond, Bool.false_eq_true, ↓reduceIte]
      by_cases hle : off ≤ i
      · have hle' : off + 1 ≤ i := by omega
        have hsub : i - off = (i - (off + 1)) + 1 := by omega
        simp [hle, hle', hsub]
      · have hle' : ¬(off + 1 ≤ i) := by omega
        simp [hle, hle']

theorem eval_listGetOptE {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    {t : Ty (e2eSig ℓ)} (K : ℕ) (lE : Expr O Γ (.list t)) (iE : Expr O Γ .nat) (ρ : Env Γ)
    (hlen : (lE.eval ρ).length ≤ K) :
    (listGetOptE K lE iE).eval ρ = (lE.eval ρ)[iE.eval ρ]? := by
  have htake : (lE.eval ρ).take K = lE.eval ρ := List.take_of_length_le hlen
  dsimp only [listGetOptE, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.eval, env_get_zero,
    env_get_succ]
  rw [htake]
  exact foldGetStep_snd (lE.eval ρ).length (iE.eval ρ) (lE.eval ρ) 0
    (Nat.zero_add (lE.eval ρ).length)

theorem cost_listGetOptE {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    {t : Ty (e2eSig ℓ)} (K : ℕ) (lE : Expr O Γ (.list t)) (iE : Expr O Γ .nat) :
    (listGetOptE K lE iE).cost ≤ lE.cost + iE.cost + 26 * K + 15 := by
  dsimp only [listGetOptE, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.cost]
  have hb0 : bits 0 = 1 := rfl
  have hb1 : bits 1 = 1 := rfl
  rw [hb0, hb1]
  have hmul :
      K * (1 + 1 + 1 + 1 + (1 + 1 + 1 + 1 + (1 + 1) + 1 + 1 + 1 + max (1 + 1) (1 + 1) + 1) + 1 + 1) ≤
        K * 26 := Nat.mul_le_mul_left K (by decide)
  omega

/-- Replace index `iE` with `valE` in an unindexed list `lE : Expr O Γ (.list t)` of length `≤ K`
via `Expr.foldrB`. -/
def listSetE {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))} {t : Ty (e2eSig ℓ)}
    (K : ℕ) (lE : Expr O Γ (.list t)) (iE : Expr O Γ .nat) (valE : Expr O Γ t) :
    Expr O Γ (.list t) :=
  .letE (.pair lE (.pair iE valE))
    (.letE (.len (.fst .v0))
      (.snd
        (.foldrB K (.fst .v1) (.pair (.nat 0) .nil)
          (.pair (.add (.fst .v1) (.nat 1))
            (.cons
              (.ite (.eqN (.add (.add (.fst .v1) (.nat 1)) (.fst (.snd .v3))) .v2)
                (.snd (.snd .v3)) .v0)
              (.snd .v1))))))

private def foldSetStep {α : Type} (L i : ℕ) (val : α) (x : α) (acc : ℕ × List α) : ℕ × List α :=
  (acc.1 + 1, (if decide (acc.1 + 1 + i = L) = true then val else x) :: acc.2)

private theorem foldSetStep_fst {α : Type} (L i : ℕ) (val : α) :
    ∀ (xs : List α), (xs.foldr (foldSetStep L i val) (0, [])).1 = xs.length
  | [] => rfl
  | _ :: xs => by simp [foldSetStep, foldSetStep_fst L i val xs]

private theorem foldSetStep_snd {α : Type} (L i : ℕ) (val : α) :
    ∀ (xs : List α) (off : ℕ), off + xs.length = L →
      (xs.foldr (foldSetStep L i val) (0, [])).2 =
        if off ≤ i then xs.set (i - off) val else xs
  | [], _, _ => by split_ifs <;> rfl
  | x :: xs, off, hL => by
    simp only [List.length_cons] at hL
    simp only [List.foldr_cons, foldSetStep, foldSetStep_fst L i val xs,
      foldSetStep_snd L i val xs (off + 1) (by omega)]
    by_cases hi : i = off
    · subst hi
      have hcond : xs.length + 1 + i = L := by omega
      have hnle : ¬(i + 1 ≤ i) := by omega
      simp [hcond, hnle]
    · have hcond : ¬(xs.length + 1 + i = L) := by omega
      simp only [decide_eq_false hcond, Bool.false_eq_true, ↓reduceIte]
      by_cases hle : off ≤ i
      · have hle' : off + 1 ≤ i := by omega
        have hsub : i - off = (i - (off + 1)) + 1 := by omega
        simp [hle, hle', hsub]
      · have hle' : ¬(off + 1 ≤ i) := by omega
        simp [hle, hle']

theorem eval_listSetE {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    {t : Ty (e2eSig ℓ)} (K : ℕ) (lE : Expr O Γ (.list t)) (iE : Expr O Γ .nat)
    (valE : Expr O Γ t) (ρ : Env Γ) (hlen : (lE.eval ρ).length ≤ K) :
    (listSetE K lE iE valE).eval ρ = (lE.eval ρ).set (iE.eval ρ) (valE.eval ρ) := by
  have htake : (lE.eval ρ).take K = lE.eval ρ := List.take_of_length_le hlen
  dsimp only [listSetE, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.eval, env_get_zero,
    env_get_succ]
  rw [htake]
  exact foldSetStep_snd (lE.eval ρ).length (iE.eval ρ) (valE.eval ρ)
    (lE.eval ρ) 0 (Nat.zero_add (lE.eval ρ).length)

theorem cost_listSetE {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    {t : Ty (e2eSig ℓ)} (K : ℕ) (lE : Expr O Γ (.list t)) (iE : Expr O Γ .nat)
    (valE : Expr O Γ t) :
    (listSetE K lE iE valE).cost ≤ lE.cost + iE.cost + valE.cost + 30 * K + 16 := by
  dsimp only [listSetE, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.cost]
  have hb0 : bits 0 = 1 := rfl
  have hb1 : bits 1 = 1 := rfl
  rw [hb0, hb1]
  have hmul :
      K * (1 + 1 + 1 + 1 + (1 + 1 + 1 + 1 + (1 + 1 + 1) + 1 + 1 + 1 + max (1 + 1 + 1) 1 + 1 + (1 + 1) + 1) + 1 + 1) ≤
        K * 30 := Nat.mul_le_mul_left K (by decide)
  omega

/-! ## Per-session pure expressions -/

section SessionExprs

variable {ℓ : ℕ} {S : Setup} {Pt : Type} {P : Primitives} {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}

@[dsl_cost, simp] theorem exprCostUB_e2ePureOp {Γ : List (Ty (e2eSig ℓ))}
    (o : E2EPureOp) (a : Expr (e2eOps ℓ P C K decT encT) Γ (o.dom ℓ)) :
    exprCostUB (e2ePureOp (P := P) (C := C) (K := K) (decT := decT) (encT := encT) o a) =
      exprCostUB a + o.cost ℓ := rfl

theorem cost_eLet_le {Γ : List (Ty (e2eSig ℓ))} {τ υ : Ty (e2eSig ℓ)}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ τ)
    (k : Var (τ :: Γ) τ → Expr (e2eOps ℓ P C K decT encT) (τ :: Γ) υ)
    {c : ℕ} (hk : exprCostUB (k .zero) ≤ c) :
    (eLet e k).cost ≤ e.cost + c + 1 := by
  have h1 := exprCost_le_costUB (k .zero)
  dsimp only [eLet, Expr.cost]; omega

@[simp] private theorem eval_parsePreKeyWire_eq (c : Bytes) :
    E2EPureOp.eval ℓ .parsePreKeyWire c =
      (bhDecodePreKeyMsgE c).map fun m => (m.regId, (hdrV (bhHdrOfPreKeyMsg m), m.inner)) := by
  change (e2ePureOps ℓ).eval .parsePreKeyWire c = _
  rw [e2ePureOps_eval_parsePreKeyWire_lossless, e2eDecodePreKeyMsg_eq_bhDecodePreKeyMsgE]; rfl

def initPrinOptE {Γ : List (Ty (e2eSig ℓ))} (sidE : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S)) :
    Expr (e2eOps ℓ P C K decT encT) Γ (.opt (FinT S.N_id)) :=
  eCaseSum sidE (fun p => .some (.fst (v p)))
    (fun r1 => eCaseSum (v r1) (fun p => .some (.fst (v p))) (fun _ => .none))

@[simp] theorem eval_initPrinOptVal {Γ : List (Ty (e2eSig ℓ))}
    (sidE : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S)) (ρ : Env Γ) :
    (initPrinOptE sidE).eval ρ = bhDrvSessionInitPrin? (sidOfV (sidE.eval ρ)) := by
  rcases h : sidE.eval ρ with ⟨u, i⟩ | ⟨u, i⟩ | ⟨k, j, o⟩ | ⟨k, j, l⟩ <;>
    simp [initPrinOptE, eCaseSum, Expr.eval, h, sidOfV, bhDrvSessionInitPrin?]

def initRegIdE {Γ : List (Ty (e2eSig ℓ))} (sidE : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S)) :
    Expr (e2eOps ℓ P C K decT encT) Γ U32 :=
  eLet sidE fun s => eCaseOpt (initPrinOptE (v s)) (e2ePureOp (.u32Lit 0#32) .unit)
    (fun u => e2ePureOp .u32OfNat (e2ePureOp (.finVal S.N_id) (v u)))

@[simp] theorem eval_initRegIdVal {Γ : List (Ty (e2eSig ℓ))}
    (sidE : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S)) (ρ : Env Γ) :
    (initRegIdE sidE).eval ρ = bhInitRegId (sidOfV (sidE.eval ρ)) := by
  unfold initRegIdE bhInitRegId
  simp only [eLet, eCaseOpt, Expr.eval, eval_initPrinOptVal, eval_v_refl, env_get_zero]
  cases bhDrvSessionInitPrin? (sidOfV (sidE.eval ρ)) <;>
    simp [eval_v_refl, env_get_zero, eval_e2ePureOp, E2EPureOp.eval]

theorem cost_initRegIdE {Γ : List (Ty (e2eSig ℓ))}
    (sidE : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S)) :
    (initRegIdE sidE).cost ≤ sidE.cost + 24 := by
  unfold initRegIdE
  refine Nat.le_trans (cost_eLet_le sidE _ (c := 23) ?_) (by omega)
  simp only [initPrinOptE, exprCostUB_eCaseOpt, exprCostUB_eCaseSum, exprCostUB_v, exprCostUB,
    exprCostUB_e2ePureOp, E2EPureOp.cost]; omega

def hdrEqE {Γ : List (Ty (e2eSig ℓ))} (h1 h2 : Expr (e2eOps ℓ P C K decT encT) Γ hdrT) :
    Expr (e2eOps ℓ P C K decT encT) Γ .bool :=
  eLet (.pair h1 h2) fun p =>
    let a := Expr.fst (v p); let b := Expr.snd (v p)
    .and (e2ePureOp (.pbytesEq 32 32) (.pair (hdrIkA a) (hdrIkA b)))
      (.and (e2ePureOp (.pbytesEq 32 32) (.pair (hdrEkA a) (hdrEkA b)))
        (.and (e2ePureOp .pu32Eq (.pair (hdrSpkId a) (hdrSpkId b)))
          (.and (optEqByE (fun x y => e2ePureOp .pu32Eq (.pair x y)) (hdrOpkId a) (hdrOpkId b))
            (.and (e2ePureOp .pu32Eq (.pair (hdrPqId a) (hdrPqId b)))
              (e2ePureOp (.pbytesEq 1568 1568) (.pair (hdrKemCt a) (hdrKemCt b)))))))

@[simp] theorem eval_hdrEqVal {Γ : List (Ty (e2eSig ℓ))}
    (h1 h2 : Expr (e2eOps ℓ P C K decT encT) Γ hdrT) (ρ : Env Γ) :
    (hdrEqE h1 h2).eval ρ = (hdrOfV (h1.eval ρ) == hdrOfV (h2.eval ρ)) := by
  rcases h1v : h1.eval ρ with ⟨ik1, ek1, s1, o1, p1, k1⟩
  rcases h2v : h2.eval ρ with ⟨ik2, ek2, s2, o2, p2, k2⟩
  unfold hdrEqE; rw [Bool.eq_iff_iff]
  rcases o1 with _ | v1 <;> rcases o2 with _ | v2
  · simp [optEqByE, eLet, eCaseOpt, isNoneE, hdrIkA, hdrEkA, hdrSpkId, hdrOpkId, hdrPqId, hdrKemCt,
      Expr.eval, eval_v_refl, env_get_zero, eval_e2ePureOp, E2EPureOp.eval, h1v, h2v, hdrOfV,
      HandshakeHdr.mk.injEq]
  · simp [optEqByE, eLet, eCaseOpt, isNoneE, hdrIkA, hdrEkA, hdrSpkId, hdrOpkId, hdrPqId, hdrKemCt,
      Expr.eval, eval_v_refl, env_get_zero, eval_e2ePureOp, E2EPureOp.eval, h1v, h2v, hdrOfV,
      HandshakeHdr.mk.injEq]
  · simp [optEqByE, eLet, eCaseOpt, isNoneE, hdrIkA, hdrEkA, hdrSpkId, hdrOpkId, hdrPqId, hdrKemCt,
      Expr.eval, eval_v_refl, env_get_zero, eval_e2ePureOp, E2EPureOp.eval, h1v, h2v, hdrOfV,
      HandshakeHdr.mk.injEq]
  · by_cases hv : v1 = v2 <;>
      simp [optEqByE, eLet, eCaseOpt, isNoneE, hdrIkA, hdrEkA, hdrSpkId, hdrOpkId, hdrPqId,
        hdrKemCt, Expr.eval, eval_v_cons, eval_v_refl, env_get_zero, eval_e2ePureOp,
        E2EPureOp.eval, h1v, h2v, hdrOfV, HandshakeHdr.mk.injEq, hv]

theorem cost_hdrEqE {Γ : List (Ty (e2eSig ℓ))} (h1 h2 : Expr (e2eOps ℓ P C K decT encT) Γ hdrT) :
    (hdrEqE h1 h2).cost ≤ h1.cost + h2.cost + 3400 := by
  unfold hdrEqE; refine Nat.le_trans (cost_eLet_le (.pair h1 h2) _ (c := 3390) ?_) ?_
  · simp only [optEqByE, isNoneE, hdrIkA, hdrEkA, hdrSpkId, hdrOpkId, hdrPqId, hdrKemCt,
      exprCostUB_eLet, exprCostUB_eCaseOpt, exprCostUB_v, exprCostUB,
      exprCostUB_e2ePureOp, E2EPureOp.cost, PNat.val_ofNat]; omega
  · simp only [Expr.cost]; omega

def isBobRecvSmQueryE {Γ : List (Ty (e2eSig ℓ))} (qE : Expr (e2eOps ℓ P C K decT encT) Γ smQT) :
    Expr (e2eOps ℓ P C K decT encT) Γ .bool :=
  eCaseSum qE (fun _ => .bool false)
    (fun r1 => eCaseSum (v r1) (fun _ => .bool false)
      (fun r2 => eCaseSum (v r2) (fun dl => .fst (v dl))
        (fun r3 => eCaseSum (v r3) (fun ij => .fst (v ij)) (fun _ => .bool false))))

@[simp] theorem eval_isBobRecvSmQueryVal {Γ : List (Ty (e2eSig ℓ))}
    (qE : Expr (e2eOps ℓ P C K decT encT) Γ smQT) (ρ : Env Γ) :
    (isBobRecvSmQueryE qE).eval ρ =
      bhIsBobRecvSMQuery (smQdec (St := GhostState Bytes) (qE.eval ρ)) := by
  rcases h : qE.eval ρ with ⟨p, _, _⟩ | ⟨p, _, _, _⟩ | ⟨p, _⟩ | ⟨p, _⟩ | _
  · simp [isBobRecvSmQueryE, eCaseSum, Expr.eval, h, smQdec, bhIsBobRecvSMQuery]
  · simp [isBobRecvSmQueryE, eCaseSum, Expr.eval, h, smQdec, bhIsBobRecvSMQuery]
  · cases p <;> simp [isBobRecvSmQueryE, eCaseSum, Expr.eval, eval_v_refl, env_get_zero, h, smQdec,
      boolToParty, bhIsBobRecvSMQuery]
  · cases p <;> simp [isBobRecvSmQueryE, eCaseSum, Expr.eval, eval_v_refl, env_get_zero, h, smQdec,
      boolToParty, bhIsBobRecvSMQuery]
  · simp [isBobRecvSmQueryE, eCaseSum, Expr.eval, h, smQdec, bhIsBobRecvSMQuery]

theorem eval_isBobRecvSmQueryE {Γ : List (Ty (e2eSig ℓ))}
    (qE : Expr (e2eOps ℓ P C K decT encT) Γ smQT) (ρ : Env Γ)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (hq : qE.eval ρ = smQenc sq) :
    (isBobRecvSmQueryE qE).eval ρ = bhIsBobRecvSMQuery sq := by
  rw [eval_isBobRecvSmQueryVal, hq, smQdec_smQenc]

theorem cost_isBobRecvSmQueryE {Γ : List (Ty (e2eSig ℓ))}
    (qE : Expr (e2eOps ℓ P C K decT encT) Γ smQT) :
    (isBobRecvSmQueryE qE).cost ≤ qE.cost + 20 := by
  dsimp only [isBobRecvSmQueryE, eCaseSum, v, Expr.cost]; omega

def isBobAcceptSmRespE {Γ : List (Ty (e2eSig ℓ))}
    (qE : Expr (e2eOps ℓ P C K decT encT) Γ smQT)
    (respE : Expr (e2eOps ℓ P C K decT encT) Γ (smRT GhostStT)) :
    Expr (e2eOps ℓ P C K decT encT) Γ .bool :=
  eLet (.pair qE respE) fun p => .and (isBobRecvSmQueryE (.fst (v p)))
    (eCaseOpt (.fst (.snd (.snd (v p)))) (.bool false)
      (fun rr => eCaseSum (v rr) (fun _ => .bool false) (fun _ => .bool true)))

theorem eval_isBobAcceptSmRespE {Γ : List (Ty (e2eSig ℓ))}
    (qE : Expr (e2eOps ℓ P C K decT encT) Γ smQT)
    (respE : Expr (e2eOps ℓ P C K decT encT) Γ (smRT GhostStT)) (ρ : Env Γ)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (r : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range sq)
    (hq : qE.eval ρ = smQenc sq) (hr : respE.eval ρ = smRenc (stT := GhostStT) id sq r) :
    (isBobAcceptSmRespE qE respE).eval ρ = bhIsBobAcceptSMResp sq r := by
  unfold isBobAcceptSmRespE
  simp only [eLet, Expr.eval, eval_isBobRecvSmQueryVal, eval_v_refl, env_get_zero, hq, hr,
    smQdec_smQenc]
  rcases sq with (((_ | _) | ⟨p, _⟩) | ⟨p, _⟩) | _
  · simp [bhIsBobRecvSMQuery, bhIsBobAcceptSMResp]
  · simp [bhIsBobRecvSMQuery, bhIsBobAcceptSMResp]
  · cases p
    · simp [bhIsBobRecvSMQuery, bhIsBobAcceptSMResp]
    · cases r with
      | none => simp [bhIsBobRecvSMQuery, bhIsBobAcceptSMResp, smRenc, eCaseOpt, Expr.eval,
          eval_v_refl, env_get_zero]
      | some rr => cases rr <;> simp [bhIsBobRecvSMQuery, bhIsBobAcceptSMResp, smRenc,
          recvResultEnc, eCaseOpt, eCaseSum, Expr.eval, eval_v_refl, env_get_zero]
  · cases p
    · simp [bhIsBobRecvSMQuery, bhIsBobAcceptSMResp]
    · cases r with
      | none => simp [bhIsBobRecvSMQuery, bhIsBobAcceptSMResp, smRenc, eCaseOpt, Expr.eval,
          eval_v_refl, env_get_zero]
      | some rr => cases rr <;> simp [bhIsBobRecvSMQuery, bhIsBobAcceptSMResp, smRenc,
          recvResultEnc, eCaseOpt, eCaseSum, Expr.eval, eval_v_refl, env_get_zero]
  · simp [bhIsBobRecvSMQuery, bhIsBobAcceptSMResp]

theorem cost_isBobAcceptSmRespE {Γ : List (Ty (e2eSig ℓ))}
    (qE : Expr (e2eOps ℓ P C K decT encT) Γ smQT)
    (respE : Expr (e2eOps ℓ P C K decT encT) Γ (smRT GhostStT)) :
    (isBobAcceptSmRespE qE respE).cost ≤ qE.cost + respE.cost + 40 := by
  unfold isBobAcceptSmRespE; refine Nat.le_trans (cost_eLet_le (.pair qE respE) _ (c := 35) ?_) ?_
  · simp only [isBobRecvSmQueryE, exprCostUB_eCaseOpt, exprCostUB_eCaseSum, exprCostUB_v,
      exprCostUB]; omega
  · simp only [Expr.cost]; omega

def setInstMetaAcceptE {Γ : List (Ty (e2eSig ℓ))}
    (imE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eInstMetaTy S ℓ))
    (ikACorrE : Expr (e2eOps ℓ P C K decT encT) Γ .bool) :
    Expr (e2eOps ℓ P C K decT encT) Γ (e2eInstMetaTy S ℓ) :=
  .pair (.bool true) (.pair ikACorrE (.snd (.snd imE)))

@[simp] theorem eval_setInstMetaAcceptVal {Γ : List (Ty (e2eSig ℓ))}
    (imE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eInstMetaTy S ℓ))
    (ikACorrE : Expr (e2eOps ℓ P C K decT encT) Γ .bool) (ρ : Env Γ) :
    (setInstMetaAcceptE imE ikACorrE).eval ρ =
      e2eInstMetaEnc (ℓ := ℓ)
        { e2eInstMetaDec (imE.eval ρ) with
          bobAccepted := true, ikACorrAtAccept := ikACorrE.eval ρ } := by
  rcases h : imE.eval ρ with ⟨_, _, _, _, _⟩
  simp [setInstMetaAcceptE, Expr.eval, h, e2eInstMetaEnc, e2eInstMetaDec]

theorem eval_setInstMetaAcceptE {Γ : List (Ty (e2eSig ℓ))}
    (imE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eInstMetaTy S ℓ))
    (ikACorrE : Expr (e2eOps ℓ P C K decT encT) Γ .bool) (ρ : Env Γ)
    (im : ModelDriverInstanceMeta S) (him : imE.eval ρ = e2eInstMetaEnc (ℓ := ℓ) im) :
    (setInstMetaAcceptE imE ikACorrE).eval ρ =
      e2eInstMetaEnc (ℓ := ℓ) { im with bobAccepted := true, ikACorrAtAccept := ikACorrE.eval ρ } := by
  rw [eval_setInstMetaAcceptVal, him, e2eInstMetaDec_e2eInstMetaEnc]

theorem cost_setInstMetaAcceptE {Γ : List (Ty (e2eSig ℓ))}
    (imE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eInstMetaTy S ℓ))
    (ikACorrE : Expr (e2eOps ℓ P C K decT encT) Γ .bool) :
    (setInstMetaAcceptE imE ikACorrE).cost ≤ imE.cost + ikACorrE.cost + 8 := by
  dsimp only [setInstMetaAcceptE, Expr.cost]; omega

/-- Pure `ReductionDsl` wire filter evaluating to `(bhFilterLocalSmQuery bobAcc sid hdr sq).map smQenc`. -/
def filterLocalSmQueryE {Γ : List (Ty (e2eSig ℓ))}
    (bobAccE : Expr (e2eOps ℓ P C K decT encT) Γ .bool)
    (sidE : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S))
    (hdrE : Expr (e2eOps ℓ P C K decT encT) Γ hdrT)
    (qE : Expr (e2eOps ℓ P C K decT encT) Γ smQT) :
    Expr (e2eOps ℓ P C K decT encT) Γ (.opt smQT) :=
  eLet (.pair bobAccE (.pair sidE (.pair hdrE qE))) fun args =>
    eLet (.fst (v args)) fun ba =>
    eLet (.fst (.snd (v args))) fun s =>
    eLet (.fst (.snd (.snd (v args)))) fun h =>
    eLet (.snd (.snd (.snd (v args)))) fun q0 =>
      eCaseSum (v q0) (fun _ => .some (v q0))
        (fun r1 => eCaseSum (v r1) (fun _ => .some (v q0))
          (fun r2 => eCaseSum (v r2)
            (fun dl =>
              eLet (.fst (v dl)) fun p =>
              eLet (.snd (v dl)) fun c =>
                .ite (.not (v p))
                  (eCaseOpt (e2ePureOp .parsePreKeyWire (v c)) (.some (v q0)) (fun _ => .none))
                  (.ite (.not (v ba))
                    (eCaseOpt
                      (e2ePureOp .partneredInnerBytes
                        (.pair (.bool false) (.pair (initRegIdE (v s)) (.pair (v h) (v c)))))
                      .none
                      (fun inner => .some (.inr (.inr (.inl (.pair (.bool true) (v inner)))))))
                    (eCaseOpt (e2ePureOp .parsePreKeyWire (v c))
                      (.some (.inr (.inr (.inl (.pair (.bool true) (v c))))))
                      (fun parsed =>
                        .ite (hdrEqE (.fst (.snd (v parsed))) (v h))
                          (.some (.inr (.inr (.inl (.pair (.bool true) (.snd (.snd (v parsed))))))))
                          .none))))
            (fun r3 => eCaseSum (v r3)
              (fun ij =>
                eLet (.fst (v ij)) fun p =>
                eLet (.snd (v ij)) fun c =>
                  .ite (.not (v p))
                    (eCaseOpt (e2ePureOp .parsePreKeyWire (v c)) (.some (v q0)) (fun _ => .none))
                    (.ite (.not (v ba)) .none
                      (eCaseOpt (e2ePureOp .parsePreKeyWire (v c))
                        (.some (.inr (.inr (.inr (.inl (.pair (.bool true) (v c)))))))
                        (fun parsed =>
                          .ite (.and (hdrEqE (.fst (.snd (v parsed))) (v h))
                              (e2ePureOp .checkShortCiphertext
                                (.pair (v c) (.some (.snd (.snd (v parsed)))))))
                            (.some (.inr (.inr (.inr (.inl
                              (.pair (.bool true) (.snd (.snd (v parsed)))))))))
                            .none))))
              (fun _ => .some (v q0)))))

theorem eval_filterLocalSmQueryE {Γ : List (Ty (e2eSig ℓ))}
    (bobAccE : Expr (e2eOps ℓ P C K decT encT) Γ .bool)
    (sidE : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S))
    (hdrE : Expr (e2eOps ℓ P C K decT encT) Γ hdrT)
    (qE : Expr (e2eOps ℓ P C K decT encT) Γ smQT)
    (ρ : Env Γ) (bobAccepted : Bool) (sid : SessionId S) (hdr : HandshakeHdr)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (hba : bobAccE.eval ρ = bobAccepted) (hsid : sidE.eval ρ = sidV sid)
    (hhdr : hdrE.eval ρ = hdrV hdr) (hq : qE.eval ρ = smQenc sq) :
    (filterLocalSmQueryE bobAccE sidE hdrE qE).eval ρ =
      (bhFilterLocalSmQuery bobAccepted sid hdr sq).map (smQenc (ℓ := ℓ)) := by
  unfold filterLocalSmQueryE
  simp only [eLet, Expr.eval, eval_v_cons, eval_v_refl, env_get_zero, hba, hsid, hhdr, hq]
  rcases sq with (((_ | _) | ⟨pDl, cDl⟩) | ⟨pIj, cIj⟩) | _
  · rfl
  · rfl
  · cases pDl
    · simp only [smQenc, partyToBool, eCaseSum, eCaseOpt, Expr.eval, eval_v_cons,
        eval_v_refl, env_get_zero, Bool.not_false, ↓reduceIte, eval_e2ePureOp,
        eval_parsePreKeyWire_eq, bhFilterLocalSmQuery]
      cases bhDecodePreKeyMsgE cDl <;> simp [smQenc, partyToBool]
    · cases bobAccepted
      · simp only [smQenc, partyToBool, eCaseSum, eCaseOpt, Expr.eval, eval_v_cons,
          eval_v_refl, env_get_zero, Bool.not_true, Bool.not_false, Bool.false_eq_true,
          ↓reduceIte, eval_e2ePureOp, E2EPureOp.eval, eval_initRegIdVal, sidOfV_sidV, hdrOfV_hdrV,
          e2ePartneredInnerBytes_lossless, e2eDecodePreKeyMsg_eq_bhDecodePreKeyMsgE,
          e2eExpectedPreKeyMsg_eq_bhExpectedPreKeyMsg, bhFilterLocalSmQuery]
        cases bhDecodePreKeyMsgE cDl with
        | none => rfl
        | some m =>
          by_cases hc : cDl == wirePrekey ::
              (bhExpectedPreKeyMsg (bhInitRegId sid) hdr m.inner).bytes <;>
            simp [hc, smQenc, partyToBool]
      · simp only [smQenc, partyToBool, eCaseSum, Expr.eval, eval_v_cons,
          eval_v_refl, env_get_zero, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          bhFilterLocalSmQuery]
        cases hdec : bhDecodePreKeyMsgE cDl with
        | none =>
          simp [eCaseOpt, Expr.eval, eval_v_refl, env_get_zero, eval_e2ePureOp,
            eval_parsePreKeyWire_eq, hdec, smQenc, partyToBool]
        | some m =>
          simp only [eCaseOpt, Expr.eval, eval_v_cons, eval_v_refl, env_get_zero,
            eval_e2ePureOp, eval_parsePreKeyWire_eq, hdec, Option.map, eval_hdrEqVal, hdrOfV_hdrV]
          by_cases hh : bhHdrOfPreKeyMsg m == hdr <;> simp [hh, smQenc, partyToBool]
  · cases pIj
    · simp only [smQenc, partyToBool, eCaseSum, eCaseOpt, Expr.eval, eval_v_cons,
        eval_v_refl, env_get_zero, Bool.not_false, ↓reduceIte, eval_e2ePureOp,
        eval_parsePreKeyWire_eq, bhFilterLocalSmQuery]
      cases bhDecodePreKeyMsgE cIj <;> simp [smQenc, partyToBool]
    · cases bobAccepted
      · simp [smQenc, partyToBool, eCaseSum, Expr.eval, eval_v_cons, eval_v_refl,
          env_get_zero, bhFilterLocalSmQuery]
      · simp only [smQenc, partyToBool, eCaseSum, Expr.eval, eval_v_cons,
          eval_v_refl, env_get_zero, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          bhFilterLocalSmQuery]
        cases hdec : bhDecodePreKeyMsgE cIj with
        | none =>
          simp [eCaseOpt, Expr.eval, eval_v_refl, env_get_zero, eval_e2ePureOp,
            eval_parsePreKeyWire_eq, hdec, smQenc, partyToBool]
        | some m =>
          simp only [eCaseOpt, Expr.eval, eval_v_cons, eval_v_refl, env_get_zero,
            eval_e2ePureOp, eval_parsePreKeyWire_eq, hdec, Option.map, eval_hdrEqVal, hdrOfV_hdrV]
          dsimp only [E2EPureOp.eval]
          by_cases hh : bhHdrOfPreKeyMsg m = hdr ∧ shortCiphertext cIj = true ∧
              m.inner.length + 2048 < 4294967296 <;>
            simp [hh, and_assoc, smQenc, partyToBool]
  · rfl

@[simp] theorem eval_filterLocalSmQueryVal {Γ : List (Ty (e2eSig ℓ))}
    (bobAccE : Expr (e2eOps ℓ P C K decT encT) Γ .bool)
    (sidE : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S))
    (hdrE : Expr (e2eOps ℓ P C K decT encT) Γ hdrT)
    (qE : Expr (e2eOps ℓ P C K decT encT) Γ smQT) (ρ : Env Γ) :
    (filterLocalSmQueryE bobAccE sidE hdrE qE).eval ρ =
      (bhFilterLocalSmQuery (bobAccE.eval ρ) (sidOfV (sidE.eval ρ)) (hdrOfV (hdrE.eval ρ))
        (smQdec (St := GhostState Bytes) (qE.eval ρ))).map (smQenc (ℓ := ℓ)) :=
  eval_filterLocalSmQueryE bobAccE sidE hdrE qE ρ (bobAccE.eval ρ) (sidOfV (sidE.eval ρ))
    (hdrOfV (hdrE.eval ρ)) (smQdec (St := GhostState Bytes) (qE.eval ρ))
    rfl (by simp) (by simp) (by simp)

theorem cost_filterLocalSmQueryE {Γ : List (Ty (e2eSig ℓ))}
    (bobAccE : Expr (e2eOps ℓ P C K decT encT) Γ .bool)
    (sidE : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S))
    (hdrE : Expr (e2eOps ℓ P C K decT encT) Γ hdrT)
    (qE : Expr (e2eOps ℓ P C K decT encT) Γ smQT) :
    (filterLocalSmQueryE bobAccE sidE hdrE qE).cost ≤
      bobAccE.cost + sidE.cost + hdrE.cost + qE.cost + 8000 := by
  unfold filterLocalSmQueryE
  refine Nat.le_trans
    (cost_eLet_le (.pair bobAccE (.pair sidE (.pair hdrE qE))) _ (c := 7990) ?_) ?_
  · simp only [initRegIdE, initPrinOptE, hdrEqE, optEqByE, isNoneE,
      hdrIkA, hdrEkA, hdrSpkId, hdrOpkId, hdrPqId, hdrKemCt,
      exprCostUB_eLet, exprCostUB_eCaseOpt, exprCostUB_eCaseSum, exprCostUB_v, exprCostUB,
      exprCostUB_e2ePureOp, E2EPureOp.cost, PNat.val_ofNat]
    omega
  · simp only [Expr.cost]; omega

attribute [local irreducible] defaultE2eGsE listGetOptE listSetE initRegIdE hdrEqE
  isBobRecvSmQueryE isBobAcceptSmRespE filterLocalSmQueryE

end SessionExprs

end Computational.Proofs.E2E.Dsl.LocalSessionStepAux
